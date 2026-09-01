import { Draft, UnknownAction, createAsyncThunk, createSlice } from '@reduxjs/toolkit';
import * as z from 'zod';

import { ThunkAction } from '../../actions';
import { jsonPost, routes } from '../../api';
import {
  currentExecutionSequenceNumberSelector,
  executeRequestPayloadSelector,
  executeViaWebsocketSelector,
} from '../../selectors';
import { Channel, Edition, Mode } from '../../types';
import {
  WsPayloadAction,
  createWebsocketResponse,
  makeWebSocketMeta,
} from '../../websocketActions';
import { websocketError } from '../websocket';

const initialState: State = {
  requestsInProgress: 0,
  allowLongRun: false,
};

interface State {
  sequenceNumber?: number;
  requestsInProgress: number;
  stdout?: string;
  stderr?: string;
  error?: string;
  residentSetSizeBytes?: number;
  totalTimeSecs?: number;
  allowLongRun: boolean;
}

type wsExecuteRequestPayload = {
  channel: Channel;
  mode: Mode;
  edition: Edition;
  crateType: string;
  tests: boolean;
  code: string;
  backtrace: boolean;
  executionTool: ExecutionTool;
};

const { action: wsExecuteBegin, schema: wsExecuteBeginSchema } = createWebsocketResponse(
  'output/execute/wsExecuteBegin',
  z.undefined().optional(),
);

const { action: wsExecuteStdout, schema: wsExecuteStdoutSchema } = createWebsocketResponse(
  'output/execute/wsExecuteStdout',
  z.string(),
);

const { action: wsExecuteStderr, schema: wsExecuteStderrSchema } = createWebsocketResponse(
  'output/execute/wsExecuteStderr',
  z.string(),
);

const { action: wsExecuteStatus, schema: wsExecuteStatusSchema } = createWebsocketResponse(
  'output/execute/wsExecuteStatus',
  z.object({
    totalTimeSecs: z.number(),
    residentSetSizeBytes: z.number(),
  }),
);

const { action: wsExecuteEnd, schema: wsExecuteEndSchema } = createWebsocketResponse(
  'output/execute/wsExecuteEnd',
  z.object({
    success: z.boolean(),
    exitDetail: z.string(),
  }),
);

const sliceName = 'output/execute';

export type ExecutionTool = 'cargo' | 'anneal-verify';


export interface ExecuteRequestBody {
  channel: string;
  mode: string;
  crateType: string;
  tests: boolean;
  code: string;
  edition: string;
  backtrace: boolean;
  executionTool: ExecutionTool;
}

const ExecuteResponseBody = z.object({
  success: z.boolean(),
  exitDetail: z.string(),
  stdout: z.string(),
  stderr: z.string(),
});
type ExecuteResponseBody = z.infer<typeof ExecuteResponseBody>;

export const performExecute = createAsyncThunk(sliceName, async (payload: ExecuteRequestBody) => {
  const d = await jsonPost(routes.execute, payload);
  return ExecuteResponseBody.parseAsync(d);
});

const prepareWithCurrentSequenceNumber = <P>(payload: P, sequenceNumber: number) => ({
  payload,
  meta: {
    websocket: true,
    sequenceNumber,
  },
});

const sequenceNumberMatches =
  <P>(whenMatch: (state: Draft<State>, payload: P) => void) =>
  (state: Draft<State>, action: WsPayloadAction<P>) => {
    const {
      payload,
      meta: { sequenceNumber },
    } = action;

    if (sequenceNumber === state.sequenceNumber) {
      whenMatch(state, payload);
    }
  };

const slice = createSlice({
  name: 'output/execute',
  initialState,
  reducers: {
    wsExecuteRequest: {
      reducer: (state, action: WsPayloadAction<wsExecuteRequestPayload>) => {
        const { sequenceNumber } = action.meta;
        if (sequenceNumber >= (state.sequenceNumber ?? 0)) {
          state.sequenceNumber = sequenceNumber;
        }

        state.requestsInProgress = 1; // Only tracking one request
      },

      prepare: (payload: wsExecuteRequestPayload) => ({
        payload,
        meta: makeWebSocketMeta(),
      }),
    },
    wsExecuteStdin: {
      reducer: () => {},

      prepare: prepareWithCurrentSequenceNumber,
    },
    wsExecuteStdinClose: {
      reducer: () => {},

      prepare: prepareWithCurrentSequenceNumber,
    },
    wsExecuteKill: {
      reducer: () => {},

      prepare: prepareWithCurrentSequenceNumber,
    },
    allowLongRun: (state) => {
      state.allowLongRun = true;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(performExecute.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performExecute.fulfilled, (state, action) => {
        const { success, exitDetail, stdout, stderr } = action.payload;
        Object.assign(state, { stdout, stderr });
        delete state.error;
        if (!success) {
          state.error = exitDetail;
        }
        state.requestsInProgress -= 1;
      })
      .addCase(performExecute.rejected, (state, action) => {
        if (!action.payload) {
          state.error = action.error.message;
        }
        state.requestsInProgress -= 1;
      })
      .addCase(
        wsExecuteBegin,
        sequenceNumberMatches((state) => {
          state.stdout = '';
          state.stderr = '';
          delete state.error;

          delete state.residentSetSizeBytes;
          delete state.totalTimeSecs;
          state.allowLongRun = false;
        }),
      )
      .addCase(
        wsExecuteStdout,
        sequenceNumberMatches((state, payload) => {
          state.stdout += payload;
        }),
      )
      .addCase(
        wsExecuteStderr,
        sequenceNumberMatches((state, payload) => {
          state.stderr += payload;
        }),
      )
      .addCase(
        wsExecuteStatus,
        sequenceNumberMatches((state, payload) => {
          Object.assign(state, payload);
        }),
      )
      .addCase(
        wsExecuteEnd,
        sequenceNumberMatches((state, payload) => {
          state.requestsInProgress = 0; // Only tracking one request
          delete state.sequenceNumber;

          if (!payload.success) {
            state.error = payload.exitDetail;
          }
        }),
      )
      .addCase(
        websocketError,
        sequenceNumberMatches((state, payload) => {
          state.error = payload.error;
        }),
      );
  },
});

export const { wsExecuteRequest, allowLongRun, wsExecuteKill } = slice.actions;

export const performCommonExecute =
  (crateType: string, tests: boolean, executionTool: ExecutionTool = 'cargo'): ThunkAction =>
  (dispatch, getState) => {
    const state = getState();
    const body = executeRequestPayloadSelector(state, { crateType, tests, executionTool, });
    const useWebSocket = executeViaWebsocketSelector(state);

    if (useWebSocket) {
      dispatch(wsExecuteRequest(body));
    } else {
      dispatch(performExecute(body));
    }
  };

const dispatchWhenSequenceNumber =
  <A extends UnknownAction>(cb: (sequenceNumber: number) => A): ThunkAction =>
  (dispatch, getState) => {
    const state = getState();
    const sequenceNumber = currentExecutionSequenceNumberSelector(state);
    if (sequenceNumber) {
      const action = cb(sequenceNumber);
      dispatch(action);
    }
  };

export const wsExecuteStdin = (payload: string): ThunkAction =>
  dispatchWhenSequenceNumber((sequenceNumber) =>
    slice.actions.wsExecuteStdin(payload, sequenceNumber),
  );

export const wsExecuteStdinClose = (): ThunkAction =>
  dispatchWhenSequenceNumber((sequenceNumber) =>
    slice.actions.wsExecuteStdinClose(undefined, sequenceNumber),
  );

export const wsExecuteKillCurrent = (): ThunkAction =>
  dispatchWhenSequenceNumber((sequenceNumber) =>
    slice.actions.wsExecuteKill(undefined, sequenceNumber),
  );

export {
  wsExecuteBeginSchema,
  wsExecuteStdoutSchema,
  wsExecuteStderrSchema,
  wsExecuteStatusSchema,
  wsExecuteEndSchema,
};

export { wsExecuteStatus, wsExecuteEnd };

export default slice.reducer;
