import { PayloadAction, createSlice } from '@reduxjs/toolkit';
import z from 'zod';

import {
  createWebsocketResponse,
  createWebsocketResponseSchema,
  makeWebSocketMeta,
} from '../websocketActions';

type State = {
  connected: boolean;
  error?: string;
};

const initialState: State = {
  connected: false,
};

const websocketConnectedPayloadSchema = z.object({
  iAcceptThisIsAnUnsupportedApi: z.boolean(),
});
type websocketConnectedPayload = z.infer<typeof websocketConnectedPayloadSchema>;

const { action: websocketError, schema: websocketErrorSchema } = createWebsocketResponse(
  'websocket/error',
  z.object({
    error: z.string(),
  }),
);

const slice = createSlice({
  name: 'websocket',
  initialState,
  reducers: {
    connected: {
      reducer: (state, _action: PayloadAction<websocketConnectedPayload>) => {
        state.connected = true;
        delete state.error;
      },

      prepare: () => ({
        payload: {
          iAcceptThisIsAnUnsupportedApi: true,
        },
        meta: makeWebSocketMeta(),
      }),
    },

    disconnected: (state) => {
      state.connected = false;
    },

    clientError: (state, action: PayloadAction<string>) => {
      state.error = action.payload;
    },
  },
  extraReducers: (builder) => {
    builder.addCase(websocketError, (state, action) => {
      state.error = action.payload.error;
    });
  },
});

export const {
  connected: websocketConnected,
  disconnected: websocketDisconnected,
  clientError: websocketClientError,
} = slice.actions;

export { websocketError, websocketErrorSchema };

export const websocketConnectedSchema = createWebsocketResponseSchema(
  websocketConnected,
  websocketConnectedPayloadSchema,
);

export default slice.reducer;
