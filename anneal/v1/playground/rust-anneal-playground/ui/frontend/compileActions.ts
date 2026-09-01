import { AsyncThunk, createAsyncThunk } from '@reduxjs/toolkit';
import * as z from 'zod';

import { ThunkAction } from './actions';
import { jsonPost, routes } from './api';
import { compileRequestPayloadSelector } from './selectors';

interface CompileRequestBody {
  channel: string;
  mode: string;
  crateType: string;
  tests: boolean; // Used?
  code: string;
  edition: string;
  backtrace: boolean; // Used?
  target: string;
  assemblyFlavor: string;
  demangleAssembly: string;
  processAssembly: string;
}

const CompileResponseBody = z.object({
  code: z.string(),
  stdout: z.string(),
  stderr: z.string(),
});
type CompileResponseBody = z.infer<typeof CompileResponseBody>;

interface Props {
  sliceName: string;
  target: string;
}

interface CompileActions {
  action: AsyncThunk<CompileResponseBody, CompileRequestBody, object>;
  performCompile: () => ThunkAction;
}

export const makeCompileActions = ({ sliceName, target }: Props): CompileActions => {
  const action = createAsyncThunk(sliceName, async (payload: CompileRequestBody) => {
    const d = await jsonPost(routes.compile, payload);
    return CompileResponseBody.parseAsync(d);
  });

  const performCompile = (): ThunkAction => (dispatch, getState) => {
    const state = getState();
    const body = compileRequestPayloadSelector(state, { target });
    dispatch(action(body));
  };

  return { action, performCompile };
};
