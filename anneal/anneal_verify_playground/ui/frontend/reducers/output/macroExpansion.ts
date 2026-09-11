import { createAsyncThunk, createSlice } from '@reduxjs/toolkit';
import * as z from 'zod';

import { jsonPost, routes } from '../../api';
import { State as RootState } from '../../reducers';
import { macroExpansionRequestSelector } from '../../selectors';

const sliceName = 'output/macroExpansion';

const initialState: State = {
  requestsInProgress: 0,
};

interface State {
  requestsInProgress: number;
  stdout?: string;
  stderr?: string;
  error?: string;
}

interface MacroExpansionRequestBody {
  code: string;
  edition: string;
}

const MacroExpansionResponseBody = z.object({
  success: z.boolean(),
  stdout: z.string(),
  stderr: z.string(),
});

type MacroExpansionResponseBody = z.infer<typeof MacroExpansionResponseBody>;

export const performMacroExpansion = createAsyncThunk<
  MacroExpansionResponseBody,
  void,
  { state: RootState }
>(sliceName, async (_arg: void, { getState }) => {
  const body: MacroExpansionRequestBody = macroExpansionRequestSelector(getState());

  const d = await jsonPost(routes.macroExpansion, body);
  return MacroExpansionResponseBody.parseAsync(d);
});

const slice = createSlice({
  name: sliceName,
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performMacroExpansion.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performMacroExpansion.fulfilled, (state, action) => {
        state.requestsInProgress -= 1;
        Object.assign(state, action.payload);
      })
      .addCase(performMacroExpansion.rejected, (state) => {
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
