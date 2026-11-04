import { createSlice } from '@reduxjs/toolkit';

import { makeCompileActions } from '../../compileActions';

const initialState: State = {
  requestsInProgress: 0,
};

interface State {
  requestsInProgress: number;
  code?: string;
  stdout?: string;
  stderr?: string;
  error?: string;
}

const sliceName = 'output/wasm';

export const { action: performCompileWasm, performCompile: performCompileToWasmOnly } =
  makeCompileActions({ sliceName, target: 'wasm' });

const slice = createSlice({
  name: 'output/wasm',
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performCompileWasm.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performCompileWasm.fulfilled, (state, action) => {
        const { code, stdout, stderr } = action.payload;
        Object.assign(state, { code, stdout, stderr });
        state.requestsInProgress -= 1;
      })
      .addCase(performCompileWasm.rejected, (state, action) => {
        state.error = action.error.message;
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
