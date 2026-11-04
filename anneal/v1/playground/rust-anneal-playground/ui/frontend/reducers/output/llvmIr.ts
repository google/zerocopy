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

const sliceName = 'output/llvmIr';

export const { action: performCompileLlvmIr, performCompile: performCompileToLlvmIrOnly } =
  makeCompileActions({ sliceName, target: 'llvm-ir' });

const slice = createSlice({
  name: 'output/llvmIr',
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performCompileLlvmIr.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performCompileLlvmIr.fulfilled, (state, action) => {
        const { code, stdout, stderr } = action.payload;
        Object.assign(state, { code, stdout, stderr });
        state.requestsInProgress -= 1;
      })
      .addCase(performCompileLlvmIr.rejected, (state, action) => {
        state.error = action.error.message;
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
