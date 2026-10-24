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

const sliceName = 'output/assembly';

export const { action: performCompileAssembly, performCompile: performCompileToAssemblyOnly } =
  makeCompileActions({ sliceName, target: 'asm' });

const slice = createSlice({
  name: 'output/assembly',
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performCompileAssembly.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performCompileAssembly.fulfilled, (state, action) => {
        const { code, stdout, stderr } = action.payload;
        Object.assign(state, { code, stdout, stderr });
        state.requestsInProgress -= 1;
      })
      .addCase(performCompileAssembly.rejected, (state, action) => {
        state.error = action.error.message;
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
