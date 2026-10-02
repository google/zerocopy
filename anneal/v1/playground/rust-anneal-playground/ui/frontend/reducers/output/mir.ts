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

const sliceName = 'output/mir';

export const { action: performCompileMir, performCompile: performCompileToMirOnly } =
  makeCompileActions({ sliceName, target: 'mir' });

const slice = createSlice({
  name: 'output/mir',
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performCompileMir.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performCompileMir.fulfilled, (state, action) => {
        const { code, stdout, stderr } = action.payload;
        Object.assign(state, { code, stdout, stderr });
        state.requestsInProgress -= 1;
      })
      .addCase(performCompileMir.rejected, (state, action) => {
        state.error = action.error.message;
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
