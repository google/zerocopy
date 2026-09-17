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

const sliceName = 'output/hir';

export const { action: performCompileHir, performCompile: performCompileToHirOnly } =
  makeCompileActions({ sliceName, target: 'hir' });

const slice = createSlice({
  name: 'output/hir',
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performCompileHir.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performCompileHir.fulfilled, (state, action) => {
        const { code, stdout, stderr } = action.payload;
        Object.assign(state, { code, stdout, stderr });
        state.requestsInProgress -= 1;
      })
      .addCase(performCompileHir.rejected, (state, action) => {
        state.error = action.error.message;
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
