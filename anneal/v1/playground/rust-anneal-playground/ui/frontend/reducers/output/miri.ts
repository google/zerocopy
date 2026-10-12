import { createAsyncThunk, createSlice } from '@reduxjs/toolkit';
import * as z from 'zod';

import { jsonPost, routes } from '../../api';
import { State as RootState } from '../../reducers';
import { miriRequestSelector } from '../../selectors';
import { AliasingModel } from '../../types';

const sliceName = 'output/miri';

const initialState: State = {
  requestsInProgress: 0,
};

interface State {
  requestsInProgress: number;
  stdout?: string;
  stderr?: string;
  error?: string;
}

interface MiriRequestBody {
  code: string;
  edition: string;
  tests: boolean;
  aliasingModel: AliasingModel;
}

const MiriResponseBody = z.object({
  success: z.boolean(),
  stdout: z.string(),
  stderr: z.string(),
});

type MiriResponseBody = z.infer<typeof MiriResponseBody>;

export const performMiri = createAsyncThunk<MiriResponseBody, void, { state: RootState }>(
  sliceName,
  async (_arg: void, { getState }) => {
    const body: MiriRequestBody = miriRequestSelector(getState());

    const d = await jsonPost(routes.miri, body);
    return MiriResponseBody.parseAsync(d);
  },
);

const slice = createSlice({
  name: sliceName,
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performMiri.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performMiri.fulfilled, (state, action) => {
        state.requestsInProgress -= 1;
        Object.assign(state, action.payload);
      })
      .addCase(performMiri.rejected, (state) => {
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
