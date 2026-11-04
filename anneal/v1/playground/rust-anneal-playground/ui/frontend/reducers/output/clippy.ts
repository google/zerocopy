import { createAsyncThunk, createSlice } from '@reduxjs/toolkit';
import * as z from 'zod';

import { jsonPost, routes } from '../../api';
import { State as RootState } from '../../reducers';
import { clippyRequestSelector } from '../../selectors';

const sliceName = 'output/clippy';

const initialState: State = {
  requestsInProgress: 0,
};

interface State {
  requestsInProgress: number;
  stdout?: string;
  stderr?: string;
  error?: string;
}

interface ClippyRequestBody {
  channel: string;
  crateType: string;
  edition: string;
  code: string;
}

const ClippyResponseBody = z.object({
  success: z.boolean(),
  stdout: z.string(),
  stderr: z.string(),
});

type ClippyResponseBody = z.infer<typeof ClippyResponseBody>;

export const performClippy = createAsyncThunk<ClippyResponseBody, void, { state: RootState }>(
  sliceName,
  async (_arg: void, { getState }) => {
    const body: ClippyRequestBody = clippyRequestSelector(getState());

    const d = await jsonPost(routes.clippy, body);
    return ClippyResponseBody.parseAsync(d);
  },
);

const slice = createSlice({
  name: sliceName,
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performClippy.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performClippy.fulfilled, (state, action) => {
        state.requestsInProgress -= 1;
        Object.assign(state, action.payload);
      })
      .addCase(performClippy.rejected, (state) => {
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
