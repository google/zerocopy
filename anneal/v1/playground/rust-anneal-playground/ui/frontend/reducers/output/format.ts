import { createAsyncThunk, createSlice } from '@reduxjs/toolkit';
import * as z from 'zod';

import { jsonPost, routes } from '../../api';
import { State as RootState } from '../../reducers';
import { formatRequestSelector } from '../../selectors';

const sliceName = 'output/format';

const initialState: State = {
  requestsInProgress: 0,
};

interface State {
  requestsInProgress: number;
  stdout?: string;
  stderr?: string;
}

interface FormatRequestBody {
  channel: string;
  edition: string;
  code: string;
}

const FormatResponseBody = z.object({
  success: z.boolean(),
  code: z.string(),
  stdout: z.string(),
  stderr: z.string(),
});

type FormatResponseBody = z.infer<typeof FormatResponseBody>;

export const performFormat = createAsyncThunk<FormatResponseBody, void, { state: RootState }>(
  sliceName,
  async (_arg: void, { getState }) => {
    const body: FormatRequestBody = formatRequestSelector(getState());

    const d = await jsonPost(routes.format, body);
    return FormatResponseBody.parseAsync(d);
  },
);

const slice = createSlice({
  name: sliceName,
  initialState,
  reducers: {},
  extraReducers: (builder) => {
    builder
      .addCase(performFormat.pending, (state) => {
        state.requestsInProgress += 1;
      })
      .addCase(performFormat.fulfilled, (state, action) => {
        state.requestsInProgress -= 1;
        Object.assign(state, action.payload);
      })
      .addCase(performFormat.rejected, (state) => {
        state.requestsInProgress -= 1;
      });
  },
});

export default slice.reducer;
