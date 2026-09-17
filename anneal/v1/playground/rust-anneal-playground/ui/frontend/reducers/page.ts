import { PayloadAction, createSlice } from '@reduxjs/toolkit';

import { Page } from '../types';

const initialState = 'index' as Page;

const slice = createSlice({
  name: 'page',
  initialState,
  reducers: {
    setPage: (_state, action: PayloadAction<Page>) => {
      return action.payload;
    },
  },
});

export const { setPage } = slice.actions;

export const navigateToIndex = () => setPage('index');
export const navigateToHelp = () => setPage('help');

export default slice.reducer;
