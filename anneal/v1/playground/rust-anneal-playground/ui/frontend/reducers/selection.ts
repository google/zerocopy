import { PayloadAction, createSlice } from '@reduxjs/toolkit';

import { Position, Selection } from '../types';

const initialState: Selection = {};

const slice = createSlice({
  name: 'selection',
  initialState,
  reducers: {
    selectText: {
      reducer: (_state, action: PayloadAction<Selection>) => action.payload,

      prepare: (start: Position, end: Position) => ({ payload: { start, end } }),
    },
  },
});

export const { selectText } = slice.actions;

export default slice.reducer;
