import { PayloadAction, createSlice } from '@reduxjs/toolkit';

import { Position } from '../types';

const initialState: Position = {
  line: 0,
  column: 0,
};

const slice = createSlice({
  name: 'position',
  initialState,
  reducers: {
    gotoPosition: (_state, action: PayloadAction<Position>) => {
      return action.payload;
    },
  },
});

export const { gotoPosition } = slice.actions;

export default slice.reducer;
