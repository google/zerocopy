import { PayloadAction, createSlice } from '@reduxjs/toolkit';

const initialState: State = {
  isSmall: true,
};

type State = {
  isSmall: boolean;
};

const slice = createSlice({
  name: 'browser',
  initialState,
  reducers: {
    browserWidthChanged: (state, action: PayloadAction<boolean>) => {
      state.isSmall = action.payload;
    },
  },
});

export const { browserWidthChanged } = slice.actions;

export default slice.reducer;
