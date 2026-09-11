import { PayloadAction, createSlice } from '@reduxjs/toolkit';

import { performFormat } from './output/format';
import { performGistLoad } from './output/gist';

const initialState: string = `fn main() {
    println!("Hello, world!");
}`;

const slice = createSlice({
  name: 'code',
  initialState,
  reducers: {
    editCode: (_state, action: PayloadAction<string>) => action.payload,

    addMainFunction: (state) => `${state}\n\n${initialState}`,

    addImport: (state, action: PayloadAction<string>) => action.payload + state,

    addCrateType: (state, action: PayloadAction<string>) =>
      `#![crate_type = "${action.payload}"]\n${state}`,

    enableFeatureGate: (state, action: PayloadAction<string>) =>
      `#![feature(${action.payload})]\n${state}`,
  },
  extraReducers: (builder) => {
    builder
      .addCase(performGistLoad.pending, () => '')
      .addCase(performGistLoad.fulfilled, (_state, action) => action.payload.code)
      .addCase(performFormat.fulfilled, (_state, action) => action.payload.code);
  },
});

export const { editCode, addMainFunction, addImport, addCrateType, enableFeatureGate } =
  slice.actions;

export default slice.reducer;
