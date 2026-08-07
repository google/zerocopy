import { PayloadAction, createSlice } from '@reduxjs/toolkit';

const NOW_TIMESTAMP = new Date().toISOString();

interface State {
  id: string;
  featureFlagThreshold: number;
  lastVisitedAt?: string;
  visitedAt?: string;
  showConfigReset: boolean;
  resetEverything: boolean;
}

const initialState: State = {
  id: '',
  featureFlagThreshold: 1.0,
  showConfigReset: false,
  resetEverything: false,
};

const slice = createSlice({
  name: 'client',
  initialState,
  reducers: {
    setIdentifiers: (
      state,
      action: PayloadAction<{ id: string; featureFlagThreshold: number }>,
    ) => {
      state.id = action.payload.id;
      state.featureFlagThreshold = action.payload.featureFlagThreshold;
    },

    updateLastVisitedAt: (state) => {
      state.lastVisitedAt = state.visitedAt;
      state.visitedAt = NOW_TIMESTAMP;
    },

    showConfigReset: (state) => {
      state.showConfigReset = true;
    },

    hideConfigReset: (state) => {
      state.showConfigReset = false;
    },

    resetEverything: (state) => {
      state.resetEverything = true;
    },
  },
});

export const {
  setIdentifiers,
  updateLastVisitedAt,
  showConfigReset,
  hideConfigReset,
  resetEverything,
} = slice.actions;

export default slice.reducer;
