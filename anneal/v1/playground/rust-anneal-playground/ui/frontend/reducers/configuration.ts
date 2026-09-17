import { PayloadAction, createSlice } from '@reduxjs/toolkit';

import {
  AliasingModel,
  AssemblyFlavor,
  Backtrace,
  Channel,
  DemangleAssembly,
  Edition,
  Editor,
  Mode,
  Orientation,
  PairCharacters,
  PrimaryAction,
  PrimaryActionAuto,
  ProcessAssembly,
  Theme,
} from '../types';

interface State {
  editor: Editor;
  ace: {
    keybinding: string;
    theme: string;
    pairCharacters: PairCharacters;
  };
  monaco: {
    theme: string;
  };
  theme: Theme;
  orientation: Orientation;
  assemblyFlavor: AssemblyFlavor;
  demangleAssembly: DemangleAssembly;
  processAssembly: ProcessAssembly;
  primaryAction: PrimaryAction;
  channel: Channel;
  mode: Mode;
  edition: Edition;
  backtrace: Backtrace;
  aliasingModel: AliasingModel;
}

const initialState: State = {
  editor: Editor.Ace,
  ace: {
    keybinding: 'ace',
    theme: 'github',
    pairCharacters: PairCharacters.Enabled,
  },
  monaco: {
    theme: 'vs',
  },
  theme: Theme.System,
  orientation: Orientation.Automatic,
  assemblyFlavor: AssemblyFlavor.Att,
  demangleAssembly: DemangleAssembly.Demangle,
  processAssembly: ProcessAssembly.Filter,
  primaryAction: PrimaryActionAuto.Auto,
  channel: Channel.Stable,
  mode: Mode.Debug,
  edition: Edition.Rust2024,
  backtrace: Backtrace.Disabled,
  aliasingModel: AliasingModel.Stacked,
};

const slice = createSlice({
  name: 'configuration',
  initialState,
  reducers: {
    changeAceTheme: (state, action: PayloadAction<string>) => {
      state.ace.theme = action.payload;
    },

    changeAssemblyFlavor: (state, action: PayloadAction<AssemblyFlavor>) => {
      state.assemblyFlavor = action.payload;
    },

    changeBacktrace: (state, action: PayloadAction<Backtrace>) => {
      state.backtrace = action.payload;
    },

    changeAliasingModel: (state, action: PayloadAction<AliasingModel>) => {
      state.aliasingModel = action.payload;
    },

    changeChannel: (state, action: PayloadAction<Channel>) => {
      state.channel = action.payload;
    },

    changeDemangleAssembly: (state, action: PayloadAction<DemangleAssembly>) => {
      state.demangleAssembly = action.payload;
    },

    changeEdition: (state, action: PayloadAction<Edition>) => {
      state.edition = action.payload;
    },

    changeEditor: (state, action: PayloadAction<Editor>) => {
      state.editor = action.payload;
    },

    changeKeybinding: (state, action: PayloadAction<string>) => {
      state.ace.keybinding = action.payload;
    },

    changeMode: (state, action: PayloadAction<Mode>) => {
      state.mode = action.payload;
    },

    changeMonacoTheme: (state, action: PayloadAction<string>) => {
      state.monaco.theme = action.payload;
    },

    changeTheme: (state, action: PayloadAction<Theme>) => {
      state.theme = action.payload;
    },

    changeOrientation: (state, action: PayloadAction<Orientation>) => {
      state.orientation = action.payload;
    },

    changePairCharacters: (state, action: PayloadAction<PairCharacters>) => {
      state.ace.pairCharacters = action.payload;
    },

    changePrimaryAction: (state, action: PayloadAction<PrimaryAction>) => {
      state.primaryAction = action.payload;
    },

    changeProcessAssembly: (state, action: PayloadAction<ProcessAssembly>) => {
      state.processAssembly = action.payload;
    },

    swapTheme: (state, action: PayloadAction<Theme>) => {
      state.theme = action.payload;
      switch (action.payload) {
        case Theme.Light: {
          state.ace.theme = 'github';
          state.monaco.theme = 'vs';
          break;
        }
        case Theme.Dark: {
          state.ace.theme = 'github_dark';
          state.monaco.theme = 'vs-dark';
          break;
        }
      }
    },
  },
});

export const {
  changeAceTheme,
  changeAssemblyFlavor,
  changeBacktrace,
  changeAliasingModel,
  changeChannel,
  changeDemangleAssembly,
  changeEdition,
  changeEditor,
  changeKeybinding,
  changeMode,
  changeMonacoTheme,
  changeTheme,
  changeOrientation,
  changePairCharacters,
  changePrimaryAction,
  changeProcessAssembly,
  swapTheme,
} = slice.actions;

export default slice.reducer;
