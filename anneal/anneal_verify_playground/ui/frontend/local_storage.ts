// This is used to store "long-term" values; those which we want to be
// preserved between completely independent sessions of the
// playground.

import { State } from './reducers';
import {removeVersion, initializeStorage, PartialState} from './storage';
import { AssemblyFlavor, DemangleAssembly, Editor, Orientation, PairCharacters, ProcessAssembly, Theme } from './types';
import { codeSelector } from './selectors';

const CURRENT_VERSION = 2;

interface V2Configuration {
  version: 2;
  client: {
    id: string;
    featureFlagThreshold: number;
    visitedAt?: string;
  };
  configuration: {
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
  };
  code: string;
  notifications: object;
}

interface V1Configuration {
  version: 1;
  configuration: {
    editor: 'simple' | 'advanced';
    keybinding: string;
    theme: string;
    pairCharacters: PairCharacters;
    orientation: Orientation;
    assemblyFlavor: AssemblyFlavor;
    demangleAssembly: DemangleAssembly;
    processAssembly: ProcessAssembly;
  };
  code: string;
  notifications: object;
}

type CurrentConfiguration = V2Configuration;

export function serialize(state: State): string {
  const code = codeSelector(state);
  const conf: CurrentConfiguration = {
    version: CURRENT_VERSION,
    client: {
      id: state.client.id,
      featureFlagThreshold: state.client.featureFlagThreshold,
      visitedAt: state.client.visitedAt,
    },
    configuration: {
      editor: state.configuration.editor,
      ace: {
        keybinding: state.configuration.ace.keybinding,
        theme: state.configuration.ace.theme,
        pairCharacters: state.configuration.ace.pairCharacters,
      },
      monaco: {
        theme: state.configuration.monaco.theme,
      },
      theme: state.configuration.theme,
      orientation: state.configuration.orientation,
      assemblyFlavor: state.configuration.assemblyFlavor,
      demangleAssembly: state.configuration.demangleAssembly,
      processAssembly: state.configuration.processAssembly,
    },
    code,
    notifications: state.notifications,
  };
  return JSON.stringify(conf);
}

const MIGRATION_TIMESTAMP = '2021-08-21T21:51:05.000Z';

function migrateV1(state: V1Configuration): CurrentConfiguration {
  const { editor, theme, keybinding, pairCharacters, ...configuration } = state.configuration;
  const step: V2Configuration = {
    ...state,
    client: {
      id: '',
      featureFlagThreshold: 0,
      visitedAt: MIGRATION_TIMESTAMP,
    },
    configuration: {
      ...configuration,
      ace: { theme, keybinding, pairCharacters },
      monaco: { theme: 'vs-dark' },
      theme: Theme.System,
      editor: editor === 'advanced' ? Editor.Ace : Editor.Simple,
    },
    version: 2,
  };
  return migrateV2(step);
}

function migrateV2(state: V2Configuration): CurrentConfiguration {
  return state;
}

function migrate(state: V1Configuration | V2Configuration): CurrentConfiguration | undefined {
  switch (state.version) {
    case 1: return migrateV1(state);
    case 2: return migrateV2(state);
    default: return undefined
  }
}

export function deserialize(savedState: string): PartialState {
  if (!savedState) { return undefined; }

  const parsedState = JSON.parse(savedState);
  if (!parsedState) { return undefined; }

  const result = migrate(parsedState);
  if (!result) { return undefined; }

  return removeVersion(result);
}

export default initializeStorage({
  storageFactory: () => localStorage,
  serialize,
  deserialize,
});
