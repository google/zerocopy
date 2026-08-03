// This is used to store "long-term" values; those which we want to be
// preserved between completely independent sessions of the
// playground.
import * as z from 'zod';

import { State } from './reducers';
import { codeSelector } from './selectors';
import { PartialState, initializeStorage, removeVersion } from './storage';
import {
  AssemblyFlavorSchema,
  DemangleAssemblySchema,
  Editor,
  EditorSchema,
  OrientationSchema,
  PairCharactersSchema,
  ProcessAssemblySchema,
  Theme,
  ThemeSchema,
} from './types';

const CURRENT_VERSION = 2;

const V2Configuration = z
  .object({
    version: z.literal(2),
    client: z
      .object({
        id: z.string(),
        featureFlagThreshold: z.number(),
        visitedAt: z.string(),
      })
      .partial(),
    configuration: z
      .object({
        editor: EditorSchema,
        ace: z
          .object({
            keybinding: z.string(),
            theme: z.string(),
            pairCharacters: PairCharactersSchema,
          })
          .partial(),
        monaco: z
          .object({
            theme: z.string(),
          })
          .partial(),
        theme: ThemeSchema,
        orientation: OrientationSchema,
        assemblyFlavor: AssemblyFlavorSchema,
        demangleAssembly: DemangleAssemblySchema,
        processAssembly: ProcessAssemblySchema,
      })
      .partial(),
    code: z.string(),
    notifications: z.looseObject({}),
  })
  .partial();
type V2Configuration = z.infer<typeof V2Configuration>;

const V1Configuration = z
  .object({
    version: z.literal(1),
    configuration: z
      .object({
        editor: z.enum(['simple', 'advanced']),
        keybinding: z.string(),
        theme: z.string(),
        pairCharacters: PairCharactersSchema,
        orientation: OrientationSchema,
        assemblyFlavor: AssemblyFlavorSchema,
        demangleAssembly: DemangleAssemblySchema,
        processAssembly: ProcessAssemblySchema,
      })
      .partial(),
    code: z.string(),
    notifications: z.looseObject({}),
  })
  .partial();
type V1Configuration = z.infer<typeof V1Configuration>;

type CurrentConfiguration = V2Configuration;

const SomeConfiguration = V1Configuration.or(V2Configuration);

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
    notifications: { ...state.notifications },
  };
  return JSON.stringify(conf);
}

const MIGRATION_TIMESTAMP = '2021-08-21T21:51:05.000Z';

function migrateV1(state: V1Configuration): CurrentConfiguration {
  const { editor, theme, keybinding, pairCharacters, ...configuration } = state.configuration ?? {};
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
    case 1:
      return migrateV1(state);
    case 2:
      return migrateV2(state);
    default:
      return undefined;
  }
}

export function deserialize(savedState: string): PartialState {
  try {
    const parsedState = JSON.parse(savedState);

    const validatedState = SomeConfiguration.parse(parsedState);

    const result = migrate(validatedState);
    if (!result) {
      return undefined;
    }

    return removeVersion(result);
  } catch {
    return undefined;
  }
}

export default initializeStorage({
  storageFactory: () => localStorage,
  serialize,
  deserialize,
});
