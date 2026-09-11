// This is used to store "short-term" values; those which we want to
// be preserved between the same sessions of the playground, such as
// when we reopen a closed tab.
import * as z from 'zod';

import { State } from './reducers';
import { codeSelector } from './selectors';
import { PartialState, initializeStorage, removeVersion } from './storage';
import { PrimaryActionSchema } from './types';

const CURRENT_VERSION = 1;

const V1Schema = z
  .object({
    version: z.literal(1),
    configuration: z
      .object({
        primaryAction: PrimaryActionSchema,
      })
      .partial(),
    code: z.string(),
  })
  .partial();
type V1Schema = z.infer<typeof V1Schema>;

export function serialize(state: State): string {
  const value: V1Schema = {
    version: CURRENT_VERSION,
    configuration: {
      primaryAction: state.configuration.primaryAction,
    },
    code: codeSelector(state),
  };

  return JSON.stringify(V1Schema.parse(value));
}

export function deserialize(savedState: string): PartialState {
  try {
    const parsedState = JSON.parse(savedState);
    const validatedState = V1Schema.parse(parsedState);

    // This assumes that the keys we serialize with match the keys in the
    // live state. If that's no longer true, an additional renaming step
    // needs to be added.

    return removeVersion(validatedState);
  } catch {
    return undefined;
  }
}

export default initializeStorage({
  storageFactory: () => sessionStorage,
  serialize,
  deserialize,
});
