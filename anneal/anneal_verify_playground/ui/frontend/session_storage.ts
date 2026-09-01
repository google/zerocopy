// This is used to store "short-term" values; those which we want to
// be preserved between the same sessions of the playground, such as
// when we reopen a closed tab.

import { State } from './reducers';
import {removeVersion, initializeStorage, PartialState} from './storage';
import { codeSelector } from './selectors';

const CURRENT_VERSION = 1;

export function serialize(state: State): string {
  const code = codeSelector(state);

  return JSON.stringify({
    version: CURRENT_VERSION,
    configuration: {
      primaryAction: state.configuration.primaryAction,
    },
    code,
  });
}

export function deserialize(savedState: string): PartialState {
  if (!savedState) { return undefined; }

  const parsedState = JSON.parse(savedState);
  if (!parsedState) { return undefined; }

  if (parsedState.version !== CURRENT_VERSION) { return undefined; }

  // This assumes that the keys we serialize with match the keys in the
  // live state. If that's no longer true, an additional renaming step
  // needs to be added.

  return removeVersion(parsedState);
}

export default initializeStorage({
  storageFactory: () => sessionStorage,
  serialize,
  deserialize,
});
