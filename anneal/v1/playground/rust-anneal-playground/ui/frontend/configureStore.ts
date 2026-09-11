import { configureStore as reduxConfigureStore } from '@reduxjs/toolkit';
import { produce } from 'immer';
import { merge } from 'lodash-es';

import initializeLocalStorage from './local_storage';
import { observer } from './observer';
import reducer from './reducers';
import initializeSessionStorage from './session_storage';
import { websocketMiddleware } from './websocketMiddleware';

const editorDarkThemes = {
  configuration: {
    ace: {
      theme: 'github_dark',
    },
    monaco: {
      theme: 'vs-dark',
    },
  },
};

export default function configureStore(window: Window) {
  const baseUrl = new URL('/', window.location.href).href;
  const websocket = websocketMiddleware(window);

  const prefersDarkTheme = window.matchMedia('(prefers-color-scheme: dark)').matches;
  const initialThemes = prefersDarkTheme ? editorDarkThemes : {};

  const initialGlobalState = {
    globalConfiguration: {
      baseUrl,
    },
  };
  const initialAppState = reducer(undefined, { type: 'initializeForStore' });

  const localStorage = initializeLocalStorage();
  const sessionStorage = initializeSessionStorage();

  const preloadedState = produce(initialAppState, (initialAppState) =>
    merge(
      initialAppState,
      initialGlobalState,
      initialThemes,
      localStorage.initialState,
      sessionStorage.initialState,
    ),
  );

  const store = reduxConfigureStore({
    reducer,
    preloadedState,
    middleware: (getDefaultMiddleware) =>
      getDefaultMiddleware().concat(websocket).prepend(observer.middleware),
  });

  store.subscribe(() => {
    const state = store.getState();

    // Some automated tests run fast enough that the following interleaving is possible:
    //
    // 1. RSpec test finishes, local/session storage cleared
    // 2. WebSocket connects, the state updates, and the local/session storage is saved
    // 3. Subsequent RSpec test starts and local/session storage has been preserved
    //
    // We allow the tests to stop saving to sidestep that.
    if (state.globalConfiguration.syncChangesToStorage) {
      localStorage.saveChanges(state);
      sessionStorage.saveChanges(state);
    }

    if (state.client.resetEverything) {
      localStorage.clear();
      sessionStorage.clear();

      // This removes any query parameters and triggers all the
      // initialization
      window.location = state.globalConfiguration.baseUrl;
    }
  });

  return store;
}

export type AppDispatch = ReturnType<typeof configureStore>['dispatch'];
