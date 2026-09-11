import 'core-js';

import 'normalize.css/normalize.css';
import './index.module.css';

import React from 'react';
import { createRoot } from 'react-dom/client';
import { Provider } from 'react-redux';
import { v4 } from 'uuid';

import {
  reExecuteWithBacktrace,
} from './actions';
import { configureRustErrors } from './highlighting';
import PageSwitcher from './PageSwitcher';
import playgroundApp from './reducers';
import * as client from './reducers/client';
import { featureFlagsForceDisableAll, featureFlagsForceEnableAll } from './reducers/featureFlags';
import { disableSyncChangesToStorage, override } from './reducers/globalConfiguration';
import Router from './Router';
import configureStore from './configureStore';
import { performVersionsLoad } from './reducers/versions';
import { performCratesLoad } from './reducers/crates';
import { gotoPosition } from './reducers/position';
import { addImport, editCode, enableFeatureGate } from './reducers/code';
import { browserWidthChanged } from './reducers/browser';
import { selectText } from './reducers/selection';
import { useAppSelector } from './hooks';
import { themeSelector } from './selectors';
import { Theme } from './types';

const store = configureStore(window);

store.dispatch(client.updateLastVisitedAt());

if (store.getState().client.id === '') {
  const { crypto } = window;

  const id = v4();

  const rawValue = new Uint32Array(1);
  crypto.getRandomValues(rawValue);
  const featureFlagThreshold = rawValue[0] / 0xFFFF_FFFF;

  store.dispatch(client.setIdentifiers({ id, featureFlagThreshold }));
}

const params = new URLSearchParams(window.location.search);
if (params.has('features')) {
  const selection = params.get('features');
  if (selection === 'false') {
    store.dispatch(featureFlagsForceDisableAll());
  } else {
    store.dispatch(featureFlagsForceEnableAll());
  }
}
const configOverrides = params.get('whte_rbt.obj');
if (configOverrides) {
  store.dispatch(override(configOverrides));
}

const whenBrowserWidthChanged = (evt: MediaQueryList | MediaQueryListEvent) =>
  store.dispatch(browserWidthChanged(evt.matches));
const maxWidthMediaQuery = window.matchMedia('(max-width: 1600px)');

whenBrowserWidthChanged(maxWidthMediaQuery);
maxWidthMediaQuery.addEventListener('change', whenBrowserWidthChanged);

configureRustErrors({
  enableFeatureGate: featureGate => store.dispatch(enableFeatureGate(featureGate)),
  gotoPosition: (p) => store.dispatch(gotoPosition(p)),
  selectText: (start, end) => store.dispatch(selectText(start, end)),
  addImport: (code) => store.dispatch(addImport(code)),
  reExecuteWithBacktrace: () => store.dispatch(reExecuteWithBacktrace()),
  getChannel: () => store.getState().configuration.channel,
});

store.dispatch(performCratesLoad());
store.dispatch(performVersionsLoad());

window.rustPlayground = {
  setCode: code => {
    store.dispatch(editCode(code));
  },
  disableSyncChangesToStorage: () => {
    store.dispatch(disableSyncChangesToStorage());
  },
};

const ThemeProvider: React.FC<React.PropsWithChildren> = ({ children }) => {
  const theme = useAppSelector(themeSelector);
  React.useEffect(() => {
    if (theme === Theme.System) {
      delete document.documentElement.dataset['theme'];
    } else {
      document.documentElement.dataset['theme'] = theme;
    }
  }, [theme]);

  return <>{children}</>;
};

const container = document.getElementById('playground');
if (container) {
  const root = createRoot(container);
  root.render(
    <Provider store={store}>
      <Router store={store} reducer={playgroundApp}>
        <ThemeProvider>
          <PageSwitcher />
        </ThemeProvider>
      </Router>
    </Provider>,
  );
}
