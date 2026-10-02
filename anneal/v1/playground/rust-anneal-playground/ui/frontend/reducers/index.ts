import { combineReducers } from '@reduxjs/toolkit';

import browser from './browser';
import client from './client';
import code from './code';
import configuration from './configuration';
import crates from './crates';
import featureFlags from './featureFlags';
import globalConfiguration from './globalConfiguration';
import notifications from './notifications';
import output from './output';
import page from './page';
import position from './position';
import selection from './selection';
import versions from './versions';
import websocket from './websocket';

const playgroundApp = combineReducers({
  browser,
  client,
  code,
  configuration,
  crates,
  featureFlags,
  globalConfiguration,
  notifications,
  output,
  page,
  position,
  selection,
  versions,
  websocket,
});

export type State = ReturnType<typeof playgroundApp>;

export default playgroundApp;
