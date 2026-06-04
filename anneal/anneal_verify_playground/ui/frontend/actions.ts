import { ThunkAction as ReduxThunkAction, UnknownAction } from '@reduxjs/toolkit';

import { State } from './reducers';
import { addCrateType, editCode } from './reducers/code';
import {
  changeBacktrace,
  changeChannel,
  changeEdition,
  changeMode,
  changePrimaryAction,
} from './reducers/configuration';
import { performCompileToAssemblyOnly } from './reducers/output/assembly';
import { performCommonExecute } from './reducers/output/execute';
import { performGistLoad } from './reducers/output/gist';
import { performCompileToHirOnly } from './reducers/output/hir';
import { performCompileToLlvmIrOnly } from './reducers/output/llvmIr';
import { performCompileToMirOnly } from './reducers/output/mir';
import { performCompileToWasmOnly } from './reducers/output/wasm';
import { navigateToHelp, navigateToIndex } from './reducers/page';
import { getCrateType, runAsTest, wasmLikelyToWork } from './selectors';
import {
  Backtrace,
  Channel,
  Edition,
  Mode,
  PrimaryAction,
  PrimaryActionAuto,
  PrimaryActionCore,
  parseChannel,
  parseEdition,
  parseMode,
} from './types';

export type ThunkAction<T = void> = ReduxThunkAction<T, State, unknown, UnknownAction>;

export const reExecuteWithBacktrace = (): ThunkAction => (dispatch) => {
  dispatch(changeBacktrace(Backtrace.Enabled));
  dispatch(performExecuteOnly());
};

function performAutoOnly(): ThunkAction {
  return function (dispatch, getState) {
    const state = getState();
    const crateType = getCrateType(state);
    const tests = runAsTest(state);

    return dispatch(performCommonExecute(crateType, tests));
  };
}

const performExecuteOnly = (): ThunkAction => performCommonExecute('bin', false);
const performCompileOnly = (): ThunkAction => performCommonExecute('lib', false);
const performTestOnly = (): ThunkAction => (dispatch, getState) => {
  const state = getState();
  const crateType = getCrateType(state);
  return dispatch(performCommonExecute(crateType, true));
};

const performCompileToNightlyHirOnly = (): ThunkAction => (dispatch) => {
  dispatch(changeChannel(Channel.Nightly));
  dispatch(performCompileToHirOnly());
};

const performCompileToCdylibWasmOnly = (): ThunkAction => (dispatch, getState) => {
  const state = getState();

  if (!wasmLikelyToWork(state)) {
    dispatch(addCrateType('cdylib'));
  }
  dispatch(performCompileToWasmOnly());
};
const performCargoAnnealOnly = (): ThunkAction => performCommonExecute('bin', false, 'anneal-verify');

const PRIMARY_ACTIONS: { [index in PrimaryAction]: () => ThunkAction } = {
  [PrimaryActionCore.Asm]: performCompileToAssemblyOnly,
  [PrimaryActionCore.Compile]: performCompileOnly,
  [PrimaryActionCore.Execute]: performExecuteOnly,
  [PrimaryActionCore.Test]: performTestOnly,
  [PrimaryActionAuto.Auto]: performAutoOnly,
  [PrimaryActionCore.LlvmIr]: performCompileToLlvmIrOnly,
  [PrimaryActionCore.Hir]: performCompileToHirOnly,
  [PrimaryActionCore.Mir]: performCompileToMirOnly,
  [PrimaryActionCore.Wasm]: performCompileToWasmOnly,
  [PrimaryActionCore.Anneal]: performCargoAnnealOnly,
};

export const performPrimaryAction = (): ThunkAction => (dispatch, getState) => {
  const state = getState();
  const primaryAction = PRIMARY_ACTIONS[state.configuration.primaryAction];
  dispatch(primaryAction());
};

const performAndSwitchPrimaryAction =
  (inner: () => ThunkAction, id: PrimaryAction) => (): ThunkAction => (dispatch) => {
    dispatch(changePrimaryAction(id));
    dispatch(inner());
  };

export const performExecute = performAndSwitchPrimaryAction(
  performExecuteOnly,
  PrimaryActionCore.Execute,
);
export const performCompile = performAndSwitchPrimaryAction(
  performCompileOnly,
  PrimaryActionCore.Compile,
);
export const performTest = performAndSwitchPrimaryAction(performTestOnly, PrimaryActionCore.Test);
export const performCompileToAssembly = performAndSwitchPrimaryAction(
  performCompileToAssemblyOnly,
  PrimaryActionCore.Asm,
);
export const performCompileToLLVM = performAndSwitchPrimaryAction(
  performCompileToLlvmIrOnly,
  PrimaryActionCore.LlvmIr,
);
export const performCompileToMir = performAndSwitchPrimaryAction(
  performCompileToMirOnly,
  PrimaryActionCore.Mir,
);
export const performCompileToNightlyHir = performAndSwitchPrimaryAction(
  performCompileToNightlyHirOnly,
  PrimaryActionCore.Hir,
);
export const performCompileToWasm = performAndSwitchPrimaryAction(
  performCompileToCdylibWasmOnly,
  PrimaryActionCore.Wasm,
);
export const performCargoAnneal = performAndSwitchPrimaryAction(
  performCargoAnnealOnly,
  PrimaryActionCore.Anneal,
);

export function indexPageLoad({
  code,
  gist,
  version,
  mode: modeString,
  edition: editionString,
}: {
  code?: string;
  gist?: string;
  version?: string;
  mode?: string;
  edition?: string;
}): ThunkAction {
  return function (dispatch) {
    const channel = parseChannel(version) || Channel.Stable;
    const mode = parseMode(modeString) || Mode.Debug;
    let maybeEdition = parseEdition(editionString);

    dispatch(navigateToIndex());

    if (code || gist) {
      // We need to ensure that any links that predate the existence
      // of editions will *forever* pick 2015. However, if we aren't
      // loading code, then allow the edition to remain the default.
      if (!maybeEdition) {
        maybeEdition = Edition.Rust2015;
      }
    }

    const edition = maybeEdition || Edition.Rust2024;

    if (code) {
      dispatch(editCode(code));
    } else if (gist) {
      dispatch(performGistLoad({ id: gist, channel, mode, edition }));
    }

    dispatch(changeChannel(channel));
    dispatch(changeMode(mode));
    dispatch(changeEdition(edition));
  };
}

export const helpPageLoad = navigateToHelp;

export function showExample(code: string): ThunkAction {
  return function (dispatch) {
    dispatch(navigateToIndex());
    dispatch(changeChannel(Channel.Stable));
    dispatch(changeMode(Mode.Debug));
    dispatch(changeEdition(Edition.Rust2024));
    dispatch(editCode(code));
  };
}
