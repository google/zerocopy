import { createSelector } from '@reduxjs/toolkit';

import { State } from '../reducers';
import {
  Backtrace,
  Channel,
  Edition,
  AliasingModel,
  Focus,
  Orientation,
  PrimaryActionAuto,
  PrimaryActionCore,
  Version,
} from '../types';

import { ExecutionTool } from '../reducers/output/execute';

const MS_PER_S = 1000;

const featureFlags = (state: State) => state.featureFlags;
const clientFeatureFlagThreshold = (state: State) => state.client.featureFlagThreshold;

const createFeatureFlagSelector = (ff: (state: State) => number) =>
  createSelector(clientFeatureFlagThreshold, ff, (c, ff) => c <= ff);

export const codeSelector = (state: State) => state.code;
export const positionSelector = (state: State) => state.position;
export const selectionSelector = (state: State) => state.selection;

const HAS_TESTS_RE = /^\s*#\s*\[\s*test\s*([^"]*)]/m;
const hasTests = (code: string) => !!code.match(HAS_TESTS_RE);
const hasTestsSelector = createSelector(codeSelector, hasTests);

// https://stackoverflow.com/a/34755045/155423
const HAS_MAIN_FUNCTION_RE = new RegExp(
  [
    /^([^\n\r/]*;)?/,
    /\s*(pub\s+)?\s*(const\s+)?\s*(async\s+)?\s*/,
    /fn\s+main\s*\(\s*(\/\*.*\*\/)?\s*\)/,
  ].map((r) => r.source).join(''),
  'm'
);
export const hasMainFunction = (code: string) => !!code.match(HAS_MAIN_FUNCTION_RE);
const hasMainFunctionSelector = createSelector(codeSelector, hasMainFunction);

const CRATE_TYPE_RE = /^\s*#!\s*\[\s*crate_type\s*=\s*"([^"]*)"\s*]/m;
const crateType = (code: string) => (code.match(CRATE_TYPE_RE) ?? []).at(1);
const crateTypeSelector = createSelector(codeSelector, crateType);

const autoPrimaryActionSelector = createSelector(
  crateTypeSelector,
  hasTestsSelector,
  hasMainFunctionSelector,
  (crateType, hasTests, hasMainFunction) => {
    if (crateType && crateType !== 'proc-macro') {
      if (crateType === 'bin') {
        return PrimaryActionCore.Execute;
      } else {
        return PrimaryActionCore.Compile;
      }
    } else {
      if (hasTests) {
        return PrimaryActionCore.Test;
      } else if (hasMainFunction) {
        return PrimaryActionCore.Execute;
      } else {
        return PrimaryActionCore.Compile;
      }
    }
  },
);

export const runAsTest = createSelector(
  autoPrimaryActionSelector,
  primaryAction => primaryAction === PrimaryActionCore.Test,
);

export const getCrateType = createSelector(
  crateTypeSelector,
  autoPrimaryActionSelector,
  (crateType, primaryAction) => {
    if (crateType) {
      return crateType;
    } else if (primaryAction === PrimaryActionCore.Execute) {
      return 'bin';
    } else {
      return 'lib';
    }
  },
);

const rawPrimaryActionSelector = (state: State) => state.configuration.primaryAction;

export const isAutoBuildSelector = createSelector(
  rawPrimaryActionSelector,
  autoPrimaryActionSelector,
  (primaryAction, autoPrimaryAction) => (
    primaryAction === PrimaryActionAuto.Auto && autoPrimaryAction === PrimaryActionCore.Compile
  ),
);

const primaryActionSelector = createSelector(
  rawPrimaryActionSelector,
  autoPrimaryActionSelector,
  (primaryAction, autoPrimaryAction): PrimaryActionCore => (
    primaryAction === PrimaryActionAuto.Auto ? autoPrimaryAction : primaryAction
  ),
);

const LABELS: { [index in PrimaryActionCore]: string } = {
  [PrimaryActionCore.Asm]: 'Show Assembly',
  [PrimaryActionCore.Compile]: 'Build',
  [PrimaryActionCore.Execute]: 'Run',
  [PrimaryActionCore.LlvmIr]: 'Show LLVM IR',
  [PrimaryActionCore.Hir]: 'Show HIR',
  [PrimaryActionCore.Mir]: 'Show MIR',
  [PrimaryActionCore.Test]: 'Test',
  [PrimaryActionCore.Wasm]: 'Show Wasm',
  [PrimaryActionCore.Anneal]: 'Anneal',
};

export const getExecutionLabel = createSelector(primaryActionSelector, primaryAction => LABELS[primaryAction]);

const channelSelector = (state: State) => state.configuration.channel;

const selectedChannelVersionsSelector = createSelector(
  channelSelector,
  (state: State) => state.versions,
  (channel, versions) => {
    switch (channel) {
      case Channel.Stable:
        return versions.stable;
      case Channel.Beta:
        return versions.beta;
      case Channel.Nightly:
        return versions.nightly;
    }
  },
)

const getStable = (state: State) => state.versions.stable?.rustc;
const getBeta = (state: State) => state.versions.beta?.rustc;
const getNightly = (state: State) => state.versions.nightly?.rustc;
const getRustfmt = createSelector(selectedChannelVersionsSelector, (versions) => versions?.rustfmt);
const getClippy = createSelector(selectedChannelVersionsSelector, (versions) => versions?.clippy);
const getMiri = (state: State) => state.versions?.nightly?.miri;

const versionNumber = (v: Version | undefined) => v ? v.version : '';
export const stableVersionText = createSelector(getStable, versionNumber);
export const betaVersionText = createSelector(getBeta, versionNumber);
export const nightlyVersionText = createSelector(getNightly, versionNumber);
export const clippyVersionText = createSelector(getClippy, versionNumber);
export const rustfmtVersionText = createSelector(getRustfmt, versionNumber);
export const miriVersionText = createSelector(getMiri, versionNumber);

const versionDetails = (v: Version | undefined) => v ? `${v.date} ${v.hash.slice(0, 20)}` : '';
export const betaVersionDetailsText = createSelector(getBeta, versionDetails);
export const nightlyVersionDetailsText = createSelector(getNightly, versionDetails);
export const clippyVersionDetailsText = createSelector(getClippy, versionDetails);
export const rustfmtVersionDetailsText = createSelector(getRustfmt, versionDetails);
export const miriVersionDetailsText = createSelector(getMiri, versionDetails);

const editionSelector = (state: State) => state.configuration.edition;
export const aliasingModelSelector = (state: State) => state.configuration.aliasingModel;

export const isNightlyChannel = createSelector(
  channelSelector,
  (channel) => channel === Channel.Nightly,
);
export const isHirAvailable = isNightlyChannel;

export const wasmLikelyToWork = createSelector(
  crateTypeSelector,
  getCrateType, (userCrateType, crateType) => {
    // If the user set it already, assume they know what they are doing
    if (userCrateType) { return true }

    return crateType === 'cdylib';
  });

export const getModeLabel = (state: State) => {
  const { configuration: { mode } } = state;
  return `${mode}`;
};

export const getChannelLabel = createSelector(channelSelector, (channel) => `${channel}`);

export const isEditionDefault = createSelector(
  editionSelector,
  edition => edition === Edition.Rust2024,
);

export const isBacktraceDefault = (state: State) => (
  state.configuration.backtrace === Backtrace.Disabled
);

export const getBacktraceSet = createSelector(isBacktraceDefault, (b) => !b);

export const isAliasingModelDefault = createSelector(
  aliasingModelSelector,
  aliasingModel => aliasingModel == AliasingModel.Stacked,
);

export const getAdvancedOptionsSet = createSelector(
  isEditionDefault, isBacktraceDefault, isAliasingModelDefault,
  (...areDefault) => !areDefault.every(n => n),
);

export const hasProperties = (obj: object) => Object.values(obj).some(val => !!val);

const getOutputs = createSelector(
  (state: State) => state,
  (state) => [
    state.output.assembly,
    state.output.clippy,
    state.output.execute,
    state.output.format,
    state.output.gist,
    state.output.llvmIr,
    state.output.mir,
    state.output.hir,
    state.output.miri,
    state.output.macroExpansion,
    state.output.wasm,
  ],
);

export const getSomethingToShow = createSelector(
  getOutputs,
  a => a.some(hasProperties),
);

export const baseUrlSelector = (state: State) =>
  state.globalConfiguration.baseUrl;

const excessiveExecutionTimeSSelector = (state: State) =>
  state.globalConfiguration.excessiveExecutionTimeS;

const killGracePeriodSSelector = (state: State) =>
  state.globalConfiguration.killGracePeriodS;

export const killGracePeriodMsSelector = createSelector(
  killGracePeriodSSelector,
  (t) => t * MS_PER_S,
);

const oldConfigurationThresholdSSelector = (state: State) =>
  state.globalConfiguration.oldConfigurationThresholdS;

const oldConfigurationThresholdMsSelector = createSelector(
  oldConfigurationThresholdSSelector,
  (t) => t * MS_PER_S,
);

const formatSeconds = (seconds: number) => {
  if (seconds === 1) {
    return '1 second';
  } else if (seconds % 1 === 0) {
    return `${seconds.toFixed(0)} seconds`;
  } else {
    return `${seconds.toFixed(1)} seconds`;
  }
};

export const excessiveExecutionTimeSelector = createSelector(
  excessiveExecutionTimeSSelector,
  formatSeconds,
);

export const killGracePeriodTimeSelector = createSelector(
  killGracePeriodSSelector,
  formatSeconds,
);

export const currentExecutionSequenceNumberSelector = (state: State) =>
  state.output.execute.sequenceNumber;

export const excessiveExecutionSelector = createSelector(
  (state: State) => state.output.execute,
  excessiveExecutionTimeSSelector,
  (e, limit) =>
    e.requestsInProgress > 0 &&
    !e.allowLongRun &&
    (e.totalTimeSecs ?? 0.0) >= limit,
);

export const resetConfigurationSelector = (state: State) => state.client.showConfigReset;

const parseMaybeISO = (s?: string): Date | undefined => {
  if (!s) {
    return undefined;
  }
  try {
    return new Date(s);
  } catch {
    return undefined;
  }
};

const lastVisitStrSelector = (state: State) => state.client.lastVisitedAt;
const currVisitStrSelector = (state: State) => state.client.visitedAt;

const lastVisitSelector = createSelector(lastVisitStrSelector, parseMaybeISO);
const currVisitSelector = createSelector(currVisitStrSelector, parseMaybeISO);

export const resetOldConfigurationSelector = createSelector(
  lastVisitSelector,
  currVisitSelector,
  oldConfigurationThresholdMsSelector,
  (last, current, thresholdMs) => {
    if (last && current) {
      const deltaTimeMs = current.getTime() - last.getTime();
      return deltaTimeMs > thresholdMs;
    } else {
      return false;
    }
  }
);


const notificationsSelector = (state: State) => state.notifications;

const NOW = new Date();

const RUST_SURVEY_2025_END = new Date('2025-12-17T00:00:00Z');
const RUST_SURVEY_2025_OPEN = NOW <= RUST_SURVEY_2025_END;
export const showRustSurvey2025Selector = createSelector(
  notificationsSelector,
  notifications => RUST_SURVEY_2025_OPEN && !notifications.seenRustSurvey2025,
);

export const anyNotificationsToShowSelector = createSelector(
  showRustSurvey2025Selector,
  excessiveExecutionSelector,
  resetConfigurationSelector,
  resetOldConfigurationSelector,
  (...allNotifications) => allNotifications.some(n => n),
);

export const clippyRequestSelector = createSelector(
  channelSelector,
  getCrateType,
  editionSelector,
  codeSelector,
  (channel, crateType, edition, code) => ({ channel, crateType, edition, code }),
);

export const formatRequestSelector = createSelector(
  channelSelector,
  editionSelector,
  codeSelector,
  (channel, edition, code) => ({ channel, edition, code }),
);

export const miriRequestSelector = createSelector(
  editionSelector,
  runAsTest,
  aliasingModelSelector,
  codeSelector,
  (edition, tests, aliasingModel, code, ) => ({ edition, tests, aliasingModel, code }),
);

export const macroExpansionRequestSelector = createSelector(
  editionSelector,
  codeSelector,
  (edition, code) => ({ edition, code })
);

const focus = (state: State) => state.output.meta.focus;
export const isOutputFocused = createSelector(
  focus,
  (focus) => !!focus,
);

export const showStdinSelector = createSelector(
  focus,
  (focus) => focus == Focus.Execute,
)
export const enableStdinSelector = createSelector(
  (state: State) => state.output.execute.requestsInProgress,
  (req) => req > 0,
)

const orientationConfig = (state: State) => state.configuration.orientation;
const browserWidthIsSmall = (state: State) => state.browser.isSmall;

export const orientation = createSelector(
  orientationConfig,
  browserWidthIsSmall,
  (orientation, widthIsSmall) => {
    if (orientation == Orientation.Automatic) {
      if (widthIsSmall) { return Orientation.Horizontal } else { return Orientation.Vertical }
    } else {
      return orientation;
    }
  }
)

const aceConfig = (s: State) => s.configuration.ace;
export const aceKeybinding = createSelector(aceConfig, c => c.keybinding);
export const acePairCharacters = createSelector(aceConfig, c => c.pairCharacters);
export const aceTheme = createSelector(aceConfig, c => c.theme);

export const offerCrateAutocompleteOnUse = createSelector(
  editionSelector,
  (edition) => edition !== Edition.Rust2015,
);

const websocket = (state: State) => state.websocket;

const showGemThreshold = createSelector(featureFlags, ff => ff.showGemThreshold);
export const showGemSelector = createFeatureFlagSelector(showGemThreshold);

export const executeViaWebsocketSelector = createSelector(websocket, (ws) => ws.connected);

export type WebSocketStatus =
  { state: 'disconnected' } |
  { state: 'connected' } |
  { state: 'error', error: string };

export const websocketStatusSelector = createSelector(
  websocket,
  (ws): WebSocketStatus => {
    if (ws.error) { return { state: 'error', error: ws.error }; }
    if (ws.connected) { return { state: 'connected' }; }
    return { state: 'disconnected' };
  }
);

export const executeRequestPayloadSelector = createSelector(
  codeSelector,
  channelSelector,
  (state: State) => state.configuration,
  getBacktraceSet,
  (_state: State, args: { crateType: string, tests: boolean, executionTool: ExecutionTool }) => args,
  (code, channel, configuration, backtrace, { crateType, tests, executionTool }) => ({
    channel,
    mode: configuration.mode,
    edition: configuration.edition,
    crateType,
    tests,
    code,
    backtrace,
    executionTool,
  }),
);

export const compileRequestPayloadSelector = createSelector(
  codeSelector,
  channelSelector,
  (state: State) => state.configuration,
  getCrateType,
  runAsTest,
  getBacktraceSet,
  (_state: State, args: { target: string }) => args,
  (code, channel, configuration, crateType, tests, backtrace, { target }) => ({
    channel,
    mode: configuration.mode,
    edition: configuration.edition,
    crateType,
    tests,
    code,
    target,
    assemblyFlavor: configuration.assemblyFlavor,
    demangleAssembly: configuration.demangleAssembly,
    processAssembly: configuration.processAssembly,
    backtrace,
  }),
);

export const isAssemblyInProgressSelector = createSelector(
  (state: State) => state.output.assembly,
  asm => asm.requestsInProgress > 0,
);

const ASSEMBLY_SYMBOLS_RE = /^[_a-zA-Z0-9<>, ]+:/m;

export const hasAssemblySymbolsSelector = createSelector(
  (state: State) => state.output.assembly,
  asm => !!asm.code?.match(ASSEMBLY_SYMBOLS_RE),
);

export const isLlvmIrInProgressSelector = createSelector(
  (state: State) => state.output.llvmIr,
  llvmIr => llvmIr.requestsInProgress > 0,
);

const LLVMIR_SYMBOLS_RE = /^define.*@.*{/m;

export const hasLlvmIrSymbolsSelector = createSelector(
  (state: State) => state.output.llvmIr,
  llvmIr => !!llvmIr.code?.match(LLVMIR_SYMBOLS_RE),
);

export const themeSelector = createSelector(
  (state: State) => state,
  (state) => state.configuration.theme,
);
