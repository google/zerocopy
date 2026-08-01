import { TypedStartListening, createListenerMiddleware, isAnyOf } from '@reduxjs/toolkit';

import { AppDispatch } from './configureStore';
import { State } from './reducers';
import {
  allowLongRun,
  wsExecuteEnd,
  wsExecuteKill,
  wsExecuteStatus,
} from './reducers/output/execute';
import {
  currentExecutionSequenceNumberSelector,
  excessiveExecutionSelector,
  killGracePeriodMsSelector,
} from './selectors';

export const observer = createListenerMiddleware();

type AppStartListening = TypedStartListening<State, AppDispatch>;
const startAppListening = observer.startListening as AppStartListening;

// Watch for requests chewing up a lot of CPU and kill them unless the
// user deliberately elects to keep them running.
startAppListening({
  matcher: isAnyOf(wsExecuteStatus, allowLongRun, wsExecuteEnd),
  effect: async (_, listenerApi) => {
    // Just one listener at a time.
    listenerApi.unsubscribe();

    await listenerApi.condition((_, state) => excessiveExecutionSelector(state));

    // Ensure that we only act on the current execution, not whatever
    // is running later on.
    const state = listenerApi.getState();
    const gracePeriod = killGracePeriodMsSelector(state);
    const sequenceNumber = currentExecutionSequenceNumberSelector(state);

    if (sequenceNumber) {
      const killed = listenerApi
        .delay(gracePeriod)
        .then(() => listenerApi.dispatch(wsExecuteKill(undefined, sequenceNumber)));

      const allowed = listenerApi.condition((action) => allowLongRun.match(action));

      const ended = listenerApi.condition(
        (action) => wsExecuteEnd.match(action) && action.meta.sequenceNumber === sequenceNumber,
      );

      await Promise.race([killed, allowed, ended]);
    }

    listenerApi.subscribe();
  },
});
