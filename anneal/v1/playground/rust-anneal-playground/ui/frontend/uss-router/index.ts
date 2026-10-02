import { isEqual } from 'lodash-es';
import { configureStore, ThunkAction, Reducer, Store, UnknownAction } from '@reduxjs/toolkit';
import { BrowserHistory, Location, Path } from 'history';

export type PlainOrThunk<St, A extends UnknownAction> = A | ThunkAction<void, St, unknown, A>;

export type StoreArg<St, A extends UnknownAction> = Store<St, A> & {
  dispatch: (a: PlainOrThunk<St, A>) => void;
};

// This is a... dense... attempt at saying "we accept any store with
// any dispatch so long as it can handle the actions you create". It's
// probably overly complicated, restrictive, and broad all at the same
// time.
interface CreateRouterArg<St, SubSt, A extends UnknownAction> {
  store: StoreArg<St, A>;
  reducer: Reducer<St>;
  history: BrowserHistory;
  stateSelector: (state: St) => SubSt;
  stateToLocation: (substate: St) => Partial<Path>;
  locationToAction: (location: Location) => PlainOrThunk<St, A> | null;
}

export interface RouterObject<A extends UnknownAction> {
  provisionalLocation: (makeAction: () => A) => Partial<Path>;
}

export function createRouter<St, SubSt, A extends UnknownAction>({
  store,
  reducer,
  history,
  stateSelector,
  stateToLocation,
  locationToAction,
}: CreateRouterArg<St, SubSt, A>): RouterObject<A> {
  let interestingPrevState: SubSt;

  // Watch changes to the Redux state
  store.subscribe(() => {
    const nextState = store.getState();

    // It's only worth checking if our state subset has changed.
    const interestingNextState = stateSelector(nextState);
    if (isEqual(interestingNextState, interestingPrevState)) { return; }
    interestingPrevState = interestingNextState;

    // If our next location matches where we already are, leave the
    // history stack as-is.
    const nextLocation = stateToLocation(nextState);
    if (pathsEqualEnough(history, history.location, nextLocation)) { return; }
    history.push(nextLocation);
  });

  const dispatchBrowserLocationChange = (nextLocation: Location) => {
    const action = locationToAction(nextLocation);
    if (action) {
      store.dispatch(action);
    }
  };

  // Watch changes to the browser state
  history.listen(({ action, location }) => {
    if (action === 'POP') {
      dispatchBrowserLocationChange(location);
    }
  });

  // Load initial browser state
  dispatchBrowserLocationChange(history.location);

  return {
    provisionalLocation: (makeAction: () => A) => {
      const preloadedState = store.getState();

      const tempStore = configureStore({
        reducer,
        preloadedState,
        devTools: false,
      });

      const action = makeAction();
      tempStore.dispatch(action);
      const maybeState = tempStore.getState();
      return stateToLocation(maybeState);
    },
  };
}

function pathsEqualEnough(history: BrowserHistory, a: Partial<Path>, b: Partial<Path>): boolean {
  const aHref = history.createHref(a);
  const bHref = history.createHref(b);

  return aHref === bHref;
}
