import { useEffect, useRef } from 'react';

// We use the "latest value" pattern [0] to access values from inside
// the editor / session constructors without recreating those
// callbacks when the value changes.
//
// We can almost use an "effect event" [1] except that they can only
// be used with `useEffect`, not `useCallback`; we need to use a `ref`
// callback in order to gain access to the DOM node.
//
// [0]: https://github.com/facebook/react/issues/16154#issuecomment-512966799
// [1]: https://react.dev/learn/separating-events-from-effects#declaring-an-effect-event
export function useLatest<T>(value: T) {
  const latestValue = useRef(value);
  useEffect(() => {
    latestValue.current = value;
  }, [value]);
  return latestValue;
}
