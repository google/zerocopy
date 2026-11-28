import React, { Activity, useRef, useState } from 'react';

import Header from './Header';
import Notifications from './Notifications';
import Output from './Output';
import Editor from './editor/Editor';
import { useAppSelector } from './hooks';
import * as selectors from './selectors';
import { Orientation } from './types';

import * as styles from './Playground.module.css';

interface Distances {
  toTop: number;
  toRight: number;
  toBottom: number;
  toLeft: number;
}

const clamp = (val: number, min: number, max: number) => Math.min(Math.max(val, min), max);
const clampPositive = (v: number): number => (v > 0 ? v : 0);

const distances = (bounds: DOMRectReadOnly, evt: React.MouseEvent): Distances => {
  const { top, right, bottom, left } = bounds;

  const pageX = clamp(evt.pageX, left, right);
  const pageY = clamp(evt.pageY, top, bottom);

  return {
    toTop: pageY - top,
    toLeft: pageX - left,
    toRight: right - pageX,
    toBottom: bottom - pageY,
  };
};

const subtractDistances = (a: Distances, b: Distances): Distances => ({
  toTop: clampPositive(a.toTop - b.toTop),
  toRight: clampPositive(a.toRight - b.toRight),
  toBottom: clampPositive(a.toBottom - b.toBottom),
  toLeft: clampPositive(a.toLeft - b.toLeft),
});

interface GutterProps {
  container: React.RefObject<HTMLDivElement | null>;
  className: string;
  orientation: Orientation;
  hidden?: boolean;
  onMove: (distances: Distances) => void;
  onReset: () => void;
}

const Gutter: React.FC<GutterProps> = ({ container, className, orientation, onMove, onReset }) => {
  'use memo';

  // Values assumed to stay stable during a drag
  interface Cache {
    // The container's position and size. The container can not move
    // or resize while we are dragging.
    containerBounds: DOMRectReadOnly;

    // The pointer's offset within the gutter. We take the offsets
    // into account while dragging to avoid an initial jump.
    initialPointerOffsets: Distances;
  }
  const cache = useRef<Cache | null>(null);
  const pendingCallback = useRef<number | null>(null);

  const onClick = (evt: React.MouseEvent) => {
    if (evt.detail === 2) {
      onReset();
    }
  };

  const onPointerDown = (evt: React.PointerEvent<HTMLDivElement>) => {
    if (!container.current || evt.button !== 0) {
      return;
    }

    evt.currentTarget.setPointerCapture(evt.pointerId);

    cache.current = {
      containerBounds: container.current.getBoundingClientRect(),
      initialPointerOffsets: distances(evt.currentTarget.getBoundingClientRect(), evt),
    };
  };

  const onPointerMove = (evt: React.PointerEvent<HTMLDivElement>) => {
    if (!cache.current) {
      return;
    }
    const { containerBounds, initialPointerOffsets } = cache.current;

    const rawDistances = distances(containerBounds, evt);

    // Keep the offset of the cursor within the gutter to avoid a
    // small jump when first dragging.
    const offsetDistances = subtractDistances(rawDistances, initialPointerOffsets);

    // Coalescing the callback because it only matters when we render.
    if (pendingCallback.current) {
      window.cancelAnimationFrame(pendingCallback.current);
    }
    pendingCallback.current = window.requestAnimationFrame(() => {
      onMove(offsetDistances);
      pendingCallback.current = null;
    });
  };

  const onPointerUp = () => {
    cache.current = null;
  };

  return (
    <div
      className={`${className} ${styles.gutter}`}
      data-orientation={orientation}
      onClick={onClick}
      onPointerDown={onPointerDown}
      onPointerMove={onPointerMove}
      onPointerUp={onPointerUp}
      onPointerCancel={onPointerUp}
    >
      <span className={styles.gutterHandle}>⣿</span>
    </div>
  );
};

const makeStyleFromPixels = (cssProps: [string, number | undefined][]): React.CSSProperties => {
  const massagedProps = cssProps
    .filter(([_k, v]) => v !== undefined)
    .map(([k, v]) => [k, `${v}px`]);
  return Object.fromEntries(massagedProps) as React.CSSProperties;
};

const ResizableArea: React.FC = () => {
  'use memo';

  const somethingToShow = useAppSelector(selectors.getSomethingToShow);
  const isFocused = useAppSelector(selectors.isOutputFocused);
  const orientation = useAppSelector(selectors.orientation);

  const container = useRef<HTMLDivElement>(null);

  const [outputWidth, setOutputWidth] = useState<number | undefined>(undefined);
  const [outputHeight, setOutputHeight] = useState<number | undefined>(undefined);

  const editorOutputGutterMove = (distances: Distances) => {
    if (orientation === Orientation.Horizontal) {
      setOutputHeight(distances.toBottom);
    } else {
      setOutputWidth(distances.toRight);
    }
  };

  const editorOutputGutterReset = () => {
    if (orientation === Orientation.Horizontal) {
      setOutputHeight(undefined);
    } else {
      setOutputWidth(undefined);
    }
  };

  const outputMode = (() => {
    if (!somethingToShow) {
      return 'none';
    }
    if (!isFocused) {
      return 'slim';
    }
    return 'full';
  })();

  const hideEditorOutputGutter = outputMode !== 'full';

  const style = makeStyleFromPixels([
    ['--output-height', outputHeight],
    ['--output-width', outputWidth],
  ]);

  return (
    <div
      className={styles.playground}
      data-orientation={orientation}
      data-output-mode={outputMode}
      ref={container}
      style={style}
    >
      <div className={styles.editor}>
        <Editor />
      </div>

      <Activity mode={hideEditorOutputGutter ? 'hidden' : 'visible'}>
        <Gutter
          className={styles.editorOutputGutter}
          orientation={orientation}
          container={container}
          onMove={editorOutputGutterMove}
          onReset={editorOutputGutterReset}
        />
      </Activity>

      <Activity mode={somethingToShow ? 'visible' : 'hidden'}>
        <div className={styles.output}>
          <Output />
        </div>
      </Activity>
    </div>
  );
};

const WebSocketStatus: React.FC = () => {
  const enabled = useAppSelector(selectors.showGemSelector);
  const status = useAppSelector(selectors.websocketStatusSelector);

  if (!enabled) {
    return null;
  }

  const style: React.CSSProperties = {
    position: 'absolute',
    left: '1em',
    bottom: '1em',
    zIndex: '1',
  };

  switch (status.state) {
    case 'connected':
      style.color = 'green';
      return <div style={style}>⬤</div>;
    case 'disconnected':
      style.color = 'grey';
      return <div style={style}>⬤</div>;
    case 'error':
      style.color = 'red';
      return (
        <div style={style} title={status.error}>
          ⬤
        </div>
      );
  }
};

const Playground: React.FC = () => {
  const showNotifications = useAppSelector(selectors.anyNotificationsToShowSelector);

  return (
    <>
      <div className={styles.container}>
        <WebSocketStatus />
        <Header />
        <ResizableArea />
      </div>
      {showNotifications && <Notifications />}
    </>
  );
};

export default Playground;
