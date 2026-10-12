import {
  FloatingArrow,
  FloatingFocusManager,
  Placement,
  arrow,
  autoUpdate,
  flip,
  offset,
  shift,
  useClick,
  useDismiss,
  useFloating,
  useInteractions,
  useRole,
} from '@floating-ui/react';
import React, { useCallback, useRef, useState } from 'react';
import { createPortal } from 'react-dom';

import * as styles from './PopButton.module.css';

export interface ButtonProps {
  toggle: () => void;
  ref: React.Ref<HTMLButtonElement>;
}

export interface MenuProps {
  close: () => void;
}

interface NewPopProps {
  Button: React.ComponentType<ButtonProps>;
  Menu: React.ComponentType<MenuProps>;
  menuContainer?: React.RefObject<HTMLDivElement | null>;
}

const CONTAINER_STYLE: { [key in Placement]?: string } = {
  top: styles.contentTop,
  bottom: styles.contentBottom,
};

const PopButton: React.FC<NewPopProps> = ({ Button, Menu, menuContainer }) => {
  const [isOpen, setIsOpen] = useState(false);
  const toggle = useCallback(() => setIsOpen((v) => !v), []);
  const close = useCallback(() => setIsOpen(false), []);

  const arrowRef = useRef(null);

  const { x, y, refs, strategy, context, placement } = useFloating({
    open: isOpen,
    onOpenChange: setIsOpen,
    // eslint-disable-next-line react-hooks/refs
    middleware: [offset(10), flip(), shift(), arrow({ element: arrowRef })],
    whileElementsMounted: autoUpdate,
  });

  const containerClass = CONTAINER_STYLE[placement] ?? '';

  const click = useClick(context);
  const dismiss = useDismiss(context);
  const role = useRole(context);

  const { getReferenceProps, getFloatingProps } = useInteractions([click, dismiss, role]);

  const FloatingMenu = isOpen && (
    <FloatingFocusManager context={context}>
      <div
        ref={refs.setFloating}
        className={styles.container}
        style={{
          position: strategy,
          top: y ?? 0,
          left: x ?? 0,
          width: 'max-content',
        }}
        {...getFloatingProps()}
      >
        <FloatingArrow
          ref={arrowRef}
          context={context}
          height={10}
          width={20}
          className={styles.arrow}
        />
        <div className={containerClass}>
          <Menu close={close} />
        </div>
      </div>
    </FloatingFocusManager>
  );

  const Portal = menuContainer?.current && createPortal(FloatingMenu, menuContainer.current);

  return (
    <>
      {/* eslint-disable-next-line react-hooks/refs */}
      <Button toggle={toggle} ref={refs.setReference} {...getReferenceProps()} />

      {Portal || FloatingMenu}
    </>
  );
};

export default PopButton;
