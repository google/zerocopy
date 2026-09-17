import React, { type JSX } from 'react';

import MenuItem from './MenuItem';

import * as styles from './SimpleButtonMenuItem.module.css';

type Button = JSX.IntrinsicElements['button'];

interface SimpleButtonMenuItemProps extends Button {
  children: React.ReactNode;
}

const SimpleButtonMenuItem: React.FC<SimpleButtonMenuItemProps> = ({
  name,
  children,
  ...props
}) => (
  <MenuItem>
    <button className={styles.container} {...props}>
      {children}
    </button>
  </MenuItem>
);

export default SimpleButtonMenuItem;
