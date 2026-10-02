import React, { type JSX } from 'react';

import { CheckmarkIcon } from './Icon';
import MenuItem from './MenuItem';

import * as styles from './SelectableMenuItem.module.css';

type Button = JSX.IntrinsicElements['button'];

interface SelectableMenuItemProps extends Button {
  name: string;
  selected: boolean;
}

const SelectableMenuItem: React.FC<SelectableMenuItemProps> = ({ name, selected, children, ...props }) => (
  <MenuItem>
    <button className={selected ? styles.selected : styles.container} {...props}>
      <div className={styles.header}>
        <span className={styles.checkmark}>
          <CheckmarkIcon />
        </span>
        <span className={styles.name}>{name}</span>
      </div>
      <div className={styles.description}>{children}</div>
    </button>
  </MenuItem>
);

export default SelectableMenuItem;
