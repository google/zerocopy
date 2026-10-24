import React, { type JSX } from 'react';

import MenuItem from './MenuItem';

import * as styles from './ConfigElement.module.css';

interface EitherProps<T extends string> extends ConfigElementProps {
  id: string;
  a: string;
  b: string;
  aLabel?: string;
  bLabel?: string;
  value: T;
  onChange: (_: T) => void;
}

export const Either = <T extends string>({
  id,
  a,
  b,
  aLabel = a,
  bLabel = b,
  value,
  onChange,
  ...rest
}: EitherProps<T>) => (
  <ConfigElement {...rest}>
    <div className={styles.toggle}>
      <input
        id={`${id}-a`}
        name={id}
        value={a}
        type="radio"
        checked={value === a}
        onChange={() => onChange(a as T)}
      />
      <label htmlFor={`${id}-a`}>{aLabel}</label>
      <input
        id={`${id}-b`}
        name={id}
        value={b}
        type="radio"
        checked={value === b}
        onChange={() => onChange(b as T)}
      />
      <label htmlFor={`${id}-b`}>{bLabel}</label>
    </div>
  </ConfigElement>
);

interface SelectProps<T extends string> extends ConfigElementProps {
  children: React.ReactNode;
  value: T;
  onChange: (_: T) => void;
}

export const Select = <T extends string>({
  value,
  onChange,
  children,
  ...rest
}: SelectProps<T>) => (
  <ConfigElement {...rest}>
    <select className={styles.select} value={value} onChange={(e) => onChange(e.target.value as T)}>
      {children}
    </select>
  </ConfigElement>
);

interface ConfigElementProps {
  children?: React.ReactNode;
  name: string;
  isDefault?: boolean;
  aside?: JSX.Element;
}

const ConfigElement: React.FC<ConfigElementProps> = ({ name, isDefault, aside, children }) => {
  const actuallyDefault = isDefault ?? true;
  const defaultStyle = actuallyDefault ? styles.name : styles.notDefault;

  return (
    <MenuItem>
      <div className={styles.container}>
        <span className={defaultStyle}>{name}</span>
        <div className={styles.value}>{children}</div>
      </div>
      {aside}
    </MenuItem>
  );
};
