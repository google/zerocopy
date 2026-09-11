import React, { type JSX } from 'react';

import Link, { LinkProps } from './uss-router/Link';

import * as styles from './ButtonSet.module.css';

interface ButtonSetProps {
  className?: string;
  children: React.ReactNode;
}

export const ButtonSet: React.FC<ButtonSetProps> = ({ className = '', children }) => (
  <div className={`${styles.set} ${className}`}>{children}</div>
);

type HTMLButton = JSX.IntrinsicElements['button'];

interface ButtonProps extends HTMLButton {
  isPrimary?: boolean;
  isSmall?: boolean;
  iconLeft?: React.FC;
  iconRight?: React.FC;
}

export const Button: React.FC<ButtonProps> = ({
  isPrimary = false,
  isSmall = false,
  iconLeft: IconLeft,
  iconRight: IconRight,
  children,
  ref,
  ...props
}) => {
  const iconLeft = IconLeft && (
    <span className={styles.iconLeft}>
      <IconLeft />
    </span>
  );
  const iconRight = IconRight && (
    <span className={styles.iconRight}>
      <IconRight />
    </span>
  );
  const ordinalStyle = isPrimary ? styles.primary : styles.secondary;
  const smallStyle = isSmall ? styles.small : '';

  return (
    <button ref={ref} className={`${ordinalStyle} ${smallStyle}`} {...props}>
      {iconLeft}
      {children}
      {iconRight}
    </button>
  );
};

export const Rule: React.FC = () => <span className={styles.rule} />;

interface IconButtonProps extends HTMLButton {
  isSmall?: boolean;
}

export const IconButton: React.FC<IconButtonProps> = ({
  ref,
  isSmall = false,
  children,
  ...props
}) => {
  const smallStyle = isSmall ? styles.small : '';

  return (
    <button ref={ref} className={`${styles.icon} ${smallStyle}`} {...props}>
      {children}
    </button>
  );
};

export const IconLink: React.FC<LinkProps> = ({ children, ref, ...props }) => (
  <Link ref={ref} className={styles.icon} {...props}>
    {children}
  </Link>
);
