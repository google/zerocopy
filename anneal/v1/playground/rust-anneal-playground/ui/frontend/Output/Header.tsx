import React from 'react';

import * as styles from './Header.module.css';

interface HeaderProps {
  label: string;
}

const Header: React.FC<HeaderProps> = ({ label }) => (
  <span className={styles.container}>{label}</span>
);

export default Header;
