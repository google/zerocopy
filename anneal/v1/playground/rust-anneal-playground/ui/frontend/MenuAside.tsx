import React from 'react';

import * as styles from './MenuAside.module.css';

const MenuAside: React.FC<React.PropsWithChildren<unknown>> = ({ children }) => (
  <p className={styles.aside}>
    {children}
  </p>
);

export default MenuAside;
