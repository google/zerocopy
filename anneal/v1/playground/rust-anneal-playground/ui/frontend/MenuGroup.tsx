import React from 'react';

import * as styles from './MenuGroup.module.css';

interface MenuGroupProps {
  children: React.ReactNode;
  title: string;
}

const MenuGroup: React.FC<MenuGroupProps> = ({ title, children }) => (
  <div className={styles.container}>
    <h1 className={styles.title}>{title}</h1>
    <div className={styles.content}>
      {children}
    </div>
  </div>
);

export default MenuGroup;
