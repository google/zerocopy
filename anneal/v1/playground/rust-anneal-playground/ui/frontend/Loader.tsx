import React from 'react';

import * as styles from './Loader.module.css';

const Loader: React.FC = () => (
  <div data-test-id="loader">
    <span className={styles.dot}>⬤</span>
    <span className={styles.dot}>⬤</span>
    <span className={styles.dot}>⬤</span>
  </div>
);

export default Loader;
