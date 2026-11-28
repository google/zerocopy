import React from 'react';

import Prism from '../Prism';

import * as styles from './OutputPrism.module.css';

interface OutputPrismProps {
  children?: string;
  language: 'rust_mir' | 'rust_errors';
}

const OutputPrism: React.FC<OutputPrismProps> = ({ language, children }) => (
  <Prism className={styles.container} language={language}>
    {children}
  </Prism>
);

export default OutputPrism;
