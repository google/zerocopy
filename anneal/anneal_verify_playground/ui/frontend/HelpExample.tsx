import React, { useCallback } from 'react';
import root from 'react-shadow';

import Prism from './Prism';
import * as actions from './actions';
import { useAppDispatch } from './hooks';

import * as styles from './HelpExample.module.css';
import prismOverrides from './prismjs-overrides.css';
import prismTheme from 'prismjs/themes/prism-okaidia.css';

export interface HelpExampleProps {
  code: string;
}

const HelpExample: React.FC<HelpExampleProps> = ({ code }) => {
  const dispatch = useAppDispatch();
  const showExample = useCallback(() => dispatch(actions.showExample(code)), [dispatch, code]);

  return (
    <div className={styles.container}>
      <button className={styles.loadExample} onClick={showExample}>
        Load in playground
      </button>
      <root.div>
        <link href={prismTheme} rel="stylesheet" />
        <link href={prismOverrides} rel="stylesheet" />

        <Prism language="rust">{code}</Prism>
      </root.div>
    </div>
  );
};

export default HelpExample;
