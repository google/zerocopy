import React, { useCallback } from 'react';

import * as selectors from '../selectors';
import * as code from '../reducers/code';
import { useAppDispatch, useAppSelector } from '../hooks';

import Section from './Section';
import SimplePane from './SimplePane';

import * as styles from './Execute.module.css';

const Execute: React.FC = () => {
  const details = useAppSelector((state) => state.output.execute);
  const isAutoBuild = useAppSelector(selectors.isAutoBuildSelector);

  const dispatch = useAppDispatch();
  const addMainFunction = useCallback(() => dispatch(code.addMainFunction()), [dispatch]);

  return (
    <SimplePane {...details} kind="execute">
      {isAutoBuild && <Warning addMainFunction={addMainFunction} />}
    </SimplePane>
  );
};

interface WarningProps {
  addMainFunction: () => void;
}

const Warning: React.FC<WarningProps> = props => (
  <Section kind="warning" label="Warnings">
    No main function was detected, so your code was compiled
    {'\n'}
    but not run. If you’d like to execute your code, please
    {'\n'}
    <button className={styles.addMain} onClick={props.addMainFunction}>
      add a main function
    </button>
    .
  </Section>
);

export default Execute;
