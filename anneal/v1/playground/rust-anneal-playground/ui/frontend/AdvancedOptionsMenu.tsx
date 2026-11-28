import React, { useCallback } from 'react';

import { Either as EitherConfig, Select as SelectConfig } from './ConfigElement';
import MenuAside from './MenuAside';
import MenuGroup from './MenuGroup';
import { useAppDispatch, useAppSelector } from './hooks';
import * as config from './reducers/configuration';
import * as selectors from './selectors';
import { AliasingModel, Backtrace, Edition } from './types';

const MIRI_TREE_BORROWS_URL = 'https://github.com/rust-lang/miri#user-content--zmiri-tree-borrows';

const TreeBorrowAside: React.FC = () => (
  <MenuAside>
    Code that is accepted by <a href={MIRI_TREE_BORROWS_URL}>Tree Borrows</a> may be declared
    undefined behavior in the future.
  </MenuAside>
);

const AdvancedOptionsMenu: React.FC = () => {
  const isEditionDefault = useAppSelector(selectors.isEditionDefault);
  const edition = useAppSelector((state) => state.configuration.edition);
  const isBacktraceDefault = useAppSelector(selectors.isBacktraceDefault);
  const backtrace = useAppSelector((state) => state.configuration.backtrace);
  const isAliasingModelDefault = useAppSelector(selectors.isAliasingModelDefault);
  const aliasingModel = useAppSelector((state) => state.configuration.aliasingModel);

  const dispatch = useAppDispatch();

  const changeEdition = useCallback((e: Edition) => dispatch(config.changeEdition(e)), [dispatch]);
  const changeBacktrace = useCallback(
    (b: Backtrace) => dispatch(config.changeBacktrace(b)),
    [dispatch],
  );
  const changeAliasingModel = useCallback(
    (b: AliasingModel) => dispatch(config.changeAliasingModel(b)),
    [dispatch],
  );

  return (
    <>
      <MenuGroup title="Advanced options">
        <SelectConfig
          name="Edition"
          value={edition}
          isDefault={isEditionDefault}
          onChange={changeEdition}
        >
          <option value={Edition.Rust2015}>2015</option>
          <option value={Edition.Rust2018}>2018</option>
          <option value={Edition.Rust2021}>2021</option>
          <option value={Edition.Rust2024}>2024</option>
        </SelectConfig>

        <EitherConfig
          id="backtrace"
          name="Backtrace"
          a={Backtrace.Enabled}
          b={Backtrace.Disabled}
          aLabel="On"
          bLabel="Off"
          value={backtrace}
          isDefault={isBacktraceDefault}
          onChange={changeBacktrace}
        />
      </MenuGroup>

      <MenuGroup title="Miri">
        <EitherConfig
          id="aliasingModel"
          name="Aliasing model"
          a={AliasingModel.Stacked}
          b={AliasingModel.Tree}
          value={aliasingModel}
          isDefault={isAliasingModelDefault}
          onChange={changeAliasingModel}
          aside={<TreeBorrowAside />}
        />
      </MenuGroup>
    </>
  );
};

export default AdvancedOptionsMenu;
