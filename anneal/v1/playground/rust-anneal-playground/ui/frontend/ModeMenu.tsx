import React, { Fragment, useCallback } from 'react';

import MenuGroup from './MenuGroup';
import SelectOne from './SelectOne';

import * as config from './reducers/configuration';
import { Mode } from './types';
import { useAppDispatch, useAppSelector } from './hooks';

interface ModeMenuProps {
  close: () => void;
}

const ModeMenu: React.FC<ModeMenuProps> = props => {
  const mode = useAppSelector((state) => state.configuration.mode);
  const dispatch = useAppDispatch();
  const changeMode = useCallback((mode: Mode) => {
    dispatch(config.changeMode(mode));
    props.close();
  }, [dispatch, props]
  );

  return (
    <Fragment>
      <MenuGroup title="Mode &mdash; Choose optimization level">
        <SelectOne
          name="Debug"
          currentValue={mode}
          thisValue={Mode.Debug}
          changeValue={changeMode}
        >
          Build with debug information, without optimizations.
        </SelectOne>
        <SelectOne
          name="Release"
          currentValue={mode}
          thisValue={Mode.Release}
          changeValue={changeMode}
        >
          Build with optimizations turned on.
        </SelectOne>
      </MenuGroup>
    </Fragment>
  );
};

export default ModeMenu;
