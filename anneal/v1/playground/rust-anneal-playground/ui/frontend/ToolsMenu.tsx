import React, { useCallback } from 'react';

import ButtonMenuItem from './ButtonMenuItem';
import MenuGroup from './MenuGroup';
import MenuAside from './MenuAside';

import * as selectors from './selectors';
import { useAppDispatch } from './hooks';
import { performFormat } from './reducers/output/format';
import { performClippy } from './reducers/output/clippy';
import { performMiri } from './reducers/output/miri';
import { performMacroExpansion } from './reducers/output/macroExpansion';
import { useAppSelector } from './hooks';

interface ToolsMenuProps {
  close: () => void;
}

const ToolsMenu: React.FC<ToolsMenuProps> = props => {
  const rustfmtVersion = useAppSelector(selectors.rustfmtVersionText);
  const rustfmtVersionDetails = useAppSelector(selectors.rustfmtVersionDetailsText);
  const clippyVersionDetails = useAppSelector(selectors.clippyVersionDetailsText);
  const clippyVersion = useAppSelector(selectors.clippyVersionText);
  const miriVersionDetails = useAppSelector(selectors.miriVersionDetailsText);
  const miriVersion = useAppSelector(selectors.miriVersionText);
  const nightlyVersion = useAppSelector(selectors.nightlyVersionText);
  const nightlyVersionDetails = useAppSelector(selectors.nightlyVersionDetailsText);

  const miriRunningTests = useAppSelector(selectors.runAsTest);
  const miriText = miriRunningTests ? "these tests" : "this program";

  const dispatch = useAppDispatch();
  const clippy = useCallback(() => {
    dispatch(performClippy());
    props.close();
  }, [dispatch, props]);
  const miri = useCallback(() => {
    dispatch(performMiri());
    props.close();
  }, [dispatch, props]);
  const format = useCallback(() => {
    dispatch(performFormat());
    props.close();
  }, [dispatch, props]);
  const expandMacros = useCallback(() => {
    dispatch(performMacroExpansion());
    props.close();
  }, [dispatch, props]);

  return (
    <MenuGroup title="Tools">
      <ButtonMenuItem
        name="Rustfmt"
        onClick={format}>
        <div>Format this code with Rustfmt.</div>
        <MenuAside>{rustfmtVersion} ({rustfmtVersionDetails})</MenuAside>
      </ButtonMenuItem>
      <ButtonMenuItem
        name="Clippy"
        onClick={clippy}>
        <div>Catch common mistakes and improve the code using the Clippy linter.</div>
        <MenuAside>{clippyVersion} ({clippyVersionDetails})</MenuAside>
      </ButtonMenuItem>
      <ButtonMenuItem
        name="Miri"
        onClick={miri}>
        <div>
          Execute {miriText} in the Miri interpreter to detect certain
          cases of undefined behavior (like out-of-bounds memory access).
        </div>
        <MenuAside>{miriVersion} ({miriVersionDetails})</MenuAside>
      </ButtonMenuItem>
      <ButtonMenuItem
        name="Expand macros"
        onClick={expandMacros}>
        <div>
          Expand macros in code using the nightly compiler.
        </div>
        <MenuAside>{nightlyVersion} ({nightlyVersionDetails})</MenuAside>
      </ButtonMenuItem>
    </MenuGroup>
  );
};

export default ToolsMenu;
