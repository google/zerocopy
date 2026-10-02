import React from 'react';

import { useAppSelector } from '../hooks';
import * as selectors from '../selectors';
import PaneWithCode from './PaneWithCode';
import WarnAboutNoSymbols from './WarnAboutNoSymbols';

const Assembly: React.FC = () => {
  const assembly = useAppSelector((state) => state.output.assembly);
  const isAssemblyInProgress = useAppSelector(selectors.isAssemblyInProgressSelector);
  const hasAssemblySymbols = useAppSelector(selectors.hasAssemblySymbolsSelector);

  return (
    <PaneWithCode {...assembly} kind="asm">
      <WarnAboutNoSymbols
        isInProgress={isAssemblyInProgress}
        hasSymbols={hasAssemblySymbols}
        name="assembly"
      />
    </PaneWithCode>
  );
};

export default Assembly;
