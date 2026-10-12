import React from 'react';

import { useAppSelector } from '../hooks';
import * as selectors from '../selectors';
import PaneWithCode from './PaneWithCode';
import WarnAboutNoSymbols from './WarnAboutNoSymbols';

const LlvmIr: React.FC = () => {
  const llvmIr = useAppSelector((state) => state.output.llvmIr);
  const isLlvmIrInProgress = useAppSelector(selectors.isLlvmIrInProgressSelector);
  const hasLlvmIrSymbols = useAppSelector(selectors.hasLlvmIrSymbolsSelector);

  return (
    <PaneWithCode {...llvmIr} kind="llvm-ir">
      <WarnAboutNoSymbols
        isInProgress={isLlvmIrInProgress}
        hasSymbols={hasLlvmIrSymbols}
        name="LLVM IR"
      />
    </PaneWithCode>
  );
};

export default LlvmIr;
