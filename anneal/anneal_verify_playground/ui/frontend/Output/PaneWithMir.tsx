import React from 'react';

import Header from './Header';
import OutputPrism from './OutputPrism';
import SimplePane, { SimplePaneProps } from './SimplePane';

interface PaneWithMirProps extends SimplePaneProps {
  code?: string;
}

const PaneWithMir: React.FC<PaneWithMirProps> = ({ code, ...rest }) => (
  <SimplePane {...rest}>
    <div data-test-id="output-result">
      <Header label="Result" />
      <OutputPrism language="rust_mir">{code}</OutputPrism>
    </div>
  </SimplePane>
);

export default PaneWithMir;
