import React from 'react';

import Section from './Section';
import SimplePane, { SimplePaneProps } from './SimplePane';

export interface PaneWithCodeProps extends SimplePaneProps {
  code?: string;
}

const PaneWithCode: React.FC<PaneWithCodeProps> = ({ children, code, ...rest }) => (
  <SimplePane {...rest}>
    <Section kind="code" label="Result">
      {code}
    </Section>
    {children}
  </SimplePane>
);

export default PaneWithCode;
