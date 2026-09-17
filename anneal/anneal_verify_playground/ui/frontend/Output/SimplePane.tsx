import React from 'react';

import Header from './Header';
import Loader from './Loader';
import OutputPrism from './OutputPrism';
import Section from './Section';

interface HighlightErrorsProps {
  children?: string;
  label: string;
}

const onOutputPrismCopy: React.ClipboardEventHandler = (event) => {
  // Blank out HTML copy data.
  // Though linkified output is handy in the Playground, it does more harm
  // than good when copied elsewhere, and terminal output is usable on its own.
  const selection = document.getSelection();
  if (selection) {
    event.clipboardData.setData('text/plain', selection.toString());
    event.preventDefault();
  }
};

const HighlightErrors: React.FC<HighlightErrorsProps> = ({ label, children }) => (
  <div data-test-id="output-stderr" onCopy={onOutputPrismCopy}>
    <Header label={label} />
    <OutputPrism language="rust_errors">{children}</OutputPrism>
  </div>
);

export interface SimplePaneProps extends ReallySimplePaneProps {
  children?: React.ReactNode;
  kind: string;
}

export interface ReallySimplePaneProps {
  requestsInProgress: number;
  stdout?: string;
  stderr?: string;
  error?: string;
}

const SimplePane: React.FC<SimplePaneProps> = (props) => (
  <div data-test-id={`output-${props.kind}`}>
    {props.requestsInProgress > 0 && <Loader />}
    <Section kind="error" label="Errors">
      {props.error}
    </Section>
    <HighlightErrors label="Standard Error">{props.stderr}</HighlightErrors>
    <Section kind="stdout" label="Standard Output">
      {props.stdout}
    </Section>
    {props.children}
  </div>
);

export default SimplePane;
