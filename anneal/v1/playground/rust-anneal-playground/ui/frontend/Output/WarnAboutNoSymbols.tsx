import React from 'react';

import Section from './Section';

export interface WarnAboutNoSymbolsProps {
  isInProgress: boolean;
  hasSymbols: boolean;
  name: string;
}

const WarnAboutNoSymbols: React.FC<WarnAboutNoSymbolsProps> = ({
  isInProgress,
  hasSymbols,
  name,
}) => {
  const warnAboutNoSymbols = !isInProgress && !hasSymbols;

  if (!warnAboutNoSymbols) {
    return null;
  }

  return (
    <Section kind="warning" label="Warnings">
      No symbols detected — they may have been optimized away.
      {'\n'}
      Add the <code>#[unsafe(no_mangle)]</code> attribute to
      {'\n'}
      functions you want to see {name} for. Generic functions
      {'\n'}
      only generate {name} when concrete types are provided.
    </Section>
  );
};

export default WarnAboutNoSymbols;
