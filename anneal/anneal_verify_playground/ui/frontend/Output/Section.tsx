import React from 'react';

import Header from './Header';

import * as styles from './Section.module.css';

interface SectionProps {
  children: React.ReactNode;
  kind: string;
  label: string;
}

const Section: React.FC<SectionProps> = ({ kind, label, children }) => (
  React.Children.count(children) === 0 ? null : (
    <div data-test-id={`output-${kind}`}>
      <Header label={label} />
      <pre><code className={styles.code}>{children}</code></pre>
    </div>
  )
);

export default Section;
