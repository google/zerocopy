import React, { useEffect, useRef } from 'react';

import RealPrism from './prism-shim';

interface PrismProps {
  children?: string;
  language: 'rust' | 'rust_mir' | 'rust_errors';
  className?: string;
}

const Prism: React.FC<PrismProps> = ({ children, language, className = '' }) => {
  const element = useRef(null);

  useEffect(() => {
    if (!element.current) {
      return;
    }

    RealPrism.highlightElement(element.current);
  }, [element, children, language]);

  return (
    <pre>
      <code ref={element} className={`${className} language-${language}`}>
        {children}
      </code>
    </pre>
  );
};

export default Prism;
