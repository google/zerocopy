import React, { Fragment, useCallback, useState } from 'react';

import { ClipboardIcon } from '../Icon';
import * as selectors from '../selectors';
import { useAppSelector } from '../hooks';

import Loader from './Loader';
import Section from './Section';

import * as styles from './Gist.module.css';

const Gist: React.FC = () => {
  const showLoader = useAppSelector(selectors.showGistLoaderSelector);
  const error = useAppSelector((state) => state.output.gist.error);

  if (showLoader) {
    return <Loader />;
  }

  if (error) {
    return <Error error={error} />;
  }

  return <Links />;
};

const Error: React.FC<{error: string}> = ({ error }) => (
  <Section kind="error" label="Errors">{error}</Section>
);

interface CopiedProps {
  children: React.ReactNode;
  href: string;
}

const Copied: React.FC<CopiedProps> = ({ children, href }) => {
  const [copied, setCopied] = useState(false);

  const startCopy = useCallback(() => {
    setCopied(true);
    window.navigator.clipboard.writeText(href);

    setTimeout(() => {
      setCopied(false);
    }, 1000);
  }, [href]);

  return (
    <p className={copied ? styles.active : styles.container}>
      <a href={href}>{children}</a>
      <button className={styles.button} onClick={startCopy}>
        <ClipboardIcon />
      </button>
      <span className={styles.text}>Copied!</span>
    </p>
  );
};

const Links: React.FC = () => {
  const codeUrl = useAppSelector(selectors.codeUrlSelector);
  const gistUrl = useAppSelector((state) => state.output.gist.url);
  const permalink = useAppSelector(selectors.permalinkSelector);
  const urloUrl = useAppSelector(selectors.urloUrlSelector);
  const textChanged = useAppSelector(selectors.textChangedSinceShareSelector);

  return (
    <Fragment>
      <Copied href={permalink}>Permalink to the playground</Copied>
      { gistUrl ? <Copied href={gistUrl}>Direct link to the gist</Copied> : null }
      <Copied href={codeUrl}>Embedded code in link</Copied>
      <NewWindow href={urloUrl}>Open a new thread in the Rust user forum</NewWindow>
      {textChanged ? <Section kind="warning" label="Code changed">
        Source code has been changed since gist was saved
      </Section>: null }
    </Fragment>
  );
};

interface NewWindowProps {
  children: React.ReactNode;
  href: string;
}

const NewWindow: React.FC<NewWindowProps> = props => (
  <p>
    <a href={props.href} target="_blank" rel="noopener noreferrer">{props.children}</a>
  </p>
);

export default Gist;
