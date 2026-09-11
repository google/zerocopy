import React, { RefObject, useCallback, useRef } from 'react';

import AdvancedOptionsMenu from './AdvancedOptionsMenu';
import BuildMenu from './BuildMenu';
import { ButtonSet, IconButton, IconLink, Button as OneButton, Rule } from './ButtonSet';
import ChannelMenu from './ChannelMenu';
import ConfigMenu from './ConfigMenu';
import {
  BuildIcon,
  ConfigIcon,
  ExpandableIcon,
  HelpIcon,
  MoreOptionsActiveIcon,
  MoreOptionsIcon,
} from './Icon';
import ModeMenu from './ModeMenu';
import PopButton, { ButtonProps } from './PopButton';
import ToolsMenu from './ToolsMenu';
import * as actions from './actions';
import { useAppDispatch, useAppSelector } from './hooks';
import { performGistSave } from './reducers/output/gist';
import { navigateToHelp } from './reducers/page';
import * as selectors from './selectors';

import * as styles from './Header.module.css';

const Header: React.FC = () => {
  const menuContainer = useRef<HTMLDivElement | null>(null);

  return (
    <>
      <div data-test-id="header" className={styles.container}>
        <div className={styles.left}>
          <ButtonSet>
            <ExecuteButton />
            <BuildMenuButton menuContainer={menuContainer} />
          </ButtonSet>

          <ButtonSet>
            <ModeMenuButton menuContainer={menuContainer} />
            <Rule />
            <ChannelMenuButton menuContainer={menuContainer} />
            <Rule />
            <AdvancedOptionsMenuButton menuContainer={menuContainer} />
          </ButtonSet>
        </div>

        <div className={styles.right}>
          <ButtonSet>
            <ShareButton />
          </ButtonSet>

          <ButtonSet>
            <ToolsMenuButton menuContainer={menuContainer} />
          </ButtonSet>

          <ButtonSet>
            <ConfigMenuButton menuContainer={menuContainer} />
          </ButtonSet>

          <ButtonSet>
            <HelpButton />
          </ButtonSet>
        </div>
      </div>

      <div ref={menuContainer} />
    </>
  );
};

interface PortalProps {
  menuContainer: RefObject<HTMLDivElement | null>;
}

const ExecuteButton: React.FC = () => {
  const executionLabel = useAppSelector(selectors.getExecutionLabel);

  const dispatch = useAppDispatch();
  const execute = useCallback(() => dispatch(actions.performPrimaryAction()), [dispatch]);

  return (
    <OneButton isPrimary type="button" onClick={execute} iconRight={BuildIcon}>
      {executionLabel}
    </OneButton>
  );
};

const BuildMenuButton: React.FC<PortalProps> = ({ menuContainer }) => {
  const Button: React.FC<ButtonProps> = ({ toggle, ref }) => (
    <IconButton type="button" title="Select what to build" ref={ref} onClick={toggle}>
      <MoreOptionsIcon />
    </IconButton>
  );

  return <PopButton Button={Button} Menu={BuildMenu} menuContainer={menuContainer} />;
};

const ModeMenuButton: React.FC<PortalProps> = ({ menuContainer }) => {
  const label = useAppSelector(selectors.getModeLabel);

  const Button: React.FC<ButtonProps> = ({ toggle, ref }) => (
    <OneButton
      type="button"
      title="Mode &mdash; Choose the optimization level"
      ref={ref}
      onClick={toggle}
      iconRight={ExpandableIcon}
    >
      {label}
    </OneButton>
  );

  return <PopButton Button={Button} Menu={ModeMenu} menuContainer={menuContainer} />;
};

const ChannelMenuButton: React.FC<PortalProps> = ({ menuContainer }) => {
  const label = useAppSelector(selectors.getChannelLabel);

  const Button: React.FC<ButtonProps> = ({ toggle, ref }) => (
    <OneButton
      type="button"
      title="Channel &mdash; Choose the Rust version"
      ref={ref}
      onClick={toggle}
      iconRight={ExpandableIcon}
    >
      {label}
    </OneButton>
  );

  return <PopButton Button={Button} Menu={ChannelMenu} menuContainer={menuContainer} />;
};

const AdvancedOptionsMenuButton: React.FC<PortalProps> = ({ menuContainer }) => {
  const advancedOptionsSet = useAppSelector(selectors.getAdvancedOptionsSet);

  const Button: React.FC<ButtonProps> = ({ toggle, ref }) => (
    <IconButton type="button" title="Advanced compilation flags" ref={ref} onClick={toggle}>
      {advancedOptionsSet ? <MoreOptionsActiveIcon /> : <MoreOptionsIcon />}
    </IconButton>
  );

  return <PopButton Button={Button} Menu={AdvancedOptionsMenu} menuContainer={menuContainer} />;
};

const ShareButton: React.FC = () => {
  const dispatch = useAppDispatch();
  const gistSave = useCallback(() => dispatch(performGistSave()), [dispatch]);

  return (
    <OneButton type="button" title="Create shareable links to this code" onClick={gistSave}>
      Share
    </OneButton>
  );
};

const ToolsMenuButton: React.FC<PortalProps> = ({ menuContainer }) => {
  const Button: React.FC<ButtonProps> = ({ toggle, ref }) => (
    <OneButton
      type="button"
      title="Run extra tools on the source code"
      ref={ref}
      onClick={toggle}
      iconRight={ExpandableIcon}
    >
      Tools
    </OneButton>
  );

  return <PopButton Button={Button} Menu={ToolsMenu} menuContainer={menuContainer} />;
};

const ConfigMenuButton: React.FC<PortalProps> = ({ menuContainer }) => {
  const Button: React.FC<ButtonProps> = ({ toggle, ref }) => (
    <OneButton
      type="button"
      title="Show the configuration options"
      ref={ref}
      onClick={toggle}
      iconLeft={ConfigIcon}
      iconRight={ExpandableIcon}
    >
      Config
    </OneButton>
  );

  return <PopButton Button={Button} Menu={ConfigMenu} menuContainer={menuContainer} />;
};

const HelpButton: React.FC = () => (
  <IconLink title="View help" action={navigateToHelp}>
    <HelpIcon />
  </IconLink>
);

export default Header;
