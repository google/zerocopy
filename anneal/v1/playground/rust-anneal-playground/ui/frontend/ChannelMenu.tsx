import React, { Fragment, useCallback } from 'react';

import MenuGroup from './MenuGroup';
import SelectOne from './SelectOne';

import * as config from './reducers/configuration';
import * as selectors from './selectors';
import { Channel } from './types';
import { useAppDispatch, useAppSelector } from './hooks';

import * as styles from './ChannelMenu.module.css';

interface ChannelMenuProps {
  close: () => void;
}

const ChannelMenu: React.FC<ChannelMenuProps> = props => {
  const channel = useAppSelector((state) => state.configuration.channel);
  const stableVersion = useAppSelector(selectors.stableVersionText);
  const betaVersion = useAppSelector(selectors.betaVersionText);
  const nightlyVersion = useAppSelector(selectors.nightlyVersionText);
  const betaVersionDetails = useAppSelector(selectors.betaVersionDetailsText);
  const nightlyVersionDetails = useAppSelector(selectors.nightlyVersionDetailsText);

  const dispatch = useAppDispatch();
  const changeChannel = useCallback((channel: Channel) => {
    dispatch(config.changeChannel(channel));
    props.close();
  }, [dispatch, props]);

  return (
    <Fragment>
      <MenuGroup title="Channel &mdash; Choose the rust version">
        <SelectOne
          name="Stable channel"
          currentValue={channel}
          thisValue={Channel.Stable}
          changeValue={changeChannel}
        >
          <Desc>Build using the Stable version: {stableVersion}</Desc>
        </SelectOne>
        <SelectOne
          name="Beta channel"
          currentValue={channel}
          thisValue={Channel.Beta}
          changeValue={changeChannel}
        >
          <Desc>Build using the Beta version: {betaVersion}</Desc>
          <Desc>({betaVersionDetails})</Desc>
        </SelectOne>
        <SelectOne
          name="Nightly channel"
          currentValue={channel}
          thisValue={Channel.Nightly}
          changeValue={changeChannel}
        >
          <Desc>Build using the Nightly version: {nightlyVersion}</Desc>
          <Desc>({nightlyVersionDetails})</Desc>
        </SelectOne>
      </MenuGroup>
    </Fragment>
  );
};

const Desc: React.FC<React.PropsWithChildren<unknown>> = ({ children }) => (
  <p className={styles.description}>{children}</p>
);

export default ChannelMenu;
