import React, { useCallback } from 'react';
import { Portal } from 'react-portal';

import { Close } from './Icon';
import { useAppDispatch, useAppSelector } from './hooks';
import * as client from './reducers/client';
import { seenRustSurvey2025 } from './reducers/notifications';
import { allowLongRun, wsExecuteKillCurrent } from './reducers/output/execute';
import * as selectors from './selectors';

import * as styles from './Notifications.module.css';

const SURVEY_URL = 'https://blog.rust-lang.org/2025/11/17/launching-the-2025-state-of-rust-survey/';

const Notifications: React.FC = () => {
  return (
    <Portal>
      <div className={styles.container}>
        <RustSurvey2025Notification />
        <ExcessiveExecutionNotification />
        <ResetConfigurationNotification />
        <ResetOldConfigurationNotification />
      </div>
    </Portal>
  );
};

const RustSurvey2025Notification: React.FC = () => {
  const showIt = useAppSelector(selectors.showRustSurvey2025Selector);

  const dispatch = useAppDispatch();
  const seenIt = useCallback(() => dispatch(seenRustSurvey2025()), [dispatch]);

  return showIt ? (
    <Notification onClose={seenIt}>
      Please help us take a look at who the Rust community is composed of, how the Rust project is
      doing, and how we can improve the Rust programming experience by completing the{' '}
      <a href={SURVEY_URL}>2025 State of Rust Survey</a>. Whether or not you use Rust today, we want
      to know your opinions.
    </Notification>
  ) : null;
};

const ExcessiveExecutionNotification: React.FC = () => {
  const showExcessiveExecution = useAppSelector(selectors.excessiveExecutionSelector);
  const time = useAppSelector(selectors.excessiveExecutionTimeSelector);
  const gracePeriod = useAppSelector(selectors.killGracePeriodTimeSelector);

  const dispatch = useAppDispatch();
  const allow = useCallback(() => dispatch(allowLongRun()), [dispatch]);
  const kill = useCallback(() => dispatch(wsExecuteKillCurrent()), [dispatch]);

  return showExcessiveExecution ? (
    <Notification onClose={allow}>
      The running process has used more than {time} of CPU time. This is often caused by an error in
      the code. As the playground is a shared resource, the process will be automatically killed in{' '}
      {gracePeriod}. You can always kill the process manually via the menu at the bottom of the
      screen.
      <div className={styles.action}>
        <button onClick={kill}>Kill the process now</button>
        <button onClick={allow}>Allow the process to continue</button>
      </div>
    </Notification>
  ) : null;
};

interface ResetNotificationCommonProps {
  preamble?: string;
  onReset: () => void;
  onCancel: () => void;
}

const ResetNotificationCommon: React.FC<ResetNotificationCommonProps> = ({
  preamble,
  onReset,
  onCancel,
}) => (
  <Notification onClose={onCancel}>
    {preamble}
    Would you like to reset all code and configuration back to the default values to get a fresh
    start?
    <div className={styles.action}>
      <button onClick={onReset}>Reset all code and configuration</button>
      <button onClick={onCancel}>Keep the current code and configuration</button>
    </div>
  </Notification>
);

const ResetConfigurationNotification: React.FC = () => {
  const showResetConfiguration = useAppSelector(selectors.resetConfigurationSelector);

  const dispatch = useAppDispatch();
  const reset = useCallback(() => dispatch(client.resetEverything()), [dispatch]);
  const keep = useCallback(() => dispatch(client.hideConfigReset()), [dispatch]);

  return showResetConfiguration ? (
    <ResetNotificationCommon onReset={reset} onCancel={keep} />
  ) : null;
};

const ResetOldConfigurationNotification: React.FC = () => {
  const showResetOldConfiguration = useAppSelector(selectors.resetOldConfigurationSelector);

  const dispatch = useAppDispatch();
  const reset = useCallback(() => dispatch(client.resetEverything()), [dispatch]);
  const keep = useCallback(() => dispatch(client.updateLastVisitedAt()), [dispatch]);

  const preamble = "It's been a while since you've used the Playground. ";

  return showResetOldConfiguration ? (
    <ResetNotificationCommon preamble={preamble} onReset={reset} onCancel={keep} />
  ) : null;
};

interface NotificationProps {
  children: React.ReactNode;
  onClose: () => void;
}

const Notification: React.FC<NotificationProps> = ({ onClose, children }) => (
  <div className={styles.notification} data-test-id="notification">
    <div className={styles.notificationContent}>{children}</div>
    <button className={styles.close} onClick={onClose} title="dismiss notification">
      <Close />
    </button>
  </div>
);

export default Notifications;
