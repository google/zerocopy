import React, { ChangeEvent, FormEvent, KeyboardEvent, useCallback, useRef, useState } from 'react';

import { Button, ButtonSet, IconButton } from './ButtonSet';
import PopButton, { ButtonProps, MenuProps } from './PopButton';
import { useAppDispatch, useAppSelector } from './hooks';
import {
  wsExecuteKillCurrent,
  wsExecuteStdin,
  wsExecuteStdinClose,
} from './reducers/output/execute';
import { enableStdinSelector } from './selectors';

import * as styles from './Stdin.module.css';

const Stdin: React.FC = () => {
  const dispatch = useAppDispatch();
  const disabled = !useAppSelector(enableStdinSelector);

  const [content, setContent] = useState('');

  const form = useRef<HTMLFormElement>(null);

  const handleKeyDown = useCallback(
    (e: KeyboardEvent<HTMLTextAreaElement>) => {
      if (e.key === 'Enter' && !e.shiftKey) {
        e.preventDefault();
        form.current?.dispatchEvent(new Event('submit', { bubbles: true, cancelable: true }));
      }

      if (e.key === 'c' && e.ctrlKey) {
        dispatch(wsExecuteKillCurrent());
      }

      if (e.key === 'd' && e.ctrlKey && content.length === 0) {
        dispatch(wsExecuteStdinClose());
      }
    },
    [dispatch, form, content],
  );

  const handleChange = useCallback(
    (e: ChangeEvent<HTMLTextAreaElement>) => {
      setContent(e.currentTarget.value);
    },
    [setContent],
  );

  const handleSubmit = useCallback(
    (e: FormEvent<HTMLFormElement>) => {
      e.preventDefault();

      dispatch(wsExecuteStdin(content + '\n'));

      setContent('');
    },
    [dispatch, content, setContent],
  );

  const menuContainer = useRef<HTMLDivElement | null>(null);

  return (
    <div data-test-id="stdin">
      <form onSubmit={handleSubmit} className={styles.form} ref={form}>
        <div className={styles.multiLine}>
          <textarea
            rows={1}
            onKeyDown={handleKeyDown}
            onChange={handleChange}
            name="content"
            autoComplete="off"
            spellCheck="false"
            className={styles.text}
            value={content}
            disabled={disabled}
          ></textarea>
          <p className={styles.sizer}>{content} </p>
        </div>

        <ButtonSet className={styles.buttons}>
          <Button isPrimary isSmall type="submit" disabled={disabled} iconRight={() => '⏎'}>
            Send
          </Button>

          <PopButton Button={MoreButton} Menu={MoreMenu} menuContainer={menuContainer} />
        </ButtonSet>
      </form>
      <div ref={menuContainer} />
    </div>
  );
};

const MoreButton: React.FC<ButtonProps> = ({ toggle, ref }) => {
  const disabled = !useAppSelector(enableStdinSelector);

  return (
    <IconButton
      isSmall
      type="button"
      ref={ref}
      title="Execution control"
      onClick={toggle}
      disabled={disabled}
    >
      ⋮
    </IconButton>
  );
};

const MoreMenu: React.FC<MenuProps> = ({ close }) => {
  const dispatch = useAppDispatch();

  const stdinClose = useCallback(() => {
    dispatch(wsExecuteStdinClose());
    close();
  }, [dispatch, close]);

  const kill = useCallback(() => {
    dispatch(wsExecuteKillCurrent());
    close();
  }, [dispatch, close]);

  return (
    <ul className={styles.menu}>
      <li>
        <button type="button" className={styles.button} onClick={stdinClose}>
          Close stdin
        </button>
      </li>
      <li>
        <button type="button" className={styles.button} onClick={kill}>
          Kill process
        </button>
      </li>
    </ul>
  );
};

export default Stdin;
