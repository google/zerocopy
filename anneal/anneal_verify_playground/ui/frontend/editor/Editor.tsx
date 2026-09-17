import React, { useCallback } from 'react';

import * as actions from '../actions';
import { useAppDispatch } from '../hooks';

import AceEditor from './AceEditor';
import SimpleEditor from './SimpleEditor';
import MonacoEditor from './MonacoEditor';
import { Editor as EditorType } from '../types';
import { codeSelector, positionSelector, selectionSelector } from '../selectors';
import { editCode } from '../reducers/code';
import { useAppSelector } from '../hooks';

import * as styles from './Editor.module.css';

const editorMap = {
  [EditorType.Simple]: SimpleEditor,
  [EditorType.Ace]: AceEditor,
  [EditorType.Monaco]: MonacoEditor,
};

const Editor: React.FC = () => {
  const code = useAppSelector(codeSelector);
  const editor = useAppSelector((state) => state.configuration.editor);
  const position = useAppSelector(positionSelector);
  const selection = useAppSelector(selectionSelector);
  const crates = useAppSelector((state) => state.crates);

  const dispatch = useAppDispatch();
  const execute = useCallback(() => dispatch(actions.performPrimaryAction()), [dispatch]);
  const onEditCode = useCallback((c: string) => dispatch(editCode(c)), [dispatch]);

  const SelectedEditor = editorMap[editor];

  return (
    <div className={styles.container}>
      <SelectedEditor code={code}
        position={position}
        selection={selection}
        crates={crates}
        onEditCode={onEditCode}
        execute={execute} />
    </div>
  );
};

export default Editor;
