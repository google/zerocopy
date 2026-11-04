import React from 'react';

import * as actions from '../actions';
import { useAppDispatch, useAppSelector } from '../hooks';
import { editCode } from '../reducers/code';
import { codeSelector, positionSelector, selectionSelector } from '../selectors';
import { Editor as EditorType } from '../types';
import AceEditor from './AceEditor';
import MonacoEditor from './MonacoEditor';
import SimpleEditor from './SimpleEditor';

import * as styles from './Editor.module.css';

const editorMap = {
  [EditorType.Simple]: SimpleEditor,
  [EditorType.Ace]: AceEditor,
  [EditorType.Monaco]: MonacoEditor,
};

const Editor: React.FC = () => {
  'use memo';

  const code = useAppSelector(codeSelector);
  const editor = useAppSelector((state) => state.configuration.editor);
  const position = useAppSelector(positionSelector);
  const selection = useAppSelector(selectionSelector);
  const crates = useAppSelector((state) => state.crates);

  const dispatch = useAppDispatch();

  const SelectedEditor = editorMap[editor];

  return (
    <div className={styles.container}>
      <SelectedEditor
        code={code}
        position={position}
        selection={selection}
        crates={crates}
        onEditCode={(c) => dispatch(editCode(c))}
        execute={() => dispatch(actions.performPrimaryAction())}
      />
    </div>
  );
};

export default Editor;
