import React from 'react';

import { CommonEditorProps, Position, Selection } from '../types';

import * as styles from './Editor.module.css';

class CodeByteOffsets {
  readonly code: string;
  readonly lines: string[];

  constructor(code: string) {
    this.code = code;
    this.lines = code.split('\n');
  }

  public lineToOffsets(line: number) {
    const precedingBytes = this.bytesBeforeLine(line);
    const nextPrecedingBytes = this.bytesBeforeLine(line + 1);

    return [precedingBytes, nextPrecedingBytes];
  }

  public rangeToOffsets(start: Position, end: Position) {
    const startBytes = this.positionToBytes(start);
    const endBytes = this.positionToBytes(end);
    return [startBytes, endBytes];
  }

  private positionToBytes(position: Position) {
    // Subtract one as this logic is zero-based and the columns are one-based
    return this.bytesBeforeLine(position.line) + position.column - 1;
  }

  private bytesBeforeLine(line: number) {
    // Subtract one as this logic is zero-based and the lines are one-based
    line -= 1;

    const precedingLines = this.lines.slice(0, line);

    // Add one to account for the newline we split on and removed
    return precedingLines.map((l) => l.length + 1).reduce((a, b) => a + b, 0);
  }
}

class SimpleEditor extends React.PureComponent<CommonEditorProps> {
  private _editor: HTMLTextAreaElement | null = null;

  private onChange: React.ChangeEventHandler<HTMLTextAreaElement> = (e) =>
    this.props.onEditCode(e.target.value);
  private trackEditor: React.RefCallback<HTMLTextAreaElement> = (component) => {
    this._editor = component;
  };
  private onKeyDown: React.KeyboardEventHandler<HTMLTextAreaElement> = (e) => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
      this.props.execute();
    }
  };

  public render() {
    return (
      <textarea
        ref={this.trackEditor}
        className={styles.simple}
        name="editor-simple"
        autoCapitalize="none"
        autoComplete="off"
        autoCorrect="off"
        spellCheck={false}
        value={this.props.code}
        onChange={this.onChange}
        onKeyDown={this.onKeyDown}
      />
    );
  }

  public componentDidUpdate(prevProps: CommonEditorProps) {
    this.gotoPosition(prevProps.position, this.props.position);
    this.setSelection(prevProps.selection, this.props.selection);
  }

  private gotoPosition(oldPosition: Position, newPosition: Position) {
    const editor = this._editor;

    if (!newPosition || !editor) {
      return;
    }
    if (newPosition === oldPosition) {
      return;
    }

    const offsets = new CodeByteOffsets(this.props.code);
    const [startBytes, endBytes] = offsets.lineToOffsets(newPosition.line);

    editor.focus();
    editor.setSelectionRange(startBytes, endBytes);
  }

  private setSelection(oldSelection: Selection, newSelection: Selection) {
    const editor = this._editor;

    if (!newSelection || !newSelection.start || !newSelection.end || !editor) {
      return;
    }
    if (newSelection === oldSelection) {
      return;
    }

    const offsets = new CodeByteOffsets(this.props.code);
    const [startBytes, endBytes] = offsets.rangeToOffsets(newSelection.start, newSelection.end);

    editor.focus();
    editor.setSelectionRange(startBytes, endBytes);
  }
}

export default SimpleEditor;
