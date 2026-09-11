import React from 'react';

import SelectableMenuItem from './SelectableMenuItem';

interface SelectOneProps<T> {
  children: React.ReactNode;
  name: string;
  currentValue: T;
  thisValue: T;
  changeValue: (_: T) => void;
}

export default class SelectOne<T> extends React.PureComponent<SelectOneProps<T>> {
  public render() {
    const { name, currentValue, thisValue, children, changeValue } = this.props;

    return (
      <SelectableMenuItem
        name={name}
        selected={currentValue === thisValue}
        onClick={() => changeValue(thisValue)}>
        {children}
      </SelectableMenuItem>
    );
  }
}
