import React from 'react';

import Help from './Help';
import Playground from './Playground';
import { useAppSelector } from './hooks';

const PageSwitcher: React.FC = () => {
  const page = useAppSelector((state) => state.page);

  switch (page) {
    case 'index':
      return <Playground />;
    case 'help':
      return <Help />;
  }
}

export default PageSwitcher;
