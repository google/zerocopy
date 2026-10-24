import React from 'react';

import GenericLoader from '../Loader';
import Header from './Header';

const Loader: React.FC = () => (
  <div>
    <Header label="Progress" />
    <GenericLoader />
  </div>
);

export default Loader;
