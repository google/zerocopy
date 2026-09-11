import React, { createContext } from 'react';
import { UnknownAction } from '@reduxjs/toolkit';

import { RouterObject } from '.';

export const Context = createContext<RouterObject<UnknownAction> | undefined>(undefined);

interface RouterProps<A extends UnknownAction> {
  children: React.ReactNode;
  router: RouterObject<A>;
}

const Router: React.FC<RouterProps<UnknownAction>> = ({router, children}) => (
  <Context.Provider value={router}>
    {children}
  </Context.Provider>
);

export default Router;
