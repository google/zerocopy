import React from 'react';
import { Reducer, UnknownAction } from '@reduxjs/toolkit';

import { createBrowserHistory as createHistory, Path, Location } from 'history';
import { createRouter, PlainOrThunk, RouterObject, StoreArg } from './uss-router';
import UssRouter from './uss-router/Router';

import qs from 'qs';
import Route from 'route-parser';

import * as actions from './actions';
import { State } from './reducers';
import { Channel, Edition, Mode, Page } from './types';

const homeRoute = new Route('/');
const helpRoute = new Route('/help');

interface Substate {
  page: Page;
  configuration: {
    channel: Channel;
    mode: Mode;
    edition: Edition;
  };
  output: {
    gist: {
      id?: string;
    }
  }
}

const stateSelector = ({ page, configuration: { channel, mode, edition}, output }: State): Substate => ({
  page,
  configuration: {
    channel,
    mode,
    edition,
  },
  output: {
    gist: {
      id: output.gist.id,
    },
  },
});

const stateToLocation = ({ page, configuration, output }: Substate): Partial<Path> => {
  switch (page) {
    case 'help': {
      return {
        pathname: '/help',
      };
    }

    default: {
      const query = {
        version: configuration.channel,
        mode: configuration.mode,
        edition: configuration.edition,
        gist: output.gist.id,
      };
      return {
        pathname: `/?${qs.stringify(query)}`,
      };
    }
  }
};

const locationToAction = (location: Location): PlainOrThunk<State, UnknownAction> | null => {
  const matchedHelp = helpRoute.match(location.pathname);

  if (matchedHelp) {
    return actions.helpPageLoad();
  }

  const matched = homeRoute.match(location.pathname);

  if (matched) {
    return actions.indexPageLoad(qs.parse(location.search.slice(1)));
  }

  return null;
};

export default class Router extends React.Component<RouterProps> {
  private router: RouterObject<UnknownAction>;

  public constructor(props: RouterProps) {
    super(props);

    const history = createHistory();

    const { store, reducer } = props;

    this.router = createRouter({
      store, reducer,
      history, stateSelector, locationToAction, stateToLocation,
    });
  }

  public render() {
    return <UssRouter router={this.router}>{this.props.children}</UssRouter>;
  }
}

interface RouterProps {
  children: React.ReactNode;
  store: StoreArg<State, UnknownAction>;
  reducer: Reducer<State>;
}
