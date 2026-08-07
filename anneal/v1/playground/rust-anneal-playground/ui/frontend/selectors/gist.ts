import { createSelector } from '@reduxjs/toolkit';
import { source } from 'common-tags';

import { baseUrlSelector, codeSelector } from '.';
import { State } from '../reducers';

const gistCodeSelector = (state: State) => state.output.gist.code;

// Selects url.query of build configs.
const urlQuerySelector = createSelector(
  (state: State) => state.output.gist.channel,
  (state: State) => state.output.gist.mode,
  (state: State) => state.output.gist.edition,
  (channel, mode, edition) => {
    const res = new URLSearchParams();
    if (channel) {
      res.set('version', channel);
    }
    if (mode) {
      res.set('mode', mode);
    }
    if (edition) {
      res.set('edition', edition);
    }
    return res;
  },
);

export const showGistLoaderSelector = createSelector(
  (state: State) => state.output.gist.requestsInProgress,
  (requestsInProgress) => requestsInProgress > 0,
);

export const permalinkSelector = createSelector(
  baseUrlSelector,
  urlQuerySelector,
  (state: State) => state.output.gist.id,
  (baseUrl, originalQuery, id) => {
    const u = new URL(baseUrl);
    const query = new URLSearchParams(originalQuery);
    if (id) {
      query.set('gist', id);
    }
    u.search = query.toString();
    return u.href;
  },
);

export const textChangedSinceShareSelector = createSelector(
  codeSelector,
  gistCodeSelector,
  (code, gistCode) => code !== gistCode,
);

const codeBlock = (code: string, language = '') => '```' + language + `\n${code}\n` + '```';

const maybeOutput = (code: string | undefined, whenPresent: (_: string) => void) => {
  if (code && code.length !== 0) {
    whenPresent(code);
  }
};

const snippetSelector = createSelector(
  gistCodeSelector,
  (state: State) => state.output.gist.stdout,
  (state: State) => state.output.gist.stderr,
  permalinkSelector,
  (code, stdout, stderr, permalink) => {
    let snippet = '';

    maybeOutput(code, (code) => {
      snippet += source`
        ${codeBlock(code, 'rust')}

        ([Playground](${permalink}))
      `;
    });

    maybeOutput(stdout, (stdout) => {
      snippet += '\n\n';
      snippet += source`
          Output:

          ${codeBlock(stdout)}
        `;
    });

    maybeOutput(stderr, (stderr) => {
      snippet += '\n\n';
      snippet += source`
          Errors:

          ${codeBlock(stderr)}
        `;
    });

    return snippet;
  },
);

export const urloUrlSelector = createSelector(snippetSelector, (snippet) => {
  const newUsersPostUrl = new URL('https://users.rust-lang.org/new-topic');
  newUsersPostUrl.searchParams.set('body', snippet);
  return newUsersPostUrl.href;
});

export const codeUrlSelector = createSelector(
  baseUrlSelector,
  urlQuerySelector,
  gistCodeSelector,
  (baseUrl, originalQuery, code) => {
    const u = new URL(baseUrl);
    const query = new URLSearchParams(originalQuery);
    if (code) {
      query.set('code', code);
    }
    u.search = new URLSearchParams(query).toString();
    return u.href;
  },
);
