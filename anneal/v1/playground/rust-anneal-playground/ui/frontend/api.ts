import * as z from 'zod';

export const routes = {
  compile: '/compile',
  execute: '/execute',
  format: '/format',
  clippy: '/clippy',
  miri: '/miri',
  macroExpansion: '/macro-expansion',
  meta: {
    crates: '/meta/crates',
    versions: '/meta/versions',
    gistSave: '/meta/gist',
    gistLoad: '/meta/gist/id',
  },
};

type FetchArg = Parameters<typeof fetch>[0];

export function jsonGet(url: FetchArg): Promise<unknown> {
  return fetchJson(url, {
    method: 'get',
  });
}

type ToJson = Parameters<typeof JSON.stringify>[0];

export function jsonPost(url: FetchArg, body: ToJson): Promise<unknown> {
  return fetchJson(url, {
    method: 'post',
    body: JSON.stringify(body),
  });
}

const ErrorResponse = z.object({
  error: z.string(),
});
type ErrorResponse = z.infer<typeof ErrorResponse>;

async function fetchJson(url: FetchArg, args: RequestInit) {
  const headers = new Headers(args.headers);
  headers.set('Content-Type', 'application/json');

  const response = await fetch(url, { ...args, headers });
  const body = await response.json();

  if (response.ok) {
    // HTTP 2xx
    return body;
  } else {
    // HTTP 4xx, 5xx (e.g. malformed JSON request)
    const error = await ErrorResponse.parseAsync(body);
    throw new Error(`The server reported an error: ${error.error}`);
  }
}
