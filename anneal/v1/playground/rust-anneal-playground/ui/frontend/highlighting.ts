import Prism from 'prismjs';
import { Channel, makePosition, Position } from './types';

interface ConfigureRustErrorsArgs {
  enableFeatureGate: (feature: string) => void;
  getChannel: () => Channel;
  gotoPosition: (p: Position) => void;
  selectText: (start: Position, end: Position) => void;
  addImport: (code: string) => void;
  reExecuteWithBacktrace: () => void;
}

export function configureRustErrors({
  enableFeatureGate,
  getChannel,
  gotoPosition,
  selectText,
  addImport,
  reExecuteWithBacktrace,
}: ConfigureRustErrorsArgs) {
  Prism.languages.rust_errors = {
    'warning': {
      pattern: /^warning(\[E\d+\])?:.*$/m,
      inside: {
        'error-explanation': /\[E\d+\]/,
      },
    },
    'error': {
      pattern: /^error(\[E\d+\])?:.*$/m,
      inside: {
        'error-explanation': /\[E\d+\]/,
      },
    },
    'note': {
      pattern: /^\s*=\s*note:.*$/m,
      inside: {
        'see-issue': /see .*rust-lang\/rust\/issues\/\d+>/,
      },
    },
    'error-location': /-->\s+(\/playground\/)?src\/.*\n/,
    'import-suggestion-outer': {
      pattern: /\+\s+use\s+([^;]+);/,
      inside: {
        'import-suggestion': /use\s+.*/,
      },
    },
    'rust-errors-help': {
      pattern: /help:.*\n/,
      inside: {
        'feature-gate': /add `#!\[feature\(.+?\)\]`/,
      },
    },
    'backtrace': {
      pattern: /at \.\/src\/.*\n/,
      inside: {
        'backtrace-location': /src\/main.rs:(\d+)/,
      },
    },
    'backtrace-enable': /Run with `RUST_BACKTRACE=1` environment variable to display a backtrace/i,
  };

  Prism.languages.rust_mir = {
    'mir-source': /src\/[A-Za-z0-9_.-]+\.rs:\d+:\d+: \d+:\d+/,
  }

  Prism.hooks.add('wrap', env => {
    if (env.type === 'error-explanation') {
      const errorMatch = /E\d+/.exec(env.content);
      if (errorMatch) {
        const [errorCode] = errorMatch;
        env.tag = 'a';
        env.attributes.href = `https://doc.rust-lang.org/${getChannel()}/error_codes/${errorCode}.html`;
        env.attributes.target = '_blank';
      }
    }
    if (env.type === 'see-issue') {
      const errorMatch = /\d+/.exec(env.content);
      if (errorMatch) {
        const [errorCode] = errorMatch;
        env.tag = 'a';
        env.attributes.href = `https://github.com/rust-lang/rust/issues/${errorCode}`;
        env.attributes.target = '_blank';
      }
    }
    if (env.type === 'error-location') {
      let line;
      let col;
      const errorMatchFull = /(\d+):(\d+)/.exec(env.content);
      if (errorMatchFull) {
        line = errorMatchFull[1];
        col = errorMatchFull[2];
      } else {
        const errorMatchShort = /:(\d+)/.exec(env.content);
        if (errorMatchShort) {
          line = errorMatchShort[1];
          col = '1';
        }
      }
      env.tag = 'a';
      env.attributes.href = '#';
      if (line && col) {
        env.attributes['data-line'] = line;
        env.attributes['data-col'] = col;
      }
    }
    if (env.type === 'import-suggestion') {
      env.tag = 'a';
      env.attributes.href = '#';
      env.attributes['data-suggestion'] = env.content;
    }
    if (env.type === 'feature-gate') {
      const featureMatch = /feature\((.*?)\)/.exec(env.content);
      if (featureMatch) {
        const [_, featureGate] = featureMatch;
        env.tag = 'a';
        env.attributes.href = '#';
        env.attributes['data-feature-gate'] = featureGate;
      }
    }
    if (env.type === 'backtrace-enable') {
      env.tag = 'a';
      env.attributes.href = '#';
      env.attributes['data-backtrace-enable'] = 'true';
    }
    if (env.type === 'backtrace-location') {
      const errorMatch = /:(\d+)/.exec(env.content);
      if (errorMatch) {
        const [_, line] = errorMatch;
        env.tag = 'a';
        env.attributes.href = '#';
        env.attributes['data-line'] = line;
        env.attributes['data-col'] = '1';
      }
    }
    if (env.type === 'mir-source') {
      const lineMatch = /(\d+):(\d+): (\d+):(\d+)/.exec(env.content);
      if (lineMatch) {
        const [_, startLine, startCol, endLine, endCol] = lineMatch;
        env.tag = 'a';
        env.attributes.href = '#';
        env.attributes['data-start-line'] = startLine;
        env.attributes['data-start-col'] = startCol;
        env.attributes['data-end-line'] = endLine;
        env.attributes['data-end-col'] = endCol;
      }
    }
  });

  Prism.hooks.add('after-highlight', env => {
    const links = env.element.querySelectorAll('.error-location, .backtrace-location');
    Array.from(links).forEach(link => {
      if (link instanceof HTMLAnchorElement) {
        const { line, col } = link.dataset;
        link.onclick = e => {
          e.preventDefault();
          if (line && col) {
            gotoPosition(makePosition(line, col));
          }
        };
      }
    });

    const importSuggestions = env.element.querySelectorAll('.import-suggestion');
    Array.from(importSuggestions).forEach(link => {
      if (link instanceof HTMLAnchorElement) {
        const { suggestion } = link.dataset;
        link.onclick = (e) => {
          e.preventDefault();
          addImport(suggestion + '\n');
        };
      }
    });

    const featureGateEnablers = env.element.querySelectorAll('.feature-gate');
    Array.from(featureGateEnablers).forEach(link => {
      if (link instanceof HTMLAnchorElement) {
        link.onclick = e => {
          e.preventDefault();
          if (link.dataset.featureGate) {
            enableFeatureGate(link.dataset.featureGate);
            gotoPosition(makePosition(1, 1));
          }
        };
      }
    });

    const backtraceEnablers = env.element.querySelectorAll('.backtrace-enable');
    Array.from(backtraceEnablers).forEach(link => {
      if (link instanceof HTMLAnchorElement) {
        link.onclick = e => {
          e.preventDefault();
          reExecuteWithBacktrace();
        };
      }
    });

    const mirSourceLinks = env.element.querySelectorAll('.mir-source');
    Array.from(mirSourceLinks).forEach(link => {
      if (link instanceof HTMLAnchorElement) {
        const { startLine, startCol, endLine, endCol } = link.dataset;
        if (startLine && startCol && endLine && endCol) {
          const start = makePosition(startLine, startCol);
          const end = makePosition(endLine, endCol);

          link.onclick = e => {
            e.preventDefault();
            selectText(start, end);
          };
        }
      }
    });
  });
}
