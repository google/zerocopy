import React from 'react';

import Example from './HelpExample';
import Link from './uss-router/Link';

import * as styles from './Help.module.css';

import integer32Logo from './assets/integer32-logo.svg';
import { navigateToIndex } from './reducers/page';
import { useAppSelector } from './hooks';
import { baseUrlSelector } from './selectors';

const ACE_URL = 'https://github.com/ajaxorg/ace';
const MONACO_URL = 'https://microsoft.github.io/monaco-editor/';
const CLIPPY_URL = 'https://github.com/rust-lang/rust-clippy';
const MIRI_URL = 'https://github.com/rust-lang/miri';
const CRATES_IO_URL = 'https://crates.io/';
const RUST_COOKBOOK_URL = 'https://rust-lang-nursery.github.io/rust-cookbook/';
const CRATES_URL = 'https://github.com/rust-lang/rust-playground/blob/main/compiler/base/Cargo.toml';
const GIST_URL = 'https://gist.github.com/';
const I32_URL = 'http://integer32.com/';
const LOCALSTORAGE_URL = 'https://developer.mozilla.org/en-US/docs/Web/API/Web_Storage_API';
const ORIGINAL_PLAYGROUND_URL = 'https://github.com/rust-lang/rust-playpen';
const REPO_URL = 'https://github.com/rust-lang/rust-playground';
const RUSTFMT_URL = 'https://github.com/rust-lang/rustfmt';
const SHEPMASTER_URL = 'https://github.com/shepmaster/';
const RUST_EDITION_2018_URL = 'https://doc.rust-lang.org/edition-guide/rust-2018/index.html';

const CRATE_EXAMPLE = `use rand::prelude::*;

fn main() {
    let mut rng = rand::rng();
    println!("{}", rng.random::<u8>());
}`;

const CLIPPY_EXAMPLE = `fn main() {
    match true {
        true => println!("true"),
        false => println!("false"),
    }
}`;

const MIRI_EXAMPLE = `fn main() {
    let mut a: [u8; 0] = [];
    unsafe {
        *a.get_unchecked_mut(1) = 1;
    }
}`;

const RUSTFMT_EXAMPLE = `// wow, this is ugly!
fn main ()
{ struct Foo { a: u8, b: String, }
match 4 {2=>{},_=>{}} }`;

const LINK_EXAMPLE_CODE = 'fn main() { println!("hello world!"); }';

const TEST_EXAMPLE = `#[test]
fn test_something() {
    assert_ne!(42, 0);
}`;

const LIBRARY_EXAMPLE = `#![crate_type="lib"]

pub fn library_fn() -> u8 {
    42
}`;

const OUTPUT_EXAMPLE = `#[inline(never)]
pub fn a_loop() -> i32 {
    let mut sum = 0;
    for i in 0..100 {
        sum += i;
    }
    sum
}

fn main() {
    println!("{}", a_loop());
}`;

const Help: React.FC = () => {
  const baseUrl = useAppSelector(baseUrlSelector);

  // Deliberately **not** using normal tools that would escape
  // characters. The example code we use is fine for URLs, and
  // skipping the escaping makes the docs prettier.
  const linkExample = `${baseUrl}?code=${LINK_EXAMPLE_CODE}`;

  return (
    <section className={styles.container}>
      <h1>The Rust Playground</h1>
      <Link action={navigateToIndex}>Return to the playground</Link>

      <LinkableSection id="about" header="About" level="h2">
        <p>
          The playground is an <a href={REPO_URL}>open source project</a>.
          If you have any suggestions for features, issues with the
          implementation, or just want to read the code for yourself,
          you are invited to participate!
        </p>

        <p>
          This playground is modeled after the <a href={ORIGINAL_PLAYGROUND_URL}>original
        Rust playground</a>, and we owe a great debt to every contributor to
                                      that project.
        </p>

        <p>
          This playground was created by <a href={SHEPMASTER_URL}>Jake Goulding</a>,
        part of <a href={I32_URL}>Integer 32</a>.
        </p>

        <p className={styles.logo}>
          <a href={I32_URL}>
            <img src={integer32Logo} alt="Integer 32 Logo" />
          </a>
        </p>
      </LinkableSection>

      <LinkableSection id="features" header="Features" level="h2">
        <LinkableSection id="features-crates" header="Crates" level="h3">
          <p>
            The playground provides the top 100 most downloaded crates
          from <a href={CRATES_IO_URL}>crates.io</a>, the crates from
          the <a href={RUST_COOKBOOK_URL}>Rust Cookbook</a>, and all
                                        of their dependencies. To use a crate, add the appropriate
            {' '}
            <Code>extern crate foo</Code> line to the code, or, since
            {' '}
            <a href={RUST_EDITION_2018_URL}>Rust Edition 2018</a>, just
            {' '}
            <Code>use</Code> any item from that crate.
          </p>

          <Example code={CRATE_EXAMPLE} />

          <p>
            See the <a href={CRATES_URL}>complete list of crates</a> to know
            what’s available.
          </p>
        </LinkableSection>

        <LinkableSection id="features-formatting" header="Formatting code" level="h3">
          <p>
            <a href={RUSTFMT_URL}>rustfmt</a> is a tool for formatting Rust code
          according to the Rust style guidelines. Click on the <strong>Format</strong>
            {' '}
            button in the <strong>Tools</strong> menu to automatically reformat your code.
          </p>

          <Example code={RUSTFMT_EXAMPLE} />
        </LinkableSection>

        <LinkableSection id="features-linting" header="Linting code" level="h3">
          <p>
            <a href={CLIPPY_URL}>Clippy</a> is a collection of lints to catch common
          mistakes and improve your Rust code. Click on the <strong>Clippy</strong>
            {' '}
            button in the <strong>Tools</strong> menu to see possible improvements to your
            code.
          </p>

          <Example code={CLIPPY_EXAMPLE} />
        </LinkableSection>

        <LinkableSection id="features-miri" header="Checking code for undefined behavior" level="h3">
          <p>
            <a href={MIRI_URL}>Miri</a> is an interpreter for Rust’s mid-level intermediate
            representation (MIR) and can be used to detect certain kinds of undefined behavior
          in your unsafe Rust code. Click on the <strong>Miri</strong> button in
          the <strong>Tools</strong> menu to check.
          </p>

          <Example code={MIRI_EXAMPLE} />
        </LinkableSection>

        <LinkableSection id="features-sharing" header="Sharing code" level="h3">
          <p>
            Once you have some code worth saving or sharing, click on the
            {' '}
            <strong>Share</strong> button. This will create a
            {' '}
            <a href={GIST_URL}>GitHub Gist</a>. You will also be provided with
            a URL to load that Gist back into the playground.
          </p>
        </LinkableSection>

        <LinkableSection id="features-linking" header="Linking to the playground with initial code" level="h3">
          <p>
            If you have a web page with Rust code that you’d like to
            show in action, you can link to the playground with the
          Rust code in the query parameter <Code>code</Code>. Make sure to
                                        escape any special characters. Keep the code short, as URLs have
                                        limitations on the maximum length.
          </p>

          <pre className={styles.code}><code>{linkExample}</code></pre>
        </LinkableSection>

        <LinkableSection id="features-tests" header="Executing tests" level="h3">
          <p>
            If your code contains the <Code>#[test]</Code> attribute and does not
          contain a <Code>main</Code> method, <Code>cargo test</Code> will be
          executed instead of <Code>cargo run</Code>.
          </p>

          <Example code={TEST_EXAMPLE} />
        </LinkableSection>

        <LinkableSection id="features-library" header="Compiling as a library" level="h3">
          <p>
            If your code contains the <Code>#![crate_type=&quot;lib&quot;]</Code> attribute,
            {' '}
            <Code>cargo build</Code> will be executed instead of <Code>cargo
          run</Code>.
          </p>

          <Example code={LIBRARY_EXAMPLE} />
        </LinkableSection>

        <LinkableSection id="features-output-formats" header="Output formats" level="h3">
          <p>
            Instead of executing the code, you can also see intermediate
            output of the compiler as x86_64 assembly, LLVM IR, Rust MIR, or
            WebAssembly. This is often used in conjunction with the
            {' '}
            <a href="#features-modes">mode</a> set to “Release” to see how the
            compiler has chosen to optimize some specific piece of code.
          </p>

          <Example code={OUTPUT_EXAMPLE} />
        </LinkableSection>

        <LinkableSection id="features-modes" header="Compilation modes" level="h3">
          <p>
            Rust has two primary compilation modes: <strong>Debug</strong> and
            {' '}
            <strong>Release</strong>. Debug compiles code faster while Release
            performs more aggressive optimizations.
          </p>

          <p>
            You can choose which mode to compile in using the <strong>Mode</strong>
            {' '}
            menu.
          </p>
        </LinkableSection>

        <LinkableSection id="features-channels" header="Rust channels" level="h3">
          <p>
            Rust releases new <strong>stable</strong> versions every 6
          weeks. Between these stable releases, <strong>beta</strong> versions of the
                                        next stable release are made available. In addition, builds containing
          experimental features are produced <strong>nightly</strong>.
          </p>

          <p>
            You can choose which channel to compile with using the
            {' '}
            <strong>Channel</strong> menu.
          </p>
        </LinkableSection>

        <LinkableSection id="features-customization" header="Customization" level="h3">
          <p>
            The <a href={ACE_URL}>Ajax.org Cloud9 Editor (Ace)</a> is used to
            provide a better interface for editing code. Ace comes with
            several keybinding options (such as Emacs and Vim) as well as many
            themes.
          </p>

          <p>
            You may choose to use the <a href={MONACO_URL}>Monaco</a> editor instead.
            This editor is used in VS Code and may be more familiar to people who
            use VS Code.
          </p>

          <p>
            You may also disable Ace and Monaco completely, falling back to a
            simple HTML text area.
          </p>

          <p>
            These options can be configured via the <strong>Config</strong> menu.
          </p>
        </LinkableSection>

        <LinkableSection id="features-persistence" header="Persistence" level="h3">
          <p>
            The most recently entered code will be automatically saved in your browser’s
            {' '}
            <a href={LOCALSTORAGE_URL}>local storage</a>. This allows you to recover
            your last work even if you close the browser.
          </p>

          <p>
            Local storage is a singleton resource, so if you use multiple windows,
            only the most recently saved code will be persisted.
          </p>
        </LinkableSection>
      </LinkableSection>

      <LinkableSection id="limitations" header="Limitations" level="h2">
        <p>
          To prevent the playground from being used to attack other computers and
          to ensure it is available for everyone to use, some limitations
          are enforced.
        </p>

        <dl>
          <dt>Network</dt>
          <dd>
            There is no network connection available during compilation or
            execution of user-submitted code.
          </dd>

          <dt>Memory</dt>
          <dd>
            The amount of memory the compiler and resulting executable use is
            limited.
          </dd>

          <dt>Execution Time</dt>
          <dd>
            The total compilation and execution time is limited.
          </dd>

          <dt>Disk</dt>
          <dd>
            The total disk space available to the compiler and resulting
            executable is limited.
          </dd>
        </dl>
      </LinkableSection>
    </section>
  );
};

const LinkableSection: React.FC<LinkableSectionProps> = ({
  id, header, level: Level, children,
}) => (
  <div id={id}>
    <Level>
      <span className={styles.header}>
        <a className={styles.headerLink} href={`#${id}`}>{header}</a>
      </span>
    </Level>
    {children}
  </div>
);

interface LinkableSectionProps {
  children: React.ReactNode;
  id: string;
  header: string;
  level: React.ElementType;
}

const Code: React.FC<React.PropsWithChildren<unknown>> = ({ children }) => (
  <code className={styles.code}>{children}</code>
);

export default Help;
