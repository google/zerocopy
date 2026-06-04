import * as z from 'zod';

export type Page = 'index' | 'help';

export interface Position {
  line: number;
  column: number;
}

export const makePosition = (line: string | number, column: string | number): Position => ({
  line: +line,
  column: +column,
});

export interface Selection {
  start?: Position;
  end?: Position;
}

export const Crate = z.object({
  id: z.string(),
  name: z.string(),
  version: z.string(),
});

export type Crate = z.infer<typeof Crate>;

export const Version = z.object({
  version: z.string(),
  hash: z.string(),
  date: z.string(),
});

export type Version = z.infer<typeof Version>;

export const ChannelVersion = z.object({
  rustc: Version,
  rustfmt: Version,
  clippy: Version,
  miri: Version.optional(),
});

export type ChannelVersion = z.infer<typeof ChannelVersion>;

export interface CommonEditorProps {
  code: string;
  execute: () => void;
  onEditCode: (_: string) => void;
  position: Position;
  selection: Selection;
  crates: Crate[];
}

export enum Editor {
  Simple = 'simple',
  Ace = 'ace',
  Monaco = 'monaco',
}

export enum PairCharacters {
  Enabled = 'enabled',
  Disabled = 'disabled',
}

export enum Orientation {
  Automatic = 'automatic',
  Horizontal = 'horizontal',
  Vertical = 'vertical',
}

export enum Theme {
  Light = 'light',
  Dark = 'dark',
  System = 'system',
}

export enum AssemblyFlavor {
  Att = 'att',
  Intel = 'intel',
}

export enum DemangleAssembly {
  Demangle = 'demangle',
  Mangle = 'mangle',
}

export enum ProcessAssembly {
  Filter = 'filter',
  Raw = 'raw',
}

export enum PrimaryActionAuto {
  Auto = 'auto',
}

export enum PrimaryActionCore {
  Asm = 'asm',
  Compile = 'compile',
  Execute = 'execute',
  LlvmIr = 'llvm-ir',
  Hir = 'hir',
  Mir = 'mir',
  Test = 'test',
  Wasm = 'wasm',
  Anneal = 'anneal-verify',
}

export type PrimaryAction = PrimaryActionCore | PrimaryActionAuto;

export enum Channel {
  Stable = 'stable',
  Beta = 'beta',
  Nightly = 'nightly',
}

const ChannelEnum = z.nativeEnum(Channel);

export function parseChannel(s?: string): Channel | null {
  const p = ChannelEnum.safeParse(s);
  return p.success ? p.data : null;
}

export enum Mode {
  Debug = 'debug',
  Release = 'release',
}

const ModeEnum = z.nativeEnum(Mode);

export function parseMode(s?: string): Mode | null {
  const p = ModeEnum.safeParse(s);
  return p.success ? p.data : null;
}

export enum Edition {
  Rust2015 = '2015',
  Rust2018 = '2018',
  Rust2021 = '2021',
  Rust2024 = '2024',
}

const EditionEnum = z.nativeEnum(Edition);

export function parseEdition(s?: string): Edition | null {
  const p = EditionEnum.safeParse(s);
  return p.success ? p.data : null;
}

export enum Backtrace {
  Disabled = 'disabled',
  Enabled = 'enabled',
}

export enum AliasingModel {
  Stacked = 'stacked',
  Tree = 'tree',
}

export enum Focus {
  Clippy = 'clippy',
  Miri = 'miri',
  MacroExpansion = 'macro-expansion',
  LlvmIr = 'llvm-ir',
  Mir = 'mir',
  Hir = 'hir',
  Wasm = 'wasm',
  Asm = 'asm',
  Execute = 'execute',
  Format = 'format',
  Gist = 'gist',
}

export enum Notification {
  RustSurvey2025 = 'rust-survey-2025',
}
