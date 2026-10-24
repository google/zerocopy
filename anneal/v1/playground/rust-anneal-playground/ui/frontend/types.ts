import * as z from 'zod';

type ValuesOf<T> = T[keyof T];

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
export const Editor = {
  Simple: 'simple',
  Ace: 'ace',
  Monaco: 'monaco',
} as const;
export type Editor = ValuesOf<typeof Editor>;
export const EditorSchema = z.enum(Object.values(Editor));

export const PairCharacters = {
  Enabled: 'enabled',
  Disabled: 'disabled',
} as const;
export type PairCharacters = ValuesOf<typeof PairCharacters>;
export const PairCharactersSchema = z.enum(Object.values(PairCharacters));

export const Orientation = {
  Automatic: 'automatic',
  Horizontal: 'horizontal',
  Vertical: 'vertical',
} as const;
export type Orientation = ValuesOf<typeof Orientation>;
export const OrientationSchema = z.enum(Object.values(Orientation));

export const Theme = {
  Light: 'light',
  Dark: 'dark',
  System: 'system',
} as const;
export type Theme = ValuesOf<typeof Theme>;
export const ThemeSchema = z.enum(Object.values(Theme));

export const AssemblyFlavor = {
  Att: 'att',
  Intel: 'intel',
} as const;
export type AssemblyFlavor = ValuesOf<typeof AssemblyFlavor>;
export const AssemblyFlavorSchema = z.enum(Object.values(AssemblyFlavor));

export const DemangleAssembly = {
  Demangle: 'demangle',
  Mangle: 'mangle',
} as const;
export type DemangleAssembly = ValuesOf<typeof DemangleAssembly>;
export const DemangleAssemblySchema = z.enum(Object.values(DemangleAssembly));

export const ProcessAssembly = {
  Filter: 'filter',
  Raw: 'raw',
} as const;
export type ProcessAssembly = ValuesOf<typeof ProcessAssembly>;
export const ProcessAssemblySchema = z.enum(Object.values(ProcessAssembly));

export const PrimaryActionAuto = {
  Auto: 'auto',
} as const;
export type PrimaryActionAuto = ValuesOf<typeof PrimaryActionAuto>;

export const PrimaryActionCore = {
  Asm: 'asm',
  Compile: 'compile',
  Execute: 'execute',
  LlvmIr: 'llvm-ir',
  Hir: 'hir',
  Mir: 'mir',
  Test: 'test',
  Wasm: 'wasm',
  Anneal: 'anneal-verify',
} as const;
export type PrimaryActionCore = ValuesOf<typeof PrimaryActionCore>;

export const PrimaryAction = { ...PrimaryActionAuto, ...PrimaryActionCore };
export type PrimaryAction = ValuesOf<typeof PrimaryAction>;
export const PrimaryActionSchema = z.enum(Object.values(PrimaryAction));

export const Channel = {
  Stable: 'stable',
  Beta: 'beta',
  Nightly: 'nightly',
} as const;
export type Channel = ValuesOf<typeof Channel>;
const ChannelSchema = z.enum(Object.values(Channel));

export function parseChannel(s?: string): Channel | null {
  const p = ChannelSchema.safeParse(s);
  return p.success ? p.data : null;
}

export const Mode = {
  Debug: 'debug',
  Release: 'release',
} as const;
export type Mode = ValuesOf<typeof Mode>;
const ModeSchema = z.enum(Object.values(Mode));

export function parseMode(s?: string): Mode | null {
  const p = ModeSchema.safeParse(s);
  return p.success ? p.data : null;
}

export const Edition = {
  Rust2015: '2015',
  Rust2018: '2018',
  Rust2021: '2021',
  Rust2024: '2024',
} as const;
export type Edition = ValuesOf<typeof Edition>;
const EditionSchema = z.enum(Object.values(Edition));

export function parseEdition(s?: string): Edition | null {
  const p = EditionSchema.safeParse(s);
  return p.success ? p.data : null;
}

export const Backtrace = {
  Disabled: 'disabled',
  Enabled: 'enabled',
} as const;
export type Backtrace = ValuesOf<typeof Backtrace>;

export const AliasingModel = {
  Stacked: 'stacked',
  Tree: 'tree',
} as const;
export type AliasingModel = ValuesOf<typeof AliasingModel>;

export const Focus = {
  Clippy: 'clippy',
  Miri: 'miri',
  MacroExpansion: 'macro-expansion',
  LlvmIr: 'llvm-ir',
  Mir: 'mir',
  Hir: 'hir',
  Wasm: 'wasm',
  Asm: 'asm',
  Execute: 'execute',
  Format: 'format',
  Gist: 'gist',
} as const;
export type Focus = ValuesOf<typeof Focus>;

export const Notification = {
  RustSurvey2025: 'rust-survey-2025',
} as const;
export type Notification = ValuesOf<typeof Notification>;
