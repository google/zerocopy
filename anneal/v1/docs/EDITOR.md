<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Editing a bound Lean workspace

Open the generated Lean project as its own VS Code workspace. Its immutable
SDK binding, private Lake outputs, local `lean-toolchain`, and generated
command gateways belong together. Keep the project's `.anneal-bin` gateway
directory outside SDK/bin. The gateway executes the actual selected SDK
Lean/Lake binaries with the admitted workspace environment.

Generate the workspace with `cargo anneal generate`, then use the printed
workspace path for batch checks or editor startup:

```sh
cargo anneal lean --workspace /absolute/workspace build
cargo anneal lean --workspace /absolute/workspace check generated/Example.lean
cargo anneal lean --workspace /absolute/workspace editor \
  --code '/absolute/Visual Studio Code.app/Contents/Resources/app/bin/code' \
  --extension /absolute/tamasfe.even-better-toml-0.21.2.vsix \
  --extension /absolute/lean4-0.0.240.vsix \
  --state-dir /absolute/short-existing-directory
```

The source path is relative to that workspace. Supply trusted local editor and
extension artifacts. `--state-dir` is optional; its parent must already exist
outside the workspace and SDK installation, be owned by the invoking user, and
not grant another account write access. The launcher checks ACLs on that path,
its ancestors, and the profile root. Only deny entries are accepted; granting
or unknown entries are rejected. It checks the physical identity of the created
profile before each Code command. A granting home-directory ACL can make the
default workspace-adjacent profile ineligible; use a short, existing private
state directory under non-granting ancestry when needed. The launcher prints
its fresh profile directory, runs version and installation commands, and waits
for the private window to close. Use `serve` instead of `editor` for a protocol
client which already implements the isolated process context described below.

The settings template in [`editor-settings.json`](editor-settings.json) uses
stock Lean extension settings verified at version 0.0.240, source commit
`dead846a035f42dc13beb7619ac779538e6ddf6e`. No `lean4.customToolchain` or
`lean4.elanMustBeInstalled` setting is required or supported by the researched
extension manifest. `lean4.showSetupWarnings: false` skips its optional Elan
installation dialog; setup errors remain visible. The binding gateway selects
the SDK without installing or updating Elan. The normal server command is PATH `lake serve --
<project-root>`. Version checks use PATH `lean --version` and `lake --version`.
Additional toolchain selectors or server arguments must not override the
generated workspace binding.

Use an isolated editor process context with private editor state and
`ELAN_HOME`, excluding ambient toolchain/import/loader selectors. The extension
can invoke Elan discovery before invoking the project gateway. A generated
PATH setting alone therefore does not isolate global Elan state or an already
running extension host. Do not run `elan override` or `elan toolchain link` for
this project. An absolute SDK path in `lean-toolchain` requires Elan 4.2.2 or
newer if Elan is used; Elan itself is optional for stock extension startup.

The private launcher in `editor_host.rs` accepts the absolute desktop
Code CLI and explicit absolute local VSIX files. It creates a fresh
profile beside the bound workspace, or beneath an explicit `--state-dir`, records its workspace/SDK ownership, and
offers only version, local installation, and single-workspace launch commands.
During preparation it copies each selected VSIX into the owner-private
profile and records that copy's content digest and physical identity.
Installation commands use those private copies, so later changes to the
original paths do not change what Code installs. The selected bytes are
trusted local inputs at preparation; this does not authenticate their origin.
The profile cannot live in `.runtime`: Chromium creates singleton/socket links,
while compiler private-output admission correctly rejects links there.
The caller records the selected Code version, completes each installation with
exit status zero, and then executes `launch_command`. The private profile must
contain Lean extension 0.0.240 and its TOML dependency. There is no Gallery ID
installation, and automatic extension-pack/dependency retrieval is disabled;
provide dependency VSIX files explicitly as well. On macOS, choose a short
existing absolute `--state-dir` if the default profile location exceeds the
103-byte local IPC limit.

On macOS, GUI launch invokes the selected bundle’s Electron executable directly
so its caller retains process ownership; the shell CLI is used only for version
and local extension installation. The private window disables Git/account
extensions and uses in-memory secret storage.
The selected CLI and Electron executable stay in the application bundle. Their
canonical files must be executable, owned by the invoking user or root, and
protected against writes and pathname replacement by another local account.
The launcher pins their physical identities and checks their modes, ancestor
directories, and ACLs. The rest of the selected Code installation remains a
trusted input at preparation.

Every Code command clears the inherited environment, uses private HOME, XDG,
temporary and Elan directories, and fixes ELAN_TOOLCHAIN to the bound SDK.
`--force-disable-user-env` prevents login-shell environment discovery. A
production-owned VSCODE_PORTABLE path keeps installation-adjacent portable
state from overriding isolation; its user-data and extensions directories
match the explicit CLI flags. The fresh user-data directory prevents reuse of
an unrelated running editor's environment. User settings install the absolute
consumer gateway path, disable Lean server logging, dependency auto-builds,
extension updates and sync. Loader and import selectors are not inherited by
Electron. The launcher currently rejects non-macOS hosts; GUI/session support
on other platforms needs its own reviewed environment contract.

Before constructing each Code command, the launcher checks the generated
Lean/Lake gateway executables and the workspace and private-profile settings
against their bound values. It checks both selected Code executables and every
private VSIX copy before constructing a command and immediately before
executing a previously constructed command. Keep these generated controls
intact; changing gateway paths or contents requires regenerating the workspace.
Changing the selected Code installation requires a fresh editor profile.

These are command-construction guarantees, not an OS network/filesystem
sandbox. VSIX contents and the selected Code executable are trusted local
inputs; editor version/capability checks and observed private-write behavior
remain acceptance requirements. Preserve the profile for review after a
failure, and remove it only after its editor processes have exited.

The freshness coordinator forwards the standard protocol to stock Lake/Lean.
Edits within a file remain incremental. Generated Lake libraries declare exact
local modules, allowing SDK and local modules to share a namespace. Rerun Anneal
after adding or removing a user module so the generated library membership
reflects the new source set. When an imported local source changes,
the coordinator replaces affected diagnostics with a pending notice and
rejects dependent requests with LSP `ContentModified`. A dirty dependency
buffer stays pending without being saved or discarded. Its own document
continues to receive interactive diagnostics.

Once the intended saved inputs are available, the coordinator builds the
current local import closure and runs stock `setup-file` for open local files,
supplying the live RC2 module header through stdin. This keeps unsaved import
changes distinct from the saved dependency state. Unrecognized header syntax
keeps affected results pending instead of guessing metadata.
It does not compile each live proof as a prerequisite for viewing that proof's
errors. Independent files with clean imported inputs can refresh while another
file's dependency buffer remains dirty. A successful unchanged import build is
followed by a stock server restart and replay of the live buffers. Replies are
checked against document versions, imported inputs, and server generations. A
dependency change during build or refresh obsoletes that cycle. Failed import builds keep the
affected results pending. Reverting a dirty dependency can request a new cycle
even if its saved bytes were unchanged.

An external cooperating Anneal writer temporarily suspends the server and
results. Buffers remain queued; after the writer completes, the coordinator
readmits the workspace and establishes a new generation. Build cycles own an
exclusive workspace lease, while normal result reconciliation uses a shared
lease. This is cooperation among project writers, not an operating-system
sandbox or a replacement for immutable SDK storage.

Saved-input freshness includes local data files, not just Lean sources. The
supported local input tree uses one filesystem and a consistent case policy;
cross-filesystem mounts and mixed case policies are rejected. Changes to local
data, saved Lean sources, or build configuration invalidate private build
outputs. This conservatively covers declared Lean providers read as data without
an import edge. Unchanged saved inputs retain warm outputs, and edits within an
open document remain incremental. An interrupted, failed, or obsolete
compilation cannot establish reusable output provenance. Shared SDK artifacts
stay untouched. Compile-time reads outside the immutable SDK and admitted local
input tree, reads of private namespaces, and filesystem metadata dependencies
are outside this contract.

SDK source views may be opened read-only when they belong to the admitted
source providers. SDK buffer modifications are rejected explicitly and never
written to SDK storage. Use a new bound workspace with fresh outputs and a new
server for an SDK upgrade. Untitled documents, foreign projects, caller-chosen
server log directories, and multiple SDKs in one editor context are not part
of the supported coordinator contract.

## Acceptance boundary

The adapter's unit protocol peers exercise its state transitions without
running Lean. They cannot establish native plugin loading, compiled import
correctness, source navigation, or actual VS Code/infoview behavior. Run the
selected tuple's positive/no-axiom, false, forbidden-sorry, native smoke,
navigation, and dependency refresh controls separately.

Actual VS Code acceptance also needs a pinned extension and isolation checks
for existing-process reuse and ambient Elan. A definition target outside the
generated project may cause the extension to launch a separate SDK-source
client. Opening source text is insufficient evidence that that client routes
through the same admitted SDK. Verify SDK-tab routing, RPC session recovery,
pending goal display, and exact source paths before claiming those UI flows
are supported. The stock settings template alone does not establish them.

The pinned extension allocates one client per discovered project root. It
routes literal `.lake/packages` paths to the consumer, but SDK source providers
outside that path retain their own project roots. A source root containing a
Lakefile invokes `lake serve -- <source-root>`; core source roots without a
Lakefile invoke `lean --server <source-root>`. Both commands can have the
explicit toolchain selector prepended. Consequently a lake-only gateway does
not cover core source tabs, and the current strict consumer-root coordinator
rejects foreign-root initialization.

The separate `sdk_source_server.rs` adapter covers these finite source-server
launch classes once the gateway admits their project roots through the runtime.
The directory must be physical, inside the immutable SDK installation, and an
ancestor of an exact published source. That admission is checked once, rather
than rescanning thousands of source paths for every message. Initialization
rootUri/rootPath/workspaceFolders are checked against that source project and
then remapped to the fixed consumer. SDK document URIs remain intact. Every
didOpen must identify an exact published SDK source and contain its immutable
bytes. Edits, saves, edit commands and applyEdit requests are rejected; the
adapter launches only bound stock Lake serve in the consumer context, with
dependencyBuildMode never. It has no local builds or refresh coordinator.

This source-only client has its own process group and no primary-server lease.
A temporary startup writer lease protects launch/initialization; subsequent
forwarding boundaries use shared leases and a captured consumer source stamp.
Writer contention waits interruptibly for at most 60 seconds, then requires
the original saved consumer context before resuming. A timeout or changed
context ends this conservative client: use the stock Restart Server action
after the writer completes. Closed-document
requests receive ContentModified, and remapped request IDs discard late replies.
The pure admission/remap/buffer tests do not establish stock Lake setup for
outside-project SDK files, extension document selection, or infoview RPC
recovery. Sources
outside the admitted installation and arbitrary foreign project roots remain
unsupported even when source text can be opened in an editor tab.

Automated acceptance on macOS arm64 used Code 1.100.3, Lean extension 0.0.240,
TOML 0.21.2, and the exact Lean 4.30.0-rc2/Aeneas/Mathlib SDK. It passed false
and true proof controls, useful goals and RPC, unsaved-buffer preservation
through saved dependency changes, exact Aeneas and Mathlib definitions,
SDK-source hover/RPC, source-tab closure, late RPC housekeeping, and consumer
RPC recovery. The 61,698-entry shared installation metadata inventory matched
before and after, and all owned process groups exited.

Code does not promise a document-close event when a tab closes. The acceptance
control checked tab closure and client continuity separately, then used Code's
supported language-mode change on the unchanged source to exercise a genuine
stock-client LSP close. Rendered infoview appearance remains unverified because
the test host was locked. Other editor versions, platforms, Elan installations,
and compiler/SDK tuples require their own acceptance; the private launcher is
currently macOS only.

Primary sources used for this integration were the pinned
[extension manifest](https://github.com/leanprover/vscode-lean4/blob/dead846a035f42dc13beb7619ac779538e6ddf6e/vscode-lean4/package.json),
[server launch](https://github.com/leanprover/vscode-lean4/blob/dead846a035f42dc13beb7619ac779538e6ddf6e/vscode-lean4/src/leanclient.ts),
[command runner](https://github.com/leanprover/vscode-lean4/blob/dead846a035f42dc13beb7619ac779538e6ddf6e/vscode-lean4/src/utils/leanCmdRunner.ts),
[startup probes](https://github.com/leanprover/vscode-lean4/blob/dead846a035f42dc13beb7619ac779538e6ddf6e/vscode-lean4/src/diagnostics/setupDiagnoser.ts),
and [Elan changelog](https://github.com/leanprover/elan/blob/master/CHANGELOG.md).
The editor-host command contract also uses Microsoft's
[CLI documentation](https://code.visualstudio.com/docs/configure/command-line),
[argument parser](https://github.com/microsoft/vscode/blob/main/src/vs/platform/environment/node/argv.ts),
[shell environment resolver](https://github.com/microsoft/vscode/blob/main/src/vs/platform/shell/node/shellEnv.ts),
[extension installer CLI](https://github.com/microsoft/vscode/blob/main/src/vs/code/node/cliProcessMain.ts),
and [portable mode bootstrap](https://github.com/microsoft/vscode/blob/main/src/bootstrap-node.ts).
These Microsoft links and the Elan changelog are moving source. Acceptance used
the selected Code distribution's shipped API declarations and the installed
Lean VSIX; the extension files cited above match its release commit
`608100d335395e29d2cb7fbb1a6f947d6db9205e`.
