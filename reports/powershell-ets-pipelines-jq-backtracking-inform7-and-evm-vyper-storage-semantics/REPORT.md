# Object-Pipeline Shells, Backtracking Stream Engines, Specificity-Sorted Rulebooks, and Smart-Contract Storage Verification (PowerShell/Nushell, jq/awk/Vim/PostScript, Inform 7, and EVM/Vyper/Move)

## Summary

Four specialized runtime families—**object-pipeline shells** (PowerShell ETS vs. Nushell and YSH), **backtracking stream and stateful stack/buffer engines** (`jq`/`jaq`, POSIX `awk`, `sed`, Vimscript/`Vim9script`, PostScript/TrueType), **controlled-English rulebook compilers** (Inform 7 vs. `ink`), and **blockchain smart-contract VMs** (EVM/Solidity/Vyper/KEVM vs. Move)—expose sharp, non-obvious semantic mechanisms where source-level intuition diverges from runtime execution:

1. **PowerShell ETS pipeline unwrapping, LHS coercion, and array-filtering equality vs. Nushell/YSH:** PowerShell's `PipelineOps.PipelineResult` silently collapses `0`-element streams to `AutomationNull.Value`/`$null` and `1`-element streams to unwrapped scalar `T`, returning `object[]` only for $\ge 2$ items. Equality (`-eq`) is **non-commutative** (`"02" -eq 2` is `False` while `2 -eq "02"` is `True`) and **switches from boolean equality to collection filtering** when the LHS is enumerable (`$x -eq $null` returns matching `$null` elements rather than a boolean, interacting nonlinearly with `LanguagePrimitives.IsTrue(IList)` where `@($null)` is `false` but `@($null, $null)` is `true`). Nushell (`PipelineData`) and YSH reject 1-element unwrapping, LHS string/int coercion, and dynamic call-stack scoping.
2. **Backtracking generators, hidden provenance tags, live editor options, and partial VM snapshots:** `jq`'s bytecode VM (`FORK`/`BACKTRACK`) lifts binary operators into Cartesian generator streams, while its update lens `|=` (`def _modify`) uses `(| (., break $out))` to **silently drop all RHS outputs after the first** (`{"a":1} | .a |= (10,20)` yields only `{"a":10}`, whereas `.a = (10,20)` yields both) and treats `empty` as deferred simultaneous path deletion (`delpaths`). In POSIX `awk` (`onetrueawk`/`mawk`), external inputs carry a hidden `strnum` (`NUM|STR`) provenance bit so `$1 == $2` and `$1 == 1` evaluate `1` on `"01"` vs `"1"`, while `$1 == "1"`, `"01" == "1"`, `1 == "01"`, and `$1 "" == $2 ""` all evaluate `0`. Legacy Vimscript's `==` is hijacked by the live interactive `'ignorecase'` option (`"a" == "A"` -> `1`, `"abc" == 0` -> `1`), fixed in `vim9script` (`false` and `E1072`). PostScript's dynamic dictionary stack can be shadowed at runtime unless frozen by `bind`, and `save`/`restore` rolls back local-VM composite mutations while preserving operand/dictionary stacks (and raising `/invalidrestore` if any post-`save` composite remains on either stack).
3. **Inform 7 non-monotonic specificity sorting vs. `ink`:** Inform 7 sorts `MIDDLE_PLACEMENT` rules inside five placement strata (`VERY_FIRST`..`VERY_LAST`) via a multi-stage lexicographic specificity comparator (`ActionPatterns::compare_specificity` / `APClauses::compare_specificity` implementing Laws `III.1` through `III.6.1`). Narrowing a noun kind or adding a `when` clause silently reorders rule firing across compilation units without changing source order, in sharp contrast to `ink`'s deterministic weave/visit-count VM.
4. **EVM flat 256-bit storage aliasing, EIP-1153 transient persistence, and Vyper `v0.2.15`–`v0.3.0` `@nonreentrant` miscompilation vs. Move's bytecode verifier:** EVM maps contract state onto an untyped $2^{256} \times 256$-bit word array where `delegatecall` proxy layout drift silently aliases unrelated state variables (mitigated by `ERC-1967`/`ERC-7201`), Solidity must mask dirty high-order stack bits (`CompilerUtils::cleanHigherOrderBits`), and `EIP-1153` `TSTORE` persists across nested calls within a single transaction. Direct diffing of `vyperlang/vyper` `v0.3.0` vs. `v0.3.1` (`vyper/semantics/validation/data_positions.py`) shows the exact 2023 Curve Finance (`CVE-2023-39363`) compiler defect: `set_storage_slots` unconditionally incremented `storage_slot` per `@nonreentrant` function *and* overwrote `ret[variable_name]` so the emitted `storage_layout` JSON falsely reported a single lock slot. By contrast, Move's on-chain bytecode verifier enforces linear/affine resource abilities (`key`, `store`, `copy`, `drop`), borrow-graph alias exclusion, explicit `acquires` annotations, and type-keyed `(address, StructType)` global storage with no dynamic `delegatecall`.

## Applicability

This report documents verified source implementations, specifications, and live execution probes across the concrete revisions pinned in `REPORT.json`:

- **Shells:** `PowerShell/PowerShell` (`cd071c986fdb21710a629e12796ff539d06afa32`, .NET / PowerShell 7+ engine), contrasted with `nushell/nushell` (`16817a88f38bb62f86c05a128188904e2f1fed0d`) and `oils-for-unix/oils` (`d114978ca467143f171a835cbcbe8ab6ccc009a7`). Windows PowerShell 5.1 shares the core ETS/pipeline/LHS-coercion architecture, though specific .NET Framework adapters differ.
- **Stream / Text / Stack Engines:** `jqlang/jq` (`5c001b18d7237cce1fdba63608732163f978dd23`, plus live execution on `jq-1.8.2`), `01mf02/jaq` (`126f17a7f3137876aeaa73dd5246811068f767bd`), `onetrueawk/awk` (`72e9b56caddb4a6f8d1405315a5183c26b8650a4`, plus live execution on `mawk 1.3.4 20260302` under POSIX.1 rules), `GNU sed 4.9` (live execution), `vim/vim` (`d399646c1f54e30f5288208a911c193fefb6d79c`, plus live execution on `VIM 9.2`), `ArtifexSoftware/ghostpdl` (`5d84ee686543383cbeb7a09ed8a111e96ddcfe95`, plus live execution on `GPL Ghostscript 10.08.0`), and `freetype/freetype` (`d7339729da576614cbf107d04a72924d21f7ec5a`).
- **Interactive Fiction DSLs:** `ganelson/inform` (`5c7ba42b74db69b93b1290453c65189fa60cfc67`, Inform 10 / Inform 7 open-source compiler) contrasted with `inkle/ink` (`4011b8c0a01828c61dd2331613c1038a3a5f294b`).
- **Smart-Contract Compilers & VMs:** `ethereum/solidity` (`ce47f2c8e97779e7df8b844648d3c14f6e4af292`), `vyperlang/vyper` across four exact revisions—vulnerable `v0.2.15` (`6e7dba7a8b5f29762d3470da4f44634b819c808d`) and `v0.3.0` (`8a23febbb2d523f3701f9a7d0aaf361c104a2a37`), fixed `v0.3.1` (`0463ea4c304858d94494e2df229021448feaedeb`), and `HEAD` (`d3d07ad34192759ea4978cfd02250c0270161683`)—alongside `ethereum/EIPs` (`b055feec322fbc37e9d77a393a50b3ff56b31c92`, EIP-1153), `ethereum/ERCs` (`10eca3cea34986aeeac0af98ad061ab8928dc15d`, ERC-1967 & ERC-7201), `runtimeverification/evm-semantics` (`fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1`, KEVM), and `move-language/move` (`c453c90994cba0af30314fe4134acee57fb20d0c`, core Move 1.x bytecode verifier).

Live execution probes (`Basis: execution`) were run locally on `jq-1.8.2`, `mawk 1.3.4`, `GNU sed 4.9`, `VIM 9.2`, and `GPL Ghostscript 10.08.0`. PowerShell, Nushell, Inform 7, `solc`, `vyper`, and Move VM binaries were not installed on this host; claims for those systems are grounded in direct primary source code inspection (`Basis: source`), formal specifications (`Basis: normative`), and an executable Python reproduction of Vyper's `set_storage_slots` allocator (`Basis: derived`).

## Findings

### 1. Object-Pipeline Shells: PowerShell ETS, Scalar Unwrapping, Asymmetric LHS Coercion, and Dynamic Scoping vs. Nushell and YSH

#### 1.1 PowerShell Extended Type System (`PSObject`) and Pipeline 1-Element Scalar Unwrapping
Basis: source

In `PowerShell/PowerShell` (`cd071c986fdb21710a629e12796ff539d06afa32`), every value flowing through the runtime can be wrapped in `PSObject` (`src/System.Management.Automation/engine/MshObject.cs:47, 139`), which layers **adapted members** (`InternalAdapter.BaseGetMember<T>(msjObj.ImmediateBaseObject, name)` for .NET/XML/WMI/COM objects) and **extended type members** (synthetic `NoteProperty`, `ScriptProperty`, `CodeMethod`, and `TypeConverter` entries loaded dynamically from `types.ps1xml` / `Update-TypeData`) on top of the underlying CLR object.

When a command or scriptblock emits objects into a pipeline and the caller captures the result (`$x = Get-Items`), the PowerShell compiler (`src/System.Management.Automation/engine/parser/Compiler.cs:2175-2179`) collects streamed objects into a `List<object>` and invokes **`PipelineOps.PipelineResult`** (`src/System.Management.Automation/engine/runtime/Operations/MiscOps.cs:832-844`):

```csharp
internal static object PipelineResult(List<object> resultList)
{
    var resultCount = resultList.Count;
    if (resultCount == 0)
    {
        return AutomationNull.Value;
    }

    var result = resultCount == 1 ? resultList[0] : resultList.ToArray();
    resultList.Clear();
    return result;
}
```

Combined with pipeline enumeration (which unrolls any `IEnumerable` except `string`, `IDictionary`, and `XmlNode` into individual stream items as they exit a function or cmdlet), this produces a **cardinality-dependent type collapse** across every pipeline boundary:

| Emitted Element Count | Captured Value `$x` | Runtime Type of `$x` | Failure Mode When Caller Assumes Collection |
| :--- | :--- | :--- | :--- |
| `0` elements | `AutomationNull.Value` (coerced to `$null` in expressions/args, `MiscOps.cs:639-648`) | `null` | `$x.Count` is `0` in PS 3+ (via synthetic member), but indexing `$x[0]` throws `Cannot index into a null array` or returns `$null`; `$x.Add(...)` throws null-deref |
| `1` element (`x0`) | **`x0` (unwrapped scalar!)** | `typeof(x0)` (not `object[]`) | If `x0` is a `string`, `$x[0]` returns the **first character** instead of the first element; if `x0` is a `Hashtable` or custom object with a `Count` property, `$x.Count` reads the scalar's own property rather than `1`! |
| $\ge 2$ elements | `object[]` | `System.Object[]` | Behaves as expected array |

To preserve collection invariants across PowerShell function/pipeline returns, callers must either wrap the call site in the array subexpression operator `@(Get-Items)` (which guarantees `object[]` of length `0`, `1`, or `N`) or prepend the unary comma operator `return ,$list` inside the producer (which wraps `$list` in a 1-element outer array so the pipeline unrolls only the outer wrapper!).

#### 1.2 Asymmetric LHS Coercion, Enumerable Filtering, and `IsTrue(IList)` Depth-1 Cutoff
Basis: source

PowerShell comparison operators (`-eq`, `-ne`, `-lt`, `-le`, `-gt`, `-ge`; case-insensitive by default via `_ignoreCase = true` in `PSBinaryOperationBinder`, `Binders.cs:2126, 2276`, with explicit `-ceq`/`-ieq` variants) dispatch through `PSBinaryOperationBinder.CompareEQ` (`src/System.Management.Automation/engine/runtime/Binding/Binders.cs:3046-3107`) and `BinaryComparisonCommon` (`Binders.cs:3378-3412`):

1. **Asymmetric Left-Operand Type Coercion:** As documented on `LanguagePrimitives.Equals` (`LanguagePrimitives.cs:594-602`), PowerShell converts the **right-hand operand** to the type of the **left-hand operand**:
   - In `BinaryEqualityComparison` (`Binders.cs:3094-3107`): when `target.LimitType == typeof(string)` (`// Doing a string comparison no matter what`), `arg` is coerced via `PSToStringBinder.Get()`. Hence `"02" -eq 2` coerces `2 -> "2"` and compares `"02" == "2"` $\implies$ **`False`**.
   - In `BinaryComparisonCommon` (`Binders.cs:3393-3412`): when `target.LimitType.IsNumeric()`, `arg` (including `string`) is parsed into `target`'s numeric type. Hence `2 -eq "02"` coerces `"02" -> 2` and compares `2 == 2` $\implies$ **`True`**.
   - Equality is therefore **neither symmetric nor transitive**: `2 -eq "02"` (`True`) $\neq$ `"02" -eq 2` (`False`), and `"02" -eq "2"` (`False`) despite both equaling `2` when `2` is on the LHS!

2. **LHS Collection Filtering Mode (`$x -eq $null` Hazard):** In `CompareEQ` (`Binders.cs:3050-3066`) and `BinaryComparisonCommon` (`Binders.cs:3380-3391`):
   - If `target.Value == null` (`$null -eq $x`), `CompareEQ` immediately returns scalar `bool` (`arg.Value == null ? BoxedTrue : BoxedFalse`).
   - If `target` is enumerable (`PSEnumerableBinder.IsEnumerable(target) != null`, e.g., `$x = @($null, 1, $null)`), `BinaryComparisonCommon` calls `EnumerableOps.Compare`, switching `-eq` from boolean equality to a **collection filter returning an `object[]` of all elements equal to `arg`**!
   - When placed inside `if ($x -eq $null)`, the resulting filtered array is tested by **`LanguagePrimitives.IsTrue(IList)`** (`src/System.Management.Automation/engine/LanguagePrimitives.cs:1024-1051`):
     ```csharp
     switch (objectArray.Count) {
         case 0: return false;
         case 1:
             if (PSObject.Base(objectArray[0]) is not IList firstElement)
                 return IsTrue(objectArray[0]);
             if (firstElement.Count < 1) return false;
             return true; // deliberately stops recursion at depth 1!
         default: return true;
     }
     ```
     This creates an extraordinary non-monotonic truth table for `if ($x -eq $null)`:
     - `$x = @(1, 2)` $\implies$ filter returns `@()` (count 0) $\implies$ `IsTrue` = **`false`**;
     - `$x = @(1, $null)` $\implies$ filter returns `@($null)` (count 1) $\implies$ delegates to `IsTrue($null)` = **`false`** (falsely claiming `$x` had no `$null` / was not null!);
     - `$x = @($null, $null)` $\implies$ filter returns `@($null, $null)` (count 2) $\implies$ `default: return true` = **`true`** (falsely entering the null-check branch on a non-null 2-element array!).
     - Furthermore, `@(@())` has `firstElement.Count == 0` $\implies$ `false`, whereas `@(@($false))` has `firstElement.Count == 1` $\implies$ **`true`** because `IsTrue(IList)` explicitly caps recursion at depth 1 (`LanguagePrimitives.cs:1036-1047`).
     This exact source behavior is why PowerShell static analyzers (`PSScriptAnalyzer`) mandate putting `$null` on the **LHS** (`$null -eq $x`).

#### 1.3 Dynamic Call-Stack Scoping vs. Nushell and Oils (YSH)
Basis: source

PowerShell resolves unqualified variable reads by walking `SessionStateScope.Parent` (`src/System.Management.Automation/engine/SessionStateScope.cs:27-50, 293-324`) up the **dynamic call stack** (`Local -> Caller -> ... -> Script -> Global`), while unqualified variable writes (`$x = 1`) allocate a new binding in the *current* local scope unless qualified (`$script:x`, `$global:x`). Consequently, a helper function reading an uninitialized `$path` silently inherits whatever `$path` happens to exist in its dynamic caller's frame (unless `Set-StrictMode -Version Latest` is enabled, and even StrictMode does not block reading caller-frame variables!).

Contrast this directly with **Nushell** (`nushell/nushell`, commit `16817a88f38bb62f86c05a128188904e2f1fed0d`) and **Oils YSH** (`oils-for-unix/oils`, commit `d114978ca467143f171a835cbcbe8ab6ccc009a7`):
- **Nushell Pipeline Representation (`crates/nu-protocol/src/pipeline/pipeline_data.rs:50-55`):** `pub enum PipelineData { Empty, Value(Value, Option<PipelineMetadata>), ListStream(ListStream, Option<PipelineMetadata>), ByteStream(ByteStream, Option<PipelineMetadata>) }`. A 0-element or 1-element `Value::List` stays a `Value::List` across pipeline stages and variable bindings—never silently collapsing to scalar `T` or `Nothing`.
- **Nushell Symmetric Equality (`crates/nu-protocol/src/value/mod.rs:2525-2785, 2904-2915, 3991-4005`):** `Value::eq` evaluates `matches!(self.partial_cmp(rhs), Some(Ordering::Equal))` over a strict cross-type ordering (`Bool < Int/Float < String/Glob < Filesize < Duration < Date < Range < Record < List < Closure < Error < Binary < CellPath < Custom < Nothing`). Distinct types (`Value::String("02")` vs `Value::Int(2)`) return `Ordering::Greater` / `Ordering::Less`, so `"02" == 2` and `2 == "02"` are **both `false`** (symmetric, no string-to-int LHS coercion, and lists compare structurally rather than switching to element filtering).
- **Oils YSH (`ysh/expr_eval.py:582-634`):** Separates command mode from Python-like expression mode (`var x = ...`), enforces strict typed arithmetic (`_ConvertToInt` rejects non-integers and negative modulo divisors, lines `620-633`), and provides lexical scoping with explicit typed equality (`===`).

---

### 2. Backtracking Stream Engines and Stateful Text/Stack VMs (`jq`/`jaq`, `awk`, `sed`, `Vim`, `PostScript`, `FreeType`)

#### 2.1 `jq` Backtracking Generator VM and Update Lenses vs. `jaq`
Basis: source + execution

`jq` (`jqlang/jq`, commit `5c001b18d7237cce1fdba63608732163f978dd23`) is not a deterministic single-value JSON expression language; it is a **nondeterministic backtracking stream machine** compiled to stack-plus-choice-point bytecode (`src/execute.c`):
- **Choice Points & Backtracking (`src/execute.c:803, 871`):** The comma operator `e1, e2` compiles to a `FORK` instruction (`execute.c:871`) that pushes a saved continuation frame onto the fork stack (`jq_state->forktop`), executes `e1`, and upon exhaustion or `empty` invokes `BACKTRACK` (`execute.c:803`) to resume `e2` with the saved input. Binary operators lift over generator streams via Cartesian product:
  - Live `jq-1.8.2`: `jq -cn '[(1,2) + (10,20)]'` $\implies$ **`[11,12,21,22]`**.
  - Live `jq-1.8.2`: `jq -cn '[(1, empty, 2) + 10]'` $\implies$ **`[11,12]`** (`empty` prunes the branch cleanly).
- **Path Expressions (`PATH_BEGIN` / `PATH_END`, `src/execute.c:625, 641`):** `path(expr)` executes `expr` in path-tracking mode, recording every index/key traversal step. Any expression that synthesizes a fresh value rather than projecting a sub-value from the input fails at runtime:
  - Live `jq-1.8.2`: `jq -cn '{"a":1} | path(.a + 1)'` $\implies$ `jq: error (at <unknown>): Invalid path expression with result 2`.
- **The `|=` vs. `=` Multi-Output Asymmetry (`src/builtin.jq:14-31`):** Direct inspection of `jq`'s standard library reveals a major semantic trap between plain assignment (`=`) and update assignment (`|=`):
  ```jq
  def _assign(paths; $value): reduce path(paths) as $p (.; setpath($p; $value));
  def _modify(paths; update):
      reduce path(paths) as $p ([., []];
          . as $dot | null | label $out | ($dot[0] | getpath($p)) as $v
        | (
            ( $$$$v | update | (., break $out) as $v | $$$$dot | setpath([0] + $p; $v) ),
            ( $$$$dot | setpath([1, (.[1] | length)]; $p) )
          )
      ) | . as $dot | $dot[0] | delpaths($dot[1]);
  ```
  - **First-output truncation in `|=`:** When `update` produces multiple outputs (`10, 20`), `(., break $out)` emits the first value (`10`), performs `setpath`, and **immediately breaks out of `$out` on backtrack**—silently discarding `20`! Thus on `jq-1.8.2`:
    - `jq -cn '{"a":1} | .a |= (10, 20)'` $\implies$ **`{"a":10}`** (1 output; `20` silently dropped!).
    - `jq -cn '{"a":1} | .a = (10, 20)'` $\implies$ **`{"a":10}`** AND **`{"a":20}`** (2 outputs, because `$value` binds via generator iteration *outside* `reduce`!).
  - **Simultaneous index-shift-safe deletion via `empty`:** When `update` yields `empty` (0 outputs), `(., break $out)` never runs, so backtracking enters the second `,` branch and records `$p` in the deferred deletion list `$dot[1]`. Executing `delpaths($dot[1])` at the end deletes all paths simultaneously without index shifting:
    - Live `jq-1.8.2`: `jq -cn '{"a":1,"b":2} | .a |= empty'` $\implies$ **`{"b":2}`**;
    - Live `jq-1.8.2`: `jq -cn '[10,20,30,40] | (.[0], .[2]) |= empty'` $\implies$ **`[20,40]`**.
- **Contrast with `jaq` (`01mf02/jaq`, commit `126f17a7f3137876aeaa73dd5246811068f767bd`):** Instead of implementing `|=` by materializing all `path(paths)` and running `setpath`/`delpaths` in bytecode, `jaq` defines `Filter::paths` (`jaq-core/src/filter.rs:578-630`) and structural in-place lens updates (`Ast::Update(path, f)` $\to$ `Path::update` / `Part::update`, `jaq-core/src/filter.rs:514-526`, `jaq-core/src/path.rs:86-156`) directly over Rust iterator combinators (`map_index`, `map_values`, `map_range`), eliminating `jq`'s bytecode path-stack allocation overhead and avoiding path-materialization quadratic costs on deep trees.

#### 2.2 POSIX `awk` Hidden `strnum` Input Provenance
Basis: normative + source + execution

POSIX `awk` (IEEE Std 1003.1) attaches a hidden **"numeric string" (`strnum`)** provenance attribute to strings that look syntactically like numbers *if and only if* they originate from external untyped input—specifically field variables (`$0`..`$NF`), `getline`, `split()`, `ARGV`, `ENVIRON`, `FILENAME`, command-line `-v` assignments, or variables copied directly from another `strnum`. String literals written in source code (`"01"`) and string concatenation results (`$1 ""`) are **plain strings**, never `strnum`.

Inspecting Brian Kernighan's `onetrueawk/awk` (`72e9b56caddb4a6f8d1405315a5183c26b8650a4`) confirms the exact runtime mechanism:
- `awk.h:101-141`: Each `Cell` carries bitmask flags `tval` combining `NUM (01)` and `STR (02)` (plus `CON`, `FLD`, `REC`). A `strnum` cell carries **both** `NUM | STR`, whereas a literal string `"01"` carries only `STR | CON`!
- `run.c:890-910` (`relop`):
  ```c
  if (x->tval&NUM && y->tval&NUM) {
      if ((x_is_nan || y_is_nan) && n != NE)
          return(False);
      j = x->fval - y->fval;
      i = j<0? -1: (j>0? 1: 0);
  } else {
      i = strcmp(getsval(x), getsval(y));
  }
  ```
  Relational comparison is numeric **iff both operands have the `NUM` bit set** (pure numbers or `strnum`s); if *either* operand is a plain string (`STR` without `NUM`), `relop` falls back to `strcmp`!

Live execution on `mawk 1.3.4 20260302` (`Basis: execution`) reproduces every corner of this provenance lattice:

| Expression (with input record `"01 1"` $\implies$ `$1="01"`, `$2="1"`, `split("01 1", a, " ")`) | LHS Type Tag | RHS Type Tag | Comparison Mode | Observed Output (`mawk 1.3.4`) |
| :--- | :--- | :--- | :--- | :--- |
| `"01" == "1"` | `STR` (literal) | `STR` (literal) | String (`strcmp`) | **`0`** |
| `1 == "01"` / `01 == "01"` | `NUM` | `STR` (literal) | String (`"1"` vs `"01"`) | **`0`** |
| `$1 == $2` / `a[1] == a[2]` | `NUM\|STR` (`strnum`) | `NUM\|STR` (`strnum`) | **Numeric (`1 == 1`)** | **`1`** |
| `$1 == 1` / `a[1] == 1` | `NUM\|STR` (`strnum`) | `NUM` | **Numeric (`1 == 1`)** | **`1`** |
| `$1 == "1"` / `a[1] == "1"` | `NUM\|STR` (`strnum`) | `STR` (literal) | **String (`"01"` vs `"1"`)** | **`0`** |
| `$1 "" == $2 ""` | `STR` (provenance stripped!) | `STR` (provenance stripped!) | String (`"01"` vs `"1"`) | **`0`** |

**Security & Correctness Hazard:** Two variables holding the exact same byte sequence `"01"` behave differently depending on **where the bytes came from** (input stream vs. script literal or concatenation). Comparing ZIP codes, padded account IDs (`"00123"` vs `"123"`), or hex strings (`"1e5"` vs `"100000"`) read from CSV fields without appending `""` silently collides distinct identifiers!

#### 2.3 GNU `sed` Two-Buffer Automaton and Branch-Flag State
Basis: execution

POSIX/GNU `sed` executes a cyclic finite-state machine over two line buffers—**pattern space** (reset and overwritten with the next input line at the top of each cycle unless bypassed by `D`) and **hold space** (persistent across cycles, initialized to empty; swapped/copied via `h`/`H`/`g`/`G`/`x`)—plus a hidden boolean **substitution-success latch** tested and **cleared** by conditional branches `t`/`T` (and cleared at each new input line). Live execution on `GNU sed 4.9` confirms both stateful hold-space accumulation (`printf 'a\nb\nc\n' | sed -n '1h; 1!H; ${g; s/\n/-/g; p;}'` $\implies$ `a-b-c`) and per-line `t` latch dispatch (`printf 'foo\nbar\n' | sed -n 's/foo/FOO/; t hit; s/^/MISS:/; b done; :hit; s/^/HIT:/; :done; p'` $\implies$ `HIT:FOO` / `MISS:bar`). Because `D` deletes only through the first embedded newline in pattern space and restarts the script *without* reading a new line, `N`/`P`/`D` loops can diverge into infinite cycles if pattern space fails to shrink.

#### 2.4 Legacy Vimscript Option-Coupled Equality vs. `Vim9script`
Basis: source + execution

In `vim/vim` (`d399646c1f54e30f5288208a911c193fefb6d79c`, `src/typval.c:1498-1555`, `typval_compare2`), legacy Vimscript's bare `==` operator passes the user's live interactive search option `'ignorecase'` (`p_ic`) as the `ic` parameter—meaning a plugin's business logic silently changes behavior depending on whether the end user ran `:set ignorecase`! Furthermore, legacy Vimscript implicitly coerces strings to numbers in mixed comparisons (`str2nr`, treating non-numeric prefixes as `0`).

Live execution on `VIM 9.2 (2026 Feb 14)` (`Basis: execution`) demonstrates the exact legacy vs. `vim9script` contrast under `:set ignorecase`:
- **Legacy Vimscript:**
  - `"a" == "A"` $\implies$ **`1`** (hijacked by `'ignorecase'`; deterministic scripts must write `==#` or `==?`)
  - `"a" ==# "A"` $\implies$ **`0`**
  - `"abc" == 0` $\implies$ **`1`** (`"abc"` silently coerced to `0`!)
  - `"12abc" + 0` $\implies$ **`12`** (trailing garbage silently truncated!)
- **`vim9script` (under the exact same `:set ignorecase`):**
  - `'a' == 'A'` $\implies$ **`false`** (bare `==` is unconditionally case-sensitive; explicit `==?` yields `true`)
  - `"abc" == 0` $\implies$ **`Vim(var):E1072: Cannot compare string with number`** (runtime/compile-time type error replacing silent coercion).

#### 2.5 PostScript Dynamic Dictionary Stacks, `bind`, and `save`/`restore` (plus TrueType Hinting VM)
Basis: source + execution

PostScript (`ArtifexSoftware/ghostpdl`, commit `5d84ee686543383cbeb7a09ed8a111e96ddcfe95`) operates on four interacting stacks (operand, execution, graphics state, and **dynamic dictionary stack** `d_stack`, manipulated by `zbegin`/`zend` in `psi/zdict.c:57-91`) plus a split **local vs. global VM heap** (`psi/zvmem.c:59-254`). Executable arrays `{ ... }` look up operator names dynamically along the dictionary stack at call time, whereas `bind` eagerly replaces operator names with direct operator objects resolved against the *current* dictionary stack:

- **Live `GPL Ghostscript 10.08.0` Probe 1 (Dynamic Shadowing vs. `bind`):**
  Defining `/f_unbound { 10 20 add } def` and `/f_bound { 10 20 add } bind def`, then shadowing `/add { sub } def` inside `1 dict begin ... end`:
  - `f_unbound` evaluates to **`-10`** (dynamically intercepted by shadowed `/add`!), while
  - `f_bound` evaluates to **`30`** (`bind` froze `systemdict /add` eagerly at definition time).
- **Live `GPL Ghostscript 10.08.0` Probe 2 (`save`/`restore` Split-State Semantics & `/invalidrestore`):**
  - `snap restore` rolls back **local-VM composite objects** (`arr 0 99 put` reverts `arr[0]` from `99` back to `1`; `pre_dict /tag (mutated_after_save) put` reverts `tag` back to `(pre_save_dict)`), while **neither rolling back the operand stack** (`999` pushed after `save` remains on top!) **nor rolling back the dictionary stack** (`pre_dict` pushed after `save` remains active on `d_stack`!).
  - However, if *any* composite object allocated **after** `save` (such as a fresh `1 dict begin`) remains reachable on the operand stack or dictionary stack at `restore` time, `restore_check_save` (`psi/zvmem.c:251`) aborts with **`/invalidrestore`** (observed live: `caught_error=/invalidrestore`). Global VM objects (`true setglobal`) are exempt from `restore` altogether.
- **Comparison with TrueType Bytecode Hinting VM (`freetype/freetype`, commit `d7339729da576614cbf107d04a72924d21f7ec5a`):** Like PostScript, TrueType font hinting (`src/truetype/ttinterp.c:106-111, 294-300, 2843-2848`) runs a Turing-complete stack-based VM carrying mutable persistent state—the `TT_GraphicsState` (projection/freedom vectors, round state, loop counter), the Control Value Table (`CVT`, writable via `Ins_WCVTP`), Storage Area, and a scratch `twilight` outline zone (`exec->twilight = size->twilight`)—mutated by font-wide `fpgm` and size-specific `prep` programs before every glyph program executes, making font rendering an untrusted stateful bytecode execution surface historically prone to memory-safety and state-confusion vulnerabilities.

---

### 3. Natural-Language Rulebook Calculi: Inform 7 Non-Monotonic Specificity Laws vs. `ink`

#### 3.1 Inform 7 Compiler Architecture and Five-Strata Booking Lists
Basis: source

Graham Nelson's **Inform 7** (`ganelson/inform`, commit `5c7ba42b74db69b93b1290453c65189fa60cfc67`) compiles controlled-English source text through a natural-language syntax tree into the `Inter` intermediate representation, targeting Inform 6 / Glulx (32-bit VM), Z-machine, or C. Rather than dispatching actions via explicit `if`/`else` chains or object-oriented virtual tables, Inform 7 decomposes every world-model action into six sequential **rulebooks**: `Before` $\to$ `Instead` $\to$ `Check` $\to$ `Carry out` $\to$ `After` $\to$ `Report` (with `Instead` terminating the action with failure by default unless `continue the action` is invoked).

Inspecting `inform7/assertions-module/Chapter 6/Booking Lists.w:83-300` and `Rule Bookings.w:118-264` reveals the exact deterministic insertion algorithm (`BookingLists::add`):
1. Every rulebook maintains a linked list partitioned into **five placement strata**: `VERY_FIRST_PLACEMENT` $\prec$ `FIRST_PLACEMENT` $\prec$ `MIDDLE_PLACEMENT` $\prec$ `LAST_PLACEMENT` $\prec$ `VERY_LAST_PLACEMENT` (`Rule Bookings.w:176-264`). Multiple `FIRST` rules stack in **reverse** order of declaration (`Rule Bookings.w:243`), whereas multiple `LAST` rules appear in declaration order (`Rule Bookings.w:258`).
2. Explicit relative directives (`listed before R` / `listed after R`, `BEFORE_SIDE` / `AFTER_SIDE`) narrow the valid insertion interval `[start_rule, end_rule)` (`Booking Lists.w:238-252`).
3. Inside that valid interval, `MIDDLE_PLACEMENT` rules are insertion-sorted in **decreasing specificity order** (`Booking Lists.w:273-279`):
   ```c
   while ((insert_after->next_booking != end_rule)
       && (insert_after->next_booking->placement != LAST_PLACEMENT)
       && (insert_after->next_booking->placement != VERY_LAST_PLACEMENT)
       && (RuleBookings::cmp(insert_after->next_booking, new_br, log) >= 0))
       insert_after = insert_after->next_booking;
   ```
   Because the loop advances while `cmp >= 0`, equally specific rules preserve insertion/declaration order within the valid interval (unless overridden by extension-vs-main-source precedence).

#### 3.2 Exact Lexicographic Specificity Laws in Primary Source (`Laws III.1`–`III.6.1`)
Basis: source

`RuleBookings::cmp` delegates to `Specifications::compare_specificity` (`inform7/values-module/Chapter 2/Specifications.w:211-215`) and for action rules to **`ActionPatterns::compare_specificity`** (`inform7/if-module/Chapter 4/Action Patterns.w:184-215`) and **`APClauses::compare_specificity`** (`inform7/if-module/Chapter 4/Action Pattern Clauses.w:281-405`). The exact lexicographic precedence hierarchy hardcoded in the compiler is:

| Priority | Compiler Law Identifier (verbatim string in `ganelson/inform`) | Comparator Source Location | Semantic Criterion (Higher Wins / Runs Earlier) |
| :--- | :--- | :--- | :--- |
| 1 | **`III.1 - Object To Which Rule Applies`** | `Action Pattern Clauses.w:389-390` | Parametric noun/second-noun specificity (specific object $\succ$ sub-kind e.g. `open container` $\succ$ `container` $\succ$ `thing`) |
| 2 | *Plugin Action Clause Hooks* (e.g., Going direction/room) | `Action Pattern Clauses.w:393-394` | Action-specific spatial/directional constraints (`Going.w`) |
| 3 | **`III.2.2 - Action/Where/Room Where Action Takes Place`** | `Action Pattern Clauses.w:397-398` | `in <room/region>` constraint (specific room $\succ$ region $\succ$ unconstrained) |
| 4 | **`III.2.3 - Action/Where/In The Presence Of`** | `Action Pattern Clauses.w:401-403` | `in the presence of <person/thing>` constraint |
| 5 | *Action Variable Clauses* | `Action Pattern Clauses.w:281-305, 405` | Count of matched shared action-variable clauses, then per-variable `Specifications::compare_specificity` |
| 6 | **`III.4.1 - Action/How/What Happens`** | `Action Patterns.w:195-198` | Narrower action name list (`taking` $\succ$ `taking or dropping` $\succ$ `doing anything`) |
| 7 | **`III.5.1 - Action/When/Duration`** | `Action Patterns.w:200-203` | Temporal/scene/repetition occurrence constraints (`during <scene>`, `for the third time`) |
| 8 | **`III.5.2 - Action/When/Circumstances`** | `Action Patterns.w:205-209` | Presence and specificity of a `when <condition>` clause |
| 9 | **`III.6.1 - Action/Name/Is This Named`** | `Action Patterns.w:211-215` | Named kind-of-action pattern (`is_named(ap1)`) $\succ$ anonymous action pattern |

**Non-Monotonicity & Verification Hazard:** Rule execution order is a **global emergent property** of syntactic preamble descriptions across the main story and all imported extensions. Adding a seemingly local guard (`when the lamp is lit`, Law `III.5.2`), narrowing a parameter from `a thing` to `a container` (Law `III.1`), or adding an `in the Laboratory` clause (Law `III.2.2`) silently hoists a rule above previously higher-priority rules declared hundreds of lines away—and if an `Instead` rule gets hoisted above a `Carry out` or another `Instead` rule, it silently preempts and aborts the remainder of the action! Conversely, `Booking Lists.w:289-299` silently upgrades a `MIDDLE_PLACEMENT` rule inserted `after` a `LAST` rule into `LAST_PLACEMENT` (and `before` a `FIRST` rule into `FIRST_PLACEMENT`) to preserve stratification invariants.

#### 3.3 Contrast with `inkle/ink`
Basis: source

By contrast, `inkle/ink` (`4011b8c0a01828c61dd2331613c1038a3a5f294b`, `ink-engine-runtime/Story.cs`) compiles narrative scripts into a deterministic JSON bytecode graph of hierarchical **knots, stitches, weaves, tunnels, and threads** with explicit `CallStack` frames and per-container visit counts (`state.VisitCountForContainer`), distinguishing once-only (`*`) from sticky (`+`) choices. Execution order follows source-text control flow and explicit diverts (`-> target`) strictly—there is no non-monotonic specificity re-sorting across compilation units.

---

### 4. Smart-Contract Storage-Slot & Linear-Resource VMs (EVM/Solidity/Vyper/KEVM vs. Move)

#### 4.1 Flat $2^{256}$ EVM Storage Aliasing, Proxy Collisions, and Solidity Dirty High Bits
Basis: normative + source

The Ethereum Virtual Machine (formalized in `runtimeverification/evm-semantics` `KEVM`, commit `fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1`, `kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md`) provides each account with an untyped flat map $\text{Storage} : \mathbb{Z}_{2^{256}} \to \mathbb{Z}_{2^{256}}$ accessed via 256-bit word operations `SLOAD` and `SSTORE`:
- **Static & Hash-Derived Slot Layouts:** Solidity and Vyper lay out sequential state variables from slot `0`, `1`, `2`, ... (Solidity packs adjacent sub-32-byte fields into single 256-bit words; Vyper traditionally aligns variables to 32-byte words), and locate dynamic arrays at `keccak256(p) + idx` and mappings at `keccak256(h(k) || p)`.
- **`delegatecall` Proxy Storage Aliasing:** `DELEGATECALL` executes a target implementation contract's bytecode while binding `SLOAD`/`SSTORE` to the **caller proxy's** `<storage>` cell. Because the EVM has no runtime type tags or field names on storage slots, any disagreement between the proxy's slot `0` (e.g., `address implementation`) and the implementation's slot `0` (e.g., `uint256 totalSupply`)—or inserting a new variable in the middle of an inherited contract during an upgrade—causes silent memory corruption (e.g., overwriting `implementation` or `owner`).
  - **Standard Mitigations (`ethereum/ERCs`, commit `10eca3cea34986aeeac0af98ad061ab8928dc15d`):**
    - **`ERC-1967`** (`ERCS/erc-1967.md`) relocates proxy administrative slots to preimage-less hash offsets such as `bytes32(uint256(keccak256('eip1967.proxy.implementation')) - 1) = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc` (the `- 1` ensures no Solidity dynamic array or mapping slot has a known preimage colliding with it).
    - **`ERC-7201`** (`ERCS/erc-7201.md`) generalizes this to diamond/modular contracts via `erc7201(id) = keccak256(abi.encode(uint256(keccak256(bytes(id))) - 1)) & ~bytes32(uint256(0xff))` (clearing the lowest byte to align a 256-slot namespace without overlap).
- **Solidity Dirty High-Order Stack Bits (`ethereum/solidity`, commit `ce47f2c8e97779e7df8b844648d3c14f6e4af292`):** Because the EVM stack is strictly 256 bits wide while Solidity supports sub-256-bit types (`bool`, `uint8`, `int16`, `address` = 160 bits, `enum`), arithmetic, inline assembly, or packed storage reads can leave non-zero "dirty" bits in the upper $256 - w$ bits of a stack word. Inspecting `libsolidity/codegen/CompilerUtils.cpp:758-897` confirms that `CompilerUtils::convertType` explicitly calls `cleanHigherOrderBits(*typeOnStack)` before widening conversions, comparisons, hashing, or ABI encoding—and notes at line `768`: `// @todo: store in the AST whether the operand might have "dirty" higher order bits`. Any Yul/assembly block or compiler optimizer bug that bypasses `cleanHigherOrderBits` allows a single logical `uint8`/`bool` value to carry distinct 256-bit representations, corrupting `keccak256` mapping keys (`mapping(uint8 => ...)`), comparisons, or ABI outputs.

#### 4.2 `EIP-1153` Transient Storage (`TLOAD` / `TSTORE`): Intra-Transaction Persistence and Composability Hazards
Basis: normative + source

`EIP-1153` (`ethereum/EIPs`, commit `b055feec322fbc37e9d77a393a50b3ff56b31c92`, `EIPS/eip-1153.md`, activated in the Cancun hard fork) introduces two 100-gas opcodes—`TLOAD` (`0x5c`) and `TSTORE` (`0x5d`)—formalized in `KEVM` (`evm.md:468, 1644-1663`):
```k
rule #changesState(TSTORE, _) => true
rule [tload]:  <k> TLOAD INDEX => #lookup(TSTORAGE, INDEX) ~> #push ... </k>
               <id> ACCT </id> <account> <acctID> ACCT </acctID> <transientStorage> TSTORAGE </transientStorage> ... </account>
rule [tstore]: <k> TSTORE INDEX NEW => .K ... </k>
               <id> ACCT </id> <account> <acctID> ACCT </acctID> <transientStorage> TSTORAGE => TSTORAGE [ INDEX <- NEW ] </transientStorage> ... </account>
```
Key operational and security properties verified directly from `eip-1153.md` and `evm.md`:
1. **Transaction-Scoped Lifetime with Frame-Scoped Reverts:** Transient storage is zero-initialized at transaction start and discarded at transaction end (zero disk I/O), is rejected inside `STATICCALL` (`#changesState(TSTORE, _) => true`), and rolls back on inner call-frame `REVERT` via a checkpointed undo journal (`eip-1153.md:165-205`).
2. **Intra-Transaction Composability Leak:** Unlike call-frame memory (`MLOAD`/`MSTORE`), `TSTORE` **persists across sequential external calls and nested `CALL`/`DELEGATECALL` frames within the same transaction**! If a contract writes a transient approval, flash-loan callback authorization, or reentrancy guard via `TSTORE` and relies on "automatic end-of-transaction cleanup" instead of explicitly clearing the slot before returning, a **multicall / batch-router / ERC-4337 bundler** executing two sequential calls against the same contract in one transaction can reuse the leftover transient state from call 1 to hijack call 2.
3. **Linear Memory Allocation Bound (`eip-1153.md:225-245`):** Because `TSTORE` costs a flat 100 gas per 32-byte word (rather than `MSTORE`'s quadratic expansion $3w + w^2/512$), a 30M-gas block allows allocating up to $\sim 9.15\text{ MB}$ in a single call frame via `TSTORE` (vs. $\sim 3.75\text{ MB}$ for single-frame `MSTORE`, though multi-frame `MSTORE` reaches $\sim 20\text{ MB}$).

#### 4.3 The Vyper `v0.2.15`–`v0.3.0` `@nonreentrant` Storage-Slot Miscompilation (`CVE-2023-39363`)
Basis: source + derived

On July 30, 2023, cross-function reentrancy exploits drained over $50M across multiple Curve Finance ETH liquidity pools (pETH/ETH, msETH/ETH, alETH/ETH) and JPEG'd—even though the pool source code correctly annotated `add_liquidity`, `remove_liquidity`, and `exchange` with the **same** `@nonreentrant("lock")` decorator.

Direct line-by-line inspection across four pinned revisions of `vyperlang/vyper` establishes the exact root cause and its secondary **audit-masking bug**:

1. **Vulnerable `v0.2.15` (`6e7dba7a8b5f29762d3470da4f44634b819c808d`, `vyper/semantics/validation/data_positions.py:30-35`):**
   ```python
   for node in vyper_module.get_children(vy_ast.FunctionDef):
       type_ = node._metadata["type"]
       if type_.nonreentrant is not None:
           type_.set_reentrancy_key_position(StorageSlot(storage_slot))
           storage_slot += 1
   ```
   Every decorated function received a **fresh, distinct `StorageSlot`** (`add_liquidity` $\to$ slot `0`, `remove_liquidity` $\to$ slot `1`, `exchange` $\to$ slot `2`) completely ignoring the shared key string `"lock"`! Single-function self-reentrancy tests still passed (a function re-entering *itself* checked its own slot), while cross-function reentrancy (`remove_liquidity` sending ETH $\to$ attacker fallback calling `add_liquidity` while pool balances were mid-update) saw slot `0 == 0` and bypassed the mutex entirely!

2. **Vulnerable `v0.3.0` (`8a23febbb2d523f3701f9a7d0aaf361c104a2a37`, `vyper/semantics/validation/data_positions.py:31-48`) — Silent Metadata Masking:**
   ```python
   for node in vyper_module.get_children(vy_ast.FunctionDef):
       type_ = node._metadata["type"]
       if type_.nonreentrant is not None:
           type_.set_reentrancy_key_position(StorageSlot(storage_slot))
           variable_name = f"nonreentrant.{type_.nonreentrant}"
           ret[variable_name] = {
               "type": "nonreentrant lock",
               "location": "storage",
               "slot": storage_slot,
           }
           storage_slot += 1
   ```
   `v0.3.0` added storage-layout export (`ret`), **still allocated a distinct slot per function**, and **silently overwrote `ret["nonreentrant.lock"]`** on each iteration—so the emitted `storage_layout` JSON reported only one entry (`{"nonreentrant.lock": {"slot": 2}}`), hiding the three-slot divergence from automated layout audits!

3. **Fixed `v0.3.1` (`0463ea4c304858d94494e2df229021448feaedeb`, `vyper/semantics/validation/data_positions.py:45-48`):**
   ```python
   if variable_name in ret:
       _slot = ret[variable_name]["slot"]
       type_.set_reentrancy_key_position(StorageSlot(_slot))
       continue
   ```
   All functions sharing `nonreentrant.lock` now bind to `_slot = 0`.

4. **Modern `HEAD` (`d3d07ad34192759ea4978cfd02250c0270161683`, `vyper/semantics/analysis/data_positions.py:49-114`):**
   Vyper refactored the allocator to make both bugs structurally impossible: (a) `InsertableOnceDict` (`lines 49-53`) raises `ValueError` on duplicate key overwrite; (b) per-key named locks were unified into a single `GLOBAL_NONREENTRANT_KEY = "$.nonreentrant_key"` allocated once at `_starting_slot`; and (c) `get_reentrancy_key_location()` routes the lock to `DataLocation.TRANSIENT` (`EIP-1153` `TLOAD`/`TSTORE`) on Cancun+ targets or `DataLocation.STORAGE` on earlier targets.

#### 4.4 Structural Contrast: Move's On-Chain Linear Resource Bytecode Verifier
Basis: source

Rather than trusting an unverified high-level compiler to uphold storage isolation and reentrancy locks on top of an untyped word array, the **Move VM** (`move-language/move`, commit `c453c90994cba0af30314fe4134acee57fb20d0c`) enforces linear/affine asset safety and aliasing invariants **on-chain at module-publish time** directly on bytecode via its multi-pass bytecode verifier (`language/move-bytecode-verifier/src/`):

1. **Ability Algebra (`ability_field_requirements.rs:20-52`):** Every struct declares a subset of four abilities: `copy` (duplicable), `drop` (implicitly discardable), `store` (embeddable inside global storage), and `key` (top-level global storage resource). `verify_module_impl` verifies that every struct field's abilities are a superset of `sh.abilities.requires()` (otherwise rejecting the module with `StatusCode::FIELD_MISSING_TYPE_ABILITY`). A token `struct Coin has store { value: u64 }` lacking `copy` and `drop` **cannot be forged or silently dropped by any bytecode sequence**.
2. **Linear Locals Safety (`locals_safety/mod.rs:82-86`):** Abstract interpretation over control-flow paths rejects any `Ret` instruction if a local variable holding a value without `drop` remains live/available (`StatusCode::UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`).
3. **Borrow-Graph Reference Safety (`reference_safety/abstract_state.rs:308-335`):** Tracks a Rust-like borrow graph over stack/local references and rejects aliasing or use-after-move bytecode (`StatusCode::COPYLOC_EXISTS_BORROW_ERROR`, `StatusCode::MOVELOC_EXISTS_BORROW_ERROR`).
4. **Type-Keyed Global Storage & Static Acquires (`acquires_list_verifier.rs:5-12, 91-104, 183-188`):** Global storage is indexed by the pair **`(address, StructType)`**—never raw 256-bit integers—making `delegatecall` proxy storage-slot collisions and Vyper-style lock-slot misallocation **unexpressible** in the VM. Every function accessing `MoveFrom`, `ImmBorrowGlobal`, or `MutBorrowGlobal` (directly or transitively through `Call`/`CallGeneric`) must declare the exact acquired struct types in `acquires_global_resources` (`StatusCode::MISSING_ACQUIRES_ANNOTATION`), and core Move 1.x forbids dynamic dispatch / function pointers across untrusted modules—eliminating classic EVM dynamic-callback reentrancy by construction.

---

### 5. Cross-System Synthesis: Semantic Traps and Verification Boundaries

Basis: derived

| System / Family | Hidden Semantic Mechanism | Concrete Counterexample / Failure Mode | Root Architectural Cause | Contrastive Safe Design |
| :--- | :--- | :--- | :--- | :--- |
| **PowerShell ETS** | `PipelineOps.PipelineResult` cardinality collapse + LHS coercion + enumerable `-eq` filter | `$x = @($null, $null); if ($x -eq $null)` is **`true`**; `$x = @(1, $null); if ($x -eq $null)` is **`false`**; `"02" -eq 2` (`False`) $\neq$ `2 -eq "02"` (`True`) | Overloading scalar/stream return values, equality/filtering, and dynamic call-stack scopes | **Nushell** (`PipelineData`, symmetric `Value::eq`, lexical `Stack`) & **YSH** (`===`, typed expr mode) |
| **`jq`** | `FORK`/`BACKTRACK` generator streams + `_modify` `(., break $out)` truncation | `{"a":1} \| .a \|= (10,20)` $\implies$ `{"a":10}` (drops `20`), whereas `.a = (10,20)` yields both | `break $out` conflates "skip `empty` deletion branch" with "truncate RHS stream to first element" | **`jaq`** explicit Rust iterator lens algebra (`Path::update` / `Part::update`) |
| **POSIX `awk`** | Hidden `NUM\|STR` (`strnum`) input-provenance bit | On input `"01 1"`: `$1 == $2` (`1`) and `$1 == 1` (`1`), yet `$1 == "1"` (`0`) and `$1 "" == $2 ""` (`0`) | Untyped text fields infer numeric type dynamically while source string literals stay `STR`-only | Explicit coercion (`x ""` for string, `x + 0` for numeric) or typed schemas |
| **Legacy Vimscript** | Live `'ignorecase'` option injected into `==` + silent `str2nr` coercion | Under `:set ignorecase`: `"a" == "A"` $\implies$ `1`, `"abc" == 0` $\implies$ `1`, `"12abc" + 0` $\implies$ `12` | Interactive editor configuration leaks into script expression semantics | **`Vim9script`** (`==` ignores `'ignorecase'`; `"abc" == 0` raises `E1072`) |
| **PostScript** | Dynamic dict stack + eager `bind` + partial `save`/`restore` | Shadowing `/add` flips unbound `{10 20 add}` to `-10` while `bind` stays `30`; `restore` leaves operand/dict stacks intact or throws `/invalidrestore` | Separation of local VM heap from execution/operand/dict stacks | Lexical scoping + full continuation/heap snapshotting |
| **Inform 7** | Five-strata `BookingLists::add` + 9-tier `ActionPatterns::compare_specificity` | Adding a `when` guard or narrowing `thing` $\to$ `container` globally hoists a rule ahead of earlier rules across extensions | Global non-monotonic declarative specificity sorting | **`inkle/ink`** explicit weave/knot/stitch control flow and visit-count state |
| **EVM / Solidity / Vyper** | Untyped $2^{256}$ word storage + `delegatecall` + `EIP-1153` tx-scoped `TSTORE` + unverified compiler slot allocation | Vyper `v0.2.15`–`v0.3.0` (`CVE-2023-39363`) assigned separate lock slots per `@nonreentrant` function and overwrote `storage_layout` JSON; uncleaned `TSTORE` leaks across multicalls | Untrusted high-level compiler owns memory/lock invariants over an untyped flat VM | **Move** on-chain bytecode verifier (abilities, borrow graph, `(address, Type)` storage, static call graph) + `ERC-1967`/`ERC-7201` + Vyper `InsertableOnceDict` |

## Boundaries

- **Uninstalled runtimes (`not examined` via live execution):** PowerShell (`pwsh`), Nushell (`nu`), Oils (`ysh`), Inform 7 (`inform7`), `solc`, `vyper`, and the Move VM CLI were not installed on this host. Claims for those runtimes are backed by direct Git source inspection (`Basis: source`), normative specifications (`Basis: normative`), and Python reproduction of Vyper's `set_storage_slots` logic (`Basis: derived`), rather than live binary execution.
- **PowerShell `StrictMode` and `.ps1xml` custom `TypeConverter` interactions (`not examined`):** While `SessionStateScope.Parent` dynamic lookup and `VariableOps.cs` strict-mode checks were inspected, custom `PSTypeConverter` precedence across `LanguagePrimitives.ConvertTo` and PowerShell class lexical scoping (`class Foo { ... }`) were not exhaustively audited.
- **GNU `gawk` extensions (`not examined`):** Live `awk` execution probes ran on `mawk 1.3.4`, paired with `onetrueawk/awk` C source inspection. `gawk`-specific extensions (`--non-decimal-data`, `typeof()`, `MPFR` arbitrary-precision flags, and `STRNUM` vs `STRING` nuances on `gawk` 5.x) were not executed directly.
- **`jaq` multi-output `|=` runtime behavior (`unknown` via execution):** Direct inspection of `01mf02/jaq` confirmed structural iterator-based `Path::update` / `Part::update` dispatch in `jaq-core/src/path.rs`, but `jaq` was not compiled/executed locally to observe whether `jaq-json`'s `map_index` yields one or multiple top-level JSON objects on `{"a":1} | .a |= (10, 20)`.
- **Solidity `via-IR` (`Yul`) optimizer vs. legacy codegen (`not examined`):** Dirty-bit cleanup citations (`libsolidity/codegen/CompilerUtils.cpp:758-897`) apply directly to Solidity's legacy EVM codegen path; equivalent cleanup passes in the `IRGenerator` / `Yul` pipeline were not inspected separately.
- **Move 2.0 / Sui / Aptos object-model extensions (`known not to apply` without qualification):** Core Move 1.x (`move-language/move`) forbids dynamic dispatch and uses account-indexed `(address, StructType)` storage. Newer ecosystem evolutions (e.g., Move 2 function values / Aptos / Sui UID object-centric storage) extend the core call-graph and storage model and require separate verification.
- **EVM `EOF` (EVM Object Format) and post-Cancun hard forks (`not examined`):** Storage-slot and `EIP-1153` findings reflect Cancun-era EVM semantics (`KEVM` `evm.md`); future `EOF` or Verkle-tree gas-cost changes were not examined.

## Evidence

### Primary Git Repositories Examined (`Basis: source`)
1. **`PowerShell/PowerShell`** at commit `cd071c986fdb21710a629e12796ff539d06afa32`:
   - `src/System.Management.Automation/engine/runtime/Operations/MiscOps.cs:460-471, 639-664, 832-844`: `PipelineOps.PipelineResult` (`0 -> AutomationNull.Value`, `1 -> resultList[0]`, `>=2 -> resultList.ToArray()`).
   - `src/System.Management.Automation/engine/runtime/Binding/Binders.cs:2119-2283, 3046-3107, 3378-3412`: `PSBinaryOperationBinder.CompareEQ`, `BinaryEqualityComparison` (LHS `string` forcing `PSToStringBinder`), and `BinaryComparisonCommon` (LHS enumerable switching to `EnumerableOps.Compare`, LHS numeric coercing RHS).
   - `src/System.Management.Automation/engine/LanguagePrimitives.cs:594-602, 1024-1051`: `Equals` LHS-driven conversion and `IsTrue(IList)` depth-1 recursion cutoff.
   - `src/System.Management.Automation/engine/MshObject.cs:47, 139`, `SessionStateScope.cs:27-50, 293-324`, `parser/Compiler.cs:2175-2179, 5808-5816`.
2. **`nushell/nushell`** at commit `16817a88f38bb62f86c05a128188904e2f1fed0d`:
   - `crates/nu-protocol/src/pipeline/pipeline_data.rs:50-55`: `PipelineData` enum preserving `Value::List` without 1-element unwrapping.
   - `crates/nu-protocol/src/value/mod.rs:2525-2785, 2904-2915, 3991-4021`: `Value::eq`, `strict_eq`, and cross-type `partial_cmp`.
3. **`oils-for-unix/oils`** at commit `d114978ca467143f171a835cbcbe8ab6ccc009a7`:
   - `ysh/expr_eval.py:582-634`: typed YSH arithmetic and strict integer checks.
4. **`jqlang/jq`** at commit `5c001b18d7237cce1fdba63608732163f978dd23`:
   - `src/execute.c:625, 641, 803, 871`: `PATH_BEGIN`, `PATH_END`, `BACKTRACK`, `FORK`.
   - `src/builtin.jq:14-31`: `def _assign` vs `def _modify` (`(., break $out)` first-output cutoff and deferred `delpaths`).
5. **`01mf02/jaq`** at commit `126f17a7f3137876aeaa73dd5246811068f767bd`:
   - `jaq-core/src/filter.rs:514-526, 578-630` and `jaq-core/src/path.rs:86-156`: `Ast::Update`, `Filter::paths`, `Path::update`, `Part::update`.
6. **`onetrueawk/awk`** at commit `72e9b56caddb4a6f8d1405315a5183c26b8650a4`:
   - `awk.h:101-141` (`Cell.tval` flags `NUM`, `STR`, `CON`, `FLD`, `REC`), `run.c:890-935` (`relop` checking `x->tval&NUM && y->tval&NUM` vs `strcmp`), `tran.c:72-81`.
7. **`vim/vim`** at commit `d399646c1f54e30f5288208a911c193fefb6d79c`:
   - `src/typval.c:1498-1555` (`typval_compare2` with `ic` flag) and `src/vim9expr.c:2439-2455`.
8. **`ArtifexSoftware/ghostpdl`** (`5d84ee686543383cbeb7a09ed8a111e96ddcfe95`) and **`freetype/freetype`** (`d7339729da576614cbf107d04a72924d21f7ec5a`):
   - `psi/zdict.c:57-91` (`zbegin`, `zend`), `psi/zvmem.c:59-254` (`zsave`, `zrestore`, `restore_check_save`), `src/truetype/ttinterp.c:106-111, 294-300, 2843-2848` (`tt_default_graphics_state`, `twilight`, `Ins_WCVTP`).
9. **`ganelson/inform`** (`5c7ba42b74db69b93b1290453c65189fa60cfc67`) and **`inkle/ink`** (`4011b8c0a01828c61dd2331613c1038a3a5f294b`):
   - `inform7/assertions-module/Chapter 6/Booking Lists.w:83-300` (`BookingLists::add`), `Rule Bookings.w:118-264` (`RuleBookings::cmp`, placement commentary).
   - `inform7/if-module/Chapter 4/Action Patterns.w:184-215` (`ActionPatterns::compare_specificity`, Laws `III.4.1`, `III.5.1`, `III.5.2`, `III.6.1`).
   - `inform7/if-module/Chapter 4/Action Pattern Clauses.w:281-305, 388-405` (`APClauses::compare_specificity`, Laws `III.1`, `III.2.2`, `III.2.3`), `inform7/values-module/Chapter 2/Specifications.w:211-215`.
   - `ink-engine-runtime/Story.cs` (deterministic story state / callstack execution).
10. **`ethereum/solidity`** (`ce47f2c8e97779e7df8b844648d3c14f6e4af292`):
    - `libsolidity/codegen/CompilerUtils.cpp:758-897` (`convertType`, `cleanHigherOrderBits`).
11. **`vyperlang/vyper`** across four pinned commits:
    - `v0.2.15` (`6e7dba7a8b5f29762d3470da4f44634b819c808d`): `vyper/semantics/validation/data_positions.py:30-35` (per-function slot increment).
    - `v0.3.0` (`8a23febbb2d523f3701f9a7d0aaf361c104a2a37`): `vyper/semantics/validation/data_positions.py:31-48` (per-function slot increment + silent `ret[variable_name]` overwrite).
    - `v0.3.1` (`0463ea4c304858d94494e2df229021448feaedeb`): `vyper/semantics/validation/data_positions.py:35-63` (deduplication via `if variable_name in ret:`).
    - `HEAD` (`d3d07ad34192759ea4978cfd02250c0270161683`): `vyper/semantics/analysis/data_positions.py:49-114` (`InsertableOnceDict`, `GLOBAL_NONREENTRANT_KEY`, `DataLocation.TRANSIENT`).
12. **`ethereum/EIPs`** (`b055feec322fbc37e9d77a393a50b3ff56b31c92`, `EIPS/eip-1153.md:165-245`), **`ethereum/ERCs`** (`10eca3cea34986aeeac0af98ad061ab8928dc15d`, `ERCS/erc-1967.md`, `ERCS/erc-7201.md`), **`runtimeverification/evm-semantics`** (`fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1`, `kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md:468, 1644-1663, 3153-3154, 3265`), and **`move-language/move`** (`c453c90994cba0af30314fe4134acee57fb20d0c`, `language/move-bytecode-verifier/src/{ability_field_requirements.rs:20-52, locals_safety/mod.rs:82-86, reference_safety/abstract_state.rs:308-335, acquires_list_verifier.rs:5-12, 91-104, 183-188}`).

### Live Execution Receipts (`Basis: execution`, observed 2026-11-19)
1. **`jq-1.8.2`:**
   - `jq -cn '[(1,2) + (10,20)]'` $\to$ `[11,12,21,22]`
   - `jq -cn '[(1, empty, 2) + 10]'` $\to$ `[11,12]`
   - `jq -cn '{"a":1,"b":2} | .a |= empty'` $\to$ `{"b":2}`
   - `jq -cn '[10,20,30,40] | (.[0], .[2]) |= empty'` $\to$ `[20,40]`
   - `jq -cn '{"a":1} | .a |= (10, 20)'` $\to$ `{"a":10}` (vs. `jq -cn '{"a":1} | .a = (10, 20)'` $\to$ `{"a":10}` and `{"a":20}`)
   - `jq -cn '{"a":1} | path(.a + 1)'` $\to$ `jq: error (at <unknown>): Invalid path expression with result 2`
2. **`mawk 1.3.4 20260302` (`awk`):**
   - `awk 'BEGIN { print ("01"=="1"), (1=="01"), (01=="01"); split("01 1",a," "); print (a[1]==a[2]), (a[1]==1), (a[1]=="1"), (a[1] ""==a[2] ""); }'` $\to$ `0 0 0` then `1 1 0 0`.
   - `printf '01 1\n' | awk '{ print ($1==$2), ($1==1), ($1=="1"), ($1 ""==$2 ""); }'` $\to$ `1 1 0 0`.
3. **`GNU sed 4.9`:**
   - `printf 'a\nb\nc\n' | sed -n '1h; 1!H; ${g; s/\n/-/g; p;}'` $\to$ `a-b-c`.
   - `printf 'foo\nbar\n' | sed -n 's/foo/FOO/; t hit; s/^/MISS:/; b done; :hit; s/^/HIT:/; :done; p'` $\to$ `HIT:FOO` / `MISS:bar`.
4. **`VIM 9.2 (2026 Feb 14)`:**
   - Legacy Vimscript with `set ignorecase`: `"a" == "A"` $\to$ `1`, `"a" ==# "A"` $\to$ `0`, `"abc" == 0` $\to$ `1`, `"12abc" + 0` $\to$ `12`.
   - `vim9script` with `set ignorecase`: `'a' == 'A'` $\to$ `false`, `'a' ==? 'A'` $\to$ `true`, `eval('"abc" == 0')` $\to$ `Vim(var):E1072: Cannot compare string with number`.
5. **`GPL Ghostscript 10.08.0` (PostScript):**
   - Shadowing `/add { sub } def` on dict stack: `f_unbound` $\to$ `-10`, `f_bound` (`bind`) $\to$ `30`.
   - `snap restore`: `arr[0]` rolled back `99 -> 1`, `pre_dict /tag` rolled back `(mutated_after_save) -> (pre_save_dict)`, operand stack retained `999`, `pre_dict` remained on dict stack; leaving a post-`save` `1 dict begin` on `d_stack` triggered `caught_error=/invalidrestore`.
6. **Vyper `set_storage_slots` Python Reproduction (`Basis: derived` from `v0.3.0` vs. `v0.3.1` source):**
   - Over `[("add_liquidity", "lock"), ("remove_liquidity", "lock"), ("exchange", "lock")]`:
   - `v0.3.0` compiled slots: `{'add_liquidity': 0, 'remove_liquidity': 1, 'exchange': 2}`, reported `storage_layout`: `{'nonreentrant.lock': {'type': 'nonreentrant lock', 'location': 'storage', 'slot': 2}}`.
   - `v0.3.1` compiled slots: `{'add_liquidity': 0, 'remove_liquidity': 0, 'exchange': 0}`, reported `storage_layout`: `{'nonreentrant.lock': {'type': 'nonreentrant lock', 'location': 'storage', 'slot': 0}}`.

## Revalidation

Each subsystem has a fast, discriminating revalidation check:

1. **PowerShell vs. Nushell:** On a host with `pwsh`, run `pwsh -NoProfile -Command '(@($null) -eq $null).Count; [bool](@(1,$null) -eq $null); [bool](@($null,$null) -eq $null); ("02" -eq 2); (2 -eq "02")'` (expect `1`, `False`, `True`, `False`, `True`) and diff `PipelineOps.PipelineResult` (`MiscOps.cs`) and `PSBinaryOperationBinder.CompareEQ` (`Binders.cs`) against newer `PowerShell/PowerShell` commits. On `nu`, confirm `("02" == 2)` and `(2 == "02")` both return `false` and `([1] | describe)` remains `list<int>`.
2. **`jq`, `awk`, `sed`, `Vim`, `PostScript`:** Rerun the exact 1-line commands recorded under **Evidence -> Live Execution Receipts** against any upgraded binary version (`jq`, `awk`/`gawk`/`mawk`, `sed`, `vim`, `gs`) to confirm behavioral continuity in under 1 second.
3. **Inform 7:** Diff `ActionPatterns::compare_specificity` (`Action Patterns.w`), `APClauses::compare_specificity` (`Action Pattern Clauses.w`), and `BookingLists::add` (`Booking Lists.w`) in `ganelson/inform` for changes to Laws `III.1`–`III.6.1` or placement strata.
4. **EVM / Vyper / Solidity / Move:**
   - Diff `vyper/semantics/analysis/data_positions.py` in `vyperlang/vyper` to verify `InsertableOnceDict` and `GLOBAL_NONREENTRANT_KEY` remain intact; for bytecode-level auditing of historical Vyper contracts compiled with `0.2.15`–`0.3.0`, inspect disassembled `SLOAD`/`SSTORE` lock-slot constants directly in runtime bytecode rather than trusting `storage_layout` JSON.
   - Check `libsolidity/codegen/CompilerUtils.cpp` (`cleanHigherOrderBits`) and the Yul optimizer for dirty-bit preservation.
   - Check `language/move-bytecode-verifier/src/{ability_field_requirements.rs, locals_safety/mod.rs, reference_safety/abstract_state.rs, acquires_list_verifier.rs}` in `move-language/move` (or target chain forks such as Aptos/Sui) for ability or dynamic-dispatch relaxations.
