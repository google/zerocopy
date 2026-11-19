# Implicit State Machines, Missing-Value Algebras, and Control-Flow Traps in Enterprise Batch and Grid Languages (SAS, SAP ABAP, IBM RPG/JCL/REXX, Excel, and DAX)

## Summary

Enterprise batch, statistical, mainframe orchestration, and reactive-grid languages—specifically **SAS DATA step / Macro** (contrasted with **SPSS/PSPP**), **SAP ABAP**, **IBM ILE RPG**, **IBM z/OS JCL**, **REXX / ooRexx**, **Microsoft Excel (Dynamic Arrays / `LAMBDA`)**, and **DAX**—depart systematically from lexical, call-stack, and three-valued-null assumptions common in mainstream imperative and functional verification models. Across these systems, correctness failures repeatedly arise from five recurring semantic mechanisms:

1. **Implicit record-loop state machines with heterogeneous retention:** SAS's Program Data Vector (PDV) resets newly computed variables to missing at the top of each row iteration while retaining `SET`/`MERGE`/`RETAIN`/`SUM` slots across rows (causing cross-subject clinical baseline bleed when `FIRST.<key>` resets are omitted), SPSS/PSPP's `LEAVE` initializes numeric retained slots to `0` rather than `SYSMIS` (`-DBL_MAX`), and IBM RPG's compiler-synthesized program cycle runs total calculations (`L1`–`L9`/`LR`) *after* reading the next record but *before* moving its fields into processing storage.
2. **Non-standard missing-value and cross-type total orders:** SAS encodes 28 distinct missing values (`._ < . < .A < ... < .Z`) as IEEE-754 tagged quiet NaNs (`0xFFFF_FF00_0000_0000` down to `0xFFFF_E400_0000_0000`) ordered strictly below $-\infty$, making predicates such as `val < 50` evaluate to **TRUE** on missing data. Excel imposes a cross-type comparison total order (`Number < Text < Logical`), making `"2" > 10` evaluate to **TRUE**.
3. **Database-vs-heap transaction divergence and dual-symbol overloading:** SAP ABAP's `ROLLBACK WORK` aborts uncommitted database writes, discards `IN UPDATE TASK` / `ON COMMIT` registrations, closes all open database cursors, and releases `_SCOPE = 2` enqueue locks, but **never rolls back ABAP session memory** (internal tables, global state, object attributes). Legacy `WITH HEADER LINE` binds a single identifier to both a table body and a 1-row scalar work area (`CLEAR itab` resets only the header; `CLEAR itab[]` / `REFRESH itab` clears the body).
4. **Inverted control-flow polarity, stateful catalog automata, and string-substituted compound environments:** IBM z/OS JCL `COND=(code, op[, step])` evaluates `code op prior_RC` (threshold on the LHS, return code on the RHS) and **skips** the step if *any* test is true; `DISP=(status, normal, abnormal)` defaults depend dynamically on whether a `MOD` dataset already exists (`KEEP` vs `DELETE`), and `NOT CATLGD 2` (`IEF287I`) leaves a dataset uncataloged with step `RC=0`. In REXX/ooRexx, unassigned simple symbols evaluate to their uppercased literal name, tail substitution preserves substituted value casing without raising `NOVALUE`, and an explicitly `DROP`ped compound tail bypasses the stem default value to trigger `NOVALUE`.
5. **Runtime dependency-graph mutation and implicit relational context lifting:** Excel Dynamic Arrays mutate cell dependency edges dynamically during recalculation (`#SPILL!` occlusion and self-referential spill cycles via `A1#`). DAX `CALCULATE` (and every measure reference) lifts active Row Contexts into Filter Contexts across all columns of the expanded table, causing multiplicative duplicate-row amplification on keyless tables and hidden circular dependencies across sibling calculated columns.

Any transpiler, static analyzer, formal verifier, or migration pipeline targeting these languages must model these implicit state spaces explicitly; naive lowering to standard SQL, Python/pandas, or lexical imperative IRs silently flips predicate truth values, leaks cross-record state, or breaks transaction boundaries.

## Applicability

This report covers the core operational semantics, memory/storage state transitions, and static-analysis hazards of the eight language and runtime families listed in `REPORT.json`. Specifically:

- **SAS 9.4 DATA step & Macro Facility** findings apply to single-node Base SAS 9.4 DATA step compilation/execution and binary `.sas7bdat` numeric encoding (cross-checked against `WizardMac/ReadStat` commit `d8ed8fa98e9b2b77cfb9cdde6d92b2531e6e13ed`), contrasted with **GNU PSPP** (`gnu-mirror-unofficial/pspp` commit `bc07898bc39c984b7486dcdbd2cbb43fabb52678`) as an open-source implementation of SPSS transformation semantics. They do **not** automatically extend to SAS Viya CAS multi-threaded DATA step execution, where `BY`-group partitioning and `RETAIN` thread-local boundaries differ.
- **SAP ABAP** findings apply to classic ABAP NetWeaver / S/4HANA on-premise SAP LUW execution (`ROLLBACK WORK`, `COMMIT WORK`, `IN UPDATE TASK`, SAP enqueue locks, and non-OO `WITH HEADER LINE` internal tables), cross-checked against `abaplint/abaplint` commit `25443dcf676e3fae546fcf3fc95fea62823f14db`. OO ABAP classes syntactically forbid `WITH HEADER LINE`, and modern ABAP RESTful Application Programming Model (RAP) managed transactional buffers introduce an application-managed buffer layer outside classic dialog LUWs.
- **IBM ILE RPG** findings apply to cycle-main RPG III/IV/ILE programs without `MAIN`/`NOMAIN` control keywords; linear-main modules (`CTL-OPT MAIN(proc)`) omit the fixed-logic cycle entirely.
- **IBM z/OS JCL** findings apply to MVS batch JCL (`EXEC`/`JOB` `COND`, `DD` `DISP`, `IF/THEN/ELSE/ENDIF`) under z/OS JES2/JES3 as specified in *z/OS MVS JCL Reference* (SA23-1385). SMS (System-Managed Storage) policies and `GDG` (Generation Data Group) roll-in rules can alter non-SMS catalog error behavior (`NOT CATLGD 2`).
- **REXX / ooRexx** findings combine ANSI X3.274-1996 classic REXX semantics with direct source inspection of `ooRexx/oorexx` commit `37d734df054a230b4c0cfb61cc4ed8d981032eac`. Where ooRexx extends classic REXX with `stem.[a,b]` bracket syntax or `StemClass` object references, those extensions are explicitly distinguished.
- **Excel and DAX** findings apply to Microsoft Excel 365 with Dynamic Arrays (`#SPILL!`, `A1#`, `@`, `LET`, `LAMBDA`) and Analysis Services Tabular / Power BI DAX engines. Legacy pre-2018 Excel (fixed CSE arrays without dynamic spilling) lacks `#SPILL!` dynamic DAG mutation.

No proprietary SAS, SAP NetWeaver, IBM z/OS, IBM i, Microsoft Excel, or Analysis Services binaries were executed on this host. Concrete open-source decoder/runtime claims are backed by direct Git source inspection (`Basis: source`), normative/vendor specifications (`Basis: normative`, `Basis: documentation`), and executable Python reference models encoding the documented/source transition rules (`Basis: derived`).

## Findings

### 1. SAS DATA Step Program Data Vector (PDV), `RETAIN` State Bleed, Ordered Missing Values, and Macro Quoting (vs. SPSS/PSPP)

#### 1.1 Two-Phase Compilation and Implicit Row-Loop Execution Model
Basis: documentation + derived

A SAS `DATA` step executes in two strictly separated phases:

1. **Compilation Phase:** SAS scans statements sequentially, performs syntax checking, constructs the **input buffer** (for raw external files), and allocates the **Program Data Vector (PDV)**—a flat, single-observation memory record containing user variables plus automatic non-output variables `_N_` (iteration counter, initialized to `1`) and `_ERROR_` (error flag, initialized to `0`).
   - **First-Mention Attribute Inference:** Every variable's type (numeric 8-byte float vs. fixed-width character `$N`) and byte length are frozen at its **first syntactic occurrence** in source order, unless explicitly overridden earlier by `LENGTH` or `ATTRIB`. A classic silent data-corruption bug occurs when a character variable is first assigned a short string literal:
     ```sas
     data t;
       if flag = 1 then status = "OK";        /* First mention freezes status as $2! */
       else             status = "APPROVED";  /* Silently truncated to "AP" at runtime! */
     run;
     ```
     Because compilation fixes `LENGTH status $2` at the first `then` branch before inspecting the `else` branch, `"APPROVED"` is silently truncated to `"AP"` without raising an error or setting `_ERROR_ = 1`.

2. **Execution Phase (Implicit Observation Loop):** SAS loops automatically from the top of the `DATA` step until an input statement (`SET`, `MERGE`, `UPDATE`, `INPUT`) hits end-of-file. At the **top of each iteration**, the PDV applies a **split retention policy** depending on how each variable entered the PDV:

| Variable Origin in PDV | Initial Value Before Iteration 1 | Reset at Top of Iteration $k \ge 2$? | Reset on `BY`-Group Boundary / New Input Dataset? |
| :--- | :--- | :--- | :--- |
| Assignment / `INPUT` (no `RETAIN`) | Missing (`.` or blanks) | **Yes** — reset to `.` or blanks | Yes (already reset every row) |
| Explicit `RETAIN var [init]` | `init` (or `.`/blanks if omitted) | **No** — retains prior row's PDV slot | **No** — persists across `BY` groups unless explicitly cleared |
| Sum statement (`acc + expr;`) | `0` (implicitly retained!) | **No** — retains prior value; ignores missing `expr` | **No** — persists across `BY` groups unless explicitly cleared |
| Read via `SET` / `MERGE` / `UPDATE` | Missing (`.` or blanks) | **No** — retains value from previous observation | **Yes** — reset to missing when switching datasets in concatenated `SET` or at start of a new `BY` group in `MERGE` |
| Automatic (`_N_`, `_ERROR_`, `FIRST.x`, `LAST.x`) | `_N_=1`, `_ERROR_=0` | `_N_` increments, `_ERROR_` resets to `0` | `FIRST.x`/`LAST.x` recomputed per `BY` key lookahead |

#### 1.2 Cross-Subject `RETAIN` State Bleed and `MERGE` Overwrite Hazards
Basis: documentation + derived

In regulated clinical data pipelines (such as CDISC SDTM and ADaM datasets sorted by `USUBJID` and `VISITNUM`), Last Observation Carried Forward (LOCF) or baseline derivation relies on `RETAIN`:

```sas
data adam_buggy;
  set sdtm_vs;
  by usubjid visitnum;
  retain base;
  /* BUG: missing `if first.usubjid then base = .;` */
  if not missing(aval) then base = aval;
  if aval < 50 then low_flag = 1;
run;
```

Two compounding bugs arise from this idiom:
1. **Cross-patient baseline bleed:** Suppose `SUBJ-01` has `VISITNUM=1, AVAL=120.0`, `VISITNUM=2, AVAL=.`, and `SUBJ-02` starts at `VISITNUM=1` with `AVAL=.A` (special missing, e.g., assay failed). Because `RETAIN base` disables both per-row reset and `BY`-group reset, `SUBJ-01`'s value `120.0` bleeds into `SUBJ-02`'s baseline record (`base = 120.0` at `(SUBJ-02, 1)`).
2. **Match-`MERGE` missing overwrite vs. sticky retention:** In `MERGE a b; BY id;`, if dataset `a` has multiple rows for `id=1` and dataset `b` has one row, `b`'s columns are **retained** in the PDV across all rows of `id=1` (implementing a many-to-one broadcast). However, if `b` also has a second row for `id=1` containing `.`, that explicit missing value **overwrites** the non-missing PDV slot from `a` or `b`'s earlier row. Worse, a many-to-many `MERGE` does **not** produce a Cartesian join (unlike SQL `JOIN`): SAS steps one-to-one through both datasets and then repeats the last row of the shorter group for the remaining rows of the longer group.

#### 1.3 28 Ordered Missing Values and IEEE-754 Tagged-NaN Encoding
Basis: documentation + source + derived

SAS defines **28 distinct numeric missing values**: the special underscore missing (`._`), standard system missing (`.`), and 26 case-insensitive lettered special missing values (`.A` through `.Z`, where `.a == .A`). In SAS 9.4, numeric missing values obey a strict total order **below every finite negative number**:

$$._ \;\prec\; . \;\prec\; .A \;\prec\; .B \;\prec\; \dots \;\prec\; .Z \;\prec\; -1.797\times 10^{308} \;\prec\; \dots \;\prec\; 0 \;\prec\; \dots \;\prec\; +1.797\times 10^{308}$$

Direct inspection of `WizardMac/ReadStat` (`d8ed8fa98e9b2b77cfb9cdde6d92b2531e6e13ed`, `src/sas/readstat_sas7bdat_read.c:458-488` and `src/sas/readstat_sas.c:639-658`) reveals the exact binary encoding used in `.sas7bdat` IEEE-754 64-bit doubles:
- On disk, SAS numeric columns have width `3..8` bytes, left-aligned into the high bytes of a 64-bit IEEE-754 double (`val <<= (8 - col_info->width) * 8`, `readstat_sas7bdat_read.c:479`).
- When `isnan(dval)` holds (`readstat_sas7bdat_read.c:483-485`), SAS encodes the missing tag in byte 5 (bits `47..40`) via bitwise complement:
  ```c
  if (isnan(dval)) {
      value.v.double_value = NAN;
      sas_assign_tag(&value, ~((val >> 40) & 0xFF));
  }
  ```
- In `sas_assign_tag` (`readstat_sas.c:639-657`):
  - `tag == 0` (`byte5 = ~0x00 = 0xFF`, 64-bit big-endian pattern `0xFFFF_FF00_0000_0000`) decodes to **`._`**;
  - `tag == 1` (`byte5 = ~0x01 = 0xFE`, `0xFFFF_FE00_0000_0000`) decodes to **`.`** (system missing);
  - `tag == 2..27` (`byte5 = 0xFD..0xE4`, `0xFFFF_FD00_0000_0000` down to `0xFFFF_E400_0000_0000`) decodes to **`'A' + (tag - 2)`** (`.A` through `.Z`).

**Critical Verification Trap (`val < c` is TRUE on missing data):** Because IEEE-754 hardware NaN comparison returns `false` for `<` while SAS's virtual machine maps these tagged NaNs below $-\infty$, any unguarded upper-bound inequality `if aval < 50 then low_flag = 1;` classifies `.`, `._`, and `.A`–`.Z` as `TRUE` (`low_flag = 1`). Safe SAS predicates must guard with `if .Z < aval < 50` or `if not missing(aval) and aval < 50`. Conversely, arithmetic operators (`a + b`) propagate missing values to `.`, whereas summary functions (`SUM(a, b)`) and the sum statement (`acc + expr;`) silently drop missing operands (treating them as `0`).

#### 1.4 Direct Contrast: GNU PSPP / SPSS Missing Values and `LEAVE` Semantics
Basis: source

Inspecting GNU PSPP (`gnu-mirror-unofficial/pspp`, commit `bc07898bc39c984b7486dcdbd2cbb43fabb52678`) exposes a fundamentally different machine representation and state-retention contract for the same statistical-batch domain:
- **System-missing representation (`src/data/val-type.h:27-29`):**
  ```c
  #define SYSMIS (-DBL_MAX)               /* System-missing value. */
  #define LOWEST (float_get_lowest ())    /* Smallest nonmissing finite value. */
  #define HIGHEST DBL_MAX                 /* Largest finite value. */
  ```
  Instead of IEEE-754 quiet NaN payloads, SPSS/PSPP steals the most negative finite double `-DBL_MAX` (`0xFFEFFFFFFFFFFFFF`) for `SYSMIS` (reserving the next representable finite float as `LOWEST`), and stores user-missing values separately as per-variable dictionary metadata (up to 3 discrete values or 1 range + 1 discrete value) rather than in-band bit tags. Relational expressions in SPSS/PSPP follow Kleene three-valued logic (`SYSMIS < 50` evaluates to `SYSMIS`, which fails `IF`), avoiding SAS's missing-less-than-threshold trap.
- **Per-case retention (`src/data/caseinit.c:54-58, 143-158, 188-203`):** PSPP partitions case slots into `preinited_values` (from the data source), `reinit_values` (`LEAVE_REINIT`, reset to `SYSMIS` or spaces on every case), and `left_values` (`LEAVE_LEFT`, corresponding to SPSS `LEAVE`, retained across cases). Crucially, lines `154-157` show:
  ```c
  if (var_is_numeric (v) && var_get_leave (v))
    iv->value.f = 0;
  else
    value_set_missing (&iv->value, iv->width);
  ```
  Unlike SAS `RETAIN x;` (which initializes `x` to missing `.` before iteration 1), SPSS/PSPP `LEAVE x.` initializes numeric retained variables to **`0`** before case 1—a subtle migration hazard when porting accumulators or sentinel-checked variables between SAS and SPSS.

#### 1.5 SAS Macro Facility: Word-Scanner Timing, Delta-Character Quoting, and `CALL SYMPUT` Inversion
Basis: documentation

The SAS Macro Facility operates as a **textual preprocessor inside the Word Scanner** ahead of the `DATA` step compiler:
1. **Compile-Time vs. Execution-Time Macro Quoting:** Quoting functions wrap tokens in unprintable internal "delta" markers to neutralize `;`, `&`, `%`, quotes, and mnemonic operators (`AND`, `OR`, `EQ`):
   - `%STR(...)` and `%NRSTR(...)` execute at **macro compilation time** on literal source text (`%NRSTR` also masks `&` and `%` triggers; unmatched quotes/parens require `%` escape such as `%'`). They cannot quote text produced by resolving a macro variable at run time.
   - `%BQUOTE(...)` and `%NRBQUOTE(...)` execute at **macro execution time** on resolved text and handle unbalanced quotes/parentheses directly. However, `%NRBQUOTE(&v)` still resolves `&v` *before* masking, so if `&v`'s value contains literal `&foo` (e.g., `"AT&T"`), SAS attempts a second-pass resolution and emits `WARNING: Apparent symbolic reference T not resolved`.
   - `%SUPERQ(v)` (taking the symbol *name* without `&`) fetches `v`'s raw value directly from the symbol table and masks all triggers in one atomic step without ever invoking resolution.
2. **The `CALL SYMPUT` / `&var` Phase-Inversion Trap:** `CALL SYMPUT('x', val)` (or `CALL SYMPUTX`) runs during **DATA step execution**, whereas `&x` is expanded by the macro processor during **DATA step compilation** (before a single row executes). Consequently, writing `call symputx('n', 42); y = &n;` inside the *same* `DATA` step either fails (unresolved `&n`) or silently reads a **stale value of `&n` from a previous step**. Reading a macro variable written within the same step requires the runtime function `SYMGET('n')` or deferring `&n` to a subsequent step boundary (`run;`).

---

### 2. SAP ABAP LUW / `ROLLBACK WORK` Heap-Database Split, `WITH HEADER LINE` Dual-Binding, and IBM RPG Fixed-Logic Cycle

#### 2.1 Database LUW vs. SAP LUW and the `ROLLBACK WORK` Split-Brain State
Basis: normative + documentation

SAP NetWeaver / S/4HANA separates **Database LUWs** (ACID transactions on an underlying RDBMS connection) from **SAP LUWs** (logical business transactions that may span multiple interactive dialog screen transitions and multiple ABAP work processes). Because a work process is released back to the pool between dialog steps (PBO/PAI), SAP issues an **implicit database commit** at every screen change, RFC call (`CALL FUNCTION ... DESTINATION`), `WAIT UP TO`, `CALL TRANSACTION`, and certain dialog `MESSAGE` events—meaning direct OpenSQL writes executed mid-dialog cannot be rolled back by a later `ROLLBACK WORK`. To achieve business-transaction atomicity, ABAP defers persistence via `CALL FUNCTION ... IN UPDATE TASK` (logging deferred `V1`/`V2` work packets into database tables `VBHDR`/`VBDATA`/`VBMOD`) and `PERFORM ... ON COMMIT`.

When an ABAP program executes **`ROLLBACK WORK`**, the SAP ABAP Keyword Documentation defines a strict 7-step operational sequence:
1. Executes all subroutines registered via `PERFORM ... ON ROLLBACK`.
2. Discards all subroutines registered via `PERFORM ... ON COMMIT`.
3. Notifies ABAP Object Services to reset managed persistent-object attributes.
4. Deletes all registered `IN UPDATE TASK` function modules (`VB*` log tables) and queued transactional/background RFCs (`ARFCSSTATE`/`ARFCSDATA`).
5. Releases all SAP Enqueue locks acquired with `_SCOPE = 2` (update-owner locks; note that dialog-only `_SCOPE = 1` locks are *not* released by `ROLLBACK WORK` alone).
6. Issues a **database rollback** across all open database connections—discarding uncommitted DB writes, **forcibly closing all open DB cursors** (subsequent `FETCH` or continued `SELECT ... ENDSELECT` raises a runtime dump `DBIF_RSQL_INVALID_CURSOR`), and **emptying Global Temporary Tables (GTTs)**—and sets `sy-subrc = 0`.
7. Raises `CL_SYSTEM_TRANSACTION_STATE=>TRANSACTION_FINISHED` with `KIND = ROLLBACK_WORK`.

**The Heap-Database Divergence Invariant:** Crucially, `ROLLBACK WORK` **does not roll back ABAP internal session memory**. Local variables, global report fields, static class attributes (`CLASS-DATA`), application-level singleton caches, and **internal tables** retain every mutation performed prior to the rollback. If an application writes to an internal buffer table `gt_cache` and updates a database table `z_ledger`, then hits an error and invokes `ROLLBACK WORK` before continuing to process the next batch item, `z_ledger` reverts while `gt_cache` remains permanently poisoned with phantom committed entries. Formal verification or static analysis of ABAP batch loops must treat `ROLLBACK WORK` as a **partial state-reset operator** affecting only $\Sigma_{\text{DB}} \times \Sigma_{\text{VB}} \times \Sigma_{\text{Lock}(\text{scope}=2)}$ while acting as the **identity map** on $\Sigma_{\text{Heap}}$.

#### 2.2 `WITH HEADER LINE` Dual-Symbol Overloading and Refactoring Traps
Basis: documentation + source

Legacy ABAP allows declaring internal tables with an implicit work area sharing the exact same identifier:
```abap
DATA gt_items TYPE STANDARD TABLE OF ty_item WITH HEADER LINE.
```
This single symbol `gt_items` simultaneously binds **two distinct memory objects**:
- `gt_items` (unqualified): resolves to the **1-row scalar header line** in general expression/statement positions (`CLEAR`, `IS INITIAL`, assignments, `MOVE`, `WRITE`), **except** in table-specific statements (`APPEND gt_items`, `LOOP AT gt_items`, `SORT gt_items`, `REFRESH gt_items`, `FREE gt_items`) where it implicitly references the table body (often implicitly reading from or writing to the header line simultaneously!).
- `gt_items[]`: explicitly forces resolution to the **table body**.

| Statement (when `gt_items` has `WITH HEADER LINE`) | Target Component | Effect on Table Body | Effect on Header Line |
| :--- | :--- | :--- | :--- |
| `CLEAR gt_items.` | **Header line only** | **Untouched** (rows remain!) | Zeroed / initial values |
| `CLEAR gt_items[].` | **Table body only** | All rows deleted (memory kept) | **Untouched** (stale row remains!) |
| `REFRESH gt_items.` | **Table body only** (obsolete) | All rows deleted (memory kept) | **Untouched** |
| `FREE gt_items.` | **Table body only** | All rows deleted + memory freed | **Untouched** |
| `IF gt_items IS INITIAL.` | **Header line only** | **Not checked!** | True iff header fields are initial |
| `IF gt_items[] IS INITIAL.` | **Table body only** | True iff 0 rows | Not checked |

Direct inspection of `abaplint/abaplint` (`25443dcf676e3fae546fcf3fc95fea62823f14db`) illustrates why this dual-binding is hazardous even for automated tooling:
- `packages/core/src/abap/types/basic/table_type.ts:24-52` explicitly tracks `withHeader: boolean` in `ITableOptions` and `TableType.isWithHeader()`.
- `packages/core/src/rules/obsolete_statement.ts:38, 166, 285-291` flags both `REFRESH` and `WITH HEADER LINE` as obsolete statements.
- However, `obsolete_statement.ts:420-425` defines a syntactic auto-fix:
  ```ts
  if (statement instanceof Statements.Refresh) {
    if (statementNode.getChildren().length === 6) {
      return undefined;
    }
    return EditHelper.replaceToken(file, statementNode.getFirstToken(), "CLEAR");
  }
  ```
  Notice that unconditionally rewriting `REFRESH gt_items.` to `CLEAR gt_items.` **without checking `TableType.isWithHeader()`** silently inverts the statement's target from the **table body** to the **header line**, turning a table clear into a memory-leaking no-op on the body!

#### 2.3 IBM i ILE RPG Fixed-Logic Cycle and Indicator State Machine
Basis: normative + documentation

Classic IBM RPG (RPG III / RPG IV / ILE RPG without `CTL-OPT MAIN(...)` or `NOMAIN`) wraps user code inside a **compiler-generated fixed program cycle** driven by primary (`P`) and secondary (`S`) input files and 99+ boolean indicators (`*IN01`–`*IN99`, control levels `*INL1`–`*INL9`, `*INL0`, matching record `*INMR`, overflow `*INOF`, and last record `*INLR`).

In each cycle iteration, the runtime executes **seven ordered phases** (IBM i *ILE RPG Reference*, SC09-2508):
1. **Heading and Detail Output:** Writes output specs conditioned on `1P` (first page, cycle 1 only) or active detail indicators from the *previous* iteration.
2. **Read Next Record & Set Control/Record Indicators:** Reads the next record from the primary/secondary file(s) (using matching-field merge logic if secondary files exist) into an **input buffer** (not yet moving data into program fields!), sets record-identifying indicators (`01`–`99`), sets `*INLR = *ON` (and forces `L1`–`L9` on) if EOF is reached, or sets `L1`–`L9` if a control-level key changed.
3. **Total Calculations (`L1`–`L9`, `L0`, `LR` in columns 7–8):** Executes total-time calculation specs while program fields **still hold the previous record's values**—allowing group summaries to finalize before the newly read group's first record overwrites working storage.
4. **Total Output:** Writes total-time output lines (`T` in column 17).
5. **Check `*INLR` Termination Gate:** If `*INLR == *ON`, closes files, unlocks data areas, and exits the program.
6. **Move Input Buffer to Fields & Set Field Indicators:** Transfers the newly read record from the input buffer into named program fields and evaluates field indicators (plus/minus/zero/blank).
7. **Detail Calculations (blank columns 7–8):** Executes record-level business logic, then loops back to Step 1 (Heading and Detail Output).

**Semantic Hazard:** Programmers coming from lexical loops assume reading a record updates variables immediately and that returning without setting `*INLR = *ON` terminates clean state. In RPG: (a) total calculations intentionally lag the physical file read by one record via the staging input buffer; (b) returning with `RETURN` while `*INLR = *OFF` leaves the program **resident in the activation group with open file cursors and preserved static/indicator memory** across subsequent `CALL` invocations; and (c) modern `CTL-OPT MAIN(entry)` or `NOMAIN` modules completely disable the cycle, turning cycle-dependent indicator conventions into dead or uninitialized state.

---

### 3. IBM z/OS JCL Inverted `COND` Predicates, `DISP` Catalog Automata, and REXX/ooRexx Compound Stems

#### 3.1 JCL `COND` Inverted Skip Predicates and `EVEN`/`ONLY` Abend Gates
Basis: normative + derived

IBM z/OS Job Control Language (JCL, *z/OS MVS JCL Reference*, SA23-1385) controls batch step execution via the `COND` parameter on `JOB` and `EXEC` statements:

```jcl
//STEP2 EXEC PGM=PROG2,COND=((4,LT,STEP1),(0,NE,STEP0))
```

`COND` implements **double-inverted boolean semantics** that routinely causes production job-scheduling bugs:
1. **Inverted Control Polarity (Skip-on-True):** If **any** sub-test in `COND=(...)` evaluates to **TRUE**, the step is **BYPASSED** (skipped). The step runs only if **all** sub-tests evaluate to **FALSE** (logical NOR of tests, equivalently logical OR to skip).
2. **Inverted Operand Order (`code` on LHS, `RC` on RHS):** A tuple `(code, op[, stepname])` tests the predicate $\text{code} \;\mathbin{\text{op}}\; \text{RC}(\text{stepname})$, **not** $\text{RC} \;\mathbin{\text{op}}\; \text{code}$! If `stepname` is omitted, the test is applied against *every* prior executed step's return code.
   - `COND=(4,LT)` means *"bypass if $4 < \text{RC}$"*, i.e., **run iff $\text{RC} \le 4$** (so `RC=0` and `RC=4` run; `RC=8` skips).
   - `COND=(0,NE)` means *"bypass if $0 \neq \text{RC}$"*, i.e., **run iff $\text{RC} = 0$**.
   - `COND=(0,LE)` means *"bypass if $0 \le \text{RC}$"*—always true for valid return codes `0..4095`, so the step is **unconditionally skipped**.
3. **`JOB`-Level vs. `EXEC`-Level Precedence:** A `COND` on the `JOB` card is checked *before* every step; if satisfied, the **entire remaining job terminates**. An `EXEC`-level `COND` overrides `JOB`-level `COND` only via `EVEN`/`ONLY` interaction rules (actually, if `JOB` `COND` is satisfied, subsequent steps are bypassed regardless of `EXEC` `COND`, except `JOB` `COND` is ignored on the first step).
4. **Abend Gates (`EVEN` / `ONLY`) and Hard System Overrides:** By default, any prior step ABEND flushes all remaining steps. `COND=EVEN` allows the step to run despite a prior ABEND (while still applying any accompanying RC tests against steps that ended normally); `COND=ONLY` executes *only* if a prior step abended. However, operator/TSO job cancellations (`S122`, `S222`) and JCL syntax/allocation failures bypass all subsequent steps **even when `COND=EVEN` or `COND=ONLY` is coded**.
5. **Contrast with `IF/THEN/ELSE/ENDIF`:** Modern JCL `IF (STEP1.RC <= 4) THEN` restores non-inverted polarity (runs when TRUE, `RC` on the LHS) and supports `ABEND` / `ABENDCC` predicates, but if a step inside an `IF` branch also carries an `EXEC COND=...`, **both** must permit execution (`IF` true AND `COND` false). Furthermore, bypassed steps **never allocate or catalog their `DD` datasets**, causing downstream backward references (`DSN=*.STEP2.OUTDD`) to fail with JCL/allocation errors.

#### 3.2 `DISP=(status, normal, abnormal)` Catalog & `SYSDSN` ENQ Automaton
Basis: normative + derived

The JCL `DD` `DISP=(status, normal, abnormal)` parameter drives a coupled **allocation, catalog, and serialization state machine** across step boundaries:

- **`status`** $\in \{\text{NEW}, \text{OLD}, \text{SHR}, \text{MOD}\}$ (default: `NEW`).
  - `MOD` is **state-dependent**: if the dataset already exists, z/OS opens it positioned at EOF for append; if it does **not** exist (and no incompatible `VOL=SER` prevents creation), z/OS treats it as `NEW` and creates it dynamically.
- **Job-Wide `SYSDSN` Serialization (`ENQ`):** Before step 1 starts, the JES/MVS initiator inspects **every step in the job** and acquires a `SYSDSN` enqueue for each permanent dataset name. If *any* step specifies `NEW`, `OLD`, or `MOD`, z/OS holds an **exclusive (`EXCL`) lock** for the entire duration of the job (until the last referencing step completes), blocking concurrent jobs even while earlier steps only read with `DISP=SHR`.
- **State-Dependent Default Matrix:** Omitted subparameters resolve according to whether the dataset was **created by this step** (`created_new = (status == NEW) || (status == MOD && !existed)`):

| Coded `DISP` | Pre-Existing Dataset? | Effective `(status, normal, abnormal)` | Critical Pitfall |
| :--- | :--- | :--- | :--- |
| `DISP=NEW` (or omitted) | No | `(NEW, DELETE, DELETE)` | Output silently deleted at normal step end! |
| `DISP=MOD` | **No** (created) | `(MOD, DELETE, DELETE)` | Newly created `MOD` dataset silently deleted! |
| `DISP=MOD` | **Yes** | `(MOD, KEEP, KEEP)` | Same JCL text yields opposite default disposition (`DELETE` vs `KEEP`) depending on external disk state! |
| `DISP=(NEW,PASS)` | No | `(NEW, PASS, DELETE)` | `PASS` is illegal as abnormal disp; defaults to `DELETE` on abend |
| `DISP=(OLD,PASS)` | Yes | `(OLD, PASS, KEEP)` | Passed datasets never received by a later step default to their pre-pass status (`DELETE` if `NEW`, `KEEP` if existing) at job end |
| `DISP=(NEW,CATLG,DELETE)` | No (but catalog entry exists on another volume) | Allocates on new vol, fails catalog step with **`IEF287I NOT CATLGD 2`** | **Step finishes with `RC=0`!** New file sits uncataloged while downstream jobs silently read the *old* cataloged dataset! |

#### 3.3 REXX and `ooRexx`: Unassigned Symbol Self-Quoting and Compound Stem Resolution
Basis: normative + source

REXX (ANSI X3.274-1996) and Open Object Rexx (`ooRexx/oorexx`, commit `37d734df054a230b4c0cfb61cc4ed8d981032eac`) exhibit three interconnected evaluation rules that frequently break assumptions about lexical variable errors and hash maps:

1. **Unassigned Simple Symbols Self-Evaluate to Uppercase Strings:** Inspecting `interpreter/expression/ExpressionVariable.cpp:128-144`:
   ```cpp
   RexxVariable *variable = context->getLocalVariable(variableName, index);
   RexxObject *value = variable->getVariableValue();
   if (value == OREF_NULL)
   {
       value = context->handleNovalueEvent(variableName, variableName, variable);
   }
   ```
   When `SIGNAL ON NOVALUE` is not active, reading an unassigned identifier `foo` does **not** raise an error or return `null`: it evaluates to the uppercase string `"FOO"` (because symbol names are uppercased during translation). A misspelled variable name in a conditional (`if countr = 0`) silently compares `"COUNTR" = 0` (`0`, false) instead of failing!

2. **Compound Variable Tail Substitution (`stem.tail1.tail2`) Preserves Substituted Value Case and Suppresses Tail `NOVALUE`:** Inspecting `interpreter/classes/support/CompoundVariableTail.cpp:101-194` and `ExpressionVariable.cpp:176-186`:
   - `CompoundVariableTail::buildTail` resolves each dot-separated tail segment via `tails[i]->getValue(context)` and joins them with literal `'.'` (`addDot()`).
   - Crucially, `RexxSimpleVariable::getValue(RexxActivation *context)` (`ExpressionVariable.cpp:176-186`) returns `variableName` when `value == OREF_NULL` **without invoking `handleNovalueEvent`**—matching ANSI REXX's rule that an unassigned *tail* symbol does not raise `NOVALUE` (only the full compound lookup can).
   - If `i = "abc"` (lowercase), `stem.i` resolves to key `"abc"` (case-sensitive, NOT uppercased!), whereas if `j` is unassigned, `stem.j` resolves to key `"J"` (uppercased symbol name). Thus `i = "x"; a.i = 1` writes tail `"x"`, completely disjoint from `a.X` (`"X"`).

3. **Unassigned Tail vs. Explicitly `DROP`ped Tail Divergence in `StemClass`:** Inspecting `interpreter/classes/StemClass.cpp:213-228` and `794-839` reveals a sharp state-machine invariant after assigning a stem default (`a. = 0`, which sets `value = 0` and `dropped = false`):
   - **Never-assigned tail (`a.foo`):** `findCompoundVariable(resolved_tail)` returns `OREF_NULL` (`StemClass.cpp:799-807`). Because `!dropped` is true, `evaluateCompoundVariableValue` returns the stem default **`0`** and **does not raise `NOVALUE`**.
   - **Explicitly `DROP`ped tail (`a.bar = 5; drop a.bar; say a.bar`):** The `CompoundTableElement` entry *still exists* in the stem's compound tree with `varValue == OREF_NULL` (`StemClass.cpp:825-836`). `evaluateCompoundVariableValue` **bypasses the stem default `0`**, synthesizes the literal string `stemName || resolved_tail` (`"A.BAR"`), and invokes **`handleNovalue(...)`**!
   ```cpp
   // StemClass.cpp:825-836
   RexxObject *varValue = variable->getVariableValue();
   if (varValue == OREF_NULL)
   {
       RexxString *tail_name = resolved_tail.createCompoundName(stemVariableName);
       RexxObject *defaultValue = resolved_tail.createCompoundName(stemName);
       return handleNovalue(context, tail_name, defaultValue, variable);
   }
   ```
   Deleting a key with `DROP a.bar` therefore does **not** restore `a.bar` to the stem default `a.`—it transitions `a.bar` into a third tombstone state (`dropped-entry`) distinct from both `assigned` and `absent`.

---

### 4. Reactive Grid and BI Formula Calculi: Excel Dynamic-Array `#SPILL!` DAG Mutation and DAX `CALCULATE` Context Transitions

#### 4.1 Excel Dynamic Arrays, Runtime Dependency-Graph Mutation (`#SPILL!`), and `LAMBDA`
Basis: documentation + derived

In classic spreadsheets (and Peyton Jones, Blackwell, & Burnett's *ICFP 2003* functional formalization, DOI `10.1145/944705.944721`), cell formulas form a **statically structured dataflow DAG** determined syntactically by cell references (apart from volatile/dynamic lookup primitives `INDIRECT` and `OFFSET`). Modern Excel 365 introduces **Dynamic Arrays** and first-class **`LAMBDA` / `LET`** closures (building on elastic sheet-defined functions, McCutchen et al. *JFP 2020*, DOI `10.1017/S0956796820000234`), fundamentally altering recalculation semantics:

1. **Dynamic Topology Mutation & `#SPILL!`:** A single formula in anchor cell `A1` (e.g., `=UNIQUE(D1:D100)`) evaluates to a 2D matrix of runtime shape $(r, c)$ and dynamically claims the target rectangle `A1 : offset(A1, r-1, c-1)`:
   - **Spatial Occlusion (`#SPILL!`):** If any non-empty cell occupies the computed spill rectangle, the anchor cell fails with `#SPILL!` and yields **zero** spilled cells—leaving downstream scalar references to `A2` seeing an empty cell (`0` in numeric contexts) rather than `#SPILL!`, whereas spill-range references (`A1#`) propagate `#SPILL!`.
   - **Dynamic Spill Cycles:** If cell `A1`'s spill dimensions depend on a cell `B5` that lies inside `A1`'s newly computed spill footprint (or depends on `A1#` in a shape-oscillating loop), the dependency graph acquires a **runtime-induced cycle** during recalculation, terminating in `#SPILL!` (indeterminate spill size).
   - **Implicit Intersection (`@`) Transition:** Legacy Excel silently projected multi-cell ranges to a single row/column cell via implicit intersection unless entered as fixed CSE (`Ctrl+Shift+Enter`). Dynamic Array Excel broadcasts ranges by default and inserts explicit `@` operators when upgrading legacy formulas to prevent accidental spilling.

2. **Cross-Type Total Order and Heterogeneous Coercion:** Excel's relational operators (`<`, `<=`, `>`, `>=`, `=`, `<>`) define a strict cross-type total order:
   $$\text{Number} \;<\; \text{Text (case-insensitive)} \;<\; \text{Logical } (\texttt{FALSE} < \texttt{TRUE})$$
   Errors (`#VALUE!`, `#N/A`, `#SPILL!`, `#CALC!`) are non-comparable and propagate immediately. Consequently:
   - `"2" > 10` evaluates to **`TRUE`** (every string exceeds every number, including `"" > 1E+300` -> `TRUE`!).
   - `FALSE > "zzz"` evaluates to **`TRUE`**!
   - Coercion is **operator-dependent**: `="2" + 10` coerces `"2"` to `2` yielding `12`; `=SUM("2", 10)` coerces direct literal arguments yielding `12`; yet `=SUM(A1:A2)` where `A1="2"` and `A2=10` **ignores** text cells in ranges yielding **`10`**!

3. **`LAMBDA` / `LET` Closure Boundaries:** `LET(x, expr, body)` introduces lexical scope and single-evaluation sharing, while `LAMBDA(x, body)` creates anonymous first-class functions consumable by `MAP`, `REDUCE`, `SCAN`, `BYROW`, `BYCOL`, and recursive Name Manager bindings. However, because grid cells must serialize to scalar/array values, an unapplied `LAMBDA` returned directly to a worksheet cell evaluates to `#CALC!` rather than a printable value.

#### 4.2 DAX Dual Evaluation Contexts and `CALCULATE` Context Transition
Basis: documentation + derived

Microsoft's **DAX** (Data Analysis Expressions, used in Power BI and Analysis Services Tabular) evaluates expressions over a star-schema relational model under **two orthogonal environments**:

- **Row Context ($\rho$):** Binds a single "current row" pointer for each table being iterated (created automatically inside **calculated columns** and inside iterator functions such as `SUMX(T, expr)`, `FILTER(T, pred)`, `ADDCOLUMNS`). A Row Context permits reading `T[Col]` directly, but **does not filter other tables** along model relationships (even active 1-to-many edges).
- **Filter Context ($\phi$):** A set of table/column predicate filters originating from report slicers, pivot axes, and `CALCULATE`/`CALCULATETABLE` arguments. Filter Contexts propagate automatically from the **1-side to the many-side** of active relationships (and bidirectionally when configured).

**The `CALCULATE` Context Transition Rule:** Whenever `CALCULATE(expr, f_1, ..., f_k)`—or **any Measure reference `[MyMeasure]`**, which implicitly wraps its body in `CALCULATE(...)`—is evaluated in a state $(\rho, \phi)$ with an active Row Context $\rho$:
1. **Step 1 (Implicit Context Transition):** Every active Row Context $\rho(T) = r$ is lifted into an equivalent Filter Context predicate constraining **every column of the expanded table $T^+$** (all columns of $T$ plus all related 1-side dimension columns reachable via many-to-one relationships) to equal their values in row $r$:
   $$\phi_1 = \phi \oplus \{ T^+[c] = r[c] \mid c \in \text{Cols}(T^+) \}$$
   (where $\oplus$ overwrites existing filters on those columns).
2. **Step 2 (Explicit Filter Modifiers):** Each filter argument $f_i$ is evaluated in the **outer** filter context $\phi$ (before Step 1/Step 2 mutations, though still seeing $\rho$ if $f_i$ references row values), then applied to $\phi_1$:
   - Default predicate `T[Col] = val` (sugar for `FILTER(ALL(T[Col]), T[Col] = val)`) **overwrites** any existing filter on `T[Col]`.
   - Wrapping in `KEEPFILTERS(T[Col] = val)` **intersects** the new filter with the existing filter on `T[Col]` instead of overwriting it.
   - Modifiers such as `REMOVEFILTERS(...)` / `ALL(...)` strip filters from $\phi_1$.
3. **Step 3 (Evaluation):** `expr` is evaluated under $(\emptyset_{\text{trans}}, \phi_2)$—the transitioned row context is consumed for the inner evaluation.

**Two Concrete Soundness & Dependency Pathologies of Context Transition:**
1. **Multiplicative Duplicate-Row Amplification (Keyless Tables):** Consider a 3-row `Sales` table with **no primary key**:
   `{ (Product: "Widget", Amount: 100), (Product: "Widget", Amount: 100), (Product: "Gadget", Amount: 50) }`.
   - `SUMX(Sales, Sales[Amount])` uses pure Row Context: $100 + 100 + 50 = \mathbf{250}$.
   - `SUMX(Sales, CALCULATE(SUM(Sales[Amount])))` (equivalently `SUMX(Sales, [Total Sales])`) triggers Context Transition on every row. For *each* of the two identical `("Widget", 100)` rows, the lifted filter `{Product="Widget", Amount=100}` matches **both** duplicate rows, yielding $200 + 200 + 50 = \mathbf{450}$—an invisible $+200$ ($+80\%$) financial overcount whenever a table lacks a unique key!
2. **Hidden Calculated-Column Circular Dependency:** Because Context Transition inside a calculated column captures **every column of the table** (including other calculated columns in the same table!), defining *two* calculated columns `ColA = [Measure1]` and `ColB = [Measure2]` on the same table causes `ColA` to depend on `{all columns including ColB}` and `ColB` to depend on `{all columns including ColA}`, triggering an engine **Circular Dependency Error** even though neither formula syntactically mentions the other! Breaking the cycle requires either moving logic to measures or restricting transition scope via `ALLEXCEPT(T, T[PrimaryKey])` / `REMOVEFILTERS`.

---

### 5. Cross-System Synthesis: Implicit State-Machine Taxonomy and Verification Boundaries

Basis: derived

| Language / Engine | Implicit State Carrier | Reset / Transition Trap | Null / Missing / Type Ordering Trap | Rollback / Side-Effect Boundary | Verification / Migration Invariant |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **SAS DATA Step** | Single-row PDV + Macro symbol table | Assignment vars reset per row; `RETAIN`/`SUM` persist across `BY` groups; `SET`/`MERGE` reset on `BY`/dataset change | 28 tagged-NaN missing values (`._ < . < .A..\,.Z < -\infty`); `x < 50` is **TRUE** on missing | First syntactic mention freezes char `$N` width (silent truncation); `CALL SYMPUT` lags `&var` by a phase | Guard all `<`/`<=` with `not missing(x)`; emit explicit `if first.key` resets; model macro quoting separately from DATA step AST |
| **SPSS / GNU PSPP** | Per-case `caseinit` (`reinit` vs `left` lists) | `LEAVE` initializes numeric retained vars to `0` (not `SYSMIS`) | `SYSMIS = -DBL_MAX` (`0xFFEFFFFFFFFFFFFF`); Kleene 3-valued relational logic | Transformation queue deferred until `EXECUTE` / procedure pass | Do not equate SAS `RETAIN` initial state (`.`) with SPSS `LEAVE` initial state (`0`) |
| **SAP ABAP** | DB LUW + VB update log + Enqueue table + ABAP session heap | `WITH HEADER LINE` splits `CLEAR itab` (header) vs `CLEAR itab[]` (body) | `INITIAL` checks header line when header exists | `ROLLBACK WORK` reverts DB/VB/`_SCOPE=2` locks & closes cursors, **never** reverts internal tables/heap; implicit DB commits on screen/RFC | Model ABAP state as $\Sigma_{\text{DB}} \times \Sigma_{\text{Heap}}$; forbid `REFRESH -> CLEAR` rewrite unless `!isWithHeader()` |
| **IBM ILE RPG** | Compiler-driven fixed cycle + input staging buffer + `*IN01`–`*IN99`/`L1`–`L9`/`LR` | Total calcs (`L1`–`L9`/`LR`) run *after* physical read but *before* field move | Indicator persistence when `RETURN` runs with `*INLR = *OFF` | Static storage & open file cursors persist across `CALL` until `*INLR = *ON` | Explicitly model the 1-record staging buffer lag between read and field load; distinguish cycle-main vs `MAIN`/`NOMAIN` |
| **IBM z/OS JCL** | Prior step RC vector + MVS catalog + `SYSDSN` ENQ table | `COND=(code, op)` tests `code op RC` and **skips on TRUE**; `DISP=MOD` defaults to `DELETE` if new vs `KEEP` if existing | `COND` OR-to-skip vs `IF/THEN` non-inverted polarity | `IEF287I NOT CATLGD 2` exits with `RC=0` leaving new dataset uncataloged; `S122`/`S222` bypass `EVEN`/`ONLY` | Formalize `COND` with explicit negation + operand swap; model catalog & volume states separately from step exit codes |
| **REXX / ooRexx** | Local var dictionary + `StemClass` compound tree (`dropped` flag + element slots) | Unassigned simple symbol -> uppercase name; `DROP a.k` bypasses stem default `a.` and triggers `NOVALUE` | Tail value substitution preserves lowercase; unassigned tail uppercases without `NOVALUE` | `SIGNAL ON NOVALUE` alters control flow globally (non-local jump, not resumable catch) | Model compound entries as 3-state (`Absent`, `Assigned(v)`, `DroppedTombstone`), never as a 2-state map |
| **Excel 365** | Reactive cell grid + dynamic spill footprints (`A1#`) | Runtime spill shape mutates dependency DAG (`#SPILL!` occlusion / cycle) | `Number < Text < Logical` (`"2" > 10` is `TRUE`); `SUM` ignores text in ranges but coerces direct literals | Unapplied `LAMBDA` in grid cell produces `#CALC!`; volatile `INDIRECT` breaks static DAG | Static spreadsheet verifiers must over-approximate spill rectangles and type-discriminate comparison operands |
| **DAX** | Dual Row Context $\rho$ + Filter Context $\phi$ over expanded star-schema tables | `CALCULATE` / measure ref lifts $\rho$ to $\phi$ across all columns of expanded table $T^+$ | Duplicate rows without primary key amplify `CALCULATE` aggregates multiplicatively | Two calculated columns using `CALCULATE` induce hidden circular dependencies | Require unique keys before Context Transition; model expanded tables $T^+$ explicitly in dependency checking |

## Boundaries

- **Proprietary runtime execution (`not examined`):** No live proprietary SAS 9.4, SAP NetWeaver ABAP, IBM i RPG, IBM z/OS JES2/JES3, Microsoft Excel 365, or Power BI / Analysis Services Tabular runtime binaries were executed on this host. Claims about those proprietary systems rely on official vendor specifications/documentation (`Basis: normative`, `Basis: documentation`), direct source inspection of open-source implementations/analyzers (`ReadStat`, `PSPP`, `abaplint`, `ooRexx`; `Basis: source`), and executable Python reference models encoding those rules (`Basis: derived`).
- **SAS Viya CAS distributed execution (`known not to apply`):** SAS 9.4 single-threaded PDV and `RETAIN` cross-row behavior does **not** carry over unchanged to SAS Viya Cloud Analytic Services (CAS) multi-threaded DATA step execution, where rows are partitioned across worker threads unless a `BY` group is explicitly grouped per thread or run in single-thread mode.
- **SAP ABAP RAP / Cloud (`not examined`):** Modern SAP BTP ABAP Cloud and the ABAP RESTful Application Programming Model (RAP) forbid `COMMIT WORK`/`ROLLBACK WORK` inside managed behavior implementations and introduce a separate transactional buffer lifecycle; this report's LUW findings characterize classic ABAP NetWeaver/S/4HANA LUWs.
- **IBM z/OS SMS overrides and GDG catalog semantics (`not examined`):** Under z/OS DFSMS (System-Managed Storage), datasets are cataloged at **allocation time** rather than step-termination time, which converts many classic non-SMS `IEF287I NOT CATLGD 2` step-end failures into immediate JCL allocation errors (`IGD17101I`). Generation Data Groups (`GDG` relative `(+1)`/`(0)` versioning) and `COND` interaction with `RESTART=` were not examined.
- **DAX Auto-Exist and `ALLSELECTED` shadow filter contexts (`not examined`):** DAX's same-table Auto-Exist optimization (which produces non-intuitive results when filtering two columns of the same table simultaneously via `SUMMARIZECOLUMNS` vs `FILTER`) and `ALLSELECTED`'s shadow filter context stack were not examined in full detail.
- **Excel floating-point IEEE-754 "close-to-zero" heuristic (`not examined`):** Excel's documented rounding-to-zero heuristic in subtraction (`=1.1 - 1.0 - 0.1` vs `=(1.1 - 1.0 - 0.1)`) was not examined here.
- **Stronger conclusion not established:** Because `abaplint` is a static analyzer/linter rather than the SAP NetWeaver ABAP kernel, its `TableType.isWithHeader()` and `obsolete_statement.ts` rules demonstrate static-tooling hazards rather than directly proving SAP kernel internals.

## Evidence

### Primary Git Repositories Examined (`Basis: source`)
1. **`WizardMac/ReadStat`** at commit `d8ed8fa98e9b2b77cfb9cdde6d92b2531e6e13ed`:
   - `src/sas/readstat_sas7bdat_read.c:458-488`: 3–8 byte column unpacking into 64-bit IEEE-754 double (`val <<= (8 - col_info->width) * 8`), `isnan(dval)` dispatch, and tag extraction `~((val >> 40) & 0xFF)`.
   - `src/sas/readstat_sas.c:639-658` (`sas_assign_tag`): exact mapping `tag == 0 -> '_'`, `tag == 1 -> system missing`, `2 <= tag < 28 -> 'A' + (tag - 2)`.
2. **`gnu-mirror-unofficial/pspp`** at commit `bc07898bc39c984b7486dcdbd2cbb43fabb52678`:
   - `src/data/val-type.h:27-29`: `#define SYSMIS (-DBL_MAX)`, `LOWEST`, `HIGHEST`.
   - `src/data/caseinit.c:54-58, 143-158, 188-203`: `LEAVE_REINIT` vs `LEAVE_LEFT`, `init_list_mark` initializing numeric `LEAVE` variables to `0` and non-`LEAVE` variables to missing.
3. **`abaplint/abaplint`** at commit `25443dcf676e3fae546fcf3fc95fea62823f14db`:
   - `packages/core/src/abap/types/basic/table_type.ts:24-52`: `ITableOptions.withHeader` and `TableType.isWithHeader()`.
   - `packages/core/src/rules/obsolete_statement.ts:38, 166, 285-291, 420-425`: `withHeaderLine` and `refresh` checks, plus `getFix` rewriting `REFRESH` token to `CLEAR`.
4. **`ooRexx/oorexx`** at commit `37d734df054a230b4c0cfb61cc4ed8d981032eac`:
   - `interpreter/expression/ExpressionVariable.cpp:128-144, 176-186`: `RexxSimpleVariable::evaluate` calling `handleNovalueEvent` vs `RexxSimpleVariable::getValue` silently returning `variableName` without raising `NOVALUE`.
   - `interpreter/classes/support/CompoundVariableTail.cpp:101-194`: `CompoundVariableTail::buildTail` substituting tail values without uppercasing and joining with `addDot()`.
   - `interpreter/classes/StemClass.cpp:213-228, 794-839`: `StemClass::setValue`, `dropValue`, and `evaluateCompoundVariableValue` distinguishing `variable == OREF_NULL` (returns stem default `value` when `!dropped`) from `variable != OREF_NULL && varValue == OREF_NULL` (explicitly dropped tail ignores stem default and invokes `handleNovalue`).

### Specifications, Vendor Documentation, and Peer-Reviewed Literature (`Basis: normative`, `Basis: documentation`)
- **SAS 9.4 Language Reference: Concepts** & **SAS 9.4 Macro Language: Reference** (SAS Institute Inc.): PDV compilation/execution phases, `RETAIN`/`SET`/`MERGE` initialization rules, 28-missing-value sort order (`._ < . < .A`–`.Z` `<` all numbers), `%STR`/`%NRSTR`/`%BQUOTE`/`%NRBQUOTE`/`%SUPERQ` quoting timing, and `CALL SYMPUT` / `SYMGET`.
- **SAP ABAP Keyword Documentation** (SAP SE): *Database LUW* vs *SAP LUW*, `ROLLBACK WORK` 7-step semantics (DB rollback, cursor invalidation, GTT clear, `_SCOPE = 2` lock release, non-rollback of ABAP session memory), and obsolete `WITH HEADER LINE` / `REFRESH` / `CLEAR itab[]` rules.
- **IBM i ILE RPG Reference** (SC09-2508): *RPG Program Cycle* 7-phase sequence, Detail vs Total calculations (`L1`–`L9`, `L0`, `LR`), `*INLR` termination gate, and `MAIN`/`NOMAIN` cycle omission.
- **IBM z/OS MVS JCL Reference** (SA23-1385): `EXEC`/`JOB` `COND=(code, op[, stepname])`, `EVEN`/`ONLY`, `S122`/`S222` cancellation override, `DISP=(status, normal, abnormal)` defaults (`NEW` vs existing vs newly created `MOD`, `PASS`), and `IEF287I NOT CATLGD 2`.
- **ANSI X3.274-1996**: REXX symbol evaluation, `NOVALUE` condition, and compound variable substitution rules.
- **Simon Peyton Jones, Alan Blackwell, and Margaret Burnett**, *"A User-Centred Approach to Functions in Excel"*, ICFP 2003, DOI `10.1145/944705.944721`.
- **Matt McCutchen, Judith Borghouts, Andrew D. Gordon, Simon Peyton Jones, and Advait Sarkar**, *"Elastic Sheet-Defined Functions: Generalising Spreadsheet Functions to Variable-Size Input Arrays"*, *Journal of Functional Programming*, Vol. 30, e26, 2020, DOI `10.1017/S0956796820000234`.
- **Microsoft Excel & DAX Documentation** (`learn.microsoft.com`): Dynamic array `#SPILL!` semantics, `Number < Text < Logical` comparison order, `CALCULATE` context transition, `KEEPFILTERS`, and calculated-column expanded-table circular dependencies.

### Executable Reference-Model Verification Probes (`Basis: derived`, observed 2026-11-19 on Python 3.13.15)
Executing a self-contained Python 3.13.15 script encoding the source/documented rules produced these exact outputs:
1. **SAS IEEE-754 Tagged-NaN Decoder (`ReadStat` bit rule):**
   - `._ -> 0xFFFFFF0000000000 -> isnan=True, decoded=._`
   - `.  -> 0xFFFFFE0000000000 -> isnan=True, decoded=.`
   - `.A -> 0xFFFFFD0000000000 -> isnan=True, decoded=.A`
   - `.Z -> 0xFFFFE40000000000 -> isnan=True, decoded=.Z`
   - All 28 bit patterns bijectively decoded in ascending sort order `['._', '.', '.A', '.B', ..., '.Y', '.Z']`.
2. **SAS PDV `RETAIN` Bleed & Missing-Less-Than-50 Trap:**
   - Input `[("SUBJ-01", 1, 120.0), ("SUBJ-01", 2, None), ("SUBJ-02", 1, '.A'), ("SUBJ-02", 2, 45.0)]` without `if first.usubjid then base = .;`:
   - Output row `('SUBJ-02', 1, '.A', 120.0, True)` confirms BOTH cross-patient baseline bleed (`base = 120.0` from `SUBJ-01`) AND `.A < 50` evaluating `True`.
3. **JCL `COND` & `DISP` Automaton:**
   - `STEP1 RC=0: COND=(4,LT) -> EXECUTED | COND=(0,NE) -> EXECUTED`
   - `STEP1 RC=4: COND=(4,LT) -> EXECUTED | COND=(0,NE) -> bypassed: (0,NE) TRUE against RC=4`
   - `STEP1 RC=8: COND=(4,LT) -> bypassed: (4,LT) TRUE against RC=8 | COND=(0,NE) -> bypassed: (0,NE) TRUE against RC=8`
   - `DISP=('MOD', None, None) existed=False -> effective=('MOD', 'DELETE', 'DELETE')` vs `existed=True -> effective=('MOD', 'KEEP', 'KEEP')`.
   - `DISP=('NEW', 'PASS', None) existed=False -> effective=('NEW', 'PASS', 'DELETE')` vs `DISP=('OLD', 'PASS', None) existed=True -> effective=('OLD', 'PASS', 'KEEP')`.
4. **DAX `CALCULATE` Duplicate-Row Amplification:**
   - Over `[{'Product':'Widget','Amount':100}, {'Product':'Widget','Amount':100}, {'Product':'Gadget','Amount':50}]`:
   - `SUMX(Sales, Sales[Amount]) = 250` vs `SUMX(Sales, CALCULATE(SUM(Sales[Amount]))) = 450` (`+200` / `+80%` amplification from matching both duplicate rows on each iteration).

## Revalidation

To cheaply verify whether these findings remain valid against newer upstream releases or when validating a live enterprise runtime:

1. **ReadStat / PSPP / abaplint / ooRexx source diff:** Diff the exact pinned paths against newer commits:
   - `WizardMac/ReadStat`: `src/sas/readstat_sas7bdat_read.c` (`sas_assign_tag` call) and `src/sas/readstat_sas.c` (`sas_assign_tag`).
   - `gnu-mirror-unofficial/pspp`: `src/data/val-type.h` (`SYSMIS`) and `src/data/caseinit.c` (`init_list_mark`).
   - `abaplint/abaplint`: `packages/core/src/rules/obsolete_statement.ts` (`getFix` for `Statements.Refresh`—check whether it now guards on `TableType.isWithHeader()`).
   - `ooRexx/oorexx`: `interpreter/classes/StemClass.cpp` (`evaluateCompoundVariableValue`) and `interpreter/expression/ExpressionVariable.cpp` (`getValue`).
2. **Live runtime discriminating probes (when proprietary/native runtimes are available):**
   - **SAS:** Run `data _null_; x = .A; put (x < 50)= x hex16.; run;` to confirm `1` and `FFFFFD0000000000` (on big-endian / `HEX16.` display; check byte order on x86-64).
   - **SAP ABAP:** In a test report, append a row to a global internal table `gt_mem`, execute `INSERT ztest ...` followed by `ROLLBACK WORK`, and assert `lines( gt_mem ) = 1` while `SELECT COUNT(*)` from `ztest` is `0`.
   - **IBM z/OS JCL:** Run a 2-step job with `STEP1` returning `RC=4` and `STEP2 EXEC PGM=IEFBR14,COND=(4,LT)` vs `COND=(0,NE)` to confirm `STEP2` executes under `(4,LT)` and is flushed (`IEF202I`) under `(0,NE)`.
   - **ooRexx:** Run `rexx -e 'signal on novalue; a. = 0; a.x = 1; drop a.x; say a.y; say a.x; exit; novalue: say "NOVALUE:" condition("D")'`—confirm `a.y` prints `0` while `a.x` jumps to `NOVALUE: A.X`.
   - **Excel 365:** Enter `="2">10` (confirm `TRUE`) and `=SEQUENCE(3)` in `A1` with literal `99` in `A2` (confirm `#SPILL!` in `A1`, `99` in `A2`, `#SPILL!` in `=SUM(A1#)`).
   - **DAX (Power BI / Tabular):** Construct the 3-row keyless `Sales` table above and evaluate `EVALUATE ROW("RowCtx", SUMX(Sales, Sales[Amount]), "CtxTrans", SUMX(Sales, CALCULATE(SUM(Sales[Amount]))))` to confirm `250` vs `450`.
