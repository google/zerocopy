//! Bodies with unstructured control-flow, i.e. with a control-flow graph and GOTOs.
//!
//! In effect, this is a cleaned up version of MIR.
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::{EnumAsGetters, EnumIsA, VariantName};
use rustc_hash::FxHashMap as HashMap;
use serde_state::{DeserializeState, SerializeState};
use smallvec::{SmallVec, smallvec};
use std::mem;
use std::ops::{Index, IndexMut};

use crate::ast::*;

// Block identifier. Similar to rust's `BasicBlock`.
generate_index_type!(BlockId, "Block");

// The entry block of a function is always the block with id 0
pub static START_BLOCK_ID: BlockId = BlockId::ZERO;

#[cfg_attr(feature = "charon_on_charon", charon::rename("Blocks"))]
pub type BodyContents = IndexVec<BlockId, BlockData>;
pub type ExprBody = GExprBody<BodyContents>;

/// A "basic block", which contains a linear sequence of statements, followed by a terminator, which
/// is where non-linear control-flow happens.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("Block"))]
pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

/// A statement.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
    /// Comments that precede this statement.
    // This is filled in a late pass after all the control-flow manipulation.
    pub comments_before: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(EnumIsA, EnumAsGetters, VariantName)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    /// A call. For now, we don't support dynamic calls (i.e. to a function pointer in memory).
    SetDiscriminant(Place, VariantId),
    /// Indicates that this local should be allocated; if it is already allocated, this frees
    /// the local and re-allocates it. The arguments do not receive a `StorageLive`. We ensure in
    /// the micro-pass `insert_storage_statements` that all other locals have a `StorageLive`
    /// associated with them.
    StorageLive(LocalId),
    /// Deallocates the given local; if it is already deallocated, this is
    /// a no-op. Not all local deallocations are explicit: if a non-return local is still live at
    /// function end (return or unwind), it is implicitly deallocated.
    /// If `--deallocate-all-locals` is set, all local deallocations are made explicit.
    StorageDead(LocalId),
    /// A place is mentioned, but not accessed. The place itself must still be valid though, so
    /// this statement is not a no-op: it can trigger UB if the place's projections are not valid
    /// (e.g. because they go out of bounds).
    PlaceMention(Place),
    /// Statements that only affect borrow-checking.
    Borrowck(BorrowckStatement),
    /// A non-diverging runtime check for a condition. This can be either:
    /// - Emitted for inlined "assumes" (which cause UB on failure)
    /// - Reconstructed from `if b { panic() }` if `--reconstruct-asserts` is set.
    ///
    /// This statement comes with the effect that happens when the check fails
    /// (rather than representing it as an unwinding edge).
    Assert {
        assert: Assert,
        on_failure: AbortKind,
    },
    /// Does nothing. Useful for passes.
    Nop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub enum TerminatorKind {
    Goto {
        target: BlockId,
    },
    Switch {
        data: SwitchData,
        branches: IndexVec<BranchId, BlockId>,
    },
    Call {
        call: Call,
        target: BlockId,
        on_unwind: BlockId,
    },
    /// Drop the value at the given place.
    ///
    /// Depending on `DropKind`, this may be a real call to `drop_glue`, or a conditional call
    /// that should only happen if the place has not been moved out of. See the docs of `DropKind`
    /// for more details; to get precise drops use `--precise-drops`.
    Drop {
        kind: DropKind,
        place: Place,
        /// Reference to the `drop_glue` code to call on drop.
        fn_ptr: FnPtr,
        target: BlockId,
        on_unwind: BlockId,
    },
    /// Assert that the given condition holds, and if not, unwind to the given block. This is used for
    /// bounds checks, overflow checks, etc.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TAssert"))]
    Assert {
        assert: Assert,
        target: BlockId,
        on_unwind: BlockId,
    },
    /// An inline assembly block. For now we only preserve the template string.
    InlineAsm {
        asm: String,
        targets: Vec<BlockId>,
        on_unwind: BlockId,
    },
    /// Handles panics and impossible cases.
    Abort(AbortKind),
    Return,
    /// Unwind out of the current function into its caller.
    UnwindResume,
}

/// A terminator: instruction to execute at the end of a block, which may jump to other blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Terminator {
    pub span: Span,
    pub kind: TerminatorKind,
    /// Comments that precede this terminator.
    // This is filled in a late pass after all the control-flow manipulation.
    pub comments_before: Vec<String>,
}

impl ExprBody {
    /// Returns a map from blocks in this body to their abort kind, if they correspond to an
    /// abort block (ie. a block with only bookkeeping statements and a
    /// [TerminatorKind::Abort] terminator).
    pub fn as_abort_map(&self) -> HashMap<BlockId, AbortKind> {
        self.body
            .iter_enumerated()
            .filter_map(|(bid, block)| block.as_abort().map(|abort| (bid, abort)))
            .collect()
    }

    pub fn transform_sequences_fwd<F>(&mut self, mut f: F)
    where
        F: FnMut(BlockId, &mut Locals, &mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        for (id, block) in &mut self.body.iter_mut_enumerated() {
            block.transform_sequences_fwd(|seq| f(id, &mut self.locals, seq));
        }
    }

    pub fn transform_sequences_bwd<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Locals, &mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        for block in &mut self.body {
            block.transform_sequences_bwd(|seq| f(&mut self.locals, seq));
        }
    }

    /// Apply a function to all the block ids in this body, i.e. the targets of its terminators.
    pub fn visit_block_ids_mut<F: FnMut(&mut BlockId)>(&mut self, mut f: F) {
        for block in &mut self.body {
            block.terminator.targets_mut().into_iter().for_each(&mut f);
        }
    }

    /// Apply a function to all the statements, in a bottom-up manner.
    pub fn visit_statements<F: FnMut(&mut Statement)>(&mut self, mut f: F) {
        for block in self.body.iter_mut().rev() {
            for st in block.statements.iter_mut().rev() {
                f(st);
            }
        }
    }
}

impl BlockData {
    /// Build a block that's just a goto terminator.
    pub fn new_goto(span: Span, target: BlockId) -> Self {
        BlockData {
            statements: vec![],
            terminator: Terminator::goto(span, target),
        }
    }
    pub fn as_goto(&self) -> Option<BlockId> {
        if let TerminatorKind::Goto { target } = self.terminator.kind {
            Some(target)
        } else {
            None
        }
    }
    pub fn as_trivial_goto(&self) -> Option<BlockId> {
        self.as_goto().filter(|_| {
            self.statements
                .iter()
                .all(|st| matches!(st.kind, StatementKind::Nop))
        })
    }

    pub fn as_abort(&self) -> Option<AbortKind> {
        if self.statements.iter().all(|st| {
            matches!(
                st.kind,
                StatementKind::Nop | StatementKind::StorageLive(_) | StatementKind::StorageDead(_)
            )
        }) && let TerminatorKind::Abort(abort) = &self.terminator.kind
        {
            Some(abort.clone())
        } else {
            None
        }
    }

    /// Build a block that's UB to reach.
    pub fn new_unreachable() -> Self {
        Terminator::new(
            Span::dummy(),
            TerminatorKind::Abort(AbortKind::UndefinedBehavior),
        )
        .into_block()
    }

    pub fn targets(&self) -> SmallVec<[BlockId; 2]> {
        self.terminator.targets()
    }
    pub fn targets_ignoring_unwind(&self) -> SmallVec<[BlockId; 2]> {
        self.terminator.targets_ignoring_unwind()
    }

    /// Apply a transformer to all the statements.
    ///
    /// The transformer should:
    /// - mutate the current statement in place
    /// - return the sequence of statements to introduce before the current statement
    pub fn transform<F: FnMut(&mut Statement) -> Vec<Statement>>(&mut self, mut f: F) {
        self.transform_sequences_fwd(|slice| {
            let new_statements = f(&mut slice[0]);
            if new_statements.is_empty() {
                vec![]
            } else {
                vec![(0, new_statements)]
            }
        });
    }

    /// Helper, see `transform_sequences_fwd` and `transform_sequences_bwd`.
    fn transform_sequences<F>(&mut self, mut f: F, forward: bool)
    where
        F: FnMut(&mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        let mut to_insert = vec![];
        let mut final_len = self.statements.len();
        if forward {
            for i in 0..self.statements.len() {
                let new_to_insert = f(&mut self.statements[i..]);
                to_insert.extend(new_to_insert.into_iter().map(|(j, stmts)| {
                    final_len += stmts.len();
                    (i + j, stmts)
                }));
            }
        } else {
            for i in (0..self.statements.len()).rev() {
                let new_to_insert = f(&mut self.statements[i..]);
                to_insert.extend(new_to_insert.into_iter().map(|(j, stmts)| {
                    final_len += stmts.len();
                    (i + j, stmts)
                }));
            }
        }
        if !to_insert.is_empty() {
            to_insert.sort_by_key(|(i, _)| *i);
            // Make it so the first element is always at the end so we can pop it.
            to_insert.reverse();
            // Construct the merged list of statements.
            let old_statements = mem::replace(&mut self.statements, Vec::with_capacity(final_len));
            for (i, stmt) in old_statements.into_iter().enumerate() {
                while let Some((j, _)) = to_insert.last()
                    && *j == i
                {
                    let (_, mut stmts) = to_insert.pop().unwrap();
                    self.statements.append(&mut stmts);
                }
                self.statements.push(stmt);
            }
        }
    }

    /// Apply a transformer to all the statements.
    ///
    /// The transformer should:
    /// - mutate the current statements in place
    /// - return a list of `(i, statements)` where `statements` will be inserted before index `i`.
    pub fn transform_sequences_fwd<F>(&mut self, f: F)
    where
        F: FnMut(&mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        self.transform_sequences(f, true);
    }

    /// Apply a transformer to all the statements.
    ///
    /// The transformer should:
    /// - mutate the current statements in place
    /// - return a list of `(i, statements)` where `statements` will be inserted before index `i`.
    pub fn transform_sequences_bwd<F>(&mut self, f: F)
    where
        F: FnMut(&mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        self.transform_sequences(f, false);
    }
}

impl Statement {
    pub fn new(span: Span, kind: StatementKind) -> Self {
        Statement {
            span,
            kind,
            comments_before: vec![],
        }
    }
}

impl Terminator {
    pub fn new(span: Span, kind: TerminatorKind) -> Self {
        Terminator {
            span,
            kind,
            comments_before: vec![],
        }
    }
    pub fn goto(span: Span, target: BlockId) -> Self {
        Self::new(span, TerminatorKind::Goto { target })
    }
    /// Whether this terminator is an unconditional error (panic).
    pub fn is_error(&self) -> bool {
        use TerminatorKind::*;
        match &self.kind {
            Abort(..) => true,
            Goto { .. }
            | Switch { .. }
            | InlineAsm { .. }
            | Return
            | Call { .. }
            | Drop { .. }
            | UnwindResume
            | Assert { .. } => false,
        }
    }

    pub fn into_block(self) -> BlockData {
        BlockData {
            statements: vec![],
            terminator: self,
        }
    }

    pub fn targets(&self) -> SmallVec<[BlockId; 2]> {
        match &self.kind {
            TerminatorKind::Goto { target } => {
                smallvec![*target]
            }
            TerminatorKind::Switch { branches, .. } => branches.iter().copied().collect(),
            TerminatorKind::InlineAsm {
                targets, on_unwind, ..
            } => targets.iter().copied().chain([*on_unwind]).collect(),
            TerminatorKind::Call {
                target, on_unwind, ..
            }
            | TerminatorKind::Drop {
                target, on_unwind, ..
            }
            | TerminatorKind::Assert {
                target, on_unwind, ..
            } => smallvec![*target, *on_unwind],
            TerminatorKind::Abort(..) | TerminatorKind::Return | TerminatorKind::UnwindResume => {
                smallvec![]
            }
        }
    }
    pub fn targets_mut(&mut self) -> SmallVec<[&mut BlockId; 2]> {
        match &mut self.kind {
            TerminatorKind::Goto { target } => {
                smallvec![target]
            }
            TerminatorKind::Switch { branches, .. } => branches.iter_mut().collect(),
            TerminatorKind::InlineAsm {
                targets, on_unwind, ..
            } => targets.iter_mut().chain([on_unwind]).collect(),
            TerminatorKind::Call {
                target, on_unwind, ..
            }
            | TerminatorKind::Drop {
                target, on_unwind, ..
            }
            | TerminatorKind::Assert {
                target, on_unwind, ..
            } => smallvec![target, on_unwind],
            TerminatorKind::Abort(..) | TerminatorKind::Return | TerminatorKind::UnwindResume => {
                smallvec![]
            }
        }
    }

    pub fn targets_ignoring_unwind(&self) -> SmallVec<[BlockId; 2]> {
        match &self.kind {
            TerminatorKind::Goto { target } => {
                smallvec![*target]
            }
            TerminatorKind::Switch { branches, .. } => branches.iter().copied().collect(),
            TerminatorKind::InlineAsm { targets, .. } => targets.iter().copied().collect(),
            TerminatorKind::Call { target, .. }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. } => {
                smallvec![*target]
            }
            TerminatorKind::Abort(..) | TerminatorKind::Return | TerminatorKind::UnwindResume => {
                smallvec![]
            }
        }
    }
}

impl TerminatorKind {
    /// Replace this terminator with a dummy.
    pub fn take(&mut self) -> Self {
        std::mem::replace(self, TerminatorKind::Abort(AbortKind::UndefinedBehavior))
    }
}

/// A statement location within a body.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct StmtLoc {
    pub block: BlockId,
    pub statement: usize,
}

impl StmtLoc {
    pub fn new(block: BlockId, statement: usize) -> Self {
        StmtLoc { block, statement }
    }

    pub fn block_start(block: BlockId) -> Self {
        StmtLoc {
            block,
            statement: 0,
        }
    }

    pub fn after(self) -> Self {
        StmtLoc {
            block: self.block,
            statement: self.statement + 1,
        }
    }
}

impl Index<StmtLoc> for ExprBody {
    type Output = Statement;
    fn index(&self, loc: StmtLoc) -> &Self::Output {
        &self.body[loc.block].statements[loc.statement]
    }
}

impl IndexMut<StmtLoc> for ExprBody {
    fn index_mut(&mut self, loc: StmtLoc) -> &mut Self::Output {
        &mut self.body[loc.block].statements[loc.statement]
    }
}

/// Helper to construct a small ullbc body.
pub struct BodyBuilder {
    /// The span to use for everything.
    pub span: Span,
    /// Body under construction.
    pub body: ExprBody,
    /// Block onto which we're adding statements. Its terminator is always `Return`.
    pub current_block: BlockId,
    /// Block to unwind to; created on demand.
    pub unwind_block: Option<BlockId>,
}

fn mk_block(span: Span, term: TerminatorKind) -> BlockData {
    BlockData {
        statements: vec![],
        terminator: Terminator::new(span, term),
    }
}

impl BodyBuilder {
    pub fn new(span: Span, arg_count: usize) -> Self {
        let mut body: ExprBody = GExprBody {
            span,
            locals: Locals::new(arg_count),
            bound_body_regions: 0,
            body: IndexVec::new(),
            comments: vec![],
        };
        let current_block = body.body.push(BlockData {
            statements: Default::default(),
            terminator: Terminator::new(span, TerminatorKind::Return),
        });
        Self {
            span,
            body,
            current_block,
            unwind_block: None,
        }
    }

    /// Finalize the builder by returning the built body.
    pub fn build(mut self) -> ExprBody {
        // Replace erased regions with fresh ones.
        let mut freshener: IndexMap<RegionId, ()> = IndexMap::new();
        self.body.dyn_visit_mut(|r: &mut Region| {
            if r.is_erased() || r.is_body() {
                *r = Region::Body(freshener.push(()));
            }
        });
        self.body.bound_body_regions = freshener.slot_count();
        // Return the built body.
        self.body
    }

    /// Create a new local. Adds a `StorageLive` statement if the local is not one of the special
    /// ones (return or function argument).
    pub fn new_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        let place = self.body.locals.new_var(name, ty);
        let local_id = place.as_local().unwrap();
        if !self.body.locals.is_return_or_arg(local_id) {
            self.push_statement(StatementKind::StorageLive(local_id));
        }
        place
    }

    /// Helper.
    fn current_block(&mut self) -> &mut BlockData {
        &mut self.body.body[self.current_block]
    }

    pub fn push_statement(&mut self, kind: StatementKind) {
        let st = Statement::new(self.span, kind);
        self.current_block().statements.push(st);
    }

    fn unwind_block(&mut self) -> BlockId {
        *self.unwind_block.get_or_insert_with(|| {
            self.body
                .body
                .push(mk_block(self.span, TerminatorKind::UnwindResume))
        })
    }

    pub fn call(&mut self, call: Call) {
        let next_block = self
            .body
            .body
            .push(mk_block(self.span, TerminatorKind::Return));
        let term = TerminatorKind::Call {
            target: next_block,
            call,
            on_unwind: self.unwind_block(),
        };
        self.current_block().terminator.kind = term;
        self.current_block = next_block;
    }

    pub fn insert_drop(&mut self, place: Place, fn_ptr: FnPtr) {
        let next_block = self
            .body
            .body
            .push(mk_block(self.span, TerminatorKind::Return));
        let term = TerminatorKind::Drop {
            kind: DropKind::Precise,
            place,
            fn_ptr,
            target: next_block,
            on_unwind: self.unwind_block(),
        };
        self.current_block().terminator.kind = term;
        self.current_block = next_block;
    }
}
