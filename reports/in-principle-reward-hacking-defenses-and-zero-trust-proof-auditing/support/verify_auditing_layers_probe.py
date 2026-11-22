#!/usr/bin/env python3
"""Self-contained stdlib-only probe for six-layer zero-trust proof auditing.

Verifies four architectural invariants without external dependencies:
  1. Disjoint NDJSON comparator (5a/5b/5c) with pinned primitive cone,
     opaque-cone ban, Quotient post-check, and closed axiom allowlist.
  2. Out-of-band lock-root authority vs. self-attesting lock mutations (M1/M2).
  3. Closed-allowlist spec preflight + module-import & namespace-component
     checks vs. denylist escapes and Trojan macro imports.
  4. Automated guard-mutation auditing of the comparator's own policy checks.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Any


PERMITTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Union of nanoda_lib 34 hardcoded Init primitives + Lake Check.lean 27+4 targets
PINNED_PRIMITIVES = frozenset({
    "Nat", "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow",
    "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land",
    "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
    "String", "String.mk", "String.ofList", "Char", "Char.ofNat",
    "List", "List.nil", "List.cons", "Bool", "Bool.true", "Bool.false",
    "Eq", "Eq.refl", "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
    "eagerReduce", "optParam", "autoParam", "semiOutParam", "outParam",
})


@dataclass(frozen=True)
class Decl:
    name: str
    kind: str  # "def" | "thm" | "axiom" | "opaque" | "quot" | "ind"
    lparams: tuple[str, ...]
    ty: Any
    val: Any = None
    deps: tuple[str, ...] = ()
    is_unsafe: bool = False


def canonical_dag_hash(decl: Decl) -> str:
    payload = json.dumps(
        {
            "name": decl.name,
            "kind": decl.kind,
            "lparams": list(decl.lparams),
            "ty": decl.ty,
            "val": decl.val,
            "is_unsafe": decl.is_unsafe,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def verify_ndjson_comparator(
    expected_cone: dict[str, Decl],
    init_primitives: dict[str, Decl],
    proof_export: dict[str, Decl],
    theorem_name: str,
    claim_name: str,
    disabled_guard: str | None = None,
) -> tuple[bool, str]:
    """Pure structural NDJSON verifier modeling Action 5c (AnnealVerifyNdjson)."""
    # Guard G1: Canonical DAG identity of expected_cone in proof_export
    if disabled_guard != "G1_expected_dag":
        for name, exp_d in expected_cone.items():
            got = proof_export.get(name)
            if got is None or canonical_dag_hash(got) != canonical_dag_hash(exp_d):
                return False, f"reject:G1_expected_mismatch:{name}"

    # Guard G2: Pinned Init primitives cone (closes unused-primitive injection)
    if disabled_guard != "G2_init_primitives":
        for name, prim_d in init_primitives.items():
            got = proof_export.get(name)
            if got is None or canonical_dag_hash(got) != canonical_dag_hash(prim_d):
                return False, f"reject:G2_primitive_mismatch:{name}"

    # Guard G3: Theorem header exactness (thm, empty lparams, type == claim)
    thm = proof_export.get(theorem_name)
    if disabled_guard != "G3_theorem_header":
        if thm is None or thm.kind != "thm" or thm.lparams != () or thm.ty != ("const", claim_name):
            return False, f"reject:G3_theorem_header:{theorem_name}"

    # Walk transitive closure from theorem_name
    seen: set[str] = set()
    stack = [theorem_name]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        d = proof_export.get(cur)
        if d is None:
            return False, f"reject:missing_dep:{cur}"
        # Guard G4: Reject unsafe/partial declarations
        if disabled_guard != "G4_no_unsafe" and d.is_unsafe:
            return False, f"reject:G4_unsafe_decl:{cur}"
        # Guard G5: Reject opaque declarations in proof cone (CollectAxioms gap)
        if disabled_guard != "G5_no_opaque" and d.kind == "opaque":
            return False, f"reject:G5_opaque_decl:{cur}"
        # Guard G6: Closed positive axiom allowlist
        if disabled_guard != "G6_closed_axioms" and d.kind == "axiom":
            if cur not in PERMITTED_AXIOMS:
                return False, f"reject:G6_unpermitted_axiom:{cur}"
        # Guard G7: Quotient post-check against pinned primitives
        if disabled_guard != "G7_quot_postcheck" and d.kind == "quot":
            if cur not in init_primitives or canonical_dag_hash(d) != canonical_dag_hash(init_primitives[cur]):
                return False, f"reject:G7_forged_quot:{cur}"
        for dep in d.deps:
            if dep not in seen:
                stack.append(dep)

    return True, "ok:verified"


def probe_1_and_4_comparator_and_guard_mutation() -> None:
    expected_cone = {
        "Expected.claim": Decl("Expected.claim", "def", (), ("sort", 0), ("eq", "zero", 0), ()),
    }
    init_prims = {
        "Nat.gcd": Decl("Nat.gcd", "def", (), "Nat->Nat->Nat", "euclid_gcd", ()),
        "Quot.lift": Decl("Quot.lift", "quot", ("u", "v"), "quot_lift_ty", None, ()),
        "propext": Decl("propext", "axiom", (), "propext_ty", None, ()),
    }

    honest_export = {
        **expected_cone,
        **init_prims,
        "Proof.verify": Decl(
            "Proof.verify", "thm", (), ("const", "Expected.claim"), "rfl", ("Expected.claim", "propext")
        ),
    }

    exploits: dict[str, dict[str, Decl]] = {
        "E1_statement_tamper": {
            **honest_export,
            "Expected.claim": Decl("Expected.claim", "def", (), ("sort", 0), "True", ()),
        },
        "E2_unused_primitive_injection": {
            **honest_export,
            "Nat.gcd": Decl("Nat.gcd", "def", (), "Nat->Nat->Nat", "const_zero", ()),
        },
        "E3_universe_poly_theorem": {
            **honest_export,
            "Proof.verify": Decl(
                "Proof.verify", "thm", ("u",), ("const", "Expected.claim"), "rfl", ("Expected.claim",)
            ),
        },
        "E4_unsafe_helper": {
            **honest_export,
            "Proof.bad": Decl("Proof.bad", "def", (), "False", "loop", (), is_unsafe=True),
            "Proof.verify": Decl(
                "Proof.verify", "thm", (), ("const", "Expected.claim"), "elim", ("Expected.claim", "Proof.bad")
            ),
        },
        "E5_opaque_stub": {
            **honest_export,
            "Proof.stub": Decl("Proof.stub", "opaque", (), "Nat->Bool", "default_false", ()),
            "Proof.verify": Decl(
                "Proof.verify", "thm", (), ("const", "Expected.claim"), "pf", ("Expected.claim", "Proof.stub")
            ),
        },
        "E6_unpermitted_axiom": {
            **honest_export,
            "sorryAx": Decl("sorryAx", "axiom", ("u",), "forall_a", None, ()),
            "Proof.verify": Decl(
                "Proof.verify", "thm", (), ("const", "Expected.claim"), "sorry", ("Expected.claim", "sorryAx")
            ),
        },
        "E7_forged_quot": {
            **honest_export,
            "Quot.fake": Decl("Quot.fake", "quot", (), "False", None, ()),
            "Proof.verify": Decl(
                "Proof.verify", "thm", (), ("const", "Expected.claim"), "pf", ("Expected.claim", "Quot.fake")
            ),
        },
    }

    ok_h, msg_h = verify_ndjson_comparator(expected_cone, init_prims, honest_export, "Proof.verify", "Expected.claim")
    assert ok_h, f"honest failed: {msg_h}"

    rejected = 0
    for ename, exp in exploits.items():
        ok, msg = verify_ndjson_comparator(expected_cone, init_prims, exp, "Proof.verify", "Expected.claim")
        assert not ok, f"{ename} unexpectedly accepted!"
        rejected += 1
    print(f"[Probe 1] Comparator 5c: pinned_primitives={len(PINNED_PRIMITIVES)}, honest=ADMITTED, exploits_rejected={rejected}/{len(exploits)}")

    # Probe 4: Guard-Mutation Audit (disable 1 guard at a time; require 100% kill)
    guards = [
        "G1_expected_dag", "G2_init_primitives", "G3_theorem_header",
        "G4_no_unsafe", "G5_no_opaque", "G6_closed_axioms", "G7_quot_postcheck",
    ]
    killed = 0
    for g in guards:
        ok_mut_h, _ = verify_ndjson_comparator(
            expected_cone, init_prims, honest_export, "Proof.verify", "Expected.claim", disabled_guard=g
        )
        assert ok_mut_h, f"mutated guard {g} broke honest case"
        exposed_by = [
            ename for ename, exp in exploits.items()
            if verify_ndjson_comparator(expected_cone, init_prims, exp, "Proof.verify", "Expected.claim", disabled_guard=g)[0]
        ]
        assert exposed_by, f"guard {g} was NOT exposed by any exploit fixture!"
        killed += 1
    print(f"[Probe 4] Guard-Mutation Audit: exposed={killed}/{len(guards)} (100.0% load-bearing guards covered)")


def sha256_str(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def probe_2_out_of_band_lock() -> None:
    real_spec = "def spec (x : Nat) : Prop := x = 0"
    weak_spec = "def spec (x : Nat) : Prop := True"
    pinned_root = sha256_str(real_spec)

    # M1: Adversary with workspace write access edits both spec and workspace lockfile
    ws_lock_m1 = {"spec_sha256": sha256_str(weak_spec), "cached_axioms": []}
    naive_m1_pass = (sha256_str(weak_spec) == ws_lock_m1["spec_sha256"])
    oob_m1_pass = (sha256_str(weak_spec) == pinned_root)

    # M2: Adversary forges cached summary ("cached_axioms": []) in workspace lockfile
    actual_axioms = {"sorryAx"}
    naive_m2_pass = (set(ws_lock_m1["cached_axioms"]) <= PERMITTED_AXIOMS)
    oob_m2_pass = (actual_axioms <= PERMITTED_AXIOMS)  # 5c replays full closure, ignoring cached summaries

    assert naive_m1_pass and naive_m2_pass
    assert (not oob_m1_pass) and (not oob_m2_pass)
    print("[Probe 2] Lock Authority: naive_self_attesting_bypasses=2/2 (M1, M2), out_of_band_bypasses=0/2")


def probe_3_closed_allowlist_and_imports() -> None:
    denylist_terms = {"by_elab", "sorry", "native_decide"}
    allowlist_terms = {"ident", "num", "app", "forall", "eq", "and", "or", "not"}
    allowed_attrs = {"expose", "reducible", "inline", "simp"}
    role_allows = {
        "spec": {"init", "model", "captured", "spec"},
        "proof": {"init", "model", "captured", "spec", "expected", "theory", "proof"},
    }

    @dataclass
    class SpecSubmission:
        name: str
        terms: set[str]
        attrs: set[str]
        imports: list[tuple[str, str]]  # (mod_name, role)
        decl_names: list[str]

    attacks = [
        SpecSubmission("A1_denylist_escape_mod_cast", {"forall", "mod_cast"}, set(), [], ["Spec.ok"]),
        SpecSubmission("A2_forbidden_attr_app_delab", {"forall"}, {"app_delab"}, [], ["Spec.ok"]),
        SpecSubmission("A3_trojan_proof_macro_import", {"forall"}, set(), [("TrojanProof", "proof")], ["Spec.ok"]),
        SpecSubmission("A4_enclosing_ns_shadow", {"forall"}, set(), [], ["Proof.Trusted.CrateTheorem"]),
    ]

    naive_caught = 0
    hardened_caught = 0
    for a in attacks:
        if a.terms & denylist_terms:
            naive_caught += 1
        bad_term = not (a.terms <= allowlist_terms)
        bad_attr = not (a.attrs <= allowed_attrs)
        bad_imp = any(role not in role_allows["spec"] for _, role in a.imports)
        bad_ns = any("Trusted" in d.split(".") for d in a.decl_names)
        if bad_term or bad_attr or bad_imp or bad_ns:
            hardened_caught += 1

    assert naive_caught == 0 and hardened_caught == len(attacks)
    print(f"[Probe 3] Spec Preflight: denylist_caught={naive_caught}/{len(attacks)}, closed_allowlist+imports+ns_caught={hardened_caught}/{len(attacks)}")


if __name__ == "__main__":
    probe_1_and_4_comparator_and_guard_mutation()
    probe_2_out_of_band_lock()
    probe_3_closed_allowlist_and_imports()
    print("ALL_PROBES_PASSED")
