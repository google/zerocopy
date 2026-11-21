<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Design examples

These examples illustrate decisions, not a required architecture or code template.

## A variant carries its own evidence

A representation with `sent: boolean`, `receipt?: string`, and `timedOut: boolean`
admits combinations such as “sent, but no receipt” and leaves the relationship
between timeout and delivery to every caller. The following synthetic contract
instead distinguishes a pending request, confirmed delivery, and an uncertain
outcome. An uncertain outcome calls for reconciliation, not an automatic resend.

The nonempty-text factory preserves validated information. The closed union makes
an added outcome visible at the decision point. Returning an action as data keeps
this decision independent of network effects.

```typescript
export type Result<T> =
  | { readonly kind: "ok"; readonly value: T }
  | { readonly kind: "invalid"; readonly reason: string };

export class NonEmptyText {
  readonly #value: string;

  private constructor(value: string) {
    this.#value = value;
  }

  static parse(input: unknown): Result<NonEmptyText> {
    if (typeof input !== "string" || input.length === 0) {
      return { kind: "invalid", reason: "Expected a nonempty string" };
    }
    return { kind: "ok", value: new NonEmptyText(input) };
  }

  get value(): string {
    return this.#value;
  }
}

export type Delivery =
  | {
      readonly kind: "pending";
      readonly operationId: NonEmptyText;
      readonly body: NonEmptyText;
    }
  | { readonly kind: "confirmed"; readonly receipt: NonEmptyText }
  | { readonly kind: "uncertain"; readonly operationId: NonEmptyText };

export type Action =
  | {
      readonly kind: "send";
      readonly operationId: NonEmptyText;
      readonly body: NonEmptyText;
    }
  | { readonly kind: "complete"; readonly receipt: NonEmptyText }
  | { readonly kind: "reconcile"; readonly operationId: NonEmptyText };

function assertNever(value: never): never {
  throw new Error("Unhandled delivery state");
}

export function nextAction(delivery: Delivery): Action {
  switch (delivery.kind) {
    case "pending":
      return {
        kind: "send",
        operationId: delivery.operationId,
        body: delivery.body,
      };
    case "confirmed":
      return { kind: "complete", receipt: delivery.receipt };
    case "uncertain":
      return { kind: "reconcile", operationId: delivery.operationId };
    default:
      return assertNever(delivery);
  }
}
```

The text contract deliberately accepts whitespace and preserves input exactly; it
is not an email, identifier, or authorization validator. Stronger domain rules
would need their own checked boundary. TypeScript's static restrictions do not
protect against arbitrary JavaScript, `any`, unchecked assertions, or reflection.
Validate untrusted data at runtime instead of casting it to `Delivery`.

This is not a complete sending protocol. `nextAction` is pure and can be called
repeatedly; it neither consumes the request nor grants one-time permission to send.
The effect owner must implement the required atomic transition, operation identity,
reconciliation, and deduplication. Returning an action does not make execution
atomic or exactly once. Immutability here protects these scalar wrappers and
well-typed uses, not arbitrary future object graphs.

**Extension probe:** add a `cancelled` variant to `Delivery`. The exhaustiveness
check should fail until the policy explicitly handles it. A correct cancellation
policy must be supplied by the task; “return complete” is not automatically valid.
An intentionally open wire protocol instead needs a specified unknown-case policy.

## Typestate is about available operations

For an exclusively owned local resource in Rust, an API might expose
`Draft::validate(self) -> Result<Ready, ValidationError>` and
`Ready::finish(self) -> Finished`. Private fields constrain construction, and
consuming `self` prevents reuse of that particular value. The error type must
preserve the original value when retry or recovery requires it. Whether cloning,
aliasing, or another factory defeats the intended guarantee is part of the API
review. These signatures are illustrative, not a compiled Rust fixture.

A remote connection is different: `Connection<Ready>` cannot prove that the peer
has not disconnected. Operations still return failures. A single runtime enum may
also be clearer for dynamic protocol state, collections of mixed-state objects,
or a system in which several actors can change state independently.

## Functional style is not a syntax quota

A bounded loop that builds a private result can be a pure function from the
caller's perspective. Keep it when it makes ordering, early exit, or resource use
clearer than a fold. Conversely, a chain of `map` calls that mutates a shared cache
has not made the cache invariant local. Judge visible dependencies and effects,
not the absence of `for` or `mut`.

Do not replace each implementation detail with an abstraction. A named domain
operation can remove a coordination obligation; a generic pipeline with several
callbacks can add one. Prefer the design a maintainer can extend while seeing the
relevant invariant and failure behavior in a small, coherent region.
