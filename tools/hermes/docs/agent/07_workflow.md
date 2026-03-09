# How to write a Hermes proof

This document contains advice on how to structure your thinking and workflow when writing Hermes proofs.

## Philosophy

Writing a Lean proof is not like other forms of software engineering. A Lean proof is *far* more brittle than a "normal" program. Starting with a complete draft and iterating **will not work**. You will never know whether you are going down blind alleys and spinning your wheels or making real progress. This approach will lead to frustration and wasted time, and likely won't produce a working proof.

## Workflow

The following is a workflow for solving [problem]. It is recursive – you will use this workflow to solve sub-problems as well.

1. Make sure you understand your goal, context, and constraints for [problem] *completely* and *precisely*.
  a. Spend as much time as you need *thinking* in order to come to this understanding.
  b. If there is any ambiguity whatsoever, ask for clarification.
  c. Repeat the process of clarification-asking and thinking until you have a *complete* and *precise* understanding of your goal, context, and constraints.
  d. Record this in as much details as you can in comments the file you are editing.
2. Once you understand the goal, context, and constraints for [problem], brainstorm a *complete* solution. Your solution must be *complete*, as the act of thinking through details may make you realize that you need to adjust your high-level plan.
  a. Spend as much time as it takes to think through your solution *completely* until you are confident that *every detail* is correct.
  b. Record this in as much details as you can in comments the file you are editing.
3. You are now ready to start writing code.
  a. Start with the specification (`requires` and `ensures` clauses).
  b. Get these working with the `verify` subcommand and the `--allow-sorry` flag, omitting any proofs.
  c. Iterate until everything verifies, implying that your specification is internally consistent. This does not necessarily mean that it's the *right* specification, only that Hermes understands it.
  d. Run the `expand` subcommand to see what Lean is generated, and make sure it looks like what you expect. This will help you when you start writing proofs.
4. Move on to the proof.
  a. First, break the proof down into lemmas. Spend as much time as you need thinking through the lemmas and how they fit together to prove the main proof.
  b. Write the *definitions* of each lemma, but do *not* prove them – leave their proofs as `sorry` for now.
5. Write the top-level proof, using the lemmas you defined in the previous step.
  a. Iterate until this proof verifies, using the `--allow-sorry` flag.
  b. If you get stuck *at all*, consider whether you need to re-visit a previous step or "pop up" one level of abstraction to reconsider your broader plan.
6. Once the top-level proof verifies, you can start proving the lemmas one by one. For each lemma, you will use *this entire workflow*, but applied to [sub-problem] instead of the top-level [problem].

Overall, your workflow will look like a recursive application of this entire workflow. Always be prepared to "pop up" one level of abstraction to reconsider your broader plan.

## Tips

When writing a proof, follow these tips:

1. Always *think deeply* before writing any code.
2. Question *all* assumptions.
3. Make liberal use of scratch `.lean` files to test out ideas.
4. The `expand` subcommand will print the generated Lean, and is *extremely* helpful in debugging.
5. If something isn't working, don't assume you know why. Instead, **STOP**. Move into debugging mode, producing a stand-alone experiment to confirm *all* your assumptions before continuing.
6. Specifications can have bugs too. Always consider whether a specification needs to be adjusted to match your understanding of the problem.
7. Proofs are more tractable when the proofs themselves and the code they model are broken down into small bits. If you are having trouble with a proof, consider breaking it further down into lemmas, or breaking the *code* that it models into smaller functions, types, etc.
8. Write extensive notes in code comments. Write notes to record your plans, what you've tried, what you've learned, what you still don't understand, etc.

## Specifics

You will use these two commands to interact with Hermes. Both accept `--help`.

1. Run `cargo run verify` to verify a target.
2. Use `cargo run expand` to see the generated Lean code.