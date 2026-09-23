---
name: pr-description
description: Write or rewrite a cert-yjs pull request description, and run the spec-shape check before the PR is opened. Use before every `gh pr create`, and whenever a PR body is written, updated, or reviewed for readiness.
---

# Writing a cert-yjs PR description

The description is what the review, and the history a year later, reads
first. The diff is the evidence for it, not a prerequisite to it.

## Shape

Four sections, in this order:

- `## What`: each change, told as what is there today, what the PR makes
  of it, and why.
- `## Why`: the problem or goal the PR as a whole serves.
- `## How`: how the change is carried out, where that is not obvious from
  the What.
- `## Specs and invariants`: every WP spec, representation predicate and
  invariant the PR changes, each with before, after and why (see the check
  below). A PR that changes none says `None.` with one sentence on why.
  A `gh pr create` hook blocks a body without this heading.

Then the three-way difference and unrequested-change reports that CLAUDE.md
(Reporting) asks for, when there are any.

## Writing rules

- Written for a reader who has not opened the diff. A reader of the body
  alone knows what changed, why, what it does to specs and invariants, where
  it diverges from the references, and what it touched outside its scope.
- Every project term gets its meaning at first use: which file, predicate or
  line it is. Never "the Require order" or "the C2 relation" without context.
- Never only the delta: first the current state, in enough words for a
  reader who never saw it, then the change, then the reason.
- Full sentences. No telegraphic noun phrases, no semicolon chains. A table
  is an index of the prose, not a substitute for it.
- No plan section number, memo, chat or milestone letter as the sole
  explanation of anything. Say the thing.
- Never a per-commit changelog. Keep one body per PR and rewrite it in
  place as the branch grows.
- Length is not a cost; missing context is.

## The spec-shape check (run it before opening the PR)

A proof in progress adds whatever closes the current goal; grouping the
result into the shapes of CLAUDE.md "Specs and invariants" is a separate
act, done by the author before review. For the diff against the base
branch:

1. **Each conjunct added to a spec or to a predicate.** Write down the
   existing predicate it was tried in and why it does not belong there.
   When that sentence cannot be written, it belongs there: move it. When
   the new fact and its neighbours are one meaning (several loose clauses
   about one thing), make them one named predicate.
2. **Each new `own_X` / `is_X`.** Write down the part of the heap its
   argument names: the reference of what it owns (a predicate about one
   field takes that field's reference), never the address of the struct
   around it. Write down the meaning its name carries; if the name does
   not carry it, rename, or give the comment both the meaning and the use
   sites.
3. **Each postcondition.** Every fact stated once, no fact derivable from
   the others, a few conjuncts, not ten.

The sentences from steps 1 and 2 go into `## Specs and invariants`, so the
reviewer sees the check was done and can dispute a specific answer.
