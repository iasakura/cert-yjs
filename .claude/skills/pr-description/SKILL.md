---
name: pr-description
description: Write or rewrite a cert-yjs pull request description. Use before every `gh pr create`, and whenever a PR body is written, updated, or reviewed for readiness.
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
  invariant the PR changes, each with before, after and why. For each new
  conjunct, the existing predicate it was tried in and why it does not fit
  there; for each new `own_X` / `is_X`, what its argument owns and what its
  name means (the `spec-shape` skill produces these answers). A PR that
  changes none says `None.` with one sentence on why.

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
