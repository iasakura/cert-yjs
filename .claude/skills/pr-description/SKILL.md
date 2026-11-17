---
name: pr-description
description: Writes or rewrites a Cert-Yjs pull request description, with its four sections and its writing rules. Use before every `gh pr create`, and whenever a PR body is written, updated, or reviewed for readiness.
---

# Writing a Cert-Yjs PR description

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
  conjunct, the existing predicates its condition was considered for and
  why it does not fit naturally into any of them (`spec-shape`, "A new
  conjunct goes into an existing predicate, or the PR says why not"); for
  each new `own_X` / `is_X`, what its argument owns and what its name
  means. A PR that changes none says `None.` with one sentence on why.

Then the three-way difference and unrequested-change reports that CLAUDE.md
(Reporting) asks for, when there are any.

## Writing rules

A person reads the description, to decide what to review and whether to
approve. Write it as technical prose for that person.

- **Conclusion first, at every level.** The body opens, before `## What`,
  with two to four sentences that say what a user of the code can do now
  that they could not do before, and what the PR leaves out. Each section
  opens with its conclusion, and each paragraph with the sentence the rest
  of it supports. Background, mechanism and history come after the claim
  they explain, and only as much as the claim needs. Check: the first
  sentences alone, read in order, are a correct summary.
- **Short.** Cut what the reader does not need in order to review: how each
  helper works line by line, lemma names internal to a proof, the list of
  test cases, the history of how the design was reached. The diff has them.
- **Say where to look.** When the diff is large, a "Where to look" table
  right after the summary names the few places a review should read (the
  exported function, its spec, the trusted hypotheses) and says the rest is
  implementation or proof.
- **One paragraph, one point**, in a handful of short sentences. One idea
  per sentence, at most one parenthesis, no semicolon chains.
- **Parallel items go in a list or a table**, one per line, starting with
  the name: the functions added, the predicates changed (before and after),
  the hypotheses of a theorem, the differences between the references. A
  table cell holds a phrase or one sentence, not a paragraph.
- **Explain in words, then name.** State the idea in plain words and give
  the identifier after it, in backticks. A sentence made of identifiers is
  not an explanation. Every project term gets its meaning at first use.
- **No terms of the PR's own making.** A thing is called by the word the
  references use for it (Yjs: struct, item, state vector, delete set) or
  described in plain words. A name in the code is not such a word, even when
  the code has it as a type, a variable or a predicate: the name may appear
  in backticks, as the name of that thing and with what the thing is, but
  its words are not turned into prose vocabulary.
- **A reader who has not opened the diff can follow it.** For each change
  the reader learns what was there, what is there now, and why. No plan
  section number, memo, chat or milestone letter stands in for an
  explanation.
- Never a per-commit changelog. Keep one body per PR and rewrite it in
  place as the branch grows.

## One PR, one reviewable change

A PR holds one change a reviewer can judge by itself: an exported function
with its specification and proof, a change to an existing specification
with the proofs it touches, or a theorem. Do not cut one change by layer
(the Go in one PR, the definitions in the next, the proofs in a third): a PR
of unexported helpers with no caller and no specification gives the
reviewer nothing to decide.
