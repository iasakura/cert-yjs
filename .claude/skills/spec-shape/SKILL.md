---
name: spec-shape
description: Keep cert-yjs specs, representation predicates and invariants in the shape CLAUDE.md "Specs and invariants" asks for. Use whenever a proof needs a new fact and you are about to add a conjunct to a WP spec, a predicate or an invariant, when you define a new own_X / is_X, and before pushing any change to a spec, predicate or invariant (the fresh-context review below).
---

# Spec shape: integrate before you add

A proof in progress adds whatever closes the current goal. That is how a
postcondition ends up with six loose clauses about one thing, or a
predicate over one field takes the address of the whole struct. The fix is
not a later cleanup: at the moment a fact is needed, find where it belongs.

## When a proof needs a new fact

1. **Say the fact in one sentence, naming the data structure or semantic
   unit it is about** ("the transaction record lists every id the delete
   sweep marked", not "`dom m' = dom m ∪ …`"). If you cannot name the unit,
   the fact is not understood yet.
2. **List the existing homes.** Read the header (the API lines at the top)
   of `heap.v` and `model.v` of each type the fact mentions, and the
   definition of the receiver's `own_X` / `is_X`. The candidates are the
   predicates about that unit (`pool_invs`, `doc_registry_coh`,
   `cell_covers`, the model's coherence relations).
3. **Try each candidate.** Adding the fact to an existing predicate is the
   default: the predicate's laws and its callers absorb it. It does not fit
   only for a reason you can write down: the predicate is about a different
   unit, or it is stated where this fact does not hold (say where). No
   written reason: it goes there.
4. **Neighbours that are one meaning become one predicate.** If the new
   fact joins other loose clauses about the same unit, define one named
   predicate for all of them in the layer file (`model.v` for pure facts,
   `heap.v` for resources) and state the spec with it.
5. **A new top-level conjunct is the last resort,** for a fact no
   predicate is about. Keep the reason from step 3; it goes into the PR's
   "Specs and invariants" section.

## When you define a new `own_X` / `is_X`

- Its argument is the reference of what it owns. A predicate about one
  field takes that field's reference, never the address of the struct
  around it.
- Its name carries its meaning. If it cannot, the comment above the
  definition gives both the meaning and the places it is used.
- It is the one predicate of its type: a method on `X` takes it whole.

## Before a postcondition is final

- Each fact once. `setintegrate input arr = Some arr'` and its unfolding are
  not both conjuncts.
- A fact derivable from the others, or one a caller merely finds
  convenient, is a lemma over the model or the predicates, not a conjunct.
- A few conjuncts, never ten.

## Fresh-context review before push

The session that wrote the proof is biased toward the conjuncts it added.
Before pushing a change to a spec, predicate or invariant, launch a
subagent (Agent tool, general-purpose) that sees only the diff and these
criteria, with a prompt like:

> Review the specification shape of `git diff origin/main...HEAD -- src/proof`
> in the cert-yjs repository. Read CLAUDE.md, section "Specs and
> invariants", and the headers of the `heap.v` / `model.v` files the diff
> touches. Report only these, each with file:line and a concrete proposal:
> (a) a conjunct added to a spec or predicate that belongs in an existing
> predicate (name the predicate); (b) two or more clauses about one data
> structure or semantic unit that should be one named predicate (propose
> the name); (c) a predicate whose argument is a struct address while it
> owns or describes only one field; (d) a new predicate whose name does not
> carry its meaning and whose comment does not give meaning and use sites;
> (e) a fact stated twice, or derivable from the other conjuncts. Do not
> report style, proof-script, or naming issues outside (d). If nothing
> qualifies, say so.

Fix each finding, or record in the PR's "Specs and invariants" section why
it stands. A reviewer asked for gaps usually reports some; a finding that
does not fall under (a) to (e) is optional.
