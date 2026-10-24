---
name: spec-shape
description: Defines the Cert-Yjs rules for WP specs, representation predicates and invariants, and the fresh-context review of a spec diff before push. Use when writing or changing a WP spec, a representation predicate, an invariant, or a definition in model.v / value.v / heap.v; when a proof needs a new condition and a conjunct is about to be added; when defining a new own_X / is_X; and before pushing any such change.
---

# Spec shape

## What each rule binds

Here a spec is the WP specification of a Go function or method. Changing one
touches four different objects, and every rule below binds the one its
subsection is named after. Where a rule binds something else as well, or
something narrower, it says so in its own first sentence. The four objects
are:

- **the statement of a spec**: the triple a caller reads, its precondition,
  its program expression and its postcondition. It is the contract, the only
  part of a verified function that a caller depends on.
- **the definition of a predicate**: where the fields and the heap of a value
  are described. The rules here reach an invariant, and a definition in
  `model.v`, `value.v` or `heap.v`, alike. A definition is not a spec.
- **which specs a file exports**: the specs a downstream file may `Require`,
  as against the stepping stones that stay inside one proof.
- **the proof and the Go code**: the script between `Proof.` and `Qed.`, which
  nothing outside the file can observe, and the Go function the spec is about.

A rule binds nothing beyond what its subsection and its first sentence
name. Publicity, as the rules use the word (a public or non-public predicate, a
function public or private for a type), is a property of an interface: the
vocabulary below settles it, by what a predicate describes and by a function's
call sites, and it constrains what a spec states. Inside a proof the ordinary
separation-logic freedom applies, so a proof may unfold, split, borrow, open
and recombine every resource it holds, non-public predicates of any type
included; a non-public predicate reaching the proof of a public function
violates nothing in this file.

## Vocabulary

These entries fix the terms the rules use. They classify and nothing more:
a rule below is what binds, and no entry here can be violated by itself.

- **Representation predicates `own_X` and `is_X`.** The representation
  predicate of a Go type `X` defined in Cert-Yjs, `own_X` (or `is_X`), relates
  a value of `X` to a model of it and states the invariant of `X`. `own_X` is
  ownership of the value, `dfrac`-parameterized when the value is plain heap
  state, not guarded by a lock or an invariant (`own_ytype`, `own_delta`);
  `is_X` is persistent, duplicable knowledge about it (`is_Doc`, `is_Text`),
  monotone where the model only grows (`is_Text`'s grow-only `L`).
- **Public and non-public predicates.** A non-public predicate of `X`
  describes a value of `X` in the place of `own_X` or `is_X`, but with some
  of the resources of the value (its fields and what they own, together with
  the invariant of `X`) left out, or in a state in which the invariant of `X`
  need not hold. Every other predicate is public: `own_X`, which holds every
  one of those resources; `is_X`, which covers the same resources
  persistently or through the lock or invariant that guards them; a fraction
  of `own_X`, which still covers every resource; the invariant of a lock of
  `X`, and a ghost token kept in that lock, which describe what the lock
  holds rather than a value of `X` in the place of `own_X` or `is_X`; and
  `is_history_lb`, persistent knowledge of a lower bound on a client's
  operation history, which covers no part of a value's resources at all.
  Whether a predicate is public depends on what it describes, not on its
  name.
- **Public and private functions.** This classifies the Go functions and
  methods of Cert-Yjs, by their call sites in the Go code. A function or
  method is private to a type `X` when it is unexported and called only from
  within the implementation of `X`, that is, from the methods of `X` and from
  other unexported functions that are themselves called only from there.
  Every other function is public for `X`: every exported one, and an
  unexported one as soon as code outside the implementation of `X` calls it.
  This is finer than Go's export, under which every unexported function would
  count as private.

## Rules

Cite a rule, or an entry of the vocabulary above, in a code comment by its
bullet title
(`spec-shape "Values of Cert-Yjs types appear in specs through their predicates"`).

### The statement of a spec

- **Values of Cert-Yjs types appear in specs through their predicates.** To
  mention a value of a Go type `X` defined in Cert-Yjs, use a predicate of
  `X`, never the value's fields. A value held inside another value may appear
  through the holder's predicate instead, as the store's nodes appear in the
  store's predicate.
- **Specs of public functions use only public predicates.** In the statement
  of a spec of a function public for `X`, mention values of `X` only through
  public predicates. Take each `own_X` / `is_X` the function needs, its
  receiver's included, as that one predicate (at any fraction), never as a
  selection of its parts, and return whatever `own_X` it returns whole:
  re-establishing the invariant of `X` is that function's job, not its
  caller's. Let a non-public predicate of `X` appear only in the statement of
  a spec of a function private to `X`. A value that appears through its
  holder's predicate (the rule above) counts as part of the holder for this
  rule, so a function private to the store may show the store's nodes through
  a non-public predicate of the store.
- **Everything a spec says about a value goes through a model parameter.**
  State the return value the same way (`RET #(f m)` or `⌜ret = f m⌝`). Keep
  out of a spec: struct field points-tos (`s .[store, "items"] ↦ …`), raw
  slices or maps of internal records, goose struct values and their fields
  (`yjs.item.t`, `itemVal.(left')`, `idv.(clock')`), flag bytes (`W8 2`), and
  `w64` / `uint.Z` arithmetic for a condition that a model predicate already
  states (state it with that predicate, such as `cell_covers` or `cell_fits`).
- **Specs stay intuitive.** This rule binds a spec's statement and the named
  predicates it groups conditions into. The developer's idea of a function is
  a few sentences, so keep its spec to a few conjuncts, never ten. Group
  conditions by the data structure or semantic unit they are about into one
  named predicate (`pool_invs`, `doc_registry_coh`, `cell_covers`) instead of
  listing them as separate conjuncts.
- **No over-specification.** This rule binds a postcondition and the layer
  file a condition it excludes goes to. State each condition once (not
  `setintegrate input arr = Some arr'` next to its unfolding `arr' = take midx
  arr ++ …`) and state only what the function means. Put a condition that
  follows from the others, including one a caller merely finds convenient in
  that form, in the layer file that defines the model or the predicates it is
  about (`model.v`, `value.v` or `heap.v`), as a lemma, not in the
  postcondition.

### The definition of a predicate

- **A new conjunct goes into an existing predicate, or the PR says why not.**
  This rule binds a predicate's definition and a spec's statement alike, and
  the PR description that reports them. When a spec or a predicate gains a
  conjunct, first consider whether its condition fits naturally into the
  predicate of an existing conjunct. If it does not, say so in the PR
  description for that conjunct, with the reason. Check every new conjunct
  against this rule in review.
- **New non-public predicates are named `own_X_…` / `is_X_…`.** This rule
  binds the name a new non-public predicate is given. Name it `own_X_…` or
  `is_X_…` so that the name marks it as one of `X`'s, and do not read
  publicity off a name: it follows from what the predicate describes
  (vocabulary, "Public and non-public predicates").

### Which specs a file exports

- **One spec per function.** Keep a second spec only if it is used and cannot
  be derived from the first. Delete a spec that is unused, and make a spec
  that is a stepping stone of one proof `#[local]` in that proof's file.

### The proof and the Go code

- **Reuse the Rocq-Yjs model, don't build on an independent one.** This rule
  reaches the statement the proof refines as well. State WP specs as
  refinements of the pure model and compose with lemmas about it
  (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
  `integrate_commutative`, `yjs_strong_convergence`), not with those of a
  model or an order theory of Cert-Yjs's own. Extract algorithmic cores into
  their own Go functions (`scanConflicts`, `findIntegrationLeft`) so hard
  loops are provable in isolation.

## Fresh-context review before push

The session that wrote the proof is biased toward the conjuncts it added.
Before pushing a change to a spec, predicate or invariant, launch a
subagent (Agent tool, general-purpose) that starts without this session's
context, and give it the diff, the PR description (the open PR's body, or
its draft when the PR is not open yet), these rules and the headers (the
comment block at the top of each file) of the layer files that define the
predicates the diff uses, with a prompt like:

> Review the spec shape of `git diff origin/main...HEAD -- src/proof`
> in the Cert-Yjs repository, against the pull request description pasted
> after this prompt. The criteria are every bullet under the "Rules" section
> of `.claude/skills/spec-shape/SKILL.md`, and only those: the skill's
> "Vocabulary" section defines the terms the rules use and is not itself a
> criterion. Read the skill first, and judge each rule against the object
> that its "What each rule binds" section and the rule's own first sentence
> assign to it. Then read the headers of the `model.v` / `value.v` /
> `heap.v` files that define the predicates the diff uses or changes,
> including files the diff does not touch.
> Decide whether each function whose spec the diff touches is public or
> private for its types from its call sites in the Go code. Report each
> violation with file:line, the rule's bullet title, and a concrete proposal.
> Look hardest for: (a) a conjunct added to a spec or predicate whose
> condition fits naturally into the predicate of an existing conjunct (name
> the predicate), or a new conjunct whose reason for not fitting is missing
> from the PR description; (b) two or more conjuncts about one data structure
> or semantic unit that should be one named predicate (propose the name); (c)
> a condition stated twice in a postcondition, or derivable from its other
> conjuncts. Do not report proof-script style. If nothing qualifies, say so.

Fix each finding that breaks a rule. Where you judge that a finding does not
break the rule it cites, say why in the PR's "Specs and invariants" section.
A reviewer asked for gaps usually reports some; a finding that cites no rule
needs neither a fix nor a note.
