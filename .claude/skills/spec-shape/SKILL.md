---
name: spec-shape
description: Defines the Cert-Yjs rules for WP specs, representation predicates and invariants, and the fresh-context review of a spec diff before push. Use when writing or changing a WP spec, a representation predicate, an invariant, or a definition in model.v / value.v / heap.v; when a proof needs a new condition and a conjunct is about to be added; when defining a new own_X / is_X; and before pushing any such change.
---

# Spec shape

## Rules

These are the project's rules for specs. Here a spec is the WP
specification of a Go function or method. The definition of a predicate is
not a spec: it is where the fields and the heap of a value are described.
Code comments cite the rules by bullet title
(`spec-shape "Values of Cert-Yjs types appear in specs through their predicates"`).

- **Values of Cert-Yjs types appear in specs through their predicates.** To
  mention a value of a Go type `X` defined in Cert-Yjs, a spec uses a
  predicate of `X`, never the value's fields. The representation predicate
  of `X`, `own_X` (or `is_X`), relates the value to a model of it and
  states the invariant of `X`. `own_X` is ownership of the value,
  `dfrac`-parameterized when the value is plain heap state, not guarded by
  a lock or an invariant (`own_ytype`, `own_delta`); `is_X` is persistent,
  duplicable knowledge about it (`is_Doc`, `is_Text`), monotone where the
  model only grows (`is_Text`'s grow-only `L`). A value held inside another
  value may appear through the holder's predicate instead, as the store's
  nodes appear in the store's predicate.
- **Public and non-public predicates.** `own_X` / `is_X` is public: `own_X`
  holds every resource of the value, all its fields and what they own,
  together with the invariant of `X`, and `is_X` covers the same resources
  persistently or through the lock or invariant that guards them. A
  non-public predicate of `X` owns or persistently covers some but not all
  of those resources, or describes a state in which the invariant of `X`
  need not hold; a fraction of `own_X` still covers every resource and is
  public. New non-public predicates are named `own_X_…` / `is_X_…`, but
  whether a predicate is public depends on what it describes, not on its
  name: any predicate that is not non-public is public. `is_history_lb`,
  persistent knowledge of a lower bound on a client's operation history,
  covers no part of a value's resources and is public.
- **Public and private functions.** A function or method is private to a
  type `X` when it is unexported and called only from within the
  implementation of `X`, that is, from the methods of `X` and from other
  functions private to `X`. Every other function is public for `X`: every
  exported one, and an unexported one as soon as code outside the
  implementation of `X` calls it. This is finer than Go's export, under
  which every unexported function would count as private.
- **Specs of public functions use only public predicates.** The spec of a
  function public for `X` mentions values of `X` only through public
  predicates. It takes each `own_X` / `is_X` it needs, its receiver's
  included, as that one predicate (at any fraction), never as a selection
  of its parts, and whatever `own_X` it returns, it returns whole:
  re-establishing the invariant of `X` is that function's job, not its
  caller's. Non-public predicates of `X` appear only in the specs of
  functions private to `X`. A value that appears through its holder's
  predicate (first bullet) counts as part of the holder for this rule, so
  a function private to the store may show the store's nodes through a
  non-public predicate of the store.
- **Everything a spec says about a value goes through a model parameter**,
  the return value included (`RET #(f m)` or `⌜ret = f m⌝`). Forbidden in a
  spec: struct field points-tos (`s .[store, "items"] ↦ …`), raw slices or
  maps of internal records, goose struct values and their fields
  (`yjs.item.t`, `itemVal.(left')`, `idv.(clock')`), flag bytes (`W8 2`),
  and `w64` / `uint.Z` arithmetic for a condition that a model predicate
  already states (state it with that predicate, such as `cell_covers` or
  `cell_fits`).
- **Specs stay intuitive.** The developer's idea of a function is a few
  sentences, so its spec is a few conjuncts, never ten. Conditions are
  grouped by the data structure or semantic unit they are about into one
  named predicate (`pool_invs`, `doc_registry_coh`, `cell_covers`), not
  listed as separate conjuncts.
- **A new conjunct goes into an existing predicate, or the PR says why
  not.** When a spec or a predicate gains a conjunct, first consider
  whether its condition fits naturally into the predicate of an existing
  conjunct. If it does not, the PR description says so for that conjunct,
  with the reason. Reviews check every new conjunct against this rule.
- **No over-specification.** A postcondition states each condition once
  (not `setintegrate input arr = Some arr'` next to its unfolding
  `arr' = take midx arr ++ …`) and states only what the function means. A
  condition that follows from the others, or that a caller merely finds
  convenient, is a lemma over the model or the predicates in the layer
  file that defines them (`model.v`, `value.v` or `heap.v`), not a
  conjunct.
- **One spec per function.** A second spec exists only if it is used and
  cannot be derived from the first. Specs that are unused, or that are a
  stepping stone of one proof, are deleted or made `#[local]` in that
  proof's file.
- **Reuse the Rocq-Yjs model, don't invent independent proofs.** State WP
  specs as refinements of the pure model and compose with its lemmas
  (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
  `integrate_commutative`, `yjs_strong_convergence`). Extract algorithmic
  cores into their own Go functions (`scanConflicts`, `findIntegrationLeft`)
  so hard loops are provable in isolation.

## Fresh-context review before push

The session that wrote the proof is biased toward the conjuncts it added.
Before pushing a change to a spec, predicate or invariant, launch a
subagent (Agent tool, general-purpose) that starts without this session's
context, and give it the diff, the PR description (the open PR's body, or
its draft when the PR is not open yet), these rules and the headers of the
layer files that define the predicates the diff uses, with a prompt like:

> Review the spec shape of `git diff origin/main...HEAD -- src/proof`
> in the Cert-Yjs repository, against the pull request description pasted
> after this prompt. The criteria are every bullet of the "Rules" section of
> `.claude/skills/spec-shape/SKILL.md`; read it first, then the headers of
> the `model.v` / `value.v` / `heap.v` files that define the predicates the
> diff uses or changes, including files the diff does not touch. Decide
> whether each function whose spec the diff touches is public or private
> for its types from its call sites in the Go code. Report each violation
> with file:line, the rule's bullet title, and a concrete proposal. Look
> hardest for: (a) a conjunct added to a spec or predicate whose condition
> fits naturally into the predicate of an existing conjunct (name the
> predicate), or a new conjunct whose reason for not fitting is missing
> from the PR description; (b) two or more conjuncts about one data
> structure or semantic unit that should be one named predicate (propose
> the name); (c) a condition stated twice in a postcondition, or derivable
> from its other conjuncts. Do not report proof-script style. If nothing
> qualifies, say so.

Fix each finding that breaks a rule. Where you judge that a finding does not
break the rule it cites, say why in the PR's "Specs and invariants" section.
A reviewer asked for gaps usually reports some; a finding that cites no rule
needs neither a fix nor a note.
