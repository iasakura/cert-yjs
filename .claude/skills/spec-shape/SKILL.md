---
name: spec-shape
description: The rules for cert-yjs WP specs, representation predicates and invariants, and the fresh-context review of a spec diff. Use before writing or changing a WP spec, a representation predicate, an invariant, or a definition in model.v / value.v / heap.v; whenever a proof needs a new fact and you are about to add a conjunct; when you define a new own_X / is_X; and before pushing any such change.
---

# Spec shape

## Rules

These are the project's rules for specifications. Code comments cite them by
bullet title (`spec-shape "Public specs use only public predicates"`).

- **`is_X` / `own_X`**: `is_X` is persistent, duplicable knowledge (`is_Store`,
  `is_Text`, `is_text_lb`, `is_origin_id`), monotone where the model only
  grows (`is_Text`'s grow-only `L`); `own_X` is ownership,
  `dfrac`-parameterized when it is plain heap state (`own_ytype`, `own_dll`,
  `own_item_map`; `own_fresh_item` is exclusive and consumed by Integrate).
- **Public / non-public predicates**: a non-public predicate describes a
  part of a value, or a state in which its type's invariant need not hold;
  new ones are named `own_X_…` / `is_X_…`. Every other predicate is public,
  among them each type's `own_X` / `is_X`, which describes a whole value
  with its invariant.
- **Public specs use only public predicates.** The specification of an
  exported function uses only public predicates, so an exported method
  takes its receiver's predicate whole, gives it back whole, and
  re-establishes the invariant itself. Non-public predicates appear only in
  specifications of unexported functions.
- **Everything a spec says about a value goes through a model parameter**,
  the return value included (`RET #(f m)` or `⌜ret = f m⌝`). Forbidden in a
  spec: struct field points-tos (`s .[store, "items"] ↦ …`), raw
  slices or maps of internal records, goose struct values and their fields
  (`yjs.item.t`, `itemVal.(left')`, `idv.(clock')`), flag bytes (`W8 2`), and
  `w64` / `uint.Z` arithmetic where the model already has the fact
  (`cell_covers`, `cell_fits`). Public predicates have the public model
  (`YjsItem` lists, `DocModel`, `gset YjsId`); store-internal helpers have the
  cell model (`item_cell` / `type_state`), and a node pointer appears only as
  the `ic_loc` / `node_loc` of a model cell.
- **Specs stay intuitive.** The developer's idea of a function is a few
  sentences, so its spec is a few conjuncts, never ten. Conditions are grouped
  by the data structure or semantic unit they are about into one named
  predicate (`pool_invs`, `doc_registry_coh`, `cell_covers`), not listed as
  loose clauses.
- **A new conjunct goes into an existing predicate, or the PR says why
  not.** When a spec or a predicate gains a conjunct, first consider
  whether its condition fits naturally into the predicate of an existing
  conjunct. If it does not, the PR description says so for that conjunct,
  with the reason. The review checks every new conjunct against this rule.
- **No over-specification.** A postcondition states each fact once (not
  `setintegrate input arr = Some arr'` next to its unfolding
  `arr' = take midx arr ++ …`) and states only what the function means. A fact
  that follows from the others, or that a caller merely finds convenient, is a
  lemma over the model or the predicates in the layer file, not a conjunct.
- **One spec per function.** A second spec exists only if it is used and cannot
  be derived from the first. Specs that are unused, or that are a stepping
  stone of one proof, are deleted or made `#[local]` in that proof's file:
  Integrate's stepping stone is folded into `wp_Store__Integrate`.
- **Reuse the rocq-yjs model, don't invent independent proofs.** State WP specs
  as refinements of the pure model and compose with its lemmas
  (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
  `integrate_commutative`, `yjs_strong_convergence`). Extract algorithmic cores
  into their own Go functions (`scanConflicts`, `findIntegrationLeft`) so hard
  loops are provable in isolation.

## Fresh-context review before push

The session that wrote the proof is biased toward the conjuncts it added.
Before pushing a change to a spec, predicate or invariant, launch a
subagent (Agent tool, general-purpose) that sees only the diff, the PR
description (the open PR's body, or its draft when the PR is not open yet)
and these criteria, with a prompt like:

> Review the specification shape of `git diff origin/main...HEAD -- src/proof`
> in the cert-yjs repository, against the pull request description pasted
> after this prompt. The criteria are every bullet of the "Rules"
> section of `.claude/skills/spec-shape/SKILL.md`; read it first, then the
> headers of the `model.v` / `value.v` / `heap.v` files the diff touches,
> since the existing predicates listed there are where a new fact should
> go. Report each violation with file:line, the rule's bullet title, and a
> concrete proposal. Look hardest for: (a) a conjunct added to a spec or
> predicate whose condition fits naturally into the predicate of an
> existing conjunct (name the predicate), or a new conjunct whose reason
> for not fitting is missing from the PR description;
> (b) two or more clauses about one data structure or semantic unit that
> should be one named predicate (propose the name); (c) a fact stated
> twice, or derivable from the other conjuncts. Do not report proof-script
> style. If nothing qualifies, say so.

Fix each finding, or record in the PR's "Specs and invariants" section why
it stands. A reviewer asked for gaps usually reports some; a finding that
breaks no rule is optional.
