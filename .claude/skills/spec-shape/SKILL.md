---
name: spec-shape
description: The rules for cert-yjs WP specs, representation predicates and invariants, and the fresh-context review of a spec diff. Use before writing or changing a WP spec, a representation predicate, an invariant, or a definition in model.v / value.v / heap.v; whenever a proof needs a new fact and you are about to add a conjunct; when you define a new own_X / is_X; and before pushing any such change.
---

# Spec shape

## Rules

These are the project's rules for specifications. Code comments cite them by
bullet title (`spec-shape "Public specs take the whole type"`).

- **`is_X` / `own_X`**: `is_X` is persistent, duplicable knowledge (`is_Store`,
  `is_Text`, `is_text_lb`, `is_origin_id`); `own_X` is ownership,
  `dfrac`-parameterized when it is plain heap state (`own_ytype`, `own_dll`,
  `own_item_map`; `own_fresh_item` is exclusive and consumed by Integrate).
- **A predicate's name must carry its meaning.** When it cannot, the comment
  above the definition owes the reader BOTH the meaning and the places it is
  used: a qualifier naming the proof step that produces or consumes it
  (`apply_live_refine`) is not self-explanatory. Restating the formula in prose
  adds nothing the `Definition` line does not say.
- **Spec shape, for every function, exported or not**:
  `{{{ own_X o dq m ∗ ⌜Pre m⌝ }}} … {{{ own_X o dq m' ∗ ⌜Post m m' ret⌝ }}}`,
  with persistent `is_X o m` handles as duplicable hypotheses carrying monotone
  knowledge (`is_Text`'s grow-only `L`). The return value is related to the
  model the same way (`RET #(f m)` or `⌜ret = f m⌝`). For an exported
  function `own_X` / `is_X` is a public predicate (the next bullet); for an
  unexported one it may be a non-public predicate (the bullet after).
- **Public specs take the whole type.** The public `own_X` / `is_X` of an
  exported Go type `X` describes a whole `X`, every field of it, and every
  public specification is stated over it: an exported method on `s : X`
  takes `own_X s` whole and gives `own_X s` back whole, never a selection
  of its parts, so re-establishing `X`'s invariant is the method's job and
  not something its postcondition hands to the caller.
- **Private specs may take parts.** The specification of an unexported
  function may be stated over non-public predicates: a part of a public
  predicate, or a predicate for a state in which one of the public
  predicate's invariants is suspended, whose model parameters track what is
  suspended. A part is not a list of resources gathered at one call site. A
  part about one field takes that field's reference (the map reference, the
  slice, the node address), not the address of the struct around it.
  - Definitions stay in `model.v` / `value.v` / `heap.v`, never in a WP
    file. A non-public predicate that several methods go through is defined
    in `heap.v` with its laws.
  - Why: a method's proof splits the public predicate into the parts it
    touches, steps the private functions over them, and reassembles it.
    Taking the whole type everywhere would push that structure into the Go
    instead (structs split, or methods turned into free functions, only so
    that a part can stand as a receiver) and would produce partial
    predicates in disguise.
- **Everything a spec says about a value goes through a model parameter.**
  Forbidden in a spec: struct field points-tos (`s .[store, "items"] ↦ …`), raw
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
> should be one named predicate (propose the name); (c) a predicate whose
> argument is a struct address while it owns or describes only one field;
> (d) a new predicate whose name does not carry its meaning; (e) a fact
> stated twice, or derivable from the other conjuncts. Do not report
> proof-script style. If nothing qualifies, say so.

Fix each finding, or record in the PR's "Specs and invariants" section why
it stands. A reviewer asked for gaps usually reports some; a finding that
breaks no rule is optional.
