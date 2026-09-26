---
name: spec-shape
description: The rules for cert-yjs WP specs, representation predicates and invariants, the procedure for placing a fact a proof needs, and the fresh-context review of a spec diff. Use before writing or changing a WP spec, a representation predicate, an invariant, or a definition in model.v / value.v / heap.v; whenever a proof needs a new fact and you are about to add a conjunct; when you define a new own_X / is_X; and before pushing any such change.
---

# Spec shape

## Rules

These are the project's rules for specifications. Code comments cite them by
bullet title (`spec-shape "The footprint is the whole receiver"`).

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
  model the same way (`RET #(f m)` or `⌜ret = f m⌝`).
- **The footprint is the whole receiver.** `own_X` / `is_X` is THE predicate of
  the receiver's type `X`, the one that owns every field of an `X`, not any
  predicate with an `own_` name: `s.Method()` takes `own_X s` whole and gives
  `own_X s` back, never a selection of its fields
  (`own_store_items s types ∗ own_type_pool dq types`) or a part borrowed out
  of it. If a proof only needs a part, the Go must say so (`s.fld.Method()`,
  `Method(s.fld, …)`), so the footprint is visible in the program and not only
  deep in the spec. Re-establishing `X`'s invariant is the callee's job, not
  something a postcondition hands to the caller. Likewise a predicate about
  one field takes that field's reference, not the address of the struct
  around it.
  - An unexported method that is only an internal step of one public method,
    called while the receiver is open, cannot take `own_X` whole. First narrow
    the Go footprint so it can (a free function over the fields it touches, as
    `addNode` / `deleteNode`). If a lemma must still be stated while `X`'s
    invariant is broken, it is `#[local]` and goes through a RELAXED
    representation predicate (`own_X_<relaxation>`, defined in `heap.v` next to
    `own_X`, its extra model parameters tracking the pure state of the
    suspended invariant, with fold/unfold laws to `own_X`), never through a
    bare list of call-site resources. A helper with standalone meaning still
    takes `own_X` whole.
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
  loose clauses. When a proof needs a new fact, first find the predicate it
  belongs to and add it there; a new top-level conjunct is the last resort, for
  a fact no existing predicate is about.
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

## Integrate before you add

A proof in progress adds whatever closes the current goal. That is how a
postcondition ends up with six loose clauses about one thing, or a
predicate over one field takes the address of the whole struct. The fix is
not a later cleanup: at the moment a fact is needed, find where it belongs.

### When a proof needs a new fact

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

### When you define a new `own_X` / `is_X`, or finish a postcondition

Check it against the Rules above, in particular "`is_X` / `own_X`", "A
predicate's name must carry its meaning", "The footprint is the whole
receiver" and "No over-specification".

## Fresh-context review before push

The session that wrote the proof is biased toward the conjuncts it added.
Before pushing a change to a spec, predicate or invariant, launch a
subagent (Agent tool, general-purpose) that sees only the diff and these
criteria, with a prompt like:

> Review the specification shape of `git diff origin/main...HEAD -- src/proof`
> in the cert-yjs repository. The criteria are every bullet of the "Rules"
> section of `.claude/skills/spec-shape/SKILL.md`; read it first, then the
> headers of the `model.v` / `value.v` / `heap.v` files the diff touches,
> since the existing predicates listed there are where a new fact should
> go. Report each violation with file:line, the rule's bullet title, and a
> concrete proposal. Look hardest for: (a) a conjunct added to a spec or
> predicate that belongs in an existing predicate (name the predicate);
> (b) two or more clauses about one data structure or semantic unit that
> should be one named predicate (propose the name); (c) a predicate whose
> argument is a struct address while it owns or describes only one field;
> (d) a new predicate whose name does not carry its meaning; (e) a fact
> stated twice, or derivable from the other conjuncts. Do not report
> proof-script style. If nothing qualifies, say so.

Fix each finding, or record in the PR's "Specs and invariants" section why
it stands. A reviewer asked for gaps usually reports some; a finding that
breaks no rule is optional.
