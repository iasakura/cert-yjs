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
- **the proof**: the script between `Proof.` and `Qed.`, which nothing outside
  the file can observe.

A rule binds nothing beyond what its subsection and its own text name. In
particular, the rules on a spec's statement say nothing about what the proof
of that spec may do. Publicity, as the rules use the word (a public or
non-public predicate, a function public or private for a type), is a property
of an interface. The vocabulary below settles it, by what a predicate
describes and by a function's call sites, and what it constrains in turn is
what a spec states. Inside a proof the ordinary separation-logic freedom
applies: the proof may unfold, split, borrow, open and recombine every
resource it holds, non-public predicates of any type included, and no rule
here restricts that. A non-public predicate reaching the proof of a public
function is therefore not a violation of anything in this file.

Code comments cite a rule, or an entry of the vocabulary below, by its bullet
title
(`spec-shape "Values of Cert-Yjs types appear in specs through their predicates"`).

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
- **Public and non-public predicates.** `own_X` / `is_X` is public: `own_X`
  holds every resource of the value, all its fields and what they own,
  together with the invariant of `X`, and `is_X` covers the same resources
  persistently or through the lock or invariant that guards them. A non-public
  predicate of `X` owns or persistently covers some but not all of those
  resources, or describes a state in which the invariant of `X` need not hold;
  a fraction of `own_X` still covers every resource and is public. Whether a
  predicate is public depends on what it describes, not on its name: any
  predicate that is not non-public is public. `is_history_lb`, persistent
  knowledge of a lower bound on a client's operation history, covers no part
  of a value's resources and is public.
- **Public and private functions.** This classifies the Go functions and
  methods of Cert-Yjs, by their call sites in the Go code. A function or
  method is private to a type `X` when it is unexported and called only from
  within the implementation of `X`, that is, from the methods of `X` and from
  other functions private to `X`. Every other function is public for `X`:
  every exported one, and an unexported one as soon as code outside the
  implementation of `X` calls it. This is finer than Go's export, under which
  every unexported function would count as private. Known deviation, and where
  it belongs: acquiring and releasing a lock counts as an operation of the type
  that holds the lock, so the classification does reach `wp_Store__rlock` and
  `wp_Store__wlock` (`src/proof/store/wp_private.v`), the specs of
  `sync.RWMutex`'s own `RLock` and `Lock` at the lock field beside the store.
  It classifies them as public, because the call sites are outside that type's
  implementation: `Text.String`, `Text.Len` and `Text.Observe` each take and
  release the lock themselves, as do `Doc` and the encoder. A public spec takes
  its type whole and gives it back whole, which an acquire cannot do, since an
  acquire is what produces the contents; so these two statements mention
  non-public predicates of the store and the rule above is not met. The
  deviation is in the Go, not in the rule: where the lock is not exposed, no
  such spec arises. `transact` takes the closure it runs under the write lock,
  and its own spec mentions no non-public predicate, because the store's
  contents appear only inside the closure's contract. Giving the remaining
  access paths that same closure-passing form leaves the acquire and the
  release called only from within the holding type, which makes them private to
  it and closes this with no change here.

## Rules

### The statement of a spec

- **Values of Cert-Yjs types appear in specs through their predicates.** To
  mention a value of a Go type `X` defined in Cert-Yjs, a spec uses a
  predicate of `X`, never the value's fields. A value held inside another
  value may appear through the holder's predicate instead, as the store's
  nodes appear in the store's predicate.
- **Specs of public functions use only public predicates.** The statement of a
  spec of a function public for `X` mentions values of `X` only through public
  predicates. It takes each `own_X` / `is_X` it needs, its receiver's included,
  as that one predicate (at any fraction), never as a selection of its parts,
  and whatever `own_X` it returns, it returns whole: re-establishing the
  invariant of `X` is that function's job, not its caller's. Non-public
  predicates of `X` appear only in the statements of specs of functions
  private to `X`. A value that appears through its holder's predicate (the
  rule above) counts as part of the holder for this rule, so a function private
  to the store may show the store's nodes through a non-public predicate of the
  store.
- **Everything a spec says about a value goes through a model parameter**, the
  return value included (`RET #(f m)` or `⌜ret = f m⌝`). Forbidden in a spec:
  struct field points-tos (`s .[store, "items"] ↦ …`), raw slices or maps of
  internal records, goose struct values and their fields (`yjs.item.t`,
  `itemVal.(left')`, `idv.(clock')`), flag bytes (`W8 2`), and `w64` / `uint.Z`
  arithmetic for a condition that a model predicate already states (state it
  with that predicate, such as `cell_covers` or `cell_fits`).
- **Specs stay intuitive.** The developer's idea of a function is a few
  sentences, so its spec is a few conjuncts, never ten. Conditions are grouped
  by the data structure or semantic unit they are about into one named
  predicate (`pool_invs`, `doc_registry_coh`, `cell_covers`), not listed as
  separate conjuncts.
- **No over-specification.** A postcondition states each condition once (not
  `setintegrate input arr = Some arr'` next to its unfolding `arr' = take midx
  arr ++ …`) and states only what the function means. A condition that follows
  from the others, or that a caller merely finds convenient, is a lemma over
  the model or the predicates in the layer file that defines them (`model.v`,
  `value.v` or `heap.v`), not a conjunct.

### The definition of a predicate

- **A new conjunct goes into an existing predicate, or the PR says why not.**
  This rule binds a predicate's definition and a spec's statement alike. When
  a spec or a predicate gains a conjunct, first consider whether its condition
  fits naturally into the predicate of an existing conjunct. If it does not,
  the PR description says so for that conjunct, with the reason. Reviews check
  every new conjunct against this rule.
- **New non-public predicates are named `own_X_…` / `is_X_…`.** This rule
  binds the name a new predicate is given. The name marks the predicate as one
  of `X`'s, and it does not decide the predicate's publicity: that follows
  from what the predicate describes (vocabulary, "Public and non-public
  predicates").

### Which specs a file exports

- **One spec per function.** A second spec exists only if it is used and
  cannot be derived from the first. Specs that are unused, or that are a
  stepping stone of one proof, are deleted or made `#[local]` in that proof's
  file.

### The proof

- **Reuse the Rocq-Yjs model, don't invent independent proofs.** This rule
  reaches the proof, the statement the proof refines, and the Go code under
  both. State WP specs as refinements of the pure model and compose with its
  lemmas (`YjsArrInvariant_integrate`, `setintegrate_eq_integrate`,
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
> after this prompt. The criteria are every bullet under the "Rules" section
> of `.claude/skills/spec-shape/SKILL.md`, and only those: the skill's
> separate "Vocabulary" section defines the terms the rules use and is not
> itself a criterion. Read the skill first, "What each rule binds" included,
> then the headers of the `model.v` / `value.v` / `heap.v` files that define
> the predicates the diff uses or changes, including files the diff does not
> touch. Judge each rule against the object its subsection is named after,
> unless the rule's own first sentence names another: a rule under
> "The statement of a spec" is judged against the triple alone, so a
> predicate that appears only inside a proof script is not a finding against
> it, whatever that predicate is.
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
