# Quiz source map

Where the material for each topic lives. Read these **live** at quiz time (code
and `git log` first; prose is a lead, not truth). Paths are repo-relative.
The memory dir is
`/home/ia/.claude/projects/-home-ia-ghq-github-com-iasakura-cert-yjs/memory/`.

Anchors that rarely go stale: `CLAUDE.md` (rules + architecture table),
`README.md`, `WORKFLOW.md`, `docs/proof-engineering.md` (technique + gotchas,
but its cert-yjs-specific facts drift, verify against code).

## データ構造 (data structures)

- Go: `yjs/item.go` (Item, DLL pointers, origins), `yjs/ytype.go` (yType /
  findPos), `yjs/store.go` (DocStore, per-client `map[Client][]Node`, clock),
  `yjs/id.go`, `yjs/content.go`, `yjs/doc.go`, `yjs/text.go`, `yjs/range.go`,
  `yjs/refs.go`, `yjs/update.go`, `yjs/codec.go` (v1 codec, `//go:build !goose`).
- Proof reps: `src/proof/yjs_item.v` (`item_cell`, `own_dll`, `cell_repr`,
  `num_visible`), `src/proof/yjs_ytype.v` (`own_ytype`), `src/proof/yjs_store_base.v`.
- Memory: `port-faithful-data-structures.md`, `item-cell-origin-existential.md`,
  `is-dll-existential-refactor-gotchas.md`, `ytype-module-split.md`,
  `store-lock-item-plan.md`.
- Essence hooks: why `[]Node` binary-search AND a linked list coexist (both
  share items, as in y-octo); why origins are ids not pointers; HashSet/HashMap
  → Go `map`, Vec → slice (faithfulness), and the known `scanConflicts` `[]Id`
  deviation.

## 不変量・表現述語 (invariants / representation predicates)

- `CLAUDE.md` "Predicate naming" rule (`is_X` persistent vs `own_X` ownership).
- `src/proof/yjs_store_base.v`: `store_inv` / `store_inv_ro` / `store_inv_excl`,
  `own_store`, `own_item_map`, `is_Store` / `is_type_lb` / `is_root` /
  `is_root_lb`, RWMutex wrappers.
- `src/proof/yjs_item.v`: `own_dll`, `cell_repr` / `cells_repr`, `num_visible`,
  `flip_cell`.
- `src/proof/yjs_ytype.v`: `own_ytype` (model = items + tombstone bits) over
  `own_ytype_cells`.
- `src/proof/yjs_history.v`: `is_history`, `own_client_history`, `is_op_cert`.
- Memory: `issue-47-predicate-model-refactor.md` (NAME MAP),
  `predicate-refactor-own-store.md`, `item-cell-origin-existential.md`,
  `is-dll-existential-refactor-gotchas.md`, `store-lock-item-plan.md`.
- Essence hooks: why public specs must be stated over `is_X`/`own_X` and never
  mention heap cells; why `own_store` is one cohesive predicate over
  `(client, history, doc)`; what the lock invariant owns vs. existentially hides.

## 仕様 (public WP specs)

- `src/proof/yjs_store_integrate.v`: `wp_Store__Integrate` (cells-level and
  model-level).
- `src/proof/yjs_text.v`: `wp_Text__Insert` (mints op certs), `wp_Text__Delete`,
  `wp_Text__Len` (read-API, RWMutex read share).
- `src/proof/yjs_store_update.v`: `wp_store__applyUpdate_certs` (`own_store`-level).
- `src/proof/yjs_doc.v`: doc-level applyUpdate wrapper.
- `CLAUDE.md` "Public specs" rule (the `{{{ own_X o dq m ∗ ⌜Pre⌝ }}} … {{{ ⌜Post⌝ }}}`
  shape; persistent `is_X` as duplicable monotone-knowledge hypotheses).
- Memory: `insert-proof-done.md`, `general-insert-progress.md`,
  `delete-proof-done.md`, `apply-update-progress.md`,
  `issue-22-rwmutex-progress.md`, `sync-fragment-specs.md`, `issue-40-done.md`.
- Essence hooks: why the spec exposes the grow-only `L` as monotone knowledge;
  why applyUpdate returns delivered content as `is_root_lb` fragments; what the
  Integrate post guarantees (refines `setintegrate`, preserves the model iso).

## アルゴリズム (algorithms)

- YATA integrate: `yjs/store.go` `Integrate` + extracted cores (`scanConflicts`
  / `findIntegrationLeft`); pure model `integrate` / `setintegrate` from the
  rocq-yjs library re-exported in `src/proof/yjs_core.v`.
- `findPos`: `yjs/ytype.go` + `wp_yType__findPos` in `src/proof/yjs_ytype.v`.
- Binary-search `GetNode` / `AddNode`: `yjs/store.go`.
- Sync protocol: state-vector + diff (`computeStateVector` / `computeDiff`).
  Note: the sync Go/proof files (`protocol.go`, `yjs_sync.v`) are NOT on every
  branch (they were absent on `quiz` when this was written). Locate them with
  `git log --all --oneline -- '*sync*'` and grep the current tree before quizzing
  on them; lean on the memory note if the files are elsewhere. The split/run work
  is separate again.
- Memory: `integrate-loop-formulation-gap.md` (set-based Go vs scanning verified
  loop, the bridge), `integrate-core-extraction.md`, `setfii-loop-eq-proof-plan.md`,
  `store-integrate-splice-plan.md`, `issue-51-sync-protocol-done.md`,
  `issue-28-runs-design.md`.
- Essence hooks: why the Go loop is set-based but the verified core is scanning
  (the refinement bridge); how YATA breaks ties with origins to converge; why
  GetNode can binary-search (per-client causal delivery ⇒ sorted clocks).

## 過去の問題・設計判断 (past problems / design decisions)

- `docs/proof-engineering.md` §A-§F (every gotcha), `CLAUDE.md` rules.
- `git log --oneline -40` and PR merge commits (the refactor stack #47/#49/#64,
  RWMutex #22, ghost history #42, sync #51, grove N0 spike).
- Memory (gotchas): `goose-method-stepping.md`,
  `goose-noop-method-breaks-wp-entry.md`, `goose-file-split-and-build-tags.md`,
  `recordset-eqrefl-vs-reflexivity.md`, `iris-rewrite-hits-whole-sequent.md`,
  `destruct-decide-reduces-hyps.md`, `set-solver-big-context-hang.md`,
  `coq-lsp-vs-coqc-strict.md`, `proof-using-type-star-cross-section.md`,
  `compile-log-hygiene.md`, `proof-file-layout-section-top.md`.
- Memory (bugs / decisions): `report-upstream-bugs.md`,
  `issue-42-ghost-history-design.md` (the `deliver_locally` bug, fixed upstream),
  `grove-new-wp-spike.md` (broken trusted code), `roadmap-after-42.md`,
  `pr-granularity-review-value.md`, `mirror-reference-formalizations.md`.
- Essence hooks: why coq-lsp green does not imply `make` green; why importing
  `iris.algebra.{auth,gmap,gset}` at file top breaks verified word-arith proofs;
  why a set must not be downgraded to a slice; a concrete upstream bug and its
  fix.

## 証明練習 (proof exercises)

- Compose the public specs above toward a small goal. Real names to build from:
  `wp_Store__Integrate`, `wp_Text__Insert`, `wp_store__applyUpdate_certs`,
  `own_store`, `is_Store`, `own_ytype`, `own_dll`, `is_history`.
- Iris / goose tactics and the scratch-context (rocq-mcp) workflow:
  `docs/proof-engineering.md` §B (Iris proof mode), §C (Perennial/goose WP),
  §D (interactive workflow), §F (ghost state).
- Model lemmas to name in convergence arguments (from rocq-yjs, re-exported in
  `src/proof/yjs_core.v`): `setintegrate_eq_integrate`, `integrate_commutative`,
  `YjsArrInvariant_integrate`, `yjs_strong_convergence`.
- Checking: `ToolSearch` query
  `select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check`, then follow
  `proof-engineering.md` §D (force_restart preamble + Section dev + Context).

## 最近の変更 (recent)

- `git log --oneline -30`, `git log --since=...`, and the newest files under the
  memory dir (`ls -t`). Build questions from the actual deltas: what a recent
  commit changed, why, and what invariant/spec it touched.
