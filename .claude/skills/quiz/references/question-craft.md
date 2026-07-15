# Crafting good questions (with calibrated examples)

The user's top priority: **questions that probe the essence, not trivia.** Use
these contrasts and anchors to calibrate. Verify the "answer" against current
code before using it (some facts below were true when written and may have
drifted; that is exactly the failure mode to avoid).

## Trivia vs. essence (rewrite trivia into insight)

| Trivia (avoid) | Essence (prefer) |
|---|---|
| "`own_dll` appears how many times in `yjs_item.v`?" | "Why does `own_dll` carry a `dfrac` while `is_Store` does not?" |
| "What line is `cell_repr` defined on?" | "`cell_repr` used to pin `flags'=W8 2` and `Len()=1` and now is just `yi = ic_item c`. What changed in the model to let it shrink?" |
| "Name the fields of `DocStore`." | "Why does the store keep BOTH a `map[Client][]Node` and a linked list, when both hold the same items?" |
| "How many args does `wp_Store__Integrate` take?" | "Why must `wp_Store__Integrate`'s spec be stated over `own_ytype` and never mention heap cells?" |
| "What is the ghost RA for the item set?" | "Why is the `auth` on the OUTSIDE of the `gmap` (`auth (gmap K (gset V))`) rather than per-key?" |

The right-column questions all force a *why / what-breaks-otherwise / how-do-these-connect*
answer. That is the target.

## The sweet spot (the target zone, user's own calibration)

A good question lives in a narrow band:

- **Too detailed** (a tactic step, a field name, a line) → not essential.
- **Too general** → either common knowledge the user already has (generic CRDT
  facts like "a deterministic tie-break is needed for convergence", generic Iris
  facts) OR not specific to this project at all.
- **The target**: a fact that is **specific to cert-yjs and non-ad-hoc** (a real
  design decision the project made, not an incidental detail) **and carries
  meaning** (knowing it changes how you understand the system).

Litmus test before asking: *"Would someone who knows CRDTs and Iris well, but
has never read THIS repo, still find the answer non-obvious? And is the answer a
deliberate design of this project rather than a stray detail?"* Both yes ⇒ in the
zone. If the answer is textbook CRDT/Iris ("pointers aren't stable across
replicas", "you need a deterministic order to converge"), it is too general even
if technically about the code. If the answer is a field or a line, too detailed.

Examples of the zone (verify current before using): why the Go integrate stays
set-based (y-octo faithful) while the verified core is scanning, and what the
bridge reconciles; why the DLL relink in Integrate is a no-op on the abstract
model; why `own_store` carries the client's ghost op-history inside the lock;
why `cell_repr` could shrink to `yi = ic_item c` (what moved out, and where).
Out of the zone: "what breaks if the tie-break used arrival order" (generic
CRDT), "how many fields does DocStore have" (detail).

**Depth over breadth fills gaps best (session finding).** In practice the most
valuable sessions were NOT a wide spread of shallow questions but a SINGLE hard
上級 question drilled deep: probe a real location, ask a "why/what-breaks", then
follow the user's answers down (RA semantics, the exact lemma, "what if we
dropped this hypothesis") over many turns, showing the anchored code and
escalating hints while withholding the answer. That Socratic drill is where a
learner who already knows the surface actually discovers what they did not know
(e.g. that `ghost_map` is a `gmap_view` whose per-key `dfrac` frags are NOT
duplicable lower bounds like an `auth (gset)`, so the authority cannot mint a
cert for an existing id). When the user is deep in one question, do not rush to
the next; the depth IS the product.

## Lessons from live iteration (failure modes to avoid)

- **One spine, not glued parts.** A multi-part question is only good if the
  parts share a single essential axis and build on each other. A question whose
  (a) and (b) are about loosely related things reads as two shallow questions
  stapled together, not one deep one. If you cannot make (b) follow from (a),
  ask just (a).
- **No gotcha answers.** Avoid a question where the "correct" answer turns out
  to be a fourth thing the setup never mentioned (e.g. asking "is it store_inv
  or own_store?" when the real answer is is_Text). Distinguishing predicates the
  user already half-knows is definitional, not essential; the sting of "actually
  it's a different predicate" tests trap-awareness, not understanding. Put the
  real axis in the open and ask *why*.
- **Definitional distinctions are weak on their own.** "What is the difference
  between X and Y" is a warm-up at best. Upgrade it to "what property forces X
  and Y to be separate; what breaks if you merge them" so the answer is an
  insight, not a pair of glossary entries.
- **Do not ask what the definitions force.** If the answer follows immediately
  once you recall what a term IS (e.g. "why does the model only change by the
  insertion?" when the model is defined as a list of items + a type key), the
  question is tautological. The insight must NOT be re-derivable from the
  definitions alone. Test: state the relevant definitions, then check whether the
  answer is already obvious. If yes, drop or resharpen.
- **Pitch above the learner's baseline (they may be the author).** For a user
  who built the system, "explain this design" questions are often trivial: the
  design is front-of-mind. What still makes them think: subtle consequences that
  are easy to get wrong, counterfactuals whose answer is genuinely non-obvious
  (not textbook), distant connections not usually held together, real bugs /
  proof-obstructions that surprised even the author, and above all **proof
  exercises** (composing the actual specs forces active work, so it cannot be
  tautological). When two "explain why" questions in a row land as
  obvious-or-generic, switch to a proof exercise or a real past-problem.

## Answering discipline (do not pad, do not ask vague sub-questions)

- **A vague sub-question is a bug, but an unfamiliar real term is not.**
  Distinguish two causes of "I don't get the question": (1) the part has no
  single clear answer (genuinely vague) -> your bug, make the target unambiguous
  or cut it; (2) the part is answerable but uses a project-specific term the
  learner has not met (e.g. "doc-level op" = `Op := TId * YjsOperation`) -> that
  is the quiz doing its job by surfacing a real concept, NOT a reason to cut.
  For (2), gloss the term in one clause when you use it (or make learning the
  term the explicit target), so the terminology does not block an otherwise
  answerable question. Tell the two apart before blaming the question: is the
  answer well-defined once the term is known?
- **Answer at the level asked; do not lecture the known.** When you reveal an
  answer, give the crisp thing that was asked, then stop. Do NOT re-explain
  background the user (often the author) already knows (e.g. "broadcasting a
  certificate guarantees receiver-side safety"). Padding a correct short answer
  with familiar generalities reads as noise and wastes their time. If unsure
  whether they know it, ask, do not assume they need it.

## Good question shapes

- **Why is it this way?** ("Why are origins stored as ids, not `*Item`
  pointers?")
- **What breaks if not?** ("If the lock invariant `store_inv` mentioned
  per-operation state instead of existentially hiding it, what goes wrong?")
- **Connect two parts.** ("How does `own_store` relate to `store_inv`, and which
  one does a public method's spec talk about?")
- **Reconstruct a decision.** ("The Delete path is still `//go:build !goose` yet
  deletion is modeled. Where did the deletion bit go, and why keep the codec out
  of goose?")
- **Spot the deviation.** ("Name one place the Go port deviates from y-octo's
  containers, and the cost of that deviation.")
- **Compose specs (proof mode).** ("Given `own_store` and
  `wp_store__applyUpdate_certs`, sketch a WP for applying two updates in
  sequence; which model lemma discharges order-independence?")

## Calibrated example questions

Illustrative only. Regenerate from live sources; do not just replay these.

### 入門

- 「`is_X` と `own_X` の命名規約の違いは何か。`own_X` にだけ `dfrac`
  引数が付くことが多いのはなぜか。」
  Answer: `is_X` = persistent handle / read-only fact (duplicable);
  `own_X` = ownership, `dfrac`-parameterized when it is plain heap state so it
  can be shared fractionally. (`CLAUDE.md` Predicate naming.)
- 「このプロジェクトのビルドは Go を編集した後になぜ必ず goose を再実行する
  必要があるのか。」
  Answer: `make` alone checks the stale translation; the Go change silently has
  no effect until goose regenerates `src/code`. (`CLAUDE.md` Workflow.)
- 「y-octo の `HashSet` / `HashMap` / `Vec` は Go では何に写すのが方針か。
  なぜ証明の都合でスライスに落としてはいけないのか。」
  Answer: `map` (`map[K]struct{}` for a set) / `map` / slice; faithfulness to a
  realistic Yjs, and Perennial-New has full map support so there is no excuse.

### 中級

- 「公開仕様（例: `wp_Store__Integrate`）が `own_ytype` などの公開述語だけで
  述べられ、ヒープセルやノード位置に触れてはいけないのはなぜか。」
  Answer: specs are contracts for callers; leaking internal heap state couples
  callers to the representation and breaks the `is_X`/`own_X` abstraction that
  lets the rep refactor freely. (`CLAUDE.md` Public specs.)
- 「store のロックが `sync.Mutex` から `sync.RWMutex` に変わった動機は何で、
  なぜ read 側の検証が別途重い作業になったのか。」
  Answer: concurrent readers for read-APIs like `Text.Len` (#22); RWMutex's
  guard needs `Fractional P`, forcing a fractional read share of `store_inv`.
- 「YATA の integrate はどうやって並行挿入の順序を決定的に解決し、収束させる
  のか（origin をどう使うか）。」
  Answer: it scans the conflict range and breaks ties by origin ids so any
  delivery order yields the same sequence; verified as a refinement of the pure
  `setintegrate` (`setintegrate_eq_integrate`).

### 上級

- 「アイテム集合のゴースト状態に `auth (gmap K (gset V))` を使い、`gmap K (auth
  (gset V))`（キー毎の auth）にしないのはなぜか。何が証明できなくなるか。」
  Answer: a per-key fragment `◯ S` is valid even when the key is absent, so it
  fails to witness membership; wrapping the `auth` around the whole map makes the
  fragment prove both key-existence and the subset lower bound.
  (`proof-engineering.md` §F.)
- 「coq-lsp / rocq-mcp が緑でも `make` が赤になる典型例を挙げ、なぜ対話チェッカ
  では見逃されるのか。」
  Answer: Fleche tolerates errors and forward references (treats broken proofs as
  admitted and continues), so a strict `coqc`/`make` is the real gate; e.g. a
  `rewrite decide_True` that needed `case_decide`, or a helper placed before the
  lemma it uses. (`proof-engineering.md` §D.)
- 「`iris.algebra.{auth,gmap,gset}` をファイル冒頭で `Import` すると、既に通って
  いた word 演算の証明が壊れることがあるのはなぜか。回避策は。」
  Answer: it retunes the `<` scope so `sint.Z i` re-parses at `nat`; `Require`
  (not `Import`) at top, then `Import` inside the section after the verified
  proofs. (`proof-engineering.md` §D.)
- (証明練習)「`own_store o dq m` と `wp_store__applyUpdate_certs` を仮定に、更新を
  2 つ順に適用する関数の WP を組み立てよ。post をどう書き、順序独立性はどの
  モデル補題で正当化するか。」
  Expected: thread `own_store` through two applyUpdate calls, collect the
  `is_root_lb` cert fragments, and argue the resulting document is independent of
  order via `integrate_commutative` / `setintegrate_eq_integrate` (name the one
  that fits how the model states convergence; verify in `yjs_core.v`).
