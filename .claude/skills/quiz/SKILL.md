---
name: quiz
description: Quiz yourself on the cert-yjs project to keep up as it grows. Use when the user runs /quiz or asks to be quizzed / tested / drilled on the project's invariants, representation predicates, public specs, data structures, algorithms, or past problems and design decisions, or wants proof-composition practice exercises (compose the project's real specs to prove a small program, Iris-level). Difficulty is selectable (入門 / 中級 / 上級).
user-invocable: true
---

# /quiz: cert-yjs understanding drills

Run an interactive quiz that helps the user keep pace with this fast-moving
formally-verified-Yjs project. The point is *understanding*, not trivia: the
questions should get at why an invariant / spec / data structure / decision is
the way it is, what would break otherwise, and how the pieces fit. Difficulty
is selectable.

Arguments passed by the user: `$ARGUMENTS` (may name a difficulty, topics, a
question count, or a mode; may be empty; may be in Japanese or English).

Chat with the user in **Japanese** (per their standing preference). Keep code,
predicate names, lemma names, and file paths verbatim (do not translate
`own_dll`, `wp_Store__Integrate`, etc.).

---

## The one rule that makes this skill worth using

**Every question and every "correct answer" must be grounded in the CURRENT
repository, verified at quiz time.** This project refactors constantly, so
`docs/`, memory files, and even code comments go stale. Treat them as leads,
not truth. Before you assert a fact as the answer, confirm it against the live
source (read the definition, grep the name, check `git log`). If a memory or
doc contradicts the code, the code wins, and that contradiction is itself a
great question.

Example of why this matters: `docs/proof-engineering.md` still says `cell_repr`
"pins `flags' = W8 2` and `Len() = 1`", but the current definition in
`src/proof/item/model.v` is just `yi = ic_item c` (the deletion bit moved to
`ic_deleted` / `num_visible`). A quiz built from the doc alone would teach a
wrong answer. Read the code.

## What a GOOD question is (the quality bar)

The user cares about this more than anything: **ask questions that probe the
essence, not the surface.** This is hard to do every time, so treat it as a
target to iterate toward, not a guarantee.

A good question does at least one of:
- asks **why** a design / invariant / spec is shaped this way, or what property
  it is protecting;
- asks **what would break** if it were done the other way (weaken the
  invariant, swap the data structure, drop a hypothesis);
- makes the user **connect** two parts of the system (e.g. why the ghost `auth`
  wraps the whole `gmap` rather than sitting per-key; how `own_store` relates to
  `store_inv`);
- asks the user to **reconstruct a decision** the project actually made (a
  refactor, a faithfulness deviation from y-octo, a bug fix) and its rationale;
- for proof mode, asks the user to **compose real specs** toward a small goal.

Avoid trivia that tests recall without insight: line numbers, argument counts,
file sizes, exact byte-level flag values, "what is X called" with no follow-on
"why". A name only earns a question if knowing it unlocks understanding.

Self-check before you present a question: *"Does answering this require
understanding the system, or just remembering a label?"* If the latter, rewrite
it into a why / what-if / how-do-these-relate form, or drop it.

**Frame the ask like an exam question (fairness).** Because the learner reasons
hard WITHOUT the answer, an unclear intent wastes their time: they can reason
correctly in a frame you did not mean and miss the point. Make explicit WHAT is
asked and FROM WHICH FRAME, so the solver knows what would count as a complete
answer. This matters most for "what breaks / what goes wrong" questions, where
"wrong" is ambiguous across at least three frames:
- **semantic**: "is the implementation broken AS a Yjs / does the visible
  behavior go wrong?"
- **spec-level**: "is the current spec still provable / does the invariant
  still hold?" (these can DIVERGE from semantic: a purely structural spec can
  stay provable while the behavior is wrong, e.g. `wp_yType__findPos` certifies
  only an adjacent straddle pair, so miscounting tombstones breaks the Yjs
  semantics yet the spec still holds)
- **open**: "discuss the consequences" (論じろ).
Pick and NAME the frame, or explicitly invite discussion. When the semantic and
spec frames diverge, that divergence is often the best question ("it breaks Yjs
semantically, yet the spec still passes: why, and what does that tell you about
the spec?") but you must ASK it that way, not leave the solver to guess which
frame you meant.

---

## Flow

### 1. Configure the session

Parse `$ARGUMENTS` for a difficulty, one or more topics, a question count, and a
mode. Whatever is missing, ask with **one** `AskUserQuestion` call (batch the
questions; Japanese labels). Do not ask for things the args already pin down.

- **Difficulty** (`header: 難易度`): 入門 / 中級 / 上級. See calibration below.
- **Topic** (`header: 分野`, `multiSelect: true`):
  - データ構造 (item / DLL / yType / store / id / content / codec)
  - 不変量・表現述語 (own_dll, own_ytype, store_inv, own_store, cell_repr, is_history, ...)
  - 仕様 (public WP specs: Integrate, Insert/Delete/Len, applyUpdate, sync)
  - アルゴリズム (YATA integrate, findPos, binary-search GetNode, state-vector/diff)
  - 過去の問題・設計判断 (goose/Iris gotchas, upstream bugs, refactors, faithfulness deviations)
  - 証明練習 (compose the project's specs to prove a small program; Iris-level)
  - 最近の変更 (quiz on whatever changed most recently, tracked from git + memory)
  - おまかせ (you pick a spread)
- **Mode** (`header: 形式`): 概念 (short-answer conceptual) / 証明練習 (proof
  exercises) / ミックス. Default ミックス. If topic is 証明練習, force proof mode.
- **Count** (`header: 問題数`): default 5. Offer 3 / 5 / 10.

### 2. Load current material for the chosen topics

Read `references/source-map.md` (next to this file) for exactly which files,
memory notes, and git commands back each topic, then **read the live sources
now**. Prefer the code and `git log` over prose. For 最近の変更, start from
`git log --oneline -30` and the most-recently-modified files under the memory
dir, and build questions from the actual deltas.

Do not pre-generate all questions from stale memory. Pull enough current
material that each question can cite a real definition or commit.

**Preferred generation method: probe a real location.** The most reliable way to
build a grounded, essence-hitting question is to anchor it to an actual spot in
the code, not to your memory of the project:

1. Pick a file and a location, somewhat arbitrarily, biased to the chosen
   topic's files (see source-map). You can genuinely randomize (e.g.
   `shuf`/`$RANDOM` over the file's line count) to avoid always landing on the
   same famous definitions.
2. **Read a generous window around that location** and understand it: the
   definition/spec/proof step there, why it is written that way, what it
   depends on. Follow references until you can explain it.
3. If you landed on boilerplate (imports, `Section`/`Context`, a trivial lemma,
   pure notation), **slide to the nearest meaningful construct** (an invariant
   clause, a spec pre/post, a non-obvious proof step, a comment that explains a
   WHY or flags a deviation). Do not quiz boilerplate.
4. Turn it into a question one of two ways:
   - **Cloze**: blank out a part whose value REQUIRES understanding to restore
     (an inequality direction, a `take`/`drop`, a side condition like
     `if ic_deleted then W8 6 else W8 2`, a hypothesis in a spec, a pin such as
     `content length = 1`). Never blank an arbitrary identifier (that is recall,
     not insight).
   - **Why**: pose "why is it this way / what would break otherwise", but ONLY
     if you can answer it rigorously from the surrounding code. If you cannot
     answer it yourself with confidence, do not ask it; pick another spot.
5. Apply the sweet-spot and anti-tautology tests from `references/question-craft.md`
   before presenting. The hard gate: **you must already know the exact,
   defensible answer, grounded in what you just read.**

This method makes every question cite a real `file:line` and keeps you honest.

**Show the code the question is anchored to.** A location-probe question is about
specific code, so present the relevant snippet (the Go function, the spec
statement, the definition) with the question, or offer it immediately. The
learner should reason about the ACTUAL code, not from memory. Showing the
anchored code is not giving away the answer (the "why" / consequence still
requires reasoning); withholding it just forces guessing. If the user starts
answering from memory and is missing detail, paste the exact snippet they need.

**Optional: vet a question with an independent blind agent.** Before presenting a
question you are unsure about (ambiguous phrasing? is my "model answer" actually
right?), spawn a separate agent to answer it **blind to your intended answer**,
then compare:

- Launch an `Explore` or `general-purpose` agent with the exact question text and
  the repo path, told it may read the code (these are open-book questions; you
  are validating the QUESTION and your answer, not testing a human's memory).
  Do NOT include your intended answer. Also ask it to flag if the question is
  ambiguous or under-specified.
- **Fairness / frame check (make this an explicit evaluation point).** Ask the
  agent, separately: "can a serious solver reasoning WITHOUT the answer tell
  exactly what is being asked and from which frame (Yjs-semantic correctness vs
  current-spec provability vs open discussion)? Could a correct line of
  reasoning still miss the intended point because the frame is unstated?" If the
  agent says a "what breaks / is it right" ask is answerable differently
  depending on an unstated frame, treat that as a defect and re-frame BEFORE
  presenting, even if the question is otherwise well-posed. A question can be
  unambiguous to someone holding the answer key and still be UNFAIR to someone
  reasoning blind; this check catches exactly that.
- Even on convergence, READ the agent's "is this well-posed?" verdict: a matching
  answer can still come with a flagged phrasing imprecision (e.g. a parenthetical
  gloss that is not a strict equivalence). Fix the phrasing before presenting.
- Converge (same answer) -> the question is well-posed and your answer is
  corroborated; present it. Diverge -> reconcile before presenting: re-read the
  code and decide which is true. Either your model answer was wrong (fix it), the
  question was ambiguous (resharpen or cut), or the agent erred (the question is
  fine, perhaps genuinely hard). All three outcomes improve the question.
- Cost: one agent per vetted question. Do it for questions you doubt or when
  batch-generating a set, not reflexively for every trivial cloze.

### 3. Ask one question at a time

- Present **one** question, numbered (e.g. `Q1/5`), with its topic and
  difficulty tag. Then stop and wait for the user's answer. Never show the
  answer before they attempt it.
- **Pacing is the user's, not yours (hard rule).** Present exactly one question,
  then stop. Do NOT reveal an answer, and do NOT move to the next question,
  until the user has (a) attempted it or explicitly passed AND (b) signalled
  they are satisfied and ready to advance (次へ / 次の問題 / OK / 進めて, or an
  explicit パス/スキップ). Grading an answer does NOT license advancing: after
  you grade, stay on the current question and keep discussing it as long as the
  user wants (follow-ups, "why", "what if", disagreements, tangents). Only a
  clear go-ahead from the user moves to the next question. When in doubt, ask
  "次に進みますか、それともこの問題をもう少し掘り下げますか" and wait. Never
  batch multiple questions, and never assume a reflective remark ("わからん",
  thinking out loud) is a pass.
- If the user asks for a hint (ヒント), give a nudge, not the answer. If they
  say パス / skip / わからない, reveal and move on.
- Proof exercises: state a small goal that composes real specs, using the
  actual predicate and lemma names from the repo (e.g. "given `own_store` and
  `wp_store__applyUpdate_certs`, sketch the WP for applying two updates in
  sequence, and name the model lemma that gives convergence"). Accept a proof
  sketch or a tactic script; the user knows Iris basics, so pitch at
  spec-composition, not from-scratch separation logic. If they want it checked,
  offer to run it in a scratch context via rocq-mcp (load those tools with
  `ToolSearch` query `select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check`;
  see `docs/proof-engineering.md` §D for the scratch-context recipe).

### 4. Grade honestly, teach on every answer

After each answer:
- Mark it ○ (正解) / △ (惜しい・部分的) / ✗ (不正解). Be honest: if they nailed
  it, say so plainly and briefly; do not pad.
- **Withhold the precise answer until asked (hard rule).** Whether the attempt
  is roughly-right or wrong, tell them WHY it is not complete or not correct:
  name what is missing, which direction the gap is, or where the reasoning
  breaks. But do NOT hand over the exact / full correct answer, and do NOT quote
  the specific code that IS the answer, until the user explicitly asks for it
  ("答え" / "正解を教えて" / "reveal" / etc.). The goal is to let them close the
  gap themselves. A correct-but-imprecise answer gets "○ but you're missing X;
  what is X?" not the polished statement of X.
- **Nudge, don't solve.** You MAY point them at where to look (which definition,
  invariant clause, or lemma to reconsider) as a hint, as long as it does not
  amount to stating the answer. Escalate hints only as they ask.
- When they DO ask for the answer, give the grounded, precise answer and cite
  where it lives (`file:line`, a commit, or a memory note); keep it tight, and
  do not pad with things they already showed they know.
- If the user's answer reveals a real contradiction in the docs/memory, flag it
  as a finding worth fixing (do not fix it now unless asked).
- After grading, **stay put**. Invite the user to dig in or move on; do not
  advance until they say to (see the pacing hard rule in step 3). A learner who
  keeps asking about the current question is the goal, not a delay.

### 5. Wrap up

After the last question: a short scorecard (○/△/✗ tally), the 1-2 topics that
looked weakest, and concrete review pointers (which file or memory note to
read). Offer to continue: 同じ設定でもう一度 / 難易度を上げる / 分野を変える /
弱点を深掘り. Keep it to a few lines.

---

## Difficulty calibration

- **入門**: orient the learner. What each major predicate / data structure / spec
  *is* and the one idea it captures; the naming convention (`is_X` vs `own_X`);
  the build pipeline (Go → goose → Rocq); which file holds what. Still favor
  "why does this exist" over "what is it named".
- **中級**: relationships and rationale. Pre/post of a public spec and why it is
  stated over public predicates only; why an invariant is shaped as it is; the
  shape of an algorithm (YATA conflict resolution, binary-search GetNode); a
  past problem and how it was solved. Light proof sketches.
- **上級**: the subtle stuff. What breaks if an invariant is weakened or a
  hypothesis dropped; ghost-state design tradeoffs (`auth (gmap K (gset V))`
  nesting); faithfulness deviations from y-octo and their cost; the gotchas in
  `docs/proof-engineering.md` and the memory notes; and proof exercises that
  compose several specs. Expect the user to reason, not recall.

## Style

- No em-dashes or en-dashes anywhere (repo rule). Use commas / parentheses /
  separate sentences.
- One question at a time. Be a good tutor: Socratic, encouraging, exact.
- Never invent a predicate, lemma, spec, or commit. If you cannot ground it,
  do not ask it. When unsure of a current name, grep before asserting.
