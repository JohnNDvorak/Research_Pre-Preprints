# Self-Drive Research Loop Skill: Review And Field Report

Date: 2026-04-18

This is a short review of the `self-drive-research-loop` Codex skill I used while developing the conditional switching roadmap for the
mean-zero version of Erdős Problem #521.

## Short Verdict

The skill is useful because it turns an open-ended research conversation into a sequence of auditable rounds. Its main value is not that it
proves theorems by itself. Its value is that it forces the assistant to keep a live target, record failed routes, preserve scale constraints,
and leave a handoff that another model or human can inspect.

In this project, that discipline mattered. The argument went through many plausible but wrong or incomplete formulations: unconditional
off-core estimates, the wrong Schur complement direction, own-block perturbations instead of total perturbations, insufficient small-ball
errors, and a public post that over-emphasized workflow before mathematics. The loop made these failures explicit rather than letting them
blend into the next answer.

## What The Skill Enforces

Each round must identify:

1. the exact theorem or obstruction being attacked;
2. the definitions and normalizations used;
3. which inputs are already banked and not being reproved;
4. what was proved, tested diagnostically, refuted, or reduced;
5. what route is now forbidden or demoted;
6. the smallest next theorem.

The skill also maintains three ledgers:

1. `round_metrics.jsonl`, recording the object, scale, classification, and status of each round;
2. `route_ledger.jsonl`, recording failed or demoted approaches so they do not silently recur;
3. `target_lineage.jsonl`, recording why the next target follows from the previous one.

It also keeps `latest.md` and `handoff_latest.md`, so the project state can be resumed without relying on chat memory.

## Why This Helped Here

The Erdős problem thread is a good example of a task where ordinary back-and-forth chat is fragile. The proof architecture has many moving
parts:

- a coupling contradiction that must preserve iid marginals;
- rare two-endpoint template events;
- conditional off-core stability under that rare event;
- finite-window Riesz and projected Schur estimates;
- endpoint and shoulder anti-concentration under fiber conditioning;
- checkpoint second-moment selection;
- a global inside-interval event from Do's theorem.

Without a ledger, it is easy to forget which of these are proved, conditional, or merely plausible. The skill forced those distinctions.
It also made external model review more effective: when GPT Pro 5.4 was called in, the prompt could include the live target, the banked
inputs, the failed routes, and the exact verdict requested. That made the review much sharper than an open-ended "what do you think?"
question.

## What Worked Best

The best parts of the skill were:

1. **Classification discipline.** Rounds had to be labeled `PROVED`, `CONDITIONAL_REDUCTION`, `FAILED_ROUTE`, `DIAGNOSTIC_ONLY`, and so on.
   This reduced premature closure.
2. **Failed-route memory.** Once a route failed, the obstruction became a guardrail. For example, the project explicitly forbade relying on
   unconditional off-core estimates where a conditional estimate under the rare core event was needed.
3. **Scale tracking.** The skill repeatedly asks for the target scale before using inequalities. That is essential in problems where a
   missing power of \(N\), a lost \(\log N\), or an \(o_N(1)\) error at polynomial smoothing scale can break the proof.
4. **Handoff prompts.** The handoff format made it possible to call in GPT Pro 5.4 as an external referee without making it rediscover the
   whole project history.
5. **Public-posting discipline.** The same ledgers that helped the proof audit also helped distinguish a proof announcement from a
   conditional roadmap.

## What The Skill Does Not Do

The skill is not a theorem prover. It does not certify that a mathematical argument is correct. It only makes the state of the argument more
legible.

It can still fail if:

1. a false lemma is banked too early;
2. the assistant misclassifies a circular reformulation as progress;
3. diagnostics are treated as proof;
4. the human does not periodically ask for hostile audit;
5. the ledgers become too verbose to review.

The skill helps with these risks by requiring classifications and route ledgers, but it does not eliminate them.

## Suggested Improvements Before Sharing Widely

I would improve the skill in five ways before presenting it as a reusable public workflow.

1. Add a **public/private mode**. Public mode should automatically separate mathematical claims from workflow notes.
2. Add a **dependency ledger** for named support lemmas, with fields for status, proof location, and first failure point.
3. Add an **exponent or parameter ledger** for problems where feasibility depends on inequalities between several exponents.
4. Add a **review packet generator** that produces a compact GPT Pro or human-referee prompt from `latest.md`, recent failed routes, and
   the current target.
5. Add a **claim-strength checker** that flags phrases like "proved" when the current classification is only conditional.

## How To Install From Git

The shareable skill lives in this repository at:

```text
skills/self-drive-research-loop/
```

From a checkout of the repository, install it into Codex with:

```bash
mkdir -p ~/.codex/skills
cp -R skills/self-drive-research-loop ~/.codex/skills/
```

or run:

```bash
./install_self_drive_skill.sh
```

Then start a new Codex session and ask:

```text
Use $self-drive-research-loop to set up a research loop for this problem.
```

## Short Reusable Description

The self-drive research-loop skill is a Codex workflow for long mathematical investigations. It breaks an open problem into auditable
rounds, tracks live targets and failed routes, records exact reductions and diagnostics, and produces handoffs for human or model review.
Its purpose is not to automate proof discovery, but to keep a model-assisted research process honest enough that progress, failures, and
conditional dependencies remain visible.

## One-Sentence Link Text

I also used a self-drive research-loop workflow in Codex for this project; here is a short review of the workflow and what it did and did
not contribute to the argument, together with install instructions for the packaged skill.
