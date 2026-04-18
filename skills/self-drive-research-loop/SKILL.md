---
name: self-drive-research-loop
description: "Use when setting up, running, or improving an autonomous iterative research loop for math or theory problems, especially when the work needs round ledgers, diagnostics, failed-route guardrails, exact reductions, and handoffs to another model or researcher."
---

# Self-Drive Research Loop

## Purpose

Use this skill to turn an open-ended research problem into a disciplined autonomous loop. The loop repeatedly selects the sharpest live
target, attempts one exact reduction or diagnostic probe, records what changed, and updates guardrails so later rounds do not retread failed
routes.

This is designed for math/theory research such as Erdos-style problems, analytic number theory, combinatorics, recurrence searches, and
formalization projects where many rounds are not proofs but still sharpen the frontier.

## Core Contract

Every round must answer:

1. What exact theorem or obstruction was attacked?
2. What definitions and normalizations were used?
3. Which facts were banked and not reproved?
4. What was proved exactly, tested diagnostically, refuted, or reduced?
5. What route is now forbidden or demoted?
6. What is the smallest next theorem?

Never let diagnostics masquerade as proof. Never replace the live object with an easier ambient object unless the implication back to the
original theorem is explicit and scale-safe.

## Repository Layout

If the project has no existing convention, create:

```text
self_drive/
├── latest.md
├── handoff_latest.md
├── raw/
│   └── ROUND001_<slug>.md
├── metrics/
│   ├── round_metrics.jsonl
│   ├── route_ledger.jsonl
│   └── target_lineage.jsonl
└── tools/
    └── self_drive_status.sh
```

Use existing project conventions if present. If the repo already has `raw/`, `metrics/`, and `tools/`, continue using them.

## Round Classifications

Use exactly one primary classification per round:

```text
EXACT_IDENTITY          Correct algebraic/logical identity; may still not close.
PROVED                  Target theorem is proved at the required scale.
CONDITIONAL_REDUCTION   Target follows from a smaller stated theorem.
DIAGNOSTIC_ONLY         Numerical/computational/model evidence only.
FAILED_ROUTE            Plausible mechanism is refuted or too coarse.
CIRCULAR_REFORMULATION  Equivalent to, or stronger than, the open target.
REFUTED                 Target statement is false.
```

## Round Protocol

At the start of each round:

1. Read `latest.md`, tails of all ledgers, and the most recent raw memo.
2. State the live target and inherited forbidden routes.
3. Choose one narrow action: prove an identity, refute a mechanism, run a diagnostic, derive a smaller theorem, or stress-test a scaling
   claim.

During the round:

1. Preserve the original coupled/matched/signed object unless the reduction proves equivalence.
2. Track the target scale before using any inequality.
3. Prefer structured formulas, quotient maps, exact reindexings, and level-set identities over generic norm bounds.
4. If running code, make the probe deterministic and record command, inputs, and raw outputs.
5. If a route fails, record the precise obstruction and add it as a guardrail.

At the end of each round:

1. Write one raw memo.
2. Append one JSON object to each ledger.
3. Update `latest.md`.
4. Update `handoff_latest.md`.
5. Run available lint/index/compile checks.

## Raw Memo Template

```text
# Round N: <Short Title>

Date: YYYY-MM-DD

## Target
Exact theorem or obstruction attacked. Include the required scale.

## Setup
Definitions, normalizations, live object, excluded degeneracies.

## Banked Inputs
Facts used without reproving.

## Work Performed
Exact identities, proof attempt, diagnostic probe, or failed route.

## Results
Tables, formulas, proof statements, or counterexamples.

## Interpretation
What changed? What did not close? What became forbidden?

## Classification
One standard classification.

## Next Target
Smallest theorem or diagnostic that should be attacked next.
```

## Ledger Schemas

`round_metrics.jsonl`:

```json
{"round":1,"created_at":"YYYY-MM-DDTHH:MM:SSZ","object":"TargetTheoremName","target_scale":"exact scale","classification":"DIAGNOSTIC_ONLY","status":"short status","observed":{},"next_target":"NextTheoremName","notes":"one sentence"}
```

`route_ledger.jsonl`:

```json
{"round":1,"route":"short route name","classification":"FAILED_ROUTE","scale_gap":"none / q-loss / log-loss / circular","obstruction":"why it failed or remains open","replacement_target":"NextTheoremName","notes":"guardrail for future rounds"}
```

`target_lineage.jsonl`:

```json
{"round":1,"object":"NextTheoremName","from":"PreviousTheoremName","relation":"exact identity / diagnostic sharpening / failed route replacement","notes":"why this is now live"}
```

## Status Script

If no project script exists, create `tools/self_drive_status.sh` that prints:

```text
Latest message:
<latest.md>

Latest metric:
tail -n 1 metrics/round_metrics.jsonl

Recent routes:
tail -n 5 metrics/route_ledger.jsonl

Live target:
tail -n 1 metrics/target_lineage.jsonl
```

Use the script for status updates so reports do not drift from the ledgers.

## Guardrails

Carry guardrails forward explicitly:

- Do not repeat `FAILED_ROUTE` mechanisms unless the new attempt changes the object or scale.
- Do not use an inequality that loses the target power of the main parameter.
- Do not replace a matched/coupled/signed object by an ambient frame, average, or absolute-value theorem without proving the implication is
  scale-safe.
- Do not treat bounded numerical tables as proof.
- Do not split into "bad" and "good" pieces if the good piece requires an equally hard theorem.
- Do not call a reformulation progress unless it is smaller, exact, or kills a route.
- When a theorem is equivalent to the original target in new coordinates, label it `CIRCULAR_REFORMULATION` or `EXACT_IDENTITY`, not a
  breakthrough.

## Diagnostic Probe Pattern

For computational rounds:

1. State the theorem-shaped quantity.
2. State the predicted scale.
3. Test stress instances large enough to expose the suspected loss.
4. Record raw counts, top masses, weak tails, max values, and support sizes.
5. Decide whether the result supports, refutes, or redirects the theorem.
6. If the mass concentrates, move to counting/classification rather than diffuse estimates.

## Handoff Prompt Template

When handing the frontier to another model, use:

```text
We are running a self-drive research loop on <problem>.

Current live target:
<TargetTheoremName>

Required scale:
<scale>

Definitions:
<minimal exact definitions>

Banked exact inputs:
<facts not to reprove>

Latest exact reductions:
<identities/equivalences>

Latest diagnostics:
<tables and what they imply>

Failed or forbidden routes:
<guardrails>

Your task:
Attack the live target. If you cannot prove it, isolate the smallest exact next theorem.

Required response format:
1. Exact theorem attacked.
2. Definitions and normalizations used.
3. Banked inputs used.
4. Full proof attempt with identities justified.
5. Degeneracy audit.
6. Consequence chain back to the main theorem.
7. First failure point.
8. Smallest next theorem, stated precisely.
9. Final verdict: PROVED, CONDITIONAL_REDUCTION, DIAGNOSTIC_ONLY, FAILED_ROUTE, or REFUTED.

Do not use any failed route listed above unless you explain what materially changed.
```

## Erdos-Style Setup

For an Erdos-style problem, define these before the first round:

```text
Main theorem:
Exact target scale:
Objects being counted:
Allowed transformations:
Known extremal examples:
Known forbidden proof routes:
Computable diagnostics:
Stress parameters:
```

The loop succeeds when it proves the theorem, finds a counterexample, or reduces the live target to a smaller named theorem with a clear
arithmetic/combinatorial obstruction.
