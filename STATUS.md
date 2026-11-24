# Verification and submission status

## Primary delivery: complete local proof checks

The current delivery selects 20 theorems in three independent configurations.
Their proof sources have compiled, and each configuration has completed all
recorded local statement/definition comparisons, axiom checks, Lean kernel
replay and NanoDa replay.

| Configuration | Selected theorems | Statement comparison and axioms | Lean kernel | NanoDa |
| --- | ---: | --- | --- | --- |
| `comparator.json` | 9 | Passed | Passed | Passed |
| `comparator-finite.json` | 4 | Passed | Passed | Passed |
| `comparator-physics.json` | 7 | Passed | Passed | Passed |

Each row is backed by `verification/<configuration-stem>/report.json` and its
logs. Configuration and toolchain copies accompany those reports. The retained
whole-development build record is `verification/serial-build-report.json`.
The central 140-declaration axiom audit also passed; its source hash and target
list are recorded in `verification/principal-axioms.json`. All audited
proofs depend only on the permitted standard axioms.

These are local proof diagnostics. The official complete mechanical-preflight
results are tracked in this repository's
[Palomar workflow runs](https://github.com/xliu2022/GHZ-unbounded-lean/actions/workflows/palomar-preflight.yml).
A passing report applies only to the exact source commit and configuration
recorded by that run. Editorial review and registration remain separate steps
for the responsible maintainer.

## Optional supplementary development

Additional finite examples, families and their dependent thresholds are
retained as an optional extension, outside the current registration scope.
The relevant conclusions had compiled in the complete development; their
exact scope and proof substitutions remain recorded in `COVERAGE_AUDIT.md`.

For `comparator-supplement.json`, the corrected statement/definition comparison
passed before the environment was lost. No completed independent Lean/NanoDa
replay report was received. After source recovery, its 397-module rebuild was
stopped intentionally when the primary scope was narrowed. This is recorded in
`verification/recovery-supplement-build.json`; it is not a failed theorem and
is not a successful supplementary replay.

The default Lake targets, serial helper and prepared preflight workflow now
select the three primary configurations. The serial helper requires explicit
`--include-supplement` to build the full retained development. Generic lemmas
from the Supplement namespace that the main finite proof uses are retained;
there is no wholesale removal of that namespace.

## Source and submission preparation

The source-layout check covers module headers, size limits, ordinary source
files, pinned public GitHub dependencies and Comparator configuration shape.
The Physics Challenge exceeds the advisory 300-line target but satisfies both
hard limits. See `verification/source-layout.json` for the latest result.

`formalization.yaml` records Xizhi Liu as formalization author and responsible
maintainer, following his explicit instruction. The public repository is
`xliu2022/GHZ-unbounded-lean`. The description records the three-configuration
primary scope, with the supplementary configuration retained as optional.
Use the exact source commit shown in a passing full-preflight report when
submitting. See `SUBMISSION.md`.
The pinned official metadata validator, source-header scan of all 817 Lean files,
and workflow-interface check passed. The evidence and validator hashes are in
`verification/publication-checks.json`; all 303 primary Lean sources match the
preserved proof checkpoint.

The official caller at `.github/workflows/palomar-preflight.yml` uses identical
immutable pins in `uses` and `pipeline_commit`. It runs only when manually
dispatched and does not submit or register an entry. The previous isolated local
launcher met the documented host
namespace restriction. No isolation or proof-checking setting was disabled.
Policy and resource findings are recorded in `verification/palomar-policy-audit.txt`
and `verification/build-scheduling-audit.txt`.
