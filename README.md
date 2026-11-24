# Rigid hypergraphs and unbounded GHZ dimension

Formalization author and responsible maintainer: **Xizhi Liu**.

Public repository: [xliu2022/GHZ-unbounded-lean](https://github.com/xliu2022/GHZ-unbounded-lean).
中文说明见 [README_zh.md](README_zh.md).

This repository contains Lean proofs of the principal mathematical results of
Heng Li and Xizhi Liu, *Unbounded GHZ dimension from fixed-order multiphoton
sources*, together with its Supplemental Material. The development constructs
ordinary finite simple hypergraphs, proves that their listed perfect matchings
are exhaustive, and connects those hypergraphs to a finite coefficient model
of coherent photon sources and exact photon-number postselection.

## Current delivery scope

The primary delivery selects **20 theorems in three configurations**:
`comparator.json`, `comparator-finite.json`, and `comparator-physics.json`.
All three have passed the recorded local statement/definition comparison,
axiom audit, Lean kernel replay and NanoDa replay.

The additional supplementary finite examples, families and dependent thresholds
are retained as an optional extension. Their fourth configuration is outside
the current registration scope and is not a completion gate for this delivery.
Its interrupted independent replay is not described as a pass. The retained
main finite extrema still include their complete necessary finite proofs.

[`STATUS.md`](STATUS.md) records the current verification and submission state.

The code fixes Lean and Mathlib in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Its proofs use only `propext`, `Classical.choice`, and
`Quot.sound`. Deliberate `sorry` declarations occur in the independent Challenge
statement files only. Solution modules do not import Challenge modules.

## Mathematical results

For an `r`-uniform hypergraph, a perfect matching covers each vertex exactly
once. On a nonempty vertex set, a `d`-rigid hypergraph has exactly `d` perfect
matchings, whose edge sets partition the entire hypergraph. The definitions
are in `RigidGHZ/Basic.lean`.
In particular, rigidity is proved for the produced examples; it is not an
assumed completeness certificate hidden in a different notion of matching.

The generic `RigidFamily` interface is an indexed exhaustive family. On an
empty vertex type, repeated empty matching classes are not distinguished by
edge-disjointness. Every advertised positive-size existence and physical
result excludes that degeneracy; the generic upper bounds at size zero are
trivial inequalities. The exact-count interpretation above concerns nonempty
vertex sets, as in the paper's extremal problem.

The principal results include:

- At every positive balanced part size `m` and every `r ≥ 3`, an actual rigid
  hypergraph with dimension at least
  `(m / (128*(r-2)^3))^(2*(r-2)/7)`. The construction includes the four parameter
  regimes, geometric anchor allocation, support packing, and the product of
  the actual factors.
- Exact prescribed dimension `d ≥ 2` at part size
  `ceil(128*(r-2)^3*d^(7/(2*(r-2))))`, and at every larger part size, with
  exactly `d*m` source configurations.
- The weighted shadow inequality, its balanced multipartite version, the
  exact floor bounds, and logarithmic upper bounds. The asymptotic modules
  prove the leading unrestricted envelope constant `1/(r-1)!`, the
  little-o consequence, and explicit path-resource bounds.
- The exact finite values `f_3(9)=13`, `f_3(6)=10`, and `g_3(3)=6`, including
  uniqueness of the balanced extremal example up to the stated relabeling.
  General two-edge extrema and the elementary degree bounds are also proved.
- Supplementary grafting, cyclic and signature lifts, linear lifts, periodic
  transfer formulas, all-size six- and ten-matching families, and the printed
  balanced, unrestricted, and linear existence thresholds.
- The exact source-state support criterion, phase correction and normalization
  to GHZ, its explicit equal-coefficient Schmidt decomposition across every
  nontrivial cut, and the unique equal-weight optimum at source probability `1/d`.
  Additional modules prove logarithmic success asymptotics, rejection of
  multiple emissions, and finite independent-event formulas.

Extremal results are usually stated as actual witnesses plus universal upper
bounds, rather than by defining numeric functions named `f`, `g`, or `ell`.
These are the corresponding extremal assertions with their quantifiers exposed.

## Scope and proof fidelity

[`COVERAGE_AUDIT.md`](COVERAGE_AUDIT.md) maps the paper and supplement to actual
Lean declarations, records their compilation status, and identifies additional
claims that are not separately formalized. That table is the detailed scope
record. This repository does not claim a literal translation of every sentence,
physical implementation discussion, historical statement, decimal approximation,
or external computer program in the source materials.
The five displayed three-significant-figure optimal probabilities in Section 5
are specifically certified by exact rational intervals in
`RigidGHZ/SourceModel/NumericalProbabilities.lean`.

Some proofs deliberately differ from the paper. In particular, the nine-vertex
upper bound uses normalized, kernel-reconstructed SAT refutations; the all-size
six- and eight-matching existence results use proved seed families and grafting;
and probability optimization uses a product-of-branch-probabilities argument.
The final ordinary mathematical conclusions, and the bridges from every finite
certificate to those conclusions, are part of the Lean development. An
alternative proof of a final theorem is not represented as a formalization of
each intermediate lemma in the original proof.

The physical model records the explicitly stated assumptions: coherent
independent source amplitudes, exact photon-number selection, and, where used,
independent flagged detection or detection after ideal selection. It does not
assert that unflagged preselection loss has the same success formula.

## Palomar statement files

Each configuration is a separate potential registry entry. The three primary
configurations can refer to the same public repository and immutable commit.
The supplementary configuration is retained for a possible later extension.

| Configuration | Challenge / Solution | Recorded mathematical scope |
| --- | --- | --- |
| `comparator.json` | `Challenge` / `Solution` | Quantitative growth, prescribed dimension, shadow, floor and logarithmic upper bounds |
| `comparator-finite.json` | `FiniteChallenge` / `FiniteSolution` | The three finite exact values and balanced uniqueness |
| `comparator-physics.json` | `PhysicsChallenge` / `PhysicsSolution` | Actual source states, support, phase correction, GHZ realization and optimum |
| `comparator-supplement.json` (optional extension) | `SupplementChallenge` / `SupplementSolution` | Concrete supplementary families, threshold theorems and unrestricted finite witnesses; outside current registration scope |

Challenge imports are restricted to canonical Mathlib. Their ordinary
definitions are copied into the statement file so the full statement is
auditable there. Comparator checks those definitions and the selected
declaration types against the corresponding Solution proof closures.

## Reproducing the build

Install Lean's ordinary Elan/Lake toolchain manager and Python 3.11 or later,
then run from the repository root. The build/check helpers use Python's standard
library. The manifest pins all dependencies; do not silently update their revisions.

```sh
lake exe cache get
python3 scripts/build_serial.py --all
python3 scripts/check_source.py
```

The serial prebuild visits the three primary Solution/Challenge dependency
closures in dependency order and then builds those six library targets.
It sets `LEAN_NUM_THREADS=1` for its local process tree.
The package's `weakLeanArgs = ["-j1"]` also limits each local Lean compiler
to one worker; this does not limit the number of modules Lake can launch.
Building all independent certificate targets concurrently can
exceed a machine's available memory. For incremental work, omit `--all` to
prebuild only modules whose missing/stale local traces predict a rebuild;
the authoritative Lake build for the selected scope still follows.
To build the entire retained development, explicitly add `--include-supplement`.
A finite-only prebuild is
also available as `scripts/build_finite_certificates.py`.
Every finite proof is checked during compilation; CaDiCaL is not run by the
proof build. The `.cnf`, `.lrat`, metadata and Lean source inputs are committed
source, while all compiled artifacts belong under `.lake`.

Certificate generation and trust boundaries are documented in
`RigidGHZ/Finite/Certificates/README.md` and
`RigidGHZ/Finite/ExactCoverCertificates/README.md`. The solver, JSON parser,
generators and pruning scripts are untrusted: reconstruction must produce
ordinary Lean proof terms for the exact semantic clauses.

## Independent proof checks and their limits

The following runs fresh exports, the toolchain's unchanged Comparator
statement comparison and axiom checks, Lean's kernel checker, and NanoDa:

```sh
python3 scripts/check_exports.py comparator.json
python3 scripts/check_exports.py comparator-finite.json
python3 scripts/check_exports.py comparator-physics.json
```

The optional supplementary replay can be requested separately with
`python3 scripts/check_exports.py comparator-supplement.json`; it is not part
of the primary delivery's completed three-configuration checks.

The machine-readable reports and concise logs from successful runs are in
`verification/`. Full transient proof exports are under `.lake/verification/`
and are deliberately excluded from the source package. Reports record export
hashes and sizes, toolchain/configuration identity, exit statuses, and times.
Only an actual successful report should be described as a completed check.

These are **local export diagnostics**, not Palomar's full isolated preflight,
AI editorial review, or registration. In the original development environment,
the official isolated Comparator launcher was blocked by the host's inability
to create a `NETLINK_ROUTE` socket for its Bubblewrap network namespace. No
sandbox setting was disabled or patched. The same isolated workflow must be
run in a supported environment. Palomar additionally requires its complete
reusable `PalomarRegistry/PalomarSubmission` workflow with `mode: full`, pinned
to an exact pipeline commit. A standalone Comparator run is not that workflow.
The official caller and submission instructions are documented in `SUBMISSION.md`.
Its [GitHub Actions runs](https://github.com/xliu2022/GHZ-unbounded-lean/actions/workflows/palomar-preflight.yml)
provide the full-preflight evidence for each exact commit and configuration.
Use a run whose mechanical report says `status: pass`; a workflow's existence
or the older local reports do not establish that result.

## Submission metadata

[`formalization.yaml`](formalization.yaml) records **Xizhi Liu** as the human
formalization author and responsible maintainer, as explicitly supplied by him.
The mathematical source authors are recorded separately. AI contributions are
disclosed in `automation` and `PRODUCTION.md`.
The pinned official metadata validator, complete source-header scan and workflow
interface check passed; see [publication-checks.json](verification/publication-checks.json).

The checked-in metadata can be regenerated and the source layout checked with:

```sh
python3 scripts/finalize_metadata.py --author 'Xizhi Liu' --maintainer 'Xizhi Liu'
python3 scripts/check_source.py --require-metadata
```

For Palomar, use repository `xliu2022/GHZ-unbounded-lean`, the exact 40-character
commit that passed the full preflight, one of the three primary configuration
paths, and root metadata `formalization.yaml`. Each configuration is a separate
submission. Official editorial review and registration are subsequent steps
for the responsible maintainer.

## Production and review

[`PRODUCTION.md`](PRODUCTION.md) records the automated proof-development roles,
the finite-certificate process, the checks performed, and the distinction
between machine checking and human mathematical review. The repository's
formalization code is provided under Apache-2.0. Cited mathematical sources,
user-supplied paper copies, and external dependencies retain their own rights
and licenses.
