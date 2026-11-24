# Production and review account

## Origin

The user requested a Lean formalization of Heng Li and Xizhi Liu's
*Unbounded GHZ dimension from fixed-order multiphoton sources* and its
Supplemental Material, prepared for Palomar's requirements. The provided
paper sources are retained under `paper/` for statement mapping. The
mathematical results are source-based, not claimed here as new results first
introduced by the formalization.

## Automated work

ChatGPT, using GPT-6 Astra Pro and collaborating agents in the same session,
performed the substantive proof development, including definition design,
proof decomposition, Lean proof writing, compiler-guided repairs, finite
certificate generation and reconstruction, supplementary threshold assembly,
coverage mapping, and preparation of the statement files and documentation.
Agents divided the geometry and combinatorial foundations, source/selector
and lift arguments, and finite exact-cover/SAT work. Their changes were
integrated into the same pinned Lean project.

The production process did not reconstruct a reliable total token cost or
wall-clock accounting; none is asserted. Running Lean and inspecting its
output is part of automated development, not evidence of a separate human
review. No human expert review or author verification of the complete Lean
development has been recorded in this session.

## Finite proofs

Small finite checks use ordinary kernel reduction. Larger nonexistence and
completeness checks use CaDiCaL-generated LRAT/RUP traces. Lean code proves
what every initial Boolean clause means about an ordinary perfect matching,
proves the necessary relabeling/translation normalizations, reconstructs the
retained proof steps, and concludes the ordinary hypergraph theorem.

The solver's exit code is not a theorem. The solver executable, parsers,
certificate pruning, generators and JSON metadata are not added to the
axiom set. A changed certificate must still reconstruct proof terms with
the required types. Axiom audits traverse the actual declarations, including
the reconstructed finite proofs. No Solution theorem may depend on `sorryAx`,
`Lean.ofReduceBool`, an arbitrary seed-completeness axiom, or a solver axiom.

## Fidelity and scope

The results use standard finite hypergraphs, exact vertex coverage, and
exhaustive matching families. Alternative coordinate, selector, transfer,
or Boolean representations have proved bridges to these definitions.
Finite seed existence is supplied explicitly rather than remaining as an
unproved premise of the final threshold results.

Proof substitutions and all separately identified omissions are listed in
`COVERAGE_AUDIT.md`. The final upper bound on nine vertices has a different
proof from the paper's Appendix B. All-size existence statements may have
grafted witnesses different from the printed modular family. These facts
must remain visible in any publication or registry description.

## Verification evidence

The current primary delivery selects 20 theorems in the main, finite-extremal,
and physics configurations. All three completed the recorded local independent
checks. Supplementary finite examples and their dependent thresholds remain
available as an optional extension; their interrupted fourth replay is not
claimed as completed and is outside the current delivery scope.

The pinned toolchain compiles the substantive proof modules. `RigidGHZ/AxiomAudit.lean`
and the finite-specific audits restrict the axiom dependencies of the
principal results. `scripts/check_source.py` checks a documented subset of
the source-layout requirements; it does not replace registry validation.

`scripts/check_exports.py` uses the unchanged toolchain Comparator comparison
and axiom functions, followed by Lean's export checker and NanoDa. Successful
per-configuration reports are retained under `verification/`. Their
`palomar_full_preflight` field is deliberately false, because this separate
diagnostic sequence does not run the registry's complete isolated workflow.

The official isolated launcher encountered a host namespace restriction:
Bubblewrap could not create a `NETLINK_ROUTE` socket. The development did
not disable that isolation. Official preflight, editorial review and
registration remain distinct external steps and must not be inferred from
local compilation or diagnostic success.

## Human responsibility

Xizhi Liu explicitly identified himself as the human formalization author and
responsible maintainer and authorized publication at
`https://github.com/xliu2022/GHZ-unbounded-lean`. The finalized
`formalization.yaml` records that instruction. Codex assisted with packaging,
metadata validation and the official mechanical-preflight setup, following the
root-project layout of his existing Lean repositories. No independent human
mathematical review is inferred from authorship or publication authorization.
The root Apache-2.0 license concerns this repository's formalization code;
it does not relicense the mathematical sources or dependencies.
