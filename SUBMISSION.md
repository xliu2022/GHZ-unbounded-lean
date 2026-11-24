# Palomar submission

The proof sources and local evidence do not themselves create a Palomar entry.
The primary delivery has three independent configuration paths, selecting 20
theorems in total: `comparator.json`, `comparator-finite.json`, and
`comparator-physics.json`. Each corresponds to a separate possible entry.
The supplementary configuration is retained as an optional extension and is
outside the current registration scope. See `README.md` for the exact scopes.

## Submission values

| Field | Value |
| --- | --- |
| Repository | `xliu2022/GHZ-unbounded-lean` |
| Formalization author | Xizhi Liu |
| Responsible maintainer | Xizhi Liu |
| Lean project | Repository root; leave the optional project-path field blank |
| Metadata | `formalization.yaml` at the repository root |
| Comparator configuration | `comparator.json`, `comparator-finite.json`, or `comparator-physics.json` |
| Source commit | The full 40-character SHA in the passing mechanical-preflight report |
| Authorization relationship for Xizhi Liu | `I am a responsible author or maintainer` |

The author, maintainer, repository and publication authorization were supplied
explicitly by Xizhi Liu. Mathematical source authorship is recorded separately.
Each configuration requires its own submission and its own passing preflight
at the chosen source commit. Do not select `comparator-supplement.json` for the
current primary delivery.

## Official full preflight

Palomar's agent-facing instructions are at
<https://submit.palomar-registry.org/llms.txt>. The policy is at
<https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md>.
Recheck them at submission time.

The mandatory mechanical preflight is the complete reusable workflow at
`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml`, using
`mode: full`. A user-owned runner call uses `execution_profile:
palomar-standard-v1`. Pin the workflow reference and its `pipeline_commit`
input to the same authenticated full PalomarSubmission commit. The prepared
workflow pins both values to
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, read from the official repository
and cross-checked against its immutable workflow, toolchain policy and
metadata profile. The provenance record is
`verification/palomar-policy-audit.txt`.

`.github/workflows/palomar-preflight.yml` is the workflow caller. Its manual inputs
choose one of the three primary configuration paths and require an explicit
authorization relationship using an exact phrase accepted by Palomar.
The workflow does not run on a push and does not submit or register anything.
If the policy has changed by submission time, verify a new pipeline revision
and update both pinned values together.

The current ordinary submitter relationships are exactly
`I am a responsible author or maintainer` and
`I have approval from a responsible author or maintainer`.
The other accepted phrases are reserved for Palomar operator roles. Choose
the statement that truthfully describes the person making the submission;
the workflow intentionally supplies no default for this input.

The `request_id` is exactly twelve lowercase alphanumeric characters. Keep
the supplied value or replace it with another valid value. Source commit
selection in the workflow is `github.sha`, so the full run checks the actual
committed project rather than an uncommitted working directory.

Inspect the resulting mechanical report. Continue to intake only after it
reports a pass for the intended source commit and configuration. Resolve any
resource failure rather than treating an incomplete run as success.

## Submission and registration are separate

After full preflight, the official intake still checks repository access and
runs its own verification and editorial review. Confirm the repository,
commit, configuration and human authorization relationship before initiating
that process. The agent-compatible access proof and the human browser flow
are documented by the service; a browser identity must not be silently
substituted for a human's authorization.

Registration is a later decision after the review has been shown to the
responsible person. It publishes the source identity and review and creates
source-preservation references. This development session has not requested
intake, created verification tags or gists, published a review, or registered
an entry.
