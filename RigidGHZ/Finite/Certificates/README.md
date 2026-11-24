# Finite nine-vertex certificates

These files support the unrestricted upper bound on the number of perfect
matchings in a rigid 3-uniform hypergraph on nine vertices. They are proof
inputs, not trusted assertions of satisfiability or unsatisfiability.

## Mathematical meaning

The first 84 variables represent the actual 3-element subsets of `Fin 9` in
lexicographic order. The next 280 variables represent the actual partitions of
`Fin 9` into three triples. The remaining variables are thresholds for prefix
counts of the 28 triples incident with each vertex.

The initial clauses express the following consequences of ordinary
`RigidFamily H (Fin 14)` and `Uniform H 3`:

| Clause kind | Proven mathematical meaning |
| --- | --- |
| `forward`, `backward` | A partition is present exactly when all three of its edges are in `H`. |
| `cover` | Every edge of `H` belongs to a prescribed perfect matching. |
| `conflict` | Distinct perfect matchings cannot share an edge. |
| `zero`, `empty`, `step1`–`step4` | The auxiliary variables are thresholds for actual incidence prefix counts. |
| `lower`, `upper` | Every vertex has degree 14. |
| `normpos`, `normneg` | The completions of the normalized pair `{0,1}` form the interval `[2,k+2)`. |
| `fan` | If all pair codegrees are at most four, five distinct completions of one pair cannot all occur. |
| `given` | The two additional edges of the normalized perfect matching are present. |

`NineSATModel.lean` proves these statements about the original hypergraph
definitions. `NineSATAssemble.lean` uses the JSON files only to select instances
of those theorems, and verifies that their clauses match the exact CNF context
of the refutation. Changing metadata to an incorrect clause cannot bypass
Lean's type checker.

The six branches have the following normalization hypotheses:

| Branch | Pair codegree `k` | Other edges of the matching containing `{0,1,2}` | Additional assumption |
| --- | ---: | --- | --- |
| `4a` | 4 | `{3,4,5}`, `{6,7,8}` | Every pair codegree is at most 4. |
| `4b` | 4 | `{3,4,6}`, `{5,7,8}` | Every pair codegree is at most 4. |
| `5a` | 5 | `{3,7,8}`, `{4,5,6}` | None. |
| `5b` | 5 | `{3,4,7}`, `{5,6,8}` | None. |
| `6a` | 6 | `{3,4,8}`, `{5,6,7}` | None. |
| `7` | 7 | No matching normalization needed. | None. |

The pair and matching normalizations are separately proved using vertex
permutations. The four-completion hypothesis comes from a proved double count;
the reduction from arbitrary rigidity parameter `d ≥ 14` restricts the actual
prescribed matching family to 14 members.

## Kernel reconstruction

`SatLRATChunk.lean` reconstructs each RUP inference using Mathlib's LRAT proof
builder and submits the resulting ordinary theorem declaration to Lean's
kernel. Learned clauses are named, shared, and split across small source
modules to bound peak memory. There are no solver axioms, native-decision
axioms, or external-checker assumptions.

Files prefixed `nine` contain the complete generated CNF and its unpruned
solver trace. Files prefixed `core` contain the dependency-pruned CNF, matching
metadata, and the renumbered refutation used by Lean. `SHA256SUMS` records the
18 exact pruned inputs. Removing unused clauses and proof steps is an
untrusted optimization: the surviving proof must still reconstruct in Lean.

## Reproduction

The recorded traces were produced by CaDiCaL 2.1.2, included with the pinned
Lean 4.35.0-rc2 toolchain, with `--lrat --no-binary`. Run from this directory:

```sh
python3 reproduce.py generate --out /tmp/rigid-nine-certificates
python3 reproduce.py solve --out /tmp/rigid-nine-certificates --cadical /path/to/cadical
python3 reproduce.py prune --out /tmp/rigid-nine-certificates
python3 reproduce.py hashes --out /tmp/rigid-nine-certificates
```

The generator is deterministic. Different solver versions can produce
different valid refutations; acceptance requires kernel reconstruction, not
matching a solver's UNSAT response. Hashes identify the exact checked inputs
in this project. The Lean proof build itself does not run CaDiCaL.
