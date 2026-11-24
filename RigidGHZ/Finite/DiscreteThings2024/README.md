# The 2024 nine-vertex example

The list comes directly from the comment by **discrete_things**, dated
5 November 2024 at 18:37 UTC, under the author's question
[3-uniform hypergraphs with only disjoint perfect matchings](https://math.stackexchange.com/questions/4994589/3-uniform-hypergraphs-with-only-disjoint-perfect-matchings)
on Mathematics Stack Exchange. This is a separate source from Mario Krenn's
2019 MathOverflow question cited earlier in the paper.

`source.json` records the thirteen matching rows exactly as numerical data,
with both the source labels 1–9 and the Lean labels 0–8. The latter subtract
one from every original vertex label. The row order is unchanged.
The original page was retrieved on 23 November 2026.

`Finite/NineDiscreteThings.lean` defines the graph from these actual triples
and verifies its ordinary thirteen-rigidity. `Finite/NineNonisomorphism.lean`
counts hyperedges whose three vertex pairs all have codegree four and
proves that this number is invariant under every vertex equivalence. The
paper's algebraic table has three such hyperedges; this list has two.
These are internally checked properties of the explicit edge sets, independent
of any unverified assertion on the source page.
