"""Generate finite symmetry witnesses; Lean independently checks every entry."""
from itertools import combinations, permutations
from pathlib import Path

root = Path(__file__).resolve().parents[1]
triples = [frozenset(t) for t in combinations(range(9), 3)]
parts = []
for a, b, c in combinations(range(84), 3):
    if len(triples[a] | triples[b] | triples[c]) == 9:
        parts.append((triples[a], triples[b], triples[c]))
assert len(parts) == 280
assert all(frozenset((0, 1, 2)) in p for p in parts[:10])

targets = {
    4: [((0,1,2),(3,4,5),(6,7,8)), ((0,1,2),(3,4,6),(5,7,8))],
    5: [((0,1,2),(3,7,8),(4,5,6)), ((0,1,2),(3,4,7),(5,6,8))],
    6: [((0,1,2),(3,4,8),(5,6,7))],
}

def fs(t):
    return '{' + ', '.join(map(str, t)) + '}'

def hg(p):
    return '{' + ', '.join(fs(t) for t in p) + '}'

def vec(rows):
    return '![' + ',\n  '.join('![' + ','.join(map(str,r)) + ']' for r in rows) + ']'

out = '''module

public import RigidGHZ.Finite.NineEnumeration
public import RigidGHZ.Finite.PairNormalization

/-!
# Normalizing the matching through edge 012

The following small tables fix vertices 0,1,2 and independently permute the
remaining pair-completion vertices and their complement. All table facts,
including the matching images, are checked by ordinary kernel `decide`.
-/

@[expose] public section

namespace RigidGHZ.Finite

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem partition012_first : ∀ j : Fin 280,
    ({0, 1, 2} : Finset (Fin 9)) ∈ ninePartition j → j.val < 10 := by
  decide

'''

for k, targs in targets.items():
    targsets = [frozenset(map(frozenset,t)) for t in targs]
    rows, invrows = [], []
    inside, outside = list(range(3, k+2)), list(range(k+2,9))
    for p in parts[:10]:
        found = None
        for ip in permutations(inside):
            for op in permutations(outside):
                g = list(range(9))
                for x,y in zip(inside,ip): g[x]=y
                for x,y in zip(outside,op): g[x]=y
                gp = frozenset(frozenset(g[x] for x in e) for e in p)
                if gp in targsets:
                    found = g
                    break
            if found is not None: break
        assert found is not None
        rows.append(found)
        invrows.append([found.index(x) for x in range(9)])
    out += f'''def matchingMap{k} : Fin 10 → Fin 9 → Fin 9 :=
  {vec(rows)}

def matchingInv{k} : Fin 10 → Fin 9 → Fin 9 :=
  {vec(invrows)}

theorem matchingInverse{k} : ∀ j : Fin 10,
    (∀ x, matchingInv{k} j (matchingMap{k} j x) = x) ∧
    (∀ x, matchingMap{k} j (matchingInv{k} j x) = x) := by
  decide

def matchingPerm{k} (j : Fin 10) : Equiv.Perm (Fin 9) where
  toFun := matchingMap{k} j
  invFun := matchingInv{k} j
  left_inv := (matchingInverse{k} j).1
  right_inv := (matchingInverse{k} j).2

theorem matchingPerm{k}_facts : ∀ j : Fin 10,
    matchingPerm{k} j 0 = 0 ∧ matchingPerm{k} j 1 = 1 ∧ matchingPerm{k} j 2 = 2 ∧
    (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < {k+2}) ↔
      (2 ≤ (matchingPerm{k} j x).val ∧ (matchingPerm{k} j x).val < {k+2})) ∧
    ('''
    out += ' ∨\n     '.join(
        f'relabelHypergraph (matchingPerm{k} j) (ninePartition ⟨j.val, by omega⟩) = {hg(t)}'
        for t in targs)
    out += ') := by\n  decide\n\n'
    out += f'''theorem normalize_matching{k} {{H M : Hypergraph (Fin 9)}}
    (hH : Uniform H 3) (hM : PerfectMatching H M)
    (h012 : ({{0, 1, 2}} : Finset (Fin 9)) ∈ M) :
    ∃ g : Equiv.Perm (Fin 9), g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 ∧
      (∀ x : Fin 9, (2 ≤ x.val ∧ x.val < {k+2}) ↔
        (2 ≤ (g x).val ∧ (g x).val < {k+2})) ∧
      ('''
    out += ' ∨\n       '.join(f'relabelHypergraph g M = {hg(t)}' for t in targs)
    out += f''') := by
  obtain ⟨j, rfl⟩ := ninePartition_complete hH hM
  let j' : Fin 10 := ⟨j.val, partition012_first j h012⟩
  have h := matchingPerm{k}_facts j'
  refine ⟨matchingPerm{k} j', ?_⟩
  simpa only [j'] using h

'''

out += 'end RigidGHZ.Finite\n'
(root / 'RigidGHZ/Finite/MatchingNormalization.lean').write_text(out)
