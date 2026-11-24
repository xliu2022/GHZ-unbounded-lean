#!/usr/bin/env python3
"""Generate exact-cover CNFs, solve, prune LRAT traces, and emit Lean data.

The solver and this script are untrusted. ExactCoverSAT proves the meaning of
the initial clauses; Lean reconstructs every retained LRAT inference.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
NORMALIZED = {'A29', 'A31', 'A41', 'A47'}


def generate(name, data, out):
    n, rows = data['n'], data['rows']
    edges = [set(edge) for row in rows for edge in row]
    size = n // 3
    clauses, metadata = [], []
    for v in range(n):
        clauses.append([i+1 for i, edge in enumerate(edges) if v in edge])
        metadata.append(['cover', v])
    for i, j in itertools.combinations(range(len(edges)), 2):
        common = edges[i] & edges[j]
        if common:
            clauses.append([-i-1, -j-1])
            metadata.append(['conflict', i, j, min(common)])
    for r in range(len(rows)):
        clauses.append([-i-1 for i in range(r*size, (r+1)*size)])
        metadata.append(['exclude', r])
    (out / f'{name}.cnf').write_text(
        f'p cnf {len(edges)} {len(clauses)}\n' +
        ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses))
    (out / f'{name}.json').write_text(json.dumps(metadata, separators=(',', ':')))


def solve(name, out, cadical):
    with (out / f'{name}.solver.log').open('w') as log:
        result = subprocess.run([cadical, '--lrat', '--no-binary',
                                 str(out / f'{name}.cnf'), str(out / f'{name}.lrat')],
                                stdout=log, stderr=subprocess.STDOUT)
    if result.returncode != 20:
        raise RuntimeError(f'{name}: solver exit {result.returncode}; expected UNSAT (20)')


def prune(name, out):
    lines = (out / f'{name}.cnf').read_text().splitlines()
    nvars, count = map(int, lines.pop(0).split()[2:])
    metadata = json.loads((out / f'{name}.json').read_text())
    proofs, order, last = {}, [], None
    for line in (out / f'{name}.lrat').read_text().splitlines():
        tokens = line.split()
        if tokens[1] == 'd':
            continue
        values = list(map(int, tokens))
        clause_id, end = values[0], values.index(0)
        literals, hints = values[1:end], values[end+1:-1]
        if not all(h > 0 for h in hints):
            raise ValueError('Only RUP traces with positive LRAT hints are supported')
        proofs[clause_id] = literals, hints
        order.append(clause_id)
        if not literals:
            last = clause_id
    if last is None:
        raise ValueError('Trace contains no empty clause')
    needed, stack = set(), [last]
    while stack:
        clause_id = stack.pop()
        if clause_id in needed:
            continue
        needed.add(clause_id)
        if clause_id > count:
            stack.extend(proofs[clause_id][1])
    inputs = sorted(i for i in needed if i <= count)
    derived = [i for i in order if i in needed]
    rename = {old: new+1 for new, old in enumerate(inputs+derived)}
    (out / f'{name}.core.cnf').write_text(
        f'p cnf {nvars} {len(inputs)}\n' + ''.join(lines[i-1]+'\n' for i in inputs))
    (out / f'{name}.core.json').write_text(
        json.dumps([metadata[i-1] for i in inputs], separators=(',', ':')))
    with (out / f'{name}.core.lrat').open('w') as trace:
        for clause_id in derived:
            literals, hints = proofs[clause_id]
            trace.write(' '.join(map(str, [rename[clause_id], *literals, 0,
                                          *(rename[h] for h in hints), 0]))+'\n')
    print(name, 'initial', len(inputs), 'derived', len(derived), flush=True)


def emit_data(name, data, destination):
    n, rows = data['n'], data['rows']
    edges = [edge for row in rows for edge in row]
    size, e, d = n//3, len(edges), len(rows)
    if 'm' in data:
        m = data['m']
        vertex_type = f'Fin 3 × ZMod {m}'
        vertex = lambda v: f'({v//m},{v % m})'
        vertex_fn = '(#['+','.join(vertex(v) for v in range(n))+f'] : Array ({vertex_type}))[i.val]!'
        extra_import = 'public import RigidGHZ.Supplement.AffineSeed\n'
        if m >= 23:
            extra_import += 'public import RigidGHZ.Finite.ExactCoverIndex\n'
    else:
        vertex_type = f'Fin {n}'
        vertex = str
        vertex_fn = 'i'
        extra_import = ''
    edge_lines = [f'  {{{",".join(vertex(v) for v in edge)}}}' for edge in edges]
    through_lines = [f'  [{",".join(str(i) for i, edge in enumerate(edges) if v in edge)}]'
                     for v in range(n)]
    row_lines = [f'  [{",".join(map(str, range(r*size,(r+1)*size)))}]' for r in range(d)]
    source = f'''module

public import RigidGHZ.Finite.ExactCoverSAT
{extra_import}
/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData ({vertex_type}) {n} {e} {d} where
  vertex i := {vertex_fn}
  edge i := (#[(
'''  # Finset literals are kept one per line for review against the source table.
    source = source[:-2] + '\n' + ',\n'.join(edge_lines) + f'] : Array (Finset ({vertex_type})))[i.val]!\n'
    source += '  through i := (#[\n'+',\n'.join(through_lines)+f'] : Array (List (Fin {e})))[i.val]!\n'
    source += '  row i := (#[\n'+',\n'.join(row_lines)+f'] : Array (List (Fin {e})))[i.val]!\n\n'
    if data.get('m', 0) >= 23:
        m, lam = data['m'], data['lam']
        shift_values = ','.join(map(str, data['shifts']))
        source += f'''def indexShift (r : Fin {d}) : ZMod {m} :=
  (#[{shift_values}] : Array (ZMod {m}))[r.val]!
def indexRow (i : Fin {e}) : Fin {d} := ⟨i.val / {m}, by omega⟩
def indexColumn (i : Fin {e}) : ZMod {m} := (i.val % {m} : ℕ)

theorem affine_edge_formula : ∀ i, data.edge i = tupleEdge
    (fun j => Supplement.Affine.baseMap ({lam} : ZMod {m}) (indexShift (indexRow i)) j (indexColumn i)) := by
  decide +kernel

theorem index_shift_injective : Function.Injective indexShift := by
  unfold Function.Injective
  decide +kernel

theorem index_parts_injective : Function.Injective (fun i => (indexRow i,indexColumn i)) := by
  intro i j h
  have hd := congrArg (fun x : Fin {d} × ZMod {m} => x.1.val) h
  have hm := congrArg (fun x : Fin {d} × ZMod {m} => x.2.val) h
  change i.val / {m} = j.val / {m} at hd
  have hm' : i.val % {m} = j.val % {m} := by
    simpa [indexColumn,ZMod.val_natCast] using hm
  apply Fin.ext
  omega

theorem table_uniform : ∀ i, (data.edge i).card = 3 := by decide +kernel

theorem table_injective : Function.Injective data.edge := by
  exact affine_table_injective ({lam} : ZMod {m}) indexShift indexRow indexColumn data.edge
    index_shift_injective index_parts_injective affine_edge_formula

theorem table_through : ∀ v i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
  decide +kernel

theorem table_counts : ∀ r, ∀ v : Fin 3 × ZMod {m},
    ((data.row r).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_perfect : ∀ r, PerfectMatching data.host (data.matching r) := by
  intro r
  exact exactCover_perfect_of_indices data table_injective r (table_counts r)

theorem table_index_disjoint : Pairwise (fun r s => Disjoint (data.row r).toFinset (data.row s).toFinset) := by
  unfold Pairwise
  decide +kernel

theorem table_disjoint : Pairwise (fun r s => Disjoint (data.matching r) (data.matching s)) := by
  exact exactCover_disjoint_of_indices data table_injective table_index_disjoint

theorem table_index_cover : ∀ i, ∃ r, i ∈ data.row r := by decide +kernel

theorem table_covers : data.host = Finset.univ.biUnion data.matching :=
  exactCover_covers_of_indices data table_index_cover

theorem valid : ExactCoverValid data :=
  ⟨table_uniform,table_injective,table_through,table_perfect,table_disjoint,table_covers⟩

theorem uniform : Uniform data.host 3 := valid.host_uniform

'''
    else:
        source += '''theorem valid : ExactCoverValid data := by
  constructor
  · decide +kernel
  · unfold Function.Injective
    decide +kernel
  · decide +kernel
  · unfold PerfectMatching
    decide +kernel
  · unfold Pairwise
    decide +kernel
  · decide +kernel

theorem uniform : Uniform data.host 3 := valid.host_uniform

'''
    source += f'end RigidGHZ.Finite.Seeds.{name}\n'
    if data.get('m', 0) >= 41:
        groups = (n+7)//8
        old = '''theorem table_through : ∀ v i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
  decide +kernel
'''
        replacement = ''
        for group in range(groups):
            replacement += f'''theorem table_through_{group} : ∀ v : Fin {n},
    {group*8} ≤ v.val → v.val < {(group+1)*8} →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

'''
        replacement += f'''theorem table_through : ∀ v i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
  have checks : ∀ b : Fin {groups}, ∀ v : Fin {n},
      b.val*8 ≤ v.val → v.val < (b.val+1)*8 →
      ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
    intro b
    fin_cases b
'''
        replacement += ''.join(f'    · exact table_through_{g}\n' for g in range(groups))
        replacement += f'''  intro v i hi
  exact checks ⟨v.val/8,by omega⟩ v
    (by change (v.val/8)*8 ≤ v.val; omega)
    (by change v.val < (v.val/8+1)*8; omega) i hi
'''
        source = source.replace(old, replacement)
        old = f'''theorem table_counts : ∀ r, ∀ v : Fin 3 × ZMod {m},
    ((data.row r).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel
'''
        replacement = ''
        for row in range(d):
            replacement += f'''theorem table_counts_{row} : ∀ v : Fin 3 × ZMod {m},
    ((data.row {row}).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

'''
        replacement += f'''theorem table_counts : ∀ r, ∀ v : Fin 3 × ZMod {m},
    ((data.row r).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by
  intro r
  fin_cases r
'''
        replacement += ''.join(f'  · exact table_counts_{r}\n' for r in range(d))
        source = source.replace(old, replacement)
        old = '''theorem table_index_disjoint : Pairwise (fun r s => Disjoint (data.row r).toFinset (data.row s).toFinset) := by
  unfold Pairwise
  decide +kernel
'''
        replacement = ''
        for row in range(d):
            replacement += f'''theorem table_index_disjoint_{row} : ∀ s : Fin {d}, {row} ≠ s →
    Disjoint (data.row {row}).toFinset (data.row s).toFinset := by decide +kernel

'''
        replacement += '''theorem table_index_disjoint : Pairwise (fun r s => Disjoint (data.row r).toFinset (data.row s).toFinset) := by
  intro r s hrs
  fin_cases r
'''
        replacement += ''.join(f'  · exact table_index_disjoint_{r} s hrs\n' for r in range(d))
        source = source.replace(old, replacement)
    destination.mkdir(parents=True, exist_ok=True)
    (destination / f'{name}Data.lean').write_text(source)


def emit_proof(name, data, out, destination):
    steps = len((out / f'{name}.core.lrat').read_text().splitlines())
    folder = destination / f'{name}Proof'
    folder.mkdir(parents=True, exist_ok=True)
    head = f'''module

public import RigidGHZ.Finite.SatLRATPremises

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context unsat (include_str "../../ExactCoverCertificates/{name}.core.cnf")
kernel_lrat_premises unsat (include_str "../../ExactCoverCertificates/{name}.core.cnf")
end RigidGHZ.Finite.Seeds.{name}
'''
    (folder / 'Context.lean').write_text(head)
    previous = f'RigidGHZ.Finite.Seeds.{name}Proof.Context'
    for k, start in enumerate(range(0, steps, 1000)):
        stop = min(start+1000, steps)
        if data.get('m', 0) >= 37:
            emit_direct_chunk(name, name, previous, k, start, stop, folder, out)
        else:
            (folder / f'Chunk{k:03}.lean').write_text(f'''module

public import {previous}

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/{name}.core.cnf")
  (include_str "../../ExactCoverCertificates/{name}.core.lrat") {start} {stop}
end RigidGHZ.Finite.Seeds.{name}
''')
        previous = f'RigidGHZ.Finite.Seeds.{name}Proof.Chunk{k:03}'
    final = f'''module

public import RigidGHZ.Finite.Seeds.{name}Data
public import {previous}
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/{name}.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin {len(data['rows'])}) :=
  valid.family complete

theorem rigid : IsRigid data.host {len(data['rows'])} := ⟨family⟩

'''
    if 'm' not in data:
        final += f'''theorem witness : ∃ H : Hypergraph (Fin {data['n']}),
    Uniform H 3 ∧ IsRigid H {len(data['rows'])} := ⟨data.host,uniform,rigid⟩

'''
    final += f'end RigidGHZ.Finite.Seeds.{name}\n'
    (destination / f'{name}.lean').write_text(final)


def emit_direct_chunk(case, namespace, previous, k, start, stop, folder, out):
    proof_lines = (out / f'{case}.core.lrat').read_text().splitlines(keepends=True)
    (out / f'{case}.chunk{k:03}.lrat').write_text(''.join(proof_lines[start:stop]))
    (folder / f'Chunk{k:03}.lean').write_text(f'''module

public import {previous}
public import RigidGHZ.Finite.SatLRATDirect

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{namespace}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_direct unsat (include_str "../../ExactCoverCertificates/{case}.chunk{k:03}.lrat")
end RigidGHZ.Finite.Seeds.{namespace}
''')


def emit_facts(name, data, destination):
    if 'm' not in data:
        return
    m, lam, shifts = data['m'], data['lam'], data['shifts']
    d, e = len(shifts), len(shifts)*m
    values = ','.join(map(str, shifts))
    source = f'''module

public import RigidGHZ.Finite.Seeds.{name}Data

/-! Kernel-checked identification of the explicit table with the paper's affine
formulas, including the ordering facts used in translation normalization. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def shifts : Finset (ZMod {m}) := {{{values}}}
def shift (r : Fin {d}) : ZMod {m} := (#[{values}] : Array (ZMod {m}))[r.val]!
def rowIndex (i : Fin {e}) : Fin {d} := ⟨i.val / {m}, by omega⟩
def column (i : Fin {e}) : ZMod {m} := (i.val % {m} : ℕ)
def rootIndex (r : Fin {d}) : Fin {e} := ⟨r.val * {m}, by omega⟩

theorem shift_mem : ∀ r, shift r ∈ shifts := by decide +kernel

theorem shift_surjective : ∀ s : shifts, ∃ r, shift r = s.val := by decide +kernel

theorem host_eq : data.host = baseGraph ({lam} : ZMod {m}) shifts := by decide +kernel

theorem matching_eq : ∀ r, data.matching r =
    coordinateMatching (baseMap ({lam} : ZMod {m}) (shift r)) := by decide +kernel

theorem edge_eq : ∀ i, data.edge i =
    tupleEdge (fun j => baseMap ({lam} : ZMod {m}) (shift (rowIndex i)) j (column i)) := by
  decide +kernel

theorem root_edge_eq : ∀ r, data.edge (rootIndex r) =
    tupleEdge (fun j => baseMap ({lam} : ZMod {m}) (shift r) j 0) := by decide +kernel

theorem lower_shift : ∀ r i, i.val < r.val * {m} →
    (shift (rowIndex i)).val < (shift r).val := by decide +kernel

end RigidGHZ.Finite.Seeds.{name}
'''
    if m >= 19:
        source = source.replace(f'public import RigidGHZ.Finite.Seeds.{name}Data\n',
            f'public import RigidGHZ.Finite.Seeds.{name}Data\npublic import RigidGHZ.Finite.ExactCoverIndex\n')
        old_host = f'theorem host_eq : data.host = baseGraph ({lam} : ZMod {m}) shifts := by decide +kernel\n\n'
        source = source.replace(old_host, '')
        old_rows = f'''theorem matching_eq : ∀ r, data.matching r =
    coordinateMatching (baseMap ({lam} : ZMod {m}) (shift r)) := by decide +kernel
'''
        new_rows = ''
        for r in range(d):
            new_rows += f'''theorem matching_eq_{r} : data.matching {r} =
    coordinateMatching (baseMap ({lam} : ZMod {m}) (shift {r})) := by decide +kernel

'''
        new_rows += f'''theorem matching_eq (r : Fin {d}) : data.matching r =
    coordinateMatching (baseMap ({lam} : ZMod {m}) (shift r)) := by
  fin_cases r
'''
        new_rows += ''.join(f'  · exact matching_eq_{r}\n' for r in range(d))
        new_rows += f'''
theorem host_eq : data.host = baseGraph ({lam} : ZMod {m}) shifts :=
  affine_host_eq_of_rows data ({lam} : ZMod {m}) shifts shift shift_mem shift_surjective
    matching_eq {'table_covers' if m >= 23 else 'valid.covers'}
'''
        source = source.replace(old_rows, new_rows)
        if m >= 23:
            source = source.replace(f'''    tupleEdge (fun j => baseMap ({lam} : ZMod {m}) (shift (rowIndex i)) j (column i)) := by
  decide +kernel''', f'''    tupleEdge (fun j => baseMap ({lam} : ZMod {m}) (shift (rowIndex i)) j (column i)) := by
  exact affine_edge_formula''')
    (destination / f'{name}Facts.lean').write_text(source)
    if m <= 7:
        return  # AffineSmallSeeds integration is owned by the symbolic-lift agent.
    source = f'''module

public import RigidGHZ.Finite.Seeds.{name}
public import RigidGHZ.Finite.Seeds.{name}Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
open RigidGHZ.Supplement.Affine

theorem seed : Seed ({lam} : ZMod {m}) shifts where
  unit_left := (ZMod.isUnit_iff_coprime {lam} {m}).mpr (by decide)
  unit_right := by
    change IsUnit ({lam+1} : ZMod {m})
    exact (ZMod.isUnit_iff_coprime {lam+1} {m}).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.{name}
'''
    (destination / f'{name}Seed.lean').write_text(source)


def normalize(name, data, out, destination, cadical):
    """Normalize the least present shift to the edge at first coordinate zero.

    Affine.normalize_counterexample supplies these assumptions for an arbitrary
    counterexample. Each branch therefore contains only justified unit clauses.
    """
    m, d, lam = data['m'], len(data['shifts']), data['lam']
    e = m*d
    original = (out / f'{name}.cnf').read_text().splitlines()
    nv, nc = map(int, original[0].split()[2:])
    base_metadata = json.loads((out / f'{name}.json').read_text())
    branches = []
    for r in range(d):
        case = f'{name}Case{r}'
        units = [[r*m+1]] + [[-i-1] for i in range(r*m)]
        metadata = base_metadata + [['present', r*m]] + [['absent', i] for i in range(r*m)]
        (out / f'{case}.cnf').write_text(f'p cnf {nv} {nc+len(units)}\n' +
            '\n'.join(original[1:])+'\n' +
            ''.join(' '.join(map(str, c))+' 0\n' for c in units))
        (out / f'{case}.json').write_text(json.dumps(metadata, separators=(',', ':')))
        solve(case, out, cadical)
        prune(case, out)
        steps = len((out / f'{case}.core.lrat').read_text().splitlines())
        folder = destination / f'{case}Proof'
        folder.mkdir(parents=True, exist_ok=True)
        chain = f'RigidGHZ.Finite.Seeds.{name}Facts' if r == 0 else branches[-1]
        (folder / 'Context.lean').write_text(f'''module

public import RigidGHZ.Finite.SatLRATPremises
public import {chain}

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}.Case{r}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_context unsat (include_str "../../ExactCoverCertificates/{case}.core.cnf")
kernel_lrat_premises unsat (include_str "../../ExactCoverCertificates/{case}.core.cnf")
end RigidGHZ.Finite.Seeds.{name}.Case{r}
''')
        previous = f'RigidGHZ.Finite.Seeds.{case}Proof.Context'
        for k, start in enumerate(range(0, steps, 1000)):
            stop = min(start+1000, steps)
            if m >= 41:
                emit_direct_chunk(case, f'{name}.Case{r}', previous, k, start, stop, folder, out)
            else:
                (folder / f'Chunk{k:03}.lean').write_text(f'''module

public import {previous}

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}.Case{r}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
kernel_lrat_chunk unsat (include_str "../../ExactCoverCertificates/{case}.core.cnf")
  (include_str "../../ExactCoverCertificates/{case}.core.lrat") {start} {stop}
end RigidGHZ.Finite.Seeds.{name}.Case{r}
''')
            previous = f'RigidGHZ.Finite.Seeds.{case}Proof.Chunk{k:03}'
        (destination / f'{case}.lean').write_text(f'''module

public import {previous}
public import RigidGHZ.Finite.ExactCoverNormalized

@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}.Case{r}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem refutation (M : Hypergraph (Fin 3 × ZMod {m}))
    (hM : PerfectMatching data.host M) (hne : ∀ r, M ≠ data.matching r)
    (hroot : data.edge (rootIndex {r}) ∈ M)
    (hlower : ∀ i : Fin {e}, i.val < {r} * {m} → data.edge i ∉ M) : False := by
  exact_cover_sat_normalized unsat (include_str "../ExactCoverCertificates/{case}.core.json")
    data valid M hM hne hroot hlower

end RigidGHZ.Finite.Seeds.{name}.Case{r}
''')
        branches.append(f'RigidGHZ.Finite.Seeds.{case}')
    source = 'module\n\n' + '\n'.join('public import '+b for b in branches)
    source += f'''
public import RigidGHZ.Supplement.AffineSymmetry

/-! Translation normalization plus the independently checked finite branches
proves completeness for the ordinary affine hypergraph. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.{name}
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  have hne : ∀ s : shifts, M ≠ coordinateMatching (baseMap ({lam} : ZMod {m}) s.val) := by
    intro s hs
    obtain ⟨r,hr⟩ := shift_surjective s
    apply hn r
    rw [matching_eq r,hr]
    exact hs
  obtain ⟨M',s,hM',hne',hroot,hlower⟩ := normalize_counterexample
    ({lam} : ZMod {m}) shifts (by simpa only [host_eq] using hM) hne
  obtain ⟨r,hr⟩ := shift_surjective s
  have hPM : PerfectMatching data.host M' := by simpa only [host_eq] using hM'
  have hnot : ∀ t, M' ≠ data.matching t := by
    intro t ht
    exact hne' ⟨shift t,shift_mem t⟩ (ht.trans (matching_eq t))
  have hroot' : data.edge (rootIndex r) ∈ M' := by
    rw [root_edge_eq r,hr]
    exact hroot
  have hlower' : ∀ i : Fin {e}, i.val < r.val * {m} → data.edge i ∉ M' := by
    intro i hi
    rw [edge_eq i]
    apply hlower ⟨shift (rowIndex i),shift_mem (rowIndex i)⟩
    rw [← hr]
    exact lower_shift r i hi
  fin_cases r
'''
    for r in range(d):
        source += f'  · exact Case{r}.refutation M\' hPM hnot hroot\' hlower\'\n'
    source += f'''
noncomputable def family : RigidFamily data.host (Fin {d}) := valid.family complete
theorem rigid : IsRigid data.host {d} := ⟨family⟩

end RigidGHZ.Finite.Seeds.{name}
'''
    (destination / f'{name}.lean').write_text(source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['generate', 'solve', 'prune', 'lean-data', 'lean-proof', 'lean-facts', 'normalize', 'hashes'])
    parser.add_argument('--out', type=Path, default=HERE)
    parser.add_argument('--cases', nargs='*')
    parser.add_argument('--cadical', default='cadical')
    args = parser.parse_args()
    seeds = json.loads((HERE / 'seeds.json').read_text())
    names = args.cases or list(seeds)
    args.out.mkdir(parents=True, exist_ok=True)
    if args.action == 'hashes':
        for name in ['seeds.json', 'manifest.json', 'reproduce.py']:
            path = HERE / name
            print(hashlib.sha256(path.read_bytes()).hexdigest(), path.name)
    for name in names:
        data = seeds[name]
        if name in NORMALIZED and args.action in ['solve', 'prune', 'lean-proof']:
            continue  # These seeds use the proved normalized branches instead.
        if args.action == 'generate': generate(name, data, args.out)
        elif args.action == 'solve': solve(name, args.out, args.cadical)
        elif args.action == 'prune': prune(name, args.out)
        elif args.action == 'lean-data': emit_data(name, data, HERE.parent / 'Seeds')
        elif args.action == 'lean-proof': emit_proof(name, data, args.out, HERE.parent / 'Seeds')
        elif args.action == 'lean-facts': emit_facts(name, data, HERE.parent / 'Seeds')
        elif args.action == 'normalize': normalize(name, data, args.out, HERE.parent / 'Seeds', args.cadical)
        elif args.action == 'hashes':
            variants = [f'{name}Case{i}' for i in range(len(data['rows']))] if name in NORMALIZED else [name]
            for variant in variants:
                for suffix in ['cnf', 'json']:
                    path = args.out / f'{variant}.{suffix}'
                    print(hashlib.sha256(path.read_bytes()).hexdigest(), path.name)
                for suffix in ['cnf', 'json', 'lrat']:
                    path = args.out / f'{variant}.core.{suffix}'
                    print(hashlib.sha256(path.read_bytes()).hexdigest(), path.name)
                for path in sorted(args.out.glob(f'{variant}.chunk*.lrat')):
                    print(hashlib.sha256(path.read_bytes()).hexdigest(), path.name)


if __name__ == '__main__':
    main()
