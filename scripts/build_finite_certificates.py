#!/usr/bin/env python3
"""Build the kernel-checked finite certificates with bounded concurrency.

Run after fetching the pinned Mathlib cache. Heavy independent table checks
are scheduled sequentially; each LRAT branch already serializes its chunks
through imports. Lake reuses completed work, so rerunning resumes a build.
"""
from pathlib import Path
import argparse
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def targets():
    modules = [
        'SixVertex', 'NineVertex', 'NineAlgebraic', 'NineAlgebraicCounts',
        'NineParallelClasses', 'NineTranslateCosets',
        'NineDiscreteThings', 'NineNonisomorphism',
        'TripartiteClassification', 'NineEnumeration',
        'NineConflict', 'NineIncident', 'NineFan', 'NineCoverSound',
        'NineCoverComplete', 'NineCover', 'NineSATModel', 'SatLRATPremises',
        'NineSATCertificate6a', 'NineSATCertificate7', 'NineSATCertificate4a',
        'NineSATCertificate4b', 'NineSATCertificate5a', 'NineSATCertificate5b',
        'MatchingNormalization', 'NormalizationTransport', 'NineNormalized6a',
        'NineNormalized7', 'NineNormalized4a', 'NineNormalized4b',
        'NineNormalized5a', 'NineNormalized5b', 'NineNormalized4',
        'NineNormalized5', 'NineNormalized6', 'NineUpper', 'AxiomAudit',
        'ExactCoverAssemble', 'ExactCoverNormalized', 'ExactCoverIndex',
        'SatLRATDirect',
    ]
    for seed in ['U12', 'U15', 'U18', 'U21', 'U24']:
        modules += [f'Seeds.{seed}Data', f'Seeds.{seed}']
    for size in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        seed = f'A{size}'
        modules += [f'Seeds.{seed}Data', f'Seeds.{seed}Facts', f'Seeds.{seed}']
        if size >= 11:
            modules += [f'Seeds.{seed}Seed']
    for seed in ['U12', 'U15', 'U18', 'U21', 'U24']:
        modules += [f'Seeds.{seed}Degrees']
    modules += ['Seeds.UnrestrictedDegrees', 'Seeds.AxiomAudit']
    return ['RigidGHZ.Finite.' + module for module in modules]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true', help='print targets without building')
    parser.add_argument('--log-dir', type=Path, help='optionally preserve every Lake log')
    args = parser.parse_args()
    modules = targets()
    if args.list:
        print('\n'.join(modules))
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    elan_bin = Path.home() / '.elan/bin'
    env['PATH'] = str(elan_bin) + os.pathsep + env.get('PATH', '')
    for index, module in enumerate(modules, 1):
        start = time.monotonic()
        result = subprocess.run(['lake', 'build', module], cwd=ROOT, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if args.log_dir:
            (args.log_dir / f'{module}.log').write_text(result.stdout)
        print(f'[{index}/{len(modules)}] {module}: exit {result.returncode}; '
              f'{time.monotonic()-start:.1f}s', flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            raise SystemExit(result.returncode)
    print('All finite certificates and their axiom audits passed.')


if __name__ == '__main__':
    main()
