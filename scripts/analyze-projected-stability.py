#!/usr/bin/env python3
"""Recheck retained CUDA arrays and plot checkpoint errors against exact references."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def error(real, imag, expected_real, expected_imag):
    # Subtract before scaling: an independent check of the CUDA runner's metrics.
    difference = (real.astype(np.float64) - expected_real) + 1j * (imag.astype(np.float64) - expected_imag)
    expected = expected_real + 1j * expected_imag
    if not np.isfinite(difference).all():
        raise ValueError('nonfinite raw output')
    scale = float(np.max(np.abs(expected)))
    relative = float(np.linalg.norm(difference / scale) / np.linalg.norm(expected / scale)) if scale else 0.0
    return {'relative_l2': relative, 'max_absolute_error': float(np.max(np.abs(difference))),
            'max_scaled_error': float(np.max(np.abs(difference)) / scale) if scale else 0.0,
            'exact_float_reference_match': bool(np.array_equal(real, expected_real) and np.array_equal(imag, expected_imag))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path('outputs/projected-stability'))
    parser.add_argument('--output', type=Path, default=Path('verification/projected-stability/analysis.json'))
    parser.add_argument('--figure', type=Path, default=Path('docs/assets/projected-stability.png'))
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    rows, manifests, fma_pairs = [], [], []
    for bits in (6, 8):
        root = args.root / f'bits{bits}'
        results = json.loads((root / 'gpu/sweep.results.json').read_text())
        terminal = json.loads((root / 'gpu/terminal.json').read_text())
        assert terminal['status'] == 'completed' and terminal['child_reaped'] and not terminal['process_group_exists']
        assert results['program_sha256'] == digest(root / 'program.json')
        assert results['fixture_sha256'] == digest(root / 'fixture.npz')
        expected_keys = set(itertools.product(range(3), ('float32', 'float64'), ('on', 'off'), ('compiled', 'direct')))
        keys = [(c['family_index'], c['dtype'], c['fmad'], c['shear_mode']) for c in results['cases']]
        assert len(keys) == len(set(keys)) == 24 and set(keys) == expected_keys
        with np.load(root / 'fixture.npz', allow_pickle=False) as fixture:
            references = {key: fixture[key] for key in ('reference_real', 'reference_imag', 'checkpoint_reference_real', 'checkpoint_reference_imag')}
        for case in results['cases']:
            assert case['status'] == 'completed'
            executed_runner = args.root / 'executed-check-projected-cuda.py'
            runner = executed_runner if executed_runner.exists() else repo / 'scripts/check-projected-cuda.py'
            assert case['runner_sha256'] == digest(runner)
            assert case['program_sha256'] == results['program_sha256'] and case['fixture_sha256'] == results['fixture_sha256']
            assert not case['nan_gate_component_events'] and not case['inf_gate_component_events']
            path = root / 'gpu' / Path(case['output_npz']).name
            family = case['family_index']
            with np.load(path, allow_pickle=False) as output:
                final = error(output['real'], output['imag'], references['reference_real'][family], references['reference_imag'][family])
                checkpoints = []
                rr, ii = output['checkpoint_real'], output['checkpoint_imag']
                for index, checkpoint in enumerate(case['checkpoints']):
                    ref_r, ref_i = references['checkpoint_reference_real'][family, index], references['checkpoint_reference_imag'][family, index]
                    checkpoints.append({'label': checkpoint['label'], 'all': error(rr[index], ii[index], ref_r, ref_i),
                                        'auxiliary': error(rr[index, 128:944], ii[index, 128:944], ref_r[128:944], ref_i[128:944])})
            reported = case['metrics']['all']['relative_l2']
            assert abs(final['relative_l2'] - reported) <= max(3e-16, 1e-8 * final['relative_l2'])
            assert (reported == 0) == final['exact_float_reference_match']
            rows.append({key: case[key] for key in ('family', 'dtype', 'fmad', 'shear_mode', 'max_finite_intermediate_component')} |
                        {'bits': bits, 'final': final, 'checkpoints': checkpoints, 'output_sha256': digest(path)})
        for family, dtype, mode in itertools.product(range(3), ('float32', 'float64'), ('compiled', 'direct')):
            base = f'sweep.family{family}.{dtype}.fmad-'
            paths = [root / 'gpu' / (base + flag + '.' + mode + '.npz') for flag in ('on', 'off')]
            with np.load(paths[0], allow_pickle=False) as a, np.load(paths[1], allow_pickle=False) as b:
                identical = all(np.array_equal(a[key], b[key]) for key in a.files)
            fma_pairs.append({'bits': bits, 'family_index': family, 'dtype': dtype, 'shear_mode': mode, 'identical_final_and_checkpoints': identical})
        manifests.append({'bits': bits, 'program_sha256': results['program_sha256'], 'fixture_sha256': results['fixture_sha256'],
                          'controller_elapsed_seconds': terminal['elapsed_seconds'], 'controller_pid': terminal['pid'],
                          'worker_pids': [c['pid'] for c in results['cases']]})
    summary = []
    for family, dtype, mode in itertools.product(('moderate_dyadic', 'wide_dynamic_range', 'cancellation'), ('float32', 'float64'), ('compiled', 'direct')):
        selected = [r for r in rows if (r['family'], r['dtype'], r['shear_mode']) == (family, dtype, mode)]
        summary.append({'family': family, 'dtype': dtype, 'shear_mode': mode,
                        'worst_relative_l2': max(r['final']['relative_l2'] for r in selected),
                        'worst_max_absolute_error': max(r['final']['max_absolute_error'] for r in selected)})
    receipt = {'schema': 'projected-stability-analysis/v1', 'raw_cases_verified': len(rows), 'projections': manifests,
               'summary': summary, 'fma_pairs': fma_pairs, 'cases': rows,
               'reference_scope': 'exact dyadic reference rounded to binary64; direct subtraction independently recomputed from retained CUDA arrays',
               'source_sha256': {str(p.relative_to(repo)): digest(p) for p in (repo / 'src/exact_fourier').glob('*.py')} |
                                {str(p.relative_to(repo)): digest(p) for p in (repo / 'scripts').glob('*projected*.py')}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, allow_nan=False) + '\n')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(2, 2, figsize=(11, 7), sharex=True)
    labels = ['Stage 1', 'Stage 2', 'Stage 3', 'Translation', 'Exchange', 'Padding', 'Role axes']
    for y, family in enumerate(('wide_dynamic_range', 'cancellation')):
        for x, dtype in enumerate(('float32', 'float64')):
            ax = axes[y, x]
            for bits, mode in itertools.product((6, 8), ('compiled', 'direct')):
                row = next(r for r in rows if (r['family'], r['dtype'], r['fmad'], r['bits'], r['shear_mode']) == (family, dtype, 'on', bits, mode))
                values = [c['all']['relative_l2'] for c in row['checkpoints']]
                ax.plot(range(7), values, marker='o', markersize=4, color='#c65f21' if mode == 'compiled' else '#286f9b',
                        linestyle='-' if bits == 6 else '--', label=f'{mode}, {1 << bits} addresses')
            positive = any(line.get_ydata().max() > 0 for line in ax.lines)
            if positive:
                ax.set_yscale('log')
            else:
                ax.set_ylim(-0.1, 1)
                ax.set_yticks([0])
                ax.text(0.5, 0.5, 'Exact agreement at every checkpoint', transform=ax.transAxes,
                        ha='center', fontsize=10)
            ax.set_title(f'{family.replace("_", " ").capitalize()} · {"FP32" if dtype == "float32" else "FP64"}')
            ax.set_ylabel('Relative L2 error')
            ax.grid(alpha=0.2)
            ax.set_xticks(range(7), labels, rotation=35, ha='right')
    axes[0, 0].legend(fontsize=8)
    fig.suptitle('Projected framed network: checkpoint error against exact arithmetic', fontsize=13)
    fig.text(0.5, 0.015, '1,024 dirty roles · FMA on (on/off arrays identical) · zero means exact agreement with the binary64 reference', ha='center', fontsize=8)
    fig.tight_layout(rect=(0, 0.03, 1, 0.96))
    args.figure.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.figure, dpi=180)
    fig.savefig(args.figure.with_suffix('.pdf'))
    print(json.dumps({'verified_raw_cases': len(rows), 'fma_identical_pairs': sum(p['identical_final_and_checkpoints'] for p in fma_pairs), 'summary': summary}, indent=2))


if __name__ == '__main__':
    main()
