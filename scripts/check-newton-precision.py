"""Untimed numerical test of paper 130's Newton Fourier factorization.

This tests F = N diag(N)^(-1) N.T, not the existential saving circuit.
Reference constants and outputs use 300 decimal digits; input samples are
dyadic rationals exactly representable in both tested hardware precisions.
"""
import json
import os
import platform
import time
from fractions import Fraction as Q
from pathlib import Path

import cupy as cp
import mpmath as mp
import numpy as np


def exact_n4():
    """Check every entry of the n=4 identity in exact Gaussian rationals."""
    def add(a, b): return (a[0] + b[0], a[1] + b[1])
    def mul(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
    def sub(a, b): return add(a, (-b[0], -b[1]))
    def inv(a):
        d = a[0]*a[0] + a[1]*a[1]
        return (a[0]/d, -a[1]/d)
    zero, one = (Q(0), Q(0)), (Q(1), Q(0))
    roots = [one, (Q(0), Q(1)), (Q(-1), Q(0)), (Q(0), Q(-1))]
    N = [[zero for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for k in range(i+1):
            v = one
            for j in range(k): v = mul(v, sub(roots[i], roots[j]))
            N[i][k] = v
    for i in range(4):
        for j in range(4):
            v = zero
            for k in range(4): v = add(v, mul(mul(N[i][k], inv(N[k][k])), N[j][k]))
            assert v == roots[(i*j) % 4], (i, j, v)
    return True


def constants(n):
    roots = [mp.exp(2*mp.pi*mp.j*j/n) for j in range(n)]
    H = [mp.mpc(1)]
    for j in range(1, n): H.append(H[-1]*(1-roots[j]))
    N = mp.matrix(n)
    for i in range(n):
        for k in range(i+1):
            N[i, k] = (-1)**k * roots[(k*(k-1)//2) % n] * H[i]/H[i-k]
    Dinv = [1/N[k, k] for k in range(n)]
    F = mp.matrix([[roots[(i*j) % n] for j in range(n)] for i in range(n)])
    return N, Dinv, F


def mp_array(a):
    return mp.matrix([[mp.mpc(float(v.real), float(v.imag)) for v in row] for row in a])


def factor_mp(N, Dinv, X):
    Y = N.T * X
    for i in range(Y.rows):
        for j in range(Y.cols): Y[i, j] *= Dinv[i]
    return N * Y


def error_mp(a, ref):
    return max(mp.sqrt(mp.fsum(abs(a[i,j]-ref[i,j])**2 for i in range(ref.rows))) /
               mp.sqrt(mp.fsum(abs(ref[i,j])**2 for i in range(ref.rows)))
               for j in range(ref.cols))


def error_hw(a, ref):
    return float(np.max(np.linalg.norm(a.astype(np.complex128)-ref, axis=0) /
                        np.linalg.norm(ref, axis=0)))


def host_array(a):
    return np.array([[complex(a[i,j]) for j in range(a.cols)] for i in range(a.rows)])


def main():
    mp.mp.dps = 300
    started = time.time()
    out = Path(__file__).resolve().parent
    cp.cuda.Device(0).use()
    props = cp.cuda.runtime.getDeviceProperties(0)
    name = props['name'].decode() if isinstance(props['name'], bytes) else props['name']
    receipt = {
        'host': platform.node(), 'pid': os.getpid(), 'cwd': str(out),
        'gpu': name, 'cupy': cp.__version__, 'numpy': np.__version__,
        'mpmath': mp.__version__, 'cuda_runtime': cp.cuda.runtime.runtimeGetVersion(),
        'cuda_driver': cp.cuda.runtime.driverGetVersion(), 'reference_decimal_digits': 300,
        'identity': 'positive-sign unnormalized F = N diag(N)^(-1) N.T',
        'exact_gaussian_rational_n4_all_entries': exact_n4(),
        'metric': 'maximum relative L2 output error across six input vectors',
        'inputs': ['basis_0', 'ones', 'alternating', 'random_1', 'random_2', 'random_3'],
        'seed': 130, 'scope': 'Newton factorization only; no saving circuit or speed claim',
        'rows': [],
    }
    print(json.dumps({k:v for k,v in receipt.items() if k != 'rows'}), flush=True)
    rng = np.random.default_rng(130)
    for n in [4, 8, 16, 32, 64, 128]:
        N, Dinv, F = constants(n)
        X = (rng.integers(-1024,1025,(n,6)) + 1j*rng.integers(-1024,1025,(n,6)))/1024
        X[:,0] = 0; X[0,0] = 1
        X[:,1] = 1; X[:,2] = (-1.)**np.arange(n)
        Xm = mp_array(X)
        ref_mp = F * Xm
        high = error_mp(factor_mp(N, Dinv, Xm), ref_mp)
        assert high < mp.mpf('1e-200'), (n, high)
        ref, N64, F64 = host_array(ref_mp), host_array(N), host_array(F)
        di64 = np.array([complex(v) for v in Dinv])
        row = {'n':n, 'high_precision_factor_error':str(high),
               'max_N_magnitude':float(np.max(abs(N64))),
               'max_Dinv_magnitude':float(np.max(abs(di64))),
               'cpu_fp64_factor_error':error_hw(N64 @ (di64[:,None]*(N64.T @ X)),ref)}
        arrays = {'inputs':X,'reference':ref,'N':N64,'Dinv':di64}
        for dtype, label in [(np.complex64,'fp32'),(np.complex128,'fp64')]:
            Nr, dr, Fr = N64.astype(dtype), di64.astype(dtype), F64.astype(dtype)
            Nd, dd, Fd, Xd = cp.asarray(Nr), cp.asarray(dr), cp.asarray(Fr), cp.asarray(X.astype(dtype))
            first = Nd.T @ Xd
            second = dd[:,None] * first
            result = Nd @ second
            direct = Fd @ Xd
            fft = cp.fft.ifft(Xd,axis=0)*n
            cp.cuda.get_current_stream().synchronize()
            result, direct, fft = cp.asnumpy(result), cp.asnumpy(direct), cp.asnumpy(fft)
            row[label] = {
                'factor_error':error_hw(result,ref), 'direct_dft_error':error_hw(direct,ref),
                'cufft_error':error_hw(fft,ref),
                'coefficient_rounding_only_error':str(error_mp(factor_mp(mp_array(Nr),
                    [mp.mpc(float(v.real),float(v.imag)) for v in dr], Xm),ref_mp)),
                'max_intermediate':float(max(cp.max(abs(first)).item(),cp.max(abs(second)).item())),
                'output_dtype':str(result.dtype), 'finite':bool(np.isfinite(result).all()),
            }
            arrays[label+'_factor'] = result
            arrays[label+'_direct'] = direct
            arrays[label+'_cufft'] = fft
            assert row[label]['cufft_error'] < (1e-5 if label == 'fp32' else 1e-12)
            assert row[label]['direct_dft_error'] < (1e-5 if label == 'fp32' else 1e-12)
        np.savez(out/f'arrays-n{n}.npz',**arrays)
        receipt['rows'].append(row)
        (out/'results.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(row),flush=True)
    receipt.update(status='completed',elapsed_seconds=time.time()-started)
    (out/'results.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('COMPLETED',flush=True)


if __name__ == '__main__': main()
