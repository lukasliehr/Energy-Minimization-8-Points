#!/usr/bin/env python3
"""Regression tests, not a complete proof or a replacement for uniform replay."""
from __future__ import annotations
import argparse, json, os, random, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent

def run(backend: str, output: Path) -> None:
    if not __debug__:
        raise RuntimeError('Do not use -O.')
    sys.path.insert(0,str(HERE/'kernel'))
    os.environ['N8_TAYLOR_ORDER']='10'
    os.environ['N8_EXACT_SCALAR_BITS']='384'
    from verify_cell import prepare_backend
    flint=prepare_backend(backend)
    fmpz_mat=flint.fmpz_mat
    rng=random.Random(20260920)
    cases=0
    for bits in (0,1,10,63,64,112,113,384,800):
        for r,k,c in ((1,1,1),(7,13,11),(3,0,4),(0,2,3),(3,4,0)):
            def rand():
                return (-1 if rng.randrange(2) else 1)*rng.getrandbits(bits)
            aa=[rand() for _ in range(r*k)]
            bb=[rand() for _ in range(k*c)]
            A=fmpz_mat(r,k,aa);B=fmpz_mat(k,c,bb)
            C=A*B
            expected=[sum(aa[i*k+h]*bb[h*c+j] for h in range(k))
                      for i in range(r) for j in range(c)]
            actual=[int(C[i,j]) for i in range(r) for j in range(c)]
            if actual != expected:
                raise ArithmeticError(('Integer product mismatch',bits,r,k,c))
            C+=C
            if [int(C[i,j]) for i in range(r) for j in range(c)] != [2*x for x in expected]:
                raise ArithmeticError('Integer addition mismatch')
            cases+=1
    import mpmath as mp
    from taylor_models import TM, normalized_phi
    from exact_iv import SCALE
    mp.mp.dps=110
    comparisons=0
    tolerance=mp.mpf('1e-75')  # For the numerical reference only, NEVER a proof tolerance.
    for qs in ('0','0.25','0.5','1'):
        q=mp.mpf(qs)
        for ts in ('-1','-0.7','0','0.3'):
            t=mp.mpf(ts);d=2-2*t
            for j in range(5):
                if j==0:
                    if q==0:
                        ref=(1-t)*mp.log((1-t)/2)+t+1
                    elif q==1:
                        ref=-mp.log((1-t)/2)/2-(t+1)/4
                    else:
                        ref=((d**(1-q)-4**(1-q))/(2*(q-1))-4**(-q)*(t+1))/q
                elif j==1:
                    ref=mp.log(4/d) if q==0 else (d**(-q)-4**(-q))/q
                else:
                    ref=mp.mpf(2)**(j-1)*mp.rf(q+1,j-2)*d**(1-q-j)
                enclosure=normalized_phi(TM.const(qs),TM.const(ts),j).interval()
                lo=mp.mpf(enclosure.lo)/SCALE;hi=mp.mpf(enclosure.hi)/SCALE
                if not lo-tolerance <= ref <= hi+tolerance:
                    raise ArithmeticError(('Potential regression mismatch',qs,ts,j))
                comparisons+=1
    result={'status':'PASS_REGRESSION_TESTS_NOT_A_PROOF', 'integer_backend':backend,
            'exact_integer_test_families':cases,
            'high_precision_potential_and_derivative_comparisons':comparisons,
            'reference_tolerance':'1e-75, numerical reference only; not used by proof checker',
            'scope':'Finite diagnostic comparisons; mathematical coverage requires cap.py replay.'}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend',choices=['flint','gmp'],default='flint')
    parser.add_argument('--output',type=Path,required=True)
    a=parser.parse_args();run(a.backend,a.output)
