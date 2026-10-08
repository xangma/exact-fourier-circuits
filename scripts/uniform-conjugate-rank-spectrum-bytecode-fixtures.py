"""Actual1460 startup -> actual835 original rank/signed bank -> actual763.
Only caller entry headers/PC are installed between these separate phases.
Within763 no host writes or precomputed spectrum is supplied. Exact finite
cyclotomic arithmetic; no floating values or free semantic conjugated state.
"""
from pathlib import Path
import copy,json,hashlib,sys
from uniform_seed_cyclotomic_engine import Poly,scalar,execute,direct_dft
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/conjugate-rank-spectrum'
programs=json.loads((P/'programs.json').read_text())
spec=json.loads((P/'spec.json').read_text())
code=programs['producer'];startup=programs['startup'];original=programs['originalRank'];rev=programs['reverse']
assert [len(code),len(startup),len(original),len(rev)]==[763,1460,835,18]
assert not any(row[0]in('input','root','output')for row in code)
def empty():return {'pc':0,'nat':[0]*2200,'sr':{},'nh':{},'sh':{},'out':{},'roots':[]}
def plan(K,a,e,S,d):
    N=spec['widths'][K];g=spec['counts'][K];cg=spec['convolutionGates'][K]
    shape=6*(3*K*N+2*N)+2*a
    A=S+6*N+20;C=A+6*N+g+24
    conv=d+3*g+20;tape=conv+5*cg+20;depth=tape+5*shape+20
    order=depth+e+1+shape+20;directory=order+shape+20
    negative=C+7*N+20;constants=negative+7*N+20
    return dict(K=K,N=N,g=g,cg=cg,shape=shape,e=e,S=S,A=A,C=C,d=d,conv=conv,tape=tape,
        depth=depth,order=order,directory=directory,negative=negative,constants=constants,
        natEnd=directory+shape+2,scalarEnd=constants+6)
def kernel_reference(D,N,a,e,i0,j0,split,h,g):
    z=Poly(D);o=Poly(D,{0:1})
    v=lambda i:-h[i0+i-split]
    w=lambda j:g[split-j0-j]
    def matrix(i,j):
        ans=z
        for l in range(split-(j0+j)):ans=ans+h[i0+i-(j0+j)-l]*g[l]
        return ans
    delta=lambda j:o if j==0 else z
    right=[w,lambda j:matrix(0,j)-v(0)*w(j),delta]
    left=[v,delta,lambda i:z if i==0 else matrix(i,0)-v(i)*w(0)]
    out=[]
    for b in range(3):
        out.append([right[b](j)if j<e else z for j in range(N)])
        out.append([left[b](i)if i<a else z for i in range(N)])
    return out
def reference_bank(D,N,kernels):
    omega=Poly(D,{1:1})**(D//N)
    return [omega**j for j in range(N)]+[v[0]for kernel in kernels for v in direct_dft(omega,[(v,False)for v in kernel])]
def install_original(s,m,j,a,e,split,p):
    s['pc']=0;s['nat'][1120]=j
    vals=[p['K'],a,e,split,0,split,p['S'],p['A'],p['d'],p['C'],p['conv'],p['tape'],p['depth'],p['order'],p['directory'],p['negative'],p['constants']]
    s['nat'][1121:1138]=vals

def install_new(s,m,j,a,e,split,p,dest):
    s['pc']=0
    s['nat'][1820]=dest;s['nat'][1821]=j
    for r in range(480,484):s['nat'][r]=17+r  # overwritten from real directory
    for r,v in {484:a,485:e,486:split,487:0,488:split,490:p['S'],525:p['K'],527:p['A'],528:p['d'],529:p['C'],563:p['conv'],564:p['tape'],675:p['depth']}.items():s['nat'][r]=v

def framed(before,after,p,dest):
    N=p['N'];g=p['g']
    natRanges=[(p['d'],3*g),(p['conv'],5*p['cg']),(p['tape'],5*p['shape']),(p['depth'],p['shape']+p['e']+1)]
    scalarRanges=[(p['S'],6*N),(p['A'],6*N+g+5),(p['C'],7*N+1),(dest,7*N)]
    for a,v in before['nh'].items():
        if not any(b<=a<b+n for b,n in natRanges):assert after['nh'].get(a)==v,('Nat frame',a)
    for a,v in before['sh'].items():
        if not any(b<=a<b+n for b,n in scalarRanges):assert after['sh'].get(a)==v,('scalar frame',a)
    assert before['out']==after['out']and before['roots']==after['roots']
    for r in list(range(100,107))+list(range(1830,2200)):assert after['nat'][r]==before['nat'][r]

success=[];negative=[];contract=[];pcs=set();retainedpcs=set();wrong_lane_cases=0
for m in spec['models'][:1] if '--focused' in sys.argv else spec['models']:
    n=m['n'];D=m['masterOrder'];B=(n+2)**19
    base=empty();inputs=[scalar(D,i+1,1-i)[0]for i in range(n)]
    startupTicks,startPC,_=execute(startup,base,B,1000000,D,n,inputs)
    assert len(base['roots'])==1 and base['roots'][0]==D
    poolEnd=m['conjugatePool']+5*sum(m['radices']);dirEnd=m['conjugateDirectory']+2*m['axisCount']
    for j,r in enumerate(m['radices']):
      for K in range(1 if '--focused' in sys.argv else 4):
       geometries=[(1,1,1)]
       if r>=3 and K>=1:geometries.append((min(2,r-2),2,2))
       if r>=4 and K>=2:geometries.append((1,3,3))
       for a,e,split in geometries:
        N=spec['widths'][K]
        if max(a,e)>N:continue
        old=plan(K,a,e,poolEnd+100,dirEnd+100)
        s=copy.deepcopy(base);install_original(s,m,j,a,e,split,old)
        oldTicks,_,_=execute(original,s,B,10000000,D,n)
        origBase=s['nh'][m['directory']+2*j]
        h=[s['sh'][origBase+3*r+l][0]for l in range(r)]
        g=[s['sh'][origBase+4*r+l][0]for l in range(r)]
        kernels=kernel_reference(D,N,a,e,split,0,split,h,g)
        expected=reference_bank(D,N,kernels)
        assert [s['sh'][old['C']+i]for i in range(7*N)]==[(v,False)for v in expected]
        p=plan(K,a,e,old['scalarEnd']+100,old['natEnd']+100);dest=p['C']+7*N+20
        for dirty in [0,1]:
          u=copy.deepcopy(s)
          for addr in range(p['S'],dest+7*N+5):u['sh'][addr]=scalar(D,addr%19-8,addr%7-3,True)
          for addr in range(p['d'],p['depth']+p['shape']+e+3):u['nh'][addr]=(addr*3+dirty)%53
          for reg in range(100):u['sr'][reg]=scalar(D,reg-17,9-reg,True)
          u['sh'][dest+7*N+17]=scalar(D,3,-2,True)
          u['nh'][p['depth']+p['shape']+e+19]=37
          install_new(u,m,j,a,e,split,p,dest);before=copy.deepcopy(u)
          steps,seen,peak=execute(code,u,B,10000000,D,n)
          assert u['pc']==762 and all(u['sh'][dest+i]==(v.conjugate(),False)for i,v in enumerate(expected))
          assert [u['sh'][old['C']+i]for i in range(7*N)]==[(v,False)for v in expected]
          assert all(u['sh'][old['negative']+i]==(-v,False)for i,v in enumerate(expected))
          assert u['sh'][0]==before['sh'][0]
          conjBase=before['nh'][m['conjugateDirectory']+2*j]
          assert u['nat'][480]==conjBase+3*r and u['nat'][482]==conjBase+4*r
          for addr in range(m['pool'],poolEnd):assert u['sh'].get(addr)==before['sh'].get(addr)
          for addr in range(m['directory'],dirEnd):assert u['nh'][addr]==before['nh'][addr]
          framed(before,u,p,dest);pcs.update(seen)
          # Deliberately evaluate the disproven lane0 hypothesis independently.
          wrongH=[before['sh'][origBase+l][0]for l in range(r)]
          wrong=reference_bank(D,N,kernel_reference(D,N,a,e,split,0,split,wrongH,g))
          if wrong!=expected:wrong_lane_cases+=1
          success.append(dict(n=n,axis=j,radix=r,K=K,a=a,e=e,dirty=dirty,ticks=steps,startupTicks=startupTicks,originalTicks=oldTicks,peak=peak))
          for label,mut in [('missingDirectory',lambda z:z['nh'].pop(m['conjugateDirectory']+2*j)),
             ('missingH',lambda z:z['sh'].pop(conjBase+3*r)),('dependentSources',lambda z:[z['sh'].__setitem__(conjBase+q*r+l,(z['sh'][conjBase+q*r+l][0],True))for q in[3,4]for l in range(r)]),
             ('missingMaster',lambda z:z['sh'].pop(0)),
             ('wordBound',lambda z:z['nat'].__setitem__(525,B+1))]:
            bad=copy.deepcopy(before);mut(bad)
            try:execute(code,bad,B,10000000,D,n)
            except AssertionError:negative.append(label)
            else:raise AssertionError(('unrejected control',label))
          for label,mut in [('dependentHOnly',lambda z:z['sh'].__setitem__(conjBase+3*r,(z['sh'][conjBase+3*r][0],True))),
             ('zeroMasterSource',lambda z:z['sh'].__setitem__(0,scalar(D)))]:
            bad=copy.deepcopy(before);mut(bad)
            try:execute(code,bad,B,10000000,D,n)
            except AssertionError:contract.append(dict(label=label,n=n,axis=j,K=K,observed='runtime guard'))
            else:
              differs=any(bad['sh'][dest+i]!=(v.conjugate(),False)for i,v in enumerate(expected))
              contract.append(dict(label=label,n=n,axis=j,K=K,differs=differs,observed=(
                'produced-bank contract differs' if differs else
                'invalid source premise; degenerate case numerically agrees')))
if '--focused' not in sys.argv:
 assert wrong_lane_cases>0
 assert any(row.get('differs')for row in contract if row['label']=='zeroMasterSource')
# Generic reversal also copies arbitrary dirty data flags, not only spectra.
for N in [1,2,4,8]:
 for mixed in [False,True]:
    D=16;s=empty();a=100;d=a+7*N+17
    s['nat'][1800:1803]=[N,a,d]
    vals=[scalar(D,i-7,3-i,mixed and i%2==0)for i in range(7*N)]
    for i,v in enumerate(vals):s['sh'][a+i]=v;s['sh'][d+i]=scalar(D,19,-3,True)
    old=copy.deepcopy(s);t,p,peak=execute(rev,s,10000,10000,D);retainedpcs.update(p)
    assert t==91*N+6 and all(s['sh'][d+i]==vals[(i//N)*N+(N-i%N)%N]for i in range(7*N))
    assert all(s['sh'][a+i]==v for i,v in enumerate(vals))
    success.append(dict(reversal=True,N=N,mixed=mixed,ticks=t,peak=peak))
summary={'status':'PASS','exactCases':len(success),'successfulCases':len(success),'guardFailures':len(negative),
 'sourceContractControls':len(contract),'sourceContractOutcomes':contract,
 'producerCases':sum('n'in row for row in success),'wrongLane0DistinguishedCases':wrong_lane_cases,
 'producerPCs':len(pcs),'producerMissingPCs':sorted(set(range(763))-pcs),'reversalPCs':len(retainedpcs),
 'provenance':'Fresh Lean literal exports; actual1460 and835 produce all roots/original/conjugate coefficients. Caller-only initial headers between phases; continuous763 has no host writes. Independent direct finite convolution/DFT reference; no typed DAG sampled-action assumption.',
 'cases':success,'negativeControls':negative,
 'programsSHA256':hashlib.sha256((P/'programs.json').read_bytes()).hexdigest()}
(P/('focused-fixtures.json' if '--focused' in sys.argv else 'fixtures.json')).write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items()if k not in('cases','negativeControls','sourceContractOutcomes')},indent=2))
