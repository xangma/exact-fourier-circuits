"""Fresh fixed524 all-axis conjugate execution.

The n1/n4 cases begin with freshly exported actual935 on empty heaps.
Other cases use actual469 and disclosed honest local physical source arrays;
canonical global Metadata/Operands for those dirty-entry diagnostics are not
asserted. Nothing writes phase headers between steps of524.
"""
from pathlib import Path
import copy, hashlib, json
from uniform_seed_cyclotomic_engine import Poly, scalar, execute
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode/all-axis-conjugate'
programs=json.loads((P/'programs.json').read_text())
code,startup,original_loop=programs['driver'],programs['startup'],programs['original']
fullcode=programs['full']
assert len(fullcode)==1460
models=json.loads((P/'spec.json').read_text())['models']
assert [len(code),len(startup),len(original_loop)]==[524,935,469]
assert all(i[0] not in ('root','input','output') for i in code)
assert code[27]==['branch',1700,1705,28,523] and code[523]==['halt']
def empty():
    return {'pc':0,'nat':[0]*1800,'sr':{},'nh':{},'sh':{},'out':{},'roots':[]}
def seed_values(D,r,omega):
    one=Poly(D,{0:1});H=[one];scale=[one]
    for j in range(1,r):
        H.append(H[-1]*(one-omega**j));scale.append(scale[-1]*-(omega**(j-1)))
    h=[v.inverse() for v in H];g=[one]
    for j in range(1,r):
        v=Poly(D)
        for k in range(1,j+1):v=v+h[k]*g[j-k]
        g.append(-v)
    return H,scale,[(v*w).inverse() for v,w in zip(H,scale)],h,g

def check_original(s,m,D):
    base=m['pool']
    for j,r in enumerate(m['radices']):
        assert s['nh'][m['directory']+2*j] == base
        assert s['nh'][m['directory']+2*j+1] == r
        lanes=seed_values(D,r,Poly(D,{1:1})**(D//r))
        for q,lane in enumerate(lanes):
            assert [s['sh'][base+q*r+k] for k in range(r)] == [(v,False) for v in lane]
        base+=5*r
    assert base==m['destination']

def dirty_entry(m,D,dirty):
    n,rs,L,ell=m['n'],m['radices'],m['L'],m['ell']
    s=empty();B=(n+2)**19
    for i in range(1800):s['nat'][i]=(i+dirty)%29
    s['nat'][100:107]=[m['nextPrime'],n,ell,L,m['masterOrder'],m['copyBase'],m['amount']]
    end=ell+8+2*n+3*L
    for a in range(end):s['sh'][a]=scalar(D,a+dirty-7,11-a,bool(a%2))
    for j,r in enumerate(rs):s['sh'][6+j]=(Poly(D,{1:1})**(D//r),False)
    s['sh'][0]=(Poly(D,{1:1}),False)  # explicit diagnostic master value; not canonical for n5.
    s['nh']={m['copyBase']+a:0 for a in range(m['amount'])}
    cf=[];idem=[]
    for j,r in enumerate(rs):
        c=L//r;iv=pow(c,-1,r) if r>1 else 0;v=(c*iv)%L
        cf.append(c);idem.append(v)
        for f,w in enumerate([r,c,iv,v]):s['nh'][m['copyBase']+ell+4*j+f]=w
    for k in range(L):
        d=k;digits=[]
        for r in rs:digits.append(d%r);d//=r
        alpha=sum(a*b for a,b in zip(idem,digits))%L
        beta=sum(a*b for a,b in zip(cf,digits))%L
        s['nh'][m['copyBase']+6*ell+5+k]=alpha
        s['nh'][m['copyBase']+6*ell+5+L+k]=beta
        s['nh'][m['copyBase']+m['amount']+beta]=k
    for a in range(m['directory'],m['directory']+2*len(rs)+5):s['nh'][a]=a+31
    for a in range(m['pool'],m['destination']+5*max(rs)+10):s['sh'][a]=scalar(D,a-13,dirty-a,True)
    s['sh'][m['destination']+5*max(rs)+9]=scalar(D)
    s['out']={0:scalar(D,17,-3)[0]};s['roots']=[m['masterOrder']]
    t,pcs,peak=execute(original_loop,s,B,100000,D,n)
    check_original(s,m,D)
    return s,t,peak


success=[];negative=[];allpcs=set();ticks=0
for m in models:
    n,rs=m['n'],m['radices'];full=n in [1,4]
    D=m['masterOrder'] if full else (12 if 3 in rs else 4)
    for dirty in [0,1,7,13]:
        if full:
            s=empty()
            inputs=[scalar(D,0 if dirty==1 else i+1,0 if dirty==1 else 2-i)[0] for i in range(n)]
            originalTicks,_,_=execute(startup,s,(n+2)**19,200000,D,n,inputs)
            check_original(s,m,D)
        else:s,originalTicks,_=dirty_entry(m,D,dirty)
        s['pc']=0
        # An actual caller state may contain dirty future allocation; it is
        # overwritten by the program rather than being a readiness premise.
        end=m['conjugatePool']+5*sum(rs)
        for a in range(m['destination'],end+9):s['sh'][a]=scalar(D,a-17,dirty-a,True)
        for a in range(m['conjugateDirectory'],m['conjugateDirectory']+2*len(rs)+3):s['nh'][a]=a+17
        for reg in range(40):s['sr'][reg]=scalar(D,reg-dirty,3-reg,True)
        s['sh'][end+11]=scalar(D)
        before=copy.deepcopy(s)
        steps,pcs,peak=execute(code,s,(n+2)**19,m['runtime'],D,n)
        assert steps==m['runtime'] and s['pc']==523 and steps<=m['budget']
        base=m['conjugatePool']
        for j,r in enumerate(rs):
            assert s['nh'][m['conjugateDirectory']+2*j]==base
            assert s['nh'][m['conjugateDirectory']+2*j+1]==r
            omega=Poly(D,{1:1})**(D//r)
            expected=seed_values(D,r,omega.conjugate())
            originalBase=m['pool']+5*sum(rs[:j])
            for q,lane in enumerate(expected):
                for i,v in enumerate(lane):
                    assert s['sh'][base+q*r+i]==(v,False)
                    assert v==before['sh'][originalBase+q*r+i][0].conjugate()
            base+=5*r
        assert base==end
        globalEnd=m['ell']+8+2*n+3*m['L']
        assert all(s['sh'][a]==v for a,v in before['sh'].items()
                   if a<globalEnd or m['pool']<=a<m['destination'] or end<=a)
        assert all(s['nh'][a]==v for a,v in before['nh'].items()
                   if m['copyBase']<=a<m['conjugateDirectory'])
        assert s['nat'][100:107]==before['nat'][100:107]
        assert s['out']==before['out'] and s['roots']==before['roots']
        assert all(s['sh'][6+j]==before['sh'][6+j] for j in range(len(rs)))
        assert s['sh'][0]==before['sh'][0]
        assert all(s['nh'][m['directory']+i]==before['nh'][m['directory']+i] for i in range(2*len(rs)))
        assert s['nat'][1700]==len(rs) and s['nat'][1701]==sum(rs)
        assert s['nat'][1709]==m['destination']
        allpcs.update(pcs);ticks+=steps
        success.append(dict(n=n,radices=rs,dirty=dirty,fieldOrder=D,steps=steps,
                            originalPreparationSteps=originalTicks,peak=peak,
                            entry='fresh empty935' if full else 'actual469 diagnostic entry; canonical global Operands not asserted'))
        for label,pc in [('missing-last-base',9),('missing-last-width',11),
                         ('missing-selected-width',48),('missing-selected-root',51),
                         ('dependent-selected-root',53),('zero-selected-root',53)]:
            bad=copy.deepcopy(before);bad['pc']=0
            # First selected axis is physically derived by the driver.
            if label=='missing-last-base':del bad['nh'][m['directory']+2*(len(rs)-1)]
            elif label=='missing-last-width':del bad['nh'][m['directory']+2*(len(rs)-1)+1]
            elif label=='missing-selected-width':del bad['nh'][m['copyBase']+m['ell']]
            elif label=='missing-selected-root':del bad['sh'][6]
            elif label=='dependent-selected-root':bad['sh'][6]=(bad['sh'][6][0],True)
            else:bad['sh'][6]=scalar(D)
            try:execute(code,bad,(n+2)**19,200000,D,n)
            except AssertionError as exc:
                assert bad['pc']==pc+1,(label,bad['pc'],pc,exc)
                negative.append(dict(n=n,dirty=dirty,name=label,failingPC=pc,error=str(exc)))
            else:raise AssertionError(('expected failure',label))
assert allpcs==set(range(524)),sorted(set(range(524))-allpcs)
# Actual continuous1460 starts from empty; its internal startup halt is a
# charged jump into524, and524's halt is a charged jump to the final halt.
fullpcs=set();continuous=[]
for m in models:
    if m['n'] not in [1,4]:continue
    n,D,rs=m['n'],m['masterOrder'],m['radices']
    for case in [0,1,7,13]:
        inputs=[scalar(D,0 if case==1 else i+1,0 if case==1 else 2-i)[0] for i in range(n)]
        reference=empty();rt,_,_=execute(startup,reference,(n+2)**19,200000,D,n,inputs)
        actual=empty();steps,pcs,peak=execute(fullcode,actual,(n+2)**19,rt+m['runtime']+1,D,n,inputs)
        assert steps==rt+m['runtime']+1 and actual['pc']==1459
        assert actual['roots']==reference['roots']==[m['masterOrder']]
        assert actual['out']==reference['out']=={}
        base=m['conjugatePool']
        for j,r in enumerate(rs):
            originalBase=m['pool']+5*sum(rs[:j])
            assert actual['nh'][m['conjugateDirectory']+2*j]==base
            assert actual['nh'][m['conjugateDirectory']+2*j+1]==r
            for q in range(5):
                for i in range(r):
                    v=reference['sh'][originalBase+q*r+i][0]
                    assert actual['sh'][base+q*r+i]==(v.conjugate(),False)
                    assert actual['sh'][originalBase+q*r+i]==reference['sh'][originalBase+q*r+i]
            base+=5*r
        assert all(actual['nh'][m['directory']+i]==reference['nh'][m['directory']+i] for i in range(2*len(rs)))
        assert actual['nat'][100:107]==reference['nat'][100:107]
        assert actual['sh'][0]==reference['sh'][0]
        fullpcs.update(pcs);ticks+=steps
        continuous.append(dict(n=n,inputCase=case,fieldOrder=D,steps=steps,originalPreparationSteps=rt,peak=peak,
                               entry='continuous1460 from empty; no host phase writes'))
result=dict(status='PASS',freshLeanExport=True,literalInstructions=524,exactCases=len(success)+len(continuous),
            successfulCases=len(success)+len(continuous),negativeCases=len(negative),original935OriginCases=sum(c['entry']=='fresh empty935' for c in success),
            visitedPCs=len(allpcs),continuousVisitedPCs=len(fullpcs),continuousProgramLength=1460,continuousCases=len(continuous),
            chargedTicks=ticks,cases=success+continuous,guards=negative,
            arithmetic='versioned exact sparse cyclotomic engine; no floats',
            noAdditionalRootRequest=True,preparedOutputsDependencyFlag=False,
            hashes={f:hashlib.sha256((P/f).read_bytes()).hexdigest() for f in ['programs.json','spec.json']})
(P/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS {result["exactCases"]} exact cases ({len(continuous)} continuous1460 + {result["original935OriginCases"]} fresh935-origin driver), {len(negative)} guards, all524 PCs')
