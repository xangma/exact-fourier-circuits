"""Fresh literal466: actual retained seed banks -> compact conjugate lanes.

Run after verification/ExportSeedConjugateBytecode.lean. n1/n4 entries come
from the freshly exported935 on empty heaps. Other dirty cases execute the
actual469 original-axis loop from honest local physical entry tables: those
are frame/decoder diagnostics, not claims of empty-start canonical Operands.
There are no interphase writes within466 and no ignored-agent dependencies.
"""
from pathlib import Path
import copy, hashlib, json
from uniform_seed_cyclotomic_engine import Poly, scalar, execute
P = Path(__file__).resolve().parents[1] / 'logs/uniform-bytecode/seed-conjugate'
code = json.loads((P/'program.json').read_text())
startup = json.loads((P/'startup.json').read_text())
original_loop = json.loads((P/'original-axis-loop.json').read_text())
models = json.loads((P/'models.json').read_text())
assert [len(code),len(startup),len(original_loop)] == [466,935,469]
assert all(i[0] not in ('root','input','output') for i in code)
assert code[9] == ['getnat',1247,1246] and code[11] == ['getnat',1248,1246]
assert code[465] == ['halt']
def relocate(ins,base,ret):
    op,*a=ins
    if op=='halt':return ['jump',ret]
    if op=='jump':a[0]+=base
    if op=='branch':a[2]+=base;a[3]+=base
    return [op,*a]
assert code[316:320] == [['lit',107,4],['mul',108,110,107],['add',108,102,108],['add',108,105,108]]
assert code[344] == ['add',120,1247,1240]
def empty():
    return {'pc':0,'nat':[0]*1280,'sr':{},'nh':{},'sh':{},'out':{},'roots':[]}
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
    for i in range(1280):s['nat'][i]=(i+dirty)%29
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

success=[];negative=[];allpcs=set();total=0
for m in models:
    n,rs=m['n'],m['radices']
    full=n in [1,4]
    D=m['masterOrder'] if full else (12 if 3 in rs else 4)
    for dirty in [0,1,7]:
        s=empty()
        if full:
            inputs=[scalar(D,0 if dirty else i+1,0 if dirty else 2-i)[0] for i in range(n)]
            t,pcs,peak=execute(startup,s,(n+2)**19,100000,D,n,inputs)
            check_original(s,m,D)
        else:s,t,peak=dirty_entry(m,D,dirty)
        for j,r in enumerate(rs):
            st=copy.deepcopy(s);st['pc']=0;st['nat'][110]=j  # declared selected-axis caller header.
            for reg in range(20):st['sr'][reg]=scalar(D,reg-5,dirty-reg,True)
            # Dirty future compact lane and external retained zero are genuine initial cells.
            for a in range(m['destination'],m['destination']+5*r):st['sh'][a]=scalar(D,a-23,dirty-a,True)
            st['sh'][m['destination']+5*max(rs)+11]=scalar(D)
            before=copy.deepcopy(st)
            steps,pcs,peak=execute(code,st,(n+2)**19,m['runtimes'][j],D,n)
            assert steps==m['runtimes'][j] and st['pc']==465
            omega=Poly(D,{1:1})**(D//r)
            expected=seed_values(D,r,omega.conjugate())
            originalBase=m['pool']+5*sum(rs[:j])
            for q,lane in enumerate(expected):
                for k,v in enumerate(lane):
                    addr=m['destination']+q*r+k
                    assert st['sh'][addr]==(v,False)
                    assert v==before['sh'][originalBase+q*r+k][0].conjugate()
            end=m['ell']+8+2*n+3*m['L']
            assert all(st['sh'][a]==v for a,v in before['sh'].items() if a<end or m['pool']<=a<m['destination'] or a>=m['destination']+5*r)
            assert all(st['nh'][a]==v for a,v in before['nh'].items() if a>=m['copyBase'])
            assert st['nat'][100:107]==before['nat'][100:107]
            assert st['out']==before['out'] and st['roots']==before['roots']
            assert st['sh'][6+j]==before['sh'][6+j] and st['sh'][0]==before['sh'][0]
            assert all(st['nh'][m['directory']+i]==before['nh'][m['directory']+i] for i in range(2*len(rs)))
            assert st['nat'][1247]==m['destination'] and st['nat'][120]==m['destination']
            allpcs.update(pcs);total+=steps
            success.append(dict(n=n,axis=j,r=r,dirty=dirty,fieldOrder=D,steps=steps,preparationSteps=t,peak=peak,
                                entry='fresh empty935' if full else 'actual469 from supplied physical entry; canonical global Operands not asserted'))
        # Guard controls start from actual generated original seed banks.
        for label,pc in [('missing-last-base',9),('missing-last-width',11),('missing-selected-width',19),
                         ('missing-selected-root',22),('dependent-selected-root',24),('zero-selected-root',24)]:
            bad=copy.deepcopy(s);bad['pc']=0;bad['nat'][110]=len(rs)-1
            if label=='missing-last-base':del bad['nh'][m['directory']+2*(len(rs)-1)]
            elif label=='missing-last-width':del bad['nh'][m['directory']+2*(len(rs)-1)+1]
            elif label=='missing-selected-width':del bad['nh'][m['copyBase']+m['ell']+4*(len(rs)-1)]
            elif label=='missing-selected-root':del bad['sh'][6+len(rs)-1]
            elif label=='dependent-selected-root':bad['sh'][6+len(rs)-1]=(bad['sh'][6+len(rs)-1][0],True)
            else:bad['sh'][6+len(rs)-1]=scalar(D)
            try:execute(code,bad,(n+2)**19,100000,D,n)
            except AssertionError as e:
                assert bad['pc']==pc+1,(label,bad['pc'],pc,e)  # engine increments pc before guard evaluation.
                negative.append(dict(n=n,dirty=dirty,name=label,failingPC=pc,error=str(e)))
            else:raise AssertionError(('expected failure',label))
assert allpcs==set(range(466)),sorted(set(range(466))-allpcs)
receipt=dict(status='PASS',fresh_Lean_export=True,programLength=466,successfulCases=len(success),negativeCases=len(negative),
             visitedPCs=len(allpcs),chargedTicks=total,cases=success,guards=negative,
             arithmetic='versioned exact sparse cyclotomic engine; no floats',
             original935OriginCases=sum(c['entry']=='fresh empty935' for c in success),
             noAdditionalRootRequest=True,preparedOutputsDependencyFlag=False,
             hashes={f:hashlib.sha256((P/f).read_bytes()).hexdigest() for f in ['program.json','startup.json','original-axis-loop.json','models.json']})
(P/'runtime-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(f'PASS {len(success)} exact cases ({receipt["original935OriginCases"]} fresh935-origin), {len(negative)} guards, all466 PCs')
