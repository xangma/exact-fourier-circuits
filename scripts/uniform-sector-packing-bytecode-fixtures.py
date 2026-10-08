"""Exact execution of the exported137-instruction program.
Expected inverse addresses are exported from Lean unpackingPermutation, not a Python
reimplementation. These are diagnostics; the universal theorem is in Lean.
"""
import copy,json,math
from pathlib import Path
repo=Path(__file__).resolve().parents[1]
P=repo/'logs/uniform-bytecode/sector-packing'
raw=[json.loads(s) for s in (P/'export.log').read_text().splitlines() if s.startswith('[')]
code=raw[0];expected=raw[1::2];permutations=raw[2::2];inputs=json.loads((repo/'verification/fixtures/sector-packing-inputs.json').read_text())
assert len(code)==137 and len(expected)==len(inputs)
assert all(i[0] in {'natLiteral','natBinary','loadNat','storeNat','branchLT','jump','halt','loadScalar','storeScalar'} for i in code)
seen=set();traces=[]
def run(nr,nh,sr,sh,out,roots,B):
    nr=nr.copy();nh=nh.copy();sr=copy.deepcopy(sr);sh=copy.deepcopy(sh);out=copy.deepcopy(out);roots=roots.copy()
    pc=0;steps=0;local=set();maximum=0;writes=[];reads=[]
    def check():
        nonlocal maximum
        maximum=max(maximum,max([pc,*nr.values(),*nh.keys(),*nh.values(),*sh.keys(),*out.keys(),*roots],default=0))
        if maximum>B:raise ValueError('word bound exceeded')
    check()
    while steps<1000000:
        local.add(pc);ins=code[pc];tag=ins[0];npc=pc+1;steps+=1
        if tag=='halt':break
        if tag=='natLiteral':nr[ins[1]]=ins[2]
        elif tag=='natBinary':
            _,op,d,l,r=ins;a=nr.get(l,0);b=nr.get(r,0)
            nr[d]={'add':lambda:a+b,'sub':lambda:max(0,a-b),'mul':lambda:a*b}[op]()
        elif tag=='loadNat':
            address=nr.get(ins[2],0);reads.append(address)
            if address not in nh:raise ValueError('undefined Nat load')
            nr[ins[1]]=nh[address]
        elif tag=='storeNat':
            address=nr.get(ins[1],0);writes.append(address);nh[address]=nr.get(ins[2],0)
        elif tag=='loadScalar':
            address=nr.get(ins[2],0)
            if address not in sh:raise ValueError('undefined Scalar load')
            sr[ins[1]]=copy.deepcopy(sh[address])
        elif tag=='storeScalar':sh[nr.get(ins[1],0)]=copy.deepcopy(sr.get(ins[2],([0,0],False)))
        elif tag=='branchLT':npc=ins[3] if nr.get(ins[1],0)<nr.get(ins[2],0) else ins[4]
        elif tag=='jump':npc=ins[1]
        else:raise AssertionError(ins)
        pc=npc
        # Initial complete word envelope plus every newly written Nat value/PC.
        # Loads/stores use bounded prior address registers; heap values copied
        # by stores were already checked when initialized or computed.
        changed=nr[ins[1]] if tag in {'natLiteral','loadNat'} else nr[ins[2]] if tag=='natBinary' else 0
        maximum=max(maximum,pc,changed)
        if maximum>B:raise ValueError('word bound exceeded')
    else:raise AssertionError('unexpected nontermination')
    seen.update(local)
    return dict(nr=nr,nh=nh,sr=sr,sh=sh,out=out,roots=roots,steps=steps,pc=pc,maximum=maximum,writes=writes,reads=reads)

def initial(fixture,perm,layout,flags):
    widths=fixture['widths'];ell=len(widths);L=math.prod(map(sum,widths));rows=100+layout*71
    bases=[];pbs=[];p=1000+layout*91
    for ws in widths:bases.append(p);p+=len(ws)+7;pbs.append(p);p+=sum(ws)+11
    suffix=p+31;stack=suffix+ell+1+layout*11;inverse=stack+9*ell+layout*17
    source=5000+layout*L;dest=source+L+layout*17;B=max(dest+L,inverse+L)+3000
    nr={j:(j*37+17)%B for j in range(700)}
    nr.update({600:ell,601:rows,602:suffix,603:stack,604:source,605:dest,637:inverse})
    nh={0:991,1:0,7:341,B-1:3}
    for j in range(suffix,inverse+L+4):nh[j]=(j*13+17)%B
    for j,(ws,b,pb,ps) in enumerate(zip(widths,bases,pbs,perm)):
        nh[rows+4*j]=len(ws);nh[rows+4*j+1]=b;nh[rows+4*j+2]=sum(ws);nh[rows+4*j+3]=pb
        nh.update({b+i:v for i,v in enumerate(ws)})
        nh.update({pb+i:v for i,v in enumerate(ps)})
    sr={j:([7*j,-3*j],bool(j%2)) for j in range(80)}
    sh={0:([0,1],False),5:([0,0],False),B-5:([17,-91],True)}
    for j in range(L):
        sh[source+j]=([0,0] if j%7==0 else [3*j+1,7-2*j],False if flags==0 else (True if flags==1 else bool(j%2)))
        sh[dest+j]=([-701+j,33],bool(j%3))
    out={0:[3,7],19:[0,0]};roots=[77,1]
    return nr,nh,sr,sh,out,roots,B,dict(ell=ell,L=L,rows=rows,bases=bases,pbs=pbs,suffix=suffix,stack=stack,inverse=inverse,source=source,dest=dest)
for index,(fixture,spec,perm) in enumerate(zip(inputs,expected,permutations)):
    for layout in range(2):
      for flags in range(3):
        nr,nh,sr,sh,out,roots,B,h=initial(fixture,perm,layout,flags)
        t=run(nr,nh,sr,sh,out,roots,B);ell=h['ell'];L=h['L'];d=h['inverse'];suffix=h['suffix'];stack=h['stack'];dest=h['dest'];source=h['source']
        assert [t['nh'][d+j] for j in range(L)]==spec,(fixture,spec)
        assert [t['sh'][dest+j]for j in range(L)]==[sh[source+i]for i in spec]
        assert t['steps']<=213*L+20 and t['pc']==136
        assert t['nr'][611]==L and t['nr'][616]==L
        assert [t['nh'][suffix+j] for j in range(ell+1)]==[math.prod(map(sum,fixture['widths'][j:])) for j in range(ell+1)]
        writable=lambda j:(suffix<=j<suffix+ell+1 or stack<=j<stack+9*ell or d<=j<d+L)
        assert all(t['nh'].get(j)==v for j,v in nh.items() if not writable(j))
        assert all(j in nh or writable(j) for j in t['nh'])
        assert all(writable(j) for j in t['writes'])
        assert all(t['nr'][j]==v for j,v in nr.items() if j<606 or j>=650 or j==637)
        assert all(t['sr'][j]==v for j,v in sr.items() if j!=70)
        assert all(t['sh'][j]==v for j,v in sh.items() if not dest<=j<dest+L)
        assert t['out']==out and t['roots']==roots
        traces.append(dict(index=index,layout=layout,flags=flags,axes=fixture['widths'],volume=L,steps=t['steps'],word_budget=B,maximum=t['maximum'],inverse_matches_lean=True,values_and_tags_retained=True,dirty_frames_retained=True))
failures=[]
for kind in ('absent_radix','absent_count','absent_widthbase','absent_first_width','absent_late_width','absent_permutation','absent_scalar','word_bound'):
    index=12;fixture=inputs[index];perm=permutations[index]
    nr,nh,sr,sh,out,roots,B,h=initial(fixture,perm,1,2)
    if kind=='absent_radix':del nh[h['rows']+2]
    elif kind=='absent_count':del nh[h['rows']]
    elif kind=='absent_widthbase':del nh[h['rows']+1]
    elif kind=='absent_first_width':del nh[h['bases'][0]]
    elif kind=='absent_late_width':del nh[h['bases'][1]+2]
    elif kind=='absent_permutation':del nh[h['pbs'][1]+2]
    elif kind=='absent_scalar':del sh[h['source']+2]
    else:B=100
    try:run(nr,nh,sr,sh,out,roots,B)
    except ValueError as e:failures.append(dict(kind=kind,reason=str(e)))
    else:raise AssertionError(f'{kind} incorrectly accepted')
assert seen==set(range(137)),set(range(137))-seen
result=dict(status='PASS',cases=len(traces),total_steps=sum(t['steps'] for t in traces),pc_coverage=sorted(seen),expected_failures=failures,traces=traces,scope='Exact sampled whole exported137; universal execution theorem independently kernel-checked in Lean.')
(P/'bytecode-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','cases','total_steps','expected_failures')})+f'; all {len(seen)} PCs')
