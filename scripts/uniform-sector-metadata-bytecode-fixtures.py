"""Exact execution of the exported92-instruction program.
Expected sector order/fields are exported from Lean sectorStates, not a Python
reimplementation. These are diagnostics; the universal theorem is in Lean.
"""
import copy,json,math
from pathlib import Path
P=Path(__file__).resolve().parents[1]/'logs/uniform-bytecode'
raw=[json.loads(s) for s in (P/'sector-metadata-export.log').read_text().splitlines() if s.startswith('[')]
code=raw[0];expected=raw[1:];inputs=[[], [[1, 1]], [[1, 2]], [[2, 1, 1]], [[2, 2]], [[1, 1, 1]], [[1, 2], [2, 1, 1]], [[2, 1], [1, 2], [2, 2]], [[1, 2, 2, 1], [2, 1, 2]], [[2, 2, 2], [2, 2]], [[1, 1], [1, 1], [1, 1], [1, 1]], [[2, 2], [2, 1], [1, 2], [2, 2]], [[2, 2, 2, 2, 2, 2, 2, 2]], [[1, 2, 1, 2, 1, 2, 1, 2]], [[2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]]
assert len(code)==92 and len(expected)==len(inputs)
assert all(i[0] in {'natLiteral','natBinary','loadNat','storeNat','branchLT','jump','halt'} for i in code)
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
        elif tag=='branchLT':npc=ins[3] if nr.get(ins[1],0)<nr.get(ins[2],0) else ins[4]
        elif tag=='jump':npc=ins[1]
        else:raise AssertionError(ins)
        pc=npc;check()
    else:raise AssertionError('unexpected nontermination')
    seen.update(local)
    return dict(nr=nr,nh=nh,sr=sr,sh=sh,out=out,roots=roots,steps=steps,pc=pc,maximum=maximum,writes=writes,reads=reads)
def treecost(counts):
    if not counts:return 10
    return 12+counts[0]*(treecost(counts[1:])+48)
def initial(widths,variant):
    ell=len(widths);L=math.prod(map(sum,widths));sectors=math.prod(map(len,widths));rows=100+variant*71
    bases=[];p=1000+variant*91
    for ws in widths:bases.append(p);p+=len(ws)+7
    suffix=p+31;stack=suffix+ell+1+variant*11;directory=stack+5*ell+variant*17;B=directory+3*L+3000
    nr={j:(j*37+17)%B for j in range(500)}
    nr.update({450:ell,451:rows,452:suffix,453:stack,454:directory})
    nh={0:991,1:0,7:341,B-1:3}
    for j in range(suffix,directory+3*sectors+4):nh[j]=(j*13+17)%B
    for j,(ws,b) in enumerate(zip(widths,bases)):
        nh[rows+3*j]=len(ws);nh[rows+3*j+1]=b;nh[rows+3*j+2]=sum(ws)
        nh.update({b+i:v for i,v in enumerate(ws)})
    sr={j:([7*j,-3*j],bool(j%2)) for j in range(20)}
    sh={0:([0,1],False),5:([0,0],False),B-5:([17,-91],True)}
    out={0:[3,7],19:[0,0]};roots=[77,1]
    return nr,nh,sr,sh,out,roots,B,dict(ell=ell,L=L,sectors=sectors,rows=rows,bases=bases,suffix=suffix,stack=stack,directory=directory)
for index,(widths,spec) in enumerate(zip(inputs,expected)):
    for variant in range(2):
        nr,nh,sr,sh,out,roots,B,h=initial(widths,variant)
        t=run(nr,nh,sr,sh,out,roots,B);ell=h['ell'];L=h['L'];S=h['sectors'];d=h['directory'];suffix=h['suffix'];stack=h['stack']
        cells=[[t['nh'][d+3*j+q] for q in range(3)] for j in range(S)]
        assert cells==spec,(widths,cells,spec)
        assert t['steps']==treecost(list(map(len,widths)))+10*ell+16
        assert t['steps']<=130*L+16 and t['pc']==91
        assert t['nr'][460]==0 and t['nr'][464]==S
        assert [t['nh'][suffix+j] for j in range(ell+1)]==[math.prod(map(sum,widths[j:])) for j in range(ell+1)]
        writable=lambda j:(suffix<=j<suffix+ell+1 or stack<=j<stack+5*ell or d<=j<d+3*S)
        assert all(t['nh'].get(j)==v for j,v in nh.items() if not writable(j))
        assert all(j in nh or writable(j) for j in t['nh'])
        assert all(writable(j) for j in t['writes'])
        assert all(t['nr'][j]==v for j,v in nr.items() if j<455 or j>=479)
        assert t['sr']==sr and t['sh']==sh and t['out']==out and t['roots']==roots
        traces.append(dict(index=index,variant=variant,axes=widths,volume=L,sectors=S,steps=t['steps'],word_budget=B,maximum=t['maximum'],directory_matches_lean=True,dirty_frames_retained=True))
failures=[]
for kind in ('absent_radix','absent_count','absent_widthbase','absent_first_width','absent_late_width','word_bound'):
    nr,nh,sr,sh,out,roots,B,h=initial([[1,2],[2,1,1]],1)
    if kind=='absent_radix':del nh[h['rows']+2]
    elif kind=='absent_count':del nh[h['rows']]
    elif kind=='absent_widthbase':del nh[h['rows']+1]
    elif kind=='absent_first_width':del nh[h['bases'][0]]
    elif kind=='absent_late_width':del nh[h['bases'][1]+2]
    else:B=100
    try:run(nr,nh,sr,sh,out,roots,B)
    except ValueError as e:failures.append(dict(kind=kind,reason=str(e)))
    else:raise AssertionError(f'{kind} incorrectly accepted')
assert seen==set(range(92)),set(range(92))-seen
result=dict(status='PASS',cases=len(traces),total_steps=sum(t['steps'] for t in traces),pc_coverage=sorted(seen),expected_failures=failures,traces=traces,scope='Exact sampled exported bytecode; general physical-table theorem proved separately in Lean.')
(P/'sector-metadata-fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','cases','total_steps','expected_failures')})+f'; all {len(seen)} PCs')
