"""Fresh exported fixed79, actual Lean-selected CRT radices and matching oracles.
Physical matched endpoint rows/directory are honest inputs; scalar and tag
frames are exact. This is not an initial-state producer or a global DFT test.
"""
from pathlib import Path
import copy,json,math,sys
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'scripts/uniform_seed_cyclotomic_engine.py').exists())
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import execute,scalar
OUT=ROOT/'logs/uniform-bytecode/all-axis-matching-table'
code=json.loads((OUT/'programs.json').read_text())['matching']
spec=json.loads((OUT/'spec.json').read_text())
assert len(code)==79 and all(ins[0] in ('lit','add','sub','mul','getnat','putnat','branch','jump','halt') for ins in code)
D=8;B=1000000;seen=set();traces=[];guards=[]
def fresh(model,variant):
    axes=model['axes'];m=len(axes);L=model['length'];protected=model['copyBase']+model['protectedAmount']
    d=protected+37+variant*31
    sources=[];cursor=d+2*m+17
    for axis in axes:
        sources.append(cursor);cursor+=3*axis['count']+13
    P=cursor+17;W=P+L*m+variant*23;U=W+L*m+variant*31;A=U+L+variant*37
    nr=[(19*i+7)%1000 for i in range(3300)]
    nr[102]=m-1;nr[103]=L;nr[105]=model['copyBase']
    nr[3240:3245]=[d,P,W,U,A]
    nh={i:(i*17+41)%1000 for i in range(protected)}
    for j,axis in enumerate(axes):
        nh[model['copyBase']+m-1+4*j]=axis['r']
        nh[d+2*j]=axis['count'];nh[d+2*j+1]=sources[j]
        for i,(left,right) in enumerate(axis['edges']):
            nh[sources[j]+3*i]=left;nh[sources[j]+3*i+1]=right
            if (i+variant)%2:nh[sources[j]+3*i+2]=77+i  # payload unused; often absent
    for base,length in ((P,L*m),(W,L*m),(U,L),(A,4*m)):
        for j in range(length):
            if (j+variant)%3:nh[base+j]=(j*31+91)%1000
    nh[A+4*m+5]=137
    state=dict(pc=0,nat=nr,nh=nh,
        sh={0:scalar(D,0,1),6:scalar(D,-2,3),55:scalar(D,0,0,True),A+99:scalar(D,7,-11,True)},
        sr={i:scalar(D,3*i-4,7-2*i,dep=bool(i%2)) for i in range(80)},
        out={0:scalar(D,3,7)[0],19:scalar(D,0,0)[0]},roots=[24,1])
    return state,dict(d=d,P=P,W=W,U=U,A=A,sources=sources,m=m,L=L,protected=protected)
for index,model in enumerate(spec['models']):
    axes=model['axes'];m=len(axes);L=model['length']
    assert math.prod(a['r'] for a in axes)==L and all(a['r']>=2 for a in axes)
    for variant in range(2):
        s,h=fresh(model,variant);old=copy.deepcopy(s)
        ticks,pcs,peak=execute(code,s,B,1000000,D);seen.update(pcs)
        assert ticks==8+sum(17*a['r']+8*a['count']+38 for a in axes)
        assert ticks<=m*(21*L+38)+8 and s['pc']==78
        for j,a in enumerate(axes):
            p=h['P']+j*L;w=h['W']+j*L
            assert [s['nh'][p+i] for i in range(a['r'])]==a['order']
            assert [s['nh'][w+i] for i in range(len(a['widths']))]==a['widths']
            assert [s['nh'][h['A']+4*j+i] for i in range(4)]==[len(a['widths']),w,a['r'],p]
            paired=[v for pair in a['edges'] for v in pair]
            assert a['order']==paired+[v for v in range(a['r']) if v not in paired]
            assert a['widths']==[2]*a['count']+[1]*(a['r']-2*a['count'])
            assert sorted(a['order'])==list(range(a['r'])) and sum(a['widths'])==a['r']
        def writable(z):
            return (h['U']<=z<h['U']+L or h['A']<=z<h['A']+4*m or
                    any(h['P']+j*L<=z<h['P']+j*L+a['r'] or
                        h['W']+j*L<=z<h['W']+j*L+a['r'] for j,a in enumerate(axes)))
        assert all(s['nh'].get(z)==v for z,v in old['nh'].items() if not writable(z))
        assert all(z in old['nh'] or writable(z) for z in s['nh'])
        assert all(s['nh'].get(z)==v for z,v in old['nh'].items() if z<h['P'])
        assert all(s[k]==old[k] for k in ('sh','sr','out','roots'))
        allowed=lambda i:840<=i<=846 or 850<=i<=861 or 3245<=i<=3254
        assert all(s['nat'][i]==v for i,v in enumerate(old['nat']) if not allowed(i))
        traces.append(dict(model=index,n=model['n'],variant=variant,radices=[a['r'] for a in axes],
            matchingCounts=[a['count'] for a in axes],ticks=ticks,maximumWord=peak,
            expected='fresh Lean SelectedCRT.radices/ordered/widths',frames=True))
# Guard paths are actual read/word failures, not runtime checks of mathematical Matching.
model=next(m for m in spec['models'] if m['n']==8 and all(a['count']>0 for a in m['axes']))
for kind in ('missing_first_radix','missing_last_radix','missing_count','missing_source_pointer',
             'missing_left','missing_right','missing_late_endpoint','small_word_budget','missing_instruction'):
    s,h=fresh(model,1);budget=B
    if kind=='missing_first_radix':del s['nh'][model['copyBase']+h['m']-1]
    elif kind=='missing_last_radix':del s['nh'][model['copyBase']+h['m']-1+4*(h['m']-1)]
    elif kind=='missing_count':del s['nh'][h['d']]
    elif kind=='missing_source_pointer':del s['nh'][h['d']+1]
    elif kind=='missing_left':del s['nh'][h['sources'][0]]
    elif kind=='missing_right':del s['nh'][h['sources'][0]+1]
    elif kind=='missing_late_endpoint':del s['nh'][h['sources'][-1]+1]
    elif kind=='small_word_budget':budget=h['A']+4*h['m']-1
    else:s['pc']=79
    try:execute(code,s,budget,1000000,D)
    except AssertionError as e:guards.append(dict(kind=kind,reason=str(e)))
    else:raise AssertionError(f'{kind} accepted unexpectedly')
assert seen==set(range(79)),set(range(79))-seen
result=dict(status='PASS',exactCases=len(traces)+len(guards),successfulCases=len(traces),guardCases=len(guards),
    totalTicks=sum(t['ticks'] for t in traces),all79PC=True,traces=traces,guards=guards,
    boundary='Physical matching endpoint banks/directory and retained CRT read cells are fixture entry arrays; no initial-state/all-axis edge producer, scalar packing action or global DFT claim.')
(OUT/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','exactCases','successfulCases','guardCases','totalTicks','all79PC')}))
