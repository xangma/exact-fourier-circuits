"""Fresh actual exported124/23 bytecode, expected directories from Lean sectorStates.
Physical per-axis rows/width/permutation tables are honest entry arrays; this
script does not claim they came from an all-axis matching caller.
"""
from pathlib import Path
import copy,json,math,sys
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'scripts/uniform_seed_cyclotomic_engine.py').exists())
sys.path.insert(0,str(ROOT/'scripts'))
from uniform_seed_cyclotomic_engine import execute,scalar
OUT=ROOT/'logs/uniform-bytecode/multi-axis-sector-metadata'
programs=json.loads((OUT/'programs.json').read_text());spec=json.loads((OUT/'spec.json').read_text())
assert len(programs['metadata'])==124 and len(programs['projection'])==23
D=8;B=100000;seen=set();traces=[];guards=[]
def treecost(cs):return 10 if not cs else 12+cs[0]*(treecost(cs[1:])+48)
def fresh(widths,variant):
    m=len(widths);volume=math.prod(map(sum,widths));sectors=math.prod(map(len,widths))
    a=100+variant*51;d=4000+variant*200;suffix=d+3*m+13;stack=suffix+m+1+11;directory=stack+5*m+17
    nr=[(i*37+13)%997 for i in range(3300)]
    nr[102]=m-1;nr[3201]=a;nr[3202]=d;nr[3213]=suffix;nr[3214]=stack;nr[3215]=directory
    nh={i:(i*7+19)%997 for i in range(65)}
    for i in range(d,directory+3*sectors+7):nh[i]=(i*13+17)%997
    bases=[];perms=[]
    for j,ws in enumerate(widths):
        w=500+variant*71+30*j;p=1500+variant*71+90*j;bases.append(w);perms.append(p)
        nh.update({a+4*j:len(ws),a+4*j+1:w,a+4*j+2:sum(ws),a+4*j+3:p})
        nh.update({w+i:v for i,v in enumerate(ws)})
        nh.update({p+i:i for i in range(sum(ws))})
    s=dict(pc=0,nat=nr,nh=nh,sr={i:scalar(D,3*i-4,7-2*i,dep=bool(i%2)) for i in range(70)},
           sh={0:scalar(D,0,1),7:scalar(D,0,0,dep=True),9000:scalar(D,-3,11,dep=True)},
           out={0:scalar(D,3,7)[0],19:scalar(D,0,0)[0]},roots=[24,1])
    return s,dict(m=m,volume=volume,sectors=sectors,a=a,d=d,suffix=suffix,stack=stack,directory=directory,bases=bases,perms=perms)
for index,model in enumerate(spec['models']):
    widths=model['widths'];expected=model['expected']
    for variant in range(2):
        s,h=fresh(widths,variant);old=copy.deepcopy(s)
        ticks,pcs,peak=execute(programs['metadata'],s,B,1000000,D);seen.update(pcs)
        m=h['m'];d=h['d'];a=h['a'];q=h['directory'];suf=h['suffix'];st=h['stack'];sectors=h['sectors']
        actual=[[s['nh'][q+3*i+j] for j in range(3)] for i in range(sectors)]
        assert actual==expected,(widths,actual,expected)
        assert ticks==treecost(list(map(len,widths)))+43*m+31
        assert ticks<=163*h['volume']+31 and s['pc']==123
        assert [s['nh'][suf+i] for i in range(m+1)]==[math.prod(map(sum,widths[i:])) for i in range(m+1)]
        assert all(s['nh'][d+3*i+j]==old['nh'][a+4*i+j] for i in range(m) for j in range(3))
        writable=lambda z:d<=z<d+3*m or suf<=z<suf+m+1 or st<=z<st+5*m or q<=z<q+3*sectors
        assert all(s['nh'].get(z)==v for z,v in old['nh'].items() if not writable(z))
        assert all(z in old['nh'] or writable(z) for z in s['nh'])
        allowed=lambda i:53<=i<=60 or 450<=i<=478 or i==3200 or 3204<=i<=3210 or i==3216
        assert all(s['nat'][i]==v for i,v in enumerate(old['nat']) if not allowed(i))
        assert all(s[k]==old[k] for k in ('sr','sh','out','roots'))
        traces.append(dict(kind='metadata',index=index,variant=variant,axes=widths,ticks=ticks,maximumWord=peak,
                           expectedDirectory='fresh Lean sectorStates',pairDimensions=sorted(set(row[2] for row in actual)),frames=True))
projectionSeen=set()
for m in (0,1,2,5,40):
    for variant in range(2):
        a=100;d=4000;nr=[(i*19+3)%97 for i in range(3300)];nr[3200]=m;nr[3201]=a;nr[3202]=d
        s=dict(pc=0,nat=nr,nh={a+4*i+j:i*13+j for i in range(m) for j in range(4)},sr={9:scalar(D,2,-7,True)},
               sh={0:scalar(D,0,1),9000:scalar(D,-3,11,True)},out={1:scalar(D,3,2)[0]},roots=[24])
        s['nh'].update({d+j:17+j for j in range(3*m+3)});old=copy.deepcopy(s)
        ticks,pcs,peak=execute(programs['projection'],s,B,100000,D);projectionSeen.update(pcs)
        assert ticks==33*m+6 and s['pc']==22
        assert all(s['nh'][d+3*i+j]==old['nh'][a+4*i+j] for i in range(m) for j in range(3))
        assert all(s['nh'].get(z)==v for z,v in old['nh'].items() if not d<=z<d+3*m)
        assert all(s[k]==old[k] for k in ('sr','sh','out','roots'))
        assert all(s['nat'][i]==v for i,v in enumerate(old['nat']) if not (53<=i<=60 or 3204<=i<=3209))
        traces.append(dict(kind='projection',count=m,variant=variant,ticks=ticks,maximumWord=peak,frames=True))
for kind in ('missing_count','missing_width_base','missing_radix','missing_late_row','missing_first_width','missing_late_width','small_word_budget'):
    s,h=fresh([[1,2],[2,1,1]],1);budget=B
    if kind=='missing_count':del s['nh'][h['a']]
    elif kind=='missing_width_base':del s['nh'][h['a']+1]
    elif kind=='missing_radix':del s['nh'][h['a']+2]
    elif kind=='missing_late_row':del s['nh'][h['a']+4+2]
    elif kind=='missing_first_width':del s['nh'][h['bases'][0]]
    elif kind=='missing_late_width':del s['nh'][h['bases'][1]+2]
    else:budget=100
    try:execute(programs['metadata'],s,budget,100000,D)
    except AssertionError as e:guards.append(dict(kind=kind,reason=str(e)))
    else:raise AssertionError(f'{kind} accepted unexpectedly')
assert seen==set(range(124)),set(range(124))-seen
assert projectionSeen==set(range(23)),set(range(23))-projectionSeen
result=dict(status='PASS',exactCases=len(traces)+len(guards),successfulCases=len(traces),guardCases=len(guards),
            totalTicks=sum(t['ticks'] for t in traces),all124PC=True,all23PC=True,traces=traces,guards=guards,
            boundary='Honest physical axis rows and widths; exact exported bytecode; universal theorem separately in Lean; no all-axis matching-row producer or DFT claim.')
(OUT/'fixtures.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','exactCases','successfulCases','guardCases','totalTicks','all124PC','all23PC')}))
