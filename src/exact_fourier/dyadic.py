"""Fast exact reference arithmetic for dyadic projected-network inputs.

Each row has integer real/imaginary numerators and a common power-of-two
denominator. This is an exact logical reference, not a floating implementation
of the compiled shear. Checkpoints therefore measure errors in both outputs
of the compiled shear, including its mathematically restored source.
"""
from dataclasses import dataclass
import hashlib
import json
import math


@dataclass
class DyadicRow:
    real: list[int]
    imag: list[int]
    exponent: int

    def normalize(self):
        nonzero=[abs(n) for n in (*self.real,*self.imag) if n]
        shift=min(self.exponent,min(((n & -n).bit_length()-1 for n in nonzero),default=self.exponent))
        if shift:
            self.real=[n >> shift for n in self.real]
            self.imag=[n >> shift for n in self.imag]
            self.exponent-=shift
        return self

    def copy(self): return DyadicRow(self.real.copy(),self.imag.copy(),self.exponent)

    def floats(self):
        return ([math.ldexp(float(n),-self.exponent) for n in self.real],
                [math.ldexp(float(n),-self.exponent) for n in self.imag])


def exact_rows(real,imag):
    if len(real)!=len(imag): raise ValueError('different role counts')
    rows=[]
    for rr,ii in zip(real,imag):
        if len(rr)!=len(ii): raise ValueError('different address counts')
        ratios=[float(v).as_integer_ratio() for v in (*rr,*ii)]
        exponent=max((d.bit_length()-1 for _,d in ratios),default=0)
        nums=[n << (exponent-(d.bit_length()-1)) for n,d in ratios]
        rows.append(DyadicRow(nums[:len(rr)],nums[len(rr):],exponent).normalize())
    return rows


def _pair(ur,ui,vr,vi):
    # Numerators of C(u,v); each output gains one denominator bit.
    sr,si=ur+vr,ui+vi
    dr,di=ur-vr,ui-vi
    return sr-di,si+dr,sr+di,si-dr


def directional(row,mask,inverse=False):
    if not mask: return
    width=len(row.real)
    if type(mask)is not int or not 0<mask<width: raise ValueError('invalid mask')
    pivot=mask & -mask
    for x in range(width):
        if x & pivot: continue
        y=x ^ mask
        r0,i0,r1,i1=_pair(row.real[x],row.imag[x],row.real[y],row.imag[y])
        if inverse: r0,i0,r1,i1=r1,i1,r0,i0
        row.real[x],row.imag[x],row.real[y],row.imag[y]=r0,i0,r1,i1
    row.exponent+=1
    row.normalize()


def shear(target,source,num,den):
    if type(den)is not int or den<1 or den & (den-1): raise ValueError('non-dyadic shear')
    shift=den.bit_length()-1
    exponent=max(target.exponent,source.exponent+shift)
    ts,ss=exponent-target.exponent,exponent-source.exponent-shift
    target.real=[(t << ts)+num*(s << ss) for t,s in zip(target.real,source.real)]
    target.imag=[(t << ts)+num*(s << ss) for t,s in zip(target.imag,source.imag)]
    target.exponent=exponent
    target.normalize()


def role_layer(rows,mask):
    if not 0<mask<len(rows): raise ValueError('invalid role mask')
    pivot=mask & -mask
    for x in range(len(rows)):
        if x & pivot: continue
        y=x ^ mask
        u,v=rows[x],rows[y]
        exponent=max(u.exponent,v.exponent)
        us,vs=exponent-u.exponent,exponent-v.exponent
        rr0=[];ii0=[];rr1=[];ii1=[]
        for ur,ui,vr,vi in zip(u.real,u.imag,v.real,v.imag):
            r0,i0,r1,i1=_pair(ur<<us,ui<<us,vr<<vs,vi<<vs)
            rr0.append(r0);ii0.append(i0);rr1.append(r1);ii1.append(i1)
        rows[x]=DyadicRow(rr0,ii0,exponent+1).normalize()
        rows[y]=DyadicRow(rr1,ii1,exponent+1).normalize()


def run_program(program,initial,checkpoint=None):
    rows=[r.copy() for r in initial]
    checkpoints={c['record_index']:c['label'] for c in program['checkpoints']}
    for index,(op,target,arg,num,den,inverse) in enumerate(program['records'],1):
        if op==0: directional(rows[target],arg,bool(inverse))
        elif op==1: shear(rows[target],rows[arg],num,den)
        elif op==2:
            old=rows[target]
            rows[target]=rows[arg]
            rows[arg]=DyadicRow([-n for n in old.real],[-n for n in old.imag],old.exponent)
        elif op==3:
            row=rows[target]
            row.real=[row.real[x ^ arg] for x in range(len(row.real))]
            row.imag=[row.imag[x ^ arg] for x in range(len(row.imag))]
        elif op==4: role_layer(rows,arg)
        else: raise ValueError('unknown projected operation')
        if checkpoint and index in checkpoints: checkpoint(checkpoints[index],rows)
    return rows


def _walsh(values):
    width=len(values);step=1
    while step<width:
        for start in range(0,width,2*step):
            for offset in range(step):
                x=start+offset;y=x+step
                a,b=values[x],values[y]
                values[x],values[y]=a+b,a-b
        step*=2


def independent_target(program,initial):
    """Diagonal Walsh reference from projected unit directions, then role axes."""
    bits=program['projection']['address_bits'];width=1 << bits
    images=program['projection']['images']
    phases=[sum((mask & frequency).bit_count()%2 for mask in images)%4 for frequency in range(width)]
    rows=[]
    for row in initial:
        rr=row.real.copy();ii=row.imag.copy()
        _walsh(rr);_walsh(ii)
        for j,phase in enumerate(phases):
            if phase==1: rr[j],ii[j]=-ii[j],rr[j]
            elif phase==2: rr[j],ii[j]=-rr[j],-ii[j]
            elif phase==3: rr[j],ii[j]=ii[j],-rr[j]
        _walsh(rr);_walsh(ii)
        rows.append(DyadicRow(rr,ii,row.exponent+bits).normalize())
    if program['metadata']['include_padding']:
        for j in range(program['metadata']['role_bits']): role_layer(rows,1 << j)
    return rows


def state_hash(rows):
    digest=hashlib.sha256()
    for row in rows:
        digest.update(json.dumps([row.real,row.imag,row.exponent],separators=(',',':')).encode())
        digest.update(b'\n')
    return digest.hexdigest()
