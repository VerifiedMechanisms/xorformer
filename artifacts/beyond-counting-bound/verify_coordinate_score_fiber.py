"""Integer-only outward interval audit of a regular positive score fiber.

The analytic existence implication is the quantitative contraction theorem
proved in coordinate-score-fiber.md. No floating arithmetic is used here.
"""
import argparse
import json
from pathlib import Path


class Interval:
    bits=256
    scale=1<<bits

    def __init__(self,lo,hi=None):
        self.lo=int(lo);self.hi=int(lo if hi is None else hi)
        assert self.lo<=self.hi

    @classmethod
    def rational(cls,a,b=1):
        assert b>0
        return cls(a*cls.scale//b,-((-a*cls.scale)//b))

    def __add__(self,o):return Interval(self.lo+o.lo,self.hi+o.hi)
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o
    def __mul__(self,o):
        v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return Interval(min(v)//self.scale,-((-max(v))//self.scale))
    def __truediv__(self,o):
        assert o.lo>0
        inv=Interval(self.scale**2//o.hi,-((-self.scale**2)//o.lo))
        return self*inv
    def square(self):return self*self
    def abs_upper(self):return max(abs(self.lo),abs(self.hi))


def isum(values):
    result=Interval(0)
    for v in values: result=result+v
    return result


def model(z,rows,n,h):
    vals=[];jac=[];numerators=[];denominators=[]
    zero=Interval(0);one=Interval.rational(1)
    for mask in rows:
        active=[i for i in range(n) if mask>>i&1]
        num=[isum(z[i*h+j] for i in active) for j in range(h)]
        den=[one+isum(z[n*h+i*h+j] for i in active) for j in range(h)]
        vals.append(one+isum(num[j]/den[j] for j in range(h)))
        jac.append([one/den[j] if i in active else zero
                    for i in range(n) for j in range(h)]+
                   [-num[j]/den[j].square() if i in active else zero
                    for i in range(n) for j in range(h)])
        numerators.append(num);denominators.append(den)
    return vals,jac,numerators,denominators


def verify(d):
    n,h=d['n'],d['heads'];size=2*n*h;rows=d['sample']
    assert len(rows)==size and len(set(rows))==size
    assert all(0<r<2**n for r in rows)
    assert len(d['center_integer'])==size
    assert len(d['inverse_integer'])==size
    assert all(len(row)==size for row in d['inverse_integer'])
    Interval.bits=d['interval_bits'];Interval.scale=1<<Interval.bits
    S=Interval.scale;one=Interval.rational(1)
    z=[Interval.rational(v,1<<d['center_bits']) for v in d['center_integer']]
    assert all(v.lo==v.hi for v in z)
    radius=Interval.rational(1,1<<d['radius_bits']);assert radius.lo==radius.hi
    assert all(v.lo>radius.hi for v in z[n*h:])
    base=[Interval.rational(v,d['numerator_scale'])
          for row in d['numerator_integer'] for v in row]
    base += [Interval.rational(v,d['denominator_scale'])
             for row in d['denominator_integer'] for v in row]
    val,jac,nums,dens=model(z,rows,n,h)
    targets,_,_,_=model(base,rows,n,h)
    A=[[Interval.rational(v,1<<d['inverse_bits']) for v in row]
       for row in d['inverse_integer']]
    residual=[v-t for v,t in zip(val,targets)]
    eta=max(isum(A[i][k]*residual[k] for k in range(size)).abs_upper()
            for i in range(size))
    anorm=max(sum(v.abs_upper() for v in row) for row in A)
    defect=0
    for i in range(size):
        row=0
        for j in range(size):
            v=isum(A[i][k]*jac[k][j] for k in range(size))
            v=(one if i==j else Interval(0))-v
            row+=v.abs_upper()
        defect=max(defect,row)
    # Uniform row-sum bound on J(z')-J(z), valid throughout the box.
    variation=0
    for r,num,den in zip(rows,nums,dens):
        k=Interval.rational(r.bit_count());change=k*radius
        total=Interval(0)
        for u,b in zip(num,den):
            lower=Interval(b.lo)-change;assert lower.lo>0
            up=Interval(u.abs_upper())
            du=change/(Interval(b.lo)*lower)
            db=change/lower.square() + up*change*(Interval(2*b.hi)+change)/(
                lower.square()*Interval(b.lo).square())
            total=total+k*(du+db)
        variation=max(variation,total.hi)
    q=(Interval(defect)+Interval(anorm)*Interval(variation)).hi
    assert 4*q<S
    assert 4*eta<radius.lo
    assert eta*(1<<200)<S
    assert q*(1<<80)<S
    # Independently certify regularity of the original rational branch.
    prime=65521
    base_mod=[]
    for r in rows:
        active=[i for i in range(n) if r>>i&1]
        un=[sum(d['numerator_integer'][i][j] for i in active)*
             pow(d['numerator_scale'],-1,prime)%prime for j in range(h)]
        bn=[(1+sum(d['denominator_integer'][i][j] for i in active)*
             pow(d['denominator_scale'],-1,prime))%prime for j in range(h)]
        assert all(bn)
        inv=[pow(v,-1,prime) for v in bn]
        base_mod.append([inv[j] if i in active else 0
                         for i in range(n) for j in range(h)]+
                        [-un[j]*inv[j]**2%prime if i in active else 0
                         for i in range(n) for j in range(h)])
    det=1
    for column in range(size):
        pivot=next(i for i in range(column,size) if base_mod[i][column]%prime)
        if pivot!=column:
            base_mod[pivot],base_mod[column]=base_mod[column],base_mod[pivot]
            det=-det
        v=base_mod[column][column]%prime;det=det*v%prime
        base_mod[column]=[x*pow(v,-1,prime)%prime for x in base_mod[column]]
        for i in range(column+1,size):
            v=base_mod[i][column]
            base_mod[i]=[(x-v*y)%prime for x,y in zip(base_mod[i],base_mod[column])]
    assert det%prime
    # The contraction also makes A*J invertible throughout the box.
    box=[Interval(v.lo-radius.hi,v.hi+radius.hi) for v in z]
    full,_,_,_=model(box,range(2**n),n,h)
    old,_,_,_=model(base,range(2**n),n,h)
    differences=[]
    for mask,(new,previous) in enumerate(zip(full,old)):
        if mask not in rows:
            differences.append((max(new.lo-previous.hi,previous.lo-new.hi),mask))
    separation,witness=max(differences);assert separation>0
    a,b=full[witness],old[witness]
    threshold=(a.lo+b.hi)//2 if a.lo>b.hi else (b.lo+a.hi)//2
    # Use a short exact dyadic threshold when it lies strictly in the gap.
    for threshold_bits in range(10,Interval.bits+1):
        step=1<<(Interval.bits-threshold_bits)
        proposed=(threshold//step)*step
        if ((a.lo>proposed>b.hi) or (b.lo>proposed>a.hi)):
            threshold=proposed
            break
    new_labels=[];old_labels=[]
    for new,previous in zip(full,old):
        assert new.lo>threshold or new.hi<threshold
        assert previous.lo>threshold or previous.hi<threshold
        new_labels.append(int(new.lo>threshold))
        old_labels.append(int(previous.lo>threshold))
    assert new_labels[witness]!=old_labels[witness]
    assert all(new_labels[r]==old_labels[r] for r in rows)
    return dict(status='PASS_INTEGER_INTERVAL_CONTRACTION',n=n,heads=h,
        equations=size,radius_bits=d['radius_bits'],interval_bits=Interval.bits,
        eta_upper_integer=eta,defect_upper_integer=defect,
        jacobian_variation_upper_integer=variation,inverse_norm_upper_integer=anorm,
        contraction_upper_integer=q,common_denominator_bits=Interval.bits,
        base_jacobian_modulus=prime,base_jacobian_determinant_mod=det%prime,
        eta_less_than_power_of_two=-200,contraction_less_than_power_of_two=-80,
        unsampled_separation_lower_integer=separation,witness_vertex=witness,
        threshold_integer=threshold,new_labels=new_labels,old_labels=old_labels,
        threshold_numerator=threshold//(1<<(Interval.bits-threshold_bits)),
        threshold_denominator_bits=threshold_bits,
        differing_vertices=[i for i in range(2**n) if new_labels[i]!=old_labels[i]],
        main_target_proved=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path)
    p.add_argument('--output',type=Path);a=p.parse_args()
    result=verify(json.loads(a.certificate.read_text()))
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if not k.endswith('_integer')
                     and k not in ['old_labels','new_labels']}))


if __name__=='__main__':main()
