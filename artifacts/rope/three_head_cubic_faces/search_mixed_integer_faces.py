"""Joint face-background selection by a bounded fixed-denominator MILP.

Every success is only a numerical proposal.  Infeasibility covers only the
chosen denominators, numerator bounds, margins, and finite background list.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy import sparse
from scipy.optimize import milp, Bounds, LinearConstraint
from search_adaptive import ZALL, XALL, FAMILIES, H, N, NV, ELL, K, BASE, cross_rows


def solve(beta, signs, choices, margin, seconds, score_basis=False):
    den=1+ZALL@beta.T
    features=(XALL[:,None,:]/den[:,:,None]).reshape(len(ZALL),NV)
    candidates=[]
    for family,indices in zip(FAMILIES,choices):
        faces,desired,name=family
        candidates.append([(faces[i],desired,name) for i in indices])
    binary_count=sum(map(len,candidates))
    if score_basis:
        left,singular,right=np.linalg.svd(features,full_matrices=False)
        rank=int(sum(singular>singular[0]*1e-12))
        score_features=left[:,:rank]
        coefficient_map=singular[:rank,None]*right[:rank]
    else:
        rank=0;score_features=features
    binary_base=BASE+rank; width=binary_base+binary_count
    rows=[];cols=[];vals=[];lo=[];hi=[]
    def add(coeff,lower=-np.inf,upper=np.inf):
        row=len(lo)
        for col,val in coeff.items():
            if val:
                rows.append(row);cols.append(col);vals.append(val)
        lo.append(lower);hi.append(upper)
    if score_basis:
        for r in range(rank):
            row={i:float(v) for i,v in enumerate(coefficient_map[r])}
            row[BASE+r]=-1
            add(row,lower=0,upper=0)
    binary=binary_base
    for group in candidates:
        ids=[]
        for masks,desired,name in group:
            ids.append(binary)
            for mask,label in zip(masks,desired):
                f=label*score_features[mask]
                big=float(np.sum(abs(f))+margin)
                offset=BASE if score_basis else 0
                row={offset+i:float(v) for i,v in enumerate(f)}
                row[binary]=-big
                add(row,lower=margin-big)
            binary+=1
        add({i:1 for i in ids},lower=1,upper=1)
    for h in range(H):
        for i in range(N):
            add({h*(N+1)+i+1:signs[h],ELL+h:-beta[h,i],K+h:-abs(beta[h,i])},lower=1e-8)
        row={h*(N+1)+i+1:-signs[h] for i in range(N)}
        row[ELL+h]=float(sum(beta[h]));row[K+h]=1
        add(row,lower=1e-8)
    cr=cross_rows(beta)
    # Valid coefficient cuts from every positive-margin parity witness.
    # The cleared polynomial is the score times the positive denominator product.
    cube_min=float(np.min(np.prod(den,axis=1)))
    for i in range(6):
        for j in range(6):
            if i!=j:
                scale=max(abs(cr[i,j]).max(),1e-15)
                add({v:float(c/scale) for v,c in enumerate(cr[i,j])},upper=-margin*cube_min/scale)
    for j in range(6):
        c=cr[:,j].sum(axis=0);scale=max(abs(c).max(),1e-15)
        add({v:float(a/scale) for v,a in enumerate(c)},lower=margin*cube_min/scale)
    matrix=sparse.csc_matrix((vals,(rows,cols)),shape=(len(lo),width))
    lower=np.r_[np.full(NV+H,-np.inf if score_basis else -1.),np.full(H,1e-8),
                np.full(rank,-1.),np.zeros(binary_count)]
    upper=np.r_[np.full(BASE,np.inf if score_basis else 1.),np.ones(rank+binary_count)]
    objective=np.zeros(width)
    result=milp(objective,integrality=np.r_[np.zeros(binary_base),np.ones(binary_count)],
                bounds=Bounds(lower,upper),constraints=LinearConstraint(matrix,np.array(lo),np.array(hi)),
                options={'time_limit':seconds,'mip_rel_gap':0.,'presolve':True})
    output={'status':int(result.status),'message':str(result.message),
            'beta':beta.tolist(),'signs':signs.tolist(),'margin':margin,
            'candidate_counts':list(map(len,candidates)),'solver':'bounded numerical MILP'}
    output['score_basis_rank']=rank
    if result.x is not None:
        theta=result.x
        score=features@theta[:NV]
        selected=[];binary=binary_base
        for group in candidates:
            index=int(np.argmax(theta[binary:binary+len(group)]))
            masks,desired,name=group[index]
            selected.append({'constraint':name,'masks':masks.tolist(),
                             'minimum_margin':float(min(score[masks]*desired))})
            binary+=len(group)
        output.update({'numerators':theta[:NV].reshape(H,N+1).tolist(),
                       'ell_signed':theta[ELL:K].tolist(),'k_absolute':theta[K:BASE].tolist(),
                       'witnesses':selected,'minimum_margin':min(w['minimum_margin'] for w in selected),
                       'maximum_constraint_violation':float(max(np.max(matrix@theta-np.array(hi)),np.max(np.array(lo)-matrix@theta)))})
    return output


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--seed-file',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--backgrounds',type=int,default=8)
    ap.add_argument('--seconds',type=float,default=120)
    ap.add_argument('--margin',type=float,default=1e-5)
    ap.add_argument('--restarts',type=int,default=8)
    ap.add_argument('--seed',type=int,default=876341)
    ap.add_argument('--score-basis',action='store_true')
    args=ap.parse_args();seed=json.loads(args.seed_file.read_text())
    beta=np.array(seed['beta']);rng=np.random.default_rng(args.seed)
    for restart in range(args.restarts):
        signs=np.array([-1 if restart>>h&1 else 1 for h in range(H)])
        choices=[]
        for faces,desired,name in FAMILIES:
            if len(faces)<=args.backgrounds:idx=np.arange(len(faces))
            else:idx=np.unique(np.r_[0,len(faces)-1,rng.choice(len(faces),args.backgrounds-2,replace=False)])
            choices.append(idx)
        start=time.time();record=solve(beta,signs,choices,args.margin,args.seconds,args.score_basis)
        record.update({'restart':restart,'seconds':time.time()-start})
        with args.out.open('a') as out:out.write(json.dumps(record)+'\n')
        print({k:record[k] for k in ['restart','status','message','seconds']},flush=True)
        if record.get('minimum_margin',-1)>0:
            print('NUMERICAL FACE WITNESS; EXACT VERIFICATION REQUIRED',flush=True);return


if __name__=='__main__':main()
