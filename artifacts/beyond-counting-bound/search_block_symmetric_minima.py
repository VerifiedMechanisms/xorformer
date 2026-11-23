"""Search full-cube unit-margin minima through coordinate-block symmetry.

All constraints are represented by block Hamming weights. Multipliers lift by
averaging over each orbit. Full-model rank also requires the standard block
representations, checked separately below. Floating outcomes are candidates,
never certificates. Run long searches with heavy and single-thread BLAS.
"""
import argparse
import itertools
import json
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.linalg import qr
from scipy.optimize import linprog, minimize


def score_jac(theta, x, sizes, heads, orientation):
    k = len(sizes)
    u = theta[:k*heads].reshape(k, heads)
    p = np.exp(theta[k*heads:].reshape(k, heads))
    total = 1 + sizes @ p
    den_pos = 1 + x @ p
    complement = 1 + (sizes[None, :] - x) @ p
    den = np.where(orientation[None, :] > 0, den_pos, complement / total)
    num = x @ u
    value = (num / den).sum(axis=1)
    ju = (x[:, :, None] / den[:, None, :]).reshape(len(x), k*heads)
    dd_pos = x[:, :, None] * p[None, :, :]
    dd_neg = p[None, :, :] * (
        (sizes[None, :, None] - x[:, :, None]) * total[None, None, :]
        - sizes[None, :, None] * complement[:, None, :]) / total[None, None, :]**2
    dd = np.where(orientation[None, None, :] > 0, dd_pos, dd_neg)
    jb = (-num[:, None, :] * dd / den[:, None, :]**2).reshape(len(x), k*heads)
    return value, np.c_[ju, jb], den, num


def check_derivative():
    rng = np.random.default_rng(320014)
    sizes = np.array([3., 4., 5.]); heads = 3
    x = np.array(list(itertools.product(range(4), range(5), range(6))), dtype=float)
    theta = rng.normal(size=18); orientation = np.array([1, -1, 1])
    _, jac, _, _ = score_jac(theta, x, sizes, heads, orientation)
    error = 0.
    for i in range(len(theta)):
        delta = np.zeros_like(theta); delta[i] = 1e-6
        diff = (score_jac(theta+delta,x,sizes,heads,orientation)[0]
                - score_jac(theta-delta,x,sizes,heads,orientation)[0])/2e-6
        error = max(error, float(np.max(abs(diff-jac[:,i]))))
    assert error < 1e-7
    # Independently expand one actual Boolean row and each repeated parameter.
    from search_full_cube_unit_minima import mixed_score_jac
    integer_sizes = sizes.astype(int)
    group = np.repeat(np.arange(3), integer_sizes)
    full_theta = np.r_[theta[:9].reshape(3,heads)[group].ravel(),
                       theta[9:].reshape(3,heads)[group].ravel()]
    full_x = np.zeros((len(x),len(group)))
    for row,counts in enumerate(x.astype(int)):
        start=0
        for j,count in enumerate(counts):
            full_x[row,start:start+count]=1
            start+=integer_sizes[j]
    value,full_jac=mixed_score_jac(full_theta,full_x,len(group),heads,orientation)
    assert np.max(abs(value-1-score_jac(theta,x,sizes,heads,orientation)[0]))<1e-12
    full_ju=full_jac[:,:len(group)*heads].reshape(len(x),len(group),heads)
    full_jb=full_jac[:,len(group)*heads:].reshape(len(x),len(group),heads)
    aggregated=np.c_[np.stack([full_ju[:,group==j].sum(axis=1) for j in range(3)],axis=1).reshape(len(x),9),
                     np.stack([full_jb[:,group==j].sum(axis=1) for j in range(3)],axis=1).reshape(len(x),9)]
    assert np.max(abs(aggregated-jac))<1e-10
    return error


def exact_start(u, weights, sizes, orientation, x):
    h=u.shape[1]
    constants=np.where(orientation>0,1,1+sizes@weights)
    fractions=[]
    for row in x.astype(int):
        fractions.append(sum((Fraction(int(row@u[:,j]),
            int(constants[j]+orientation[j]*(row@weights[:,j]))) for j in range(h)),Fraction(0)))
    negatives=[-v for v in fractions if v<0]
    if not negatives or not any(v>0 for v in fractions): return None
    gamma=min(negatives)
    labels=np.array([1. if v>=0 else -1. for v in fractions])
    theta=np.r_[(u/constants[None,:]).ravel(),np.log(weights).ravel()]
    return theta,labels,float(gamma),str(gamma)


def checkerboard_start(sizes, x, rng):
    """Two affine factors, followed by the proved one-head origin repair.

    The full grid margins are checked using rational arithmetic before the
    parameters are converted to floats. This supplies more curved labels than
    typical random sums of three ratios.
    """
    k=len(sizes);n=int(sum(sizes))
    a=Fraction(int(rng.integers(0,sizes[0])),1)+Fraction(1,2)
    b=Fraction(int(rng.integers(0,sizes[1])),1)+Fraction(1,2)
    eps=Fraction(1,8*n);delta=eps/4
    d=[Fraction(1),1-delta*a]
    slopes=[[-eps]*k,[-eps+delta]+[-eps]*(k-1)]
    # L1=t0-a, L2=t1-b, B2-B1=delta*L1.
    r0=a*b/(d[0]*d[1])
    cs=[1/(delta*r0),-1/(delta*r0)]
    normalized_b=[[slopes[h][j]/d[h] for j in range(k)] for h in range(2)]
    normalized_u=[[cs[h]*((1 if j==1 else 0)+b*normalized_b[h][j])/d[h]
                   for j in range(k)] for h in range(2)]
    scores=[]
    for row in x.astype(int):
        score=1+sum((sum(normalized_u[h][j]*int(row[j]) for j in range(k)) /
                     (1+sum(normalized_b[h][j]*int(row[j]) for j in range(k)))
                     for h in range(2)),Fraction(0))
        expected=(Fraction(int(row[0]))-a)*(Fraction(int(row[1]))-b)
        expected/=r0*(d[0]+sum(slopes[0][j]*int(row[j]) for j in range(k)))*(
            d[1]+sum(slopes[1][j]*int(row[j]) for j in range(k)))
        assert score==expected and score!=0
        scores.append(score)
    margin=min([Fraction(1)]+[abs(z) for z in scores])
    q=2/margin;K=q-1
    for row,score in zip(x.astype(int),scores):
        repaired=q*score-K/(1+2*K*int(sum(row)))
        assert abs(repaired)>Fraction(3,2) and (repaired>0)==(score>0)
    u=np.array([[float(q*normalized_u[h][j]) for h in range(2)]+[float(2*K*K)]
                for j in range(k)])
    p=np.zeros_like(u)
    for h in range(2):
        tail=1+sum(Fraction(int(sizes[j]))*normalized_b[h][j] for j in range(k))
        assert tail>0 and all(z<0 for z in normalized_b[h])
        p[:,h]=[float(-normalized_b[h][j]/tail) for j in range(k)]
    p[:,2]=float(2*K)
    scale=max(1.,float(np.max(abs(u))))
    theta=np.r_[(u/scale).ravel(),np.log(p).ravel()]
    labels=np.array([1. if z>0 else -1. for z in scores])
    gamma=2/scale
    return theta,labels,gamma,'2 / floating_common_numerator_scale',np.array([-1,-1,1])


def full_rank_diagnostics(theta,x,sizes,h,orientation,active,jac):
    _,_,den,num=score_jac(theta,x,sizes,h,orientation)
    # Coordinate changes within one block, of total sum zero, see this feature
    # vector for every orbit with a nonconstant block. Natural b coordinates
    # are used; the log-p change of coordinates is invertible in the interior.
    feature=np.c_[1/den,-num/den**2]
    block_sv=[]
    for j,size in enumerate(sizes):
        rows=active[(x[active,j]>0)&(x[active,j]<size)]
        if len(rows)<2*h:
            block_sv.append(0.)
        else:
            block_sv.append(float(np.linalg.svd(feature[rows],compute_uv=False)[-1]))
    reduced_sv=float(np.linalg.svd(jac[active],compute_uv=False)[-1]) if len(active)>=jac.shape[1] else 0.
    return reduced_sv,block_sv


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--seconds',type=float,default=7200)
    ap.add_argument('--trial-seconds',type=float,default=180)
    ap.add_argument('--seed',type=int,default=96234011)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    print(json.dumps(dict(status='DERIVATIVE_AND_LIFT_CHECK_PASS',error=check_derivative())),flush=True)
    rng=np.random.default_rng(args.seed);start=time.monotonic();trial=0
    class Expired(Exception):pass
    cases=[([8,8],2),([8,8],3),([8,8],4),([5,5,5],3),([5,5,5],4),([12,12],3),([6,6,6],3)]
    with (args.output/'results.jsonl').open('a',buffering=1) as log:
        while time.monotonic()-start<args.seconds:
            sizes0,h=cases[trial%len(cases)];sizes=np.array(sizes0);k=len(sizes);pcount=2*k*h
            x=np.array(list(itertools.product(*(range(s+1) for s in sizes))),dtype=float)[1:]
            orientation=rng.choice([-1,1],size=h)
            weights=rng.integers(1,7,size=(k,h))
            u=rng.integers(-15,16,size=(k,h))
            if trial%3==0:u[:,-1]=-u[:,:-1].sum(axis=1)
            initial=exact_start(u,weights,sizes,orientation,x)
            seed_kind='integer_ratios'
            if h==3 and trial%2==0:
                theta,y,gamma,gamma_exact,orientation=checkerboard_start(sizes,x,rng)
                initial=theta,y,gamma,gamma_exact
                seed_kind='exact_checkerboard_origin_repair'
            if initial is None:trial+=1;continue
            theta,y,gamma,gamma_exact=initial
            value=score_jac(theta,x,sizes,h,orientation)[0]
            assert (y*value-gamma*(y<0)).min()>-1e-9
            begin=time.monotonic();history=[];cache={}
            scale_weights=np.repeat(sizes,h)
            def evaluate(t):
                if time.monotonic()-start>args.seconds or time.monotonic()-begin>args.trial_seconds:raise Expired
                if 'theta' not in cache or not np.array_equal(t,cache['theta']):
                    value,jac,_,_=score_jac(t,x,sizes,h,orientation)
                    cache.update(theta=t.copy(),value=value,jac=jac)
                return cache
            try:
                for stage in range(4):
                    norm_scale=max(1e-16,float(scale_weights@theta[:k*h]**2))
                    result=minimize(lambda t:.5*float(scale_weights@t[:k*h]**2)/norm_scale,theta,
                        jac=lambda t:np.r_[scale_weights*t[:k*h]/norm_scale,np.zeros(k*h)],
                        method='SLSQP',bounds=[(None,None)]*(k*h)+[(-18.,18.)]*(k*h),
                        constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-gamma*(y<0),
                                          jac=lambda t:y[:,None]*evaluate(t)['jac'])],
                        options=dict(maxiter=2500,ftol=1e-13,disp=False))
                    theta=result.x
                    value,jac,_,_=score_jac(theta,x,sizes,h,orientation)
                    slack=y*value-gamma*(y<0)
                    history.append(dict(stage=stage,solver_status=int(result.status),iterations=int(result.nit),
                        relative_slack=float(slack.min()/gamma),norm=float(scale_weights@theta[:k*h]**2),
                        boundary_distance=float(18-np.max(abs(theta[k*h:])))))
                active=np.flatnonzero(slack<=max(1e-10,1e-5*gamma))
                reduced_sv,block_sv=full_rank_diagnostics(theta,x,sizes,h,orientation,active,jac)
                record=dict(trial=trial,sizes=sizes0,heads=h,seed_kind=seed_kind,orbits=len(x),active_count=len(active),
                    reduced_parameter_count=pcount,reduced_min_singular=reduced_sv,block_min_singular=block_sv,
                    gamma=gamma_exact,status='UNKNOWN',history=history,elapsed_seconds=time.monotonic()-start)
                if slack.min()>-1e-7*gamma and history[-1]['boundary_distance']>1e-3 and reduced_sv>1e-8 and min(block_sv)>1e-8:
                    signed=y[active,None]*jac[active]
                    gradient=np.r_[scale_weights*theta[:k*h],np.zeros(k*h)]
                    m=len(active);column_scale=np.maximum(np.linalg.norm(signed,axis=0),1e-14)
                    mat=signed.T/column_scale[:,None];rhs=gradient/column_scale
                    # Maximize a common positive lower bound on every active
                    # orbit multiplier; exact replay is still required.
                    lp=linprog(np.r_[np.zeros(m),-1.],A_eq=np.c_[mat,np.zeros(pcount)],b_eq=rhs,
                        A_ub=np.c_[-np.eye(m),np.ones(m)],b_ub=np.zeros(m),
                        bounds=[(0,None)]*m+[(None,None)],method='highs')
                    record.update(status='FLOATING_FULL_RANK_CANDIDATE',dual_status=int(lp.status),
                        min_multiplier=float(lp.x[-1]) if lp.success else None)
                    if lp.success and lp.x[-1]>1e-9:record['status']='FLOATING_POSITIVE_DUAL_CANDIDATE'
                    name=f'candidate-{trial}.json'
                    data=dict(record,theta=theta.tolist(),orientation=orientation.tolist(),labels=y.tolist(),
                        orbit_points=x.astype(int).tolist(),active_indices=active.tolist(),
                        multipliers=lp.x[:-1].tolist() if lp.success else None,main_target_proved=False)
                    (args.output/name).write_text(json.dumps(data,indent=2)+'\n');record['candidate']=name
            except Expired:
                record=dict(trial=trial,sizes=sizes0,heads=h,status='TIME_LIMIT_UNKNOWN',history=history,
                            elapsed_seconds=time.monotonic()-start)
            except (ValueError,np.linalg.LinAlgError,FloatingPointError) as exc:
                record=dict(trial=trial,status='NUMERICAL_FAILURE_UNKNOWN',error=str(exc))
            log.write(json.dumps(record)+'\n')
            if trial%10==0 or 'candidate' in record:
                print(json.dumps({a:b for a,b in record.items() if a!='history'}),flush=True)
            trial+=1
    print(json.dumps(dict(status='FINISHED_UNKNOWN',trials=trial,elapsed_seconds=time.monotonic()-start)),flush=True)


if __name__=='__main__':main()
