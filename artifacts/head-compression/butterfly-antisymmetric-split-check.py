#!/usr/bin/env python3
"""Exact polynomial checks for the scoped antisymmetric split audit."""
import random
import sympy as s
x=s.Symbol('x');mid=s.Rational(1,2);rng=random.Random(11024);cases=0
reflect=lambda p:s.Poly(p.as_expr().subs(x,1-x),x)
for M in (2,4,6,8):
 for trial in range(10):
  roots=rng.sample(range(1,91),2*M)
  Q=[s.Poly(s.prod(x-s.Rational(a,400) for a in roots[j*M:(j+1)*M]),x) for j in range(2)]
  D=[reflect(q)-q for q in Q];G=s.gcd(*D).monic();g=G.degree()
  assert g%2==1 and 1<=g<=M-1 and reflect(G)==-G
  U=[z.exquo(G) for z in D];assert all(reflect(z)==z for z in U)
  for k in range((g+1)//2):
   S=s.Poly((x-mid)**(2*k+1),x);N0=S*U[0];N1=-S*U[1];N=N0*Q[1]+N1*Q[0]
   assert reflect(N0)==-N0 and reflect(N1)==-N1 and reflect(N)==-N
   assert (N0*D[1]+N1*D[0]).is_zero
   for t in (s.Rational(51,100),s.Rational(3,4),s.Rational(1),s.Rational(2)):
    assert all(z.eval(t)<0 for z in D)
    assert N0.eval(t)*N1.eval(t)<0
   cases+=1
 # Polynomial-preimage closure is an exact identity; real-root geometry
 # for sufficiently small shifts is established separately in the proof.
 Q0=s.Poly(s.prod(x-s.Rational(j+1,100) for j in range(M)),x);delta=s.Rational(1,10**12)
 QL=Q0-delta;QR=Q0+delta;D0=reflect(QL)-QL;D1=reflect(QR)-QR;assert D0==D1
 for k in range(M//2):
  NL=s.Poly((x-mid)**(2*k+1),x);NR=-NL;N=NL*QR+NR*QL
  assert N==2*delta*NL and reflect(N)==-N
  cases+=1
print(f'{cases} exact antisymmetric split cases passed; no general decoder obstruction asserted')
