from mpmath import mp, mpf, matrix, log, exp, sqrt
import mpmath
mp.dps = 600
G = matrix([[exp(3), mpf('0.5'), mpf('0.5')],
            [0, exp(mpf(3)/2), mpf('0.5')],
            [0, 0, exp(0)]])
def matpow(M,n):
    R=mpmath.eye(M.rows)
    for _ in range(n): R=M*R
    return R
# FIXED slow vector from large N
NB=46
GNB=matpow(G,NB); Gr=GNB.T*GNB; E,Q=mpmath.eigsy(Gr)
v=matrix([Q[i,0] for i in range(3)]); v=v/sqrt(sum(v[i]**2 for i in range(3)))  # Lambda-slow
print("overlap |<v, u_j(n)>| decay rates (1/n)log, v=Lambda-slow (block2,lam=0):")
print("  block-specific predicts: j=0(lam3)->-3, j=1(lam1.5)->-1.5 ; band-edge predicts both ->-1.5")
for n in [12,20,28,36]:
    Gn=matpow(G,n); Grn=Gn.T*Gn; En,Qn=mpmath.eigsy(Grn)  # ascending; col2=fastest
    # u_j(n): col index by exponent — col0 slow(lam0=0), col1 mid(1.5), col2 fast(3)
    u_fast=matrix([Qn[i,2] for i in range(3)])  # lam=3 block (j=0 fastest)
    u_mid =matrix([Qn[i,1] for i in range(3)])  # lam=1.5
    ov_fast=abs(sum(v[i]*u_fast[i] for i in range(3)))
    ov_mid =abs(sum(v[i]*u_mid[i]  for i in range(3)))
    print(f"  n={n:3d}: <v,u_fast>={mpmath.nstr(log(ov_fast)/n,6)}  <v,u_mid>={mpmath.nstr(log(ov_mid)/n,6)}")
