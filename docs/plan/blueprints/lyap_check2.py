from mpmath import mp, mpf, matrix, log, exp, sqrt
import mpmath
mp.dps = 600

# upper-triangular, eigenvalues = diagonal = e^3, e^1.5, e^0 (3 distinct blocks)
G = matrix([[exp(3), mpf('0.5'), mpf('0.5')],
            [0,      exp(mpf(3)/2), mpf('0.5')],
            [0,      0,            exp(0)]])

def matpow(M,n):
    R = mpmath.eye(M.rows)
    for _ in range(n): R = M*R
    return R

N = 50
GN = matpow(G,N)
Gr = GN.T*GN
E, Q = mpmath.eigsy(Gr)         # ascending eigenvalues
print("gram_N eigenvalue exponents (1/(2N) log):",
      [mpmath.nstr(log(E[i])/(2*N),6) for i in range(3)])   # expect ~ 0, 1.5, 3
# slowest = column 0 (smallest eigenvalue)
v = matrix([Q[i,0] for i in range(3)]); v = v/sqrt(sum(v[i]**2 for i in range(3)))
# CONSISTENCY: ||G^N v|| should be ~ e^{N*0}=1  (slowest singular value)
wN = matpow(G,N)*v; nN = sqrt(sum(wN[i]**2 for i in range(3)))
print("consistency  (1/N)log||G^N v|| =", mpmath.nstr(log(nN)/N,8), " (must be ~0 if v=slowest)")
print("growth of the Lambda-slowest eigenvector:")
for m in [10,20,30,40,50]:
    w = matpow(G,m)*v; nw = sqrt(sum(w[i]**2 for i in range(3)))
    print(f"  m={m:3d}: (1/m)log||G^m v|| = {mpmath.nstr(log(nw)/m,8)}")
# also the middle Lambda-eigenvector
vm = matrix([Q[i,1] for i in range(3)]); vm=vm/sqrt(sum(vm[i]**2 for i in range(3)))
print("growth of the Lambda-MIDDLE eigenvector:")
for m in [10,30,50]:
    w=matpow(G,m)*vm; nw=sqrt(sum(w[i]**2 for i in range(3)))
    print(f"  m={m:3d}: {mpmath.nstr(log(nw)/m,8)}")
