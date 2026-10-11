import numpy as np, sys
rng=np.random.default_rng(1)
d=1; L=int(sys.argv[1]); W=int(sys.argv[2]); g=float(sys.argv[3]); eta=float(sys.argv[4]); ns=int(sys.argv[5])
N=L*W; E=0.0; z=E+1j*eta
# block Laplacian Psi (nearest neighbour ring), M^{(B)}, m via self-consistent eq
PsiB=np.zeros((L,L)); 
for a in range(L): PsiB[a,(a+1)%L]=1; PsiB[a,(a-1)%L]=1
def solve_m():
    m=0.5j
    for _ in range(2000):
        MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); m=np.trace(MB)/L
    return m
m=solve_m(); MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); M=np.kron(MB,np.eye(W))
def gue(n):
    A=(rng.standard_normal((n,n))+1j*rng.standard_normal((n,n)))/np.sqrt(2*n)
    return (A+A.conj().T)/np.sqrt(2)
def blk(a): return slice(a*W,(a+1)*W)
a=0; c1=1; c2=2  # external block a, twist blocks c1!=c2 (c2 adjacent to c1)
Lt=[];Lo=[];Lo2=[];tr=[];trt=[]
for s in range(ns):
    V=np.zeros((N,N),complex)
    for b in range(L): V[blk(b),blk(b)]=gue(W)
    H=V+g*np.kron(PsiB,np.eye(W)); G=np.linalg.inv(H-z*np.eye(N)); Gc=G-M; Gs=G.conj().T
    X=Gs[:,blk(a)]@Gc[blk(a),:]/W          # G^* E_a Gc
    Lt.append(np.trace(X[blk(c2),blk(c1)])/W)   # twisted 2-loop Tr(G^* E_a Gc P_{c1c2})
    Lo.append(np.trace(X[blk(c1),blk(c1)])/W)   # ordinary (circled) 2-loop (a,c1)
    Y=Gs[:,blk(a)]@G[blk(a),:]/W
    Lo2.append(np.trace(Y[blk(c1),blk(c1)])/W)  # ordinary L^{(2)}_{(a,c1)}
    tr.append(np.trace(Gc[blk(c1),blk(c1)])/W)  # light weight tr(Gc E_{c1})
    trt.append(np.trace(Gc[blk(c2),blk(c1)])/W) # twisted 1-loop Tr(Gc P_{c1c2})
Lt=np.array(Lt);Lo=np.array(Lo);Lo2=np.array(Lo2);tr=np.array(tr);trt=np.array(trt)
B=1/(g*g+eta)+1/(L*eta); Psi2=B/W
print(f"L={L} W={W} g={g} eta={eta} Im m={m.imag:.3f} |m|={abs(m):.3f}  W^-d B={Psi2:.3e}  (W^-d B)^2={Psi2**2:.3e} (W^-dB)^1.5={Psi2**1.5:.3e}")
for name,v in [("twisted L~ (a;c1,c2)",Lt),("circled L (a,c1)",Lo),("L^(2) (a,c1)",Lo2),("tr(Gc E_c1)",tr),("twisted tr(Gc P)",trt)]:
    print(f"{name:22s} |E|={abs(v.mean()):.3e}  sd={v.std():.3e}  E|.|={abs(v).mean():.3e}")
