import numpy as np, sys
rng=np.random.default_rng(2)
L=int(sys.argv[1]); W=int(sys.argv[2]); g=float(sys.argv[3]); eta=float(sys.argv[4]); ns=int(sys.argv[5])
N=L*W; z=0.0+1j*eta
PsiB=np.zeros((L,L))
for a in range(L): PsiB[a,(a+1)%L]=1; PsiB[a,(a-1)%L]=1
m=0.5j
for _ in range(3000): MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); m=np.trace(MB)/L
MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); M=np.kron(MB,np.eye(W))
Mpm=np.abs(MB)**2; Th=np.linalg.inv(np.eye(L)-Mpm)   # Theta^{(+,-)} (static, t=1 form)
def gue(n):
    A=(rng.standard_normal((n,n))+1j*rng.standard_normal((n,n)))/np.sqrt(2*n); return (A+A.conj().T)/np.sqrt(2)
blk=lambda a: slice(a*W,(a+1)*W)
a=0; c1=1; c2=2
Lt=[];Lo=[]
for s in range(ns):
    V=np.zeros((N,N),complex)
    for b in range(L): V[blk(b),blk(b)]=gue(W)
    G=np.linalg.inv(V+g*np.kron(PsiB,np.eye(W))-z*np.eye(N)); Gs=G.conj().T
    Y=Gs[:,blk(a)]@G[blk(a),:]/W
    Lt.append(np.trace(Y[blk(c2),blk(c1)])/W); Lo.append(np.trace(Y[blk(c1),blk(c1)])/W)
Lt=np.array(Lt);Lo=np.array(Lo)
Kt=sum(Th[a,ap]*np.conj(MB[ap,c2])*MB[ap,c1] for ap in range(L))/W
Ko=(Th@Mpm)[a,c1]/W
print(f"L={L} W={W} g={g} eta={eta}: row sum |M|^2={Mpm.sum(1)[0]:.3f}")
print(f"ordinary  E L2(a,c1)={Lo.mean():.4e}  K={Ko:.4e}  |E-K|={abs(Lo.mean()-Ko):.1e}  sd={Lo.std():.1e}  err={Lo.std()/np.sqrt(ns):.1e}")
print(f"twisted   E Lt(a;c1,c2)={Lt.mean():.4e}  Kt={Kt:.4e}  |E-Kt|={abs(Lt.mean()-Kt):.1e}  sd={Lt.std():.1e}  err={Lt.std()/np.sqrt(ns):.1e}")
