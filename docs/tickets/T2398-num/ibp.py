import numpy as np
rng=np.random.default_rng(7)
L=4; W=3; g=0.8; z=0.1+0.5j; N=L*W; ns=400000
PsiB=np.zeros((L,L))
for a in range(L): PsiB[a,(a+1)%L]=1; PsiB[a,(a-1)%L]=1
m=0.5j
for _ in range(5000): MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); m=np.trace(MB)/L
MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); M=np.kron(MB,np.eye(W)); Psi=np.kron(PsiB,np.eye(W))
c1,c2=1,2
tau=np.zeros((N,N)); 
for o in range(W): tau[c1*W+o,c2*W+o]=1
P=tau/W
blk=lambda a: slice(a*W,(a+1)*W)
# batch of GUE blocks
def sample(n):
    A=(rng.standard_normal((n,L,W,W))+1j*rng.standard_normal((n,L,W,W)))/np.sqrt(2*W)
    V=(A+np.conj(np.transpose(A,(0,1,3,2))))/np.sqrt(2)
    H=np.zeros((n,N,N),complex)
    for b in range(L): H[:,blk(b),blk(b)]=V[:,b]
    return H+g*Psi
acc=np.zeros(5,complex); S=np.zeros((N,N)); 
for b in range(L): S[blk(b),blk(b)]=1.0/W
bs=20000
for it in range(ns//bs):
    H=sample(bs); G=np.linalg.inv(H-z*np.eye(N)); Gc=G-M
    Tt=np.einsum('nij,ji->n',Gc,P)                       # Tr(Gc P)
    tr=np.array([np.einsum('nii->n',Gc[:,blk(b),blk(b)])/W for b in range(L)]).T  # tr(Gc E_b)
    SG=np.zeros((bs,N,N),complex)
    for b in range(L):
        for o in range(W): SG[:,b*W+o,b*W+o]=tr[:,b]
    X=np.einsum('nij,njk,kl,lm,mi->n',G,SG,M,P,np.eye(N))     # Tr(G S[Gc] M P)
    MPG=np.einsum('ij,jk,nkl->nil',M,P,G); GPG=np.einsum('nij,jk,nkl->nil',G,P,G)
    S1=np.einsum('xw,nwx,nxw->n',S,MPG,GPG)                   # sum S_xw (MPG)_wx (GPG)_xw
    acc+=np.array([Tt.sum(),X.sum(),(Tt*Tt).sum(),(X*Tt).sum(),S1.sum()])
acc/=ns
print(f"E[T~]        = {acc[0]:.5f}   u*E[Tr(G S[Gc] M P)] = {acc[1]:.5f}")
print(f"E[T~^2]      = {acc[2]:.5f}   E[X T~] + E[S1]       = {acc[3]+acc[4]:.5f}   (E[X T~]={acc[3]:.5f}, E[S1]={acc[4]:.5f})")
