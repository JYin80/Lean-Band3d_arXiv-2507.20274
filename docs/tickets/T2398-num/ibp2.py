import numpy as np, time
rng=np.random.default_rng(7)
L=4; W=3; g=0.8; z=0.1+0.5j; N=L*W; ns=int(4.0e6)
PsiB=np.zeros((L,L))
for a in range(L): PsiB[a,(a+1)%L]=1; PsiB[a,(a-1)%L]=1
m=0.5j
for _ in range(5000): MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); m=np.trace(MB)/L
MB=np.linalg.inv(g*PsiB-(z+m)*np.eye(L)); M=np.kron(MB,np.eye(W)); Psi=np.kron(PsiB,np.eye(W))
c1,c2=1,2
tau=np.zeros((N,N))
for o in range(W): tau[c1*W+o,c2*W+o]=1
P=tau/W; MP=M@P
S=np.zeros((N,N))
for b in range(L): S[b*W:(b+1)*W,b*W:(b+1)*W]=1.0/W
Eb=[np.zeros((N,N)) for b in range(L)]
for b in range(L): Eb[b][b*W:(b+1)*W,b*W:(b+1)*W]=np.eye(W)
acc=np.zeros(5,complex); bs=10000; t0=time.time()
for it in range(ns//bs):
    A=(rng.standard_normal((bs,L,W,W))+1j*rng.standard_normal((bs,L,W,W)))/np.sqrt(2*W)
    V=(A+np.conj(np.transpose(A,(0,1,3,2))))/np.sqrt(2)
    H=np.zeros((bs,N,N),complex)
    for b in range(L): H[:,b*W:(b+1)*W,b*W:(b+1)*W]=V[:,b]
    G=np.linalg.inv(H+g*Psi-z*np.eye(N)); Gc=G-M
    Tt=np.einsum('nij,ji->n',Gc,P)
    SG=np.zeros((bs,N,N),complex)
    for b in range(L):
        trb=np.einsum('nii->n',Gc[:,b*W:(b+1)*W,b*W:(b+1)*W])/W
        SG+=trb[:,None,None]*Eb[b][None]
    X=np.einsum('nij,ji->n',G@SG@MP,np.eye(N))      # Tr(G S[Gc] M P)
    MPG=MP[None]@G; GPG=G@P@G
    S1=np.einsum('xw,nwx,nxw->n',S,MPG,GPG)
    acc+=np.array([Tt.sum(),X.sum(),(Tt*Tt).sum(),(X*Tt).sum(),S1.sum()])
acc/=ns
print(f"time {time.time()-t0:.0f}s  ns={ns}")
print(f"E[T~]   = {acc[0]:.5f}    E[Tr(G S[Gc] M P)] = {acc[1]:.5f}")
print(f"E[T~^2] = {acc[2]:.5f}    E[X T~] + E[S1]    = {acc[3]+acc[4]:.5f}   (E[X T~]={acc[3]:.5f}, E[S1]={acc[4]:.5f})")
