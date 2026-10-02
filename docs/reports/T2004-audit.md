Auditor model: claude-opus-5-5
# T2004 audit (round 1) — KL-D1 design: `𝒦`, `(WI_calK)`, `(eq:bcal_k)` pins (report only)
Date (`date -u`): Fri Oct  2 23:21:46 UTC 2026. Branch `t/T2004` @ 64b58eb, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2004-audit1` (detached). Paper: `1_2_Intro_model_result.tex:986–1062, 1066–1187`, `A_deterministic_estimates.tex:600–760`, `3_5_Loop_Hierarchy.tex:1001–1006`.

## 1. Build, axioms, scope
```
$ lake build RBM3D.Probe.T2004Pins > build.txt 2>&1; echo exit=$?; grep -n 'Built RBM3D.Probe' build.txt; tail -1 build.txt; grep -c 'warning\|error' build.txt
exit=0
25:ℹ [3253/3253] Built RBM3D.Probe.T2004Pins (21s)
Build completed successfully (3253 jobs).
0
$ grep -c 'depends on axioms' build.txt; grep 'depends on axioms' build.txt | grep -vc 'propext, Classical.choice, Quot.sound\]'
71
0
$ grep -o 'constants with prefix.*' build.txt
constants with prefix RBM.Loop.KL; axioms used: [propext, Classical.choice, Quot.sound]; constants using another axiom: 0
constants with prefix RBM.Loop.KLinst_; axioms used: [propext, Classical.choice, Quot.sound]; constants using another axiom: 0
$ grep -nE '^ *(axiom|sorry|admit)|native_decide|sorry' RBM3D/Probe/T2004Pins.lean | wc -l
0
$ git diff --name-only main...t/T2004; git diff main...t/T2004 -- RBM3D/Loop RBM3D/Defs RBM3D/Propagator RBM3D.lean | wc -l
RBM3D/Probe/T2004Pins.lean
0
```
`#axioms_with_prefix` (probe l.1212) iterates `env.constants.map₂` and calls `collectAxioms` on each: a real check. Sole writable files respected; no frozen signature touched; probe stays on the branch (report-only).

## 2. Statements against the paper (read from the file, l.119–870)
| Lean | paper | verdict |
|---|---|---|
| `KLK` = `KLgen`: `n=1` `m(σ)`; `n=2` `kTwo` = `W^{-d}m₁m₂Θ_{tm₁m₂}(a₁,a₂)`; `n≥3` `KLn` = `∏m · (W^{-d})^{n-1} Σ_{F∈TSP n}` tree value, leaves `Θ^{(σ_v,σ_{v+1})}`, internal `Θ^{(σ_i,σ_j)}−I` | `Def_Ktza` via `(eq_Ktree)` (option B; ODE = pin) | PASS (definition choice = ticket item 2) |
| `KLisKLoopPin`: `IsKLoop … (Ico 0 1) KLK` for all `d L W g E`, `3≤L`, `1≤W`, `\|E\|<2` | `(pro_dyncalK)`: `treeEqRhs` sums `k∈[1,n]`, `l∈(k,n]`, `W^d Σ_{a,b} K(cutL)S_{ab}K(cutR)` (TreeRep.lean:145); `(eq:initial_K)`=`MLoop` = `W^{-(k-1)d}∏m 1(a₁=…=a_k)` (`(eq:KMloop)` RBM form); `𝒦^{(1)}=m` | PASS; `t∈[0,1)` = T2004d |
| `KLuniquePin`: any `IsKLoop` family equals `KLK` on `[0,1)`, `WF`, `length ≥ 1` | "unique solution" | PASS (no `TwoLoopBounded` premise; retired by `KLretire_twoLoopBounded`, compiled) |
| `KLK_two`, `KLK_three` (proved) | `(Kn2sol)`: `W^{-d}(Θ M^{(σ₁σ₂)})_{a₁a₂}`, `M^{(σ₁σ₂)}=m₁m₂I`; `(Kn3sol)` with `𝓜^{(3)}=W^{-2d}m₁m₂m₃1(b₁=b₂=b₃)` | PASS (exact) |
| `KLwardPin`: `σ=(s,μ,¬s)`, `a.length=μ.length+1`, `Σ_x K(σ,(a,x)) = (2iW^dη_t)⁻¹(K(+::μ,a)−K(−::μ,a))`, `η_t = Gauss.etaT = (1-t)Im mE` | `(WI_calK)`, `σ₁=−σ_n`, `n≥2` (`μ=[]`), `(eta)` 1_2:720 | PASS; `KLward_two` proved (both orders) |
| `KLBoundAt d n κ gmax`: `∀τ>0 ∃C>0 ∀p:KLPar ∀σ a, ‖K‖ ≤ C L^τ (W^{-d}B_{t,0})^{n-1}`; `KLboundPin` for `3≤d`, `1≤n`, under `KLPT` | `(eq:bcal_k)`: fixed `d≥3`, every `n`, `t∈[0,1)`, max over `σ,a`, `≺` | PASS; C before `L,W,g,E,t,σ,a`; `L^τ ⇒ N^τ` by `KLBoundAt_prec` (`N=(WL)^d`, the scale T2002 fixed); `g ≤ gmax` = T2004b; loss form = T2004e |
| `KLwardIneqAt` (`n≥2`): `Σ_x‖K(σ,(a,x))‖ ≤ C L^τ (W^dη_t)⁻¹(W^{-d}B_{t,0})^{n-2}`, every `σ` | `(wardineq_K)` 3_5:1003 | PASS |
| `KLKpi` (`∏m` inside), `KLK_eq_sum_Kpi` (proved, `n≥3`), `KLKpiBoundAt`: `‖K^{(π)}‖ ≤ C L^τ B_{t,0}^{n-1}`, every `π` | `(eq:defKpi)`, `(eq_K-Kpi)` A:621, `(eq:K-pi-bound)` A:675 | PASS |
| `KLpureAt` (`KLShort` only), `KLmoleculeAt` (`Σ^{(∅)}`, every `σ`), `KLsumZeroAt` (`n` even ≥4, alternating, `δ₀=x` fixed: signed `≤C(1-t)`, absolute `≤C(g²+1-t)`) | `(res_pureKes)` A:645, `(eq:molecule-decay)` A:691, `(eq:Sigma-empty-sum-zero)` A:731 | PASS |
| `KLindStepAt`: root leaf `r` long, other leaves `Θ^{(σ_i,σ_{i+1})}`, `Σ_b‖Σ_{δ_r=b}Σ^{(∅)}∏_{i≠r}Θ‖ ≤ C L^τ B_{t,0}^{n-2}` | `(eq:ind-step-bound)` A:703 with `Θ̃∈{Θ, tSΘ^{(+,-)}}` | PASS as route pin (restricted `Θ̃`; observation O2) |
| `KLPT` = `KLDecay` (5, `(+,-)` only; other charges by merged property 4 `norm_Theta_apply_le`), `KLShort` (5'), `KLDiffOne/Two` (6, 7; `\|r\|≤c\|a\|`, `c<1`), `KLZero` (8); constants depend on `d, κ, gmax` (+`c, τ`), uniform in `g∈(0,gmax]`, `L≥3`, `t∈[0,1)` | `lem_propTH` 5–8 | PASS as local PT stand-in (ticket: "written locally as `Prop` hypotheses"); range `c<1` = T2004c |

Quantifier order everywhere: `(d, n, κ, gmax[, c], τ)` → constants → `p = (L, W, g, E, t)` → `σ, a`: matches "constants chosen before `λ, L, W`". Index ranges: `n≥1` (bound), `n≥2` (Ward, wardineq), `n≥3` (Kpi, molecule, indStep), `n≥4` even (sum-zero): as in the paper.
T2004c spot check (by hand): at `t=0`, `Θ_0=I`; `a≠0`, `r=−a`: LHS of (prop:BD1) `=|1−0|=1`, RHS `≺ |a|/(|a|+1)^{d-1} ≤ (|a|+1)^{-(d-2)}`, false for `|a|≍L`, `d≥3`: the range `|r|≤c|a|`, `c<1`, is needed.

## 3. Hidden hypotheses, vacuity, cycles
- `KLPar`: explicit range fields only (`3≤L`, `1≤W`, `0<g≤gmax`, `|E|≤2−κ`, `0≤t<1`); inhabited by `KLinstPar` (compiled). `KLPT`: a named bundle of the five PT shapes, always an explicit hypothesis (`hPT`), never hidden in `KLPar`.
- No cycle: proofs use merged RBM3D declarations only (`Theta`, `Bparam`, `TSP`, `thetaEdge`, `kTwo`, `IsKLoop`, `norm_Theta_apply_le`, `sum_Theta_row_of_three_le`, `sum_exp_decay_centre`, `kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop`, `LoopVec.exists_toLoop`); no pin is used to prove itself.
- External-hypothesis limit checks (TEAM §8.14): report (a) rows 5, 7 and `ext` blocks `bd`, `short`; and the auditor's independent check below (`t→1`, `g→0`, `g=gmax`, `L=31`).
```
$ python3 aud2.py   # auditor script (scratchpad), d=3, W=1, l1 distance, exact Θ by FFT; ratios = |lhs|/(pinned rhs without C, L^τ)
L=15 g=0.02 1-t=1e-09 E=0.0 B0=2.99e+05 | KLDecay 1.418 KLShort 0.500 KLZero 0.238 | bcal n=2 0.994 n=3 0.494 | WI n=3 rel.err 2.8e-08 | wardineq n=3 0.496
L=15 g=1 1-t=1e-09 E=1.5 B0=2.96e+05 | KLDecay 1.419 KLShort 0.455 KLZero 1.664 | bcal n=2 1.000 n=3 0.756 | WI n=3 rel.err 1.4e-07 | wardineq n=3 0.500
L=31 g=0.5 1-t=1e-06 E=0.0 B0=37.6 | KLDecay 1.433 KLShort 0.590 KLZero 0.614 | bcal n=2 0.959 n=3 0.478 | WI n=3 rel.err 2.9e-11 | wardineq n=3 0.451
L=31 g=0.02 1-t=5e-01 E=0.0 B0=2 | KLDecay 0.998 KLShort 0.667 KLZero 0.998 | bcal n=2 0.998 n=3 0.665 | WI n=3 rel.err 5.1e-09 | wardineq n=3 0.000
```
```python
import numpy as np  # independent auditor check of the KL pins at extreme inputs, d=3, W=1, l1 distance (zdistD)
d=3
def ax(L): a=np.arange(L); return np.minimum(a,L-a)
def dist(L): A=ax(L); return (A[:,None,None]+A[None,:,None]+A[None,None,:]).astype(float)
def shat(L,g):
    k=2*np.pi*np.arange(L)/L; c=np.cos(k); return (1+2*g*g*(c[:,None,None]+c[None,:,None]+c[None,None,:]))/(1+2*d*g*g)
def Th(L,g,xi): return np.fft.ifftn(1/(1-xi*shat(L,g)))   # Theta_xi(0,x)
def mm(E): m=(-E+1j*np.sqrt(4-E*E))/2; return {1:m,-1:np.conj(m)}
def B(L,g,tau,K): return 1/((g*g+tau)*(K+1)**(d-2))+1/(L**d*tau)
for (L,g,tau,E) in [(15,0.02,1e-9,0),(15,1.0,1e-9,1.5),(31,0.5,1e-6,0),(31,0.02,0.5,0)]:
    t=1-tau; m=mm(E); D=dist(L); B0=B(L,g,tau,0); eta=tau*m[1].imag
    T={(a,b):Th(L,g,t*m[a]*m[b]) for a in (1,-1) for b in (1,-1)}
    ell=min(max(g/np.sqrt(tau),1),L)
    dec=np.max(np.abs(T[(1,-1)])/(B(L,g,tau,D)*np.exp(-0.25*D/ell)))          # KLDecay, c_d=1/4
    sh=max(np.max(np.abs(T[(s,s)])/((D==0)+g*g*np.exp(-0.5*D))) for s in (1,-1))  # KLShort, c=1/2
    T0=T[(1,-1)]-T[(1,-1)].mean(); zer=np.max(np.abs(T0)*(g*g+tau)*(D+1)**(d-2))  # KLZero (no L^tau)
    k2=max(np.max(np.abs(T[(a,b)]))/B0 for a in (1,-1) for b in (1,-1))        # bcal n=2
    # n=3: K = m1m2m3 sum_b Th12(a1-b)Th23(a2-b)Th31(a3-b); a1=0, a2,a3 on a grid of 27 points near 0 and far
    pts=[(i,j,0) for i in (0,1,L//2) for j in (0,2,L//3)]
    k3=0; wi=0; wq=0
    for s in [(1,-1,1),(1,-1,-1),(1,1,-1),(1,1,1)]:
        A,Bm,C=T[(s[0],s[1])],T[(s[1],s[2])],T[(s[2],s[0])]
        for p in pts:
            for q in pts:
                f2=np.roll(Bm,p,(0,1,2)); f3=np.roll(C,q,(0,1,2))
                k3=max(k3,abs(np.sum(np.conj(np.ones(1))*A[(-np.indices(A.shape)[0])%L,(-np.indices(A.shape)[1])%L,(-np.indices(A.shape)[2])%L]*f2*f3))/B0**2)
        if s[0]==-s[2]:  # Ward n=3 at a1=0,a2=p: sum_x K(0,p,x) = (2i eta)^-1 (K2(+,s2;0,p)-K2(-,s2;0,p)), W=1
            p=(1,2,0); Ar=A[(-np.indices(A.shape)[0])%L,(-np.indices(A.shape)[1])%L,(-np.indices(A.shape)[2])%L]
            lhs=np.prod([m[x] for x in s])*np.sum(Ar*np.roll(Bm,p,(0,1,2))*C.sum())
            rhs=(m[1]*m[s[1]]*T[(1,s[1])][p]-m[-1]*m[s[1]]*T[(-1,s[1])][p])/(2j*eta)
            wi=max(wi,abs(lhs-rhs)/abs(rhs))
            # wardineq n=3: sum_x |sum_b A(0-b)B(p-b)C(x-b)| <= sum_b |A||B| * sum|C| ; exact via FFT conv
            prodAB=Ar*np.roll(Bm,p,(0,1,2)); conv=np.fft.ifftn(np.fft.fftn(prodAB)*np.fft.fftn(C))
            wq=np.abs(conv).sum()*eta/B0
    print('L=%d g=%g 1-t=%.0e E=%.1f B0=%.3g | KLDecay %.3f KLShort %.3f KLZero %.3f | bcal n=2 %.3f n=3 %.3f | WI n=3 rel.err %.1e | wardineq n=3 %.3f'%(L,g,tau,E,B0,dec,sh,zer,k2,k3,wi,wq))
```
Script content (`aud2.py`, above): `Θ_ξ(0,·)=ifftn(1/(1−ξŝ))`, `ŝ=(1+2g²Σcos k_i)/(1+6g²)` (= `sbKernel`, Block.lean:39); `KLDecay` with `c_d=1/4`, `KLShort` with `c=1/2`, `KLZero` without `L^τ`; `n=3` from `(Kn3sol)` at 81 label pairs × 4 charge patterns; WI `n=3` at `σ=(+,−,∓)`, `a=(0,(1,2,0),x)`; wardineq `n=3` by FFT convolution. All ratios ≤ 1.7 (constants), WI exact to 1e-7: every pin shape holds at `t→1` (1−t=1e-9), `g→0` (0.02), `g=1`, `E=1.5`, `L=31`; no pin is vacuous or false at these extremes.

## 4. Compiled nonempty instances (d=3, L=5, W=2, g=1/2, E=0, t=9/10; `KLinstPar : KLPar 1 1`)
```
$ grep -c 'theorem KLinst_' RBM3D/Probe/T2004Pins.lean; grep -o 'names after the prefix.*' build.txt | cut -c1-200
21
names after the prefix: Kpi, KpiBound, bound_four, bound_one, bound_three, bound_two, indStep, molecule, ode, pure, retire_bound, retire_kTwoFormula, retire_two, scales, sumZero, three, two, unique, ward, wardIneq, ward_two
```
| target | instance | hypotheses left (allowed: other gates' / KL pins) | deterministic hyps discharged |
|---|---|---|---|
| `KLK_two`, `KLK_three`, `KLK_eq_sum_Kpi` | `KLinst_two` (σ=(+,−), a=(0,1)), `KLinst_three` (σ=(+,−,+), a=(0,1,2)), `KLinst_Kpi` (n=4) | none | `3≤4` |
| `KLward_two` | `KLinst_ward_two` | none | `3≤5`, `1≤2`, `|0|<2`, `t∈[0,1)` |
| `KLBoundAt_one/two/three` | `KLinst_bound_one/two/three` | `KLPT 3 1 1` (PT gate) | `KLinstPar` fields, `0<κ` |
| `KLisKLoopPin`, `KLuniquePin`, `KLwardPin` | `KLinst_ode`, `KLinst_unique`, `KLinst_ward` (n=3) | the pin | `3≤5`, `1≤2`, `|0|<2`, `WF`, length |
| `KLboundPin`, `KLwardIneqPin`, `KLKpiBoundPin`, `KLpurePin`, `KLmoleculePin`, `KLsumZeroPin`, `KLindStepPin` | `KLinst_bound_four`, `_wardIneq`, `_KpiBound`, `_pure`, `_molecule`, `_sumZero` (`Even 4` by `⟨2,_⟩`), `_indStep` (`σ 0 ≠ σ 1` by `simp`) | pin + `KLPT 3 1 1` | `3≤3`, `n`-range, `0<1`, `KLinstPar` |
| `KLretire_twoLoopBounded`, `KLretire_kTwoFormula`, `KLretire_KLoopBound` | `KLinst_retire_two`, `_retire_kTwoFormula`, `_retire_bound` | `KLisKLoopPin` / `∀n, KLBoundAt 3 n 1 1` | `3≤5`, `‖mSigma 0 s‖=1` |
| `KLinst_scales` | `η_t = 1/10`, `B_{t,0} = 514/175` | none | — |
Data nondegenerate: 125 blocks, `N=1000`, distinct labels, `t∈(0,1)`, `g∈(0,gmax)`, bulk `E`.

## 5. Paper-delta coverage
Candidates in the prove report (d): T2004a (n=3 needs (prop:ThfadC_short)), T2004b (`g ≤ gmax`), T2004c (BD1/BD2 range `c<1`), T2004d (`t∈[0,1)`), T2004e (loss `L^τ`, stronger than `≺`). Every statement difference found in §2 is covered, except the route-level ones listed as observations O2, O3 (no statement of a paper target changes).

## 6. Observations (no RETURN)
- O1. No compiled instance for `KLBoundAt_prec`, `KLKpi_eq_sum_SigmaPi`, `KLretire_kThree` (supporting lemmas, not pins): the second has no hypotheses; the first's only non-trivial hypothesis is discharged unconditionally by `KLBoundAt_one`. Suggest adding one-line instances when KL1/KL11 port them.
- O2. `KLindStepAt` takes the leaves `Θ^{(σ_i,σ_{i+1})}` only, not the paper's `Θ̃ ∈ {Θ, tS^{(B)}Θ^{(+,-)}}`; this is RBM2D's `innerId` route (`KBoundCut.lean:1954` `Kpi_cut` at c9a24cf: glued edge `ξ_J·S_{uw}` times a standard outer leaf). KL10/KL11 should confirm that the cut route closes with this form; the dispatcher may record a route note.
- O3. The probe measures `|a|` by `zdistD` (l1); T2002b chose `zdistInf` for statements. Equivalent up to `d`-dependent constants (all constants here may depend on `d`); KL1 should follow T2002's convention.
- O4. `KLisKLoopPin`, `KLuniquePin`, `KLwardPin` quantify over every `d` and every `g : ℝ` (stronger than needed; algebraic statements, `SB` is stochastic for every `g`). If KL3/KL6 meet a `d`- or `g`-restriction, a primed pin is needed.
- O5. Split table: KL14 (cleanup, 150 lines) is below the 600–1500 band; KL4+KL5 and KL8+KL9 are merged to fit it. KL10 (`KLindStepPin`) is the stated high risk.
- O6. `KLPT` is local; its agreement with T2003's PT pins (range `c<1`, loss `L^τ` vs `N^τ`, `g ≤ gmax`) is a dispatcher cross-check (report (d) T2004c); not a defect of this ticket.

## 7. Verdict
| target | verdict |
|---|---|
| Item 1 inventory, item 2 definition choice (option B, retirements compiled) | PASS |
| Item 3 pins (`KLK`, `KLisKLoopPin`, `KLuniquePin`, `KLwardPin`, `KLboundPin`, `KLwardIneqPin`, `KLKpiBoundPin`, route pins) | PASS |
| Item 4 routes, item 6 block Anderson, item 7 split | PASS |
| Item 5 skeleton `n=2,3` (`KLBoundAt_two/three` from `KLDecay`, `KLShort`) | PASS |
| Item 8 instances | PASS |
**Overall: PASS.** No dispatcher sign-off required.
