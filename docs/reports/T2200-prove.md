Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 18:10:38 UTC 2026

### (i) Exponent table
Notation: N = sz.size n, Δ = gridStep ≤ 1/K ≤ N^{-CK} (eventually, K n ≥ N^{CK}), KΔ = t−s ≤ 1, δ = N^{-D}/2, ρ = N^{ε'}/4,
x_Y = ¼N^{ε'}δ^{1/2}, μ_i = cycProd. For w ≤ t: 1/(1−w) ≤ 16N (`difRep_flow_bounds`: η_w ≥ N^{-1+ε}/16 ≥ 1/(16N), η_w ≤ 1−w).
Chosen: **C' = 4m+D+6, CK = 5m+2D+16** (functions of m, D only). Constants below are worst case (32N per slot for every Q), so Q = ∅, {0} give the same numbers.

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 (stop row, f1) | kernel `uKer μ v_p u_k − 1 = (u_k−v_p)μ S Θ_{u_kμ}` (`uKer_eq_one_add`, no order hypothesis; Evolution.lean:90) | slot row sum ≤ (v_p−u_k)/(1−u_k) ≤ N^{-C'}·16N =: ε₀ ≤ 16N^{1−C'} (≤1: log10 = −87 at n=0) | — |
| 1 | tensor bound | Σ_b|Π_i(δ+Ξ_i)(a_i,b_i) − Πδ| ≤ Σ_{S≠∅}Π_{i∈S}ε₀ = (1+ε₀)^m−1 ≤ m2^{m−1}ε₀ (slots use distinct index variables, row sums multiply; entrywise, not only operator norms) | exact |
| 1 | err1 = m2^{m−1}ε₀‖W‖, ‖W‖ ≤ ρ(V_Q+δ)^{1/2} | err1 ≤ ¼N^{ε'}δ^{1/2} ⟺ A²(V_Q+δ) ≤ δ, A = m2^{m+3}N^{1−C'}; N^{ε'} cancels; needs 2C' ≥ 4m+D+5+log_N(const), i.e. C' ≥ 2m+D/2+2.5 | C'−(2m+D/2+2.5) = 2m+D/2+3.5 (err1 margin −452 at n*=18, m=2,D=1) |
| 2 (f2) | per-slot row sum of uKerQ(u_j,v_p)−uKerQ(u_j,u_k) | ≤ ‖projMat‖·‖1−u_jμS‖·‖Θ_{v_pμ}−Θ_{u_kμ}‖ ≤ 2·2·(16N)²(v_p−u_k) (`Theta_sub_Theta`, ‖SB‖=1) | — |
| 2 | c₃ (telescoping over the 2m slots, other slots ≤ 32N, × M_ee) | \|ΔSTeeUQM\| ≤ c₃N^{4m+4}(v_p−u_k), c₃ = 2m·1024·32^{2m−1}·m·16^{2m+2} (m=2: 4.5e15; m=3: 2.7e21) | |
| 2 | Σ_{j<k}Δ\|Δa_j\| ≤ c₃N^{4m+4−C'} ≤ N^{-D}/4 | ⟺ c₃ ≤ N^{C'−4m−4−D}/4 = N²/4 (ticket's C' ≥ 4m+D+5 would give N¹) | N², holds for N ≥ 2√c₃ |
| 3 | S_Q = Σ_b\|κ_b\| ≤ (2·16N)^m = (32N)^m (`norm_projMat_le`≤2, `norm_uKer_le` (1−v)/(1−w) ≤ 16N, 0≤v≤w≤t) | | |
| 3 | M_ee = mN(16N)^{2m+2} (`difRep2_norm_STeeM_le_N`); V_Q = S_Q²M_ee = m32^{2m}16^{2m+2}N^{4m+3} | Σ_{j<K}a_j ≤ KΔV_Q ≤ V_Q | |
| 3 | ‖Q∘T_w‖_{∞→∞} ≤ Π_i(2‖Θ_{wμ_i}‖) ≤ (32N)^m (via `zeroModeSet_tensorKer`+`norm_tensorKer_le`+`norm_Theta_le`; `norm_zeroModeSet_le` alone gives only 2^{\|Q\|}‖T_w‖); row sums of P_j ≤ (1+u_j‖SB‖)^m ≤ 2^m | | |
| 4 shift | Σe_j ≤ c_sh N^{4m+4}Δ, c_sh = 32^{2m}m(2m+2)16^{2m+3} (`difRep2_eeShift_sum_le`×S_Q²) ≤ δ ⟺ c_sh ≤ N^{CK−4m−4−D}/2 | needs CK ≥ 4m+D+5; chosen CK−(4m+D+4) = m+D+12 | c_sh(2)=3.4e15, c_sh(3)=1.8e21 |
| 5 Y (route e) | P_Y = 2000(2^m m(m+1)16^{m+2})²N^{2m+14} (`AzumaProxyN_YfieldsW`, Smax=2^m, C₂ ≤ m(m+1)N(16N)^{m+2}); Doob per b: 4KΔ²P_Y/x'², x' = x_Y/(32N)^m, 1/x_Y² = 32N^{D−2ε'} | Y_bad ≤ N^m·4N^{-CK}P_Y(32N)^{2m}·32N^D = c_Y N^{5m+14+D−CK} ≤ N^{-D}/4 ⟺ 4c_Y ≤ N^{CK−5m−2D−14} = N² (N^{-2ε'} dropped: ε'-free); c_Y = 128·2000·(2^m m(m+1)16^{m+2})²32^{2m} (m=2: 6.6e23; m=3: 2.8e30) | needs CK ≥ 5m+2D+14+log_N(4c_Y) (ticket: 15); chosen gives N² |
| 5 variant (not chosen) | Doob per (p,a') with κ^{p,a'} (Smax=(32N)^m, P'~N^{4m+14}), events (P_n+1)N^m ≈ N^{C'+m}: exponent 9m+2D+20−CK ≤ −D−(slack) | CK ≥ 9m+3D+21 (arithmetic only, not checked further) | |
| 6 Z | (P_n+1)N^m(Lmax+1)·4e^{−N^{2ε'}/(256m)} ≤ N^{-D}/2; P_n=⌈N^{C'}⌉, Lmax=⌈log₂(V_Q/δ)⌉ (peel: ρ²/(16c)=N^{2ε'}/(256m), c=m) | polynomial vs stretched exponential; threshold N₀(m,D,ε') (only place ε' enters) | first n in output (ii) |
| 7 (g) | |X_k| ≤ \|W^{p,Z}_k(a)\| + err1 + \|X^Y_k\| ≤ (¼+¼+¼)N^{ε'}(Σ_{j<k}a_j+δ)^{1/2}, Σ_{j<k}a_j+δ ≤ A_k+N^{-D}/4+δ ≤ A_k+N^{-D} | ¾ < 1 and (A_k+N^{-D})^{1/2} > 0 gives the contradiction with the pin's event | ¼ |
| 8 | conj(uKerQ σ(v,w)(x,y)) = uKerQ(!σ)(v,w)(x,y), 0≤w<1 (conj mSigma = mSigma ∘ !, conj SB = SB, conj Θ_ξ = Θ_{conj ξ}, projMat real) | Σκ_bκ̄_{b'}STeeM_{u_j,σ,b,b'} = STeeUQM_{u_j,v_p}(a') exactly | exact |
| 8 | v_j = max(0,Δ m Re Σκκ̄ STeeM_{u_{j+1}}) ≤ m(a_j+e_j) | a_j = 1[u_j≤v_p]Δ‖STeeUQM_{u_j,v_p}‖, e_j = ΔS_Q²eeShiftErrN (`norm_STeeM_shiftN_le`: \|STeeM_{u'}−STeeM_u\| ≤ eeShiftErrN) | exact |
| 8 | `difRepTail_condMGF_Z` takes κ after (n j) (j-dependent κ allowed); k=m≥2; proxy bound with `max(0,·)` is legal (exp monotone) | | |
| 9 | order: m → Q → (κ,ε,𝔡,𝔠,sz,z,s,t) → D → CK(m,D) → K → ε' → ∀ᶠ n; coarse grid P_n=⌈N^{C'}⌉ independent of K; v_p = s+p(t−s)/P_n, p(k)=⌈kP_n/K⌉ | CK, C' free of ε', Q, κ, ε; N₀ depends on (m,D,ε') and on K only through K n ≥ N^{CK} | |
| T4 | hypotheses: 3≤L (`sz.three_le_L`), \|E\|≤2, 0≤v,w<1, u_j arbitrary; proof: additivity of UN, `zeroModeSet_UN` at w (‖wμ‖<1), `GridDuhamelN_Ugen_comp` (no condition on u) | holds for any order of v,w (script: (v,w)=(0.3,0.6),(0.6,0.3)) | |
| d | 3 ≤ d used nowhere in targets 1–6 (L^{dm} ≤ N^m needs only W ≥ 1, `W_pos`); target 7 only via `stGridRepN_of_tails` | | |

External hypotheses: none new. Flow data `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (Induction/Defs.lean:435), sz0: L=4(n+1), W=(2(n+1))^5, N_n=(W_nL_n)^3→∞ (Defs/Sizes.lean:260; limit computed in the log10 N column below).

### (ii) Concrete instance (d=3, sz0, z0, s≡0, t≡1/16, m∈{2,3}, D∈{1,3}, ε'∈{1/10,1/2}, Q∈{∅,{0}}, K n=⌈N^{CK}⌉+1)
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2200/budgets.py` (margins are log10(lhs/rhs); <0 holds; (4),(5),(6),err1,err2 as in rows 4,5,6,1,2):
```
n=0..7 table, m=2 D=1 eps'=1/10 (CK=28, C'=15); entries log10(lhs/rhs), <0 holds
n  log10N  log10P_n  (4)shift (5)Y  (6)Z  err1  err2  log10eps0max
0    6.32    94.82   -78.99    11.78    117.15  -83.69    3.61  -87.30
1   11.74   176.10  -160.27     0.94    214.75 -170.38   -7.22 -163.16
2   14.91   223.65  -207.82    -5.40    271.27 -221.10  -13.56 -207.53
3   17.16   257.38  -241.55    -9.89    310.33 -257.08  -18.06 -239.02
4   18.90   283.55  -267.72   -13.38    338.94 -284.99  -21.55 -263.44
5   20.33   304.93  -289.10   -16.23    359.88 -307.79  -24.40 -283.39
6   21.53   323.00  -307.17   -18.64    374.27 -327.07  -26.81 -300.26
7   22.58   338.66  -322.83   -20.73    382.48 -343.78  -28.90 -314.88
first n with all of (4),(5),(6),err1,err2,eps0<=1 (and all sampled n above it up to 10^9):
m=2 D=1 eps'=0.1 CK=28 C'=15: n*=18 log10N=29.3  margins(4,5,6,e1,e2)=-424.3 -34.3 -93.6 -452.0 -42.4  monotone_above=True
m=2 D=1 eps'=0.5 CK=28 C'=15: n*=2 log10N=14.9  margins(4,5,6,e1,e2)=-207.8 -5.4 -689170761656.5 -221.1 -13.6  monotone_above=True
m=2 D=3 eps'=0.1 CK=32 C'=17: n*=19 log10N=29.7  margins(4,5,6,e1,e2)=-489.8 -35.1 -94.2 -517.9 -43.2  monotone_above=True
m=2 D=3 eps'=0.5 CK=32 C'=17: n*=2 log10N=14.9  margins(4,5,6,e1,e2)=-237.6 -5.4 -689170761596.8 -250.9 -13.6  monotone_above=True
m=3 D=1 eps'=0.1 CK=33 C'=19: n*=21 log10N=30.5  margins(4,5,6,e1,e2)=-466.2 -29.9 -1.8 -585.7 -38.9  monotone_above=True
m=3 D=1 eps'=0.5 CK=33 C'=19: n*=3 log10N=17.2  margins(4,5,6,e1,e2)=-253.0 -3.3 -81495352785790.9 -319.2 -12.3  monotone_above=True
m=3 D=3 eps'=0.1 CK=37 C'=21: n*=23 log10N=31.2  margins(4,5,6,e1,e2)=-539.4 -31.3 -121.5 -661.6 -40.3  monotone_above=True
m=3 D=3 eps'=0.5 CK=37 C'=21: n*=3 log10N=17.2  margins(4,5,6,e1,e2)=-287.3 -3.3 -81495352785722.2 -353.5 -12.3  monotone_above=True
```
Reading: for ε'=1/10 all budgets close only from n*≈18–23 (N≈10^{29}–10^{31}) because of the Z budget; at ε'=1/2 from n*=2–3; n=0..7 (m=2,D=1,ε'=1/10) shows (5) failing at n=0,1, err2 failing at n=0, and (6) failing through n=7 (all pin statements are ∀ᶠ n, so this is the threshold N₀, not a defect). No margin depends on Q.
Boundary cases and grid, command `python3 .../grid.py` (exact `Fraction` arithmetic; s=t included, giving Δ=0, v_p=u_k=s, ε₀=0, err1=err2=0; v_p−u_k=N^{-C'} is the extreme in `eps0` column):
```
grid p(k)=ceil(kP/K): 60000 random (s,t,K,P,k) incl. s=t; violations of u_k<=v_p<=min(t,u_k+(t-s)/P): 0; cases v_p=u_k: 36400
c3(m)=2m*1024*32^(2m-1)*m*16^(2m+2): m=2 4.504e+15, m=3 2.656e+21
3/4<1: True
m=2 c_sh=32^2m*m(2m+2)16^(2m+3)=3.38e+15  c_Y=128*2000*(2^m m(m+1)16^(m+2))^2*32^2m=6.64e+23
m=3 c_sh=32^2m*m(2m+2)16^(2m+3)=1.77e+21  c_Y=128*2000*(2^m m(m+1)16^(m+2))^2*32^2m=2.79e+30
```
Extreme-input test (lesson 25), command `python3 .../extreme.py`: d=3, L=3, W=1 (27 sites), g=1/2, E=0.7, m=2, σ=(+,−), Q={0}, random complex tensors. STeeM is replaced by a random complex array T_{b,b'} (the identity (β) is algebraic in it; STeeM itself is not recomputed):
```
(alpha) max|conj(uKerQ sigma)-uKerQ !sigma| = 0.00e+00
target3 max|Q(UN A)-tensorKer(uKerQ) A| = 8.15e-15
(beta) max|sum kappa conj(kappa') T - STeeUQM| over 20 random a = 0.00e+00
target4 (v=0.3000,w=0.6000) max|LHS-RHS| = 1.45e-14
target4 (v=0.6000,w=0.3000) max|LHS-RHS| = 1.08e-14
target4 (v=0.0312,w=0.0625) max|LHS-RHS| = 5.33e-15
factorisation UN_{u_j,w}=T_w P_j: max err = 6.23e-15
row sums of P_j slot kernels (<=2): 1.170 ; of Q T_w slot kernels vs 2/(1-w)=5.000: 2.974
Y-form sum_j Q UN_{u_j,u_k}Y_j = Q T_{u_k} sum_j P_j Y_j: max err = 1.42e-14
(f1) v-u=1e-03: ||UN_{v,u}W-W||=4.303e-03 <= ((1+e0)^m-1)||W||=1.379e-02 : True ; slot rowsum(Xi)=2.000e-03 <= e0=2.000e-03 : True
(f1) v-u=1e-06: ||UN_{v,u}W-W||=4.304e-06 <= ((1+e0)^m-1)||W||=1.377e-05 : True ; slot rowsum(Xi)=2.000e-06 <= e0=2.000e-06 : True
(f1) v-u=0e+00: ||UN_{v,u}W-W||=3.179e-15 <= ((1+e0)^m-1)||W||=0.000e+00 : True ; slot rowsum(Xi)=7.952e-16 <= e0=0.000e+00 : True
(f2) v_p-u_k=1e-03: max_a|diff|=6.215e-03 <= bound 4.137e+00 : True
(f2) v_p-u_k=1e-06: max_a|diff|=6.202e-06 <= bound 4.096e-03 : True
```
### Verdicts
- Target 1 `STeeUQM_empty`: PASS (Q=∅: `if_neg`; product of `uKer` vs `uKerQ ∅` agree entrywise by definition).
- Target 2 `gridRepWTailN_of_Q`: PASS (`zeroModeSet_empty`, target 1).
- Target 3 `zeroModeSet_UN_eq_uKerQ`: PASS (`zeroModeSet_tensorKer` ∘ `UN_eq_tensorKer`; script residual 8e-15).
- Target 4 `difRep3_UN_transfer`: PASS (script residual ≤1.5e-14 for both orders of v,w).
- Target 5 `gridRepWTailQN_holds`: PASS: every row of (i) closes with C'=4m+D+6, CK=5m+2D+16 (both free of ε', Q); row 1 (stop row, f1) and row 2 (f2) hold as written (tensor bound is the entrywise (1+ε₀)^m−1); conjugation identity with `projMat` holds; no case condition used. Y route (e) used (factorisation 𝒰_{u_j,w}=T_wP_j confirmed numerically, err 6e-15).
- Target 6 `gridRepWTailN_holds`: PASS (targets 2, 5 at Q=∅). Target 7 `stGridRepN_holds`: PASS (assembly; `3 ≤ d` only from `stGridRepN_of_tails`).

## (b) Script output — Mon Oct  5 19:13:40 UTC 2026
### b.1 Build, registry pre-check, full build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2200`, branch `t/T2200`; the two runs below: 19:11:59-19:12:56 UTC)
```
$ git log --oneline -1; wc -l RBM3D/Path/DifREP3.lean; grep -cE '^private' RBM3D/Path/DifREP3.lean; grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Path/DifREP3.lean | wc -l
afb1467 T2200: ST2-13b Path/DifREP3 (Q^{(A)} o U-weighted martingale tail; STGridRepN unconditional for d >= 3)
2567 RBM3D/Path/DifREP3.lean
82
0
$ lake build RBM3D.Path.DifREP3 2>&1 | grep -n "DifREP3\|Build completed\|error"
748:✔ [3855/3855] Built RBM3D.Path.DifREP3 (18s)
749:Build completed successfully (3855 jobs).
$ registry pre-check after deleting the two owed lines (tmp file: import RBM3D / import RBM3D.Path.DifREP3 / #assert_rbm_axioms; `lake env lean`)
registry pre-check (import RBM3D + import RBM3D.Path.DifREP3 + #assert_rbm_axioms) exit=0
1:axiom audit: 5895 theorems, 2084 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c 'GridRepWTailQNAt\|GridRepWTailNAt\|STGridRepN' <pre-check output>   -> 0   (none is reported unproved; `GridRepWTailQNAt` is proved by target 5)
$ full `lake build` with `import RBM3D.Path.DifREP3` added after the last import of RBM3D.lean (hub step A.4); the line was reverted afterwards
full lake build (root import simulated) exit=0
Build completed successfully (4003 jobs).
2405:info: RBM3D.lean:245:0: axiom audit: 5895 theorems, 2084 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
RBM3D.lean restored: git status --short => []
$ git diff --stat main...t/T2200
 RBM3D/Path/DifREP3.lean | 2567 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    2 -        (exactly the two owed lines `RBM.Gauss.Sizes.STGridRepN`, `RBM.Ind.GridRepWTailNAt`)
```
### b.2 `#print axioms` of the new public declarations (all 12 are exactly `[propext, Classical.choice, Quot.sound]`); the `private` helpers (mangled names) are checked by a script over the environment
```
uKerQ: [propext, Classical.choice, Quot.sound]
STeeUQM: [propext, Classical.choice, Quot.sound]
GridRepWTailQNAt: [propext, Classical.choice, Quot.sound]
STeeUQM_empty: [propext, Classical.choice, Quot.sound]
gridRepWTailN_of_Q: [propext, Classical.choice, Quot.sound]
zeroModeSet_UN_eq_uKerQ: [propext, Classical.choice, Quot.sound]
difRep3_UN_transfer: [propext, Classical.choice, Quot.sound]
gridRepWTailQN_holds: [propext, Classical.choice, Quot.sound]
gridRepWTailN_holds: [propext, Classical.choice, Quot.sound]
stGridRepN_holds: [propext, Classical.choice, Quot.sound]
DifREP3Inst.inst_gridRepWTailQN: [propext, Classical.choice, Quot.sound]
DifREP3Inst.inst_gridRepWTailN: [propext, Classical.choice, Quot.sound]
$ lake env lean privaudit.lean   (`collectAxioms` on every `_private.RBM3D.Path.DifREP3` theorem and def)
private declarations of DifREP3 (theorems+defs, incl. compiler auxiliary): 158, theorems: 144, with a non-standard axiom (incl. sorryAx): 0
```
### b.3 Statements: script diff against `docs/tickets/checks/T2200-check.lean` (section 2), and the extraction by script
```
$ python3 scratchpad/T2200/stmtdiff.py
vocabulary (3 defs incl. docstrings) identical: True
STeeUQM_empty: type == body of STeeUQMEmptyStmt: True
gridRepWTailN_of_Q: type == body of GridRepWTailNOfQStmt: True
zeroModeSet_UN_eq_uKerQ: type == body of ZeroModeSetUNEqUKerQStmt: True
difRep3_UN_transfer: type == body of DifRep3UNTransferStmt: True
gridRepWTailQN_holds: type == body of GridRepWTailQNHoldsStmt: True
gridRepWTailN_holds: type == body of GridRepWTailNHoldsStmt: True
stGridRepN_holds: type == body of StGridRepNHoldsStmt: True
ALL targets identical: True
$ lake env lean checkex.lean   (check-file section 2 + `example : T2200Check.<X>Stmt := @<target>` for the seven targets)   -> exit 0, no output
# whitespace-collapsed text of the three vocabulary heads and the seven target types, extracted from RBM3D/Path/DifREP3.lean (the body of `GridRepWTailQNAt` is covered by the first line of the diff)
noncomputable def uKerQ (d L : ℕ) [NeZero L] (g E : ℝ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (v w : ℝ) (i : Fin m) : Matrix (Zd d L) (Zd d L) ℂ :=
noncomputable def STeeUQM {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (a :
    Fin m → Zd d (sz.L n)) : ℂ :=
def GridRepWTailQNAt (d m : ℕ) (Q : Finset (Fin m)) : Prop :=

theorem STeeUQM_empty : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L
    n)), STeeUQM sz n E v w H (∅ : Finset (Fin m)) σ a = sz.STeeUM n E v w H σ a :=
theorem gridRepWTailN_of_Q : ∀ d m : ℕ, GridRepWTailQNAt d m (∅ : Finset (Fin m)) → GridRepWTailNAt d m :=
theorem zeroModeSet_UN_eq_uKerQ : ∀ {d L : ℕ} [NeZero L] (g E : ℝ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (v w : ℝ) (A : (Fin m → Zd d L) → ℂ), zeroModeSet d L Q (UN d L g (fun i =>
    mSigma E (σ i)) v w A) = tensorKer d L (uKerQ d L g E Q σ v w) A :=
theorem difRep3_UN_transfer : ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {m : ℕ} (σ : Fin m → Bool) (Q : Finset (Fin m)) {v w : ℝ}, 0 ≤ v → v < 1 → 0 ≤ w → w < 1 → ∀ (k :
    ℕ) (u : ℕ → ℝ) (A : ℕ → (Fin m → Zd d L) → ℂ), ∑ j ∈ Finset.range k, zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) (u j) w (A j)) = UN d L g (fun i => mSigma E (σ i)) v w (∑ j ∈
    Finset.range k, zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) (u j) v (A j))) :=
theorem gridRepWTailQN_holds : ∀ d m : ℕ, 2 ≤ m → ∀ Q : Finset (Fin m), GridRepWTailQNAt d m Q :=
theorem gridRepWTailN_holds : ∀ d m : ℕ, 2 ≤ m → GridRepWTailNAt d m :=
theorem stGridRepN_holds : ∀ d : ℕ, 3 ≤ d → STGridRepN d :=
```
### b.4 The compiled nonempty instances (lines 2386-2565 of the file, namespace `RBM.Ind.DifREP3Inst`; `d = 3`, `sz0`, `z0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`; the `∃ CK …` statements of `inst_*` are abbreviated by the extraction script; three further `example`s repeat targets 1, 3, 4 at `H = 1`, `A b = (b_0)_0`, `A_j b = j + (b_0)_0`)
```
example : STeeUQM sz0 0 (1 / 2) 0 (1 / 16) (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (∅ : Finset (Fin 3)) σ3 a0 = sz0.STeeUM 0 (1 / 2) 0 (1 / 16) (0 : Matrix
    (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ3 a0 := STeeUQM_empty sz0 0 (1 / 2) 0 (1 / 16) 0 σ3 a0
example : zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3)) (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) 0 (1 / 16) (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ))) = tensorKer 3
    (sz0.L 0) (uKerQ 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ({0} : Finset (Fin 3)) σ3 0 (1 / 16)) (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ)) := zeroModeSet_UN_eq_uKerQ (sz0.lam 0) (1 / 2) ({0} :
    Finset (Fin 3)) σ3 0 (1 / 16) _
example : ∑ j ∈ Finset.range 4, zeroModeSet 3 (sz0.L 0) ({0} : Finset (Fin 3)) (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) (gridTime sInst tInst (fun _ => 4) 0 j) (1 / 16)
    (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ))) = UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) (1 / 32) (1 / 16) (∑ j ∈ Finset.range 4, zeroModeSet 3 (sz0.L 0) ({0} : Finset
    (Fin 3)) (UN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma (1 / 2) (σ3 i)) (gridTime sInst tInst (fun _ => 4) 0 j) (1 / 32) (fun _ : Fin 3 → Zd 3 (sz0.L 0) => (1 : ℂ)))) :=
    difRep3_UN_transfer (d := 3) (sz0.lam 0) (sz0.three_le_L 0) (E := 1 / 2) (by norm_num) σ3 ({0} : Finset (Fin 3)) (v := 1 / 32) (w := 1 / 16) (by norm_num) (by norm_num) (by norm_num) (by
    norm_num) 4 (fun j => gridTime sInst tInst (fun _ => 4) 0 j) (fun _ _ => (1 : ℂ))
theorem inst_gridRepWTailQN (m : ℕ) (hm : 2 ≤ m) (Q : Finset (Fin m)) : ∃ CK, 0 ≤ CK ∧ ∃ K, (∀ n, K n ≠ 0) ∧ (∀ᶠ n, N_n^CK ≤ K n) ∧ (∀ᶠ n, ∀ i, pathP sz0 {…pin event…} ≤ ofReal (N_n^(-1)))
    [full statement: file]  obtain ⟨CK, hCK, h⟩ := gridRepWTailQN_holds 3 m hm Q (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0
    hst htT 1 one_pos
example := inst_gridRepWTailQN 2 le_rfl ({0} : Finset (Fin 2))
example := inst_gridRepWTailQN 3 (by norm_num) (∅ : Finset (Fin 3))
example : GridRepWTailNAt 3 2 := gridRepWTailN_of_Q 3 2 (gridRepWTailQN_holds 3 2 le_rfl ∅)
theorem inst_gridRepWTailN (m : ℕ) (hm : 2 ≤ m) : ∃ CK, 0 ≤ CK ∧ ∃ K, (∀ n, K n ≠ 0) ∧ (∀ᶠ n, N_n^CK ≤ K n) ∧ (∀ᶠ n, ∀ i, pathP sz0 {…pin event…} ≤ ofReal (N_n^(-1)))  [full statement: file]
    obtain ⟨CK, hCK, h⟩ := gridRepWTailN_holds 3 m hm (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT 1 one_pos
example := inst_gridRepWTailN 2 le_rfl
example := inst_gridRepWTailN 3 (by norm_num)
example : STGridRepN 3 := stGridRepN_holds 3 (by norm_num)
example : STGridMart 3 := ST_gridMart_of_repN (stGridRepN_holds 3 (by norm_num))
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) : STStep2 3 := ST_step2_of_pinsN' hNew hLWT hEMe (stGridRepN_holds 3 (by
    norm_num)) hOpt hClos
```
### b.5 Name-clash grep (`grep -rn -F NAME RBM3D RBM3D.lean` outside `RBM3D/Path/DifREP3.lean`; and `git grep` on main 9a207a1)
```
uKerQ STeeUQM GridRepWTailQNAt STeeUQM_empty gridRepWTailN_of_Q zeroModeSet_UN_eq_uKerQ difRep3_UN_transfer gridRepWTailQN_holds gridRepWTailN_holds stGridRepN_holds DifREP3Inst difRep3_ inst_gridRepWTailQN inst_gridRepWTailN
-> 0 hits in the worktree and 0 hits on main (9a207a1), for each of the 14 patterns
```
### b.6 Ports and sister projects
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  -> 9e0f275  (RBM2D HEAD; the provenance line RBM2D/Induction/StoppedEndDefs.lean:690 `qvFormN_eq_re_UgenPair` was read at c9a24cf)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/StoppedEndDefs.lean  ->  1 file changed, 90 insertions(+), 508 deletions(-)
$ git -C ../RBM2D --no-optional-locks grep -n -i 'coarse time\|coarse grid\|coarse level' c9a24cf -- '*.lean' | wc -l  -> 0;  the same in ../RBM1D at de0de42 -> 0
copies (private, prefix `difRep3_`; RBM3D file:line, merge commit): NQGood1.lean:151-196 (691566a), GridDuhamelN.lean:75-79, 91-104, 242 (2ebee73), DifREP2.lean:658-748, 923-954, 1265, 1308, 2098 (76b840e); weighted forms of DifREP2.lean:1777-1908 (76b840e)
```
### b.7 Numerics at the instance data (`sz0`: N_n = ((2(n+1))^5 · 4(n+1))^3), a Python transcription of `difRep3_cShift/c3/VQ/PY/Cbig` and of the budget (B5) `24 (2 c_V + 2) N^{9m+9} (N^D)³ exp(-(N^{ε'}/4)²/(16 m)) ≤ 1`; the last column is at the larger of the two `n`
```
$ python3 scratchpad/T2200/thresh2.py
# columns: m, D, eps', log10 Cbig(m), first n with N_n >= Cbig(m), first n with (B5) (and for all n up to 400), log10 N_n there
2 1 0.1 23.7 9 21 30.5
2 1 0.5 23.7 9 0 24.3
2 3 0.1 23.7 9 22 30.8
2 3 0.5 23.7 9 0 24.3
3 1 0.1 29.7 19 25 31.8
3 1 0.5 29.7 19 0 29.7
3 3 0.1 29.7 19 26 32.1
3 3 0.5 29.7 19 0 29.7
```
### Narrative
1. Layout of `RBM3D/Path/DifREP3.lean` (2567 lines; every helper outside the instance namespace is `private` with the prefix `difRep3_`): §1 vocabulary; §2 targets 1-4; §3 kernel algebra (conjugation `difRep3_conj_uKerQ`, the proxy as a quadratic form `difRep3_STeeUQM_eq` (β), row sums, `difRep3_sum_prod_sub_prod`, (f1) `difRep3_norm_UN_sub_le`, (f2) `difRep3_norm_STeeUQM_sub_le`); §4 coarse grid `difRep3_vc`, `difRep3_coarse`; §5 weighted Doob tail `difRep3_Y_tail`; §6 `Z` increments, `difRep3_Z_tail` (through `difRep2_peel`); §7 `difRep3_pathwise` (step (g)) and `difRep3_core`; §8 budgets; §9 `difRep3_tail_at`; §10 targets 5-7; §11 instances.
2. **Route variant of step (e), as the ticket allows:** Doob per `(p, a')` on `Σ_j κ^{p,a'}_j Y_j` with the weights of (d), and the transfer (f1) applied to `W^p = W^{p,Z} + W^{p,Y}`; no factorisation `T_w P_j`. Exponents proved: `CK = 9m + 3D + 22` (`Δ N^{9m+22} (N^D)^3 ≤ 1`) and `C' = 4m + D + 6` (`P = ⌈N^{4m+6} N^D⌉`), functions of `m, D` only. Section (a) rows 1-4, 6-9 stand; its row 5 budget for route (e) (`CK = 5m+2D+16`) is not used; its variant bound `CK ≥ 9m+3D+21` is met by `9m+3D+22` (the extra unit leaves a margin: `difRep3_budget_Y` needs `1536 c_PY ≤ N²`); no (a′).
3. Targets 1-4: 1 is `simp` on the definitions; 2 is `zeroModeSet_empty` and target 1; 3 is `UN_eq_tensorKer` then `zeroModeSet_tensorKer` (`uKerQ` is its kernel family); 4 is finite additivity of `UN` (`map_sum` of `GridDuhamelN_UgenHom`), `GridDuhamelN_Ugen_comp` and `zeroModeSet_UN` at `w` (`‖w μ_i‖ < 1`).
4. Target 5 at one `n` (`difRep3_tail_at` → `difRep3_core`): `(P+1) N^m` events. `EZ p a'` is the peeling event for `ζ_j = Σ_b κ_{j,b} Z_{j,b}`, `a_j = 1[u_j ≤ v_p] Δ ‖STeeUQM_{u_j,v_p}‖`, `v_j = max(0, Δ m Re Σ κ κ̄ 𝓔⊗𝓔_{u_{j+1}})`, `e_j = Δ (32N)^{2m} eeShiftErrN`, with `v_j ≤ m (a_j + e_j)` from (β) and `norm_STeeM_shiftN_le`. `EY p a'` is the Doob event (`AzumaProxyN_YfieldsW` at `κ_j`, `S = (32N)^m`). Off all events, for `k ≤ K`, `p = ⌈kP/K⌉` (`u_k ≤ v_p ≤ u_k + 1/P`): `X_k = (𝒰_{v_p,u_k} W^p_k)_a` (target 4), `|X_k − W^p_k(a)| ≤ m ε₀ (1+ε₀)^{m-1} ‖W^p_k‖_∞ ≤ ρ √δ` ((f1), `ε₀ = 16 N / X`, `X = N^{4m+6} N^D`), `Σ_{j<k} a_j ≤ A_k + N^{-D}/4` ((f2)), hence `|X_k| ≤ ρ T' + 2 ρ √δ ≤ ¾ N^{ε'} T'` with `T' = (A_k + N^{-D})^{1/2}`, `ρ = N^{ε'}/4`, `δ = N^{-D}/2`: a contradiction with the pin's event. The union is in `ℝ` (`measureReal_biUnion_finset_le`) and then `ofReal_measureReal`, as T2180 3(e).
5. Budgets (pure real arithmetic, `ε'`-free): (B1) shift, (B2) = (f2), (B3) = (f1) (`ρ` cancels), (B4) `Y`; all hold once `N ≥ difRep3_Cbig m` (explicit) and `Δ N^{9m+22}(N^D)^3 ≤ 1`; (B5) `Z` is `difRep3_eventually_Z` (`ε'` enters only here). Total failure probability `≤ N^{-D}/2 + N^{-D}/4 ≤ N^{-D}`.
6. §29 checklist: (1) `0 ≤ s`, `s ≤ t ≤ lemT z`; every `u_j`, `v_p ∈ [s,t] ⊂ [0,1)` (`difRep3_vc_ge/le`); (2) no case-(ii) boundary, no `norm_zeroModeSet_UN_le`, only `norm_projMat_le`; (3) no `L^d ≤ W^K` (`L^d ≤ N` from `W ≥ 1`, `difRep3_card_label_le`); (4) target 5 is `∀ᶠ n` as pinned, targets 1, 3, 4 hold at every size; (5) `∃ k ≤ K n` is inside the events; (6) `N → ∞` is `hz.1.2.2.1 : sz.SizeTendsto` (from `STFlow`), never a premise; (7) `CK` and `P` depend on `m, D, N` only, `P` not on `K`.
7. Consumer check (§45 O2): `zeroModeSet Q ∘ UN(u_j,u_k) = UN(u_j,u_k) ∘ zeroModeSet Q` is `zeroModeSet_UN`; the kernel index of clause (iv) is `u_j` (T2066/T2168), that of `zeroModeCalc_duhamel_inside_at` is `u_{j+1}`; the shift `𝒰_{u_{j+1},u_k} = 𝒰_{u_j,u_k} ∘ 𝒰_{u_{j+1},u_j}` is S5-15's step and is not done here.
8. `3 ≤ d` is used nowhere in targets 1-6; target 7 uses it only through `stGridRepN_of_tails` (`gridRepRemN_holds`, DECISIONS §36). The consumers `ST_gridMart_of_repN`, `ST_step2_of_pinsN`, `ST_step2_of_pinsN'`, `ST_step2_of_pinsLW'`, S5-15, S5-26 are under `3 ≤ d`; b.4 compiles `STGridRepN 3`, `STGridMart 3` and `STStep2 3` (the other pins as hypotheses). No new hypothesis anywhere; target 7 is the merged `stGridRepN_of_tails` applied to the merged `gridRepTailN_holds` and target 6.
9. Registry: only the two owed lines were deleted (pre-check exit 0); the stale `STOptL2` comment (`:127` on main) is untouched (LW-01's, §59 O4).
10. Hub: add `import RBM3D.Path.DifREP3` after the last `import` line of `RBM3D.lean` (b.1: the full build passes with it).

## (c) Verified Mathlib names (all used in `DifREP3.lean` and compiled; Mathlib at the project's `v4.34.0`)
- structure: `Fin.consEquiv`, `Fin.prod_univ_succ`, `Fin.cons_zero`, `Fin.cons_succ`, `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Fintype.card_fun`, `Finset.prod_univ_sum`, `Fintype.piFinset_univ`, `Finset.sum_mul_sum`, `Finset.prod_le_prod₀`, `Finset.stronglyMeasurable_fun_sum`, `Finset.measurable_sum`, `map_sum`, `map_prod`
- norms: `norm_prod`, `norm_sum_le`, `norm_smul_le`, `norm_mul_le`, `norm_sub_norm_le`, `norm_le_pi_norm`, `pi_norm_le_iff_of_nonneg`, `Complex.norm_conj`, `Complex.conj_natCast`, `Complex.norm_le_sqrt_two_mul_max`
- reals: `Real.sqrt_eq_rpow`, `Real.sq_sqrt`, `Real.le_sqrt`, `Real.sqrt_le_left`, `Real.one_le_rpow`, `Real.rpow_neg`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Nat.ceil_le`, `Nat.le_ceil`, `Nat.ceil_lt_add_one`, `Nat.ceil_pos`, `Nat.lt_two_pow_self`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_atTop`
- order: `div_le_div_of_nonneg_right`, `div_le_iff₀`, `le_div_iff₀`, `one_div_le_one_div_of_le`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `le_self_pow₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_mul_of_one_le_of_one_le`; measure: `measureReal_biUnion_finset_le`, `measureReal_union_le`, `measureReal_mono`, `ofReal_measureReal`, `measure_mono`, `measure_ne_top`
- changed or rejected here (tool log): `if_false` is deprecated (`ite_false`, `↓reduceIte` used); `Finset.prod_le_prod` takes one hypothesis here (the semiring form is `Finset.prod_le_prod₀`); `Π₁`, `Π₂` are rejected as identifiers (`Π` is a binder token); `Finset.notMem_empty` is the name that compiles.

## (d) Open issues and paper-delta candidates
Exponents proved: `CK = 9m + 3D + 22`, `C' = 4m + D + 6` (coarse grid `P = ⌈N^{4m+6} N^D⌉`); both free of `ε'`, `Q`, `κ`, `ε`, `𝔡`, `𝔠`, `K`. Route variant of step (e): Doob per `(p, a')` (Narrative 2).
Open: (1) Hub: the root import (Narrative 10). (2) S5-15 (`Q = ∅`) and S5-26 (`Q = {0}`) consume the public `Q`-form `gridRepWTailQN_holds`; the kernel-index shift `u_{j+1} → u_j` is theirs (Narrative 7). (3) The route-(e) factorisation `𝒰_{u,w} = T_w P_u` (`CK = 5m+2D+16`) was not implemented; it would only lower the value of `CK` (the pin is `∃ CK`). (4) ST-2's plan row ends with this ticket; the Step 2 closing composition and its registry deletions are LW-01's (§59 O4). (5) RBM2D HEAD is `9e0f275`, not `c9a24cf`; the cited provenance line was read at `c9a24cf` (b.6). (6) The pin is `∀ᶠ n`: b.7 gives the explicit thresholds at `sz0` (`N_n ≥ 10^{23.7}` for `m = 2`, `10^{29.7}` for `m = 3`, and `n ≥ 21` for (B5) at `m = 2`, `D = 1`, `ε' = 1/10`); the instances `inst_gridRepWTailQN/N` apply the theorems with `D = 1`, `ε' = 1/10` and the grid `K_n = ⌈N_n^{CK}⌉ + 1`.
Paper-delta candidates (tags `T2200a`…; the dispatcher numbers them):
- T2200a: `(alu9_STime)` of `lem:DIfREP` (`3_5:229`) holds uniformly in the endpoint `k ≤ K` on the grid, by a coarse time grid `v_p` of `P = ⌈N^{C'}⌉` points independent of `K` and the exact transfer `Σ_{j<k} 𝒰_{u_j,u_k} ξ_j = 𝒰_{v_p,u_k} Σ_{j<k} 𝒰_{u_j,v_p} ξ_j` (semigroup `𝒰_{v,w} 𝒰_{u,v} = 𝒰_{u,w}`), with `𝒰_{v_p,u_k} = id + O(N^{1-C'})` entrywise on tensors; the maximal random-proxy Azuma bound replaces BDG (D90/T2180a).
- T2200b: the zero-mode-removed form `Q^{(A)} ∘ 𝒰` for every `A ⊆ ⟦m⟧` (`(sahwNQ2)`, `3_5:1908`) with the proxy `((Q∘𝒰) ⊗ (Q∘𝒰̄)) ∘ (ℰ⊗ℰ)` and no case condition (`Q^{(A)} 𝒰 = tensorKer (uKerQ …)`; `I - L^{-d}J` is real, so `conj (uKerQ σ) = uKerQ σ̄`).
- T2200c: the second-order part by Doob per `(p, a')` with the weights of the first-chaos part; `CK = 9m + 3D + 22` and `C' = 4m + D + 6` depend on `m, D` only.
- T2200d: the proxy at `u_{j+1}` is moved to `u_j` at cost `(32N)^{2m} m(2m+2) 16^{2m+3} N^{2m+4} Δ`, and from `(u_j, v_p)` to `(u_j, u_k)` at cost `c₃ N^{4m+4} (v_p - u_k)` (absolute, deterministic), both absorbed in the `N^{-D}` floor.
- T2200e: the weighted tail holds for every `d`; `STGridRepN d` is unconditional for `d ≥ 3` (`C₀ = m + 9`).
