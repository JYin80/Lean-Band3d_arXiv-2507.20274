Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 09:57:06 UTC 2026

Notation: u = W^d, B = Bctl = W^{-d}Bparam(L,lam,t,0) (so B_0 = uB), eta = eta_t = (1-t) Im mF (`etaOf`), Ǧ = G_t - M, S_A = Σ_{x∈[a]}‖Ǧ^*e_x‖², S_C = Σ_{x∈[a]}‖Ce_x‖² with C = ǦE_bǦ^{(σ)}, Y = sup_c|X(c)|, N = sz.size. Sources: Fable `2026-10-12-s3-fold-A.md` §2.2, §4, §5 (re-derived below, not trusted); `Chain/Carrier.lean:47-125`; `Defs/Params.lean:36`; `Defs/Sizes.lean:211`.

### (i) Exponent table
| # | quantity | value / bound | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | root of target 3 | `|twLoop2X|² ≤ W^{-5d} β r₁r₂ S_A S_C`: W^{-6d} (target 2) times the free `w∈[c₁]` sum (card u) in F₂ (the `_w` binder of the pin); root `W^{-5d/2}` | Fable §5 prints `W^{-3d/2}` (wrong); `W^{-5d}` is what the table closes with | exact (script `expo.py` below) |
| 2 | β = max_{u,c}Σ_{v∈[c]}‖Ǧ_{uv}‖² | `≤ u·STWB ≤ uB = B_0` (`STLocalEntrygL`, `BAExp14a_STWB_le` needs `t<1`: `1-BAflowT0 = Im z/(Im m+Im z) > 0`) | pathwise on the good event of the pin; sup over (u,v) inside P (`StochDomAt`: the union over `u` is inside `P`) | exact, no loss |
| 3 | r₁, r₂ (weights) | `≤ Cρ` (7′), `≤ Cρ·Y` with Y ≺ uB (7); `Y` = sup over `c₁..c₄` is the pin's `U`-sup | `Σ_{c₂c₃c₄}|ρX| ≤ Y·Cρ`, both marginals | exact |
| 4 | S_A | `S_A ≤ 2η^{-1}Σ_{x∈[a]}Im G_xx + 2Σ‖M^*e_x‖² ≤ 2η^{-1}u|𝓛^{(1)}_{+,a}| + 2u ≺ uη^{-1}` (`BAExp14a_L1_eq`, `STLmaxgL` k=1: `B^0`, 5a, `η ≤ 1`) | `η ≤ 1`: `Im mF ≤ |mF| = |M_aa| ≤ 1` (5a at x=y), `0 ≤ 1-t ≤ 1`. Target 4 is applied to `G^*, M^*, φ=e_x` with `η → -η` (allowed: hypothesis is only `η ≠ 0`) | numeric: η = 0.4997 ≤ 1 (script inst) |
| 5 | S_C | `S_C ≤ 2η^{-1}u·Tr(E_aǦE_b ImG E_bǦ^*) (σ=false; σ=true: Tr(E_aǦ^*E_b ImG E_bǦ)) + 2𝓛̊^{(2)}_{(a,b)} ≺ η^{-1}uB² + B ≲ η^{-1}uB²` | last step needs `B_0 = uB ≥ c0` (row 7) and `η ≤ 1`; `𝓛̊^{(2)} = W^{-2d}Σ_{[a]×[b]}‖Ǧ_{xy}‖² ≤ B` (entry law, includes a=b) | uses all of row 7 |
| 6 | 3-loop, S3A-C1 | `Tr(E_aǦE_b ImG E_bǦ^*) = (2i)^{-1}[T(+,+,-) - T(+,-,-)]`, each `T0 - T1 - T1' + T2` (identities verified numerically below). `T0 ≺ B²` (`STLmaxgL` k=3, charges `(+,±,-)` / `(-,±,+)` for σ = false / true, blocks `(a,b,b)`); `|T1|,|T1'| ≤ W^{-d}|M^B_{ab}|(𝓛^{(2)}_{bb}𝓛^{(2)}_{ab})^{1/2} ≺ W^{-d}B = B²/B_0`; `|T2| = W^{-2d}|M^B_{ab}|²|𝓛^{(1)}_b| ≺ W^{-2d} = B²/B_0²` | `|M^B_{ab}| ≤ 1` (Ward); band formula `E_cME_{c'}=δ W^{-d}mE_c` used nowhere | one-M term loses `B_0^{-1}`, two-M `B_0^{-2}`: both ≤ 101^k·B² at 𝔡=1/10 |
| 7 | B_0 = uB lower bound (6a) | `uB ≥ (lam²+|1-t|)^{-1} ≥ (𝔡^{-2}+1)^{-1} = c0` (WO: `0<lam≤𝔡^{-1}`, eventually; `t∈[0,1]`; second summand of Bparam ≥ 0, also at t=1) | used in rows 5, 6 and in 7′ (Y=1 vs `uB`) | c0 = 1/101 at 𝔡=1/10; actual `uB = 2.03` (n=0), → 2 = (1-t)^{-1} |
| 8 | η lower bound (6b) | `κ(1-t) ≤ (1-t)Im mF = η`, `κ ≤ Im mF` (`BAflow_real`), `t ≤ 1` | gives `η^{-1} ≤ κ^{-1}(1-t)^{-1}`, the `(1-t)^{-1}` of the conclusion; `κ^{-1}` absorbed in `N^τ` | κ(1-t) = 1/4 ≤ η = 0.4997 |
| 9 | total, Y = uB (#17,#47) | `|twLoop2X|² ≺ u^{-5}·(uB)·(Cρ uB)²·(uη^{-1})·(η^{-1}uB²) = Cρ² η^{-2}B^5`; root `Cρ η^{-1}B^{5/2}` | target `(1-t)^{-1}B^{5/2}`: matches exactly, margin `(uB)^{-1}` consumed by Y | 0 (as Fable §4 says) |
| 10 | total, Y = 1 (7′) | `|twLoop2X|² ≺ Cρ² η^{-2}B^5 (uB)^{-2}`, root has extra `(uB)^{-1} ≤ 𝔡^{-2}+1` | row 7 | factor 101 at 𝔡=1/10 (actual 0.49) |
| 11 | `≺` bookkeeping | 7 pin events (entry, 𝓛^{(1)}, 𝓛^{(2)} ×2 charges, 𝓛^{(3)}, Y), product of ≤ 7 factors `N^{τ'}`, then root: `N^{7τ'/2} ≤ N^τ` for `τ' = τ/4`; D' = D+1; constants (2, 4, Cρ, κ^{-1}, 101^k) ≤ N^{τ'} eventually since `SizeTendsto` (Admissible) | every pin is a `∀τ D, ∀ᶠ l` statement; deterministic inequality holds on the intersection of good events | no loss in B-exponent |
| 12 | `r₁,r₂` at the 7′ instance (ρ₀ = t²1[c₃=c₁∧c₄=c₂](M^B_{c₁c₂})²) | `t²Σ_{c₂}|M^B_{c₁c₂}|² = t²` (Ward, symmetry) = 1/4 | `≤ Cρ` with Cρ = 1/4 | equality (script inst: 0.25000000000000033) |

Exponent bookkeeping (monomials in u, B, η, Y; `expo.py`, `python3 expo.py`):
```
|twLoop2X|^2 <~ {'u': Fraction(-2, 1), 'B': Fraction(3, 1), 'Y': Fraction(2, 1), 'e': Fraction(-2, 1)}
Y=W^d Bctl : |twLoop2X|^2 <~ {'B': Fraction(5, 1), 'e': Fraction(-2, 1)}   => root: eta^-1 Bctl^(5/2)
```
(first line = rows 1-5 multiplied; with `Y² → (uB)²` the `u` cancels; with `Y=1` the ratio to the target² is `(uB)^{-2}`, row 10.)

### (ii) One concrete nondegenerate instance
Data: `sz0` n=0 (`d=3, L=4, W=32, lam=1/64, N=2097152`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (κ=1/2, ε=1/10, 𝔠=1/6, 𝔡=1/10), `t ≡ 1/2` (`half_lt_t0`; `t0 ≥ 2/3`, `t0_sz0`). All numbers solve the Lean definitions (`PsiB` = ℓ¹-adjacency of Z_4^3, `zS = wI - mS`, `wI = 1.2i`, `BAt0`, `BAflowE`, `BAflowLam0 = √t0·lam`, `BAm` real-axis fixed point by Newton). Command `python3 inst.py` (scratch `T2445/inst.py`):
```
mS 0.8324879132742102j zS 0.3675120867257897j
t0 0.6937399277285086 E0 0.0 lam0 0.013014226813110832 kappa<=Im m: True
Newton residual 1.4444474582904269e-33
mF (-6.505213034913012e-19+0.9994926192469116j) |mF| 0.9994926192469116 Im mF 0.9994926192469116 mF vs m/sqrt(t0) 0.9994926192469118j
Ward row sums max|1-sum|: 1.3322676295501878e-15 symm: 1.0408340855860843e-17 diag-mF: 6.661350827510019e-16
eta_t 0.4997463096234558 kappa(1-t) 0.25 eta<=1 True
Bparam(K=0) 2.0302739141044412 Bctl 6.195904278883183e-05 W^d*Bctl=B0 2.0302739141044412 (dd^-2+1)^-1 0.009900990099009903 ok True
lam<=1/dd True W^(-d/2+dd)<=lam True t<T0 True
1-t 0.5 (1-t)^-1 Bctl^(5/2) 6.043544786717419e-11 eta^-1 Bctl^(5/2) 6.046612721633755e-11
margin (W^d Bctl)^-1 0.4925443769202455 <= dd^-2+1 100.99999999999999
r1=r2 (rho0=t^2 1[c3=c1,c4=c2] MB^2): 0.25000000000000033 0.25000000000000044
target-3 root exponent: W^{-5d}= 2.6469779601696886e-23  W^{-3d}= 2.842170943040401e-14
```
Deterministic targets 1-5 and the S3A-C1 identities at (d,L,W)=(3,4,2), N=512, G=(H-z)^{-1}, z=E0+iη, M=Mres(lam0 PsiI,E0,mF), random complex A,X,C,ρ (12 weights); command `python3 fold.py`:
```
BAMfine_eq (M = MB (x) I): 4.440892098500626e-16
target4 hyp  G-G^* = 2i eta G^*G : 7.993605777301127e-15
target4: 968.9069490694247 <= 6777.768245180419 True
5a max_x ||M^*e_x||^2 = 1.0000000000000013
5b ||M phi||^2 vs ||phi||^2: 7.7852032398508975 7.785203239850902
target1 body vs trace form: 1.6740958540805346e-22
target2: |L|^2 = 5.678894402969443e-14 <= W^-6d F1 F2 = 4.86149122398503e-10
target3: |L|^2 = 5.678894402969443e-14 <= W^-5d beta r1 r2 SA SC = 4.632804820839831e-07
   with W^-3d/2-root misprint: W^-3d beta.. = 2.964995085337492e-05 (Fable 5 prints W^{-3d/2} for the root)
Sum_x <phi_x,ImG phi_x> = W^d Tr(...): 4.366485651654079e-19
Sum_x||phi_x||^2 = Lcirc2: 0.001832865348466159 <= 0.01265390782036236
S_C 0.0018338739824726334 <= 2/eta Wd?  0.01265390782036236 True
expansion T0-T1-T1'+T2: 9.317362419797304e-21
one-M identity (sigma=true left end M^*): 1.7462031549538564e-21
one-M CS: 5.153226666583049e-06 <= 3.089430602831355e-05
   = W^-d |MB| sqrt(L2_bb L2_ab): 3.0512990006863718e-05 (sum_u,y |X_{(b,o(u)),y}|^2 = W^2d L2_bb : 12.356602106014517 12.356602106014517 )
two-M identity: 2.1177477977964176e-21
```
External hypotheses `STLocalEntrygL`, `STLmaxgL` (registered owed pins, stay hypotheses): concrete limit of their right-hand sides and of the flow data along `sz0`, n = 0,1,3,7,15 (`python3 limit.py`; exact eigenvalues of Ψ^B via the 1D cycle spectrum):
```
n  L   W        N^(1/6)<=W  WO(lo<=lam<=10)  Imm>=k  N^(-.9)<=Imz<=1  t0>=2/3  eta   W^d*Bctl  Bctl      Bctl^(5/2)/(1-t)  eta<=1  margin<=101  |mF|
0 4 32 True True True True True 0.499746 2.030274 6.196e-05 6.044e-11 True True 0.99949262 res 0.0e+00
1 8 1024 True True True True True 0.5 2.003906 1.866e-09 3.009e-22 True True 0.99999988 res 1.1e-16
3 16 32768 True True True True True 0.5 2.000488 5.686e-14 1.542e-33 True True 1.0 res 1.1e-16
7 32 1048576 True True True True True 0.5 2.000061 1.735e-18 7.928e-45 True True 1.0 res 2.2e-16
15 64 33554432 True True True True True 0.5 2.000008 5.294e-23 4.078e-56 True True 1.0 res 3.3e-26
```
Limit reading: `uB → (lam²+1/2)^{-1}+0 = 2 = (1-t)^{-1}`, `η → 1/2`, `|mF| → 1`, `Bctl ~ 2u^{-1} → 0` polynomially (≈ N^{-5/6}); so the pin bounds `B^{k-1}`, `STWB ≤ B` are the true small orders, the target `(1-t)^{-1}B^{5/2}` is positive, and `N^{-1+ε} ≤ Im z`, `W ≥ N^{1/6}`, WO hold at every listed n (`SizeTendsto`: N→∞). Nothing is `N=0`, empty or collapsed: blocks have u=32768 points, L^d=64 blocks.

### (iii) Charges, S3A-C1, targets 4-6 (checked above)
- σ=false: `φ_x=E_bǦ^*e_x`, 3-loops `Tr(E_aǦE_b(G|G^*)E_bǦ^*)` = loops `(-,+,±)` blocks `(a,b,b)`; σ=true: `ψ_x=E_bǦe_x`, `Tr(E_aǦ^*E_b(G|G^*)E_bǦ)` = `(+,-,±)`. Fold identity `Σ_x⟨φ_x,ImGφ_x⟩ = u·Tr(E_aǦE_b ImG E_bǦ^*)`, expansion `T0-T1-T1'+T2`, one-M closed form and Cauchy–Schwarz (`Σ_{u∈[a],y∈[b]}|X_{(b,o(u)),y}|² = W^{2d}𝓛^{(2)}_{bb}`), two-M closed form: all verified in `fold.py` (differences 1e-21; CS inequality 5.2e-6 ≤ 3.1e-5).
- 5a: `Σ_v|M_{xv}|² = Σ_c|M^B_{[x]c}|² = 1` (`BAMB_row_sq_real`, `BAMfine_eq`); 5b: `‖Mφ‖² = ‖φ‖²` on `[b]` by column Ward = row Ward (`BAMB_symm`) — equality, so ≤ holds (script: 7.7852… = 7.7852…). 4: `Im⟨φ,Gφ⟩ = η‖Gφ‖²` from `G-G^*=2iηG^*G`, then `‖(G-M)φ‖² ≤ 2‖Gφ‖²+2‖Mφ‖²`; 6a at t=1 also holds (`lam>0` from WO's lower bound, `1+𝔡² ≥ 1`); 6b needs only `κ ≤ Im mF`, `1-t ≥ 0`.
- 1: summand of `twLoop2X` at `c` equals `twLoopX n (XP_{c₃c₄}C) A a c₁ c₂` (`twLoopX` unfolds to `W^{-2d}Σ_xΣ_w A_{xw}(XP C)_{(c₂,o(w)),x}`; with `(XP_{c₃c₄}C)_{ux} = W^{-d}Σ_{w'∈[c₃]}X_{uw'}C_{(c₄,o(w')),x}` this is the body of `T2445_twLoop2X_eq`); numerically body = trace form to 1.7e-22.
- 2: Cauchy–Schwarz over `(c,x,w,w')` with weight `|ρ|`, both factors indexed by the same set (the pin's `∑ _w` in the C-factor). 3: F₁ ≤ β r₁ Σ_xΣ_v|A_{xv}|² (blocks partition, `c₂c₃c₄` marginal), F₂ ≤ u r₂ Σ_xΣ_v|C_{vx}|² (free `w`: card u; `w'↦shift c₄ w'` injective on `[c₃]`, `c₁c₂c₃` marginal at fixed `c₄`).

### Findings / open items for 1b (no pin is false)
1. Fable §5 `W^{-3d/2}` → `W^{-5d/2}` root; Fable §5 `GG^*` → `G^*G` in `twVec`: both already pinned correctly in the check file (row 1; `fold.py` target 3 line: the `W^{-5d}` bound holds; the `W^{-3d}` bound printed on the next line is the weaker, non-sharp constant).
2. `B_0 ≥ c0` (6a) is needed inside the ≺ proof at rows 5, 6, 10, not only in 7′; so 7 depends on 6a and 6b as well as 5a, 5b, 4.
3. Fine-trace forms of `(baFMz sz z).L` at k=2,3: needed (rows 4, 5, 6: 𝓛^{(2)} with charges (+,-), 𝓛^{(3)}). They follow from `BAExp14a_Gres_blockMat` + `BAExp14a_trace_Eblk`'s argument for any k; recommend one general-k public statement with the stem prefix (`TwistFold2_`), since L4d2b consumes k=2,3.
4. Premises of 7 used: `STLocalEntrygL` (row 2, 5), `STLmaxgL` k=1,2,3 (rows 4-6). Not used: `STLKgL`, `STDecaygL`, `LWAvgLawgL`, any `BATwist*` (C4).
5. File split: recommend the pre-authorized split. Facts: `wc -l` of the twins `BA/TwistPins.lean` 962, `Graph/BAExp14a.lean` 1307, `Graph/BAExp14aB.lean` 1771, `BA/TwistKer.lean` 1599 (landed files). `TwistFold2.lean` = targets 1-6, no stochastic imports (only `Sizes`, `BAMfine`, `BAflow_real`); `TwistFold2B.lean` = fine-trace forms, rows 4-6 of the table, 7, 7′, instances. No numeric size estimate is given here.

## Verdicts
- Target 1 (`twLoop2X`, `twLoop2X_trace`): PASS. Target 2 (`twFold2`): PASS. Target 3 (`twFold2_bound`, `W^{-5d}`): PASS.
- Target 4 (`twVec`, `G^*G` form): PASS. Target 5a (`twMrow_le`), 5b (`twMblk_le`): PASS. Target 6a (`twB0_ge`), 6b (`twEta_ge`): PASS.
- Target 7 (`twFold2Prec`) and 7′ (`twFold2PrecDet`): PASS (exponents close exactly at Y = uB, with factor `(𝔡^{-2}+1)` at Y = 1). Target 8 (instances): PASS, data above.

## (b) Script output (stage 1b) — Mon Oct 12 11:00:28 UTC 2026

Branch `t/T2445` at `817dcbd`, tree clean. Stage 1b began `Mon Oct 12 09:58:14 UTC 2026` (first `date -u` of the stage). Commits (`git log --format='%h %cI'`, = UTC − 7h): 9098ff9 03:22:11 (TwistFold2 part A), c6405ed 03:47:12, 842559c 03:52:52 (RBM3D.lean), 817dcbd 03:55:35.

### Line counts against the stop line (2000 per file; the pre-authorized split, as 1a finding 5 recommends)
```
$ wc -l RBM3D/BA/TwistFold2.lean RBM3D/BA/TwistFold2B.lean
     656 RBM3D/BA/TwistFold2.lean
    1066 RBM3D/BA/TwistFold2B.lean
    1722 total          (section commits: 642 lines at 9098ff9; 642 + 1051 at c6405ed)
```
### Builds
```
$ lake build RBM3D.BA.TwistFold2 RBM3D.BA.TwistFold2B 2>&1 | grep -E "TwistFold2|Build completed|error"     # Mon Oct 12 10:59:42 UTC 2026
Build completed successfully (4007 jobs).          (no warning or error line names either file)
$ lake build     # whole library; RBM3D.lean imports both modules; Test/Axioms.lean unchanged; 10:55:35 - 10:56:28 UTC
Build completed successfully (4272 jobs).          exit: 0   (the `#assert_rbm_axioms` of RBM3D.lean passed, no registry change)
```
### Axioms (`#print axioms` of the 77 public declarations of the two files; the 5 private helpers are not printed)
```
public decls: 77, standard three: 77, other lines: 0
'RBM.BA.twLoop2X_trace'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2_bound_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twVec_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twMrow_le_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twMblk_le_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twB0_ge_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twEta_ge_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2Prec_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2PrecDet_holds'  depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/TwistFold2.lean RBM3D/BA/TwistFold2B.lean      -> no match (exit 1)
```
### Target statements, extracted by script (`file:line: first 132 characters of the head`; full text compared with the pins just below)
```
TwistFold2.lean:114: def twLoop2X (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L
TwistFold2.lean:121: theorem twLoop2X_trace (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (ρ : Zd d (sz.L n) → Zd d (sz.L n) → 
TwistFold2.lean:147: def twFold2 : Prop := ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
TwistFold2.lean:234: def twFold2_bound : Prop := ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
TwistFold2.lean:397: def twVec : Prop := ∀ {ι : Type} [Fintype ι] (G M : Matrix ι ι ℂ) (η : ℝ), η ≠ 0 →
TwistFold2.lean:436: def twMrow_le : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
TwistFold2.lean:454: def twMblk_le : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
TwistFold2.lean:516: def twB0_ge : Prop := ∀ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ), sz.WO 𝔡 → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ 1) →
TwistFold2.lean:542: def twEta_ge : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
TwistFold2B.lean:895: def twFold2Prec (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠
TwistFold2B.lean:917: def twFold2PrecDet (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ 
$ python3 -I diffpins.py     # whitespace-normalised bodies of the 9 pin defs of docs/tickets/checks/T2445-check.lean vs the targets (`T2445_` stripped, `L2X d sz ` := `twLoop2X `)
twVec           : identical to T2445_twVec (after L2X d sz -> twLoop2X, T2445_ stripped)
twMrow_le       : identical to T2445_twMrow_le (after L2X d sz -> twLoop2X, T2445_ stripped)
twMblk_le       : identical to T2445_twMblk_le (after L2X d sz -> twLoop2X, T2445_ stripped)
twB0_ge         : identical to T2445_twB0_ge (after L2X d sz -> twLoop2X, T2445_ stripped)
twEta_ge        : identical to T2445_twEta_ge (after L2X d sz -> twLoop2X, T2445_ stripped)
twFold2         : identical to T2445_twFold2 (after L2X d sz -> twLoop2X, T2445_ stripped)
twFold2_bound   : identical to T2445_twFold2_bound (after L2X d sz -> twLoop2X, T2445_ stripped)
twFold2Prec     : identical to T2445_twFold2Prec (after L2X d sz -> twLoop2X, T2445_ stripped)
twFold2PrecDet  : identical to T2445_twFold2PrecDet (after L2X d sz -> twLoop2X, T2445_ stripped)
twLoop2X        : body identical to the RHS of T2445_twLoop2X_eq
```
### The check file and its scratch copy (CLAUDE.md §4 step 0; the copy is not committed)
```
$ lake env lean docs/tickets/checks/T2445-check.lean                  # Mon Oct 12 10:58:37 UTC 2026, in the t/T2445 worktree
exit 0, error lines 0
$ lake env lean T2445-check-scratch.lean    # = the check file + `import RBM3D.BA.TwistFold2/B` + 11 examples, each closed by the target theorem as a term
example : T2445_twVec := twVec_holds
example : T2445_twMrow_le := twMrow_le_holds
example : T2445_twMblk_le := twMblk_le_holds
example : T2445_twB0_ge := twB0_ge_holds
example : T2445_twEta_ge := twEta_ge_holds
example : T2445_twLoop2X_eq (fun d sz => @twLoop2X d sz) := fun _ _ _ _ _ _ _ _ => rfl
example : T2445_twLoop2X_trace (fun d sz => @twLoop2X d sz) := @twLoop2X_trace
example : T2445_twFold2 (fun d sz => @twLoop2X d sz) := twFold2_holds
example : T2445_twFold2_bound (fun d sz => @twLoop2X d sz) := twFold2_bound_holds
example (d : ℕ) : T2445_twFold2Prec (fun d sz => @twLoop2X d sz) d := twFold2Prec_holds d
example (d : ℕ) : T2445_twFold2PrecDet (fun d sz => @twLoop2X d sz) d := twFold2PrecDet_holds d
exit 0, error lines 0
```
### Compiled nonempty instances (`example`s in the files; `sz0` = (d,L,W) = (3,4,32) at n = 0, `zSeq`, `flow_sz0`; nothing is N = 0, empty or collapsed)
```
TwistFold2.lean:592  twLoop2X (sz := sz0) 0 1 1 1 (1[c = (0,0,0,0)]) 0 ≠ 0    (value 1: `TwistFold2_inst_val`; block card 32768: `TwistFold2_card_sz0`)
TwistFold2.lean:595  twLoop2X_trace at the same data     :598  twFold2_holds 3 sz0 0 ...     :601  twFold2_bound_holds ... β = 32768, r₁ = r₂ = 1 (row/column sums by TwistFold2_rho0_row/_col)
TwistFold2.lean:612  green [[0,1],[1,0]] i ≠ 0     :622  twVec at G = green [[0,1],[1,0]] i, M = 1/2, φ = e₀ (statement written out; gram identity discharged)
TwistFold2.lean:631  twMrow_le at baFMz sz0 zSeq, n = 0, x = 0     :635  twMblk_le with φ = indicator of the block [0]     :642  twB0_ge, t ≡ 1/2, 𝔡 = 1/10 (∃ n)     :647  twEta_ge, n = 0, t = 1/2
TwistFold2B.lean:1034 twFold2PrecDet at d = 3, κ = 1/2, ε = 1/10, 𝔡 = 1/10, 𝔠 = 1/6, t ≡ 1/2, Cρ = 1/4, ρ₀ = (1/2)² 1[c₃ = c₁ ∧ c₄ = c₂] (twMB c₁ c₂)²: r₁, r₂ ≤ 1/4 PROVED (TwistFold2_rho2_bounds, M-Ward + BAMB_symm); only STLocalEntrygL, STLmaxgL stay hypotheses
TwistFold2B.lean:1047 twFold2Prec at the same data with X ≡ 1 (‖1‖ ≺ W^d Bctl by TwistFold2_one_prec, i.e. by target 6a)
```
### Name clash, S3A-C1 grep, diff
```
$ bash clash.sh   # the 82 new names (77 public + 5 private) as `theorem|def|lemma|abbrev|structure|inductive|instance` heads in `git grep` of main (20917ed) and the 48 other t/T24* branches
clashes: 0         (sanity: the same grep finds twLoopX and twFold_holds on main)
$ grep -nwE 'mE|STGM|STKloop' RBM3D/BA/TwistFold2.lean RBM3D/BA/TwistFold2B.lean     -> no match (exit 1)
$ grep -n BATwist RBM3D/BA/TwistFold2.lean RBM3D/BA/TwistFold2B.lean                  -> no match (exit 1)
$ git diff --stat main...t/T2445
 RBM3D.lean | 2 +   RBM3D/BA/TwistFold2.lean | 656 +   RBM3D/BA/TwistFold2B.lean | 1066 +    3 files changed, 1724 insertions(+)       (all three are sole writable files)
```
### Narrative
- **Files.** `TwistFold2.lean` = targets 1-6 and their instances (deterministic; imports `TwistPins`, `ConArgDet`). `TwistFold2B.lean` = the fine-trace `3`-loop, the marginals `S_A`, `S_C`, the `≺` calculus, targets 7, 7′ and their instances. `RBM3D.lean` got the two `import` lines after the last `import` (sole writable file; the hub's merge step 4 adds the same two lines). `git show main:RBM3D.lean` (20917ed) has three further lines after `import RBM3D.Graph.BAZetaExp` (`Graph.BALvl1C`, `BA.TwistStep`, `BA.TwistStep2`), the same insertion point, so that file is a union at the merge (ticket: "`RBM3D.lean`: union").
- **Targets 1-6** are the pinned statements verbatim (diff above); `twLoop2X` has the pinned body, so `T2445_twLoop2X_eq` is `rfl`. The two Fable §5 corrections hold as compiled: the root `W^{-5d}` (target 3: `twFold2_holds` gives `W^{-6d}`, the free `o`-sum gives `W^d`), and the `G^*G` form of target 4 (`TwistFold2_imQ`: `Im⟨φ,Gφ⟩ = η‖Gφ‖²`).
- **Target 7 (chain).** `TwistFold2_pathwise` = `twFold2_bound_holds` with `β = W^d b²`, `r₁ = r₂ = Cρ·Y` (`b = max|Ǧ|`, `Y = max|X|`) times `TwistFold2_SA_carrier` and `TwistFold2_SC_carrier`; `TwistFold2_row` then applies `TwistFold2_arith` (the exponent table, rows 9-10; `K = 16+16c₀⁻²+8c₀⁻¹`, `c₀ = (𝔡⁻²+1)⁻¹`) and `η⁻¹ ≤ κ⁻¹(1-t)⁻¹` (target 6b). The `≺` closure is the one-index calculus of `BAExp14a_Dom` on `Z = 1 + b²/B + ℓ₁ + ℓ₃/B² + Y/(W^d B)` (`Z ≺ 1`, `Z⁵ ≺ 1`) and `f² ≺ g² ⇒ f ≺ g` (`TwistFold2_prec_sqrt`). Target 7′ is target 7 at `X ≡ 1` (`TwistFold2_one_prec`, target 6a).
- **S3A-C1 is organised differently from 1a (ii)/(iii)**, no band formula (grep above). 1a expands both circled legs into `T0 - T1 - T1' + T2` with 2-loop Cauchy-Schwarz bounds. The proof instead (a) bounds the column `Ǧφ_x` by `twVec_holds` (`φ_x = E_b Ǧ(σ) e_x`), (b) splits only the vector, `φ = φ^G - φ^M`, and uses `Im⟨φ,Gφ⟩ = η‖Gφ‖²` and `‖a-b‖² ≤ 2‖a‖²+2‖b‖²`: `Im Q(φ) ≤ 2 Im Q(φ^G) + 2 Im Q(φ^M)` (`TwistFold2_imQ_sub`), so no cross term occurs; (c) `Σ_x Q(φ^G_x) = W^d 𝓛^{(3)}_{(σ̄,+,σ),(b,b,a)}` (`TwistFold2_L3_carrier`), (d) `φ^M_x` is supported at the one point `(b,o(x))` by the BA tie `M_{uv} = 1[o(u)=o(v)] M^{(B)}_{[u][v]}` (`BAMfine_eq`), so `Σ_x Im Q(φ^M_x) ≤ W^{-d} ℓ₁`.
- **Premises actually used:** `STLocalEntrygL` (through `BAExp14a_Dom_b`) and `STLmaxgL` at `k = 1` and `k = 3` only. 1a findings 3-4 (fine-trace forms at `k = 2`, `STLmaxgL` at `k = 2`) are not needed. Not used: `STLKgL`, `STDecaygL`, `LWAvgLawgL`, any `BATwist*`. The hypotheses `3 ≤ d`, `0 < ε`, `0 < 𝔡` of the pins are unused by the proof (kept as pinned).
- **Public stem-prefixed helpers** (CLAUDE.md §3 (E)) used across the two files: `TwistFold2_sum_shift`, `_mem_blk`, `_split_shift`, `_card_blk`, `_green_conj`, `_gram_green`, `_imQ`; the `3`-loop form is `TwistFold2_loop3` (any matrix `H`, `k = 3`) and `TwistFold2_L3_carrier`.
- No `(a′)`: no mistake in section (a) was found; its plan differs from the proof only as stated above.

## (c) Verified Mathlib names (all `#check`ed in this tree; 51 names, one script run, no error)
`Finset.`: `sum_mul_sq_le_sq_mul_sq`, `sum_sq_le_sum_mul_sum_of_sq_le_mul`, `sum_fiberwise`, `sum_nbij`, `sum_ite_mem`, `univ_inter`, `exists_mem_eq_sup'`, `le_sup'`, `univ_nonempty`, `sum_eq_single`, `sum_product`.
`Matrix.`: `star_mulVec`, `dotProduct_mulVec`, `star_dotProduct`, `sub_mulVec`, `smul_mulVec`, `mulVec_mulVec`, `conjTranspose_nonsing_inv`, `nonsing_inv_mul`, `isUnit_iff_isUnit_det`, `mul_diagonal`, `nonsing_inv_eq_ringInverse`; root: `dotProduct_sub`, `dotProduct_smul`.
`Complex.`: `conj_mul'`, `sub_conj`, `im_ofReal_mul`, `im_mul_ofReal`, `im_sum`, `im_le_norm`, `star_def`. `Equiv.sum_comp`, `Fintype.sum_prod_type`, `star_mul'`, `mul_inv`, `inv_mul_cancel₀`, `mul_inv_cancel₀`.
Order/pow: `inv_anti₀`, `one_le_inv₀`, `pow_le_pow_left₀`, `pow_lt_pow_left₀`, `lt_div_iff₀`, `norm_sub_le`, `norm_sum_le`. Real/filters: `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_nonneg`, `tendsto_rpow_atTop`, `tendsto_natCast_atTop_iff`, `Filter.eventually_ge_atTop`.
Verified absent or changed: `star_dotProduct` and `isUnit_iff_isUnit_det` are not root names (they are `Matrix.`); `mul_le_one₀` is deprecated ("No replacement"), `if_neg`, `if_true` deprecated; there is no `Mathlib.olean` (no `import Mathlib` in scratch files).

## (d) Open issues and paper-delta candidates
1. **Dispatcher notes vs proof.** DECISIONS §257 says the three-cross-term/2-loop expansion of S3A-C1 is "required content of the proof". The proof proves the pinned statement without it (narrative above); the premise set is smaller (`k = 2` unused). If a consumer wants the `𝓛^{(2)}`-form, it is not here.
2. **Pathwise, no `U`-subtype.** Target 7 is pathwise over `(σ,a,b)` and holds for all `t ∈ [0, T₀]`; `BAExp14bS3`'s `{λ²/L^d ≤ 1-t}` restriction is the consumer's. The `𝔼` form needs `BAExp14a_prec_integral` with a polynomial envelope of `X` (L4d2b / L4c1).
3. **Eventual in `n`.** The weight bounds `r₁, r₂ ≤ Cρ` (pinned, as `twK_bound`, T2421a) and `W^d Bctl ≥ c₀` (target 6a, from `WO`) hold eventually; the constant of 7 is `K Cρ² κ⁻²`, `K = 16+16c₀⁻²+8c₀⁻¹`, not optimised.
4. **Unused pin hypotheses:** `3 ≤ d`, `0 < ε`, `0 < 𝔡` (target 7, 7′); `0 < κ` is used.
5. **Paper-delta candidates** (the dispatcher assigns numbers): **T2445a** the stuck nodes are bounded by the fold (A′) of Fable §2.2 with the root `W^{-5d}` (Fable §5 printed `W^{-3d/2}`) and `G^*G` (printed `GG^*`), in place of the second `GG` step of B:118 (also T2434a/b). **T2445b** the leaf bound is the `[a]×[b]`-averaged ord-5 bound, pathwise in `(σ,a,b)`, with an `X`-factor `≺ W^d Bctl` for #17, #47; the paper's `N` sufficiently large is made `∀ᶠ n`. **T2445c** S3A-C1 is proved by the BA tie of `M` and the splitting `Ǧ(σ) = G(σ) - M(σ)` (no band formula, no cross terms).
