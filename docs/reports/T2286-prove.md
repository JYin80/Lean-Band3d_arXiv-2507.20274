Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 11:19:43 UTC 2026

### (i) Exponent table
Notation: `k = m+2`, `W`, `N` as in the ticket, `C_n = qProxyCn d (m+1) Λg KL C c`, `C₄ = qProxy4C d (m+2) Λg κ' KL`, `C_Q = 2C_n+2` (QProxy.lean:434-444); `C_n, C₄ > 0` for `d ≥ 3`, positive data (`qProxyCn_pos`, `qProxy4C_pos`) and depend on `(d, m, Λg, κ'/KL, C, c)` only.

**Level-use audit of `dFlowQN_levelM` (QLevelsB.lean:189-238) against `GoodSetN` (GridGoodN.lean:124-149) and the target-1 replacement:**
| use in the proof | clause | level in the clause | target 1 |
|---|---|---|---|
| `hHerm := hG.1` | 1 (Herm) | none | kept |
| `drift13_fastDecay` -> `driftTensorN_far_of_goodSet` (NQGood1.lean:138) | 8 (Va): `<= W^{-D'}` | none | kept (any `Γc Λc Φc`) |
| `goodSetN_LKM_far` (QLevelsB.lean:108-123) | 3 (Dec): `<= W^{-D'}` | none | kept (`hF`) |
| `goodSetN_LKM_le` (G2) (QLevelsB.lean:86) | 2: `Ξ <= Γc Φc` | `Γc Φc` | used only for `hY`; replaced by the explicit premise `hY` (`ν X B^{m+1}`) |
| `driftTensorN_norm_le_of_goodSet` | 4-6 (D1)-(D3) | `Γc, Φc` | replaced by `driftTensorN_norm_le_of_goodLin` (NQLin.lean:732; levels `Γ,Φ₁,Φ₂,Φ₃` of `GoodLinN`) |
| clauses 7, 9 `(D4)` | ee | `Λc` | unused |
`GoodLinN` quantifies every `σ` (NQLin.lean:66-74), `driftTensorN` is `σ`-generic, and `dFlowQN`'s block is the text `driftTensorN sz n E u Hm σ b` (`hflow := rfl`, QLevelsB.lean:230-233); so `σ (Fin.last (m+1)) = !σ 0` enters only through `altB45N_levelM` (QLevelsA.lean:376). After the substitution `Γc Λc Φc` occur only inside the membership `H ∈ GoodSetN … Γc Λc Φc`, whose used clauses 1, 3, 8 carry no level. The nonnegativity needed by `pi_norm_le_iff_of_nonneg` follows from the pointwise bound at `fun _ => 0`, so no sign hypothesis on `Φ_i`. Supervisor 2026-10-06-1102 §1.2 (A2: yes) is consistent with this audit.

**Linear level vs merged level (target 4):** `dDriftLinN(k,Γ,Φ,kΓΦ²,Φ) = Γ²(B^k/η)((k-2)Φ+kΓΦ²+Φ) = Γ(ΓΦ)(B^k/η)((k-1)+kΓΦ) = dDriftNonAltN`. `dDriftAltQN` unfolds (QLevelsB.lean:53-56) to `dDriftNonAltN sz n E u (m+1+1) Γ Φ`, so `rw [dDriftNonAltN_eq_lin]` unifies at `k := m+1+1`, producing the statement's `((m+1+1:ℕ):ℝ)*Γ*Φ^2`; `m+2` occurs only in the third summand's `Bctl^(m+2)`, identical on both sides (QBudgetA.lean:94-97). Target 3: `(k:ℝ)-2 = m >= 0`, `Γ*Γ >= 0`, `etaT_pos (|E|<2, u<1)`, `STBctl_pos (u<1)`: no hypothesis on `Γ` needed.

**Sufficiency (ii-part):** `budgetAltQN` (QBudgetA.lean:575-) concludes `N^{ε₀}(Λ^{1/2}+Φd)B_v^k`, affine in `Φd = Φ₁+Φ₂+Φ₃+X` (`dDriftAltLinQN_le_shape`, QBudgetA.lean:419). With `Φ₂ = nqLinPhi2 … (XLK k)` (NQLin.lean:84-88) the current length enters only as `B_v^{1/6} XLK k` (script: every `XLK`/`XL` index in the sum is `<= k-1`); `X` is the length-`(k-1)` level of `hY`. So the right side differs from NQEndLin's `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k` (NQEndLin.lean:31, 1096) only by `+X`. Closing the bootstrap with it is S3-18b, not checked here.

**`ν`, `τ_N` (targets 1-2):** need `(2m+5)·3·4^{dm}(2/√κ)Cν² <= N^{τ_N}`, `(W^{τ'})^{dm} <= ν <= N`, `W^{-D'} <= ν N^{-(2m+4)}`. With `ν = N^δ`: `2δ < τ_N <= ε₀/8`; `τ' d m <= δ` (since `W <= N`, NQEndLin.lean:142); `𝔠 D' >= 2m+4+δ`. Compatible: `τ_N, δ` free in `(0, ε₀/8)`; `D'` is an eventual lower bound only.

**Boundary data:** target 1 `0 <= u < 1`, `|E| <= 2-κ`, `N⁻¹ <= 1-u` (case (i) only); target 2 `0 <= s n <= v n < 1`, `N⁻¹ <= 1-v n`; no `t <= lemT`, no `1-g²/L²`. `L^d <= W^{KL}` is an explicit premise of targets 1-2; targets 5-6 use only `W <= N` (`1 <= d`) and `Bandwidth 𝔠`. Target 6 is `∀ᶠ n` in its conclusion and in the `κ' <= Im mE(E n)`, `0 < lam <= Λg` premises.

**Target 5 (`ξ = -(2k+1)`; hypotheses `a=C₄ε, C_nε, C_nε' <= ε₀/8`, `ε₁,εq,τ_N <= ε₀/8`, `ε <= 1/2`, `D' >= C₄+C_n+(2k+1)/𝔠`, `D'' >= C_Q+2C₄+k+(4k+1)/𝔠`, `D_Y,D_t >= k`); slack of each of the 20 conjuncts of `altBudgetExpQN`:**
| conjunct | bound derived | slack |
|---|---|---|
| `C₄ε+ε₁`, `C₄ε+τ_N` `< ε₀` | `<= ε₀/4` | `>= 3ε₀/4` |
| `C₄ε+C_nε'+2ε₁`, `εq+C₄ε+C_nε+ε₁` `< ε₀` | `<= ε₀/2` | `>= ε₀/2` |
| `C₄ <= D'`; `k+𝔠(C₄-D') < ε₀` | `D'-C₄ >= C_n+(2k+1)/𝔠`; `<= -(k+1)-𝔠C_n` | `>= C_n+(2k+1)/𝔠`; `>= ε₀+k+1+𝔠C_n` |
| `C₄ε+C_n <= D'`; `2k+𝔠(C₄ε+C_n-D') < ε₀` | `ε <= 1`; `<= -1-𝔠C₄(1-ε)` | `>= (2k+1)/𝔠`; `>= ε₀+1` |
| three `<= 0` of `D''-C_Q` | `D''-C_Q >= 2C₄+k+(4k+1)/𝔠` | `>= k+(4k+1)/𝔠`, `>= k+(4k+1)/𝔠`, `>= C₄+(4k+1)/𝔠` |
| three `<= ξ` | `-2k-1-𝔠k`, `-3k-1-𝔠k`, `-𝔠C₄-4k-1` | `>= 𝔠k`, `>= k+𝔠k`, `>= 2k+𝔠C₄` |
| `εq+k+ξ/2 < ε₀` | `= εq-1/2` | `>= 7ε₀/8+1/2` |
| `k-D_Y`, `k-D_t` `< ε₀` | `<= 0` | `>= ε₀` |
All slacks positive for every `C₄, C_n, 𝔠, ε₀ > 0`; `0 < ε` is not used.

**The eight rows of target 6** at the ticket's choice (`ε₀=1, k=3, 𝔠=1/6, Λg=1` so `P=(1+Λg²)^k=8`, `κ'=24/25`, `ε=min(1/(8(C₄+C_n)),1/2)`, `ε'=1/(8C_n)`, `ε₁=εq=τ_N=1/8`, `D'=C₄+C_n+42`, `D''=C_Q+2C₄+81`, `ξ=-7`); positive `W`-powers `<= N`-powers, negative via `W >= N^𝔠`, `Ls <= κ'⁻¹ log N`; `N₀` = last `N` at which the worst-case form fails (script S3):
| row | `log_N` of left side (worst case) | margin to `ε₀=1` | `N₀` |
|---|---|---|---|
| `ha1` | `C₄ε+ε₁ <= 1/4` | 3/4 | 10.9 |
| `ha2` (two summands, each `<= N^{ε₀}/24`) | `1/2` (`k N^{C₄ε+C_nε'+2ε₁}`) and `1/4`, times `Ls` | 1/2 (polylog) | 2.19e5 |
| `ha3` | `1/2` times `√(k(Ls+1))` | 1/2 (polylog) | 4.2e3 |
| `he0` | `-4-𝔠C_n` (constant 2) | `>= 5` | 1.9 |
| `he1` | `max(-1-𝔠C₄(1-ε), -4-𝔠C_n)` (constants `P`, 4) | `>= 2` | 9.8 |
| `he2` | `εq+k+ξ/2 = -3/8`, constant `√(k(P²+P+1)) = 14.80` | 11/8 | 43 |
| `he3`, `he4` | `k-D = 0` | 1 | 6.0 |
Dominant crossover `2.19e5` (`ha2`) is independent of `C₄, C_n`; ticket (iii) says `5·10³` for `ha3`, script gives `4.2·10³` (ticket values for the other rows agree). `sz0` at `n=0` has `N = 2^21 > 2.2e5`.

### (ii) One concrete nondegenerate instance
(1) targets 1-4: `sz0`, `d=3`, `n=4` (`x=10, W=10^5, L=20, N=8·10^18, lam=10^{-6}`), `m=2, k=4`, `E=0, u=0`, `κ=1`, `H=0`, `σ = ![T,F,T,F]`, `(Γc,Λc,Φc)=(4,100,1)`, `(Γ,Φ₁,Φ₂,Φ₃)=(4,1,16,1)` (`goodSetN_subset_goodLinN`, `Φ₂ = kΓΦ² = 16`), `τ'=1/10, ε'=1/5, D'=40, ν=W, X=1, τ_N=2, C=Cmol3=(1+40·9)·6^9, c=1/2, KL=2, Λg=1`; target 2 on the walk `E≡0, s≡0, v≡1/2, Kg≡4, τ≡1, j=0` (same numbers, `N⁻¹ <= 1-v`). Both `GoodSetN` and `GoodLinN` memberships are for `H=0` (QLevelsBInst `zero_mem_inst`); `hY` is `4 <= νX = W`, via `goodSetN_LKM_le`.
(2) target 5: the choice above for `(C₄,C_n) ∈ {(1/100,1/100),(1,1),(100,2),(3,200)}` plus 20000 random hypothesis-satisfying rational parameter sets.
(3) target 6: `sz0` (all `n`), `d=3`, `m=1` (`k=3`), `Λg=1, KL=1, C=1, c=1/2, κ'=24/25`, `E≡1/2` (`Im mE = √15/4`), `𝔠=1/6`, the choice of (2). External hypotheses: `SizeTendsto`: `N_n = 8x^{18}`, `x=2(n+1) -> ∞`; `Bandwidth 1/6`: `N^{1/6} = 8^{1/6}x^3 <= x^5 = W` iff `x² >= √2`, true for all `n` (script last block; Sizes.lean:260-300); `lam = x^{-6} ∈ (0,1]`.
Commands (scratchpad `S = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2286`; run in `/Users/junyin/Lean_proof/RBM3D`; Python only, no Lean):
`python3 $S/preflight.py` (S1 level data, S2 target 5, S3 rows, S4 actual row values at `sz0`: `log10(lhs/rhs)`, negative = holds):
```
S1 sz0 n=4: x,W,L,N = 10 100000 20 8000000000000000000  lam= 1/1000000  k=m+2= 4
 hNu  N^-1<=1-u        : True
 hMLam (2m+5)*3*4^(dm)*(2/sqrt1)*Cmol3*nu^2 <= N^tauN, nu=W,tauN=2 : True  ratio N^2/lhs=7.953e+12
 hFv  W^-40 <= nu*N^-(2m+4)  (<=> N^8 <= W^41): True
 4<=W^(1/5) (4^5<=W): True ; L^3<=W^K,K=2: True ; 3W^(1/10)<=W^(1/5) (3^10<=W): True
 (W^(1/10))^(dm)=W^(0.6)<=nu=W : True ; nu<=N: True ; hY: Gc*Phic=4<=nu*X=W: True
 coefficient at (G,Phi)=(4,1),k=4: linear (k-2)P1+P2+P3 = 19 = 2+16+1 ; merged (k-1)+kG*P = 19  ; Gamma^2-multiples equal: True
 identity dDriftLinN(k,G,Phi,k G Phi^2,Phi)=dDriftNonAltN(k,G,Phi), 2000 random rationals: True
 k=2..60, indices in Phi2 (nqLinPhi2): max(XLK index - k) = -1 , max(XL index - k) = -1 ; violations of (XLK index<k, XL index>=1): []
 => Phi2 = S + B^(1/6)*XLK(k) with S free of XLK(k); dDriftAltLinQN is affine in Phi2: coefficient of XLK(k) is W^(Cn e') G^2 (B^k/eta) B^(1/6)
S2 ticket choice (k=3,c=1/6,e0=1): D'=C4+Cn+42, D''=2Cn+2+2C4+81, eps=min(1/(8(C4+Cn)),1/2), eps'=1/(8Cn), e1=eq=tN=1/8, xi=-7
  C4=1/100 Cn=1/100: all 20 conjuncts hold: True ; tightest strict one: C4e+Cne'+2e1<e0, slack 31/50
  C4=1 Cn=1: all 20 conjuncts hold: True ; tightest strict one: C4e+Cne'+2e1<e0, slack 9/16
  C4=100 Cn=2: all 20 conjuncts hold: True ; tightest strict one: C4e+Cne'+2e1<e0, slack 205/408
  C4=3 Cn=200: all 20 conjuncts hold: True ; tightest strict one: C4e+Cne'+2e1<e0, slack 253/406
  target 5: random hypothesis-satisfying parameter sets (exact Fractions): 20000  failures of altBudgetExpQN: 0
S3 rows at the choice, eps0=1,k=3,P=(1+Lg^2)^k=8, Ls<=kappa'^-1 log N, kappa'=24/25; last N where the worst-case row fails:
  ha1  N0=10.9         N^(C4e+e1)=N^(1/4)  <= N/6
  ha2  N0=2.193e+05    (k N^(1/8+1/8+1/4)+N^(1/8+1/8)) Ls <= N/12
  ha3  N0=4184         N^(1/2) sqrt(k(Ls+1)) <= N/12
  he0  N0=1.888        2N^(k+c(C4-D'))=2N^(-4-cCn) <= N/12
  he1  N0=9.797        P N^(2k+c(C4e+Cn-D'))+4N^(k+c(C4-D')) <= N/12
  he2  N0=43.24        N^(eq+k+xi/2) sqrt(k(P^2+P+1)) <= N/12
  he3  N0=5.999        N^(k-D_Y)=N^0 <= N/6
  he4  N0=5.999        N^(k-D_t)=N^0 <= N/6
  sqrt(k(P^2+P+1)) = 14.799
S4 sz0, E=1/2 (Im mE=sqrt15/4=0.9682>=24/25), eps0=1: log10(lhs/rhs) of the eight rows (negative = holds)
  C4=0.01 Cn=0.01 n=0 N=2.10e+06: ha1:-4.75 ha2:-1.80 ha3:-2.81 he0:-49.21 he1:-30.54 he2:-27.25 he3:-5.54 he4:-5.54
  C4=0.01 Cn=0.01 n=4 N=8.00e+18: ha1:-15.74 ha2:-10.32 ha3:-11.98 he0:-170.86 he1:-114.43 he2:-104.33 he3:-18.12 he4:-18.12
  C4=1 Cn=1 n=0 N=2.10e+06: ha1:-4.66 ha2:-1.71 ha3:-2.63 he0:-50.70 he1:-31.94 he2:-28.65 he3:-5.54 he4:-5.54
  C4=1 Cn=1 n=4 N=8.00e+18: ha1:-15.45 ha2:-10.03 ha3:-11.40 he0:-175.81 he1:-119.09 he2:-108.99 he3:-18.12 he4:-18.12
  C4=100 Cn=2 n=0 N=2.10e+06: ha1:-4.57 ha2:-1.62 ha3:-2.63 he0:-52.20 he1:-51.90 he2:-111.89 he3:-5.54 he4:-5.54
  C4=100 Cn=2 n=4 N=8.00e+18: ha1:-15.15 ha2:-9.73 ha3:-11.40 he0:-180.81 he1:-180.51 he2:-382.35 he3:-18.12 he4:-18.12
  C4=3 Cn=200 n=0 N=2.10e+06: ha1:-4.75 ha2:-1.80 ha3:-2.63 he0:-350.22 he1:-35.04 he2:-31.75 he3:-5.54 he4:-5.54
  C4=3 Cn=200 n=4 N=8.00e+18: ha1:-15.75 ha2:-10.33 ha3:-11.40 he0:-1170.81 he1:-129.40 he2:-119.29 he3:-18.12 he4:-18.12
sz0 limits (Sizes.lean:260-300): W=x^5,L=2x,N=8x^18, x=2(n+1)->inf; N^(1/6)=8^(1/6)x^3 <= x^5 iff x^2>=sqrt2: [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True)]
exact: kappa'=24/25 <= Im mE(1/2)=sqrt(15)/4  <=>  (24/25)^2*16 <= 15 : True ; target 2 walk (v=1/2): N^-1 <= 1-v : True ; Phi2=k*G*Phi^2= 16
```
`python3 $S/consumer_diff.py` (the text of `ha1`-`he4` of `budgetAltQN`, QBudgetA.lean:597-623, with `Pa = W^{C_nε'}(Γ n·Γ n)k+N^{τ_N}`, `Γ n = N^{ε₁}`, `b = W^{-D'+C_n}`, `δ0 = 2W^{-D'}`, `δD = 4W^{-D'}` substituted, against the conjuncts of `altBudgetNumQN` in the check file):
```
budgetAltQN numeric hypotheses: 8   altBudgetNumQN conjuncts: 8
whitespace-normalized text identical, row by row: [('ha1', True), ('ha2', True), ('ha3', True), ('he0', True), ('he1', True), ('he2', True), ('he3', True), ('he4', True)]
```

## Verdict (section (a))
- Targets 0 (vocabulary), 1 `dFlowQN_levelLin`, 2 `alt_hdriftLinQN`, 3 `dDriftAltLinQN_nonneg`, 4 `dDriftAltQN_eq_lin`, 5 `altBudgetExpQN_of_choice`, 6 `altBudgetNumQN_eventually`: PASS. The linear level is true (audit above) and sufficient (affine in `Φd`, differs from NQEndLin's right side by `+X`); every hypothesis set holds at the instance; every exponent conjunct closes with the slacks above.
- Inputs left with S3-18a (as the ticket says): `hY` at length `m+1` and `GoodSetN` membership at some crude level (not tied to `Γ, Φ_i`).

## (a′) Preflight corrections — Tue Oct  6 11:42:01 UTC 2026
- (i) Target 5 table, last line "`0 < ε` is not used": conjuncts 1-2 (`0 ≤ C₄ε`, `0 ≤ C_nε`) are not implied by the other hypotheses without `0 ≤ ε`, so `hε : 0 < ε` is used (proof: `positivity` at those two conjuncts). The slack column and the verdict are unchanged.

## (b) Script output — Tue Oct  6 11:42:01 UTC 2026
Branch `t/T2286`, commit `e1e4846` (`git rev-parse --short HEAD` in `/Users/junyin/Lean_proof/RBM3D-wt/T2286`), one file: `RBM3D/Induction/QBudgetB.lean`, 1142 lines.
```
$ lake build RBM3D.Induction.QBudgetB ; echo exit=$?      (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2286)
exit=0
$ grep "QBudgetB.lean" build.out | grep -v "info:" | wc -l        # warnings/errors from the new file
0
$ grep "Build completed" build.out
Build completed successfully (3862 jobs).
$ lake env lean RBM3D/Induction/QBudgetB.lean | grep -v "^'RBM"        # no output: no warning, no error
$ lake build ; echo exit=$?       (whole library; root RBM3D.lean does not import the new module before the hub merge)
Build completed successfully (4092 jobs).   exit=0
$ grep -n "sorry\|admit\|native_decide\|^axiom\|maxHeartbeats" RBM3D/Induction/QBudgetB.lean | wc -l
0
```
Axioms (`#print axioms` lines at the end of the file, from the build output):
```
QBudgetB.lean:1129:0: 'RBM.Ind.altBudgetNumQN' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1130:0: 'RBM.Ind.altBudgetExpQN' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1131:0: 'RBM.Ind.dFlowQN_levelLin' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1132:0: 'RBM.Ind.alt_hdriftLinQN' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1133:0: 'RBM.Ind.dDriftAltLinQN_nonneg' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1134:0: 'RBM.Ind.dDriftAltQN_eq_lin' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1135:0: 'RBM.Ind.altBudgetExpQN_of_choice' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1136:0: 'RBM.Ind.altBudgetNumQN_eventually' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1137:0: 'RBM.Ind.QBudgetBInst.dFlowQN_levelLin_instance' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1138:0: 'RBM.Ind.QBudgetBInst.alt_hdriftLinQN_instance' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1139:0: 'RBM.Ind.QBudgetBInst.dDriftAltLinQN_nonneg_instance' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1140:0: 'RBM.Ind.QBudgetBInst.dDriftAltQN_eq_lin_instance' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1141:0: 'RBM.Ind.QBudgetBInst.altBudgetExpQN_of_choice_instance' : [propext, Classical.choice, Quot.sound]
QBudgetB.lean:1142:0: 'RBM.Ind.QBudgetBInst.altBudgetNumQN_eventually_instance' : [propext, Classical.choice, Quot.sound]
```
Registry pre-check (DECISIONS §20): temp file `import RBM3D` / `import RBM3D.Induction.QBudgetB` / `#assert_rbm_axioms`, `lake env lean`; no `Axioms.lean` edit:
```
exit=0
axiom audit: 8223 theorems, 2670 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
```
Statement diff against the check file (`python3 stmtdiff.py`: whole §2 text with doc comments verbatim; each §3 body between `def T2286_X : Prop :=` and `theorem X : … := by`):
```
vocabulary (check file §2, whole text incl. doc comments) verbatim in QBudgetB.lean: True
dFlowQN_levelLin: statement text identical=True (whitespace-normalized True); doc comment identical=True
alt_hdriftLinQN: statement text identical=True (whitespace-normalized True); doc comment identical=True
dDriftAltLinQN_nonneg: statement text identical=True (whitespace-normalized True); doc comment identical=True
dDriftAltQN_eq_lin: statement text identical=True (whitespace-normalized True); doc comment identical=True
altBudgetExpQN_of_choice: statement text identical=True (whitespace-normalized True); doc comment identical=True
altBudgetNumQN_eventually: statement text identical=True (whitespace-normalized True); doc comment identical=True
```
Target statements, extracted from the file by script (`python3 extract.py <names>`, whitespace-normalized, wrapped at 205 columns):
```
theorem dFlowQN_levelLin : ∀ (d m : ℕ) (Λg KL C c : ℝ), 3 ≤ d → 0 < Λg → 0 < KL → 0 < C → 0 < c → ∀ (sz : Sizes d) (n : ℕ) (E u κ Γc Λc Φc Γ Φ₁ Φ₂ Φ₃ τ' ε' D' ν X τN : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W
    n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ), 0 < κ → |E| ≤ 2 - κ → 0 ≤ u → u < 1 → 0 < sz.lam n → sz.lam n ≤ Λg → (((sz.size n : ℕ) :
    ℝ))⁻¹ ≤ 1 - u → 1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W
    n : ℕ) : ℝ) ^ ε' → 1 ≤ ν → 1 ≤ X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) → ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ → (2 * (m : ℝ) + 5) *
    (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * C * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN → STMollifierProps (d := d) (sz.lam n) C c ϑ → H ∈ sz.GoodSetN n E u (m + 1 + 1) Γc Λc Φc τ' D' → H ∈ GoodLinN sz n E u (m
    + 1 + 1) Γ Φ₁ Φ₂ Φ₃ → (∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)), ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1)) → σ (Fin.last (m + 1)) = !σ 0 → ∀ a : Fin (m + 1 + 1) →
    Zd d (sz.L n), ‖dFlowQN sz n E u ϑ σ H a‖ ≤ dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ (qProxyCn d (m + 1) Λg KL C c) ε' D' τN X
theorem alt_hdriftLinQN : ∀ (d m : ℕ) (Λg KL : ℝ), 3 ≤ d → 0 < Λg → 0 < KL → ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (κ τ' ε' D' ν X τN :
    ℝ) (τ : PathΩ sz → ℕ), 0 < κ → |E n| ≤ 2 - κ → 0 < sz.lam n → sz.lam n ≤ Λg → 0 ≤ s n → s n ≤ v n → v n < 1 → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n → 1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1
    < D' → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → 1 ≤ ν → 1 ≤ X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m)
    ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) → ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ → (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * ((1 + 40 * ((d * (m + 1) : ℕ) :
    ℝ)) * 6 ^ (d * (m + 1))) * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN → σ (Fin.last (m + 1)) = !σ 0 → (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈ sz.GoodSetN n (E n) (gridTime s v Kg n j) (m
    + 1 + 1) (Γ n) (Λ n) (Φ n) τ' D' ∩ GoodLinN sz n (E n) (gridTime s v Kg n j) (m + 1 + 1) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) → (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1)
    → Zd d (sz.L n)), ‖sz.STLKM n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ' a'‖ ≤ ν * X * sz.Bctl n (gridTime s v Kg n j) ^ (m + 1)) → ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → ∀ b : Fin
    (m + 1 + 1) → Zd d (sz.L n), ‖dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω b‖ ≤ dDriftAltLinQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
    (qProxyCn d (m + 1) Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)) ε' D' τN X
theorem dDriftAltLinQN_nonneg : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ), |E| < 2 → u < 1 → 0 ≤ Φ₁ → 0 ≤ Φ₂ → 0 ≤ Φ₃ → 0 ≤ X → 0 ≤ dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂
    Φ₃ Cn ε' D' τN X
theorem dDriftAltQN_eq_lin : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ), dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X = dDriftAltLinQN sz n E u m Γ Φ (((m + 1 + 1 : ℕ) : ℝ) * Γ
    * Φ ^ 2) Φ Cn ε' D' τN X
theorem altBudgetExpQN_of_choice : ∀ (k : ℕ) (C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ : ℝ), 0 < C4 → 0 < Cn → 0 < 𝔠 → 0 < ε₀ → 0 < ε → ε ≤ 1 / 2 → C4 * ε ≤ ε₀ / 8 → Cn * ε ≤ ε₀ / 8 → 0 ≤ ε' → Cn * ε' ≤ ε₀
    / 8 → ε₁ ≤ ε₀ / 8 → εq ≤ ε₀ / 8 → τN ≤ ε₀ / 8 → C4 + Cn + (2 * (k : ℝ) + 1) / 𝔠 ≤ D' → 2 * Cn + 2 + 2 * C4 + (k : ℝ) + (4 * (k : ℝ) + 1) / 𝔠 ≤ D'' → (k : ℝ) ≤ D_Y → (k : ℝ) ≤ D_t → altBudgetExpQN k C4
    Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ (-(2 * (k : ℝ) + 1))
theorem altBudgetNumQN_eventually : ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (m : ℕ) (Λg κ' KL C c 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ : ℝ), 1 ≤ d → sz.SizeTendsto → sz.Bandwidth 𝔠 → 0 < κ' → (∀ᶠ n : ℕ in
    atTop, κ' ≤ (mE (E n)).im) → (∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg) → altBudgetExpQN (m + 1 + 1) (qProxy4C d (m + 1 + 1) Λg κ' KL) (qProxyCn d (m + 1) Λg KL C c) 𝔠 ε ε' τN D' D'' D_Y D_t εq
    ε₀ ε₁ ξ → ∀ᶠ n : ℕ in atTop, altBudgetNumQN sz E n m Λg κ' KL C c ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁
```
Compiled nonempty instances (namespace `RBM.Ind.QBudgetBInst`; statements extracted by the same script; all proved, axioms above). `σalt = ![true,false,true,false]`, `Cmol3 = (1+40·9)·6^9`, `C4i = qProxy4C 3 (1+1+1) 1 (24/25) 1`, `Cni = qProxyCn 3 (1+1) 1 1 1 (1/2)`, `εi = min (1/(8(C4i+Cni))) (1/2)`, `ε'i = 1/(8 Cni)`, `D'i = C4i+Cni+42`, `D''i = 2Cni+2+2C4i+3+78`:
```
theorem dFlowQN_levelLin_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) : ‖dFlowQN sz0 4 0 0 (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt H0 a‖ ≤ dDriftAltLinQN sz0 4 0 0 2 4 1 (((2 + 1 + 1
    : ℕ) : ℝ) * 4 * 1 ^ 2) 1 (qProxyCn 3 (2 + 1) 1 2 Cmol3 (1 / 2)) (1 / 5) 40 2 1
theorem alt_hdriftLinQN_instance : ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)), ‖dGridQN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4 (QopAlgebra_mollifier 3
    (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω b‖ ≤ dDriftAltLinQN sz0 4 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4 0) 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 (qProxyCn 3 (2 + 1)
    1 2 ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1))) (1 / 2)) (1 / 5) 40 2 1
theorem dDriftAltLinQN_nonneg_instance : 0 ≤ dDriftAltLinQN sz0 4 0 0 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 1 (1 / 5) 40 2 1
theorem dDriftAltQN_eq_lin_instance : dDriftAltQN sz0 4 0 0 2 4 1 1 (1 / 5) 40 2 1 = dDriftAltLinQN sz0 4 0 0 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 1 (1 / 5) 40 2 1
theorem altBudgetExpQN_of_choice_instance : altBudgetExpQN (1 + 1 + 1) C4i Cni (1 / 6) εi ε'i (1 / 8) D'i D''i 3 3 (1 / 8) 1 (1 / 8) (-(2 * ((1 + 1 + 1 : ℕ) : ℝ) + 1))
theorem altBudgetNumQN_eventually_instance : ∃ n : ℕ, altBudgetNumQN sz0 (fun _ => (1 / 2 : ℝ)) n 1 1 (24 / 25) 1 1 (1 / 2) εi ε'i (1 / 8) D'i D''i 3 3 (1 / 8) 1 (1 / 8)
```
Also compiled in the file (`example`, `QBudgetBInst`, line 1085): S3-18a's consumer step. From `h : altBudgetNumQN …`, `obtain ⟨ha1, …, he4⟩ := h`, then `exact budgetAltQN … (Pa := W^{C_nε'}(N^{ε₁}N^{ε₁})k + N^{τ_N}) Φd (b := W^{-D'+C_n}) (2W^{-D'}) (4W^{-D'}) … ha1 ha2 ha3 he0 he1 he2 he3 he4`, the other hypotheses of `budgetAltQN` kept as hypotheses of the example. This is the compiled form of the preflight (v) text diff.
Name-clash grep (`grep -rn -w -F <name> RBM3D --include=*.lean`, hits outside `QBudgetB.lean`; also `QBudgetB_` prefix: 0 hits):
```
altBudgetNumQN:0 altBudgetExpQN:0 dFlowQN_levelLin:0 alt_hdriftLinQN:0 dDriftAltLinQN_nonneg:0 dDriftAltQN_eq_lin:0 altBudgetExpQN_of_choice:0 altBudgetNumQN_eventually:0 QBudgetBInst:0 dFlowQN_levelLin_instance:0 alt_hdriftLinQN_instance:0 dDriftAltLinQN_nonneg_instance:0 dDriftAltQN_eq_lin_instance:0 altBudgetExpQN_of_choice_instance:0 altBudgetNumQN_eventually_instance:0
```
Scope: `git diff --name-only main...t/T2286` = `RBM3D/Induction/QBudgetB.lean` only. Ports: no file of RBM1D/RBM2D was read or copied in this stage (RBM2D HEAD, `git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h`: `9e0f275`; no diff-stat); the row lemmas are copies of RBM3D `Induction/NQEndLin.lean` (last change `cef761a`, itself a port of RBM2D `NonAltEnd.lean:54-121` at `c9a24cf`) and the instance helpers copies of private ones of `QLevelsB.lean` (`54b8610`) and `QBudgetA.lean` (`im_ge`, `:901`).

Narrative.
- All seven targets (0 vocabulary, 1-6) are in the file with exactly the pinned statements (script diff above); no hypothesis added or weakened, no frozen signature touched, no `set_option maxHeartbeats`.
- File layout: vocabulary `:46-105`; targets 1-4 `:107-283`; asymptotic helpers and the eight row lemmas `:286-704`; targets 5-6 `:706-793`; instances `:796-1123`.
- Target 1 (`dFlowQN_levelLin`): the proof of `dFlowQN_levelM` (`QLevelsB.lean:189-238`) with the block sup from `driftTensorN_norm_le_of_goodLin` (`NQLin.lean:732`) and `hY` the explicit premise. `GoodSetN` is used only through `hG.1` (Herm), `drift13_fastDecay` (Vb) and `goodSetN_LKM_far` (Dec); `goodSetN_LKM_le` is not used, and no clause is read at the level `(Γc, Λc, Φc)`.
- `C_n`: the private `QBudgetB_qProxyCn_eq` rewrites `qProxyCn` to the `Classical.choose` of `stQopNorm_holds` (`dite_eq_left_of_eq_true`, as `qProxyCn_pos`, `QProxy.lean:458-463`); `Classical.choose_spec` plus `generalize` then gives an opaque `Cn` with `0 < Cn` and the `(normQA)` bound.
- Target 2 (`alt_hdriftLinQN`): the proof of `alt_hdriftQN` (`QLevelsB.lean:268-283`) with target 1 at `C = (1+40d(m+1))6^{d(m+1)}`, `c = 1/2`; `(hτG ω j hjτ).1/.2` are the `GoodSetN`/`GoodLinN` memberships (the form of `mem_of_lt_nqLinExitTauN`), `hY` on `{j < τ}` is a separate premise.
- Target 3: `unfold dDriftAltLinQN dDriftLinN`, `(k:ℝ)-2 = m ≥ 0` (no hypothesis on `Γ`). Target 4: `unfold dDriftAltQN dDriftAltLinQN; rw [dDriftNonAltN_eq_lin]` closes the goal at `k := m+1+1` (no extra step).
- Target 5: with `q₁ = (2k+1)/𝔠`, `q₂ = (4k+1)/𝔠` (`𝔠 q₁ = 2k+1`, `𝔠 q₂ = 4k+1`) the five rows with a factor `𝔠` follow from `mul_le_mul_of_nonneg_left` and `linarith`; the other 15 conjuncts are closed by `positivity`/`mul_nonneg`/`linarith`. Slack as in (a).
- Target 6: `filter_upwards` over nine eventual facts. `QBudgetB_ev_ha1` is `nqEnd_ev_ha1`; `ha2` (two summands, each `≤ N^{ε₀}/24`, eventual `κ' ≤ Im m`), `ha3` (`c = a+b`), `he0` (constant `c₀`, divisor `q`), `QBudgetB_ev_he1b` (the `b` part of `he1`, `2k` in the exponent), `QBudgetB_ev_he2` (`r = k`, not `k-1`) are adapted from `nqEnd_ev_ha2/ha3/he1/he2`; `he4` (rows `he3`, `he4`) and the `he2` bound/final are verbatim copies. The `δD` part of `he1` is `QBudgetB_ev_he0` at `c₀ = 4`, `q = 24`; `he2` rewrites `-D''+C_Q = -(D''-(2C_n+2))` (`unfold qProxyCQ; ring`).
- Instances: targets 1-2 at the preflight data (`sz0`, `n = 4`, `m = 2`, `GoodLinN` at `(4,1,16,1)` by `goodSetN_subset_goodLinN`, `hY` by `goodSetN_LKM_le`, `4 ≤ W`); targets 3-4 at the same numbers; target 5 at the abstract `C₄, C_n > 0` (`qProxy4C_pos`, `qProxyCn_pos`); target 6 at `sz0` (`sz0_tendsto`, `sz0_bandwidth`, `E ≡ 1/2`, `24/25 ≤ Im m(1/2)`), `.exists` gives a concrete `n`. Every deterministic hypothesis is discharged.
- The registry scan (`scanPremises`, `Test/Axioms.lean`) needs no new line: the Prop `altBudgetExpQN` is a hypothesis of target 6 but is concluded by target 5, so it is not an unproved premise (pre-check exit 0 above); `altBudgetNumQN` is a conclusion only.

## (c) Verified Mathlib names
- `#check @name` on 82 names used in the file (script `names_check2.lean`, `lake env lean`, exit 0, 0 error lines). Names used: `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_nonneg`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_pos_of_pos`, `Real.one_le_rpow`, `Real.log_le_rpow_div`, `Real.log_nonneg`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `Real.sqrt_eq_rpow`, `Real.sqrt_le_iff`, `Real.le_sqrt'`, `tendsto_rpow_atTop`, `inv_anti₀`, `pow_le_pow_left₀`, `div_le_iff₀`, `le_div_iff₀`, `mul_one_div`, `mul_pow`, `norm_add₃_le`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `Real.exp_le_one_iff`, `div_nonpos_of_nonpos_of_nonneg`, `dite_eq_left_of_eq_true`, `Filter.Eventually.exists`, `Filter.Eventually.of_forall`, `Filter.Tendsto.eventually_ge_atTop`.
- Deprecated, not used: `dif_pos` (`#check` warning: "deprecated: Use `dite_eq_left` instead"); `dite_eq_left_of_eq_true` is used in its place (`QBudgetB_qProxyCn_eq`).

## (d) Open issues and paper-delta candidates
- `T2286a` (expected): the alternating drift level at `d ≥ 3` is `dDriftAltLinQN`, linear in the levels `Φ₁, Φ₂, Φ₃` of (D1')-(D3') and in the length-`(k-1)` control `X`, with `GoodSetN` read only through (Herm), (Vb), (Dec) and `hY` an explicit premise (the paper's `(y27kasdfg)`/`(A4)`/`(A5)` and `(normQA)` at the deterministic current-length level, DECISIONS §62 (4)).
- `T2286b`: none. No absorption row needs a hypothesis beyond `SizeTendsto`, `Bandwidth 𝔠`, `1 ≤ d`, `0 < κ'`, eventual `κ' ≤ Im m(E n)` and eventual `0 < g ≤ Λg` (target 6 has no `0 < 𝔠`; target 5 has it).
- Registry: expected diff empty, confirmed (pre-check exit 0). `altBudgetExpQN` is a Prop used as a hypothesis of a public theorem (target 6), proved by target 5; the ticket text says "no public theorem takes a new Prop as a hypothesis", which holds only for unproved Props.
- For S3-18a: after `dDriftAltLinQN_le_shape` at `Γ n`, `rw [hΓ]` turns `Γ n * Γ n` into `N^{ε₁} N^{ε₁}`, the `Pa` of `altBudgetNumQN` (the compiled example shows the exact passing). One `D'` for `δ0`, `δD` and `b`, one `(C, c)` for the drift and the QV `C_n` (ticket Open issue 2); `hY` at length `m+1` stays with S3-18a (Open issue 3).
- Observation: the preflight crossover of `ha3` (`4.2·10³`) differs from the ticket (`5·10³`), (a) already records it; no effect on a statement.
