Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct 13 05:14:18 UTC 2026
Notation: `𝔟 = Bctl = W^-d B_t0`; `X_c = tr(ǦE_c)`; `T^σ_ac = twTrP (G^σ) a c = T̂ + twMB` (T̂ = `twTr` or its conjugate; script 3, rows 1a/1a'); `MB = M^(B)`; `ω = Θ^(+,+)`, `κ_0 = 1`, `κ_1 = ω-1`; blue `σc=+`; red = `star` of blue at swapped blocks and flipped tail charge (`BAExp14bS2Fam_block`, `BAExp14b.lean:894`), so each blue bound is the red bound; block forms `BAExp14b.lean:673-880`.
Worktree HEAD `3d0b9578` = main HEAD; `cmp` of `BAExp14b`, `BAExp14aB`, `BAExp14a`, `LWExpTerm4`, `TwistPins`, `Test/Axioms`, `Defs/Sizes`, `FlowPins` (worktree vs main): identical. Scratch (`$SP/T2489/`): `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad`.
### (i) Exponent table (b-exponents; target `(1-t)⁻¹𝔟^(5/2)`; `η⁻¹ ≤ κ⁻¹(1-t)⁻¹` `BAExp14aB:1271`, constant `κ⁻¹` absorbed by `≺`; `1 ≤ (1-t)⁻¹`)
| input | value | constraint / use | slack |
|---|---|---|---|
| P1 `STLocalEntrygL` `Carrier:121` | `|Ǧ_xy| ≺ 𝔟^(1/2)`; `A = max|G_xx| ≺ 1` (`|M_xy| ≤ 1`, `BAExp14a:1035`) | `A` is a factor of exponent 0 in T3B, T3C-Ḡ(i); P3 | 0 |
| P2 `LWAvgLawgL` `LWGen:48` | `|X_c| ≺ 𝔟` | every family | 0 |
| P3 (derived; not a premise) | `|𝔼X_c| ≺ 𝔟^(3/2)`: `q=𝔼[XǦ] ≺ 𝔟·𝔟^(1/2)`, `|R| ≤ CM·ε₂` (`ε₂=𝔟^(3/2)`), `e=ωR` (`e=tM⁺e+R` `BAExp14aB:951`; `1-tM⁺` unit `BATheta_isUnit` `KBase:324`), `|e_c| ≤ S·CM·ε₂`, `S=S(k,Λ,κ)` from `BAExp14a_theta_l1` `BAExp14a:988` (row sums of `ω`, uniform in `t∈[0,1)`; window `g₀≤𝔡⁻¹` eventual) | no `(1-t)⁻¹` (the Neumann `BAExp14a_e_bound` `:978` has it); `q_prec` `:1377` is private and reads private `Dom_a` `:270` (`open private` or stem copy) | **0** (3/2 = 3/2) |
| P4 `STLmaxgL` `:87`, `STLKgL` `:80` | `|L²| ≺ 𝔟` (`√max L² ≺ 𝔟^(1/2)`); `|L²-K²| ≺ 𝔟²` | T3B; D1t(c), T3C-Ḡ(i) | 1/2 (D1t(c)), 1/2 (T3CG(i)), 0 (T3B) |
| `STKboundgL` / `STKwardgL` (`baKbound_holds` `KBound:245`, `baKward_holds` `:302`) | `|K²| ≲ 𝔟`; `Σ_x|K²_(b,x)| ≺ (W^dη)⁻¹` | D1t, T3C-Ḡ(ii)-(iv) | 0 in T3CG(ii),(iii) |
| TL1 `BATwistAvgLaw` `TwistPins:91` | `|T̂_(c1c2)| ≺ 𝔟`, all ordered pairs (red: conjugate) | T3B(a) `X·T̂·[W^d Σ|L³|]` = 1+1+1/2 | **0** in T3B; 1/2 elsewhere |
| TL2 `BATwistLoopLaw` `:95` | `|L̃-K̃| ≺ 𝔟^(3/2)`, all `σ,a,c1,c2` | D2t(c), T2a/b(a), T3CG(ii): `1+3/2` | **0** (exactly 3/2) |
| `twK_bound_holds` `TwistPins:692` (eventual) | (i) `|K̃| ≤ C𝔟` used; (ii) `Σ_a|K̃| ≤ C(W^dη)⁻¹` **not used** by any route below | D2t, T2, T3CG(iii) | 0 with P3 |
| `ℓ¹` rows | `Σ_c|MB_ac|, Σ_a|MB_ac| ≤ CM` (`BAMB_row_l1`, `BAMB_symm` `Ward:83`); `Σ_a|ω_ab| ≤ S` (`theta_col` `BAExp14a:1023`), `Σ_a|ω-1| ≤ S+1` (`Wsub_col` `:1142`) | all sums over `a1,c,c1,c2` | uniform in `t` |
| `twB0_ge_holds` `TwistFold2:520` (eventual, `sz.WO 𝔡`) | `W^-d ≤ (𝔡⁻²+1)𝔟` | only T2a/b(c),(d): `𝔼X·W^-d` = 3/2+1 (T3CG(iv) needs none: `W^d·W^-d = 1`, sup of `K`) | 0 |
| fold + Ward sum (switch (b)) | `Σ_{c1,c2}|MB||L̃| ≤ (CM/2)(Σ_c2 twSq(G^σ,c2,a)+Σ_c1 twSq(G,a,c1)) = CM·W^-2d Σ_{x∈[a]}Im G_xx/η ≤ CM A (W^dη)⁻¹` from `twFold_holds` `:352` (|L̃|² ≤ twSq·twSq, AM-GM) + fine Ward `BAExp14a_G_ward` `BAExp14a:1253` (row and column) + `ℓ¹` of `MB`; times `Σ_a1|κ| ≤ S+1` | T3CG(i): `W^d·𝔟·𝔟²·(W^dη)⁻¹ = η⁻¹𝔟³`; `twWard_holds` not needed (sum is over `c1,c2`, `a` fixed) | 1/2 (script 3, last 3 rows) |
Script 1 (every term of the 8 families; sums are exponents of `𝔟`, `η⁻¹` carried by Ward terms; red rows = blue rows):
```
$ python3 $SP/T2489/exps.py
term bound = b^(sum) [x eta^-1 if Ward]; eta^-1 <= kappa^-1 (1-t)^-1, 1 <= (1-t)^-1; slack = sum - 5/2
j=0 D1t       : sums 5/2 3 3                zero-slack: a:P3
j=1 D2t       : sums 5/2 3 5/2              zero-slack: a:P3 c:TL2
j=2 T2a       : sums 5/2 5/2 5/2 3          zero-slack: a:TL2 b:P3 c:P3+B0
j=3 T2b       : sums 5/2 5/2 5/2 3          zero-slack: a:TL2 b:P3 c:P3+B0
j=4 T3B(k=0)  : sums 5/2                    zero-slack: a:TL1+P4
j=5 T3B(k=1)  : sums 5/2                    zero-slack: a:TL1+P4
j=6 T3CG(k=0) : sums 3 3 5/2 5/2 5/2 3      zero-slack: ii:TL2+Kward iii:P3+Kward iv:P3
j=7 T3CG(k=1) : sums 3 3 5/2 5/2 5/2 3      zero-slack: ii:TL2+Kward iii:P3+Kward iv:P3
8 families x 2 charges = 16 rows; all terms >= 5/2: True | rows with a zero-slack term: 16
```
All 8×2 rows close; every row has a zero-slack term, and every zero-slack term is a P3, TL1 (with P4), TL2 or `W^-d≲𝔟`-with-P3 term at its exact exponent (no `STExpAvgAt`-type improved average, `T2418-prove:140`, is read: the band I1K/I41K terms that read `𝔼X ≺ 𝔟²` close here at `3/2+1`). S1 does not occur.
| row | value | constraint | slack |
|---|---|---|---|
| switch (a) | every term uses only P1-P4, TL1, TL2, `twK_bound` (i), `baKbound/baKward`, `ℓ¹` rows, `twB0_ge`, `twFold`, fine Ward, and P3 (derived above) | no estimate beyond the listed inputs | **does not hold** |
| switch (b) | fold-plus-Ward sum follows from `twFold_holds` + `BAExp14a_G_ward` + `MB` rows/columns (row above; numeric chain in script 3) | `≤ C(W^dη)⁻¹` | **does not hold**: stay `prover-hard` |
| unused premise | `STDecaygL` (premise 5): no route reads it (it stays in the def) | | |
| size (script 4) | file A (targets 1-3) central **1240**, high 1716; file B (targets 4-7) central **1156**, high 1600; total central **2396** > 1950 | stop line 2000 per file; reserve file C trigger 1800 | split applies; no file above 2000 at high, nor at the precedent-scaled A 1839, B 1715 (A above the 1800 trigger only there); no third row; L40-C3 projection 48 (ticket line 10, not recomputed) |
| registry (script 5) | six of the seven premises are registered (lines below); `LWAvgLawgL` is not | public theorems: target 1 (no pin binder), target 6 `∀ d, BAExp14bS2 d` (premises inside the def: `scanPremises` reads binders only) | **no line needed**. A public helper with an `LWAvgLawgL` binder would need `RBM.BA.LWAvgLawgL` in `owedProps` (`Test/Axioms.lean`, not writable here): such helpers stay `private` (`keep` in `scanPremises`, `Axioms:471-473`, needs the prefix `RBM`) |
### (ii) One nondegenerate instance and scripts
Instance: `d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `λ_n=(2(n+1))^-6`), `zSeq`, `flow_sz0` at `κ=1/2, ε=𝔡=1/10, 𝔠=1/6`, `t≡1/2 ≤ 2/3 ≤ T0` (`t0_sz0`), `n=0`: `L=4, W=32, N=2097152`. Seven premises of S2 stay hypotheses (other gates' pins); all deterministic hypotheses are numbers below. Script 2 reads the data from `Defs/Sizes.lean`, `BA/FlowPins.lean`, `Defs/Params.lean`, `Loop/GLoopFlow.lean` (asserts the text):
```
$ python3 $SP/T2489/inst.py
d=3>=3 | kappa=1/2 eps=1/10 dd=1/10 c=1/6 all >0 | BAFlow: flow_sz0 | t=1/2 in [0,T0]: T0>=2/3 (t0_sz0) -> True | Im m>=Im mS>=4/5 -> eta=(1-t)Im m >= 2/5
n=0: L=4 W=32 lam=1/64 N=2097152 | Bparam=2.030274 b=W^-d B=6.1959e-05 target (1-t)^-1 b^(5/2)=6.0435e-11
      U_n nonempty lam^2/L^d=3.81e-06<=1-t: True | eta^-1<=kappa^-1(1-t)^-1 (2.500<=4): True | W^-d<=(dd^-2+1)b (3.052e-05<=6.258e-03): True | WO window: True | floor N^-5/2<=target: True
n=1: L=8 W=1024 lam=1/4096 N=549755813888 | Bparam=2.003906 b=W^-d B=1.8663e-09 target (1-t)^-1 b^(5/2)=3.0094e-22
      U_n nonempty lam^2/L^d=1.16e-10<=1-t: True | eta^-1<=kappa^-1(1-t)^-1 (2.500<=4): True | W^-d<=(dd^-2+1)b (9.313e-10<=1.885e-07): True | WO window: True | floor N^-5/2<=target: True
n=5: L=24 W=248832 lam=1/2985984 N=212986666247081951232 | Bparam=2.000145 b=W^-d B=1.2982e-16 target (1-t)^-1 b^(5/2)=3.8405e-40
      U_n nonempty lam^2/L^d=8.11e-18<=1-t: True | eta^-1<=kappa^-1(1-t)^-1 (2.500<=4): True | W^-d<=(dd^-2+1)b (6.491e-17<=1.311e-14): True | WO window: True | floor N^-5/2<=target: True
```
Script 3 (relations of target 1 at random Hermitian data with the `TwistPins` convention `twShift`/`twTrP`/`twLoopX`/`twChg`, `TwistPins:51-67`; `M = MB⊗I`, `G=(H-z)⁻¹`; the last line is the t=0 limit computation for the external hypotheses TL1, TL2: `G=M`, `Ǧ=0`, `L̃ = K̃_0 = W^-d MB(σ0)_(c2 a) MB(σ1)_(a c1)`, `Θ_0 = 1`):
```
$ python3 $SP/T2489/rel.py
max abs error over 200 random (a,b,c,c1,c2), both charges (nb=5 blocks, w=W^d=4 offsets, random Hermitian H, MB complex random):
  1a twTrP G a c = twTr c a + MB c a                             2.73e-16
  1a' false charge = conj(twTr a c + MB a c)                     2.73e-16
  twTr_eq twTr c1 c2 = twTrP GM c2 c1                            0.00e+00
  1b slot-1 circle (check shape)                                 5.72e-17
  twCirc slot-2 (merged)                                         5.72e-17
  T2a: loop GM G^s b a c = L~ - W^-d MB_cb T^s_ab                5.87e-17
  T3C: loop G^s GM a c1 c2 = L~ - W^-d MB_ac1 T^s_ac2            5.72e-17
  control (slot-1 relation with the slot-2 pattern MB_ac1 T_{c1 a}) fails: 6.34e-02
  sigma=+: fold max(|L~|^2 - sq*sq)=-2.5e-04 (<=0) | sum|MB||L~|=1.0108 <= schur 3.7785 | Ward sum_c twSq=0.46678,0.46678 vs (W^d eta)^-1 W^-d sum ImG=0.46678
  sigma=-: fold max(|L~|^2 - sq*sq)=4.3e-19 (<=0) | sum|MB||L~|=0.9895 <= schur 3.7785 | Ward sum_c twSq=0.46678,0.46678 vs (W^d eta)^-1 W^-d sum ImG=0.46678
t=0 limit (G=M): TL2 max|L~ - K~_0| over 4 charge pairs x 125 blocks = 1.1e-16; TL1 max|twTr| = 0.0e+00
```
Target 1(b) has the index pattern of the check shape (`MB c₂ a`, `twTrP X₂ c₁ a`); the slot-2 pattern fails on slot 1 (control). S2 of the stop rules does not occur.
Script 4 (size; comparable = measured lines of the cited ranges, low/central/high = ×1.0/×1.3/×1.8 on every row, the multipliers of `T2418-prove.md:174`; an estimate, not a count):
```
$ python3 $SP/T2489/lines.py
  item                                                       comp  low cent high
A 1a  bridges twTrP = twTr + twMB, both charges                35   35   46   63
A 1b  slot-1 circle + T2a/T2b/T3C instantiations               63   63   82  113
A 1d  kernel sums, kappa_k and MB (l1, 2/3 indices)           164  164  213  295
A 1c  L3 Ward twin + fold-Ward sum (ward2 not read)           245  245  318  441
A 2   P3 sharp (q_prec copy, omega inversion)                 119  119  155  214
A 3   I1K twins D1t,D2t,T2a,T2b                               328  328  426  590
B 4   I23K twin T3B_k                                         290  290  377  522
B 5   I41K twin T3C-Gbar_k                                    383  383  498  689
B 6   binding S2: block forms, red charge, 8-tag union, fact  136  136  177  245
B 7   instances (target 6, TL1 by name, target 1, U_n)         80   80  104  144
file A: comparable 954  low 954  central 1240  high 1716
file B: comparable 889  low 889  central 1156  high 1600
total  : comparable 1843  low 1843  central 2396  high 3316   | pre-signed split if central > 1950: True
precedent T2418: 1a central 930+1145=2075, high 1245+1660=2905, landed 1307+1771=3078 -> landed/central 1.48; scaled central A 1839, B 1715 (stop line 2000, reserve trigger 1800)
```
Cut: file A = 1(a)-(d), 2, 3; file B = 4-7 (B imports A). `ward2` of band §3 is read by no route (kernel Ward is `baKward_holds`); the L3 twin (`LWExpTerm4:415-575`) feeds T3B only, so 1(c) could sit in B if A passes 1800 at 1b.
Script 5 (registry, `Test/Axioms.lean`; lists `owedProps` 102-246 contain the six lines):
```
$ bash $SP/T2489/reg.sh
lists in RBM3D/Test/Axioms.lean: 91:def borrowedProps  102:def owedProps  247:def structuralProps  
STLocalEntrygL: registry line [144 ] def RBM3D/Chain/Carrier.lean:121
STLmaxgL: registry line [133 ] def RBM3D/Chain/Carrier.lean:87
STLKgL: registry line [135 ] def RBM3D/Chain/Carrier.lean:80
STDecaygL: registry line [217 ] def RBM3D/Chain/Carrier.lean:94
BATwistAvgLaw: registry line [192 ] def RBM3D/BA/TwistPins.lean:91
BATwistLoopLaw: registry line [193 ] def RBM3D/BA/TwistPins.lean:95
LWAvgLawgL: registry line [] def RBM3D/Chain/LWGen.lean:48
LWAvgLawgL occurrences outside binders/defs:        6 (def LWGen:48, iff LWGen:136, one unfold, one have, two def-bodies; none concludes it)
```
Verdicts. Targets 1, 2, 3, 4, 5, 6, 7: **PASS** (all hypotheses hold at the instance; all 8×2 rows close; S1, S2 and both switch conditions absent). Overall **PASS**, role `prover-hard`, pre-signed split applies (L4b2a = file A, L4b2b = file B on `t/T2489b`; third row not needed). Findings for the 1b: (1) the ticket's target 1(c) names `ward2` and `twWard`; the routes read neither (L3 twin + `twFold` + fine Ward instead); (2) ticket target 5(iv) cites `twB0_ge_holds`; the route above needs it only in T2a/T2b; (3) P3 needs the private `BAExp14a_Dom_a` (`open private` or +18 lines, counted).
## (b) Script output — stage 1b (`prover-hard`), row **L4b2a = file A (targets 1-3)**; written Tue Oct 13 06:07:26 UTC 2026
**L4b2a delivered**: `RBM3D/Graph/BAExp14b2.lean` on `t/T2489` (HEAD `2f825d5e`, base `3d0b9578`): targets 1 (a)-(d), 2, 3 with instances. Targets 4-7 = **L4b2b**, not started; it runs later on `t/T2489b` (pre-signed split). Switch conditions (a), (b) were absent in (a) and no 1b step needed an input beyond the listed ones (census).
```
$ lake build RBM3D.Graph.BAExp14b2 2>&1 | tail -2
Build completed successfully (4025 jobs).
$ lake build   (full library, `#assert_rbm_axioms` last in RBM3D.lean; import line added after BAAnpLift)
Build completed successfully (4347 jobs).
exit=0
$ wc -l RBM3D/Graph/BAExp14b2.lean; git log (section commits)
1794
  f5df8a68      302 lines
  09ac8d0d     1383 lines
  d31a6034     1780 lines
  5a1e7dae     1780 lines
  2f825d5e     1794 lines
$ grep -nE "sorry|admit|native_decide|^axiom|inductive|^structure" RBM3D/Graph/BAExp14b2.lean
(no hit)
```
Axioms (`#print axioms`, scratch file with `open private` for the private names; the full build ran `#assert_rbm_axioms`): all 19 print std3: twTrP_G, twTrP_G_false, twTrP_chg, twCirc1, Tsplit, L3_ward, fold_ward, wsum_c2, wsum_c1, kap_col, close, closeA, closeB, private P3, private D1t, private D2t, private T2a, private T2b, private I1K; std3 = `[propext, Classical.choice, Quot.sound]`.
Target statements, extracted by script (1 (a), (b) public; 2, 3 private: `LWAvgLawgL` is not registered):
```
-- BAExp14b2.lean:47
theorem BAExp14b2_twTrP_G (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a c : Zd d (sz.L n))
    (hm : 0 < ((baFMz sz z).m n).im) :
    twTrP n ((baFMz sz z).G n t ω) a c = twTr (baFMz sz z) n t ω c a + twMB (baFMz sz z) n c a
-- BAExp14b2.lean:84
theorem BAExp14b2_twCirc1 (sz : Sizes d) (n : ℕ) (X₁ X₂ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hM : ∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n (fun x y => X₁ x y - M x y) X₂ a c₁ c₂ =
      twLoopX n X₁ X₂ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB c₂ a * twTrP n X₂ c₁ a
-- BAExp14b2.lean:264
private theorem BAExp14b2_P3 (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
      (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ))
-- BAExp14b2.lean:1396
private theorem BAExp14b2_I1K (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (j : Fin 8) (hj : (j : ℕ) < 4) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω j p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
```
Target 1 (c), (d), public, no pin binder (statement lines): `BAExp14b2_L3_ward` :1473 (`W^d Σ_a |𝓛^(3)_(+,+,σ),(a,b,c)| ≤ η⁻¹ A Q^{1/2}`), `_fold_ward` :1549 (`Σ_{c₁c₂} |MB||L̃(G^σ,G;a,c₁,c₂)| ≤ C_M A (W^dη)⁻¹`), `_wsum_c2` :1632, `_wsum_c1` :1650 (`Σ_{a₁c₁c₂} |κ||MB| h ≤ S C_M Σ h`), `_kap_col` :1381 (`Σ_{a₁} |κ_k(a₁,c)| ≤ S`), `_Tsplit` :788.
Instances (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`, `n = 0`: `L = 4`, `W = 32`; blocks `0, e₀, e₁` pairwise distinct, :1706). 1 (a) :1684, 1 (b) :1697, P3 :1722, I1K :1730:
```
example (ω : sz0.SeqΩ) :
    twTrP 0 ((baFMz sz0 zSeq).G 0 (1 / 2) ω) 0 (Pi.single 0 1) =
      twTr (baFMz sz0 zSeq) 0 (1 / 2) ω (Pi.single 0 1) 0 + twMB (baFMz sz0 zSeq) 0 (Pi.single 0 1) 0 :=
  BAExp14b2_twTrP_G sz0 zSeq 0 (1 / 2) ω 0 (Pi.single 0 1) BAExp14b2_hr0.1.1
example (ω : sz0.SeqΩ) :
    twLoopX 0 (fun x y => (baFMz sz0 zSeq).G 0 (1 / 2) ω x y - (baFMz sz0 zSeq).M 0 x y) (twChg ((baFMz sz0 zSeq).G 0 (1 / 2) ω) false)
        0 (Pi.single 0 1) (Pi.single 1 1) =
      twLoopX 0 ((baFMz sz0 zSeq).G 0 (1 / 2) ω) (twChg ((baFMz sz0 zSeq).G 0 (1 / 2) ω) false) 0 (Pi.single 0 1) (Pi.single 1 1) -
        (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * BAExp14b_MB sz0 zSeq 0 (Pi.single 1 1) 0 *
          twTrP 0 (twChg ((baFMz sz0 zSeq).G 0 (1 / 2) ω) false) (Pi.single 0 1) 0 :=
  BAExp14b2_twCirc1 sz0 0 _ _ _ _ (BAExp14b2_M_tie 0 BAExp14b2_hr0.1.1) 0 (Pi.single 0 1) (Pi.single 1 1)

example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n)) (fun n c _ => ‖∫ ω, BAExp14a_X sz0 zSeq n (1 / 2) ω c ∂μ0‖)
      (fun n _ _ => (sz0.Bctl n (1 / 2)) ^ (3 / 2 : ℝ)) :=
  BAExp14b2_P3 (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num) flow_sz0 (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hE hA
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hT1 : BATwistAvgLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (j : Fin 8) (hj : (j : ℕ) < 4) :
    PrecL sz0 μ0 (U := fun n => Bool × Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz0 zSeq n (1 / 2) ω j p.1 p.2.1 p.2.2 ∂μ0‖)
      (fun n _ _ => (1 - 1 / 2 : ℝ)⁻¹ * (sz0.Bctl n (1 / 2)) ^ (5 / 2 : ℝ)) :=
  BAExp14b2_I1K (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num) flow_sz0 (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hE hA hK hT1 hT2 j hj
```
Also compiled: false charge :1692, `Tsplit` :1689, I1K with TL1 by name (`baTwistAvgProd_holds 3`) :1743, `U` nonempty :1739, `fold_ward` :1767, `L3_ward` :1774, `wsum_c2/c1` :1781, :1785. Only the pins `STLocalEntrygL, LWAvgLawgL, STLKgL, BATwistAvgLaw, BATwistLoopLaw` stay hypotheses; `STLmaxgL`, `STDecaygL` are not read in file A.
```
$ lake env lean docs/tickets/checks/T2489-check.lean ; echo exit=$?
exit=0
$ scratch (not committed): shapes 1(a), 1(b) copied from the check by script, `example : Chk1a := @BAExp14b2_twTrP_G`, `example : Chk1b := @BAExp14b2_twCirc1`
exit=0
$ for each of the refs (heads+remotes) except t/T2489: git grep -l "BAExp14b2\|baExp14bS2_holds" <ref> -- RBM3D RBM3D.lean
refs scanned: 504, refs with a hit: 0
$ git diff --stat main...t/T2489
 RBM3D.lean                 |    1 +
 RBM3D/Graph/BAExp14b2.lean | 1794 ++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1795 insertions(+)
$ grep -nE "sz\.lam|withLam|gK" RBM3D/Graph/BAExp14b2.lean
(no hit)
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus' RBM3D/Graph/BAExp14b2.lean
(no hit)
```
Script over the file: public declarations with a pin in the signature: none; private with pins: `P3, base, tl2, D1t, D2t, T2a, T2b, I1K` (49 public, 10 private declarations).
Census (merged declarations read; `file:line`; all public unless `(P)` = private, reached by `open private` at the top of the file; stem copies: none; ports from `../RBM1D`, `../RBM2D`: none, those trees were not touched):
- `Graph/BAExp14a.lean`: `BAExp14a_Dom` 260 (`.refl .mul .add .of_le .mono .const_mul .index` 267-293), `det_iff` 58, `prec_of_bad` 99, `prec_of_le_ev` 109, `prec_mono` 116, `prec_int` 299, `M_row_eq` 1053, `G_ward` 1253, `eta_pos` 1266, `G_le` 1273.
- `Graph/BAExp14aB.lean`: `X` 57, `Wk` 61, `Facts` 391, `a` 216, `le_a` 224, `a_nonneg` 233, `facts_of_flow` 633, `GM_le` 814, `X_le` 821, `int_X` 852, `e` 867, `q` 871, `MB` 908, `R` 912, `e_eq` 951, `ev` 1253, `t_lt_one` 1267, `floor` 1280; (P) `Dom_a` 270, `q_prec` 1377.
- `Graph/BAExp14b.lean` (L4b1): `pt` 392, `sum_idx` 407, `sum_blk` 413, `MB` 427, `om` 431, `kap` 435, `M_pt` 439, `Wk_pt_true` 464, `L2_eq` 493, `L3_eq` 503, `twTrP_pt` 525, `twLoopX_pt` 533, `FS2` 124, `BS2` 856, `FS2_block` 879.
- TL0 `BA/TwistPins.lean`: `twBlk` 47, `twTr` 55, `twChg` 61, `twTrP` 63, `twLoopX` 66, `twTr_eq` 68, `twL2'` 70, `twMB` 73, `twK` 76, `twMB_ba` 80, `BATwistAvgLaw` 91, `BATwistLoopLaw` 95, `twSq` 100, `twFold_holds` 352, `twCirc_holds` 467, `twK_bound_holds` 692; `BA/TwistFold2.lean` `twB0_ge_holds` 520; `BA/TwistAvgB.lean` `baTwistAvgProd_holds` 451 (instance only). K12 `BA/KBound.lean` `baKbound_holds` 245. Also `BAMfine_eq` (`GreenSchur` 93), `BAMB_symm` (`Ward` 83), `BATheta_isUnit` 324, `BATheta_isSymm` 371 (`KBase`), `PrecL` (`Carrier` 51).
- Band templates read, not imported (`Graph/LWExpTerm4.lean`): `lwExpTerm4_vertex` 429 (twin `BAExp14b2_vertex`), `lwExpTerm4_L3` 488 (twin `_L3_ward`), `_wsum3K` 963, `_wsum2K` 948 (twins `_wsum_c2`, `_wsum_c1`), `_I1K_n` 868, `lwExpI1K_holds` 903 (route). Not read: `ward2` 391, `kward` 746, `twWard_holds`.

Hypothesis and UBA-C1 table (grep above: file A has no `sz.lam`, `withLam`, `gK`, no comparison text R1, no new `inductive`):
| declaration | pins in binders | other hypotheses | coupling `g₀` read |
|---|---|---|---|
| `twTrP_G`, `_G_false`, `_chg`, `Tsplit` | none | `0 < Im m` | `BAMfine_eq` inside `twMB` |
| `twCirc1` | none | block tie `hM` | none |
| `L3_ward`, `fold_ward`, `wsum_c1/c2`, `kap_col`, `close{,A,B}` | none | pathwise or `Dom` data (`A`, `Q`, `C_M`, `S` as parameters) | none |
| `P3` | `STLocalEntrygL`, `LWAvgLawgL` | `BAFlow`, `t ∈ [0, T0]` | only inside merged `facts_of_flow`, `q_prec` |
| `D1t` | + `STLKgL`, `BATwistAvgLaw` | same | + `baKbound_holds` |
| `D2t`, `T2a`, `T2b` | `STLocalEntrygL`, `LWAvgLawgL`, `BATwistAvgLaw`, `BATwistLoopLaw` | same | + `twK_bound_holds`, `twB0_ge_holds` (T2a, T2b) |
| `I1K` (`j < 4`) | the five above | same | as above |
Constants: `C_M, S` from `facts_of_flow` (depend on `(k, 𝔡, κ)`), `C` from `twK_bound_holds` (chosen before `sz, z`); no smallness of `g`, no `M = mI` (C1).

Narrative.
- Route (all in file A): `BAExp14b2_close` writes `Φ = Σ_{a₁,c} u X_{a₁} (Y_det + Y_rnd)` with deterministic weights `u` (`ℓ¹ ≤ U₁`), pays `Σ u Y_det X` with the sharp average (`‖𝔼X‖ ≺ 𝔟^{3/2}`, `BAExp14b2_P3`) and `Σ u X Y_rnd` pathwise with `a ≺ 𝔟` through `BAExp14a_prec_int`; `closeA` (`D1t`, `D2t`) takes `T̂ + B` times `K + Δ`, `closeB` (`T2a`, `T2b`) takes `(K + Δ) - ρ (T̂ + B)`.
- `D1t`: `Y_det = B K²`, `Y_rnd = T̂ K² + (T̂ + B)(𝓛² - 𝒦²)` (`STKboundgL` k=2, `STLKgL` k=2, TL1). `D2t`: `K̃`, TL2. `T2a`: slot-1 circle (`BAExp14b2_twCirc1`, target 1 (b)) then `L̃(Ǧ, G^σ) = L̃ - W^{-d} MB T^σ`; `T2b`: `twCirc_holds` (slot 2). `W^{-d} ≤ (𝔡⁻² + 1) 𝔟` from `twB0_ge_holds`.
- Zero-slack lines of (a) are the ones the arithmetic hits with equality (`BAExp14b2_poly`: `s = 𝔟^{1/2}`, `𝔟 = s²`, `𝔟^{3/2} = s³`, `𝔟^{5/2} = s⁵`, monomials `s⁵..s⁸` against `ω₁ s⁵`, `ω₁ = (1 - t)⁻¹ ≥ 1`): P3 times `K²` or `K̃` (`3/2 + 1`), TL2 times `X` (`3/2 + 1`).
- P3 is not the Neumann `BAExp14a_e_bound` (which carries `(1 - t)⁻¹`): `e = ω R` with row sums `Σ_b |ω_{cb}| ≤ S + 1` (symmetry of `ω`, columns of `ω - 1` from `Facts.hWk`), `|R| ≤ C_M ε₂` (`BAExp14b2_R_le`), `ε₂ = max |q| ≺ 𝔟^{3/2}` (`BAExp14a_q_prec`).
- Integrability needs no continuity of the loops: `BAExp14b2_norm_int_add` (triangle inequality when one summand is integrable) and `int_X` only; envelopes are `η⁻¹ ≤ N²` (`BAExp14b2_L2_le`, `_Lt_le`, `_tw_le`).
- The pins `STLmaxgL`, `STDecaygL` are not read; `twWard_holds` and `ward2` are not read (a, finding 1); `twK_bound` (ii) is not read.
- Section commits (`wc -l`): `f5df8a68` 302, `09ac8d0d` 1383, `d31a6034` 1780, `5a1e7dae` 1780, `2f825d5e` 1794; stop line 2000 not reached.

## (c) Verified Mathlib names (`#check` in a scratch file, 0 errors)
`Finset.sum_mul_sq_le_sq_mul_sq`, `sq_sum_le_card_mul_sum_sq`, `Finset.sum_mul_sum`, `Finset.exists_mem_eq_sup'`, `Finset.le_sup'`, `Finset.sup'_le`, `Matrix.mulVec_mulVec`, `Matrix.sub_mulVec`, `Matrix.smul_mulVec`, `Matrix.one_mulVec`, `Ring.inverse_mul_cancel`, `MeasureTheory.integral_add`, `integral_undef`, `integrable_finsetSum`, `integral_finsetSum`, `integral_const_mul`, `Real.le_sqrt_of_sq_le`, `le_mul_inv_iff₀`, `inv_le_iff_one_le_mul₀`, `one_le_inv₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `sq_le_sq₀`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_pos_of_pos`.
Deprecated (warning, not used): `MeasureTheory.integrable_finset_sum`, `integral_finset_sum` (use `...finsetSum`), `if_pos`. `import Mathlib` has no olean in this tree (import the project modules instead).

## (d) Open issues and paper-delta candidates
- Size: file A landed 1794 lines against (a) script 4 central 1240 / high 1716 (ratio 1.45 to the central); file B at the same ratio from its central 1156 is about 1680, near the 1800 reserve-file trigger (L4b2b decision).
- Hand-over to L4b2b: `open private BAExp14b2_P3 BAExp14b2_base BAExp14b2_tl2 BAExp14b2_I1K from RBM3D.Graph.BAExp14b2` (checked from a downstream scratch file); public API `BAExp14b2_close{,A,B}`, `_Dom_sup`, `_det_ev`, `_L3_ward` (for `T3B`, `Q` from the `STLmaxgL` supremum), `_fold_ward` (for `T3C-Ḡ` (i), with `twCirc_holds` slot 2 and `baKward_holds`), `_wsum_c1/c2`, `_kap_col`, `_Tsplit`, `_Th`, `_Bs`, `_poly(K)`, `_s`. Left to L4b2b: `T3B`, `T3C-Ḡ`, the S2 assembly (red charge `star`, the eight tags, restriction of `I1K` from `Bool × Zd × Zd` to the subtype `U`), the instances of target 6.
- `main` has moved since the base `3d0b9578` (`git log 3d0b9578..main`: `e0043e75` T2482, `e6c26ca4` T2484, `7be99aae` T2486 merged; they add six import lines after `BAAnpLift` in `RBM3D.lean`, where my branch adds one); my full `lake build` is on base plus my two files; the hub merges the import line by union. None of the modules I import changed on `main`.
- Paper-delta candidates: **T2489a** (route, no statement difference): BA has no improved average, so the band terms that read `𝔼X ≺ 𝔟²` close with the derived P3 `𝔼X ≺ 𝔟^{3/2}` at exact exponent `3/2 + 1`, and TL2 at `3/2 + 1`; P3 is a Lean lemma, not a paper statement. **T2489b** (statement shape): `I1K` is stated over `Bool × Zd × Zd` (full index), S2 over its subtype `λ²/L^d ≤ 1 - t`; the restriction is a precomposition.
