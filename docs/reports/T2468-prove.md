Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 19:05:37 UTC 2026

Setting (read from `RBM3D/BA/GreenCore.lean:1616-1654`, `Step1.lean:191-260`): the pin `BAGbEXPij'` gives `c = c(κ',ε',𝔡)` before `(𝔠, sz, z)`; at a member `z'`, time `u ∈ [s,t]`, `ε₀ = c'` (`s1_F5`), `D = d/2`, `Φ_n ≡ φ_n := Bctl_n(s_n)^{7/15}`, `Ψ_n := φ_n`, from `GreenCore_loopPrem` it gives `1_Ω ‖GM_xy‖ ≺ decayRHS`. Step 1 then needs `‖GM_ij‖² ≤ K Nτ² φ²`.

### (i) Exponent table (instance: d=3, sz0, κ=1/2, ε=𝔡=1/10, 𝔠=1/6, 𝔠d=1/100, s≡1/2, t≡2/3; values from the script below)

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| `τ = ε/2`, `c₀ = min(2𝔠𝔡, τ)`, `c' = c₀/8` (`s1_F5`, `Step1Setup:438`) | 1/20, 1/30, 1/240 | `c' > 0`; `2 B^{1/4} ≤ W^{-c'}` eventually | n=0: 0.1774 ≤ 0.9857; n=8: 4.67e-5 ≤ 0.9416 |
| Φ exponent 7/15 (`Φ² = B^{14/15}`) | 7/15 | `0 < Φ ≤ W^{-c'}` eventually: `B^{7/15} ≤ B^{1/4} ≤ 2B^{1/4} ≤ W^{-c'}` (needs `B ≤ 1`, `s1_B_le_one :316`; `s1_B_pos :278`) | 7/15 − 1/4 = 13/60; n=0: 1.087e-2 ≤ 0.9857 |
| Ψ := Φ lower window | `W^{-d/2} ≤ Φ` | squares to `(W^d)⁻¹ ≤ B^{14/15}` = `s1_F8` (`:504`) | n=0: 5.52e-3 ≤ 1.087e-2; n=8: 3.85e-10 ≤ 2.26e-9 |
| `D = d/2` in `W^{-D}` | 3/2 | `W^{-D} ≤ φ` (same as previous row); `D > 0` | exponent slack 0 (exact: `(W^{-d/2})² = W^{-d}`); value slack n=0 factor 1.97 |
| `con_st_ind` exponent `𝔠d` (`s1_ratio_ev :340`) | 1/100 | `B(1-s)/(1-u) ≤ B^{14/15}`: needs `𝔠d ≤ 1/15` | 1/15 − 1/100 = 17/300; n=0: 9.29e-5 ≤ 1.18e-4 |
| `STConStInd 𝔠d s t` (eventual hypothesis of `S1Std`) | `B(2/3)^{1/100} ≤ 2/3` | holds iff `n ≥ 8` for sz0 | n=8: 0.6554 ≤ 0.6667 (thin) |
| `(eq:WO)` | `W^{-7/5} ≤ λ ≤ 10` | `S1Std.hWO` | holds all n (script, WO line) |
| loop input `k = 2` (event `omegaC(1+κm⁻¹)`) | RHS `ratio·B ≤ B^{14/15}` | `indMax(W^{-c'}) ≤ omegaC(1+κm⁻¹)`: needs `W^{-c'} ≤ 1` (`c' > 0`, `W ≥ 1`, all n) and `‖M_xy‖ ≤ (Im m)⁻¹ ≤ κm⁻¹` (`baM_entry_le`, `Step1Boot:322`) | exact for every n |
| `S = expC(d-2, c/d)` (`RadialSum:271`) | `d=3`: 4.98e5 (c=1), 4.98e9 (c=1/10), 4.98e13 (c=1/100) | `Σ_{a'} e^{-c‖a'-a‖_∞} ≤ Σ e^{-(c/d)‖a'-a‖_1} ≤ S` (`zdistD_le_mul_zdistInf` `Defs/Sizes:122`, `zdistD_neg` `Defs/Lattice:103`, `BAsum_exp_decay_le` `Prop5Short:251`, guard `2 ≤ d`) | depends on `(d,c)` only |
| `S ≥ 64` | `expC(k,·) ≥ 2^{k+2}·2·2^{k+3}·1 = 2^{2k+6} ≥ 64` for `k = d-2 ≥ 0` | `S² ≥ 2` so that `(S²+2)² ≤ 3S⁴+4` | S² ≥ 4096 vs 2 |
| `K = 3S⁴+4` | 1.84e23 (c=1), 1.84e39 (c=1/10) | `K ≥ (S²+2)²` (off-diagonal), `K ≥ 1` (diagonal) | script: both True |
| absorption `√K ≤ 2·3^d N^{τ'/2}` | `√K/(2·3^d) = 7.95e9` (c=1) | needed only for the *conclusion* `≺ 2·3^d φ` (verbatim), eventual in `n` for each fixed `(c, τ')` | see (ii) note |
| guard | `2 ≤ d` | `BAsum_exp_decay_le`, `baGbEXPij'_holds`, `baGbEXPii_holds`, `baGbEXPav_holds` | d=3: slack 1 |

**(iii) Bookkeeping, target 2 (a)** (premises of `BAGbEXPij'` at member `z'`, time `u ∈ [s,t]`):

| Premise | Merged fact | Event / eventual index |
|---|---|---|
| `BAFlow sz κ'' ε'' 𝔠 𝔡 z''`, `z'' = z'` for `n ≥ n₀`, `u ≤ t₀(z'')` | `Boot_member` `Step1Boot:232` (`BAFlowMember_holds` `Step1Fam:624`, `BAFamZ_mono :173`, `BAFamZ_horizon :179`) | `n₀` of `BAFlowMember`; transfer back by `PrecL_congr :185` + `Boot_baFMz_eqAt :224` (L, G, M at index n depend on `z n` only) |
| `0 ≤ u`, `u ≤ t`, `c = c(κ'',ε'',𝔡)` fixed before `(𝔠, sz, z)` | `hs0`, `hu` of `S1Std`; order of `BAGbEXPij'` | none |
| `ε₀ = c' > 0` | `s1_F5` (`Step1Setup:438`) | none |
| `D = d/2 > 0` | `d ≥ 2` | none |
| `∀ᶠ n, ∀ a b, 0 < Φ ∧ Φ ≤ W^{-c'}` | `s1_B_pos :278`; `s1_F5`, `s1_B_le_one :316` | n ≥ 0 (positivity), n ≥ 0 at the instance for the upper bound |
| `∀ᶠ n, W^{-d/2} ≤ Ψ` | `s1_F8 :504` (square root of `(W^d)⁻¹ ≤ B^{14/15}`) | n ≥ 0 at the instance |
| `∀ᶠ n, Ψ ≤ W^{-c'}` | same as Φ row (`Ψ = Φ`) | n ≥ 0 at the instance |
| `GreenCore_loopPrem sz z' u c' Φ` | `hLI u hu 2` (from `baBoot_LI` `Step1Boot:577`, `κm = κ` via `BAFamZ_im_m_ge`) `→ StochDomAt.precomp_param` (`Defs/StochDomAt:335`, along `p ↦ (![false,true], ![p.1,p.2])`) `→ of_le_left :347` (`indMax ≤ omegaC(1+κm⁻¹)` for all n, see table) `→ of_subset :325` (`ratio·B ≤ B^{14/15}` from `s1_ratio_ev :340`, with `(B^{7/15})² = B^{14/15}`) | `s1_ratio_ev`: eventual, from `STConStInd` (n ≥ 8 at the instance) |

Verdict (iii): every premise has a merged source; no `n`-dependent constant enters; no premise beyond `S1Std`, `κm ≤ Im m`, `hLI`.

**(iv) `step1Prime_wl_det`.** Twin of `flowFM_wl_det` (`Step1Setup:113`): hypotheses unchanged except the off-diagonal one, which becomes `indMax(W^{-c'}) ‖GM_xy‖ ≤ Nτ · GreenCore_decayRHS d L W c (d/2) (fun _ _ => φ) φ ([x],[y])` (`x ≠ y`); extra data `0 < φ`, `g = φ²`, `W^{-d/2} ≤ φ`, `c > 0`. Proof of the bound: `decayRHS ≤ φ S² + φ·e^{-c‖a-b‖} + W^{-d/2} ≤ (S²+2) φ` (each exponential ≤ 1; the double sum factorises), so `‖GM_xy‖² ≤ (S²+2)² Nτ² φ² ≤ (3S⁴+4) Nτ² g`; diagonal: `‖GM_ii‖² ≤ Nτ · STmaxLoop2g ≤ Nτ²g ≤ K Nτ² g` (unchanged, `Step1Setup:152`). Conclusion `‖GM_ij‖² ≤ (3S⁴+4) Nτ² g`, `S = expC(d-2, c/d)`, depends on `(d, c)` only (`c = c(κ',ε',𝔡)`), independent of `n`. Passage to the verbatim `≺ 2·3^d B^{7/15}` of `baS1_wl_seq`: apply the events at `τ'/2`, then `√K · N^{τ'/2} ≤ 2·3^d · N^{τ'}` eventually by `s1_N_pow_ev :350` (`√K/(2·3^d) ≤ N^{τ'/2}`).

**(v)** n/a (stage 1a is mathematics only; no name or copy-plan checks). Mathematical content: the merged `baS1_wl_seq/forb/boot/weakPT/loopPT` use `hGij` only through `baS1_wl_seq` (`Step1.lean:209`); `forb`, `boot`, `weakPT`, `loopPT` pass it on (`:316, 438, 479, 517`). So the primed five differ from the merged five in that hypothesis alone (plus the binder `c`, `0 < c`). **(vi)** n/a, size estimates excluded from (a). **(vii)** n/a, no mathematics.

**Targets 1, 4, 5, 6 (math only).** 1: order `∃ κ' ε'` (BAFlowMember) before `∃ c` (`BAGbEXPij'` at `(κ',ε',𝔡)`) before `∀ 𝔠 sz z` matches the pin; the loop premise and conclusion transfer `z'' ↔ z'` because they read `indMax, L, GM` at index `n` only. 4: `baBootstrap'_holds` threads `hGij` into `baS1_loopPT/weakPT`; replace by target 1 with its `c`. 5: `BAFlowMember_holds`, `baGbEXPii_holds`, `baGbEXPij'_holds` (`GreenOff:1289`) discharge target 4 for `2 ≤ d`. 6: `BAGiiGEX` and `STGiiGEXgL (baFMz sz z)` have the same body (`FlowFM.indMax` and `STindMaxg` both `if ∀ x y, ‖GM‖ ≤ A then 1 else 0`; `Step1Boot:54, 79`, `Step2Gen:742`); `BAGavLGEX` is `STGavLGEXgL` with the two premises of `STInitialGT2gL` (`Carrier:140-146`) curried (`Step1Boot:97`, `Step2Gen:768`). `STGijGEXgL` not produced.

### (ii) One concrete nondegenerate instance

`d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `λ_n=(2(n+1))^{-6}`; `Defs/Sizes.lean:260-263`), `BAFlow sz0 (1/2)(1/10)(1/6)(1/10) zSeq` (`flow_sz0`, `FlowPins:1214`), `t₀ ≥ 2/3` (`t0_sz0 :1227`), `c₁ = 1/3`, `s ≡ 1/2`, `t ≡ 2/3`, `u ∈ {1/2, 2/3}`, `𝔠d = 1/100`, `ε₀ = c' = 1/240`, `D = 3/2`, `Φ=Ψ=Bctl_n(1/2)^{7/15}`, `Bctl_n(t)=W^{-3}((λ²+|1-t|)⁻¹ + (L³|1-t|)⁻¹)` (`Sizes.lean:214`, `Bparam` `Params.lean:34`, `K=0`). Command (scratch `T2468/inst.py`, `T2468/margins.py`; output verbatim):

```
$ python3 -I inst.py   (condensed to the lines used)
tau=0.05 c0=0.0333333 c'=0.00416667
n=0: L=4 W=32 N=2097152 lam=0.015625 Bctl(1/2)=6.1959e-05 Phi=0.0108722 W^-c'=0.985663 W^-1.5=0.00552427
  n=0 E1 0<B True | E2 B<=1 True | F5 2B^(1/4)<=W^-c True | Phi<=W^-c' True | F8 W^-d<=B^(14/15) True
  n=0 Psi: W^(-d/2)<=Phi True | ratio B(1-s)/(1-t)<=B^(14/15) True | WO True | conStInd B(t)^cd<=(1-t)/(1-s) False
first n* (scan n<3000): E1 0, E2 0, F5 0, Phi 0, F8 0, Psi 0, ratio 0, conStInd 8, WO 0
n* = 8   all hold at n*: True  N(n*)=3.148e+23   all hold for 3000>n>=n*: True
c=0.01 S=expC(1,c/d)=4.9766e+13 S>=64:True (S^2+2)^2<=3S^4+4:True K=1.8402e+55 sqrt(K)/(2*3^d)=7.9440e+25
c=0.1  S=expC(1,c/d)=4.9766e+09 S>=64:True (S^2+2)^2<=3S^4+4:True K=1.8402e+39 sqrt(K)/(2*3^d)=7.9440e+17
c=1    S=expC(1,c/d)=4.9792e+05 S>=64:True (S^2+2)^2<=3S^4+4:True K=1.8440e+23 sqrt(K)/(2*3^d)=7.9522e+09
$ python3 -I margins.py
n=8 L=36 W=1889568 lam=2.940e-08 N=3.148e+23 Bctl(1/2)=2.9645e-19
  F5   2B^(1/4)=4.6668e-05 <= W^-c'=0.9416 ; Phi  B^(7/15)=2.2572e-09 <= W^-c'=0.9416
  F8   W^-d=1.4822e-19 <= B^(14/15)=5.0951e-18 ; W^-1.5=3.8500e-10 <= Phi=2.2572e-09
  ratio B*(1/2)/(1/3)=4.4468e-19 <= B^(14/15)=5.0951e-18 ; conStInd B(2/3)^0.01=0.6554 <= 2/3
```

All hypotheses hold at once for `n ≥ 8` (the only non-trivial one is the eventual `STConStInd`; all window inequalities hold already at `n = 0`). Hypotheses that stay open in the instances (targets 7) are the merged BA-V premises `hLK`, `hLoc` and the family premise: no deterministic or limit computation applies to them (they are unchanged premises of `BABootstrap'`/`BAStep1`, not new pins). No new external hypothesis enters targets 1–6: `BAFlowMember`, `BAGbEXPii`, `BAGbEXPij'` are proved.

Note (finding, not a failure): the absorption `√K ≤ 2·3^d N^{τ'/2}` is needed only for the *conclusion* of `baS1_wl_seq'`, which is a `∀ τ'`-`≺` (eventual) statement; for `d=3, c=1/10, τ'=0.1` it first holds at `ln N ≥ 824` (`n ≈ 3.4e19` for sz0), so a numerical witness of that conclusion is astronomically large. The compiled instances claim only `∀ᶠ` conclusions (as the merged `inst_baBootstrap'` does), so no hypothesis needs it. If the conclusion constant `2·3^d` were not kept verbatim, the absorption would be unnecessary; keeping it verbatim is the ticket's rule.

### Verdicts
- Target 1 `baGij'_member`: PASS.
- Target 2 (a) `step1Prime_loopPrem`: PASS (all premises eventual from `S1Std`; no `n`-dependent constant).
- Target 2 (b) `step1Prime_wl_det`: PASS (constant `3S⁴+4`, `S = expC(d-2,c/d) ≥ 64`, depends on `(d,c)` only; `2 ≤ d` needed).
- Target 3 (`baS1_*'`): PASS (only `hGij` changes).
- Targets 4, 5, 6, 7: PASS. Target 8 (registry): no mathematics.
- No g/g₀ crossing: Φ is built from `Bctl` at `sz.lam`; `s1_F5/F8` and `s1_ratio_ev` read `sz.lam` only; no comparison hypothesis arises.

## (a′) Preflight corrections — Mon Oct 12 19:29:34 UTC 2026
(a)(v) says the primed five differ in `hGij` "plus the binder `c`, `0 < c`". Also added: `hd : 2 ≤ d` (needed by `BAsum_exp_decay_le`), and the family states `GreenCore_decayConcl` unfolded to its `PrecL` body (premise scan, see (d)). No verdict changes. (a)(iii): `ε₀` is any `ε₀ > 0` in `step1Prime_loopPrem` (contains `c'`); `of_subset` + `precomp_param` are used, `of_le_left` is not.

## (b) Script output
```
$ git diff main...t/T2468 --shortstat; git diff main...t/T2468 --name-only | tr '\n' ' '
 3 files changed, 1188 insertions(+), 6 deletions(-)
RBM3D.lean RBM3D/BA/Step1Prime.lean RBM3D/Test/Axioms.lean 
$ wc -l RBM3D/BA/Step1Prime.lean; ls RBM3D/BA/Step1PrimeB.lean; grep -rn "import RBM3D.BA.Step1Prime" RBM3D RBM3D.lean
    1181 RBM3D/BA/Step1Prime.lean
ls: RBM3D/BA/Step1PrimeB.lean: No such file or directory
RBM3D.lean:527:import RBM3D.BA.Step1Prime
$ lake build RBM3D.BA.Step1Prime | tail -1; lake build | tail -1   # the full library runs #assert_rbm_axioms
Build completed successfully (3829 jobs).
Build completed successfully (4298 jobs).
$ lake env lean check_on_branch.lean   # docs/tickets/checks/T2468-check.lean + import Step1Prime + 9 examples + 27 #print axioms
exit 0; lines with 'error': 0
T2468_GijMember' := baGij'_member;T2468_BootstrapIj' := baBootstrap'_of_ij';T2468_Step1Ij' := baStep1_of_ij';T2468_BootstrapHolds := baBootstrap'_holds';T2468_Step1Holds := baStep1_holds';T2468_STGiiBA := baSTGiiGEXgL_holds;T2468_STGavBA := baSTGavLGEXgL_holds;T2468_InstBootstrap := Step1PrimeInst.inst_baBootstrap'_ij';T2468_InstStep1 := Step1PrimeInst.inst_baStep1'
$ grep "depends on axioms" check_out3.txt | sed "s/.*axioms: //" | sort | uniq -c   # Step1Prime_K, 14 theorems, 12 instances
  27 [propext, Classical.choice, Quot.sound]
$ python3 stmtdiff.py | grep "^[<>]"   # statement of baS1_X (Step1.lean) vs baS1_X' (Step1Prime.lean), name normalised; wl_seq shown
< theorem baS1_wl_seq (d : ℕ) :
> theorem baS1_wl_seq (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
<     (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
>     (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
>       ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
>         (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
>         (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
>         (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
>         GreenCore_loopPrem sz z' u ε₀ Φ →
>         PrecL sz (Sizes.seqP (sz.withLam 0))
>           (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
>           (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
>             ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
>           (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
>             (Sizes.STblk sz n p.1.2))) →
forb, boot, weakPT, loopPT with exactly these 2 removed and 13 added lines (same text): 4
$ git diff --stat main...t/T2468 -- RBM3D/Test/Axioms.lean RBM3D.lean; grep -n registry edits
 RBM3D.lean             |  1 +
 RBM3D/Test/Axioms.lean | 12 ++++++------
134:(instances: discharged with `inst_BAKbound` in `inst_baBootstrap'_ij'`, T2468;
148:BA: proved at `baFMz` (`baSTGiiGEXgL
149:BA: not produced in the window shape
150:BA: proved at `baFMz` (`baSTGavLGEXgL
391:`RBM.BA.BAGbEXPij]
$ lake env lean scan.lean   # scanPremises of RBM.Audit on the built library (ledger flags)
BAGbEXPij: f=true sup=true owed=false|BAGbEXPij': f=false sup=false owed=false|GreenCore_decayConcl: f=false sup=false owed=false|GreenCore_loopPrem: f=false sup=false owed=false|BAGbEXPii: f=false sup=false owed=false|STGiiGEXgL: f=false sup=false owed=true|STGavLGEXgL: f=false sup=false owed=true|STGijGEXgL: f=true sup=false owed=true|STKboundgL: f=false sup=false owed=true
$ greps of target 9
(a) exact unprimed names, line numbers (all inside docstrings): 15,16,95,218,371,845,846,878,
(b) 'm₀|Cλ|g ≤ W': 0 hits; (c) 'TwistStep2_lam0_sq|gK|lam0 n ≤|sz.lam n ^ 2': 0 hits
(d) 6:import RBM3D.BA.GbEXPav 7:import RBM3D.BA.KBound  ; sorry|admit|native_decide|axiom: 0 hits
$ name-clash: grep -rnF <name> RBM3D RBM3D.lean (excluding Step1Prime.lean and Test/Axioms.lean), 28 new public names
total hits: 0
```
- Layout: `RBM3D/BA/Step1Prime.lean` 1181 lines (stop line 2,000), no `Step1PrimeB`; reverse cone empty (only `RBM3D.lean`). Targets by line: `baGij'_member` 99, `Step1Prime_K` 143, `step1Prime_wl_det` 221, `step1Prime_loopPrem` 321, `baS1_wl_seq'` 408, `baS1_forb'` 555, `baS1_boot'` 677, `baS1_weakPT'` 728, `baS1_loopPT'` 772, `baBootstrap'_of_ij'` 848, `baStep1_of_ij'` 880, `baBootstrap'_holds'` 886, `baStep1_holds'` 892, `baSTGiiGEXgL_holds` 904, `baSTGavLGEXgL_holds` 913, instances 946-1177 (`Step1PrimeInst`).
- Bookkeeping as used: (a)(iii) stands. `step1Prime_loopPrem` (321): `hLI` at `k = 2` -> `precomp_param` along `p -> (![false,true], ![p.1,p.2])` -> `of_subset` with `s1_ratio_ev` (338) and `Step1Prime_indMax_le_omegaC` (294, `baM_entry_le`). Windows in `baS1_wl_seq'` (444-455): `s1_F5`, `s1_B_le_one`, `s1_F8`, `Step1Prime_wd_half` (384). Events at `τ'/2` (472) and `K <= 4*9^d*N^τ'` from `s1_N_pow_ev`.
- Core constant: `Step1Prime_K d c = 3 S^4 + 4`, `S = expC (d-2) (c/d)` (`BAsum_exp_decay_le` 167, `zdistD_le_mul_zdistInf` 171, `S >= 64` 146, `(S^2+2)^2 <= 3 S^4 + 4`); depends on `(d, c)` only; enters only in `step1Prime_wl_det` (221) and one inequality of `baS1_wl_seq'` (472).
- `open private`: `Boot_baFMz_eqAt` (Step1Boot); `BAStep1_le_gmMax, _gmMax_le, _gmMax_nonneg, _gmMax_le_add, _gmMax_continuousOn, _norm_BAmF_le_one, _net, _net_mem, _exists_close, _perTime_timeIcc` (Step1); `BASetup_maxLoop_nonneg`, `BASetup_omegaC_le_one` (Step1Setup, instances). Copies under the stem: `Step1Prime_member` (of private `Boot_member`, Step1Boot:232: its `κ', ε'` come after the sizes, the pin needs them before `c`), `Step1Prime_indMax_eq`, `Step1Prime_GM_eq`, `Step1Prime_indMax_le_omegaC`. No merged Lean file edited; no private deleted. Ports from `../RBM1D`, `../RBM2D`: none (copies are of merged RBM3D files).
- Instances: `inst_baGij'_member` (946), `inst_step1Prime_loopPrem` (964), `inst_step1Prime_wl_det` (973; `n = 0`, `u = 0`, as the merged `inst_flowFM_wl_det`), `inst_baS1_*'` (1049-1094), `inst_baBootstrap'_ij'` (1110; `hK` by `inst_BAKbound`), `inst_baStep1'`, `inst_baStep1'_low` (1127, 1144), examples for `baStep1_of_ij'`, `baBootstrap'_holds'`, `baStep1_holds'`, `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`, and `inst_BALmaxFromLK inst_BAKbound` (1161-1177). Hypotheses left: `hLK`, `hLoc` (and the family premise of `inst_baStep1'*`), the BA-V premises.
- Stage G closing conditions (2254 Q2 `:72-78`): (1) `BAGbEXPij'` proved: `baGbEXPij'_holds` (`BA/GreenOff.lean:1289`); (2) `BAGbEXPii` proved: `baGbEXPii_holds` (`BA/GreenLocal.lean:474`); (3) `BAGbEXPav` proved with nonempty instance: `baGbEXPav_holds` + `example : BAGbEXPav 3` (`BA/GbEXPav.lean:24, 28`); (4) primed consumers: `baBootstrap'_of_ij'`, `baStep1_of_ij'`, `baBootstrap'_holds'`, `baStep1_holds'` (`Step1Prime.lean:848-892`); (5) `BAGbEXPij` superseded: `supersededProps` entry (`Test/Axioms.lean:391`; scan above: f=true, sup=true, owed=false).

## (c) Verified Mathlib names (all compile in `Step1Prime.lean`)
`Real.rpow_le_rpow_of_exponent_ge`, `Real.one_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.exp_le_one_iff`, `Real.exp_add`, `pow_le_pow_iff_left₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `Finset.sum_mul_sum`, `Finset.mul_sum`, `Finset.sup'_le`, `inv_anti₀`, `neg_sub`, `neg_div`, `norm_le_norm_sub_add`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Premise scan: `baS1_*'` state the family with `GreenCore_decayConcl` unfolded (diff above), because `GreenCore_decayConcl` is concluded only inside `∃` (`baGij'_member`) and the scan lists a `Prop` definition that sits in a hypothesis and heads no theorem conclusion. `GreenCore_loopPrem` is concluded by `step1Prime_loopPrem`. Dispatcher: the folded form needs a registry line for `GreenCore_decayConcl`.
- Registry: `STGiiGEXgL`, `STGavLGEXgL`, `STKboundgL` are registered and not found by the scan (f=false above: each is concluded by a theorem); `STGijGEXgL` is still found (owner T1-BA, DECISIONS §272). `inst_baBootstrap'`, `inst_baBootstrap'_full` keep `hK`.
- Finding (from 1a): the conclusions of `inst_baS1_*'` are `∀ᶠ`; a finite-`n` numerical witness of the absorption `K <= 4*9^d N^τ'` needs `n` astronomically large (1a, (ii) note); no hypothesis needs it.
- Paper-delta candidates: none new at statement level (guard `2 <= d`: T2403a, T2408b). T2468a (informational): `baS1_*'` carry `hd : 2 ≤ d`, the explicit rate `c` and `0 < c`; Step 1's `3 S^4 + 4` window constant is Lean-internal (paper: "same as [RBSO1D, §7.1]", no constant).
