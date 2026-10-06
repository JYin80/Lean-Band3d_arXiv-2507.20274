Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 07:58:07 UTC 2026

### (i) Exponent table
`N = sz.size n = (WL)^d`, `a_s = Bctl n (s n) = W^{-d}B_{s,0}`, `κm = κ` (target 6), `c₀ = min(2𝔠𝔡, τ)`, `τ = ε/2` (`baS1Std`). Eventual (`∀ᶠ`) rows hold for `N ≥ N_*`; numbers are from the script in (ii).

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `τ`, `c₀` (instance) | `τ = 1/20`, `c₀ = min(2·(1/6)(1/10), 1/20) = 1/30` | `S1Std.hτ>0`; `a_u ≤ 2N^{-c₀}` (`s1_a_le`, `scaleFacts_R1`, needs `Bandwidth`, `WO`, `RangeCond`) | `a_s ≤ 2N^{-c₀}` at n=0: 6.2e-5 ≤ 1.2 |
| 2 | `c'` (`s1_F5`, `ε₀` of `GiiGEX/GijGEX`) | `c₀/8 = 1/240` | `2a_s^{1/4} ≤ W^{-c'}`: `2·2N^{-c₀/4}·W^{c'} ≤ 4N^{-c₀/8} ≤ 1` (`W^{c'} ≤ N^{c'/d}`) | exponent margin `c₀/8`; proof-level `N^{c₀/8} ≥ 4` |
| 3 | `τ₀` (`s1_F3`, target 3 initial) | `c₀/8` | `N^{τ₀}a_s^{1/2} < a_s^{1/4}` iff `N^{τ₀}a_s^{1/4} < 1`; `2N^{-c₀/4+c₀/8}`; needs `N^{c₀/8} > 2` (3 used) | margin `c₀/8` |
| 4 | `ε_f` (`s1_F4`, forbidden region) | `c₀/8` | `C_d a_s^{7/15} ≤ N^{-ε_f}a_s^{1/4}/2`, `C_d = 2·3^d = 54`: `4C_d N^{ε_f}a_s^{13/60} ≤ 1`, `a_s^{13/60} ≤ 2N^{-13c₀/60}` | exponent `13/60 − 1/8 = 11/120`; proof-level `N^{11c₀/120} ≥ 4C_d = 216` |
| 5 | constant of target 1 | `2·9^d+1` vs `(2·3^d)² = 4·9^d` | `‖GM_ij‖² ≤ (2·9^d+1)Nτ²g`, `g = a_s^{14/15} = (a_s^{7/15})²`, so `‖GM‖ ≤ C_d Nτ a_s^{7/15}` | d=3: 1459 ≤ 2916 (factor 1.99) |
| 6 | `g` (`s1_ratio_ev`, `s1_F8`) | `a_s^{14/15}` | `a_s(1−s)/(1−u) ≤ a_s^{1−𝔠d} ≤ a_s^{14/15}` for `s≤u≤t` (`𝔠d ≤ 1/100 ≤ 1/15`, `a_s ≤ 1`); `W^{-d} ≤ a_s^{14/15}` (`(𝔡⁻²+1)a_s^{1/15} ≤ 1`) | `1/15 − 𝔠d ≥ 17/300`; `a_s ≤ (2/3)^{15} = 2.3e-3` at u=t |
| 7 | event threshold `C₀` (targets 1, 5) | `1 + κm⁻¹ = 3` | on `{gmMax ≤ 2a_s^{1/4}}`: `‖G_xy‖ ≤ ‖M_xy‖ + 2a_s^{1/4} ≤ (Im m)⁻¹ + W^{-c'} ≤ κm⁻¹ + 1` (`baM_entry_le`, `κm ≤ Im m`, `W ≥ 1`) | n=0: max‖G‖ ≤ 1.177 ≤ 3; n=1: 1.013 ≤ 3 |
| 8 | target 5 event | `Ω_u = {∀xy, ‖G_u,xy‖ ≤ 1+κm⁻¹}` | on target 3's event: `‖G_xy‖ < (Im m)⁻¹ + a_s^{1/4} ≤ κm⁻¹ + 1` (`s1_F7`: `a_s^{1/4} ≤ 1`); `Ω_u` is exactly the `omegaC` condition, so `indicator = omegaC` | equality at `C₀` allowed (`≤`) |
| 9 | `C'` (`baGopbound`, `C=1`) | `2C+10 = 12`; net `≤ N^{C'+1} = N^{13}`, mesh `N^{-12}` | `N ≥ max(3, 3κ⁻²) = 12`; `u,u' ≤ 1 − N⁻¹` | `1−t = 1/3 ≥ N^{-1+τ} ≥ N⁻¹` (`hR`, `τ>0`) |
| 10 | mesh vs band (`s1_F6`) | `N⁻¹ ≤ a_s^{1/4}/2` | `a_s ≥ N⁻¹` (`cont_inv_size_le_Bctl`), `2N⁻¹ ≤ N^{-1/4}` iff `N^{3/4} ≥ 2` | exponent 3/4; n=0: 4.8e-7 ≤ 4.4e-2 |
| 11 | forbidden-region closure | `gmMax_u ≤ gmMax_{u'} + N⁻¹` (`M` time independent) | `gmMax_{u'} ≤ f < a/2·N^{-ε_f}`: `gmMax_u < a/2 + a/2`; or `gmMax_{u'} > 2a`: `gmMax_u > 2a − a/2 > a` (`a = a_s^{1/4}`) | strict via `N^{-ε_f} < 1`, `N ≥ 2` |
| 12 | target 4 | `gmMax_u < a_s^{1/4} ≤ a_u^{1/4}` | `Bctl n s ≤ Bctl n u` (`STBctl_mono`, `s ≤ u < 1`); `Bctl n u > 0` | n=0,1: `a_t/a_s = 1.5` |
| 13 | target 6 data | `S1Std(min κ 1, 𝔠, 𝔡, ε/2, 𝔠d, 0, s, t)` | `hE`: `0 ≤ 2 − min κ 1`; `κm = κ ≤ Im m(E,g₀')` via `BAFamZ_mono` (`0 ≤ s < t`) then `BAFamZ_im_m_ge`; `‖m‖ ≤ 1` from `Im m > 0`; `baBoot_LI` at `C₀ = 1+κ⁻¹ > 0`; `baNetLift` at `τ = ε/2` | `min κ 1 ≤ 1 ≤ 2` |

**P1 (decisive): `BABootstrap'` (`Step1Boot.lean:148-166`) walked through target 6; the pin is true as merged.**
- `baS1Std` needs `BAFlow`, `0 ≤ s`, `s ≤ t` (from `s < t`), `t ≤ t₀(z)`, `STConStInd 𝔠d s t`, `0 < 𝔠d ≤ 1/100`: all premises of the pin.
- `BAFamZ_mono (s ≤ t)` turns `BAFamZ … t z'` into `BAFamZ … (fun _ => 0) z'`; `BAFamZ_im_m_ge` needs `BAFlow`, `0 < sz.lam n`, `c₁ ∈ (0, 1/2]`, `BAWinBulk sz z c₁ κ`: premises.
- `baBoot_LI` needs `BAFlow`, `lam>0`, `c₁`, `BAWinBulk`, `0 ≤ s ≤ t ≤ t₀`, `BAFamZ … t z'` and exactly the `BAConArgLoop''` half of the pin's ConArg premise (range `max(s,1−c₁) ≤ u ≤ max(t,1−c₁)`, all `C₀>0`, `k ≥ 2`).
- `baGii_member` / `baGij_member` need `BAGbEXPii/ij`, `BAFlowMember`, `t ≤ t₀`, `BAFamZ … t z'`, `0 ≤ u ≤ t` (`u ∈ [s,t]`, `s ≥ 0`): supplied.
- Targets 3, 4, 5 use `STLocalMaxgL … s`; `baNetLift` needs `κ ≤ Im m`, `‖m‖ ≤ 1`, `0 < τ`, `0 ≤ s ≤ t < 1` (`S1Std.ht1`), `SizeTendsto` (`S1Std.hN`), `RangeCond (ε/2) t` (`S1Std.hR`), and the two per-time hypotheses = targets 5, 4 (`baFMz sz z' = baFM sz (BAflowLam0 sz z') (BAflowEs sz z')` by `def`).
- **Premises of `BABootstrap'` not used:** `STKboundgL`, `STLKgL` (grep below: they occur only in the pin, `Step1Boot.lean:156-157`), `BAConArgVec` (`:162`), `s ≤ t₀(z)` (follows from `s < t ≤ t₀`), and the strictness of `s < t` (only `s ≤ t` is used).

### (ii) One concrete nondegenerate instance
Data: `d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N_0 = 2^21`), `z' = zSeq` (`BAFamZ_main`), `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `𝔠d=1/100`, `c₁=1/3`, `s≡1/2`, `t≡2/3` (`t₀ ≥ 2/3`, `t0_sz0`), `κm = 1/2`, `C₀ = 3`. Hypotheses deterministic at this data: `S1Std` (`inst_baS1Std`), `Im m ≥ 1/2`, `‖m‖ ≤ 1`, `STConStInd` (merged `s1Setup_conStInd_const`, an eventual statement: holds from n=8, T2262 (a)(ii)(B)). Hypotheses kept: `BAFlowMember 3`, `BAGbEXPii 3`, `BAGbEXPij 3` (owed pins), `hwin : BAWinBulk sz0 zSeq (1/3) (1/2)` (external; limit computation: T2262 (a)(ii)(F): `min_{g'} Im m(E_n,g') ≥ 0.9994`, `E_n → 0`, `Im m → 1 ≥ 1/2`), `STKboundgL`, `STLKgL`, `STLocalMaxgL` at `sI` (other gates). The ConArg premise: `inst_hcon` (`Step1Boot.lean:748`, from `baConArg''_holds 3`) gives the loop half; the `BAConArgVec` half is `(baConArg''_holds 3 … C₀ hC₀).2` at the same data (`hκm`, `hL`, range `u ≡ 2/3` of `inst_hcon`): obtained by the same reduction as `inst_hcon` (`hu`, `hs₁`, `hκm`, `hL`), so not kept as a hypothesis.
```
$ grep -n "STKboundgL\|STLKgL\|BAConArgVec" RBM3D/BA/Step1Boot.lean RBM3D/BA/Step1Setup.lean | cut -c1-140
RBM3D/BA/Step1Boot.lean:156:              STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) →
RBM3D/BA/Step1Boot.lean:157:              STLKgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
RBM3D/BA/Step1Boot.lean:162:                  BAConArgVec sz z' (fun n => max (s n) (1 - c₁)) u) →
$ python3 scratchpad/T2269/inst.py | cut -c1-250
== (A) exponents: tau=eps/2=0.05, c0=min(2*c*dd,tau)=0.0333333, tau0=eps_F4=c'=c0/8=0.00416667 ; C_d=2*3^d=54, (C_d)^2=4*9^d=2916 >= 2*9^d+1=1459
   slacks: F3 N^{c0/8}*2N^{-c0/4}=2N^{-c0/8} (margin c0/8); F4 exponent 13/60-1/8=0.0916667 (=11/120); F5 1/4-1/8=1/8; F6 3/4; ratio 14/15 vs 1-cd: 1/15-cd=0.0566667; ratio_ev at u=t needs a<=(2/3)^15=2.284e-03
   proof-level N thresholds (log10 N): F3 N^{c0/8}>=3: 114.5 ; F4 N^{11c0/120}>=4*C_d: 764.0 ; F5 N^{c0/8}>=4: 144.5 ; F6 N^{3/4}>=2: 0.40
== (B) actual values at sz0 (L=4(n+1), W=(2(n+1))^5, g=(2(n+1))^-6), s=1/2,t=2/3,u in[s,t]; eventual statements checked at actual a_s
n   N          a_s        a^(1/4)   F3:N^t0 a^(1/4)<1  F4 lhs<=rhs (lhs,rhs)       F5 2a^(1/4)<=W^-c'  F6 1/N<=a^(1/4)/2  F7  F8 W^-3<=a^(14/15)  ratio(u=t)<=a^(14/15)  a<=2N^-c0
0   2.097e+06 6.196e-05 8.872e-02 True               False (5.87e-01,4.17e-02) True                True               True True              True                   True
1   5.498e+11 1.866e-09 6.573e-03 True               False (4.56e-03,2.94e-03) True                True               True True              True                   True
2   8.125e+14 4.256e-12 1.436e-03 True               True  (2.67e-04,6.22e-04) True                True               True True              True                   True
3   1.441e+17 5.686e-14 4.883e-04 True               True  (3.56e-05,2.07e-04) True                True               True True              True                   True
5   2.130e+20 1.298e-16 1.067e-04 True               True  (2.08e-06,4.39e-05) True                True               True True              True                   True
8   3.148e+23 2.965e-19 2.333e-05 True               True  (1.22e-07,9.31e-06) True                True               True True              True                   True
20  1.323e+30 8.960e-25 9.729e-07 True               True  (3.24e-10,3.64e-07) True                True               True True              True                   True
100 2.509e+42 5.257e-35 2.693e-09 True               True  (5.44e-15,8.96e-10) True                True               True True              True                   True
first n at which each inequality holds (and for all later sampled n): {'F3': 0, 'F5': 0, 'F6': 0, 'F7': 0, 'F8': 0, 'rat': 0, 'R1': 0, 'F4': 2}
   all eight hold for every n in [2,400)
== (C) events (targets 1,5): C0=1+1/kappa=3; recomputed member data zSeq (w=6i/5, z+m_S=w), M=(g0 Psi-(E+m))^-1 block
   n=0 Im m(E,g0)=0.99949 max|M_ab|=0.99949 <= 1/Im m=1.00051 <= 1/kappa=2 ; on {gmMax<=2a_s^(1/4)=1.774e-01}: max|G|<=1.17693 <= C0=3
   n=1 Im m(E,g0)=1.00000 max|M_ab|=1.00000 <= 1/Im m=1.00000 <= 1/kappa=2 ; on {gmMax<=2a_s^(1/4)=1.315e-02}: max|G|<=1.01315 <= C0=3
== (D) target 2: gopbound C=1 -> C'=2C+10=12, net #<=N^(C'+1)=N^13, mesh N^-12; N>=max(3,3/kappa^2)=12 ; u<=1-1/N: 1-t=1/3>=N^(-1+tau)>=N^-1
   n=0 N=2.097e+06: 1/N=4.77e-07 <= a^(1/4)/2=4.44e-02 (mesh N^-12=1.4e-76); 1-t=1/3>=N^(-0.95)=9.87e-07
   n=1 N=5.498e+11: 1/N=1.82e-12 <= a^(1/4)/2=3.29e-03 (mesh N^-12=1.3e-141); 1-t=1/3>=N^(-0.95)=7.03e-12
   n=8 N=3.148e+23: 1/N=3.18e-24 <= a^(1/4)/2=1.17e-05 (mesh N^-12=1.1e-282); 1-t=1/3>=N^(-0.95)=4.75e-23
== (E) target 3: gmMax_s <= N^tau0 a^(1/2) < a^(1/4)  (F3 above); continuity: 0<kappa<=Im m, t<1; a=b=a_s^(1/4) const
== (F) target 4: a_s^(1/4)<=a_u^(1/4): Bctl monotone in u: Bctl(t)/Bctl(s) at n=0,1: ['1.500', '1.500']
```
Reading: (A) rows 1-6; proof-level thresholds (log10 N: 114.5, 764.0, 144.5) are far beyond `N_0` because the proof uses the weak bound `a_s ≤ 2N^{-c₀}`; the statements are `∀ᶠ`, so the compiled instance applies theorems with eventual conclusions and claims no value at a finite `n`. (B) the eight eventual inequalities, evaluated at the **actual** `a_s ≈ 2W^{-3}` (`Bparam` at `K=0`, `Params.lean:36`; `Bctl`, `Sizes.lean:214`), hold for every n in [2,400); F4 fails at n=0,1 only. (C) rows 7-8, member data recomputed. (D) rows 9-11. (F) row 12.

### Verdicts
- Target 0 `FlowFM.gmMax` and helpers (`le_gmMax`, `gmMax_le`, `gmMax_nonneg`, `gmMax_le_add`, `gmMax_continuousOn`): **PASS** (rows 11-12; `GM_u − GM_{u'} = BAGt_u − BAGt_{u'}`, `M = BAMfine` time independent).
- Target 1 `baS1_wl_seq`: **PASS** (rows 2, 5-7; `flowFM_wl_det` hypotheses all supplied, `k=2` loop input uniform).
- Target 2 `baS1_forb`: **PASS** (rows 4, 9-11).
- Target 3 `baS1_boot`: **PASS** (rows 3, 13; `stepOneBootstrap` with `a = b = a_s^{1/4}`).
- Target 4 `baS1_weakPT`: **PASS** (row 12).
- Target 5 `baS1_loopPT`: **PASS** (row 8; `k=1` included).
- Target 6 `baBootstrap'_holds`: **PASS** (P1: pin true as merged, no primed successor needed; unused premises listed above for T2269b).

## (b) Script output (commands and verbatim output) and narrative — Tue Oct  6 08:30:24 UTC 2026
```
$ date -u
Tue Oct  6 08:26:18 UTC 2026
$ git log -1 --format="%h %an" t/T2269; git diff --stat main...t/T2269
7932bb0 Jun Yin
 RBM3D/BA/Step1.lean    | 784 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   4 +-
 2 files changed, 787 insertions(+), 1 deletion(-)
$ lake build RBM3D.BA.Step1 2>&1 | tail -1; ... | grep -c "BA/Step1.lean:"   (warnings located in the new file)
Build completed successfully (3756 jobs).
0
$ lake build 2>&1 | tail -1   (full library; the root has no BA.Step1 import until the hub merges)
Build completed successfully (4076 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/BA/Step1.lean; wc -l RBM3D/BA/Step1.lean
0
     784
```

Target statements, extracted from RBM3D/BA/Step1.lean by script (whitespace-normalised, wrapped at 200):
```
noncomputable def FlowFM.gmMax {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W
n) => ‖C.GM n v ω q.1 q.2‖)

theorem baS1_wl_seq (d : ℕ) : ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ), RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm → (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz
  z') n).im) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => (baFMz sz
  z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖) (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t
  n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) → ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
  PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun _ => Unit) (fun n _ ω => {ω | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}.indicator (fun ω => gmMax (baFMz sz
  z') n (u n) ω) ω) (fun n _ _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))

theorem baS1_forb (d : ℕ) : ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ), RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm → (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z')
  n).im) → (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k →
  Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖) (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^
  (k - 1))) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
  HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n, gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) ∨ (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) < gmMax
  (baFMz sz z') n (u : ℝ) ω})

theorem baS1_boot (d : ℕ) : ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ), RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm → (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z')
  n).im) → (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k →
  Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖) (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^
  (k - 1))) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
  STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s → HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n, gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^
  ((1 : ℝ) / 4)})

theorem baS1_weakPT (d : ℕ) : ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ), RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm → (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz
  z') n).im) → (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k
  → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖) (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n))
  ^ (k - 1))) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
  STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s → PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p
  ω => ‖(baFMz sz z').GM n (p.1 : ℝ) ω p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

theorem baS1_loopPT (d : ℕ) : ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ), RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm → (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz
  z') n).im) → (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k
  → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖) (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n))
  ^ (k - 1))) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) → (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
  STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s → ∀ k : ℕ, 1 ≤ k → PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
  (fun n p ω => ‖(baFMz sz z').L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

theorem baBootstrap'_holds (d : ℕ) : BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d
```

Statement checks (check file `docs/tickets/checks/T2269-check.lean`; scratch copy = check file + `import RBM3D.BA.Step1` + the examples below):
```
$ python3 stmtdiff.py   # whitespace-normalised bodies, check file `def *_stmt` vs the theorem
baS1_wl_seq IDENTICAL (1031/1031 chars); baS1_forb IDENTICAL (983/983 chars); baS1_boot IDENTICAL (972/972 chars)
baS1_weakPT IDENTICAL (1061/1061 chars); baS1_loopPT IDENTICAL (1102/1102 chars); baBootstrap'_holds IDENTICAL (59/59 chars); FlowFM.gmMax body IDENTICAL (121/121 chars)
$ lake env lean check_stmt.lean; echo $?
exit 0   (error lines: 0)
example : @FlowFM.gmMax = @gmMax := rfl
example (d : ℕ) : baBootstrap'_holds_stmt d := baBootstrap'_holds d
example (d : ℕ) : baS1_wl_seq_stmt d := baS1_wl_seq d
example (d : ℕ) : baS1_forb_stmt d := baS1_forb d
example (d : ℕ) : baS1_boot_stmt d := baS1_boot d
example (d : ℕ) : baS1_weakPT_stmt d := baS1_weakPT d
example (d : ℕ) : baS1_loopPT_stmt d := baS1_loopPT d
$ #print axioms of every new public declaration (in check_stmt.lean), summarised by script
18 declarations printed by #print axioms; axiom sets: {'[propext, Classical.choice, Quot.sound]': 18}
FlowFM.gmMax, baS1_wl_seq, baS1_forb, baS1_boot, baS1_weakPT, baS1_loopPT, baBootstrap'_holds, Step1Inst.inst_hcon_full, Step1Inst.inst_hLI, Step1Inst.inst_hGii, Step1Inst.inst_hGij, Step1Inst.inst_baS1_wl_seq, Step1Inst.inst_baS1_forb, Step1Inst.inst_baS1_boot, Step1Inst.inst_baS1_weakPT, Step1Inst.inst_baS1_loopPT, Step1Inst.inst_baBootstrap', Step1Inst.inst_gmMax_zero
```

Compiled nonempty instances (namespace `RBM.BA.Step1Inst`, same file); the list of them, and the endpoint instance of target 6:
```
633 inst_hcon_full;673 inst_hLI;686 inst_hGii;694 inst_hGij;703 inst_baS1_wl_seq;715 inst_baS1_forb;726 inst_baS1_boot;736 inst_baS1_weakPT;748 inst_baS1_loopPT;764 inst_baBootstrap';780 inst_gmMax_zero;
theorem inst_baBootstrap' (hmem : BAFlowMember 3) (hii : BAGbEXPii 3) (hij : BAGbEXPij 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2))
    (hK : STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)))
    (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI)
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧
      STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI :=
  baBootstrap'_holds 3 hmem hii hij (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100)
    (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin sI tI
    (fun _ => by norm_num [sI]) (fun n => (show sI n ≤ 2 / 3 by norm_num [sI]).trans (t0_sz0 n))
    (fun _ => by norm_num [sI, tI]) (fun n => t0_sz0 n) zSeq (BAFamZ_main sz0 zSeq (1 / 3) tI) hK hLK hLoc
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (s0 := 1 / 2) (t0 := 2 / 3) (by norm_num) (by norm_num)
      (by norm_num)) (inst_hcon_full hwin)

```

Name clashes, registry pre-check (DECISIONS §20 (2)), ports, P1:
```
$ name-clash: declarations (theorem|lemma|def|abbrev) of each new name in RBM3D/ outside BA/Step1.lean
FlowFM.gmMax=0 gmMax=0 baS1_wl_seq=0 baS1_forb=0 baS1_boot=0 baS1_weakPT=0 baS1_loopPT=0 baBootstrap'_holds=0 inst_hcon_full=0 inst_hLI=0 inst_hGii=0 inst_hGij=0 inst_baS1_wl_seq=0 inst_baS1_forb=0 inst_baS1_boot=0 inst_baS1_weakPT=0 inst_baS1_loopPT=0 inst_baBootstrap'=0 inst_gmMax_zero=0 
$ registry pre-check: printf "import RBM3D\nimport RBM3D.BA.Step1\n#assert_rbm_axioms\n" > precheck.lean; lake env lean precheck.lean
exit 0
axiom audit: 7899 theorems, 2609 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines of the output naming BABootstrap': 0
55:  RBM.BA.STKboundgL: 3 [no certificate]
56:  RBM.BA.STLKgL: 4 [no certificate]
57:  RBM.BA.STLocalMaxgL: 9 [no certificate]
291:non-vacuity certificates: 0 of 159 premises in the two ledgers; the rest are not known to be satisfiable (
$ owed names in `owedProps`: main (HEAD~1:RBM3D/Test/Axioms.lean) vs t/T2269
owed on main: 155  owed on t/T2269: 157  removed: ["RBM.BA.BABootstrap'"]  added: ['RBM.BA.STKboundgL', 'RBM.BA.STLKgL', 'RBM.BA.STLocalMaxgL']
$ git diff HEAD~1 HEAD -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-70
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
+   `RBM.BA.STKboundgL, -- `ML:Kbound` `max |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d
+   `RBM.BA.STLKgL, -- `(Eq:L-KGt)` (a) at a law `μ` over a flow carri
+   `RBM.BA.STLocalMaxgL, -- `(Gt_bound+IND)` at a law `μ` over a flow
-   `RBM.BA.BABootstrap', -- BA Step 1 bootstrap for one member of `Fa
$ ports (sources in this repo, not RBM1D/RBM2D): commits touching each source since the cited commit, and git diff --stat <cited> HEAD -- <file>
RBM3D/Induction/Step1.lean @ b969625: commits since: 0; diff --stat: []
RBM3D/Induction/Step1Setup.lean @ 4f186cf: commits since: 0; diff --stat: []
RBM3D/BA/Step1Setup.lean @ 8bb6f82: commits since: 0; diff --stat: []
RBM3D/Induction/PerTimeCalc.lean @ 5d1e6b1: commits since: 0; diff --stat: []
$ grep -n "RBM1D\|RBM2D" RBM3D/BA/Step1.lean | wc -l   # no RBM1D/RBM2D text read or copied
       0
$ P1: where the premises of BABootstrap' not used by Step 1 occur in the proof of baBootstrap'_holds
2:  intro hmem hii hij κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT z' hfam
3:    hK hLK hLoc hCond hcon
12:    hfam (fun u h1 h2 => (hcon u h1 h2).1) (1 + κ⁻¹) (by positivity)
```

Narrative:
- New file `RBM3D/BA/Step1.lean`, 784 lines (ticket size band 600 / 800 / 1100). Section 0: `FlowFM.gmMax` and private helpers `BAStep1_le_gmMax`, `_gmMax_le`, `_gmMax_nonneg`, `_gmMax_le_add`, `_gmMax_continuousOn`, `_norm_BAmF_le_one`, `_net`, `_net_mem`, `_exists_close`, `_perTime_timeIcc` (the copies cite `Step1.lean:line` at b969625 in their docstrings). Sections 1-4: the six targets. Section 5: the instances.
- The six statements are the check file's bodies character for character (script above). No hypothesis was added or weakened and no merged pin or signature was touched (`git diff --stat`: the new file and four lines of `Axioms.lean`). No (a') section: section (a) needed no correction.
- Differences from the band proofs. `baS1_wl_seq`: the `k = 2` loop input is the uniform `PrecL`; its event is `perTimeCalc_highProbAt_of_stochDomAt` and it is enlarged to `a_s^{14/15}` by `s1_ratio_ev` (the file contains no `s1_card_loops` and no `s1_highProb_of_pt`); core `flowFM_wl_det` at `C0 = 1 + κm^{-1}`, with `‖G_xy‖ ≤ 2a + (Im m)^{-1} ≤ W^{-c'} + κm^{-1} ≤ 1 + κm^{-1}` (`baM_entry_le`, `κm ≤ Im m`); constant `2·9^d + 1 ≤ 4·9^d` as the band. `baS1_forb`: `baGopbound` at `C = 1`; passage to all `u` by `BAStep1_gmMax_le_add` and `N^{-1} ≤ a/2` (`s1_F6`). `baS1_boot`: initial event from `STLocalMaxgL` with `τ0` of `s1_F3`, continuity from `baG_continuousOn`, `stepOneBootstrap` with `a = b = a_s^{1/4}`. `baS1_weakPT`: `STBctl_mono`. `baS1_loopPT`: `stochDom_of_indicator`; the loop input per `u` is made per time by `perTimeOfStochDomAt` and lifted by `BAStep1_perTime_timeIcc`. `baBootstrap'_holds`: `baS1Std`; `BAFamZ_mono` and `BAFamZ_im_m_ge` (`κm = κ`); `BAStep1_norm_BAmF_le_one`; `baBoot_LI` at `C0 = 1 + κ^{-1}`; `baGii_member`, `baGij_member`; `baNetLift`.
- P1 (grep above): the pin is true as merged. Premises it carries and the proof does not use: `STKboundgL`, `STLKgL` (occur only in the `intro`), the `BAConArgVec` half of the ConArg premise (only `.1` is used), `s ≤ t0(z)` (`hsT`), and the strictness of `s < t` (only `(hst n).le`).
- Registry deviation from the ticket (which says no line added, owed count = main's - 1). The first pre-check run, before any line was added, exited 1: `axiom audit: 3 premise(s) that no theorem of this development proves are in none of ...: [RBM.BA.STLocalMaxgL, RBM.BA.STLKgL, RBM.BA.STKboundgL]`. The instances take these three as hypotheses (the ticket's instance list requires them) and are the first theorems to do so. I appended three `owedProps` lines (DECISIONS §20 (1); `STLmaxgL` was registered the same way by T2197) and deleted the `BABootstrap'` line; pre-check exit 0; owed count 155 -> 157 (T2269c).
- Instances (`RBM.BA.Step1Inst`): `sz0`, `zSeq`, `z' = zSeq`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`, `c1 = 1/3`, `s = sI ≡ 1/2 < t = tI ≡ 2/3 ≤ t0` (`t0_sz0`). Discharged: `flow_sz0`, `sz0_lam_pos`, `inst_baS1Std`, `inst_im_m_ge`, `inst_norm_m_le`, the times, `STConStInd` (`s1Setup_conStInd_const`), and both halves of the ConArg premise (`inst_hcon_full`, 37 lines, from `baConArg''_holds 3`; so `hvec` is not a hypothesis). Hypotheses: `BAFlowMember 3`, `BAGbEXPii 3`, `BAGbEXPij 3`, `BAWinBulk sz0 zSeq (1/3) (1/2)` (limit check in (a)(ii)), `STKboundgL`, `STLKgL`, `STLocalMaxgL` at `sI` (other gates). The conclusions are `∀ᶠ`-type statements: no value at a finite `n` is claimed. `inst_gmMax_zero` gives `gmMax = 0` at `n = 0`, `t = 0` (from `inst_GM_zero`).

## (c) Verified Mathlib names used (`#check` in `scratchpad/T2269/mathlib_names.lean`, no error; verified absent: none queried)
```
@ContinuousOn.finset_sup'_apply : ∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topologi
@Finset.le_sup' : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β} (
@Finset.sup'_le : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (H : s.Nonempty) (f :
@Finset.univ_nonempty : ∀ {α : Type u_1} [inst : Fintype α] [Nonempty α], Finset.univ.Nonempty
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@norm_le_norm_sub_add : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a‖ ≤ ‖a - b‖ + ‖b‖
@inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPos
@Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
@Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
@pow_le_pow_iff_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : LinearOrder M₀] [PosMulStrictMono
@one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] 
@Set.indicator_of_mem : ∀ {α : Type u_1} {M : Type u_2} [inst : Zero M] {s : Set α} {a : α}, a ∈ s → ∀ (f : α → 
@Set.indicator_of_notMem : ∀ {α : Type u_1} {M : Type u_2} [inst : Zero M] {s : Set α} {a : α}, a ∉ s → ∀ (f : α
@Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
@Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
@Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
@one_div_le_one_div_of_le : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] 
@norm_sub_rev : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a - b‖ = ‖b - a‖
@MeasureTheory.measure_mono : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.
```

## (d) Open issues and paper-delta candidates
- **T2269a** `7_8:1987-1990` ("same as [RBSO1D, §7.1]") is read here with the continuity argument on `‖G_u - M‖_max` over the carrier `baFMz sz z'` (vocabulary `FlowFM.gmMax`, `M = M(E, g0)` non-scalar, time independent), the event threshold `1 + κ^{-1}` for `Ω_u` in place of the band's `2` (`|M_xy| ≤ (Im m)^{-1}`, `baM_entry_le`), and the uniform loop input `PrecL`.
- **T2269b** The pinned `BABootstrap'` (`BA/Step1Boot.lean:148`) carries premises Step 1 does not use: `STKboundgL`, `STLKgL`, the `BAConArgVec` half of the ConArg premise, `s ≤ t0(z)`, and `s < t` strict (P1 grep above). BA-S3 must still supply them; a slimmer successor is a supervisor question and is not done.
- **T2269c** (process, not a paper delta) `Test/Axioms.lean`: `BABootstrap'` deleted from `owedProps`; `STKboundgL`, `STLKgL`, `STLocalMaxgL` added as owed (they are hypotheses of public instance theorems). Owed count 155 -> 157, not main's - 1 as the ticket's acceptance line says; dispatcher to confirm or to move the three lines to the ticket that owns them.
- Open: the instances' hypotheses (`BAFlowMember 3`, `BAGbEXPii 3`, `BAGbEXPij 3`, `hwin`, `STKboundgL`, `STLKgL`, `STLocalMaxgL`) are other gates' pins; the instance conclusions are eventual statements.
