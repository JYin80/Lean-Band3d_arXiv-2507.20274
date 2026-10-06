Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 07:08:48 UTC 2026

Notation: `N = Nsz sz n = (W L)^d`, `t* = ouTStar sz τU n = N^{-1+τU}`, `m_s = stieltjesN (ouMat (band) n s ω)`,
`F(s) = E ∏ Im m_s(z_i)`, `g(s) = -(1/2) e^{-s} Σ_{ab} S°_{ab} E wirtSecond Φ (𝐇_s) a b` (UN-15 B1/B2 integrand).

### (i) Exponent table

| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | generator prefactor | `-(1/2) e^{-s}` (B2, `OUGenerator.lean:1073`) | `‖·‖ ≤ 1/2` on `s ≥ 0` | `1/2 (1 - e^{-s}) ≥ 0`, exact at `s = 0` |
| 2 | pointwise kernel bound | UN-17 target 5 at `s = univ`, `ι = Fin nf`, constant 1 in front of `L1t`, `L2t` (`OUContraction.lean:1077`) | RHS tokens = target 1's integrand tokens (`univ.erase i`, `(univ.erase i).erase j`) | exact (0 loss) |
| 3 | counting constant | `Σ_i B + Σ_i Σ_{j≠i} B = nf B + nf(nf-1) B = nf² B` | `Bd := nf² B` | exact identity (`nf ≥ 1`: `Nat.cast_sub`) |
| 4 | interval factor | `(1/2)(t* - t) Bd` | `0 ≤ t ≤ t*` gives `t* - t ≤ t*` | `t` (slack `t* - (t*-t) = t`) |
| 5 | eventual threshold | `1/2 nf² ≤ N^ε`, `ε > 0`, `nf ≥ 1` | `N ≥ (nf²/2)^{1/ε}`, from `N → ∞` (`sz.SizeTendsto`) | `n0(ε, nf)` finite; table below; uniform in `z, B, t` |
| 6 | exponent comparison | `N^{-1+τU} ≤ N^{-1+Cn τU}` | `N ≥ 1` and `-1+τU ≤ -1+Cn τU` i.e. `τU ≤ Cn τU` (no `0 < τU` needed) | `(Cn - 1) τU` in the exponent; `0` at `Cn = 1` |
| 7 | row constants | `Cn = 1`, `τ₀ = 1` | row needs `0 < τ₀`, `τU ≤ τ₀`, `τU ≤ Cn τU` | row 6 slack 0 (`1 * τU = τU`); `τ₀` arbitrary `> 0` |
| 8 | positivity of `Im z_i` | window `Im z_i ≥ N^{-1-τU}` | `> 0`: needs `N > 0` only (`N = (W L)^d`, `L ≥ 3`, `W ≥ 1`, any `d`) | `N^{-1-τU} > 0` for every real `τU` |
| 9 | `N ≥ 1` | `N = (W L)^d`, `W L ≥ 3` | row 6 | `N ≥ 1` for every `d ≥ 0` (`N ≥ 3^d`) |
| 10 | `Im m ≥ 0`, `L1t, L2t ≥ 0` | `stieltjesN_im_eq_normalized_specWeight` at `E = Re z`, `η = Im z > 0` (`InjSum.lean:196`); `L1t, L2t` are sums of norms | needed for `0 ≤ Bd` (`t < T`) and for integrability bounds | exact |
| 11 | resolvent bound | `‖Gres H z b‖ ≤ (Im z)⁻¹`, both `b` (`norm_Gsig_le_inv_eta`, `FlowCalculus.lean:644`, `η = |(z̄).im| = Im z`) | boundedness (hence integrability) of each kernel term at fixed `z`: `L1t ≤ 4 N^{-1} Σ_{xy}|S°| η^{-3}`, `Im m ≤ η^{-1}` | finite constant for fixed `z` |
| 12 | `nf = 0` | pin holds for every `sz`, `B ≥ 0` (`un_emcte2_zero`, `Pins.lean:1835`) | `0 ≤ N^ε N^{..} B` | uses `0 ≤ B` (the pin's own hypothesis) |
| 13 | `d` | only through `Idx d`, `N = (W L)^d` | no `3 ≤ d` used by targets 1-2; targets 3-4 carry `3 ≤ d` from the row | instance at `d = 3` |

Mathematical chain of target 2 (`nf ≥ 1`), checked line by line against the RBM2D proof (`EMCTE2.lean:567-643` at c9a24cf):
`|F(t) - F(t*)| ≤ (1/2)(t* - t) nf² B ≤ (1/2) nf² t* B ≤ N^ε t* B = N^ε N^{-1+τU} B ≤ N^ε N^{-1+Cn τU} B`;
the third step uses `B ≥ 0`, `t* ≥ 0`, row 5; the last uses rows 6, `B ≥ 0`. The two `hB` hypotheses of the pin
(on `s ∈ [0, t*]`) cover target 1's `Ioo t t*` since `t ≥ 0`.

Target 1 mathematics (RBM2D `:440-559`), what the port must keep true:
- `F(T) - F(0) = ∫_0^T g`, `F(t) - F(0) = ∫_0^t g` (B2); `F(T) - F(t) = ∫_t^T g` when `g` is interval integrable on `[0,t]`;
  otherwise both integrals are the junk value `0` (`integral_undef`), so `F(T) - F(t) = 0 ≤ (1/2)(T-t) Bd` (needs `Bd ≥ 0`, forced by `hB` as the integrand is `≥ 0` when `t < T`; trivial when `t = T`).
- `‖g(s)‖ ≤ (1/2) Bd` on `(t, T)`: `‖Σ_{ab} S°_{ab} E wirtSecond‖ = ‖E Σ_{ab} S°_{ab} wirtSecond‖` (swap needs `wirtSecond Φ(𝐇_s) a b` integrable) `≤ E[kernel sum] ≤ Bd`.
- measurability of `g` on `(t, T]`: `g = deriv F` there (B1 on `s > 0`), `deriv` measurable.

### Findings on the ported pieces (mathematics only)

1. Integrability of `ω ↦ wirtSecond Φ (ouMat (band) n s ω) a b` on the band carrier. RBM2D used continuity of
   `ouMat` on `Ω × Ω` (`EMCTE2_continuous_ouMat`, `:393`). On the RBM3D carrier `SeqΩ sz × Ω`, by T1
   (`ouMat_band_eq_ouPairMat`, `rfl`) the map is `(wirtSecond Φ ∘ ouPairMat s) ∘ Prod.map (slice sz n) id`:
   first factor continuous on the pair carrier (`continuous_Xmat`, `Φ` is `C²` at Hermitian points), second measurable
   (`measurable_slice`, `measurable_id`). So it is measurable (hence a.e.-strongly measurable, codomain `ℂ`) and bounded by the
   constant of the second-derivative bound in `TestFunH` (`OUGenerator.lean:68`) times the norms of the fixed basis matrices: integrable on the probability measure `ouP (band) n`. Continuity on the carrier is
   not needed and not claimed.
2. `EMCTE2_sum_integral_swap` (`:408`) ports with only the integrability input replaced (finding 1): its proof uses only
   `integral_const_mul`, `integral_finsetSum` and that integrability; the swapped expression is exactly B2's integrand shape
   `Σ_a Σ_b (S°_{ab} : ℂ) * ∫ wirtSecond …`.
3. `Gres` bridge: `L1t`, `L2t`, `stieltjesN` are `Gres`-based (`Pins.lean:88, 617-629`); `Gres M z false = (M - z̄)⁻¹`; entry
   measurability `walk_measurable_Gres_apply ∘ measurable_ouMat` (`measurable_ouMat M n t : Measurable (ouMat M n t)`, `OU.lean:80`);
   entry bound via `‖M p q‖ ≤ ‖M‖` (`norm_apply_le_l2_opNorm`) and `‖(G G) a a‖ ≤ ‖G‖² ≤ η^{-2}`.
4. Two data, one model: B1/B2's `S°` is `centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n)`; `L1t`, `L2t` in the pin
   carry `sz.lam n` through `scirc`; UN-17 at `lam = sz.lam n` converts (`paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t`). Same
   coupling in both: no mismatch.
5. Target 4: `UNEMCTE2Rowk (fun d => UNKind.band d) ↔ UNEMCTE2Row` is the merged `UNEMCTE2Rowk_band` (`PinsK.lean:534`, an `↔` proved by unfolding and `simp`; the bulk premise `∀ᶠ n, |E| ≤ 2 - κ` is a constant statement and unused). No new mathematics.
6. Pin scope: the merged `UNEMCTE2` has no size hypothesis, but the step `1/2 nf² ≤ N^ε` (row 5) needs `N → ∞`; target 2 therefore carries `sz.SizeTendsto` and `τU ≤ Cn τU` (ticket T2266a (1)).
   Consumers reach the pin only through `UNEMCTE2Row` / `UNClaimRow` at admissible sizes (third conjunct of `Admissible`).

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`L(n) = 4(n+1)`, `W(n) = (2(n+1))^5`, `lam(n) = (2(n+1))^{-6}`), `n = 0`: `L = 4`, `W = 32`, `N = 2^21`,
`lam = 1/64`. Target 1: `nf = 1`, `z = ![I]` (`Im z = 1`), `t = 0`, `T = 1`, `Bd = 8`. Target 2: `E = 0`, `nf = 2`, `τU = 1/2`,
`Cn = 1`, `ε = 1/10`, window point `z_i = 2^{-11} I` (in `[N^{-3/2}, N^{-1/2}] = [2^{-31.5}, 2^{-10.5}]`), `B = 2^47`.
Targets 3-4: `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/2`, `E = 1`, `nf = 2`, `Cn = τ₀ = 1`.
Kernel bound used for `Bd`, `B` (η = Im z): `‖(G G)_aa‖ ≤ η^{-2}`, `‖G_bb‖ ≤ η^{-1}`, so
`L1t ≤ 4 · N^{-1} Σ_{xy}|S°_{xy}| η^{-3} = 4 Σ_b |SBR_{0b} - L^{-d}| η^{-3}` (block form: `S_{xy} = W^{-d} SBR_{ab}`, `1/N = W^{-d}L^{-d}`),
`L2t ≤ 4 N^{-2} Σ|S°| η^{-4} ≤ 8 N^{-1} η^{-4}`; `Im m ≤ η^{-1}`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2266/inst.py`
(exact `Fraction` arithmetic for kernel sums and thresholds; `float` only for the printed `N^ε`, windows, and the admissibility check). Output:

```
sz0: L,W,N,lam at n=0: 4 32 2097152 1/64 ; N(n)=2^21 (n+1)^18 for n<200: ok
block kernel row sum = 1 ; #{zdistD=1} = 6
4*sum_b|SBR_0b-L^-d| = 7.863298391028766 <= 8: True
T1: eta=1, kernel sum <= 4*S*1 + 0 = 7.863298391028766 <= Bd= 8 ; bound (1/2)(T-t)Bd = 4
N=2^21.0; window Im z in [N^(-1-tau), N^(-1+tau)] = [2^-31.50, 2^-10.50]; eta=2^-11 in window: True
B = 2^47; L1 term <= 1.383e+14 <= B; L2 term <= 6.711e+07 <= B
pin: (1/2) nf^2 = 2 <= N^eps = 4.2870938501451725 ; t*=N^(-1/2)=2^-10.5
N^eps >= nf^2/2 thresholds n0 (N=2^21 (n+1)^18) :
  eps=1/1 nf=1: least n = 0 (N=2097152)
  eps=1/1 nf=2: least n = 0 (N=2097152)
  eps=1/1 nf=5: least n = 0 (N=2097152)
  eps=1/2 nf=1: least n = 0 (N=2097152)
  eps=1/2 nf=2: least n = 0 (N=2097152)
  eps=1/2 nf=5: least n = 0 (N=2097152)
  eps=1/10 nf=1: least n = 0 (N=2097152)
  eps=1/10 nf=2: least n = 0 (N=2097152)
  eps=1/10 nf=5: least n = 1 (N=549755813888)
  eps=1/100 nf=1: least n = 0 (N=2097152)
  eps=1/100 nf=2: least n = 20 (N=1323052915536356766729237430272)
  eps=1/100 nf=5: least n = 553022 (N=49091623806516649657125479172893189037772982628346750880498529454595715215441223919216698866162019204845273088)
SizeTendsto: N(n)>=n for n<2000: True ; N(10^3)=2.135e+60, N(10^6)=2.097e+114
sz0 admissible (c=1/6,d=1/10) numerically for n<500: True ; n=0: N^(1/6)=11.314<=32, W^-1.4=0.00781<=lam=0.01562<=10
T3/T4: d=3,c=1/6,dd=1/10,kappa=1/2,E=1: |E|=1<=2-kappa=3/2: True; Cn=1,tau0=1: tau<=Cn*tau
```

External hypothesis `sz.SizeTendsto` (structural): `N(n) = (W L)^3 = (32 (n+1)^5 · 4 (n+1))^3 = 2^21 (n+1)^18`, so `N(n) → ∞`
(`N(10^3) = 2.135e60`, `N(10^6) = 2.097e114` above; `N(n) ≥ n`, as used by `sz0_tendsto`). Hypothesis `τU ≤ Cn τU`: `1/2 ≤ 1 · 1/2`.
No `N = 0`, no empty index (`Idx 3 4 32` has `2^21` points), window nonempty, every hypothesis of targets 1-4 satisfied at these numbers.

### Verdicts

- Target 1 `eq225_interval`: PASS (statement true as pinned; hypotheses satisfiable at the instance; `Bd ≥ 0` forced when `t < T`).
- Target 2 `unEMCTE2_of_sizeTendsto`: PASS (chain rows 3-6 closes; `nf = 0` is `un_emcte2_zero`).
- Target 3 `unEMCTE2Row`: PASS (`Cn = τ₀ = 1`, `hA` third conjunct gives `SizeTendsto`, `τU ≤ 1 * τU`).
- Target 4 `unEMCTE2Rowk_band`: PASS (from target 3 and `UNEMCTE2Rowk_band`).
- Target 5 instances: PASS (data above; `inst_unEMCTE2Row_sz0` needs `UNInst.sz0_adm`, checked numerically for `n < 500` and merged as `sz0_admissible`).

## (a′) Preflight corrections — Tue Oct  6 07:21:43 UTC 2026

- Finding 5 of (a) says target 4 follows from target 3 and `UNEMCTE2Rowk_band`. `UNEMCTE2Rowk` takes the bulk premise `∀ᶠ n, |E| ≤ 2 - κ` where `UNEMCTE2Row` takes `|E| ≤ 2 - κ`, so target 4 is proved from target 2 (`unEMCTE2_of_sizeTendsto`) and `UNEMCTE2k_band`. No verdict changes.

## (b) Script output — Tue Oct  6 07:21:43 UTC 2026
```
$ git log -1 --format=%h; git diff --stat main...t/T2266; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/EMCTE2.lean
709ba21
 RBM3D/Test/Axioms.lean         |   2 -
 RBM3D/Universality/EMCTE2.lean | 778 +++++++++++++++++++++++++++++++++++++++++
 2 files changed, 778 insertions(+), 2 deletions(-)
0
$ lake build RBM3D.Universality.EMCTE2 > build_mod.out; tail -1 build_mod.out
Build completed successfully (3370 jobs).
$ grep "EMCTE2.lean.*depends on axioms" build_mod.out | sed "s/.*axioms: //" | sort | uniq -c
   8 [propext, Classical.choice, Quot.sound]
$ (declarations printed by the same lines)
eq225_interval unEMCTE2_of_sizeTendsto unEMCTE2Row unEMCTE2Rowk_band EMCTE2Inst.inst_eq225_interval EMCTE2Inst.inst_unEMCTE2_sz0 EMCTE2Inst.inst_unEMCTE2Row_sz0 EMCTE2Inst.inst_unEMCTE2Rowk_band_sz0
$ lake build   # worktree RBM3D.lean unchanged (hub adds the root import)
error: RBM3D.lean:309:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `
  [RBM.Univ.UNEMCTE2Row]
exit 1
$ lake build   # RBM3D.lean temporarily with "import RBM3D.Universality.EMCTE2" after OUGenerator; restored, git status clean
Build completed successfully (4073 jobs).
errors in log: 0
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Universality.EMCTE2; #assert_rbm_axioms
exit 0; 0 lines name UNEMCTE2 or UNEMCTE2Row
axiom audit: 7765 theorems, 2576 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 95, structural 40, refuted 6, superseded 11).
registry: 2 borrowed + 155 owed + 102 structural + 7 refuted + 12 superseded; 125 registered premise(s) carry nothing 
$ git diff main -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Univ.UNEMCTE2, -- bulk universality pin (T2162 portmap P.4; T2174, UN-0
-   `RBM.Univ.UNEMCTE2Row, -- bulk universality pin (T2162 portmap P.4; T2174, U
$ lake env lean scratch.lean   # T2266-check.lean, imports RBM3D + RBM3D.Universality.EMCTE2, plus the 7 examples below; exit 0, 0 errors
T2266_eq225_interval := @RBM.Univ.eq225_interval
T2266_unEMCTE2_of_sizeTendsto := @RBM.Univ.unEMCTE2_of_sizeTendsto
T2266_unEMCTE2Row := RBM.Univ.unEMCTE2Row
T2266_unEMCTE2Rowk_band := RBM.Univ.unEMCTE2Rowk_band
T2266_inst_eq225_interval := RBM.Univ.EMCTE2Inst.inst_eq225_interval
T2266_inst_unEMCTE2_sz0 := RBM.Univ.EMCTE2Inst.inst_unEMCTE2_sz0
T2266_inst_unEMCTE2Row_sz0 := RBM.Univ.EMCTE2Inst.inst_unEMCTE2Row_sz0
```

### Target statements (sed from RBM3D/Universality/EMCTE2.lean)
```
:455-473
theorem eq225_interval (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ)
    (hz : ∀ i : Fin nf, 0 < (z i).im) (t T Bd : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hB : ∀ s ∈ Set.Ioo t T,
      ∫ ω, ((∑ i : Fin nf, (∏ j ∈ Finset.univ.erase i,
              (stieltjesN (ouMat (UNModel.band sz) n s ω) (z j)).im) *
              L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i)) +
            ∑ i : Fin nf, ∑ j ∈ Finset.univ.erase i,
              (∏ k ∈ (Finset.univ.erase i).erase j,
                (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
              L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z i) (z j))
        ∂(ouP (UNModel.band sz) n) ≤ Bd) :
    |(∫ ω, ∏ i : Fin nf, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im
          ∂(ouP (UNModel.band sz) n)) -
      ∫ ω, ∏ i : Fin nf, (stieltjesN (ouMat (UNModel.band sz) n T ω) (z i)).im
          ∂(ouP (UNModel.band sz) n)| ≤
      (1 / 2) * (T - t) * Bd := by
  classical
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    fun K => ((∏ i, (stieltjesN K (z i)).im : ℝ) : ℂ) with hΦdef
:597-598
theorem unEMCTE2_of_sizeTendsto (d : ℕ) (sz : Sizes d) (hd : sz.SizeTendsto) (E : ℝ) (nf : ℕ)
    (τU Cn : ℝ) (hτ : τU ≤ Cn * τU) : UNEMCTE2 sz E nf τU Cn := by
:683-684
theorem unEMCTE2Row : UNEMCTE2Row := by
  intro d _ 𝔠 𝔡 sz hA κ _ E _ nf
:690-691
theorem unEMCTE2Rowk_band : UNEMCTE2Rowk (fun d => UNKind.band d) := by
  intro d _ 𝔠 𝔡 sz hA κ _ E _ nf
```
### Compiled instances (namespace RBM.Univ.EMCTE2Inst, RBM3D/Universality/EMCTE2.lean:706-765; `inst_eq225_interval` :710-747 is the statement of check 2.5, proved with hypotheses discharged by `EMCTE2_hsum_bdd`)
```
theorem inst_unEMCTE2_sz0 : UNEMCTE2 sz0 0 2 (1 / 2) 1 :=
  unEMCTE2_of_sizeTendsto 3 sz0 sz0_tendsto 0 2 (1 / 2) 1 (one_mul _).ge
theorem inst_unEMCTE2Row_sz0 : ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧ UNEMCTE2 sz0 1 2 τ₀ Cn := by
  obtain ⟨Cn, τ₀, hτ₀, h⟩ := unEMCTE2Row 3 le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm (1 / 2)
    (by norm_num) 1 (by norm_num) 2
  exact ⟨Cn, τ₀, hτ₀, h τ₀ hτ₀ le_rfl⟩

theorem inst_unEMCTE2Rowk_band_sz0 : ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
    UNEMCTE2k (UNKind.band 3) sz0 1 2 τ₀ Cn := by
  obtain ⟨Cn, τ₀, hτ₀, h⟩ := unEMCTE2Rowk_band 3 le_rfl (1 / 6) (1 / 10) sz0 UNInst.sz0_adm
    (1 / 2) (by norm_num) 1 (Eventually.of_forall fun n => by
      change |(1 : ℝ)| ≤ 2 - 1 / 2
      norm_num) 2
```
### Name-clash grep and port source
```
$ grep -rnw "<name>" RBM3D RBM3D.lean | grep -v Universality/EMCTE2.lean | grep -v Probe | wc -l   (9 public names; EMCTE2_ prefix)
eq225_interval:0 unEMCTE2_of_sizeTendsto:0 unEMCTE2Row:0 unEMCTE2Rowk_band:0 EMCTE2Inst:0 inst_eq225_interval:0 inst_unEMCTE2_sz0:0 inst_unEMCTE2Row_sz0:0 inst_unEMCTE2Rowk_band_sz0:0 
EMCTE2_ outside file: 0; private decls in file: 33; public theorems: 8
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/EMCTE2.lean   (RBM2D HEAD = 9e0f275)
 RBM2D/Universality/EMCTE2.lean | 158 +++++++----------------------------------
```
Port: RBM2D `Universality/EMCTE2.lean` at c9a24cf: sections 1 (:51-127), 2 (:129-230), 3 (:232-314), 4 (:316-432), `eq225_interval` (:440-559), `emcte2Row` (:567-643), `EMCTE2Check` (:653-718).

### Narrative (at most 40 lines)

- All four targets and the instances compiled against the merged names listed in the ticket; no statement was changed, no hypothesis added, no merged file touched; files written: `RBM3D/Universality/EMCTE2.lean` (new), `RBM3D/Test/Axioms.lean` (two deletions).
- Target 1 is the RBM2D proof with these substitutions: `Idx L W` to `Idx d (sz.L n) (sz.W n)`; `gSel`/`green` to the merged `Gres` (entries measurable by `walk_measurable_Gres_apply`, bounded by `norm_apply_le_l2_opNorm` and `norm_Gsig_le_inv_eta`, for both signs `b`); `L1t`/`L2t` carry `d` and `lam`; the pointwise kernel bound is `centeredVariance_wirtProduct_kernel_bound_Lt` at `s = Finset.univ` (no `simp only [paperL*Kernel_eq_L*t]` step).
- Measurability of `ω ↦ wirtSecond Φ (ouMat (band) n s ω) a b` (RBM2D `:393` used continuity of `ouMat` on `Ω × Ω`): continuous on the pair carrier (private copies of the OUGenerator helpers, prefix `EMCTE2_`) composed with the measurable `Prod.map (slice sz n) id`; T1 is `rfl`, so the integrand is used as is. `EMCTE2_sum_integral_swap` ports with only this integrability input replaced (preflight finding 2).
- Target 2: `hd : sz.SizeTendsto` replaces RBM2D's `hd.1` (the tendsto is already real-valued, no cast); one eventual threshold `½ nf² ≤ N^ε` from `tendsto_rpow_atTop`; `N ≥ 1` from `three_le_L`, `W_pos`; the exponent step is `Real.rpow_le_rpow_of_exponent_le` with `-1 + τU ≤ -1 + Cn τU` from `τU ≤ Cn * τU`; `nf = 0` is `UNInst.un_emcte2_zero`; `nf ≥ 1` uses `Nat.cast_sub` as RBM2D `:631`.
- Targets 3 and 4: `Cn = 1`, `τ₀ = 1`, `hA.2.2.1`, `(one_mul τU).ge`. Neither the row's `|E| ≤ 2 - κ` nor the band bulk premise is used.
- Instances: `inst_eq225_interval` (target 1 at `sz0`, `n = 0`, `nf = 1`, `z = ![I]`, `t = 0`, `T = 1`, with `hB` discharged by `EMCTE2_hsum_bdd`, the uniform bound of the kernel sum over Hermitian matrices); `inst_unEMCTE2_sz0` (`sz0_tendsto`); `inst_unEMCTE2Row_sz0` (`UNInst.sz0_adm`); `inst_unEMCTE2Rowk_band_sz0` (extra: target 4 at the same data, bulk premise `|1| ≤ 2 - 1/2` by `norm_num`). No premise of the instances is another gate's pin.
- Known Lean drift: `integral_finsetSum` is used (the deprecated `integral_finset_sum` is not); `if_neg` is not used; no `simp` unfolds `card (Idx d L W)`; the module build log has 0 occurrences of `deprecated`.
- Scope: `Apriori` half (UN-18b), `UNEMCTE2k` (generic pin), `UNEMCTE2RowBA`, `UNClaimRow`, `UNJak*`, `UNUyw*`, `UNUnivMainRow` are not targets and are not touched. The registry keeps `UNEMCTE2k`, `UNEMCTE2Rowk`, `UNEMCTE2RowBA`.
- The module build prints 4 long-line warnings, all in the module docstring (lines 20, 24, 34, 36); the `set_option linter.style.longLine false` comes after the docstring (as in `OUGenerator.lean`).
- Full `lake build` in this worktree fails by itself because the root `RBM3D.lean` is the hub's file and lacks `import RBM3D.Universality.EMCTE2`, so `UNEMCTE2Row` is an unregistered unproved premise; with that import added temporarily (and restored), the full build passes (second `lake build` above).

## (c) Verified Mathlib names (all compiled in `EMCTE2.lean`)

`integral_ofReal`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integrable_finsetSum`, `MeasureTheory.integral_const_mul`, `MeasureTheory.integral_add`, `MeasureTheory.norm_integral_le_integral_norm`, `MeasureTheory.integral_mono_of_nonneg`, `MeasureTheory.integral_mono`, `Integrable.of_bound`, `measurable_deriv`, `intervalIntegral.integral_add_adjacent_intervals`, `intervalIntegral.norm_integral_le_of_norm_le_const_ae`, `intervalIntegral.integral_undef`, `intervalIntegrable_iff`, `Real.rpow_le_rpow_of_exponent_le`, `tendsto_rpow_atTop`, `Finset.card_erase_of_mem`, `Nat.cast_sub`, `Complex.measurable_ofReal`, `Complex.abs_im_le_norm`, `measurable_subtype_coe`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates

- T2266a (1) (design, no paper statement): `UNEMCTE2` is proved under `sz.SizeTendsto` and `τU ≤ Cn * τU` (target 2); the merged statement has no size hypothesis, and the registry line is deleted because `UNEMCTE2Row` (target 3) and `UNClaimRow` reach it at admissible sizes. As stated by the ticket; the statement as written was proved, not changed.
- T2266a (2): the ticket's correction to T2261a (3) (the model-generic flow `ouMatC` is centred, so the BA kind has no drift term; `UNEMCTE2RowBA` needs a mean shift and a carrier transfer at coupling `0`). This stage did not check it (BA files not read).
- T2266a (3): `UNEMCTE2Rowk (fun d => UNKind.band d)` is proved (target 4); the bulk premise is unused.
- Correction to (a), finding 5: see (a′) (target 4 goes through target 2, not target 3).
- For the hub at merge: add `import RBM3D.Universality.EMCTE2` after `import RBM3D.Universality.OUGenerator` in `RBM3D.lean`; `Axioms.lean` differs from main by exactly the two deleted lines `UNEMCTE2`, `UNEMCTE2Row`; no registry line is added.
