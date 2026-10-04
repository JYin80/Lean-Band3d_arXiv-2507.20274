Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 02:05:14 UTC 2026

Sources: RBM2D `Green/FlucIter.lean` at `c9a24cf` (1877 lines, `git --no-optional-locks show c9a24cf:...`; Part 2 = `:819–:1877`, key statement at `:1453`); merged `RBM3D/Green/{FlucVanish,LDE}.lean`. Scripts (no Lean): `<scratchpad>/T2096/check.py`, `stir.py`.

### (i) Exponent table, statements that change, uniform-to-bounded replacements

d-token census of Part 2 (grep on `c9a24cf:819–1877`): `Z2` 2 (both in check 4), `svar ` 3 (check 3 and its docstring), `UniformWeight` 3 (`:967`, `:1024`, `:1458`), `uniformWeight_*` 2 (checks 3, 4), `hw.mass` 1 (`:1017`), `hw.mem` 1 (`:996`), `hw.not_mem` 1 (`:991`), `hw.nonneg` 5, `flucVanish_card_*` 2, `W ^ 2` 0, `L ^ 2` 0. All other tokens are the renames `d : Sizes` -> `sz : Sizes d`, `spectralZ/spectralM` -> `zt/mE`, `d.L n` -> `sz.L n`.

| Item | Value / constraint | Slack at the instance |
|---|---|---|
| counting `loneSlots`, `image_loneSlots_eq`, `two_mul_card_image_le_add_card_loneSlots`, `card_filter_card_image_le` | generic `ι κ`, no `d`; `2·#im v ≤ #ι + #lone(v)` | identical at d ≥ 3; checked on all `v ∈ [4]^n`, n = 2,3,4 (script) |
| `OpsOkOut.length_le`, `..._graded`, `..._qRow_graded`, `FlucGainUpTo'`, `..._le_budget` | no weight, no `d`-exponent; factor `(2 max(1,ρ))^{(2p-1)#R} ρ^{#R} B^{2p}` | ported with renames only |
| weight `c` | `c = W^{-d}` (`boundedWeight_svarF`, `FlucVanish.lean:1170`; block average `uniformWeight_blockAvg2`, `c = (W^d)⁻¹`) | d = 3, W = 2: `c = 1/8` |
| support `#A` | row: `(2d+1)W^d` (`flucVanish_card_svarSupport_eq`); block: `W^d` (`flucVanish_card_blockSupport`) | row 56, block 8 |
| mass `c·#A` | row: `2d+1 = 7 > 1`; block: `1`. RBM2D `hw.mass : c·#A ≤ 1` is false for the row at d ≥ 3 | `UniformWeight` false for the row (`not_uniformWeight_svarF`) |
| `hcρ : c ≤ ρ²` | `ρ ≥ W^{-d/2}` (RBM2D: `ρ ≥ W⁻¹`) | `ρ = 1`: 1/8 ≤ 1; `ρ = 1/2`: 1/8 ≤ 1/4, factor 2 (RBM2D block family was tight at `ρ = W⁻¹`) |
| `ρ ≤ 1`, `hp : 2p ≤ #A`, `hM, hK : 2p ≤ M, K` | unchanged | `#A = 56 ≥ 4`; M = K = 2p |
| crude gain (`flucIter_flucGainUpTo'_of_crude`) | `2^q·2(η⁻¹+1) ≤ B ρ^q`, `q ≤ M`; `η = Im zt E t` | E = 0, t = u = 1/2: `η = 1/2`, `2(η⁻¹+1) = 6`; `ρ = 1`: `B = 6·2^M` (M = 4: 96) |
| budget `(2p+1)(2p)^{2p}(2^{2p-1}ρB)^{2p}` | d-free formula | p = 1, `(24,1)`: 27648; p = 2, `(96,1)`: 4.45e14 |

**The one statement that changes: `sum_prod_abs_card_image_le`** (`:966`, ported under the same name). RBM2D hypothesis `hw : UniformWeight t c A` is used at three places: `hw.not_mem` (terms outside `A` vanish; replaced by `BoundedWeight.not_mem`, same), `hw.mem` + `hw.nonneg` in `hval : ∏|t(v i)| = c^n` (DECISIONS §30: replaced by `∏ t(v i) ≤ c^n` using `BoundedWeight.nonneg`, `.le`), and `hw.mass` in `(c·#A)^s ≤ 1` (the step `pow_le_one₀` of the calc). The first two are one-for-one. **The third cannot be ported:** `c·#A = 2d+1 = 7` at the instance, so the ported chain `|G| c^n ≤ (c #A)^s c^{n-s} s^n ≤ c^{n-s} s^n` loses the factor `7^s` (script below: factors 7, 49, 343, 2401). So the Lean proof of this lemma and of the `sum_weighted_le` call must change; the budget statement still holds (finding, not a stop: no step needs an equality, only the mass step needs a different argument). Two routes, both true at d ≥ 3:
- **Route A (sharp, keeps the pinned conclusion `≤ c^{n-s} s^n` and the budget constants).** Hypotheses `BoundedWeight t c A`, `s ≤ n`, `Fintype.card ι = n`, plus `c ≤ 1` (new; `sum_weighted_le` has it from `c ≤ ρ² ≤ 1`). Group `v` by its kernel (the set partition of `ι` into fibres). For a partition with blocks of sizes `b_1..b_m`: `∑_{v with that kernel} ∏ t(v i) ≤ ∏_j ∑_x t(x)^{b_j} ≤ ∏_j c^{b_j-1} ∑_x t(x) ≤ c^{n-m}` (`t ≥ 0`, `t ≤ c`, `∑ t ≤ 1`; `t(x)^b ≤ c^{b-1} t(x)`). `c ≤ 1` gives `c^{n-m} ≤ c^{n-s}` for `m ≤ s`. The number of set partitions with `≤ s` blocks is `∑_{m≤s} S(n,m) ≤ s^n` (each is the kernel of some `ι → Fin s`). Support `A` and `hs : s ≤ #A` are not used; `hp : 2p ≤ #A` of the budget becomes unused (keep it, to keep the signature).
- **Route B (mechanical fallback).** Keep `card_filter_card_image_le` (count `≤ #A^s s^n`), replace `(c #A)^s ≤ 1` by `(c #A)^s ≤ max(1, c·#A)^n`: conclusion `max(1,c·#A)^n · c^{n-s} s^n`, and the budget gains the factor `(2d+1)^{2p}` at the row family. This changes a pinned constant: paper-delta candidate `T2096a`; use only if Route A is not finished.

Other uses of the uniform weight: only in the checks. Check 3 (`uniformWeight_svar`, false at d ≥ 3) becomes `boundedWeight_svarF hL g i`; check 4 uses `uniformWeight_blockAvg2 ...toBoundedWeight`. Check sizes: `Sizes 3` with `L = 3`, `W = 2`, any `lam` (e.g. `1/64`; no constraint on `lam` in the structure, `Defs/Sizes.lean:138`).

### (ii) Nondegenerate instance and numeric check (d = 3, L = 3, W = 2, g = 1/2)

Data: `N = (WL)^d = 216`, `i = (0,0,0)`, `T_j = S_{ij}` (the row, support = 7 blocks × 8 = 56 sites, values 0.05 on the own block and 0.0125 on the six neighbouring blocks), `c = W^{-3} = 1/8`, `p ∈ {1,2}`, `M = K = 2p`, `E = 0`, `t = u = 1/2` (so `zt = i/2`, `mE = i`, `m = -(t m + z)⁻¹` asserted in the script, `η = 1/2`; `|E| < 2`, `t < 1`). `H = √u X` Hermitian, `E|X_ij|² = S_ij`, real Gaussian diagonal, `G = (H - z)⁻¹`. The left side is `E‖∑_k T_k Z_k‖^{2p}`, `Z_k = (1-E_k)(G_kk - m)`. `E_k` is estimated by 16 inner samples of the row `k` (Schur complement `G_kk = 1/(H_kk - z - h*G^{(k)}h)`, minor from `G` by the rank-one identity), `10^4` outer samples; terms with `T_k = 0` are omitted (they have weight 0). The budget is evaluated at the crude gain pair `(B, ρ)` (the only gain available without a local law): `B = max_{q≤2p} 2^q·6/ρ^q`.
```
$ cd <scratchpad>/T2096 && python3 check.py 10000 16    (1195 s)
N 216 W^d 8 row sum 1.0 #A 56 (2d+1)W^d 56
max T 0.05 <= c 0.125 ; c*#A = 7.0 (>1: UniformWeight.mass fails); distinct nonzero values [0.0125, 0.05]
n= 2 2|im|<=n+lone on [4]^n: True
n= 3 2|im|<=n+lone on [4]^n: True
n= 4 2|im|<=n+lone on [4]^n: True
n=2 s=1: sum_(|im|<=s) prod T = 0.0275 <= c^(n-s) s^n = 0.125: True
n=2 s=2: sum_(|im|<=s) prod T = 1 <= c^(n-s) s^n = 4: True
n=4 s=1: sum_(|im|<=s) prod T = 5.11719e-05 <= c^(n-s) s^n = 0.00195312: True
n=4 s=2: sum_(|im|<=s) prod T = 0.00633672 <= c^(n-s) s^n = 0.25: True
n=4 s=3: sum_(|im|<=s) prod T = 0.154288 <= c^(n-s) s^n = 10.125: True
n=4 s=4: sum_(|im|<=s) prod T = 1 <= c^(n-s) s^n = 256: True
eta 0.5 envelope b=2(1/eta+1) = 6.0
p=1 rho=1.0 B(crude)=24 c<=rho^2: True budget=27648
p=1 rho=0.5 B(crude)=96 c<=rho^2: True budget=110592
p=2 rho=1.0 B(crude)=96 c<=rho^2: True budget=4.45302e+14
p=2 rho=0.5 B(crude)=1536 c<=rho^2: True budget=1.82396e+18
MC outer=10000 inner K=16 time 1195s; max|G_kk-m| observed 0.661
p=1: E||flucAvg||^2 ~ 0.001308 (se 1.4e-05)
p=2: E||flucAvg||^4 ~ 3.718e-06 (se 9.3e-08)
$ python3 stir.py
sum_{m<=s} S(n,m) <= s^n for all 1<=s<=n<=8: True
n=2 s=1: old chain factor (c*#A)^s = 7 (>1 -> `pow_le_one` step fails); partition bound sum_m S(n,m) c^(n-m) = 0.125 <= c^(n-s) s^n = 0.125
n=2 s=2: old chain factor (c*#A)^s = 49 (>1 -> `pow_le_one` step fails); partition bound sum_m S(n,m) c^(n-m) = 1.125 <= c^(n-s) s^n = 4
n=4 s=1: old chain factor (c*#A)^s = 7 (>1 -> `pow_le_one` step fails); partition bound sum_m S(n,m) c^(n-m) = 0.00195312 <= c^(n-s) s^n = 0.00195312
n=4 s=2: old chain factor (c*#A)^s = 49 (>1 -> `pow_le_one` step fails); partition bound sum_m S(n,m) c^(n-m) = 0.111328 <= c^(n-s) s^n = 0.25
n=4 s=3: old chain factor (c*#A)^s = 343 (>1 -> `pow_le_one` step fails); partition bound sum_m S(n,m) c^(n-m) = 0.861328 <= c^(n-s) s^n = 10.125
n=4 s=4: old chain factor (c*#A)^s = 2401 (>1 -> `pow_le_one` step fails); partition bound sum_m S(n,m) c^(n-m) = 1.86133 <= c^(n-s) s^n = 256
```
Reading: at `p = 1` the left side is `1.3e-3` against the budget `27648` (`(B,ρ) = (24,1)`) and `110592` (`(96,1/2)`); at `p = 2` it is `3.7e-6` against `4.45e14` and `1.82e18`. The inequality holds with a huge slack because the budget uses only the gain-free crude pair; the instance checks that all hypotheses (`|E|<2`, `t<1`, `ρ ≤ 1`, `c ≤ ρ²`, `2p ≤ #A = 56`, `M = K = 2p`, bounded weight with `c·#A = 7`) hold at once, not the sharpness of the budget. The stratified bound `∑_{|im v| ≤ s} ∏ T ≤ c^{n-s} s^n` holds with the true row at `n = 2, 4`, all `s` (the partition bound `∑_m S(n,m) c^{n-m}` equals `c^{n-s} s^n` exactly at `s = 1`, see `stir.py`). External hypothesis: none (`FlucGainUpTo'` is a hypothesis of the consumers, discharged gain-free in the checks as in RBM2D, which needs no limit computation).

### Verdict
- The other declarations of Part 2 (counting, graded iteration, `FlucGainUpTo'`, `..._le_budget`, crude gain, checks with renames): **PASS** (no exponent depends on `d`; checks 3 and 4 switch to bounded weights as above).
- `sum_prod_abs_card_image_le`, `sum_weighted_le`, `integral_norm_flucAvg_pow_le_iter_budget` (bounded weight): **PASS**, with the finding that `hw.mass` cannot be replaced one-for-one; use Route A (or Route B with paper-delta `T2096a`). Statement true at d ≥ 3 (numerics above, proof sketch Route A).
- Overall: **PASS**.

## (b) Script output — Sun Oct  4 02:29:17 UTC 2026

b.1, b.4–b.6 and b.7 items 1, 5–8 are the round-1 output at commit `43782c0` (line numbers of that commit); b.2, b.3, b.7 item 3 and (d) are updated to the repair commit `e16dab6`; see `## Repair (round 1)` at the end.

### b.1 Branch, hygiene, builds, axioms
```
$ date -u; git log -1 --format="%h %s"; git diff --name-only main...t/T2096
Sun Oct  4 02:29:01 UTC 2026
43782c0 T2096: S1-21 Green/FlucIterGain (counting, graded iteration, moment budget, bounded weights)
RBM3D/Green/FlucIterGain.lean
RBM3D/Test/Axioms.lean
$ grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/Green/FlucIterGain.lean
0
$ lake build RBM3D.Green.FlucIterGain   # run 02:21:59Z-02:22:04Z; output kept in modbuild.txt:
grep -n "FlucIterGain\|Build completed" modbuild.txt
80:✔ [3333/3333] Built RBM3D.Green.FlucIterGain (3.0s)
81:Build completed successfully (3333 jobs).
82:lake build RBM3D.Green.FlucIterGain  9.89s user 4.55s system 248% cpu 5.805 total
$ lake build   # full library, run 02:22:08Z-02:22:32Z (root #assert_rbm_axioms included); output kept in fullbuild.txt:
grep -n "Build completed" fullbuild.txt
746:Build completed successfully (3841 jobs).
$ lake env lean axioms_check.lean > axioms_out.txt   # scratch: import RBM3D.Green.FlucIterGain + 37 lines "#print axioms <public name>"; exit 0
grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]" axioms_out.txt; grep -vc <same> axioms_out.txt
37
0
$ grep -E "integral_norm_flucAvg_pow_le_iter_budget|sum_prod_abs_card_image_le|sum_weighted_le|moment_row_p2" axioms_out.txt | sed "s/RBM.Green.//"
'sum_prod_abs_card_image_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'sum_weighted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'integral_norm_flucAvg_pow_le_iter_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'FlucIterGainInst.moment_row_p2' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b.2 Target statements, extracted from the file by script (`extract.py`: first line of the declaration to its first `:=`)
```
$ for n in sum_prod_abs_card_image_le sum_weighted_le integral_norm_flucAvg_pow_le_iter_budget; do awk -v n="$n" '$0 ~ "^theorem "n" " {f=1} f{print NR": "$0} f && /:= by/{f=0}' RBM3D/Green/FlucIterGain.lean; done   # at repair commit e16dab6
371: theorem sum_prod_abs_card_image_le {t : κ → ℝ} {c : ℝ} {A : Finset κ}
372:     (hw : BoundedWeight t c A) {s n : ℕ} (_hs : s ≤ A.card) (hsn : s ≤ n)
373:     (hcard : Fintype.card ι = n) :
374:     ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter
375:         (fun v => ((Finset.univ : Finset ι).image v).card ≤ s), ∏ i, |t (v i)|
376:       ≤ c ^ (n - s) * (s : ℝ) ^ n := by
395: theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : BoundedWeight t c A)
396:     {n : ℕ} (hcard : Fintype.card ι = n) (hn : n ≤ A.card)
397:     {ρ B K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hK : 1 ≤ K) (hB : 0 ≤ B)
398:     (hcρ : c ≤ ρ ^ 2) {f : (ι → κ) → ℝ}
399:     (hf : ∀ v, f v ≤ K ^ (loneSlots v).card * ρ ^ (loneSlots v).card * B ^ n) :
400:     ∑ v : ι → κ, (∏ i, |t (v i)|) * f v
401:       ≤ ((n : ℝ) + 1) * (n : ℝ) ^ n * (K * ρ * B) ^ n := by
823: theorem integral_norm_flucAvg_pow_le_iter_budget (hE : |E| < 2) (ht : t < 1) {u : ℝ}
824:     {B ρ c : ℝ} {M K : ℕ} {A : Finset (Idx d (sz.L n) (sz.W n))} {T : Idx d (sz.L n) (sz.W n) → ℝ}
825:     (hg : FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K) (hM : 2 * p ≤ M)
826:     (hK : 2 * p ≤ K)
827:     (hρ1 : ρ ≤ 1) (hcρ : c ≤ ρ ^ 2)
828:     (hw : BoundedWeight T c A) (hp : 2 * p ≤ A.card) :
829:     ∫ ω, ‖flucAvg sz n u (zt E t) (mE E) T ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
830:       ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
831:         * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) := by
$ sed -n 727,734p RBM3D/Green/FlucIterGain.lean   # FlucGainUpTo' (moved from 704 by the repair, text unchanged)
def FlucGainUpTo' (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
      (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
      ∫ ω, ∏ i, ‖applyOps sz n (L i) (flucDiag sz n u z m (k i)) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)
```
### b.3 Statement diff against RBM2D `c9a24cf` after renaming (ST1-COMMON item 6)
```
$ python3 stmt_diff.py   # RBM2D c9a24cf :819-:1877 (git show), renamed by the R1-R4/zt/mE regexes of port.py, against FlucIterGain.lean (signatures up to ":=")
(round-1 output for the three DIFFER lines replaced by the repair run below)
$ python3 sdiff_r.py sum_prod_abs_card_image_le sum_weighted_le integral_norm_flucAvg_pow_le_iter_budget   # scratch; same renaming, at e16dab6
DIFFER sum_prod_abs_card_image_le
    replace RBM2D: UniformWeight | RBM3D: BoundedWeight
    replace RBM2D: (hs | RBM3D: (_hs
DIFFER sum_weighted_le
    replace RBM2D: UniformWeight | RBM3D: BoundedWeight
DIFFER integral_norm_flucAvg_pow_le_iter_budget
    replace RBM2D: UniformWeight | RBM3D: BoundedWeight
SAME after renaming (16): loneSlots, mem_loneSlots, image_loneSlots_eq, two_mul_card_image_le_add_card_loneSlots, card_filter_card_image_le, bddMeas_epsHom_flucDiag, OpsOkOut.length_le, norm_integral_prod_applyOps_le_graded, norm_integral_prod_qRow_le_graded, FlucGainUpTo', FlucGainUpTo'.B_nonneg, FlucGainUpTo'.rho_nonneg, FlucGainUpTo'.gain, norm_integral_prod_epsHom_flucDiag_le_budget, flucIter_integral_prod_norm_applyOps_le_crude, flucIter_flucGainUpTo'_of_crude
differences: 3
```
### b.4 Compiled nonempty instances (d = 3, L = 3, W = 2, g = 1/2, E = 0, t = 1/2, every `u` (the preflight uses `u = 1/2`); `szG`, constant sequences, slice 0)
Key statement at the true row (`boundedWeight_svarF`, c = 1/8, #A = 56, c·#A = 7) at p = 1 and p = 2, and at the block average; weight-sum lemmas at the row; the rest in the namespace list below.
```
$ python3 extract.py moment_row_p1 moment_row_p2 moment_block_p1 sum_prod_abs_card_image_row sum_weighted_row rowA_card blockA_card
1103: theorem moment_row_p1 (u : ℝ) :
1104:     ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) rowW ω‖ ^ (2 * 1) ∂(Sizes.seqP szG)
1105:       ≤ 110592 := by
1114: theorem moment_row_p2 (u : ℝ) :
1115:     ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) rowW ω‖ ^ (2 * 2) ∂(Sizes.seqP szG)
1116:       ≤ 445302209249280 := by
1143: theorem moment_block_p1 (u : ℝ) :
1144:     ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) blockW ω‖ ^ (2 * 1) ∂(Sizes.seqP szG)
1145:       ≤ 110592 := by
1078: theorem sum_prod_abs_card_image_row :
1079:     ∑ v ∈ (Finset.univ : Finset (Fin 2 → Idx 3 (szG.L 0) (szG.W 0))).filter
1080:         (fun v => ((Finset.univ : Finset (Fin 2)).image v).card ≤ 1), ∏ i, |rowW (v i)|
1081:       ≤ 1 / 8 := by
1089: theorem sum_weighted_row :
1090:     ∑ v : Fin 2 → Idx 3 (szG.L 0) (szG.W 0), (∏ i, |rowW (v i)|)
1091:         * (((1 : ℝ) * (1 / 2)) ^ (loneSlots v).card * (1 : ℝ) ^ 2)
1092:       ≤ (((2 : ℕ) : ℝ) + 1) * ((2 : ℕ) : ℝ) ^ 2 * ((1 : ℝ) * (1 / 2) * 1) ^ 2 := by
1072: theorem rowA_card : rowA.card = 56 := by
1137: theorem blockA_card : blockA.card = 8 := by
$ grep -n -E '^theorem' RBM3D/Green/FlucIterGain.lean | awk -F: '$1>949' | sed 's/ (u : ℝ)//; s/ :.*//' | tr '\n' ';'
991:theorem flucGainUpTo'_szG_projections;1005:theorem flucGainUpTo'_szG_gain;1026:theorem counting_values;1031:theorem counting_two_mul;1036:theorem counting_image_lone;1043:theorem counting_mem_lone;1048:theorem counting_card_filter;1072:theorem rowA_card;1078:theorem sum_prod_abs_card_image_row;1089:theorem sum_weighted_row;1103:theorem moment_row_p1;1114:theorem moment_row_p2;1137:theorem blockA_card;1143:theorem moment_block_p1;1155:theorem bddMeas_epsHom_flucDiag_szG;1167:theorem iter_epsHom_budget;1208:theorem opsOkOut_length_le_szG;1217:theorem iter_graded;1236:theorem iter_qRow;1253:theorem iter_comm;
```
### b.5 Registry pre-check (ST1-COMMON item 8; the root file does not import the new module, so this scratch file does)
```
$ cat registry_check.lean; lake env lean registry_check.lean > registry_out.txt 2>&1; echo "exit $?"; grep -n "FlucGainUpTo\|STLoopGenNForm\|axiom audit:\|premises found" registry_out.txt   # scratch files in <scratchpad>/T2096
import RBM3D
import RBM3D.Green.FlucIterGain

#assert_rbm_axioms
exit 0
1:axiom audit: 3152 theorems, 1154 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
111:  RBM.Ind.STLoopGenNForm: 2 [no certificate]
113:  RBM.Green.FlucGainUpTo': 2 [no certificate]
114:premises found by scanning: 84 (borrowed 2, owed 67, structural 15).
$ git diff main...t/T2096 -- RBM3D/Test/Axioms.lean | grep -E "^[+-] "
-   `RBM.Gauss.Sizes.STLocalEntry] -- local law for the entries, a hypothesis of `lem:LWterm_EXP`: first used by T2067
+   `RBM.Gauss.Sizes.STLocalEntry, -- local law for the entries, a hypothesis of `lem:LWterm_EXP`: first used by T2067
+   `RBM.Green.FlucGainUpTo'] -- gain interface of the higher-order minor expansion `(GavLGEX)` (`3_5:33`): hypothesis of the budget and moment bounds of T2096; proved by S1-22 `flucGainUpTo'_of_minorDiffGainUp
```
### b.6 Name-clash grep (CLAUDE.md §5.2) and the RBM2D port (source commit, diff-stat, d = 2 token census of `:819-:1877`)
```
$ bash clash.sh   # scratch; for each of the 37 names of public_names.txt: git --no-optional-locks grep -n -E "^(private )?(theorem|def|lemma|structure|abbrev|instance) (RBM.Green.)?<short name>" main -- RBM3D
declarations of the 37 public names found on main (RBM3D/): 0
$ # positive control of the pattern, short=predSplit (merged T2089 name):
git --no-optional-locks grep -n -E <same pattern> main -- RBM3D
main:RBM3D/Green/FlucIter.lean:77:def predSplit (sz : Sizes d) (p : Sizes.SeqCoord sz → Pr
$ git --no-optional-locks grep -n -E "loneSlots|FlucGainUpTo|integral_norm_flucAvg_pow_le_iter_budget|sum_weighted_le|sum_prod_abs_card_image_le|flucIterGain_" main -- RBM3D RBM3D.lean | cut -c1-110
main:RBM3D/Green/FlucIter.lean:46:The counting section (`:828`, `loneSlots`, ...) and everything after it, wit
main:RBM3D/Green/FlucIter.lean:47:`integral_norm_flucAvg_pow_le_iter_budget` (`:1453`), are S1-21.
main:RBM3D/Green/FlucIter.lean:701:(`norm_applyOps_le`); this is what makes the gain interface `FlucGainUpTo'`
$ git -C ../RBM2D --no-optional-locks log -1 --format="%h %s" c9a24cf; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/FlucIter.lean
c9a24cf T2273: merge dead-code closure tool and report
 RBM2D/Green/FlucIter.lean | 428 ++++------------------------------------------
 1 file changed, 36 insertions(+), 392 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/FlucIter.lean | sed -n '819,1877p' | grep -o -E 'W⁻²|L⁻²|W \^ 2|Z2|zdist|svar |UniformWeight|uniformWeight_[a-zA-Z0-9]*|d = 2|⁻¹ \^ 2' | sort | uniq -c
   3 ⁻¹ ^ 2
   2 svar 
   3 UniformWeight
   1 uniformWeight_blockAvg2
   1 uniformWeight_svar
   1 W⁻²
   2 Z2
```
### b.7 Narrative
1. `RBM3D/Green/FlucIterGain.lean` (1265 lines, `namespace RBM.Green`, imports `RBM3D.Green.FlucIter` only) ports RBM2D `Green/FlucIter.lean` `:819-:1877` at `c9a24cf`: counting (`loneSlots`, ...), the stratified weight sum, `OpsOkOut.length_le`, the graded iteration, `FlucGainUpTo'`, the budget and the moment bound `:1453`, and the two crude-gain helpers (private). Of the 19 signatures compared in b.3, 16 are RBM2D's after renaming; the other three differ only in the weight (items 2, 3).
2. DECISIONS §30: RBM2D uses `t = c` once, at `:996` (`hw.mem`, in `hval : ∏|t (v i)| = c^n`); no step needs equality. The mass step `:1017` (`pow_le_one₀ ... hw.mass`, i.e. `(c·#A)^s ≤ 1`) cannot be ported: at the instance `c·#A = (1/8)·56 = 7` (b.4 `rowA_card`), as preflight (a) found.
3. `sum_prod_abs_card_image_le` is re-proved (Route A of (a)). A multi-index with at most `s` values is `w ∘ φ` with `φ : ι → Fin s`; for fixed `φ` the sum over the assignments `w` (default value `x₀` off the range of `φ`) is a product of one-letter sums `∑_x t_x^{n_b} ≤ c^{n_b-1}` (from `t_x^b ≤ c^{b-1} t_x`, `∑ t ≤ 1`; private `flucIterGain_sum_pow_le`, `flucIterGain_sum_comp_le`); the `s^n` labellings give `≤ c^{n-s} s^n`, using `c ≤ 1` for `c^{n-m} ≤ c^{n-s}` (private `flucIterGain_sum_prod_abs_card_image_le_of_le_one`). The public lemma has RBM2D's signature with `UniformWeight → BoundedWeight` (b.3; `hs` named `_hs`, unused): it applies the private bound at `min c 1` (a bounded weight has `t k ≤ ∑ t ≤ 1` by `Finset.single_le_sum`) and uses `(min c 1)^{n-s} ≤ c^{n-s}`. `sum_weighted_le` passes `hs` as `le_trans hsan hn`. Route B (a changed constant) was not needed.
4. `d`-dependence. Counting, graded iteration, `FlucGainUpTo'` and the budget formula carry no `d`. The weights: `c = W^{-d}`, `#A = (2d+1) W^d` (row), `#A = W^d` (block); `hcρ : c ≤ ρ²` reads `ρ ≥ W^{-d/2}` (RBM2D: `ρ ≥ W⁻¹`); the instance values `c = 1/20, 1/4` of RBM2D checks 3, 4 become `1/8` (d = 3, W = 2). The `d = 2` tokens of `:819-:1877` (census in b.6) sit in the three `UniformWeight` hypotheses (`:967`, `:1024`, `:1458`) and in checks 3, 4 (`:1623-:1658`): replaced by `BoundedWeight`, `boundedWeight_svarF` (for `svar`, `uniformWeight_svar`), `uniformWeight_blockAvg2 ... .toBoundedWeight` with `split ... = 0` (for `Z2`, `blk`), `(W^3)⁻¹` (for `W⁻²`, `⁻¹ ^ 2`).
5. Instances (b.4): gain-free `FlucGainUpTo'` at `(B, ρ, M, K) = (96, 1/2, 2, 2)` (tight at `q = 2`) and `(96, 1, 4, 4)` (tight at `q = 4`) with `η = 1/2` (`eta_eq`); these two are private, because a public theorem concluding `FlucGainUpTo' ...` would make the premise scan treat the interface as proved. The key statement is applied at the true row for `p = 1` (bound 110592) and `p = 2` (445302209249280) and at the block average for `p = 1`; the weight-sum lemmas at the row; the counting lemmas at `v = (0,0,1,2)` and on `Fin 3`; the iteration lemmas at the sites `(0,0,0)`, `(0,0,1)`. All deterministic hypotheses are discharged; the gain is the gain-free interface; no external hypothesis; constant size sequences, no limit claimed.
6. Registry (DECISIONS §20): `FlucGainUpTo'` is a `Prop` that the budget and moment theorems take as hypothesis and no public theorem here proves; registered as owed (one line at the end of `owedProps`: S1-22 `flucGainUpTo'_of_minorDiffGainUpTo'`; class proposed, dispatcher to confirm). The scan with the module reports `FlucGainUpTo': 2` (b.5).
7. `main` moved while I worked (T2095 merge `9bb2cbe`, one new line at the end of `owedProps`). I rebased `t/T2096` on it (one conflict in `Test/Axioms.lean`, resolved by keeping both lines); the builds, axioms and pre-check in b.1, b.5 are on the rebased commit `43782c0`.
8. Preflight (a) needed no correction; its instance (E = 0, t = 1/2, `u` arbitrary and in particular `1/2`, `c = 1/8`, `#A` = 56 and 8, pairs `(96, 1/2)` and `(96, 1)`) is the compiled one.

## (c) Verified Mathlib names (all used in `FlucIterGain.lean`, which compiles)
- `Finset.sum_image_le_of_nonneg` (additive form of `prod_image_le_of_one_le`, `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:326`); `Finset.prod_le_prod₀` (`.../GroupWithZero/Finset.lean:39`); `pow_le_pow_of_le_one` (`.../GroupWithZero/Basic.lean:429`).
- `Finset.prod_fiberwise'` (`Algebra/BigOperators/Group/Finset/Basic.lean:287`); `Finset.card_eq_sum_card_fiberwise` (`:993`); `Finset.prod_univ_sum` (`Algebra/BigOperators/Ring/Finset.lean:157`); `Finset.prod_pow_eq_pow_sum`; `Finset.sum_sigma`; `Finset.mem_sigma`; `Fintype.mem_piFinset`; `Finset.sum_le_sum_of_subset_of_nonneg`.
- `Function.Embedding.nonempty_of_card_le`; `Fintype.card_fun`; `Fintype.card_eq_zero`; `Finset.univ_eq_empty` (`Data/Finset/BooleanAlgebra.lean:73`); `ite_eq_left`, `ite_eq_right`.
- Verified changed in this Mathlib: `if_pos`, `if_neg`, `dif_pos` are deprecated (compiler warnings: `if_pos` → `ite_eq_left`, `if_neg` → `ite_eq_right`, `dif_pos` → `dite_eq_left`); `Finset.prod_le_prod` takes the single hypothesis `f i ≤ g i` (`Finset.lean:111`), the nonnegative two-hypothesis form is `prod_le_prod₀`.

## (d) Open issues and paper-delta candidates
- `T2096a` (proposed; a proof difference from RBM2D, not a statement difference): RBM2D `sum_prod_abs_card_image_le` (`:966`) is proved through the mass bound `c·#A ≤ 1` of the uniform weight (`:1017`), false for the row of `S` at `d ≥ 3` (`c·#A = 2d + 1`); Lean proves the same statement (RBM2D's signature with `UniformWeight → BoundedWeight`) by the labelling argument at the bound `min c 1`; `hs : s ≤ #A` is unused. The budget constants are unchanged. `T2061a` (bounded weight, DECISIONS §30) is cited, not re-proposed.
- Consumers (S1-22, S1-30): the key statement takes `BoundedWeight` (a uniform weight gives one by `.toBoundedWeight`); at the row `hcρ` means `ρ ≥ W^{-d/2}`.
- Hypothesis kept for the signature although the proof does not use it: `hs` of `sum_prod_abs_card_image_le` (named `_hs`); `hn` of `sum_weighted_le` and `hp` of the key statement only feed it. `card_filter_card_image_le` (RBM2D counting route) is not used by the rest of the file; it stays as ported.
- The registry class of `FlucGainUpTo'` (owed) is a proposal; only the comment on its line in `Test/Axioms.lean` would change.
- The instances show that the hypotheses are jointly satisfiable at constant sequences with the gain-free constants; they do not test sharpness of the budget.

## Repair (round 1) — Sun Oct  4 02:37:37 UTC 2026

Defects of `docs/reports/T2096-audit.md` (Required for resubmission 1–3), fixed at commit `e16dab6` on `t/T2096`.
```
$ git log -1 --format="%h %s"; git diff --name-only main...t/T2096; git diff --stat 43782c0 HEAD
e16dab6 T2096: repair round 1 — sum_prod_abs_card_image_le restored to the pinned signature
RBM3D/Green/FlucIterGain.lean
RBM3D/Test/Axioms.lean
 RBM3D/Green/FlucIterGain.lean | 73 ++++++++++++++++++++++++++++---------------
 1 file changed, 48 insertions(+), 25 deletions(-)
$ git diff -U0 43782c0 HEAD -- RBM3D/Green/FlucIterGain.lean | grep "^@@"
@@ -47,12 +47,12 @@ Everything lives at one slice `n` of a size sequence `sz : Sizes d`.
@@ -280,9 +280,7 @@ private theorem flucIterGain_sum_comp_le {β : Type*} [Fintype β] [DecidableEq
@@ -366,0 +365,26 @@ theorem sum_prod_abs_card_image_le {t : κ → ℝ} {c : ℝ} {A : Finset κ}
@@ -372 +396 @@ theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : Bounded
@@ -380 +403,0 @@ theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : Bounded
@@ -421 +444 @@ theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : Bounded
@@ -1083 +1106 @@ theorem sum_prod_abs_card_image_row :
$ lake build RBM3D.Green.FlucIterGain
✔ [3333/3333] Built RBM3D.Green.FlucIterGain (4.4s)
Build completed successfully (3333 jobs).
$ lake env lean RBM3D/Green/FlucIterGain.lean; echo "exit $?"     # no warnings in this file
exit 0
$ lake build > fullbuild_r.txt 2>&1; echo "exit $?"; tail -1 fullbuild_r.txt
exit 0
Build completed successfully (3841 jobs).
$ grep -n -E "sorry|admit|native_decide|^\s*axiom" RBM3D/Green/FlucIterGain.lean | wc -l
       0
$ lake env lean ax_r.lean > ax_r.txt 2>&1; echo "exit $?"; grep -n "depends\|axiom audit\|FlucGainUpTo\|premises found" ax_r.txt
exit 0     # ax_r.lean: import RBM3D; import RBM3D.Green.FlucIterGain; 8 x #print axioms; #assert_rbm_axioms
1:'RBM.Green.sum_prod_abs_card_image_le' depends on axioms: [propext, Classical.choice, Quot.sound]
2:'RBM.Green.sum_weighted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
3:'RBM.Green.integral_norm_flucAvg_pow_le_iter_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
4:'RBM.Green.FlucIterGainInst.sum_prod_abs_card_image_row' depends on axioms: [propext, Classical.choice, Quot.sound]
5:'RBM.Green.FlucIterGainInst.sum_weighted_row' depends on axioms: [propext, Classical.choice, Quot.sound]
6:'RBM.Green.FlucIterGainInst.moment_row_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
7:'RBM.Green.FlucIterGainInst.moment_row_p2' depends on axioms: [propext, Classical.choice, Quot.sound]
8:'RBM.Green.FlucIterGainInst.moment_block_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
9:axiom audit: 3152 theorems, 1154 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
121:  RBM.Green.FlucGainUpTo': 2 [no certificate]
122:premises found by scanning: 84 (borrowed 2, owed 67, structural 15).
$ awk '/^theorem sum_prod_abs_card_image_row/,/norm_num \[szG\]$/{print NR": "$0}' RBM3D/Green/FlucIterGain.lean
1101: theorem sum_prod_abs_card_image_row :
1102:     ∑ v ∈ (Finset.univ : Finset (Fin 2 → Idx 3 (szG.L 0) (szG.W 0))).filter
1103:         (fun v => ((Finset.univ : Finset (Fin 2)).image v).card ≤ 1), ∏ i, |rowW (v i)|
1104:       ≤ 1 / 8 := by
1105:   refine le_trans (sum_prod_abs_card_image_le (ι := Fin 2) (s := 1) (n := 2) rowW_bounded
1106:     (by rw [rowA_card]; norm_num) (by norm_num) (by simp)) ?_
1107:   norm_num [szG]
$ grep -n "sum_prod_abs_card_image_le hw" RBM3D/Green/FlucIterGain.lean
444:      · exact sum_prod_abs_card_image_le hw (le_trans hsan hn) hsan hcard
```
1. `sum_prod_abs_card_image_le` has the pinned signature (b.3: only `UniformWeight | BoundedWeight` and `hs | _hs`). The previous labelling proof is the private `flucIterGain_sum_prod_abs_card_image_le_of_le_one` (keeps `hc1 : c ≤ 1`); the public lemma applies it at `min c 1`.
2. Calls updated: `sum_weighted_le` (`:444`, `hs := le_trans hsan hn`; its binder is `hn` as in RBM2D, b.3 shows no `hn` difference) and the instance `sum_prod_abs_card_image_row` (`:1106`, `1 ≤ #A = 56` by `rowA_card`, nondegenerate: true row, `c = 1/8`, `ι = Fin 2`).
3. Report: b.2, b.3, b.7 item 3, `T2096a` in (d) rewritten as a proof-only difference; module docstring (`:47-:58`) updated. New private name `flucIterGain_sum_prod_abs_card_image_le_of_le_one` carries the file-stem prefix (CLAUDE.md §3 (E)).

Verified Mathlib names added: `Finset.single_le_sum`, `le_min`, `min_le_left`, `min_le_right` (used in the compiled file).
