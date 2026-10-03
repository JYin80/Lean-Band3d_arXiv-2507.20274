Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  2 23:52:47 UTC 2026 (start); written after the script runs below

Notation: `lam` is the paper's `\ilambda` (= `g`, `def:ilambda`), the `g` of the merged `SB`/`SBR`/`sbKernelR`; `S_ij = W^{-d} S^{(B)}_{[i][j]}(lam)`, `[i] = (split i).1`. Targets (items 1-3) contain no further numerical constant: `Sizes`, `size`, `svarF`, `PF`, `seqP`, `seqXmat`, `seqHflow`, the RBM2D lemmas and `LinearForm` are exponent-free; the exponents enter only through `Admissible`, `lam_sq_mul_pow_ge`, `W_rpow_le`, `size_rpow_le_W_rpow` and the instance.

### (i) Exponent table (d = 3; 𝔠 = 1/6, 𝔡 = 1/10, κ = ε = 1/10; probe instance `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, write `m = n+1`)

| Quantity | Value | Constraint (target) | Slack (n = 0, i.e. m = 1; general m) |
|---|---|---|---|
| `N = size n` | `(W L)^d` (`Sizes.size`, 1_2:263) | `SizeTendsto` (N → ∞) | `N_0 = 2097152`; `N_n ≥ n+1` (checked n < 2000) |
| block size / `Σ_j` | `W^d` points per block (`card_Iblk`), `card_Idx = (WL)^d` | `d`-power, not `W^2`; `L ≥ 3` (field `three_le_L`) | `W^3 = 32768`; `L_n = 4m ≥ 4 ≥ 3` |
| `Bandwidth 𝔠` | `N^𝔠 ≤ W`, 𝔠 = 1/6 (Main_DEL_COND, 1_2:359) | `W^6 ≥ N` (𝔠 = 1/6) | `W^6/N = 512` at n=0; exact `W^6 = (2m)^30 ≥ (2m)^15 (4m)^3 = N` all m; `log W/log N` = 0.2381 (n=0) → 0.2736 (n=999) ∈ [1/6, 1/3] |
| `WO 𝔡` (eq:WO, 1_2:363) | `W^{-d/2+𝔡} = W^{-7/5} ≤ lam ≤ 𝔡^{-1} = 10` | window nonempty and met | `lam/W^{-7/5} = (2m)^{-6}(2m)^7 = 2m` (2 at n=0, → ∞); `lam_n ≤ 1/64 ≤ 10`; `lam_n → 0` allowed (λ is a sequence) |
| `lam_sq_mul_pow_ge` | `W^{2𝔡} ≤ lam² W^d` (pointwise from the lower WO bound) | `lam² W^{-d+2𝔡}`: exponents add to `2𝔡` exactly | `lam² W^3 = (2m)^3`, `W^{1/5} = 2m`; n=0: 8 ≥ 2; `(lam²W^d)^{-1} = 1/8 ≤ W^{-1/5} = 1/2` |
| `W_rpow_le` | `W^τ ≤ N^{τ/d}`, τ ≥ 0, `0 < d` | `W^d ≤ N` (since `L ≥ 1`) | n=0: τ=1: 32 ≤ 128; τ=3: 32768 ≤ 2097152; `W^3/N = L^{-3} = 1/64` |
| `size_rpow_le_W_rpow` | `N^τ ≤ W^{τ/𝔠}`, `0 < 𝔠`, `N^𝔠 ≤ W`, τ ≥ 0 | uses `Bandwidth` at n | n=0: τ=1: 2.097e6 ≤ 1.074e9 (= W^6); τ=3: 9.2e18 ≤ 1.2e27 |
| `Σ_j S_ij = 1` | `W^d · W^{-d} Σ_b S^{(B)}_{ab}(g)`; `S^{(B)}(g)` row: `(1+2dg²)^{-1}(1 + #{zdistD = 1}·g²)`, `#{zdistD=1} = 2d` iff `L ≥ 3` | needs `L ≥ 3` (neighbours `±e_i` distinct) | script C: L = 3,4,5: row sum exactly 1, 6 neighbours |
| `E|X_ij|² = S_ij` | off-diagonal: two real coords with `gvarF = S_ij/2`; diagonal: one real coord with `gvarF = S_ii` (`gvarF`) | `S_ij ≥ 0` (`svarF_nonneg`), `svarF_comm` | script D: `S/2 + S/2 = S`; `S_xx = W^{-d}(1+2dg²)^{-1}` (`svarF_diag`) |
| `D_{κ,ε}` (`locDomain`) | `|Re z| ≤ 2-κ`, `N^{-1+ε} ≤ Im z ≤ 1` | nonempty | n=0: `N^{-9/10} = 2.04e-6`; `z = 1/2 + i N^{-4/5}` lies in it (T2002 (a), unchanged) |
| Energies | sequences `E : ℕ → ℝ` (not used by items 1-3; `locDomain` takes one `z` at index n) | not fixed by any row | `lam` and `L, W` vary along the sequence; nothing is a constant in n |
| `zdistInf ≤ zdistD ≤ d·zdistInf` | `d = 3` | integers | `zdistD ∈ [zdistInf, 3 zdistInf]` (pure order statement, no exponent) |

### (ii) One concrete nondegenerate instance

`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`; `sz0 : Sizes 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; n = 0: `L = 4, W = 32, lam = 1/64, N = 2097152`, `W^3 = 32768` (matches probe `sz0_values`, `5d2a4a8` lines 1049-1056). Every hypothesis of `Admissible 𝔠 𝔡` (`0<𝔠`, `0<𝔡`, `SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡`), `Sizes.three_le_L`, `W_pos`, `lam_sq_mul_pow_ge`, `W_rpow_le`, `size_rpow_le_W_rpow` holds for all n. Fine-lattice model checks at a small `W=2, L=3` fixed size (`N = 216`) because the model statements are fixed-size.

Command (pure Python 3, scratchpad only; `t2006_pre.py` in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/`): `python3 t2006_pre.py`

```
A: n L W lam N | W^6>=N | lam^5>=W^-7 & lam<=10 | (lam^2 W^d)^5>=W | N^(1/3)>=W [W^3<=N] | logW/logN
0 4 32 1/64 2097152 | True True True True 0.2381
1 8 1024 1/4096 549755813888 | True True True True 0.2564
2 12 7776 1/46656 812479653347328 | True True True True 0.261
5 24 248832 (2m)^-6 (WL)^3 | True True True True 0.2654
10 44 5153632 (2m)^-6 (WL)^3 | True True True True 0.2678
100 404 336323216032 (2m)^-6 (WL)^3 | True True True True 0.2719
1000 4004 32160320320160032 (2m)^-6 (WL)^3 | True True True True 0.2736
A': exact checks n=0..1999 ok; N_n>=n+1: True
lam_n -> 0: lam_999 = 1.5625e-20
B: tau 0.5  W^tau=5.657 <= N^(tau/d)=11.31 ; N^tau=1448 <= W^(tau/c)=3.277e+04 (c=1/6)
B: tau 1  W^tau=32 <= N^(tau/d)=128 ; N^tau=2.097e+06 <= W^(tau/c)=1.074e+09 (c=1/6)
B: tau 3  W^tau=3.277e+04 <= N^(tau/d)=2.097e+06 ; N^tau=9.223e+18 <= W^(tau/c)=1.238e+27 (c=1/6)
C: L=3 g=1/2  sum_b S^B_ab = 1  #neighbours(zdistD=1) = 6 (=2d) symmetric=True
C: L=4 g=1/64  sum_b S^B_ab = 1  #neighbours(zdistD=1) = 6 (=2d) symmetric=True
C: L=5 g=7/3  sum_b S^B_ab = 1  #neighbours(zdistD=1) = 6 (=2d) symmetric=True
D: N= 216 =(WL)^d= 216 row sum_j S_{0j} = 1
D: row sums =1 for 60 rows: True  S_xx = W^-d (1+2dg^2)^-1: True
D: E|X_ij|^2 = S/2+S/2 = True
```
Script A' covers the exact integer inequalities `W^6 ≥ N`, `lam^5 W^7 ≥ 1`, `(lam²W^3)^5 ≥ W`, `3 ≤ L`, `0 < W` for n < 2000 (asserts); for all n they hold by the closed forms in the table. In script D the block label of a fine point is `i mod L` (each block then has `W^d` points); row sums do not depend on the particular bijection `split`. The `n=0` slack numbers in the table (`W^{-7/5} = 0.0078125`, `lam/W^{-7/5} = 2`, `lam²W³ = 8`, `W^6/N = 512`) come from a second one-line script run at the same time.

External hypotheses: none in the targets (`RBM3D/Gauss/FineModel.lean`, `Defs/Sizes.lean`, `Gauss/LinearForm.lean` take no external input; the T2002 preflight's note on `eq:zztE` is not used here). The sequence-level `WO` limit: `lam_n/W_n^{-7/5} = 2(n+1) → ∞` and `lam_n → 0`, so the window is non-collapsed and `lam` is genuinely not constant.

### Verdicts (stage 1a)

- Target 1 (`Defs/Sizes.lean`, `Gauss/FineModel.lean` pinned probe text): PASS. All constraints hold at once at the instance above for every n; slack positive.
- Target 2 (RBM2D `Model.lean` port to `d` dimensions): PASS. The only dimension-dependent numerical facts (`W^d` block size, `(WL)^d = N`, row sum `Σ_j S_ij = 1` with `2d` neighbours, `E|X_ij|² = S_ij`) verified in A, C, D.
- Target 3 (`Gauss/LinearForm.lean`, generic port): PASS (no numerical hypothesis; the instance sequence has `Sizes.SeqCoord` nonempty).

## (b) Script output (commands run Sat Oct  3 00:31:58 UTC 2026 .. Sat Oct  3 00:32:47 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2006`, branch `t/T2006`, commit `9381f0f`; `$SP` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2006`)

### b.1 Build, hygiene, scope
```
$ lake build RBM3D.Defs.Sizes RBM3D.Gauss.FineModel RBM3D.Gauss.LinearForm 2>&1 | tail -3
Build completed successfully (3245 jobs).
$ for f in RBM3D/Defs/Sizes.lean RBM3D/Gauss/FineModel.lean RBM3D/Gauss/LinearForm.lean; do lake env lean -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 $f; echo "$f exit=$?"; done   # fresh elaboration, lakefile leanOptions, no message lines
RBM3D/Defs/Sizes.lean exit=0
RBM3D/Gauss/FineModel.lean exit=0
RBM3D/Gauss/LinearForm.lean exit=0
$ git --no-optional-locks diff --stat main...t/T2006
 RBM3D/Defs/Sizes.lean       | 417 ++++++++++++++++++++++++
 RBM3D/Gauss/FineModel.lean  | 763 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Gauss/LinearForm.lean | 404 +++++++++++++++++++++++
 3 files changed, 1584 insertions(+)
$ grep -nE "sorry|admit|native_decide|^ *axiom " RBM3D/Defs/Sizes.lean RBM3D/Gauss/FineModel.lean RBM3D/Gauss/LinearForm.lean; echo "grep exit=$? (1 = no match)"
grep exit=1 (1 = no match)
$ lake env lean $SP/FullAudit.lean 2>&1 | head -2 | cut -c1-100   # FullAudit.lean = import RBM3D + the 3 modules + #assert_rbm_axioms
axiom audit: 612 theorems, 216 definitions, 0 axioms in `RBM` (compiler-generated declarations exclu
All within [propext,
```

### b.2 Item 1: the pinned text against the probe (`5d2a4a8:RBM3D/Probe/T2002Vocab.lean`)
```
$ diff <(git --no-optional-locks show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean | sed -n 39,249p) <(sed -n 36,246p RBM3D/Defs/Sizes.lean); echo "exit=$?"
exit=0
$ diff <(git --no-optional-locks show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean | sed -n 251,446p) <(sed -n 37,232p RBM3D/Gauss/FineModel.lean); echo "exit=$?"
exit=0
$ lake env lean $SP/ProbeTypes.lean > $SP/ProbeTypes.out; lake env lean $SP/MineTypes.lean > $SP/MineTypes.out; diff $SP/ProbeTypes.out $SP/MineTypes.out; echo "exit=$? lines=$(wc -l < $SP/MineTypes.out)"
exit=0 lines=      88
# ProbeTypes.lean = probe lines 1-446 + `end RBM.Gauss` + `#check @name` (pp.fullNames) for the pinned names found by `names.py` (57) and 6 `Sizes` constants;
# MineTypes.lean = `import RBM3D.Defs.Sizes, RBM3D.Gauss.FineModel` + the same checks.
```

### b.3 `#print axioms` of every public declaration of the three files
```
$ python3 $SP/names.py FILE 1 $(wc -l < FILE)  # for the 3 files > names_all.txt; kinds: abbrev 5, def 31, instance 4, structure 1, theorem 83
$ lake env lean $SP/AxAll.lean > $SP/AxAll.out   # one `#print axioms` per name; then `python3 $SP/axgroup.py $SP/AxAll.out`
exit=0
public declarations printed: 124
 115 with axioms [propext, Classical.choice, Quot.sound]
   4 with axioms [(none)]
   3 with axioms [propext]
   2 with axioms [propext, Quot.sound]
$ grep -E "sz0_admissible|svarF_eq_svar|integral_normSq_Xentry|seqP_map_slice|map_sum_const_mul_coord" $SP/AxAll.out
'RBM.Gauss.SizesInst.sz0_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.svarF_eq_svar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.seqP_map_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.integral_normSq_Xentry' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LinearForm.map_sum_const_mul_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.4 Items 2-3: the ports against RBM2D `c9a24cf` after the renaming R1-R4 (statements; proofs informational)
```
$ python3 $SP/portdiff.py <git show c9a24cf:RBM2D/Gauss/Model.lean> RBM3D/Gauss/FineModel.lean | grep -E "^statements identical|DIFFERS"
statements identical after R1-R4: 32/32; whole declarations identical: 23/32
# whole declaration differs after renaming only in: integral_normSq_Xentry Xmat_update Xmat_eq_sum_coordinates seqHflow_isHermitian measurable_seqHflow_entry integral_normSq_seqXmat integral_normSq_seqHflow seqXmat_eq_sum_coordinates seqXmat_update (extra explicit args `d`, `g`; `fineModel_*` helper names; a bound `d` renamed `e`)
$ python3 $SP/cite.py <Model.lean at c9a24cf> RBM3D/Gauss/FineModel.lean   # RBM2D line -> line here, in the order of the ticket
P_map_eval 136->270  P_map_restrict 142->277  measurable_Xentry 180->282
integrable_sq_coord 188->291  integral_sq_coord 198->302  integral_normSq_Xentry 210->314
Xmat_add 253->359  Xmat_smul 261->367  Xlinear 270->377
coordinateMatrix 277->384  coordinateMatrix_isHermitian 283->388  Xmat_update 287->393
Xmat_eq_sum_coordinates 300->407  continuous_Xmat 319->427  Hflow 327->437
Hflow_eq_realSmul 337->446  continuous_Hflow 344->454  Hflow_isHermitian 350->461
measurable_Hflow 357->469  Hflow_sub 363->475  Hflow_sub_apply 369->481
integral_normSq_Hflow 376->488  norm_Hflow_sub 387->500  seqP_map_eval 448->516
seqP_map_restrict 452->521  seqHflow_eq_smul 499->527  seqHflow_isHermitian 508->531
measurable_seqHflow_entry 511->536  integral_normSq_seqXmat 517->543  integral_normSq_seqHflow 530->557
seqXmat_eq_sum_coordinates 544->572  seqXmat_update 550->579
$ diff <(sed -n 28,231p LinearForm.lean@c9a24cf | sed R1) <(sed -n <namespace>,<end Glue> RBM3D/Gauss/LinearForm.lean)   # R1: Sizes.SeqCoord d -> Sizes.SeqCoord sz, ...
11c11,12
<   have := iIndepFun_infinitePi (P := fun c : Sizes.SeqCoord sz => gaussianReal 0 (Sizes.seqGvar sz c))
---
>   have := iIndepFun_infinitePi
>     (P := fun c : Sizes.SeqCoord sz => gaussianReal 0 (Sizes.seqGvar sz c))
36a38
> set_option linter.unusedDecidableInType false in
107a110
> set_option linter.unusedDecidableInType false in
152a156,157
> set_option linter.unusedSectionVars false in
> set_option linter.overlappingInstances false in
exit=1
```

### b.5 Target statements, extracted by script (`python3 $SP/extract.py WIDTH FILE NAME...`: theorems up to `:=`, defs whole)
```
$ grep -nE "^structure Sizes|^  (L|W|lam|three_le_L|W_pos) : " RBM3D/Defs/Sizes.lean
138:structure Sizes (d : ℕ) where
140:  L : ℕ → ℕ
142:  W : ℕ → ℕ
144:  lam : ℕ → ℝ
145:  three_le_L : ∀ n, 3 ≤ L n
146:  W_pos : ∀ n, 0 < W n
$ python3 $SP/extract.py 150 RBM3D/Defs/Sizes.lean WO Bandwidth Admissible locDomain lam_sq_mul_pow_ge size_rpow_le_W_rpow
Sizes.lean:164: def WO (𝔡 : ℝ) : Prop := ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹
Sizes.lean:168: def Bandwidth (𝔠 : ℝ) : Prop := ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)
Sizes.lean:177: def Admissible (𝔠 𝔡 : ℝ) : Prop := 0 < 𝔠 ∧ 0 < 𝔡 ∧ sz.SizeTendsto ∧ sz.Bandwidth 𝔠 ∧ sz.WO 𝔡
Sizes.lean:186: def locDomain (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop := |z.re| ≤ 2 - κ ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
Sizes.lean:193: theorem lam_sq_mul_pow_ge (n : ℕ) {𝔡 : ℝ} (h : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * ((s…
Sizes.lean:237: theorem size_rpow_le_W_rpow {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ) (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) {τ : ℝ} (hτ : 0 ≤ τ) : ((sz.size n : ℕ) : ℝ) …
$ python3 $SP/extract.py 150 RBM3D/Gauss/FineModel.lean svarF_eq_svar PF seqHflow seqP_map_slice integral_normSq_Xentry integral_normSq_seqXmat integral_normSq_seqHflow
FineModel.lean:68: theorem svarF_eq_svar (i j : Idx d L W) : svarF d L W g i j = svar d L W g (split d L W i) (split d L W j)
FineModel.lean:97: def PF : Measure (Ω d L W) := Measure.infinitePi fun c => gaussianReal 0 (gvarF d L W g c)
FineModel.lean:225: def seqHflow (n : ℕ) (u : ℝ) (ω : SeqΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := (Real.sqrt u : ℂ) • seqXmat sz n ω
FineModel.lean:184: theorem seqP_map_slice (n : ℕ) : (seqP sz).map (slice sz n) = PF d (sz.L n) (sz.W n) (sz.lam n)
FineModel.lean:314: theorem integral_normSq_Xentry (i j : Idx d L W) : ∫ ω, ‖Xentry d L W ω i j‖ ^ 2 ∂(PF d L W g) = svarF d L W g i j
FineModel.lean:543: theorem integral_normSq_seqXmat (n : ℕ) (i j : Idx d (sz.L n) (sz.W n)) : ∫ ω, ‖seqXmat sz n ω i j‖ ^ 2 ∂(seqP sz) = svarF d (sz.L n) (sz.W n) (sz.lam…
FineModel.lean:557: theorem integral_normSq_seqHflow (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (i j : Idx d (sz.L n) (sz.W n)) : ∫ ω, ‖seqHflow sz n u ω i j‖ ^ 2 ∂(seqP sz) = u * svar…
$ python3 $SP/extract.py 150 RBM3D/Gauss/LinearForm.lean map_sum_const_mul_coord
LinearForm.lean:118: theorem map_sum_const_mul_coord (a : Sizes.SeqCoord sz → ℝ) (s : Finset (Sizes.SeqCoord sz)) : (Sizes.seqP sz).map (fun ω : Sizes.SeqΩ sz => ∑ c ∈ s, …
```

### b.6 The compiled nonempty instances (`python3 $SP/show.py FILE REGEX...`; all compile in the builds of b.1)
```
$ python3 $SP/show.py RBM3D/Defs/Sizes.lean '^def sz0 ' '^theorem sz0_admissible'
-- Sizes.lean:260
def sz0 : Sizes 3 where
  L := fun n => 4 * (n + 1)
  W := fun n => (2 * (n + 1)) ^ 5
  lam := fun n => ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  three_le_L := fun n => by omega
  W_pos := fun n => by positivity
-- Sizes.lean:331
theorem sz0_admissible : sz0.Admissible (1 / 6) (1 / 10) :=
  ⟨by norm_num, by norm_num, sz0_tendsto, sz0_bandwidth, sz0_WO⟩
$ python3 $SP/extract.py 150 RBM3D/Defs/Sizes.lean sz0_locDomain
Sizes.lean:406: theorem sz0_locDomain : sz0.locDomain (1 / 10) (1 / 10) 0 (⟨1 / 2, ((sz0.size 0 : ℕ) : ℝ) ^ (-(4 / 5) : ℝ)⟩ : ℂ)
$ python3 $SP/show.py RBM3D/Gauss/FineModel.lean '^example \(i j : Idx 3 \(sz0.L 0\)' '^example : ∫ ω, ‖Xentry 3 4 32 ω 0 0‖' '^example : \(Sizes.seqP sz0\).map'
-- FineModel.lean:613
example (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j =
        svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (split 3 (sz0.L 0) (sz0.W 0) i)
          (split 3 (sz0.L 0) (sz0.W 0) j) ∧
      ∫ ω, ‖Xentry 3 (sz0.L 0) (sz0.W 0) ω i j‖ ^ 2 ∂(PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0)) =
        svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j :=
  ⟨svarF_eq_svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j,
    integral_normSq_Xentry 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j⟩
-- FineModel.lean:623
example : ∫ ω, ‖Xentry 3 4 32 ω 0 0‖ ^ 2 ∂(PF 3 4 32 (1 / 64)) =
    ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹ := by
  rw [integral_normSq_Xentry, svarF_diag]; norm_num
-- FineModel.lean:662
example : (Sizes.seqP sz0).map (Sizes.slice sz0 0) = PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) :=
  Sizes.seqP_map_slice sz0 0
$ grep -n -A1 '^example : ∫ ω, ‖Xentry 3 4 32 ω 0 ![32' RBM3D/Gauss/FineModel.lean | cut -c1-120   # the off-diagonal example: statement; its proof is in the file
629:example : ∫ ω, ‖Xentry 3 4 32 ω 0 ![32, 0, 0]‖ ^ 2 ∂(PF 3 4 32 (1 / 64)) =
630-    ((32 : ℝ) ^ 3)⁻¹ * ((1 / 64 : ℝ) ^ 2 * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹) := by
$ grep -c "^example" RBM3D/Defs/Sizes.lean RBM3D/Gauss/FineModel.lean RBM3D/Gauss/LinearForm.lean; grep -c "^theorem sz0_" RBM3D/Defs/Sizes.lean
RBM3D/Defs/Sizes.lean:3
RBM3D/Gauss/FineModel.lean:16
RBM3D/Gauss/LinearForm.lean:6
11
```

### b.7 Name clash, paper labels, sources
```
$ python3 $SP/clash.py $SP/names_all.txt main   # `git grep` of declaration lines `(def|theorem|...) [ns.]NAME` in `main`, every new short name
124 new public declarations, 123 distinct short names; declaration lines of the same short name in main: 0
$ grep -no 'label{...}' paper/tex/1_2_Intro_model_result.tex   # the labels of the model statements (main worktree)
256:label{def:ilambda} 266:label{eq:blockIa} 295:label{bandcw0} 303:label{eq:variancematrix} 359:label{Main_DEL_COND} 363:label{eq:WO} 380:label{eq:spectral_domain} 
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Gauss/Model.lean RBM2D/Gauss/LinearForm.lean   # RBM2D HEAD below
RBM2D HEAD: bcc2c11, c9a24cf: c9a24cf
 RBM2D/Gauss/LinearForm.lean |  87 ++------------------------------
 RBM2D/Gauss/Model.lean      | 118 --------------------------------------------
 2 files changed, 3 insertions(+), 202 deletions(-)
$ python3 $SP/removed.py   # declared names of the two RBM2D files at c9a24cf minus the same at HEAD
Model.lean declarations c9a24cf/HEAD: 76 / 66 ; removed at HEAD: Hflow_sub_apply, P_map_restrict, constantSizes, integral_normSq_Hflow, integral_normSq_Xentry, integral_normSq_seqHflow, integral_normSq_seqXmat, nontrivial_diagonal_example, norm_Hflow_sub, seqP_map_restrict
LinearForm.lean declarations c9a24cf/HEAD: 19 / 13 ; removed at HEAD: checkSizes, check_map_sum_const_mul_coord, eq_glue_of_congr, hasLaw_const_mul_coord, hasLaw_coord, iIndepFun_const_mul_coord
$ $SP/usage.sh   # RBM2D (c9a24cf) uses of the unlisted lemmas outside Model.lean: lines/files
lines/files outside Model.lean: gvar_diag:15/13 gvar_offDiag:16/12 Xmat_apply:15/11 coordinateMatrix_apply:24/6 Hflow_apply:5/5 seqHflow_zero:33/12 size_eq:154/65
```

### Narrative (at most 40 lines)
1. Delivered: commit `9381f0f` on `t/T2006` adds `RBM3D/Defs/Sizes.lean`, `RBM3D/Gauss/FineModel.lean`, `RBM3D/Gauss/LinearForm.lean` and nothing else (b.1; 1584 lines). `Sizes.lean` is probe lines 39-249 verbatim plus checks; `FineModel.lean` is probe lines 251-446 verbatim, the 32 lemmas of ticket item 2 ported to `d` dimensions, and checks; `LinearForm.lean` is RBM2D's file with R1 (adaptations in item 4 (iii)) plus checks at `sz0`. No pinned statement, no ported statement and no hypothesis was changed; `RBM3D.lean` is untouched (the hub adds the three imports).
2. Evidence: fresh elaboration of the three files with the lakefile's `leanOptions` prints no message (b.1); `lake build` of the three modules succeeds; all 124 public declarations (83 theorems) print only `propext`, `Classical.choice`, `Quot.sound` (b.3); the pinned text is identical to the probe (diff exit 0) and the elaborated types of its 57 declarations and of the `Sizes` constants equal the probe's (b.2); the 32 ported statements equal RBM2D's after R1-R4 (b.4); the library audit with the three modules imported passes (b.1); no name clash with `main` (b.7).
3. Instances (b.6), all at `d = 3` and nondegenerate: `SizesInst.sz0_admissible` is `Admissible (1/6) (1/10)` for `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}` (a sequence with `lam_n -> 0`, `lam/W^{-7/5} = 2(n+1)` as in section (a)) with every conjunct proved; `sz0_locDomain` puts a point in `D_{kappa,eps}`. At `L = 4, W = 32, g = 1/64`: `svarF_eq_svar`; `E|X_xx|^2` and `E|X_xy|^2` for two neighbouring blocks with their numeric values `W^{-3}(1+6g^2)^{-1}` and `W^{-3} g^2 (1+6g^2)^{-1}`; the row sums `sum_y S_xy = 1` for all `d, L, W` with `3 <= L`; `seqP_map_slice` and `integral_normSq_seqHflow` at `sz0`; one application of every other ported lemma of `Model.lean`, and at `sz0` of `iIndepFun_coord`, `hasLaw_coord`, `hasLaw_const_mul_coord`, `iIndepFun_const_mul_coord`, `map_sum_const_mul_coord`, `map_lin`, `measurable_lin`, `(l)integral_indep_pair(_le)` and the `glue` lemmas (the `example`s at the end of `FineModel.lean`, `LinearForm.lean`).
4. Decisions inside the ticket: (i) the four RBM2D `@[simp]` lemmas `gvar_diag`, `gvar_offDiag`, `Xmat_apply`, `Hflow_apply`, which the listed proofs use and the ticket does not list, are private `fineModel_*` copies (CLAUDE.md §3 (E)); the other unlisted RBM2D lemmas are not ported (d, O1). (ii) The concrete sequence and its checks are public in the stem-prefixed namespace `RBM.Gauss.SizesInst`, because the checks of `FineModel.lean` and later tickets reuse `sz0`; effect on the premise scan: (d), O2. (iii) `LinearForm.lean`: RBM2D's `#print axioms` lines are dropped (b.3 prints them); four inherited lint warnings on three lemmas (unusedDecidableInType twice, unusedSectionVars, overlappingInstances) are silenced by `set_option ... in` so that the statements stay RBM2D's (b.4 diff); `checkSizes` is a `Sizes 3` with `lam = 1/2`, `noncomputable`. (iv) `Sizes.lean` imports `RBM3D.Gauss.Model` only for `Vtx` (the target of `split`) and `RBM3D.Defs.Params` for `Bparam`.
5. Paper re-check (CLAUDE.md §5.2; label lines in b.7): `(eq:variancematrix)` is `svarF` (`S_xy = W^{-d} S^{(B)}_{ab}(g)`, the merged `sbKernelR`); `(bandcw0)` is `Xentry`/`PF` with `E|X_xx|^2 = S_xx`, `E|X_xy|^2 = S_xy` (`integral_normSq_Xentry`); `(Main_DEL_COND)`, `(eq:WO)`, `(eq:spectral_domain)` are `Bandwidth`, `WO`, `locDomain`. The ported lemmas contain no lattice exponent: their only powers are squares of a coordinate or of a norm; the dimension enters through `svarF` (`W^{-d}`), `Idx d L W` and `size = (W L)^d` of the verbatim text.
6. Finding: RBM2D HEAD deleted 10 of the 76 declarations of `Model.lean` and 6 of the 19 of `LinearForm.lean` (b.7), among them lemmas that the ticket lists (`integral_normSq_Xentry`, `integral_normSq_seqXmat`, `hasLaw_coord`, ...); they are ported as ticketed.
7. Limits: probe and RBM2D proofs are reused (argument insertion and the `fineModel_*` helper names only, b.4); the examples apply theorems at the data above and prove no new mathematics.

## (c) Verified Mathlib names used (`#check`, `$SP/Names.lean`; one line per name, first 100 characters)
```
@Measure.infinitePi_map_eval : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (
@Measure.infinitePi_map_restrict : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpa
@Measure.eq_infinitePi : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} 
@Measure.infinitePi_pi : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} 
@memLp_id_gaussianReal : ∀ {μ : ℝ} {v : NNReal} (p : NNReal), MemLp id (↑p) (gaussianReal μ v)
@variance_fun_id_gaussianReal : ∀ {μ : ℝ} {v : NNReal}, Var[fun x => x; gaussianReal μ v] = ↑v
@variance_eq_integral : ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}, AEMea
@integral_map : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace 
@integrable_map_measure : ∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : Measure α} [i
@iIndepFun_infinitePi : ∀ {ι : Type u_1} {𝓧 : ι → Type u_2} {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {
@HasLaw : {Ω : Type u_1} → {𝓧 : Type u_2} → {mΩ : MeasurableSpace Ω} → {m𝓧 : MeasurableSpace 𝓧} → (Ω
@gaussianReal_map_const_mul : ∀ {μ : ℝ} {v : NNReal} (c : ℝ), Measure.map (fun x => c * x) (gaussian
@gaussianReal_conv_gaussianReal : ∀ {m₁ m₂ : ℝ} {v₁ v₂ : NNReal}, gaussianReal m₁ v₁ ∗ gaussianReal 
@iIndepFun.indepFun_finsetSum_of_notMem : ∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} 
@IndepFun.map_add_eq_map_conv_map : ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {M : T
@indepFun_iff_map_prod_eq_prod_map_map : ∀ {Ω : Type u_1} {β : Type u_2} {β' : Type u_3} {_mΩ : Meas
@integral_prod_symm : ∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] [ins
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@Fintype.sum_equiv : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fin
@Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} [inst : Fintype α₁] [inst_
@Equiv.subLeft : {G : Type u_1} → [AddGroup G] → G → G ≃ G
@Finset.univ_sum_single : ∀ {I : Type u_1} [inst : DecidableEq I] {M : I → Type u_2} [inst_1 : (i : 
@continuous_finsetSum : ∀ {ι : Type u_1} {M : Type u_2} {X : Type u_3} [inst : TopologicalSpace X] [
@Complex.real_smul : ∀ {x : ℝ} {z : ℂ}, x • z = ↑x * z
Complex.normSq_eq_norm_sq : ∀ (z : ℂ), Complex.normSq z = ‖z‖ ^ 2
@finFunctionFinEquiv : {m n : ℕ} → (Fin n → Fin m) ≃ Fin (m ^ n)
@Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x 
```

## (d) Open issues and paper-delta candidates
* **O1 (unlisted RBM2D lemmas; dispatcher decision)**: Four RBM2D `@[simp]` lemmas are private copies here (`fineModel_*`); these RBM2D lemmas are absent: `coordinateMatrix_apply`, `Hflow_zero`, `seqHflow_zero`, `Sizes.size_eq`, `svar_diag_pos`, `constantSizes`, `svar_cast_eq_Spaper` (d = 2 specific), `nontrivial_diagonal_example`. RBM2D uses several downstream (`lines/files outside Model.lean: gvar_diag:15/13 gvar_offDiag:16/12 Xmat_apply:15/11 coordinateMatrix_apply:24/6 Hflow_apply:5/5 seqHflow_zero:33/12 size_eq:154/65`). When MD-2/MD-3/ST tickets port RBM2D files that use them, one ticket should pin them publicly once (one-line proofs), so that two parallel tickets do not add the same public name.
* **O2 (premise scan of `RBM3D/Test/Axioms.lean`)**: the public theorems `SizesInst.sz0_admissible`, `sz0_WO`, `sz0_bandwidth`, `sz0_tendsto`, `sz0_locDomain` conclude `Admissible`, `WO`, `Bandwidth`, `SizeTendsto`, `locDomain`, so `scanPremises` counts these predicates as proved. Demonstration (a fixture theorem with an `Admissible` hypothesis in `$SP/Scan.lean`, not in the repository; the second line treats `SizesInst.*` as non-proofs, as if they were private):
  
```
unclassified premises, instances counted as proofs : []
unclassified premises, SizesInst.* not counted     : [RBM.Gauss.Sizes.Admissible]
```
  With the instances public, a later theorem with an `Admissible` hypothesis passes `#assert_rbm_axioms` unregistered; without them it would be reported as an unclassified premise and block the hub's merge until `Sizes.Admissible` is listed in `structuralProps`. Dispatcher: decide whether `Admissible` (the standing hypotheses of `MR:decol`, `MR:locSC`) should be registered as structural.
* **Paper-delta candidate T2006a** (representation, no statement change): the sample space `Ω d L W` (and `Sizes.SeqΩ`) carries independent real coordinates that `Xentry` never reads (the pairs `(a, b, ·)` with `idxKey b < idxKey a`, and the imaginary part on the diagonal; `FineModel.lean:105-111`); the paper's `(bandcw0)` has none. The law of `X` is exactly `(bandcw0)` (`integral_normSq_Xentry`, `Xmat_isHermitian`, `Xentry_swap`).
* Signed entries cited, not re-proposed: T2002a-i and DECISIONS §12 (the pinned text carries them). The ports add no further Lean/paper statement difference.
