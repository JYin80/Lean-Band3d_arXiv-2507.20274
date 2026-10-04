Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 06:39:43 UTC 2026

### (i) Exponent table and inventory
Paper `3_5:1435–1601`; all paths under `RBM3D/`. `Q^(A)` = merged `zeroModeSet d L A` (`Kernel/Evolution.lean:199`, a `foldr` of `zeroModeOp` over `A.toList`).

| item | value / merged declaration | constraint | slack |
|---|---|---|---|
| def `zero_mode_remove` (`P^(i)`, `Q^(i)`, `Q^(A)`) | `avgOp:190`, `zeroModeOp:194`, `zeroModeSet:199`, `projMat:205` (merged); commutation of the `Q^(i)`: private `npq_zmo_comm` (`Induction/NewPQ.lean`) | the list-fold proofs below need no ordering | none needed |
| `(normQA2)` | **target 1** (not merged; no linearity or sup-norm lemma for `zeroModeSet` exists: grep) | `‖Q^(A)𝒜‖∞ ≤ 2^{|A|}‖𝒜‖∞`, sup norm on `(Fin n → Zd d L) → ℂ`; constant `2^{|A|}`, free of `L,W,λ` | `n=3,|A|=2`: bound 4; 100 random tensors max ratio 1.043; adversarial tensor 3.876 (so the constant 2 per index is sharp up to 3%) |
| commutation remark `3_5:1540–1545` | **target 2**. Merged ingredients: `projMat_mul_SB_comm:359` (`3 ≤ L`), `projMat_mul_Theta:373` (`‖ξ‖<1`; gives `projMat·Θ = Θ0` only), `zeroModeOp_tensorKer:236`, `zeroModeSet_tensorKer:298` | hyp: `3 ≤ L`, `‖(t:ℂ)·cycProd m i‖ < 1` all `i`; `s` arbitrary real | slot: `‖tμ‖ = t` (`‖μ‖=1`), so slack `1−t`; `t=0.99`: 0.01 |
| `Θ·projMat = projMat·Θ` | **not merged**; new: from `Theta` symmetric (`Theta_transpose_of_three_le`) and row sums `(1−ξ)⁻¹`, or transpose of `projMat_mul_Theta` | same hyp as above | none |
| `ThetaN` single index `i≠j` / `i=j` | `Q^(j)` acts on a different index (`Function.update_comm`) / needs `projMat·K = K·projMat` for `K = thetaKer` (`μ SB·Θ(tμ)`) | `projMat` commutes with `SB` and with `Θ` | none |
| `UN`/`Ugen` | `UN = tensorKer (uKer …)` (`UN_eq_tensorKer:210`); `Ugen = UN (fun i => mSigma E (σ i))` (`Induction/GridDuhamelN.lean:65`); `Q^(A)` on the right of `tensorKer`: **not merged**, one direct sum swap | for `Ugen v w`: `|E| ≤ 2`, `0 ≤ w < 1` (`norm_mul_mSigma_lt_one`, `Defs/Semicircle.lean:91`); `v` arbitrary | `E=0`: slack 2 |
| `(eq_L-Keee_nonzeromode)` | continuous-time SDE; **no merged statement**; its grid form is target 3 | – | – |
| `(iisuwjyys)` grid form | **target 3**. Ingredients: `stoppedDuhamelN_at` (`GridDuhamelN.lean:310`, hyps only at index `n`: `|E n|<2`, `0 ≤ s n ≤ t n < 1`, `K n ≠ 0`, `min j (τ ω) ≤ K n`), `GridDuhamelN_Ugen_duhamel_telescope:161`, `GridDuhamelN_Ugen_add:82` | needs additivity of `Q^(A)` over `range` sums | grid times `0.90 … 0.99` all in `[0,1)` |
| combination `3_5:1590`, `A=∅` | **target 4**. `stNewPQ_holds:584` (pin `STNewPQ`, `Step34Pins.lean:330`): ONE data `(ℓ,k,ξ,σ',ι,A')` serves both the `𝓛` and the `𝒦` identity, with `A_n = A ∪ STIdiff σ`, `STIdiff σ ⊆ A' α`, `1 ≤ k α`, `k α + 1 ≤ m`; window `|E|<2`, `0 ≤ τ < 1` | subtract the two identities; `zeroModeSet` additive/sub (target 1) | none: no different `𝒦` form needed |
| `(𝓛−𝒦)` | `STLKM sz n E u (seqHflow sz n u ω) σ a = Lloop … − STKloop …` by definition (`Induction/Step2Defs.lean:68`, `STLM_seqHflow` rfl); `STKloop` deterministic (`Induction/Defs.lean:64`) | – | – |
| §29 (1) time domain | targets 1–3: `0 ≤ w < 1` (`t<1`), `s` free; target 3: `0 ≤ u_j < 1`, `j ≤ m`; target 4: `0 ≤ τ < 1` | – | `1−t = 0.01` |
| §29 (2) case `1−s ≤ g²/L²` | **not used** by targets 1–4 (stated in the ticket); threshold at `g=1/2, L=4`: `1/64 = 0.015625` | – | n/a |
| §29 (3) `L`–`W` relation | not used; only `3 ≤ L` (`sz.three_le_L n`) | – | – |
| §29 (4) `∀ n` vs `∀ᶠ n` | use the `_at` form `stoppedDuhamelN_at` (not `stoppedDuhamelN`, whose hypotheses are `∀ n`); `stNewPQ_holds` is pointwise in `(sz,n)` | – | – |

Findings for stage 1b (no verdict change):
- **F1.** `norm_zeroModeSet_UN_le:629` has hypothesis `hmi : ∀ i, 0 < (m i).im`, false for `m i = mSigma E false = conj (mE E)` (`Im<0`; `Defs/Semicircle.lean:85`). So "every term is in the range of `norm_zeroModeSet_UN_le`" holds only for the `SameSignOutside` part. The consumer form for mixed `σ` is `ekSumDecayNonzero_holds` (`Evolution/Nonzero.lean:146`) / `STEKNonzero` (`Step34Pins.lean:666`), stated with `UN … (EKsgn m σ)` (`Evolution/Pins.lean:45`, `EKsgn m σ i = PropSpin m (σ i)`); `Ugen … E σ = UN … (EKsgn (mE E) σ)` is definitional unfolding (`mSigma E b = PropSpin (mE E) b`). `SameSignOutside (fun i => mSigma E (σ i)) A` follows from `STIdiff σ ⊆ A` by `congrArg`. Stage 1b may add this bridge; it must not pass `norm_zeroModeSet_UN_le` an `hmi` it cannot prove.
- **F2.** The ticket writes `Σ_j Q^(A) 𝒰_{u_j,u_k}(predInc_j)`; the merged telescope and `stoppedDuhamelN_at` carry `𝒰_{u_{j+1},u_m}` (script below uses `u_{j+1}`, error 1e-13).
- **F3.** Target 3 as stated (apply `Q^(A)` pointwise to `stoppedDuhamelN_at`, use additivity) needs no integrability. The form "`Q^(A) martInc_j` is again a martingale increment" needs `Q^(A)` to commute with `condExp`, i.e. integrability of every coordinate; that belongs to S3-21 (the Azuma pin there takes `Ugen … (martIncN …) a` coordinatewise; `(Q^(A)𝒰 ξ)_a` is a sum of `≤ 2^{|A|}` coordinates of `𝒰 ξ`, not one).
- **F4.** The ticket's check point `(s,t)=(0.9,0.99)` is not in case (ii) at `g=1/2, L=4` (`1−s = 0.1 > 1/64`); targets 1–3 do not use the case condition. A case-(ii) point `(0.99, 0.995)` is checked as well.

### (ii) Concrete nondegenerate instance
`d=3, L=4, g=1/2, E=0 (m(+)=i, m(−)=−i), n=3, σ=(+,−,+), μ=cycProd=(1,1,−1), I_diff(σ)=A={0,1}` (nonempty, proper), `(s,t)=(0.9,0.99)` and `(0.99,0.995)`, `|E|=0<2`, `3 ≤ L`, `‖tμ_i‖ = t < 1`. Lean instances also at `sz0` (`Defs/Sizes.lean:260`: `sz0.L 0 = 4`, `sz0.lam 0 = 1/64`, `sz0_values`), `E ≡ 0`, grid `s ≡ 1/10, t ≡ 1/2, K ≡ 4` (as the merged examples), `τ ≡ 3`, `σ=(+,−,+)`. No external hypothesis occurs in targets 1–4 (`STNewPQ` is proved by `stNewPQ_holds`; no Prop5/Prop8 pin), so no limit computation is owed. Exact `SB` (`Defs/Block.lean:44`: `1/(1+6g²)` at 0, `g²/(1+6g²)` at `zdistD=1`), `Θ=(1−ξ SB)⁻¹`, `thetaKer`, `uKer`, `ThetaN`, `UN`, `Q^(i)=I−P^(i)` implemented as in `Kernel/Evolution.lean:52–65,190–196`; tensors `64³` complex.

Command (scratch script, not Lean): `python3 scratchpad/T2112/pre.py`, then `pre2.py`, then `pre.py` with `g=1/64`:
```
rowsum SB True colsum True nonzero/row 7
m = [(1j), (-1j), (1j)] mu = [(1+0j), (1+0j), (-1+0j)] Idiff = [0, 1]
Q^(i) == projMat on axis i: 4.446439748506845e-15
UN  commutation, (s,t)=(0.9,0.99), A=Idiff: 2.9421538573982354e-14
UN  commutation, A={0,1,2}: 2.808666774861361e-14
ThetaN commutation, t=0.99, A=Idiff: 8.260805387140494e-14
sup|UN T| scale: 14.690679273795118
NEG CONTROL UN commutation with non-translation-invariant S: 0.23775971877892876
normQA2: max ratio over 100 random tensors = 1.0425402607851875 <= 2^|A| = 4 | all ok: True
normQA2 adversarial ratio: 3.8759765625
Duhamel telescope (Q outside U): 1.247571103928564e-13 | (Q inside U): 3.66400511635346e-14
--- pre2.py (case-(ii) point) ---
Q^(i) == projMat on axis i: 4.446439748506845e-15
case (ii) threshold g^2/L^2 = 0.015625 ; (s,t)=(0.9,0.99): 1-s = 0.09999999999999998 in case (ii)? False
(s,t)=(0.99,0.995): 1-s = 0.01 in case (ii)? True
UN  commutation at case-(ii) point: 4.915417623429601e-14
ThetaN commutation at t=0.995: 1.921486566460083e-13
--- pre.py with g = 1/64 (sz0.lam 0) ---
UN  commutation, (s,t)=(0.9,0.99), A=Idiff: 7.958157941762625e-13
ThetaN commutation, t=0.99, A=Idiff: 7.958078640513122e-13
normQA2: max ratio over 100 random tensors = 1.0425402607851875 <= 2^|A| = 4 | all ok: True
Duhamel telescope (Q outside U): 1.4612804921678514e-12 | (Q inside U): 1.5184354995120252e-12
```
Reading: commutation errors ≈ 1e-14 against a tensor scale 14.7 (the negative control with a non-translation-invariant `S` gives 0.238, so the check can fail); `(normQA2)` holds with ratio ≤ 3.876 ≤ 4; the grid identity holds with `Q` outside and inside `𝒰`.

### Verdict per target
- Target 1 `(normQA2)` + linearity: **PASS** (induction on `A.toList`: `|A a| + |mean| ≤ 2‖A‖`; `card = toList.length`).
- Target 2 commutation (`ThetaN`, `UN`, `Ugen`): **PASS** (new: `Θ·projMat = projMat·Θ`, right-side `tensorKer` lemma, single-index commutation then list induction; hyps `3 ≤ L`, `‖t μ_i‖<1`).
- Target 3 grid `(iisuwjyys)`: **PASS** (pointwise `Q^(A)` applied to `stoppedDuhamelN_at`; F2, F3).
- Target 4 combination for `A=∅`: **PASS** (subtract the `𝓛`, `𝒦` identities of `stNewPQ_holds`; shared data; F1 for the range remark).

## (b) Script output (Sun Oct  4 06:59:37 UTC 2026)
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2112`, branch `t/T2112`. No port: no RBM1D/RBM2D file was read or copied for this ticket (the zero-mode regime has no `d ≤ 2` source), so there is no diff-stat.
```
$ git log -1 --format='%h %an' && git diff --name-only $(git merge-base main HEAD) HEAD && wc -l RBM3D/Induction/ZeroModeCalc.lean
c6ff966 Jun Yin
RBM3D/Induction/ZeroModeCalc.lean
     820 RBM3D/Induction/ZeroModeCalc.lean
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/ZeroModeCalc.lean; echo "grep exit=$?"
grep exit=1
$ lake build RBM3D.Induction.ZeroModeCalc 2>&1 | grep -E 'ZeroModeCalc|error|Build completed'
Build completed successfully (3761 jobs).
$ lake env lean precheck.lean  # temporary file, not committed: import RBM3D; import RBM3D.Induction.ZeroModeCalc; #assert_rbm_axioms
registry pre-check (import RBM3D, import RBM3D.Induction.ZeroModeCalc, #assert_rbm_axioms) exit=0
axiom audit: 3646 theorems, 1277 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
$ # registry lines added to RBM3D/Test/Axioms.lean (lines of diff-stat):
       0
```
`#print axioms` of every public declaration of the file (`lake env lean axioms.lean`, 36 names), names printed only where the line is exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`:
```
lines=      36 standard=36 other=0
ZeroModeCalc_zeroModeOp_add ZeroModeCalc_zeroModeOp_smul ZeroModeCalc_zeroModeOpLin ZeroModeCalc_zeroModeOp_sum zeroModeSet_add zeroModeSet_smul zeroModeSetLin zeroModeSet_zero zeroModeSet_sub 
zeroModeSet_sum zeroModeSet_empty norm_zeroModeOp_le norm_zeroModeSet_le ZeroModeCalc_tensorKer_zeroModeOp ZeroModeCalc_zeroModeOp_tensorKer_comm ZeroModeCalc_zeroModeSet_comm_of_comm 
ZeroModeCalc_zeroModeSet_tensorKer_comm ZeroModeCalc_projMat_comm_of_sums ZeroModeCalc_projMat_mul_Theta_comm ZeroModeCalc_projMat_mul_uKer_comm ZeroModeCalc_projMat_mul_thetaKer_comm zeroModeSet_UN 
zeroModeOp_UN zeroModeOp_ThetaN zeroModeSet_ThetaN ZeroModeCalc_mem_STIdiff ZeroModeCalc_STIdiff_subset_iff sameSignOutside_of_STIdiff_subset sameSignOutside_union_STIdiff Ind.Ugen_eq_UN_EKsgn 
Ind.zeroModeSet_Ugen Ind.zeroModeOp_Ugen Ind.zeroModeCalc_duhamel_at Ind.zeroModeCalc_duhamel_inside_at Gauss.Sizes.zeroModeCalc_LK_expansion Gauss.Sizes.zeroModeCalc_LK_expansion_empty 
```
Target statements, extracted by `extract.py stmts` (declaration lines up to `:=`, whitespace collapsed; `d L : ℕ` `[NeZero L]` are the variables of the enclosing section):
```
-- ZeroModeCalc.lean:124
theorem norm_zeroModeOp_le (i : Fin n) (T : (Fin n → Zd d L) → ℂ) : ‖zeroModeOp d L i T‖ ≤ 2 * ‖T‖
-- ZeroModeCalc.lean:163
theorem norm_zeroModeSet_le (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) : ‖zeroModeSet d L A T‖ ≤ 2 ^ A.card * ‖T‖
-- ZeroModeCalc.lean:91
theorem zeroModeSet_add (A : Finset (Fin n)) (S T : (Fin n → Zd d L) → ℂ) : zeroModeSet d L A (S + T) = zeroModeSet d L A S + zeroModeSet d L A T
-- ZeroModeCalc.lean:96
theorem zeroModeSet_smul (A : Finset (Fin n)) (c : ℂ) (T : (Fin n → Zd d L) → ℂ) : zeroModeSet d L A (c • T) = c • zeroModeSet d L A T
-- ZeroModeCalc.lean:332
theorem zeroModeSet_UN (hL : 3 ≤ L) {m : Fin n → ℂ} {s t : ℝ} (hξ : ∀ i, ‖(t : ℂ) * cycProd m i‖ < 1) (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) : zeroModeSet d L A (UN d L g m s t T) = UN d L g
    m s t (zeroModeSet d L A T)
-- ZeroModeCalc.lean:395
theorem zeroModeSet_ThetaN (hL : 3 ≤ L) {m : Fin n → ℂ} {t : ℝ} (hξ : ∀ i, ‖(t : ℂ) * cycProd m i‖ < 1) (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) : zeroModeSet d L A (ThetaN d L g m t T) =
    ThetaN d L g m t (zeroModeSet d L A T)
-- ZeroModeCalc.lean:450
theorem zeroModeSet_Ugen (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (A : Finset (Fin k)) (T : (Fin k → Zd d L) → ℂ) : zeroModeSet d L A (Ugen
    d L g E σ v w T) = Ugen d L g E σ v w (zeroModeSet d L A T)
-- ZeroModeCalc.lean:493
theorem zeroModeCalc_duhamel_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ} (σ : Fin k → Bool) (A : Finset
    (Fin k)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hjτ : min j (τ ω) ≤ K n) : zeroModeSet d (sz.L n) A (AvecN sz E s t K n (min j (τ ω)) σ ω) = zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam
    n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω))) (AvecN sz E s t K n 0 σ ω)) + ∑ i ∈ Finset.range (min j (τ ω)), zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) (E n) σ
    (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω))) (predIncN sz E s t K n i σ ω)) + ∑ i ∈ Finset.range (min j (τ ω)), zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) (E n) σ
    (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω))) (martIncN sz E s t K n i σ ω))
-- ZeroModeCalc.lean:522
theorem zeroModeCalc_duhamel_inside_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ} (σ : Fin k → Bool) (A :
    Finset (Fin k)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hjτ : min j (τ ω) ≤ K n) : zeroModeSet d (sz.L n) A (AvecN sz E s t K n (min j (τ ω)) σ ω) = Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime
    s t K n 0) (gridTime s t K n (min j (τ ω))) (zeroModeSet d (sz.L n) A (AvecN sz E s t K n 0 σ ω)) + ∑ i ∈ Finset.range (min j (τ ω)), Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
    (gridTime s t K n (min j (τ ω))) (zeroModeSet d (sz.L n) A (predIncN sz E s t K n i σ ω)) + ∑ i ∈ Finset.range (min j (τ ω)), Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
    (gridTime s t K n (min j (τ ω))) (zeroModeSet d (sz.L n) A (martIncN sz E s t K n i σ ω))
-- ZeroModeCalc.lean:563
theorem zeroModeCalc_LK_expansion (d m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)) : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α,
    Finset (Fin (k α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧ ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a = zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a + ∑ α : Fin ℓ, ((ξ α :
    ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) * zeroModeSet d (sz.L n) (A' α) (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) (σ' α) a') (a ∘ ι α)
-- ZeroModeCalc.lean:595
theorem zeroModeCalc_LK_expansion_empty (d m : ℕ) (σ : Fin m → Bool) : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k
    α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧ ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)), STLKM sz n E τ
    (sz.seqHflow n τ ω) σ a = zeroModeSet d (sz.L n) (STIdiff σ) (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a + ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ :
    ℂ)) ^ (m - k α)) * zeroModeSet d (sz.L n) (A' α) (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) (σ' α) a') (a ∘ ι α)
```
Compiled nonempty instances (`extract.py examples`, whitespace collapsed so tactic-block newlines show as spaces; each is an `example` that applies the target at the data stated in the file header of section 7, every deterministic hypothesis discharged by `norm_num`/`decide`; `ω`, `a`, tensors universally quantified or the nonzero point mass `zmcDelta`). Helper data:
```
9:private def zmcSigma : Fin 3 → Bool := ![true, false, true]
12:private noncomputable def zmcDelta : (Fin 3 → Zd 3 4) → ℂ := fun a => if a = 0 then 1 else 0
14:private theorem zmcDelta_ne : zmcDelta ≠ 0 := fun h => by
18:private theorem zmcIdiff_card : (STIdiff zmcSigma).card = 2 := by decide
115:private noncomputable def zmcE : ℕ → ℝ := fun _ => 0
116:private noncomputable def zmcS : ℕ → ℝ := fun _ => 1 / 10
117:private noncomputable def zmcT : ℕ → ℝ := fun _ => 1 / 2
118:private def zmcK : ℕ → ℕ := fun _ => 4
(line numbers above are relative to line 620)
-- ZeroModeCalc.lean:642
example : zmcDelta ≠ 0 ∧ ‖zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta‖ ≤ 2 ^ 2 * ‖zmcDelta‖ := by refine ⟨zmcDelta_ne, ?_⟩ have h := norm_zeroModeSet_le (d := 3) (L := 4) (STIdiff zmcSigma) zmcDelta
    rwa [zmcIdiff_card] at h
-- ZeroModeCalc.lean:649
example : ‖zeroModeOp 3 4 (1 : Fin 3) zmcDelta‖ ≤ 2 * ‖zmcDelta‖ := norm_zeroModeOp_le 1 zmcDelta
-- ZeroModeCalc.lean:653
example : zmcDelta ≠ 0 ∧ zeroModeSet 3 4 (STIdiff zmcSigma) (zmcDelta + (2 : ℂ) • zmcDelta) = zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta + (2 : ℂ) • zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta :=
    ⟨zmcDelta_ne, by rw [zeroModeSet_add, zeroModeSet_smul]⟩
-- ZeroModeCalc.lean:659
example : zeroModeSet 3 4 (STIdiff zmcSigma) (zmcDelta - (3 : ℂ) • zmcDelta) = zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta - (3 : ℂ) • zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta := by rw
    [zeroModeSet_sub, zeroModeSet_smul]
-- ZeroModeCalc.lean:665
example : zeroModeSet 3 4 (STIdiff zmcSigma) (∑ i : Fin 3, (i.val + 1 : ℂ) • zmcDelta) = ∑ i : Fin 3, zeroModeSet 3 4 (STIdiff zmcSigma) ((i.val + 1 : ℂ) • zmcDelta) := zeroModeSet_sum _ _ _
-- ZeroModeCalc.lean:669
example : zeroModeSet 3 4 (∅ : Finset (Fin 3)) zmcDelta = zmcDelta := zeroModeSet_empty _
-- ZeroModeCalc.lean:678
example : zmcDelta ≠ 0 ∧ zeroModeSet 3 4 (STIdiff zmcSigma) (UN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (9 / 10) (99 / 100) zmcDelta) = UN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (9
    / 10) (99 / 100) (zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta) := ⟨zmcDelta_ne, zeroModeSet_UN (by norm_num) zmc_slot_lt_one _ _⟩
-- ZeroModeCalc.lean:686
example : zmcDelta ≠ 0 ∧ zeroModeSet 3 4 (STIdiff zmcSigma) (ThetaN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (99 / 100) zmcDelta) = ThetaN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (99
    / 100) (zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta) := ⟨zmcDelta_ne, zeroModeSet_ThetaN (by norm_num) zmc_slot_lt_one _ _⟩
-- ZeroModeCalc.lean:694
example : zmcDelta ≠ 0 ∧ zeroModeSet 3 4 (STIdiff zmcSigma) (Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) zmcDelta) = Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) (zeroModeSet 3 4
    (STIdiff zmcSigma) zmcDelta) := ⟨zmcDelta_ne, zeroModeSet_Ugen (by norm_num) (by norm_num) zmcSigma (by norm_num) (by norm_num) _ _⟩
-- ZeroModeCalc.lean:703
example : zeroModeOp 3 4 (1 : Fin 3) (Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) zmcDelta) = Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) (zeroModeOp 3 4 (1 : Fin 3) zmcDelta) :=
    zeroModeOp_Ugen (by norm_num) (by norm_num) zmcSigma (by norm_num) (by norm_num) _ _
-- ZeroModeCalc.lean:709
example : projMat 3 4 * Theta 3 4 (1 / 2 : ℝ) ((99 / 100 : ℝ) : ℂ) = Theta 3 4 (1 / 2 : ℝ) ((99 / 100 : ℝ) : ℂ) * projMat 3 4 := ZeroModeCalc_projMat_mul_Theta_comm (by norm_num) (by rw
    [Complex.norm_real]; norm_num)
-- ZeroModeCalc.lean:715
example : tensorKer 3 4 (fun i => uKer 3 4 (1 / 2 : ℝ) (cycProd (fun i => mSigma 0 (zmcSigma i)) i) (9 / 10) (99 / 100)) (zeroModeOp 3 4 (1 : Fin 3) zmcDelta) = tensorKer 3 4 (Function.update (fun i
    => uKer 3 4 (1 / 2 : ℝ) (cycProd (fun i => mSigma 0 (zmcSigma i)) i) (9 / 10) (99 / 100)) 1 (uKer 3 4 (1 / 2 : ℝ) (cycProd (fun i => mSigma 0 (zmcSigma i)) 1) (9 / 10) (99 / 100) * projMat 3 4))
    zmcDelta := ZeroModeCalc_tensorKer_zeroModeOp 1 _ zmcDelta
-- ZeroModeCalc.lean:725
example : SameSignOutside (fun i => mSigma 0 (zmcSigma i)) (STIdiff zmcSigma) := sameSignOutside_of_STIdiff_subset (mSigma 0) zmcSigma (Finset.Subset.refl _)
-- ZeroModeCalc.lean:728
example : SameSignOutside (fun i => PropSpin Complex.I (zmcSigma i)) ((∅ : Finset (Fin 3)) ∪ STIdiff zmcSigma) := sameSignOutside_union_STIdiff (PropSpin Complex.I) zmcSigma ∅
-- ZeroModeCalc.lean:741
example (ω : PathΩ sz0) : zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (AvecN sz0 zmcE zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)) zmcSigma ω) = zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
    (Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 0) (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω))) (AvecN sz0 zmcE zmcS zmcT zmcK 0 0 zmcSigma ω)) + ∑ i
    ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)), zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1)) (gridTime zmcS
    zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω))) (predIncN sz0 zmcE zmcS zmcT zmcK 0 i zmcSigma ω)) + ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)), zeroModeSet 3 (sz0.L 0) (STIdiff
    zmcSigma) (Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1)) (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω))) (martIncN sz0 zmcE zmcS zmcT zmcK 0 i
    zmcSigma ω)) := zeroModeCalc_duhamel_at sz0 zmcE zmcS zmcT zmcK 0 (by norm_num [zmcE]) (by norm_num [zmcS]) (by norm_num [zmcS, zmcT]) (by norm_num [zmcT]) (by norm_num [zmcK]) zmcSigma (STIdiff
    zmcSigma) (fun _ => 3) 4 ω (by norm_num [zmcK])
-- ZeroModeCalc.lean:763
example (ω : PathΩ sz0) : zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (AvecN sz0 zmcE zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)) zmcSigma ω) = Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma
    (gridTime zmcS zmcT zmcK 0 0) (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω))) (zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (AvecN sz0 zmcE zmcS zmcT zmcK 0 0 zmcSigma ω)) + ∑ i ∈
    Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)), Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1)) (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3)
    ω))) (zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (predIncN sz0 zmcE zmcS zmcT zmcK 0 i zmcSigma ω)) + ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)), Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0)
    zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1)) (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω))) (zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (martIncN sz0 zmcE zmcS zmcT zmcK 0 i
    zmcSigma ω)) := zeroModeCalc_duhamel_inside_at sz0 zmcE zmcS zmcT zmcK 0 (by norm_num [zmcE]) (by norm_num [zmcS]) (by norm_num [zmcS, zmcT]) (by norm_num [zmcT]) (by norm_num [zmcK]) zmcSigma
    (STIdiff zmcSigma) (fun _ => 3) 4 ω (by norm_num [zmcK])
-- ZeroModeCalc.lean:786
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A'
    α) ∧ ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)), STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a = zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma) (fun a' => STLKM sz0 0 0 (1 / 2)
    (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a') a + ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) * (etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) * zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => STLKM
    sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) (σ' α) a') (a ∘ ι α) := by obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansion_empty 3 3 zmcSigma exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun
    ω a => h sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ω a⟩
-- ZeroModeCalc.lean:802
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A'
    α) ∧ ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)), zeroModeSet 3 (sz0.L 0) ({2} : Finset (Fin 3)) (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a') a = zeroModeSet 3 (sz0.L
    0) (({2} : Finset (Fin 3)) ∪ STIdiff zmcSigma) (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a') a + ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
    (etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) * zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) (σ' α) a') (a ∘ ι α) := by obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ :=
    zeroModeCalc_LK_expansion 3 3 zmcSigma {2} exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a => h sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ω a⟩
```
Name clash (every public short name of the file, 36 names, against `main` and against the worktree outside the file):
```
names:       36
git grep -nw on main: hits:        0
git grep -nw on HEAD outside own file: hits:        0
main = 2270c89
```

### Narrative
- All proofs are new; no RBM1D/RBM2D text was used. Section (a) is not edited and no (a′) was needed: the line numbers it cites were re-read in the files (`GridDuhamelN.lean:82,161,310`, `Kernel/Evolution.lean:190-205,359,373,629`, `NewPQ.lean:584`, `Step34Pins.lean:330,666`).
- Target 1: `norm_zeroModeOp_le` bounds `|T a - L^{-d} Σ_c T(a[i↦c])| ≤ ‖T‖ + L^{-d}·L^d‖T‖`; `norm_zeroModeSet_le` is induction on `A.toList` with `Finset.length_toList`. Linearity: one-index `add/smul`, list induction (`zmc_foldr_add/smul`), then `zeroModeSetLin` gives `zeroModeSet_zero/sub/sum` by `map_zero/map_sub/map_sum`.
- Target 2: new right-hand identity `ZeroModeCalc_tensorKer_zeroModeOp`, `K ∘ Q^{(i)} = K[i ↦ K_i (I − L^{-d}J)]`, via the involution `(b,c) ↦ (b[i↦c], b_i)` of `(Z_L^d)^n × Z_L^d` (`zmc_sum_update`, `Equiv.sum_comp`). With the merged left identity `zeroModeOp_tensorKer` it gives `Q^{(i)} K = K Q^{(i)}` whenever `projMat K_i = K_i projMat`; `ZeroModeCalc_zeroModeSet_comm_of_comm` lifts a single-index commutation to `Q^{(A)}` by induction on `A.toList`. `projMat` commutes with `SB` (merged `projMat_mul_SB_comm`) and, new, with `Θ_ξ` (`ZeroModeCalc_projMat_comm_of_sums`: row and column sums `(1-ξ)⁻¹`, columns by symmetry `Theta_transpose_of_three_le`), hence with `uKer`, `thetaKer`.
- `ThetaN` is `Σ_i zmcSlot i (thetaKer …)`; for `i ≠ j`, `Q^{(j)}` passes by `Function.update_comm`; for `i = j` by column sums = row sums (`zmc_sum_col_eq_row`, derived from the commutation). `Ugen = UN (fun i => mSigma E (σ i))` by definition; its slot hypothesis is the merged `norm_mul_mSigma_lt_one`. Hypotheses: `3 ≤ L`, `‖t μ_i‖ < 1` (for `Ugen`: `|E| ≤ 2`, `0 ≤ w < 1`); `s` (resp. `v`) is arbitrary.
- Target 3: `Q^{(A)}` applied pathwise to the merged `stoppedDuhamelN_at` (hypotheses at the single index `n`, DECISIONS §29 (4)), split by `GridDuhamelN_Ugen_add`, `zeroModeSet_add`, `zeroModeSet_sum`. The telescope's kernel index is `u_{i+1}` (preflight F2). `…_inside_at` commutes `Q^{(A)}` through `Ugen` at `w = u_{j∧τ}`; `0 ≤ w < 1` comes from `0 ≤ s n ≤ t n < 1`, `j∧τ ≤ K n` (the merged grid lemmas are private, so `zmc_gridTime_nonneg/lt_one` re-prove them). The case condition `1 − s ≤ g²/L²` and any `L`–`W` relation are not used (§29 (2), (3)).
- Target 4: `stNewPQ_holds d m σ A` gives one data `(ℓ,k,ξ,σ',ι,A')` serving both the `𝓛` and the `𝒦` identity; subtracting them (`STLKM = Lloop − STKloop`, `zeroModeSet_sub`) gives the expansion for every `A`; `A = ∅` is the corollary (`zeroModeSet_empty`, `∅ ∪ I_diff = I_diff`). No other form of the `𝒦` half of `STNewPQ` is needed.
- F1: `norm_zeroModeSet_UN_le` (hyp. `0 < (m i).im`) is not used. `sameSignOutside_of_STIdiff_subset` gives `SameSignOutside (fun i => f (σ i)) A` from `I_diff σ ⊆ A` for any `f : Bool → ℂ` (`mSigma E` or `PropSpin m`); `Ind.Ugen_eq_UN_EKsgn` is `rfl`; `ZeroModeCalc_STIdiff_subset_iff` is the hypothesis shape of `STEKNonzero` (`Step34Pins.lean:666`).
- F3 (that `Q^{(A)} martIncN` is again a martingale increment) is not proved: it needs integrability of every coordinate of `AvecN` (left to S3-21, as in (a)).
- No new `Prop`-valued definition, so no registry line in `Test/Axioms.lean`; the registry pre-check exits 0. The build of the module at 06:56:12 UTC (tool log) printed `✔ [3761/3761] Built RBM3D.Induction.ZeroModeCalc (12s)`; `lake build` of the whole library in the worktree at 06:55:20 UTC printed `Build completed successfully (3864 jobs)` (the root `RBM3D.lean` does not yet import the module; the hub adds that at merge).

## (c) Verified Mathlib names used (`lake env lean names.lean`: `(← getEnv).contains name`, one line each)
```
Equiv.sum_comp: true
Fintype.sum_prod_type: true
map_sum: true
map_sub: true
Finset.length_toList: true
Finset.mem_toList: true
List.foldr_cons: true
List.mem_cons_of_mem: true
List.mem_cons_self: true
Commute.sub_right: true
Commute.one_right: true
Commute.smul_right: true
Commute.mul_right: true
Finset.sum_comm: true
pi_norm_le_iff_of_nonneg: true
norm_le_pi_norm: true
Finset.sum_ite_eq': true
Function.update_comm: true
Function.update_idem: true
Function.update_of_ne: true
Function.update_self: true
Finset.mul_prod_erase: true
Finset.prod_congr: true
Finset.sum_sub_distrib: true
mul_left_cancel₀: true
sub_right_injective: true
Finset.empty_union: true
Finset.subset_union_right: true
Finset.sum_apply: true
norm_sum_le: true
norm_sub_le: true
Nat.cast_le: true
Matrix.mul_apply: true
Matrix.one_apply: true
Finset.sum_add_distrib: true
```

## (d) Open issues and paper-delta candidates
- T2112a: the paper's commutation remark (`3_5:1540-1545`) has no hypotheses; Lean needs `3 ≤ L` and `‖t m_i m_{i+1}‖ < 1` (so that `Θ_{tμ}` exists), for `Ugen` also `|E| ≤ 2`, `0 ≤ w < 1`.
- T2112b: `(normQA2)` (paper: `Q^{(i)}`, constant 2) is stated in Lean for `Q^{(i)}` and for `Q^{(A)}` with `2^{|A|}` (product of the one-index bounds).
- T2112c: `(iisuwjyys)` is the pathwise stopped grid Duhamel identity (sum over `i < j∧τ`, kernel `𝒰_{u_{i+1},u_{j∧τ}}`), not the integral in `u`; both the `Q^{(A)}`-outside and -inside forms are stated. The ticket's `𝒰_{u_j,u_k}` on the predictable part is `u_{j+1}` in the merged telescope (preflight F2).
- T2112d: the `lem: newPQ` combination is stated for every `A` (paper `3_5:1590`: `A = ∅`), for `(𝓛−𝒦) = STLKM sz n E τ (sz.seqHflow n τ ω)`.
- T2112e (merged-file observation, F1): `norm_zeroModeSet_UN_le` (`Kernel/Evolution.lean:629`) has `hmi : ∀ i, 0 < (m i).im`, unsatisfiable for `m i = mSigma E false`; mixed-sign `σ` goes through `ekSumDecayNonzero_holds` / `STEKNonzero`.
- Open: F3 (S3-21); root import `import RBM3D.Induction.ZeroModeCalc` by the hub at merge.
