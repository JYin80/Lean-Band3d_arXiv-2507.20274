Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 06:24:44 UTC 2026

### (i) Exponent table

Mathematics of the family glue (no new analysis): `BAMainIndFamTL d R` = `3 ≤ d → ∀ κ ε 𝔡>0, ∃ 𝔠d ∈ (0,1/100], ∀ 𝔠 sz z, BAFlow … → …` (`BA/MainIndOutBA.lean:60`). Every target concludes it, so each constant is produced after `(κ, ε, 𝔡)` and before `(𝔠, sz, z)`.

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | target 1 constant | same `𝔠d` as the hypothesis `BAMainIndFamTL d R` | `R' ⊆ R` (pointwise in `sz, s, t`) | none needed |
| 2 | target 2 constant | `𝔠d = min c₁ c₂` (`c_i` of `R_i`) | `st_conStInd_sub` on `[s,m]`, `[m,t]` needs `s ≤ m`, `m < t`, `t < 1`; `st5_conStInd_mono` needs `0 < min`, `min ≤ c_i`, `t < 1` | `t ≤ T0 < 1` by `BAflow_T0_bounds`; `0 < min` by `lt_min` |
| 3 | `𝔠d` of target 4 (ticket (i)) | `inf'` over `P : Fin 4 × Fin 4` (nonempty) of the target-3 constant at `(i,m) = (P.1, P.2 − P.1)`; fixed by `(κ,ε,𝔡)` | `0 < 𝔠d ≤ 1/100` (finite `inf'` of positives, each `≤ 1/100`); `𝔠d ≤ c_P` so `(con_st_ind)` at `𝔠d` gives it at `c_P` (`st5_conStInd_mono`, `t<1`) | all 16 pairs satisfy `i + (P.2 − P.1) ≤ 3` (truncated subtraction: `P.1 ≤ P.2` gives `P.2 ≤ 3`; `P.1 > P.2` gives `m = 0`, `i ≤ 3`), so target 3 applies to every pair and `P.1 > P.2` needs no vacuity argument |
| 4 | chain length | `i + m ≤ 3` (4 regimes `III, I, II, IV`) | induction on `m` by target 2 (`STRegChain_succ` is `Iff.rfl`); `STRegK i` for `i ≤ 3` is one of the four | step needs `(i+1)+m ≤ 3` from `i+(m+1) ≤ 3` |
| 5 | dimension | `d` general, `3 ≤ d` | `STStage_le` needs `2 ≤ d`; `STRegChain_of_class` needs `3 ≤ d`, `s<t`, `t<1`, derives `0 < lam²` | the guard of `BAMainIndFamTL` is `3 ≤ d`: slack 1 at `d = 3` for `STStage_le`, 0 for `STRegChain_of_class` |
| 6 | cuts | `c₁ = 1 − lam²`, `c₂ = 1 − lam²/L²`, `c₃ = 1 − lam²/L^d` (`STCutK`) | strictly increasing in `k` when `0 < lam²`, `L ≥ 3`, `d ≥ 3` | at `sz0, n = 0` (`lam² = 2⁻¹²`, `L = 4`): see (ii); `t = 1/2 ≤ c₁`, slack `1/2 − 2⁻¹² ` |
| 7 | classes | finite cover by `Nat.nth` of the 16 preimages `{n | STPattern n = P}` (finite ones are eventually absent, `nth_cover`) | `φ_P` strictly monotone (`Nat.nth_strictMono` on infinite classes) | `Tendsto φ_P atTop atTop` gives `comp_admissible` (same `𝔠, 𝔡`), `STConStInd_comp`; `BAdom`, `BAflowT0`, `BAWinBulk`, `BAFamZ` are pointwise in `n`, so they restrict to `sz.comp φ` with the same `κ, c₁` (no halving, unlike the tail `κ/2`) |
| 8 | window `c₁` | `1/3` | `0 < c₁ ≤ 1/2`; passes unchanged to the class (the `∀ c₁` of the def) | `1/6` to the upper bound |
| 9 | extension of a class member | `Function.extend φ z'' z ∈ Fam(sz,z,c₁,s)` | `φ` injective; on `range φ` the condition is that of `z''` at `j`; off the range it is `BAFamZ_main` | none |
| 10 | restriction of a member | `z' ∈ Fam(sz,z,c₁,t)` gives `z' ∘ φ ∈ Fam(sz.comp φ, z∘φ, c₁, t∘φ)` | pointwise (`BAFamZ` is `∀ n`); `BAflowEs`/`BAflowT0` of `sz.comp φ` at `j` are those of `sz` at `φ j` | none |
| 11 | TL2 | `BATwistLoopLaw` passes unchanged (conjunct 6 down, conjunct 7 up) | `Bctl (sz.comp φ) j (τ (φ j)) = Bctl sz (φ j) (τ (φ j))` | none |
| 12 | `withLam 0` law | `seqP (sz.withLam 0)` pulled back by `reindex` is `seqP ((sz.comp φ).withLam 0)` (`seqP_withLam_reindex_preimage`, `φ` injective) | needed for `hlaw` of every transport | none |

Fill-in table of the ticket (§269 (5)):
- (i) `𝔠d`: rows 2 and 3 (`min`, `inf'`; ticket F4: no def).
- (ii) route per target (band line → BA line): 1 `MainIndRegimes:105` → mono with `BAMainIndFamTL` hypothesis, same constant; 2 `:266-299` (`STMainIndRAt_seq`) → target 2: constants `∃` inside, `hR₁/hR₂` at the cut `m`, the six hypotheses of stage 2 at `m` for every member of `Fam(m)` from stage 1's seven by `STLocalMaxgL_of_STLocalEntrygL` (drop `STLmaxgL`); 3 `:586-614` → induction on `m` by target 2 (no common constant needed, the constant is inside each `BAMainIndFamTL`); 4 `:616-668` → rows 3, 7-12; 5 probe `:3086` → row 9; 6 → rows 11-12 and the 13 transports.
- (iii) transports through `stochDomAt_iff_comp_cover`: 6 down (LK, Decay, DecayStrong, LocalMax, Exp2, TL2) and 7 up (LK, Lmax, Decay, Exp2, LocalEntry, DecayStrong, TL2), 13 in all. Every predicate is `PrecL` with `ξ ∘ reindex = ξ ∘ φ` pointwise (`hξ`, `hζ` by `rfl`: `C.L, C.K, C.GM, twL2', twK, STWB, Bctl` of `sz.comp φ` at `j` are those of `sz` at `φ j`), except `STExp2gL`, whose left side is `‖∫ L ∂μ − K‖` and needs `integral_reindex` (as `baConclShift`, `MainIndOutBA:172`).
- (iv) registry preview: targets 1-4 conclude head `BAMainIndFamTL`; their hypotheses are `BAMainIndFamTL` (already listed, `Test/Axioms.lean:140`); privates carry `STLKgL … BATwistLoopLaw` (already listed at `:133, :135, :136, :141, :189, :204, :215`). Expected new premises: 0; owner-text edits only.
- (v) lines: bottom-up 260 / 365 / 615, calibrated 350-467, stop 800, 2,000 per file: unchanged by this preflight.
- (vi) instance numbers: (ii) below.
- (vii) n/a, because the terminal is T2511 row b (V2O-C1).

### (ii) One concrete nondegenerate instance (`d = 3`)

Data: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))⁵`, `lam_n = (2(n+1))⁻⁶`); `zSeq`; `κ = 1/4`, `(ε,𝔠,𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`; `s ≡ 1/10 < m ≡ 3/10 < t ≡ 1/2`; member `BAzSrc sz0 zSeq (2/3) (17/25)` of `Fam(1/2)` (`MainIndOutBA_mem u := 1/2`: `max(1/2, 2/3) ≤ max(2/3, 2/3)`, slack 0, an equality `2/3 ≤ 2/3`).
Facts from files: `BAt0 z m = Im m/(Im m + Im z)` (`BA/MFixedPoint.lean:279`); along `zSeq`, `Im m + Im z = 6/5` and `Im m ≥ 4/5` (`mS_im_half`, `FlowPins:1147`, hypothesis `lam² L³ ≤ 1/64`, equality at `n = 0`), so `T0 ≥ (4/5)/(6/5) = 2/3` (`t0_sz0`, `FlowPins:1227`) and `T0 < 1`; `Bctl n c ≤ 2 (1−c)⁻¹ (W_n³)⁻¹` (`Bctl_const_le`, `Induction/Defs.lean:472`).
`(con_st_ind)` at `[1/10, 1/2]`, for the constant `𝔠d > 0` of target 4 (every `𝔠d > 0`, `s1Setup_conStInd_const`, `Step1Setup:1226`): `Bctl^𝔠d ≤ (4 (2(n+1))⁻¹⁵)^𝔠d ≤ (1−t)/(1−s) = 5/9 < 1` for `n` past the thresholds printed below (it is an `∀ᶠ n` statement; no threshold enters a witness).
Not external: the four regime steps and the six family conjuncts stay hypotheses (T2511 produces the steps); the deterministic side is discharged.

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2512/inst.py` (exact `Fraction` arithmetic for `n < 3000`; closed form for the thresholds)

```
pattern (0,0) for n<3000
regime III at [s,m] and [m,t]: max lam^2 = 1/4096 <= 1/2
s<m<t<1; lam^2 L^3 <= 1/64 (n=0: 1/64 )
T0 >= (4/5)/(6/5) = 2/3 > t = 1/2 ; s<=t<=T0<1
window c1=1/3 in (0,1/2]: True ; kappa,eps,dd>0; 1-t= 1/2 1-s= 9/10 ratio= 5/9
cd= 1/100 threshold n >= 2.700e+01 (finite: con_st_ind is an eventual statement)
cd= 1/1000 threshold n >= 5.718e+16 (finite: con_st_ind is an eventual statement)
cd= 1/10000 threshold n >= 8.333e+169 (finite: con_st_ind is an eventual statement)
inf' over Fin4xFin4 of 16 constants in (0,1/100]: 1/1600 True
i+m<=3 for all 16 pairs
```

Reading: the pattern of `[1/10, 1/2]` is `(0,0)` at every `n` (`1/2 ≤ c₁(n) ≥ 1 − 2⁻¹²`), so there is one class and regime (iii) holds on `[s,m]` and `[m,t]` (the split `T2512_InstSeqReg` is hypothesis-free); `(con_st_ind)` is eventual with threshold `n ≥ 27` at `𝔠d = 1/100` (the thresholds at smaller `𝔠d` are huge but belong to an `∀ᶠ`, and the Lean discharge is the limit `Bctl → 0` of `s1Setup_conStInd_const`, not a witness). The `inf'` constant of target 4 is any positive number `≤ 1/100` (the 16-constant demo gives `1/1600`).

### Verdict
- Target 1 `baMainIndFamTL_mono`: PASS.
- Target 2 `baMainIndFamTL_seq`: PASS.
- Target 3 `baMainIndFamTL_chain`: PASS.
- Target 4 `baMainIndFamTL_of_regimes`: PASS (all `d ≥ 3`; no `STStep5IIIgL`; the constant row 3 closes).
- Target 5 private `MainIndGlue_extendMember`: PASS (rows 9, 10).
- Target 6 private `MainIndGlue_down` / `_up`: PASS (rows 11-12, 13 transports).
- Imports fixed: `RBM3D.BA.MainIndOutBA`, `RBM3D.Induction.MainIndRegimes`.
- No pin, row or stop line is moved; no probe section needs porting (F2 holds: the band layer and `SizesComp` carry no carrier).

Overall: PASS.

## (b) Script output (prover stage 1b)

Branch `t/T2512` at `0810e3e2`, from main `97779231`; report written Thu Oct 15 06:43:24 UTC 2026.

### (1) Size against the booked prices
```
$ wc -l RBM3D/BA/MainIndGlue.lean
     436 RBM3D/BA/MainIndGlue.lean
$ git diff main...t/T2512 --stat
 RBM3D.lean                |   1 +
 RBM3D/BA/MainIndGlue.lean | 436 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |  16 +-
 3 files changed, 445 insertions(+), 8 deletions(-)
```
Ticket prices (lo / central / hi): bottom-up 260 / 365 / 615, calibrated 350-467, T2503 540 / 700 / 1,100, stop line 800. The file has 436 lines: central x1.19, inside the calibrated band 350-467, below the bottom-up high 615. No probe section was ported.

### Build, axioms
```
$ lake build RBM3D.BA.MainIndGlue   (tail)
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4161 jobs).
$ lake build   (whole library, runs #assert_rbm_axioms; exit 0; tail)
 RBM.Gauss.Sizes.STLWT].
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4415 jobs).
$ lake env lean pins.lean   (scratch, uncommitted: the pins of docs/tickets/checks/T2512-check.lean plus the examples below; exit 0, no error)
'RBM.BA.baMainIndFamTL_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_of_regimes' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`baMainIndFamTL_of_regimes` depends on `_chain`, `_seq` and the private lemmas, so its line covers them. `pins.lean` adds `example (d : ℕ) : T2512_Mono d := baMainIndFamTL_mono d`, likewise `T2512_Seq`, `T2512_Chain`, `T2512_OfRegimes`, `T2512_ExtendMember`, `T2512_DownShape`, `T2512_UpShape` (private ones through `open private`), and `T2512_InstSeqReg`, `T2512_InstOfRegimes` proved by the in-file instance terms; all elaborate.

### (2)-(3) Targets, extracted from the file by script (`awk` from `theorem <name>` to `:= by`)
```
theorem baMainIndFamTL_mono (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : BAMainIndFamTL d R) : BAMainIndFamTL d R' := by
theorem baMainIndFamTL_seq (d : ℕ) (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h₁ : BAMainIndFamTL d R₁) (h₂ : BAMainIndFamTL d R₂) : BAMainIndFamTL d (STRegSeq R₁ R₂) := by
theorem baMainIndFamTL_chain (d : ℕ) (h₃ : BAMainIndFamTL d STReg5III) (h₁ : BAMainIndFamTL d STReg5I)
    (h₂ : BAMainIndFamTL d STReg5II) (h₄ : BAMainIndFamTL d STReg5IV) :
    ∀ m i : ℕ, i + m ≤ 3 → BAMainIndFamTL d (STRegChain i m) := by
theorem baMainIndFamTL_of_regimes (d : ℕ) (h₃ : BAMainIndFamTL d STReg5III) (h₁ : BAMainIndFamTL d STReg5I)
    (h₂ : BAMainIndFamTL d STReg5II) (h₄ : BAMainIndFamTL d STReg5IV) : BAMainIndFamTL d STAny := by
private theorem MainIndGlue_extendMember {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (z'' : ℕ → ℂ) (h : BAFamZ (sz.comp φ) (fun j => z (φ j)) c₁ (fun j => u (φ j)) z'') :
    BAFamZ sz z c₁ u (Function.extend φ z'' z) := by
```
Statement diff against the pins is the compile of `pins.lean` above: each target is accepted at its `T2512_*` type by `example ... := target`. Binder form: the targets take `(d R R' hRR h)` etc. as explicit binders; the pins are the `∀` forms of the same text.
Routes (band line -> BA line): 1 `MainIndRegimes:105` -> file `:46` (same constant); 2 `:266-299` -> `:57` (`st_conStInd_sub`, `st5_conStInd_mono`, `BAflow_T0_bounds`, `STLocalMaxgL_of_STLocalEntrygL`); 3 `:586-614` -> `:82` (induction on `m`, `Iff.rfl` with `STRegSeq`); 4 `:616-668` -> `:288` (`choose` of the 16 chain constants, `Finset.inf'`, `STPattern`, `nth_cover`, `STRegChain_of_class`, `comp_admissible`, `STConStInd_comp`, `extendMember`, `down`, `up`); 5 probe `:3086` -> `:101`.

### (4) The 13 transports (one `stochDomAt_iff_comp_cover`, through `MainIndGlue_precIff`, per predicate; `hlaw` = `seqP_withLam_reindex_preimage`)
```
$ grep -nE "^private theorem MainIndGlue_(LK|Lmax|Decay|DecayStrong|LocalMax|LocalEntry|Exp2|TL2)_iff|^private theorem MainIndGlue_(precIff|down|up|exp2_eq)" RBM3D/BA/MainIndGlue.lean | cut -c1-60
123:private theorem MainIndGlue_precIff {d : ℕ} (sz : Sizes 
135:private theorem MainIndGlue_exp2_eq {d : ℕ} (sz : Sizes 
147:private theorem MainIndGlue_LK_iff {d : ℕ} (sz : Sizes d
158:private theorem MainIndGlue_Lmax_iff {d : ℕ} (sz : Sizes
168:private theorem MainIndGlue_Decay_iff {d : ℕ} (sz : Size
187:private theorem MainIndGlue_DecayStrong_iff {d : ℕ} (sz 
204:private theorem MainIndGlue_LocalMax_iff {d : ℕ} (sz : S
213:private theorem MainIndGlue_LocalEntry_iff {d : ℕ} (sz :
224:private theorem MainIndGlue_Exp2_iff {d : ℕ} (sz : Sizes
237:private theorem MainIndGlue_TL2_iff {d : ℕ} (sz : Sizes 
250:private theorem MainIndGlue_down {d : ℕ} (sz : Sizes d) 
264:private theorem MainIndGlue_up {d : ℕ} (sz : Sizes d) (z
```
Down (`MainIndGlue_down`, 6 uses): LK, Decay, DecayStrong, LocalMax, Exp2, TL2. Up (`MainIndGlue_up`, 7 uses): LK, Lmax, Decay, Exp2, LocalEntry, DecayStrong, TL2. `hξ`, `hζ` are `fun _ _ _ _ => rfl` for every predicate except `STExp2gL`, whose `hξ` is `MainIndGlue_exp2_eq` (`Sizes.integral_reindex`, as `MainIndOutBA:172`).

### (5) Instances (`d = 3`; `sz0`, `zSeq`; `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2`, member `BAzSrc sz0 zSeq (2/3) (17/25)`; `open private MainIndOutBA_flow MainIndOutBA_win MainIndOutBA_mem`)
Hypothesis-free: the split at `m ≡ 3/10`, the pattern `(0, 0)` at every `n`, target 5 along `φ = (2 ·)`. Hypotheses left in the other examples: the regime steps (producers: T2511) and the six conjuncts on `Fam(1/10)` (`Hyp6`); `(con_st_ind)` is discharged by `s1Setup_conStInd_const` at the constant that the target produces. The seven examples of section 5 (lines 360-432) and the target-4 instance verbatim:
```lean
367: -- the regime-(iii) split of `[1/10, 1/2]` at `3/10` (target 2, hypothesis-free)
368: example : STRegSeq STReg5III STReg5III sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
371: -- the stage pattern of `[1/10, 1/2]` along `sz0` is `(0, 0)` at every `n` (one class, regime (iii); hypothesis-free)
372: example : ∀ n, STPattern sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) n = (0, 0) := fun n => by
386: -- target 5 along `φ = (2 ·)`: the member `mem0 ∘ φ` of `Fam(1/2)` along `sz0.comp φ`, extended by the main flow (hypothesis-free)
387: example : BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 2)
392: -- target 1: `STAny ⊇ STReg5III`; the step at `STReg5III` from the step at `STAny`, applied at the data
393: example (h : BAMainIndFamTL 3 STAny) (hyp : Hyp6) :
402: -- target 2 at `R₁ = R₂ = STReg5III`, cut at `m ≡ 3/10`, applied at the data
403: example (h : BAMainIndFamTL 3 STReg5III) (hyp : Hyp6) : ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Concl7 := by
412: -- target 3 at `(i, m) = (0, 0)` (`STRegChain 0 0 = STReg5III`), applied at the data
413: example (h₃ : BAMainIndFamTL 3 STReg5III) (h₁ : BAMainIndFamTL 3 STReg5I) (h₂ : BAMainIndFamTL 3 STReg5II)
422: -- target 4 (`T2512_InstOfRegimes`): the four regime steps and the six conjuncts on `Fam(1/10)` are the hypotheses
423: example (h₃ : BAMainIndFamTL 3 STReg5III) (h₁ : BAMainIndFamTL 3 STReg5I) (h₂ : BAMainIndFamTL 3 STReg5II)

-- target 4 (`T2512_InstOfRegimes`): the four regime steps and the six conjuncts on `Fam(1/10)` are the hypotheses
example (h₃ : BAMainIndFamTL 3 STReg5III) (h₁ : BAMainIndFamTL 3 STReg5I) (h₂ : BAMainIndFamTL 3 STReg5II)
    (h₄ : BAMainIndFamTL 3 STReg5IV) (hyp : Hyp6) : Concl7 := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_of_regimes 3 h₃ h₁ h₂ h₄ le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) trivial hyp
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))

end Inst
```

### (6) Registry before / after (the `#assert_rbm_axioms` scan of `lake build`; main `97779231` vs branch)
```
before (log of `lake build RBM3D` after the first commit of the new file, which was not yet imported by RBM3D.lean; no registry edit):
  7664:  RBM.BA.BAMainIndFamTL: 3 [no certificate]
  registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet
after:
7664:  RBM.BA.BAMainIndFamTL: 7 [no certificate]
7752:registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded; 163 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
7915:non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each w
set difference of the "carry nothing yet" lists (python over the two logs): new [RBM.BA.BAMainIndFamTL], dropped [], 162 -> 163
```
Ledgers unchanged (2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded), 0 new premises; `BAMainIndFamTL` joins "carry nothing yet" as the ticket predicted (note (3)), kept. `git diff main...t/T2512 -- RBM3D/Test/Axioms.lean` touches 8 lines (133, 135, 136, 140, 141, 189, 204, 215), owner texts only; untouched: 139, 143, 186, 188, 192, 193, 224, T2510 lines.

### (7) Hypothesis greps (command, output; label after `#`)
```
$ grep -cE "mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT" RBM3D/BA/MainIndGlue.lean   # C1, expect 0
0
$ grep -c STStep5IIIgL RBM3D/BA/MainIndGlue.lean   # Q4, expect 0
0
$ grep -cE "^(private )?(noncomputable )?(def|abbrev|structure) " RBM3D/BA/MainIndGlue.lean   # X1-C4, expect 0
0
$ grep -n withLam RBM3D/BA/MainIndGlue.lean | grep -v "withLam 0)" | cut -c1-120   # UBA: withLam lines not of the form `X.withLam 0)`
122:`seqP_withLam_reindex_preimage`, `SizesComp:239`). -/
131:    (fun k s => seqP_withLam_reindex_preimage sz (φ k) 0 (hφ k).injective s) ξ ζ ξ' ζ' hξ hζ
$ grep -c "· + n₀" RBM3D/BA/MainIndGlue.lean   # UBA, expect 0
0
$ grep -E "baMainIndFamTL_(III|I|II|IV)|MainIndFamTL_|MainIndRegBA|BAStep6R|baStep6" RBM3D/BA/MainIndGlue.lean | grep -vcE "baMainIndFamTL_(mono|seq|chain|of_regimes)"   # F1 cut minus the four own target names (the ticket pattern MainIndFamTL_ also matches them), expect 0
0
$ grep -cE "baMainIndFamTL_three|baMLOutTL_three|unMLOutBA_three" RBM3D/BA/MainIndGlue.lean   # V2O-C1 terminal names, expect 0
0
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/BA/MainIndGlue.lean   # hygiene, expect 0
0
$ grep -rlE "baMainIndFamTL_(mono|seq|chain|of_regimes)|MainIndGlue_" RBM3D --include="*.lean" | grep -vE "BA/MainIndGlue.lean|Test/Axioms.lean" | wc -l   # name clash, code files outside this file and Axioms.lean (registry text), expect 0
       0
$ grep -c "∃" RBM3D/BA/MainIndGlue.lean   # U5S-C3: lines with ∃ (all: `∃ k, n ∈ Set.range` in cover hypotheses, `∃ P` in one proof, `∃ 𝔠d` in the example conclusions; none after (sz, z) in a target statement)
15
$ git diff main...t/T2512 --stat -- RBM3D/Chain RBM3D/Induction RBM3D/Graph | wc -l   # scope: Chain/Induction/Graph unchanged, expect 0
       0
$ git diff main...t/T2512 --stat -- RBM3D/BA | head -3   # scope: merged BA files, only the new file
 RBM3D/BA/MainIndGlue.lean | 436 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 436 insertions(+)
```

Narrative.
- Route as the ticket: the band glue with the pattern layer (`STPattern`, `STRegChain_of_class`, `nth_cover`) and the subsequence layer used verbatim; no probe section was ported, no stop rule fired.
- The constant of target 4 is `Finset.univ.inf'` of the 16 constants `c P` chosen (`choose`) from `baMainIndFamTL_chain` at `(P.2 - P.1, P.1)`; `i + m ≤ 3` holds for all 16 pairs by `omega` (truncated subtraction), so the `P.1 > P.2` pairs need no vacuity argument (preflight row 3). `hinf : inf' ≤ c P` gives `(con_st_ind)` at `c P` through `st5_conStInd_mono` with `t < 1` (`BAflow_T0_bounds`).
- The down transport acts on `Function.extend (φ P) z'' z`; `Function.Injective.extend_apply` rewrites `ext ∘ φ P = z''`; `MainIndGlue_down` is applied at `k = P`.
- The iff lemmas carry explicit `ξ'`, `ζ'`: with `_` for them the elaboration failed (type mismatch, then a heartbeat timeout).
- No `STStep5IIIgL`, no terminal name, no def. `local notation Hyp6/Concl7` (under `set_option quotPrecheck false`) abbreviates the example statements only; it is not a declaration.

## (c) Verified names used (all compile in the file)
- `Function.Injective.extend_apply`
- `Function.extend_apply'`
- `Finset.inf'_le`
- `Finset.lt_inf'_iff`
- `Finset.mem_univ`
- `Nat.nth_strictMono`
- `Nat.nth_mem_of_infinite`
- `StrictMono.tendsto_atTop`
- `inv_anti₀`
- `pow_le_pow_left₀`
- `lt_min`
- `min_le_left`
- `min_le_right`
- `Prod.ext`
- `Fin.ext`
Project: `STRegChain_of_class`, `STPattern`, `nth_cover`, `Sizes.stochDomAt_iff_comp_cover`, `seqP_withLam_reindex_preimage`, `Sizes.integral_reindex`, `comp_admissible`, `STConStInd_comp`, `st_conStInd_sub`, `st5_conStInd_mono`, `STLocalMaxgL_of_STLocalEntrygL`, `BAflow_T0_bounds`, `BAFamZ_main`, `BAflowEs_congr`, `BAflowT0_congr`, `s1Setup_conStInd_const` (namespace `RBM.Ind.Step1SetupInst`). Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none beyond the existing D536, D723 (the targets are the family form of the merged band glue; no Lean/paper statement difference was introduced).
- Observation: the ticket's F1 cut grep (`MainIndFamTL_`) cannot be 0 because it matches this ticket's own target names; the check above excludes them.
- Registry line `:136` now says "then as `STLocalEntrygL`" where the ticket text says "then as `:141`": same meaning, no line-number reference inside a registry text.
- Section (a): no correction needed.
