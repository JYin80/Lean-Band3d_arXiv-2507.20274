Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 12:51:34 UTC 2026

Targets (math only): kernel `U = Step2Gen_UN C n σ s t` = `A ↦ Σ_b Π_i uKer_{σ_i,σ_{i+1}}(s,t)_{a_i b_i} A_b`, `uKer_{σσ'}(s,t) = (1 - sX)(1 - tX)⁻¹`, `X = M^{(σσ')}S` (`Chain/Step2Gen.lean:192`).
T3 = semigroup law (`T2453_USemigroup`); T1 = telescope; T5 = stopped Duhamel (G1); T6 = stopped Azuma (G3); T2 = bridge to `Ugen`; T4 = vocabulary.

### (i) Exponent table (no exponents; the thresholds and constants the targets use)
| quantity | value at the instance | constraint | slack |
|---|---|---|---|
| `d` | 3 | band `Zd d L`; `3 ≤ d` not used by targets | - |
| `sz.L 0` | 4 | `3 ≤ L` for `ukerMat_self/mul` (`Path/Kernel:77,103`), `Sizes.three_le_L` | 1 |
| `g = sz.lam 0` | 1/64 | `SB` doubly stochastic, `‖SB‖ = 1` (needs `3 ≤ L`) | measured: row-sum dev 1e-16, `‖S‖₂ = 1.0`, spec S ⊂ [0.997075, 1] |
| `E 0` | 0 | `|E| ≤ 2` for `norm_mul_mSigma_lt_one` (`Defs/Semicircle:91`); `|E n|<2` in band G1/G3 | 2 |
| `m(E)`, `μ = m(σ)m(σ')` | `m = i`; `μ = ±1` | `‖μ‖ = 1` (`norm_mSigma`) | equality |
| `s` | 1/10 | `0 ≤ s` | 1/10 |
| `t` | 1/2 | `s ≤ t < 1` | `t - s = 2/5`, `1 - t = 1/2` |
| `K` | 4 | `K n ≠ 0`; `m ≤ K` | 4 |
| `gridStep` | `(t-s)/K = 1/10` | `≥ 0` | 1/10 |
| grid times `u_j`, `j ≤ 4` | 0.1, 0.2, 0.3, 0.4, 0.5 | `0 ≤ u_j < 1` for `j ≤ min j τ ≤ K` (T1, T5 hypotheses) | `1 - u_K = 1/2` |
| `‖v μ‖` on the grid | `v ≤ 1/2` | `< 1` (slot condition of `ukerMat_self/mul`) | `1/2` |
| T3 window | `v, w ∈ [0,1)`, `u ∈ ℝ` arbitrary | band: `‖vμ‖ = v < 1` (tight: `1-vμλ` has min modulus `1-v` for `μ = 1`, `λ_max = 1`) | `v=0.99`: 0.0100; `v=1`: 4e-16 (fails) |
| `τ`, `j`, `min j τ` | 3, 4, 3 | `min j τ ≤ K`; T6: `m ≤ K`, `{j<τ}` is `filt j`-measurable (constant `τ` is) | 1 |
| T6 constant | 4, `4Σc` | `azuma_complex` (`Path/Azuma:87`); `Σ c = 0` is harmless (Lean `x²/0 = 0`, bound `4 ≥ P`) | m=3, c=1, x=8: `4e^{-16/3} = 0.0193` |
| T6 premise (d) | sub-Gaussian proxy `c_j` per weighted increment | external input (producer `azumaSubGN`, T4s2); band `:553` | see (ii) |

### (ii) One nondegenerate instance (band, `bandStep2Mat sz0 (fun _ => 0)`)
Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), `n = 0`, `E ≡ 0`, `σ = (+,+,-)` (`k = 3`, slots `(+,+),(+,-),(-,+)`), `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`, `j = 4` (`min j τ = 3 ≤ K`).
Check (T3 for all four charge pairs incl. `u ∈ {-3, 7}`; T1 on 4 random complex 262144-entry tensors `A_0..A_4`, `m = 3`; the slot kernel is `(1-vμS)(1-wμS)⁻¹` with `M^{(σσ')} = μ·1` from `Step2Kern_Mss_band`, `Chain/Step2Gen:268`):
```
$ cd .../scratchpad/T2453 && PYTHONPATH=./pylib python3 inst.py
rowsum max dev 1.1102230246251565e-16 opnorm S 1.0
target3 (USemigroup) max err: self 1.9984014443252818e-15 comp (incl. u=-3,7) 1.5916157281026244e-12
grid times [0.1, 0.2, 0.30000000000000004, 0.4, 0.5] all in [0,1): True slack 1-u_K = 0.5
target1 telescope residual (k=3,sigma=(+,+,-),m=3, tensor entries 262144 ): 3.468447607305094e-14 scale 5.1189124402740545
target6 RHS 4*exp(-x^2/(4*sum c)) at m=3,c=1,x=8: 0.019311799975325766
norm slot v*|mu| = v <1 : max over grid 0.5
$ PYTHONPATH=./pylib python3 tight.py | tail -5
spec S in [0.997075, 1.000000]
(+,+) mu = (-1+0j) min_lambda |1-v mu lambda| at v=0.5: 1.4985, at v=0.99: 1.9871, at v=1: 2.00e+00
(+,-) mu = (1+0j) min_lambda |1-v mu lambda| at v=0.5: 0.5000, at v=0.99: 0.0100, at v=1: 4.44e-16
(-,+) mu = (1+0j) min_lambda |1-v mu lambda| at v=0.5: 0.5000, at v=0.99: 0.0100, at v=1: 4.44e-16
(-,-) mu = (-1-0j) min_lambda |1-v mu lambda| at v=0.5: 1.4985, at v=0.99: 1.9871, at v=1: 2.00e+00
```
T5 at this data: for each `i < 3`, `(Y_i - U A_i) + (A_{i+1} - Y_i) = A_{i+1} - U A_i` is a ring identity per entry (`Y` cancels, no measure hypothesis), so T5 is T1 at `u = gridTime`, `A_i = STLKMg … i`; instance satisfied since T1 residual `~1e-14` at these times.
T6 at this data: premise (a) (T3) is not used by T6; premise (b) measurability holds by `walk_measurable_loopFine` (`Path/Walk:794`) ∘ `pathH_measurable_filt` (`Path/Stop:159`) on a `Measurable.sub measurable_const` (as `GridDuhamelN:395-400`); premise (c) `isProbabilityMeasure_pathP` (`Path/Walk:94`, an `instance`). Premise (d) with `τ ≡ 3`, `m = 3` is an external hypothesis: the sub-Gaussian bound of a Gaussian-walk functional is T4s2's `azumaSubGN`; the increments `U ξ_{j+1}` are not bounded (the grid walk is a centred Gaussian, `Path/Walk:30-31`), so no Hoeffding-type constant can be computed here, and the limit computation of TEAM §8 lesson 14 is not available. Concrete discharges: `τ ≡ 0, c ≡ 0` (the indicator vanishes, band `:752-778`) and the conclusion value above; `τ ≡ 3` keeps (d) as a hypothesis of the example (allowed by CLAUDE §4 step 2: another gate's pin).

### (iii) Hypothesis table (band fact → generic premise → band discharge → BA source)
| band fact | generic premise | band discharge | BA |
|---|---|---|---|
| `3 ≤ L`, `|E| ≤ 2` (`GridDuhamelN:91,108`) | `Step2Gen_USemigroup C n` (T3) | `step2Gen_USemigroup_band`: `Step2Kern_uKer_band` (`Chain/Step2Gen:305`) + `ukerMat_self` (`Path/Kernel:103`), `ukerMat_mul` (`:77`), `norm_mul_mSigma_lt_one`, `sz.three_le_L n` | T4-BA: `BAuKer_self/_comp` (`BA/TwistGrid:184,188`) via `Step2Kern_uKer_BA` (`Chain/Step2Kern:112`) |
| `|E n| < 2`, `0≤s≤t<1`, `K≠0` (G1, `:293`) | `∀ n, USemigroup` + same `s,t,K` premises | `|E n|<2` → T3 band theorem; grid arithmetic `GridDuhamelN_gridTime_nonneg/_lt_one` (private, `:249,256`) | T4-BA (T3 at `baFM`) |
| `[IsFiniteMeasure (pathP sz)]` | `[IsProbabilityMeasure Cm.Pp]` | `isProbabilityMeasure_pathP` | T4-BA |
| (implicit) measurability of `AvecN` (`GridDuhamelN:395`) | `∀ j b, Measurable[filt sz j] (STLKMg … j σ b)` (T6 premise) | `walk_measurable_loopFine` ∘ `pathH_measurable_filt`, `.sub measurable_const` | T4-BA (`Hpath = λ₀Ψ + pathH`) |
| conditional sub-Gaussian (`:553`) | same, `Step2Gen_UN` for `Ugen`, `martIncNg` for `ξ` | input (T4s2 `azumaSubGN`) | input |
| five window premises of G3 | dropped (unused, `:553`) | - | - |

### (iv) Bridge table
| generic | band bridge | kind |
|---|---|---|
| `Step2Gen_UN` (T1, T5, T6) | `bandStep2_Ugen : Ugen d (sz.L n) (sz.lam n) (E n) σ v w A = Step2Gen_UN (bandFM sz E) n σ v w A` | `Ugen` unfolds to `UN` by definition (`GridDuhamelN:65`), so the check's `↔` is `Iff.rfl`; the equality itself is **proved**: `(Step2Kern_UN_band …).symm` (`Chain/Step2Gen:328`; its proof is `funext`/`simp [Step2Kern_uKer_band]`, not `rfl`) |
| `Step2Gen_UN_add` / `_self` / `_comp` / `_UNHom` / `_duhamel_telescope` | `GridDuhamelN_Ugen_add/_self/_comp/_UgenHom/_duhamel_telescope` (`:82,91,108,145,161`) | proved here; statements differ only by `Ugen ↦ Step2Gen_UN`, `(3 ≤ L, |E| ≤ 2) ↦ T3` |
| `AvecNg` | `bandStep2_AvecN` | `rfl` (`bandStep2_STLKM` is `rfl`, `Chain/Step2Gen:417`; `Hpath` field `:= pathH`) |
| `martIncNg` | `bandStep2_martIncN` | `rfl` (`condExp (filt sz j) (pathP sz)`) |
| `predIncNg` | `bandStep2_predIncN` | proved: `bandStep2_Ugen` under `condExp`-difference (`funext`/`rw`) |
| `AvecNg_two` | `STgAg` (`Chain/Step2Gen:836`) | `rfl` (`STgAg` unfolds to `STLKMg …`) |
| `StoppedDuhamelNg`, `stoppedDuhamelNg(_at)` | band `StoppedDuhamelN` (`:293`) | route (7a): T5 at `bandStep2Mat sz E` + `bandStep2_*` + band T3; proved |
| `StoppedAzumaNg`, `stoppedAzumaNg(_at)` | band `StoppedAzumaN` (`:531`) | route (7a): T6 at `bandStep2Mat` + `bandStep2_Ugen`/`_martIncN` rewrite under the binders; proved |

### (v) Privates
- Reused by `open private … from RBM3D.Induction.GridDuhamelN` (precedent `Graph/BASymm2:22`): `GridDuhamelN_gridTime_nonneg` (`:249`), `GridDuhamelN_gridTime_lt_one` (`:256`), `GridDuhamelN_azuma_step` (`:447`; model-free: `X : ℕ → Ω' → ℂ`, `ℱ`, `μ`).
- Copied under the stem `GridDuhamelGen_` (they mention `AvecN`/`martIncN`/`Ugen`/`pathP`): `_measurable_AvecNg` (from `:395`), `_stronglyMeasurable_martIncNg` (`:402`), `_stronglyMeasurable_UN_apply` (`:414`, `Ugen` ↦ `Step2Gen_UN`; continuity of a finite sum).
- Not needed: `_uKer_eq` (`:70`; `Step2Gen_uKer` is used directly), `_norm_slot_lt_one` (the slot condition is T3), `_prependZero`, `_sum_range_succ_prependZero` (inside `azuma_step`), `_gridStep_nonneg`, `_gridTime_mono`.

### (vi) Size, cone, imports
- Predicted lines (from band blocks): algebra `:55-200` 145 → ~130; vocabulary `:239-345` 105 → ~120; measurability `:380-430` 50 → ~45; G3 `:524-610` 85 → ~80; `bandStep2_*` bridges and band route (7a) ~120; instances `:614-778` 165 → ~150; header/docs ~40. Total ~690 against stop line 2,000 (estimate 450/650/1,000).
- Cone and imports (script over `import` lines of every `RBM3D/**/*.lean` on the worktree, which is `main` 4d4091e):
```
transitive imports of {Chain.Step2Gen, Induction.GridDuhamelN}: 76 modules; BA/* among them: []
modules importing RBM3D.Chain.GridDuhamelGen: [] ; file exists: False
```
- Name scan of the ticket's 20 new names + `GridDuhamelGen` on `main`, `t/T2450`, `t/T2451`, `t/T2449`, `t/T2452` (t/T2454 does not exist): 0 hits in each (`git grep`, empty output).
- `docs/reports/T2452-prove.md` exists but is uncommitted (not on `main`); nothing read from it. T2452 lines for T4s1: none cited.

### Verdict
- T1 (kernel algebra over the carrier): PASS
- T2 (`Ugen = Step2Gen_UN`, no third kernel): PASS (bridge is a proved one-line rewrite, not `rfl`; the check's `Iff.rfl` shape holds because `Ugen` unfolds to `UN`)
- T3 (`Step2Gen_USemigroup` + band theorem): PASS (window `[0,1)` is tight at 1; band theorem needs `3 ≤ sz.L n`, available as `sz.three_le_L n`)
- T4 (vocabulary and bridges): PASS
- T5 (G1 over the carrier): PASS
- T6 (G3 over the carrier): PASS, with premise (d) an external hypothesis whose concrete nonzero discharge is T4s2's; no limit computation is available here (see (ii))
- T7-T9: PASS (statement-level; instances above; `GridDuhamelN` untouched, cone of the new file is empty)

## (b) Script output — Mon Oct 12 12:59:48 UTC 2026

Branch t/T2453 at e54487c, based on main 4d4091e. Layout: one new file, additive, `GridDuhamelN` not edited; the lane is not entered.
```
$ wc -l RBM3D/Chain/GridDuhamelGen.lean   (stop line 2,000)
     683 RBM3D/Chain/GridDuhamelGen.lean
$ git diff --stat main...t/T2453
 RBM3D/Chain/GridDuhamelGen.lean | 683 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 683 insertions(+)
$ git diff main...t/T2453 -- RBM3D/Induction RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/Carrier.lean | wc -l
       0
$ grep -n '^import' RBM3D/Chain/GridDuhamelGen.lean
6:import RBM3D.Chain.Step2Gen
7:import RBM3D.Induction.GridDuhamelN
$ git grep -n 'Chain.GridDuhamelGen' t/T2453 -- RBM3D RBM3D.lean | grep -v '^t/T2453:RBM3D/Chain/GridDuhamelGen.lean'   # cone
(empty: cone empty, 0 modules)
$ lake build RBM3D.Chain.GridDuhamelGen 2>&1 | tail -1
Build completed successfully (3760 jobs).
$ lake env lean docs/tickets/checks/T2453-check.lean >/dev/null 2>&1; echo exit=$?
exit=0
$ grep -nE 'sorry|admit|^axiom|native_decide' RBM3D/Chain/GridDuhamelGen.lean
(no match, grep exit=1)
$ python3 -I cmp.py   # def bodies vs docs/tickets/checks/T2453-check.lean, names T2453_X -> X
Step2Gen_USemigroup identical
StoppedDuhamelNg identical modulo the binders {d} {sz} (file: section variables)
StoppedAzumaNg identical modulo the binders {d} {sz} (file: section variables)
$ lake env lean AuditT2453.lean   # scratchpad file: check Part 2 defs T2453_* + examples applying the file's theorems to them; exit 0
  example : T2453_UNTelescope := Step2Gen_UN_duhamel_telescope ; T2453_USemigroup ↔ Step2Gen_USemigroup := Iff.rfl ;
  band shape |E n| ≤ 2 → T2453_USemigroup (bandFM sz E) n := step2Gen_USemigroup_band ; T2453_StoppedDuhamelNg := stoppedDuhamelNg (+ ↔ Iff.rfl) ;
  T2453_StoppedAzumaNg := stoppedAzumaNg (+ ↔ Iff.rfl) ; Ugen shape of target 2 := Iff.rfl ; target 4 (STgAg) := AvecNg_two ; check-file route (7a) G1 shape := proof via bridges
$ #print axioms of the 16 public theorems/defs (same run): count by axiom list
16
0
(first number: lines with exactly the standard three; second: other lines, 0 = no error, no other axiom)
$ premise scan: 'import RBM3D.Test.Axioms; import RBM3D.Chain.GridDuhamelGen; #assert_rbm_axioms'
0
(0 = none of this file's pins is in the unproved-premise list; the list has 26 STxxx names of modules this partial import does not load; full run at merge)
$ new public declarations and examples (grep)
51:def Step2Gen_USemigroup {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
58:theorem step2Gen_USemigroup_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| ≤ 2) :
74:theorem Step2Gen_UN_add (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
82:theorem Step2Gen_UN_self (C : FlowFM sz) (n : ℕ) (h : Step2Gen_USemigroup C n) {k : ℕ}
99:theorem Step2Gen_UN_comp (C : FlowFM sz) (n : ℕ) (h : Step2Gen_USemigroup C n) {k : ℕ}
132:def Step2Gen_UNHom (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) :
143:theorem Step2Gen_UN_duhamel_telescope (C : FlowFM sz) (n : ℕ) (hS : Step2Gen_USemigroup C n) {k : ℕ}
181:theorem bandStep2_Ugen {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
193:def AvecNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
198:def martIncNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
204:def predIncNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
211:theorem AvecNg_two (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (σ : Fin 2 → Bool) (ω : PathΩ sz)
220:theorem bandStep2_AvecN {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
223:theorem bandStep2_martIncN {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
226:theorem bandStep2_predIncN {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ sz) :
243:def StoppedDuhamelNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
261:theorem stoppedDuhamelNg_at (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
284:theorem stoppedDuhamelNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedDuhamelNg Cm s t K :=
336:def StoppedAzumaNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]
365:theorem stoppedAzumaNg_at (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]
409:theorem stoppedAzumaNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] (s t : ℕ → ℝ) (K : ℕ → ℕ) :
examples: 16
522:example : Step2Gen_USemigroup (bandFM sz0 GridDuhamelGen_instE) 0 :=
526:example (A : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
608:example : StoppedDuhamelNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
614:example (a : Fin 3 → Zd 3 (sz0.L 0)) (c : ℕ → ℝ≥0)
649:example (a : Fin 3 → Zd 3 (sz0.L 0)) (x : ℝ) (hx : 0 ≤ x) :
675:example : StoppedAzumaNg (bandStep2Mat sz0 GridDuhamelGen_instE) GridDuhamelGen_instS
$ name clash: the 22 new public names (+ GridDuhamelGen) on main, t/T2450, t/T2451, t/T2449, t/T2452: total hits
hits=0
$ target-8 grep: awk NR 66..420 (generic declarations) for mE|mSigma|zt|etaT|SB|cycProd|sz.lam|"|E "
180: docstring of bandStep2_Ugen ("mSigma" in the quoted definition of Ugen)
183: the statement of the band bridge bandStep2_Ugen (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) ...)
(other hits outside that range: step2Gen_USemigroup_band l.58-65, the band-only measurability helper l.428, band corollary examples)
```

Narrative (facts from the files and logs above):
- Layout: new file `RBM3D/Chain/GridDuhamelGen.lean` (683 lines, stop line 2,000), imports `Chain.Step2Gen`, `Induction.GridDuhamelN`; no `BA/*`; cone empty; no U-row file, `GridDuhamelN`, `Step2Gen`, `Step2Kern`, `Carrier` touched (diff 0 lines). `RBM3D.lean` not edited by this stage (root imports are the hub's, CLAUDE.md §1/§3 (A)); the full `lake build` and `import RBM3D` + `#assert_rbm_axioms` are the hub's merge step.
- One kernel (U-C4): no kernel definition and no `abbrev` added; `Ugen` is read through `bandStep2_Ugen`, proved as `(Step2Kern_UN_band …).symm`; the check's `Ugen = UN` side is `Iff.rfl`, the equality with `Step2Gen_UN` is the proved bridge (as 1a (iv)).
- Targets: 1 `Step2Gen_UN_add/_self/_comp`, `Step2Gen_UNHom(_apply)`, `Step2Gen_UN_duhamel_telescope`; 2 `bandStep2_Ugen`; 3 `Step2Gen_USemigroup`, `step2Gen_USemigroup_band`; 4 `AvecNg`, `martIncNg`, `predIncNg`, `AvecNg_two`, `bandStep2_AvecN/_martIncN` (both `rfl`), `bandStep2_predIncN` (proved); 5 `StoppedDuhamelNg`, `stoppedDuhamelNg_at`, `stoppedDuhamelNg`; 6 `StoppedAzumaNg`, `stoppedAzumaNg_at`, `stoppedAzumaNg`; 7 `example`s (file l.416-482 band corollaries, l.484-683 instances).
- `Step2Gen_USemigroup` and `StoppedDuhamelNg`/`StoppedAzumaNg` equal `T2453_USemigroup`/`T2453_StoppedDuhamelNg`/`T2453_StoppedAzumaNg` (script above). The hypothesis lists of `_at` theorems follow the ticket (premises at `n` only; G3 has no window premises).
- Privates: reused by `open private` (it worked): `GridDuhamelN_gridTime_nonneg`, `_gridTime_lt_one`, `_azuma_step`. Copied under `GridDuhamelGen_`: `_stronglyMeasurable_martIncNg`, `_stronglyMeasurable_UN_apply`; plus new private `GridDuhamelGen_band_measurable`, the private instance `GridDuhamelGen_bandPp_isProbabilityMeasure` (so `IsProbabilityMeasure (bandStep2Mat sz E).Pp` is found syntactically) and the instance data `GridDuhamelGen_inst*`.
- Instances: every example at `sz0`, `n = 0`, `E ≡ 0`, `σ = (+,+,-)`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`; `stoppedDuhamelNg_at` at `τ ≡ 3`, `j = 4` fully discharged (T3 by `step2Gen_USemigroup_band`); `stoppedAzumaNg_at` at `τ ≡ 3`, `m = 2` keeps the conditional sub-Gaussian input `hsubG` as a hypothesis (input (d), producer `azumaSubGN` of T4s2; as 1a (ii)); its measurability premise is discharged by `walk_measurable_loopFine` ∘ `pathH_measurable_filt`; `τ ≡ 0`, `c ≡ 0` discharges `hsubG` too. The `∀ n` pins `stoppedDuhamelNg`, `stoppedAzumaNg` are also used at `bandStep2Mat sz0 (fun _ => 0)`.
- Band corollaries (target 7 (a)): the merged `stoppedDuhamelN_at`, `StoppedDuhamelN` (from `StoppedDuhamelNg`), `stoppedAzumaN_at` are re-derived as `example`s through the bridges. The BA readings (target 3 at `baFM`, measurability at `baStep2Mat`) are not in the file (T4-BA).
- Ported: the proofs are adapted from `RBM3D/Induction/GridDuhamelN.lean` (same project, commit 4d4091e, lines 82-166, 272-335, 395-421, 447-601, 614-778).

## (c) Verified Mathlib / merged names used
- `Finset.sum_add_distrib`, `Finset.sum_eq_single`, `Fintype.prod_boole`, `Fintype.prod_sum`, `Finset.prod_mul_distrib`, `Finset.sum_comm`, `AddMonoidHom.mk'`, `continuous_finsetSum`, `stronglyMeasurable_condExp`, `measurable_pi_iff`: all compile in the build above.
- Merged project names: `Step2Kern_uKer_band`, `Step2Kern_UN_band`, `ukerMat_self`, `ukerMat_mul`, `norm_mul_mSigma_lt_one`, `Sizes.three_le_L`, `duhamel_telescope`, `sum_stopped`, `azuma_complex` (inside `GridDuhamelN_azuma_step`), `walk_measurable_loopFine`, `pathH_measurable_filt`, `isProbabilityMeasure_pathP`, `HasCondSubgaussianMGF.fun_zero`, `STgAg`, `STLKMg`, `bandStep2Mat`, `bandFM`, `Step2Gen_UN`, `Step2Gen_uKer`.
- Verified absent: none needed.

## (d) Open issues and paper-delta candidates
- T2453a (statement shape): `Step2Gen_USemigroup` (target 3) replaces `3 ≤ L`, `|E| ≤ 2` in the generic statements; at the band it is `step2Gen_USemigroup_band` (needs `|E n| ≤ 2`), at BA it is owed by T4-BA (`BAuKer_self/_comp` via `Step2Kern_uKer_BA`).
- T2453b: the generic G3 pin `StoppedAzumaNg` has the measurability premise (`hmeas`) and no window premises; the band `StoppedAzumaN` has five window premises, unused (`GridDuhamelN:553`). Band route: `GridDuhamelGen_band_measurable`.
- Open: `RBM3D.lean` import line (hub). Full `lake build` not run by this stage. The T2452 report is not on `main`; nothing cited from it.
