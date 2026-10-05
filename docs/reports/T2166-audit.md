Auditor model: claude-opus-5-5

# T2166 audit (S3-10a, `RBM3D/Induction/NQGood1.lean`), round 1 — Mon Oct  5 01:18:15 UTC 2026
Branch `t/T2166` at `ff596fc`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2166-audit1` (detached). The ticket has no pinned
statement text (check file has `#check` lines of merged names only), so statements are checked against the ticket's mathematics
and the merged consumers (`GoodSetN` `GridGoodN.lean:124`, `GridAssemblyHypN` `GridAssemblyN.lean:183`, `EKSumDecayNAL` `Evolution/Pins.lean:92`).

## 1. Build, scope, hygiene, axioms
```
$ lake build RBM3D.Induction.NQGood1 | grep -E "NQGood1|^error|Build completed"; echo exit=$?
✔ [3799/3799] Built RBM3D.Induction.NQGood1 (6.6s)
Build completed successfully (3799 jobs).
exit=0            (0 lines starting with "error"; the warnings printed are in other, merged files)
$ lake env lean RBM3D/Induction/NQGood1.lean     (re-elaboration from source)
(no output; 5.6 s)
$ git diff --stat main...HEAD ; git diff --name-only main...HEAD | grep -v '^RBM3D/Induction/NQGood1.lean$' | wc -l
 RBM3D/Induction/NQGood1.lean | 1481 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1481 insertions(+)
       0
$ grep -n -E "sorry|admit|native_decide|^axiom" RBM3D/Induction/NQGood1.lean | wc -l
       0
$ (scratch ax.lean: `import RBM3D.Induction.NQGood1` + `#print axioms` of every theorem/def/abbrev of the file, 63)
$ lake env lean ax.lean; grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]"; other lines
exit=0
63
(none)
$ name clash: 63 public names, git grep of declarations on main (daa7cc1)
names=63 hits=0
```
Frozen signatures: no merged file is touched. Registry (`Test/Axioms.lean`) untouched (none expected).

## 2. Statements (per target)
### Target 1 — drift tensor and its compositions with `GoodSetN`
- `driftTensorN := Σ_{l∈Icc 3 k} STksimLKM + STelklkM + STegtM` at `(n,E,u,H,loopOf σ a)`: verbatim the inline sum of
  `GridDriftN` (`GridDriftN.lean:670-673`) and of `GoodSetN` clause (Va); new name justified (no merged def).
- `driftTensorN_norm_le_of_goodSet` (`2 ≤ k`, `M ∈ GoodSetN … u …`): `‖Dr‖ ≤ Γ(ΓΦ)(B_u^k/η_u)((k-1)+kΓΦ)` = the ticket's `dDrift`,
  no additive `W^{-D'}`. Constant check (clauses (D1)×(k-2) via `Icc 3 k`, (D2), (D3) of `GridGoodN.lean:124`):
```
drift: (k-2)(D1)+(D2)+(D3) == Gamma(Gamma Phi)((k-1)+k Gamma Phi): 2000 exact rational samples, mismatches = 0
```
- `driftTensorN_far_of_goodSet`: `ℓ_u W^{τ'} ≤ STdiamInf a → ‖Dr‖ ≤ W^{-D'}` — clause (Va), same radius as `GoodSetN`.
- `qvFormN_eq_re_UgenPairN` (`|E| ≤ 2`, `|w| < 1`): `qvFormN … M a = (UgenPairN … σ v w (STeeM n E v M σ) a).re`, `UgenPairN`
  = `𝒰_σ ⊗ 𝒰_{σ̄}` (second factor with `!σ`), i.e. the paper's `((𝒰_σ⊗𝒰_σ̄)∘(𝓔⊗𝓔))_{a,a}` (`3_5:1152ff`, martingale term).
- `qvFormN_le_of_goodSetN`: on `GoodSetN` at `u`, `w ≥ u`, `qvFormN ≤ κ₁(κ₁·Γ(ΓΛ)B_u^{2k}/η_u + W^C W^{-D'}) + W^C W^k W^{-D'}`,
  `κ₁ = W^{Cε} r^{k-1}`, `r = (g²+|1-u|)/(g²+|1-w|)`, `C = nqGood1C d k Λ_g κ'`; uses (D4) and (Vb) of `GoodSetN`. Added premise
  `D' > k+1` (route through two EK-6 applications) — candidate `T2166b`. The QV constant `qvBd` itself is S3-10b (ticket split).
- Verdict target 1: **PASS**.

### Target 2 — `hker_of_case1N`
```
EKSumDecayNAL (Pins.lean:92-103): ∃ C>0, ∀ L≥3, 0<g≤Λ, 1<W, 0<ε<1, 1<D, 4≤W^ε, 0≤s≤t≤1-g²/L², W⁻¹≤(1-t)/(1-s),
  ‖m‖=1, κ≤Im m, σ non-alt, EKFastDecay g s W ε D A → ‖UN … A‖ ≤ W^{Cε} r^{n-1}‖A‖ + W^{-D+C}
hker field (GridAssemblyN.lean:201-203): ∀ i ≤ m ≤ K, X M δ, 0≤M, 0≤δ, (∀ b, ‖X b‖≤M), Cls i δ X →
  ∀ a, ‖Ugen … (u i) (u m) X a‖ ≤ κ i m * M + εK i m * δ
```
- Lean conclusion `‖Ugen d L g E σ s t X a‖ ≤ W^{Cε} r^{k-1} M + W^C δ` has exactly the field's shape with `κ = W^{Cε} r^{k-1} ≥ 0`,
  `εK = W^C ≥ 0`; `C` is `Classical.choose` of `ekSumDecayNAL_holds d k Λ_g κ'` with `prop5Decay_holds`, `prop5Short_holds`
  (merged theorems: no external hypothesis). `C` depends on `(d,k,Λ_g,κ')` only, fixed before `L,g,W,ε,D` (order kept).
- Class premises: `δ ≤ W^{-D}`, `1 < D`, `‖X b‖ ≤ δ` off `ℓ_s W^{τ'} ≤ diam_∞` (the `GoodSetN` radius); `d W^{τ'} ≤ W^ε` converts to
  EK-6's ℓ¹ window. `δ > 0`: `D'' = -log_W δ ≥ D`; `δ = 0`: limit `D'' → ∞` (proof read, `NQGood1.lean:345-375`). `log L` power 0, no
  `ρ`: stated (ticket asked to state them). Eventual `0 < g ≤ Λ_g` is a premise, not a `Sizes` field (§45 O3 (3) respected).
- Verdict target 2: **PASS** (shape differences vs RBM2D: candidate `T2166a`).

### Target 3 — shift lemmas (d ≥ 3 scales)
- `norm_loopL_zshiftN_le`/`loopMax_zshiftN_le`/`loopFine_shiftN_le`: error `ℓ η^{-(ℓ+1)} (W^{-d})^{ℓ-1} Δ` (`loopShiftErrN`): one
  `W^{-d}` per insertion (RBM2D: `(W⁻¹)²`), as the ticket requires.
- `STXiLM_shiftN_le`, `nqGood1_STmaxLM_shiftN_le`: `Ξ̂^{(𝓛)}` shift with `B_u = Bctl` (RBM2D `scaleM`).
- `goodSetN_dec_shiftN`: hypothesis for `2 ≤ ℓ ≤ 2k+2` (RBM2D `1 ≤ ℓ`; `ℓ = 1` vacuous since `STdiamInf` of one label is 0 —
  proved, `NQGood1.lean:906-913`), conclusion the `𝓛` part only (same as RBM2D `NonAltGood:267-274`); RBM2D's `0 ≤ u` dropped.
- `norm_loopFine_crudeN`, `STmaxLKM_crudeN`, `STXiLKM_crudeN` (needs `B_u ≤ 1`, `‖𝒦‖ ≤ M_K`): 3D forms of `norm_gloop_crudeN`,
  `norm_lk_envN`, `xiLK_crudeN`.
- `etaT_inv_shiftN_le`: corrected form `η_{u'}⁻¹ ≤ η_u⁻¹(1 + 2Δη_u⁻¹)`, `2Δ ≤ η_u` (= RBM2D's corrected statement `NAG:159`).
- `norm_STeeM_shiftN_le` / `eeShiftErrN = W^d·k·L^d·loopShiftErrN(2k+2)`: `STeeM` contains `𝓛` only, as the ticket states.
- `ellT_mono` (§45 O3 (3)): `nqGood1_ellT_mono` for every real `g` (`g ≥ 0`: `ellT_mono`; `g < 0`: both sides `min 1 L`, proof
  `NQGood1.lean:812-820`); no `0 ≤ lam n` hypothesis anywhere:
```
$ grep -n "ellT_mono" NQGood1.lean   → uses only at :815 (inside nqGood1_ellT_mono, under `0 ≤ g`), :897, :1362-1363
```
- Verdict target 3: **PASS**.

## 3. Hidden hypotheses, vacuity, cycles
- No structure is introduced; all hypotheses are explicit binders. Dependencies are merged on `main` (`GoodSetN`, `qvFormN`,
  `ekSumDecayNAL_holds`, `prop5Decay_holds`, `prop5Short_holds`, `zero_mem_goodSetN_of_levels`); no pin `Prop` is a hypothesis of
  any theorem, so no external hypothesis and no limit check is needed. No cycle (the file imports only merged modules).
- D366: `zero_mem_goodSetN_inst` uses `zero_mem_goodSetN_of_levels` with `(Γ,Λ,Φ) = (4,3,1)`, `Γ²Λ = 48 ≥ 3(1+g²)^6`; no unit levels.

## 4. Compiled nonempty instances (same file, namespace `RBM.Ind.NQGood1Inst`, d = 3, `sz0`, n = 0: L = 4, W = 32, g = 1/64)
| endpoint | instance (line) | data |
|---|---|---|
| `driftTensorN_norm_le_of_goodSet` | `drift_norm_instance` (:1138) | `H_0 = 0 ∈ GoodSetN 0 (1/2) 0 3 4 3 1 (1/5) 6`, k = 3, σ = (+,-,+) |
| `driftTensorN_far_of_goodSet` | `drift_far_instance` (:1146) | `aFar`, `diam_∞ = 2 ≥ ℓ_0 W^{1/5} = 2` |
| `qvFormN_eq_re_UgenPairN` | `qvFormN_eq_re_instance` (:1265) | E = 1/2, v = 0, w = 1/128 |
| `qvFormN_le_of_goodSetN` | `qvFormN_instance` (:1224) | ε = 4/5, τ' = 1/5, D' = 6 > k+1, Λ_g = 10, κ' = 1/2 |
| `nqGood1_ugenPairN_le_of_bounds` | `ugenPairN_instance` (:1243) | `T = 𝓔⊗𝓔`, bounds from (D4), (Vb) |
| `hker_of_case1N` | `hker_instance` (:1200) | `X = 1_{diam ≤ 1}` (nonzero: `Xinst_zero`), M = 1, δ = W^{-6}, D = 6 |
| shift lemmas (11) | `loopL_shift_`, `loopMax_shift_`, `loopFine_shift_`, `STmaxLM_shift_`, `STXiLM_shift_`, `dec_shift_` (hδ discharged, D'' = 3), `loopFine_crude_`, `STmaxLKM_crude_`, `STXiLKM_crude_` (`B_0 ≤ 1` proved), `etaT_inv_shift_`, `STeeM_shift_instance` | one step `u_0 = 0 → u_1 = 1/128`, E = 1/2 |
| `nqGood1_ellT_mono` | `ellT_mono_instance` (:1359) | g = 1/64 and g = -1/64 |
All deterministic hypotheses are discharged by terms (e.g. `hker_instance` `NQGood1.lean:1200-1211`); no `N = 0`, empty index,
collapsed window or `False` premise; data are small (W = 32). `zero_mem_goodSetN_inst_grid` ties u = 0 to the merged `gridTime … 0`.

## 5. Paper-delta coverage
Lean/paper differences and their candidates in the prove report (d): `hker` coefficients/class/window premise → `T2166a`;
QV majorant route and `D' > k+1` → `T2166b`; corrected `η⁻¹` shift → `T2166c`; dec shift range and `𝓛`-only conclusion → `T2166d`;
`ellT` monotone for all `g` → `T2166e`; `Ξ̂^{(𝓛)}` shift / crude `Ξ̂^{(𝓛-𝒦)}` premises → `T2166f`; `κ' = min κ (4/5)` replacing
`|E| ≤ 2-κ`, the constant `nqGood1C`, the name `driftTensorN` → `T2166g`. No uncovered statement difference found.

## 6. Observations (no verdict effect)
- `nqGood1_qvFormN_le_of_bounds` (public, file-stem prefixed intermediate) has no instance of its own; it is applied inside
  `qvFormN_le_of_goodSetN`, whose instance compiles. It is not a ticket endpoint.
- The far hypotheses of the instances need `τ' = 1/5`, `ε = 4/5` at n = 0 (section (a′)); the preflight's `τ' = 1/2` has no far
  label vector at L = 4 — recorded by the prover, no statement effect.
- Instances use the zero matrix as the good-set member (the walk's initial state, `zero_mem_goodSetN_of_levels`); conclusions are
  not trivial (e.g. `hker_instance` with nonzero `X`; loops at `H = 0` are nonzero).

## Verdict
Target 1 PASS; target 2 PASS; target 3 PASS. **Ticket T2166: PASS.** No dispatcher sign-off needed.
