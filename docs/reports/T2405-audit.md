Auditor model: claude-opus-5-5

# T2405 audit, round 1 (Sun Oct 11 04:20:56 UTC 2026)
Branch `t/T2405` at 50818fe; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2405-audit1` (detached). Binding inputs: ticket
`docs/tickets/T2405.md` and Amend 1 (`T2405-amend-1.md`, D1 primed pins with premise `κ ≤ Im m`, `δ₀ = κ/2`; D1′ unprimed pins
as corollaries; layout (A); no BA proof; registry none unless the pre-check asks). Scratch: `scratchpad/T2405/`.

## 1. Diff, layout, size
```
$ git diff --name-status main...t/T2405
A	RBM3D/Chain/NewKLKGen.lean
$ wc -l < RBM3D/Chain/NewKLKGen.lean          # stop line 900
     816
$ grep -rln "Chain.NewKLKGen" RBM3D RBM3D.lean; echo $?     # importers of the new file
1
$ git grep -F -c <name> main -- RBM3D RBM3D.lean | wc -l   # clash check on current main
STNewKLKAtgL':0 STNewKLKgL':0 NewKLKGenHyp:0 stNewKLKAtgL'_of:0 stNewKLKgL'_of:0 stNewKLKAtgL_of_primed:0 stNewKLKgL_of_primed:0 newKLKGenHyp_band:0
```
Only the layout-(A) sole writable file is touched; `NewKLK.lean`, `Step2K2.lean`, `Step2Gen.lean` untouched (G1 by construction).
`RBM3D.lean` import line is left to the hub (§3 (A) 4). Imports: `Induction.NewKLK`, `Chain.Step2Gen`, `BA.FlowPins` (no cycle:
zero importers).

## 2. Statements
### 2.1 Primed pins against the merged pins (Amend 1 D1)
```
$ ext Step2Gen.lean STNewKLKAtgL > p1; ext NewKLKGen.lean "STNewKLKAtgL'" | sed "s/STNewKLKAtgL'/STNewKLKAtgL/" > n1; diff p1 n1
2c2
<   ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
---
>   ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
$ ext Step2Gen.lean STNewKLKgL > p2; ext NewKLKGen.lean "STNewKLKgL'" | sed "s/'//g" > n2; diff p2 n2 && echo identical
STNewKLKgL' identical modulo prime
```
(`ext` = awk extraction of the `def` block, 12 and 2 lines each.) Exactly the one premise swap of D1; all other quantifiers,
losses `C/(1-u)`, `Ĵ + Ĵ²·1_{ℓ≥1}`, `STprof`, `σ, a` ranges unchanged.

### 2.2 Targets (signatures, `RBM3D/Chain/NewKLKGen.lean`)
- `stNewKLKAtgL'_of (hd : 3 ≤ d) (κ 𝔡) (hκ : 0 < κ) (mk) (hyp : NewKLKGenHyp d κ 𝔡 mk) : ∃ C, 0 < C ∧ STNewKLKAtgL' d κ 𝔡 C (κ/2) mk`
  (:412). Shape of the band `nkl_at` (`NewKLK.lean:993-994`: `∃ C, 0 < C ∧ STNewKLKAt d κ 𝔡 C (κ / 2)`); `δ₀ = κ/2` as D1.
  Constant in the proof: `refine ⟨2 * K_c + 2 * Cs * (4 + C_K) + Cs * CT, …⟩` with `Cs = 2^(d-2) e`, `CT` of `ekPropTInf_holds d hd`.
- `stNewKLKgL'_of (mk) (h : 3 ≤ d → ∀ κ 𝔡, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) : STNewKLKgL' d mk` (:624): quantified as the pin.
- D1′ corollaries: `stNewKLKAtgL_of_primed (h : STNewKLKAtgL' d (κ/2) 𝔡 C δ₀ mk) (hdom : … |E| ≤ 2-κ → κ/2 ≤ Im m) :
  STNewKLKAtgL d κ 𝔡 C δ₀ mk` (:634) and `stNewKLKgL_of_primed (h : STNewKLKgL' d mk) (hdom : ∀ κ 𝔡 > 0, …) : STNewKLKgL d mk`
  (:644), applying the primed pin at `κ' = κ/2` (so `δ₀ = κ/4`, allowed by `∃ C δ₀`). Matches D1′ verbatim.
- `stNewKLKAtgL'_holds` (:617): `.choose_spec` form of target 1 (shape of `stNewKLKAt_holds`, `NewKLK.lean:1321`).

### 2.3 Hypothesis bundle `NewKLKGenHyp d κ 𝔡 mk` (:378; a transparent `Prop` def, not a structure field)
`∃ K_c C_K ≥ 0` and, on the primed domain `0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m` (and `0 ≤ u < 1`):
F5 support/row-sum/symmetry of `mk.S`; F6 `‖mk.m n‖ ≤ 1`; F7 `Σ_b ‖(S·Step2Gen_Theta S (u m_{σ0} m_{σ1}))_{ab}‖·tailW(|b-a'|)
≤ K_c/(1-u)·tailW(|a-a'|)` for all `ℓ', D' ≥ 0`; F8 both marginals `Σ‖mk.K n u σ ![·,·]‖ ≤ C_K W^{-d}(1-u)⁻¹`; F9 `∃ ζ, Im ζ =
(1-u) Im m`, `mk.LM = loopFine … ζ`, diagonal `mk.GMM = Gres H ζ true x x - m`.
C1 check (ticket target 3): every clause is read through `mk` fields (`S`, `m`, `K`, `LM`, `GMM`, `STmsigg`); no `‖m‖ = 1`,
scalar `mE`, `mSigma`, `M = m I`, band `Theta`, `SB`. The only `sz.lam` occurrence is the `tailW` coupling of F7, which is the
profile of the frozen pin's `STprof` (`Step2Defs.lean:75-77`: `tailW d (sz.L n) (sz.lam n) …`); see observation O1.
Non-vacuity: `newKLKGenHyp_band` (:664) proves the bundle at `fun sz E => bandStep2Mat sz E` for every `κ, 𝔡 > 0`, `3 ≤ d`.
External limit check (TEAM §8 l.14): prove report (a) script (b-b), BA `S = 1` data at `u ∈ {1/32, …, 0.9999}`: `C_K = 1`,
`K_c ≤ 1` (rows 6-8), and (a′) C2 `max (1-u)/|1-ξ| = 0.99999`. BA sources/owing rows: (a′) C4 (F6 `baPropM_holds` merged; F5,
F7, F8 product bound, F9 BA `Step2Mat` owed to T3-BA). Consistent with Amend 1 ("no BA proof here").

Dependencies: `ekPropTInf_holds`, `prop5Decay_holds`, `Ind.half_le_mE_im`, 18 opened privates of `Induction/NewKLK.lean`
(listed in the header, :46-49), all merged. No circularity (§1).

## 3. Build, axioms, checks (audit worktree)
```
$ lake build RBM3D.Chain.NewKLKGen 2>&1 | grep -E "error|NewKLKGen|Build completed"
✔ [3744/3744] Built RBM3D.Chain.NewKLKGen (12s)
Build completed successfully (3744 jobs).
(warnings: only longLine / unused-hypothesis linters in upstream merged files; none in NewKLKGen.lean)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Chain/NewKLKGen.lean; echo $?
1
$ lake env lean scratchpad/T2405/audit.lean   # G1 + #print axioms + premise-swap example
stNewKLKAt_holds : ∀ (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡), STNewKLKAt d κ 𝔡 ⋯.choose ⋯.choose
'RBM.BA.STNewKLKAtgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STNewKLKgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.NewKLKGenHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKAtgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKAtgL'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKAtgL_of_primed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKgL_of_primed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.newKLKGenHyp_band' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ lake env lean docs/tickets/checks/T2405-check.lean; echo $?; grep -c error
0
0
$ lake env lean scratchpad/T2405/precheck.lean   # import RBM3D; import RBM3D.Chain.NewKLKGen; #assert_rbm_axioms
axiom audit: 11364 theorems, 3424 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit 0
```
`audit.lean` contains `example (d) : STNewKLK d := stNewKLK_holds d`, `example (d) : STK2decay d := stK2decay_holds d`,
`#check @stNewKLKAt_holds` (G1, ticket item 5), and an `example` deriving `STNewKLKAtgL` from `STNewKLKAtgL'` plus
`|E| ≤ 2-κ → κ ≤ Im m` by direct application (confirms the single-premise relation).

## 4. Compiled nonempty instances (same file, `section Inst`, :740-814; built in §3)
| endpoint | instance | data / discharge |
|---|---|---|
| `stNewKLKgL'_of` (target 2) | `example : STNewKLKgL' 3 band` (:746) | hypothesis by `newKLKGenHyp_band` (all κ, 𝔡) |
| `stNewKLKAtgL'_of` (target 1) | :750 at `d=3, κ=𝔡=1/10, δ₀=1/20`; pointwise :775 | `sz0` (`L=4, W=32, lam=1/64`), `n=0`, `E=0` (`Im mE 0 = 1 ≥ 1/10` by `nkl_mE_zero`), `u=1/32`, `D=1`, `ℓ=2 ≤ 4` (indicator on), `H=0` Hermitian, `‖GMM‖ ≤ u/(1-u)=1/31 ≤ 1/20` (`nkl_STGMM_zero`); every premise discharged |
| `stNewKLKgL_of_primed` (+ `stNewKLKAtgL_of_primed` inside) | `example (d) : STNewKLK d` (:760) via `bandStep2_STNewKLK` | `hdom` by `Ind.half_le_mE_im` (target 6 band re-derivation) |
| target 1 at BA (statement level, ticket item 6) | :810, family `NewKLKGen_baMk` over `baFM sz sz.lam E` | `NewKLKGenHyp` left open (owed to T3-BA, as ticket item 6 and Amend 1 allow) |
No `N = 0`, empty index, collapsed window or `False` premise: `L = 4`, `W = 32`, `0 < u < 1`, `0 < ℓ`, `κ ≤ Im m` satisfied with
slack 9/10.

## 5. Paper deltas
Prove report (d) proposes: T2405a (`S = 1` at BA: `STthetaOpg` is the diagonal operator, not `BATheta`), T2405b (primed premise
`κ ≤ Im m` for `|E| ≤ 2-κ`, `lem:newKLK` `3_5:371-378`), T2405c (generic theorems are conditional adapters, BA facts owed),
T2405d (unprimed route gives `δ₀ = κ/4` vs merged `κ/2`). These cover every Lean/paper difference found in §2.

## 6. Observations (no statement/instance/build/axiom/delta effect)
- O1 (for the dispatcher / T3-BA): F7 and the frozen `STprof` profile use the coupling `sz.lam n`, and the pin requires
  `0 < sz.lam n`; whether the BA chain's `sz` carries the coupling or reads the law at `sz.withLam 0` (`BA/ConArg.lean:62`) is a
  property of the merged T2386 pin, inherited unchanged here (D1 changes only the energy premise). To be settled in the BA-T pin REQ.
- O2 (registry): `stNewKLKAtgL'_holds` and `newKLKGenHyp_band` are what make the pre-check classify `STNewKLKAtgL'`,
  `NewKLKGenHyp`; at BA these remain owed. Prove report (d) asks the dispatcher whether to register them in `owedProps`.
- O3: `stNewKLKAtgL_of_primed` and `stNewKLKAtgL'_holds` have no example of their own; the first is applied through
  `stNewKLKgL_of_primed` in the `STNewKLK d` example, the second is `choose_spec` of target 1 (whose instances compile).
- O4: Layout (A) was chosen by Amend 1 D1 although the 1a rule computed (B) (285 > 150); actual 816 ≤ 900.
- O5: `∃ C` follows `mk`, as in `nkl_at` and the pin's `∃ C δ₀`; the explicit formula is in the proof term (§2.2).

## 7. Verdict
- `STNewKLKAtgL'`, `STNewKLKgL'` (pins of Amend 1 D1): **PASS** (script diff §2.1).
- Target 1 `stNewKLKAtgL'_of` (with `stNewKLKAtgL'_holds`): **PASS**.
- Target 2 `stNewKLKgL'_of`: **PASS**.
- D1′ corollaries `stNewKLKAtgL_of_primed`, `stNewKLKgL_of_primed`: **PASS**.
- Target 3 (C1, hypotheses through `mk`; band discharge `newKLKGenHyp_band`): **PASS** (O1 noted).
- Targets 4-6 (Step2K2 untouched, G1 examples, instances): **PASS**. Target 7 (pre-check): passes.
Overall: **PASS**. No dispatcher sign-off required for the merge.
