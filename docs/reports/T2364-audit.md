Auditor model: claude-opus-5-5

# T2364 audit (round 1) — LW-13b R3 = G + F, `lem:LW_moment_exp`; Amend 1 (C6 = form (β))
Written Sat Oct 10 06:08:33 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2364-audit1`, detached at `t/T2364` = 0b74a90; merge base 010cad9; main c0a7747. Scratch scripts in scratchpad `T2364/`.

## 1. Scope (sole writable files)
```
$ git diff --stat main...t/T2364
 RBM3D/Graph/AuxGraphRooted.lean |  569 +++++++++++++++
 RBM3D/Graph/LWMomentExp.lean    | 1509 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |    1 -
$ git diff main...t/T2364 -- RBM3D/Test/Axioms.lean | grep '^[-+][^-+]'
-   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-13b
$ git diff 010cad9 main --stat -- RBM3D/Graph/      # merged inputs unchanged since the base
(empty)
$ for m in LWProv LWMomentExpA LWMomExpInf LWXiExp LWMomExpFar AuxGraph LWMoment LWMomExpD; git log -1 --format=%h main -- RBM3D/Graph/$m.lean
LWProv: c587dcd  LWMomentExpA: eb56169  LWMomExpInf: eb56169  LWXiExp: eb56169  LWMomExpFar: fbec579  AuxGraph: 87cf70c  LWMoment: 1546ef7  LWMomExpD: d71c955
```
Three files = the ticket's sole writable files; every import is a merged module (`LWMomExpD` is an extra import of a merged module, allowed by "only what a lemma needs"). Size 2078 < stop line 2100. No frozen signature touched.

## 2. Statements against the pins (script diff, probe `t/T2348:RBM3D/Probe/T2348Pins.lean`)
`extract.py` cuts each declaration block from both files (for theorems, the text before `:= by`) and runs `difflib.unified_diff`.
```
$ python3 -I extract.py probe.lean AuxGraphRooted.lean auxValOn LWGtoAGRooted LWAuxNestedOwnOn
auxValOn IDENTICAL
LWGtoAGRooted IDENTICAL
LWAuxNestedOwnOn IDENTICAL
$ python3 -I extract.py probe.lean LWMomentExp.lean domFar domNearA domNearB domFar_eq dom_union dom_disj LWf_split \
    norm_add3_pow_le LWMomentExpOn regA LWMomExpFarPin LWMomExpNearPin LWMomentExpOfParts
domFar IDENTICAL / domNearA IDENTICAL / domNearB IDENTICAL / domFar_eq IDENTICAL / dom_union IDENTICAL / dom_disj IDENTICAL
LWf_split IDENTICAL / norm_add3_pow_le IDENTICAL / LWMomentExpOn IDENTICAL / LWMomExpFarPin IDENTICAL / LWMomExpNearPin IDENTICAL
regA MISSING True False
LWMomentExpOfParts DIFF
   -  ∀ K : ℝ, LWMomExpNoExp d K → LWMomExpFarPin d K → LWMomExpNearPin d K → LWMomentExp d
   +  ∀ K : ℝ, 0 < K → LWMomExpNoExpF d K → LWMomExpFarPin d K → LWMomExpNearPin d K → RBM.Gauss.Sizes.LWMomentExp d
$ python3 -I extract.py probe.lean RBM3D/Graph/LWMomentExpA.lean regA
regA IDENTICAL
```
- `regA` is not redefined: the merged one (`LWMomentExpA.lean:49`) is the probe's verbatim.
- `LWMomentExpOfParts`: (A) is the merged `LWMomExpNoExpF` (ticket §162 (2): "(A) is merged in the form `LWMomExpNoExpF`"), and `0 < K →` is the (β) form of Amend 1 ("Keep `∀ K > 0`"). Both are required by the ticket. `LWMomExpNoExpF` (`LWMomentExpA.lean:56`) is `LWMomentExp` with the subtype restricted by `regA d K` and the same `LWf`, bound and floor.
- Endpoint target, unchanged pin `LWPins.lean:341` (not in the diff):
```
RBM3D/Graph/LWMomentExp.lean:1436:theorem lwMomentExp_holds : ∀ d : ℕ, LWMomentExp d := fun d =>
  RBM.Graph.lwMomentExp_of_parts d 1 one_pos (RBM.Graph.lwMomExpNoExp_holds d 1 one_pos) (RBM.Graph.lwMomentExp_farPin_holds d one_pos) ...
RBM3D/Graph/AuxGraphRooted.lean:244:theorem lwGtoAGRooted_holds (d : ℕ) : LWGtoAGRooted d := by
RBM3D/Graph/AuxGraphRooted.lean:457:theorem lwAuxNestedOwnOn_holds : LWAuxNestedOwnOn := by
RBM3D/Graph/LWMomentExp.lean:179:theorem lwMomentExp_of_parts (d : ℕ) : LWMomentExpOfParts d := by
RBM3D/Graph/LWMomentExp.lean:1422:theorem lwMomentExp_farPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : LWMomExpFarPin d K :=
RBM3D/Graph/LWMomentExp.lean:1426:theorem lwMomentExp_nearPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : LWMomExpNearPin d K :=
RBM3D/Graph/LWMomentExp.lean:1302:theorem lwMomentExp_pin_gen {d : ℕ} {K : ℝ} (hK : 0 < K) (dom : ...)
    (hPin : 3 ≤ d → ∀ {p q : ℕ}, 0 < p → ∀ Γ : NGraph p q, Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → lwMomentExp_PinN d Γ dom) :
    LWMomentExpOn d dom (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q)
```
The far pin and the near pins are proved for every `K > 0` (probe statements verbatim, Amend 1); `hPin` is discharged inside both pins by `lwMomExpFar_and` / `lwMomExp_nearInf`, so neither public pin has an extra hypothesis.

## 3. Amend 1 checks (C6 = (β)), C5, L1
```
$ git diff main...t/T2364 | grep -E '^\+.*∃ ?K\b|^\+.*∃ \(K'      # any ∃ K in the added text
(no match, exit 1)
$ awk: public theorem/def statements (text up to ':=') containing ∃
AuxGraphRooted.lean: lwAuxRoot_exists_forest   (∃ par edge ρ: the forest, rep given)
AuxGraphRooted.lean: lwAuxRoot_exists_rep      (∃ rep)
LWMomentExp.lean:   lwMomentExp_assm           (∃ ε₁ > 0, a window; not a scale K)
$ grep -n "Krad\|K / Kc\|lw_localregularXP\|lwTail32" LWMomentExp.lean   (excerpt)
1031: private theorem lwMomentExp_prec_anp ... {K Kc D : ℝ} ... radius `R = K (log W)^{3/2}`, `r = (K/Kc) (log W)^{3/2}`
1083:   lwTail32 sz h𝔠 (mul_pos hc (div_pos hK hKc)) hsz hband ...
1325: obtain ⟨outs, errs, hcovx, Hm⟩ := lw_localregularXP p (ε₁ / 2) (half_pos hε₁) K0 d ((D + 1) / 𝔠)
1326: set Kn : ℕ := ((outs ++ errs).map fun o => Fintype.card (o.Q.E' ⊕ o.Q.I')).sum
1327: set Kc : ℝ := (Kn : ℝ) + 1
1357: ... lwMomentExp_prec_scale H hd0 hD (Krad := K / Kc) (div_pos hK hKc0) ...
$ grep -n lwProv_locStepXProvPos_holds RBM3D/Graph/{AuxGraphRooted,LWMomentExp}.lean
(no match)
```
- No public `∃ K`. `lwMomentExp_PinN` (a `def`) has `∃ C, 0 < C ∧ …`, a constant of the normalized pin, not the scale `K`.
- Far radius in the 5b form: `K_card = Kc` is taken after `(p, ε₁, K0 = ⌈1/𝔠⌉, D)` from the engine lists; tail radius `r = (K/Kc)(log W)^{3/2}`, tail constant `c·K/Kc` in `lwTail32`, `R = K (log W)^{3/2}`.
- C5: `lwAuxRoot_exists_forest` takes `rep` and `hrep : ∀ c, Γ.molOf (inr (rep c)) = c.1` as hypotheses; route (R), no (E). `LWGtoAGRooted` has the same `rep`/`hrep` binders as the probe.
- L1 / §167: the engine is used only as `lw_localregularXP : LWEngineProv` (`LWProv.lean:1680`, a theorem).

## 4. Vacuity, hidden hypotheses, cycles
- Public statements are `def … : Prop` copied from the probe, plus theorems whose hypotheses are in their signatures. The only structure added, `lwMomentExp_Ctx`, is `private` and used only inside proofs. It bundles `LWMomentCtx` and `LWAssmExp`, both derived inside `lwMomentExp_pin_gen` from its binders.
- No cycle: the four `#print axioms` dependencies below close without any hypothesis, and `lwMomentExp_holds` applies only proved theorems (`lwMomExpNoExp_holds`, both pins, the assembly).
- There is no new external hypothesis. `LWInit` and `LWLoopExp` stay hypotheses only in the examples; they are owed premises (`Test/Axioms.lean:159,161`), so they are other gates' pins.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.AuxGraphRooted RBM3D.Graph.LWMomentExp RBM3D.Test.Axioms
✔ [3856/3905] Built RBM3D.Test.Axioms (4.2s)
⚠ [3905/3905] Built RBM3D.Graph.LWMomentExp (231s)
Build completed successfully (3905 jobs).
exit 0
errors: 0; warnings in the two new files: 27 (style linters)
$ git diff main...t/T2364 | grep -nE '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom '
(no match, exit 1)
$ lake env lean ax.lean
'RBM.Graph.lwGtoAGRooted_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAuxNestedOwnOn_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_farPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_nearPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwMomentExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWf_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.dom_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.dom_disj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.domFar_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.norm_add3_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_inst_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
#eval RBM.Audit.owedProps.contains `RBM.Gauss.Sizes.LWMomentExp
false
```
The full-library `lake build` and the `#assert_rbm_axioms` pre-check were not rerun here; the hub runs them at merge. The prove report's b1 pastes both: exit 0, 4179 jobs, 0 axioms, and 0 occurrences of `LWMomentExp`.

## 6. Compiled nonempty instances (compiled by the module build of §5)
- **`LWGtoAGRooted`** (`AuxGraphRooted.lean:509`). It applies `lwGtoAGRooted_holds 3` at `figGraph`, `d = 3`, `L = 4`, `W = 2`, `auxGraph_instD`, `m = mE 0`, `Ψ = 1/2`, `r = 1`, `R = 8`, `ξ ≡ 1/2`, with `C, c > 0` from `lwSpOf_decay_E` and roots from `lwAuxRoot_exists_rep`. `Dm = {0, e₀}` has card 2. The weight `Wt = 1[every root block ∈ Dm]` takes both values 1 and 0, and the restricted main term is `auxValOn … = 1/16 ≠ 0`. Every hypothesis is discharged (window `2^{-3/2} ≤ 1/2`, `card·r ≤ R`, `|Wt| ≤ 1`, support of `Wt`). Nondegenerate.
- **`LWAuxNestedOwnOn`** (`:554`). At `localReg2_inst_Q.pack`, `p = 2`, the example gives `Γa` with `NoGhost`, `IsNested`, `ownExt` and `ordN = 2`, and computes `valOn … = 1/8`. Nondegenerate.
- **Assembly** (`LWMomentExp.lean:1492`). It applies `lwMomentExp_of_parts 3 (1/100)` with the proved (A), far and near pins, at `sz0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z0`, `flow_z0`, `t ≡ 1/16`, `p = 2`, `ε₀ = 1/20`, `Ψ0`, `ℓ = ℓT tInst`, and `LWAssmExp` from `assmExp_of hI hL` (`hI : LWInit`, `hL : LWLoopExp` are owed pins).
- **`lwMomentExp_holds 3`** (`:1475`) runs at the same data. The index set `λ²/L² < 1 − t` is nonempty at every `n` (`:1478`, `strict_all n`).
- **Domains** (`:1497-1506`): `domFar`, `domNearA`, `domNearB` are nonempty at `L = 4`, `a = 0`, `b = (2,0,0)`, `ℓ = 1`; `dom_union`, `dom_disj` and `domFar_eq` hold there, and `LWf_split` holds at `sz0`.

## 7. Paper deltas (prove report (d))
- T2364a: scale `K`. The paper has `K = 1` at `7_8:1598-1600`; the pins hold `∀ K > 0`, and the target uses `K = 1`.
- T2364b: three exact domains in place of `f^{>ℓ}` / `f^{≤ℓ}` (`7_8:1606-1612`).
- T2364c: the rooted, weighted, restricted `GtoAG` in place of the full-sum `GtoAG` (`7_8:907`).

Checked against `7_8:1597-1612`. The paper's window `(log W)^{3/2}ℓ_t ≤ ℓ ≤ (log W)^{10}ℓ_t` (`eq:far_ab_K`) is a proof-internal reduction. The Lean pins hold on all of `¬ regA` without the upper bound, which is more general, and the target `LWMomentExp` (`LWPins.lean:341`) is unchanged. So every statement difference is covered.

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The far/near pin examples at `K = 1/100` (`:1481-1491`) become vacuous for large `n`. At `sz0`, `ℓ_n = ellT = 1`, because `λ_n = (2(n+1))^{-6}` gives `max(λ/√(15/16), 1) = 1`. `K(log W_n)^{3/2}` is 0.9983 at `n = 36` and 1.0076 at `n = 37` (python script). So `¬ regA` is empty for every `n ≥ 37`; it is nonempty at `n = 0` (`lwMomentExp_inst_nonempty`). The ticket does not require these examples. The required endpoint instances (`lwMomentExp_holds 3` and the assembly, whose conclusion is on the full set, nonempty at every `n`) are nondegenerate. This is a property of the merged `assmExp_of` data, which fixes `ℓ = ℓ_t`.
- O2. `hK : 0 < K` is unused in the proof of `lwMomentExp_of_parts` (prove report (d)(ii)). It is kept because Amend 1 fixes the `∀ K > 0` shape.
- O3. There are 27 style-linter warnings, and `set_option maxHeartbeats 3200000 in` has no comment (`LWMomentExp.lean:1029`).
- O4. The branch base is 010cad9. `Test/Axioms.lean` changed on main since then (c0a7747, 79dec34, 0347cb8), so the one-line deletion is applied under H23 (b) at merge.

## Verdict
| Target | Verdict |
|---|---|
| `AuxGraphRooted.lean`: `auxValOn`, `LWGtoAGRooted` + `lwGtoAGRooted_holds`, `LWAuxNestedOwnOn` + `lwAuxNestedOwnOn_holds` | PASS |
| `LWMomentExp.lean`: domains, `LWf_split`, `norm_add3_pow_le`, `LWMomentExpOn`, pins (β, `∀ K > 0`), `lwMomentExp_of_parts`, `lwMomentExp_holds : ∀ d, LWMomentExp d` | PASS |
| `Test/Axioms.lean`: owed line `LWMomentExp` deleted | PASS |

**T2364: PASS.** No dispatcher sign-off needed.
