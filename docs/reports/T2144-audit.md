Auditor model: claude-opus-5-5

# T2144 audit (round 1) — Sun Oct  4 17:42:57 UTC 2026

Branch `t/T2144` at `d846287` (merge-base `ae259a6`, main `3b1c6a5`); audit worktree `RBM3D-wt/T2144-audit1` (detached at `d846287`).
The check file `docs/tickets/checks/T2144-check.lean` pins no statement text; it only has `#check` lines. Statements are therefore checked against the ticket's mathematics (items 1–3) and the RBM2D sources at `c9a24cf`.

## 1. Scope, build, axioms, hygiene

```
$ git diff --name-status main...t/T2144
A	RBM3D/Evolution/CltPath.lean
A	RBM3D/Evolution/CltResolvent.lean
$ git diff --stat main...t/T2144 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ lake build RBM3D.Evolution.CltResolvent RBM3D.Evolution.CltPath   (audit worktree)
Build completed successfully (3777 jobs).
exit=0
$ grep -E "^(error|warning).*Evolution/Clt(Resolvent|Path)" build.log      -> (no lines)
$ grep -cwE "sorry|admit|native_decide|axiom" <both files>
RBM3D/Evolution/CltPath.lean:0
RBM3D/Evolution/CltResolvent.lean:0
$ grep axioms build.log  (private prefix `_private.…0.` stripped; 19 lines)
'RBM.Evol.cltCoord_adj'            [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltDeriv_entry'          [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltDeriv_eval_le'        [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltDeriv_evalMulti_le'   [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltEta_lower'            [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltEval_det_le'          [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltEval_detMulti_le'     [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltFarGeomHalf'          [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltFarGeomNear'          [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltPath_bound'           [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltPathMulti_bound'      [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltPert_max_le'          [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltPert_sub_le'          [propext, Classical.choice, Quot.sound]
cltres_chk_witness, cltres_chk_near, cltres_chk_half,
cltpath_chk_szCL, cltpath_chk_szCL_multi, cltpath_chk_nondeg   [propext, Classical.choice, Quot.sound]
$ imports
CltResolvent.lean: RBM3D.Evolution.CltSwap, RBM3D.Gauss.FlowCalculus, RBM3D.Green.EntryCore
CltPath.lean:      RBM3D.Evolution.CltResolvent, RBM3D.Induction.Step5Pins   (no `import RBM3D`)
$ public-name clash grep against main 3b1c6a5 (git grep -nwE "(def|theorem|lemma|structure|abbrev) <n>" main -- RBM3D)
gEntry:0 LocalForm:0 cltY:0 cltCoordDir:0 CltPertMaxLe:0 CltPertSubLe:0 CltDerivEntry:0 CltDerivEval:0
CltDerivEvalMulti:0 cltCk:0 CltEtaLower:0 CltEvalDetLe:0 CltEvalDetLeMulti:0 CltFarGeomHalf:0 CltFarGeomNear:0
CltCoordAdj:0 cltPert_max_le:0 cltPert_sub_le:0 cltDeriv_entry:0 cltDeriv_eval_le:0 cltDeriv_evalMulti_le:0
cltEta_lower:0 cltEval_det_le:0 cltEval_detMulti_le:0 cltFarGeomHalf:0 cltFarGeomNear:0 cltCoord_adj:0
cltEvalAt:0 cltYo:0 cltCoefSum:0 cltCoefSumMulti:0 cltGoodAt:0 CltPathBound:0 CltPathBoundMulti:0
cltPath_bound:0 cltPathMulti_bound:0
```
Only the two sole writable files are touched; no frozen signature is touched (both files are new).

## 2. Statements against the ticket (independent script `auddiff.py`)

Each RBM2D statement at `c9a24cf` (`git show`), with the ticket's dictionary applied textually (`Z2 L→Zd d L`, `zdist2 L→zdistInf d L`, `Idx L W→Idx d L W`, `Coord L W→CoordF d L W`, `spectralZ→zt`, `splitEquiv→split`, `(W*L)^2→(W*L)^d`, extra `d`), token-diffed against the RBM3D statement:
```
cltCoordDir IDENTICAL after dictionary
CltPertMaxLe IDENTICAL after dictionary
CltPertSubLe IDENTICAL after dictionary
CltDerivEntry IDENTICAL after dictionary
CltDerivEval IDENTICAL after dictionary
cltCk IDENTICAL after dictionary
CltEtaLower IDENTICAL after dictionary
CltEvalDetLe IDENTICAL after dictionary
CltFarGeomHalf IDENTICAL after dictionary
CltFarGeomNear DIFFERS
   2D: (w ℓ  | 3D: (ρ R
   2D: 6 ≤ w → 1 ≤ ℓ → w ^ 2 * ℓ  | 3D: R
   2D: ℓ * w  | 3D: ρ
   2D: ℓ * w  | 3D: R / 2 - ρ - 1
   2D: ℓ * w  | 3D: R / 2 - ρ - 1
CltCoordAdj DIFFERS
   2D:   | 3D: (g : ℝ)
   2D: W], 3 ≤ L → ∀ c  | 3D: W] (c
   2D: W, (gvar  | 3D: W), (gvarF d
   2D:   | 3D: g
   2D:   | 3D: d
   2D:   | 3D: d
cltYo IDENTICAL after dictionary
cltCoefSum DIFFERS
   2D: ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool, ‖F.coef  | 3D: cltCoefSumMulti F
   2D: j q‖ * (j : ℝ) * 4 ^ (j : ℕ)  | 3D:
cltGoodAt DIFFERS
   2D:   | 3D: (d L W : ℕ) [NeZero L] [NeZero W]
   2D: ρ  | 3D: θ
   2D: ρ  | 3D: θ
CltPathBound DIFFERS
   2D: τ  | 3D: ρ R θ
   2D: τ u → 6 ≤ (W : ℝ) ^ τ → 1 ≤ ellT L u  | 3D: ρ
   2D: ((W : ℝ) ^ τ) ^ 2 * ellT L u  | 3D: R
   2D:   | 3D: θ ≤ R / 2 - ρ - 1 →
   2D:   | 3D: d L W
   2D: (ellT L u * (W : ℝ) ^ τ)  | 3D: θ
```
Reading of the differences against the ticket:
* `CltFarGeomNear` (item 2): exactly the ticket's re-scaled form `R/2 ≤ |a−b|_∞ → |a'−a|_∞ ≤ 1 → |x−b|_∞ < ρ → R/2−ρ−1 ≤ |x−a|_∞ ∧ R/2−ρ−1 ≤ |x−a'|_∞`, for all real `ρ, R`. At `ρ=w`, `R=10w` the bound is `4w−1 ≥ c w` for `c∈{1,3}`, `w ≥ 1`. That inequality is proved in Lean in `cltpath_chk_nondeg`.
* `CltCoordAdj`: `g` explicit (`gvarF` needs it); `3 ≤ L` dropped, which weakens the hypotheses; adjacency is in `zdistInf`, as the ticket's dictionary says. This is the general statement, not a special case.
* `cltCoefSum := cltCoefSumMulti F (fun _ => b)`, and `cltCoefSumMulti` is RBM2D's sum with `F.coef b` written out (`CltPath.lean:69-75`). It unfolds to the same expression.
* `cltGoodAt`/`CltPathBound`: the far threshold `θ` is a free parameter with `θ ≤ R/2−ρ−1`. RBM2D's `6 ≤ W^τ`, `1 ≤ ellT` are gone (ticket item 3). The conclusion and the remaining hypotheses (`0≤u<1`, `Im z≠0`, `16W^{-1/2}≤1`, adjacency, `|s−ω₀c|≤2W^{-1/2}`) are unchanged. `θ` is free, so the consumer can take `θ = c(log W)^3ℓ_s` (§43). This is at least as general as the ticket's form.
* Vocabulary (item 1): `LocalForm d L W k K` (single field `coef`, no Prop field), `eval`, `Local ρ` with `zdistInf` and `< ρ` (RBM2D `< ellT L s * W^τ`), `gEntry := Gres M (zt E s) σ x y` (ticket: "or the merged analogue"; grep: none on main), `cltY F E s M b := F.eval E s M (fun _ => b)`. All match the ticket (`CltResolvent.lean:61-98`).
* Additional public `Multi` forms (`CltDerivEvalMulti`, `CltEvalDetLeMulti`, `CltPathBoundMulti`, `cltEvalAt`, `cltCoefSumMulti` and their theorems): the one-label pins are corollaries at `k = 1` (`cltPath_bound` := `cltPathMulti_bound … 1 … (fun _ => b)`, `CltPath.lean:299-302`). Their names are not pinned, but all carry the `clt` stem and none clashes with a name on main. Recorded as an observation.

## 3. Hidden hypotheses, vacuity, cycles

* `LocalForm` has no Prop field; `cltGoodAt`, `F.Local ρ` and `cltCoordDir` appear as explicit hypotheses in the signatures.
* Every target theorem has a closed type `: CltXxx …` with no extra hypotheses (`grep "^theorem"` lines 335, 368, 439, 483, 575, 610, 694, 719, 746, 764, 805 of CltResolvent; 281, 299 of CltPath).
* Dependencies are merged modules only (imports above). No new pin of another gate is assumed, and the targets have no external hypothesis, so no limit check is owed (TEAM §8 lesson 14 not triggered).
* Joint satisfiability of all `CltPathBound` hypotheses: shown by the instance in §4.

## 4. Compiled nonempty instances (read in the files; all build)

| endpoint | check (same file) | data | open hyps |
|---|---|---|---|
| `cltPert_max_le`, `cltPert_sub_le`, `cltDeriv_entry` | `cltres_chk_M1/M2/M3`, bundled in `cltres_chk_witness` (:1082) | d=3, L=3, W=1, g=1/2, M=0, z=zt 0 (1/2), t=1/8, g-bound 2 (4·|t|·2=1); direction `coordinateMatrix c` with `gvarF c ≠ 0`, `c.1 ≠ c.2.1`, entry 1 (`cltres_chk_offdiag`, by `decide` on blocks 0, e₀) | none |
| `cltDeriv_eval_le` / `…Multi` | `cltres_chk_M4` / `M4Multi` | the same data, K=1, one monomial `G_{c.1 c.2.1}`, k=1 / k=2 | none |
| `cltEta_lower` | `cltres_chk_E4` | κ=1, δ=1/2, E=0, u=1/2, N=27 (`27^{-1/2} ≤ 1/2` proved) | none |
| `cltEval_det_le` / `…Multi` | `cltres_chk_M5` / `M5Multi` | same, C'=0, M=0 | none |
| `cltFarGeomHalf` | `cltres_chk_half` | Z_7^3, m=2, b=(0,(3,0,0)), R=3, a=(1,0,0); first disjunct shown false | none |
| `cltFarGeomNear` | `cltres_chk_near` | Z_61^3, ρ=1, R=16, a=(10,0,0), a'=(11,0,0), b=x=0 → 6 ≤ dists | none |
| `cltCoord_adj` | `cltres_chk_dir`, `cltres_chk_adj` | L=3, W=1, g=1/2, the coordinate with `gvarF ≠ 0` | none |
| `cltPath_bound` | `cltpath_chk_szCL` (:486) | `szCL` n=0 (L=15925248, W=2^24), E=0, u=1/2, ω₀=0, ρ=w=(log W)^3ℓ_s, R=10w, θ=R/2−ρ−1, D'=1, b=0, c=(x₁,x₁,+), x₁ block (70000,0,0) (`cpx_far`), s=W^{-1/2}>0 | none |
| `cltPathMulti_bound` | `cltpath_chk_szCL_multi` (:510) | same, k=2 | none |

Every argument in these checks is a proof term or a closed tactic proof; no hypothesis is left open. The data is not degenerate: N = 27 or (WL)^3, the index sets are nonempty, the window ρ = w ≥ 1 > 0, θ = 4w−1 ≥ 3w, and the step s > 0. The `szCL` sizes are the data the ticket prescribes.

## 5. Paper-delta coverage

The prove report §(d) proposes `T2144a` (label count k), `T2144b` (`CltFarGeomNear` ρ/R form), `T2144c` (`CltCoordAdj`: g explicit, no `3 ≤ L`, `zdistInf` adjacency), `T2144d` (free threshold θ in `cltGoodAt`/`CltPathBound`; `gEntry` = merged `Gres`; `Local ρ`). Together these cover every difference listed in §2. `N=(WL)^d` is the ticket's dictionary.

## 6. Observations (no effect on the verdict)

* O1. The ticket asks for instances at `L = 3`. The geometry instances use `L = 7` and `L = 61` instead, because at `L = 3` every block pair is adjacent and the instance would be degenerate. This is a stronger choice, not a defect.
* O2. In `cltpath_chk_szCL`, ω₀ = 0, so the resolvent is diagonal and the perturbed coordinate is diagonal at a block far from the monomial. The left side is therefore 0. Every hypothesis is still discharged at nondegenerate data, which is what CLAUDE.md §4 step 2 requires.
* O3. The branch is based on `ae259a6`; main is now at `3b1c6a5`. The clash grep at `3b1c6a5` is clean, and the hub's full build at merge decides the rest.
* O4. The consumer check (S5-20/S5-21 scales, finding F1 on two labels) is in prove report (a)/(b). The Multi forms address F1. The two-label threshold arithmetic (`ρ = w+1`, `c ≤ 2`) is a matter for S5-21 and is not a target here.

## Verdict

| target | verdict |
|---|---|
| 1. Vocabulary (`LocalForm`, `eval`, `Local ρ`, `gEntry`, `cltY`) | PASS |
| 2. Port of `CltResolvent` (11 pins + re-scaled `CltFarGeomNear`, `CltCoordAdj`) | PASS |
| 3. Port of `CltPath` (`cltYo`, `cltCoefSum`, `cltGoodAt`, `CltPathBound`, `cltPath_bound`) | PASS |

**T2144: PASS.** No dispatcher sign-off needed.
