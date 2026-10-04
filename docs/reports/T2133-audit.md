Auditor model: claude-opus-5-5

# T2133 audit (round 1): S3-07a `Induction/DecayLoopA` (written Sun Oct  4 12:24:44 UTC 2026)

Branch `t/T2133` at `cc56e20`; audit worktree `RBM3D-wt/T2133-audit1` (detached at `cc56e20`).
`S=` scratchpad `T2133/`.

## 1. Scope, build, axioms

```
$ git diff --name-only main...t/T2133
RBM3D/Induction/DecayLoopA.lean
$ git diff main...t/T2133 -- RBM3D/Test/Axioms.lean | wc -l
       0
$ lake build RBM3D.Induction.DecayLoopA        (audit worktree)
Build completed successfully (3732 jobs).      (no warning line from DecayLoopA.lean)
$ lake env lean $S/audit_axioms.lean
'RBM.Gauss.Sizes.stDecayLoopAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDecayLoopPT_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.DecayLoopA_diam_le_KLmaxDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.DecayLoopAInst.sz0_far_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|set_option" RBM3D/Induction/DecayLoopA.lean
54:set_option linter.style.longLine false
55:set_option linter.unusedSectionVars false
$ sed -n 6,11p RBM3D/Induction/DecayLoopA.lean      (imports; no `import RBM3D`)
import RBM3D.Induction.KDecay / Step2Defs / Split / Defs / PerTimeCalc ; import RBM3D.Green.Pins
```
Only the one writable file changes; no frozen signature touched (no other file in the diff).

## 2. Target 1: `STDecayLoopAt` / `stDecayLoopAt_holds (hd : 3 ≤ d)`

Pin (`DecayLoopA.lean:84-104`), hypotheses vs the ticket's mathematics:

| ticket | Lean |
|---|---|
| `sz.Admissible 𝔠 𝔡` | `sz.Admissible 𝔠 𝔡` |
| `|E n| ≤ 2 − κ` | `0 < κ → (∀ n, |E n| ≤ 2 - κ)` (`0 < κ` as RBM2D `DecayLoopAt`) |
| `0 ≤ u n < 1` | `(∀ n, 0 ≤ u n) → (∀ n, u n < 1)` |
| `1 ≤ P n ≤ N^{C₀}` eventually | `∀ᶠ n in atTop, 1 ≤ P n ∧ P n ≤ N ^ C₀` |
| decay input = section of `STStep2DecayPT` with prefactor `P` | script diff below: identical |
| `∀ k ≥ 1, τ' > 0, D' > 0`, `(‖𝓛‖+‖𝓛−𝒦‖)·1(ℓ_u W^{τ'} ≤ diam_∞ a) ≺ W^{-D'}` per time | `∀ k, 1 ≤ k → ∀ τ', 0 < τ' → ∀ D', 0 < D' → PrecPT … ((‖Lloop‖ + ‖Lloop − STKloop‖) * if ellT … * W^τ' ≤ STdiamInf a then 1 else 0) (W^(-D'))` |
| `diam_∞ a = max_{i,j} zdistInf (a i − a j)` | `STdiamInf a = univ.sup (p : Fin k × Fin k) ↦ zdistInf d L (a p.1 − a p.2)` |

Paper convention check (`|a−b|` is `ℓ^∞`, so `diam_∞` matches the paper):
```
$ sed -n 275p paper/tex/1_2_Intro_model_result.tex
\[ |x-y|\equiv \|\rep{x-y}_{WL}\|_{\infty},\quad \forall x,y\in \ZL,\quad \text{and}\quad |a-b|\equiv \|\rep{a-b}_L\|_{\infty},\quad \forall a,b\in \Zn.\]
```
Decay input vs merged `STStep2DecayPT` (`Step2Defs.lean:287-297`), after substituting the section
`(p.1 : ℝ) := u n`, `TimeIcc s t n := Unit`, prefactor `((1-s)/(1-u))^Cd * Bctl^{1/5} := P n`:
```
$ for f in step2_sec pin_in; do tr -s ' \n' ' ' < $f.txt | grep -o '(fun n p ω.*(-D))' > $f.body; done
$ diff step2_sec.body pin_in.body && echo "IDENTICAL (after s:=section u, prefactor:=P n)"
IDENTICAL (after s:=section u, prefactor:=P n)
```
Quantifier order: fixed data `sz κ 𝔠 𝔡 C₀ E u P` before the hypotheses, `k τ' D'` after, `∀ᶠ n`
inside `PrecPT` (merged `Path.PerTimeDomAt`). `stDecayLoopAt_holds` has no hypothesis beyond
`3 ≤ d` (DECISIONS §36, from `stKcalDecay_holds`); it proves the pin for all inputs.

Vacuity / hidden hypotheses / cycles: the pin is a plain `Prop` (no structure); `Sizes`,
`Admissible`, `PrecPT`, `Lloop`, `STKloop`, `STWB`, `ellT` are merged. Dependencies
(`stKcalDecay_holds` T2129, `Split`, `PerTimeCalc`, `Green/Pins`) are merged; nothing on `main`
references the new names (prover grep, exit 1), so no cycle. The decay input is the only
non-deterministic hypothesis; it is a section of the owed Step-2 pin `STStep2DecayPT` (another
gate), allowed to stay a hypothesis of the example. Limit check of that input: at the instance
`P ≡ 1` dominates the paper's prefactor `Bctl^{1/5}` at `s = u` (prove report `check_inst.py`,
`Bctl^{1/5} = 0.144, 0.018, 0.005, 0.002` at `n = 0..3`), so the input is the paper's
`(Eq:Gdecay_w)` weakened, not a stronger premise.

Compiled nonempty instance (`DecayLoopA.lean:1174-1195`, compiled by the build above):
`stDecayLoopAt_holds (d := 3)` at `sz0`, `κ = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`, `C₀ = 0`, `E ≡ 0`,
`u ≡ 1/2`, `P ≡ 1`, `k = 3`, `τ' = 1/10`, `D' = 1`; discharged: `0 < κ`, `|E| ≤ 2−κ`,
`sz0_admissible`, `0 ≤ u`, `u < 1`, `1 ≤ P ≤ N^0` (`Eventually.of_forall … ⟨le_rfl, by simp⟩`);
`hdec` (decay input) stays a hypothesis. Non-degeneracy of the indicator:
`sz0_far_nonempty (n) : ∃ a : Fin 3 → Zd 3 (sz0.L n), ellT … (1/2) * W^(1/10) ≤ STdiamInf a`
(`:1106`), proved for every `n`, axioms standard. `L = 4(n+1) ≥ 4`, `W = (2(n+1))^5`, `k = 3`:
not `N = 0`, not empty, not collapsed.

**Target 1: PASS.**

## 3. Target 2: `STDecayLoopPT` / `stDecayLoopPT_of_step2`

Window conclusion vs single-time conclusion (substituting `u n := p.1`, `Unit := TimeIcc s t n`):
```
$ diff at_concl.txt pt_concl.txt      (bodies of DecayLoopA.lean:96-104 vs :107-115)
< PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖Lloop … - STKloop …‖) * (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0)) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) /-- **`lem_decayLoop` over a window …
> PrecPT sz (U := fun n => TimeIcc s t n × …) … (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))
```
(the only difference is the trailing docstring captured by the line range: bodies identical.)

Signature (`#check`, audit worktree):
```
@RBM.Gauss.Sizes.stDecayLoopPT_of_step2 : ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : RBM.Gauss.Sizes d) {κ ε 𝔠 𝔡 : ℝ}
  {z : ℕ → ℂ}, 0 < κ → 0 < ε → sz.STFlow κ ε 𝔠 𝔡 z → ∀ {s t : ℕ → ℝ}, (∀ (n : ℕ), 0 ≤ s n) →
  (∀ (n : ℕ), s n ≤ t n) → (∀ (n : ℕ), t n ≤ RBM.lemT (z n)) → ∀ (Cd : ℝ),
  sz.STStep2DecayPT Cd (RBM.Gauss.Sizes.STflowE z) s t → sz.STDecayLoopPT (RBM.Gauss.Sizes.STflowE z) s t
```
Matches the ticket: flow hypotheses `STFlow`, `0 ≤ s ≤ t ≤ lemT z`, decay input exactly the merged
`STStep2DecayPT Cd sz E s t`, any real `Cd` (no sign condition). `E` is `STflowE z`, which is the
energy every merged Step-2/main-induction pin uses (`Defs.lean:283-300`: `STMainInd` states
`STLK sz (STflowE z) s …`), so this is the ticket's `E`, not a special case. `C₀` source stated in
the prove report (b) item 7: `1 − u ≥ N^{-1+ε/2}` from `v3_premises_of_stFlow`, `Bctl ≤ 2`,
`P' = max P_u 1`, `C₀ = max Cd 0 + 1`. No `STConStInd`, no structure hypothesis.

Compiled nonempty instances (`:1197-1217`, compiled): `stDecayLoopPT_of_step2 (d := 3)` at
`sz0`, `κ = ε = 1/10`, `flow_z0`, `sInst ≡ 0`, `tInst ≡ 1/16` (`Defs.lean:439-440`), `0 ≤ s`
(`le_rfl`), `s ≤ t` (`norm_num`), `t ≤ lemT z0` (`sixteenth_le_lemT`, `Defs.lean:429`), any `Cd`,
`hD : STStep2DecayPT …` as hypothesis (another gate's pin); the third example further applies it at
`k = 3`, `τ' = 1/10`, `D' = 1`. Window `[0, 1/16]` is nondegenerate.

**Target 2: PASS.**

## 4. Paper-delta coverage

| Lean/paper difference | candidate |
|---|---|
| Hypotheses: only the `(+,−)` 2-loop decay section; no `(Gt_bound_flow)`, no `(GijGEX)` (`3_5:1113, 1126`) | `T2133a` |
| `3 ≤ d` on both theorems (§36) | `T2133b` |
| `‖𝓛‖ + ‖𝓛−𝒦‖` vs paper `|𝓛| + |𝒦|`; `k ≥ 1` vs `n ≥ 2`; per-`(σ,a)` per-time `≺` vs `max_σ` inside `P(·) ≤ W^{-D'}` | `T2133c` |
| Prefactor carried as `P`, `C₀`; window uses `P' = max(P_u,1)`, `C₀ = max Cd 0 + 1` | `T2133d` |
| `diam_∞` = `ℓ^∞` (paper line 275 convention) | none needed |
All differences are covered.

## 5. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. `sz0_far_nonempty` is an unpinned public name; it lives in namespace
  `RBM.Gauss.DecayLoopAInst` (file stem), which satisfies §3 (E) in substance.
- O2. Prove report (b) item 3 ports from RBM2D `9e0f275`, the ticket cites `c9a24cf`; the
  diff-stat between them is pasted, so the port citation is complete.
- O3. Prove report (a) row 9 gives `Q* = 2D'+3+…`, the Lean proof uses `2D'+1+…` with a larger
  eventual threshold on `W`; constants only (stated in (b) item 6).
- O4. The uniform-in-`(σ,a)` form of `res_decayLK` (`max_σ` inside the probability) is not
  proved; prove report (d) records it, derivable via `stochDomAt_of_perTimeDomAt`.

## Verdict

| target | verdict |
|---|---|
| 1 `STDecayLoopAt`, `stDecayLoopAt_holds` | PASS |
| 2 `STDecayLoopPT`, `stDecayLoopPT_of_step2` | PASS |

**T2133: PASS.** No dispatcher sign-off needed.
