Auditor model: claude-opus-5-5

# T2176 audit (round 1) — UN-06 `Universality/FreeConv` + `FreeConvStability` (port)

Written Mon Oct  5 06:08:56 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2176-audit1`, detached at `t/T2176` = `23ab8ce`.
Scratch: `scratchpad/T2176/` (`diff.sh`, `ax.lean`, `src1.lean`, `src2.lean` = `git -C ../RBM2D show c9a24cf:RBM2D/Universality/{FreeConv,FreeConvStability}.lean`).

**Overall: BLOCKED — needs dispatcher sign-off** (one item, §3 below). Four targets PASS; `freeConv_stable_local` passes statement, build and axioms, but its instance keeps the deterministic hypothesis `hyp`, which the ticket said must be discharged, and no repair can discharge it.

## 1. Statements (script diff against the RBM2D source `c9a24cf`, the ticket's pin)

```
$ bash scratchpad/T2176/diff.sh   (extract each declaration header up to its first `:=` from source and from the new file; diff)
== freeConv_existsUnique (src 4 lines, new 4 lines, new at 639)
IDENTICAL
== freeConvST (src 1 lines, new 1 lines, new at 656)
IDENTICAL
== isFreeConv51_freeConvST (src 2 lines, new 2 lines, new at 660)
IDENTICAL
== FreeConvStability.msc_tendsto_mE (src 2 lines, new 2 lines, new at 223)
2c2
<     Tendsto (fun η : ℝ => msc ⟨E, η⟩) (𝓝[>] 0) (𝓝 (spectralM E)) := by
---
>     Tendsto (fun η : ℝ => msc ⟨E, η⟩) (𝓝[>] 0) (𝓝 (mE E)) := by
== FreeConvStability.freeConv_stable_local (src 9 lines, new 9 lines, new at 748)
IDENTICAL
```
The renaming `spectralM` → `mE` keeps the same definition:
```
RBM3D  Defs/Semicircle.lean:38   noncomputable def mE (E : ℝ) : ℂ := (-E + Real.sqrt (4 - E ^ 2) * I) / 2
RBM2D  c9a24cf Gauss/SpectralWindow.lean:21-22  noncomputable def spectralM (E : ℝ) : ℂ := (-E + Real.sqrt (4 - E ^ 2) * I) / 2
RBM3D  Pins.lean:237  def mV … := (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹          (= RBM2D Pins.lean:114-115)
RBM3D  Pins.lean:84   def rhoSC (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / (2 * Real.pi)         (= RBM2D Pins.lean:139)
RBM3D  Pins.lean:249  def IsFreeConv32 … := ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧ m z = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹
```
`isFreeConv51_freeConvST` concludes `IsFreeConv32 v t (freeConvST v t)` (the merged pin; no `IsFreeConv51` occurs).
Elaborated statement of the stability endpoint (`#check`, scratch `ax.lean`): quantifier order `κ > 0 → ∃ c₀ C₀ > 0, ∀ n v s t E₀ ε, 0<t → t≤c₀ → s=1-t → |E₀|≤2-κ → 0≤ε → ε≤c₀ → hyp → ∃ ρ, …` — the same order as the source.
No statement mentions `d`, `L`, `W` or `N = (WL)^d` (all are over an arbitrary `Fintype`/`Nonempty` index), so the ticket's stop condition (dependence on `d = 2`) is not triggered.

Body diff (source with `spectralM→mE`, `RBM.Endpoints` dropped, vs new file, from `noncomputable section`):
```
== FreeConv:            6c6 (open line) ; 685a686,698 ; 686a700,725   (added instances only)
== FreeConvStability:   6c6 ; 11,36c11 (3 private helpers deleted, replaced by merged
                        msc_add_eq_neg_inv / lemT_ge / norm_msc_pos of Defs/Semicircle) ; 54c29 ; 132c107 ; 141c116
                        (call sites renamed) ; 786a762,799 (added negative example)
```

## 2. Hidden hypotheses, vacuity, cycles

```
$ grep -n "^import\|^structure\|^class\|^axiom\|^opaque" RBM3D/Universality/FreeConv*.lean
FreeConv.lean:6:import RBM3D.Universality.Pins
FreeConvStability.lean:6:import RBM3D.Universality.FreeConv
FreeConvStability.lean:7:import RBM3D.Defs.Semicircle
FreeConvStability.lean:8:import Mathlib.Analysis.Complex.Liouville
FreeConvStability.lean:9:import Mathlib.Analysis.Real.Pi.Bounds
FreeConvStability.lean:10:import Mathlib.Topology.MetricSpace.Contracting
```
No structure/class fields; dependencies are merged modules (`Pins` T2174, `Defs/Semicircle`) and Mathlib; no cycle.
`freeConv_existsUnique`, `freeConvST`, `isFreeConv51_freeConvST`, `msc_tendsto_mE`: only deterministic hypotheses (`0≤t`, `0<Im z`, `|E|<2`), all non-vacuous (instances §3).
`freeConv_stable_local`: the premise `hyp` (closeness of `mV v` to the rescaled semicircle on `|Re w| ≤ min κ 1/16`, `c₀t/4 ≤ Im w ≤ 1/2`) is the analytic input supplied downstream by the local law. Non-vacuity is supported only numerically: prove report (a)(ii-c), quantile measure with `N = 10^6`, sampled sup `3.36e-4 ≤ ε = 2.08e-3` (a sampled-grid check, not a proof).

## 3. Compiled nonempty instances

| Target | Instance (file:line) | Data | Verdict |
|---|---|---|---|
| `freeConv_existsUnique` | `FreeConv.lean:697`, `:729` | `Fin 3`, `v=(-1,0,1)`, `t=1/2`, `z=i/10`; and `v≡0`, `t=1/2`, `z=3/10+i/2` | PASS, all hypotheses discharged |
| `freeConvST`, `isFreeConv51_freeConvST` | `FreeConv.lean:703`, `:706`, `:736` | same; `:736` also proves `Im m>0` and `(1/2)m²+zm+1=0` at `v≡0` | PASS |
| `msc_tendsto_mE` | `FreeConvStability.lean:774`, `:779` | `E=0`, `E=1`, with `0 < Im mE E` | PASS |
| `freeConv_stable_local` | `FreeConvStability.lean:785`, `:800` | `κ=1`, `E₀=0`, `t=c₀` (resp. `1/240`), `ε=c₀/2` (resp. `1/480`), `s=1-t`; **`hyp` kept, `v` and index type universal** | **needs dispatcher sign-off** |

The ticket (line 16) asks for `freeConv_stable_local` "at a concrete `v` (e.g. `v ≡ 0` on `Fin 3`) … all hypotheses discharged". `hyp` is deterministic (a condition on the concrete `v`), not another gate's named pin, so CLAUDE.md §4 step 2 requires it discharged. The file proves the ticket's example impossible (`FreeConvStability.lean:821`, compiled: `¬ hyp` at `v ≡ 0` on `Fin 3`, `κ=1`, `t=1/240`, `ε=1/480`). Any witness must be large:
```
$ python3 -c "…"   (lower bound on N for any v satisfying hyp; c₀ ≤ min κ 1/240 ≤ 1/240, best case t = c₀)
max c0 (kappa'=1) = 0.004166666666666667  lowest Im w = 4.340277777777778e-06
at w=v_j+i*eta: Im mV >= 1/(N*eta); target norm <= sigma^-1*1 = 0.9979144919948469 ; need 1/(N*eta) <=  1.0020811586615137
=> N >=  229921.49688528897
no atom in |Re|<=1/16: Im mV(i*eta) <= 256*eta = 0.0011111111111111111  vs Im target ~ 0.9979144919948469
```
So every `v` that satisfies `hyp` has `N ≳ 2.3·10^5` points (an atom must lie in `|Re w| ≤ 1/16`, else `Im mV` is ≤ 1.1e-3 at `w = iη`, far below the target's ≈ 1). A Lean witness of that size is not feasible, so a repairer cannot meet the ticket's instance requirement. The source's own instance (RBM2D `FreeConvStabilityCheck`, under an RBM2D ruling "T2205-amend-1, ruling 1", quoted in the docstring at `FreeConvStability.lean:762`) keeps `hyp` the same way; I find no RBM3D DECISIONS entry that adopts that ruling (`grep -n -i "locSC\|undischarg\|stable_local\|T2176" docs/DECISIONS.md` hits only §1 line 12/32 and §54's re-slicing line 380).

**Missing input (dispatcher decision):** either (A) accept, for `freeConv_stable_local`, an instance that discharges every hypothesis except the local-law input `hyp` (as the RBM2D ruling did), recorded in DECISIONS, or (B) amend the ticket's instance requirement. Under (A) this target PASSes as built (no code change needed); under (B) state the new requirement.

## 4. Build and axioms (audit worktree)

```
$ lake build RBM3D.Universality.FreeConv RBM3D.Universality.FreeConvStability 2>&1 | grep -E "error|declaration uses|sorry|Build completed"
Build completed successfully (3333 jobs).
$ grep -nE "sorry|admit|native_decide|^\s*axiom |set_option (maxHeartbeats|maxRecDepth)" RBM3D/Universality/FreeConv*.lean
(no output)
$ lake env lean scratchpad/T2176/ax.lean
'RBM.Univ.freeConv_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.isFreeConv51_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvStability.msc_tendsto_mE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvStability.freeConv_stable_local' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-only main...HEAD
RBM3D/Universality/FreeConv.lean
RBM3D/Universality/FreeConvStability.lean
$ git diff --stat main...t/T2176 -- RBM3D/Universality/Pins.lean RBM3D/Defs RBM3D.lean
(no output)
```
Only the two sole writable files; no frozen signature touched. Public declarations: 11 + 2; private: 12 + 32 (§3 (E) respected; the prover's name-clash grep on `main` is 0 for every public name).

## 5. Paper deltas

No Lean statement differs from its RBM2D source except `spectralM → mE` (same definition). The paper (arXiv:2507.20274) does not state these lemmas; they are inputs of [32] (2.5). Prove report (d) proposes no candidate; none is required. The kept-`hyp` form of the stability instance is a ticket/process question (§3), not a paper delta.

## 6. Observations (no verdict effect)

- Docstrings quote RBM2D labels (`T2205`, `T2205-amend-1`, `DECISIONS §70`) at `FreeConv.lean:26,667,681`, `FreeConvStability.lean:40,762,797`; in RBM3D these point to the wrong documents (prove report (d) records this).
- Prove report (a)(ii-c) gives non-vacuity of `hyp` as a sampled-grid numerical check only (stated as such).

## Verdicts

- `freeConv_existsUnique`: PASS.
- `freeConvST`: PASS.
- `isFreeConv51_freeConvST`: PASS.
- `FreeConvStability.msc_tendsto_mE`: PASS.
- `FreeConvStability.freeConv_stable_local`: BLOCKED — **needs dispatcher sign-off**: the instance at `FreeConvStability.lean:785/800` keeps the deterministic hypothesis `hyp`; the ticket's instance (`v ≡ 0` on `Fin 3`, all discharged) is proved false (`:821`), and any witness needs `N ≳ 2.3·10^5`. Missing input: dispatcher ruling (A) or (B) of §3. Statement, build, axioms and port fidelity otherwise PASS.
- Ticket overall: BLOCKED (needs dispatcher sign-off); no repair list (a repairer cannot discharge `hyp`).
