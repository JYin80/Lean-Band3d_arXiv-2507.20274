Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 05:52:54 UTC 2026 (start); written 05:55 UTC

Statements read from `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/{FreeConv,FreeConvStability}.lean`
(`freeConv_existsUnique` FreeConv:636, `freeConv_stable_local` FreeConvStability:765, `fcs_stable_local_explicit` :746,
`fcs_core` :645, `fcs_contract` :516). Both statements quantify over an arbitrary `Fintype`/`Nonempty` index type `n`;
neither mentions `N`, `W`, `L`, `d` or `Z2`. Hence no constant below depends on `N = (WL)^d` (checked: grep of the two source
files for `Z2|Fin 2|d = 2` returns nothing). The only `N`-dependence is whether hypothesis `hyp` can hold (see (ii-b)).

### (i) Exponent table

Data: `κ > 0` (bulk margin, `|E₀| ≤ 2-κ`), `κ' := min κ 1 ≤ 1`, `s = 1-t`, `σ = s^{-1/2}`.

| Quantity | Value (source) | Constraint | Slack |
|---|---|---|---|
| `c₀` (window and size of `t`, `ε`) | `κ'/240` (`:765-771`) | `0<t≤c₀`, `0≤ε≤c₀` | none: the contraction below closes with equality at `t=ε=c₀` |
| `C₀` (Lipschitz/closeness const.) | `2` | `|ρ-ρ_sc(E₀)| ≤ C₀ε`, `‖freeConvST v t ⟨0,η⟩ - msc⟨E₀,η⟩‖ ≤ C₀ε` for `η∈(0,1/4]` | ball radius `2tε` for `ω` (`:557,573`) |
| Strip of `hyp` | `|Re w| ≤ κ'/16`, `c₀t/4 ≤ Im w ≤ 1/2` | closeness `‖mV v w - σ·msc(σ(w+E₀))‖ ≤ ε` on it | lowest scale `c₀t/4 = κ'² t/960` |
| Contraction constant | `t·(ε/(κ't/96) + 24/κ') = (96ε+24t)/κ'` (`fcs_contract:536-541`) | `≤ 1/2` | at `ε=t=κ'/240`: `(96+24)/240 = 1/2` exactly, slack 0 |
| Lipschitz of `m_sc`-reference | `24/κ'` (`fcsRef_lip:394`) on `|Re ω|≤κ'/16`, `Im ω ≤ 5/4` | uses `Im msc ≥ κ'/12` (`fcs_msc_im_ge:164`, `fcs_zregion:360`), `σ ≤ 1+2t`, `σ² ≤ 2` (`fcs_sigma:340`, needs `t ≤ 1/2`) | `t ≤ κ'/240 ≤ 1/240 ≪ 1/2` |
| Working rectangle | `|Re w| ≤ κ'/32`, `κ't/48 ≤ Im w ≤ ηmax+1/8` (`fcsRect:317`) | inside the strip of `hyp` with `ηmax = 1/4`: `Im w ≤ 3/8 ≤ 1/2` | `1/8` |
| `ηmax` | `1/4` (`fcs_core` `hη1: ηmax ≤ 1`) | `0<ηmax≤1`; `hyp` needed up to `ηmax+1/4 = 1/2` | `ηmax ≤ 1` vs `1/4`: factor 4 |
| Lipschitz of `η ↦ ω(η)` | `2` (header; gives limit `η↓0`) | — | — |
| `msc_tendsto_mE` | no constants | `|E|<2` | `Im mE E>0` |
| `freeConv_existsUnique` | none; `t ≥ 0`, `Im z>0` | `t=0` branch: `m = mV v z`; `t>0`: Banach/Liouville route | — |
| `N = (WL)^d` dependence | **none** (index type generic) | redo at `N=(WL)^3`: identical | — |

### (ii) One concrete nondegenerate instance

**(ii-a) `freeConv_existsUnique`, `freeConvST`, `isFreeConv51_freeConvST` (ticket data).** `N=27`, `t=1/2`, `z=0.3+0.5i`,
`v_i` = quantiles `(i+1/2)/27` of the semicircle of variance `s=1-t=1/2` (so `v ⊞ sc_t ≈ sc_1`, compared with `msc`).
Polynomial form of `m = N⁻¹Σ(v_i - z - t m)⁻¹` (degree 28) solved with mpmath at 60 digits; all roots with `Im>0` listed.
Command: `python3 inst1.py` (scratchpad `T2176/inst1.py`). Output:
```
v range -1.2736829400192806 1.2736829400192804 N= 27 t= 0.5 s=1-t= 0.5 z= (0.3 + 0.5j)
degree 28 roots with Im>0: ['(-0.113256715051 + 0.770744155841j)']
residual 1.6299e-61
msc(z)  = (-0.113252074982 + 0.770465780903j)
|m-msc(z)| = 0.000278414
iteration check:
(-0.113256715051 + 0.770744155841j)
```
Exactly one root with `Im>0` (existence and uniqueness); `Im m = 0.7707 > 0`; the fixed-point iteration from `m=i` agrees; the
fixed point is within `2.8e-4` of `msc(z)` (as `v` is a 27-point approximation of `sc_{1/2}`).
Second instance (`v ≡ 0` on `Fin 3`, `t=1/2`, same `z`; there `m` solves `t m²+z m+1=0`), `python3 inst3.py`:
```
roots [-0.40181803-1.97321652j -0.19818197+0.97321652j]
positive-Im root (-0.19818197250400657+0.9732165186160434j) residual 0.0
```
Exactly one root with `Im>0`. The source's own Lean instance (`Fin 3`, `v=(-1,0,1)`, `t=1/2`, `z=i/10`, FreeConv.lean `FreeConvCheck`)
also satisfies all hypotheses (`0≤t`, `0<Im z`, `Fintype`, `Nonempty`); no external hypothesis occurs.

**(ii-b) `msc_tendsto_mE`.** Hypothesis `|E|<2` only: `E=0`: `mE 0 = i`, `Im = 1`; `E=1`: `Im mE 1 = √3/2`. No external hypothesis.
Limit computation: `‖msc⟨E,η⟩ - mE E‖·Im mE E ≤ η` (`fcs_msc_sub_mE_le:231`), so the error is `≤ η/Im mE E → 0` as `η↓0`.

**(ii-c) `freeConv_stable_local`: the ticket's suggested instance cannot hold.** Take `κ=1`: `c₀ = 1/240`, `t=c₀`, `s=239/240`,
`ε=c₀/2`, `E₀=0`, strip `|Re w|≤1/16`, `c₀t/4 = 4.34e-6 ≤ Im w ≤ 1/2`. At `w=i/2` the left side of `hyp` is
`‖mV v w - σ msc(σ w)‖`. Command `python3 inst2.py` (first lines of output):
```
c0= 0.004166666666666667 t= 0.004166666666666667 s= 0.9958333333333333 eps= 0.0020833333333333333 eta_min=c0*t/4= 4.340277777777778e-06 strip |Re w|<= 0.0625
v=0 on Fin 3 LHS at w=i/2: 1.2179883272293917  vs eps= 0.0020833333333333333
v=(-1,0,1) LHS at w=i/2: 0.15132166056272478  vs eps= 0.0020833333333333333
```
So for `v ≡ 0` on `Fin 3` (the ticket's example) `hyp` is false (`1.218 > ε`); the hypothesis `hyp` says `mV v` is `ε`-close to the
Stieltjes transform of the semicircle of variance `s` down to scale `4.3e-6`, which `v ≡ 0` is not (the free convolution of `δ₀` is
`sc_t`, not the input `v` of `hyp`). The source records the same (`FreeConvStability:779-786`: `hyp` fails at `Fin 3`, `v=(-1,0,1)`).
A genuine witness needs `N` large. Same script, `v` = midpoint quantiles of `sc_s`, sampled sup of the left side over
`Re w ∈ {0,1/16} + [0, spacing]` (41 offsets) and `Im w` on 35 log/linear points in `[4.34e-6, 1/2]`:
```
N= 100000 spacing at 0= 3.135040836961802e-05 sup over sampled grid of LHS = 1.4453916197914796 at w= (1.567520418480901e-05+4.340277777777778e-06j) <= eps? False
N= 400000 spacing at 0= 7.837602092404505e-06 sup over sampled grid of LHS = 0.0638214753250559 at w= (0.06250333098088927+4.340277777777778e-06j) <= eps? False
N= 1000000 spacing at 0= 3.1350408369618016e-06 sup over sampled grid of LHS = 0.00033562411251682384 at w= (0.0625025864086905+4.340277777777778e-06j) <= eps? True
```
So `hyp` holds (on the sampled grid; a numerical check, not a proof) only for `N ≳ 10^6` (e.g. `N=(WL)^3=100^3`), where `hyp` is the
input supplied downstream by the local law (`locSC`); the source also keeps it as the only undischarged hypothesis (`:779-786`).
All other hypotheses are discharged at `κ=1`, `E₀=0`, `t=1/240=c₀`, `ε=1/480`, `s=239/240`, with `v` and the index type universal
(as in the source instance, `FreeConvStabilityCheck`, `:788-833`). Conclusion at these data (the `C₀=2` bound): `|ρ-ρ_sc(0)| ≤ 1/240`,
`‖freeConvST v t ⟨0,η⟩ - msc⟨0,η⟩‖ ≤ 1/240` for `η∈(0,1/4]`.
Limit computation for the closeness hypothesis (TEAM §8 lesson 14): the 10^6-point quantile measure satisfies it numerically
(sup `3.4e-4 ≤ 2.1e-3`), so the hypothesis set is satisfiable.

### Verdicts

- `freeConv_existsUnique`: PASS (instance (ii-a); dimension-free).
- `freeConvST`, `isFreeConv51_freeConvST` (against `IsFreeConv32`, `Pins.lean:124`, same shape `0<Im m ∧ m = N⁻¹Σ(v_i-z-t m)⁻¹`;
  here `Fintype.card ι` cast replaces `((Fintype.card n : ℕ) : ℂ)`, identical): PASS.
- `msc_tendsto_mE`: PASS (constants none; `spectralM` → `mE`).
- `freeConv_stable_local`: PASS as a statement (all constants `N`-independent, contraction closes with slack 0 at the stated `c₀`).
  Finding for stage 1b: the ticket's instruction "`v ≡ 0` on `Fin 3`, all hypotheses discharged" is unsatisfiable (`hyp` false, `1.218 > ε`);
  the compiled instance must keep `hyp` as the only undischarged hypothesis, as RBM2D `FreeConvStabilityCheck` does, with `v` and the
  index type universally quantified. No source statement depends on `d = 2`; none changes.

## (a') Preflight corrections (Mon Oct  5 06:05:58 UTC 2026)

No verdict changes.
- Citation: (a) cites `IsFreeConv32, Pins.lean:124`; that is the RBM2D line. In RBM3D it is `RBM3D/Universality/Pins.lean:249` (`mV` `:237`).
- The finding of (a) (ii-c) that the ticket's instance "`v = 0` on `Fin 3`, all hypotheses discharged" is unsatisfiable for `freeConv_stable_local` is confirmed in Lean: the compiled negative example `FreeConvStability.lean:821` proves `hyp` false there (left side at `w = i/2` is `>= 2 - 100/99 > 1/480`).

## (b) Script output

```
$ date -u
Mon Oct  5 06:05:12 UTC 2026
$ lake build RBM3D.Universality.FreeConv RBM3D.Universality.FreeConvStability 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3333 jobs).
$ git rev-parse --short HEAD; git status --short | wc -l
23ab8ce        0
$ grep -cE "sorry|admit|native_decide|^ *axiom " FreeConv.lean FreeConvStability.lean
RBM3D/Universality/FreeConv.lean:0
RBM3D/Universality/FreeConvStability.lean:0
$ grep -cE "Z2|Fin 2|d = 2|\(W ?\* ?L\)|Zd|WL" FreeConv.lean FreeConvStability.lean
RBM3D/Universality/FreeConv.lean:0
RBM3D/Universality/FreeConvStability.lean:0
$ lake env lean ax.lean   (imports RBM3D, both new modules; #print axioms of each public declaration, then #assert_rbm_axioms)
RBM.Univ.freeConv_existsUnique : [propext, Classical.choice, Quot.sound]
RBM.Univ.freeConvST : [propext, Classical.choice, Quot.sound]
RBM.Univ.isFreeConv51_freeConvST : [propext, Classical.choice, Quot.sound]
RBM.Univ.exists_isFreeConv32 : [propext, Classical.choice, Quot.sound]
RBM.Univ.isFreeConv32_unique : [propext, Classical.choice, Quot.sound]
RBM.Univ.FreeConvStability.msc_tendsto_mE : [propext, Classical.choice, Quot.sound]
RBM.Univ.FreeConvStability.freeConv_stable_local : [propext, Classical.choice, Quot.sound]
RBM.Univ.FreeConvCheck.z0_im : [propext, Classical.choice, Quot.sound]
RBM.Univ.FreeConvCheck.z1_im : [propext, Classical.choice, Quot.sound]
axiom audit: 5317 theorems, 1883 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). All within [propext,  Classical.choice,  Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted. 

$ extract statements by script (awk, up to the first `:=`) from the new files and from `git show c9a24cf:...`; diff
-- freeConv_existsUnique  FreeConv.lean:639; vs RBM2D source: IDENTICAL
theorem freeConv_existsUnique {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    ∃! m : ℂ, 0 < m.im ∧
      m = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m)⁻¹ := by
-- freeConvST  FreeConv.lean:656; vs RBM2D source: IDENTICAL
noncomputable def freeConvST {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) (t : ℝ) : ℂ → ℂ :=
-- isFreeConv51_freeConvST  FreeConv.lean:660; vs RBM2D source: IDENTICAL
theorem isFreeConv51_freeConvST {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) : IsFreeConv32 v t (freeConvST v t) := by
-- exists_isFreeConv32  FreeConv.lean:671; vs RBM2D source: IDENTICAL
theorem exists_isFreeConv32 {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) {t : ℝ}
    (ht : 0 < t) : ∃ m : ℂ → ℂ, IsFreeConv32 v t m :=
-- isFreeConv32_unique  FreeConv.lean:676; vs RBM2D source: IDENTICAL
theorem isFreeConv32_unique {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) {t : ℝ}
    (ht : 0 < t) {m₁ m₂ : ℂ → ℂ} (h₁ : IsFreeConv32 v t m₁) (h₂ : IsFreeConv32 v t m₂)
    {z : ℂ} (hz : 0 < z.im) : m₁ z = m₂ z :=
-- FreeConvStability.msc_tendsto_mE  FreeConvStability.lean:223; vs RBM2D source: DIFFERS
theorem FreeConvStability.msc_tendsto_mE {E : ℝ} (hE : |E| < 2) :
    Tendsto (fun η : ℝ => msc ⟨E, η⟩) (𝓝[>] 0) (𝓝 (mE E)) := by
-- FreeConvStability.freeConv_stable_local  FreeConvStability.lean:748; vs RBM2D source: IDENTICAL
theorem FreeConvStability.freeConv_stable_local {κ : ℝ} (hκ : 0 < κ) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ {n}
    [Fintype n] [Nonempty n] (v : n → ℝ) (s t E₀ ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t →
    |E₀| ≤ 2 - κ → 0 ≤ ε → ε ≤ c₀ →
    (∀ w : ℂ, |w.re| ≤ min κ 1 / 16 → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * msc ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) →
    ∃ ρ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
      |ρ - rhoSC E₀| ≤ C₀ * ε ∧
      ∀ η ∈ Set.Ioc (0:ℝ) (1 / 4), ‖freeConvST v t ⟨0, η⟩ - msc ⟨E₀, η⟩‖ ≤ C₀ * ε := by
$ diff (source msc_tendsto_mE) (new msc_tendsto_mE)
2c2
<     Tendsto (fun η : ℝ => msc ⟨E, η⟩) (𝓝[>] 0) (𝓝 (spectralM E)) := by
---
>     Tendsto (fun η : ℝ => msc ⟨E, η⟩) (𝓝[>] 0) (𝓝 (mE E)) := by

$ compiled instances: every `example` of the two files, first line (all compile in the build above)
FreeConv.lean:697: example : ∃! m : ℂ, 0 < m.im ∧
FreeConv.lean:703: example : IsFreeConv32 v3 (1 / 2) (freeConvST v3 (1 / 2)) :=
FreeConv.lean:706: example : 0 < (freeConvST v3 (1 / 2) z0).im :=
FreeConv.lean:710: example : ∃ m : ℂ → ℂ, IsFreeConv32 v3 (1 / 2) m :=
FreeConv.lean:715: example : ∃ m : ℂ → ℂ, IsFreeConv32 v3 (1 / 2) m ∧ m z0 = freeConvST v3 (1 / 2) z0 := by
FreeConv.lean:729: example : ∃! m : ℂ, 0 < m.im ∧
FreeConv.lean:736: example : 0 < (freeConvST v0 (1 / 2) z1).im ∧
FreeConvStability.lean:774: example : Tendsto (fun η : ℝ => msc ⟨0, η⟩) (𝓝[>] 0) (𝓝 (mE 0)) ∧
FreeConvStability.lean:779: example : Tendsto (fun η : ℝ => msc ⟨1, η⟩) (𝓝[>] 0) (𝓝 (mE 1)) ∧
FreeConvStability.lean:785: example : ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ),
FreeConvStability.lean:800: example : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ),
FreeConvStability.lean:821: example : ¬ (∀ w : ℂ, |w.re| ≤ 1 / 16 → 1 / 240 * (1 / 240) / 4 ≤ w.im → w.im ≤ 1 / 2 →
$ the instance of freeConv_stable_local used (FreeConvStability.lean), full statement
example : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ),
    (∀ w : ℂ, |w.re| ≤ 1 / 16 → 1 / 240 * (1 / 240) / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - (Real.sqrt (239 / 240) : ℂ)⁻¹ *
        msc ((Real.sqrt (239 / 240) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ 1 / 480) →
    ∃ ρ : ℝ, Tendsto (fun η : ℝ => (freeConvST v (1 / 240) ⟨0, η⟩).im / Real.pi)
        (𝓝[>] 0) (𝓝 ρ) ∧
      |ρ - rhoSC 0| ≤ 2 * (1 / 480) ∧
      ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
        ‖freeConvST v (1 / 240) ⟨0, η⟩ - msc ⟨0, η⟩‖ ≤ 2 * (1 / 480) := by
$ the negative example (hyp is false at v = 0 on Fin 3), statement
example : ¬ (∀ w : ℂ, |w.re| ≤ 1 / 16 → 1 / 240 * (1 / 240) / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV (fun _ : Fin 3 => (0 : ℝ)) w - (Real.sqrt (239 / 240) : ℂ)⁻¹ *
        msc ((Real.sqrt (239 / 240) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ 1 / 480) := by

$ name clashes: git grep -n -w <name> main -- RBM3D RBM3D.lean, outside Universality/FreeConv*.lean
freeConv_existsUnique=0 freeConvST=0 isFreeConv51_freeConvST=0 exists_isFreeConv32=0 isFreeConv32_unique=0 msc_tendsto_mE=0 freeConv_stable_local=0 FreeConvCheck=0 FreeConvStabilityCheck=0 
FreeConvStability (namespace name) on main outside the new files:
main:RBM3D/Universality/Pins.lean:824:the limit `η ↓ 0`; RBM2D `Step1RegularityB_msc_im_ge`, `FreeConvStability` "contin
public declarations: RBM3D/Universality/FreeConv.lean:11 RBM3D/Universality/FreeConvStability.lean:2  ; private: 12 / 32

$ port diff: source body (after `noncomputable section`) with the rename rules applied, vs new body (negative example removed)
rules: R1 open RBM.Endpoints->RBM; R2 spectralM*->mE*; R3 fcs_msc_add_eq_neg_inv->msc_add_eq_neg_inv, fcs_lemT_ge->lemT_ge, fcs_rhoSC_eq_spectralM_im->fcs_rhoSC_eq_mE_im; R4 delete private fcs_norm_msc_pos, fcs_msc_add_eq_neg_inv, fcs_lemT_ge
FreeConvStability.lean: residual diff EMPTY after R1-R4 (negative example, 38 lines, is the only addition)
FreeConv.lean: diff of bodies (source vs new):
6c6
685a686,724
  (6c6 = R1; 685a686,724 = the added v0/z1 instances, 39 lines)

$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  ;  RBM2D source lines at c9a24cf
9e0f275
636:theorem freeConv_existsUnique {n : Type*} [Fintype n] [N
653:noncomputable def freeConvST {n : Type*} [Fintype n] [No
657:theorem isFreeConv51_freeConvST {n : Type*} [Fintype n] 
668:theorem exists_isFreeConv32 {ι : Type*} [Fintype ι] [Non
673:theorem isFreeConv32_unique {ι : Type*} [Fintype ι] [Non
240:theorem FreeConvStability.msc_tendsto_mE {E : ℝ} (hE : |E| < 2) :
765:theorem FreeConvStability.freeConv_stable_local {κ : ℝ} (hκ : 0 < 
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/FreeConv.lean RBM2D/Universality/FreeConvStability.lean
 RBM2D/Universality/FreeConv.lean          |  79 ++--------------------
 RBM2D/Universality/FreeConvStability.lean | 106 +++++++-----------------------
 2 files changed, 29 insertions(+), 156 deletions(-)
$ git -C ../RBM2D --no-optional-locks log --oneline c9a24cf..HEAD -- <the two files>
81fca44 T2276: merge comment clean-up (Universality, Main, Endpoints, small top-level modules)
99d6fe0 T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)
$ grep -c "exists_isFreeConv32\|isFreeConv32_unique" at RBM2D HEAD (FreeConv.lean, FreeConvStability.lean)
0
$ git diff --name-only main...t/T2176; git log --format="%h %an <%ae>" main..t/T2176
RBM3D/Universality/FreeConv.lean
RBM3D/Universality/FreeConvStability.lean
23ab8ce Jun Yin <321276894+JYin80@users.noreply.github.com>
$ (statements of the five RBM2D HEAD declarations vs the new files, scratch head.sh)
freeConv_existsUnique: same at RBM2D HEAD
freeConvST: same at RBM2D HEAD
isFreeConv51_freeConvST: same at RBM2D HEAD
FreeConvStability.freeConv_stable_local: same at RBM2D HEAD
FreeConvStability.msc_tendsto_mE: same at RBM2D HEAD (as source c9a24cf)
```

Narrative:
- Both files are copies of RBM2D `c9a24cf` (`FreeConv.lean` 719 lines, `FreeConvStability.lean` 835 lines) with the renamings R1-R4 above (the port diff block), the added import `Mathlib.Analysis.Real.Pi.Bounds` and the added instances; no other code change; the five ticket endpoints are IDENTICAL to the source (`msc_tendsto_mE` differs only by `spectralM` -> `mE`).
- No statement or proof depends on `d`: both source files quantify over an arbitrary finite nonempty index type; the grep for `Z2|Fin 2|d = 2|(W L)|Zd|WL` is 0 in the new files, so the ticket's stop condition (a statement depending on `d = 2` beyond tokens) is not triggered and no statement was changed.
- `IsFreeConv51` does not occur in the source: `isFreeConv51_freeConvST` is already stated against `IsFreeConv32` (`Pins.lean:249`), and `mV` is the merged `Pins.lean:237`.
- `RBM.Endpoints` does not exist in RBM3D: `open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints` became `open RBM RBM.Gauss RBM.Gauss.Sizes`.
- `Mathlib.Analysis.Real.Pi.Bounds` had to be imported in `FreeConvStability.lean`: the first build failed with "Unknown constant `Real.pi_gt_three`" (RBM2D reaches it through its own imports).
- The three private copies of `norm_msc_pos`, `msc_add_eq_neg_inv`, `lemT_ge` (private in RBM2D `Defs/Semicircle.lean`) are deleted; the public RBM3D versions (`Defs/Semicircle.lean:198,303,331`) have the same statements and are used.
- All RBM2D public names are kept, including `exists_isFreeConv32` and `isFreeConv32_unique` (present at `c9a24cf`; deleted from RBM2D HEAD by the dead-code ticket T2274, `99d6fe0`).
- RBM2D HEAD `9e0f275` differs from `c9a24cf` in these two files (diff stat above: comment clean-up T2276 and dead-code deletion T2274); the endpoint statements at HEAD equal the new files (last block above).
- Instances (every `example` listed above compiles in the build): `freeConv_existsUnique`, `freeConvST`, `isFreeConv51_freeConvST`, `exists_isFreeConv32`, `isFreeConv32_unique` at `Fin 3`, `v = (-1,0,1)`, `t = 1/2`, `z = i/10` (source instance) and at `v = 0`, `t = 1/2`, `z = 3/10 + i/2` (the ticket's data; `FreeConv.lean:729-736`, the second also proves the root is nonzero and solves `t m^2 + z m + 1 = 0`); `msc_tendsto_mE` at `E = 0` and `E = 1`.
- `freeConv_stable_local`: the instances at `kappa = 1`, `E0 = 0`, `t = c0` (and the literal `t = 1/240`, `eps = 1/480`) keep the closeness hypothesis `hyp` as the only undischarged hypothesis, with `v` and the index type universal (as RBM2D `FreeConvStabilityCheck`; `hyp` is another gate's input, supplied downstream by the local law). The ticket's `v = 0` on `Fin 3` cannot discharge `hyp`: `FreeConvStability.lean:821` proves the negation. A genuine witness needs the semicircle resolved down to `Im w = c0 t/4 ~ 4.3e-6` (preflight numerics: `N >~ 10^6`), which is not a Lean witness.
- Full `lake build` in the worktree completed (3961 jobs) but does not compile the new modules (root imports are the hub's); instead `ax.lean` imports `RBM3D` plus both modules and runs `#assert_rbm_axioms`: no error, 0 axioms.

## (c) Verified Mathlib names (`#check` in the worktree; scratch `chk.lean`)

- `Real.pi_gt_three : 3 < Real.pi` (`Mathlib/Analysis/Real/Pi/Bounds.lean:151`; with the imports `RBM3D.Universality.FreeConv`, `RBM3D.Defs.Semicircle`, `Mathlib.Analysis.Complex.Liouville`, `Mathlib.Topology.MetricSpace.Contracting` the first build reported it unknown; fixed by importing `Mathlib.Analysis.Real.Pi.Bounds`).
- `Real.le_sqrt_of_sq_le : x ^ 2 <= y -> x <= sqrt y`; `Complex.norm_real : ‖(r : C)‖ = ‖r‖`; `Real.norm_of_nonneg`; `Complex.norm_def : ‖z‖ = sqrt (normSq z)`.
- `inv_le_comm₀`, `inv_mul_cancel₀`, `norm_sub_norm_le : ‖a‖ - ‖b‖ <= ‖a - b‖`, `_root_.inv_zero` (`inv_zero` alone is ambiguous with `Matrix.inv_zero` under `open Matrix`).
- Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates

- Open: the ticket's instruction for `freeConv_stable_local` ("`v = 0` on `Fin 3`, all hypotheses discharged") is unsatisfiable as stated (negative example `FreeConvStability.lean:821`); the instance keeps `hyp`, as CLAUDE.md §4 step 2 allows for another gate's pin. Consumers (the `UNInfty1Row` regularity tickets, UN-07) must supply `hyp` with `c0 = min kappa 1 / 240` at scale `Im w >= c0 t / 4`.
- Open (observation): docstrings of both files still quote RBM1D/RBM2D ticket labels (`T2205`, `T2205-amend-1`, `DECISIONS §70`: `FreeConv.lean:26,667,681`, `FreeConvStability.lean:40,762,797`); they are historical text from the source, not RBM3D decisions.
- Paper-delta candidates: none. Both files are deterministic complex analysis around [32] (2.5) and its stability; no statement of the d >= 3 paper is restated, and no Lean statement differs from the RBM2D source beyond the `spectralM` -> `mE` renaming.

