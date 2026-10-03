Auditor model: claude-opus-5-5
# T2012 audit (round 1) — Sat Oct  3 02:05:19 UTC 2026
Branch `t/T2012` at `7d75f54` (merge-base `c950f27`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2012-audit1` (detached).
`$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`.

## 1. Statements
### Target 1: pinned block against the probe (`5d2a4a8`, lines 795–881 + 891–935; `LocalLawPT` = 882–890 excluded)
```
$ git show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean > $S/probe.lean; git show t/T2012:RBM3D/Defs/StochDomAt.lean > $S/sda.lean
$ (sed -n '795,881p' probe.lean; sed -n '891,935p' probe.lean) > pin_probe.txt; sed -n '43,174p' sda.lean > pin_file.txt
$ diff pin_probe.txt pin_file.txt; echo "diff exit=$?"; wc -l < pin_probe.txt
diff exit=0
     132
$ grep -n LocalLawPT sda.lean
21:  `RBM3D/Probe/T2002Vocab.lean` at `5d2a4a8`, lines 795–935, without `LocalLawPT`): `badSetAt`,
```
(Only a module-doc mention; no declaration.) Key pinned shapes, verbatim from the file:
```
def StochDomAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
    P (badSetAt size ξ ζ τ l) ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))
def Prec (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := StochDomAt (seqP sz) sz.size ξ ζ
```
Quantifier order (τ, D before `∀ᶠ l`), scale `size l = sz.size n = (W L)^d`, union over `u` inside `P` for `StochDomAt`, outside for `PerTimeDomAt`: as pinned.

### Target 2: ports against RBM2D `c9a24cf` (own script `$S/aud_cmp.py`: statement text up to `:=`, whitespace-normalised)
```
$ python3 aud_cmp.py r2_Path_PerTime.lean sda.lean PerTimeOfStochDomAt,perTimeOfStochDomAt,perTimeDomAt_iff_forall_section,stochDomAt_of_perTimeDomAt,highProbAt_iInter
PerTimeOfStochDomAt:55 -> PerTimeOfStochDomAt:189 SAME
perTimeOfStochDomAt:60 -> perTimeOfStochDomAt:195 SAME
perTimeDomAt_iff_forall_section:77 -> perTimeDomAt_iff_forall_section:213 SAME
stochDomAt_of_perTimeDomAt:112 -> stochDomAt_of_perTimeDomAt:249 SAME
highProbAt_iInter:141 -> highProbAt_iInter:279 SAME
$ python3 aud_cmp.py r2_Gauss_Domination.lean dat.lean MomentDomAt,stochDomAt_of_momentDomAt,highProbAt_univ,stochDomAt_Icc_of_holder_on_good,momentDomAt_constant_one_example
MomentDomAt:162 -> MomentDomAt:66 SAME
stochDomAt_of_momentDomAt:171 -> stochDomAt_of_momentDomAt:75 SAME
highProbAt_univ:467 -> highProbAt_univ:160 SAME
stochDomAt_Icc_of_holder_on_good:474 -> stochDomAt_Icc_of_holder_on_good:167 SAME
momentDomAt_constant_one_example:649 -> momentDomAt_constant_one_example:295 SAME
$ python3 aud_cmp.py r2_Gauss_MomentBridge.lean dat.lean integrable_abs_evenPow_of_envelope,momentDomAt_of_stochDomAt
integrable_abs_evenPow_of_envelope:29 -> integrable_abs_evenPow_of_envelope:314 SAME
momentDomAt_of_stochDomAt:170 -> momentDomAt_of_stochDomAt:328 SAME
$ python3 aud_cmp.py r2_Gauss_SteinMatrix.lean dat.lean Sample,law,law_pi,map_update,stein
Sample:29 -> Sample:497 SAME / law:32 -> law:500 SAME / law_pi:83 -> law_pi:509 SAME / stein:134 -> stein:559 SAME
map_update:91 -> map_update:517 DIFF
   R2: ... ((law v).prod (gaussianReal 0 (v c))).map (update c) = law v
   R3: ... ((law v).prod (gaussianReal 0 (v c))).map (upd c) = law v
```
`update` vs `upd` are the same function:
```
RBM2D SteinMatrix.lean:51  noncomputable def update (c : ι) (p : Sample ι × ℝ) : Sample ι := Function.update p.1 c p.2
main:RBM3D/Gauss/SteinMatrix.lean:70:def upd (c : ι) (p : (ι → ℝ) × ℝ) : ι → ℝ := Function.update p.1 c p.2
```
Calculus at scale (RBM2D has only index-scale `StochDom.*`; prove-report F1, confirmed by the grep in (a)). Side by side (excerpt of own extraction):
```
trans R2 202 theorem trans (h₁ : StochDom P ξ ζ) (h₂ : StochDom P ζ χ) : StochDom P ξ χ
trans R3 411 theorem trans (hsize : Tendsto size atTop atTop) (h₁ : StochDomAt P size ξ ζ) (h₂ : StochDomAt P size ζ χ) : StochDomAt P size ξ χ
mul R2 225 theorem mul (hξ₂ : ∀ N u ω, 0 ≤ ξ₂ N u ω) (hζ₁ : ∀ N u ω, 0 ≤ ζ₁ N u ω) (h₁ : StochDom P ξ₁ ζ₁) (h₂ : StochDom P ξ₂ ζ₂) : StochDom P (ξ₁ * ξ₂) (ζ₁ * ζ₂)
mul R3 439 theorem mul (hsize : Tendsto size atTop atTop) (hξ₂ : ∀ l u ω, 0 ≤ ξ₂ l u ω) (hζ₁ : ∀ l u ω, 0 ≤ ζ₁ l u ω) (h₁ : StochDomAt P size ξ₁ ζ₁) (h₂ : StochDomAt P size ξ₂ ζ₂) : StochDomAt P size (ξ₁ * ξ₂) (ζ₁ * ζ₂)
of_forall_le R3 507 theorem of_forall_le (hsize : Tendsto size atTop atTop) [∀ l, Fintype (U l)] {C : ℝ} (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ C) (h : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u, P {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))) : StochDomAt P size ξ ζ
of_unifDetDom R2 183 theorem of_unifDetDom {f g : ∀ N, U N → ℝ} (h : UnifDetDom f g) : StochDom P (fun N u _ => f N u) (fun N u _ => g N u)
of_unifDetDom R3 387 theorem of_unifDetDom {f g : ∀ l, U l → ℝ} (hl : ∀ᶠ l : ℕ in atTop, l ≤ size l) (hg : ∀ l u, 0 ≤ g l u) (h : UnifDetDom f g) : StochDomAt P size (fun l u _ => f l u) (fun l u _ => g l u)
of_add_le R3 669 theorem StochDomAt.of_add_le (hsize : Tendsto size atTop atTop) {b : ℝ} {ε : ℕ → ℝ} (hlow : ∀ᶠ l : ℕ in atTop, ∀ u ω, (size l : ℝ) ^ (-b) ≤ ζ l u ω) (hε : ∀ᶠ l : ℕ in atTop, ε l ≤ (size l : ℝ) ^ (-b)) (h : StochDomAt P size ξ (fun l u ω => ζ l u ω + ε l)) : StochDomAt P size ξ ζ
```
`refl, add, const_mul_left/right, of_subset_union, highProb` checked the same way: RBM2D statement with `N := size l`, `StochDom P := StochDomAt P size`, plus `hsize` where the union step `2N^{-(D+1)} ≤ N^{-D}` needs `N ≥ 2` (table (a) row "union"); `highProb` carries no `hsize`. `hsize` is a genuine requirement (fails for bounded `size`) and is discharged at `sz0` by `Sizes.tendsto_size sz0 sz0_tendsto`; signed delta D20 (`N → ∞`) covers it. `of_unifDetDom` adds `l ≤ size l` eventually and `0 ≤ g` (needed to pass `l^τ g ≤ (size l)^τ g`): proposed T2012b.
Not ported, with evidence: RBM2D `Gauss/Envelope.lean` at `c9a24cf` has no size/StochDom statement (`grep -cE "size|StochDom|HighProb|MomentDom"` → `0`); `momentDom_green_of_stochDom` (MomentBridge:325) needs `green`, absent on `main`. Index-scale items already merged are not re-declared.

## 2. Vacuity, hidden hypotheses, cycles
No `structure`/`class` is introduced (declaration list of both files: only `def`/`abbrev`/`theorem`/`instance`/`example`; the one `instance` is `IsProbabilityMeasure (law v)`, proved). Hypotheses are explicit binders. Dependencies are merged modules (`RBM3D.Gauss.FineModel`, `RBM3D.Defs.StochDom`, `Gauss/SteinMatrix` etc.) only; no external input. `PerTimeOfStochDomAt : Prop` is proved by `perTimeOfStochDomAt`, not assumed.

## 3. Compiled nonempty instances (all at `sz0`: `d = 3`, `N_0 = 2097152`, on `seqP sz0`; `obs n = |sin ω_{(n,0,0,re)}|`, nonconstant by `obs_nonconst`)
```
theorem prec_Xi_Ze : sz0.Prec Xi Ze :=                                         -- prec_of_le
  Sizes.prec_of_le sz0 Ze_nonneg fun n u ω => by unfold Xi Ze; linarith [obs_nonneg n ω]
theorem stochDomAt_Xi_Ch : StochDomAt (seqP sz0) sz0.size Xi Ch :=             -- StochDomAt.trans
  StochDomAt.trans tendsto_sz0_size prec_Xi_Ze prec_Ze_Ch
theorem stochDomAt_id_Ze : StochDomAt (seqP sz0) id Ze Ze :=                   -- stochDom_iff_at_id (→)
  (stochDom_iff_at_id (seqP sz0) Ze Ze).mp (StochDom.refl Ze_nonneg)
theorem stochDom_Ze : StochDom (seqP sz0) Ze Ze :=                             -- stochDom_iff_at_id (←)
  (stochDom_iff_at_id (seqP sz0) Ze Ze).mpr (StochDomAt.refl tendsto_id Ze_nonneg)
theorem stochDomAt_obs_of_moment : ... := stochDomAt_of_momentDomAt sz0.size tendsto_sz0_size (Ccard := 0) ... momentDomAt_obs
theorem momentDomAt_obs_of_dom : ... := momentDomAt_of_stochDomAt sz0.size tendsto_sz0_size (Env := fun _ => 1) (Kenv := 0) (B := 0) ...
theorem stochDomAt_Icc_Yt : ... := stochDomAt_Icc_of_holder_on_good sz0.size tendsto_sz0_size (T := 1) ... (Y := Yt) ...   -- Y_n(u) = u·obs n
theorem stein_sin_seqP : ∫ ω, ω c0 • ↑(sin (ω c0)) ∂(seqP sz0) = (seqGvar sz0 c0 : ℝ) • ∫ ω, ↑(cos (ω c0)) ∂(seqP sz0)   -- gvar_c0_pos
```
Every deterministic hypothesis is discharged; no `N = 0`, empty index (`Unit`, `Fin 2`, `Icc 0 1`) or `False` premise; `Tendsto sz0.size` from merged `sz0_tendsto`. The three instances required by the ticket are present and compile (build below).

## 4. Build, axioms, hygiene, diff
```
$ cd RBM3D-wt/T2012-audit1 && lake build RBM3D.Defs.StochDomAt RBM3D.Gauss.DominationAt
Build completed successfully (3248 jobs).        # grep -ci warning on the log: 0
$ lake env lean $S/aud_ax.lean      # collectAxioms over every non-internal constant of the two modules
declarations scanned: 129; axioms used overall: [Quot.sound, Classical.choice, propext]; outside the standard three: []
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option.*(debug|trust)|@\[implemented_by|unsafe" RBM3D/Defs/StochDomAt.lean RBM3D/Gauss/DominationAt.lean; echo "grep exit=$?"
grep exit=1
$ lake env lean $S/aud_root.lean    # RBM3D.lean imports + the two modules, then #assert_rbm_axioms
axiom audit: 829 theorems, 305 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 14 (borrowed 5, owed 1, structural 8).
$ lake env lean $S/aud_clash.lean   # import RBM3D + both modules: no duplicate-declaration error
@RBM.StochDomAt.trans : ... Filter.Tendsto size Filter.atTop Filter.atTop → RBM.StochDomAt P size ξ ζ → RBM.StochDomAt P size ζ χ → RBM.StochDomAt P size ξ χ
$ git diff --stat main...t/T2012
 RBM3D/Defs/StochDomAt.lean    | 997 ++++
 RBM3D/Gauss/DominationAt.lean | 849 ++++
 RBM3D/Test/Axioms.lean        |   2 +
$ git diff main...t/T2012 -- RBM3D/Test/Axioms.lean | grep '^+ '
+   `RBM.NormStochDomAt,       -- notation of `(stoch_domination)` at scale `N`
+   `RBM.Path.PerTimeDomAt,    -- notation of `(stoch_domination)` at scale `N`
$ git diff --stat c950f27 main -- RBM3D RBM3D.lean     # main moved since the branch point
 RBM3D.lean                         |   1 +
 RBM3D/Propagator/HeatBounds1D.lean | 871 ++++   (namespace RBM.Heat: no overlap)
```
Only sole writable files touched; `Test/Axioms.lean` change is exactly the two registry lines DECISIONS §16 permits. No frozen signature edited (no existing file other than `Test/Axioms.lean` changed).

## 5. Paper deltas
- `hsize : Tendsto size atTop atTop` on the calculus / bridges: signed D20 (docs/paper-deltas.md:223).
- Per-time `≺` with union outside `P`: signed D21 (:228). `W^τ` written `N^τ`: signed D23 (:241).
- Arbitrary measure, real-valued families, no sign condition in the definitions: candidate T2012a.
- `StochDomAt.of_unifDetDom` scale change (`l ≤ size l`, `0 ≤ g`): candidate T2012b.
All Lean/paper differences found above are covered.

## Verdicts
- Target 1 (pinned section 7 without `LocalLawPT`): **PASS**.
- Target 2, `Defs/StochDomAt.lean` (PerTime port; `StochDomAt`/`HighProbAt` calculus at scale; Absorb; `NormStochDomAt`): **PASS**.
- Target 2, `Gauss/DominationAt.lean` (`*At` Domination, MomentBridge, countable-product Stein): **PASS**.
- Axiom registry edit (`Test/Axioms.lean`): **PASS**.
**Overall: PASS.** No dispatcher sign-off needed.

## Observations (no verdict effect)
- O1. The ticket's "sequence-level part of `RBM2D/Gauss/Envelope.lean`" is empty at `c9a24cf` (grep count 0); the portmap row should be corrected by the dispatcher.
- O2. `stochDomAt_Icc_Yt` uses the good event `Ξ = univ` and `K = 0`: a valid nondegenerate instance (random `Y`), but it does not exercise a nontrivial good event.
- O3. `momentDom_green_of_stochDom` and an at-scale deterministic-modulus time net are not ported (listed in prove report (d)); downstream MD-4 should check whether it needs them.
