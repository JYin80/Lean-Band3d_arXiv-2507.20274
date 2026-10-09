Auditor model: claude-opus-5-5
# T2361 audit (round 1) — UN-50b `PathBounds` — Fri Oct  9 19:28:13 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2361-audit1`, detached at `f9cce14` (= `t/T2361`).
Source of the port: RBM2D `Universality/GUEPhase/PathBounds.lean` at `9e0f275` (`git -C ../RBM2D log -1` = `9e0f275`).
The ticket pins no statement text. It gives a port with a statement table, so each target is checked against the RBM2D statement, with the token map applied by a script, and against the ticket's points (i)–(vi).

## 1. Scope, build, axioms, hygiene
```
$ git diff --stat main...t/T2361
 RBM3D/Universality/GUEPhase/PathBounds.lean | 903 ++++++++++++++++++++++++++++
 1 file changed, 903 insertions(+)
$ lake build RBM3D.Universality.GUEPhase.PathBounds      (audit worktree; error lines / tail)
grep -c '^error' build.log -> 0 ; grep 'PathBounds.lean' build.log -> (none)
Build completed successfully (3825 jobs).
exit=0
$ lake env lean RBM3D/Universality/GUEPhase/PathBounds.lean ; echo exit=$? ; wc -l <output>
exit=0
       0
$ lake env lean ax.lean     (import RBM3D.Universality.GUEPhase.PathBounds; #print axioms ×3)
'RBM.Univ.GUEPhase.gueBds_h745E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueBds_h746' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueGrid_pathBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE 'sorry|admit|native_decide|^\s*axiom|set_option|implemented_by|unsafe|opaque' PathBounds.lean
56:set_option linter.style.longLine false
57:set_option linter.unusedSectionVars false
$ grep -n import PathBounds.lean
6:import RBM3D.Universality.GUEPhase.HypB    7: ...BoundsA   8: ...DuhamelC   9: ...EntryGrid
10:import RBM3D.Universality.GUEPhase.BootstrapAt   11:import RBM3D.Universality.GUEPhase.ProcK
```
The file is new, so no frozen signature is touched. It does not use `import RBM3D`. `ProcK` is used by `gueKproc_detDom`/`gueK_exists`, and the ticket's check file imports it too. Only linter options are set.

## 2. Statements against the RBM2D source (script `sigdiff.py`)
The script applies the token map (`d.`→`sz.`, `Z2`→`Zd d`, `Pgue/gueScale/gueGridK/gueDelta/gue?proc/GUEPathBounds d`→`… sz`, `primRhsGUE (`→`primRhsGUE d (`), splits each signature at its hypotheses and diffs them.
```
=== gueBds_h745E
-theorem gueBds_h745E {𝔠 κ τU : ℝ}
- (h𝔠 : 0 < 𝔠)
- (hadm : RBM.Endpoints.Admissible 𝔠 d)
+theorem gueBds_h745E
+ (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ}
+ (hadm : sz.Admissible 𝔠 𝔡)
- (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
+ (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
+ (hKb : sz.STKbound E)
- (hKinit : ∀ n I, Kt n (t1 n) I = KLoop.Kcal (sz.L n) (sz.W n) (E n) (t1 n) I)
+ (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
- (hB : RBM.Ind.MLConcl d E t1) : …
+ (hLK : sz.STLK E t1) : …
=== gueBds_h746
-theorem gueBds_h746 {κ τU : ℝ}
- (hsz : Tendsto (fun n => sz.size n) atTop atTop)
+theorem gueBds_h746 {𝔠 𝔡 κ τU : ℝ}
+ (hadm : sz.Admissible 𝔠 𝔡)
- (hell : … ^ 2 * (1 - t1 n) ≤ 1)        + (hell : … ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
+ (hKb : sz.STKbound E)
- (hKinit : ∀ n I, … KLoop.Kcal …)       + (hKinit : ∀ n {k} σ a, … (loopOf σ a) = sz.STKloop …)
- (hB : RBM.Ind.MLConcl d E t1) : …      + (hLK : sz.STLK E t1) : …
=== gueGrid_pathBounds
-theorem gueGrid_pathBounds {𝔠 κ τU : ℝ}
- (h𝔠 : 0 < 𝔠)
- (hadm : RBM.Endpoints.Admissible 𝔠 d)
+theorem gueGrid_pathBounds
+ (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ}
+ (hadm : sz.Admissible 𝔠 𝔡)
- (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - t1 n) ≤ 1)
+ (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
+ (hell1 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1)
+ (hKb : sz.STKbound E)
- (hKinit : …)                            + (hKinit : … loopOf σ a … STKloop …)
- (hB : RBM.Ind.MLConcl d E t1) : GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt := by
+ (hLK : sz.STLK E t1)
+ (hLoc : sz.STLocalEntry E t1) : GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt := by
--- conclusions (after the last hypothesis) equal after token map?
gueBds_h745E True
gueBds_h746 True
gueGrid_pathBounds True
```
All other hypotheses (`hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hK`) are the same after the token map, in the same order. The conclusions are textually identical.

Line-by-line check against the ticket's statement points:
* **(i) `hB` ↦ `hLK`, `hLoc`.** The source uses only `hB.1.1` (InitLK) and `hB.1.2.2` (InitLocal). `STLK` and `STLocalEntry` (`#print` below) are exactly two conjuncts of `UNMLOut` (`Pins.lean:432`). The conversion to the step-0 inputs is proved inside the file by `PathBounds_Bctl_le` (hyp. `hell`, gives `Bctl ≤ 2 (N η)⁻¹`), `PathBounds_STWB_le`, `PathBounds_init_loops` and `PathBounds_init_local`, all compiled. No FAIL. Only the conjuncts that are needed are consumed.
* **(ii)** `hell` (`L^d(1-t₁) ≤ ilambda²`), `hKb : sz.STKbound E`, and `hKinit` on `loopOf σ a` with `STKloop` match the merged `Hyp_Kt_detDom` signature (`#check`, ax.lean) hypothesis for hypothesis. This is already delta D631 (T2352a).
* **(iii)** The `∀ n` facts `hE ht1 ht10 ht0` stay hypotheses, as in the source.
* **Admissible.** The `Endpoints.Admissible 𝔠 d` and `h𝔠` of `h745E`/main become `sz.Admissible 𝔠 𝔡 = 0<𝔠 ∧ 0<𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 ∧ WO 𝔡` (`Defs/Sizes.lean:177`), which is the paper's standing hypothesis (`1_2:357-363`). In `h746`, `hsz` is strengthened to `hadm`, because `hbig` of the merged `HypB_fixed` carries `A = 1+2 ilambda²` and needs `ilambda ≤ 𝔡⁻¹` (`PathBounds_lam_bd`, `:307`). Proposed as T2361c.
* **`hell1` (main theorem only).** The merged `Bounds_path` (`#check` in ax.lean) takes `↑(sz.L n) ^ d * (1 - t1 n) ≤ 1` at each `n`. `(eq:WO)` allows `ilambda ≤ 𝔡⁻¹ > 1`, so `hell` does not imply it. `hell1` is the literal d ≥ 3 form of the source's own `hell` (`L²(1−t₁) ≤ 1`). It is consistent with the paper's footnote (`1_2:372`, "replace `ilambda` by `ilambda ∧ 1`"). It is a deterministic hypothesis, discharged in the instance (§4), and proposed as T2361b. Limit check in §3.

## 3. Hidden hypotheses, vacuity, cycles, external inputs
```
$ #print RBM.Gauss.Sizes.STLK / STLocalEntry ; #print GUEPathBounds   (ax.lean, abridged)
def STLK  := fun sz E τ => ∀ k, 1 ≤ k → sz.Prec (‖sz.Lloop … - sz.STKloop …‖) (sz.Bctl n (τ n) ^ k)
def STLocalEntry := fun sz E τ => sz.Prec (‖sz.STGM … ω p.1 p.2‖ ^ 2) (sz.STWB n (τ n) (zdistInf …))
structure GUEPathBounds … : Prop   fields: lk (∀ m, 1 ≤ m → m ≤ n0 → StochDomAt … (gueScale)⁻¹ ^ m),
                                           localLaw (StochDomAt … (gueScale)⁻¹ ^ (1/2))
def STKbound (Induction/Defs.lean:174) := ∀ τ, (0 ≤ τ) → (τ < 1) → ∀ k ≥ 1, Prec ‖STKloop‖ ≺ Bctl^(k-1)
```
* No hypothesis hides in a structure field. `GUEPathBounds` is the conclusion. `Admissible` and `STKbound` are plain `Prop` definitions whose content is listed above.
* There is no cycle. All dependencies (`HypB`, `BoundsA`, `DuhamelC`, `EntryGrid`, `BootstrapAt`, `ProcK`) are merged on `main`, and the diff adds one file only.
* External inputs: `hLK` and `hLoc` are the conclusions of the owed pin `UNMLOut` (ST-6), so they may stay hypotheses. The preflight gives the limit check: at k = 1, `N η_{t₁} Bctl(t₁) = 1 + L^d x/(lam²+x)`, which is 1.19, 1.02, 1.0002 at n = 0, 1, 10 and tends to 1. So the scales agree. The audit's own limit check of the new deterministic `hell1` in the consumer regime (`1−t₀ = N^{-1+2τU}`, `t₀−t₁ = N^{-τU}(1−t₀)/2`, `sz0`) follows.
```
$ python3 lim.py
n | N | L^3(1-t1) [hell1, <=1] | L^3(1-t1)/lam^2 [hell, <=1] | consumer window 1-t0=N^(-1+2tU), t0-t1=N^(-tU)(1-t0)/2
0 2.09715e+6 4.69016e-5 0.192109
1 5.49756e+11 1.46148e-9 0.0245196
10 1.166e+25 1.20695e-20 0.000155153
1000 2.13522e+60 5.69634e-50 2.36137e-10
1000000 2.09719e+114 7.15173e-95 2.92938e-19
```
In general `L^d(1−t₁) ≍ N^{2τU} W^{-d} ≤ N^{2τU − d𝔠} → 0`. So `hell1` holds in the GUE-phase regime and is not vacuous.

## 4. Compiled nonempty instances (`PathBoundsInst`, same file, lines 669-899)
```
$ sed -n 687,691p ; grep exists_Kt/hKb0 (abridged)
private def Ei : ℕ → ℝ := fun _ => 0
private def yy (n : ℕ) : ℝ := sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3
private def tw1 (n : ℕ) : ℝ := 1 - yy n
private def tw0 (n : ℕ) : ℝ := 1 - yy n * Nn n / (Nn n + 1)
exists_Kt : from RBM.Univ.GUEPhase.gueK_exists 3 (sz0.L n) (sz0.W n) … (tw1_nonneg n) (tw1_le_tw0 n) (tw0_lt_one n) (4*2)
hKb0 : sz0.STKbound Ei := Sizes.stKbound_holds sz0 (le_refl 3) (κ := 1/10) (gmax := 1) …
$ sed -n 893,899p
example (hLK : sz0.STLK Ei tw1) (hLoc : sz0.STLocalEntry Ei tw1) :
    GUEPathBounds sz0 Ei tw1 tw0 (gueGridK sz0 2) 2 Kt0 :=
  gueGrid_pathBounds sz0 (le_refl 3) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at)
    (Eventually.of_forall hell1_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK hLoc
```
The examples for `gueBds_h745E` (`:878`) and `gueBds_h746` (`:885`) use the same arguments without `hell1`/`hLoc`. All three compile (build exit 0, 0 messages).

The data are nondegenerate:
* d = 3, n₀ = 2, `N(0) = 2097152`, L = 4, W = 32, `ilambda = 1/64`, E = 0.
* Window at n = 0: `1−t₁ = 3.81e-6`, `t₀−t₁ = 1.8e-12 > 0` (`yy_pos`), `0 ≤ t₁ ≤ t₀ < 1`.
* `Kt0` comes from the merged `gueK_exists` (the true K-loops, not a stub).

Every deterministic hypothesis is discharged (`hadm hκ hτU hn0 hE ht1 ht10 ht0 h730 hscale hell hell1 hKb hKinit hK`). Only the other-gate pins `hLK` and `hLoc` stay hypotheses, as the rules allow. This is the instance the ticket asked for, on the `Grid.lean` §`GridCheck` sizes (`sz0`).

## 5. Paper deltas
The prove report (d) proposes T2361a (`MLConcl` ↦ `hLK`, `hLoc`; `scaleM` ↦ the `Bctl ≤ 2(Nη)⁻¹` inequality), T2361b (`hell1`) and T2361c (`Admissible`/`hd`, `hsz` ↦ `hadm` in `h746`, `hKb`, `hKinit`, `hell`).
The `hell`/`hKb`/`hKinit` changes are also already D631 (T2352a, `docs/paper-deltas.md:1590`). Every statement difference in §2 is covered.

## 6. Observations (no RETURN)
* O1. The main theorem has the extra hypothesis `hell1`, which a consumer (UN-51) must supply. It is redundant when `ilambda ≤ 1`, and §3 shows it holds in the GUE regime. The dispatcher may later want a primed `Bounds_path` with `≤ ilambda² ∧ 1`, but this is not a defect here.
* O2. `UNMLOut` gives `STLK`/`STLocalEntry` at `STflowE z` and times `t ≤ lemT z`. The consumer must match `(E, t₁)` to that form (prove report Open 1).

## Verdicts
`gueBds_h745E` **PASS**; `gueBds_h746` **PASS**; `gueGrid_pathBounds` **PASS**. Ticket T2361: **PASS**. No dispatcher sign-off is needed.
