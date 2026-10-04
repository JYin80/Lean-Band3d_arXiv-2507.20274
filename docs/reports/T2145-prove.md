Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 17:25 UTC 2026 (date -u)

### (i) Exponent table and the declarations to copy

Probe = `git show 7b2b789:RBM3D/Probe/T2134Pins.lean`; lines 482-1039 of it (namespace `RBM.Gauss.Sizes`, `variable {d} (sz)`) are already merged in `Step5Kit.lean` (T2143 audit §1: diff EMPTY) and `Step5Pins.lean`; every `st5_*` / `ST*` / `st_*` name the copied segment uses and does not define exists in `main` (grep over `RBM3D/`: `st5_prec_mono`, `st5_prec_cover`, `st5_Bctl_ge`, `st5_compare_I`, `st5_conStInd_mono`, `st5_t_lt_one`, ... in `Step5Kit`; `st5_reg5I_mid`, `STReg5II/Mid/III`, `STPfStep5`, `STStep5II/III`, `STtailTD` in `Step5Pins`; `st_Bctl_pos` `Step34Pins:680`; `detDom_log_pow`, `eventually_le_rpow`, `rpow_half_mul_rpow_half` `Defs/Domination`; `lam_sq_mul_pow_ge` `Defs/Sizes`). The 14 declarations below are in no file of `main` (grep `(theorem|lemma|def) <name>` over `RBM3D/`: no hit); all are to be copied, none skipped.

| Probe line | Declaration | Says |
|---|---|---|
| 1040 | header `### Case (iii)` | section comment (segment 1040-1702 opens inside `namespace RBM.Gauss.Sizes`; new file needs the header lines of probe 482-486) |
| 1043 | `st5_prec_mono'` | `ξ ≺ ζ₁`, `ζ₁ ≤ N^τ ζ₂` eventually for every `τ>0` gives `ξ ≺ ζ₂` (primed variant of merged `st5_prec_mono`, which has a constant `c`) |
| 1061 | `st5_one_add_log_pow_le` | `(1+log W)^m ≤ 2^{m+1} W^τ` eventually (`W→∞`, `τ>0`) |
| 1088 | `st5_ellT_one` | `ilambda² ≤ 1-u` implies `ℓ_u = 1` |
| 1104 | `st5_Bctl_ge_III` | `(2 W^d (1-u))⁻¹ ≤ Bctl n u` for `ilambda² ≤ 1-u` |
| 1124 | `st5_STWB_ge_III` | `(2W^d(1-u))⁻¹ (k+1)^{-(d-2)} ≤ STWB n u k` |
| 1150 | `st5_compare_IIIa` | `T_{u,D}(r) ≤ 4(Bctl² e^{-√r} + W^{-D})` (`(Eq:Gdecay+s<g_flow)`) |
| 1179 | `st5_compare_IIIb` | `T_{u,D}(r) ≤ 4(Bctl^{1/5} STWB e^{-(r/ℓ_u)^{1/2}} + W^{-D})` given `y=(W^d(1-u))⁻¹ ≤ 1` and `y^{4/5}((D log W)²+1)^{d-2} ≤ 1` |
| 1285 | `st5_polylog_le_W` | `((D log W)²+1)^{d-2} ≤ W^{8𝔡/5}` eventually |
| 1315 | `ST_step5_caseIII_of_pf` | `STPfStep5 d → STStep5III d` (`lem:pf_step5`) |
| 1410 | header `### Case (ii)` | section comment |
| 1413 | `st5_mE_im_ge` | `|E| ≤ 2-κ` implies `Im m(E) ≥ √(2κ)/2` |
| 1422 | `st5_A15_le` | `A^{-1/5} ≤ 2 Δ_u^{1/5}` for `1-u ≤ ilambda²`, `A = ilambda² W^d ≥ 1` |
| 1442 | `st5_compare_IIward` | `A⁻¹ (N η_u)⁻¹ ≤ (6/c) Δ^{1/5} STWB e^{-(r/ℓ_u)^{1/2}}` for `1-u ≤ ilambda²/L²`, `Im m ≥ c` |
| 1536 | `st5_reg5II_mid` | `STReg5II → STReg5Mid` (regime window) |
| 1546 | `ST_step5_caseII_of_pins` | `STEtermsMid ∧ STDuhamelII ∧ STIniTermII ∧ STWardII → STStep5II d` |
| 1702 | `end RBM.Gauss.Sizes` | closes the namespace |
| 2263-2272 | `inst_skeletonII`, `inst_skeletonIII` (`inst_skeletonI` merged, `Step5Kit:636`) | the two instances; namespace `T2134Inst` becomes `Step5Inst` |

Constants and exponents (d = 3, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠_d ≤ 1/100`; `N = (WL)^d`, `ℓ_u = min(max(ilambda/√|1-u|,1),L)`):

| Item | Value / constraint | Slack |
|---|---|---|
| III regime `ilambda_n² ≤ 1-t` | `sz0`: `ilambda_n = (2(n+1))^{-6}`, `t = 1/16` | `ilambda_0² = 1/4096 ≤ 15/16` |
| `(eq:WO)` `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡⁻¹` | `sz0`: `W^{-7/5} ≤ W^{-6/5}`, `ilambda ≤ 10` | factor `W^{1/5}` (n=0: `32^{1/5}≈2`) |
| Bandwidth `N^{1/6} ≤ W` | `N = (WL)^3 ≤ W^6` (`L ≤ W`) | exact when `L = W`; `sz0` has `L ≪ W` for `n ≥ 1` |
| `ℓ_u = 1` in III | needs `ilambda² ≤ 1-u` | none needed |
| Bctl ≥ `(2W^d(1-u))⁻¹`; `(W^d(1-u))^{-2} ≤ 4 Bctl²` | lower bound `Bctl ≥ 1/2 · (W^d(1-u))⁻¹` (zero-mode-free term only); squared: `1/4` | constant 4 = `(1/(1/2))²` |
| `y = (W^d(1-u))⁻¹ ≤ W^{-2𝔡}` | `ilambda² W^d ≥ W^{2𝔡}` from WO | `sz0`: `ilambda²W^3 = W^{3/5} ≥ W^{1/5}` |
| `hcond`: `y^{4/5}·polylog ≤ 1` | `y^{4/5} ≤ W^{-8𝔡/5}`; polylog `≤ W^{4𝔡/5}·W^{4𝔡/5}` | exponents match exactly (`-8𝔡/5 + 8𝔡/5 = 0`); room only in `∀ᶠ n` |
| `st5_polylog_le_W` threshold (`D=1,d=3,𝔡=1/10`) | holds for `n > 8206`, `W ≈ 1.2·10²¹` (script) | eventual statement; the instance's own `hcond` holds from `n = 0` (script) |
| loss exponent `C_d = 0` | no `((1-s)/(1-u))^{C_d}` factor | `(·)^{(0:ℝ)} = 1` |
| II regime `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²` | `szB` (`L=4, ilambda=1`), `(s,t)=(15/16,31/32)` | `1/64 ≤ 1/32 ≤ 1/16 ≤ 1/16` |
| `Im m(E) ≥ c = √(2κ)/2` | `√0.2/2 = 0.2236` | at `E(zB) = 0.499984`: `Im m = 0.9682` |
| `A^{-1/5} ≤ 2Δ^{1/5}` | `2^{1/5} ≤ 2`; `A = ilambda²W^3 ≥ 1` | `A_0 = 64` |
| Ward constant `6/c` | `ℓ_u = L = 4` for `1-u ≤ ilambda²/L²` | script: holds with margin at all points below |

### (ii) One concrete nondegenerate instance

Case (iii): the merged `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6}`), `z0 = 1/2 + i N^{-4/5}`, `(s,t) = (0,1/16)`, `u ∈ {0,1/32,1/16}`, `r ∈ {0,1,5,40}`, `D = 1`, `n ∈ {0,1,10,100,1000}`. Case (ii): merged `szB` (`L = 4`, `W_n = n+4`, `ilambda = 1`), `zB = 1/2 + i/64`, `u ∈ {15/16, 0.95, 31/32}`, `n ∈ {0,1,10,1000}`. The script checks every hypothesis of the six comparison lemmas at all points (regime, WO, bandwidth, `lemT ≥ t`, `|E| ≤ 2-κ`, `hy1`, `hcond`, `ℓ_u`) and each conclusion. The ingredient pins (`STPfStep5`, `STEtermsMid`, `STDuhamelII`, `STIniTermII`, `STWardII`) are the `example` hypotheses (other gates' pins, CLAUDE.md §4 step 2); the instances `inst_step5II/III` use the merged data (`szB_reg5II`, `sz0_reg5III`). The only limit input of the targets is `W_n → ∞` (`(2(n+1))^5`, `n+4`) and `N → ∞` (`SizeTendsto`), both explicit sequences.

```
$ python3 $SCRATCH/T2145/inst.py        # numeric check, d=3, κ=ε=𝔡=1/10, 𝔠=1/6 (no Lean)
n=0 W=32 L=4 lam=0.0156 N=2.1e+06 y(u=1/16)=3.26e-05 hcond=0.00334
n=1 W=1024 L=8 lam=0.000244 N=5.5e+11 y(u=1/16)=9.93e-10 hcond=3.08e-06
n=10 W=5.15363e+06 L=44 lam=8.82e-09 N=1.17e+25 y(u=1/16)=7.79e-21 hcond=1.96e-14
n=100 W=3.36323e+11 L=404 lam=1.47e-14 N=2.51e+42 y(u=1/16)=2.8e-35 hcond=1.61e-25
n=1000 W=3.21603e+16 L=4004 lam=1.55e-20 N=2.14e+60 y(u=1/16)=3.21e-50 hcond=3.67e-37
case III instance points checked: 60
polylog_le_W (D=1,d=3,dd=1/10): last failing n = 8206 (W=1.19e+21)
zB: E=0.499984 lemT=0.983992
Im mE=0.9682 c=0.2236
n=0 W=4 N=4096 A=64  ell(u=31/32)=4
n=1 W=5 N=8000 A=125  ell(u=31/32)=4
n=10 W=14 N=175616 A=2744  ell(u=31/32)=4
n=1000 W=1004 N=64771076096 A=1.01205e+09  ell(u=31/32)=4
case II instance points checked: 48
ALL OK
```

(`y(u=1/16)` is `(W^3 · 15/16)⁻¹`; `hcond` is `y^{4/5}((D log W)²+1)`; all at the printed `n`.)

### Verdicts

- Targets 1 (copy of probe `1040-1702`: case (iii) `ST_step5_caseIII_of_pf` and case (ii) `ST_step5_caseII_of_pins` with the deterministic comparisons): **PASS**. All hypotheses hold at the instance; exponents close (`8𝔡/5` exactly, `∀ᶠ` absorbs the logarithm); no declaration is already merged.
- Target 2 (`inst_skeletonII`, `inst_skeletonIII`): **PASS**; they use the merged `inst_step5II`, `inst_step5III` (`Step5Kit:603,608`) and `ST_step5_caseII_of_pins`, `ST_step5_caseIII_of_pf`.
- Note for stage 1b: the segment opens inside the namespace; the file must carry the header of probe lines 1-51/482-486 (imports `Induction.Step5Kit`; `noncomputable section`; `open MeasureTheory ProbabilityTheory Filter Matrix`; `open scoped NNReal ENNReal`; `namespace RBM.Gauss.Sizes`; `open RBM RBM.Loop RBM.Path RBM.Gauss`; `variable {d : ℕ} (sz : Sizes d)`). Probe `2255-2274` as named in the ticket starts inside the `inst_skeletonI` block; the two instances are at `2263-2272`.

## (b) Script output — Sun Oct  4 17:28 UTC 2026 (date -u)

Commit `27a8824` on `t/T2145` (worktree `RBM3D-wt/T2145`); only `RBM3D/Induction/Step5Cases.lean` (new, 717 lines). `RBM3D/Test/Axioms.lean` is unchanged (registry: no new premise, see below).

```
$ git diff --stat main...t/T2145
 RBM3D/Induction/Step5Cases.lean | 717 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 717 insertions(+)

$ lake build RBM3D.Induction.Step5Cases 2>&1 | tail -3
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3776 jobs).
```
(`lake env lean RBM3D/Induction/Step5Cases.lean` prints no warning or error).

Registry pre-check: `import RBM3D.Induction.Step5Cases` added temporarily after the last `import` line of `RBM3D.lean` (restored afterwards; `git status`: only the new file differs):
```
$ lake build | grep -E "axiom audit|registry:|premises found|Build completed|error|sorry"
info: RBM3D.lean:191:0: axiom audit: 4479 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 89 (borrowed 0, owed 69, structural 20).
registry: 1 borrowed + 91 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3892 jobs).
```
No unclassified premise; `STStep5II`, `STStep5III`, `STPfStep5`, `STEtermsMid`, `STDuhamelII`, `STIniTermII`, `STWardII` were already registered owed (`Test/Axioms.lean:167,168,170,172,174,175,182`), so no registry edit.

Axioms (`lake env lean` on a scratch file importing the module):
```
'RBM.Gauss.Sizes.ST_step5_caseIII_of_pf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step5_caseII_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st5_compare_IIIa' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st5_compare_IIIb' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st5_compare_IIward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.st5_reg5II_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_skeletonII' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_skeletonIII' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(the hub's full-build `#assert_rbm_axioms` covers every other declaration of the file; it passed above.)

Copied text against the probe (script diff, `S` = `git --no-optional-locks show 7b2b789:RBM3D/Probe/T2134Pins.lean`):
```
$ diff <(sed -n 36,698p RBM3D/Induction/Step5Cases.lean) <(S | sed -n 1040,1702p)
(empty)   EMPTY
$ diff <(sed -n 706,715p RBM3D/Induction/Step5Cases.lean) <(S | sed -n 2263,2272p)
(empty)   INST_EMPTY
```
Differences from the probe, all outside those ranges: file header/imports/docstring (lines 1-35, `import RBM3D.Induction.Step5Kit`, the three `open` lines, `namespace RBM.Gauss.Sizes`, `variable {d : ℕ} (sz : Sizes d)` as probe 482-486), and lines 699-705: `namespace RBM.Gauss.Step5Inst` with the `open` line of Step5Kit:593 (probe 1721 with `T2134Inst` renamed), heading `### The skeletons at the data`. No copied declaration was already merged (preflight grep), so none was skipped.

Target statements (extracted by script, `sed -n`):
```
311: theorem ST_step5_caseIII_of_pf (hPf : STPfStep5 d) : STStep5III d := by
542: theorem ST_step5_caseII_of_pins (hE : STEtermsMid d) (hD : STDuhamelII d) (hI : STIniTermII d) (hWd : STWardII d) :
543:     STStep5II d := by
```
Compiled nonempty instances (in the file, lines 706-715; both apply the target at the concrete merged data and use the merged `inst_step5II/III`; ingredient pins are hypotheses, being other gates' owed pins):
```
/-- Case (ii) from its ingredients, at `(szB, zB, 15/16, 31/32)`. -/
theorem inst_skeletonII (hE : STEtermsMid 3) (hD : STDuhamelII 3) (hI : STIniTermII 3) (hW : STWardII 3)
    (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step5II (ST_step5_caseII_of_pins hE hD hI hW) Cd hCd

/-- Case (iii) from `lem:pf_step5`, at `(sz0, z0, 0, 1/16)`. -/
theorem inst_skeletonIII (hPf : STPfStep5 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_step5III (ST_step5_caseIII_of_pf hPf) Cd hCd
```
Hygiene and name clash:
```
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/Step5Cases.lean
(no hit)
$ for each of the 16 public names in the file: grep -rlE "(theorem|lemma|def) <name>( |$)" RBM3D | grep -v Step5Cases
(no hit)
```
Ports: from the unmerged probe `7b2b789` only (`RBM3D/Probe/T2134Pins.lean`, RBM3D itself); nothing from `../RBM1D` or `../RBM2D`, so no diff-stat.

Narrative: the file is the header plus probe `1040-1702` plus the two skeleton instances; it compiled without change. Statements are unchanged from the probe; the only edit to copied material is `T2134Inst` to `Step5Inst` (in the instance namespace line).

## (c) Verified Mathlib names

None new: the file uses no Mathlib name that is not in the copied probe text (which compiles unchanged).

## (d) Open issues and paper-delta candidates

* No open issue; no stop condition of the ticket (a copied statement needing change) occurred.
* Registry: `STStep5II` and `STStep5III` stay owed; the pre-check required no new line.
* Paper-delta candidates: none new; D315-D324 (DECISIONS §40) cover `tailTD` and the registry classes.
