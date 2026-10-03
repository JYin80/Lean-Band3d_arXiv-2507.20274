Auditor model: claude-opus-5-5

# T2088 audit (round 1): S1-19, `Green/IBPPoly` (`gaussIBP`, `stochDom_ldeQuad`)

Written Sat Oct  3 23:11:36 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2088-audit1`, detached at `t/T2088` = `6a1e786`. Scratch: `scratchpad/T2088/`.

## 1. Statements against the pins

Target T1 `gaussIBP`. Pin: type exactly `RBM.Green.GaussIBP sz` for every `sz : Sizes d` (`Green/LDEQuad.lean:302`, owed registry line `Test/Axioms.lean:90`).
```
$ grep -n "^theorem gaussIBP\|structure GaussIBP" RBM3D/Green/IBPPoly.lean
305:theorem gaussIBP (sz : Sizes d) : GaussIBP sz := by
```
No local `structure GaussIBP` in the file (grep above), so `GaussIBP` resolves to the merged `RBM.Green.GaussIBP` (file is in `namespace RBM.Green`). No hypotheses besides `sz`. Its `stein` field uses `Sizes.seqGvar sz c`:
```
RBM3D/Gauss/FineModel.lean:164:def seqGvar (c : SeqCoord sz) : ℝ≥0 := gvarF d (sz.L c.1) (sz.W c.1) (sz.lam c.1) c.2
RBM3D/Gauss/FineModel.lean:169:def seqP : Measure (SeqΩ sz) := Measure.infinitePi fun c => gaussianReal 0 (seqGvar sz c)
```
= the ticket's `gvarF d L W g c` (the `d`-dimensional profile, not RBM2D's `1/(5W²)`). **T1 statement: PASS.**

Target T2 `stochDom_ldeQuad`. Pin: the `hLquad` hypothesis text of `diag_bound_stochDom` (`Green/EntryDom.lean:1010-1015`), which it must feed.
```
$ sed -n 1010,1015p RBM3D/Green/EntryDom.lean | tr -s ' \n' ' ' | sed 's/^ *(hLquad : //; s/) *$//' > pin.txt
$ awk '/^theorem stochDom_ldeQuad /{p=1} p{print} /:= by/{if(p)exit}' RBM3D/Green/IBPPoly.lean | sed -n '3,$p' \
    | tr -s ' \n' ' ' | sed 's/^ *//; s/ := by *$//' > lean.txt
$ cmp pin.txt lean.txt && echo "conclusion == hLquad text: IDENTICAL"
conclusion == hLquad text: IDENTICAL
$ awk ... | head -3
theorem stochDom_ldeQuad (sz : Sizes d) {κ : ℝ} (hκ : 0 < κ) (hsz : sz.SizeTendsto)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
```
Hypotheses `hκ, hE, ht0, ht1` are the same as `diag_bound_stochDom`'s (`EntryDom.lean:997-998`); the only extra one is `hsz : sz.SizeTendsto` (`Defs/Sizes.lean:173`, `N = (WL)^d → ∞`), with no `3 ≤ d`, no `𝔠, 𝔡`. Fixed parameters come before the `∀ᶠ n` inside `PrecPT`.

Against RBM2D at `c9a24cf` (ST1-COMMON item 6), after the listed renames R1, `RBM.Ind.SizeTendsto d → sz.SizeTendsto`, `PerTimeDomAt (Sizes.seqP d) d.size → sz.PrecPT` (`Defs/StochDomAt.lean:125` is that def), `BlockIndex → Vtx d`, `Sblk2 L W → svar d L W (sz.lam n)`:
```
$ diff <(rename-normalised RBM2D LDEQuadInst.lean:641 statement) <(RBM3D statement) && echo ...
RBM2D stochDom_ldeQuad (after listed renames) == RBM3D: IDENTICAL
```
**T2 statement: PASS.**

Other ported public declarations (name lists by script, RBM2D `IBPPoly` + `LDEQuadInst` at `c9a24cf` vs RBM3D file):
```
in RBM2D not RBM3D:
in RBM3D not RBM2D:
gaussIBP_sz0_polyInt  gaussIBP_sz0_stein_cubic  hwConst_two  seqGvar_sz0_c0  seqGvar_sz0_c0_pos  stochDom_ldeQuad_sz0
```
Nothing dropped. Signatures compared token-wise after a perl rename normaliser (`d : Sizes → sz : Sizes d`, `d.L/W/lam/size → sz.*`, `Idx L W → Idx d L W`, `spectralZ → zt`, `BlockIndex → Vtx d`, `GaussianProduct.update → upd`): 16 identical; the 27 residual diffs consist only of these token kinds:
```
< d > sz                                  (implicit Sizes argument in applications, e.g. `minorRes d n …`)
< (Sizes.seqHflow > (sz.seqHflow ... sz   (dot notation, same term)
< svar > svarF > d ... > (sz.lam          (modelChaos_sg/_normSq_chaos/_Vq: RBM2D fine `svar L W` → `svarF d L W g`, rule R4)
< RBM.Ind.SizeTendsto … PerTimeDomAt (Sizes.seqP sz) sz.size > sz.SizeTendsto … sz.PrecPT   (stochDom_ldeQuad, defs above)
```
No residual difference beyond ST1-COMMON item 2 renamings. `d = 2` tokens: the prove report's grep finds only a docstring at `LDEQuadInst:498`; neither target contains an exponent of `d`, `W`, `L`.

## 2. Vacuity, hidden hypotheses, cycles

- `Sizes d` fields (`Defs/Sizes.lean:138-146`): `L, W, lam, three_le_L, W_pos`; no hidden analytic hypothesis.
- `gaussIBP` takes no hypothesis; `stochDom_ldeQuad` takes only deterministic ones (above). No `GaussIBP`, owed or structural predicate is assumed: the proof instantiates the merged `RowChaos.mom_le_momVpow` with the proved `gaussIBP sz`:
```
IBPPoly.lean:729:  have h := (modelChaosEps sz n u hz hu i ε hε).mom_le_momVpow (gaussIBP sz) q
```
- Imports: `RBM3D.Green.{LDEQuadT, LDE, RowIndep, EntryDom}`, all on `main`; no `import RBM3D`, no ST-2..ST-6 file; `GaussIBP` is a structure in `LDEQuad` (no cycle). No external hypothesis, so no limit check needed.

## 3. Compiled nonempty instances (`IBPPoly.lean:1086-1155`, namespace `RBM.Green.IBPInst`)

- `gaussIBP` at `sz0` (`d = 3`, `sz0.L 0 = 4`, `W 0 = 32`, `N = 2^21`, `Defs/Sizes.lean:260-267`): `gaussIBP_sz0_polyInt` (set `{c0, c1}` of two sizes, exponent 2) and `gaussIBP_sz0_stein_cubic` (`g = ω_{c0}³`, `g' = 3ω_{c0}²`, unbounded, Tame side conditions discharged by `Tame.coord/const/pow/mul`, derivative by `HasDerivAt.fun_pow`), at a coordinate with `seqGvar_sz0_c0 : seqGvar sz0 c0 = 32⁻³(1 + 6/64²)⁻¹`, `seqGvar_sz0_c0_pos` (positive variance, so not the Dirac case).
- `stochDom_ldeQuad_sz0`: `stochDom_ldeQuad sz0 (κ := 1) one_pos sz0_tendsto (E := 0) (t := 1/2)` with `|0| ≤ 1`, `0 ≤ 1/2 < 1` by `norm_num`; all hypotheses discharged, `t = 1/2 > 0` (non-zero chaos), `N → ∞`.
- `example : GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 1/2) 1 := diag_bound_stochDom sz0 … sz0_admissible … stochDom_ldeRow_sz0 stochDom_ldeCol_sz0 stochDom_ldeQuad_sz0 stochDom_normSq_Hflow_diag_sz0`: the target feeds its downstream pin with no hypothesis left (`*_sz0` lemmas are closed theorems in merged `Green/LDE.lean:1195,1242,1253`).
All compile (build below). **Instances: PASS** for both targets.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Green.IBPPoly   (warnings in IBPPoly.lean: 14, all "This line exceeds the 100 character limit")
Build completed successfully (3334 jobs).
exit=0
$ lake build RBM3D   (branch root; does not import the new module yet)
Build completed successfully (3824 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option|@\[implemented_by|@\[extern|unsafe" RBM3D/Green/IBPPoly.lean
grep exit=1
$ (48 public theorem/def names by script) -> ax.lean with `#print axioms` each; lake env lean ax.lean
lean exit=0
  48 depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.gaussIBP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeQuad' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.IBPInst.gaussIBP_sz0_stein_cubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.IBPInst.stochDom_ldeQuad_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ cat precheck.lean        # registry pre-check, ST1-COMMON item 8
import RBM3D
import RBM3D.Green.IBPPoly

#assert_rbm_axioms
$ lake env lean precheck.lean ; grep -nE "error|axiom audit|GaussIBP" precheck.out
precheck exit=0
1:axiom audit: 2779 theorems, 1107 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
14:  RBM.Green.GaussIBP: 23 [no certificate]
108: RBM.Green.GaussIBP,
$ git diff --name-only main...t/T2088
RBM3D/Green/IBPPoly.lean
$ git merge-base main t/T2088 ; git rev-parse main
4f186cf8027fffad75812d440eab93711440fecb
7f9bfa15b1396371fa764c86b92cf44c0823757e
$ git diff --name-only $(git merge-base main t/T2088) main
RBM3D.lean  RBM3D/Induction/Step2Events.lean  RBM3D/Test/Axioms.lean  docs/queue/T2080.state  docs/reports/T2080-*.md
```
Only the sole writable file `RBM3D/Green/IBPPoly.lean` (new) is touched; no frozen signature changed; `Test/Axioms.lean` untouched by the branch (main's later T2080 edit of it does not conflict, the branch does not touch it). **Build/axioms: PASS.**

## 5. Paper deltas

- T2088a (prove report (d)): `hLquad` (paper (4.7), from [YY_25, Lemma 4.2]) is now proved for the Gaussian flow with constant `hwConst q` and threshold `N^{τ(q+1)-D}`. Covers the only Lean/paper difference of T2: the paper's statement is the cited general LDE, Lean's is the Gaussian-model instance in `PrecPT` form.
- T2088b: `GaussIBP sz` becomes a theorem; existing D80 (`docs/paper-deltas.md:390`) records it as owed, S1-19; T2088b updates that. T1 is not a paper statement (abstract Gaussian calculus), so no further delta.
Coverage: **PASS.**

## Observations (no verdict impact)

- O1. 14 line-length style warnings in the new file.
- O2. No compiled instance at a zero-variance coordinate of `stein` (the prove report says so); the endpoint `gaussIBP` is unconditional and is instantiated nondegenerately at positive variance, so this is not required.
- O3. Registry line `RBM.Green.GaussIBP` in `owedProps` (`Test/Axioms.lean:90`) becomes superfluous after merge; removal is for the cleanup ticket, as the ticket says.
- O4. RBM2D sources changed after `c9a24cf` (prove report's `diff --stat`); the ticket pins `c9a24cf`, which is what was compared.

## Verdicts

| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `gaussIBP` | = `GaussIBP sz` | none | `gaussIBP_sz0_polyInt`, `gaussIBP_sz0_stein_cubic` | PASS | T2088b | **PASS** |
| `stochDom_ldeQuad` | = `hLquad` text; = RBM2D after renames | none | `stochDom_ldeQuad_sz0` + `GiiOmegaSeq sz0` example | PASS | T2088a | **PASS** |

Ticket T2088: **PASS**. No dispatcher sign-off needed.
