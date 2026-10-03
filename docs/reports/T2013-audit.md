Auditor model: claude-opus-5-5

# T2013 audit (round 1) — MD-3 flow data, G-loops, block Anderson wrapper, cut-and-glue, envelope
Written Sat Oct  3 02:16:22 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2013-audit1`,
detached at `t/T2013` = `e40d210`. `$SP` = the auditor's scratchpad. **Verdict: PASS (all targets).**

## 1. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Loop.GLoopFlow RBM3D.Gauss.BlockAnderson 2>&1 | grep -v '^trace' | grep -iE "error|warning|sorry|Build completed"
Build completed successfully (3294 jobs).            # exit 0, no error/warning lines
$ lake env lean $SP/AuditAx.lean     # import RBM3D.Gauss.BlockAnderson; #print axioms of 37 declarations
ztOf, ztOf_im, zt_eq_ztOf, etaT_eq_etaOf, Gres, Mres, Gsig_eq_Gres, gloop_eq_loopM, loopM_eq_loopL,
Sizes.{Gt, Lloop, Gn, gLoopFlow_seqHflow_isHermitian, Gt_lemT, Lloop_zero_one, norm_Lloop_le,
seqHflowBA, seqHBA_isHermitian, Gt_BA}, ring_inverse_smul_one, Mres_zero_msc, trace_Eblk, blockMat_zero,
gloop_cutGlueL_split, gloop_cutGlueR_split, norm_loopM_le, norm_gloop_le_sharp, norm_loopM_le_sharp,
PsiB_isHermitian, PsiI_isHermitian, BlockAndersonInst.Gt_BA_sz0, GLoopFlowInst.{z0_Gt, Lloop_sz0,
norm_gloop_sharp_sz0, norm_Lloop_sz0, norm_loop_sz0}
   -> each: depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Loop.LoopIdx.cutGlue' does not depend on any axioms
exit=0
$ grep -nE "sorry|admit|native_decide|^ *axiom |set_option.*(debug|skip)|@\[implemented_by|unsafe" <both files>; echo $?
1
$ git diff --name-only main...t/T2013
RBM3D/Gauss/BlockAnderson.lean
RBM3D/Loop/GLoopFlow.lean
$ grep -n "^import" <both files>   # all imported modules exist on main (git ls-tree main)
BlockAnderson.lean:6:import RBM3D.Loop.GLoopFlow   :7:import Mathlib.LinearAlgebra.Matrix.Kronecker
GLoopFlow.lean:6:import RBM3D.Loop.GLoop   :7:import RBM3D.Loop.TreeRep   :8:import RBM3D.Gauss.FineModel
```
Only the two sole writable files; no frozen file touched; `RBM3D/Test/Axioms.lean`, `RBM3D.lean`, `GLoop.lean` untouched.

## 2. Statements — item 1 (pinned probe text `5d2a4a8:RBM3D/Probe/T2002Vocab.lean` lines 448–791)
```
$ git --no-optional-locks show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean > $SP/probe.lean
$ diff <(sed -n '503,655p;696,791p' $SP/probe.lean) <(sed -n '48,298p' RBM3D/Loop/GLoopFlow.lean)
122c122,125
< theorem seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
---
> /-- `H_u` is Hermitian: the probe's `seqHflow_isHermitian` (probe lines 624-628), renamed with the
> file stem because T2006 merged the same statement under that name
> (`RBM3D/Gauss/FineModel.lean:531`, `Sizes.seqHflow_isHermitian`). -/
> theorem gLoopFlow_seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
153d155
<
$ diff <(sed -n '448,501p;656,695p' $SP/probe.lean) <(sed -n '35,133p' RBM3D/Gauss/BlockAnderson.lean)
54a55,59
>
> namespace Sizes
>
> variable {d : ℕ} (sz : Sizes d)
>
$ lake env lean $SP/Ren.lean
example : @Sizes.seqHflow_isHermitian = @Sizes.gLoopFlow_seqHflow_isHermitian := rfl   -- compiles
@Sizes.seqHflow_isHermitian : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (sz.seqHflow n u ω).IsHermitian
@Sizes.gLoopFlow_seqHflow_isHermitian : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (sz.seqHflow n u ω).IsHermitian
exit=0
```
All pinned text is verbatim except: (a) one blank line; (b) the block Anderson items of probe 656–695 sit after a
re-opened `namespace Sizes` (file placement only, the ticket allows it); (c) `seqHflow_isHermitian` is renamed with
the file stem because `main` already declares `RBM.Gauss.Sizes.seqHflow_isHermitian` (FineModel.lean:531) with the
identical type (checked above). The ticket's clash rule ("a clash is renamed with the file stem and listed") covers
(c); the downstream name `Sizes.seqHflow_isHermitian` resolves to the merged lemma with the same statement.
Mathematics (ticket preflight): `ztOf m E t = E + (1-t) m`, `etaOf m t = (1-t) Im m` (lines 55, 58); `Gt_lemT`:
`√t₀ · G_{t₀}(E₀) = G(z)` with `(E₀,t₀) = (lemE z, lemT z)`, hypothesis `0 < Im z` only — the third clause of
`(eq:zztE)`; `Lloop_zero_one`: `𝓛^{(1)}_{0,σ,a} = m(σ)` for `|E| ≤ 2`; `Gt_BA`: `√t₀ G_{t₀;E,λ₀} = G(z,λ)` given
`0<Im z`, `0<t₀`, `λ₀ = √t₀ λ`, `z_{t₀}(E,λ₀) = √t₀ z` (`(eq:t0E0_BA)`, `(eq:zztE_BA)`, data of the deterministic
layer, DECISIONS §11). All match the pin.

## 3. Statements — item 2 (ports from `../RBM2D` at `c9a24cf`, renaming R1–R4, `Z2→Zd d`, `W^2→W^d`)
```
$ python3 $SP/pd.py   # git show c9a24cf:<file>, statement up to `:=`, whitespace-normalised, renames:
#   gloop L W H z→loopL d L W H z, Gsig H z→Gres H z, Eblk L W→Eblk d L W, gloopProd L W→gloopProd d L W,
#   Z2 L→Zd d L, LoopIdx→Loop.LoopIdx, BlockIndex L W→Vtx d L W, ((W:ℝ)⁻¹ ^ 2)→(((W:ℝ) ^ d)⁻¹);
#   section variable [NeZero W] dropped from the RBM3D side for the sharp envelope
def cutGlue DIFF            2D: ... (I : Loop.LoopIdx α) : Loop.LoopIdx α ...   3D: ... (I : LoopIdx α) : LoopIdx α ...
theorem gloop_cutGlueL_split IDENTICAL
theorem gloop_cutGlueR_split IDENTICAL
theorem norm_gloop_le_sharp IDENTICAL
$ diff <(git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Hierarchy/Operations.lean | sed -n 27,29p) \
       <(sed -n 317,319p RBM3D/Loop/GLoopFlow.lean); echo $?
0
```
(`cutGlue` DIFF is only my `LoopIdx→Loop.LoopIdx` substitution; RBM3D declares it inside `namespace RBM.Loop.LoopIdx`;
the declaration lines are identical.) Envelope for arbitrary Hermitian `H` (ticket item 2):
`norm_loopM_le (hH : H.IsHermitian) (hη : 0 < η) (hz : η ≤ |z.im|) (σ a : Fin (n+1) → _) : ‖loopM d L W H z σ a‖ ≤ η⁻¹^(n+1)`
— `n+1 ≥ 1` factors (the `n = 0` loop is `tr I = N`, so `n ≥ 1` is necessary); the merged `norm_gloop_le`
(GLoop.lean:245) is re-derived from it by the `example` at GLoopFlow.lean:1090. The sharp form
`norm_gloop_le_sharp`: `≤ η⁻¹^n · (W^{-d})^(n-1)`, `n = I.a.length ≥ 1`, `I.WF` — RBM2D's `(W⁻¹)^2` correctly
becomes `(W^d)⁻¹`. `Sizes.norm_Lloop_le` is the flow case (`|E|<2`, `t<1`, bound `(etaT E t)⁻¹^(k+1)`). The
source is `RBM2D/Gauss/LoopEnvelope*.lean`, not `Hierarchy/Loops.lean` as the ticket says (prove report (a),(a′)).
`zztE`: nothing ported; `Gt_lemT`'s pinned proof uses the merged `eq_inv_sqrt_mul_zt`. Both are within the ticket.

## 4. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` is declared in either file (grep: only a docstring hit at GLoopFlow.lean:513); no new
  hypothesis `Prop`. Every hypothesis is a signature argument.
- Imports are merged modules only (section 1); `BlockAnderson` → `GLoopFlow` → {GLoop, TreeRep, FineModel}; no cycle.
- External hypotheses of `Gt_BA` (`hlam0`, `hzt`): concrete limit check present in the prove report (a), instance B,
  at the compiled sequence `sz0` with the deterministic-layer values `m₀ = m(E,λ₀)`: `t₀ = 0.99999094 ∈ (0,1)`,
  `|z_{t₀} − √t₀ z0| = 5.9e-17`, `self_m` residual `5.6e-17`, `Im m₀ > 0`. Accepted.

## 5. Compiled nonempty instances (d = 3, `sz0` at n = 0: L = 4, W = 32, λ = 1/64, N = 2097152)
Read from the files; all compile in the build of section 1 and their axioms print as in section 1.
| target | instance | hypotheses discharged at concrete data |
|---|---|---|
| `Gt_lemT` | `GLoopFlowInst.z0_Gt` (GLoopFlow:955) | `0 < Im z0`, `z0 = 1/2 + i N^{-4/5}` (`z0_im_pos`) |
| `Lloop_zero_one` | `GLoopFlowInst.Lloop_sz0` (:976) | `|1/2| ≤ 2` by `norm_num`; `σ = true`, any `a` |
| `Gt_BA` | `BlockAndersonInst.Gt_BA_sz0` (BlockAnderson:209) | `0<Im z0`; `t₀ = 1/4 > 0`; `λ₀ = λ/2 = √t₀ λ` (`hlam0`); `z_{t₀}(1/4, m₀) = √t₀ z0` with `m₀ = i(2/3)Im z0` (`hzt0`, proved by `Complex.ext`) |
| `gloop_cutGlueL/R_split` | `example`s :1027, :1075 | 6-loop on `Z_4^3`, cut `k=2<l=4`, `H = Hmat ω`, `z = z_{1/2}(1/2)`; length hyps `rfl` |
| `norm_loopM_le` | `norm_loop_sz0` (:1045), `norm_loop_BA_sz0` (BA:231) | Hermitian via `seqXmat_isHermitian`/`seqHBA_isHermitian`; `η = Im z0 > 0`; `η ≤ |Im z0|` |
| `Sizes.norm_Lloop_le` | `norm_Lloop_sz0` (:1054) | `|lemE z0| < 2`, `lemT z0 < 1` from merged lemmas at `0 < Im z0` |
| `norm_gloop_le_sharp` / `_loopM_le_sharp` | `norm_gloop_sharp_sz0` (:1062), `norm_loop_BA_sharp_sz0` (BA:240) | `WF`, `1 ≤ length` by `simp`; Hermitian; `η = Im z0` |
None is degenerate: `N = 2097152`, nonempty index types, `t₀ ∈ (0,1)`, no `False` premise, no large witness.
The `Gt_BA_sz0` data `m₀` is not the deterministic-layer value (the ticket keeps that as data, DECISIONS §11); the
numeric check of section 4 covers the actual values.

## 6. Paper deltas
- No new Lean/paper statement difference: `Gres`/`Mres` via `Ring.inverse` (D22), single-time flow `Gt`, `Lloop`
  (D21), 0-based blocks (D19) are signed entries, cited in the prove report (d). The envelope is a deterministic
  consequence of `‖G_t‖ ≤ η_t^{-1}` (`7_8:949`, checked: `sed -n 945,952p paper/tex/7_8_light_weight.tex`), not
  a numbered paper statement; no delta needed.
- The label "(5.2)" used by the ticket and merged `GLoop.lean` is not this paper's (5.2) (prove report (a′):
  p. 44, `t ≥ 1 − (log W)^{-10}`). This is a ticket/doc label issue, not a statement difference; forwarded as a
  doc-fix item (prove report O2).

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O-a: the ticket names `RBM2D/Hierarchy/Loops.lean` as the envelope source; the actual source is
  `RBM2D/Gauss/LoopEnvelope.lean`, `Envelope.lean`, `LoopEnvelopeSharp.lean` at `c9a24cf` (the last is absent at
  RBM2D HEAD `9e0f275`). Dispatcher may record this in the portmap.
- O-b: `gloopProd` is public with RBM2D's name (it occurs in the statements of the two `*_split` theorems); the
  name-clash grep of the prove report (b.6) shows no clash on `main`.
- O-c: `GLoop.lean` module doc "What is missing" is stale (prove report O2); file not writable here.

## Verdict per target
| target | verdict |
|---|---|
| item 1, `GLoopFlow.lean` pinned text (25 names; `seqHflow_isHermitian` stem-renamed per clash rule) | PASS |
| item 1, `BlockAnderson.lean` pinned text (`PsiB`, `PsiV`, `PsiI`, `*_isHermitian`, `seqHflowBA`, `seqHBA`, `Gt_BA`) | PASS |
| item 2, `cutGlue`, `gloop_cutGlueL_split`, `gloop_cutGlueR_split` | PASS |
| item 2, envelope `norm_loopM_le`, `Sizes.norm_Lloop_le`, `norm_gloop_le_sharp`, `norm_loopM_le_sharp` | PASS |
| item 2, `zztE` (nothing needed beyond merged `eq_inv_sqrt_mul_zt`) | PASS |
Overall: **PASS**. No dispatcher sign-off required.
