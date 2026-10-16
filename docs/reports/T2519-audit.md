Auditor model: claude-opus-5-5
# T2519 row a: audit, round 1 (Fri Oct 16 14:26:24 UTC 2026)
Scope: row a (targets 1-5) on `t/T2519` at `f44898b4`, under the ticket and Amends 1-3. Audit worktree `RBM3D-wt/T2519-audit1` (detached).
The probe `RBM3D/Probe/T2519Pins.lean` (b992c2e7) is used only as the source of the signed texts. Rows b, b′, c, d are out of scope.
Scratch files are in `SCR/T2519/` (session scratchpad): `A1.lean`, `*.chk.lean`, `first.lean`. None is committed.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.GUEProcBA RBM3D.BA.GUEHypABA RBM3D.BA.GUEEntryGridBA
✔ [3998/4000] Built RBM3D.BA.GUEProcBA (5.9s)
✔ [3999/4000] Built RBM3D.BA.GUEEntryGridBA (4.3s)
✔ [4000/4000] Built RBM3D.BA.GUEHypABA (7.9s)
Build completed successfully (4000 jobs).
exit=0            (error lines: 0; the warnings are all in upstream merged files)
$ lake env lean SCR/T2519/A1.lean   # 27 x `#print axioms RBM.BA.<each public decl of the three files>` + the checks of §2
exit=0; lines "depends on axioms: [propext, Classical.choice, Quot.sound]": 27; any other output: none
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' GUEProcBA GUEHypABA GUEEntryGridBA   ->  0 0 0
$ X1-C4 grep '^(private )?(noncomputable )?(def|abbrev|structure) (gueHBA|ztOf|…|BAEd|BAMO)\b'  ->  0 0 0
$ grep -cE '^import RBM3D\.BA\.(MainInd|TwistPins|Step6|TwistStep)'  ->  0 0 0
$ import closure (python over `^import RBM3D` lines), modules matching BA.(MainInd|TwistPins|Step6|TwistStep|TwistAvg)
RBM3D.BA.GUEProcBA 256 forbidden: []   RBM3D.BA.GUEHypABA 264 forbidden: []   RBM3D.BA.GUEEntryGridBA 267 forbidden: []
$ git diff --stat main...t/T2519   (main = a925870b)
 RBM3D.lean | 3 +   RBM3D/BA/GUEEntryGridBA.lean | 425 +   RBM3D/BA/GUEHypABA.lean | 920 +   RBM3D/BA/GUEProcBA.lean | 645 +
 RBM3D/Probe/T2519Pins.lean | 298 +   RBM3D/Test/Axioms.lean | 1 +      6 files changed, 2292 insertions(+)
$ git diff main...t/T2519 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep '^[+-][^+-]'
+import RBM3D.BA.GUEProcBA / +import RBM3D.BA.GUEHypABA / +import RBM3D.BA.GUEEntryGridBA    (lines 656-658; last import 658, `#assert_rbm_axioms` 661)
+   `RBM.BA.GUEPathBoundsBA, -- BA twin of `GUEPathBounds` (T2519 row a, …   (hunk @@ -381 structuralProps; Decision (9))
$ name clash: git grep -wc NAME main -- RBM3D RBM3D.lean, for the 27 new public names  ->  all 0
$ C1 regex (ticket Rules) on the 27 public statements (comments removed; `gueH|Pgue|PathΩ|filt` only at `(sz.withLam 0)`; `ouP (UNModel.band (sz.withLam 0))` allowed)
C1 hits on public statements: 0
$ wc -l   645 GUEProcBA.lean   920 GUEHypABA.lean   425 GUEEntryGridBA.lean   1990 total
```
Diff: only sole writable files (row a's three files, the `RBM3D.lean` import lines, the named registry line, and the 1a probe, which stays branch-only). No merged file is edited, so no frozen signature changes. Lines: 1,990 ≤ row a landing line 2,927 (Amend 2 item 5). Largest file 920 ≤ 2,000.
**Merge note for the hub:** rule (A)3 must bring in the three `BA/GUE*BA` files, `RBM3D.lean` and `Test/Axioms.lean`. It must **not** bring in `RBM3D/Probe/T2519Pins.lean` (ticket: never merged).

## 2. Statements against the signed texts (targets 1, 4) and Amend 3 item 5 (target 3), checked in Lean
`A1.lean` imports the built probe and the three modules, and compiles with exit 0 (§1):
```
example : @T2519Probe.T2519_PathBoundsBA = @GUEPathBoundsBA := rfl
example : @T2519Probe.T2519_KFamBA = @BAKFam := rfl
example : @T2519Probe.T2519_PBBA = @BAPB := rfl
example : T2519Probe.T2519_ProducersBA = (RBG_Prod … (BAKFam d) (BAPB d) ∧ RandomLayerB_LL … (BAPB d) ∧ RBG_Que … (BAKFam d) (BAPB d)) := rfl
def MapMixTy : Prop := <verbatim text of T2519_MapMixBA, docs/tickets/checks/T2519-pins.lean:167-170>
example : MapMixTy := fun sz g t1 t0 K n k h1 h2 => map_gueHBA_eq_mixMatBA sz g t1 t0 K n k h1 h2
example … (hKF : T2519Probe.KClauses sz g E t1 t0 m Kt) : <probe hKdet, :238-240: ∀ ε > 0, ∀ᶠ n, ∀ s ∈ Icc (t1 n) (t0 n), ∀ I, I.WF →
    2 ≤ I.length → I.length ≤ 2 * 4 → ‖Kt n s I‖ ≤ N ^ ε * (N * etaOf (m n) s)⁻¹ ^ (I.length - 1)>
  := Hyp_Kt_detDomBA hd sz hκ hΛ hτU 4 hr hlam ht1 ht10 ht0 hsz h730 hell Kt hKF.1 hKF.2
example (hH : T2519Probe.T2519_HoffBA d) … (hKF : KClauses …) (hP : GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz 4) 4 Kt) :=
  hH hd sz κ Λ hκ hΛ g E t1 t0 m 4 Kt hsz le_rfl hlam hr ht1 ht10 ht0
    (fun n hg s hs σ a => Hyp_Kt_oneBA sz hκ 4 (by norm_num) Kt hr ht1 ht10 ht0 hKF.1 hKF.2 n hg hs σ a)
    (fun ε hε => (Hyp_Kt_detDomBA … ε hε).mono fun n h s hs I hI h2 h4 => h s hs I hI h2 (by omega)) hP
```
Result: target 1 (`GUEPathBoundsBA`, `BAKFam`, `BAPB`) is definitionally the signed `T2519_*` text. That text carries Amend 1 item 1: `n₀ = 4`, `gueGridK sz 4`, lengths `≤ 4 * 4`.
`map_gueHBA_eq_mixMatBA` proves the signed `T2519_MapMixBA` verbatim.
`Hyp_Kt_detDomBA` at `n₀ = 4` concludes the probe's `hKdet` with no adapter (Amend 3 item 5). Together with `Hyp_Kt_oneBA` and PB, it feeds every premise of the signed `T2519_HoffBA`. That is the exact-type chain row d needs.
First commit: `git show 19df37e2:RBM3D/BA/GUEProcBA.lean` compiles (`lake env lean`, 0 error lines). Its §1 vocabulary text (`def GUEPathBoundsBA` … exact-type `example`) is `diff`-identical to HEAD, and 19df37e2 is an ancestor of HEAD. So rows b and b′ stack on the final texts.

## 3. Per-target statement review (signatures read in the files; band twins `Proc:596, 771`, `ProcK:553`, `HypA:690, 712, 981`, `EntryGrid:518`)
- **T2 process layer.** `gueDevBA`, `gueStopBA`, `gueLmaxBA`, `gueDmaxBA`, `gueLprocBA`, `gueDprocBA` and their facts are the twins of `Proc:83-122` with three substitutions: `gueH ↦ gueHBA`, `zt ↦ ztOf (m n) (E n)`, `mE E • 1 ↦ Mres (g Ψ_I) E m`.
  `norm_egtNGUEOf_le` uses the generic `egtNGUEOf`. Its `hε` is the block-trace error `tr(Gres σ · E_a) − mSigOf m σ` (the diagonal only), and its conclusion has the band form `|I| · N · ε · B`.
  `gueDevBA_succ_le` replaces `|E n| < 2` by `0 < Im m n`, `‖m n‖ ≤ 1`. Its conclusion is the band one, with `etaOf (m n)`.
- **T3.** `Hyp_Kt_detDomBA` and `gueKproc_detDomBA` replace the band `|E| ≤ 2 − κ`, `hKb : sz.STKbound E`, `STKloop` with `BAReal`, eventual `0 < g ≤ Λ`, and the `BAKsol` start guarded by `0 < g n`. They carry **no external K-bound premise**: it is proved from the merged `baKBoundAt_holds` (coverage row 12, D1 (iii)). This is weaker in hypotheses than the twin.
  `hell` is `L^d(1−t₁) ≤ 2 g²`. `GUEHypABA_hell_of_hell` derives it from RBG_Prod's two zero-mode premises (`≤ λ²`, `≤ 1`; `3 ≤ d`, `3 ≤ L`) at `g = √t₀ λ`.
  The conclusion range `2 ≤ |I| ≤ 2 n₀` and the quantifier order `∀ ε, ∀ᶠ n, ∀ s, ∀ I` are those of the band. `gueKproc_detDomBA` drops the band's unused `hscale` (weaker in hypotheses).
  `Hyp_Kt_oneBA` takes the `0 < g n` guard of `BAKFam` (F2 of Amend 3). `Hyp_gridBA` is the band `Hyp_grid` with the generic `genMatGUEOf`/`egtNGUEOf`. It drops `|E|<2`, `0 ≤ t1`, `1 ≤ m` and adds `0 < Im m`.
- **T4.** `gueGrid_entry_boundBA` is `gueGrid_entry_bound` at `(g, E, m)` with the centre `Mres`. Its family premise is C3 b's `GUEEntryMixBA` premise (`∀ n, 0 < g n ≤ 𝔡⁻¹ ∧ BAReal`), and its conclusion has the band's `StochDomAt` shape over `Fin (gueGridK sz n0 n + 1) × Idx²`.
- All public statements take `d` as a parameter (`{d : ℕ}`, `3 ≤ d` where the band has it), and all instances are at `d = 3` (MNO-C2).
- Hidden hypotheses and cycles: none. `GUEPathBoundsBA`, `BAKFam`, `BAPB` are `def … : Prop` (the signed vocabulary), not structures. No row-a theorem takes them or another new `Prop` as a premise. Every import is a merged module on `main` (closure above).
  Row a uses no external hypothesis, so lesson 14's limit check does not apply. `GUEPathBoundsBA` is registered as structural (Decision (9)).

## 4. Compiled nonempty instances
Every theorem or definition applied by a compiled `example` (prover's index, cross-checked against the files):
GUEProcBA: `:99` (exact type of `BAKFam`/`BAPB` in the three `RBG_*`), `:541`, `:574-617`. GUEHypABA: `:774, 785, 796, 862, 912`. GUEEntryGridBA: `:408, 413`.
I renamed every bare `example :=` / `example (ω …) :=` of GUEProcBA and GUEEntryGridBA to a named definition in a scratch copy and printed its type. The goal was to confirm that no hypothesis is left unapplied:
```
$ lake env lean SCR/T2519/GUEProcBA.chk.lean | grep -E "chk[0-9] :" -A2      (heads; exit 0)
chk1 : ∀ (ω : PathΩ (sz0.withLam 0)) (Kt : …), gueLprocBA sz0 … ≤ gueDprocBA … + gueKproc …        (gueLprocBA_le)
chk2 : ∀ ω Kt, gueDprocBA sz0 … ≤ gueLprocBA … + gueKproc …                                      (gueDprocBA_le)
chk3 : ∀ ω, gueLprocBA … (2*1+1) … ≤ √(gueLprocBA … (2*1) … * gueLprocBA … (2*1+2) …)              (gueLprocBA_odd)
chk4 : ∀ ω, gueLprocBA … (gridTime … 3) ω = gueLmaxBA … (min 3 (gueStopBA …)) ω                  (gueLprocBA_time)
chk5 : ∀ ω Kt, gueDprocBA … = gueDmaxBA …                                                         (gueDprocBA_time)
chk6/chk7 : ∀ ω (Kt), ContinuousOn (fun t => gueLprocBA/gueDprocBA …) (Set.Icc (1/4) (1/2))
chk8 : ∀ ω, gueDevBA sz0 … ≤ gueDevBA sz0 … + …                                                  (gueDevBA_succ_le)
$ lake env lean SCR/T2519/GUEEntryGridBA.chk.lean | grep -E "chk[0-9] :" -A1
chk1 : ∀ (k : ℕ), Measure.map (gueHBA sz0 (BAflowLam0 sz0 zSeq) (fun x => 1/4) (fun x => 1/2) (fun x => 4) 0 k) … = …
chk2 : StochDomAt (Pgue (sz0.withLam 0)) sz0.size (fun n p ω => {ω' | ∀ i j, ‖(green (gueHBA sz0 …) … - Mres …) i j‖ ≤ ↑(sz0.size n) ^ (-(1/20))}.indicator …) …
```
Only data binders remain (`ω`, `Kt`, `k`), and no `Prop` premise is left. The GUEHypABA examples state their conclusions explicitly (`∃ Kt, ∀ ε > 0, ∀ᶠ n, …`).
Data: `d = 3`, `sz0` (`N_0 = 2^21`). The BA flow datum is `BAflowLam0`/`BAflowEs`/`BAmF`, with `BAReal` at `κ = 1/2` for every `n` and `0 < g` for every `n`.
- K lemmas: window `1 − t₀ = λ²/(4L³) > 0`, `t₀ − t₁ = x/(2N) > 0`, `n₀ = 4`, `τ_U = 1/20`, `Λ = 10`. `h730` and `hell` are proved for every `n`, and `Kt` comes from `gueK_existsBA`.
- Process and entry instances: grid `t₁ = 1/4 < t₀ = 1/2`, `K = 4`, or `gueGridK sz0 2` for the entry bound with `δ = N^{-1/20}`, `c₀ = 1/20`, `(𝔠, 𝔡) = (1/6, 1/10)` (`flow_sz0.1`).
- `Hyp_gridBA` is applied for every `ω`, `δ`, `Kt` at `n = 0`, `l = 2`. Its constants are finite sums of the left sides over `k ≤ 4` and the labels; this is the band `HypAInst` pattern, not an astronomically large witness.
- None of the instances is degenerate: no `N = 0`, no empty index, no collapsed window, no `False` premise.
- `GUEPathBoundsBA`/`BAPB` are vocabulary, not endpoint theorems. Their nonempty instance is row c's producer, and their exact-type check is `:99`.

## 5. Paper deltas
`docs/paper-deltas.md` has no T2519 entry yet. The prove report proposes:
- `T2519a` (1a, (a′)): `n₀ = 4`, path bounds to `lk 4`, and T.7's input set.
- `T2519b`: the grid local law against `M^{(B)} ⊗ 1`.
- `T2519c`: `0 < g` only eventually in the K lemmas, `∀ n` in the entry bound.
- `T2519e`: the zero-mode regime `L^d(1−t₁) ≤ 2g²`.
- `T2519f`: the grid jump `Δ‖m‖ ≤ Δ`.

Each Lean/paper difference in row a's statements (§3) maps to one of these entries. Two parametrisation differences are already covered by the merged deltas D734 (ba) and D737 (c): the free flow datum `(g, E, m)` in place of `m_sc(E)`, and `0 < Im m`, `‖m‖ ≤ 1` in place of `|E| < 2`. Removing the band `STKbound` premise is weaker in hypotheses and not a delta. Coverage: complete.

## 6. Observations (no RETURN)
1. The prove report has 397 lines, over CLAUDE.md §6's 300 and the ticket's 250. Sections (a)/(a′)/(a″) come from earlier stages (262 lines), and the prover notes this in (d) 2. This is a report defect only.
2. Prove report (d) 1 is a real open issue for the consumers (rows c, d, N2), not for row a: the `∀ n` window of `GUEEntryMixBA`/`gueGrid_expect_oneLoopBA` versus the eventual window from the producers. Owner and price need a dispatcher decision before row d. Row a's statements follow the merged inputs' texts.
3. The probe file is in `git diff main...t/T2519` by design. The hub must leave it out at merge (§1).

## Verdict
| target | verdict |
|---|---|
| 1 `GUEPathBoundsBA`, `BAKFam`, `BAPB` (signed texts, `rfl`; first commit 19df37e2) | PASS |
| 2 process layer, `norm_egtNGUEOf_le`, `gueDevBA_succ_le` | PASS |
| 3 `Hyp_Kt_detDomBA` (Amend 3 item 5 exact form), `gueKproc_detDomBA`, `Hyp_Kt_oneBA`, `Hyp_gridBA` | PASS |
| 4 `map_gueHBA_eq_mixMatBA` (= `T2519_MapMixBA`), `gueGrid_entry_boundBA` | PASS |
| 5 instances | PASS |
**T2519 row a: PASS.** No dispatcher sign-off is needed for row a. Observation 2 is for rows c, d, N2.
