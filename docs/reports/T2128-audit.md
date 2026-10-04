Auditor model: claude-opus-5-5
# T2128 audit (round 1) — LW-08 `Graph/LWLvl1`: `deflvl1`, `strat_local` as `LocStep`, `lvl1 lemma`, induction, cutoff
Written Sun Oct  4 15:41 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2128-audit1`, detached at `t/T2128` = 7768a79.
Pin: the ticket gives the targets in mathematics only (no Lean pin text); the check file has only `#check` of upstream names. Statements are compared with the ticket's mathematics and with `7_8:367-399`, `B:122-157`.

## 1. Diff, build, axioms
```
$ git diff --stat main...t/T2128
 RBM3D/Graph/LWLvl1.lean | 4462 +++   RBM3D/Test/Axioms.lean | 4 +      2 files changed, 4466 insertions(+)
$ git merge-base main t/T2128 -> a871db4 ; git merge-tree --write-tree main t/T2128 -> rc=0 (clean; main changed Axioms.lean lines 117-122 only)
$ git diff main...t/T2128 -- RBM3D/Test/Axioms.lean    # 4 lines added to `structuralProps`:
+ `RBM.Graph.LGraph.XBetween, `RBM.Graph.lvl1Split, `RBM.Graph.lvl1Split.below, `RBM.Graph.Lvl1Reach.below
$ grep -cwE "sorry|admit|native_decide|axiom" RBM3D/Graph/LWLvl1.lean -> 0
$ grep -n "^import" RBM3D/Graph/LWLvl1.lean -> LWSymm, LWVocab, ScalingOrder, LWWeightExp, ... (no `import RBM3D`)
$ lake build RBM3D.Graph.LWLvl1          (audit worktree)
Build completed successfully (3365 jobs).   rc=0    (no `error` line in the log)
$ lake env lean ax.lean   (#print axioms)
LGraph.LocStd, PGraph.LocStd, LocStep, lvl1_step_identity, lvl1_step_good, lvl1_exists_step, lvl1_lemma, lvl1_lemma_size,
lvl1_lemma_induction, lvl1_induction, lvl1_size_le, lvl1_inst_lemma, lvl1_inst_lemma_size, lvl1_inst_induction,
lvl1_inst_step1, lvl1_inst_step2, lvl1_inst_step3, lvl1_inst_locStd, lvl1_inst_not_locStd:
  each "depends on axioms: [propext, Classical.choice, Quot.sound]"   (19 lines, identical)
```
Public names outside the `lvl1`/`Lvl1` prefix: `LGraph.StdNeutral`, `LGraph.LocStd`, `PGraph.LocStd`, `LocStep` (all target names). Frozen signatures: none touched (only a new file and registry lines).

## 2. Target 1 `deflvl1` — PASS
```
def SEdge.lvl1ChargeAt (e : SEdge V) (v : V) : ℤ := if e.src = v then (if e.σ then -1 else 1) else (if e.σ then 1 else -1)
def LGraph.lvl1SolidAt Γ v := Γ.solid.filter fun e => e.lvl1IncAt v      -- lvl1IncAt: src ≠ dst ∧ (src = v ∨ dst = v)
def LGraph.StdNeutral (Γ : LGraph E I) (v : E ⊕ I) : Prop :=
  ((Γ.lvl1SolidAt v).map SEdge.σ = [true, false] ∨ (Γ.lvl1SolidAt v).map SEdge.σ = [false, true]) ∧ Γ.lvl1ChargeAt v = 0
def LGraph.LocStd (Γ : LGraph E I) : Prop :=
  Γ.Normal ∧ (∀ e ∈ Γ.solid, e.src ≠ e.dst) ∧ ∀ i : I, Γ.StdNeutral (Sum.inr i) ∨ Γ.lvl1DegAt (Sum.inr i) = 0
```
- (i) `Normal` (merged LWVocab:990; its third clause makes every solid self-loop circled, so weights in a normal graph are light-weights). (ii) no solid self-loop at any vertex. (iii) internal vertices: exactly two non-loop solid edges, one `G` and one `Ḡ` ("opposite charges"), and charge 0; charge = +1 for incoming blue / outgoing red, −1 otherwise = `(eq:neutralcharge)`. Degree excludes loops (`B:128`). Matches `7_8:367-386`.
- Instances (`by decide`, L4147-4186): `lvl1_inst_locStd`, `lvl1_inst_locStd_pack` (positive); `lvl1_inst_fail_{normal,loop,loopExt,deg1,deg3,same,charge}` each fail exactly one clause with the others proved; `lvl1_inst_not_locStd`. Decidability instance for `PGraph.LocStd` present (L3217).

## 3. Target 2 `LocStep` and the one-step identity — PASS
Statement (L3260-3275; extracted in the prove report (b), re-read here): constructors
- `weight` at any `x : E' ⊕ I'` with `lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩` (a light-weight of either colour, internal or external vertex; no precondition = Step 1 first);
- `edge` at internal `x`, `hwf` (no self-loop: Step 1 null) and `hbad : deg x ≠ 0 ∧ (deg x ≠ 2 ∨ charge x ≠ 0)` (= `B:146` "degree ∉ {0,2} or non-neutral"; with no loops deg 0 forces charge 0);
- `gg` at internal `x` with two same-colour edges `G_{xy}`, `G_{y'x}` after the twist, `hwf` and `hnb` (every internal vertex deg 0 or deg 2 with charge 0: Step 2 null) = `B:150-156`.
Outputs: the T2131 terms `lwSymmOwxT1-4`, `lwSymmOe1xOwx/Ds`, `lwSymmOe2xR2-R8`, each followed by `LGraph.partition m` and packed. Order of steps as in `B:135-157`.
Identity (`lvl1_step_identity`, L3590): `∫ P.val = Σ_{Q ∈ outs} ∫ Q.val` for every `LocStep m P outs` with `P.g.Normal`, under
`GaussIBP sz, 0 < z.im, 0 < u, m ≠ 0, z + u m = −m⁻¹, hSp, Spᵀ = Sp, M a a = m, M a b = 0 (a ≠ b)`.
- `M a b = 0`: Amend 1 (C4). `Spᵀ = Sp`: inherited from the merged T2131 forms:
```
$ grep -n "hSpT" RBM3D/Graph/LWSymm.lean (signatures)
1593: lwSymm_weight_graph_E ... (hSpT : Spᵀ = Sp)   1641: lwSymm_oe1x_graph_E ... (hSpT : Spᵀ = Sp)   1693: lwSymm_oe2x_graph_E ... (hSpT : Spᵀ = Sp)
1540: theorem lwSymm_lwSplus_symm {u : ℝ} (hu : 0 ≤ u) {m : ℂ} (hm : ‖m‖ ^ 2 * u < 1) :
```
  A deterministic data condition, discharged at the instance by the merged `lwSymm_inst_hSpT` and true for `S⁺` in the regime `‖m‖²u < 1`; covered by candidate `T2128a`. Not an external hypothesis, no limit check owed.
- Dropped terms `m 1_{x=y₁}` and `R1` are zero on normal graphs; the identity is proved with them removed (candidate `T2128c`).
- Instances: `lvl1_inst_step1` (Step 1 on `p2Graph` at `(Ǧ−M)_{β₁β₁}`), `lvl1_inst_step1Ext` (red light-weight at an external vertex), `lvl1_inst_step2` (degree-1 vertex, transposed selector), `lvl1_inst_step3` (`G_{a₀α₀}G_{α₀a₁}`), each `lvl1_step_identity` at `lwWxInstSz` (`lwWxSizes 3 3 1 (1/2)`: d = 3, L = 3, W = 1, N = 27), `m = mE 0`, `z = zt 0 (1/2)`, `u = 1/2`, with `gaussIBP`, `lwWx_inst_im`, `norm_num`, `lwWx_mE_ne`, `lwWx_flow`, `lwWx_inst_hSp`, `lwSymm_inst_hSpT`, `lwWx_inst_hM`, `lwSymm_inst_hM0`, normality by `decide`: every hypothesis discharged. Term counters by `decide` (`lvl1_inst_step{1,2,3}_terms`, e.g. Step 1 on `p2Graph`: 12 terms, all `ord = 3 = ord p2Graph + 1`).

## 4. Target 3 `lvl1 lemma` — PASS
```
$ #check @lvl1_lemma
∀ {E : Type} (m : ℂ) (K : ℤ) (Γ : PGraph E), Γ.g.Normal →
  ∃ outs errs,
    (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧
    (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ outs ++ errs, Lvl1Reach m K Γ Q ∧ Q.g.Normal ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ Γ.g.nM ∧
        ↑Q.g.nV - ↑Q.g.nW ≤ ↑Γ.g.nV - ↑Γ.g.nW) ∧
    ∀ {d sz n z u} (Sp M), GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + ↑u * m = -m⁻¹ → (hSp) → Sp.transpose = Sp →
      (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe,
        ∫ Γ.val (lwSampleData ..) ℓe ∂sz.seqP = (outs.map ∫ Q.val ..).sum + (errs.map ∫ Q.val ..).sum
$ #print LGraph.scalingOrder  ->  fun Γ => ord Γ.counters
$ #check @lvl1_exists_step : ∀ {E} (m : ℂ) (P : PGraph E), P.g.Normal → ¬P.g.LocStd → ∃ outs, LocStep m P outs
```
- Quantifier order: `m, K, Γ` fixed; `∃ outs errs` precedes all sample data `d, sz, n, z, u, Sp, M, ℓe` — lists independent of the data and of `n`, as the ticket asks ("if possible"). Every `m`, every normal `Γ`, every cutoff `K`.
- Content not vacuous: `outs` must be `LocStd` with `ord ≥ ord Γ`; `errs` must have `ord ≥ K`; the identity holds for all data. Termination is carried by the proved `lvl1_exists_step` (every normal non-`LocStd` graph admits a step), `lvl1_step_good` (every output normal and `Lvl1Good`: `ord` up, or `ord` equal and `(nLoops, nS, nPairs)` lex-smaller) and well-founded induction on `Lvl1Mu K = ((K−ord)^+, nLoops, nS, nPairs)` (`InvImage.wf`, `WellFounded.prod_lex`). No structure-field hypothesis: `PGraph` fields are types/instances and `ext_surj`; `LocStep`/`Lvl1Reach` are the relation itself.
- Input restricted to normal graphs (the paper: "arbitrary graph"); covered by `T2128e`.
- Instance `lvl1_inst_lemma` (L4384): `lvl1_lemma (mE 0) 72 p2Graph.pack (by decide)` with every identity hypothesis discharged at the instance data of §3; `p2Graph` = 2 external, 4 internal vertices, counters (6,2,4,2), `ord 2`. Nondegenerate.

## 5. Target 4 induction principle — PASS
```
theorem lvl1_induction {m K P Q} (h : Lvl1Reach m K P Q) (Pred : PGraph E → Prop) (h0 : Pred P)
    (hstep : ∀ A L, LocStep m A L → Pred A → ∀ B ∈ L, Pred B) : Pred Q
inductive Lvl1Reach (m : ℂ) (K : ℤ) : PGraph E → PGraph E → Prop
  | refl P | step P Q R L : Lvl1Reach m K P Q → ord Q.g.counters < K → ¬ Q.g.LocStd → LocStep m Q L → R ∈ L → Lvl1Reach m K P R
```
`lvl1_lemma` gives `Lvl1Reach m K Γ Q` for every `Q ∈ outs ++ errs` (same lists); `lvl1_lemma_induction` states the predicate form directly. LW-10 needs no unfolding of the proof. Instances `lvl1_inst_induction` / `lvl1_inst_lemma_induction` (invariant "normal ∧ n_M ≤ 2" on `p2Graph`, via `lvl1_step_good`), the second with the identity at the instance data.

## 6. Target 5 cutoff (a) — PASS
```
def lvl1Cutoff (c : ℝ) (K0 d : ℕ) (D : ℝ) (G : Counters) : ℕ := ⌈(D + K0 * G.nM + d * ((G.nV − G.nW).toNat)) / c⌉₊
theorem lvl1_size_le (c) (hc : 0 < c) (K0 d D G W L Ψ) (hW : 1 ≤ W) (hL : 1 ≤ L) (hLW : L^d ≤ W^K0)
    (hlow : W^(−d/2) ≤ Ψ) (hup : Ψ ≤ W^(−c)) (Q) (hK : lvl1Cutoff c K0 d D G ≤ ord Q) (hM : Q.nM ≤ G.nM)
    (hV : Q.nV − Q.nW ≤ G.nV − G.nW) : Q.scalingSize Ψ W d L ≤ W^(−D)
4047 theorem lvl1_lemma_size (m c) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (Γ) (hN : Γ.g.Normal) : ∃ outs errs,
   (∀ Q ∈ outs, Q.g.LocStd ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder) ∧
   (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → L^d ≤ W^K0 → W^(−d/2) ≤ Ψ → Ψ ≤ W^(−c) → Q.g.scalingSize Ψ W d L ≤ W^(−D)) ∧
   (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff ..) Γ Q ∧ ...) ∧ ∀ {sz : Sizes d} ..., (identity as in lvl1_lemma)
```
Order cutoff independent of `n`, `W`, `L`, `Ψ` (choice (a), Amend 1). Paper form `Err = O(W^{-D})` follows with constant 1 in the regime `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`; the lists are fixed before `(W, L, Ψ)`. Instances `lvl1_inst_cutoff` (= 72 at `p2Graph`, c = 1/4, K0 = 1, d = 3, D = 10), `lvl1_inst_size_le` (counters (80,4,6,1), W = 27, L = 3, Ψ = 27^{-1/4}), `lvl1_inst_lemma_size` (regime hypotheses discharged by `norm_num`/`rpow` monotonicity). Covered by `T2128b`.

## 7. Paper-delta coverage
| Lean/paper difference | candidate |
|---|---|
| identity needs `Spᵀ = Sp` (T2131) and `M a b = 0` (Amend 1) | T2128a |
| order cutoff `ord ≥ K` instead of `(eq:smallsize)`; `errs` may contain LocStd graphs of order ≥ K; constant 1; regime hypotheses | T2128b |
| `m 1_{x=y₁}` (Oe1x) and `R1` (Oe2x) omitted from the outputs (zero on normal graphs) | T2128c |
| measure `(K−ord, nLoops, nS, nPairs)` (internal) | T2128d |
| input is a normal packed graph; regular weights split by `partition m` of each output, not inside Step 1 | T2128e |
No uncovered statement difference found. Step 2/3 act at internal vertices only; `B:146` says "a vertex", but `deflvl1` (iii) and Step 3 constrain internal vertices only, so this changes no statement of the lemma (observation O2).

## 8. Observations (no verdict effect)
- O1. Ticket "Instances": item 3 on `p2Graph` "with the outputs listed". The outputs of `lvl1_lemma` stay existential: `LGraph.partition` does not reduce in the kernel (prove report (b), `decide` stuck on `Classical.propDecidable`), and section (a) counts 487745 tree nodes already at K = 5. The listed outputs are given at term level before the partition (`lvl1_inst_step{1,2,3}_terms`). The CLAUDE.md §4 instance requirement (endpoint theorem applied at concrete nondegenerate data, every deterministic hypothesis discharged) is met by `lvl1_inst_lemma`/`lvl1_inst_lemma_size`.
- O2. See §7 (internal vertices for Steps 2-3).
- O3. Identity instance data use W = 1 (merged `lwWxInstSz`, as in T2107/T2131); the regime instance uses W = 27 separately. Both nondegenerate (N = 27; Ψ window nonempty).
- O4. The branch is based on a871db4; main has since changed `Axioms.lean` at lines 117-122 only; `git merge-tree` is clean. The hub's full build at merge decides the registry check.
- O5. 164 warnings in the module (unused hypotheses, simp args, long lines); no errors.

## Verdict
| target | verdict |
|---|---|
| 1 `deflvl1` (`LGraph.LocStd`, `PGraph.LocStd`, `StdNeutral`) | PASS |
| 2 `LocStep` + `lvl1_step_identity` | PASS |
| 3 `lvl1_lemma` | PASS |
| 4 `lvl1_induction`, `lvl1_lemma_induction` | PASS |
| 5 cutoff (`lvl1Cutoff`, `lvl1_size_le`, `lvl1_lemma_size`) | PASS |
**T2128: PASS.** No dispatcher sign-off needed.
