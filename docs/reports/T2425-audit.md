Auditor model: claude-opus-5-5

# T2425 audit (round 1) — Sun Oct 11 13:21:20 UTC 2026

Branch `t/T2425` @ `ef3f4a4`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2425-audit1` (detached at `t/T2425`).
Scratch: `<scratchpad>/T2425/` (`probe.lean` = `git show t/T2395:RBM3D/Probe/T2395Pins.lean`, `f.lean` = `git show t/T2425:RBM3D/Graph/BASymm1.lean`).

## 1. Diff scope

```
$ git diff --stat main...t/T2425
 RBM3D/Graph/BASymm1.lean | 475 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 475 insertions(+)
$ git diff --name-only main...HEAD      (audit worktree)
RBM3D/Graph/BASymm1.lean
```
Only the sole writable file; no frozen signature touched (new file only). `RBM3D.lean` not edited (the hub adds the import at merge).
## 2. Statements against the pins (script diff vs the T2395 probe)

```
$ diff <(sed -n '71,104p' probe.lean) <(sed -n '65,98p' f.lean); echo "pins exit $?"
pins exit 0
$ diff <(sed -n '272,273p' probe.lean) <(sed -n '171,172p' f.lean); echo "inv exit $?"
inv exit 0
$ diff <(sed -n '234,238p' probe.lean) <(sed -n '399,403p' f.lean); echo "int exit $?"
int exit 0
```
Probe 71-104 = `BAMEdge.twist`, `BAPsiEdge.twist`, `BAGraph.twist`, `BAGraph.twist_atomAdj`, `ba_twist_counters` with proofs (target 1, verbatim);
probe 272-273 = `BAtwistInv` (target 2); probe 234-238 = `BAtwistIntegral` (target 3). Pinned statement of target 3 (from `f.lean:399-403`):
```
def BAtwistIntegral (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (c t' : Bool) (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      ∫ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        (if c then (star : ℂ → ℂ) else id) (∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))
```
The endpoint theorems prove exactly the pinned Props, with no added hypothesis:
```
theorem baTwistInv_holds : BAtwistInv := by ...                     (f.lean:175)
theorem baTwistIntegral_holds (d : ℕ) : BAtwistIntegral d := by ...  (f.lean:407)
$ (ax.lean) example : BAtwistInv := baTwistInv_holds ; example : ∀ d, BAtwistIntegral d := baTwistIntegral_holds   -> compiles (§5)
```
C1 (ticket item 5): the pin carries `BASelf` and `0 ≤ t < 1` only; no smallness of `g0`. Proof of `baTwistIntegral_holds` binds them as `_`
(unused): `intro L W _ _ _ g0 Em t m _ _ _ Ex Ix _ _ _ _ c t' Γ ℓe` (f.lean:408).
## 3. Vacuity, hidden hypotheses, cycles

- `BAtwistInv`, `BAtwistIntegral` are `def … : Prop` with all hypotheses in the binder list; no structure carries a field hypothesis.
- Integral proof (f.lean:408-421): pathwise `BAGraph.BASymm1_val_twist` (needs `star S = S`, `star gPsi = gPsi`, discharged by
  `BASymm1_data_real` for every `ω`), `BASymm1_dataTr_flip` (transposed data = data at the flipped sample; `Sp` symmetric by
  `BASymm1_pushThrough`, unconditional), `(BASymm1_flip_measurePreserving d L W 0).integral_comp'`, `lwSymm_integral_cj`. None of these needs
  integrability, so no hypothesis is hidden in an integrability side condition.
- Imports: `Graph.LWSymm`, `Graph.BAAtomic`, `Graph.BAExpandW`, `BA.CouplingWindow` (all merged on `main`); `CouplingWindow` imports
  `RBM3D.BA.MFixedPoint` and Mathlib only (`grep -n "^import" RBM3D/BA/CouplingWindow.lean`: lines 7-8). No cycle.
- `open private BAExpandW_PsiI_transpose from RBM3D.Graph.BAExpandW` reads a merged private lemma (no new assumption).
- External hypothesis: none.

## 4. Compiled nonempty instances (namespace `RBM.Graph.BASymm1Inst`, f.lean:424-471)

```
def G0 : BAGraph (Fin 2) (Fin 3) where
  solid := [⟨true, true, Sum.inl 0, Sum.inr 0⟩, ⟨false, true, Sum.inr 1, Sum.inl 1⟩, ⟨true, true, Sum.inl 1, Sum.inr 2⟩]
  waved := [⟨true, true, Sum.inl 0, Sum.inl 1⟩, ⟨false, true, Sum.inl 0, Sum.inr 0⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inl 1⟩]
  coeff := 1 + (1 / 2 : ℂ) * Complex.I
  psi := [⟨Sum.inl 1, Sum.inr 2⟩]
  mdot := [⟨true, Sum.inr 0, Sum.inr 1⟩]
theorem G0_normal : G0.Normal := ⟨by decide, by decide⟩
theorem G0_counts : G0.nExt = 2 ∧ G0.nLoops = 1 ∧ G0.nPairs = 1 := by decide
example : (G0.twist true true).mdot.map (fun e => (e.σ, e.x, e.y)) = [(false, Sum.inr 1, Sum.inr 0)] ∧
    (G0.twist true true).psi.map (fun e => (e.x, e.y)) = [(Sum.inr 2, Sum.inl 1)] := by constructor <;> rfl
example : (G0.twist true true).atomAdj = G0.atomAdj ∧ (G0.twist true true).counters = G0.counters :=
  ⟨BAGraph.twist_atomAdj true true G0, ba_twist_counters true true G0⟩
example : (G0.twist true true).Normal ∧ (G0.twist true true).nExt = 2 ∧ (G0.twist true true).nLoops = 1 ∧
    (G0.twist true true).nPairs = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := baTwistInv_holds true true G0
  obtain ⟨c1, c2, c3⟩ := G0_counts
  exact ⟨h1 G0_normal, h2.trans c1, h3.trans c2, h4.trans c3⟩
open RBM.BA.CouplingWindowInst in
example (c t' : Bool) :
    ∫ ω, (G0.twist c t').val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      (if c then (star : ℂ → ℂ) else id) (∫ ω, G0.val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) :=
  baTwistIntegral_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 c t' G0 ℓ0
```
Nondegeneracy: `G0` has 2 external and 3 internal vertices, one `M`-dotted edge (`u—w`), one `Ψ`-dotted edge (`v1—x`), solid, waved and
`×`-dotted edges, nonzero coefficient; the twist `(true,true)` changes the graph (first example). `BAtwistInv` is applied with its premise
`G0.Normal` discharged and nonzero counters (`nExt = 2`, `nLoops = 1`, `nPairs = 1`). Integral at `d = 3, L = 4, W = 2` (`N = 512`) and the
merged flow point; every hypothesis discharged:
```
$ grep -nE "t0P|EP|m0P|g0P|flowP_data" RBM3D/BA/CouplingWindow.lean | head -6
861:def t0P : ℝ := BAt0 (zS 4 10) (mS 4 10)
862:def EP : ℝ := BAflowE (zS 4 10) (mS 4 10)
863:def m0P : ℂ := mS 4 10 / (Real.sqrt t0P : ℂ)
864:def g0P : ℝ := Real.sqrt t0P * 10
869:theorem flowP_data : 0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P (EP : ℂ) m0P :=
874:theorem g0P_pos : 0 < g0P := mul_pos (Real.sqrt_pos.mpr flowP_data.1) (by norm_num)
```
`3 ≤ 4` by `norm_num`; `BASelf`, `0 ≤ t0P`, `t0P < 1` from `flowP_data`; `g0P > 0` (`g0P_pos`), no `False` premise, no empty index.
Statement level for the integral at `d = 3`, as the ticket allows (item 4).

## 5. Build, axioms, hygiene (audit worktree)

```
$ lake build RBM3D.Graph.BASymm1 > build.out 2>&1; echo "exit $?"
✔ [3810/3810] Built RBM3D.Graph.BASymm1 (4.2s)
Build completed successfully (3810 jobs).
exit 0
$ grep -n "BASymm1" build.out          (warnings/errors in the new file)
1364:✔ [3810/3810] Built RBM3D.Graph.BASymm1 (4.2s)
$ lake env lean ax.lean   (import RBM3D; import RBM3D.Graph.BASymm1; #print axioms …; the two examples of §2; #assert_rbm_axioms)
'RBM.Graph.BAGraph.twist_atomAdj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_twist_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwistInv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwistIntegral_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BASymm1_flip_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BASymm1_pushThrough' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BASymm1Inst.G0_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 11939 theorems, 3688 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). All within [propext,
 Classical.choice,  Quot.sound]; no project axioms: …
exit 0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2425-check.lean >/dev/null 2>&1; echo "check exit $?"
check exit 0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/BASymm1.lean; echo "grep exit $?"
grep exit 1
$ grep -rnE "baTwistInv_holds|baTwistIntegral_holds|BASymm1Inst|BAtwistInv|BAtwistIntegral|BAGraph\.twist|BAMEdge\.twist|BAPsiEdge\.twist" \
    RBM3D RBM3D.lean | grep -v "Graph/BASymm1.lean" | wc -l      (name clash)
       0
```

## 6. Paper deltas

The three statements are the probe pins verbatim (§2); no new Lean/paper statement difference is introduced by this ticket. The prove report
proposes `T2425a` (no statement delta; the proof is the BA twin of `LWSymm` §1-§3, not a call of `lwSymm_twist_integral`).
`grep -n T2425 docs/paper-deltas.md`: no entry yet (candidate pending dispatcher numbering). Coverage adequate.

## 7. Verdicts

| target | statement | vacuity/hidden/cycle | instance | build/axioms | verdict |
|---|---|---|---|---|---|
| 1 `BAMEdge.twist`, `BAPsiEdge.twist`, `BAGraph.twist`, `twist_atomAdj`, `ba_twist_counters` | verbatim (diff exit 0) | none | `G0`, twist `(true,true)` | ok | **PASS** |
| 2 `BAtwistInv` / `baTwistInv_holds` | verbatim | none | `G0` normal, counters 2/1/1 | ok | **PASS** |
| 3 `BAtwistIntegral d` / `baTwistIntegral_holds` | verbatim | none (BASelf, t-range unused) | `d=3,L=4,W=2`, `flowP` | ok | **PASS** |
Overall: **PASS**. No dispatcher sign-off needed.

## 8. Observations (no RETURN)

- Ticket acceptance asks for a prove report ≤ 120 lines; `wc -l docs/reports/T2425-prove.md` = 230 (within CLAUDE.md §6's 300). Report defect only.
- Ticket item 3 says "proved from `lwSymm_twist_integral`"; the proof is a twin built from that lemma's ingredients (stated as `T2425a`).
  The statement is unchanged, so this is a route difference only.
- Public unpinned helpers carry the stem (`BASymm1_*`, `BAGraph.BASymm1_*`, namespace `BASymm1Inst`); the endpoint proof names
  `baTwistInv_holds`, `baTwistIntegral_holds` are unpinned but unprefixed (no clash, grep count 0).
