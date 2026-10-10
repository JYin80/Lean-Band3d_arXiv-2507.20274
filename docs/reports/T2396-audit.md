Auditor model: claude-opus-5-5

# T2396 audit (round 1): BA-K09b, `BA/KStep.lean` (Sat Oct 10 22:44:31 UTC 2026)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2396-audit1`, detached at `t/T2396` = 27b48e4; `main` = 1a5f972.

## 1. Build, axioms, hygiene, diff

```
$ lake build RBM3D.BA.KStep            (error/warning-on-sorry lines: none)
Build completed successfully (3776 jobs).
$ lake env lean ax.lean                (scratch: #print axioms + statement checks below)
'RBM.BA.KStep_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KStep_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KStep_baIndStepAbs_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKpi_empty_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKpiBoundAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
(no other output line: both statement-check examples elaborate)
$ lake env lean docs/tickets/checks/T2396-check.lean ; grep -c error
check exit 0
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/KStep.lean
grep exit 1
$ git diff --name-only main...HEAD
RBM3D.lean
RBM3D/BA/KStep.lean
$ git diff main...HEAD -- RBM3D.lean
@@ -435,6 +435,7 @@ import RBM3D.BA.EKSum
 import RBM3D.BA.KSumZeroB
 import RBM3D.Chain.LWGen
 import RBM3D.BA.LWPinsBA
+import RBM3D.BA.KStep
 
 /-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
 #assert_rbm_axioms
$ grep -n "BAKpiBoundAt\|KStep" RBM3D/Test/Axioms.lean
reg exit 1          (target 6: no registry line, no change needed)
$ wc -l RBM3D/BA/KStep.lean
     746            (stop line 1,300)
```
Only sole writable files are touched; the import is after the last import line; no frozen signature edited
(`Loop/KLInduct.lean` untouched). Full `lake build` is the hub's at merge.

## 2. Statements

### Target 3 `baKpiBoundAt_holds` against the pin `BAKpiBoundAt` (`BA/KInduct.lean:66`)
```
theorem baKpiBoundAt_holds (d n : ℕ) [NeZero n] {Λ κ : ℝ} (hd : 3 ≤ d) (hn : 3 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    BAKpiBoundAt d n Λ κ
-- scratch check (elaborates):
example : ∀ (d n : ℕ) [NeZero n] {Λ κ : ℝ}, 3 ≤ d → 3 ≤ n → 0 < Λ → 0 < κ → BAKpiBoundAt d n Λ κ :=
  fun d n _ _ _ hd hn hΛ hκ => baKpiBoundAt_holds d n hd hn hΛ hκ
```
The conclusion is the pinned def itself (∀ τ>0, ∃ C>0, ∀ L≥3, g∈(0,Λ], E m with `BAReal`, t∈[0,1), σ, π, a:
`‖BAKpi‖ ≤ C L^τ B_{t,0}^{n-1}`). Hypotheses are exactly the ticket's `3 ≤ d, 3 ≤ n, 0 < Λ, 0 < κ`. No extra
hypothesis, unconditional: no `IndStepTH`, `KLPT` or other gate pin remains (the leaf bundle `IndStepTH` is proved in the
file, `KStep_indStepTH`, from merged `baProp5_holds`, `baProp5s_holds`, `baProp6/7_holds` at c = 1/2, `baProp8_holds`,
plus private copies of translation and row sum). C1 (target 4): `∃ C` precedes every model quantifier, so C depends on
`(d, n, Λ, κ, τ)` only. **PASS.**

### Target 2 (D3) `baKpi_empty_bound`
Scratch `example` restating the ticket's D3 (`‖K^{(∅)}_{t,σ,a}‖ ≤ C L^τ B_{t,0}^{n−1}`, constants uniform in
`L ≥ 3, g ∈ (0,Λ], BAReal, t ∈ [0,1)`, quantifier order of the pin restricted to π = ∅) is closed by
`fun τ hτ => baKpi_empty_bound n hd hn hΛ hκ τ hτ` (elaborates, see §1). Not the one-line `C_Σ S^n` reduction; the
report's F5 explains why that reduction is not uniform. **PASS.**

### Target 1 abstract step `KStep_step`, `KStep_all` (`KStep.lean:76, 212`)
Hypotheses (read from the signature): `hn : 3 ≤ n`, `hBp : 0 ≤ Bp`, `ht : ‖t‖ ≤ 1`, `hempty` (layer ∅ bound at n),
`hzero : KLTSPlong n σ π = ∅ → Kp n σ a π = 0`, `hcut` (verbatim right side of `baKpi_cut_abs`, `BA/KInduct.lean:734-746`,
with `BASig`→`Sig`, `BAThetaOf ..`→`TH`, `BAKpi`→`Kp`), `hind : IndStepAbs d k L Bp (Sig k) TH` for 3 ≤ k < n,
`hout : KStepAt .. k` for 3 ≤ k < n. Conclusion `KStepAt d L Bp Kp n` (= the `BAKpiBoundAt` shape over abstract ι).
- The ticket lists four hypotheses; `hzero`, `hBp`, `ht` are additional. `hzero` is necessary: without it, `Kp n σ a π`
  on a layer with no tree is constrained by none of the four (hcut needs some `F₀ ∈ TSP n` with `KLFlong F₀ σ = π`),
  so the four-hypothesis version is false. The band step uses the same fact (`Loop/KLInduct.lean:46`, "(b)
  `KLTSPlong n σ π = ∅`: `K^{(π)} = 0`"). `ht`, `hBp` are deterministic and needed for a uniform constant. All three are
  discharged at BA (`KStep_BA_all`: `unfold BAKpi; rw [h, Finset.sum_empty]`, `Complex.norm_real`, `KLIndStepA_Bparam_nonneg`).
  Ticket preflight item (ii) delegated the exact statement to the 1a, which wrote F1. Paper-delta candidate T2396a covers it.
- Ward: `grep -c KLWardIneq Loop/KLInduct.lean` = 0, so the band step does not use the Ward inequality; not using
  `baWardIneq_holds` does not weaken target 3, whose conclusion is the pin.
**PASS.**

### `KStep_baIndStepAbs_holds` (extra public, stem-prefixed)
`IndStepAbs` at family `KWardIneq_Data d Λ κ` (fields `L, hL:3≤L, g, hg:0<g, hgΛ:g≤Λ, E, m, hr:BAReal, t, ht0:0≤t,
ht1:t<1`, `BA/KWardIneq.lean:141-152`): the fields are exactly the pin's quantified data, no hidden hypothesis.
Hypotheses `3 ≤ d, 3 ≤ k, 0 < Λ, 0 < κ` only. **PASS.**

## 3. Compiled nonempty instances (all in `namespace KStepInst`, `KStep.lean:615-744`, built in §1)
Data: flow point `P` of `(d, L) = (3, 4)`, `Λ = 10`, `κ = P.m0.im` (`P.real.1.1 : 0 < κ`), `g = P.g0 ∈ (0,10]`,
`t = 1/2`, `τ = 1`, distinct labels in `Z_4^3`.
| endpoint | instance (line) | nondegeneracy |
|---|---|---|
| `baKpiBoundAt_holds` | 634 (n=4, σ=KLsigAlt 4, π=∅), 644 (n=4, σ=(+,+,-,+), π={(0,2)}), 654 (n=5, π={(0,2),(2,4)}), 666 (n=3) | each layer proved `Nonempty` (`decide` / tree witness `KStep_layer4/5`) |
| `baKpi_empty_bound` | 676 (σ=(+,+,-,+)), 685 (σ ≡ +) | both branches (long root / all short) |
| `KStep_baIndStepAbs_holds` | 694 (k=4, r=1, `σ 1 ≠ σ 2` by `decide`) | root long |
| `KStep_step` | 709: all eight hypotheses discharged at BA data, n=4, inequality at π={(0,2)} | nonempty layer |
| `KStep_all` | applied in `KStep_BA_all` (570) with every hypothesis discharged at the BA family; that is instantiated at d=3, Λ=10 in 709 and via `baKpiBoundAt_holds` in 634-666 | as above |
| K11 premise | 740: `baWardIneq_holds 3 4 ..` with premises from `KStep_baIndStepAbs_holds` | no hypothesis left |
No example carries a hypothesis; no N = 0, empty index, collapsed window or `False` premise.
Target 5's literal data (σ = KLsigAlt 4) is used at π = ∅ (3 trees); line 630 proves by `decide` that its layer
{(0,2)} is empty, so the π ≠ ∅ instance uses σ = (+,+,-,+). This is a correction of degenerate ticket data, not a defect.

## 4. Paper deltas
Report (d) proposes T2396a (`hzero` in the abstract step; structural, no paper statement differs) and T2396b
(`IndStepTH` fields carry `L^τ`, BA props carry none: weaker interface). The target statement `BAKpiBoundAt` is a
merged pin unchanged here; no further Lean/paper difference found.

## 5. Observations (no RETURN)
- O1. `KStep_all` has no standalone `example`; its instance is the private named application `KStep_BA_all`
  (every hypothesis discharged) used by concrete examples. Accepted as a named check.
- O2. Six private copies duplicate private lemmas of `BA/KInduct.lean`, `BA/KWardIneq.lean` (report (d)); housekeeping only.
- O3. Ticket target 3 names `baWardIneq_holds` as an input; the band step does not use Ward (grep 0), so it is
  correctly a consumer (example 740). Dispatcher may note this for K12; no sign-off needed.

## Verdict
| target | verdict |
|---|---|
| 1 `KStep_step` / `KStep_all` | PASS |
| 2 `baKpi_empty_bound` (D3) | PASS |
| 3 `baKpiBoundAt_holds` | PASS |
| 4 C1 | PASS |
| 5 instances | PASS |
| 6 registry | PASS (no change) |
**T2396: PASS.**
