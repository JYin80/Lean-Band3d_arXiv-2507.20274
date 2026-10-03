Auditor model: claude-opus-5-5
# T2056 audit (round 1) — KL7c `KLSumZeroWard`
Written Sat Oct  3 14:57:00 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2056-audit1`, detached at `t/T2056` = `45d225d`; `main` = `a68a954`. Scratch: scratchpad `T2056/`.

## 0. Scope of the branch
```
$ git diff --stat main...t/T2056
 RBM3D/Loop/KLSumZeroWard.lean | 1265 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1265 insertions(+)
$ git diff --name-only main...t/T2056 ; git diff main...t/T2056 -- RBM3D/Test/Axioms.lean | wc -l
RBM3D/Loop/KLSumZeroWard.lean
       0
$ grep -n "^import" RBM3D/Loop/KLSumZeroWard.lean
6:import RBM3D.Loop.KLSumAll
7:import RBM3D.Loop.KLCut
```
Only the sole writable file; no merged file, no frozen signature touched; does not import `RBM3D`.

## 1. Statements (script diffs)
Targets extracted from the branch file (`:1071`, `:1160`):
```
theorem Qlayer_alt_one_eq_zero :
    ∀ E : ℝ, |E| < 2 → ∀ (n : ℕ) [NeZero n], 4 ≤ n → Even n →
      Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 := by
variable (d : ℕ) (g : ℝ)          -- :1153, same section binders as KLSumZero.lean:704
theorem KLSigmaPi_alt_sumZero_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t := by
```
Diffs (RBM2D read with `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Loop/SumZeroWard.lean`):
```
# A: RBM2D :1921 (mSig->mSigma, sigAlt->KLsigAlt) vs Lean
diff exit 0
# B: RBM2D :2002 (Z2 L->Zd d L, SigmaPi L->KLSigmaPi d L g, mSig->mSigma, sigAlt->KLsigAlt,
#    etaT->Gauss.etaT, bound var d->δ, name SigmaPi->KLSigmaPi) vs Lean
diff exit 0
# C: merged adapter SigmaPi_alt_sumZero_le_of_Qlayer_one (KLSumZero.lean:813, renamed) vs Lean
3,4c3
<     ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n →
<       Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 → ∀ d₁ : Zd d L,
---
>     ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
diff exit 1
```
Diff C is exactly the ticket's pin: the adapter without the hypothesis `Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0`; quantifier order, `|E| ≤ 2 - κ`, `t ∈ [0,1)`, `n ≥ 4` even, `d₁`, constant and `η_t` unchanged. No `W`, no `3 ≤ d` (DECISIONS §23, T2043 audit O1). Target 2's proof (`:1166-1169`) is the adapter applied to `Qlayer_alt_one_eq_zero E hE2 n hn hev`, `hE2 : |E| < 2` from `0 < κ`.

Target 1 is not vacuous / not a junk-value identity. Merged definitions:
```
KLTree.lean:336   def KLFlong F σ := F.filter fun J => σ J.1 ≠ σ J.2
KLTree.lean:340   def KLTSPlong n σ π := (TSP n).filter fun F => KLFlong F σ = π
KLSumZero.lean:256 edgeR m t s s' := (1 - (t : ℂ) * (m s * m s'))⁻¹ - 1
KLSumZero.lean:261 Qlayer m t σ π := ∑ F ∈ KLTSPlong n σ π, ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2)
```
In the layer `π = ∅` every edge joins equal charges, so at `t = 1` each factor is `(1 - m(s)²)⁻¹ - 1` with `m(s)² ≠ 1` for `|E| < 2` (`m = ±1` only at `E = ∓2`): no `0⁻¹`. It is [YY_25] Lemma 3.10 (2) (`R_n(1) = 0`), the closed-form ingredient of the paper's first estimate in `(eq:Sigma-empty-sum-zero)` (A_deterministic_estimates.tex:731-734: `∑_{b∖b₁} Σ^{(∅)} = O(|1-t|)`, cited by the paper from [YY_25] Lemma 3.10 / [RBSO1D] Lemma 4.29).

DECISIONS §23 factor: it enters only the private `Alayer_cut` (`:452-458`), whose prefactor is `t (1 - t m(σ_{J.1}) m(σ_{J.2}))` instead of RBM2D's `ξ_J(1-ξ_J)`; hypotheses `hm : ‖t m m'‖ < 1` only. This is the expected §23 change (identity `t(1-ξ_J)(∏_in m)(∏_out m) = ξ_J(1-ξ_J)∏ m`, no division). It does not reach either target statement (diffs A, B exit 0).

Verdict on statements: both targets equal the pin.

## 2. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^(structure|class) |sorry|admit|native_decide|^axiom|implemented_by|extern|unsafe|opaque" RBM3D/Loop/KLSumZeroWard.lean
grep exit 1
```
No structure/class; no hypothesis `Prop`; both targets carry only numeric/data hypotheses (`0 < κ`, `3 ≤ L`, `|E| ≤ 2-κ` / `|E| < 2`, `t ∈ [0,1)`, `4 ≤ n`, `Even n`). Dependencies: only merged modules (`KLSumAll`, `KLCut` and their imports, which include `KLSumZero`); target 2 depends on target 1, target 1 on no target 2: no cycle. No external hypothesis, so no limit check needed.

## 3. Compiled nonempty instances (`:1181-1263`)
| endpoint | instance | data | hypotheses discharged |
|---|---|---|---|
| `Qlayer_alt_one_eq_zero` | `KLSumZeroWard_inst_Q_four` | `E=0, n=4` | `|0|<2` norm_num, `4≤4` le_rfl, `Even 4` decide |
| `Qlayer_alt_one_eq_zero` | `KLSumZeroWard_inst_Q_six` | `E=1, n=6` | `|1|<2`, `4≤6`, `Even 6` |
| `KLSigmaPi_alt_sumZero_le` | `KLSumZeroWard_inst_bound` (all `d₁`), `_bound_zero` (`d₁=0`) | `κ=1, d=3, L=3, g=1/2, E=0, t=1/2, n=4` | `0<1`, `3≤3`, `|0|≤2-1`, `1/2∈[0,1)`, `4≤4`, `Even 4` |
| `KLSigmaPi_alt_sumZero_le` | `KLSumZeroWard_inst_bound_six` | `κ=1, E=1=2-κ, n=6, d=3, L=3, g=1/2, t=1/2` | as above |
Exactly the ticket's instance data. Nondegeneracy, compiled in the same file:
```
KLSumZeroWard_Qlayer_zero        : Qlayer m 0 σ ∅ = 1                         (any m, σ)
KLSumZeroWard_inst_Q_four_nondeg : Qlayer (mSigma 0) 0 (KLsigAlt 4) ∅ ≠ Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅
KLSumZeroWard_inst_Q_six_nondeg  : same at (E, n) = (1, 6)
KLSumZeroWard_inst_card          : (KLTSPlong 4 (KLsigAlt 4) ∅).card = 3 ∧ (TSP 6).card = 45 ∧
                                   (KLTSPlong 6 (KLsigAlt 6) ∅).card = 18      (by decide)
KLSumZeroWard_inst_bound_lhs d₁  : (the n = 4 sum) = 1 / 3                     (KLSumZero_inst_slice_alt)
```
So target 1's instances are cancellations of 3 resp. 18 nonzero-index terms (not an empty sum), and target 2's left side is `1/3 ≠ 0` on a 27-site lattice; no `N = 0`, no empty index, no `False` premise, no huge witness. PASS.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Loop.KLSumZeroWard 2>&1 | grep -i "error\|warning\|completed"
Build completed successfully (3249 jobs).
exit 0
$ lake env lean ax.lean     # import RBM3D.Loop.KLSumZeroWard; #print axioms for each public name
'RBM.Loop.Qlayer_alt_one_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSigmaPi_alt_sumZero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_Qlayer_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_four_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_six_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound_lhs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound_six' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean pre.lean    # import RBM3D; import RBM3D.Loop.KLSumZeroWard; #assert_rbm_axioms
axiom audit: 1813 theorems, 813 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit 0
```
(A first run of `ax.lean` also tried a spurious name `RBM.Loop.class` picked up by my declaration grep from a docstring line `:759`; that line errored, the 12 real names above printed. Not a file defect.)

Public-name clash check against `main` (12 public names; everything else is `private`):
```
$ for n in <12 names>; do git grep -nw "$n" main -- 'RBM3D/*.lean' 'RBM3D.lean' | wc -l; done
Qlayer_alt_one_eq_zero 0 | KLSigmaPi_alt_sumZero_le 0 | KLSumZeroWard_Qlayer_zero 0 | KLSumZeroWard_inst_Q_four 0
KLSumZeroWard_inst_Q_six 0 | KLSumZeroWard_inst_Q_four_nondeg 0 | KLSumZeroWard_inst_Q_six_nondeg 0
KLSumZeroWard_inst_card 0 | KLSumZeroWard_inst_bound 0 | KLSumZeroWard_inst_bound_zero 0
KLSumZeroWard_inst_bound_lhs 0 | KLSumZeroWard_inst_bound_six 0
```
`Qlayer_alt_one_eq_zero` keeps RBM2D's pinned name (ticket: "Key statements: `Qlayer_alt_one_eq_zero`"); helper names carry the stem `KLSumZeroWard_` (§3 (E)).

## 5. Paper deltas
- Lean vs paper for target 2: explicit constant `2^{n²} n gapK(κ)^{-n} (2/√(κ(4-κ)))` times `η_t` in place of `O(|1-t|)`, and the bulk restriction `|E| ≤ 2-κ`. This is RBM2D's T2004a-11; the ticket instructs "cite, do not re-propose"; prove report (d) cites it. Same treatment was accepted for the merged adapter (T2043 audit :108). Covered per ticket.
- Restriction to `σ^{(alt)}`, `n ≥ 4` even, `π = ∅`: this is the paper's case (ii) (A:729-731, "alternating σ"), and the pin of the merged adapter. Not a delta.
- The §23 factor (private `Alayer_cut` prefactor): signed in DECISIONS §23 as not a paper-delta. Target statements unaffected.
- Target 1: no paper statement of its own (cited [YY_25] Lemma 3.10 (2)); matches the closed form `R_n(1) = 0`.

## 6. Observations (no effect on statement, instance, build, axioms or coverage)
- O1. `docs/paper-deltas.md` has no line naming T2004a-11 or the sum-zero bound (`grep -n "SigmaPi\|T2004a-11\|bulk\|gapK" docs/paper-deltas.md` empty). The ticket forbids re-proposing; the dispatcher may want an RBM3D entry for the explicit-constant/bulk form of `(eq:Sigma-empty-sum-zero)` (covers T2043's adapter and this target).
- O2. `t/T2056` is not based on current `main` (`git merge-base --is-ancestor main t/T2056` → 1; main moved to `a68a954`). The three-dot diff touches one new file only; the hub's full `lake build` at merge settles it.
- O3. The prove report's (d) notes that `sigmaIn`, `sigmaOut`, `exists_innermost`, `Flong_*` are private here; KL11 will need them (a later ticket must either duplicate or this file must be edited to make them public).

## Verdict
- `Qlayer_alt_one_eq_zero`: **PASS** (statement = RBM2D :1921 after renaming; nondegenerate compiled instances at `(0,4)`, `(1,6)`; axioms standard).
- `KLSigmaPi_alt_sumZero_le`: **PASS** (statement = merged adapter minus the `Qlayer … = 0` hypothesis = RBM2D :2002 after renaming; compiled instance at the ticket's data, left side `1/3`; axioms standard).
Ticket T2056: **PASS**. No dispatcher sign-off needed.
