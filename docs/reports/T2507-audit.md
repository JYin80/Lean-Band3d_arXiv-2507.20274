Auditor model: claude-opus-5-5

# T2507 audit (round 1) — U3-BA (a), row a: targets 1–6, 8 — Wed Oct 14 13:29:16 UTC 2026

Inputs: ticket `docs/tickets/T2507.md` (Decision (2): target 7 / `BA/QtNZBA` moved to U3-BA (b), not audited here); check `docs/tickets/checks/T2507-check.lean`;
prove report `docs/reports/T2507-prove.md`; branch `t/T2507` HEAD `dff84231` (base `5f6270cd`); detached audit worktree `RBM3D-wt/T2507-audit1`.

## 1. Diff scope
```
$ git diff --name-status main...HEAD
M	RBM3D.lean
A	RBM3D/BA/EKGenBA.lean
A	RBM3D/BA/KLipBA.lean
$ git diff main...t/T2507 -- RBM3D.lean   (two lines after the last import; #assert_rbm_axioms stays last)
@@ -623,6 +623,8 @@ import RBM3D.Chain.ExpWardIGen
 import RBM3D.Chain.QtNonzeroEndGen
+import RBM3D.BA.EKGenBA
+import RBM3D.BA.KLipBA
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | wc -l        (registry: no line closed or added)
       0
$ grep -rln "RBM3D.BA.EKGenBA\|RBM3D.BA.KLipBA" RBM3D RBM3D.lean   (importers)
RBM3D.lean
$ grep -c EKGenBA RBM3D/BA/KLipBA.lean                          (KLipBA does not import EKGenBA)
0
```
Only the sole writable files are touched; no merged file changes; no frozen signature touched.

## 2. Statements against the pins
Script text diff (whitespace-normalised; target text from `theorem/def <name>` to `:=`, pin text from `def T2507_*`, `T2507_EKKer` renamed to `BAEKKer`):
```
$ python3 -I sdiff.py docs/tickets/checks/T2507-check.lean RBM3D/BA/EKGenBA.lean RBM3D/BA/KLipBA.lean
BAEKKer                      DIFF
  PIN : {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop := ∃ E : ℕ → ℝ, C = baFM sz gK E ∧ ∀ n, BAReal d (sz.L n) (gK n) κ (E n) (BAmF sz gK E n)
  LEAN: {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop := ∃ E : ℕ → ℝ, C = baFM sz gK E ∧ ∀ n, BAReal d (sz.L n) (gK n) κ (E n) (BAmF sz gK E n) /-- **Target 2, `baEKKer_flow`** (= `T2507_KerFlowBA`): the `hKer
baEKKer_flow                 IDENTICAL
baEKSumNdecaygL_holds        IDENTICAL
baEKSumRes1gL_holds          IDENTICAL
baEKSumRes2NALgL_holds       IDENTICAL
baEKSumRes2gL_holds          IDENTICAL
baEKNonzerogL_holds          DIFF
  PIN : (d : ℕ) : Prop := ∀ Aof : ℝ → ℝ, STEKNonzerogL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) Aof
  LEAN: (d : ℕ) (Aof : ℝ → ℝ) : STEKNonzerogL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) Aof
baEKSumDecayNonzeroA_holds   IDENTICAL
baNQGoodGen_kerNAL           IDENTICAL
baQProxyG_kerEK4             IDENTICAL
baKloop_lip                  IDENTICAL
```
The two `DIFF` lines are not statement differences: for `BAEKKer` the body is identical and the regex ran on into the next docstring (no blank line
after the `def`); for `baEKNonzerogL_holds` the pin's `∀ Aof : ℝ → ℝ,` is a binder `(Aof : ℝ → ℝ)` in the theorem. Both are confirmed by Lean below.

Uncommitted scratch `audit_pins.lean` = imports and Part 2 of the check (target 7 copies included, unused) + the two new modules, then:
```
$ grep "^example" audit_pins.lean
example {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : T2507_EKKer sz C gK κ ↔ BAEKKer sz C gK κ := Iff.rfl
example : @T2507_EKKer = @BAEKKer := rfl
example (d : ℕ) : T2507_KerFlowBA d := baEKKer_flow d
example (d : ℕ) : T2507_SumNdecayBA d := baEKSumNdecaygL_holds d
example (d : ℕ) : T2507_SumRes1BA d := baEKSumRes1gL_holds d
example (d : ℕ) : T2507_SumRes2NALBA d := baEKSumRes2NALgL_holds d
example (d : ℕ) : T2507_SumRes2BA d := baEKSumRes2gL_holds d
example (d : ℕ) : T2507_NonzeroBA d := fun Aof => baEKNonzerogL_holds d Aof
example : ∀ d n Λ κ, T2507_EKNonzeroA d n Λ κ := baEKSumDecayNonzeroA_holds
example (d : ℕ) : T2507_KerNALBA d := baNQGoodGen_kerNAL d
example (d : ℕ) : T2507_KerEK4BA d := baQProxyG_kerEK4 d
example (d : ℕ) : T2507_KLipBA d := baKloop_lip d
$ lake env lean audit_pins.lean > audit_pins.out 2>&1; echo "exit $?"; grep -c error audit_pins.out
exit 0
0
```
`@T2507_EKKer = @BAEKKer := rfl` compiles: the class is the pinned text, `STEKKer d`-typed (used as `@BAEKKer d` in the five forms).
Hypotheses, quantifier order and `∃` placements (target 2: `κm` after `κ`, before `(sz, ε, 𝔠, 𝔡, z)`; 4: `C` after `(d, n, Λ, κ, A)`;
5a/5b: `Ck`/`C4` inside the merged families `NQGoodGen_KerNALFam` / `QProxyG_KerEK4Fam`; 6: none) are the pinned ones; law `seqP (sz.withLam 0)`;
target 3 (e) is for every `Aof` (Decision (3)); target 4 for every `A > 0`; target 6 for every `k ≥ 2` (family form).

## 3. Vacuity, hidden hypotheses, cycles; hypothesis-rule greps
- One new public `def` (`BAEKKer`, an `∃ E` class with no extra field; UBA-C2: no `0 < lam0 ≤ Λ` field). No structure; no hypothesis in a field.
- Inhabited at the flow: `inst_kernel : BAEKKer sz0 (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) (1/2)` (`EKGenBA:536`, from merged `BAflow_real`).
- No external hypothesis: every input is a merged theorem (module builds from `main` + the two files). New leaves, no cycle (sole importer `RBM3D.lean`).
```
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" (both files) | wc -l
       0
$ C1 grep 'mE\b|norm_mE|\|E\||SB d|BAK_le_small|BAMB_upper_small|Mbound_AO|W\^\(-eps|BAm_im_lower_window|STGridRepNgL' | wc -l
       0
$ grep -nE "^(noncomputable )?(def|abbrev|structure) " (both files)
RBM3D/BA/EKGenBA.lean:64:def BAEKKer {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK 
$ grep -n withLam | grep -v "seqP (sz.withLam 0)\|seqP (sz0.withLam 0)" | wc -l
       0
$ grep -nE "∀ \(sz : Sizes d\)"      (U5S-C3: the one hit is family-table row 2)
RBM3D/BA/EKGenBA.lean:70:theorem baEKKer_flow (d : ℕ) : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : 
$ grep -n "open private" -A1
RBM3D/BA/EKGenBA.lean:48:open private step34Gen_win_sz0 step34Gen_Az step34Gen_Az_sumZero step34Gen_Az_decay step34Gen_norm_Az_le
RBM3D/BA/EKGenBA.lean-49-  step34Gen_norm_delta0_le from RBM3D.Chain.Step34Gen
$ for n in <11 public names>; git grep -lw $n main -- RBM3D | wc -l   (name clash on main)
BAEKKer=0 baEKKer_flow=0 baEKSumNdecaygL_holds=0 baEKSumRes1gL_holds=0 baEKSumRes2NALgL_holds=0 baEKSumRes2gL_holds=0 baEKNonzerogL_holds=0 baEKSumDecayNonzeroA_holds=0 baNQGoodGen_kerNAL=0 baQProxyG_kerEK4=0 baKloop_lip=0 
```

## 4. Compiled nonempty instances (in the files; built in §5)
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5 ≥ 32`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`; `sInst ≡ 0`, `tInst ≡ 1/16`
(`Induction/Defs:439-440`); `Aof κ = (κ+1)/κ`.
| target | instance | data / discharge |
|---|---|---|
| 1, 2 | `EKGenBA:587`, `:594` | `baEKKer_flow 3 (1/2)` at `flow_sz0`; class by `inst_kernel` |
| 3 (a)–(d) | `:597`, `:603`, `:609`, `:615` | `n_ = 2`, `σ = (+,-)` ((c): `(+,+)`), window `(0, 1/16)` (`inst_win` via merged `step34Gen_winK_of_cmp` + R1), `𝒜 = δ₀` / sum-zero `step34Gen_Az` ((d)), `X ≡ 1`; `PrecL`, `STEKDecayKgL`, `STEKLowgL` discharged deterministically |
| 3 (e) | `:650` | `Aof = (κ+1)/κ` (`= 3 ≥ 1`), `s = 1 − λ²/L²`, `t = (1+s)/2`, `A = univ`, threshold `inst_thr` |
| 4 | `:661` | `n = 2`, `Λ = 10`, `κ = 1/2`, `A = 3`, flow datum at an index of the window, same `s, t`, `σ = (+,-)`, `𝒜 = δ₀` |
| 5a | `:677` | `k = 3`, `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`; class eventually and its bound at an index: `ε = 1/2`, `D = 2`, `(s,t) = (0,1/16)`, `σ = (+,+,-)`, `𝒜 = δ₀` |
| 5b | `:691` | `k = 3`, `KL = 6`: the class `QProxyG_KerEK4 … 3 6 C4 n` at an index (family hypotheses all discharged) |
| 6 | `KLipBA:312` | `k = 3`, `t ≡ 1/2 ≤ t₀` (`half_lt_t0`); bound at an index with `u = 0`, `u' = 1/2` |
| P7 | `EKGenBA:698` | `NQGood1Gen_eta_anti` at `baStep2Mat_loopForm … flow_sz0` |
No `N = 0`, empty index, collapsed window (`s < t < 1`, `0 ≤ s`) or `False` premise; every deterministic hypothesis is discharged at the concrete data.

## 5. Build and axioms (audit worktree, HEAD dff84231)
```
$ lake build RBM3D.BA.EKGenBA RBM3D.BA.KLipBA > build.log 2>&1; echo exit $?; tail -1 build.log; grep -c "^error" build.log
exit 0
Build completed successfully (4123 jobs).
0
$ grep -E "warning: RBM3D/BA/(EKGenBA|KLipBA)" build.log | wc -l; ... | grep -vc "exceeds the 100 character limit"   (style only)
20
0
$ lake build > full.log 2>&1; echo "exit $?"; grep -E "^error|axiom audit|non-vacuity" full.log; tail -1 full.log
exit 0
info: RBM3D.lean:630:0: axiom audit: 15285 theorems, 4721 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 124 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4400 jobs).
$ lake env lean audit_pins.lean | grep depends | sort | uniq -c   (#print axioms of the 11 public names)
1 'RBM.BA.baEKKer_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.BAEKKer' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baEKNonzerogL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baEKSumDecayNonzeroA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baEKSumNdecaygL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baEKSumRes1gL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baEKSumRes2gL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baEKSumRes2NALgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baKloop_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baNQGoodGen_kerNAL' depends on axioms: [propext, Classical.choice, Quot.sound]
1 'RBM.BA.baQProxyG_kerEK4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Paper deltas
The A-form threshold `(1 − s) L² ≤ Aof κ · gK²` with coupling `gK` (targets 3 (e), 4) and the `gK`-coupled forms are covered by D699 (a)–(b)
(`docs/paper-deltas.md:1707`); targets 4 (every `A > 0`; `A = 1` is `BAEKSumDecayNonzero`), 5a/5b and 6 are BA instances of merged Lean forms (D699, D730)
and change no paper statement. The prove report proposes no candidate (`T2507a` unused); none is missing.

## 7. Verdict
Targets 1, 2, 3 (a)–(e), 4, 5a, 5b, 6, 8: **PASS** (each equals its `T2507_*` pin; instances compile at nondegenerate `d = 3` data; build and axioms clean).
Observations (no RETURN): (O1) the target-5b instance applies the class at an index but not its inner bound (no length-3 sum-zero tensor; the pin's
bound is exercised by 3 (d)), prove report (d)1; (O2) instance helpers read six private `Chain/Step34Gen` names by `open private`; (O3) docstrings cite
`T2507_*` names (comments only, no declaration; X1-C4 "no `T25*_` text" read as declarations, as on `main`). No dispatcher sign-off needed.
