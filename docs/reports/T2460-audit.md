Auditor model: claude-opus-5-5
# T2460 audit, round 1 (Mon Oct 12 19:30:17 UTC 2026)
Branch `t/T2460` at `79339380` (base `a1412ad1`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2460-audit1` (detached, cache cloned from main).
Binding: ticket `docs/tickets/T2460.md` + Amend 1 (`docs/tickets/T2460-amend-1.md`, CONTROL H252 (3)): the third conjunct of `T2460_Bridge` is the
inequality H3′; target 4 left the row; delivered targets 1 (amended), 2, 3, 5, 6. Scratch `S` = scratchpad `T2460/`.

## 1. Statements against the pin (script diff, whitespace and blank lines ignored)
`S/sdiff.sh` takes the body after the head line of `def T2460_Bridge` / `def T2460_GridMart` in the amended check file on main
(`docs/tickets/checks/T2460-check.lean`, last change `a1628b9d` H252) and of `def BAGridBridge` / `theorem baGridMart_holds` on the branch.
```
$ S/sdiff.sh
target 1: pin 11 lines, lean 11 lines; diff -wB:
  (identical)
target 2: pin 2 lines, lean 1 lines; diff -wB:
  (identical)
$ grep -n -A1 '^theorem baGridBridge_holds' RBM3D/BA/GridMartBA.lean
538:theorem baGridBridge_holds (d : ℕ) : BAGridBridge d := by
```
Compiled form of the same comparison (check file + `import RBM3D.BA.GridMartBA` + the ticket's auditor lines), in the audit worktree:
```
-- appended to the check file (S/audchk.lean)
example : ∀ d : ℕ, T2460_Bridge d := baGridBridge_holds
example : ∀ d : ℕ, T2460_GridMart d := baGridMart_holds
example (d : ℕ) : BAGridBridge d = T2460_Bridge d := rfl
#print axioms RBM.BA.baGridBridge_holds
#print axioms RBM.BA.baGridMart_holds
$ lake env lean S/audchk.lean > S/audchk.out 2>&1; echo "exit $?"; grep -E 'error|axioms' S/audchk.out
exit 0
'RBM.BA.baGridBridge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridMart_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Reading of the statements (against ticket + Amend 1):
- Target 1 `BAGridBridge d`: `∀ κ ε 𝔡 > 0, ∀ 𝔠 sz z, BAFlow … →  ∀ s t (0 ≤ s ≤ t ≤ BAflowT0) → ∀ K (K n ≠ 0) → ∀ᶠ n, ∀ σ a, ∀ k ≤ K n, ∀ ω`,
  H1 `twAk … (a 1) (a 1) k ω (a 0) = STgAg (baStep2Mat …) … σ a k ω`, H2 `twDriftk … = STgDriftg …`,
  H3′ `‖twEEk … (a 0) (a 1) (a 1) k ω‖ ≤ 2 * ‖STEEMg … σ a‖`. Same parameter order as the pin; all charges `σ` (same-charge pairs included);
  constant 2 as amended. Matches Amend 1 item 1 exactly.
- Target 2 `baGridMart_holds d : STGridMartgL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0`: unchanged pin
  (`Chain/Step2Gen.lean:857-883`: `∃ C₀ ≥ 0`, then `∀ κ ε 𝔡`, flow, window, `∀ D > 0, ∃ CK ≥ 0, ∀ K ≥ N^CK`, `∃ Mart Rem`, clauses (i)–(iii)).
  Clause (iii) of the pin is untouched; the `ε′ → ε′/2` shift of Amend 1 item 2 is inside the private glue only.
- Target 3 (every `d`): both public theorems take only `(d : ℕ)`; no `3 ≤ d` premise.
**Targets 1, 2, 3: statement PASS.**

## 2. Vacuity, hidden hypotheses, cycles
```
$ F=RBM3D/BA/GridMartBA.lean; grep -nE '^(theorem|lemma|def|abbrev|structure|class|instance|noncomputable def)' $F
55:def BAGridBridge (d : ℕ) : Prop :=
538:theorem baGridBridge_holds (d : ℕ) : BAGridBridge d := by
673:theorem baGridMart_holds (d : ℕ) :
== private decl count: 37
== private names without stem GridMartBA_: 0
== structure/class in file: 0
$ grep -n -A2 'theorem baTwistGridMart_holds' RBM3D/BA/TwistStep.lean
73:theorem baTwistGridMart_holds (d : ℕ) : BATwistGridMart d := by
74-  obtain ⟨C₀, hC₀, hR⟩ := baTwistGridRem_holds d
75-  exact ⟨C₀, hC₀, baTwistGridAssemble_holds d C₀ hC₀ hR (baTwistGridTail_holds d) (baTwistGridWTail_holds d)⟩
$ sed -n 673,676p RBM3D/BA/GridMartBA.lean   (target 2 proof)
  obtain ⟨C₀, hC₀, hAt⟩ := baTwistGridMart_holds d
  exact ⟨C₀, hC₀, GridMartBA_bridge C₀ (baGridBridge_holds d) hAt⟩
```
- Public theorems carry no Prop premise. `BATwistGridMartAt` appears only as a premise of the private glue
  `GridMartBA_bridge` (`:591`), discharged by the merged, premise-free `baTwistGridMart_holds` (ticket "premise scan" respected).
- No new structure; `BAFlow` is the merged predicate (instance `flow_sz0` below). No cycle: the file imports only
  `BA.TwistStep`, `BA.EMn2BA`, `BA.KInduct` (all on main), and nothing imports the new file (`grep -rln 'import RBM3D.BA.GridMartBA' RBM3D RBM3D.lean | wc -l` → `0`).
- No external hypothesis (ticket "Inputs used as hypotheses only: none"), so no limit check is owed.
- Registry: `git grep -n -E 'GridMart|GridRepN' main -- RBM3D/Test/Axioms.lean` → 1 hit, `:389`, a comment in the `STOptL2` entry (not a premise).
**PASS.**

## 3. Compiled nonempty instances (`RBM3D/BA/GridMartBA.lean:678-743`)
```
$ grep -n '^example' RBM3D/BA/GridMartBA.lean | cut -c1-60
695:example : ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fi
709:example : ∃ n : ℕ, ∀ (σ : Fin 2 → Bool) (ω : PathΩ sz0), le
725:example : True := by
739:example (d : ℕ) : STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => (baS
```
- (a) `:695` target 1 at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `s ≡ 1/10`, `t ≡ 1/2`, `t ≤ BAflowT0` by
  `half_lt_t0`, `K n = ⌈N_n^{43}⌉₊+1` (`≠ 0` by `GridMartBA_Kinst_ne`): every premise discharged by `norm_num` / named lemmas, no hypothesis left.
  `:709` reads it at one `n` (`Filter.Eventually.exists`), `k = 1`, `a = (0,0)`, all four `σ` (same-charge pairs included), all `ω`.
- (b) `:725` target 2 at the same data, `D = 1`, grid `K n = ⌈N_n^{CK}⌉₊+1` with `N^{CK} ≤ K n` (`GridMartBA_Kinst_ge`, all `n`); obtains
  `Mart, Rem` and the three clauses and takes `.exists` of clause (i) at `n = 0`, `i = (![false,true], 0)`, of clause (ii), and of clause (iii)
  at `ε′ = 1/10` (under `IsProbabilityMeasure` of `Pp`). No premise left as hypothesis.
- (c) `:739` the `baStep2Data` reading (`toStep2Mat`, `flowOK`, `T0`), definitional.
- Nondegenerate: `L_0 = 4`, `W_0 = 32`, `N_0 = 2^21` (prove report (a)(ii)), `s > 0`, window `[1/10, 1/2]` not collapsed, index sets nonempty.
  `K_n` is large (`N^{CK}`), but that is the pin's own grid premise `N^{CK} ≤ K n`, not a witness chosen to make a bound hold.
- All four examples compile (module build, §4). **PASS.**

## 4. Build, axioms, hygiene, diff
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2460-audit1; lake build RBM3D.BA.GridMartBA > S/build.out 2>&1; echo exit $?
exit 0
$ grep -E 'Built RBM3D.BA.GridMartBA|Build completed' S/build.out; grep -c '^error' S/build.out; grep -E '^(error|warning)' S/build.out | grep -c GridMartBA
✔ [4049/4049] Built RBM3D.BA.GridMartBA (6.6s)
Build completed successfully (4049 jobs).
0
0
```
(Axioms of both public theorems: §1 output, standard three only.)
```
$ grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' RBM3D/BA/GridMartBA.lean | wc -l
0
$ grep -nE '\|E\||\bmE\b|etaT|\bzt\b|mSigma|sz\.lam' RBM3D/BA/GridMartBA.lean | wc -l      (item 6, C1/spectral rule)
0
$ git diff main...t/T2460 --name-only
RBM3D/BA/GridMartBA.lean
$ git diff --name-only a1412ad1 main -- RBM3D | grep -E 'BA/(Twist|EMn2BA|KInduct|Step2BA|FlowPins|GreenSchur|KTree|TwistKer)|Chain/Step2(Gen|Kern)' | wc -l
0
$ for r in main t/T2461; do git grep -n -E 'BAGridBridge|baGridBridge_holds|baGridMart_holds|GridMartBA' $r -- 'RBM3D/*.lean' 'RBM3D.lean' | wc -l; done
0
0
```
- Only the sole writable file is touched (`RBM3D.lean` import left to the hub at merge, as §3 (A) 4). No merged file edited;
  private upstream helpers are used via `open private … from` (`:38-41`), no edit and no deletion. No frozen signature touched.
- Files changed on main since the base (`a1412ad1..03109267`) do not include any module in the file's import set listed above; the hub's
  full build at merge remains the acceptance step.
- Target 6 (no `|E| < 2`, `mE`, `etaT`, `zt`, `mSigma`, `sz.lam` window): grep 0. **PASS.**

## 5. Paper deltas
- Lean vs paper difference in this row: at BA the grid pin comes from TL's twisted pin plus three identities, not from `lem:DIfREP`
  (`7_8:1994`); already numbered `D690` (T2452b) in `docs/paper-deltas.md:1654`. The prove report (d) proposes **T2460a**: it confirms
  T2452b and records that the probe's equality H3 is false and the true statement is H3′ (constant 2 = slot count), costing `ε′ → ε′/2`
  inside the glue. `STGridMartgL` itself is unchanged, so no further statement delta. Coverage complete. **PASS.**
- Target 4 (`T2460_GridRepN2`) left the row by Amend 1 item 3; its absence is not a defect here (report (a)(iv) records the one-slot vs
  two-slot obstruction for the dispatcher).

## 6. Observations (no verdict effect)
- O1. The target-2 instance `:725` has conclusion `True`; it nevertheless applies `baGridMart_holds 3` at the data with every premise
  discharged and extracts all three clauses (`c1`–`c3`), which is what §4 step 2 requires.
- O2. The glue needs `2 ≤ N^{ε′/2}` (`:645`), a stronger eventual threshold than the `√2` of (a′); same conclusion, as the report states.
- O3. 793 lint warnings in the build log all belong to upstream modules rebuilt from the branch base; 0 in `GridMartBA`.

## Verdicts
| target | verdict |
|---|---|
| 1 `BAGridBridge` / `baGridBridge_holds` (amended H3′) | PASS |
| 2 `baGridMart_holds` | PASS |
| 3 every `d` | PASS |
| 4 `T2460_GridRepN2` | not in this row (Amend 1 item 3) |
| 5 instances (a), (b), (c) | PASS |
| 6 item-6 spectral grep | PASS |
**Overall: PASS.** No dispatcher sign-off needed.
