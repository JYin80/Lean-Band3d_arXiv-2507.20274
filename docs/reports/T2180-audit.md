Auditor model: claude-opus-5-5

# T2180 audit (round 1) — ST2-13a `Path/DifREP2.lean`
Written Mon Oct  5 15:33:42 UTC 2026 (`date -u`). Branch `t/T2180` at `a5491d5`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2180-audit1` (detached, fresh). Inputs: ticket, Amend 1, Amend 2, check file `docs/tickets/checks/T2180-check.lean`, prove report.

## 1. Diff scope
```
$ git diff --stat main...t/T2180
 RBM3D/Path/DifREP2.lean | 2623 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    2 -
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   (the only two lines)
-   `RBM.Ind.GridRepTailNAt, -- clause (iii) / (iv) of `STGridRepNAt` for `difRepMartN`: ST2-13 (T2168)
-   `RBM.Gauss.Sizes.STGridMartAt, -- the grid martingale pin `STGridMart` at one `C₀` (`3_5:218-240`): hypothesis of `ST_selfImprove_section`
$ git merge-tree --write-tree main t/T2180
f1c33f995a3ca697b8da5d84d274cb96e17b025f            (no conflict)
```
Only the two sole writable files; `STGridRepN` / `GridRepWTailNAt` registry lines kept; no merged file touched (no frozen signature changed).

## 2. Build, forbidden tokens, axioms (audit worktree)
```
$ lake build RBM3D.Path.DifREP2         # exit=0
✔ [3852/3852] Built RBM3D.Path.DifREP2 (14s)
Build completed successfully (3852 jobs).
$ grep -E '^(error|warning)' build.log | grep -c DifREP2      -> 0     (0 error lines in the whole log)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' RBM3D/Path/DifREP2.lean   -> (no output)
$ lake env lean conf.lean   (#print axioms)
'RBM.Ind.azumaRandProxy_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRepTail_condMGF_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridRepTailN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridMart_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridMartAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRep2_peel' / 'difRep2_peel_N' / 'difRep2_norm_STeeM_le' / 'difRep2_norm_STeeM_le_N' /
'difRep2_eeShiftErrN_le' / 'difRep2_eeShift_sum_le' / 'DifREP2Inst.inst_azumaRandProxy_max' / 'inst_peel' /
'inst_peel_N' / 'inst_gridRepTailN': each [propext, Classical.choice, Quot.sound]
```
Registry pre-check (root imports + `import RBM3D.Path.DifREP2` + `#assert_rbm_axioms`, i.e. the root after hub merge step 4):
```
$ lake build RBM3D        # root WITHOUT the new import: root_exit=1 (expected; hub adds the import at merge)
error: RBM3D.lean:228:0: axiom audit: 1 premise(s) ... in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Ind.GridRepTailNAt]
$ lake env lean reg.lean  # root + DifREP2 import
reg_exit=0
axiom audit: 5382 theorems, 1904 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
```
File-level options: only `set_option linter.*` (lines 60-64); no `instance`/`attribute`/`opaque`/`unsafe`; `variable` blocks only `{d : ℕ} (sz : Sizes d)`.

## 3. Statements against the pins (check file §2)
Script: `import RBM3D.Path.DifREP2` + section 2 of the check file verbatim + `example : XStmt := @x` for the five targets, plus a meta comparison of each target's type with its `…Stmt` body.
```
$ lake env lean conf2.lean ; echo exit=$?
RBM.Ind.azumaRandProxy_max: syntactic-equal=false reducible-defeq=true
RBM.Ind.difRepTail_condMGF_Z: syntactic-equal=false reducible-defeq=true
RBM.Ind.gridRepTailN_holds: syntactic-equal=true reducible-defeq=true
RBM.Ind.stGridMart_holds: syntactic-equal=true reducible-defeq=true
RBM.Ind.stGridMartAt_holds: syntactic-equal=false reducible-defeq=true
exit=0
```
The three `false` cases, diffed token-by-token under `pp.all` (script `difflib` on the printed types): every difference is an
instance-proof argument that the check file abstracts into an auxiliary constant, e.g.
```
replace (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 ..) (@Nat.instNeZeroSucc ..)) | RBM.Ind.T2180Check.AzumaRandProxyMaxStmt._proof_1
replace (@MeasureTheory.Measure.instOuterMeasureClass (@RBM.Path.PathΩ d sz) ..)       | (@RBM.Ind.T2180Check.DifRepTailCondMGFZStmt._proof_1 d sz)
replace (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 10 ..) (@Nat.instNeZeroSucc ..)) | RBM.Ind.T2180Check.StGridMartAtHoldsStmt._proof_1
```
No other token differs: hypotheses, quantifier order, the maximal form `∃ k ≤ K` inside `μ.real`, `exp(-x²/(2V))`, the proxy
`Δ k Re Σ_{b,b'} κ_b κ̄_{b'} STeeM_{u_{j+1}}(H_j)`, the window `0 ≤ s n ≤ t n < 1`, `j+1 ≤ K n`, `2 ≤ k`, `∀ d m, 2 ≤ m`, `3 ≤ d`, `C₀ = 11` are identical to the pins.

Target 3 is the merged T2168 pin `GridRepTailNAt d m` (`Path/DifREP1.lean:95`, read): `∀ D > 0, ∃ CK ≥ 0, ∀ K, (∀ n, K n ≠ 0) → (∀ᶠ n, N^CK ≤ K n) → ∀ ε' > 0, ∀ᶠ n, ∀ i, P(∃ k ≤ K n, N^{ε'}(Σ_{j<k} Δ‖STeeM_{u_j}(H_j)_{σ,a,a}‖ + N^{-D})^{1/2} < ‖Mart_k‖) ≤ N^{-D}`. Proof (`DifREP2.lean:2180-2275`): `CK := 2m + 2D + 16` (literal, depends on `m, D` only; fixed before `K` and `ε'`); `N → ∞` from `hz.1.2.2.1 : sz.SizeTendsto` (from `STFlow`), never a premise; no `3 ≤ d`.
Target 4: `stGridMart_holds := stGridMart_of_tail d hd (gridRepTailN_holds d 2 le_rfl)`; `stGridMartAt_holds` from `stGridMartAt_of_parts2 d (2+9)`, `gridRepRemN_holds d hd 2`, target 3 — exactly the ticket's composition.

Amend 2 interface pieces (public, `difRep2_` prefix): `difRep2_norm_STeeM_le(_N)`, `difRep2_eeShiftErrN_le`, `difRep2_eeShift_sum_le` match Amend 2 (i) (`‖STeeM‖ ≤ m N (16N)^{2m+2}` under `1/(16N) ≤ η`). `difRep2_peel_N` is Amend 2 (ii) generalised: threshold increments `a_j` with `v_j ≤ m(a_j + e_j)`, `Σ e_j ≤ N^{-D}`, `Σ a_j ≤ 2^{L} N^{-D}`; the amend's literal form is the specialisation `a = v`, `e = 0` (`v ≤ m v` for `m ≥ 1`, `v ≥ 0`); the amend's `v_j ≤ B` is not required (weaker hypotheses). Conclusion `(L+1)·4·exp(-N^{2ε'}/(64m))` as in the amend.

## 4. Hidden hypotheses, vacuity, cycles
- No target takes a structure argument carrying an assumption; target 1 is model-free; target 2's hypotheses are numeric/window conditions; target 3 is the pin with the merged `STFlow` input.
- Proof dependencies are merged (`difRep_flow_bounds`, `stepDecompCN*`, `qvPropagatedN`, `AzumaProxyN_YfieldsW`, `doob_L2_max`, `martingale_sq_eq_sum`, `stGridMart_of_tail`, `stGridMartAt_of_parts2`, `gridRepRemN_holds`); the axioms output above shows no external hypothesis was introduced; no Lean cycle is possible.
- No new external hypothesis (none needs a limit check). Target 1's hypothesis `v_j ≤ B` is pinned and unused by the proof (prove report narrative 2): stronger theorem, not a defect.

## 5. Compiled nonempty instances (same file, namespace `RBM.Ind.DifREP2Inst`; compiled in §2's build)
```
$ grep -nE '^example|^theorem inst_' RBM3D/Path/DifREP2.lean | cut -c1-110
2375:example := difRepTail_condMGF_Z sz0 E12 sInst tInst (fun _ => 4) 0 0 hE12 (hs0 0) (hst 0) ht0
2385:example := difRep2_norm_STeeM_le sz0 0 (E := E12 0) (u := 1 / 16) hE12 (by norm_num) herm0 σ3 a0 a0
2388:example := difRep2_norm_STeeM_le_N sz0 0 (E := E12 0) (u := 1 / 16) hE12 (by norm_num) herm0
2392:example := difRep2_eeShiftErrN_le sz0 0 (E12 0) (u := 0) (u' := 1 / 64) (by norm_num)
2397:example := difRep2_eeShift_sum_le sz0 E12 sInst tInst (fun _ => 4) 0 3 (hst 0)
2413:theorem inst_azumaRandProxy_max :
2460:theorem inst_peel :
2513:theorem inst_peel_N :
2577:theorem inst_gridRepTailN (m : ℕ) (hm : 2 ≤ m) :
2600:example := inst_gridRepTailN 2 le_rfl
2601:example := inst_gridRepTailN 3 (by norm_num)
2604:example : STGridMart 3 := stGridMart_holds 3 (by norm_num)
2607:example : STGridMartAt 3 11 := stGridMartAt_holds 3 (by norm_num)
2611:example (hLWB : STLWB 3) : STOptL2 3 :=
2617:example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hOpt : STOptL2 3)
```
Read (lines 2309-2621):
- Target 2: `d = 3`, `sz0`, `E ≡ 1/2` (`hE12`), `s ≡ 0`, `t ≡ 1/16` (`ht0`), `K ≡ 4`, `n = j = 0`, `k = 3`, `σ = (+,-,+)`, `κ = δ_{a0}`, `r = 1`: every hypothesis discharged; `Δ = 1/64 > 0` (`gridStep_inst`).
- Target 1: `(PathΩ sz0, pathP sz0, filt sz0)`, `ζ_j = Re Z_{j,a0}`, `v_j` = target-2 proxy, `G_j = univ`, `K = 4`, `B = B3 > 0`, `V = 4·B3`, `x = 1`; measurability, `0 ≤ v_j ≤ B3`, integrability and conditional mgf discharged from the model, `Σ v ≤ V` proved.
- Target 3: `inst_gridRepTailN` at `m = 2, 3` on `z0`/`flow_z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `D = 1`, `ε' = 1/10`, `K n = ⌈N_n^{CK}⌉₊ + 1` for the returned `CK` (`K n ≠ 0` and `N^{CK} ≤ K n` proved).
- Target 4: unconditional at `d = 3`; chain examples keep only other gates' pins (`STLWB`, `STNewKLK`, `STLWT`, `STEMn2Exp`, `STOptL2`, `STLocalAvgOfL2`) as hypotheses, as the ticket lists.
- Amend 2 pieces: each applied at the data (`inst_peel`, `inst_peel_N` with `N = N_0`, `D = 1`, `ε' = 1/10`, `m = 3`).
No `N = 0`, empty index, collapsed window (`t > s`, `K = 4`) or `False` premise.

## 6. Paper deltas
Report (d) proposes `T2180a` (BDG `(aaswtghh)` + Markov → maximal exponential bound with a predictable proxy, uniform in `K`, with D90), `T2180b` (proxy at `u_{j+1}` moved to `u_j` at cost `O(N^{2m+4}Δ)`), `T2180c` (`Y` by Doob L² in the `N^{-D}` floor), `T2180d` (`CK = 2m+2D+16`; tail for every `d`), `T2180e` (`STGridMart`, `STGridMartAt d 11` unconditional for `3 ≤ d`, `C₀ = 11` explicit vs paper `C₀(d)`), `T2180f` (Lean device `YvecN := martIncN − ZvecN`). `grep -n 'T2039h' docs/paper-deltas.md` → `403: D90 (T2039h)` present. These cover every Lean/paper difference found in §3 (targets 1–2 and the `difRep2_*` pieces are Lean-only tools with no paper statement; their role is described in T2180a/b).

## 7. Verdicts
| target | verdict |
|---|---|
| 1 `azumaRandProxy_max` | PASS |
| 2 `difRepTail_condMGF_Z` | PASS |
| 3 `gridRepTailN_holds` | PASS |
| 4 `stGridMart_holds`, `stGridMartAt_holds` | PASS |
| registry edit (`Test/Axioms.lean`, two owed lines) | PASS (pre-check exit 0 with the new import) |

Overall: **PASS**. No dispatcher sign-off needed.

## 8. Observations (no RETURN)
- O1 (merge, hub): `main` changed `RBM3D/Test/Axioms.lean` (+21/−3) and `RBM3D.lean` (+9) since the merge base `4c52041`. The branch's `Test/Axioms.lean` must be brought in as the 2-line deletion (`git merge-tree` is clean, tree `f1c33f9`), not by copying the branch file over `main`'s, which would revert main's 21 lines.
- O2 (merge, hub): the root `lake build` fails until `import RBM3D.Path.DifREP2` is added (registry deletion of `GridRepTailNAt`); with the import the pre-check exits 0 (§2).
- O3: the target-1 instance uses the ticket-prescribed crude `V = 4·B3` (`B3 ≈ 10^{65.7}` per report (a)(ii)), so its conclusion is `≈ 1 − 10^{-67}`. Every hypothesis is discharged at real model data; the size of `V` comes from the ticket's chosen `B`, not from a weakened hypothesis.
- O4: the `STOptL2` registry comment (`Test/Axioms.lean:126` on the branch) is stale once `STGridMart` is proved; left for the dispatcher, as the ticket says (report (d)(3)).
- O5: `difRep2_peel_N` states exponent `64m`; the proof gives `16m` (report narrative 5(iii)). This is the amend's form, so it is not a defect.
