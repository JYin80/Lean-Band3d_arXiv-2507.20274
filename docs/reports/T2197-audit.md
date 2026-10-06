Auditor model: claude-opus-5-5

# T2197 audit (round 1) — Tue Oct  6 00:20:19 UTC 2026
Ticket `docs/tickets/T2197.md` + `T2197-amend-1.md` + `T2197-amend-2.md` (amendments govern); branch `t/T2197` at `e854613`;
audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2197-audit1` (detached). `$A` = scratchpad `T2197/audit`.

## 1. Diff scope, forbidden tokens, build
```
$ git diff --name-only main...HEAD
RBM3D/BA/FlowPins.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep -E '^[-+]' | grep -vE '^\+\s+(`RBM|--)'   # non-registry lines: headers only
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
$ grep -nwE 'sorry|admit|native_decide|axiom' RBM3D/BA/FlowPins.lean      # (no output)
$ lake build RBM3D.BA.FlowPins 2>&1 | tail -n 2
Build completed successfully (3734 jobs).
exit=0
$ grep -E '^(error|warning)' $A/build.out | grep -c FlowPins   # 13 warnings in total, all upstream
0
$ lake build RBM3D 2>&1 | grep -E 'Build completed|^error'      # branch root library (FlowPins not yet imported)
Build completed successfully (4029 jobs).
```
Imports: `RBM3D.BA.MFixedPoint`, `.Induction.Defs`, `.Induction.Step2Defs`, `.Loop.KLTree` (allowed set).

## 2. Statements against the check file (compiled; `$A/cmp.lean` = check sections 2-4 verbatim + the lines below, `import RBM3D.BA.FlowPins`)
```
example : @RBM.BA.BASelfFine = @RBM.BA.T2197Check.BASelfFine := rfl
example (d L W : ℕ) [NeZero L] [NeZero W] : T2197Check.BAMres_fine_kron_stmt d L W := BAMres_fine_kron d L W
example (d L W : ℕ) [NeZero L] [NeZero W] : T2197Check.BAMres_fine_apply_stmt d L W := BAMres_fine_apply d L W
example (d L W : ℕ) [NeZero L] [NeZero W] : T2197Check.BAfine_trace_stmt d L W := BAfine_trace d L W
example (d L W : ℕ) [NeZero L] [NeZero W] : T2197Check.BASelf_iff_fine_stmt d L W := BASelf_iff_fine d L W
example : @RBM.BA.BAProp5 = @RBM.BA.T2197Check.BAProp5 := rfl      -- same for BAProp5s, BAProp6, BAProp7, BAProp8
example : @RBM.BA.PrecL = @RBM.BA.T2197Check.PrecL := rfl
$ lake env lean $A/cmp.lean; echo exit=$?
(only the #print axioms lines of §4)
exit=0
```

## 3. Statements against the probes (independent script `$A/pdiff.py`, `$A/tokdiff.py`; whitespace-normalised token diff)
```
$ python3 $A/pdiff.py $A          # T2161 82e72b3 :661-1191 vs FlowPins.lean :160-660; T2173 a543154 :1932-2055
probe T2161 :661-1191 decls 64 identical 29 differ 30 absent in FlowPins 5
absent: BAMainInd BAGbEXPpre BAGbEXPconcl BAGbEXP BAStep1
FlowPins decls (lines 160-660) not in probe T2161 by name: PrecL
T2173 :1932-2055 decls 14 in FlowPins 14 identical 13 differ FlowFM.GM
$ python3 $A/tokdiff.py $A        # every distinct token edit over the 30 differing declarations (count)
17 [] -> [(Sizes.seqP sz)]                       11 [] -> [(law sz)]
14 [Prec] -> [PrecL]                             13 [] -> [μ]
 2 [] -> [(Sizes.seqP (sz.withLam 0))]            2 [Whp sz] -> [HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size]
 1 [∂(sz.seqP))] -> [∂μ)]                         1 [] -> [(law : ∀ sz : Sizes d, Measure sz.SeqΩ)]
 1 [] -> [(fun sz => Sizes.seqP sz)]              1 [BAConArg] -> [BAConArg']
 1 [STLmaxg] -> [(∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) → STLmaxgL]
 3-4 each: [STXg] -> [STXgL] for the 12 carrier predicates (renaming L1)
BAConArg :: [BAConArg] -> [BAConArg'] | [STLmaxg] -> [(∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) → STLmaxgL] | [] -> [(Sizes.seqP (sz.withLam 0))]
```
Every edit is L1 (μ after `C`, `Prec sz ↦ PrecL sz μ`, `∂(sz.seqP) ↦ ∂μ`, suffix `L`), L2 (`law`, `(law sz)`),
L3 (`Sizes.seqP (sz.withLam 0)`, `Whp ↦ HighProbAt (…)`), L4 (`Sizes.seqP sz` in the bridges) or L5 (Amend 1: the
premise `κ ≤ Im m(E_n, g_s)` inserted right after `(∀ n, t n < 1) →`). The five absent declarations are removed by
Amend 1 (`BAMainInd`, `BAStep1`) and Amend 2 line 3 (`BAGbEXP*`). `FlowFM.GM` differs from T2173 in binder syntax only
(the prove report's b.5 gives the same counts; `cmp.lean` and the full build typecheck all uses).

§57 (3) grep (`grep -nE "Prec sz|Whp sz|sz.seqP|seqP sz" RBM3D/BA/FlowPins.lean`), matching lines:
```
321 326 488 489 491 … 513 (bandFM_* bridges) 581 584 (STMainInd_iff) 610 (docstring) 642 649-653 (STStep1_iff)
1465-1506 (band-bridge examples at sz0) 1521 (docstring)
```
No BA statement uses `Prec sz`/`Whp sz`/`seqP sz`; BA statements carry `Sizes.seqP (sz.withLam 0)` (lines 555-635, 983, 1094).

## 4. Axioms (`#print axioms` in `$A/cmp.lean`)
```
'RBM.BA.BAMres_fine_kron' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMres_fine_apply' / 'BAfine_trace' / 'BASelf_iff_fine' / 'baSelf_none_of_gt' / 'BAConArg'_premise_diag' /
'not_BAConArg_of_data' : [propext, Classical.choice, Quot.sound]   (each printed separately, identical)
'RBM.BA.FlowPinsInst.inst_selfFine' / 'inst_selfFine_real' / 'inst_apply_concrete' / 'flow_sz0' / 'inst_BAConArg'' /
'BAMfine_sz0_kron' / 'inst_premise_diag' / 'seqGvar_ne_withLam_zero' / 'inst_BAProp5' : [propext, Classical.choice, Quot.sound]
```
Registry pre-check (DECISIONS §20 (2)): `import RBM3D`, `import RBM3D.BA.FlowPins`, `#assert_rbm_axioms`:
```
$ lake env lean $A/precheck.lean; echo exit=$?
axiom audit: 6669 theorems, 2299 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.BAProp5: 1 … RBM.BA.BAProp8: 1   RBM.BA.BAProp5to8: 0   RBM.BA.BAConArg': 1   RBM.BA.STLmaxgL: 3
premises found by scanning: 132 (borrowed 1, owed 99, structural 26, refuted 6).
exit=0
```
Registered (owed): `BAProp5, BAProp5s, BAProp6, BAProp7, BAProp8, BAProp5to8, BAConArg', STLmaxgL` — the premises that
occur; `BAMainInd/BAStep1/BAGbEXP` not registered (deferred); no line for the private `BAConArg` (Amend 1).

## 5. Per target
**Target 1 (D472): `BASelfFine`, `BAMres_fine_kron`, `BAMres_fine_apply`, `BAfine_trace`, `BASelf_iff_fine` — PASS.**
Statement = check section 2 by `rfl`/term (§2). Only hypotheses: `(z+m).im ≠ 0` (1a-1c), `0 ≤ z.im` (1d); no `3 ≤ L`,
`0 < g`, `3 ≤ d` — the general statement for every `d, L, W ≥ 1`. Proof is a genuine Kronecker/`Ring.inverse`/trace
argument (`FlowPins.lean:70-151`), no structure hypothesis. Instances (`FlowPinsInst`, compiled): `inst_kron`,
`inst_apply`, `inst_trace`, `inst_selfFine` at `(3,4,2,10,i)`, `m = BAm 3 4 10 i` (`N = 512`), hypothesis discharged by
`im_I_add_m` from `BAm_self`; `inst_apply_concrete` (two explicit entries: offset differs → `0`; same offset → `M^{(B)}_{0,e₁}`);
`inst_selfFine_real`, `inst_kron_real` at the real flow point `P` from `P.real.1`; `BAMfine_sz0_kron n` for every `n`.
**Target 2 (PT pins `BAProp5`, `BAProp5s`, `BAProp6`, `BAProp7`, `BAProp8`, `BAProp5to8`) — PASS.** Verbatim probe
(§3: identical) and = check section 3 (`rfl`). Stated only, owed. Instances `inst_BAProp5…8` keep only the pin as
hypothesis and discharge `3 ≤ 3`, `0 < 10`, `0 < Im m₀` (`P.real.1.1`), `3 ≤ 4`, `0 < g₀ ≤ 10`, `BAReal` (`P.real`),
`t = 1/2 ∈ [0,1)`, and for 6/7 `|r| = 1 ≤ (1/2)|a| = 1` with `a = (2,0,0)`, `r = (1,0,0)` (`zd_a`, `zd_r` by `decide`):
window not collapsed.
**Target 3 (flow `BAmF … BAGM`) — PASS.** Verbatim (§3). Used nondegenerately by `BAMfine_sz0_kron`, `BAmF_sz0_eq`.
**Target 4 (carrier over a law, `PrecL`, 12 `…gL` predicates, `STmaxLoop2g`, `STJhatg`, `STEEg`, `bandFM`, `baFM`,
13 bridges) — PASS.** Edits are L1/L4 only (§3); `FlowFM` fields are data (no `Prop` field: `FlowPins.lean:332-346`).
Bridges are `Iff.rfl`/`rfl` and compile; applied at `sz0` (examples `:1479-1512`). Law not vacuous:
`seqGvar_ne_withLam_zero` (∃ coordinate whose variance differs under `seqP sz0` and `seqP (sz0.withLam 0)`) and
`svarF_ne_zero_profile` (T2173 text) compile.
**Target 5 as amended (`BAflowT0`, `BAflowEs`, `BAflowLam0`, `BAFlow`, `baFMz`, `STMainIndG`, `STMainInd_iff`, `BAvecEntry`,
`BAlamS`, `BAConArgLoop`, `BAConArgVec`, `BAConArg'`, `STStep1_iff`) — PASS.** L2-L5 only (§3); `BAConArg'` = Amend 1 text
(premise inserted at the specified place). `STMainInd_iff 3`, `STStep1_iff 3` applied as examples. Instance
`inst_BAConArg'` at `sz0`, `zSeq`, `(κ,ε,𝔡,ε₁,𝔠) = (1/2,1/10,1/10,1/2,1/6)`, `s ≡ t ≡ 1/2` (Amend 2 line 1): `BAFlow` by
`flow_sz0` (`sz0_admissible`, `BAdom` at every `n`, no `BAmExists` hypothesis: grep finds `BAmExists` only in a docstring),
ranges by `norm_num`, the L5 premise by `BAConArg'_premise_diag`; left as hypotheses only the pin `BAConArg' 3` and the
stochastic premise `STLmaxgL` (registered owed). `t0_sz0`: `2/3 ≤ t₀_n`, so `s = t = 1/2 < t₀_n` (`half_lt_t0`).
**Extra (a) `baSelf_none_of_gt` (+ `BAm_eq_zero_of_gt`, `BArho_eq_zero_of_gt`) — PASS.** `∀ m, ¬ BASelf d L g E m`
under `2 + 2d|g| < |E|`, `g` real of either sign, as Amend 1 (a). Instances `inst_none_pos` (`g=1, E=9`), `inst_none_neg`
(`g=-1, E=-9`), `inst_BAm_zero`, `inst_BArho_zero`; sanity `inst_flowPt_inside` (hypothesis fails at `P`).
**`BAConArg'_premise_diag` — PASS.** General (`∀ sz z`, `BAFlow`, `t > 0`); instance `inst_premise_diag` at `sz0`.
**Extra (b) `not_BAConArg_of_data` — PASS (conditional, as Amend 2 line 2 states).** Hypotheses = those of the
unrepaired `BAConArg` (private def; token diff vs probe `:1160-1166`: `[] -> [private]`, `[STLmaxg] -> [STLmaxgL]`,
`[] -> [(Sizes.seqP (sz.withLam 0))]`, i.e. L1-L4 only) plus
`∀ n, 2 + 2d|g_s| < |E_n|`. No compiled instance: Amend 2 line 2 waives it ("no instance of (b) is required"); nothing
depends on it (`¬ BAConArg d` of a private def). See observation 1.

## 6. Paper deltas
```
$ grep -nE 'D472|D536|T2173a' docs/paper-deltas.md | cut -c1-60
1402:- **D443（T2173a）**：T2161 的 BA 钉文写在 `sz.seqP` 下…
1431:- **D472（T2189b）**：`(self_m)` 论文是精细 `N × N` 矩阵上的 `N⁻¹ tr`…
1495:- **D536（T2205b）**：`lem:main_ind_BA` 的 Step 1 … 要 `Im m(E, g_s) ≥ κ`（缺这条 `BAConArg` 为假，F1）…
```
Coverage of every Lean/paper difference: law `seqP (sz.withLam 0)` → D443; target 1 closes D472 → candidate **T2197a**;
coupling `g` vs `g₀` in the carrier controls and gates → **T2197b** (open, as the ticket asks, with the preflight's reading);
`BAConArg'` premise → D536 and **T2197c**; `baSelf_none_of_gt` → **T2197d**; PT pins are the T2161 text (T2161 deltas).
All covered.

## 7. Observations (no RETURN)
1. `not_BAConArg_of_data` has no compiled instance, so satisfiability of its hypotheses (`BAFlow` with
   `2 + 2d|g_s| < |E_n|` for all `n`, plus `STLmaxgL`) is not shown in Lean; Amend 2 waives the instance and it is a
   refutation record only. Its hypothesis uses `|BAlamS …|` where Amend 2 writes `BAlamS …` (same when `g_s ≥ 0`;
   stronger hypothesis otherwise); listed in prove report b.7.
2. `mS_im_half` keeps its probe name but now states `4/5 ≤ Im m_S` (prove report (d)(5)).
3. T2197b (coupling) is not decided; its main consumer `BAMainInd` is deferred to BA-D3, which should settle it.
4. 13 build warnings in the module build, none in `FlowPins.lean` (all from upstream files, e.g. `Defs/Tail.lean`).

## Verdict
Targets 1-5 (as amended), extras (a), (b), `BAConArg'_premise_diag`: **PASS**. No dispatcher sign-off needed.
