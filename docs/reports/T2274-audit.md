Auditor model: claude-opus-5-5
# T2274 audit (round 1) — S3-21 `Induction/QtNonzero` — Tue Oct  6 10:05:18 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2274-audit1`, detached at `67f6489` (`t/T2274`), merge base `b2529ba`; scratch `<scratchpad>/T2274/`.

## 1. Diff scope and hygiene
```
$ git diff --name-only main...t/T2274
RBM3D/Induction/QtNonzero.lean
$ git diff --stat main...t/T2274 | tail -1
 1 file changed, 1726 insertions(+)
$ git diff main...t/T2274 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l   ->   0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom|maxHeartbeats" RBM3D/Induction/QtNonzero.lean; echo exit=$?
exit=1            (no hits)
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev)" QtNonzero.lean   (non-private declarations)
97 zeroModeSet_idem  224 cQVNZN  233 assembledRHSNZN  299 nzUgen_holds  327 nz_hker  358 nz_hdriftN
417 subGaussStop_nzN  731 yMomentBounds_nzN  872 budgetNZN   + 10 theorems in namespace RBM.Ind.QtNonzeroInst
(all other helpers `private`, prefix `qtNZ_`/`qn`)
$ git grep -n -F -w <name> main -- RBM3D RBM3D.lean | wc -l   (main = 66cddb4, after T2270/T2273/T2275/T2276)
zeroModeSet_idem:0 cQVNZN:0 assembledRHSNZN:0 nzUgen_holds:0 nz_hker:0 nz_hdriftN:0 subGaussStop_nzN:0 yMomentBounds_nzN:0 budgetNZN:0 QtNonzeroInst:0
```
Only the sole writable file is touched; no merged file, registry line or frozen signature changed.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.QtNonzero ; echo exit=$?
Build completed successfully (3845 jobs).   exit=0   (errors in log: 0; warnings in QtNonzero.lean: 0)
$ (parse of the `#print axioms` lines of QtNonzero.lean:1708-1726 in build.log)
1708 RBM.zeroModeSet_idem [propext, Classical.choice, Quot.sound]
1709 RBM.Ind.cQVNZN [propext, Classical.choice, Quot.sound]
1710 RBM.Ind.assembledRHSNZN [propext, Classical.choice, Quot.sound]
1711 RBM.Ind.nzUgen_holds [propext, Classical.choice, Quot.sound]
1712 RBM.Ind.nz_hker [propext, Classical.choice, Quot.sound]
1713 RBM.Ind.nz_hdriftN [propext, Classical.choice, Quot.sound]
1714 RBM.Ind.subGaussStop_nzN [propext, Classical.choice, Quot.sound]
1715 RBM.Ind.yMomentBounds_nzN [propext, Classical.choice, Quot.sound]
1716 RBM.Ind.budgetNZN [propext, Classical.choice, Quot.sound]
1717 RBM.Ind.QtNonzeroInst.idem_instance [propext, Classical.choice, Quot.sound]
1718 RBM.Ind.QtNonzeroInst.nzUgen_instance [propext, Classical.choice, Quot.sound]
1719 RBM.Ind.QtNonzeroInst.nz_hker_instance [propext, Classical.choice, Quot.sound]
1720 RBM.Ind.QtNonzeroInst.nz_hdrift_instance [propext, Classical.choice, Quot.sound]
1721 RBM.Ind.QtNonzeroInst.nz_hdrift_level_pos [propext, Classical.choice, Quot.sound]
1722 RBM.Ind.QtNonzeroInst.subGaussStop_nz_instance [propext, Classical.choice, Quot.sound]
1723 RBM.Ind.QtNonzeroInst.cQVNZN_inst_pos [propext, Classical.choice, Quot.sound]
1724 RBM.Ind.QtNonzeroInst.yMoment_zero_instance [propext, Classical.choice, Quot.sound]
1725 RBM.Ind.QtNonzeroInst.yMoment_random_instance [propext, Classical.choice, Quot.sound]
1726 RBM.Ind.QtNonzeroInst.budgetNZN_instance [propext, Classical.choice, Quot.sound]
```
Registry pre-check (root of the branch, then the new module on top):
```
$ lake build RBM3D            -> info: RBM3D.lean:317:0: axiom audit: 7934 theorems, 2615 definitions, 0 axioms in `RBM` ...  rootexit=0
$ lake env lean pre_after.lean   (import RBM3D; import RBM3D.Induction.QtNonzero; #assert_rbm_axioms)
axiom audit: 7951 theorems, 2617 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit=0
registry message identical except counts: True     (no new unregistered premise; owed `STOeqQtNZ'` unchanged)
```

## 3. Statements against the pins (check file `docs/tickets/checks/T2274-check.lean`)
`stmt.lean` = `import RBM3D.Induction.QtNonzero` + the check file verbatim (sections 1–4) + inside `namespace RBM.Ind.T2274Check`:
```
example : T2274_zeroModeSet_idem := @RBM.zeroModeSet_idem
example : T2274_nzUgen := @RBM.Ind.nzUgen_holds
example : T2274_nz_hker := @RBM.Ind.nz_hker
example : T2274_nz_hdriftN := @RBM.Ind.nz_hdriftN
example : T2274_subGaussStop_nzN := @RBM.Ind.subGaussStop_nzN
example : T2274_yMomentBounds_nzN := @RBM.Ind.yMomentBounds_nzN
example : T2274_budgetNZN := @RBM.Ind.budgetNZN
example : @RBM.Ind.cQVNZN = @RBM.Ind.T2274Check.cQVNZN := rfl
example : @RBM.Ind.assembledRHSNZN = @RBM.Ind.T2274Check.assembledRHSNZN := rfl
$ lake env lean stmt.lean ; echo exit=$? ; grep -c error stmt.out
exit=0
0
$ python3 difflib of the definition text (check §2 vs file)
cQVNZN check lines 5 file lines 5 diff lines 0
assembledRHSNZN check lines 12 file lines 12 diff lines 0
```
The seven theorems have exactly the pinned types; the two definitions are verbatim and definitionally equal.
Hence hypotheses, quantifier order (`∀ d k Λg κ', ∃ C, ∀ L g E v w σ A`), the case-(ii) window `0 ≤ v`, `1 − g²/L² ≤ v ≤ w < 1`,
`STIdiff σ ⊆ A`, the levels and the six budget premises are exactly the ticket's.

## 4. Hidden hypotheses, vacuity, cycles
```
$ sed -n 316-319p QtNonzero.lean   (proof of nzUgen_holds)
  obtain ⟨C, hC, H⟩ := ekSumDecayNonzero_holds d k Λg κ' (prop5Short_holds d Λg κ')
    (prop8ZeroMode_holds d Λg κ') hd hk hΛg hκ'
$ grep -n "^theorem prop5Short_holds\|^theorem prop8ZeroMode_holds\|theorem ekSumDecayNonzero_holds"
Prop5Short.lean:400:theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
Prop5Hold.lean:1266:theorem prop8ZeroMode_holds (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ := by
Nonzero.lean:146:theorem ekSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNonzero d n Λ κ := by
```
- Target 4 is unconditional (merged EK-5 with both of its inputs discharged by merged theorems); no external
  hypothesis, so no limit check is owed.
- No new structure; the merged predicates in binders (`GoodSetN`, `GoodLinN`, `YMomentBoundsN`, `SubGaussStopN`)
  are unchanged merged definitions. Targets 5–7 carry as premises exactly what the pins carry (operator bound
  for target 5, `∃κ` row for target 7; both supplied by target 4 in the case-(ii) window).
- Imports are merged modules only (`ZeroModeCalc`, `NQLin`, `GridAssemblyN`, `AzumaProxyN`, `QVN`, `ScaleFacts`,
  `Step34Pins`, `Evolution.Nonzero`, `Prop5Hold`, `Prop5Short`); no cycle; no conclusion pin is proved or assumed.

## 5. Compiled nonempty instances (namespace `RBM.Ind.QtNonzeroInst`; all compiled in §2's build)
| target | instance (line) | data / discharge | verdict |
|---|---|---|---|
| 3 idem | `idem_instance` (1193) | `d=3, L=4, A=I_diff(+,−,+)={0,1}`, `T=δ₀`; also `δ₀≠0`, `Q^Aδ₀≠δ₀`, `Q^Aδ₀≠0` (`(Q^Aδ₀)(0)=(63/64)²`) | nondegenerate |
| 4 nzUgen | `nzUgen_instance` (1217) | `nzUgen_holds 3 3 _ _ 1 (1/2)` at `L=4, g=1, E=0` (`Im mE 0 = 1 ≥ 1/2`), `v=15/16=1−g²/L², w=31/32`, `σ=(+,−,+)`, `A=STIdiff σ`, `X=δ₀`, row at `a=0`; every hypothesis by `norm_num` | nondegenerate |
| 5 hker | `nz_hker_instance` (1260) | `szB`, `n=0`, `K=1`, `u_i=15/16+i/32`, operator premise from `nzUgen_holds` at each pair, `X=Q^Aδ₀≠0` (class membership by `zeroModeSet_idem`) | nondegenerate |
| 6 drift | `nz_hdrift_instance` (1289) + two `example`s (`A=∅`, `A=STIdiff σ`, `j=0`, every `ω`, via `nqLinExitTauN_pos`) + `nz_hdrift_level_pos` (level `>0`) | `sz0` of `NQLinInst`, GoodLinN premise by `mem_of_lt_nqLinExitTauN` | nondegenerate |
| 7 subGauss | `subGaussStop_nz_instance` (1345), `cQVNZN_inst_pos` (1372) | `sz0`, grid `(0,1/32,4)`, `tau0` (`tau0_pos`: positive at every sample), `goodExitMeasN`, `tau0_mem`, shift `delta_shift_ok`, `∃κ` from private `qtNZ_row_coarse` with `C = 2^{|A|}(32/31)³`; proxy `>0` | nondegenerate (see O2) |
| 8 Y-moments | `yMoment_zero_instance` (1412, `Y≡0`) and `yMoment_random_instance` (1515): Gaussian `Y_j = ζ_j δ₀`, `Y_0 ≠ 0` and `Q^A Y_0 ≠ 0` at some sample, levels `R²Eζ²`, `R⁴Eζ⁴` | the random one applies `yMomentBounds_nzN` (line 1585) | nondegenerate |
| 9 budget | `budgetNZN_instance` (1660) | `sz0` (`N=2^21`, `W=32`, `L=4`), `k=3`, `C=5`, `cA=4`, `ε₀=9`, `ε₁=2/21`, `εq=1`, `D''=5`, `D_Y=1`, `D_t=−5`; `hlog`, `hR` = merged `NQBudgetInst` instances; H1–H6 numerically | discharged (see O1) |

Targets 3–9 are each applied at concrete data with every hypothesis discharged; no `N=0`, empty index, collapsed
window or `False` premise (`Y ≡ 0` alone would be degenerate for target 8; the random instance covers it).

## 6. Paper-delta coverage
Statement differences against `3_5:1546-1559, 1666, 1889-1928` and the report's candidates (`(d)` of the prove report):
- loss-free deterministic `‖Q^A𝒰X‖ ≤ C‖X‖` instead of `≺`; no decay class/far part/ratio weight → `T2274a`.
- Azuma via row sum of `Q^A∘𝒰` and pointwise `ee` bound instead of BDG + `(sahwNQ2)` → `T2274b`.
- separate `Y` part with levels `4^{|A|+1}v`, `16^{|A|+1}w` (Lean device) → `T2274c`.
- explicit `D''`, `D_Y`, `D_t`, `C`, `cA = 2^{|A|}` replacing `W^{-D}`/`≺` in the budget → `T2274d`.
- `εK ≡ 0` (`+ 0 * δ` in `nz_hker`) and the class "fixed point of `Q^A`" are the merged `GridAssemblyHypN.hker`
  shape at this data; covered by `T2274a` (no decay class). No uncovered difference found.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1 (budget instance regime). `budgetNZN_instance` uses `ε₀ = 9`, `εq = 1`, `D_t = −5` at `N = 2^21`, i.e. outside
  the small-`ε₀` regime; this is the regime of the merged precedent the ticket prescribes
  (`NQLin.lean:1724-1729`: `budgetNonAltLinN_instance` with `D_t = −5`, `ε₀ = nqGood1C … + 12`). Satisfiability of
  H1–H6 at small `ε₀` for large `N` rests on the preflight G2 table only. The same G2 rows report that the
  ticket's suggested `D'' = 2k+4d+10` makes H4 false for `W = N^𝔠` with small `𝔠` (e.g. `𝔠=1/3, k=6`:
  coefficient `+0.246`), while `D'' = 2(k+2)/𝔠` works. `D''` is a free real in the pin, so nothing here is
  affected; the S3-22a ticket should choose `D''` accordingly (dispatcher note, not a defect of T2274).
- O2 (instance (5) data). The ticket asked for "the row of (2) as the `∃κ` premise" at the `sz0` grid; that row
  lives in the case-(ii) window `[15/16, 1)` at `szB`, while the `sz0` grid is `[0, 1/32]`, so the prover used the
  coarse row `qtNZ_row_coarse` (disclosed in the prove report, narrative 9). The premise is still a deterministic
  hypothesis discharged at concrete data; the target does not require the case-(ii) window.

## 8. Verdicts
| target | statement | hidden hyp./vacuity | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `cQVNZN` | verbatim (0 diff, `rfl`) | — | used | ok | — | PASS |
| 2 `assembledRHSNZN` | verbatim (0 diff, `rfl`) | — | used | ok | — | PASS |
| 3 `zeroModeSet_idem` | = pin | none | ok | ok | n/a | PASS |
| 4 `nzUgen_holds` | = pin | none (EK-5 unconditional) | ok | ok | T2274a | PASS |
| 5 `nz_hker` | = pin | none | ok | ok | T2274a | PASS |
| 6 `nz_hdriftN` | = pin | none | ok | ok | — | PASS |
| 7 `subGaussStop_nzN` | = pin | none | ok (O2) | ok | T2274b | PASS |
| 8 `yMomentBounds_nzN` | = pin | none | ok | ok | T2274c | PASS |
| 9 `budgetNZN` | = pin | none | ok (O1) | ok | T2274d | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed for this ticket; O1's `D''` remark is input for the S3-22a draft.
