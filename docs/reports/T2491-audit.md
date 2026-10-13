Auditor model: claude-opus-5-5
# T2491 audit, row U3s2a (targets 1-6) — Tue Oct 13 07:34:37 UTC 2026
Branch `t/T2491` HEAD `ae93f0a2`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2491-audit1` (detached at ae93f0a2), merge base `7be99aae`,
`main` `0a68e61d`. Scope: `Chain/NQGood1Gen` (targets 1-3) + `Chain/NQGood2Gen` (targets 4-6), per the 1a-audit (`T2491-1a-audit.md`,
pre-signed rows a/b/c). U3s2b (7-10), U3s2c (11-15) are later stacked rows, not a defect here. Scratch: scratchpad `T2491/` (uncommitted).

## 1. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Chain.NQGood1Gen RBM3D.Chain.NQGood2Gen      (07:29:36 -> 07:29:53 UTC; fresh oleans written in the audit worktree)
Build completed successfully (3877 jobs).   exit 0
$ lake build      (full library, branch root imports incl. RBM3D.Chain.NQGood1Gen/NQGood2Gen; 07:30:17 -> 07:31:35 UTC)
premises found by scanning: 128 (borrowed 1, owed 61, structural 46, refuted 6, superseded 14).
Build completed successfully (4354 jobs).   exit 0      (error lines: 0; `#assert_rbm_axioms` passed)
$ grep -hE "^(theorem|lemma|def|abbrev|structure) " NQGood1Gen.lean NQGood2Gen.lean | awk '{print $2}' > names.txt; wc -l  -> 55
$ lake env lean axioms.lean   (#print axioms RBM.BA.<each of the 55>)        exit 0
55 of 55 lines: depends on axioms: [propext, Classical.choice, Quot.sound]; other lines: none
$ grep -nE 'sorry|admit|native_decide|^axiom|withLam|^import RBM3D.BA' NQGood1Gen.lean NQGood2Gen.lean | wc -l   ->  0
$ git diff --name-only main...t/T2491
RBM3D.lean  RBM3D/Chain/NQGood1Gen.lean  RBM3D/Chain/NQGood2Gen.lean  RBM3D/Probe/T2491Pins.lean  RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Defs | wc -l   ->  0      (G1: band and merged files untouched)
$ wc -l NQGood1Gen.lean NQGood2Gen.lean   ->  836, 687   (stop line 2,000 per file)
$ grep -rln "import RBM3D.Chain.NQGood[12]Gen" RBM3D RBM3D.lean   ->  RBM3D/Chain/NQGood2Gen.lean, RBM3D.lean
$ lake env lean docs/tickets/checks/T2491-check.lean   ->  exit 0, error lines 0
```
All five touched files are sole writable files. `Test/Axioms.lean`: one comment line (owner text of `GoodSetNg`), the ticket's
registry text ("hQ: generic `hQ_nonAltNg` (T2491)"); no `owedProps` name added or removed; the scan passes.

## 2. Ticket hypothesis rules (greps over the two files)
```
U-C4  def .*[Kk]er\b|def Ugen: 0      TN-C4  STGridRepNgL|ST_gridMart_of_repN: 0      X1-C4 (def|abbrev|structure of merged pins): 0
U5S-C3  ∀ (sz : Sizes d):  NQGood1Gen.lean:67, 68, 70 only (= NQGoodGen_KerNALFam, the pinned D1 family text, guarded by Flow)
GridDriftNg|HierarchyNg: 1 hit, NQGood1Gen.lean:121 (docstring of driftTensorNg); no public premise (DECISIONS §294 (3) (9))
X1-C1 regex: NQGood1Gen 55, NQGood2Gen 23 hits; inside generic public statements (band bridges, hQ_nonAltN_of_Ng, Inst excluded):
  only the lemma names etaT_inv_shiftNg_le:460, loopFine_shiftNg_le:488, norm_loopFine_crudeNg:581 (names, not band objects)
```

## 3. Statements against the pins (script)
```
$ diff <(awk-extract check "def T2491_KerNAL " | sed s/T2491_KerNAL/NQGoodGen_KerNAL/g) <(awk-extract NQGood1Gen "def NQGoodGen_KerNAL ")
diff 0 (10 lines)
$ diff <(… "def T2491_KerNALFam" …) <(… "def NQGoodGen_KerNALFam")
diff 0 (5 lines)
$ lake env lean audit_pins2.lean     (check defs T2491_HQg, T2491_KerNAL, T2491_KerNALFam copied by awk from the check file, then:)
  example : @T2491_KerNAL = @NQGoodGen_KerNAL := rfl
  example : @T2491_KerNALFam = @NQGoodGen_KerNALFam := rfl
  example <the full telescope of hQ_nonAltNg> : T2491_HQg Cm s v K n k σ Γ Λ Φ τ' D' m a j (cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j)
    := hQ_nonAltNg hd hL hm hS hcmp hA hKer hRow hCv hs0 hsv hv1 hwL hWt hW hε0 hε1 hWε hdW hAk hD'' hσ Γ Λ Φ hΛ m hmK a j hj hδ
  example … : GridAssemblyHypNg Cm σ (gridTime s v K n) (goodExitTauNg …) Δ (K n) (nonAltClsN … τ' D' (gridTime s v K n))
      (AvecNg Cm s v K n 0 σ) A' (driftTensorNg …) Z Y R (kappaNonAltNg k Cv …) (epsNonAltNg Cv W) (W^-D') (dDriftNonAltNg …) (W^-D')
      (cQVNonAltNg … Cv …) vv w stepErr where
    hker := nonAlt_hkerNg …; hκ0 := nonAlt_hκ0Ng …; hε0 := nonAlt_hε0Ng …; hA0cls := nonAlt_hA0clsNg …; hdDrift0 := nonAlt_hdDrift0Ng …;
    hdrift := nonAlt_hdriftNg …; hDcls := nonAlt_hDclsNg …; hc_pos := cQVNonAltNg_sum_pos …; hKer := hRow; (hexp, hY, hR, … as hypotheses)
exit 0 (only unused-variable warnings of the scratch)
$ lake env lean band_eq.lean    (types of RBM.BA.hQ_nonAltN_of_Ng and RBM.Ind.hQ_nonAltN)
types of hQ_nonAltN_of_Ng and band hQ_nonAltN: syntactically equal = true, defeq = true
```
Read against the ticket's mathematics (UBA-C1, D1, D3), by signature:
- **T1 (D1).** `NQGoodGen_KerNAL`/`…Fam` equal the 1a-audit-fixed check text (diff 0, `rfl`); `∃ Ck` after `(k, κ, ε, 𝔡)`, before
  `(sz, 𝔠, z)` (no F1). Band discharges `nqGoodGen_kerNAL_band_at` (per index, `Ck = nqGood1C d k Λ κ'`) and `nqGoodGen_kerNAL_band`
  (family, all `d`, `Ck = nqGood1C d k 𝔡⁻¹ (min κ (4/5))`, inside `∀ᶠ n` from `WO`): the class is concluded, not assumed.
- **T2.** `hker_of_case1Ng` = band `hker_of_case1N` (NQGood1:310) with `Ugen → Step2Gen_UN C`, `nqGood1C → Cv`, `|E| ≤ 2`, `κ' ≤ Im m`
  replaced by `hKer : NQGoodGen_KerNAL C gK k Ck n`; added R1 `hcmp` (the `T2491_R1Fam` comparison, `∀ m`), `1 ≤ A`, `Ck ≤ Cv`,
  `hdW : d√A W^{τ'} ≤ W^ε`, `hAk : A^{k-1} ≤ W^{(Cv-Ck)ε}`: the shape the 1a-audit accepted (`probe_hkerNg`, §4 R1). Weight at `sz.lam`,
  window `t ≤ 1 - lam²/L²` (size level), as UBA-C1. At `A = 1`, `Cv = Ck`, `gK = lam` it is the band statement. `driftTensorNg`,
  `driftTensorNg_norm_le/far_of_goodSetNg`, `qvFormNg_le_of_goodSetNg` port NQGood1:95-143, 379-576 with `η = Cm.eta n`.
- **T3.** Shift layer under `StepDecompGen_LoopForm Cm E` + inline `hm : ‖Cm.m n‖ ≤ 1` (D3, §294 (3) (5)) and, for
  `norm_STeeMg_shiftNg_le`, the row sums `hS : ∑ b ‖Cm.S n a b‖ ≤ 1`; band `|E| < 2` dropped. Names: `etaT_inv_shiftNg_le`,
  `loopFine_shiftNg_le`, `STXiLMg_shiftNg_le`, `goodSetNg_dec_shiftNg`, `norm_loopFine_crudeNg`, `STmaxLKMg_crudeNg`, `STXiLKMg_crudeNg`,
  `eeShiftErrNg`, `norm_STeeMg_shiftNg_le`; `loopShiftErrN`, `norm_loopL_zshiftN_le`, `nqGood1_ellT_mono` reused by name.
- **T4.** `kappaNonAltNg`, `epsNonAltNg`, `qvBdNonAltNg`, `cQVNonAltNg` take an explicit constant; five `_band` bridges are `rfl` at
  `Ck = nqGood1C d k Λg κ'`. (5.93) as `kappaNonAltNg(_succ)_mul_Bctl_pow_le`.
- **T5.** The eight field theorems fill the merged `GridAssemblyHypNg` (`Chain/GridAssemblyGen.lean:125`) by name (scratch above).
- **T6.** `hQ_nonAltNg` concludes the binding `T2491_HQg` at `Q = cQVNonAltNg … Cv …` (scratch above); `subGaussStop_nonAltNg` passes it
  to the merged `azumaProxy_subG_goodExitg` as its `hQ` (compiles); band re-derivation `hQ_nonAltN_of_Ng` has the band type exactly.
- No `∃` after `(sz, z)`; no `sz.withLam`; coupling `gK` only; no new kernel or carrier field; no `GridDriftNg`/`HierarchyNg` premise.

## 4. Hidden hypotheses, vacuity, cycles
- No new structure. The only new `Prop` class used as a premise is `NQGoodGen_KerNAL` (`hKer`); it is concluded by
  `nqGoodGen_kerNAL_band_at` (band) and instantiated at `sz0` (`NQGood1Gen_kerNAL0`, `NQGood2Gen_kerNAL0`) and at the flow `(szB, zB)`;
  its BA source (`baEKSumDecayNAL_holds` at `BAflowLam0`) is compiled in the probe (1a-audit §4 D1). The full build's scan lists no new
  premise.
- Other premises are merged classes/facts with merged band discharges used in the instances: `StepDecompGen_LoopForm`
  (`stepDecompGen_loopForm_band`), `GridRepTailGen_Ker` (`gridRepTailGen_ker_band`), `AzumaSubGNg` (`azumaSubGNg`), `QVPropagatedNg`
  (`qvPropagatedNg`), `StepDecompGen_WalkForm` (`stepDecompGen_walkForm_band`), `GoodSetNg` membership (`bandStep2_GoodSetN` +
  `zero_mem_goodSetN_inst(_grid)`), shift hypothesis `hδ` (`delta_shift_ok`).
- Imports: NQGood1Gen ← AzumaProxyGen, GridEnvelopeGen, GridRepTailGen, Induction.NQGood1; NQGood2Gen ← NQGood1Gen, StepDecompGen,
  Induction.NQGood2. No `BA/*`, `Q*`, `Qt*`, `Iterations*`, `Step3/4` import; no cycle (only RBM3D.lean and NQGood2Gen import the new files).
- External hypotheses: none new (D1 is deterministic and discharged; R1 crossings `hdW`, `hAk` are deterministic and discharged at `A = 1`).

## 5. Compiled nonempty instances (same files, `section Inst`; compiled by the module build of §1)
```
$ for each public theorem: grep -cw <name> inst sections   (count includes docstrings)
nqGoodGen_kerNAL_band_at:3 nqGoodGen_kerNAL_band:1 driftTensorNg_norm_le_of_goodSetNg:1 driftTensorNg_far_of_goodSetNg:1 hker_of_case1Ng:2
qvFormNg_le_of_goodSetNg:2 etaT_inv_shiftNg_le:2 loopFine_shiftNg_le:2 STXiLMg_shiftNg_le:2 goodSetNg_dec_shiftNg:2 norm_loopFine_crudeNg:2
STmaxLKMg_crudeNg:2 STXiLKMg_crudeNg:2 norm_STeeMg_shiftNg_le:2 kappaNonAltNg_mul_Bctl_pow_le:1 kappaNonAltNg_succ_mul_Bctl_pow_le:1
{kappa,eps,dDrift,qvBd,cQV}NonAltNg_band:1 each  nonAlt_hkerNg:2 goodSetNg_A0clsNg:2 nonAlt_hA0clsNg:2 nonAlt_hdriftNg:2
goodSetNg_driftClsNg:2 nonAlt_hDclsNg:2 nonAlt_hκ0Ng:2 nonAlt_hε0Ng:2 nonAlt_hdDrift0Ng:2 qvBdNonAltNg_pos:2
qvFormNg_le_of_goodSetNg_shift:2 hQ_nonAltNg:2 subGaussStop_nonAltNg:2 cQVNonAltNg_sum_pos:2 hQ_nonAltN_of_Ng:2
NQGood1Gen_* (11 file-stem helpers): 0 (helpers, not endpoints)       examples: NQGood1Gen 13, NQGood2Gen 16
```
Every endpoint of targets 1-6 is applied (read in the files): `d = 3`, band carrier `bandStep2Mat sz0 Einst` (`L = 4`, `W = 32`,
`lam = 1/64`, `E ≡ 1/2`), `n = 0`, `k = 3`, `σ = (+,-,+)` non-alternating, `ε = 4/5`, `τ' = 1/5`, `D' = 6`, `D'' = 5` (G2) / `3` (G1),
grid `u_j = j/128`, `K = 4`; D1 family at the flow `(szB, zB)`, `k = 2`. `hker_of_case1Ng` and `nonAlt_hkerNg` at the nonzero tensor
`Xinst` (`M = 1`, `δ = W^{-6}`), window `(0, 1/128)` / `(u_0, u_4)`; far label `aFar` with `diam_∞ = 2 = ℓ_0 W^{τ'}`. `hQ_nonAltNg` is
discharged for all `m ≤ 4`, `j < m`, `a` (private theorem `NQGood2Gen_hQ_instance`) and `subGaussStop_nonAltNg` at `(j, m) = (0, 4)` with
`azumaSubGNg`, `qvPropagatedNg`, `delta_shift_ok`: no open hypothesis (closes T2473c-audit O1). Every deterministic hypothesis is
discharged by `norm_num` / merged band facts; no `N = 0`, empty index, collapsed window or `False` premise.

## 6. Paper deltas
Prove report (d): `T2491a` (D1 as a class with a family-uniform explicit `Ck`; vocabulary constant `Cv ≥ Ck`; crossings
`d√A W^{τ'} ≤ W^ε`, `A^{k-1} ≤ W^{(Cv-Ck)ε}`) and `T2491b` (D3: `‖m‖ ≤ 1`, `Σ_b ‖S_ab‖ ≤ 1`, `η_u = (1-u) Im m` via `LoopForm`). These
cover every Lean/paper difference of targets 1-6 found in §3. The band's own deltas (`T2258b`) carry over unchanged.

## 7. Observations (no RETURN)
- O1 (hub, merge). `main` moved since the base: `git merge-tree --write-tree main t/T2491` reports content conflicts in `RBM3D.lean`
  (import lines) and `RBM3D/Test/Axioms.lean`: T2492 (b3ead83b) rewrote the BA clause of the same `GoodSetNg` comment line
  ("BA: the initial membership is `baGoodSetNg_init` (T2492 …)"), T2491 rewrote its band-majorant clause. Copying the branch versions of
  these two files would revert main's lines; the merge must be the union (main's line with T2491's `hQ_nonAltNg` clause; append the two
  import lines). `RBM3D/Probe/T2491Pins.lean` is on the branch and must not be merged (ticket).
- O2. All instances are at the band carrier, where R1 is `A = 1`, `Cv = Ck` and `hAk` is `1 ≤ W^0`; the `A > 1` crossings are exercised
  only by the generic proof (BA instances are U3-BA's, ticket "Not here"). Several shift-layer instances use `H = 0` (a `GoodSetNg`
  member); the hypotheses are still discharged at nondegenerate sizes and windows.
- O3. The paper-delta tag `T2491b` coincides with the branch name `t/T2491b` (row U3s2b); the dispatcher renumbers anyway.

## Verdict
Targets 1, 2, 3, 4, 5, 6 (row U3s2a): **PASS**. Statements match the binding pins (`T2491_KerNAL(Fam)` diff 0 / `rfl`, `T2491_HQg` by
type ascription) and the ticket's mathematics; no hidden or vacuous hypothesis; compiled nonempty instances for every endpoint; module and
full builds pass; 55/55 standard axioms; diff within the sole writable files; paper deltas proposed. No dispatcher sign-off needed.
