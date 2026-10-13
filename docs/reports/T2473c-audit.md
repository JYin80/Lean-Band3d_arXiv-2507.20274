Auditor model: claude-opus-5-5
# T2473c (T4s2c of T2473: `Chain/AzumaProxyGen`, targets 8-10) -- audit, round 1
Written Tue Oct 13 04:52:00 UTC 2026 (`date -u`). Branch `t/T2473c` at 61732d61, detached audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2473c-audit1`. Binding: ticket T2473, Amend 1 (three rows, S1-S3), Amend 2 (WalkForm),
supervisor 2351 T4S2-C2/C3. Scratch files: scratchpad `T2473c/`.

**Verdict: PASS** (targets 8, 9, 10). No dispatcher sign-off needed.

## 1. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.AzumaProxyGen
✔ [3872/3872] Built RBM3D.Chain.AzumaProxyGen (10s)
Build completed successfully (3872 jobs).
$ grep -E "^(error|warning)" build.out | grep -c AzumaProxyGen ; grep -c "^error" build.out
0
0
$ lake env lean ax.lean   (#print axioms of the 19 public declarations of the file)
exit 0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out ; other lines
19
(none)
$ lake build   (full, audit worktree) ; lake env lean <RBM3D.lean + `import RBM3D.Chain.AzumaProxyGen` after the last import>
Build completed successfully (4342 jobs).   exit 0
axiom audit: 14528 theorems, 4547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.GoodSetNg: 3 [no certificate]
premises found by scanning: 127 (borrowed 1, owed 60, structural 46, refuted 6, superseded 14).
root-exit 0
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Chain/AzumaProxyGen.lean
(none)
```
The 19 names: `azumaSubGNg azumaProxy_Hpath_zerog azumaProxy_pos_gridExitTauNg azumaProxy_pos_goodExitTauNg
azumaProxy_subG_ugeng azumaProxy_subG_goodExitg AzumaProxyN_stopWg AzumaProxyN_YfieldsWg AzumaProxyN_c0_pos_pubg
AzumaProxyN_eta_inv_le_pubg AzumaProxyN_rowsum_UN_pubg YMomentsUnifNg yMomentsUnifNg yMomentsNg_of_unif yMomentsNg
bandStep2_AzumaSubGN` and `AzumaProxyGenCheck.{azumaSubGNg_instance, yMomentsUnifNg_instance, yfieldsWg_instance}`.

## 2. Diff and layering
```
$ git diff main...t/T2473c --stat
 RBM3D/Chain/AzumaProxyGen.lean | 950 +++   RBM3D/Probe/T2473Pins.lean | 400 +++   RBM3D/Test/Axioms.lean | 1 +
$ git log --oneline main..t/T2473c -- RBM3D/Probe/T2473Pins.lean
b8c9b113 T2473 probe: D2 texts of T4s2 compiled against main (never merged)      (unchanged by T4s2c)
$ git diff main...t/T2473c --stat -- RBM3D/Induction RBM3D/Path RBM3D/BA Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,
    DecayGen,Step34Gen,GridGoodGen,GridEnvelopeGen,GridAssemblyGen,StepDecompGen}.lean RBM3D.lean
(empty)
$ git diff main...t/T2473c -- RBM3D/Test/Axioms.lean | grep "^+ "   (cut)  ; enclosing list
+   `RBM.BA.GoodSetNg, -- the good set ... (hypothesis `h0` of `azumaProxy_pos_goodExitTauNg` ...) and ... `hQ` ...
line 234 is inside `102: def owedProps : List Name :=`
$ grep -n '^import RBM3D.BA' ; grep -nE "def .*[Kk]er\b|def Ugen" ; grep -n STGridRepNgL   (the file)
(none) (none) (none)
$ grep -rln "import RBM3D.Chain.AzumaProxyGen" RBM3D RBM3D.lean
(none; the hub adds the root import at merge)
$ git grep -nE "^(theorem|def|...) <name>\b" main -- RBM3D   (17 new public names and the namespace AzumaProxyGenCheck)
all 0
```
Only sole writable files are touched; the probe is listed "1a only, never merged". Imports: `Chain/GridGoodGen`,
`Chain/GridAssemblyGen`, `Induction/AzumaProxyN2` (ticket layout).

## 3. Statements
Pins against the 1a probe (script `pindiff.py`, whitespace-normalised `def` text):
```
IDENTICAL YMomentsUnifNg 574 chars      (RBM3D/Probe/T2473Pins.lean vs RBM3D/Chain/AzumaProxyGen.lean)
IDENTICAL AzumaSubGNg 772 chars         (probe vs merged Chain/GridAssemblyGen.lean, T4s2b)
IDENTICAL YMomentsNg 278 chars          (probe vs merged Chain/GridAssemblyGen.lean, T4s2b)
```
Hypothesis-rule / X1-C1 / UBA-C1 grep restricted to the public signatures (script `sig.py`, pattern of the ticket plus
`withLam|BAflowLam0|\bgK\b`):
```
azumaSubGNg (L87-89): hits=[]             azumaProxy_Hpath_zerog (L136-139): hits=[]
azumaProxy_pos_gridExitTauNg (L147-150): hits=[]   azumaProxy_pos_goodExitTauNg (L164-167): hits=[]
azumaProxy_subG_ugeng (L193-203): hits=[]  azumaProxy_subG_goodExitg (L230-240): hits=[]
AzumaProxyN_stopWg / _YfieldsWg / _c0_pos_pubg / _eta_inv_le_pubg / _rowsum_UN_pubg: hits=[]
YMomentsUnifNg / yMomentsUnifNg / yMomentsNg_of_unif / yMomentsNg: hits=[]   three instance theorems: hits=[]
```
Every `withLam`/`pathH`/`pathP` hit of the file is in a proof that takes `hW : StepDecompGen_WalkForm`, in the private
abstract-walk core, a docstring, or the band bridge/instances (read at L78-142, 483-492, 649-735, 755-942).

Per target, against the ticket's mathematics and the band originals (`AzumaProxyN:970-1040`, `AzumaProxyN2:894-992, 1016-1258`):
- **Target 8.** `azumaSubGNg Cm [IsProbabilityMeasure Cm.Pp] (hW : WalkForm Cm lam' Ψ) s t K : AzumaSubGNg Cm lam' s t K`:
  the band `azumaSubGN` at `sz.withLam lam'` with the shift `Ψ` (ticket: "under W ... at `sz.withLam g′` and the shift
  `H₀`"). `azumaProxy_Hpath_zerog`: `s n = 0 → Cm.Hpath … 0 ω = Ψ n` (ticket: `= H₀ n` under W).
  `azumaProxy_pos_gridExitTauNg`: hypotheses `0 < K n`, `H_0 ∈ G 0`, as the band. `azumaProxy_subG_ugeng`: band
  `azumaProxy_subG_ugen` with `hE : |E n| < 2` and `qvPropagatedN` replaced by `LoopForm`, `QVPropagatedNg Cm g`
  (same `g` as the pin hypothesis `h`) and `hKer : GridRepTailGen_Ker Cm.toFlowFM n` (K4 identifies `qvFormNg`);
  all other hypotheses, the quantifier order `n k … m a j Q` and the majorant `hQ` are the band's.
  `azumaProxy_subG_goodExitg`: the same plus `hW` (for `goodExitMeasNg`). Matches; no loss or range changed.
- **Target 9.** `azumaProxy_pos_goodExitTauNg … (h0 : GoodSetNg Cm n (gridTime s v K n 0) k … (Cm.Hpath s v K n 0 ω))`:
  the initial membership is inline, per `ω` at one `n` (no named `Prop`, no `∀ n`). The ticket text is
  `∀ ω, … ∈ GoodSetNg` at `s n = 0`; the per-`ω`, any-`s` form is weaker in its hypothesis, conclusion per `ω`: it implies
  the ticket form. **Supervisor T4S2-C2:** no statement of the file takes target 9 as `∀ n`
  (`grep -nE "∀ n.*GoodSetNg|GoodSetNg.*∀ n"`: none); no BA reading in the file.
- **Target 10.** `YMomentsUnifNg` = band `YMomentsUnifN` with `0 < κ`, `|E n| ≤ 2-κ` → `DecayGen_Spec Cm.toFlowFM κm`; same
  binders and order (`k σ`, `∃ C_P` before `∀ K`, `∀ᶠ n`, `∃ P ≤ N^{C_P}`, `∀ τ` stopping). `yMomentsUnifNg` takes
  `LoopForm`, `WalkForm`, `∀ n, Ker`; witness `C_P = 11 + (4k+4) max 0 (1-τ')` as the band (L566).
  `yMomentsNg_of_unif`, `yMomentsNg` as band. `AzumaProxyN_YfieldsWg`: eight fields as band `AzumaProxyN_YfieldsW`,
  dropping the unread `0 ≤ s n`, `|E n| < 2` (weaker hypotheses). Public forms: `c0_pos` = `DecayGen_Spec.1`;
  `eta_inv_le` = band `etaT_inv_le_pub` with `η` from `DecayGen_Spec`; `rowsum_UN` bound `(1+(1-w)⁻¹)^k` for
  `0 ≤ v,w < 1` (band's range) from K3 (prove report (a′)).
- **Hidden hypotheses / cycles.** Premises are merged single texts: `StepDecompGen_LoopForm` (`StepDecompGen.lean:60`),
  `StepDecompGen_WalkForm` (`:73`), `QVPropagatedNg` (`:479`), `GridRepTailGen_Ker` (`GridRepTailGen.lean:54`),
  `DecayGen_Spec` (`DecayGen.lean:91`), pins `AzumaSubGNg`, `YMomentsNg` (`GridAssemblyGen.lean:81,118`); all `git grep`
  hits on `main`. Their band discharges (`stepDecompGen_loopForm_band :459`, `_walkForm_band :465`, `qvPropagatedNg :505`,
  `gridRepTailGen_ker_band` `GridRepTailGen2:672`, `DecayGen_bandSpec :142`) are used jointly in §5 of the file, so
  the hypothesis sets are satisfiable at once. No structure is introduced; no new `Prop` beyond the pin `YMomentsUnifNg`;
  the file is imported by nothing, so no cycle.
- **Supervisor T4S2-C3.** `open private` (L42-45): seven grid/moment helpers of `Induction/AzumaProxyN2` and
  `GridAssemblyGen_row_le`; none is an S2 / LoopForm BA reading (no `ConArg_self_of_im_pos`).

## 4. Compiled nonempty instances (§5 of the file, L749-944; all compile in the build of §1)
Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `bandStep2Mat sz0 Einst`, `Einst ≡ 1/2`, `s ≡ 0`, `t ≡ 1/32`, `K ≡ 4`,
`Δ = 1/128` (example L785 checks these values), `k = 3`, `σ = (+,-,+)`, `κm = √1/2`, `τ' = 1/2` (`rangeCond_vg` proved).
| target | instance | open hypotheses |
|---|---|---|
| `azumaSubGNg` | `azumaSubGNg_instance` L792 (`G 0 = {0}`, `Q = qProxy3 m a`; `0 < qProxy3 1 b0` L802) | none |
| `azumaProxy_Hpath_zerog` | example L805 | none |
| `azumaProxy_pos_gridExitTauNg` | example L808 (`G = Hermitian`) | none |
| `azumaProxy_pos_goodExitTauNg` | example L821, `h0` by `h0_inst` (band `zero_mem_goodSetN_instance_grid`, levels `Γ4 Λ3 Φ1`, `τ'=1/2`, `D'=1`) | none |
| `azumaProxy_subG_ugeng` | example L826 (`m ∈ [1,4]`, every `a`, `Q` = majorant at `M = 0`) | none |
| `azumaProxy_subG_goodExitg` | example L843 | `hQ` (majorant on the good set) |
| `AzumaProxyN_YfieldsWg` | `yfieldsWg_instance` L917 (`n = j = 0`, every `κ`, `C₂`, `P` explicit) | none |
| `c0_pos`, `eta_inv_le`, `rowsum_UN` | examples L853, L855 (`N = 4`, `u = 1/4`, `t = 1/2`), L861 | none |
| `yMomentsUnifNg`, `_of_unif`, `yMomentsNg` | L868, L880, L893 (instance-`n` from the eventual filter, `Δ > 0`) | none |
No `N = 0`, empty index set, collapsed window or `False` premise. The one open `hQ` is the Step 3 output (U3s2-U3s3; band
`qvFormN_le_of_goodSetN_shiftN`, `NQGood2:435`), kept exactly as in the merged band instance
`azumaSubGN_goodExit_instance` (`AzumaProxyN:1251`) and accepted in audits T2159 (`:107`) and T2194 (`:92`); the
underlying composition `azumaProxy_subG_ugeng` has a fully discharged instance (L826). Observation O1, not a RETURN.

## 5. Paper deltas
`grep -oE "T2473[a-z]\b"`: T2473 1a uses a-e, T2473b f-i, this report adds j-n (new tags; `docs/paper-deltas.md` has 0 T2473
entries yet). Coverage of the Lean/paper differences found in §3:
- `|E| < 2` / `qvPropagatedN` → LoopForm + `QVPropagatedNg` + K4 in the compositions: T2473j.
- `YfieldsWg` drops `0 ≤ s n`, `|E n| < 2`; `hC2` on the shifted loop family: T2473k.
- `c₀ = κm` (`DecayGen_Spec`) in `yMomentsUnifNg`; explicit `P` differs, `∃ P` agrees: T2473l.
- row sum from K3 (not K2); `eta_inv_le` renamed; `c0_pos` = `Spec.1`: T2473m.
- target 9 inline per-`ω` `h0`; `[IsProbabilityMeasure Cm.Pp]` on `azumaSubGNg`: T2473n.
Every difference is covered.

## 6. Observations (no verdict effect)
- O1: `hQ` open in the `azumaProxy_subG_goodExitg` example (§4); same as the band precedent.
- O2: the prove report has no section (a) of its own; it points to `T2473-prove.md` (a)/(a″)/(a‴) and the 1a-audit.
- O3: `azumaProxy_Hpath_zerog` concludes `= Ψ n` (generic shift); at BA this is `λ₀ Ψ_B ≠ 0`, so the BA initial membership
  stays owed to T4-BA (Amend 1 item 4; T4S2-C1/C2); recorded in the registry line comment.
- O4: registry class of `GoodSetNg` (`owedProps`, prove report (d)): the root check with the import line passes (§1);
  the class choice (owed vs structural) is a registry-bookkeeping question for the dispatcher, not a statement defect.

## Verdict
Target 8: PASS. Target 9: PASS. Target 10: PASS. Ticket T2473c: **PASS**.
