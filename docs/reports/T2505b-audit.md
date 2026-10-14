Auditor model: claude-opus-5-5

# T2505b audit (U3s4b, targets 6-9), round 1 — Wed Oct 14 12:40:26 UTC 2026

Branch `t/T2505b` at `29c0faf2`, merge-base `d3104f3b`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2505b-audit1` (detached); scratch in the session scratchpad `T2505b/audit/`.

## 1. Diff scope, imports, layering
```
$ git diff main...t/T2505b --stat
 RBM3D.lean                       |   2 +
 RBM3D/Chain/QtNonzeroEndGen.lean | 688 ++++
 RBM3D/Chain/QtNonzeroGen.lean    | 956 ++++
 RBM3D/Probe/T2505Pins.lean       | 292 ++++      (row b's probe; sole-writable on t/T2505b, never merged)
$ git diff main...t/T2505b -- RBM3D.lean
+import RBM3D.Chain.QtNonzeroGen
+import RBM3D.Chain.QtNonzeroEndGen          (after `import RBM3D.Chain.QEndB1Gen`, before `#assert_rbm_axioms`)
$ git diff main...t/T2505b -- RBM3D/Induction RBM3D/BA RBM3D/Graph RBM3D/Test | wc -l
0
$ grep -n "^import" (new files)
QtNonzeroGen:    Chain.ZeroModeGen Chain.NQLinGen Chain.GridAssemblyGen Chain.AzumaProxyGen Chain.StepDecompGen Induction.QtNonzero
QtNonzeroEndGen: Chain.QtNonzeroGen Chain.NQEndLinGen Chain.NQBudgetGen Induction.QtNonzeroEnd
$ grep -rn "import RBM3D.Chain.QtNonzero\|import RBM3D.Probe" RBM3D RBM3D.lean
RBM3D/Chain/QtNonzeroEndGen.lean:6:import RBM3D.Chain.QtNonzeroGen
RBM3D.lean:618:import RBM3D.Chain.QtNonzeroGen
RBM3D.lean:619:import RBM3D.Chain.QtNonzeroEndGen
$ wc -l  -> 956 QtNonzeroGen, 688 QtNonzeroEndGen (both < 2,000), probe 292 (< 300)
```
No `BA/*`, no `Chain.Step2Kern`; the probe is not imported; no band, BA, Graph, Test or merged Chain file touched.

## 2. Build and axioms
```
$ lake build RBM3D.Chain.QtNonzeroGen RBM3D.Chain.QtNonzeroEndGen
⚠ [3888/3889] Built RBM3D.Chain.QtNonzeroGen (13s)
⚠ [3889/3889] Built RBM3D.Chain.QtNonzeroEndGen (7.5s)
Build completed successfully (3889 jobs).      exit=0
(warnings in the two new modules: only `longLine`; 0 error lines)
$ grep -nE "sorry|admit|native_decide|^\s*axiom|withLam|STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" (both files) | wc -l
0
$ lake env lean <scratch: T2505-check.lean + import RBM3D.Chain.QtNonzeroEndGen + examples + #print axioms of the 19 public decls>
exit=0
  19  [propext, Classical.choice, Quot.sound]
```
The 19 public declarations: `QtNZGen_KerNZ, QtNZGen_KerNZFam, qtNZGen_bandC, qtNZGen_bandC_pos, qtNZGen_kerNZ_band_at, qtNZGen_kerNZ_band,
qtNZGen_row_of_op, qtNZGen_row_of_kerNZ, cQVNZNg, assembledRHSNZNg, nz_hkerg, nz_hdriftNg, subGaussStop_nzNg, yMomentBounds_nzNg, budgetNZNg,
qtNZGen_subGaussStop_instance, nzGridEndNg, nzGridEndN_of_gen, qtNZEndGen_instance`. Name clash against current `main` (`git grep -c` per name over `RBM3D`): 0 files for each.

## 3. Statements

### Target 6 (D1) against the pin `T2505_KerNZ`, `T2505_KerNZFam` (check `:157-167`)
```
$ diff <(check:157-167, T2505_KerNZ->QtNZGen_KerNZ, blank lines dropped) <(QtNonzeroGen:56-66, blank and /-- lines dropped)
5d4
< /-- **D1 default, the family form** (guarded; ...) -/        (docstring only; code lines identical)
$ scratch file (same compile as §2), exit 0:
example : @T2505_KerNZ = @QtNZGen_KerNZ := rfl
example : @T2505_KerNZFam = @QtNZGen_KerNZFam := rfl
example (d : ℕ) : T2505_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
    (fun sz _ => sz.lam) (fun _ => 1) := qtNZGen_kerNZ_band d          -- band half of the check's T2505_shape_KerNZ
```
Against the ticket's mathematics: per index, `‖Q^{(A)} 𝒰 X‖ ≤ C5 ‖X‖` for every `σ`, `Aset ⊇ I_diff(σ)` (stated as `σ i ≠ σ (finRotate k i) → i ∈ Aset`),
A-form window `(1 - v) L² ≤ A gK²`, `0 ≤ v ≤ w < 1`; family: guarded by `Flow`, `∃ C5 > 0` after `(k, κ, 𝔡)` and before `(sz, ε, 𝔠, z)`, `∀ᶠ n`.
Paper `lem:sum_decay_nonzero` (`3_5:1666-1672`): `1 - λ²/L² ≤ s ≤ t < 1`, `‖Q^{(A)}∘𝒰∘𝒜‖_∞ ≺ ‖𝒜‖_∞`. Lean is loss-free (constant instead of `≺`)
and in the A-form with a kernel coupling `gK`; at the band (`A = 1`, `gK = lam`) the window is the paper's. Delta: proposed `T2505ba`.
Band discharge `qtNZGen_kerNZ_band_at` (head `QtNZGen_KerNZ`, constant `qtNZGen_bandC`) and `qtNZGen_kerNZ_band` (head `QtNZGen_KerNZFam`)
read `nzUgen_holds`, `bandStep2_Ugen`, `ZeroModeCalc_STIdiff_subset_iff`, `nqGood1_mE_im_ge`; row-sum form `qtNZGen_row_of_kerNZ` from the
`∞→∞` bound. Pinned `∃ C5` position: as pinned. **PASS.**

### Target 7 (`QtNonzero` §2-§8 twins) against the band statements (`Induction/QtNonzero.lean` `:224, 233, 327, 358, 417, 731, 872`)
Read side by side (band statement extracted by `awk` from the decl line to `:= by`):
- `cQVNZNg`, `assembledRHSNZNg`: band defs with `etaT (E n)` → `Cm.eta n`, `sz` → `Cm`; same terms (proxy, drift `cA · dDriftLinNg`, step error).
- `nz_hkerg`: band `|E| ≤ 2`, `u_i ≥ 0`, `u_i < 1` replaced by `hKS : ZeroModeGen_KerSums C n`; operator bound `hop` as hypothesis (as band); same conclusion `≤ C M + 0·δ`.
- `nz_hdriftNg`: same statement on `GoodLinNg`/`driftTensorNg`/`dDriftLinNg`, factor `2^{|A|}`.
- `subGaussStop_nzNg`: band `∀ n, |E n| < 2` → `LoopForm`, plus carrier facts `AzumaSubGNg`, `QVPropagatedNg`, `hKS`, `‖m‖ ≤ 1`, row sums `≤ 1`
  (merged generic classes, discharged at the band carrier in the instance); row hypothesis, `hδ`, conclusion as band.
- `yMomentBounds_nzNg`: band `|E| ≤ 2`, `u` range → `hKS`; levels `4^{|A|+1} v`, `16^{|A|+1} w` as band.
- `budgetNZNg`: hypotheses H1-H6, `hlog`, `hX0`, `hR` and the conclusion are the band's verbatim with `mE (E n)` → `Cm.m n`, `etaT` → `Cm.eta`; `|E n| < 2` → `LoopForm`.
No hypothesis dropped or weakened beyond the carrier vocabulary. **PASS.**

### Target 8 `nzGridEndNg` against band `nzGridEndN` (`QtNonzeroEnd:979`) and the merged twin `nqGridEndLinNg` (`NQEndLinGen:600`)
Quantifier order (`QtNonzeroEndGen:382`): carrier hypotheses → `∀ k ≥ 2, ∀ C > 0, (∀ᶠ n, QtNZGen_KerNZ Cm gK k Ar C n)` → `Λ, Φ₁..Φ₃` (as band)
→ `v ∈ [s,t]` → `ε₀ > 0`, `D₁ > 0` → `∃ ε₁ τ' D' C_K` → `∀ Φc K` grid `N^{C_K} ≤ K ≤ ⌈N^{C_K}⌉` → `∀ᶠ n, ∃ G, P(Gᶜ) ≤ N^{-D₁}` ∧ initial bound
`N^{ε₁} B_s^k` for every `σ`, `A ⊇ I_diff` → terminal `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃) B_v^k` for every `σ`, `A ⊇ I_diff`, `a`. Identical to the band
conclusion shape (loss, exponents, index ranges, both `σ`/`A` quantifiers). Changes vs band: `𝔡`, `WO`, `|E| ≤ 2-κ` → D1 (`hKerN`) + `hR1 : lam² ≤ Ar gK²`
+ `DecayGen_Spec κm` + `LoopForm`; `STCaseII` kept; `STKbound` → pin `hKb : STKboundgL` (owedProps); merged carrier classes `hRow`, `hKS`, `hKK`,
four eventual drift classes (no `∀ n` drift premise, UP-C4). R1 enters once, A-form, `gK` only; no `sz.withLam`. Same shape as `nqGridEndLinNg`
with `NQGoodGen_KerNAL/Ck/Cv/hcmp/hA` replaced by D1 and `STCaseI/hWt` by `STCaseII`. Delta: proposed `T2505bb`.
`nzGridEndN_of_gen` (`:553`) has the band statement of `nzGridEndN` (prover's script diff: 0 lines; I read both: same text) and is proved from
`nzGridEndNg` at `bandStep2Mat sz E`, so every hypothesis of `nzGridEndNg` is dischargeable at the band for all `d ≥ 3`. **PASS.**

### Hypothesis rules (ticket C1, X1-C1, X1-C4, U5S-C3)
```
$ python (statement text of each public decl up to `:=`, `KLloopOf` excepted) — C1/X1-C1 regex hits:
QtNonzeroGen.lean qtNZGen_kerNZ_band_at ['mE']             (band discharge)
QtNonzeroGen.lean qtNZGen_kerNZ_band ['STFlow', 'STflowE'] (band discharge)
QtNonzeroEndGen.lean nzGridEndN_of_gen ['2 - κ']           (band re-derivation)
X1-C4 (def|abbrev|structure of merged class names): []
$ grep -n "∀ (sz : Sizes d)" -> QtNonzeroGen:62, 63, 65 (the guarded D1 family def; family row 14)
```
0 hits in generic statements.

## 4. Vacuity, hidden hypotheses, cycles
- D1 is a plain `def … : Prop` (no structure); every hypothesis is in the signatures above. New Props `QtNZGen_KerNZ` (concluded by
  `qtNZGen_kerNZ_band_at`), `QtNZGen_KerNZFam` (concluded by `qtNZGen_kerNZ_band`); `STKboundgL` is an existing owedProps pin (unchanged registry).
- No cycle: the new modules import only merged modules (§1); nothing merged imports them.
- External hypotheses: none new. D1 is a band lemma at the band (`nzUgen_holds`); its BA source is shown on the probe (`probe_kerNZ_BA_at`,
  `probe_kerNZFam_BA`, prove report (a″)), which stays on the branch (U3-BA (a) owns the merged BA instance).

## 5. Compiled nonempty instances (all in the two files, built in §2)
```
$ grep -nE "^(example|theorem qtNZ\w*instance|private theorem QtNZGen_(D1_szB|drift_instance|row_coarse))"
QtNonzeroGen:770 QtNZGen_D1_szB      qtNZGen_kerNZ_band_at at szB, n = 0, E ≡ 0, k = 3, Λg = 1, κ' = 1/2
QtNonzeroGen:777 example             qtNZGen_kerNZ_band at flow_zB (κ=ε=𝔡=1/10, 𝔠=1/6), window (1-15/16)·16 = 1 ≤ lam², σ=(+,-,+), A={0,1}, X=δ₀, ‖X‖=1
QtNonzeroGen:793 example             qtNZGen_row_of_kerNZ at szB, A = I_diff(sig3)
QtNonzeroGen:803 example             nz_hkerg at szB, K = 1, X = Q^{(A)}δ₀ ≠ 0
QtNonzeroGen:827/835/846             nz_hdriftNg at sz0, A = ∅ and I_diff; level > 0
QtNonzeroGen:854/883/894             subGaussStop_nzNg at sz0 (every A, m ≤ 4, j < m), coarse row 2^{|A|}(1+32/31)^3; proxy > 0
QtNonzeroGen:909 example             yMomentBounds_nzNg at a random Y_j = ζ_j δ₀ (Y_0 ≠ 0, Q^{(A)}Y_0 ≠ 0)
QtNonzeroGen:923 example             budgetNZNg at N = 2^21, all 6 absorption inequalities proved numerically
QtNonzeroEndGen:639 qtNZEndGen_instance  nzGridEndNg at bandStep2Mat szB Einst (d=3, L=4, W=n+4, lam≡1, s=15/16 < v=31/32, τ=1/2, ε₀=1/10, D₁=1,
                                         grid KB C_K, Δ > 0); every hypothesis discharged (STKboundgL by stKbound_holds, D1 by qtNZGen_kerNZ_band_at, R1 Ar=1)
QtNonzeroEndGen:676/679/682 example  the instance at k = 2, 3, 4
```
No `N = 0`, empty index, collapsed window (`window_nondegenerate`: `s < v`, `0 < Δ`) or `False` premise; no astronomical witness (the endpoint
instance takes `n` from the filter, `Eventually.exists`). No open hypothesis in any example. Targets 6, 7, 8 each have an instance; target 9 is these.

## 6. Paper-delta coverage
Prove report (d) proposes `T2505ba` (D1: constant for `≺`, A-form window, coupling `gK`), `T2505bb` (`nzGridEndNg` vs `lem:STOeq_Qt_nonzero`:
D1 constant, `hR1`, `STCaseII`, no `𝔡/WO/κ`, `DecayGen_Spec`, `ZeroModeGen_KerSums`, `STKboundgL`), `T2505bc` (Lean-only `qtNZGen_bandC`).
Existing context entries checked present in `docs/paper-deltas.md`: D37 (`:303`), D588 (`:1547`), D699 (`:1707`). Coverage complete for the
statement differences found in §3.

## 7. Observations (no verdict change)
- O1. `nzGridEndN_of_gen` (band re-derivation, not a numbered row-b target) has no `example` of its own; its statement equals the merged band
  `nzGridEndN`, and `nzGridEndNg` (which it instantiates) has the compiled instance at `szB`.
- O2. `nzGridEndNg` keeps `hst : ∀ n, s n ≤ t n` unused (stated in the report narrative item 4); harmless.
- O3. `main` has moved past the branch point (74b7c64b row a, c9b3f490 T2506): `RBM3D.lean` is a union of import lines at merge; the hub's
  full `lake build` (with `#assert_rbm_axioms` and the premise scan) is the merge check.
- O4. Prove report (b) lists 5 regex hits (it counts the body of `qtNZGen_bandC`); my statement-only scan gives 3 declarations — all band-side either way.
- O5. Target-7 twins add carrier-class hypotheses (`hKS`, `‖m‖ ≤ 1`, row sums) to Lean-internal lemmas with no paper statement; covered in substance by `T2505bb`.

## Verdict
| target | verdict |
|---|---|
| 6 D1 `QtNZGen_KerNZ`, `QtNZGen_KerNZFam`, band discharge, row-sum form | PASS |
| 7 `cQVNZNg`, `assembledRHSNZNg`, `nz_hkerg`, `nz_hdriftNg`, `subGaussStop_nzNg`, `yMomentBounds_nzNg`, `budgetNZNg` | PASS |
| 8 `nzGridEndNg` (+ `nzGridEndN_of_gen`) | PASS |
| 9 instances at `d = 3` | PASS |

**T2505b: PASS.** No dispatcher sign-off needed. Merge: exactly `RBM3D/Chain/QtNonzeroGen.lean`, `RBM3D/Chain/QtNonzeroEndGen.lean` and the two
`RBM3D.lean` import lines; `RBM3D/Probe/T2505Pins.lean` stays on the branch (never merged).
