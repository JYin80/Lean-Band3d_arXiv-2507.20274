Auditor model: claude-opus-5-5

# T2505b (U3s4b) stage-1a audit (design gate D1 and probe) — Wed Oct 14 09:55 UTC 2026

Inputs: `docs/tickets/T2505.md`, `docs/reports/T2505b-prove.md` (a), (a″); branch `t/T2505b` at `bf9aaf6a` (parent `main` d3104f3b). Audit worktree: detached `/Users/junyin/Lean_proof/RBM3D-wt/T2505b-1a-audit`.
Scratch: `<scratchpad>/T2505b/audit/`. No source edited.

## 1. Branch scope
```
$ git diff --stat d3104f3b HEAD
 RBM3D/Probe/T2505Pins.lean | 292 +++++++++++++++++++++++++++++++++++++++++++++
$ git diff d3104f3b HEAD --name-only -- RBM3D/Induction RBM3D/BA RBM3D/Graph RBM3D/Chain | wc -l
0
$ grep -c "Probe" RBM3D.lean        # probe not imported at the root
0
```
Probe: 292 lines (cap 300), `t/T2505b` only; single `[[lean_lib]]`, default roots: the probe is not built into the library.

## 2. Probe recompile (`lake env lean`, own worktree)
```
$ lake env lean RBM3D/Probe/T2505Pins.lean      (09:50:35 -> 09:50:57 UTC)
unclassified T2505_ premises, file as written: []
same, `probe_kerNZ_band_at'` excluded as a head: [RBM.BA.T2505_KerNZ]
(#check lines of T2505_KerNZ, T2505_KerNZFam, probe_shape_KerNZ elided; probe_shape_KerNZ's type = the check's T2505_shape_KerNZ)
'RBM.BA.probe_kerNZ_band_at'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_kerNZFam_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_kerNZ_BA_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_kerNZFam_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_shape_KerNZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_BAReal_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_BA_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Scratch copy (examples renamed `aud_example_N`, plus `example : <check :183-186 verbatim> := probe_shape_KerNZ`):
```
'RBM.BA.aud_example_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.aud_example_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.aud_example_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.aud_example_4' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0          # the check's T2505_shape_KerNZ body elaborates against probe_shape_KerNZ
forbidden-token hits (sorry|admit|native_decide) in the probe: 0
$ lake env lean docs/tickets/checks/T2505-check.lean   (worktree copy, cmp = main copy)
check exit 0    # D3 binding texts (rows a, c) unchanged and compiling at bf9aaf6a
```
## 3. D1 statement (the text fixed by this audit)
```
$ diff <(sed -n 154,167p docs/tickets/checks/T2505-check.lean | grep -v '^\s*$') <(git show t/T2505b:RBM3D/Probe/T2505Pins.lean | sed -n 36,49p | grep -v '^\s*$')
D1 text identical (check:154-167 vs probe:36-49)
```
Against the mathematics (`lem:sum_decay_nonzero`, `3_5:1666-1671`: `1-λ²/L² ≤ s ≤ t < 1`, `A ⊇ I_diff(σ)`, `‖Q^{(A)}∘𝒰∘𝒜‖_∞ ≺ ‖𝒜‖_∞`):
- hypotheses: `0 ≤ v`, window `(1-v)L² ≤ A·gK²` (A=1, gK=lam is exactly the paper's `1-λ²/L² ≤ s`), `v ≤ w < 1`, every `σ`, every `Aset` with
  `σ i ≠ σ (finRotate k i) → i ∈ Aset` (= `STIdiff σ ⊆ Aset`, `ZeroModeCalc_STIdiff_subset_iff`), every tensor `X`. Matches.
- conclusion: constant `C5` instead of `≺` (loss-free; stronger, deterministic) — covered by paper-deltas D37, D588; A-form window and kernel
  coupling `gK` — covered by D699 (b) (UBA-C1). No uncovered Lean/paper difference at the 1a level.
- family: `3 ≤ d → ∀ k ≥ 2, ∀ κ 𝔡 > 0, ∃ C5 > 0, ∀ sz ε 𝔠 z, Flow … → ∀ᶠ n, …`: `∃ C5` after `(k, κ, 𝔡)`, before `(sz, z)`; guarded by
  `Flow`; eventual in `n` (no `∀ n` premise). Ticket D1 shape satisfied.
- band source `nzUgen_holds` (`QtNonzero:299`): window `1 - g²/L² ≤ v`, `|E| < 2`, `κ' ≤ Im mE E`, constant before `(L, g, E)`; the probe's
  `probe_kerNZ_band_at'`/`probe_kerNZFam_band` discharge D1 at `(STFlow, bandFM, sz.lam, Aof = 1)` (compiled above).
- BA source: `probe_kerNZ_BA_at`/`probe_kerNZFam_BA` prove D1 at `(BAFlow, baFMz, BAflowLam0, Aof κ = (κ+1)/κ)` from `baTwKerZero_holds`
  (`TwistKer:256`, `∀ A > 0`, `C(A) = 2 + A·C₀E_k`) and `baEKSameRow_holds` (`EKPins:568`) through `Step2Kern_UN_BA`, `BAflow_real`,
  `BAflow_lam0_window` (`GreenSchur:59, 72`). Stop line "D1 without a BA source" not hit (a proof, not only a typecheck).
- No hidden hypothesis: both defs are plain `Prop`s, no structure fields; no cycle (probe-only imports of `BA.*`/`Chain.Step2Kern`).
## 4. Nondegenerate D1 instances (fill-in (ii))
Compiled (section 2): band at `szB` (`L ≡ 4`, `lam ≡ 1`, merged `flow_zB`), `k = 3`, `σ = (+,-,+)`, `Aset = {0,1} = I_diff(σ)`, `X = δ₀`
(`‖δ₀‖ = 1`), grid pair `(15/16, 31/32)` (`0 < v < w < 1`), window `(1-15/16)·16 = 1 ≤ 1`; BA kernel `baFM szB (g₀) (E₀)` at `n = 0`,
`L = 4`, `Aof = (κ₀+1)/κ₀`, `g = 1/64` and `g = 1` (genuine window `0 < v < w < 1`), `g = 10` (`v = 0`, window all of `[0,1)`).
No `N = 0`, empty index, collapsed window or `False` premise; every deterministic hypothesis of `T2505_KerNZ` discharged.

## 5. Numerics rerun (preflight scripts, unchanged; outputs identical to (a))
```
$ python3 -I expo.py
grid k{2,3,4,6} tau{.1,.5,1,3} D1{.1,1,10} c{.01,1/6,.5,1} eps0{.01,.1,1,5} Cmax{0,1,50}: min slack over grid (all > 0 required)
  C_K slacks : hC1=54.0  hC2=62.7  hC3=73.1  hC4=82.7  hC5=92.2  hC6=75.1
  N-exponent gaps (a power of N left over):  H1=0.00875  H2=0.0075  H3=0.0075  H4=2.0137  H5=2.01  H6=2.01
instance exponents: e0=1 eps1=eps_q=1/8 D''=61 D'=62 tau'=1 tauR=1/2 tauK=1 D_Y=D_t=5 cA=8  C_K=166 + 2 Cmax
  case (ii): 1-s=1/16 <= lam^2/L^2=1/16 : True ; 0<=s<=v<=t<1: True ; s<v (non-collapsed): True
  D1 A-form window at grid time u=15/16: (1-u) L^2 = 1 <= A gK^2 = 1 : True
  BA-type R1 (kappa_BA=1/2, Aof=(k+1)/k=3, gK=3/5 lam): lam^2=1 <= Aof gK^2=27/25 : True ; gK<=lam: True ; window (1-s)L^2=1 <= Aof gK^2: True
  H1-H6 hold for all N > e^13.10 = 4.88e+05 (C5=9.528, eps0=1, Lambda_g=1); szB index with (4(n+4))^3 above it: n >= 16
$ python3 -I d1large.py
A=1 g=10 T1 Q.K(mu=1), w=1-1e-9: L=12: 29.55  L=16: 29.78  L=24: 29.92  L=32: 29.98  L=48: 30.02
A=3 g=10 T1 Q.K(mu=1), w=1-1e-9: L=12: 41.90  L=16: 73.95  L=24: 86.82  L=32: 87.01  L=48: 87.13
```
(`d1num.py` rerun too: all six rows equal the (a) paste; outputs in `<scratchpad>/T2505b/audit/*.out`.) Band constants:
```
QtNonzeroEnd:1025: κ' = min κ (4 / 5)        QtNonzeroEnd:1026: Λg = 𝔡⁻¹        QtNonzeroEnd:1046: e0 = min ε₀ 1
QtNonzeroEnd:1050: D'' = 2 * ((k : ℝ) + 2) / 𝔠 + 1
QtNonzeroEnd:1055: C_K = D₁ + 2 * (Cmax + 2 * (k : ℝ) + 2) + D'' + 16 * k + 40
QtNonzeroEnd:1057: refine ⟨e0 / 8, 1, D'' + 1, C_K, …⟩          QtNonzeroEnd:1079: D_t := k + 2      QtNonzeroEnd:1083: cA := 2 ^ k
```
`hC1..hC6` in `expo.py` are the band's `hC1..hC6` (`QtNonzeroEnd:1066-1074`, each closed by `linarith`, so symbolic for all parameters);
H1-H6 are `budgetNZN`'s six absorption premises (`QtNonzero:891-905`). D1's limit check: the saturation in `L` (d1large) — D1 is a lemma at
band and BA, not an external hypothesis. Bootstrap `c`: n/a for row b (correct; targets 2, 4 are row a's).

## 6. Fill-in table, D3-D4, plan
(i) matches band constants (section 5); (ii) compiled (sections 2, 4); (iii) present, every name exists (grep below); (iv) default text
accepted unchanged (section 3), probe 292 lines; (v) row 14 only for row b, the rest moved to the 1b start (allowed, 0149 `:98`); (vi) present;
(vii) R1 only at target 8 (`st6_ini_nonzerog` precedent), no `sz.withLam`; (viii) present, probe-confirmed (O2); (ix) present; (x) section 7;
(xi) 0 declaration hits (below). Every row is a line or "n/a, because …".
```
$ for n in <28 names read by the plan>; do grep -rnE "^(private )?(theorem|lemma|def|abbrev|structure|noncomputable def) $n\b" RBM3D; done
gridDriftNg_envelope_ev NQEndLinGen:93  ZeroModeGen_KerSums ZeroModeGen:54  ZeroModeGen_WardCls ZeroModeGen:289  B45Gen_Facts B45Gen:61
driftTensorNg_norm_le_of_goodLin NQLinGen:430  nqBudget_merged_inputsg NQBudgetGen:734  yMomentsUnifNg AzumaProxyGen:558
SubGaussStopNg StepDecompGen:575  azumaSubGNg AzumaProxyGen:87  qvPropagatedNg StepDecompGen:505  YMomentBoundsNg GridAssemblyGen:96
nqLinExitTauNg NQLinGen:413  assembledNg GridAssemblyGen:807  zeroModeSet_UNg ZeroModeGen:161  STKboundgL Carrier:147
bandStep2_Ugen GridDuhamelGen:181  ZeroModeCalc_STIdiff_subset_iff ZeroModeCalc:412  nqGood1_mE_im_ge NQGood1:404
st6_ini_nonzerog Step6KitGen:401  zeroModeGen_kerSums_band ZeroModeGen:85  STEKNonzerogL Step34Gen:575  Step2Gen_UN Step2Gen:202
baTwKerZero_holds TwistKer:256  baEKSameRow_holds EKPins:568  Step2Kern_UN_BA Step2Kern:124  BAflow_lam0_window GreenSchur:72  BAflow_real GreenSchur:59
$ grep -rnwE "QtNZGen_KerNZ|QtNZGen_KerNZFam|qtNZGen_kerNZ_band(_at)?|cQVNZNg|assembledRHSNZNg|nz_hkerg|nz_hdriftNg|subGaussStop_nzNg|yMomentBounds_nzNg|budgetNZNg|nzGridEndNg|QtNonzeroGen|QtNonzeroEndGen" RBM3D lakefile* RBM3D.lean
RBM3D/Probe/T2505Pins.lean:36:/-- **D1 default, `QtNZGen_KerNZ`** …      (docstring)
RBM3D/Probe/T2505Pins.lean:267:/-- A consumer of the per-index class, as `nz_hkerg` will be … (docstring)
$ python3 -I cone_aud.py   (planned imports of both row-b files)
cone modules: 182 | BA.* / Chain.Step2Kern / Chain.Qt* in the cone of the planned imports: []
```
D3: no row-b pin (D3 texts are rows a, c; the check compiles, section 2). D4 as it bears on row b: the plan reads only merged texts
(`gridDriftNg_envelope_ev`, `ZeroModeGen_KerSums` as a `B45Gen_Facts` field, `nqBudget_merged_inputsg`); no restated merged class.

## 7. Row packing
```
$ python3 -I census.py   (run in the audit worktree; instance markers QtNonzero:1137, QtNonzeroEnd:1184 = the ticket's instance sections)
QtNonzero.lean         pure  decl-lines=1072 (to line 1136) B=621(8) P=53(3) M=398(17) census=719 x1.06=762
QtNonzero.lean         wide  decl-lines=1072 (to line 1136) B=682(11) P=55(3) M=335(14) census=781 x1.06=827
QtNonzeroEnd.lean      pure  decl-lines=1121 (to line 1183) B=824(10) P=0(0) M=297(20) census=887 x1.06=940
QtNonzeroEnd.lean      wide  decl-lines=1121 (to line 1183) B=862(12) P=0(0) M=259(18) census=925 x1.06=980
```
1a central (×1.06, mean of pure/wide) = (762+827)/2 + (940+980)/2 = 794.5 + 960 = **1,755 ≤ 1,950** (ticket 1,751). Each file ≤ 980 < 2,000.
**Row packing confirmed: row b as pre-signed** (no b | b′ split, no `t/T2505b2`, BA stays 192, U 39–41 / 42).

## 8. Stop lines (ticket "Stop rules") — none hit
new file > 2,000: no (≤ 980 projected) · 1a central > 1,950: no (1,755) · band file edit: none (diff section 1) · cycle / band importing a new file /
`BA`/`Step2Kern` import in the cone: none · binding `T2505_*` or merged pin unprovable: none found · D1 without BA source: no (proved) · `∃` after
`(sz, z)`: no · unguarded flow premise: no · `∀ n` drift: no · new kernel / `FlowFM` field / `STGridRepNgL`: no · restated merged text: no ·
`sz.withLam` / other comparison / other coupling: no · unregistered `Prop` premise: handled by O2 (a 1b obligation). No sign-off request.

## 9. Observations (no verdict effect)
- O1 (x): the bottom-up estimate in (a) (≈ 2,120 with D1 and instance sections; 1.16 × 1,755 = 2,036) exceeds 1,950, but the ticket's row cap is
  defined on the census central, which excludes instance sections for every row. The in-1b checkpoint split proposed in (a)(x) ("file 1 > 1,000
  or file 1 + 960 > 1,950 → `t/T2505b2`") is not a pre-signed trigger: if it fires during 1b it is a stop-and-report for the dispatcher, not
  an automatic split.
- O2 (viii), binding on 1b: file 1 must contain a per-index band theorem with head `QtNZGen_KerNZ` (explicit constant, a total
  `Classical.choose` def as `probeBandC`), besides the family theorem; without it `scanPremises` reports `QtNZGen_KerNZ` (probe output above).
  Its statement reads `mE`/`|E n| < 2` and is a labelled band re-derivation hit of the X1-C1 regex.
- O3 (xi): (a) pastes the name-clash result without its grep command; reproduced in section 6.
- O4: D1 at 1b is `QtNZGen_KerNZ` / `QtNZGen_KerNZFam` = `T2505_KerNZ` / `T2505_KerNZFam` (check `:154-167`) up to the name; the 1b auditor
  diffs by script and adds `example : T2505_shape_KerNZ`-style checks.
- O5: a paper-delta candidate for the new D1 class (loss-free, A-form, `gK`; covered in substance by D37, D588, D699 (b)) belongs in 1b's (d).

## Verdict
Row b (U3s4b) stage 1a, targets 6-9 design gate: **PASS**. D1 text fixed as `T2505-check.lean:154-167`; probe compiles (exit 0, standard
axioms); every 1a deliverable present; no binding stop line hit; row b as pre-signed (central 1,755). No dispatcher sign-off needed.
