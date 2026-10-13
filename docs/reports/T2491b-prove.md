Prover model: claude-sonnet-5-5

## (a) Math preflight (stage 1a of T2491, not repeated)
Section (a) of this row is `docs/reports/T2491-prove.md` (a) lines 3-92, (a″) lines 94-177 and `docs/reports/T2491-1a-audit.md` (verdict PASS: rows U3s2a 1,634 / U3s2b 1,909 / U3s2c 1,817). Row U3s2b = `Chain/NQBudgetGen` + `Chain/NQLinGen`, targets 7-10. No mistake found in (a) for these targets; no (a′).

## (b) Script output
Branch `t/T2491b` HEAD `2cd1f7db` (parent chain: `main` 3238c365 merged in at `151e6ded`, then commits `638fd8a4` NQBudgetGen, `2cd1f7db` NQLinGen). Scratch scripts: scratchpad `T2491b/rep/`.
```
$ date -u; lake build RBM3D.Chain.NQBudgetGen RBM3D.Chain.NQLinGen 2>&1 | tail -1; date -u
Tue Oct 13 08:10:55 UTC 2026
Build completed successfully (3881 jobs).
Tue Oct 13 08:10:57 UTC 2026
$ wc -l RBM3D/Chain/NQBudgetGen.lean RBM3D/Chain/NQLinGen.lean
     982 RBM3D/Chain/NQBudgetGen.lean
    1101 RBM3D/Chain/NQLinGen.lean
    2083 total
$ git status --short; git rev-parse --short HEAD; git log --oneline main..HEAD
2cd1f7db
2cd1f7db T2491b: NQLinGen (U3s2b file 2): GoodLinNg, NQLinConclg/NQLinGoodgL, nqLinGoodgL_of, linear drift/exit/budget, instances
638fd8a4 T2491b: NQBudgetGen (U3s2b file 1): vocabulary, generic budgets, budgetNonAltNg, nqBudget_merged_inputsg, instances
151e6ded T2491b: merge main into t/T2491b
ae93f0a2 T2491: NQGood1Gen docstring of hker_of_case1Ng names the R1 steps as used
2b52ca2e T2491: NQGood1Gen/NQGood2Gen: instances of qvBdNonAltNg_pos and the band bridges, pruned open private lists
3e30e364 T2491: NQGood2Gen section 5 (compiled instances of targets 4-6), root imports, registry owner text of GoodSetNg
dbb1c31b T2491: NQGood2Gen sections 1-4 (vocabulary with explicit Ck, GridAssemblyHypNg fields, hQ_nonAltNg, band re-derivation); NQGood1Gen helper lemmas public under the file stem
55c27778 T2491: NQGood1Gen section 6 (compiled instances of targets 1-3 at the band carrier)
d2b6f5ac T2491: NQGood1Gen sections 1-5 (D1 classes and band discharge, drift tensor, hker_of_case1Ng, QV majorant, shift layer)
9b4bc546 T2491: probe adds the BA instance at the merged flow (sz0, zSeq) for D1 and D3; drops the redundant combined band statement
e6ea965e T2491: probe RBM3D/Probe/T2491Pins.lean (D1, D2, D3, R1, D5 texts, band and BA discharges, target-2 instance; never merged)
$ lake build   (full library, both import lines in RBM3D.lean, HEAD 2cd1f7db; log lines)
Tue Oct 13 08:04:41 UTC 2026   (start)
premises found by scanning: 128 (borrowed 1, owed 61, structural 46, refuted 6, superseded 14).
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/In ...
Build completed successfully (4363 jobs).   exit code: 0   Tue Oct 13 08:05:54 UTC 2026   (end)
$ lake env lean axioms.lean   # collectAxioms over the public theorem/def/abbrev of the two files (names.txt)
declarations checked: 39; exactly the three standard axioms: 39; a proper subset: 0 []; outside the three: []
$ grep -cE "sorry|admit|native_decide|^axiom|withLam" NQBudgetGen.lean NQLinGen.lean   ->  0, 0
$ lake env lean docs/tickets/checks/T2491-check.lean   -> exit 0, error lines 0
$ git diff main...HEAD --stat
 RBM3D.lean                   |    2 +
 RBM3D/Chain/NQBudgetGen.lean |  982 +++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/NQLinGen.lean    | 1101 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2491Pins.lean   |  397 +++++++++++++++
 4 files changed, 2482 insertions(+)
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Chain ":!RBM3D/Chain/NQBudgetGen.lean" ":!RBM3D/Chain/NQLinGen.lean" | wc -l
       0
$ grep -nE "NQLin|NQBudget|budgetNonAlt|nqLinGood|U3s2b" RBM3D/Test/Axioms.lean | wc -l
       0
$ date -u; git rev-parse --short main
Tue Oct 13 08:13:31 UTC 2026
6ccc6be2
```
Pins (script `pindiff.py` + `pins.lean` = the four check defs `T2491_GoodLinNg`, `T2491_NQLinConclg`, `T2491_NQLinGoodgL`, `T2491_NQLinGoodOf` copied verbatim by script):
```
T2491_GoodLinNg vs GoodLinNg: identical after dropping the binder {d} {sz} and the name: True (582/582 chars, whitespace-collapsed)
T2491_NQLinConclg vs NQLinConclg, T2491_NQLinGoodgL vs NQLinGoodgL: the only differences are the references T2491_GoodLinNg -> GoodLinNg, T2491_NQLinConclg -> NQLinConclg
example : @T2491_GoodLinNg = @GoodLinNg := rfl ; example : @T2491_NQLinConclg = @NQLinConclg := rfl ; example : @T2491_NQLinGoodgL = @NQLinGoodgL := rfl
example : T2491_NQLinGoodOf := nqLinGoodgL_of      (compile: exit 0, error lines 0; the family shape of the theorem is the check shape)
```
Public statements by script (`stmts.py`: line, name, conclusion with whitespace collapsed, cut at 190 characters; the full text is in the files; defs show their type):
```
NQBudgetGen:
NQBudg:53 assembledRHSNonAltNg : ℝ
NQBudg:71 NQBudgetGen_kapFar : ℝ
NQBudg:76 NQBudgetGen_qvFar : ℝ
NQBudg:81 assembledRHSNonAltNg_band : assembledRHSNonAltNg (bandStep2Mat sz E) s v K n k (nqGood1C d k Λg κ') ε Γ Λ Φ D' D'' D_Y τK εq X0 a = RBM.Ind.assembledRHSNonAltN sz E s v K n k Λg κ' ε Γ Λ Φ D ...
NQBudg:86 NQBudgetGen_kapFar_band : NQBudgetGen_kapFar sz n k (nqGood1C d k Λg κ') ε = RBM.Ind.nqBudget_kapFar sz n k Λg κ' ε
NQBudg:89 NQBudgetGen_qvFar_band : NQBudgetGen_qvFar sz n k (nqGood1C d k Λg κ') ε = RBM.Ind.nqBudget_qvFar sz n k Λg κ' ε
NQBudg:101 NQBudgetGen_inv_one_sub_le : (1 - v)⁻¹ ≤ Nn
NQBudg:115 NQBudgetGen_kappa_le_kapFar : kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤ NQBudgetGen_kapFar sz n k Ck ε
NQBudg:159 tbInitNg : κ 0 K * X0 ≤ Cκ * G * B K ^ k
NQBudg:169 tbDriftNg : Δ * ∑ j ∈ Finset.range K, (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤ Cκ * a * B K ^ k * ∑ j ∈ Finset.range K, Δ / Cm.eta n (u j) + ((K : ℝ) * Δ) * (Cfar * b + Cε * δmax)
NQBudg:215 tbQvNg : ∑ j ∈ Finset.range K, Δ * ((k : ℝ) * nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1)) (Cm.eta n (u (j + 1)))) ≤ (k : ℝ) * Cκ ^ 2 * G * (B K ^ k) ^ 2 * ∑ j ∈ Finset.range K, Δ / Cm.e ...
NQBudg:273 qvBdNonAltNg_eq_qvShape : qvBdNonAltNg Cm n k Ck ε Γ Λ D'' u w = nqBudget_qvShape k (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) (((sz.W ...
NQBudg:286 tbInitNonAltNg : kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * G * (sz.Bctl n (v n)) ^ k
NQBudg:308 tbDriftNonAltNg : gridStep s v K n * ∑ j ∈ Finset.range (K n), (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) * dDriftNonAltNg Cm n (gridTime s v K n j ...
NQBudg:374 tbQvNonAltNg : ∑ j ∈ Finset.range (K n), (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' (K n) a j : ℝ) ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (Ck * ε)) ^ 2 * (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k ...
NQBudg:452 budgetNonAltNg : assembledRHSNonAltNg Cm s v K n k Ck ε Γ Λ Φ D' D'' D_Y τK εq X0 a ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k
NQBudg:734 nqBudget_merged_inputsg : ∀ᶠ n : ℕ in atTop, (∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ∧ (∑ j ∈ Finset.ra ...
NQLinGen:
NQLinG:59 GoodLinNg : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
NQLinG:71 NQLinConclg : Prop
NQLinG:92 NQLinGoodgL : Prop
NQLinG:103 bandStep2_GoodLinN : GoodLinN sz n (E n) u k Γ Φ₁ Φ₂ Φ₃ = GoodLinNg (bandStep2Mat sz E) n u k Γ Φ₁ Φ₂ Φ₃
NQLinG:107 bandStep2_NQLinConcl : NQLinConcl sz E s t ↔ NQLinConclg (bandStep2Mat sz E) (Sizes.seqP sz) s t
NQLinG:111 bandStep2_NQLinGood : NQLinGood d ↔ NQLinGoodgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))
NQLinG:127 measurableGoodLinNg : MeasurableSet (GoodLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃)
NQLinG:144 goodSetNg_subset_goodLinNg : H ∈ GoodLinNg Cm n u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ
NQLinG:344 nqLinConclg_of : NQLinConclg Cm μ s t
NQLinG:358 nqLinGoodgL_of : NQLinGoodgL d law Flow mkM T0
NQLinG:389 nqLinGood_holds_of_gen : NQLinGood d
NQLinG:408 dDriftLinNg : ℝ
NQLinG:413 nqLinExitTauNg : PathΩ sz → ℕ
NQLinG:421 dDriftNonAltNg_eq_lin : dDriftNonAltNg Cm n u k Γ Φ = dDriftLinNg Cm n u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ
NQLinG:430 driftTensorNg_norm_le_of_goodLin : ‖driftTensorNg Cm n u M σ a‖ ≤ dDriftLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃
NQLinG:454 nqLin_hdriftNg : ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n), ‖driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ b‖ ≤ dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) ...
NQLinG:465 mem_of_lt_nqLinExitTauNg : Cm.Hpath s v K n j ω ∈ {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} ∩ GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
NQLinG:473 nqLinExitMeasNg : MeasurableSet[filt sz j] {ω | j < nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω}
NQLinG:485 subGaussStop_linNg : SubGaussStopNg Cm σ (gridTime s v K n) (nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n) (fun j ω => ZvecNg Cm s v K n j σ ω) m a j (cQVNonAltNg Cm s v K n k Cv ε Γ Λ  ...
NQLinG:519 assembledRHSLinNg : ℝ
NQLinG:538 tbDriftLinNg : gridStep s v K n * ∑ j ∈ Finset.range (K n), (kappaNonAltNg k Ck (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) * dDriftLinNg Cm n (gridTime s v K n j) k (Γ ...
NQLinG:605 budgetNonAltLinNg : assembledRHSLinNg Cm s v K n k Ck ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq X0 a ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k
```
Compiled nonempty instances (same files, section 6, band carrier `bandStep2Mat sz0 Einst`, `d = 3`, `n = 0`, `k = 3`, `σ = (+,-,+)`, `ε = 4/5`, `W = 32`, `lam = 1/64`, `K = 4`, grid `u_j = j/128`; `index.py`):
```
NQBudgetGen: 12 examples from line 756 (section 6); lines:
  789 799 809 826 835 852 868 878 887 902 918 958
  789 /-- Band bridges of the vocabulary at the data (`Ck = nqGood1C 3 3 10 (1/2)`, `E ≡ 1/2`). -/
  799 /-- `NQBudgetGen_inv_one_sub_le` at `E = 1/2`, `v = 1/32`, `N = 2^21`: `(1 - v)⁻¹ ≤ N`. -/
  809 /-- `NQBudgetGen_kappa_le_kapFar` at `sz0`, `n = 0`, `i = 1`, `m = 4` on the grid. -/
  826 /-- Instance of `tbInitNg`: `K = 4`, `κ ≡ 2`, `C_κ = 2`, `G = 3`, `X0 = 3 B_0^3`. -/
  835 /-- Instance of `tbDriftNg`: `Δ = 1/128`, `K = 4`, `κ ≡ 2`, `ε ≡ 1`, `C_κ = C_far = 2`, `C_ε = 
  852 /-- Instance of `tbQvNg`: `Δ = 1/128`, `K = 4`, `k = 3`, `κ ≡ 2`, `C_κ = C_far = 2`, `C_e = C_c
  868 /-- `qvBdNonAltNg_eq_qvShape` at `n = 0`, `k = 3`, `ε = 4/5`, `(Γ, Λ) = (4, 3)`, `D'' = 5`, `(u
  878 /-- `tbInitNonAltNg` at the data: `G = 4`, `X0 = 4 B_0^3`. -/
  887 /-- `tbDriftNonAltNg` at the data: levels `(Γ, Φ) = (4, 1)`, `D' = 6`. -/
  902 /-- `tbQvNonAltNg` at the data: levels `(Γ, Λ) = (4, 3)`, `D'' = 5`, label `aFar`. -/
  918 /-- **`budgetNonAltNg` at the data** (`d = 3`, `sz0`, `n = 0`: `L = 4`, `W = 32`, `N = 2^21`; `
  958 /-- **`nqBudget_merged_inputsg` at the data of `GridEnvelopeNCheck`** (`d = 3`, `sz0`, `κ_m = 1
NQLinGen: 15 examples from line 878 (section 6); lines:
  938 943 947 954 963 997 1001 1011 1017 1025 1032 1039 1045 1061 1079
  938 /-- **Instance of `goodSetNg_subset_goodLinNg`** at the data (`k = 3`, `Γ = 4`, `Φ = 1`): a mem
  943 /-- **Instance of `measurableGoodLinNg`** at the data. -/
  947 /-- Band bridge of the set at the data (`rfl`): the merged `GoodLinN` is `GoodLinNg` at the ban
  954 /-- **Target 9 (a), `nqLinConclg_of`** at `(sz0, Einst, s ≡ 0, t ≡ 1/16)`: the pin `NQLinConclg
  963 /-- **Target 9 (b), `nqLinGoodgL_of`** over the band family `(seqP, STFlow, bandStep2Mat · (STf
  997 
  1001 /-- **Instance of `dDriftNonAltNg_eq_lin`** at the data. -/
  1011 
  1017 /-- The linear drift level at the data is positive (so the bound above is not vacuous). -/
  1025 /-- **Instance of `nqLin_hdriftNg`**: along the walk, strictly before the exit time of `GoodSet
  1032 /-- **Instance of `mem_of_lt_nqLinExitTauNg`**: strictly before the exit, the grid state is in 
  1039 /-- **Instance of `nqLinExitMeasNg`**: `{j < nqLinExitTauNg}` is `filt sz0 j`-measurable. -/
  1045 /-- **Instance of `subGaussStop_linNg`**: the `SubGaussStopNg` input of `AssembledNg` at the ex
  1061 /-- **`tbDriftLinNg` at the data** (levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, 12, 1)`, `D' = 6`). -/
  1079 /-- **`budgetNonAltLinNg` at the data** (`d = 3`, `sz0`, `n = 0`: `L = 4`, `W = 32`, `N = 2^21`
```
Not an `example` but a theorem: `nqLinGood_holds_of_gen` (NQLinGen:389), the band re-derivation `NQLinGood d` for every `d`, from `nqLinGoodgL_of` at the band family with no open hypothesis; example 963 applies `nqLinGoodgL_of` at `d = 3` and returns both `NQLinGoodgL 3 ...` and the merged `NQLinGood 3`.
Open hypotheses of instances: only example 954 (`nqLinConclg_of`) keeps `hSE : STSEforLnConclgL ...` (the registered pin `lem:SEforLn`, U2). Every other instance discharges every premise. Nondegeneracy: `Ck = nqGood1C 3 3 10 (1/2)` stays abstract (only `> 0`); the budget instances hold for every `Ck > 0` (`ε₀ = Ck + 12`); `H_0 = 0 ∈ GoodSetNg ∩ GoodLinNg` at `(Γ, Λ, Φ, Φ₁, Φ₂, Φ₃) = (4, 3, 1, 1, 12, 1)`; the exit time is positive at every sample (example 997); `dDriftLinNg > 0` (example 1017); `K = 4`, `Δ = 1/128`.
Greps and layering (`greps.sh`; hypothesis rules of the ticket):
```
$ grep -cE "def .*[Kk]er\b|def Ugen" (NQBudgetGen, NQLinGen)
RBM3D/Chain/NQBudgetGen.lean:0
RBM3D/Chain/NQLinGen.lean:0
$ grep -cE "STGridRepNgL|ST_gridMart_of_repN"
RBM3D/Chain/NQBudgetGen.lean:0
RBM3D/Chain/NQLinGen.lean:0
$ grep -cE "(def|abbrev|structure) (GoodSetNg|GridGoodNConclg|qvFormNg|STXiLg|STXiLKg|STNQConclgL|STXiBootgL|STIterRgL|STIngRgL|StepDecompGen_LoopForm|GridRepTailGen_Ker| ...
RBM3D/Chain/NQBudgetGen.lean:0
RBM3D/Chain/NQLinGen.lean:0
$ grep -n "^import RBM3D.BA" RBM3D/Chain/NQ*Gen*.lean
(no output above = none)
$ grep -n "^import" (both files)
RBM3D/Chain/NQBudgetGen.lean:6:import RBM3D.Chain.NQGood2Gen
RBM3D/Chain/NQBudgetGen.lean:7:import RBM3D.Induction.NQBudget
RBM3D/Chain/NQLinGen.lean:6:import RBM3D.Chain.NQBudgetGen
RBM3D/Chain/NQLinGen.lean:7:import RBM3D.Induction.NQLin
$ importers of the two modules
RBM3D/Chain/NQLinGen.lean
RBM3D.lean
$ grep -nE "∀ \(sz : Sizes d\)" (both files)
RBM3D/Chain/NQLinGen.lean:93:    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
RBM3D/Chain/NQLinGen.lean:94:    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
RBM3D/Chain/NQLinGen.lean:359:    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
RBM3D/Chain/NQLinGen.lean:360:    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
RBM3D/Chain/NQLinGen.lean:361:    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
RBM3D/Chain/NQLinGen.lean:362:    (E lam' : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
RBM3D/Chain/NQLinGen.lean:363:    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
RBM3D/Chain/NQLinGen.lean:365:    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
RBM3D/Chain/NQLinGen.lean:367:    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
RBM3D/Chain/NQLinGen.lean:369:    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
RBM3D/Chain/NQLinGen.lean:370:    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z)) :
$ sorry/admit/native_decide/axiom/withLam
RBM3D/Chain/NQBudgetGen.lean:0
RBM3D/Chain/NQLinGen.lean:0
```
X1-C1/C1 regex (`\bmE\b|zt E|…|norm_mE`) on the two files: NQBudgetGen 14 hits = {module doc 13-14; `open` 42, 768; docstrings 80, 760, 788, 916; band-bridge statements 83, 87, 90; instance code 777, 781, 947}; NQLinGen 28 hits = {module doc 14; docstrings 58, 386, 883, 952, 960, 1077; `open` 49, 889; band-bridge statements 108, 112-113; band re-derivation 391-392; instance code 897, 907, 913-914, 954-956, 963-966, 1093-1095}. No hit in a generic statement or proof.
Name clash (`git grep -h -w -F -f short.txt <ref> -- RBM3D` minus the two files and `Probe`, 39 public names; 08:07 UTC): main 6ccc6be2 0 | t/T2482b 0 | t/T2484b 0 | t/T2486 0 | t/T2486b 0 | t/T2489 0 | t/T2489b 0 | t/T2490 0 | t/T2491 0 | t/T2492 0 | t/T2493 0 | t/T2494 0 | t/T2495 0 | t/T2496 0.
`open private` (no `private` deleted): NQBudgetGen:31 `nqBudget_absorb nqBudget_gridTime_nonneg nqBudget_gridTime_le nqBudget_K_mul_step nqBudget_final` (NQBudget, model-free); NQLinGen:32 `GridGoodGen_precL_whp GridGoodGen_one_le_STXiLg GridGoodGen_one_le_STXiLKg GridGoodGen_meas_STksimLKMg GridGoodGen_meas_STelklkMg GridGoodGen_meas_STegtMg` (GridGoodGen §4a), :35 `gridGood_whp_forall_mem gridGood_whp_and gridGood_gridTime_mem gridGood_measurableSet_forall gridGood_measurableSet_imp` (GridGoodN), :38 `nqLin_rpow_third nqLin_sqrt_bound nqLin_clause nqLin_D2_arith nqLin_absorb nqLin_gridTime_nonneg nqLin_gridTime_le nqLin_K_mul_step nqLin_final` (NQLin, model-free). Instance-only: NQBudgetGen:768 `W0 lam0 N0 im_ge u_le u_nonneg u_lt_one u_mono eta_inv_le_N eta_inv_le_v Bseq Bseq_pos Bseq_mono Kg0 u4 step0 N_eps1 ha1_inst … he4_inst Cpos`; NQLinGen:889 `W0 lam0 L0r rpow32_fifth rpow32_four_fifth im_mE_half hσ3 hW1 hWε hdW hvL eta_inv_le_N eta_inv_le_v step0 N_eps1 ha1_inst … he4_inst`.
Tables as used (ticket report items 4-7):
* D1 `NQGoodGen_KerNAL`: enters only `subGaussStop_linNg` (hypothesis `hKer`, NQLinGen:491, passed to `hQ_nonAltNg`) and the instance `NQLinGen_kerNAL0` (= `nqGoodGen_kerNAL_band_at`); NQBudgetGen has no D1/R1 hypothesis. D2 and D5 are row c (not here). D3: inline `‖Cm.m n‖ ≤ 1` (per index) in `NQBudgetGen_inv_one_sub_le`, `tbDriftNonAltNg`, `tbQvNonAltNg`, `budgetNonAltNg`, `tbDriftLinNg`, `budgetNonAltLinNg`, `subGaussStop_linNg`; `∀ n, (Cm.m n).im ≤ 1` in `nqBudget_merged_inputsg` (the premise of the merged `sum_weighted_stepErrNg_le`); `nqLinConclg_of` does not read D3. BA sources: those of row a (`T2491-prove.md` (b) l.234), unchanged.
* Family-premise rows as used (rows 1-5 enter `nqLinGoodgL_of`, guard as in the table): 1 `hSE : STSEforLngL d STAny law Flow mkM Hf T0`; 2 `hFlow : Step2EventsGen_Flow d Flow T0`; 3 `hL` (guarded `0 < κ → Flow … →`); 4 `hW` (guarded; in the check shape, **not read by the proof**); 5 `hLaw` (unguarded) and `hC : Step34Gen_LCompat` (unguarded; **not read**). No pinned `∃` after `(sz, z)`; no `GridDriftNg`/`HierarchyNg` premise. The U5S-C3 grep hits (NQLinGen:93-94, 359-370) are exactly `NQLinGoodgL` and `nqLinGoodgL_of`.
* UBA-C1 (R1 only): R1 (`hcmp`, `hA`, `hCv`, `hdW`, `hAk`) enters only `subGaussStop_linNg` (NQLinGen:490-506) through `hQ_nonAltNg`; `tbDriftNg`, `tbQvNg`, `budget*`, `nqBudget_merged_inputsg`, `GoodLinNg`, `nqLinConclg_of`, `nqLinGoodgL_of` never; `step34Gen_*` and `withLam` do not occur (grep).
* Registry: no `Test/Axioms.lean` line changed or added for this row (the `grep -nE "NQLin|NQBudget|budgetNonAlt|nqLinGood|U3s2b" RBM3D/Test/Axioms.lean | wc -l` above prints 0); the scan line above (128 premises) equals the U3s2a one in `T2491-prove.md` l.185. Importers: `RBM3D.lean` (two import lines after the last `import`) and `NQLinGen` imports `NQBudgetGen`; no `Q*`, `Qt*`, `Iterations*`, `Step3/4`, U4s3 or U5 file imports either (grep of `import RBM3D.Chain.NQBudgetGen|NQLinGen` finds `RBM3D.lean` and `NQLinGen.lean` only). C6/D2: row c.

Narrative.
1. Size: NQBudgetGen 982 and NQLinGen 1,101 lines (2,083 in all; row estimate 1,909 in the 1a, `T2491-prove.md` l.86, +174); both under the 2,000 stop line; no reserve file. `wc -l` was run at each section commit (982 at the first, 1,101 at the second).
   C6 figure: n/a for this row (`stKloop_lip`, D2, is in `NQEndFlowGen`, row c). No RBM1D/RBM2D port: the ported statements and proofs are the band files `Induction/NQBudget` and `Induction/NQLin` of this project (cited per declaration in the docstrings), so no RBM1D/RBM2D file:line, commit or diff-stat is due.
2. Method: every band theorem of `NQBudget:200-857` and `NQLin` §1-§5 is ported to a carrier `Cm : Step2Mat sz` by a mechanical rewrite (`etaT (E n)` to `Cm.eta n`, `(mE (E n)).im` to `(Cm.m n).im`, `nqGood1C d k Λg κ'` to an explicit `Ck`, `stepErrN` to `stepErrNg`, `kappaNonAltN` to `kappaNonAltNg`, `dDriftNonAltN` to `dDriftNonAltNg`), then the places that read `hE : |E n| < 2` are changed by hand to `hL : StepDecompGen_LoopForm Cm E` and `hm : ‖Cm.m n‖ ≤ 1` (D3). The statements keep the band hypotheses, order and losses otherwise.
3. `tbInitNg` is the model-free band `tbInitN` under the ticket's name (one-line proof); `nqBudget_qvShape`, `nqBudget_sum_succ_le`, `nqBudget_sqrt_add_le`, `nqLinPhi1-3` are used by name.
4. Target 9: `GoodLinNg` has no Hermitian clause and no decay clause, and its three clauses are `STksimLKg`, `STelklkg`, `STegtg` at `Hf n u ω` by definition; the per-carrier theorem `nqLinConclg_of` therefore needs only `LoopForm` (η > 0, measurability), `Step2EventsGen_Law`, `SizeTendsto`, the window `0 ≤ s`, `t < 1` and `STSEforLnConclgL` on `[s, t]` (restricted to `[s, v]` by `NQLinGen_SE_restrict`). The family theorem keeps `WalkForm` and `Step34Gen_LCompat` because the check text `T2491_NQLinGoodOf` has them; they are unused (observation, not a paper delta).
5. `nqLinExitMeasNg` and `subGaussStop_linNg` do read `WalkForm` (adaptedness of the walk to the filtration, `gridExitTauNg_measurableSet`) and `LoopForm` (`measurableGoodSetNg`, `measurableGoodLinNg`).
6. Band re-derivation `nqLinGood_holds_of_gen d : NQLinGood d` uses `stSEforLn_holds` through `bandFM_STSEforLn`, `Step2EventsGen_bandFlow`, `stepDecompGen_loopForm_band` (with `|lemE z| < 2` from `abs_lemE_lt_two`, `ST_flow_im_pos`), `stepDecompGen_walkForm_band`, `Step2EventsGen_bandLaw`, `bandStep34_LCompat`; the other band theorems of rows 7-10 are not re-derived (the acceptance list names only `nqLinGood_holds` for this row).
7. Budget instances reuse the band numerics by `open private` from `NQBudget` and `NQLin`: the generic hypotheses at `bandStep2Mat sz0 Einst` are the band ones up to definitional unfolding (`Cm.eta 0 u = etaT (Einst 0) u`, `stepErrNg (bandFM ..) = stepErrN ..`), so `hlog_instance`, `hR_instance` and `ha1_inst … he4_inst` are passed unchanged.
8. Stop rules: none fired (files under 2,000; no BA import; no band or merged file edited, G1 diff 0 lines; no private deleted; no new kernel, carrier field or `STGridRepNgL` premise; no `sz.withLam`; no comparison other than R1; no `Prop` premise left unconcluded: the scan count is unchanged).
9. `main` moved on during the stage (`6ccc6be2` at 08:13:31 UTC, last lines of the git block above; I merged `3238c365` at the start). The merge of `main` into the branch conflicted in `RBM3D.lean` (import lines) and `RBM3D/Test/Axioms.lean` (the `GoodSetNg` owner text); both were resolved with main's version (`git checkout --theirs`), which already holds the U3s2a lines.

## (c) Mathlib names (resolved by script from the identifiers of the two files; module under `Mathlib`/`Init`/`Std`/`Batteries`)
Filter.Eventually.of_forall, Finset.Icc, Finset.card_range, Finset.mem_Icc, Finset.mul_sum, Finset.range, Finset.single_le_sum, Finset.sum_add_distrib, Finset.sum_congr, Finset.sum_const, Finset.sum_le_card_nsmul, Finset.sum_le_sum, Fintype.card_fin, Iff.rfl, MeasurableSet.inter, Nat.card_Icc, Nat.cast_nonneg, Nat.cast_sub, Nat.lt_succ_of_le, Nat.mul_pos, Nat.one_le_pow, Nat.zero_le, Real.coe_toNNReal, Real.log, Real.log_nonneg, Real.one_le_rpow, Real.rpow_le_rpow, Real.rpow_le_rpow_of_exponent_le, Real.rpow_nonneg, Real.sqrt, Real.sqrt_eq_rpow, Real.sqrt_le_sqrt, Real.sqrt_mul, Real.sqrt_one, Real.sqrt_sq, Set.mem_ofPred_eq, Set.ofPred_and, abs_of_pos, add_le_add, add_nonneg, add_zero, div_eq_mul_inv, div_le_iff₀, div_nonneg, inv_pow, le_max_left, le_max_right, le_mul_of_one_le_left, le_of_eq, le_rfl, measurableSet_le, measurable_const, MeasureTheory.measure_mono, mul_comm, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_one, mul_self_nonneg, MulZeroClass.mul_zero, norm_add₃_le, norm_sum_le, nsmul_eq_mul, one_mul, one_pos, pow_le_pow_left₀, pow_mul', pow_nonneg, pow_pos, sq_nonneg, zero_add
Names verified absent: none needed (no name was invented; every Mathlib name above was resolved in the environment).

## (d) Open issues and paper-delta candidates
1. **T2491-b1** (Lean/paper, D3 at the budget): over a carrier, `|E n| < 2` is replaced by `StepDecompGen_LoopForm Cm E` (η = (1-u) Im m, `0 < Im m`) and the inline `‖Cm.m n‖ ≤ 1`; `nqBudget_merged_inputsg` takes `DecayGen_Spec` and `∀ n, (Cm.m n).im ≤ 1` instead of `|E n| ≤ 2 - κ` (band: `Im m ≤ 1` by `nqBudget_im_le_one`; equality `|m| = 1`). Same content as T2491b of row a.
2. **T2491-b2** (Lean/paper, constant): the budget vocabulary `assembledRHSNonAltNg`, `NQBudgetGen_kapFar`, `NQBudgetGen_qvFar`, `tb*NonAltNg`, `budget*Ng` carry the explicit kernel constant `Ck` (band: `nqGood1C d k Λg κ'`, a `Classical.choose`); the band readings are `rfl` (`*_band` bridges). Continues T2491a.
3. **T2491-b3** (Lean/paper, linear set): `GoodLinNg`/`NQLinConclg` are stated with `TimeIcc s v n`, `Cm.Hpath` and the law `μ` of the flow matrix; the grid transfer uses `Step2EventsGen_Law` (band: `map_pathH_eq`). No hypothesis of the paper changes.
4. Observation for the dispatcher: the unused premises `hW` (row 4) and `hC` of `nqLinGoodgL_of` could be dropped from the check shape; if so, the BA discharge of target 9 needs rows 1, 2, 3, 5 (`Law`) only. Left as in the check.
5. Observation: the module docstrings carry 9 (NQBudgetGen: lines 10-21) and 11 (NQLinGen: lines 10-23) long-line warnings in the full build log, as the merged `Induction/NQGood2.lean`; no other warning in the two files.
6. For the hub: the merge brings `Chain/NQBudgetGen.lean`, `Chain/NQLinGen.lean` and their two import lines in `RBM3D.lean` (after the last `import`); `RBM3D/Probe/T2491Pins.lean` is on the branch (from `t/T2491`) and must not be merged. Row c (`NQEndLinGen`, `NQEndFlowGen`) reads `nqLinGoodgL_of`, `nqLinConclg_of`, `budgetNonAltNg`/`budgetNonAltLinNg`, `nqBudget_merged_inputsg`, `NQBudgetGen_kapFar` by name.
