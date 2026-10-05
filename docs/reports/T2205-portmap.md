Prover model: claude-sonnet-5-5
# T2205 portmap — BA-D3: Step 1 and `lem:main_ind_BA` over a family of flows in a coupling window
Written Mon Oct  5 21:50:44 UTC 2026.  Probe `RBM3D/Probe/T2205Pins.lean` on `t/T2205` (HEAD `96e4087`, base `cef761a`); prove report `docs/reports/T2205-prove.md` (script output b.1-b.4).  Line numbers below are probe lines unless a file is named; `S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2205`.

## P.1 BA count (target 7)
Ticket baseline: 4 used / 63 planned with BA-D3 (cap 70, DECISIONS §52).  This note: **66 planned** (63 + BA-D8 + BA-S2a + BA-V2b, with BA-V2 split into V2a/V2b); no row cancelled (P.4); folding S2a back into S2 gives 65 at the price of an S2 central size of 1800 lines (over the 600-1500 rule).  Within the cap; no question to Jun.  Lines (central): +800 (D8) +700 (S2a) -100 (S3: 1000 → 900, a port) +300 (V2: 1500 → V2a 1100 + V2b 700, a port) = +1700 on the T2161 P.9 total of 67.1k.

## P.2 Registry class and owner of every `Prop` of the probe (DECISIONS §16, §20, §66; T2197 ticket line 36: carrier predicates are owed like their band forms)
| `Prop` (probe name) | class | owner row | note |
|---|---|---|---|
| `STLKgL`, `STLmaxgL`, `STDecaygL`, `STDecayStronggL`, `STLocalMaxgL`, `STLocalEntrygL`, `STExp2gL`, `STKboundgL`, `STStep1LoopgL`, `STStep1WeakgL`, `STInitialGT2gL`, `STLWassmExpgL` | owed (as the band forms `STLK`, ... `Axioms.lean:91-158`) | BA chain: S3 (Step 1 pair), V2a/V2b (the six conclusions), K4 (`STKboundgL`), G3/G4 (`STInitialGT2gL`), L4/V1 (`STLWassmExpgL`) | T2197 registers them (expected `STLmaxgL`, `STLKgL`, `STLocalMaxgL`, `STKboundgL`) |
| `STLmaxUgL`, `STLKUgL`, `STAvgUgL`, `STLocalEntryUgL`, `STGdecayWgL`, `STStep2ConclgL`, `STDecayStrongUgL`, `STStep5ConclgL`, `STExp2UgL`, `STKwardgL` | owed (like merged `STLmaxU` ...) | T8, U1-U6, V1 | uniform-in-time step forms (probe 6.1) |
| `BAGbEXP` (+ `BAGbEXPpre`, `BAGbEXPconcl`) | owed | BA-G6 | T2205e: event form needed |
| `BAConArg'` (+ `BAConArgLoop`, `BAConArgVec`) | owed | BA-S1 | T2197 Amend 1; premise added (L5) |
| `BATrivialLmax` | owed (new) | BA-S2a (new) | (lRB1) deterministic below `1 - c₁` |
| `BABootstrap` | owed (new) | BA-S2b | band `step1TargetV3_holds` with the carrier |
| `BAStep1` | owed | BA-S3 | family form (replaces T2161 `:1170`) |
| `BAMainIndR d R` (`R` = `STReg5I`..`IV`), `BAMainInd` | owed (`BAMainIndR` new) | V2a (regimes), V2b (`BAMainInd`) | `BAMainInd_iff_any` |
| `BAStep3R`, `BAStep4R`; `BAStep5R`; `BAStep6R` | owed (new regime pins) | U1-U3; U4-U6; V1 | shape of merged `STStep3R/4R/5R`, T2191 `STStep6R` |
| `BAKboundF`, `BAKwardF`, `BAStep2` (family style) | derived, not registered | V2a proves them from the per-flow `BAKbound` (K4), `BAKward` (K5), `BAStep2` (T8) | `BAmember_transfer` + the `*_congr` lemmas (compiled for any tail-local `Q`) |
| `BAFlow`, `BAWinBulk`, `BAFamZ`, `BAFamCone`, `BAMem`, `BAGenPos`, `BAPat`, `BAinS`, `BAinT`, `TailLocal`, `LawComp`, `PrecL`, `FlowFM.EvEq`, `FlowFM.CompRel` | structural | - | conditions on data / quantifier towers; `LawComp` is discharged for `seqP` and `seqP ∘ withLam 0` |
| `BAExactLaw` | proved elsewhere (merged T2206 theorems; no registry line) | - | `BAExactLaw_of_T2206` compiles in scratch against `main` (b.3); in the probe it is the one hypothesis of `BAMainIndR_of_cover`, `BA_mainInd_of_regimes` |
| `BAgapReal`, `BAmWindow`, `BAzztE_inv`, `BAWinBulk_of_dom_stmt`, `BAFamCone_closed_stmt`, `BAFlowMember`, `BALmaxFromLK` | proved in the probe (`*_holds`) | D8 (first four), S3 (last two) | no registry line after the port |

## P.3 Split: rows new or changed against T2161 P.9 (all other rows unchanged)
Probe section sizes (script `s_sizes.py`; the numbers below cite them):
```text
$ python3 s_sizes.py   # lines of each probe section (start-end, count, title)
   45-46       2  1. The vocabulary of T2197 -/
   47-115     69  1.1. The flow of the block Anderson model along a size sequence, and the loops
  116-285    170  1.2. The carrier over a law (T2173 `:1944-2012`, T2161 section 6; substitution
  286-445    160  1.3. `lem:main_ind_BA` and the steps that change: flow data, the chain pins, `
  446-478     33  1.2b The band bridges (T2161 `:985-1008`, substitution L4: the law is `Sizes.s
  479-523     45  2. The deterministic pins of the coupling window (target 2)
  524-672    149  2.1 `BAgapReal` (proved) -/
  673-745     73  2.2 `BAzztE_inv` (proved) -/
  746-1230   485  2.3 `BAmWindow` (proved): a one-step Newton-Kantorovich contraction at the cou
 1231-1269    39  3. The family predicates, the window and the closure (targets 1 and 2)
 1270-1354    85  3.1 Elementary facts -/
 1355-1382    28  3.2 `BAWinBulk_of_dom` (proved from `BAmWindow`) -/
 1383-1494   112  3.3 The ConArg source of a member: closure of the family (route (A), compiled)
 1495-1610   116  4. The family pins `BAStep1`, `BAMainInd` and the cost of route (A) (target 1)
 1611-1680    70  4.2 More tail congruence and the case split in time (used by the skeleton of s
 1681-1736    56  4.3 The family pins (replacing the per-flow `BAStep1` `:1170` and `BAMainInd` 
 1737-1884   148  5. The ConArg chain from `s₀ = 1 - c₁` (targets 3 and 4)
 1885-2106   222  5.3 `BAFlowMember` is a theorem (the cost of route (A), compiled)
 2107-2193    87  6. Steps 2-6 per member and the gluing of the regimes (target 5)
 2194-2269    76  The endpoints `u = t` of the uniform conclusions (copies of the merged `STLK_o
 2270-2493   224  6.2 The per-member step pins (family style) and the one-step assembly -/
 2494-2520    27  6.3 The member transfer: single-flow pins give the family-style pins -/
 2521-2615    95  6.4 The regime gluing in generic position (all four stages nonempty at every s
 2616-2729   114  6.5 What BA needs from the subsequence transfer (A) (target 5)
 2730-2788    59  6.6 `LawComp` for `seqP` (the measure-preserving reindexing; proof pattern of 
 2789-3309   521  6.7 `BA_mainInd_of_regimes`: the main induction in general position, through (
 3310-3447   138  7. Compiled nonempty instances at `d = 3`
 3448-3603   156  7.1 The family pins applied along `sz0` (every deterministic hypothesis discha
 3604-3691    88  7.2 The one-point sequence `(L, g) = (4, 10)` (interior gaps; the construction
 3692-3819   128  7.3 The skeleton theorems at `d = 3` (the pins they combine stay hypotheses: t
 3820-3860    41  7.4 Extreme inputs (target 8): `t₀ < 1 - c₁`, `c₁ = 1/2`, `u = 1 - c₁` (source
 3861-3867     7  8. Comparison with the check file (`docs/tickets/checks/T2205-check.lean`)
```
| id | file (`RBM3D/…`) | role | content (probe part) | lo | central | hi | depends on | against P.9 |
|---|---|---|---|---|---|---|---|---|
| BA-D8 | BA/CouplingWindow | prover (port) | `BAgapReal`, `BAzztE_inv`, `BAmWindow`, `BAWinBulk_of_dom`, public `tr M²` spectral form, `BAwindow_step/iter/floor` (2.1-2.3, 3.2: 735 lines compiled) | 600 | 800 | 1100 | T2189 (merged `BA/MFixedPoint`) | NEW; dispatcher prior prover-hard 600/900/1300, lowered: the proofs exist |
| BA-S1 | BA/ConArg | prover-hard | `BAConArg'` | 800 | 1100 | 1500 | BA-G6, BA-K4 | statement primed (Amend 1); no size change |
| BA-S2a | BA/Step1Trivial | prover-hard | `BATrivialLmax` (‖G‖ ≤ 1/η, `\|𝓛^{(k)}\| ≤ ‖G‖^k W^{-(k-1)d}`, `W^{-d} ≤ (g²+1) Bctl`; model merged `s1_loop_det`, `Induction/Step1Setup.lean:653`) | 500 | 700 | 1000 | merged flow (T2013), BA-D1 | NEW (split from S2) |
| BA-S2b | BA/Step1Boot | prover-hard | `BABootstrap` (band `step1TargetV3_holds`, `Induction/Step1.lean:525`, with the carrier; needs `BAGbEXP` in event form, T2205e) | 800 | 1100 | 1600 | BA-S1, BA-G6, BA-S2a | S2 minus the trivial bound |
| BA-S3 | BA/Step1 | prover (port) | `BAStep1` family: 3.1, 3.3, 4.1-4.3, 5.1, 5.3 (`BAzSrc`, `BAFamZ_closed`, tail congruence, `BAFlowMember_holds`, `BALmaxFromLK_holds`, `BAStep1_of_parts`; ≈ 800 probe lines) | 700 | 900 | 1300 | BA-S1, S2a, S2b, D8 | statement changed (family); was 700/1000/1500 |
| BA-V2a | BA/MainIndR | prover-hard | `BAMainIndR` for the four regimes (`BA_mainIndR_of_steps`), family forms of the step pins (transfer), initial step for every member (`H_0 = g'Ψ`, `G_0 = M`: new content) (6.1-6.4: ≈ 510 probe lines) | 800 | 1100 | 1600 | BA-S3, T8, U3, U6, V1, K4, K5 | NEW (split from V2) |
| BA-V2b | BA/MainIndGlue | prover (port) | `BA_mainInd_of_regimes` through (A): probe 6.5-6.7 (≈ 680 lines compiled): `BAMainIndR_pat`, `BAMainIndR_of_cover`, the `*_fwd`/`*_cov` transports of the 11 predicates, `BAextend`, `BAFlow_comp`, `BAWinBulk_comp`, `BAFamZ_comp`; `BAExactLaw` from T2206 | 500 | 700 | 1000 | BA-V2a, T2206 (ST-A, merged) | NEW (split from V2); V2 was 1000/1500/2200; lowered: the proofs exist |
| BA-U3, BA-U6, BA-V1 | as in P.9 | as in P.9 | now prove the regime pins `BAStep3R/4R`, `BAStep5R`, `BAStep6R` | - | - | - | - | statement shape only (P.4) |
| BA-V3, BA-M1 | as in P.9 | as in P.9 | take `BAMainInd` as an opaque hypothesis; produce its window premise by `BAWinBulk_of_dom` (D8) on the tail `sz.comp (· + n₀)` (T2205d) | - | - | - | + BA-D8 | dependency added |

## P.4 Superseded rows, consumers of (A), consumers of the new pins
- **No row is superseded.**  The ST cancellations (§68 (9): S3-27, S5-29, S6-13) removed *general-range* assemblies `STStep3/4/5/6` that had been pinned.  T2161 has no `BAStep3`..`BAStep6` pin (script: `git show 82e72b3:RBM3D/Probe/T2161Pins.lean | grep -c "BAStep3\|BAStep4\|BAStep5\|BAStep6\|STStep[3-6]"` prints 0; its Steps 3-6 are rows U1-U6, V1 feeding V2).  BA-U3 (`Step34Pins` consumers), U6 (`BAStep5I-IV`), V1 (Step 6 consumers) therefore keep their rows; their targets become the regime pins `BAStep3R/4R/5R/6R` of the probe (6.2), which V2a consumes.
- **Consumers of (A)**: BA-V2b only (a port of the compiled probe 6.5-6.7).  (A) is no longer an open ticket: T2206 (ST-A) is merged (`main` 8810a23, after this branch's base `cef761a`; read with `git show main:RBM3D/Induction/SizesComp.lean`).
- **Consumers of the family pins**: `BAStep1` ← BA-V2a; `BAMainInd` ← BA-M1 (`BAGlueLoc`), BA-V3 (`UNMLOutBA`), both uniform over every `z` with `BAFlow` and every `t ≤ t₀` through `BAFamZ_main` (the main flow is a member).

## P.5 The interface BA needs from route (A) (target 5) — compared with what T2206 provides
The one statement BA needs from (A) is `BAExactLaw d` (probe 6.7): the BA law `seqP (sz.withLam 0)` is carried exactly (every set, every integrand) onto the BA law of the composed sizes by the reindexing of samples along a strictly increasing `φ`.  Everything else is compiled in the probe: `BAMainIndR_of_cover` (hypothesis `BAExactLaw`), `BAMainIndR_pat`, `BA_mainInd_of_regimes`.  T2206 proves the statement (`BAExactLaw_of_T2206`, compiled in scratch against `main` with the definitions copied from the probe checked identical, b.3).  The probe's older copies (`LawComp_seqP`, `StochDomAt_of_PrecL_comp`, `StochDomAt_of_cover`, `szComp`, `szReindex`; 6.5-6.6) show feasibility at the old base; `szComp`, `szReindex` are T2206's `Sizes.comp`, `Sizes.reindex` by `rfl`.  T2206 statements (by script):
```text
$ python3 s_ifc.py | cut -c1-260
T2206 (ST-A) `RBM3D/Induction/SizesComp.lean`, last commit on main touching it: 8810a23
  :55 def comp (φ : ℕ → ℕ) : Sizes d where L := fun j => sz.L (φ j) W := fun j => sz.W (φ j) lam := fun j => sz.lam (φ j) three_le_L := fun j => sz.three_le_L (φ j) W_pos := fun j => sz.W_pos (φ j)
  :222 def reindex (φ : ℕ → ℕ) (ω : SeqΩ sz) : SeqΩ (sz.comp φ) := fun p => ω ⟨φ p.1, p.2⟩
  :239 theorem seqP_withLam_reindex_preimage (φ : ℕ → ℕ) (g : ℕ → ℝ) (hφ : Function.Injective φ) (s : Set (SeqΩ ((sz.comp φ).withLam fun j => g (φ j)))) : seqP (sz.withLam g) (reindex sz φ ⁻¹' s) = seqP ((sz.comp φ).withLam fun j => g (φ j)) s
  :245 theorem measurePreserving_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ) : MeasurePreserving (reindex sz φ) (seqP sz) (seqP (sz.comp φ))
  :93 theorem comp_admissible (φ : ℕ → ℕ) (𝔠 𝔡 : ℝ) (hφ : Tendsto φ atTop atTop) (h : sz.Admissible 𝔠 𝔡) : (sz.comp φ).Admissible 𝔠 𝔡
  :104 theorem STConStInd_comp (φ : ℕ → ℕ) (𝔠d : ℝ) (s t : ℕ → ℝ) (hφ : Tendsto φ atTop atTop) (h : STConStInd sz 𝔠d s t) : STConStInd (sz.comp φ) 𝔠d (fun j => s (φ j)) (fun j => t (φ j))
  :353 theorem map_iff {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] (μ : Measure Ω₀) (ν : Measure Ω₁) (f : Ω₀ → Ω₁) (hf : ∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s) (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ) : RBM.StochDomAt ν siz
  :389 theorem iff_cover {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) {U : ℕ → Type v} (ξ ζ : ∀ l, U l → Ω₀ → ℝ) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) : RBM.S
  :536 theorem stochDomAt_iff_comp_cover (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ) (ν : ∀ k, Measure (SeqΩ (sz.comp (φ k)))) (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (hlaw : ∀ k (s : Set (SeqΩ (sz.comp
BA side, probe (compiled; port into BA-V2b with `Sizes.comp`, `Sizes.reindex` in place of `szComp`, `szReindex`):
  :2804 def BAExactLaw (d : ℕ) : Prop := ∀ (sz : Sizes d) (φ : ℕ → ℕ), StrictMono φ → (∀ B : Set (szComp sz φ).SeqΩ, Sizes.seqP (sz.withLam 0) (szReindex sz φ ⁻¹' B) = Sizes.seqP ((szComp sz φ).withLam 0) B) ∧ (∀ g : (szComp sz φ).SeqΩ → ℂ, ∫ ω, g (szReindex s
  :2679 theorem BAFlow_comp {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} {φ : ℕ → ℕ} (hφ : StrictMono φ) (h : BAFlow sz κ ε 𝔠 𝔡 z) : BAFlow (szComp sz φ) κ ε 𝔠 𝔡 (fun n => z (φ n))
  :2671 theorem BAWinBulk_comp {sz : Sizes d} {z : ℕ → ℂ} {c₁ κ : ℝ} (φ : ℕ → ℕ) (h : BAWinBulk sz z c₁ κ) : BAWinBulk (szComp sz φ) (fun n => z (φ n)) c₁ κ
  :2675 theorem BAFamZ_comp {sz : Sizes d} {z : ℕ → ℂ} {c₁ : ℝ} {u : ℕ → ℝ} {z' : ℕ → ℂ} (φ : ℕ → ℕ) (h : BAFamZ sz z c₁ u z') : BAFamZ (szComp sz φ) (fun n => z (φ n)) c₁ (fun n => u (φ n)) (fun n => z' (φ n))
```
`BAExactLaw_of_T2206` is `⟨fun B => seqP_withLam_reindex_preimage sz φ 0 hφ.injective B, fun g => integral_reindex (sz.withLam 0) φ hφ.injective g⟩`; `fun j => (0 : ℕ → ℝ) (φ j)` is `0` by `rfl`.  `PrecL sz μ = StochDomAt μ sz.size` (probe 1.2).  The cover lemma `StochDomAt_of_cover_ev`, the exact-law transports `*_fwd`, `*_cov` and the extension of members `BAextend` are compiled in the probe (6.7).

## P.6 "Two data, one model" (target 8; supervisor 1651 O1, §66 (5))
Each row: the data a pin quantifies; what its hypotheses observe; a datum not observed, with two data agreeing on the observed region and the conclusions compared.  Evidence: compiled theorem/example (probe name) or script output (b.4, or section (a)).
| item | data quantified | observed | unobserved datum: two data, conclusions | result |
|---|---|---|---|---|
| `BAFlow`, `baFMz sz z` | `z_n`; `(t₀,E,g₀)` of `z` | `BAdom` (`Im m(z,g) ≥ κ`, `N^{-1+ε} ≤ Im z ≤ 1`), `Admissible` | `Re z`, `Im z` beyond `(t₀,E)`: `z`, `z̃` with equal `(t₀,E)` have the same carrier (`baFMz_eqAt`, `rfl`-level) hence the same conclusions; `BAm_real_eq_of_self` shows `z̃ = z` | no second datum |
| `BAWinBulk sz z c₁ κ` | `c₁`, `κ` | `Im m(E_n,g') ≥ κ` for `g' ∈ [√(1-c₁) g₀, g₀]` | `Im m(E_n,g')` below the window: `L=16`, `E=3.2`, `Im m = 0.2380` at `g'=0.9`, `0` at `g' ≤ 0.3` ((a) (iii)).  Same window, different values below: the pins agree, ConArg is used from `max(s,1-c₁)` only (`BAzSrc_spec`, `BAFamZ_closed`) and `(lRB1)` below `1-c₁` uses the member's own flow | independent |
| `BAFamZ` (A) | member `z'` | `E(z')`, horizon `τ ∈ [min(t₀,max(u,1-c₁)),t₀]` | `z'` beyond `(τ,E)`: as `BAFlow`.  `c₁ < c₁'` with the same window premise: the families are nested (`max(u,1-c₁)` decreases), hypotheses and conclusions both range over the larger one; the pin at `c₁'` is not implied by that at `c₁`, both are pinned (`∀ c₁`) | consistent |
| `BAFamCone` (B) | `lam'` | `lam'/g₀ ∈ [√max(u,1-c₁), 1]` | whether a spectral parameter with that coupling exists: horizon `t₀(lam'/g₀)²` is below the (A) floor at the cone bottom; (A) ⊂ (B) (`BAFamZ_subCone`; the cone bottom has horizon `t₀ max(u,1-c₁)`, below the (A) floor when `t₀ < 1`); the consumers need only the main flow; (A) is closed on its own (`BAFamZ_closed`) | (A) suffices |
| `BAmWindow`, `BAWinBulk_of_dom` | `c₁`, `C` before `L,g,E,m`; `c₁` before `ε,sz,z` | `BAReal d L g κ E m`, `g ≤ Λ`; `lam n ∈ (0,Λ]`, `BAdom κ` | `L ≥ 3`, `E`: the proof uses only `\|λ_i\| ≤ 2d` (`card_adj`) and `Im m ≤ 1`; numerics `L ∈ {4,6,16}`, 10 bulk-edge rows (b.4): `Im m ≥ κ/2` and `Lip ≤ C` all hold | uniform |
| `BAzztE_inv` | `(L,g,τ,E,m₀)` | all | none: `z'` is determined (`BAm_real_eq_of_self`); `τ = 1` excluded (`Im z' = 0`) | - |
| `BAgapReal` | `(L,g,E,m)` | `BASelf` (so `Im m > 0`) | `Im m → 0⁺`: bound `2(Im m)² → 0`; `gap.out`: `Im m ∝ η` at the support edge, `Im m(E+i0) = 0` is outside `BASelf` | - |
| `BAStep1`, `BAMainInd(R)`, steps in member style | `c₁`; `lam n` for all `n`; `z` | `BAFlow` (eventual), `BAWinBulk`, hypotheses at `s` for every member of `Fam(s)`, `(con_st_ind)` | `lam n ≤ 0` at finitely many `n`: `BAFlow` does not see it, conclusions are eventual, so two sequences differing at finitely many `n` give the same conclusions; the premise `∀ n, 0 < lam n` serves the closure proofs (T2205d); consumers pass to the tail `sz.comp (· + n₀)` (`comp_admissible`) | premise convenient, harmless |
| `BAConArg'` | `g_s = g₀√(s/t)`, `E` | `κ ≤ Im m(E,g_s)` (added premise) | source spectral parameter: as `BAFlow`.  Supervisor 1806 §1.4 data (`E=3.2`, `L=16`, `g_s ≤ 0.3`: `Im m = 0`): the premise fails, the pin is silent; with it `η_s ≥ (1-s)κ`.  T2197 `inst` data `(1/16,1/2)`: premise true (0.9995, (a) (4a)) but outside the window | premise necessary |
| `BATrivialLmax` | `c₁`; `u ≤ 1-c₁` | `BAWinBulk` | `m(E,g')` below the window: not used, `η_u = (1-u) Im m(E,g₀') ≥ c₁κ` for the member's own coupling `g₀'` in the window | independent |
| `BABootstrap` | ConArg outputs for `u ∈ [s₁,t]` | hypothesis | `BAGbEXP` in event form (T2205e) | risk, not a defect of the shape |
| `BAFlowMember` | `(κ',ε')` before `𝔠,sz,z` | `(κ,ε,𝔡)` | the sequence: constants `c_κ κ`, `ε/2` (`BAFlowMember_holds`) | uniform |
| `BAMainIndR_of_cover`, `BA_mainInd_of_regimes` | pattern class `(a,b)` of `n`; `φ k` | `BAinS`/`BAinT` pointwise (`s n`, `t n` against the three cuts) | the other sizes: the pin of a class is applied along its subsequence only (`BAFlow_comp`, `BAWinBulk_comp`, `BAFamZ_comp`); two sequences with the same class along `φ k` but different elsewhere give the same conclusion along `φ k`; finite classes are covered eventually (`StochDomAt_of_cover_ev`); members along `φ k` extend by the main flow (`BAFamZ_extend`); `lam` is not seen by the BA law (`BAExactLaw`) | consistent |
| `LawComp` | `φ`, `sz` | `StrictMono φ` | `lam` (the BA law does not see it): `(sz.comp φ).withLam 0 = (sz.withLam 0).comp φ` by `rfl` (`LawComp_ba`) | - |

Extreme inputs (every one compiled or scripted):
| input | pin tried | result and evidence |
|---|---|---|
| `g'` at the window bottom | `BAmWindow`, `BAFamZ` bottom member | `BAmWindow_holds`: `Im m(E,g') ≥ κ/2`, `‖Δm‖ ≤ C(g-g')`; b.4: `min Im m/κ = 0.5000` at `c₁*`; bottom member: `BAzSrc_spec` puts its ConArg source in the window |
| `u = 1 - c₁` (source time = target time) | `BAFamZ_closed` | example `s = u = 2/3`, `c₁ = 1/3` at `sz0` (7.4); `BAlamS = g₀` (identity source) |
| `t₀ < 1 - c₁` | `BAFamZ` | `BAFamZ_main_only`: the family is the main flow only; one-point data `t₀ = 0.218` ((a) `chk_inst.py`); Step 1 deterministic (`BATrivialLmax`) |
| `c₁ = 1/2` | window, closure | `sz0_win_half` (window at `c₁ = 1/2`, `Im m ≥ 3/5`); example `BAFamZ_closed` at `c₁ = 1/2`, `s ≡ 1/2` (7.4); in general `c₁ = 1/2` is admissible in 4 of 10 bulk-edge rows (b.4), so the window premise stays a hypothesis of the pins |
| `E` at the bulk edge at `g₀` | `BAmWindow` | `κ = Im m(E,g₀)` by construction, down to `κ = 0.0559` (b.4): window and Lipschitz bound hold |
| `s = 0` | `BAStep1`, `BAConArg'` | `inst_BAStep1` at `(s,t) = (0, 1/16)` (7.1); ConArg is taken from `s₀ = 1-c₁ ≥ 1/2 = ε₁`; `BAConArg'` excludes `s < ε₁` |

## P.7 §29 checklist (§45 O2) for the new pins
(1) `0 ≤ s < t ≤ t₀ < 1`: in every pin; `t₀ < 1` is `BAflow_T0_bounds`.  (2) gate, `Bctl`, `STWB`, `ellT` at the model coupling `g = sz.lam n` for every member: member couplings lie in `[√(1-c₁) g₀, g₀] ⊆ [√(κ/(2(κ+1))) g, g]`, constants in `κ` only ((a) row 7: P 4.67 ≥ 3.22); `BAFlowMember_holds` gives `κ' = c_κ κ`.  (3) no `L`-`W` relation beyond `Admissible`.  (4) `∀ n` against `∀ᶠ n`: `BAdom`, `BAWinBulk`, `0 < lam n` are `∀ n`; conclusions are `PrecL` (eventual); `c₁` is quantified before the sequence (F-f).  (5) `Prec`-type over `seqP (sz.withLam 0)` everywhere (L3).  (6) `0 < κ, ε, 𝔡, c₁` and `BAFlow` are premises.  (7) consumers `UNMLOutBA`, `BAGlueLoc`: see P.4.

## P.8 Ports and merged facts (file:line)
- T2161 probe at 82e72b3: `:744-811` (flow, loops; probe 46-114, verbatim), `:878-961` (carrier predicates, L1/L3; probe 184-260), `:965-983` (`bandFM`, `baFM`), `:985-1008` (band bridges, L4; probe `bandFM_*`), `:1023-1043` (`BAflow*`, `BAFlow`, `baFMz`), `:1079-1154` (`BAvecEntry`, `BAGbEXP*`, `BAlamS`, `BAConArgLoop/Vec`), `:1160` (`BAConArg` → `BAConArg'`, L5), `:1170`, `:1071` (per-flow pins, replaced), `:1896-1928`, `:2095-2199` (instance data, re-proved from `BASelf_unique`).  T2206 (`main` 8810a23) `Induction/SizesComp.lean`: `seqP_withLam_reindex_preimage :239`, `integral_reindex :253` used by `BAExactLaw_of_T2206`; Mathlib `Nat.nth` (`Mathlib/Data/Nat/Nth.lean`) for the subsequences.
- T2173 probe at a543154: `:1945-2010` (`FlowFM`, `GM`, `PrecL`, `STLKgL`, `STLmaxgL`, `STDecaygL`, `STLocalEntrygL`, `STExp2gL`).  T2191 probe at 96c6b4c: `:340-372` (`ST_mainInd_of_steps`: proof shape of `BA_mainIndR_of_steps`), `:291` (`STLK_of_STLKU_at`), `STExp2U`, `STStep6R`.
- merged, worktree base `cef761a`: `Induction/Step5Kit.lean:101` (`st5_conStInd_mono` → `BAconStInd_mono`, copied: outside the allowed imports), `Gauss/FineModel.lean:184` (`seqP_map_slice`: pattern of `LawComp_seqP`), `BA/MFixedPoint.lean:614` (private `MFixedPoint_inv_spectral` → `T2205_inv_spectral`), models only: `Induction/Step1Setup.lean:653` (`s1_loop_det`), `:693` (`s1_h55`), `Induction/Step1.lean:525` (`step1TargetV3_holds`).  RBM1D/RBM2D: no text ported (one docstring names RBM2D `s1_h55`).
- merged facts the deterministic proofs use (script `s_used.py`): gap: `BAMB_trace_eq_sum :655`, `BAspec :371`, `BAcard_Zd :143`, `MFixedPoint_inv_spectral :614`, `PsiB_isHermitian` (`Gauss/BlockAnderson.lean:55`), `Mres` (`Loop/GLoopFlow.lean:81`); `BAzztE_inv`: `BASelf_unique :715`, `BAm_spec :441`, `BAt0 :279`, `BAflowE :280`, `ztOf` (`Loop/GLoopFlow.lean:55`); window: `BAm_real_eq_of_self :824`, `card_adj` (`Defs/Neighbours.lean:168`), `Adj` (`Defs/Lattice.lean:108`); family: `BAdom_real :479`, `BAg0_le :493`, `BAzztE_data :297`, `BAm_self :809`.  `BAward_avg :389` is not used (it needs `0 ≤ Im z`; the imaginary part of `(self_m)` gives `⟨|w|^{-2}⟩ = 1` directly).

## P.9 Vocabulary lines that differ from the T2161/T2173 probe texts (script `python3 vocabdiff.py list`; classes L1-L5, `struct` = section/variable lines; the 246 identical lines are not listed)
```text
$ python3 vocabdiff.py list | sed -n "14,\$p"   # probe line, class, [source line <- probe line]
  236 L1 T2161:936 <- PrecL sz μ (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
  247 L1 T2161:947 <- def STLWassmExpgL (t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
  248 L1 T2161:948 <- PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
  263 struct end GenericL
  314 struct section MainInd
  319 L2 def STMainIndG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  320 L2 (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  321 L2 (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  323 L2 ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
  324 L2 ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
  325 L2 ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T0 sz z n) → (∀ n, s n < t n) →
  326 L2 (∀ n, t n ≤ T0 sz z n) →
  327 L2 (STLKgL (mk sz z) (law sz) s ∧ STDecaygL (mk sz z) (law sz) s ∧ STDecayStronggL (mk sz z) (law sz) s ∧
  328 L2 STLocalMaxgL (mk sz z) (law sz) s ∧ STExp2gL (mk sz z) (law sz) s) →
  329 L2 STConStInd sz 𝔠d s t →
  330 L2 STLKgL (mk sz z) (law sz) t ∧ STLmaxgL (mk sz z) (law sz) t ∧ STDecaygL (mk sz z) (law sz) t ∧
  331 L2 STExp2gL (mk sz z) (law sz) t ∧ STLocalEntrygL (mk sz z) (law sz) t ∧
  332 L2 STDecayStronggL (mk sz z) (law sz) t
  335 L4 theorem STMainInd_iff (d : ℕ) :
  336 L4 STMainInd d ↔ STMainIndG d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
  337 L4 (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl
  339 struct end MainInd
  341 struct section Step1
  350 L3 T2161:1086 <- STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ∧
  351 L3 T2161:1087 <- PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
  359 L3 T2161:1095 <- PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
  361 L3 T2161:1097 <- PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
  365 L3 T2161:1101 <- PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
  398 L3 T2161:1134 <- PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
  410 L3 T2161:1146 <- (∃ C₀ : ℝ, 0 < C₀ ∧ HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω |
  414 L3 T2161:1150 <- ∃ C₁ : ℝ, 0 < C₁ ∧ HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω |
  423 L5 def BAConArg' (d : ℕ) : Prop :=
  424 L5 ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
  425 L5 ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  426 L5 ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  427 L5 (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) →
  428 L5 STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s →
  429 L5 (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t
  432 L4 theorem STStep1_iff (d : ℕ) :
  433 L4 STStep1 d ↔ ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
  434 L4 ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
  435 L4 ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
  436 L4 ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
  437 L4 (∀ n, t n ≤ lemT (z n)) →
  438 L4 STKboundgL (bandFM sz (STflowE z)) (Sizes.seqP sz) → STLKgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s →
  439 L4 STLocalMaxgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s → STConStInd sz 𝔠d s t →
  440 L4 STStep1LoopgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t ∧
  441 L4 STStep1WeakgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t := Iff.rfl
  443 struct end Step1
  450 L4 theorem bandFM_STLK {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) : STLK sz E τ ↔ STLKgL (bandFM sz E) (Sizes.seqP sz) τ := Iff.r
  451 L4 theorem bandFM_STLmax {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
  452 L4 STLmax sz E τ ↔ STLmaxgL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
  453 L4 theorem bandFM_STDecay {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
  454 L4 STDecay sz E τ ↔ STDecaygL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
  455 L4 theorem bandFM_STDecayStrong {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
  456 L4 STDecayStrong sz E τ ↔ STDecayStronggL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
  457 L4 theorem bandFM_STLocalMax {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
  458 L4 STLocalMax sz E τ ↔ STLocalMaxgL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
  459 L4 theorem bandFM_STLocalEntry {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
  460 L4 STLocalEntry sz E τ ↔ STLocalEntrygL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
  461 L4 theorem bandFM_STExp2 {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
  462 L4 STExp2 sz E τ ↔ STExp2gL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
  463 L4 theorem bandFM_STInitialGT2 {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) :
  464 L4 STInitialGT2 sz E t ε₀ Ψ ↔ STInitialGT2gL (bandFM sz E) (Sizes.seqP sz) t ε₀ Ψ := Iff.rfl
  465 L4 theorem bandFM_STKbound {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) :
  466 L4 STKbound sz E ↔ STKboundgL (bandFM sz E) (Sizes.seqP sz) := Iff.rfl
  467 L4 theorem bandFM_STStep1Loop {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) :
  468 L4 STStep1Loop sz E s t ↔ STStep1LoopgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
  469 L4 theorem bandFM_STStep1Weak {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) :
  470 L4 STStep1Weak sz E s t ↔ STStep1WeakgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
  471 L4 theorem bandFM_STLWassmExp {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) :
  472 L4 STLWassmExp sz E t D ℓ ↔ STLWassmExpgL (bandFM sz E) (Sizes.seqP sz) t D ℓ := Iff.rfl
  474 L4 theorem bandFM_STEEk {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool)
  475 L4 (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
  476 L4 STEEk sz n (E n) u k σ a ω = STEEg (bandFM sz E) n u k σ a ω := rfl
```
