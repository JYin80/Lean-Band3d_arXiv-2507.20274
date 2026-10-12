Auditor model: claude-opus-5-5
# T2458 audit (round 1): U6, `Chain/Step5Gen.lean`. Mon Oct 12 15:03:20 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2458-audit1`, detached at t/T2458 = 48a7583. Scratch: `<scratchpad>/T2458/`.
Binding (CONTROL H248 (3)): the BA example at check line 462 (`∀ lam0, T2458_STTailtoTailgL' 3 (baFM sz lam0 ·)`) is a shape and is not a target. It was not audited as one.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Chain.Step5Gen 2>&1 | grep -E "error|warning|Build" | grep -c Step5Gen ; echo exit
0          exit 0   (the only warnings are in merged files: Defs/Tail, Path/Markov, ...)
$ lake env lean Ax.lean   # import RBM3D.Chain.Step5Gen; #print axioms RBM.BA.<each of the 26 `theorem`s>
  26 [propext, Classical.choice, Quot.sound]
$ lake build RBM3D && lake env lean Assert.lean   # import RBM3D; import RBM3D.Chain.Step5Gen; #assert_rbm_axioms
Build completed successfully (4281 jobs).
axiom audit: 13315 theorems, 4196 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -nE "STNewKLKL|STTailtoTail|gL'|_band|Step5Gen" assert.out | wc -l     # unproved-premise lists
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Chain/Step5Gen.lean | wc -l
0
$ git diff --name-only main...HEAD
RBM3D/Chain/Step5Gen.lean
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,NewKLKGen}.lean RBM3D/BA | wc -l
0
$ grep -n "^import" RBM3D/Chain/Step5Gen.lean ; grep -rn "Chain.Step5Gen" RBM3D RBM3D.lean | wc -l ; wc -l < Step5Gen.lean
6:import RBM3D.Chain.GridDuhamelGen   7:import RBM3D.Induction.Step5Pins      0 (cone empty)      666 (stop line 2000)
```
`RBM3D.lean` is not touched on the branch. The hub adds the import at merge (§3 (A) step 4).

## 2. Statements against the pins (targets 2-10), check file, shapes, G1
The scratch file `AuditCheck.lean` contains: `import RBM3D.Chain.Step5Gen` plus the check's imports; the check's Part 2, lines 174-463, copied verbatim; then 43 auditor `example`s:
- (a) `T2458_X … ↔ X …` by `Iff.rfl` for all 25 pins (targets 2, 4-10, including `T2458_STIngR5gL` with its inline premises `T2458_LmaxU_inline`, `T2458_LKU_inline`), and target 3 by `rfl` against the marked subterms (`STLK2g = ‖C.L - C.K‖`, `STELKLKg = W^d Σ_x Σ_y (L-K)(x,a₁) C.S (L-K)(a₀,y)`);
- (b) each binding shape of the check (lines 412-444) proved by the branch's bridge or band theorem;
- (c) the band theorems at the proved band pins;
- (d) G1: `example : <statement> := <name>` for `st5_reg5I_mid` and for `inst_etermsMid`, `inst_duhamelI`, `inst_iniTermI`, `inst_wardII`, `inst_pfStep5`.
```
$ grep -c "^example" AuditCheck.lean ; sed -n '/Auditor: pins/,$p' AuditCheck.lean | grep -c "^example"
59   43
$ lake env lean AuditCheck.lean ; echo exit=$? ; grep -c error audit.out
exit=0   0
$ lake env lean docs/tickets/checks/T2458-check.lean (on the branch worktree); echo exit ; grep -c error
exit=0   0
```
Selected lines of (b)-(c) as compiled:
```
example : ∀ d : ℕ, STNewKLKL d → T2458_STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) := stNewKLKLgL'_band
example : ∀ d : ℕ, STTailtoTail d → T2458_STTailtoTailgL' d (fun sz E => bandFM sz E) := stTailtoTailgL'_band
example : ∀ d : ℕ, STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) := fun d => stNewKLKLgL'_band d (stNewKLKL_holds d)
example : ∀ d : ℕ, STTailtoTailgL' d (fun sz E => bandFM sz E) := fun d => stTailtoTailgL'_band d (stTailtoTail_holds d)
example : ∀ d R Concl, STIngR5 d R Concl ↔ T2458_STIngR5gL d R (seqP) (STFlow) (bandFM ∘ STflowE) (lemT) (Concl ∘ STflowE)
  := fun d R Concl => STIngR5_iff_gL d R Concl
```
The prover's three textual differences are confirmed definitional by (a): `STEtermsMidConclgL` uses `STELKLKg`, `STPfConclgL` uses `STLK2g`, and `STIngR5gL` writes the Steps 3-4 premises inline. The prover's U-C5 change table (report (b) 4) is complete.

Mathematics against the ticket (read from the signatures in `Step5Gen.lean`):
- Target 2. Loss exponent `0` in `STGdecayWgL … 0`. Index subtype `lam² ≤ 1 - t n`. `Bctl²·e^{-|a₁-a₂|^{1/2}} + W^{-D}`. Band text `:69`, `:97`.
- Target 4. Exponents `A^{-1/3}`, `A^{-1/2}`, `A^{-1/2}` (EtermsMid); `A^{-1/5}` (IniTerm, Duhamel); `A^{-1}(N·η)^{-1}` (WardII); `C.eta n` for `etaT`. The kernel is `Step2Gen_UN C n σ (s n) u` at the time `s n`, as U-C4 requires.
- Target 6. Parameter order `3 ≤ d → ∀ κ 𝔡 > 0 → ∃ Ck δ₀ > 0 → ∀ sz n E u D …`. The band window `|E| ≤ 2-κ` is replaced by `κ ≤ Im m`. The band theorem applies the band pin at the margin `κ²`, so the constants still depend on `(κ, 𝔡)` only. The private helper `Step5Gen_abs_le_of_im` proves `κ ≤ Im mE E → |E| ≤ 2-κ²`.
- Target 7. `∃ Cc` comes after `κ` only. Hypotheses: `0 < lam`, `κ ≤ Im m`, `0 ≤ s ≤ t < 1`, `lam² ≤ 1-t`. The bound is `Cc·T_{t,D} + ((1-s)/(1-t))²W^{-D}`. The kernel is `Step2Gen_UN`. The band theorem reaches `RBM.UN` only through `Step2Kern_UN_band`, and `‖mE E‖ = 1` through `norm_mE`.
- Target 8. Binder order `(d R law Flow mk T0 Concl)`. `Concl : ∀ sz z, (ℕ→ℝ)→(ℕ→ℝ)→Prop`. Premises in the band order (`3 ≤ d`, `κ ε 𝔡 > 0`, `Cd > 0`, `∃ 𝔠d ∈ (0,1/100]`, Flow, `0 ≤ s < t ≤ T0`, R, the Steps 1-2 carrier pins, `STConStInd`, the two inline Steps 3-4 premises). The D2 default of `T2457_IngRgL` is followed.
- Target 11 is not written. The ticket allows this: T2457 is not merged (`docs/queue/T2457.state`: `state: held`; `Chain/Step34Gen.lean` is absent from `main`). The target moves to U4s3, as §266 accepts.

## 3. Hidden hypotheses, vacuity, cycles
- No `structure`, `class` or `instance` is declared. Every pin is a `def … : Prop`, and the carrier `FlowFM` is merged.
- The premises of the public theorems are the band pins `STNewKLKL d` and `STTailtoTail d`, and both are discharged by the merged `stNewKLKL_holds` and `stTailtoTail_holds` (§2 (c)). Every other theorem is a bridge with no premise. No registry line is needed: `assert.out` shows 0 unproved-premise entries for this file.
- There is no cycle. The imports are `GridDuhamelGen` and `Step5Pins` only (no `BA/*`, `CltGen`, U4/U5/V/X1 file), and nothing imports the new file.
- One rule-(E) item: the helper `Step5Gen_ingR5_iff_congr` is public. It carries the file stem, so it complies.

## 4. Compiled nonempty instances (section 10 of the file, `d = 3`; built in §1)
```
$ grep -n "^example" RBM3D/Chain/Step5Gen.lean | wc -l
27
```
- **Targets 2-5 (11 bridges).** Concrete data: `(sz0, STflowE z0, sInst=0, tInst=1/16)`, `szB` at `(7/8, 15/16)` and at `(15/16, 31/32)`, and `n = 0`, `u = 1/32` for the vocabulary.
- **Targets 9-10 and 15.** The pins `inst_etermsMid`, `_duhamelI`, `_iniTermI`, `_wardII`, `_pfStep5`, `_duhamelII`, `_iniTermII` are re-derived from the generic wrapped pin through its bridge. That generic pin, an unproved pin of U4s1-U4s3/U5, is the only hypothesis. The deterministic data are discharged inside the merged `inst_ing5_I`/`_II`/`_III`: flow `flow_zB`, regime `szB_reg5I`, `t ≤ lemT`, and `(con_st_ind)` by `conStInd_const`. The six per-regime bridges are at `d = 3`.
- **Target 8.** `inst_ing5_I STReg5I Concl ((STIngR5_iff_gL 3 STReg5I Concl).2 h) szB_reg5I`.
- **Target 6 (lines 622-640).** Data: `sz0`, `n = 0` (`lam = 1/64 ≤ 10 = 𝔡⁻¹`), `E = 0` (`Im m = 1 ≥ κ = 1/10`, proved in `Step5Gen_im_zero`), `u = 0`, `D = 1`. `H = 0` is Hermitian, and `‖STGMMg‖ = 0 ≤ δ₀` by `STGMM_zero`. The only hypothesis is `STNewKLKL 3`, a merged proved pin that cannot be imported here (cycle with U4s1). §2 (c) shows it closes with `stNewKLKL_holds`.
- **Target 7 (lines 645-660).** Data: `sz0`, `n = 0`, `E = 0`, `D = 2`, `s = 1/2`, `t = 3/4`, `lam² = 1/4096 ≤ 1/4`, `σ = (true, false)`, and the nonzero extremal tensor `A_b = T_{s,D}(|b₁-b₂|)`. The only hypothesis is `STTailtoTail 3`, handled as in target 6.
- **Degeneracy.** None: no `N = 0`, no empty index (`lam_n² ≤ 15/16` at `sz0`), no collapsed window, no `False` premise.

## 5. Acceptance greps (targets 12-14)
```
$ grep -nE "^(noncomputable )?(private )?(def|abbrev|structure|instance)" Step5Gen.lean | cut -d: -f1
51 62 68 74 85 102 115 130 139 151 164 169 178 191 214 226-230 234 236 239 241 246 250 252 353(docstring word) 607 609
$ grep -nE "Matrix\.of|Ring\.inverse|Step2Kern_Mss|cycProd" Step5Gen.lean | wc -l            # 12(a)
0
$ grep -nE "Ring\.inverse|…|RBM\.UN|\bUN d|Ugen|EKsgn|PropSpin|Theta d" Step5Gen.lean            # 12(b)
284 (docstring), 288 simp only [bandStep2_Ugen], 291 (docstring), 295 simp only [bandStep2_Ugen], 344 (proof of stTailtoTailgL'_band)
$ grep -c "Step2Gen_UN" ; grep -nE "(def|theorem|lemma|abbrev) [A-Za-z_']*Ugen" | wc -l           # 12(c), 12(d)
11   0
$ grep -nE "<target-13 pattern>" | line ranges
1-256 (all generic defs): 0 | 257-299 concl bridges: 7 | 300-348 band theorems: 11 | 349-476 pin bridges: 48 | 477+ instances: 61
$ grep -nE "Clt|fFar|cltB|cltX|ExpInv" Step5Gen.lean | wc -l                                       # 14
0
```
- Kernel rule: the bodies at lines 607 and 609 are `bandStep2Mat sz0 (fun _ => 0)` and `0`, so no definition carries a kernel or propagator.
- Spectral rule: no generic definition carries a target-13 item. All hits are on band bridges, band theorems or `d = 3` instances, which use the old names.

## 6. Paper deltas
- **T2458a** (prove report (d) 2). Targets 6-7 replace `|E| ≤ 2-κ` / `‖m‖ = 1` by `κ ≤ Im m`; the band ⇒ generic proof uses the margin `κ²`. This covers the only spectral-datum difference.
- **T2458b** ((d) 3). The kernel is `Step2Gen_UN C n` in place of the named propagator. This covers the kernel difference.
- No other Lean/paper difference was found. The inline Steps 3-4 premises are the band `STLmaxU`/`STLKU` text, and the band bridges are `Iff.rfl`.

## 7. Observations (no RETURN)
- O1, for U5/T2459. No hypothesis links `sz.lam n` (indices, regimes, `STAI`, `STprof`) with the carrier's `C.S n`. They agree at `bandFM`; at `baFM`, `S = 1`. The prover records this in (d) 4. It does not affect the band bridges.
- O2, for consumers. The four rows that read the kernel (`STDuhamelI/II`, `STIniTermI/II`) close only through `Step5Gen_ingR5_iff_congr` with `bandFM_STIniTermConcl`/`bandFM_STDuhamelConcl`, which are not `Iff.rfl`. The prover records this in (d) 5.
- O3. The prove report is 192 lines, within the ticket's 200-line limit.

## Verdict
| target | verdict |
|---|---|
| 1 (names reused) | PASS |
| 2 | PASS |
| 3 | PASS |
| 4 | PASS |
| 5 | PASS |
| 6 | PASS |
| 7 | PASS |
| 8 | PASS |
| 9 | PASS |
| 10 | PASS |
| 11 | not written; moved to U4s3 (permitted, T2457 unmerged) |
| 12-14 (greps) | PASS |
| 15 (G1, instances) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
