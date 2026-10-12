Auditor model: claude-opus-5-5
# T2428 audit (round 1) — Mon Oct 12 01:16:38 UTC 2026
Ticket `docs/tickets/T2428.md` + Amend 1 (`T2428-amend-1.md`, CONTROL H223; targets: 1–3, `BAuKerSemigroup`, 4 (a), clause (i) of 4 (b), the item-(iii) bridges, the six pins verbatim from the probe at `f6c3866`, `baTwistGridAssemble_holds`; clauses (ii)–(iv) are TL2a2–TL2a4; registry none). Branch `t/T2428` at `bed7d4f`; audit worktree `RBM3D-wt/T2428-audit1` (detached).

**Verdict: PASS** (every target of Amend 1). No dispatcher sign-off needed.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.TwistGrid RBM3D.BA.TwistGrid2 2>&1 | grep -E "error|warning: RBM3D/BA/TwistGrid|Built RBM3D.BA.TwistGrid|Build completed"; echo exit $?
✔ [4012/4013] Built RBM3D.BA.TwistGrid (4.7s)
✔ [4013/4013] Built RBM3D.BA.TwistGrid2 (3.5s)
Build completed successfully (4013 jobs).
exit 0
$ wc -l RBM3D/BA/TwistGrid.lean RBM3D/BA/TwistGrid2.lean        (stop line 2,000 per file)
     963 RBM3D/BA/TwistGrid.lean
     345 RBM3D/BA/TwistGrid2.lean
$ grep -hoE "^(theorem|lemma) \S+" both files  -> 20 public theorems; Ax.lean = import RBM3D.BA.TwistGrid2 + #print axioms of each
TwistGrid2_twAk_step TwistGrid2_twAk_duhamel BATwistDuhamel_holds baTwistGrid_decomp baTwistGrid_decomp_ae baTwistGridAssemble_holds twL2M_eq twL3M_eq twEGM_eq twB1M_eq twB2M_eq twDerM_eq twEEM_eq BAuKer_self BAuKer_comp BAuKerSemigroup_holds twTheta_eq_thetaKer twU_eq_uKer BATwistGen_holds BATwistHier_holds
$ lake env lean Ax.lean; (axiom lists, counted)
exit 0
  20 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/TwistGrid.lean RBM3D/BA/TwistGrid2.lean RBM3D/Probe/T2428Pins.lean | wc -l
0
$ grep -nE "STthetaOpg|STgDriftg|Step2Gen_ThetaN|Step2Gen_UN" RBM3D/BA/TwistGrid*.lean | wc -l
0
$ grep -nE "Step2Gen_thetaKer|Step2Gen_uKer" RBM3D/BA/TwistGrid*.lean   (C1/BAT-F1: only the two bridges, their instances, comments)
TwistGrid.lean:35, :202, :203 (doc comments); :211 twTheta_eq_thetaKer; :215 twU_eq_uKer; :954, :958 (their instances)
$ git diff --name-only main...t/T2428
RBM3D/BA/TwistGrid.lean
RBM3D/BA/TwistGrid2.lean
RBM3D/Probe/T2428Pins.lean
$ git diff main...t/T2428 -- RBM3D.lean RBM3D/Test/Axioms.lean | wc -l
0
$ lake env lean docs/tickets/checks/T2428-check.lean (in the audit worktree); echo exit $?; grep -c error
exit 0
0
```
All three files are sole writable files. The probe is "1a only, never merged". At merge the hub brings in only `TwistGrid.lean` and `TwistGrid2.lean`, plus the two import lines.

## 2. Pins verbatim from the probe at f6c3866 (Amend 1 item 2)
```
$ git show f6c3866:RBM3D/Probe/T2428Pins.lean > probe.lean
$ python3 verb.py probe.lean RBM3D/BA/TwistGrid.lean RBM3D/BA/TwistGrid2.lean   (every `def NAME` block of the probe vs the same block in the two files, exact text)
30 probe def blocks; 30 identical
```
These 30 blocks cover the vocabulary `twGM`…`twGenM`, `twAk`…`twRem`, `BATwistGen`, `BATwistHier`, `BAuKerSemigroup`, `BATwistDuhamel`, `BATwistGridMartAt`, `BATwistGridMart`, `BATwistGridRem`, `BATwistGridTail`, `BATwistGridWTail`, `BATwistGridAssemble`. The 1a-audit already reviewed the pins against the ticket, and the dispatcher accepted them in Amend 1.

## 3. Statement review, per target
**Target 1, vocabulary and bridges: PASS.**
- `twL2M`, `twL3M`, `twEGM`, `twB1M`, `twB2M`, `twDerM`, `twEEM` are TL0's `twL2'`, `twL3`, `twEG`, `twB1`, `twB2`, `twDer`, `twEE` at `H = sz.seqHflowBA lam0 n u ω`, with carrier `baFM`.
- All seven bridges `tw*M_eq` (TwistGrid.lean:131-138) are proved by `rfl` and compiled.
- `G_u(H) = Gres H (ztOf (BAmF …) (E n) u) true` follows the `LM` convention of `baStep2Mat`.
- `twGenM` is `genMatOf` (`Induction/LoopGenN.lean:556-561`) at `g = 0` with `loopL` replaced by `twL2M`. Both have the same `(1/2) Σ_c gvarF·∂²_y + ∂_u` shape.

**Target 2, T.8 `BATwistGen`: PASS.**
- Hypotheses: `0 < Im m`, `u < 1`, `H` Hermitian. They are for all `σ, a, c₁, c₂` and every `d`, as the ticket requires.
- Conclusion: `twGenM = W^d Σ_b L̃(b)·LM σ ![a,b] + twEGM`. This is (D.1) of TP:104-108, read as the generator (drift) part: `W^dΣ_b L̃_u(b) L^{(2)}_{(a,b)} + Ẽ^{G̊}`.
- `𝓛^{(2)}` is `Tr(G(σ0)E_aG(σ1)E_b)` (`TwistGrid_LM_two`, :764), with `a` first, which matches TP.
- No `3 ≤ L` and no `0 ≤ u` are needed. This is weaker than the ticket's setting and is proposed as delta T2428b.

**Target 3, T.9 (D.4) `BATwistHier`: PASS.**
- Hypotheses: `0 < κ`, `0 < lam0 n`, `BAReal`, `0 ≤ u < 1`, `H` Hermitian. The hypothesis `0 < lam0 n` is the `hg` of `baKsol_two` (`BA/KInduct.lean:88`: `(hκ : 0 < κ) (hg : 0 < g)`). It is deterministic and is discharged in the instance by `gI_pos`.
- Conclusion: `twGenM − deriv(v ↦ twK … v) u = twDriftM`, where `twDriftM = ((BATheta u σ0 σ1 * BAMss … σ0 σ1) *ᵥ (L̃−K̃))(a) + twB1M + twB2M + twEGM`.
- This is (D.4) with `Θ̃_u = Θ_u M^{(σ1σ2)}`, the one-slot summand (TP:113). The diagonal `2mm'(1−umm')⁻¹` does not occur.
- `∂_u K̃` is an honest `deriv`, computed through `BATheta_hasDerivAt` (`TwistGrid_hasDerivAt_twK`).

**`BAuKerSemigroup` / `BAuKer_self` / `BAuKer_comp`: PASS.**
- They state `Ũ_{v,v} = 1` and `Ũ_{v,w}Ũ_{u,v} = Ũ_{u,w}` under `BAReal` with `0 ≤ v, w < 1`.
- The Lean statements are a semigroup law that holds for every `u` (no condition on `u`). TP:115 writes `Ũ_{v,u} = (1−vM)(1−uM)⁻¹`, and the Lean statements agree with it.

**Item (iii) bridges `twTheta_eq_thetaKer`, `twU_eq_uKer`: PASS.**
- Their hypothesis is `(E n + m).im ≠ 0`.
- They are the symmetric forms of the merged `Step2Kern_thetaKer_BA` and `Step2Kern_uKer_BA`.

**4 (a) `BATwistDuhamel`: PASS.**
- Hypotheses: `BAFlow`, `0 ≤ s ≤ t ≤ BAflowT0`, `K n ≠ 0`, and `min j (τ ω) ≤ K n`. This is the same hypothesis set as the band twin `StoppedDuhamelN` (`Induction/GridDuhamelN.lean:293-305`, which also has `min j (τ ω) ≤ K n`).
- Conclusion: `A_{j∧τ} = Ũ_{u₀,u_{j∧τ}} *ᵥ A₀ + Σ_{i<j∧τ} Ũ_{u_{i+1},u_{j∧τ}} *ᵥ (P_i + ξ_{i+1})`, where `Ũ = twU = BAuKer … (σ 0) (σ 1)` acts on `a` only. This is the discrete (D.5).
- The proof uses `duhamel_telescope` together with `BAuKer_self` and `BAuKer_comp`. `T0 < 1` comes from `flowOK_T`.

**Clause (i) of 4 (b), `baTwistGrid_decomp` / `_ae`: PASS.**
- These are pathwise identities with the canonical `twMart` and `twRem`, which are the twins of `difRepMartN` and `difRepRemN`.
- The `_ae` form is the first conjunct of `BATwistGridRem`. The example at TwistGrid2:320-327 shows this by compiling.

**`baTwistGridAssemble_holds : BATwistGridAssemble`: PASS.**
- It proves that `BATwistGridRem d C₀ ∧ BATwistGridTail d ∧ BATwistGridWTail d → BATwistGridMartAt d C₀` for every `d` and every `C₀ ≥ 0`.
- `CK := max` of the three constants, `Mart := twMart`, `Rem := twRem`, and the `N^{CK}` monotonicity uses `sz.one_le_size`. This is the twin of `stGridMartAt_of_parts2`.
- The three part pins appear only as hypotheses of this implication. No merged statement assumes them, so the registry stays empty (Amend 1 item 4).

## 4. Hidden hypotheses, vacuity, cycles
- No new `structure` and no hypothesis carried in a field. The pins are `Prop`-valued defs whose hypotheses are all explicit binders.
- `BAReal` and `BAFlow` are merged definitions, consumed as such. `BAReal` is discharged in the instances from `BAflow_real` and `flow_sz0`.
- Dependencies are merged declarations only: `baKsol_two`, `BATheta_hasDerivAt`, `BATheta_resolvent`, `Step2Kern_*_BA`, `duhamel_telescope`, `baStep2Data`, `BAflow_real`. There is no cycle; nothing imports `TwistGrid*` except `TwistGrid2`.
- No external hypothesis is introduced, so no limit check is owed. The three part pins of 4 (b) belong to successor rows and are not assumed by any merged result.

## 5. Compiled nonempty instances (all compiled in the build above; `d = 3`, `sz0`, `L = 4`, `W = 32`, `n = 0`)
```
$ grep -n <applications of each endpoint theorem in the Inst sections>
TwistGrid.lean:907 twL2M_eq sz0 … (1/2) ω ![false,true] 0 0 ![1,0,0]   (+ :913-918 the other six bridges)
TwistGrid.lean:926 BATwistGen_holds 3 sz0 … 0 (BAmF_sz0_im_pos 0) (1/2) (by norm_num) _ (EMn2BA_seqHflowBA_herm …) ![false,true] 0 0 ![1,0,0]
TwistGrid.lean:934 BATwistHier_holds 3 sz0 … 0 (1/2) (by norm_num) gI_pos (BAflow_real (1/2) (1/10) (1/6) (1/10) sz0 zSeq flow_sz0 0) (1/2) …
TwistGrid.lean:940 BAuKer_self hrI …  :943 BAuKer_comp hrI …  :949 BAuKerSemigroup_holds 3 (sz0.L 0) gI (1/2) EI mI hrI false true (2/3) (1/4) (1/2) …
TwistGrid.lean:955 twTheta_eq_thetaKer sz0 … (BAmF_sz0_im_pos 0).ne' …   :959 twU_eq_uKer sz0 … (1/4) (1/2)
TwistGrid2.lean:302 BATwistDuhamel_holds 3 (1/2) (1/10) (1/10) … (1/6) sz0 zSeq flow_sz0 (s≡1/2) (t≡2/3) … (t0_sz0) (K≡4) … 0 ![false,true] 0 ![1,0,0] (τ≡3) 3 ω
TwistGrid2.lean:314 baTwistGrid_decomp sz0 … (s≡1/2) (t≡2/3) (K≡4) 0 ![false,true] 0 0 ![1,0,0] 3 ω   :317 baTwistGrid_decomp_ae …
TwistGrid2.lean:331 baTwistGridAssemble_holds 3 11 (by norm_num) hRem hTail hW  (and :335-343, applied at flow_sz0, K_n = ⌈N^CK⌉+1)
```
- The data are nondegenerate. The window is `1/2 < 2/3 ≤ BAflowT0` (`t0_sz0`). `K ≡ 4` and `τ ≡ 3`. `c₁ = 0 ≠ c₂ = (1,0,0)`. `σ = (false, true)`. `H` is the Hermitian flow matrix at an arbitrary sample.
- There is no `N = 0`, no empty index set and no `False` premise.
- Every deterministic hypothesis is discharged at the data. The only premises left in the instances are the three part pins `BATwistGridRem/Tail/WTail` of the successor rows TL2a2–TL2a4. These are other gates' unproved pins, which CLAUDE.md §4 step 2 allows.

## 6. Paper deltas
The prove report (d) proposes:
- **T2428a**: the grid/discrete form of (D.1)/(D.5), and Azuma in place of BDG.
- **T2428b**: every `d`, with weaker hypotheses for T.8.
- **T2428c**: the clause-(iv) weights `Ũ_{u_j,u_k}` versus `Ũ_{u_{i+1},u_{j∧τ}}`.

The coupling-0 law (`withLam 0`, `S^{(B)}(0) = I`) is existing D443 (`docs/paper-deltas.md:1402`). Every Lean/paper difference found in §3 is covered by these entries. The extra `0 < lam0 n` of T.9 is the paper's `g > 0`, so it is not a delta.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The last example of TwistGrid2 (:335-343) concludes `True`. The substantive assembled instance is the one at :330-331, which has conclusion `BATwistGridMartAt 3 11`. The `True` example only shows that the eventual hypothesis on `K` is dischargeable at `flow_sz0`.
- O2. `TwistGrid2_twAk_step` and `TwistGrid2_twAk_duhamel` are public but carry the file stem, which §3 (E) allows.
- O3. The probe `RBM3D/Probe/T2428Pins.lean` is in `git diff main...t/T2428` by design (it is a sole writable file, 1a only). The hub must not bring it in at merge.
