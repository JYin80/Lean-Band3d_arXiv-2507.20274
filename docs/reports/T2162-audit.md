Auditor model: claude-opus-5-5
# T2162 audit (UN-D1, design / report only) — Sun Oct  4 22:40:39 UTC 2026
Branch `t/T2162` at `73b451c` (merge-base `a21a819`, main `6e63fbc`); audit worktree `RBM3D-wt/T2162-audit1` (detached).
Scratch: `scratchpad/T2162/` (build.out, lean.out, word-diffs, clos.py).

## 1. Build, axioms, hygiene, writable files
```
$ git diff --name-only main...t/T2162
RBM3D/Probe/T2162Pins.lean
$ lake build RBM3D.Probe.T2162Pins ; tail -1
Build completed successfully (3328 jobs).
$ grep -nE "error|warning" build.out   (only upstream, merged file; none in the probe)
warning: RBM3D/Defs/Tail.lean:169:100 / :170:100 / :171:100: line exceeds 100 characters
$ lake env lean RBM3D/Probe/T2162Pins.lean; echo exit=$?      (ticket acceptance command)
exit=0     (output = #print axioms lines only)
$ grep "depends on axioms" lean.out | sed "s/.*axioms: //" | sort | uniq -c
 139 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Probe/T2162Pins.lean | wc -l
0
```
Sole writable files: probe (branch only), `T2162-prove.md` (296 lines), `T2162-portmap.md` (present). No frozen signature touched (new file, no root import). Report-only ticket: nothing merged into the library.

## 2. Statements against the paper and the ported sources (script word-diffs, whitespace-normalised)
```
## UNBUniv (probe:176) vs RBM2D Endpoints.lean:209 BUniv (c9a24cf)
[-BUniv-]{+UNBUniv+} {+d : ℕ, 3 ≤ d → ∀+} {+𝔡+} [-0 < 𝔠 →-] [-Sizes, Admissible-]{+Sizes d, sz.Admissible+}
[-ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport-]{+IsTestFun+} (+ carrier renames d.L→sz.L, seqXmat sz)
## UNBUniv vs T2001_BUniv (bd95cc9:RBM3D/Probe/T2001Endpoints.lean:230)
[-0 < 𝔠 → 0 < 𝔡 →-] [-SizeSeq, Admissible d-]{+Sizes d, sz.Admissible+} [-ContDiff … HasCompactSupport-]{+IsTestFun+}
[-(eigs (Hmat d …)) ∂(Pn d s n)-]{+(Sizes.seqXmat_isHermitian sz n ω).eigenvalues ∂(Sizes.seqP sz)+}
## UNL32 (probe:280) vs RBM2D Universality/Pins.lean:156 L32
[-L32-]{+UNL32+} [-Sizes,-]{+ℕ, 3 ≤ d → ∀ sz : Sizes d,+} [-ContDiff … HasCompactSupport-]{+IsTestFun+} (+ renames only)
## UNGreenCorr (probe:534) vs RBM2D Pins.lean:359 GreenCorr
{+(M : UNModel sz)+} [-Claim417 d-]{+UNClaim417 sz M+} [-AprioriImM d-]{+UNApriori sz M+}
{+∀ (r : ℕ → ℝ) (a b : ℝ), 0 < a → (∀ᶠ n in atTop, a ≤ r n ∧ r n ≤ b)+} {+(fun α => O (r n • α))+} (both sides)
```
`Defs/Sizes.lean:177`: `Admissible 𝔠 𝔡 := 0 < 𝔠 ∧ 0 < 𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 ∧ WO 𝔡`, so the dropped `0 < 𝔠`, `0 < 𝔡` are inside `Admissible`.
- **UNBUniv vs `1_2:452-459`** (read): "setting of MR:decol" (d ≥ 3, `W ≥ N^𝔠`, `(eq:WO)`) = `3 ≤ d`, `Admissible`; `O ∈ C_c^∞(ℝ^n)` = `IsTestFun` (index `∞`); `|E| ≤ 2-κ`, fixed `n = k ≥ 1`; scale `α/N` and GUE at the same `E` = `kPoint` on both sides (normalisation of `p^{(k)}`: T2001h, DECISIONS §10). Order `d, 𝔠, 𝔡, sz, k, κ, E, O` as in T2001/RBM2D. **PASS (2(a)).**
- **UNL32**: a pure port of the authorized input (DECISIONS §5); the added `3 ≤ d` only weakens the assumed hypothesis. Premises are functions of `N` only; arithmetic limit computation `un_L32_arith` (proved, instances at `τ = 1/2` and at the sharp threshold `N = 2^{2/τ}`, `τ = 1/8`); regularity premises go through the owed `UNStep1Good` (range `τ_s ≤ 𝔠𝔡`). **PASS (2(c)).**
- **2(d) / `𝓑(y)`** vs `1_2:570-577`: `UNBadY` (probe:1146) has window `N^{-1}W^{𝔡/3}`, threshold `W^{-𝔡/6}`; `unBadY_subset` (proved) gives `𝓑(y) ⊆ ⋃_{b: SBR b a ≠ 0} QUE-bad(b)` at `(ε₀, c) = (𝔡/3, 𝔡/6)` under `(eq:WO)`; `unBadY_measure_le` gives `ℙ ≤ (2d+1)p`; `un_que_exponent`: `-(2ε₀ ∧ 2𝔡/5) + 2c = -𝔡/15` (= `1_2:577`). `queBadMat` matches `(Meq:QUE)` (`1_2:409-416`: window `W^{-ε₀}λW^{d/2}/N`, threshold `W^{d-c}/N`, bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}`; parameter range `0<c<ε₀∧𝔡/5` in `UNQueBand`). `M_{y,α}` for `d ≥ 3` is not defined in the TeX (`1_2:571` cites [DYYY25] (2.24)): T2162a. **PASS.**
- **2(b) `UNCore`** (probe:759): inputs `UNL32`, `UNGUELocal`, `UNGreenCorrAll`, and for the model `UNDens` (positive lower bound, Lipschitz, `ρ_n = π⁻¹Im m_n(E+i0)`), `UNTrLocal`, `UNNormBound`, **`UNClaimAll` (the Claim (417) for the model's OU path)**; conclusion `UNUnivDilAt` for every `|E'| < 2` = DECISIONS §11 form (arbitrary `E'`, each side dilated by its own density). **Deviation from the ticket's 2(b) list** ("local law and delocalization on `D_{κ,ε}`, `(Meq:QUE)` at `(ε₀,c)`, a density"): delocalization and QUE are not inputs of the core; they enter only the band rows (`UNOURow`, `UNJakUywRow`) that produce `UNClaimAll` for the band model. Reason given (report b.8 item 2, d.3): the OU generator identity of `(EMCTE2)` has a first-order drift for a model with nonzero mean `iλΨ` (BA) — "to be checked by BA-D1, not verified here". Auditor check of the reason: `UNModel.ba` is `seqXmat (withLam 0) + const` (probe:110-118, `seqHBA`), and `ouMat` applies the OU flow to the whole matrix, so `d/dt E F(𝐇_t)` contains the term `-½e^{-t/2}⟨iλΨ, ∇F⟩`: the reason is correct for this OU path. Consequence: the BA chain must supply its own Claim (417) (OU QUE, `EMCTE2` with drift, Jak/Uyw), which is **not in the 52-ticket count**. Sound as a design and band-consistent (`un_bUniv_of_rows` composes it), but it changes what BA-D1 must deliver: **needs dispatcher sign-off**. Statement-level: **PASS as a design pin, with sign-off.**
- `UNGreenCorrAll` quantifies over every `UNModel` (RBM2D: band model on every sequence) and dilations `r_n ∈ [a,b]`, `a > 0` (T2162d). The a priori bound `UNApriori` excludes the degenerate model `H = E·I` (`Im m(E+i/N) = N`). Observation: UN-03..05 must prove the comparison model-independently.
- `UNOUQUE`/`UNOUDiag`/`UNEMCTE2`/`UNJak`/`UNUyw`: ports of RBM2D `Pins.lean:206,218,288,313,331` with `(ε₀,c) = (𝔡/3,𝔡/6)` and `c' = 𝔠𝔡/30` in the row `UNJakUywRow` (RBM2D `𝔠/36`); the `c'` value is the design value of target 3 (exponent table; proof is UN-19..23).

## 3. Hidden hypotheses, vacuity, cycles
- Only structure: `UNModel` (fields `μ`, `prob`, `H`, `herm`, `meas`: data and measurability, no mathematical hypothesis). Pins are `Prop` defs; composition theorems take them as explicit hypotheses.
- No cycle: `un_core_of_rows : UNInfty1Row → UNUnivMainRow → UNCore`; `un_bUniv_of_rows` uses rows + `UNL32`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNGUELocal`, `UNGreenCorrAll`; none of these mentions `UNCore`/`UNBUniv`. Merged dependencies only (imports: `Defs/*`, `Gauss/BlockAnderson`, `Induction/Defs`, `Propagator/Gap`).
- External hypothesis `UNL32`: limit check at the `d ≥ 3` OU time is `un_L32_arith` (compiled, b.7 of the prove report) — TEAM §8 lesson 14 satisfied.
- Auditor extreme inputs (scratch file importing the built probe, compiled, then deleted):
```
example (m E ρ) : ¬ UNDens m E ρ 0                         -- collapsed window excluded
example (W ≥ 1) (𝔡 > 0) : 1 ≤ queBound W 𝔡 (𝔡/3) (𝔡/6) (𝔡/15)  -- τQ = 𝔡/15: bound trivial; content only for small τQ
example : UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1/2) := un_dens_msc_zero   -- 2(b) non-vacuous at ρ_sc
$ lake env lean .audit/T2162Audit.lean; echo exit=$?
'RBM.Univ.un_bUniv_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_core_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unBadY_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0   (one unused-variable linter warning in the scratch file)
```
Prover's extreme inputs (compiled in the probe, re-checked by reading): `k = 0` (`unUnivDilAt_zero`), `k > N` (`kPoint_eq_zero_of_card_lt`), `|E| = 2-κ` (`un_rhoSC_edge`), `lam = W^{-d/2+𝔡}` and `lam = 𝔡⁻¹` (`inst_window_sub_*`), `n_f = 0` (`un_emcte2_zero`; false without `0 ≤ B`: `un_not_emcte2_zero_noB`), `τ_s = 𝔠𝔡` (`inst_step1_floor`).

## 4. Compiled nonempty instances (endpoint/composition theorems)
| theorem | instance (probe) | data | open hypotheses |
|---|---|---|---|
| `un_bUniv_of_rows` | `inst_bUniv_band` (1756) | `sz0` (`d=3`, `L=4(n+1)`, `W=(2(n+1))^5`, `N(0)=2097152`), `𝔠=1/6`, `𝔡=1/10`, `k=1`, `κ=1/10`, `E=0`, `O=bump` | rows, `UNL32`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNGUELocal`, `UNGreenCorrAll` |
| `un_core_of_rows` | `inst_core_of_rows` (1887) | same, `ρ=ρ_sc(0)`, `δ=1/2`, `UNDens` discharged | `UNTrLocal`, `UNNormBound`, `UNClaimAll` (MA/UN) |
| `UNCore` (band / BA) | `inst_core_band` (1772), `inst_core_ba` (1785) | `UNModel.band sz0` / `UNModel.ba sz0` | BA data (BA-D1 pins to be frozen) |
| `un_claimAll_of_rows` | `inst_claimAll_band` (1796) | `sz0`, `κ=1/10`, `E=0` | rows, MA/ST-6 inputs |
| `unBadY_subset`, `unBadY_measure_le` | `inst_badY_subset`, `inst_badY_measure`, `badY_zero` | `Idx 3 4 32`, `lam=1/64`, `𝔡=1/10`, `E=0` | none |
| `un_L32_arith` | `inst_L32_arith_half`, `inst_L32_arith_sharp` | `N=2097152, τ=1/2`; `N=2^16, τ=1/8` | none |
`Admissible` at `sz0` is the merged `sz0_admissible`; `bump` is nonzero (`bump_nondegenerate`). Every deterministic data hypothesis is discharged. Observation: `inst_bUniv_band` keeps the deterministic UN row `UNDensBandRow` (∀ bulk `E`, `δ ≤ κ/2`) as a hypothesis (target 5 allows UN pins as hypotheses); at its data (`κ = 1/10`) `un_dens_msc_zero` has `δ = 1/2 > κ/2`, so it is not plugged in. The row is true by inspection (`msc` bounded and Lipschitz on `|x| ≤ 2-κ/2`, `0 < η ≤ 10`) and is proved at `E = 0`; not a vacuity risk. **PASS.**

## 5. Inventory, exponent table, split (items 1, 3, 6)
```
$ python3 clos.py   (import closure of RBM2D/Main/BUnivHolds.lean at c9a24cf; auditor's own script)
CLOSURE 383 files 260192 lines
UN-part 58 files 61014 lines
```
Matches the report's `TOTAL files=58 lines=61014`; closure line total differs (report 260575, line-count convention): observation. Exponent rows re-derived by hand at `(𝔠,𝔡)=(1/6,1/10)`: `ε₀=1/30<𝔡/2`, `c=1/60<min(1/30,1/50)`, QUE exponent `-1/150 = -𝔡/15`, window `N^{-1}W^{1/30} ⊂ 𝓘_E` since `W^{-ε₀}λW^{3/2}/N ≥ W^{2𝔡/3}/N`; all agree with b.4/(a)(i). Ticket's `L = W^{1/𝔠-1}` is the d = 1 form (`un_dc_lt_one`: `d𝔠 < 1`), T2162g. Split: 52 tickets > 50, stated on line 2 of the prove report as required.

## 6. Paper-delta coverage
| Lean/paper difference | covered by |
|---|---|
| `kPoint` eigenvalue-sum form, arbitrary orthonormal eigenbasis | T2001h (DECISIONS §10) |
| `M_{y,α}` at `d ≥ 3` with `S^{(B)}` weights, union over `2d+1` blocks | T2162a |
| proof needs `𝐇_t` claims, ML outputs, `UNGUELocal` beyond `decol`, `locSC`, `(Meq:QUE)` | T2162b |
| `(Meq:QUE)` window `λ` vs `λ ∧ 1` (footnote `1_2:372`) | T2162c |
| `UNGreenCorr` for dilation sequences | T2162d |
| range of `τ_U`, `τ_s ≤ 𝔠𝔡`, `c' = 𝔠𝔡/30` | T2162e |
| BA universality in the dilated form `UNUnivDilAt` | T2162f (DECISIONS §11) |
| ticket's `L = W^{1/𝔠-1}` | T2162g |
| `UNL32` (external) | DECISIONS §5 |
All statement differences are covered. `UNClaimAll` as a core input and `UNNormBound` are design choices with no paper counterpart (the paper states no core theorem): recorded in report d.3 and b.8 item 10.

## 7. Verdict per target
| target | verdict |
|---|---|
| 1 inventory | PASS (58 files / 61014 lines reproduced) |
| 2(a) `UNBUniv` | PASS |
| 2(b) `UNCore` | PASS as a design, **needs dispatcher sign-off**: the core takes `UNClaimAll` instead of delocalization/`(Meq:QUE)`; BA-D1 must then supply the BA Claim (417) (OU QUE, `EMCTE2` with drift, Jak/Uyw), which is outside the 52-ticket count |
| 2(c) `UNL32` + limit computation | PASS |
| 2(d) `𝓑(y)`, `(2.22)/(2.23)` analogues | PASS |
| 3 exponent table | PASS |
| 4 interfaces | PASS (MA/ST-6/BA producers "to be frozen", listed) |
| 5 skeleton, 7 instances | PASS |
| 6 split | PASS; count 52 > 50 flagged at the top (DECISIONS §9 O2: the dispatcher asks Jun before any UN proof ticket) |

**Overall: PASS, needs dispatcher sign-off** on (i) the 2(b) interface (BA-D1 scope) and (ii) the over-50 count (DECISIONS §9 O2).
Observations (no statement/instance/build/axiom/delta effect): narrative says "137 declarations", the axiom count is 139; "names checked: 111" vs "109" in the command comment; closure line total 260575 vs 260192.
