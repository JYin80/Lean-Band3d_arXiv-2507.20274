Auditor model: claude-opus-5-5

# T2398 audit (round 3, Amend 2: D2-D4) — BA LW-14 design gate, report only

Written Sun Oct 11 08:33:31 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2398-audit3` (detached at `t/T2398` = `6429bb5`; merge base `1a5f972`). Inputs: `docs/tickets/T2398.md`, Amend 1, **Amend 2** (binding, CONTROL H204), `docs/reports/T2398-design.md` §(b′) (lines 171-282), `docs/reports/T2398-prove.md`, `docs/tickets/T2398-TL-proofs.md` (A.2, (B.1)-(B.3), T.1), `docs/supervisor/2026-10-11-0652.md` (C3, Q4). Scratch: scratchpad `T2398/` (`genax.py`, `Ax.lean`, `checks.py`, `NV.lean`, `Cut.lean`).

**Verdict: PASS** (D2, D3, D4). The round-1 BLOCKED (§8 question) is answered by Amend 2 (route R1). No dispatcher sign-off needed beyond the scheduled report-only merge (the probe stays on `t/T2398`).

## 1. Build, axioms, hygiene, diff, limits
```
$ lake build RBM3D.Probe.T2398Pins 2>&1 | grep -E "error|warning.*T2398Pins|Build completed|sorry"; echo "build exit ..."
Build completed successfully (3975 jobs).
build exit 0
$ python3 SP/genax.py RBM3D/Probe/T2398Pins.lean > SP/Ax.lean; grep -c print SP/Ax.lean    # every theorem/def/abbrev, full namespace
51
$ lake env lean SP/Ax.lean 2>&1 | sed -E 's/^.*depends on axioms/depends on axioms/' | sort | uniq -c
  51 depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2398Pins.lean; echo "grep exit $?"
grep exit 1
$ git diff --stat main...t/T2398
 RBM3D/Probe/T2398Pins.lean | 498 +++++++++++++++++++++++++++++++++++++++++++++
$ git status --short docs/reports/T2398-design.md docs/reports/T2398-prove.md     # main worktree (reports live there)
 M docs/reports/T2398-design.md
 M docs/reports/T2398-prove.md
$ wc -l RBM3D/Probe/T2398Pins.lean docs/reports/T2398-design.md
     498 RBM3D/Probe/T2398Pins.lean          # limit 500 (Amend 2)
     282 docs/reports/T2398-design.md         # limit 300; section (b′) = lines 171-282 = 112 <= 120
$ git diff -U0 2257f54 6429bb5 -- RBM3D/Probe/T2398Pins.lean | grep "^@@"     # round-2 changes
@@ -16,2 +16,2 @@   @@ -26 +26 @@   @@ -211 +211 @@   @@ -216 +216 @@      (header/docstring lines only, line numbers 1-275 kept)
@@ -276,6 +276,48 @@ @@ -283,5 +325,41 @@ @@ -352 +430 @@ @@ -354,0 +433,9 @@ @@ -378,0 +466,12 @@
```
Only the sole writable files are touched; no merged file, no frozen signature. Prove report line 1 `Prover model: claude-sonnet-5-5`.

## 2. D2 — the probe's section `Twist` (statement-centred)

**`BATwistLaw` removed; `BATwistAvgLaw` = its first conjunct verbatim** (script, whitespace-normalised):
```
$ python3 SP/checks.py
round-1 conjunct : PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ‖twTr C n (τ n) ω p.1 p.2‖) (fun n _ _ => sz.Bctl n (τ n))
BATwistAvgLaw    : PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ‖twTr C n (τ n) ω p.1 p.2‖) (fun n _ _ => sz.Bctl n (τ n))
identical: True
BATwistLaw still in probe: False
```
Index set: all ordered pairs `(c₁,c₂)`, one charge (`twTr` is `Tr(G̊ P_{c₂c₁})`, `twTr_eq` by `rfl`; `T̃_−(c₁,c₂) = conj T̃_+(c₂,c₁)`, proofs C, line 68; 0652 C3). `G̊ = C.GM = G − M` (`Carrier.lean:76-77`), so the circled loop of TL1 (proofs line 7). Bound `sz.Bctl n τ = W^{-d} B_{τ,0}` (`Defs/Sizes.lean:214-215`). PASS.

**`twK` (probe 306) against Amend 2 / proofs (B.1)** `K̃ = W^{-d} Σ_{a'} Θ^{(σ₁σ₂)}(a,a') M^{(B)}(σ₁)_{c₂a'} M^{(B)}(σ₂)_{a'c₁}`:
- `PropThetaQ Q t = Ring.inverse (1 − t•Q)` (`Propagator/Pins.lean:214-216`); `Q = BAMss … (σ 0) (σ 1)`, `BAMss M σ₁ σ₂ a b = BAMsigma M σ₁ b a * BAMsigma M σ₂ a b`, `BAMsigma M σ = if σ then M else Mᴴ` (`BA/MFixedPoint.lean:507-512`). For `(−,+)`: `Mᴴ_{ba} M_{ab} = |M_{ab}|²` — the entrywise product, not `M∘M`, as the amend requires. `Θ = (1 − tM^{(σ₁σ₂)})⁻¹` matches proofs line 38 (`S^{(B)} = I`).
- Factors `BAMsigma (σ 0) c₂ a' * BAMsigma (σ 1) a' c₁`, prefactor `(W^d)⁻¹`: exact match. "Θ from the carrier": `FlowFM` has no `Θ` field (`Carrier.lean:55-71`); `twMB` reads `M^{(B)}` off the carrier's `M` and equals `BAMB` at `baFMz` (`twMB_ba`, compiled, needs `0 < Im m`), so `twK` at BA is built from `BATheta` (`MFixedPoint.lean:515-516`), the same `Θ` as the merged BA K-loops. PASS (observation O1).

**`BATwistLoopLaw` (probe 328)**: `PrecL` over `U n = (Fin 2 → Bool) × Zd³` (all `σ ∈ {±}²`, all `(a,c₁,c₂)`), quantity `‖twL2' − twK‖` with `twL2'` = `twLoopX (twChg G σ₁) (twChg G σ₂)` on the **uncircled** `C.G`, bound `Bctl^{(3/2 : ℝ)}`, per `τ` with the same shape as `STLKgL` (`Carrier.lean:80-84`). No `∃ Kt`. PASS.

**Convention (probe 276-289)** vs proofs line 23/27: `Tr(XP_{c₁c₂}) = W^{-d}Σ_o X_{(c₂,o),(c₁,o)}` = `twTrP` (sum over `w ∈ [c₂]`, `X w (twShift c₁ w)`); `L̃ = W^{-2d}Σ_oΣ_{x∈[a]} X₁_{(c₂,o),x} X₂_{x,(c₁,o)}` = `twLoopX` (`w ∈ [c₁]`, `X₂ x w * X₁ (twShift c₂ w) x`). Hand check of the base case: at `G = M` (block-tied), `twLoopX = W^{-d} M^{(B)}(σ₁)_{c₂a} M^{(B)}(σ₂)_{ac₁} = twK` at `t = 0` (`Θ_0 = I`); the prover's numeric check (design §B, 2.2e-16, 4 charges) agrees. One convention for `twL2'`, `twK`, `twCirc`, `twWard`. PASS.

**Model-free statements (row L4t), checked against the proofs:**
| pin | proofs | check |
|---|---|---|
| `twFold` (340) | (B.2) | `‖twLoopX‖² ≤ twSq X₁ c₂ a · twSq X₂ a c₁`; Cauchy-Schwarz over `(o,x)` with exactly these two sums (proofs line 47). True for all matrices; no hypothesis. |
| `twWard` (345) | T.3, `n = 2` | `Σ_a E_a = W^{-d}`, `GG^* = G^*G = (G−G^*)/(2iη)` ⇒ `Σ_a L̃ = (2iW^dη)⁻¹(Tr(GP) − Tr(G^*P))` for both `σ`: matches. |
| `twCirc` (352) | A.2 (line 28) | `Tr(X₁E_a(X₂−M)P) = L̃ − W^{-d}M^{(B)}_{ac₁}Tr(X₁P_{ac₂})`: matches term for term. |
| `twK_bound` (360) | T.1 (i)-(ii) | (i) weakened to `C·W^{-d}B_{t,0}` (valid: `Bparam` decreasing in `K`, `Defs/Params.lean:36-37`); (ii) `Σ_a‖K̃‖ ≤ C(W^dη_t)⁻¹`, `η_t = (1−t)Im m` (`Loop/GLoopFlow.lean:58`) = proofs' `(Im m)(W^dη_u)⁻¹`. `C` before `𝔠, sz, z, t, n`. |

**Non-vacuity of hypotheses** (auditor's scratch checks, not in the probe):
```
$ lake env lean SP/NV.lean    # twWard's two resolvent identities at G = I•1 (= (0 − iη)⁻¹, η = 1), sz0, n = 0: proved
... (lint warnings only) ...
exit 0
$ lake env lean SP/Cut.lean   # example (h : BALWCutExp d) : BALWCutExpTw d := fun … _ _ => h …   (same conclusion, +TL1, +TL2)
exit 0
```
`twCirc`'s hypothesis is the block-tie of `BAMfine_eq` (`BA/GreenSchur.lean:93`), already discharged in the compiled `twTie_ba`/`twMB_ba`. `twFold` has none.

**Compiled instances** (built with the module, §1): 467 `BALWCutExpTw 3` at `d = 3`, `sz0` (`L = 4`, `W = 32`, `λ = 1/64`), `flow_sz0`, `t ≡ 1/2`, every deterministic hypothesis discharged; Step 1/2 pins and TL1/TL2 (owed pins, Amend 2 D1) stay hypotheses. 474 `twK_bound 3` at the same data, no hypothesis left. 460, 479 (round 1) unchanged. Non-degenerate (no `N = 0`, empty index, collapsed window, `False` premise).

**Hidden hypotheses / cycles.** All premises are explicit `Prop`s in signatures; no structure fields added. The probe imports only merged modules. TL1/TL2 have no producer (owed text pins with the standing of `STLKgL`, 0652 Q3; new BA stage, C4): the limit check is the base case `L̃_0 = K̃_0` (proofs line 8; hand check above) and the numeric scaling `|L̃ − K̃| ≍ W^{-2d}` (design §B, `limit2.py`, d = 1). D2: **PASS**.

## 3. D3 — row table under R1 (design §(b′) C)
```
$ python3 SP/checks.py   (rows transcribed from design §C)
totals lo/central/hi: [8286, 10858, 19627]
L4b2 = 1255 x TW (0.73,0.85,1.61): [916, 1067, 2021]  basis 1716-828+1+366 = 1255
central x 1.144 = 12422
```
- L4b2: twin of `lwExpI1K_holds`/`lwExpI23K_holds`/`lwExpI41K_holds` with `(twL2', twK, twTr)` for `(𝓛^{(2)}, 𝒦^{(2)}, Tr(G̊E))`, hypotheses `BATwistAvgLaw`, `BATwistLoopLaw`; re-priced 916 / 1,067 / 2,021 (the analysis' 700 / 1,000 / 1,800 noted). Matches D3.
- L4a2 assembly: two more premises, `BALWCutExpTw` (compiled; weakening of `BALWCutExp`, `Cut.lean` above).
- New row L4t (F, role `prover-hard`, 320 / 450 / 700): `twFold`, `twWard`, `twCirc`, `twK_bound`.
- Order re-stated; "No row waits for §8"; L4t can start at once; producers of TL1/TL2 not priced (D3 last bullet). Totals reproduce. PASS.

## 4. D4 — paper delta T2398d
```
$ python3 SP/checks.py
T2398d verbatim (sup 170-177 vs design §D, 8 lines): True
$ grep -c "T2398" docs/paper-deltas.md
0
```
Recorded in the supervisor's wording as a candidate (the dispatcher appends and numbers it). The further Lean/paper-text differences (TL1 one charge, TL2 exponent 3/2 vs proofs' `2 − δ`, `twK_bound` (i) without `|a−c₁|`-decay and `e^{-c|c₁−c₂|/2}`) are weakenings of the T2398d statements and are listed in design §D. Round-1 candidates T2398a-c, e, f stand (round-1 audit §6). PASS.

## 5. Observations (no RETURN)
- O1 `twMB` reads `M` at offset 0 of any carrier; it is `M^{(B)}` only for a block-tied `M` (`twMB_ba`, BA, `0 < Im m`). The L4b2 / producer tickets should state `twK` at `baFMz` (or use `BATheta` directly) so no non-BA reading arises.
- O2 `twK_bound` has `∃ C` (fixed before `sz`, correct order) against CLAUDE §7's "hard-code constants"; T.1's `C_dC_M²` depends on `κ` via `C_M`. The L4t ticket should pin the form (explicit `C(d, κ)` or the `∃ C` kept with a dispatcher note).
- O3 Instance 474 uses `c₁ = c₂ = 0`; the twK_bound hypotheses do not depend on `c₁, c₂`, so it is non-degenerate, but an L4t instance with `c₂ ≠ c₁` would be more telling.
- O4 Non-vacuity of `twWard`'s hypotheses is compiled only in this audit's scratch (`NV.lean`), not in the probe (the probe is at 498/500 lines); the L4t ticket should carry it.
- O5 Design §0 line 1 still reads as round 1 (STOP); §(b′) states that Amend 2 resolves it. Record only.

## For the hub
Report-only merge (rule (A); CLAUDE §3 report-only path): state, prove, design and this audit report; `RBM3D/Probe/T2398Pins.lean` stays on `t/T2398` and is never merged.
