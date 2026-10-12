Auditor model: claude-opus-5-5

# T2427 1a-audit, round 2 (design gate, after one rule-(B) repair of the probe) — Sun Oct 11 23:21:10 UTC 2026 (`date -u`)

Inputs: ticket `docs/tickets/T2427.md`; `docs/reports/T2427-prove.md` (a), (a″), (a‴); round-1 audit (this file, overwritten; its
"Required for resubmission": 1. add `0 < ε` to `twAvgReg`, update the examples at `:224`, `:235`; 2. recompile and paste in (a‴)).
Branch `t/T2427` at `73b3a8d`; audit worktree `../RBM3D-wt/T2427-1a-audit2` (detached, `73b3a8d`, build cache cloned with `cp -c -R`).
Scratch: `scratchpad/T2427/audit2/` (prover scripts copied to `audit2/src/` and rerun there; auditor's own `reg_eps_pos.py`, `chk_pos.lean`, `chk_neg.lean`).

## 1. Round-1 item 1: the repair (diff by script)
```
$ git diff --stat d60d13d 73b3a8d
 RBM3D/Probe/T2427Pins.lean | 6 +++---
$ git diff -U0 d60d13d 73b3a8d | grep '^[-+][^-+]'
-  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
+  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
-  obtain ⟨-, hb, he⟩ := h (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0
+  obtain ⟨-, hb, he⟩ := h (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) (by norm_num) flow_sz0
-  obtain ⟨-, hb, he⟩ := hreg (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0
+  obtain ⟨-, hb, he⟩ := hreg (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) (by norm_num) flow_sz0
```
Exactly the requested change; nothing else in the probe moved. The two `twAvgReg` examples (`:222-226`, `:230-244`) discharge `0 < 1/10`.
Auditor's own premise check (probe copied to scratch, one `example` appended, compiled from the audit worktree):
```
$ lake env lean audit2/chk_pos.lean   # example ... (hκ : 0 < κ) (hε : 0 < ε) (hF : BAFlow sz κ ε 𝔠 𝔡 z) := h κ ε 𝔠 𝔡 sz z hκ hε hF
pos exit=0
$ lake env lean audit2/chk_neg.lean   # same without hε
neg exit=1
chk_neg.lean:278:59: error: Application type mismatch: The argument
  hF
has type
  BAFlow sz κ ε 𝔠 𝔡 z
but is expected to have type
```
The round-1 counterexample (`ε = −1/2`, `Im z_n = N⁻¹`) no longer satisfies the premises.

**Is the repaired `twAvgReg` now true?** Conjunct 3 (`∀ᶠ n, ∀ t ∈ [0,T₀], η_t⁻¹ + 1 ≤ N`). Definitions (merged):
```
FlowPins.lean:328     eta := fun n t => etaOf (BAmF sz lam0 E n) t          Loop/GLoopFlow.lean:58  def etaOf (m : ℂ) (t : ℝ) : ℝ := (1 - t) * m.im
MFixedPoint.lean:279  def BAt0 (z m : ℂ) : ℝ := m.im / (m.im + z.im)
MFixedPoint.lean:435  def BAdom ... := κ ≤ (BAm d L g z).im ∧ (N : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
GreenSchur.lean:59    theorem BAflow_real ... (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) (BAmF ...)   -- κ ≤ Im m₀
```
So `η_t ≥ η_{T₀} = (1−T₀) Im m₀ ≥ κ Im z/(Im m + Im z) ≥ (κ/2) N^{−1+ε}` (`Im m ≤ 1` by the Ward identity `MFixedPoint.lean:386`
and `|m| ≤ (L^{-d}Σ|M_ab|²)^{1/2}`), hence `η_t⁻¹ + 1 ≤ (2/κ)N^{1−ε} + 1`, which is `≤ N` eventually because `ε > 0` and `SizeTendsto`:
```
$ python3 reg_eps_pos.py
kappa=0.5 eps=0.1: (2/kappa)N^(1-eps)+1 <= N from N=2^21 on (checked 2000 doublings: True)
kappa=0.5 eps=0.01: (2/kappa)N^(1-eps)+1 <= N from N=2^200 on (checked 2000 doublings: True)
kappa=0.1 eps=0.1: (2/kappa)N^(1-eps)+1 <= N from N=2^44 on (checked 2000 doublings: True)
eps=-1/2 (round-1 counterexample): excluded by the new premise 0 < eps; eps -> 0: threshold 2^lg grows like (2/kappa)^(1/eps)
```
Conjuncts 1–2 hold at every `n` (`η_t ≥ η_{T₀} > 0`; `‖BAMfine‖ ≤ 1`, `BAMfine_norm_le_one` `GreenSchur.lean:105`; `C.S n = 1`, so
`Σ_{α,β} W^{-d}S_{[α][β]} = N`); script envelope check below (§3). Consumers (`twAvgSPrec :114`, `BATwistAvgRec :164`, `BATwistAvgProd`
`TwistPins.lean:155`) all carry `0 < ε` (pasted in (a‴), re-read here). **Item 1: met. Target 2 (iv): PASS.**

## 2. Round-1 item 2: recompile (deliverable (iii))
```
$ cd ../RBM3D-wt/T2427-1a-audit2 && git rev-parse --short HEAD && lake env lean RBM3D/Probe/T2427Pins.lean   # Sun Oct 11 23:15:12 UTC 2026
73b3a8d
exit=0
$ grep -ciE 'error|warning' probe.out  ->  0
$ grep -E '^[A-Za-z@∀]' probe.out | cut -c1-40
@twAvgGPM  @twAvgGPG  @twAvgS1  @twAvgS2  @twAvgX  @twAvgXmax  @twAvgMomentAt  twAvgMoment : ℕ → Prop  twAvgSCS : ℕ → Prop
twAvgSPrec : ℕ → Prop  twAvgT6 : Prop  twAvgReg : ℕ → Prop  @BATwistAvgRecAt  BATwistAvgRec : ℕ → Prop  T2427_TL1b : Prop
∀ (d : ℕ), BATwistAvgRec d : Prop
$ git diff --stat main...HEAD
 RBM3D/Probe/T2427Pins.lean | 275 +++++++++++++++++++++++++++++++++++++++++++++
$ wc -l < RBM3D/Probe/T2427Pins.lean; grep -c -E 'sorry|admit|native_decide|^axiom' ...; grep -c -E 'Step2Gen_|STthetaOpg' ...
275   0   0
$ lake env lean docs/tickets/checks/T2427-check.lean (from the audit worktree)  ->  exit=0, error lines 0
$ grep -rn --include='*.lean' -e twAvg -e BATwistAvgRec -e T2427_TL1b -e baTwistAvgRec RBM3D RBM3D.lean   (main 0a8176c) | wc -l  ->  0
$ grep -n -e twAvg -e BATwistAvgRec -e baTwistAvgRec docs/tickets/T2428.md T2429.md T2430.md T2431.md  ->  (no match)
```
(a‴) pastes the same compile (exit 0, the corrected `twAvgReg` text `:134-149` extracted by `awk`, the repair diff, a negative control).
**Item 2: met.** The probe stays ≤ 400 lines and touches only its own file (never merged).

## 3. Deliverable (i): numerics rerun (prover scripts, fresh MC seed)
```
$ python3 inst.py   (tail)
g=0.01562: Im m=0.9993  C_M=sum_b|M_ab|=1.101 ...  g=1.00000: Im m=0.4665  C_M=15.625 ...  g=10.00000: Im m=0.3654  C_M=13.378
eps'=0.05: ... absorbed form needs W^eps' >= C_M^Lean, i.e. log10 W >= 314 (astronomical); kept form `exists C` needs none
Step 4: (L4 * L2)^(1/2) = Bctl^((3+1)/2) = Bctl^2; needed: Bctl^2 (the term 2p W^eps' B^2 X^(2p-2)) slack 0
coefficients: (p-1) + p = 2p-1 <= 2p (pin) : slack 1; factor t <= 1 : slack 1-t = 1/2 at t=1/2
n=0: eta_(t0)=0.3061; 1/eta+1/Im m0 = 4.267 <= N=2.10e+06 (C0=1); Bctl(t=1/2) 6.196e-05 >= N^-1 4.768e-07: True; ...
n=3: eta_(t0)=0.3056; 1/eta+1/Im m0 = 4.273 <= N=1.44e+17 (C0=1); Bctl(t=1/2) 5.686e-14 >= N^-1 6.939e-18: True; ...
$ python3 mc_det.py 20 3
(C.4) max |Tr(G S[G°] M P) - sum_c ...| over 20 samples = 1.10e-17
Step 4 loop forms: max|S2 - S2_loop| = 1.52e-18, max|S1 - S1_loop| = 6.55e-19
CS bounds |S2| <= sum_c|M_cc1|(L4 L2)^(1/2), |S1| <= ...: min slack = 1.11e-03, 1.59e-03 (>= 0 required); ratios |S|/bound: 0.587, 0.196
twTr c1 c2 (TwistPins.lean:57) = Tr(G° P_(c2,c1)): max err 0.00e+00
$ C1=a C2=b python3 lean_conv.py 20 5 det    (three pairs; grep C.4 / CS / envelope)
c1=0,0,0 c2=1,0,0: (C.4 Lean) 2.92e-18 | CS min slack S1 1.62e-03, S2 1.09e-03 | max|S1|,|S2| = 4.120e-04, 1.647e-03 <= N eta^-3 = 8.563e+03; max|twTr| = 4.554e-02 <= eta^-1 + 1 = 4.410
c1=1,2,0 c2=0,1,2: (C.4 Lean) 3.47e-18 | CS min slack 1.55e-03, 1.07e-03 | max|S1|,|S2| = 3.354e-04, 1.479e-03 <= 8.563e+03; max|twTr| = 4.489e-02 <= 4.410
c1=2,1,1 c2=2,1,1: (C.4 Lean) 7.41e-18 | CS min slack 7.06e-03, 1.70e-03 | max|S1|,|S2| = 3.450e-03, 1.057e-02 <= 8.563e+03; max|twTr| = 1.160e-01 <= 4.410
$ python3 lean_conv.py 40000 33      (seed not used in (a) or round 1; 152 s)
p=1: LHS E|T|^2 = 7.621879e-04 +- 3.8e-06 | RHS = 7.548805e-04 +- 8.9e-07 | paired LHS-RHS = 7.31e-06 +- 4.4e-06 (z=1.65) | S-terms sign-flipped: z=388.4
p=2: LHS E|T|^4 = 1.160805e-06 +- 1.3e-08 | RHS = 1.155476e-06 +- 5.2e-09 | paired LHS-RHS = 5.33e-09 +- 9.4e-09 (z=0.57) | S-terms sign-flipped: z=125.5
```
All reproduce (a), (a″). The identity `twAvgMomentAt` agrees within `2σ` at a fresh seed (seeds 11, 12, 21, 33: `z_{p=1}` = 0.92, −0.52, 0.23,
1.65; combined ≈ 1.1σ), the sign-flipped variant is rejected (`z > 120`). Exponent `3/2 + 1/2 = 2` sharp; every other row has slack. **Met.**

## 4. Targets (statement level; unchanged since round 1 except `twAvgReg`)
| target | Lean (probe) | check | verdict |
|---|---|---|---|
| 1 `BATwistAvgRec` | `:163-166`, conclusion `BATwistAvgRecAt :156-160` | frame = `BATwistAvgProd` (`TwistPins.lean:154-157`) plus `∃ K > 0` before `𝔠, sz, z` (O2 form, decided in (a); absorbed form would need `log10 W ≥ 314`); TP:89 term by term with `C_M → K` | PASS |
| 2 (i) `twAvgMoment` | `:87-98` | exact identity; hypotheses those of `BAExp14a_lanlw_diag`; numerics §3 | PASS |
| 2 (ii) `twAvgSCS`, `twAvgSPrec` | `:104-119` | CS pathwise (script slack > 0); `STLmaxgL` (`Carrier.lean:87-91`) is over all `(Fin k → Bool)` signs, uniform in labels; `(B³·B)^{1/2} = B²` | PASS |
| 2 (iii) `twAvgT6` | `:125-130` | no floor, uniform in `v` (`StochDomAt` bounds `badSetAt` over all `v`, `Defs/StochDomAt.lean:61-63`); delta T2427b | PASS |
| 2 (iv) `twAvgReg` | `:137-149` | repaired, §1 | PASS |
| `T2427_TL1b` | `:169`, `Iff.rfl` check `:275` | statement only, as the ticket asks | met |
| 3 instances | `:179-244` | `(1/2,1/10,1/10,1/6)`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2` (`half_lt_t0`); `n = 0`, `p = 1, 2`, `c₂ = (1,0,0) ≠ 0`; only `LWAvgLawgL`, `STLmaxgL`, the target pins stay hypotheses; compiled | met (statement level) |

No hidden hypothesis (all are `Prop` definitions with hypotheses in the binder list; no structure field), no cycle (inputs: other gates'
pins `LWAvgLawgL`, `STLmaxgL`; merged `baLanlw_holds`, `BAMB_row_l1`, `BAMfine_norm_le_one`, `BAflow_real`). C1: no smallness of `g`,
`Step2Gen_`/`STthetaOpg` grep 0.

## 5. Deliverables (ii), (iv), (v); stop lines
- (ii) Route R-a, mirror form (C.3′)–(C.5′) in (a″); 𝒮₁, 𝒮₂ fold into the mirror loop pairs of TP:83 (script loop-form errors ≤ 2e-18). Met.
- (iv) TL1b plan (`T2427-prove.md:136`): S1 bootstrap, Markov at `μ`, union over `L^{2d} ≤ N²` pairs, `PrecL = StochDomAt`, no net. Met.
  It uses `twAvgReg` for `Integrable`; TL1b has `0 < ε` from the frame of `BATwistAvgProd`, so the repair costs TL1b nothing.
- (v) Predicted `TwistAvgA ≈ 1,200`, `TwistAvgA2 ≈ 1,280` (+30%: 1,560, 1,660) vs boundary-move 1,700 and **binding stop line 2,000**:
  not hit; fallback (T.6 back to TL1b) not invoked, so no sign-off is needed for it. Probe 275 ≤ 400.

## 6. Paper deltas
T2427a (mirror form; `twTr c₁ c₂ = T̃_{(c₂,c₁)}`), T2427b (`twAvgT6` at scale `N`, no floor), T2427c (`K` kept): proposed in (a″).
The repair adds a premise that the paper has (`ε > 0` in the domain `N^{−1+ε} ≤ Im z`), so no new delta. Coverage complete.

## 7. Observations (no verdict impact)
- The docstring of `twAvgReg` (`:134-136`) does not mention `0 < ε`; (a‴) flags it for 1b. Docstrings are not evidence (§5.7).
- `lean_conv.py` fails if `C1`/`C2` are passed through an unquoted zsh word list (auditor's shell, not the script); rerun with explicit env vars.

## 8. Verdict
| item | verdict |
|---|---|
| round-1 item 1 (`0 < ε` in `twAvgReg`, examples updated) | met |
| round-1 item 2 (recompile, (a‴) with script output) | met (exit 0 reproduced at `73b3a8d`) |
| (i) exponent table, instance, MC `p = 1, 2` | met |
| (ii) route R-a, form of (C.3)–(C.5), mirror delta | met |
| (iii) probe: targets 1, 2 (i)–(iv), `T2427_TL1b`, target 3 at statement level | met |
| (iv) TL1b plan; (v) lines vs stop line 2,000 | met; no stop line hit |

**Verdict: PASS.** No dispatcher sign-off requested (fallback not invoked; no binding stop line hit). Stage 1b may start.
