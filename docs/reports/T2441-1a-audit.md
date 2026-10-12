Auditor model: claude-opus-5-5

# T2441 (BA-TL TL2d) — 1a-audit (design gate + probe), Mon Oct 12 06:36:19 UTC 2026

Inputs: ticket `docs/tickets/T2441.md`; `docs/reports/T2441-prove.md` (a) + (a″); branch `t/T2441` at `f459c7f`, audited in the detached worktree `../RBM3D-wt/T2441-1a-audit`. Scratch: scratchpad `T2441/aud/`.

## 1. Probe recompile (own worktree)
```
$ cd ../RBM3D-wt/T2441-1a-audit && lake env lean RBM3D/Probe/T2441Pins.lean      (Mon Oct 12 06:29:28 UTC 2026)
exit=0   (only the 12 #check lines; no error, no warning)
BATwistStepFixed : ℕ → ({d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) → Prop
T2441_TL2e : Prop
... (BATwistGridMart, BATwistZeroMode, baTwistGridRem/Tail/WTail_holds, baTwistGridAssemble_holds, BATwFrame, BATwistLoopLaw, BATwistLoopStep as in (a″))
$ lake env lean docs/tickets/checks/T2441-check.lean        -> exit=0
$ lake env lean T2441/aud/tl1.lean   (F5: twSteps ⇒ LWAvgLawgL ∧ STLmaxgL at every τ ∈ [s,t]; 58 lines, 0 sorry) -> exit=0
$ lake env lean T2441/aud/t1.lean    (target 1 as a 3-line corollary, written by the auditor:)
    obtain ⟨C₀, hC₀, hR⟩ := baTwistGridRem_holds d
    exact ⟨C₀, hC₀, baTwistGridAssemble_holds d C₀ hC₀ hR (baTwistGridTail_holds d) (baTwistGridWTail_holds d)⟩
  -> exit=0
$ git diff --stat main...t/T2441
 RBM3D/Probe/T2441Pins.lean | 332 +++  (1 file)
$ grep -cE "sorry|admit|native_decide|^axiom|Step2Gen_|STthetaOpg" RBM3D/Probe/T2441Pins.lean  -> 0
$ git grep -n -e BATwistStepFixed -e baTwistStepFixed -e T2441_ -e baTwistGridMart_holds -e baTwistZeroMode_holds main -- RBM3D RBM3D.lean | wc -l  -> 0   (main c43bdf1)
$ git log --all --oneline -- 'RBM3D/BA/TwistStep*' | wc -l  -> 0
```

## 2. Numerics rerun
```
$ python3 T2441/aud/pre.py > pre.out; diff pre.out <(a)'s run T2441/pre.out>
exit=0; IDENTICAL to (a) pasted run           (all of [E] [G] [A] [B] [K] [T] [R] reproduce verbatim)
$ python3 T2441/aud/ev.py
TL2d central 1250: at min/median/max ratio -> 1424 / 2572 / 3430 lines in total (two files, stop line 2000 each)
Im w/(|w|^2+g^2 L^d) at Im w=1.2, g=5, L=4, d=3: 7.493256e-04
Im w/(|w|^2+g^2 L^d) at Im w=1.0006, g=5, L=4, d=3: 6.249839e-04
$ python3 -I T2441/aud/cites.py    (23 file:line citations of (a)/(a″): declaration line found)
EKPins:baEKSameRow_holds 568 OK | TwistKer: baTwKerFar_holds 86, baTwKerZero_holds 256, baTwKDecay_holds 455 OK
TwistKer2: Src5 1364, Src1 168, Src2 589, Src4 422, _Z_crude 1321, _eta_inv_le 708, _Bctl_rpow_ge 1342, _eta_pos 127, _conU 281 OK
TwistQV:baTwistSrc3_holds 1385 | TwistGrid2:BATwistDuhamel_holds 143 | TwistGrid:BATwistHier_holds 855 | EKPins:BAuKer_eq_one_add 62 OK
TwistAvgB:baTwistAvgProd_holds 451 | TwistPins:twWard_holds 412 | GreenSchur:BAflow_real 59 | KBase:BATheta_swap 350, BATheta_row_sum_pm 381 | MFixedPoint:BASelf_subord 215  OK
```

## 3. Statement of target 3 (the new pin) — script diff against the merged pins
```
$ diff <BATwistLoopLaw body, TwistPins:96-98> <probe conclusion, T2441Pins:48-50>
3c3
< (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
> (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n))
$ diff <twSrc body, TwistPins:251-252> <probe bootstrap hypothesis, T2441Pins:44-46>
  line 1 (index TimeIcc s t n × (Fin 2 → Bool) × Zd × Zd × Zd): identical
  F := ‖twL2' − twK‖ at p.1;  bound Ξ n * Bctl n p.1 ^ (3/2)   (twSrc: Ξ n ω * (η⁻¹ * Bctl^e))
```
Checked against the ticket's intended shape (item 3): frame `BATwFrame d R` (merged, `TwistPins:146`; κ ε 𝔡 Cd → ∃ 𝔠d ≤ 1/100 → 𝔠 sz z, BAFlow, `0 ≤ s < t ≤ T0`, `R`, `STConStInd`, `twSteps`); `BATwistLoopLaw C μ s →`; `∀ Ξ : ℕ → ℝ, (∀ n, 1 ≤ Ξ n) →`; bootstrap on `[s,t]`; `∀ τ, s ≤ τ ≤ t →`; conclusion at `τ` over `(Fin 2 → Bool) × Zd³` (all four charges in one statement); exponents `3/2` in and out, `+1/6` on the Ξ term (T.11 (iv) at γ = 3/2). Quantifier order is the frame's; no structure field, no new hypothesis beyond the ticket's list. The conclusion is exactly `BATwistLoopLaw`'s body with the bound `B^{3/2}(1 + B^{1/6}Ξ)`, so at `Ξ ≍ 1` it gives `BATwistLoopLaw C μ τ` (TL2e's closing step). **Statement: PASS.**

**Decision on the Ξ̃ form (ticket item 3, DECISIONS §249 (2): the 1a-audit decides): the `≺`-at-deterministic-level form is ACCEPTED.** Reasons, checked on the definitions:
- `PrecL = StochDomAt μ sz.size` (`Chain/Carrier:51`), whose failure event is `badSetAt = {ω | ∃ u, …}` (`Defs/StochDomAt:53`): the union over `u ∈ TimeIcc s t × σ × a × c₁ × c₂` is **inside** the probability. Hence the hypothesis gives one good event `G_n` (prob ≥ 1 − N^{−D}) on which `‖Z_v‖ ≤ N^{τ'}Ξ_n B_v^{3/2}` for all `v ∈ [s,t]` simultaneously.
- `BATwistSrc4`'s premise (`TwistPins:269-272`) is pathwise `∀ n ω v`; it is met by `Ξ'(n,ω) := N^{τ'}Ξ_n` on `G_n` and `max(N^{τ'}Ξ_n, a priori)` off it, the a priori pathwise level being F4's `2(2/κ)²N⁴` (compiled in the probe, lines 122-139, 258-276, via `TwistKer2_Z_crude`). Src4's output `B̃₂ ≺ Ξ'η⁻¹B^{5/3}` then gives `B̃₂ ≺ Ξ_n η⁻¹B^{5/3}` (one more union with `G_nᶜ`); `Ξ'` needs no measurability (`badSetAt` under an outer measure).
- A deterministic level is a functional of nothing random, so it passes to the grid walk `Pp` through `ST_grid_whp_of_sections` (`Step2Events:93`) / `StochDomAt.precomp_param`; the pathwise `Ξ̃(ω)` on the coupling would not (ticket item 3).
- Consequence for TL2e (stated in (a) row 14 and (vii)): `Ξ_j` deterministic; start `Ξ_0 = 2(2/κ)²N⁴` (pathwise ⇒ ≺, as the probe's instances do); per-τ → `TimeIcc` by the net with the worst-net-point sequence `τ*_n` (the pin is `∀ τ`), union bound over `≤ N^C` points; contraction since `Bctl_t ≤ C·W^{−2𝔡} ≤ C·N^{−2𝔡𝔠}` (`WO`: `λ ≥ W^{−d/2+𝔡}`, BAFlow: `W ≥ N^𝔠`), `O(1/(𝔡𝔠))` rounds; final `Ξ_J ≤ 2` gives `BATwistLoopLaw C μ τ`. Plausible; nothing of it is a 1b obligation. Paper delta `T2441a` (deterministic level) is proposed in (a″).

## 4. Stage-1a deliverables (ticket "1a items")
| item | where in (a)/(a″) | audit check | result |
|---|---|---|---|
| (i) drift 2, martingale 13/8, B̃₂ 3/2+1/6 | rows 1-4 | [E] rerun; e=4−1/4−1/2=13/4, e/2=13/8 ≥ 3/2 | met |
| (i) log((1−s)/(1−u)) ≤ C log W from STConStInd | row 6 | `STConStInd` (`Induction/Defs:168`): Bctl_t^{𝔠d} ≤ (1−t)/(1−s) | met |
| (i) regime (i) integrals with κ_{v,u}; regime (ii) TP:169 | rows 9-11 | [R] rerun: ratios 0.43-0.95; (ii) 0.50 ≤ 29-37 | met |
| (i) BATwKerFar side conditions; power of W | row 7 | `u ≤ 1−g²/L²` from STCaseI and g₀ ≤ λ; `W⁻¹ ≤ (1−u)/(1−v)` with power `W^{d𝔠d}`, needs `𝔠d ≤ 1/(2d)` in the ∃ (row 5) — the prover chooses 𝔠d, so admissible | met |
| (i) every F1 use | row 8 (ℓ_v, ε′ with factor d, A=(κ+1)/κ, κ_{v,u}) | consistent with `BATwKerFar`/`BATwKerZero` signatures (TwistPins:199-215) | met |
| (ii) case × merged input | row 17 | 23 citations resolve (§2) | met |
| (iii) bootstrap form + passage to grid | row 14, (vi) decision 2 | §3 above | met; form accepted |
| (iv) grid budget, CK vs N^{C₀}√Δ, weights, decision-4 term | row 13 | [G] rerun: D=1 slack 8, D=5 slack 14; K is free (∀ K ≥ N^{CK}) | met |
| (v) concrete instance (numbers) | (ii) I-A, I-B; [A] [B] [K] [T] | rerun identical | met (see O1) |
| (vi) pin text + `T2441_TL2e`, compiled | (a″) (vi) | §1 exit 0 | met |
| (vii) TL2e plan ≤ 10 lines | (a″) (vii), 6 lines | net S2, per-τ→TimeIcc, bootstrap from a priori N^C, both regimes, T.12, T.13/S3 | met |
| (viii) lines per file; merged privates file:line | (a″) (viii) | ev.py rerun; privates at stated lines, `open private` pattern exists (`TwistGridRem2:35`) | met |
| target 2: `eta` of `baFMz` = (1−t)·Im m of `twMB_ba` | row 15 | `FlowPins:328` `eta := etaOf (BAmF sz lam0 E n) t`, `GLoopFlow:58` `etaOf m t = (1−t)*m.im`; `baFMz = baFM sz (BAflowLam0 sz z) (BAflowEs sz z)` (`FlowPins:393`), same `m` as `twMB_ba` (`TwistPins:80`) | met |
| stop rule: TL1 at τ from `twSteps` | row 16, F5 | tl1.lean compiles (§1) | no premise missing |

Corrections to the ticket found by (a), verified: (−,+) row sums come from `BATheta_swap` (`KBase:350`, `σ₁ σ₂ ↦ σ₂ σ₁`), not `BATheta_conj` (`KBase:362`, `false false` vs `true true`).

## 5. Compiled nonempty instances (probe; for 1b)
| statement | datum | deterministic hypotheses discharged | remaining hypotheses |
|---|---|---|---|
| target 2 `BATwistZeroMode 3` (as hypothesis `h`) | sz0, zSeq, flow_sz0, t≡1/2, n=0, σ=(false,true), c₁=0, c₂=(1,1,0) | all | none (h is the target itself, probe only) |
| target 3 `STCaseI` | sz0, s≡1/2, t≡2/3 | frame, t ≤ T0, STCaseI, STConStInd (∀ 𝔠d), bootstrap at Ξ=32N⁴ | `twSteps`, TL2 at s (other gates' pins; ticket item 5) |
| target 3 `STCaseII` | new `T2441_szII` (L≡4, W=n+25, λ≡5), w=(5003/5000)i, κ=3/5000, s≡0, t≡1/2000 | BAFlow (proved), t ≤ T0, STCaseII, STConStInd, bootstrap | `twSteps`, TL2 at s |
| emptiness at sz0 | – | `¬∃ s t, s<t ≤ T0 ∧ STCaseII sz0 s t` compiled (lines 294-308) | – |
Ticket item 5 allowed `STCaseII` to stay an instance hypothesis; on `sz0` that premise is provably False (compiled), so the new datum is required, not optional. The ticket's target-2 point `c₂=(1,0,0)` gives `0 = 0` ([T]: `|Im M_{c₂c₁}| = 0`, odd distance at E = 0); `(1,1,0)` gives `|rhs| = 2.06e-8`. Both deviations are toward nondegeneracy; no sign-off needed.

## 6. Binding stop lines
- Pinned statement false / missing input: none found (targets 1, 2 merged-input corollaries; target 3 inputs all merged, TL1 at τ derivable — F5).
- Two files cannot hold the three cases: not predicted (median 1,181 / 1,391; max-ratio 1,610 / 1,820 with the flag stated, 1,710 / 1,720 after moving the STCaseII datum to `TwistStep`'s head). Stop line 2,000 per file is enforced in 1b.
- Probe ≤ 400 lines: 332. Diff only the probe. C1 grep 0.

## 7. Observations (no RETURN)
- O1. (a)'s I-B uses κ = 1/4 (numerically true, Im m = 0.2666) which is not provable from the merged `BASelf_subord` bound (7.49e-4); the probe's F1 supersedes it with κ = 3/5000. Recorded in (a″) Findings rather than an (a′) section; changes no statement.
- O2. (a) row 12 says decay is needed for "the drift in case B"; with T.10 (a) the drift loses only `Bc^{−𝔠d}` (2 − 𝔠d ≥ 3/2), so decay is needed only for `Z_s` and `B̃₂`. Over-cautious, harmless.
- O3. For 1b (§3 (E)): the probe names `T2441_szII`, `T2441_wII`, `T2441_mII`, `T2441_zII` must become `private` or `TwistStep2_`/`TwistStep_`-stemmed in the merged files; `T2441_TL2e` stays in the probe (TL2e's pin text).
- O4. For 1b: the bootstrap is discharged in the instances at the a priori level Ξ = 32N⁴ (resp. 2(2/κ)²N⁴), where the conclusion is weaker than the a priori bound; this proves the hypotheses consistent (the purpose of the instance). Keeping also an instance with Ξ as a hypothesis (ticket item 5 wording) is advisable but not required.
- O5. New measurability lemmas (`twL3M`, `twEGM`, `twB1M`, `twB2M`) are predicted new in 1b; they count against the line budget.

## Verdict
- Target 1 `baTwistGridMart_holds`: **PASS** (3-line corollary compiled by the auditor).
- Target 2 `baTwistZeroMode_holds`: **PASS** (plan; inputs verified; instance point c₂ = (1,1,0)).
- Target 3 `BATwistStepFixed`, `baTwistStepFixed_caseI/II`: **PASS**; bootstrap form decided: `≺` at a deterministic level `Ξ : ℕ → ℝ` over `TimeIcc s t`, as in probe lines 41-50.
- Stage 1a + probe step: **PASS** — every deliverable met, no binding stop line hit. No dispatcher sign-off needed. 1b may start.
