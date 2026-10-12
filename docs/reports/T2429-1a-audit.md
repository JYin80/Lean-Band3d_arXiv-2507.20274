Auditor model: claude-opus-5-5
# T2429 1a-audit (design gate): section (a) and probe step (a″) of `T2429-prove.md`
Written Sun Oct 11 22:59 UTC 2026 (`date -u`). Detached worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2429-1a-audit` at `t/T2429` = `e1edb72`, merge-base `main` `0a8176c`. Scratch in `<scratchpad>/T2429/audit/`.

## 1. Branch, probe compile, axioms
```
$ git diff --stat main...t/T2429
 RBM3D/Probe/T2429Pins.lean | 119 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 119 insertions(+)
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2429Pins.lean
0
$ date -u; lake env lean RBM3D/Probe/T2429Pins.lean > probe.out 2>&1; echo exit=$?; date -u
Sun Oct 11 22:55:35 UTC 2026
exit=0
Sun Oct 11 22:55:41 UTC 2026
$ grep -ciE "error|warning" probe.out; wc -l < probe.out; grep axioms probe.out
0
37
'RBM.BA.BATwKDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Probe 119 lines (limit 400), only the probe file touched (sole writable, never merged).

## 2. Statement of the new pin T.1 (iii) `BATwKDecay` against the ticket's intended shape
```
$ sed -n 123,124p BA/TwistPins.lean | sed 's/ ∃ C : ℝ, 0 < C ∧//; s/ ∀ t : ℕ → ℝ.*$//' > p1   # twK_bound prefix, ∃ C removed
$ sed -n 55,56p Probe/T2429Pins.lean | sed 's/ ∀ ε₁ D.*$//' > p2; diff p1 p2 && echo IDENTICAL
IDENTICAL
$ grep -n "if 3 \*" BA/TwistPins.lean ; grep -n "ellT (sz.L n) (sz.lam n) v ≤" Probe/T2429Pins.lean
256:      (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) (p.1 : ℝ) ≤ (zdistInf d (sz.L n) (p.2.2.1 - p.2.2.2.1) : ℝ) then 1 else 0))
58:        ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) →
```
Remaining text (probe :57, :59): `∀ ε₁ D : ℝ, 0 < ε₁ → 0 < D → ∀ᶠ n in atTop, ∀ v, 0 ≤ v → v ≤ BAflowT0 sz z n → ∀ σ a c₁ c₂, … → ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ W_n^(-D)`.
Item by item against ticket target 2: prefix = `twK_bound` prefix (diff above); `∀ ε₁ D > 0` then `∀ᶠ n`; uniform in `v ∈ [0, t₀]`, `σ, a, c₁, c₂`; cut at `ellT (sz.L n) (sz.lam n) v` (model scale) in `zdistInf`, the form of `twDec` without its factor 3; bound `W^{-D}`, no `∃ C`. **Matches.**
Truth (checked against signatures, not docstrings): `twK_ba` gives `K̃ = W^{-d} Σ_{a'} Θ_{g₀,v}(a,a') M(c₂,a') M(a',c₁)`; `BAProp5` (`FlowPins:173-180`) gives `|Θ(0,a)| ≤ C·Bparam·exp(-c|a|_D/ellT L g₀ t)` with `g ≤ Λ` (eventual via `BAflow_lam0_window`, `Λ = 𝔡⁻¹`); `BAMB_decay_large` exponential in `|a-b|_D`; `zdistInf ≤ zdistD`; `ellT` nondecreasing in `g` and `g₀ ≤ lam` (forward F1 step). Split `|a-a'|_D ≥ X/2` or `|a'-c₁|_D ≥ X/2` (`X ≥ W^{ε₁} ℓ_v(g₀)`); `Bparam ≤ g₀⁻² + (L^d(1-t))⁻¹` is polynomial in `W` (`Bparam`, `Defs/Params.lean:36-37`; WO, `1-t₀ ≥ Im z/2`). The pin is true; numerics in §4 agree (effective `D` 4.97 / 5.28 / 6.53 at `n = 0,1,2`).
Instance (probe :68-115): `h : BATwKDecay 3` is a hypothesis only in the probe (it is this ticket's target; 1b replaces it by `baTwKDecay_holds 3`); at `sz0, zSeq, flow_sz0, ε₁ = 1/10, D = 2` every deterministic hypothesis is discharged and the witness `a = (2(n+1),0,0), c₁ = 0` is in the cut region for every `n`, `v ∈ [0,1/2]` (`half_lt_t0`). Nondegenerate.

## 3. Keyword list, name clashes, cone (rerun of `kw.sh` in this worktree; main snapshot by `git archive main`)
```
$ zsh kw.sh > kw.out; diff <(grep -v '^\$' <prover>/kw.out) <(grep -v '^\$' kw.out) && echo "kw: identical to prover output"
kw: identical to prover output
EKPins.lean: 151 EKPins_norm_Q_le 161 EKPins_norm_Theta_le 185 EKPins_norm_uKer_le 276 EKPins_Mss_shift … 452 EKPins_sum_ball_le
EKNonzero.lean: 50 EKNonzero_E 53 EKNonzero_E_pos 60 … 102 EKNonzero_projMat_comm 110 EKNonzero_Mss_shift 123 EKNonzero_projMat_mul_Theta 143 EKNonzero_Theta0_shift 149 EKNonzero_norm_Q_le 168 EKNonzero_coef 191 EKNonzero_norm_projMat_mul_uKer_le
EKNonzero_coef x1  EKNonzero_E x10  EKNonzero_E_pos x1  EKNonzero_Mss_shift x1  EKNonzero_norm_Q_le x1  EKNonzero_projMat_comm x1  EKNonzero_projMat_mul_Theta x1  EKNonzero_Theta0_shift x1
3:    (hsg : 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s) (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bo
28:  have hcoef := EKNonzero_coef hg hL hsg hst ht
58:          mul_le_mul_of_nonneg_left hcoef (by positivity)
RBM3D.BA.EKPins: transitive reverse cone 6: ['RBM3D', 'RBM3D.BA.EKNonzero', 'RBM3D.BA.EKSum', 'RBM3D.BA.NewKLKBA', 'RBM3D.BA.TwistPins', 'RBM3D.Chain.Step2Kern']
RBM3D.BA.EKNonzero: transitive reverse cone 1: ['RBM3D']
$ grep -nw EKPins_norm_Q_le BA/EKNonzero.lean; grep -nw "EKPins_norm_uKer_le\|EKNonzero_norm_projMat_mul_uKer_le" BA/TwistPins.lean | cut -c1-60
148:`EKPins_norm_Q_le`, `BA/EKPins.lean:151`). -/
192:/-- **T.10 (a)** (`‖Ũ∘A‖_∞ ≤ ((1-v)/(1-u)) ‖A‖_∞`; the one
206:/-- **T.10 (d)** (zero mode: `1 - v ≤ A g²/L²`, `Q^{(1)} =
$ for n in <9 new public names, stems>; do git grep -c "$n" main -- RBM3D RBM3D.lean | wc -l; done   # all 0
baTwKerA_holds main:0 baTwKerFar_holds main:0 baTwKerZero_holds main:0 BATwKDecay main:0 baTwKDecay_holds main:0 baTwistSrc1_holds main:0 baTwistSrc2_holds main:0 baTwistSrc4_holds main:0 baTwistSrc5_holds main:0 TwistKer_ main:0 TwistKer2_ main:0
$ for b in t/T2423 t/T2427 t/T2428; do git grep -lE '<same names>' $b -- RBM3D RBM3D.lean | wc -l; done   # t/T2430, t/T2431 do not exist
0 0 0
$ for t in T2423 T2427 T2428 T2430 T2431; do grep -m1 "Sole writable" docs/tickets/$t.md | grep -c "EKPins\|EKNonzero"; done
0 0 0 0 0
```
Fixed list (9 `private ` deletions): EKPins :151, :161, :185; EKNonzero :50, :53, :102, :110, :123, :143. All lie in the ticket's allowed set (EKPins three; EKNonzero helpers of :50-189 used by the `A`-form body). `EKNonzero_norm_Q_le` (:149) has the same signature as `EKPins_norm_Q_le` (checked, `EKPins:151-152` vs `EKNonzero:149-150`), so it needs no deletion; `EKNonzero_coef` (:168) is replaced by its `A`-form, and `hsg` occurs in the body only at the `hcoef` line (above). Cone count equals the ticket's (5 modules plus the root; EKNonzero root only).

## 4. Numerics rerun (preflight `inst.py`, `lines.py`, `inputs.sh`, copied to `audit/`)
```
$ date -u; python3 inst.py > inst.out 2>&1; echo exit=$?; date -u; diff <prover>/out.txt inst.out && echo "inst: identical …"
Sun Oct 11 22:58:02 UTC 2026
exit=0
Sun Oct 11 22:58:09 UTC 2026
inst: identical to prover's out.txt (29 lines)
$ python3 -I lines.py <audit worktree> > lines.out; echo exit=$?; diff <(grep -v '^\$' <prover>/lines.out) lines.out && echo "lines: identical"
exit=0
lines: identical
$ zsh inputs.sh > inputs.out; diff <prover>/inputs.out inputs.out && echo "inputs: identical"
inputs: identical
```
(`python3 -I inst.py` fails with `ModuleNotFoundError: numpy` because `-I` hides the user site; rerun without `-I` from the audit directory.) Selected lines of `inst.out` (verbatim):
```
[T10] L=4 lam=0.5: t0=0.4466 g0=0.3341 kappa=Im mS=0.5359<=Im mF=0.8019, Im zS=0.6641<=1:True Lambda=max(1,lam)=1 g0<=Lambda:True BASelf residual=1.1e-16
  (a) max over 4 charges, 4 (v,u): ||U||/((1-v)/(1-u)) = 1.0000 <= 1: True
  (d) u=1-1e-3 g0^2/L^2; A=1.000: v=0.99302 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=1.995 | A=2.866: v=0.98000 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=2.043 | A=5.000: …=2.098
[T1iii] n=2: … eps1=0.1: threshold W^eps1*ell=2.449 (ell_v(lam)=1.000); #a with zdistInf(a-c1)>=thr: 1603 of 1728; … max|K| on cut region=3.966e-26 <= W^-D (D=2.0): True
[T11] Cd=1.0: c_d=min(1/100,1/(30Cd))=0.01; c_d*Cd=0.0100 <= 1/30=0.0333; 1/5-c_d*Cd=0.1900 >= 1/6=0.1667 (slack 0.0233)
[W0] kappa=0.5 Lam=1/dd=10: r=0.00416, c3=r/2=0.00208; c3*W^eps1 >= D*ln W first holds at ln W=116.2 (the larger root; the smaller root is below ln W=1), W0~1e50
```
Spot checks of the script against Lean definitions: `ellT` (`Params:32-33`) and `Bparam` (`Params:36-37`, used in `Bctl`) are coded identically; `STConStInd` (`Induction/Defs:168-169`) is the `n0` test of `[T11]`.

## 5. The written argument, per target (against pins `TwistPins:193-209, 261-277` and their inputs)
| target | check | result |
|---|---|---|
| T.10 (a) `BATwKerA` | `EKPins_norm_uKer_le` (:185) has exactly the conclusion `‖BAuKer‖ ≤ (1-s)/(1-t)` under `0 ≤ s ≤ t < 1`; `‖Ũ *ᵥ A‖ ≤ ‖Ũ‖‖A‖` | sound |
| T.10 (b) `BATwKerFar` | `BAEKXiBall` (`EKPins:250-257`): hypotheses `g²/L² ≤ 1-t`, `1 ≤ Λ'`, `1 ≤ R ≤ Λ' ellT L g s`, ball `zdistD(ctr-b) ≤ R`, bound `C Λ'^2 (g²+|1-s|)/(g²+|1-t|)`; at `Λ' = W^ε, R = W^ε ℓ_v(g)` this is the pin's `C₁ W^{2ε}` term; far part `W^{-D}(u-v)/(1-u) ≤ W^{-D}(W-1)` from `W⁻¹ ≤ (1-u)/(1-v)`; needs `zdistD(-x) = zdistD x` (1b) | sound |
| T.10 (d) `BATwKerZero` | `BAProp8` (`FlowPins:217-223`) has no regime hypothesis (`0 ≤ t < 1`); `A`-form coefficient `(u-v)(g²+|1-u|)⁻¹L² ≤ (1-v)L²/g² ≤ A`; constant `2 + A C₀ E_k` | sound |
| T.1 (iii) | §2 | sound |
| T.11 (i) | exponent `W^d · (W^dη)⁻¹ · Bctl² = η⁻¹Bctl²`; `twK_bound` is per time sequence, uniformity on `TimeIcc` by the eventual-for-every-sequence argument | sound |
| T.11 (ii) | T.4 at `n = 3` via `STContractM` (`Contract:1011, 1069`), `baKsol_one`, `twSteps` conj 1-2: exponent 2 | sound (plan) |
| T.11 (iv) | `stSumTwoLoop` (`KDecay:1262-1271`) needs `𝔠d Cd ≤ 1/30`, gives `Bctl^{1/6}(etaT)⁻¹`; `stSumTwoLoop_exists` fixes `𝔠d = min(1/100, 1/(30Cd))`, compatible with `BATwFrame`'s `∃ 𝔠d ≤ 1/100`; exponent `γ + 1/6` | sound |
| T.11 (v) | `3X` split, `BATwKDecay` at `ε₁ = ε` and `twSteps` conj 4 at `τ' = ε` cut at the same `ellT (sz.L n) (sz.lam n)`; deterministic `N^C` off the event | sound (plan) |
F1 uses listed (prove :15): T.1 (iii) forward step only (`EMn2BA_ellT_mono_g`, `EMn2BA:591`); T.11 (v) same model scale on both sides; T.10 at the kernel's own `g`. No reverse comparison is used; consistent with ticket item 4.

## 6. Line prediction against the stop lines
`lines.out` (identical rerun): literal boundary `TwistKer.lean` 514 / 655 / 895, `TwistKer2.lean` 1,686 / **2,249** / 3,195; with the deterministic helpers D1-D3 in `TwistKer.lean` (ticket: boundary = deterministic vs `PrecL`, 1b may move helpers keeping `TwistKer → TwistKer2`) 1,086 / 1,320 / 1,740 and 1,114 / 1,584 / **2,350**. The probe states this (prove :73, :208) as the ticket requires. The 2,000 stop line binds 1b's files, not a prediction; under the moved boundary both central predictions are below 1,800. Not a stop-line hit.

## 7. Deliverables (ticket "Preflight (stage 1a) and probe step")
| item | status |
|---|---|
| (i) table: T.10 `C₁`, `A`-dependence of (d), T.1 (iii) `W₀(ε₁,D)`, T.11 exponents `2, 2, γ+1/6`, `𝔠d Cd ≤ 1/30`, every F1 use | met (prove :5-25) |
| (ii) one concrete instance, script and output | met; rerun identical (§4) |
| (iii) pin and instance compiled, exit 0 | met; rerun exit 0 (§1) |
| (iv) keyword list file:line, name-clash grep, cone count on `main` | met; rerun identical (§3) |
| (v) input of each T.11 item (file:line) | met; `inputs.sh` rerun identical |
| (vi) predicted lines per file vs stop line | met (§6) |
| stop rule (pin false / input outside TP and merged) | not hit |
| paper delta | T2429a-1 (T.1 (iii): `∀ᶠ n`, `zdistInf`, model-scale `ℓ`) covers the only new Lean/paper statement difference |

## 8. Observations (no RETURN)
- O1. `TwistKer2.lean` high-column prediction 2,350 > 2,000 even with D1-D3 moved; the largest row is P5 (T.11 (v), fixed estimate, no twin). The ticket's clause "a third file is named by amend" stays available to the dispatcher; 1b must stop at 2,000 in any file.
- O2. `BATwFrame` is existential in `𝔠d` per target; T.11 (iv) chooses `min(1/100, 1/(30Cd))`. TL2d must reconcile the `𝔠d` of the targets it combines (outside this ticket).
- O3. Section (a) restates `‖Ξ‖ ≤ (u-v)/(1-u)`; the `zdistD` symmetry and the `zdistInf` triangle inequality are not on `main` and are 1b work (stated in (a″) (v)).

## Verdict
**T2429 stage 1a (design gate): PASS.** All six deliverables met, numerics reproduce verbatim, probe compiles (exit 0, standard axioms), no binding stop line hit. No dispatcher sign-off needed.
