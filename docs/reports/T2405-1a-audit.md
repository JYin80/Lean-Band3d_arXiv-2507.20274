Auditor model: claude-opus-5-5

# T2405 1a-audit round 2 (design gate, after one rule-(B) repair under Amend 1): Sun Oct 11 03:50:01 UTC 2026

Inputs: ticket `docs/tickets/T2405.md`; Amend 1 `docs/tickets/T2405-amend-1.md` (binding, D1-D4); sections (a) and (a′) of
`docs/reports/T2405-prove.md` (154 lines); round-1 list of this file. Branch `t/T2405` = a34b8d9, `git diff --stat main...t/T2405`: empty
(no Lean, as expected). Scratch: `scratchpad/T2405/`.

## 1. Rerun of the (a′) scripts (verbatim output)
```
$ python3 -I aprime.py
D2  kappa/2<=Im mE on |E|<=2-kappa: violations 0  min(Im mE - kappa/2) = 0.0005
D1  kappa<=Im mE with |E|>2: counterexamples 0
Ward step: violations 0
constants: max |generic - band| = 0
BA conv constant K_c: max (1-u)/|1-xi| = 0.9999960659888103
primed, delta0=kappa/2 : 0<lam True lam<=1/dd True kp<=Im m(E) True 0<=u<1 True 0<=D True 0<=ell<=L True |G-M|=u/(1-u)=0.03226 <= delta0=0.05000 True | dom |E|<=2-kappa and kappa/2<=Im m: True
unprimed via kappa'=kappa/2, delta0=kappa/4 : 0<lam True lam<=1/dd True kp<=Im m(E) True 0<=u<1 True 0<=D True 0<=ell<=L True |G-M|=u/(1-u)=0.01587 <= delta0=0.02500 True | dom |E|<=2-kappa and kappa/2<=Im m: True
$ python3 band_corollary.py | grep -E "G-M|l="          (diff vs band.py: only u=1/64 and the delta0 label)
||G-M||_max = 0.015873015873015817 = u/(1-u) = 0.015873015873015872  delta0=kap/4= 0.025  Im G= 1.0158730158730158  2 Im m= 2.0
l=0.5: J=0.04591  C needed: bound1 1.936, bound2 0.04655; proof constant C=2K_conv+2Cs(4+C_K)+Cs*C_T = 138.3  ok=True
l=2.0: J=0.04591  C needed: bound1 1.936, bound2 0.04451; proof constant C=2K_conv+2Cs(4+C_K)+Cs*C_T = 138.3  ok=True
$ python3 -I cone.py
RBM3D.Induction.NewKLK reverse cone: modules 83 lines 93804 LWExpCert* 6
RBM3D.Chain.Step2Gen reverse cone: modules 54 lines 45724 LWExpCert* 0
RBM3D.Induction.Step2K2 reverse cone: modules 99 lines 116247 LWExpCert* 6
Step2Gen in closure(NewKLK imports): False
NewKLK in closure(Step2Gen imports): False
importers of Chain.NewKLKGen: 0 module exists: False
direct importers of NewKLK: ['RBM3D.Induction.NewKLKL', 'RBM3D.Induction.OptL2a', 'RBM3D.Induction.Step5Kit', 'RBM3D.Induction.Step5Pins']
$ python3 -I layout.py | tail -4
(A) total 768
(B) total 483
(A)-(B) = 285  ticket rule: (B) only if (A)-(B) > 150 -> (B)
stop line 900: (A) margin 132  (B) margin 417
```
All outputs match (a′) C2/C5 verbatim. (`band_corollary.py` needs numpy, so it ran without `-I`.)

## 2. Independent checks
(a) Cited sources (`sed -n <line>p`, cut at 120 chars):
```
Induction/ConArgDet.lean:746   theorem half_le_mE_im {E κ : ℝ} (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) :
BA/CombesThomas.lean:562       theorem baPropM_holds (d : ℕ) (Λ κ : ℝ) : BAPropM d Λ κ := by
BA/MFixedPoint.lean:432        def BAReal (g κ E : ℝ) (m : ℂ) : Prop := BASelf d L g (E : ℂ) m ∧ κ ≤ m.im
BA/KTreeRep.lean:1699          theorem baKsolve : ∀ d, BAKsolve d := by
BA/KWardIneq.lean:255          private theorem KWardIneq_theta_row_le (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
BA/KWardIneq.lean:265          private theorem KWardIneq_theta_col_le (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
BA/KKernel.lean:124            theorem BAK_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
Loop/GLoopFlow.lean:64         theorem ztOf_im (m : ℂ) (E t : ℝ) : (ztOf m E t).im = etaOf m t := by
Defs/Semicircle.lean:42        theorem mE_im (E : ℝ) : (mE E).im = Real.sqrt (4 - E ^ 2) / 2 := by simp [mE]
Defs/Semicircle.lean:63        theorem norm_mE {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1 := by
Defs/Semicircle.lean:182       theorem zt_im (E t : ℝ) : (zt E t).im = (1 - t) * (mE E).im := by
Defs/Block.lean:58             theorem SB_transpose : (SB d L g)ᵀ = SB d L g := SB_isSymm d L g
Defs/Block.lean:118            theorem sum_norm_SB_row (hL : 3 ≤ L) (a : Zd d L) : ∑ b, ‖SB d L g a b‖ = 1 := by
Propagator/Prop5Hold.lean:784  theorem prop5Decay_holds (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := by
Induction/NewKLK.lean:201      private theorem nkl_SB_support (g : ℝ) {a b : Zd d L} (h : SB d L g a b ≠ 0) :
Induction/NewKLK.lean:700      private theorem nkl_ward_K (n : ℕ) {E u : ℝ} (hE : |E| ≤ 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
Induction/NewKLK.lean:623      private theorem nkl_ward_L [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
Induction/NewKLK.lean:740      private theorem nkl_gres_blockMat_true {d L W : ℕ} [NeZero L] [NeZero W]
Chain/Carrier.lean:205           K := fun n t {_k} σ a => STKloop sz n (E n) t σ a
BA/FlowPins.lean:327             S := fun n => 1
Induction/DuhamelII.lean:42    open private emn2Exp2_exists_CR from RBM3D.Induction.EMn2Exp2
```
`sum_norm_SB_row` needs `3 ≤ L`: available as the field `Sizes.three_le_L` (`Defs/Sizes.lean:138-145`). The pin text
`STNewKLKAtgL` (`Chain/Step2Gen.lean:889-902`) has exactly one energy premise `|E| ≤ 2 - κ →`, so the primed pin of D1 is a one-binder change.
(b) F7 against the merged band proof: `nkl_at` uses `nkl_conv_P` once (`NewKLK.lean:1057`), to produce `hK1`
(`:1054-1058`: `∑_b ‖SΘ p b‖ * P(|b-q|) ≤ K * P(|p-q|)`, `K = C₁Cs·CT/(1-u) + Cs/(1-u)`), which is F7 with `K_c = C₁CsCT + Cs`.
So F7 is the right interface, and `nkl_conv_P` is needed only on the band side (it is in (iv)'s band list).
(c) F9 against the merged definitions: `STLM … := loopFine d (sz.L n) (sz.W n) H (zt E u) σ a` (`Step2Defs.lean:60-62`); `STGMM … :=
Gres H (zt E u) true x y - (if x = y then mE E else 0)` (`:146-148`); `BALloop … := loopFine … (ztOf (BAmF …) (E n) t) σ a` (`FlowPins.lean:264-266`).
The diagonal-only GMM clause is what `nkl_ward_LKM`'s `hdiag` step reads (`NewKLK.lean:771-785`). F9 is C1-clean.
(d) Stop line, with the double count removed (the (A) budget copies `nkl_conv_P` generically (72 lines), which (b) shows is not needed):
```
$ python3 -c "A=768;B=483;print(A-72, B-29, (A-72)-(B-29), 900-(A-72))"
696 454 242 204
```
(e) Names on `main` 3e72137 (the ticket's sibling-scan grep; (a′) does not show it):
```
$ git grep -nE "STNewKLKAtgL'|STNewKLKgL'|stNewKLKAtgL'?_of|stNewKLKgL'?_of|NewKLKGen" main -- RBM3D RBM3D.lean
(no output)
```

## 3. Round-1 "Required for resubmission" and Amend 1

| # | requirement | (a′) | status |
|---|---|---|---|
| 1 | (i) layout, both predictions, cone by script | C5: cone.py, layout.py; (A) 768, (B) 483; zero importers | met (see L below) |
| 2 | (iii) statements of targets 1, 2; `rfl` failures + alternatives; band re-derivation | C3: primed pins as a one-binder diff; target 1 (`δ₀ = κ/2`, `C` formula), target 2, 2′ (D1′ corollary); Fail 1-4 with alternatives; band via 2′ + `bandStep2_STNewKLK` | met |
| 3 | (iv) private names to open, with reasons | C5: 10 generic-side + 7 band-side names, spans and reasons (per group) | met |
| 4 | (v) lines against stop line 900 | (A) 768 (my correction: 696), (B) 483 | met; no stop line hit |
| 5 | row 2 restated; `nkl_ward_K`, `zt_im`, row-7 BA source | C1 rows 1, 2 per D1/D2; C4 table with all three | met |
| 6 | row 8 vs T2404 (HK) | C1 last bullet, one line, per Amend D3 | met |
| 7 | dispatcher decision on D3 | Amend 1 D1/D1′ | resolved |
| D2 | false band claim dropped | C1 rows 1, 2; aprime.py D2: 0 violations | met |
| D4 | design-gate items override CLAUDE §4 generic format | C3-C5 | met |

Target-level reading of (a′):
- **Target 1 `stNewKLKAtgL'_of`**: hypotheses F5-F9 are stated through `mk` only (`S`, `m`, `K`, `LM`, `GMM`): no `‖m‖ = 1`, `M = mI`,
  `mSigma`, band `Theta`. The premise `κ ≤ Im m` is the `BAReal` datum. The Ward step `Im G_xx ≤ Im m + κ/2 ≤ 2 Im m` closes
  (aprime.py "Ward step: violations 0"). The constant agrees with `nkl_at:1001` (difference 0). PASS.
- **Target 2 / 2′**: `STNewKLKgL'` by target 1 at each `κ, 𝔡`. The unprimed `STNewKLKgL` comes from the primed pin at `κ/2` plus `dom_κ`
  (band: `Ind.half_le_mE_im`, hypotheses `0 ≤ κ`, `|E| ≤ 2-κ`, checked above). Both instance premise sets hold (aprime.py last two lines). PASS.
- **Target 3 (C1)**: every F-row has a merged source or an owing T3-BA row (C4); none is proved here, as Amend 1 "BA reading" requires. PASS.
- **Target 4**: `stK2decay_holds` is the only public declaration of `Step2K2.lean` (round 1 §2(c)). PASS.
- **Target 6**: band `example` route through 2′; BA statement-level `example` over a private `Step2Mat` extending `baFM` (`FlowPins.lean:322-328`). PASS (plan).

## 4. Layout (L)
(a′) C5 reports "(B) by the ticket's rule (285 > 150); (A) feasible". Amend 1 is binding and fixes **layout (A)**: D1 says the
primed pins are "stated in the new file (layout (A))", and D1′ says "`NewKLK.lean` is not edited, so G1 holds by construction". The amend
overrides the ticket's 150-line rule. (A) fits the stop line: 768 by (a′), 696 after §2(d), against 900. Under (A) the merge rebuilds no
certificate module (zero importers, §1). So stage 1b runs **layout (A)**. Its sole writable files are `RBM3D/Chain/NewKLKGen.lean`
(new) and one import line in `RBM3D.lean`; `NewKLK.lean` is not edited. The (iv) list in C5 applies. No dispatcher decision is needed,
because Amend 1 already made it. The measured gap (242-285 lines) is recorded for the dispatcher as information only.

## 5. Observations (no RETURN)
- O1. The (B) selection in (a′) C5 is superseded by Amend 1 (§4). It changes no statement, hypothesis or stop-line outcome.
- O2. The (A) budget counts a generic copy of `nkl_conv_P` (72 lines) that F7 makes unnecessary (§2(b)). The estimate is conservative.
- O3. The BA statement-level example needs `import RBM3D.BA.FlowPins` (for `baFM`) in the new file, beyond the ticket's two imports.
  The new file has zero importers, so the cone and the lane are unchanged. 1b should list the import.
- O4. In target 2, F5, F6 and F9 must also be quantified `∀ κ 𝔡 > 0` (their premise Π mentions `κ, 𝔡`). (a′) C3 states this only for F7, F8.
- O5. The name-clash grep was missing from (a′). I ran it (§2(e)): no clash on `main`. The 1b report must show it again.
- O6. Paper-delta candidates T2405a (S = 1 at BA, diagonal `STthetaOpg`) and T2405b (primed premise `κ ≤ Im m` replacing `|E| ≤ 2-κ`,
  `lem:newKLK` `3_5:371-378`) cover the statement differences planned so far.

## 6. Verdict: PASS (stage 1a design gate, round 2); no dispatcher sign-off needed
Every stage-1a deliverable (i)-(v) is present, and the round-1 items 1-7 are met or resolved by Amend 1. No binding stop line is hit:
(A) is 768 (696 corrected), under 900. Stage 1b (`prover-hard`) proceeds in **layout (A)** per Amend 1 D1/D1′ (§4), with the statements
of (a′) C3, hypotheses F5-F9, and the opened names of C5 (iv).
