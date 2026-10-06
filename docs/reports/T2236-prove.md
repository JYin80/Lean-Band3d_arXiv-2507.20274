Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 01:06:00 UTC 2026

### (i) Exponent table
Notation: `N = sz.size n = (W L)^d`, `B = Bctl = W^{-d}B_{t,0}`, `η = etaT = (1-t) Im m(E)`, `X_{a₁} = 𝓛^{(1)}_{σ₁,a₁} - m(σ₁)`, `D = (𝓛-𝒦)^{(2)}`, `A = 𝓛^{(2)}_{(-,+),(a,a₂)} ≥ 0`, `K' = 𝒦^{(2)}_{(-,+),(a₃,b)}`. All `≺` are `∀τ,D>0`, so `N^τ` losses are free; "slack" is in the exponent of `B` or `η⁻¹`.

| quantity | value / bound used | constraint | slack / source |
|---|---|---|---|
| `t < 1`, `|E| ≤ 2-κ` | from `t ≤ lemT z`, `Im z>0` | needed for `G_t` to exist, `η>0` | `st5_t_lt_one` Step5Kit:192, `st6_flowE_le` Step6Kit:535 |
| `η⁻¹ ≤ N` (eventually, all `u ≤ lemT z`) | `ExpAvg:631` (`1-lemT ≥ N^{-1+ε}/4`, `Im m ≥ √(2κ)/2`) | envelope `‖G_t‖ ≤ η⁻¹ ≤ N` | instance below: True at `tInst`, `tEnd` |
| `‖𝓛^{(k)}‖ ≤ η^{-k}` | `norm_Lloop_le` GLoopFlow:700 | pointwise in `ω` | `k ≤ 3`: `|X| ≤ N+1 ≤ 2N`, `|𝓛^{(2)}| ≤ N²` |
| `B ≥ 1/N` | second term of `Bparam` (Params:36): `B ≥ W^{-d}(L^d(1-t))⁻¹ = (N(1-t))⁻¹ ≥ N⁻¹` for `0≤t<1` | lower bound on every target `ζ`, so `N^{-D}` errors are absorbed | slack `N^{-3}` for `B³` |
| `B ≤ 2` (eventually) | `W^{-d}/(g²+1-t) ≤ (g²W^d)⁻¹ ≤ 1` (`STAI ≥ 1`, Step5Kit:`st5_eventually_A_ge_one`), `1/(N(1-t)) ≤ 1/(Nη) ≤ 1` | `|𝒦^{(2)}| ≤ N·B ≤ 2N` (deterministic `Prec` at `τ=1`, `st6_prec_det_iff` Step6Kit:81) | envelope of `D`: `|D| ≤ N²+2N ≤ 3N²` |
| `≺→𝔼` loss, `I₁` | `|XD| ≤ 6N³`; `𝔼|XD| ≤ N^τ B³ + 6N^{3-D}` | `6N^{3-D} ≤ N^{-3} ≤ B³` | `D = 7`: `6N^{-4} ≤ N^{-3}` iff `N ≥ 6` (`N ≥ 2097152` at `sz0`) |
| `≺→𝔼` loss, `I₄₁` | `|XD'|·A ≤ 6N⁵`; error `W^dΣ_{a₁a₂a₃}S S·6N^{5-D} = 6N^{6-D}` (`Σ_{a₁a₂a₃}SS = L^d`, `W^dL^d = N`) | `6N^{6-D} ≤ N^{-3} ≤ η⁻¹B³` | `D = 10`: `6N^{-4} ≤ N^{-3}` |
| `𝔼X_{a₁}` | `≺ B²` | `STExpAvgAt` Step6Pins:177 = `stImproveExpAver_holds` ExpAvg:879 (premises `LWAvgLaw`, `STLK` = those of `LWExpI1`) | `σ₁=-`: `ST_Lloop_one_false` Step2Iterate:1218 |
| `X_{a₁}` pointwise | `≺ B` | `LWAvgLaw` (`STLK` `k=1` has `𝒦^{(1)}=m`, `KLK_one` KLTree:206) | — |
| `𝒦^{(2)}` | `≺ B^{k-1} = B` | `STKbound` (`stKbound_of_flow` KLFinal:302; all `τ∈[0,1)`, all charges incl. `(+,+)`) | — |
| `D` | `≺ B²` | `STLK` `k=2` | — |
| `|𝓛^{(1)}|` | `≺ B⁰ = 1` | `STLmax` `k=1` | — |
| `I₁` (target `B³`) | `|𝔼X||𝒦^{(2)}| ≺ B²·B`; `𝔼|X D| ≺ B·B²`; `Σ_{a₁}S^B_{a₁b} = 1` (`sum_SB_row` Block:108, `SB` symmetric `sbKernel_neg`) | exponent `3 = 2+1 = 1+2` | slack 0 (exact), no `STLmax` needed |
| `I₄₁` `T_a = W^dΣSS 𝔼[X A D']` (`D' = (𝓛-𝒦)^{(2)}_{(a₃,b)}`) | `≤ N^τ B³·W^dΣ_{a₂}𝔼A`, `A ≥ 0`, `Σ_{a₁}S=Σ_{a₃}S=1` | `W^dΣ_{a₂}A = η⁻¹ Im 𝓛^{(1)}_{+,a}` (Ward), `𝔼|𝓛^{(1)}| ≺ 1` | `B³·η⁻¹`, slack 0 |
| `T_{b1} = 𝔼X·𝒦_{(a,a₂)}·W^dΣSS K'` | `|𝔼X| |𝒦| ≺ B²·B` | `W^dΣ_{a₃}|K'| ≺ η⁻¹` (`STKward` `k=2`: `(W^dη)⁻¹B^0`, KLFinal:308) | `B³η⁻¹`, slack 0 |
| `T_{b2} = W^dΣSS 𝔼[X D_A] K'` | `𝔼|XD_A| ≺ B³` | same `STKward` | `B³η⁻¹`, slack 0 |
| `K'` summed over its first label | `𝒦_{(-,+),(a₃,b)} = 𝒦_{(+,-),(b,a₃)}` by `KLK_rotate` KLUnique:604 (`t∈[0,1)`, `|E|<2`, `3 ≤ L`) | `STKward` sums the last label | `STKward` applies at `σ=(+,-)` |
| `η⁻¹` vs `(1-t)⁻¹` (LW-14b) | `√(2κ)/2 ≤ Im m ≤ 1` ⇒ `(1-t)⁻¹ ≤ η⁻¹ ≤ √(2/κ)(1-t)⁻¹` (`st6_mE_im_ge` Step6Kit:544; `mE_im`) | `√(2/κ) = 4.47` at `κ=1/10` | exists; constant only |
| `B³` vs `B^{5/2}` (LW-14b) | `B³ ≤ B^{5/2}` iff `B ≤ 1`; `B ≤ W^{-2𝔡} + 4N^{-ε}` (`lam_sq_mul_pow_ge` Defs/Sizes:193: `lam²W^d ≥ W^{2𝔡}`; `1-t ≥ N^{-1+ε}/4`, ExpAvg:631-650) | `B<1` eventually | at `sz0`: `B = 3.3·10^{-5}` (n=0) |
| reduction (target 2) | `‖𝔼LWE‖ ≤ ‖𝔼LWcut₁‖+‖𝔼LWcut₂‖ ≤ 2 N^τ ζ`; `StochDomAt.add` StochDomAt:427, `precomp_param` :335 | same index set `lam²/L^d ≤ 1-t`, same `ζ = (1-t)⁻¹B^{5/2}` | slack: constant 2 absorbed by `N^τ` |

Inspection items asked by the ticket:
- (i) Normalisation: `Eblk` has `W^{-d}` (GLoop:55), so `𝓛^{(3)} = W^{-3d}Σ_{α∈a₂,x,y}GGG` and `W^{-2d}Σ_{x,y,α}GGG = W^d 𝓛^{(3)}`; hence by this count `LWcut` (LWPins:211) equals the LHS of `(eq:ELW_term)` with factor 1, not `W^{-d}` (the ticket's remark is not reproduced); consistent with `I₁ = Σ S^B tr(ǦE_{a₁})·𝓛^{(2)}` (`B:39`), `𝓛^{(2)}_{(-,+)} = W^{-2d}Σ|G_{xy}|²`.
- (iii)(2) `sum_gloop_ward_last` (ConArgDet:268) is `(2iη)Σ_b 𝓛⟨+..-⟩ = W^{-d}(𝓛_+ - 𝓛_-)`, last charge `-`. The pin needs `(-,+)` with the second label summed: apply it at `z̄` (`Gres H z false = green H z̄`, `cad_Gres_false` ConArgDet:145), giving `Σ_{a₂}𝓛^{(2)}_{(-,+),(a,a₂)} = (𝓛_+-𝓛_-)/(2iW^dη)`. The model is complex Hermitian (`Xentry`, FineModel:105), so `𝓛_{(-,+),(a,b)} ≠ 𝓛_{(-,+),(b,a)}` in general (script: `max|L2-L2ᵀ| = 2.8e-3`); no transposition symmetry is used. `A ≥ 0` is `Σ_{x∈a,y∈a₂}W^{-2d}|G^+_{yx}|²` (`G^- = (G^+)ᴴ`).
- (iii)(1) `t<1`, `|E|<2` as in the first rows. (iii)(4) `LWExpI1` at `(+,+)` needs only `STKbound` `k=2`, `STLK` `k=2`, `STExpAvgAt`; no `STLmax`.
- Pin `LWExpI41` has no factor `m` (paper `I₄₁ = m W^d Σ…`): `|m(σ)| ≤ 1`, so the pin's bound is the paper's bound.

### (ii) One concrete nondegenerate instance
`d=3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`; Sizes:260), `z0 n = 1/2 + i N^{-4/5}` (Defs:413), `t = tInst = 1/16` (Defs:440) and `t = tEnd = lemT(z0 n)` (Defs:626); merged `flow_z0`, `tInst_range`, `tEnd_range`. Hypotheses checked: `0≤t≤lemT`, `η⁻¹≤N`, `B≥1/N`, `B<1`, `B³≤B^{5/2}`, `N ≥ 12`.
```
$ cd $SP/T2236 && python3 pre.py        # mpmath, 60 digits
n  N  t-case  t<=lemT  eta^-1<=N  Bctl>=1/N  Bctl<1  log10(Bctl)  Bctl^3<=Bctl^2.5
0 2.097e+6 tInst True True True True -4.481 True
0 2.097e+6 tEnd True True True True -0.7614 True
1 5.498e+11 tInst True True True True -9.002 True
1 5.498e+11 tEnd True True True True -1.702 True
2 8.125e+14 tInst True True True True -11.64 True
2 8.125e+14 tEnd True True True True -2.25 True
5 2.13e+20 tInst True True True True -16.16 True
5 2.13e+20 tEnd True True True True -3.179 True
N0 = 128 ^3 = 2097152 >= 12: True
n = 0  W^3*Bctl = 1.0830556  16/15 = 1.0666667
n = 5  W^3*Bctl = 1.0667438  16/15 = 1.0666667
n = 50  W^3*Bctl = 1.0666668  16/15 = 1.0666667
n = 500  W^3*Bctl = 1.0666667  16/15 = 1.0666667
```
External premises `LWAvgLaw`, `STLK`, `STLmax` (other gates' pins) stay hypotheses of the examples. Limit computation: at `tInst`, `W^d B → 1/(0+15/16) = 16/15` (last four lines), so `B ~ 1.07 W^{-3} → 0`: the bounds `B^k` are nontrivial (`B<1`), and `B ≥ 1/N` holds with room (`log10 B = -4.5` vs `log10(1/N) = -6.3` at n=0).

Evidence for the pins on a complex Hermitian Gaussian sample (`d=3, L=3, W=2`, `lam=1/2`, `E=0`; `E|X_xy|² = W^{-d}S^B`, off-diagonal real/imag parts variance `S/2`, as `PF`/`Xentry`), identities exact, ratios Monte Carlo (600 samples, evidence only):
```
$ cd $SP/T2236 && python3 mc.py
SB row sums 0.9999999999999999 1.0000000000000002 symmetric True
Ward  max|sum_b L2[a,b] - (L1+ - L1-)/(2i W^d eta)| = 1.1102416645531043e-16
Ward' (first label summed) max|sum_b L2[b,a] - same| = 1.665335681376521e-16
max|Im L2| = 6.982604984414756e-19  min Re L2 = 0.00025727567968664584  max|L2-L2^T| = 0.0027776049631559312 (complex Hermitian: not symmetric)
t=0.5: Bctl=1.7593e-01 Bctl^3=5.445e-03 eta=0.500  max|E X|/Bctl^2=0.136  max|I1|/Bctl^3=0.068  max|I41|/(eta^-1 Bctl^3)=0.025  (N_samples=600)
t=0.9: Bctl=4.0344e-01 Bctl^3=6.567e-02 eta=0.100  max|E X|/Bctl^2=0.045  max|I1|/Bctl^3=0.031  max|I41|/(eta^-1 Bctl^3)=0.009  (N_samples=600)
```
`SP` = the session scratchpad (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`).

§29 checklist: (1) `0≤t≤lemT z` unchanged, `t<1` by `st5_t_lt_one`. (2) `LWExpI1`, `LWExpI41` have no boundary; `LWCutExp` carries `lam²/L^d ≤ 1-t` as `LWtermEXP` does. (3) no `L^d ≤ W^K`: only `W^dL^d = N`, `L^d ≤ N`. (4) `∀ n` premises as in `LWtermEXP`. (5) per `(σ,a)`, uniform over the index set (deterministic left sides: `Prec` ⇔ pointwise `∀ index`, `st6_prec_det_iff`). (6) no parameter lower bound beyond `WO` (`STAI ≥ 1`, eventually). (7) scale `N = sz.size n`, control `sz.Bctl n (t n)`. §64 (4): no grid lift.

Mathematical route confirmed: `E[X·𝓛^{(2)}] = 𝔼X·𝒦 + 𝔼[XD]`, `T_a, T_{b1}, T_{b2}` for `I₄₁` (the paper's three groups, `B:63-72`); the `≺→𝔼` step is `𝔼|Y| ≤ N^τζ + sup|Y|·P(bad)` with `ζ ≥ N^{-3}`, valid because `Y` is bounded (`norm_Lloop_le`) and measurable (loops are continuous in the sample: `continuous_gloop_HflowBlock_sample`, used at `k=1` in ExpAvg:272; the `k=2,3` use is the same lemma at a longer `WF` index).

### Verdicts
- Target 1 (vocabulary `LWCutExp`, `LWExpI1`, `LWExpI41`, `LWExpG5`): PASS (check-file definitions compile; every hypothesis set is satisfiable at the instance).
- Target 2 (`lwTermEXP_of_cut`): PASS.
- Target 3 (`lwExpI1_holds`): PASS (exponent `B³` closes exactly).
- Target 4 (`lwExpI41_holds`): PASS (`η⁻¹B³` closes exactly via Ward `(WI_calL)` at `z̄` and `STKward` through `KLK_rotate`).
- Target 5 (instances at `sz0, z0, tInst`, and `inst_LWtermEXP`): PASS.

## (b) Script output (stage 1b, `prover-hard` role run as Sonnet; report written Tue Oct  6 01:36:55 UTC 2026; commit f282b96 on t/T2236)

```
$ date -u
Tue Oct  6 01:34:29 UTC 2026
$ git log -1 --format="%h %s" && git diff --stat main...t/T2236
f282b96 T2236: LW-14a lem:LWterm_EXP part a (LWE -> LWcut reduction, I1, I41)
 RBM3D/Graph/LWExpTerm.lean | 1256 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    1 +
 2 files changed, 1257 insertions(+)
$ wc -l RBM3D/Graph/LWExpTerm.lean; grep -c "sorry\|admit\|native_decide\|axiom" RBM3D/Graph/LWExpTerm.lean
    1256 RBM3D/Graph/LWExpTerm.lean
0
$ lake build RBM3D.Graph.LWExpTerm | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3852 jobs).
$ lake env lean axioms.lean
'RBM.Gauss.Sizes.lwTermEXP_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI41_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm_prec_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm_inst_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm_inst_I1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm_inst_I41' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean verify.lean (check-file section 2 copied into T2236Check; Iff.rfl for the 4 defs, @name for the 3 theorems); exit code:
exit=0
$ lake env lean precheck.lean  (import RBM3D; import RBM3D.Graph.LWExpTerm; #assert_rbm_axioms; shown: exit code, `head -2`, `tail -1` of the log)
exit=0
axiom audit: 6879 theorems, 2336 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
non-vacuity certificates: 0 of 147 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would 
$ grep (name clash, outside the file and the registry)
LWCutExp: 0
LWExpI1: 0
LWExpI41: 0
LWExpG5: 0
lwTermEXP_of_cut: 0
lwExpI1_holds: 0
lwExpI41_holds: 0
lwExpTerm_prec_integral: 0
lwExpTerm_inst_cut: 0
lwExpTerm_inst_I1: 0
lwExpTerm_inst_I41: 0
$ lake build | tail -1   (full library, run after the commit)
Build completed successfully (4039 jobs).
```

check-file section 2 copied by script (a python slice between `namespace T2236Check` and `/-! ## Section 3`) into `verify.lean`, then appended (the file's last 8 lines):
```
theorem pinIff_cut (d : ℕ) : LWCutExpPin d ↔ LWCutExp d := Iff.rfl
theorem pinIff_I1 (d : ℕ) : LWExpI1Pin d ↔ LWExpI1 d := Iff.rfl
theorem pinIff_I41 (d : ℕ) : LWExpI41Pin d ↔ LWExpI41 d := Iff.rfl
theorem pinIff_G5 (d : ℕ) : LWExpG5Pin d ↔ LWExpG5 d := Iff.rfl
example (d : ℕ) : LwTermEXPOfCutPin d := @lwTermEXP_of_cut d
example (d : ℕ) : LWExpI1Pin d := @lwExpI1_holds d
example (d : ℕ) : LWExpI41Pin d := @lwExpI41_holds d
end T2236Check
```

Statements extracted by script (`extract.py <name>`: the file's text from the `def`/`theorem` line to `:= by`):
```
RBM3D/Graph/LWExpTerm.lean:143: theorem lwExpTerm_prec_integral {d : ℕ} (sz : Sizes d) {V : ℕ → Type} (X : ∀ n, V n → sz.SeqΩ → ℂ)
RBM3D/Graph/LWExpTerm.lean:144:     (R : ∀ n, V n → ℝ) {Kenv Kf : ℝ} (hsz : sz.SizeTendsto)
RBM3D/Graph/LWExpTerm.lean:145:     (henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
RBM3D/Graph/LWExpTerm.lean:146:     (hfloor : ∀ᶠ n in atTop, ∀ v, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v)
RBM3D/Graph/LWExpTerm.lean:147:     (hprec : sz.Prec (U := V) (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v)) :
RBM3D/Graph/LWExpTerm.lean:148:     sz.Prec (U := V) (fun n v _ => ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v _ => R n v) := by

RBM3D/Graph/LWExpTerm.lean:286: theorem lwTermEXP_of_cut (d : ℕ) : LWCutExp d → LWtermEXP d := by

RBM3D/Graph/LWExpTerm.lean:535: theorem lwExpI1_holds (d : ℕ) : LWExpI1 d := by

RBM3D/Graph/LWExpTerm.lean:1119: theorem lwExpI41_holds (d : ℕ) : LWExpI41 d := by

RBM3D/Graph/LWExpTerm.lean:52: def LWCutExp (d : ℕ) : Prop :=
RBM3D/Graph/LWExpTerm.lean:53:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
RBM3D/Graph/LWExpTerm.lean:54:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
RBM3D/Graph/LWExpTerm.lean:55:       ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
RBM3D/Graph/LWExpTerm.lean:56:         STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
RBM3D/Graph/LWExpTerm.lean:57:         STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
RBM3D/Graph/LWExpTerm.lean:58:         Prec sz (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) //
RBM3D/Graph/LWExpTerm.lean:59:             sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
RBM3D/Graph/LWExpTerm.lean:60:           (fun n p _ => ‖∫ ω, LWcut sz n (STflowE z n) (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(sz.seqP)‖)
RBM3D/Graph/LWExpTerm.lean:61:           (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

RBM3D/Graph/LWExpTerm.lean:66: def LWExpI1 (d : ℕ) : Prop :=
RBM3D/Graph/LWExpTerm.lean:67:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
RBM3D/Graph/LWExpTerm.lean:68:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
RBM3D/Graph/LWExpTerm.lean:69:       ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
RBM3D/Graph/LWExpTerm.lean:70:         LWAvgLaw sz (STflowE z) t → STLK sz (STflowE z) t →
RBM3D/Graph/LWExpTerm.lean:71:         Prec sz (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)))
RBM3D/Graph/LWExpTerm.lean:72:           (fun n p _ => ‖∑ a₁, (SB d (sz.L n) (sz.lam n) a₁ (p.2 1) : ℂ) *
RBM3D/Graph/LWExpTerm.lean:73:               ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![a₁] ω - mSigma (STflowE z n) p.1.1) *
RBM3D/Graph/LWExpTerm.lean:74:                 Lloop sz n (STflowE z n) (t n) p.1.2 p.2 ω ∂(sz.seqP)‖)
RBM3D/Graph/LWExpTerm.lean:75:           (fun n _ _ => (sz.Bctl n (t n)) ^ 3)

RBM3D/Graph/LWExpTerm.lean:80: def LWExpI41 (d : ℕ) : Prop :=
RBM3D/Graph/LWExpTerm.lean:81:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
RBM3D/Graph/LWExpTerm.lean:82:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
RBM3D/Graph/LWExpTerm.lean:83:       ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
RBM3D/Graph/LWExpTerm.lean:84:         LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t → STLK sz (STflowE z) t →
RBM3D/Graph/LWExpTerm.lean:85:         Prec sz (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
RBM3D/Graph/LWExpTerm.lean:86:           (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
RBM3D/Graph/LWExpTerm.lean:87:               (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
RBM3D/Graph/LWExpTerm.lean:88:               ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1] ![a₁] ω - mSigma (STflowE z n) p.1) *
RBM3D/Graph/LWExpTerm.lean:89:                 Lloop sz n (STflowE z n) (t n) ![false, true] ![p.2 0, a₂] ω *
RBM3D/Graph/LWExpTerm.lean:90:                 Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, p.2 1] ω ∂(sz.seqP)‖)
RBM3D/Graph/LWExpTerm.lean:91:           (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3)
```

Compiled nonempty instances (namespace `RBM.Gauss.LWInst`; `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, merged data `sz0 z0 tInst`; proofs: `inst_LWtermEXP (lwTermEXP_of_cut 3 hcut) …`, and `lwExpI1_holds 3 le_rfl (1/10) (1/10) (1/10) … sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 …`, `lwExpI41_holds` likewise):
```
RBM3D/Graph/LWExpTerm.lean:1223: theorem lwExpTerm_inst_cut (hcut : LWCutExp 3) (h1 : STLocalEntry sz0 (STflowE z0) tInst)
RBM3D/Graph/LWExpTerm.lean:1224:     (h2 : LWAvgLaw sz0 (STflowE z0) tInst) (h3 : STLmax sz0 (STflowE z0) tInst)
RBM3D/Graph/LWExpTerm.lean:1225:     (h4 : STLK sz0 (STflowE z0) tInst) (h5 : STDecay sz0 (STflowE z0) tInst) :
RBM3D/Graph/LWExpTerm.lean:1226:     Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
RBM3D/Graph/LWExpTerm.lean:1227:         sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
RBM3D/Graph/LWExpTerm.lean:1228:       (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
RBM3D/Graph/LWExpTerm.lean:1229:       (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=

RBM3D/Graph/LWExpTerm.lean:1233: theorem lwExpTerm_inst_I1 (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) :
RBM3D/Graph/LWExpTerm.lean:1234:     Prec sz0 (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd 3 (sz0.L n)))
RBM3D/Graph/LWExpTerm.lean:1235:       (fun n p _ => ‖∑ a₁, (SB 3 (sz0.L n) (sz0.lam n) a₁ (p.2 1) : ℂ) *
RBM3D/Graph/LWExpTerm.lean:1236:           ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1.1] ![a₁] ω - mSigma (STflowE z0 n) p.1.1) *
RBM3D/Graph/LWExpTerm.lean:1237:             Lloop sz0 n (STflowE z0 n) (tInst n) p.1.2 p.2 ω ∂(sz0.seqP)‖)
RBM3D/Graph/LWExpTerm.lean:1238:       (fun n _ _ => (sz0.Bctl n (tInst n)) ^ 3) :=

RBM3D/Graph/LWExpTerm.lean:1243: theorem lwExpTerm_inst_I41 (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
RBM3D/Graph/LWExpTerm.lean:1244:     (hLK : STLK sz0 (STflowE z0) tInst) :
RBM3D/Graph/LWExpTerm.lean:1245:     Prec sz0 (U := fun n => Bool × (Fin 2 → Zd 3 (sz0.L n)))
RBM3D/Graph/LWExpTerm.lean:1246:       (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
RBM3D/Graph/LWExpTerm.lean:1247:           (SB 3 (sz0.L n) (sz0.lam n) a₁ a₂ : ℂ) * (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
RBM3D/Graph/LWExpTerm.lean:1248:           ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1] ![a₁] ω - mSigma (STflowE z0 n) p.1) *
RBM3D/Graph/LWExpTerm.lean:1249:             Lloop sz0 n (STflowE z0 n) (tInst n) ![false, true] ![p.2 0, a₂] ω *
RBM3D/Graph/LWExpTerm.lean:1250:             Lloop sz0 n (STflowE z0 n) (tInst n) ![false, true] ![a₃, p.2 1] ω ∂(sz0.seqP)‖)
RBM3D/Graph/LWExpTerm.lean:1251:       (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ 3) :=
```

Narrative:
1. Files: new `RBM3D/Graph/LWExpTerm.lean` (1256 lines; grep for `sorry|admit|native_decide|axiom`: 0 hits) and `RBM3D/Test/Axioms.lean` (+1 line in `owedProps`). Base: main f6650b2; main is now e5b944a, whose edits to `Test/Axioms.lean` are other lines of `owedProps`, so the added line does not overlap.
2. Targets 1-5 are delivered. Target 1: the four definitions are the check-file text (each `…Pin ↔ …` is `Iff.rfl`, `verify.lean` exit 0). Targets 2-4: `lwTermEXP_of_cut`, `lwExpI1_holds`, `lwExpI41_holds` are accepted as `LwTermEXPOfCutPin`, `LWExpI1Pin`, `LWExpI41Pin` by `@name`; no hypothesis added, no primed successor needed, the check file is untouched. Target 5: three named instances above.
3. Reduction: `integral_add` of the two cuts (each bounded measurable: `lwExpTerm_BM_LWcut` from `walk_measurable_Lloop` (Path/Walk:819) and `norm_Lloop_le` (GLoopFlow:700)), triangle inequality, `2 ≤ N^{τ/2}`, `st6_prec_det_iff` (Step6Kit:81) on both sides; both cuts live on the same index set `ĝ²/L^d ≤ 1-t`.
4. `≺ → 𝔼` (`lwExpTerm_prec_integral`): a copy of `expDr_expect` (ExpEtermsB:553) and `expDr_first_moment` (ExpEtermsB:523), since `ExpEtermsB` is not among the ticket's imports; first moment off the failure event, envelope `N^{Kenv}`, floor `N^{-Kf}`, no measurability needed.
5. `I₁`: `𝓛^{(2)} = 𝒦 + (𝓛-𝒦)`. `‖𝔼X‖ ≺ B²` is `STExpAvgAt_of_LWAvgLaw` (ExpAvg:799, the proof of `stImproveExpAver_holds`), `‖𝒦‖ ≺ B` is `stKbound_of_flow` (KLFinal:302, `k = 2`), `‖𝔼[X(𝓛-𝒦)]‖ ≺ B³` is `lwExpTerm_XD` (`‖X‖‖D‖ ≺ B·B²` by `STLK` `k = 1, 2` and `StochDomAt.mul`, then `≺ → 𝔼` with envelope `4N³ ≤ N⁴`, floor `N⁻³ ≤ B³`); `Σ_{a₁}‖S_{a₁b}‖ = 1`. `STLmax` is not used.
6. `I₄₁`: `𝔼[XAA'] = 𝔼[XAD'] + (𝔼X)KK' + 𝔼[XD]K'` (`lwExpTerm_I41_split`, abstract in the random variables). `T_a`: off the bad events of `STLK` (`k = 1, 2`) and `STLmax` (`k = 1`), `‖X_{a₁}‖‖D'_{a₃}‖ ≤ N^{τ/2}B³` and `‖𝓛^{(1)}_{+,a}‖ ≤ N^{τ/2}`; `lwExpTerm_Ta_n` and `lwExpTerm_ward_sum_le` give `‖R_a‖ ≤ N^τ η⁻¹B³` (Ward `sum_gloop_two_ward` (ConArgDet:235) at `z̄`; `𝓛^{(2)}_{(-,+)} ≥ 0` is `lwExpTerm_loop2_nonneg`, via `trace_Eblk_mul_mul_conjTranspose` (ConArgDet:640)); then `≺ → 𝔼`. `T_{b1}`, `T_{b2}`: `lwExpTerm_Tb_n` with `STKward` (`stKward_of_flow`, KLFinal:308, `k = 2`) through `KLK_rotate` (KLUnique:604); `η⁻¹B³` closes with `u + u³ + u² ≤ u⁴`, `u = N^{τ/4} ≥ 2`.
7. Copies from RBM3D (not imports): `lwExpTerm_loopL_rot`, `_conj`, `_one`, `lwExpTerm_green_conj`, `lwExpTerm_ward_loop` from `Induction/WardII.lean` (`wardII_loopL_rot` :31, `wardII_loopL_conj` :37, `wardII_loopL_one` :42, `wardII_sum` :47, `wardII_green_conj` :70; private there). No RBM1D/RBM2D port (ticket: no port), so no sister-project `diff --stat`.
8. Registry: the first pre-check run (before the edit) failed with exactly one unclassified premise, `RBM.Gauss.Sizes.LWCutExp` (premise of `lwTermEXP_of_cut`, `lwExpTerm_inst_cut`); I added it to `owedProps` after the `LWtermEXP` line (comment `LW-14b`); the pre-check then exits 0. `LWExpG5` is a premise of no theorem of this file, the pre-check did not list it, so it is not registered (to be registered by LW-14c if it becomes a premise). `LWtermEXP` is not deleted (owed until LW-14c); `LWAvgLaw` stays.
9. Remaining hypotheses of the instances: `LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`, `STDecay` (ST-chain pins, as in the merged `inst_LWtermEXP`) and `LWCutExp` (LW-14b/c).
10. Section (a): I found no mistake in it, so no `(a′)`.

## (c) Verified Mathlib names (one line each; `#check @name` in `names.lean`, importing `RBM3D.Graph.LWExpTerm` because `import Mathlib` has no object file in this tree; 0 errors)
`MeasureTheory.integral_add`, `integral_sub`, `integral_const`, `integral_const_mul`, `integral_mul_const`, `integral_finsetSum`, `integrable_finsetSum`, `Integrable.of_bound`, `norm_integral_le_integral_norm`, `integral_mono_of_nonneg`, `integral_indicator_const`, `measure_toMeasurable`; `Complex.im_le_norm`, `Complex.norm_conj`, `Complex.norm_real`, `Complex.norm_natCast`, `Complex.normSq_nonneg`; `Matrix.diagonal_mul_diagonal`, `Matrix.diagonal_conjTranspose`, `Matrix.trace_mul_comm`, `Matrix.conjTranspose_mul`; `Real.mul_self_sqrt`, `Real.rpow_natCast`, `Real.rpow_neg`, `tendsto_rpow_atTop`, `one_le_inv₀`; `Finset.sum_comm`, `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_add_distrib`, `Finset.measurable_sum`, `Measurable.sub_const`, `norm_sum_le`, `norm_sub_le`, `norm_add₃_le`.
Verified deprecated (build warning, names.lean lines 38-39): `MeasureTheory.integral_finset_sum`, `integrable_finset_sum` (use `integral_finsetSum`, `integrable_finsetSum`).

## (d) Open issues and paper-delta candidates
- `LWCutExp` (one cut in expectation) is proved by nobody yet: LW-14b (`(eq:ELW_term)` from `LWcut`, `I₂`, `I₃`, `J₁–J₄`, assembly via `LWExpG5`) and LW-14c (`LWExpG5`); `LWtermEXP` stays owed. The `η⁻¹ ≤ C(1-t)⁻¹` conversion of `I₄₁`/`LWExpG5` is LW-14b's.
- `T2236a`: `(eq:termI1)` and `(eq:termI41)` (`B:40-42`, `B:64-66`) cite `(res_ELK_n=1)` (`lem:improve_exp_aver`), which is not among the hypotheses of `lem:LWterm_EXP` (`6:83-86`). In Lean `lwExpI1_holds` and `lwExpI41_holds` take `LWAvgLaw`, `STLK` (and `STLmax` for `I₄₁`) only; `(res_ELK_n=1)` is the merged `STExpAvgAt_of_LWAvgLaw` (ExpAvg:799), derived from `LWAvgLaw` at the same time `t`. The lemma is correct as stated; its proof cites an input outside its hypothesis list.
- `T2236b`: `B:61` writes the `T_a` part as `O_≺(B³)·W^d Σ_{a₂} 𝔼 𝓛^{(2)}_{(-,+),(a,a₂)}`, i.e. replaces `Σ_{a₂}|𝓛^{(2)}|` by `Σ_{a₂}𝓛^{(2)}`; this uses `𝓛^{(2)}_{(-,+),(a,b)} ≥ 0`, which the paper does not state. Lean proves it (`lwExpTerm_loop2_nonneg`).
- `T2236c`: the check-file pins of `I₁`, `I₄₁` omit the paper's factor `m` (`|m(σ)| = 1`, `norm_mSigma`) and state `I₁` for all charges `(σ₁, σ)` (the paper takes `σ = -`, `(-,+)` and says the other case is analogous); both are stronger or equal to the paper's bound.
