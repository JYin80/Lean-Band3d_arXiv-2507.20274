Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 13:48:23 UTC 2026

Target (T2299 = "T2292b" of `docs/tickets/T2292.md`, read with T2292b := T2299): `RBM.Ind.stOeqNZ''_holds : ∀ d, STOeqNZ'' d`, the uniform-in-`u` lift of the merged per-time `stOeqNZPT''_holds` (`Induction/QtNonzeroFlow.lean:837`, merged 59a0ab5). Method (a copy of the merged case-(i) lift `Induction/NQEndFlowLift.lean`, `nqLift_lift :868`): envelope `XL♯ = nqFlowSharp t XL`; per-time pin at `(XL♯, XLK♯)` gives `PrecPT(ξ ≺ ζ♯)`; one-sided floor-net core `nqLift_core_below` (`P = seqP`, `Ξ = contGood`, `ε = 1`, `A = 6n_+20`, `Cv = 2n_`) gives `Prec(ξ ≺ ζ♯)`; `ζ♯ ≤ ζ`. Only the label set `V_n`, the `ξ`-modulus and the cardinality change: `V_n = {σA // STIdiff σA.1 ⊆ σA.2} × (Fin n_ → Zd d L)`, `ξ = ‖zeroModeSet d L A (fun b => Lloop … b ω − STKloop … b) a‖ / B_u^{n_}`. The right side `B_u^{1/6} XLK n_ + STbootRHS 2 … B_s n_ p` is the pin of case (i) unchanged, so `ζ♯` (`nqLift_zeta_mono/_le/_one_le`) is reused verbatim.

### (i) Exponent table

| item | value | constraint | slack |
|---|---|---|---|
| `𝔠_d` | that of `stOeqNZPT''_holds d` at the same `(κ,ε,𝔡,C_d)` (`min 𝔠d_G 𝔠d_L`, `≤ 1/100`) | the lift introduces no new `𝔠`; `Admissible`, `RangeCond (ε/2) t`, `t<1`, `\|E\|≤2−κ/2` from `v3_premises_of_stFlow` | none used |
| `ε` of core | `1` | `ε n ≤ ζ♯` (`ζ♯ ≥ 1`: `nqLift_zeta_one_le`, needs `XL,XLK ≥ 1`, `n_ ≥ 1`) | `ζ♯ − 1 ≥ 0` |
| mesh exponent `A` | `6n_ + 20` (= 32, 38, 56 at `n_ = 2, 3, 6`) | `δ := u−u' ≤ N^{-A}` makes the closeness error `≤ B_u^{n_}` | see arithmetic row |
| `Cv` | `2n_` | `#V_n ≤ N^{Cv}` eventually | `#V_n ≤ 2^{n_}·2^{n_}·(L^d)^{n_} ≤ 4^{n_} N^{n_} ≤ N^{2n_}` iff `N ≥ 4` (exact counts, T3) |
| `Q^{(A)}` modulus (new) | `‖Q^{(A)}T‖_∞ ≤ 2^{\|A\|}‖T‖_∞ ≤ 2^{n_}‖T‖_∞` (`norm_zeroModeSet_le`, `Finset.card_le_univ`; linearity `zeroModeSet_sub`) | applied to `T = (L_u−L_{u'})(·)` and `T = (K_u−K_{u'})(·)`, uniformly in `b` (both bounds hold for every `σ : Fin n_ → Bool`, every label) | factor `2^{n_}` is the only change vs case (i) |
| per-label bounds | `‖ΔL‖ ≤ 3n_ N^{2n_+7} √δ` (`LemDecCalELip_Lloop_sub`), `‖ΔK‖ ≤ N^{2n_+2} δ` (`stKloop_lip`, needs `3 ≤ d`, `2 ≤ n_`) | unchanged from case (i) | none used |
| arithmetic | `2^{n_} N^{n_}(3n_ N^{2n_+7}√δ + N^{2n_+2}δ) ≤ 2^{n_}(3n_+1) N^{-3}` at `δ = N^{-(6n_+20)}` (the two summands are `≤ 3n_N^{-3}`, `≤ N^{-3}`, as in `nqLift_arith :705-750`) | `≤ 1`, i.e. `2^{n_}(3n_+1) ≤ N^3`; ticket takes the stronger `hM' : 2^{n_}(3n_+1) ≤ N` (eventual by `LemDecCalELip_env … M := 2^{n_}(3n_+1)`) | at `N = 2^{n_}(3n_+1)`: value `1.09e-3` (`n_=2`), `1.4e-4` (`3`), `6.4e-7` (`6`) (T2) |
| `B`-control | `B_{u'} ≤ B_u` (`STBctl_mono`, `0 ≤ s ≤ u'`), `N^{-1} ≤ B_u` (`cont_inv_size_le_Bctl`) | used to turn the absolute error into `≤ 1` after division by `B_u^{n_}` and to drop the favourable ratio term | `log_N B_u ≥ −0.45 > −1` on all rows of T1; `log_N(B_t/B_s) ∈ [0.017, 0.697] ≥ 0` |
| `ζ♯` | `B_u^{1/6} XLK♯ n_ u + STbootRHS 2 XL♯ XLK♯ B_s n_ p` | non-decreasing in `u ≤ t_n` (`STBctl_mono`, envelopes non-decreasing, `B_s` fixed), `ζ♯ ≤ ζ`, `ζ♯ ≥ 1`, `ζ♯(u') ≤ 2ζ♯(u)` | none used |
| `(1−t)⁻¹ ≤ N` | from `RangeCond (ε/2) t`: `(1−t)⁻¹ ≤ N^{1−ε/2} ≤ N` | hypothesis `htN` of `stKloop_lip`, `LemDecCalELip_env` | instance: `32 ≤ 4096` (T4) |
| `hQ` | `(etaT E t)⁻¹ ≤ N²` (`LemDecCalELip_env`) | | instance: `33.05 ≤ 4096²` at worst `\|E\| = 1/2` (T4) |
| `0 < lam ≤ 𝔡⁻¹` | `nqLift_flowLam` (copy) from `WO 𝔡` | `gmax := 𝔡⁻¹` of `stKloop_lip` | instance: `lam = 1 ≤ 10` |
| crossovers (`log₁₀ N`) | `2^{n_}(3n_+1) ≤ N`: `1.447 / 1.903 / 3.085` at `n_ = 2/3/6`; `N ≥ 4`: `0.602` | eventual (`SizeTendsto`) | instance `N = 4096` (`3.612`) clears all |

The explicit threshold of `stKloop_lip` (`N^{2k+2}` against `k²C²2^k N^{k+3}`) depends on the constant `C` of the merged `KLbound_holds`; it is an `∀ᶠ n` hypothesis-free conclusion of a merged theorem, so no numeric `N` is claimed for it (the Lean instance applies the eventual statement, see T4 note).

### (ii) One concrete nondegenerate instance

Data of the merged `inst_OeqQtNZ` (`Step34Pins.lean:710-837,1006`): `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `lam = 1`, `N_n = (4(n+4))³`; index `n = 0`: `L = W = 4`, `N = 4096`), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `zB = 1/2 + i/64`, `s ≡ 15/16`, `t ≡ 31/32` (`1−s = 1/16 ≤ lam²/L² = 1/16` `STCaseII`: `1−s ≤ lam²/L²`, equality, `lemT zB ≥ 31/32`), `C_d = 1`; lift data `n_ ∈ {2,3,6}`, `p ≥ 1`, `XL ≡ XLK ≡ 1`. Script `pre.py` (scratch; mathematics only; exact `Fraction` arithmetic for T2–T4, `mpmath` 40 digits for T1, T1 at the case-(ii) boundary `1−s = g²/L²`, `1−t = N^{-1+τ}`, `τ = 1/20`, `u` the geometric midpoint, `W = N^𝔠`, `L = N^{1/3−𝔠}`, `g ∈ {1, W^{-1.4}}`):

`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2299/pre.py`
```
T1: c, g, log10N | logN B_s, logN B_u, logN B_t, logN(B_t/B_s), ok(B_s<=B_u<=B_t), ok(logN B_u>=-1)
c=0.1667 g=1      e= 3 | -0.470583649116 -0.312609520255 -0.0436825844002 0.426901064715 True True
c=0.1667 g=1      e= 6 | -0.493755675802 -0.34877089542 -0.0498557222738 0.443899953528 True True
c=0.1667 g=1      e=12 | -0.499643468625 -0.357618333412 -0.0499998559205 0.449643612704 True True
c=0.1667 g=W^-1.4 e= 3 | -0.00391698244888 0.0228979770765 0.0562694953884 0.0601864778373 True True
c=0.1667 g=W^-1.4 e= 6 | -0.0270890091351 -0.0155610487369 0.00893291008303 0.0360219192182 True True
c=0.1667 g=W^-1.4 e=12 | -0.0329768019583 -0.0305674537571 -0.0156298182695 0.0173469836889 True True
c=0.2500 g=1      e= 3 | -0.709579851307 -0.42572797851 -0.0488562443062 0.660723607001 True True
c=0.2500 g=1      e= 6 | -0.735291824558 -0.440651841846 -0.0499954331316 0.685296391426 True True
c=0.2500 g=1      e=12 | -0.746877837901 -0.441659446293 -0.0499999998559 0.696877838045 True True
c=0.2500 g=W^-1.4 e= 3 | -0.00957985130737 0.0142088372216 0.0389805709166 0.048560422224 True True
c=0.2500 g=W^-1.4 e= 6 | -0.0352918245578 -0.020213610243 -0.000946308171986 0.0343455163858 True True
c=0.2500 g=W^-1.4 e=12 | -0.0468778379009 -0.0401425263455 -0.0249322490703 0.0219455888306 True True
T2: n_, N | log10 of 2^n N^n (3n N^(2n+7) sqrt(delta) + N^(2n+2) delta) at delta=N^-(6n+20); <=1 ?
n_=2 N=   28 value=1.093294e-03 <=1:True  bound 2^n(3n+1)/N^3=1.276e-03
n_=2 N= 4096 value=3.492460e-10 <=1:True  bound 2^n(3n+1)/N^3=4.075e-10
n_=3 N=   80 value=1.406250e-04 <=1:True  bound 2^n(3n+1)/N^3=1.563e-04
n_=3 N= 4096 value=1.047738e-09 <=1:True  bound 2^n(3n+1)/N^3=1.164e-09
n_=6 N= 1216 value=6.406956e-07 <=1:True  bound 2^n(3n+1)/N^3=6.763e-07
n_=6 N= 4096 value=1.676381e-08 <=1:True  bound 2^n(3n+1)/N^3=1.770e-08
T3: n_ | #{(sigma,A): Idiff(sigma) subset A} | 4^n | #V = that * 64^n | N^(2n) | #V<=N^(2n)
n_=2 pairs=10 4^n=16 #V=40960 N^2n=281474976710656 ok=True pairs<=4^n:True
n_=3 pairs=28 4^n=64 #V=7340032 N^2n=4722366482869645213696 ok=True pairs<=4^n:True
n_=6 pairs=730 4^n=4096 #V=50165218017280 N^2n=22300745198530623141535718272648361505980416 ok=True pairs<=4^n:True
crossovers log10: 2^n(3n+1): [(2, 1.447), (3, 1.903), (6, 3.085)]  N>=4: 0.602
T4: N= 4096 N=(L W)^3: True  (1-t)^-1= 32  <=N: True
B_s= 0.018612132352941176  B_t= 0.022964015151515152  B_s<=B_t: True  N^-1<=B_s: True  N^-1<=B_t: True
worst |E|=1/2: Im mE= 0.9682458365518543  etaT= 0.030257682392245445  etaT^-1= 33.04945788763662  <=N^2: True  |E|<=2-kappa/2=1.95: True
RangeCond: N^(-1+eps/2)=N^-0.95= 0.0003700479898707028  <= 1-t=1/32: True
lam=1 in (0, 1/𝔡=10]: True   c=1/6<=1/100? (c_d of flow is different; here Bandwidth(1/6): N^(1/6)<=W: True
```
Reading of the output. T1: all 12 rows `B_s ≤ B_u ≤ B_t` with `1−s > 1−t`, `log_N B_s ≥ −0.747`, `log_N B_u ≥ −0.45`. T2: the closing inequality of the `ξ`-modulus holds with room at the minimal allowed `N` and at `N = 4096`. T3: exact label counts at `szB` (`n = 0`): `#V ≤ N^{2n_}`. T4: `N = (LW)³ = 4096`, `(1−t)⁻¹ = 32 ≤ N`, `etaT⁻¹ ≤ N²`, `|E| ≤ 1/2 ≤ 2 − κ/2`, `N^{-0.95} ≤ 1/32` (`RangeCond (ε/2) t`), `lam = 1 ∈ (0, 10]`, `N^{-1} ≤ B_s ≤ B_t < 1`. The index set of the pin is nonempty and nondegenerate at `n_ = 3`: `σ = (+,−,+)`, `A = {0,1}` is a member, 28 pairs `(σ,A)` (T3). Every hypothesis of the lift except the stochastic premises `STLK s`, `STStep2Concl`, the pair hypotheses `Ξ̂ ≺ 1` (other gates' pins, hypotheses of the example as in the merged `QtNonzeroFlowInst` example (2)) is deterministic and holds at these numbers. External hypotheses: none (the lift cites only merged theorems `stOeqNZPT''_holds`, `stKloop_lip`, `LemDecCalELip_Lloop_sub`, `cont_highProbAt_good`), so no limit computation is owed.

### Gates (one line each)
- **§95 (3):** the lift adds no drift or good-set level; no level requires `Ξ̂` at the current length: `ζ♯` is a deterministic function of the controls `(XL♯, XLK♯)` and `B`, and the only event is `contGood = {ω | ∀ c, |ω ⟨n,c⟩| ≤ N}` (`ContinuityNet.lean:225`), a deterministic event of the Gaussian coordinates.
- **Index set / quantifiers:** pin texts (check file §2) differ from the merged `STNZConclPT''` (`QtNonzeroFlow.lean:75`) only in `PrecPT ↦ Prec`; same binders `{d} (sz) (E s t)`; same `𝔠d` as `stOeqNZPT''_holds d`; `3 ≤ d` is a hypothesis of `stKloop_lip` and is `stOeqNZ''_holds`' own `hd`.
- **Ticket size gate (ticket text):** "above 1300 lines at stage 1a: stop"; the ticket's own estimate is 650 / 800 / 1000, below 1300.

### Verdict
- `RBM.Ind.stOeqNZ''_holds` (T2299): **PASS** (no hypothesis set that cannot hold, every exponent closes with the slacks above, statement true as the case-(i) lift with the `Q^{(A)}` modulus `2^{n_}`; no missing input).

## (b) Script output

```
$ date -u
Tue Oct  6 14:02:12 UTC 2026
$ lake build RBM3D.Induction.QtNonzeroFlowLift 2>&1 | tail -3
info: RBM3D/Induction/QtNonzeroFlowLift.lean:966:0: 'RBM.Ind.stOeqNZ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlowLift.lean:967:0: 'RBM.Ind.QtNonzeroFlowLiftInst.inst_OeqNZ''' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3861 jobs).
$ lake env lean RBM3D/Induction/QtNonzeroFlowLift.lean; echo EXIT $?   (fresh elaboration, all output)
'RBM.Gauss.Sizes.STNZConcl''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STOeqNZ''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stOeqNZ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QtNonzeroFlowLiftInst.inst_OeqNZ''' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT 0
$ grep -n "sorry\|admit\|native_decide\|^axiom\|maxHeartbeats" RBM3D/Induction/QtNonzeroFlowLift.lean | wc -l
       0
$ wc -l RBM3D/Induction/QtNonzeroFlowLift.lean
     967 RBM3D/Induction/QtNonzeroFlowLift.lean
$ git diff --stat main...t/T2299
 RBM3D/Induction/QtNonzeroFlowLift.lean | 967 +++++++++++++++++++++++++++++++++
 1 file changed, 967 insertions(+)

$ date -u; lake build 2>&1 | tail -2   (whole library, worktree t/T2299 at 993f772; RBM3D.lean does not import the new module yet: the hub adds the import at merge)
Tue Oct  6 14:03:41 UTC 2026
non-vacuity certificates: 0 of 147 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4104 jobs).
993f772

$ target statements (python extraction from the file)
763: theorem stOeqNZ''_holds : ∀ d : ℕ, STOeqNZ'' d := by
68: def STNZConcl'' (E s t : ℕ → ℝ) : Prop :=
69:   ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
70:     (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
71:     (∀ m, 1 ≤ m → STlenL n_ p m →
72:       Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
73:     (∀ m, 1 ≤ m → m ≤ n_ →
74:       Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
75:     Prec sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
76:         (Fin n_ → Zd d (sz.L n)))
77:       (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
78:           (fun b : Fin n_ → Zd d (sz.L n) =>
79:             Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
80:         (sz.Bctl n (q.1 : ℝ)) ^ n_)
81:       (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
82:         STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)
88: def STOeqNZ'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConcl'' sz E s t)
799: theorem inst_OeqNZ'' :
800:     InstIngConcl (fun sz E s t => STNZConcl'' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
801:   inst_ing STCaseII (fun sz E s t => STNZConcl'' sz E s t) (stOeqNZ''_holds 3) szB zB flow_zB
802:     (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
803:     (szB_flow_ht (by norm_num)) szB_caseII
804:     (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos
805: 
$ ports from RBM1D/RBM2D: grep -c 'RBM1D\|RBM2D' in the new file:
0
$ provenance of the internal copies: diff of §2-§4 against RBM3D/Induction/NQEndFlowLift.lean at d0484be (git log -1 --format=%h):
d0484be
source lines 71-250 -> new file line 96 ; source 257-418 -> new file line 277
block A (71-250) : differing lines: 2
   -`B` is needed): for `s_n ≤ θ ≤ u ≤ t_n < 1`, the right side of `STNQConclPT''` at the envelope controls
   +`B` is needed): for `s_n ≤ θ ≤ u ≤ t_n < 1`, the right side of `STNZConclPT''` at the envelope controls
block B (257-418) : differing lines: 4
   -/-- **The floor net point** (`T2258_netPt_floor`; the witness of `exists_netPt_close`, `Domination.lean:171`, at
   +/-- **The floor net point** (the witness of `exists_netPt_close`, `Domination.lean:171`, at
   -/-- **The one-sided net lift** (`T2258_core_below`): the merged `cont_core` (`ContinuityNet.lean:142`) with the
   +/-- **The one-sided net lift** : the merged `cont_core` (`ContinuityNet.lean:142`) with the 
$ python3 difflib: pin bodies, check file T2299-check.lean (section 2) vs RBM3D/Induction/QtNonzeroFlowLift.lean (a file `variable {d} (sz)` line is replaced by the explicit binders in the check text)
STNZConcl'': check file vs new file: identical
STOeqNZ'': check file vs new file: identical
$ python3 difflib: merged STNZConclPT'' (QtNonzeroFlow.lean) vs new STNZConcl'' (unified, 0 context lines)
--- STNZConclPT''
+++ STNZConcl''
@@ -1 +1 @@
-def STNZConclPT'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
+def STNZConcl'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
@@ -8 +8 @@
-    PrecPT sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
+    Prec sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×

$ name-clash grep (new public names `STNZConcl''`, `STOeqNZ''`, `stOeqNZ''_holds`, `inst_OeqNZ''`, prefix `nzLift_`, namespace `QtNonzeroFlowLiftInst`; zero hits outside the new file; the one hit is the docstring of the merged QtNonzeroFlow.lean:21)
$ for n in names: grep -rn -F -- "$n" RBM3D RBM3D.lean | grep -v 'RBM3D/Induction/QtNonzeroFlowLift.lean'   (hits outside the new file)
== STNZConcl''
== STOeqNZ''
RBM3D/Induction/QtNonzeroFlow.lean:21:is the per-time endpoint, the uniform lift `STOeqNZ''` is T2292b. Paper: arXiv:2507.20274,
== stOeqNZ''_holds
== inst_OeqNZ''
== nzLift_
== QtNonzeroFlowLiftInst
== sanity: hits of nzLift_ in the new file:
83
== sanity: STNZConclPT'' hits in RBM3D outside the new file (grep works):
       9

$ statement script: check-file lines 183-245 (§2-§3 verbatim, namespace RBM.Gauss.Sizes.T2292Check) + two examples; lake env lean stmt.lean

example : RBM.Gauss.Sizes.T2292Check.T2292b_stOeqNZ''_holds := @RBM.Ind.stOeqNZ''_holds
example : RBM.Gauss.Sizes.T2292Check.T2292_stOeqNZPT''_holds := @RBM.Ind.stOeqNZPT''_holds
EXIT 0
$ instances in namespace QtNonzeroFlowLiftInst (line: first line of declaration)
799: theorem inst_OeqNZ'' :
812: example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
839: example : ∃ n : ℕ, ∀ ω ∈ ContinuityNet.contGood szB n, ∀ u u' : ℝ, (15 / 16 : ℝ) ≤ u' → u' ≤ u →
861: example (n : ℕ) : (0 : szB.SeqΩ) ∈ ContinuityNet.contGood szB n := fun c => by simp
865: example : (Fintype.card ({σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} ×
872: example (n : ℕ) : Nonempty (TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
876: example : ∃ x : {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2},
882: example : (2 : ℝ) ^ 3 * ((4096 : ℝ) ^ 3 * (3 * ((3 : ℕ) : ℝ) * (4096 : ℝ) ^ (2 * 3 + 7) *
888: example (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 4) :
895: example : StochDomAt szB.seqP szB.size (U := fun n => TimeIcc (fun _ : ℕ => (15 / 16 : ℝ))
920: example : ∃ k : Fin (netSize 1 4 + 1), netPt 1 1 4 k ≤ (1 / 2 : ℝ) ∧
924: example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) 3 1 ≤
932: example : ∀ (m n : ℕ) (u : ℝ), nqFlowSharp (fun _ : ℕ => (31 / 32 : ℝ)) (fun _ _ _ => (1 : ℝ)) m n u = 1 :=
937: example : nqFlowSharp (fun _ : ℕ => (31 / 32 : ℝ)) (fun _ _ u => (2 : ℝ) + u) 0 0 (15 / 16) = 2 + 15 / 16 ∧
954: example : ∀ d : ℕ, STOeqNZ'' d := @stOeqNZ''_holds
956: example : STOeqNZ'' 3 = STIngR 3 STCaseII (fun sz E s t => STNZConcl'' sz E s t) := rfl
$ registry pre-check (scratch files import RBM3D; reg1 adds import RBM3D.Induction.QtNonzeroFlowLift; then #assert_rbm_axioms; lake env lean)
reg0 (before): exit 0; axiom audit: 8567 theorems, 2815 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
reg1 (after) : exit 0; axiom audit: 8569 theorems, 2817 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff reg0.out reg1.out (whole output, 273 lines each):
1c1
< axiom audit: 8567 theorems, 2815 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 8569 theorems, 2817 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
owed/borrowed premise lines mentioning NZ in reg1.out:
33:  RBM.Gauss.Sizes.STOeqQtNZ': 1 [no certificate]
166: RBM.Gauss.Sizes.STOeqQtNZ',
```

Narrative (script output above is the evidence):
- Method: the new file is the merged case-(i) lift (`Induction/NQEndFlowLift.lean`, d0484be) with the case-(ii) label set. Its sections 2-4 (envelope lemmas, right side `zeta-sharp`, one-sided floor-net core) are copies of source lines 71-250 and 257-418 with the prefix `nqLift_` -> `nzLift_`; the diff above shows 3 differing docstring lines (6 -/+ lines) and nothing else. `nqFlowSharp` and `stKloop_lip` are reused public (import of `NQEndFlowLift`); the per-time pin `stOeqNZPT''_holds` is the merged T2292 theorem. No port from RBM1D/RBM2D.
- New content (file lines 440-779, section 5 and the target): `nzLift_arith` (mesh arithmetic with the factor `2^{n_}`, threshold `2^{n_}(3n_+1) <= N`), `nzLift_proj_le` (copy of the private `nzFlow_proj_le`, `QtNonzeroFlow.lean:467`), `nzLift_xi_close` (the `Q^{(A)}` modulus: linearity `zeroModeSet_sub`, `norm_zeroModeSet_le`, per-label bounds `LemDecCalELip_Lloop_sub` and `stKloop_lip`), `nzLift_card_V` (`#V <= 4^{n_} N^{n_} <= N^{2n_}` for `N >= 4`), `nzLift_xi_close_ev` (the eventual form with `LemDecCalELip_env` at `M = 2^{n_}(3n_+1)`), `nzLift_lift`, and the target.
- Mesh exponent: `A = 6n_ + 20` is kept (the ticket left `6n_+22` as an alternative); the factor `2^{n_}` is absorbed by the stronger threshold `2^{n_}(3n_+1) <= N`, eventual by `LemDecCalELip_env`. `Cv = 2n_`.
- DECISIONS §95 (3): the lift adds no drift or good-set level. `zeta-sharp` is a deterministic function of the controls and `B`; the only event is `contGood` (`ContinuityNet.lean:225`); no level requires `Xi-hat` at the current length.
- Merged names against the ticket text: the names `STNZConclPT''`, `STOeqNZPT''`, `stOeqNZPT''_holds`, `nqFlowSharp`, `stKloop_lip` exist as in the ticket; no merged name differs from the ticket.
- Instances (namespace `RBM.Ind.QtNonzeroFlowLiftInst`, data of `inst_OeqQtNZ`: `szB`, `zB`, `s = 15/16`, `t = 31/32`, `C_d = 1`): (1) `inst_OeqNZ''` by `inst_ing` with `stOeqNZ''_holds 3`; (2) the applied form at `n_ = 3`, `p = 1`, `XL = XLK = 1` (hypotheses left open: `STLK s`, `STStep2Concl`, the two pair hypotheses `Xi-hat < 1`: other gates' pins, as in the merged `QtNonzeroFlowInst` example (2)); (3) `nzLift_xi_close_ev` at the data with every deterministic hypothesis discharged, unfolded at a size index by `.exists`, and `0 in contGood`; (4) `#V <= N^6` at size index 0 and the nonempty index set with the members `(sig3, {0,1})` and `(constant +, empty)`; (5)-(8) arithmetic, `(normQA2)`, core, floor net, envelope at numbers; (9) the pinned types by `example`.
- Registry: no change to `RBM3D/Test/Axioms.lean` (the pins are defined and concluded in this file); the pre-check adds 2 theorems and 2 definitions and no premise (diff above); `STOeqQtNZ'` stays owed (reg1.out line 33).
- Hygiene: no `maxHeartbeats` option, no `sorry`/`admit`/`axiom`/`native_decide` (grep count 0 above); every helper is `private` or prefixed `nzLift_`; the branch diff touches only the new file.

## (c) Verified Mathlib names (one line each; `#check` output, first line, from `lake env lean` on a scratch file importing the new module)
@Finset.card_le_univ : ∀ {α : Type u_1} [inst : Fintype α] (s : Finset α), s.card ≤ Fintype.card α
@Fintype.card_subtype_le : ∀ {α : Type u_1} [inst : Fintype α] (p : α → Prop) [inst_1 : Fintype { a // p 
@Fintype.card_finset : ∀ {α : Type u_1} [inst : Fintype α], Fintype.card (Finset α) = 2 ^ Fintype.card α
@Fintype.card_fun : ∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] [inst_2 :
Fintype.card_bool : Fintype.card Bool = 2
Fintype.card_prod : ∀ (α : Type u_1) (β : Type u_2) [inst : Fintype α] [inst_1 : Fintype β],
@pi_norm_le_iff_of_nonneg : ∀ {ι : Type u_1} {G : ι → Type u_2} [inst : Fintype ι]
@norm_le_pi_norm : ∀ {ι : Type u_1} {G : ι → Type u_2} [inst : Fintype ι] [inst_1 : (i : ι) → SeminormedA
@one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneCla
@le_self_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} {n : ℕ} [Zer
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMu
@pow_le_pow_right₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} {m n : 
@div_le_div_of_nonneg_left : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosM
@div_le_div_of_nonneg_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀]
@Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
@Filter.Eventually.exists : ∀ {α : Type u_1} {p : α → Prop} {f : Filter α} [f.NeBot], (∀ᶠ (x : α) in f, p
@IsLeast.csInf_eq : ∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderInf α] {s : Set α} {a : α},
Real.sInf_empty : sInf ∅ = 0
Names used in the new proofs and not listed (all in the copied sections, compile-verified by the build above): `Real.sqrt_le_sqrt`, `Real.rpow_neg`, `Set.Icc_eq_empty`, `Set.image_empty`, `norm_sub_le`, `norm_add_le`, `Nat.floor_le`, `Nat.lt_floor_add_one`, `csInf_le`, `exists_lt_of_csInf_lt`.
Form note (from the compiler message): in this Mathlib `add_le_add_right h c` has type `c + a <= c + b`; the file uses `add_le_add h le_rfl` where `a + c <= b + c` is needed. No invented names: every name above is in the build.

## (d) Open issues and paper-delta candidates
- `T2299a` (Lean/paper difference): the uniform-in-`u` form `STNZConcl''` is derived from the per-time `STNZConclPT''` by the envelope `X-sharp`, the one-sided floor net and the moduli, before the `newPQ` bootstrap; the paper lifts after it (`3_5:1931`, "a standard `N^{-C}`-net argument"). Equivalent; the same shape as `T2258a` in case (i).
- `T2299b`: the `Q^{(A)}` modulus used for the net: `|| (Q^{(A)} T)_a || <= 2^{|A|} || T ||_infty` (`(normQA2)`, `3_5:1466`) applied to `T = (L_u - L_{u'}) - (K_u - K_{u'})`, giving the closeness `xi(u) <= xi(u') + 1` on `contGood` for `u - u' <= N^{-(6n_+20)}` once `2^{n_}(3n_+1) <= N`; the paper does not state a time modulus of the projected tensor (nor of `K^{(k)}`, cf. `T2258b`).
- No open obstruction; no pinned signature changed; no hypothesis added; no (a') corrections needed (section (a) was not edited).
- Not done here (by the ticket): the root import of the new module in `RBM3D.lean` and the merge (hub); the full-library `lake build` in the worktree does not yet contain the new module, which the registry pre-check imports explicitly.
