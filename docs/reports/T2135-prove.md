Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 12:49:32 UTC 2026

### (i) Exponent table
Notation: `d=3`, `N=sz.size n=(WL)^d`, `g=lam n`, `ℓ_v=ellT L g v=min(max(g/√|1-v|,1),L)`, `η_v=(1-v)Im m(E)`, `m=` tensor length (paper's `n`), `C_κ=2/√κ`, `Admissible 𝔠 𝔡`: `N^𝔠≤W`, `W^{-d/2+𝔡}≤g≤𝔡⁻¹`, `N→∞`. All inequalities are `∀ᶠ n`. Scripts: `scratchpad/T2135/{cut,glue,expo}.py`.
Route. Far premise of `EKFastDecay`: some pair has `zdistD(a_i-a_j) ≥ W^ε ℓ_v`. Then `zdistInf ≥ zdistD/d` (`zdistD_le_mul_zdistInf`) so `diam_∞ ≥ ℓ_v W^ε/d ≥ 2R+1`, `R:=ℓ_v W^{ε/2}`, once `W^{ε/2}≥3d` (`ℓ_v≥1`). A cut (`cutGlueL/R k l' ·`, glued labels `|α-β|_∞≤1` on `supp S^{(B)}`) leaves one piece with `diam_∞ ≥ R` (`l^∞` triangle inequality along `x→α→β→y`); `cutGlue k b` and `eeLoop` keep every label. The far piece is bounded by `STDecayLoopPT`-type input at `τ'=ε/2` (`𝓛, 𝓛-𝒦`) or by `STKcalDecay` at `τ=ε/2` (`𝒦`, `KLmaxDist ≥ diam_∞`); the other factor is crude.
Far factor per term: `STegt`: `𝓛^{(m+1)}(cutGlue_k b)`, other `|avgErr|≤η⁻¹+1`. `STksimLK`: `(𝓛-𝒦)` or `𝒦` piece, other `|𝓛|+|𝒦|` resp. `|𝒦|` (`𝒦` crude, below). `STelklk`: `(𝓛-𝒦)` piece, other `|𝓛|+|𝒦|`. `STee`: one `𝓛^{(2m+2)}`, no other factor (all `2m` labels of `(a,a')=Fin.append` survive).

| # | Quantity | Value / supplier | Constraint | Slack |
|---|---|---|---|---|
| 1 | `ε` adjustment (`l¹→l^∞`) | decay threshold `τ'=ε/2`; `2R+1 ≤ 3ℓW^{ε/2} ≤ ℓW^ε/d ≤ diam_∞` | `W^{ε/2} ≥ 3d=9` | `sz0, ε=1/10`: from `n=3280` (script) |
| 2 | `ℓ_v<L` | `W^ε ℓ_v ≤ zdistD ≤ d⌊L/2⌋` | `W^ε>d/2` | `sz0`: `n≥1` |
| 3 | `1-v` from far premise (no window hyp.) | `ℓ_v<L` ⟹ `g/√(1-v)<L` ⟹ `1-v>g²/L² ≥ W^{-d}L^{-2} ≥ N⁻¹` (`g²≥W^{-d+2𝔡}`, `L^{d-2}≥1`) | `W^ε>d/2` | `sz0`: `g²/L²≥1/N` all `n` |
| 4 | `η_v⁻¹` | `Im m(E)≥√κ/2` for `|E|≤2-κ`, so `η_v⁻¹ ≤ C_κ N` | row 3 | `E=1/2,κ=1`: `Im m=0.968≥0.5` |
| 5 | crude `𝓛` | `‖𝓛_J‖ ≤ η^{-|J|}(W^{-d})^{|J|-1} ≤ (C_κ N)^{|J|}`, `|J|≤2m+2` (`norm_gloop_le_of_le_abs_im`, Hermitian `seqHflow=√v X`) | none | — |
| 6 | crude `𝒦` | `stKbound_holds` (`Loop/KLFinal.lean:243`, from `Admissible`, `|E|≤2-κ`, `lam≤𝔡⁻¹`) + window form of private `gdn_STKbound_win` (`GridDriftN.lean:1027`, copy): `‖𝒦_w‖ ≤ N^{τ₀}Bctl_w^{|J|-1}`, `Bctl_w ≤ 2(1-w)⁻¹ ≤ 2N` (row 3) | per `w` (not `η_{t_n}`: `exists_norm_Kcal_le_win` bounds by `η_{v_n}^{-m}` and `1-t_n` is unconstrained) | `τ₀=1` |
| 7 | `Q` of `STKcalDecay` | `Q=d/2`, `W^{-Q}≤g` (`inst_stKcalDecay_admissible`, `KDecay.lean:976`, for `0≤u<1`) | `W^{-Q}≤g` | `sz0`: `W^{-3/2}` vs `g=W^{-6/5}` |
| 8 | sums | `Σ_{a,b}‖S^{(B)}_{ab}‖=L^d` (`sum_norm_SB_row`, any `g`), `W^dL^d=N`; window `#{a:zdistInf(c-a)≤R}≤(2R+1)^d`; pairs `(k,l')≤m²` | — | script `glue.py` |
| 9 | degree `ν` (with `τ₀=1`, decay input `≤N W^{-D'}`) | `egt: N·m(C_κN+1)·N`=3; `ee: N m N`=2; `ksimLK`: `4m²N·(N W^{-D'})·M`, `M=(C_κ^m+2^{m-1})N^m` ⟹ `ν=m+2`; `elklk` same (`m²`) | `ν=m+2` | `m=2`: `ν=4` |
| 10 | `D''` | `D''=D'+ν/𝔠+1`, i.e. input at `D'':=D+(m+2)/𝔠+1`; `N≤W^{1/𝔠}`; `K_m:=4m²(C_κ^m+2^{m-1}) ≤ W` absorbed by the `+1` | `K_m≤W` eventually | `m=2`: `D''=26`, `K_2=96`, `n≥1` |
| 11 | probability | input hypothesis with the labels inside `Prec`: bad set `{∃(v,σ,a)}` ⊇ complement of the event, no label union; finite intersection over `≤2m+3` lengths, each `≤N^{-D_p-1}` | `N≥2m+3` | — |
| 12 | **quantifier over `v`** | `STEKDecay` is `Whp{∀ v∈[s_n,t_n], …}` (union over `v` inside `P`); `STDecayLoopPT` is `PrecPT` (`∀ u, P{…}≤…`, union outside). Per-time ⇏ uniform (`Ω=[0,1]`, `ξ_v=1_{ω=v}`). Merged `stochDomAt_of_perTimeDomAt` (`StochDomAt.lean:249`) needs `Fintype (U l)`, `#U≤N^C`: true for labels, false for `TimeIcc`; the time lift for 2-loops is the owed pin `STNetLift2` (`Step2Defs.lean:581`) | uniform input needed | **fails with `STDecayLoopPT`** |

Row 12 evidence (`cd /Users/junyin/Lean_proof/RBM3D`, the greps as printed; copy in `scratchpad/T2135/forms.txt`):
```
$ grep -n "∀ u : U l,\|{ω | ∃ u," RBM3D/Defs/StochDomAt.lean
54:  {ω | ∃ u, (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω}
106:  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u : U l,
$ sed -n 595,600p RBM3D/Induction/Step34Pins.lean   (STEKDecay)
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    Whp sz (fun n => {ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D (𝒜 n v ω)})
$ grep -n "def STDecayLoopPT" -A3 RBM3D/Induction/DecayLoopA.lean
106:def STDecayLoopPT (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
108:    PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
$ grep -n "^def STStep2Decay\|^def STStep2DecayPT" -A2 RBM3D/Induction/Step2Defs.lean
263:def STStep2Decay (Cd : ℝ) (E s t : ℕ → ℝ) : Prop :=
265:    Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
287:def STStep2DecayPT (Cd : ℝ) (E s t : ℕ → ℝ) : Prop :=
289:    PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
```
The merged `STSEforLnConcl` (`Step34Pins.lean:363`) is also `Prec` over `TimeIcc × labels`, so the uniform form is the one Step 3 uses. Repair (needs dispatcher): target 2 takes `STDecayLoopU sz E s t` (= `STDecayLoopPT` with `Prec` for `PrecPT`; same `k,τ',D'`; defined in `DecayLoopB.lean`) as hypothesis, and a separate ticket derives it from `STStep2Decay` as `stDecayLoopPT_of_step2` derives `STDecayLoopPT` (the pointwise implication `perTimeCalc_of_imp` is replaced by badSet inclusion `{∃(v,σ,a) bad} ⊆ {∃(v,c) bad}`). With it rows 1-11 close.

### (ii) Concrete instance (`d=3`)
Target 1 (deterministic), `d=3`, `L=9` (random loops, `n∈[2,6]`) and `L=5`. Cut formulas as merged `TreeRep.lean:75-82`, `GLoopFlow.lean:317`, `Step34Pins.lean:152`. `python3 cut.py`:
```
d=3 L=9 n in [2,6]: far-piece trials=212878 violations=0 (tight cases max(spread)=R: 8); length/single-cut violations=0; anchor violations=0, glue-independent anchor violations=0
zdistInf triangle violations: 0
eeLoop length/membership violations: 0
  L=5 R=0: count=1 <= (2R+1)^d=1
  L=5 R=0.5: count=1 <= (2R+1)^d=8.0
  L=5 R=1: count=27 <= (2R+1)^d=27
  L=5 R=1.5: count=27 <= (2R+1)^d=64.0
  L=5 R=2: count=125 <= (2R+1)^d=125
  L=5 R=3: count=125 <= (2R+1)^d=343
  L=5 R=4: count=125 <= (2R+1)^d=729
  L=9 R=0: count=1 <= (2R+1)^d=1
  L=9 R=0.5: count=1 <= (2R+1)^d=8.0
  L=9 R=1: count=27 <= (2R+1)^d=27
  L=9 R=1.5: count=27 <= (2R+1)^d=64.0
  L=9 R=2: count=125 <= (2R+1)^d=125
  L=9 R=3: count=343 <= (2R+1)^d=343
  L=9 R=4: count=729 <= (2R+1)^d=729
window count ok: True
```
`S` is the merged `SB d L g` (kernel `(1+2dg²)⁻¹` at `0`, `g²(1+2dg²)⁻¹` at `zdistD=1`), not `svar`. `python3 glue.py` (`L=5`, loops of length 2-4, two labels at `zdistInf=2=2R+1`, `R=1/2`, synthetic `F,G` with `LoopDecay`):
```
g=0.05: row sums in [1.000000000000,1.000000000000]  sum_ab|S|=125.000000000 (L^d=125)  max |a-b|_inf on support=1
g=0.7: row sums in [1.000000000000,1.000000000000]  sum_ab|S|=125.000000000 (L^d=125)  max |a-b|_inf on support=1
g=3.0: row sums in [1.000000000000,1.000000000000]  sum_ab|S|=125.000000000 (L^d=125)  max |a-b|_inf on support=1
window sum: max ratio |sum S F| / bound = 0.0164  (<=1 required)
glue term: trials=60, violations=0, max |glueTerm|/(L^d(dF MG+MF dG))=0.0044
```
Target 2 at the merged `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`), `𝔠=1/6`, `𝔡=1/10`, `κ=1`, `E=1/2` (flow energy), window `[s,t]=[0,1/16]` (`0≤s≤t<1`), `m=2`, `ε=1/10`, `D=1`. `python3 expo.py`:
```
Im m(E=0.5)=0.9682 >= sqrt(kappa)/2=0.5: True
rows: m, nu=m+2, D''=D+nu/c+1, K_m=4m^2(Ck^m+2^(m-1)) ; threshold n for K_m<=W
  m=2: nu=4, D''=26, K_m=96, first n with K_m<=W: n=1 (W=1.02e+03)
  m=3: nu=5, D''=32, K_m=432, first n with K_m<=W: n=1 (W=1.02e+03)
  m=4: nu=6, D''=38, K_m=1536, first n with K_m<=W: n=2 (W=7.78e+03)
  m=6: nu=8, D''=50, K_m=13824, first n with K_m<=W: n=3 (W=3.28e+04)
per-n hypotheses at sz0 (d=3,c=1/6,dd=1/10,eps=1/10): 
  n   L    W            N^c<=W  W^-(d/2)<=g<=1/dd  g^2/L^2>=1/N  W^(eps/2)>=3d  W^eps>d/2  far-set(l1) nonempty: W^eps*ell<=d*floor(L/2), ell=1
  0       4        3.200e+01    True    True               True          False          False     True
  1       8        1.024e+03    True    True               True          False          True      True
  2       12       7.776e+03    True    True               True          False          True      True
  5       24       2.488e+05    True    True               True          False          True      True
  100     404      3.363e+11    True    True               True          False          True      True
  3280    13124    1.217e+19    True    True               True          True           True      True
  3281    13128    1.219e+19    True    True               True          True           True      True
  1000000 4000004  3.200e+31    True    True               True          True           True      True
first n with W^(eps/2)>=3d: 3280
nonvacuity needs W^eps <= d*floor(L/2): W=(2(n+1))^5, L=4(n+1) => 5*eps<1+o(1), eps<1/5; eps=1/10 ok
N/W^(1/c) at n=0,1,100: ['1.953e-03', '4.768e-07', '1.733e-27']
```
Thresholds (`n≥3280`) are the `∀ᶠ`, not data; the far set is nonempty at every `n` (last column). External hypothesis: the decay input (`STDecayLoopU`, from Step 2 `STStep2Decay`, another gate) stays a hypothesis of the example; no limit computation of it is possible without the Step-2 proof; computed: its use needs only `W^{-D'}`, `D'=D''=26`, `N^{ν}W^{-D''}K_m ≤ W^{-D}` (rows 9-10), and `N≤W^6` (last line). `STKbound` is not a hypothesis (derived, row 6). DECISIONS §29: (1) `0≤s`, `t<1` are theorem hypotheses (`STKcalDecay`, `Bctl`, `gdn_STKbound_win` need `0≤v<1`); (2) no case-(ii) boundary: in case (ii) the far premise is empty (`ℓ_v=L`, `W^εL>dL/2`), so the claim is vacuous there, not false; (3) `L^d≤W^K` unused, only `N≤W^{1/𝔠}`; (4) all `∀ᶠ n`; `3≤d` from `stKcalDecay_holds`/`stKbound_holds` (§36: consumers `STEKSum*` begin `3≤d →`).

### Verdicts
* Target 1 (`LoopDecay`, anchors, `far_cutGlueL_or_far_cutGlueR`, window sums with `SB d L g`, `glueTerm`, `norm_glueTerm_le_of_far`, `eeLoop` lemmas): **PASS**. Dimension changes: `Σ|S|=L^d`, window `(2R+1)^d` (per coordinate `≤2R+1`), support `|a-b|_∞≤1`; no hidden hypothesis. Paper-delta candidate `T2135a`: statements are new (no paper pin; paper `3_5:1115-1130` states `Def_decay` only).
* Target 2 (`stEtermDecay`, `STEKDecay` for `STegt`, `STksimLK`, `STelklk`, `STee`): **FAIL as pinned** (hypothesis `STDecayLoopPT` is per time; `STEKDecay` is uniform in `v∈[s_n,t_n]`, row 12). Every term has a far factor and rows 1-11 close with `τ'=ε/2`, `D''=D+(m+2)/𝔠+1`, so with the repair of row 12 (hypothesis `STDecayLoopU`, `Prec` form; `stDecayLoopU_of_step2` from merged `STStep2Decay` as a follow-up ticket or as an extra part of this one) target 2 is **PASS**. Paper-delta candidate `T2135b`: uniform-in-`u` decay input (paper's "uniformly in `u`" `1_2:1371`) vs per-time `STDecayLoopPT`.

## (a′) Preflight corrections / addendum for Amend 1 (target 3) — Sun Oct  4 13:18:38 UTC 2026

Target 3 `STDecayLoopU`, `stDecayLoopU_of_step2` from `STGdecayW sz E s t Cd` (`Prec`), mathematics only (no Lean, no new check script).
Route: badSet inclusion `{∃ (v,σ,a) : N^{τ₀} W^{-D'} < ξ} ⊆ {∃ (v,c) : N · ζ_Q < ξ_c}` with the far pair `c = c(σ,a)` of the merged `DecayLoopA_pair` and the input `STGdecayW` at `D = Q = 2D' + (2(k-1)+1+C₀)/𝔠 + 1`, `C₀ = max Cd 0 + 1`, `τ₁ = 1`; the pointwise chain of `DecayLoopA_main` is applied at the time `v ∈ [s_n,t_n]` of the index. Row 3 of (i) gives `1-v ≥ N⁻¹` from the far premise alone (`ℓ_v<L`), so the prefactor `P_v = ((1-s)/(1-v))^{Cd} Bctl_v^{1/5} ≤ N^{max Cd 0}·2 ≤ N^{C₀}` (`0 ≤ s ≤ v`, `Bctl_v ≤ 2`) needs no flow premise; hypotheses of the theorem: those of `stDecayLoopPT_of_step2` with `STGdecayW` for `STStep2DecayPT`. Exponent table rows 1-11 unchanged (same `Q`, same slacks); row 12 closes (uniform input). For target 2 the prover uses the cruder uniform degree `D'' = D + (2m+4)/𝔠 + 1` (crude bound `(2Γ N)^{2m+2}` for every factor, `Γ = 2/√κ`) instead of `D + (m+2)/𝔠 + 1`; the hypothesis `STDecayLoopU` holds for every `D'`, so this changes no statement.

## (b) Script output and narrative (stage 1b rerun after the session-limit error; written Sun Oct  4 14:52:20 UTC 2026)

Evidence generated by scripts in `scratchpad/T2135/` (`gen_b.sh`, `gen_ax.sh`, `gen_st.py`, `gen_inst.py`, `clash.sh`); worktree `RBM3D-wt/T2135`, branch `t/T2135`.

```
$ git log --oneline -1; git diff main...t/T2135 --stat; git status --short RBM3D.lean
7f58247 T2135: DecayLoopB docstring references corrected
 RBM3D/Induction/DecayLoopB.lean | 2486 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |    1 +
 2 files changed, 2487 insertions(+)
$ wc -l RBM3D/Induction/DecayLoopB.lean; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/DecayLoopB.lean
    2486 RBM3D/Induction/DecayLoopB.lean
0

$ lake build RBM3D.Induction.DecayLoopB 2>&1 | grep -n "DecayLoopB\|sorry\|error\|Build"
151:Build completed successfully (3766 jobs).

$ full build, RBM3D.lean patched locally with `import RBM3D.Induction.DecayLoopB` (reverted afterwards): lake build 2>&1 | grep "axiom audit\|registry:\|STGdecayW:\|error\|Build completed"
info: RBM3D.lean:183:0: axiom audit: 4153 theorems, 1436 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STGdecayW: 1 [no certificate]
registry: 1 borrowed + 76 owed + 39 structural; 44 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3884 jobs).
Updated 1 path from the index
$ git status --short
```
```
$ lake env lean axioms.lean   (#print axioms of every public declaration of the file, 37; grouped by axiom set by sed)
3 decls with [propext]: Ind.mem_cutGlue Ind.mem_cutGlueL Ind.mem_cutGlueR
7 decls with [propext, Quot.sound]: Ind.DecayLoopB_length_cutGlue Ind.DecayLoopB_wf_cutGlue Ind.eeLoop_WF Ind.exists_anchor_cutGlueL Ind.exists_anchor_cutGlueR Ind.length_eeLoop Ind.mem_cutGlueL_or_mem_cutGlueR
27 decls with [propext, Classical.choice, Quot.sound]: Gauss.DecayLoopBInst.DecayLoopB_sz0_far_nonempty_EK Gauss.DecayLoopBInst.DecayLoopB_sz0_far_nonempty_U Gauss.Sizes.STDecayLoopU Gauss.Sizes.stDecayLoopU_of_step2 Gauss.Sizes.stEtermDecay Ind.DecayLoopB_avgErr_eq Ind.DecayLoopB_bound_of Ind.DecayLoopB_card_ball Ind.DecayLoopB_det_ee Ind.DecayLoopB_det_egt Ind.DecayLoopB_det_elklk Ind.DecayLoopB_det_ksimLK Ind.DecayLoopB_loopDecay_of Ind.DecayLoopB_norm_mul_le_of_far_aux Ind.DecayLoopB_sum_norm_glue_le_of_far Ind.DecayLoopB_sum_sum_norm_SB Ind.far_cutGlueL_or_far_cutGlueR Ind.glueTerm Ind.LoopDecay Ind.LoopDecay.mono Ind.LoopDecay.sub Ind.mem_cutGlue_of_mem Ind.mem_eeLoop_left Ind.mem_eeLoop_right Ind.norm_glueTerm_le_of_far Ind.norm_sum_SB_le_left Ind.norm_sum_SB_le_right
```
Statements extracted from `RBM3D/Induction/DecayLoopB.lean` by `gen_st.py` (file line numbers; `norm_sum_SB_le_right` has the same shape with `b - c`):
```
--- statements (sed-style extraction: file line numbers, signature through the end of the statement)
55: def LoopDecay (N : ℕ) (R δ : ℝ) (F : LoopIdx (Zd d L) → ℂ) : Prop :=
56:   ∀ J : LoopIdx (Zd d L), J.WF → J.length ≤ N → ∀ x ∈ J.a, ∀ y ∈ J.a,
57:     R ≤ (zdistInf d L (x - y) : ℝ) → ‖F J‖ ≤ δ
58: 
177: theorem far_cutGlueL_or_far_cutGlueR (I : LoopIdx (Zd d L)) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
178:     {R : ℝ} {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
179:     (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ)) {α β : Zd d L}
180:     (hab : zdistInf d L (α - β) ≤ 1) :
181:     (∃ x' ∈ (I.cutGlueL k l α).a, ∃ y' ∈ (I.cutGlueL k l α).a,
182:         R ≤ (zdistInf d L (x' - y') : ℝ)) ∨
183:       (∃ x' ∈ (I.cutGlueR k l β).a, ∃ y' ∈ (I.cutGlueR k l β).a,
184:         R ≤ (zdistInf d L (x' - y') : ℝ)) := by
303: theorem norm_sum_SB_le_left (hL : 3 ≤ L) {R M δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (c : Zd d L)
304:     (F : Zd d L → Zd d L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
305:     (hFd : ∀ a b, R ≤ (zdistInf d L (a - c) : ℝ) → ‖F a b‖ ≤ δ) :
306:     ‖∑ a : Zd d L, ∑ b : Zd d L, SB d L g a b * F a b‖ ≤ (2 * R + 1) ^ d * M + (L : ℝ) ^ d * δ := by
370: def glueTerm (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) (k l : ℕ) : ℂ :=
371:   ∑ a : Zd d L, ∑ b : Zd d L, F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b)
372: 
437: theorem norm_glueTerm_le_of_far (hL : 3 ≤ L) {F G : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)}
438:     (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
439:     (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
440:     (hFd : LoopDecay d L I.length R δF F) (hGd : LoopDecay d L I.length R δG G)
441:     (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
442:     {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
443:     (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ)) :
444:     ‖glueTerm g F G I k l‖ ≤ (L : ℝ) ^ d * (δF * MG + MF * δG) := by
461: theorem length_eeLoop (σ : List Bool) (a a' : List α) {k : ℕ} (hk : k ≤ a.length + 1)
462:     (ha' : a'.length = a.length) (b b' : α) :
463:     (STeeLoop σ a a' k b b').length = 2 * a.length + 2 := by
468: theorem eeLoop_WF (σ : List Bool) (a a' : List α) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ a.length)
469:     (hσ : σ.length = a.length) (ha' : a'.length = a.length) (b b' : α) :
470:     (STeeLoop σ a a' k b b').WF := by
475: theorem mem_eeLoop_left (σ : List Bool) (a a' : List α) (k : ℕ) (b b' : α) {c : α}
476:     (hc : c ∈ a) : c ∈ (STeeLoop σ a a' k b b').a := by
792: def STDecayLoopU (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
793:   ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
794:     Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
795:       (fun n p ω =>
796:         (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
797:           ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) *
798:         (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
799:           then 1 else 0))
800:       (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))
801: 
1637: theorem stDecayLoopU_of_step2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
1638:     (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
1639:     (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n)) (Cd : ℝ)
1640:     (hD : STGdecayW sz (STflowE z) s t Cd) : STDecayLoopU sz (STflowE z) s t := by
2209: theorem stEtermDecay (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 : ℝ} {E s t : ℕ → ℝ}
2210:     (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡)
2211:     (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
2212:     (hU : STDecayLoopU sz E s t) (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) :
2213:     STEKDecay sz s t (m := k)
2214:       (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
2215:         sz.STegt n (E n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
2216:     (∀ l : ℕ, STEKDecay sz s t (m := k)
2217:       (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
2218:         sz.STksimLK n (E n) (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
2219:     STEKDecay sz s t (m := k)
2220:       (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
2221:         sz.STelklk n (E n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
2222:     STEKDecay sz s t (m := k + k)
2223:       (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) => sz.STee n (E n) (v : ℝ) ω σ (fun i => b (Fin.castAdd k i))
2224:         (fun i => b (Fin.natAdd k i))) := by
```
Compiled nonempty instances in the same file (`namespace RBM.Gauss.DecayLoopBInst`; `Sizes`, `sz0` at `Defs/Sizes.lean:260`, window `sInst = 0`, `tInst = 1/16` at `Induction/Defs.lean:439-440`); the file's `example`s are at the lines printed first:
```
--- instances (file line numbers; blocks printed up to the next blank line)
example lines: [2283, 2288, 2303, 2311, 2399, 2406, 2425, 2446]
target 1 (d=3, L=5), glueTerm:
2283: example : ‖glueTerm (1 / 2) DecayLoopB_F3 DecayLoopB_F3 DecayLoopB_I3 1 2‖ ≤ ((5 : ℕ) : ℝ) ^ 3 * (1 / 10 * 1 + 1 * (1 / 10)) :=
2284:   norm_glueTerm_le_of_far (g := 1 / 2) (R := 1 / 2) (by norm_num) DecayLoopB_I3_WF le_rfl (by norm_num)
2285:     (by rw [DecayLoopB_I3_length]; norm_num) (by norm_num) (by norm_num) (DecayLoopB_F3_decay _) (DecayLoopB_F3_decay _)
2286:     (fun a => DecayLoopB_F3_bound _) (fun b => DecayLoopB_F3_bound _) DecayLoopB_I3_mem0 DecayLoopB_I3_mem1 DecayLoopB_I3_far
target 1 (d=3, L=5), window sum:
2288: example : ‖∑ a : Zd 3 5, ∑ b : Zd 3 5, SB 3 5 (1 / 2) a b * (if a = 0 then (1 : ℂ) else 1 / 10)‖ ≤
2289:     (2 * 1 + 1) ^ 3 * 1 + ((5 : ℕ) : ℝ) ^ 3 * (1 / 10) :=
2290:   norm_sum_SB_le_left (g := 1 / 2) (by norm_num) zero_le_one (by norm_num) 0
   ... (proof term: 7 more lines, lines 2291-2297)
targets 3 and 2 chained (`STGdecayW` only): see the `example` at line 2446 (not repeated here)
target 2 (hypothesis: STDecayLoopU):
2425: example (hU : STDecayLoopU sz0 (STflowE z0) sInst tInst) :
2426:     STEKDecay sz0 sInst tInst (m := 2)
2427:       (fun n v ω (a : Fin 2 → Zd 3 (sz0.L n)) =>
2428:         sz0.STegt n (STflowE z0 n) (v : ℝ) ω ⟨List.ofFn ![true, false], List.ofFn a⟩) ∧
2429:     (∀ l : ℕ, STEKDecay sz0 sInst tInst (m := 2)
2430:       (fun n v ω (a : Fin 2 → Zd 3 (sz0.L n)) =>
2431:         sz0.STksimLK n (STflowE z0 n) (v : ℝ) ω l ⟨List.ofFn ![true, false], List.ofFn a⟩)) ∧
2432:     STEKDecay sz0 sInst tInst (m := 2)
2433:       (fun n v ω (a : Fin 2 → Zd 3 (sz0.L n)) =>
2434:         sz0.STelklk n (STflowE z0 n) (v : ℝ) ω ⟨List.ofFn ![true, false], List.ofFn a⟩) ∧
2435:     STEKDecay sz0 sInst tInst (m := 2 + 2)
2436:       (fun n v ω (b : Fin (2 + 2) → Zd 3 (sz0.L n)) =>
2437:         sz0.STee n (STflowE z0 n) (v : ℝ) ω ![true, false] (fun i => b (Fin.castAdd 2 i))
2438:           (fun i => b (Fin.natAdd 2 i))) :=
2439:   stEtermDecay (d := 3) (by norm_num) sz0 (κ := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num)
2440:     inst_hE sz0_admissible (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
2441:     (fun n => by norm_num [tInst]) hU 2 le_rfl ![true, false]
target 3:
2399: example (Cd : ℝ) (hD : STGdecayW sz0 (STflowE z0) sInst tInst Cd) :
2400:     STDecayLoopU sz0 (STflowE z0) sInst tInst :=
2401:   stDecayLoopU_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
2402:     (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
2403:     (fun n => sixteenth_le_lemT n) Cd hD
```
Name-clash grep (`clash.sh`; every count is 0, so no new public name exists on `main`):
```
$ git log -1 --format=%h main
549a62d
$ for each new public name n: grep -rnE "(theorem|lemma|def|abbrev|structure|instance) ([A-Za-z_.]*\.)?n( |:|$)" RBM3D (main worktree, DecayLoopB.lean absent there)
LoopDecay=0 mem_cutGlueL=0 mem_cutGlueR=0 mem_cutGlue=0 mem_cutGlue_of_mem=0 exists_anchor_cutGlueL=0 exists_anchor_cutGlueR=0 mem_cutGlueL_or_mem_cutGlueR=0 far_cutGlueL_or_far_cutGlueR=0 norm_sum_SB_le_left=0 norm_sum_SB_le_right=0 glueTerm=0 norm_glueTerm_le_of_far=0 length_eeLoop=0 eeLoop_WF=0 mem_eeLoop_left=0 mem_eeLoop_right=0 STDecayLoopU=0 stDecayLoopU_of_step2=0 stEtermDecay=0 
$ grep -rn "DecayLoopB_" RBM3D --include=*.lean | wc -l
0
$ grep -rn "STDecayLoopU\|DecayLoopBInst" RBM3D RBM3D.lean | wc -l
0
```
Port source (RBM2D `Induction/BcalEDecay.lean`, read at `c9a24cf` through `git show`, 1314 lines there; HEAD and RBM1D HEAD printed by `git log -1 --format=%h`):
```
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/BcalEDecay.lean
 RBM2D/Induction/BcalEDecay.lean | 199 ++++------------------------------------
 1 file changed, 16 insertions(+), 183 deletions(-)
de0de42
```
Narrative:
* Delivered: target 1 (sections 1-7, namespace `RBM.Ind`, lines 42-774), target 3 (section 8: `STDecayLoopU` line 792, `stDecayLoopU_of_step2` line 1637, pointwise-in-`u` chain `DecayLoopB_main_u` line 1386), target 2 (section 9: `stEtermDecay` line 2209), instances (section 10, line 2237 on). Commits on `t/T2135`: `ce32596`, `7cd9b46` (WIP), `2e13857` (code), `7f58247` (docstring references); `git diff main...t/T2135` is the two writable files; `RBM3D.lean` is not in the branch (the root import for the full build was applied locally and reverted, `git status --short` empty).
* Ports (RBM2D `c9a24cf`): `LoopDecay` :74, `far_cutGlueL_or_far_cutGlueR` :179, `norm_sum_SB_le_left` :237, `norm_sum_SB_le_right` :279, `glueTerm` :302, `norm_mul_le_of_far_aux` :307, `norm_glueTerm_le_of_far` :356, `length_eeLoop` :377, `eeLoop_WF` :384, `mem_eeLoop_left` :391 (`grep -n` of the saved copy). Replacements: `Z2 L -> Zd d L`, `zdist2 -> zdistInf`, window `(2R+1)^d` (`DecayLoopB_card_ball`), `sum |S^(B)| = L^d` (`sum_norm_SB_row`, `Defs/Block.lean:118`, `card_Zd`). `S` is the merged `SB d L g`, not `svar`. RBM1D analogues cited in docstrings: `Hierarchy/Decay.lean:164, 339, 368` (RBM1D `de0de42`). RBM2D HEAD differs from `c9a24cf` in this file (diff-stat above); the port is from `c9a24cf` as the ticket pins. Unpinned helpers are `private` or prefixed `DecayLoopB_`; the pinned/ticket-listed names keep their RBM2D names.
* Target 3: the hypotheses of the merged `stDecayLoopPT_of_step2` (`DecayLoopA.lean:970`) with `hD : STGdecayW sz (STflowE z) s t Cd` (`Step34Pins.lean:208`) instead of `STStep2DecayPT`. `k = 1`: the far set is empty (`diam_inf = 0`). `k >= 2`: one event on which the decay input holds for every `(v, sigma, a)`; the cut chain of S3-07a is applied at the index time `v` (docstring of `DecayLoopB_main_u`).
* Target 2: hypotheses are `3 <= d`, `|E n| <= 2 - kappa`, `Admissible c d`, `0 <= s n <= t n < 1`, `STDecayLoopU`, `2 <= k`; `STKbound` and `STKcalDecay` are not hypotheses (used through `stKbound_timeIcc`, `KDecay.lean:1062`, and `inst_stKcalDecay_admissible`, `KDecay.lean`). `l^1 -> l^inf`: `tau' = eps/2`, `W^(eps/2) >= 3d` eventually (`zdistD_le_mul_zdistInf`, `Defs/Sizes.lean:122`); degree `D'' = D + 1 + (2k+4)/c`, the cruder degree of the last sentence of (a'), not the row-10 value `D + (m+2)/c + 1` (`STDecayLoopU` holds for every `D'`, so no statement changes). The second term is stated for every `l` (paper: `3 <= l <= n`, `3_5:1027`).
* Instances: the only hypothesis of the target-3 example is `STGdecayW` (another gate's output, Step 2), of the target-2 example `STDecayLoopU`; every deterministic hypothesis is discharged. `DecayLoopB_sz0_far_nonempty_U` (line 2360) and `DecayLoopB_sz0_far_nonempty_EK` (line 2459) prove that the far set of `STDecayLoopU` and the `l^1` far premise of `EKFastDecay` are nonempty at the `sz0` data for every `n`.
* Registry: `RBM.Gauss.Sizes.STGdecayW` added to `owedProps` (`Test/Axioms.lean:124`); the full build with the root import reports `STGdecayW: 1` and `4153 theorems, 0 axioms`.

## (c) Verified Mathlib/core names used

Root-level (non-`RBM`) identifiers of the file (comments stripped; 431 candidate tokens with `_` or `.`) that resolve in the environment, by `run_cmd` with `env.contains` (`scratchpad/T2135/names.lean`): 212 names. Names verified absent: none recorded (the module builds, so every identifier used resolves).
```
Filter.eventually_all Filter.eventually_all_finset Fin.addCases Fin.append Fin.append_castAdd_natAdd Fin.append_left Fin.append_right Fin.castAdd Fin.natAdd Finset.Icc Finset.Ico Finset.Ioc Finset.card_bij Finset.card_le_card Finset.card_le_card_of_injOn Finset.card_range Finset.card_union_le
Finset.card_univ Finset.coe_Ico Finset.coe_filter Finset.coe_range Finset.coe_union Finset.exists_mem_eq_sup Finset.le_sup Finset.mem_Icc Finset.mem_Ioc Finset.mem_filter Finset.mem_univ Finset.prod_le_prod Finset.range Finset.sum_add_distrib Finset.sum_comm Finset.sum_congr Finset.sum_const
Finset.sum_const_zero Finset.sum_ite Finset.sum_le_sum Finset.sum_mul Finset.sup_congr Finset.sup_le Fintype.card_coe Fintype.card_piFinset Fintype.mem_piFinset Fintype.piFinset List.cons_append List.drop_drop List.eq_nil_of_length_eq_zero List.ext_getElem List.getElem_mem List.getElem_of_mem
List.getLast List.length_append List.length_cons List.length_drop List.length_map List.length_reverse List.length_rotate List.length_singleton List.length_take List.map_append List.map_cons List.map_nil List.mem_append List.mem_cons List.mem_ofFn List.mem_reverse List.mem_singleton List.nil_append
List.ofFn List.ofFn_getElem List.ofFn_succ List.prod_append List.prod_cons List.prod_nil List.rotate_cons_succ List.singleton_append List.take_append_drop List.zip_append List.zip_cons_cons List.zip_nil_left Matrix.mul_one Matrix.trace Matrix.trace_mul_comm Nat.add_le_add Nat.add_le_add_right
Nat.add_mod_right Nat.add_sub_cancel Nat.card_Icc Nat.card_Ico Nat.card_Ioc Nat.cast_mul Nat.cast_nonneg Nat.cast_sub Nat.eq_zero_of_le_zero Nat.floor_le Nat.le_floor_iff Nat.lt_or_ge Nat.mod_eq_of_lt Nat.mul_le_mul_right Nat.sub_le NeZero.ne Option.some.inj Or.inl Or.inr Real.exp Real.exp_pos
Real.log Real.log_le_rpow_div Real.one_le_rpow Real.rpow_add Real.rpow_def_of_pos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_neg_one Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.sq_sqrt Real.sqrt Real.sqrt_eq_rpow
Real.sqrt_le_sqrt Real.sqrt_one Real.sqrt_sq Set.mem_Ico Set.mem_Iio Set.mem_iInter Set.mem_ofPred_eq Set.mem_union Subsingleton.elim ZMod.val_injective ZMod.val_lt ZMod.val_natCast_of_lt abs_nonneg abs_of_pos add_le_add add_zero by_cases by_contra dite_true div_le_div_iff₀ div_le_iff₀ div_lt_iff₀
div_nonneg div_one div_pow half_pos inv_anti₀ inv_eq_one_div inv_inv inv_le_one_of_one_le₀ inv_nonneg inv_pos ite_true le_div_iff₀ le_max_left le_max_right le_mul_of_one_le_left le_mul_of_one_le_right le_of_eq le_of_mul_le_mul_left le_of_mul_le_mul_right le_or_gt le_rfl le_total le_trans lt_irrefl
lt_of_le_of_lt lt_of_lt_of_le lt_of_not_ge max_eq_right min_le_left mul_assoc mul_comm mul_inv_cancel₀ mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_nonneg mul_nonpos_of_nonpos_of_nonneg mul_one mul_one_div_cancel mul_pos mul_pow neg_sub norm_add_le norm_le_norm_add_norm_sub'
norm_mul norm_nonneg norm_num norm_sub_le norm_sum_le nsmul_eq_mul one_div one_div_le_one_div_of_le one_le_pow₀ one_mul one_pos pow_le_one₀ pow_le_pow_left₀ pow_le_pow_right₀ pow_lt_pow_left₀ pow_succ' sq_le_sq₀ sub_add_sub_cancel tendsto_rpow_atTop true_and two_ne_zero zero_add zero_le_one
```

## (d) Open issues and paper-delta candidates

* `T2135a`: target 1 (`LoopDecay` with `zdistInf`, window sums `(2R+1)^d M + L^d delta`, `glueTerm`, the `eeLoop` label lemmas) has no paper pin; the paper states `Def_decay` (`3_5:1115`) and `lem_decayLoop` (`3_5:1126`) only. `3 <= L` is a hypothesis of the window and glue lemmas.
* `T2135b` (Amend 1): uniform-in-`u` decay input: `STDecayLoopU` (`Prec`) from `STGdecayW` (`Prec`) instead of per-time `STDecayLoopPT` from `STStep2DecayPT`; the paper's `(Eq:L-KGt-flow)` is `forall u in [s,t]` inside `\prec` (`1_2:1371-1373`).
* `T2135c`: `stEtermDecay` states `(deccA0)` for `STksimLK` for every `l` (paper `3 <= l <= n`, `3_5:1027`), `STee` as a tensor of the `2k` labels `(a, a')`, `eps -> eps/2` for the `l^1 -> l^inf` conversion, and the extra hypotheses `0 <= s <= t < 1`, `|E| <= 2 - kappa`, `Admissible`.
* Open: `STGdecayW` is owed (Step 2 chain ST2-04); `stDecayLoopU_of_step2` is conditional on it and `stEtermDecay` on `STDecayLoopU`. `stDecayLoopU_of_step2` is the special case `E = lemE z` of the flow with `0 <= s <= t <= lemT z`; it is not `STDecayLoopU` for general `E`.
