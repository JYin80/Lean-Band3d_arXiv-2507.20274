Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:30:43 UTC 2026

Route: **A** (primed pin `STExpIniI'`, `0 < C`, `0 < c`). Base of worktree: `afdb81e` (main). Scripts: `<scratchpad>/T2223/inst.py`, `ta.py` (Python; no Lean).

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `𝔠_d` | `1/(100 d)` (`1/300` at `d=3`) | `0<𝔠_d≤1/100` (`STIngR6`, `Step6Pins.lean:111`); `d𝔠_d<1` (`st_window`) | `1/300` vs `1/100` (x3); `d𝔠_d=1/100<1` |
| window `STEKWin sz s u`, `u∈[s,t]` | `W⁻¹ ≤ (1-t)/(1-s) ≤ (1-u)/(1-s)` | `(1-t)/(1-s) ≥ B_t^{𝔠_d} ≥ (W^{d𝔠_d}(1+𝔡⁻²)^{𝔠_d})⁻¹ ≥ W⁻¹` (`st_window`) | exponent `1-d𝔠_d = 0.99`; `u ≤ t ≤ 1-λ²/L²` is `STReg5I` |
| ratio, `σ₁=σ₂` (`(sum_res_2_NAL)`, `n=2`) | `(λ²+1-s)/(λ²+1-u) ≤ 2` | `1-s ≤ λ²` (regime (i)), `1-u ≥ 0`: numerator `≤ 2λ²`, denominator `≥ λ²`, `λ>0` eventually (`WO`) | instance max `1.0588` (<2) |
| ratio, `σ₁≠σ₂` (`(sum_res_2)`) | `ratio² ≤ 4` | same | instance max `1.1211` (<4) |
| `T_s ≤ T_u` | `T_u=B_u²(G+B_u)`, `G=(λ²W^d)^{-1/5}≥0` | `B_s ≤ B_u` (`STBctl_mono`, `s≤u<1`) | instance `T_s/T_t = 0.72` (all `W` tried) |
| `STEKLow` exponent `b` | `b = 4` | `T_s ≥ B_s³ ≥ (W^{-d}(1+𝔡⁻²)⁻¹)³ ≥ N⁻³·101⁻³ ≥ N⁻⁴` (`N ≥ 101³`) (`STBctl_ge`, `W^d ≤ N`, `𝔡=1/10`) | any `b>3` |
| kernel start/end | `κ' = √(2κ)/2 = 0.2236 ≤ Im m(E)=0.968` (`st6_mE_im_ge`); `‖m‖=1`; `σ` non-alternating: `k=0`, `σ0=σ1` | `STEKSumRes2NAL`; `STEKSumRes2` takes any `σ` | `0.968` vs `0.2236` |
| `≺→𝔼` (1a), `τ` | `τ = 𝔠/2 = 1/12` | `N^τ ≤ W^{1/2}` (`Bandwidth`: `N^𝔠 ≤ W`) | `N^τ=W^{0.255}` at `W=1e31` |
| `D'` (decay floor of `STDecay`) | `D' = D+1` | `N^τ W^{-D'} ≤ W^{-D}/2`, i.e. `W^{1/2} ≥ 2` | `W^{-5.745} ≤ W^{-5}/2` (`D=5`) |
| `D₁` (failure probability) | `D₁ = D+3` | `(η_s⁻²+‖𝒦‖)N^{-D₁} ≤ W^{-D}/2`; `η_s=(1-s)Im m(E)`, `1-s ≥ 1-lemT ≥ Im z/(1+‖z‖) ≥ N^{-1+ε}/4` (`ST_one_sub_lemT`, `Step2Iterate.lean:1014`), `‖𝒦‖ ≤ poly(N)` (`stKbound_of_flow`; take `‖𝒦‖ ≤ N`), `η_s⁻¹ ≤ 18N` | `W^{-21.4} ≤ W^{-5}/2` |
| super-polynomial tail | `e^{-(W^{ε'}/d)^{1/2}}` (`zdistInf ≥ zdistD/d ≥ W^{ε'}ℓ_s/d`) | `N^τ B^{1/5}STWB e^{-…} ≤ W^{-D}/2`, eventual (`W→∞`, `scaleFacts3_W_tendsto`) | threshold, see (ii) |
| `lem_+Q` (`STQopNorm`): `m=1`, `Λ=𝔡⁻¹=10`, `K=1/𝔠=6` | `L^d ≤ N ≤ W^{1/𝔠}` | `L^d ≤ W^K` | instance `64 ≤ W^6` (`W≥4`) |
| `ε_Q` | `min(1/2, τ/(2C_n))` | `W^{C_nε_Q} ≤ W^{τ/2} ≤ N^{τ/(2d)}` (`W_rpow_le`); `4 ≤ W^{ε_Q}` eventually | total `N^{τ/2+τ/(2d)} ≤ N^{2τ/3}`: slack `τ/3` |
| `D_Q` | `D_Q = C_n + 6(b+1)` | `W^{-D_Q+C_n} ≤ N^{-𝔠·6(b+1)} = N^{-b-1} ≤ N^{-b}/2 ≤ T_s/2` | factor `N` |
| `𝒫∘𝒬_s=0` | `Σϑ=1` (clause 1 of `STMollifierProps`) | `QopAlgebra_Psum_Qop`, `i₀=0` | exact |
| `(deccA0)` of `𝒬f` | `f` by 1a; `f-𝒬f=(𝒫f)ϑ` by `stQop_sub_fastDecay` (needs `0<c`, `‖f‖≤W^{C₀}`) | sum of two `W^{-D}` bounds | `c>0` **is used** |
| 1b | `ℓ_s ≤ ℓ_v` for `s ≤ v < 1`, `g≥0`; `W^ε ≥ 0` | `ellT L g t = min(max(g/√|1-t|,1),L)` monotone | exact |
| T2223a: loss without decay | `T_s·(ℓ_s/L)^d·min(R,(L/ℓ_s)²)²`, `R=(1-s)/(1-u)` | `max_q q⁻³min(R,q²)² = R^{1/2}` (`d=3`; `R^{(4-d)/2}`) | script C: equal to 4 digits |
| T2223a: size of `R` | `R ≤ B_t^{-𝔠_d} ≤ (W^d(1+𝔡⁻²))^{𝔠_d}`, loss `≲ R^{1/2} ≈ W^{1/200}` (`d=3`, `𝔠_d=1/300`) | `≺` allows only `N^{τ}`, `τ` arbitrarily small after `𝔠_d` is fixed | fixed positive power: no slack |

### (ii) One concrete nondegenerate instance

Data: `d=3`, `L=4`, `W_n=n+4`, `λ=1`, `N=(4W)³`, `z=1/2+i/64`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `(s,t)=(7/8,15/16)`, `𝔠_d=1/300`, `E=lemE z`. Command and output:

```
$ python3 <scratchpad>/T2223/inst.py
msc(z)=-0.247983+0.960467i  lemT(z)=0.983992  t<=lemT:True  1-lemT=0.01601  Im z/(1+|z|)=0.01041
E=lemE=0.49998 |E|<=2-kappa:True  Im m(E)=0.96825 >= sqrt(2k)/2=0.22361:True |mE|=1.000000
regime(i): lam^2/L^2=0.06250 <= 1-t=0.06250:True ; 1-s=0.12500 <= lam^2=1:True ; s>=0:True ; s<t:True
ell_s=2.8284 ell_t=4.0000
n=0 W=4 N=4.1e+03  locDomain-im, WO, Bandwidth, L^d<=W^6, 4<=W^(1/200): [True, True, True, True, False]
n=1000 W=1004 N=6.48e+10  locDomain-im, WO, Bandwidth, L^d<=W^6, 4<=W^(1/200): [True, True, True, True, False]
n=1e+31 W=1e+31 N=6.4e+94  locDomain-im, WO, Bandwidth, L^d<=W^6, 4<=W^(1/200): [True, True, True, True, False]
ratio (lam^2+1-s)/(lam^2+1-u): max=1.05882 <=2:True ; max^2=1.12111 <=4:True ; (1-t)/(1-s)=0.500
W=4 T_s=0.0001132 T_t=0.0001572 B_s^3=3.976e-06  T_s<=T_u on grid:True  2T_s<=2T_u
W=1004 T_s=1.587e-20 T_t=2.19e-20 B_s^3=1.005e-27  T_s<=T_u on grid:True  2T_s<=2T_u
W=1e+31 T_s=2.582e-205 T_t=3.564e-205 B_s^3=1.042e-279  T_s<=T_u on grid:True  2T_s<=2T_u
cd=0.00333: B_t=1.1912*W^-3; B_t^cd<=1/2 iff W>=1.344e+30 ; at W0 check 0.5000; window 1/W<=(1-u)/(1-s) needs only W>=2
cd=0.01000: B_t=1.1912*W^-3; B_t^cd<=1/2 iff W>=1.147e+10 ; at W0 check 0.5000; window 1/W<=(1-u)/(1-s) needs only W>=2
tau=c/2=0.0833: N^tau=W^0.255 <= W^(1/2):True ; N^tau W^-(D+1)=W^-5.745 <= W^-D/2:True
eta_s=0.1210 eta_s^-2=68.27 ; (eta^-2+|K|)N^-(D+3)=W^-21.41 <= W^-D/2:True
fast-decay term N^tau B_s^(1/5) e^-(W^eps'/d)^(1/2), eps'=1/100: W^-0.357 <= W^-D/2:False ; needs W^eps' ~ >= 6e+05 (W>=1e31 gives 2.04)
```

Reading. Every hypothesis of targets 2, 4 (and 3 up to `STDecay`, `STExp2`, the mollifier) holds at the sequence `szB`, `zB`, `(7/8,15/16)`: regime (i) with `1-t=λ²/L²` exactly, `0≤s<t≤lemT z`, flow `STFlow` (`locDomain`, `WO`, `Bandwidth`), window, `ratio ≤ 2`. `STDecay`, `STExp2` at `s` and the Step 2-5 premises are other gates' pins and stay hypotheses of the compiled instances (ticket, target 8); the mollifier family is the merged `st6_mollifier_family`/`stMollifierEx_holds` (positive `C,c`). The `False` entries are thresholds of the conclusions (`∀ᶠ n`), not of any hypothesis: `4 ≤ W^{ε_Q}` needs `W ≥ 4^{1/ε_Q}` (`2^{400}` for the illustrative `C_n=10`, `τ=1/10`; the pin's `C_n` is not numerically available); the fast-decay term at `ε'=1/100`, `D=5` needs `W^{ε'} ≳ 6e5`, i.e. `W ≳ 1e570`. These thresholds are inherent to `≺`; the Lean statements quantify `∀ᶠ n`.

External-limit line (the only eventual deterministic hypothesis, `STConStInd 𝔠_d`): `B_t = 1.1912 W^{-3} → 0`, so `B_t^{𝔠_d} → 0 < 1/2 = (1-t)/(1-s)`; threshold `W ≥ 1.344e30` for `𝔠_d=1/300` (`1.147e10` for `1/100`), output above. This is the merged shape `hcon : ∀ 𝔠d>0, STConStInd sz 𝔠d s t` of `inst_ing6` (`Step6Inst`, `inst_ing6` signature), eventual in `n`, not a single astronomically large witness; the window itself needs only `W≥2`.

### T2223a (route table (iii)): the second conjunct for `c ≤ 0`

Target 5 `expIniI_props_shift` is true as stated: the shift `a_i ↦ a_i+v` (`i≠0`) is a bijection of `{a : a 0 = a₁}` (clause 1), clauses 3, 4 are pointwise in the shifted index, and clause 2: `exp(-c S'/ℓ) ≤ 1` for `c≥0`, `S'≥0`, `ℓ≥1` (`one_le_ellT`). So a decay-free family satisfies `STMollifierProps … C 0`. Exact computation (`U_{s,u,(+,-)}` has `μ=m m̄=1`, multiplier `r(p)²` on `α(a₂-a₁)`, `Ŝ(p)=(1+2g²Σcos p_i)/(1+2dg²)`):

```
$ python3 <scratchpad>/T2223/ta.py
A. mode p=(2pi/L,0,0): ratio r(p)=(1-s S^)/(1-u S^) vs R=(1-s)/(1-u); premise-only loss (l_s/L)^d*|e^{ipv}-1|*r^2 vs R^{(4-d)/2}
  g    L     1-s    1-u   R=x/y   r(p)   r/R    ell_s   loss=(ell/L)^3*2*r^2   R^(1/2)  log10 W needed for (1-u)/(1-s)>=W^-0.03
  1    16    0.5    0.00391  128      19.98    0.156  1.414   0.5513                 11.3     70
  1    100   0.5    0.0001   5e+03    753.7    0.151  1.414   3.214                  70.7     123
  1    1000  0.5    1e-06    5e+05    7.53e+04 0.151  1.414   32.08                  707      190
  0.3  1000  0.09   9e-08    1e+06    3.755e+04 0.038  1.000   2.819                  1e+03    200
  1    4     0.125  0.0625   2        1.135    0.568  2.828   0.9111                 1.41     10
B. exact FFT on Z_L^3: A(a1,a2)=alpha(a2-a1), alpha=theta(.-v)-theta, theta=gaussian bump width ell_s, sum 1; U multiplies mode p by r(p)^2
  g=1, x=1-s=1/2, y=1-u=g^2/L^2 (regime (i) edge); loss = ell^3*||U alpha||_inf (c0=ell^3*T_s is the premise-only size of P f_s): target is <= ~1
  L=16   R=x/y=128.0   ||alpha||inf*ell^3=0.063  ||U alpha||inf*ell^3=2.836  ratio(loss/R^(1/2))=0.251
  L=32   R=x/y=512.0   ||alpha||inf*ell^3=0.063  ||U alpha||inf*ell^3=7.528  ratio(loss/R^(1/2))=0.333
  L=64   R=x/y=2048.0  ||alpha||inf*ell^3=0.063  ||U alpha||inf*ell^3=17.201  ratio(loss/R^(1/2))=0.380
  L=128  R=x/y=8192.0  ||alpha||inf*ell^3=0.063  ||U alpha||inf*ell^3=36.709  ratio(loss/R^(1/2))=0.406
C. premise-only bound T_s*(l/L)^d*min(R,(L/l)^2)^2, q=L/l>=1: max_q q^-3 min(R,q^2)^2 vs R^(1/2) (d=3), R in {2,512,5e5}
  R=2        max=1.4142 at q=1.414 ; R^(1/2)=1.4142
  R=512      max=22.627 at q=22.63 ; R^(1/2)=22.627
  R=500000   max=707.1 at q=707.1 ; R^(1/2)=707.11
```

Confirmed: the lowest mode `|p|=2π/L` is amplified by `r(p) ≈ 0.15 R` (not suppressed); the dipole tensor with premise-size `c₀=ℓ^dT_s` has `ℓ^d‖𝒰α‖∞` growing like `0.4 R^{1/2} ∝ L` (`2.8 → 36.7` for `L=16 → 128`); `T_u/T_s = 1.38` at `W=1e31` (instance), so `T_u` does not absorb it. The premises of `STIngR6` (`Step6Pins.lean:111-121`: `STLK`, `STDecay`, `STExp2`, `STConStInd`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW`) contain no smallness of `𝒫f_s`, only `‖f_s‖≺T_s` and decay. This is an upper-bound computation, not a refutation of `STExpIniI` (true `c₀` may be small by Ward).
Ward route for `c ≤ 0`: needs the 2-loop Ward step `(eq:EPL-K)` `6:107` = the owed pin `STExpWardI` (`Test/Axioms.lean:236`, S6-10, still owed at `afdb81e`); `(res_ELK_n=1)` is available (`stImproveExpAver_holds`, `ExpAvg.lean:879`, T2217 merged), but the Ward step plus the `L^∞` kernel loss `R²` is S6-10-sized: **does not close in this ticket**. Route B unavailable.

### Verdicts

| target | verdict | reason |
|---|---|---|
| 1a `expIniI_fastDecay` | PASS | constants `τ=𝔠/2`, `D'=D+1`, `D₁=D+3`; tail `e^{-(W^{ε'}/d)^{1/2}}` beats every power of `W` eventually; `1-s ≥ Im z/(1+‖z‖)` gives `η_s⁻¹ ≤ 18N` |
| 1b `expIniI_fastDecay_mono` | PASS | `ℓ_s ≤ ℓ_v`; statement true for `g≥0`, `W≥0`, `s≤v<1` |
| 2 `expIniI_same` | PASS | window from `st_window` (`u≤t`), `STEKLow` `b=4`, ratio `≤2`, `T_s≤T_u`, uniformization `st6_precU_of_forall_seq` |
| 3 `expIniI_Qop` | PASS | `lem_+Q` with `C_n,ε_Q,D_Q` above; needs `0<C`, `0<c` (as stated) |
| 4 `expIniI_mixed` | PASS | `STEKSumRes2` needs `EKSumZero` for every `n`: `𝒜 := if STMollifierProps then 𝒬f else 0`; ratio² `≤4` |
| 5 `expIniI_props_shift` | PASS | statement true (bijection, `exp(-cS'/ℓ)≤1`) |
| 6a `stExpIniI'_holds` | PASS | `𝔠_d=1/(100d)`, `⟨2,4⟩` from 2 and 4 |
| 6b `stExpIniI_holds` (route B) | BLOCKED | needs `STExpWardI` (S6-10, owed): not provable from `STIngR6` premises |
| 7 `ST_step6_caseI_of_pins'` | PASS | consumer check: `Step6Kit.lean:947-1028` differs in `hIni : STExpIniI' d` and the one application `hini.2 C c' hC hc' ϑ hϑ` (`hC, hc'` are in the `obtain` at `:994`); `hini.1` unchanged |
| 8 instances | PASS | `inst_expIniI'` = `inst_ing6_I STReg5I _ (stExpIniI'_holds 3) szB_reg5I`; `inst_skeleton6I'`; `inst_expIniI_fastDecay` (premise `STDecay` at `7/8`); `inst_expIniI_props_shift` (`d=3`, `L=4`, `g=1`, `v=Pi.single 0 2`) |

Observations: (1) the ticket's registry line `:239` (`STExpIniI`) is at `:237` at base `afdb81e` (grep of `RBM3D/Test/Axioms.lean`, worktree); route A leaves it, appends `STExpIniIConcl'` to `structuralProps` (`:330` is the last entry, `STExpIniIConcl]`). (2) `ST_one_sub_lemT` (`Step2Iterate.lean:1014`) is the quantitative `1-lemT` bound the `≺→𝔼` step needs; it is not in the check file's `#check` list.

### (a′) Preflight corrections — Mon Oct  5 23:05:48 UTC 2026

(a) is unchanged. Three constants of (a) differ from the proof; no verdict changes.
1. Row `D₁` (`η_s⁻¹ ≤ 18N`) needs `ε ≥ 0`; the pinned `expIniI_fastDecay` has no `0 < ε`. The proof uses `(1-u)⁻¹ ≤ 4N^{1+|ε|}` (`expIniI_inv_one_sub_le`), `q = 2+|ε|`, `D₁ = (2q+1)/𝔠 + D + 1`.
2. Rows `τ = 𝔠/2`, `D' = D+1`: the proof uses `τ = 𝔠` (`N^𝔠 ≤ W`, `Bandwidth`) and `D' = D+2`.
3. Row `STEKLow` `b = 4`: `b = 3` suffices (`N⁻¹ ≤ B_s`, so `N^{-3} ≤ B_s³ ≤ T_s`).

## (b) Script output
```
$ date -u; git log -1 --format="%h %an" t/T2223; git diff --stat main...t/T2223; git diff main -- Step6Pins.lean Step6Kit.lean | wc -l
Mon Oct  5 23:05:02 UTC 2026
0d2f9ad Jun Yin <321276894+JYin80@users.noreply.github.com>
 RBM3D/Induction/ExpIniI.lean | 1324 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    3 +-
 2 files changed, 1326 insertions(+), 1 deletion(-)
0
$ wc -l ExpIniI.lean; grep -c "sorry|admit|native_decide|^axiom" ExpIniI.lean; imports
    1324 lines; 0 hits; imports: Induction.Step6Kit Induction.QopNorm Evolution.Prec Induction.ScaleFacts3 Induction.Step2Events Gauss.DominationAt Path.Walk Loop.GLoopFlow Loop.KLFinal 
$ lake build RBM3D.Induction.ExpIniI | tail -2; lake build | tail -2   (full library, root #assert_rbm_axioms)
Build completed successfully (3847 jobs). exit=0 
Build completed successfully (4024 jobs). exit=0 
$ lake env lean axioms.lean   (#print axioms of the 19 public declarations of ExpIniI.lean, grouped)
19 declarations with [propext, Classical.choice, Quot.sound]: expIniI_fastDecay expIniI_fastDecay_mono expIniI_same expIniI_Qop expIniI_mixed 
expIniI_props_shift STExpIniIConcl' STExpIniI' stExpIniI'_holds ST_step6_caseI_of_pins' inst_expIniI' inst_skeleton6I' inst_expIniI_fastDecay 
inst_expIniI_fastDecay_mono inst_expIniI_same inst_expIniI_Qop inst_expIniI_mixed inst_expIniI_props_shift inst_expIniI_props_shift_ex
$ python3 extract3.py targets   (statements copied from ExpIniI.lean, proofs omitted; "line: text")
309: theorem expIniI_fastDecay {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s : ℕ → ℝ) (hs0 : ∀
    n, 0 ≤ s n) (hsT : ∀ n, s n ≤ lemT (z n)) (hDec : STDecay sz (STflowE z) s) (ε' D : ℝ) (hε' : 0 < ε') (hD : 0 < D) : ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
    EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D (fun b => STExpErr sz n (STflowE z n) (s n) σ b) := by
495: theorem expIniI_fastDecay_mono {d L n : ℕ} {g s v W ε D : ℝ} (A : (Fin n → Zd d L) → ℂ) (hg : 0 ≤ g) (hW : 0 ≤ W) (hsv : s ≤ v) (hv : v < 1) (h :
    EKFastDecay g s W ε D A) : EKFastDecay g v W ε D A := by
646: theorem expIniI_same {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow :
    STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hDec : STDecay sz
    (STflowE z) s) (hExp : STExp2 sz (STflowE z) s) (hcon : STConStInd sz 𝔠d s t) : Prec sz (U := STIdx2P sz STSigSame s t) (fun n p _ => ‖RBM.Ind.Ugen d
    (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b) p.2.2‖) (fun n p _ => STExpTarget sz n
    (p.1 : ℝ)) := by
735: theorem expIniI_Qop {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤
    s n) (hsT : ∀ n, s n ≤ lemT (z n)) (hDec : STDecay sz (STflowE z) s) (hExp : STExp2 sz (STflowE z) s) (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ
    → (Fin 2 → Zd d (sz.L n)) → ℂ) (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) : (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
    ‖STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * STExpTarget sz n (s n)) ∧ (∀ ε' D : ℝ, 0 < ε'
    → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, EKFastDecay (sz.lam n) (s n) ((sz.W n : ℕ) : ℝ) ε' D (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n
    (STflowE z n) (s n) σ b))) ∧ (∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, EKSumZero (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) σ b)))
    := by
892: theorem expIniI_mixed {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow :
    STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hDec : STDecay sz
    (STflowE z) s) (hExp : STExp2 sz (STflowE z) s) (hcon : STConStInd sz 𝔠d s t) (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L
    n)) → ℂ) (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖RBM.Ind.Ugen d
    (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ) (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖) (fun
    n p _ => STExpTarget sz n (p.1 : ℝ)) := by
1015: theorem expIniI_props_shift {d L m : ℕ} [NeZero L] (g C c : ℝ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (v : Zd d L) (hc : 0 ≤ c) (h : STMollifierProps (d
    := d) g C c ϑ) : STMollifierProps (d := d) g C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + v)) := by
1089: def STExpIniIConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop := Prec sz (U := STIdx2P sz STSigSame s t) (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n)
    (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (s n) p.2.1.1 b) p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧ ∀ (C c : ℝ), 0
    < C → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ, (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → Prec sz (U := STIdx2P sz
    STSigMixed s t) (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ) (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (E n)
    (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ))
1102: def STExpIniI' (d : ℕ) : Prop := STIngR6 d STReg5I (fun sz E s t => STExpIniIConcl' sz E s t)
1106: theorem stExpIniI'_holds (d : ℕ) : STExpIniI' d := by
1127: theorem ST_step6_caseI_of_pins' {d : ℕ} (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hDuQ :
    STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d) (hIni : STExpIniI' d) (hInt : STExpIntI d) : STStep6I d := by
$ python3 extract3.py inst   (the compiled instances, statements truncated at 230 characters; each compiles with no sorry)
1225: theorem inst_expIniI' : InstIng6Concl (fun sz E s t => STExpIniIConcl' sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
1230: theorem inst_skeleton6I' (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3) (hDuQ : STExpDuhamelQ 3) (hDec :
    STExpDriftDecay 3) (hWd : STExpWardI 3) (hInt : STExpIntI 3) : InstIng6Concl ( ...
1236: theorem inst_expIniI_fastDecay (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8)) : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
    EKFastDecay (szB.lam n) (7 / 8) ((szB.W n : ℕ) : ℝ) ε' D (fun b => STExpErr szB n  ...
1245: theorem inst_expIniI_fastDecay_mono : EKFastDecay (d := 3) (L := 4) (n := 2) 1 (15 / 16) 5 (1 / 100) 5 (fun a => if a 0 = a 1 then (1 : ℂ) else 0) := by
1262: theorem inst_expIniI_same (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8)) (hExp : STExp2 szB (STflowE zB) (fun _ => 7 / 8)) : Prec szB (U := STIdx2P
    szB STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16)) (fun n p _ => ‖RBM.Ind.Ugen ...
1274: theorem inst_expIniI_Qop (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8)) (hExp : STExp2 szB (STflowE zB) (fun _ => 7 / 8)) : ∃ C c : ℝ, 0 < C ∧ 0 < c
    ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ, (∀ᶠ n in atTop, STMollifie ...
1292: theorem inst_expIniI_mixed (hDec : STDecay szB (STflowE zB) (fun _ => 7 / 8)) (hExp : STExp2 szB (STflowE zB) (fun _ => 7 / 8)) : ∃ C c : ℝ, 0 < C ∧ 0 <
    c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ, (∀ᶠ n in atTop, STMollif ...
1309: theorem inst_expIniI_props_shift : ∀ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 ≤ c → STMollifierProps (d := 3) 1 C c ϑ → STMollifierProps (d := 3) 1 C
    0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + Pi.single 0 2)) :=
1317: theorem inst_expIniI_props_shift_ex : ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 < C ∧ 0 < c ∧ STMollifierProps (d := 3) 1 C c ϑ ∧ STMollifierProps
    (d := 3) 1 C 0 (fun t a => ϑ t (fun i => if i = 0 then a 0 else a i + Pi.single ...
$ registry pre-check: lake env lean pre_base.lean (import RBM3D; #assert_rbm_axioms; run before editing Test/Axioms.lean) and pre_after.lean (+ import RBM3D.Induction.ExpIniI, edited Axioms.lean)
base : exit 0; premises found by scanning: 126 (borrowed 1, owed 94, structural 25, refuted 6).; registry: 2 borrowed + 145 owed + 80 structural + 7 refuted; 108 registered premise(s) carry;   RBM.Gauss.Sizes.STExpIniI: 4 [no certificate]
after: exit 0; premises found by scanning: 125 (borrowed 1, owed 94, structural 24, refuted 6).; registry: 2 borrowed + 145 owed + 81 structural + 7 refuted; 110 registered premise(s) carry;   RBM.Gauss.Sizes.STExpIniI: 4 [no certificate]
$ diff of the two outputs, lines naming new classifications:
> RBM.EKFastDecay,
> RBM.Gauss.Sizes.STExpIniIConcl',
$ git diff main...t/T2223 -- RBM3D/Test/Axioms.lean | grep "^[+-] "
-   `RBM.Gauss.Sizes.STExpIniIConcl] -- conclusion of the initial term, regime (i) (`6:117`); S6-01 (T2204, DECISIONS §67: structural)
+   `RBM.Gauss.Sizes.STExpIniIConcl, -- conclusion of the initial term, regime (i) (`6:117`); S6-01 (T2204, DECISIONS §67: structural)
+   `RBM.Gauss.Sizes.STExpIniIConcl'] -- conclusion of the initial term, regime (i), positive mollifier constants (`6:117`; T2223a); S6-11 (T2223, DEC
$ check-file equality (eq_check.lean = check imports + import ExpIniI + sections 1-2 + 8 `example : T2223Check.X := @X`, 2 `rfl` examples, 4 instance examples; lake env lean)
exit 0; 'error' lines: 0; examples compiled: 14
$ name clash: grep -rnF --include=*.lean PATTERN RBM3D RBM3D.lean, excluding ExpIniI.lean, Probe/, the registry line Axioms.lean:331
'expIniI_' 0 hits;'stExpIniI'' 0 hits;'STExpIniI'' 0 hits;'STExpIniIConcl'' 0 hits;'ST_step6_caseI_of_pins'' 0 hits;'inst_expIniI'' 0 hits;'inst_skeleton6I'' 0 hits;'inst_expIniI_' 0 hits;'ExpIniI.lean' 0 hits;'Induction.ExpIniI' 0 hits;'T2223' 0 hits;
$ ports: sources are RBM3D files (no RBM1D/RBM2D port); last commits:
RBM3D/Evolution/MeanFar.lean a21a819; RBM3D/Induction/ExpAvg.lean d0d79ce; RBM3D/Evolution/Prec.lean fc76526; RBM3D/Induction/Step6Kit.lean 9e0d6a7; 
```

Narrative (route A; preflight verdict 6b BLOCKED, so `STExpIniI` is not proved).
1. `STExpIniI` is unchanged and stays owed (`STExpIniI: 4 [no certificate]` in both pre-check outputs; `Test/Axioms.lean:237` at the base). New: `STExpIniI'`, `stExpIniI'_holds`, `ST_step6_caseI_of_pins'`. `git diff main -- Step6Pins.lean Step6Kit.lean` is empty (0 lines).
2. File layout: §1 private facts, §2 targets 1a/1b, §3 window and lower control, §4 target 2, §5 target 3, §6 target 4, §7 target 5, §8 pin and consumer, §9 instances. 1324 lines (ticket estimate 800/1000/1250).
3. Target 1a: `τ = 𝔠`, `D' = D+2`, `q = 2+|ε|`, `D₁ = (2q+1)/𝔠 + D + 1`. Off an event of probability `≤ N^{-D₁}` (the witness `(σ,a)` lies in the union inside `STDecay`), `‖f_{σ,a}‖ ≤ N^𝔠 Z + (η⁻² + |𝒦|) N^{-D₁}`; `Z ≤ B^{6/5} e^{-(W^{ε'}/d)^{1/2}} + W^{-D'}` (`W^{-d}B_{K} ≤ B`, `K ≥ W^{ε'}ℓ_s/d`); `B, η⁻¹ ≤ N^q`; `|𝒦| ≤ N·B` from `stKbound_of_flow` and `st6_prec_det_iff`; `W ≤ N ≤ W^{1/𝔠}`; `W^c e^{-(W^{ε'}/d)^{1/2}} ≤ W^{-D}/3` eventually.
4. Target 2 follows `st6_ini_sumNdecay`: `stek_sumRes2NAL_holds` (`n = 2`, `κ' = √(2κ)/2`) with `𝒜 n v ω := f_s`, `X := T_s`, `STEKDecay` from 1a and 1b, `STEKLow` with `b = 3`, window from `st_window` at `t` then `(1-t)/(1-s) ≤ (1-u)/(1-s)`; evaluation at `v = s` by `precomp_param`; ratio `≤ 2` from `1-s ≤ ilambda²` (`STReg5I`) and `T_s ≤ T_u`; `st5_prec_mono` with `c = 2`; `st6_precU_of_forall_seq`, `st6_prec_of_forall_fin` for `u` and `σ`.
5. Target 3: (i) `stQopNorm_holds` at `m = 1`, `Λ = 𝔡⁻¹`, `K = 1/𝔠`, `ε_Q = min(1/2, τd/(4C_n))`, `D_Q = C_n + 5/𝔠 + 1`, with `‖f_s‖ ≤ N^{τ/4}T_s` from `STExp2`; (ii) `stQop_sub_fastDecay` with `C₀ = (2q+2)/𝔠` from the private bound `expIniI_env_poly`; (iii) `QopAlgebra_Psum_Qop`.
6. Target 4: `stek_sumRes2_holds` needs `EKSumZero` for every `n`, so the tensor is `if STMollifierProps … then 𝒬_s f_s else 0`; the conclusion is transferred by `StochDomAt.of_subset` on the eventual equality; ratio² `≤ 4`, `st5_prec_mono` with `c = 4`.
7. Target 5 and the instance `inst_expIniI_props_shift_ex`: a concrete family from the merged `stMollifierEx_holds` (`d = 3`, `m = 1`, `Λ = 1`, `L = 4`, `g = 1`) satisfies the premises, so its shift is a non-decaying member of the class quantified by `STExpIniIConcl`.
8. Preflight numbers for T2223a (from (a), T2223a block): loss `T_s(ℓ_s/L)^d min(R,(L/ℓ_s)²)²` with `max_q = R^{1/2}` at `d = 3` (script C: max = 1.4142, 22.627, 707.1 against `R^{1/2}` = 1.4142, 22.627, 707.11 at `R = 2, 512, 5e5`); the lowest mode is amplified by `r(p) ≈ 0.15 R`; `ℓ^d‖𝒰α‖_∞` goes `2.8 → 36.7` for `L = 16 → 128`; `R ≤ (W^d(1+𝔡⁻²))^{𝔠_d}`, loss `≈ W^{1/200}`. Not compiled, no refutation registered; the Ward route is S6-10-sized.
9. Not done (not targets): refutation of `STExpIniI`; the `c ≤ 0` question for `STExpIntQConcl`, `STExpWardIConcl`; any change of a merged pin. No hypothesis was added to a pinned statement; the instances keep `STDecay`, `STExp2` at `s ≡ 7/8` and the other regime-(i) pins as hypotheses.
10. Imports are nine of the ten of the check file; `Evolution.ExpInv` is not needed by any proof.

## (c) Verified Mathlib names (from the constants of ExpIniI.lean declared in Mathlib, script `used.lean`)
- `Real.`: `rpow_add`, `rpow_mul`, `rpow_neg`, `rpow_neg_one`, `rpow_natCast`, `rpow_one`, `rpow_nonneg`, `rpow_pos_of_pos`, `rpow_le_rpow`, `rpow_le_rpow_of_exponent_le`, `rpow_le_one`, `rpow_one_add'`, `div_rpow`, `exp_le_exp`, `exp_le_one_iff`, `exp_pos`, `exp_zero`, `sqrt_le_sqrt`, `sqrt_pos`.
- `Real.rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z` (`Pow/Real.lean:565`).
- `tendsto_rpow_atTop`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s b) (hb : 0 < b)`, `Filter.Tendsto.atTop_div_const`, `.const_mul`, `.comp`, `.eventually`, `Filter.eventually_ge_atTop`, `eventually_gt_atTop`.
- `MeasureTheory.`: `integral_sub`, `integral_add`, `integral_const`, `integral_const_mul`, `integral_indicator_one`, `integral_mono`, `norm_integral_le_integral_norm`, `Integrable.of_bound`, `Integrable.norm`, `integrable_const`, `measure_mono`, `measureReal_le_one`, `measurableSet_lt`; `Finset.sum_equiv`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `Complex.norm_le_abs_re_add_abs_im`, `ENNReal.toReal_mono`, `ENNReal.toReal_ofReal`.
- `inv_anti₀`, `div_le_div_iff₀`, `div_le_iff₀`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`, `one_le_pow₀`, `pow_le_pow_left₀`, `inv_le_one_of_one_le₀`, `one_div_le_one_div_of_le`, `min_le_min`, `max_le_max`.
- Verified absent: `Real.rpow_le_rpow_of_exponent_nonpos` (grep of `.lake/packages/mathlib/Mathlib`: no hit). `if_pos`, `if_neg` are deprecated in this toolchain (build warning at the first use), replaced by `simp [Q0, hn]`.

## (d) Open issues and paper-delta candidates
- **T2223a (paper-delta candidate).** Lean: the merged `STExpIniIConcl` (`Step6Pins.lean:458-469`) quantifies over every `(C, c)`; paper (`6:117`, `Def:QtPt` `3_5:1204-1229`, "for a constant `c>0`" at `:1214`, `rmk:choosechi` `3_5:1250`): the mollifier has `c > 0`. Lean successor: `STExpIniIConcl'`, `STExpIniI'` (`0 < C → 0 < c →`), proved by `stExpIniI'_holds`; evidence of the gap: `expIniI_props_shift`, `inst_expIniI_props_shift_ex`. `STExpIniI` is kept owed; the dispatcher decides whether it moves to "superseded" once `ST_step6_caseI_of_pins'` is the consumer.
- The same unrestricted quantifier is in `STExpIntQConcl` (`Step6Pins.lean:409-411`) and `STExpWardIConcl` (`:342-344`); untouched.
- No `T2223b`: no step needed a hypothesis the pin lacks.
- Observation: the owed line of `STExpIniI` is `Test/Axioms.lean:237` at the base, not `:239` as in the ticket.
- Observation: `RBM.EKFastDecay` (registered structural, `Axioms.lean:269`) now appears in the "carry nothing yet" list and the scanned structural count drops 25 → 24. Cause isolated by `iso.lean` (calls `RBM.Audit.scanPremises` on `import RBM3D` + `import RBM3D.Induction.ExpIniI`, once as is, once with `expIniI_fastDecay_mono` and `inst_expIniI_fastDecay_mono` as witnesses): `scan: 125 premises found, EKFastDecay found: false; with the two theorems treated as non-proofs: 126 found, EKFastDecay found: true`. The pinned conclusion of `expIniI_fastDecay_mono` has head `EKFastDecay`, so the scan counts it as a proof. Registry counts: owed 145 → 145, structural 80 → 81; `#assert_rbm_axioms` exits 0; no registry line was added for it.
- Merge note for the hub: the `Axioms.lean` change is at the end of `structuralProps` (the closing `]` moves to the new last line); a union with the tickets that also append there needs the `]` kept on the last line. The root import `import RBM3D.Induction.ExpIniI` goes after the last import of `RBM3D.lean`.
