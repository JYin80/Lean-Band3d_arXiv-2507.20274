Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 14:38:10 UTC 2026

Notation (merged defs): `x_u=1−u`, `g=ilambda`, `B_u=sz.Bctl n u=W^{-d}[(g²+x_u)^{-1}+(L^d x_u)^{-1}]` (`Defs/Sizes.lean:214`, `Params.lean:36`, K=0), `ρ_q=η_s/η_{q.1.2}=(1−s)/(1−q.1.2)` (`scaleFacts_etaT_div_etaT`, |E|<2), `c=𝔠d`, `Ψ=A^{3/4}+ρ^{r−1}A^{1−k/8}` (`STPsi A ρ r k`), `A_I=g²W^d` (`STAI`), `A_II=B_s^{-1}` (`STAII`). `con` = `STConStInd c s t`: eventually `B_t^c ≤ x_t/x_s < 1`.

### (i) Exponent table
| quantity | value | constraint / derivation (merged lemma) | slack |
|---|---|---|---|
| `k_min(c,r)` | `⌊2+8c(r−1)⌋+1` | `Ψ`-exponent `c(r−1)+1−k/8 ≤ 3/4` iff `k ≥ 2+8c(r−1)`; floor+1 gives `k>2+8c(r−1)` | exponent slack `(k−2−8c(r−1))/8 ∈ (0,1/8]`; c=1/100: r=2,3,10→k=3; r=50→6; r=100→10 |
| `ρ_q` upper bound | `1 ≤ ρ_q ≤ (1−s)/(1−t) ≤ B_t^{-c}` | `q.1.1≤q.1.2≤t`, con (`B_t>0`: `STBctl_pos`, needs `t<1`) | `ρ_q≥1` since `s≤q.1.2` |
| case I: `B_t ≥ 1/(2A_I)` | `B_t^{-c} ≤ (2A_I)^c` | `x_t≤x_s≤g²` (STRegIterI, `s≤t` from q) ⇒ `g²+x_t≤2g²` ⇒ `B_t ≥ W^{-d}/(2g²)`; no `d`-condition | R2: `B_t=0.0935 ≥ 1/16` |
| case II: `B_t^{-c}≤B_s^{-c}=A_II^c` | `ρ_q ≤ A_II^c` | `STBctl_mono` (`B_s≤B_t`, `t<1`) | exact, no loss |
| `A ≥ 1` case I | `A_I ≥ W^{2𝔡} ≥ 1` | `Sizes.lam_sq_mul_pow_ge` from `WO 𝔡` (eventually). `WO 𝔡` forces `𝔡>0`: `0<W^{..}≤ilambda≤𝔡⁻¹` | sz0: `A_I=8` |
| `A ≥ 1` case II | `B_s ≤ B_t < 1` ⇒ `A_II>1` | con gives `B_t^c<1`, `c>0` ⇒ `B_t<1`. **No range hypothesis needed** (ticket item 3 suggested `N^{-1+τ}≤1−t`; unnecessary) | R3: `A=4.60`, R4: `3.55` |
| `Ψ` constant case I | `c_I(r)=1+2^{c(r−1)}` | `ρ^{r−1}A^{1−k/8} ≤ 2^{c(r−1)}A^{c(r−1)+1−k/8} ≤ 2^{c(r−1)}A^{3/4}` (needs `A≥1`) | r=100,c=1/100: 2.99 |
| `Ψ` constant case II | `c_II=2` | `ρ^{r−1}A^{1−k/8} ≤ A^{c(r−1)+1−k/8} ≤ A^{3/4}` | exact |
| `hBA` case I | `B_vA^{3/4} ≤ 2` (c_B=2) | `v≤t`: `x_v≥x_t≥g²/L²`; `(L^dx_v)^{-1} ≤ L^{2−d}g^{-2} ≤ g^{-2}` needs **`2 ≤ d`** (`L≥1`); `(g²+x_v)^{-1}≤g^{-2}`; `B_v ≤ 2/A_I`; `2A^{-1/4}≤2` | R2: `B_tA^{3/4}=0.44`; bound `2A^{-1/4}=1.19` |
| `hBA` case II | `B_vA_II^{3/4} ≤ 1` (c_B=1) | `scaleFacts_R2`: `B_v ≤ B_s^{1−c}`; product `≤ B_s^{1/4−c} ≤ 1` since `B_s<1` and **`c ≤ 1/4`** (extra hypothesis: `d c<1` alone gives only `c<1/3`; sufficiency only, not claimed necessary) | R3: `0.68`; `c=1/100`: slack exponent `0.24` |
| window (item 4) | `W^{-1} ≤ x_t/x_s` | con ⇒ `x_s>0`, `s<t` (ratio∈(0,1) since `B_t^c>0`); `0≤s<t`; `STBctl_ge`: `B_t≥W^{-d}(g²+1)^{-1}`; so `ratio ≥ (W^d(1+g²))^{-c} ≥ W^{-1}` iff `(1+g²)^c ≤ W^{1−dc}`: needs **`dc<1`, `g²≤𝔡^{-2}` (`WO 𝔡`) and `W→∞`** (not in the ticket list) | sz0: `(W^d(1+g²))^c=1.110 ≤ 32`; at c=0.34 (dc=1.02) the chain gives 34.3>32 (derivation fails; no claim on statement) |
| `st_EKWin` | `STEKWin` | `0≤s`, `s≤t`, `t≤1−g²/L²` (= `STCaseI`), `t<1`, window (above) | all fields given or derived |
| `st_conStInd_sub` | `B_{t'}^c ≤ B_t^c ≤ x_t/x_s ≤ x_{t'}/x_{s'}` | `STBctl_mono` (`t'≤t<1`); `x_t x_{s'} ≤ x_{t'} x_s` (`x_t≤x_{t'}`, `x_{s'}≤x_s`); `<1`: `x_{t'}<x_{s'}` from `s'<t'`, `x_{s'}>0` needs **`t<1`** | R2 sub-pair: ratio 0.9995 |
| split `u_n=1−g²/L²` | I on `[s,min(t,u)]`, II on `[max(s,u),t]` | `STCaseI`: `g²/L²=x_u≤x_{min(t,u)}`; `STCaseII`: `x_{max(s,u)}≤x_u`: both unconditional. Con via `sub`: part I needs strictness `s<min(t,u)` iff **`s_n<u_n`** (given `s<t` from con); part II needs `max(s,u)<t` iff **`u_n<t_n`**. These two hypotheses (∀n) are how the statements avoid the empty window | sample s<u<t: both con's hold (0.981≤0.997, 0.981≤0.996) |
| `c` choice | composers: `min(1/100,1/(2d))` | hscale: any `c>0`; hBA_II: `c≤1/4`; window: `dc<1`; all hold at d=3: `c=1/100`, `1/6` | d=3: `dc=0.03` vs 1; `c` vs `1/4`: 0.24 |
| instance `c` at `szB` | `c=1/10` | con on `szB` needs `B_t^c ≤ 1/2`, `B_t∝W^{-3}`: smallest `n`: c=1/10 → n=7 (case I), 8 (case II); c=1/100 → n≈1.1e10, 1.2e10 | use `c=1/10` (`dc=0.3`, `c≤1/4`) so the eventual witness is `n≥8`, not astronomical |
| `st_Bctl_ge` (copied) | `B_u ≥ N^{-2}`, `u∈[0,1]` | `W^{-d}≥N^{-1}`, `(g²+1)^{-1}≥(Λ²+1)^{-1}`, `N≥Λ²+1` | sz0, Λ=10: `3.1e-5 ≥ 2.3e-13` |
| `st_iterate`, `st_bootRHS_one` | pure induction / `simp` | no exponents | n/a |

### (ii) One concrete nondegenerate instance
Command (scripts in my scratchpad dir `T2058/`, python only): `python3 pre.py | cut -c1-190`. Instance: `sz0` n=0 (`d=3, L=4, W=32, ilambda=1/64, 𝔡=1/10`, R2–R4 pairs of T2041 (a)(ii)), `c=1/100`, r∈{2,3,10,50,100}, `k=k_min`; `szB` (`L=4, W=n+4, ilambda=1`) at `n=8, c=1/10`. All hypotheses (con, regime, WO, `|E|<2` irrelevant to numbers, `t<1`) hold at once; `Ψ` is evaluated at the extreme pair `q=(s,t)` (max `ρ`). External hypotheses: none (con, `WO`, `STRegIterI` are merged structural predicates); their limits are in the last lines (con at `szB`: `B_t^c→0`, `n0` listed; at `sz0` with `sInst,tInst`: `B_{1/16}^{1/100}=0.902 ≤ 15/16`).
```
sz0 n=0: d=3 L=4 W=32 g=1/64 cd=0.0100 d*cd=0.030 g^2=2.4414e-04 g^2/L^2=1.5259e-05 A_I=g^2W^d=8.000
R2 case(i)  1-t=0.0001 1-s=0.0001002 regime=True con:0.97658<=0.99800<1 True; Bt>=1/(2A) True; Bs<=Bt<1 True; A=8.000>=1 True; ratio<=Bt^-cd<=(2A|A)^cd True
   r=  2 k_min= 3 2+8cd(r-1)=2.08<k True; Psi=8.4322 <= c*A^(3/4)=9.5467 (c=2.0070) True
   r=  3 k_min= 3 2+8cd(r-1)=2.16<k True; Psi=8.4395 <= c*A^(3/4)=9.5801 (c=2.0140) True
   r= 10 k_min= 3 2+8cd(r-1)=2.72<k True; Psi=8.4914 <= c*A^(3/4)=9.8199 (c=2.0644) True
   r= 50 k_min= 6 2+8cd(r-1)=5.92<k True; Psi=6.6116 <= c*A^(3/4)=11.4375 (c=2.4044) True
   r=100 k_min=10 2+8cd(r-1)=9.92<k True; Psi=5.4815 <= c*A^(3/4)=14.2048 (c=2.9862) True
   hBA: B_t*A^(3/4)=0.4445<=c=2.0 True; I:2A^-1/4=1.1892 / II: B_s^(1/4-cd)=0.5661<=1
R3 case(ii) 1-t=5e-06 1-s=5.015e-06 regime=True con:0.98488<=0.99701<1 True; Bt>=1/(2A) n/a; Bs<=Bt<1 True; A=4.596>=1 True; ratio<=Bt^-cd<=(2A|A)^cd True
   r=  2 k_min= 3 2+8cd(r-1)=2.08<k True; Psi=5.7411 <= c*A^(3/4)=6.2782 (c=2.0000) True
   r=  3 k_min= 3 2+8cd(r-1)=2.16<k True; Psi=5.7489 <= c*A^(3/4)=6.2782 (c=2.0000) True
   r= 10 k_min= 3 2+8cd(r-1)=2.72<k True; Psi=5.8042 <= c*A^(3/4)=6.2782 (c=2.0000) True
   r= 50 k_min= 6 2+8cd(r-1)=5.92<k True; Psi=4.8348 <= c*A^(3/4)=6.2782 (c=2.0000) True
   r=100 k_min=10 2+8cd(r-1)=9.92<k True; Psi=4.0578 <= c*A^(3/4)=6.2782 (c=2.0000) True
   hBA: B_t*A^(3/4)=0.6839<=c=1.0 True; I:2A^-1/4=1.3659 / II: B_s^(1/4-cd)=0.6935<=1
R4 case(ii) 1-t=3e-06 1-s=3.009e-06 regime=True con:0.98744<=0.99701<1 True; Bt>=1/(2A) n/a; Bs<=Bt<1 True; A=3.547>=1 True; ratio<=Bt^-cd<=(2A|A)^cd True
   r=  2 k_min= 3 2+8cd(r-1)=2.08<k True; Psi=4.7973 <= c*A^(3/4)=5.1690 (c=2.0000) True
   r=  3 k_min= 3 2+8cd(r-1)=2.16<k True; Psi=4.8039 <= c*A^(3/4)=5.1690 (c=2.0000) True
   r= 10 k_min= 3 2+8cd(r-1)=2.72<k True; Psi=4.8510 <= c*A^(3/4)=5.1690 (c=2.0000) True
   r= 50 k_min= 6 2+8cd(r-1)=5.92<k True; Psi=4.1738 <= c*A^(3/4)=5.1690 (c=2.0000) True
   r=100 k_min=10 2+8cd(r-1)=9.92<k True; Psi=3.5647 <= c*A^(3/4)=5.1690 (c=2.0000) True
   hBA: B_t*A^(3/4)=0.7299<=c=1.0 True; I:2A^-1/4=1.4574 / II: B_s^(1/4-cd)=0.7380<=1
all Psi checks: True
--- window (1-t)/(1-s)>=1/W, lower bound B_t>=W^-d/(g^2+1) ---
R1: ratio=0.98039>=B_t^cd=0.91230>=lb^cd=0.90125>=1/W=0.03125  True
R2 case(i) : ratio=0.99800>=B_t^cd=0.97658>=lb^cd=0.90125>=1/W=0.03125  True
R3 case(ii): ratio=0.99701>=B_t^cd=0.98488>=lb^cd=0.90125>=1/W=0.03125  True
R4 case(ii): ratio=0.99701>=B_t^cd=0.98744>=lb^cd=0.90125>=1/W=0.03125  True
(W^d(1+g^2))^cd =1.110 <= W=32 : True (needs d*cd<1: 0.03)
sharpness of the derivation only: cd=0.34, d*cd=1.02>1: (W^d(1+g^2))^cd=34.30 > W=32 : True
--- sub-interval (1-t)(1-s') <= (1-t')(1-s) ---
R2 [s,t] -> [s',t'] 1-s'=0.0001001 1-t'=0.00010005: B_t'^cd=0.97657<=0.99950<1 True ; product ineq True
--- split at u=1-g^2/L^2 ---
1-u=1.52588e-05; s=1-1.53e-05<u<t=1-1.52e-05: True
[s,min(t,u)=u] caseI: g^2/L^2<=1-u True; con: B_u^cd=0.98114<=(1-u)/(1-s)=0.99731<1 True
[max(s,u)=u,t] caseII: 1-u<=g^2/L^2 True; con: B_t^cd=0.98114<=(1-t)/(1-u)=0.99615<1 True
full: B_t^cd=0.98114<=(1-t)/(1-s)=0.99346<1 True
--- st_Bctl_ge (copied helper): W^-d B_u >= N^-2, u in [0,1], Lambda=1/dd=10 ---
N=2097152 Lambda^2+1=101<=N True ; min over u (x=1): B=3.0987e-05 >= N^-2=2.2737e-13 True
--- szB (d=3,L=4,lam=1,W=n+4): con_st_ind eventual witness, cd=1/10 and 1/100 ---
  (7/8,15/16) case(i), 1-s<=g^2:1/8<=1, 1-t=g^2/L^2:1/16: cd=0.1: smallest n with B_t^cd<=1/2: n0=7 (W=11)
  (7/8,15/16) case(i), 1-s<=g^2:1/8<=1, 1-t=g^2/L^2:1/16: cd=0.01: smallest n with B_t^cd<=1/2: n0=11472512971 (W=11472512975)
  (15/16,31/32) case(ii), 1-s=g^2/L^2:1/16: cd=0.1: smallest n with B_t^cd<=1/2: n0=8 (W=12)
  (15/16,31/32) case(ii), 1-s=g^2/L^2:1/16: cd=0.01: smallest n with B_t^cd<=1/2: n0=12304834824 (W=12304834828)
  n=8 W=12 I  WO(dd=1/10): W^(-3/2+dd)=0.031<=lam=1<=10; A=1728.000 B_t^cd=0.4829<=1/2 True; Psi<=cA^(3/4) at r=2,3,10,50,100 (k=kmin): True ; B_t*A^(3/4)=0.1848<=2
  n=8 W=12 II WO(dd=1/10): W^(-3/2+dd)=0.031<=lam=1<=10; A=1450.667 B_t^cd=0.4931<=1/2 True; Psi<=cA^(3/4) at r=2,3,10,50,100 (k=kmin): True ; B_t*A^(3/4)=0.1999<=1
--- sz0 s=0,t=1/16 (sInst,tInst), window: ratio=15/16 ; B_t^cd<=15/16 at n=0: W=32 L=4 Bt=3.3052e-05 Bt^(1/100)=0.9020<=0.9375 True; 1/W=3.125e-02<=0.9375
```
Verdict per target (math preflight):
- Item 1 `st_kmin`, `st_hscale_I`, `st_hscale_I'`: **PASS** (hypotheses: `STRegIterI`, con, `WO 𝔡`, `t<1`, `|E|<2`, `c>0`; `c_I=1+2^{c(r−1)}`).
- Item 2 `st_hscale_II`, `st_hscale_II'`: **PASS** (`A≥1` comes from con; `c_II=2`).
- Item 3 `st_hBA_I`: **PASS** with extra hypothesis `2 ≤ d` (`L^d ≥ L²`); `st_hBA_II`: **PASS** with extra hypothesis `c ≤ 1/4` and no range condition (reason in the table: `B_s<1` from con). The ticket's `scaleFacts_R1` range is not needed.
- Item 4 `st_window`: **PASS** with extra hypotheses `WO 𝔡` and `Tendsto W atTop atTop` (not only `d c<1`, `0≤s`, `t<1`); `st_EKWin`: **PASS** (adds `s≤t`, `STCaseI`).
- Item 5 `st_conStInd_sub`: **PASS** with `∀ n, t n<1`; split: **PASS** with hypotheses `∀ n, s n<u n` (part I) and `∀ n, u n<t n` (part II).
- Item 6 helper copies: **PASS** (no mathematics beyond the above; the `STBctl_ge` name of merged `ScaleFacts` is a different statement from probe `st_Bctl_ge`).
- Instances at `szB`: use `c=1/10` (not the composers' `1/100`) so the `∀ᶠ` witness is `n≥8`.
- Paper-delta candidates (for 1b to confirm): `T2058a` (hBA_II: `c≤1/4`), `T2058b` (window needs `WO` and `W→∞`), `T2058c` (hBA_I needs `d≥2`).

## (b) Script output (generated Sat Oct  3 14:56:47 UTC 2026)

### b.1 Build, registry pre-check, axioms
```
$ git log --oneline -1 && git diff --stat main...t/T2058
c1ef5fb T2058: S3-23 deterministic scale facts of Steps 3-4 (RBM3D/Induction/ScaleFacts3)
 RBM3D/Induction/ScaleFacts3.lean | 642 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 642 insertions(+)
$ lake env lean RBM3D/Induction/ScaleFacts3.lean 2>&1 | wc -l; (exit code)   # no warning, no error
0 exit=0
$ lake build RBM3D.Induction.ScaleFacts3 2>&1 | tail -1
Build completed successfully (3706 jobs).
$ lake env lean scratchpad/T2058/precheck.lean   # import RBM3D; import RBM3D.Induction.ScaleFacts3; #assert_rbm_axioms
exit=0
axiom audit: 1815 theorems, 814 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 49 (borrowed 2, owed 34, structural 13).
-- baseline, import RBM3D only:
axiom audit: 1800 theorems, 813 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake build 2>&1 | tail -1   # whole library (root RBM3D.lean does not yet import the new module: hub adds it at merge)
Build completed successfully (3771 jobs).
$ lake env lean scratchpad/T2058/axioms.lean   # #print axioms of the 16 public declarations of the file: count with / without exactly the 3 standard axioms
16  /  0  /  0   (3-axiom decls / other / sorry|admit|native_decide|axiom hits in the file)
```

### b.2 Verbatim copies from the probe (script diff of the three declarations, docstring included)
```
$ python3 scratchpad/T2058/vdiff.py   # block(probe 3c58211, name) == block(ScaleFacts3.lean, name)
st_Bctl_ge : probe 39 lines, ScaleFacts3 39 lines, IDENTICAL
st_bootRHS_one : probe 6 lines, ScaleFacts3 6 lines, IDENTICAL
st_iterate : probe 17 lines, ScaleFacts3 17 lines, IDENTICAL
```

### b.3 Target statements (extracted from the file by script: `theorem NAME` to the line ending `:=`/`:= by`)
```
def st_kmin (𝔠d : ℝ) (r : ℕ) : ℕ := ⌊2 + 8 * 𝔠d * ((r : ℝ) - 1)⌋₊ + 1
theorem st_hscale_I {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (h𝔠d : 0 < 𝔠d) (hreg : STRegIterI sz s t)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAI n) (etaT (E n) (s n) / etaT (E n) q.1.2) r (st_kmin 𝔠d r) ≤
        c * sz.STAI n ^ (3 / 4 : ℝ) := by …
theorem st_hscale_II {E s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAII s n) (etaT (E n) (s n) / etaT (E n) q.1.2) r (st_kmin 𝔠d r) ≤
        c * sz.STAII s n ^ (3 / 4 : ℝ) := by …
theorem st_hscale_I' {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (h𝔠d : 0 < 𝔠d) (hreg : STRegIterI sz s t)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) :
    ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAI n) (etaT (E n) (s n) / etaT (E n) q.1.2) r k ≤ c * sz.STAI n ^ (3 / 4 : ℝ) :=
theorem st_hscale_II' {E s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) :
    ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAII s n) (etaT (E n) (s n) / etaT (E n) q.1.2) r k ≤ c * sz.STAII s n ^ (3 / 4 : ℝ) :=
theorem st_hBA_I {s t : ℕ → ℝ} {𝔡 : ℝ} (hd : 2 ≤ d) (hcase : STCaseI sz s t) (hWO : sz.WO 𝔡) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      sz.Bctl n (v : ℝ) * sz.STAI n ^ (3 / 4 : ℝ) ≤ c := by …
theorem st_hBA_II {s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 4)
    (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      sz.Bctl n (v : ℝ) * sz.STAII s n ^ (3 / 4 : ℝ) ≤ c := by …
theorem scaleFacts3_W_tendsto {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by …
theorem st_window {𝔠d 𝔡 : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡)
    (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ)⁻¹ ≤ (1 - t n) / (1 - s n) := by …
theorem st_EKWin {𝔠d 𝔡 : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡)
    (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hcase : STCaseI sz s t) (ht1 : ∀ n, t n < 1) :
    STEKWin sz s t :=
theorem st_conStInd_sub {𝔠d : ℝ} {s t s' t' : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (hs : ∀ n, s n ≤ s' n) (hst : ∀ n, s' n < t' n) (ht : ∀ n, t' n ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.STConStInd 𝔠d s' t' := by …
theorem st_split_I {𝔠d : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hst : ∀ n, s n < t n)
    (hsu : ∀ n, s n < 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) :
    STCaseI sz s (fun n => min (t n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) ∧
      sz.STConStInd 𝔠d s (fun n => min (t n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) := by …
theorem st_split_II {𝔠d : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hst : ∀ n, s n < t n)
    (hut : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < t n) :
    STCaseII sz (fun n => max (s n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) t ∧
      sz.STConStInd 𝔠d (fun n => max (s n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) t := by …
```

### b.4 Compiled nonempty instances (the `example`s of section 6; first line and proof term of each; the omitted type lines are the theorem's conclusion at the data)
```
example : st_kmin (1 / 100) 2 = 3 ∧ st_kmin (1 / 100) 3 = 3 ∧ st_kmin (1 / 100) 10 = 3 ∧  ...
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [st_kmin, Nat.floor_eq_iff]
example (r : ℕ) (hr : 2 ≤ r) :  ...
  st_hscale_I szB (E := STflowE zB) (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) szB_regIterI
    (szB_conI (by norm_num)) szB_WO (fun _ => by norm_num) zB_abs_E r hr
example : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,  ...
  st_hscale_I' szB (E := STflowE zB) (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) szB_regIterI
    (szB_conI (by norm_num)) szB_WO (fun _ => by norm_num) zB_abs_E
example (r : ℕ) (hr : 2 ≤ r) :  ...
  st_hscale_II szB (E := STflowE zB) (𝔠d := 1 / 100) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num) zB_abs_E r hr
example : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,  ...
  st_hscale_II' szB (E := STflowE zB) (𝔠d := 1 / 100) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num) zB_abs_E
example : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,  ...
  st_hBA_I szB (𝔡 := 1 / 10) (by norm_num) szB_regIterI.1 szB_WO
example : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,  ...
  st_hBA_II szB (𝔠d := 1 / 100) (by norm_num) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num)
example : ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ)⁻¹ ≤ (1 - tInst n) / (1 - sInst n) :=
  st_window sz0 (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) (by norm_num) (sz0_con _ (by norm_num)) sz0_WO
    W_tendsto_sz0 sz0_hs0 (fun n => by simp only [tInst]; norm_num)
example : STEKWin sz0 sInst tInst :=
  st_EKWin sz0 (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) (by norm_num) (sz0_con _ (by norm_num)) sz0_WO
    (scaleFacts3_W_tendsto sz0 sz0_admissible) sz0_hs0 (fun n => (sz0_hst n).le) sz0_caseI
    (fun n => by simp only [tInst]; norm_num)
example : szB.STConStInd (1 / 100) (fun _ => 29 / 32) (fun _ => 59 / 64) :=
  st_conStInd_sub szB (by norm_num) (szB_conI (by norm_num)) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
example :=
  st_split_I szB (𝔠d := 1 / 100) (s := fun _ => 7 / 8) (t := fun _ => 31 / 32) (by norm_num) szB_con_wide
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => by simp [szB]; norm_num)
example :=
  st_split_II szB (𝔠d := 1 / 100) (s := fun _ => 7 / 8) (t := fun _ => 31 / 32) (by norm_num) szB_con_wide
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => by simp [szB]; norm_num)
example : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((szB.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ szB.Bctl n u :=
  st_Bctl_ge szB (Λ := 1) (tendsto_size szB szB_tendsto)
    (Eventually.of_forall fun n => ⟨by simp [szB], by simp [szB]⟩)
example : STbootRHS 1 (fun _ => 1) (fun _ => 1) (1 / 2) 3 2 =  ...
  st_bootRHS_one 1 (1 / 2) 3 2
example : ∀ k r, 2 ≤ r → 2 ≤ r + k :=
  st_iterate (S := fun r k => 2 ≤ r + k) (fun r hr => by omega) (fun n k hn _ _ _ => by omega)
```

### b.5 Hypothesis necessity (compiled negative, scratch file, not committed) and name clashes
```
$ lake env lean scratchpad/T2058/neg_window.lean   # szW1: L=3, W=1, ilambda=1, d=3: con_st_ind at (0,1/1000), 𝔠d=1/100 and WO(1/10) hold, window fails
'szW1_con' : [propext, Classical.choice, Quot.sound]
'szW1_WO' : [propext, Classical.choice, Quot.sound]
'szW1_no_window' : [propext, Classical.choice, Quot.sound]
$ for n in <every new name>; do git grep -n -w -F -- "$n" main -- RBM3D/*.lean RBM3D.lean | wc -l; done   # matches on main (a68a954)
st_kmin=0 st_hscale_I=0 st_hscale_II=0 st_hscale_I'=0 st_hscale_II'=0 st_hBA_I=0 st_hBA_II=0 st_window=0 st_EKWin=0 st_conStInd_sub=0 st_split_I=0 st_split_II=0 st_iterate=0 st_Bctl_ge=0 st_bootRHS_one=0 scaleFacts3_W_tendsto=0 st_WO_pos=0 st_WO_AI=0 st_con_aux=0 st_rho_le=0 st_BI_lower=0 st_psi_core=0 st_kmin_gt=0 ScaleFacts3Inst=0 zB_abs_E=0 szB_conI=0 szB_conII=0 szB_con_wide=0
```

### b.6 Narrative
Result: items 1-6 are in `RBM3D/Induction/ScaleFacts3.lean` (commit c1ef5fb on `t/T2058`, one file); the module build, the registry pre-check and the
whole-library build succeed; all 16 public declarations carry exactly the three standard axioms; no new hypothesis `Prop` (every hypothesis is a merged structural
predicate: `STRegIterI`, `STCaseI`, `STConStInd`, `WO`, `Admissible`), so `Test/Axioms.lean` is untouched; no RBM2D source (portmap: "new"), so no port diff.
Proofs are real-variable algebra on the merged `STBctl_pos/mono/ge`, `scaleFacts_etaT_div_etaT`, `scaleFacts_R2`, `Sizes.lam_sq_mul_pow_ge`.
Constants in the Lean statements: `hscale` I `c = 1 + (2^𝔠d)^(r-1)`, II `c = 2`; `hBA` I `c = 2`, II `c = 1`; section (a) predicted all four.
Differences from the ticket text (each a mathematical condition, none weakens a conclusion; `STIterR` carries `3 ≤ d` and `𝔠d ≤ 1/100`, `STFlow` carries `Admissible`):
1. `st_hBA_I`: extra `2 ≤ d` (used for `L^d ≥ L²`); regime hypothesis is `STCaseI` (weaker than `STRegIterI`, which contains it); no `t < 1`.
2. `st_hBA_II`: no range hypothesis; `Bctl < 1` comes from `(con_st_ind)` (`B_s ≤ B_t < 1`, private `st_con_aux`); instead `𝔠d ≤ 1/4`
   (`1/4 - 𝔠d ≥ 0` in `B_s^{1/4-𝔠d} ≤ 1`); `STIterR` has `𝔠d ≤ 1/100` (`Step34Pins.lean:481`). Sufficiency only, necessity not studied.
3. `st_window`: besides `d 𝔠d < 1`, `0 ≤ s`, `t < 1` it needs `(eq:WO)` (`ilambda ≤ 𝔡⁻¹`) and `W → ∞`; b.5 compiles the negative (`W ≡ 1`: every other
   hypothesis holds, window false). `STFlow` carries `Admissible` (`Defs.lean:286`), from which `scaleFacts3_W_tendsto` gives `W → ∞`.
4. `st_hscale_II` does not use `STCaseII` (the regime enters only through `A = STAII`): `A ≥ 1` and `ρ ≤ A^𝔠d` follow from `(con_st_ind)`, `t < 1`.
5. `st_conStInd_sub`/splits take `∀ n` order hypotheses; the splits need `s n < u n` (part I) and `u n < t n` (part II): at equality the window is a point and
   `(1-t')/(1-s') < 1` fails, so the statements do not cover that endpoint; `s n < t n` is a hypothesis (`(con_st_ind)` gives it only eventually).
6. `st_kmin` uses real subtraction `(r : ℝ) - 1`; for `r ≥ 2` it is `⌊2 + 8 𝔠d (r - 1)⌋₊ + 1`, so `st_kmin (1/100) r = 3, 3, 3, 6, 10` at `r = 2, 3, 10, 50, 100` (b.4).
Instances: `𝔠d = 1/100` at `szB` (not (a)'s `1/10`): merged `conStInd_const` gives `(con_st_ind)` for every `𝔠d > 0`, so no numeric witness `n ≥ 8` is needed.
Private instance helpers (not printed): `szB_conI/II := conStInd_const szB szB_W_tendsto ..`, `zB_abs_E := abs_lemE_lt_two ..`, `szB_con_wide` (same, `(7/8, 31/32)`).
The split instance is at `[7/8, 31/32]` with `u = 15/16`, which lies strictly inside; `st_conStInd_sub` goes `[7/8,15/16] → [29/32,59/64]`.
Extra public name: `scaleFacts3_W_tendsto` (file-stem prefix, for the composers S3-24a/b, S3-25, S3-26); all other helpers are `private`.

## (c) Verified Mathlib names used (each occurs in the compiled file; count of occurrences; `Real.pow_rpow_inv_natCast` only in the scratch negative)
Nat.lt_floor_add_one (1) | Nat.floor_eq_iff (1) | Nat.cast_sub (1) | Real.rpow_le_rpow (3) | Real.rpow_le_rpow_of_nonpos (2)
Real.rpow_le_rpow_of_exponent_le (2) | Real.rpow_add (3) | Real.rpow_mul (2) | Real.rpow_natCast (3) | Real.rpow_neg (5) | Real.inv_rpow (5)
Real.mul_rpow (2) | Real.one_le_rpow (2) | Real.rpow_le_one (1) | Real.rpow_pos_of_pos (4) | Real.rpow_nonneg (5) | Real.rpow_one (1)
one_le_inv₀ (1) | inv_anti₀ (8) | div_le_div_of_nonneg_left (1) | div_le_div_iff₀ (1) | div_lt_one (2) | div_pos_iff (1) | pow_le_pow_left₀ (2)
pow_le_pow_right₀ (1) | tendsto_rpow_atTop (2) | Filter.Tendsto.eventually_ge_atTop (1) | tendsto_atTop_mono' (1) | Filter.Eventually.exists (1)
inv_pos (1) | inv_div (1) | mul_inv (2) | lt_min (1) | max_lt (1)
Verified absent / deprecated: none invented; `push_neg` is deprecated in this Mathlib (replaced by `not_lt`).

## (d) Open issues and paper-delta candidates
Open issues: none blocking. The hub adds `import RBM3D.Induction.ScaleFacts3` after the last import of `RBM3D.lean` at merge. Composers must supply `∀ n, |E n| < 2`
(`abs_lemE_lt_two` with `0 < (z n).im`), `W → ∞` (`scaleFacts3_W_tendsto` from `STFlow.1`), `𝔠d ≤ 1/4` for `hBA` II, and the strict `s n < u n`, `u n < t n` for the splits.
`st_hBA_II` is sufficient only: `d 𝔠d < 1` alone gives `𝔠d < 1/3` at `d = 3`, and whether `𝔠d ∈ (1/4, 1/3)` also works was not studied.
Paper-delta candidates:
- T2058a: `hBA` case (ii) (`3_5:1577-1595`, details omitted in the paper) is proved with explicit `𝔠d ≤ 1/4` and `Bctl < 1` derived from `(con_st_ind)`.
- T2058b: the window `(1-t)/(1-s) ≥ W⁻¹` of `lem:sum_decay` (`3_5:1633-1637`) follows from `(con_st_ind)` only with `d 𝔠d < 1`, `(eq:WO)` and `W → ∞` (compiled negative b.5).
- T2058c: `hBA` case (i) (`3_5:1396`) uses `2 ≤ d` (`L^d ≥ L²`); the paper has `d ≥ 3`, so no loss.
- T2058d: explicit depth `k_min = ⌊2 + 8 𝔠d (r - 1)⌋ + 1` and constants `Ψ ≤ (1 + 2^{𝔠d(r-1)}) A^{3/4}` (i), `2 A^{3/4}` (ii) for the paper's "k large enough" (`3_5:1431`).
- T2058e: the case split at `u = 1 - ilambda²/L²` (`3_5:1104-1105`) is stated with strict `s < u` (part I) and `u < t` (part II) so both sub-windows are nonempty.
