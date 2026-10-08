Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 18:56:50 UTC 2026

Scripts (Python, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2341`; `poly_head_lib.py` (integrand `h`, quadrature), `poly_head2.py`, `inst.py`.
Notation: `n ∈ {1,2}` (first/second difference), `p = d+n-2` (target decay `(|a|+1)^{-(d-1)}` resp. `^{-d}`), `q = (d+n)/2`, `M = ⌊d/2⌋+1`, `A = |a|`, `ε = (1-t)/γ`, `γ = t g²`,
`h(τ) = min(1, τ^{-q}) (1 + A²/max(τ,1))^{-M}`; the head of `kBA_diff{1,2}_le` is `C h(τ)` (KHeatDiff.lean:1573-1599).

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `d` | `≥ 3` (pin) | `kBA_diff*_le` needs `2 ≤ d`; `kBA_gap` needs `0 < d` | 1 |
| `p` | `d-1` (n=1), `d` (n=2) | equals the pinned decay; `p ≥ 2` | d=3,n=1: p=2 (0) |
| `q-1` | `(d+n-2)/2 = p/2` | `> 0` (`u→∞` end and `∫_{A²}^∞ τ^{-q}`) | `≥ 1` |
| `M` | `⌊d/2⌋+1` (KHeatDiff.lean:1573) | `M-q+1 > 0` (`τ→0` end of `∫_1^{A²} τ^{M-q}`) | `M-q+1 ≥ 1/2` (n=2, d odd), table (a) below |
| `2M-p` | `(2⌊d/2⌋-d)+4-n` | `≥ 0` (head on `(0,1]` and sup bound: `(1+A²)^{-M} ≤ A^{-2M} ≤ A^{-p}`) | `≥ 1` |
| head integral `∫_0^∞ h` | `≤ 5 A^{-p}` for `A ≥ 1`; `≤ 1 + 1/(q-1) ≤ 2` for `A < 1` | `∫_0^1 ≤ A^{-2M}`; `∫_1^{A²} τ^{M-q}A^{-2M} ≤ A^{-p}/(M-q+1)`; `∫_{A²}^∞ τ^{-q} = A^{-p}/(q-1)` (pointwise, no substitution/Beta needed) | `1+2+2 = 5` |
| `sup_τ h` | `≤ A^{-p}` for `A ≥ 1`; `≤ 1` for `A < 1` | `τ<1`: `A^{-2M}`; `1≤τ<A²`: `τ^{M-q}A^{-2M} ≤ max(A^{-2q}, A^{-2M})`; `τ≥A²`: `A^{-2q}`; all `≤ A^{-p}` | `(A+1)^p ≤ 2^p max(1,A^p)` |
| lemma constant `C_P` | `5·2^p·C_A` | `γ⁻¹∫e^{-ετ}h ≤ C_P (g²+e)⁻¹(A+1)^{-p}`, `e = 1-t` | see (b) |
| `ε<1` branch | `γ⁻¹ ∫e^{-ετ}h ≤ γ⁻¹ ∫h`, `1/γ ≤ C_A/(g²+e)` (`baP5_convA` 2nd conjunct) | uses nothing about `ε` beyond `ε<1` | — |
| `ε≥1` branch | `γ⁻¹∫e^{-ετ}h ≤ γ⁻¹ ε⁻¹ sup h = e⁻¹ sup h`, `1/e ≤ C_A/(g²+e)` (1st conjunct) | **`sup h ≤ C (A+1)^{-p}`, not `(A+1)^{-(d+n)}`** (ticket step (2) wording is false: see (b'), d=3, n=2, `sup·(A+1)^5 = 10005` at `A=10⁴`) | `2M-p ≥ 1` |
| `C_A` | `3+2Λ²` (`baP5_convA`, Prop5.lean:170); `203` at `Λ=10` | `ε≥1 → 1/(1-t) ≤ C_A/(g²+1-t)`; `ε<1 → 1/γ ≤ C_A/(g²+1-t)` for `0<g≤Λ`, `0<t<1` | checked (ii) |
| tail (`τ ≥ L²`) | `kBA_gap` conjuncts 2, 3: `C L^{-(d+n)} e^{-cτ/L²}` (KHeat.lean:989) | `γ⁻¹L^{-m}min(1/ε, L²/c) ≤ C_T (g²+e)⁻¹(A+1)^{-p}`, `m = p+2`, via `2A ≤ dL` (`pu_zdistD_two_le`), `L^{-p} ≤ (d/2+1)^p (A+1)^{-p}`, band `pu_tail` (:239) verbatim, `C_T = C_A (d/2+1)^p (1+1/c)` | `m-p = 2` |
| `t = 0` | `Θ_0 = 1` (`baP5_Theta_zero`); `pu_t0_bound` (:695) with exponent `p ≤ d` | `D ≤ 4`, `D = 0` for `|a| > 2`; const `4(Λ²+1)3^d` | `d-p ≥ 0` (0 at n=2) |
| `L`, `τ`-window | `L ≥ 3`, head window `(0, L²]`, `L² ≥ 9` | window nondegenerate | `L²-1 ≥ 8` |
| §29 (1)–(4) | (1) `0 ≤ t < 1` is in the pin, `t = 0` is its own branch; (2) the regime-(ii) boundary is `τ = L²`, no `ilambda` here; (3) no `L ≤ W^K` used; (4) no `n`/`N` in the pins (`L ≥ 3` for all `L`) | — | — |
| external hypotheses | none: `kBA_diff1_le`, `kBA_diff2_le`, `kBA_gap`, `BATheta_eq_laplace_kBA` are merged theorems | no limit computation needed | — |

Substitution table band `Propagator/PropUnit.lean` → BA (band line → BA name, file:line):
- `Theta_eq_laplace_prod` (:461, in `pu_Theta_eq` :454) → `BATheta_eq_laplace_kBA` (KHeat.lean:540; needs `BASelf` = `hr.1`, `0 ≤ t < 1`); the `τ = γs` step is `baP5_theta_eq` (Prop5.lean:146).
- `lgGam/lgEps` (:458-472, 481-485, 503-508, 549-582) → `baP5Gam/baP5Eps` (Prop5.lean:78/81; `γ = t g²`, same `ε = (1-t)/γ`); band `hεγ` (:469) ↔ `baP5_gam_mul_eps` (:91).
- `kProd_diff1_le`/`diff2_le` (:749, :828) → `kBA_diff1_le`/`kBA_diff2_le`; the head becomes `C min 1 (τ^{-(d+n)/2}) (1+A²/max τ 1)^{-M}`, no `cK`/`exp` factor, so `pu_head`, `pu_lg_nonneg` (:317) and the head hypothesis of `pu_int_bound` (:325) change; `hhead` at :815, :910.
- `kProd_gap` (:750, :829; used `.2.1` :819, `.2.2` :915) → `kBA_gap` (same conjunct layout, extra args `g E m hr`).
- `lg_convA` (:549) → `baP5_convA` (no `d` argument).
- `lg_bulk` (:136, :552), `lg_zero` (:149, :565) → replaced by the new polynomial lemma and by integrability of `e^{-ετ}h ≤ min(1,τ^{-q})` (`q>1`); `lg_tail` (:362, `pu_int_bound`) kept (kernel-independent, LaplaceGauss.lean:295).
- `pu_kProd_cont/nonneg_le_one/int_K` (:424, :430, :441) → components of `kBA_basic` (KHeat.lean:387) and `baP5_F_integrable` (Prop5.lean:113).
- `pu_Theta_zero` (:679) → `baP5_Theta_zero` (:141); `PropSpin`, `pu_spin_ne` (:718), `prop5Short_holds` (:751, :830), `pu_KS`/`pu_S_*` (:592-675) dropped: the pin has `σ₁ ≠ σ₂` and `baP5_Theta_mixed` (:132) reduces to `(true,false)`.
- Verbatim ports: `pu_zdist_two_le`…`pu_shift` (:68-98), `pu_tail` (:239), `pu_one_norm_le` (:683), `pu_one_eq_zero` (:689), `pu_t0_bound` (:695), `pu_ne_zero` (:731), `pu_norm4` (:739), the `pu_diff1_eq`/`pu_diff2_eq` shape (:477, :497).
- Private names the ticket's edit list does not cover but the proof needs: `baP5_gam_mul_eps` (:91), `baP5_F_integrable` (:113), `baP5_kBA_bounds` (:101), `baP5_kBA_continuous` (:107). Port them as `baPU_*` (or use `kBA_basic`); the allowed list `baP5Gam … baP5_convA` suffices otherwise.

Numerical check of (a) the exponent slacks, (b) the head integral and the sup bound; command `cd $S && python3 poly_head2.py` (verbatim output):
```
(a) exponent slacks, d=3..9, n=1,2:  M-q+1 (need >0), q-1 (need >0), 2M-p (need >=0)
 d=3 M=2 n=1: p=2 q-1=1.0 M-q+1=1.0 2M-p=2  n=2: p=3 q-1=1.5 M-q+1=0.5 2M-p=1
 d=4 M=3 n=1: p=3 q-1=1.5 M-q+1=1.5 2M-p=3  n=2: p=4 q-1=2.0 M-q+1=1.0 2M-p=2
 d=5 M=3 n=1: p=4 q-1=2.0 M-q+1=1.0 2M-p=2  n=2: p=5 q-1=2.5 M-q+1=0.5 2M-p=1
 d=6 M=4 n=1: p=5 q-1=2.5 M-q+1=1.5 2M-p=3  n=2: p=6 q-1=3.0 M-q+1=1.0 2M-p=2
 d=7 M=4 n=1: p=6 q-1=3.0 M-q+1=1.0 2M-p=2  n=2: p=7 q-1=3.5 M-q+1=0.5 2M-p=1
 d=8 M=5 n=1: p=7 q-1=3.5 M-q+1=1.5 2M-p=3  n=2: p=8 q-1=4.0 M-q+1=1.0 2M-p=2
 d=9 M=5 n=1: p=8 q-1=4.0 M-q+1=1.0 2M-p=2  n=2: p=9 q-1=4.5 M-q+1=0.5 2M-p=1
(b) I_eps(A)*(A+1)^p for eps=0,1e-3,1 ; bound 5*2^p ; sup_tau h*(A+1)^p ; sup_tau h*(A+1)^(d+n)
 d=3 n=1 A=   1 I*(A+1)^p =   3.000   2.975   0.836 | 5*2^p= 20 | sup*(A+1)^p= 1.0000 sup*(A+1)^(d+n)=    4.00
 d=3 n=1 A=  10 I*(A+1)^p =   1.210   0.966   0.012 | 5*2^p= 20 | sup*(A+1)^p= 0.0119 sup*(A+1)^(d+n)=    1.44
 d=3 n=1 A= 100 I*(A+1)^p =   1.020   0.086   0.000 | 5*2^p= 20 | sup*(A+1)^p= 0.0001 sup*(A+1)^(d+n)=    1.04
 d=3 n=2 A=   1 I*(A+1)^p =   4.283   4.272   1.601 | 5*2^p= 40 | sup*(A+1)^p= 2.0000 sup*(A+1)^(d+n)=    8.00
 d=3 n=2 A=  10 I*(A+1)^p =   1.957   1.822   0.118 | 5*2^p= 40 | sup*(A+1)^p= 0.1305 sup*(A+1)^(d+n)=   15.79
 d=3 n=2 A= 100 I*(A+1)^p =   1.608   0.519   0.009 | 5*2^p= 40 | sup*(A+1)^p= 0.0103 sup*(A+1)^(d+n)=  105.08
 d=4 n=1 A=   1 I*(A+1)^p =   2.571   2.562   0.830 | 5*2^p= 40 | sup*(A+1)^p= 1.0000 sup*(A+1)^(d+n)=    4.00
 d=4 n=1 A=  10 I*(A+1)^p =   0.523   0.436   0.001 | 5*2^p= 40 | sup*(A+1)^p= 0.0034 sup*(A+1)^(d+n)=    0.42
 d=4 n=1 A= 100 I*(A+1)^p =   0.405   0.020   0.000 | 5*2^p= 40 | sup*(A+1)^p= 0.0000 sup*(A+1)^(d+n)=    0.27
 d=4 n=2 A=   1 I*(A+1)^p =   4.000   3.993   1.592 | 5*2^p= 80 | sup*(A+1)^p= 2.0000 sup*(A+1)^(d+n)=    8.00
 d=4 n=2 A=  10 I*(A+1)^p =   0.732   0.673   0.014 | 5*2^p= 80 | sup*(A+1)^p= 0.0142 sup*(A+1)^(d+n)=    1.72
 d=4 n=2 A= 100 I*(A+1)^p =   0.520   0.081   0.000 | 5*2^p= 80 | sup*(A+1)^p= 0.0001 sup*(A+1)^(d+n)=    1.06
(b') ticket's sup claim sup<=C(A+1)^-(d+n) fails (d=3,n=2): A=1e2,1e3,1e4 -> [105.1, 1005.0, 10005.0]
```

### (ii) One concrete nondegenerate instance

Data (pattern `BA/Prop5.lean:1428`, flow point `P` of `KKernelInst`): `d = 3`, `L = 4` (`L² = 16`), `Λ = 10`, `κ = P.m0.im > 0`, `g = P.g0` with `0 < g ≤ Λ` (fields `P.g0_pos`, `P.g0_le`; only these two facts are used; the value `≈ 4.67` is the comment at Prop5.lean:1418, so the script also tries `g = 10`), `BAReal 3 4 g0 κ E m0 = P.real`, `t ∈ {1/2, 1/100}`, `σ = (true,false)`, `a = (1,0,0)` (`|a| = 1`, `2|a| ≤ dL = 12`), `i = j = 0`. Hypotheses `3 ≤ d`, `0<Λ`, `0<κ`, `3 ≤ L`, `0<g≤Λ`, `0≤t<1`, `σ₁≠σ₂`, `BAReal` all hold at once (`P.real`); `t = 1/2` gives `ε<1`, `t = 1/100` gives `ε ≥ 1` at `g = 4.67`.
Command `cd $S && python3 inst.py` (verbatim output; `head` = `γ⁻¹∫_0^{16} e^{-ετ}h`, compared with the printed bound `C_P (g²+1-t)⁻¹ (A+1)^{-p}`, `C_P = 5·2^p·C_A`):
```
d=3 L=4 L^2=16 Lam=10.0 |a|=1 2|a|<=dL: True  3<=d:True 3<=L:True  M=2  C_A=3+2Lam^2=203.0
 g=4.67 t=0.5: 0<g<=Lam:True 0<=t<1:True gamma=10.9044 eps=0.0459 (<1) convA(203.0) holds:True
    n=1: p=2 2M-p=2>=0:True M-q+1=1.0>0  head gamma^-1*int_0^16=0.05666 <= 45.498:True  L^-p<=(d/2+1)^p(A+1)^-p:True
    n=2: p=3 2M-p=1>=0:True M-q+1=0.5>0  head gamma^-1*int_0^16=0.04466 <= 45.498:True  L^-p<=(d/2+1)^p(A+1)^-p:True
 g=4.67 t=0.01: 0<g<=Lam:True 0<=t<1:True gamma=0.2181 eps=4.5394 (>=1) convA(203.0) holds:True
    n=1: p=2 2M-p=2>=0:True M-q+1=1.0>0  head gamma^-1*int_0^16=0.25207 <= 44.520:True  L^-p<=(d/2+1)^p(A+1)^-p:True
    n=2: p=3 2M-p=1>=0:True M-q+1=0.5>0  head gamma^-1*int_0^16=0.25190 <= 44.520:True  L^-p<=(d/2+1)^p(A+1)^-p:True
 g=10.0 t=0.5: 0<g<=Lam:True 0<=t<1:True gamma=50.0000 eps=0.0100 (<1) convA(203.0) holds:True
    n=1: p=2 2M-p=2>=0:True M-q+1=1.0>0  head gamma^-1*int_0^16=0.01347 <= 10.100:True  L^-p<=(d/2+1)^p(A+1)^-p:True
    n=2: p=3 2M-p=1>=0:True M-q+1=0.5>0  head gamma^-1*int_0^16=0.01033 <= 10.100:True  L^-p<=(d/2+1)^p(A+1)^-p:True
 g=10.0 t=0.01: 0<g<=Lam:True 0<=t<1:True gamma=1.0000 eps=0.9900 (<1) convA(203.0) holds:True
    n=1: p=2 2M-p=2>=0:True M-q+1=1.0>0  head gamma^-1*int_0^16=0.21053 <= 10.051:True  L^-p<=(d/2+1)^p(A+1)^-p:True
    n=2: p=3 2M-p=1>=0:True M-q+1=0.5>0  head gamma^-1*int_0^16=0.20138 <= 10.051:True  L^-p<=(d/2+1)^p(A+1)^-p:True
```
No external hypothesis occurs (all inputs are merged theorems), so no separate limit computation is needed.

### Verdict

- `baPropUnit1mixed_holds` (n=1, `p = d-1`): **PASS** (all exponents close; `2M-p ≥ 2`, `M-q+1 ≥ 1`).
- `baPropUnit2mixed_holds` (n=2, `p = d`): **PASS** (`2M-p ≥ 1`, `M-q+1 ≥ 1/2`: tight but positive for every `d ≥ 3`).
- New Laplace lemma `γ⁻¹ ∫ e^{-ετ} h ≤ C_P (g²+e)⁻¹(A+1)^{-p}` (integral over `(0,∞)`, hence over `(0,L²]` since `h ≥ 0`): **PASS**, with correction C1.
- C1 (ticket step (2), `ε`-side): the sup bound needed is `sup_τ h ≤ C (A+1)^{-(d+n-2)}`; the stated `(A+1)^{-(d+n)}` is false (b'). The lemma as stated in the ticket is unaffected.
- C2: the ticket's `private`-deletion list omits `baP5_gam_mul_eps`, `baP5_F_integrable`, `baP5_kBA_bounds`, `baP5_kBA_continuous`; port them as `baPU_*` or use `kBA_basic`.
## (b) Script output — Thu Oct  8 19:31:58 UTC 2026

```
$ cd RBM3D-wt/T2341 && lake build RBM3D.BA.PropUnit   # final file, see commit list below ; then `lake build` (full), output kept in scratch
Build completed successfully (3746 jobs).
(first build of the final file, before commit 9a65c58 at 19:28:32Z: ✔ [3746/3746] Built RBM3D.BA.PropUnit (42s); the line above is the cached rerun)
--- full lake build of the worktree, started 19:12:28Z (task output), before the import drop; the library does not import PropUnit, Prop5 unchanged since:
Build completed successfully (4151 jobs).
exit: 0
```
```
$ three scratch files (imports | #check); transitivity of the ticket import list (ticket: drop what is transitive)
import RBM3D.BA.KHeatDiff import RBM3D.BA.Prop5 #check @RBM.propUnit1_holds 
RBM.propUnit1_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.PropUnit1 d Λ κ
import RBM3D.BA.KHeatDiff import RBM3D.Propagator.PropUnit #check @RBM.BA.baProp5mixed_holds 
trans2.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `RBM.BA.baProp5mixed_holds`
import RBM3D.BA.Prop5 import RBM3D.Propagator.PropUnit #check @RBM.BA.kBA_diff1_le 
trans3.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `RBM.BA.kBA_diff1_le`
```
```
$ lake env lean registry_check.lean   # temporary, uncommitted, outside the repo
import RBM3D import RBM3D.BA.PropUnit  #assert_rbm_axioms 
exit: 0
axiom audit: 10250 theorems, 3041 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
44:  RBM.BA.BAProp6: 1 [no certificate]
45:  RBM.BA.BAProp7: 1 [no certificate]
```
```
$ lake env lean axioms.lean   # import RBM3D.BA.PropUnit + #print axioms (targets, new lemma, 7 instances)
'RBM.BA.baPropUnit1mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropUnit2mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropUnit_laplace_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit1_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit2_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit1_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit2_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_laplace_head' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
$ diff check.lean check_eq.lean ; lake env lean check_eq.lean   # check-file equality
11a12
> import RBM3D.BA.PropUnit
68a70,74
> 
> example : @RBM.BA.T2341Check.T2341_BAPropUnit1mixed = @RBM.BA.BAPropUnit1mixed := rfl
> example : @RBM.BA.T2341Check.T2341_BAPropUnit2mixed = @RBM.BA.BAPropUnit2mixed := rfl
> example : RBM.BA.T2341Check.T2341_baPropUnit1mixed_holds := RBM.BA.baPropUnit1mixed_holds
> example : RBM.BA.T2341Check.T2341_baPropUnit2mixed_holds := RBM.BA.baPropUnit2mixed_holds
lake env lean check_eq.lean: exit 0; error/warning lines: 0
```
```
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/BA/PropUnit.lean RBM3D/BA/Prop5.lean | wc -l
       0
```
```
$ sed -n '59,66p;70,80p' RBM3D/BA/PropUnit.lean   # the two pins (equal to the check file by rfl above)
def BAPropUnit1mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ (a : Zd d L) (j : Fin d),
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single j 1) - BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹
def BAPropUnit2mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ (a : Zd d L) (i j : Fin d),
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single i 1 + Pi.single j 1)
              - BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single i 1)
              - BATheta d L g E m t σ₁ σ₂ 0 (a + Pi.single j 1) + BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹
```
```
$ grep -n '^theorem baPropUnit[12]mixed_holds' RBM3D/BA/PropUnit.lean   # the two targets
886:theorem baPropUnit1mixed_holds (d : ℕ) (Λ κ : ℝ) : BAPropUnit1mixed d Λ κ := by
942:theorem baPropUnit2mixed_holds (d : ℕ) (Λ κ : ℝ) : BAPropUnit2mixed d Λ κ := by
```
```
$ sed -n '485,495p' RBM3D/BA/PropUnit.lean   # the new Laplace lemma (public)
theorem baPropUnit_laplace_head (d n : ℕ) (hd : 3 ≤ d) (hn1 : 1 ≤ n) (hn2 : n ≤ 2) {Λ : ℝ}
    (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g t A : ℝ), 0 < g → g ≤ Λ → 0 < t → t < 1 → 0 ≤ A →
      IntegrableOn (fun τ : ℝ => Real.exp (-(baP5Eps g t) * τ) *
          (min 1 (τ ^ (-((d : ℝ) + n) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ)))))
        (Ioi 0) ∧
      (baP5Gam g t)⁻¹ * ∫ τ in Ioi (0 : ℝ), Real.exp (-(baP5Eps g t) * τ) *
          (min 1 (τ ^ (-((d : ℝ) + n) / 2)) * (1 + A ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))))
        ≤ C * ((g ^ 2 + (1 - t))⁻¹ * (((A + 1) ^ (d + n - 2))⁻¹)) := by
  obtain ⟨CA, hCA, hconv⟩ := baP5_convA Λ hΛ
  obtain ⟨CH, hCH, hhead⟩ := baPU_head (N := d + n) (M := d / 2 + 1) (p := d + n - 2)
```
```
$ sed -n '1026,1035p' RBM3D/BA/PropUnit.lean; grep -c '^theorem inst_' ...   # instance of target 1 (flow point P, d=3, L=4, t=1/2); the other six (`inst_unit2`, `*_large_eps`, `*_zero`, `inst_laplace_head`) follow
theorem inst_unit1 : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ((![1, 0, 0] : Zd 3 4) + Pi.single 0 1)
        - BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![1, 0, 0] : Zd 3 4)‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹
        * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baPropUnit1mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0] 0⟩
7
```
```
$ name-clash grep
BAPropUnit1mixed:0  BAPropUnit2mixed:0  baPropUnit1mixed_holds:0  baPropUnit2mixed_holds:0  baPU_:0  PropUnitInst:0  baPropUnit_laplace_head:0  (hits outside Probe/ and the new file)
```
```
$ ports and diff-stat
ports from merged band file RBM3D/Propagator/PropUnit.lean, last commit: 1c434bb T2024: merge PT-F2 route H unit first and second differences of Theta (no RBM1D/RBM2D file read, so no RBM1D/RBM2D diff-stat)
 RBM3D/BA/Prop5.lean    |   16 +-
 RBM3D/BA/PropUnit.lean | 1119 ++++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1127 insertions(+), 8 deletions(-)
```
```
$ git diff -U0 main...t/T2341 -- RBM3D/BA/Prop5.lean   # removed lines only
-private noncomputable def baP5Gam (g t : ℝ) : ℝ := t * g ^ 2
-private noncomputable def baP5Eps (g t : ℝ) : ℝ := (1 - t) / baP5Gam g t
-private lemma baP5_gam_pos {g t : ℝ} (hg : 0 < g) (ht : 0 < t) : 0 < baP5Gam g t := by
-private lemma baP5_eps_pos {g t : ℝ} (hg : 0 < g) (ht : 0 < t) (ht1 : t < 1) :
-private lemma baP5_Theta_mixed (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) {σ₁ σ₂ : Bool}
-private lemma baP5_Theta_zero (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) :
-private lemma baP5_theta_eq (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g E : ℝ) (m : ℂ) (t : ℝ)
-private lemma baP5_convA (Λ : ℝ) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧
diff after stripping line-initial `private `:        0 lines
```
```
$ uses of the deleted-`private` names; wc -l (stop rule 1700); section commits (UTC)
baP5Gam:19 baP5Eps:34 baP5_gam_pos:4 baP5_eps_pos:3 baP5_Theta_mixed:2 baP5_Theta_zero:3 baP5_theta_eq:7 baP5_convA:4 (uses in PropUnit.lean; all eight listed deletions are used)
    1119 RBM3D/BA/PropUnit.lean
9a65c58 19:28:32Z;86107d6 19:21:46Z;993bf93 19:14:53Z;e7d2148 19:10:32Z;5e9d79d 19:08:14Z;
```

Narrative (facts from the files and the tool log above):
- Files: new `RBM3D/BA/PropUnit.lean` (1119 lines) and `RBM3D/BA/Prop5.lean` (the eight listed `private` keywords deleted, nothing else; all eight are used, see the count line). Imports: `BA.KHeatDiff`, `BA.Prop5`; the ticket's third import `Propagator.PropUnit` is dropped as transitive (scratch check above: with `KHeatDiff` + `Prop5` only, `propUnit1_holds` is visible; `KHeatDiff` and `Prop5` are each needed: `baProp5mixed_holds` is unknown without `Prop5`, `kBA_diff1_le` without `KHeatDiff`).
- Route (ticket steps 1-5). Representation: `baP5_theta_eq` and the private `baPU_diff1_eq` / `baPU_diff2_eq` (twins of `pu_diff1_eq`, `pu_diff2_eq`). Head `τ ≤ L²`: `kBA_diff1_le` / `kBA_diff2_le` rewritten as `|Δ kBA_τ(a)| ≤ C_K baPU_h (d+n) (d/2+1) |a| τ` with `baPU_h N M A τ = min 1 (τ^{-N/2}) (1 + A²/max τ 1)^{-M}`. Tail `τ ≥ L²`: `kBA_gap` conjuncts `.2.1`, `.2.2`, `baPU_tail` (= `pu_tail :239` verbatim) and `lg_tail` inside `baPU_int_bound` (= `pu_int_bound :325`, `lgIntegrand` replaced by `e^{-ετ} H`). Glue `baPU_master` (= `pu_master :537`). `t = 0`: `baP5_Theta_zero` and the band ports `baPU_t0_bound` etc.
- New Laplace lemma (public): `baPropUnit_laplace_head` (statement above); proved from the private `baPU_head` under `N = p+2`, `2 ≤ p`, `p+1 ≤ 2M` (all discharged by `omega` from `3 ≤ d`, `1 ≤ n ≤ 2`, `M = d/2+1`).
- Proof of `baPU_head`, with `B = max A 1`, `R = B²`: `baPU_h_int` splits `(0,∞)` at `τ = 1` and `τ = R` (bounds `(R^M)⁻¹`, `τ^{M-N/2}(R^M)⁻¹`, `τ^{-N/2}`; `integral_rpow` with `s = M - N/2 > -1`, `s+1 ≥ 1/2`; `integral_Ioi_rpow_of_lt`) and gives `∫ h ≤ 4 (B^p)⁻¹`; `baPU_h_sup` gives `h ≤ (B^p)⁻¹` (`h ≤ (τ+A²)^{-v}`, `v = min(N/2, M)`); `ε < 1` uses the integral, `ε ≥ 1` uses `sup · ∫e^{-ετ} = sup/ε`; `baP5_convA` converts `1/γ`, `1/e`; `A+1 ≤ 2B`.
- Deviations from the ticket text: (1) the lemma integrates over `(0, ∞)`, not `(0, L²]` (stronger, the integrand is `≥ 0`; no `L` in the statement). (2) Preflight C1 confirmed: the `ε ≥ 1` branch needs `sup h ≤ C (A+1)^{-(d+n-2)}`, which is what `baPU_h_sup` proves; the `(A+1)^{-(d+n)}` of ticket step (2) is not used. (3) Preflight C2: `baP5_F_integrable` and `baP5_kBA_continuous` are not in the deletion list; ported as `baPU_F_integrable`, `baPU_kBA_cont` (from `kBA_basic`); `baP5_gam_mul_eps`, `baP5_kBA_bounds` not needed.
- Instances: seven named theorems in `RBM.BA.PropUnitInst`: `inst_unit1`, `inst_unit1_large_eps`, `inst_unit1_zero`, `inst_unit2`, `inst_unit2_large_eps`, `inst_unit2_zero`, `inst_laplace_head`. The first six apply the targets at the flow point `P` of `MFixedPointInst` (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, `BAReal` by `P.real`; `t = 1/2`, `1/100`, `0`; both mixed charges; `a = (1,0,0)` (`|a| = 1`) resp. `a = (2,1,0)` (`|a| = 3`, `t = 1/100`), `a ≠ 0` and `|a|` checked by `decide` in `inst_unit1`, `inst_unit2`, `|a| = 3` in the `*_large_eps` ones); `inst_laplace_head` is at `g = 1`, `t = 1/2`, `A = 1`. Every deterministic hypothesis is discharged; the constants stay existential.
- No external hypothesis, no registry entry added (`BAProp6`, `BAProp7` stay owed until P8: registry lines 44-45 above). Constants: `C = max CM (4(Λ²+1)3^d)`, `CM = C_K C_H + C_G C_T`, depending on `(d, Λ, κ)` only.
- Stop rule: `wc -l` at the section commits was 513 (19:08:14Z), 1014 (19:10:32Z), 1118 (19:14:53Z), 1117 after the import drop (19:21:46Z), 1119 final (19:28:32Z); limit 1700.

## (c) Verified Mathlib names (present: compiled; file:line from `grep`)
- `Real.rpow_le_rpow_of_nonpos` (Analysis/SpecialFunctions/Pow/Real.lean:565), `Real.rpow_le_rpow_of_exponent_le` (:617), `Real.rpow_le_one_of_one_le_of_nonpos` (:670)
- `Real.mul_rpow` (:477), `Real.rpow_natCast` (:62), `Real.rpow_add` (:208), `Real.rpow_neg` (:260), `Real.rpow_mul` (:415)
- `integral_Ioi_rpow_of_lt` (Analysis/SpecialFunctions/ImproperIntegrals.lean:178), `integrableOn_Ioi_rpow_of_lt` (:130), `integrableOn_exp_mul_Ioi` (:77), `integral_exp_mul_Ioi` (:102)
- `integral_rpow` (Analysis/SpecialFunctions/Integrals/Basic.lean:147, hypothesis `-1 < r ∨ ...`), `intervalIntegral.intervalIntegrable_rpow'` (`(h : -1 < r)`, used at Analysis/MellinTransform.lean:244), `intervalIntegral.integral_of_le` (MeasureTheory/Integral/IntervalIntegral/Basic.lean:679)
- `setIntegral_mono_on` (MeasureTheory/Integral/Bochner/Set.lean:763), `setIntegral_union` (:87), `setIntegral_mono_set` (:739), `integrableOn_const` (MeasureTheory/Integral/IntegrableOn.lean:119), `Real.volume_real_Ioc` (MeasureTheory/Measure/Lebesgue/Basic.lean:117)
- `Set.Ioc_union_Ioc_eq_Ioc` (Order/Interval/Set/LinearOrder.lean:382), `Set.Ioc_union_Ioi_eq_Ioi` (:190), `Set.Ioc_disjoint_Ioc_of_le` (Order/Interval/Set/Disjoint.lean:53), `Set.Ioc_disjoint_Ioi_same` (:68)
- Absent (grep, no hit): `Real.rpow_le_rpow_of_exponent_nonpos`; use `Real.rpow_le_rpow_of_nonpos`.

## (d) Open issues and paper-delta candidates
- Open issues: none blocking. `BAProp6`, `BAProp7` (the path lemma for `σ₁ ≠ σ₂`) are consumers of these two theorems in P8; nothing is registered here (ticket).
- T2341a: for the unit differences (`n = 1, 2`) Lean uses the polynomial head `min(1, τ^{-(d+n)/2}) (1 + |a|²/max(τ,1))^{-(⌊d/2⌋+1)}` (T2336 `kBA_diff1_le`, `kBA_diff2_le`) instead of the exponential factor `exp(-c(|a|²/(\ilambda² k) ∧ |a|))` of A:58-67 (which bounds the walk probability itself; for the differences the paper cites `yang2024Del` and `RBSO1D` Lemma 3.10 and says the reasoning "extends directly to dimensions d ≥ 3"), with `max τ 1` in place of `τ`.
- T2341b: the Laplace lemma `baPropUnit_laplace_head` is the polynomial twin of `lg_bulk`; it integrates over `(0, ∞)` (not `(0, L²]`); decay exponent `d+n-2` in both the integral and the supremum bound (ticket step (2) wrote `d+n` for the supremum, which is false; section (a) (b')).
- T2341c: both pins are the special case `σ₁ ≠ σ₂` with the bulk datum `BAReal d L g κ E m`; the general-`σ` pins are not proved here (`σ₁ = σ₂` comes from `BAProp5s` in P8).
- T2341d: eight declarations of `BA/Prop5.lean` (`baP5Gam`, `baP5Eps`, `baP5_gam_pos`, `baP5_eps_pos`, `baP5_Theta_mixed`, `baP5_Theta_zero`, `baP5_theta_eq`, `baP5_convA`) are now public (the ticket's authorized edit); no statement changed.
