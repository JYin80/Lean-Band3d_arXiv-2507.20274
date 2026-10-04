Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 07:18:17 UTC 2026
Notation: `B=Bparam d L g t 0`, `η=etaT E t=(1-t)Im m^{(E)}`, `K^π=KLKpi`, `v=n-1` the last vertex (its label is the summed `x`), `P'(n)`: for all `σ,π,a`: `Σ_x|K^π(σ,(a,x))| ≤ C L^τ η⁻¹B^{n-2}`. Scripts in `scratchpad/T2122/` (`kk.py` = `T2115/kk.py`, same Lean conventions; `ward.py` computes `x ↦ K^π(σ,(a,x))` exactly by FFT: the last vertex belongs to the root node, `K(x)=Σ_uΘ^{(σ_v,σ_0)}(x,u)Y(u)`).
**The induction (written first; the ticket's text covers only a long last edge, case S below is added).**
Reduction (targets 2,3, `n≥3`): `KLK=(W^d)⁻¹^{n-1}Σ_{π⊆diagonals n}K^π` (`KLK_eq_sum_Kpi`, KLTree:392) so `Σ_x|KLK|≤(W^d)⁻¹^{n-1}2^{|diag n|}·C L^τη⁻¹B^{n-2}=C' L^τ(W^dη)⁻¹(W^{-d}B)^{n-2}` exactly. Needs `η⁻¹≥(1-t)⁻¹`: `Im m=√(4-E²)/2∈(0,1]` (`mE_im`, Semicircle:42; `mE_im_pos`, :56, for `|E|≤2-κ<2`). Strong induction on `n≥3`; step at `n` uses `P'(n'')`, `3≤n''<n`, and `KLindStepPin_holds` / merged bounds (no induction).
(L) `π=∅`, `σ_v≠σ_{v+1}` (last edge long): `K^∅(x)=Σ_bΘ_t(x,b)X_b`, `X_b=Σ_{δ_v=b}Σ^{(∅)}(δ)∏_{i≠v}Θ_i(a_i,δ_i)` (`KLKpi_eq_sum_SigmaPi` KLTree:435; `KLIndStepA_thetaEdge_long` KLIndStepA:466). Column sum `Σ_x|Θ_t(x,b)|=Σ_s|Θ_t(s)|≤(1-t)⁻¹` (`KLlat_sum_norm_Theta_row_le` KLIndStepA:460 + `KLIndStepA_Theta_apply_sub` :107 for `x↦b-x`); `Σ_b|X_b|≤C L^τB^{n-2}` (`KLindStepPin_holds` at `r=v`, hypothesis `σ_v≠σ_{v+1}` is exactly (L)). Total `(1-t)⁻¹C L^τB^{n-2}≤C L^τη⁻¹B^{n-2}`. Cancellation in `Σ_b|X_b|` is needed: absolute values would give `(1-t)⁻²B^{n-3}` (not `≤η⁻¹B^{n-2}`).
(S) `π=∅`, `σ_v=σ_{v+1}` (last edge short; any `σ`, also constant): `KLindStepAt` does not apply (root must be long) and `KLindStep_nonAlt_noloss` (KLIndStepA:1139) needs a second short leaf `j≠r` and a fixed `a_j`. New absolute-value bound, no cancellation: `Σ_x|K^∅|≤Σ_δ|Σ^{(∅)}(δ)|(Σ_x|Θ_v(x,δ_v)|)∏_{i≠v}|Θ_i(a_i,δ_i)|`; `Σ_x|Θ_v^{short}(x,·)|≤S` (`KLedge_l1`, KLInduct:171); `|Σ^{(∅)}(δ)|≤Cm e^{-cm·maxdist δ}` (`KLmolecule_holds`, KLMolecule:610); pick `i0≠v`: the other `n-2` leaves `≤CdB` (`KLedge_sup`, KLInduct:142), `Σ_{δ:δ_{i0}=y}e^{-cm maxdist}≤expC^{n-1}` (`KLIndStepA_sum_exp_root`, KLIndStepA:912, **private**), `Σ_y|Θ_{i0}(a_{i0},y)|≤(1-t)⁻¹` (any charges, `sum_norm_Theta_row_le`, Props4:210, `‖m‖=1`). Total `S·Cm·(CdB)^{n-2}expC^{n-1}(1-t)⁻¹≤C η⁻¹B^{n-2}`, no `L^τ`. The ticket allows no further `open private`: copy `KLIndStepA_sum_exp_root` (stem-prefixed private) and take the leaf bound from `KLedge_sup`, not from the private `KLIndStepA_leaf` (:1061).
(C) `π≠∅`, `KLTSPlong n σ π=∅`: `K^π=0`; else `F₀`, `J∈π` innermost, `J=(i,j)`, `w=j-i∈[2,n-2]` (as in `KLKpi_step`, KLInduct:987). `KLKpi_cut` (KLInduct:609, uses private `sigmaIn,sigmaOut` via `open private … from RBM3D.Loop.KLSumZeroWard`, allowed): `K^π(σ,a)=tΣ_{u,w'}A(u)SB_{uw'}K^{π''}(σ_out,a_out(w'))`. The glued outer labels are `KLInduct_aOut J a w'` (`Function.update` at the glue vertex `i`); since `j≤n-1`, the outer last vertex is `a_{n-1}` and is not the glue (`i<i+1≤n-w`), so `x` stays the outer's summed label with the same last leaf `Θ^{(σ_{n-1},σ_0)}`. Then `Σ_x|K^π|≤|t|Σ_u|A(u)|Σ_{w'}|SB_{uw'}|Σ_x|K''(w',x)|≤Σ_u|A|·sup_{w'}Σ_x|K''|` (`Σ_{w'}|SB_{uw'}|=1`, `sum_norm_SB_row`, Block:118; `KLInduct_norm_cut_le`, private, copy). `Σ_u|A|≤C_inL^{τ/2}B^{k-2}` (`KLindStepPin_holds` at `k=w+1`, `σ_in(last)≠σ_in(0)`), `sup_{w'}Σ_x|K''|≤C_outL^{τ/2}η⁻¹B^{n''-2}` (`P'(n'')` at `τ/2`, `n''=n-w+1`). Statement must use `x`-update form (`update a last x`), converted to the pin's `List.ofFn a ++ [x]` once at the end (`KLloopOf`).
(P) Pin: `n=2`: `KLK_two` (KLTree:211) `=(W^d)⁻¹m₁m₂Θ_{tm₁m₂}(a₁,x)`, `Σ_x≤(W^d)⁻¹(1-t)⁻¹≤(W^dη)⁻¹` (`sum_norm_Theta_row_le`, `‖m₁m₂‖=1`), covers `σ=(s,s)` which `KLward_two` (KLTree:457, `σ=(s,!s)` only, equality form) does not. `n≥3`: reduction above, `n=3`: `diagonals 3=∅`, only (L)/(S).
**(i) Exponent table**
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | ranges | `3≤d`, pin `n≥2`; induction `n≥3`; `n=2` by `KLK_two`; `KLPar`: `0≤t<1,3≤L,1≤W,0<g≤gmax,|E|≤2-κ` | `d-2≥1` |
| 2 | `η⁻¹` vs `(1-t)⁻¹` | `η=(1-t)Im m`, `0<Im m=√(4-E²)/2≤1` so `(1-t)⁻¹≤η⁻¹`; `Im m>0` since `|E|≤2-κ<2` | `Im m≤1`; at `E=0` equality |
| 3 | `W^{-d}` count | `(W^dη)⁻¹(W^{-d}B)^{n-2}=(W^d)⁻¹^{n-1}η⁻¹B^{n-2}` (`W^{-d}·W^{-d(n-2)}`); `2^{|diag n|}` into `C` (`n=3:1,4:4,5:32`) | exactly 0 |
| 4 | `η⁻¹` once | (L): `(1-t)⁻¹` from the summed last leaf; (S): `(1-t)⁻¹` from `Σ_{i0}`; (C): from `P'(n'')` only (inner has none) | one factor |
| 5 | `B` exponent (L) | `X_b`: `B^{n-2}` (merged pin, cancellation) | 0 |
| 6 | `B` exponent (S) | `n-2` leaves pointwise `CdB` (`i0,v` excluded) | 0 |
| 7 | `B` exponent (C) | `(k-2)+(n''-2)=n-2`, `k+n''=(w+1)+(n-w+1)=n+2`; `n=5`: `(k,n'')∈{(3,4),(4,3)}` | exactly 0 |
| 8 | cut geometry | `w∈[2,n-2]`, `k=w+1∈[3,n-1]`, `n''=n-w+1∈[3,n-1]` (`P'(n'')` and `KLindStepPin` apply; `n≥4` for `π≠∅`) | `n-k≥1`, `n-n''≥1` |
| 9 | `L^τ` split | (C): `τ/2+τ/2=τ` (`Real.rpow_add`); (L): `L^τ` once; (S): none (`1≤L^τ`, `KLone_le_rpow`); pin: no split | `τ` exact |
| 10 | `t`, `SB` | cut factor exactly `t≤1`; `Σ_{w'}|SB_{uw'}|=1` for `3≤L` | exactly 0 |
| 11 | constants | `C=C(d,n,κ,gmax,τ)`: `∃C` before `∀p σ π a` (as `KLKpiBoundAt`); `C=2^{|diag n|}max(C_L,C_S,ΣC_inC_out)`; `Cm,Cd,S,cm,expC` depend on `d,n,κ,gmax` | no `L,W,g,t,E` |
| 12 | `0≤t<1`, ticket regimes `1-t≷g²,g²/L²,g²/L^d` | no `ilambda`, no `L`–`W` relation; `B` absorbs the regimes (uniform in `t`) | all four visited below |
| 13 | hypotheses | only `KLPT d κ gmax`; a new `Prop` for `P'(n)` as a step binder needs a theorem concluding it in the file (T2115 report row 12: registry rule, `scanPremises` in `Test/Axioms.lean`), else inline the `∀` | no new line in `Axioms.lean` expected |
| 14 | `STKward` bridge (not a target) | needs `KLPT` from the PT proofs (KL14), `KLPar` data per `n` (`|E n|≤2-κ`, `g n≤gmax`, `0≤τ n<1`), `STKI=KLK`, `Bctl=Bparam`, `L^τ≤N^{τ/d}` (`KL_rpow_le` appears only in the KLInduct:91 docstring; `grep -rn KL_rpow_le RBM3D` finds no declaration) | — |
**(ii) One concrete nondegenerate instance and numerics**
Instance (probe `KLinst` data): `d=3, κ=gmax=1, L=5, W=2, g=1/2, E=0, t=9/10, τ=1/2`; `n=3, σ=(+,-,+)` (last edge the only short one, case S) and `n=4, σ=(+,+,-,-)` (last edge long, L), `(+,-,-,+)` (last short, S).
```
$ python3 -W ignore inst.py
hyp: 3<=d True 0<kappa True 0<gmax True 3<=L True 1<=W True 0<g<=gmax True |E|<=2-kappa True 0<=t<1 True | n=3,4 >=2 True
B=2.9371 eta_t=(1-t)Im m=0.1000  eta^-1=10.000 >= (1-t)^-1=10.000 : True ; Im m<=1 : True ; W^d eta=0.800 ; W^-d B=0.3671 ; L^tau=2.2361
n=3 sigma=[1, -1, 1] short edges [2] a=[(0, 0, 0), (1, 0, 0)]: sum_x|KLK|=1.7280e-02 ; (W^d eta)^-1 (W^-d B)^(n-2)=4.5893e-01 ; ratio=0.0377 (/L^tau=0.0168) ; per-pi: []:0.038
n=4 sigma=[1, 1, -1, -1] short edges [0, 2] a=[(0, 0, 0), (1, 0, 0), (0, 1, 2)]: sum_x|KLK|=9.7173e-05 ; ... =1.6849e-01 ; ratio=0.0006 (/L^tau=0.0003)
n=4 sigma=[1, -1, -1, 1] short edges [1, 3] a=[(0, 0, 0), (1, 0, 0), (0, 1, 2)]: sum_x|KLK|=1.1818e-04 ; ... =1.6849e-01 ; ratio=0.0007 (/L^tau=0.0003)
```
(In the pasted `n=4` lines the middle field `... =1.6849e-01` abbreviates the script's full text `(W^d eta)^-1 (W^-d B)^(n-2)=1.6849e-01`; the per-`π` field is cut.) `KLPT 3 1 1` stays an instance hypothesis; its limit computation (`T2115/pre2.py` copied unchanged, md5 `145174ee…` equal to `T2115/pre2.py`):
```
$ python3 -W ignore pre2.py inst 0 | sed -n '1p;4,6p'
B0=2.9371 A=0.35 m(+)m(-)=1.0; max|Tp(z)-Tp(-z)|=2e-17; signed c0+sum_{y!=0}(Tp+Tn)=0.05263 (T2056 closed form 2/(1+t)-1=1/19=0.05263)
  1-t=1e-01: L^d(1-t)Theta(0,0)=23.2191 (1-t)rowsum=1.000000 BD1 0.809 BD2 2.427 KLZero 0.622 KLDecay 0.632 KLShort 0.0043
  1-t=1e-06: L^d(1-t)Theta(0,0)=1.0003 (1-t)rowsum=1.000000 BD1 0.845 BD2 2.576 KLZero 0.520 KLDecay 1.350 KLShort 0.0042
  1-t=1e-09: L^d(1-t)Theta(0,0)=1.0000 (1-t)rowsum=1.000000 BD1 0.845 BD2 2.576 KLZero 0.577 KLDecay 1.350 KLShort 0.0042
```
Ticket grid (`d=3, L∈{5,9}, g∈{.5,1}, 1-t∈{1e-1,1e-3}, E∈{0,1}`, all `σ`, 20 configs `a`, last label summed; `R=Σ_x|KLK|/((W^dη)⁻¹(W^{-d}B)^{n-2})=Σ_x|Σ_πK^π|/(η⁻¹B^{n-2})`, `W` cancels; `n=2`: `R=η Σ_x|Θ^{(s1,s2)}(a1,x)|`):
```
$ python3 -W ignore ward.py | sed -n '1p;/MAX/p'
self-check n=4: |Kvec(x)-sum_pi Kpi_all|=2.4e-19
MAX n=2 over the grid: R=1.000 ; max_pi 0.000
MAX n=3 over the grid: R=1.285 ; max_pi 1.285
MAX n=4 over the grid: R=2.169 ; max_pi 2.169
```
(`max_pi` = max over single layers `π` of `Σ_x|K^π|/(η⁻¹B^{n-2})`, i.e. target 2 itself; the largest `R` is at `L=9,g=1,1-t=0.1,E=0`.) `n=5` and the family (c) `σ_{n-1}=σ_0`, all other edges long (`n` odd), 5 configs `a`, `E=0`, rows with `1-t=1e-3, L=9` skipped for time:
```
$ python3 -W ignore ward5.py | grep "n=5" | grep -v "R=0.000 |"      # (4 of 6 rows shown; max over all 6 rows: R=3.524, max_pi 2.615, family (c) 1.349)
L=5 g=1 1-t=0.1 n=5 | max_sigma R=2.939 | max_pi 2.166 | family (c) (only last edge short) R=1.047
L=9 g=1 1-t=0.1 n=5 | max_sigma R=3.524 | max_pi 2.615 | family (c) (only last edge short) R=1.349
L=5 g=1 1-t=0.001 n=5 | max_sigma R=0.631 | max_pi 0.310 | family (c) (only last edge short) R=0.500
L=9 g=0.5 1-t=0.1 n=5 | max_sigma R=0.181 | max_pi 0.067 | family (c) (only last edge short) R=0.050
```
Regimes on the grid and beyond (`reg.py`: grid points `{g²/L²<1-t≤g²: 4, 1-t≤g²/L³: 3, g²/L³<1-t≤g²/L²: 1}`; `1-t>g²` is off the ticket grid, added by `ward_t0.py`, `E=0`, `g∈{.05,.5}`, `1-t∈{1,.5}`, `L∈{5,9}`):
```
$ python3 -W ignore ward_t0.py | cut -c1-80
L=5 g=0.05 1-t=1 (1-t>g^2: True): n=3 R=0.995; n=4 R=0.989
L=5 g=0.5 1-t=1 (1-t>g^2: True): n=3 R=1.238; n=4 R=1.532
L=9 g=0.05 1-t=1 (1-t>g^2: True): n=3 R=1.001; n=4 R=1.002
L=9 g=0.5 1-t=1 (1-t>g^2: True): n=3 R=1.248; n=4 R=1.557
(the four rows with 1-t=0.5 give R<=0.795 for n=3 and <=0.774 for n=4)
```
Reading: `R` bounded uniformly in `L,g,t,E` at each `n` (`n=2` exactly `≤1`; `n=3,4,5`: `≤1.29, 2.17, 3.52`), growing mildly with `n` as `C(n)` allows; at `E=0` the `n=2` ratio equals 1 (`η⁻¹=(1-t)⁻¹`, row sum `(1-t)⁻¹`), so row 2 has no slack there and `η⁻¹` cannot be replaced by anything smaller. The only-last-short family (the case absent from the ticket text) stays `≤1.35`, consistent with case S.
**Verdicts.** Target 1 (pins verbatim from `docs/tickets/checks/T2122-check.lean`): PASS. Target 2 (`P'(n)`: cases L, S, C; every step is a merged lemma, a ported private lemma (`KLInduct_norm_cut_le`, `KLIndStepA_sum_exp_root`) or a new short lemma (cases L, S assembly)): PASS. Target 3 (`KLwardIneqPin_holds`; `n=2` by `KLK_two`, not `KLward_two`): PASS. No exponent is short (slack 0 exactly at rows 3, 5–7, 10). Finding for the prover: the paper's `π=∅` line (`A_deterministic_estimates.tex:817`) and the ticket assume a long last edge; case S (last edge short, including `n` odd with exactly one short edge, where `KLindStepAt` and `KLindStep_nonAlt_noloss` both fail to apply) is proved here by absolute values and one `ℓ¹` leaf: paper-delta candidate `T2122a`. Overall: **PASS**.

## (b) Script output (HEAD `d2a52e9` of `t/T2122`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2122`; one run of `scratchpad/T2122/final_evidence.sh`)
```
# final_evidence.sh started Sun Oct  4 07:59:27 UTC 2026
$ git log -1 --format="%h %s"; git status --short
d2a52e9 T2122: KL12 Loop/KLWardIneq (lem_wardineq_K: KLwardIneqPin_holds)
(status above: empty = clean)
$ lake build RBM3D.Loop.KLWardIneq 2>&1 | tail -3
Build completed successfully (3258 jobs).
$ git diff --stat main...t/T2122; wc -l; grep -cE "sorry|admit|native_decide|^axiom|maxHeartbeats"; grep -n "^open private\|^import"
 RBM3D/Loop/KLWardIneq.lean | 1084 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1084 insertions(+)
    1084 RBM3D/Loop/KLWardIneq.lean
0
6:import Batteries.Tactic.OpenPrivate
7:import RBM3D.Loop.KLInduct
81:open private sigmaIn sigmaOut from RBM3D.Loop.KLSumZeroWard
$ lake env lean axscan.lean   # every constant of the module, private included
module RBM3D.Loop.KLWardIneq: 25 hand-written constants (22 theorems, 3 defs, 15 private, counted among them); constants using an axiom outside [propext, Classical.choice, Quot.sound]: 0 []
$ lake env lean axpub.lean | grep depends   # #print axioms of the 9 public declarations
KLwardIneqPin_holds : [propext, Classical.choice, Quot.sound]
KLWardIneq_KpiAt_holds : [propext, Classical.choice, Quot.sound]
KLWardIneq_Kpi_step : [propext, Classical.choice, Quot.sound]
KLWardIneq_Kpi_empty_bound : [propext, Classical.choice, Quot.sound]
KLWardIneq_At_two : [propext, Classical.choice, Quot.sound]
KLWardIneq_At_of_Kpi : [propext, Classical.choice, Quot.sound]
KLwardIneqAt : [propext, Classical.choice, Quot.sound]
KLwardIneqPin : [propext, Classical.choice, Quot.sound]
KLWardIneq_KpiAt : [propext, Classical.choice, Quot.sound]
$ lake build 2>&1 | tail -1   # original RBM3D.lean (root olean without the new module)
Build completed successfully (3867 jobs).
$ registry pre-check: printf "import RBM3D\nimport RBM3D.Loop.KLWardIneq\n#assert_rbm_axioms\n" | lake env lean --stdin  (and without the second import)
with: exit=0
base: exit=0
1c1
< axiom audit: 3670 theorems, 1286 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 3677 theorems, 1289 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
10c10
<   RBM.Loop.KLPT: 15 [no certificate]
---
>   RBM.Loop.KLPT: 19 [no certificate]
reg_base.txt:premises found by scanning: 80 (borrowed 2, owed 63, structural 15).
reg_with.txt:premises found by scanning: 80 (borrowed 2, owed 63, structural 15).
$ full build with a temporary `import RBM3D.Loop.KLWardIneq` after the last import of RBM3D.lean (reverted afterwards)
 RBM3D.lean | 1 +
 1 file changed, 1 insertion(+)
full build exit=0
631:info: RBM3D.lean:167:0: axiom audit: 3677 theorems, 1289 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
745:premises found by scanning: 80 (borrowed 2, owed 63, structural 15).
Build completed successfully (3868 jobs).
Build completed successfully (3867 jobs).
$ git status --short   # after the revert (and a rebuild of the original root)
(empty = clean)
$ pins: docs/tickets/checks/T2122-check.lean and 64b58eb:RBM3D/Probe/T2004Pins.lean vs KLWardIneq.lean section 1
      12 pin_check.txt
      12 pin_file.txt
      12 pin_probe.txt
      36 total
check file vs KLWardIneq.lean: PIN-IDENTICAL
probe (64b58eb) vs KLWardIneq.lean: PIN-IDENTICAL
$ statements extracted from the file by script (stmts.py; proofs omitted)
L91 def KLwardIneqAt (d n : ℕ) (κ gmax : ℝ) : Prop :=
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (a : Fin (n - 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLK d p.L p.g p.W p.E p.t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
    ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d) * Gauss.etaT p.E p.t)⁻¹
    * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 2)
L98 def KLwardIneqPin : Prop :=
    ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLwardIneqAt d n κ gmax
L956 theorem KLwardIneqPin_holds : KLwardIneqPin
L663 def KLWardIneq_KpiAt (d m : ℕ) (κ gmax : ℝ) : Prop :=
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin (m + 1) → Bool)
    (π : Finset (Fin (m + 1) × Fin (m + 1))) (a : Fin (m + 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) π‖
    ≤ C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1)
L852 theorem KLWardIneq_KpiAt_holds (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLWardIneq_KpiAt d m κ gmax
L676 theorem KLWardIneq_Kpi_step (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax)
    (hout : ∀ m'' : ℕ, 2 ≤ m'' → m'' < m → KLWardIneq_KpiAt d m'' κ gmax) :
    KLWardIneq_KpiAt d m κ gmax
L431 theorem KLWardIneq_Kpi_empty_bound (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) ∅‖
    ≤ C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1)
L864 theorem KLWardIneq_At_two (d : ℕ) {κ gmax : ℝ} (hκ : 0 < κ) : KLwardIneqAt d 2 κ gmax
L899 theorem KLWardIneq_At_of_Kpi (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLwardIneqAt d (m + 1) κ gmax
$ the compiled nonempty instances: grep -n "^example" ; sed -n 977,1004p ; sed -n 1069,1080p  (RBM3D/Loop/KLWardIneq.lean)
977:example (hPT : KLPT 3 1 1) :
1009:example (hPT : KLPT 3 1 1) :
1041:example (hPT : KLPT 3 1 1) :
1052:example (hPT : KLPT 3 1 1) :
1063:example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
1069:example :
1078:example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn ![true, false], List.ofFn ![KLinsta 0] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn KLinstσ, List.ofFn ![KLinsta 0, KLinsta 1] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn KLInduct_instσ,
            List.ofFn ![KLInduct_insta 0, KLInduct_insta 1, KLInduct_insta 2] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLwardIneqPin_holds 3 2 1 1 (by norm_num) (by norm_num) one_pos one_pos
      hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar ![true, false] ![KLinsta 0]⟩
  · obtain ⟨C, hC, H⟩ := KLwardIneqPin_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos
      hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLinstσ ![KLinsta 0, KLinsta 1]⟩
  · obtain ⟨C, hC, H⟩ := KLwardIneqPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos
      hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLInduct_instσ
      ![KLInduct_insta 0, KLInduct_insta 1, KLInduct_insta 2]⟩
example :
    ∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn ![true, true], List.ofFn ![KLinsta 0] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 2) := by
  obtain ⟨C, hC, H⟩ := KLWardIneq_At_two 3 (κ := 1) (gmax := 1) one_pos 1 one_pos
  exact ⟨C, hC, H KLinstPar ![true, true] ![KLinsta 0]⟩

example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
  ⟨KLWardIneq_At_of_Kpi 3 2 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT,
    KLWardIneq_At_of_Kpi 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT⟩
$ name clash (clash.py)
new declarations: 24 (public 9, private 15)
declaration clashes in main: 0 []
main HEAD: 3fcd6c6
$ ports: RBM2D analogue of wardineq?
       0
RBM2D HEAD: 9e0f275
$ grep -rn "L_rpow_le\|KL_rpow\|rpow_le_size" RBM3D   # an L-version of Sizes.W_rpow_le?
RBM3D/Loop/KLInduct.lean:91:`N = (WL)^d` (`KL_rpow_le`) this implies the paper's `≺` (deterministic, `N = (WL)^d`). -/
# final_evidence.sh finished Sun Oct  4 08:00:47 UTC 2026
```

Narrative (each claim is read off the scripts above or the file `RBM3D/Loop/KLWardIneq.lean`):
1. One new file, 1084 lines, branch `t/T2122`; no other file is touched and `Test/Axioms.lean` needs no line (pre-check: exit 0, 80 premises with and without the module; the new `Prop` `KLWardIneq_KpiAt` is concluded by `KLWardIneq_KpiAt_holds`). Target 1: the two pins are byte-identical to the check file and to the probe `64b58eb` (script diff). Target 3: `KLwardIneqPin_holds` (L956) = `KLWardIneq_At_two` (L864; `n = 2`, `KLK_two`, every `σ` including `(s,s)`, which `KLward_two` does not cover; only `0 < κ`) and `KLWardIneq_At_of_Kpi` (L899; `n ≥ 3`: `KLK_eq_sum_Kpi`, `Fin.update_snoc_last`, the `2^{|diagonals n|}` layers). The only hypothesis is `KLPT d κ gmax`; no regime split in `t` (DECISIONS §29).
2. Target 2 = `KLWardIneq_KpiAt_holds` (L852; `n = m+1 ≥ 3`, see (d) T2122c): strong induction with `KLWardIneq_Kpi_step` (L676), skeleton of `KLKpi_step`. `π = ∅` (`KLWardIneq_Kpi_empty_bound`, L431), last leaf long: column sums `≤ (1-t)⁻¹ ≤ η_t⁻¹` (`Theta_transpose_of_three_le`, `sum_norm_Theta_row_le`) times `KLindStepPin_holds` at the root `Fin.last m`. `π ≠ ∅`: `KLKpi_cut` at an innermost long edge; `KLWardIneq_aIn_update`, `_aOut_update` (L532, L551) show that the summed vertex stays the last vertex of the outer polygon and is not seen by `A(u)`; `KLWardIneq_norm_cut_sum_le` (L606) keeps `∑_x` in the outer factor; the induction hypothesis and `KLindStepPin_holds` at `τ/2` give `L^τ`, `B^{n-2}` and `η_t⁻¹` once.
3. Case (S), last leaf short (`σ_{n-1} = σ_0`), is not in the ticket text nor in the paper's displayed bound `A_deterministic_estimates.tex:816-818` (finding of (a), T2122a). `KLWardIneq_abs_sum_le` (L312): `∑_x|Θ^{(s,s)}(x,b)| ≤ S` (`KLedge_l1`), `|Σ^{(∅)}| ≤ C_m e^{-c_m max|δ_i-δ_j|}` (`KLmolecule_holds`), the `n-2` leaves other than `v`, `0` are `≤ C_d B` (`KLedge_sup`), the leaf at `0` is summed (`≤ (1-t)⁻¹`), the slice sum is `≤ expC^{n-1}`; no cancellation, no `L^τ`.
4. `open private` only for `sigmaIn sigmaOut` (L81). Four private helpers are copied with the prefix `KLWardIneq_` (the ticket allows no other `open private`): `KLMolecule_sum_slice` (`KLMolecule.lean:688`), `KLMolecule_sum_exp_maxDist` (`:722`), `exists_innermost` (`KLSumZeroWard.lean:577`), `Flong_subset_diagonals` (`:594`). (a) planned to copy `KLIndStepA_sum_exp_root` and `KLInduct_norm_cut_le`; with vertex `0` as the summed leaf the root-`0` slice lemmas suffice, and the `∑_x` form needed the new `KLWardIneq_norm_cut_sum_le`. No RBM1D/RBM2D port (grep `wardineq` in RBM2D: 0).
5. Instances (L965-1082): `KLwardIneqPin_holds` at `n = 2, 3, 4` (`n = 3`, `σ = (+,-,+)`: last leaf short; `n = 4`, `σ = (+,+,-,-)`: long), `KLWardIneq_KpiAt_holds` at `n = 4` (layers `∅`, `{(0,2)}`, `{(1,3)}`) and `n = 3`, `KLWardIneq_Kpi_step`, `KLWardIneq_Kpi_empty_bound`, `KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1`, `KLWardIneq_At_two` at `σ = (+,+)` (no hypothesis left) and `KLWardIneq_At_of_Kpi` at `n = 3, 4`; data `KLinstPar` (`L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`), spread labels in `Z_5^3`. Only `KLPT 3 1 1` stays a hypothesis (limit checks: (a), `pre2.py`, not re-run).
6. Bridge `KLwardIneqPin → STKward` (`Step34Pins.lean:229`, not a target) needs: `KLPT d κ gmax` from the PT proofs (KL14); eventually in `n` a `KLPar κ gmax` at `(sz.L n, sz.W n, sz.lam n, E n, τ n)` (`3 ≤ L`, `1 ≤ W`, `0 < lam ≤ gmax`, `|E n| ≤ 2-κ`); `STKI sz n E τ = KLK d (sz.L n) (sz.lam n) (sz.W n) E τ` (definition, `Step34Pins.lean:111-112`) and `sz.Bctl n t = (W^d)⁻¹ Bparam d L lam t 0` (`Defs/Sizes.lean:214-215`), so the right sides agree; and the loss conversion `L^{τ'} → size^τ` with `sz.size n = (W n L n)^d` (`Defs/Sizes.lean:157`), `C` absorbed in `Prec = StochDomAt`: `Sizes.W_rpow_le` (`:220`) is the `W` version, the last grep of (b) finds no `L` version (`KL_rpow_le` occurs only in the docstring `KLInduct.lean:91`).
7. Section (a): no mistake found, no (a′); the departures from its plan are in item 4. Report written Sun Oct  4 08:01:02 UTC 2026 (`date -u`).

## (c) Verified Mathlib names (script `names_check.lean`: the 98 distinct theorems outside `RBM` named in the code of the file, comments removed; each resolves in the compiled environment of `RBM3D.Loop.KLWardIneq`)
root: add_halves, add_zero, div_le_one, inv_anti₀, inv_pos, le_of_eq, le_rfl, le_trans, mul_inv, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_one, mul_pow, norm_inv, norm_mul, norm_nonneg, norm_pow, norm_prod, norm_sum_le, norm_zero, nsmul_eq_mul, one_mul, one_pos, pow_add, pow_le_pow_left₀, pow_nonneg, pow_succ, pow_zero, sq_nonneg, true_and, zero_le_one
Complex.{norm_natCast, norm_real}
Fin.{ext, last_add_one, le_def, lt_def, snoc_castSucc, snoc_last, update_snoc_last, val_last, val_zero}
Finset.{card_erase_of_mem, card_powerset, card_univ, eq_empty_or_nonempty, exists_min_image, filter_subset, le_sup, mem_erase, mem_filter, mem_powerset, mem_range, mem_univ, mul_prod_erase, mul_sum, ne_of_mem_erase, nonempty_iff_ne_empty, prod_congr, prod_const, prod_le_prod₀, prod_nonneg, prod_univ_sum, single_le_sum, sum_comm, sum_congr, sum_const, sum_const_zero, sum_empty, sum_fiberwise, sum_le_sum, sum_mul, sum_neg_distrib, sum_nonneg}
Fintype.{card_fin, mem_piFinset}
Function.{update_of_ne, update_self}
List.{ofFn_succ, ofFn_succ'}
Matrix.{transpose_apply}
MulZeroClass.{mul_zero}
Nat.{add_sub_cancel, cast_nonneg, lt_or_ge, strong_induction_on}
Ne.{symm}
NeZero.{pos}
Prod.{ext}
Real.{exp_le_exp, exp_pos, exp_sum, norm_of_nonneg, rpow_add, rpow_nonneg, sqrt_le_iff}
Verified absent as declarations: `KL_rpow_le` (docstring only); public versions of `exists_innermost`, `Flong_subset_diagonals`, `KLMolecule_sum_slice`, `KLMolecule_sum_exp_maxDist`, `KLIndStepA_sum_exp_root` (all `private`: item 4).

## (d) Open issues and paper-delta candidates
- T2122a (proof gap in the paper, statement unchanged; `A_deterministic_estimates.tex:816-818`): the displayed `π = ∅` bound writes the last leaf as `Θ^{(+,-)}_{t,a_n b_n}`, i.e. `σ_n ≠ σ_1`; the lemma is `max_σ`. For `σ_n = σ_1` the Lean proof is the absolute-value bound (item 3); (a) reports the numerics of the family with only the last edge short (`R ≤ 1.35`, `ward5.py` line).
- T2122b (induction scheme; = T2115a): induction on the number of polygon vertices for the standard `K^{(π)}` with the summed label as the last label, not on molecules for `K̃^{(π)}` (`A:820-827`); exponents as in the paper (`B^{l-1} · η⁻¹B^{n-l-1}`).
- T2122c (range): `(eq:K-pi-bound_partial)` is proved for `n ≥ 3`, where `(eq_K-Kpi)` and `K^{(π)}` live (`KLgen` uses `kTwo` at length 2, `KLTree.lean:135-143`); `n = 2` is `(Kn2sol)`. The ticket text says `n ≥ 2` for target 2.
- Existing entries cover the loss `L^τ` (D178, T2004e) and the scale `N` of `STKward` (D55, T2041h); no new delta for them.
- For KL14 (observation): make `exists_innermost`, `Flong_subset_diagonals`, `sigmaIn`, `sigmaOut` and the two `KLMolecule` slice lemmas public, then the four copies in this file can be deleted.
- Not done: the sequence-level `STKward` (item 6); `KLPT 3 1 1` remains a hypothesis of the examples. All three targets are built, committed (`d2a52e9`) and reported.
