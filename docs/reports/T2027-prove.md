Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:28:28 UTC 2026

Scripts (mathematics only, Python, scratchpad `pre27.py`, `inst27.py`; exact `Θ` by FFT: `Θ(0,a)=L^{-d}Σ_k e^{2πi k·a/L}/(1-ξ ŝ(k))`, `ŝ(k)=(1+g²Σ_j 2cos(2πk_j/L))/(1+2dg²)`, from `sbKernel`, `Theta` in `Defs/Block.lean:38`, `Propagator/Basic.lean:70`).

### (i) Exponent / constant table (targets: P6 `Prop6Diff1`, P7 `Prop7Diff2`, bundle `Prop5to8`, old forms)
Notation: `n = |r|_L`, `e = |1-t| = 1-t` (t<1), `w = g²+e`, `C₁ = C_U1(d,Λ,κ)` of `PropUnit1`, `C₂ = C_U2(d,Λ,κ)` of `PropUnit2` (merged `propUnit1_holds`, `propUnit2_holds`; `PropUnit.lean:746,826`), steps `u_k ∈ {±e_j}`.

| item | value | constraint | slack |
|---|---|---|---|
| P6 exponent on `(|a|+1)` | `d-1` (same as U1) | path-point bound, no loss | exact, no loss |
| P7 exponent on `(|a|+1)` | `d` (same as U2) | n² terms, `n²=|r|²` | exact, no loss |
| `|r|` power: P6 / P7 | 1 / 2 | P6 = n unit differences; P7 = n² unit second differences | exact |
| steps | `n=|r|_L` unit steps, `r=u_1+…+u_n`, `u_k=±e_j` | `exists_step` (`Gap.lean:88`): `|x-e|+1=|x|`, `|e|=1`; induct n times; `|e|_L=1` forces `e=±e_j` (one coordinate with `zdist=1`, i.e. val ∈ {1,L-1}) | L ≥ 3 so `1 ≠ -1` |
| partial sums `s_k` | `|s_k|_L ≤ k ≤ n` | `zdistD_add_le`, `|u|=1` | — |
| P6 path-point bound | `|a+s_k| ≥ |a|-n ≥ (1-c)|a|` | hypothesis `n ≤ c|a|` | `c<1` ⇒ `(1-c)|a|>0` unless `a=0` (then `n=0`) |
| P6 base of each term | step `+e_j`: base `a+s_{k-1}`; step `-e_j`: `f(b-e_j)-f(b)=-(f((b-e_j)+e_j)-f(b-e_j))`, base `b-e_j=a+s_k`; both are path points, no extra shift | — | no `-1` loss in P6 |
| P6 conversion | `((1-c)|a|+1)^{-(d-1)} ≤ (1-c)^{-(d-1)}(|a|+1)^{-(d-1)}` since `(1-c)|a|+1 ≥ (1-c)(|a|+1)` | `0<c<1` | `1-(1-c)=c>0` |
| **P6 constant** | `C₆ = C₁(1-c)^{-(d-1)}`, `n·C₆` total | pin: ∃ C>0 depending on (d,Λ,κ,c) | `C₆>0`; at d=3, c=1/2: factor 4; c=0.9: 100 |
| P7 identity | `f(a+r)+f(a-r)-2f(a)=Σ_{k,l=1}^n D_{u_l}D_{u_k}f(x_{kl})`, `x_{kl}=a-r+s_{k-1}+s_{l-1}=a-(u_k+…+u_n)+(u_1+…+u_{l-1})` | derivation: `[f(a+r)-f(a)]-[f(a)-f(a-r)]=Σ_l D_{u_l}f(a+s_{l-1})-Σ_k D_{u_k}f(a-r+s_{k-1})`, pair, then `D_{u_l}f(y+r)-D_{u_l}f(y)=Σ_k D_{u_k}D_{u_l}f(y+s_{k-1})` at `y=a-r+s_{l-1}` | numeric error 9.3e-15 (script (1)) |
| displacement `|x_{kl}-a|_L` | `≤ n`: `l ≤ k`: `(l-1)+(n-k+1) ≤ n` steps; `l>k`: overlap `u_k..u_{l-1}` cancels, left `(k-1)+(n-l+1)=n-(l-k) ≤ n` | `zdistD_add_le`, `zdistD_neg` | script: `max(|x_{kl}-a|-|r|)=0` |
| P7 base lower bound | `|x_{kl}| ≥ |a|-n ≥ (1-c)|a|` | same as P6 | — |
| P7 sign shift | `D_{u}D_{v}f(x)=±D_{e_i}D_{e_j}f(x')`, `x'=x+[u<0]u+[v<0]v`, `|x'-x| ≤ 2`; so `|x'| ≥ (1-c)|a|-2` | `D_{-e}h(y)=-D_{e}h(y-e)` applied twice (mixed or `i=j`) | needs care at small `|a|` (below) |
| P7 conversion (**corrects "|x|≥(1-c)|a|-2-type" loosely stated in ticket**) | `|x'|+1 ≥ (1-c)(|a|+1)/3` for every integer `|a| ≥ 0`, `0<c<1`: if `|a|<2/(1-c)`: `|x'|+1 ≥ 1 ≥ (1-c)(|a|+1)/3` (as `|a|+1<3/(1-c)`); if `|a| ≥ 2/(1-c)` (so `|a| ≥ 2`): `|x'|+1 ≥ (1-c)|a|-1 ≥ (1-c)|a|/2 ≥ (1-c)(|a|+1)/3` | `(1-c)|a|-1 ≥ (1-c)|a|/2 ⇔ (1-c)|a| ≥ 2`; `|a|/2 ≥ (|a|+1)/3 ⇔ |a| ≥ 2` | script (3): min ratio `(|x'|+1)/((1-c)(|a|+1))` = 1.077 (L=9), 1.143 (L=5) ≥ 1/3 |
| **P7 constant** | `C₇ = 3^d C₂ (1-c)^{-d}`, times `n²` terms | pin: ∃ C>0 | d=3,c=1/2: ×216; the `n²` terms use `n²=|r|²`; `n=0` gives empty sum (both sides 0) |
| `a=0` | forces `r=0` (`n ≤ c·0`), `n=0`, both sides 0, no path needed | — | — |
| `σ₁≠σ₂`, bulk `κ ≤ Im m` | carried by the unit pins and the targets, idle for `μ=1` | pins as merged | — |
| `ThetaDecay d g m` | `(prop5Decay_holds d g).thetaDecay m` (`Pins.lean:325`), all `d g m` | constants `(d, Λ=g)` | none external |
| `ThetaDecayShort d g m` | `Prop5Short.thetaDecayShort (prop5Short_holds d g m.im)` (`Pins.lean:316`, `Prop5Short.lean:400,493`) | `κ=Im m`; inside the pin `0<Im m` | — |
| `ThetaZeroMode d g μ` bridge hyps | `Prop8ZeroMode.thetaZeroMode (h:Prop8ZeroMode d Λ κ) (0<g) (g ≤ Λ) (0<κ) (‖m‖=1) (κ ≤ Im m) σ₁ σ₂` gives `ThetaZeroMode d g (PropSpin m σ₁*PropSpin m σ₂)` (`Pins.lean:334`) | — | — |
| `ThetaZeroMode` reach (consumer μ) | merged consumers: `Kernel/Evolution.lean:521` (`‖μ‖=1`, any μ), `:632` (`μ=cycProd m i=m_i m_{i+1}`, `Im m_i>0`, `‖m_i‖=1`). Bridge reaches **every unit μ**: μ=1 by `m=I, σ=(true,false)` (`I·Ī=1`); μ≠1: `m=e^{iθ/2}`, `θ=arg μ ∈(0,2π)`, `m*m=μ` (σ=(true,true)), `Im m=sin(θ/2)>0`, take `Λ=g`, `κ=Im m` | script (4) below; `Complex.arg` range `(-π,π]`: use `m` or `-m` to make `Im m>0` (`Im m=0⇒m=±1⇒μ=1`) | so `∀ d g μ, ThetaZeroMode d g μ` is provable; the whole `∃μ` set of the consumers is covered, no `μ` to list |

Cross-check of the constants against exact `Θ` (script (2); grid `g∈{.5,1}`, `t∈{0,.5,.9,.99}`, `μ∈{1,-1,e^{iπ/3}}`, all `(a,r)`, `d=3`): empirical unit constants `U1=8.0`, `U2(mixed+same)=54.0`; every P6/P7 ratio is below `U1(1-c)^{-(d-1)}` resp. `3^d U2 (1-c)^{-d}` (outputs below).

### (ii) One concrete nondegenerate instance
`d=3, L=9, Λ=1, κ=c=1/2, g=1/2, t=9/10, m=I, σ₁=true, σ₂=false (μ=m·m̄=1, ξ=t·μ=0.9), a=(4,0,0), r=(1,0,0)`: `|a|_L=4`, `|r|_L=1 ≤ c|a|=2`; hypotheses of both pins: `3≤d`, `0<Λ`, `0<κ≤Im I=1`, `0<c<1`, `‖I‖=1`, `0<g≤Λ`, `0≤t<1`, `3≤L`.
External hypotheses: none (every input is a merged theorem: `propUnit1_holds`, `propUnit2_holds`, `prop5Decay_holds`, `prop5Short_holds`, `prop8ZeroMode_holds`; no limit computation needed). Note P6 lhs is 0 at this instance by the symmetry `Θ(5)=Θ(4)` on `Z_9` (`|5|=|4|=4`); the P7 lhs is nonzero (below).

```
$ python3 inst27.py
hyps: 3<=d True 0<Lam True 0<kap<=Im m True |m|=1 True g<=Lam True 0<=t<1 True 3<=L True |r|<=c|a| True (|a|,|r|)= (4, 1) mu= (1+0j) |xi|= 0.9
P6: lhs=0.000000  (g^2+|1-t|)^-1 |r| (|a|+1)^-(d-1)=0.114286  ratio=0.0000
P7: lhs=0.011630  (g^2+|1-t|)^-1 |r|^2 (|a|+1)^-d=0.022857  ratio=0.5088
constants: (1-c)^-(d-1)= 4.0  (1-c)^-d= 8.0  3^d(1-c)^-d= 216.0
theta=0.0010 Im m=0.0005  m*m=mu: True
theta=0.5000 Im m=0.2474  m*m=mu: True
theta=3.0416 Im m=0.9988  m*m=mu: True
theta=3.1416 Im m=1.0000  m*m=mu: True
theta=4.0000 Im m=0.9093  m*m=mu: True
theta=6.2822 Im m=0.0005  m*m=mu: True
sigma1!=sigma2 gives mu= (1+0j)

$ python3 pre27.py
P7 identity d=3 L=9: tests 300 max err 9.33e-15 max(|x_kl-a|-|r|) = 0
L=5 d=3: unit consts U1=8.000 U2(mixed+same)=54.000
  c=0.5: P6 sup ratio=2.326 <= U1(1-c)^-(d-1)=32.000 [True]; P7 sup ratio=6.978 <= 3^d U2 (1-c)^-d=11664.000 [True]
  c=0.9: P6 sup ratio=3.723 <= U1(1-c)^-(d-1)=800.000 [True]; P7 sup ratio=6.978 <= 3^d U2 (1-c)^-d=1458000.000 [True]
L=9 d=3: unit consts U1=8.000 U2(mixed+same)=54.000
  c=0.5: P6 sup ratio=2.594 <= U1(1-c)^-(d-1)=32.000 [True]; P7 sup ratio=7.191 <= 3^d U2 (1-c)^-d=11664.000 [True]
  c=0.9: P6 sup ratio=5.953 <= U1(1-c)^-(d-1)=800.000 [True]; P7 sup ratio=9.213 <= 3^d U2 (1-c)^-d=1458000.000 [True]
L=5: 58632 (a,r,k,l,c) cases; min (|x'|+1)/((1-c)(|a|+1)) = 1.1429 (claim >= 1/3)
L=9: 7717908 (a,r,k,l,c) cases; min (|x'|+1)/((1-c)(|a|+1)) = 1.0769 (claim >= 1/3)
```

Script legend: (1) P7 identity on random `f` on `Z_9³`, 300 random `(a,r)` with minimal-representative steps; (2) exact-`Θ` ratios `d=3`, `L∈{5,9}`, `c∈{1/2,0.9}`; (3) shifted base `x'` lower bound over all `(a,r,k,l)`; (4) in `inst27.py`, `m*m=μ` for `μ=e^{iθ}`, `Im m>0`.

### Verdicts
- Target 1 (`prop6Diff1_holds`, `prop7Diff2_holds`): PASS. Constants `C₁(1-c)^{-(d-1)}` and `3^d C₂(1-c)^{-d}` close with no loss; P7 needs the `/3` conversion above (not `(1-c)^{-d}` alone).
- Target 2 (`prop5to8_holds`): PASS (five merged/new theorems, order `decay, short, diffOne, diffTwo, zeroMode`).
- Target 3 (`thetaDecay_holds`, `thetaDecayShort_holds`, `ThetaZeroMode`): PASS; `ThetaZeroMode d g μ` holds for every unit `μ` through the bridge, so the registry entry may be removed (every consumer `μ` is reached).

## (b) Script output — Sat Oct  3 05:41:39 UTC 2026

Branch `t/T2027`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2027`.
```
$ git log --oneline -1; git diff --stat main...t/T2027
ebdab34 T2027: PT-G properties 6 and 7 of lem_propTH, Prop5to8, old interface forms, registry update
 RBM3D/Propagator/Prop6Hold.lean | 560 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |  12 +-
 2 files changed, 565 insertions(+), 7 deletions(-)
$ lake build RBM3D.Propagator.Prop6Hold > mod27c.out; echo $?; tail -1 mod27c.out; grep -c 'Prop6Hold.lean:.*warning' mod27c.out
0
Build completed successfully (3410 jobs).
0
```

Full build, with a temporary uncommitted `import RBM3D.Propagator.Prop6Hold` after the `Prop5Hold` import of `RBM3D.lean` (restored afterwards; the hub adds the root import at merge). Registry counts of the audit info line (lines `  RBM.…`/` RBM.…` of the lists filtered out):
```
$ lake build > full27.out; echo $?  ->  0
$ sed -n '/axiom audit/,$p' full27.out | grep -v '^ RBM\.\|^ Classical\|^ Quot'
info: RBM3D.lean:71:0: axiom audit: 1048 theorems, 400 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
theorems resting on each premise the PAPER borrows:
  RBM.ThetaDiffOne: 1 [certificate: RBM.Test.thetaDiffOne_fixedL]
  RBM.ThetaDiffTwo: 1 [certificate: RBM.Test.thetaDiffTwo_fixedL]
  RBM.PropTH: 1 [certificate: RBM.Test.propTH_fixedL]
  RBM.Loop.KTreeRep: 0 [no certificate]
  RBM.Loop.KLPT: 0 [no certificate]
theorems resting on each premise THIS FORMALIZATION owes:
  RBM.Loop.TwoLoopBounded: 5 [certificate: RBM.Test.twoLoopBounded_kTwoLoop]
  RBM.Loop.KLoopBound: 0 [no certificate]
premises found by scanning: 8 (borrowed 2, owed 1, structural 5).
registry: 5 borrowed + 2 owed + 13 structural; 12 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
non-vacuity certificates: 4 of 7 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3729 jobs).
```

`#print axioms` (`lake env lean ax27.lean`, exit 0):
```
'RBM.prop6Diff1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop7Diff2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop5to8_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaDecayShort_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.thetaZeroMode_unit_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statements (script `extract27.py`: each `theorem NAME` up to its first `:=`):
```
theorem prop6Diff1_holds (d : ℕ) (Λ κ c : ℝ) : Prop6Diff1 d Λ κ c := by
theorem prop7Diff2_holds (d : ℕ) (Λ κ c : ℝ) : Prop7Diff2 d Λ κ c := by
theorem prop5to8_holds (d : ℕ) (Λ κ c : ℝ) : Prop5to8 d Λ κ c :=
theorem thetaDecay_holds (d : ℕ) (g : ℝ) (m : ℂ) : ThetaDecay d g m :=
theorem thetaDecayShort_holds (d : ℕ) (g : ℝ) (m : ℂ) : ThetaDecayShort d g m :=
theorem thetaZeroMode_holds (d : ℕ) {Λ κ g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    {m : ℂ} (hm : ‖m‖ = 1) (hmi : κ ≤ m.im) (σ₁ σ₂ : Bool) :
    ThetaZeroMode d g (PropSpin m σ₁ * PropSpin m σ₂) :=
theorem thetaZeroMode_unit_holds (d : ℕ) (g : ℝ) (μ : ℂ) : ThetaZeroMode d g μ := by
```

The first six types are the merged pins (`lake env lean chk27.lean`, exit 0, empty stderr; the `example`s of that file):
```
example : ∀ d Λ κ c, Prop6Diff1 d Λ κ c := prop6Diff1_holds
example : ∀ d Λ κ c, Prop7Diff2 d Λ κ c := prop7Diff2_holds
example : ∀ d Λ κ c, Prop5to8 d Λ κ c := prop5to8_holds
example : ∀ d g m, ThetaDecay d g m := thetaDecay_holds
example : ∀ d g m, ThetaDecayShort d g m := thetaDecayShort_holds
example : ∀ d g μ, ThetaZeroMode d g μ := thetaZeroMode_unit_holds
```

Compiled nonempty instances (`Prop6Hold.lean` lines 502-560; `d=3`, `L=9`, `g=1/2`, `t=9/10`, `m=I`, `(σ₁,σ₂)=(+,-)`, `a=(4,0,0)`, `r=(1,0,0)`, `|r|=1 ≤ (1/2)|a|=2`; every hypothesis discharged by `norm_num`/`decide`/`Complex.norm_I`; no pin of another gate is a hypothesis):
```
private lemma p6h_inst_a : zdistD 3 9 (![4, 0, 0] : Zd 3 9) = 4 := by decide
private lemma p6h_inst_r : zdistD 3 9 (![1, 0, 0] : Zd 3 9) = 1 := by decide
private lemma p6h_inst_hr :
    (zdistD 3 9 (![1, 0, 0] : Zd 3 9) : ℝ)
      ≤ (1 / 2 : ℝ) * (zdistD 3 9 (![4, 0, 0] : Zd 3 9) : ℝ) := by
  rw [p6h_inst_a, p6h_inst_r]
  norm_num
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![4, 0, 0] : Zd 3 9) + ![1, 0, 0])
        - Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (![4, 0, 0] : Zd 3 9)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹ * (zdistD 3 9 (![1, 0, 0] : Zd 3 9) : ℝ)
        * (((zdistD 3 9 (![4, 0, 0] : Zd 3 9) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop6Diff1_holds 3 1 (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨C, hC, H 9 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false ![4, 0, 0] ![1, 0, 0]
    p6h_inst_hr⟩
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![4, 0, 0] : Zd 3 9) + ![1, 0, 0])
        + Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((![4, 0, 0] : Zd 3 9) - ![1, 0, 0])
        - 2 * Theta 3 9 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (![4, 0, 0] : Zd 3 9)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹ * (zdistD 3 9 (![1, 0, 0] : Zd 3 9) : ℝ) ^ 2
        * (((zdistD 3 9 (![4, 0, 0] : Zd 3 9) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop7Diff2_holds 3 1 (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨C, hC, H 9 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false ![4, 0, 0] ![1, 0, 0]
    p6h_inst_hr⟩
/-- The bundle at `(d, Λ, κ, c) = (3, 1, 1/2, 1/2)`, and its `diffOne` field. -/
example : Prop5to8 3 1 (1 / 2) (1 / 2) := prop5to8_holds 3 1 (1 / 2) (1 / 2)
example : Prop6Diff1 3 1 (1 / 2) (1 / 2) := (prop5to8_holds 3 1 (1 / 2) (1 / 2)).diffOne
example : ThetaDecay 3 (1 / 2) Complex.I := thetaDecay_holds 3 (1 / 2) Complex.I
example : ThetaDecayShort 3 (1 / 2) Complex.I := thetaDecayShort_holds 3 (1 / 2) Complex.I
example : ThetaZeroMode 3 (1 / 2) (PropSpin Complex.I true * PropSpin Complex.I false) :=
  thetaZeroMode_holds 3 (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 2) Complex.norm_I (by norm_num) true false
example : ThetaZeroMode 3 (1 / 2) (-1) := thetaZeroMode_unit_holds 3 (1 / 2) (-1)
end RBM
```

Name clash and hygiene (hits outside `Prop6Hold.lean` under `RBM3D/`, `RBM3D.lean`; counts in the two files):
```
$ grep -rnw <name> RBM3D RBM3D.lean (7 names): prop6Diff1_holds:0  prop7Diff2_holds:0  prop5to8_holds:0  thetaDecay_holds:0  thetaDecayShort_holds:0  thetaZeroMode_holds:0  thetaZeroMode_unit_holds:0  
$ grep -cE 'sorry|admit|native_decide|^axiom ' Prop6Hold.lean: 0;  in the Axioms.lean diff (+ lines): 0;  RBM1D/RBM2D mentions in Prop6Hold.lean: 0
```

Registry diff (`git diff main...t/T2027 -- RBM3D/Test/Axioms.lean | grep '^[-+]'`), confined to the listed entries and one docstring sentence:
```
-external inputs (DECISIONS §5), so they must end up proved. -/
+external inputs (DECISIONS §5), so they must end up proved.  Route H proved `lem_propTH`
+5–8 for every `d ≥ 3` (T2023, T2024, T2027), so `Prop5Decay`, `Prop8ZeroMode`, `Prop5to8`,
+`ThetaDecay`, `ThetaDecayShort` and `ThetaZeroMode` left this list. -/
-  [`RBM.ThetaDecay, `RBM.ThetaDecayShort, `RBM.ThetaDiffOne, `RBM.ThetaDiffTwo,
-   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep,
-   `RBM.Prop5Decay, `RBM.Prop8ZeroMode, `RBM.Prop5to8, `RBM.Loop.KLPT]
+  [`RBM.ThetaDiffOne, `RBM.ThetaDiffTwo, `RBM.PropTH, `RBM.Loop.KTreeRep, `RBM.Loop.KLPT]
-  [(`RBM.ThetaDecay, `RBM.Test.thetaDecay_fixedL),
-   (`RBM.ThetaZeroMode, `RBM.Test.thetaZeroMode_fixedL),
-   (`RBM.ThetaDiffOne, `RBM.Test.thetaDiffOne_fixedL),
+  [(`RBM.ThetaDiffOne, `RBM.Test.thetaDiffOne_fixedL),
```

Consumers of `ThetaZeroMode` in merged code (`grep -rn ThetaZeroMode RBM3D`, minus `Pins`, `Interface`, `Test/`, this file, the `Prop5Hold` example):
```
RBM3D/Kernel/Evolution.lean:521:    (hμ : ‖μ‖ = 1) (hzero : ThetaZeroMode (k + 2) g μ) {τ : ℝ} (hτ : 0 < τ) :
RBM3D/Kernel/Evolution.lean:632:    (hzero : ∀ i, ThetaZeroMode (k + 2) g (cycProd m i))
```

**Narrative (`Prop6Hold.lean`, 560 lines; every statement below is in the file or the output above).**
- No port from RBM1D/RBM2D (0 mentions); `p6h_exists_sq` is the text of the private `pins_exists_sq` of the merged `Propagator/Pins.lean`.
- Section (a) needed no correction: its constants `C₁(1-c)^{-(d-1)}`, `3^d C₂ (1-c)^{-d}`, the `/3` conversion and the claim that the bridge reaches every unit `μ` are the ones proved; so there is no `(a′)`.
- Path lemma `p6h_path`: for `G`, a predicate `P` and a bound `B` on unit steps between good points, `|G(a+r) - G(a)| ≤ |r| B` when every `z` with `|z-a| ≤ |r|` is good; induction on `n = |r|` with `exists_step` (`r = (r-e) + e`, `|r-e| = n-1`), no explicit path.
- P6 (`p6h_unit`, `p6h_bound`): a unit `e = ±e_j` (`exists_unitVec_of_zdistD_eq_one`); `-e_j` is a forward step at the base `x + e` (a path point, no loss); good = `M ≤ |z|` with `M = (1-c)|a|`, `|r| + M ≤ |a|`; `p6h_conv1`: `(1-c)|a|+1 ≥ (1-c)(|a|+1)`.
- P7 (`p6h_second`): not the explicit `x_{kl}` double sum of (a) but its recursion in `n`: for `r = r' + e`, `G = D_e f`,
  `Δ²_{r'+e} f(a) = Δ²_{r'} f(a) + [G(a-e) - G(a-e-r')] + [G(a-e+r') - G(a-e)] + [G(a+r') - G(a-e+r')]`; the two brackets are first differences of `G` along `∓r'` from `a-e` (the path lemma, all points within `n` of `a`), the last is one unit second difference, so `(n-1)² + 2(n-1) + 1 = n²` terms; `a = 0` gives `n = 0` and both sides vanish.
- Sign shifts (`p6h_reduce`, `p6hQ_neg_left`, `p6hQ_comm`): `Q(x,u,e) = ±Q(x', e_i, e_j)` with `|x' - x| ≤ 2`, so the good predicate is `∀ w, |w-x| ≤ 2 → M ≤ |w|` with `M = max(0, (1-c)|a| - 2)`; `p6h_conv2`: `M + 1 ≥ (1-c)(|a|+1)/3`, constant `C₂ 3^d (1-c)^{-d}`.
- The constants are `C₆ = C₁(1-c)^{-(d-1)}` and `C₇ = C₂ 3^d (1-c)^{-d}` (`C₁`, `C₂` of `propUnit1_holds`, `propUnit2_holds`); no loss, no `σ`/`m`/`L`/`g`/`t` dependence.
- Old interface: `thetaDecay_holds`, `thetaDecayShort_holds` are the merged bridges; `thetaZeroMode_holds` has exactly the bridge's hypotheses; additionally `thetaZeroMode_unit_holds : ∀ d g μ, ThetaZeroMode d g μ` (`p6h_exists_spin`: `μ = 1` is `m = I`, `(+,-)`; `μ ≠ 1`: a square root `m` of `μ`, `Im m > 0` after a sign, `(+,+)`; `Λ = g`, `κ = Im m`). The two consumers (`Kernel/Evolution.lean:521`, `:632`) are therefore all covered: no `μ` is left to list.
- Registry: six premises (`Prop5Decay`, `Prop8ZeroMode`, `Prop5to8`, `ThetaDecay`, `ThetaDecayShort`, `ThetaZeroMode`) left `borrowedProps`; certificates of `ThetaDecay` and `ThetaZeroMode` removed; `ThetaDiffOne`, `ThetaDiffTwo`, `PropTH`, `Loop.KTreeRep`, `Loop.KLPT` kept; one docstring sentence added; the full build passes with 5 borrowed + 2 owed + 13 structural premises.
- Root import for the hub: `import RBM3D.Propagator.Prop6Hold` after `import RBM3D.Propagator.Prop5Hold` in `RBM3D.lean`.

## (c) Verified Mathlib names (all `#check`ed, `chk27.lean`, `chk27b.lean`)
- `inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹`; `pow_le_pow_left₀ : 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`
- `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c`; `add_sub_cancel_left : a + b - a = b`
- `norm_add_le`, `norm_sub_rev : ‖a - b‖ = ‖b - a‖`, `norm_neg : ‖-a‖ = ‖a‖`
- `Pi.single_neg : Pi.single i (-x) = -Pi.single i x`; `mul_inv`, `inv_div`, `div_pow`, `mul_pow`
- `Complex.norm_exp_ofReal_mul_I`, `Complex.norm_mul_exp_arg_mul_I`, `Complex.norm_real`, `Complex.exp_add`, `Real.norm_eq_abs`, `abs_mul_abs_self`
- `max_le`, `le_max_left`, `le_max_right`, `Nat.cast_nonneg`, `lt_or_gt_of_ne`
- project: `exists_step`, `exists_unitVec_of_zdistD_eq_one`, `zdistD_unitVec`, `zdistD_add_le`, `zdistD_neg`, `zdistD_eq_zero_iff`
- Names verified absent: none searched for.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (`T2027a` not used). The pins keep the merged reading `|r| ≤ c|a|`, `0 < c < 1` (merged D12); the proof adds no Lean/paper statement difference.
- `ThetaDiffOne`, `ThetaDiffTwo`, `PropTH` stay registered (false as stated, Pins.lean `Prop6Old_false`, `Prop7Old_false`, `PropTH_false`); the final cleanup ticket deletes them.
- The root import is the hub's (merge step A.4); the full build above used a temporary uncommitted import.
- Closes gate PT in Lean: `lem_propTH` properties 5-8 hold for every `d ≥ 3` (`prop5to8_holds`).
