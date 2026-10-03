Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:56:52 UTC 2026

Target: `KLK_ward` = body of `KLwardPin` (`docs/tickets/checks/T2036-check.lean`): for `σ = (s, μ, !s)`, `n = |μ|+2 ≥ 2`,
`Σ_x 𝒦_{t,σ,(a,x)} = κ_t (𝒦_{t,(+,μ),a} − 𝒦_{t,(−,μ),a})`, `κ_t = (2 i W^d η_t)⁻¹`, `η_t = (1−t) Im m(E)`
(`Gauss.etaT`, `RBM3D/Loop/GLoop.lean:75`), `m(+) = mE E`, `m(−) = conj mE E` (`mSigma`, `Defs/Semicircle.lean:85`).
Route (read from `RBM2D/Loop/Ward.lean` at the working copy): for `s = +`, `D_t(μ,a') := Σ_x K_t(+,μ,−;a',x) − κ_t(K_t(+,μ;a') − K_t(−,μ;a'))`
satisfies `∂_t D = W^d·T[D] + (1−t)⁻¹ D` (`T` linear in same-level `D` at adjacent cuts `(k,k+1)` and the cut `(1,N)`, times 2-loops, bounded by `R`; cyclic invariance `KLK_rotate` for cuts `(k,n)`),
`D_0 = 0`, level 2 gives `D = 0` (`KLward_two`, `KLTree.lean:457`), Grönwall. For `s = −`: flip lemma `K(!σ,a) = conj K(σ,a)` (tree-sum level, no ODE).

### (i) Exponent table (no analytic exponents; the exponent is `W^d` and the constants it enters)

| # | Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | `W^d` in `κ_t`, `c_t`, `treeEqRhs`, `MLoop` | `κ_t = (2iW^dη_t)⁻¹`, `c_t = (W^d(1−t))⁻¹`; `W^d` replaces `W²` (RBM2D) | `κ_t(m₊−m₋) = c_t`; `W^d c_t = (1−t)⁻¹`; `κ_t' = κ_t/(1−t)` | exact identities (0 slack); instance: `κ = −0.625i`, `c = 1.25`, `κ·2i = 1.25` |
| 2 | `η_t` | `(1−t) Im m(E)`: `E=0`: 0.1; `E=1`: 0.0866 | `η_t > 0` so `κ_t` is defined: `|E|<2`, `t<1` | `Im m = 1 / 0.866 > 0`; `1−t = 0.1` |
| 3 | `|m| = 1` | `m₊m₋ = |m|² = 1`, `‖t m₊m₋‖ = t` | `|E| ≤ 2` (used as `|E| < 2`); `t < 1` so `‖ξ‖<1` | `1 − t = 0.1`; `\|m\| = 1.000000000000000` at both `E` |
| 4 | level `n=2` base | `Σ_x 𝒦⁽²⁾ = W^{-d}/(1−t|m|²) = c_t` | row sum of `Θ_t` is `(1−t)⁻¹` (`sum_Theta_row_of_three_le`, `Propagator/Props4.lean:114`, `L ≥ 3`) | merged as `KLward_two`; instance: 1.25 = 1.25 |
| 5 | initial value `t=0` | `D_0 = (W^d)^{-N} P I ((W^d)⁻¹ m₊m₋ − κ_0(m₊−m₋))` | `m₊m₋ = 1`, `κ_0(m₊−m₋) = c_0 = W^{-d}` | exact, 0 |
| 6 | stochasticity of `S^{(B)}` | `c0 + 2d c1 = 1`, `c0 = (1+2dg²)⁻¹`, `c1 = g²c0` | `L ≥ 3` (the `2d` neighbours distinct); `g ∈ ℝ` any sign | instance `0.4 + 6·0.1 = 1.0`; row sum of `‖SB‖` entries `= 1` gives `‖SB_{ab}‖ ≤ 1` (merged `norm_SB_apply_le`, `Loop/Unique.lean:112`) |
| 7 | Grönwall constant `C` on `[0,T₀]`, `T₀ = t` | `C = W^d·(Σ_{k<N}Σ_{a,b} R + Σ_{a,b} R) + (1−T₀)⁻¹` (RBM2D `Ward_level`, `Z2 L ↦ Zd d L`: `L^{2d}` terms) | finite: `T₀ < 1`; `R` = 2-loop bound on `[0,T₀]` from continuity (merged `KLretire_twoLoopBounded`); `C` may depend on `L,d,W,t` (it is only used to conclude `D ≡ 0`) | instance: `(1−T₀)⁻¹ = 10`, `W^d = 8`, `L^{2d} = 15625`, all finite; no `L²` enters |
| 8 | flip | `conj κ_t = −κ_t`; `Θ(conj ξ) = conj Θ(ξ)` (`SB` real); `m(!s) = conj m(s)` | `g,E,t ∈ ℝ`; `W^d ∈ ℝ` | exact; derivation: `Σ K(false,μ,true) = conj(κ(K(+,!μ)−K(−,!μ))) = −κ(K(−,μ)−K(+,μ)) = κ(K(+,μ)−K(−,μ))` |
| 9 | parameter range of the pin | `3 ≤ L`, `1 ≤ W`, `\|E\|<2`, `0 ≤ t < 1`, `d` any (no `3 ≤ d`), `g` any real | all used above only through rows 2–8 | numerics below also at `d = 0,1,2`, `g ∈ {0, 0.7, 2, −1.3}`, `t ∈ {0, 0.95, 0.99}` |

External inputs: none (no unproved `Prop` hypothesis; deps are merged `KLK_isKLoop`, `KLK_rotate`, `KLretire_twoLoopBounded`, `KLward_two`), so no external limit computation applies.
The `s = −` order cannot come from `KLK_rotate` (rotation permutes positions, never flips charges): flip lemma is needed.

### (ii) One concrete nondegenerate instance

Data: `d=3, L=5, W=2, g=1/2, E=0, t=9/10, s ∈ {true,false}, μ=[false], a=[0,1]` (`a.length = 2 = |μ|+1`, `n = 3`).
Hypotheses: `NeZero 5`, `3 ≤ 5`, `1 ≤ 2`, `|0| < 2`, `0 ≤ 9/10 < 1`. `η_t = 0.1 ≠ 0`; both sides are `≈ −0.0232 i` (not 0, not collapsed).
`𝒦` is defined by the tree sum (`KLgen`/`KLn`, `KLTree.lean:129-145`; `TSP 3 = {∅}`, `TSP 4 = {∅,{(0,2)},{(1,3)}}`), so evaluating it literally evaluates both sides of the pin.
The script `ward_check.py` (python3/numpy; no Lean) builds `SB` (circulant, `c0 I + c1 Σ_i(shift_i+shift_iᵀ)`), `Θ_ξ = (1−ξSB)⁻¹`, the tree sum with laminar parents exactly as `KLleafPar`/`KLnodePar`, and checks the pin for all `μ`, `s` and random `a`, and the flip.

```
$ python3 ward_check.py
d=3 L=5 W=2 g=0.5 E=0.0 t=0.9 n in [2, 3]: max |LHS-RHS| = 3.11e-15; max flip err = 0.00e+00
d=3 L=3 W=2 g=0.5 E=0.0 t=0.9 n in [2, 3, 4]: max |LHS-RHS| = 1.78e-15; max flip err = 0.00e+00
d=3 L=5 W=2 g=0.5 E=1.0 t=0.9 n in [2, 3]: max |LHS-RHS| = 2.44e-15; max flip err = 2.93e-19
d=3 L=3 W=2 g=0.5 E=1.0 t=0.9 n in [2, 3, 4]: max |LHS-RHS| = 1.33e-15; max flip err = 1.58e-18
instance s= True  LHS= -0.023242426581640337j  RHS= -0.023242426581640257j eta= 0.09999999999999998 |LHS|= 0.023242426581640337
instance s= False  LHS= -0.02324242658164029j  RHS= -0.023242426581640257j eta= 0.09999999999999998 |LHS|= 0.02324242658164029
n=2 a=[0]: sum_x K2 = (1.2500000000000029+0j)  W^-d/(1-t)= 1.25  RHS= (1.2500000000000002+0j)
```
Absolute errors are 1.3e-15 to 3.1e-15 (float64; the ticket's 2e-15 is slightly exceeded at `L=5`, where the instance RHS is `0.0232`: relative error `3.4e-15`). Both charge orders at every length `n = 2,3,4` agree.
All `μ ∈ {±}^{n-2}` and 2–3 random `a` per case were checked. Other `(d,L,W,g,E,t)` (same script, `run`):
```
d=0 L=3 W=1 g=0.5 E=0.0 t=0.5: max |LHS-RHS| = 8.88e-16 (n=2,3,4)    d=1 L=3 W=1 g=0.0 E=1.5 t=0.0: 1.57e-16 (n=2,3,4)
d=1 L=4 W=3 g=-1.3 E=-1.9 t=0.99: 1.15e-10 abs, max relative error 9.8e-15 (|RHS| ≈ 6e3) (n=2,3,4)
d=2 L=3 W=1 g=2.0 E=0.3 t=0.7: 3.64e-15 (n=2,3,4)                     d=2 L=4 W=2 g=0.7 E=-1.0 t=0.95: 1.18e-14 (n=2,3)
```
Table constants (`table.py`):
```
SB row sum c0+2d*c1 = 1.0
E=0.0: |m|=1.000000000000000 m+*m-=1.000000+0.000000j Im m=1.000000 eta_t=0.100000 kappa=0.000000-0.625000j c_t=1.2500 kappa*(m-conj m)=1.250000+0.000000j conj(kappa)+kappa=0.0e+00 W^d*c_t*(1-t)=1.000
   kappa'(FD)= -6.250000000818101j  kappa/(1-t)= -6.250000000000003j
E=1.0: |m|=1.000000000000000 m+*m-=1.000000+0.000000j Im m=0.866025 eta_t=0.086603 kappa=0.000000-0.721688j c_t=1.2500 kappa*(m-conj m)=1.250000+0.000000j conj(kappa)+kappa=0.0e+00 W^d*c_t*(1-t)=1.000
   kappa'(FD)= -7.216878365801094j  kappa/(1-t)= -7.216878364870325j
Groenwall constant pieces at T0=t=0.9: (1-T0)^-1 = 10.000000000000002 ; W^d = 8 ; L^(2d) = 15625
```
Consistency of the tree-sum definition with `(pro_dyncalK)` (`ode_check.py`: central finite difference `h=1e-5` vs `treeEqRhs`, `d=3, L=3, W=2, g=1/2, E=1, t=9/10`):
```
n=2 sig=[True, False] a=[0, 5]: dK/dt(FD)=0.4505177325+0.0000000000j  treeEqRhs=0.4505177279-0.0000000000j  |diff|=4.6e-09
n=3 sig=[True, False, False] a=[0, 5, 7]: dK/dt(FD)=-0.0001028397-0.0170906354j  treeEqRhs=-0.0001028397-0.0170906350j  |diff|=4.2e-10
n=3 sig=[False, True, True] a=[2, 2, 9]: dK/dt(FD)=-0.0184895240+0.0952608645j  treeEqRhs=-0.0184895238+0.0952608633j  |diff|=1.3e-09
```
Scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/{ward_check,table,ode_check}.py` (python only).

### Verdict
- Target 1 `KLK_ward` (pin `KLwardPin`): **PASS**. Pin is true at every tested point (both `s`, `n = 2,3,4`, `d = 0..3`); every exponent identity (rows 1,3,4,5,8) is exact; Grönwall constant finite for `t < 1` (row 7); no hypothesis is unproved; no `3 ≤ d`, no `L²`.

## (a′) Preflight corrections — Sat Oct  3 06:28:14 UTC 2026
1. Line 10 (route for `s = −`: "flip lemma ... tree-sum level, no ODE") and line 26 (dependencies): the flip is proved by uniqueness, `KLK_unique` (merged, KL4), applied to the family `conj ∘ 𝒦 ∘ flip`, not at the tree-sum level; the dependencies of the target therefore also contain `KLK_unique`. No verdict changes.

## (b) Script output (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2036, branch t/T2036; scripts: /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2036_prover/{evidence.sh,rename2d.py,strip.py,pincheck.py}; the output below is `evidence.txt`, verbatim)
```
$ cd RBM3D-wt/T2036; date -u; git log -1 --format="%h %s"; git status --short; git diff --stat main...HEAD
Sat Oct  3 06:27:28 UTC 2026
9dcb3a6 T2036: KL6 Ward identity KLK_ward (every n, both charge orders), flip lemma KLWard_flip
 RBM3D/Loop/KLWard.lean | 1224 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1224 insertions(+)

$ lake build RBM3D.Loop.KLWard > out.txt 2>&1; echo exit=$?; tail -2 out.txt; grep -c "warning\|error" out.txt
exit=0
Build completed successfully (3246 jobs).
warning/error lines: 0

$ wc -l KLWard.lean; grep -c "^private" KLWard.lean; grep -c "sorry\|admit\|native_decide\|^axiom" KLWard.lean; lines of section Flip (awk /^section Flip/,/^end Flip/ | wc -l)
    1224 RBM3D/Loop/KLWard.lean
53
0
      99

$ lake env lean axioms.lean   (#print axioms of the 7 public declarations)
'RBM.Loop.KLK_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWard_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_two_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_ward_four_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_flip' depends on axioms: [propext, Classical.choice, Quot.sound]

$ sed -n "/^theorem KLK_ward :/,/:= by\$/p" RBM3D/Loop/KLWard.lean   # target statement
theorem KLK_ward :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
        ∑ x : Zd d L, KLK d L g W E t ⟨s :: μ ++ [!s], a ++ [x]⟩
          = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
              (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩) := by
$ sed -n "/^theorem KLWard_flip :/,/:= by\$/p" ...   # new public helper
theorem KLWard_flip :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (σ : List Bool) (a : List (Zd d L)), σ.length = a.length → 1 ≤ a.length →
        KLK d L g W E t ⟨σ.map not, a⟩ = (starRingEnd ℂ) (KLK d L g W E t ⟨σ, a⟩) := by

$ python3 pincheck.py; lake env lean pincheck.lean   # the type of KLK_ward is the body of KLwardPin (check file)
pin body (check file) == KLK_ward type (file), whitespace-normalised: True
'RBM.Loop.T2036Check.pin_is_type_of_KLK_ward' depends on axioms: [propext, Classical.choice, Quot.sound]

$ sed -n "/^theorem KLWardInst_ward_true/,/rfl\$/p; /^theorem KLWardInst_ward_false/,/rfl\$/p" RBM3D/Loop/KLWard.lean   # instances
theorem KLWardInst_ward_true :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false] ++ [!true], [0, 1] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false], [0, 1]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false], [0, 1]⟩) := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) true [false] [0, 1] rfl
theorem KLWardInst_ward_false :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false] ++ [!false], [0, 1] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false], [0, 1]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false], [0, 1]⟩) := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) false [false] [0, 1] rfl
$ grep -n "^theorem KLWardInst" RBM3D/Loop/KLWard.lean
1179:theorem KLWardInst_ward_true :
1188:theorem KLWardInst_ward_false :
1197:theorem KLWardInst_ward_two_false :
1206:theorem KLWardInst_ward_four_false :
1216:theorem KLWardInst_flip :

$ git grep -n "KLWard\|KLK_ward\|KLWardInst" main -- RBM3D | wc -l   # name clash on main
       0

$ git -C ../RBM2D log -1 --format=%h; git -C ../RBM2D log -1 --format=%h c9a24cf; git -C ../RBM2D diff --stat c9a24cf HEAD -- RBM2D/Loop/Ward.lean; code-only (comments stripped) diff c9a24cf vs HEAD
9e0f275
c9a24cf
 RBM2D/Loop/Ward.lean | 61 +++++++++++++++++++---------------------------------
 1 file changed, 22 insertions(+), 39 deletions(-)
7
844,850d843
< example (a₁ : Z2 3) :
<     Kcal_ward 3 2 (by norm_num) (by norm_num) 0 (by norm_num) (1 / 2)
<         ⟨by norm_num, by norm_num⟩ [] [a₁] rfl
<       = WI_calK_two 3 (by norm_num) 2 (by norm_num) (by norm_num)
<         ⟨by norm_num, by norm_num⟩ a₁ :=
<   rfl
< #print axioms Kcal_ward

$ port script: RBM2D c9a24cf Ward.lean:37-922 renamed (rename2d.py) vs KLWard.lean sections 1-4, comments stripped; diff lines:
     779 a.txt
     778 b.txt
21
< variable (d L : ℕ) [NeZero L]
> variable (d L : ℕ) [NeZero L] (g : ℝ)
<     refine LoopIdx.WF.cutGlueL ?_ b le_rfl (by omega) ?_
>     refine LoopIdx.wf_cutGlueL _ b ?_ le_rfl (by omega) ?_
< variable {E : ℝ}
> variable (d : ℕ) {E : ℝ}
< private theorem KLWard_etaT_eq (E t : ℝ) : Gauss.etaT E t = (1 - t) * (mE E).im := by
<   rw [Gauss.etaT, Gauss.spectralZ_im]
> private theorem KLWard_etaT_eq (E t : ℝ) : Gauss.etaT E t = (1 - t) * (mE E).im := rfl
< variable (d L : ℕ) [NeZero L] {E : ℝ}
> variable (d L : ℕ) [NeZero L] (g : ℝ) {E : ℝ}
<       have hWR := LoopIdx.WF.cutGlueR hWFp b hk.1 (Nat.lt_succ_self k) hlpN
>       have hWR := LoopIdx.wf_cutGlueR _ b hWFp hk.1 (Nat.lt_succ_self k) hlpN
<             exact KLWard_norm_SB_apply_le d L hL a b
>             exact KLWard_norm_SB_apply_le d L g hL a b
<       have hWL := LoopIdx.WF.cutGlueL hWFm b le_rfl (by omega) hlmN
>       have hWL := LoopIdx.wf_cutGlueL _ b hWFm le_rfl (by omega) hlmN
<             exact KLWard_norm_SB_apply_le d L hL a b
>             exact KLWard_norm_SB_apply_le d L g hL a b
< private theorem KLWard_of_isPrimitive (hL : 3 ≤ L) (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2)
> private theorem KLWard_of_isKLoop (hL : 3 ≤ L) (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2)

$ Kcal_ward (c9a24cf:969-1000, renamed) vs KLWard_pos, comments stripped: number of differing lines, then the first 14 lines of the diff
33
1,7c1,6
< theorem Kcal_ward :
<   ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
<     ∀ (σ : List Bool) (a : List (Zd d L)), a.length = σ.length + 1 →
<       ∑ x : Zd d L, KLK d L g W E t ⟨true :: σ ++ [false], a ++ [x]⟩
<         = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
<             (KLK d L g W E t ⟨true :: σ, a⟩ - KLK d L g W E t ⟨false :: σ, a⟩) := by
<   intro L W _ hL hW E hE t ht σ a ha
---
> private theorem KLWard_pos (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ}
>     (ht : t ∈ Set.Ico (0 : ℝ) 1) (μ : List Bool) (a : List (Zd d L))
>     (ha : a.length = μ.length + 1) :
>     ∑ x : Zd d L, KLK d L g W E t ⟨true :: μ ++ [false], a ++ [x]⟩
>       = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *

$ lake env lean registry_precheck.lean   # DECISIONS 20 pre-check: import RBM3D, import RBM3D.Loop.KLWard, #assert_rbm_axioms
exit=0
0
axiom audit: 1174 theorems, 419 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
premises found by scanning: 12 (borrowed 2, owed 0, structural 10).

$ lake env lean listdecls.lean   # non-private declarations of the new module
theorem RBM.Loop.KLK_ward
theorem RBM.Loop.KLWardInst_flip
theorem RBM.Loop.KLWardInst_ward_false
theorem RBM.Loop.KLWardInst_ward_four_false
theorem RBM.Loop.KLWardInst_ward_true
theorem RBM.Loop.KLWardInst_ward_two_false
theorem RBM.Loop.KLWard_flip
theorem RBM.Loop.MLoop.congr_simp

$ lake build   (full library; the root does not import KLWard yet: the hub adds the import at merge)
exit=0
Build completed successfully (3734 jobs).
info: RBM3D.lean:74:0: axiom audit: 1166 theorems, 419 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 12 (borrowed 2, owed 0, structural 10).
lines mentioning KLWard: 0

$ lake env lean names.lean (27 #check lines): number of error lines; names_absent.lean (import RBM3D.Loop.KLUnique)
0
Unknown constant `HasDerivAt.star`
Unknown constant `HasDerivAt.conj`
```

Narrative (every number is in the script output above or in the files).
1. Verdict: `KLK_ward` (the only target) is proved for every `n ≥ 2` and both charge orders, with the pin's numeric hypotheses only (no named `Prop` such as `KLPT` as a hypothesis, no `3 ≤ d`). Build exit 0 with 0 warning/error lines, only the three standard axioms, 0 `sorry`/`admit`/`native_decide`/`axiom` matches, `main...HEAD` is `RBM3D/Loop/KLWard.lean` alone (1224 lines, commit 9dcb3a6).
2. Statement = pin: the whitespace-normalised pin body of `docs/tickets/checks/T2036-check.lean` equals the statement of `KLK_ward` (pincheck.py), and `type_of% @KLK_ward = KLwardPin := rfl` compiles.
3. Instances (same file, compiled): `KLWardInst_ward_true` and `KLWardInst_ward_false` are the probe's `KLinst_ward` data (d=3, L=5, W=2, g=1/2, E=0, t=9/10, μ=[−], a=(0,1)); every deterministic hypothesis (3 ≤ 5, 1 ≤ 2, |0| < 2, 0 ≤ 9/10 < 1, length) is discharged by `norm_num`/`rfl`, none is left as a hypothesis. Also n=2 and n=4 with s=−, and `KLWard_flip` at n=3. By (a) both sides at the n=3 data are ≈ −0.0232 i, not 0.
4. Order s=+ is `KLWard_pos`, a port of `Kcal_ward` (RBM2D `Loop/Ward.lean`:37-1000 at c9a24cf; RBM2D HEAD 9e0f275 differs only by comments and the removed `Checks` example, 7 code lines). Lines 37-922 were renamed by script (Z2 L→Zd d L, SB L→SB d L g, primRhs/primInit/IsPrimitive→treeEqRhs/MLoop/IsKLoop, mSig→mSigma, etaT→Gauss.etaT, spectralM→mE, W^2→W^d) and compared with sections 1-4 of the new file with comments stripped: 21 differing lines, all listed above (section variables `d`, `g`; `LoopIdx.WF.cutGlueL/R`→`LoopIdx.wf_cutGlueL/R`; `KLWard_etaT_eq` by `rfl`; explicit `g` in `KLWard_norm_SB_apply_le`; `of_isPrimitive`→`of_isKLoop`). The `2`-loop bound section (`Ward_two_loop_bound` and its `LoopVec` helpers, 924-958) is not ported: merged `KLretire_twoLoopBounded` replaces it. The `Kcal_ward` proof (969-1000) becomes `KLWard_pos` with `isPrimitive_Kcal`→`KLK_isKLoop`, `Kcal_rotate`→`KLK_rotate`, `WI_calK_two`→`KLward_two` (33 differing lines after renaming; the statement part is shown). `Kcal.lean:528` is not ported (merged `KLward_two`); `SumZeroWard.lean:1369-1395` was only read (it flips `Alayer`).
5. Order s=−: `KLK_rotate` does not give it (`⟨s :: σ, b :: a⟩ ↦ ⟨σ ++ [s], a ++ [b]⟩` moves positions and flips no charge), and the induction is not redone. New public lemma `KLWard_flip` (`𝒦(−σ) = conj 𝒦(σ)`; section Flip is 99 lines), proved by `KLK_unique`: `(t, I) ↦ conj 𝒦_{t,flip I}` is again a family of `K`-loops (`S^(B)` is real, `conj m(−s) = m(s)`, flip commutes with the cut operators, `HasDerivAt.star` for the derivative). With `conj κ_t = −κ_t` this reduces s=− to s=+.
6. Dimension: `W^2→W^d` in `κ_t`, `c_t`, the Grönwall constant and the derivative identity; `g` is any real; `L ≥ 3` enters through `sum_SB_row`, `norm_SB_apply_le` and the merged `KLward_two`, `KLK_rotate`; `|m| = 1` through `norm_mE` (`KLWard_mSigma_mul`); no `L²`, no `3 ≤ d`.
7. Registry (DECISIONS §20): the 53 helpers are `private` with prefix `KLWard_`; public names are `KLK_ward` (pinned), `KLWard_flip`, `KLWardInst_*` (`git grep` on `main`: 0 lines). The pre-check exits 0 and finds 12 premises, as the full build without the module does, so no registry line is needed and `RBM3D/Test/Axioms.lean` is untouched. 1174 = 1166 + 7 public theorems + the auto-generated `RBM.Loop.MLoop.congr_simp` (listdecls).
8. One extra import, `Mathlib.Analysis.Calculus.Deriv.Star`, for `HasDerivAt.star` (unknown in the import closure of `RBM3D.Loop.KLUnique`: names_absent output).
9. Not done here: the root import (hub). The full `lake build` (3734 jobs) ran on the unmodified root; the module itself is covered by `lake build RBM3D.Loop.KLWard` and the pre-check.

## (c) Verified Mathlib names (`#check` with `import RBM3D.Loop.KLWard`: 27 lines, 0 error lines)
HasDerivAt.star (Mathlib/Analysis/Calculus/Deriv/Star.lean:45), List.map_take, List.map_drop, List.map_append, List.map_map, map_list_prod, map_sum, map_mul, map_pow, map_sub, map_inv₀, inv_neg, map_ofNat, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I, Function.comp_def, Nat.strong_induction_on, eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right, pi_norm_le_iff_of_nonneg, norm_le_pi_norm, hasDerivAt_pi, HasDerivAt.fun_sum, HasDerivAt.inv, HasDerivAt.ofReal_comp; RBM3D: sbKernel_eq_ofReal, SB_apply.
Verified absent: `HasDerivAt.conj` (unknown constant; no declaration of that name under Mathlib/ by grep); `HasDerivAt.star` is unknown without the Star import. The ported proofs use further Mathlib names, verified by the build.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new. `KLK_ward` is `(WI_calK)` of `lem_WI_K` (`paper/tex/1_2_Intro_model_result.tex:1034-1044`) for `σ = (s, μ, −s)`, `n ≥ 2`, with `t ∈ [0,1)` (the paper's `[0,1]` is T2004d, DECISIONS §15) and the random band matrix model (paper-delta D6). The paper cites [YY_25] Lemma 3.6 for it; here it is proved, not assumed.
- External inputs and unproved `Prop`s: none. Dependencies are merged: `KLK_isKLoop`, `KLK_unique`, `KLK_rotate`, `KLretire_twoLoopBounded`, `KLward_two`.
- Hub: add `import RBM3D.Loop.KLWard` after the last `import` line of `RBM3D.lean`. The module has 1224 lines (design row KL6 estimated 950).
- Process observation: the session scratchpad is shared by concurrent workflows (generic file names such as `ax.lean`, `assemble.py` are in use by others). `scratchpad/precheck_out.txt`, written by me at a first pre-check and read back with 1174 theorems, read 1120 theorems at a later read, with no write by me in between; all evidence above was therefore regenerated in `scratchpad/T2036_prover/`.
