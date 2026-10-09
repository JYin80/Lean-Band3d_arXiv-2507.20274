Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 21:04:34 UTC 2026

### (i) Exponent table

Notation: `K = BAK` (`K_ab = |M^{(B)}_ab|^2`), `Q = M^{(σ₁σ₂)}`, `Θ = (1 - tQ)^{-1}`, data `BAReal d L g κ E m` (= `BASelf d L g E m ∧ κ ≤ Im m`), `0 ≤ t < 1`. `S^{(B)}(0) = I` (paper `def_Thxi`, `1_2:1073-1076`), so `Θ = (1 - tQ)^{-1}` as in `BATheta`/`PropThetaQ` (`Propagator/Pins.lean:214`, `Ring.inverse`).

| item | value | constraint / source | slack |
|---|---|---|---|
| `|Q_ab|` | `= K_ab` for all four `(σ₁,σ₂)` | `BAMss_norm_eq_BAK` (`KKernel.lean:102`): `Q_ab = M_{ba}(σ₁)M_{ab}(σ₂)`, `|M(-)_{xy}| = |M_{xy}|`, `M` symmetric | equality, no loss |
| Ward row sum of `K` | `Σ_b K_ab = 1` exactly (real `E`) | `BAK_row_sum` (`KKernel.lean:124`) needs only `BASelf` (not `3 ≤ L`, not `κ`); `BAMB_row_sq_real` | equality (for complex `z` it would be `< 1`; at real `E` it is `= 1`) |
| `‖Q‖_{∞→∞} = max_a Σ_b |Q_ab|` | `= 1` for all four `(σ₁,σ₂)` | `≤ 1` needed | slack 0 (sharp; table below: 1.000000000000 in 8/8 cases (4 charge pairs, L = 3, 5)) |
| Neumann radius `‖tQ‖_{∞→∞}` | `t` | `< 1` iff `t < 1` | `1 - t` (0.1 at `t = 0.9`); no slack at `t = 1`, so `t < 1` is binding and `t = 1` is excluded |
| invertibility of `1 - tQ` | `Σ_k t^kQ^k` converges, `‖(1-tQ)^{-1}‖_{∞→∞} ≤ (1-t)^{-1}` | Neumann series, `‖tQ‖ ≤ t < 1`; `‖·‖_{∞→∞}` is a submultiplicative operator norm on `ℂ^{Zd d L}` | `(1-t)^{-1}` finite for `t < 1` |
| spectral radius of `Q` | `ρ(Q^{(+,-)}) = 1` (Perron vector `1`); `ρ(Q^{(+,+)}) < 1` numerically (0.716 at `L = 3`, 0.864 at `L = 5`) | not used; only `‖Q‖_∞ ≤ 1` is | `Q^{(+,-)}` has eigenvalue 1, so `Θ^{(+,-)}` blows up at `t = 1` exactly |
| row sum of `Θ^{(+,-)}` | `Σ_b Θ_ab = (1-t)^{-1}` | `Q^{(+,-)} = map ofReal K` (`BAMss_pm_eq`, `BATheta_pm_eq`), `K·1 = 1`, so `(1 - tQ)·1 = (1-t)·1`, hence `Θ·1 = (1-t)^{-1}·1` | equality |
| resolvent | `Θ = 1 + tQΘ = 1 + tΘQ` | `Θ(1-tQ) = (1-tQ)Θ = 1` | identity |
| derivative | `∂_tΘ = ΘQΘ` entrywise, `HasDerivAt` at every `t ∈ [0,1)` (also a two-sided neighbourhood: `Θ` exists for `|t| < 1`) | `d/dt (1-tQ)^{-1} = (1-tQ)^{-1}Q(1-tQ)^{-1}`; twin of `hasDerivAt_Theta_mul_apply` (`Propagator/Deriv.lean:108`) with `μ·SB` replaced by `Q` | identity |
| swap | `Q^{(σ₁σ₂)} = Q^{(σ₂σ₁)}` hence `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}` | `Q_ab = M_{ba}(σ₁)M_{ab}(σ₂)` and `M(σ)` symmetric (`BAMB_symm`): `Q^{(σ₂σ₁)}_ab = M_{ba}(σ₂)M_{ab}(σ₁) = M_{ab}(σ₂)M_{ba}(σ₁)` | identity (uses symmetry of `M^{(B)}` only; probe `BATheta_swap`, `t/T2360:RBM3D/Probe/T2360Pins.lean:387`) |
| conjugation | `Q^{(-,-)} = conj Q^{(+,+)}` entrywise, `Θ^{(-,-)}_t = conj Θ^{(+,+)}_t` | `M(-) = M^* = conj M` (symmetric `M`); `t` real | identity; fails for complex `t` |
| symmetry | `(Q^{(σ₁σ₂)})ᵀ = Q^{(σ₁σ₂)}` hence `Θᵀ = Θ` | `Q_ba = M_{ab}(σ₁)M_{ba}(σ₂) = Q_ab` by symmetry of `M(σ)` | identity |
| `BAMLoop` pairing | `σ_i ↔ (a_{i-1}, a_i)`, `a_{-1} = a_{n-1}`; value `W^{-(n-1)d}∏M(σ_i)_{a_{i-1}a_i}` | `(eq:KMloop)` `1_2:1003`; `loopM` `Loop/GLoopFlow.lean:92`; `E_a = W^{-d}1_{[a]}` (`Loop/GLoop.lean:55`): `tr ∏(M(σ_i)⊗I · E_{a_i})` has `W^d` diagonal terms times `W^{-kd}` = `W^{-(k-1)d}` | exponent `W^{-(n-1)d}` unchanged by the repair |
| `n ≤ 2` agreement | old = new for `n ≤ 2` | `n ∈ {0,1}`: both bodies equal (rotate by `0`/empty; no symmetry needed); `n = 2`: pairings `(a₁,a₀),(a₀,a₁)` vs `(a₀,a₁),(a₁,a₀)`, equal iff `M(σ)` symmetric | needs `(M σ)ᵀ = M σ` only at `n = 2`; false for `n ≥ 3` (witness: 14 vs 15) |
| hypotheses needed beyond `BAReal` | none: `BAReal.1 = BASelf` suffices for every calculus row; `3 ≤ L` not needed; `κ` not needed; `d`, `L` arbitrary (`[NeZero L]`) | rows above use only `BAK_row_sum`, `BAMss_norm_eq_BAK`, `BAMB_symm`, `BAMss_pm_eq` | — |

### (ii) Concrete nondegenerate instance (numerical; no Lean)

Data: `d = 1`, `W = 1`, `L ∈ {3, 5}` (`Adj`: `zdistD = 1`, `Lattice.lean:108`), `g = 0.5`, `E = 0.3`, `m` the root of `m = L^{-d} tr(gΨ - E - m)^{-1}` with `Im m > 0` (found by `fsolve`; residual printed), `κ := Im m` (0.7355 at `L = 3`, 0.8072 at `L = 5`, so `BAReal` holds with equality in `κ`), `M^{(B)} = (gΨ - E - m)^{-1}`, `Q` from the definition `Q_ab = M(σ₁)_{ba}M(σ₂)_{ab}`, `M(+) = M^{(B)}`, `M(-) = M^{(B)*}`. `t ∈ {0, 0.5, 0.9}`; derivative by central difference `h = 1e-6` (error `O(h²)·|Θ'''|`, so `1e-10`…`4e-9` is the expected order); Neumann sum with 4000 terms; trace form with `W^d = 2`, `L = 3`, 200 random `(σ, a)`, `n ≤ 5`, `E_a = W^{-d}1_{[a]}`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/pre.py`

```
== L=3 d=1 W=1 g=0.5 E=0.3: m=-0.219728398270+0.735456339537j  |self_m resid|=0.00e+00  Im m (=kappa)=0.735456
K row sums [1. 1. 1.] col sums [1. 1. 1.] K_aa=|m|^2 True
 sigma=(+,+) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=0.715846549518
 sigma=(+,-) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=1.000000000000
 sigma=(-,+) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=1.000000000000
 sigma=(-,-) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=0.715846549518
 t=0.0: res1=0.0e+00  res2=0.0e+00  deriv=4.4e-11  symm=0.0e+00  swap=0.0e+00  conj=0.0e+00  rowsum=0.0e+00  neumann=0.0e+00  1/(1-t)=1.000000  rowsum Th(+,-)[0]=1.000000
 t=0.5: res1=3.4e-16  res2=3.4e-16  deriv=1.5e-10  symm=1.1e-16  swap=1.1e-16  conj=9.8e-18  rowsum=8.9e-16  neumann=2.2e-16  1/(1-t)=2.000000  rowsum Th(+,-)[0]=2.000000
 t=0.9: res1=8.9e-16  res2=4.4e-16  deriv=4.0e-09  symm=8.9e-16  swap=1.0e-15  conj=1.6e-17  rowsum=3.7e-14  neumann=5.3e-15  1/(1-t)=10.000000  rowsum Th(+,-)[0]=10.000000
== L=5 d=1 W=1 g=0.5 E=0.3: m=-0.068889007022+0.807159076383j  |self_m resid|=1.11e-16  Im m (=kappa)=0.807159
K row sums [1. 1. 1. 1. 1.] col sums [1. 1. 1. 1. 1.] K_aa=|m|^2 True
 sigma=(+,+) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=0.863614149087
 sigma=(+,-) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=1.000000000000
 sigma=(-,+) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=1.000000000000
 sigma=(-,-) ||M||_{inf->inf}=1.000000000000  ||M||_(1->1)=1.000000000000 spec.rad=0.863614149087
 t=0.0: res1=0.0e+00  res2=0.0e+00  deriv=1.8e-10  symm=0.0e+00  swap=0.0e+00  conj=0.0e+00  rowsum=0.0e+00  neumann=0.0e+00  1/(1-t)=1.000000  rowsum Th(+,-)[0]=1.000000
 t=0.5: res1=3.3e-16  res2=3.3e-16  deriv=1.7e-10  symm=8.3e-17  swap=8.3e-17  conj=0.0e+00  rowsum=8.9e-16  neumann=4.4e-16  1/(1-t)=2.000000  rowsum Th(+,-)[0]=2.000000
 t=0.9: res1=4.4e-16  res2=8.9e-16  deriv=3.3e-09  symm=8.9e-16  swap=8.9e-16  conj=0.0e+00  rowsum=1.1e-14  neumann=3.1e-15  1/(1-t)=10.000000  rowsum Th(+,-)[0]=10.000000
witness old (a_i,a_{i+1}) = 14.0  repaired (a_{i-1},a_i) = 15.0
trace form tr prod(M(s_i)E_{a_i}) (W^d=2, random n<=5, 200 samples) vs repaired: mismatches = 0 of 200
```

Reading the output: (1) `K` row/column sums are 1, `K_aa = |m|^2`; (2) `‖Q‖_{∞→∞} = ‖Q‖_{1→1} = 1` for all four `(σ₁,σ₂)` and `|Q| = K` entrywise (assert in the script); (3) at every `t` the resolvent identities `Θ = 1 + tQΘ = 1 + tΘQ`, `Θ_t = Σ t^kQ^k`, symmetry, swap, `Θ^{(-,-)} = conj Θ^{(+,+)}`, `Σ_bΘ^{(+,-)}_ab = (1-t)^{-1}` (10 at `t = 0.9`) hold to `≤ 4e-14`; (4) `∂_tΘ = ΘQΘ` matches the finite difference to `≤ 4e-9`; (5) witness on `Z_3` (`d = 1`, `W = 1`, `σ = (+,+,-)`, labels `(0,1,2)`, `N_01=1, N_12=2, N_20=3`, `N'_01=1, N'_12=5, N'_20=7`): old pairing `(a_i,a_{i+1})` gives 14, repaired `(a_{i-1},a_i)` gives 15, as in the ticket; (6) the repaired index form equals the trace `tr ∏(M(σ_i)⊗I_{W^d}·E_{a_i})` in 200/200 samples and agrees with the old pairing at `n ≤ 2` for symmetric `M` (script `assert`, passed).

Compiled-instance data for 1b (not computed here): merged `KKernelInst` at `d = 3`, `L = 4`, `(g, E, m) = (P.g0, P.E, P.m0)` with `BAReal 3 4 P.g0 κ P.E P.m0` available as `flowP_real` (`CouplingWindow.lean:878`, `κ = (mS 4 10).im`); `KKernel.lean:394-446` already states `BAK`/`BAMss`/`BATheta` instances at it. `t` for the examples: any `t ∈ [0,1)`, e.g. `1/2`. External hypotheses: none (every target is deterministic and uses only merged `BAReal`; no cited-from-other-work input), so no limit computation is required.

### Verdicts

- Target 1 (`BAMLoop` body in place, `FlowPins.lean:272-276`): PASS. The repaired body equals `(eq:KMloop)` / `loopM` (checks 5, 6); `BAMLoop_witness` 15 (new) vs 14 (old).
- Target 2 `BAMLoop_apply`, `BAMLoop_le_two`, `BAMLoop_witness`: PASS (`BAMLoop_le_two` needs symmetric `M σ` only for `n = 2`).
- Target 2 calculus `BATheta_isUnit`, `BATheta_resolvent`, `BATheta_hasDerivAt`, `BATheta_swap`, `BATheta_conj`, `BATheta_isSymm`, `BATheta_row_sum_pm`: PASS under `BAReal` (indeed `BASelf` alone), `0 ≤ t < 1`; `3 ≤ L` not needed. `‖Q‖_{∞→∞} ≤ 1` is sharp (`= 1`), so `t < 1` is binding.
- Optional trace form: statable (check 6 verifies the identity numerically at `W^d = 2`); cost left to 1b.

## (b) Script output (stage 1b, `date -u`: Fri Oct  9 21:25:56 UTC 2026)

Numbering of the blocks below: 1 git state and diff stat; 2 `FlowPins.lean` hunks; 3 module builds; 4 full build; 5 axioms; 6 hygiene grep; then statements, 7 instances, 8 name-clash grep, 9 section-3 size.

```
$ git log --oneline main..t/T2362; git status --short; git diff --stat main...t/T2362
708bbd4 T2362: BA/KBase sections 3-4 (BAMLoop_trace, compiled instances)
a61ba21 T2362: BAMLoop in place (F1) and BA/KBase sections 1-2 (loop lemmas, Theta_BA calculus)
 RBM3D/BA/FlowPins.lean |   6 +-
 RBM3D/BA/KBase.lean    | 569 +++++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 572 insertions(+), 3 deletions(-)
```
```
$ git diff -U0 main...t/T2362 -- RBM3D/BA/FlowPins.lean | grep '^@@'; for n in 274 275; do diff <(git show main:RBM3D/BA/FlowPins.lean | sed -n ${n}p) <(sed -n ${n}p RBM3D/BA/FlowPins.lean) && echo "line $n identical to main"; done; echo 'main 276:'; git show main:RBM3D/BA/FlowPins.lean | sed -n 276p; echo 'branch 276:'; sed -n 276p RBM3D/BA/FlowPins.lean; echo 'branch 274:'; sed -n 274p RBM3D/BA/FlowPins.lean
@@ -272,2 +272,2 @@ variable (d L W : ℕ) [NeZero L]
@@ -276 +276 @@ def BAMLoop (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) :
line 274 identical to main
line 275 identical to main
main 276:
    ((I.σ.zip (I.a.zip (I.a.rotate 1))).map fun p => M p.1 p.2.1 p.2.2).prod
branch 276:
    ((I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map fun p => M p.1 p.2.1 p.2.2).prod
branch 274:
def BAMLoop (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
```
```
$ lake build RBM3D.BA.FlowPins 2>&1 | tail -n 2; lake build RBM3D.BA.KBase 2>&1 | tail -n 2; wc -l RBM3D/BA/KBase.lean
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3734 jobs).
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3739 jobs).
     569 RBM3D/BA/KBase.lean
```
```
$ tail -n 2 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/build_full.txt; grep -c '^error' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/build_full.txt; grep -n 'Built RBM3D.BA.Step1Fam\|Built RBM3D.BA.FlowPins\|Built RBM3D.BA.Prop5Short' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/build_full.txt
Build completed successfully (4173 jobs).
lake build  345.30s user 79.47s system 378% cpu 1:52.12 total
0
4116:✔ [4170/4173] Built RBM3D.BA.Step1Fam (12s)
```
```
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/axioms.lean
'RBM.BA.BAMLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_witM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_witness_old' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_row_sum_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KBaseInst.witM_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/BA/KBase.lean RBM3D/BA/FlowPins.lean; echo "exit $? (1 = none)"
exit 1 (1 = none)
```
Statements, extracted by script (`python3 .../extract.py`; section variables listed after):
```
L54: theorem BAMLoop_apply (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) (n : ℕ)
    (hn : 1 ≤ n) (hσ : I.σ.length = n) (ha : I.a.length = n) :
    BAMLoop d L W M I = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
      ∏ i ∈ Finset.range n, M (I.σ.getD i false) (I.a.getD ((i + (n - 1)) % n) 0) (I.a.getD i 0) := by
L81: theorem BAMLoop_le_two (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (hM : ∀ σ, (M σ)ᵀ = M σ)
    (I : LoopIdx (Zd d L)) (hn : I.length ≤ 2) :
    BAMLoop d L W M I = (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) *
      ((I.σ.zip (I.a.zip (I.a.rotate 1))).map fun p => M p.1 p.2.1 p.2.2).prod := by
L102: def BAMLoop_witM (σ : Bool) : Matrix (Zd 1 3) (Zd 1 3) ℂ :=
L108: theorem BAMLoop_witness :
    BAMLoop 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ = 15 := by
L121: theorem BAMLoop_witness_old :
    (((((1 : ℕ) : ℂ) ^ 1)⁻¹) ^ (([true, true, false] : List Bool).length - 1) *
      ((([true, true, false] : List Bool).zip (([![0], ![1], ![2]] : List (Zd 1 3)).zip
        (([![0], ![1], ![2]] : List (Zd 1 3)).rotate 1))).map
          fun p => BAMLoop_witM p.1 p.2.1 p.2.2).prod) = 14 := by
L434: theorem BAMLoop_trace (d L W : ℕ) [NeZero L] [NeZero W] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) {n : ℕ} (hn : 1 ≤ n)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    BAMLoop d L W M (loopOf σ a) =
      Matrix.trace (List.ofFn fun i : Fin n =>
        (M (σ i) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)) * Eblk d L W (a i)).prod := by
L324: theorem BATheta_isUnit (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    IsUnit (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) :=
L330: theorem BATheta_resolvent (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t σ₁ σ₂ = 1 + (t : ℂ) •
        (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂) ∧
      BATheta d L g E m t σ₁ σ₂ = 1 + (t : ℂ) •
        (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) :=
L341: theorem BATheta_hasDerivAt (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    HasDerivAt (fun s : ℝ => BATheta d L g E m s σ₁ σ₂ a b)
      ((BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
        BATheta d L g E m t σ₁ σ₂) a b) t :=
L350: theorem BATheta_swap {d L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t σ₁ σ₂ = BATheta d L g E m t σ₂ σ₁ := by
L362: theorem BATheta_conj (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a b : Zd d L) :
    BATheta d L g E m t false false a b = starRingEnd ℂ (BATheta d L g E m t true true a b) :=
L371: theorem BATheta_isSymm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    (BATheta d L g E m t σ₁ σ₂)ᵀ = BATheta d L g E m t σ₁ σ₂ :=
L381: theorem BATheta_row_sum_pm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a : Zd d L) :
    ∑ b, BATheta d L g E m t true false a b = (1 - (t : ℂ))⁻¹ := by
47:variable (d L W : ℕ) [NeZero L]
148:variable {d L : ℕ} [NeZero L] {Q : Matrix (Zd d L) (Zd d L) ℂ}
302:variable (d L : ℕ) [NeZero L]
```
Instances (section 4 of the file, extracted by script `inst_extract.py`: `example` heads and the applying term):
```
L503: theorem witM_symm (σ : Bool) : (BAMLoop_witM σ)ᵀ = BAMLoop_witM σ := by
L511: example : BAMLoop 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ =
L516:   BAMLoop_apply 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ 3 (by norm_num) rfl rfl
L519: example : BAMLoop 1 3 1 BAMLoop_witM ⟨[true, false], [![0], ![2]]⟩ =
L522:   BAMLoop_le_two 1 3 1 BAMLoop_witM witM_symm ⟨[true, false], [![0], ![2]]⟩ (by decide)
L525: example : BAMLoop 1 3 2 BAMLoop_witM (loopOf ![true, true, false] ![![0], ![1], ![2]]) =
L528:   BAMLoop_trace 1 3 2 BAMLoop_witM (by norm_num) _ _
L531: example : IsUnit (1 - (((1 / 2 : ℝ)) : ℂ) • BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false) :=
L532:   BATheta_isUnit 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true false
L534: example : IsUnit (1 - (((1 / 2 : ℝ)) : ℂ) • BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false false) :=
L535:   BATheta_isUnit 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) false false
L538: example : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true = 1 + (((1 / 2 : ℝ)) : ℂ) •
L542:   BATheta_resolvent 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true true
L545: example : HasDerivAt (fun s : ℝ => BATheta 3 4 P.g0 P.E P.m0 s true false 0 ![1, 0, 0])
L548:   BATheta_hasDerivAt 3 4 P.g0 P.m0.im P.E P.m0 P.real (by norm_num) (by norm_num) true false 0 ![1, 0, 0]
L551: example : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false = BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false true :=
L552:   BATheta_swap P.g0 P.E P.m0 (1 / 2) true false
L555: example : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![1, 0, 0] =
L557:   BATheta_conj 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) 0 ![1, 0, 0]
L560: example : (BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true)ᵀ = BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true :=
L561:   BATheta_isSymm 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true true
L564: example : ∑ b, BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 b = (1 - (((1 / 2 : ℝ)) : ℂ))⁻¹ :=
L565:   BATheta_row_sum_pm 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) 0
```
```
$ grep -rn -E '(BAMLoop_(apply|le_two|witM|witness|witness_old|trace)|BATheta_(isUnit|resolvent|hasDerivAt|swap|conj|isSymm|row_sum_pm)|KBaseInst|BAKBase_)' RBM3D RBM3D.lean --include='*.lean' | grep -v '^RBM3D/BA/KBase.lean'; echo "worktree exit $? (1 = no clash)"; grep -rn -E '(BAMLoop_(apply|le_two|witM|witness|witness_old|trace)|BATheta_(isUnit|resolvent|hasDerivAt|swap|conj|isSymm|row_sum_pm)|KBaseInst|BAKBase_)' /Users/junyin/Lean_proof/RBM3D/RBM3D /Users/junyin/Lean_proof/RBM3D/RBM3D.lean --include='*.lean' | grep -v '/Probe/'; echo "main worktree exit $? (1 = no clash)"
worktree exit 1 (1 = no clash)
main worktree exit 1 (1 = no clash)
```
```
$ awk '/^\/-! ## 3/{f=1} /^\/-! ## 4/{f=0} f{n++} END{print "section 3 lines (header to section 4 header):", n}' RBM3D/BA/KBase.lean
section 3 lines (header to section 4 header): 97
```

### Narrative (stage 1b)

* Scope: branch `t/T2362`, two commits (block 1); only `BA/FlowPins.lean` (hunks `-272,2` and `-276`, block 2) and the new `BA/KBase.lean` (569 lines; stop line 950 not reached; section commits at 390 and 569 lines). `Test/Axioms.lean` untouched (no registry change).
* Target 1: the `BAMLoop` body is the probe's `BAMLoop'` body; line 274 (name, binders, result type) and line 275 (the factor `(W^d)⁻¹ ^ (I.length - 1)`) are identical to main (block 2). The docstring states `σ_i` on the edge `(a_{i-1}, a_i)`, cyclic, with `(eq:KMloop)`, `A:571`, `loopM`. I read `1_2:995-1010, 1065-1080` and `A:566-575`: `(eq:KMloop)` is `tr ∏ (M(σ_i) E_{a_i})`; `(eq:Msig)` is `M^{(σ₁σ₂)}_{ab} = M^{(B)}_{ba}(σ₁) M^{(B)}_{ab}(σ₂)`, as merged `BAMss`.
* Loop part: `BAMLoop_apply` (index form: `List.getD`, `Finset.range n`, cyclic predecessor `a_{(i+n-1)%n}`); `BAMLoop_le_two` needs only `I.length ≤ 2` and `∀ σ, (M σ)ᵀ = M σ` (no `σ`-length hypothesis); `BAMLoop_witness` is the value 15, `BAMLoop_witness_old` the old pairing's 14 at the same data; `BAMLoop_trace` (the recommended trace form, `n ≥ 1`, `[NeZero W]`, `List.ofFn` order of `loopM`) is delivered, section 3 = 97 lines (block 9, within the 100-line allowance).
* Calculus: the seven pinned names, hypotheses exactly `BAReal d L g κ E m`, `0 ≤ t`, `t < 1`. The proofs use only `hr.1 : BASelf` (through `BAK_row_sum` and `BAMss_norm_eq_BAK`): `κ` and `3 ≤ L` are not used, as (a) row 25 predicted. `BATheta_swap` is stated as probe line 387 (implicit `d L`, no hypothesis on `g E m t`). `BATheta_conj` is entrywise and needs real `t`.
* Route: private lemmas `BAKBase_*` for a generic `Q` with row sums of `|Q|` at most 1 (`‖Q‖_{∞→∞} ≤ 1`, `Units.oneSub`), real parameter `t`: twins of merged RBM3D `Propagator/Basic.lean:78-104,203` and `Propagator/Deriv.lean:44,57,78,108` (resolvent identity, continuity, slope argument). No port from RBM1D/RBM2D (no diff-stat needed).
* Instances: block 7. Loop targets at the witness data (`d = 1`, `L = 3`, `W = 1`; `W = 2` for the trace form so that `W^d = 2`); calculus targets at the merged flow point `P` (`MFixedPoint.lean:893`, `P.real` is the field at `:883`), `t = 1/2`, charge pairs `(+,-)`, `(-,-)`, `(+,+)`. Every hypothesis is discharged (`by norm_num`, `rfl`, `by decide`, `P.real`); none is another gate's pin.
* Builds: `lake build RBM3D.BA.FlowPins` and `RBM3D.BA.KBase` pass; the full `lake build` (4173 jobs, 0 errors, block 4) was run at the final commit `708bbd4` (tree clean, block 1) and rebuilt `BA.Step1Fam`. `RBM3D.lean` does not import `RBM3D.BA.KBase` yet (hub adds it at merge), so that build's `#assert_rbm_axioms` did not see KBase; block 5 is the axiom evidence for KBase.
* Names: public names are the ticket's plus `BAMLoop_witM`, `BAMLoop_witness_old`, `BAMLoop_trace`, `KBaseInst.witM_symm`; helpers are `private` with prefix `BAKBase_`; no clash on main or in the worktree (block 8).
* Section (a): read, no correction needed (no (a′)); the facts the proofs use agree with the compiled lemmas.

## (c) Verified Mathlib names

`lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/names.lean` (a `#check` of each name below; exit 0); three per line:
`Matrix.linfty_opNNNorm_def`, `Units.oneSub`, `Units.val_oneSub`
`NormedRing.inverse_continuousAt`, `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`
`hasDerivAt_iff_tendsto_slope`, `slope_def_module`, `Complex.real_smul`
`eventually_nhdsWithin_of_eventually_nhds`, `isOpen_lt`, `continuous_abs`
`Matrix.mul_kronecker_mul`, `Matrix.trace_kronecker`, `Matrix.trace_one`
`Matrix.one_kronecker_one`, `map_list_prod`, `List.map_map`
`List.getElem?_ofFn`, `List.getD_eq_getElem?_getD`, `List.range_succ`
`List.prod_append`, `Matrix.mul_diagonal`, `Finset.sum_ite_eq'`
`Fin.prod_univ_eq_prod_range`, `List.prod_ofFn`, `List.getElem_rotate`
`Nat.add_mod_right`, `sub_eq_iff_eq_add`, `Complex.norm_real`
`Complex.continuous_ofReal`, `RBM.continuous_matrix_entry`, `RBM.one_sub_ne_zero`

## (d) Open issues and paper-delta candidates

* **T2362a (candidate).** `def_Theta` (`1_2:1072`) defines `Θ_t^{(σ₁,σ₂)}` "for `t ∈ [0,1]`". For the block Anderson model at real `E`, `M^{(+,-)} 1 = 1` (`BAK_row_sum`), so `1 - M^{(+,-)}` is not invertible at `t = 1`; compiled negative statement (scratch file, not committed):
```
$ sed -n 5,6p /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/neg.lean; lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362/neg.lean; echo "exit $?"
theorem BAKBase_neg_t_one (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) :
    ¬ IsUnit (1 - (((1 : ℝ)) : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) true false) := by
exit 0
```
  The Lean calculus is stated for `0 ≤ t < 1` (ticket); this changes no Lean statement (note for the dispatcher's paper-deltas).
* Already recorded, not new: F1 is D632 = T2360a; `BATheta_swap` is T2360c (`Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}`, a remark of the paper, now compiled with no hypothesis).
* Remark: the calculus needs `BASelf` only; `BAReal` (with `κ`) is carried because the ticket pins the calculus under `BAReal`. No Lean/paper statement difference.
* Hub at merge: add `import RBM3D.BA.KBase` after the last `import` line of `RBM3D.lean`; supervisor K-a (no other stage-K row mentioning `BAKsol`, `BAKloop`, `BAMLoop`, `baFM*` before this merge).
