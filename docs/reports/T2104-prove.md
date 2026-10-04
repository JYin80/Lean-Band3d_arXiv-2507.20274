Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 03:16:39 UTC 2026

Sources: RBM2D `Path/DuhamelTail` (967 lines) and `Induction/GridDuhamelN` (510 lines) read with `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/<file>` (RBM2D HEAD is `9e0f275`, not `c9a24cf`); merged `RBM3D/Path/{Kernel,UBounds,Expansion,Azuma,Walk}.lean`, `RBM3D/Kernel/Evolution.lean`. Paper: `def_Ustz`, `int_K-L_ST`, `alu9_STime` (BDG replaced by Azuma, D10).

### (i) Exponent table (every `d = 2` token of both files)

| # | RBM2D token (count at c9a24cf: DuhamelTail / GridDuhamelN) | `d >= 3` value | Constraint / why it holds | Slack |
|---|---|---|---|---|
| 1 | `L ^ 4` label count (4 / 0; `card_label`, `cheb_tail` RHS) | `L^(2d)` (`card (Zd d L x Zd d L) = (L^d)^2`, `card_Zd`) | union bound over all labels `(a1,a2)`; `d = 3, L = 3`: 729 | equality |
| 2 | `W ^ 2`, `W^-2`, `(W L)^2`, `scaleM`, `ellT`, `tailT` (0 / 0) | none occurs | the two files never use `W` or `N`; `W` enters only as `Idx d (sz.L n) (sz.W n)` inside `pathH`, `martInc` | n/a |
| 3 | `Z2 L` (55 / 21): label type | `Zd d L` (R2), `Fin k -> Zd d L` | type change only; sums are `Fintype` sums, `Nonempty` witness `0` | n/a |
| 4 | back-kernel constant `4` (merged `uopBack`, `4 * alpha`) | `4 = 2^2`, dimension-free: per slot row `l1 <= 1 + (t-u)|xi|/(1-u|xi|) <= 2` (`UBounds:467-513`, uses only `3 <= L`, `||SB|| = 1`, `norm_Theta_le`) | needs `0 <= u <= t < 1`, `|xi| <= 1`, `3 <= L`; any real `g` | 0 at `u = 0`, `t -> 1`, `|xi| = 1` (sharp); at `t = 1/2`: row sum <= 1.5 |
| 5 | `det_bound` constant `4 * (4 * sum r)` | unchanged: `hFwd` (forward bound `4 r_j`) is a hypothesis, `uopBack` gives the second `4` | the forward kernel `U_{u_{j+1},t}` has no uniform bound as `t|xi| -> 1`; so `hR` does not imply `hFwd` (conditional adapter, as RBM2D) | n/a |
| 6 | Azuma constants `4`, `4 sum c` (`azuma_complex`, merged) | unchanged: `P(|sum| >= x) <= 4 exp(-x^2/(4 sum c))` | `Re`/`Im` each at `x/sqrt 2`, factor `2 exp(-x^2/(4 sum c))` each; `c` is a variance proxy (`N(0,c)`); no `d` | MC below: bound - empirical >= 0.0077 at every grid `x` |
| 7 | `xi = |m(E)|^2` (`Complex.normSq (spectralM E)`, 5 / 1) | `normSq (mE E) = 1` for `|E| <= 2` (`norm_mE`, `Expansion_normSq_mE`); slot `m(s_i) m(s_{i+1})` is `cycProd (mSigma E . )`, `norm = 1` | `|v xi| = v < 1` for `v < 1` | `2 - |E|` (pin `|E| < 2`; `<= 2` suffices) |
| 8 | grid window `0 <= s n <= t n < 1`, `K n != 0`, `k <= K n`, `u_j = s + j (t-s)/K` | same | `u_j in [s n, t n] subset [0,1)` (`gridTime_last`); `StoppedAzuma108` and `GridDuhamelN` hypotheses are used only at index `n`: state `_at` forms (T2098 `stoppedDuhamel105_at`, D188) | `1 - t n`: `s = 0, t = 1/2, K = 50`: `1/2` |
| 9 | boundary values (DECISIONS §29) | `k = 0`: empty sum, RHS `4 exp(0) = 4`; `x = 0`: RHS `4`; `sum c = 0`: Lean `x^2/0 = 0`, RHS `4` | `P <= 1 <= 4`, true; `union` form needs `x 0 a > 0` and sum over `k in Icc 1 K` (RBM2D `hx0`) | n/a |
| 10 | lattice `3 <= L`, coupling `g = sz.lam n` (RBM2D: no `g`) | `Uop d (sz.L n) (sz.lam n) xi v w` as merged `StoppedDuhamel105`; `d` enters only via `Theta d L g`, `SB d L g` | `SB` doubly stochastic needs `3 <= L` (2d neighbours); no condition on `g` (`1 + 2 d g^2 > 0`) | `L - 3`; `g` free |
| 11 | `Ugen L E sigma v w` (slot `m(s_i) m(s_{i+1})`, cyclic) | merged `UN d L g (fun i => mSigma E (sigma i)) v w` or `Ugen` re-defined with `ukerMat d L g`; `UN` uses `cycProd` (`finRotate`) = RBM2D `sigma (i+1)` on `Fin k` | at `k = 2`, `sigma = (+,-)`: both slots `m_+ m_- = |m|^2 = 1` (script, E = 0, 1.3, -1.9, 2), i.e. `Ugen = Uop` at `xi = |m|^2` after `Fin 2 -> Zd ~ Zd x Zd`, `Fin.prod_univ_two`: so `GridDuhamelN_Ugen_duhamel_telescope` at `n = 2` is `Uop_duhamel_telescope` (Kernel:292) | n/a |

Findings (not exponents):
* F1. RBM3D has no `Ugen`, `AvecN`, `martIncN`, `predIncN`, `StoppedDuhamelN`, `StoppedAzumaN` (T2049 skipped them: `T2049-prove.md` item 3). GridDuhamelN.lean must define them (RBM2D `HierVocab.lean:387-474`, renamed `sz : Sizes d`): `AvecN sz E s t K n j sigma omega a := sz.STLKM n (E n) (gridTime s t K n j) (pathH sz s t K n j omega) sigma a` (`Step2Defs:68`; at `k = 2` it is `Avec`), `martIncN`, `predIncN` with `Ugen`, `StoppedDuhamelN` as `StoppedDuhamel105` with `(E : N -> R)`.
* F2. `uopBack` is in `RBM3D/Path/UBounds.lean` (T2097, merged 5bef95c), not in the ticket's import list, and `Expansion` does not import it (script below): DuhamelTail must `import RBM3D.Path.UBounds`.
* F3. Measurability of `Avec`/`AvecN` along the walk needs no `HermTestFun`/`GoodEvent` (class c, not ported): `walk_measurable_loopFine` (`Walk:794`) composed with `pathH_measurable_filt` (`Stop:159`) replaces RBM2D `GoodEvent_measurable_gloop`.
* F4. `stoppedAzumaN` is not in P.1's consumed list for row 4 (6 names); dropping it is allowed if the report says so.
* F5. No statement is false at `d >= 3`; the only exponent change is row 1 (`L^4 -> L^(2d)`).

### (ii) Concrete instance: `d = 3`, `L = 3`, `W = 2` (same sizes as `StepDecompLoop_sizes`), `g = 1/2`, `E = 0`

Hypotheses at once: `|E| = 0 < 2`; `s = 0 <= t = 1/2 < 1`; `K = 50` (Azuma) / `K = 2` (telescope); `k = K`; `3 <= L`; `NeZero L`; `tau` = first exit of `|S_j|` from radius `theta`, `{j < tau}` is `F_j`-measurable; conditional sub-Gaussian proxies `c_j = s^2 ||K_j||^2` with `s = 0.05` (Gaussian increments, both parts `N(0, c_j)`); `n = 3` slots, `sigma = (+,+,-)` (slot params `-1, 1, 1`), grid `u = (0, 1/4, 1/2)`; tensors `27^3 = 19683` entries. `Uop`, `ukerMat` as `Path/Kernel:46-51`, `SB`, `Theta` as `Defs/Block:38-44`, `Propagator/Basic:70`.

Command and output (script `scratchpad/T2104/inst2104.py`, numpy 2.0.2; scratch only):

```
$ cd <scratchpad>/T2104 && python3 inst2104.py
d,L,W,g = 3 3 2 0.5  |Z_L^d| = 27  label count L^(2d) = 729 = L^6 = 729
SB row sums all 1: True  neighbours per point: 6
E= 0.00 slots (+,-): [1.+0.j 1.+0.j]  normSq(mE)= 1.0
E= 1.30 slots (+,-): [1.+0.j 1.-0.j]  normSq(mE)= 1.0
E=-1.90 slots (+,-): [1.+0.j 1.-0.j]  normSq(mE)= 1.0
E= 2.00 slots (+,-): [1.+0.j 1.+0.j]  normSq(mE)= 1.0
slot parameters xi_i = m(s_i)m(s_{i+1}): [-1.+0.j  1.+0.j  1.+0.j]  norms [1. 1. 1.]
telescope n=3, 2 steps: max|A_2 - rhs| = 1.439917960680388e-14  max|A_2| = 4.7157658470278685
Ugen_self  max|U_{v,v}A - A| (v=1/4): 7.856740153113387e-15
Ugen_comp  max|U_{v,w}U_{u,v}A - U_{u,w}A| (u,v,w=0,.25,.5): 1.2872843271903405e-14
max row l1 norm of back kernel U_{t,u} one slot (<= 2): 1.4566604616581025  => two slots <= 4 = 4
sum_j c_j = 0.22276344551465446  stopped before k: 0.8708  (npaths=10000, K=50)
   x/sqrt(sum c)   P_emp(stopped)  P_emp(unstopped)   bound 4exp(-x^2/(4 sum c))
       0.00           1.0000            1.0000         4.0000
       0.50           0.9453            0.8903         3.7577
       1.00           0.8708            0.6151         3.1152
       1.50           0.0005            0.3297         2.2791
       2.00           0.0000            0.1364         1.4715
       3.00           0.0000            0.0107         0.4216
       4.00           0.0000            0.0002         0.0733
       5.00           0.0000            0.0000         0.0077
max over x of (P_emp - bound): stopped -0.0077, unstopped -0.0077  (must be <= 0; MC s.e. <= 0.005)
```

Import check (script `scratchpad/T2104/deps.py`: transitive `import RBM3D.*` closure of `Path.{Expansion,Azuma,Kernel,StepDecompLoop}`):

```
RBM3D.Induction.Step2Defs True   (so sz.STLKM, STKloop available)
RBM3D.Path.UBounds False         (uopBack: import explicitly)
RBM3D.Path.Kernel True   RBM3D.Kernel.Evolution True   RBM3D.Path.Stop True
RBM3D.Path.Walk True     RBM3D.Path.Azuma True         RBM3D.Defs.Semicircle True
$ grep -rnE "\b(Ugen|AvecN|martIncN|predIncN|StoppedDuhamelN|StoppedAzumaN)\b" RBM3D | cut -c1-160
RBM3D/Induction/Step2Defs.lean:814:index `k` follows from the decomposition by the algebraic telescope of `Ugen`, RBM2D   (a comment: no definition)
```

External hypothesis: none (the `Azuma` sub-Gaussian input is a hypothesis of the pin; the instance above realises it by Gaussian increments with `c_j` the exact conditional variance). Limit computation of TEAM §8 lesson 14 is not needed (no external hypothesis).

### Verdict

* `StoppedAzuma108` (+ `stoppedAzuma108`, `stopped_duhamel_azuma_tail_fixed/_union`, `stopped_duhamel_cheb_tail` with `L^(2d)`, `stopped_duhamel_det_bound`): PASS.
* `GridDuhamelN_Ugen_add/_self/_comp/_UgenHom/_Ugen_duhamel_telescope`, `stoppedDuhamelN`: PASS (needs the definitions of F1 inside `GridDuhamelN.lean`).

## (b) Script output — Sun Oct  4 03:29:09 UTC 2026

```
$ cd RBM3D-wt/T2104 && git log -1 --format=%h && git diff --stat main...t/T2104
b3f7b96
 RBM3D/Induction/GridDuhamelN.lean | 778 +++++++++++++++++++++++++++++++
 RBM3D/Path/DuhamelTail.lean       | 951 ++++++++++++++++++++++++++++++++++++++
 2 files changed, 1729 insertions(+)
$ lake build RBM3D.Path.DuhamelTail RBM3D.Induction.GridDuhamelN 2>&1 | tail -2   (then full `lake build | tail -1`)
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3759 jobs).
Build completed successfully (3848 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" <both files>
RBM3D/Path/DuhamelTail.lean:0
RBM3D/Induction/GridDuhamelN.lean:0
$ #print axioms of the 30 new public names + #assert_rbm_axioms  (scratch axprobe.lean: import RBM3D + both new modules); exit code:
exit=0
lines with exactly [propext, Classical.choice, Quot.sound]: 30 of 30
other axiom lines: 0; 'unregistered' / error lines in output: 0
Path.stoppedEdge Path.stoppedEdge_apply Path.stopped_duhamel_azuma_tail_fixed Path.stopped_duhamel_azuma_union Path.stopped_duhamel_cheb_tail Path.stopped_duhamel_det_bound Path.StoppedAzuma108 Path.stoppedAzuma108 Path.stoppedAzuma108_at Ind.Ugen Ind.GridDuhamelN_Ugen_add Ind.GridDuhamelN_Ugen_self Ind.GridDuhamelN_Ugen_comp Ind.GridDuhamelN_UgenHom Ind.GridDuhamelN_UgenHom_apply Ind.GridDuhamelN_Ugen_duhamel_telescope Ind.Ugen_two_eq_Uop Ind.AvecN Ind.martIncN Ind.predIncN Ind.StoppedDuhamelN Ind.stoppedDuhamelN_at Ind.stoppedDuhamelN Ind.AvecN_two Ind.martIncN_two Ind.predIncN_two Ind.stoppedDuhamel105_of_stoppedDuhamelN Ind.StoppedAzumaN Ind.stoppedAzumaN_at Ind.stoppedAzumaN 
$ name-clash grep (git grep on main for each new public name, other files): 
(no output above = no clash; sanity:        1 hit for the merged stoppedDuhamel105_at)
$ RBM2D diff-stat (RBM2D HEAD 9e0f275; the port is of the c9a24cf text):
  git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/DuhamelTail.lean RBM2D/Induction/GridDuhamelN.lean RBM2D/Induction/HierVocab.lean
 RBM2D/Induction/GridDuhamelN.lean | 312 +--------------------------
 RBM2D/Induction/HierVocab.lean    | 392 +++++++---------------------------
 RBM2D/Path/DuhamelTail.lean       | 432 ++++----------------------------------
 3 files changed, 128 insertions(+), 1008 deletions(-)
$ statement diff, RBM2D@c9a24cf (rename rules R1-R3, Z2 -> Zd d, L -> d L g, Ugen L -> Ugen d L g d (sz.L n) (sz.lam n), spectralM -> mE) vs RBM3D, token level (scratchpad stmts.py)
stoppedEdge: token-identical
stoppedEdge_apply: token-identical
stopped_duhamel_azuma_tail_fixed: token-identical
stopped_duhamel_azuma_union: token-identical
stopped_duhamel_cheb_tail: token-identical
stopped_duhamel_det_bound: token-identical
StoppedAzuma108: token-identical
GridDuhamelN_Ugen_add: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
GridDuhamelN_Ugen_self: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
GridDuhamelN_Ugen_comp: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
GridDuhamelN_UgenHom: differs by: delete RBM2D[[NeZero k]] RBM3D[-]; delete RBM2D[L] RBM3D[-]
GridDuhamelN_Ugen_duhamel_telescope: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
StoppedDuhamelN: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
StoppedAzumaN: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
predIncN: differs by: delete RBM2D[[NeZero k]] RBM3D[-]
```

```
$ python3 extract.py <file> <names>   (target statements, extracted from the files; section variables: (d L : ℕ) [NeZero L] (g : ℝ), {d : ℕ} (sz : Sizes d))
-- DuhamelTail.lean:715
def StoppedAzuma108 [IsFiniteMeasure (pathP sz)] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  |E| < 2 → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n : ℕ) (τ : PathΩ sz → ℕ), (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ (k : ℕ), k ≤ K n → ∀ (a : Zd d (sz.L n) × Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      (∀ j < k,
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω') a)
            ω).re) (c j) (pathP sz) ∧
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω') a)
            ω).im) (c j) (pathP sz)) →
      ∀ x : ℝ, 0 ≤ x →
        (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n k) (martInc sz E s t K n j ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range k, (c j : ℝ)))
806:theorem stoppedAzuma108 [IsFiniteMeasure (pathP sz)] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
807-    StoppedAzuma108 sz E s t K :=
808-  fun _ _ _ _ _ n τ hτ k _ a c hsubG _ hx =>
-- GridDuhamelN.lean:82
theorem GridDuhamelN_Ugen_add (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (A B : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v w (A + B) = Ugen d L g E σ v w A + Ugen d L g E σ v w B := by
-- GridDuhamelN.lean:91
theorem GridDuhamelN_Ugen_self (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (A : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v v A = A := by
-- GridDuhamelN.lean:108
theorem GridDuhamelN_Ugen_comp (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (A : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v w (Ugen d L g E σ u v A) = Ugen d L g E σ u w A := by
-- GridDuhamelN.lean:161
theorem GridDuhamelN_Ugen_duhamel_telescope (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j)
    (hu1 : ∀ j ≤ m, u j < 1) (A : ℕ → ((Fin k → Zd d L) → ℂ)) :
    A m = Ugen d L g E σ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Ugen d L g E σ (u (j + 1)) (u m)
        (A (j + 1) - Ugen d L g E σ (u j) (u (j + 1)) (A j)) := by
-- GridDuhamelN.lean:293
def StoppedDuhamelN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz),
      min j (τ ω) ≤ K n →
      AvecN sz E s t K n (min j (τ ω)) σ ω =
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
            (AvecN sz E s t K n 0 σ ω) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
              (gridTime s t K n (min j (τ ω)))
              (predIncN sz E s t K n i σ ω + martIncN sz E s t K n i σ ω)
335:theorem stoppedDuhamelN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedDuhamelN sz E s t K :=
$ grep -n "^example" <both files>   (compiled instances; every one elaborates in the build above)
RBM3D/Path/DuhamelTail.lean:844:example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (c : ℕ → ℝ≥0)
RBM3D/Path/DuhamelTail.lean:873:example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (x : ℝ) (hx : 0 ≤ x) :
RBM3D/Path/DuhamelTail.lean:896:example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (τ : PathΩ sz0 → ℕ)
RBM3D/Path/DuhamelTail.lean:914:example (a : Zd 3 3 × Zd 3 3) :
RBM3D/Induction/GridDuhamelN.lean:644:example (A B : (Fin 3 → Zd 3 3) → ℂ) :
RBM3D/Induction/GridDuhamelN.lean:651:example (A : (Fin 3 → Zd 3 3) → ℂ) :
RBM3D/Induction/GridDuhamelN.lean:657:example (A : (Fin 3 → Zd 3 3) → ℂ) :
RBM3D/Induction/GridDuhamelN.lean:665:example (A : (Fin 3 → Zd 3 3) → ℂ) :
RBM3D/Induction/GridDuhamelN.lean:672:example (A : ℕ → ((Fin 3 → Zd 3 3) → ℂ)) :
RBM3D/Induction/GridDuhamelN.lean:689:example (ω : PathΩ sz0) :
RBM3D/Induction/GridDuhamelN.lean:714:example : StoppedDuhamel105 sz0 0 GridDuhamelN_instS GridDuham
RBM3D/Induction/GridDuhamelN.lean:721:example (a : Fin 3 → Zd 3 (sz0.L 0)) (c : ℕ → ℝ≥0)
RBM3D/Induction/GridDuhamelN.lean:752:example (a : Fin 3 → Zd 3 (sz0.L 0)) (x : ℝ) (hx : 0 ≤ x) :
$ sed -n 672,688p RBM3D/Induction/GridDuhamelN.lean   (telescope at d=3, L=3, g=1/2, E=0, sigma=(+,+,-), u j = j/10, m=3)
example (A : ℕ → ((Fin 3 → Zd 3 3) → ℂ)) :
    A 3 = Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma ((fun j : ℕ => (j : ℝ) / 10) 0)
        ((fun j : ℕ => (j : ℝ) / 10) 3) (A 0) +
      ∑ j ∈ Finset.range 3, Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma
        ((fun j : ℕ => (j : ℝ) / 10) (j + 1)) ((fun j : ℕ => (j : ℝ) / 10) 3)
        (A (j + 1) - Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma
          ((fun j : ℕ => (j : ℝ) / 10) j) ((fun j : ℕ => (j : ℝ) / 10) (j + 1)) (A j)) :=
  GridDuhamelN_Ugen_duhamel_telescope (by norm_num) (by norm_num) GridDuhamelN_instSigma
    (fun j : ℕ => (j : ℝ) / 10) 3
    (fun j _ => by positivity)
    (fun j hj => by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
      change (j : ℝ) / 10 < 1
      linarith) A

/-- **`stoppedDuhamelN` at `sz0`**: `τ ≡ 3`, `j = 4` (so `min j τ = 3 ≤ K = 4`), `σ = (+,+,-)`,
for every sample `ω`. -/
$ sed -n 705,713p RBM3D/Induction/GridDuhamelN.lean   (proof term of the stoppedDuhamelN instance at sz0, n=0, tau=3, j=4)
              martIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
                GridDuhamelN_instK 0 i GridDuhamelN_instSigma ω) :=
  stoppedDuhamelN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
    GridDuhamelN_instK GridDuhamelN_inst_E GridDuhamelN_inst_s0 GridDuhamelN_inst_st
    GridDuhamelN_inst_t1 GridDuhamelN_inst_K 0 3 GridDuhamelN_instSigma (fun _ => 3) 4 ω
    (by norm_num [GridDuhamelN_instK])

/-- The reduction at `n = 2`: the merged `StoppedDuhamel105` at `sz0`, `E = 0`, from the
general-`n` pin. -/
```

Narrative (stage 1b, `prover` = claude-sonnet-5-5):
* Files: `RBM3D/Path/DuhamelTail.lean` (951 lines), `RBM3D/Induction/GridDuhamelN.lean` (778 lines); `RBM3D/Test/Axioms.lean` untouched (the registry pre-check above is `#assert_rbm_axioms` on `import RBM3D` plus both new modules, exit 0: `StoppedAzuma108`, `StoppedDuhamelN`, `StoppedAzumaN` are `Prop` pins that the new theorems prove, not hypotheses of any theorem). Root imports for the hub at merge: `RBM3D.Path.DuhamelTail`, `RBM3D.Induction.GridDuhamelN`.
* Ports (RBM2D at `c9a24cf`): `Path/DuhamelTail.lean:52-702` (generic part, text-level with `Uop L ξ -> Uop d L g ξ`, `Z2 L -> Zd d L`, `uopBack d g L`) and `:704-865` (pin); `Induction/GridDuhamelN.lean:62-217` (algebra, `stoppedDuhamelN`) and `:219-387` (measurability, Azuma step, `stoppedAzumaN`); the vocabulary `AvecN`, `martIncN`, `predIncN`, `StoppedDuhamelN`, `StoppedAzumaN` from `Induction/HierVocab.lean:387-474` (T2049 skipped it, preflight F1).
* The only exponent that changes: the label count in `stopped_duhamel_cheb_tail`, `L ^ 4 -> L ^ (2 * d)` (`DuhamelTail_card_label`, `card_Zd`). `W`, `N`, `W^2` do not occur in either file (preflight (i) row 2).
* Residual statement differences (script diff above): `[NeZero k]` dropped from the `Ugen` family (`UN` uses `finRotate`, no `σ (i+1)`); `Ugen d L g E σ v w := UN d L g (fun i => mSigma E (σ i)) v w`, so the semigroup law comes from `ukerMat_mul` per slot (`uKer = ukerMat` by `rfl`). `StoppedAzuma108` is token-identical to RBM2D's after renaming; its kernel is the merged `Uop d (sz.L n) (sz.lam n) |m(E)|^2`, as `StoppedDuhamel105`.
* Measurability along the walk: `walk_measurable_loopFine` composed with `pathH_measurable_filt` replaces RBM2D `GoodEvent_measurable_gloop` and the Hermitian-test-function helpers (not ported, no `HermTestFun`).
* Reduction at `n = 2` (D161, D162, D190), compiled: `Ugen_two_eq_Uop` (`Ugen ... ![true,false] = Uop` at `xi = |m|^2` via `finTwoArrowEquiv`), `AvecN_two`, `martIncN_two` (`rfl`), `predIncN_two`, `stoppedDuhamel105_of_stoppedDuhamelN` (general-`n` pin gives the merged `StoppedDuhamel105`; example at `sz0`); `GridDuhamelN_Ugen_duhamel_telescope` at `k = 2` is `Uop_duhamel_telescope` through `Ugen_two_eq_Uop`.
* DECISIONS §29 checks: (1) `0 <= s`, `t < 1`, `K != 0`, `|E| < 2` enter only through `u_j in [0,1)` and `|m| = 1` in `stoppedDuhamelN_at` (hypotheses at the single index `n`); (2) case (ii) boundary not applicable (no `ilambda`, no `L`-`W` relation); (3) `L^d <= W^K` not used; (4) pins keep RBM2D's `forall n` form, and each has an `_at` form (`stoppedDuhamelN_at`, `stoppedAzuma108_at`, `stoppedAzumaN_at`); the two Azuma `_at` theorems have no window hypothesis at all (`Uop`/`Ugen` are total in the real times; measurability of `martInc` uses none). Boundary example `k = 0` (empty sum, bound `4`) compiled in `DuhamelTail.lean` (third example).
* Instances (all compiled, none with `N = 0`, empty index set or `False` premise): `Ugen` algebra and telescope at `d = 3`, `L = 3`, `g = 1/2`, `sigma = (+,+,-)` non-constant (`GridDuhamelN_instSigma_nonconst`); pins at the merged `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`), `n = 0`, `s = 1/10`, `t = 1/2`, `K = 4`, `tau = 3`. The conditional sub-Gaussian input of `stoppedAzuma108`/`stoppedAzumaN` stays a hypothesis of the nondegenerate examples (no conditional Hoeffding lemma in Mathlib, see (c)); the companion examples at `tau = 0`, `c = 0` discharge it by `HasCondSubgaussianMGF.fun_zero` (stopped sum empty there). `stopped_duhamel_det_bound` has an example with every hypothesis discharged at a nonzero remainder `R j = U_{t,u_{j+1}} 1` (via `uopBack` and `Uop_comp`, `Uop_self`). Not instantiated: `stopped_duhamel_azuma_union`, `stopped_duhamel_cheb_tail` (ports not consumed by P.1; their hypotheses need a conditional-mean-zero family on a probability space).
* Imports: `DuhamelTail.lean`: `Path.{Expansion,Azuma,Kernel,Stop,UBounds,StepDecompLoop}`; `GridDuhamelN.lean`: `Path.{Expansion,Azuma,Kernel,Stop}`, `Kernel.Evolution`. `Path.UBounds` (for `uopBack`) is the one module outside the ticket's import list (preflight F2).
* Drops: no public declaration. Not ported: RBM2D private helpers made unnecessary by the merged layer (`DuhamelTail_herm*`, `DuhamelTail_gridStep/Time*`, `DuhamelTail_measurable_phi`: the window arithmetic is not needed there, see §29 (1)) and RBM2D's own `*_check_*` lemmas, replaced by the examples above. Kept although P.1 lists only 6 names: `stoppedAzumaN` (weighted tail of `STGridRepN`, portmap row `STGridRepN`).

## (c) Mathlib names used, verified by the compiled build above (one line each)
* `HasCondSubgaussianMGF`, `HasCondSubgaussianMGF.fun_zero` (`Mathlib/Probability/Moments/SubGaussian.lean:574`): present. A grep `theorem.*HasCondSubgaussianMGF` over `Mathlib/Probability` lists only `mgf_le, cgf_le, ae_trim_condExp_le, ae_condExp_le, fun_zero, zero, memLp_exp_mul, integrable_exp_mul` (no lemma producing it from boundedness, so no conditional Hoeffding there).
* `martingale_of_condExp_sub_eq_zero_nat`, `mul_meas_ge_le_integral_of_nonneg`, `measureReal_iUnion_fintype_le`, `measureReal_biUnion_finset_le`, `measureReal_mono`, `stronglyMeasurable_condExp`, `Finset.stronglyMeasurable_fun_sum`, `measurable_pi_iff`, `continuous_finsetSum`: used in the ported proofs, compile.
* `finTwoArrowEquiv`, `Fintype.sum_equiv`, `Fin.prod_univ_two`, `Fintype.prod_sum`, `Fintype.prod_boole`, `Complex.mul_conj`: used in `Ugen_two_eq_Uop` and the algebra, compile.
* Names verified absent from RBM3D: `Ugen`, `AvecN`, `martIncN`, `predIncN`, `StoppedDuhamelN`, `StoppedAzumaN` (preflight grep), and no clash for the 30 new public names (grep above).

## (d) Open issues and paper-delta candidates
* The sub-Gaussian input of `StoppedAzuma108`/`StoppedAzumaN` (conditional Hoeffding for the stopped martingale differences of the walk) is the pin's hypothesis, not derived; the nondegenerate instances keep it as a hypothesis. The Gaussian check of the preflight (a) (ii) is numerical evidence only, not a Lean statement.
* `stopped_duhamel_det_bound` is a conditional adapter (`hFwd` is a hypothesis, as in RBM2D); `stopped_duhamel_cheb_tail` and `stopped_duhamel_azuma_union` carry no instance (ports, not consumed).
* T2104a: `Ugen` and the `*N` vocabulary drop `[NeZero k]` (finRotate form); `Ugen` is the merged `UN` at `m i = m(sigma_i)`.
* T2104b: `StoppedDuhamelN`, `StoppedAzumaN` keep the energy as a sequence `E : N -> R` (RBM2D); the merged `StoppedDuhamel105`/`StoppedAzuma108` take a scalar `E`; the bridge is `stoppedDuhamel105_of_stoppedDuhamelN` and `AvecN_two`, `martIncN_two`, `predIncN_two`.
* T2104c: the `_at` forms `stoppedAzuma108_at`, `stoppedAzumaN_at` hold without any window hypothesis (stronger than the pins); `stoppedDuhamelN_at` needs `|E n| < 2`, `0 <= s n <= t n < 1`, `K n != 0` only at the index `n`.
* T2104d: label count `L^(2d)` in `stopped_duhamel_cheb_tail` (RBM2D `L^4`); Lean-only intermediate, no paper statement. The Azuma constants `4`, `4 sum c` replace BDG as signed in D10 (cited, not re-proposed).
