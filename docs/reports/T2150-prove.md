Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 18:10:54 UTC 2026

Notation: `x = 1-u`, `r = |a-b|_∞` (`zdistInf`), `ω = W^{-D}`, `𝒯 = tailT`, `𝒯̃^L(r) = max(𝒯(min(r,L)), ω)` (`Defs/Tail.lean:52`), `prof = W^{-d}𝒯̃^L` (`STprof`, `Step2Defs.lean:75`), `Ĵ = STJhatM` at `ℓ = L`, `F_σ(x,y) = (𝓛-𝒦)^{(2)}_{σ,(x,y)}`, `Cs = 2^{d-2}e`, `CT` = constant of `ekPropTInf_holds` (`(TTT2)`), `C₁ = C₅ e^{1/(4c)}` (`prop5Decay_holds`, no unproved input: `Prop5Hold.lean:780-784`). The pin `STNewKLKLAt` (`Step5Pins.lean:245`) has no external hypothesis (the inputs `prop5Decay_holds`, `ekPropTInf_holds` are merged theorems), so no limit computation is owed (TEAM §8 lesson 14).

### (i) Route, exponent table, slack

**Route.** `nkl_bound2` (`NewKLK.lean:840`) writes `W^{-d}·E = Σ_{x,y} F(x,a₁) S_{xy} F(a₀,y)` and splits pairs `(x,y)`: (far `y`) `B_y ≤ K0`, sum `Σ_x A_x ≤ Sig`; (near `y`, far `x`) `A_x ≤ K0`, sum `Σ_y B_y ≤ Sig` (S symmetric, row sums 1); (both near, only if `1 ≤ ℓ`) the `(TTT2)` convolution. "Far" = `¬(1 ≤ ℓ ∧ r ≤ ℓ ∧ ω ≤ 𝒯(r))`. The merged proof bounds `A_x ≤ Ĵ W^{-d}𝒯̃(r_x) ≤ K0 := Ĵ W^{-d} Cs 𝒯̃(|a₀-a₁|)` for far `x` (`nkl_tailW_far`, shift `Cs`), and this is where the linear term `Ĵ W^{-d} 𝒯̃(|a₀-a₁|)` of `(juwo=Lklk)` comes from: `W^d·2K0·Sig = (10Cs/(1-u)) Ĵ·prof`.
**At `ℓ = L`.** `L ≥ 3`, so `1 ≤ ℓ`; `zdist L v = min(v.val, L - v.val) ≤ L/2` (as `2 min ≤ v.val + (L - v.val) = L`), hence `r ≤ L/2 ≤ L`. So `min(r,L) = r`, `𝒯̃^L(r) = max(𝒯(r), ω)` and, for far `r` (`𝒯(r) < ω`), `𝒯̃^L(r) = ω` exactly. No `WLOG 𝒯(L) ≥ ω` is needed: the pointwise near/far split covers both cases (`3_5:612-616` is subsumed). So for far `x`: `A_x ≤ K0' := Ĵ W^{-d} ω` (no shift, no `𝒯̃(|a₀-a₁|)`). Then
`W^d [2 K0' Sig + (Ĵ W^{-d})² Cs (CT/x) 𝒯(|a₀-a₁|)] = 10 Ĵ W^{-d-D}/x + (Cs CT/x) Ĵ² W^{-d}𝒯(|a₀-a₁|)`, with `Sig = 5 W^{-d}/x` (`nkl_ward_LKM`, `NewKLK.lean:759`: Ward `Σ_c|𝓛_{(a,c)}| ≤ 4W^{-d}/x` from `Im G_{xx} ≤ Im m + κ/2 ≤ 2 Im m`, plus `Σ_c|𝒦_{(a,c)}| ≤ W^{-d}/x`) and `𝒯 ≤ 𝒯̃` (`nkl_tailT_le_tailW`). This is the pin `C/x (Ĵ² prof + Ĵ W^{-d} W^{-D})`. The first power of `Ĵ` multiplies only `W^{-d-D}`; the second power multiplies the profile.

| item | value | constraint | slack |
|---|---|---|---|
| `δ₀` | `κ/2` (as `nkl_at`) | `Im G_xx ≤ Im m + δ₀ ≤ 2 Im m`, `Im m ≥ κ/2` | equality at `δ₀ = κ/2` (merged) |
| Ward constant `Sig` | `5 W^{-d}/(1-u)` | `4 + 1` (`𝓛`: `Im G/η ≤ 2Im m/((1-u)Im m)`, 2 sides; `𝒦`: `‖m‖=1`, `Σ_b|Θ| ≤ 1/(1-u)`) | `Σ|F| ≤ Sig` verified numerically: max `Σ|F|(1-u)/5 = 0.37` at hypothesis-satisfying samples |
| `Cs` | `2^{d-2}e = 5.4366` (`d=3`) | `Cs ≥ 1` (`nkl_Cs_ge_one`) | `4.44` |
| floor-term constant | `10` (`2·5`) | pin needs `C ≥ 10 + Cs CT` | merged `C = 2(C₁CsCT+Cs)+10Cs+CsCT` exceeds it by `2(C₁CsCT+Cs)+10(Cs-1) > 0` |
| near-near constant | `Cs·CT` | `≤ C` | same |
| power of `Ĵ` against `ω` | `1` | pin: `Ĵ W^{-d-D}` | exact |
| power of `Ĵ` against profile | `2` | pin: `Ĵ²` | exact |
| exponent of `W` in the floor term | `-d-D`: `W^d · W^{-d}(Ĵ-bound) · W^{-D} · W^{-d}(Sig)` | pin `W^{-d}·W^{-D}` | exact |
| `r` vs `ℓ = L` | `r ≤ L/2` | `r ≤ ℓ` for the "near" test | slack `L/2 ≥ 1.5` |
| `1 ≤ ℓ` | `L ≥ 3` | `1 ≤ ℓ` | `≥ 2` |
| `C, δ₀` dependence | `d, κ, 𝔡` only (`C₅, c, CT`) | pin | — |

Verdict on the route: the sharp form is true as pinned; the candidate false cases (`𝒯_u(L) < W^{-D}`, the Ward constant, the power of `Ĵ`) all close by the pointwise split above. The near-near term uses `A_x ≤ Ĵ W^{-d}𝒯(r_x)` (valid when `𝒯̃ = 𝒯`), then `Σ_{x,y}𝒯 |S| 𝒯 ≤ Cs·(CT/x)·𝒯(|a₀-a₁|)` (`nkl_conv_two`).

### (ii) Concrete instance and numerics (script `scratchpad/T2150/inst.py`, `pre.py`, `pre3.py`; numpy)

Instance for the compiled example: `d=3, L=3, W=1` (`N=27`), `lam=1`, `E=0` (`m = i`), `κ=1`, `δ₀=1/2`, `𝔡=1`, `D=0`, `u=0`, `H=0`, `Sizes.L ≡ 3, W ≡ 1` (`three_le_L`, `W_pos` hold). At `H=0, u=0`: `z = i = m`, `G = i·I = M`, `𝓛^{(2)}_{σ,(a,b)} = G_σ(b,a)G_σ'(a,b)`, `𝒦 = m m' Θ_0 = m m' I`, so `F ≡ 0`, `Ĵ = 0`, both sides `0` (hypotheses nondegenerate; value trivial). The second row of the output has `Ĵ > 0` at `L=3`.
Command: `python3 inst.py`. Output:
```
d=3 L=3 W=1 N=27 lam=1.0 E=0 kappa=1.0 delta0=kappa/2=0.50  |E|<=2-kappa:True  lam<=1/dd with dd=1: True  D=0  3<=L:True
max_a |a-b|_inf = 1  <= L/2 = 1.5
u=0.0 H=zero  hyp ||G-M||max=0.000e+00<=delta0:True | Jhat=0.000e+00  max|ELKLK|=0.000e+00  max RHS/C*(1-u)=0.000e+00  C*=0.000e+00
u=0.0 H=near0 hyp ||G-M||max=2.295e-02<=delta0:True | Jhat=3.492e-02  max|ELKLK|=1.748e-04  max RHS/C*(1-u)=3.614e-02  C*=4.837e-03
u=0.3 H=near0 hyp ||G-M||max=4.243e-01<=delta0:True | Jhat=1.060e+00  max|ELKLK|=2.317e-01  max RHS/C*(1-u)=3.118e+00  C*=7.430e-02
Cs=2^(d-2)e=5.4366 (d=3)
```
(`C*` = max over `σ, a` of `|ℰ|(1-u)/(Ĵ²prof + Ĵ ω W^{-d})`, the constant the pin needs on this sample; required `C ≥ 10 + Cs CT`, so on the last row the slack is `10/C* ≈ 135`.) Here `ℰ = (F S F)(a₀,a₁)` (`W=1`, `S` symmetric).

Ticket item (iii): `d=3`, `W=1`, `L ∈ {5,7}`, `g ∈ {1/2,1}`, `u ∈ {0,.5,.9}`, `E=0`; samples `near0`: `H = 0.05·GUE/√N`; `band`: `H = √u·(real symmetric, variance S^B)` (`H=0` at `u=0`); 3 samples per row. Command `python3 pre.py` (prof/ω = largest `𝒯̃^L/ω`, i.e. printed-form linear `Ĵ·prof` over the floor `Ĵ·ω`; `ward` = max `Σ|F|(1-u)/5`; `wardID` = max `| Σ_c|G_{ac}|² - Im G_{aa}/η |`, the Ward identity behind `Σ_c 𝓛_{(-,+),(a,c)}`). Hypothesis `δ̂ = ‖G-M‖max`: rows with `δ̂ ≤ 0.995 = κ/2` at `κ = 1.99` satisfy it (`u ∈ {0, 0.5}`); the `u = 0.9` rows violate the hypothesis (listed only for the ratio).
```
L g u omega kind | max_delta  Jhat  C*  ward(<=1)  wardID  prof/omega  #near
5 0.5 0.0 1.0 near0 | 0.0147 0.0294 0.0114 0.00641 2.1e-15 1 0
5 0.5 0.5 1.0 near0 | 0.986 2.3 0.211 0.338 6.2e-15 1.35 125
5 0.5 0.5 1.0 band | 0.992 1.9 0.195 0.287 4.0e-15 1.35 125
5 0.5 0.9 1.0 near0 | 7.7 25.5 0.116 1.7 1.3e-13 2.94 125
5 1.0 0.0 1.0 near0 | 0.0146 0.0289 0.00402 0.00623 1.8e-15 1 0
5 1.0 0.5 1.0 near0 | 0.985 2.98 0.0678 0.368 8.4e-15 1 0
5 1.0 0.5 1.0 band | 0.937 2.78 0.0662 0.339 3.1e-15 1 0
5 1.0 0.9 1.0 near0 | 7.62 73.4 0.0143 1.69 1.3e-13 1 0
7 0.5 0.0 1.0 near0 | 0.0119 0.0239 0.00932 0.00524 3.0e-15 1 0
7 0.5 0.5 1.0 near0 | 0.984 2.31 0.21 0.339 1.4e-14 1.34 343
7 0.5 0.5 1.0 band | 0.973 2.2 0.206 0.32 7.5e-15 1.34 343
7 0.5 0.9 1.0 band | 5.41 13.8 0.117 1.2 3.6e-14 2.89 343
7 1.0 0.0 1.0 near0 | 0.00962 0.0192 0.00269 0.00436 3.7e-15 1 0
7 1.0 0.5 1.0 near0 | 0.984 2.97 0.0678 0.368 1.5e-14 1 0
7 1.0 0.5 1.0 band | 0.962 2.6 0.0603 0.321 8.9e-15 1 0
7 1.0 0.9 1.0 near0 | 7.5 71.3 0.0144 1.67 1.7e-13 1 0
```
(16 of the 24 printed rows of `pre.py`; the omitted rows (`u=0` `band`, `H=0`, all zeros; and the remaining `L,g,u,kind` combinations) have `C* ≤ 0.211`, `ward ≤ 1.7` only at `u=0.9`, and the same `prof/ω`.) At `W=1`: `ω = 1`, `#near` counts pairs with `𝒯(r) ≥ 1` (`0` means every pair is far, `𝒯̃ ≡ 1`, and linear-over-floor `= 1`). Over all 24 rows `C* ≤ 0.211`; where the hypothesis holds `ward ≤ 0.37 < 1`.

Floor as a free number (`ω := W^{-D}` free, `W^d = 1`; an analytic extension of the instance, not a Lean instance, since `W=1` forces `ω=1`), `L=7`, covering mixed near/far (`python3 pre3.py`, excerpt):
```
g 1.0 u 0.5 T(r=0..3) [0.6725 0.1463 0.0694 0.0402]
 omega 0.1 near0 | delta 0.984 Jhat 4.43 C* 0.195 prof/omega 6.72  r with T>=omega: [0, 1]
 omega 0.3 near0 | delta 0.984 Jhat 4.42 C* 0.0898 prof/omega 2.24  r with T>=omega: [0]
 omega 0.5 band  | delta 0.941 Jhat 3.72 C* 0.0484 prof/omega 1.34  r with T>=omega: [0]
 omega 0.7 near0 | delta 0.984 Jhat 4.25 C* 0.0513 prof/omega 1  r with T>=omega: []
g 0.5 u 0.5 T(r=0..3) [1.3392 0.2474 0.1095 0.06  ]
 omega 0.1 near0 | delta 0.983 Jhat 2.31 C* 0.334 prof/omega 13.4  r with T>=omega: [0, 1, 2]
 omega 0.5 near0 | delta 0.984 Jhat 2.31 C* 0.239 prof/omega 2.68  r with T>=omega: [0]
```
Over the full `pre2.py`/`pre3.py` runs (`ω ∈ {0.1,…,10⁻⁸}`, 50 rows) `C* ≤ 0.393`. The ratio linear-over-floor (printed-form `Ĵ·prof` vs sharp `Ĵ·ω`) is `prof/ω ≥ 1`, up to `1.3·10⁸`; the pin keeps only `Ĵ·ω`, true with `C* ≤ 0.4` in every sample (no counterexample `H` found; the sharp form is proved above, so none exists).

### Verdict

- Target 1, `stNewKLKL_holds (d : ℕ) : STNewKLKL d`: **PASS** — the sharp form holds with `C = 10 + Cs CT` (or the merged `C` of `nkl_at`), `δ₀ = κ/2`; no hypothesis is unsatisfiable; the instance above (`d=3, L=3, W=1, H=0, u=0`) has all hypotheses true. Proof obligation for 1b: a private copy `newKLKL_bound2` of `nkl_bound2` at `ℓ = L` with the extra fact `zdistInf ≤ L` (so far `r` gives `𝒯̃ = ω`), keeping the near-near term, and the Ward sums `Sig` of `nkl_ward_LKM` unchanged.
- Registry line `STNewKLKL` (`Test/Axioms.lean:175`): to be deleted by 1b after the registry pre-check.

## (b) Script output — Sun Oct  4 18:20:07 UTC 2026

Evidence scripts (`scratchpad/T2150/ev.sh`, `ev2.sh`) print the blocks b.1 and b.4 verbatim.

### b.1 Build, axioms, hygiene
```
$ date -u
Sun Oct  4 18:20:07 UTC 2026
$ git log -1 --format="%h %an <%ae> %s" && git status --short
ef46fb0 Jun Yin <321276894+JYin80@users.noreply.github.com> T2150: S5-12 Induction/NewKLKL (proves STNewKLKL)
$ lake build RBM3D.Induction.NewKLKL 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3775 jobs).
$ lake build RBM3D.Induction.NewKLKL 2>&1 | grep -ci "error\|sorry"
0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/NewKLKL.lean | wc -l
       0
$ lake env lean ax.lean   (import RBM3D.Induction.NewKLKL; #print axioms RBM.Gauss.Sizes.stNewKLKL_holds)
'RBM.Gauss.Sizes.stNewKLKL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ wc -l RBM3D/Induction/NewKLKL.lean
     956 RBM3D/Induction/NewKLKL.lean
$ grep -n "theorem \|private def \|^example" RBM3D/Induction/NewKLKL.lean | grep -v "private theorem"
221:private def newKLKLQ (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) : ℝ :=
836:theorem stNewKLKL_holds (d : ℕ) : STNewKLKL d := by
893:example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
920:private def newKLKLsz31 : Sizes 3 where
930:example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
$ grep -c "private theorem" RBM3D/Induction/NewKLKL.lean
31
```

### b.2 Registry pre-check (DECISIONS §16, §20): line `STNewKLKL` deleted from `owedProps`
Command (run between the `date -u` outputs 18:16:54 and 18:17:32 UTC of the tool log; temp file `scratchpad/T2150/precheck.lean`, not committed):
`import RBM3D` + `import RBM3D.Induction.NewKLKL` + `#assert_rbm_axioms`, run as `lake env lean precheck.lean > precheck.out; echo $?` after `lake build RBM3D.Test.Axioms`.
```
exit: 0
axiom audit: 4639 theorems, 1640 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 ... (149 lines in total; lines containing "NewKLKL": 0)
non-vacuity certificates: 0 of 89 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)

```

### b.3 Full `lake build`
The root `RBM3D.lean` does not import the new module (the hub adds the import at merge, CLAUDE.md §3 (A) step 4), so the plain full build of the worktree stops at the registry audit, as expected after the registry line is gone (`Step5Pins.lean` still assumes `STNewKLKL`, only the new module proves it).  Plain `lake build`, exit 1:
```
error: RBM3D.lean:197:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Gauss.Sizes.STNewKLKL]
Classify each of them: borrowed from the literature, owed by this formalization, or a predicate that defines the objects under study.
Some required targets logged failures:
- RBM3D
error: build failed
```
With the hub's import added temporarily after the last `import` line of `RBM3D.lean` (reverted afterwards, never committed; `git status --short` is empty in b.1), `lake build` exit 0, 18:17:55 UTC:
```
info: RBM3D.lean:198:0: axiom audit: 4639 theorems, 1640 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3916 jobs).
```

### b.4 Target statement, pin, name clashes, diff-stat, registry diff, instances
```
$ sed -n "233,246p" RBM3D/Induction/Step5Pins.lean   # the pin, merged (c8e4f17)
def STNewKLKLAt (d : ℕ) (κ 𝔡 C δ₀ : ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLKM sz n E u H σ a‖ ≤
          C / (1 - u) * (STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H ^ 2 *
              STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
            STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **`lem:newKLK` at `ℓ = L`, the pin** (constants `C, δ₀` depend on `d, κ, 𝔡` only, as `STNewKLK`). -/
def STNewKLKL (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKLAt d κ 𝔡 C δ₀

$ sed -n "832,836p" RBM3D/Induction/NewKLKL.lean   # target 1
  linarith

/-- **`lem:newKLK` at `ℓ = L`, sharp form** (`(i2kk2zgg)` `3_5:628-651` with `ℓ = L`; paper-delta candidate `T2134a`):
the pin `STNewKLKL` holds, with `δ₀ = κ/2` and `C = 10 + 2^{d-2} e C_T` (`newKLKL_at`). -/
theorem stNewKLKL_holds (d : ℕ) : STNewKLKL d := by

$ git grep -n "stNewKLKL_holds\|newKLKL" main -- RBM3D | grep -v "NewKLKL.lean"   # name-clash grep on main
main:RBM3D/Induction/Step5Pins.lean:1013:theorem inst_newKLKL (h : STNewKLKL 3) :
(exit 0: one match, the merged `inst_newKLKL`, see the note after this block)
$ grep -rn "stNewKLKL_holds\|newKLKL" /Users/junyin/Lean_proof/RBM3D/RBM3D /Users/junyin/Lean_proof/RBM3D/RBM3D.lean   # main worktree files
/Users/junyin/Lean_proof/RBM3D/RBM3D/Induction/Step5Pins.lean:1013:theorem inst_newKLKL (h : STNewKLKL 3) :
(exit 0: one match, the merged `inst_newKLKL`, see the note after this block)
$ grep -c "stNewKLKL_holds" RBM3D/Induction/NewKLKL.lean
7
$ git diff --stat main...t/T2150
 RBM3D/Induction/NewKLKL.lean | 956 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |   1 -
 2 files changed, 956 insertions(+), 1 deletion(-)
$ git diff main...t/T2150 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STNewKLKL, -- `lem:newKLK` sharp at `ℓ = L` (paper-delta T2134a); S5-01 (T2138, DECISIONS §40: owed)
$ git grep -n "STNewKLKL" t/T2150 -- RBM3D/Test/Axioms.lean; echo exit
(exit 1: no match)

--- the two compiled instances (statements; proofs in the file) ---
893: example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
894:     ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
895:       ‖STELKLKM sz0 0 0 u
896:           (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
897:         C / (1 - u) * (STJhatM sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) u
898:               (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
899:             STprof sz0 0 u 1 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) +
900:           STJhatM sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) u
901:               (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
902:             (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
930: example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
931:     ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (newKLKLsz31.L 0)),
932:       ‖STELKLKM newKLKLsz31 0 0 u
933:           (0 : Matrix (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0))
934:             (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0)) ℂ) σ a‖ ≤
935:         C / (1 - u) * (STJhatM newKLKLsz31 0 0 1 ((newKLKLsz31.L 0 : ℕ) : ℝ) u
936:               (0 : Matrix (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0))
937:                 (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0)) ℂ) ^ 2 *
938:             STprof newKLKLsz31 0 u 1 ((newKLKLsz31.L 0 : ℕ) : ℝ) (a 0) (a 1) +
939:           STJhatM newKLKLsz31 0 0 1 ((newKLKLsz31.L 0 : ℕ) : ℝ) u
940:               (0 : Matrix (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0))
941:                 (Idx 3 (newKLKLsz31.L 0) (newKLKLsz31.W 0)) ℂ) *
942:             (((newKLKLsz31.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * ((newKLKLsz31.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
```
Ports from RBM1D/RBM2D: none (the helpers are private copies of `Induction/NewKLK.lean`, commit `b06ff9b`, as listed in the module docstring), so no RBM1D/RBM2D diff-stat is owed.
`inst_newKLKL` above is the merged instance of the *pin* in `Step5Pins` (`RBM.Gauss.Step5Inst.inst_newKLKL`), not a clash with a new name: the only new public declaration is `stNewKLKL_holds`; the others are `private` with prefix `newKLKL_` (31 private theorems, `newKLKLQ`, `newKLKLsz31`).

### b.5 Narrative
* **Target.** `stNewKLKL_holds d : STNewKLKL d` is exactly the merged pin (same text, `Step5Pins.lean:245`); `δ₀ = κ/2`, `C = 10 + C_s C_T` with `C_s = 2^(d-2) e`, `C_T` from `ekPropTInf_holds` (`(TTT2)`); both depend on `d` only.  The pin was proved as stated; no hypothesis was added or weakened.
* **Proof.** Private copy of the route of `nkl_bound2` (`NewKLK.lean:840`), with the cut at `ℓ = L` built in (`newKLKL_bound2`).  `newKLKL_zdistInf_le_L` gives `|x|_∞ ≤ L` (`zdist L u = min u.val (L - u.val) ≤ L`), so `1_{ℓ≥1} = 1` (`L ≥ 3`: the both-near term is always present) and for every distance `r` either `W^{-D} ≤ 𝒯(r)` (`𝒯̃^L = 𝒯`, `newKLKL_tailW_eq_of_near`) or `𝒯(r) < W^{-D}` and `𝒯̃^L(r) = W^{-D}` exactly (`newKLKL_tailW_of_far`).  A far factor is therefore bounded by `K0 = Ĵ W^{-d} W^{-D}` with no shift `C_s` and no profile at `|a₁-a₂|`: this replaces the merged `K0 = Ĵ W^{-d} C_s 𝒯̃(|a₁-a₂|)` and removes the term linear in `Ĵ` against the profile.  The marginal sums are the merged Ward bound `5 W^{-d}/(1-u)` (`newKLKL_ward_LKM`, copied unchanged), the both-near term is `(Ĵ W^{-d})² C_s C_T/(1-u) 𝒯(|a₁-a₂|)` (`newKLKL_conv_two`).  Times `W^d`: `10 Ĵ W^{-d} W^{-D}/(1-u) + C_s C_T/(1-u) Ĵ² W^{-d} 𝒯`, then `𝒯 ≤ 𝒯̃^L` and `C = 10 + C_s C_T`.
* **Against section (a).** Every row of the exponent table is used as written (Ward constant 5, floor constant 10, power 1 of `Ĵ` against `W^{-d-D}`, power 2 against the profile, `C ≥ 10 + C_s C_T`).  Two harmless differences: (a) bounds `r ≤ L/2`, the proof uses only `r ≤ L`; (a) says `C₁` appears in the merged `C`, but the pin has no `Θ^{(2)}` term, so `prop5Decay_holds` and the hypothesis `lam ≤ 𝔡⁻¹` are not needed here (the latter stays in the statement, unused).  No `(a′)` section is needed.
* **Instances.** Two compiled `example`s apply `stNewKLKL_holds 3` at `κ = 𝔡 = 1/10`, `E = 0`, `D = 1`, `H = 0`, `u = δ₀/(1+δ₀) ∈ (0,1)` (so `G_u - M = i u/(1-u) I ≠ 0`, `‖G_u - M‖_max = δ₀`, `newKLKL_STGMM_zero`), for all `σ` and all `a`: one at the merged `sz0` (`L = 4`, `W = 32`), one at the private `Sizes 3` with `L = 3`, `W = 1`, `lam = 1` (`κ = 𝔡 = 1`), the data requested by the ticket (`d = 3`, `L = 3`, `W = 1`, `H = 0`).  Every deterministic hypothesis is discharged; no hypothesis of the pin is left open (the pin has none from other gates).
* **Registry.** The owed line for `STNewKLKL` is deleted; the pre-check passes without it.

## (c) Verified Mathlib / project names used in the new code (`#check` in `scratchpad/T2150/names2.lean`: 0 errors)
`Finset.sup_le`, `min_le_right`, `Nat.sub_le`, `Real.rpow_pos_of_pos`, `Finset.le_sup'`, `div_le_iff₀`, `div_lt_one`, `Matrix.isHermitian_zero`, `Finset.sum_comm` (all elaborated; signatures printed by the check).  Project: `RBM.zdist`, `RBM.tailW_pos`, `RBM.ekPropTInf_holds` (elaborated).  Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
* **Hub step.** After adding `import RBM3D.Induction.NewKLKL` to `RBM3D.lean`, the full `lake build` passes (b.3); before that import the root audit fails on `STNewKLKL` (expected, §20 order).
* **T2150a (route note, no statement difference).** The paper's reduction "WLOG `𝒯_u(ℓ) ≥ W^{-D}`, otherwise pass to `K ≤ ℓ` with `𝒯_u(K) = W^{-D}`" (`3_5:612-616`) is replaced, as in the merged T2099, by the pointwise near/far split; at `ℓ = L` the far values are `W^{-D}` exactly.  The statement is the sharp form already recorded as D315 (`T2134a`).
* **T2150b (constants).** Lean carries `C = 10 + 2^(d-2) e C_T`, `δ₀ = κ/2`; the paper's weak-law "w.h.p. with `1+o(1)`" (`3_5:640-646`) is the explicit hypothesis `‖G_u - M‖_max ≤ δ₀` with `Im G_xx ≤ 2 Im m` (same as merged `STNewKLK`).
