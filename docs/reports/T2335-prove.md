Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 13:08:22 UTC 2026

Target `kBA_le` (check section 2): for `2 ≤ d`, `Λ, κ > 0` there are `C, c > 0` with, for all `L ≥ 3`, `0 < g ≤ Λ`, `BAReal d L g κ E m`,
`0 < τ ≤ L²`, `a`: `kBA τ a ≤ C min(1, τ^{-d/2}) exp(-c min(|a|²/τ, |a|))`, `|a| = zdistD d L a` (torus ℓ¹). Route: ticket (1)-(4).

### (i) Exponent table
Notation: `r = |a|`, `s = τ/g²`, `K = BAK d L g E m`, `c₁ := BAct_rate d Λ κ = min(log(1+κ/(4dΛ)), κ/2)` (`CombesThomas.lean:45`),
`A := BAp5s_A d Λ κ = 4(BAct_C/c₁)²`, `BAct_C = 16d²/κ³` (`:42`), `S := BAp5s_S = expC (d-2) c₁` (`Prop5Short.lean:49,52`).

| # | quantity | value / definition | constraint | slack |
|---|---|---|---|---|
| 1 | centered lift `K̃(0,y)`, `y ∈ (-L/2, L/2]^d` | `K(0, y mod L)`; a tie coordinate `y_j = ±L/2` (L even) is split `1/2`-`1/2`, so a point with `k` tie coords has `2^k` lifts of weight `K/2^k` | symmetric `K̃(0,y) = K̃(0,-y)` from `BAK_zero_neg` (`K(0,-a)=K(0,a)`) and the tie swap; `Σ_y K̃ = Σ_a K = 1` (`BAK_row_sum`) | exact |
| 2 | lifted coordinate vs torus distance | `\|ỹ_j\| = zdist L (a_j)`, `Σ_j \|ỹ_j\| = zdistD(a)` for `a = y mod L` | torus position `X` of the projected walk: `zdistD(X) ≤ \|Σỹ_i\|₁` (triangle inequality per coordinate, `zdist L (x+y) ≤ zdist L x + zdist L y`) | exact |
| 3 | `c₁` | `min(log(1+κ/(4dΛ)), κ/2)` | `> 0`, uniform in `L, g ≤ Λ` | at instance: 0.004661 (script below) |
| 4 | `c₀ := c₁/2`, `ε := c₁/2` | tilt range `\|λ\| ≤ c₀`; auxiliary exponent `ε` | `μ := \|λ\| + ε ≤ c₁` as `BAK_exp_moment_le` (`KKernel.lean:228`) requires `0 ≤ μ ≤ c₁` | `μ ≤ c₁` with equality at `\|λ\| = c₀` (no slack needed) |
| 5 | Chernoff constant `C_ch` | `Σ_a K_{0a}(cosh(λ ã_j) - 1) ≤ C_ch g² λ²`, `C_ch = ε⁻² A S = 4AS/c₁²` | `\|λ\| ≤ c₀`, `L ≥ 3`, `0 < g ≤ Λ`, `2 ≤ d`, `BAReal`; depends on `(d, Λ, κ)` only | derivation below; observed ratio `Σ/(g²λ²)` = 0.04 to 0.30 vs `C_ch = 2.9e29` (instance) |
| 6 | single-coordinate tail | `P_s(\|S_j\| ≥ ρ) ≤ 2 exp(-λρ + C_ch g² λ² s)`, `\|λ\| ≤ c₀` | uses `E e^{λS_j} = exp(s Σ_a K(cosh(λã_j) - 1))` (Poisson `N`, symmetric increments) | exact identity |
| 7 | torus tail | `P_s(0, {zdistD ≥ ρ}) ≤ 2d exp(-c_T min(ρ²/(g²s), ρ))`, `c_T = min(1/(4d²C_ch), c₀/(2d))` | `{zdistD(X) ≥ ρ} ⊂ ∪_j {\|S_j\| ≥ ρ/d}`; `λ := min(ρ/(2dC_ch τ), c₀)` (`τ = g²s`): if `λ = ρ/(2dC_chτ) ≤ c₀` exponent `= -ρ²/(4d²C_ch τ)`; else `C_ch τ λ < ρ/(2d)` so exponent `≤ -c₀ρ/(2d)` | `c_T` positive, depends on `(d,Λ,κ)`; at instance 9.4e-32 (route constant, see (ii)) |
| 8 | on-diagonal `C_D` | `kBA_diag_le` (`KHeat.lean:1221`, `0 < d`): `kBA τ a ≤ C_D (min(1,τ^{-d/2}) + L^{-d})` | any `τ > 0`, `L ≥ 3` | applied at `τ/2` |
| 9 | floor absorbed | `L^{-d} ≤ min(1, τ^{-d/2})` for `τ ≤ L²`; `min(1,(τ/2)^{-d/2}) ≤ 2^{d/2} min(1,τ^{-d/2})` | `τ ≤ L²` (this is the regime (i) hypothesis) | script below checks both; first inequality is equality at `τ = L²` (slack 0, so `τ ≤ L²` cannot be weakened) |
| 10 | combination | `P_s(0,a) = Σ_b P_{s/2}(0,b) P_{s/2}(0,a-b)` (`BAP_semigroup_shift`, `BAP_shift`); `zdistD a ≤ zdistD b + zdistD(a-b)` so `zdistD b ≥ r/2` or `zdistD(a-b) ≥ r/2` | each part `≤ sup P_{s/2} · tail_{s/2}(r/2)`, row sum `Σ P = 1` | exact |
| 11 | final constants | `C = 2·C_D(2^{d/2}+1)·2d`; `c = c_T/2` | tail at `(s/2, r/2)`: `min((r/2)²/(τ/2), r/2) = min(r²/(2τ), r/2) ≥ min(r²/τ, r)/2` | factor 2 loss in `c`, in the constraint direction (`c` smaller is allowed) |
| 12 | hypotheses used by the three inputs | `BAK_exp_moment_le`: `3 ≤ L`, `2 ≤ d`, `0 < g ≤ Λ`, `0 < κ`, `BAReal`; `kBA_diag_le`: `0 < d`, same others | target has `2 ≤ d`, `3 ≤ L`, `g ≤ Λ`, `BAReal` | all supplied, none extra |

Two points that differ from the ticket's wording (ticket step (2): "from `BAK_exp_moment_le`, the diagonal term cancels"):
- `BAK_exp_moment_le` bounds `Σ_b K_{0b} e^{μ|b|} ≤ ‖m‖² + A g² S`, with `‖m‖²` on the right. The diagonal of the left side is `K_00 = ‖m‖²` (`BAK_diag`, `KKernel.lean:120`), so `Σ_{b≠0} K_{0b} e^{μ|b|} ≤ A g² S` by subtraction. The `‖m‖²` does cancel, via `BAK_diag`; no use of `‖m‖ ≤ 1` is needed.
- A linear bound `Σ K(e^{μ|b|}-1)` only gives `O(g²λ)`, not `O(g²λ²)`. The quadratic bound uses `cosh y - 1 ≤ (y²/2) e^{|y|}`, `\|ã_j\| ≤ r`, and `r² ≤ (2/ε²) e^{εr}`:
  `Σ_a K(cosh(λã_j) - 1) ≤ (λ²/2) Σ_{b≠0} K_{0b} r² e^{\|λ\| r} ≤ (λ²/ε²) Σ_{b≠0} K_{0b} e^{(\|λ\|+ε) r} ≤ ε⁻² A S g² λ²`.
  So `μ = \|λ\| + ε` with `ε = c₀` is why `c₀ = c₁/2` and not `c₁`.
Paper-delta candidate (O4): `A:58-67` walk on `Z^d`, `p(0,a) = M^{(+,-)}_{0a}`, is the centered lift of the torus kernel `K = |M_L|²` (depends on `L`, `m`; not the projection of a fixed `Z^d` kernel). Also: the paper's `A:62` local CLT is replaced by `kBA_diag_le` (Fourier/gap route, P4a).

### (ii) Concrete nondegenerate instance
Data: `d = 3`, `L = 4` (64 sites), `(g₀, E, m₀)` = flow point of `(L, g) = (4, 10)` from `MFixedPoint.lean:846-893`: `w = 6i/5`, `m_S = L⁻³ Σ_k (gψ_k - w)⁻¹` (`ψ_k = 2Σ_j cos θ_j`, spectrum of `PsiB`, nearest-neighbour adjacency),
`z_S = w - m_S`, `t₀ = Im m_S/(Im m_S + Im z_S)`, `E = (t₀ Re z_S - (1-t₀) Re m_S)/√t₀`, `m₀ = m_S/√t₀`, `g₀ = √t₀ g`, `κ := Im m₀`, `Λ := 10`; `K_{0a} = |M_{0a}|²`, `M = L⁻³ Σ_k e^{iθ·a}/(g₀ψ_k - E - m₀)`. Also `L ∈ {6, 8}` with the same recipe.
`kBA` evaluated by the Fourier form `kBA_fourier` (`KHeat.lean:355`), `K̂_k = Σ_a K_{0a} cos(2π k·a/L)`. Hypotheses to check: `2 ≤ d`, `3 ≤ L`, `0 < g₀ ≤ Λ`, `BAReal` (`BASelf` residual, `κ ≤ Im m₀`), `0 < τ ≤ L²`.
Scripts (not Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2335/{run1,run2,run3}.py` (library `inst.py` in the same directory).

`run1.py` (hypotheses, Chernoff sum, `A, S`, exponential moment), selected lines verbatim, L = 4 and L = 8 (L = 6: ratio 0.2139, residual 1.11e-16, all checks True):
```
L=4: E=0.000000 m0=-0.000000+0.560680j g0=4.672337 kappa=Im m0=0.560680  BASelf residual=1.11e-16  Im m0>0:True
   row sum K_0.=1.000000000000  K_00=0.31436254  |m0|^2=0.31436254  K_00<=1:True  K symmetric:True
   lam=0.00233: sum_a K_0a (cosh(lam a_1)-1) = 4.838e-06;  / (g0^2 lam^2) = 0.0408
   BAct_rate c=0.004661, c0=c/2=0.002331, A=1.229e+11, S=1.301e+13, proved-constant C_ch = eps^-2 A S (eps=c/2) = 2.943e+29
   sum_(b!=0) K_0b e^(c|b|) = 6.9966e-01  <=  A g0^2 S = 3.490e+25: True
   instance hyps: 3<=L:True, 0<g0<=Lam:True, kappa<=Im m0:True, tau=1<=L^2=16
   a=(1, 0, 2): zdistD=3, kBA(tau=1,a)=3.700055e-06, kBA(1,0)=9.691821e-01
L=8: E=0.000000 m0=-0.000000+0.374428j g0=3.120230 kappa=Im m0=0.374428  BASelf residual=5.27e-18  Im m0>0:True
   row sum K_0.=1.000000000000  K_00=0.14019602  |m0|^2=0.14019602  K_00<=1:True  K symmetric:True
   lam=0.00156: sum_a K_0a (cosh(lam a_1)-1) = 7.044e-06;  / (g0^2 lam^2) = 0.2982
   BAct_rate c=0.003115, c0=c/2=0.001558, A=3.101e+12, S=6.522e+13, proved-constant C_ch = eps^-2 A S (eps=c/2) = 8.337e+31
   sum_(b!=0) K_0b e^(c|b|) = 8.7789e-01  <=  A g0^2 S = 1.969e+27: True
   instance hyps: 3<=L:True, 0<g0<=Lam:True, kappa<=Im m0:True, tau=1<=L^2=64
```
(`K_00 = ‖m₀‖²` is the diagonal cancelled in the Chernoff sum: `cosh 0 - 1 = 0`; the same ratio `Σ/(g²λ²)` holds at `λ = c₀/2, c₀/10` since the sum is `∝ λ²` for tiny `λ`.)

`run2.py` (target inequality on a `τ`-grid, 61 points in `[1e-3, L²]` including `τ = 1` and `τ = L²`, all `a ∈ Z_L³`; the smallest admissible `c` is `min` over `(τ, a)` with `r > 0`, `kBA > 1e-12` of `ln(C min(1,τ^{-3/2})/kBA)/min(r²/τ, r)`; also the `a = 0` ratio `kBA(0)/(C min(1,τ^{-3/2}))` must be `≤ 1`), verbatim:
```
L=4, g0=4.6723, tau grid: 61 points in [1e-3, L^2=16], |kBA| floor for the c-ratio: 1e-12
   C=16.0: max_tau kBA(0)/(C min(1,tau^-3/2))=2.486 (needs bigger C);  smallest admissible c (r>0, kBA>1e-12) = 0.2622 at (tau,r)=(16,6)
   C=64.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.621 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.6892 at (tau,r)=(5.98,6)
   C=256.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.155 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.9202 at (tau,r)=(5.98,6)
L=6, g0=2.8514, tau grid: 61 points in [1e-3, L^2=36], |kBA| floor for the c-ratio: 1e-12
   C=16.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.765 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.5405 at (tau,r)=(6.08,6)
   C=64.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.191 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.7591 at (tau,r)=(8.68,9)
   C=256.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.048 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.9131 at (tau,r)=(8.68,9)
L=8, g0=3.1202, tau grid: 61 points in [1e-3, L^2=64], |kBA| floor for the c-ratio: 1e-12
   C=16.0: max_tau kBA(0)/(C min(1,tau^-3/2))=1.007 (needs bigger C);  smallest admissible c (r>0, kBA>1e-12) = 0.1683 at (tau,r)=(11.8,12)
   C=64.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.252 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.2838 at (tau,r)=(11.8,12)
   C=256.0: max_tau kBA(0)/(C min(1,tau^-3/2))=0.063 (ok);  smallest admissible c (r>0, kBA>1e-12) = 0.3993 at (tau,r)=(11.8,12)
```
`C = 1, 2, 4, 8` fail on the `a = 0` ratio (max ratios 39.8, 19.9, 9.9, 5.0 at `L = 4`): `C` must be at least about `L^{-d}`-normalised `kBA(0)` at `τ = L²`, `s = L²/g²` small. This is a dependence of `C` on `(Λ, κ)`, allowed by `∃ C c` after `Λ κ`.

`run3.py` (route constants at the L = 4 instance, and the two prefactor inequalities of row 9), verbatim:
```
c=0.00466145 c0=0.00233073 C_ch=2.943e+29 c_T=min(1/(4d^2 C_ch), c0/(2d))=9.438e-32  final c=c_T/2=4.719e-32
L^-d<=min(1,tau^-d/2) on tau<=L^2: True ; min(1,(tau/2)^-d/2) <= 2^(d/2)min(1,tau^-d/2): True
```
The instance data are ordinary (`L = 4`, `g₀ = 4.67`, `κ = 0.56`, `τ = 1 ≤ 16`, `a = (1,0,2)` with `zdistD = 3`, `kBA = 3.7e-6`). The route constants (`c_T ≈ 1e-31`, `C_ch ≈ 3e29`) are small/large only because `BAct_C, A, S` are crude; they are existential in the target (`∃ C c`), the instance does not evaluate them. Observed admissible constants `(C, c) = (64, 0.69)` hold on the grid.
No external hypothesis occurs (the target is deterministic; all inputs `kBA_diag_le`, `BAK_exp_moment_le`, `BAP_semigroup_shift` are merged on `main`), so no limit computation applies.

§29 checks (DECISIONS §29, items 1-4; §29 later items 5-7 not applicable, deterministic, no `PrecPT`/`W`):
1. Time domain: `0 < τ ≤ L²`, `s = τ/g² > 0` (`g > 0`); the semigroup is used at `s/2 > 0`, `kBA_diag_le` at `τ/2 > 0`: fine.
2. Boundary of regime (i): `τ ≤ L²` is used only in row 9 (`L^{-d} ≤ τ^{-d/2}`), equality at `τ = L²`: boundary included, consistent with the pin.
3. `L`-`W` relation: no `W` and no `L ≤ W^K` is used; all constants depend on `(d, Λ, κ)` only (rows 3-8).
4. `∀ L` vs `∀ᶠ`: pin is `∀ L ≥ 3` (needed by `BAK_off_le`, `BAK_exp_moment_le`, `kBA_diag_le`); `2 ≤ d` is stated in the pin and needed by `BAK_exp_moment_le`.

### Verdict per target
- `kBA_le` (and helpers `BAP_tail_le`, centered lift): **PASS**. Hypotheses hold simultaneously at the instance (`d = 3`, `L = 4`, `g₀ = 4.672`, `κ = 0.5607`, `Λ = 10`, `τ = 1`, `a = (1,0,2)`), every exponent in the table closes, and the grid check supports the statement with explicit constants. The one correction to the ticket's wording is the quadratic Chernoff step (`μ = |λ| + ε`, `ε = c₀`; diagonal removed via `BAK_diag`), recorded above.

### (a′) Preflight corrections — Thu Oct  8 13:25:47 UTC 2026
No verdict changes. Two remarks on the route text of (a): (1) rows 1, 2, 6 and the ticket's step (1) describe the centered lift of `K` to `Z^d` and the identity `E e^{λS_j} = exp(s Σ_a K(cosh(λã_j) - 1))`; the Lean proof builds no lift. It uses the torus test function `h(x) = cosh(λ|x_j|_L)` and the inequality `Σ_b P_s(0,b) h(b) ≤ exp(s(ρ_λ - 1))`, `ρ_λ = Σ_c K(0,c) cosh(λ|c_j|_L)` (the lift enters only through `zdist(u ± v) ≤ |ε p ± δ q|`). (2) Rows 5, 7, 11 hold with `C_ch := max 1 (ε⁻² A S)` (positivity); `c_T`, `C`, `c` as in the table.

## (b) Script output
```
$ date -u   (time of this script output)
Thu Oct  8 13:26:26 UTC 2026
$ git log --oneline -3 && wc -l RBM3D/BA/KHeatTail.lean && git status --short
6c88c68 T2335: BA-P4b KHeatTail (kBA_le regime (i), BAP_tail_le, instances)
a260800 T2335: KHeatTail sections 5-6 (BAP_tail_le, kBA_le; instance pending)
35aec4b T2335: KHeatTail sections 1-4 (cosh pairing, Poisson moment, Chernoff constant, coordinate tail; WIP)
     786 RBM3D/BA/KHeatTail.lean
(clean: nothing above after wc)

$ lake build RBM3D.BA.KHeatTail 2>&1 | tail -4
warning: RBM3D/BA/Ward.lean:16:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3742 jobs).

$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2335/axioms.lean   (import RBM3D.BA.KHeatTail; #print axioms ...)
'RBM.BA.kBA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAP_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatTailInst.inst_kBA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatTailInst.inst_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatTailInst.inst_zdistD' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0

$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2335/registry.lean   (import RBM3D; import RBM3D.BA.KHeatTail; #assert_rbm_axioms)
exit 0
axiom audit: 10105 theorems, 3011 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
[...      265 lines of registry output; lines mentioning KHeatTail / kBA_le: 0]

$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2335/checkeq.lean   (check file imports + import RBM3D.BA.KHeatTail + example : RBM.BA.T2335Check.T2335_kBA_le := RBM.BA.kBA_le)
exit 0; error lines: 0
$ diff docs/tickets/checks/T2335-check.lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2335/checkeq.lean   (the only differences are the two added items)
9a10
> import RBM3D.BA.KHeatTail
50a52,53
> example : RBM.BA.T2335Check.T2335_kBA_le := RBM.BA.kBA_le
> 

$ lake build   (full library, worktree)
Build completed successfully (4143 jobs).
lake build  1.59s user 4.34s system 273% cpu 2.167 total
(exit 0; KHeatTail is not yet a root import: the hub adds it at merge; the registry pre-check above covers it)

$ git diff --stat main...t/T2335
 RBM3D/BA/KHeatTail.lean | 786 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 786 insertions(+)

$ grep -rn --include=*.lean -E "kBA_le|KHeatTail|BAP_tail_le|inst_kBA_le|inst_tail_le" RBM3D | grep -v Probe/ | grep -v BA/KHeatTail.lean | wc -l
       0

$ grep -n -E "^(theorem|def|lemma|abbrev|instance|structure) " RBM3D/BA/KHeatTail.lean   (all public declarations)
515:theorem BAP_tail_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ cT : ℝ, 0 < cT ∧
631:theorem kBA_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
758:theorem inst_zdistD : zdistD 3 4 (![1, 0, 2] : Zd 3 4) = 3 := by
762:theorem inst_kBA_le :
775:theorem inst_tail_le :

$ grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/BA/KHeatTail.lean
0

$ grep -n "RBM1D\|RBM2D" RBM3D/BA/KHeatTail.lean   (ports: none)
26:Nothing is ported from `../RBM1D` or `../RBM2D`.

$ grep -n "^/-! ##" RBM3D/BA/KHeatTail.lean   (sections)
44:/-! ## 1. One-dimensional facts on `ℤ_L` -/
143:/-! ## 2. The test function, one step of `K`, the Poisson series -/
294:/-! ## 3. The quadratic Chernoff constant -/
416:/-! ## 4. The Chernoff tail -/
511:/-! ## 5. Target helper: the tail of the torus `ℓ¹` distance -/
587:/-! ## 6. Target: regime (i) `τ ≤ L²` -/
751:/-! ## 7. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P` of `KKernelInst`) -/

--- target statements, extracted by sed
$ sed -n "/^theorem BAP_tail_le/,/:= by$/p" RBM3D/BA/KHeatTail.lean
theorem BAP_tail_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ cT : ℝ, 0 < cT ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → ∀ ρ : ℝ, 0 ≤ ρ →
        ∑ b ∈ Finset.univ.filter (fun b : Zd d L => ρ ≤ (zdistD d L b : ℝ)), kBA d L g E m τ b
          ≤ 2 * d * Real.exp (-cT * min (ρ ^ 2 / τ) ρ) := by
$ sed -n "/^theorem kBA_le/,/:= by$/p" RBM3D/BA/KHeatTail.lean
theorem kBA_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ a : Zd d L,
        kBA d L g E m τ a ≤ C * min 1 (τ ^ (-(d : ℝ) / 2))
          * Real.exp (-c * min ((zdistD d L a : ℝ) ^ 2 / τ) (zdistD d L a : ℝ)) := by

--- statement diff against the check file (target, text between "def T2335_kBA_le : Prop :=" and "example : Prop")
$ diff <(check statement body with theorem header substituted) <(file statement)
check body == file statement body (whitespace-normalised): True

--- the compiled nonempty instance, extracted by sed
$ sed -n "/^namespace KHeatTailInst/,/^end KHeatTailInst/p" RBM3D/BA/KHeatTail.lean
namespace KHeatTailInst

open RBM.BA.MFixedPointInst

/-- `zdistD 3 4 (1, 0, 2) = 3` (the point of the instance is at torus `ℓ¹` distance `3`). -/
theorem inst_zdistD : zdistD 3 4 (![1, 0, 2] : Zd 3 4) = 3 := by
  decide

/-- Target `kBA_le` at `τ = 1 ≤ L² = 16`, `a = (1, 0, 2)`, `Λ = 10`, `κ = Im m₀`. -/
theorem inst_kBA_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2] ≤ C * Real.exp (-c * 3) := by
  obtain ⟨C, c, hC, hc, h⟩ := kBA_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  refine ⟨C, c, hC, hc, ?_⟩
  have h1 := h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) ![1, 0, 2]
  have h2 : min (((3 : ℕ) : ℝ) ^ 2 / 1) ((3 : ℕ) : ℝ) = 3 := by
    rw [min_eq_right (by norm_num)]
    norm_num
  rw [inst_zdistD, h2] at h1
  simpa using h1

/-- Target `BAP_tail_le` at `τ = 1`, `ρ = 2`: the mass at torus distance `≥ 2`. -/
theorem inst_tail_le :
    ∃ cT : ℝ, 0 < cT ∧
      ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => (2 : ℝ) ≤ (zdistD 3 4 b : ℝ)), kBA 3 4 P.g0 P.E P.m0 1 b
        ≤ 2 * ((3 : ℕ) : ℝ) * Real.exp (-cT * min ((2 : ℝ) ^ 2 / 1) 2) := by
  obtain ⟨cT, hcT, h⟩ := BAP_tail_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨cT, hcT, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos 2 (by norm_num)⟩

end KHeatTailInst
```

### Narrative
- Delivered: `kBA_le` (statement equal to the check-file pin, whitespace-normalised: True above) and the public helper `BAP_tail_le` (tail of the torus `ℓ¹` distance, `2d e^{-c_T min(ρ²/τ, ρ)}`). Constants depend on `(d, Λ, κ)` only. No hypothesis added, no pin changed; `git diff --stat` lists only the new file.
- Route differs from the ticket's step (1) (see (a′)): no centered lift of `K`; the Chernoff step runs on the torus with `h(x) = cosh(λ|x_j|_L)`.
  - `KHeatTail_cosh_pair`: `cosh(λ|u+v|) + cosh(λ|u−v|) ≤ 2 cosh(λ|u|) cosh(λ|v|)` on `ℤ_L` (centered-representative signs, `zdist(n) ≤ |n|` for integer casts). With `K(0,−c) = K(0,c)` (`BAK_zero_neg`) it gives `KHeatTail_step`: `Σ_b K(x,b) h(b) ≤ ρ_λ h(x)`.
  - `KHeatTail_pow`, `KHeatTail_P_h`: `Σ_b P_s(0,b) h(b) ≤ exp(s(ρ_λ − 1))` along the Poisson series (summability re-proved locally; `KHeat_summable` in `KHeat.lean` is private).
- `KHeatTail_cosh_sum`: `Σ_c K(0,c)(cosh(λ|c_j|) − 1) ≤ C g² λ²` for `0 ≤ λ ≤ BAct_rate/2`, `C = max 1 (ε⁻² A S)`, `ε = BAct_rate/2`. Uses `BAK_exp_moment_le` at `μ = λ + ε ≤ BAct_rate`; the diagonal term is removed by `BAK_diag` and `cosh 0 − 1 = 0` (as in (a), second point). Quadratic step: `cosh y − 1 ≤ (y²/2) e^y` (`KHeatTail_cosh_sub_one_le`) and `n² ≤ (2/ε²) e^{εn}` (`Real.quadratic_le_exp_of_nonneg`).
- `KHeatTail_coord_tail` (`2 exp(−λR + Cτλ²)`), `KHeatTail_opt` (`λ = min(R/(2Cτ), c₀)`), union over the `d` coordinates with `R = ρ/d`: `BAP_tail_le`, `c_T = min(1/(4d²C), c₀/(2d))` (as (a) row 7).
- `kBA_le`: semigroup at `τ/2` (`BAP_semigroup_shift`), split at `|c| ≥ r/2` or `|a−c| ≥ r/2` (`zdistD_add_le`), sup bound `kBA_diag_le` at `τ/2` with the floor absorbed (`KHeatTail_floor_le`: uses `τ ≤ L²`; `KHeatTail_half_le`), `C = 4d·C_D(2^{d/2}+1)`, `c = c_T/2` (as (a) row 11).
- Instances: `inst_kBA_le` applies `kBA_le` at the flow point `P` (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`), `τ = 1 ≤ 16`, `a = ![1,0,2]` (`zdistD = 3` by `decide`); every hypothesis is discharged by `P.real`, `P.g0_pos`, `P.g0_le`. `inst_tail_le` does the same for `BAP_tail_le` (`τ = 1`, `ρ = 2`). The instances are `∃ C c` statements: they check applicability at nondegenerate data, not numerical size (sizes: (a) run2.py).
- Stop rule: `wc -l` printed 511, 751, 786 at the three commits (stop size 1500 not reached).

## (c) Verified Mathlib names (each by `#check @name`, scratch `names.lean`, no error)
- `Real.cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y|`; `Real.cosh_add`, `Real.cosh_sub`, `Real.cosh_neg`, `Real.cosh_eq`, `Real.cosh_pos`
- `Real.quadratic_le_exp_of_nonneg : 0 ≤ x → 1 + x + x ^ 2 / 2 ≤ exp x`; `Real.add_one_le_exp`, `Real.one_le_exp`
- `Real.rpow_le_rpow_of_nonpos : 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z`; `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.div_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_pos_of_pos`
- `Summable.tsum_le_tsum`, `Summable.tsum_finsetSum` (forward: `∑' b, ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' b, f i b`), `tsum_mul_right`, `Real.summable_pow_div_factorial`, `NormedSpace.expSeries_div_hasSum_exp`, `Real.exp_eq_exp_ℝ`
- `ZMod.val_natCast`, `ZMod.val_lt`, `ZMod.natCast_zmod_val`, `Int.natAbs_eq`, `Nat.cast_natAbs`, `Int.cast_abs`
- `Finset.exists_le_of_sum_le`, `Finset.sum_filter`, `Finset.add_sum_erase`, `Finset.single_le_sum`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.sum_comm`, `Equiv.sum_comp`, `Equiv.subLeft`, `mul_min_of_nonneg`, `min_le_min`, `one_le_inv₀`, `inv_le_one_of_one_le₀`
- Verified absent (`#check` error `Unknown constant`): `Real.rpow_le_rpow_of_exponent_nonpos`, `Real.exp_half_le_cosh`, `Real.exp_le_two_mul_cosh`, `Finset.sum_filter_le`, `Real.cosh_le_exp_abs`, `Finset.sum_union_le`, `Finset.sum_biUnion_le`.
- `if_pos`, `if_neg` compile with a deprecation warning in this Mathlib ("Use `ite_eq_left`/`ite_eq_right`"); replaced by `simp only [h, ↓reduceIte]`.

## (d) Open issues and paper-delta candidates
- No open issue for this ticket. Downstream P5 may use the public `BAP_tail_le` (hypotheses: `2 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `BAReal d L g κ E m`).
- `T2335a` (ticket, O4): `A:58-67`, the walk on `Z^d` with `p(0,a) = M^{(+,-)}_{0a}`, is read as the centered lift of the torus kernel `K = |M_L|²` (`K` depends on `L` through `M_L` and `m`, so it is not the projection of a fixed `Z^d` kernel). The Lean proof constructs no lift (torus test function `cosh(λ|x_j|_L)`), see (a′).
- `T2335b`: the paper's local CLT (`A:62`, constants not uniform in `(L, g, E, m)`) is replaced by `kBA_diag_le` (P4a, Fourier/gap route) plus the Chernoff tail and the semigroup splitting of `A:64`.
- `T2335c`: `kBA_le` carries `2 ≤ d` (needed by `BAK_exp_moment_le`), `3 ≤ L`, `0 < g ≤ Λ`, `BAReal d L g κ E m`; its twin `kProd_le` has only `1 ≤ d`. `C, c` depend on `(d, Λ, κ)` only, not on `(L, g, E, m)`.
