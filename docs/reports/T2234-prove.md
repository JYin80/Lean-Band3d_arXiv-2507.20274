Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 00:53:42 UTC 2026

Scripts (Python, mathematics only; no Lean) are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2234/`: `g.py` (graph records as in `LWVocab.lean:302-331`), `t1.py`, `t2.py`, `pre.py`, `inst.py`.
Notation: `k := ordN - nngh`, `D_i := zdistInf(a_i - b_i)`, `RHS := θ^q ψ(0)^k Π_{i: noGhostPath i} ψ(c D_i)` (the right side of `AnpDetGhAtPin`, check file `:96-101`). All `val/RHS` ratios below use `C = 1`.

### (i) Exponent table

| quantity | value | constraint | slack / status |
|---|---|---|---|
| `C` (target 2, `q = 0`) | `1` | `0 < C` | exact: `oneEdge` ratio `1.0000` (equality) |
| `c` (target 2) | `1 / max(1, max_i |path i|)` | `0 < c ≤ 1`; per `i`, a walk `a_i = v_0..v_m = b_i` has an edge with `zdistInf ≥ D_i/m ≥ c D_i` | `m ≥ 1` since `WalkOK` forces `inl(inl i) ≠ inl(inr i)`; `c = 1` iff all paths are one edge |
| `k = ordN - nngh` at `q = 0` | `nSolid - nngh ≥ 0` | `ψ(0)^k` as `ℕ`-power | chosen edges (one per ghost-free path) are solid and pairwise distinct (`IsNested` conjuncts 3, 4), so `nngh ≤ nSolid` |
| `ordN` | `nSolid - 2q` (`ord ⟨nSolid,0,q,0,0,0⟩ = nSolid + 2(0-q)`, `ScalingOrder.lean:65`) | | `figAux`: 2; `oneEdge`: 1; two-step: 3; ghost edge: 0 |
| homogeneity | both sides scale as `λ^{nSolid}` | `2q + k + nngh = 2q + ordN = nSolid` | script (ii)(2): rel. diff `2e-16` |
| `q ≤ p` | from `IsNested` conjunct 6 at `A = univ`: `q ≤ card{j ∣ ∃α, Visits j α} ≤ card (Fin p) = p` | needed only by the merged pins (hypothesis there) | not assumed by `AnpDetGhPin` |
| `τ'` (target 4) | `τ / (2 (q + |k| + p + 1))` | `τ' > 0` | |
| `N`-exponent of the lift | `τ'(q + max(k,0) + nngh)` | `ψ(0)^k = N^{τ'k} Φ^k ≤ N^{τ' max(k,0)} Φ^k` (`N ≥ 1`, `one_le_size`), `nngh ≤ p` | `≤ τ/2`, so slack `τ - exponent ≥ τ/2` |
| `C ≤ N^{slack}` | needs `∀ᶠ n` (`SizeTendsto`) | `slack ≥ τ/2 > 0` | `C = 1` (every `q = 0` graph, hence `oneEdge`): holds for all `n`; `C > 1`: eventually (see lift table below) |
| `θ_n = (W^d η_t)⁻¹ > 0` | `W_pos`, `η_t > 0` | needed to apply the deterministic bound | see (iii)(1): follows from `STFlow` and `t ≤ lemT z` |
| `ψ = N^{τ'} Φ n` | antitone on `[0,∞)`, `> 0` | `LWPsiRel` conjunct 1; `LWClass` conjunct 1 (`∀ᶠ n`) | no other `LWPsiRel`/window conjunct used |
| probability | `P(Ξ_nᶜ) ≤ N^{-D}` for all `D` | `Ξ_n = Ξ¹ ∩ Ξ²` from `Prec.whp` (`StochDomAt.lean:165`) at `τ'` for the two `LWXi` `Prec` conjuncts, `HighProbAt.inter` (`:571`, needs `Tendsto size`) | `badSetAt` already has `∃ u` inside `P` (`:53`): no union bound over `L^{2d}` pairs, no `card_Idx`, no `biInter` needed |

Graph rows (script `pre.py`, `d = 3`, `L = 5`, `ψ = (1+r)^{-1}`, `θ ∈ 10^{-3..3}`, six `ξ` families: saturated, random, 0/1 mask, near-only, flat cap, concentrated; random `(a,b)`; `ξ` symmetric, `0 ≤ ξ ≤ ψ(dist)`, row sums `≤ θ` asserted):
```
$ python3 pre.py
figAux                 p,q=2,2 nSolid=6 ordN=2 nngh=2 ordN-nngh=0 maxlen=3 c=0.25 max val/RHS=0.1749
oneEdge                p,q=1,0 nSolid=1 ordN=1 nngh=1 ordN-nngh=0 maxlen=1 c=1.0 max val/RHS=1.0000
twoStep(a0-b1-b0)      p,q=2,0 nSolid=3 ordN=3 nngh=2 ordN-nngh=1 maxlen=2 c=0.5 max val/RHS=0.2256
oneGhost               p,q=1,0 nSolid=0 ordN=0 nngh=0 ordN-nngh=0 maxlen=1 c=1.0 max val/RHS=1.0000
figAux.ghostify(e0)    p,q=2,2 nSolid=5 ordN=1 nngh=1 ordN-nngh=0 maxlen=3 c=0.25 max val/RHS=0.3970
```
Chosen long edges in the base-case rows: `oneEdge`: the edge `a_0 b_0`; two-step (`es = [(a_0,b_1),(b_1,b_0),(a_1,b_1)]`, paths `[e0,e1]`, `[e2]`): path 0 picks `e0` or `e1` (the longer; `c = 1/2`), path 1 picks `e2`; the unchosen solid edge gets `ψ(0)^1`, matching `k = 1`.
Random nested graphs (checked `IsNested` conjuncts 1-6 and `GhostOK` by brute force; `d = 1`, `L = 31` (`L = 15` for `q = 2`), `ψ ∈ {(1+r)^{-1}, e^{-r/2}}`):
```
$ python3 t2.py
tries 2423 nested ghost-ok graphs (any q): 300 with a ghost edge: 225 q=2: 2 p=3: 96
d=1 max over graphs/xi/theta/psi/(a,b) of val/RHS with C=1: {'c=1/(2L)': 1.0, 'c=1/(4L)': 1.0}
```
(`L` = longest path length; of the 300, 256 have `q = 0`, so 44 have `q ≥ 1`. For the 256 `q = 0` graphs alone, `c = 1/maxlen`, `C = 1`: max ratio `1.0` — the base-case claim; for `q ≥ 1` this is evidence, not a proof.) Also at `figAux`, `d = 3, L = 5`, `c = 1/4`: max `0.18`; `d = 1, L = 31`, `c = 1/4`: `0.2715`, `c = 1/2`: `0.8695` (both `≤ 1 = C`).

Lift arithmetic at `sz0` (`Defs/Sizes.lean:260`, `size n = ((2(n+1))^5 · 4(n+1))^3`, `size 0 = 2097152`), `τ = 1/10`:
```
$ python3 inst.py   (last block)
 oneEdge  q=0 k=0 p=1 tau'=1/40 N-exp=1/40 slack=3/40  N(0)^slack=2.9794 N(10)^slack=75.858 N(100)^slack=1513.408  eventual threshold for C=30: N>= 4.954e+19
 twoStep  q=0 k=1 p=2 tau'=1/80 N-exp=3/80 slack=1/16  N(0)^slack=2.4837 N(10)^slack=36.870 N(100)^slack=446.646  eventual threshold for C=30: N>= 4.305e+23
 figAux   q=2 k=0 p=2 tau'=1/100 N-exp=1/25 slack=3/50  N(0)^slack=2.3950 N(10)^slack=31.916 N(100)^slack=349.917  eventual threshold for C=30: N>= 4.156e+24
 Phi0=W^-1, W(0)=32: W^-3/2=0.00552 <= Phi0=0.03125 <= W^-1/20=0.84090
```
`N^{slack} → ∞` since `size n → ∞` (`SizeTendsto`, from `Admissible` in `STFlow`); for every `q = 0` graph `C = 1`, so no threshold. The thresholds for `C = 30` are the usual eventual quantifier of `≺` (the lift fixes no `n`, the compiled instance is a `Prop`-level application with no chosen `N`).

### (ii) Concrete nondegenerate instance

```
$ python3 inst.py   (first two blocks)
== instance 1 (target 2): d=3, L=3, oneEdge, psi=(1+r)^-1, theta=1, xi=psi(dist)/3, a=(0,0,0), b=(1,1,1)
 xi symmetric: True  0<=xi<=psi(dist): True  max row sum xi^2: 0.833333 <= theta=1: True
 |a-b|= 1  val= 0.16666666666666666  RHS(C=1,c=1)= 0.5  val<=RHS: True
== instance 2 (figAux, q=2): d=3, L=5, psi=(1+r)^-1, theta=20, xi=psi(dist), a_i=(0,0,0), b_i=(2,2,2), c=1/4
 max row sum xi^2 = 18.3889 <= 20: True  GhostOK True  IsNested True
 |a-b|= 2  val= 49.231674  RHS(C=1)= 177.777778  val<=RHS: True
```
Hypotheses at these numbers: `3 ≤ d`, `L ≥ 3` (`NeZero`), `ψ` positive antitone on `[0,∞)`, `θ > 0`, `ξ` symmetric `≥ 0`, `ξ ≤ ψ(zdistInf)`, `Σ_β ξ² ≤ θ`, `Γ.GhostOK`, `Γ.IsNested`, `0 < C`, `0 < c ≤ 1`: all hold, `p = 1, q = 0` and `p = q = 2` (no empty index, `a ≠ b`). Target 3's hypotheses `AnpDetGhZero d`, `AnpDetGhStep d` are pins (no closed-form witness; the step is LW-12b-f).
(ii)(2) homogeneity on `figAux` (`C = 1`, `c = 1/4`, `θ = 20`, random `ξ`):
```
 lam 3.0 ratio 0.008402126459162308 ratio at lam=1 0.00840212645916231 rel.diff 2.0646243357657801e-16
 lam 0.1 ratio 0.008402126459162306 ratio at lam=1 0.00840212645916231 rel.diff 4.1292486715315603e-16
 nSolid==2q+ordN for all graphs above (exponent of lam on both sides): True
```
(ii)(3) A2 replacement (`c′`): `figAux` with edge 0 `(a_0, m_0)` made ghost:
```
 GhostOK True IsNested True nSolid 6 -> 5 nngh 2 -> 1 ordN 2 -> 1 ordN-nngh 0 -> 0
```
(`IsNested` conjuncts 1-6 mention only `u, v, path`, never `ghost`; hence preserved by `ghostify` in general; `nSolid`, `nngh`, `ordN` each drop by 1 when the edge lies on a ghost-free path and was solid; the bound for `Γ` follows from that for `Γ.ghostify e` and `ξ_e ≤ ψ(...)`, `ξ ≥ 0`.)

### (iii) Inspection
1. **`η_t > 0`.** The lift needs `0 < etaT (STflowE z n) (t n)` for `θ_n > 0`. `STFlow` gives `locDomain κ ε n (z n)` (`Defs/Sizes.lean:186-187`: `size^{-1+ε} ≤ (z n).im`, `size ≥ 1` by `one_le_size`), so `0 < (z n).im =: hz`. Then `lemT_lt_one hz : lemT z < 1` (`Defs/Semicircle.lean:209`) with `t n ≤ lemT (z n)` gives `t n < 1`; `abs_lemE_lt_two hz : |lemE z| < 2` (`:229`), and `STflowE z n = lemE (z n)` (`Induction/Defs.lean:283`) by definition; `etaT_pos (hE : |E| < 2) (ht : t < 1)` (`Loop/GLoop.lean:83`) closes it. The hypothesis `0 ≤ t` is not used.
2. **`(eq:Psi)`.** Not needed by 12a: target 4 uses `LWPsiRel` conjunct 1 (antitone) and `LWClass` conjunct 1 (positivity, `∀ᶠ n`) only; no `ε₀`, `C₁..C₃`, window. `grep -n "eq:Psi" paper/tex/*.tex`: hits at `7_8:87, 883, 2045, 2074`, `3_5:391`, none in `7_8:1103-1599`. The proof text of cases (I)-(IV) uses monotonicity of `Ψ_t` only: `(eq:change_of_order2)` (`7_8:1172`, `Π Ψ_t(c|α_q-b_i|)^{χ} ≤ Π Ψ_t(c|a_i-b_i|/2)^{χ}` "by the definitions of A1 and B1") and `7_8:1238` (`Π Ψ(c|a_{j,r}-b_{j,r}|) ≤ Ψ(c|a_j-b_j|/2) Ψ(0)^{Σχ-χ}`). So no `LWPsiRel`-type hypothesis is added to a primed successor; `c` shrinks by factors of `1/2` along the induction, which is why `AnpDetGhAt` takes `c` after the graph and why the pin's `c ≤ 1` is harmless. The base case and its `c` are not affected.
3. **`q ≤ p`.** Follows from `IsNested` conjunct 6 at `A = univ` (row `q ≤ p` of the table); the pins' `q ≤ p` hypothesis is therefore redundant for the lift (carried, unused).
4. **Targets 1-3 and 5** involve no `t`, `η`, `Sizes`; target 5's reductions are exact: `NoGhost → GhostOK` (no edge is ghost, so each path's ghost filter is empty), `noGhostPath i = true` for all `i` so `nngh = p`; `lwAnp_of_key` is the instance at `(fun _ => a, fun _ => b)`, `Π_{i ∈ Fin p}` of a constant `= (·)^p` and `ordN - p`.

### (iv) §29 checklist
(1) time: `0 ≤ t`, `t ≤ lemT z` carried, only `η_t > 0` is used (iii)(1). (2) no `1 - ilambda²/L²` boundary appears. (3) no `L^d ≤ W^K`; no cardinality bound at all (`Prec` is already uniform in `u`). (4) `∀ᶠ n` only for `Φ n > 0`, `C ≤ N^{slack}`, `Tendsto size` (all inside one `∀ᶠ`, fine for `Prec`). (5) uniform in `(a,b)`: `Prec` over `U n = (Fin p → Zd)²`, the `∃ u` inside `P`. (6) no parameter lower bound used. (7) scale `N = sz.size n`, `Φ n (c |a-b|)` with the `c` of the deterministic lemma, as in the pin.

### Verdicts
- Target 1 (vocabulary, `AnpDetGhAt/AnpDetGh/AnpDetGhZero/AnpDetGhStep`): **PASS** (hypotheses satisfiable, instances above; `C, c` before `L, ψ, θ, ξ`; `c ≤ 1` holds at the base case).
- Target 2 (`anpDetGh_zero`, plus `ghostify` lemma (c′)): **PASS** (`C = 1`, `c = 1/max(1, max|path i|)`, `k = nSolid - nngh ≥ 0`; numerics ratio `≤ 1`).
- Target 3 (`anpDetGh_of_step`): **PASS** (strong induction on `q`, all `p`; base case from target 2).
- Target 4 (`lwAnpKeyGh_of_det`): **PASS**, with two corrections to the ticket's route: (a) the union bound over pairs is unnecessary, use `Prec.whp` + `HighProbAt.inter` + `badSetAt`'s inner `∃ u`; (b) take `τ' = τ/(2(q+|k|+p+1))` (slack `≥ τ/2`) instead of `τ/(q+|k|+p+1)`; `etaT_pos` is fed as in (iii)(1).
- Target 5 (`lwAnpKey_of_gh`, `lwAnp_of_key`): **PASS**.
Overall: **PASS**. Not verified here: that `AnpDetGhStep` (cases I-IV) holds in deterministic form; numerics at `q ≥ 1` are evidence only, and the paper's text for cases (I)-(IV) uses only monotonicity of `Ψ_t`, `Σ_β ξ² ≤ θ`, `ξ ≤ ψ` (see (iii)(2)).
Paper-delta candidates seen in this preflight: `T2234a` (`lem:Anp_key_gh` proved deterministically on one event, `7_8:1041-1077`); `T2234b` (`q = 0` needs the triangle inequality along a walk, `c = 1/max path length`, `7_8:1110`).

## (b) Script output - Tue Oct  6 01:20:42 UTC 2026

Branch `t/T2234` at `50e0550` (three commits on top of `3a58663`); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2234`.
```
$ lake build RBM3D.Graph.AnpKey 2>&1 | tail -3
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3346 jobs).
$ lake build 2>&1 | tail -1          (whole library, incl. `#assert_rbm_axioms`; `AnpKey` is not yet in `RBM3D.lean`: the hub adds the root import)
Build completed successfully (4038 jobs).
$ git diff main...t/T2234 --stat
 RBM3D/Graph/AnpKey.lean | 945 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   1 +
 2 files changed, 946 insertions(+)
$ wc -l RBM3D/Graph/AnpKey.lean; grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Graph/AnpKey.lean
945
0
```
Registry pre-check (temporary file `import RBM3D` + `import RBM3D.Graph.AnpKey` + `#assert_rbm_axioms`, `lake env lean`; exit 0); before the registry line the same file failed with `1 premise(s) ... [RBM.Graph.AnpDetGhStep]`:
```
axiom audit: 6893 theorems, 2340 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Graph.AnpDetGhStep: 3 [no certificate]
premises found by scanning: 129 (borrowed 1, owed 92, structural 30, refuted 6).
registry: 2 borrowed + 146 owed + 88 structural + 7 refuted; 114 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
`#print axioms` (script `axs.lean`: every new public theorem; the targets and the instance/A2 theorems shown, the rest summarized):
```
anpDetGh_zero : [propext, Classical.choice, Quot.sound]
anpDetGh_of_step : [propext, Classical.choice, Quot.sound]
lwAnpKeyGh_of_det : [propext, Classical.choice, Quot.sound]
lwAnpKey_of_gh : [propext, Classical.choice, Quot.sound]
lwAnp_of_key : [propext, Classical.choice, Quot.sound]
anpKey_inst_zero : [propext, Classical.choice, Quot.sound]
anpKey_inst_anp : [propext, Classical.choice, Quot.sound]
anpKey_inst_figAux : [propext, Classical.choice, Quot.sound]
anpKey_inst_figAux_step : [propext, Classical.choice, Quot.sound]
anpKey_inst_ghostify : [propext, Classical.choice, Quot.sound]
anpKey_ghostify_ghostOK : [propext, Classical.choice, Quot.sound]
anpKey_ghostify_nested : [propext, Classical.choice, Quot.sound]
anpKey_ghostify_nSolid : [propext, Classical.choice, Quot.sound]
anpKey_ghostify_nngh : [propext, Classical.choice, Quot.sound]
anpKey_ghostify_ord : [propext, Classical.choice, Quot.sound]
11 more theorems : [propext, Classical.choice, Quot.sound]
12 more theorems : [propext, Quot.sound]
1 more theorems : [propext]
```
Name-clash grep (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2234/clash.sh`: each of the 47 new public names, whole-word, over `RBM3D/` except `AnpKey.lean`):
```
CLASH? AnpDetGhStep
RBM3D/Test/Axioms.lean:160:   `RBM.Graph.AnpDetGhStep, -- induction step of `lem:Anp_key_gh`, cases (I)-(IV) after the A2 replacement (`7_8:1110-1599`): LW-12b-f (T2234, DECISIONS §24)
names checked:       47, clashes: 1
```
(The one hit is the registry line added by this ticket, not a clash.)

Targets 2-5 against the check-file pins (script `pins.lean`: check-file section 2 copied by script into namespace `RBM.Graph.T2234Check`, then):
```
$ lake env lean pins.lean ; echo $?   -> (no output) exit 0
-- definitions of target 1: each `...Pin` is `Iff.rfl` with the file's definition
example (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : AnpDetGhAtPin d Γ ↔ RBM.Graph.AnpDetGhAt d Γ := Iff.rfl
example (d : ℕ) : AnpDetGhPin d ↔ RBM.Graph.AnpDetGh d := Iff.rfl
example (d : ℕ) : AnpDetGhZeroPin d ↔ RBM.Graph.AnpDetGhZero d := Iff.rfl
example (d : ℕ) : AnpDetGhStepPin d ↔ RBM.Graph.AnpDetGhStep d := Iff.rfl
-- theorems of targets 2-5: each pin is discharged by `@name`, no added hypothesis
example : ∀ d, AnpDetGhZeroPin d := @RBM.Graph.anpDetGh_zero
example : AnpDetGhOfStepPin := @RBM.Graph.anpDetGh_of_step
example : LwAnpKeyGhOfDetPin := @RBM.Graph.lwAnpKeyGh_of_det
example : LwAnpKeyOfGhPin := @RBM.Graph.lwAnpKey_of_gh
example : LwAnpOfKeyPin := @RBM.Graph.lwAnp_of_key
```
Target 1, the definitions of the file (extracted by script; the `...Pin` text of the check file is `Iff.rfl` with each, above):
```
-- AnpKey.lean:41
def AnpDetGhAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ),
      AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          Γ.val ξ a b ≤ C * θ ^ q * ψ 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) *
            ∏ i, (if Γ.noGhostPath i = true then
              ψ (c * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)
-- AnpKey.lean:55
def AnpDetGh (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → AnpDetGhAt d Γ
-- AnpKey.lean:61
def AnpDetGhZero (d : ℕ) : Prop :=
  ∀ (p : ℕ) (Γ : NGraph p 0), Γ.GhostOK → Γ.IsNested → AnpDetGhAt d Γ
-- AnpKey.lean:67
def AnpDetGhStep (d : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q →
    (∀ (p' k : ℕ), k < q → ∀ Γ' : NGraph p' k, Γ'.GhostOK → Γ'.IsNested → AnpDetGhAt d Γ') →
    ∀ (p : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → AnpDetGhAt d Γ
```
Every public declaration of the file, with line and full statement (script `decls.py`; the instances are the `anpKey_inst_*` and `anpKey_oneEdge*` rows, all compiled in the file; the proofs are in the file):
```
41: def AnpDetGhAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop
55: def AnpDetGh (d : ℕ) : Prop
61: def AnpDetGhZero (d : ℕ) : Prop
67: def AnpDetGhStep (d : ℕ) : Prop
80: theorem anpKey_zdistInf_add_le (x y : Zd d L) : zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y
91: theorem anpKey_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x
97: theorem anpKey_zdistInf_sub_comm (x y : Zd d L) : zdistInf d L (x - y) = zdistInf d L (y - x)
101: theorem anpKey_zdistInf_tri (x y z : Zd d L) : zdistInf d L (x - z) ≤ zdistInf d L (x - y) + zdistInf d L (y - z)
124: theorem anpKey_walk {p q : ℕ} (Γ : NGraph p q) {d L : ℕ} [NeZero L] (lbl : NV p q → Zd d L) (M : ℕ) : ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), l.foldl (anpKey_stepFn Γ) (some x) = some y → (∀ st ∈ l, zdistInf d L (lbl (Γ.es.get st.1).u - lbl (Γ.es.get st.1).v) ≤ M) → zdistInf d L (lbl x - lbl y) ≤ l.length * M
167: theorem anpKey_long_edge {p q : ℕ} (Γ : NGraph p q) {d L : ℕ} [NeZero L] (lbl : NV p q → Zd d L) (i : Fin p) (hW : Γ.WalkOK i) : ∃ st ∈ Γ.path i, zdistInf d L (lbl (Sum.inl (Sum.inl i)) - lbl (Sum.inl (Sum.inr i))) ≤ (Γ.path i).length * zdistInf d L (lbl (Γ.es.get st.1).u - lbl (Γ.es.get st.1).v)
339: theorem anpDetGh_zero (d : ℕ) : AnpDetGhZero d
369: def NGraph.ghostifyEs (Γ : NGraph p q) (j : Fin Γ.es.length) : List (NEdge p q)
373: def NGraph.ghostifyIdx (Γ : NGraph p q) (j : Fin Γ.es.length) (i : Fin Γ.es.length) : Fin (Γ.ghostifyEs j).length
378: @[reducible] def NGraph.ghostify (Γ : NGraph p q) (j : Fin Γ.es.length) : NGraph p q
384: theorem anpKey_gf_get (i : Fin Γ.es.length) : (Γ.ghostifyEs j).get (Γ.ghostifyIdx j i) = if i = j then { Γ.es.get i with ghost := true } else Γ.es.get i
393: theorem anpKey_gf_u (i : Fin Γ.es.length) : ((Γ.ghostifyEs j).get (Γ.ghostifyIdx j i)).u = (Γ.es.get i).u
397: theorem anpKey_gf_v (i : Fin Γ.es.length) : ((Γ.ghostifyEs j).get (Γ.ghostifyIdx j i)).v = (Γ.es.get i).v
401: theorem anpKey_gf_ghost (i : Fin Γ.es.length) : ((Γ.ghostifyEs j).get (Γ.ghostifyIdx j i)).ghost = (decide (i = j) || (Γ.es.get i).ghost)
405: theorem anpKey_gf_idx_inj : Function.Injective (Γ.ghostifyIdx j)
410: theorem anpKey_gf_idx_surj (i' : Fin (Γ.ghostify j).es.length) : ∃ i, Γ.ghostifyIdx j i = i'
414: theorem anpKey_gf_path (i : Fin p) : (Γ.ghostify j).path i = (Γ.path i).map fun st => (Γ.ghostifyIdx j st.1, st.2)
417: theorem anpKey_gf_visits (i : Fin p) (v : NV p q) : (Γ.ghostify j).Visits i v ↔ Γ.Visits i v
427: theorem anpKey_gf_walkOK (i : Fin p) (h : Γ.WalkOK i) : (Γ.ghostify j).WalkOK i
434: theorem anpKey_ghostify_nested (h : Γ.IsNested) : (Γ.ghostify j).IsNested
462: theorem anpKey_gf_ghost' (i : Fin Γ.es.length) : ((Γ.ghostify j).es.get (Γ.ghostifyIdx j i)).ghost = (decide (i = j) || (Γ.es.get i).ghost)
468: theorem anpKey_gf_key (hN : Γ.IsNested) {i₀ : Fin p} {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) : ∀ i, ∀ st ∈ Γ.path i, st.1 = st₀.1 → i = i₀ ∧ st = st₀
477: theorem anpKey_ghostify_ghostOK (hG : Γ.GhostOK) (hN : Γ.IsNested) {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true) {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) (hend : (Γ.path i₀).head? = some st₀ ∨ (Γ.path i₀).getLast? = some st₀) : (Γ.ghostify st₀.1).GhostOK
556: theorem anpKey_ghostify_nSolid {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true) {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) : (Γ.ghostify st₀.1).nSolid + 1 = Γ.nSolid
589: theorem anpKey_gf_noGhostPath_iff (hN : Γ.IsNested) {i₀ : Fin p} {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) (i : Fin p) : (Γ.ghostify st₀.1).noGhostPath i = true ↔ Γ.noGhostPath i = true ∧ i ≠ i₀
617: theorem anpKey_ghostify_nngh (hN : Γ.IsNested) {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true) {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) : (Γ.ghostify st₀.1).nngh + 1 = Γ.nngh
634: theorem anpKey_ghostify_ord (hN : Γ.IsNested) {i₀ : Fin p} (hn : Γ.noGhostPath i₀ = true) {st₀ : Fin Γ.es.length × NV p q} (hst₀ : st₀ ∈ Γ.path i₀) : (Γ.ghostify st₀.1).ordN - ((Γ.ghostify st₀.1).nngh : ℤ) = Γ.ordN - (Γ.nngh : ℤ)
649: theorem anpDetGh_of_step : ∀ d : ℕ, AnpDetGhZero d → AnpDetGhStep d → AnpDetGh d
689: theorem lwAnpKeyGh_of_det : ∀ d : ℕ, AnpDetGh d → LWAnpKeyGh d
778: theorem anpKey_ghost_false (h : Γ.NoGhost) (j : Fin Γ.es.length) : (Γ.es[j.1]).ghost = false
782: theorem anpKey_ghostOK_of_noGhost (h : Γ.NoGhost) : Γ.GhostOK
793: theorem anpKey_noGhostPath_of_noGhost (h : Γ.NoGhost) (i : Fin p) : Γ.noGhostPath i = true
799: theorem anpKey_nngh_of_noGhost (h : Γ.NoGhost) : Γ.nngh = p
814: theorem lwAnpKey_of_gh : ∀ d : ℕ, LWAnpKeyGh d → LWAnpKey d
825: theorem lwAnp_of_key : ∀ d : ℕ, LWAnpKey d → LWAnp d
843: def anpKey_oneEdge : NGraph 1 0
847: theorem anpKey_oneEdge_nested : anpKey_oneEdge.IsNested
851: theorem anpKey_oneEdge_ghostOK : anpKey_oneEdge.GhostOK
865: theorem anpKey_inst_zero : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧ anpKey_oneEdge.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤ C * (1 : ℝ) ^ 0 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (anpKey_oneEdge.ordN - (anpKey_oneEdge.nngh : ℤ)) * ∏ i, (if anpKey_oneEdge.noGhostPath i = true then (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1)
894: theorem anpKey_inst_anp (hs : AnpDetGhStep 3) (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) : ∃ c : ℝ, 0 < c ∧ Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) (fun n ab ω => figAux.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2)) (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 * Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 * Φ0 n 0 ^ (figAux.ordN - (2 : ℕ)))
908: theorem anpKey_inst_figAux (h : AnpDetGh 3) : AnpDetGhAt 3 figAux
912: theorem anpKey_inst_figAux_step (hs : AnpDetGhStep 3) : AnpDetGhAt 3 figAux
918: theorem anpKey_inst_ghostify : let st₀ : Fin figAux.es.length × NV 2 2 := (⟨0, by decide⟩, Sum.inr 0) (figAux.ghostify st₀.1).GhostOK ∧ (figAux.ghostify st₀.1).IsNested ∧ (figAux.ghostify st₀.1).nSolid = 5 ∧ (figAux.ghostify st₀.1).nngh = 1 ∧ (figAux.ghostify st₀.1).ordN - ((figAux.ghostify st₀.1).nngh : ℤ) = 0
```
Ports: none from RBM1D/RBM2D (`grep -rlE 'NGraph|Anp_key|AnpKey'` over `RBM1D/RBM1D` at `de0de42` and `RBM2D/RBM2D` at `9e0f275`: 0 files each; diff-stat not applicable).  `anpKey_zdistInf_add_le`, `anpKey_zdistInf_neg`, `anpKey_zdistInf_sub_comm` are copies of the private merged `farEntry_zdistInf_add_le` (`RBM3D/Evolution/FarEntry.lean:117`), `farEntry_zdistInf_neg` (`:127`) and `farEntry_zdistInf_comm` (`:136`), file last touched at `3b1c6a5` on `main`.

### Narrative
- Targets 1-5 are proved with the pinned statements and no added hypothesis; the pins of check-file section 2 are the file's definitions, no primed successor was needed.  `anpDetGh_zero` is `C = 1`, `c = 1/max(sup_i |path i|, 1)`: `Γ.val` at `q = 0` is a single product over the edge list (`Fintype.sum_unique`); a walk lemma (`anpKey_walk`, `anpKey_long_edge`) plus the triangle inequality gives each path an edge of length at least `|a_i-b_i|/|path i|`; the chosen edges are distinct (`IsNested` conjunct 4), the rest are at most `ψ(0)` (solid) or `1` (ghost); `ord - n_ngh = n_S - n_ngh` as a natural power.
- `lwAnpKeyGh_of_det` follows preflight (iii), not the ticket's union-bound route: `badSetAt` already has the `∃ u` inside `P`, so the event `Ξ_n` (two `Prec.whp` events at `τ'`, `HighProbAt.inter`) suffices, with `τ' = τ/(2(q+|ord-n_ngh|+p+1))`; on `Ξ_n` the deterministic bound at `(ψ, θ) = (N^τ' Φ_n, N^τ' θ_n)` has the factor `N^{τ'(q+k+n_ngh)} <= N^{τ/2}` (`k = ord - n_ngh`), and `C <= N^{τ/2}` eventually (`Sizes.tendsto_size`); `θ_n > 0` uses `etaT_pos` fed by `lemT_lt_one` and `abs_lemE_lt_two`, from `STFlow` (`locDomain` gives `0 < Im z`) and `t <= lemT z` (preflight (iii)(1)).  `3 <= d`, `κ, ε, 𝔡 > 0`, `q <= p` and `0 <= t` are carried and not used.
- Lemma (c'): `NGraph.ghostify` (edge `j` made ghost; `ghostifyEs`, `ghostifyIdx` carry the length cast) with `anpKey_ghostify_nested`, `_ghostOK` (hypotheses: `Γ.GhostOK`, `Γ.IsNested`, a ghost-free path `i0` with its step `st0` first or last), `_nSolid` (`+1 = nSolid`), `_nngh`, `_ord` (`ord - n_ngh` unchanged); section 3 is lines 362-644 (below the 300-line limit of the ticket), so it stays here, not in LW-12b.  Instance `anpKey_inst_ghostify` is `figAux` with its first step ghosted: `nSolid = 5`, `nngh = 1`, `ord - n_ngh = 0`.
- Instances (CLAUDE.md section 4 step 2): `anpKey_inst_zero` (`anpDetGh_zero` at the one-edge graph, `d = L = 3`, `ψ r = (1+r)⁻¹`, `θ = 1`, `ξ = 1/6`, `a = 0`, `b = 1`, every deterministic hypothesis discharged); `anpKey_inst_anp` (the chain `anpDetGh_of_step`, `lwAnpKeyGh_of_det`, `lwAnpKey_of_gh`, `lwAnp_of_key` as the `h` of the merged `inst_Anp`; `hs : AnpDetGhStep 3` (LW-12b-f) and the edge variables `ξ` with `hξ : LWXi ...` (the random premise; the ticket says LW-11b's `lwXiClaim_holds` proves it at the random data) stay hypotheses); `anpKey_inst_figAux`, `anpKey_inst_figAux_step` (`figAux` is a legal input, `GhostOK` from `anpKey_ghostOK_of_noGhost figAux_nested.2`).
- Registry: the pre-check listed only `RBM.Graph.AnpDetGhStep` (the ticket expected also `AnpDetGh`, which the pre-check did not list; `AnpDetGhZero`, `AnpDetGhAt` were not listed either, so only `AnpDetGhStep` is registered); one line added to `RBM3D/Test/Axioms.lean` after the `LWAnp` line, no deletion.
- Not checked here: that `AnpDetGhStep` holds (cases (I)-(IV) are LW-12b-f; the numerics in (a) at `q = 2` are evidence only).  The merged pins `LWAnpKey`, `LWAnpKeyGh`, `LWAnp` stay owed (no deletion).

## (c) Verified Mathlib names (script: `#check @name` in `m_present.lean`, no error; five per line)
```
Finset.card_filter; Finset.card_image_of_injective; Finset.card_erase_of_mem; Finset.card_sdiff_of_subset; Finset.exists_max_image
Finset.prod_le_prod₀; Finset.prod_image; Finset.prod_mul_prod_compl; Finset.prod_ite; Finset.prod_mul_distrib
Finset.filter_true_of_mem; Finset.card_filter_le; Fintype.sum_unique; List.ofFn_getElem_eq_map; List.prod_ofFn
List.sum_ofFn; List.inj_on_of_nodup_map; List.Nodup.subperm; List.Subperm.length_le; List.Nodup.of_map
List.Nodup.filter; List.filter_congr; List.filter_map; List.foldl_map; List.head?_map
List.getLast?_map; List.getElem_set; List.length_set; List.getElem_mem; List.mem_iff_get
List.all_eq_true; List.filter_eq_nil_iff; List.toFinset_eq_empty_iff; Int.le_natAbs; zpow_natCast
zpow_add₀; mul_zpow; zpow_le_zpow_right₀; zpow_nonneg; Real.one_le_rpow
Real.rpow_mul; Real.rpow_add; Real.rpow_le_rpow_of_exponent_le; Real.rpow_pos_of_pos; Real.rpow_nonneg
tendsto_rpow_atTop; Filter.Tendsto.eventually_ge_atTop; inv_anti₀; one_div_le_one_div_of_le; inv_mul_le_iff₀
div_le_div_iff₀; div_le_one; half_pos; Nat.strong_induction_on; Bool.or_eq_false_iff
```
Verified absent (`#check` -> `Unknown constant`): `Fin.prod_univ_get'`, `List.length_filter`, `List.card_filter_univ`, `Option.some_bind`, `Finset.prod_le_prod_of_nonneg`.  Deprecated in this Mathlib (warning at build, not used): `if_pos`, `if_neg`, `ite_cond_eq_true`, `ite_cond_eq_false`.  `Finset.prod_le_prod` has no nonnegativity hypothesis here; the nonnegative version is `Finset.prod_le_prod₀`.

## (d) Open issues and paper-delta candidates
- Open: `AnpDetGhStep` is the content of LW-12b-f (cases (I)-(IV), `7_8:1111-1599`); this ticket proves only `q = 0` and the assembly.  The ticket's count question (LW-12 as 6 tickets, 38 vs 43) is the dispatcher's; this file has 945 lines (ticket estimate 1000-1400).
- `T2234a`: `lem:Anp_key_gh` is proved in a deterministic form (`AnpDetGhAt`: exact inequalities under deterministic `(eq:Gbyxi3)` with `ψ`, `θ`; `C, c` depend on `Γ` and `d` only) and lifted to `≺` on one event (`Prec.whp` at `τ'` for the two premises of `LWXi`, `HighProbAt.inter`); the paper states `(adsuu22)` with `≺` (`7_8:1043`) under `(eq:Gbyxi3)` with `≺` (`7_8:963-966`).  No union bound over the `L^(2d)` pairs is needed: the union over `u` is inside `badSetAt`.
- `T2234b`: the base case `q = 0` (`7_8:1117`, "is trivial in the case `q=0`, by `(eq:Gbyxi3)`"; the ticket cites `:1110`) needs the triangle inequality along a walk of an external-vertex path; the constant is `c = 1/max(1, max_i |path i|)`, `C = 1`.
- `T2234c`: the A2 replacement of `7_8:1143-1148` is made explicit as `NGraph.ghostify` (one edge index made ghost; the bookkeeping `n_S - 1`, `n_ngh - 1`, `ord - n_ngh` unchanged is `(eq:noA2)`, `7_8:1146`).
- `T2234d`: the merged pins carry `q <= p` and `0 <= t`; `q <= p` follows from `IsNested` conjunct 6 at `A = univ` and is not used; `0 <= t` is not used; `0 < η_t` (needed for `θ_n > 0`) is derived from `STFlow` and `t <= lemT z` (`etaT_pos`, `lemT_lt_one`, `abs_lemE_lt_two`), which the paper leaves implicit.
