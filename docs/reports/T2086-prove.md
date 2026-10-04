Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 23:19:02 UTC 2026

Sources read: ticket T2086; pin `STNewPQ` (`RBM3D/Induction/Step34Pins.lean:330`); paper `3_5_Loop_Hierarchy.tex:1482-1507` (`lem: newPQ`, `(yurenAL)`, `(yurenAK)`) and its proof `3_5:1866-1886`; `(WI_calL)`, `(WI_calK)` `1_2_Intro_model_result.tex:1036-1042`; merged `sum_gloop_ward_last_div` (`Induction/ConArgDet.lean:312`), `KLK_ward` (`Loop/KLWard.lean:1123`), `KLK_rotate` (`Loop/KLUnique.lean:640`), `zeroModeSet` (`Kernel/Evolution.lean:199`).
Conventions (from the files): `Lloop = tr Π_i G(σ_i) E_{a_i}` (`Loop/GLoop.lean:96-99`, `E_a = W^{-d} 1_{[a]}`); `P^(i) f = L^{-d} Σ_c f(a with a_i := c)`, `Q^(i) = I − P^(i)`, `Q^(A) = Π_{i∈A} Q^(i)`; `STIdiff σ = {i : σ_i ≠ σ_{i+1}}`, cyclic `finRotate` (= paper `3_5:1470`); `N = sz.size n = (W L)^d`; `η_τ = etaT E τ = (1−τ) Im m(E) = Im z_τ` (`etaT_eq_zt_im`).

**Mathematics of the construction (one Ward step at index `i`).** `σ_i ≠ σ_{i+1}`, `m ≥ 2`. The factors around `E_{a_i}` are `G(σ_i) E_{a_i} G(σ_{i+1})`; `Σ_{a_i} E_{a_i} = W^{-d}·1`, so `Σ_{a_i} 𝓛_{σ,a} = W^{-d} tr(… G(σ_i)G(σ_{i+1}) …)`, and `G(z)G(z̄) = G(z̄)G(z) = (G(z) − G(z̄))/(2iη)` (`green_sub_green`, `green_sub_green_conj'`), for both orders `(σ_i,σ_{i+1}) = (−,+)` and `(+,−)` with the same right side. Hence `Σ_{a_i} 𝓛^{(m)}_{σ,a} = (2iW^dη)⁻¹ (𝓛^{(m−1)}_{σ⁺, a∘ι_i} − 𝓛^{(m−1)}_{σ⁻, a∘ι_i})`, `ι_i = Fin.succAbove i : Fin(m−1) → Fin m`, `σ^s := (σ with σ_{i+1} := s) ∘ ι_i`. Then `P^(i)` gives `L^{-d}·(2iW^dη)⁻¹ = (2iNη)⁻¹` (`N = W^d L^d`), and `Q^(A)` with `i ∉ A` commutes through (the right side does not depend on `a_i`; `A ↦ A_(i) = ι_i⁻¹(A)`). Same for `𝒦`: `KLK_ward` has the same right side for both `s = ±`.
Induction on `r = #(Idiff(σ) \ A)` (`r = 0`, or `m ≤ 1` where `Idiff = ∅`: no terms, `ℓ = 0`). Else `i = min(Idiff\A)`: `Q^(A) = Q^(A∪{i}) + Q^(A) P^(i)`. First term: `r−1`, same `σ`, `A ∪ {i}`, main term `Q^(A∪{i}∪Idiff) = Q^(A∪Idiff)`. Second term: `Σ_± ±(2iNη)⁻¹ Q^(A_(i)) 𝓛^{(m−1)}_{σ^±}`; apply the induction on `m` to each: it yields the term `(k = m−1, ξ = ±1, σ^±, ι_i, A_(i) ∪ Idiff(σ^±))` (exponent `(2iNη)^{-1} = (·)^{-(m−k)}`, `A' ⊇ Idiff(σ^±)` by construction) and, for every induction term `(k,ξ,σ',ι',A')` of `(m−1,σ^±,A_(i))`, the term `(k, ±ξ, σ', ι_i∘ι', A')` with exponent `(m−1−k)+1 = m−k` and `A' ⊇ Idiff(σ')` inherited. Ranges: `k ≤ m−1`, `k ≥ 1` (Ward needs `m ≥ 2`, output length `m−1 ≥ 1`). The data `(ℓ,k,ξ,σ',ι,A')` depend only on `(m,σ,A)`, not on `sz, n, E, τ, ω, a`.
Where the non-merged piece is: `sum_gloop_ward_last_div` is the case `σ_1 = +`, `σ_n = −` at the last index only; `Σ_{a_i}` at interior `i`, and the order `(−,…,+)`, need (1) cyclic invariance of `𝓛` (trace cyclicity, `cad_gloop_rotate` is private: copy) and of `𝒦` (`KLK_rotate`, one step `⟨s::σ, b::a⟩ ↦ ⟨σ++[s], a++[b]⟩`), iterated to bring `a_i` last and then back; (2) for `(−,…,+)`: `G(+)G(−)` instead of `G(−)G(+)` — the same resolvent identity `green_sub_green hz hz'` (no conjugate-transpose symmetry of loops is needed; reversal of orientation never occurs).

### (i) Exponent table

| # | Quantity | Value | Constraint | Slack / check |
|---|---|---|---|---|
| 1 | `η_τ = (1−τ) Im m(E)`, `m(E) = (−E+i√(4−E²))/2` | `0.494343` at `E=0.3`, `τ=1/2` | `> 0` iff `\|E\|<2`, `τ<1` (`etaT_pos`); Ward needs `Im z_τ ≠ 0`, `KLK_ward` needs `0 ≤ τ < 1`, `\|E\|<2` | exactly the pin's range; `τ = 0` allowed |
| 2 | Ward factor on `Σ_{a_i}`: `(2i W^d η)⁻¹` | `1/(2i·8·0.494343)` | `W ≥ 1` (`Sizes.W_pos`), `Im z ≠ 0` | no further condition |
| 3 | `P^(i)` factor `L^{-d}`; product `(2iNη)⁻¹`, `N = (WL)^d` | `N = 216 = W^d L^d = 8·27` | `L ≥ 1` (`Sizes.three_le_L`) | control run: replacing `N` by `W^d` breaks the identity (`6.55e-2` vs `3.5e-18`, below) |
| 4 | exponent of `(2iNη)⁻¹` in a term | `m − k_α`, `1 ≤ m−k_α` | one Ward step lowers length by 1 and gives one factor, so `m−k` = number of steps | `k_α ≤ m−1` ✓ (pin); `k_α ≥ 1` from `m ≥ 2` at each step |
| 5 | `ξ_α ∈ ℤ` | `±1` per term (`sum_xi = 0` in the runs; not merged) | integer, independent of `W, L, λ, sz, n, E, τ, ω, a` | no constant in `ℓ`, `ξ` involves `W, L, λ` |
| 6 | count `ℓ(m,σ,A)` | `T(m,r) = T(m,r−1) + 2(1 + T(m−1,r'))`, `r,r' ≤ m` | finite, depends on `m` only: `U(1)=0`, `U(m) ≤ 2m(1+U(m−1))`: `U(2)=4, U(3)=30, U(4)=248` | actual `ℓ = 10` (`m=3,+−+,A=∅`), `4` (`m=2`), `32` (`m=4,++−−`) |
| 7 | `A_α ⊇ Idiff(σ_α)` | main term: `A_(i) ∪ Idiff(σ^±)` ⊇ `Idiff(σ^±)`; induction terms: inherited | `A_(i) = ι_i⁻¹(A)` valid since `i ∉ A` | script asserts `idiff(σ') ⊆ A'` for every term |
| 8 | `ι_α : Fin k_α → Fin m` | composite of `succAbove`'s, strictly increasing, injective | `a_α = a ∘ ι_α` a sub-collection of `a` | script asserts `ι` sorted and injective |
| 9 | edge lengths | `m = 0`: `Fin 0`, `Idiff = ∅`; `m = 1`: `finRotate 1 = id`, `Idiff = ∅`; `m = 2`: `k = 1` | `m ≤ 1`: `ℓ = 0` forced (`1 ≤ k`, `k+1 ≤ m` impossible) and the identity is `Q^(A)T = Q^(A∪∅)T` | no degenerate counterexample; `σ` constant: `Idiff = ∅`, `ℓ = 0` ✓ |
| 10 | `Sizes` fields | `3 ≤ L n`, `0 < W n` for every `n` | needed by `KLK_ward`, `KLK_rotate`, `NeZero` | the pin quantifies `∀ n`; no `∀ᶠ n`, no relation between `L, W, lam` is used (DECISIONS §29 items (3),(4)) |
| 11 | §29 item (1): time domain | `0 ≤ τ < 1`, `\|E\| < 2` | as row 1 | pin hypotheses are exactly these; item (2) (`1−ilambda²/L²` boundary) does not occur |

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `L = 3`, `W = 2` (`Vtx = Z_3^3 × Fin 8`, `N = 216`, `27` labels per slot), one sample `H = (X+Xᴴ)/√(4N)` (complex Gaussian `X`, seed 2086, `H = Hᴴ` asserted), `E = 0.3`, `τ = 1/2` (`z_τ = E + (1−τ)m(E) = 0.225+0.494343i`), `m = 3`, `σ = (+,−,+)`, `A = ∅`, so `Idiff = {0,1}` (0-based). The recursion above (`expand`) produces the data; both sides are tensors over all `27³` labels `a`; `lhs = Q^(A)𝓛^{(m)}`, `rhs` = right side of `(yurenAL)` with `A_m = A ∪ Idiff`, `c = (2iNη)⁻¹`. Extra rows: `A = {1}`, `m = 2`, `m = 4` (`++−−`, and `+−+−` with `A = {0}`; tensors of `27^4` entries). `lhs − mainterm` shows the identity is not vacuous (the `Σ_α` terms are the whole difference). The `𝒦` identity uses the same data, and `KLK_ward` + `KLK_rotate` are the only inputs the bookkeeping uses, so the numerics for `𝓛` are the check of the bookkeeping for both.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2086/inst.py 2>&1 | cut -c1-330` (numpy; Python only, no Lean). Verbatim output:

```
N=216 blocks=27 W^d=8 z=0.225000+0.494343j eta=0.494343 |E|<2:True 0<=tau<1:True 2iN*eta=0.0000+213.5562j
ticket instance: m=3 sigma=+-+ A=[] Idiff=[0, 1] #terms=10 k-histogram={1: 6, 2: 4} sum_xi=0 max|lhs|=8.973e-03 max|lhs-rhs|=3.48e-18 max|lhs-mainterm|=1.503e-03
   control with N'=W^d: max|lhs-rhs'|=6.55e-02
A={1}: m=3 sigma=+-+ A=[1] Idiff=[0, 1] #terms=4 k-histogram={1: 2, 2: 2} sum_xi=0 max|lhs|=8.199e-03 max|lhs-rhs|=1.75e-18 max|lhs-mainterm|=7.292e-04
   control with N'=W^d: max|lhs-rhs'|=1.99e-02
m=2: m=2 sigma=+- A=[] Idiff=[0, 1] #terms=4 k-histogram={1: 4} sum_xi=0 max|lhs|=8.540e-02 max|lhs-rhs|=1.39e-17 max|lhs-mainterm|=7.787e-03
   control with N'=W^d: max|lhs-rhs'|=2.02e-01
m=4 ++--: m=4 sigma=++-- A=[] Idiff=[1, 3] #terms=32 k-histogram={1: 16, 2: 12, 3: 4} sum_xi=0 max|lhs|=9.810e-04 max|lhs-rhs|=7.59e-19 max|lhs-mainterm|=1.593e-04
   control with N'=W^d: max|lhs-rhs'|=2.56e-02
m=4 +-+-: m=4 sigma=+-+- A=[0] Idiff=[0, 1, 2, 3] #terms=18 k-histogram={1: 4, 2: 8, 3: 6} sum_xi=0 max|lhs|=8.995e-04 max|lhs-rhs|=8.67e-19 max|lhs-mainterm|=2.179e-04
```

Reading (`m=3`, `σ=(+,−,+)`, `A=∅`): `max|lhs| = 8.97e-3`, `max|lhs−rhs| = 3.5e-18` (relative `4e-16`), while `max|lhs − Q^(A∪Idiff)𝓛| = 1.5e-3` (the `Σ_α` terms carry a relative `17%` of `lhs`). No hypothesis is external, so no limit computation is required (the `𝒦` Ward identity and its rotation are merged theorems, `KLK_ward`, `KLK_rotate`).

### Verdicts

- `stNewPQ_holds (d : ℕ) : STNewPQ d`: **PASS.** The pin is true as written: the range `0 ≤ τ < 1`, `|E| < 2` is exactly where `η_τ > 0` and where `KLK_ward` applies; no constant depends on `W, L, λ`; degenerate `m ≤ 1`, `A = ⟦m⟧`, constant `σ` all give `ℓ = 0` and a trivial identity (row 9), so no counterexample exists. The data are built by induction on `(m, #(Idiff\A))`, one Ward step per index, with `ξ = ±1`.
- Stage-1b notes (mathematical, not Lean): (1) Ward at an interior index `i` for `𝓛` and for `𝒦` = rotate `a_i` to the end (`gloop_rotate` copy / `KLK_rotate`, iterated), apply the last-index Ward, rotate the `(m−1)`-loop back; the order `(−,…,+)` is `green_sub_green hz hz'` instead of `green_sub_green_conj'` (same right side `(+) − (−)`). (2) `STKloop sz n E τ σ a = KLK d L (lam n) (W n) E τ (KLloopOf σ a)` with `KLloopOf σ a = ⟨ofFn σ, ofFn a⟩` is already the list form of `KLK_ward`/`KLK_rotate`, so no bridge beyond `ofFn` list lemmas is needed; `Lloop = loopFine = loopM (blockMat H) z (…)` and `loopM_eq_loopL` (`Loop/GLoopFlow.lean:~120`) gives the list form. (3) `Q^(A)` through the Ward sum: `zeroModeSet` is defined by `A.toList.foldr`, so a commutation lemma `Q^(i)Q^(j) = Q^(j)Q^(i)` (or order independence) is needed for `Q^(A) = Q^(A∪{i}) + Q^(A)P^(i)`; no such lemma exists in `Kernel/Evolution.lean` (`grep zeroMode…`: only `zeroModeOp_tensorKer`, `zeroModeList_tensorKer`, `zeroModeSet_tensorKer`).
- Paper-delta candidate (for the report (d)): `T2086a`: the proof of `lem: newPQ` writes `(y2ussz)` with the sets `A_(i)` and the deletion of position `i` as if `i < n`; for `i = n` (cyclic, `σ_{n+1} = σ_1`) the deleted charge is `σ_n` and `σ_1` is replaced (what `ι = succAbove`, `σ^s` above does); the printed formula `σ_± = (σ_1…σ_{i−1}, ±, σ_{i+2}…)` is the same loop only up to a cyclic rotation.

## (a′) Preflight corrections — Sun Oct  4 00:02:09 UTC 2026

No verdict-changing mistake in (a). One difference of construction, not of the pin: (a) row 8 describes the Python construction with `ι_α` a composite of `succAbove` (strictly increasing). The Lean construction rotates the loop by `ρ^(i+1)` (`ρ = finRotate`) so that the edge `i` is last and lists the remaining positions cyclically from `i+1`: `ι = ρ^(i+1) ∘ castSucc` (not monotone). The pin only asks `ι_α : Fin k_α → Fin m` and `a_α = a ∘ ι_α`, so the target is unchanged (candidate T2086b, section (d)).

## (b) Script output — Sun Oct  4 00:02:09 UTC 2026

### Module build (new module), then the full library build, then the registry pre-check (CLAUDE.md §5.4, DECISIONS §20)
```
$ lake build RBM3D.Induction.NewPQ 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3708 jobs).
```
```
$ lake build 2>&1 | tail -2
non-vacuity certificates: 4 of 97 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3829 jobs).
```
```
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2086/precheck.lean > /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2086/precheck.out 2>&1; echo exit=$?; head -2 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2086/precheck.out | cut -c1-120; grep -n 'STNewPQ' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2086/precheck.out
exit=0
axiom audit: 2856 theorems, 1121 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
44:  RBM.Gauss.Sizes.STNewPQ: 2 [no certificate]
120: RBM.Gauss.Sizes.STNewPQ,
```
(precheck file, not committed: `import RBM3D`, `import RBM3D.Induction.NewPQ`, `#assert_rbm_axioms`.)

### Axioms and hygiene
```
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2086/ax.lean
'RBM.Gauss.Sizes.stNewPQ_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/NewPQ.lean; wc -l RBM3D/Induction/NewPQ.lean
0
     682 RBM3D/Induction/NewPQ.lean
```
```
$ git diff main...t/T2086 --stat
 RBM3D/Induction/NewPQ.lean | 682 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 682 insertions(+)
```

### Target statement (extracted from the file) and the pin it must equal
```
$ grep -n '^theorem stNewPQ_holds' RBM3D/Induction/NewPQ.lean
584:theorem stNewPQ_holds (d : ℕ) : STNewPQ d := by
```
```
$ sed -n '330,344p' RBM3D/Induction/Step34Pins.lean
def STNewPQ (d : ℕ) : Prop :=
  ∀ (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)),
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ)
        (a : Fin m → Zd d (sz.L n)),
        (zeroModeSet d (sz.L n) A (fun a' => Lloop sz n E τ σ a' ω) a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => Lloop sz n E τ σ a' ω) a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α) (fun a' => Lloop sz n E τ (σ' α) a' ω) (a ∘ ι α)) ∧
        (zeroModeSet d (sz.L n) A (fun a' => STKloop sz n E τ σ a') a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => STKloop sz n E τ σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α) (fun a' => STKloop sz n E τ (σ' α) a') (a ∘ ι α))
```

### Compiled nonempty instance (`example` in the same file; `sz0`, `d = 3`, `m = 3`, `σ = (+,-,+)`, `A = ∅`, `n = 0`, `E = 0`, `τ = 1/2`)
```
$ sed -n '/^example : ∃ (ℓ/,/^end Gauss.Sizes.NewPQInst/p' RBM3D/Induction/NewPQ.lean
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      (zeroModeSet 3 (sz0.L 0) ∅ (fun a' => Lloop sz0 0 0 (1 / 2) ![true, false, true] a' ω) a =
        zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff ![true, false, true])
            (fun a' => Lloop sz0 0 0 (1 / 2) ![true, false, true] a' ω) a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                (Gauss.etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => Lloop sz0 0 0 (1 / 2) (σ' α) a' ω) (a ∘ ι α)) ∧
      (zeroModeSet 3 (sz0.L 0) ∅ (fun a' => STKloop sz0 0 0 (1 / 2) ![true, false, true] a') a =
        zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff ![true, false, true])
            (fun a' => STKloop sz0 0 0 (1 / 2) ![true, false, true] a') a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                (Gauss.etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => STKloop sz0 0 0 (1 / 2) (σ' α) a') (a ∘ ι α)) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := Gauss.Sizes.stNewPQ_holds 3 3 ![true, false, true] ∅
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ω a⟩

end Gauss.Sizes.NewPQInst
```

### Name-clash grep (new public names: `stNewPQ_holds`; every helper is `private`)
```
$ grep -rnE 'stNewPQ_holds|NewPQInst' RBM3D RBM3D.lean --include='*.lean' | grep -v 'Induction/NewPQ.lean' | wc -l
       0
```
```
$ grep -rnE 'npq_|npqRot|npqSg|npqIota|NPQ(Ward|Fam|Term)' RBM3D RBM3D.lean --include='*.lean' | grep -v 'Induction/NewPQ.lean' | wc -l
       0
```
```
$ grep -cE '^private' RBM3D/Induction/NewPQ.lean
37
```
```
$ grep -nE '^(theorem|def|structure|lemma|instance|example)' RBM3D/Induction/NewPQ.lean | cut -c1-70
584:theorem stNewPQ_holds (d : ℕ) : STNewPQ d := by
660:example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin
```

### Ports
None: no RBM2D/RBM1D source (portmap row S3-03: "new (paper lines)").
```
$ grep -rlE 'newPQ|NewPQ|new_PQ' /Users/junyin/Lean_proof/RBM2D/RBM2D /Users/junyin/Lean_proof/RBM2D/docs /Users/junyin/Lean_proof/RBM1D/RBM1D 2>/dev/null | wc -l
       0
```

### Narrative (facts checked against the file; at most 40 lines)

1. Target: `RBM.Gauss.Sizes.stNewPQ_holds (d : ℕ) : STNewPQ d` (`RBM3D/Induction/NewPQ.lean:584`), the pin's type exactly, for every `d` (no `3 ≤ d` used). Sole writable file touched: `RBM3D/Induction/NewPQ.lean` (commit `ae37223` on `t/T2086`); `RBM3D/Test/Axioms.lean` is untouched.
2. Data. `npq_main` (private) states, for every `m`, `σ`, `B ⊆ I_diff σ` and `A`: there is a `List (NPQTerm m)` (records `(k, ξ, σ, ι, A)`) such that for all `L`, `c`, loop families `T` with the hypothesis `NPQWard` the identity `Q^(A) T_σ = Q^(A ∪ B) T_σ + ∑ ξ c^(m-k) Q^(A_α) T_{σ_α}(· ∘ ι)` holds. The `∃` precedes `L, c, T`, so the data do not depend on sizes, sample, labels, `E`, `τ`; the same list serves `𝓛` and `𝒦` (final step of `stNewPQ_holds`).
3. Induction: strong induction on `m`, `Finset.induction_on` on `B`. Step for `i ∉ A`: `Q^(A) = Q^(insert i A) + P^(i) Q^(A)` (`npq_split`, from `npq_zms_insert`), `P^(i)` passes through `Q^(A)` (`npq_avg_zms`), `P^(i) T_σ = c (T_{σ^+} - T_{σ^-})` (`NPQWard`), and `Q^(A)(G ∘ (· ∘ ι)) = (Q^(ι⁻¹A) G) ∘ (· ∘ ι)` for `A ⊆ range ι` (`npq_zms_comp`); the main term of each `σ^±` becomes a new term with `ξ = ±1`, `k = m-1`, `A_α = ι⁻¹A ∪ I_diff(σ^±) ⊇ I_diff(σ^±)`; the terms of the induction hypothesis are lifted with a sign (`NPQTerm.lift`, `npq_lift_sum`), exponent `(m-1-k)+1 = m-k`. For `i ∈ A` no step is made. A step needs `m ≥ 2` (`i ∈ I_diff σ` is impossible for `m = 0, 1`), so `1 ≤ k` and `k + 1 ≤ m`.
4. `Q^(A)` is `zeroModeSet`, defined by `A.toList.foldr`; the commutation `Q^(i) Q^(j) = Q^(j) Q^(i)` (`npq_zmo_comm`) was missing and is proved here (as (a) noted); it gives `LeftCommutative` and `npq_zms_insert` through `List.Perm.foldr_eq`.
5. `𝓛`, which Ward lemmas: the merged `sum_gloop_ward_last_div` is `σ₁ = +` only. `npq_loopL_ward` gives both orders: `s = +` is the merged lemma, `s = -` is the merged lemma at `z̄` (`Im z̄ = -Im z`) with the charges flipped by `npq_loopL_conj`; no conjugate-transpose symmetry of loops is used. Cyclic invariance `npq_loopL_rotate` is proved here by `Matrix.trace_mul_comm` (the merged one is private to `ConArgDet`). A Ward step at an interior index is `npq_ward_of_fam`: rotate by `ρ^(i+1)` (`npq_rot_pow`, `ρ = finRotate`), apply the last-index identity (`npq_ward_last`), keep the rotated labelling (`ι = ρ^(i+1) ∘ castSucc`, correction (a′)).
6. `𝒦`: `KLK_rotate` and `KLK_ward` are used as stated. `STKloop sz n E τ σ a` is `KLK … ⟨List.ofFn σ, List.ofFn a⟩` by `rfl` (`KLloopOf`), so `h … hward` elaborates with `T := STKloop …` and no bridge lemma is needed. `Lloop` is turned into `loopL` by `loopM_eq_loopL` (`RBM3D/Loop/GLoopFlow.lean:127`); Hermitian-ness of `blockMat (seqHflow …)` is `gLoopFlow_seqHflow_isHermitian` plus `Matrix.IsHermitian.submatrix`.
7. Constants (DECISIONS §29): `c = L^{-d} (2 i W^d η_τ)⁻¹ = (2 i N η_τ)⁻¹`, `N = sz.size n = (W L)^d` (`hcL` in `stNewPQ_holds`); `ξ_α` are products of `±1`; the only hypotheses used are the pin's `|E| < 2`, `0 ≤ τ < 1`, `3 ≤ L n`, `1 ≤ W n` (`Sizes.three_le_L`, `W_pos`) with `etaT_pos`, `KLK_ward`, `KLK_rotate`. No constant depends on `W`, `L`, `λ`; no `∀ᶠ n`.
8. Instance: the `example` instantiates the theorem at `sz0`, `n = 0`, `E = 0`, `τ = 1/2`, `m = 3`, `σ = (+,-,+)`, `A = ∅`, all three deterministic hypotheses by `norm_num`; `ω`, `a` universally quantified. It does not expose the length `ℓ` of the Lean list (existential in the pin); the `ℓ = 10` of (a) is the count of the Python construction, not a statement about the Lean data. The identity itself was checked numerically in (a).
9. Registry: no new `Prop`-valued hypothesis is taken by a public lemma (`NPQWard`, `NPQFam` are private). `STNewPQ`'s owed line (`RBM3D/Test/Axioms.lean:120`) can go once this merges; `inst_newPQ (h : STNewPQ 3)` (`RBM3D/Induction/Step34Pins.lean:1062`) can then take `stNewPQ_holds 3`.

## (c) Verified Mathlib / core names used (each by `#check` in a scratch file, exit 0, no error; one line each, output cut at 150 characters)

```
@List.Perm.foldr_eq : ∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ l₂ : List α} [lcomm : LeftCommutative f], [...]
@Finset.toList_insert : ∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {s : Finset α}, a ∉ s → (insert a s).toList.Perm (a :: s.toList)
@Function.update_comp_eq_of_injective : ∀ {α : Sort u_1} {α' : Sort u_2} [inst : DecidableEq α] [inst_1 : DecidableEq α'] {β : Sort u_3} (g : α' → β) 
@Function.update_comp_equiv : ∀ {α : Sort u_1} {β : Sort u_2} {α' : Sort u_3} [inst : DecidableEq α'] [inst_1 : DecidableEq α] (f : α → β) [...]
@Function.update_comm : ∀ {α : Sort u_2} [inst : DecidableEq α] {β : α → Sort u_1} {a b : α}, [...]
@finRotate_apply : ∀ {n : ℕ} (i : Fin n), (finRotate n) i = i + 1
@finRotate_last : ∀ {n : ℕ}, (finRotate (n + 1)) (Fin.last n) = 0
@coe_finRotate_of_ne_last : ∀ {n : ℕ} {i : Fin n.succ}, i ≠ Fin.last n → ↑((finRotate (n + 1)) i) = ↑i + 1
@Fin.exists_castSucc_eq : ∀ {n : ℕ} {i : Fin (n + 1)}, (∃ j, j.castSucc = i) ↔ i ≠ Fin.last n
@List.ofFn_succ : ∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofFn f = f 0 :: List.ofFn fun i => f i.succ
@List.ofFn_succ' : ∀ {α : Type u_1} {n : ℕ} (f : Fin n.succ → α), List.ofFn f = (List.ofFn fun i => f i.castSucc).concat (f (Fin.last n))
@List.sum_ofFn : ∀ {M : Type u_1} [inst : AddCommMonoid M] {n : ℕ} {f : Fin n → M}, (List.ofFn f).sum = ∑ i, f i
@List.ofFn_get : ∀ {α : Type u_1} (l : List α), List.ofFn l.get = l
@List.map_ofFn : ∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
@Matrix.IsHermitian.submatrix : ∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : Star α] {A : Matrix n n α}, [...]
@Fin.coeSucc_eq_succ : ∀ {n : ℕ} {a : Fin n}, a.castSucc + 1 = a.succ
Fin.last_add_one : ∀ (n : ℕ), Fin.last n + 1 = 0
@Fin.succ_castSucc : ∀ {n : ℕ} (i : Fin n), i.castSucc.succ = i.succ.castSucc
Fin.succ_last : ∀ (n : ℕ), (Fin.last n).succ = Fin.last n.succ
@Bool.eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b
@List.zip_map_left : ∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {f : α → γ} {l₁ : List α} {l₂ : List β}, [...]
@List.zip_append : ∀ {α : Type u_1} {β : Type u_2} {l₁ r₁ : List α} {l₂ r₂ : List β}, [...]
@List.sum_map_mul_left : ∀ {ι : Type u_1} {R : Type u_2} [inst : NonUnitalNonAssocSemiring R] (l : List ι) (f : ι → R) (r : R), [...]
@List.map_congr_left : ∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
@Equiv.Perm.coe_mul : ∀ {α : Type u_1} (f g : Equiv.Perm α), ⇑(f * g) = ⇑f ∘ ⇑g
@Equiv.symm_apply_eq : ∀ {α : Sort u_1} {β : Sort u_2} (e : α ≃ β) {x : β} {y : α}, e.symm x = y ↔ x = e y
@Matrix.trace_mul_comm : ∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : AddCommMonoid R] [...]
@Finset.induction_on : ∀ {α : Type u_1} {motive : Finset α → Prop} [inst : DecidableEq α] (s : Finset α), [...]
@Finset.insert_eq_of_mem : ∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {a : α}, a ∈ s → insert a s = s
@Finset.union_insert : ∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s t : Finset α), s ∪ insert a t = insert a (s ∪ t)
@Finset.insert_union : ∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s t : Finset α), insert a s ∪ t = insert a (s ∪ t)
@LeftCommutative : {α : Sort u_1} → {β : Sort u_2} → (α → β → β) → Prop
@Fin.cons_zero : ∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (x : α 0) (p : (i : Fin n) → α i.succ), Fin.cons x p 0 = x
@Fin.cons_succ : ∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (x : α 0) (p : (i : Fin n) → α i.succ) (i : Fin n), Fin.cons x p i.succ = p i
@Fin.castSucc_lt_last : ∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
Fin.castSucc_injective : ∀ (n : ℕ), Function.Injective Fin.castSucc
@Nat.strong_induction_on : ∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n, p m) → p n) → p n
@List.get_mem : ∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n ∈ l
Complex.conj_im : ∀ (z : ℂ), ((starRingEnd ℂ) z).im = -z.im
```
Verified absent (errors in the tool log of this session): `Std.LeftCommutative` (unknown identifier; the class is the root `LeftCommutative`), `finRotate_castSucc` (unknown identifier), `Fin.sum_univ_get` (unknown constant). `finRotate_succ_apply` exists but is deprecated (`finRotate_apply` used).

## (d) Open issues and paper-delta candidates

Open issues: none; the pin is proved as written, all targets delivered (theorem, instance, build, axioms, pre-check).

- **T2086a** (carried from (a)): the proof of `lem: newPQ` (`3_5:1866-1886`) writes `(y2ussz)` with the sets `A_(i)` and the deletion of position `i` as if `i < n`; for `i = n` (cyclic, `σ_{n+1} = σ_1`) the deleted charge is `σ_n` and `σ_1` is replaced; the printed `σ_± = (σ_1 … σ_{i-1}, ±, σ_{i+2} …)` is the same loop only up to a cyclic rotation. Lean: `npqSg` lists the positions cyclically from `i + 1`.
- **T2086b**: the Lean labels `ι_α` are compositions of `ρ^(i+1) ∘ castSucc` (cyclically rotated, not increasing); the paper's `ι` is the order-preserving inclusion of a sub-collection. The pin only uses `a ∘ ι_α`, so the statement is unchanged.
- **T2086c** (supplements D105): `(WI_calL)` with `σ₁ = -` and cyclic invariance of `𝓛` are proved here as private `npq_loopL_ward`, `npq_loopL_rotate`; if another ticket needs them, a cleanup ticket should move them to `RBM3D/Induction/ConArgDet.lean` as public lemmas.
- Cleanup (not a paper delta): after the merge the owed line `RBM.Gauss.Sizes.STNewPQ` (`RBM3D/Test/Axioms.lean:120`) is superfluous (`stNewPQ_holds` discharges it); the cleanup ticket removes it, as for `GaussIBP`.
