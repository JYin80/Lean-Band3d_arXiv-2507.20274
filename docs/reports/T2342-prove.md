Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 18:57:26 UTC 2026

Target: `lwtermExpN_of_LWterm : ∀ d, LWterm d → LWtermExpN d` (assembly only). Notation: `u = 1-t_n`, `g = lam n`, `B_m = Bparam d L g t m`, `Bctl = W^{-d} B_0`, `N = (W L)^d`.
Route (the ticket's, with one correction, row 5): apply `LWterm` to `Φ = LWPhiB sz d K t`, `K n = min ⌊ℓ n⌋₊ (L n)`, `c₀ = d`, at a **new** window pair `(ε₀', Ψ')` (not the `(ε₀, Ψ)` of `LWAssmExp`).

### (i) Exponent table

| # | quantity | value / choice | constraint | slack |
|---|---|---|---|---|
| 1 | `c₀` | `d` | `LWPhiB_psiAll`: `c₀ ≤ d` (`LWPsi.lean:417`); final loss must vanish for every `τ`, so `c₀ < d` is not allowed (fixed `W^{(d-c₀)/2}` loss) | 0 (equality) |
| 2 | `Λ` (`hg`) | `𝔡⁻¹` | eventually `0 < g ≤ Λ`: `(eq:WO)`: `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹`, `W^{..} > 0` | 0 |
| 3 | `ht` | `0 ≤ t ≤ 1` | hyp. `0 ≤ t n`, `t n ≤ lemT (z n) < 1` (`lemT_lt_one`, `Im z > 0` from `locDomain`: `N^{-1+ε} ≤ Im z`) | `t < 1` strictly |
| 4 | `c` (size data) | `c = min(2𝔡𝔠, ε)/2` (`ST_Bdata_holds`, `Step2Iterate.lean:1049`) | `Bctl n u ≤ N^{-c}` eventually, `u ∈ [0, t n]` (take `u = t n`) | at sz0: `c = 1/60` |
| 5 | `ε₀'` (`hup`) | `min(ε₀, d·c/2, d/2)` | `hup`: `W^{-d} B_0 ≤ W^{-2ε₀'}`; from row 4 and `W^d ≤ N` (`ST_Wpow_le_size`): `N^{-c} ≤ W^{-dc} ≤ W^{-2ε₀'}` needs `2ε₀' ≤ dc`; `LWWindow_max_Bctl` needs `ε₀' ≤ d/2`; `LWInit` part 1 at `ε₀'` needs `ε₀' ≤ ε₀` (`W^{-ε₀} ≤ W^{-ε₀'}`, `W ≥ 1`) | sz0: `ε₀' = 1/40`; `dc/2 = 1/40`, `ε₀ = 1/20` (slack 1/40); `d/2 = 3/2` |
| 6 | `Ψ'` | `max(W^{-d/2}, √Bctl)` | `LWWindow ε₀' Ψ'` by `LWWindow_max_Bctl` (needs row 5); `Ψ'² = max(W^{-d}, Bctl)` | — |
| 7 | `LWInit` part 2 at `Ψ'` | `STmaxLoop2 ≺ Ψ'²` from `LWLoopExp` at any `D>0` | `W^{-d} tailW_D(r) ≤ max(Bctl, W^{-d-D}) ≤ Ψ'²` since `tailT ≤ BparamR(s) ≤ BparamR(0) = B_0` (`tailT_antitone`/exp ≤ 1, `tailT_zero`); sup over `(a,b)` at `σ = ![false,true]` is inside `Prec` (union inside `P`) | no regime needed |
| 8 | `D'` for `LWLoop2` | `D' = max(D, 1/𝔠)` (sz0: 6) | `W^{-D'} ≤ L^{-d} ≤ B_m` (`B_m ≥ (L^d u)⁻¹ ≥ L^{-d}` as `0 < u ≤ 1`); `L^d ≤ N ≤ W^{1/𝔠}` from `Bandwidth 𝔠` (`N^𝔠 ≤ W`), so `W^{-1/𝔠} ≤ N^{-1} ≤ L^{-d}`; `D' ≥ D` not needed here (only for the conclusion at the given `D`) | sz0: `N = (WL)^3 ≤ W^6` iff `L ≤ W`; slack `W/L = 8(n+1)^4` |
| 9 | `LWLoop2` comparison | `W^{-d} tailW_{D'}(r) ≤ W^{-d} B_{min(r,K)}` (`r = |a-b|_∞ ∈ ℕ`, `r ≤ L`) | `tailT(s) ≤ BparamR(s)`, `s = min(r,ℓ)`; `⌊s⌋ = min(r, ⌊ℓ⌋) = min(r, K)` (since `r ≤ L`); `BparamR` antitone: `BparamR(s) ≤ BparamR(⌊s⌋) = B_{⌊s⌋}` (`BparamR_natCast`); `W^{-D'} ≤ B_m` row 8. Uses `tailT` directly: `tailW_regime2_bounds` needs `ℓ ≤ L`, but `LWAssmExp` allows `ℓ ≤ (log W)^{10} ℓ_t` | — |
| 10 | conclusion constant `C` | `C = e · 2^{d-2}` (sz0 `d=3`: `2e`) | regime `u ≤ g²/L²`: `ℓ_t = L` (`ellT_eq_of_le`), `s = min(r,ℓ) ≤ r ≤ L`, `tailT(s) ≥ e⁻¹ BparamR(s)` (`tailT_regime2_bounds`); `B_{⌊s⌋} ≤ 2^{d-2} BparamR(s)` since `s+1 ≤ 2(⌊s⌋+1)` and the zero-mode term has factor `≤ 1 ≤ 2^{d-2}`; `tailW_D ≥ tailT(s)`. Absorbed by `Prec` (`StochDomAt.const_mul_left`, `N → ∞` from `SizeTendsto`, `tendsto_size`) | numerically attained ratio `e` (ℓ = L) and `≤ 1.80` for `ℓ = 7.5`: far below `2e = 5.44` |
| 11 | `Φ(0)` | `Φ(0)² = W^{-d} B_0 = Bctl` (`Sizes.Bctl`, defn; `LWPsi_phi_eq` is private, restate) | `Φ(0)Φ(r)² = Bctl^{1/2}·W^{-d}B_{min(r,K)}` exactly the target's shape | — |
| 12 | regime subtype | index `{p // 1 - t n ≤ g²/L²}` | restrict `Prec` along the subtype inclusion (`StochDomAt.precomp_param`); pointwise facts of rows 9-10 needed only on `n` large (`g > 0`, `t < 1`, `1 ≤ L`: eventual) | no subsequence machinery |

Correction to the ticket (preflight, finding): the ticket says `hup` comes "from `LWWindow_max_Bctl` / `LWInit`". `LWWindow_max_Bctl` (`LWPsi.lean:344`) *consumes* `Bctl ≤ W^{-2ε₀}`, it does not give it; `LWWindow`, `LWInit` only give upper bounds (`Ψ ≤ W^{-ε₀}`, `STGM ≺ W^{-ε₀}`, `STmaxLoop2 ≺ Ψ²`), no lower bound on `Bctl` can be extracted (and `Bctl ≤ W^{-2ε₀}` is false at `ε₀ = d/2`, `t = 0`, `g² < L^{-d}`: `B_0 = (g²+1)⁻¹ + L^{-d} > 1`). The source is `ST_Bdata_holds` (data only: `Bctl ≤ N^{-c}`) with the new `ε₀'` of row 5. Import consequence: `ST_Bdata_holds`, `ST_one_sub_lemT` (`Step2Iterate.lean:1014`), `ST_flow_im_pos`, `ST_W_tendsto` (`Step2Events.lean:317, 235`) are in `RBM3D.Induction.Step2Iterate` / `Step2Events`, which are NOT in the import closure of `RBM3D.Graph.LWPins` (script below). Step2Iterate's closure contains `LWPins` and not `LWTermExpN` (file absent), so importing `RBM3D.Induction.Step2Iterate` is acyclic; the alternative is re-proving `ST_one_sub_lemT` (uses only `Defs/Semicircle`) and the `≤ N^{-c}` bound locally (~110 lines). The prover must choose one; the ticket's import line (`LWPins` only) must be read accordingly (paper-delta/ticket note `T2342a`: import list).

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, merged `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N = (WL)^3`), `z_n = 1/2 + i N^{-4/5}`, `t = tEnd = lemT z` (merged, `inst_LWtermExpN`), `ε₀ = 1/20`, `ℓ = ℓT tEnd = ellT`, `D = 1`; `n = 0, 5, 500` (`L = 4, 24, 2004`). Checked per `n` (150 digits, `msc` from `m² + z m + 1 = 0`, `Im m > 0`): the regime holds (`1-t ≤ g²/L²`, so the index set is nonempty), `ℓ_t = L`, `ℓ ≤ (log W)^{10} ℓ_t`, `0 < g ≤ 10`, `0 ≤ t ≤ 1`, `hup` at `ε₀' = 1/40` and the data bound `Bctl ≤ N^{-1/60}`, `W^{-D'} ≤ L^{-d}` with `D' = 6`, `LWInit` part 2 at `Ψ'` (`max_{r ≤ L} W^{-d} tailW_{D'}(r) ≤ Ψ'²`), the `LWLoop2` comparison (row 9) and the conclusion comparison (row 10) for **every integer `r ∈ [0, L]`**, `K = min ⌊ℓ⌋ L`.

    $ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2342/pre.py
    c=0.016667 eps0'=0.0250 D'=6.0
    n  L  W  | regime(1-t<=lam^2/L^2) ellT==L  l<=(logW)^10 ellT | lam<=10 | Bctl<=W^-2e0' | Bctl<=N^-c | W^-D'<=L^-d | loopmax<=Psi'^2 | LWLoop2 | ratio<=2e | maxratio
    0 4 32 | True True True | True | True True True True True True | 2.7183 | u=9.0512e-06 lam2/L2=1.5259e-05 Bctl=1.732e-01 W^-1/20=8.409e-01
    5 24 248832 | True True True | True | True True True True True True | 2.7183 | u=5.6407e-17 lam2/L2=1.9472e-16 Bctl=6.616e-04 W^-1/20=5.373e-01
    500 2004 1010040080080032 | True True True | True | True True True True True True | 2.7183 | u=1.1996e-44 lam2/L2=2.4310e-43 Bctl=1.004e-09 W^-1/20=1.777e-01

(`u` and `lam²/L²` agree with `T2040-prove.md` b.7 for `n = 0, 5, 500`: 9.0512e-06 / 1.5259e-05, etc. `W^{-1/20}` is `W^{-2ε₀'}`.) Floor/window cases (non-integer `ℓ`, `ℓ > L`; `n = 5`), the ratio `max_r W^{-d}B_{min(r,K)} / (W^{-d} tailW_D(r))`:

    $ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2342/pre2.py
    ell=7.5 K=7 max W^-d B_{min(r,K)} / (W^-d tailW_D(r)) = 1.7981  <= 2e = 5.4366
    ell=0.5 K=0 max W^-d B_{min(r,K)} / (W^-d tailW_D(r)) = 1.6304  <= 2e = 5.4366
    ell=72.9 K=24 max W^-d B_{min(r,K)} / (W^-d tailW_D(r)) = 2.7183  <= 2e = 5.4366

Import-closure check (rows 4-5 correction):

    $ cd /Users/junyin/Lean_proof/RBM3D && python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2342/clo.py
    Step2Events in LWPins closure False
    Step2Iterate in LWPins closure False
    LWPins in Step2Iterate closure True
    LWTermExpN file exists False

External hypotheses (limit computation, TEAM §8 lesson 14). The external inputs are `LWterm d` (conclusion `‖𝓔‖ ≺ η⁻¹ Φ(0) Φ(r)²`) and `LWLoopExp`/`LWInit` (premises). At `Φ = LWPhiB`: `Φ(0)Φ(r)² = Bctl^{1/2}·W^{-d}B_{min(r,K)}`, and the target is `Bctl^{1/2}·W^{-d} tailW_D(r)`; the ratio of the two is exactly `1` at `r = 0` (`tailW_D(0) = B_0`, `tailT_zero`) and tends to the constant `e` at `r = L` (`e^{-√(L/ℓ_t)} = e^{-1}`): table above, `2.7183` at `n = 0, 5, 500`, so the two sides have the same `n → ∞` limit behaviour and the constant is `n`-independent. The premise `LWLoopExp ⟹ LWLoop2` has margin `loopmax ≤ Ψ'²` (`Bctl` vs `max(W^{-3}, Bctl)`), checked above; no normalisation factor is lost (`Φ(r)² = W^{-d}B` is the same normalisation as `LWLoopExp`'s `W^{-d}`).

### Verdicts
- `lwtermExpN_of_LWterm`: **PASS** (hypothesis set satisfiable: instance above; all exponents close with the slacks in (i)). Notes for stage 1b: (1) `hup` via `ST_Bdata_holds` and a new `(ε₀', Ψ')`, row 5, not via `LWInit`; (2) import of `Step2Iterate` (or local re-proof), row 4-5 note; (3) use `tailT`, not `tailW_regime2_bounds`, rows 9-10 (`ℓ` may exceed `L`); (4) paper-delta candidate `T2342a`: the B class in place of `Ψ² = W^{-d}𝒯̃` (`7_8:20`), with the window pair re-chosen.

## (a′) Preflight corrections — Thu Oct  8 19:09:28 UTC 2026

No verdict changes. Two stage-1b choices differ from section (a); both are checked by the build below.
- Row 5/6 of (a) re-chose the window pair `(ε₀', Ψ')`. Not needed: `Ψ' = Ψ` (the given one) works, since `LWWindow ε₀ Ψ` and `LWInit ε₀ Ψ` give `LWWindow ε₁ Ψ`, `LWInit ε₁ Ψ` for `ε₁ ≤ ε₀` (`W ≥ 1`). Only `ε₁ = min(ε₀, d c/2)`, `c = min(2𝔡𝔠, ε)/2`, is new (the class `LWClass` needs `W^{-d}B_0 ≤ W^{-2ε₁}`).
- Import (note after row 5): `Step2Iterate` is NOT imported (it would make `LWtermExpN` -> `Step2Iterate` -> `Step2Events` -> `LWPins`; a later import of `LWtermExp` by `Step2Events`/`Step2Iterate` would be cyclic). The upper half of `ST_Bdata_holds` and `ST_one_sub_lemT` are copied (`Step2Iterate.lean:1014-1175`) as `lwN_Bctl_le`, `lwN_one_sub_lemT`; imports stay `RBM3D.Graph.LWPins` only.
- `D'` of row 8: `D' = 1/𝔠` (not `max(D, 1/𝔠)`); `LWLoopExp` holds for every `D > 0`, so `D' ≥ D` is not needed.

## (b) Script output

### Build
    $ cd /Users/junyin/Lean_proof/RBM3D-wt/T2342 && lake build RBM3D.Graph.LWTermExpN 2>&1 | tail -4
    warning: RBM3D/Graph/LWTermExpN.lean:22:100: This line exceeds the 100 character limit, please shorten it!
    Note: This linter can be disabled with `set_option linter.style.longLine false`
    Build completed successfully (3346 jobs).
    exit 0

### Hygiene and size
    $ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/LWTermExpN.lean; echo "grep exit $?"
    grep exit 1
    $ wc -l RBM3D/Graph/LWTermExpN.lean
         546 RBM3D/Graph/LWTermExpN.lean
    $ git diff --stat main...t/T2342
     RBM3D/Graph/LWTermExpN.lean | 546 ++++++++++++++++++++++++++++++++++++++++++++
     1 file changed, 546 insertions(+)

### Axioms
    $ lake env lean scratch/ax.lean   (import RBM3D.Graph.LWTermExpN; #print axioms ...)
    'RBM.Gauss.Sizes.lwtermExpN_of_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWTermExpNInst.inst_lwtermExpN_of_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.Sizes.lwN_Bctl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.lwN_B_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.lwN_tailW_le' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.lwN_prec_mono' depends on axioms: [propext, Classical.choice, Quot.sound]

### Target statement (extracted by script)
    $ sed -n 414p RBM3D/Graph/LWTermExpN.lean
    theorem lwtermExpN_of_LWterm (d : ℕ) (hLW : LWterm d) : LWtermExpN d := by
    $ sed -n 462,473p RBM3D/Graph/LWPins.lean     (the Prop `LWtermExpN`)
    def LWtermExpN (d : ℕ) : Prop :=
      3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
              ∀ D : ℝ, 0 < D →
                Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                    1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
                  (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
                  (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                    ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                      ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))
    $ sed -n 240,249p RBM3D/Graph/LWPins.lean     (the hypothesis Prop `LWterm`)
    def LWterm (d : ℕ) : Prop :=
      3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
              LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
              Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
                  Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

### Check-file equality
    $ cat scratch/chk.lean; lake env lean scratch/chk.lean; echo "exit $?"
    import RBM3D.Graph.LWPins
    import RBM3D.Graph.LWTermExpN
    namespace RBM.Gauss.Sizes.T2342Check
    def T2342_lwtermExpN_of_LWterm : Prop := ∀ d : ℕ, LWterm d → LWtermExpN d
    end RBM.Gauss.Sizes.T2342Check
    example : RBM.Gauss.Sizes.T2342Check.T2342_lwtermExpN_of_LWterm := RBM.Gauss.Sizes.lwtermExpN_of_LWterm
    exit 0

### Compiled nonempty instance (RBM3D/Graph/LWTermExpN.lean:529-546)
    namespace RBM.Gauss.LWTermExpNInst
    
    open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
      RBM.Gauss.LWInst
    
    /-- **`lem: EWGn2_N`, second regime, from `lem:LWterm`, instantiated** (`d = 3`, merged data). -/
    theorem inst_lwtermExpN_of_LWterm (h : LWterm 3)
        (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
        (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) (D : ℝ) (hD : 0 < D) :
        Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
            1 - tEnd n ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2})
          (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1.1 p.1.2 ω‖)
          (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * (sz0.Bctl n (tEnd n)) ^ (1 / 2 : ℝ) *
            ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tEnd n) (ℓT tEnd n)
              ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
      inst_LWtermExpN (lwtermExpN_of_LWterm 3 h) hI hL D hD
    
    end RBM.Gauss.LWTermExpNInst

### Registry pre-check (temporary uncommitted file: import RBM3D; import RBM3D.Graph.LWTermExpN; #assert_rbm_axioms)
    $ lake env lean scratch/reg.lean; echo "exit $?"
    axiom audit: 10245 theorems, 3037 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
    All within [propext,
     Classical.choice,
    ... (full output has 0 axioms in RBM; the line below is the owed-premise ledger entry of the target, still listed)
      RBM.Gauss.Sizes.LWtermExpN: 2 [no certificate]
    exit 0

### Name-clash grep (main worktree, RBM3D/ and RBM3D.lean, outside Probe/)
    $ cd /Users/junyin/Lean_proof/RBM3D && grep -rn "lwtermExpN_of_LWterm\|inst_lwtermExpN_of_LWterm\|LWTermExpNInst\|lwN_" RBM3D RBM3D.lean --include=*.lean | grep -v "Probe/" | wc -l
           0
    $ ls RBM3D/Graph/LWTermExpN.lean (main worktree)  ->  No such file or directory

### Ports (copies from the merged RBM3D main, not RBM1D/RBM2D)
    $ git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks log -1 --format=%h -- RBM3D/Induction/Step2Iterate.lean
    c5bbae7
    Copied: Step2Iterate.lean:1014-1046 (ST_one_sub_lemT), :1049-1175 upper half (ST_Bdata_holds), Step2Events.lean:242-251 (ST_size_rpow_neg_le). No RBM1D/RBM2D port; diff-stat not applicable.

Narrative. `lwtermExpN_of_LWterm` (RBM3D/Graph/LWTermExpN.lean:414) applies `LWterm d` to `Φ = LWPhiB sz d K t`,
`K n = ⌊ℓ n⌋ ∧ L n`, `c₀ = d`, `(C₁, C₂, C₃, Cc)` as in `LWPhiB_psiAll`, at `ε₁ = min(ε₀, d c/2)` and the given
`Ψ`. Pieces: (1) `LWClass` by `LWPhiB_psiAll`, its `hup` (`W^{-d}B_{t,0} ≤ W^{-2ε₁}`) from `lwN_Bctl_le`
(`Bctl ≤ N^{-c}`, copied size data) and `lwN_size_rpow_neg_le`; `hg` from `(eq:WO)`, `ht` from `t ≤ lemT z < 1`.
(2) `LWLoop2` for `Φ` from `LWLoopExp` at `D' = 1/𝔠` via `lwN_prec_mono` (constant 1) and
`lwN_tailW_le` (`wT ≤ B_{r∧K}` for `r ≤ L`, using `𝒯 ≤ B`, `B` antitone, `⌊r∧ℓ⌋ = r ∧ ⌊ℓ⌋`, `W^{-D'} ≤ L^{-d} ≤ B`,
with `W^{-1/𝔠} ≤ L^{-d}` from `Bandwidth 𝔠`, `lwN_Wneg_le`). (3) The conclusion of `LWterm` is restricted to the
regime subtype by `StochDomAt.precomp_param` and compared with `tailW` by `lwN_prec_mono` with constant
`e · 2^{d-2}` (`lwN_B_le_tail`: `tailT_regime2_bounds`, `ℓ_t = L`, `B_{⌊s⌋} ≤ 2^{d-2} B_s`); `Φ(0) = Bctl^{1/2}`
and `Φ(r)² = W^{-d} B_{r∧K}` exactly; `η_t⁻¹ ≥ 0` (`lwN_etaT_nonneg`). No subsequence machinery.
Hypotheses of the target: exactly those of `LWtermExpN` plus `LWterm d`. The instance keeps `LWterm 3`,
`LWInit`, `LWLoopExp` (other gates' pins) as hypotheses. `LWtermExpN` stays owed in the registry (LW-01 discharges `LWterm`).

## (c) Verified Mathlib names used (all compile in this file)
- `Monotone.map_min`, `Nat.floor_mono`, `Nat.floor_natCast`, `Nat.floor_le`, `Nat.lt_floor_add_one`
- `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_one`
- `Real.sqrt_eq_rpow`, `Real.sq_sqrt`, `Real.exp_le_one_iff`, `Real.exp_add`, `Real.rpow_add'`
- `inv_anti₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `mul_le_of_le_one_right`, `tendsto_rpow_atTop`, `tendsto_natCast_atTop_iff`
- Merged project names used: `LWPhiB_psiAll`, `LWPhiB`, `tailT_regime2_bounds`, `BparamR_antitone`, `BparamR_natCast`, `StochDomAt.of_subset`, `StochDomAt.precomp_param`, `eventually_le_rpow`, `Sizes.size_rpow_le_W_rpow`, `etaT`, `mE_im`, `lemT_lt_one`, `inst_LWtermExpN`.

## (d) Open issues and paper-delta candidates
- Finding on the ticket (also in (a)): `hup` does not come from `LWWindow_max_Bctl`/`LWInit`; it is the size data `Bctl ≤ N^{-c}` (deterministic, from `(eq:WO)`, `Im z ≥ N^{-1+ε}`, `W ≥ N^𝔠`) at the new window `ε₁`.
- T2342a: Lean applies `lem:LWterm` to the B class `Ψ² = W^{-d} B_{t,|a-b|∧K}` (`K = ⌊ℓ⌋ ∧ L`, `c₀ = d`) instead of `Ψ_t² = W^{-d} 𝒯̃` (`7_8:20`), with window `ε₁ = min(ε₀, d c/2)` (the paper's `ε₀` of `lem: EWGn2_N` is not assumed to satisfy `W^{-d}B_{t,0} ≤ W^{-2ε₀}`; it follows from the flow data only for the smaller `ε₁`), and `Ψ` unchanged.
- T2342b: the premise `(LW_assm)` for the B class is derived from `(LW_assm_exp)` at the single `D' = 1/𝔠` (paper: "for all `D`"), with `W^{-D'} ≤ L^{-d}` from `(Main_DEL_COND)`.
- T2342c: the constant between the B class and `tailW` in the regime is `e · 2^{d-2}`, absorbed by `≺` (paper: "immediate consequence").
- Duplication: `lwN_Bctl_le`, `lwN_one_sub_lemT`, `lwN_size_rpow_neg_le` (RBM3D/Graph/LWTermExpN.lean:176-374) copy merged `ST_*` lemmas (`Step2Iterate`/`Step2Events`) to keep imports at `LWPins`. A later ticket may move them to a shared lower file.
- Not done in this stage: the full `lake build` (hub, at merge, with the root import). The regime nonemptiness of the instance (`1 - t ≤ ĝ²/L²` at `n = 0, 5, 500`) is the preflight/`T2040-prove.md` b.7 numerical check, not a Lean proof here.
