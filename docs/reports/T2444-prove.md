Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 09:21:37 UTC 2026

### (i) Exponent table

Notation: `Θ_r := 𝖳_t(r ∧ ℓ) + W^{-D}` (target profile), `Φ_E := lwXE_phi … (2D)`, `ζ = baZetaVar … D₁`, `u = N^{τ/16}` (any `τ > 0`), `d = 3` at the instance.

| Row | Quantity | Value / constraint | Slack |
|---|---|---|---|
| R1 | floor exponent `D₁` (conj. 2) | `BAAuxGraph2_zetaSq_le` (`BAAuxGraph2.lean:950`): `ζ² ≤ (2(2ρ+1)^{2d}B + C₃²)K²Φ_E² + W^{-D₁}`. With `B = u⁴`, `K² ≤ u²`, `C₃² = 1+𝔡⁻² ≤ u⁴`, `3 ≤ u⁸`: the bracket times `K²` is `≤ 2u⁸` (the arithmetic of `BAAuxGraph2_num`, `:803`, without its `+1`). `Φ_E ≤ (1+2^{d-1})Θ ≤ u⁸Θ` (`lwXE_phi_le`, `LWXiExp.lean:210`). `W^{-D₁} ≤ W^{-2D} ≤ (W^{-D})² ≤ Θ²` iff `D₁ ≥ 2D` (`W ≥ 1`). So `ζ² ≤ (2u⁸·u¹⁶ + 1)Θ² ≤ (u¹⁶)²Θ² = (N^τ Θ)²` (`2u²⁴+1 ≤ u³²` from `3 ≤ u⁸`). | `D₁ ≥ 2D` suffices; zero slack at `D₁ = 2D`; `u²⁴·2+1 ≤ u³²` slack `u⁸ − 3 ≥ 0` |
| R2 | floor exponent `D₁` (conj. 3, Ward) | `BAAuxGraph2_floorL_le` (`:672`): `L^d W^{-D₁} ≤ W^{-d}` iff `D₁ ≥ 1/𝔠` (`N = W^dL^d ≤ W^{1/𝔠}`). Ward sum `≤ 2(2ρ+1)^{2d}(W^dη)⁻¹(1+A) + (2ρ+1)^dW^{-d} + L^dW^{-D₁}` (`baZeta_ward_sum`, `:461`), `A = 1`: `≤ 6(2ρ+1)^{2d}(W^dη)⁻¹` (as `BAZetaClaim` conj. 3, constant 6 = 4 + 1 + 1, with `η ≤ 1`). | `D₁ ≥ 1/𝔠`; at `𝔠 = 1/6`: `1/𝔠 = 6` |
| R3 | **threshold actually needed** | `max (2D) (1/𝔠) ≤ D₁` = the pin of the check file. T2435 E4's `D₁ ≥ D + d` (`T2435-prove.md:14`) is NOT needed: it is the condition `W^{-D₁} ≤ Φ_E²` (since `Φ_E² ≥ W^{-d-2D}`), i.e. absorbing the floor into the class; here the floor is kept additive and absorbed into `W^{-D}` of the target by R1. At `d=3, 𝔠=1/6`: `D+3 ≤ max(2D, 6)` for every `D>0`, so the pin is also at least `D+d` at this instance. | No larger threshold needed: **no stop** |
| R4 | window constant | `W^{-d} ≤ (1+𝔡⁻²)Φ_E(0)²` (`lwXE_window`, `:244`, from `0 ≤ g ≤ 𝔡⁻¹` = `Admissible`'s `WO`, `t<1`); `BAAuxGraph2_zetaSq_le` wants `C₃²`, so `C₃ = √(1+𝔡⁻²)`, `C₃² ≤ u⁴` | `𝔡 = 1/10`: `C₃² = 101` |
| R5 | profile comparison | `Φ_E ≤ (1+2^{d-1})Θ` needs `λ²/L² ≤ 1−t` (subtype of conj. 2, strict ⇒ `.le`), `t<1` (`ba_G_data`), `0 ≤ r ≤ L` (`BAAuxGraph2_zdistInf_le_L`), `0 ≤ ℓ` (`LWAssmExpgL` 4th conjunct), `2 ≤ d` | `d=3`: constant 5 |
| R6 | radius | `√ρ ≤ τ log N` eventually ∀τ ⇒ `ρ+1 ≤ N^τ` eventually ∀τ (`lwXE_rho_poly`, `:374`, copied) ⇒ `BAAuxGraph2_ev_poly` (`:884`) gives `c(aρ+b)^e ≤ N^{τ'}` | `ρ = log N`: `√ρ/ρ = (log N)^{-1/2} → 0` |
| R7 | conj. 3 entry law | `τ' = 𝔠ε₁/2`, `N^{𝔠ε₁/2}W^{-ε₁} ≤ W^{-ε₁/2} ≤ 1` (`BAAuxGraph2_pow_small`, `:926`), then `‖GM‖ ≤ 1` ⇒ `A = 1` in `baZeta_ward_sum` | `ε₁=1/20`, `𝔠=1/6`, `n=0`: `0.893 ≤ 0.917 ≤ 1` |
| R8 | `η ≤ 1`, `t<1`, admissible (replace `lwXE_etaT_le_one`, `lwXE_flow_facts`, `LWXiExp.lean:324,330`) | `hflow.1 : Admissible`; `t n < 1` and `η>0` from `ba_G_data` (`BA/GreenLDE.lean:55`: components 1 and 4, `ztOf_im`); `η ≤ 1` from `BAAuxGraph2_eta_le_one` (`:652`) | none needed |
| R9 | exponents of `u` | conj. 2 uses `u⁴` (loop), `u²` (`(2ρ+1)^{2d}`, `K²`), `u⁴` (`C₃²`), `u⁸` (`1+2^{d-1}`, `3 ≤ u⁸`); conj. 3 uses `6(2ρ+1)^{2d} ≤ N^τ` | `u = N^{τ/16}`, `N^τ = u¹⁶` |

Verdict (i): the floor threshold is `max (2D) (1/𝔠)`; it closes; no conjunct of `LWXiEgL` is unreachable from `baZetaVar`.

Argument (ii) replacements: see R8. (iii) C1: no hypothesis on `g` beyond `Admissible` (`WO`, used only for `0 ≤ g ≤ 𝔡⁻¹`), no `M = mI`; BA facts used are `ba_G_data`, `baZeta_ward_sum`, `BAAuxGraph2_*` only; `Φ_E` (`tailW`, `Defs/Tail.lean:52`), `sfT` (`Kernel/PropT.lean:469`) and `lwXE_phi_le` depend only on `(d, L, W, g, t, ℓ, D)`. `lwXE_phi` / `lwTail32` are public in `LWXiExp.lean` and imported.

(iv) Section and helper map (predicted lines; stop line 2000, central 600–1100)

| `LWXiExp.lean` | → `BAZetaExp.lean` | Source of helpers | Pred. lines |
|---|---|---|---|
| header, imports, §1 `:1-76` (`LWXiE`, `LWXiExpClaim`) | `LWXiEgL`, `LWXiEgL_bandFM` (`Iff.rfl`), `BAZetaExpClaim` | statement = check file `T2444_LWXiEgL`, `T2444_BAZetaExpClaim` | 90 |
| §2 `:77-117` `lwTail32` | imported, not twinned | `LWXiExp.lean:81` | 0 |
| §3 `:118-270` (`lwXE_phi_pos` … `_window`) | copied private, stem `BAZetaExp_` (`lwXE_phi` imported) | `LWXiExp.lean:124-270` | 150 |
| §4 `:272-534` | NOT copied except `lwXE_rho_poly` (`:374-401`) | `BAAuxGraph2_zdistInf_tri_real`, `_zdistInf_le_L`, `_zetaSq_nonneg`, `_zetaVar_sq`, `_pair_sum`, `_prec_of_imp`, `_ev_poly`, `_card_ball`, `_pow_small`, `_rpow_nat`, `_zetaSq_le`, `_eta_le_one`, `_floorL_le`, `BAAuxGraph2_num` (variant without `+1` re-derived in 8 lines) | 40 |
| `lwXE_core` `:535-558` | restated for `baZetaVar` with the floor term (R1) | `BAAuxGraph2_zetaSq_le` | 50 |
| §5 `:560-716` | `baZetaExpClaim_holds`; conj. 1 `baZetaVar_nonneg/_symm`, conj. 2 R1+R5, conj. 3 as `BAAuxGraph2B.lean:185-232` | R1-R9 | 200 |
| §6 `:718-783` | instances (`d=3`, `LWPinsBA §3` data); `Ψ0`, `ℓ ≡ 0` bound, `ρ0 = log N` re-derived (private there) | `BA/LWPinsBA.lean:66-90` | 90 |
| total | | | ≈ 620 (range 600–1100) vs stop line 2000: slack ≈ 1380 |

### (ii) One concrete nondegenerate instance

Data (`BA/LWPinsBA.lean` §3, `Defs/Sizes.lean:260`): `d=3`, `sz0`: `L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`, `N=(WL)^3`; `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`; `t ≡ 1/2` (`1/2 < BAflowT0`, `half_lt_t0`, `t0_sz0: 2/3 ≤ T₀`); `ε₀=1/10`, `Ψ=W^{-1/2}`, `ℓ ≡ 0`, `ε₁=1/20`, `ρ = log N`, `D ∈ {1/2,1,3,5}`, `D₁ = max(2D, 6)`. Stochastic inputs `STInitialGT2gL`, `LWLoopExpgL`, entry law stay hypotheses (ticket target 4). The sequences' eventual hypotheses (`Admissible`'s `WO`, `Bandwidth`, window) are checked at `n = 0, 1, 5, 50` (the deterministic ones hold at every `n`).

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2444/inst.py
n  L  W  lam  N | W>=N^c | W^(-d/2+dd)<=lam<=1/dd | lam^2/L^2<1-t | Psi window | ellT=min(max(lam/sqrt(1-t),1),L)
0 4 32 0.015625 2097152 | True | True | True 1.52587890625e-05 | True | 1 True
1 8 1024 0.000244140625 549755813888 | True | True | True 9.313225746154785e-10 | True | 1 True
5 24 248832 3.3489797668038406e-07 212986666247081951232 | True | True | True 1.9471641455662338e-16 | True | 1 True
50 204 11040808032 8.87971382186192e-13 11425969980610183329762199225554173952 | True | True | True 1.8946875614707235e-29 | True | 1 True
D  D1=max(2D,1/c)  L^dW^-D1  W^-d  ok | W^(-D1/2) W^-D ok  (n=0,5)
0 0.5 6.0 5.960464477539063e-08 3.0517578125e-05 True | 3.0517578125e-05 0.1767766952966369 True
0 1 6.0 5.960464477539063e-08 3.0517578125e-05 True | 3.0517578125e-05 0.03125 True
0 3 6 5.960464477539063e-08 3.0517578125e-05 True | 3.0517578125e-05 3.0517578125e-05 True
0 5 10 5.684341886080802e-14 3.0517578125e-05 True | 2.9802322387695312e-08 2.9802322387695312e-08 True
5 0.5 6.0 5.823664450220056e-29 6.490547151887447e-17 True | 6.490547151887447e-17 0.0020046884346862004 True
5 1 6.0 5.823664450220056e-29 6.490547151887447e-17 True | 6.490547151887447e-17 4.018775720164609e-06 True
5 3 6 5.823664450220056e-29 6.490547151887447e-17 True | 6.490547151887447e-17 6.490547151887447e-17 True
5 5 10 1.5190477394757894e-50 6.490547151887447e-17 True | 1.0482596010396101e-27 1.0482596010396101e-27 True
C3^2= 100.99999999999999   (lam^2+|1-t|)^-1 = 1.9990239141044412  C3^2*that >=1: True
1+2^(d-1)= 5
tau 0.1 need m=n+1 >= 115.224666573406 (log10 = 2.061545460076754 )
tau 0.01 need m=n+1 >= 8.385143645136323e+240 (log10 = 240.92351050686526 )
tau=1/10 loop: first n = 115 log N = 100.12071423167342
limit: sqrt(logN)/logN=(logN)^(-1/2)->0 as logN=3*log(128 (n+1)^6)->inf
entry n=0: 0.8934754536956512 <= 0.9170040432046712 <=1
Ward const: 2*(1+A)+1+1 with A=1: 6 <=6
```

Reading: at `n=0` (`L=4`, `W=32`, `N=2097152`, `λ=1/64`): `λ²/L² = 1.5e-5 < 1/2`, so the subtype of conj. 2 is nonempty at every `n`; window `32^{-3/2} ≤ 32^{-1/2} ≤ 32^{-1/10}`; `ellT = 1`, `ℓ=0 ≤ (log W)^{10}·1`; Ward floor `L³W^{-6} = 6.0e-8 ≤ W^{-3} = 3.1e-5` (`D₁=6`); `W^{-D₁/2} ≤ W^{-D}` for `D₁ = max(2D,6) ≥ 2D`.

External hypothesis (radius premise `√ρ ≤ τ log N` eventually ∀τ, TEAM §8 lesson 14): the limit is `√(log N)/log N = (log N)^{-1/2} → 0` with `log N_n = 3 log(128 (n+1)^6) → ∞`. It holds for every `τ` only from a `τ`-dependent `n` (`τ=1/10`: `n ≥ 115`; `τ=1/100`: `n+1 ≥ 8.4e240`). This is the quantifier "eventually for every `τ`", inherent to the premise (as in the band instance `LWXiExp.lean:737`), not a size choice of the witness; the deterministic hypotheses hold at `n = 0`.

### Verdicts

- Target 1 (`LWXiEgL`, `LWXiEgL_bandFM`): PASS (all three conjuncts' data reachable; bridge `Iff.rfl` as `LWXigL_bandFM`, `BAAuxGraph2.lean:1044`).
- Target 2 (`BAZetaExpClaim`, `baZetaExpClaim_holds`): PASS with threshold `max (2D) (1/𝔠) ≤ D₁` (R1-R3); no false pin, no missing input.
- Target 3 (helpers): PASS (map in (iv)); target 4 (instances): PASS (data above); target 5 (registry): nothing to check at the mathematics level.

## (b) Script output and map (stage 1b, rerun after the API usage limit; the first 1b committed 6586809, 590 lines)

**Verdict of (i), the threshold actually needed:** `D₁ ≥ max (2D) (1/𝔠)` closes; T2435's E4 `D + d` is not needed (the floor `W^{-D₁}` stays additive and is absorbed: `W^{-D₁} ≤ W^{-2D} = (W^{-D})² ≤ Θ²`, `BAZetaExp_core` and the `hfl` step of `baZetaExpClaim_holds`). No stop; no larger threshold; no conjunct of `LWXiEgL` unreachable from `baZetaVar`. Section (a) needs no correction: no `(a′)`.
**Lines against the stop line:** 591 vs 2000 (central 600-1100, estimate 620).  `wc -l` at the section commits: 590 (6586809), 591 (c8facc2, 617661a).

```
$ date -u
Mon Oct 12 09:44:14 UTC 2026
$ wc -l RBM3D/Graph/BAZetaExp.lean   # stop line 2000 per file (ticket); central 600-1100
     591 RBM3D/Graph/BAZetaExp.lean
$ git log --oneline main..t/T2444
617661a T2444: BAZetaExp: port source commit in the module docstring
c8facc2 T2444: BA-L L3c3b Graph/BAZetaExp: clean linter header, root import
6586809 T2444: BA-L L3c3b Graph/BAZetaExp: LWXiEgL, LWXiEgL_bandFM, BAZetaExpClaim, baZetaExpClaim_holds, instances
$ git diff --stat main...t/T2444
 RBM3D.lean                 |   1 +
 RBM3D/Graph/BAZetaExp.lean | 591 +++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 592 insertions(+)
$ git diff --stat main...t/T2444 -- RBM3D/Test/Axioms.lean | wc -l   # Test/Axioms.lean unchanged
       0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/BAZetaExp.lean
0
$ lake build RBM3D.Graph.BAZetaExp 2>&1 | grep -c "BAZetaExp.lean"   # warnings/errors located in this file
0
$ lake build RBM3D.Graph.BAZetaExp 2>&1 | tail -1
Build completed successfully (4003 jobs).
$ lake build   # full library, with the root import; runs #assert_rbm_axioms (09:42:47-09:43:58 UTC, tree = commit 617661a)
Build completed successfully (4268 jobs).
lake build  42.37s user 5.45s system 96% cpu 49.632 total
$ lake env lean ax.lean   # #print axioms of the public declarations
'RBM.Graph.LWXiEgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWXiEgL_bandFM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAZetaExpClaim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baZetaExpClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2444-check.lean   # on the branch: exit code and error lines
exit 0, error lines: 0
$ grep -rn "LWXiEgL\|BAZetaExpClaim\|baZetaExpClaim_holds" RBM3D RBM3D.lean --include="*.lean" | grep -v "^RBM3D/Graph/BAZetaExp.lean" | wc -l   # name clash, branch tree
       0
$ git grep -n "LWXiEgL\|BAZetaExp" main t/T2433 t/T2434 t/T2441 t/T2442 t/T2443 -- "RBM3D/*.lean" | wc -l
       0
$ grep -n "BAXi" RBM3D/Graph/BAZetaExp.lean | wc -l   # no new BAXi* name
       0
$ grep -rln "LWXiEgL\|BAZetaExpClaim" ../RBM1D/RBM1D ../RBM2D/RBM2D --include="*.lean" | wc -l   # sister projects (read-only grep)
       0
```

```
$ python3 -I stmt.py docs/tickets/checks/T2444-check.lean RBM3D/Graph/BAZetaExp.lean
def LWXiEgL vs check file (after renaming): IDENTICAL
def BAZetaExpClaim vs check file (after renaming): IDENTICAL

$ python3 -I ext.py RBM3D/Graph/BAZetaExp.lean "def LWXiEgL" "theorem LWXiEgL_bandFM" "def BAZetaExpClaim" "theorem baZetaExpClaim_holds"
BAZetaExp.lean:62-70
def LWXiEgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t ℓ : ℕ → ℝ) (D : ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    PrecL sz μ (U := fun n => {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ξ n p.1.1 p.1.2 ω)
      (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)
BAZetaExp.lean:74-76
theorem LWXiEgL_bandFM {d : ℕ} (sz : Sizes d) (E t ℓ : ℕ → ℝ) (D : ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) :
    LWXiEgL (bandFM sz E) (Sizes.seqP sz) t ℓ D ξ ↔ LWXiE sz E t ℓ D ξ := Iff.rfl
BAZetaExp.lean:83-94
def BAZetaExpClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
            ∀ D₁ : ℝ, max (2 * D) (1 / 𝔠) ≤ D₁ →
              LWXiEgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ℓ D (baZetaVar sz z t ρ D₁)
BAZetaExp.lean:325-325
theorem baZetaExpClaim_holds (d : ℕ) : BAZetaExpClaim d := by

$ python3 -I ext.py RBM3D/Graph/BAZetaExp.lean "example"   # the three instances, in file order
BAZetaExp.lean:564-565
example : ∀ n, Nonempty {_p : Zd 3 (sz0.L n) × Zd 3 (sz0.L n) // sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - 1 / 2} :=
  fun n => ⟨⟨(0, 0), BAZetaExp_strict n⟩⟩
BAZetaExp.lean:570-580
example (hI : STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 10) BAZetaExp_Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 0))
    (hent : PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ))))
    (D : ℝ) (hD : 0 < D) :
    LWXiEgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 0) D
      (baZetaVar sz0 zSeq (fun _ => 1 / 2) BAZetaExp_ρ0 (max (2 * D) 6)) :=
  baZetaExpClaim_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) BAZetaExp_Ψ0 (fun _ => 0)
    ⟨by norm_num, BAZetaExp_Ψ0_window, hI, fun _ => le_rfl, BAZetaExp_ell0, hL⟩ (1 / 20) (by norm_num) hent D hD
    BAZetaExp_ρ0 BAZetaExp_ρ0_nonneg BAZetaExp_ρ0_rad (max (2 * D) 6) (le_of_eq (by norm_num))
BAZetaExp.lean:583-585
example : LWXiEgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) (fun _ => 1 / 2) (fun _ => 0) 1 (fun _ _ _ _ => 1) ↔
    LWXiE sz0 (fun _ => 0) (fun _ => 1 / 2) (fun _ => 0) 1 (fun _ _ _ _ => 1) :=
  LWXiEgL_bandFM sz0 (fun _ => 0) (fun _ => 1 / 2) (fun _ => 0) 1 (fun _ _ _ _ => 1)
```

**Section map `LWXiExp.lean` -> `BAZetaExp.lean`** (target 3; ports are merged RBM3D text, last commit touching `LWXiExp.lean`: `eb56169`; nothing is ported from RBM1D/RBM2D, grep above is 0; so no diff-stat):

| `LWXiExp.lean` | `BAZetaExp.lean` | Treatment |
|---|---|---|
| §1 `:1-76` (`LWXiE`, `LWXiExpClaim`) | `:55-94` `LWXiEgL`, `LWXiEgL_bandFM` (`Iff.rfl`), `BAZetaExpClaim` | statements = check file up to the name (script diff above) |
| §2 `:77-117` `lwTail32` | none | imported, not twinned (`lwTail32` is cited only in the docstring) |
| §3 `:124-270` | `:95-221` `BAZetaExp_phi_pos/_phi_sq/_tailT_shift/_tailW_shift/_phi_cmp/_phi_le/_window` | copied private; `lwXE_phi` imported; `_window` constant `1+𝔡⁻²` |
| §4 `:272-534` | `:247-275` `BAZetaExp_rho_poly` (copy of `:374`), `:279-292` `BAZetaExp_num` | the rest replaced by L3c3a's public `BAAuxGraph2_*` (below) |
| `lwXE_core` `:535` | `:294-313` `BAZetaExp_core` | restated for `baZetaVar` with the additive floor, through `BAAuxGraph2_zetaSq_le` |
| §5 `:560-716` | `:316-498` `baZetaExpClaim_holds` | conj. 1 `baZetaVar_nonneg/_symm`; conj. 2 R1+R5; conj. 3 `baZeta_ward_sum`, `BAAuxGraph2_floorL_le` |
| §6 `:718-783` | `:500-584` instances | `d = 3` data of `BA/LWPinsBA.lean` §3; `Ψ0`, `ell0`, `ρ0` re-derived as private `BAZetaExp_*` |

Public helpers used instead of private copies (call count in the file): `BAAuxGraph2_ev_poly` 3, `_prec_of_imp` 2, `_zetaSq_le`, `_zdistInf_le_L`, `_rpow_nat`, `_zetaVar_sq`, `_pow_small`, `_floorL_le`, `_eta_le_one` 1 each; `baZeta_ward_sum`, `ba_G_data`, `baZetaVar_nonneg`, `baZetaVar_symm`.  Named in the ticket and not called here: `_zdistInf_tri_real`, `_zetaSq_nonneg`, `_pair_sum`, `_card_ball`, `_num` (the `+1`-free variant is `BAZetaExp_num`).
**Instances (target 4):** `baZetaExpClaim_holds` at `d = 3`, `sz0`, `zSeq`, `t ≡ 1/2`, `ℓ ≡ 0`, `ε₀ = 1/10`, `Ψ = W^{-1/2}`, `ε₁ = 1/20`, `ρ = log N`, every `D > 0`, `D₁ = max (2D) 6`; `Ψ0_window`, `ell0`, `ρ0_rad`, `strict` are proved in the file; the three hypotheses `STInitialGT2gL`, `LWLoopExpgL` and the entry law stay hypotheses of the example (other gates' stochastic inputs).  The subtype of conjunct 2 is nonempty at every `n` (example 1).  The instance of `LWXiEgL_bandFM` is example 3.  Registry (target 5): none; no public theorem has a `LWAssmExpgL`/`LWLoopExpgL` binder (only `BAZetaExpClaim`, a `Prop` def, and `example`s); `Test/Axioms.lean` unchanged, full `lake build` passes.


## (c) Verified Mathlib names (`#check` in `lake env lean` on the branch build; all resolve, no unknown identifier except the one listed absent)

`Real.sqrt_pos, Real.sq_sqrt, Real.sqrt_le_sqrt, Real.sqrt_le_iff, Real.sqrt_mul`; `Real.rpow_le_rpow_of_exponent_le, Real.rpow_natCast, Real.rpow_mul, Real.rpow_add, Real.rpow_def_of_pos, Real.one_le_rpow`
`Real.log_le_rpow_div, Real.log_nonneg, Real.tendsto_log_atTop, Real.one_le_exp, tendsto_rpow_atTop`; `one_le_pow₀, pow_le_pow_left₀, pow_le_pow_right₀, inv_anti₀, inv_le_one_of_one_le₀`
`div_le_div_iff₀, div_le_self, mul_one_div_cancel, le_mul_of_one_le_left, mul_le_of_le_one_left, one_le_mul_of_one_le_of_one_le`
Absent from Mathlib: `sqrt_add_le_add_sqrt` (it is `RBM.sqrt_add_le_add_sqrt`, `RBM3D/Kernel/PropT.lean:511`, used in `BAZetaExp_tailT_shift`).

## (d) Open issues and paper-delta candidates

- `T2444a` (threshold): the claim at BA carries the premise `D₁ ≥ max (2D) (1/𝔠)` on the floor exponent of `ζ`; the paper's `claim:xi` (`7_8:884-890`, stated with "we readily see", `(eq:xia1a2)` `7_8:882`) has no floor and no `D₁`.  Needed: `2D` to absorb the floor in `W^{-D}`, `1/𝔠` for the Ward floor `L^d W^{-D₁} ≤ W^{-d}`.  T2435 E4's `D + d` is not needed.
- `T2444b` (carrier form): `LWXiEgL` is `LWXiE` over `FlowFM sz` and a law `μ`; at BA the law is `seqP (sz.withLam 0)` while the subtype `λ²/L² < 1 - t` and the profile `𝖳_t` read `sz.lam` (as the merged generic pins `LWLoopExpgL`, `LWtermExpG`; the dispatcher's note says: not this row's question).
- `T2444c` (radius): the premise `√ρ ≤ τ log N` eventually for every `τ > 0` is the band's, verbatim; the instance `ρ = log N` meets it only from a `τ`-dependent `n` (`τ = 1/10`: `n ≥ 115`, section (a)), inherent in the quantifier.
- Inputs used as hypotheses only: `LWAssmExpgL` (via `LWLoopExpgL`), `STInitialGT2gL` (registered owed), the entry law `‖G_t - M‖_max ≺ W^{-ε₁}`.
- The first 1b stopped on the API usage limit with the file complete in substance (590 lines, committed); this rerun fixed the linter header and a docstring commit reference only (diff of the proof text: none).
