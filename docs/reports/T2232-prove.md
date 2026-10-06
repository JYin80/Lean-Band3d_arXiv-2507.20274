Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 00:25:58 UTC 2026

Base checked: worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2232` is at `b750bf3` (main moved past the ticket's `dc2d99b`; ExpWardI.lean absent, 0 hits for the new names).

### (i) Exponent table
Notation: `N = sz.size n = (W L)^d`, `η_u = (1-u) Im m(E_n)`, `ℓ_u = ellT L lam u`, `Bctl = W^{-d} Bparam d L lam u 0`, `K_c = C e^{|c|d/2} + 2C/d`.

| item | value / form | constraint | slack |
|---|---|---|---|
| `𝔠_d` (`STIngR6`) | `1/100` (any in `(0,1/100]`; no premise of `STIngR6` beyond `STReg5I`, `STExpAvgU` is used) | `0 < 𝔠_d ≤ 1/100` (`Step6Pins.lean:111`) | 0 at the top end; unused by the proof |
| flow `(κ,ε,𝔠,𝔡)` | `(1/10,1/10,1/6,1/10)` (`inst_ing6`) | `\|E_n\| ≤ 2-κ`, `N^{-1+ε} ≤ Im z_n`, `t ≤ lemT z_n < 1` | `2-κ-\|E\| = 1.4000`; `N^{-0.9}=5.6e-4 ≤ 1/64` (n=0); `lemT-t = 0.0465` (script below) |
| Ward factor `‖κ_u‖` | `(2 W^d η_u)^{-1}` (`B45_norm_kappa`) | sum of two terms each `≤ N^τ' Bctl²` | factor 2 of the difference cancels the `2` in `‖κ_u‖` exactly: `‖𝒫f_u‖ ≤ (W^dη_u)^{-1} N^{τ'} Bctl²` |
| `τ` split | `τ' = τ/2` for `STExpAvgU`; remaining `N^{τ/2}` absorbs the constants | `K ≤ N^{τ/2}` eventually | threshold `N ≥ K^{2/τ}`; asymptotic (`Prec`), not an instance constraint |
| `Im m(E_n)` | `≥ √(2κ)/2` (`st6_mE_im_ge`) | `(Im m)^{-1} ≤ 2/√(2κ)` | `1.0328 ≤ 4.4721` at `E=0.49998` |
| `K_c` (target 4) | `C e^{\|c\|d/2} + 2C/d` (`B45_vth_mid` at `m=1`: `(m:ℝ)d/2 = d/2`, `((d*1:ℕ):ℝ)=d`) | `1 ≤ d·1`, `3 ≤ L`, `0<g`, `0≤u<1`, window `1 ≤ g/√(1-u) ≤ L`, any real `c`; `K_c ≥ 0` needs `C ≥ 0` (`B45_C_nonneg`, from the mollifier, `0<lam`, `3≤L`) | `d=3, C=c=1`: `K_c = 5.1484` (illustrative `C,c`) |
| window (target 3) | `ℓ_u = lam/√(1-u) ∈ [1,L]` | `1-u ≤ 1-s ≤ lam²` gives `√(1-u) ≤ lam`; `1-u ≥ 1-t ≥ lam²/L² > 0` gives `lam ≤ L√(1-u)`; `0<lam` eventually (`st6_lam_pos`) | at `lam=1,L=4`: `1-t = lam²/L² = 1/16` (slack 0 at `t`), `1-s = 1/8 ≤ 1` (slack 7/8); `1-u>0` follows from `lam>0` (target 3 has no `u<1` premise, none needed) |
| scale | `(ℓ_u^d (1-u))^{-1} ≤ 2 Bparam d L lam u 0` (`B45_scale`, `2 ≤ d`, `1 ≤ L`, `0<lam`, `u<1`) | holds for every `u<1`; regime (i) only enters via the window | script: True at all tested `u` |
| first conjunct | `‖𝒫f(a₁) ϑ‖ ≤ N^{τ'} (W^dη)^{-1}Bctl² · K_c ℓ^{-d} ≤ N^{τ'} · (2K_c/Im m) Bctl³` | `(W^dη)^{-1}ℓ^{-d} = W^{-d}(Im m)^{-1}(ℓ^d(1-u))^{-1} ≤ 2(Im m)^{-1}Bctl` | `K1 = 2K_c/Im m = 10.63` |
| commutator | `B45_B4_le` at `m=1`: `2(m+1)=4`, `‖μs_i‖ = 1` (`norm_mSigma`, `\|E\|≤2`), `Π = (W^dη)^{-1}N^{τ'}Bctl²`, `vs = K_cℓ^{-d}` | `0≤u<1`, `3≤L`; `Θ^{(2)} = ThetaN … (fun i => mSigma E (σ i))` (`STthetaOp_eq_ThetaN`) | `≤ 8K_c/Im m · (1-u)^{-1}N^{τ'}Bctl³` |
| `∂_uϑ` term | `‖𝒫f(a₀) ∂_uϑ‖ ≤ Π · C(1-u)^{-1}ℓ^{-d}` (clause 4 of `STMollifierProps`, no `c`) | `0 ≤ u < 1` | `≤ 2C/Im m · (1-u)^{-1}N^{τ'}Bctl³`; total second-conjunct const `K2 = (8K_c+4C)/Im m = 46.67` |
| integrability | `‖Lloop^{(k)}‖ ≤ η_u^{-k}` (`norm_Lloop_le`), measurable (`walk_measurable_Lloop`), `seqP` probability measure (`isProbabilityMeasure_seqP`, `FineModel.lean:171`) | `\|E\|<2`, `u<1` | `∫` of the constant `STKloop` is itself |

Ward step at `m = 0` (target 1; checked against the Lean signatures): `B45_ward_fin` (`B45.lean:200`) at `m=0` needs `σ (Fin.last 1) = !σ 0`, which for `Bool` is `σ 0 ≠ σ 1`; `B45_sgnCons b σ : Fin 1 → Bool` is `Fin.cons b _`, equal to `fun _ => b`; `B45_Psum_snoc` (`:378`) at `m=0` turns `STPsum` into `Σ_{a'|a' 0=a₁} Σ_x A(snoc a' x)`; `STKloop` at one index is `mSigma E σ` (`lemDecCalEPrec_STKloop_one`, `LemDecCalEPrec.lean:370`). Integrating the pathwise identity (`∫` of `STLKtensor = Lloop - STKloop`; `STExpErr = ∫Lloop - STKloop`) gives exactly the right side of `expWI_Psum_eq`. Paper form `(eq:EPL-K)` `6_Step6_two_loop.tex:104-107` agrees.
`expWI_Psum_prec` (target 2) needs only `STExpAvgU` (the same `Prec` over `TimeIcc × Bool × Zd` with `‖∫Lloop - mSigma‖ ≤ N^τ Bctl²`), `hflow.1.2.2.1 : SizeTendsto` for `st6_prec_det_iff`, `s ≥ 0`, `t ≤ lemT z` (`st5_t_lt_one` gives `u<1`), `|lemE z| ≤ 2-κ`; no regime, no mollifier.

### (ii) One concrete nondegenerate instance
Data: `d=3`, `L=4`, `W_n=n+4`, `lam=1` (`szB`, `Step34Pins.lean:710`), `z_n = 1/2 + i/64` (`zB`, `:765`), `(s,t)=(7/8,15/16)`, `u ∈ [7/8,15/16]`, mollifier constants illustrative `C=c=1` (the consumer's positive family is `st6_mollifier_family`; existence from `stMollifierEx_holds`, merged). Sizes `n=0` (`N=4096`, `W=N^{1/6}` equality case) and `n=60` (`W=64`, `N=16777216`). Hypotheses checked numerically: `STFlow` margins, `STReg5I`, window of target 3, `B45_scale`, the chain `(W^dη)^{-1}ℓ^{-d} ≤ 2(Im m)^{-1}Bctl` of the first conjunct, `‖ϑ‖` bound of target 4, constants `K1, K2`. `msc z` solves `m²+zm+1=0`, `Im m>0`; `lemE = -2 Re m/|m|`, `lemT = |m|²` (`Semicircle.lean:190,193`); `Bparam d L g u 0 = (g²+|1-u|)^{-1} + (L^d|1-u|)^{-1}` (`Params.lean:36`, `(0+1)^{d-2}=1`).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2232/inst.py; echo exit=$?`
```
msc(z)= (-0.24798289121083006+0.9604669554693998j)  E=lemE=0.499984 t0=lemT=0.983992 ImmE=0.968248 sqrt(2k)/2=0.223607
n=0 N=4096 u=0.8750 l_u=2.8284 win=True scale=True chain=True Bctl=1.584e-02 vth_bd=0.2275 K1=10.63 K2=46.67
n=0 N=4096 u=0.9000 l_u=3.1623 win=True scale=True chain=True Bctl=1.665e-02 vth_bd=0.1628 K1=10.63 K2=46.67
n=0 N=4096 u=0.9375 l_u=4.0000 win=True scale=True chain=True Bctl=1.861e-02 vth_bd=0.0804 K1=10.63 K2=46.67
n=60 N=16777216 u=0.8750 l_u=2.8284 win=True scale=True chain=True Bctl=3.868e-06 vth_bd=0.2275 K1=10.63 K2=46.67
n=60 N=16777216 u=0.9000 l_u=3.1623 win=True scale=True chain=True Bctl=4.064e-06 vth_bd=0.1628 K1=10.63 K2=46.67
n=60 N=16777216 u=0.9375 l_u=4.0000 win=True scale=True chain=True Bctl=4.544e-06 vth_bd=0.0804 K1=10.63 K2=46.67
ALL OK True
absorption: N^(1/2) >= K2=46.67 needs N >= 2178.0 (illustrative tau=1); n=60 N=16777216
n=0: N^(-1+eps)=5.609e-04 <= Im z=0.0156 ; N^(1/6)=4.000 <= W=4 ; 2-kappa-|E|=1.4000 ; lemT-t=0.0465 ; Kc=5.1484
n=60: N^(-1+eps)=3.146e-07 <= Im z=0.0156 ; N^(1/6)=16.000 <= W=64 ; 2-kappa-|E|=1.4000 ; lemT-t=0.0465 ; Kc=5.1484
(Im m)^-1 = 1.0328 <= 2/sqrt(2k) = 4.4721
exit=0
```
External hypothesis of the mixed instance: `STExpAvgU szB (STflowE zB) (7/8) (15/16)` (`(res_ELK_n=1)` uniformly in `u`) stays a hypothesis of `inst_expWardI'_mixed`; it is another gate's merged conclusion (`stImproveExpAver_holds`, `ExpAvg.lean:879`, via `st6_expAvgU_of_pin`). Concrete limit computation: the premise reads `‖𝔼Lloop^{(1)} - m‖ ≤ N^τ Bctl²` for all large `n`; at `u=15/16`, `Bctl(n=60) = 4.544e-06` and `Bctl(n=0) = 1.861e-02` (script), `Bctl ≍ W^{-3}` since `lam=1` fixed, so `N^τ Bctl² ≍ W^{3τ-6} → 0` for every `τ < 2` along `W=n+4`, `N=(4W)^3`; the pathwise envelope is `‖Lloop^{(1)}‖ ≤ η_u^{-1} = 16/0.968 = 16.5 ≥ 1`, so the premise is a genuine decay statement, not vacuous; it is not checkable at one `n` and is not needed to be (conclusions are `Prec`, asymptotic). No `False`/`N=0`/empty index: index set `TimeIcc × {σ // σ0≠σ1} × Zd 3 4` has `2·64²` elements per time, interval `[7/8,15/16]` has positive length.

### Checklist lines (§29 / §45 O2) and route
- (1) time: `0 ≤ s < t ≤ lemT z`, `t<1` (`st5_t_lt_one`), `u ∈ [s_n,t_n]` including endpoints (window uses only `s_n ≤ u ≤ t_n`). (2) regime (i) used only for the window of target 3. (3) `L^d ≤ W^K` unused. (4) mollifier hypothesis eventual, `Prec` eventual, no `∀ n`. (5) conclusions deterministic, uniform in `u` via `st6_prec_det_iff` (no grid lift). (6) `0<lam` eventually (`st6_lam_pos`), `|E_n| ≤ 2-κ`, `SizeTendsto` from `hflow`; no new premise. (7) scale `N`; `(W^dη)^{-1}ℓ^{-d} ≤ 2(Im m)^{-1}Bctl` for every `u<1` (`B45_scale`).
- **(iii) Route decision: route U** (prove `expWI_core` for every real `C,c`, `stExpWardI_holds`, then `expWI_concl_prime`, `stExpWardI'_holds`). Criterion (a): target 4 is `B45_vth_mid` at `m=1` plus two cast simplifications (`(1:ℕ)` cast, `d*1 = d`), estimated ~15 lines (`≤ 100`). Criterion (b): `c` enters only through target 4 (clause 2 of `STMollifierProps`, inside `B45_vth_mid`); the first conjunct, the commutator and the `∂_uϑ` term use `K_c` only as a nonnegative constant and clause 4 (no `c`); `0<C` is replaced by `C ≥ 0` (`B45_C_nonneg`, eventual, `0<lam`, `3≤L`), so neither `0<C` nor `0<c` is used. (The inside of `B45_vth_mid` uses clause 3, differentiability, internally; merged, not this ticket's cost.) Both criteria hold.
- **(iv) Consumer check:** `STExpWardI' d := STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t)` has the same `STIngR6` premises as `STExpWardI` (`Step6Pins.lean:361`), so `H₃ 𝔠 sz z … hAvgU` of `Step6Kit.lean:974` typechecks with the primed premise and the merged `(hward C c' ϑ hϑ).1` (`Step6Kit.lean:1001`) becomes `(hward C c' hC hc' ϑ hϑ).1` against `STExpWardIConcl'` (`0<C`, `0<c` supplied by `st6_mollifier_family`, `:845`; S6-09's edit, not this ticket). `inst_expWardI'` is `inst_ing6_I STReg5I _ (stExpWardI'_holds 3) szB_reg5I` (`:525`); route U: `stExpWardI_holds 3` is `h` of `inst_expWardI` (`:607`) and `hWd` of `ST_step6_caseI_of_pins` (`:948`).
- **(v) Registry plan:** line numbers moved on `b750bf3`: owed line `STExpWardI` is at `RBM3D/Test/Axioms.lean:239` (not `:232`), `STExpIniIConcl'` at `:336`, last entry `locBad1]` at `:337`. Route U: delete `:239` by text; append one structural line for `STExpWardIConcl'` after `:336` (before `locBad1]`); `STExpWardI'` needs no line. Expected pre-check: `STExpWardI` absent from the owed ledger (owed count one less than at `b750bf3`), structural count one more.

### Verdicts
- Target 1 `expWI_Psum_eq`: PASS. Target 2 `expWI_Psum_prec`: PASS. Target 3 `expWI_window`: PASS. Target 4 `expWI_vth_le`: PASS.
- Target 5 `STExpWardIConcl'`, `STExpWardI'`, `expWI_core'`: PASS. Target 6 `stExpWardI'_holds`: PASS. Target 7 `expWI_core`, `expWI_concl_prime`, `stExpWardI_holds` (route U): PASS. Target 8 instances `inst_expWardI'`, `inst_expWardI'_mixed`, `inst_expWardI_holds`: PASS (hypothesis left: `STExpAvgU` at the instance, in the mixed one only).
- Overall: PASS.

## (b) Script output — Tue Oct  6 00:42:14 UTC 2026
Branch `t/T2232`, commit `37b7c91 Jun Yin <321276894+JYin80@users.noreply.github.com>`, base `b750bf3`; `main` is now `e64e4f0`. All commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2232`. Scratch scripts: `scratchpad/T2232/{axioms.lean,stmts.py,mkcheck.py,count.py,precheck.lean}`.

**Build** (`lake build RBM3D.Induction.ExpWardI 2>&1 | tail -2`):
```
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3869 jobs).
```
**Axioms** (`lake env lean axioms.lean | sed 's/depends on axioms: //'`; `axioms.lean` = `import RBM3D.Induction.ExpWardI` + `#print axioms` of the 16 names below):
```
'RBM.Gauss.Sizes.expWI_Psum_eq' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_Psum_prec' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_window' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_vth_le' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_core' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_concl_prime' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWI_core'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpWardI_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpWardI'_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardI'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardI_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardI'_mixed' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_Psum_eq' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_Psum_prec' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_window' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWI_vth_le' [propext, Classical.choice, Quot.sound]
```
**Statements** (`python3 stmts.py`, extracted from the file; theorems are shown up to `:=`; the instance statements are the compiled nonempty instances, all built above; `inst_expWardI'_mixed` exhibits `0 < C ∧ 0 < c`):
```
-- ExpWardI.lean:120
theorem expWI_Psum_eq {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (fun b => STExpErr sz n E u σ b) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (((∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a₁) ω ∂(sz.seqP)) - mSigma E true) -
          ((∫ ω, Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a₁) ω ∂(sz.seqP)) - mSigma E false)) := by
-- ExpWardI.lean:143
theorem expWI_Psum_prec {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hAvg : STExpAvgU sz (STflowE z) s t) :
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (STflowE z n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
      (fun n q _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (STflowE z n) (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 2) := by
-- ExpWardI.lean:184
theorem expWI_window {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (hR : STReg5I sz s t) (n : ℕ) (u : ℝ)
    (hsu : s n ≤ u) (hut : u ≤ t n) (hlam : 0 < sz.lam n) :
    1 ≤ sz.lam n / Real.sqrt (1 - u) ∧ sz.lam n / Real.sqrt (1 - u) ≤ ((sz.L n : ℕ) : ℝ) := by
-- ExpWardI.lean:206
theorem expWI_vth_le {d L : ℕ} [NeZero L] {g C c : ℝ} (ϑ : ℝ → (Fin 2 → Zd d L) → ℂ) (hd : 1 ≤ d) (hL : 3 ≤ L)
    (hg : 0 < g) (hϑ : STMollifierProps (d := d) g C c ϑ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hx1 : 1 ≤ g / Real.sqrt (1 - u)) (hxL : g / Real.sqrt (1 - u) ≤ (L : ℝ)) (a : Fin 2 → Zd d L) :
    ‖ϑ u a‖ ≤ (C * Real.exp (|c| * ((d : ℝ) / 2)) + 2 * C / (d : ℝ)) * ((ellT L g u) ^ d)⁻¹ := by
-- ExpWardI.lean:321
def STExpWardIConcl' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ (C c : ℝ), 0 < C → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
          STthetaOp sz n (E n) (q.1 : ℝ) q.2.1.1
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErr sz n (E n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)
-- ExpWardI.lean:339
def STExpWardI' (d : ℕ) : Prop :=
  STIngR6 d STReg5I (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t)
-- ExpWardI.lean:411
theorem expWI_core {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hAvg : STExpAvgU sz (STflowE z) s t) :
    STExpWardIConcl sz (STflowE z) s t := by
-- ExpWardI.lean:428
theorem expWI_concl_prime {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (h : STExpWardIConcl sz E s t) :
    STExpWardIConcl' sz E s t :=
-- ExpWardI.lean:433
theorem expWI_core' {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hAvg : STExpAvgU sz (STflowE z) s t) :
    STExpWardIConcl' sz (STflowE z) s t :=
-- ExpWardI.lean:441
theorem stExpWardI_holds (d : ℕ) : STExpWardI d := by
-- ExpWardI.lean:448
theorem stExpWardI'_holds (d : ℕ) : STExpWardI' d := by
-- ExpWardI.lean:469
theorem inst_expWardI' :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl' sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
-- ExpWardI.lean:476
theorem inst_expWardI_holds :
    InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) :=
-- ExpWardI.lean:483
theorem inst_expWardI'_mixed :
    STExpAvgU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ,
        (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧
        Prec szB (U := fun n => TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n ×
            {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (szB.L n)))
          (fun n q _ => ‖STPsum (d := 3) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
            ϑ n (q.1 : ℝ) q.2.2‖)
          (fun n q _ => (szB.Bctl n (q.1 : ℝ)) ^ 3) ∧
        Prec szB (U := fun n => TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n ×
            {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd 3 (szB.L n)))
          (fun n q _ =>
            ‖STQop (d := 3) (ϑ n) (q.1 : ℝ) (STthetaOp szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1
                (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b)) q.2.2 -
              STthetaOp szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1
                (STQop (d := 3) (ϑ n) (q.1 : ℝ) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b)) q.2.2‖ +
            ‖STPsum (d := 3) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
              deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
          (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (szB.Bctl n (q.1 : ℝ)) ^ 3) := by
-- ExpWardI.lean:512
theorem inst_expWI_Psum_eq :
    STPsum (d := 3) (fun b => STExpErr szB 0 0 (7 / 8) ![true, false] b) (0 : Zd 3 (szB.L 0)) =
      (2 * Complex.I * ((szB.W 0 : ℕ) : ℂ) ^ 3 * (etaT 0 (7 / 8) : ℂ))⁻¹ *
        (((∫ ω, Lloop szB 0 0 (7 / 8) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
            mSigma 0 true) -
          ((∫ ω, Lloop szB 0 0 (7 / 8) (fun _ : Fin 1 => false) (fun _ => (0 : Zd 3 (szB.L 0))) ω ∂(szB.seqP)) -
            mSigma 0 false)) :=
-- ExpWardI.lean:522
theorem inst_expWI_Psum_prec (hAvg : STExpAvgU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    Prec szB (U := fun n => TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n ×
        {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd 3 (szB.L n))
      (fun n q _ => ‖STPsum (d := 3) (fun b => STExpErr szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1 b) q.2.2‖)
      (fun n q _ => (((szB.W n : ℕ) : ℝ) ^ 3 * etaT (STflowE zB n) (q.1 : ℝ))⁻¹ * (szB.Bctl n (q.1 : ℝ)) ^ 2) :=
-- ExpWardI.lean:532
theorem inst_expWI_window (n : ℕ) (u : ℝ) (h1 : 7 / 8 ≤ u) (h2 : u ≤ 15 / 16) :
    1 ≤ szB.lam n / Real.sqrt (1 - u) ∧ szB.lam n / Real.sqrt (1 - u) ≤ ((szB.L n : ℕ) : ℝ) :=
-- ExpWardI.lean:538
theorem inst_expWI_vth_le :
    ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 4) → ℂ), 0 < C ∧ 0 < c ∧ STMollifierProps (d := 3) 1 C c ϑ ∧
      ∀ a, ‖ϑ (3 / 4) a‖ ≤
        (C * Real.exp (|c| * (((3 : ℕ) : ℝ) / 2)) + 2 * C / ((3 : ℕ) : ℝ)) * ((ellT 4 1 (3 / 4)) ^ 3)⁻¹ := by
```
**Check-file equality** (`python3 mkcheck.py && lake env lean checkeq.lean; echo exit=$?`; `checkeq.lean` = check imports + `import RBM3D.Induction.ExpWardI` + sections 1-2 + 9 `example : T2232Check.X := @X` (route U: all 9 pins) + 2 defeq `example`s (`STExpWardI'`, `STExpWardIConcl'`) + 3 section-3 `example : <stmt> := @inst_*`; then `grep -c error`, `grep -c '^example'`):
```
exit=0
0
14
```
**Name clash** (`git grep -nF <name> main -- RBM3D RBM3D.lean | grep -v Axioms.lean | wc -l`, new public names and the check namespace; hits on `main`):
```
expWI_:        0
STExpWardIConcl':        0
STExpWardI':        0
stExpWardI_holds:        0
stExpWardI'_holds:        0
inst_expWardI':        0
inst_expWardI_holds:        0
T2232Check:        0
```
**Registry** (`Axioms.lean` diff `b750bf3..t/T2232`, `count.py`, pre-check `precheck.lean` = `import RBM3D` + `import RBM3D.Induction.ExpWardI` + `#assert_rbm_axioms`, `lake env lean`, exit 0):
```
-   `RBM.Gauss.Sizes.STExpWardI, -- `6:104-107`, `6:121-131` Ward term, regime (i): S6-10; S6-01 (T2204, DECIS
+   `RBM.Gauss.Sizes.STExpWardIConcl', -- conclusion of the Ward term, regime (i), positive mollifier constant
base  (b750bf3): {'owedProps': 147, 'structuralProps': 84, 'borrowedProps': 2, 'refutedProps': 7}
branch (working tree): {'owedProps': 146, 'structuralProps': 85, 'borrowedProps': 2, 'refutedProps': 7}
STExpWardI as owed entry in branch: False
1:axiom audit: 6819 theorems, 2330 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
155:premises found by scanning: 129 (borrowed 1, owed 95, structural 27, refuted 6).
156:registry: 2 borrowed + 146 owed + 85 structural + 7 refuted; 111 registered premise(s) carry nothing yet: [RBM.Loop.
```
**Full `lake build`** with `import RBM3D.Induction.ExpWardI` added to `RBM3D.lean` after the last import line (uncommitted, reverted afterwards; the hub adds it at merge): exit 0.
```
2765:premises found by scanning: 129 (borrowed 1, owed 95, structural 27, refuted 6).
2766:registry: 2 borrowed + 146 owed + 85 structural + 7 refuted; 111 registered premise(s) carry nothing yet:
2878:Build completed successfully (4036 jobs).
```
**Scope** (`git diff main -- Step6Pins.lean Step6Kit.lean ExpIniI.lean | wc -l` = 0; `git diff --stat main...t/T2232`; `git merge-tree --write-tree main t/T2232`):
```
 RBM3D/Induction/ExpWardI.lean | 550 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   2 +-
 2 files changed, 551 insertions(+), 1 deletion(-)
4400f3e685f893c2d0026875967a20d0bcd3066b exit=0
```
Ports: none from RBM1D/RBM2D (`MLExpQ.lean` was not read, so no RBM2D diff-stat). Copies inside RBM3D: `expWI_scale` = first conjunct of `B45_scales` (`B45.lean:2246`) without its unused hypothesis `N⁻¹ ≤ 1-u`; `expWI_pw` = step `hsum` of `B45_Psum_LK_le` (`B45.lean:429`).

### Narrative (facts from the files and the tool log above)
- Route: U, as the preflight (iii) decided. Criterion (a): `expWI_vth_le` is 6 lines (statement and proof, `ExpWardI.lean:206-211`; 8 with its docstring) and the other size lemma `expWI_scale` is 27 lines (`:224-250`): far below 100. Criterion (b): `0 < C`, `0 < c` occur only in docstrings, in `STExpWardIConcl'`, in `expWI_concl_prime`, and in the instances (`grep -n "0 < C\|0 < c" ExpWardI.lean`); `expWI_core` and `stExpWardI_holds` take every real `C, c`; `C ≥ 0` comes from `B45_C_nonneg` (`ExpWardI.lean:377`); `c` enters only inside `B45_vth_mid` and the constant `e^{|c|d/2}`.
- File: 550 lines (ticket estimate 700 / 950 / 1250). §1 Ward step, §2 `expWI_Psum_prec`, §3 `expWI_window`, `expWI_vth_le`, §4 `expWI_scale`, `expWI_pt`, §5 vocabulary, constants, `expWI_step`, `expWI_core`, `expWI_core'`, the two pins, §6 instances.
- Ward step: `expWI_pw` is the pathwise identity (`B45_ward_fin` at `m = 0`, `B45_Psum_snoc`, `B45_sgnCons b σ = fun _ => b`); `expWI_Psum_eq` integrates it (`integral_finsetSum`, `integral_const_mul`, `integral_sub`; integrability from `norm_Lloop_le` and `walk_measurable_Lloop` on the probability measure; `∫ 𝒦 = 𝒦`; `𝒦^{(1)} = m` by `lemDecCalEPrec_STKloop_one`).
- `Prec` bookkeeping: `st6_prec_det_iff` in both directions. `expWI_Psum_prec` uses the same `τ` for both signs: the factor 2 of the difference cancels `‖κ‖ = (2W^dη)⁻¹` (`B45_norm_kappa`). `expWI_step` takes `N^{τ/2}` from it and absorbs the constants `K1 = 2ΓK_c`, `K2 = 2Γ(4K_c + C)`, `Γ = 2/√(2κ) ≥ (Im m)⁻¹` (`st6_mE_im_ge`), by `eventually_le_rpow` and `N^{τ/2} N^{τ/2} = N^τ`; `K1, K2` do not depend on `n, u, σ, a`.
- Commutator and `∂_uϑ`: `B45_B4_le` at `m = 1` with `STthetaOp = ThetaN` (`STthetaOp_eq_ThetaN`) and `‖m(σ_i)‖ = 1` (`norm_mSigma`); `∂_uϑ` by clause 4 of `STMollifierProps`; scale `(W^dη)⁻¹ℓ^{-d} ≤ 2Γ W^{-d}B` by `B45_scale` (`expWI_scale`).
- Section (a): no correction needed (no (a′)). Differences from its table: `K1, K2` of the proof use the constant `Γ` instead of `1/Im m` (the numbers 10.63 / 46.67 of (a) were illustrative); `expWI_Psum_prec` needs no `τ/2` split.
- Consumer check (§45 O2): `inst_expWardI'` is `inst_ing6_I STReg5I _ (stExpWardI'_holds 3) szB_reg5I`, equal to the check section-3 statement (compiled `example`); `STExpWardI' = T2232Check.STExpWardI'` by `rfl`, the same `STIngR6` premises as `STExpWardI`; `inst_expWardI_holds := inst_expWardI (stExpWardI_holds 3)` compiles: `stExpWardI_holds 3` is exactly the `h` of the merged `inst_expWardI` (`Step6Pins.lean:607`).
- Instances: every deterministic hypothesis is discharged at `szB`, `zB`, `(7/8, 15/16)` (`inst_expWardI'`, `inst_expWardI_holds`); what stays a hypothesis is `STExpAvgU` (in `inst_expWardI'_mixed`, `inst_expWI_Psum_prec`) and the stochastic premises of `InstIng6Concl`. `inst_expWI_Psum_eq` (`n = 0`, `E = 0`, `u = 7/8`, `σ = (+,-)`, `a₁ = 0`), `inst_expWI_window`, `inst_expWI_vth_le` (mollifier of `stMollifierEx_holds`, `u = 3/4`, `ℓ_u = 2`) have no hypothesis left except the stated reals.
- Full build: a first full `lake build` without the root import line exited 1 (`RBM3D.lean:275`: "1 premise(s) that no theorem of this development proves are in none of ...: [RBM.Gauss.Sizes.STExpWardI]"): the owed line is deleted and the module is not yet imported by the root. With the import line (run shown above) the build exits 0. The hub must add `import RBM3D.Induction.ExpWardI` in the same commit as the `Axioms.lean` change.
- Merge note (§20 (3)): line numbers on `b750bf3` differ from the ticket's: the owed `STExpWardI` line was `Axioms.lean:239`, `STExpIniIConcl'` `:336`; delete by text, append the structural line after `STExpIniIConcl'`, before `RBM.Endpoints.locBad1]`. `git merge-tree` against `main` `e64e4f0` is clean.

## (c) Verified Mathlib names (`#check` in `scratchpad/T2232/mathlib.lean`, all elaborate)
`MeasureTheory.Integrable.of_bound` (`hf`, `C`, bound a.e.) · `MeasureTheory.Integrable.sub` · `MeasureTheory.integrable_const` · `MeasureTheory.integral_sub` · `MeasureTheory.integral_finsetSum` · `MeasureTheory.integral_const_mul` · `Finset.sum_singleton` · `Real.sqrt_pos` · `Real.sqrt_le_left` (`0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`) · `Real.sq_sqrt` · `le_div_iff₀` · `div_le_iff₀` · `pow_le_pow_iff_left₀` · `inv_anti₀` · `Real.rpow_nonneg` · `Filter.Eventually.of_forall` · `Filter.Tendsto.eventually`.
Verified deprecated (warning in the same run): `MeasureTheory.integral_finset_sum` (use `integral_finsetSum`).

## (d) Open issues and paper-delta candidates
- No step needed a hypothesis the pin lacks (no `T2232b`).
- `T2232a` (statement difference, Lean stronger): `STExpWardI` (merged pin, `Step6Pins.lean:361`) is now proved (`stExpWardI_holds`) for every real mollifier constants `C, c`, including `c ≤ 0` (the paper's mollifier has `c > 0`, `Def:QtPt` `3_5:1214`); the primed `STExpWardIConcl'` (`0 < C`, `0 < c`) is its consequence `expWI_concl_prime`. Consequence for S6-09 (dispatcher decision, §73 (3)-(4)): the unsigned `stExpWardI_holds d` can already serve as `hWd` of the merged `ST_step6_caseI_of_pins` (`Step6Kit.lean:948`) and of `ST_step6_caseI_of_pins'` (`ExpIniI.lean:1128`).
- The two bounds `(eq:boundcommutator)` and `(eq:boundELKQ1)` are proved jointly as one `Prec` (their sum), as the merged conclusion states them; the paper states them separately (no loss).
