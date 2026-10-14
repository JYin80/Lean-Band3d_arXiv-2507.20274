Prover model: claude-sonnet-5-5
## (a) Math preflight — Wed Oct 14 03:34:48 UTC 2026

Scope: T2501 row b (targets 9-12) on main db1932eb; rows a1 (`BA/Step5KerBA`), a2 (`BA/CltFlowBA`) are merged and read only.
Tuple: `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `d = 3` at instances. Script: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2501b/preflight.py` (Python, no Lean).

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠d` of `stStep5IVgL_holds`, `stWardIIgL_of`, `stDuhamelIgL_of`, `stDuhamelIIgL_of`, `stIniTermIIgL_of`, `stCltFarUgL_of` (feeds `stIniTermIgL_of`) | 1/100 (`refine ⟨1 / 100, …⟩`: Step5CasesGen:213, 291; DuhamelI2:1506, DuhamelII:847; IniTermIIGen:997; CltFarUGen:488) | `0 < 𝔠d ≤ 1/100` (`STIngR5gL`, Step5Gen:196) | 0 |
| 2 | `𝔠d` of `stEtermsMidgL_of` | `min(1/100, 1/(30 Cd))` (EtermsMid:375) | `≤ 1/100`; `𝔠d·Cd ≤ 1/30` (`hcC`, EtermsMid:379) | at `Cd = 1`: 𝔠d = 1/100, 𝔠d·Cd = 1/100 ≤ 1/30, slack 7/300 |
| 3 | `𝔠d` of case (i), (ii) | `min c₁ (min c₂ c₃)`, `min c₁ (min c₂ (min c₃ c₄))` (Step5CasesGen:349, 559) | `0 < 𝔠d ≤ 1/100` (`(min_le_left _ _).trans hc₁'`) | 0 (all cᵢ = 1/100 here) |
| 4 | `κm` (`Step5CasesGen_FlowFacts`) | `κm = κ` (`baStep5CasesGen_flowFacts`, SEforLnBA:152) | `0 < κm`, `κm ≤ Im m_n` (`EMn2BA_mF_data`) | 0; `T0 < 1` by `EMn2BA_T0_lt_one` |
| 5 | `Cd` of `STStep2ConclgL` | 1 (instances) | any `Cd > 0` | free |
| 6 | D3 modulus exponent | `N^(2·2+2) = N^6`: `hKs` of `stDuhamelIgL_of`/`stDuhamelIIgL_of` (DuhamelI2:1470-1520, DuhamelII:815-860) = `NQEndFlowGen_KLip … 2` (NQEndFlowGen:209-213, `2*k+2` at `k = 2`) | the two texts agree syntactically | 0 (target 5 of row a1, merged, is applied as is) |
| 7 | Ward constant (target 9) | `κ_W = (2 i W^d η)⁻¹`, `η = C.eta n u`; `N = (WL)^d = sz.size n` | `ZeroModeGen_WardCls` (ZeroModeGen:289) gives rotation + Ward with `κ_W` for `TL` and `TK`; linear in `T = TL − TK` | if `η = 0`: both `κ_W = 0` and `x/0 = 0` in ℂ, so the identity holds without an `η ≠ 0` hypothesis |
| 8 | regime windows (`Step5Pins:44-63`), `d = 3` | (i) `λ²/L² ≤ 1−t ≤ 1−s ≤ λ²`; (ii) `λ²/L³ ≤ 1−t ≤ 1−s ≤ λ²/L²`; (iv) `1−s ≤ λ²/L³`; `Mid` = `λ²/L³ ≤ 1−t ≤ 1−s ≤ λ²` | with `s < t ≤ T0`: `1−T0 ≤ 1−t < 1−s` | see (ii) below: empty at `sz0`; nonempty at data B |
| 9 | `T0 = Im m/(Im m + Im z)` (`BAt0`, MFixedPoint:279) | at `z = w − m_w`, `w = iy`: `T0 = Im m_w / y`, `Im m_w ∈ [y/(y² + λ²L³), 1/y]` (`BASelf_subord`, MFixedPoint:215-218) | `T0 ≥ t` | data B: see (ii) |
| 10 | `BAdom` / `Admissible` at data B (`ε, 𝔠, 𝔡`) = (1/2, 1/9, 1/10) | `κ ≤ Im m`, `N^{-1/2} ≤ Im z ≤ 1`; `W ≥ N^{1/9}` (⇐ `W ≥ L`); `W^{-3/2+1/10} ≤ λ ≤ 10` | (ii) below | tightest is `N₀^{-1/2} ≤ y − 1/y`: (i),(ii) 1.0e-3 ≤ 1.2e-3, (iv) 7.6e-4 ≤ 1.2e-3 |
| 11 | `(con_st_ind)` at constant `s < t` | `Bctl_n(t) = W_n^{-3}·Bp`, `Bp = (λ²+1−t)⁻¹ + (L³(1−t))⁻¹` (`Defs/Params.lean:36`) | `Bctl^{𝔠d} ≤ (1−t)/(1−s) < 1` for every `𝔠d > 0`, eventually | limit: `W_n → ∞` gives `Bctl_n → 0`; (ii) block D |
R1 (`A = (κ+1)/κ`), `Ck`, `δ₀`, `C₆`, `c` (FlowMod) are produced by rows a1/a2 and passed through unchanged; row b adds no constant after `(sz, z)`. No external input is used in row b.

### (ii) Concrete nondegenerate instance (numbers; script output pasted)
**Finding 1 (ticket correction).** At `(sz0, zSeq)` (`FlowPins:1111-1254`, `w = 6i/5`) `T0_n ≤ 25/36` (`Im m ≤ 1/Im w = 5/6`; `t0_sz0` gives only the lower bound `2/3`), so `1−s_n > 11/36`, while regimes (i), (ii), (iv) need `1−s_n ≤ 1.2e-4, 1.5e-5, 3.8e-6` (n = 0, then smaller): **the regime premise is `False` at `sz0`** for every `s < t ≤ T0`. The ticket's "below `t₀`, `half_lt_t0`" does not give a regime time. Block A below.
**Datum B** (the pattern of the compiled private datum `CltFlowBA_szI/_wI/_flowI`, `CltFlowBA.lean:597-690`, `BASelf_subord` at `w = (5003/5000) i`, `z_n ≡ w − m_w`): constant `L`, constant `lam`, `W_n = n + W₀`, `d = 3`; `BAm = m_w` by uniqueness; `s, t` constant. Rows: (i) is `CltFlowBA_szI` itself with `κ = 1/70`; (ii), (iv) change `(L, lam, κ, W₀)` only; all three use `(ε, 𝔠, 𝔡) = (1/2, 1/9, 1/10)`.
```
$ python3 -I .../T2501b/preflight.py
A. sz0: T0_n <= 25/36 = 0.6944444444444444  => need 1-s_n > 1-T0 >= 11/36 = 0.3055555555555556
   n=0: max(1-s) allowed (i)=0.000244 (ii)=1.53e-05 (iv)=3.81e-06  all < 11/36: True
   n=1: max(1-s) allowed (i)=5.96e-08 (ii)=9.31e-10 (iv)=1.16e-10  all < 11/36: True
   n=2: max(1-s) allowed (i)=4.59e-10 (ii)=3.19e-12 (iv)=2.66e-13  all < 11/36: True
B. (kappa,eps,c,d)=(kappa,1/2,1/9,1/10), z_n = w - m_w, T0 = Im m / Im w, Im m in [y/(y^2+lam^2 L^3), 1/y], Im z = y - Im m
   (i) L=4 lam=1 kappa=1/70 W_n=n+25 s=0 t=1/100: lam^2/L^2=0.0625 lam^2/L^3=0.01562 1-t=0.99 1-s=1
       Im m>=0.015394, T0>=0.015384, Im z in [0.0011996,0.98521], N0^-1/2=0.001; exact T0=0.4177>=t; OK
   (ii) L=4 lam=4 kappa=1/1100 W_n=n+25 s=1/2000 t=9/10000: lam^2/L^2=1 lam^2/L^3=0.25 1-t=0.9991 1-s=0.9995
       Im m>=0.00097619, T0>=0.00097561, Im z in [0.0011996,0.99962], N0^-1/2=0.001; exact T0=0.3201>=t; OK
   (iv) L=3 lam=6 kappa=1/1000 W_n=n+40 s=1/2000 t=1/1000: lam^2/L^2=4 lam^2/L^3=1.333 1-t=0.999 1-s=0.9995
       Im m>=0.0010284, T0>=0.0010277, Im z in [0.0011996,0.99957], N0^-1/2=0.000761; exact T0=0.4455>=t; OK
C. EtermsMid c_d = 1/100 ; c_d*Cd = 1/100 <= 1/30: True ; all other pins c_d = 1/100 <= 1/100
ALL OK
D. (con_st_ind): Bctl_n(t)^cd <= (1-t)/(1-s) iff W_n >= (Bp * r^(-1/cd))^(1/3); threshold n (log10) for cd = 1/100, 1/1000:
   (i) Bp=0.5183 ratio=0.99  cd=0.01: W_n>=10^0.05035 (n>=0); cd=0.001: W_n>=10^1.36 (n>=0)
   (ii) Bp=0.074466 ratio=0.9996  cd=0.01: W_n>=10^-0.3702 (n>=0); cd=0.001: W_n>=10^-0.3181 (n>=0)
   (iv) Bp=0.064102 ratio=0.9995  cd=0.01: W_n>=10^-0.3905 (n>=0); cd=0.001: W_n>=10^-0.3253 (n>=0)
```
Use of the data (the nine carrier predicates of `STIngR5gL`, stochastic pins of other gates, stay hypotheses of the examples, as in T2499 `Step5IIITargets_instPrem`; `STConStInd`, regime, `s < t ≤ T0`, `BAFlow` are discharged):
- target 11 (iv): data (iv). Target 10 `STDuhamelIgL`/`STIniTermIgL`/`STEtermsMidgL` and target 11 (i): data (i). Target 10 `STDuhamelIIgL`/`STIniTermIIgL`/`STWardIIgL`/`STEtermsMidgL` and target 11 (ii): data (ii). The `Mid` window (`λ²/L³ ≤ 1−t ≤ 1−s ≤ λ²`) follows from (i) and from (ii) (`λ²/L² ≤ λ²`).
- target 9: `baStep5CasesGen_wardIdent` at `(sz0, zSeq, flow_sz0)` (no regime needed), at `n = 0`, `u = 1/2`, `σ = (true, false)`, `a = 0`.
- (iv) is instance-trivial in `s` (`1−s ≤ 1 ≤ λ²/L³ = 4/3`) but `t ≤ T0` is genuine: `t = 1/1000 ≤ 0.0010277`.

### Verdict per target
- **9** (`step5CasesGen_wardIdent_of_wardCls`, `baStep5CasesGen_wardIdent`): **PASS**. Math: `X = L − K`; rotation `X⟨[s,!s],[c,a₁]⟩ = X⟨[!s,s],[a₁,c]⟩`, Ward at `!s`: `Σ_c X⟨[s,!s],[c,a₁]⟩ = κ_W (X_true(a₁) − X_false(a₁))` (`ZeroModeGen_WardFam`, ZeroModeGen:226-230; pattern `stWardII_identity`, WardII:143); `X_false = conj X_true` gives `X_true − X_false = 2i Im X_true`; `zeroModeSet {0}` is `L^{-d} Σ_c` (`wardII_zeroMode`); `κ_W · 2i · L^{-d} = (N η)⁻¹`. Conjugation sources, every `n`, no `g₀_n > 0`: `𝓛` is conjunct 2 of `baStep2_oneLoop` (Step2IterBA:83, `∀ n u a ω`); `𝒦` is clause 3 of `IsKLoopS` (`K t ⟨[s],[a]⟩ = PropSpin m s`, `PropSpin m false = conj m`) for `BAKsol`, which is `h.choose` once `∃ K, IsKLoopS`, given by `baKcac_isKLoopS` from `BAReal` (`BAflow_real`, every `n`) (FlowPins:283-288, KTreeRep:1674). Do **not** use conjunct 1 of `baStep2_oneLoop` or `baKsol_one` for this (eventual, needs `0 < g₀`, Step2IterBA:77).
- **10** (six pins): **PASS** (constants rows 1-2; premise discharges as the ticket's family table).
- **11** (`baStep5I/II/IV_holds`): **PASS** (rows 1-3; (iv) strong estimate void since `1−t < 1−s ≤ λ²/L^d ≤ λ² ≤ 1−t` is impossible, Step5CasesGen:329).
- **12** (instances): **PASS with correction**: use datum B (not `sz0`), Finding 1.

Notes for 1b (inputs, not defects of the targets):
- `hmn`, `hSr` are `private` in `Step5KerBA` (`Step5KerBA_hmn` :535, `Step5KerBA_hSr` :541); row b copies them as `private` `Step5CasesBA_*` (the ticket's target 6 says private).
- Datum B is `private` in `CltFlowBA` (:597-690); row b ports it, generalised over `(L, lam, κ, W₀)`, with citation of `CltFlowBA.lean:597-690` and commit `db1932eb`.
- The ticket's "(iv) with every premise discharged" is read as T2499: only the nine stochastic pins stay hypotheses.

## (a′) Preflight corrections — Wed Oct 14 03:51:30 UTC 2026

1. Data (iv) of (a) uses `s = 1/2000`, `t = 1/1000` with `t ≤ T₀` from the exact `T₀ = 0.0010277`. The Lean route has only `TwistStep2_T0_ge` (`T₀ ≥ κ/(κ+1) = 1/1001 < 1/1000`), so Lean uses `s ≡ 0`, `t ≡ 1/2000` there; for (ii) `t = 9/10000 ≤ 1/1101`; for (i) `t = 1/100 ≤ 1/71`. No verdict changes (all (L, W₀, lam, κ) as in (a) rows B).
2. Data (i), (ii), (iv) all take `s ≡ 0` (the regime windows need only `1 - s ≤ …`, true at `s = 0`; (iv): `1 - 0 ≤ 36/27`).

## (b) Script output

Branch `t/T2501b`, commit `df731125` (base `db1932eb`), file `RBM3D/BA/Step5CasesBA.lean`, full build and scratch checks ran on this commit between 03:49:35 and 03:50:45 UTC; the module build below at 03:51:51-03:51:53 UTC (`date -u` in the tool log).

```
$ lake build RBM3D.BA.Step5CasesBA | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4214 jobs).

$ lake build 2>&1 | tail -1 ; grep -E '^registry:|axiom audit' (full library, with the registry edit)
Build completed successfully (4381 jobs).
registry: 2 borrowed + 109 owed + 123 structural + 7 refuted + 18 superseded; 137 register
info: RBM3D.lean:611:0: axiom audit: 14993 theorems, 4631 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

**wc -l (stop rule, row b stop line 900 per Amend 1):**
```
$ wc -l RBM3D/BA/Step5CasesBA.lean
     556 RBM3D/BA/Step5CasesBA.lean
```

**Axioms** (scratch `pins.lean` = the ticket check plus `#print axioms`, uncommitted):
```
$ lake env lean pins.lean | grep -c error  -> 0
'RBM.BA.step5CasesGen_wardIdent_of_wardCls' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5CasesGen_wardIdent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTEtermsMidgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTDuhamelIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTDuhamelIIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIniTermIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIniTermIIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTWardIIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5I_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Pin match** (scratch, uncommitted, appended to a copy of `docs/tickets/checks/T2501-check.lean`; exit 0, 0 error lines): `example : T2501_WardIdentBA := fun d sz κ ε 𝔠 𝔡 z => baStep5CasesGen_wardIdent d sz κ ε 𝔠 𝔡 z`; the same for `T2501_EtermsMidBA := baSTEtermsMidgL_holds`, `_DuhamelIBA := baSTDuhamelIgL_holds`, `_DuhamelIIBA := baSTDuhamelIIgL_holds`, `_IniTermIBA := baSTIniTermIgL_holds`, `_IniTermIIBA := baSTIniTermIIgL_holds`, `_WardIIBA := baSTWardIIgL_holds`, `_Step5IBA := baStep5I_holds`, `_Step5IIBA := baStep5II_holds`, `_Step5IVBA := baStep5IV_holds`; and the bridge shape example of the check (`step5CasesGen_wardIdent_of_wardCls sz C`). Rows a1/a2 pins also re-checked against `baIniTermGen_kerFacts`, `baStep5KerGen_thDecay`, `baIniTermGen_cltFlow`, `baEtermsMid_newKLKL`, `baLemDecCalELipG_flowMod`, `baKLip_two`, `baNewKLKLgL'`: exit 0.

**Target statements** (extracted by script from the file, whitespace collapsed):
```
theorem step5CasesGen_wardIdent_of_wardCls {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (hW : ZeroModeGen_WardCls sz C) (hc : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)), C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω = (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω) ∧ C.K n u (fun _ : Fin 1 => false) (fun _ => a) = (starRingEnd ℂ) (C.K n u (fun _ : Fin 1 => true) (fun _ => a))) : Step5CasesGen_WardIdent C

theorem baStep5CasesGen_wardIdent (d : ℕ) : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → Step5CasesGen_WardIdent (baFMz sz z)

theorem baSTEtermsMidgL_holds : ∀ d : ℕ, 3 ≤ d → STEtermsMidgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baSTDuhamelIgL_holds : ∀ d : ℕ, 3 ≤ d → STDuhamelIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baSTDuhamelIIgL_holds : ∀ d : ℕ, 3 ≤ d → STDuhamelIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baSTIniTermIgL_holds : ∀ d : ℕ, 3 ≤ d → STIniTermIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baSTIniTermIIgL_holds : ∀ d : ℕ, 3 ≤ d → STIniTermIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baSTWardIIgL_holds : ∀ d : ℕ, 3 ≤ d → STWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baStep5I_holds : ∀ d : ℕ, 3 ≤ d → STStep5IgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baStep5II_holds : ∀ d : ℕ, 3 ≤ d → STStep5IIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

theorem baStep5IV_holds : ∀ d : ℕ, STStep5IVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
```

**Compiled nonempty instances** (`d = 3`; `grep -n '^example'`):
```
472:example : Step5CasesGen_WardIdent (baFMz sz0 zSeq) :=
476:example (ω : sz0.SeqΩ) :
490:example (hp : Step5CasesBA_prem Step5CasesBA_szIV Step5CasesBA_zIV (fun _ => 0) (fun _ => 1 / 2000)) :
497:example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
502:example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
509:example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
514:example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
521:example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
526:example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
535:example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
542:example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
547:example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
```

Data (private, `Step5CasesBA_sz/_z/_flow/_datum`; `L ≡ L`, `W_n = n + W₀`, `lam ≡ lam`, `w = (5003/5000) i`, `z_n ≡ w - BAmSubord 3 L lam w`, `(ε, 𝔠, 𝔡) = (1/2, 1/9, 1/10)`, `s ≡ 0`):
| case | (L, W₀, lam) | κ | t | regime window (norm_num) | `t ≤ T₀` |
|---|---|---|---|---|---|
| (i) | (4, 25, 1) | 1/70 | 1/100 | `1/16 ≤ 0.99`, `1 ≤ 1` | `≤ κ/(κ+1) = 1/71` |
| (ii) | (4, 25, 4) | 1/1100 | 9/10000 | `1/4 ≤ 0.9991`, `1 ≤ 16/16`; Mid too | `≤ 1/1101` |
| (iv) | (3, 40, 6) | 1/1000 | 1/2000 | `1 ≤ 36/27` | `≤ 1/1001` |
Discharged in every example: `BAFlow` (`Step5CasesBA_flow`, lines 297-372, proved once; each datum is one call of `Step5CasesBA_datum`), `0 ≤ s < t ≤ T₀`, the regime, `(con_st_ind)` at every `𝔠d > 0` (`Step5CasesBA_conStInd`). Hypotheses of the examples: only `Step5CasesBA_prem` = the nine carrier predicates of `STIngR5gL` (`STKboundgL, STKwardgL, STLKgL, STDecaygL, STDecayStronggL, STStep1LoopgL, STStep2ConclgL, STLmaxUgL, STLKUgL`), other gates' pins, as `Step5IIITargets_instPrem` (T2499). Target 9: `baStep5CasesGen_wardIdent` at `(sz0, zSeq, flow_sz0)` as a class and at `n = 0`, `u = 1/2`, `σ = (true, false)`, `a = 0`, every `ω`, no hypothesis left.

**Greps** (hypothesis rules; 0 hits each):
```

$ C1: grep -nE 'BAK_le_small|BAMB_upper_small|Mbound_AO|W\^\(-eps|BAm_im_lower_window|\|E\||norm_mE|mSigma|SB d|E2Hyp|STGridRepNgL' F
(0 hits)
$ X1-C4: grep -nE '^(noncomputable )?(def|abbrev|structure) ' F
(0 hits)
$ T24 text: grep -nE 'T24[0-9]*_' F
(0 hits)
$ hygiene: grep -nE 'sorry|admit|native_decide|^axiom' F
(0 hits)
$ local copies of the families: grep -nE '^(theorem|def|abbrev|structure) .*(IniTermGen_KerFacts|IniTermGen_CltFlow|EtermsMid_NewKLKL|LemDecCalELipG_FlowMod|NQEndFlowGen_KLip|ZeroModeGen_WardCls|STThPropsg|STKpropsg|STIngR5gL)' F
83:theorem step5CasesGen_wardIdent_of_wardCls {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (hW : ZeroModeGen_WardCls sz C)
(the one hit is the bridge, which takes `ZeroModeGen_WardCls` as a hypothesis; not a local copy of the class)
$ grep -c 'withLam' F ; grep -n 'withLam' F | grep -vc 'seqP (.*withLam 0)'
52
0   (52 lines contain `withLam`; 0 of them are outside `seqP (… .withLam 0)`)
```

**Name-clash grep** (new public names; hits outside the new file; RBM1D/RBM2D hits):
```

step5CasesGen_wardIdent_of_wardCls: outside = 0; RBM1D/RBM2D = 0
baStep5CasesGen_wardIdent: outside = 0; RBM1D/RBM2D = 0
baSTEtermsMidgL_holds: outside = RBM3D/Test/Axioms.lean:203:   -- T2462 (BA-U U4s1a, DECISION; RBM1D/RBM2D = 0
baSTDuhamelIgL_holds: outside = RBM3D/Test/Axioms.lean:203:   -- T2462 (BA-U U4s1a, DECISION; RBM1D/RBM2D = 0
baSTDuhamelIIgL_holds: outside = RBM3D/Test/Axioms.lean:203:   -- T2462 (BA-U U4s1a, DECISION; RBM1D/RBM2D = 0
baSTIniTermIgL_holds: outside = RBM3D/Test/Axioms.lean:203:   -- T2462 (BA-U U4s1a, DECISION; RBM1D/RBM2D = 0
baSTIniTermIIgL_holds: outside = RBM3D/Test/Axioms.lean:203:   -- T2462 (BA-U U4s1a, DECISION; RBM1D/RBM2D = 0
baSTWardIIgL_holds: outside = 0; RBM1D/RBM2D = 0
baStep5I_holds: outside = RBM3D/Test/Axioms.lean:204:   `RBM.BA.STStep5ConclgL, -- uni; RBM1D/RBM2D = 0
baStep5II_holds: outside = RBM3D/Test/Axioms.lean:204:   `RBM.BA.STStep5ConclgL, -- uni; RBM1D/RBM2D = 0
baStep5IV_holds: outside = RBM3D/Test/Axioms.lean:204:   `RBM.BA.STStep5ConclgL, -- uni; RBM1D/RBM2D = 0
```
(The `Test/Axioms.lean:203-204` hits are the registry comments added by this ticket.)

**Diff and registry:**
```
$ git diff --stat main...t/T2501b
 RBM3D.lean                 |   1 +
 RBM3D/BA/Step5CasesBA.lean | 556 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   9 +-
 3 files changed, 559 insertions(+), 7 deletions(-)
$ git diff --stat main...HEAD -- RBM3D/Chain RBM3D/Induction RBM3D/Evolution RBM3D/Graph RBM3D/BA ':(exclude)RBM3D/BA/Step5CasesBA.lean'
(empty: 0 chars)
$ importers of RBM3D.BA.Step5CasesBA
RBM3D.lean:608:import RBM3D.BA.Step5CasesBA
$ git diff -U0 main...HEAD -- RBM3D/Test/Axioms.lean | cut -c1-105
@@ -203,7 +203,2 @@ def owedProps : List Name :=
-   -- T2462 (BA-U U4s1a, DECISIONS §270): the generic Step-5 pins that the public theorems of `RBM3D/Cha
-   `RBM.BA.STStep5ConclgL, -- uniform Step-5 conclusion `STGdecayWgL … 0 ∧ STDecayStrongUgL` over a carr
-   `RBM.BA.STEtermsMidgL, -- `(S5WG+M000)`, `(S5WG+M)` over a carrier tuple (`Chain/Step5Gen.lean:234`):
-   `RBM.BA.STDuhamelIgL, -- the integrated hierarchy of case (i) over a carrier tuple (`Chain/Step5Gen.l
-   `RBM.BA.STDuhamelIIgL, -- the integrated hierarchy of case (ii) over a carrier tuple (`Chain/Step5Gen
-   `RBM.BA.STIniTermIgL, -- the initial term of case (i) over a carrier tuple (`Chain/Step5Gen.lean:239`
-   `RBM.BA.STIniTermIIgL, -- the initial terms of case (ii) over a carrier tuple (`Chain/Step5Gen.lean:2
+   -- T2462 (BA-U U4s1a, DECISIONS §270): the generic Step-5 pins that the public theorems of `RBM3D/Cha
+   `RBM.BA.STStep5ConclgL, -- uniform Step-5 conclusion `STGdecayWgL … 0 ∧ STDecayStrongUgL` over a carr
owedProps.length before (#eval, main oleans) = 114; after: `registry: ... 109 owed` (full build above). Five names deleted: STEtermsMidgL, STDuhamelIgL, STDuhamelIIgL, STIniTermIgL, STIniTermIIgL; `STStep5ConclgL` stays with the new owner text.
```

**Ports** (all from RBM3D merged files, none from RBM1D/RBM2D; no `diff --stat` needed): `Step5CasesBA_zeroMode` = `wardII_zeroMode` (`Induction/WardII.lean:131`); `Step5CasesBA_hmn`, `_hSr` = `Step5KerBA_hmn`, `_hSr` (`BA/Step5KerBA.lean:535`, `:541`); `Step5CasesBA_flow` = `CltFlowBA_flowI` generalised (`BA/CltFlowBA.lean:610-681`, commit `db1932eb`); `Step5CasesBA_conStInd` = `s1Setup_conStInd_const` (`Induction/Step1Setup.lean:1226`). `open private SEforLnBA_Ksol_isKLoopS from RBM3D.BA.SEforLnBA` (the pattern of `Step5KerBA`; no merged file changed).

**Narrative** (routes; every target applies a merged result):
- Target 9 bridge `step5CasesGen_wardIdent_of_wardCls`: `ZeroModeGen_WardCls` gives `TL`, `TK` with rotation and Ward at `κ_W = (2 i W^d η)⁻¹`; `Σ_c X⟨[s,!s],[c,a₁]⟩ = κ_W (X_true - X_false)` (rotation then Ward at `!s`, `Step5CasesBA_sum_ward`); the conjugation `X_false = conj X_true` (inline hypothesis `hc`) gives `X_true - X_false = 2 i Im X_true`; `zeroModeSet {0}` is `L^{-d} Σ_c`; `κ_W · 2i · L^{-d} = (N η)⁻¹`, with `N = (WL)^d`. At `η = 0` both sides are `0` in `ℂ` (case split), so no `η ≠ 0` premise.
- `baStep5CasesGen_wardIdent`: `baZeroModeGen_wardCls` (U2-BA); `𝓛` conjugation = conjunct 2 of `baStep2_oneLoop` (every `n u a ω`, no `g₀ > 0`); `𝒦` = clause 3 of `IsKLoopS` for `BAKsol` (`SEforLnBA_Ksol_isKLoopS`, from `baKcac_isKLoopS`; `BAReal` only, `BAflow_real`, every `n`): conjunct 1 of `baStep2_oneLoop` and `baKsol_one` are not used.
- Target 10: one call each of `stEtermsMidgL_of` (with `Hf = baEMn2Hf`, `ζf = baEMn2Zf`, `hLW` = `stLWTgL_of_LWtermExpG` + `Step2EventsGenTw_baRot3` + `baLWtermExp_holds d`, `hEMe = baEMn2ExpFacts d`, `hHK = baEMn2ExpHK`, `hBd = baSTBdatagL_holds`, `hK2 = baStep2_K2`, `hNew` = row a1 A9, `hFM` = row a1 D2, `hmn`, `hSr`, `hLF = baStep2Mat_loopForm`), `stDuhamelIgL_of`, `stDuhamelIIgL_of` (`hKer = baIniTermGen_kerFacts`, `hGR = gridRepTailGen_ker_BA`, `hGM = baGridMart_holds`, `hKs = baKLip_two` at `3 ≤ d`, `hGrid = Step2EventsGenTw_baGrid`, `hHerm = baStep2Mat_Hpath_herm`), `stIniTermIgL_of` (Ward class `baZeroModeGen_wardCls`, X1 class `baIniTermGen_cltFlow`), `stIniTermIIgL_of`, `stWardIIgL_of` (target 9). Family table rows 1-12 of the ticket each have the discharge named there; no premise beyond the table.
- Target 11: `ST_step5_caseI_of_pinsgL`, `ST_step5_caseII_of_pinsgL`, `stStep5IVgL_holds` with `baStep5CasesGen_flowFacts d`.
- Target 12: Finding 1 of (a) (regime premise `False` at `sz0`) stands as written there (script output in (a)); the instances use the private data above. Case (iv)'s nine carrier predicates stay hypotheses (Amend 1 item 3; the ticket text "every premise discharged" for (iv) is read as T2499 reads it: the regime, flow, `(con_st_ind)` and `s < t ≤ T₀` are discharged, the nine stochastic pins cannot be).
- Hypothesis table: `d = 3` at instances, `3 ≤ d` in the pins (`baStep5IV_holds` every `d`); no constant is introduced after `(sz, z)`; R1 enters only through the merged rows a1/a2 (`baIniTermGen_kerFacts` conjunct, `baStep2_K2`).

## (c) Verified Mathlib names used (all compile in this file)

`Complex.sub_conj`, `Finset.sum_sub_distrib`, `Finset.sum_congr`, `Finset.sum_ite_eq`, `Matrix.one_apply`, `Real.rpow_inv_le_iff_of_pos`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.zero_rpow`, `tendsto_atTop_mono`, `tendsto_natCast_atTop_atTop`, `tendsto_inv_atTop_zero`, `tendsto_pow_atTop`, `gt_mem_nhds`, `div_lt_one`, `le_div_iff₀`, `Nat.pow_le_pow_left`, `Nat.le_self_pow`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates

- Paper-delta candidates: none (compositions of merged generic results at the BA tuple; the bridge is a new generic statement of `(zYU1)`'s proof, no statement differs from the paper).
- The audit should read: (1) the cases (i), (ii), (iv) are `d = 3` at instances only because the instances are; the pins hold for every `3 ≤ d` (`baStep5IV_holds`: every `d`). (2) the instances keep the nine carrier predicates as hypotheses; (3) the instance data are private (Amend 1 item 1, 0 public `def`).
- `RBM3D.lean` (one import line) and `Test/Axioms.lean` (five deletions, two owner-text edits) are a union with T2498 row a at merge.
- Downstream: V's cases (i), (ii), (iv) producers are `baStep5I_holds`, `baStep5II_holds`, `baStep5IV_holds`; U6-BA reads them (REQ-1418 `:72-75`); `baSTWardIIgL_holds` and the bridge close the UN-C3 owner (answer (5)).
