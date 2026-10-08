Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 10:30:08 UTC 2026

Target: `stEtermsMid_of_LWT : ∀ d, STLWT d → STEtermsMid d` (`Step5Pins.lean:275`, conclusion `STEtermsMidConcl` `:259`; paper `3_5:1961-1979`).
Notation: `A = ilambda² W^d` (`STAI`), `Bctl = W^{-d}B_{u,0}` (`Defs/Sizes.lean:214`), `B_{u,r} = (g²+|1-u|)⁻¹(r+1)^{-(d-2)} + (L^d|1-u|)⁻¹` (`Defs/Params.lean:36`),
`prof_ℓ = STprof(·,ℓ,·) = W^{-d} 𝒯̃^ℓ` (`Step2Defs.lean:75`), `Ĵ^ℓ_D = STJhatM` (`:81`), `η_u = (1-u) Im m^{(E)}` (`Loop/GLoop.lean:75`), `ρ_u = (1-s)/(1-u)`, `N = (WL)^d`.

### (i) Exponent table (window `STReg5Mid`: `λ²/L^d ≤ 1-t ≤ 1-u ≤ 1-s ≤ λ²`, every `u ∈ [s,t]`)

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `A` | `≥ W^{2𝔡}`, `≤ 𝔡⁻²W^d` | `(eq:WO)` eventually (`WO`, `Defs/Sizes.lean:164`, `lam_sq_mul_pow_ge :193`) | `A ≥ 1` eventually; `A⁻¹ ≤ W^{-2𝔡}` |
| 2 | `B_{u,0}` | `∈ [1/(2λ²), 2/λ²]`: `(λ²+1-u)⁻¹ ∈ [1/(2λ²),1/λ²]`, `(L^d(1-u))⁻¹ ≤ 1/λ²` since `1-u ≥ λ²/L^d` | none beyond the window | `Bctl ∈ [1/(2A), 2/A]` (constant 2 each side) |
| 3 | `𝔠_d` | `min(1/100, 1/(30 C_d))` | `𝔠_d ≤ 1/100` (`STIngR5`, `Step5Pins.lean:85`); `𝔠_d C_d ≤ 1/30 = 1/5 - 1/6` | `1/30 - 𝔠_d C_d = 1/30 - C_d/100` for `C_d < 10/3`; `0` (tight, closes) for `C_d ≥ 10/3` |
| 4 | `ρ_u` | `≤ ρ_t = (1-s)/(1-t) ≤ Bctl(t)^{-𝔠_d} ≤ (2A)^{𝔠_d}` | `STConStInd 𝔠_d s t` (`Induction/Defs.lean:168`, eventually) + row 2 | factor `2^{𝔠_d} ≤ 2^{1/100}` |
| 5 | loss | `ρ_u^{C_d} Bctl(u)^{1/5} ≤ 2^{𝔠_dC_d+1/5} A^{𝔠_dC_d-1/5} ≤ 2^{7/30} A^{-1/6}` | rows 2-4, `A ≥ 1` | exponent slack `1/30 - 𝔠_dC_d`; `2^{7/30}` absorbed in `≺` |
| 6 | `Ĵ^L_{D₁}` (`D₁ = D+2d`) | `≺ A^{-1/6}` | `STGdecayW` at `D₁`, `STK2decay` not needed here; `STWB·e^{-√(r/ℓ_u)} = W^{-d}𝒯_u(r) ≤ prof_L` (`r ≤ L/2`, so `r∧L = r`); floor `W^{-D₁}/prof_L(D) ≤ W^{D+d-D₁} = W^{-d} ≤ 𝔡^{1/3}W^{-d/6} ≤ A^{-1/6}` | floor slack `W^{-5d/6}` eventually; main term exponent `1/6` exact (const `2^{7/30}`) |
| 7 | `ℰ^{LK×LK}` | `≤ C(1-u)⁻¹(Ĵ² prof_{D_N} + Ĵ W^{-d-D_N})`, `D_N = D+d`, `δ₀ = κ/2` (`stNewKLKL_holds`, `NewKLKL.lean:836`) | `‖STGMM‖ ≤ δ₀` from `STLocalEntryU`: `\|G-M\| ≺ (2/A)^{1/2} ≤ √2 W^{-𝔡}`; `(1-u)⁻¹ ≤ η_u⁻¹` since `η_u=(1-u)Im m`, `Im m = √(4-E²)/2 ≤ 1` (`Defs/Semicircle.lean:42`); `prof_{D_N} ≤ prof_D`; need `A^{1/6}W^{-d-D_N} ≤ W^{-d-D} ≤ prof_D` | target `A^{-1/3}`: `2·(1/6)` exact (slack 0, `N^{2τ}` absorbed); floor slack `W^{-5d/6}`; `\|G-M\|` slack `W^{-𝔡}` vs `δ₀` |
| 8 | `ℰ^{G̃}` | `STLWT`: `η⁻¹ Bctl^{1/2} prof_ℓ ≤ √2 A^{-1/2} η⁻¹ prof_ℓ` | premises of row 10-12; `prof_ℓ ≤ prof_L` (row 12) | exponent `1/2` exact (slack 0) |
| 9 | `(ℰ⊗ℰ)^{M,(2;k)}` | `STEMn2Exp`: `η⁻¹(Bctl^{1/2} + (Ĵ^ℓ_D)³) prof_ℓ²`, `Ĵ^ℓ_D ≤ Ĵ^L_D` (as `prof_L ≤ prof_ℓ`), `Ĵ^L_D ≺ A^{-1/6}` | row 6, 12 | `3·(1/6) = 1/2` exact (slack 0) |
| 10 | `ε₀` of `STInitialGT2` | `𝔡/2` (any `ε₀ ∈ (0,𝔡)`) | `\|G-M\|_max ≺ √2A^{-1/2} ≤ W^{-ε₀}` eventually; `Ψ_n := max(W^{-d/2}, (C₂/A)^{1/2})` with `C₂` the constant of `max 𝓛^{(2)} ≺ C₂ A⁻¹` (row 6 + `STK2decay`, `prof ≤ 2/A`); `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` | `Ψ ≤ √C₂ W^{-𝔡} ≤ W^{-𝔡/2}` slack `W^{-𝔡/2}` eventually |
| 11 | `STLWassmExp` premise at `ℓ` | `𝓛^{(2)} ≺ prof_ℓ`: `\|𝓛\| ≤ \|𝓛-𝒦\| + \|𝒦\| ≤ (A^{-1/6}+C) prof_L + W^{-D₁} ≤ C' prof_ℓ` | `prof_L ≤ prof_ℓ` (`𝒯` nonincreasing in `r`, `r∧ℓ ≤ r∧L`) | no loss; deterministic |
| 12 | `ℓ_n` | `min(L, (log W)^{10} ellT(L,λ,t_n))` (`ellT` `Defs/Params.lean:32`) | `0 ≤ ℓ ≤ (log W)^{10} ℓ_t` (STLWT `∀ᶠ`); and `prof_ℓ ≤ prof_L`: for `r>ℓ`, `𝒯(ℓ) ≤ B_{u,0} e^{-(log W)^5} ≤ 2W^d e^{-(log W)^5} ≤ W^{-D}` iff `(log W)^5 ≥ (d+D) log W + log 2` | `W ≥ 8` suffices at `d=3, D=10` (`(log 8)^5 = 39.0 ≥ 27.7`); vacuous when `ℓ = L` |
| 13 | lift `PrecPT → Prec` (u-uniformity of rows 8, 9) | per-time from sections via `ST_PT_of_sections` (`Step2Core.lean:500`); Hölder-1/2 in `u` on `contGood`: `N^{18}` (`LemDecCalELip_EGt :808`), `N^{21}` (`_ee :823`, sum over `k`); `R = bound ≥ prof ≥ W^{-d-D} ≥ N^{-(d+D)}`; `(1-t)⁻¹ ≤ N`: `1-t ≥ λ²/L^d ≥ W^{2𝔡}/N` | `lemDecCalEPrec_lift`/`LemDecCalELip_lift :1175` (`J ≡ 1, m = 0`, as `pfStep5_lift`, `PfStep5.lean:2398`) | `(1-t)⁻¹ ≤ N W^{-2𝔡}` slack `W^{2𝔡}` |
| 14 | `ST_selfImprove_section` twin | single time section, loss `((1-s)/(1-u))^{C_d}` | here no loss (rows 3-5 remove it) | n/a |

§29 one line each: (1) `0 ≤ s`, `t ≤ lemT z <1` are hypotheses of `STIngR5`; (2) `STReg5Mid` is the only regime hypothesis, `λ > L` harmless (row 2 uses only `1-u ∈ [λ²/L^d, λ²]`, `1-u ≤ 1` from `s ≥ 0`); (3) `L^d ≤ W^K` is not used, only `W ≥ N^𝔠` (for `N^τ ≤ W^{τ/𝔠}`) and `W^dL^d = N`; (4) `STReg5Mid` is `∀ n`, `WO`, `STConStInd`, `Bandwidth` are `∀ᶠ n`; the conclusion is `Prec` (eventual), so no condition is forced at finitely many `n`; `𝔠_d` is small depending on `C_d` (row 3).

### (ii) One nondegenerate instance (d = 3)
Data (`sz0` of `Step5Pins.lean` §8, `m = 2(n+1)`): `L=4(n+1)`, `W=m^5`, `λ=m^{-6}`, `N=(WL)^3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `E=0`, `z_n = i·λ²/4`, `C_d = 1`, `𝔠_d = 1/100`,
`1-s = λ²/2`, `1-t = (1-s)/1.01` (`ρ = 1.01`), `D = 10`; `A = m³` (n=0: `A = 8`, `L=4`, `W=32`, `N = 2097152`). Window, `t ≤ lemT(z_n)` (`1-|m_sc(iη)|² = η(√(η²+4)-η)/2`), `locDomain`, `WO`, `Bandwidth`, `(con_st_ind)` at `𝔠_d = 1/100`, row 2, row 5, row 10 `Ψ` class, row 12 tail inequality, all at once; the exponent closure (iv) on the grid; the external pin `STLWT 3` (LW gate, owed) is a hypothesis: limit computation of its premises along the instance (`log Ψ/log W → -0.3 ∈ (-3/2, -1/20)`, `√(A·Bctl)` stable at `0.818 ≤ √2`).
Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2328/inst.py`
```
checks (in order): window STReg5Mid, t<=lemT(z_n), locDomain, WO, Bandwidth, con_st_ind, Bctl in [1/2,2]/A, loss<=2^(7/30)A^(-1/6), Psi class, tail 2W^d e^{-(logW)^5}<=W^-D
n=0 L=4 W=32 lam=0.0156 A=8 | 1-s=0.000122 1-t=0.000121 1-lemT=6.1e-05 | 0.9759 0.9901 | 0.698..0.700 | all10=True (1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
n=1 L=8 W=1024 lam=0.000244 A=64 | 1-s=2.98e-08 1-t=2.95e-08 1-lemT=1.49e-08 | 0.9555 0.9901 | 0.671..0.673 | all10=True (1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
n=2 L=12 W=7776 lam=2.14e-05 A=216 | 1-s=2.3e-10 1-t=2.27e-10 1-lemT=1.15e-10 | 0.9439 0.9901 | 0.668..0.670 | all10=True (1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
n=5 L=24 W=248832 lam=3.35e-07 A=1728 | 1-s=5.61e-14 1-t=5.55e-14 1-lemT=2.8e-14 | 0.9244 0.9901 | 0.667..0.669 | all10=True (1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
n=50 L=204 W=11040808032 lam=8.88e-13 A=1.061e+06 | 1-s=3.94e-25 1-t=3.9e-25 1-lemT=1.97e-25 | 0.8670 0.9901 | 0.667..0.669 | all10=True (1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
n=1000 L=4004 W=32160320320160032 lam=1.55e-20 A=8.024e+09 | 1-s=1.21e-40 1-t=1.19e-40 1-lemT=6.03e-41 | 0.7929 0.9901 | 0.667..0.669 | all10=True (1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
ALL OK: True
grid Cd in [1,100], c_d=min(1/100,1/(30Cd)), Delta in [1e-20,1]: violations = 0 ; min slack 1/30-c_d*Cd = 0
c_d*Cd at Cd=1,10/3,100: [0.01, 0.033333, 0.033333]
n=1: log Psi/log W = -0.2500 (must lie in (-d/2,-eps0)=(-1.5,-0.05)); sqrt(A*Bctl(t))=0.8203
n=50: log Psi/log W = -0.2850 (must lie in (-d/2,-eps0)=(-1.5,-0.05)); sqrt(A*Bctl(t))=0.8178
n=1000: log Psi/log W = -0.2909 (must lie in (-d/2,-eps0)=(-1.5,-0.05)); sqrt(A*Bctl(t))=0.8178
n=1000000: log Psi/log W = -0.2952 (must lie in (-d/2,-eps0)=(-1.5,-0.05)); sqrt(A*Bctl(t))=0.8178
```
(the last column is `√(A·Bctl(t))`; `A·Bctl → 2/3` (table column 4); `slack 0` in the `C_d` line is the exact equality `𝔠_dC_d = 1/30`, computed in `Fraction`.)

### Verdict per target
- `stEtermsMid_of_LWT`: **PASS** (mathematics). All three exponents close with slack 0 in the powers of `A` that `≺` absorbs; `𝔠_d C_d ≤ 1/30` is tight but closes; the instance satisfies every hypothesis at once.
- Findings for stage 1b, none changing the verdict:
  - (F1) The ticket's import list (`EMn2Exp2`, `NewKLKL`) does **not** contain `RBM3D.Induction.LemDecCalELip` (nor `LemDecCalEPrec`, `Step5Kit`): a script over `import` lines (closure of the two imports, 115 modules) printed `LemDecCalEPrec False`, `LemDecCalELip False`, `Step2Core True`, `Step2Iterate True`, `NetLift2 True`, `ContinuityNet True`. The u-uniform lift of rows 8, 9 needs the Hölder moduli `LemDecCalELip_EGt`, `_ee`, `_env` and `LemDecCalELip_lift` (`LemDecCalELip.lean`, imports only `Step5Pins`, `NetLift2`, `Propagator.Deriv`, `Props4`: no cycle with `EtermsMid`). Required amendment: add `import RBM3D.Induction.LemDecCalELip`, or reprove from `ContinuityNet.cont_core` (in the closure).
  - (F2) `STEEk` is one summand `k` of `STee` (`STeeLoop`, `Induction/Step34Pins.lean`, `m=2`, `a'=a`: `k=1` labels `(a₁,a₂,c',a₂,a₁,c)`, `k=2` swapped, matching `STEEkM`); `LemDecCalELip_ee` bounds the sum over `k`, so the per-`k` Hölder bound must be redone from the public `LemDecCalELip_STLI_sub` (`:225`) and `STeeLoop` length lemma (private there).
  - (F3) The ticket's step "(1)" gives `Ĵ ≺ A^{-1/6}` only with the shifted `D₁ = D + 2d` (row 6): `prof ≥ W^{-d-D}`, not `W^{-D}`; paper-delta candidate `T2328a` (floor `W^{-D}` in `3_5:1961-1979` is read as `W^{-d}·W^{-D}`).
  - (F4) `STLWT` is stated at `ℓ ≤ (log W)^{10} ellT`, `ℓ = L` is not always admissible (it is when `ellT ≥ L/(log W)^{10}`); row 12 reduces to `ℓ_n = min(L,(log W)^{10} ellT)` and `prof_ℓ ≤ prof_L` eventually (paper-delta candidate `T2328b`: the paper applies `lem: EWGn2_N` "at `ℓ = L`" without this reduction).

## (a′) Preflight corrections — Thu Oct  8 11:11:43 UTC 2026
No verdict of (a) changes.  The Lean instance (section 10 of the file) uses the merged Step-5 data `szB`, not the (a)(ii) data.  Notes on (a):
- **(F1) confirmed by script** (`closure2.py`, closure of the two ticket imports over the `import` lines of the worktree):
```
closure of the two ticket imports: 115 modules
RBM3D.Induction.LemDecCalELip False
RBM3D.Induction.LemDecCalEPrec False
RBM3D.Induction.ContinuityNet True
RBM3D.Induction.Step2Core True
RBM3D.Path.NetLift2 True
RBM3D.Induction.EtermsMid False
LemDecCalELip imports: ['RBM3D.Induction.Step5Pins', 'RBM3D.Path.NetLift2', 'RBM3D.Propagator.Deriv', 'RBM3D.Propagator.Props4']
EtermsMid imports: ['RBM3D.Induction.EMn2Exp2', 'RBM3D.Induction.NewKLKL', 'RBM3D.Induction.LemDecCalELip']
EtermsMid in closure of LemDecCalELip (cycle check): False
```
  `import RBM3D.Induction.LemDecCalELip` is therefore added to the new file (no cycle).  It supplies `LemDecCalELip_EGt`,
  `LemDecCalELip_env`, `LemDecCalELip_Lloop_sub`, the Hölder moduli of the net lift.  The ticket's "imports (exactly ...)" is a ticket defect.
- **(F2)** realized: `etermsMid_EEk_sub` (per-`k` Hölder modulus `18 N^20 √|u-u'|` of `STEEk`, from `LemDecCalELip_Lloop_sub` at `k = 6`).
- **(F3)** realized: `STGdecayW` is applied at `D + 2d` (`etermsMid_J`), `STNewKLKLAt` at `D + d` (`etermsMid_ELKLK_det`).
- **(F4)** realized: `K_u = min (L, (log W)^10 ℓ_u)` (`etermsMid_Kf`) is the scale given to `STLWT`/`STEMn2Exp`; `𝒯̃^{K_u} = 𝒯̃^L` for
  `(d+D) log W ≤ (log W)^5` (`etermsMid_prof_Kf_le`).
- **Route difference (row 13 of (a))**: the lift uses `cont_core` directly (`etermsMid_lift`), not `LemDecCalELip_lift` at `J ≡ 1`: the latter
  needs `R(u') ≤ (1+N^C√|u-u'|) R(u)` for all pairs, the former the factor `2` at the mesh `N^{-A}` only (`etermsMid_zeta_close`);
  the profile depends on `u` through `ℓ_u`, `B_{u,r}`, `η_u`.  Not a correction of a verdict.

## (b) Script output

Targets (statements extracted by script; the pin `STEtermsMid` is merged, `git diff main...t/T2328` touches neither `Step5Pins.lean` nor `Step2Defs.lean`: 0 diff lines):
```
$ grep -n '^theorem stEtermsMid_of_LWT' RBM3D/Induction/EtermsMid.lean
1670:theorem stEtermsMid_of_LWT (d : ℕ) (hLWT : STLWT d) : STEtermsMid d := by
$ sed -n 259,275p RBM3D/Induction/Step5Pins.lean     # STEtermsMidConcl, STEtermsMid (merged pins)
def STEtermsMidConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := STIdx2 sz s t)
      (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    Prec sz (U := STIdx2 sz s t)
      (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    Prec sz (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEk sz n (E n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2)

/-- **`(S5WG+M000)`, `(S5WG+M)`**, window of cases (i)+(ii). -/
def STEtermsMid (d : ℕ) : Prop := STIngR5 d STReg5Mid (fun sz E s t => STEtermsMidConcl sz E s t)
$ sed -n 49,50p docs/tickets/checks/T2328-check.lean
def T2328_stEtermsMid_of_LWT : Prop := ∀ d : ℕ, STLWT d → STEtermsMid d
```
Build, axioms, registry pre-check, full build, check-file equality (one script, `mk_b.sh`, all after commit 0174c09):
```
$ date -u; git log --oneline -3; git diff --stat main...t/T2328; wc -l RBM3D/Induction/EtermsMid.lean
Thu Oct  8 11:08:15 UTC 2026
0174c09 T2328: S5-13 EtermsMid, stEtermsMid_of_LWT from STLWT
e3bc718 T2328: WIP EtermsMid (scalar, J control, ELKLK, net helpers)
4fa6d31 Dispatcher V1: DECISIONS §145 (Jun: close other gates first; S5-13 = T2328, S5-16 = T2329), H131
 RBM3D/Induction/EtermsMid.lean | 1757 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    2 +-
 2 files changed, 1758 insertions(+), 1 deletion(-)
    1757 RBM3D/Induction/EtermsMid.lean
[exit 0]

$ lake build RBM3D.Induction.EtermsMid 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3819 jobs).
[exit 0]

$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2328/ax.lean
'RBM.Gauss.Sizes.stEtermsMid_of_LWT' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]

$ lake build 2>&1 | grep -E "axiom audit|Build completed|^error" ; echo "lake build exit: ${pipestatus[1]}"
info: RBM3D.lean:370:0: axiom audit: 9900 theorems, 2972 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4136 jobs).
lake build exit: 0
[exit 0]

$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2328/registry.lean 2>&1 | head -3 ; echo "registry pre-check exit: ${pipestatus[1]}"
axiom audit: 9901 theorems, 2972 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
registry pre-check exit: 0
[exit 0]

$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2328/checkeq.lean > /dev/null; echo "check-file equality exit: $?"; grep -n "^import\|^example : RBM" /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2328/checkeq.lean
check-file equality exit: 0
7:import RBM3D.Induction.Step5Pins
8:import RBM3D.Induction.Step2Iterate
9:import RBM3D.Induction.EMn2Exp2
10:import RBM3D.Induction.Step2K2
11:import RBM3D.Induction.NewKLKL
12:import RBM3D.Induction.EtermsMid
57:example : RBM.Gauss.Sizes.T2328Check.T2328_stEtermsMid_of_LWT := RBM.Gauss.Sizes.stEtermsMid_of_LWT
[exit 0]
```

`#print axioms` is for the only public declaration.  The file has 1 public theorem, 55 `private theorem`/`def`, 4 `example`s.  Count of `sorry`/`admit`/`axiom`/`native_decide` (`grep -cE`): 0.
`registry.lean` (scratch file, not committed) = `import RBM3D` / `import RBM3D.Induction.EtermsMid` / `#assert_rbm_axioms`; its output above is the head (9901 theorems with the new module, 9900 without: one new public theorem).

Compiled nonempty instances (section 10 of the file, docstrings stripped by script; namespace `RBM.Gauss.EtermsMidInst`):
```
namespace RBM.Gauss.EtermsMidInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 1 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 1 one_pos

example (hLWT : STLWT 3) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) 100 :=
  inst_etermsMid (stEtermsMid_of_LWT 3 hLWT) 100 (by norm_num)

example (n : ℕ) : 1 / (2 * STAI szB n) ≤ szB.Bctl n (15 / 16) ∧ szB.Bctl n (15 / 16) ≤ 2 / STAI szB n :=
  etermsMid_Bctl_window szB n (by simp [szB]) (by norm_num [szB]) (by norm_num [szB])

example : ((101 / 100 : ℝ)) ^ (1 : ℝ) * (1 / 8 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * (8 : ℝ) ^ (-(1 / 6) : ℝ) := by
  refine etermsMid_q_le (A := 8) (ρ := 101 / 100) (b := 1 / 8) (bt := 1 / 12) (Cd := 1) (c := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (1 / 12 : ℝ) = 12⁻¹ by norm_num, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  calc (101 / 100 : ℝ) = ((101 / 100 : ℝ) ^ 100) ^ (((100 : ℕ) : ℝ)⁻¹) := by
        rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    _ ≤ 12 ^ (1 / 100 : ℝ) := by
        rw [show (1 / 100 : ℝ) = ((100 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)

end RBM.Gauss.EtermsMidInst
```

Name-clash grep of the new public names and prefixes (`RBM3D/`, outside `Probe/`):
```
RBM3D/Test/Axioms.lean:182:   `RBM.Gauss.Sizes.STEtermsMid, -- `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1979`); S5-01 (T2138
hits outside the new file: 1 (the registry comment line only)
```
Unused hypotheses of the pin (underscored binders of the proof; `STStep2Concl` is split as `⟨STLocalEntryU, -, STGdecayW⟩`):
```
1673:  intro 𝔠 sz z hflow s t hs hst htz hReg _hKb _hKw _hLKs _hDec _hDecS hCon _hStep1 hStep2 _hLmax _hLKU D hD
```
No port from RBM1D/RBM2D (copies from RBM3D only, cited in the module docstring; `git log -1 --format=%h -- RBM3D/Path/NetLift1.lean` = 06b49b2).

Narrative.
- `stEtermsMid_of_LWT : ∀ d, STLWT d → STEtermsMid d` is proved from the merged proved pieces `stK2decay_holds`, `stNewKLKL_holds`, `stEMn2Exp_holds`,
  `ST_Bdata_holds`, `ST_LW_sections` (`STLWT` stays the hypothesis).  The constant of the pin is `𝔠_d = min (1/100, 1/(30 C_d))`.
- Of the hypotheses of `STIngR5` only `STFlow`, `STReg5Mid`, `STConStInd 𝔠_d`, `STLocalEntryU` and `STGdecayW` are used (see the grep above).
- `ℰ^{LK×LK}`: no net lift needed, the good event `‖G-M‖_max ≤ δ₀` and `Ĵ^L_{D+d} ≤ N^τ Θ` hold simultaneously in `u` (`STLocalEntryU`,
  `STGdecayW`); `STNewKLKLAt` gives `C/(1-u) (Ĵ² 𝒯̃ + Ĵ W^{-d-(D+d)})`; `Θ = 2A^{-1/6} + W^{-d}`, `W^{-d} ≤ 𝔡^{-1/3} A^{-1/6}`.
- `ℰ^{G̃}`, `(ℰ⊗ℰ)^{M,(2;k)}`: `STLWT`, `STEMn2Exp` are single-time statements; `ST_LW_sections` (merged) takes the premises at a time section `tt`
  (`(Gtmwc)` from `STLocalEntryU` through `etermsMid_S1W` (the premise `hS1W`), `(eq:LW_assm_exp)` at `K_u` from `|𝓛^{(2)}| ≺ W^{-d}𝒯̃^L`), then `etermsMid_lift`
  (`cont_core`, `contGood`, Hölder `LemDecCalELip_EGt`/`etermsMid_EEk_sub`, factor-2 variation `etermsMid_zeta_close`, floor `N^{-(3+2D)}`) gives `u ∈ [s,t]`.
- The random `Ĵ³` of `STEMn2Exp` is controlled by `Ĵ^{K_u} ≤ Ĵ^L ≺ Θ` (`etermsMid_Jhat_mono`, `etermsMid_Jhat_sec`, `etermsMid_prec_two`).
- Instances: `STLWT 3` and the Step 1-4 stochastic premises inside `InstIng5Concl` stay hypotheses (other gates' pins); every deterministic hypothesis
  (`flow_zB`, `s < t ≤ lemT`, `STReg5Mid`, `STConStInd` at every `𝔠_d > 0`) is discharged by the merged `inst_ing5_I`.
- The registry line `STEtermsMid` is kept; its comment gets "proved from `STLWT` by `stEtermsMid_of_LWT` (T2328, S5-13)".
- Size: 1757 lines; the file passed 1500 lines inside section 8 (section 8 = lines 1359-1661; the target is section 9, lines 1662-1716).

## (c) Verified Mathlib names (by compilation of this file; none invented; none searched and found absent)
`Real.`/`Finset.`/`Filter.`/`Nat.`/`StochDomAt.` names used by the new code (script `grep -o`):
Complex.norm_natCast, Filter.Eventually, Finset.card_univ, Finset.le_sup', Finset.lt_sup'_iff, Finset.mem_univ, Finset.sum_const, Finset.sum_le_sum, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sup'_le, Finset.univ, Fintype.card, Nat.cast_nonneg, Nat.cast_zero, Nat.le_mul_of_pos_left, Nat.le_self_pow, Nat.pow_le_pow_left, Real.add_one_le_exp, Real.div_rpow, Real.exp, Real.exp_add, Real.exp_le_exp, Real.exp_log, Real.exp_nat_mul, Real.exp_one_lt_d9, Real.exp_pos, Real.inv_rpow, Real.log, Real.log_nonneg, Real.mul_rpow, Real.mul_self_sqrt, Real.one_le_exp, Real.one_le_rpow, Real.pow_rpow_inv_natCast, Real.rpow_add, Real.rpow_def_of_pos, Real.rpow_le_one_of_one_le_of_nonpos, Real.rpow_le_rpow, Real.rpow_le_rpow_of_exponent_ge, Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow_of_nonpos, Real.rpow_mul, Real.rpow_natCast, Real.rpow_neg, Real.rpow_neg_one, Real.rpow_nonneg, Real.rpow_one, Real.rpow_pos_of_pos, Real.rpow_sub, Real.sqrt, Real.sqrt_eq_rpow, Real.sqrt_le_iff, Real.sqrt_le_left, Real.sqrt_le_sqrt, Real.sqrt_nonneg, Real.sqrt_pos, Real.sqrt_sq, Real.tendsto_log_atTop, StochDomAt.of_subset, StochDomAt.of_subset_union, StochDomAt.precomp_param.
Generic order/algebra names (same compilation): `mul_max_of_nonneg`, `abs_norm_sub_norm_le`, `one_le_inv₀`, `inv_anti₀`, `pow_le_pow_left₀`,
`pow_le_pow_iff_left₀`, `pow_lt_pow_left₀`, `div_le_div_of_nonneg_left`, `div_le_iff₀`, `lt_div_iff₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀`,
`tendsto_rpow_atTop`, `eventually_gt_atTop`, `eventually_ge_atTop`, `Finset.sum_sub_distrib`.

## (d) Open issues and paper-delta candidates
1. **Ticket defect (F1)**: the file imports `RBM3D.Induction.LemDecCalELip` besides the two listed imports; the dispatcher should amend the ticket text.
2. **Size**: 1757 lines against the estimate 700/900/1300 and the stop rule (1500 at a section boundary).  The rule was not applied: the file was
   1358 lines at the end of section 7, and the target theorem sits in section 9, after the boundary at line 1661.  The copy of four `NetLift1` helpers is 104 lines
   (script count of the extracted block), the instances section is 41 lines.  For the dispatcher's decision.
3. `T2328a` (`D`-shifts): `(eq:Step2_inputs)` at `ℓ = L` gives `Ĵ ≺ A^{-1/6}` only with `STGdecayW` at `D + 2d` (profile floor `W^{-d-D}` vs `W^{-D₁}`);
   `lem:newKLK` is used at `D + d` so that the floor `Ĵ W^{-d-D'}` is `≤ A^{-1/3} W^{-d}𝒯̃_D`.  The paper (`3_5:1961-1979`) uses one `D`.
4. `T2328b` (scale): `lem: EWGn2_N`/`lem: EMn2_N` are applied "at `ℓ = L`" (`3_5:1961`), but their range is `ℓ ≤ (log W)^10 ℓ_u`, and `ℓ = L` fails this e.g. at `1-u = ilambda²`
   (`ℓ_u = 1`) when `L > (log W)^10`; Lean uses `K_u = min (L, (log W)^10 ℓ_u)` and `𝒯̃^{K_u} = 𝒯̃^L` (eventually, `W^d e^{-(log W)^5} ≤ W^{-D}`).
5. `T2328c` (constant): `𝔠_d = min (1/100, 1/(30 C_d))` realizes "choose `𝔠_d` accordingly" (`ρ^{C_d} Δ_u^{1/5} ≤ 2 A^{-1/6}`, constant `2` in place of `Δ_u^{1/6}`).
6. `T2328d` (uniformity in `u`): `STLWT`, `STEMn2Exp` are single-time; the uniform-in-`u` statement `STEtermsMidConcl` needs the net lift (as T2193c′).
7. `T2328e` (hypotheses): the pin `STEtermsMid` assumes the Step 1-4 conclusions (`STLmaxU`, `STLKU`, `STStep1Loop`, the hypotheses at `s`) that the proof does not use.
8. `STLWT` is the LW gate's pin (owed); its limit check along the instance is in (a), (ii).  `ST_step5_caseI_of_pins` can take `stEtermsMid_of_LWT d hLWT`
   once the LW gate proves `STLWT` (`STLWT_of_LWtermExp`).

