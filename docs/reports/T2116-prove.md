Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 06:29:46 UTC 2026 (`date -u`)

Paper `3_5` = `paper/tex/3_5_Loop_Hierarchy.tex` (`(eq:opt_L2)` proof `3_5:466–512`). Scripts `$S/T2116/{chain,inst}.py`, `$S` = session scratchpad. Notation: `B_u := sz.Bctl n u`, `ρ_T := (1-s)/(1-T) ≥ 1`, `λ := OptL2alam = ρ_T B_T` (`OptL2a.lean:163`), `N = size`, `J_k = OptL2aJ`.

### (i) Exponent table and proof map

| quantity | value | constraint | slack |
|---|---|---|---|
| `C₀` of `stOptL2a_gronwall` (`OptL2a:1260`) | `∃ C₀>0` chosen after `κ ε 𝔡` only (`C₀ = 2C`, `C` of `stNewKLK_holds`) | `β_j = C₀/(1-u_j) ≥ 0` for `ST_gronwall` (`Core:56`) | free of `W,L,λ,s,T` (§29) |
| `𝔠₀` (pin: `∃ 𝔠₀>0` before `𝔠_d`, sequences) | `min(1/2, 1/(8C₀+10))` (`= 1/(8C₀+10)`, as `C₀>0` gives `≤ 1/10`) | (1) `𝔠_d ≤ 1/2` (hyp. of T2110); (2) `𝔠_d(C₀+5/4) ≤ 1/4`; (3) `C₀𝔠_d ≤ 1` | (2): `≤ 1/8`, slack `1/8`; (3): `≤ 1/8·C₀/(C₀+5/4) < 1/8`; (1): `≤ 1/10`, slack `2/5` |
| restriction of `STConStInd` to `T ≤ t` | `B_T^{𝔠_d} ≤ B_t^{𝔠_d} ≤ (1-t)/(1-s) ≤ (1-T)/(1-s)` | `STBctl_mono` (`ScaleFacts:74`, `T≤t<1`), `𝔠_d>0` (rpow monotone), `1-s>0` | none needed; first conjunct only (T2110d): the 2nd, `(1-T)/(1-s)<1`, fails at `T=s` |
| restriction of `STStep1Loop/Weak`, `STLK` | `TimeIcc s T ⊆ TimeIcc s t` (same bound: `B_s`, `ρ` unchanged) ; `STLK` is at `s` only | `Prec` pulled back along the inclusion | exact |
| `B_T ≤ 1`, `B_T ≤ N^{-c}` | `ST_Bdata_holds` (`Iterate:1049`) at the section: `B_T ≤ N^{-c}`, `N ≥ 1` | needs `0 ≤ T ≤ lemT`; eventually in `n` | `c=min(2𝔡𝔠,ε)/2>0`; only `B_T ≤ 1` used below |
| grid end | `gridTime K = s+KΔ = T` (`gridTime_last`, `Walk:160`), `T ≤ lemT < 1` (`lemT_lt_one`) | `ST_logsum`, `ST_prod_le_rpow` (`Core:160`) need `s+KΔ<1`; `Δ=(T-s)/K ≥ 0` | `T=s`: `Δ=0`, product `=1 = ρ^{C₀}` |
| Grönwall end | `J_K ≤ α ∏(1+ΔC₀/(1-u_j)) ≤ α ρ_T^{C₀}`, `α = N^τ(B_s²+λ^{5/4})` | `α` constant (monotone) | exact |
| term 1 | `ρ_T^{C₀}B_s² ≤ B_T^{-C₀𝔠_d}B_T² ≤ B_T^{2-C₀𝔠_d} ≤ B_T` | `B_s ≤ B_T` (mono), `ρ_T ≤ B_T^{-𝔠_d}` (first conjunct), `B_T ≤ 1`, `C₀𝔠_d ≤ 1` | exponent gain `≥ 7/8` |
| term 2 | `ρ_T^{C₀}λ^{5/4} = ρ_T^{C₀+5/4}B_T^{5/4} ≤ B_T^{5/4-𝔠_d(C₀+5/4)} ≤ B_T` | `𝔠_d(C₀+5/4) ≤ 1/4`, `B_T ≤ 1` | exponent gain `≥ 1/8` beyond `B_T` |
| closing | `J_K ≤ N^τ·2B_T ≤ N^{ε}B_T` with `τ = ε/2`, `N^{ε/2} ≥ 2` | eventually in `n` (`N→∞`, `tendsto_size`) | `Prec` is for every `ε,D`; `D` passes to `stOptL2a_gronwall` unchanged |
| model transfer | the `Bad` event of `stOptL2a_gronwall` is global (not per label), `{N^ε B_T < ‖L-K‖_i}` at `k=K` ⊆ `Bad` via `OptL2aJ_ge` (`OptL2a:56`), `ST_model_le_path` (`Events:566`), `K_n ≠ 0` | `K_n=⌈N^{CK}⌉ ≥ 1`, `N ≥ 1` | no union over labels, no `N^{-C}`-net (T2110a) |
| per time | `ST_PT_of_sections` (`Core:500`): `PrecPT` of the pin from `Prec` on `V_n = (Fin 2→Bool)×(Fin 2→Zd d L)` at every section `tt n ∈ TimeIcc s t n` | `V_n` finite nonempty | exact |

**Map of steps.** Step 1 (restrictions): `STStep1Loop`, `STStep1Weak`, first conjunct of `STConStInd`, `STLK` as in the table; the remaining premises of `stOptL2a_gronwall` at `(s,T)` are `STFlow`, `0≤s≤T≤lemT` (from `T=tt n ≤ t`). Step 2: `stOptL2a_gronwall` at `(s,T=tt)` (`τ=ε/2`, any `D`), `ST_prod_le_rpow` with `c=C₀` (`C₀/(1-u)=C₀·(1-u)⁻¹`), `ST_logsum` is inside it; comparison with `B_T` by terms 1–2 (this is `(eq:L-K2max)` with the explicit `𝔠₀`); `ST_model_le_path`; `ST_PT_of_sections`. Step 3: the pin as stated, `hd : 3 ≤ d` (T2110f), hypotheses `STLWB d`, `STGridMart d` passed to `stOptL2a_gronwall`.

**§29 checks.** (1) `0 ≤ s ≤ T ≤ t ≤ lemT < 1` for every section, including `T=s` (`ρ=1`) and `T=t`: PASS. (2) per time via `PrecPT`/`ST_PT_of_sections`, no net: PASS. (3) `L^d ≤ W^K` unused: PASS. (4) `Prec` eventual in `n`; `C₀,𝔠₀` constant before the sequences and free of `W,L,λ`: PASS. **Paper point (`3_5:481,504–509`):** `(eq:L-K2max)` has `((1-s)/(1-t))^{C₀}((W^{-d}B_{t,0})²+W^{-5c₀/4})` and chooses `𝔠_d` small depending on `C₀`; Lean's `α` has `B_s² ≤ B_T²` (mono), and `W^{-c₀}` it is exactly terms 1–2 above (`λ=ρ_T B_T`); the paper needs `𝔠_d` small in terms of `C₀` only, and `𝔠₀ = 1/(8C₀+10)` is explicit (candidate `T2116a`). The term-1/2 argument needs only `B_T ≤ 1`, not a power of `N`; the loss `2` is absorbed by `N^{ε/2}`.

### (ii) Concrete instance (d = 3)
Data: `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`), `z0`, `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (`Induction/Defs.lean`), `s≡0`, `t≡1/16 ≤ lemT(z0_n)` (`sixteenth_le_lemT`), `κ=ε=𝔡=1/10`, `𝔠=1/6`, `C₀=2` (illustrative; the real `C₀` is the output of `stNewKLK_holds`, covered below for `C₀ ∈ {2,20}`), `𝔠_d=𝔠₀=1/26`; sections `T ∈ {s=0, 1/32, t=1/16}`. `STLK`, `STStep1Loop`, `STStep1Weak`, `STLWB 3`, `STGridMart 3` stay hypotheses of the example (other gates' pins, read through `inst_optL2`, `Step2Defs:1134`); `conStInd_inst` (`Defs:516`) discharges `STConStInd`. Command `cd $S/T2116 && python3 inst.py` (columns: `B_s ≤ B_T ≤ B_t`; `B_T ≤ 1`; first conjunct at the section; `R = ρ^{C₀}(B_s²+λ^{5/4})/B_T`, to be `≤ 2`):
```
C0=2 cd=cd0=0.03846  cd<=1/2: True  cd*(C0+5/4)=0.1250 (<=1/4)  cd*C0=0.0769 (<=1)
    n       T   rho_T  B_s<=B_T<=B_t B_T<=1 B_T^cd<=1-T   B_T^cd R=rho^C0(Bs^2+lam^5/4)/B_T  R<=2
    0  0.0000  1.0000           True   True        True   0.6708                     0.0746  True
    0  0.0312  1.0323           True   True        True   0.6716                     0.0834  True
    0  0.0625  1.0667           True   True        True   0.6725                     0.0936  True
   10  0.0000  1.0000           True   True        True   0.1681                     0.0000  True
   10  0.0312  1.0323           True   True        True   0.1683                     0.0000  True
   10  0.0625  1.0667           True   True        True   0.1685                     0.0000  True
 1000  0.0000  1.0000           True   True        True   0.0125                     0.0000  True
 1000  0.0312  1.0323           True   True        True   0.0125                     0.0000  True
 1000  0.0625  1.0667           True   True        True   0.0125                     0.0000  True
limits: B_t <= 1.1 W^-3 ->0: True ; W_n=(2(n+1))^5 -> inf (sz0_admissible, merged)
```
External-type hypotheses (limits): `B_t ≤ 1.1 W^{-3} → 0` (the `limits:` line prints `True` for n = 0,1,5,100,1000) and `W_n=(2(n+1))^5 → ∞`, `N→∞` (`sz0_admissible`, merged); `B_T^{𝔠_d}` falls from `0.67` (n=0) to `0.0125` (n=1000), always `≤ 1-T`.

### (iii) Scalar chain `(eq:Gronwall_2L_max) → (eq:L-K2max)` at d = 3
Worst case `B_s=B_T=B`, `ρ` on a 61-point geometric grid of `[1, B^{-𝔠_d}]`, `cB=1/101` (`𝔡=1/10`, the lower bound of `ST_Bdata_holds`), `B ∈ {cB W^{-3}, W^{-1}}`; `F = max_ρ ρ^{C₀}(B+ρ^{5/4}B^{1/4}) = max LHS/B_T`. Largest admissible `𝔠_d` by bisection for (A) `F ≤ 1` (no loss) and (B) `F ≤ 2` (the form proved above); `python3 chain.py`:
```
d=3, cB=1/101 (DD=1/10).  F = max_rho rho^C0 (B + rho^{5/4} B^{1/4}) = max LHS/B_T; (A): F<=1, (B): F<=2
     W              B  C0  cd_max(A)  cd_max(B)  1/(4C0+5)  cd0=1/(8C0+10)   F(cd0) F(cd0)<=1
2^4          W^-3/101   2    0.07692    0.09341    0.07692         0.03846   0.1986      True
2^4          W^-3/101  20    0.01176    0.01429    0.01176         0.00588   0.1986      True
2^4              W^-1   2    0.06642    0.14578    0.07692         0.03846   0.7845      True
2^4              W^-1  20    0.00983    0.02167    0.01176         0.00588   0.7937      True
2^8          W^-3/101   2    0.07692    0.08696    0.07692         0.03846   0.0702      True
2^8          W^-3/101  20    0.01176    0.01330    0.01176         0.00588   0.0702      True
2^8              W^-1   2    0.07641    0.11500    0.07692         0.03846   0.5060      True
2^8              W^-1  20    0.01164    0.01753    0.01176         0.00588   0.5075      True
2^12         W^-3/101   2    0.07692    0.08414    0.07692         0.03846   0.0248      True
2^12         W^-3/101  20    0.01176    0.01287    0.01176         0.00588   0.0248      True
2^12             W^-1   2    0.07689    0.10254    0.07692         0.03846   0.3540      True
2^12             W^-1  20    0.01175    0.01568    0.01176         0.00588   0.3542      True
```
Reading: the exponent criterion `𝔠_d ≤ 1/(4C₀+5)` is what (A) approaches as `B→0` (`cd_max(A) = 1/(4C₀+5)` at `B=cB W^{-3}`), and it is the binding one for all `B ≤ 1` in form (B); `𝔠₀ = 1/(8C₀+10)` is half of it. Margin at `𝔠₀`: `F ≤ 0.794 < 1` in all 12 rows (largest at `W=2^4`, `B=W^{-1}`, the least asymptotic case); (B) holds up to `cd_max(B) ≥ 0.01287` in all rows, always `≥ 1/(4C₀+5)`, i.e. a factor `≥ 2` above `𝔠₀`.

### Verdicts
- Target `stOptL2_of_pins (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d`: **PASS**. Hypotheses `3 ≤ d`, `STLWB d`, `STGridMart d` are satisfiable together with the instance (they are pins); every exponent closes with the slacks above; no step is false as written.
- Notes for the prover (not defects): only `B_T ≤ 1` is needed from `ST_Bdata_holds`; `𝔠₀ ≤ 1/2` must be part of the `min`; `T=s` is the only section where the second conjunct of `STConStInd` fails, hence the first-conjunct-only restriction (already built into `stOptL2a_gronwall`).

## (b) Script output — Sun Oct  4 06:41:42 UTC 2026 (`date -u`)

### b.1 Build, hygiene, diff scope (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2116`, branch t/T2116)
```
$ git log --oneline -2; git diff --name-only main...t/T2116; wc -l RBM3D/Induction/OptL2b.lean
02d54f2 T2116: ST2-15 Induction/OptL2b (stOptL2_of_pins: STLWB, STGridMart => STOptL2)
aaf704f T2109: merge ST2-10 Induction/EMn2Exp1
RBM3D/Induction/OptL2b.lean
RBM3D/Test/Axioms.lean
     400 RBM3D/Induction/OptL2b.lean
$ lake build RBM3D.Induction.OptL2b 2>&1 | grep -E "OptL2b|Build completed|error"
Build completed successfully (3767 jobs).
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/OptL2b.lean; echo "grep exit $?"
grep exit 1
```

### b.2 Axioms (`lake env lean $S/T2116/axioms.lean`: import RBM3D.Induction.OptL2b + #print axioms)
```
'RBM.Gauss.Sizes.stOptL2_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_rho_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_loop_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_weak_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_con_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_J_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_badSet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Target statement (extracted by script) and the pin it concludes
```
$ awk '/^theorem stOptL2_of_pins/{print; exit}' RBM3D/Induction/OptL2b.lean
theorem stOptL2_of_pins {d : ℕ} (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d := by
$ git diff main...t/T2116 --stat -- RBM3D/Induction/Step2Defs.lean   (the pin file; empty output = unchanged)
$ sed -n 667,678p RBM3D/Induction/Step2Defs.lean
def STOptL2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep1Weak sz (STflowE z) s t →
          PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
              STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
            (fun n p _ => sz.Bctl n (p.1 : ℝ))

section L2
```

### b.4 Compiled nonempty instance (`RBM3D/Induction/OptL2b.lean`, namespace `RBM.Gauss.OptL2bInst`; extracted by `sed -n 333,362p`)
```
/-- **`stOptL2_of_pins` at `d = 3`, read through the merged `inst_optL2`**. -/
example (hLWB : STLWB 3) (hGM : STGridMart 3) :
    ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep1Weak sz0 (STflowE z0) sInst tInst →
        PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ))) :=
  inst_optL2 (stOptL2_of_pins (d := 3) (by norm_num) hLWB hGM)

/-- **`stOptL2_of_pins` at `d = 3`, applied directly** to `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`,
`s ≡ 0`, `t ≡ 1/16` (a window with `s < t`): `𝔠₀` is the constant of the pin, and for every
`0 < 𝔠_d ≤ 𝔠₀` the per-time bound `(eq:opt_L2)`
`max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| ≺ W^{-d} B_{u,0}` holds on the window, from `(con_st_ind)`
(discharged) and the three stochastic premises. -/
example (hLWB : STLWB 3) (hGM : STGridMart 3) :
    ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep1Weak sz0 (STflowE z0) sInst tInst →
        PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ))) := by
  obtain ⟨𝔠₀, h0, hall⟩ := stOptL2_of_pins (d := 3) (by norm_num) hLWB hGM (1 / 10) (1 / 10)
    (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠₀, h0, fun 𝔠d h1 h2 hLK hS1L hS1W => hall 𝔠d h1 h2 (1 / 6) sz0 z0 flow_z0 sInst tInst
    (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) hLK (conStInd_inst h1) hS1L hS1W⟩

```
```
$ grep -n "^example" RBM3D/Induction/OptL2b.lean   (five examples; the remaining three: restrictions at [0,1/32], arithmetic at rho=1 and at rho=32/31)
334:example (hLWB : STLWB 3) (hGM : STGridMart 3) :
349:example (hLWB : STLWB 3) (hGM : STGridMart 3) :
364:example (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
377:example : (2 : ℝ) * ((1 / 10 : ℝ) ^ 2 + (1 * (1 / 10 : ℝ)) ^ (5 / 4 : ℝ)) * (1 : ℝ) ^ (2 : ℝ) ≤
387:example : (2 : ℝ) * ((1 / 20 : ℝ) ^ 2 + (32 / 31 * (1 / 10 : ℝ)) ^ (5 / 4 : ℝ)) *
```

### b.5 Name-clash grep (public names of the file, in main-worktree `RBM3D/`, `RBM3D.lean`, `../RBM1D/RBM1D`, `../RBM2D/RBM2D`)
```
$ cd /Users/junyin/Lean_proof/RBM3D; for n in stOptL2_of_pins OptL2b_rho_pow_mul OptL2b_arith OptL2b_loop_restrict OptL2b_weak_restrict OptL2b_con_restrict OptL2b_J_measurable OptL2b_badSet_eq OptL2bInst; do echo "== $n"; grep -rn "\b$n\b" RBM3D RBM3D.lean ../RBM1D/RBM1D ../RBM2D/RBM2D | head -3; done
== stOptL2_of_pins
== OptL2b_rho_pow_mul
== OptL2b_arith
== OptL2b_loop_restrict
== OptL2b_weak_restrict
== OptL2b_con_restrict
== OptL2b_J_measurable
== OptL2b_badSet_eq
== OptL2bInst
```

### b.6 Registry (`RBM3D/Test/Axioms.lean`, one comment edit on the `STOptL2` line) and the pre-check (DECISIONS §20)
```
$ git diff main...t/T2116 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STOptL2, -- `(eq:opt_L2)` (`3_5:470`): ST2-14, ST2-15 (T2066, DECISIONS §28)
+   `RBM.Gauss.Sizes.STOptL2, -- `(eq:opt_L2)` (`3_5:470`): ST2-14, ST2-15 (T2066, DECISIONS §28); `stOptL2_of_pins` (T2116) proves it from `STLWB` and `STGridMart`, so it stays owed through those two
$ cat $S/T2116/precheck.lean   (uncommitted temporary file)
import RBM3D
import RBM3D.Induction.OptL2b
#assert_rbm_axioms
$ lake env lean $S/T2116/precheck.lean > out 2>&1; echo "exit $?"
exit 0
$ head -1 out; grep -n "premises found\|STOptL2" out | cut -c1-200
axiom audit: 3607 theorems, 1266 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
67:  RBM.Gauss.Sizes.STOptL2: 7 [no certificate]
115:premises found by scanning: 81 (borrowed 2, owed 63, structural 16).
144: RBM.Gauss.Sizes.STOptL2,
```

### b.7 Full build in the worktree
```
$ lake build 2>&1 | grep -E "^axiom audit|^registry|Build completed|error" | cut -c1-200
registry: 5 borrowed + 103 owed + 39 structural; 64 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3862 jobs).
```

### b.8 Ports
None: the ticket and the file header say "New; no port"; no RBM1D/RBM2D file was read for this ticket's Lean, so no `git diff --stat` of the sister projects applies.

### b.9 Narrative (≤ 40 lines)
- **Delivered.** One new file `RBM3D/Induction/OptL2b.lean` (400 lines, namespace `RBM.Gauss.Sizes`) with the target `stOptL2_of_pins {d} (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d` (b.3); the pin `STOptL2` (`Step2Defs:667`) is not touched (b.3: empty diff). One comment edit on the `STOptL2` registry line of `RBM3D/Test/Axioms.lean` (b.6). Commit `02d54f2` on `t/T2116` (stage 1b: first `date -u` of the stage Sun Oct  4 06:30:13 UTC 2026; commit made before the `date -u` reading Sun Oct  4 06:40:36 UTC 2026); `git diff --name-only main...t/T2116` lists exactly these two files (b.1).
- **Proof shape (follows section (a) as written; no (a′) needed).** `C₀` comes from `stOptL2a_gronwall` (T2110), which is chosen after `κ ε 𝔡` and before `𝔠, sz, z, s, t, 𝔠_d` (its signature, `OptL2a.lean:1260`); `𝔠₀ := 1/(8 C₀ + 10)`. For each time section `T_n = tt n ∈ [s_n, t_n]` (`ST_PT_of_sections`):
  1. restrictions to `[s,T]`: `OptL2b_loop_restrict`, `OptL2b_weak_restrict` (`StochDomAt.precomp_param` along `TimeIcc s T n ⊆ TimeIcc s t n`), `OptL2b_con_restrict` (first conjunct of `STConStInd` through `STBctl_mono`; `𝔠_d > 0`); `STLK` is at `s` and is passed unchanged;
  2. `stOptL2a_gronwall` at `(s, T)` with `τ := τ'/2` and the `D` of `PrecPT`; on the grid `K_n = ⌈N^{CK}⌉`, `ST_gronwall` (constant `α`, `β_j = C₀/(1-u_j)`) and `ST_prod_le_rpow` give `J_K ≤ α ρ_T^{C₀}`, `ρ_T = (1-s)/(1-T)`, `gridTime_last` turns `u_K` into `T_n`;
  3. `OptL2b_arith` (the paper's `(eq:L-K2max)` with the explicit `𝔠₀`): `M(B_s² + λ^{5/4}) ρ^{C₀} ≤ M² B_T` for `M = N^{τ'/2} ≥ 2`, via `OptL2b_rho_pow_mul` (`ρ^p B^e ≤ B` from `ρ ≤ B^{-𝔠_d}`, `1 + 𝔠_d p ≤ e`) with `p = C₀, e = 2` and `p = C₀ + 5/4, e = 5/4`; `B_s ≤ B_T` by `STBctl_mono`, `B_T ≤ 1` from `OptL2a_sizedata` and `N ≥ 1`;
  4. the endpoint `k = K` is moved from the grid walk to the single-time model by `ST_model_le_path` with `F = OptL2aJ`, `Z = B` (`OptL2b_J_measurable`, `OptL2b_badSet_eq` identify the union over labels `∃ v` with `N^τ' B_T < J`); the grid failure event is the global one of `stOptL2a_gronwall` (no union over labels, no `N^{-C}`-net in `u`).
- **Constants.** `𝔠_d ≤ 𝔠₀ = 1/(8C₀+10) ≤ 1/2` gives the hypothesis `𝔠_d ≤ 1/2` of `stOptL2a_gronwall` (`hc12`). In `OptL2b_arith`, `h8 : 𝔠_d (8C₀+10) ≤ 1` yields `e1 : 𝔠_d C₀ ≤ 1` and `e2 : 1 + 𝔠_d (C₀ + 5/4) ≤ 5/4`, the two inequalities the terms need; the exact values are `𝔠_d C₀ ≤ 1/8` and `𝔠_d (C₀+5/4) ≤ 1/8` (the slacks of section (a) (i)). The scalar chain of (a) (iii) is the same computation; `OptL2b_arith` is also instantiated at numbers in the file (b.4: `C₀ = 2`, `𝔠_d = 1/26`, `ρ = 1` and `ρ = 32/31`).
- **Instances.** `stOptL2_of_pins` at `d = 3`, `sz0, z0, s ≡ 0, t ≡ 1/16`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, all `0 < 𝔠_d ≤ 𝔠₀` (b.4). Discharged: `3 ≤ d`, `STFlow` (`flow_z0`), the time ranges, `(con_st_ind)` (`conStInd_inst`). Left as hypotheses: `STLWB 3`, `STGridMart 3` (other gates' pins) and `STLK`, `STStep1Loop`, `STStep1Weak` (the ST-6 chain and S1-36).
- **Registry.** `stOptL2_of_pins` concludes `STOptL2`, so the scan of `#assert_rbm_axioms` no longer lists `STOptL2` as assumed-but-unproved: in the pre-check output it is in the "registered premise(s) carry nothing yet" list (b.6, line 144), as `STLWB` and `STStep2` are (same list, b.6 output). The line is kept, with a comment; no new `Prop` definition and no new premise was introduced. The root `RBM3D.lean` does not import `OptL2b` (the hub adds it at merge), so the pre-check imports it explicitly (b.6); the full `lake build` of the worktree (b.7) does not contain `OptL2b`.

## (c) Verified Mathlib names (`#check @name` on `import RBM3D.Induction.OptL2b`, 26 names, all resolve; first 150 characters)
```
@Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
@Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
@Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
@Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
@Real.rpow_le_rpow_of_exponent_ge : ∀ {x y z : ℝ}, 0 < x → x ≤ 1 → z ≤ y → x ^ y ≤ x ^ z
@Real.rpow_one : ∀ (x : ℝ), x ^ 1 = x
@Real.rpow_two : ∀ (x : ℝ), x ^ 2 = x ^ 2
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ 
@Real.mul_rpow : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → (x * y) ^ z = x ^ z * y ^ z
@inv_mul_cancel₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a⁻¹ * a = 1
@div_le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : CommGroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}, 0 < b → 0 < d → (a 
@div_le_div_of_nonneg_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, a ≤ b → 0 ≤ c 
@Finset.measurable_sup' : ∀ {α : Type u_1} {m : MeasurableSpace α} {δ : Type u_2} [inst : MeasurableSpace δ] [inst_1 : SemilatticeSup α] [MeasurableSu
@Finset.sup'_apply : ∀ {α : Type u_1} {β : Type u_2} {C : β → Type u_3} [inst : (b : β) → SemilatticeSup (C b)] {s : Finset α} (H : s.Nonempty) (f : α
@Finset.lt_sup'_iff : ∀ {α : Type u_1} {ι : Type u_2} [inst : LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}, a < s.sup' H f ↔ ∃ b
@Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
@inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < b → b ≤ 
@inv_div : ∀ {α : Type u_1} [inst : DivisionMonoid α] (a b : α), (a / b)⁻¹ = b / a
@Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, 0 < c → (a ≤ b / c ↔ a * c ≤ 
@monotoneOn_const : ∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] {c : β} {s : Set α}, MonotoneOn (fun x => c) s
@Real.one_le_rpow_of_pos_of_le_one_of_nonpos : ∀ {x z : ℝ}, 0 < x → x ≤ 1 → z ≤ 0 → 1 ≤ x ^ z
@Real.inv_rpow : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x⁻¹ ^ y = (x ^ y)⁻¹
@Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
@Finset.prod_congr : ∀ {ι : Type u_1} {M : Type u_2} {s₁ s₂ : Finset ι} [inst : CommMonoid M] {f g : ι → M}, s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.prod
```
Names verified absent: none was needed. The helper names of this file are all prefixed `OptL2b_` (b.5); reused merged names: `stOptL2a_gronwall`, `OptL2a_sizedata`, `OptL2a_grid`, `OptL2aJ`, `OptL2alam`, `ST_gronwall`, `ST_prod_le_rpow`, `ST_PT_of_sections`, `ST_model_le_path`, `ST_gridTime_mem`, `ST_gridStep_nonneg`, `ST_size_pow_big`, `STBctl_mono`, `STBctl_pos`, `gridTime_last`, `StochDomAt.precomp_param`, `inst_optL2`, `conStInd_inst` (all resolved by the build).

## (d) Open issues and paper-delta candidates — Sun Oct  4 06:43:23 UTC 2026 (`date -u`)
- **Paper-delta candidate T2116a** (`3_5:508–509` "choose `𝔠_d` sufficiently small depending on `C₀`"): Lean gives `𝔠₀ = 1/(8 C₀ + 10)`, with `C₀` the constant of `stOptL2a_gronwall` (chosen after `κ ε 𝔡`, before `𝔠`, the sequences and `𝔠_d`); `STOptL2` has `∃ 𝔠₀` before `∀ 𝔠_d ≤ 𝔠₀`, `𝔠`, `sz`, `z`, `s`, `t`.
- **Paper-delta candidate T2116b** (`(eq:L-K2max)`, `3_5:504–509`): the paper bounds `ρ^{C₀}((W^{-d}B_{t,0})² + W^{-5c₀/4}) ≤ W^{-d}B_{t,0}` with the display `ρ^{C₀+5/4}(W^{-d}B_{t,0})^{1/4} ≪ 1`; Lean uses `B_s ≤ B_T` (`STBctl_mono`) instead of `B_t`, and proves each of the two terms `≤ B_T` exactly by the exponent count `1 + 𝔠_d(C₀ + 5/4) ≤ 5/4`, `1 + 𝔠_d C₀ ≤ 2`, `B_T ≤ 1` (no smallness of `B_T^{1/4}`), so the sum is `≤ 2 B_T` and the factor `2` is absorbed in `N^{τ'/2} ≥ 2` (the `≺` loss).
- **Carried from T2110, no new delta:** only the first conjunct of `(con_st_ind)` is used (T2110d); per time via `PrecPT`, no `N^{-C}`-net in `u` (T2110a); `hd : 3 ≤ d` (T2110f). The `(eq:opt_L2)` bound at the section `T = t` is `(eq:L-K2max)` itself; the sections `T = s` (`ρ = 1`) and `T < t` are covered by the same argument (the proof is uniform in `T`).
- **Open (not defects of this file):** (1) `stOptL2_of_pins` is conditional on the owed pins `STLWB` (LW gate) and `STGridMart` (ST2-12/13, via `STGridRepN`); (2) the examples keep `STLK`, `STStep1Loop`, `STStep1Weak` as hypotheses (other gates, §4 step 2); (3) the `STOptL2` registry line is kept with a comment (b.6); the dispatcher may decide to drop it once `STLWB` and `STGridMart` are proved; (4) `RBM3D.lean` needs `import RBM3D.Induction.OptL2b` after the last `import` line at merge (hub, CLAUDE.md §3 (A) step 4).
