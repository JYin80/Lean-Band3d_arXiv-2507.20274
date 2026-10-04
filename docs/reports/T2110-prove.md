Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 05:06:20 UTC 2026 (`date -u`)

Paper `3_5` = `paper/tex/3_5_Loop_Hierarchy.tex`. Scripts: `$S/T2110/{inst,gron,gron2}.py`, `$S` = session scratchpad. HEAD of main = 6187713.

### (i) Exponent table, proof map and cut

Notation (Lean): `B_u := sz.Bctl n u` (= `W^{-d}B_{u,0}`), `ρ := (1-s)/(1-t) ≥ 1`, `λ := ρ B_t` (the paper's `W^{-c₀}`, never named in Lean), `N = size`, `J_k := max_{σ,a} ‖STgA(k)‖`.

| quantity | value | constraint (where used) | slack |
|---|---|---|---|
| `C` of `STNewKLK` (`stNewKLK_holds`, `NewKLK:1198`) | `C(d,κ,𝔡)` | `0<C` | free of `W,L,λ,s,t` (§29) |
| `C₀` | `2C`: `‖Θ∘LK‖ ≤ C/(1-u)·Ĵ·prof`, `‖E^{LK×LK}‖ ≤ C/(1-u)(Ĵ+Ĵ²·1_{ℓ≥1})·prof`, `ℓ=0` kills `Ĵ²` (`Step2Defs:363`) | `β_j = C₀/(1-u_j) ≥ 0`, `u_j<1` | `prof` at `ℓ=0` is `W^{-d}max(𝒯(min(r,0)),W^{-D})`, constant in `a` (`Defs/Tail.lean:52`), so `Ĵ·prof = J` exactly |
| `𝔠₀` (pin: `∃ 𝔠₀>0` before the sequences) | `1/(8C₀+10)` | `𝔠_d(C₀+5/4) < 1/4` (the paper's last step) | `𝔠_d(C₀+5/4) ≤ 1/8`; slack `1/8` |
| `B_s²` term | `ρ^{C₀}B_s² ≤ B_t^{2-C₀𝔠_d}` | `C₀𝔠_d<1` | `C₀𝔠_d < 1/8` |
| `λ^{3/2}` term (`E^{G̃}`, `η⁻¹Ψ(0)Ψ²`) | `ρ^{C₀+3/2}B_t^{3/2}` | `𝔠_d(C₀+3/2) < 1/2` | `≤ 3/20`; slack `≥ 0.35` |
| `λ^{5/4}` term (martingale `(Σ_jΔ λ^{5/2}/η)^{1/2}`) | `ρ^{C₀+5/4}B_t^{5/4} = B_t·ρ^{C₀+5/4}B_t^{1/4}` | `≤ B_t·N^{-c/8}` | `B_t^{1/4-𝔠_d(C₀+5/4)} ≤ B_t^{1/8} ≤ N^{-c/8}` |
| size data (`ST_Bdata_holds`, `Step2Iterate:1049`) | `cB=(𝔡⁻²+1)⁻¹`, `c=min(2𝔡𝔠,ε)/2` | `cB W^{-d} ≤ B_u ≤ N^{-c}` eventually, `0≤u≤t` | `c` depends on `𝔠`; used only inside the proof (`𝔠` is after `𝔠₀`) |
| `ε₀` (`STPsiClass`, `STInitialGT2`) | `min(dc/4, d/4)` | `ε₀ ≤ d/2`; weak law `B^{1/4} ≤ N^{-c/4} ≤ W^{-dc/4}` (`ST_quarter_le`, `Events:329`) | `d/2-ε₀ ≥ d/4` |
| `Ψ n r` | `min(√λ_n, W_n^{-ε₀})` (constant in `r`) | `STPsiClass`: `0<Ψ≤W^{-ε₀}` for **all** `n` (`Step2Defs:333`); lower window and `(lokis2)` only `∀ᶠ n` | `√λ ≥ √cB W^{-d/2}`; `λ ≤ B_t^{1-𝔠_d} ≤ W^{-dc(1-𝔠_d)} ≤ W^{-2ε₀}` needs `𝔠_d ≤ 1/2` |
| `(lokis2)` (Lean) | `‖𝓛^{(2)}_u‖ ≺ ((1-s)/(1-u))B_s ≤ ρB_t = λ`, `u∈[s,t]` | `STBctl_mono` (`ScaleFacts:74`, `s≤t<1`) and `1-u ≥ 1-t` | `STStep1Loop` at `k=2` (`Defs:234`) |
| `1/η_u` | `η_u=(1-u)Im m(E) ≥ (1-u)√κ/2` (`ST_mE_im_ge`, `Events:555`) | `Δ Σ_{j<k} 1/η_{u_j} ≤ (2/√κ) log ρ` by `ST_logsum` (`Core:127`) | `log ρ ≤ 𝔠_d·log(B_t⁻¹) ≤ C' log N`, absorbed in `N^{c/64}` |
| grid | `K=⌈N^{C_K'}⌉`, `C_K' = max(C_K(D), 2(C_M+5))`, `Δ ≤ 1/K` | `Rem ≤ N^{C_M}√Δ ≤ N^{-5} ≪ λ^{5/4}`; `λ^{5/4} ≥ cB^{5/4}N^{-5/4}` | `N^{-5}` vs `N^{-5/4}` |
| tail / union | pin failure `N^{-D_pin}`, `D_pin = D+3`; `#STLab ≤ N^3` (`ST_card_lab_le`, `Events:172`), `(K+1)#V ≤ N^{C_K'+4}` | `ST_union_prob` (`Events:832`) | `N^{-D} ≤ λ^{5/2}` for `D≥3`, `N` large |
| whp losses | `ε₁=c/16` (weak law `N^{ε₁}B_t^{1/4} ≤ δ₀`), other `N^{τ'}` with `τ' ≤ c/64` | total loss `≤ N^{c/16}` against the gain `N^{-c/8}` | slack `N^{-c/16}` |

**Proof of `(eq:opt_L2)` and the cut.** Fix `d ≥ 3`, `κ,ε,𝔡`; `C,δ₀ := stNewKLK_holds d`, `C_M` from `STGridMart`, `𝔠₀` as above; `𝔠_d ≤ 𝔠₀`. For a time `T ∈ [s,t]` (a section) run the grid from `s` to `T`.
1. Initial value: `ST_grid_whp_zero` (`Events:118`) with `STLK` at `k=2` (`Defs:104`): `J_0 ≺ B_s²`. Map: merged.
2. Weak law `‖G−M‖_max ≤ δ₀` on all grid states: `ST_event_weak` (`Events:609`) with `STStep1Weak`. Map: merged, used with `T:=t`.
3. Drift of `(𝓛−𝒦)^{(2)}`: `STgDrift` (`Step2Defs:496`) = `Θ∘LK + E^{LK×LK} + E^{G̃}` for all `σ,a` (`HierarchyN2` is not needed: the pin `STGridMartAt` is stated with `STgDrift`). `‖Θ∘LK‖+‖E^{LK×LK}‖ ≤ C₀/(1-u_j)·J_j` from `stNewKLK_holds` at `ℓ=0, D=1`. **Target 1.**
4. `‖E^{G̃}_j‖ ≤ N^{τ'}η_{u_j}⁻¹Ψ(0)Ψ² = N^{τ'}η⁻¹λ^{3/2}` whp for all `j,σ,a`: `STLWB` (hypothesis) at each section through `ST_grid_whp_of_sections` (`Events:93`); premises: `STInitialGT2` (weak law `W^{-ε₀}` + `(lokis2)` for `STmaxLoop2`), `STLWassm` from `(lokis2)`, `STPsiClass` of `Ψ` above (model: `ST_LW_sections`, `Events:348`). **Target 1.**
5. Quadratic variation `‖STEEM_j‖ ≤ ‖STEEk_{0}‖+‖STEEk_{1}‖ ≤ N^{τ'}η⁻¹Ψ⁵ = N^{τ'}η⁻¹λ^{5/2}` whp: `stEMn2Poly_holds` (`EMn2Poly:838`), same premises as step 4, same bridge (model: `ST_event_mg`, `Events:710`). **Target 2.**
6. Martingale tail: the pin `STGridMartAt` (`Step2Defs:513`) gives, pathP-a.e., `A_k = A_0 + ΔΣ_{j<k}Drift_j + Rem_k + Mart_k`, `‖Rem‖ ≤ N^{C_M}√Δ`, `‖Mart_k‖ ≤ N^{ε'}(Σ_jΔ‖STEEM_j‖+N^{-D})^{1/2}` w.p. `≥ 1−N^{-D}`. With step 5 and `ST_logsum`: `‖Mart_k‖ ≤ N^{τ'}λ^{5/4}` whp. The paper's Markov step (`3_5:476–478`) is already inside the pin. **Target 2.**
7. Combination: whp, for all `k ≤ K`: `J_k ≤ α + ΔΣ_{j<k}β_jJ_j`, `α := N^{τ}(B_s²+λ^{5/4})` (constant, hence nondecreasing), `β_j = C₀/(1-u_j)`; the `E^{G̃}` sum is `≤ N^{τ'}(2/√κ)log ρ·λ^{3/2} ≤` the `λ^{5/4}` term. **Target 3 = end of ST2-14.**
8. (ST2-15) `ST_gronwall` (`Core:56`) with `ST_logsum`: `J_K ≤ α ρ_T^{C₀}`; compare with `B_T` by the table (`𝔠_d ≤ 𝔠₀`); transfer the endpoint `k=K` to the model by `ST_model_le_path` (`Events:566`); `PrecPT` by `ST_PT_of_sections` (`Core:500`).

**Cut (fixed).** ST2-14 ends with step 7, stated for a pair `(s,T)` with the hypotheses of `STOptL2` at `(s,T)`, concluding the whp inequality `J_k ≤ α_n + Δ Σ_{j<k} β_{n,j} J_{n,j}` for all `k ≤ K_n` with explicit `α_n, β_{n,j}` (the form `ST_gronwall` takes). ST2-15: restriction lemmas to `(s,T)`, steps 8, the choice of `𝔠₀`, the pin `stOptL2_of_pins`.

**§29 checks (1)–(4) and findings.**
- (1) `0≤s≤t≤lemT<1` (`lemT_lt_one`): gives `η>0`, `ρ ≥ 1>0`, `Ψ>0` for all `n`, `u_j<1`. PASS.
- (2) per-time vs uniform: the pin concludes `PrecPT` (`Step2Defs:667`). `ST_PT_of_sections` turns per-section `Prec` into it, so **no net/perturbation in `u` is needed** (the paper's `N^{-C}`-net is for the uniform statement, which the pin does not claim). `STStep1Loop/Weak` are uniform `Prec`, so they restrict to any section.
- **Finding F1 (boundary, §29 (1),(4))**: for a section `T_n` the argument needs `STConStInd` only through its first conjunct `B_T^{𝔠_d} ≤ (1-T)/(1-s)`, which restricts from `(s,t)` by `STBctl_mono`; the second conjunct `(1-T)/(1-s)<1` fails when `T_n=s_n`. So the ST2-14 theorem takes **only the first conjunct** (`∀ᶠ n`), and `STStep1Loop/Weak` restricted to `TimeIcc s T ⊆ TimeIcc s t`. Without this the `T=s` sections are lost.
- **Finding F2 (§29 (4))**: `STPsiClass` has `∀ n` clauses; `Ψ := √λ` can violate `Ψ ≤ W^{-ε₀}` at finitely many `n`, hence `Ψ := min(√λ, W^{-ε₀})` (equal to `√λ` eventually; the pins `STLWB`, `stEMn2Poly_holds` only use `Prec`, eventual).
- **Finding F3 (`3 ≤ d`)**: `STOptL2 d`, `STLWB d` have no `3 ≤ d`, `STNewKLK d` is `3 ≤ d → …`. The ticket's `stOptL2_of_pins : STLWB d → STGridMart d → STOptL2 d` cannot be proved for `d ≤ 2`; it needs `(hd : 3 ≤ d)` (as DECISIONS §31 for the LW bridges). Pins unchanged. Targets of ST2-14 take `hd`.
- (3) `L^d ≤ W^K` is not used: only `L^d ≤ N` (`ST_card_lab_le`). PASS.

### (ii) Concrete instance and scripts

Data: `d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`), `z0`, `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (`Induction/Defs.lean:435`), `s≡0`, `t≡1/16 ≤ lemT(z0_n)` (`sixteenth_le_lemT`, `Defs.lean:429`), `ρ=16/15`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `C=δ₀=C_M=1`, `C₀=2`, `𝔠_d=𝔠₀=1/26`. Hypotheses `STLK`, `STStep1Loop`, `STStep1Weak`, `STLWB`, `STGridMart` are other gates' pins: they stay hypotheses of the example. Deterministic data checked by `cd $S/T2110 && python3 inst.py` (columns: `B_t^{𝔠_d} ≤ 15/16`; `cB W^{-3} ≤ λ`; `λ ≤ B_t^{1-𝔠_d}` and `≤ W^{-2ε₀}`; `N^{ε₁}B_t^{1/4} ≤ δ₀`; `-log R/log N` with `R = ρ^{C₀}(B_s²+λ^{5/4})/B_t`, to be `≥ c/8`; `Rem`, `Mart` floors):
```
cB=0.00990099 c=0.0166667 C0=2 cd=1/26  cd*(C0+5/4)=0.1250 (<1/4)  cd*C0=0.0769 (<1)  cd*(C0+3/2)=0.1346 (<1/2)
n  logN   conSt(<=15/16) PsiLo PsiHi  weak  loss-slack(-logR/logN vs c/8)  RemFloor  MartFloor
0      6.32  0.6725 True  True  True  True   0.1628 True  True  True
1     11.74  0.4506 True  True  True  True   0.1839 True  True  True
2     14.91  0.3566 True  True  True  True   0.1891 True  True  True
5     20.33  0.2390 True  True  True  True   0.1943 True  True  True
10    25.07  0.1685 True  True  True  True   0.1969 True  True  True
100   42.40  0.0469 True  True  True  True   0.2016 True  True  True
1000  60.33  0.0125 True  True  True  True   0.2036 True  True  True
c/8 = 0.0020833333333333333 ; time domain: s=0<=t=1/16<=lemT(z_n) (merged sixteenth_le_lemT), t<1
```
(`n=3,4` rows are also all `True`; `log10 N` is printed under the header `logN`.) Limits for the external-type hypotheses at this data: `B_t ≤ 1.1 W^{-3} → 0` and `N→∞` (`sz0_admissible`, merged); `B_t^{𝔠_d}` decreases from `0.6725` to `0.0125` (the `STConStInd` condition holds at every sampled `n`: 0–5, 10, 100, 1000).

(iii) Scalar Grönwall step `(eq:Gronwall_2L_max) → (eq:L-K2max)`, `d=3`, `B=W^{-b}`, worst case `B_s=B_t=B`, `ρ` on a 61-point grid of `[1, B^{-𝔠_d}]`: check `ρ^{C₀}(B²+λ^{5/4}+(2/√κ)log ρ·λ^{3/2}) ≤ B`, `κ=1/10`; `python3 gron2.py` (columns: largest admissible `𝔠_d` by bisection; `1/(4C₀+5)`; ratio `LHS/B` at `𝔠₀=1/(8C₀+10)`, `ρ=B^{-𝔠₀}`):
```
W      C0  B=W^-b  cd_max      1/(4C0+5)  ratio(cd0,rho_max)<=1
2^4    1   W^-1    0.04481    0.11111    1.1380 False        (W^-0.2: cd_max 0, ratio 1.6848; W^-3: 0.08406, 0.4989 True)
2^4    5   W^-1    0.02370    0.04000    0.9153 True         (W^-0.2: cd_max 0, ratio 1.5973; W^-3: 0.03565, 0.4026 True)
2^4    20  W^-1    0.00870    0.01176    0.8303 True         (W^-0.2: cd_max 0, ratio 1.5629; W^-3: 0.01134, 0.3680 True)
2^8    1   W^-1    0.06950    0.11111    0.7684 True         (W^-0.2: cd_max 0, ratio 1.4825; W^-3: 0.10480, 0.1394 True)
2^8    5   W^-1    0.03225    0.04000    0.5969 True         (W^-0.2: cd_max 0, ratio 1.3322; W^-3: 0.03929, 0.1295 True)
2^8    20  W^-1    0.01087    0.01176    0.5335 True         (W^-0.2: cd_max 0, ratio 1.2737; W^-3: 0.01171, 0.1262 True)
2^64   1   W^-0.2  0.08636    0.11111    0.4567 True         (W^-1: 0.11109, 0.0039; W^-3: 0.11111, 0.0000)
2^128  1   W^-0.2  0.10602    0.11111    0.1191 True         (W^-1, W^-3: 0.11111 = 1/(4C0+5))
2^128  5   W^-0.2  0.03945    0.04000    0.1120 True         (W^-1, W^-3: 0.04000)
2^128  20  W^-0.2  0.01172    0.01176    0.1097 True         (W^-1, W^-3: 0.01176)
```
Reading: `cd_max → 1/(4C₀+5)` as `W→∞` (the binding term is `ρ^{C₀+5/4}B^{1/4}`); `𝔠₀=1/(8C₀+10)` is half of it. The failures at `W ∈ {2⁴,2⁸}`, `B=W^{-0.2}` (and `2⁴, C₀=1, b=1`) are the finite-`W` size of `B^{1/4}` (at `ρ=1`, independent of `𝔠_d`: `0.2`-column `cd_max=0`); the statements are `≺`/`∀ᶠ n` with `B_t ≤ N^{-c}`, so only the asymptotic reading is claimed, and `inst.py` shows the instance data satisfies the finite check from `n=0`.

### Verdicts
- Target 1 (drift bound `(l>0EQ)`): PASS (steps 3–4; `C₀=2C`; `E^{G̃}` through the hypothesis `STLWB`).
- Target 2 (martingale bound): PASS (steps 5–6; `STGridMart` hypothesis; `stEMn2Poly_holds` merged).
- Target 3 (form for `ST_gronwall`): PASS with F1 (first conjunct of `STConStInd` only, restricted pins), F2 (`Ψ` as a `min`), F3 (`hd : 3 ≤ d` for the ST2-15 end theorem; dispatcher to amend the ticket text, no pin changes).
- Paper-delta candidates for the prover to propose: `T2110a` (the paper's `N^{-C}`-net is not needed for the per-time pin), `T2110b` (the paper's `W^{-c₀}` is `ρ B_t` in Lean; `(lokis2)` is derived from `STStep1Loop` plus `STBctl_mono`).

## (b) Script output — Sun Oct  4 05:46:05 UTC 2026 (`date -u`); worktree `RBM3D-wt/T2110`, branch `t/T2110`, sole file `RBM3D/Induction/OptL2a.lean`

```
$ git log -1 --format=%h; wc -l
879daff 1486 lines
$ lake build RBM3D.Induction.OptL2a 2>&1 | tail -1
Build completed successfully (3766 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/OptL2a.lean
0
$ lake env lean axioms.lean   (one #print axioms per new public declaration; counts)
declarations printed: 38; with exactly [propext, Classical.choice, Quot.sound]: 38
'RBM.Gauss.Sizes.stOptL2a_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stOptL2a_martingale' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stOptL2a_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
$ registry pre-check: printf "import RBM3D\nimport RBM3D.Induction.OptL2a\n#assert_rbm_axioms\n" | lake env lean ; echo exit
exit=0
axiom audit: 3403 theorems, 1223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ name-clash grep of every new name (theorem/def, incl. private) in main (RBM3D/, RBM3D.lean), excluding OptL2a.lean itself
names: 39  clashes: 0
$ git diff --stat main...t/T2110
 RBM3D/Induction/OptL2a.lean | 1486 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1486 insertions(+)
$ (temporary root import `import RBM3D.Induction.OptL2a` after the last import of RBM3D.lean, then `lake build`, then the line removed again; not committed)
info: RBM3D.lean:156:0: axiom audit: 3403 theorems, 1223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3857 jobs).
```

Target statements, extracted by `python3 extract.py stOptL2a_drift stOptL2a_martingale stOptL2a_gronwall` (OptL2a.lean at 879daff):
```lean
-- OptL2a.lean:983
theorem stOptL2a_drift {d : ℕ} (hd : 3 ≤ d) (hLWB : STLWB d)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ lemT (z n)) →
        ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1Loop sz (STflowE z) s T → STStep1Weak sz (STflowE z) s T →
          ∀ τ : ℝ, 0 < τ → ∀ CK : ℝ, 0 ≤ CK → ∀ K : ℕ → ℕ,
            (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
                ‖STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω‖ ≤
                  C₀ / (1 - gridTime s T K n j) *
                      OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) +
                    ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
                      (OptL2alam sz s T n) ^ (3 / 2 : ℝ))}) := by
-- OptL2a.lean:1078
theorem stOptL2a_martingale {d : ℕ} (hd0 : 0 < d) (hGM : STGridMart d)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ lemT (z n)) →
        ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1Loop sz (STflowE z) s T → STStep1Weak sz (STflowE z) s T →
          ∀ τ : ℝ, 0 < τ → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
            ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
                (∀ n i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                  STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
                    STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
                        Rem n i k ω + Mart n i k ω) ∧
                (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                  ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)) ∧
                (∀ᶠ n in atTop, pathP sz {ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ τ * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) := by
-- OptL2a.lean:1260
theorem stOptL2a_gronwall {d : ℕ} (hd : 3 ≤ d) (hLWB : STLWB d) (hGM : STGridMart d)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ lemT (z n)) →
        STLK sz (STflowE z) s → ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1Loop sz (STflowE z) s T → STStep1Weak sz (STflowE z) s T →
          ∀ τ : ℝ, 0 < τ → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
            ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              ∀ᶠ n in atTop, pathP sz {ω | ¬ ∀ k, k ≤ K n →
                OptL2aJ sz n (STflowE z n) (gridTime s T K n k) (pathH sz s T K n k ω) ≤
                  ((sz.size n : ℕ) : ℝ) ^ τ *
                      ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
                    gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
                      OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω)} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
```

Compiled nonempty instances (`sed -n 1436,1485p OptL2a.lean`): `sz0`, `z0`, `flow_z0`, `s ≡ 0`, `T ≡ 1/16 ≤ lemT z_n`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `𝔠_d=1/26`, `τ=D=1`; discharged: `STFlow`, time ranges, `𝔠_d ≤ 1/2`, the first conjunct of `(con_st_ind)` (`conStInd_inst`); hypotheses of the examples: the pins `STLWB`, `STGridMart` and the premises `STLK`, `STStep1Loop`, `STStep1Weak`.
```lean
private theorem OptL2a_hcon :
    ∀ᶠ n in atTop, (sz0.Bctl n (tInst n)) ^ (1 / 26 : ℝ) ≤ (1 - tInst n) / (1 - sInst n) :=
  (conStInd_inst (by norm_num : (0 : ℝ) < 1 / 26)).mono fun n hn => hn.1

/-- **Target 1 at the data**: the drift bound on the grid `K_n = ⌈N_n⌉` from `0` to `1/16`. -/
example (hLWB : STLWB 3) (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ)⌉₊) →
      Gauss.HighProbAt (pathP sz0) sz0.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz0 n,
        ‖STgDrift sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω‖ ≤
          C₀ / (1 - gridTime sInst tInst K n j) *
              OptL2aJ sz0 n (STflowE z0 n) (gridTime sInst tInst K n j)
                (pathH sz0 sInst tInst K n j ω) +
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) *
              ((etaT (STflowE z0 n) (gridTime sInst tInst K n j))⁻¹ *
                (OptL2alam sz0 sInst tInst n) ^ (3 / 2 : ℝ))}) := by
  obtain ⟨C₀, hC₀, h⟩ := stOptL2a_drift (d := 3) le_rfl hLWB (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C₀, hC₀, fun K hK => h (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT (1 / 26)
    (by norm_num) OptL2a_hcon hS1L hS1W 1 one_pos 1 zero_le_one K hK⟩

/-- **Target 2 at the data**: the grid decomposition of `STGridMart` with `|Rem| ≤ N^{-2}` and
`|Mart_k| ≤ N λ^{5/4}` w.h.p. -/
example (hGM : STGridMart 3) (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :=
  stOptL2a_martingale (d := 3) (by norm_num) hGM (1 / 10) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT (1 / 26)
    (by norm_num) OptL2a_hcon hS1L hS1W 1 one_pos 1 one_pos

/-- **Target 3 at the data**: `(eq:Gronwall_2L_max)` on the grid from `0` to `1/16`. -/
example (hLWB : STLWB 3) (hGM : STGridMart 3) (hLK : STLK sz0 (STflowE z0) sInst)
    (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ CK : ℝ, 0 ≤ CK ∧ ∀ K : ℕ → ℕ,
      (∀ n, K n = ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊) →
        ∀ᶠ n in atTop, pathP sz0 {ω | ¬ ∀ k, k ≤ K n →
          OptL2aJ sz0 n (STflowE z0 n) (gridTime sInst tInst K n k) (pathH sz0 sInst tInst K n k ω) ≤
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) *
                ((sz0.Bctl n (sInst n)) ^ 2 + (OptL2alam sz0 sInst tInst n) ^ (5 / 4 : ℝ)) +
              gridStep sInst tInst K n * ∑ j ∈ Finset.range k,
                C₀ / (1 - gridTime sInst tInst K n j) *
                  OptL2aJ sz0 n (STflowE z0 n) (gridTime sInst tInst K n j)
                    (pathH sz0 sInst tInst K n j ω)} ≤
          ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  obtain ⟨C₀, hC₀, h⟩ := stOptL2a_gronwall (d := 3) le_rfl hLWB hGM (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CK, hCK0, h'⟩ := h (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT hLK (1 / 26)
    (by norm_num) OptL2a_hcon hS1L hS1W 1 one_pos 1 one_pos
  exact ⟨C₀, hC₀, CK, hCK0, h'⟩
```

Ports: none (new file; nothing copied from `../RBM1D` or `../RBM2D`, so no `diff --stat` against them).

Narrative (section (a) used unchanged; no (a′): no verdict of (a) changed):
- Targets to theorems. T1 `stOptL2a_drift` (`(l>0EQ)`): `stNewKLK_holds` at `ℓ=0, D=1` bounds `Θ∘LK + E^{LK×LK}` by `2C(1-u)⁻¹ J` (`OptL2a_drift_matrix`/`_grid`; at `ℓ=0` the `Ĵ²` term is absent and `STprof` is constant in `(a,b)`, `OptL2a_prof_zero`); `E^{G̃}` comes from the pin `STLWB` at every grid time through `ST_grid_whp_of_sections`. T2 `stOptL2a_martingale`: `(eq:MG_conclusion)` from `stEMn2Poly_holds` at every grid time, `Δ Σ_j η_{u_j}⁻¹ ≤ q log ρ` (`ST_logsum`), `q log ρ ≤ N^ε` (`OptL2a_q_log_le`), the Markov step is the tail clause of the pin `STGridMart`. T3 `stOptL2a_gronwall`: Targets 1, 2 and the initial value `J_0 ≺ B_s²` (`STLK` at `k=2`, `ST_grid_whp_zero`) combined by `ST_pathwise_ineq` with `P ≡ 1` (`OptL2a_pathwise`); `α` is constant in `k`, so `ST_gronwall` applies with `β_j = C₀/(1-u_j)`.
- Constants and quantifiers (DECISIONS §29): `C₀ = 2C`, `(C,δ₀)` from `stNewKLK_holds`, chosen right after `κ ε 𝔡` and before the sequences; the grid exponent `CK` is chosen after `τ, D`: in T2 `CK = max(CK₀(Dm), 2(C_M+2))`, `Dm = D+4`, `K_n = ⌈N^CK⌉` (T3 takes the `CK` of T2 at `(τ/2, D+4)`); all `≺` are `HighProbAt`/eventual in `n`, never `∀ n`.
- Hypotheses against (a): only the first conjunct of `STConStInd` (F1) with `𝔠_d ≤ 1/2`; `3 ≤ d` in T1 and T3 (`stNewKLK_holds` begins `3 ≤ d →`, F3), T2 needs `0 < d` only and no `STLWB`. `Ψ = min(√λ, W^{-ε₀})` (F2, `OptL2aPsi`), `ε₀ = d c/4` with `c` of `ST_Bdata_holds` replaced by `min(c,1)` (`OptL2a_sizedata`); `OptL2a_premises` builds `STPsiClass`, `STInitialGT2`, `STLWassm` at a section from Step 1, `(lokis2)` is `OptL2a_loop_ctl`. Loss exponents differ from the row `whp losses` of (a): `τ/8` for the events, `c/8` for the weak law, remainder `N^{-2}` (not `N^{-5}`); all within the slack of (a).
- Left to ST2-15 (not done here): `ST_gronwall` with `ST_prod_le_rpow`, the choice `𝔠₀ = 1/(8C₀+10)`, restriction of `STConStInd`, `STStep1Loop`, `STStep1Weak` from `[s,t]` to `[s,T_n]`, `ST_model_le_path`, `ST_PT_of_sections`, `hd : 3 ≤ d` in `stOptL2_of_pins`.
- No `set_option maxHeartbeats`, no `sorry`; `Test/Axioms.lean` untouched: `OptL2aJ`, `OptL2alam`, `OptL2aPsi` are real-valued, there is no new `Prop`-valued definition (registry pre-check above exits 0). Public helpers carry the file-stem prefix `OptL2a`.

## (c) Mathlib names used (all confirmed by `#check` in the project environment: 64 names, 0 errors; none found absent; none invented)
Complex.norm_real Finset.le_sup' Finset.mem_range.mp Finset.mem_range.mpr Finset.mem_univ Finset.mul_sum
Finset.sum_congr Finset.sum_le_sum Finset.sup'_le Finset.univ.sup' Nat.cast_nonneg Nat.ceil_pos.2 Nat.le_ceil
Nat.lt_succ_of_le Real.div_rpow Real.inv_rpow Real.log_le_log Real.log_le_rpow_div Real.log_nonneg Real.log_rpow
Real.mul_rpow Real.norm_of_nonneg Real.one_le_rpow Real.rpow_add Real.rpow_add' Real.rpow_le_one
Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_ge
Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_mul Real.rpow_natCast Real.rpow_neg
Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.sq_sqrt Real.sqrt_eq_rpow Real.sqrt_le_sqrt Real.sqrt_mul
Real.sqrt_pos.2 Real.sqrt_sq add_le_add_left ae_all_iff ae_iff div_le_div_of_nonneg_left div_le_div_of_nonneg_right
inv_anti₀ inv_div le_div_iff₀ le_inv_mul_iff₀ le_mul_of_one_le_left measure_empty measure_mono measure_union_le
mul_inv mul_le_of_le_one_left norm_sum_le not_lt not_not pow_le_pow_left₀ pow_le_pow_of_le_one pow_le_pow_right₀

## (d) Open issues and paper-delta candidates
- `T2110a` (from (a)): the paper's `N^{-C}`-net and perturbation in `u` is not needed for the per-time pin `STOptL2` (`PrecPT`, `ST_PT_of_sections`).
- `T2110b` (from (a)): the paper's `W^{-c₀}` of `(lokis2)` is `λ = ((1-s)/(1-T)) W^{-d}B_{T,0}` (`OptL2alam`); `(lokis2)` is derived from `STStep1Loop` and `STBctl_mono` (`OptL2a_loop_ctl`).
- `T2110c`: the paper's `Ψ_t` of `(eq:Psi)` is realised as `min(√λ, W^{-ε₀})` because `STPsiClass` asks `0 < Ψ ≤ W^{-ε₀}` for every `n`.
- `T2110d`: `(con_st_ind)` enters through its first conjunct `B_T^{𝔠_d} ≤ (1-T)/(1-s)` and `𝔠_d ≤ 1/2` only; its second conjunct fails for the section `T = s`.
- `T2110e`: the paper's `O_≺` terms are explicit here: initial value `N^τ B_s²`, remainder `≤ N^{-2}`, martingale `≤ N^τ λ^{5/4}`, light-weight drift `≤ N^τ η⁻¹ λ^{3/2}`; the Grönwall right side has a constant `α` (nondecreasing) and `β_j = C₀/(1-u_j)`.
- `T2110f`: ticket text for ST2-15: `stOptL2_of_pins` needs `(hd : 3 ≤ d)` (pins unchanged); `stOptL2a_martingale` needs only `0 < d`.
- Open: `STLWB` and `STGridMart` stay owed (registry); the examples keep `STLK`, `STStep1Loop`, `STStep1Weak` as hypotheses (stochastic premises of Step 1 and the induction).
- Hub: at merge add `import RBM3D.Induction.OptL2a` after the last `import` line of `RBM3D.lean` (tested temporarily above; not committed).
