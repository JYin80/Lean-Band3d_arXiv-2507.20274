Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 08:23:33 UTC 2026

Notation: `u = 1/N`, `N = (W L)^d`, `η = Im z`, `t₀ = Im m/(Im m + Im z)`, `κ' = (πκ)^5/2048` (`ba_dom_of_bulk`, RandomLayerBGBA:69, any `L, g`, `0 < Im z ≤ 1`),
`C₀ = κ'^{-2}(1 + κ'^{-2})`, `R = 2 + 2d/𝔡`, `C_R = 4R + 2` (T2514 1a (a′) 3). T2514 row a is on `main` (`git log`: 3a67e18d), so ticket F1 "unmerged" is stale: `BA/MAPins`, `BA/MALocal` are on `main`.
Scripts (numpy, no Lean): `.../scratchpad/T2516/inst.py`, `thr.py`. `S0` = class `(L, g) = (4, 3/10)`, `W_n = (2(n+1))^5`, `(𝔠, 𝔡) = (1/6, 1/10)`; numeric stand-in `λ = 0.3`, `κ = 1/4` (`ρ(0) = 0.2636`).

### (i) Exponent table
| # | quantity (target) | value | constraint | slack |
|---|---|---|---|---|
| 1 | `κ'` (6, 8) | `(πκ)^5/2048` | `Im m ≥ κ'` on `{BAbulk κ (Re z), 0 < Im z ≤ 1}`; domain empty if `κ > 1/π` (`Im m ≤ 1`, `BAm_norm_le_one` Ward:136) | `κ'(1/4) = 1.4592e-4`; `ρ(0) = 0.2636 ≥ 1/4` |
| 2 | `‖M(z)−M(w)‖_{L²op}` (6) | `≤ C₀ ‖z−w‖` | `cont_green_diff` (ContinuityNet:448) at `H = λΨ_B`, `q = z+m`, `Im q ≥ κ'`; `|Δq| ≤ (1+κ'^{-2})|z−w|` (`BAm_sub_le_of_im` MReg:84) | `C₀(1/4) = 2.2056e15`; numeric max `‖ΔM‖/(c^{-2}(1+c^{-2})|Δz|) = 0.2576`, `c = min Im m` |
| 3 | `‖Q(z)‖_{∞→∞}` (6), `Q = BAMss(M,+,σ)` | `= t₀ < 1` (row sums `Σ_b|M_ab|²`, both `σ`, `M` symmetric `BAMB_symm` Ward:83; `BAMB_ward_row` Ward:108) | `‖Θ‖ ≤ (1−t₀)^{-1} = (Im m+η)/η ≤ 2/η` (`Im m ≤ 1`, `η ≤ 1`; from `Θ(1−Q) = 1`, `‖Θ‖(1−‖Q‖) ≤ 1`, `Ring.inverse_mul_cancel`) | numeric `|‖Q‖_∞ − t₀| ≤ 2.1e-15`; `max ‖Θ‖η/2 = 0.7354 ≤ 1` |
| 4 | `ProfLip` constant `C` (6) | pin `C = 12 C₀`; derivation `8 C₀`: `ΘQ = Θ−1`, `Θ−Θ' = Θ(Q−Q')Θ'`, `‖Q−Q'‖_∞ ≤ 2 max_a ‖row_a ΔM‖₂ ≤ 2‖ΔM‖_op` (row `ℓ²` ≤ `L²op`: `l2_opNorm_conjTranspose` Mathlib CStarAlgebra/Matrix:204, `l2_opNorm_mulVec`) | `|Δprof_ab| ≤ (2/η)² 2‖ΔM‖ = 8η^{-2}‖ΔM‖ ≤ 8C₀ η^{-2}|z−w|`, then `/W^d` | pin has factor 1.5 slack; numeric `max|ΔBAprof|W^dη²/|z−w| = 0.4519` vs `C = 2.6467e16`; `max ‖Q−Q'‖/(2‖ΔM‖) = 0.6451`; `max |Δprof|/(8η^{-2}‖ΔM‖) = 0.1573` |
| 5 | mesh and cover (8) | `‖z−w‖ ≤ 2u⁷` (`MALocal_geom`, private, MALocal:571), `η ≥ u` | `G`: `2u⁵·2u^{-1} = 4u⁴`; profile: `12C₀u^{-2}·2u⁷ = 24C₀u⁵ ≤ 24u⁴` iff `C₀ ≤ N` (= T2514's `hCN`); `E ≤ 28u⁴ ≤ 4u⁴+24u³ ≤ u²` (private `znet_num2` ZNet:674 reused, `u ≤ 1/32`) | no new threshold; at the instance below `E = 1.07e-60 ≤ u² = 1.97e-31`; shift `2u⁷ ≤ u/2` |
| 6 | `N`-thresholds (5, 8) | `32 ≤ N`, `C_R ≤ N`, `C₀ ≤ N` (all eventual, `SizeTendsto`) | binding one is `C₀` | `S0`, `κ = 1/4`: first `n = 3`, `N = 2.252e15 ≥ C₀ = 2.2056e15`; `C_R = 250` and `32` are below `C₀`, not binding |
| 7 | `W`-thresholds (3, 5, 8) | probability halves `5 ≤ W^{τ'/2}` at `τ' ∈ {τ, τ/2}` (fixed call at `τ/2` inside the net, cover at `τ`); expectation half `8 ≤ W^{τ/2}` (no lift) | eventual (`tendsto_W`) | `τ = 1`: `W_3 = 32768`, `W^{1/2} = 181.02`, `W^{1/4} = 13.45`; `τ = 1/2`: first `n = 6`; `τ = 1/10`: `n = 195312` (eventual, not a witness) |
| 8 | floor exponent (3, 5) | `D_dec = 6/(5𝔠)`, `W^{-D_dec} ≤ 𝓑_{η,0}^{1/5}𝓑_{η,K}` (`floor_X` FixedZ:222, needs `N^𝔠 ≤ W`, `η ≤ 1`) | `D_dec = 7.2` at `𝔠 = 1/6`; equality case of `N ≤ W^{1/𝔠}`, `𝓑 ≥ N^{-1}` | `W^{-7.2} = 3.08e-33 ≤ N^{-6/5} = 3.78e-19` (`n = 3`) |
| 9 | union (5, 8) | fixed call at `(κ, ε, τ/2, D+15)`; count `≤ C_R N^{14}`; fixed form: two halves `N^{-(D+1)}` (`two_rpow_le` FixedZ:358, `N ≥ 2`) | `C_R N^{14} N^{-(D+15)} = C_R N^{-1} N^{-D} ≤ N^{-D}` iff `C_R ≤ N` | `D = 1`: `4.93e-29 ≤ 4.44e-16` |
| 10 | transfer data (1, 2) | `BAzztE_data` (MFixedPoint:297): `t₀ ∈ (0,1)`, `m₀ = m/√t₀`, `g₀ = √t₀ λ`, `E = BAflowE`, `ztOf = √t₀ z`, `√t₀ M₀ = M`; `BAdom_real` (:479) at `κ_f := Im m(z) > 0` (`BAm_self`); `BASelf_unique` (:715) gives `BAmF = m₀`; `Gt_BA` (BlockAnderson:112) | `0 < g₀` iff `0 < sz.lam n`: eventual (`WO`, Defs/Sizes:164: `W^{-d/2+𝔡} ≤ λ`); `baKsol_two` (KInduct:88) needs `0 < κ_f`, `0 < g₀`, `3 ≤ L`, `t₀ ∈ [0,1)` | numeric: `|selfcons(m₀)| ≤ 1.1e-16`, `|√t₀M₀−M| ≤ 4.4e-16`, `|prof − t₀Θ_{t₀}Q₀| ≤ 4.2e-15` (both `σ`, 2 points), `Gt_BA` `1.0e-15`; `ΘQ` symmetric `8.4e-15` (orientation `(b,a)` vs `(a,b)`) |
| 11 | `ε`, end domain (5, 8) | `Im z ≥ N^{-1+ε} ≥ u` for `ε ≥ 0`; `N^{-1+ε} ≤ 1` needs `ε ≤ 1` | `ε > 1`: end domain empty for `N > 1` (vacuous); else sections run at `ε' = min(ε, 1)`, `κ_f` of T2514 row 10 (`MALocal_kappa_floor`) | `N^{-0.9} = 1.52e-14 ≥ u = 4.44e-16` |
| 12 | `B`-constants at `t₀` (3) | `STWB(t₀,k) ≤ 2𝓑_{η,Wk}`, `Bctl ≤ 2𝓑_{η,0}` (`MALocal_STWB_le` :293, `MALocal_Bctl_le` :322, public) replace band `btBt`; `hre` drops out | factor 2 independent of `κ'`; `qd_core`/`qd_exp_core` bodies reused | none lost |

### (ii) One concrete nondegenerate instance (`d = 3`, `S0`, `n = 3`, `κ = 1/4`, `ε = 1/10`, `τ = 1`, `D = 1`)
Data: `L = 4`, `W = 32768`, `N = 2.2518e15`, `λ = 0.3` stand-in (the Lean `S0 = clsS 4 _ _` has `λ = (fp 4 _).g0 ≤ 3/10`, UNPins:851, :887; `ρ`-numerics are at `λ = 0.3`), `z = 0.5 i`, `0.05 + 0.3 i`, `E_* = 0`.
Hypotheses of the targets: `3 ≤ d`; `S0_adm` (UNPins:887); `κ, ε, τ, D > 0`; `0 < Im z ≤ 1`; `0 < λ`; `UNMLOutBA 3 = unMLOutBA_three` (merged, MainIndTermBA:47, no binder); the Lean `example`s (T2449 probe 277-286) apply at `(1/6, 1/10, S0, clsκ, 1/20, 1/10, 2)`. External hypotheses: none. `d > 3` carries `STStep5IIIgL d` (out of scope, ticket Rules).
Limits: `N_n = 64(2(n+1))^{15} → ∞`; `W_n^6 ≥ N_n`, so `N^{1/6} ≤ W` (`N^{1/6} = 362.04 ≤ 32768`); `W^{-1.4} = 4.77e-7 ≤ 0.3 ≤ 𝔡^{-1} = 10`. All `∀ᶠ n` statements need only these limits; `n = 3` is where all thresholds of rows 6-9 first hold at `τ = 1`, `N ≈ 2e15` because `C₀ ≈ 2.2e15` is a constant of `κ`, not an artefact of the statement.
Commands and verbatim output (`cd .../scratchpad/T2516 && python3 thr.py; python3 inst.py`):
```
kappa'=1.4592e-04 C0=2.2056e+15 R=62.0 C_R=4R+2=250.0  ProfLip C=12*C0=2.6467e+16 (8*C0=1.7645e+16 suffices)
S0 tau=1.0: first n with N>=max(32,C_R,C0): 3 (N=2.252e+15); first n with the N-thresholds, W^(tau/2)>=8, W^(tau/4)>=5: 3 (N=2.252e+15, W^(tau/2)=181.02)
S0 tau=0.5: first n with N>=max(32,C_R,C0): 3 (N=2.252e+15); first n with the N-thresholds, W^(tau/2)>=8, W^(tau/4)>=5: 6 (N=9.956e+18, W^(tau/2)=27.08)
S0 tau=0.1: first n with N>=max(32,C_R,C0): 3 (N=2.252e+15); first n with the N-thresholds, W^(tau/2)>=8, W^(tau/4)>=5: 195312 (N=4.815e+85, W^(tau/2)=25.00)
instance (tau=1) n=3: L=4 W=32768 N=2.2518e+15 u=1/N=4.441e-16; N^(1/6)=362.04 <= W: True; lam=0.3 in [W^(-1.4), 10]: True
  floor decay exponent 6/(5c)=7.2: W^-(6/(5c))=3.081e-33 <= N^(-6/5)=3.775e-19: True
  cover budget: G part 2u^5*2/u=1.556e-61; profile part 12*C0*u^-2*2u^7=9.143e-61 (<=24u^4=9.335e-61: True); E=1.070e-60 <= u^2=1.972e-31: True; 28u^4 <= 4u^4+24u^3: True
  mesh/shift: |dIm|<=2u^7=6.81e-108 <= u/2=2.22e-16: True; floor Im z >= N^(-1+eps)=1.523e-14 >= u: True
  union: C_R N^14 N^-(D+15) = 4.930e-29 <= N^-D = 4.441e-16: True
  expectation half: W^(tau/2)=181.02 >= 8: True; probability halves: W^(tau/4)=13.45 >= 5 (fixed call at tau/2), W^(tau/2) >= 5 (cover)
kappa=0.25 rho(0)=0.263612 rho(0.05)=0.263537 rho(-0.05)=0.263537  kappa'=1.4592e-04  C0=kappa'^-2(1+kappa'^-2)=2.2056e+15  C=12*C0=2.6467e+16
72 pairs (eta in {0.9,0.3,0.05,0.005}, E in {0,+-0.05}, sigma=+-):
  max | ||Q||_inf - t0 | = 2.11e-15   max ||Theta|| eta/2 = 0.7354 (<=1)   max Theta*Q asym = 8.44e-15
  max ||Q-Q'||_inf/(2||dM||_op) = 0.6451 (<=1)   max ||dM||_op/(c^-2(1+c^-2)|dz|) = 0.2576 (<=1)
  max |dprof|/(8 eta^-2 ||dM||_op) = 0.1573 (<=1);  max |dBAprof| W^d eta^2/|z-w| = 4.5185e-01  vs C = 2.6467e+16: True  (ratio/C = 1.71e-17)
  z=0.5j: t0=0.57274 Im m0=0.8856>0; |self(m0)|=6.5e-18; |sqrt(t0)M0-M|=4.4e-16; |E+(1-t0)m0-sqrt(t0)z|=0.0e+00; sigma=+ |prof - t0*Theta_t0*Q0|=5.6e-16
  z=0.5j: t0=0.57274 Im m0=0.8856>0; |self(m0)|=6.5e-18; |sqrt(t0)M0-M|=4.4e-16; |E+(1-t0)m0-sqrt(t0)z|=0.0e+00; sigma=- |prof - t0*Theta_t0*Q0|=1.4e-15
  z=(0.05+0.3j): t0=0.70827 Im m0=0.8654>0; |self(m0)|=1.1e-16; |sqrt(t0)M0-M|=4.4e-16; |E+(1-t0)m0-sqrt(t0)z|=5.6e-17; sigma=+ |prof - t0*Theta_t0*Q0|=5.0e-16
  z=(0.05+0.3j): t0=0.70827 Im m0=0.8654>0; |self(m0)|=1.1e-16; |sqrt(t0)M0-M|=4.4e-16; |E+(1-t0)m0-sqrt(t0)z|=5.6e-17; sigma=- |prof - t0*Theta_t0*Q0|=4.2e-15
  Gt_BA: |sqrt(t0) G_t0(zt) - G(z)| = 1.0e-15  (zt = sqrt(t0) z: 0.0e+00)
```

### Verdicts
Fill-in (§269 (5)): (i) routes by merged name in rows 2-4, 10, 12; (ii) rows 10-11; (iii) rows 2-4 (`C = 12 C₀`, pin kept, `8 C₀` suffices; numeric max ratio `0.4519`); (iv) `MALocal_STWB_le`, `MALocal_Bctl_le` (public), `MALocal_geom`, `MALocal_kappa_floor` (`open private`); (v) rows 7-8; (vi), (vii), (viii) n/a, because section (a) has no Lean and no size estimates; (ix) probe step n/a, because the F5 route is named by merged and Mathlib names (rows 2-4).
- Targets 1, 2 (`baTrace2`, `baProfile_eq`): **PASS** (rows 10, 12; `baKsol_two` is exactly `(Kn2sol)`; `ΘQ` symmetric so `(b,a)` ↔ `(a,b)`).
- Target 3 comparisons, target 4 `det_of_precL`: **PASS** (rows 7, 8, 12).
- Target 5 `baQDiffFixed_of_ML`: **PASS** (rows 7-9, 11; `UNMLOutBA d` at `t = BAflowT0` as `UNPins:110`).
- Target 6 `baProf_lip` (`T2516_ProfLip`): **PASS**, true for every `d, sz, n` (no `3 ≤ d`, no `0 < λ`), pin constant `12 C₀` kept (rows 2-4).
- Targets 7, 8 (cover lemmas, `baMANetQD`): **PASS** (rows 5, 6, 9); the only threshold added to the band's is `C₀ ≤ N`, already T2514's `hCN`.
- Target 9 (`baEnd_QDiffL`, `_three`, `baMAFixed_holds`) and target 10 (instances): **PASS**.
- No pin, row or stop line moves; verdict PASS.
### (a′) Preflight corrections — Thu Oct 15 08:56:21 UTC 2026
Section (a) rows 5-6 and the (ii) limits take `C₀ ≤ N` as the binding `N`-threshold of the cover and `E = 28u⁴ ≤ u²`. The Lean cover lemma takes the `∃`-constant `C` of `baProf_lip` as opaque (pin shape),
so its threshold is `C ≤ N` with `C = 12 C₀` (the constant of the proof), the profile part is `2C u⁵ ≤ 2u⁴`, `E = 4u⁴ + 2u⁴ = 6u⁴ ≤ u²`, and the first `n` of the `τ = 1` instance is `n = 4` (not `n = 3`).
No pin, exponent, row or verdict of (a) changes.  Script (`.../scratchpad/T2516/corr.py`, numpy-free), verbatim:
```
n=0 N=2.0972e+06 N>=max(32,C_R,C=12C0)? False  E=6u^4=3.102e-25 <= u^2=2.274e-13: True  C*u=1.262e+10
n=1 N=6.8719e+10 N>=max(32,C_R,C=12C0)? False  E=6u^4=2.690e-43 <= u^2=2.118e-22: True  C*u=3.851e+05
n=2 N=3.0092e+13 N>=max(32,C_R,C=12C0)? False  E=6u^4=7.317e-54 <= u^2=1.104e-27: True  C*u=8.795e+02
n=3 N=2.2518e+15 N>=max(32,C_R,C=12C0)? False  E=6u^4=2.334e-61 <= u^2=1.972e-31: True  C*u=1.175e+01
n=4 N=6.4000e+16 N>=max(32,C_R,C=12C0)? True  E=6u^4=3.576e-67 <= u^2=2.441e-34: True  C*u=4.135e-01
C0=2.2056e+15 C=12*C0=2.6467e+16 C_R=250.0
```

## (b) Script output
```
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2516 log -1 --format='%h %ad %s' --date=iso-strict; git status --short; git diff --stat main...t/T2516
7c80bd9a 2026-10-15T01:49:29-07:00 T2516: M2 QDiff at BA from UNMLOutBA d (BA/MAQDiff)
 RBM3D.lean            |    1 +
 RBM3D/BA/MAQDiff.lean | 1099 +++++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1100 insertions(+)
$ stat -f '%Sm %N' <olean> <source>; grep -c 'MAQDiff.lean' final_build.log (warning lines of the module in the log); tail -1 final_build.log   [after `lake build RBM3D.BA.MAQDiff`]
Oct 15 01:48:52 2026 .lake/build/lib/lean/RBM3D/BA/MAQDiff.olean
Oct 15 01:48:24 2026 RBM3D/BA/MAQDiff.lean
0
Build completed successfully (4358 jobs).
$ lake build   (full library; `#assert_rbm_axioms` at RBM3D.lean:651; selected log lines)
ℹ [4420/4421] Built RBM3D (74s)
info: RBM3D.lean:651:0: axiom audit: 15473 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 54, structural 52, refuted 6, superseded 14).
non-vacuity certificates: 0 of 121 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4421 jobs).
$ wc -l RBM3D/BA/MAQDiff.lean   (stop line 1300; 2,000 per file)
    1099 /Users/junyin/Lean_proof/RBM3D-wt/T2516/RBM3D/BA/MAQDiff.lean
$ per-section lines against the ticket's bottom-up (targets 1+2 = rows 1+2 of the ticket table, etc.)
part                                                     lines     n   bottom-up lo / central / hi
header, docstring, opens (1-80)                        1-80       80   25 / 25 / 30
section Transfer: targets 1+2                         81-254     174   85 / 130 / 200
section Compare: targets 3+4                         258-413     156   125 / 150 / 190
section Fixed: target 5                              417-568     152   120 / 150 / 200
section ProfLip: target 6                            572-852     281   120 / 200 / 330
section Net: targets 7+8                             856-1005    150   125 / 160 / 230
section Main: target 9                              1009-1021     13   10 / 15 / 20
section Inst: instances (10)                        1029-1094     66   35 / 50 / 70
  theorem baProf_lip alone (docstring..end)          764-850      87   
total 1099 lines: ticket bottom-up 645 / 880 / 1,270, calibrated 845-1,126, stop line 1,300 (not reached: no `MAQDiffNet`)
```
```
$ #print axioms of every public declaration of the file (scratch file `pincheck.lean`, exit 0, 0 errors)
'baTrace2' depends on axioms: [propext, Classical.choice, Quot.sound]
'baProfile_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'baQDiffFixed_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'baProf_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'baMANetQD' depends on axioms: [propext, Classical.choice, Quot.sound]
'baEnd_QDiffL' depends on axioms: [propext, Classical.choice, Quot.sound]
'baEnd_QDiffL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'baMAFixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ the targets against the pins (auditor-style, scratch file `pincheck.lean` = T2516-check.lean + these lines; exit 0)
example : ∀ d, BAEnd_QDiffL d ↔ T2516_EndQDiff d := fun _ => Iff.rfl
example : ∀ d, BAQDiffFixed d ↔ T2516_QDiffFixed d := fun _ => Iff.rfl
example : ∀ d, BAMANetQD d ↔ T2516_NetQD d := fun _ => Iff.rfl
example : T2516_Trace := @baTrace2
example : T2516_Profile := @baProfile_eq
example : T2516_ProfLip := baProf_lip
example : T2516_FixedOfML := baQDiffFixed_of_ML
example : T2516_NetQDAll := baMANetQD
example : T2516_EndOfML := baEnd_QDiffL
example : T2516_EndThree := baEnd_QDiffL_three
example : ∀ d, BAMAFixed d := baMAFixed_holds
```
Target statements, extracted by script from `RBM3D/BA/MAQDiff.lean` (line numbers are the file's):
```
-- RBM3D/BA/MAQDiff.lean:107
theorem baTrace2 {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    avg2 sz n (fun x y => BAGz sz n (z n) ω x y * BAGz sz n (z n) ω y x) a b =
        (BAflowT0 sz z n : ℂ) *
          BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, true] ![b, a] ω ∧
      avg2 sz n (fun x y => ((‖BAGz sz n (z n) ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (BAflowT0 sz z n : ℂ) *
          BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, false] ![b, a] ω := by …
-- RBM3D/BA/MAQDiff.lean:208
theorem baProfile_eq {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) (hl : 0 < sz.lam n) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    BAprof sz n (z n) true σ a b =
      (BAflowT0 sz z n : ℂ) * BAKloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, σ] ![b, a] := by …
-- RBM3D/BA/MAQDiff.lean:432
theorem baQDiffFixed_of_ML (d : ℕ) (hML : UNMLOutBA d) : BAQDiffFixed d := by …
-- RBM3D/BA/MAQDiff.lean:768
theorem baProf_lip (κ : ℝ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (η : ℝ) (z w : ℂ), 0 < η → η ≤ z.im →
    η ≤ w.im → z.im ≤ 1 → w.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re → BAbulk d (sz.L n) (sz.lam n) κ w.re →
      ∀ (σ : Bool) (a b : Zd d (sz.L n)),
        ‖BAprof sz n z true σ a b - BAprof sz n w true σ a b‖ ≤ C * (η ^ 2)⁻¹ * ‖z - w‖ / ((sz.W n : ℕ) : ℝ) ^ d := by …
-- RBM3D/BA/MAQDiff.lean:965
theorem baMANetQD (d : ℕ) : BAMANetQD d := by …
-- RBM3D/BA/MAQDiff.lean:1012
theorem baEnd_QDiffL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_QDiffL d :=
-- RBM3D/BA/MAQDiff.lean:1016
theorem baEnd_QDiffL_three : BAEnd_QDiffL 3 := baEnd_QDiffL 3 unMLOutBA_three
-- RBM3D/BA/MAQDiff.lean:1019
theorem baMAFixed_holds (d : ℕ) : BAMAFixed d := fun hML => ⟨baLocSCFixed_of_ML d hML, baQDiffFixed_of_ML d hML⟩
```
Compiled nonempty instances at `d = 3` on `S0` (`section Inst`, file lines 1029-1094, docstrings omitted here; `unMLOutBA_three` is the merged `UNMLOutBA 3`):
```
example (ω : S0.SeqΩ) (a b : Zd 3 (S0.L 0)) : True := by
  have hz : 0 < ((fun _ : ℕ => (⟨(fp 4 MAQDiff_hg).E, 1 / 2⟩ : ℂ)) 0).im := by
    change (0 : ℝ) < 1 / 2
    norm_num
  have _ := baTrace2 S0 (fun _ : ℕ => (⟨(fp 4 MAQDiff_hg).E, 1 / 2⟩ : ℂ)) 0 hz ω a b
  have _ := baProfile_eq S0 (fun _ : ℕ => (⟨(fp 4 MAQDiff_hg).E, 1 / 2⟩ : ℂ)) 0 hz (fp 4 MAQDiff_hg).g0_pos false a b
  have _ := baProfile_eq S0 (fun _ : ℕ => (⟨(fp 4 MAQDiff_hg).E, 1 / 2⟩ : ℂ)) 0 hz (fp 4 MAQDiff_hg).g0_pos true a b
  trivial
example (a b : Zd 3 (S0.L 0)) : True := by
  obtain ⟨C, hC, h⟩ := baProf_lip (clsκ 4 MAQDiff_hg) (clsκ_pos 4 MAQDiff_hg)
  have h1 := cls_bulk 4 (by norm_num) MAQDiff_hg
  have _ := h 3 S0 0 (1 / 4) ⟨(fp 4 MAQDiff_hg).E, 1 / 2⟩ ⟨(fp 4 MAQDiff_hg).E, 1 / 4⟩ (by norm_num)
    (by change (1 / 4 : ℝ) ≤ 1 / 2; norm_num) (by change (1 / 4 : ℝ) ≤ 1 / 4; norm_num) (by change (1 / 2 : ℝ) ≤ 1; norm_num)
    (by change (1 / 4 : ℝ) ≤ 1; norm_num) h1 h1 true a b
  have _ := h 3 S0 0 (1 / 4) ⟨(fp 4 MAQDiff_hg).E, 1 / 2⟩ ⟨(fp 4 MAQDiff_hg).E, 1 / 4⟩ (by norm_num)
    (by change (1 / 4 : ℝ) ≤ 1 / 2; norm_num) (by change (1 / 4 : ℝ) ≤ 1 / 4; norm_num) (by change (1 / 2 : ℝ) ≤ 1; norm_num)
    (by change (1 / 4 : ℝ) ≤ 1; norm_num) h1 h1 false a b
  trivial
example : (∀ᶠ n in atTop, ∀ z : ℂ, BAendDom S0 (clsκ 4 MAQDiff_hg) (1 / 20) n z →
      (Sizes.seqP (S0.withLam 0) {ω | BAqdBadz S0 (1 / 10) n z ω false} ≤ ENNReal.ofReal (Nsz S0 n ^ (-(2 : ℝ))) ∧
        Sizes.seqP (S0.withLam 0) {ω | BAqdBadz S0 (1 / 10) n z ω true} ≤ ENNReal.ofReal (Nsz S0 n ^ (-(2 : ℝ)))) ∧
      ∀ a b : Zd 3 (S0.L n), ‖(∫ ω, avg2 S0 n (fun x y => ((‖BAGz S0 n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (S0.withLam 0))) -
            BAprof S0 n z true false a b‖ ≤ qdBoundExp S0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 S0 n (fun x y => BAGz S0 n z ω x y * BAGz S0 n z ω y x) a b ∂(Sizes.seqP (S0.withLam 0))) -
            BAprof S0 n z true true a b‖ ≤ qdBoundExp S0 n (1 / 10) z.im) ∧
    ∀ n, ∃ z : ℂ, BAendDom S0 (clsκ 4 MAQDiff_hg) (1 / 20) n z :=
  ⟨baQDiffFixed_of_ML 3 unMLOutBA_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAQDiff_hg) (1 / 20) (1 / 10) 2
      (clsκ_pos 4 MAQDiff_hg) (by norm_num) (by norm_num) (by norm_num),
    fun n => inst_locAvg_domain (by norm_num) n⟩
example : (∀ᶠ n in atTop, Sizes.seqP (S0.withLam 0) {ω | ∃ z : ℂ, BAendDom S0 (clsκ 4 MAQDiff_hg) (1 / 20) n z ∧
        BAqdBadz S0 (1 / 10) n z ω false} ≤ ENNReal.ofReal (Nsz S0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP (S0.withLam 0) {ω | ∃ z : ℂ, BAendDom S0 (clsκ 4 MAQDiff_hg) (1 / 20) n z ∧
        BAqdBadz S0 (1 / 10) n z ω true} ≤ ENNReal.ofReal (Nsz S0 n ^ (-(2 : ℝ)))) ∧
    ∀ n, ∃ z : ℂ, BAendDom S0 (clsκ 4 MAQDiff_hg) (1 / 20) n z :=
  ⟨(baMANetQD 3 (baQDiffFixed_of_ML 3 unMLOutBA_three) le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAQDiff_hg) (1 / 20) (1 / 10) 2
      (clsκ_pos 4 MAQDiff_hg) (by norm_num) (by norm_num) (by norm_num)).mono fun n hn => hn.1,
    fun n => inst_locAvg_domain (by norm_num) n⟩

example := baEnd_QDiffL_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAQDiff_hg) (1 / 20) (1 / 10) 2
  (clsκ_pos 4 MAQDiff_hg) (by norm_num) (by norm_num) (by norm_num)

example (hML : UNMLOutBA 3) : True := by
  have _ := baEnd_QDiffL 3 hML le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAQDiff_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAQDiff_hg)
    (by norm_num) (by norm_num) (by norm_num)
  have _ := (baMAFixed_holds 3 hML).2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAQDiff_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAQDiff_hg)
    (by norm_num) (by norm_num) (by norm_num)
  have _ := (baMAFixed_holds 3 hML).1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MAQDiff_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 MAQDiff_hg)
    (by norm_num) (by norm_num) (by norm_num)
  trivial
```
Hypothesis-rule greps (ticket "Hypothesis rules"; commands verbatim, counts):
```
$ C1: grep -nE 'mE\b|\|E\| ≤ 2|SB d|M = m|m • 1|etaT|STFlow|lemT|lemE|msc|locDomain|Mband|sz\.Gn|ThetaP[MP]|profP[MP]|KLK_two|Theta d' MAQDiff.lean | cut -c1-72
228:  have hXsym : (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz 
230:      (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
243:      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BATheta d (sz.L n) (BAflowLam0 s
248:  change (t0 : ℂ) * (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowE
   (4 hits, all `BATheta d` inside proof bodies of `baProfile_eq`; the same grep with `\bTheta d`: 0 hits; in the 8 statements: 0)
$ X1-C4 (defs in MAQDiff | MN1 defs outside MAPins): 0 | 0
$ MN-D3 grep -nE 'ℕ → Prop\)|· = 3': 0 hits
$ UBA grep -n withLam | grep -vc 'seqP (\(sz\|S0\).withLam 0)'   (hits that are not the law `seqP (sz.withLam 0)`): 0   (of 25 lines)
$ U5S-C3 grep -n '∃' (line numbers): 768 882 884 885 990 997 1065 1071 1073 1075 
   768 target 6 `∃ C` before `sz`; 882, 884-885 private cover lemma (`∃ w ∈ S`, event `∃ z`); 990, 997 event sets of `baMANetQD`; 1065-1075 instances (`∃ z`)
$ grep -n unMLOutBA_three | awk -F: '$1>80' | cut -d: -f1 (code and instances; docstrings at 1015, 1027, 1057): 1015 1016 1027 1057 1066 1076 
```
Registry scan (full `lake build`, `#assert_rbm_axioms`; `diff` of the scan log lines after the first two, parent state `3a67e18d` RBM3D.lean vs HEAD):
```
$ diff <(tail -n +3 scan_before.txt) <(tail -n +3 scan_after.txt)
290c290,291
< Build completed successfully (4420 jobs).
---
> Build completed successfully (4421 jobs).
> lake build  69.47s user 6.34s system 98% cpu 1:16.87 total
before: info: RBM3D.lean:650:0: axiom audit: 15465 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after : info: RBM3D.lean:651:0: axiom audit: 15473 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
both : premises found by scanning: 127 (borrowed 1, owed 54, structural 52, refuted 6, superseded 14).
```
Name clashes of the new public names (`git grep` at `main`, `t/T2514`, `t/T2515` in /Users/junyin/Lean_proof/RBM3D, 2026-10-15; regex baTrace2|baProfile_eq|baProf_lip|baQDiffFixed_of_ML|baMANetQD|baEnd_QDiffL|baMAFixed_holds|det_of_precL|MAQDiff):
```
main: 0 hits
t/T2514: 0 hits
t/T2515: 0 hits
```
Ports: from RBM3D's own merged band files (not RBM1D/RBM2D): `Main/FixedZ.lean:259, 373, 419`, `Main/ZTransfer.lean:394, 473`, `Main/ZNet.lean:888, 935, 1024`, `Endpoints.lean:443`, `BA/MALocal.lean:384, 785` (last commits touching them, as of `3a67e18d`: Main/FixedZ 0d5868e9, Main/ZTransfer afdb81e4, Main/ZNet 3a586632, Endpoints 8a437158, BA/MALocal 3a67e18d).
RBM1D/RBM2D `git diff --stat`: n/a, because no text was copied from `../RBM1D` or `../RBM2D` (every port is from the merged RBM3D band twins; each is re-derived at `d ≥ 3` / BA data, not by `d = 1, 2` facts).
Narrative (routes and judgement calls; every cited name is a merged file:line or a name of `MAQDiff.lean`).
- T1 `baTrace2`: port of `zTrace` (ZTransfer:394); `Gt_BA` (BlockAnderson:112), `BAzztE_data` (MFixedPoint:297), `Gres_blockMat'` (ZTransfer:253), `trace_four` (:269); `Gres_conjTranspose'` (ZTransfer:344) and `ConArg_seqHflowBA_isHermitian` (BA/ConArg:310) by `open private`. Needs only `0 < Im z_n`, no `BAFlow`.
- T2 `baProfile_eq`: `baKsol_two` (KInduct:88) at the `BAReal` datum of `BAdom_real` (MFixedPoint:479, `κ := Im m`), `BAm_real_eq_of_self` (:824) for `m_F = m/√t₀`. Ticket row 8 (Θ transfer) is inline (`Q(z) = t₀ Q₀` from `BAzztE_data` cl. 5: `MAQDiff_Mss_smul`, `MAQDiff_Theta_smul`); C3's lemma is not in `3a67e18d` (`baThetaTransfer`, `t/T2515:RBM3D/BA/GUEKPrim.lean:122`, is unmerged), so it is not imported. Orientation `(b,a)` vs `(a,b)`: `BATheta_resolvent` (KBase:330), `BATheta_isSymm` (:371).
- T3, T4 (private): `qd_core`, `qd_exp_core` (FixedZ:259, 373) with `t₀ ≤ 1` and the `(eq:BtBt)` constants as hypotheses (given by `MALocal_STWB_le` :293, `MALocal_Bctl_le` :322); `MAQDiff_det_of_precL` = `det_of_prec` (Endpoints:443) at a probability law (`isProbabilityMeasure_seqP`, FineModel:171).
- T5 `baQDiffFixed_of_ML`: `QDiffFixed_of_ML` (FixedZ:419) in the pattern of `baLocSCFixed_of_ML` (MALocal:384): chain domain `BAdom κ_f ε` with `MALocal_kappa_floor` (:339), `eventually_forall_of_sections` (Endpoints:423), `explicit_of_stochDomAt` (:376) at `τ/2`, union with `D + 1` (`prob_union_le`, `two_rpow_le`), `0 < sz.lam n` eventually (`MAQDiff_lam_pos`, `(eq:WO)`).
- T6 `baProf_lip` (F5): Ward rows `MAQDiff_Q_row_sum` (`BAMB_ward_row`, Ward:108); Neumann `MAQDiff_neumann` (`Units.oneSub`); `MAQDiff_prof_diff` (`ΘQ = Θ − 1`, `Θ − Θ' = Θ(Q − Q')Θ'`); `MAQDiff_Q_row_diff` (Cauchy-Schwarz on columns); `MAQDiff_M_col_sq` (`cont_green_diff` ContinuityNet:448, `BAm_sub_le_of_im` MReg:84, column `ℓ²` ≤ `ℓ²`-operator norm); `ba_dom_of_bulk` (RandomLayerBGBA:69). The pin `C = 12 C₀` is proved with slack (the route gives `8 C₀`). Size: section 281 lines, theorem alone 87; the stop for target 6 was 330. No probe step (`Probe/T2516Pins.lean` not created).
- T7, T8: `qd1Bad_net`/`qd2Bad_net` (ZNet:888, 935) in one private lemma (both `σ`), `netQD` (ZNet:1024); net, count, geometry from `BA/MALocal` (`MALocal_net_exists` :510, `_card_le` :759, `_net_count` :742, `_geom` :571, `_thresholds` :772, `_Gres_lip` :559) and `znet_qd_core` (ZNet:759), `znet_sq_diff` (:632), `znet_prod_diff` (:642), `znet_c4` (:879) by `open private`. Extra threshold `C ≤ N` ((a′)).
- T9: `baEnd_QDiffL = baMANetQD ∘ baQDiffFixed_of_ML`; `baEnd_QDiffL_three` at `unMLOutBA_three`; `baMAFixed_holds` pairs `baLocSCFixed_of_ML` (T2514) with T5.
- Statements: the eight targets equal the `T2516_*` pins and the `BA/MAPins` names (the examples above compile); targets 1, 2 are stated with `BAGz`, `BAprof` (delta-equal to the pins' unfoldings). No new hypothesis, no changed signature, no weakened target; `baProfile_eq` carries `0 < sz.lam n` as pinned.
- Coverage rows as used: 1, 2, 4-7, 9-11, 13, 15 as listed; row 3 = `MAQDiff_det_of_precL`; row 8 inline; row 12 = T6; row 14 = the private ZNet cores (`znet_c3`, `znet_num2`, `znet_min_*` not needed: `E ≤ u²` by `nlinarith`). Ticket F1 "unmerged" is stale: `BA/MAPins`, `BA/MALocal` are on `main` 3a67e18d ((a) line 6).
- Stop rules: none hit (file 1099 < 1300; target 6 below 330; no public def; no second MN1 text; every statement and proof at one `d`, instances at `d = 3`). `unMLOutBA_three` also occurs in the instances of targets 5, 8 (grep above).

## (c) Verified Mathlib names (`#check @name` in scratch `names.lean`)
```
$ lake env lean names.lean 2>&1   (19 `#check`s; 18 resolve, 1 error)
resolve: Matrix.linfty_opNNNorm_def, Matrix.linfty_opNormOneClass, Matrix.l2_opNorm_mulVec, EuclideanSpace.norm_sq_eq, PiLp.norm_single, Units.oneSub, Units.val_oneSub,
  Ring.inverse_mul_cancel, Ring.mul_inverse_cancel, Finset.sum_mul_sq_le_sq_mul_sq, pow_le_pow_iff_left₀, norm_star, Real.coe_toNNReal', abs_norm_sub_norm_le,
  MeasureTheory.integral_const_mul, MeasureTheory.integral_congr_ae, Finset.le_sup, Finset.single_le_sum
error (verified absent): (lean.unknownIdentifier): Unknown constant `Matrix.norm_entry_le_linfty_opNorm`
```
The entry bound `‖Q a b‖ ≤ ‖Q‖_{∞→∞}` is therefore the private `MAQDiff_entry_le_normInf`.

## (d) Open issues and paper-delta candidates
- `T2516a` (paper-delta candidate): the paper (`paper/tex/1_2_Intro_model_result.tex:1228`) extends the fixed-`z` estimates to all `z` by "a standard $N^{-C}$-net and perturbation argument, whose details we omit"; at BA the perturbation step needs a `z`-Lipschitz bound of the profile `W^{-d}(ΘM)^{(+,σ)}(z)`, which the paper does not state. Lean: `baProf_lip`, `C = 12 κ'⁻²(1 + κ'⁻²)`, `κ' = (πκ)^5/2048` (route constant `8 κ'⁻²(1 + κ'⁻²)`), every `d`, `sz`, `n`. No other Lean/paper statement difference; D689 (T2449a-c) unchanged.
- Open: (1) `d > 3` only under `UNMLOutBA d` (Jun decision B, DECISIONS §316), as the ticket. (2) All helpers and the cover lemma are private (stem `MAQDiff_`): registry unchanged (scan above: 0 new, 0 removed). (3) (a′): threshold `C ≤ N`, no verdict change. (4) `RBM3D.lean` gets one line, `import RBM3D.BA.MAQDiff` after `import RBM3D.BA.MALocal` (union at merge with T2514 b, T2515). (5) Counts: no split, M/N row 9, BA 198 (+0).
- Consumers: `baEnd_QDiffL_three` is, per the ticket, the input of N2 (`BAThm27L 3`) and M3 (`BAMAQUE 3`); `Test/Axioms.lean` untouched.
