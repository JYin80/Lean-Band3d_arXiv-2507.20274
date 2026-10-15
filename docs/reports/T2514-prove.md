Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 07:31:29 UTC 2026 (row a: P1-P6, A1-A9; `main` = `t/T2514` = b2326aac)

Notation: `N = (W L)^d`, `u = 1/N`, `η = Im z`, `t₀ = Im m/(Im m + Im z)`, `κ' = (πκ)^5/2048` (`ba_dom_of_bulk`, RandomLayerBGBA:69),
`R = 2 + 2d/𝔡`, `h = N^{-7}`. Scripts: `.../scratchpad/T2514/inst.py` (numpy, no Lean). No pin, row or stop line moves (verdict PASS).

### (i) Exponent table
| # | quantity (target) | value | constraint | slack at `d=3, 𝔡=1/10, κ=1/4, ε=1/10` |
|---|---|---|---|---|
| 1 | end domain `BAendDom` (P1; A2, A3) | `BAbulk κ Re z`, `N^{-1+ε} ≤ Im z ≤ 1` | empty if `ε>1` (`N>1`) or `κ>1/π` (`Im m ≤ 1`, `BAm_norm_le_one` Ward:136): both vacuous | `ρ(0) = 0.3183` (sz0, n=1), `0.2636` (S0): `κ=1/4 ≤ ρ` |
| 2 | `κ'(κ)` (A2, A3) | `(πκ)^5/2048` | `κ' ≤ Im m(z) ≤ 1` on the end domain (`ba_dom_of_bulk`) | `κ' = 1.4592e-4` |
| 3 | transfer window (A1) | `1-t₀ = η/(Im m+η) ∈ [η/2, η/κ']` (`BAt0_mul` MFixedPoint:290, `Im m ≤ 1`) | `STWB_compare` (ZTransfer:174): `η ≤ 2u₁`, `u₁ ≤ C η`, `C = 1/κ' ≥ 1` | script: all 5 test `y` in window; used direction `STWB(t₀,k) ≤ 2 calB`: constant 2, independent of `κ'` |
| 4 | fixed-`z` loss (A2) | `τ/2`, prob `N^{-(D+15)}` (`explicit_of_stochDomAt` Endpoints:376, needs `𝔠>0` and `Bandwidth`) | `2 ≤ W^{τ/2}` to turn `W^{τ/2}·2·calB` into `W^τ calB` | `W^{1/2} = 32` (τ=1, n=1) |
| 5 | pathwise flow (A1) | `G(z) = √t₀ G_{t₀}` (`Gt_BA`), `M(z) = √t₀ M_{t₀}` (`BAzztE_data`, 5th clause), `λ₀ = √t₀ λ` | `0 < t₀ < 1`; entry `‖G−M‖² = t₀‖G_{t₀}−M_{t₀}‖² ≤ ‖·‖²` | Ward identity check `0.820107 = Im m` |
| 6 | **real range of the BA bulk (NEW, A3)** | `BAbulk κ E, κ>0 ⇒ |E| ≤ 2 + 2d|λ|` | Ward at real `E` (`BAward_avg` MFixedPoint:389) gives `‖M‖_F² = L^d`; `‖M‖_F² ≤ L^d/(|w|−|λ|‖Ψ‖)²`, `‖Ψ‖ ≤ 2d` (`Adj` = ℓ¹ distance 1: ≤ 2d neighbours), `|m| ≤ 1`; no merged lemma (the `BAbulk` theorems of `BA/*.lean`: ImmLower:424, MFixedPoint:448, 830, RandomLayerBGBA:69, MReg:122, 169, 192, 227: none bounds `|E|`) | actual support `[-2.6363, 2.6363]` ⊂ `[-3.8, 3.8]` (S0); eventual `R = 62` (`WO`: `λ ≤ 𝔡⁻¹`) |
| 7 | net mesh, count (A3) | `h = N^{-7}`; one representative per cell meeting the domain (net lies in the end domain at `κ`; `BAbulk_window` **not needed**); count `≤ (2R N^7+2)(N^7+1) ≤ C_R N^{14}`, `C_R = 4(R+1)` | `25 N^{14}` of `net_count` (ZNet:101) is **not** valid for BA: `C_R ≤ N` (eventual, `SizeTendsto`) replaces `25 ≤ N`; union `C_R N^{14} N^{-(D+15)} = C_R N^{-1} N^{-D} ≤ N^{-D}` | `C_R = 252`; `N = 5.5e11 ≥ 252`; union `8.3e-22 ≤ 1.8e-12` (D=1) |
| 8 | cover error (A3) | `‖G(z)−G(w)‖ ≤ 2u⁵` (carrier: `Gres (seqHBA)`); `|m(z)−m(w)| ≤ ‖z−w‖/κ'²` (`BAm_sub_le_of_im` MReg:84); `‖M(z)−M(w)‖ ≤ κ'^{-2}(‖z−w‖+|Δm|)`, `‖M‖ ≤ 1/(Im z+Im m) ≤ 1/κ'`, `‖z−w‖ ≤ 2u⁷` | total `e ≤ 2u⁵ + 2u⁷(κ'^{-2}+κ'^{-4}) ≤ 4u⁵` iff `N² ≥ κ'^{-2}+κ'^{-4}`; then the carrier-free private cores `znet_loc1_core/loc2_core` (ZNet:681, 693, `e ≤ 4u⁵`) apply verbatim | `κ'^{-2}+κ'^{-4} = 2.206e15` vs `N² = 3.0e23`; script Lipschitz test: `|Δm| 3.97e-5 ≤ 1.66e-4`, `‖ΔM‖_op 1.02e-4 ≤ 2.25e-4` |
| 9 | thresholds of the cover (A3) | `32 ≤ N` (`u ≤ 1/32`), `5 ≤ W^{τ/2}`, `|Δη| ≤ η/2` (`calB_shift_le` ZNet:123, `N^{-7} ≤ u/2`) | all three eventual (`SizeTendsto`, `Bandwidth`, `tendsto_W`) | τ=1: `W^{1/2}=32 ≥ 5` at n=1; τ=1/10 (Lean instance): first at `n = 312` (eventual, not used as a witness) |
| 10 | **sections need a flow at every `n` (NEW, A2)** | `BAFlow sz κ_f ε 𝔠 𝔡 z` needs `BAdom` at all `n`, the end domain may be empty at infinitely many `n` (band `locDomain` never is) | section type `Option {z // endDom n z}`, fallback `z_n = i`; `κ_f = min(κ', inf_n Im m_n(i))`; `Im m_n(i) > 0` ∀n (`BASelf_exists` MFixedPoint:691, any real `g`); eventual lower bound `Im m(i) ≥ (2+2d|λ|)^{-2}` (Ward at `Im z = 1`: `Im m = (Im m+1)S`, `S ≥ ‖A‖_op^{-2}`, `‖A‖_op ≤ 2d|λ| + 2`); `ε ≤ 1` for `N^{-1+ε} ≤ 1`; `BAdom κ'⇒BAdom κ_f` | `c₀ = (2+2d/𝔡)^{-2} = 2.60e-4`; script `Im m(i) = 0.549 ≥ 0.069` (S0), `0.618 ≥ 0.250` (sz0 n=1) |
| 11 | bridge A6/A7 | `calB sz n η 0 = Bctl sz n (1−η)` (`calB_zero_eq_Bctl` Endpoints:231, `d ≥ 2`); `UNKind.ba` fields `bulk = BAbulk`, `mdet = BAm`, `M = UNModelC.ba` (UNPins:84) | exact (no exponent); P4 domain = P1 domain (`size n` cast = `Nsz`); P6 `Iff.rfl` by unfolding `UNLocAvgk` | n/a |
| 12 | A5 route | `unMLOutBA_three : UNMLOutBA 3` is **merged** on `main` (`BA/MainIndTermBA:47`; the ticket's F1 "unmerged" is stale) | A5, A9 are unconditional in row a; `UNMLOutBA 3` is not a binder | n/a |

Fill-in table (ticket §269 (5)). **(i)** routes: P1-P3 probe text, P4-P6 readings; A2 = `locSCFixed_of_ML` (FixedZ:100) twin; A3 = `netLoc` (ZNet:999) twin with rows 6-8; A6 = `locSC_to_UNLocAvgBand` (Endpoints:519) twin;
A7, A8, A5 one-liners. **(ii)** A1: `Gt_BA` (BlockAnderson:112), `BAzztE_data` (MFixedPoint:297), `BAt0_mul` (:290), `BAm_norm_le_one` (Ward:136), `STWB_compare` (ZTransfer:174).
**(iii)** F3: margin `h = N^{-7}`, representatives instead of a `κ/2` shift: the fixed-`z` form is called at `(κ, ε, τ/2, D+15)`, not at `κ/2`; row 6 (new lemma ≈ 50 lines) bounds the cell count. **(iv)** n/a: row b's 1a.
**(v)** below. **(vi)** scan (`Test/Axioms.lean:494-517`, premises minus conclusion heads): row a removes `UNLocAvgBA` (`:177` now; `:178` before T2511 b) once A7 concludes it; new theorem premises `UNMLOutBA d`
(concluded by `unMLOutBA_of_famStep`), `BAEnd_locSCL d` (concluded by A4, A5), `LocSCFixed d` (A2) are all concluded by a theorem: 0 new, −1.
**(vii)** central `MAPins` ≈ 195 (stop 350); `MALocal` ≈ 730 + rows 6, 10 (≈ 50 + 70, minus the dropped `κ/2` window ≈ 20) ≈ 830, calibrated ×0.96-1.28 ≈ 800-1,060 (stop 1,300; hi 1,170+100 over it, spare `MALocalNet` as ticketed).
**(viii)** greps are 1b's. **(ix)** A5 in row a (row 12).

### (ii) One concrete nondegenerate instance (all targets, `d = 3`)
Data: Lean instance class `S0 = clsSz 4 (3/10)`: `L_n = 4`, `λ_n = 3/10`, `W_n = (2(n+1))^5`, `(𝔠, 𝔡) = (1/6, 1/10)` (`S0_adm`, UNPins:887); numeric stand-in `κ = 1/4`, `ε = 1/10`, `τ = 1`, `D = 1`
(the Lean `example`s of probe 277-300 use `κ_* = clsκ` (existential flow point, `fp`), `ε = τ = 1/10`, `D = 1`; domain nonempty at every `n` by `inst_locAvg_domain`, UNPins:990).
Second sequence `sz0` (`L = 4(n+1)`, `λ = (2(n+1))^{-6}`, SizesInst) at `n = 1`: `L = 8`, `W = 1024`, `λ = 2^{-12}`, `N = 5.5e11`. Hypotheses of the targets: `3 ≤ d`, admissibility, `0 < κ, ε, τ, D`;
`UNMLOutBA 3 = unMLOutBA_three` (merged theorem, no binder); the pins `BAEnd_QDiffL`, `BAEnd_decolL`, `BAThm27L`, `BAQDiffFixed`, `BAMAFixed`, `BAMANetQD`, `BAMADecol`, `BAMAQUE` are only `example` hypotheses.
External hypotheses: none. The size hypotheses are limits: `N_n ≥ n → ∞`; `W_n^6 ≥ N_n` (`L ≤ W`), so `N^{1/6} ≤ W`; `W^{-d/2+𝔡} = W^{-1.4} → 0` between `0` and `λ`; `λ ≤ 𝔡⁻¹ = 10`.

Command: `cd .../scratchpad/T2514 && python3 inst.py` (numpy 2.0.2; Newton continuation for `w = z + m_Ψ(w)`, `Ψ` spectrum `2Σcos(2πk_i/L)`):
```
S0 n=0: W=32, N=2097152, N^(1/6)=11.3137 <= W: True;  W^(-d/2+1/10)=0.007813 <= g=0.30 <= 1/dd=10: True
[S0] L=4 g=0.3 W=32 N=2097152: rho(0)=0.263612 max rho=0.263612
  support of rho: [-2.6363,2.6363]  bound R=2+2d*g=3.8000  ok=True
  Im m(i)=0.549085 >= (2+2dg)^-2=0.069252  ok=True
[sz0 n=1] L=8 g=0.000244140625 W=1024 N=549755813888: rho(0)=0.318310 max rho=0.318310
  support of rho: [-2.0000,2.0000]  bound R=2+2d*g=2.0015  ok=True
  Im m(i)=0.618034 >= (2+2dg)^-2=0.249634  ok=True
  rho(0)=0.318310 >= kappa=0.25: True;  kappa'=(pi k)^5/2048=1.4592e-04;  window (pi k)^3/8=0.06056
  R_eventual=2+2d/dd=62.0  C_R=4(R+1)=252.0  N=5.4976e+11 >= max(32,C_R): True
  cover M-part: N^2=3.022e+23 >= kp^-2+kp^-4=2.206e+15: True;  W^(tau/2)=32.000 >= 5: True
  union bound: C_R N^14 N^-(D+15) = 8.338e-22 <= N^-D = 1.819e-12: True
  mesh N^-7=6.589e-83; Im z floor N^(-1+eps)=2.715e-11; cover error e<=4u^5=7.965e-59 <= u=1.819e-12
  y=2.715e-11: Im m=1.00000 (>= kappa' True), 1-t0=2.7155e-11 in [1.358e-11,2.715e-11]
  y=1.000e-03: Im m=0.99950 (>= kappa' True), 1-t0=9.9950e-04 in [5.000e-04,1.001e-03]
  y=5.000e-02: Im m=0.97531 (>= kappa' True), 1-t0=4.8766e-02 in [2.500e-02,5.127e-02]
  y=3.000e-01: Im m=0.86119 (>= kappa' True), 1-t0=2.5836e-01 in [1.500e-01,3.484e-01]
  y=1.000e+00: Im m=0.61803 (>= kappa' True), 1-t0=6.1803e-01 in [5.000e-01,1.618e+00]
  transfer window OK: True
  m-Lipschitz: |m1-m2|=3.965e-05 <= |z1-z2|/c^2=1.662e-04;  ||M1-M2||_op=1.017e-04 <= c^-2(|dz|+|dm|)=2.252e-04
  Ward at z1: (Im m + Im z) * mean_ab |M_ba|^2 = 0.820107  vs Im m = 0.820107
S0 n=1: W=1024 N=6.8719e+10; N>=max(32,C_R=252): True; N^2>=kp^-2+kp^-4: True; W^(1/2)=32.0>=5: True; rho(0)=0.2636>=1/4: True
S0 admissible n=1: N^(1/6)=64.000<=W: True; W^(-1.4)=6.10e-05<=0.3<=10
tau=1/10: W_n^(1/20)>=5 first at n = 312 (W_n=(2(n+1))^5 >= 5^20 = 95367431640625 )
```
Reading: at `S0`, `n = 1` (and every `n ≥ 1` at τ = 1) all thresholds of rows 2-9 hold with the bulk nonempty (`ρ(0) = 0.2636 ≥ 1/4`); the end domain is nonempty (`E = 0`, `z = i`).

### Verdicts
- **P1-P6: PASS** (verbatim texts; P6 three `Iff.rfl` by unfolding `UNLocAvgk` at `UNKind.ba d`, UNPins:84, PinsK:406).
- **A1, A2, A3, A4: PASS**, with three routes that differ from the ticket's F3 and are needed (rows 6, 7, 10): (1) the BA bulk has no merged real-range bound: new lemma `|E| ≤ 2 + 2d|λ|`, so the net count is `C_R N^{14}` with `C_R = 252`, not `25`; `net_count` is not reusable, a private count with `C_R ≤ N` is.
  (2) net points are cell representatives inside the end domain at `κ` (no `κ/2`, no `BAbulk_window`). (3) `eventually_forall_of_sections` (Endpoints:423) needs `Nonempty (Z n)` at every `n`; for BA use `Option` sections with fallback `z = i` and `κ_f = min(κ', inf_n Im m_n(i))` (row 10).
  Cover cores need `N² ≥ κ'^{-2}+κ'^{-4}` (row 8): eventual, no new exponent. Paper-delta candidates: none (all three are proof routes).
- **A5: PASS** (`unMLOutBA_three` merged; stale F1). **A6-A9: PASS** (rows 11, 12).


## (a′) Preflight corrections — Thu Oct 15 08:07:33 UTC 2026

No verdict changes; the three Lean routes below differ in detail from the rows of (a) they name.
1. Row 8: the cover threshold in Lean is `κ'⁻¹ κ'⁻¹ (1 + κ'⁻¹ κ'⁻¹) ≤ N` (hypothesis `hCN` of `MALocal_moduli` and of the two cover lemmas), not `N² ≥ κ'^{-2} + κ'^{-4}`.  With (a)'s own numbers (`κ'^{-2} + κ'^{-4} = 2.206e15`, `N = 5.5e11` at `sz0`, `n = 1`) the threshold is not met at that `n`; every statement is `∀ᶠ n`, no witness `n` is used.
2. Row 10: the sections lemma runs over `{z // BAdom d L N λ κ_f ε z}` (not over `Option {z // endDom}`): `i` lies in it at every `n` by `MALocal_im_I_ge` and the uniform floor `MALocal_kappa_floor`; the end domain is inside it by `ba_dom_of_bulk`.
3. Row 7: the net count is `(2R/h + 1)(1/h + 1) ≤ (4R + 2) N^14` (`MALocal_card_le`), constant `4R + 2`, not `4(R + 1)`.

## (b) Script output (row a, branch `t/T2514`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2514`)

```
### b1 commits, scope, sizes
$ git log --format="%h %cI %s" b2326aac..HEAD
cf63c909 2026-10-15T01:05:23-07:00 T2514a: BA/MALocal module docstring
0c3ab6b0 2026-10-15T01:01:06-07:00 T2514a: BA/MALocal (locSC at BA from UNMLOutBA d, bridge to UNLocAvgBA), imports, registry
7a8294ac 2026-10-15T01:01:05-07:00 T2514a: BA/MAPins instances of the P6 readings at d = 3
112ffba2 2026-10-15T00:40:11-07:00 T2514a: BA/MAPins (MN1 pin texts P1-P6, per-d readings, instances)
$ git diff --stat main...t/T2514
 RBM3D.lean             |   2 +
 RBM3D/BA/MALocal.lean  | 927 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/MAPins.lean   | 279 +++++++++++++++
 RBM3D/Test/Axioms.lean |   5 +-
 4 files changed, 1210 insertions(+), 3 deletions(-)
$ wc -l RBM3D/BA/MAPins.lean RBM3D/BA/MALocal.lean
     279 RBM3D/BA/MAPins.lean
     927 RBM3D/BA/MALocal.lean
    1206 total
### b2 builds
$ lake build RBM3D.BA.MAPins RBM3D.BA.MALocal 2>&1 | tail -2
Build completed successfully (4357 jobs).
$ lake build 2>&1 | grep -E "^registry|axiom audit:|Build completed" | cut -c1-205
info: RBM3D.lean:650:0: axiom audit: 15465 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 119 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4420 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/BA/MAPins.lean RBM3D/BA/MALocal.lean
RBM3D/BA/MAPins.lean:0
RBM3D/BA/MALocal.lean:0
### b3 axioms
$ lake env lean ax2.lean   (#print axioms RBM.BA.<name>; std3 = [propext, Classical.choice, Quot.sound])
baLocSCFixed_of_ML std3
baMANetLoc std3
baEnd_locSCL std3
baEnd_locSCL_three std3
unLocAvgBAAt_of_locSCL std3
UNLocAvgBA_of_BAEnd_locSCL std3
unLocAvgBAAt_of_ML std3
UNLocAvgBA_iff_at std3
UNTrLocalBARow_iff_at std3
UNTrLocalInitBARow'_iff_at std3
MALocal_bulk_abs_le std3
MALocal_im_I_ge std3
MALocal_G_sub_M std3
MALocal_avg_sub_m std3
MALocal_STWB_le std3
MALocal_Bctl_le std3
### b4 target statements (python extract.py, text of the files)
theorem baLocSCFixed_of_ML (d : ℕ) (hML : UNMLOutBA d) : BAlocSCFixed d

theorem baMANetLoc (d : ℕ) : BAMANetLoc d

theorem baEnd_locSCL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_locSCL d

theorem baEnd_locSCL_three : BAEnd_locSCL 3

theorem unLocAvgBAAt_of_locSCL (d : ℕ) (hd : 3 ≤ d) (h : BAEnd_locSCL d) : UNLocAvgBAAt d

theorem UNLocAvgBA_of_BAEnd_locSCL (h : ∀ d : ℕ, BAEnd_locSCL d) : UNLocAvgBA

theorem unLocAvgBAAt_of_ML (d : ℕ) (hd : 3 ≤ d) (hML : UNMLOutBA d) : UNLocAvgBAAt d

theorem UNLocAvgBA_iff_at : UNLocAvgBA ↔ ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d

theorem UNTrLocalBARow_iff_at : UNTrLocalBARow ↔ (UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → UNTrLocalBAAt d)

theorem UNTrLocalInitBARow'_iff_at :
    UNTrLocalInitBARow' ↔ (UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → UNTrLocalInitBAAt' d)

$ grep -n "^def " RBM3D/BA/MAPins.lean   (the 22 P1-P5 defs: line, name)
51 BAGz;55 BAMz;59 BAprof;65 BAendDom;69 BAlocBad1z;74 BAlocBad2z;80 BAqdBadz;86 BAdecolBad;97 BAEnd_locSCL;107 BAEnd_QDiffL;121 BAEnd_decolL;126 BAThm27L;132 BAlocSCFixed;139 BAQDiffFixed;152 BAMAFixed;155 BAMANetLoc;158 BAMANetQD;161 BAMADecol;164 BAMAQUE;170 UNLocAvgBAAt;180 UNTrLocalBAAt;187 UNTrLocalInitBAAt';
### b5 statement diff against the pins (scratch `diff_a1.lean` = the check + `example`s, uncommitted)
$ lake env lean diff_a1.lean | grep -ciE "error|sorry"; echo exit=$?
0
examples in diff_a1.lean: 24 = 14 `Iff.rfl` (BAEnd_locSCL, BAEnd_QDiffL, BAEnd_decolL, BAThm27L, BAlocSCFixed, BAQDiffFixed, BAMAFixed, BAMANetLoc, BAMANetQD, BAMADecol, BAMAQUE, UNLocAvgBAAt, UNTrLocalBAAt, UNTrLocalInitBAAt' against the `T2514_*` pins; these cover P1's eight defs through their uses) + 2 (the three P6 theorems, `T2514_ReadIff`) + 7 (`example : T2514_X := target` for A2-A8) + 1 trivial
### b6 compiled instances (all inside the two files, built by the commands of b2)
RBM3D/BA/MAPins.lean:215:example (h : BAThm27L 3) : True
RBM3D/BA/MAPins.lean:228:example (hF : BAlocSCFixed 3) (hQ : BAQDiffFixed 3) (hN : BAMANetLoc 3) (hM : BAMADecol 3) (hNQ : BAMANet
RBM3D/BA/MAPins.lean:241:example : ∀ n, ∃ z : ℂ, BAendDom S0 (clsκ 4 MAPins_hg) (1 / 20) n z
RBM3D/BA/MAPins.lean:245:example (hL : UNLocAvgBAAt 3) (hT : UNTrLocalBAAt 3) (hI : UNTrLocalInitBAAt' 3) : True
RBM3D/BA/MAPins.lean:259:example (hL : UNLocAvgBA) (hR : UNTrLocalBARow) (hI : UNTrLocalInitBARow') : True
RBM3D/BA/MALocal.lean:873:example : (∀ᶠ n in atTop, ∀ z : ℂ, BAendDom S0 (clsκ 4 MALocal_hg) (1 / 20) n z →
RBM3D/BA/MALocal.lean:883:example : (∀ᶠ n in atTop, Sizes.seqP (S0.withLam 0) {ω | ∃ z : ℂ, BAendDom S0 (clsκ 4 MALocal_hg) (1 / 2
RBM3D/BA/MALocal.lean:893:example
RBM3D/BA/MALocal.lean:897:example
RBM3D/BA/MALocal.lean:902:example (h : ∀ d : ℕ, BAEnd_locSCL d) : True
RBM3D/BA/MALocal.lean:910:example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (a : Zd 3 (sz0.L 0)) : True
RBM3D/BA/MALocal.lean:918:example : |(fp 4 MALocal_hg).E| ≤ 2 + 2 * (3 : ℕ) * |S0.lam 0| ∧
### b7 name clash
$ for each of the 38 public names: git grep -w -F <name> b2326aac -- RBM3D   (hits outside the two files)
public names:       38; hits at b2326aac: 0
### b8 registry
$ git diff b2326aac HEAD -- RBM3D/Test/Axioms.lean RBM3D.lean | grep -E "^[-+][^-+]" | cut -c1-210
+import RBM3D.BA.MAPins
+import RBM3D.BA.MALocal
-   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`); `UNMLOutBA` left this list (BA: T2504)
-   `RBM.Univ.UNLocAvgBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-M1, `(G_bound_ave)` from `BAEnd_locSC`)
+   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`); `UNMLOutBA` left this list (BA: T2504); `UNLocAvgBA` left this list (T2514a: concluded by `UNLocAvgBA_of_BAEnd_loc
-   `RBM.Univ.UNLocAvgk, -- bulk universality pin, model-generic (T2187, UN-01b): structural as `UNTrLocal` (supervisor 0853 Q2 (d), (e)). Band instance: `UNLocAvgk_band` (`Universality/PinsK.lean:554`) at `unL
+   `RBM.Univ.UNLocAvgk, -- bulk universality pin, model-generic (T2187, UN-01b): structural as `UNTrLocal` (supervisor 0853 Q2 (d), (e)). Band instance: `UNLocAvgk_band` (`Universality/PinsK.lean:554`) at `unL
scan before (lake build RBM3D at b2326aac, tool log): RBM3D.lean:648:0: axiom audit: 15449 theorems, 4728 definitions, 0 axioms
scan before: registry: 2 borrowed + 120 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet
scan after  (lake build at HEAD):
info: RBM3D.lean:650:0: axiom audit: 15465 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 119 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
### b9 hypothesis-rule greps
$ C1: grep -nE "mE|\|E\| ≤ 2|SB d|M = m|m • 1|etaT|STFlow|lemT|lemE|msc|locDomain|Mband|sz\.Gn" (two files) | wc -l
       0
$ X1-C4: grep -cE "^(private )?(noncomputable )?(def|abbrev|structure) " per file
RBM3D/BA/MAPins.lean:22
RBM3D/BA/MALocal.lean:0
$ MN-D3: grep -cE "ℕ → Prop\)|· = 3" per file
RBM3D/BA/MAPins.lean:0
RBM3D/BA/MALocal.lean:0
$ UBA: grep -n withLam (two files) | grep -vc "seqP (sz.withLam 0)\|seqP (S0.withLam 0)"   [lines not of the form seqP (sz.withLam 0)]
0
UBA hits total: 14 (MAPins) 11 (MALocal)
$ U5S-C3: lines with ∃
MAPins: 70 75 81 100 102 110 112 173 174 241 
MALocal: 240 340 512 513 519 520 636 638 639 685 687 688 812 819 876 883 885 887 
$ F1: grep -nE "unMLOutBA_three|baMLOutTL_three" lines
MAPins: 
MALocal: 49 837 839 857 871 877 881 888 896 897 
### b10 ports
$ grep -c "RBM2D\|RBM1D" (two files)
RBM3D/BA/MAPins.lean:0
RBM3D/BA/MALocal.lean:0
```

### Narrative (row a only)
- Scope: `BA/MAPins` (P1-P6, 22 defs, 3 `Iff.rfl`, 5 `example`s) and `BA/MALocal` (A1-A9), the two import lines of `RBM3D.lean`, three edits in `Test/Axioms.lean`. No file of the ticket's row b, no merged file other than those two root files is touched (`git diff --stat` above).
- `BA/MAPins` was committed alone first (112ffba2, 260 lines at that commit); 7a8294ac only adds `example`s of the P6 readings. Row b needs only P4-P6 (`BA/MAPins`).
- Routes (merged file:line): P1-P3 = probe `t/T2449` 921369b `RBM3D/Probe/T2449Pins.lean:158-217, 232-257` with `BAGz`, `BAMz`, `BAprof` kept as defs; P4-P5 = `Universality/PinsK.lean:406-414`, `BA/UNPins.lean:169-174, 181-186` cut at one `d`; P6 `Iff.rfl`.
- A1 (public helpers `MALocal_G_sub_M`, `MALocal_avg_sub_m`, `MALocal_STWB_le`, `MALocal_Bctl_le`): `Gt_BA` (`Gauss/BlockAnderson:112`), `BAzztE_data` (`BA/MFixedPoint:297`), `BAMres_fine_apply` (`BA/FlowPins:102`), `baKcac_isKLoopS` (`BA/KTreeRep:1674`, `𝒦^{(1)} = m_F`), `STWB_compare` (`Main/ZTransfer:174`), `calB_blk_eq_STWB`, `EMn2BA_*` (`BA/EMn2BA`).
- A2 = twin of `locSCFixed_of_ML` (`Main/FixedZ:100`): `eventually_forall_of_sections` (`Endpoints:423`) over the chain domain `BAdom κ_f ε`, `UNMLOutBA d` conjuncts 1, 5 at `t = BAflowT0`, `explicit_of_stochDomAt` (`Endpoints:376`) at `τ/2`, A1.
- A3 = twin of `netLoc` (`Main/ZNet:999`) with a new net (cell representatives, `MALocal_net_exists`), cover lemmas as twins of `locBad1_net`, `locBad2_net` (`ZNet:781, 831`) whose carrier-free cores (`znet_geom`, `znet_floor`, `znet_avg1`, `znet_loc1_core`, `znet_loc2_core`) are reached by `open private`; `BAm_sub_le_of_im` (`BA/MReg:84`), `ba_dom_of_bulk` (`BA/RandomLayerBGBA:69`), `net_union_le` (`ZNet:91`). A4 = A3 after A2; A5 = A4 at `unMLOutBA_three` (`BA/MainIndTermBA:47`, merged); A6 = twin of `locSC_to_UNLocAvgBand` (`Endpoints:519`); A7, A8 one line.
- F3 as used: no `κ/2` window, no `BAbulk_window`: net points are cell representatives inside the end domain at `κ`; the fixed-`z` form is called at `(κ, ε, τ/2, D + 15)`. The real range of the ρ-bulk is a new lemma (`MALocal_bulk_abs_le`: `|x| ≤ 2 + 2 d |g|`; `Im z = 0` in `(self_m)` and `|v_i| ≤ 2 d |g|`), `R = 2 + 2 d 𝔡⁻¹` eventually; count `(4R + 2) N^14`, so `net_count` (constant 25) is replaced by the private `MALocal_net_count` (`C ≤ N`).
- F5 (row b, upward coupling) is not used by row a: n/a.
- F6: the registry scan loses `UNLocAvgBA` (head of A7): owed 120 to 119, 0 new; the cover lemmas and the net lemmas are `private` (unpinned helpers, CLAUDE.md §3 (E)); `#assert_rbm_axioms` passes (b2, b8).
- `UNMLOutBA 3` is not a binder in `MALocal` (A5 and the instances use the merged `unMLOutBA_three`; the ticket's F1 "unmerged" is stale, merge commit c536c603); the `BAMAFixed` example of `MAPins` keeps `hML : UNMLOutBA 3` as in the probe text (`BA/MAPins` does not import `BA/MainIndTermBA`).
- Sizes against the ticket (`wc -l` above): `MAPins` 279 (bottom-up 160 / 195 / 265, stop 350: above the high, below the stop line); `MALocal` 927 (495 / 730 / 1,170, stop 1,300: inside); row a total 1,206 (calibrated 888-1,184).
- Hypotheses of the instances: the pins that no M1 theorem concludes (`BAEnd_QDiffL`, `BAEnd_decolL`, `BAThm27L`, `BAQDiffFixed`, `BAMAFixed`, `BAMANetQD`, `BAMADecol`, `BAMAQUE`), `UNTrLocalBARow`, `UNTrLocalInitBARow'` (row b) and `∀ d, BAEnd_locSCL d` (`d > 3`, Jun decision B) are `example` hypotheses only; every deterministic hypothesis (admissibility of `S0`, `κ_*` positivity, `E_*` in the bulk, the window `δ = (π κ_*)³/8` by `BAbulk_window`) is discharged.
- Ports from RBM1D/RBM2D: none (b10); the twins are RBM3D's own band files.
- U5S-C3 hits placed: `MAPins` 70, 75, 81 event sets of `BAlocBad1z`, `BAlocBad2z`, `BAqdBadz`; 100-112 the `∃ z` of the end events; 173-174 the event of P4; 241 an instance. `MALocal` 240 proof-internal `∃ K` (existence of the K-loop solution); 340 private `MALocal_kappa_floor` (`∃ c`); 512-520 private `MALocal_net_exists` (`∃ S`, cells); 636-639, 685-688 private cover lemmas (`∃ z`, `∃ w ∈ S`); 812, 819 event sets of `baMANetLoc`; 876-887 instances. No `∃` constant in a target statement.
- F1 hits: `MALocal` 839 is A5; 49, 837, 857 are docstrings; 871-897 are the instances that feed the merged `unMLOutBA_three` to A2, A3, A6, A8; `MAPins` none.
- C1: the grep has 0 hits (the real-range lemma uses the variable `x`, not `E`).

## (c) Verified Mathlib names used

(each compiled in the build of b2; no name invented, none absent)
- `Nat.floor_le`, `Nat.lt_floor_add_one`, `Nat.floor_le_floor`: floors of the cell indices
- `Finset.card_product`, `Finset.card_image_le`, `Finset.card_le_card`, `Finset.filter_subset`: the cardinality of the net
- `Finset.mem_image`, `Finset.mem_image_of_mem`, `Finset.mem_filter`, `Finset.mem_product`, `Finset.mem_range`: net membership
- `Finset.sum_lt_sum_of_nonempty`, `Finset.single_le_sum`, `Finset.univ_nonempty`: the spectral facts, `Zd d L` nonempty
- `Complex.inv_im`, `Complex.normSq_eq_norm_sq`, `Complex.abs_re_le_norm`, `Complex.im_sum`, `Complex.im_ofReal_mul`: `Im (v - w)⁻¹`
- `Real.one_lt_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg_one`: powers of `N`, `W`
- `tendsto_rpow_atTop`, `Filter.eventually_atTop`, `Filter.Tendsto.eventually_ge_atTop`, `Filter.Tendsto.eventually_gt_atTop`: thresholds
- `abs_sub_abs_le_abs_sub`, `abs_sub`, `one_le_inv₀`, `one_div_le_one_div_of_le`, `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_one₀`, `one_le_pow₀`, `mul_le_of_le_one_left`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`: inequalities
- `ENNReal.ofReal_mul`, `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_natCast`, `measure_mono`: union bound
- `dif_pos` is deprecated in this Mathlib (`dite_eq_left`); not used (`simp only [..., ↓reduceDIte]` instead)

## (d) Open issues and paper-delta candidates

- Paper-delta candidates: none. The three routes of (a′) are proof routes; every Lean statement equals its pin (b5: `Iff.rfl` / term-mode `example`s against `T2514_*`, exit 0, 0 errors); P1-P3 are the probe texts. (Expected: none beyond D689 = T2449a-c.)
- `d > 3`: `UNLocAvgBA_of_BAEnd_locSCL` takes `∀ d, BAEnd_locSCL d`; at `d > 3` this needs `UNMLOutBA d`, open under Jun decision B (§316); `d = 3` is unconditional (`baEnd_locSCL_three`, `unLocAvgBAAt_of_ML 3 le_rfl unMLOutBA_three` = N2's `d = 3` input).
- Row b stacks on `BA/MAPins`: names `UNLocAvgBAAt`, `UNTrLocalBAAt`, `UNTrLocalInitBAAt'` and the three P6 theorems; hash 112ffba2 (first commit of the file), final state at HEAD of `t/T2514` (cf63c909).
- M2 (QDiff) can reuse the public A1 helpers and, by `open private`, `MALocal_net_exists`, `MALocal_net_count`, `MALocal_card_le`, `MALocal_geom`, `MALocal_moduli`; the profile Lipschitz bounds and the `QDiff` expectation half are not here.
- `RBM3D.lean` and `RBM3D/Test/Axioms.lean` are a union at merge with T2515 (different registry lines: row a edits the `UNLocAvgBA` line, its header and the `UNLocAvgk` owner text).

