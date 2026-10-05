Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct  5 23:15:53 UTC 2026

Pins (all in `RBM3D/Main/FixedZ.lean`, text of probe 97d958e): `locSCFixed`, `QDiffFixed`, `MAFixed := (∀ d, UNMLOut d) → locSCFixed ∧ QDiffFixed`,
`MADecol := locSC → decol`. Paper = `paper/tex/1_2_Intro_model_result.tex` (1_2:line).

### (i) Exponent table
| # | Quantity | Value / form | Constraint | Slack |
|---|---|---|---|---|
| 1 | `𝔠` (Main_DEL_COND 1_2:359) | 1/6 | `W ≥ N^𝔠`, `Bandwidth` | sz0: `N ≤ W^6` (L ≤ W) all n<2000; n=0: N^{1/6}=11.31 ≤ W=32 |
| 2 | `𝔡` (eq:WO 1_2:363) | 1/10 | `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` | n=0: W^{-7/5}=1/128 ≤ lam=1/64 ≤ 10 (factor 2 below; sz0: lam=(2(n+1))^{-6}, W^{-7/5}=(2(n+1))^{-7}) |
| 3 | `d` | 3 | `3 ≤ d` (inside `locSCFixed`, `QDiffFixed`, `decol`; the lemma `decol_scalars` itself needs only `2 ≤ d`) | no `L^d ≤ W^K` (§29 (3)) |
| 4 | `κ, ε` (𝐃_{κ,ε}, 1_2:380) | 1/10, 1/20 | `κ ≤ 2`, `ε ≤ 1` (else domain empty, `locDomain_empty_*`: proofs split off these cases) | z=i is in 𝐃 for every n (`locDomain_nonempty`); lower edge n=0: N^{-1+ε}=9.87e-7 |
| 5 | `τ, D` | 1/10; D=2 (fixed-z), D=1 (decol) | `τ, D > 0` | W^τ=1.414 at n=0 |
| 6 | `W^{τ/2}` vs 2 (`locSCFixed_of_ML`, form bridge `explicit_of_prec` at `τ/2`, `W^τ=W^{τ/2}·W^{τ/2}`) | ≥ 2 eventually | `W → ∞` (`RBM.Green.tendsto_W` from Admissible) | sz0: first n=7 (W=2^20); derived inside, not a premise |
| 7 | `W^{τ/2}` vs 8, 5 (`QDiffFixed_of_ML`: `hW8`; `qd_core` `hW: 5 ≤ W^{τ/2}`) | ≥ 8 ⇒ ≥ 5 | same | sz0: first n=2047 (W=2^60); eventual statement, not a hypothesis |
| 8 | `N^{𝔠τ/2} ≤ W^{τ/2}` (`det_of_prec`, expectation halves) | 1/120 exponent | from `Bandwidth` | n=0: 1.129 ≤ 1.189 |
| 9 | floor `W^{-6/(5𝔠)} ≤ 𝓑_{η,0}^{1/5} 𝓑_{η,K}` (`floor_X`; `STDecay` at D=6/(5𝔠)) | exponent 7.2 | `𝓑 ≥ (Nη)⁻¹ ≥ N⁻¹ ≥ W^{-1/𝔠}`, so product ≥ N^{-6/5} ≥ W^{-6/(5𝔠)} | n=0, z=i: 1.46e-11 ≤ 1.34e-6 (script below) |
| 10 | decol scale `ε_d = min(τ/2,1/2)` (D502) | 1/20 | `ε_d < τ`, `ε_d ≤ 1` | 2N^{-1+ε_d} ≤ N^{-1+τ} iff N^{τ-ε_d} ≥ 2: n=0: 2.0705 ≥ 2 (3.5%); N^{τ/2}→∞ in general |
| 11 | decol `τ_L = min(𝔡, d ε_d/2)` | 3/40 | need `τ_L < 2𝔡` (term `(lam²W^d)⁻¹ ≤ W^{-2𝔡}`) and `τ_L < d ε_d` (term `N^{-ε_d} ≤ W^{-dε_d}`) so `W^{τ_L}𝓑_{η,0} ≤ 1` eventually | 2𝔡=0.2, dε_d=0.15 vs τ_L=0.075; n=0: W^{τ_L}𝓑=0.788 ≤ 1 (terms 0.162+0.626); fails for no n<3000 |
| 12 | `η = N^{-1+ε_d}` in 𝐃: `N^{-1+ε_d} ≤ 1` | — | needs N ≥ 1 | equality with the lower edge of 𝐃_{κ,ε_d} (allowed, "≤") |
| 13 | `1_2:399 (eq:ukx)`: ψ² ≤ η Im G_xx; Im G ≤ Im m + 1 ≤ 2 | factor 2 | the 2 of row 10 | as row 10 |
| 14 | `btBt` constants (MA-02, `(eq:BtBt)` 1_2:1111) | 2 (at `t₀ = lemT z` only) | `2 W^{τ/2} ≤ W^τ` iff `W^{τ/2} ≥ 2` | row 6 |

Pin lines (what / paper / class / consumer):
- `locSCFixed`: (G_bound) 1_2:388 (squared, `W^τ 𝓑_{η,distB[x][y]}`), (G_bound_ave) 1_2:391 (not squared, `W^τ 𝓑_{η,0}`); `∀ᶠ n` before `∀ z ∈ 𝐃`, union over x,y / a inside, z outside; proved here (`locSCFixed_of_ML`); consumer MA-04 `MANetLoc`.
- `QDiffFixed`: (eq:diffu1,2) 1_2:494,498 (`qdBound`), (Meq:QdS1,2) 1_2:504,507 (`qdBoundExp`); proved here (`QDiffFixed_of_ML`); consumer MA-04 `MANetQD`.
- `MAFixed`: 1_2:1228 with ML:GtLocal 1217, ML:GLoop 1193 (n=1), ML:GLoop_expec (Eq:Gdecay 1205, Eq:Gtlp_exp 1210), hyp `∀ d, UNMLOut d` (owed pin); proved (`fixed_of_ML`); consumer MA-06.
- `MADecol`: Thm 2.1 1_2:357-370, proof 1_2:397-401; hyp `locSC` (owed, ∩_z inside); proved (`decol_of_locSC`); consumer MA-06. Note `MADecol := locSC → decol`, so it does not prove `decol`.

### (ii) One concrete nondegenerate instance
Data: d=3, sz0 (L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{-6}), 𝔠=1/6, 𝔡=1/10, κ=1/10, ε=1/20, τ=1/10, D=2 (decol: D=1), z_n ≡ i (E=0, η=1), time t_n = lemT(i) ∈ [0, lemT]. At n=0: L=4, W=32, N=2097152, lam=1/64. All deterministic hypotheses (Admissible, STFlow's z_n ∈ 𝐃 for every n, 0 ≤ t_n ≤ lemT z_n) hold at once; the only open hypotheses are the owed pins `UNMLOut d`, `locSC`. The eventual thresholds (rows 6, 7) are in the conclusion's `∀ᶠ n`, not hypotheses: sz0 reaches them at n=7 and n=2047.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2225/inst.py` (Python, no Lean; the script restates the Lean definitions `calB`, `qdBound`, `qdBoundExp`, `Sizes`, `msc` from `RBM3D/Endpoints.lean:58-104`, `Defs/Sizes.lean`, `Defs/Semicircle.lean:116`; checks are on n ranges, not for all n)
```
n=0: L,W,N,lam = 4 32 2097152 0.015625 N==(W*L)^3: True
Bandwidth+WO for n<2000: True
n=0: N^(1/6)=11.3137<=W=32 ; W^(-7/5)=0.00781<=lam=0.01562<=1/dd=10
z=i: msc=0.6180339887498949j  m^2+z m+1=0.0e+00  lemT=|m|^2=0.381966  lemE=-0.000000
locDomain(1/10,1/20) at z=i, n=0..1999: True  lower edge n=0: N^(-1+eps)=9.873e-07
decol: eps_d=0.0500 tauL=0.0750 (<= 2*dd=0.20, < d*eps_d=0.1500)
hs1,hs2 of decol_core fail at n in: []
n=0: W^tL*calB=0.7878<=1 ; 2N^(-1+ed)=1.975e-06 <= N^(-1+tau)=2.044e-06 (ratio N^(tau-ed)=2.0705>=2)
  n=0: W^tL*calB=7.878e-01  (first term 1.615e-01, second 6.263e-01)
  n=10: W^tL*calB=1.782e-01  (first term 2.993e-04, second 1.779e-01)
  n=100: W^tL*calB=5.553e-02  (first term 8.881e-07, second 5.553e-02)
  n=10000: W^tL*calB=4.975e-03  (first term 5.125e-12, second 4.975e-03)
W^(tau/2)>=2 (locSCFixed) first n = 7 (W=1048576)
W^(tau/2)>=8 (QDiffFixed) first n = 2047 (W=1152921504606846976)
N>=2 at n=0: True
floor exponent 6/(5c) = 7.200000000000001
  n=0 z=i: floor=1.455e-11 <= min_k B0^(1/5)B_Wk=1.335e-06: True ; N^(-6/5)=2.594e-08
  n=1 z=i: floor=2.118e-22 <= min_k B0^(1/5)B_Wk=2.940e-12: True ; N^(-6/5)=8.162e-15
  n=5 z=i: floor=1.411e-39 <= min_k B0^(1/5)B_Wk=2.892e-21: True ; N^(-6/5)=4.036e-25
  qdBound(n=0,z=i,k=0)=1.358e-09
  qdBound(n=0,z=i,k=2)=1.358e-09
  qdBoundExp(n=0,z=i)=8.959e-10 ; locBad1z threshold W^tau B_{1,0}=4.382e-05
tau/2 scales: N^(c tau/2)=1.1290<=W^(tau/2)=1.1892 at n=0
```
External/owed-hypothesis limit computation (TEAM §8 lesson 14), for `locSC` along sz0: W^{τ_L}𝓑_{η,0} at η=N^{-1+ε_d} is 0.788, 0.178, 0.0555, 0.00498 at n=0,10,100,10^4 (script), consistent with closed forms: first term ≈ (2(n+1))^{-3+0.375} → 0, second ≈ N^{-1/20} W^{τ_L}, N ≥ (2(n+1))^{18}, so ≤ (2(n+1))^{-0.9+0.375} → 0. `UNMLOut`'s own hypotheses (STFlow) are satisfied for all n by the constant z=i (script lines "Bandwidth+WO", "locDomain ... True").

### Verdicts per target
Paper comparison (all PASS; differences are the signed deltas):
- `locSCFixed` vs (G_bound), (G_bound_ave): PASS. Differences: `N₀` uniform over 𝐃 (D500), `L^∞` block distance `W|[x]-[y]|_∞` for |x-y| (D501), explicit `W^τ`/`N^{-D}` (D504), no energy net (the paper's net, 1_2:1228, is MA-04).
- `QDiffFixed` vs (eq:diffu1,2), (Meq:QdS1,2): PASS. `a,b` inside the probability (D503), loop indices (b,a) (D506), `N₀` uniform (D500), D501, D504. The `min(𝓑_0^{1/5}𝓑_{W|a-b|}, 𝓑_0²)` shape and the expectation bound `W^τ 𝓑_0²((lam²W^d)^{-1/5}+𝓑_0)` match 1_2:494-507 verbatim.
- `MAFixed`: PASS vs 1_2:1228 (hypothesis `∀ d, UNMLOut d` is the merged pin's shape, supplied for every d; only the d at hand is used). Observation, not a defect.
- `MADecol`: PASS vs Thm 2.1 / 1_2:399; `η = N^{-1+min(τ/2,1/2)}`, not `N^{-1+τ}` (D502, rows 10-13: the conclusion is `‖ψ‖² ≤ N^{-1+τ}` with constant 1, which `η=N^{-1+τ}` would give only with a constant).
§29 (1)-(7): (1) single time `t_n = lemT z_n` (`STFlow`), no u-grid; (2) `1-ilambda²/L²` boundary absent; (3) no `L^d ≤ W^K`; (4) `∀ᶠ n` before `∀ z` (sections lemma, `eventually_forall_of_sections`), uniform in a,b; (5) unions inside as listed above, `locSC`'s ∩_z inside for `MADecol`; (6) `W→∞`, `N ≥ 2`, `lam ≥ W^{-d/2+𝔡}` derived from `sz.Admissible 𝔠 𝔡` (rows 1, 2, 6, 7, 11); (7) rows 6-9, 14. Two-data-one-model (O1): the pins quantify over d, 𝔠, 𝔡, sz, κ, ε, τ, D, n, z, a, b only; every other object is a function of these: PASS. Consumers: MA-04 `MANetLoc`/`MANetQD`, MA-06 `band_endpoints_of_pins`; no merged consumer.
- locSCFixed: PASS
- QDiffFixed: PASS
- MAFixed: PASS
- MADecol: PASS
Overall verdict: PASS

## (b) Script output (stage 1b, Mon Oct  5 23:20:47 UTC 2026)

### Build, commit, diff-stat
```
$ lake build RBM3D.Main.FixedZ   (tail)
Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
Build completed successfully (3349 jobs).
$ git log -1 --format="%h %an <%ae>" ; git diff --stat main...t/T2225
a1575d4 Jun Yin <321276894+JYin80@users.noreply.github.com>
 RBM3D/Main/FixedZ.lean | 851 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   3 +-
 2 files changed, 853 insertions(+), 1 deletion(-)
$ lake build   (full library; tail)
non-vacuity certificates: 0 of 146 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4027 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Main/FixedZ.lean | wc -l
       0
$ imports of FixedZ.lean
6:import RBM3D.Main.ZTransfer
7:import RBM3D.Green.LDE
```
The full `lake build` does not contain FixedZ (root import is added by the hub at merge); the module-level `#assert_rbm_axioms` check is the pre-check below.

### Registry pre-check (temporary file outside the repo: import RBM3D, import RBM3D.Main.FixedZ, #assert_rbm_axioms)
Before the `structuralProps` line (Axioms.lean unchanged):
```
axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`:
  [RBM.Endpoints.locBad1]    (exit 1; recorded at 23:16:43 UTC, tool log)
```
After the line (after `lake build RBM3D.Test.Axioms`), `lake env lean` exit 0:
```
axiom audit: 6573 theorems, 2241 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
non-vacuity certificates: 0 of 146 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ git diff main...t/T2225 -- RBM3D/Test/Axioms.lean (changed lines)
-   `RBM.Gauss.Sizes.STExpIniIConcl'] -- conclusion of the initial term, regime (i), positive mollifier constants (`6:117`; T2223a); S6-11 (T2223, DECISIONS §20: structural)
+   `RBM.Gauss.Sizes.STExpIniIConcl', -- conclusion of the initial term, regime (i), positive mollifier constants (`6:117`; T2223a); S6-11 (T2223, DECISIONS §20: structural)
+   `RBM.Endpoints.locBad1] -- the bad event of `(G_bound)` in `locSC` (MA-01, `Endpoints.lean:136`); `¬ locBad1` is a hypothesis of the deterministic `decol_core` (MA-03, T2225, DECISIONS §20: structural)
```

### Verbatim (python: block in text, order, and diff against concatenated blocks)
```
C1 probe 1061 1092 lines 32 in text: True after previous: True
C2 probe 1131 1862 lines 732 in text: True after previous: True
C3 probe 2206 2234 lines 29 in text: True after previous: True
C4 probe 2453 2458 lines 6 in text: True after previous: True
total block lines 799
$ diff blocks.txt FixedZ.lean | grep "^[0-9]"   (only added hunks; "<" lines: 0)
0a1,41
32a74
764a807,811
793a841
799a848,851
$ sed -n 472,507p RBM3D/Endpoints.lean | diff - probe[1094,1129] | wc -l
       0
```
Hunks: 0a1,41 head (copyright, imports, docstring, set_option, opens, namespace); 32a74 and 764a807,811 blank/`namespace Inst`/`open`; 793a841 blank; 799a848,851 blank/`end Inst`/`end RBM.Endpoints`. The allowed added lines only.

### `#print axioms` of the 22 theorems
```
'
RBM.Endpoints.Bctl_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.STKloop_one' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.locSCFixed_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.zdistInf_neg'' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.floor_X' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.qd_core' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.prob_union_le' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.two_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.qd_exp_core' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.QDiffFixed_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.fixed_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.Gres_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.ukx' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.zdistInf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.decol_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.decol_spectral_core' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.decol_core' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.decol_of_locSC' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.Inst.inst_decol_of_locSC' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.Inst.inst_locSCFixed' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.Inst.inst_QDiffFixed' depends on axioms: [propext, Classical.choice, Quot.sound] '
RBM.Endpoints.Inst.inst_decol_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] 
```

### Check-file equality (scratch file = check file with `import RBM3D.Main.FixedZ` + 26 examples), `lake env lean`
```
exit 0 ; examples: 26 ; error lines: 0
```

### Targets: pins (extracted by script from FixedZ.lean)
```
def locSCFixed : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      Sizes.seqP sz {ω | locBad1z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def QDiffFixed : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      (Sizes.seqP sz {ω | qd1Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im
def MAFixed : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed ∧ QDiffFixed
73:def MAFixed : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed ∧ QDiffFixed
100:theorem locSCFixed_of_ML (hML : ∀ d, UNMLOut d) : locSCFixed := by
419:theorem QDiffFixed_of_ML (hML : ∀ d, UNMLOut d) : QDiffFixed := by
538:theorem fixed_of_ML : MAFixed := fun hML => ⟨locSCFixed_of_ML hML, QDiffFixed_of_ML hML⟩
787:def MADecol : Prop := locSC → decol
789:theorem decol_of_locSC : MADecol := by
theorem locSCFixed_of_ML (hML : ∀ d, UNMLOut d) : locSCFixed := by
  intro d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hA' := hA
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA'
  by_cases hκ2 : κ ≤ 2
  swap
  · exact Filter.Eventually.of_forall fun n z hz => absurd hz (locDomain_empty_kappa sz (not_le.mp hκ2) n z)
  by_cases hε1 : ε ≤ 1
  swap
  · filter_upwards [hsz.eventually_gt_atTop 1] with n hn z hz
    exact absurd hz (locDomain_empty_eps sz (not_le.mp hε1) hn z)
  have hne : ∀ n, Nonempty {z : ℂ // sz.locDomain κ ε n z} := fun n =>
theorem QDiffFixed_of_ML (hML : ∀ d, UNMLOut d) : QDiffFixed := by
  intro d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hA' := hA
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA'
  by_cases hκ2 : κ ≤ 2
  swap
  · exact Filter.Eventually.of_forall fun n z hz => absurd hz (locDomain_empty_kappa sz (not_le.mp hκ2) n z)
  by_cases hε1 : ε ≤ 1
  swap
  · filter_upwards [hsz.eventually_gt_atTop 1] with n hn z hz
    exact absurd hz (locDomain_empty_eps sz (not_le.mp hε1) hn z)
  have hne : ∀ n, Nonempty {z : ℂ // sz.locDomain κ ε n z} := fun n =>
```

### The compiled nonempty instances (C3, C4 verbatim; d = 3, sz0 at the data of the ticket)
```
namespace Inst
open RBM.Gauss.SizesInst RBM.Univ.UNInst
theorem inst_decol_of_locSC (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  decol_of_locSC h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num)
    (by norm_num)
hypothesis). -/
theorem inst_locSCFixed (hML : ∀ d : ℕ, UNMLOut d) :
    ∀ᶠ n in atTop, ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z →
      Sizes.seqP sz0 {ω | locBad1z sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2z sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  locSCFixed_of_ML hML 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
and both expectation halves, for every `z ∈ 𝐃_{1/10,1/20}` and every pair of blocks, `N₀` uniform. -/
theorem inst_QDiffFixed (hML : ∀ d : ℕ, UNMLOut d) :
    ∀ᶠ n in atTop, ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z →
      (Sizes.seqP sz0 {ω | qd1Badz sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Badz sz0 (1 / 10) n z ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im :=
  QDiffFixed_of_ML hML 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
theorem inst_decol_scalars :
    ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (min (1 / 10 : ℝ) (((3 : ℕ) : ℝ) * min ((1 / 10 : ℝ) / 2) (1 / 2) / 2)) *
        calB sz0 n (Nsz sz0 n ^ (-1 + min ((1 / 10 : ℝ) / 2) (1 / 2))) 0 ≤ 1 ∧
      2 * Nsz sz0 n ^ (-1 + min ((1 / 10 : ℝ) / 2) (1 / 2)) ≤ Nsz sz0 n ^ (-1 + (1 / 10 : ℝ)) :=
  decol_scalars (d := 3) sz0 (by norm_num) sz0_admissible (τ := 1 / 10) (by norm_num)
end Inst
```
Every deterministic hypothesis is discharged (`le_rfl`, `sz0_admissible`, `norm_num`); the open hypotheses are the owed pins `locSC` and `UNMLOut`. Check-file equality above shows each `inst_*` theorem equals its pin.

### Name-clash grep (new public names vs RBM3D, outside FixedZ.lean)
```
$ grep -rnE "(theorem|def|lemma) (RBM\.Endpoints\.)?(<26 names>)( |$)" RBM3D --include=*.lean | grep -v Main/FixedZ.lean
RBM3D/Green/Pins.lean:1303:private theorem zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
$ grep -cE "^(theorem|def) " RBM3D/Main/FixedZ.lean
26
```
The only hit is the known `private theorem zdistInf_zero` of `Green/Pins.lean:1303` (no clash: Lean accepted the block unmodified, check-file `zdistInf_zero` example resolves to RBM.Endpoints).

### Ports
Source: `git --no-optional-locks show 97d958e:RBM3D/Probe/T2192Pins.lean` (branch `t/T2192`), blocks :1061-1092, :1131-1862, :2206-2234, :2453-2458. No RBM1D/RBM2D text was copied in this ticket (the probe carries its own RBM2D citations in docstrings). No RBM1D/RBM2D diff-stat applies.

### Narrative
- FixedZ.lean = the ticket head (copyright, the two imports, a new docstring, `set_option`s, `noncomputable section`, opens, `namespace RBM.Endpoints`) + C1 + C2 + `namespace Inst` + C3 + C4 + `end Inst` + `end RBM.Endpoints`; 851 lines, 26 declarations.
- The four blocks compiled unedited against `main` (f2766db) with the imports `RBM3D.Main.ZTransfer`, `RBM3D.Green.LDE`; no import was added.
- The worktree base is f2766db (main had moved past afdb81e by T2222, T2223 merges); the registry line was appended after the last entry `STExpIniIConcl'`, whose `]` moved.
- Section (a) was not edited; no (a') needed.

## (c) Verified Mathlib names
No Mathlib name was written by this ticket (verbatim move); every Mathlib name of the blocks elaborated in the build above.

## (d) Open issues and paper-delta candidates
- None. D500, D501, D502, D503, D504, D506 apply as cited in the ticket; no `T2225a`.
- Hub note: `RBM3D.lean` root import `import RBM3D.Main.FixedZ` goes after the last `import` line; the full `lake build` before merge will then run `#assert_rbm_axioms` over FixedZ (already exit 0 by the pre-check).
