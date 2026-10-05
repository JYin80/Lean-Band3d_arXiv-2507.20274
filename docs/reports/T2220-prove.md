Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:16:11 UTC 2026

Source read: RBM2D `Universality/Step1RegularityGUE.lean` at c9a24cf (1221 lines; `git show`), RBM3D check file `docs/tickets/checks/T2220-check.lean`, `Pins.lean`, `PinsDens.lean`, `Step1Good.lean`, `FreeConv.lean`, `FreeConvStability.lean:748`, `Sizes.lean`, `FineModel.lean`. Notation: `N = sz.size n = (W L)^d`, `κ' = min κ 1`, `T = t* = N^{-1+τs}`, `t = 1 - e^{-T}`, `a = e^{-T/2}`, `δ = min(τs/4,(1-τs)/3)`.

### (i) Exponent table
| quantity | value | constraint | slack / check |
|---|---|---|---|
| window of `UNGUELocal` exponent (targets 1a,1b) | `τ ∈ (0, τs/8)`; composition at `τ = τs/16` | `τ ≤ τs/4` (edge `N^{-1+τ} ≤ g = N^{-1+τs/4}`); `τ-τs/8 < 0` (regularity error `N^{τ-τs/8}`); `τ-τs/2 < -3τs/8` (strip error vs rate); `τ < τs` (strip edge `Im w ≥ c₀T/8` above `N^{-1+τ}`) | all four are linear in `τ`, no sign hypothesis on `τs` needed beyond `τ>0`; strip slack `τs/8 - τ` (= `1/960` at `τs=1/60, τ=1/960`); sharp: `τ ≥ τs/8` kills both strict ones (target 1b) |
| `UNL32` exponents at `σ=δ` (target 1c) | `δ = min(τs/4,(1-τs)/3) > 0` | `-1+δ ≤ -1+τs/4`; `-1+τs/4 ≤ -δ`; `-1+τs/4+δ ≤ -1+τs/2`; `-1+τs ≤ -3δ` | each follows from `δ ≤ τs/4` or `3δ ≤ 1-τs` (equality allowed in the last), `-δ ≥ -1+τs/4` since `δ ≤ τs/4 ≤ 1 - τs/4` (`τs ≤ 2`) |
| entry tail (S7a) | coordinate `N(0,gueVar)`, `gueVar ≤ 1/N` (`N⁻¹` diag, `(2N)⁻¹` off-diag); `#CoordF = N·N·2 = 2N²` | `P(|ω_c| ≥ 1/2) ≤ 2e^{-N/8}`; `‖X_xy‖ ≤ |re|+|im| ≤ 1` | union `4N²e^{-N/8} ≤ N^{-(D+1)}` iff `4N^{D+3}e^{-N/8} ≤ 1`, true for `N` large (`N → ∞` only, no `Admissible`); `UNGUELocal` at `(κ,τ,D+1)`; sum `2N^{-(D+1)} ≤ N^{-D}` iff `N ≥ 2` |
| `gue_err_pow` (target 2b) | on event, `|Re z| ≤ 2-κ`, `N^{-1+τ} ≤ Im z ≤ 10`, `Im z ≥ cN^{-1+σ}`, `c>0`, `N ≥ 1` | `N·Im z ≥ cN^σ`, so `N^τ/√(N Im z) ≤ c^{-1/2}N^{τ-σ/2}` | exact (needs `Im z>0`, which `N^{-1+τ}>0` gives) |
| time `T` | `T = N^{-1+τs} ∈ (0,1]` for `N≥1`, `τs<1` | `T ≤ c₀ = κ'/240` (stability), `t ∈ [T/2, T]`, `a⁻¹ = e^{T/2} ≤ 1+T ≤ 2` | threshold `N^{-1+τs} ≤ κ'/240` (row eT below) |
| domain (`_domain` :690) | `z = a⁻¹(w+E₀)`, `|E₀| ≤ 2-κ`, `|Re w| ≤ R ≤ κ'/4`, `T ≤ κ'/240` | `|Re z| ≤ (1+T)(R+2-κ) ≤ 2-κ/2` (event at `κ/2`); `Im z ≥ Im w`; `Im z ≤ (1+T)/2 ≤ 1` | slack `(2-κ/2) - (1+T)(R+2-κ) ≈ 0.24κ` (script D, `2.4e-05` at `κ=1e-4`) |
| regularity (2.2): `c, C` | `c = κ'/960`, `C = 2` (Prop pinned) | chain at `η ≤ 1/2`: `Im m_sc ≥ κ'/12` (`_msc_im_ge` :627, `|Re|≤2-κ'/2`, `Im z ≤ 3`) minus error `≤ κ'/24` gives `Im m_N ≥ κ'/24`; for `1/2 < η ≤ 10`: `η Im mV` nondecreasing (`mV_eta_mul_im_mono`) gives `η S ≥ κ'/48`, `S ≥ κ'/480`; `Im mV = a⁻¹ S ≥ S` | final `≥ κ'/480 ≥ κ'/960 = c` (slack factor 2). Upper: `η ≤ 1/2`: `a⁻¹(1+κ'/24) ≤ 2`; `η > 1/2`: `Im mV ≤ 1/η < 2` (`mV_im_le_inv`). **Ticket row correction (T2220a'):** the ticket table's "bulk `Im m_sc ≥ min κ 1/480`" is the end of this chain for `Im m_N` at `η ≤ 10`; the in-file `m_sc` bound is `κ'/12`. No change to any statement. |
| regularity error | `N^{τ-τs/8}` at `Im z ≍ g = N^{-1+τs/4}` (`σ = τs/4`, `c=1`) | `≤ κ'/24` | exponent `-(τs/8-τ) < 0` strict |
| (2.3) `CV = 2` | `|λ_i| ≤ N` on entry event (`‖X‖ ≤` row sum; `_eigenvalue_le` :741) | `|v_i| ≤ a|λ_i|+|E₀| ≤ N+2 ≤ N²` | iff `N ≥ 2` (`N²-N-2=(N-2)(N+1)`) |
| stability constants | `freeConv_stable_local hκ`: `c₀ = κ'/240`, `C₀ = 2` (`FreeConvStability.lean:748-760`) | needs `0<t≤c₀`, `s=1-t`, `|E₀|≤2-κ`, `0≤ε≤c₀`, strip `|Re w| ≤ κ'/16`, `c₀t/4 ≤ Im w ≤ 1/2` with `‖mV - a⁻¹ msc(a⁻¹(w+E₀))‖ ≤ ε` | `ε = N^{-3τs/8}/C₀ ≤ c₀` iff `N^{-3τs/8} ≤ c₀C₀`; conclusion `|ρ - ρ_sc(E₀)| ≤ C₀ε = N^{-3τs/8}` exactly; `mfc = freeConvST`, `IsFreeConv32 v t (freeConvST v t)` for `t ≥ 0` (`FreeConv.lean:660`) |
| strip error | `ε_cl ≤ a⁻¹ c₁^{-1/2}N^{τ-τs/2}`, `c₁ = min 1 (c₀/8)`, `σ=τs` (`Im z ≥ Im w ≥ c₀T/8`) | `≤ N^{-3τs/8}/C₀` | split `N^{τ-τs/2} = N^{τ-τs/8}·N^{-3τs/8}`; need `N^{τ-τs/8} ≤ √c₁/(2C₀)` (row eerr); `a⁻¹ ≤ 2` (c9a24cf `_strip` :964-1043) |
| strip edge | `N^{-1+τ} ≤ (c₀/8)N^{-1+τs}` | `N^{τ-τs} ≤ c₀/8` (row eedge) | exponent `-(τs-τ) < 0` |
| `UNL32` premises at `v n = vGUE(ω_n)` (consumer check) | `g = N^{-1+τs/4}`, `G = N^{-δ}`, `t = 1-e^{-T}`, `E n = 0`, `ρ n = ρ'`, `σ = δ`, `q = 1/2`, `c = κ'/960`, `C = CV = 2` | `N^δ/N ≤ g ≤ N^{-δ}`, `G ≤ N^{-δ}`, `gN^σ ≤ t ≤ N^{-σ}G²`, `|0| ≤ qG`, `IsRegular32`, `IsFreeConv32`, density limit at `E=0` | rows 1-2 of the `gue_l32_exponents` row; `gN^δ ≤ N^{-1+τs/2} ≤ T/2 ≤ t` needs `N^{τs/2} ≥ 2`; `t ≤ T ≤ N^{-3δ}` equality-safe; the last three are the three components of `GUEGoodAt`, same tokens as `UNStep1Good'` (`PinsDens.lean:76-82`) with `ρ n ↦ rhoSC E₀`, `vOU ↦ vGUE`; `ω_n` chosen in the good event (nonempty by P(bad) ≤ N^{-D} < 1) |
| two data, one model (O1) | n/a: GUE has one datum `msc`, `ρ = ρ_sc(E₀)` | — | — |
| `d ≥ 3` | `d` only in `Idx d`, `CoordF d`, `gueVar d` (`N = (WL)^d`); every exponent in `τs, τ` | no `Admissible`, no `τs ≤ 𝔠𝔡` | — |

### (ii) One concrete instance: `d = 3`, `sz0`, `κ = 1`, `τs = 1/60`, `E₀ = 1`, `τ = τs/16 = 1/960`, `D = 2`
Hypotheses: `3 ≤ 3`; `size → ∞` (`sz0_tendsto`); `κ>0`; `0<τs<1`; `|E₀| = 1 ≤ 2-κ = 1`; `0<τ<τs/8 = 1/480`; `D>0`. `N_n = 2097152 (n+1)^18` (`sz0.L = 4(n+1)`, `sz0.W = (2(n+1))^5`). `UNGUELocal` is the one kept hypothesis (owed UN-09/UN-10; `Pins.lean:483-489` describes it as the weak averaged bulk local law of the `N×N` GUE, `N=(WL)^d`, union over `z` inside the probability). Constants: `c₀ = 1/240`, `C₀ = 2`, `δ = 1/240`, `c = 1/960`, `ρ_sc(1) = 0.27566 ≠ ρ_sc(0) = 0.31831` (`inst_rhoSC_one_lt_zero`, merged). Every statement of the instances is eventual in `n` (DECISIONS §56); the `ln N` thresholds come from the script (rows eg…eeps are the size conditions of c9a24cf `_det`, :1044-1104).
Commands (scratch, `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2220/`): `python3 pre.py`, `python3` one-liners (`out2.txt`). Output verbatim:
```
exponent conjunctions (gue_window, _sharp, l32_exponents) all true: True
tau_s=1/60 tau=0.0010417 tau-ts/8=-0.0010417 tau-ts/2=-0.0072917 -3ts/8=-0.0062500 slack=1/960 delta= 1/240
tau_s=1/200 tau=0.0003125 tau-ts/8=-0.0003125 tau-ts/2=-0.0021875 -3ts/8=-0.0018750 slack=1/3200 delta= 1/800
eg  N^(-1+ts/4)<=1/2                                       ln N >=       0.7
eG  N^(-delta)<=kp/4                                       ln N >=     332.7
eT  N^(-1+ts)<=min(kp/240,c0)                              ln N >=       5.6
eerr N^(tau-ts/8)<=min(kp/24,sqrt(min(1,c0/8))/(2C0))      ln N >=    4959.7
eedge N^(tau-ts)<=c0/8                                     ln N >=     483.8
eeps N^(-3ts/8)<=c0*C0                                     ln N >=     766.0
binding ln N threshold = 4959.7 ; ln N_0 = ln 2097152 = 14.556
N_n=2097152 (n+1)^18 -> need n+1 >= 2.058e+119 (log10 = 119.3)
entry tail D=1: 4N^2 e^{-N/8} <= N^-2 at N=2^21: log10 lhs = -113821.80408441892
2N^{-(D+1)}<=N^{-D} iff N>=2: ok at N=2^21; N^2>=N+2 iff N>=2
min over grid of Im msc/(kp/12), Im z<=3: 3.115 (>=1 needed)
min over grid of Im msc/(kp/480), Im z<=10: 46.532 (>=1 needed)
min slack (2-k/2)-(1+T)(R+2-k) over k in (0,2]: 2.42e-05 (>0 needed)
N=2000: max_{s,x,y}|X_xy| over 20 samples = 0.111 (<=1 needed)
eta=0.0005161  max_s|mN-msc|=0.7904  bound N^tau/sqrt(N eta)=0.9921
eta=1  max_s|mN-msc|=0.0003406  bound N^tau/sqrt(N eta)=0.02254
--- out2.txt (identity ((2(n+1))^5·4(n+1))^3 = 2^21(n+1)^18 for n<200, then N=2^21 at n=0):
True 2097152
N^2>=N+2 for N>=2: True ; 2N^-(D+1)<=N^-D for N>=2
t=1-e^{-T} in [T/2,T] for T in (0,1]: True
e^{T/2}<=1+T for T in [0,1]: True
rho_sc(1)=0.27566 rho_sc(0)=0.31831
```
Reading of the output. (1) Rows 1-3 (`gue_window`, `_sharp`, `gue_l32_exponents`) hold on a grid of five `τs` and three `τ` each, and by the linear arithmetic of the table. (2) Size conditions at the instance: binding `ln N ≥ 4959.7` (row eerr, `N^{-1/960} ≤ √(1/1920)/4`), i.e. `n+1 ≥ 2.06e119`; the other rows need `ln N ≤ 766`. The entry tail holds at `n=0` already (`log10 = -113821`). So the instances' conclusions are nonempty only for astronomically large `n`; this is the price of `τ = 1/960` with the pinned constants and is inherent in the `∀ᶠ` shape (DECISIONS §56), not a degenerate hypothesis set (nothing is `0`, empty or collapsed; `N_0 = 2^21`). (3) Numerics (`N = 2000`, 20 samples, `E₀ = 1`): `max|X_xy| = 0.111 ≤ 1`; at `η = N^{-1+τs/4}` `max‖m_N-m_sc‖ = 0.790 ≤ 0.992 = N^τ(Nη)^{-1/2}`; at `η=1` `3.4e-4 ≤ 0.0225`: the weak pin is consistent with GUE samples (a sanity check, not a proof of `UNGUELocal`).
Not checked here (mathematics-only stage): the Lean-level scratch `example` `T2220_UN14_GUETranslation` + `step1Band` ⇒ `UNInfty1`; stage 1b/UN-14 owns it. Source note: the file is read at c9a24cf as the ticket cites; RBM2D HEAD (9e0f275) has changed it (1035 lines), line numbers above are c9a24cf.

### Verdicts
- Target 1 (1a `gue_window`, 1b `gue_window_sharp`, 1c `gue_l32_exponents`): PASS (statements true as written; the script covers the arithmetic).
- Target 2 (2a `guelocalEventHighProb`, 2b `gue_err_pow`): PASS (union bound over `2N²` coordinates, `N^{D+3}e^{-N/8} → 0`, `N ≥ 2`; 2b exact algebra).
- Target 3 (`guedetHalf`): PASS (all constants close with the RBM3D `freeConv_stable_local` constants `κ'/240, 2`; `c = κ'/960`, `C = CV = 2` close with slack factor 2 in `c`).
- Target 4 (4a `gueGoodHighProb_of`, 4b `gueGoodHighProb`): PASS (composition at `τ = τs/16 ∈ (0,τs/8)`, `h1` at `(κ/2, τs/16, D)`).
- Target 5 (instances): PASS as eventual statements; thresholds above (`ln N ≥ 4959.7` at `τs=1/60`); the nonempty-event instances follow from `P(bad) ≤ N^{-D} < 1`.
- Design-table correction T2220a (UN-11 has no UN-10/UN-05 dependency by imports) is not contradicted by anything read.

## (b) Script output — Mon Oct  5 22:33:50 UTC 2026
```
$ git log -1 --format='%h %s' | cut -c1-72 ; git diff --stat main...t/T2220 ; wc -l RBM3D/Universality/Step1RegularityGUE.lean
b6fd83b T2220: UN-11 Step1RegularityGUE (GUE-side Step-1 regularity even
 RBM3D/Test/Axioms.lean                     |    1 +
 RBM3D/Universality/Step1RegularityGUE.lean | 1053 ++++++++++++++++++++++++++++
 2 files changed, 1054 insertions(+)
    1053 RBM3D/Universality/Step1RegularityGUE.lean
$ lake build RBM3D.Universality.Step1RegularityGUE 2>&1 | grep -E '^(✔|⚠|✖|Build)' | tail -3   (⚠: replayed imports Tail, InjSum, not this file; this file's own build at 22:26:37 UTC printed ✔, no warning)
⚠ [3304/3347] Replayed RBM3D.Defs.Tail
⚠ [3341/3347] Replayed RBM3D.Universality.InjSum
Build completed successfully (3347 jobs).
$ lake build   (whole library, root #assert_rbm_axioms and Test/AuditNegative; run before the commit; the root import of the new module is added by the hub, so the module itself is checked by the pre-check below)
Build completed successfully (4023 jobs).
lake build  30.71s user 5.50s system 109% cpu 33.186 total
$ grep -cE 'sorry|admit|native_decide|axiom' RBM3D/Universality/Step1RegularityGUE.lean
0
$ lake env lean axioms.lean   (#print axioms of the 18 new public theorems; the 8 targets verbatim, the 10 instances counted)
'RBM.Univ.gue_window' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_window_sharp' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_l32_exponents' [propext, Classical.choice, Quot.sound]
'RBM.Univ.guelocalEventHighProb' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_err_pow' [propext, Classical.choice, Quot.sound]
'RBM.Univ.guedetHalf' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueGoodHighProb_of' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueGoodHighProb' [propext, Classical.choice, Quot.sound]
instances: 10 of 10 lines read 'depends on axioms: [propext, Classical.choice, Quot.sound]'
all: 18 of 18
```
```
-- targets 1-4 (python3 extract.py: text from `theorem <name>` up to `:=`)
theorem gue_window :
    ∀ {τs τ : ℝ}, 0 < τ → τ < τs / 8 →
      τ ≤ τs / 4 ∧ τ - τs / 8 < 0 ∧ τ - τs / 2 < -(3 * τs / 8) ∧ τ < τs
theorem gue_window_sharp :
    ∀ {τs τ : ℝ}, τs / 8 ≤ τ → ¬ (τ - τs / 8 < 0) ∧ ¬ (τ - τs / 2 < -(3 * τs / 8))
theorem gue_l32_exponents :
    ∀ {τs : ℝ}, 0 < τs → τs < 1 →
      0 < min (τs / 4) ((1 - τs) / 3) ∧
      -1 + min (τs / 4) ((1 - τs) / 3) ≤ -1 + τs / 4 ∧
      -1 + τs / 4 ≤ -(min (τs / 4) ((1 - τs) / 3)) ∧
      -1 + τs / 4 + min (τs / 4) ((1 - τs) / 3) ≤ -1 + τs / 2 ∧
      -1 + τs ≤ -(min (τs / 4) ((1 - τs) / 3)) - 2 * min (τs / 4) ((1 - τs) / 3)
theorem guelocalEventHighProb : UNGUELocalEventHighProb
theorem gue_err_pow :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {κ τ : ℝ} {ω : Ω d (sz.L n) (sz.W n)},
      Step1LocalEventGUE sz n κ τ ω → 1 ≤ sz.size n → ∀ {z : ℂ},
        |z.re| ≤ 2 - κ → Nsz sz n ^ (-1 + τ) ≤ z.im → z.im ≤ 10 → ∀ {c σ : ℝ}, 0 < c →
          c * Nsz sz n ^ (-1 + σ) ≤ z.im →
            ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ ≤ Real.sqrt c⁻¹ * Nsz sz n ^ (τ - σ / 2)
theorem guedetHalf : UNGUEDetHalf
theorem gueGoodHighProb_of : UNGUELocalEventHighProb → UNGUEDetHalf → UNGUEGoodHighProb
theorem gueGoodHighProb : UNGUEGoodHighProb
-- target 5, the six instances of the check file 2.5 (python3 extract_inst.py)
theorem inst_sz0_size_tendsto : Tendsto (fun n => sz0.size n) atTop atTop
theorem inst_guelocalEvent_sz0 :
    UNGUELocal → ∀ᶠ n in atTop,
      gueP 3 (sz0.L n) (sz0.W n) {ω | ¬ Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))
theorem inst_event_nonempty_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n),
      Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω
theorem inst_guedetHalf_sz0 :
    ∀ᶠ n in atTop, ∀ ω : Ω 3 (sz0.L n) (sz0.W n),
      Step1LocalEventGUE sz0 n (1 / 2) (1 / 960) ω → GUEGoodAt sz0 n 1 (1 / 60) 1 ω
theorem inst_gueGood_sz0 :
    UNGUELocal → ∀ᶠ n in atTop,
      gueP 3 (sz0.L n) (sz0.W n) {ω | ¬ GUEGoodAt sz0 n 1 (1 / 60) 1 ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))
theorem inst_gueGood_nonempty_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n), GUEGoodAt sz0 n 1 (1 / 60) 1 ω
-- extra instances: inst_gueGoodHighProb_of_sz0 (target 4a; statement of inst_gueGood_sz0), inst_size_zero_sz0 (N_0 = 2097152, L = 4, W = 32), and, for targets 1a-1c and 2b:
theorem inst_exponents_sz0 :
    (1 / 960 : ℝ) ≤ (1 / 60 : ℝ) / 4 ∧ (1 / 960 : ℝ) - (1 / 60 : ℝ) / 8 < 0 ∧
      (1 / 960 : ℝ) - (1 / 60 : ℝ) / 2 < -(3 * (1 / 60 : ℝ) / 8) ∧ (1 / 960 : ℝ) < 1 / 60 ∧
    (¬ ((1 / 480 : ℝ) - (1 / 60 : ℝ) / 8 < 0) ∧ ¬ ((1 / 480 : ℝ) - (1 / 60 : ℝ) / 2 < -(3 * (1 / 60 : ℝ) / 8))) ∧
    0 < min ((1 / 60 : ℝ) / 4) ((1 - 1 / 60) / 3)
theorem inst_gue_err_pow_sz0 :
    UNGUELocal → ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n),
      ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) ⟨0, 1⟩ - msc ⟨0, 1⟩‖ ≤
        Real.sqrt (1 : ℝ)⁻¹ * Nsz sz0 n ^ ((1 / 960 : ℝ) - (1 / 60 : ℝ) / 2)
-- proof term of inst_guedetHalf_sz0 (sed -n 980,981p): every deterministic hypothesis by le_rfl, one_pos, norm_num
  guedetHalf 3 le_rfl sz0 inst_sz0_size_tendsto 1 (1 / 60) 1 one_pos (by norm_num) (by norm_num)
    (by norm_num) (1 / 960) (by norm_num) (by norm_num)
```
```
$ lake env lean T2220-check-scratch.lean   (the ticket's check file + import of the new module + 14 lines `example : T2220_<name> := RBM.Univ.<theorem>`: 8 targets, 6 instances)
exit 0; lines containing 'error': 0
$ python3 diffcheck.py   (check sections 2.1-2.5 against the file)
2.1 vocabulary defs (whitespace-normalized text equal to the check file): 6 of 6: vGUE, Step1LocalEventGUE, GUEGoodAt, UNGUELocalEventHighProb, UNGUEDetHalf, UNGUEGoodHighProb
2.2-2.5 target/instance statements (14): identical text: 8; identical up to `open RBM.Gauss.SizesInst` (sz0): 6; different: 0
$ python3 tokencheck.py   (event of UNStep1Good', PinsDens.lean:78-84, with vOU->vGUE, c C (CV0+1)->(min κ 1/960) 2 2, rho n->rhoSC E0, E->E0, against the body of GUEGoodAt)
equal: True
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Universality.Step1RegularityGUE; #assert_rbm_axioms; scratch, uncommitted)  vs the same without the new import
exit 0
without: axiom audit: 6477 theorems, 2222 definitions, 0 axioms | scan: 126 (borrowed 1, owed 94, structural 25, refuted 6). | registry: 2 borrowed + 145 owed + 81 structural + 7 refuted
with:    axiom audit: 6495 theorems, 2228 definitions, 0 axioms | scan: 127 (borrowed 1, owed 94, structural 26, refuted 6). | registry: 2 borrowed + 145 owed + 81 structural + 7 refuted
  RBM.Univ.UNGUELocal: 21 [no certificate]   (without)     RBM.Univ.UNGUELocal: 27 [no certificate]   (with)
$ git diff -U0 HEAD~1 HEAD -- RBM3D/Test/Axioms.lean | grep '^+ ' | cut -c1-100
+   `RBM.Univ.Step1LocalEventGUE, -- bulk universality: the GUE-side local event (averaged law at th
$ grep -nE 'UNStep1Good|UNInfty1Row|UNStep1GoodC|UNCoreC|UNTrLocalInit|UNDensBandRow' RBM3D/Universality/Step1RegularityGUE.lean | cut -c1-96   (refuted pins and UNDensBandRow; hits: comments naming the owed primed pins)
26:* S7 `gueGoodHighProb`: the composition at `τ = τs/16`, the input of UN-14 (`UNInfty1Row'`).
62:/-- `GUEGoodAt`: the GUE-side good event (RBM2D `:78`) in the shape of the event of `UNStep1G
```
```
$ for n in $(grep -ohE '^(theorem|def) [A-Za-z0-9_]+' RBM3D/Universality/Step1RegularityGUE.lean | awk '{print $2}') Step1RegularityGUEInst; do ...; done   (main worktree, afdb81e: grep -rnwF $n RBM3D RBM3D.lean)
25 names (6 defs, 8 targets, 10 instances, the instance namespace); total hits outside the new file: 0
$ grep -rn 'Step1RegularityGUE_' RBM3D | wc -l   (prefix of the 26 private helpers, main worktree)
0
$ RBM2D (read-only): git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h ; show c9a24cf:RBM2D/Universality/Step1RegularityGUE.lean | wc -l ; diff --stat c9a24cf HEAD -- <file>
9e0f275
    1221
 RBM2D/Universality/Step1RegularityGUE.lean | 312 ++++++-----------------------
 1 file changed, 63 insertions(+), 249 deletions(-)
```

### Narrative (b)
1. File `RBM3D/Universality/Step1RegularityGUE.lean`, 1053 lines; imports `Step1Good`, `FreeConvStability`, four Mathlib files (lines 6-11); branch `t/T2220`, one commit touching this file and `Test/Axioms.lean` (one inserted line).
2. Port of RBM2D `Universality/Step1RegularityGUE.lean` at c9a24cf (1221 lines; RBM2D HEAD 9e0f275 has 1035 lines and was not used). Source lines: vocabulary `:50-120` (`vGUE` `:56`, `Step1LocalEventGUE` `:67`, `GUEGoodAt` `:78`, Props `:93,106,116`); `gue_window` `:140`, `_sharp` `:148`, `gue_l32_exponents` `:196`; entry tail and union bound `:215-377`; `guelocalEventHighProb` `:381`; `gue_err_pow` `:437`; helpers `:475-792`, `bulk` `:792`, `regular` `:839`, `strip` `:964`, `det` `:1044`, `guedetHalf` `:1109`; `gueGoodHighProb_of` `:123`; `gueGoodHighProb` `:1116`.
3. Statements: the six vocabulary defs and the eight targets are text-identical to the check file after whitespace normalization; the six target-5 instances are identical up to `open RBM.Gauss.SizesInst` (diffcheck above). `GUEGoodAt` equals the event of `UNStep1Good'` after the substitution of the ticket (tokencheck). No statement was changed or weakened; no hypothesis added.
4. Dimension changes: `Sizes` -> `Sizes d`, `Ω L W` -> `Ω d L W`, `Coord` -> `CoordF d`, `(W L)^2` -> `(W L)^d` (`RBM.Gauss.card_Idx`, `Sizes.card_Idx`; `Fintype.card (CoordF d L W) = 2 N²` by `Fintype.card_prod`), `d.size n` casts -> `Nsz sz n`, `GUELocal` -> `UNGUELocal`; `GUEGoodAt` has `∃ mfc, IsFreeConv32 ...` with witness `freeConvST` (`isFreeConv51_freeConvST`). `3 ≤ d` is used only to apply `UNGUELocal`; no `Admissible`, no relation between `L` and `W`.
5. Reuse instead of RBM2D copies: `stieltjesN_eq_mV`, `mV_im_le_inv` (replaces `mV_norm_le` `:577`), `stieltjesN_eta_mul_im_mono` (InjSum), and the public `RBM.lemT_ge`, `RBM.msc_add_eq_neg_inv`, `RBM.norm_msc_pos` (RBM2D `:596-621` re-proved them privately). `Step1Good_mV_affine` is private (`Step1Good.lean:107`), so `Step1RegularityGUE_mV_affine` is a copy. `locDomain` is not used: `Step1RegularityGUE_domain` states its three conjuncts. Elementary facts on `a = e^{-T/2}` are re-proved under the prefix `Step1RegularityGUE_` (26 private helpers).
6. Not ported: `gue_count_exponents` `:160`, `gue_count_rate_free` `:180`, `gue_window_rate` `:154`, the RBM2D section-7 instances (replaced by the `sz0` instances).
7. Constants: `freeConv_stable_local` is applied through `obtain ⟨c₀, C₀, ...⟩`; `c = min κ 1/960`, `C = CV = 2` do not depend on `c₀`, `C₀`; the bound used for `1/2 < η ≤ 10` is `min κ 1/480 ≤ S₂` (`Step1RegularityGUE_regular`), as in (a), so `c` closes with factor 2.
8. The one kept hypothesis of the instances is `UNGUELocal` (owed, UN-09/UN-10): the pinned weak averaged bulk local law of the `N × N` GUE (`Pins.lean:483-489`); it is a hypothesis here, not proved; the `N = 2000` numerics of (a) are consistent with it and are not a proof. "Two data, one model" (O1): n/a, `GUEGoodAt` has the one datum `msc`, `ρ = rhoSC E₀`.
9. Instances are eventual in `n` (DECISIONS §56). The binding size threshold at `τs = 1/60`, `τ = 1/960` is `ln N ≥ 4959.7` (row eerr of (a): `n+1 ≥ 2.06e119` at `sz0`); the instances do not exhibit such an `n`. Nonemptiness: `inst_event_nonempty_sz0`, `inst_gueGood_nonempty_sz0` (`P(bad) ≤ N^{-D} < 1` for large `N`), `inst_size_zero_sz0` (`N_0 = 2097152`, `L = 4`, `W = 32`).
10. Registry: before the line was added the pre-check at 22:22:19 UTC failed with exactly one premise, `RBM.Univ.Step1LocalEventGUE`; it is now one structural line (condition on data, class as `IsRegular32`). `GUEGoodAt` was not flagged. Scanned owed premises 94 and registered owed 145, equal to the branch without the new module; no owed line deleted; no refuted pin used; `UNGUELocal` carriers 21 -> 27 (the new theorems).
11. Not targets, not done: `UNInfty1Row'` and the GUE translation (UN-14); the scratch `example` `T2220_UN14_GUETranslation` + `step1Band` => `UNInfty1` of preflight (i) (section (a) leaves it to UN-14); check section 3 elaborates in the scratch, and `T2220_gueGoodHighProb` is closed by `gueGoodHighProb`.
12. Merge note for the hub (§20 (3)): `Test/Axioms.lean` conflicts only inside `structuralProps`: take the union; add `import RBM3D.Universality.Step1RegularityGUE` after the last `import` line of `RBM3D.lean`.
13. Section (a) was read and not edited; no mistake found, so there is no `(a′)`; one documentation difference is listed in (d).

## (c) Verified Mathlib and project names (`#check` ok in this session; every other name used elaborates; none checked absent)
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`, `.id_map_iff`, `.neg`; `ProbabilityTheory.mgf_id_gaussianReal`, `integrable_exp_mul_gaussianReal`; `MeasureTheory.Measure.infinitePi_map_eval`
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_neg_atTop`, `tendsto_natCast_atTop_atTop`, `tendsto_natCast_atTop_iff` (`Mathlib.Order.Filter.AtTopBot.Archimedean`)
`MeasureTheory.measure_iUnion_fintype_le`, `MeasureTheory.measureReal_union_le`, `ENNReal.le_ofReal_iff_toReal_le`, `ENNReal.ofReal_lt_one`
`Real.rpow_one_add'`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.exp_half`, `Real.sqrt_inv`, `inv_lt_one_of_one_lt₀`
Project: `RBM.lemT_ge`, `RBM.msc_add_eq_neg_inv`, `RBM.norm_msc_lt_one`, `RBM.norm_msc_pos`, `RBM.Gauss.card_Idx`, `RBM.Univ.stieltjesN_eta_mul_im_mono`, `RBM.Univ.stieltjesN_eq_mV`, `RBM.Univ.mV_im_le_inv`

## (d) Open issues and paper-delta candidates
- T2220a (design table, no paper statement; ticket's own candidate): the portmap row UN-11 (`T2162-portmap.md:205`) lists UN-10, UN-05 as dependencies; by the import lines of the new file (§54) UN-11 depends on UN-12 (`Step1Good`) and UN-06 (`FreeConvStability`) only.
- T2220b (documentation, from (a), no statement change): the ticket's design-table row "(2.2) ... bulk `Im m_sc ≥ min κ 1 / 480`" is not a bound on `m_sc`; the in-file bound is `Im m_sc ≥ κ'/12` (`Step1RegularityGUE_msc_im_ge`, `|Re z| ≤ 2 - κ'/2`, `Im z ≤ 3`, `κ' = min κ 1`); the chain ends at `κ'/480` for `η Im m_N` (`1/2 < η ≤ 10`) and gives `c = κ'/960`.
- No Lean/paper statement difference was found: the vocabulary is internal to the Lean development (the paper cites [YY25]; `UNGUELocal` is already recorded as not in the paper, `Pins.lean:485`).
- Open: instance thresholds are astronomically large (`ln N ≥ 4959.7` at the instance); inherent in the eventual form with the pinned constant `c = min κ 1/960` and `τ = τs/16`; nothing is degenerate (`N_0 = 2^21`).
- `UNGUELocal`, UN-14 (`UNInfty1Row'`, which consumes `gueGoodHighProb`) remain owed; nothing is registered as proved by this ticket.
