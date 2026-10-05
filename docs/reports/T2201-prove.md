Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct  5 18:28:05 UTC 2026

### (i) Exponent table

Notation: `ts = τs = 𝔠𝔡`, `τ = ts/8`, `N = (WL)^d`, `A = lam²W^d`. Facts used: `W ≥ N^𝔠` (`Bandwidth`), `A ≥ W^{2𝔡}` (`WO`, `Sizes.lam_sq_mul_pow_ge`), `W ≤ N`, `un_Bctl_le: Bctl ≤ A⁻¹ + (Nη)⁻¹` (`Pins.lean:961`).

| quantity | value | constraint | slack |
|---|---|---|---|
| `τs` (refutation) | `min(𝔠𝔡, 1/2)`; `1/60` at `(1/6,1/10)` | `0<τs<1`, `τs ≤ 𝔠𝔡` (`UNStep1Good` hypotheses) | `0` vs `𝔠𝔡`, `59/60` vs 1 |
| `D` | `1` | `0 < D` | free |
| rate `N^{-3τs/8}` | `N^{-1/160}` | `2N^{-3τs/8} < 1/(2π)` (4d) | needs `ln N > 404.96`; eventual only (`SizeTendsto`), `N_0` fails |
| two bad events | `2N^{-1}` | `< 1` (`IsProbabilityMeasure`) | `N > 2` (`N_0 = 2097152`) |
| shift height `h_n` | `N^{-2}` | `h_n ≤ N^{-1+ε}` all `ε>0` (UNTrLocal window); `h_n ≤ 1` | `N ≥ 27`; exponent gap `1-ε`; `N_0`: `2.3e-13 ≤ N_0^{-9/10}` |
| box constants band | `c=9/100, K=1, Lp=62` | `c ≤ Im msc` (`un_msc_im_ge`), `‖msc‖<1`, `Lp ≥ 1/(2c²)=61.73` | `Lp`: `0.27` |
| box constants BA `uI` | `c=1/20, K=1, Lp=200` | `Lp ≥ 1/(2c²)=200` (`freeConvST_sub_le`: `(2c)²‖Δm‖ ≤ 2‖Δz‖`) | `0` |
| box vs window | box `0<Im z≤1` | inside `UNDens` window `0<η≤10` | factor 10 |
| jump contradiction | `ε' = min(h_n/2, 1/(4(Lp+Lp')))` | `1/2 ≤ (Lp+Lp')ε'` must fail | `1/2` vs `≤ 1/4` |
| band energy | `κ=1, E=0, δ=1/2` | `|E| ≤ 2-κ`, `δ ≤ κ/2`, `0<δ` | `1`, `0` (equality), `1/2` |

"Two data, one model" test (supervisor O1). Mechanism: from the box Lipschitz bound and the limit in `UNDens`, `|Im m_n(E+iη)/π − ρ_n| ≤ Lp·η/π` (`0<η≤1`). On the common local-law event, at `η = N^{-1/2}` (`≥ N^{-1+ε}`, `ε<1/2`; the point `E+iη` is in both windows),
`|ρ_n − ρ̃_n| ≤ (Lp+L̃p)N^{-1/2}/π + (2/π)W^τ(A⁻¹ + N^{-1/2})`. Decay exponents of `N` of each term against `3τs/8` (script (A)):

| `(𝔠,𝔡)` | `3τs/8` | `N^{-1/2}` | `W^τ W^{-2𝔡} ≤ N^{-𝔠(2𝔡-τ)}` | `W^τ N^{-1/2} ≤ N^{-(1/2-τ)}` | slack (min) |
|---|---|---|---|---|---|
| `(1/6, 1/10)` | `1/160 = 0.00625` | `0.5` | `19/576 = 0.03299` | `239/480 = 0.49792` | `0.0267` (2nd term) |
| `(1/10, 1/20)` | `3/1600 = 0.001875` | `0.5` | `159/16000 = 0.00994` | `799/1600 = 0.49938` | `0.0081` (2nd term) |

UN-12 terms (supervisor 2.2; `ε ≲ W^τW^{-2𝔡} + W^τ/(Nt)`, `t ≈ N^{-1+ts}`, `Nt ≈ N^{ts}`): `t`: `N^{-(1-ts)} = 59/60, 199/200` vs `3ts/8`; `N^{-ts+τ}`: `7/480, 7/1600` vs `1/160, 3/1600`; all strictly larger, min slack `0.00833` and `0.00250` (script (A)). The constraints that close it: `ts ≤ 𝔠𝔡` (floor `W^{-2𝔡}`), `ts < 8/11` (term `t`).
Per pin (what the hypotheses observe of `(m,ρ)`: `m_n` on `|Re z−E| ≤ δ`, `N^{-1+ε} ≤ Im z ≤ 1` via `UNTrLocal`/`UNTrLocalInit`, plus `UNDens'`: `m_n` on the whole box uniformly and `ρ_n = lim π⁻¹Im m_n(E+iη)`):
| pin | conclusion reads | test |
|---|---|---|
| `UNStep1Good'`, `UNStep1GoodC'` | `ρ'` (density at 0 of `v ⊞ sc_t`) vs `ρ_n` within `N^{-3τs/8}` | `ρ'` is the same for both data (common `ω`, same `v`, `t`, uniqueness); needs `|ρ_n−ρ̃_n| ≤ 2N^{-3τs/8}`; true bound is the table above, all terms strictly smaller: PASS |
| `UNInfty1Row'`, `UNCore'`, `UNCoreC'` | only the dilation `O(ρ_n·)` | PASS (argued): `ρ ≥ c/π` (`UNDens`), `O ∈ C_c^∞` so `|O(ρα)−O(ρ̃α)| ≤ ‖∇O‖∞|ρ−ρ̃||α|·1_{|α|≤R'}`; with `|ρ_n−ρ̃_n| ≤ N^{-c₁}` and `≤ N^{kε'}` tuples in the window (local law, `ε'<c₁/k`), the two `k`-point functionals differ by `≤ C_O N^{kε'−c₁} + N^{k−D}‖O‖∞ → 0`; so both `→ 0` limits are compatible. Not a provability proof. |
`UNDens'` (condition on data, no model), `UNDensBandRow'` and `un_bUniv_of_rows'` (fixed data `msc, ρ_sc(E)`) need no test.

T2190a family (ii-prerequisite): `m^h = unDensShift m h`, `h_n = N^{-2}`, meets `UNDens` and `UNTrLocal` (events equal since `N^{-2} ≤ N^{-1+ε}`), but at `z=E+ih_n`, `z'=E+ih_n/2`: `‖Δm^h‖ ≥ 1/2 − Lp h_n/2`, `‖Δz‖ = h_n/2`, ratio `≥ 1/h_n − Lp`. At `sz0`: `n=0`: `N=2097152`, `h=2.274e-13`, ratio `≥ 4.398e12` vs `Lp=62`; `n=1`: `N=549755813888`, `h=3.309e-24`, ratio `≥ 3.02e23`. General form: a perturbation invisible to `UNTrLocal` moving `ρ_n` by `a` changes `Im m_n` by `≥ aπ − o(1)` between `η=0` and `η=N^{-1+ε}`, so `max(Lp,L̃p) ≥ (aπ−o(1))N^{1−ε}/2 → ∞` (argued).

### (ii) One concrete nondegenerate instance
Data: `d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`; `n=0`: `L=4, W=32, lam=1/64, N=2097152`), `(𝔠,𝔡)=(1/6,1/10)`, `k=1`, `E=E'=0`, `δ=1/2`, `ρ_n = ρ_sc(0)=1/π`, `O = bump` (`bump 0 = 1`), `κ=1/10` (`inst_*`) and `κ=1` (`not_UNStep1Good_band`), `D=1`, `τs=1/60`, `CV₀=1`.
Hypotheses discharged at these numbers: `Admissible` (merged `sz0_admissible`; script B checks `n ≤ 20000`), `|0|<2`, `1≤1`, `0<δ`, `δ ≤ κ/2`, `UNDens'` for `msc` (`c,K,Lp = 9/100,1,62`, D), `UNDens'` for `freeConvST uI 1`, `uI=(-1e-4,1e-4)` on `Fin 2` (`1/20,1,200`, D), the shift family (B), the refutation arithmetic (C). Stay hypotheses (other gates, unchanged from merged `inst_*`): the rows, `UNL32`, `UNGUELocal`, `UNGreenCorr(All)(C)`, `UNTrLocal(Init)`, `UNNormBound`, `UNClaimAll(C)`, the consumed `UNMLOut`, `UNLocAvgBand`, `UNQueBand`. No new external hypothesis is introduced (`UNL32` appears only copied from merged `inst_core_band`, `Pins.lean:1773-1776`, not re-examined). Limits computed: `SizeTendsto` (`N_n ≥ n`), `ln N > 404.96`, and `η→0` of the shifted quotient (script C).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2201/preflight.py` (consumer check (E): `hbox`, `hlip` of `freeConv_stable_lip`, `FreeConvRegular.lean:1238-1240`, vs the second conjunct of `UNDens'` in `docs/tickets/checks/T2201-check.lean`)
```
(A) two-data terms: decay exponent of N vs 3ts/8 (ts=c*d, tau=ts/8, W>=N^c, lam^2W^3>=W^{2d}, W<=N)
 (c,d)=(1/6,1/10) ts=1/60 3ts/8=1/160: N^-1/2:1/2  W^tau W^-2d:19/576=0.03299  W^tau N^-1/2:239/480=0.49792  t~N^(-1+ts):59/60  N^(-ts+tau):7/480=0.01458; all>3ts/8: True; min slack 0.00833; ts<=cd,ts<1: True
 (c,d)=(1/10,1/20) ts=1/200 3ts/8=3/1600: N^-1/2:1/2  W^tau W^-2d:159/16000=0.00994  W^tau N^-1/2:799/1600=0.49938  t~N^(-1+ts):199/200  N^(-ts+tau):7/1600=0.00438; all>3ts/8: True; min slack 0.00250; ts<=cd,ts<1: True
(B) shift family at sz0 (L=4(n+1),W=(2(n+1))^5,N=(WL)^3), Lp=62, ratio >= 1/h-Lp at z=E+ih, z'=E+ih/2
 n=0: L=4 W=32 N=2097152 h=N^-2=2.274e-13 (<=1: True, <=N^(-9/10): True) ratio>= 4.3980e+12
 n=1: L=8 W=1024 N=549755813888 h=N^-2=3.309e-24 (<=1: True, <=N^(-9/10): True) ratio>= 3.0223e+23
 sz0 Admissible(1/6,1/10), n=0..20000: N_n>=n, W>=N^(1/6), W^(-7/5)=(2(n+1))^-7<=lam<=10: True
(C) refutation: ts=min(cd,1/2)=1/60, D=1; need 2N^(-3ts/8)<1/(2pi) <=> ln N>404.96; at ln N=410: 2N^(-1/160)=0.15422 < 0.15915; N_0=2097152 (ln=14.56) does NOT meet it: eventual only
    limit eta->0 of shifted quotient at n=0: eta=1e-14<h_0=2.274e-13: (Im msc(i eta)+1/2)/pi=0.477465 vs rhoSC(0)+1/(2pi)=0.477465
    kappa=1: |0|<=2-1 True, delta=1/2<=kappa/2 True; N_n>=(1*3)^3=27 for every sz (W>=1,L>=3)
(D) UNDens' constants numerically: Lp=1/(2c^2): msc 1/(2*0.09^2)=61.73<=62 ; uI 1/(2*0.05^2)=200
 msc E=0 dl=1/2 (c=9/100,K=1,Lp=62): grid 240199 pts min Im m=0.0988>=c=0.09:True; max|m| (eta<=1)=1.000000<=K=1.0:True; 2247 near pairs max ratio=0.516, 3000 vertical pairs max=0.516; <=Lp=62.0:True
 freeConvST uI 1 E=0 dl=1/2 (c=1/20,K=1,Lp=200): grid 240199 pts min Im m=0.0988>=c=0.05:True; max|m| (eta<=1)=1.000000<=K=1.0:True; 2283 near pairs max ratio=0.516, 3000 vertical pairs max=0.516; <=Lp=200.0:True
 uI fixed-point residual at z=0.3+0.01i: 2.237726045655905e-16
(E) hbox (FreeConvRegular.lean:1238-1240, mref z->m n z, E0->E) = token substring of UNDens' 2nd conjunct: True
(E) hlip (FreeConvRegular.lean:1238-1240, mref z->m n z, E0->E) = token substring of UNDens' 2nd conjunct: True
```
Not covered (not targets): the C-form rescaling of supervisor 2.2 (UN-12), band bridges for `UNStep1GoodC'`/`UNCoreC'`, refutations of `UNInfty1Row`/`UNCore`/`UNCoreC` (need the GUE one-point limit, argued only).

### Verdict
- Targets 1 (vocabulary/pins), 2 (`toUNDens`, `unDens'_msc_of_unDens`, `unDensBandRow'_of_row`, `unDens'_freeConvST`), 3 (`un_core_of_rows'`, `un_bUniv_of_rows'`), 4 (`unDensShift_of_le`, `unDens_shift`, `unTrLocal(Init)_shift`, `not_unDens'_unDensShift`, `not_UNStep1Good`, `not_UNStep1GoodC`), 5 (`un_msc_box_zero`, `un_dens'_msc_zero`), and the instances `inst_*`, `inst_dens'_uI`, `inst_T2190a_family`, `not_UNStep1Good_band`: **PASS** (every hypothesis set is satisfiable at the data above; every exponent closes with the slacks tabulated; the consumer shape matches token for token).
- Remarks: the refutation rate is eventual only (`N > e^{405}` at `sz0`); a concrete `n` must not be sought. `Lp = 62` is the instance constant (`61.73` needed). Registry edits (`refutedProps`) are not mathematics and are not judged here.

## (b) Script output - written Mon Oct  5 18:45:51 UTC 2026 (`date -u`), commit `b33918f` on `t/T2201`

Files:
```
$ git diff --stat main...t/T2201
 RBM3D/Test/Axioms.lean           |  53 ++-
 RBM3D/Universality/PinsDens.lean | 682 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 723 insertions(+), 12 deletions(-)
```
Build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2201`):
```
$ lake build RBM3D.Universality.PinsDens 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3338 jobs).
$ lake build 2>&1 | tail -2        # whole library: root #assert_rbm_axioms and the Test/AuditNegative.lean reverse test
non-vacuity certificates: 0 of 128 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4003 jobs).
```
Registry pre-check (scratch `import RBM3D` + `import RBM3D.Universality.PinsDens` + `#assert_rbm_axioms`, not committed):
```
$ lake env lean precheck.lean > precheck.out 2>&1 ; echo "precheck exit $?"
precheck exit 0
$ grep "premises found\|^registry" precheck.out | cut -c1-120
premises found by scanning: 111 (borrowed 1, owed 83, structural 23, refuted 4).
registry: 2 borrowed + 126 owed + 59 structural + 4 refuted; 80 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep "^  RBM.Univ.\(UNStep1Good'\|UNInfty1Row'\|UNStep1GoodC'\|UNCoreC'\):" precheck.out     # the owed ledger: the four primed names
  RBM.Univ.UNStep1Good': 0 [no certificate]
  RBM.Univ.UNInfty1Row': 5 [no certificate]
  RBM.Univ.UNStep1GoodC': 0 [no certificate]
  RBM.Univ.UNCoreC': 1 [no certificate]
$ grep -c "^  RBM.Univ.\(UNStep1Good\|UNInfty1Row\|UNStep1GoodC\|UNCoreC\):" precheck.out     # the four refuted names in the owed ledger
0
```
Registry negative test (scratch copy of the committed `Test/Axioms.lean` with `RBM.Univ.UNStep1Good` put back into `owedProps`, plus `import RBM3D.Universality.PinsDens` and `#assert_rbm_axioms`; the error is the disjointness check):
```
$ lake env lean negtest.lean > neg.out 2>&1 ; echo "negtest exit $?" ; head -2 neg.out
negtest exit 1
negtest.lean:529:0: error: axiom audit: 1 refuted premise(s) are also in `borrowedProps`, `owedProps` or `structuralProps`: [RBM.Univ.UNStep1Good]
A refuted pin is in `refutedProps` only (DECISIONS §66 (2)); never put it back into a ledger.
```
Axioms and hygiene:
```
$ lake env lean axioms.lean   # import RBM3D.Universality.PinsDens + one #print axioms per public declaration of PinsDens.lean
declarations printed: 31; axiom set [propext, Classical.choice, Quot.sound]: 31; any other axiom set: 0
$ grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Universality/PinsDens.lean
0
$ git diff main...t/T2201 -- RBM3D/Test/Axioms.lean | grep -cE "^\+(axiom |.*sorry|.*admit|.*native_decide)"
0
```
Statements extracted from the file by script (`python3 extract.py`: definitions in full, theorems up to `:=`, whitespace joined, wrapped at 235 columns):
```
def UNDens' (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) : Prop := UNDens m E ρ δ ∧ ∃ c K Lp : ℝ, 0 < c ∧ 0 < K ∧ 0 < Lp ∧ ∀ᶠ n in atTop, (∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (m n z).im ∧ ‖m n z‖ ≤ K) ∧ (∀ z z' : ℂ,
    |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖m n z - m n z'‖ ≤ Lp * ‖z - z'‖)
noncomputable def unDensShift (m : ℕ → ℂ → ℂ) (h : ℕ → ℝ) : ℕ → ℂ → ℂ := fun n z => m n z + (if z.im < h n then Complex.I / 2 else 0)
def UNStep1Good' : Prop := ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M
    CV₀ → ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D → ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, M.μ {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧ ∃ mfc :
    ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤ ENNReal.ofReal (Nsz sz n ^
    (-D))
def UNInfty1Row' : Prop := UNL32 → UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤
    CV₀ ∧ UNNormBound sz M CV₀) → ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E E' k O τU
def UNCore' : Prop := UNL32 → UNGUELocal → UNGreenCorrAll → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀
    : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) → UNClaimAll sz M E → ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivDilAt sz M ρ E E' k O
def UNDensBandRow' : Prop := ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∃ δ : ℝ, δ ≤ κ / 2 ∧ UNDens' (fun _ => msc) E (fun _ => rhoSC E) δ
def UNStep1GoodC' : Prop := ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound
    sz M.toUNModel CV₀ → ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D → ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C
    (CV₀ + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
    ENNReal.ofReal (Nsz sz n ^ (-D))
def UNCoreC' : Prop := UNL32 → UNGUELocal → UNGreenCorrAllC → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m
    E δ → UNTrLocalInit sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀) → UNClaimAllC sz M E → ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivDilAt sz M.toUNModel ρ E E' k O
theorem UNDens'.toUNDens {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ : ℝ} (h : UNDens' m E ρ δ) : UNDens m E ρ δ
theorem unDens'_msc_of_unDens (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : UNDens (fun _ => msc) E ρ δ) : UNDens' (fun _ => msc) E ρ δ
theorem unDensBandRow'_of_row (h : UNDensBandRow) : UNDensBandRow'
theorem unDens'_freeConvST : ∀ {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)] (u : ∀ n, ι n → ℝ) (E δ c : ℝ), 0 < δ → 0 < c → (∀ᶠ n in atTop, ∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 → c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) → ∃
    ρ : ℕ → ℝ, UNDens' (fun n => freeConvST (u n) 1) E ρ δ ∧ ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 → |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤ η / c ^ 2
theorem un_core_of_rows' (h1 : UNInfty1Row') (h2 : UNUnivMainRow) : UNCore'
theorem un_bUniv_of_rows' (rI : UNInfty1Row') (rU : UNUnivMainRow) (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) : UNL32 → (∀ d : ℕ, UNMLOut d)
    → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll → UNBUniv
theorem unDensShift_of_le (m : ℕ → ℂ → ℂ) (h : ℕ → ℝ) (n : ℕ) (z : ℂ) (hz : h n ≤ z.im) : unDensShift m h n z = m n z
theorem unDens_shift (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hD : UNDens m E ρ δ) : UNDens (unDensShift m h) E (fun n => ρ n + 1 / (2 * Real.pi)) δ
theorem unTrLocal_shift {d : ℕ} (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) (hT : UNTrLocal sz M m E δ) : UNTrLocal sz M (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E δ
theorem unTrLocalInit_shift {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) (hT : UNTrLocalInit sz M m E δ) : UNTrLocalInit sz M (unDensShift m (fun n => Nsz sz n ^ (-2 : ℝ))) E δ
theorem not_unDens'_unDensShift (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ ρ' : ℕ → ℝ) (δ : ℝ) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (h1 : ∀ᶠ n in atTop, h n ≤ 1) (hD : UNDens' m E ρ δ) : ¬ UNDens' (unDensShift m h) E ρ' δ
theorem not_UNStep1Good (hS : UNStep1Good) : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
    UNNormBound sz M CV₀ → False
theorem not_UNStep1GoodC (hS : UNStep1GoodC) : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤
    CV₀ → UNNormBound sz M.toUNModel CV₀ → False
theorem un_msc_box_zero : ∀ z z' : ℂ, |z.re - 0| ≤ 1 / 2 → 0 < z.im → z.im ≤ 1 → |z'.re - 0| ≤ 1 / 2 → 0 < z'.im → z'.im ≤ 1 → 9 / 100 ≤ (msc z).im ∧ ‖msc z‖ ≤ 1 ∧ ‖msc z - msc z'‖ ≤ 62 * ‖z - z'‖
theorem un_dens'_msc_zero : UNDens' (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2)
theorem inst_core_band' (hcore : UNCore') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2)) (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) (hC :
    UNClaimAll sz0 (UNModel.band sz0) 0) : UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)
theorem inst_core_of_rows' (rI : UNInfty1Row') (rU : UNUnivMainRow) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2)) (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0
    (UNModel.band sz0) CV₀) (hC : UNClaimAll sz0 (UNModel.band sz0) 0) : UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)
theorem inst_bUniv_band' (rI : UNInfty1Row') (rU : UNUnivMainRow) (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ,
    UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) : Tendsto (fun n => (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) - (∫ ω,
    kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0)
theorem inst_bUniv_band_k' (rI : UNInfty1Row') (rU : UNUnivMainRow) (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d)) (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand) (rO : UNOURowk (fun
    d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand) (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAll) : Tendsto (fun n => (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) - (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n)
    (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0)
theorem inst_coreC_band' (hcore : UNCoreC') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2)) (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 /
    2)) (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) (hC : UNClaimAllC sz0 (UNModel.band sz0).toC 0) : UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)
theorem inst_dens'_uI : ∃ ρ : ℕ → ℝ, UNDens' (fun _ : ℕ => freeConvST FreeConvRegularInst.uI 1) 0 ρ (1 / 2) ∧ ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 → |(freeConvST FreeConvRegularInst.uI 1 ⟨0, η⟩).im / Real.pi - ρ n| ≤ η / (1 / 20 : ℝ)
    ^ 2
theorem inst_T2190a_family : UNDens (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0 (fun _ => rhoSC 0 + 1 / (2 * Real.pi)) (1 / 2) ∧ (UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) → UNTrLocal sz0
    (UNModel.band sz0) (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0 (1 / 2)) ∧ ¬ UNDens' (unDensShift (fun _ => msc) (fun n => Nsz sz0 n ^ (-2 : ℝ))) 0 (fun _ => rhoSC 0 + 1 / (2 * Real.pi)) (1 / 2)
theorem not_UNStep1Good_band (hS : UNStep1Good) (hLoc : UNLocAvgBand) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) : False
```
Statements against the ticket check file `docs/tickets/checks/T2201-check.lean` (sections 2-3), two ways:
```
$ python3 diff_check_pins.py        # textual: each def of section 2 against the def in PinsDens.lean (docstrings excluded)
check section 2 vs PinsDens.lean, def UNDens': IDENTICAL
check section 2 vs PinsDens.lean, def unDensShift: IDENTICAL
check section 2 vs PinsDens.lean, def UNStep1Good': IDENTICAL
check section 2 vs PinsDens.lean, def UNInfty1Row': IDENTICAL
check section 2 vs PinsDens.lean, def UNCore': IDENTICAL
check section 2 vs PinsDens.lean, def UNDensBandRow': IDENTICAL
check section 2 vs PinsDens.lean, def UNStep1GoodC': IDENTICAL
check section 2 vs PinsDens.lean, def UNCoreC': IDENTICAL
non-identical: 0
$ lake env lean cmp.lean ; echo $?   # check file + `import RBM3D.Universality.PinsDens` + 31 comparisons `T2201Check.X = _root_.RBM.Univ.X := rfl` (8 defs) and `T2201Check.T2201_name = (type_of% @_root_.RBM.Univ.name) := rfl` (15 theorems, 8 instances)
exit 0; examples: 31; compile errors: 0.   Control (two deliberately wrong comparisons added, cmp_neg.lean): compile errors: 2.
```
Each primed pin and primed instance against its merged source after the declared substitution (`diffs.py`; `UNDens -> UNDens'`, `Name -> Name'`, `un_dens_msc_zero -> un_dens'_msc_zero`):
```
$ python3 diffs.py
def UNStep1Good -> UNStep1Good': IDENTICAL
def UNInfty1Row -> UNInfty1Row': IDENTICAL
def UNCore -> UNCore': IDENTICAL
def UNDensBandRow -> UNDensBandRow': IDENTICAL
def UNStep1GoodC -> UNStep1GoodC': IDENTICAL
def UNCoreC -> UNCoreC': IDENTICAL
theorem inst_core_band -> inst_core_band': IDENTICAL
theorem inst_core_of_rows -> inst_core_of_rows': IDENTICAL
theorem inst_bUniv_band -> inst_bUniv_band': IDENTICAL
theorem inst_bUniv_band_k -> inst_bUniv_band_k': IDENTICAL
theorem inst_coreC_band -> inst_coreC_band': IDENTICAL
theorem un_core_of_rows -> un_core_of_rows': DIFFERS
    --- 
    +++ 
    @@ -3 +3 @@
    -  obtain ⟨τ₀, hτ₀, hU⟩ := h2 hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hC k
    +  obtain ⟨τ₀, hτ₀, hU⟩ := h2 hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD.toUNDens hT hC k
theorem un_bUniv_of_rows -> un_bUniv_of_rows': DIFFERS
    --- 
    +++ 
    @@ -14 +14,2 @@
    -    (fun _ => msc) E (fun _ => rhoSC E) δ hDens hTr (rN d hd 𝔠 𝔡 sz hA) hCl E hE2 k hk _ hO'
    +    (fun _ => msc) E (fun _ => rhoSC E) δ (unDens'_msc_of_unDens E _ δ hDens) hTr
    +    (rN d hd 𝔠 𝔡 sz hA) hCl E hE2 k hk _ hO'
non-identical: 2
```
Name-clash grep of the 34 new public names (8 defs, 15 theorems incl. `UNDens'.toUNDens`, 8 instances, `UNDensInst`, `refutedProps`, helper prefix `PinsDens_`) against `main` (`git grep -nF -e NAME main -- RBM3D RBM3D.lean`; not `-w`, primed names contain `'`):
```
$ ./clash.sh | awk '$1>0' | wc -l      -> 0       # 34 names checked, total hits 0
```
Ports: none (no RBM1D/RBM2D text copied; every source is a merged RBM3D file cited in the ticket); RBM1D/RBM2D diff-stat not applicable.

Narrative:
- New file `RBM3D/Universality/PinsDens.lean` (682 lines, namespace `RBM.Univ`, instances in `RBM.Univ.UNDensInst`); `RBM3D/Test/Axioms.lean` edited only as the ticket lists. No merged file was touched.
- Targets 1-5 and the eight instances compiled; the statements equal the check file up to defeq (31/31 `rfl`); the only binder difference is `Type` -> `Type*` in `unDens'_freeConvST`, which the ticket allows.
- Target 4: the datum `(unDensShift m h, rho + 1/(2 pi))`, `h n = N^(-2)`, meets the hypotheses of `UNStep1Good` by `unDens_shift` and `unTrLocal_shift` (`unTrLocalInit_shift` for the C form). The private helper `PinsDens_refute` (generic `tau_s`, `D = 1`, arbitrary regularity clauses) derives the contradiction; `not_UNStep1Good` and `not_UNStep1GoodC` instantiate it at `tau_s = min (c d) (1/2)` with `vOU` resp. `vOUC`.
- Helper `PinsDens_exists_not_mem`: two events of measure `<= x < 1/2` in a probability space miss a common point (`measure_union_le`, `measure_univ`). Helper `PinsDens_rho_eq`: the two limit densities of the same `v`, `t` agree (`isFreeConv32_unique`, `tendsto_nhds_unique`), so `1/(2 pi) <= 2 r`.
- The rate is eventual only: `tendsto_rpow_neg_atTop` composed with `SizeTendsto` gives `N^(-1) < 1/2` and `N^(-3 tau_s/8) < 1/(4 pi)` eventually; no concrete `n` is exhibited (the preflight computes `N > e^405` at `sz0`).
- `not_unDens'_unDensShift`: `eps' = min (h_n/2) (1/(4(Lp+Lp')))` at `z = E + i h_n`, `z' = E + i (h_n - eps')`, as in the ticket; `Lp`, `Lp'` are the box constants of the two `UNDens'` data.
- `un_msc_box_zero` uses `PinsDens_lip_one` (re-derived from public targets 1-2 of T2190, as the ticket asks: `FreeConvRegular_lip_one` is private) with `1/(2 (9/100)^2) = 61.73 <= 62`.
- Registry: four lines moved out of `owedProps`, four primed lines added, `UNDens'` added to `structuralProps`, new list `refutedProps` after `structuralProps`; `classified` in `#assert_rbm_axioms` and in `#assert_rbm_audit_detects` includes it; a disjointness check; the `refuted` count in the two report lines. The pre-check shows `refuted 4` found and the four primed names in the owed ledger; the negative test fires.
- `UNDens'`, `UNStep1Good'`, `UNStep1GoodC'` appear in the "carry nothing yet" list of the pre-check: `UNDens'` is concluded by `unDens'_msc_of_unDens` (as `UNDens` is by `un_dens_msc_zero`), and no theorem takes the two Step 1 pins as hypotheses yet (ledger counts 0).
- Differences from merged text beyond `UNDens -> UNDens'`: proofs only (`un_core_of_rows'` passes `hD.toUNDens`; `un_bUniv_of_rows'` converts `hDens` by `unDens'_msc_of_unDens`); all statements are identical (diff script above). No `(a')` section: no discrepancy with section (a) was met.
- Not targets (as in the ticket): refutations of `UNInfty1Row`, `UNCore`, `UNCoreC` (argued only); any proof of a primed owed pin; the rescaling of supervisor 2.2; `UNDensBARow'`; band bridges for `UNStep1GoodC'`/`UNCoreC'`.

## (c) Verified Mathlib names used (one line each; printed by a scratch `#oneline` command, exit 0, 0 errors)
- `MeasureTheory.measure_union_le : ∀ {α : Type u_1} [MeasureTheory.OuterMeasureClass F α] {μ : F} (s t : Set α), μ (s ∪ t) ≤ μ s + μ t`
- `MeasureTheory.IsProbabilityMeasure.measure_univ : ∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProb...`
- `MeasureTheory.measure_mono : ∀ {α : Type u_1} [MeasureTheory.OuterMeasureClass F α] {μ : F} {s t : Set α}, s ⊆ t → μ s ≤ μ t`
- `tendsto_nhds_unique : ∀ [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} [l.NeBot], Tendsto f l (𝓝 a) → Tendsto f l (𝓝 b) → a = b`
- `Filter.Eventually.exists : ∀ {α : Type u} {p : α → Prop} {f : Filter α} [f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x`
- `Filter.Eventually.and : ∀ {α : Type u} {p q : α → Prop} {f : Filter α}, Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x`
- `Filter.Tendsto.eventually : ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}, Tendsto f l₁ l₂ → (∀ᶠ (y : β)...`
- `Filter.Tendsto.congr' : ∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β}, f₁ =ᶠ[l₁] f₂ → Tendsto f₁ l₁ l₂ → Tendsto f₂...`
- `Filter.Tendsto.add_const : ∀ [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M} {x : Filter α} {a : M} (b : M), Tendsto f x (𝓝 a) → Tendsto (fun x...`
- `Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z`
- `Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1`
- `Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y`
- `Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y`
- `tendsto_rpow_neg_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ (-y)) atTop (𝓝 0)`
- `gt_mem_nhds : ∀ {α : Type u} [ts : TopologicalSpace α] [OrderTopology α] {a b : α}, b < a → ∀ᶠ (x : α) in 𝓝 b, x < a`
- `Real.exp_lt_one_iff : ∀ {x : ℝ}, Real.exp x < 1 ↔ x < 0`
- `ENNReal.ofReal_add : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q`
- `ENNReal.ofReal_one : ENNReal.ofReal 1 = 1`
- `ENNReal.ofReal_lt_ofReal_iff : ∀ {p q : ℝ}, 0 < q → (ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q)`
- `self_mem_nhdsWithin : ∀ {α : Type u_1} {a : α} {s : Set α}, s ∈ 𝓝[s] a`
- `Ioo_mem_nhdsGT : ∀ {α : Type u} [ClosedIciTopology α] {a b : α}, b < a → Set.Ioo b a ∈ 𝓝[>] b`
- `norm_sub_le : ∀ (a b : E), ‖a - b‖ ≤ ‖a‖ + ‖b‖`
- `norm_div : ∀ {α : Type u_1} (a b : α), ‖a / b‖ = ‖a‖ / ‖b‖`
- `Complex.norm_I : ‖Complex.I‖ = 1`
- `Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖`
- `Real.norm_eq_abs : ∀ (r : ℝ), ‖r‖ = |r|`
- `Complex.div_ofNat_im : ∀ (z : ℂ) (n : ℕ) , (z / OfNat.ofNat n).im = z.im / OfNat.ofNat n`
- `Nat.one_le_pow : ∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n`
- `le_div_iff₀ : ∀ {G₀ : Type u_3} [MulPosReflectLT G₀] {a b c : G₀}, 0 < c → (a ≤ b / c ↔ a * c ≤ b)`
- verified absent: `Real.exp_lt_one` (`Unknown constant`; `Real.exp_lt_one_iff` is used).
- deprecated in this Mathlib: `if_neg` (warning "Use `ite_eq_right` instead"; used in the first draft only, replaced by `simp [unDensShift, not_lt.mpr hz]`).

## (d) Open issues and paper-delta candidates
- **T2201a** (Lean structure, no paper statement changes; variant of T2190b): the abstract density hypothesis of the Lean core, `UNDens'`, is stronger than the paper's bulk conditions (Thm 2.7 `rho_N(E) >= kappa`, DECISIONS §51): it asks for box regularity of `m_n` as a complex function, uniform in `n`, because the paper's Step 1 argument is exact only for `msc`; the band data (`un_dens'_msc_zero`, `unDensBandRow'_of_row`) and the BA class (`unDens'_freeConvST`, `inst_dens'_uI`) meet it.
- **T2201b**: none (no statement of a primed pin or instance differs from its merged source beyond `UNDens -> UNDens'` etc.; two proofs differ as listed, statements identical).
- **T2201c** (registry): new class `refutedProps` (DECISIONS §66 (2)). The merged docstrings of `UNStep1Good` (`Pins.lean:583`), `UNInfty1Row` (`:730-731`), `UNStep1GoodC` (`PinsK.lean:274`), `UNCoreC` (`:290-291`) still say "owed" and are not edited (CLAUDE.md §5.3).
- Open: the refutations of `UNInfty1Row` and `UNCoreC` are argued (supervisor 2026-10-05-1651 1.3), not compiled; they are in `refutedProps` on that argument.
- Open: `not_UNStep1Good_band` has the owed pins `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow` (other gates) as hypotheses, and `UNStep1Good` as the hypothesis it refutes; every other hypothesis is discharged at `sz0`, `kappa = 1`, `E = 0`, `delta = 1/2`.
- **Merge note for the hub (§20 (3))**: root import `import RBM3D.Universality.PinsDens` after the last `import` line of `RBM3D.lean`; if `Test/Axioms.lean` conflicts only in the lists, take the union except that `UNStep1Good`, `UNInfty1Row`, `UNStep1GoodC`, `UNCoreC` must not be in `owedProps` (the full build fails otherwise: the negative test shows the error line).

## Repair (audit round 1 RETURN) - Mon Oct  5 18:57:14 UTC 2026 (`date -u`), repairer claude-opus-5-5, commit `b818bb5`
Addresses `T2201-audit.md` §7 items 1-4 only; no statement, registry line or other file changed.
```
$ git diff --stat b33918f b818bb5
 RBM3D/Universality/PinsDens.lean | 20 ++++++++++++++++++++
$ grep -n "^example" RBM3D/Universality/PinsDens.lean      # namespace RBM.Univ.UNDensInst
680:example (hS : UNStep1GoodC)
688:example (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2)) :
694:example (rD : UNDensBandRow) :
$ lake build RBM3D.Universality.PinsDens        # only warnings: longLine in RBM3D/Defs/Tail.lean
✔ [3338/3338] Built RBM3D.Universality.PinsDens (4.2s)
Build completed successfully (3338 jobs).
$ lake env lean <scratchpad>/T2201/Ax.lean       # three #print axioms lines; exit 0
'RBM.Univ.not_UNStep1GoodC' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unTrLocalInit_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDensBandRow'_of_row' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Data: `sz0`, `(UNModel.band sz0).toC`, `msc`, `E = 0`, `δ = 1/2` (first two; the first also `ρ = rhoSC 0`,
`un_dens_msc_zero`); `κ = 1/10`, `E = 0` (third). Hypotheses kept: `UNStep1GoodC` (the premise refuted), and the other
gates' pins `UNTrLocalInit` at the data, `UNNormBandRow`, `UNDensBandRow`. Bodies as in the audit's §4; no new public name.
The three `example`s (lines 680, 688, 694) apply `not_UNStep1GoodC`, `unTrLocalInit_shift`, `unDensBandRow'_of_row`.
