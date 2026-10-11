Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 03:40:23 UTC 2026

Target 1 `baEKSumDecayNonzero_holds : BAEKSumDecayNonzero d n Λ κ` (`BA/EKPins.lean:134`): `∃ C>0` (fixed after `d,n,Λ,κ`, before `L g s t E m σ A 𝒜`) with `‖Q^(A) U^(n)_{s,t,σ} 𝒜‖_∞ ≤ C‖𝒜‖_∞` for `1-g²/L² ≤ s ≤ t < 1`, `0 ≤ s`, `BAReal d L g κ E m`, `A ⊇ I_diff(σ)`. Targets 2-4 (C1, instances, registry) are not statements; they are covered in (i)-(ii).

### (i) Exponent table and band-to-BA replacement (all file:line from the tree at `3e72137`)

| step of the band proof | band object (`Evolution/Nonzero.lean`) | BA replacement (merged name, file:line) |
|---|---|---|
| tensor form `Q^(A)U = ⊗_i (Proj^{[i∈A]} · uKer_i)` (`:158-186`) | `UN_eq_tensorKer`, `zeroModeSet_tensorKer`, `norm_tensorKer_le` (`Kernel/Evolution.lean:210, 298, 420`) | `BAUN` (`EKPins:53`) is `tensorKer d L (fun i => BAuKer … (σ i) (σ (finRotate n i)))` by `rfl` (same sum); `zeroModeSet_tensorKer` and `norm_tensorKer_le` are model-free (no `‖m‖=1`), reused as is |
| `i ∉ A ⇒ σ_i = σ_{i+1}`, factor `≤ Cs` (`:158-173`) | `ekSameRow_holds` (EK-2) | `baEKSameRow_holds` (`EKPins:568`): `‖BAuKer … σ σ‖ ≤ Cs`, `Cs = 1 + Cκ(1+Λ² expC k cκ)`; `hcyc` step vanishes (`BAuKer` takes `σ i, σ (finRotate n i)` directly) |
| `uKer = 1 + (t-s)μ SΘ` (`:112-118`) | `uKer_eq_one_add` | `BAuKer_eq_one_add_Xi` (`EKPins:72`) / `BAuKer_eq_one_add` (`:62`), needs `BAReal`, `0 ≤ t < 1` |
| `Proj S = S Proj` (`:112-118`) | `projMat_mul_SB_comm` (`Kernel/Evolution.lean:359`, `S^(B)` has unit row/col sums) | no BA lemma exists (grep: none). New: `Proj T = T Proj` for any translation-invariant `T` (`Σ_b T(0,b)` = row sum = col sum, so `JT = TJ`). Shift of `BAMss`: `baP8_BAMss_shift` is `private` (`Prop6Path:483`), so re-derive from `BAMB_shift` (`BA/Ward.lean:53`, used at `KKernel:68`) |
| `Proj Θ = Θ̊` (`:112-118`) | `projMat_mul_Theta` (`Kernel/Evolution.lean:373`, uses `sum_Theta_row`, symmetry) | no BA lemma. New: for translation-invariant `Θ` (`baP8_BATheta_shift`, `Prop6Path:497`, public) `Proj Θ = Θ - L^{-d}JΘ`, `JΘ = c J` with `c` the column sum, and `BATheta0 = Θ - L^{-2d} Σ_a Σ_b Θ` has `L^{-2d}·L^d c = L^{-d} c`: equal. Needs no stochasticity, so no case split on `σ₁=σ₂`. Numerics below: both `(+,-)` and `(+,+)` |
| `‖Θ̊‖ ≤ Σ_b |Θ̊(0,b)|` (`:74-80`) | `norm_le_sum_row_zero` (`Kernel/Evolution.lean:307`) | same lemma, shift-invariance of `BATheta0` from `baP8_BATheta_shift` (the double sum is shift-free) |
| pin 8 `Prop8ZeroMode` at `μ = m_σ m_σ'`, `‖m‖=1`, `PropSpin` (`:54-60, 74`) | `h8 : Prop8ZeroMode` with `‖Theta0 … (tμ)‖ ≤ C₀ (g²+|1-t|)⁻¹ (|b|+1)^{-(k)}` | `baProp8_holds` (`Prop6Path:1009`, `BAProp8`, `FlowPins:217`): `‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C₀ (g²+|1-t|)⁻¹ ((|a|+1)^{d-2})⁻¹` for ALL `σ₁ σ₂ : Bool`, `BAReal`, `0 ≤ t < 1`; `PropSpin`, `μ`, `‖m‖=1` do not occur |
| radial sum (`:81-92`) | `sum_radial_pow_le` (`Defs/RadialSum.lean:192`), `radC_pos` (`:99`) | same, model-free: `Σ_b ((|b|+1)^k)⁻¹ ≤ E_k L²`, `k = d-2`, `E_k = exp √(k+2) · 2^{k+2} · radC 1` (private `ekE` is re-defined as `EKNonzero_E`) |
| `‖S‖ = 1` (`norm_SB`, `:123`) | `norm_SB` | `‖M^{(σσ')}‖_{∞→∞} ≤ 1` for every `σσ'`: `‖M_ab‖ = BAK_ab` (`BAMss_norm_eq_BAK`, `KKernel:102`), `Σ_b BAK_ab = 1` (`BAK_row_sum`, `:124`, needs `hr.1 : BASelf`); `norm_le_sum_row` style bound |
| `‖Proj‖ ≤ 2` | `norm_projMat_le` (`Kernel/Evolution.lean:331`) | same, model-free |
| `(1-s)L² ≤ g²` (`:96-110`) | arithmetic | same arithmetic, `g>0`, from `1-g²/L² ≤ s` |

Constants and constraints (`k = d-2 ≥ 1`):

| quantity | value | constraint | slack |
|---|---|---|---|
| `Cs` (same-row, `baEKSameRow_holds`) | `1 + Cκ(1 + Λ² expC k cκ)`, `Cκ,cκ` from `baProp5s_holds (d,Λ,κ)` | `> 0`; depends on `(d,Λ,κ)` | `Cκ>0, expC ≥ 0` give `Cs ≥ 1` |
| `C₀` (pin 8, `baProp8_holds`) | `max Cm (Cs(Λ²+1)+ …)` from `(d,Λ,κ)` (`Prop6Path:1015-1017`) | `> 0` | `lt_max_of_lt_left hCm` |
| `E_k` | `exp √(k+2) · 2^{k+2} · radC 1`, `radC 1 = 32(1+720)=23072` | `> 0`; needs `1 ≤ L` (`L ≥ 3`) | `k=1`: `E_1 = 1043266.68` (script below) |
| radial exponent | decay `(|b|+1)^{-(d-2)}` summed over `Z_L^d`, `d-2 = k` | `Σ_b (|b|+1)^{-k} ≲ L^{2}` exactly the `k+2 = d` case of `sum_radial_pow_le` | exponent `2` equals the loss `L²` to be cancelled: slack 0, the same-exponent cancellation is the whole point |
| `(1-s)L² ≤ g²` | from `1-g²/L² ≤ s` | `g>0` | equality at `s = 1-g²/L²`: slack 0 (needed sharp) |
| `(t-s)(g²+|1-t|)⁻¹ L² ≤ 1` | `t-s ≤ 1-s`, `(g²+|1-t|)⁻¹ ≤ g⁻²` | `≤ 1` | sup over window `= 1` (`t→1`); at the instance below `0.4848`, slack `0.5152` |
| `Ci = max Cs (2 + C₀E_k)` | one-index bound: `i∉A: ≤ Cs`; `i∈A: ‖Proj‖ + (t-s)‖M‖‖Θ̊‖ ≤ 2 + C₀E_k` | `Ci > 0` | `Ci ≥ 2 + C₀E_k > 2` |
| `C` of the pin | `Ci^n` (`n ≥ 2`) | depends on `(d,n,Λ,κ)` only; `∏_i ≤ Ci^n` | none needed |
| C1 | only `BAReal` (`BASelf ∧ κ ≤ Im m`), `0<g≤Λ`, `L≥3`; no `‖m‖=1`, scalar `μ`, `M = mI`, smallness of `g` or `‖M-m₀I‖` | `Λ` enters only via `Cs, C₀` | `Im m ≥ κ` is carried inside `Cs, C₀` (`baProp5s`, `baProp8`) |

`Ci = max Cs (2 + C₀E_k)`: `i ∈ A` is bounded by the Proj+Θ̊ split for all `σ`, `i ∉ A` by `Cs`.

Verdict on the proof route: complete and uniform. The paper step `(eq:diffcolor)` (`A:216-218`) is applied to every `i ∈ A`, including `σ_i = σ_{i+1}` (A may contain same-sign indices); the BA lemma `Proj Θ = Θ̊` holds for any translation-invariant `Θ`, so no stochastic-row hypothesis is lost.

### (ii) Nondegenerate instance (flow datum `n = 0` of `sz0`, `EKPins:638-852`)

Data: `d=3, n=2, Λ=1, κ=1/2, L=4` (`sz0.L 0 = 4`, `Defs/Sizes.lean:261, 267`), `g=g_I=√t₀·λ ≤ 1/64` (`gI_le`, `EKPins`), `E=E_I`, `m=m_I` with `BAReal 3 4 g_I (1/2) E_I m_I` (Lean: `hrI`, `BAflow_real`, `flow_sz0`), `s = 1-g²/L²`, `t = 1-g²/(2L²)` (`0 ≤ s ≤ t < 1`, `1-g²/L² ≤ s`), `σ=(+,-)`, `A = {0,1} ⊇ I_diff`, `𝒜=δ_0`. Second: `n=3, σ=(+,+,-)`, `I_diff = {1,2}`, `A = {1,2}` (index `0` has `σ_0=σ_1`, so the same-row branch is used), `𝒜=δ_0`, same other data. Independent numerical check of every hypothesis (rebuilds `Ψ^{(B)}` on `Z_4^3`, solves `(self_m)` at `g_I`, forms `M`, `Θ`, `U`, and applies `Q^(A)` to `δ_0`; `‖Q^(A)Uδ_0‖_∞` is the quantity the pin bounds):

```
$ python3 <scratchpad>/T2406/inst.py
L,d,N 4 3 64 lam 0.015625 Im mS 0.8324879132742102 t0 0.6937399277285086 gI 0.013014226813110832 gI<=1/64 True
EI 0.0 mI 0.9994926192469116j self residual 1.1102230246251565e-16 Im mI>=1/2 True
Ward row sums of |M|^2 in [min,max]: 0.9999999999999989 1.0000000000000013 symm 1.0408340855860843e-17
window: g^2/L^2 1.0585631221443309e-05 s 0.9999894143687785 t 0.9999947071843893 0<=s<=t<1 True
sig (1, 0) ||U|| 2.0 ||Proj U|| 1.981 ||M|| 1.0
sig (0, 1) ||U|| 2.0 ||Proj U|| 1.981 ||M|| 1.0
sig (1, 1) ||U|| 1.0 ||Proj U|| 1.9687 ||M|| 1.0
sig (0, 0) ||U|| 1.0 ||Proj U|| 1.9687 ||M|| 1.0
Proj Theta = Theta0: 6.09894357239682e-09
Proj M = M Proj (+-): 3.8163916471489756e-17
inst1 n=2 sig=(+,-) A={0,1}: ||Q U delta0||_inf = 0.9810882115342677 ||delta0||=1
inst2 n=3 sig=(+,+,-) A={1,2}: ||Q U delta0||_inf = 0.9810856164856917 ||delta0||=1
I_diff(sig) = [1, 2]
sig (1, 0) max|Proj Theta - Theta0| = 6.09894357239682e-09  row-sum range of M^{ss'}: 1.0 1.0
sig (1, 1) max|Proj Theta - Theta0| = 4.440892098500626e-16  row-sum range of M^{ss'}: 0.997974 0.997974
```
(`E_I = 0.0` by the symmetry of the spectrum of `Ψ^{(B)}` on the even torus at `w = 6i/5`; `Im m_I = 0.9995 ≥ 1/2`, Ward row sums `Σ_b|M_ab|² = 1` to `1e-15`.) Lean's `inst_BAEKSumDecayNonzero` (`EKPins:758`) already fixes the same data with the pin as hypothesis; E3 turns it into a direct instance, plus the `n=3` one.

Constant numerics for the table (`k = 1`, `g = g_I`, `L = 4`, window of the instance):
```
$ python3 <scratchpad>/T2406/const.py
radC(1)= 23072.0 ekE(k=1)= 1043266.6826185165
(1-s)L^2 = 0.0001693700995435421  g^2 = 0.00016937009954309294  slack g^2-(1-s)L^2 = -4.4915785500643235e-16
(t-s)(g^2+|1-t|)^-1 L^2 = 0.48484848485497084  slack to 1: 0.5151515151450292
sup over window (t=1-,s=1-g^2/L^2): 1.0
```
(the `-4.5e-16` is floating rounding of the exact identity `(1-s)L² = g²`.)

External hypotheses: none. The pin takes no external input here: `baProp5s_holds`, `baProp8_holds`, `baEKSameRow_holds` are merged theorems (axioms checked by their own tickets); `BAEKSumDecayNonzero` is proved from them, so no limit computation (TEAM §8 lesson 14) applies.

Name check (script output): `git grep -n "baEKSumDecayNonzero_holds\|EKNonzero_" main -- RBM3D` printed nothing.

Plan against stop line 800 (`wc -l RBM3D/BA/EKNonzero.lean`), by block: header and imports (`BA.EKPins`; it imports `Prop6Path`, `KBase`, `KKernel`) 15; `EKNonzero_E`, positivity 15; `BAMss` and `BATheta` shift, `Proj T = T Proj`, `Proj Θ = Θ̊` (translation-invariant, generic matrix lemmas) 70; `‖M^{(σσ')}‖ ≤ 1` 20; one-index bound `‖Proj·BAuKer‖ ≤ 2 + C₀E_k` (band `ek_norm_projMat_mul_uKer_le`, 70 lines, ported with `BAProp8`) 80; `(1-s)L²≤g²` arithmetic 25; main theorem (band `:150-189`) 55; instances 100; total about 380 lines (estimate 350 within the ticket's 250/350/550; far below 800). Registry edit: delete line `:196`, relabel comments at `:133-135` (3 comments, text in the ticket).

### Verdicts
- Target 1 `baEKSumDecayNonzero_holds`: PASS (all steps have a merged BA replacement; the two missing generic matrix lemmas `Proj T = T Proj` and `Proj Θ = Θ̊` for translation-invariant `T`, `Θ` are elementary and provable in the new file; no step uses `‖m‖=1`, `PropSpin`, `μ`, or smallness).
- Target 2 (C1): PASS (table, last row).
- Target 3 (nonempty instances, `n=2` and `n=3` with proper `A`): PASS (numbers above; Lean side `hrI`, `gI_le`, `gI_pos`, `LI_real` already merged).
- Target 4 (registry): PASS (lines `:133-135`, `:196` read from `RBM3D/Test/Axioms.lean`; pure deletion plus comments).

## (b) Script output (stage 1b, `prover-hard`; commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2406`, branch `t/T2406`)
Section (a) was not edited; no `(a′)` section was written. Line count against the stop line: 357 of 800 (first command).
```
$ date -u; git log --oneline -1; wc -l RBM3D/BA/EKNonzero.lean   # stop line 800
Sun Oct 11 03:50:48 UTC 2026
6dfc2c9 T2406: BA-E3 baEKSumDecayNonzero_holds (lem:sum_decay_nonzero at BA), registry relabel
     357 RBM3D/BA/EKNonzero.lean
$ lake build RBM3D.BA.EKNonzero 2>&1 | tail -1; grep 'axiom audit:\|Build completed\|^exit' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2406/fullbuild.log | cut -c1-130   # full lake build (registry scan inside)
Build completed successfully (3758 jobs).
info: RBM3D.lean:445:0: axiom audit: 11344 theorems, 3414 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded
Build completed successfully (4213 jobs).
exit 0
$ git diff --stat main...t/T2406
 RBM3D.lean              |   1 +
 RBM3D/BA/EKNonzero.lean | 357 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   7 +-
 3 files changed, 361 insertions(+), 4 deletions(-)
$ echo "check file exit $(lake env lean docs/tickets/checks/T2406-check.lean >/dev/null 2>&1; echo $?); sorry/admit/native_decide/axiom lines: $(grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/BA/EKNonzero.lean); name-clash matches on main: $(git grep -n 'baEKSumDecayNonzero_holds\|EKNonzero_\|EKNonzeroInst' main -- RBM3D | wc -l | tr -d ' ')"
check file exit 0; sorry/admit/native_decide/axiom lines: 0; name-clash matches on main: 0
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2406/ax.lean | sed 's/ depends on axioms//'
'RBM.BA.baEKSumDecayNonzero_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.EKNonzeroInst.inst_baEKSumDecayNonzero_n2': [propext, Classical.choice, Quot.sound]
'RBM.BA.EKNonzeroInst.inst_baEKSumDecayNonzero_n3': [propext, Classical.choice, Quot.sound]
$ git grep -n 'PropSpin\|‖m‖ = 1\|Prop8ZeroMode\|SB d L\|cycProd\|EKsgn' t/T2406 -- RBM3D/BA/EKNonzero.lean | cut -c1-60   # C1: docstring line only
t/T2406:RBM3D/BA/EKNonzero.lean:20:`norm_zeroModeSet_UN_le`,
$ git diff main...t/T2406 -- RBM3D/Test/Axioms.lean | grep '^[-+] ' | sed -E 's/^([-+]) +`RBM.BA.([A-Za-z]+),.*(owner.*|owed.*)$/\1 \2 ... \3/' | cut -c1-200
- STLmaxgL ... owed like its band form `STLmax`: BA chain, BA-V2/BA-K4 (T2197)
- STKboundgL ... owed: the BA chain, BA-K4/BA-V2
- STLKgL ... owed like its band form `STLK`: BA chain, BA-V2/BA-K4
+ STLmaxgL ... owner BA-V (main induction); at BA it follows from `STLKgL` by `BALmaxFromLK_holds` once `STKboundgL` is supplied (K12) (T2197)
+ STKboundgL ... owner: BA: proved at `baFMz` by `baKbound_holds` (K12); generic premise of `stBaseG_of_init`, `BALmaxFromLK`, `BAStep1`, `BABootstrap'`; discharged at BA by BA-V (instances: G7)
+ STLKgL ... owner BA-V (main induction)
- BAEKSumDecayNonzero ... owner BA-E3)
$ grep -n -A1 '^theorem baEKSumDecayNonzero_holds' RBM3D/BA/EKNonzero.lean
261:theorem baEKSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecayNonzero d n Λ κ := by
262-  intro hd _hn hΛ hκ
$ awk '/^theorem inst_baEKSumDecayNonzero_n[23]/,/:= by$/' RBM3D/BA/EKNonzero.lean
theorem inst_baEKSumDecayNonzero_n2 : ∃ C : ℝ, 0 < C ∧ AI 0 = 1 ∧
    ‖zeroModeSet 3 (sz0.L 0) ({0, 1} : Finset (Fin 2)) (BAUN 3 (sz0.L 0) gI EI mI ![true, false]
      (1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) (1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2)) AI)‖
        ≤ C * ‖AI‖ := by
theorem inst_baEKSumDecayNonzero_n3 : ∃ C : ℝ, 0 < C ∧ AI3 0 = 1 ∧ (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) ∧
    ‖zeroModeSet 3 (sz0.L 0) ({1, 2} : Finset (Fin 3)) (BAUN 3 (sz0.L 0) gI EI mI ![true, true, false]
      (1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) (1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2)) AI3)‖
        ≤ C * ‖AI3‖ := by
$ grep -rn 'theorem baKbound_holds\|theorem BALmaxFromLK_holds\|theorem stBaseG_of_init' RBM3D | cut -c1-70
RBM3D/BA/KBound.lean:245:theorem baKbound_holds (d : ℕ) : BAKbound d :
RBM3D/BA/Step1Fam.lean:665:theorem BALmaxFromLK_holds (d : ℕ) : BALmax
RBM3D/Induction/MainIndBase.lean:110:theorem stBaseG_of_init {law : ∀ 
```
Narrative.
- One commit `6dfc2c9` on `t/T2406`, three files (diff-stat above): the new `BA/EKNonzero.lean`, one import line in `RBM3D.lean` (after the last `import`), and the registry edit (the `owedProps` line of `BAEKSumDecayNonzero` deleted; the owner comments of `STLmaxgL`, `STKboundgL`, `STLKgL` relabelled as in the ticket, lists otherwise unchanged; the names cited in the new comments exist, last command).
- Port source: the RBM3D band proof `Evolution/Nonzero.lean:32-185` (last commit `c163ca8`); `projMat_mul_SB_comm`, `projMat_mul_Theta` (`Kernel/Evolution.lean:359, 373`, last commit `ff8d36d`) were the models of the two new matrix lemmas. No RBM1D/RBM2D text was used, so there is no RBM1D/RBM2D diff-stat.
- Section 1 (generic, no BA lemma existed): for a translation-invariant `T` all row sums and column sums equal `Σ_c T 0 c`, hence `Proj T = T Proj`; and `Proj Θ = Θ̊` from the public `baP8_BATheta_shift` (`Prop6Path:497`) alone, with no stochasticity and no case split on `σ₁ = σ₂`. `baP8_BAMss_shift` (`Prop6Path:483`) and `EKPins_norm_Q_le` (`EKPins:151`) are private upstream, so `EKNonzero_Mss_shift` and `EKNonzero_norm_Q_le` are private re-derivations (from `BAMB_shift`; from `BAMss_norm_eq_BAK`, `BAK_row_sum`).
- Section 2 (`EKNonzero_norm_projMat_mul_uKer_le`, any `(σ₁, σ₂)`): `Proj (1 - s M) Θ_t = Proj + (t - s) M Θ̊_t` (`BAuKer_eq_one_add`), `‖Proj‖ ≤ 2`, `‖M‖ ≤ 1`, the `BAProp8` row bound with `sum_radial_pow_le`, and `(t - s)(g² + |1 - t|)⁻¹ L² ≤ 1` from `1 - g²/L² ≤ s` (`EKNonzero_coef`).
- Section 3: `Ci = max Cs (2 + C₀ E_k)`, `C = Ci ^ n`; `Cs` from `baEKSameRow_holds` and `C₀` from `baProp8_holds` are obtained before `intro L hL g ...`, so `C` depends on `(d, n, Λ, κ)` only. `i ∈ A`: section 2; `i ∉ A`: `σ i = σ (finRotate n i)` and `baEKSameRow_holds`; product by `zeroModeSet_tensorKer`, `norm_tensorKer_le`; `BAUN` is `tensorKer` of the `BAuKer` family by `rfl`. C1: the band objects of the grep above (`PropSpin`, `‖m‖ = 1`, `Prop8ZeroMode`, `SB d L`, `cycProd`, `EKsgn`) occur only in the module docstring; the hypotheses used are `BAReal`, `0 < g ≤ Λ`, `3 ≤ L`.
- Section 4 instances take no pin as hypothesis: `d = 3`, flow datum `n = 0` of `sz0` (`L = 4`, `gI`, `hrI`), `s = 1 - g²/L²`, `t = 1 - g²/(2L²)`, `𝒜 = δ₀` (`AI 0 = 1`, `AI3 0 = 1` in the conclusions); `n = 2`, `σ = (+,-)`, `A = {0, 1}`; `n = 3`, `σ = (+,+,-)`, `A = {1, 2}` with `0 ∉ A` in the conclusion (same-row branch at index `0`). The conditional `inst_BAEKSumDecayNonzero` of `BA/EKPins.lean` is unchanged.

## (c) Verified Mathlib names (all 28 `#check` lines elaborate, exit 0, `T2406/names.lean`); verified absent: none checked
`Fintype.sum_equiv`, `Equiv.subRight`, `Equiv.neg`, `Matrix.sub_mul`, `Matrix.mul_sub`, `Matrix.one_mul`, `Matrix.mul_one`, `Matrix.sub_apply`, `Matrix.mul_apply`, `Matrix.mul_add`, `Matrix.mul_smul`, `Matrix.mul_assoc`, `Matrix.linfty_opNNNorm_def`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.prod_le_prod₀`, `Finset.prod_const`, `Fintype.card_fin`, `inv_anti₀`, `le_div_iff₀`, `div_le_one`, `norm_smul_le`, `norm_mul_le`, `norm_add_le`, `Complex.norm_real`, `Real.norm_of_nonneg`, `Complex.ofReal_sub`, `Nat.one_le_of_lt`.

## (d) Open issues and paper-delta candidates
- No paper-delta candidate: the target is the T2388 pin (`BA/EKPins.lean:134`, absent from the diff-stat) and the theorem concludes it by name. Observation: the proof uses `3 ≤ d`, `0 < Λ`, `0 < κ` of the pin; `2 ≤ n` is not used (`_hn`), as in the band proof (`Evolution/Nonzero.lean:147`).
- C4: only the pin `BAEKSumDecayNonzero` is proved; open: the BA forms of `STEK*` at scale `N` (U3-BA, after U3s1 merges). Cleanup candidate: `EKNonzero_Mss_shift`, `EKNonzero_norm_Q_le` duplicate private lemmas of `BA/EKPins.lean`, `BA/Prop6Path.lean`.
