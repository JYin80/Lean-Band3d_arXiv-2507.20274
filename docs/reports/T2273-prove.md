Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 08:48:48 UTC 2026

Setting: `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/2`, `nf = 2`, `τ = τ_U = 10⁻⁴`; `c := 2𝔠𝔡 = 1/30` (RBM2D `Jak_fixed_time` parameter, c9a24cf `Jak.lean:553-831`); `N = (WL)^d`.
Scripts (no Lean): `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2273/pre.py`, `.../tok.py` (stdlib Python, exact `Fraction`, float log10).

### (i) Exponent table (values at the setting; slack = exact or numeric from `pre.py` below)

| quantity | value | constraint | slack |
|---|---|---|---|
| `c = 2𝔠𝔡` | `1/30` | `0 < c < 36` (`Jak_alpha1_le hc2`); `𝔠𝔡 ≤ 1/2` (`un_cd_le_half`) | `𝔠𝔡 = 1/60` vs `1/2` |
| `un_cd_le_half` | `𝔠 < 1/d`, `𝔡 ≤ d/2` ⇒ `𝔠𝔡 < 1/2` | (1) `N^𝔠 ≤ W`, `W^d < N` (`L ≥ 3`, `W ≥ 1`), `N > 1` ⇒ `N^{𝔠d} ≤ W^d < N` ⇒ `𝔠d < 1`; (2) `𝔡 > d/2` would give `W^{𝔡-d/2} → ∞` (`W ≥ N^𝔠 → ∞`) against `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` eventually | sz0: `𝔠d = 1/2 < 1`, `𝔡 = 1/10 ≤ 3/2` |
| window `w'` | `N^{-1+𝔠𝔡/3}/2`, `𝔠𝔡/3 = 1/180` | `w' + C₀/N ≤ N⁻¹W^{𝔡/3}`: `2C₀ ≤ N^{𝔠𝔡/3}` (eventual), `N^{𝔠𝔡/3} ≤ W^{𝔡/3}` (`Bandwidth`); `w' ≤ κ/4` (`ev4`) | holds exactly eventually; `ev2` needs `log10 N ≥ 54.19` at `C₀ = 1` |
| `θ` (good-event threshold) | `N^{-𝔠𝔡/18} = N^{-c/36}`, `1/1080` | off `B`: `‖blockM‖ < W^{-𝔡/6} ≤ N^{-𝔠𝔡/6} ≤ θ` (`un_W_neg_le`, `N ≥ 1`) | `𝔠𝔡/6 − 𝔠𝔡/18 = 1/540` |
| block threshold | `W^{-𝔡/6}`, `N^{-𝔠𝔡/6}`, `1/360` | fixed by merged `measure_bad_le_of_queBadMat` | — |
| QUE params | `ε₀ = 𝔡/3`, `c_Q = 𝔡/6` | `0 < ε₀ < 𝔡/2`, `0 < c_Q < ε₀ ∧ 𝔡/5` | `c_Q` vs `𝔡/5`: `1/300`; vs `ε₀`: `1/60` |
| `τQ` | `𝔡/30` | `> 0` (UNOUQUE is for every `τQ > 0`) | — |
| `queBound` exponent | `-min(2ε₀,2𝔡/5)+2c_Q+τQ = -𝔡/30` | `= -𝔡/15 + τQ` | printed: `-1/300` |
| `ℙ(B_y)` | `≤ (2d+1)W^{-𝔡/30} ≤ (2d+1)N^{-𝔠𝔡/30}`, `𝔠𝔡/30 = 1/1800` | `un_W_neg_le` at `x = 𝔡/30` | — |
| `c'` (pin exponent) | `𝔠𝔡/30 = 1/1800` | `= min(𝔠𝔡/6, 𝔠(𝔡/15−τQ))`; `< 𝔠𝔡/18 < 𝔠𝔡/6 < 𝔠𝔡/3`; `< 1` (crude lemma) | binding term: `ℙ(B)` (`𝔠𝔡/18 − 𝔠𝔡/30 = 1/2700`) |
| `δ` | `τ/(nf+5) = 1.43e-5` | `(m+3)δ ≤ τ`, `m ≥ |s|` | `τ − (nf+3)δ = 2.86e-5` |
| `D` (UNOUDiag exponent) | `(1+τ)(nf+3)+3 = 8.0005` | `(1+τ)(m+3)+3 ≤ D` (crude) | equality at `m = nf` |
| `η̃` | `N^{-1+2τ}` | `τ ≤ 1/4` ⇒ `η̃ → 0` (`ev3`) | `1 − 2τ = 0.9998` |
| `C` | `3nf+16 = 22` | `T = 1−c'+(3|s|+16)τ`, `|s| ≤ nf` | `T−6τ−good ≥ 5.99e-4`, `T−6τ−bad ≥ 2.86e-5` (sc = nf, worst) |
| `τ₀` | `min τ₁ (1/4)` | `UNOUClaims` gives `τ₁ > 0`; `τ_U ≤ 1/4` | — |
| `α₁` exponent | `2 − 𝔠𝔡/18 + 4τ + 2δ` (`1.999503`) | three terms `θ`-term, window `4/w'`, window `4η̃/w'²`, dyadic tail all `≤` it | all three True (printed) |
| `ev5` constant | `3(C₁+4(2d+1))C₂ ≤ N^{6τ}`; `C₁ = 193+128/κ² = 705`, `4(2d+1) = 28`, `C₂ = 6+16/τ+8/κ = 160022` | RBM2D `h5` with `20` replaced by `4(2d+1)` (`d` fixed before `n`) | threshold `log10 N ≥ 14244` (eventual, binding) |

Good part exponent: `a+b+e−1 = 1 − 𝔠𝔡/18 + (3sc+7)τ + (sc+3)δ ≤ T − 6τ = 1 − 𝔠𝔡/30 + (3sc+10)τ` (uses `𝔠𝔡/18 ≥ 𝔠𝔡/30` and `(sc+3)δ ≤ τ`). Bad part: `a+b+f+g−1 = 1 − 𝔠𝔡/30 + (3sc+9)τ + (sc+3)δ ≤ T − 6τ`. Crude part: `4(3+m)N⁻¹ ≤ 1/3 ≤ N^T` (`T ≥ 1 − 1/60 > 0`, `ev1`: `N ≥ 12(3+nf)`).
Window (R1, R3): `|λ_α − E| ≤ w' + C₀/N ≤ N⁻¹N^{𝔠𝔡/3} ≤ N⁻¹W^{𝔡/3}` — the window of `UNBadY`/`measure_bad_le_of_queBadMat`; `un_window_sub` needs `1 ≤ W`, `W^{-d/2+𝔡} ≤ lam` (`WO`).

Consumer token check (script `tok.py`; `Pins.lean:806-809`, check file `def T2273_jakRow`):
```
$ python3 .../T2273/tok.py
pin  : UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
check: UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
hypotheses/quantifiers identical: True
pin conjunct 1 present: True ; UNClaimRow UNJak token present: True
```
Integrand: `UNJak` (`Pins.lean:700-704`) `‖∑ x, (Gres H z_i b₁ * Gres H z_i b₁) x x * scirc d L W lam x y * Gres H z_i b₂ y y‖`, weight `∏_{j∈s}(stieltjesN H (z j)).im`, equals the left side of `jak_pointwise_good/_crude` (`JakKernel.lean:874-876, 937-939`) at `H = ouMat (UNModel.band sz) n t ω`, `lam = sz.lam n`, `u = z i`, `w = z`, `σ = b`. `jak_pointwise_good` takes `hα₁` (`:866-869`), `hα₂` (`:870-871`), `hQb` (`:872`) in the same shapes as RBM2D, with `N = ((W*L)^d : ℕ)` and `Cb = N^δ`.
Bad block: `measure_bad_le_of_queBadMat` (`JakSpectral.lean:559`) at `P = ouP`, `Hr = ouMat … t`, `p = queBound W 𝔡 (𝔡/3) (𝔡/6) (𝔡/30)`: `hp` is `UNOUQUE sz 𝔡 τU` at `(κ, 𝔡/30)`, energy `E`, `t ≤ ouTStar` (same set `queBadMat … (𝔡/3) (𝔡/6) E b`); conclusion `≤ ((2d+1 : ℕ)) * p`; `toReal`: `≤ (2d+1)W^{-𝔡/30} ≤ (2d+1)N^{-𝔠𝔡/30}`. Grid: `UNOUDiag` at `(κ/2, δ, D)`; grid energies `|e| < 2 − κ/2` (RBM2D `Jak_grid_energy_lt` from `ev3`) ⊂ `|e| ≤ 2 − κ/2`. Total: good + bad `≤ ⅓ N^T` (script: ratio `0.005`), crude `≪ ⅓ N^T`; hence `≤ N^ε N^{1−c'+Cτ_U}` with `N^ε ≥ 1`.
Consumer remark (not a target): `UNJakUywRow` has one joint `C` for `UNJak ∧ UNUyw`; `jakRow` gives `C = 3nf+16`; UN-23 must take the max of two `C`s, using that `UNJak` is monotone in `C` (`N ≥ 1`, `τ_U > 0`).

### (ii) Concrete nondegenerate instance (sz0, `d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `Admissible (1/6) (1/10)`: `sz0_admissible`, `Sizes.lean:331`)
Data: `κ = 1/2`, `E = 1` (`|E| = 1 ≤ 3/2`), `nf = 2`, `τ_U = 10⁻⁴ ≤ 1/4`, `C₀ = 1`, `z_i = 1 + i N⁻¹` (window), `t = 0 ≤ t*`. Deterministic hypotheses at `n = 0` (`N = 2097152`), the eventual ones at their thresholds.
```
$ python3 .../T2273/pre.py
cd = 1/60 c=2cd = 1/30 cd<=1/2: True c<36: True
exps: cprime=cd/30= 1/1800  theta=cd/18= 1/1080  blockthr cd/6= 1/360  window w' cd/3= 1/180
order cd/30<cd/18<cd/6<cd/3: True ; cprime<1: True
QUE: eps0=dd/3 in (0,dd/2): True  c=dd/6<eps0,dd/5: True True  slack to dd/5: 1/300
queBound exp at tauQ=dd/30: -1/300 = -dd/30: -1/300
delta= 1.4285714285714285e-05  (nf+3)delta<=tau: True slack 2.857142857142857e-05  D= 8.0005
sc=0: T-6tau-good=6.275e-04  T-6tau-bad=5.714e-05 (both >=0: True)
sc=1: T-6tau-good=6.132e-04  T-6tau-bad=4.286e-05 (both >=0: True)
sc=2: T-6tau-good=5.989e-04  T-6tau-bad=2.857e-05 (both >=0: True)
crude: T(sc=0)= 1.0010444444444444 >=0
alpha1: E1=1.999503 ; term exps <= E1: [True, True, True]
C1= 705 4(2d+1)= 28 C2= 160022.0
log10 thresholds N: ev1 1.78 ev2 54.19 ev3 1.39 ev4 0.61 ev5 14244.0
binding: ev5, log10 N* = 14244.0
log10 target N^T (eps=0) = 14267.43
log10 good 14258.41 ; log10 bad 14265.13 ; log10 crude -14242.71
good<=T/3, bad<=T/3 (sum good+bad<=T/3 overall), crude<=T/3: True True True
log10(total/N^T)=-2.3020  (<0 means <1)  good+bad vs 1/3: 0.004988399431784919
n=0: 4 32 2097152 N^(1/6)=11.3137<=W W^(-d/2+dd)=0.007813 lam=0.015625 <=1/dd=10
W^d<N: True  c*d= 0.5  dd<=d/2: True
sz0: N_n>=N* once log10(n+1)>= 791.0
window n=0: |Re z-E|=0<=C0/N; N^(-1-tU)=4.761e-07<=Im z=4.768e-07<=N^(-1+tU)=4.775e-07 : True
t*=N^(-1+tU)=4.775e-07 >0 ; |E|=1<=2-kappa=1.5: True
w'+C0/N=7.353e-07 <= N^-1 W^(dd/3)=5.352e-07 : False ; 2C0<=N^(cd/3)? False (eventual)
n=1e0-ish: log10 W=1.5  log10[(2d+1)W^(-dd/30)]=0.840
n=1e1-ish: log10 W=6.7  log10[(2d+1)W^(-dd/30)]=0.823
n=1e3-ish: log10 W=16.5  log10[(2d+1)W^(-dd/30)]=0.790
n=1e30-ish: log10 W=151.5  log10[(2d+1)W^(-dd/30)]=0.340
n=1e260-ish: log10 W=1301.5  log10[(2d+1)W^(-dd/30)]=-3.493
```
Reading of the output (instance hypotheses, all of the target's deterministic ones are satisfied at one concrete point):
- `sz0` at `n = 0`: `N^{1/6} = 11.31 ≤ W = 32` (`Bandwidth`), `W^{-d/2+𝔡} = 0.0078 ≤ lam = 0.0156 ≤ 10 = 𝔡⁻¹` (`WO`), `W^d < N`, `L = 4 ≥ 3`, `W ≥ 1`; `𝔠d = 1/2 < 1`, `𝔡 = 1/10 ≤ 3/2` (`un_cd_le_half` premises and conclusion `𝔠𝔡 = 1/60 ≤ 1/2`).
- Window point `z = 1 + i/N`: `N^{-1-τ} ≤ Im z ≤ N^{-1+τ}`, `Re z = E`; `t* > 0`, so `t = 0 ∈ [0, t*]` (`inst_window`).
- The two lines `... : False` / `(eventual)` at `n = 0` are the eventual conditions `ev2`/window inclusion, NOT hypotheses of any target (`UNJak` is `∀ᶠ n`): `ev2` needs `log10 N ≥ 54.19`; the window inclusion then holds at every such `n` (`ev2` + `Bandwidth`). Binding eventual threshold `ev5`, `log10 N ≥ 14244` (`N_n` of `sz0` reaches it at `log10(n+1) ≥ 791`); RBM2D-type threshold (`T2162-prove.md:49`: `10^{1.412e5}` for its constants). No witness of any target is taken at this size: the examples apply the theorems to the `∀ᶠ`-statement.
- At `N* = 10^{14244}` (`ev1-ev5` all hold), the three parts of the majorant relative to `N^T` (`ε = 0`, `sc = nf`): good `10^{-9.02}`, bad `10^{-2.30}` (`good + bad = 0.005 ≤ 1/3`), crude `10^{-28510}`.

External hypotheses (TEAM §8 lesson 14): `UNOUQUE`, `UNOUDiag`, `UNLocAvgBand`, `UNOUClaims` stay hypotheses of `inst_row` (pins of other rows). Limit computations of the bounds they assert at `sz0`: `UNOUDiag` bound `N^{-D} → 0` (`D = 8.0005`, `N_n → ∞`; `sz0_tendsto`); `UNOUQUE` bound `W^{-𝔡/15+τQ} = W^{-1/300}` at `τQ = 𝔡/30`, `W_n = (2(n+1))^5 → ∞`, so `→ 0` (printed: `(2d+1)W^{-𝔡/30} = 10^{0.340}` at `n ~ 10^30`, `10^{-3.493}` at `n ~ 10^260`, i.e. non-trivial only for `log10 W > 253`: an eventual statement, consistent with the `∀ᶠ n`). The constraints on `(ε₀, c_Q) = (𝔡/3, 𝔡/6)` (`0 < c_Q < ε₀`, `c_Q < 𝔡/5`, `ε₀ < 𝔡/2`) hold with slacks `1/60`, `1/300`, `1/60` (printed).

### Verdicts
- `un_cd_le_half`: PASS (both limit arguments above; needs `1 ≤ d` for `𝔠 < 1/d` and `W^d < N` from `L ≥ 3`).
- `unJak_of_ouClaims`: PASS (exponents close at `c = 2𝔠𝔡`: good `𝔠𝔡/18`, bad `𝔠𝔡/30`, crude `N⁻¹`; `C = 3nf+16`; only constant change vs RBM2D is `20 → 4(2d+1)` in `ev5`; binding term `ℙ(B)`).
- `jakRow`: PASS (token-identical to the first conjunct of `UNJakUywRow` at `c' = 𝔠 * 𝔡 / 30`; `τ₀ = min τ₁ (1/4)`).
- `inst_row`, `inst_window`: PASS (sz0 admissible; every deterministic hypothesis holds at the printed data; `UNLocAvgBand`, `UNOUClaims` remain hypotheses).

## (b) Script output

```
$ date -u
Tue Oct  6 09:09:48 UTC 2026
$ git log -1 --format='%h %an <%ae>' t/T2273   # worktree /Users/junyin/Lean_proof/RBM3D-wt/T2273
9715ac7 Jun Yin <321276894+JYin80@users.noreply.github.com>
$ git diff --stat main...t/T2273   # main is now e2703ec; merge-base ed29a8b
 RBM3D/Test/Axioms.lean      |    2 +-
 RBM3D/Universality/Jak.lean | 1003 +++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1004 insertions(+), 1 deletion(-)
$ git diff main...t/T2273 -- RBM3D/Test/Axioms.lean | grep '^[+-]'
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNJak, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
+   `RBM.Univ.UNOUClaims, -- bulk universality pin, the two 𝐇_t claims (T2273, UN-21: owed; owner UNOURow)
$ git merge-tree --write-tree main t/T2273; echo exit=$?   # clean merge into the current main
exit=0
$ wc -l RBM3D/Universality/Jak.lean; grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/Jak.lean
    1003 RBM3D/Universality/Jak.lean
grep exit=1 (1 = no hit)

$ lake build RBM3D.Universality.Jak 2>&1 | tail -9
ℹ [3333/3333] Built RBM3D.Universality.Jak (19s)
info: RBM3D/Universality/Jak.lean:995:0: 'RBM.Univ.un_cd_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:996:0: 'RBM.Univ.unJak_of_ouClaims' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:997:0: 'RBM.Univ.jakRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:998:0: 'RBM.Univ.JakInst.inst_row' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:999:0: 'RBM.Univ.JakInst.inst_window' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:1000:0: 'RBM.Univ.JakInst.inst_unJak' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:1001:0: 'RBM.Univ.JakInst.inst_cd_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3333 jobs).
$ grep -c 'warning.*Jak.lean' <that build output>
0

$ lake build     # full library in the worktree (root without the Jak import, which the hub adds at merge)
Build completed successfully (4079 jobs).
exit=0
info: RBM3D.lean:316:0: axiom audit: 7922 theorems, 2614 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

```
$ python3 extract.py un_cd_le_half unJak_of_ouClaims jakRow   # target statements, extracted from RBM3D/Universality/Jak.lean
-- Jak.lean:451-452
theorem un_cd_le_half : ∀ d : ℕ, 1 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    𝔠 * 𝔡 ≤ 1 / 2 := by
-- Jak.lean:854-857
theorem unJak_of_ouClaims : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE sz 𝔡 τU → UNOUDiag sz τU →
        UNJak sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30) := by
-- Jak.lean:931-934
theorem jakRow :
    UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
        ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNJak sz E nf τU C (𝔠 * 𝔡 / 30) := by

$ python3 stmtdiff.py   # statement bodies of Jak.lean vs 'def T2273_<name> : Prop' of docs/tickets/checks/T2273-check.lean (whitespace-normalised)
un_cd_le_half: statement body identical to T2273_un_cd_le_half: True
unJak_of_ouClaims: statement body identical to T2273_unJak_of_ouClaims: True
jakRow: statement body identical to T2273_jakRow: True
inst_row: statement body identical to T2273_inst_row: True
inst_window: statement body identical to T2273_inst_window: True
ALL IDENTICAL

$ lake env lean check_with_jak.lean   # the check file + 'import RBM3D.Universality.Jak' + before 'end T2273Check':
#   example : T2273_un_cd_le_half := un_cd_le_half;  example : T2273_unJak_of_ouClaims := unJak_of_ouClaims;
#   example : T2273_jakRow := jakRow;  example : T2273_inst_row := JakInst.inst_row;  example : T2273_inst_window := JakInst.inst_window;
#   example (hrow : UNJakUywRow) : T2273_jakRow := (first-conjunct projection of hrow, binder for binder);
#   example (...) : UNJak sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30) := unJak_of_ouClaims ...;  #print axioms T2273Check.T2273_jakRow
exit=0   errors in output: 0
'T2273Check.T2273_jakRow' depends on axioms: [propext, Classical.choice, Quot.sound]

$ sed -n '954,965p;983,992p' RBM3D/Universality/Jak.lean   # the compiled nonempty instances (namespace RBM.Univ.JakInst); inst_window's tactic proof is Jak.lean:966-979
theorem inst_row :
    UNLocAvgBand → UNOUClaims →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJak SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun hloc hOU =>
    jakRow hloc hOU 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2

theorem inst_window :
    ∀ (n : ℕ) (τU : ℝ), 0 < τU →
      InWindow SizesInst.sz0 1 1 τU n (⟨1, (Nsz SizesInst.sz0 n)⁻¹⟩ : ℂ) ∧
        0 ≤ ouTStar SizesInst.sz0 τU n := by
  ...
theorem inst_unJak (τU : ℝ) (hτ : 0 < τU) (hτ4 : τU ≤ 1 / 4)
    (hQUE : UNOUQUE SizesInst.sz0 (1 / 10) τU) (hDiag : UNOUDiag SizesInst.sz0 τU) :
    UNJak SizesInst.sz0 1 2 τU (3 * ((2 : ℕ) : ℝ) + 16) ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  unJak_of_ouClaims 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
    (by norm_num) 2 τU hτ hτ4 hQUE hDiag

/-- `un_cd_le_half` at `sz0`: `𝔠𝔡 = 1/60 ≤ 1/2`. -/
theorem inst_cd_le_half : (1 / 6 : ℝ) * (1 / 10) ≤ 1 / 2 :=
  un_cd_le_half 3 (by norm_num) (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm

```

```
$ git log main -1 --format=%h; for n in <each new public name>; do git grep -nw $n main -- RBM3D RBM3D.lean; done   # name-clash grep on main
e2703ec
# un_cd_le_half
# unJak_of_ouClaims
# jakRow
main:RBM3D/Universality/Pins.lean:636:Registry class: **owed** (UN, `QUEFlow`/GUE phase). Consumer (RBM2D `c9a24cf`): `U
main:RBM3D/Universality/Pins.lean:647:(`|ψ_α(x)|² ≤ η Im 𝐑_xx`, `(eq:ukx)`).  RBM2D `OUDiag` (`Pins.lean:218`).  Registr
main:RBM3D/Universality/Pins.lean:658:RBM2D `OUClaims` (`Pins.lean:229`). Consumer (RBM2D `c9a24cf`): `Universality/Jak.
# JakInst
# inst_unJak
# inst_cd_le_half
# inst_row
# inst_window
main:RBM3D/Universality/JakKernel.lean:1025:theorem inst_window :
main:RBM3D/Universality/JakKernel.lean:1088:#print axioms RBM.Univ.JakKernelInst.inst_window
# jakRow: docstring notes only (RBM2D consumer lines, no declaration); inst_window: RBM.Univ.JakKernelInst.inst_window (another namespace)
$ git grep -nE 'namespace JakInst|JakInst\.' main -- RBM3D | wc -l;  git grep -n 'Jak_' main -- RBM3D | wc -l   # fresh namespace, fresh private prefix
       0
       0

$ python3 portdiff.py   # ports of RBM2D Universality/Jak.lean at c9a24cf (read with git show; 952 lines); private lemmas, block text normalised
Jak_rpow_mul                   RBM2D c9a24cf:66  RBM3D Jak.lean:57  verbatim
Jak_exists_dyadic              RBM2D c9a24cf:69  RBM3D Jak.lean:60  verbatim
Jak_Qb_le                      RBM2D c9a24cf:87  RBM3D Jak.lean:78  verbatim
Jak_alpha1_le                  RBM2D c9a24cf:138  RBM3D Jak.lean:129  verbatim
Jak_alpha2_le                  RBM2D c9a24cf:198  RBM3D Jak.lean:189  verbatim
Jak_good_total_le              RBM2D c9a24cf:220  RBM3D Jak.lean:213  modified
Jak_crude_total_le             RBM2D c9a24cf:279  RBM3D Jak.lean:271  modified
Jak_prod_row_le                RBM2D c9a24cf:313  RBM3D Jak.lean:305  verbatim
Jak_prod_crude_le              RBM2D c9a24cf:333  RBM3D Jak.lean:325  verbatim
Jak_grid_energy_lt             RBM2D c9a24cf:362  RBM3D Jak.lean:354  verbatim
Jak_integral_le_of_majorant    RBM2D c9a24cf:384  RBM3D Jak.lean:376  verbatim
Jak_measure_grid_fail          RBM2D c9a24cf:416  RBM3D Jak.lean:408  modified
Jak_pointwise_good_norm        RBM2D c9a24cf:500  RBM3D Jak.lean:497  modified
Jak_fixed_time                 RBM2D c9a24cf:553  RBM3D Jak.lean:561  modified
Jak_c_le_half                  RBM2D c9a24cf:471  RBM3D Jak.lean:None  not in RBM3D file
Jak_gSel_eq_Gsig               RBM2D c9a24cf:456  RBM3D Jak.lean:None  not in RBM3D file
Jak_integrand_eq               RBM2D c9a24cf:463  RBM3D Jak.lean:None  not in RBM3D file
Jak_main                       RBM2D c9a24cf:834  RBM3D Jak.lean:None  not in RBM3D file
# RBM2D public/private mapping: Jak_main :834 -> unJak_of_ouClaims; jakRow :903 -> jakRow; JakCheck :923-948 -> RBM.Univ.JakInst;
#   Jak_c_le_half :471 -> public un_cd_le_half (rewritten); Jak_gSel_eq_Gsig :456, Jak_integrand_eq :463 dropped (integrand already in Gres form)
$ git -C ../RBM2D --no-optional-locks log -1 --format='RBM2D HEAD %h'; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/Jak.lean
RBM2D HEAD 9e0f275
 RBM2D/Universality/Jak.lean | 133 +++++++++++++-------------------------------
 1 file changed, 40 insertions(+), 93 deletions(-)
# (the port was read at c9a24cf as pinned by the ticket: git show c9a24cf:RBM2D/Universality/Jak.lean; RBM2D HEAD only trims dead code/comments)
$ git -C ../RBM1D ...  # no RBM1D text was ported directly (RBM2D Jak.lean cites RBM1D c06b103 for the arithmetic; RBM2D's text is the source)

$ lake env lean precheck.lean   # file: import RBM3D; import RBM3D.Universality.Jak; #assert_rbm_axioms   (registry pre-check, T2273 ticket)
exit=0
axiom audit: 7929 theorems, 2614 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
166:premises found by scanning: 160 (borrowed 1, owed 101, structural 41, refuted 6, superseded 11).
167:registry: 2 borrowed + 157 owed + 103 structural + 7 refuted + 12 superseded; 121 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
111:  RBM.Univ.UNOUClaims: 3 [no certificate]
# owed count: the registry diff above is one deletion + one addition (owedProps entries 275 -> 275, below); the category counts '2 borrowed + 157 owed + 103 structural + 7 refuted + 12 superseded' are identical with and without the Jak import (full-build line: registry: 2 borrowed + 157 owed + 103 structural + 7 refuted + 12 superseded; 124 )
$ python3 (owedProps entries at the merge-base ed29a8b vs the branch, parsed from RBM3D/Test/Axioms.lean)
merge-base ed29a8b: owedProps entries 275; branch: 275; removed: ['RBM.Univ.UNJak']; added: ['RBM.Univ.UNOUClaims']
```

### Narrative (stage 1b; every statement is backed by the script output above)
- Delivered: new `RBM3D/Universality/Jak.lean` (1003 lines, commit 9715ac7 on `t/T2273`; direct imports `JakKernel`, `OU` only) and one registry line in `RBM3D/Test/Axioms.lean`. Public: `un_cd_le_half`, `unJak_of_ouClaims`, `jakRow`; in `RBM.Univ.JakInst`: `inst_row`, `inst_window` (the ticket's instances) and `inst_unJak`, `inst_cd_le_half` (extra applications of the other two targets at `sz0`). The statements of `un_cd_le_half`, `unJak_of_ouClaims`, `jakRow`, `inst_row`, `inst_window` are identical to the check file bodies (`stmtdiff.py`); `example : T2273_<name> := <name>` compiles for each.
- Exponent redo: the parameter of RBM2D `Jak_fixed_time` is `c = 2𝔠𝔡` (`hcdef`); `Jak_alpha1_le`, `Jak_alpha2_le`, `Jak_Qb_le` are verbatim at this `c` (`portdiff.py`). Changed: `Jak_good_total_le` takes the pin exponent `c'` (`= 𝔠𝔡/30`) as a separate parameter, with `c' ≤ c/36` (`𝔠𝔡/30 ≤ 𝔠𝔡/18`) and the bad constant `K = 2d+1` (so `h5` is `3 (C₁ + 4K) C₂ ≤ N^{6τ}`); `Jak_crude_total_le` needs `c' ≤ 1` instead of `c < 36`; `Jak_measure_grid_fail` uses `Gres · · true`. Binding term: `ℙ(𝓑)` (slack `𝔠𝔡/18 − 𝔠𝔡/30 = 𝔠𝔡/45` in the good part).
- `Jak_fixed_time` is stated over an abstract probability space (`P`, `Hr`, `hH`); the band data `ouP (UNModel.band sz) n`, `ouMat … t` enter only in `unJak_of_ouClaims`. Its `hque` has the form `W^{-𝔡/30}`, converted from `queBound` by the private `Jak_queBound_eq` (`un_que_exponent`).
- Bad block: the merged `measure_bad_le_of_queBadMat` gives the event at `siteBlock y` only, while `jak_pointwise_good` asks `hBad` for every block `a0`; the predicate is `Bad a0 := a0 ≠ siteBlock d L W y ∨ ω ∈ Bm`, so `Bad (siteBlock y) ↔ ω ∈ Bm`. Off `Bm`: `‖blockM‖ < W^{-𝔡/6} ≤ N^{-𝔠𝔡/6} ≤ N^{-c/36}` (`un_W_neg_le`, `N ≥ 1`). Window: `|λ_α − E| ≤ w' + C₀/N ≤ N^{-1+c/6} = N⁻¹ N^{𝔠𝔡/3} ≤ N⁻¹ W^{𝔡/3}` from `h2` and `N^𝔠 ≤ W`.
- `un_cd_le_half` proves `𝔠 d ≤ 1` (non-strict suffices: `W^d ≤ (W L)^d` at a size with `N ≥ 2` and `N^𝔠 ≤ W`) and `𝔡 ≤ d/2` (by contradiction: `W → ∞` from `Bandwidth`, so `W^{-d/2+𝔡} → ∞` against `lam ≤ 𝔡⁻¹`), then `𝔠𝔡 ≤ 𝔠 d/2 ≤ 1/2`. `3 ≤ d` is carried; the lemma uses `1 ≤ d` only.
- `Jak_grid_energy_lt` is kept strict (`<`); `UNOUDiag` (energy range `≤`) is applied with `he.le`.
- `Jak_fixed_time` carries `set_option maxHeartbeats 400000 in` with a comment (the default 200000 timed out at the first full elaboration, tool log; same option in `PinsC2.lean:581`, `PoissonSmoothing.lean:623`). Otherwise only the RBM2D linter options.
- Registry: the `UNJak` owed line is deleted and the `UNOUClaims` owed line (the ticket's text) is written at the same position, not at the end of `owedProps` (position only). Against the current main the branch merges cleanly (`git merge-tree`, exit 0); `git diff main -- Test/Axioms.lean` also shows T2270's registry deletions (main moved), so the acceptance check is the three-dot form printed above.
- Instances: `UNLocAvgBand`, `UNOUClaims` (`inst_row`) and `UNOUQUE`, `UNOUDiag` (`inst_unJak`) stay hypotheses (pins of other rows); every deterministic hypothesis is discharged at `sz0` (`UNInst.sz0_adm`, `d = 3`, `κ = 1/2`, `E = 1`, `nf = 2`). `inst_window` holds at every `n` and every `τ_U > 0`. Limit checks of the external hypotheses: section (a).
- Not targets, untouched: `UNUyw`, `uywRow`, `UNJakUywRow`, `UNJakk`, `UNJakUywRowk`, `UNJakUywRowBA`, the hypotheses `UNOUClaims`/`UNOUQUE`/`UNOUDiag`/`UNLocAvgBand`, `JakKernel`, `JakSpectral`, `Pins`, `OU`, every refuted or superseded pin. No direct import of `OUHessian`, `PinsK`, `Green/*`.
- Section (a): no correction. (a) writes `W^d < N` for `un_cd_le_half`; the proof uses the weaker `W^d ≤ N`, enough for the stated conclusion.

## (c) Verified Mathlib names used
Checked present in the environment by `#eval` over `env.contains` (script `names2.lean` checked 102 names, the 101 below and `ite_eq_left` (the replacement named by the deprecation warning below, not used by the file): 102 `present`, 0 `ABSENT`; the bare measure-theory names are in `MeasureTheory`, `Measure.real` is `MeasureTheory.Measure.real`):
```
Complex.I, Complex.im_le_norm, ENNReal.mul_ne_top, ENNReal.natCast_ne_top, ENNReal.ofReal, ENNReal.ofReal_mul
ENNReal.ofReal_natCast, ENNReal.ofReal_ne_top, ENNReal.toReal_le_of_le_ofReal, ENNReal.toReal_mono
ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal, Finset.card_image_le, Finset.card_le_univ
Finset.card_range, Finset.card_union_le, Finset.mem_image, Finset.mem_range, Finset.mem_singleton, Finset.mem_union
Finset.mem_univ, Finset.prod_const, Finset.prod_le_prod₀, Finset.prod_nonneg, Finset.range, Finset.sum_congr
Finset.sum_const, Finset.sum_le_sum, Finset.univ, Measure.real, Nat.add_le_add, Nat.add_le_add_right
Nat.cast_nonneg, Nat.ceil_lt_add_one, Nat.ceil_mono, Nat.find, Nat.find_min, Nat.find_spec, Nat.le_mul_of_pos_right
Nat.le_succ, Nat.lt_succ_iff, Nat.lt_two_pow_self, Nat.one_le_iff_ne_zero, Nat.one_le_pow, Nat.pos_of_ne_zero
Nat.pow_le_pow_left, Real.log, Real.log_inv, Real.log_le_log, Real.log_le_rpow_div, Real.log_le_sub_one_of_pos
Real.log_pow, Real.one_le_rpow, Real.rpow_add, Real.rpow_le_rpow, Real.rpow_le_rpow_of_exponent_le
Real.rpow_lt_rpow_of_exponent_lt, Real.rpow_mul, Real.rpow_natCast, Real.rpow_neg, Real.rpow_neg_one, Real.rpow_one
Real.rpow_sub, Set.indicator_nonneg, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_iUnion
Set.mem_ofPred_eq, tendsto_rpow_atTop, tendsto_rpow_neg_atTop, tendsto_atTop_mono', tendsto_natCast_atTop_atTop
pow_unbounded_of_one_lt, pow_le_pow_right₀, pow_le_pow_left₀, one_le_pow₀, inv_anti₀, le_inv_comm₀, inv_le_comm₀
div_le_div_of_nonneg_left, mul_inv_le_iff₀, div_le_iff₀, le_div_iff₀, mul_le_mul_of_nonneg_left
mul_le_mul_of_nonneg_right, measure_toMeasurable, subset_toMeasurable, measurableSet_toMeasurable
measure_biUnion_finset_le, integral_mono, integral_undef, integral_indicator_one, integral_add, integral_const
integral_const_mul, integrable_const, abs_sub_le, abs_le, abs_lt, half_pos
```
Observed in the tool log: `if_pos` / `if_neg` raise a deprecation warning in this Mathlib (`Use ite_eq_left instead`); the file uses `simp only [..., ↓reduceIte]` instead. `Set.mem_ofPred_eq` is the membership simp lemma used (as in RBM2D `Jak.lean:428`); `Set.mem_setOf_eq` is also present. No name was found absent.

## (d) Open issues and paper-delta candidates
- No open issue blocks the merge. No statement differs from the ticket's pins; no primed successor.
- **T2273a** (design table, no paper statement): portmap row UN-21 "`C = 3nf+16` to be redone" is confirmed: `C = 3nf+16`, `τ₀ = min τ₁ (1/4)` hold at `d ≥ 3`; the only constant that changes against RBM2D is `20 = 4·5 → 4(2d+1)` in `h5`; good exponent `𝔠𝔡/18`, bad exponent `𝔠𝔡/30` (`ℙ(𝓑)` binds, as `un_cprime`); the registry entry `UNOUClaims` (owner `UNOURow`) is added. `un_cd_le_half` is a new public lemma (RBM2D's was private, `Jak_c_le_half` `:471`); it has no paper statement (it follows from `(Main_DEL_COND)` and `(eq:WO)` as `Admissible` states them).
- **T2273b**: none (no statement difference found).
- For the dispatcher (not a defect): `inst_window` is also the name of `RBM.Univ.JakKernelInst.inst_window` (another namespace, no clash); UN-23 will need the `max` of the `C` of `jakRow` and `uywRow` (`UNJak` monotone in `C`), which is not in this file.
