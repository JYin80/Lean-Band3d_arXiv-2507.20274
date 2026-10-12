Auditor model: claude-opus-5-5

# T2435 1a-audit (design gate, BA-L L3c3a `BAAuxGraph2`) — Mon Oct 12 05:50:58 UTC 2026

Inputs: ticket `docs/tickets/T2435.md`; `docs/reports/T2435-prove.md` (a), (a′), (a″); branch `t/T2435` at e9a3986; own detached
worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2435-1a-audit` (`.lake/build` CoW clone, packages symlink). Scratch: `<scratchpad>/T2435/audit/`.

**Verdict: PASS.** All stage-1a deliverables (i)–(vi) present; probe compiles (exit 0); numerics reproduce; no binding stop line hit.

## 1. Probe compile (acceptance "1a")

```
$ cd RBM3D-wt/T2435-1a-audit; git log -1 --format=%h  ->  e9a3986
$ time lake env lean RBM3D/Probe/T2435Pins.lean; echo "exit code: $?"      (Mon Oct 12 05:47:00 -> 05:47:09 UTC)
@baZetaSq : ...   @baZetaVar : ...   BAZetaVarNonneg : Prop   BAZetaVarSymm : Prop   BAZetaWard : Prop   @LWXigL : ...
BAZetaClaim : ℕ → Prop   @BAGbyZetaU : ...   BAGbyZeta : ℕ → Prop   BAGbyZetaHxi : Prop   BAEntryPsi : ℕ → Prop   BAAnpAuxG : ℕ → Prop
baGtoAG_holds : ∀ (d : ℕ), BAGtoAG d
baGbEXPij'_holds : ∀ (d : ℕ), 2 ≤ d → BAGbEXPij' d
baGbEXPii_holds : ∀ (d : ℕ), 2 ≤ d → BAGbEXPii d
BAm_norm_le_one : ∀ (d L : ℕ) [inst : NeZero L] (g : ℝ) (z m : ℂ), 0 ≤ z.im → BASelf d L g z m → ‖m‖ ≤ 1
exit code: 0            (no error/warning line; #check lines abbreviated to their heads above)
$ wc -l < RBM3D/Probe/T2435Pins.lean; grep -n -E "sorry|admit|axiom|native_decide" ...; echo "grep exit $?"
331
grep exit 1
$ git diff --stat main...t/T2435
 RBM3D/Probe/T2435Pins.lean | 331 +++++++++++++++++++++++++++++++++++++++++++++
$ git diff --name-status $(git merge-base main t/T2435) main -- RBM3D RBM3D.lean lean-toolchain lake-manifest.json   (main = d11da04)
M RBM3D.lean / A BA/TwistGridWTail.lean / A BA/TwistGridWTail2.lean / A Graph/BALvl1A.lean / M Test/Axioms.lean
$ python3 closure (import closure of the probe vs. those five files)
263 files; changed-on-main files in closure: none
```

## 2. Pins against the ticket and the band basis (script diffs)

```
$ diff <(sed -n "/^def T2435_LWXigL/,/^$/p" docs/tickets/checks/T2435-check.lean | sed s/T2435_LWXigL/LWXigL/) \
       <(sed -n "/^def LWXigL/,/^$/p" RBM3D/Probe/T2435Pins.lean); echo "diff exit: $?"
diff exit: 0                                    (target 2 = check-file pin; bridge `… ↔ LWXi …` is `Iff.rfl`, probe :87-89, compiled)
$ diff <(def BAAnpAux, BAAtom2.lean:677..) <(def BAAnpAuxG, probe)      (target 6)
1c1  BAAnpAux -> BAAnpAuxG
6,7c6,7  STFlow -> BAFlow ; lemT (z n) -> BAflowT0 sz z n
9,10c9,11  LWXi sz (STflowE z) t Φ ξ -> LWXigL (baFMz sz z) (seqP (sz.withLam 0)) t Φ ξ ; Prec sz -> PrecL sz (seqP (sz.withLam 0))
12c13  etaT (STflowE z n) (t n) -> (baFMz sz z).eta n (t n)
```
Only the substitutions the ticket names (target 6). Targets 3, 5 (`BAZetaClaim`, `BAEntryPsi`) read line by line against `LWXiClaim`
(`AuxGraph2:951`), `LWEntryPsi` (`:1177`): same quantifier order (`3 ≤ d`, `κ ε 𝔡`, `𝔠 sz z`, flow, `t`, class, loop, `ε₁`, entry bound,
`ρ`); carrier/law/`T0` substituted; target 3 adds `D₁ ≥ d + 2C₂/(𝔠d) + 1` (the floor; E4). Target 4 (`BAGbyZeta`) vs `LWGbyXi`
(`:1106`): index set includes `x = y` (G3's `hξ` reads all pairs, `BAAtom2:405-406`), `‖G−M‖` instead of `|G|`, no class/loop premise,
and `2R+1 ≤ ρ` is replaced by `∀ K, ∀ᶠ n, K log W ≤ ρ − 2R` (needed by the tail, see §3). `BAGbyZetaHxi` feeds `hξ0`, `hξ` of
`baGtoAG_holds` without cast (probe :287-320 compiled; prover's neg1 swaps them and fails).

## 3. Item (i): ζ and the joint check (a)+(b) — PASS

ζ = `baZetaVar` = √(block loop-window sum of `‖L_{(t,f)}‖ + ‖L_{(f,t)}‖` over ℓ∞-balls radius ρ + `W^{-d}1(|a−b|∞≤ρ)` + `W^{-D₁}`),
the band's `lwXiSq` (`AuxGraph2:67`) on `baFMz` plus a floor. Checks of the cited inputs:
```
$ sed -n 916,940p RBM3D/BA/GreenOff.lean   (GreenOff_carrier_decay, abbreviated)
theorem GreenOff_carrier_decay ... (ω : sz.SeqΩ) {P δ Ψ : ℝ} {φ : Zd d (sz.L n) → Zd d (sz.L n) → ℝ} ... (hΩ : ∀ x y, ‖GM‖ ≤ δ)
    (hLrow …) (hLcol …) (hLquad …) (hLdiag …) (hC1 …)
    (hφ0 : ∀ a b, 0 ≤ φ a b) (hφ : ∀ a b, ‖(baFMz sz z).L n t ![false, true] ![a, b] ω‖ ≤ φ a b ^ 2)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt ((W ^ d)⁻¹) ≤ Ψ) (hC2 …) (x y : Idx …) :
    ‖(baFMz sz z).GM n t ω x y‖ ≤ 2 * GreenOff_Cl … * GreenOff_T d (sz.L n) (GreenStab_clam d 𝔡⁻¹ κ) Ψ φ (STblk x) (STblk y)
$ sed -n 49,52p RBM3D/BA/GreenOff.lean
def GreenOff_T (d L : ℕ) [NeZero L] (γ Ψ : ℝ) (φ …) (a c : Zd d L) : ℝ :=
  (∑ a', ∑ b', φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - c) : ℝ)))) + Ψ * Real.exp (-γ * (zdistD d L (a - c)))
$ grep: zdistD = ∑ i, zdist (Lattice.lean:71); zdistInf = sup_i zdist (Sizes.lean:115); Bandwidth: N^𝔠 ≤ W (Sizes.lean:168-169)
$ GLoopFlow.lean:55,58: ztOf m E t = E + (1-t) m ; etaOf m t = (1-t) Im m      (so Im z_t = η = C.eta: Ward applies verbatim)
$ FlowPins.lean:264-266: BALloop = loopFine … (seqHflowBA …) (ztOf …)   (same loopFine as the band's Lloop: symmetry/Ward twin)
```
(a) re-derived: the core is per-sample with φ an arbitrary nonnegative function of the sample, so φ := ‖L_{(f,t)}‖^{1/2} discharges
`hφ` by `le_of_eq`; it holds at every `x, y` (diagonal included). Near part (ℓ∞ distance ≤ ρ' = ρ−2R from `[x]`,`[y]`):
zdistInf ≤ zdistD gives `|a'−a|∞ ≤ ρ'+R ≤ ρ`, Cauchy–Schwarz with `Σw ≤ S²` gives `≤ S²·ζ²`. Far part: zdistD ≥ zdistInf > ρ' ≥ K log W,
factor `W^{-γK/2}`, ≤ `W^{-D₁}` for `K` large: the hypothesis "every K" carries it (E5). Ψ := W^{-d/2} meets `hΨw` with equality; its
term is ≤ `W^{-d}1(|a−b|∞≤ρ)` or, off the window, ≤ `W^{-D₁}`. Ω and the LDE events as in `baGbEXPij'_holds`. No hidden hypothesis,
no unprimed `BAGbEXPij`. (b) is the band twin (`lwXiClaim_holds`, `lwXi_ward_sum` `AuxGraph2:507`; `η>0` from `BAFlow` + `t<1`
replaces `|E|<2`). Floor `W^{-D₁}`: Ward side needs `N W^{-D₁} ≤ 1` (⇔ `L^d W^{-D₁} ≤ W^{-d}`), `D₁ ≥ 1/𝔠 = 6`; `≺ Φ` side needs
`D₁ ≥ d + 2C₂/(𝔠d) + 1` (`L ≤ W^{1/(𝔠d)}` from Bandwidth). One ζ, one `(ρ,R,D₁)` serve both: instance §5.
E10 (pin-form ζ = Φ fails the block Ward by `N^{0.7}` at the admissible constant profile `W^{-1/2}`) is reproduced (§6); this is the
reason for the loop form, consistent with T2387 `:53`. Fine-lattice → block Ward: candidate T2435d. Generic-over-carrier: `LWXigL` only.

## 4. Item (ii) (2149 L6 (i)–(iv), 2254 G3) — PASS (written argument present; checked)

```
$ sed -n 1622-1627,1644-1652 RBM3D/BA/GreenCore.lean   (abbrev.)
GreenCore_decayRHS = Σ_{a',b'} Φ a' b' e^{-c(|a'-a|∞+|b'-b|∞)} + Ψ e^{-c|a-b|∞} + W^{-D}
BAGbEXPij': (∀ᶠ n, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ W^{-ε₀}) → (∀ᶠ n, W^{-d/2} ≤ Ψ n) → (∀ᶠ n, Ψ n ≤ W^{-ε₀}) → GreenCore_loopPrem … → …
$ sed -n 52-64 RBM3D/Graph/LWPsi.lean  LWClass: 0<Φ≤W^{-ε₀}, W^{-d/2} ≤ C₃Φ n 0 ; LWPsiRel: AntitoneOn, Φ0 ≤ Cc C·Φ ℓ (ℓ≤C),
  Φ ℓ₁ ≤ C₁ (ℓ₂/ℓ₁)^{C₂} Φ ℓ₂ (1≤ℓ₁≤ℓ₂)
$ sed -n 53-56 RBM3D/Chain/LWGen.lean  LWLoop2gL: PrecL ‖C.L ![p.1, !p.1] ![a,b]‖ (Φ(|a−b|)²)   (indMax ∈{0,1} ⇒ loopPrem at p.1=false)
```
Term 1, class `(eq:Psi)`: antitone + `(eq:Psi)` give `Φ(|a'−b'|) ≤ Cc(2)C₁(s+1)^{C₂}Φ(r)`, summable against `e^{-γs}`. Term 2:
`W^{-d/2}e^{-γr} ≤ C₃Cc(2)C₁ r^{C₂}e^{-γr}Φ(r)`, sup `(C₂/γ)^{C₂}`. Class `𝖳` (`3_5:313`, `𝒯_t(r)=B_{t,r}e^{-(r/ℓ_t)^{1/2}}`):
`(s+1)^{(d−2)/2}e^{√s/2}` ratio, summable; Term 2 via `A=(g²+|1−t|)^{-1} ≥ (Λ²+1)^{-1}` and `sup e^{-γs+√s/2} ≤ e^{1/(16γ)}`. Constants
n-independent (`exp(~6e31)` at `c_λ ≈ 2e-33`, finite). (iii) diagonal by `baGbEXPii_holds`; (iv) Ward via `BAMB_diag_eq` (`Ward.lean:89`),
`BAm_norm_le_one`. Stop line "(ii) false for class 𝖳" not hit. (ii) is not on the chosen path for target 4 (the core is used directly).

## 5. Items (iii)–(vi) and the instance

- (iii) unprimed `BAGbEXPij` not used, not a hypothesis. (iv) constants rerun (§6). (v) consumers, grep in the audit worktree:
```
LWXiExp: lwXi_ward_sum, lwXiClaim_holds, lwXiSq, lwXiVar, lwXiVar_nonneg, lwXiVar_symm
LWMoment: lwEntryPsi_holds, lwGbyXi_holds, lwGbyXi_hxi, lwXiClaim_holds, lwXiRad_holds, lwXiVar
LWMomentExp: lwGbyXi_holds, lwGbyXi_hxi, lwXiRad_holds, lwXiVar, lwXiVar_nonneg, lwXiVar_symm
LWExpTerm3: lwGbyXi_holds, lwXi_ward_sum, lwXiRad_holds, lwXiSq, lwXiVar, lwXiVar_nonneg, lwXiVar_symm
LWTermHolds: lwGbyXi_holds, lwXiClaim_holds, lwXiSq, lwXiVar
```
- (vi) section map: `AuxGraph2` §1–3 `:61-945` (885 lines) → `BAAuxGraph2` ≈ 950; §4 `:946-1100` + §5 `:1101-1232` (287) + §7
  `:1297-1500` (204) + ≈350 new (sample-wise route) → `BAAuxGraph2B` ≈ 950–1,150; §6 imported. Both under the stop line 2,000 even
  at the L3c1 landed ratio 1.34 (≈1,270 / ≈1,540). Boundary = end of §3, a section boundary (`grep "^/-! ## "`: §4 at `:946`).
- Name clash on `main` (d11da04), 20 names: `git grep -w -c` = 0 for each. `RBM3D/Graph/BAAuxGraph2*.lean`: absent on main.
- Joint instance (probe :191-275, compiled): `d=3`, `sz0`, `flow_sz0`, `t≡1/2`, `Φ0≡W^{-1/2}`, `ε₁=1/20`, `D₁=12`, `R=(log W)^{21/20}`,
  `ρ=2R+(log W)^{3/2}`; `LWPsiAll`, `ρ≥0`, `ρ+1≤N^τ`, `D₁` bound, `R≥0`, separation, Ward `hA` discharged; `LWLoop2gL` and the
  entry bound are other gates' pins (hypotheses). Nondegenerate: `n=0` gives `L=4, W=32`; proper window from `n=199` (§6).

## 6. Numerics rerun (copies of the prover's scripts; `python3`, numpy needs the user site)

```
$ python3 consts.py; python3 inst.py; python3 ii_check.py    (exit 0; verbatim lines, "…" marks abbreviations; full output in scratch rerun.out)
g=0.015625 Im m=0.8325 Im z=0.3675 kappa<=Im m:True Im z<=1:True c=4.1580e-03 C=1.152e+03 A=3.070e+11 S=2.055e+13 p5s=1.287e-32 c_lam=2.145e-33
g=1 Im m=0.3435 Im z=0.8565 kappa<=Im m:True Im z<=1:True c=2.0812e-03 C=9.216e+03 A=7.844e+13 S=3.275e+14 p5s=9.889e-38 c_lam=1.648e-38
g=10 Im m=0.0442 Im z=0.9558 kappa<=Im m:True Im z<=1:True c=3.3328e-04 C=2.250e+06 A=1.823e+20 S=4.980e+17 p5s=2.937e-51 c_lam=4.894e-52
D1 = d + 2*C2/(c*d) + 1 = 12;  Ward floor needs D1 >= 1/c = 6;  eps0 = eps1/2 = 0.025;  tau0 <= c*eps0 = 0.00417;  class T needs eps0 < min(dd, eps/2) = 0.05
n=0: L=4 W=32 N=2.097e+06 lam=0.0156 | hypotheses True | … | Ward ceiling 2/(W^d eta)=0.000153 <= Phi0^2=0.0313 (ratio 205) | W^-eps1/W^-d/2=152 | N*W^-D1=1.8e-12
      pin-form zeta=Phi0: (sum_b Phi0^2)*(W^d eta) = 2.62e+04 = N^0.699   (Ward block form needs <= N^tau for every tau>0)
n=10: … (ratio 5.31e+12) | W^-eps1/W^-d/2=5.4e+09 | N*W^-D1=3.3e-56 ;  pin-form … = 9.05e+17 = N^0.716
n=199: L=800 W=1.024e+13 N=5.498e+47 … (ratio 2.1e+25) | W^-eps1/W^-d/2=7.33e+18 | N*W^-D1=4.1e-109
      window: R=(log W)^(1+eps1)=35.5, rho=2R+(log W)^(3/2)=235.0, L/2=400, ball volume (2rho+1)^3/L^3 = 0.204 (proper subset iff rho<L/2: True)
      pin-form zeta=Phi0: (sum_b Phi0^2)*(W^d eta) = 2.15e+34 = N^0.719
g=0.015625: gamma=c_lam=2.145e-33  K_tail=2(1/c+D1+1)/gamma=1.772e+34  with rho-2R=(log W)^(3/2): log10(log W) >= 68.5
g=1: … K_tail=2.306e+39 … >= 78.7 ;  g=10: … K_tail=7.765e+52 … >= 105.8
 W=100 [(0, 22080.0, 0.01), (3, 351400.0, 0.0878), (6, 1071000.0, 0.148)]   (eq:Psi; W=1e6: Term2 ×1e-4)  class T: [(0, 154300.0, 9.77), …] W-independent
c=0.2 C2=2.0: max_r (r+1)^C2 e^-cr = 16.53 <= (C2/c)^C2 = 100 ;  c=0.2: max_s e^(-cs+sqrt(s)/2) = 1.367 <= e^(1/(16c)) = 1.367
```
Every value in the report's (a)(ii) block (lines 54-66) matches this rerun.

## 7. Paper-delta coverage
Candidates T2435a (block loop-window ζ, not the atom-centre sum `B:424-426`), T2435b (floor `W^{-D₁}`), T2435c ((a) from the
sample-wise core, not `(GijGEX_BA)` `7_8:1942`), T2435d (block Ward form) cover the statement differences of (vi).

## 8. Observations (no verdict change)
- O1. The report's (a)(ii) script block is a condensed reformatting of the output (headers omitted, lines merged), not verbatim; values identical.
- O2. (ii)'s constants also depend on `Cc(2)`, `C₃`, `Λ = 𝔡⁻¹` beyond the ticket's `(c_λ, d, C₁, C₂)`; all fixed, n-independent.
- O3. Target 4's separation premise `∀K ∀ᶠn, K log W ≤ ρ−2R` replaces the band's `2R+1 ≤ ρ`; the BA consumers (L3d2) must choose ρ
  accordingly (polylog, e.g. as in the instance). 1b should name it explicitly in T2435c.
- O4. The eventual thresholds of E5 are astronomical (`log₁₀ log W ≥ 68.5`); they sit in the conclusion's `≺`, not in a hypothesis.

## Verdict per item
(i) PASS · (ii) PASS (both terms, both classes) · (iii) PASS · (iv) PASS · (v) PASS · (vi) PASS (probe exit 0, 331 ≤ 400 lines).
Targets 1–7 as designed: PASS for 1b. Stop rule not triggered. No dispatcher sign-off required.
