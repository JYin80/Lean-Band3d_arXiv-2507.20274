Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 12:32:47 UTC 2026

The only mathematical target is D4, the shared statement `BAKellStarEv d` (D1–D3, D5, D6 are census and sizing, with no exponent). Its content is `KellStarEv` (`RBM3D/Path/KellStar.lean:54`) at the BA carrier. The data are `BATheta` and the rate `ellT L g t`, as in `BACompBound` (`BA/EMn2BA.lean:457`) and `baEMn2ExpHK` (`BA/EMn2BA.lean:637`).

### (i) Exponent table

| Quantity | Value or source | Constraint | Slack |
|---|---|---|---|
| `d` | 3 | `3 ≤ d` (`KellStarEv:55`) | 0 at the minimum |
| `Λ` | `𝔡⁻¹` (`FarEntry:712`, `LemDecCalEPrec:990`) | `0 < Λ`; `0 < lam n ≤ Λ` eventually | `WO` (`Defs/Sizes.lean:164`) gives `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`, so the window holds with equality at the top end when `lam = 𝔡⁻¹` |
| `𝔠` | `≤ 1/100` (`BA/FlowPins.lean:412`, `𝔠_d`) | `0 < 𝔠`; `Bandwidth`: `N^𝔠 ≤ W` eventually | at the instance below, `N^𝔠 = 1.72 ≤ W = 1048576` |
| `τ` | `ε/2` (FarEntry, LemDecCalEPrec) | `0 < τ`; `RangeCond τ t`: `N^{-1+τ} ≤ 1-t_n` | `A = max(1-τ,0) = 1-τ < 1`, margin `τ` |
| `δ` | `1/8` (LemDecCalEPrec) or `ε/2` (FarEntry) | `0 < δ` | the closing inequality needs `c δ √x ≥ K` (next rows) |
| `D` | free real (`2D'` at FarEntry) | none (`W^{-D}`; `D` may be negative) | enters `K` through `|D|` |
| amplitude | `Bparam ≤ 2(1-u)⁻¹ ≤ 2N^{1-τ} ≤ 2W^{A/𝔠}` (`KellStar:68`, `EMn2BA_bparam_le`) | `A/𝔠 ≥ 0` | at the instance, `A/𝔠 = 75` |
| `K` (kellStar form) | `2C + A/𝔠 + |D|` (`KellStar:178`) | `K ≥ 0` | `K = 79` with the placeholder `C = 1`, `𝔠 = 1/100`, `τ = 1/4`, `D = 2` |
| `K` (BA form, `baEMn2ExpHK`) | `2C + 1/𝔠 + |D+d|` (`EMn2BA:648`), since `1-t ≥ N⁻¹/2` there | `K ≥ 0` | `K = 107` at the same data, with `D+d = 5` |
| closing threshold | `x = log W ≥ max(1, (K/(cδ))²)` (`EMn2BA_arith`, `EMn2BA:597`: needs `2C + k + |D| ≤ c δ √x`) | this is the conclusion's `∀ᶠ n` threshold, not a hypothesis | with the placeholders `C = c = 1`, `δ = 1/8` it is `x ≥ 3.99e5` (kellStar form) or `7.33e5` (BA form) |
| `(log W)^{3/2}` vs `log W` | exponent 3/2 vs 1 | `3/2 > 1` | margin 1/2; this is why `√x` can absorb the constants |
| far-set nonemptiness | `δ (log W)^{3/2} ℓ_u ≤ ⌊L/2⌋` (`ellT` in `Defs/Params.lean:32`) | else the conclusion is vacuous | at the instance with `1-t = 1/2`: `9.12 ≤ 32` |
| flags | T: `28.5 + 1.5k`; U: `34.5 + 1.5j` (1152 `:155, :175`); BA 119 | stop rule: more than about 3 producers beyond U-C1's 23 rows | `k + j = 3` gives at most 33.0 and 39.0 |
| census threshold | 200 lines below (C10); T2379 B5b reference: 147 facts / 3065 lines (`T2379-prove.md:179`) | the rebuilt B5b list must be compared to this | not an exponent |
| size limits | report ≤ 300, probe ≤ 400 lines | stop rule | not an exponent |

The constants `C, c` are existential, from `baComp_holds` (depending only on `(d, Λ, κ)`). Their values were not computed. `C = c = 1` is a placeholder used only to show the order of magnitude of the closing threshold. The target does not depend on their values.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `κ = ε = 1/2`, `𝔡 = 1` (so `Λ = 1`), `𝔠 = 1/100`, `τ = ε/2 = 1/4`, `δ = 1/8`, `D = 2`. Sizes: `L_n = 64`, `W_n = 2^{20}`, `lam = 1`. Time: `1-t = 1/2`, so `t = 1/2 < 1`. Spectral datum: `Im z = 0.01`.

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2452 && python3 -I inst.py
N=(WL)^d = 302231454903657293676544   log W = 13.863
H1 3<=d: True   H2 0<c: True  0<Lam: True  0<tau: True  0<delta: True
Bandwidth N^c<=W: 1.7171308728755075 <= 1048576 True
WO W^(-d/2+dd)<=lam<=1/dd: 0.0009765625 <= 1.0 <= 1.0 True
lam window 0<lam<=Lam: True
1-t=5.000e-01  RangeCond: True  t<1: True  ell_t=1.414  delta*(logW)^1.5*ell=9.124  max zdistInf=floor(L/2)= 32  far set nonempty: True
1-t=1.000e-02  RangeCond: True  t<1: True  ell_t=10.000  delta*(logW)^1.5*ell=64.520  max zdistInf=floor(L/2)= 32  far set nonempty: False
BAdom z: N^(-1+eps)=1.819e-12 <= Im z=0.010 <=1 : True
illustrative C=c=1: K(kellStar)= 79.0  K(BA emn2ExpHK form)= 107.0
threshold x>=max(1,(K/(c*delta))^2): 399424.0  ; BA form: 732736.0
exponent margin: 3/2-1 = 0.5
```

Reading of the output:
- All hypotheses of `KellStarEv` hold at one point: `3 ≤ d`, `0 < 𝔠, Λ, τ, δ`, `SizeTendsto`, `Bandwidth`, `RangeCond τ t`, `t < 1`, and the `lam` window. `BAdom` (`BA/MFixedPoint.lean:435`) holds for the `z` datum. `κ ≤ Im m` is a datum of `BAdom` and was not evaluated here.
- The block sequence `W_n = 2^n`, `L_n = 64` satisfies the `Bandwidth` and `RangeCond` inequalities for every `n ≥ 1`, with `t_n = 1/2`. The check `(64·2^n)^{0.03} ≤ 2^n` first holds at `n = 1`. `N → ∞` is clear since `N = (64·2^n)³`.
- The far set is nonempty at `1-t = 1/2` (`9.12 ≤ 32`). At `1-t = 1/100` it is empty at `L = 64` (`64.5 > 32`), so the far set needs `ℓ_u` small relative to `L`. The consumers' `∀ u ≤ t_n` range includes `u = 0`, where `ℓ_0 = min(max(lam,1), L) = 1` at `lam = 1`.
- No external hypothesis occurs. `STFlow`/`BAFlow` data enter only through the pieces listed above, and the inputs are merged declarations (`prop5Decay_holds`, `baComp_holds`).
- The conclusion's threshold `log W ≥ 3.99e5` (placeholder constants) is eventual, not a hypothesis. The hypotheses are satisfied at `W = 2^{20}`. The probe `example`s can be given at generic `sz`, with the hypotheses as local data.

### Verdicts
- D4 (`BAKellStarEv`): **PASS**. The hypothesis set is satisfiable at nondegenerate data, all exponents close (`3/2 > 1`, `τ < 1`), and no new mathematics is needed beyond `baComp_holds` and the closing inequality `EMn2BA_arith`.
- D1–D3, D5, D6 (census, producers, flags): no exponent or hypothesis set to check at this stage. **PASS**, with no missing input. The facts they rely on are all in merged files (ticket: "merged inputs only").

## (a′) Preflight corrections — Mon Oct 12 13:42:32 UTC 2026
- (a) cites `baComp_holds` as the source of the constants `C, c`. The Theta-level statement `BAKellStarEv` takes them from `baProp5_holds` (`BA/Prop6Path.lean:850`, `BAProp5`: `‖Θ(0,a)‖ ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}`), as the ticket's D4 route says. `baComp_holds` (`BA/EMn2BA.lean:472`) bounds `ΘM` and serves the K-level `baEMn2ExpHK` (design report D4). The dependence is `(d, Λ, κ)` in both, and the exponent table is unchanged. No verdict changes.

## (b) Script output — Mon Oct 12 13:41:51 UTC 2026
Report-only design ticket: the deliverable is `docs/reports/T2452-design.md` (script analysis there). The probe is never merged and is not a library module, so the build command is `lake env lean` (ticket acceptance), not `lake build`.

### Build, axioms, forbidden tokens (probe file as committed in `20d5f15`; later commits on the branch add only the design report)
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2452 && lake env lean RBM3D/Probe/T2452Pins.lean; echo "exit=$?"
'RBM.BA.baKellStarEv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_kellFarGen_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_kellFarGen_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_kellFarGen_ba_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_ba_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_bridge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_twMB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_K_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_etaOf_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ wc -l RBM3D/Probe/T2452Pins.lean
     371 RBM3D/Probe/T2452Pins.lean
$ grep -nE 'sorry|admit|native_decide|^axiom|^inductive' RBM3D/Probe/T2452Pins.lean | wc -l
       0
```
### Name-clash grep of the new public names (hits outside `Probe/`; `main` for the first three)
```
BAKellStarEv 0 | KellFarGen 0 | baKellStarEv 0 | T2452_Bridge 0 | T2452_bridge 0 | T2452_bridge_holds 0 | T2452_K_eq 0 | T2452_twMB 0 | T2452_ba_premises 0 | T2452_etaOf_antitone 0 | T2452_arith 0 | T2452_kellFarGen_band 0 | T2452_kellFarGen_ba 0 | T2452_kellFarGen_ba_flow 0 | 
on main: BAKellStarEv 0 | KellFarGen 0 | baKellStarEv 0 | 
```
### Target statements, extracted from the probe by `sed -n`
```
$ sed -n 38,53p   (BAKellStarEv, KellFarGen)
def BAKellStarEv (d : ℕ) : Prop :=
  ∀ (Λ κ : ℝ) (sz : Sizes d) (𝔠 τ δ D : ℝ) (t : ℕ → ℝ) (g E : ℕ → ℝ) (m : ℕ → ℂ),
    3 ≤ d → 0 < Λ → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < δ → sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.RangeCond τ t →
    (∀ n, t n < 1) → (∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
    ∀ σ₁ σ₂ : Bool, ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ a b : Zd d (sz.L n),
      δ * (Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (g n) u) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖BATheta d (sz.L n) (g n) (E n) (m n) u σ₁ σ₂ a b‖ ≤ (sz.W n : ℝ) ^ (-D)

/-- **The generic consumer hypothesis** (proposal): the far field of a family of profiles `Th n u a b` at the rate `ell n u`, uniformly in
`u ∈ [0, t_n]`.  The band instance is `Theta` at `ellT L (lam n)`, the BA instance is `BATheta` at `ellT L g_n`. -/
def KellFarGen {d : ℕ} (sz : Sizes d) (ell : ℕ → ℝ → ℝ) (Th : ∀ n : ℕ, ℝ → Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (δ D : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ a b : Zd d (sz.L n),
    δ * (Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ell n u) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Th n u a b‖ ≤ (sz.W n : ℝ) ^ (-D)

$ sed -n 179,181p (BA flow premises)
theorem T2452_ba_premises {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (htT : ∀ n, t n ≤ BAflowT0 sz z n) :
    (∀ n, t n < 1) ∧ sz.RangeCond (ε / 2) t := by
$ sed -n 229,242p (the three identities; the bridge)
def T2452_Bridge (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) =
            STgAg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
            STgDriftg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
            STEEMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n k)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n k ω) σ a

theorem T2452_bridge {d : ℕ} (C₀ : ℝ) (hB : T2452_Bridge d) (hT : BATwistGridMartAt d C₀) :
    STGridMartAtgL d C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
$ sed -n 308,310p (the bridge, for STGridMartgL)
theorem T2452_bridge_holds {d : ℕ} (hB : T2452_Bridge d) :
    STGridMartgL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
  obtain ⟨C₀, hC₀, hAt⟩ := baTwistGridMart_holds d
$ sed -n 347,348p (CondDom carrier form)
theorem T2452_etaOf_antitone {m : ℂ} (hm : 0 ≤ m.im) {u t : ℝ} (hut : u ≤ t) : etaOf m t ≤ etaOf m u := by
  unfold etaOf; nlinarith
```
### The compiled nonempty instance (`d = 3`; every deterministic hypothesis discharged)
```
$ sed -n 205,214p

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst in
/-- **Compiled nonempty instance of `baKellStarEv`** at `d = 3`: the BA instance `sz0`, `zSeq` of `FlowPins` §9 (`flow_sz0`:
`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`), `t ≡ 1/2 < t₀_n`, `δ = 1/8`, `D = 1`, charges `(+,-)`; every deterministic hypothesis is discharged. -/
example : KellFarGen sz0 (fun n u => ellT (sz0.L n) (BAflowLam0 sz0 zSeq n) u)
    (fun n u a b => BATheta 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n)
      (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) u true false a b) (1 / 8) 1 (fun _ => 1 / 2) :=
  T2452_kellFarGen_ba_flow (le_refl 3) (baKellStarEv 3) (by norm_num) (by norm_num) sz0 flow_sz0
    (fun n => (half_lt_t0 n).le) (1 / 8) 1 (by norm_num) true false

```
The other four `example`s (`:172`, `:216`, `:351`, `:355`) apply the band and BA implications at local hypotheses (`STFlow`, `BAFlow`, `|E| < 2`, `BAReal`). `T2452_bridge_holds` takes the three identities `T2452_Bridge` as a hypothesis: they are the content of row P1 (another gate's unproved pin), not an instance obligation of this ticket.
### Ports
None from RBM1D or RBM2D (no diff-stat). The closing inequality `T2452_arith` is a copy inside RBM3D of `kellStar_arith` (`Path/KellStar.lean:89`) and `EMn2BA_arith` (`BA/EMn2BA.lean:597`), both `private`; the design report names the amend that removes the copy.
### Census scripts (scratch `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2452`; sha256 prefix, lines, file)
```
19496da7bbf7 204 cenlib.py
971493906ecb 174 census.py
f0b52a1a5123 73 b5b.py
1d3b0df8f238 21 rowtable.py
52d2482e6fdc 62 report_tables.py
8042984d728b 35 bound.py
af9d5aa8642e 24 cone.py
69643ec94407 51 dens.py
67ce6603c8f6 39 b5b_join.py
8f284d55a4fb 30 urows.py
190cdce25b10 26 unresolved.py
839fd54db9fb 24 run_all.sh
```
Run: `bash $S/run_all.sh <outdir>` from the repository root (61 s; worktree and `main` agree, see the design report D1). The name check `names.lean` (78 `#check` of the BA and band declarations cited): `lake env lean $S/names.lean` exit 0, 0 errors.
### The 77 facts over 200 lines below (`out_wt/facts.tsv`: full name | producer file:line | own lines | lines below | spec (S) | first use of each reader (`*` = through a pin) | group | status)
```
RBM.sum_conv_le | Defs/Convolution:225 | 26 | 401 | - | U4s2:IniTermII:185 | Defs lattice sums | reuse
RBM.sum_radial_pow_le | Defs/RadialSum:192 | 37 | 251 | - | U4s2:IniTermII:164 | Defs lattice sums | reuse
RBM.sum_ball_pow_le | Defs/RadialSum:445 | 5 | 292 | - | U4s2:IniTermI:553 | Defs lattice sums | reuse
RBM.sum_gloop_ward_last_div | Induction/ConArgDet:312 | 32 | 216 | - | U1s1:NewPQ:230 U2:B45:126 U3s3:QLevelsA:99 | Loop, any Hermitian H | reuse
RBM.Ind.norm_sq_gloop_le_symIdx | Induction/Split:444 | 7 | 222 | - | T7:DecayLoopA:352 U2:B45:1126 | Loop, any Hermitian H | reuse
RBM.Ind.loopMax_odd_sq_le | Induction/Split:598 | 32 | 296 | - | U1s2:IterationsA:755 | Loop, any Hermitian H | reuse
RBM.Ind.loopXi_le | Induction/Split:640 | 18 | 430 | - | U1s2:IterationsA:772 | Loop, any Hermitian H | reuse
RBM.Ind.norm_gloop_le_of_le_abs_im | Induction/Split:757 | 7 | 246 | - | T7:DecayLoopA:359 T5s2:GridDriftN:754 U1s2:QGridA:550 U2:B45:1133 U3s2:NQGood1:924 | Loop, any Hermitian H | reuse
RBM.Gauss.Sizes.norm_Lloop_le | Loop/GLoopFlow:700 | 7 | 374 | S | X1b:CltMoments2:795 | Loop, any Hermitian H | reuse
RBM.Gauss.Sizes.ST_pathP_eq_seqP | Induction/Step2Core:400 | 16 | 449 | - | T7:Step2Events:579 U4s3:DuhamelI:1641 U5t:PfStep5:1914 | Gaussian path, any `sz` | reuse
RBM.Gauss.Sizes.ST_whp_grid | Induction/Step2Core:422 | 38 | 549 | - | T7:Step2Events:109 | Gaussian path, any `sz` | reuse
RBM.Path.map_pathH_eq | Path/Walk:598 | 37 | 395 | - | T4s2:GridGoodN:899 U3s2:NQEndFlow:615 U3s3:QEndB1:414 U3s4:QtNonzeroFlow:447 | Gaussian path, any `sz` | reuse
RBM.Path.integrable_normSq_incr | Path/StepDecomp:687 | 4 | 252 | - | T4s2:AzumaProxyN2:748 T5s2:StepDecompN:561 | Gaussian path, any `sz` | reuse
RBM.Path.integrable_normPow4_incr | Path/StepDecomp:693 | 4 | 262 | - | T4s2:AzumaProxyN2:428 T5s2:StepDecompN:991 | Gaussian path, any `sz` | reuse
RBM.Path.integral_normSq_incr_le | Path/StepDecomp:699 | 7 | 449 | - | T4s2:AzumaProxyN2:703 | Gaussian path, any `sz` | reuse
RBM.Path.integral_normPow4_incr_le | Path/StepDecomp:708 | 7 | 550 | - | T4s2:AzumaProxyN2:744 | Gaussian path, any `sz` | reuse
RBM.Path.condExp_linear_eq_zero | Path/Markov:335 | 45 | 492 | - | T5s2:StepDecompN:679 | Gaussian path, any `sz` | reuse
RBM.Path.hasCondSubgaussianMGF_linear | Path/Markov:636 | 44 | 711 | - | T5s2:StepDecompN:894 | Gaussian path, any `sz` | reuse
RBM.Ind.ContinuityNet.cont_core | Induction/ContinuityNet:142 | 74 | 268 | - | U4s3:EtermsMid:1391 | Net (ContinuityNet) | reuse
RBM.Ind.ContinuityNet.cont_highProbAt_good | Induction/ContinuityNet:369 | 7 | 326 | - | U3s2:NQEndFlowLift:900 U3s4:QtNonzeroFlowLift:726 U4s3:DuhamelI:1805 | Net (ContinuityNet) | reuse
RBM.ekPropTInf_holds | Evolution/PropTInf:534 | 30 | 899 | - | U4s1:Step5Kernel:209 U4s2:IniTermI:2202 | E: PropTInf | reuse
RBM.ekSumDecayNonzero_holds | Evolution/Nonzero:146 | 40 | 1490 | - | U3s4:QtNonzero:311 | E: sums and kernel norms | covered
RBM.ekSumDecayNAL_holds | Evolution/SumDecay:420 | 99 | 1953 | - | U3s2:NQGood1:263 | E: sums and kernel norms | covered
RBM.ekSumDecay2_holds | Evolution/SumDecayZero:1411 | 110 | 2834 | - | U3s3:QDriftA:282 | E: sums and kernel norms | covered
RBM.Gauss.Sizes.stek_sumNdecay_holds | Evolution/Prec:215 | 22 | 561 | - | U3s1:Step34Pins:613* | E: sums and kernel norms | covered
RBM.Gauss.Sizes.stek_sumRes1_holds | Evolution/Prec:358 | 30 | 5719 | - | U3s1:Step34Pins:625* | E: sums and kernel norms | covered
RBM.Gauss.Sizes.stek_sumRes2NAL_holds | Evolution/Prec:242 | 113 | 6221 | - | U3s1:Step34Pins:637* | E: sums and kernel norms | covered
RBM.Gauss.Sizes.stek_sumRes2_holds | Evolution/Prec:391 | 28 | 8429 | - | U3s1:Step34Pins:651* | E: sums and kernel norms | covered
RBM.Gauss.Sizes.stek_nonzero_holds | Evolution/Prec:422 | 16 | 5880 | - | U3s1:Step34Pins:666* | E: sums and kernel norms | covered
RBM.norm_uKer_le | Kernel/Evolution:114 | 13 | 363 | - | U4s1:TailtoTail:417 U5t:PfStep5Grid:779 | E: sums and kernel norms | covered
RBM.norm_UN_apply_le | Kernel/Evolution:131 | 23 | 399 | - | U3s2:NQGood1:491 | E: sums and kernel norms | covered
RBM.norm_UN_le | Kernel/Evolution:157 | 6 | 405 | - | U3s4:QtNonzero:290 | E: sums and kernel norms | covered
RBM.Loop.KLbound_holds | Loop/KLFinal:154 | 3 | 16705 | - | U3s2:NQEndFlowLift:477 | K: loops | covered
RBM.Gauss.Sizes.stKbound_holds | Loop/KLFinal:243 | 14 | 16802 | S | T4s2:GridEnvelopeN:113* T5s2:GridDriftN:1027* U3s2:NQEndLin:772* U3s3:QEndGrid:833* U3s4:QtNonzeroEnd:669* | K: loops | covered
RBM.Gauss.Sizes.stKward_holds | Loop/KLFinal:260 | 21 | 17019 | S | U3s1:Step34Pins:229* | K: loops | covered
RBM.Loop.KLPT_holds | Loop/KLFinal:143 | 4 | 6671 | - | U2:KDecay:800 | K: loops | covered
RBM.Loop.KLK_ward | Loop/KLWard:1318 | 12 | 4266 | S | U1s1:NewPQ:640 U2:B45:216 U3s3:QLevelsA:150 | K: loops | covered
RBM.Loop.KLK_rotate | Loop/KLUnique:713 | 10 | 3049 | S | U1s1:NewPQ:639 U2:SEforLn1:132 U4s1:WardII:165 | K: loops | covered
RBM.Loop.KLK_isKLoop | Loop/KLTreeDeriv:1049 | 11 | 2561 | S | T4s2:AzumaProxyN:503 T5s2:HierAlgebra:746 U3s2:NQEndFlowLift:612 | K: loops | covered
RBM.Loop.KLward_two | Loop/KLTree:457 | 31 | 355 | S | U4s1:WardII:167 | K: loops | covered
RBM.Loop.KLIndStepA_Theta_apply_sub | Loop/KLIndStepA:109 | 5 | 213 | - | U2:KDecay:343 | K: loops | covered
RBM.prop5Decay_holds | Propagator/Prop5Hold:784 | 29 | 4296 | - | U3s2:NQGood1:263 U3s3:QDriftA:282 U4s1:Step5Kernel:139 U4s2:IniTermI:2158 X1b:CltMoments1:944 | P: properties 5-8 | covered
RBM.prop5Short_holds | Propagator/Prop5Short:400 | 62 | 600 | - | U3s2:NQGood1:264 U3s3:QDriftA:283 U3s4:QtNonzero:311 U4s2:IniTermI:1237 | P: properties 5-8 | covered
RBM.prop6Diff1_holds | Propagator/Prop6Hold:353 | 27 | 4717 | - | U3s3:QDriftA:283 X1b:CltMoments1:981 | P: properties 5-8 | covered
RBM.prop7Diff2_holds | Propagator/Prop6Hold:384 | 45 | 4944 | - | X1b:MeanFar:1995 | P: properties 5-8 | covered
RBM.prop8ZeroMode_holds | Propagator/Prop5Hold:1266 | 35 | 4900 | - | U3s4:QtNonzero:312 U4s2:IniTermII:1060 | P: properties 5-8 | covered
RBM.Theta_transpose_of_three_le | Propagator/Props4:95 | 3 | 201 | - | T5s2:HierAlgebra:544 U1s1:ZeroModeCalc:307 U4s1:Step5Kernel:513 U4s2:IniTermI:1282 X1b:MeanFar:928 | P: Props4 (explicit Theta) | covered
RBM.Theta_apply_add_right_of_three_le | Propagator/Props4:100 | 3 | 208 | - | U4s1:Step5Kernel:144 U4s2:IniTermI:528 X1b:CltMoments1:926 | P: Props4 (explicit Theta) | covered
RBM.sum_Theta_row_of_three_le | Propagator/Props4:114 | 3 | 211 | - | U1s1:ZeroModeCalc:308 U4s2:IniTermII:983 | P: Props4 (explicit Theta) | covered
RBM.Theta_real_eq | Propagator/Props4:173 | 3 | 207 | - | U4s1:Step5Kernel:119 | P: Props4 (explicit Theta) | covered
RBM.Theta_real_nonneg | Propagator/Props4:177 | 4 | 217 | - | U4s1:Step5Kernel:120 | P: Props4 (explicit Theta) | covered
RBM.norm_Theta_apply_le | Propagator/Props4:188 | 13 | 240 | - | U4s1:TailtoTail:265 U4s3:DuhamelI:591 | P: Props4 (explicit Theta) | covered
RBM.sum_Theta_real_row | Propagator/Props4:203 | 6 | 217 | - | U4s1:Step5Kernel:392 | P: Props4 (explicit Theta) | covered
RBM.sum_norm_Theta_row_le | Propagator/Props4:210 | 5 | 293 | - | U4s1:Step5Kernel:217 U4s2:IniTermI:381 U4s3:DuhamelI:545 | P: Props4 (explicit Theta) | covered
RBM.norm_Theta_le | Propagator/Props4:218 | 13 | 306 | - | T4s2:AzumaProxyN2:561 T5s2:GridDriftN:318 U1s2:QGridA:305 U2:B45:667 U4s2:IniTermI:1640 U4s3:LemDecCalELip:336 U5t:PfStep5Grid:636 | P: Props4 (explicit Theta) | covered
RBM.Theta0_apply_eq | Propagator/Props4:243 | 16 | 227 | - | U4s2:IniTermII:1084 | P: Props4 (explicit Theta) | covered
RBM.Green.gbEXPV3 | Green/GbEXP:806 | 2 | 12963 | - | U4s3:LemDecCalEPrec:654 X1a:FarEntry:700 | G: Green | covered
RBM.Green.stGbEXPij_of_v3 | Green/Pins:1137 | 5 | 651 | - | X1a:FarEntry:700 | G: Green | covered
RBM.Green.v3_premises_of_stFlow | Green/Pins:1049 | 42 | 309 | S | T7:DecayLoopA:994 U1s2:IterationsB:552 U2:B45:2720 U3s2:NQEndFlow:934 U3s3:QEndB1:1807 U3s4:Step3:350 U4s3:DuhamelI:1439 U5t:PfStep5:2133 X1a:FarEntry:693 | G: flow premises | covered
RBM.lemma28_quant | Defs/Semicircle:359 | 19 | 232 | S | U4s1:Step5Kit:387 | G: flow premises | covered
RBM.Green.gijGEXPTSwap_giiGEXPT_of_V3 | Green/Pins:310 | 31 | 323 | S | U4s3:LemDecCalEPrec:657 | G: LemDecCalE input | noreader
RBM.Gauss.Sizes.lwterm_holds | Graph/LWTermHolds:682 | 4 | 36208 | - | T7:Step2Events:1355* | L: Graph pins | covered
RBM.Gauss.Sizes.lwtermExp_holds | Graph/LWTermHolds:1604 | 10 | 43789 | - | T7:Step2Events:1427* T1:Step2Iterate:1793* | L: Graph pins | covered
RBM.Gauss.Sizes.ST_good_engine | Induction/Step2Core:997 | 299 | 1129 | S | T1:Step2Iterate:609 | Step2Core / Step2Scale | producer
RBM.Gauss.Sizes.stScaleExists_holds | Induction/Step2Scale:430 | 128 | 982 | - | T1:Step2Iterate:1395* | Step2Core / Step2Scale | producer
RBM.Ind.stGridMart_holds | Path/DifREP2:2283 | 2 | 21028 | - | T1:Step2Iterate:1394* | DifREP: grid pins | producer
RBM.Ind.stGridMartAt_holds | Path/DifREP2:2288 | 6 | 21027 | - | T1:Step2Iterate:289* | DifREP: grid pins | producer
RBM.Ind.stGridRepN_holds | Path/DifREP3:2381 | 2 | 23181 | - | T1:Step2Iterate:1729* U4s3:DuhamelI:1446 U5t:PfStep5:2170 | DifREP: grid pins | producer
RBM.Ind.difRep_flow_bounds | Path/DifREP1:600 | 32 | 306 | S | U5t:PfStep5:2112 | DifREP: U5 template | u5
RBM.Ind.difRep2_norm_STeeM_le_N | Path/DifREP2:1277 | 29 | 552 | S | U5t:PfStep5:1714 | DifREP: U5 template | u5
RBM.Gauss.Sizes.stNetLift2_holds | Path/NetLift2:688 | 8 | 2165 | - | T1:Step2Iterate:1394* | NetLift | producer
RBM.Path.kellStarEv | Path/KellStar:173 | 106 | 4560 | - | U4s3:LemDecCalEPrec:990 X1a:FarEntry:712 | KellStar | covered
RBM.Path.lemDecCalE_lk | Path/LemDecCalE:786 | 130 | 940 | - | U4s3:LemDecCalEPrec:912 | LemDecCalE* | noreader
RBM.Path.lemDecCalE_dif | Path/LemDecCalEdif2:852 | 8 | 2673 | - | U4s3:LemDecCalEPrec:942 | LemDecCalE* | noreader
RBM.Path.lemDecCalE_wG | Path/LemDecCalEwG:1995 | 123 | 2811 | - | U4s3:LemDecCalEPrec:925 | LemDecCalE* | noreader
RBM.Path.ukerMat_mul | Path/Kernel:77 | 23 | 242 | - | T4s1:GridDuhamelN:117 | Kernel algebra | covered
RBM.Path.condExp_loop_drift | Path/LoopStep:310 | 29 | 2683 | S | T5s2:GridDriftN:824 | LoopStep drift | covered
```
### Narrative
- Method, closure rule, B5b comparison, tables, sizes and the decisions are in the design report; nothing in the probe depends on an unmerged input.
- The probe proves `baKellStarEv` (70 lines) from `baProp5_holds`, `EMn2BA_theta_shift`, `EMn2BA_bparam_le` and a copy of the closing inequality; the consumer theorems are one-line applications.

## (c) Verified Mathlib and project names
Used in the compiled probe (verified by the build above): `Real.rpow_add`, `Real.rpow_one`, `Real.sqrt_eq_rpow`, `Real.add_one_le_exp`, `Real.exp_le_exp`, `Real.exp_add`, `Real.exp_pos`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.rpow_def_of_pos`, `Real.rpow_neg`, `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.rpow_le_rpow_of_exponent_le`, `Real.tendsto_log_atTop`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `div_le_iff₀`, `le_div_iff₀`, `inv_anti₀`, `neg_le_neg_iff`, `exists_congr`, `and_congr_right`, `Finset.sum_congr`, `Finset.sum_range_succ`, `Matrix.mul_apply`, `Filter.Eventually.of_forall`, `eventually_le_rpow` (`Defs/Domination.lean:68`), `Sizes.tendsto_size` (`Defs/StochDomAt.lean:735`), `zdistInf_le_zdistD`, `zdistD_neg`, `ellT_pos`, `etaT_eq_etaOf` (`Loop/GLoopFlow.lean:60`), `mE_im_pos` (`Defs/Semicircle.lean:56`).
Verified absent (`grep` outside `Probe/`): `BAKellStarEv`, `KellFarGen`, `baKellStarEv`, `baGridMart*`, `baNetLift2*`, `baScaleExists*`, `baFlow_premises`, `etaOf_antitone`: 0 hits; no `good_engine` in `Chain/` or `BA/`; `EMn2BA_arith` is `private` (`BA/EMn2BA.lean:597`).
## (d) Open issues and paper-delta candidates
- Candidates (the dispatcher numbers them): `T2452a` registry: `STLemDecCalE` has no reader, `Path/UTransport` is imported by nothing; `T2452b`: at BA the grid martingale pin is derived from the twisted pin, not from `lem:DIfREP` (`7_8:1994`); `T2452c`: `BAKellStarEv` is a Lean statement the paper does not make (`(prop:ThfadC)` at the far scale).
- Open: the identities H1-H3 of row P1 (observable loop part, drift, QV) are not proved; the same-charge pairs were not compiled for the loop part. P1 needs a 1a design gate; fallback P1G (design report D5).
- Open: X1a's 1a should choose the K-level far field (`emn2ExpHK`, merged `baEMn2ExpHK`) for the generic `FarEntry`; if it chooses the Theta level it needs `BAKellStarEv` and the `ΘM` decay too.
- Open: the amend `private` deletion at `BA/EMn2BA.lean:597` (§153 (1)) and the `private` moduli of `BA/TwistLoop` (P2) are recommendations, not done here.
