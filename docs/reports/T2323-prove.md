Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 09:18:52 UTC 2026

Source: RBM2D `Universality/GUEPhase/Proc.lean:862-1424` (file last changed at `81fca44`; `git log -1` of the file). Target `gueKproc_detDom` = check section 2 (`docs/tickets/checks/T2323-check.lean`). Notation: `x = 1 - t₁`, `g = sz.lam n`, `N = sz.size n = (W L)^d`, `η = etaT E t = (1-t) Im m`, `Bctl = W^{-d}((g²+x)⁻¹ + (L^d x)⁻¹)` (`Defs/Sizes.lean:214`, `Bparam` at `K = 0`: `((0+1)^{d-2})⁻¹ = 1`).

### (i) Exponent table (the `d ≥ 3` table; token table of `:862-1424` first)

| RBM2D token (line) | `d ≥ 3` replacement | dimension-sensitive? |
|---|---|---|
| `Proc_lam_near_le` (:869), `Proc_gueTent_sum_le_two` (:891), `Proc_inv_le_two_inv_of_le_two_mul` | none (real analysis, tents) | no |
| `Proc_gueKbar_mono` (:957), `Proc_gueTime_mem_Icc` (:969), `Proc_gueTime_kstar_near` (:980), `Proc_gueKbar_le_of_hbase` (:1040) | `Z2 (d.L n)` ↦ `Zd d (sz.L n)`, `d` ↦ `sz`, `LoopIdx` ↦ `RBM.Loop.LoopIdx`; uses the merged *private* `Proc_gueTent_nonneg` (Proc.lean:132), `Proc_le_ciSup_finite_aux` (:390), `Proc_gridTime_mono` (:761): copy under `ProcK_` | no |
| `Proc_size_pos`, `Proc_one_le_size` | `d.size n` ↦ `sz.size n = (W L)^d`; positivity from `W_pos`, `three_le_L` | no |
| `Proc_etaT_nonneg/anti`, `Proc_gueScale_pos` | `spectralM` ↦ `mE`; `(mE E).im = √(4-E²)/2` (`Defs/Semicircle.lean:42`) | no |
| `Proc_ofFn_getD`, `Proc_loopOf_eq` (:1120) | `KLoop.loopOf L σ a` ↦ `RBM.Gauss.loopOf σ a` on `Zd d L` (`List.ofFn`, `GLoopFlow.lean:117`) | no |
| `Proc_initial` (:1133) | **the adaptation**: `Kbound_prec_uncond`/`kloop_Mt_eq`/`scaleM`/`ellT_eq_L` replaced by `hKb : sz.STKbound E` at `τ = t₁` + `hell` (row 4 below) | **yes** |
| `Proc_hbase` (:1175) | `eq736 (d.L n) (d.W n)` ↦ `eq736 d (sz.L n) (sz.W n)`; `hsmall`: `(((W L)^2 : ℕ):ℝ) = d.size n` (`rfl`) ↦ `(((W L)^d : ℕ):ℝ) = sz.size n` (`rfl`); the three thresholds are `N`-power statements | no |
| `gueKproc_detDom` (:1247) | `primRhsGUE (d.L n) (d.W n)` ↦ `primRhsGUE d (sz.L n) (sz.W n)`; `gueGridK d n0` ↦ `gueGridK sz n0`; `hell` and `hKinit` per check §2; `hscale` unused (as RBM2D); `hKb` new | via `hell` only |

| # | exponent / threshold / constant | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | `hinit` of `eq736` (`Bootstrap.lean:442`): `A` | `A = N^{τ'}`, `τ' = min(τ,τ_U)/2` | `‖Kt t₁ I‖ ≤ A (Nη_{t₁})^{-(\|I\|-1)}`, `2 ≤ \|I\| ≤ 2n₀` | from `hKb` at `τ = t₁ ∈ [0,1)` (`ht1`, `ht10`, `ht0`), `k = \|I\|`, each `k ∈ [2,2n₀]` (finite intersection); `‖K‖ ≤ N^{τ'/2} Bctl^{k-1}` |
| 2 | `≺` of a deterministic left side | `P(univ)=1 > N^{-1}` | for `N ≥ 2` the bad event is `∅`: "∀ε, ∀ᶠ n, ‖STKloop‖ ≤ N^ε Bctl^{k-1}" (needs `Tendsto size`; `hKb` at the one sequence `t₁`, no sup over `w`) | `N^{-1} ≤ 1/2` |
| 3 | `Bctl → (Nη)⁻¹` factor | `Bctl(t₁) ≤ 2 (N η_{t₁})⁻¹` | **`L^d x ≤ g²`** (`hell`) ⟹ `g²+x ≥ L^d x` ⟹ `(g²+x)⁻¹ ≤ (L^d x)⁻¹`, so `Bctl ≤ 2 W^{-d}(L^d x)⁻¹ = 2 (N x)⁻¹ ≤ 2 (N x Im m)⁻¹` (`0 < Im m ≤ 1`: `\|E\| ≤ 2-κ`) | constant `2` exactly (toy: `55/224` vs `1/4`); `2^{k-1} ≤ 2^{2n₀} ≤ N^{τ'/2}` eventually |
| 4 | `hell` | `L^d (1-t₁) ≤ g²` (∀ᶠ n) | necessary at order `L^{d-2}`: with only `L² x ≤ g² < L^d x` the ratio `Bctl/(Nη)⁻¹ ≈ L^{d-2}` (script iv-b), not absorbed by `N^ε` (ticket §141) | `L^d x ≤ g²` implies `L² x ≤ g²` (`L ≥ 1`, `d ≥ 2`): one hypothesis serves both `hell` here and the `ellT_eq_L`-form `hell` of T2322 |
| 5 | grid size `K` | `gueGridK sz n₀ n = (N+1)^{32n₀+64}` (`Grid.lean:106`) | `K ≠ 0`; `gridStep ≤ η_{t₀}` from `h730`, `N^{-τ_U} ≤ 1`, `K ≥ 1` | proof device only, never a hypothesis witness |
| 6 | `h730`, `τ_U` | `t₀-t₁ ≤ N^{-τ_U} η_{t₀}` | gives `hsmall`: `N(u-t₁) ≤ N^{-τ_U} Nη_u` (`η` antitone) and `4n₀³·N^{τ'}N^{-τ_U} < 1` (`eventually_small`, `τ' < τ_U`) | `τ'/τ_U ≤ 1/2` |
| 7 | `lam_near` constant | `Nη_u ≤ 2 Nη_{u'}` for `\|u-u'\| ≤ Δ ≤ η_{t₀}`, `u' ≤ t₀` | `NΔ ≤ N(1-t₀) Im m`, `Im m ≤ 1` | factor `2` (RBM2D `Proc_lam_near_le`) |
| 8 | output exponent | `τ/2 + τ/2` | `2^{2n₀+1} ≤ N^{τ/2}` eventually (`eventually_le_rpow`); `2 ≤ m ≤ 2n₀` | `N^{τ/2}/2^{2n₀+1} → ∞` |
| 9 | §29 (1) time domain | `0 ≤ t₁ ≤ t₀ < 1` | `STKbound` needs `τ n ∈ [0,1)`; `eq736` needs `t₁ ≤ t₀`; `etaT_pos` needs `t < 1` | all in the hypotheses |
| 10 | §29 (2) boundary `1 - g²/L²` | not used | `hell` + `0 ≤ t₁` give `x ≤ min(1, g²/L^d)`; if `g > L^{d/2}` then `x ≤ 1` is the binding constraint; `Bctl` only needs `x > 0` (`t₁ < 1`) | none needed |
| 11 | §29 (3) `L`-`W` relation | not used | the target has no `L^d ≤ W^K` hypothesis and the proof uses none (only `Tendsto size`) | n/a |
| 12 | §29 (4) `∀ n` vs `∀ᶠ n` | `hell`, `h730`, `hscale`: `∀ᶠ`; `ht*`, `hE`, `hKinit`, `hK`: `∀ n` | `hKinit`/`hK` identify/define the family `Kt`; no condition at finitely many `n` is forced on a size statement | none needed |

### (ii) One concrete nondegenerate instance

Hypotheses of `gueKproc_detDom` at: `d = 3`, `sz0` (`SizesInst`, `Defs/Sizes.lean:257`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, so `N = 2^21 (n+1)^18 → ∞`), `κ = 1/10`, `E n = 0` (`Im m = 1`), `τ_U = 1/1000 ≤ ouTauMax(1/6,1/10) = 1/720` (`ZeroModeProfile.lean:779`), `n₀ = 2`, `1-t₀ = N^{-1+2τ_U}` (the `η_LL` scale of `ouEtaLL`, `ZeroModeProfile.lean:81`), `t₀ - t₁ = N^{-τ_U}(1-t₀)/2`. `hKb`, `hKinit`, `hK` stay hypotheses (owed pin KL7 / the Duhamel family; `STKbound` registered). Command:

`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2323/pre.py`

```
== (iv-a) ratio Bctl/(2 (N eta)^-1), L^d x <= g^2 (expect <= 1 i.e. Bctl <= 2(N eta)^-1)
max ratio = 0.999999995 (<=1 everywhere)           [L in {3,10,100}, d in {3,4}, g in {0.1,1}, L^d x/g^2 in {1,.5,1e-3,1e-6}, Im m in {1,.3}; assert passed]
== (iv-b) control: L^2 x <= g^2 < L^d x ; ratio Bctl/(N eta)^-1 (Im m=1) grows with L
d=3 g=0.1: ratio at L=3,10,100 = [3.7, 10.901, 100.99] ; L^(d-2)= [3, 10, 100]
d=3 g=1.0: ratio at L=3,10,100 = [3.7, 10.901, 100.99] ; L^(d-2)= [3, 10, 100]
d=4 g=0.1: ratio at L=3,10,100 = [9.1, 100.01, 10000.0] ; L^(d-2)= [9, 100, 10000]
d=4 g=1.0: ratio at L=3,10,100 = [9.1, 100.01, 10000.0] ; L^(d-2)= [9, 100, 10000]
== (iv-c) toy instance d=3,L=3,W=2,g=1,1-t1=1/27
N= 216 L^d x= 1 <= g^2=1: True Bctl= 55/224 0.24553571428571427 2/(N eta)= 1/4 0.25 Bctl<=: True
== (ii) sequence sz0 (x=1-t): L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6, d=3, E=0 (Im m=1), kappa=1/10, tauU=1/1000
ouTauMax(1/6,1/10)=min(min(1/12*1/6,1/6*1/10/12),1/100)= 0.001388888888888889  tauU<=it: True
n=     0 logN=   14.56 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=1.921e-01) Bctl<=2/(N eta):True
n=     1 logN=   27.03 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=2.452e-02) Bctl<=2/(N eta):True
n=     2 logN=   34.33 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=7.354e-03) Bctl<=2/(N eta):True
n=     5 logN=   46.81 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=9.387e-04) Bctl<=2/(N eta):True
n=    10 logN=   57.72 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=1.552e-04) Bctl<=2/(N eta):True
n=   100 logN=   97.63 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=2.144e-07) Bctl<=2/(N eta):True
n= 10000 logN=  180.34 dom(0<x0<=x1<=1):True h730:True hscale:True hell:True (L^3(1-t1)/lam^2=2.541e-13) Bctl<=2/(N eta):True
all ok: True
== (ii-ext) STKbound k=2 limit check: max_ab t*Theta_ab(t) vs (g^2+x)^-1+(L^d x)^-1, d=3, S^(B)(g)
L=3 g=0.1: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 0.9999
L=3 g=1.0: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 1.0990
L=4 g=0.1: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 0.9999
L=4 g=1.0: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 1.1733
L=5 g=0.1: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 0.9999
L=5 g=1.0: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 1.2171
L=6 g=0.1: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 0.9999
L=6 g=1.0: max_ab t*Theta/B over L^3x/g^2 in (1,1e-2,1e-4): 1.2461
```

Reading: (iv-a) `hell` ⟹ `Bctl ≤ 2(Nη)⁻¹` (expected); (iv-b) with only `L² x ≤ g²` the ratio is `≈ L^{d-2}` (unbounded in `L`, as expected). The toy `d=3, L=3, W=2, g=1, 1-t₁=1/27` is the ticket's instance (`hell` with equality). The sequence rows exhibit every deterministic hypothesis at once (`hE`, `ht1`, `ht10`, `ht0` via `dom`, `h730`, `hscale`, `hell`, `Tendsto size`) at every sampled `n`; `N` is not astronomical at `n = 0` (`N = 2097152`). `hscale` holds as `(Nη_{t₀})⁻¹ = N^{-2τ_U} ≤ N^{-τ_U}`.

External hypothesis `hKb` (`STKbound`, owed, KL7), concrete limit computation: the leading term of `K^{(2)}` is `t·Θ_ab(t)/W^d` (`profPMTilde` form, `ZeroModeProfile.lean`), and `max_ab tΘ_ab(t) / ((g²+x)⁻¹ + (L^d x)⁻¹)` stays ≤ 1.25 for `L ≤ 6`, `d = 3` (script ii-ext; `Θ = (1 - tS^{(B)}(g))⁻¹`, `S^{(B)}` rows sum to 1), i.e. `‖K^{(2)}‖ ≲ Bctl`, matching `STKbound` at `k = 2`. This is a sanity check at the leading term only, not a proof of `STKbound`.

**`hell` against the consumer's `t₁` (ticket (ii)).** Grid.lean:558 (`t₁ = (1-ζ(τ)) t₀`, `ζ = 1 - e^{-τ}`, `τ ≤ ouTStar = N^{-1+τ_U}`, `Pins.lean:142`) gives `1-t₁ ≤ (1-t₀) + N^{-1+τ_U}`. At `η_LL`: `1-t₀ = η/(Im m + η) ≤ η/Im m` (`1_2:789`), so `L^d x ≤ C N^{2τ_U} W^{-d}` with `C ≤ 1/Im m + 1`, and `Im m ≥ √(4κ-κ²)/2` (`mE_im`, `|E| ≤ 2-κ`). `Admissible`: `lam² ≥ W^{-d+2𝔡}` (`WO`, `Defs/Sizes.lean:164`), `N^{2τ_U} ≤ W^{2τ_U/𝔠} ≤ W^{𝔡/6}` (`Bandwidth`, `τ_U ≤ 𝔠𝔡/12` = `ouTauMax` branch). Hence `L^d x/g² ≤ C W^{-(2𝔡 - 𝔡/6)}` = `C W^{-11𝔡/6} → 0`; numbers (`𝔡 = 1/10`, `τ_U = 1/1000`): `W^{-0.188}`. At the QUE scale `η_Q = W^{-𝔡/3} g W^{d/2}/N` (`ZeroModeProfile.lean:84`): `L^d η_Q = g W^{-d/2-𝔡/3} ≤ g²` iff `g ≥ W^{-d/2-𝔡/3}`, true from `WO` with slack `W^{4𝔡/3}`. So the consumers' `t₁` satisfies `hell` eventually (the regime is the zero-mode regime `1 - t ≲ g²/L^d`, i.e. `η ≲ g² L^{-d}`, as for RBM2D).

**Finding F1 (instance data).** The `Grid.lean` §`GridCheck` times (`t₀ = 9/10`, `t₁ = e^{-1/20}·9/10`, `Grid.lean:792-799`) are *not* in the zero-mode regime: `1-t₁ = 0.14389`, `L^3(1-t₁) = 9.209` vs `g² = (1/64)² = 2.44e-4` at `n = 0` (`python3 -c`, run above: `0.14389351794935734 9.20918514875887 0.000244140625`); since `L^3 ≥ 64` and `g² ≤ 2.44e-4` for all `n`, `hell` fails at every `n`. The `ProcKInst` instance of `gueKproc_detDom` must therefore use the `t₁`, `t₀` of (ii) (`1-t₀ = N^{-1+2τ_U}`), keeping the `GridCheck` sizes `sz0` only. Paper-delta candidate: none (instance data, not a statement difference). Paper-delta candidate `T2323a`: `hell` reads `L^d(1-t₁) ≤ ilambda²` (RBM2D `L²(1-t₁) ≤ 1`, the `d=2`, `ilambda=1` case); `hKb : sz.STKbound E` new hypothesis (as T2153a; RBM2D proves `Kbound_prec_uncond` unconditionally); `hKinit` only for `loopOf σ a` (RBM2D: all `I`).

**§29 (one line each).** (1) `0 ≤ t₁ ≤ t₀ < 1` are hypotheses; (2) `1 - g²/L²` not used, `hell` is the only boundary and `0 ≤ t₁` caps `x ≤ 1`; (3) no `L^d ≤ W^K` used by the proof; (4) `∀ᶠ` for `hell`, `h730`, `hscale`, `∀ n` only for sequence-level identification (`hKinit`, `hK`) and bounds on `E, t`.

### Verdict

- `gueKproc_detDom`: **PASS** — every hypothesis holds at one nondegenerate instance (script ii, `n = 0..10000`); the exponent table closes (rows 1-8); `hell` (`L^d(1-t₁) ≤ g²`) is necessary and sufficient for the `Bctl ≤ 2(Nη)⁻¹` step and holds at the consumers' `t₁` with slack `W^{11𝔡/6}`; the only external hypothesis (`hKb`) passes the leading-term limit check. Instance caveat F1: do not use `GridCheck` `t₁, t₀`.

## (b) Script output (stage 1b, `prover-hard` role run as claude-sonnet-5-5; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2323`, branch `t/T2323`, commit `c05626e`)

Script `mkreport.sh` (scratchpad), output verbatim (the `$ ` lines are the commands):

```
$ date -u
Thu Oct  8 09:31:48 UTC 2026

$ git log --oneline -2; git diff --stat main...t/T2323
c05626e T2323: UN-31b GUEPhase/ProcK (gueKproc_detDom, d >= 3 port of RBM2D Proc.lean:862-1424)
f38bffa Dispatcher V1: T2323-check fix (STBctl_pos not imported), H126
 RBM3D/Universality/GUEPhase/ProcK.lean | 963 +++++++++++++++++++++++++++++++++
 1 file changed, 963 insertions(+)

$ lake build RBM3D.Universality.GUEPhase.ProcK 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3757 jobs).

$ lake env lean RBM3D/Universality/GUEPhase/ProcK.lean   (warnings and errors)
exit=0

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/ProcK.lean  (hygiene)
grep-exit=1 (1 = no hit)

$ lake env lean axioms.lean  (#print axioms of every public declaration)
'RBM.Univ.GUEPhase.gueKproc_detDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ProcKInst.szToy' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ProcKInst.szToy_Bctl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ProcKInst.szToy_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ProcKInst.szToy_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0

$ registry pre-check: lake env lean registry.lean  (import RBM3D, import ...ProcK, #assert_rbm_axioms; temporary, uncommitted)
import RBM3D
import RBM3D.Universality.GUEPhase.ProcK
#assert_rbm_axioms
exit=0
0
 RBM.Gauss.Sizes.STOeqNQ'].
non-vacuity certificates: 0 of 138 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/In

$ lake build   (full library; ProcK is not yet a root import, the hub adds it at merge)
Build completed successfully (4132 jobs).

$ check-file equality: eq_check.lean = check imports + import ProcK + example (...) := @gueKproc_detDom
11:import RBM3D.Universality.GUEPhase.Proc
12:import RBM3D.Induction.Defs
13:import RBM3D.Universality.GUEPhase.ProcK
76:example : RBM.Univ.GUEPhase.T2323Check.T2323_gueKproc_detDom := @RBM.Univ.GUEPhase.gueKproc_detDom
exit=0
0

$ target statement, extracted from the file
theorem gueKproc_detDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n : ℕ in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (m : Set.Icc 2 (2 * n0)),
      gueKproc sz t1 t0 (gueGridK sz n0) Kt n (m : ℕ) (t : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale sz E n (t : ℝ))⁻¹ ^ ((m : ℕ) - 1) := by

$ compiled nonempty instance of gueKproc_detDom, extracted from the file
example (hKb : sz0.STKbound (fun _ => (0 : ℝ)))
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd 3 (sz0.L n)),
      Kt n (t1 n) (loopOf σ a) = sz0.STKloop n 0 (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd 3 (sz0.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * 2 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (m : Set.Icc 2 (2 * 2)),
      gueKproc sz0 t1 t0 (gueGridK sz0 2) Kt n (m : ℕ) (t : ℝ) ≤
        ((sz0.size n : ℕ) : ℝ) ^ ε * (gueScale sz0 (fun _ => (0 : ℝ)) n (t : ℝ))⁻¹ ^ ((m : ℕ) - 1) :=
  gueKproc_detDom sz0 (κ := 1 / 10) (τU := 1 / 1000) (by norm_num) (by norm_num) 2
    (E := fun _ => (0 : ℝ)) (t1 := t1) (t0 := t0)
    (fun n => by norm_num) t1_nonneg t1_le_t0 t0_lt_one
    (Sizes.tendsto_size sz0 sz0_tendsto)
    (Filter.Eventually.of_forall h730_at) (Filter.Eventually.of_forall hscale_at)
    (Filter.Eventually.of_forall hell_at) hKb Kt hKinit hK

$ name-clash grep (RBM3D outside Probe/ and outside ProcK.lean)
-- gueKproc_detDom
RBM3D/Universality/GUEPhase/Proc.lean:19:`gueKproc_detDom`, is T2323 = UN-31b).  Paper: the GUE phase of Thm 2.4
-- ProcKInst
-- szToy
-- szToy_Bctl
-- szToy_scale
-- szToy_conv
-- ProcK_

$ port source and RBM2D/RBM1D diff-stat
RBM2D last change of Proc.lean: 81fca44
RBM2D HEAD: 9e0f275
diff-stat-exit=0
RBM1D: no port

$ residual d=2 tokens in ProcK.lean (Z2, KLoop., spectralM, d.size, Kcal, Kbound_prec_uncond), (docstring mentions only expected)
23:`KLoop.Kbound_prec_uncond` and converts `KLoop.Mt` into `gueScale` (`kloop_Mt_eq`, `scaleM`,
33:(`Z2 L ↦ Zd d L`, `d.size ↦ sz.size`, `LoopIdx ↦ RBM.Loop.LoopIdx`, `spectralM ↦ mE`).
411:`:1133`, from `Kbound_prec_uncond`.) -/
residual-exit=0

$ line counts
     963 RBM3D/Universality/GUEPhase/ProcK.lean

$ python3 -c ... GridCheck t1: 1-t1, L^3(1-t1), lam^2 at n=0 (F1 of (a))
0.14389351794935734 9.20918514875887 0.000244140625
```

### Narrative (stage 1b)

- New file `RBM3D/Universality/GUEPhase/ProcK.lean`, 963 lines, only file in `git diff --stat main...t/T2323`; no root import (the hub adds it at merge, so the full `lake build` above does not contain it; the registry pre-check does).
- Port of RBM2D `Universality/GUEPhase/Proc.lean:862-1424` (last changed at `81fca44`; unchanged between `81fca44` and RBM2D HEAD `9e0f275`, diff-stat above empty). Sections `KprocDom` (`:862-1075`) and `KprocInput` (`:1077-1422`) ported with the renames `Proc_`↦`ProcK_`, `Z2 (d.L n)`↦`Zd d (sz.L n)`, `d.size`↦`sz.size`, `LoopIdx`↦`RBM.Loop.LoopIdx`, `spectralM`↦`mE`, `gueKbar d`↦`gueKbar sz`, `eq736 (d.L n)`↦`eq736 d (sz.L n)`, `(W L)^2`↦`(W L)^d` in `hsmall`. The theorem `gueKproc_detDom` has the check-file §2 statement (equality `example` exits 0; all binders in check order).
- Three merged privates are re-declared locally (they are `private` in `Proc.lean`): `Proc_gueTent_nonneg` (`Proc.lean:132`), `Proc_le_ciSup_finite_aux` (`:390`), `Proc_gridTime_mono` (`:761`), as `ProcK_gueTent_nonneg`, `ProcK_le_ciSup_finite_aux`, `ProcK_gridTime_mono`. `ProcK_loopOf_eq`, `ProcK_ofFn_getD` are copies of RBM2D `Proc_loopOf_eq` and (read from) the merged private `gdn_loopOf_eq` (`Induction/GridDriftN.lean:936`).
- The one adaptation (ticket §141), the `Proc_initial` row of the token table and rows 3-4 of the exponent table in (a): `Proc_initial` is replaced by `ProcK_initial`, which uses (1) `ProcK_stKbound_eventually`, the single-time form of `STKbound` (`≺` of a deterministic left side: the bad event of `StochDomAt` at `D = 1` has measure `≤ N^{-1} < 1 = P(univ)` once `N ≥ 2`, so no sample point is bad; same argument as the merged private `gdn_STKbound_win`, `GridDriftN.lean:1027`, without the supremum over `w`); (2) `hKinit` at `loopOf σ a` with `ProcK_loopOf_eq`; (3) `ProcK_Bctl_le`: `L^d (1 - t) ≤ ilambda²` gives `Bctl n t ≤ 2 (N η_t)⁻¹` (`(ilambda²+x)⁻¹ ≤ (L^d x)⁻¹`, `W^{-d}(L^d x)⁻¹ = (N x)⁻¹`, `η ≤ x` since `Im m ≤ 1`); (4) `2^{|I|-1} ≤ 2^{2 n₀} ≤ N^{τ'/2}` eventually, so `N^{τ'/2} · N^{τ'/2} = N^{τ'}`. `ellT_eq_L`, `kloop_Mt_eq`, `scaleM`, `Sizes.size_eq`, `Kbound_prec_uncond` are not used.
- `hscale` is unused in the proof (as RBM2D, `have _hs := hscale`) and kept in the statement. `hKb`, `hKinit`, `hK`, `hell`, `h730`, `hscale` are hypotheses of the theorem; the theorem is conditional on the owed pin `STKbound` (KL7) and on `hell`; it is not the unconditional RBM2D statement.
- `import RBM3D.Induction.Defs` is dropped: `lake env lean` of the file without that line exits 0 (it is transitive through `Proc`). The check-equality scratch keeps the check's own imports.
- Instances (namespace `ProcKInst`): (i) `szToy_conv` and the `example` applying `ProcK_Bctl_le` at `d = 3`, `L = 3`, `W = 2`, `ilambda = 1`, `1 - t₁ = 1/27` (`hell` with equality), `E = 0`: `Bctl = 55/224 ≤ 1/4 = 2/(N η)`, `N η = 8` by `norm_num`. (ii) `gueKproc_detDom` applied at the merged `Grid.lean`/`SizesInst.sz0` sizes (`d = 3`, `N = 2^21 (n+1)^18`), `κ = 1/10`, `E = 0`, `τ_U = 1/1000`, `n₀ = 2`, `1 - t₀ = N^{1/500}/N`, `t₀ - t₁ = N^{-τ_U}(1 - t₀)/2` at every `n`; `hE`, `ht1`, `ht10`, `ht0`, `hsz` (`Sizes.tendsto_size sz0 sz0_tendsto`), `h730`, `hscale`, `hell` are proved for every `n` (private lemmas `ProcKInst.*_at`, from `N^{1/500} ≤ 4 (n+1)^3`); `hKb`, `hKinit`, `hK` remain hypotheses of the example. A second `example` shows `0 < t₁ n < t₀ n < 1` for every `n` (a genuine window).
- Finding F1 of (a) confirmed (last script block): at the `GridCheck` times `t₀ = 9/10`, `t₁ = e^{-1/20}·9/10`, `1 - t₁ = 0.1439`, `L^3 (1 - t₁) = 9.209` at `n = 0` against `ilambda² = 2.44e-4`; `hell` fails, so the instance shares only the `GridCheck` sizes, as (a) prescribed. No correction to (a) was needed; no (a′).
- Not shown here: that a family `Kt` satisfying `hKinit` and `hK` exists at the instance data (e.g. `Kt n t I = KLK … I`), and `STKbound` itself (owed, KL7).

## (c) Verified Mathlib and RBM3D names used (`#check` run in `names.lean`, scratchpad, exit 0)

- `Real.rpow_le_rpow_of_exponent_le : 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z`
- `Real.rpow_le_one_of_one_le_of_nonpos : 1 ≤ x → z ≤ 0 → x ^ z ≤ 1`
- `Real.pow_rpow_inv_natCast : 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x`
- `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_le_rpow`, `Real.rpow_add`, `Real.sqrt_sq`, `Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2`
- `ENNReal.one_le_ofReal : 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p`; `MeasureTheory.measure_univ`, `MeasureTheory.measure_mono`
- `Filter.eventually_all_finset`; `Complex.abs_im_le_norm : |z.im| ≤ ‖z‖`; `Finset.single_le_sum`
- `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `inv_anti₀`, `div_le_div_iff₀`, `div_le_div_of_nonneg_right`
- RBM3D: `RBM.Gauss.Sizes.tendsto_size`, `RBM.Gauss.SizesInst.sz0_tendsto`, `RBM.mE_im`, `RBM.norm_mE`, `RBM.Gauss.etaT_pos`, `RBM.eventually_le_rpow`, `RBM.Univ.GUEPhase.eventually_small`, `RBM.Univ.GUEPhase.eq736`
- Names verified absent as declarations in RBM3D (not used), by
  `grep -rnE "(theorem|lemma|def|abbrev) +(\S+\.)?(Kbound_prec_uncond|kloop_Mt_eq|scaleM|size_eq)\b" RBM3D --include='*.lean' | grep -v "^RBM3D/Probe/"`:
  only hit `RBM3D/Universality/GUEPhase/ProcK.lean:789: private theorem size_eq` (the private instance lemma `ProcKInst.size_eq` of this file); `Kbound_prec_uncond`, `kloop_Mt_eq`, `scaleM`, `Sizes.size_eq` do not exist.
- `grep -n "ProcK" RBM3D.lean`: no hit (exit 1), so the full `lake build` above does not contain `ProcK`.

## (d) Open issues and paper-delta candidates

- **T2323a** (statement differences to RBM2D `gueKproc_detDom`): (1) `hell : ∀ᶠ n, L^d (1 - t₁) ≤ ilambda²` for RBM2D's `L² (1 - t₁) ≤ 1` (the `d = 2`, `ilambda = 1` case; the literal `ℓ_{t₁} = L` condition `L² (1 - t₁) ≤ ilambda²` loses `L^{d-2}`, script iv-b of (a)); (2) the new hypothesis `hKb : sz.STKbound E` (as T2153a; RBM2D proves `Kbound_prec_uncond` unconditionally); (3) `hKinit` identifies `Kt n t₁` with `STKloop` only on `loopOf σ a` (RBM2D: every `I`).
- **T2323b** (instance data, not a statement difference): the `GridCheck` times `t₀ = 9/10`, `t₁ = e^{-1/20}·9/10` violate `hell` at every `n`; consumers' `t₁` (UN-33…UN-52) must come from the zero-mode regime `1 - t₁ ≲ ilambda²/L^d`, which the consumers' `t₁` of `Grid.lean:558` satisfies eventually (argument in (a)).
- Downstream owes: discharge of `hKb` (`stKbound_of_flow`, `Loop/KLFinal.lean:302`, under the flow) and of `hell` (UN-33…UN-52).
- No blueprint, registry or other-file change; the root import `import RBM3D.Universality.GUEPhase.ProcK` after the last `import` line of `RBM3D.lean` is for the hub.
