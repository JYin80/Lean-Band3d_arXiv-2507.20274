Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 20:31:34 UTC 2026 (preflight 1a; sources: ticket, check file, RBM2D `c9a24cf:BootstrapAt.lean`, merged `Bootstrap.lean`)

Notation: `s = size N`, `x = (Nf·η_t)⁻¹`, `p = s^{τ'}`, `q = s^{-τU}`, `ρ(n₀) = 1/(36(20n₀+48))`.
No external hypothesis occurs (class G: `P`, `size`, `Nf` abstract; the only limits are `∀ᶠ N` along `size → ∞`).

### (i) Exponent table

| row | value | constraint | slack |
|---|---|---|---|
| τ' (targets 5, 6) | `min(τ,τU)/16` | `τ' < τ`; `3τ' − τU < 0` | `τ−τ' ≥ 15τ/16`; `3τ'−τU ≤ −13τU/16` (script asserts both strict inequalities for `τ ∈ {.01,.5,1,7}`, `τU ∈ {.1,.05,1}`) |
| τ' (target 4) | `min(τ,τU)/2` | `τ' < τ`; `τ' < τU` (`eventually_small`) | `τ−τ' ≥ τ/2`; `τU−τ' ≥ τU/2` |
| `p³q ≤ ρ(n₀)` (targets 5, 6) | `p³q = s^{3τ'−τU} ≤ s^{−13τU/16}` | `≤ ρ(n₀)` | holds for `s ≥ ρ(n₀)^{−16/(13τU)}` (table (vi)) |
| `cond728G` (`M=Φ=p, M'=3p, ε=δ=q`) | `p(qn₀(1+3p)3p + 1 + 3qp² + √(qp)) < 3p` | `S₇₂₈ := qn₀(1+3p)3p+1+3qp²+√(qp) < 2` | max `S₇₂₈` on grid `1.0263` (n₀=1,p=1,q=ρ): slack `2−S = 0.9737` |
| `gEven_cond727G` (`A=Φ=p, M=3p`) | `p + p·S₇₂₇ < 3p`, `S₇₂₇ = qn₀(1+4p)4p+q+9qp²+3√q p` | `S₇₂₇ < 2` | max `S₇₂₇ = 0.0780` (n₀=0,p=1,q=ρ): slack `1.922` |
| `hε` of `eq736` (target 4) | `4n²·n·A·ε = 4n³ s^{τ'−τU}` | `< 1` | `s^{τU−τ'} ≥ 8n³+1` (`eventually_small`) ⟸ `s ≥ (8n³+1)^{2/τU}`; true threshold is `(4n³)^{1/(τU−τ')}` |
| `2 ≤ s^{τ−τ'}` (target 4) | `2A ≤ s^{τ−τ'}A` | | `s ≥ 2^{2/τ}` |
| `3p ≤ s^τ` (targets 5, 6) | `s^{τ−τ'} ≥ 3` | | `s ≥ 3^{16/(15τ)}` |
| `1 ≤ p`, `q ≤ 1`, `x ≤ 1` | `s ≥ 1`, `τ' > 0`, `τU > 0`; `x ≤ δ = q ≤ 1` (`hscale`) | | `s ≥ 1` |
| (7.30) scale in target 4 | `(W L)^d (t−t₁) ≤ s^{−τU} lam_t` | with `lam = s·η_t`, `s = (W L)^d` ⟺ `t−t₁ ≤ s^{−τU} η_t` (h730 of targets 5, 6) | exact equivalence (below) |
| window | `[t₁N, t₀N]`, `t₁ ≤ t₀` | `0 < η`, `0 < lam`, `0 < Nf` hypotheses; no `t<1` | none used |
| `3 ≤ d` | not used | `eq736 d L W` (merged `Bootstrap.lean:442`) has no `hd`; `(W L)^d` enters only as a ℕ-cast in (7.30) | — |
| `n₀` parity | `Even n₀` only in `eq727GEAt`; consumer uses `2n₀` | `hodd` indices `2l+2 ≤ n₀` | odd step `(2k+1)+(2k+3) = 2(2k+2)` (script) |
| `d`-token count | in `c9a24cf:BootstrapAt.lean` `Z2`, `LoopSet`, `primRhsGUE`, lattice `^ 2`: only `:564-581` (`eq736_detDomAt`) and its instance | other `^ 2`: martingale variance `N⁻¹η⁻²` (`:148-176`, `:427-447`), `(x^m)^2`/`(M s^{2k+2})^2` (`:166-171`, `:271-279`), scalars of the cond lemmas (`:209-230`, `:491-512`, `(1/6)^2`) | `d`-free |
| pathwise exponents | `728`: line1 `m(1+M')M' x^{m+1}·εx⁻¹ = x^m`; line3 `D₁L_{m+1} ≤ M'M x^{m+1} → x^m`; line4 `√(εx)√(Mx^{2m−1}) = √(εM)x^m`; `727`: line1 `x^m·εx⁻¹ → x^{m−1}`, line3 `L₂L_m ≤ M²x^m → x^{m−1}`, line4 `√ε M x^{m−1}` | match `hcond` of both lemmas | script: integer bookkeeping `m ≤ 16` |

### (ii) Concrete nondegenerate instance (all numbers; no `N = 0`, grid `N = 1..10`)

* Common: `P = δ_()`, `size N = N+1`, `Nf N = N+1`, `η ≡ 1`, `t₁ = 0`, `t₀ = 1/(N+1)` (window not collapsed), `τU = 1`; `x = 1/(N+1)`.
* `eq736_detDomAt` tight: `d=3`, `Lf≡3`, `Wf≡2` (`(W L)^d = 216`), `n=2`, `Kt N t _ = K(t) = (1/7000)/(1 − 216t/7000)`, `lam ≡ 7000`; `K' = 216K²` on `[0,1] ⊇` window; (7.30): `216 t ≤ (N+1)⁻¹·7000` (holds for `t ≤ 1/(N+1)`); `h732`: `K(0) = 1/7000 ≤ s^τ·7000⁻¹`. Conclusion at `t₀`: `K·lam ≤ 1.0157 (N≥1) ≤ 7000/6784 = 1.0318`, so `K ≤ s^τ lam⁻¹` as soon as `(N+1)^τ ≥ 1.0318`.
* `eq736_detDomAt` zero: `d=3, Lf≡3, Wf≡2, n=2, K≡0`, window `[0,1]`, `lam N = 216(N+1)`: `216 t ≤ (N+1)⁻¹·216(N+1)`.
* `eq727GEAt`, `n₀ = 4` (even): `Lm m = x^{m−1}`, `Dm m = x^m`, `Km m = x^{m−1} − x^m`: `hLDK` equality; `hDLK` ⟺ `x ≤ 1`; `hodd` equality `x^{2l} = √(x^{2l−1}x^{2l+1})`; `hK`: `Km ≤ s^τ x^{m−1}`; `h745`: `x^m ≤ rhs745G` (the term `(Nη_t)^{−m}` of `rhs745G`, other terms ≥ 0).
* `eq728GAt`, `n₀ = 2`: same `Lm, Dm`; `h727 :=` output of `eq727GEAt` at `2·2` (index `Icc 2 4`); `h746`: `x^m ≤ rhs746G` (`m = 1,2`); `h730`: `t ≤ (N+1)⁻¹` (equality at `t₀`); `hscale`: `x ≤ (N+1)⁻¹` (equality).

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2212/pre.py
scale (3, 4, 32) size= 2097152 equivalence (7.30)<=>h730 on grid: True
scale (3, 5, 32) size= 4096000 equivalence (7.30)<=>h730 on grid: True
scale (4, 3, 8) size= 331776 equivalence (7.30)<=>h730 on grid: True
cond728G worst case (slack 2-S, (n0,p,q/rho_max)): (0.9736612469332468, (1, 1.0, 1.0))
gEven_cond727G worst case (slack 2-S, (n0,p,q/rho_max)): (1.9220441793142597, (0, 1.0, 1.0))
tau' checks passed; 3tau'-tauU <= -13 tauU/16 (max slack-form): -0.8125
pathwise exponent bookkeeping: True
pos(727,n0=4)/chain(728,n0=2) data N<=10: all hyps ok: True  min(rhs745-D)=0.000e+00 min(rhs746-D)=0.000e+00
tight eq736: ODE K'=216K^2 ok, (7.30) ok, h732 base K(0)=1/7000:  True  max K(t)*lam=1.0157 (<=7000/6784=1.0318)
tight: tau such that (N+1)^tau>=7000/6784 at N=1: tau>=0.0452
zero eq736 (7.30): True
tauU      n0=2    n0=4    n0=8   n0'=16 (targets5,6: log2 size >= 16/(13 tauU)*log2(36(20n0+48)))
1.000e-01      143.1     149.8     158.4     168.5
5.000e-02      286.3     299.6     316.8     337.1
1.263e-05  1.134e+06 1.186e+06 1.255e+06 1.335e+06
3.788e-06  3.779e+06 3.954e+06 4.182e+06 4.449e+06
target4: log2 size >= (2/tauU)*log2(8n^3+1) (eventually_small, tau'<=tauU/2); and >= 2/tau (tau-tau'>=tau/2) for 2<=size^(tau-tau')
1.000e-01      120.4     180.1       240
5.000e-02      240.9     360.1       480
1.263e-05  9.539e+05 1.426e+06 1.901e+06
3.788e-06   3.18e+06 4.753e+06 6.336e+06
targets5,6 extra: size^(tau-tau')>=3, tau-tau'>=15 tau/16 -> log2 size >= (16/(15 tau)) log2 3; tau=1: 1.691
```

Reading of the output: rows 1-3 = scale consistency (ii) at `(d,L,W) ∈ {(3,4,32),(3,5,32),(4,3,8)}`, exact `Fraction` arithmetic with `τU ∈ {1, 1/d}` (so `size^{−τU}` is rational) on a grid of 41 values of `η` and 21 of `t−t₁`; rows 4-5 = cond lemmas on the grid `p ∈ [1,10³]` (3001 log-spaced points), `q ∈ {1, .5, .01}·ρ(n₀)/p³` (the left sides increase in `q`, so `q = ρ/p³` is extremal), `n₀ ∈ 0..8` (728), `n₀ ∈ {0,2,…,16}` (727); the instance rows use `supOn` = grid max over 41 points.

(vi) Threshold tables above are `log₂ size` (columns `n₀ = 2, 4, 8, 16`, rows `τU = 1/10, 1/20, 1/79200, 1/264000`; the last two values are the `τ_U` of `docs/reports/T2202-prove.md:26` (F1)). They are asymptotic requirements for the consumers' conclusions, not hypotheses of the targets; as in RBM2D, no limit is external.

### Verdicts

* Target 1 `UnifDetDomAt`, 1′ `unifDetDom_iff_at_id` (`Iff.rfl`, `id N` unfolds): PASS.
* Target 2 `eventually_size_rpow_le_of_neg`, target 3 `stochDomAt_of_forall_highProbAt` (both `d`-free, verbatim): PASS.
* Target 4 `eq736_detDomAt`: PASS (`d` threaded into `Zd d`, `LoopSet d`, `primRhsGUE d`, `(W L)^d`; no `3 ≤ d`; exponents close with the slacks above; tight and zero instances satisfy every hypothesis).
* Target 5 `eq728GAt`, target 6 `eq727GEAt`, with their private pathwise/cond lemmas: PASS (cond lemmas close with slack `0.9737` / `1.922`; positive and chained instances satisfy every deterministic hypothesis).

## (b) Script output — Mon Oct  5 20:44:37 UTC 2026 (prover-hard stage 1b; commit 67194e3 on t/T2212; scripts and raw outputs in the scratchpad T2212/)

```
$ date -u; lake build RBM3D.Universality.GUEPhase.BootstrapAt   (worktree RBM3D-wt/T2212, commit 67194e3)
Mon Oct  5 20:42:27 UTC 2026
Build completed successfully (3252 jobs).
exit=0

$ lake build   (whole library in the worktree; the root import of the new module is added by the hub at merge)
info: RBM3D.lean:254:0: axiom audit: 6225 theorems, 2195 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
Build completed successfully (4014 jobs).

$ lake env lean axioms.lean   # #print axioms of the 7 public targets and the 10 instances (output in scratchpad/axioms.out)
declarations printed: 17
distinct axiom sets (script): [propext, Classical.choice, Quot.sound];
declarations whose set differs from [propext, Classical.choice, Quot.sound]: 0

$ targets 1-4 (and the first line of 5-6) extracted from RBM3D/Universality/GUEPhase/BootstrapAt.lean by script (extract.py)
def UnifDetDomAt (size : ℕ → ℕ) {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) : Prop :=  -- :535
  ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ ((size N : ℕ) : ℝ) ^ τ * g N u
theorem unifDetDom_iff_at_id {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) :  -- :540
    UnifDetDom f g ↔ UnifDetDomAt id f g :=
theorem eventually_size_rpow_le_of_neg {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop)  -- :544
    {a ρ : ℝ} (ha : a < 0) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, ((size N : ℕ) : ℝ) ^ a ≤ ρ :=
theorem stochDomAt_of_forall_highProbAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}  -- :551
    {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), RBM.Gauss.HighProbAt P size
      (fun N => {ω | ∀ u, ξ N u ω ≤ ((size N : ℕ) : ℝ) ^ τ * ζ N u ω})) :
    StochDomAt P size ξ ζ :=
theorem eq736_detDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) (d : ℕ)  -- :573
    (Lf Wf : ℕ → ℕ) [∀ N, NeZero (Lf N)]
    (Kt : ∀ N, ℝ → LoopIdx (Zd d (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
    (ht10 : ∀ N, t1 N ≤ t0 N) (lam : ℕ → ℝ → ℝ)
    (hlam : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < lam N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → lam N t ≤ lam N u)
    (hlamc : ∀ N, ContinuousOn (lam N) (Icc (t1 N) (t0 N)))
    (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (Zd d (Lf N)), I.WF → 2 ≤ I.length →
      I.length ≤ n →
      HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE d (Lf N) (Wf N) (Kt N t) I)
        (Icc (t1 N) (t0 N)) t)
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N),
      (((Wf N * Lf N) ^ d : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t)
    (h732 : UnifDetDomAt size (fun N (I : LoopSet d (Lf N) n) => ‖Kt N (t1 N) I.1‖)
      (fun N I => (lam N (t1 N))⁻¹ ^ (I.1.length - 1))) :
    UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × LoopSet d (Lf N) n) => ‖Kt N p.1 p.2.1‖)
      (fun N p => (lam N p.1)⁻¹ ^ (p.2.1.length - 1)) :=
theorem eq728GAt (P : Measure Ω) (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ →  ...  -- :627, signature 19 lines
theorem eq727GEAt (P : Measure Ω) (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) {n0 : ℕ} (hn0 : Even n0) (Nf : ℕ → ...  -- :691, signature 24 lines

$ lake env lean pins.lean   # check file section 2 copied verbatim (sed 108..253 of T2212-check.lean) + the examples below
Mon Oct  5 20:43:07 UTC 2026
exit=0  (no output: every pin and the rfl example elaborate)
/-! ## Pin examples (T2212): each pin of the check file is proved by the library target -/
example : T2212Check.T2212_unifDetDom_iff_at_id :=
  fun {U} f g => @unifDetDom_iff_at_id.{0} U f g
example : T2212Check.T2212_eventually_size_rpow_le_of_neg :=
  fun {size} hsize {a ρ} ha hρ => eventually_size_rpow_le_of_neg hsize ha hρ
example : T2212Check.T2212_stochDomAt_of_forall_highProbAt :=
  fun {Ω} _ {P} {size} {U} {ξ ζ} h => @stochDomAt_of_forall_highProbAt.{0, 0} Ω _ P size U ξ ζ h
example : T2212Check.T2212_eq736_detDomAt :=
  fun size hsize d Lf Wf _ Kt n t1 t0 ht10 lam hlam hanti hlamc hK {τU} hτU h730 h732 =>
    eq736_detDomAt size hsize d Lf Wf Kt n t1 t0 ht10 lam hlam hanti hlamc hK hτU h730 h732
example : T2212Check.T2212_eq728GAt :=
  @eq728GAt.{0}
example : T2212Check.T2212_eq727GEAt :=
  @eq727GEAt.{0}
example : T2212Check.T2212_inst_bounds :=
  BootstrapAtCheck.inst_bounds
example (size : ℕ → ℕ) {U : ℕ → Type} (f g : ∀ N, U N → ℝ) :
    T2212Check.UnifDetDomAtV size f g = UnifDetDomAt size f g := rfl

$ instances (statements extracted by script; each proof applies the target at the concrete data of (a) (ii); `inst_bounds` is shown by its pin above)
theorem inst_unifDetDom_iff_at_id :  -- :843
    UnifDetDomAt id (fun (N : ℕ) (_ : Unit) => ((N : ℝ) + 1)⁻¹) (fun _ _ => (1 : ℝ)) :=
theorem inst_eventually_size_rpow_le_of_neg :  -- :850
    ∀ᶠ N : ℕ in atTop, ((sizeD N : ℕ) : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 :=
theorem inst_stochDomAt_of_forall_highProbAt :  -- :856
    StochDomAt (Measure.dirac ()) sizeD (fun _ (_ : Unit) (_ : Unit) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
theorem inst_eq736_detDomAt_zero : UnifDetDomAt sizeD  -- :867
    (fun N (_ : Path.TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) N × LoopSet 3 3 2) =>
      ‖(0 : ℂ)‖)
    (fun N p => (lamD N p.1)⁻¹ ^ (p.2.1.length - 1)) :=
theorem inst_eq736_detDomAt_tight : UnifDetDomAt sizeD  -- :899
    (fun N (p : Path.TimeIcc t1D t0D N × LoopSet 3 3 2) => ‖(kTight p.1 : ℂ)‖)
    (fun _ p => (7000 : ℝ)⁻¹ ^ (p.2.1.length - 1)) :=
theorem inst_eq728GAt_zero : StochDomAt (Measure.dirac ()) sizeD  -- :958
    (fun N (_ : Path.TimeIcc t1D t0D N × Set.Icc 1 2) (_ : Unit) => (0 : ℝ))
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ (p.2 : ℕ)) :=
theorem inst_eq727GEAt_zero : StochDomAt (Measure.dirac ()) sizeD  -- :973
    (fun N (_ : Path.TimeIcc t1D t0D N × Set.Icc 2 4) (_ : Unit) => (0 : ℝ))
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) :=
theorem inst_eq727GEAt_pos : StochDomAt (Measure.dirac ()) sizeD  -- :1101
    (fun N (p : Path.TimeIcc t1D t0D N × Set.Icc 2 (2 * 2)) (ω : Unit) => LmD N p.2 p.1 ω)
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) :=
theorem inst_eq728GAt_chain : StochDomAt (Measure.dirac ()) sizeD  -- :1126
    (fun N (p : Path.TimeIcc t1D t0D N × Set.Icc 1 2) (ω : Unit) => DmD N p.2 p.1 ω)
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ (p.2 : ℕ)) :=

$ cat regcheck.lean   # temporary, uncommitted (scratchpad)
import RBM3D
import RBM3D.Universality.GUEPhase.BootstrapAt
#assert_rbm_axioms
$ date -u; lake env lean regcheck.lean   # in the worktree
Mon Oct  5 20:42:36 UTC 2026
exit=0
axiom audit: 6269 theorems, 2206 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
lines of the output naming UnifDetDomAt or BootstrapAt: 0
premises found by scanning: 132 (borrowed 1, owed 103, structural 24, refuted 4).
registry: 2 borrowed + 148 owed + 79 structural + 4 refuted; 101 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,

$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/BootstrapAt.lean   # HEAD = 9e0f275
 RBM2D/Universality/GUEPhase/BootstrapAt.lean | 128 +++------------------------
 1 file changed, 12 insertions(+), 116 deletions(-)
$ diff src_body.txt new_body.txt | grep "^[<>]"   # source c9a24cf:BootstrapAt.lean :37-751 vs the new file up to the instance section (hunk headers dropped)
> 
> /-- The merged `RBM.UnifDetDom` (`Defs/Domination.lean:52`) is `UnifDetDomAt` at `size = id`, as
> `RBM.stochDom_iff_at_id` and `RBM.Gauss.highProb_iff_at_id` are. -/
> theorem unifDetDom_iff_at_id {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) :
>     UnifDetDom f g ↔ UnifDetDomAt id f g := Iff.rfl
< `UnifDetDom ↦ UnifDetDomAt size` and the failure threshold `N^{-τU} ↦ (size N)^{-τU}` in (7.30);
< the matrix dimension `size N` is not tied to `(Wf N * Lf N)^2` (`eq736` takes `A, ε` free). -/
< theorem eq736_detDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop)
> `UnifDetDom ↦ UnifDetDomAt size`, `Z2 ↦ Zd d` and the failure threshold `N^{-τU} ↦ (size N)^{-τU}` in (7.30);
> the matrix dimension `size N` is not tied to `(Wf N * Lf N)^d` (`eq736` takes `A, ε` free). -/
> theorem eq736_detDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) (d : ℕ)
<     (Kt : ∀ N, ℝ → LoopIdx (Z2 (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
>     (Kt : ∀ N, ℝ → LoopIdx (Zd d (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
<     (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (Z2 (Lf N)), I.WF → 2 ≤ I.length →
>     (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (Zd d (Lf N)), I.WF → 2 ≤ I.length →
<       HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE (Lf N) (Wf N) (Kt N t) I)
>       HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE d (Lf N) (Wf N) (Kt N t) I)
<       (((Wf N * Lf N) ^ 2 : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t)
<     (h732 : UnifDetDomAt size (fun N (I : LoopSet (Lf N) n) => ‖Kt N (t1 N) I.1‖)
>       (((Wf N * Lf N) ^ d : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t)
>     (h732 : UnifDetDomAt size (fun N (I : LoopSet d (Lf N) n) => ‖Kt N (t1 N) I.1‖)
<     UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × LoopSet (Lf N) n) => ‖Kt N p.1 p.2.1‖)
>     UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × LoopSet d (Lf N) n) => ‖Kt N p.1 p.2.1‖)
<   have key := eq736 (Lf N) (Wf N) (Kt N) (ht10 N) (lam N) (hlam N) (hanti N) (hlamc N) (hK N)
>   have key := eq736 d (Lf N) (Wf N) (Kt N) (ht10 N) (lam N) (hlam N) (hanti N) (hlamc N) (hK N)
< 
source declarations :1-750 not ported: none (script set difference empty); new declaration: unifDetDom_iff_at_id; source :752-853 (instances) replaced by the BootstrapAtCheck section
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/Universality/GUEPhase/BootstrapAt.lean; echo exit=$?
exit=1 (1 = no match)
$ git diff --stat main...t/T2212
 RBM3D/Universality/GUEPhase/BootstrapAt.lean | 1142 ++++++++++++++++++++++++++
 1 file changed, 1142 insertions(+)

$ grep -rn <name> RBM3D/ --include="*.lean" | wc -l   # main worktree, main HEAD ed9c0f1 (script clash.sh)
UnifDetDomAt: 0 unifDetDom_iff_at_id: 0 eventually_size_rpow_le_of_neg: 0 stochDomAt_of_forall_highProbAt: 0 eq736_detDomAt: 0 eq728GAt: 0 eq727GEAt: 0 BootstrapAtCheck: 0 BootstrapAt_: 0 T2212Check: 0
branch worktree, files other than GUEPhase/BootstrapAt.lean naming any of the 8 public names: 0
```

Narrative (stage 1b):
- Port: `c9a24cf:RBM2D/Universality/GUEPhase/BootstrapAt.lean` `:37-751` copied by script; the diff above is the whole change: the `d` threading of `eq736_detDomAt` (`Zd d`, `primRhsGUE d`, `LoopSet d`, `(W L)^d`, `eq736 d …`, `d` explicit after `hsize`), the new `unifDetDom_iff_at_id` (`Iff.rfl`), two docstring lines. The six pathwise/constant lemmas are `private`, prefix `BootstrapAt_`, text unchanged. No `3 ≤ d` appears in any statement or proof.
- Imports: `Bootstrap`, `Defs.StochDomAt`, `Induction.PerTimeCalc`. `Gauss.DominationAt` is not imported: the instances use `RBM.Gauss.HighProbAt.of_eventually_univ` instead of `highProbAt_univ`.
- No (a′): the rows of (a) I relied on (the `d`-token count, `τ'` values, instance data) agree with the files; no preflight mistake found.
- Instances (all in `RBM.Univ.GUEPhase.BootstrapAtCheck`, theorems): every deterministic hypothesis is discharged; `P = δ_()`, `size N = N + 1`. `inst_eq728GAt_zero` and `inst_eq727GEAt_zero` (`L = D = K = 0`) and `inst_eq736_detDomAt_zero` (`K ≡ 0`) are degenerate on purpose (ticket: RBM2D pattern). The nondegenerate ones: `inst_eq736_detDomAt_tight` (`K(t) = (1/7000)/(1 - 216t/7000)`, derivative from merged `kTight_hasDerivAt` and `primRhsGUE_const_len_two`, window `[0, 1/(N+1)]`, `λ ≡ 7000`), `inst_eq727GEAt_pos` (`n₀ = 2 * 2`, `L_m = x^{m-1}`, `D_m = x^m`, `K_m = x^{m-1} - x^m`, `x = 1/(N+1)`; `h745` from `x^m ≤ rhs745G`), `inst_eq728GAt_chain` (`n₀ = 2`, `h727 := inst_eq727GEAt_pos`, `h746` from `x^m ≤ rhs746G`). The helper names of the section (`xD`, `LmD`, …) are public but live in `BootstrapAtCheck` (ticket-named data plus helpers of the positive data).
- Registry: `UnifDetDomAt` is the only new `Prop`-valued definition; the pre-check exits 0 and its output names neither `UnifDetDomAt` nor `BootstrapAt`; `RBM3D/Test/Axioms.lean` is not touched, no registry line owed. The full `lake build` in the worktree does not contain the new module (root import added by the hub at merge).
- §29 checklist: (1) every statement is on `Icc (t1 N) (t0 N)` with `ht10`; no `t < 1` hypothesis occurs in any signature above. (2) no case-(ii) boundary hypothesis occurs. (3) `Lf`, `Wf` are free in `eq736_detDomAt`, `size` is not tied to `(W L)^d` (the consumer ties them: `Sizes.size n := (sz.W n * sz.L n) ^ d`, `Defs/Sizes.lean:157`). (4) `∀ᶠ N` only in `h730`, `hscale` and the `≺`'s; the `∀ N` hypotheses are `∀ n` facts at the consumer RBM2D `PathBounds.lean:457-472` (`hη`, `hanti`, `hηc`, `hNpos`), with `h730'`, `hscale'` eventual (`:474`, `:482`). (5) inputs and outputs are `StochDomAt`/`HighProbAt` over `TimeIcc × index`, continuity is a `HighProbAt` event. (6) `0 < Nf`, `0 < η`, `0 < lam`, `0 < τU`, `hsize` are hypotheses. (7) scale `size N` everywhere, `(W L)^d` only in `h730` of `eq736_detDomAt`.
- `T2212b`, checked against RBM1D: `c06b103:RBM1D/Hierarchy/GUEPhase.lean:72-74` proves (7.27) by a continuity argument over all lengths `2 ≤ n ≤ n₀` from (7.45) at all those lengths, with no even/odd split (no word `odd`/`even` in that file); the even-length variant with `L_{2l+1} ≤ √(L_{2l} L_{2l+2})` is the RBM2D construction ported here. [YY_25] §7.2 is not among this project's sources and was not compared.

## (c) Verified Mathlib names (`#check` in the worktree, scratchpad/mathlib.lean and m2.lean; signatures printed there)
- `inv_le_one_of_one_le₀ : 1 ≤ a → a⁻¹ ≤ 1`; `div_le_one : 0 < b → (a / b ≤ 1 ↔ a ≤ b)`; `mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a * b ≤ a`
- `Finset.sum_nonneg`; `HasDerivAt.ofReal_comp : HasDerivAt f u z → HasDerivAt (fun y => ↑(f y)) ↑u z`; `hasDerivWithinAt_const`; `even_two_mul`
- `Real.one_le_rpow : 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z`; `Real.rpow_neg_one`; `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`; `Set.eq_empty_of_forall_notMem`
- `Filter.tendsto_atTop_mono` exists; the root name `tendsto_atTop_mono` is an unknown identifier (mathlib.lean:9:8), used here only through `open Filter`
- Names of the ported source (check file §1 list: `Set.finite_Icc`, `Set.Icc_subset_Icc_right`, `Nat.even_or_odd`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `one_div_le_one_div_of_le`, `pow_le_pow_right₀`, `one_le_pow₀`, `inv_anti₀`, `ContinuousOn.inv₀`, `MeasureTheory.measure_mono`, `MeasureTheory.Measure.dirac`): all `#check` OK
- Merged: `RBM.StochDomAt.of_le_left`, `RBM.StochDomAt.refl` (needs `Tendsto size`), `RBM.Gauss.HighProbAt.of_eventually_univ`, `RBM.UnifDetDom.of_le`: signatures printed OK. Names verified absent: none.

## (d) Open issues and paper-delta candidates
- `T2212a` (Lean structure, not a paper delta): the `≺` of (7.27), (7.28), (7.36) along `size N` (`StochDomAt`, `HighProbAt`, `UnifDetDomAt`); the index-scale forms are the `size = id` instances by `Iff.rfl` (`stochDom_iff_at_id`, `highProb_iff_at_id`, new `unifDetDom_iff_at_id`).
- `T2212b` (candidate): (7.27) is bootstrapped at even lengths only, odd lengths by `L_{2l+1} ≤ √(L_{2l} L_{2l+2})`; RBM1D C.7 does not do this (narrative), [YY_25] §7.2 not compared.
- `T2212c` (bookkeeping): explicit smallness of the `L`-bootstraps (`Φ = M = N^{τ'}`, `M' = 3N^{τ'}`, `ε = δ = N^{-τU}`, `τ' = min(τ, τU)/16`, `p³q ≤ 1/(36(20 n₀ + 48))`) with the `log₂ size` thresholds of (a) (vi); consumer flag, asymptotic as in RBM2D. The `(W L)^d` of (7.30) in `eq736_detDomAt` is D521 (T2202b), no new delta.
- None open on this ticket: all six targets and the bridge are proved and instanced; no external hypothesis.
