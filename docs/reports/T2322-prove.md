Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 04:10:33 UTC 2026

Source read: `git -C ../RBM2D --no-optional-locks show HEAD:RBM2D/Universality/GUEPhase/Proc.lean` (HEAD `9e0f275`; the last commit touching the file is `81fca44`, as in the ticket). Local paper has no GUE-phase section: `1_2_Intro_model_result.tex:566-570` delegates the universality proof to [Xu:2024aa]/[DYYY25]; (7.25)-(7.36) are [YY_25] §7.2 (as in `Grid.lean` header). So the d >= 3 statements below are checked by direct computation (identities from the merged lemmas, numerics), not against a local paper line.

### (i) Exponent table

d = 2 token table of `Proc.lean:1-860` (script `tokens.py`; lines are source lines):

| token (d=2) | source lines | d-dimensional replacement |
|---|---|---|
| `Z2 (d.L n)` / `Z2 L` (51 lines) | 36,84-108,273-419,456,561-578 | `Zd d (sz.L n)` / `Zd d L` |
| `BlockIndex L W` (2) | 471,500 | `Vtx d L W` |
| `Idx (d.L n) (d.W n)`, `Idx L W` (22) | 34,70,72,510,520,563,727-856 | `Idx d (sz.L n) (sz.W n)`, `Idx d L W` (`= Zd d (W*L)`) |
| `(d : Sizes)`, `PathΩ d`, `d.L`,`d.W`,`d.size` | 17-860 (114 lines) | `{d} (sz : Sizes d)`, `PathΩ sz`, `sz.L`, `sz.W`, `sz.size n = (W L)^d` (def) |
| `spectralZ` / `spectralM` (52/16) | 71-72,303-351,511-549,743-856 | `zt` / `mE` |
| `gloop L W (blockMat M)` (9) / `blockMat M` (14) | 87,303-350 / 35,80,511-549 | `loopL d L W (blockMat d L W M)` |
| `RBM.Ind.loopMax L W` (18) | 473-549 | `RBM.Ind.loopMax d L W` |
| `maxLoopPM/greenBlk/avgErr/egtNGUE/SBgue L W` (4/1/10/1/9) | 511-622 | same with `d L W` explicit (`Green.*`, `egtNGUE d L W`, `SBgue d L`) |
| `pmLoop a b` (1) | 514 | list loop `⟨[true,false],[a,b]⟩` via `loopPM = loopFine`, `loopM_eq_loopL` (used `Path/Expansion.lean:652`) |
| `RBM.Ind.LLf L W E u M (I.cutGlue k b)` (11) | 565-626 | `loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)` (the term `egtNGUE` takes) |
| `RBM.Gauss.norm_green_le` (2) | 756,760 | operator-norm resolvent bound `‖G‖ <= 1/η` of `Green/IBPPoly.lean:411` route (`norm_Gsig_le_inv_eta`, L2-operator norm) |
| `^ 2` on `W`,`L`,`W*L`,`SBgue` (29 lines) | 521,524,534-544 (`gue_inv_W`); 566,581-636 (`norm_egtNGUE`) | `^ d` (exactly the two d-sensitive theorems) |
| `^ 2` dimension-free (12 lines) | 176,482-502,668,726,797,816 | unchanged (`loopMax²`, `η⁻²` from two resolvents) |
| `Fintype.card (Z2 L) = L*L` (`ZMod.card`) | 576-577 | `card_Zd : Fintype.card (Zd d L) = L ^ d` (`Defs/Lattice.lean:67`) |
| `(0 : Z2 (W*L))` Nonempty witness | 729 | `(0 : Zd d (W*L))` |
| docstrings "`d = 2`", `N = (W L)²` | 17,33,518 | `d >= 3`, `N = (W L)^d` |
| `BlockIndex`-free defs 1-110 (`gueDelta ... gueKproc`) | 56-110 | = check section 2 (only renamings above; exponent `-(τU/4)` unchanged) |

Exponents, thresholds, constants (d = 3 numbers in the last column are the instance of (ii)):

| quantity | value | constraint | slack / instance |
|---|---|---|---|
| `N = sz.size n` | `(W L)^d` | `= card (Idx d L W)`; `√(Δ/N)` in `gueH` | d=3,L=3,W=4: N=1728; sz0 n=0: 2097152 |
| `δ_n = N^{-τU/4}` (`gueDelta`) | exponent `-τU/4`, d-free | Ward step needs `δ <= Im m/2` (consumer hypothesis `hδN`, RBM2D `HypB.lean:112`) | not a hypothesis of any target |
| Ward bound (`inv_N_le_maxLoopPM`) | `Im m /(2 N η) <= maxLoopPM`, `N=(WL)^d`, `η=(1-u) Im m` | `Im z > 0`, `GoodEvent .. (mE E) δ`, `δ <= Im m/2` | verified numerically below |
| Ward lemma exponent | `(W⁻¹)^d = 2 L^d (1-u) · Im m/(2 N η)` (identity) | conclusion `(W⁻¹)^d <= 2 L₂` needs `L^d (1-u) <= 1` | instance `L^d(1-u) = 1` (slack 0); `1-u = L⁻ᵈ/2` gives factor 2 |
| `hell` | `(L:ℝ)^d * (1-u) <= 1` | **not** `L²(1-u) <= 1` (see Correction C1) | d=3: `L²(1-u) <= 1` allows `L^d(1-u) = L` |
| `egt` prefactor | `W^d · (L^d · L^d) · L^{-d} = (W L)^d` | `‖SBgue‖ = (L^d)⁻¹`, two label sums of `L^d` terms | 216 = 6³ = 216 (script) |
| (6.4)/(5.117) | `L_{2l+1} <= √L₂ · L_{2l}`, `L_{4l} <= L_{2l}²` | `l >= 1`, `H` Hermitian; d-free (`loopMax_odd_sq_le`, `loopMax_two_mul_add_le`) | constants 1, no slack |
| `gueDev_succ_le` | `η_{t0}⁻² (√(Δ/N) Σ_{ij}|X_ij| + Δ)` | `|E|<2`, `t1<=t0<1`, `k<K`; `‖z'-z‖ = Δ‖m‖ = Δ` (`‖mE E‖=1`, `|E|<=2`); `η_u >= η_{t0}` for `u <= t0`; d-free | E=0,t0=.9: `η⁻²=100`; `‖z'-z‖ = Δ` checked |
| grid | `Δ = (t0-t1)/K`, `u_k = t1 + kΔ` | `Δ >= 0` iff `t1 <= t0`, `K n ≠ 0`; tent is `δ_{jk}` at grid nodes iff `Δ > 0`; `Δ = 0` branch constant | t1=.85611, t0=.9, K=4, Δ=.010973 |
| §29 boundary rows | (1) `t0<1` is a hypothesis of `gueDev_succ_le`; `0<=t1` unused (only `t1<=t0`) (2) n/a (no `ilambda`) (3) `L^d <= W^K` unused (4) all targets pointwise in `n` (no `∀ n`/`∀ᶠ n`) (5)-(7) n/a (deterministic, no `PrecPT`, no scale lower bounds, no `ℓ`) | | |

The three d >= 3 statements (Lean-side; `NeZero L`, `NeZero W`):
- `gue_inv_W_le_loopMax`: `M` Hermitian on `Idx d L W`, `|E|<2`, `u<1`, `hell : (L:ℝ)^d * (1-u) <= 1`, `GoodEvent (greenBlk d L W E u M true) (mE E) δ`, `δ <= (mE E).im/2` ⟹ `((W:ℝ)⁻¹)^d <= 2 * loopMax d L W (blockMat d L W M) (zt E u) 2`. Proof: `inv_N_le_maxLoopPM` (`EntryDet.lean:354`), `(zt E u).im = (1-u)(mE E).im`, `((W*L)^d:ℕ) = W^d L^d`, `maxLoopPM >= 0`, `maxLoopPM <= L₂` (`norm_gloop_le_loopMax` on the 2-loop).
- `norm_egtNGUE_le`: `(L W) [NeZero]`, `hε : ∀ σ a, ‖avgErr d L W E u M σ a‖ <= ε`, `hB : ∀ k ∈ Icc 1 I.length, ∀ b, ‖loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖ <= B` ⟹ `‖egtNGUE d L W E u M I‖ <= I.length * (((W*L)^d : ℕ):ℝ) * ε * B` (case `I.length = 0` trivial).
- `gueDev_succ_le`: the check section 3 text (dimension-free; `‖G‖ <= η_{t0}⁻¹` at both grid times from the `Green/IBPPoly.lean:411` route; `‖G'-G‖ <= ‖G'‖(‖H'-H‖+‖z'-z‖)‖G‖`; `‖X‖_op <= Σ|X_ij|`).

**Correction C1 (ticket text).** The ticket asks both for the exponent "exactly as `inv_N_le_maxLoopPM` gives it" and for `hell` "as the `ellT_eq_L` condition" (`L²(1-t) <= g²`, `Bootstrap.lean:148`). These differ for d >= 3: `inv_N_le_maxLoopPM` gives `W^{-d} <= 2 L^d (1-u) · maxLoopPM`, so the conclusion `W^{-d} <= 2 L₂` needs `L^d (1-u) <= 1` (equal to `L²(1-u) <= 1` only at d = 2; `L^d(1-u) <= 1` implies `L²(1-u) <= 1` but not conversely). `gue_inv_W_le_loopMax` does not mention `ellT`, so only `hell : (L:ℝ)^d * (1-u) <= 1` is used. The consumer (UN-48/49, `HypB` analogue, RBM2D `HypB.lean:112,170-174` derives it from the hypothesis `hellN : L²(1-t1) <= 1`) must supply `L^d (1-t1) <= 1`; this is a consumer-side obligation, not checked here.

### (ii) One concrete nondegenerate instance

Command: `PYTHONPATH=pylib /usr/bin/python3 pre.py` (scratch dir `.../scratchpad/T2322/`; numpy 2.0.2 installed locally by `pip --target`; `pre.py` is Python, no Lean). Output verbatim:

```
Ward d=3 L=3 W=4 N=1728 E=0.0 L^d(1-u)=1.00 N*eta=64: dev=0.456<=Imm/2=0.500 True; m/(2N eta)=7.81e-03<=maxLPM=3.12e-02 True; W^-d=1.56e-02<=2L^d(1-u)maxLPM=6.23e-02 True
Ward d=3 L=3 W=4 N=1728 E=0.0 L^d(1-u)=1.00 N*eta=64: dev=0.491<=Imm/2=0.500 True; m/(2N eta)=7.81e-03<=maxLPM=3.18e-02 True; W^-d=1.56e-02<=2L^d(1-u)maxLPM=6.35e-02 True
Ward d=3 L=2 W=4 N=512 E=0.0 L^d(1-u)=1.00 N*eta=64: dev=0.406<=Imm/2=0.500 True; m/(2N eta)=7.81e-03<=maxLPM=2.73e-02 True; W^-d=1.56e-02<=2L^d(1-u)maxLPM=5.47e-02 True
egt prefactor W^d*(L^d*L^d)*L^-d = 216.0  (WL)^d = 216
aligned |egt| = 290.9088  n*(WL)^d*eps*B = 290.9088
gueDev_succ: dev_2=0.5535 <= dev_1+eta0^-2(sqrt(D/N)*sum|X|+D)=47439.5: True; |z'-z|=0.025000=D=0.025000
sz0 n=0: N=2097152=2097152:True; t1=0.85611<=t0=0.9<1; Delta=0.010973>0; u_K=0.900000; E=0: etaT(t0)=0.100, eta^-2=100
tent(1,u_1)=1.0, tent(1,u_2)=0, tent(1,mid(u_1,u_2))=0.5000; interp(k^2, mid(u_1,u_2))=2.5000 (=(1+4)/2); interp(k^2,u_3)=9.0000
```

Instances per target:
- `gue_inv_W_le_loopMax`: `d=3, L=3, W=4, E=0, u = 1-1/27, M = H` (GUE sample, N=1728): `|E|<2`, `u<1`, `L^d(1-u) = 1`, `δ = dev = 0.456` (and 0.491 for seed 1) `<= Im m/2 = 0.5`, Ward lower bound and the conclusion hold (1.56e-2 <= 6.2e-2). Margin to `Im m/2` is small at W=4 (`Nη = W^d = 64`); larger `W` widens it. No Lean-checkable witness for `GoodEvent` exists at small `N`: a diagonal `M` cannot satisfy `‖G-m‖_max <= 1/2` together with `L^d(1-u) <= 1` (`G_xx = (r+iη)/(r²+η²)`, `η = 1/27`), and a hand-built matrix with `G ≈ m·1` is not available. So in the Lean example `hΩ` (the entry local law, another gate's input) stays a hypothesis; `hE`, `hu`, `hell`, `hδ` are discharged at `d=3, L=3, W=4, E=0, u=26/27, δ=1/2` and `M` stays an abstract Hermitian matrix (`M = 0` is NOT a witness: there `G = i/(1-u) = 27i`, so `hΩ` fails). Hypothesis set is consistent (numerical GUE samples above), not vacuous.
- `norm_egtNGUE_le`: `d=3, L=3, W=2, n=4`, aligned labels attain the bound exactly (290.9088 = 4·216·0.37·0.91), so the prefactor `(WL)^d` is sharp; `ε = 0.37`, `B = 0.91` are the example's `hε`,`hB` bounds (the example may take `ε`,`B` as the stated bounds; `hε`,`hB` are the example's hypotheses on `M`, `E`, `u`).
- `gueDev_succ_le`: `sz0` at `n=0` (`d=3, L=4, W=32, N=2097152`), `E 0 = 0`, `t1 0 = e^{-1/20}·9/10 = 0.85611`, `t0 0 = 9/10`, `K = 4`, `k ∈ {0,1,2,3}`; `|E|<2`, `t1<=t0<1`, `k<K`, `Δ = 0.010973`, `η_{t0}⁻² = 100`; sample check at `d=3,L=3,W=2` shows `dev_2 = 0.5535 <= 47439.5` and `|z'-z| = Δ`.
- `gueLproc_time`: same `sz0`, `t1 0 <= t0 0`, `k = 4 = K 0` (`k <= K n`), any `ω`; `gueLproc_nonneg` any data.
- `gueTent` / `gueInterp`: grid `t1 = .8, t0 = .9, K = 4` (`Δ = .025`): `tent_1(u_1) = 1`, `tent_1(u_2) = 0`, `tent_1(midpoint u_1,u_2) = 1/2`, `interp(k²)(midpoint) = 5/2`, `interp(k²)(u_3) = 9` (script above; `norm_num`-checkable).
- External hypotheses: none are assumed by these targets (no new `Prop`, no registry line); the only non-discharged input is `hΩ` of `gue_inv_W_le_loopMax`, a local-law event, supplied by the consumer. Limit computation for `δ <= Im m/2`: `δ_N = N^{-τU/4} → 0` for `τU > 0` while `Im m(E) > 0` is fixed for `|E|<2`, so it holds eventually; e.g. `N = 2097152`, `τU = 1/2`: `δ = N^{-1/8} = 0.1621 <= Im m(0)/2 = 0.5` (python3 `2097152**(-1/8)`).

### Verdicts
- Eleven definitions (check section 2, verbatim) and the helpers `:112-374`: PASS (renaming only; exponents/thresholds unchanged).
- `gueLproc_nonneg` ... `gueDproc_time` (`:380-463`, incl. `gueLproc_time`): PASS (d-free; `gueH_isHermitian` + `submatrix` for `blockMat`).
- `gueLoopMax_odd_succ_le`, `gueLoopMax_four_mul_le`: PASS (d-free).
- `gue_inv_W_le_loopMax`: PASS with Correction C1 (`hell : L^d (1-u) <= 1`, conclusion `(W⁻¹)^d <= 2 L₂`); the literal reading `L²(1-u) <= 1` is not derivable by this route (loses factor `L^{d-2}`).
- `norm_egtNGUE_le`: PASS (`(WL)^d`, hypothesis in `avgErr`/`loopL` form).
- `gueDev_succ_le`: PASS (d-free).
Overall: PASS.

## (b) Script output (stage 1b, written Thu Oct  8 04:33:36 UTC 2026; branch `t/T2322`, commit `0d695a8`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2322`)

### b.1 Build, hygiene, full build, registry pre-check
```
$ lake build RBM3D.Universality.GUEPhase.Proc
Thu Oct  8 04:29:08 UTC 2026
exit 0
messages mentioning GUEPhase/Proc.lean: 0
✔ [3756/3756] Built RBM3D.Universality.GUEPhase.Proc (5.7s)
Build completed successfully (3756 jobs).
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/Proc.lean | wc -l  # -> 0
$ lake build   # full library (the root RBM3D.lean does not import Proc until the hub merges)
Thu Oct  8 04:30:11 UTC 2026
exit 0
Build completed successfully (4127 jobs).
$ lake env lean registry.lean   # = import RBM3D; import RBM3D.Universality.GUEPhase.Proc; #assert_rbm_axioms (scratch, uncommitted)
exit 0
axiom audit: 9092 theorems, 2956 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ git diff --stat main...t/T2322
 RBM3D/Universality/GUEPhase/Proc.lean | 1113 +++++++++++++++++++++++++++++++++
 1 file changed, 1113 insertions(+)
```

### b.2 `#print axioms` of every public declaration (11 definitions, 14 theorems)
```
$ lake env lean axioms.lean   # one `#print axioms RBM.Univ.GUEPhase.<name>` per public def/theorem of the file
exit 0
  25 depends on axioms: [propext, Classical.choice, Quot.sound]
declarations printed: 25; other lines: 0
```

### b.3 Target statements, extracted by script (`extract.py`: text of each theorem up to `:= by`)
```lean
theorem gueLproc_nonneg (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ)
    (ω : PathΩ sz) : 0 ≤ gueLproc sz E t1 t0 K δ n m t ω

theorem gueLproc_time (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m k : ℕ)
    (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n) (ω : PathΩ sz) :
    gueLproc sz E t1 t0 K δ n m (gridTime t1 t0 K n k) ω =
      gueLmax sz E t1 t0 K n m (min k (gueStop sz E t1 t0 K δ n ω)) ω

theorem gueDev_succ_le (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (hE : |E n| < 2)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) (ω : PathΩ sz) :
    gueDev sz E t1 t0 K n (k + 1) ω ≤ gueDev sz E t1 t0 K n k ω +
      (etaT (E n) (t0 n))⁻¹ ^ 2 * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
        ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
          ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n)

theorem gue_inv_W_le_loopMax {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {E u : ℝ}
    (hE : |E| < 2) (hu : u < 1) {g : ℝ} (hell : (L : ℝ) ^ 2 * (1 - u) ≤ g ^ 2) {δ : ℝ}
    (hΩ : RBM.Green.GoodEvent (RBM.Green.greenBlk d L W E u M true) (mE E) δ)
    (hδ : δ ≤ (mE E).im / 2) :
    ((W : ℝ)⁻¹) ^ d ≤
      2 * (L : ℝ) ^ (d - 2) * g ^ 2 * RBM.Ind.loopMax d L W (blockMat d L W M) (zt E u) 2

theorem norm_egtNGUE_le (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (Zd d L)) {ε B : ℝ}
    (hε : ∀ (σ : Bool) (a : Zd d L), ‖RBM.Green.avgErr d L W E u M σ a‖ ≤ ε)
    (hB : ∀ k ∈ Finset.Icc 1 I.length, ∀ b : Zd d L,
      ‖loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)‖ ≤ B) :
    ‖egtNGUE d L W E u M I‖ ≤ (I.length : ℝ) * (((W * L) ^ d : ℕ) : ℝ) * ε * B

theorem gueLoopMax_odd_succ_le {L W : ℕ} [NeZero L]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    RBM.Ind.loopMax d L W H z (2 * l + 1) ≤
      Real.sqrt (RBM.Ind.loopMax d L W H z 2) * RBM.Ind.loopMax d L W H z (2 * l)

theorem gueLoopMax_four_mul_le {L W : ℕ} [NeZero L]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {l : ℕ}
    (hl : 1 ≤ l) :
    RBM.Ind.loopMax d L W H z (4 * l) ≤ RBM.Ind.loopMax d L W H z (2 * l) ^ 2
```
The three pinned statements `gueLproc_nonneg`, `gueLproc_time`, `gueDev_succ_le` are the texts of check section 3; `norm_egtNGUE_le` is the `d ≥ 3` statement of (a)(i); `gue_inv_W_le_loopMax` is the ticket form (`ellT_eq_L` condition, repair round 1; replaces (a)(i)'s Correction C1 form). Statement re-extracted at `5bce253` (`awk '/^theorem gue_inv_W_le_loopMax/,/:= by$/'`).

### b.4 Check-file equality (ticket acceptance)
```
(a) python3 -I defcmp.py   # whitespace-normalized text of the 11 definitions (docstrings included): check lines 96-150 vs file
check defs : 11 ['gueDelta', 'gueDev', 'gueDmax', 'gueDproc', 'gueInterp', 'gueKbar', 'gueKproc', 'gueLmax', 'gueLproc', 'gueStop', 'gueTent']
file  defs : 11 ['gueDelta', 'gueDev', 'gueDmax', 'gueDproc', 'gueInterp', 'gueKbar', 'gueKproc', 'gueLmax', 'gueLproc', 'gueStop', 'gueTent']
ALL EQUAL: True
(b) check_equal.lean = the check file, with `import RBM3D.Universality.GUEPhase.Proc` added after its last import, plus at the end:
open RBM.Univ.GUEPhase in
example (d : ℕ) (sz : RBM.Gauss.Sizes d) : RBM.Univ.GUEPhase.T2322Check.T2322_gueLproc_nonneg sz :=
  gueLproc_nonneg sz
open RBM.Univ.GUEPhase in
example (d : ℕ) (sz : RBM.Gauss.Sizes d) : RBM.Univ.GUEPhase.T2322Check.T2322_gueLproc_time sz :=
  gueLproc_time sz
open RBM.Univ.GUEPhase in
example (d : ℕ) (sz : RBM.Gauss.Sizes d) : RBM.Univ.GUEPhase.T2322Check.T2322_gueDev_succ_le sz :=
  gueDev_succ_le sz
$ lake env lean check_equal.lean
exit 0
lines containing 'error' in output: 0
```

### b.5 Compiled nonempty instances (at `5bce253`; `python3 -I instidx2.py Proc.lean`: theorem @ `example` line ranges)
```
ProcInst: lines 920-1124
gueLproc_nonneg @949-951 | gueDproc_nonneg @953-955 | gueLproc_continuousOn @957-960 | gueDproc_continuousOn @962-965 |
gueLproc_le @967-971 | gueDproc_le @973-977 | gueLproc_odd @979-983 | gueLproc_time @986-991 | gueDproc_time @993-998 |
gueLoopMax_odd_succ_le @1030-1033 | gueLoopMax_four_mul_le @1035-1037 | gue_inv_W_le_loopMax @1044-1050,1054-1063 |
norm_egtNGUE_le @1118-1120 | gueDev_succ_le @1001-1003,1005-1007
```
Data: `sz0` at `n = 0` (`d = 3`, `L = 4`, `W = 32`), `E = 0`, `t₀ = 9/10`, `t₁ = (1 - ouZeta (1/20)) · 9/10`, `K = 4`, `δ = gueDelta sz0 (1/2)`, every `ω`; tent/interp on `t₁ = 4/5`, `t₀ = 9/10`, `K = 4` (`norm_num`); loop facts at `H = 1` on `Vtx 3 3 2`, `z = I`. Excerpts:
```lean
example (ω : PathΩ SizesInst.sz0) :
    gueLproc SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 2
        (gridTime t1c t0c Kc 0 4) ω =
      gueLmax SizesInst.sz0 Ec t1c t0c Kc 0 2
        (min 4 (gueStop SizesInst.sz0 Ec t1c t0c Kc (gueDelta SizesInst.sz0 (1 / 2)) 0 ω)) ω :=
  gueLproc_time SizesInst.sz0 Ec t1c t0c Kc _ 0 2 4 t1c_le le_rfl ω
example (ω : PathΩ SizesInst.sz0) :=
  gueDev_succ_le SizesInst.sz0 Ec t1c t0c Kc 0 0 (by norm_num [Ec]) t1c_le (by norm_num [t0c])
    (by norm_num [Kc]) ω
example {M : Matrix (Idx 3 3 4) (Idx 3 3 4) ℂ} (hM : M.IsHermitian)       -- g = 1, L²(1-u) = 1/3
    (hΩ : RBM.Green.GoodEvent (RBM.Green.greenBlk 3 3 4 0 (26 / 27) M true) (mE 0) (1 / 2)) :
    (((4 : ℕ) : ℝ)⁻¹) ^ 3 ≤
      2 * ((3 : ℕ) : ℝ) ^ (3 - 2) * (1 : ℝ) ^ 2 *
        RBM.Ind.loopMax 3 3 4 (blockMat 3 3 4 M) (zt 0 (26 / 27)) 2 :=
  gue_inv_W_le_loopMax hM (by norm_num) (by norm_num) (by norm_num) hΩ
    (by rw [mE_zero_im])
example : (((2 : ℕ) : ℝ)⁻¹) ^ 3 ≤                                        -- every hypothesis discharged
    2 * ((3 : ℕ) : ℝ) ^ (3 - 2) * (3 : ℝ) ^ 2 *
      RBM.Ind.loopMax 3 3 2 (blockMat 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) (zt 0 0) 2 :=
  gue_inv_W_le_loopMax (L := 3) (W := 2) (E := 0) (u := 0) (g := 3) (δ := 0)
    Matrix.isHermitian_zero (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [RBM.Green.greenBlk_time_zero (by norm_num)]
      intro x y
      by_cases h : x = y <;> simp [h])
    (by rw [mE_zero_im]; norm_num)
-- egt_hB below (egt_hε: ‖avgErr 3 3 2 0 (1/2) M σ a‖ ≤ 3, same pattern), proved for every Hermitian M
private theorem egt_hB {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 I2.length) (b : Zd 3 3) :
    ‖loopL 3 3 2 (blockMat 3 3 2 M) (zt 0 (1 / 2)) (I2.cutGlue k b)‖ ≤ 1 / 8 := by ...
example {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian) :
    ‖egtNGUE 3 3 2 0 (1 / 2) M I2‖ ≤ (I2.length : ℝ) * (((2 * 3) ^ 3 : ℕ) : ℝ) * 3 * (1 / 8) :=
  norm_egtNGUE_le 3 2 0 (1 / 2) M I2 (egt_hε hM) (egt_hB hM)
```

### b.6 Name-clash grep, port sources, leftover `d = 2` tokens, section line counts
```
$ grep -rnE "\b(<25 new public names>|gueKproc_detDom|ProcInst)\b" RBM3D --include="*.lean" --exclude-dir=Probe | grep -v "^RBM3D/Universality/GUEPhase/Proc.lean" | wc -l
0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h -- RBM2D/Universality/GUEPhase/Proc.lean ; git -C ../RBM2D --no-optional-locks log -1 --format=%h
81fca44
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat 81fca44 HEAD -- RBM2D/Universality/GUEPhase/Proc.lean   # (empty output = file unchanged since the port source)
(empty)
$ grep -nE "Z2|BlockIndex|spectralZ|spectralM|gloop |d\.L n|d\.size|PathΩ d" Proc.lean | grep -v "^3[6-9]:\|^4[0-2]:"   # d = 2 tokens outside the docstring (lines 36-42)
545:  have him : 0 < (mE E).im := spectralM_im_pos hE
546:  have hzeq : (zt E u).im = (1 - u) * (mE E).im := spectralZ_im E u
1059:  rw [spectralZ_im, mE_zero_im]; norm_num
$ grep -n "^end \|^end$" Proc.lean   # file length after each section
68:/-! ### Definitions -/ 259:end GueInterpHelpers 293:end GueConstZero 388:end GueTriangle 394:/-! ### Structural facts of the stopped processes -/ 478:/-! ### Structural facts on the loop maxima (R6a, R6b), the Ward lower bound (A3) -/ 576:end LoopMaxFacts 666:end EgtBound 897:end DevStep 899:end RBM.Univ.GUEPhase 1109:end Egt 1111:end RBM.Univ.GUEPhase.ProcInst 1113:end 
$ wc -l Proc.lean
    1113
```

### b.7 Narrative
1. Scope. Port of RBM2D `Universality/GUEPhase/Proc.lean:1-860` at `81fca44` (b.6: unchanged up to RBM2D HEAD `9e0f275`) into the new file `RBM3D/Universality/GUEPhase/Proc.lean`, 1113 lines (ticket estimate 900 / 1050 / 1450, stop rule 1500 not reached; per-section counts in b.6). `:862-1424` (`gueKproc_detDom`) is not ported (T2323). Only that file is committed (b.1); no registry line, no new `Prop`, no hypothesis added to a target, no pinned signature changed.
2. Definitions and pins. The eleven definitions were copied from check lines 96-150; b.4(a) shows them equal to the file's after whitespace normalisation, docstrings included. The three pinned theorems are the check section-3 statements: in b.4(b) each check `Prop` is closed by the file theorem applied to `sz`, without unfolding or `rfl` rewrites (the two copies of the definitions are defeq).
3. Renaming. A Python script (`conv.py`, scratch dir) applied the check-file rules to source lines 112-463 and 642-860; lines 465-640 (loop-maximum facts, Ward bound, `𝓔^{(G̃)}` bound) and the helper `Proc_norm_green_le` are by hand. b.6 lists the leftover `d = 2` tokens outside the module docstring: only the merged lemma names `spectralM_im_pos`, `spectralZ_im`.
4. Dimension-sensitive statements (as (a)(i)).
   - `gue_inv_W_le_loopMax`: `inv_N_le_maxLoopPM` gives `Im m / (2 N η) ≤ maxLoopPM`, `N = (W L)^d`, `η = (1-u) Im m`; the proof rewrites `((W L)^d : ℕ) = W^d L^d` and shows `(W⁻¹)^d = 2 L^d (1-u) · [Im m / (2 N η)]` (`field_simp`), so `hell : L^d (1-u) ≤ 1` and the conclusion is `(W⁻¹)^d ≤ 2 L₂` (Correction C1 of (a); see (d), T2322a).
   - `norm_egtNGUE_le`: `SBgue d L` has entries `(L^d)⁻¹` (`SBgue_apply`), each label sum has `L^d` terms (`card_Zd`), the prefactor is `W^d`: `W^d · (L^d · L^d) · L^{-d} = (W L)^d`.
   - The `^ 2` that remain are dimension-free: `loopMax²` in `gueLoopMax_*`, `η⁻²` in `gueDev_succ_le`, the tent square in `Proc_gueInterp_sqrt_mul_le`, the Cauchy-Schwarz square in `Proc_opNorm_le_sum_norm`.
5. Names without an RBM3D twin: `RBM.Gauss.norm_green_le` is the private `Proc_norm_green_le` (from `norm_Gsig_le_inv_eta`, the route of `Green/IBPPoly.lean:411`); `pmLoop a b` is `loopOf ![true,false] ![a,b]` via `RBM.Green.loopPM`, `loopFine`, `loopM_eq_loopL` (in `Proc_maxLoopPM_le_loopMax`); `RBM.Ind.LLf …` is `loopL d L W (blockMat d L W M) (zt E u) …`; `ZMod.card` is `card_Zd`; `isUnit_sub_smul_one_of_im_ne_zero` is `RBM.Ind.…`.
6. Instances (b.5), `d = 3`. Grid processes: `sz0` at `n = 0` with the `GridCheck` data; `gueDev_succ_le` at `k = 0` and `k = 3`, `gueLproc_time` at `k = 4 = K 0`; loop-maximum facts at `H = 1` on `Vtx 3 3 2`, `z = I`.
   - Ward bound, nondegenerate: `L = 3`, `W = 4`, `E = 0`, `u = 26/27` (`L^d (1-u) = 1`), `δ = 1/2 = Im m / 2`. `hΩ` (the entry local law of `M`, the consumer's input) stays a hypothesis of the example, as (a)(ii) prescribes; every other hypothesis is discharged. Second Ward instance, all hypotheses discharged (`M = 0`, `u = 0`, `δ = 0`, `greenBlk_time_zero`) but with `L = 1` (one block): it only certifies that the hypothesis set is satisfiable and is degenerate in `L`.
   - `norm_egtNGUE_le`: `L = 3`, `W = 2`, `E = 0`, `u = 1/2`, loop `⟨[+,-],[0,0]⟩`, every Hermitian `M`; `hε` (`ε = 3`) and `hB` (`B = 1/8`) are proved (`split_norm_trace_mul_Eblk_le`, `norm_Gsig_le_inv_eta`, `norm_gloop_le_of_le_abs_im`), not kept as example hypotheses as (a)(ii) allowed.
7. No (a′) section: nothing in (a) was found wrong; the three `d ≥ 3` statements of (a)(i) compile as stated there.

## (c) Verified Mathlib names (all resolved by the build of b.1; extracted by `grep -ohE` over the file)
```
Complex.I Complex.norm_natCast Complex.norm_real EuclideanSpace.norm_eq Finset.card_univ Finset.Icc Finset.Icc_eq_empty Finset.mem_Icc
Finset.mem_insert Finset.mem_range Finset.range Finset.sum_add_distrib Finset.sum_congr Finset.sum_const Finset.sum_eq_single Finset.sum_insert
Finset.sum_le_sum Finset.sum_mul Finset.sum_nonneg Finset.sum_range_succ Finset.sum_sq_le_sq_sum_of_nonneg Finset.sup'_le Fintype.card
Matrix.isHermitian_one Matrix.isHermitian_zero Matrix.isUnit_iff_isUnit_det Matrix.l2_opNorm_toEuclideanCLM Matrix.mul_assoc Matrix.mul_nonsing_inv
Matrix.mul_one Matrix.mul_sub Matrix.mulVec Matrix.nonsing_inv_eq_ringInverse Matrix.nonsing_inv_mul Matrix.Norms Matrix.one_mul Matrix.smul_mul
Matrix.sub_apply Matrix.sub_mul Matrix.trace Matrix.trace_smul Matrix.trace_sub Nat.card_Icc Nat.cast_le Nat.cast_nonneg Nat.eq_zero_or_pos
Nat.pos_of_ne_zero Nat.zero_min PiLp.norm_apply_le Real.exp Real.exp_le_one_iff Real.iSup_nonneg Real.le_sqrt_of_sq_le Real.norm_eq_abs
Real.rpow_pos_of_pos Real.sqrt Real.sqrt_le_sqrt Real.sqrt_mul Real.sqrt_nonneg Real.sqrt_sq Real.sqrt_zero Real.sum_sqrt_mul_sqrt_le Set.Finite
Set.finite_range Set.Icc
```
Unqualified (open-namespace) names used, also resolved by the build: `ciSup_le`, `le_ciSup`, `norm_sum_le`, `norm_sub_le`, `norm_add_le`, `norm_mul_le`, `norm_smul`, `continuous_finsetSum`, `continuousOn_const`, `inv_pow`, `mul_pow`, `pow_ne_zero`, `toEuclideanCLM`. `Matrix.Norms` above is the scoped namespace `Matrix.Norms.L2Operator`, not a declaration. Names verified absent: none was searched for (no Mathlib name was missing).

## (d) Open issues and paper-delta candidates
- **T2322a (paper-delta candidate, statement difference; reworded in repair round 1).** `gue_inv_W_le_loopMax` carries `hell : (L:ℝ)^2 * (1 - u) ≤ g^2` (the `ellT_eq_L` condition, `Bootstrap.lean:148`) and concludes `((W:ℝ)⁻¹)^d ≤ 2 L^{d-2} g² L₂`; `[YY_25]`/RBM2D (`Proc.lean:519`) have `W^{-2} ≤ 2 L₂` under `L²(1-u) ≤ 1`. The factor `L^{d-2} g²` comes from `inv_N_le_maxLoopPM` (`W^{-d} ≤ 2 L^d (1-u) maxLoopPM`) and `L^d ≤ L^{d-2} L²` (`L ≥ 1`); at `d = 2`, `g = 1` it is the RBM2D statement.
- Consumer obligation (not checked here): UN-48/49 (the `HypB` analogue, RBM2D `HypB.lean:112,170-174`) must supply `δ ≤ Im m / 2` and `L² (1 - t₁) ≤ g²`.
- The local paper has no GUE-phase section (`1_2_Intro_model_result.tex:566-570` delegates to [Xu:2024aa], [DYYY25]); the `d ≥ 3` statements of this file are checked by Lean and by the numerics of (a)(ii), not against a paper equation.
- Ward instances (b.5): `L = 3, W = 4, u = 26/27` with `hΩ` kept; `L = 3, W = 2, M = 0, u = 0, δ = 0, g = 3` with every hypothesis discharged.
- Downstream: T2323 (UN-31b `GUEPhase/ProcK`), UN-32, UN-33. Registry: none (no new `Prop`). Root import for the hub: `import RBM3D.Universality.GUEPhase.Proc`.

## Repair (round 1, audit `T2322-audit.md` §7; written Thu Oct  8 04:41:32 UTC 2026; prover model claude-opus-5-5; commit `5bce253` on `t/T2322`)
```
$ lake build RBM3D.Universality.GUEPhase.Proc     # Thu Oct  8 04:38:46 UTC 2026
Build completed successfully (3756 jobs).          # 0 lines matching "GUEPhase/Proc" or "error"
$ lake env lean axioms.lean                         # 25 public declarations
axioms exit 0 ; 25 x "depends on axioms: [propext, Classical.choice, Quot.sound]" ; other lines: 0
$ python3 -I defcmp.py | tail -1 ; lake env lean check_equal.lean   (as b.4)
ALL EQUAL: True ; check_equal exit 0 ; lines containing 'error': 0
$ lake build ; lake env lean registry.lean          # Thu Oct  8 04:39:28 UTC 2026 (registry.lean as b.1)
Build completed successfully (4127 jobs). ; registry exit 0
axiom audit: 9092 theorems, 2956 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ git diff --stat main...t/T2322
 RBM3D/Universality/GUEPhase/Proc.lean | 1126 +++++++++++++++++++++++++++++++++
$ grep -rnw gue_inv_W_le_loopMax RBM3D --include='*.lean' | grep -v GUEPhase/Proc.lean | wc -l   # -> 0
```
- Required 1: `gue_inv_W_le_loopMax` restated exactly as the audit's form (b.3); no `hd` added (`L^d ≤ L^{d-2} L²` holds for every `d` since `L ≥ 1` and `d ≤ (d-2)+2` in ℕ). The old `L^d(1-u) ≤ 1` form is not kept.
- Required 2: `L = 3` instance with every hypothesis discharged replaces the `L = 1` one (b.5, `Proc.lean:1054-1063`).
- Required 3: above; b.3, b.5, T2322a updated. b.1, b.2, b.4, b.6 and the Ward items of b.7 (4, 6) describe commit `0d695a8`; for the Ward lemma, b.3/b.5/(d) and this section are current. (a)(i) Correction C1 and the (a) Ward rows describe the replaced form.
- Mathlib names added: `pow_le_pow_right₀` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:501`), `pow_add`; resolved by the build.
