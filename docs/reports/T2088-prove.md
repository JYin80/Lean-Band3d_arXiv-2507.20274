Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 22:58:14 UTC 2026

Sources: `git -C ../RBM2D show c9a24cf:RBM2D/Green/{IBPPoly,LDEQuadInst}.lean`; `RBM3D/Green/{LDEQuad,LDEQuadT,LDE,EntryCore,EntryDom}.lean`, `RBM3D/Gauss/{FineModel,DominationAt,Stein}.lean`, `RBM3D/Defs/{Sizes,Block,StochDomAt}.lean`, `RBM3D/Test/Axioms.lean:90`.

### (i) Exponent table

Targets in mathematics. (T1) `gaussIBP sz : GaussIBP sz` for every `sz : Sizes d` (`LDEQuad.lean:302`, two fields): `stein`: for `g, g'` tame (continuous, finitely dependent, `‖g‖ ≤ C polyW I ^ n`) with `∂_{ω_c} g = g'` along coordinate `c`: `E[ω_c g] = v_c E[g']`, `v_c = seqGvar sz c`, law `seqP sz = law (seqGvar sz)` (`Sizes.seqP_eq_law`, `DominationAt.lean:663`); `polyInt`: `E[(1+Σ_{c∈I}|ω_c|)^n] < ∞`. (T2) `stochDom_ldeQuad`: for `sz.SizeTendsto`, `κ > 0`, `|E n| ≤ 2-κ`, `0 ≤ t n < 1`: `sz.PrecPT (U := Vtx d L_n W_n) (ldeQuadLHS (blockMat H) (greenBlk E t H true) (svar d L_n W_n (lam n)) (t n) i) (ldeQuadRHS (svar …) (greenBlk …) i)` (the `hLquad` text of `EntryDom.diag_bound_stochDom`, `EntryDom.lean:1010`), `H = sz.seqHflow n (t n)`.

| item | value / form | constraint | slack |
|---|---|---|---|
| `d` | parameter, no `3 ≤ d` used by (T1), (T2) | none: both files use `d` only through `Idx d L W`, `Vtx d L W`, `svar`, `sz.size n = (W L)^d` | none needed |
| `GaussIBP` variance `v_c` (replaces RBM2D's `1/(5W²)`-type profile) | `seqGvar sz c = gvarF d L_n W_n (lam n) c` = `svarF` (diag) or `svarF/2` (off-diag), `svarF = W^{-d} SBR(blk i - blk j)`, diag `W^{-d}(1+2dg²)⁻¹` | `v_c ≥ 0`; `v_c = 0` occurs (blocks at `ℓ¹`-distance `≥ 2`) | `stein` must hold with `v_c = 0` (both sides `0`: `gaussianReal 0 0` is Dirac `0`): `integral_mul_gaussianReal_complex_int` (IBPPoly:182) has no `var ≠ 0` hypothesis; `d=3,L=3,W=2`: 160 of 216 row coordinates have `v_c = 0` (script 3) |
| `stein` integrability side conditions | on `seqP ⊗ N(0,v_c)` with `p ↦ g(update c p)`: majorant `C 2^n (polyW I p.1^n + |p.2|^n)`; for `p.2 · g`: `C 2^n (polyW^n |p.2| + |p.2|^{n+1})` | `polyW I (update c p) ≤ polyW I p.1 + |p.2|`, `(a+b)^n ≤ 2^n (a^n+b^n)` (`a,b ≥ 0`); need `polyInt` and Gaussian `E|x|^k < ∞` | exact, no loss; `g'` uses its own `(I', n', C')`; `C` replaced by `max C 0` |
| `polyInt` | `E polyW I ^ n < ∞` for every finite `I`, `n` | induction on `|I|`: `polyW (insert c I) = polyW I + |ω_c|`, `E|ω_c|^k < ∞` (`LDE.lean:1034` `integrable_pow_coord`) | exact |
| resampling | `(seqP ⊗ N(0,v_c)).map (upd c) = seqP` | `GaussianProduct.map_update` (`DominationAt.lean:517`), measurable `upd c`, `upd_self`, `upd_of_ne` (renames of RBM2D `update`, `update_self`, …) | exact |
| `hwConst q` | `((2q+1)(4q+2))^{q+1}`; `q=2`: `125000` | `E|Q|^{2(q+1)} ≤ hwConst q · E V_q^{q+1}` (`RowChaos.mom_le_momVpow`, `LDEQuadT.lean:1010`, hypothesis `GaussIBP sz` := `gaussIBP sz`) | independent of `d, W, L, n, lam` |
| `u = t n` | `0 ≤ u ≤ 1` | `u² ≤ 1` so `λ = s/u² ≥ s`; `u = 0` ⇒ chaos `0` (empty failure set) | `t = 1/2`: `u² = 1/4` |
| `Im z_t`, `z_t = E + (1-t) m_E` | `(1-t) √(4-E²)/2 > 0` | `\|E\| ≤ 2-κ`, `t < 1`: `zt_im_ne_zero` (`EntryDom.lean:79`); `‖G^{(i)}‖ ≤ 1/Im z_t` | `E=0,t=1/2`: `Im z = 1/2`, bound `2` (observed max `1.405`, script 2) |
| `τ, D`; `q` | `q = ⌈(D+1)/τ⌉` | `τ q ≥ D+1` | `τq-(D+1) ≥ 0`, exponent `e = τ(q+1) - D ≥ 1 + τ > 0` |
| threshold in `N = sz.size n = (W L)^d` | `∀ᶠ n`: `hwConst q ≤ N^{e}` (`eventually_le_rpow`, `Defs/Domination.lean:68`) | `N → ∞` = `hsz : SizeTendsto` (no `𝔠`, `𝔡`, bandwidth) | `sz0` (`N = 2^21 (n+1)^18`): `n0(τ=1,D=1)=0`, `(1,3)=0`, `(1/2,1)=1`, `(1/10,1)=2449` (script 4) |
| tail with deterministic `s` | `P(s·RHS < LHS) ≤ hwConst q / s^{q+1}` for `s > 0`, `0 ≤ u ≤ 1` | `s = N^τ`: `hwConst q / N^{τ(q+1)} ≤ N^{e}/N^{τ(q+1)} = N^{-D}` | slack `N^e / hwConst q ≥ 1` eventually |
| `L ≥ 3`, `W ≥ 1` | `sz.three_le_L`, `sz.W_pos` | row sum `Σ_j svarF i j = 1` (`2d` distinct neighbours) | `L=3` tight, row sums `1.0` (script 2) |

`d = 2` tokens of the two sources (portmap: `IBPPoly` none; `LDEQuadInst` `Z2/zdist2:1`): `grep -nE "Z2|zdist2|1 / 5|W \^ 2|L \^ 2"` on `LDEQuadInst` at `c9a24cf` gives only line 498, a docstring ("`Idx L W = Z2 (W * L)`"); replaced by `Zd d (W L)` in the docstring. Every `^ 2` in the code is a square (`‖·‖²`, `u²`, `lam²`), dimension-free. The only changes of declarations: `Sblk2 L W` → `svar d L W (sz.lam n)`, `BlockIndex` → `Vtx d L W`, `spectralZ` → `zt`, `Idx L W` → `Idx d L W`, `d : Sizes` → `sz : Sizes d`, `PerTimeDomAt (seqP d) d.size` → `sz.PrecPT`, `Ind.SizeTendsto` → `sz.SizeTendsto`, the `svar` profile `S_ik` enters `ldeQuadRHS`/`LHS` only as the profile argument; the chaos' coordinate variance is `seqGvar (rowCoord …) = svarF i k /2` (`fineModel_gvarF_offDiag`, FineModel:260), so `E|h_k|² = u · S_ik` for any profile. RBM2D `GaussIBP` structure (2 fields) = merged `GaussIBP sz`: same fields, so `gaussIBP` discharges the registered owed `RBM.Green.GaussIBP` (`Test/Axioms.lean:90`); that registry line can go after this merge (cleanup ticket). No new registry line is expected (no new predicate that a deterministic lemma takes as hypothesis).

Verdict statements: nothing in either target depends on an exponent of `d`; `d` enters through `N = (WL)^d` only via `N → ∞`.

### (ii) One concrete nondegenerate instance

Instance: `d = 3, L = 3, W = 2` (`N = 216`), `g = 1/2`, `E = 0`, `t = u = 1/2` (`z_t = i/2`, `κ = 1`, `|E| ≤ 1`), row `i = 0`. Hypotheses of (T2): `SizeTendsto` (checked at `sz0`, `N = 2^21 (n+1)^18 → ∞`), `κ=1>0`, `|0| ≤ 1`, `0 ≤ 1/2 < 1`. Hypotheses of (T1): none (`sz`-independent); tame test function `f = x³` (continuous, finitely dependent, `|x³| ≤ polyW{c}^3`). Checks: (1) Stein `E[x·x³] = v E[3x²] = 3v²` at the diagonal coordinate `v = 0.05` and at a same-block off-diagonal coordinate `v = 0.025`, `10^5` samples; (2) the row chaos `Q = Σ_{k,l≠0} H_{0k} G^{(0)}_{kl} H_{l0} - t Σ_k S_{0k} G^{(0)}_{kk}` on the full `216×216` model (`3000` Hermitian samples with the `svarF` profile): `E|Q|^6 ≤ hwConst 2 · E V_q^3` (`V_q = u² Σ S_{0k}|G^{(0)}_{kl}|² S_{l0}`), tail bound; (3) zero-variance coordinates; (4) thresholds `n0` at `sz0`.

```
$ SCR=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2088; cd $SCR && python3 chk.py
N = 216  row sums of S (min,max) = 1.0 1.0  S_xx = 0.05  1/20 = 0.05
Stein diag coord (0,0,true): var=0.05000 E[x f]=7.441908e-03 var*E[f']=7.498319e-03 exact 3var^2=7.500000e-03 MC se=7.5e-05
Stein same-block off-diag (0,1,true): var=0.02500 E[x f]=1.867817e-03 var*E[f']=1.871766e-03 exact 3var^2=1.875000e-03 MC se=1.9e-05
hwConst(2) = 125000
max |G^(i)_kl| over samples = 1.4050339479253395  <= 1/|Im z| = 2.0
E[LHS]/E[u^2 RHS] = 1.001937403571598 (expected ~ 1)
q=2: E|Q|^6 = 1.5272e-05; hwConst*E[V^3] = 1.1140e-01; ratio = 1.371e-04 (<= 1 required)
s=200.0: empirical P(s*RHS < LHS) = 0.0000; bound hwConst/s^3 = 0.0156
s=100.0: empirical P(s*RHS < LHS) = 0.0000; bound hwConst/s^3 = 0.1250
$ cd $SCR && python3 zero.py
blocks by periodic l1 distance from 0: {0: 1, 1: 6, 2: 12, 3: 8}  total 27
zero-variance blocks: 20 of 27 -> zero-variance fine coordinates in row 0: 160 of 216
Stein at a zero-variance coordinate: x=0 a.s., E[x f(x)] = 0 = 0 * E[f'(x)] (gaussianReal 0 0 = Dirac 0)
$ cd $SCR && python3 thr.py
size(0) = 2097152 = 2^21 (n+1)^18: 2097152
tau=1 D=1: q=2, hwConst q=1.250e+05, exponent tau(q+1)-D=2, slack tau*q-(D+1)=0, n0=0, check at n0: log hw=11.74 <= 29.11
tau=1 D=3: q=4, hwConst q=1.116e+11, exponent tau(q+1)-D=2, slack tau*q-(D+1)=0, n0=0, check at n0: log hw=25.44 <= 29.11
tau=1/2 D=1: q=4, hwConst q=1.116e+11, exponent tau(q+1)-D=3/2, slack tau*q-(D+1)=0, n0=1, check at n0: log hw=25.44 <= 40.55
tau=1/10 D=1: q=20, hwConst q=1.144e+74, exponent tau(q+1)-D=11/10, slack tau*q-(D+1)=0, n0=2449, check at n0: log hw=170.53 <= 170.53
```

Reading: Stein: the sample `E[x f]` is within `0.8 se` of the exact `3v²` at the diagonal coordinate (`7.44e-3` vs `7.50e-3`, `se 7.5e-5`) and within `0.4 se` at the off-diagonal one (`1.868e-3` vs `1.875e-3`, `se 1.9e-5`). The Monte-Carlo `E[LHS]/E[u²RHS] = 1.002` confirms `ldeQuadRHS = u^{-2} V_q` as used by `RowChaos.Vq_eq_ldeQuadRHS`; the moment bound holds with ratio `1.4e-4`, and `hwConst/s^{q+1}` dominates the empirical tail. `Im z_t = 1/2` is the value from `zt E t = E + (1-t) mE E`, `mE 0 = i` (`Defs/Semicircle.lean:38`). External hypothesis: none (the `GaussIBP` is proved here; the instance's `SizeTendsto` is the explicit limit `N = 2^21 (n+1)^18 → ∞`, computed above for `sz0`, `sz0.L n = 4(n+1)`, `sz0.W n = (2(n+1))^5`, `Defs/Sizes.lean:260-263`).

### Verdicts

- `gaussIBP` (T1, `GaussIBP sz` for every `sz : Sizes d`): **PASS**. Dimension-free; `v_c = 0` handled by the complex one-dimensional Stein with no `var ≠ 0`; integrability side conditions are closed by the majorants above.
- `stochDom_ldeQuad` (T2) and the other ported declarations (`minorRes`, `modelChaos`, `modelChaosEps`, `hwConst`, `mom_modelChaosEps_le`, `meas_lt_normSq_chaos_le`, the private `LDEQuadInst_*` relabelling lemmas): **PASS**. No `d = 2` exponent; `hwConst q` and the `N^{τ(q+1)-D}` threshold are `d`-free; no statement is false at `d ≥ 3`. Dropped declarations: none planned (the portmap notes of row 50 were not re-read for an "unused" mark; the prover reports any drop).

## (b) Script output — Sat Oct  3 23:07:16 UTC 2026

Branch `t/T2088`, commit `6a1e786` (author Jun Yin <321276894+JYin80@users.noreply.github.com>); file `RBM3D/Green/IBPPoly.lean`, 1157 lines.

```
$ lake build RBM3D.Green.IBPPoly   (tail; 14 warnings in this file, all "line exceeds 100 characters"; 0 errors)
Build completed successfully (3334 jobs).
exit=0
$ lake build   (full library, root #assert_rbm_axioms; the root does not yet import the new module)
non-vacuity certificates: 4 of 95 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3824 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Green/IBPPoly.lean  -> no match (exit 1)
$ git diff --name-only main...t/T2088
RBM3D/Green/IBPPoly.lean
```

### Axioms (`#print axioms` of all 48 public declarations, script `axioms.lean`)
```
$ lake env lean axioms.lean | sort | uniq -c  (messages with the axiom list stripped of the declaration name)
  48 depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axioms.lean | grep -E "gaussIBP'|stochDom_ldeQuad'"
'RBM.Green.gaussIBP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeQuad' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Registry pre-check (ST1-COMMON item 8): scratch `import RBM3D`, `import RBM3D.Green.IBPPoly`, `#assert_rbm_axioms`
```
$ cat precheck.lean
import RBM3D
import RBM3D.Green.IBPPoly

#assert_rbm_axioms
$ lake env lean precheck.lean   -> exit 0; first lines of the output:
axiom audit: 2779 theorems, 1107 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
...
14:  RBM.Green.GaussIBP: 23 [no certificate]
108: RBM.Green.GaussIBP,
```
No new registry line: no new `Prop`-valued predicate is taken as a hypothesis by a deterministic lemma; `Test/Axioms.lean` is untouched. The existing line for `RBM.Green.GaussIBP` (`Test/Axioms.lean:90`, "proved by S1-19") can go once this merges (`gaussIBP` discharges it); the cleanup ticket removes it.

### Target statements (extracted by script from `RBM3D/Green/IBPPoly.lean`)
```
$ awk (theorem gaussIBP ... := by)
theorem gaussIBP (sz : Sizes d) : GaussIBP sz := by
$ awk (theorem stochDom_ldeQuad ... := by)
theorem stochDom_ldeQuad (sz : Sizes d) {κ : ℝ} (hκ : 0 < κ) (hsz : sz.SizeTendsto)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true)
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i)
      (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) i) := by
```
RBM2D at c9a24cf, same extraction (`Green/IBPPoly.lean:299`, `Green/LDEQuadInst.lean:641`):
```
theorem gaussIBP (d : Sizes) : GaussIBP d := by
theorem stochDom_ldeQuad (d : Sizes) {κ : ℝ} (hκ : 0 < κ) (hsz : RBM.Ind.SizeTendsto d)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    PerTimeDomAt (Sizes.seqP d) d.size (U := fun n => BlockIndex (d.L n) (d.W n))
      (fun n i ω => ldeQuadLHS (blockMat (Sizes.seqHflow d n (t n) ω))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true)
        (Sblk2 (d.L n) (d.W n)) (t n) i)
      (fun n i ω => ldeQuadRHS (Sblk2 (d.L n) (d.W n))
        (greenBlk (d.L n) (d.W n) (E n) (t n) (Sizes.seqHflow d n (t n) ω) true) i) := by
```
The pin `GaussIBP sz` is exactly `RBM.Green.GaussIBP` of `Green/LDEQuad.lean:302` (two fields, `stein`, `polyInt`; no change to it); `stochDom_ldeQuad` has the text of `hLquad` of `diag_bound_stochDom` (`Green/EntryDom.lean:1010`).

### Compiled nonempty instances (`RBM.Green.IBPInst`, `RBM3D/Green/IBPPoly.lean:1086-1155`; `sz0`, `d = 3`, `E ≡ 0`, `t ≡ 1/2`, `κ = 1`)
```
theorem gaussIBP_sz0_polyInt :
    Integrable (fun ω : Sizes.SeqΩ sz0 =>
      polyW ({c0, c1} : Finset (Sizes.SeqCoord sz0)) ω ^ 2) (Sizes.seqP sz0) :=
  (gaussIBP sz0).polyInt _ 2
theorem gaussIBP_sz0_stein_cubic :
    ∫ ω, (ω c0 : ℂ) * (ω c0 : ℂ) ^ 3 ∂(Sizes.seqP sz0)
      = (Sizes.seqGvar sz0 c0 : ℝ) * ∫ ω, (3 : ℂ) * (ω c0 : ℂ) ^ 2 ∂(Sizes.seqP sz0) :=
  (gaussIBP sz0).stein c0 (fun ω => (ω c0 : ℂ) ^ 3) (fun ω => 3 * (ω c0 : ℂ) ^ 2)
    ((Tame.coord c0).pow 3) ((Tame.const 3).mul ((Tame.coord c0).pow 2)) (fun ω => by
      have h := (RowChaos.hasDerivAt_ofReal_id (ω c0)).fun_pow 3
      simpa only [Function.update_self, Nat.cast_ofNat, mul_one] using h)
theorem stochDom_ldeQuad_sz0 :
    sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ldeQuadLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true)
        (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n)) (1 / 2) i)
      (fun n i ω => ldeQuadRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) i) :=
  stochDom_ldeQuad sz0 (κ := 1) one_pos sz0_tendsto (E := fun _ => 0) (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
example : GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  diag_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) one_pos stochDom_ldeRow_sz0
    stochDom_ldeCol_sz0 stochDom_ldeQuad_sz0 stochDom_normSq_Hflow_diag_sz0
```
`gaussIBP`: `polyInt` at `{c₀, c₁}` (coordinates of sizes 0 and 1), and `stein` at `c₀` (positive variance `seqGvar_sz0_c0_pos`, `= 32⁻³ (1 + 6/4096)⁻¹`) with the unbounded cubic `g = ω³`. `stochDom_ldeQuad`: hypotheses `SizeTendsto` (`sz0_tendsto`), `κ = 1`, `|0| ≤ 1`, `0 ≤ 1/2 < 1`, all discharged; the `example` feeds it, with the three other proved inputs, into `diag_bound_stochDom`, so `GiiOmegaSeq sz0 … 1` has no hypothesis left. `hwConst_two : hwConst 2 = 125000` matches the preflight table.

### Name-clash grep of the 48 new public names (against `RBM3D/` of this worktree and of the main worktree)
```
$ for n in <48 names>; do grep -rn -E "^(private |protected )?(noncomputable )?(theorem|def|lemma|abbrev|structure|instance) ([A-Za-z.]*\.)?$n( |$)" RBM3D --include=*.lean | grep -v Green/IBPPoly.lean; done
(no output:        0 bytes)
```

### Ports (RBM2D at c9a24cf; RBM2D HEAD 9e0f275)
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/IBPPoly.lean RBM2D/Green/LDEQuadInst.lean
 RBM2D/Green/IBPPoly.lean     | 114 ++++-----------------------------------
 RBM2D/Green/LDEQuadInst.lean | 124 ++++---------------------------------------
 2 files changed, 20 insertions(+), 218 deletions(-)
$ public declarations (name list by script): RBM2D 42 (IBPPoly 10 + LDEQuadInst 32), RBM3D 48
in RBM2D, not in RBM3D:
in RBM3D, not in RBM2D:
gaussIBP_sz0_polyInt
gaussIBP_sz0_stein_cubic
hwConst_two
seqGvar_sz0_c0
seqGvar_sz0_c0_pos
stochDom_ldeQuad_sz0
$ grep -nE "Z2|zdist2|1 / 5|W \^ 2|L \^ 2" IBPPoly.lean LDEQuadInst.lean   (RBM2D c9a24cf)
LDEQuadInst.2d.lean:498:`blockMat`, `greenBlk`, `Sblk2`; the model lives on `Idx L W = Z2 (W * L)`.  These are the
```

### Narrative

- Both RBM2D sources (`Green/IBPPoly.lean`, 392 lines, `Green/LDEQuadInst.lean`, 701 lines, at `c9a24cf`) are ported into the single sole writable file `RBM3D/Green/IBPPoly.lean`. All 42 public RBM2D declarations are present under the same names (script diff above); none is dropped. RBM2D's private check sections (`ibpChk_*`, `chk_*`) are replaced by the `IBPInst` instances at `sz0` (`d = 3`).
- `gaussIBP sz : GaussIBP sz` (`polyInt` = `integrable_polyW_pow`, `stein` = fibrewise argument through `GaussianProduct.map_update`) is the registered owed predicate, with its type unchanged (`Green/LDEQuad.lean:302`). The complex one-dimensional Stein identity of the file has no `var ≠ 0` hypothesis, so coordinates with `seqGvar = 0` (zero-variance entries of `svarF`) are covered.
- `d`-dependence: the ported statements contain no exponent of `d`, `W`, `L`. The only `d = 2` token of the two sources (grep above) is a docstring (`Idx L W = Z2 (W * L)`), rewritten. `d` enters via `Idx d L W`, `Vtx d L W`, `svar d L W (sz.lam n)` and `N = sz.size n = (W L)^d → ∞` (`SizeTendsto`) only; `hwConst q = ((2q+1)(4q+2))^{q+1}` is independent of `d` (`hwConst_two : hwConst 2 = 125000`).
- Residual differences of `stochDom_ldeQuad` against RBM2D (after ST1-COMMON item 2): `d : Sizes` -> `sz : Sizes d`; `RBM.Ind.SizeTendsto d` -> `sz.SizeTendsto`; `PerTimeDomAt (Sizes.seqP d) d.size (U := …)` -> `sz.PrecPT (U := …)` (a `def` equal to it, `Defs/StochDomAt.lean:125`); `BlockIndex` -> `Vtx d`; `Sblk2 L W` -> `svar d L W (sz.lam n)`; `blockMat`, `greenBlk` take `d`. Conclusion text = `hLquad` of `diag_bound_stochDom` (`Green/EntryDom.lean:1010`).
- Chaos side: RBM2D's `Sblk2` profile enters the row chaos only as the profile argument; the chaos works on the fine lattice, so its profile is `svarF d L W (sz.lam n)` and the coordinate variance is `svarF i k / 2` (`gvar_rowCoord`, `Green/RowIndep.lean:502`). `modelChaos_sg` reads `sg k = u * svarF … i k`. The relabelling block-to-fine (`LDEQuadInst_greenBlk_true`, `LDEQuadInst_svar_funext`, `LDEQuadInst_blk_quadLHS/RHS`) follows the private pattern of `Green/LDE.lean:652-700`.
- Dimension-specific replacements outside the table: RBM2D `norm_green_le` / `norm_apply_le` are re-derived from `norm_Gsig_le_inv_eta` and `norm_matrix_entry_le_opNorm` (`Gauss/FlowCalculus.lean`) in `LDEQuadInst_norm_green_apply_le`; `Sizes.seqHflow_zero` is the private `LDEQuadInst_seqHflow_zero`; RBM2D `spectralZ` is `zt`.
- Imports: `RBM3D.Green.{LDEQuadT, LDE, RowIndep, EntryDom}` (merged ST-1 files); never `RBM3D`, never an ST-2 .. ST-6 file. Three public helpers (`add_pow_le_two_pow_mul`, `integral_mul_gaussianReal_int`, `integral_mul_gaussianReal_complex_int`) are new to RBM3D (grep above); the two Gaussian-moment helpers are private copies, as in RBM1D and in `Green/RowIndep.lean`, `Green/LDE.lean`.
- Instances: `polyInt` and `stein` (unbounded cubic test function at a positive-variance coordinate) of `gaussIBP`; `stochDom_ldeQuad_sz0`; the `example` closes `GiiOmegaSeq sz0 … 1` with no hypothesis left. The preflight's Monte Carlo checks (section (a)) were not repeated.

## (c) Verified Mathlib names (compiled in `IBPPoly.lean`)

- Used and compiling: `gaussianReal_of_var_ne_zero`, `gaussianReal_zero_var`, `memLp_id_gaussianReal'`, `integrable_withDensity_iff_integrable_smul'`, `MemLp.integrable_norm_pow'`, `Finset.induction`, `Integrable.mono'`, `Integrable.comp_fst`, `Integrable.comp_snd`, `Integrable.mul_prod`, `integral_prod`, `integral_map`, `integral_const_mul`, `tendsto_measure_iUnion_atTop`, `exists_nat_one_div_lt`, `exists_nat_ge`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_sub`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `HasDerivAt.fun_pow`, `Complex.reCLM.integral_comp_comm`, `Complex.imCLM.integral_comp_comm`, `pow_le_pow_left₀`, `div_le_div₀`, `div_le_div_of_nonneg_left`, `Set.mem_ofPred_eq` (the name that replaces the deprecated `Set.mem_setOf_eq`; the build warned on the old one).
- Absent (grep for a declaration in `RBM3D/` finds none, or the build reports "Unknown identifier/constant"): `GaussianProduct.update`, `GaussianProduct.update_self`, `GaussianProduct.update_of_ne`, `GaussianProduct.measurable_update` (RBM3D has `RBM.Gauss.upd`, `upd_self`, `upd_of_ne`, `measurable_upd`, `Gauss/SteinMatrix.lean:70-78`); `norm_green_le`; `l2_opNorm_mulVec` (as a bare identifier); `RBM.Gauss.Sizes.seqHflow_zero`.

## (d) Open issues and paper-delta candidates

- Paper-delta candidate **T2088a**: the paper takes the quadratic large deviation (4.7) from [YY_25, Lemma 4.2]; here `stochDom_ldeQuad` proves it for the Gaussian flow (statement `hLquad`, constant `hwConst q`, threshold `N^{τ(q+1)-D}`), so `hLquad` of `diag_bound_stochDom` is no longer an input once the caller applies this theorem. No change of any other statement.
- Paper-delta candidate **T2088b**: `GaussIBP sz` (owed in the registry, `Test/Axioms.lean:90`) is now a theorem, `gaussIBP`; the registry line is superfluous; the cleanup ticket removes it. Consumers `Tame.integrable`, `RowChaos.mom_le_momVpow`, `RowChaos.integrable_norm_pow` can now be applied with `gaussIBP sz`.
- Not compiled: an instance at a zero-variance coordinate (the lemma `integral_mul_gaussianReal_complex_int` covers `var = 0` by `gaussianReal_zero_var`, but no `sz0` zero-variance coordinate is exercised; the preflight's script 3 only argues it).
- 14 style warnings in the file (lines longer than 100 characters, inherited from the RBM2D text); no other warning in this file.
- Hub at merge: add `import RBM3D.Green.IBPPoly` after the last `import` of `RBM3D.lean`; `RBM3D/Test/Axioms.lean` is unchanged by this ticket.
