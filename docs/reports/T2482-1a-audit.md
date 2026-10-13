Auditor model: claude-opus-5-5
# T2482 (U U5b) 1a-audit: design gate E, probe step — Tue Oct 13 02:51:54 UTC 2026
Inputs: the ticket; `T2482-prove.md` (a), (a″) (213 lines; (a) is 76 lines); `t/T2482` 0ac2aab8. Worktree: detached
`/Users/junyin/Lean_proof/RBM3D-wt/T2482-1aaudit` (cache `cp -c`). Scratch: `<scratchpad>/T2482/aud/`. I edited no source files.

## 1. Probe compile, axioms, hygiene (audit worktree)
```
$ git diff --stat main...t/T2482
 RBM3D/Probe/T2482Pins.lean | 395 +++++++++++++++++++++++++++++++++++++++++++++
$ lake env lean RBM3D/Probe/T2482Pins.lean; echo "exit $?"        # 02:46:37 UTC
exit 0                                                              (no output lines)
$ lake env lean aud/ax.lean   # probe + 4 examples (∀ d, T2482_LoopHS d := T2482_LoopHS_holds; same for LoopGlue,
                              # LoopHSList; TraceMulLe ∧ TraceMul3Le ∧ TraceProdLe) + 17 "#print axioms RBM.BA.<thm>"
exit 0
17
  17 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^[[:space:]]*axiom" RBM3D/Probe/T2482Pins.lean; echo rc=$?
rc=1
$ lake env lean docs/tickets/checks/T2482-check.lean; echo "check exit $?"; grep -c error check.out
check exit 0
0
```
The 17 theorems are the probe's public `T2482_*` theorems. The probe has 395 lines (limit 400).

## 2. Pins: probe against the check (my own script, `aud/pindiff_aud.py`)
```
$ python3 -I pindiff_aud.py docs/tickets/checks/T2482-check.lean RBM3D/Probe/T2482Pins.lean
check pins 11 probe pins 13
T2482_TraceMulLe identical      T2482_TraceMul3Le identical   T2482_TraceProdLe identical   T2482_LoopHS identical
T2482_SumTheta identical        T2482_BAScalar identical      T2482_BAMatrix identical      T2482_BAEdet identical
T2482_EdetLk identical          T2482_EdetWG identical        T2482_EdetDif identical
probe-only: ['T2482_LoopGlue', 'T2482_LoopHSList']
```
The bundle text (`T2482_BAScalar`, `T2482_BAMatrix`) is unchanged and has no new conjunct, so stop rule 2 does not fire. U5c's
`T2485-check` copies it verbatim (`T2485-check.lean:7-9`, `:145`, `:152`).

## 3. Numerics rerun (`aud/run/`: fresh copies of the scripts; `num.py` and `stab.py` byte-equal to `t/T2459:docs/reports/T2459/`)
```
$ for f in num stab; do git show t/T2459:docs/reports/T2459/$f.py | diff -q - $f.py && echo "$f.py == t/T2459"; done
num.py == t/T2459
stab.py == t/T2459
$ python3 num.py hs|sums|consts|exps; python3 {hs_ba,sth,ec,inst,nmin}.py   # 02:47:36-02:48:28 UTC; diff against the prover's out/
ec.out identical  hs_ba.out identical  inst.out identical  nmin.out identical  num_consts.out identical
num_exps.out identical  num_hs.out identical  num_sums.out identical  sth.out identical
$ tail -1 out/num_hs.out
max ratio |Tr| / HS-product over 400 x 20 samples: k=3,4: 0.6849; k=6 all legs: 0.5392; k=6 glue form: 0.6660  (all <= 1 required); max |sum_b L2_ab - Im L1_a/eta|(Ward) = 5.3e-15
$ cut -c1-215 out/hs_ba.out   (BA resolvents H = g0 Psi + sqrt(u) V, d=3, L=4, W=2; rows g=1/64 u=t0 and g=10 u=t0 shown)
g=0.015625 u=t0    t0=0.6937 g0=0.0130 E=+0.0000 eta=0.3061 | HS max ratio k=3:0.5075 k=4:0.4837 k=6:0.1743 | glue ratio k=1:0.3242 k=2:0.3242 |
g=10       u=t0    t0=0.3138 g0=5.6017 E=+0.0000 eta=0.3844 | HS max ratio k=3:0.3395 k=4:0.1587 k=6:0.0227 | glue ratio k=1:0.0611 k=2:0.0611 |
  (all 9 rows: errors Hermitian <= 1e-14, dense-vs-block 0, leg-identity <= 6e-16, swap <= 1e-16, Ward <= 7e-16, ||Y||^2-vs-4loop <= 7e-17;
   k=1 |trX|/||X||_F max 2.83 = sqrt(8): k = 1 fails, as the ticket says)
$ cat out/ec.out (first and last lines)
d= 3 W=54.6: lk=15.6 wG=21.1 dif<=6l=11.7 dif>6l=19.8 | loss=65.4 margin=44.2
d= 3 W=1e+12: lk=15.6 wG=23.9 dif<=6l=35.1 dif>6l=29.4 | loss=107.7 margin=72.6
d=10 W=1e+12: lk=72.2 wG=88.9 dif<=6l=55.7 dif>6l=86.0 | loss=235.7 margin=146.8
min margin over d in [3,399], log W in {4..1e5}: log10 =44.22 at d=3, logW=4
$ cat out/sth.out
theta=0.5: ... L=Z^3:2.359e+07 | analytic C(3,theta)=7.888e+18; max S / C = 3.0e-12
theta=0.1: ... L=Z^3:3.686e+11 | analytic C(3,theta)=1.926e+27; max S / C = 1.9e-16
theta=0.02: ... L=Z^3:5.76e+15 | analytic C(3,theta)=4.702e+35; max S / C = 1.2e-20
$ cat out/nmin.out
smallest n with 6*l* <= L/2: n=642 (L=2572, W=3.517e+15, l*=214.2)
```
Every numeric stop threshold holds: the HS and glue ratios are at most 0.6849 (limit 1 + 1e-9), the leg-identity and Ward errors at
most 5.3e-15 (limit 1e-8), and `S_θ` is bounded in `L`, up to its `Z^3` value. `ec.py` uses the loss
`10^12(1600d⁴)^d(1+log(L^dW^{2d}))^4(1+x)^3e^{8x^{3/4}}·1000^d(1+log(L^dW^{6d}))^{2d}`. I checked this formula against
`lossE2` (`Path/LemDecCalE.lean:54-57`) and `lossE2wG` (`Path/LemDecCalEwG.lean:74-75`); it is the same, at `Λ = K₀ = 1`.

## 4. Design gate E: the written argument (checked against the merged signatures)
- **E-a** ((a) line 19; probe 170-353). The leg identity `loopM ![σ,!σ] ![a,b] = ‖E_b^{1/2}G(σ)E_a^{1/2}‖_F²` is proved
  (253-258). So are the swap (347-353), the HS bound for `k ≥ 2` (274-289, 326-328), the list form (333-341) and the glue
  form together with its 4-loop identity (260-272, 291-316). They use only `H.IsHermitian` and hold for any `z : ℂ`, with no
  entry bound. Every leg has charges `(σ,!σ)`, and the swap moves it to `(+,-)`. So the bundle's 𝒦 conjuncts (ii) and (iii)
  at `![true,false]` cover every leg, and no 𝒦 bound at equal charges is used.
- **E-b** ((a) lines 21-34). I re-derived each chain against the definitions and lemmas below:
  `STEGtMg`/`STELKLKMg`/`STeeMg` (`Chain/Step2Gen.lean:368-378`, `:960-963`; single sums at `S = 1`); `STtailTD` = `tailTD` at
  `zdistInf (a 0 - a 1)` (`Step5Pins:151`, `Tail:173`); `LemDecCalE_sum_tail_tail` (`:395`, floor `w·L^d ≤ A`);
  `LemDecCalEwG_sum_sqrt_tail` (`EwG:318`, floor `w·L^{2d} ≤ A`); `tailT_shift` (`:527`); `e10a` (`:186`).
  - Floors: `(L^dW^{6d})² ≤ W^D` and `τ ≥ W^{-d}` give `W^{-D}L^{2d} ≤ W^{-12d} ≤ τ²`. Balls are unions around `a₀, a₁`
    (factor 2). For `c ∉ 𝔹_{3ℓ}` the near cut gives `|c-a_i'| > ℓ`; for `r > 6ℓ` the non-glued legs are `≥ r-5ℓ > ℓ`.
  - Case B: 16 terms `≤ α⁴τ⁴S_θ` (using `L^dW^{-2D} ≤ τ⁴`), constant `4·16·2 = 128`. Exponents: C `(√3+√5+2)/2 ≤ 3`, D `1+√2`.
  - Every `J` term carries `τ^{1/2}` (wG2-4, C, D); the indicator terms (wG1, A, B) are `J`-free. RHS shapes match the pins
    (`Bτ = (1-u)⁻¹`; dif uses `W^{2θd(Cd+1)} ≥ 1`, `S_θ ≥ 1`).
  - No step needs an entry-level bound, `|E| < 2`, `M = mI`, `SB d`, or a 𝒦 bound at equal charges. Stop rule 1 does not fire.
- **`STeeLoop` at `m = 2`, `k = 1,2`, `S = 1`**: compiled in the probe (356-360). The bridge `STeeMg` = `W^d Σ_c` (two explicit
  six-loops), P7, I recompiled from the prover's scratch file:
```
$ lake env lean <scratch>/T2482/lean/br2.lean; echo "br2 exit $?"; grep -nE "sorry|admit|native_decide|axiom" br2.lean; echo rc=$?
br2 exit 0
rc=1
```
  The charge and block lists in br2 equal those of (a) line 20. The glue positions are `p = 2` (`c` after `a₁`) and `p = 5`.
- **E-c** ((a) row 7, row 9, line 35). Each structural constant is bounded by a factor of `lossE2wG`:
  - the shifts are `≤ e^{2√6·x^{3/4}} ≤ e^{8x^{3/4}}`;
  - the ball counts satisfy `(6ℓ+1)^d ≤ (1+log(L^dW^{6d}))^{2d}`, since `log P ≥ 6dx`;
  - `2S_d+1` and `C_sq` are `≤ 10^12(1600d⁴)^d·1000^d`;
  - `Λ³ ≤ Λ⁶` and `1 ≤ K₀`.
  The numeric minimum margin is `10^44.2` (§3). Stop rule 3 does not fire; no fallback loss and no primed loss are needed.

## 5. H250 (4) fill-in table ((a″) final table, lines 198-212)
Rows (i)-(xii) are all filled; I checked each one:
- (i), (ii), (vii): see §1, §2 and §4.
- (iii): loss inequalities per constant; fallback n/a.
- (iv): ten outputs rerun byte-identical, at the ticket's grid (g, u, θ, W).
- (v): bundle conjunct → steps, with merged lemma file:line.
- (vi): adjoint copied under the stem (232-242); `open private lemDecCalE_sum_zdist_le` resolves; `LemDecCalEdif` §1 not reused.
- (viii): consumers U5c, U5d, U5e.
- (ix), (x): UBA-C1 not triggered; registry none; public Props are only the bundle and `BAStep5IIIEdet`.
- (xi): central 2,450 = 1,262 + 1,188.
- (xii): 491 refs, 0 hits.
Re-greps:
```
$ grep -nE 'BAK_le_small|BAMB_upper_small|BAGbEXP|Mbound_AO|W\^\(-eps|BAm_im_lower_window' RBM3D/Probe/T2482Pins.lean; echo rc=$?
rc=1
$ grep -nE 'STGridRepNgL|withLam|\|E\||norm_mE|mSigma|SB d|E2Hyp|gexRHS|STGMMg|≤ A \*' RBM3D/Probe/T2482Pins.lean; echo rc=$?
rc=1
$ grep -nE "lam0 ≤|gK|withLam" RBM3D/Probe/T2482Pins.lean; echo rc=$?
rc=1
$ git grep -nE 'Step5IIIEdet|BAStep5IIIE|baStep5IIIE' <ref> -- RBM3D | wc -l   # main 78f4cc14, t/T2483, t/T2484, t/T2473b, t/T2480b
main: 0   t/T2483: 0   t/T2484: 0   t/T2473b: 0   t/T2480b: 0
```

## 6. Decisions fixed at this 1a-audit (within the ticket's latitude; no dispatcher sign-off requested)
1. **Target 2 texts.** The list form `T2482_LoopHSList` and the glue form `T2482_LoopGlue` are fixed as probe lines 113-130
   on 0ac2aab8, verbatim (ticket target 2: "texts fixed at the 1a-audit from the probe"). Both are proved in the probe.
2. **Target 8 instance at `n = 800`.** At `n = 1`, `L/2 = 4 < ℓ* = 18.25` (`inst.out`), so the far windows of (iii), the
   indicators and the near cut are collapsed. Under CLAUDE.md §5.5 a target-7 instance there would be degenerate. The 1b
   therefore keeps the `n = 1` instances (scalar part, target 2) and must also give the target-7 instance at `n = 800`, where
   `6ℓ* = 1344.6 ≤ L/2 = 1602` (any `n ≥ 642` works). The scalar part at `n = 800` is already proved in the probe (364-368).
   This adds an instance and changes no pin.
3. **Split confirmed (pre-signed).** Central 2,450, in (1,950, 3,600]; no third row (each file < 1,800, no `Step5IIIEdet3`).
   U5b-1 = targets 1-5, 8 (a) on `t/T2482` (`BA/Step5IIIEdet.lean`). U5b-2 = targets 6-7, 8 (b) on `t/T2482b`, stacked after
   U5b-1's audit PASS (`BA/Step5IIIEdet2.lean`). The sixth-row notice REQ is the dispatcher's and blocks nothing
   (§282 (3), answer (1)). No REQ is needed before 1b.

## 7. Paper deltas
The candidates are T2459b (cut-offs `2ℓ*`/`6ℓ*`), T2459c (HS route instead of `lem_GbEXP_BA`) and T2459f (the
`W^{2θd(Cd+1)}S_θ` factor), all in `T2459-design.md:264-268`. They are listed as unnumbered pending candidates in
`docs/paper-deltas.md:1598`. The probe adds no new Lean/paper difference. Coverage is complete.

## 8. Observations (no RETURN)
- O1: Bundle (ii) (`K₀`) and the cap `J ≤ W^{1/2}` are read by no chain ((a) F2); they stay, because U5c's target is frozen.
- O2: 1b imports: the ticket's six plus `Graph/BAAuxGraph2` (flow instance, probe 380-381); the adjoint is a stem copy, no `LWWeightExp`.
- O3: The matrix bundle's limit check is deterministic, at `u = 0` only ((a) l. 59); the `u > 0` witness is U5c's (answer (4)).
- O4: The (xi) line counts are estimates (factor 1.5 assumed); the 2,000-per-file stop line binds again in the 1b.

## Verdict
Every stage-1a deliverable of design gate E and of the H250 (4) table is met, and no binding stop line is hit. The pre-signed
split U5b-1 / U5b-2 is confirmed, with no REQ before 1b. **PASS**, with no dispatcher sign-off needed. U5b-1's 1b
(`prover-max`) may start. T2485's start condition ("after T2482's 1a-audit PASS") now holds.
