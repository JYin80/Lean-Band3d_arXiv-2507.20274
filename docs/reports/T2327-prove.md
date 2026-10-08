Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 10:05:20 UTC 2026

Targets (mathematics only): on the grid walk `Pgue sz` (independent steps; step `k+1 ≥ 1` has law `gueUnit sz`, coordinates independent
centred Gaussians of variance `gueUnitVar ∈ {1, 1/2}`, `Grid.lean:49-61`): (T1,T2) freezing and conditional sub-Gaussianity of a
`filt k`-frozen function of the next step; (T3) the law of `y ↦ Re tr(A·seqXmat n y)` under `gueUnit` is `N(0, vGue)`; (T4) the
frozen linear case; (T5) `HighProbAt (Pgue sz) sz.size`: every entry of every increment `seqXmat n (ω k)`, `1 ≤ k ≤ gueGridK n0 n`, has
norm `≤ sz.size n`, given `Tendsto sz.size atTop atTop`. Only T5 has exponents; T1-T4 are exact identities (independence + Gaussian law).

### (i) Exponent table (T5; `N := sz.size n = (W L)^d`, source `RBM2D/Universality/GUEPhase/Markov.lean:766-912`; `git -C ../RBM2D --no-optional-locks log -1 --format=%h` = 9e0f275)

| quantity | value | constraint | slack |
|---|---|---|---|
| `gueGridK sz n0 n` (`Grid.lean:106`) | `(N+1)^m`, `m = 32 n0 + 64` | proof device only (never a witness); `≠ 0` | n0 = 1: m = 96 |
| `card Idx d (sz.L n) (sz.W n)` | `N` (`Sizes.card_Idx`, `Sizes.lean:160`) | the only `d`-dependent count; dimension enters only via `N = (W L)^d` | exact |
| `card coordFinset n = card (Idx × Idx × Bool)` | `2 N²` | equals RBM2D's `N·(N·2)` | exact |
| `card K_n = card (Fin gueGridK × coordFinset)` | `(N+1)^m · 2N²` | `≤ N^C`, `C = m + 4 = 32 n0 + 68` | factor `≈ N²/2` (≈ 2^193.9 at n = 18, n0 = 1) |
| arithmetic threshold | `N ≥ 2^(m+1) = 2^(32 n0 + 65)` | `(N+1)^m ≤ (2N)^m`; `2^(m+1) N^(m+2) ≤ N^(m+3) ≤ N^(m+4)` | n0 = 1: 2^97; exponent chain m+2 = 98, m+3 = 99, m+4 = 100 = C |
| coordinate variance `v` | `1` (i = j) or `1/2` (i ≠ j) | tail lemma needs `0 < v ≤ 1` | `v ≥ 1/2 > 0`, `v ≤ 1` exact |
| per-coordinate tail | `P(\|y\| > N/2) ≤ 2 exp(-(N/2)²/(2v)) ≤ 2 exp(-N²/8)` | need `≤ N^{-(D+C)}` eventually, for every `D > 0` (`highProbAt_iInter`, `PerTime.lean:136`, uses `D+C`) | n0 = 1: threshold N ≥ 58 (D = 1), 61 (D = 10), 85 (D = 100), all ≪ 2^97 |
| entry bound | `‖Xentry‖ ≤ 2·(N/2) = N` (off-diagonal: two coordinates; diagonal: one) | `N/2 ≥ 0` | exact |
| eventual range | `∀ᶠ n`: `N ≥ max(2^(32 n0+65), tail threshold)` | hypothesis `Tendsto sz.size atTop atTop` (T5) | none needed beyond N → ∞ |
| `vGue` at `A = 1` (T3, T4) | `vGue = Σ_c v_c a_c²` with `a_c = 1` on the N diagonal `true` coordinates, `0` elsewhere | `s² · vGue ≤ c` for T4 | `vGue = N`; with `s = 1`, `c = N`: equality |

Quantifier note: T5 is `HighProbAt` (`∀ D>0, ∀ᶠ n`), so no condition is imposed at finitely many n (§29 item 4). §29 one line each: (1) time domain: none (no time parameter); (2) boundary of case (ii): none; (3) L–W relation: only `N = (W L)^d`, no `L^d ≤ W^K` used; (4) `∀ᶠ n` as above; (5) union over grid steps and coordinates is inside the probability (`⋂ p : K n`), `HighProbAt` polynomial union bound; (6) the parameter lower bound is `N → ∞`, which is written as a hypothesis of T5; (7) scale is `N = sz.size n` throughout, matching the consumers' `HighProbAt … sz.size`.

Consumers (ticket): UN-33 `BoundsA`, UN-34/35 `Drift`, UN-50 `PathBounds` (not checked here; targets restated verbatim from the check file, which the hub compiled).

### (ii) One concrete nondegenerate instance (`sz0 : Sizes 3`, `Defs/Sizes.lean:260`: `L = 4(n+1)`, `W = (2(n+1))^5`; `d = 3`, `n0 = 1`)

Command: `python3 -I <scratchpad>/T2327/inst.py` (pure integer/float arithmetic, no Lean). Output, verbatim:

```
m= 96 C= 100 threshold 2^97
least n with size n >= 2^97: 18 size=2^97.463 size(17)<2^97: True
n=18: log2 card K = 9552.3441 <= log2 S^C = 9746.2695 ; slack log2 = 193.9254 (>= log2 S - 1 expected)
chain exps m+2=98, m+3=99, m+4=100 == C:True
D=1: D+C=101, exp-beats-poly threshold N>=58  (<< 2^97: True)
D=10: D+C=110, exp-beats-poly threshold N>=61  (<< 2^97: True)
D=100: D+C=200, exp-beats-poly threshold N>=85  (<< 2^97: True)
at n=18: ln S = 67.556 ; -(D+C) ln S = -6823.155 ; -S^2/8 = -(2^191.9)
n=0: N=2097152, #coords=8796093022208, vGue(A=1)=2097152 (>0), sqrt=1448.155
linear: s^2*vGue=2097152 <= c=2097152 : True
size(n)>=n+1 for n<2000: True  size(10)= 11659991713824860234842112  size(100)=2.509e+42
```

Reading of the output.
- T5 at `n0 = 1`, `D` any: the union-bound cardinality constraint `card K_n ≤ N^100` first holds (by the stated threshold) at `n = 18`, `N = 2^97.46 ≥ 2^97`; actual value verified with exact integers: `log2 card = 9552.34 ≤ 9746.27`. The tail threshold (N ≥ 58..85) is far below. The statement is an `∀ᶠ n` event; the instance is the application `gue_highProb_incr_le sz0 1 hsize`, no witness `n` is built (`gueGridK` at `n = 18` is `(N+1)^96`, astronomically large, but it is a set bound in the event, not a constructed witness).
- External hypothesis `Tendsto sz.size atTop atTop`, limit computation: `sz0.size n = (W L)^3 = 2^21 (n+1)^18 ≥ n+1 → ∞` (asserted for n < 50 in the script, size(100) ≈ 2.5e42); merged lemma `sz0_tendsto : sz0.SizeTendsto` (`Sizes.lean:300`, proved via `n ≤ size n`) is the same limit in the real-cast form, so the hypothesis holds at the instance.
- T3 at `n = 0`, `A = 1`: `N = 2097152` (matches `sz0_values`, `Sizes.lean:267`), `vGue = N = 2097152 > 0` (`Re tr X = Σ_i y(i,i,true)`, `Xentry` `FineModel.lean:105-110`, `idxKey_injective` `:75` so the diagonal branch is exactly `i = j`; `gueUnitVar = 1` there), so the law `N(0, 2097152)` is nondegenerate.
- T4 at the same data: `E = univ`, `A ≡ 1` (measurable for every `filt k`), `s = 1`, `c = vGue`: `s² vGue ≤ c` holds with equality.
- T1, T2: take `β = Unit` (or the matrix type), `F y x = x c₀` for a fixed coordinate: `HasSubgaussianMGF (F y) v (gueUnit)` holds for `c = gueUnitVar c₀ ∈ {1, 1/2}` (centred Gaussian coordinate); integrability and joint measurability are those of a coordinate evaluation.

### Port check (ticket preflight (i)-(iii))
- `d = 2` tokens to change: `Z2 L ↦ Zd d L`, `Idx (d.L n)(d.W n) ↦ Idx d (sz.L n)(sz.W n)`, `d : Sizes ↦ sz : Sizes d`, `Markov_card_Idx` (`simp [Idx, Z2, ZMod.card, pow_two]` ↦ `Sizes.card_Idx`), docstrings. The arithmetic `Markov_card_arith` and the exponent count are unchanged (`C = 32 n0 + 68`).
- `Xmat_apply`, `hfun`: no RBM3D declaration (grep over `RBM3D/` found 0 definitions); re-derive under `Markov_` (as the ticket states). Private in the merged twin `Path/Markov.lean` and so re-derived locally (the source also has its own private copies): `measurable_linTr_uncurry`, `instStandardBorelSpaceMatrix`, `instStandardBorelSpacePathΩ`, `mgf_linTr_seqXmat`.
- Merged signatures vs the source's use, compared by `diff` of the RBM2D and RBM3D declarations: `lintegral_indep_pair`, `linVar` identical; `map_sum_const_mul_of_indep` and `lintegral_indep_pair_le` the same statement (only `d ↦ sz` in proofs / an extra example); `highProbAt_iInter` identical statement (`Path/PerTime.lean:136` vs `Defs/StochDomAt.lean:279`); `linTr`, `coordFinset`, `linTr_seqXmat_eq_sum` have the form the source assumes with `sz` implicit.

### Verdicts
- T1 `gueCondExp_freeze`: PASS (independence of `ω(k+1)` from `filt k` under `Measure.infinitePi`, step law `gueUnit`; no exponents).
- T2 `gueHasCondSubgaussianMGF_of_frozen`: PASS.
- T3 `gueMap_lin_Xmat` (with `vGue`): PASS; instance `vGue = 2097152`.
- T4 `gueHasCondSubgaussianMGF_linear`: PASS; instance `s = 1, c = vGue`.
- T5 `gue_highProb_incr_le`: PASS; exponent chain closes with slack `≈ N²/2`; hypothesis `Tendsto` holds at `sz0`.

## (a′) Preflight corrections — Thu Oct  8 10:22:34 UTC 2026

No verdict changes. Two notes on section (a): (1) its instance line "`vGue = N = 2097152` at `n = 0`" is not proved in Lean; the Lean instance proves `0 < vGue sz0 n 1` for every `n` (`MarkovInst.vGue_one_pos_sz0`) and the five applications below. (2) The ticket's "HEAD 81fca44" is the last RBM2D commit touching the source file; RBM2D HEAD is 9e0f275 (section (a) and (b9) use HEAD; the file is identical between the two, see (b9)).

## (b) Script output

Times (`date -u`): preflight (a) 10:05:20; stage 1b start 10:05:51; module build 10:12:47; axioms 10:13:13; check-equality scratch 10:13:35; registry pre-check 10:13:48; commit 85ac68f 10:15:39; full lake build 10:20:41-10:20:44 UTC (all UTC)

### b1. `lake build RBM3D.Universality.GUEPhase.Markov` (final state, commit 85ac68f)
```
$ lake build RBM3D.Universality.GUEPhase.Markov   (started 10:12:47 UTC; module compiled 10:12:47-10:12:55 UTC per the mtimes below)
✔ [3743/3743] Built RBM3D.Universality.GUEPhase.Markov (6.2s)
Build completed successfully (3743 jobs).
$ lake build RBM3D.Universality.GUEPhase.Markov   (again after the commit, 10:20:52 UTC)
Build completed successfully (3743 jobs).
exit 0
lake build RBM3D.Universality.GUEPhase.Markov  1.36s user 2.94s system 220% cpu 1.951 total
Thu Oct  8 10:12:47 2026 UTC  RBM3D/Universality/GUEPhase/Markov.lean
Thu Oct  8 10:12:55 2026 UTC  .lake/build/lib/lean/RBM3D/Universality/GUEPhase/Markov.olean
git hash-object Markov.lean = HEAD:Markov.lean = 5f0c92c371abb87068b61710084429e4d265f626 (commit 85ac68f, file unchanged since the 10:12:47 build)
warnings/errors from RBM3D/Universality/GUEPhase/Markov.lean in the 10:12:47 build log: 0
```
### b2. `#print axioms` (scratch file `import RBM3D.Universality.GUEPhase.Markov`; five targets, `vGue`, instances)
```
'RBM.Univ.GUEPhase.gueCondExp_freeze' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_of_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueMap_lin_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueHasCondSubgaussianMGF_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gue_highProb_incr_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.vGue' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.vGue_one_pos_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueMap_lin_Xmat_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueCondExp_freeze_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueHasCondSubgaussianMGF_of_frozen_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gueHasCondSubgaussianMGF_linear_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.sz0_size_tendsto_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.MarkovInst.gue_highProb_incr_le_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b3. Target statements (extracted by script from `RBM3D/Universality/GUEPhase/Markov.lean`, line numbers are file lines)
```
291: def vGue (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ≥0 :=
292:   linVar (gueUnitVar sz)
293:     (fun c => linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) (coordFinset n)
109: theorem gueCondExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
110:     (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
111:     {F : β → Sizes.SeqΩ sz → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
112:     (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue sz)) :
113:     (Pgue sz)[fun ω => F (Y ω) (ω (k + 1)) | filt sz k]
114:       =ᵐ[Pgue sz] fun ω => ∫ x, F (Y ω) x ∂(gueUnit sz) := by
184: theorem gueHasCondSubgaussianMGF_of_frozen {β : Type*} [MeasurableSpace β]
185:     [StandardBorelSpace β] (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
186:     {F : β → Sizes.SeqΩ sz → ℝ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
187:     {c : ℝ≥0} (hsub : ∀ y, HasSubgaussianMGF (F y) c (gueUnit sz)) :
188:     HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
189:       (fun ω => F (Y ω) (ω (k + 1))) c (Pgue sz) := by
298: theorem gueMap_lin_Xmat (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
299:     (gueUnit sz).map (fun y => linTr n A (Sizes.seqXmat sz n y)) =
300:       gaussianReal 0 (vGue sz n A) := by
615: theorem gueHasCondSubgaussianMGF_linear (n k : ℕ) (s : ℝ)
616:     {A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
617:     (hA : Measurable[filt sz k] A) (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz k] E) (c : ℝ≥0)
618:     (hbound : ∀ ω ∈ E, s ^ 2 * (vGue sz n (A ω) : ℝ) ≤ c) :
619:     HasCondSubgaussianMGF (filt sz k) ((filt sz).le k)
620:       (fun ω => E.indicator (fun ω => s * linTr n (A ω) (Sizes.seqXmat sz n (ω (k + 1)))) ω)
621:       c (Pgue sz) := by
863: theorem gue_highProb_incr_le (n0 : ℕ) (hsize : Tendsto (fun n => sz.size n) atTop atTop) :
864:     HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n →
865:       ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)}) := by
```
### b4. Compiled nonempty instances (`d = 3`, `RBM.Gauss.SizesInst.sz0`; namespace `RBM.Univ.GUEPhase.MarkovInst`; statements extracted by script)
```
1027: theorem vGue_one_pos_sz0 (n : ℕ) :
1028:     0 < (vGue sz0 n (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) : ℝ) :=
1033: theorem gueMap_lin_Xmat_sz0 (n : ℕ) :
1034:     (gueUnit sz0).map (fun y => linTr n
1035:         (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)
1036:         (Sizes.seqXmat sz0 n y))
1037:       = gaussianReal 0 (vGue sz0 n 1) ∧ 0 < (vGue sz0 n 1 : ℝ) :=
1064: theorem gueCondExp_freeze_sz0 (k : ℕ) :
1065:     (Pgue sz0)[fun ω : PathΩ sz0 => markovInstF (ω k markovInstCoord) (ω (k + 1)) | filt sz0 k]
1066:       =ᵐ[Pgue sz0] fun ω => ∫ x, markovInstF (ω k markovInstCoord) x ∂(gueUnit sz0) :=
1098: theorem gueHasCondSubgaussianMGF_of_frozen_sz0 (k : ℕ) :
1099:     HasCondSubgaussianMGF (filt sz0 k) ((filt sz0).le k)
1100:       (fun ω : PathΩ sz0 => markovInstF (ω k markovInstCoord) (ω (k + 1)))
1101:       (vGue sz0 0 markovInstOne) (Pgue sz0) :=
1110: theorem gueHasCondSubgaussianMGF_linear_sz0 (k : ℕ) :
1111:     HasCondSubgaussianMGF (filt sz0 k) ((filt sz0).le k)
1112:       (fun ω => ({ω : PathΩ sz0 | ω k markovInstCoord ≤ 0} : Set (PathΩ sz0)).indicator
1113:         (fun ω => (1 : ℝ) * linTr 0 markovInstOne (Sizes.seqXmat sz0 0 (ω (k + 1)))) ω)
1114:       (vGue sz0 0 markovInstOne) (Pgue sz0) :=
1122: theorem sz0_size_tendsto_nat : Tendsto (fun n => sz0.size n) atTop atTop :=
1127: theorem gue_highProb_incr_le_sz0 :
1128:     HighProbAt (Pgue sz0) sz0.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK sz0 1 n →
1129:       ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
1130:         ‖Sizes.seqXmat sz0 n (ω k) i j‖ ≤ ((sz0.size n : ℕ) : ℝ)}) :=
```
Data: `A = 1`, size index `0` (`N = 2097152`) for the Gaussian law/linear instances; frozen variable `Y ω = ω k c₀` (`c₀ = ⟨0,(0,0,true)⟩`, `filt sz0 k`-measurable, non-constant), `F y x = cos y * Re tr(seqXmat sz0 0 x)`; `E = {ω | ω k c₀ ≤ 0}`; `n0 = 1`, `Tendsto sz0.size` from the merged `sz0_tendsto`. Every deterministic hypothesis is discharged (no hypothesis of any instance is left open).

### b5. Check-file equality
(a) `vGue` whitespace-normalized, check file vs `Markov.lean` (script `mkcheck.py`):
```
check vGue : def vGue (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ≥0 := linVar (gueUnitVar sz) (fun c => linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) (coordFinset n)
file  vGue : def vGue (n : ℕ) (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ≥0 := linVar (gueUnitVar sz) (fun c => linTr n A (Sizes.seqXmat sz n (Pi.single c 1))) (coordFinset n)
EQUAL
```
(b) scratch file = `docs/tickets/checks/T2327-check.lean` with `import RBM3D.Universality.GUEPhase.Markov` added and its final `example : Prop` replaced by `example {d : ℕ} (sz : Sizes d) : RBM.Univ.GUEPhase.T2327Check.T2327_<name> sz := RBM.Univ.GUEPhase.<name> sz` for the five names; `lake env lean` (scratch file contains 5 `example` lines):
```
exit 0
```
### b6. Registry pre-check (uncommitted scratch file `import RBM3D` / `import RBM3D.Universality.GUEPhase.Markov` / `#assert_rbm_axioms`, `lake env lean`)
```
axiom audit: 9148 theorems, 2963 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
...
non-vacuity certificates: 0 of 138 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
lake env lean registry.lean  42.24s user 3.15s system 92% cpu 49.219 total
exit 0
```
### b7. Full `lake build` in the worktree (started after the certificate build `LWExpCertBS1` had finished, CONTROL H122)
```
⚠ [4116/4132] Replayed RBM3D.Graph.LWExpCert
⚠ [4117/4132] Replayed RBM3D.Graph.LWExpCertS0
⚠ [4118/4132] Replayed RBM3D.Graph.LWExpCertS1
Build completed successfully (4132 jobs).
lake build  1.61s user 3.94s system 233% cpu 2.373 total
exit 0
```
### b8. Hygiene
```
$ for each new public name N: grep -rnw N RBM3D --include=*.lean | grep -v Markov.lean | grep -v Probe/ | wc -l
17 names checked (6 targets/defs, MarkovInst, 3 helper defs, 7 instance theorems); total hits outside RBM3D/Universality/GUEPhase/Markov.lean and RBM3D/Probe/: 0
banned tokens (sorry|admit|native_decide|declared axiom) in RBM3D/Universality/GUEPhase/Markov.lean: 0
 RBM3D/Universality/GUEPhase/Markov.lean | 1135 +++++++++++++++++++++++++++++++
 1 file changed, 1135 insertions(+)
commit 85ac68f  author Jun Yin <321276894+JYin80@users.noreply.github.com>
branch t/T2327 vs main: git diff --stat main...t/T2327 (above) lists only the new file
```
### b9. Port (RBM2D `Universality/GUEPhase/Markov.lean`, RBM2D HEAD `9e0f275`; declaration lines)
```
gueCondExp_freeze: RBM2D :92 -> RBM3D :109
gueHasCondSubgaussianMGF_of_frozen: RBM2D :167 -> RBM3D :184
def vGue: RBM2D :274 -> RBM3D :291
gueMap_lin_Xmat: RBM2D :281 -> RBM3D :298
gueHasCondSubgaussianMGF_linear: RBM2D :598 -> RBM3D :615
gue_highProb_incr_le: RBM2D :843 -> RBM3D :863
RBM2D diff --stat 81fca44 HEAD -- RBM2D/Universality/GUEPhase/Markov.lean: empty (exit 0); working tree of the source file clean
     912 ../../RBM2D/RBM2D/Universality/GUEPhase/Markov.lean
    1135 RBM3D/Universality/GUEPhase/Markov.lean
```
Mechanical regex renames of the source (`conv.py`): `Idx (d.L n) (d.W n)` → `Idx d (sz.L n) (sz.W n)`, `d.L/d.W/d.size` → `sz.L/sz.W/sz.size`, argument `d` → `sz` of `Pgue/filt/gueUnit/gueUnitVar/gueGridK/vGue/Sizes.SeqΩ/SeqCoord/seqXmat/slice/PathΩ/Markov_*`. Remaining differences (`diff` of the renamed source against `Markov.lean` lines 39-928; new-side lines; 38 lines differ in total, 14 removed and 24 added of which 3 are blank and omitted here):
```
> variable {d : ℕ} (sz : Sizes d)
> /-- `PathΩ sz` is standard Borel (a countable product of countable products of `ℝ`); the instance
> search does not find it by itself at a generic `sz` (as in `Path/Markov.lean`). -/
> private instance Markov_standardBorelPathΩ {sz : Sizes d} : StandardBorelSpace (PathΩ sz) :=
>   haveI : StandardBorelSpace (Sizes.SeqΩ sz) := inferInstance
>   StandardBorelSpace.pi_countable (α := fun _ : ℕ => Sizes.SeqΩ sz)
> /-- **The law of a linear functional**: under `gueUnit sz`, `y ↦ Re tr (A · seqXmat sz n y)` is the
> variable {sz}
>     (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)
> the `E`-truncated variable `s · Re tr (A · seqXmat sz n (ω (k+1)))` has a conditionally
> private theorem Markov_Xmat_apply {L W : ℕ} [NeZero L] [NeZero W] (y : Ω d L W) (i j : Idx d L W) :
>     Xmat d L W y i j = Xentry d L W y i j := rfl
> private theorem Markov_norm_Xentry_le {L W : ℕ} [NeZero L] [NeZero W] (y : Ω d L W)
>     (i j : Idx d L W) {t : ℝ} (h : ∀ c : CoordF d L W, |y c| ≤ t) : ‖Xentry d L W y i j‖ ≤ 2 * t := by
>     Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n :=
>   Sizes.card_Idx sz n
>   change (Finset.univ.map (Function.Embedding.sigmaMk (β := fun m => CoordF d (sz.L m) (sz.W m)) n)).card = _
> dimension `sz.size n`, every entry of every GUE increment `seqXmat sz n (ω k)`,
>     have hbound : ∀ c : CoordF d (sz.L n) (sz.W n),
>     rw [Markov_Xmat_apply]
>     calc ‖Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n (ω k)) i j‖
```

### Narrative
- Port of the five targets and `vGue` of RBM2D `Markov.lean` (912 lines) into `RBM3D/Universality/GUEPhase/Markov.lean` (1135 lines: port ends at `end IncrTruncation` line 928; `section LinearSubgaussian` (helpers for the instances) line 932; `namespace RBM.Univ.GUEPhase.MarkovInst` line 1010; ticket size 850/950/1200, stop rule 1500). Imports are exactly the ticket's three; `highProbAt_iInter`, `Idx`, `Sizes.card_Idx` come through `Grid.lean`.
- The proofs are the source's; the changes are the renames above and (b9): `Sizes.card_Idx` replaces the `Z2`-specific `simp`; `Markov_Xmat_apply` (`rfl`) replaces RBM2D's `Xmat_apply`; `Xentry`/`Ω`/`CoordF` carry `d`; the `sigmaMk` in `Markov_card_coordFinset` carries `(β := fun m => CoordF d (sz.L m) (sz.W m))`; the twin's private `PathΩ` standard-Borel instance is reproduced as `Markov_standardBorelPathΩ`.
- `RBM.Path.hfun` (ticket port map) is not used by the source: its `hfun` is a local `have` in `gueMap_lin_Xmat` (grep of the source: lines 285, 291 only), so nothing was re-derived for it.
- The exponent count is the source's: `card K_n = (N+1)^(32 n₀+64)·2N² ≤ N^(32 n₀+68)` for `N ≥ 2^(32 n₀+65)` (`Markov_card_arith`, unchanged) and the tail `2 exp(-N²/8)` beating `N^{-D'}` (`Markov_eventually_exp_beats_rpow`, unchanged); both match the table of section (a).
- Instances: all five targets are applied at `sz0`; the freeze and of_frozen instances use the non-constant frozen variable `ω k c₀`, the linear instance uses the non-trivial set `E = {ω k c₀ ≤ 0}`, the `gueMap_lin_Xmat` instance adds `0 < vGue sz0 n 1`, and `gue_highProb_incr_le` is applied with `n0 = 1`.
- `d ≥ 3` content: the only `d`-dependent fact in the file is `Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n` (merged `Sizes.card_Idx`); `d` enters the count only through `N = sz.size n`.
- Process disclosure (CONTROL H122/H101 (4)): my single-module builds and the registry pre-check ran while `lake build RBM3D.Graph.LWExpCertBS1` (pid 69612, started 09:50:57 UTC) was running in the main worktree; `vm_stat` at the start of my session showed `Pages free: 4072` (16384-byte pages). I had read an empty `ps` filter as "no build running" and did not wait. The full `lake build` (b7) waited for the certificate build to end.
- Not claimed: the exact value of `vGue sz0 0 1` (only positivity is proved); the instance of `gueHasCondSubgaussianMGF_linear` uses the constant direction `A = 1` (as the band twin's `markov_hasCondSubgaussianMGF_linear_sz0` does).

## (c) Verified Mathlib names (`#check` in `lake env lean`, one line each)
$ lake env lean names.lean (one `#check @N` per name below): exit 0, 0 errors
- MeasureTheory.Measure.infinitePi_map_eval
- ProbabilityTheory.iIndepFun_infinitePi
- ProbabilityTheory.iIndepFun_iff_iIndep
- ProbabilityTheory.indep_biSup_compl
- ProbabilityTheory.indep_of_indep_of_le_left
- ProbabilityTheory.indep_of_indep_of_le_right
- ProbabilityTheory.Indep_iff
- ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
- MeasureTheory.integral_prod
- MeasureTheory.StronglyMeasurable.integral_prod_right'
- MeasureTheory.Integrable.integral_prod_left
- MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
- ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel
- ProbabilityTheory.condExpKernel_comp_trim
- ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat
- ProbabilityTheory.HasSubgaussianMGF.measure_ge_le
- ProbabilityTheory.HasSubgaussianMGF.neg
- ProbabilityTheory.HasSubgaussianMGF.integrable
- ProbabilityTheory.HasSubgaussianMGF.mgf_le
- ProbabilityTheory.mgf_gaussianReal
- ProbabilityTheory.integrable_exp_mul_gaussianReal
- MeasureTheory.Integrable.bdd_mul
- MeasureTheory.integrable_map_measure
- MeasureTheory.ofReal_integral_eq_lintegral_ofReal
- Real.measurable_cos
- Real.abs_cos_le_one
- tendsto_natCast_atTop_iff
- tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
- Measurable.eval_matrix
- Matrix.measurable_apply
- StandardBorelSpace.pi_countable
- Set.mem_Iic
- Real.sin_sq_add_cos_sq
- MeasureTheory.Integrable.aestronglyMeasurable
- verified absent: integrable_id_gaussianReal (grep -rn over .lake/packages/mathlib/Mathlib: no hit); integrability of the Gaussian identity is via HasSubgaussianMGF.integrable instead

## (d) Open issues and paper-delta candidates
- T2327a (candidate): no paper statement is pinned for `gue_highProb_incr_le` (ticket); the proof of Thm `B_Univ` says "essentially identical to [YY_25, Theorem 2.6]" (`1_2_Intro_model_result.tex:569`). The Lean statement is RBM2D's: threshold `N = sz.size n`, grid range `gueGridK sz n0 n = (N+1)^(32 n₀+64)`, hard-coded constants `32 n₀ + 64`, `C = 32 n₀ + 68`, and the extra hypothesis `Tendsto sz.size atTop atTop` (without it a bounded size gives a constant failure probability).
- T2327b (candidate): `gueCondExp_freeze`, `gueHasCondSubgaussianMGF_of_frozen` are stated for `β : Type*` (ticket check: `β : Type`); the check-equality example (b5) instantiates the universe.
- Consumers named by the ticket (not checked here): UN-33 `BoundsA`, UN-34/35 `Drift`, UN-50 `PathBounds`. No merged file is changed (b8 diff stat).
- Mathlib API facts for `docs/mathlib-api.md`: `MeasureTheory.Integrable.bdd_mul` takes `(hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c)` with `{c}` implicit; `HasSubgaussianMGF.integrable` exists; `integrable_id_gaussianReal` does not.
