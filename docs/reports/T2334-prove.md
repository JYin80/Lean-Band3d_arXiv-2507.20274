Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 13:12:37 UTC 2026

Scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2334/` (python only; `eng.py`, `tree.py`, `canon.py`, `root.py` are copies of the T2265 stage-1a symbolic engine, read from `.../85663390-.../scratchpad/T2265/`).

### (i) Exponent table
(A) `LwGraphPrecJoin`, P normal packed, `LWJoined P` (`ext 0 ≠ ext 1`, one molecule, `n_M = 0`). Pathwise recipe: every solid factor `≤ Ψ` (non-loop solid pair ⇒ `×` edge ⇒ distinct labels ⇒ `G_ab = (G−M)_ab`; loops are circled by `Normal` (iv): `(G−M)_aa`), a waved spanning tree from `x`, `n_V` tree edges summed (row sums `≤ C_row·t`), the other `n_W − n_V` waved edges bounded by sup `≤ C t W^{-d}`.

| quantity | value | constraint | slack |
|---|---|---|---|
| `t`-power | `n_W` | `P.g.nW`; `n_W ≥ n_V + 1 ≥ 1` (molecule of `x` contains `y` and all internal vertices, `Normal` (ii) no `=` edges, so connected by waved edges) | `t n = 0` allowed: `n_W ≠ 0` ⇒ `P.val = 0` (S, S⁺ vanish at `u = 0`), RHS `= 0` |
| `W^{-d}`-power | `n_W − n_V` | `≥ 1` (needed to convert `W^{-d} → B`) | min over the 17 222 joined leaves of the script below: `1` |
| `Ψ`-power | `n_S` | `Ψ = N^{τ'} B^{1/2}` | — |
| `B`-exponent | `n_S/2 + (n_W − n_V) = ord/2`, `ord = n_S + 2(n_W − n_V)` | must equal the pin's `ord/2` | exact (script: all joined leaves) |
| `ord` of a joined leaf | `≥ 5` (`ext 0 ≠ ext 1`) | `5 ≤ ord`; so `B^{ord/2} ≤ B^{5/2}` as `B ≤ 1` (consumer) | min `ord − 5 = 0` (F2 term) |
| `W^{-d} ≤ (𝔡⁻²+1) B` | `STBctl_ge`: `W^{-d}(λ²+1)⁻¹ ≤ Bctl`, `λ ≤ 𝔡⁻¹` (`WO`, eventually) | `λ² + 1 ≤ 𝔡⁻² + 1 = 101` at `𝔡 = 1/10` | at the instance `W^{-d}/Bctl ≈ 0.92–0.94`, slack factor ≈ 108 |
| window `W^{-d/2} ≤ Ψ` | from the previous row and `N^{2τ'} ≥ 𝔡⁻²+1` (eventually, `N → ∞`) | `(Ψ² = N^{2τ'} B ≥ N^{2τ'} W^{-d}(λ²+1)⁻¹)` | eventual in `n` |
| `η⁻¹` | `η = (1−t) Im m(E) ∈ (0, 1]`, so `η⁻¹ ≥ 1` | the factor is only dropped (`≥ 1`) | at the instance `η = 0.9077` |
| `‖m^j m̄^{j'}‖` | `1` | `‖mE E‖ = 1` for `|E| ≤ 2` (`norm_mE`) | exact |
| row sum `C_row` | `Σ_b e^{-c‖b‖₁} ≤ coth(c/2)^d` (periodic `ℓ¹` block distance `lwBdist`, `Σ_y W^{-d} e^{-c·bdist(x,y)} ≤ coth(c/2)^d`); `S`: row sum `= u` exact | uniform in `L` | `c = 1`, `d = 3`: `≤ 10.13`; `L = 12`: `10.058` |
| `S⁺` size | `‖S⁺_xy‖ ≤ t Cs W^{-d} e^{-cs·bdist}` (`lwExpTerm3_Sp_decay`, `λ ≤ Λ = 𝔡⁻¹`, `|E| ≤ 2−κ`) | needs `0 < λ ≤ 𝔡⁻¹`, eventually | — |
| consumer exponent | `B^{ord/2}`, `ord ≥ 5` (distinct/joined), `≥ 4` (`x = y`) ⇒ `Λ N^{τ'} η⁻¹ (B^{5/2} + W^{-d} B²)` | same shape as merged `lwExpTerm3_T4pos` | unchanged |

Paper source `B:78-108`: `(Gammamuxy)` there is claimed through `GtoAG` for every `Γ_μ`; the T2265 report (`docs/reports/T2265-prove.md:15`) found joined leaves, outside `GtoAG` (distinct external molecules). Candidate `T2334a`: for joined graphs `(Gammamuxy)` is proved directly (above recipe), not through `GtoAG`.

### (ii) Concrete nondegenerate instance (d = 3, `sz0`, `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `t ≡ 1/16`, merged `flow_z0`, `tInst`)
Graph: the T2265 F2 term (`α = x`, `β = y`, internal `γ`; `m² Σ_γ S_{γx} S_{xy} G_{xγ} G_{γy} Ḡ_{xy}`), `Normal`, `LWJoined`. Script 1 runs the symbolic T2265 tree (all four `(k,s)`) and checks on every joined leaf: waved connectivity, spanning tree `= n_V + 1` edges, `n_W ≥ n_V + 1`, `n_M = 0`, `Normal`, `2(n_W−n_V) + n_S = ord`, `ord ≥ 5`, no uncircled loop.
```
$ cd .../scratchpad/T2334 && python3 joined_bound.py
k=False s=False joined leaves  4104, all-checks-ok  4104, with j'>0 1424, min(nW-nV) 1, min(ord-5) 0, stuck 0
k=False s=True  joined leaves  4507, all-checks-ok  4507, with j'>0    0, min(nW-nV) 1, min(ord-5) 0, stuck 0
k=True  s=False joined leaves  4104, all-checks-ok  4104, with j'>0 1424, min(nW-nV) 1, min(ord-5) 0, stuck 0
k=True  s=True  joined leaves  4507, all-checks-ok  4507, with j'>0    0, min(nW-nV) 1, min(ord-5) 0, stuck 0
example (depth 0, k=False s=False): coeff(sign,j,jbar)=(1, 2, 0) ext=['a+x', 'b+y'] ints=['c']
  solid [(True, False, 'a+x', 'c'), (True, False, 'c', 'b+y'), (False, False, 'a+x', 'b+y')]
  waved [(False, True, 'c', 'a+x'), (False, False, 'a+x', 'b+y')]  dotted [(False, 'a+x', 'c'), (False, 'c', 'b+y'), (False, 'a+x', 'b+y')]
  nS,nW,nV,nM = (3, 2, 1, 0)  ord = 5  t-power 2  W^-d power 1  Psi power 3  B-power nS/2+nW-nV = 2.5  = ord/2 = 2.5
```
Joined output of the expansion: this F2 term is a depth-0 term of the root partition; it is a leaf for any "expand while `ord < tgt`" rule, `leaf N := tgt N ≤ scalingOrder` (`Graph/LWExpCert.lean:147-150`, the rule of T2318's certificate); the T2265 tree is a python model, T2318's Lean list `expandRoot selClassical 4` was not evaluated here (no Lean run in 1a). The counts above (17 222 joined leaves in total) are those of the T2265 tree, not of T2318's list.

Hypotheses of `LwGraphPrecJoin` at the instance (script 2; exact definitions of `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`, `N = (WL)^3`, `z0 n = 1/2 + i N^{-4/5}`): `locDomain`, `WO` (`W^{-d/2+𝔡} ≤ λ ≤ 𝔡⁻¹`), `Bandwidth` (`N^{1/6} ≤ W`), `t ≤ lemT`, `STBctl_ge`, `Bctl ≤ 1`, `η ≤ 1`, `W^{-d} ≤ 101·Bctl`, `|mE E| = 1`:
```
$ python3 instance.py     (asserts all of the above for n = 0..6; rows 0, 1, 3, 6 shown)
n  W      L   lam        N          Im z0     E=lemE   lemT   locDom WO  BW   W^-d/B   (lam^2+1)  eta     B        t^2 eta^-1 B^2.5   t^2 W^-3 B^1.5 / that
0     32   4 1.562e-02 2.097e+06 8.76e-06 0.50000 0.99999 True True True 0.9233 1.000244 0.9077 3.305e-05 2.703e-14 0.838 True
1   1024   8 2.441e-04 5.498e+11 4.05e-10 0.50000 1.00000 True True True 0.9357 1.000000 0.9077 9.954e-10 1.345e-25 0.849 True
3  32768  16 3.815e-06 1.441e+17 1.88e-14 0.50000 1.00000 True True True 0.9373 1.000000 0.9077 3.032e-14 6.891e-37 0.851 True
6 537824  28 1.328e-07 3.415e+21 5.93e-18 0.50000 1.00000 True True True 0.9375 1.000000 0.9077 6.857e-18 5.298e-46 0.851 True
limit n->inf: W^d*Bctl -> 1/(1-t) = 1.0666666666666667  so W^-d/Bctl -> 0.9375 <= dd^-2+1 = 100.99999999999999
```
(`dd^-2` is `0.1**-2` in floating point; exactly `100`, so the bound is `101`.) Last column = `η W^{-d}/B ≈ 0.85 ≤ 1`: the pathwise product `t² W^{-3} B^{3/2}` is below the pinned bound `t² η⁻¹ B^{5/2}` already without the factor 101.

External hypothesis `STLocalEntry sz0 (STflowE z0) tInst` (`Induction/Defs.lean:151`, a stochastic premise of the gate that proves `(Gt_bound)`; not discharged here, stays a hypothesis of the instance). Lesson 14, concrete limit: Ward identity `Σ_y |G_xy|² = Im G_xx/η_t`, `G_xx ≈ m`, `|m| = 1`, `η_t = (1−t) Im m`, so `Σ_y |(G−M)_xy|² ≈ 1/(1−t) − 1 = t/(1−t) = 1/15`; the hypothesis' right side summed over `y` (each block has `W^d` points, `STWB = W^{-d} B_{t,K}`) must dominate it, and its diagonal value `Bctl → 0`:
```
$ python3 ward.py
n=0: blocks 64, sum_y STWB = 29.1482 >= Ward value t/(1-t) = 0.0667 : True ; per-site STWB(0)=Bctl=3.305e-05 -> 0
n=1: blocks 512, sum_y STWB = 145.0311 >= Ward value t/(1-t) = 0.0667 : True ; per-site STWB(0)=Bctl=9.954e-10 -> 0
n=2: blocks 1728, sum_y STWB = 358.8419 >= Ward value t/(1-t) = 0.0667 : True ; per-site STWB(0)=Bctl=2.270e-12 -> 0
n=3: blocks 4096, sum_y STWB = 672.8271 >= Ward value t/(1-t) = 0.0667 : True ; per-site STWB(0)=Bctl=3.032e-14 -> 0
$ python3 rowsum.py | grep 'c=1.0'
c=1.0 L= 4  sum_b exp(-c|b|_1) = 6.5507 <= coth(c/2)^d = 10.1331 : True
c=1.0 L= 8  sum_b exp(-c|b|_1) = 9.5865 <= coth(c/2)^d = 10.1331 : True
c=1.0 L=12  sum_b exp(-c|b|_1) = 10.0580 <= coth(c/2)^d = 10.1331 : True
```
Order of magnitude check of the left side of `(A)` on the F2 term: `|𝔼 Γ| ≲ t · (t C_row) · W^{-d} · (W^{-d/2})³ = t² W^{-5d/2}`; with `B ≈ (1−t)⁻¹ W^{-d}` (limit row above) this is the pinned `t² η⁻¹ B^{5/2}` up to the constants `(0.9375)^{5/2}` and `η`, i.e. neither side is vacuous or off in scale.

Targets (B)–(D), by reading the merged signatures (no Lean run): `LWG5Expand'` (`LWExpSound.lean:55`) has leaf conjunct "distinct external molecules ∨ `LWJoined`", `Normal`, `n_M ≤ 1`, `LWAttached`, `ord ≥ (4|5)`: the distinct branch feeds `lwGraphPrec1` (`LWExpTerm3.lean:1442`, takes `STLmax`, available in `LWExpG5'`), the joined branch `LwGraphPrecJoin` (needs only `STLocalEntry`, `Normal`, `LWJoined`). Coefficient `(mE E)^j · star(mE E)^{j'}` has norm 1. (C): `lwCutExp_of_G5' : LWExpG5' d → LWCutExp d` (`LWExpTerm4.lean:1717`) and `lwTermEXP_of_cut : LWCutExp d → LWtermEXP d` (`LWExpTerm.lean:286`). (D): `stStep6I_of_LW (d) (h : LWtermEXP d) : STStep6I d` (`ExpIntIQ.lean:1362`); `ST_step6_caseII_of_pins (hLK hLW hAvg hDu hInt hWd)` (`Step6Kit.lean:865`) against `stExpLKLKHi_holds`, `lwTermEXP_holds`, `stImproveExpAver_holds`, `stExpDuhamelZ_holds`, `stExpIntII_holds`, `stExpWardII_holds`, each `(d : ℕ) : P d` (`ExpEtermsA:607`, `ExpAvg:879`, `ExpDuhamel:385`, `ExpIntII:553`, `ExpWardII:419`); `ST_step6_caseIII_of_pins (hLK hLW hDu hInt)` (`Step6Kit.lean:737`) against `stExpLKLKHi_holds`, `lwTermEXP_holds`, `stExpDuhamelZ_holds`, `stExpIntIII_holds` (`ExpIntEasy:610`). Argument orders agree; `hS5` and the other `STIngR`-type premises are binders of the pins' bodies (`intro 𝔠 sz z hflow s t ... hS5`), not of the closures.

§29, one line each: (1) `0 ≤ t n ≤ lemT (z n)` hypotheses; `t < 1` derived from `STFlow` (`v3_premises_of_stFlow`), `t n = 0` handled (`n_W ≥ 1`). (2) no index-set boundary in `LwGraphPrecJoin`; the `λ²/L^d ≤ 1 − t` window of `LWExpG5'` is unchanged. (3) `L^d ≤ W^K` not used: `STBctl_ge` and the row sums are uniform in `L`. (4) `t`, `P` quantified `∀ n`; `λ ≤ 𝔡⁻¹` and `N^{2τ'} ≥ 101` used only eventually (inside `Prec`). (5) `Prec` (union inside probability), as `LwGraphPrec1`; no `PrecPT`. (6) `λ ≤ 𝔡⁻¹`, `0 < λ`, `SizeTendsto` come from `STFlow`/`WO` (not new hypotheses). (7) scale `N^{τ'}` (`Ψ = N^{τ'} B^{1/2}`), as `lwGraphPrec1`.

### Verdicts
- `LwGraphPrecJoin` / `lwGraphPrecJoin_holds`: PASS (statement true by the recipe; exponents close exactly, `ord/2 = n_S/2 + (n_W − n_V)`, slack `101` vs `1.07` in the `W^{-d} → B` conversion; instance nondegenerate, `STLocalEntry` a hypothesis of the instance with the limit check above).
- `lwExpG5'_of_expand'`, `lwExpG5'_holds`, `lwCutExp_holds`, `lwTermEXP_holds`: PASS.
- `stStep6I_holds`, `stStep6II_holds`, `stStep6III_holds`: PASS (signatures fit as read; no new hypothesis).
- Paper-delta candidate `T2334a` as above. Dead certificate modules (`LWExpCertS0/S1`) are not touched in 1a.

## (a′) Preflight corrections — Thu Oct  8 13:36:24 UTC 2026
Three statements of (a) differ from what the Lean proof uses; none changes a verdict (all targets stay PASS):
1. (a) row "`W^{-d}`-power `n_W − n_V ≥ 1` (needed to convert `W^{-d} → B`)" and the "window `W^{-d/2} ≤ Ψ`" row: the proof needs only `n_V ≤ n_W` (`LGraph.counters_le`); `(W^{-d})^k ≤ (𝔡⁻²+1)^k B^k` holds for `k = 0` as well, and the window is not used.
2. (a) row "row sum `C_row ≤ coth(c/2)^d`": the proof uses the merged `lwKBound_of_decay` constant `C expC (d-2) c` (`Defs/RadialSum.lean`, `sum_radial_exp_decay_le`).
3. (a) "a waved spanning tree of the molecule from `x`": the proof uses `LGraph.waved_sum_le` (a forest with all external vertices as roots, same count `n_V` tree edges, `n_W − n_V` sup edges); `LWJoined` enters only through `n_M = 0`.

## (b) Script output — Thu Oct  8 13:36:24 UTC 2026
### Commits and build
```
$ git log --format='%h %ci %s' main..t/T2334
4982248 2026-10-08 06:30:58 -0700 T2334: instances, registry (six owed lines deleted), lint cleanup (section 7)
1bfe500 2026-10-08 06:24:27 -0700 T2334: consumer lwExpG5'_of_expand', unconditional chain and Step 6 closures (sections 5-6)
8a46721 2026-10-08 06:22:34 -0700 T2334: LwGraphPrecJoin and lwGraphPrecJoin_holds (sections 1-4)
$ wc -l RBM3D/Graph/LWExpTerm6.lean ; git diff --stat main...t/T2334
     754 RBM3D/Graph/LWExpTerm6.lean
 RBM3D/Graph/LWExpTerm6.lean | 754 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |   6 -
 2 files changed, 754 insertions(+), 6 deletions(-)
$ lake build RBM3D.Graph.LWExpTerm6        (tail; no warning, no error from LWExpTerm6.lean)
info: RBM3D/Induction/ExpIntEasy.lean:764:0: 'RBM.Gauss.Step6Inst.inst_expIntIV_rate_le_target' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3918 jobs).
0
$ grep -nE 'sorry|admit|native_decide|^axiom ' RBM3D/Graph/LWExpTerm6.lean | wc -l
       0
```
### `#print axioms` (lake env lean axioms.lean | sed 's/depends on axioms: //'; `S.` = `RBM.Gauss.Sizes.`, `..` = `RBM.Gauss.Sizes.`; eight targets, three helpers, twelve instance declarations)
```
'S.lwGraphPrecJoin_holds' [propext, Classical.choice, Quot.sound]
'S.lwExpG5'_of_expand'' [propext, Classical.choice, Quot.sound]
'S.lwExpG5'_holds' [propext, Classical.choice, Quot.sound]
'S.lwCutExp_holds' [propext, Classical.choice, Quot.sound]
'S.lwTermEXP_holds' [propext, Classical.choice, Quot.sound]
'S.stStep6I_holds' [propext, Classical.choice, Quot.sound]
'S.stStep6II_holds' [propext, Classical.choice, Quot.sound]
'S.stStep6III_holds' [propext, Classical.choice, Quot.sound]
'S.lwExpTerm6_pathwise' [propext, Classical.choice, Quot.sound]
'S.lwExpTerm6_arith' [propext, Classical.choice, Quot.sound]
'S.lwExpTerm6_T4pos' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_instGraph_normal' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_instGraph_nM' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_instGraph_joined' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_instGraph_counters' [propext,
 Classical.choice,
 Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_join' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_expand' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_G5' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_cut' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_term' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_step6I' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_step6II' [propext, Classical.choice, Quot.sound]
'..LWExpTerm6Inst.lwExpTerm6_inst_step6III' [propext, Classical.choice, Quot.sound]
```
### Target statements (python extract.py: lines of RBM3D/Graph/LWExpTerm6.lean up to `:=`; proofs not shown)
```
55: def LwGraphPrecJoin (d : ℕ) : Prop :=
56:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
57:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
58:       ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
59:         STLocalEntry sz (STflowE z) t →
60:         ∀ P : PGraph (Fin 2), P.g.Normal → LWJoined P →
61:           Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
62:             (fun n p _ => ‖∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖)
63:             (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
64:               (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))

187: theorem lwGraphPrecJoin_holds (d : ℕ) : LwGraphPrecJoin d :=
462: theorem lwExpG5'_of_expand' (d : ℕ) : LWG5Expand' d → LwGraphPrecJoin d → LWExpG5' d :=
613: theorem lwExpG5'_holds : ∀ d : ℕ, LWExpG5' d :=
617: theorem lwCutExp_holds : ∀ d : ℕ, LWCutExp d :=
620: theorem lwTermEXP_holds : ∀ d : ℕ, LWtermEXP d :=
623: theorem stStep6I_holds : ∀ d : ℕ, STStep6I d :=
626: theorem stStep6II_holds : ∀ d : ℕ, STStep6II d :=
631: theorem stStep6III_holds : ∀ d : ℕ, STStep6III d :=
```
### Compiled instances (namespace `RBM.Gauss.Sizes.LWExpTerm6Inst`; all in the file, lines 634-754; `STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay` and the premises of `InstIng6Concl` are other gates' pins and stay hypotheses)
```
644: def lwExpTerm6_instGraph : LGraph (Fin 2) (Fin 1) where
645:   solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inl 1),
646:     SEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
647:   waved := [WEdge.mk false true (Sum.inr 0) (Sum.inl 0), WEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
648:   dotted := [DEdge.mk false (Sum.inl 0) (Sum.inr 0), DEdge.mk false (Sum.inr 0) (Sum.inl 1),
649:     DEdge.mk false (Sum.inl 0) (Sum.inl 1)]
650:   coeff := 1
652: theorem lwExpTerm6_instGraph_normal : lwExpTerm6_instGraph.Normal := by decide
654: theorem lwExpTerm6_instGraph_nM : lwExpTerm6_instGraph.nM = 0 := by decide
656: theorem lwExpTerm6_instGraph_joined : LWJoined lwExpTerm6_instGraph.pack := by
657:   refine ⟨by decide, ?_, lwExpTerm6_instGraph_nM⟩
658:   change lwExpTerm6_instGraph.molOf (Sum.inl 0) = lwExpTerm6_instGraph.molOf (Sum.inl 1)
659:   rw [LGraph.molOf_eq_iff]
660:   decide
663: theorem lwExpTerm6_instGraph_counters :
664:     lwExpTerm6_instGraph.nS = 3 ∧ lwExpTerm6_instGraph.nW = 2 ∧ lwExpTerm6_instGraph.nV = 1 ∧
665:       lwExpTerm6_instGraph.scalingOrder = 5 := by
671: theorem lwExpTerm6_inst_join (hLE : STLocalEntry sz0 (STflowE z0) tInst) :
672:     Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
673:       (fun n p _ => ‖∫ ω, (lwExpTerm6_instGraph.pack).val (LWG5Data sz0 n (STflowE z0 n) (tInst n) ω) ![p.1, p.2] ∂(sz0.seqP)‖)
674:       (fun n _ _ => (tInst n) ^ (lwExpTerm6_instGraph.pack).g.nW * (etaT (STflowE z0 n) (tInst n))⁻¹ *
675:         (sz0.Bctl n (tInst n)) ^ (((lwExpTerm6_instGraph.pack).g.scalingOrder : ℝ) / 2)) :=
676:   lwGraphPrecJoin_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
677:     tInst tInst_range.1 tInst_range.2 hLE (lwExpTerm6_instGraph.pack) lwExpTerm6_instGraph_normal
678:     lwExpTerm6_instGraph_joined
736: theorem lwExpTerm6_inst_step6I :
737:     RBM.Gauss.Step6Inst.InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
738:   RBM.Gauss.Step6Inst.inst_step6I (stStep6I_holds 3)
741: theorem lwExpTerm6_inst_step6II :
742:     RBM.Gauss.Step6Inst.InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
743:   RBM.Gauss.Step6Inst.inst_step6II (stStep6II_holds 3)
746: theorem lwExpTerm6_inst_step6III :
747:     RBM.Gauss.Step6Inst.InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
748:   RBM.Gauss.Step6Inst.inst_step6III (stStep6III_holds 3)
682:theorem lwExpTerm6_inst_expand (hLE : STLocalEntry sz0 (STflowE z0) tInst)
683-    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
698:theorem lwExpTerm6_inst_G5 (hLE : STLocalEntry sz0 (STflowE z0) tInst)
699-    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
714:theorem lwExpTerm6_inst_cut (hLE : STLocalEntry sz0 (STflowE z0) tInst)
715-    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
725:theorem lwExpTerm6_inst_term (hLE : STLocalEntry sz0 (STflowE z0) tInst)
726-    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
```
`lwExpTerm6_instGraph` = the T2265 F2 term `Σ_γ S_{γx} S_{xy} G_{xγ} G_{γy} Ḡ_{xy}` (n_S = 3, n_W = 2, n_V = 1, ord = 5, `×`-dotted on the three solid pairs); it is `Normal`, `n_M = 0`, `LWJoined` by `decide`.
### Registry pre-check (temporary scratch file outside the repo: `import RBM3D` + `import RBM3D.Graph.LWExpTerm6` + `#assert_rbm_axioms`; after `lake build RBM3D.Test.Axioms` of the edited registry)
```
$ lake env lean precheck.lean > precheck.log 2>&1 ; echo exit=$?
exit=0
axiom audit: 10123 theorems, 3013 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
premises found by scanning: 141 (borrowed 1, owed 80, structural 41, refuted 6, superseded 13).
registry: 2 borrowed + 128 owed + 106 structural + 7 refuted + 14 superseded; 116 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,   [lines cut at 210 chars]
non-vacuity certificates: 0 of 130 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ grep -cE 'LWExpG5|LWCutExp|LWtermEXP|STStep6I|LwGraphPrecJoin' precheck.log
0
```
No newly unregistered premise is reported.  Registry edit: six registry lines of `RBM3D/Test/Axioms.lean` deleted by text anchor, nothing added (names of the deleted lines):
```
LWtermEXP LWCutExp LWExpG5' STStep6I STStep6II STStep6III
```
### Full `lake build` (the root import `import RBM3D.Graph.LWExpTerm6` was added to RBM3D.lean temporarily, uncommitted, and removed afterwards: `git status --short` shows no RBM3D.lean change)
```
$ lake build  > fullbuild.log ; echo exit=$?
exit=0
info: RBM3D.lean:377:0: axiom audit: 10123 theorems, 3013 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4144 jobs).
lake build  41.76s user 6.11s system 105% cpu 45.477 total
```
### Check-file equality
```
$ python3 cmp_pin.py   # docstring + `def LwGraphPrecJoin` of docs/tickets/checks/T2334-check.lean vs RBM3D/Graph/LWExpTerm6.lean, whitespace-normalized
check-file def == Lean file def (docstring + def, whitespace-normalized): True
771 771
$ lake env lean check_eq.lean ; echo exit=$?   # check file + `import RBM3D.Graph.LWExpTerm6` + eight `example : RBM.Gauss.Sizes.T2334Check.T2334_<n> := RBM.Gauss.Sizes.<n>`
exit=0
eight examples elaborate:
lwGraphPrecJoin_holds lwExpG5'_of_expand' lwExpG5'_holds lwCutExp_holds lwTermEXP_holds stStep6I_holds stStep6II_holds stStep6III_holds
```
### Name-clash grep (RBM3D/ and RBM3D.lean outside Probe/ and outside the new file; `grep -rnF`, hits per new public name)
```
LwGraphPrecJoin: 0; lwGraphPrecJoin_holds: 0; lwExpG5'_of_expand': 0; lwExpG5'_holds: 0; lwCutExp_holds: 0; lwTermEXP_holds: 0; stStep6I_holds: 0; stStep6II_holds: 0; stStep6III_holds: 0; lwExpTerm6_: 0; LWExpTerm6: 0
```
### Old certificate modules (`LWExpCertS0/S1`, unprimed `cert_all`): consumers
```
$ grep -rn 'import RBM3D.Graph.LWExpCertS0\|import RBM3D.Graph.LWExpCertS1' RBM3D RBM3D.lean --include='*.lean' | grep -v Probe/
RBM3D/Graph/LWExpCertS1.lean:7:import RBM3D.Graph.LWExpCertS0
RBM3D.lean:350:import RBM3D.Graph.LWExpCertS0
RBM3D.lean:351:import RBM3D.Graph.LWExpCertS1
$ grep -rnw 'cert_all' RBM3D RBM3D.lean --include='*.lean' | grep -v Probe/ | grep -v 'RBM3D/Graph/LWExpCert[B]*S[01].lean' | grep -v '^RBM3D/Graph/LWExpCert.lean'   # (word match, also matches `cert_all'`; outside LWExpCertS1/LWExpCert/LWExpCertB*)
RBM3D/Graph/LWExpSound.lean:13:The AND-tree certificate `cert_all'` (T2319, kernel) is carried through the simulation relation
RBM3D/Graph/LWExpSound.lean:1397:  obtain ⟨hflag, hall⟩ := cert_all' s
```
Consumers: none (only `LWExpCertS1.lean:7` imports `LWExpCertS0`, and `RBM3D.lean:350-351` imports both; the two remaining hits are the primed `cert_all'` of `LWExpSound.lean`).  The dispatcher can schedule the deletion of both modules and their two root imports.
### Ports from RBM1D/RBM2D: none (no `../RBM1D`, `../RBM2D` file read for this ticket; no `git -C ../RBM*` command run).  Intra-project copies: `lwExpTerm3_T4pos` (`Graph/LWExpTerm3.lean:1859-1953`) and `lwExpG5'_of_expand` (`:2031-2171`), commit of main `5b6221f`.

### Narrative
* New file `RBM3D/Graph/LWExpTerm6.lean` (754 lines, stop size 1400), imports the five modules of the check file that are not transitive (`LWExpSound`, `LWExpTerm4`, `ExpIntIQ`, `ExpWardII`, `ExpIntEasy`; `Step6Kit`, `ExpEtermsA`, `ExpAvg`, `ExpDuhamel`, `ExpIntII` are imported by `ExpIntIQ`/`ExpWardII`/`ExpIntEasy`; the check section 1 compiled with this reduced list).
* (A) `lwGraphPrecJoin_holds` does not go through `GtoAG`.  `lwExpTerm6_pathwise` (l. 76-146): on the entry event `‖(G−M)_{xy}‖ ≤ Ψ` every solid factor is `≤ Ψ` (merged `LGraph.term_norm_le`), the waved factors are summed by the merged `LGraph.waved_sum_le` with `lwKBound_of_decay` (`n_V − n_M` tree edges cost `t Cs expC`, the other `n_W − n_V + n_M` cost `t Cs W^{-d}`), giving `t^{n_W} C_Γ Ψ^{n_S} (W^{-d})^{n_W−n_V}` for `n_M = 0`.  `lwExpTerm6_arith` turns it into `N^τ η⁻¹ B^{ord/2}` with `Ψ = N^{τ'} B^{1/2}`, `W^{-d} ≤ (𝔡⁻²+1) B` (`STBctl_ge`, `λ ≤ 𝔡⁻¹`), `η ≤ 1`, `ord = n_S + 2(n_W − n_V)` (`τ' = τ/(2(n_S+1))`).
* The `≺ → 𝔼` skeleton is that of `lwGraphPrec1` (`LWExpTerm3.lean:1442-1657`: `X = t^{-n_W} Γ`, envelope `lwExpTerm3_X_norm_le`, floor `lwExpTerm3_floor`, `StochDomAt.of_highProbAt_add_rpow_neg`, `lwExpTerm_prec_integral`), with the single event `lwExpTerm3_entry_whp` (no `ξ` event, no `lwGbyXi`, no tail, no window `W^{-d/2} ≤ Ψ`, no `STLmax`).  `LWJoined` is used only through `n_M = 0`: the proved statement holds for every normal packed graph with `n_M = 0`; `ext 0 ≠ ext 1` is used by the consumer (`ord ≥ 5`).
* (B) `lwExpTerm6_T4pos` (copy of `lwExpTerm3_T4pos`: list type `List ((ℕ × ℕ) × PGraph (Fin 2))`, coefficient `(mE E)^j · (star (mE E))^{j'}`, its norm `1` by `norm_mE`) and `lwExpG5'_of_expand'` (copy of `lwExpG5'_of_expand`: the leaf disjunction "distinct external molecules ∨ `LWJoined`" is split, the first branch by `lwGraphPrec1`, the second by the hypothesis `LwGraphPrecJoin d`).
* (C), (D) are the one-liners of the ticket: `lwExpG5'_holds`, `lwCutExp_holds` (`lwCutExp_of_G5'`), `lwTermEXP_holds` (`lwTermEXP_of_cut`), `stStep6I_holds` (`stStep6I_of_LW`), `stStep6II_holds` (`ST_step6_caseII_of_pins`, six ingredients), `stStep6III_holds` (`ST_step6_caseIII_of_pins`, four ingredients); argument orders agree as read in (a).
* Registry: the six owed lines `LWtermEXP`, `LWCutExp`, `LWExpG5'`, `STStep6I`, `STStep6II`, `STStep6III` of `RBM3D/Test/Axioms.lean` deleted, no line added.  Only the two writable files differ from `main`.
* Instances: `lwExpTerm6_inst_join` applies `lwGraphPrecJoin_holds` at `d = 3`, `sz0`, `z0`, `tInst ≡ 1/16`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6` to the F2 graph; `_expand`, `_G5`, `_cut`, `_term` apply the consumer and the proved chain at the same data; `_step6I/II/III` apply the closures at the merged data of `inst_step6I/II/III` (`Induction/Step6Pins.lean:560-570`).

## (c) Verified Mathlib names — Thu Oct  8 13:36:25 UTC 2026  (scratch `names.lean`, `lake env lean`, exit 0, no error; names verified absent: none looked up)
- `Real.rpow_natCast`: `#check` ok
- `Real.rpow_mul`: `#check` ok
- `Real.sqrt_eq_rpow`: `#check` ok
- `Real.rpow_add`: `#check` ok
- `Real.rpow_le_rpow_of_exponent_le`: `#check` ok
- `one_le_inv₀`: `#check` ok
- `div_le_div_iff₀`: `#check` ok
- `div_mul_eq_mul_div`: `#check` ok
- `norm_sum_le`: `#check` ok
- `Finset.mul_sum`: `#check` ok
- `Finset.sum_le_sum`: `#check` ok
- `inv_mul_cancel₀`: `#check` ok

## (d) Open issues and paper-delta candidates
- **T2334a** (`B:78-108`, `(eq:sizeGammamu_E)`, `(Gammamuxy)`): the paper obtains `(Gammamuxy)` from `GtoAG` for every `Γ_μ`; for joined `Γ_μ` (both external vertices in one molecule, `n_M = 0`) `GtoAG` is not the route (T2265a).  Lean proves it directly: `|Γ_{xy}| ≤ t^{n_W} C_Γ Ψ^{n_S} (W^{-d})^{n_W−n_V}` on `‖(G−M)_{xy}‖ ≤ Ψ` for every normal graph with `n_M = 0`, then `W^{-d} ≤ (𝔡⁻²+1) B` (`STBctl_ge`): no `ξ`, no `scalemole`, no window, only `STLocalEntry` (not `STLmax`).
- **T2334b** (remark, not a statement difference): `lwGraphPrecJoin_holds` is proved for `LWJoined P` as pinned; the proof uses only `P.g.nM = 0`.
- **Instances**: `STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay` and the stochastic premises of `InstIng6Concl` (`STLK`, `STDecay`, `STExp2`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW`) stay hypotheses of the instances (other gates' pins).  Lesson 14 (concrete limit of `STLocalEntry`) was checked in (a).
- **Dead modules**: `LWExpCertS0/S1` and the unprimed `cert_all` have no consumer (above); deletion not done here (sole-writable-file rule).
- **Hub at merge**: add `import RBM3D.Graph.LWExpTerm6` after the last `import` line of `RBM3D.lean`.  Without it the full `lake build` of this branch fails (script output, `lake build` at the committed state, exit 1):
```
error: RBM3D.lean:376:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Gauss.Sizes.LWExpG5']
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed).
```
  With the temporary root import the full build passes (above).
- No `STStep6IV` closure here (not in the ticket).
