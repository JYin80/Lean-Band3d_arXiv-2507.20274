Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 16:13:36 UTC 2026

Source: RBM2D `Evolution/CltSwap.lean` at `c9a24cf` (385 lines; read by `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Evolution/CltSwap.lean`; `$HOME/mnt/RBM2D` does not exist, `../RBM2D` is used).  RBM2D `HEAD` is `9e0f275`; that file differs between `c9a24cf` and `HEAD` (`git diff --stat`: 31 insertions, 98 deletions), so only `c9a24cf` is the source.  The model lemmas used are RBM2D `Gauss/Model.lean` at `c9a24cf`.

### (i) Exponent table and dictionary

The statements involve no exponent or threshold.  The only constants are `d`, `L`, `W` (index sizes), `g` (variance parameter, a free real), and the cardinality `card(CoordF d L W) = 2 (W L)^{2d}`.

| quantity | value / constraint | slack |
|---|---|---|
| `d` | any `ℕ`; no `3 ≤ d` needed (no Θ, no lattice-sum estimate) | instance uses `d = 3` |
| `L`, `W` | `[NeZero L] [NeZero W]` only | instance `L = 3`, `W = 1`; `sz0` at `n = 0`: `L = 4`, `W = 32` |
| `g` | free `g : ℝ`; `gvarF` is `ℝ≥0`-valued for every `g` by `svarF_nonneg` (`FineModel.lean:51`) | instance `g = 1/2` |
| `card CoordF` | `2 (W L)^{2d}` (merged `Path/StepDecomp.lean:476`) | `1458` at `(3,3,1)` |
| telescope length | `Fintype.card (CoordF d L W)` | `1458` terms at `(3,3,1)` |

Dictionary (RBM2D at `c9a24cf` → RBM3D merged; RBM3D lines from `grep -n` of `RBM3D/Gauss/FineModel.lean` and `RBM3D/Defs/Sizes.lean`):

| RBM2D name (`Gauss/Model.lean`) | RBM3D name | merged location |
|---|---|---|
| `Coord L W` (:102) | `CoordF d L W` | `FineModel.lean:80` |
| `Ω L W` (:105) | `Ω d L W` | `FineModel.lean:84` |
| `gvar L W c` (:108) | `gvarF d L W g c` | `FineModel.lean:89` |
| `P L W` (:127) | `PF d L W g` | `FineModel.lean:97` |
| `Sizes.SeqΩ d` | `Sizes.SeqΩ sz` (`sz : Sizes d`, `d` = dimension) | `FineModel.lean:160` |
| `Sizes.seqP d` (:434) | `Sizes.seqP sz` | `FineModel.lean:169` |
| `Sizes.slice d n` (:442) | `Sizes.slice sz n` | `FineModel.lean:176` |
| `Sizes.measurable_slice d n` (:444) | `Sizes.measurable_slice sz n` | `FineModel.lean:178` |
| `Sizes.seqP_map_slice d n` (:457), law `P (d.L n) (d.W n)` | `Sizes.seqP_map_slice sz n`, law `PF d (sz.L n) (sz.W n) (sz.lam n)` | `FineModel.lean:184` |
| `Sizes d` (`d.L n`, `d.W n`) | `Sizes d` with fields `L W lam`, instances `neZeroL`, `neZeroW` | `Defs/Sizes.lean:138, 152, 153` |
| pattern `measurePreserving_rowSplit` | same, `seqP` version | `Green/FlucVanish.lean:151` |

`sz0` is `RBM.Gauss.SizesInst.sz0 : Sizes 3` (`Defs/Sizes.lean:260`), `L n = 4 (n+1)`, `W n = (2 (n+1))^5`, `lam n = (2 (n+1))^{-6}`.

Variable lists: RBM2D `variable (L W : ℕ) [NeZero L] [NeZero W]` becomes `variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]`.  Declarations whose statements do not mention `P` (`cltSplit`, `cltHybSet`, `cltHyb`, `CltTelescope`, `cltHyb_*`, `cltSwap`, `update_cltSwap_fst`, `cltTelescope`) do not take `g`.  `cltTransfer` takes `{d : ℕ} (sz : Sizes d)` (RBM2D: `(d : Sizes)`).

Differences between RBM2D `P` and merged `PF` that touch the proofs:
- (P1) `Measure.infinitePi`: `PF d L W g := Measure.infinitePi fun c => gaussianReal 0 (gvarF d L W g c)` (`FineModel.lean:97`) is the same shape as RBM2D `P`; `change _ = Measure.infinitePi _`, `Measure.eq_infinitePi`, `Measure.infinitePi_pi` (`ProductMeasure.lean:385`, name verified present) are used as in `Green/FlucVanish.lean:151–163`; `rw [P, …]` becomes `rw [PF, …]`, `show P L W _ * P L W _` becomes `show PF d L W g _ * PF d L W g _`.
- (P2) Variances `gvarF`: only enter through `PF`'s definition; the proof of `measurePreserving_cltSwap` sets `μ c' := gaussianReal 0 (gvarF d L W g c')` and `PF d L W g = Measure.pi μ` by `Measure.infinitePi_eq_pi μ` (`ProductMeasure.lean:507`, needs `[Fintype CoordF]`).  No property of `gvarF` (diagonal/off-diagonal values, `g`) is used, so no hypothesis on `g` is added.
- (P3) Measurability of the split: the proof (`measurable_pi_iff`, `measurable_pi_apply`, `measurable_fst/snd`) only uses the product-of-reals structure of `Ω d L W = CoordF d L W → ℝ`; unchanged.
- (P4) `Fintype (CoordF d L W)`: `Idx d L W = Zd d (W*L) = Fin d → ZMod (W*L)` (`Defs/Sizes.lean:46`, `Defs/Lattice.lean:63`); the instance comes from `NeZero (W*L)` (from `[NeZero L] [NeZero W]`, as in the merged `Path/StepDecomp.lean:476` and `Green/RowIndep.lean:585`, which use `Fintype.card (CoordF …)` and `Finset.univ` on `CoordF`).  Decidable equality on `CoordF` is the product/pi/`ZMod`/`Bool` instance, as RBM2D's `Z2 (W*L)`.
- (P5) The RBM2D check `card_coord_one_one` (`simp [Coord, Idx, Z2, …]`, `L = W = 1`, two coordinates) does not transfer: at `d = 3`, `L ≥ 3` (the check uses `L = 3`) the number of coordinates is `1458`, so the explicit two-term expansion is replaced by the applied statement (see (ii)).  The merged `Path/StepDecomp.lean:477` shows `card (CoordF d L W) = 2 (card (Idx d L W))^2`, available for any card computation.
- (P6) `cltTransfer`: the proof `rw [← seqP_map_slice, integral_map …]` is unchanged; `seqP_map_slice` has the law `PF d (sz.L n) (sz.W n) (sz.lam n)`, so the RBM3D statement reads `∫ ω, f (slice sz n ω) ∂(seqP sz) = ∫ ω, f ω ∂(PF d (sz.L n) (sz.W n) (sz.lam n))`, i.e. the variance parameter is `sz.lam n` (not a free `g`).  This is the only statement whose right-hand law is determined by the size data.

One line per ported statement (all 20 public declarations; "unchanged" = unchanged up to the dictionary, parameter `d`, and `g` where `P` occurs):

| declaration | status |
|---|---|
| `cltSplit`, `cltHybSet`, `cltHyb`, `cltSwap` | unchanged (`CoordF d L W`, `Ω d L W`); no `g` |
| `CltTelescope`, `cltTelescope`, `cltHyb_zero`, `cltHyb_card`, `cltHyb_succ`, `cltHyb_eq_update_succ`, `cltHyb_cltSwap`, `cltHyb_succ_cltSwap`, `update_cltSwap_fst` | unchanged; pure combinatorics of `Function.update` and the enumeration `e`; no `g`, proofs verbatim |
| `MeasurePreservingCltSplit`, `MeasurePreservingCltSwap`, `IntegralEqZeroOfCltSwapNeg` | unchanged with `P L W` → `PF d L W g` and parameter `g`; `Prop` definitions (no hypothesis added) |
| `measurePreserving_cltSplit`, `measurePreserving_cltSwap`, `integral_eq_zero_of_cltSwap_neg` | unchanged with `g` added; proofs via (P1)–(P3); `integral_eq_zero_of_cltSwap_neg` uses only `MeasurePreserving.integral_comp'` and `integral_neg` |
| `cltTransfer` | `d : Sizes` → `sz : Sizes d`; law `PF d (sz.L n) (sz.W n) (sz.lam n)` (P6); statement is RBM2D's up to this |

None of the 20 needs a hypothesis on `g` or a different law: the ticket's stop condition does not fire.  Name clash: none of the 20 names occurs in `RBM3D` (`grep -rlw`, output below).  RBM2D's `Checks` section contains only `example`s and its `#print axioms` lines (20 lines, unregistered); no `@[simp]` or `instance` is declared there.

### (ii) One concrete nondegenerate instance

Instance A (one-size, `d = 3`, `L = 3`, `W = 1`, `g = 1/2`): all four targets `measurePreserving_cltSplit 3 3 1 (1/2)`, `measurePreserving_cltSwap`, `integral_eq_zero_of_cltSwap_neg`, `cltTelescope` are applied at these data; their only hypotheses are `[NeZero 3] [NeZero 1]`; the enumeration `e = Fintype.equivFin (CoordF 3 3 1)` has `1458` elements (a nonempty coordinate set, so a nonempty `S` and `c` exist); `F` in `integral_eq_zero_of_cltSwap_neg` can be the antisymmetric `F p = (p.1 c : ℂ) - (p.2 c : ℂ)` (`F ∘ cltSwap c = -F` holds at once: the swap exchanges `p.1 c` and `p.2 c`).  Instance B (sequence, `cltTransfer`): `sz = RBM.Gauss.SizesInst.sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`), `f = fun ω => (ω c0 : ℂ)` (measurable) for a coordinate `c0`.  Every hypothesis is a typeclass or `Measurable f`; no external hypothesis occurs (the tickets's "no premise expected"; nothing to register), hence no limit computation is owed.

```
$ python3 $SCRATCH/T2140/inst.py
d,L,W,g = 3 3 1 1/2 ; NeZero L,W:  True True
|Idx|=(W*L)^d = 27 ; |CoordF|=2|Idx|^2 = 1458 (>=2: telescope has 1458 terms; enumeration e: CoordF ≃ Fin 1458 )
gvarF diag (i,i,b) = 2/5 = 0.4 -> True ; offdiag variance = S_ij/2 >= 0 (svarF_nonneg for every g)
sz0 n=0: L,W,lam = 4 32 1/64 ; 3<=L: True ; 0<W: True ; size=(W*L)^3 = 2097152 ; |CoordF| = 8796093022208
$ for n in <20 names>; do grep -rlw "$n" RBM3D | wc -l; done      # each of the 20 names
0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
$ ls RBM3D/Evolution/CltSwap.lean
ls: RBM3D/Evolution/CltSwap.lean: No such file or directory
```
(`$SCRATCH` is the session scratchpad; `gvarF` diagonal value from `svarF_diag`, `FineModel.lean:61`: `W^{-d} (1 + 2 d g²)^{-1} = 1/(1 + 2·3/4) = 2/5`.)  The `|CoordF|` value at `sz0` is only the cardinality of the index set; no proof computes it.

### Verdicts

- Target 1 (port of the 20 public declarations, dictionary, no extra hypothesis): PASS.
- Target 2 (docstrings: paper arXiv:2507.20274 `(eq:bound_isolated)` `3_5:2245`, cites [DYYY25] (7.39); i.i.d. copy and exchange not in the paper; RBM2D docstring says so for its paper): PASS (no mathematical content).
- Checks at `d = 3`, `L = 3`, `W = 1`, `g = 1/2` and `cltTransfer` at `sz0`: PASS; the RBM2D two-term `L = W = 1` unfolding is replaced by the applied `cltTelescope` (P5).

## (b) Script output — Sun Oct  4 16:17:31 UTC 2026

```
$ git log -1 --format=%h t/T2140; git diff --stat main...t/T2140
4a77a7f
 RBM3D/Evolution/CltSwap.lean | 365 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 365 insertions(+)

$ lake build RBM3D.Evolution.CltSwap 2>&1 | grep -v ^trace | tail -3
Build completed successfully (3244 jobs).

$ lake build   # full library at t/T2140 (root import not yet added; hub adds it at merge)
non-vacuity certificates: 0 of 75 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3887 jobs).

$ printf "import RBM3D
import RBM3D.Evolution.CltSwap
#assert_rbm_axioms
" > reg.lean; lake env lean reg.lean  # registry pre-check with the new module
premises found by scanning: 74 (borrowed 0, owed 55, structural 19).
lean exit=0

$ lake env lean ax.lean   # #print axioms of the 20 public declarations
'RBM.Evol.cltSplit': [propext, Classical.choice, Quot.sound]
'RBM.Evol.MeasurePreservingCltSplit': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHybSet': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb': [propext, Classical.choice, Quot.sound]
'RBM.Evol.CltTelescope': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltSwap': [propext, Classical.choice, Quot.sound]
'RBM.Evol.MeasurePreservingCltSwap': [propext, Classical.choice, Quot.sound]
'RBM.Evol.IntegralEqZeroOfCltSwapNeg': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb_zero': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb_card': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltTelescope': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb_succ': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb_eq_update_succ': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb_cltSwap': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltHyb_succ_cltSwap': [propext, Classical.choice, Quot.sound]
'RBM.Evol.update_cltSwap_fst': [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltTransfer': [propext, Classical.choice, Quot.sound]
'RBM.Evol.measurePreserving_cltSplit': [propext, Classical.choice, Quot.sound]
'RBM.Evol.measurePreserving_cltSwap': [propext, Classical.choice, Quot.sound]
'RBM.Evol.integral_eq_zero_of_cltSwap_neg': [propext, Classical.choice, Quot.sound]

$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Evolution/CltSwap.lean | grep -v "#print"
(no matches above)

$ name-clash: for each of the 21 names (20 public + private helper), grep -rlw RBM3D excluding the new file | wc -l
       0        0        0        0        0        0        0        0        0        0        0        0        0        0        0        0        0        0        0        0        0 

$ RBM2D source and drift
source commit c9a24cf (RBM2D/Evolution/CltSwap.lean, 385 lines); RBM2D HEAD 9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/CltSwap.lean | tail -1
 1 file changed, 31 insertions(+), 98 deletions(-)

$ python3 ext.py   # each target statement, extracted from the file (Prop defs in full; theorems up to `:= by`)
def MeasurePreservingCltSplit : Prop :=
  ∀ S : Finset (CoordF d L W),
    MeasurePreserving (fun p : Ω d L W × Ω d L W => cltSplit d L W S p.1 p.2)
      ((PF d L W g).prod (PF d L W g)) (PF d L W g)

def CltTelescope : Prop :=
  ∀ (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (Φ : Ω d L W → ℂ) (ω ω' : Ω d L W),
    Φ ω - Φ ω' = ∑ k ∈ Finset.range (Fintype.card (CoordF d L W)),
      (Φ (cltHyb d L W e k ω ω') - Φ (cltHyb d L W e (k + 1) ω ω'))

def MeasurePreservingCltSwap : Prop :=
  ∀ c : CoordF d L W,
    MeasurePreserving (cltSwap d L W c) ((PF d L W g).prod (PF d L W g)) ((PF d L W g).prod (PF d L W g))

def IntegralEqZeroOfCltSwapNeg : Prop :=
  ∀ (c : CoordF d L W) (F : Ω d L W × Ω d L W → ℂ), (∀ p, F (cltSwap d L W c p) = -F p) →
    ∫ p, F p ∂((PF d L W g).prod (PF d L W g)) = 0

theorem measurePreserving_cltSplit : MeasurePreservingCltSplit d L W g := by

theorem measurePreserving_cltSwap : MeasurePreservingCltSwap d L W g := by

theorem integral_eq_zero_of_cltSwap_neg : IntegralEqZeroOfCltSwapNeg d L W g := by

theorem cltTelescope : CltTelescope d L W := by

theorem cltTransfer {d : ℕ} (sz : Sizes d) (n : ℕ) (f : Ω d (sz.L n) (sz.W n) → ℂ)
    (hf : Measurable f) :
    ∫ ω, f (Sizes.slice sz n ω) ∂(Sizes.seqP sz) =
      ∫ ω, f ω ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by


$ instances (Checks section, compiled in the module build above)
section Checks

example : MeasurePreservingCltSplit 3 3 1 (1 / 2) := measurePreserving_cltSplit 3 3 1 (1 / 2)
example : MeasurePreservingCltSwap 3 3 1 (1 / 2) := measurePreserving_cltSwap 3 3 1 (1 / 2)
example : IntegralEqZeroOfCltSwapNeg 3 3 1 (1 / 2) :=
  integral_eq_zero_of_cltSwap_neg 3 3 1 (1 / 2)

/-- `cltTelescope` at the concrete enumeration `Fintype.equivFin`, for every `Φ`. -/
example (Φ : Ω 3 3 1 → ℂ) (ω ω' : Ω 3 3 1) :
    Φ ω - Φ ω' = ∑ k ∈ Finset.range (Fintype.card (CoordF 3 3 1)),
      (Φ (cltHyb 3 3 1 (Fintype.equivFin (CoordF 3 3 1)) k ω ω') -
        Φ (cltHyb 3 3 1 (Fintype.equivFin (CoordF 3 3 1)) (k + 1) ω ω')) :=
  cltTelescope 3 3 1 (Fintype.equivFin (CoordF 3 3 1)) Φ ω ω'

/-- The antisymmetric integrand `F p = p.1 c - p.2 c` against `PF ⊗ PF` at `(3, 3, 1, 1/2)`:
the hypothesis `F ∘ cltSwap c = -F` is discharged and the integral vanishes. -/
example (c : CoordF 3 3 1) :
    ∫ p, ((p.1 c : ℂ) - (p.2 c : ℂ)) ∂((PF 3 3 1 (1 / 2)).prod (PF 3 3 1 (1 / 2))) = 0 :=
  integral_eq_zero_of_cltSwap_neg 3 3 1 (1 / 2) c (fun p => (p.1 c : ℂ) - (p.2 c : ℂ))
    (fun p => by simp [cltSwap])

/-- `cltTransfer` at the merged `sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`) and the
measurable integrand `ω ↦ ω c₀`. -/
example (c₀ : CoordF 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0)) :
    ∫ ω, ((Sizes.slice SizesInst.sz0 0 ω c₀ : ℝ) : ℂ) ∂(Sizes.seqP SizesInst.sz0) =
      ∫ ω, (ω c₀ : ℂ) ∂(PF 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0) (SizesInst.sz0.lam 0)) :=
  cltTransfer SizesInst.sz0 0 (fun ω => (ω c₀ : ℂ))
    (Complex.measurable_ofReal.comp (measurable_pi_apply c₀))

end Checks
```

Narrative.  `RBM3D/Evolution/CltSwap.lean` (365 lines, commit `4a77a7f` on `t/T2140`) is the RBM2D file at `c9a24cf` with the preflight dictionary applied by script (`Coord L W ↦ CoordF d L W`, `Ω L W ↦ Ω d L W`, `P L W ↦ PF d L W g`, `L W ↦ d L W` in every ported name; `g` added only to the three `MeasurePreserving…`/`IntegralEq…` Props and their three theorems); the proofs are verbatim except `rw [P, …]` to `rw [PF, …]`, `gvar` to `gvarF d L W g`, and `measurePreserving_cltSwap d L W g c` in `integral_eq_zero_of_cltSwap_neg`.  `cltTransfer` takes `{d} (sz : Sizes d)`, law `PF d (sz.L n) (sz.W n) (sz.lam n)`.  No hypothesis on `g` and no new premise: the registry scan finds 74 premises with and without the module, `#assert_rbm_axioms` exit 0.  Private helpers are `cltSwap_cltHyb_ne`, `cltSwap_cltSplit_measurable`, `cltSwap_cltSplit_preimage_pi`, `cltSwap_cltSwap_involutive` (RBM2D names with prefix `cltSwap_`).  The RBM2D `Checks` section became the instances above at `(d, L, W, g) = (3, 3, 1, 1/2)` and `sz0`, `n = 0`; the two-term `L = W = 1` expansion was replaced by the applied `cltTelescope` (preflight P5).  The statement list printed above is the full ticket target list: 20 public declarations, all present (axiom lines).  The `Test/Axioms.lean` file was not touched (no registry lines).  `$HOME/mnt/RBM2D` does not exist; the source was read from `../RBM2D` (read-only) at `c9a24cf`.

## (c) Verified Mathlib names (all compile in this file)

`Measure.infinitePi`, `Measure.eq_infinitePi`, `Measure.infinitePi_pi`, `Measure.infinitePi_eq_pi`, `Measure.map_apply`, `Measure.prod_prod`, `measurePreserving_arrowProdEquivProdArrow`, `MeasurableEquiv.arrowProdEquivProdArrow`, `measurePreserving_pi`, `Measure.measurePreserving_swap`, `MeasurePreserving.integral_comp'`, `integral_neg`, `integral_map`, `Finset.sum_range_sub'`, `Finset.prod_filter_mul_prod_filter_not`, `Function.update_of_ne`, `Complex.measurable_ofReal`, `measurable_pi_apply`, `measurable_pi_iff`.

## (d) Open issues and paper-delta candidates

- T2140a: the Lean statements are the RBM2D ones up to the dictionary; the route (i.i.d. copy `H'`, coordinate exchange) is not in arXiv:2507.20274; `STCltIso` (`(eq:bound_isolated)`, `3_5:2245`, citing [DYYY25] (7.39)) is not proved by this file, which is only its first brick (the split, hybrids, telescope, exchange, transfer).  The sum runs over the `2 (W L)^{2d}` real coordinates, not over entries `i <= j`.
- No open issue; no stop condition fired.  S5-18 and S5-21 may start after merge.
