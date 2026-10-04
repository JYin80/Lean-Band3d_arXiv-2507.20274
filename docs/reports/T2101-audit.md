Auditor model: claude-opus-5-5

# T2101 audit (round 1): S1-24 `Green/CondDom.lean`. Verdict: PASS

Audit time: `date -u` = Sun Oct  4 03:21:03 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2101-audit1`,
detached at `t/T2101` = `72a80c4` (merge-base with main `5bef95c`). RBM2D sources: `git show c9a24cf:RBM2D/Green/{CondDom,CondStable,EntryGauss}.lean`.

## 1. Statements against RBM2D `c9a24cf` (ST1-COMMON item 6), auditor's own script

`sdiff.py`: extract every public header up to `:=` in both texts, rename the 3D side back
(`(sz : Sizes d)`→`(d : Sizes)`, `Idx d`→`Idx`, `svarF d`→`svar`, `sz`→`d`, `zt`→`spectralZ`, `mE`→`spectralM`), compare.
```
$ python3 sdiff.py        (2D text lines shortened by the auditor to the differing fragments)
DIFF CondDom:217 -> 3D:209 norm_condExpDiag_sub_le_offdiag
  2D: ... (hG : GaussIBP d) (hE : |E| < 2) ... (svar (d.L n) (d.W n) i k : ℂ) ... ≤ A + svar (d.L n) (d.W n) i i * Adiag
  3D: ...                   (hE : |E| < 2) ... (svar (d.L n) (d.W n) (d.lam n) i k : ℂ) ... ≤ A + svar (d.L n) (d.W n) (d.lam n) i i * Adiag
DIFF CondDom:298 -> 3D:295 W_le_self
  2D: theorem W_le_self (d : Sizes) (n : ℕ) : d.W n ≤ d.size n
  3D: theorem W_le_self (d : Sizes) (hd : 1 ≤ d) (n : ℕ) : d.W n ≤ d.size n
DIFF CondStable:123 -> 3D:401 perTimeDomAt_of_le_left_on
  2D: theorem perTimeDomAt_of_le_left_on {d : Sizes} {V : ℕ → Type*} ...
  3D: theorem perTimeDomAt_of_le_left_on {d : Sizes} (hd : 1 ≤ d) {V : ℕ → Type*} ...   (rest identical)
DIFF EntryGauss:55 -> 3D:753 gijOmegaSeq
  2D: (d : Sizes) {κ 𝔠 δ : ℝ} (hκ : 0 < κ) (h𝔠 : 0 < 𝔠) (_hδ : 0 < δ) (hsz : SizeTendsto d) (hbw : Bandwidth d 𝔠) (E t : ℕ → ℝ) ...
  3D: (d : Sizes) {κ 𝔠 𝔡 δ : ℝ} (hκ : 0 < κ) (_hδ : 0 < δ) (hA : d.Admissible 𝔠 𝔡) (E t : ℕ → ℝ) ...   (rest identical)
DIFF EntryGauss:67 -> 3D:765 giiOmegaSeq       same as gijOmegaSeq, plus (hd : 3 ≤ d)
DIFF EntryGauss:81 -> 3D:780 gijSeq_of_asGMc   same as gijOmegaSeq
DIFF EntryGauss:93 -> 3D:792 giiSeq_of_asGMc   same as gijOmegaSeq, plus (hd : 3 ≤ d)
public 2D decls: 24  identical after renaming: 17
```
The 7 differences:
- `norm_condExpDiag_sub_le_offdiag`: `hG` was dropped (T2091 O1), and `svar` gained `lam`. This is renaming rule R4 (`svarF d L W g`).
- `W_le_self`, `perTimeDomAt_of_le_left_on`: these add `hd : 1 ≤ d`. The extra hypothesis is necessary: at `d = 0`, `size = (W L)^0 = 1 < W = 2` (prove report (a) rows 1–2). It is harmless for `d ≥ 3`.
- EntryGauss (4): `hsz`, `hbw`, `h𝔠` become `hA : sz.Admissible 𝔠 𝔡`. The merged definition gives `Admissible 𝔠 𝔡 := 0 < 𝔠 ∧ 0 < 𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 ∧ WO 𝔡` (`Defs/Sizes.lean:177`), so `h𝔠` is kept inside `hA`. The order is that of the pin `GbEXPHypV3` (`Green/Pins.lean:210`):
  `sz.Admissible 𝔠 𝔡 → ∀ E t, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t → ∀ c > 0, GijOmegaSeq ∧ GiiOmegaSeq ∧ (AsGMcSeq → GijSeq ∧ GiiSeq ∧ …)`.
  The four conclusions are exactly the first four components of the pin, under the same premises. The added `hd : 3 ≤ d` (gii only) is the hypothesis of the merged `diag_bound_stochDom` (`Green/EntryDom.lean:997`) and `diag_bound_stochDom_of_asGMc` (`:1128`).
- No public declaration was dropped: all 24 RBM2D public names are present, with no "MISSING" lines. The 3D file has 24 non-private top-level declarations (grep count 23 plus the `@[simp]` lemma).

**Key targets**, from the file:
- `perTimeDomAt_of_moment` (3D:314) is identical to CondDom:316. It does not depend on `d`, since `size : ℕ → ℕ` is abstract.
- `norm_greenDiagCentered_sub_minor_le` (3D:703) is identical to CondStable:410 after renaming: same `hE`, `hu1`, `δ' ≤ 1/2`, `GoodEvent` hypothesis, factor 2 and `i ≠ k`.
- `giiSeq_of_asGMc` (3D:792) is identical to EntryGauss:93, apart from the `Admissible`/`hd` change above.

**Import cut `Path/Scales`.** The ticket asks for a private copy of the helper with `d`-dimensional scales. The auditor checked what the three RBM2D files actually use:
```
$ grep -cwE "scaleM|ellT|tailT|ellStar|Meta|ellz|etaT_div_etaT" *.2d.lean   -> 0 / 0 / 0
$ grep -ow "etaT[A-Za-z_]*" *.2d.lean | sort | uniq -c   -> etaT, etaT_le_of_le (in-file), etaT_pos only
RBM2D Path/Scales.lean:38  def etaT (E u : ℝ) : ℝ := (1 - u) * (spectralM E).im
RBM3D Loop/GLoop.lean:75   noncomputable def etaT : ℝ := (1 - t) * (mE E).im ;  :83 theorem etaT_pos
```
The only helpers used are `etaT` and `etaT_pos`. They do not depend on the dimension, and the merged definitions are the same as RBM2D's. Because of that, no private copy is needed and no `d`-dimensional scale occurs. This is recorded as observation O1.

**DECISIONS §29 (time windows).** The time hypotheses are `t < 1` / `u < 1`, `u ≤ t`, and `0 ≤ t` in `norm_condExpDiag_sub_le_offdiag`. The prove report (b.8) gives `grep -cE "lemT|ilambda|ℓ|W \^ K|L \^ d|UniformWeight|BoundedWeight"` = 0, which the auditor confirmed in the file header and statements. **Statements: PASS.**

## 2. Vacuity, hidden hypotheses, cycles

- No new `structure` or `class` is introduced. The only new definitions are `condRowReal` and `rowSlice` (non-Prop). The `Sizes` fields are the merged ones.
- External or conditional hypotheses:
  - `hsize : Tendsto size atTop atTop` in `perTimeDomAt_of_moment`, `_condRow_of_envelope` and `_sub_self` is the same as in RBM2D. A compiled negative statement, `condDom_no_hsize` (3D:1027), shows it cannot be dropped: at the constant sizes `L=3, W=2`, `size ≡ 216`, `MomentDomAt` holds and `¬ PerTimeDomAt`.
  - `hAs : AsGMcSeq` (the paper's (asGMc), `3_5:16`) appears only in the two conditional adapters. This is the antecedent of the pin `GbEXPHypV3` itself. The limit check is in prove (a) SC: `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}`, `c = 1/40 ≤ d/2`, and `W_n^{-(d/2-c)}` takes the values `6.0e-3`, `3.6e-5`, → 0.
- Dependencies are all merged imports (`Green.{IBP,Pins,EntryDom,LDE,IBPPoly}`, `Induction.PerTimeCalc`, `Gauss.DominationAt`, `Loop.GLoop`). The module imports neither `RBM3D` nor any ST-2…6 file, and has no cycle.
- `gijOmegaSeq` and `giiOmegaSeq` are unconditional: their only premises are the deterministic premises of `GbEXPHypV3`.

## 3. Compiled nonempty instances (section `Checks`, 3D:805–1456)

| target | instance | data | hypotheses discharged |
|---|---|---|---|
| `perTimeDomAt_of_moment` | `condDom_inst_moment` (1009) | `sz0`; `Y = 1_{ω_c<0}` (non-constant); `Φ ≡ 1` | `hsize` = `tendsto_sz0_size`; `hΦ`, `hint`, `MomentDomAt` (`C = 1`) are proved |
| `norm_greenDiagCentered_sub_minor_le` | `condStable_inst_minor_nd` (1397) and `example` (1422) at `sz0`, `i=(0,0,0)`, `k=(1,0,0)` | `E = 0`, `u = 1/4`; explicit `ω` with `H_ik = H_ki` coordinates `1/2` | `GoodEvent … (1/2)` is proved from the explicit resolvent (`condStable_goodEvent_nd`, 1340); the instance also proves `0 < ‖G_ki‖‖G_ik‖` (`G_ki = G_ik = 2/5`), so it is not the degenerate `u = 0` case of RBM2D |
| `giiSeq_of_asGMc` (and `gijSeq_of_asGMc`) | `EntryGauss_chk_adapters` (1446) | `sz0`, `STflowE z0`, `tInst`, `κ = δ = 1/20`, `c = 1/40` | every deterministic hypothesis comes from `Instance.premises` or `norm_num`; only `hAs : AsGMcSeq` (the paper's (asGMc), the pin's antecedent) remains |
| `gijOmegaSeq`, `giiOmegaSeq` | `EntryGauss_chk_gij/_gii` (1434/1440) | same data | all discharged |

- The other public declarations are each used in `Checks` (prove report b.6 coverage list; the line numbers match the file).
- `sz0`, slice 0, has `L=4`, `W=32` and `N=2097152`. The data is nondegenerate: there is no `N=0`, no empty index, no collapsed window, no `False` premise, and no astronomically large witness that is load-bearing.
- **Instances: PASS.**

## 4. Build, axioms, hygiene, diff

```
$ date -u; lake build RBM3D.Green.CondDom      (audit worktree; error/summary lines only)
Sun Oct  4 03:19:05 UTC 2026
Build completed successfully (3336 jobs).      (warnings only, all in merged LDEQuad/LDEQuadMom; no `error`)
$ lake build RBM3D | grep -E "^error|Build completed"
Build completed successfully (3845 jobs).
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Green/CondDom.lean
0
$ git diff --name-only main...HEAD
RBM3D/Green/CondDom.lean
```
The scratch file `scratchpad/T2101/ax.lean` contains `import RBM3D`, `import RBM3D.Green.CondDom`, `#print axioms …` and `#assert_rbm_axioms`. Running `lake env lean` on it gives:
```
'RBM.Green.perTimeDomAt_of_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.norm_greenDiagCentered_sub_minor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.giiSeq_of_asGMc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.gijSeq_of_asGMc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.gijOmegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.giiOmegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.perTimeDomAt_condRow_of_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.W_le_self' depends on axioms: [propext, Quot.sound]
axiom audit: 3175 theorems, 1177 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 83 (borrowed 2, owed 66, structural 15).
registry: 5 borrowed + 101 owed + 38 structural; ...
exit=0
```
- The only file touched is the sole writable file `RBM3D/Green/CondDom.lean`. `Test/Axioms.lean` is unchanged, which is correct because no new `Prop` predicate is defined and the premise scan count is unchanged (83).
- No frozen signature was touched.
- **Build/axioms: PASS.**

## 5. Paper deltas

| Lean/paper or RBM2D difference | coverage |
|---|---|
| `hd : 1 ≤ d` on `W_le_self`, `perTimeDomAt_of_le_left_on` | `T2101a` (proposed, prove (d)) |
| `hd : 3 ≤ d` on `giiOmegaSeq`, `giiSeq_of_asGMc` | `T2101b` (proposed) |
| `Admissible 𝔠 𝔡` (with `(eq:WO)`) in place of `SizeTendsto`, `Bandwidth`, `0 < 𝔠` | D39 (`docs/paper-deltas.md:311`, cited) |
| `hG : GaussIBP` dropped | T2091 audit O1 (cited); this weakens the hypotheses only |
| `hsize` in place of `N → ∞` | carried over from RBM2D `T2156a` / D20 (cited in prove (b) narrative 6) |

The paper does not state these lemmas separately: `lem_GbEXP` is cited from `[YY_25]` at `3_5:37`. The pin `GbEXPHypV3` governs the statements. **Paper deltas: PASS.**

## Observations (no RETURN)

- **O1.** The ticket asks for a `private` copy of the `Path/Scales` helper with `d`-dimensional scales. The three source files use only `etaT` and `etaT_pos`, which are dimension-free and already merged (`Loop/GLoop.lean:75,83`), so no copy was made. This is correct by the grep in §1; the dispatcher may wish to correct the portmap note.
- **O2.** The registry lists `RBM.Green.GijOmegaSeq` as **owed** ("S1-24 `gijOmegaSeq`"). This ticket proves `gijOmegaSeq` and `giiOmegaSeq` unconditionally, for the Gaussian flow under `Admissible`. The dispatcher may reclassify that registry line, which is not writable by this ticket beyond appends.
- **O3.** RBM2D HEAD `9e0f275` differs from `c9a24cf` in the three files. The port follows `c9a24cf`, as ST1-COMMON item 1 requires.

## Verdict

| target | verdict |
|---|---|
| `perTimeDomAt_of_moment` | PASS |
| `norm_greenDiagCentered_sub_minor_le` | PASS |
| `giiSeq_of_asGMc` (conditional adapter under `AsGMcSeq`, as pinned in `GbEXPHypV3`) | PASS |
| the other 21 public ports | PASS |

Overall: **PASS**. No dispatcher sign-off is needed.
