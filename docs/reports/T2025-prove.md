Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 04:56:56 UTC 2026

Targets (mathematics only): (T1) `KLuniquePin`: every `K` with `IsKLoop d L W g (mSigma E) (Ico 0 1) K` equals `KLK` on `Ico 0 1`
for all WF loops of length >= 1. (T2) `TwoLoopBounded` holds for every `IsKLoop` family on `Ico 0 1`; consequences `KTwoFormula`, `kThree`.
(T3) `KLK_rotate`: `KLK ⟨s::σ, b::a⟩ = KLK ⟨σ++[s], a++[b]⟩`; `KLK_translate`: `KLK ⟨σ, a.map (·+c)⟩ = KLK ⟨σ, a⟩` (WF, `t ∈ [0,1)`).

### (i) Exponent table

| item | value / form | constraint | slack |
|---|---|---|---|
| time window | `t ∈ [0,T₀]`, `T₀ = t < 1` (T = `Ico 0 1`) | `Icc 0 T₀ ⊆ Ico 0 1` for `isKLoop_unique` (merged, `Loop/Unique.lean:247`) | `T₀ < 1` strict: needed only for continuity on compact `[0,T₀]`; `K` has a derivative at every point of `[0,1)` (clause 1), so is continuous there |
| a priori 2-loop bound `R` | `R = max(C₁,C₂,0)`; `C_i` = sup over `[0,T₀]` of the finitely many coordinates `‖K_i s J‖`, `J` a WF 2-loop | needs finitely many 2-loops: `LoopVec d L 2 = Vector Bool 2 × Vector (Zd d L) 2` is finite (`2^2 · L^{2d}` loops); `K` and `KLK` both `IsKLoop` (`KLK_isKLoop`), so both are bounded | none needed; no smallness. At the instance below `KLK` has `R ≤ 0.2322` (script) |
| Grönwall constant | `C = W^d · (n(n-1)/2) · (L^d)^2 · 2R` (merged `eq_on_level`, uses `‖SB a b‖ ≤ 1`, needs `3 ≤ L`) | any finite real `C ≥ 0` works (`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`, no `C T₀ < 1`) | unlimited: finite is the only requirement (instance: `C = 9.4e5` at `n = 3`; irrelevant) |
| induction on length | `n ≥ 2`, `K 0 = MLoop` on both sides | length 1: `K t ⟨[s],[a]⟩ = m s` (clause 3) and `KLK` at length 1 `= m(σ.getD 0 false)` (`KLK_one`) | none |
| `m(σ)` | `mSigma E`, `‖m‖ = 1` for `|E| < 2`, `m(+) = mE E` | `|E| < 2` | at `E = 0.3`: `|m| = 1.0` (script) |
| spectral parameter | `ξ = t m(σ)m(σ')`, `‖ξ‖ = t` | `‖ξ‖ < 1` for `Θ_ξ = (1 - ξ S^(B))⁻¹`; `‖S^(B)‖ = 1` | `1 - t`; instance `t = 0.9`, slack `0.1` |
| `W^d` normalisation | `W^d` in `treeEqRhs` and `MLoop` (`(W^d)⁻¹^(n-1)`); `d = 3` | `1 ≤ W`; `W^d ≠ 0` | `W = 2`: `W^d = 8`; `W = 1` in the numeric check |
| `3 ≤ L` | hypothesis `hL` of merged `isKLoop_unique` and of the pin | `L ≥ 3` | `L = 5` (compiled instance), `L = 3` (numeric check) |
| `3 ≤ d` | not used: pin and merged `isKLoop_unique`, `KLK_isKLoop` carry no `hd` | none | the instances use `d = 3` |
| rotation `ρ` | `ρ(σ,a) = (σ.rotate 1, a.rotate 1)`; cuts of `ρI`: `(k,l)` with `l < n` ↔ cut `(k+1,l+1)` of `I` (rotated), `l = n` ↔ cut `(1,k+1)` of `I` (2D: `Cyclic_cutGlueL_rot_last`, `Cyclic_cutGlueR_rot_last`; the `cutL`/`cutR` roles and `(a,b)` swap there, to be re-checked in 3D) | bijection of the `n(n-1)/2` pairs; `SB` symmetric (`SB_isSymm`) makes the swap harmless; `MLoop` invariant (`∏ m(σ_i)`, "all `a_i` equal" are rotation-invariant) | exact bijection, no loss. Induction on length `n ≥ 2` with the Grönwall step at length `n` (no direct use of `isKLoop_unique`: rotated family satisfies the equation only through the lower lengths) |
| translation `τ_c` | `a ↦ a.map (· + c)` | `SB (a+c) (b+c) = SB a b` (`SB_apply_add_right`); `cutGlueL/R` commute with `map (·+c)` (insert `b+c`); `MLoop` invariant | exact: `K ∘ τ_c` is again `IsKLoop`, so `= KLK` by T1 (no extra induction) |
| 2D → 3D renaming | `Z2 L → Zd d L`, `W^2 → W^d`, `SB L → SB d L g`, `primRhs → treeEqRhs d L W g`, `primInit → MLoop d L W m`, `Kcal L W E → KLK d L g W E`, `mSig → mSigma`, `IsPrimitive → IsKLoop` | statements change only by these | no dimension-specific closed form is used by the ports (index type, `SB`, cuts only) |

Sources read: RBM2D `Loop/Unique.lean:254` (`Unique_two_loop_bound`), `:276` (`isPrimitive_eq_Kcal`); `Loop/Cyclic.lean:328`
(`Cyclic_rot_eq_on_level`), `:487` (`Cyclic_isPrimitive_rot`), `:569` (`Kcal_rotate`), `:594` (`Kcal_translate`), all at `c9a24cf`.
RBM2D HEAD is `9e0f275`; `git diff --stat c9a24cf HEAD` touches both files (26 ins / 39 del), so port from `c9a24cf` as the ticket says.

### (ii) One concrete nondegenerate instance

Compiled-instance data: `d = 3`, `L = 5` (`125` blocks), `W = 2` (`W^d = 8`), `g = 1/2`, `E = 0`, `t = 9/10`, `n = 3`, `m(+) = i`.
Hypotheses: `3 ≤ 5`, `1 ≤ 2`, `|0| < 2`, `0 ≤ 9/10 < 1`, `‖ξ‖ = 0.9 < 1`; `K = KLK` (the trivial case of T1, an `IsKLoop`
family by `KLK_isKLoop`); rotation/translation at `n = 3` loops. External hypotheses: none (every ingredient is a merged theorem).

Command: `python3 pf.py` (scratchpad, Python only, no Lean). Output:
```
hyps: 3<=L True 1<=W True |E|<2 True t in [0,1) True |m|= 1.0 |t m m'|= 0.9
N=L^d= 125 W^d= 8 SB row sums min/max 0.9999999999999999 1.0000000000000002 max SB entry 0.4
a priori 2-loop bound R = max |W^-d m m' Theta| = 0.23219078500910165 <= W^-d/(1-t) = 1.2500000000000002
n=2: #(k<l)=1, Gronwall constant C=W^d*pairs*(L^d)^2*2R = 3.125e+05 (finite; Gronwall needs no smallness)
n=3: #(k<l)=3, Gronwall constant C=W^d*pairs*(L^d)^2*2R = 9.375e+05 (finite; Gronwall needs no smallness)
n=4: #(k<l)=6, Gronwall constant C=W^d*pairs*(L^d)^2*2R = 1.875e+06 (finite; Gronwall needs no smallness)
```
Numeric check requested by the ticket, `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0.3`, `t = 0.6`: `𝒦` built from the tree sum
(`KLn`: `m_σ W^{-d(n-1)} Σ_{F ∈ TSP(n)} Γ_F`, laminar leaf/node parents, leaf edges `Θ^{(σ_v,σ_{v+1})}`, internal edges `Θ^{(σ_i,σ_j)} - 1`)
compared with its rotation and with the translation by `e_1 = (1,0,0)` on random `(σ,a)`.
Command: `python3 chk.py` (first lines of `ode.py` reuse it). Output:
```
row sum SB [1. 1.] |m| 1.0
n 3 |TSP| 1
 max|K-K∘rot|=5.463e-20  max|K-K∘shift_e1|=2.182e-18  sample |K|=1.277e-04
n 4 |TSP| 3
 max|K-K∘rot|=1.220e-19  max|K-K∘shift_e1|=1.759e-19  sample |K|=1.466e-05
n 5 |TSP| 11
 max|K-K∘rot|=6.627e-19  max|K-K∘shift_e1|=3.787e-20  sample |K|=1.713e-06
```
Consistency of the cut conventions (`cutGlueL/R` of `TreeRep.lean:84–91`) with the tree sum, finite difference `h = 1e-5` against
`W^d Σ_{k<l} K(cutL)·SB·K(cutR)` at the same data, command `python3 ode.py`:
```
n 3 dK/dt(FD)= (0.0009337522545041574-0.00419601630188848j) rhs= (0.0009337522529835236-0.004196016287031848j) |diff|=1.49e-11
n 4 dK/dt(FD)= (8.750880811414296e-05-3.158243693377427e-05j) rhs= (8.75088073700063e-05-3.158243678483423e-05j) |diff|=7.59e-13
```

### Verdicts
- T1 `KLK_unique`: PASS. Argument closed: both `K` and `KLK` are `IsKLoop` on `Ico 0 1`; bound `R` from continuity on `[0,t]` (finitely many 2-loops);
  `isKLoop_unique` with `T₀ = t`, `hT : Icc 0 t ⊆ Ico 0 1` gives equality for length >= 2; length 1 by clause 3 and `KLK_one`.
- T2 retirement (`KLretire_twoLoopBounded`, `KLretire_kTwoFormula`, `KLretire_kThree`): PASS (same continuity argument; premises of merged
  `kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop`; `KLretire_KLoopBound` is out of scope as the ticket says).
- T3 `KLK_rotate`, `KLK_translate`: PASS (statements true at `n = 3,4,5` numerically; rotation by Grönwall induction, translation by T1).

### (a′) Preflight corrections — Sat Oct  3 05:34:53 UTC 2026
One imprecision in the (a) table, row "rotation ρ"; no verdict changes. (a) calls both pieces of the cut of ρI "rotated" for l < n and leaves the roles of cutL/cutR "to be re-checked in 3D".
The compiled statements (RBM3D/Loop/KLUnique.lean:268, 285, 299, 315; statement text EQUAL to RBM2D's, table in (b)) read, with ρ = `KLUnique_rot`, I = ⟨s::ss, c::cs⟩, n = |cs|+1:
for l ≤ |cs|: `cutGlueL (ρI) k l b = ρ (cutGlueL I (k+1) (l+1) b)`, `cutGlueR (ρI) k l b = cutGlueR I (k+1) (l+1) b` (not rotated); for l = n: `cutGlueL (ρI) k n b = ρ (cutGlueR I 1 (k+1) b)`,
`cutGlueR (ρI) k n b = ρ (cutGlueL I 1 (k+1) b)`. The statements are index-only (no `d`, `L`, `SB`).

## (b) Script output (written Sat Oct  3 05:34:53 UTC 2026; first command of stage 1b: Sat Oct  3 04:57:51 UTC 2026, tool log)

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2025 && git log --oneline 3dc4f1c..t/T2025 && git diff --stat main...t/T2025 && git status --short   # status: (empty)
d1cc86e T2025: shifted-family lemma and a KLK_unique instance for a family other than KLK
2a9ac4b T2025: compiled instances of the three retirement lemmas
0f6c40b T2025: KL4+KL5 KLK_unique, retirement of TwoLoopBounded, KLK_rotate, KLK_translate
 RBM3D/Loop/KLUnique.lean | 767 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 767 insertions(+)
$ lake build RBM3D.Loop.KLUnique          # 0 warnings in the log
✔ [3243/3243] Built RBM3D.Loop.KLUnique (8.2s)
Build completed successfully (3243 jobs).
$ lake build   # whole library, twice: RBM3D.lean as committed, then with `import RBM3D.Loop.KLUnique` added after its last import line (temporary local edit, restored: `git status` empty)
info: RBM3D.lean:68:0: axiom audit: 1037 theorems, 398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3726 jobs).
info: RBM3D.lean:69:0: axiom audit: 1054 theorems, 398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
Build completed successfully (3727 jobs).
$ lake env lean axioms_check2.lean      # import RBM3D.Loop.KLUnique; #print axioms of the six targets
'RBM.Loop.KLK_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLretire_twoLoopBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLretire_kTwoFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLretire_kThree' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axioms_check3.lean | tail -1   # collectAxioms over all 40 declarations of the module (17 public; 23 private = the 21 `private` ones + 2 generated `eq_1`)
union of axioms used by all 40: [propext, Classical.choice, Quot.sound]
$ grep -n -E 'sorry|admit|native_decide|axiom' RBM3D/Loop/KLUnique.lean; echo "exit=$?"
exit=1
$ grep -n -E '3 ≤ d|\bhd\b' RBM3D/Loop/KLUnique.lean | cut -c1-60; grep -c -E '^private (theorem|def) ' RBM3D/Loop/KLUnique.lean
65:`d` is a parameter and `3 ≤ d` is not used (no dimension-
21
```
Targets, statements extracted from the file by script (from `theorem NAME` to the first `:=`):
```
theorem KLK_unique :   -- RBM3D/Loop/KLUnique.lean:117
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
      ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoop d L W g (mSigma E) (Set.Ico 0 1) K →
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length →
          K t I = KLK d L g W E t I := by
theorem KLK_rotate :   -- RBM3D/Loop/KLUnique.lean:640
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
        KLK d L g W E t ⟨s :: σ, b :: a⟩ = KLK d L g W E t ⟨σ ++ [s], a ++ [b]⟩ := by
theorem KLK_translate :   -- RBM3D/Loop/KLUnique.lean:222
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
        KLK d L g W E t ⟨I.σ, I.a.map (· + c)⟩ = KLK d L g W E t I := by
```
Pin and retirement checks:
```
$ python3 pincheck.py     # body of `def KLuniquePin` in docs/tickets/checks/T2025-check.lean vs 64b58eb:RBM3D/Probe/T2004Pins.lean vs the type text of `KLK_unique`
pin body (check file) == pin body (probe 64b58eb): True
KLK_unique type text == pin body (whitespace-normalised): True
$ lake env lean pinexample.lean   # the pin def copied from the check file, then `example : KLuniquePin := KLK_unique`
exit=0
$ python3 retirecheck.py  # blocks (docstring + theorem + proof) of the three lemmas: probe lines 915-971 vs RBM3D/Loop/KLUnique.lean
KLretire_twoLoopBounded : probe lines 917-933, file lines 77-93, verbatim equal: True
KLretire_kTwoFormula : probe lines 955-963, file lines 95-103, verbatim equal: True
KLretire_kThree : probe lines 965-970, file lines 105-110, verbatim equal: True
probe lines 915-971 contain "KLisKLoopPin": False
```
Ports (RBM2D at c9a24cf, read-only), `python3 portcheck.py`, then `python3 shiftblock.py | head -1`:
```
rename (RBM2D text -> RBM3D): Cyclic_>KLUnique_ (primRhs_>treeEqRhs_, primInit_>MLoop_, isPrimitive_rot>isKLoop_rot); primRhs L W>treeEqRhs d L W g;
  primInit L W>MLoop d L W; IsPrimitive L W>IsKLoop d L W g; Kcal L W E>KLK d L g W E; mSig>mSigma; Z2 L>Zd d L; SB L>SB d L g; (W : ℂ|ℝ) ^ 2>^ d; KLUnique_shift L>KLUnique_shift d L;
  Kcal_rotate, Kcal_translate, isPrimitive_eq_Kcal > KLK_rotate, KLK_translate, KLK_unique.  RBM2D: git show c9a24cf:RBM2D/Loop/{Cyclic,Unique}.lean
stmt = statement text up to the first ":=" compared token-wise; body = changed lines (+added/-removed) of the whole declaration after renaming
stmt EQUAL (14), 2D:line->3D:line(body +added/-removed):
  Cyclic_rot:135->KLUnique_rot:245(+0/-0); Cyclic_rot_mk_cons:137->KLUnique_rot_mk_cons:248(+0/-0); Cyclic_length_rot:142->KLUnique_length_rot:254(+0/-0);
  Cyclic_WF_rot:146->KLUnique_WF_rot:259(+2/-1); Cyclic_cutGlueL_rot_of_lt:153->KLUnique_cutGlueL_rot_of_lt:268(+0/-0);
  Cyclic_cutGlueR_rot_of_lt:169->KLUnique_cutGlueR_rot_of_lt:285(+0/-0); Cyclic_cutGlueL_rot_last:182->KLUnique_cutGlueL_rot_last:299(+0/-0);
  Cyclic_cutGlueR_rot_last:197->KLUnique_cutGlueR_rot_last:315(+0/-0); Cyclic_shift:519->KLUnique_shift:149(+0/-0);
  Cyclic_shift_WF:523->KLUnique_shift_WF:154(+0/-0); Cyclic_length_shift:528->KLUnique_length_shift:160(+0/-0);
  Cyclic_cutGlueL_shift:533->KLUnique_cutGlueL_shift:166(+2/-1); Cyclic_cutGlueR_shift:538->KLUnique_cutGlueR_shift:173(+2/-1);
  Cyclic_primInit_shift:555->KLUnique_MLoop_shift:195(+1/-1)
stmt DIFF  Cyclic_primRhs_split:221->KLUnique_treeEqRhs_split:341 body +2/-2  [(W : ℕ) => -]
stmt DIFF  Cyclic_primRhs_rot:236->KLUnique_treeEqRhs_rot:357 body +4/-4  [(W : ℕ) => -]
stmt DIFF  Cyclic_primInit_rot:319->KLUnique_MLoop_rot:441 body +2/-2  [(W : ℕ) => -]
stmt DIFF  Cyclic_rot_eq_on_level:328->KLUnique_rot_eq_on_level:452 body +29/-30  [(W : ℕ) => -]
stmt DIFF  Cyclic_isPrimitive_rot:487->KLUnique_isKLoop_rot:611 body +2/-2  [(W : ℕ) => -]
stmt DIFF  Cyclic_primRhs_shift:542->KLUnique_treeEqRhs_shift:180 body +4/-3  [- => (g : ℝ)]
stmt DIFF  Kcal_rotate:569->KLK_rotate:640 body +7/-8  [(L => (d L] [L], => L] (g E : ℝ),] [∀ E : ℝ, => -]
stmt DIFF  Kcal_translate:594->KLK_translate:222 body +8/-15  [(L => (d L] [L], => L] (g E : ℝ),] [∀ E : ℝ, => -]
stmt DIFF  isPrimitive_eq_Kcal:276->KLK_unique:117 body +12/-12  [(L => (d L] [L], => L] (g E : ℝ),] [∀ E : ℝ, => -]
2D lines 8 (RBM2D Cyclic.lean 609-616, inline block of Kcal_translate), 3D lines 8 (KLUnique.lean 207-214)
```
Residuals: `(W : ℕ) => -`: binder supplied by `variable (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ)` of section RotEq; `- => (g : ℝ)`: the new parameter; last three lines: theorem binders
`(d L W : ℕ) [NeZero L] (g E : ℝ)` as in `KLuniquePin` (RBM2D: `∀ E : ℝ` after `1 ≤ W`). `body` counts: line wrapping and the replacements of narrative item 5.

Compiled nonempty instances, all at d = 3, L = 5, W = 2, g = 1/2, E = 0, t = 9/10; `KLK_unique` (shifted family: `K ≠ KLK` as a function), `KLK_rotate`, `KLK_translate`; extracted by script:
```
theorem KLUniqueInst_unique_shifted :
    (fun r (J : LoopIdx (Zd 3 5)) =>
        KLK 3 5 (1 / 2) 2 0 r ⟨J.σ, J.a.map (· + (![1, 0, 0] : Zd 3 5))⟩) (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ :=
  KLK_unique 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (fun r (J : LoopIdx (Zd 3 5)) =>
      KLK 3 5 (1 / 2) 2 0 r ⟨J.σ, J.a.map (· + (![1, 0, 0] : Zd 3 5))⟩)
    (KLUnique_isKLoop_shift 3 5 2 (1 / 2) (mSigma 0) KLTreeDerivInst_isKLoop (![1, 0, 0] : Zd 3 5))
    (9 / 10) ⟨by norm_num, by norm_num⟩
    ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ rfl
    (by simp [LoopIdx.length])
theorem KLUniqueInst_rotate_three :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false, true], (0 : Zd 3 5) :: [1, 2]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false, true] ++ [true], [1, 2] ++ [(0 : Zd 3 5)]⟩ :=
  KLK_rotate 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ true 0 [false, true] [1, 2] rfl
theorem KLUniqueInst_translate_three :
    KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true],
          ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5)).map (· + (![1, 0, 0] : Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ :=
  KLK_translate 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ (![1, 0, 0] : Zd 3 5)
    ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ rfl
```
Also compiled, same shape (file lines): `KLUniqueInst_unique_one` 677 (length 1), `_unique_two` 685, `_unique_three` 693 (`K = KLK`, the ticket's trivial case), `_rotate_four` 726, `_retire_twoLoopBounded` 747,
`_retire_kTwoFormula` 752, `_retire_kThree` 759. Name-clash grep of the new public names (the branch worktree has no other occurrence; `main` as of the command):
```
git grep on main (976030d), RBM3D/ and RBM3D.lean: matching lines per new public name
KLK_unique=0; KLK_rotate=0; KLK_translate=0; KLretire_twoLoopBounded=0; KLretire_kTwoFormula=0; KLretire_kThree=0; KLUniqueInst_unique_one=0; KLUnique
Inst_unique_two=0; KLUniqueInst_unique_three=0; KLUniqueInst_rotate_three=0; KLUniqueInst_rotate_four=0; KLUniqueInst_translate_three=0; KLUniqueInst_
retire_twoLoopBounded=0; KLUniqueInst_retire_kTwoFormula=0; KLUniqueInst_retire_kThree=0; KLUniqueInst_unique_shifted=0; (substring) KLUnique=0
RBM2D HEAD 9e0f275
port source c9a24cf T2273: merge dead-code closure tool and report
 RBM2D/Loop/Cyclic.lean | 40 ++++++++++++++--------------------------
 RBM2D/Loop/Unique.lean | 25 ++++++++++++-------------
 2 files changed, 26 insertions(+), 39 deletions(-)
```

### Narrative
1. Result: all three targets (uniqueness, retirement, symmetries) and their instances are delivered, no obstruction. `RBM3D/Loop/KLUnique.lean` (767 lines, branch t/T2025, HEAD d1cc86e, 3 commits,
   only this file): `KLK_unique` (pin `KLuniquePin`), the retirement lemmas `KLretire_twoLoopBounded/kTwoFormula/kThree` (probe text), `KLK_rotate`, `KLK_translate`, ten compiled instances,
   21 private declarations (prefix `KLUnique_`). No hypothesis added, no signature changed; merged files, `RBM3D.lean` and `RBM3D/Test/Axioms.lean` untouched.
2. Uniqueness. `K` is `IsKLoop` on `Ico 0 1` by hypothesis, `KLK` by the merged `KLK_isKLoop`. Clause 1 gives a derivative of `s ↦ K s I` at every point of `[0,1)`, so each coordinate is
   continuous on the compact `[0,t]`, `t < 1`, and `LoopVec d L 2` is finite: the 2-loops are bounded (`KLretire_twoLoopBounded`; no smallness used). The merged `isKLoop_unique` with
   `T₀ = t`, `R = max R R'` gives equality at lengths ≥ 2; length 1 is clause 3 for both families.
3. Translation. `J ↦ K r (shift_c J)` is again `IsKLoop` for every family `K` (`KLUnique_isKLoop_shift`): the cuts of a shifted loop are the shift of the cuts with label `b - c` inserted; reindexing the
   `a`- and `b`-sums by `Equiv.addRight c` and `SB_apply_add_right` make `treeEqRhs` commute with the shift; `MLoop` is invariant; clause 3 holds at label `a + c`. `KLK_unique` identifies it with `KLK`.
4. Rotation. The rotated family does not satisfy `(pro_dyncalK)` termwise, so uniqueness is not used. Strong induction on the length `n ≥ 2`: `D = K∘ρ − K` at length `n` has
   `∂_t D = treeEqRhs (K t) (ρI) − treeEqRhs (K t) I`; `KLUnique_treeEqRhs_rot` expresses the first term through the four cut lemmas of (a′) (the `(a,b)` sums swapped by `sum_comm`, `SB_transpose`),
   `KLUnique_treeEqRhs_split` separates the `k = 1` terms. A term difference is `(X−X') s Y + X' s (Y−Y')`, at most `2R‖D‖` (`norm_mul_mul_sub_le`): a factor of length `n` forces the other to be
   a 2-loop, lengths `< n` agree by induction. `D 0 = 0` by rotation invariance of `MLoop`; Grönwall (`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`).
5. 3D versus 2D. `d` enters only through `Zd d L`, `SB d L g`, `W^d`; `3 ≤ d` is unused (grep). Changes beyond the renaming (diff of the declarations after renaming, tool log): (i) merged helpers replace
   RBM2D's re-ported copies: `LoopVec.toLoop/wf/length/exists_toLoop`, `LoopIdx.wf_cutGlueL/R`, `LoopIdx.two_le_length_cutGlueL/R`, `LoopIdx.length_cutGlueL/R_le`, `LoopIdx.length_cutGlueL/R_eq_two`,
   `norm_SB_apply_le`, `norm_mul_mul_sub_le`; (ii) the 2-loop bound is `KLretire_twoLoopBounded` (it gives `R ≥ 0`: no `max 0 _`), `isPrimitive_Kcal` is `KLK_isKLoop`, `Unique_isPrimitive_unique`
   is `isKLoop_unique`; (iii) in `KLUnique_treeEqRhs_rot`, `congr 1` is replaced by `refine congrArg₂ (· + ·) ?_ ?_` (with `congr 1` the first compile stopped with "(deterministic) timeout at
   `whnf`" at that line, tool log); (iv) the inline block `hK'` of `Kcal_translate` is the private lemma `KLUnique_isKLoop_shift` (script line above; the 3 changed line pairs only add the argument `d`);
   (v) the theorem binders (table); (vi) the other body differences are line wrapping (`KLUnique_` is longer than `Cyclic_`).
6. The retirement lemmas are the probe text (diff above: verbatim equal); none has a `KLisKLoopPin` hypothesis (script: 0 occurrences in probe lines 915-971), so nothing was discharged with `KLK_isKLoop`.
   `KLretire_KLoopBound` is not here (it needs `KLBoundAt`, KL11), as the ticket says.
7. Instances. The `IsKLoop` hypothesis is the merged `KLTreeDerivInst_isKLoop` (`K = KLK`, the trivial case the ticket allows) or its shift by `KLUnique_isKLoop_shift` (`KLUniqueInst_unique_shifted`: a family
   that is not `KLK` as a function). Rotation at `n = 3, 4`; translation by `e₁ = (1,0,0)` at `n = 3` with three distinct labels; `‖m(±)‖ = 1` by the merged `norm_mSigma`. No `N = 0`, empty index set
   or `False` premise.

## (c) Verified Mathlib/core names used (resolved by Lean in the module's environment; `name — module`); first the names found in no other RBM3D file, then those used through dot notation; none searched for absence
Finset.Ioc_self — Mathlib.Order.Interval.Finset.Basic
Finset.sum_Ioc_succ_top — Mathlib.Algebra.BigOperators.Intervals
List.drop_append_of_le_length — Init.Data.List.Nat.TakeDrop
List.drop_eq_nil_of_le — Init.Data.List.Basic
List.drop_left — Init.Data.List.TakeDrop
List.drop_succ_cons — Init.Data.List.Basic
List.exists_cons_of_length_pos — Init.Data.List.Lemmas
List.length_eq_one_iff — Init.Data.List.Lemmas
List.length_eq_zero_iff — Init.Data.List.Lemmas
List.length_rotate — Mathlib.Data.List.Rotate
List.map_drop — Init.Data.List.TakeDrop
List.map_rotate — Mathlib.Data.List.Rotate
List.map_take — Init.Data.List.TakeDrop
List.mem_rotate — Mathlib.Data.List.Rotate
List.rotate_cons_succ — Mathlib.Data.List.Rotate
List.rotate_perm — Mathlib.Data.List.Rotate
List.singleton_append — Init.Data.List.Lemmas
List.take_append_of_le_length — Init.Data.List.Nat.TakeDrop
List.take_of_length_le — Init.Data.List.TakeDrop
List.take_succ_cons — Init.Data.List.Basic
add_left_inj — Mathlib.Algebra.Group.Semigroup
and_imp — Init.SimpLemmas
continuousOn_pi — Mathlib.Topology.ContinuousOn
forall_apply_eq_imp_iff₂ — Init.PropLemmas
forall_exists_index — Init.PropLemmas
IsCompact.exists_bound_of_continuousOn — Mathlib.Analysis.Normed.Group.Bounded
CompactIccSpace.isCompact_Icc (exported as `isCompact_Icc`) — Mathlib.Topology.Order.Compact:51-55
List.Perm.prod_eq — Mathlib.Algebra.BigOperators.Group.List.Basic
HasDerivAt.continuousAt, HasDerivAt.hasDerivWithinAt (Mathlib.Analysis.Calculus.Deriv.Basic), ContinuousAt.continuousWithinAt (Mathlib.Topology.ContinuousOn)
Also used and already compiled in merged RBM3D files (61 names, same resolution):
Complex.norm_natCast, Equiv.coe_addRight, Equiv.sum_comp, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_insert, Finset.sum_Icc_succ_top,
Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_congr, Finset.sum_empty, Finset.sum_insert, Finset.sum_le_sum, Finset.sum_mul, Finset.sum_nbij',
Finset.sum_nonneg, Finset.sum_sub_distrib, List.append_assoc, List.cons_append, List.drop_zero, List.mem_map, List.nil_append, List.take_zero,
Nat.add_sub_cancel, Nat.cast_nonneg, Nat.strong_induction_on, Nat.sub_self, Set.Ico_subset_Icc_self, add_comm, add_le_add, add_mul, add_nonneg,
add_sub_cancel_right, add_zero, congrArg, congrArg₂, congrFun, eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right, funext, hasDerivAt_pi,
le_max_left, le_max_right, le_rfl, le_trans, lt_of_le_of_lt, mul_assoc, mul_comm, mul_le_mul, mul_le_mul_of_nonneg_left, mul_nonneg, norm_add_le,
norm_le_pi_norm, norm_mul, norm_nonneg, norm_pow, norm_sum_le, norm_zero, pi_norm_le_iff_of_nonneg, pow_nonneg, sub_eq_zero, sub_self

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none for a changed statement; all statements are on `t ∈ [0,1)` as the pins (accepted T2004d, DECISIONS.md:142). T2025a (note only, no Lean/paper difference): the paper uses
  rotation and translation invariance of 𝒦 without stating a lemma (cyclic convention `σ_{n+1} = σ_1`, paper/tex/3_5_Loop_Hierarchy.tex:114; translation invariance of `S^(B)`, `M`, `Θ`:
  paper/tex/7_8_light_weight.tex:1857, paper/tex/1_2_Intro_model_result.tex:1133); RBM2D proposed the same note (its T2004a-3, named in the header of RBM2D/Loop/Cyclic.lean at c9a24cf).
- Binder order of `KLK_rotate`, `KLK_translate`: `(g E : ℝ)` before the hypotheses, as in `KLuniquePin`/`KLisKLoopPin`; independent binders, same statement as RBM2D's.
- The module's environment contains the compiler-generated `RBM.Loop.treeEqRhs.congr_simp` (from `congr`/`simp` on the merged `treeEqRhs`); the root audit count went 1037 → 1054 theorems (16 written
  + this one). Seven other `congr_simp` lemmas of upstream declarations already exist in merged RBM3D modules (scan in the tool log).
- Registry: the `TwoLoopBounded`, `KTreeRep`, `KLoopBound` entries of `RBM3D/Test/Axioms.lean` are untouched (KL14); no new `Prop` hypothesis.
- Hub at merge: add `import RBM3D.Loop.KLUnique` after the last `import` line of `RBM3D.lean`. `main` moved during the work (976030d at the name-clash command); the branch is based on 3dc4f1c; only the new file differs.
- RBM2D HEAD 9e0f275 differs from c9a24cf in the two ported files only by docstrings, `#print axioms` lines and the private helper `Cyclic_sum_Ioc_shift` (defined once in c9a24cf, never used).
