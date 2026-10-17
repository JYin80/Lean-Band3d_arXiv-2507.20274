Auditor model: claude-opus-5-5

# T2535 audit, round 1 (Sat Oct 17 02:23:27 UTC 2026)

Branch `t/T2535` at `a84e21da`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2535-audit1`. Report-only: target `docs/PAPER-VS-LEAN.md`;
no endpoint theorem, so the instance/build items reduce to "main and the final forms are described correctly".
**Verdict: PASS** (the ticket's Acceptance holds; every §2 item checked matches the final PDF/TeX and the Lean source).

## 1. Scope, length, vocabulary

```
$ git rev-parse --short main ; git merge-base main t/T2535 | cut -c1-8      -> d44d29d1 / d44d29d1
$ git diff --name-only main...t/T2535
docs/PAPER-VS-LEAN.md
$ wc -l docs/PAPER-VS-LEAN.md      ->  695
$ grep -nEi 'T2[0-9]{3}|DECISIONS|paper-delta|ticket|prover|auditor|dispatcher|\bgate\b|pinned|\bowed\b' docs/PAPER-VS-LEAN.md ; echo "grep exit $?"
grep exit 1
```

## 2. Every Lean name exists on main (independent extraction, audit worktree)

The name list was extracted by my own script (`names.py`: every backticked span outside code fences; `RBM.`-prefixed tokens, and other
identifier-like tokens), plus 61 short names from the text added by hand (`Mband`, `Gn`, `BAm`, `PropThetaQ`, `Xentry`, `lemT`, …).

```
$ wc -l rbm_chk.txt oth_chk.txt   -> 135, 130   (pending names and bare namespaces removed)
$ lake env lean chk_rbm.lean   (import RBM3D; open …; 135 × #check @RBM.…)  -> exit 0 ; grep -c error: 0
$ lake env lean chk_oth.lean   (130 × #check @<name>)                      -> exit 1, 8 errors, all dot notation:
  Unknown identifier `sz.Admissible` | `sz.L` | `sz.W` | `sz.lam` | `sz.seqHBA` | `sz.seqXmat` | `sz.size` | `sz.withLam`
$ lake env lean chk_dot.lean
@Sizes.Admissible : {d : ℕ} → Sizes d → ℝ → ℝ → Prop
@Sizes.L … @Sizes.W … @Sizes.lam … @Sizes.seqHBA … @Sizes.seqXmat … @Sizes.size … @Sizes.withLam : {d : ℕ} → Sizes d → (ℕ → ℝ) → Sizes d
@Sizes.three_le_L : ∀ {d : ℕ} (self : Sizes d) (n : ℕ), 3 ≤ self.L n
chk_dot.lean:12:8: error(lean.unknownIdentifier): Unknown identifier `RBM.BA.baStep5III_holds_any`
chk_dot.lean:13:8: error(lean.unknownIdentifier): Unknown identifier `RBM.BA.baThm27L_all`
```

Every name exists on main except the two names the ticket allows (`baStep5III_holds_any`, `baThm27L_all`), which the prove report lists as
pending T2533/T2534.

## 3. Quoted Lean statements: copied verbatim

Script `quotes.py`: splits every ```` ```lean ```` block of the document into declarations and checks each one as a contiguous substring of
some `RBM3D/**/*.lean` file or of `docs/tickets/checks/T2534-check.lean`.

```
$ python3 -I quotes.py
OK   size <- RBM3D/Defs/Sizes.lean          … (61 lines OK: WO … locDomain, svarF, BASelf BAm BArho BAbulk, IsRegular32 IsFreeConv32
     UNL32, IsOrthoEigenbasis … UNUnivDilAt, calB … QDiff, BAprof … BAThm27L)
MISS Sizes            (lines present but not contiguous)
MISS Thm27            first non-matching line: ['def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d']
MISS RBM.Endpoints.Thm27_of_L32 / RBM.BA.baThm27L_all / final_shape
verbatim 61 not verbatim 5
```

The five: `Sizes` is the source structure with its three field docstrings removed (`RBM3D/Defs/Sizes.lean:138-146`; the document says
"without docstrings"). The four others are the final forms, checked against the T2534 check file:

```
$ diff <(Thm27New body, renamed) <(grep '^def Thm27 ' docs/PAPER-VS-LEAN.md) && echo …   -> Thm27: identical to Thm27New
$ diff <(FinalShapeNew body, Thm27New→Thm27) <(final_shape block) && echo …            -> final_shape: type identical to FinalShapeNew
$ grep -o 'RBM.Univ.UNL32 → ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d' T2534-check.lean PAPER-VS-LEAN.md  -> both files (baThm27L_all)
$ grep -o 'RBM.Univ.UNL32 → RBM.Endpoints.T2534Check.Thm27New := RBM.Endpoints.Thm27_of_L32' T2534-check.lean  -> found
```

On main `Thm27 := RBM.BA.BAThm27L 3` (`Main/FinalShape.lean:36`); the document describes the final form, as the ticket requires.

## 4. Axioms and build (main = merge base; no Lean file changed)

```
$ lake build RBM3D.Main.FinalShape  -> Build completed successfully (4427 jobs).
$ lake env lean ax.lean   (#print axioms of the 9 names in the document's §1 block)   -> exit 0
'RBM.Endpoints.decol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
  … (8 more lines, all [propext, Classical.choice, Quot.sound]) …
$ diff <(lake env lean ax.lean) <(grep "depends on axioms" docs/PAPER-VS-LEAN.md) && echo …   -> doc axiom block identical
$ sed -n 9,17p RBM3D/Test/Axioms.lean ; grep -n 'def interfaceAxioms' RBM3D/Test/Axioms.lean
  `#assert_rbm_axioms` … fails unless each [axiom] is either one of propext, Classical.choice, Quot.sound, or an interface axiom
67:def interfaceAxioms : List Name := []
```

So "fails the build unless every declaration in `RBM` depends only on the three axioms" (document §1) is true on main; the registry scan
that main's command also performs is not described, matching the public form the ticket asks for. `tail -1 RBM3D.lean` is `#assert_rbm_axioms`.

## 5. Page, equation and theorem references (PDF)

`pdftotext` is absent; text per page extracted with `pypdf` (106 pages). §1/§4 references (`pdfrefs.py`, whitespace removed):

```
p7 OK (2.1);(2.2);(2.4);(2.5);N=(W | p8 OK Theorem2.1(Delocalization);Fixanydimensiond;(2.9);(2.10);(2.12);(2.13);
Theorem2.2(Localsemicirclelaw);(2.14);(2.15) | p9 OK Theorem2.3(…);(2.18);(2.19);Theorem2.4(Bulkuniversality);(2.20);
Theorem2.5(Quantumdiffusion);(2.22) | p10 OK (2.24);(2.25);ProofofTheorem2.4;[28,Theorem2.6] | p11 OK (2.29)…(2.32);
Theorem2.7(Mainresultsfortheblock;Fixanydimensiond | p12 OK (2.34);normalizedbythelocaldensities | p45 OK (iii) |
p72 OK centeredatthedeterministic | p104 [28] | p105 [59],[64] | p106 [69]          not found: 0
$ bibliography: [28] S. Dubova, K. Yang, H.-T. Yau, J. Yin … arXiv:2503.07606 ; [59] S. K. Truong, F. Yang, J. Yin … arXiv:2503.11382 ;
  [64] C. Xu, F. Yang, H.-T. Yau, J. Yin … Annals of Probabil… ; [69] H.-T. Yau, J. Yin … arXiv:2501.01718   (as in the header)
$ grep -il 'landon\|sosoe\|1609.09011' pp/*.txt paper/final/tex/*.tex   -> (no output): the PDF cites [LANDON20191137] only through [28], as the header says
```

All 198 equation/theorem references of §§1-5 were cross-checked against `paper-labels.tsv` (`refs.py`); every flagged pair was read by
hand and is a line carrying two references (e.g. "Lemma 3.6 in [69] … p. 15" refers to Lemma 2.15 on p. 15; Step 5 (iii) at p. 45 is the
case list of Section 5, p. 45). One loose citation, see Observation 3.

## 6. §2 differences against the TeX of the final paper and the Lean source (read: `1_2_Intro_model_result.tex:250-346, 357-530, 600-690`)

| Item | Paper (TeX) | Lean (source) | Finding |
|---|---|---|---|
| 2.1 sequences | "provided N sufficiently large", (2.9),(2.10) | `Admissible` = `0<𝔠 ∧ 0<𝔡 ∧ SizeTendsto ∧ Bandwidth ∧ WO` | matches |
| 2.2 blocks, `L≥3` | `[a]=∏⟦(a(i)−1)W+1,a(i)W⟧`; no bound on `L`; `S` "symmetric doubly stochastic" | `three_le_L`; `card_nbhd (hL : 3 ≤ L) : … = 2*d`; `sum_sbKernelR (hL : 3 ≤ L)` | shift `x↦x−1, a↦a−1` checked; `L=2`: `d` neighbours, row sum `≠1`: correct |
| 2.3 labels | `λ_1≤…≤λ_N`, normalized `ψ_k` | `∃ μ ψ, IsOrthoEigenbasis …` in the bad events | Lean bad event ⊇ paper's: Lean stronger, correct |
| 2.4 failure prob. | `P(…) ≥ 1−N^{−D}` | `seqP {bad} ≤ ofReal (N^{−D})` | correct (outer-measure remark valid) |
| 2.5 uniformity | `⋂_z` inside `P`; (2.24),(2.25) "for each z" | `∃ z, locDomain …` inside; `eventually_forall_of_sections` (`Endpoints.lean:423`) | matches |
| 2.6 QUE | (2.17)-(2.19), `0<c<ε₀∧(𝔡/5)`, `W^{−(2ε₀)∧(2𝔡/5)+2c+τ}`, "any subset A" | `queWindow`,`queBound`, `A.Nonempty` | `A=∅`: event `0≥0`; reading justified |
| 2.7 distance | `|x−y|=‖[x−y]_{WL}‖_∞` in (2.14) | `distB = W·zdistInf(a−b)` of block labels `STblk` | `|K−Wk|<W` per coordinate ⇒ ratio in `[1/2,2]`, factor `≤2^{d−2}`: checked |
| 2.8 `m,Θ` | (2.6)-(2.8),(2.21) | `msc`, `Theta = Ring.inverse(1−ξ•SB)`; `Theta_mul_of_three_le (hL) (hξ : ‖ξ‖<1)`, `norm_msc_lt_one` | matches |
| 2.9 correlation fns | `p^{(n)}_H`, GUE, `O∈C_c^∞` | `kPoint` = `N^k/descFactorial N k · Σ_{Fin k ↪ ι}`; `IsTestFun`; `gueVar` | identity `∫O p^{(k)}(E+α/N) = N^k(N−k)!/N! 𝔼Σ…` checked |
| 2.10 bulk | (2.34) `ρ_N(E)=π^{−1}Im m(E+i0_+)` | `BAbulk`,`BArho`; `BArho_rate_of_bulk … ≤ 2*η/(π^3*κ^2)`; `BAbulk_iff_exists` | signatures match the text |
| 2.11 BA universality | display with `ρ_N(E)^{−n}`, `ρ_sc(E')^{−n}`, `E'∈(−2,2)` | `BAEnd_BUnivL`, `UNUnivDilAt`, bulk `∀ᶠ n` | matches; Lean stronger in `E∈B_κ` |
| 2.12 BA Θ, M | (2.35), `M^{(+,−)}_{ab}=|M^{(B)}_{ab}|²`, `S^{(B)}=I` | `BAMss = M(σ₁)_{ba} M(σ₂)_{ab}` (`MFixedPoint.lean:511`), `PropThetaQ Q 1 = Ring.inverse(1−Q)` | matches |

§1 instances (checked in source): `BandTerminal.lean:118-153` (UNL32 only or none), `BUnivHolds.lean:239,249` (six leaves as hypotheses),
`MAPins.lean:215-226` (five conjuncts of `BAThm27L 3` at `S0`, `clsκ 4`, `(fp 4 _).E`, `S0_bulk`, `bump`), `FinalShape.lean:84-112` (ten
conjuncts, `UNL32` only). `S0 = clsS 4 … UNPins_hg_3_10` (`L=4`, `W=(2(n+1))^5`, constant `g₀`), as described. `BUniv_of_L32 := unBUniv_of_L32
= bUniv_holds unNormBandRow h32 unMLOut_holds unLocAvgBand_holds unQueBand_holds gueSchurTail` (`BandTerminal.lean:95-100`): the document's
"applies `bUniv_holds` to the proved leaves" is correct, and its use of `BUniv_of_L32` (not `bUniv_holds`) in the table is the accurate
reading of the ticket's table (`bUniv_holds` has six hypotheses, `BUnivHolds.lean:227-229`).

§4: `UNL32` quoted verbatim (§3 above); `UNStep1Good'` (`PinsDens.lean:73-84`) has `g = N^{−1+τs/4}`, `G = N^{−min(τs/4,(1−τs)/3)}`,
`τs ≤ 𝔠*𝔡`, `|ρ'−ρ n| ≤ N^{−(3τs/8)}`, as §4.4 states. The v4 facts of §4.2 (prefactors, complex Hermitian Remark) agree with
`../RBM2D/docs/PAPER-VS-LEAN.md:312-322` (read-only grep); v4 itself is not in either repository (prove report (b)).
§5 spot checks: `decol_of_locSC` uses `min (τ / 2) (1 / 2)` (`Main/FixedZ.lean:793-799`); `QUE_of_QDiff` uses `locDomain κ (𝔠 * (𝔡 - ε₀))`
(`Main/QUEFromQDiff.lean:93`); `envConst = 16 (k+3)^4 N^4 (1+η^{-1})^{k+4}` (`Path/OneStep.lean:78-79`); `KLK_isKLoop` on `Set.Ico 0 1`.

## 7. Paper-delta coverage

The document is itself the public list of Lean/paper differences (§2: twelve items). The prove report (d) proposes `T2535a` (`L ≥ 3`) and
`T2535b` (`(2.19)` for `A ≠ ∅`) and maps the other items to existing entries. No uncovered statement difference found.

## Observations (no RETURN)

1. **Final forms pending T2534.** Lines 94-99, 107-109, 143-145 describe `baThm27L_all`, `baStep5III_holds_any`, `.2 3 le_rfl` and the
   `d = 4` example, none of which compiles on main yet; recheck after T2534 merges (prove report (d) 1).
2. **`d = 4` instance and the BA bulk** (prove report (d) 3, re-derived): `BAm` is a solution of (2.32) or `0`, and `BAm_norm_le_one`
   gives `‖m‖ ≤ 1`, so `BArho ≤ 1/π < 1/2`. If T2534's `d = 4` example keeps `κ = 1/2`, its four BA conjuncts run over an empty bulk.
   The document's sentence (line 144) does not claim a nonempty bulk, but it appears under "The statements are not vacuous". This is
   T2534's instance and needs the dispatcher's attention there, not a change to this document now.
3. Line 451 cites "(2.52) (Definition 2.14, p. 14)": Definition 2.14 is on p. 14, but (2.52) is on p. 15 (`paper-labels.tsv`). Cosmetic.
4. §2.12 does not say that `Ring.inverse (1 − M^{(σ₁,σ₂)})` is the true inverse on `BAendDom` (as §2.8 does for the band model).
   Optional wording.

**Result.** T2535: PASS; no dispatcher sign-off needed for this ticket; Observations 1-2 are recheck items for T2534's merge.
