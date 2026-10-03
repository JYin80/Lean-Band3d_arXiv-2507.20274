Auditor model: claude-opus-5-5

# T2057 audit (round 1) — S1-16 `RBM3D/Green/EntryDom.lean` — Sat Oct  3 14:32:17 UTC 2026

Branch `t/T2057` at `d8fe7c5`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2057-audit1` (detached).
Targets: `norm_avgErr_le` (RBM2D EntryBlock:594), `avg_bound_stochDom` (RBM2D EntryDom:696, `(GavLGEX)` 3_5:33);
public per portmap P.3: `blkCoef2`, `sum_blkCoef2`, `goodSet`.

## 1. Statement against the ticket's pin (RBM2D `c9a24cf` statement, renamed by ST1-COMMON item 2)

Script `sdiff.py`: RBM2D statement text (`git show c9a24cf:…`), renamed (`spectralM→mE`, `BlockIndex→Vtx d`,
`Z2→Zd d`, `d.L→sz.L`, `PerTimeDomAt (seqP sz) sz.size→sz.PrecPT`, `Sblk2 …→svar d … (sz.lam n)`, `Kstab2 κ L→Kstab3 d Λ κ`),
token-diffed against the RBM3D statement:
```
$ python3 sdiff.py <scratch>/T2057 RBM3D/Green/EntryDom.lean
== theorem norm_avgErr_le tokens 242 267
  insert RBM2D:  | RBM3D: ( hd : 3 ≤ d )
  insert RBM2D:  | RBM3D: ) {g Λ : ℝ} ( hg : 0 < g ) ( hgΛ : g ≤ Λ
== theorem avg_bound_stochDom tokens 512 507
  insert RBM2D:  | RBM3D: 𝔡
  insert RBM2D:  | RBM3D: ( hd : 3 ≤ d )
  replace RBM2D: h𝔠 | RBM3D: hA
  replace RBM2D: 0 < | RBM3D: sz.Admissible
  replace RBM2D: ) ( hsz : RBM.Ind.SizeTendsto d ) ( hbw : Bandwidth d 𝔠 | RBM3D: 𝔡
```
Every residual difference is one the ticket prescribes:
- `Kstab2 κ L` → `Kstab3 d Λ κ` with the hypotheses of the merged `stable_svar_bulk_vtx` (`Stability.lean:320`:
  `(hd : 3 ≤ d) (hL : 3 ≤ L) … (hg : 0 < g) (hgΛ : g ≤ Λ)`). The profile `svar d L W g` is the merged
  `((W:ℝ)^d)⁻¹ * SBR d L g x.1 y.1` (`Gauss/Model.lean:63`); at sequence level `g = sz.lam n`, the model's coupling.
- `h𝔠, hsz, hbw` → `hA : sz.Admissible 𝔠 𝔡` (`Defs/Sizes.lean:177`: `0 < 𝔠 ∧ 0 < 𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 ∧ WO 𝔡`),
  as DECISIONS §22 / D39. Parameter order `κ 𝔠 𝔡` fixed before the sequences; conclusion `GavLDetSeq sz E t Ψ`
  is the merged pin (`Green/Pins.lean:179`), hypothesis `LoopDetSeq sz E t Ψ` the merged pin (`Pins.lean:172`).
- Conclusion of `norm_avgErr_le` unchanged: `‖avgErr d L W E u M true a‖ ≤ B' + Kstab3 d Λ κ * (A + B)`.
- Public definitions: `blkCoef2 d L W a k := if k.1 = a then ((W : ℝ) ^ d)⁻¹ else 0` (RBM2D `((W:ℝ)⁻¹)^2`; `W² → W^d`);
  `sum_blkCoef2 : ∑ k, blkCoef2 d L W a k = 1`; `goodSet` = `{ω | ∀ i j : Idx d …, llErrMat … i j ≤ ((sz.W n:ℕ):ℝ)^(-c)}`,
  RBM2D `goodSet` (EntryDom:154) after renaming.
- D40 (one orientation): `offSq_le_gexRHS_blk` keeps `81 * Φ ^ 2 * gexRHS d L W E u M q.1 p.1` (RBM2D EntryBlock:406
  same right side); `Pins.lean` untouched (section 4). The stop condition of the ticket is not triggered.

Against the paper: (GavLGEX) (3_5:33–36) assumes `(initialGT2)`; the target, as pinned by the ticket (RBM2D port), is the
step "`≺ max|𝓛|` then `≺ Ψ²`" with the IBP and fluctuation-averaging inputs `hIBP`, `hFArow`, `hFAblk` as hypotheses
(each `≺ maxLoopPM`). It matches the ticket's target exactly; it is a conditional step of the proof of `lem_GbEXP`
(paper: "proven as Lemma 4.1 in [YY_25] … dimension-independent", 3_5:38), not `(GavLGEX)` itself (see observation O1).

Verdicts on statement: `norm_avgErr_le` PASS; `avg_bound_stochDom` PASS; `blkCoef2`, `sum_blkCoef2`, `goodSet` PASS.

## 2. Vacuity, hidden hypotheses, cycles

- No `structure`/`class` declared in the file (`grep -nE "^(structure|class)"`: none). Hypotheses are explicit signature
  arguments; `Admissible`, `PrecPT`, `LoopDetSeq`, `GavLDetSeq` are merged `def`s (Prop), not structure fields.
- Imports: `RBM3D.Green.{EntryCore,Stability,Pins}`, `RBM3D.Induction.PerTimeCalc`, all merged on `main`
  (T2029 890a89f, T2046 ea63565, T2028 64bdfd3, T2045 5d1e6b1); no `import RBM3D`; no cycle.
- `hIBP`, `hFArow`, `hFAblk` are stochastic inputs owed by later ST-1 tickets (report (d)); the ticket keeps them as
  hypotheses (RBM2D form). `hLoop` is the merged pin `LoopDetSeq`. Joint satisfiability: section 3 (t ≡ 0 instance).

## 3. Compiled nonempty instances (same file, built in section 4)

```
$ grep -nE "^example" RBM3D/Green/EntryDom.lean
1345:example (a : Zd 3 4) :                                         -- norm_avgErr_le
1370:example (a : Zd 3 4) : ‖avgErr 3 4 32 0 (1 / 2) 0 true a‖ = 1 ∧   -- nondegeneracy of the above
1426:example : GavLDetSeq sz0 (fun _ => 0) (fun _ => 0)              -- avg_bound_stochDom, t ≡ 0
1487:example : GijOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
1494:example : GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
1503:example {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) Ψ) :   -- avg_bound_stochDom, t ≡ 1/2
1549:example (p q : Vtx 3 4 2) :
1561:example (p : Vtx 3 4 2) :
1580:example : GijOmegaSeq sz0 (fun _ => 0) (fun _ => 0) 1 ∧ GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 0) 1 := by
```
- `norm_avgErr_le` (:1345): `d = 3, L = 4, W = 32, g = 1/64 ≤ Λ = 10, E = 0, κ = 1, u = 1/2, M = 0, x ≡ -i/2,
  A = 0, B = B' = 3/2`; all of `hd hL hg hgΛ hκ hE hu0 hu1` by `norm_num`, `hIBP/hFA/hFA'` proved in the `·` blocks.
  Nondegenerate: (:1370) proves `‖avgErr …‖ = 1` (`entryDom_inst_avgErr : avgErr … = Complex.I`) and right side `≥ 3`.
  Window `u = 1/2 ∈ [0,1)`, `N = (4·32)^3`, nonempty index. PASS.
- `avg_bound_stochDom` (:1426): `sz0`, `κ = 1, 𝔠 = 1/6, 𝔡 = 1/10`, `sz0_admissible`, `E ≡ 0, t ≡ 0, x ≡ 0`,
  `Ψ_n = √(W_n^{-3})` (= `W^{-d/2}`, the paper's lower endpoint of `Ψ_t`, 3_5:27); `hIBP, hFArow, hFAblk` proved
  (`perTimeDomAt_of_nonpos`), `hLoop` proved (`entryDom_loopDet_zero`). Every hypothesis discharged.
  (:1503) the same theorem at `t ≡ 1/2` with `hIBP, hFArow, hFAblk` (section variables) and `hLoop` (pin) as hypotheses,
  every deterministic hypothesis discharged. PASS (see observation O2).

## 4. Build, axioms, hygiene, scope

```
$ git diff --name-only main...t/T2057
RBM3D/Green/EntryDom.lean
$ git diff main...t/T2057 -- RBM3D/Test/Axioms.lean RBM3D/Green/Pins.lean RBM3D/Green/Stability.lean | wc -l
       0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|implemented_by|extern|unsafe|opaque" RBM3D/Green/EntryDom.lean
48:set_option linter.style.longLine false
$ lake build RBM3D.Green.EntryDom      (audit worktree; no EntryDom olean in the copied cache)
✔ [3320/3320] Built RBM3D.Green.EntryDom (9.9s)
Build completed successfully (3320 jobs).
$ lake env lean ax.lean     (import RBM3D.Green.EntryDom; #print axioms of the 36 public names)
exit=0
35 lines "[propext, Classical.choice, Quot.sound]"; remaining: 'RBM.Green.OffPair' depends on axioms: [propext]
'RBM.Green.avg_bound_stochDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.blkCoef2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.goodSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.norm_avgErr_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.sum_blkCoef2' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D && lake env lean reg.lean   (import RBM3D; import RBM3D.Green.EntryDom; #assert_rbm_axioms)
Build completed successfully (3751 jobs).
axiom audit: 1708 theorems, 640 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 47 (borrowed 2, owed 34, structural 11).
exit=0
$ for n in $(cat pub.txt); do git grep -w -l "$n" main -- RBM3D RBM3D.lean; done   (36 public names, current main 6ef5d49)
(no output)
```
Main moved since the branch base `6b2494e` (`RBM3D/Graph/LWVocab.lean` added, `RBM3D/Test/Axioms.lean` +4/-1); the branch
touches neither and no public name clashes with current `main`. The hub's full build at merge is the final check.

## 5. Paper deltas

| Difference | Coverage |
|---|---|
| `Admissible 𝔠 𝔡` in place of `SizeTendsto`, `Bandwidth` | D39 (signed) |
| one-orientation `gexRHS … [q] [p]` | D40 (signed); proved, no switch |
| `zdistInf ≤ 1` neighbourhoods in `gexRHS`-facing bounds | D18 (cited in report (d)) |
| `Ψ` window of `GavLDetSeq` | D41 (signed, pin-level) |
| loop-floor constant `2 → 4 maxLoopPM`, `4320 → 8640` (RBM2D→RBM3D, non-target lemmas) | candidate T2057a |
| `|E| ≤ 2-κ` vs `<` in `GbEXPHypV3`; `Vtx` block lemmas vs `Idx` pins | candidate T2057b |
| `Kstab3 d Λ κ` (no `L`) in place of `Kstab2 κ L` | ticket-prescribed, same form `≤ B' + K(A+B)`; no paper statement (paper has `≺`) |

All Lean/paper statement differences of the targets are covered.

## Observations (no RETURN)

- O1. `avg_bound_stochDom` is a conditional step: `(GavLGEX)` of the paper follows only once `hIBP`, `hFArow`, `hFAblk`
  (each `≺ maxLoopPM`) are proved from `(initialGT2)`. The report (d) lists them as open inputs "not added to any pin";
  the dispatcher should make sure a later ST-1 ticket (S1-17/S1-30 assembly) owns them, since `GbEXPHypV3` consumes
  `GavLDetSeq`.
- O2. In the fully discharged instance of `avg_bound_stochDom` (:1426, `t ≡ 0`) the left sides vanish (`H = 0`), so it shows
  joint satisfiability only; the `t ≡ 1/2` instance (:1503) carries the stochastic inputs as hypotheses. This is the form
  the ticket and CLAUDE.md §4 allow; the deterministic `norm_avgErr_le` instance is nontrivial (`‖avgErr‖ = 1`).
- O3. Report (b) says "35 declarations … others: OffPair depends on axioms: [propext]" — reproduced above.

## Verdict

- `norm_avgErr_le`: **PASS**
- `avg_bound_stochDom`: **PASS**
- `blkCoef2`, `sum_blkCoef2`, `goodSet`: **PASS**

Ticket T2057: **PASS**. No dispatcher sign-off needed (O1 is a tracking note).
