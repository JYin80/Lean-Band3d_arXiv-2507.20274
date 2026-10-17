Verdict: PASS, no stop rule fired.  The gap is a coverage gap, not a mathematical one: the census finds 236 dimension-3 tokens in the five files that change (151 class (a) index-only, 85 class (b) constant/exponent, every (b) with a merged general-`d` twin or a one-line side step) and **0 class (c)**; an in-place generalization of Good, Good2, Walk, Walk2, Targets compiled in scratch to `baStep5III_holds_any : ∀ d, 3 ≤ d → STStep5IIIgL d …` with standard axioms (272 head + 16 instance-tail edited lines); probe 409 lines (cap 500), 31/31 theorems standard axioms, no merged file changed; D4: in place, ≈ 300 landing lines (≈ 520 at ×1.74) against ≈ 3,330 in new files; rows R1 (the five files) and R2 (assembly + the `d = 4` instance, ≈ 110); the `d = 4` instance costs 78 lines (< 150: full instance); BAD-C3: three "no"; BA-D forecast after this gate: 3 tickets (3–4).

# T2524 design: BA case (iii) of Step 5 at every `d ≥ 3` (stage BA-D, row 1)
Written Sat Oct 17 00:55:29 UTC 2026 (`date -u`) by the stage-1b prover (claude-sonnet-5-5) on branch `t/T2524` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2524`, base `main` afab243f; `main` is now 99651343 = T2524 Amend 1, answered in sections 1, 4, 5, 7).  Probe `RBM3D/Probe/T2524Pins.lean`, 409 lines, never merged; section (a) of `docs/reports/T2524-prove.md` is not edited.  `X:N` = `RBM3D/X.lean:N` at afab243f (T2523 has not merged: `git diff --stat main...t/T2523` is `DeadDecls.lean` only); `:N` alone = a probe line.  The scripts are in the scratchpad `T2524/` (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d6ebe5cd-b9c4-4c2a-9b3c-fa912982a931/scratchpad/T2524`, as T2513); every block below is their output, verbatim.

## 0. Script output
```
$ git log --oneline main..t/T2524   # cwd = RBM3D-wt/T2524
67f99efb T2524: probe, T2524_Step5IIIAny as a plain implication
a37fb256 T2524: probe, exact-type pin of baStep5III_holds_any, producer of Thm27, one-line d = 3 recoveries
751fd963 T2524: probe, self-contained d = 4 sequence (no instance helper that T2523 deletes) and the d = 4 Thm27 instance
ca161de2 T2524: probe docstring (long lines)
c15e9934 T2524: probe (BA-D design gate: general-d texts, chain to BAThm27L d, d = 3 recovery, (b) inequalities, d = 4 sequence, final texts)
$ bash probe_check.sh
lines:      409
lake env lean RBM3D/Probe/T2524Pins.lean: exit=0, output lines=0
lake build RBM3D.Probe.T2524Pins: exit=0, last line: Build completed successfully (4443 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs: 8, theorems: 31, examples: 9
#print axioms, every probe theorem: 31 of 31 with exactly [propext, Classical.choice, Quot.sound]; other lines: 0
main: 0 files; this tree outside the probe: 0
other t/* branches: 0 files
--- git diff --stat main...t/T2524 -- RBM3D
 RBM3D/Probe/T2524Pins.lean | 409 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 409 insertions(+)
$ lake env lean docs/tickets/checks/T2524-check.lean; echo exit=$?   # acceptance: the check compiles
exit=0 (output lines 33, lines containing 'error': 0)
$ lake env lean scan_probe.lean   # RBM.Audit.scanPremises (registry rule of Test/Axioms.lean), names starting RBM.BA.T2524_
scanPremises over the environment with the probe: 128 premises in all; probe premises: [RBM.BA.T2524_WalkAt]
$ zsh pipeline.sh   # scratch, not committed: 13 lexical rules, then 77 hand-edited head lines and 16 tail call sites in the five files; compile in import order
Good: exit=0 output_lines=       0 error_lines=0
Good2: exit=0 output_lines=       0 error_lines=0
Walk: exit=0 output_lines=       0 error_lines=0
Walk2: exit=0 output_lines=       0 error_lines=0
Targets: exit=0 output_lines=       0 error_lines=0
$ lake env lean exp_axioms.lean   # import T2524G.Targets: signatures and #print axioms of the generalized chain
#print axioms (9 theorems): 9 of 9 with exactly [propext, Classical.choice, Quot.sound]
RBM3D.Main.BandTerminal: closure 567 modules; U5 files in it: none
RBM3D.Main.BUnivHolds: closure 284 modules; U5 files in it: none
RBM3D.Endpoints: closure 87 modules; U5 files in it: none
```

## 1. D1: the census
Classes (lexical, so the audit can re-grep): **(a)** `Sizes 3`, `Zd 3`, `Idx 3` and the dimension argument `3` of `zdistInf`, `KLloopOf`, `tailTD`, `Step5IIIWalk_Ctot` (hand edits M also: `baKbound_holds 3 le_rfl` → `d hd`); **(b)** `((sz.W n : ℕ) : ℝ) ^ 3`, `((sz.L n : ℕ) : ℝ) ^ 3`, `((3 : ℕ) : ℝ)`, `(6 * 3)`, `2 * 3`; **(c)** none.  Head = the file before its instance section; tail = the instance section (data at `d = 3`: `SizesInst.sz0`, `FlowPinsInst.*`, `Step1SetupInst.*`).  The 22 `Fin 3` are 3-loops (`σ : Fin 3 → Bool`, `Edet:316, :529-538`, `Good:359-404`, `Good2:104`, `Walk:194`), not the lattice index `Fin d`.
```
$ grep -c 'Sizes 3\|Zd 3' RBM3D/BA/Step5III*.lean; python3 census_summary.py   # grep lines (the ticket's 116; 117 occurrences), tokens by class in head and tail
file     lines  grep Sizes 3|Zd 3 instance from | (a) head (b) head | tail (a)+(b)
Edet      1493                  9          1385 |        0        0 |           22
Edet2     1277                  6          1176 |        0        0 |           23
Good       704                 17           605 |       23       28 |            7
Good2      198                  1            82 |        1        5 |            2
Ker        709                  2           650 |        0        0 |            4
Ker2       471                  8           366 |        0        0 |           16
Walk      1799                 21          1521 |       15       16 |           51
Walk2     1067                 52           987 |      112       36 |            0
Targets    112                  0            61 |        0        0 |            0
total     7830                116               |      151       85 |          125
$ python3 census_annot.py   # one row per declaration of the five files that change, head only; R_a, R_b = tokens, M = hand-edited lines (experiment of section 3)
file:lines       declaration                  Ra  Rb   M cl.  change (general-d value; merged twin)
Good:66-66       (file header)                 0   0   1 (a)  new line `variable {d : ℕ}`
Good:393-408     BAStep5IIIGood               12   8   0 (b)  `Zd/zdistInf 3→d`; `W^3→W^d`; `θ(3(Cd+1))→θ(d(Cd+1))`; twin `baStep5III_matrix_level d` (Good:349)
Good:414-415     BAStep5IIIGoodThm             1   0   2 (a)  `Sizes 3→Sizes d`; `(d : ℕ)` binder, `3 ≤ d →` in front
Good:434-600     baStep5IIIGoodThm_holds      10  20   8 (b)  `W^3→W^d` ((ii)-(vi), `ρ ≤ W^d`, `τ⁻¹ ≤ W^d`, `1 ≤ lam²W^d`); `-(D+3) ≤ -D`: `0 ≤ d`; calls `baKbound_holds d hd`, `baEMn2ExpHK hd`, `baKsol_one d`, `Step5IIIGood_Wpow d`
Good2:45-45      (file header)                 0   0   1 (a)  new line `variable {d : ℕ}`
Good2:52-75      baStep5III_scalar_flow        1   5   3 (b)  floor `(L^d W^{6d})² ≤ W^D`; `1 ≤ lam²W^d`; `3 ≤ 3`→`3 ≤ d`; binders `(d) (hd)`
Walk:87-88       baStep5IIIGood_bundle         1   0   1 (a)  `Sizes 3→Sizes d`, `{d}`
Walk:102-110     Step5IIIWalk_good_of_flow     1   0   2 (a)  `{d} (hd)`; call `baStep5IIIGoodThm_holds d hd`
Walk:253-298     baStep5III_walkLevel          3   9   6 (b)  floor; `Dst-2·3→Dst-2d`; `W^{-3}→W^{-d}` (`hWdl`); `pfStep5Grid_level d`
Walk:1317-1345   Step5IIIWalk_pertime         10   7   4 (b)  `W^d`, `lossE2wG d`, `d(Cd+1)`, floor, `(d := d) hd`
Walk2:57-57      (file header)                 0   0   1 (a)  new line `variable {d : ℕ}`
Walk2:73-74      BAStep5IIIWalk                0   0   2 (a)  `(d : ℕ)`; `STIngR5gL 3→d`
Walk2:79-80      BAStep5IIIFromWalk            1   0   2 (a)  `(d : ℕ)`; `3 ≤ d →` in front; `Sizes d`
Walk2:90-108     Step5IIIWalk2_Num             1   3   0 (b)  `hA : 1 ≤ lam²W^d`, `hRm : 64 (W^d)^7 (..)`
Walk2:116-348    Step5IIIWalk2_path           50  14   3 (b)  `W^d`; `√(2 Cq d) log W` (`d log W`); `Ctot d`; `mart_real d`; `KLloopOf d`
Walk2:365-581    Step5IIIWalk2_fixedN         33   3   1 (a)  index only (`Zd/Idx/zdistInf`, `Ctot d`)
Walk2:582-734    baStep5III_walk_at           14  13   9 (b)  `D₀=2/𝔠+12d`, `D*=max(D,D₀)+2d+1`; floor (`pfStep5_fl`); `1 ≤ d` (omega); calls with `d hd`
Walk2:763-767    baStep5IIIWalk_holds          0   0   2 (a)  `(d : ℕ)`; `walk_at d hd`
Walk2:782-829    Step5IIIWalk2_PT              6   1   5 (a)  `(hd)`; `pfStep5Grid_level d`; `1 ≤ d` (omega); `W^{-d}`
Walk2:866-941    Step5IIIWalk2_lift            7   2  11 (b)  `#V=4L^{2d}`, `N=(WL)^d`, `L^d ≤ N`; `Cv = 3` is the exponent of `N³`, not `d`
Walk2:977-981    baStep5IIIFromWalk_holds      0   0   4 (a)  `(d : ℕ)`; `intro hd`; `PT/lift hd`
Targets:42-48    baPfStep5_of_walk             0   0   4 (a)  `(d : ℕ)`; `STPfStep5gL d`; `fromWalk hd`
Targets:52-54    baPfStep5_holds               0   0   3 (a)  `(d : ℕ)`
Targets:57-59    baStep5III_holds              0   0   2 (a)  `baStep5III_holds_any (d) (hd)` new; `baStep5III_holds` = one line at `3`
per file (rows / R_a / R_b / M): Good 4/23/28/11; Good2 2/1/5/4; Walk 4/15/16/13; Walk2 11/112/36/40; Targets 3/0/0/9; total 24/151/85/77
```
Edet, Edet2, Ker, Ker2 have no class (a)/(b) token in their heads (their statements are at `(d : ℕ) (hd : 3 ≤ d)`, constants `S_d = (1+1536 d^4)^d` (`Edet:549-551`), `lossE2wG d`: general already); their `Zd 3`/`Idx 3` are in instance tails.  Tails: `python3 inst_census.py`: 1,006 lines in nine files, `SizesInst.sz0` 699 uses, `FlowPinsInst.*` 276, `Step1SetupInst.*` 3, uses in a head: 0.  Steps that evaluate the dimension: `by norm_num` for `-(D+3) ≤ -D` (`Good:531`), `hd1 : 1 ≤ 3 := by norm_num` (`Walk2:595, :877`), `(by norm_num : 1 ≤ 3)` (`Walk2:799`), and the `le_rfl : 3 ≤ 3` arguments of calls (`Good:453, :467`, `Good2:75`, `Walk:1345`, `Walk2:597-598, :661-665`); `decide` at `Edet:535-538` (`finRotate 3`), `Walk:1387` (`Icc 3 2`), `Ker2:83-84` (`Fin 2`) is loop order: d-free.  d-free `3`s that stay (`dfree2.py`, 492 numerals in the nine heads after the edit: `3 ≤ d` guards 38, loop order 24, `ℓ* = (log W)^{3/2}`, `(log W)^{3/4}`, `J^{3/2}` 191, powers `τ^3` (4-loop), `N^3`, `ρ^3`, `J^3` 96, numeric constants `3(w-v)`, `3ε₀`, `hN3 : 3 ≤ N` 143).

**Class (b): the general-`d` value, the merged twin, "deleted by T2523" (BAD-C2 (a); `deadcheck.py`) and the probe lemma.**
| item | `d = 3` text | general `d` | twin | deleted by T2523 | probe |
|---|---|---|---|---|---|
| b1 volume | `W^3`, `1 ≤ lam²W^3` | `W^d`; `1 ≤ lam²W^d`, `(W^d)⁻¹ ≤ lam²` | `Sizes.lam_sq_mul_pow_ge` Defs/Sizes:193 | no | `T2524_vol` :163, `T2524_tau_le` :176 (`τ ≤ W^{-2𝔡}`) |
| b2 level | `Dst - 2·3` | `Dst - 2d` | `pfStep5Grid_level` PfStep5Grid:149 | no | `T2524_level` :191 |
| b3 floor | `(L^3 W^{6·3})² ≤ W^D` | `(L^d W^{6d})² ≤ W^{Dst-2d}`, needs `Dst-2d ≥ 2/𝔠+12d` | `pfStep5_fl` PfStep5:1984 | no | `T2524_floor` :198 |
| b4 constants | `D₀ = 2/𝔠 + 12·3`, `D* = max(D,D₀)+2·3+1` | `2/𝔠 + 12d`, `max(D,D₀)+2d+1` | `pfStep5_walk` PfStep5:2129 (lines 2148-2155; band, general `d`); `walk_at` Walk2:606-614 | no | `omega`, `linarith` |
| b5 `d log W` | `√(2 Cq·3) log W` | `√(2 Cq d) log W` | `Step5IIIWalk_Ctot d` Walk:988 | no | `T2524_logbound` :204 |
| b6 loss | `θ(3(Cd+1))` | `θ(d(Cd+1))` | `Step5IIIGood_Wpow d` Good:430 | no | `T2524_Wpow` :235 |
| b7 lift count | `#V = 4L^{2·3} ≤ N³` | `4L^{2d} ≤ N³` (`N³`: `Cv = 3`, not `d`) | `Sizes.card_Idx` Defs/Sizes:160 | no | `T2524_card_le` :215 |
| b8 side steps | `-(D+3) ≤ -D`, `1 ≤ 3` | `0 ≤ d`, `1 ≤ d` | | | `Nat.cast_nonneg d`, `omega` |

**Column "deleted by T2523"** (BAD-C2 (a); names outside the U5 chain that D1, D2, D4 and the probe cite; method: the tool of `t/T2523` with roots core + G1-G4 run on afab243f, `lake env lean DeadDecls.lean`, exit 0, `dead/dead_T2523roots.out`; `python3 deadcheck.py <names>`):
```
  lam_sq_mul_pow_ge Defs/Sizes:193 no                            | pfStep5Grid_level Induction/PfStep5Grid:149 no
  pfStep5_fl Induction/PfStep5:1984 no                           | pfStep5_Rm Induction/PfStep5:2014 no
  pfStep5_sizes Induction/PfStep5:375 no                         | baKbound_holds BA/KBound:245 no
  baEMn2ExpHK BA/EMn2BA:637 no                                   | baKsol_one BA/KInduct:77 no
  baGridRepNAt2_holds BA/GridRepTailBA:1237 no                   | baFlow_premises BA/NetLiftBA:65 no
  baStep5CasesGen_flowFacts BA/SEforLnBA:152 no                  | ST_step5_caseIII_of_pfgL Chain/Step5CasesGen:406 no
  STIngR5gL Chain/Step5Gen:191 no                                | STStep5IIIgL Chain/Step5Gen:228 no
  STPfStep5gL Chain/Step5Gen:252 no                              | lossE2wG Path/LemDecCalEwG:74 no
  baThm27L_any BA/UNBUniv:286 no                                 | baThm27L_three BA/UNBUniv:281 no
  baThm27L_of_ML BA/UNBUniv:271 no                               | BAThm27L BA/MAPins:126 no
  Thm27 Main/FinalShape:36 no                                    | Thm27_of_L32 Main/FinalShape:39 no
  final_shape Main/FinalShape:43 no                              | sz0 Defs/Sizes:260 no
  sz0_L_le_W Defs/Sizes:272 no                                   | zSeq BA/FlowPins:1181 yes
  flow_sz0 BA/FlowPins:1214 yes                                  | half_lt_t0 BA/FlowPins:1254 yes
  sz0_lam_pos BA/FlowPins:1184 yes                               | Step5IIIGood_sz0_lam_le BA/Step5IIIGood:614 yes
  Step5IIIGood_reg_sz0 BA/Step5IIIGood:623 yes
```
`python3 deadcheck_probe.py` over every identifier of the probe: names deleted by T2523: none.  T2523 deletes 22 unreached declarations in the five files (207 lines; `dead_u5.py`, `dead_tail.py`: 20 in tails, 2 in heads) and every `example` outside FinalShape/BandTerminal/MAPins/BUnivHolds: none of the 272 head edit lines lies in a deleted declaration, and each of the 16 tail edit lines lies in an `example` or an unreached declaration, so the tail edits do not arise after T2523.

**(c) substantive: none.**  No inequality of the `d = 3` argument fails for `d > 3`: every hand edit (77 lines) is a binder or an argument (`(d : ℕ)`, `hd`, `variable {d : ℕ}`, `d hd` at call sites) or one of b1-b8; the only exponent that looks like the dimension and is not is `Cv = 3` in the lift (b7), which stays `3`.  Nothing is open: no Fable check is needed.

## 2. D2: the general-`d` texts (probe :47-157; final names in place)
```
$ python3 extract_targets.py   # statements extracted from the probe
:50   def T2524_BAStep5IIIGood {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ) : Prop :=
:51     ∀ τ' D₁ θ : ℝ, 0 < τ' → 0 < D₁ → 0 < θ → θ < 1 → ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, ∃ G : Set sz.SeqΩ,
:52       Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
      ... (13 more lines, to :65)
:68   def T2524_BAStep5IIIGoodThm (d : ℕ) : Prop :=
:69     3 ≤ d → ∀ (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → BAFlow sz κ ε 𝔠 𝔡 z →
:70       ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
:71         STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
:72         STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
:73           ∀ D : ℝ, 0 < D → T2524_BAStep5IIIGood sz z s t D Cd
:76   def T2524_BAStep5IIIWalk (d : ℕ) : Prop :=
:77     STIngR5gL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
:78       (fun sz z s t => BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t)
:81   def T2524_BAStep5IIIFromWalk (d : ℕ) : Prop :=
:82     3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z →
:83       ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
:84         BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t → STPfConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t
:89   theorem T2524_baPfStep5_of_walk (d : ℕ) :
:90       T2524_BAStep5IIIWalk d → T2524_BAStep5IIIFromWalk d →
:91         STPfStep5gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
:100  theorem T2524_baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) (walk : T2524_BAStep5IIIWalk d) (fromWalk : T2524_BAStep5IIIFromWalk d) :
:101      STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
:105  theorem T2524_baThm27L_of_texts (d : ℕ) (hd : 3 ≤ d) (walk : T2524_BAStep5IIIWalk d) (fromWalk : T2524_BAStep5IIIFromWalk d)
:106      (h32 : RBM.Univ.UNL32) : BAThm27L d :=
:141  def T2524_WalkAt (d : ℕ) : Prop :=
:142    3 ≤ d → ∀ (κ ε 𝔡 Cd : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
:143      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      ... (4 more lines, to :147)
:374  def T2524_Step5IIIAny : Prop :=
:375    ∀ d : ℕ, 3 ≤ d → STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
:383  theorem T2524_baThm27L_all (h5 : T2524_Step5IIIAny) (h32 : RBM.Univ.UNL32) : T2524_Thm27 :=
:355  def T2524_Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → BAThm27L d
:364  theorem T2524_final_shape (hW : ∀ d : ℕ, 3 ≤ d → T2524_BAStep5IIIWalk d) (hF : ∀ d : ℕ, 3 ≤ d → T2524_BAStep5IIIFromWalk d) :
:365      RBM.Univ.UNL32 → (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
:366        T2524_Thm27 :=
:370  theorem T2524_Thm27_three (h : T2524_Thm27) : RBM.Endpoints.Thm27 := h 3 le_rfl
```
In place the names stay: `BAStep5IIIGoodThm`, `BAStep5IIIWalk`, `BAStep5IIIFromWalk` become `(d : ℕ) : Prop`; `baStep5IIIGoodThm_holds`, `baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds`, `baPfStep5_of_walk`, `baPfStep5_holds` take `(d : ℕ)`; `baStep5III_scalar_flow`, `baStep5III_walkLevel`, `baStep5III_walk_at` take `(d : ℕ) (hd : 3 ≤ d)`; `baStep5IIIGood_bundle`, `Step5IIIWalk_good_of_flow`, `Step5IIIWalk_pertime`, the private `Step5IIIWalk2_{Num,path,fixedN,PT,lift}` take `{d}` and `hd` where used (rows of the table in section 1 give each binder change); `BAStep5IIIWalkConcl` is generic; new `baStep5III_holds_any`.  The `3 ≤ d →` sits inside the Prop texts (house shape of `STIngR5gL d`).  New signatures of the scratch experiment (`#check`):
```
baStep5III_holds_any : ∀ (d : ℕ),
 3 ≤ d → STStep5IIIgL d (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
baPfStep5_holds : ∀ (d : ℕ),
 STPfStep5gL d (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
baStep5IIIWalk_holds : ∀ (d : ℕ), BAStep5IIIWalk d
baStep5IIIFromWalk_holds : ∀ (d : ℕ), BAStep5IIIFromWalk d
baStep5IIIGoodThm_holds : ∀ (d : ℕ), BAStep5IIIGoodThm d
```

## 3. D3: the probe
409 lines (`wc -l`, above), `lake env lean` exit 0 and `lake build RBM3D.Probe.T2524Pins` exit 0; sections: (1) texts :47-83; (2) the chain two texts → `STPfStep5gL d` → `STStep5IIIgL d` → `BAThm27L d` through the merged `baThm27L_any` :86-107; (3) the `d = 3` recovery :109-136: the texts at `d = 3` are the merged texts (`Iff.rfl` for `Good`, `Walk`; `3 ≤ 3 →` for `GoodThm`, `FromWalk`), the merged `baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds`, `baStep5IIIGoodThm_holds` prove them, and `T2524_baThm27L_three` :135 is `BAThm27L 3` from the merged theorems with only `UNL32` (the nonempty instance of the chain); (4) the interface `T2524_WalkAt` :141 and its pin proof :150; (5) the (b) inequalities :159-237, 4-20 lines each; (6) `d = 4`: `T2524_sz4`, `Admissible (1/8) (1/10)` for every `n` :301, and b1, b4 (`τ`), b3, b7 at `d = 4` :306-350; (7) final texts :352-409.  Axioms: 31 of 31 `[propext, Classical.choice, Quot.sound]`.  Registry scan (above): the only premise that no probe theorem concludes is the probe-local `T2524_WalkAt`.  The experiment of D4 (scratch, not in the repo): 13 lexical rules and 77 hand edits on the five files, compiled in import order, exit 0 each, `#print axioms` standard for 9 of 9 (above).

## 4. D4: layout and price
```
$ price.sh   # (A) diff(1) of the experiment; (B) the heads that new files would copy
file     orig_lines head_edit tail_edit    new_lines
Good           704        48         2          706
Good2          198         9         3          200
Walk          1799        33         4         1799
Walk2         1067       169         6         1069
Targets        112        13         1          117
total head edit lines: 272, tail edit lines: 16, all: 288
Good       604
Good2       81
Walk      1520
Walk2      986
Targets     60
total copied head lines: 3251
```
```
$ python3 census_lines.py   # grep-derivable lower bound of (A): head lines carrying a class (a)/(b) token
head lines with a class (a)/(b) token: Good 37, Good2 4, Walk 24, Walk2 134, Targets 0; total 199
```
**(A) in place**: 272 head edit lines (the 199 token lines above plus binder lines, call sites `d hd`, `variable {d : ℕ}`; the 16 tail lines vanish with T2523, section 1); + ≈ 30 doc lines (7 head comment lines say `d = 3`, new docstrings): landing ≈ 300; ×1.74 (§308 (2)) ≈ 520.  **(B) new files**: 3,251 copied head lines + ≈ 75 header/doc lines ≈ 3,330 (the 7,830 `d = 3` lines stay as dead duplicates; every public name needs a primed twin).  **Recommend (A)** (BAD-C4: also at equal price).  External readers of the five files: of their 66 public declarations only `baStep5III_holds` is used in code (`MainIndFamTL:323, :331`, `MainIndTermBA:80, :95, :100, :114`, `MainIndRegBA:42, :83`, `UNBUniv:395`; kept, same type); the other uses are comments (`Test/Axioms:189, :205`, `DuhamelI2:21`).  The certificate cone is untouched: `RBM3D.Main.BandTerminal`, `RBM3D.Main.BUnivHolds` closures contain no U5 file (above); importers of U5: root, `BA/KDecayBA` (Ker, unchanged), `BA/MainIndFamTL` (Targets).
| row | sole writable files | landing (×1.74) | role | depends on | cited names T2523 deletes |
|---|---|---|---|---|---|
| R1 | `BA/Step5III{Good,Good2,Walk,Walk2,Targets}.lean`, in import order | ≈ 300 (≈ 520) | `prover-hard`; the recipe (13 lexical rules + the 77 hand edits) as an amend | 1a-audit, T2523 merged | none: restore 0 lines |
| R2 | `BA/UNBUniv.lean`, `Main/FinalShape.lean` | ≈ 110 (≈ 190) | `prover` | R1 (`baStep5III_holds_any`) | none: restore 0 lines |
R1 needs no split (≤ 1,950 even at ×1.74); the pre-signed split, if its 1b stalls: R1a = Good, Good2 (62 edit lines), R1b = Walk, Walk2, Targets (226).  Rows are sequential: the five files are an import chain and R2 imports R1's theorem.  Restore from e3540151 (BAD-C2 (c)): none, R1 and R2 need no declaration T2523 deletes: price 0.

## 5. D5: the assembly
```lean
theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0))   -- BA/Step5IIITargets; no premise beyond 3 ≤ d;
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0                                       --   exact type of `h5` of `baThm27L_any` (BA/UNBUniv:286), probe :374
def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d                    -- Main/FinalShape:36; probe :355
theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d :=        -- BA/UNBUniv after :281; probe :383
  fun d hd => baThm27L_any d hd (baStep5III_holds_any d hd) h32
theorem Thm27_of_L32 : UNL32 → Thm27 := RBM.BA.baThm27L_all                -- Main/FinalShape:39
theorem final_shape : UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27   -- :43, text unchanged; the single hypothesis is UNL32
```
`∀ d, 3 ≤ d →` is the paper's `d ≥ 3` and matches the band endpoints (`Endpoints:165, :172, :182, :197, :209`); every conjunct of `BAThm27L d` takes `3 ≤ d` first (`BA/MAPins:97, :107, :121`; the instances at `Main/FinalShape:86-93, :105-112` pass `le_rfl` to all five), so no other form is better.  **One-line `d = 3` recoveries** (closing (iii)): `baStep5III_holds := baStep5III_holds_any 3 le_rfl`; `baThm27L_three h32 := baThm27L_all h32 3 le_rfl`; `Thm27_of_L32 h32 3 le_rfl : BAThm27L 3` (probe :387, :390, :392 compile the three).  **Files the assembly edits**: `BA/UNBUniv.lean` (`baThm27L_all`, docstrings :20, :41, :279, :284), `Main/FinalShape.lean` (`Thm27`, `Thm27_of_L32`, docstrings :19-21, :33-35, the two `have h` lines :85, :99 and the five accessors of the second BA instance); `Endpoints.lean` none (`:24` only says Theorem 2.7 stays with the BA gate).  A scratch copy of `Main/FinalShape.lean` with these edits compiled (exit 0): the BA instances become `(final_shape h32).2 3 le_rfl`.
```
$ lake env lean finalshape_test.lean   # scratch copy of Main/FinalShape.lean with R2's edits (Thm27, producer, instances at d = 3 via .2 3 le_rfl); STStep5IIIgL d enters as hA
exit=0 output lines=0
```
**Instances.**  Keep the `d = 3` ones of `final_shape` (the U5 instance sections go with T2523).  **Closing (vii), the `d = 4` instance:** `Sizes 4` data (`T2524_sz4`, `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`) with `Admissible (1/8) (1/10)` for every `n`, `n = 0` included (64 lines, :241-304), and the four conjuncts of `Thm27 4` that read `Sizes` + `Admissible` (decol, locSC, QUE, QDiff) applied to it (14 lines, :394-407): 78 lines < 150, so the full instance, as private helpers and one `example` in `Main/FinalShape.lean`; the BUniv conjunct reads the UN data at `d = 3` (`S0`, `fp`, `clsκ`) and is not applied.  Preflight row 16 (`g²L^d ≤ 1/64` at `d = 4`, `n = 0`) concerns the flow instance `BAFlow`, which no `Thm27` conjunct reads; for a flow instance the data that works is `n ≥ 1` (row 16).

## 6. D6: registry and deltas
Registry lines: none.  `BAStep5IIIWalk/FromWalk/GoodThm` stay Props concluded by a theorem head (`baStep5IIIWalk_holds d`, …), `STStep5IIIgL`, `STPfStep5gL` by `baStep5III_holds_any`, `baPfStep5_holds`; the scan of the probe (above) finds only `T2524_WalkAt`; the real check is the full-build scan at the merge of R1 and R2 (closing (vi)).  Paper deltas: D723 withdrawn = D754 (dispatcher, DECISIONS §371), no new candidate; `T2524a`: D712 (d) ("targets 3, 4 only at `d = 3`") is superseded by R1; no (b)/(c) item for `7_8:2101` (T2459a is already in `d`).  Stale D723/§316/"decision B" text (`stale.sh`): 22 lines in 11 files — `BA/{MADecolQUE, MainIndFamTL, MainIndRegBA, MainIndTermBA, MALocal, MAQDiff, UNBUniv}`, `Main/FinalShape`, `Test/Axioms:175, :381-385`, `Universality/PinsKD:12`, `Universality/GUEPhase/RandomLayerBGD:13`: for the comment tickets (the stage's files: R1's five, R2's two).

## 7. BAD-C3, BAD-C4 and the forecast
**BAD-C3 (REQ triggers).** (1) A (c) item whose replacement changes a statement read outside the U5 files: **no** (no (c) item; of the 66 public declarations of the five files only `baStep5III_holds` is read in code outside, `UNBUniv:395` etc., type unchanged; `STStep5IIIgL` `Chain/Step5Gen:228` unchanged).  (2) An input of the chain merged only at `d = 3` outside the U5 files: **no**; the generalized files compile at abstract `d` against unchanged imports, and the inputs read at `d` are general:
```
baKbound_holds : ∀ (d : ℕ), BAKbound d
@baEMn2ExpHK : ∀ {d : ℕ}, 3 ≤ d → emn2ExpHK d BAFlow baFMz BAflowT0
baKsol_one : ∀ (d : ℕ) {κ g : ℝ}, 0 < κ → 0 < g → ∀ {L : ℕ} [inst : NeZero L], 3 ≤ L → ∀ (W : ℕ) {E : ℝ} {m : ℂ}, BAReal d L g κ E m → ∀ {t : ℝ}, t ∈ Set.Ico 0 1 → ∀ (σ : Fin 
baGridRepNAt2_holds : ∀ (d : ℕ), ∃ C₀, 0 ≤ C₀ ∧ STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0
baFlow_premises : ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ), 0 < κ → 0 < ε → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ (t : ℕ → ℝ), (∀ (n : ℕ), t n ≤ BAflowT0 sz z n) → (∀ (n : ℕ), 
pfStep5Grid_level : PfStep5Grid_level_pin
baStep5CasesGen_flowFacts : ∀ (d : ℕ), Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) fun sz z => BAflowT0 sz z
ST_step5_caseIII_of_pfgL : ∀ (d : ℕ) (law : (sz : Sizes d) → MeasureTheory.Measure (SeqΩ sz)) (Flow : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) (mk : (sz : Sizes d) → (ℕ → ℂ) 
baThm27L_any : ∀ (d : ℕ), 3 ≤ d → (STStep5IIIgL d (fun sz => seqP (withLam sz 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) fun sz z => BAflowT0 sz z)
@lam_sq_mul_pow_ge : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔡 : ℝ}, ↑(W sz n) ^ (-↑d / 2 + 𝔡) ≤ lam sz n → ↑(W sz n) ^ (2 * 𝔡) ≤ lam sz n ^ 2 * ↑(W sz n) ^ d
```
(`PfStep5Grid_level_pin` is `∀ (d : ℕ) (W Dst u u' : ℝ), …`, `PfStep5Grid:97`.  The `d = 3` declarations that U5 reads are instance data: `SizesInst.sz0` Defs/Sizes:260, `FlowPinsInst.*` BA/FlowPins:1181-1254, `Step1SetupInst.*`, read by the instance tails only: no head reads any of them, `inst_census.py`.)  (3) Forecast after this gate ≥ 8: **no** (3).  Any "yes" would be a REQ; none.
**BAD-C4.** In place, rows start after T2523 merges (section 4).  **Stop rules:** merged file changed: no (`git diff --stat` above); probe 409 ≤ 500; open (c): none.  **Forecast (7)**: BA-D = this gate + R1 + R2 = **3 tickets (3–4)**, the 4th being the split of R1 or a comment ticket for the stage's files; the flag 10 and the REQ line 8 are not approached.  The earlier ≈ 5 (4–8) priced ≈ 90-116 places (supervisor 0342 V-F2, REQ BAanyD) that might need mathematics; the census finds none, and the in-place price (≈ 520 at ×1.74) is one row.
