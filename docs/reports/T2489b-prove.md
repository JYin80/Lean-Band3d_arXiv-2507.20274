Prover model: claude-sonnet-5-5
# T2489b: L4b2b = file B (targets 4-7) of ticket T2489, stage 1b (`prover-hard`), branch `t/T2489b`; report written Tue Oct 13 07:07:22 UTC 2026

## (a) Math preflight
Not repeated. Section (a) of `/Users/junyin/Lean_proof/RBM3D/docs/reports/T2489-prove.md` (lines 2-103, written Tue Oct 13 05:14:18 UTC 2026, verdict PASS, pre-signed split applies) is the stage-1a material of this run; file B = its rows B 4-7 (script 4: central 1156, high 1600). Switch conditions (a), (b) absent there; no step below needed an input beyond its list.
## (a′) Preflight corrections
None. Findings (1) and (2) of that 1a are confirmed for file B by the grep below: `twB0_ge`, `ward2`, `twWard` occur 0 times in file B (the fold-plus-Ward sum is `BAExp14b2_fold_ward` of file A, which reads `twFold_holds`); finding (3) (private `Dom_a`) concerned file A.
```
$ grep -c "twB0_ge\|ward2\|twWard" RBM3D/Graph/BAExp14b2B.lean
0
```

## (b) Script output (stage 1b, row L4b2b)
```
# main (6a1c1f8f) was merged into t/T2489b before the first edit: commit 8dae485c (the RBM3D.lean import conflict was resolved by union)
$ lake build RBM3D.Graph.BAExp14b2B 2>&1 | tail -2        (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2489b)
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4026 jobs).
$ lake build   (full library; `#assert_rbm_axioms` last in RBM3D.lean; import line RBM3D.lean:584 after BAExp14b2)  [log tail]
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4355 jobs).
exit=0
$ stop rule: wc -l of the new file at each section commit (stop line 2000 per file, reserve-file trigger 1800), times from git (UTC)
9eb3a3f1 370 lines 06:41:17Z
f0bd13ba 688 lines 06:50:21Z
4eafeb83 1022 lines 06:55:15Z
e0be2a55 1174 lines 06:57:25Z
a4e272dc 1174 lines 07:02:29Z
$ wc -l RBM3D/Graph/BAExp14b2B.lean
    1174 RBM3D/Graph/BAExp14b2B.lean
$ grep -nE "sorry|admit|native_decide|^axiom|inductive|^structure" RBM3D/Graph/BAExp14b2B.lean
(no hit, exit=1)
```

Axioms (`#print axioms` in a scratch file with `open private`; the full build ran `#assert_rbm_axioms`):
```
# ax.lean (scratchpad T2489b/): `import RBM3D.Graph.BAExp14b2B`, `open private` of the three private theorems and `U0`, `#print axioms` of the 29 theorems
$ lake env lean ax.lean | grep "depends on axioms" | wc -l ; ... | grep -c "\[propext, Classical.choice, Quot.sound\]$"
      29
29
'RBM.BA.BAExp14b2B_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2B_T3B' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2B_I41_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2B_T3CG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14b2B_core8' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExp14bS2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All 29 printed theorems of file B (26 public and 3 private: `T3B`, `T3CG`, `core8`; the 10 public defs and the private instance helper `U0` are not printed) print the standard three: `propext`, `Classical.choice`, `Quot.sound`.

Target statements, extracted from the file by script (`sed -n`; file lines given). Target 4, `T3B` (`j = 4, 5`):
```
-- RBM3D/Graph/BAExp14b2B.lean:258
private theorem BAExp14b2B_T3B (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hLm : STLmaxgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) (kb : Bool) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FT3B sz z n (t n) ω kb p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
```
Target 5, `T3C-Ḡ` (`j = 6, 7`):
```
-- RBM3D/Graph/BAExp14b2B.lean:815
private theorem BAExp14b2B_T3CG (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) (kb : Bool) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FT3CG sz z n (t n) ω kb p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
```
Targets 4-5 together, the eight blue families (`core8`, private) and target 6 (the binding conclusion, public; the pin `BAExp14bS2` is `Graph/BAExp14b.lean:170`, unchanged):
```
-- RBM3D/Graph/BAExp14b2B.lean:1033
private theorem BAExp14b2B_core8 (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hLm : STLmaxgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t) (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Fin 8 × Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
-- RBM3D/Graph/BAExp14b2B.lean:1064
theorem baExp14bS2_holds (d : ℕ) : BAExp14bS2 d := by
-- RBM3D/Graph/BAExp14b2B.lean:408  (the deterministic decomposition, public, no pin binder)
theorem BAExp14b2B_I41_eq {n : ℕ} (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (kb σ : Bool) (a b : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) :
    BAExp14b_FT3CG sz z n t ω kb σ a b =
      (∑ a₁, BAExp14b2B_Dd sz z n t kb σ a b a₁ * BAExp14a_X sz z n t ω a₁) + BAExp14b2B_Rr sz z n t ω kb σ a b := by
```
Instances (target 7), `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`), `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2` (`half_lt_t0`); every deterministic hypothesis is discharged; the pins of other gates stay hypotheses. Target 6 (:1121), `U_n` nonempty (:1114):
```
example (n : ℕ) : Nonempty {_p : Fin 8 × (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
    sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)} :=
  ⟨⟨(0, (true, true), (0, 0)), BAExp14b2B_U0 n⟩⟩
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hLm : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hDec : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hT1 : BATwistAvgLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    PrecL sz0 μ0 (U := fun n => {_p : Fin 8 × (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
      (fun n p _ => ‖∫ ω, BAExp14bS2Fam sz0 zSeq n (1 / 2) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ0‖)
      (fun n _ _ => (1 - 1 / 2 : ℝ)⁻¹ * (sz0.Bctl n (1 / 2)) ^ (5 / 2 : ℝ)) :=
  baExp14bS2_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hLm hK hDec hT1 hT2
```
Target 6 with TL1 supplied by name (:1134, terms), target 4 (:1147), target 5 (:1156), the decomposition (:1166); the hypotheses of the last three examples are the pins each theorem reads (4 and 5 pins):
```
  baExp14bS2_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hLm hK hDec
    (baTwistAvgProd_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hLm) hT2
  BAExp14b2B_T3B (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num) flow_sz0 (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hE hA hLm hT1 kb
  BAExp14b2B_T3CG (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num) flow_sz0 (t := fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hE hA hK hT1 hT2 kb
example (ω : sz0.SeqΩ) (kb σ : Bool) :=
  BAExp14b2B_I41_eq (z := zSeq) (BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0) (n := 0) (t := 1 / 2) (by norm_num)
    (by norm_num) kb σ 0 (Pi.single 0 1) ω
```

Checks. `docs/tickets/checks/T2489-check.lean` compiles on the branch; target 6 equals `T2489_S2` (scratch copy = the check + `import RBM3D.Graph.BAExp14b2`, `...B2B` + `example : T2489_S2 := baExp14bS2_holds`, a term; not committed). Target 1 (a), (b) were checked in the report of L4b2a.
```
$ lake env lean docs/tickets/checks/T2489-check.lean > chk1.out 2>&1; echo exit=$?; grep -c error chk1.out
exit=0
0
$ lake env lean chk2.lean > chk2.out 2>&1; echo exit=$?; grep -c error chk2.out; grep -n T2489_S2 chk2.lean | sed -n "1p;\$p"
exit=0
0
186:def T2489_S2 : Prop := ∀ d : ℕ, BAExp14bS2 d
251:example : T2489_S2 := baExp14bS2_holds
```
Name clash, diff, importers (greps; `main` = 5e44951d, scan over all local heads and remotes except `t/T2489b`):
```
$ git grep -n -e BAExp14b2B -e baExp14bS2_holds main -- RBM3D RBM3D.lean | cut -c1-110
main:RBM3D/Graph/BAExp14b2.lean:18:(`Graph/BAExp14b2B.lean`, L4b2b) holds `T3B`, `T3C-Ḡ` and the binding concl
$ for r in <refs except t/T2489b>; do git grep -q -e BAExp14b2B -e baExp14bS2_holds $r -- RBM3D RBM3D.lean && echo HIT $r; done
HIT refs/heads/main: (`Graph/BAExp14b2B.lean`, L4b2b) holds `T3B`, `T3C-Ḡ` and th
HIT refs/heads/t/T2489: (`Graph/BAExp14b2B.lean`, L4b2b) holds `T3B`, `T3C-Ḡ` and th
HIT refs/heads/t/T2493: (`Graph/BAExp14b2B.lean`, L4b2b) holds `T3B`, `T3C-Ḡ` and th
HIT refs/remotes/origin/main: (`Graph/BAExp14b2B.lean`, L4b2b) holds `T3B`, `T3C-Ḡ` and th
refs scanned: 507
$ git diff --stat main...t/T2489b
 RBM3D.lean                  |    1 +
 RBM3D/Graph/BAExp14b2B.lean | 1174 +++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1175 insertions(+)
$ grep -rn "BAExp14b2B" RBM3D RBM3D.lean | grep import
RBM3D.lean:584:import RBM3D.Graph.BAExp14b2B
$ ports from ../RBM1D, ../RBM2D: none (those trees were not read or touched); stem copies of merged private lemmas: none
```
Greps required by the ticket (file B only):
```
$ grep -nE "\.lam|withLam|gK" RBM3D/Graph/BAExp14b2B.lean | cut -c1-105
1061:on `U_n = {λ²/L^d ≤ 1 - t}`, over the carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`, from t
1072:        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ (k + 2) ≤ 1 - t n}) =>
1098:private theorem BAExp14b2B_U0 (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ) :=
1099:  have h1 : sz0.lam n ≤ 1 := by
1115:    sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)} :=
1126:        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
1138:        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ)})
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus' RBM3D/Graph/BAExp14b2B.lean
(no hit)
$ script: pins in signatures (the seven premises) of public / private declarations of file B
public decls 36 | private decls 4
public with a pin in the signature: []
private with pins (name, number of the seven): [('BAExp14b2B_T3B', 4), ('BAExp14b2B_T3CG', 5), ('BAExp14b2B_core8', 6)]
```

Hypothesis and UBA-C1 table (file B has no `sz.lam` outside the pin's own `U` (:1072) and the instance data, no `gK`, no comparison text R1, no new `inductive`, no `ℝ`-valued `∃ C` after `(sz, z)`; constants `(CM, S)` come from `BAExp14a_facts_of_flow` and `C` from `twK_bound_holds` (both before `sz, z`)):
| declaration | pins in binders | other hypotheses | coupling `g₀` read |
|---|---|---|---|
| `Dom_sqrt`, `wsum12`, `s`, `a_le`, `b_le`, `Lm_le`, `diag_le`, `split3`, `Lt_eq`, `sum3`, `vec_eq`, `arith{D,Q}`, `envQ`, `*_ge` | none | pathwise or real data | none |
| `T3B_le`, `Yr_le`, `Rr_le`, `Dd_le`, `I41_eq` | none | `BAFlow`, `Facts`, `t in [0, T0]`, sup-bounds as reals | `BAMfine_eq` inside `twMB`, `fold_ward`, `L3_ward` (file A) |
| `core` | none (`hP3 : PrecL`, generic) | `BAFlow`, eventual `Facts`, deterministic `D`, pathwise `Q` | none |
| `T3B` (private) | `STLocalEntrygL, LWAvgLawgL, STLmaxgL, BATwistAvgLaw` | `BAFlow`, `t in [0, T0]` | only inside merged `facts_of_flow` |
| `T3CG` (private) | `STLocalEntrygL, LWAvgLawgL, STLKgL, BATwistAvgLaw, BATwistLoopLaw` | same | + `baKbound_holds`, `baKward_holds`, `twK_bound_holds` (window `BAflow_lam0_window`, eventual) |
| `core8` (private) | the above six (not `STDecaygL`) | same | as above |
| `baExp14bS2_holds` | none in a binder (all seven inside the def `BAExp14bS2`) | `d` | the pin's `U`: `sz.lam n ^ 2 / L^d ≤ 1 - t n` |
Registry: no line added. `LWAvgLawgL` is not registered, so every helper with a Step 1/2 or TL binder is private; the public theorems are pin-free by the script above. The full `lake build` (registry check, `scanPremises`) passed.

Census (merged declarations read by file B; `file:line`; all public unless marked; `open private` from file A: `base` :804, `tl2` :975, `I1K` :1396; stem copies of merged lemmas: none):
- `Graph/BAExp14b2.lean` (file A): `sup` 108, `le_sup` 110, `sup_le` 113, `sup_nonneg` 116, `Dom_sup` 120, `det_ev` 135, `MB_row` 152, `MB_col` 159, `norm_int_add` 414, `s` 736, `Th` 780, `Bs` 784, `Tsplit` 788, `Bs_le` 793, `vec2` 800, `base` (P) 804, `tl2` (P) 975, `twChg_true` 970, `M_tie` 1120, `L2_le` 364, `kap_col` 1381, `I1K` (P) 1396, `L3_ward` 1473, `fold_ward` 1549, `wsum_c2` 1632, `wsum_c1` 1650.
- `Graph/BAExp14aB.lean`: `X` 57, `a` 216, `b` 220, `le_a` 224, `le_b` 228, `a_nonneg` 233, `b_nonneg` 236, `Dom_b` 288, `Facts` 391, `GM_le` 814, `X_le` 821, `int_X` 852, `ev` 1253, `t_lt_one` 1267, `eta_inv_le` 1271, `floor` 1280. `Graph/BAExp14a.lean`: `Dom` 260 (`refl mul add of_le mono const_mul`), `prec_congr` 90, `prec_of_bad` 99, `prec_of_le_ev` 109, `prec_mono` 116, `prec_fin` 217, `prec_int` 299, `eta_pos` 1266.
- `Graph/BAExp14b.lean`: `FS2` 124, `FT3B` 112, `FT3CG` 118, `FT3B_block` 762, `FT3CG_block` 807, `MB` 427, `kap` 435. `BA/TwistPins.lean`: `twChg` 61, `twTrP` 63, `twLoopX` 66, `twK` 76, `BATwistAvgLaw` 91, `BATwistLoopLaw` 95, `twCirc_holds` 467. `BA/KBound.lean`: `baKbound_holds` 245, `baKward_holds` 302. `BA/TwistAvgB.lean`: `baTwistAvgProd_holds` 451 (instance only). `BA/GreenSchur.lean`: `BAflow_real` 59.

Narrative.
- Delivered: `RBM3D/Graph/BAExp14b2B.lean`, 1174 lines (1a central 1156, high 1600; stop line 2000 and reserve trigger 1800 not reached), and `import RBM3D.Graph.BAExp14b2B` at `RBM3D.lean:584`. Targets 4 (`T3B`), 5 (`T3C-Ḡ`), 6 (`baExp14bS2_holds`), 7 (instances above). No third file.
- `BAExp14b2B_core` (:90) is the general form of file A's `BAExp14b2_close`: `Φ = Σ_{a₁} D_{a₁} X_{a₁} + R`, `Σ|D| ≤ D_n ≺ g_D` paid with the sharp P3 (`D_n g_D 𝔟^{3/2} ≲ ζ`), `|R| ≤ Q ≺ g_Q ≲ ζ` with `BAExp14a_prec_int`, `ζ = (1 - t)⁻¹ 𝔟^{5/2}`; `T3B` uses it with `D = 0`.
- `T3B` (:258): pathwise `‖T3B‖ ≤ S C_M a τ̂ η⁻¹ A √Q` (`T3B_le`: block form, `wsum_c2`, file A's `L3_ward`), `A = 1 + b` (`diag_le`), `Q = max|𝓛^{(2)}|` (`STLmaxgL`, `Dom_sqrt`); `a ≺ 𝔟`, `τ̂ ≺ 𝔟` (TL1), `b ≺ 𝔟^{1/2}`: exponent `1 + 1 + 1/2` against `5/2`, zero slack in TL1; `η⁻¹ ≤ κ⁻¹ (1 - t)⁻¹`.
- `T3C-Ḡ` (:815): the slot-2 circle (`twCirc_holds`, as in `T2b`) and `Tr(G^σ P) = T̂ + B` give `Φ = Σ D X + R` (`I41_eq`); `L̃ = K̃ + (L̃ - K̃)`, `𝓛^{(2)} = 𝒦^{(2)} + (𝓛 - 𝒦)`. `D`: (iii) `K̃ 𝒦` and the `B 𝒦` part of (iv): `Σ|D| ≤ W^d S C_M (C 𝔟) y_W + S C_M² y_K` (`Dd_le`), `W^d y_W ≺ η⁻¹` (`baKward_holds`, `Dom.mono`), `y_K ≺ 𝔟` (`baKbound_holds`), paid with P3 (`3/2 + 1`, zero slack). `R`: (i) `wsum12` + `fold_ward` with `A = 1 + b`; (ii) TL2 `λ̃ ≺ 𝔟^{3/2}` times `W^d y_W` (zero slack); the `T̂` part of (iv) with `W^d W^{-d} = 1` (`Rr_le`). `STDecaygL` is read by no family; `STLmaxgL` only by `T3B`.
- `baExp14bS2_holds` (:1064): `core8` (`BAExp14a_prec_fin` over `Fin 8`; `I1K` of file A for `j < 4`, `T3B`, `T3C-Ḡ`) precomposed with the red-charge map and `integral_conj`, as `baExp14a_S1_holds` (`BAExp14aB:1685-1715`). The statement is the merged pin `BAExp14bS2` unchanged (X1-C4); TL1, TL2 and the five Step 1/2 pins are exact-type premises inside it.
- Not done here and not owed by this row: S1, S3, the identity, `BALWCutExpTw` and its closure (T2490), L6's wiring.

## (c) Verified Mathlib names (`#check` in a scratch file importing `RBM3D.Graph.BAExp14b2B`, 0 errors for each)
`Real.sqrt_le_iff`, `Real.sq_sqrt`, `Real.sqrt_eq_zero_of_nonpos`, `Real.sqrt_eq_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.norm_eq_abs`, `pow_lt_pow_left₀`, `pow_le_pow_right₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `mul_inv_cancel₀`, `one_le_inv₀`, `inv_le_one_of_one_le₀`, `Finset.sum_comm`, `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_le_sum`, `Finset.sum_nonneg`, `Finset.sum_congr`, `Finset.sup'_le`, `Complex.norm_real`, `Complex.norm_conj`, `Complex.norm_natCast`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integrable_finsetSum`, `MeasureTheory.integral_const_mul`, `norm_sum_le`, `norm_sub_le`, `norm_add_le`.
Absent under the name tried: `MeasureTheory.integral_conj` (the root `integral_conj` is the one used, with `open MeasureTheory`). `import Mathlib` has no olean in this tree (the scratch imports the project module).

## (d) Open issues and paper-delta candidates
- Size: file B landed at 1174 lines against 1a central 1156 (ratio 1.02, file A had 1.45).
- `main` moved after the first merge (HEAD `5e44951d`): `git diff 6a1c1f8f main -- RBM3D.lean` adds `import RBM3D.BA.B45BA` right after `import RBM3D.Graph.BAExp14b2`, the position of this branch's `import RBM3D.Graph.BAExp14b2B`. The hub adds the import line itself (CLAUDE.md §3 (A) 4); this branch's full build is on base `6a1c1f8f` plus the two files.
- Observation: premise 5 of S2 (`STDecaygL`) is read by none of the eight families (file A reads neither `STLmaxgL` nor `STDecaygL`; file B reads `STLmaxgL` in `T3B` only). It stays in the pinned text (X1-C4).
- Paper-delta candidates (route only; no Lean/paper statement difference in this file): **T2489c**: `T3C-Ḡ` (iii), (iv) use no decay in `|a - c₁|`, no `twB0_ge`, and no improved average: the `ℓ¹` data read are the columns of `κ_k` (`≤ S`), rows/columns of `M^{(B)}` (`≤ C_M`) and `Σ_{c₂}|𝒦^{(2)}| ≺ (W^d η)⁻¹`; the deterministic terms close with the derived sharp P3 (`3/2 + 1`), the fluctuation of `Tr(G^σ P)` with TL1 and `W^d W^{-d} = 1`. **T2489d**: `T3B` closes with TL1 at zero slack and `A = max|G_{xx}| ≺ 1 + 𝔟^{1/2}` (`|M| ≤ 1`), no `STExpAvgAt` twin. T2489a, T2489b (file A) are unchanged.
