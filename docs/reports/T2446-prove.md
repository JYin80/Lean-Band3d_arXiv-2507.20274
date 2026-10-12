Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 09:48:29 UTC 2026

### (i) Exponent table (T2446: no exponent beyond target 5; the other rows are the numerical parameters of the instance)
| quantity | value | constraint | slack |
|---|---|---|---|
| `L`, `W` (targets 4, 5 identity) | `L = 4`, `W = 2`, `d = 3` | `3 ≤ L`, `NeZero L, W` (statement `T2446_Lemma`) | `L - 3 = 1` |
| data `(g0, Em, t, m)` | `(g0P, EP, t0P, m0P)`, `CouplingWindow.lean:861-864` | `BASelf d L g0 Em m`, `0 ≤ t < 1`; `flowP_data : 0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P EP m0P` (`:869`) | `t0P` interior to `(0,1)` |
| cutoff `K` (targets 3, 4) | `ord P + 2` (script), `10` at `baGGLhs` | strategy steps only if `ord Q < K`; `ord baGGLhs = 0` | `K - ord = 2`, `10` |
| measure `μ = ((K-ord)⁺, nExt, loops, nS, pairs) ∈ ℕ⁵` | lex order | `Γ.ord < K`, `BALvl1Good Γ Q` ⇒ `μ Q <lex μ Γ`: if `ord Q > ord Γ` then `(K-ord Q)⁺ ≤ K-ord Γ-1 < (K-ord Γ)⁺` (`≥ 1` as `ord Γ < K`); if equal, `BALvl1Good` second disjunct is lex-fall of `(nExt, loops, nS, pairs)` (`BALvl1B:63-69`), and `nExt ≤` is a conjunct | per step, strict by `≥ 1` in one component; WF: product of `ℕ` orders |
| `c` (target 5) | `1/4` | `0 < c` | `1/4` |
| `K0`, `d` (target 5) | `2`, `3` | `L^d ≤ W^K0` with `W^(-d/2) ≤ Ψ ≤ W^(-c)` | `d/2 - c = 5/4 > 0` (window nonempty); instance `W=16, L=6`: `216 ≤ 256` (log2 slack 0.246), `Ψ ∈ [1/64, 1/2]` |
| `D` (target 5) | `10` | error size `≤ W^(-D)` | see next rows |
| counters of `P = baGGLhs` | `(nS, nW, nA, nM) = (2, 0, 1, 1)`, `ord = 0` (`BAVocab.lean:1237-1242`; slot `nV = nA`, `BAVocab:143`) | `lvl1Cutoff c K0 d D G = ⌈(D + K0·nM + d·(nA-nW)⁺)/c⌉` (`LWLvl1:3981-3982`) | `K = ⌈(10 + 2 + 3)·4⌉ = 60` |
| exponent inequality of `lvl1_size_le` (`lvl1_size_le`, `LWLvl1:3989`) | `c·K = 15` | `c·K ≥ D + K0·nM + d·δ = 15` (`δ = (nA-nW)⁺ = 1`) | exponent slack `0` (ceiling is exact here); numeric slack of the actual size: log2 `2.245` (below) |
| `Q ∈ outs ++ errs` (third conjunct) | `ord Q ≥ K = 60`, `nM Q ≤ 1`, `nA Q - nW Q ≤ 1` | hypotheses `hK, hM, hV` of `lvl1_size_le` (`nV` slot = `nA` by `BAGraph.counters`) | all three are conjuncts of `T2446_Lemma`/`T2446_LemmaSize` third clause |

### (ii) One concrete nondegenerate instance
Data (all targets): `d = 3, L = 4, W = 2`, `(g0P, EP, t0P, m0P)` (row 2: `BASelf`, `0 < t0P < 1` by `flowP_data`). Graphs: `baGGLhs` (`E = Fin 2`, one internal vertex, solid `0→x`, `x→1`, `ord 0`, `nM = nA = 1`) and `(baPG baPB).twist true true` (`P_B`: `E = Fin 2`, three internal vertices, `nS = 3, nW = 1, nA = 2, ord = 1`). No `N = 0`, no empty edge list, no collapsed window, no external hypothesis.
Script: Python model of the BA strategy (frame steps `lw2/lw4`, `lanlw`, `gg2/gg4`, macro (a), macro (b), BA partition `ba_partition`; copied from the T2423/T2442 scratchpad `model.py`, `run.py`, `inv.py`, which transcribe `BASim:82-100`, `BAWeightOp`, `BAGGOp`, `BAExpandW`), plus `strategy.py`: the case table (iv) below with the selector `(c,t)` of `LWSymm:1975-2030`, the step at `twistG(P,c,t)`, outputs twisted back, `μ` compared output vs parent at every expanded node (memo by canonical form), leaves classified, and the assertion that the chosen constructor is a member of `frame_steps` of the twisted graph (the hypotheses of `BAFrameStep.<kind>`).
```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2446 && python3 strategy.py
baGGLhs: K=2 root inv(ord,nM,nA-nW,loops,nS,pairs,nExt)=(0, 1, 1, 0, 2, 1, 2) distinct nodes=192
  steps by (case,kind): {('1a', 'weight'): 2, ('1b', 'within'): 4, ('3gg', 'gg'): 1}
  leaves: {'err(ord>=K)': 182, 'out(LocStd, ord<K)': 3} | output-vs-parent mu comparisons: 191 | violations: 0
baGGLhs: K=10 root inv(ord,nM,nA-nW,loops,nS,pairs,nExt)=(0, 1, 1, 0, 2, 1, 2) distinct nodes=4001 TRUNCATED at cap
  steps by (case,kind): {('1a', 'weight'): 18, ('1b', 'within'): 70, ('3gg', 'gg'): 9, ('3split', 'ggSplit'): 14}
  leaves: {'out(LocStd, ord<K)': 11, 'err(ord>=K)': 3884} | output-vs-parent mu comparisons: 4165 | violations: 0
twist(true,true) baPB: K=3 root inv(ord,nM,nA-nW,loops,nS,pairs,nExt)=(1, 1, 1, 1, 3, 0, 2) distinct nodes=416
  steps by (case,kind): {('1a', 'weight'): 1, ('1b', 'within'): 3, ('2', 'edge'): 7}
  leaves: {'err(ord>=K)': 405} | output-vs-parent mu comparisons: 417 | violations: 0
ALL OK
$ python3 rand.py     # 120 random normal non-LocStd BA parents, K = ord+1 or ord+2, cap 150 nodes each
random non-LocStd normal parents: 120 | runs with violations: 0
steps by (case,kind) over all runs: {('1a', 'weight'): 142, ('1b', 'within'): 89, ('2', 'edge'): 122, ('3gg', 'gg'): 34, ('3split', 'ggSplit'): 11}
$ python3 size.py     # target 5: cutoff and the size bound on a grid of (Ψ, ord ≥ K, nM ≤ 1, nA-nW ≤ 1) at d=3, c=1/4, K0=2, D=10, W=16, L=6
cutoff K = 60 | c*K = 15 >= D + K0*nM + d*delta = 15 | ord(G) = 0 < K: True
L^d = 216 <= W^K0 = 256 : True | window W^(-d/2) = 0.015625 <= Psi <= W^(-c) = 0.5
max over the grid of log2 size(Q) = -42.245 at Psi=0.50000 ord=60 nM=1 nA-nW=1 <= log2 W^(-D) = -40.0
slack in log2 = 2.245
```
Reading: at `baGGLhs`, `K = 2`: 192 distinct nodes, steps `weight`, `within`, `gg`, 3 locally standard leaves with `ord < K`, 182 leaves with `ord ≥ K`; at `K = 10` the run was cut at the 4000-node cap (every expanded node checked) and reaches all four kinds `weight/within/gg/ggSplit`; at the twist of `P_B`, `K = 3`: kinds `weight/within/edge`. `μ` falls at all 191 + 4165 + 417 output comparisons, 0 violations; the random runs hit every case `1a, 1b, 2, 3gg, 3split`. (Statement-level instances of the ticket (target 2 at `baGGLhs`, at the twist of `P_B`; target 4 at `K = 10`; target 5 at `d=3, c=1/4, K0=2, D=10`) are the data above.)

### (iv) Case table of target 2 (normal `P`, `¬ LocStd`); selector `(c,t)`; every constructor hypothesis at `P.twist c t`
Exhaustive: `Normal ∧ ¬LocStd ⇒ ¬hwf ∨ ¬(third clause)` (`BAAtomic:70-74`). Under `hwf`, `¬(third clause)` gives an internal atom with `atEdges ≠ []` and `¬(σ-list ∈ {[true,false],[false,true]} ∧ charge = 0)`. Either `length ≠ 2 ∨ charge ≠ 0` (case 2) or, for every internal atom, `atEdges = [] ∨ (length = 2 ∧ charge = 0)` (= `hnb`), and the bad atom has `length = 2`, `charge = 0`, σ-list `[t,t]` or `[f,f]`; with `atCharge` (`BAAtomic:66-68`) an equal-colour pair with charge `0` has exactly one end in the atom per edge, one out and one in (two out-edges of one colour give `±2`). The twist maps `atEdges` by `lwSymmTwistS` and multiplies `atCharge` by `±1`, so none of `atEdges = []`, `length`, `charge = 0` changes.
| branch | constructor | `(c,t)` | hypotheses at the twist |
|---|---|---|---|
| 1a: `e ∈ solid`, `src = dst` | `weight` | `(!σ, false)`, `lwSymm_twist_weight` (merged) | `p ∈ lwSplit`: `BASymm2_frame_mem` (merged, with `lvl1_exists_split_fst`); `σ`, `src = dst`: selector + `lwSymmTwistS_loop`; `circ`: `Normal` + `BASymm2_frame_circ` (merged) |
| 1b: `sameAtom src dst`, `src ≠ dst` | `within` | `(!σ, false)`, `lwSymm_twist_out` (merged) | `sameAtom` at twist: `BASymm1_twist_sameAtom` (merged); `src ≠ dst`: `lwSymmTwistS_loop` (merged) |
| 2: `hwf`; internal atom, `atEdges ≠ [] ∧ (len ≠ 2 ∨ charge ≠ 0)` | `edge` at `e ∈ atEdges`, `x = inr j` its end in the atom (`isRight` by `intAtom`, `BAAtomic_intAtom_iff`) | `lwSymm_selector_edge` (merged): out `(!σ,false)`, in `(!σ,true)`; other end `≠ x` as exactly one end is in the atom | `hwf`, `hv`: `BASymm1_twist_sameAtom` (merged); `hint`: `BASymm1_twist_intAtom` (merged); `hbad`: **new** transport `atEdges(twist) = (atEdges).map twistS` (filter predicate `!=` symmetric in `src/dst`), same length, `atCharge(twist) = ± atCharge` (`c`, `t` each flip the sign) |
| 3: `hnb`; bad atom (equal colours); `p = e1`, `q = e2` from `lvl1_split_two` on `atEdges` | `gg` if `u1 = u2`, else `ggSplit` (`u1 = p'.src`, `u2 = q'.dst`, both in the atom, `hsame`) | `lwSymm_selector_pair` (merged) for `gg`; for `ggSplit` a **new** two-vertex form from `lwSymm_twist_out/in`, `lwSymm_twist_pair_in/out` (merged) | `q' ∈ lwSplit p'.2`: `BASymm2_pair_mem` (merged); `hnb`, `hwf`, `hint` at the twist: **new** (same transport as in 2); `ggSplit` index `j` with `(lwSplit p'.2)[j]? = some q'`: **new** (from membership) |
Every branch finds a constructor; none is missing. The script instantiates the constructor at the twisted graph in every expanded node of every run above (assertion `(kind,i,j) ∈ frame_steps`).

### Verdicts
- Target 1 (pins `BAlvl1ExistsStep`, `BAlvl1Lemma`): PASS — the two statements are satisfiable at the instance (ii) (target 2 at `baGGLhs` and at the twist of `P_B`: the script finds a step; target 4: all hypotheses are the data row of (i)).
- Target 2 (`baLvl1ExistsStep_holds`): PASS — case table complete (iv); new work is the twist transport of `atEdges`/`atCharge`/`hnb` and the two-vertex pair selector.
- Target 3 (`BALvl1Mu`, `baLvl1Lt_wf`, `ba_lvl1_mu_lt`, `BAReach.trans`, `ba_lvl1_induction`): PASS — `μ` falls by the measure row of (i) (script: 0 violations); `trans`, `induction` are induction on `BAReach` (`BAReach.step`: `Pred Q`, `BALocStep Q L`, `R ∈ L`).
- Target 4 (`baLvl1Lemma_holds`): PASS — strong induction on `μ`: `ord ≥ K` ⇒ `errs = [P]`; `LocStd ∧ ord < K` ⇒ `outs = [P]`; else target 2 and `baLvl1StepGood_holds` give `Q` normal and `BALvl1Good`, so target 3 gives the IH at each output; `BAReach K P Q` by `BAReach.step P P Q L refl`. Identity: `∫P.val = ∫BAComb.val L` (`baLvl1StepIdentity_holds`), then `∫ Σ_Q Q.val = Σ_Q ∫ Q.val` needs `Integrable (Q.val ·)` (`BALvl1A_integrable_val` via `val_of_factor`/`val_of_not`), IH per `Q`, and the pathwise identity `BAComb.val (L.flatMap fo ++ L.flatMap fe) = Σ_Q BAComb.val (fo Q ++ fe Q)`; the lists come from `lvl1_choose_list` and do not depend on the data. The hypotheses `3 ≤ L`, `BASelf`, `0 ≤ t < 1` are consumed by `baLvl1StepIdentity_holds` and `BALvl1A_integrable_val`.
- Target 5 (`baLvl1LemmaSize_holds`): PASS — target 4 at `K = lvl1Cutoff c K0 d D P.g.counters`, then `lvl1_size_le`; exponent slack `0` in `c·K ≥ D + K0·nM + d·δ` (exact at the instance, `15 = 15`), numeric slack log2 `2.245` at the worst grid point.
- Sections (iii) section map, (v) `obtain` steps and (vi) line prediction of the ticket's preflight list are not part of section (a) under CLAUDE.md §4 step 1 (exactly (i)-(ii); no size estimates); they go to the 1b report.

## (b) Script output — stage 1b, model claude-sonnet-5-5, branch `t/T2446` (base 74af906), started Mon Oct 12 09:49:07 UTC 2026

### Files, stop line, diff, commits
```
$ wc -l RBM3D/Graph/BALvl1C.lean; ls RBM3D/Graph | grep -c BALvl1C2   # stop line 2,000 per file; reserve file not used
     627 RBM3D/Graph/BALvl1C.lean
0
$ git diff --stat main...t/T2446; git status --short | wc -l
 RBM3D/Graph/BALvl1C.lean | 627 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 627 insertions(+)
       0
$ TZ=UTC git log main..t/T2446 --format="%h %ad %s" --date=format-local:"%H:%M:%S UTC"
4a40bd2 10:03:10 UTC T2446: BALvl1C section 7 (instances), change for show
d284d0d 09:58:26 UTC T2446: BALvl1C sections 5-6 (baLvl1Lemma_holds, baLvl1LemmaSize_holds)
3c0b6d8 09:57:10 UTC T2446: BALvl1C sections 1-4 (pins, measure, induction, twist transport, baLvl1ExistsStep_holds)
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/BALvl1C.lean | wc -l; grep -c "^inductive" RBM3D/Graph/BALvl1C.lean
       0
0
```

### Build
```
$ date -u; lake build RBM3D.Graph.BALvl1C 2>&1 | tail -1; date -u; lake env lean RBM3D/Graph/BALvl1C.lean 2>&1 | wc -l   # last: lines of warnings/errors of this file
Mon Oct 12 10:14:32 UTC 2026
Build completed successfully (3826 jobs).
Mon Oct 12 10:14:34 UTC 2026
       0
$ full library with a temporary `import RBM3D.Graph.BALvl1C` in RBM3D.lean (restored from a copy; the hub adds the import at merge, §3 (A) 4): `lake build` 10:01:47 -> 10:02:38 UTC, exit 0
5212:info: RBM3D.lean:502:0: axiom audit: 13036 theorems, 4108 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
5427:Build completed successfully (4270 jobs).
$ git status --short | wc -l; git diff --stat main...t/T2446 -- RBM3D.lean RBM3D/Test | wc -l   # RBM3D.lean and Test/Axioms.lean unchanged on the branch
       0
       0
```

### Axioms of the 25 public declarations (scratch file `import RBM3D.Graph.BALvl1C` + `#print axioms` for every `theorem`/`def` name of the file, `lake env lean`; grouped by script)
```
[propext, Classical.choice, Quot.sound] (22): ba_lvl1_induction, ba_lvl1_mu_lt, BALvl1C_atCharge_twist, BALvl1C_atCharge_twist_eq_zero, BALvl1C_atEdges_twist, BALvl1C_atEdges_twist_length, BALvl1C_atEdges_twist_ne_nil, BALvl1C_atom_congr, BALvl1C_end_in_atom, BALvl1C_hbad_twist, BALvl1C_hnb_twist, BALvl1C_hwf_twist, BALvl1C_inr_of_mem, BALvl1C_twist_solid, BAlvl1ExistsStep, baLvl1ExistsStep_holds, BAlvl1Lemma, baLvl1Lemma_holds, BAlvl1LemmaSize, baLvl1LemmaSize_holds, BALvl1Mu, BAReach.trans
[propext] (1): BALvl1C_pair_selector
NONE (2): BALvl1Lt, baLvl1Lt_wf
```

### Targets 1-5, extracted by script (`python3 -I stmt.py show`; body diff against the check file by `stmt.py diff`)
```
[50] def BAlvl1ExistsStep : Prop := ∀ {E : Type} (P : BAPGraph E), P.g.Normal → ¬ P.g.LocStd → ∃ outs, BALocStep P outs
-- BALvl1C.lean:53
def BAlvl1Lemma (d : ℕ) : Prop :=
  ∀ {E : Type} (K : ℤ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧ (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ outs ++ errs, BAReach K P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
-- BALvl1C.lean:63
def BAlvl1LemmaSize (d : ℕ) : Prop :=
  ∀ {E : Type} (c : ℝ), 0 < c → ∀ (K0 : ℕ) (D : ℝ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
    (∀ Q ∈ outs ++ errs, BAReach (lvl1Cutoff c K0 d D P.g.counters : ℤ) P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧
      Q.g.nM ≤ P.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
[95] def BALvl1Mu (K : ℤ) (P : BAPGraph E) : ℕ × ℕ × ℕ × ℕ × ℕ := ((K - P.g.scalingOrder).toNat, P.g.nExt, P.g.nLoops, P.g.nS, P.g.nPairs)
[99] def BALvl1Lt (a b : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))) a b
[102] theorem baLvl1Lt_wf : WellFounded BALvl1Lt :=
[107] theorem ba_lvl1_mu_lt {K : ℤ} {Γ Q : BAPGraph E} (hK : Γ.g.scalingOrder < K) (hg : BALvl1Good Γ.g Q.g) : BALvl1Lt (BALvl1Mu K Q) (BALvl1Mu K Γ) := by
[80] theorem BAReach.trans {K : ℤ} {P Q R : BAPGraph E} (h1 : BAReach K P Q) (h2 : BAReach K Q R) : BAReach K P R := by
[87] theorem ba_lvl1_induction {K : ℤ} {P Q : BAPGraph E} (h : BAReach K P Q) (Pred : BAPGraph E → Prop) (h0 : Pred P) (hstep : ∀ (A : BAPGraph E) (L : List (BAPGraph E)), BALocStep A L → Pred A → ∀ B ∈ L, Pred B) : Pred Q := by
[430] theorem baLvl1ExistsStep_holds : BAlvl1ExistsStep := by
[532] theorem baLvl1Lemma_holds (d : ℕ) : BAlvl1Lemma d := by
[554] theorem baLvl1LemmaSize_holds (d : ℕ) : BAlvl1LemmaSize d := by
BAlvl1ExistsStep vs T2446_ExistsStep -> IDENTICAL BODY (83 chars)
BAlvl1Lemma vs T2446_Lemma -> IDENTICAL BODY (640 chars)
BAlvl1LemmaSize vs T2446_LemmaSize -> IDENTICAL BODY (820 chars)
```

### Scratch copy of the check file (not merged): `import RBM3D.Graph.BALvl1C` added, then these lines
```
216:example : BAlvl1ExistsStep = T2446_ExistsStep := rfl
217:example (d : ℕ) : BAlvl1Lemma d = T2446_Lemma d := rfl
218:example (d : ℕ) : BAlvl1LemmaSize d = T2446_LemmaSize d := rfl
219:example : T2446_ExistsStep := baLvl1ExistsStep_holds
220:example (d : ℕ) : T2446_Lemma d := baLvl1Lemma_holds d
221:example (d : ℕ) : T2446_LemmaSize d := baLvl1LemmaSize_holds d
222:example : T2446_Trans := @BAReach.trans
223:example : T2446_Induction := @ba_lvl1_induction
225:example : T2446_MuLt := fun K Γ Q hK hg => ba_lvl1_mu_lt hK hg
$ lake env lean T2446-check-scratch.lean  -> exit 0; lines with 'error': 0
```

### The compiled nonempty instances (module `BALvl1CInst`, `BALvl1C.lean:562-623`; statements by script, proofs apply the targets)
```
[570] example : (∃ outs, BALocStep (baPG baGGLhs) outs) ∧ (∃ outs, BALocStep ((baPG baPB).twist true true) outs) :=
[575] example : ∃ Q ∈ (((baPG baPB).withinOuts pB).map (BAPGraph.twist true true)), Q.g.Normal ∧ BALvl1Lt (BALvl1Mu 100 Q) (BALvl1Mu 100 ((baPG baPB).twist true true)) ∧ BAReach 100 ((baPG baPB).twist true true) Q := by
[588] example : ∃ outs errs : List (BAPGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ (baPG baGGLhs).g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < 10) ∧ (∀ Q ∈ errs, 10 ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ outs ++ errs, BAReach 10 (baPG baGGLhs) Q) ∧ ∫ ω, (baPG baGGLhs).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) := by
[599] example : ∃ outs errs : List (BAPGraph (Fin 2)), (∀ Q ∈ outs ++ errs, BAReach 3 ((baPG baPB).twist true true) Q ∧ Q.g.Normal ∧ ((baPG baPB).twist true true).g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ ((baPG baPB).twist true true).g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (((baPG baPB).twist true true).g.nA : ℤ) - ((baPG baPB).twist true true).g.nW) ∧ ∫ ω, ((baPG baPB).twist true true).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) := by
[609] example : ∃ outs errs : List (BAPGraph (Fin 2)), (∀ Q ∈ outs, Q.g.LocStd ∧ (baPG baGGLhs).g.scalingOrder ≤ Q.g.scalingOrder) ∧ (∀ Q ∈ errs, Q.g.scalingSize (1 / 4) 4 3 2 ≤ (4 : ℝ) ^ (-(10 : ℝ))) ∧ ∫ ω, (baPG baGGLhs).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) := by
$ grep -n applications of the targets in the instance module
(+10)   ⟨baLvl1ExistsStep_holds (baPG baGGLhs) (by decide) (by decide), baLvl1ExistsStep_holds _ normalB (by decide)⟩
(+18)   have hg := baLvl1StepGood_holds _ _ locStepB normalB Q hQ
(+20)     (BAReach.refl _).trans (BAReach.step _ _ Q _ (BAReach.refl _) (by decide +kernel) (by decide +kernel) locStepB hQ)
(+21)   have hn : Q.g.Normal := ba_lvl1_induction hr (fun R => R.g.Normal) normalB
(+22)     (fun A L hst hA B hB => (baLvl1StepGood_holds A L hst hA B hB).1)
(+23)   exact ⟨Q, hQ, hn, ba_lvl1_mu_lt (by decide +kernel) hg.2, hr⟩
(+32)   obtain ⟨outs, errs, h1, h2, h3, h4⟩ := baLvl1Lemma_holds 3 10 (baPG baGGLhs) (by decide)
(+43)   obtain ⟨outs, errs, -, -, h3, h4⟩ := baLvl1Lemma_holds 3 3 ((baPG baPB).twist true true) normalB
(+52)   obtain ⟨outs, errs, h1, h2, -, h4⟩ := baLvl1LemmaSize_holds 3 (1 / 4) (by norm_num) 2 10 (baPG baGGLhs) (by decide)
```

### Name-clash grep (new public names, main and the sibling and probe branches)
```
new public names:       25
== main (d5e9fa3): declaration lines with a new public name, over RBM3D/
== t/T2395 (4c1de4c): declaration lines with a new public name, over RBM3D/
t/T2395:RBM3D/Probe/T2395Pins.lean:275:def BAlvl1ExistsStep : Prop := ∀ {E : Type} (P : BAPGraph E), P.g.Normal → ¬ P.g.LocStd → ∃ outs, BALocStep P outs
t/T2395:RBM3D/Probe/T2395Pins.lean:281:def BAlvl1Lemma (d : ℕ) : Prop :=
== t/T2433 (b06b027): declaration lines with a new public name, over RBM3D/
== t/T2434 (6cccbdd): declaration lines with a new public name, over RBM3D/
== t/T2441 (4901a69): declaration lines with a new public name, over RBM3D/
== t/T2443 (e9528ea): declaration lines with a new public name, over RBM3D/
== t/T2444 (617661a): declaration lines with a new public name, over RBM3D/
== t/T2445 (23a4e69): declaration lines with a new public name, over RBM3D/
== files named BALvl1C* on main: 0
```

### Narrative: section map (iii), case table (iv), identity (v), lines (vi)
Result: targets 1-5 and the instances compile in `BALvl1C.lean`, 627 lines (31% of the 2,000 stop line; `BALvl1C2` not created); `wc -l` at the section commits (tool log): 446, 564, 627. No stop rule fired. No new `inductive`; `Test/Axioms.lean` and `RBM3D.lean` are unchanged on the branch; the full build's `#assert_rbm_axioms` passes with the temporary import. No (a′): nothing in (a) is corrected.
(iii) Section map (lines of `BALvl1C.lean` <- source; generic band | merged BA | new):
- §1 `47-71`: pins `BAlvl1ExistsStep`, `BAlvl1Lemma` (probe `T2395Pins.lean:275, 281-287`; body diff above is empty), `BAlvl1LemmaSize` (= `T2446_LemmaSize`).
- §2 `73-128` <- `LWLvl1` §13 `:3755-3809`: `BAReach.trans`, `ba_lvl1_induction`, `baLvl1Lt_wf`, `ba_lvl1_mu_lt`, the band proofs with the fifth component `nExt` (K3); merged `BALvl1Good` (`BALvl1B:63`).
- §3 `130-257` new, no band twin: twist transport of `atEdges` (a `map`), `atCharge` (a sign), `hwf`, `hnb`, `hbad`; `BALvl1C_end_in_atom`, `BALvl1C_atom_congr`.
- §4 `259-442` <- `lvl1_exists_step` `:3655-3735`. Generic: `lvl1_exists_split_fst`, `lvl1_split_two`, `lvl1_mem_split(_fst)`, `lwSymm_selector_edge`, `lwSymm_twist_out`, `lwSymm_twist_weight`. Merged BA: `BASymm2_frame_mem`, `_pair_mem`, `_frame_circ`, `BASymm1_twist_sameAtom`, `_intAtom`, `BALvl1B_atom_eq_of_mem`, `BAAtomic_sameAtom_iff(_iff_atom_eq)`, `BAAtomic_intAtom_iff`. New: `BALvl1C_pair_selector`, `BALvl1C_exists_{weight,within,edge,pair}`.
- §5 `444-547` <- `lvl1_exists_aux` `:3837-3880`, `lvl1_lemma` `:3907-3938`. Generic: `lvl1_choose_list`, `lvl1_sum_flatMap`, `owx_integral_list_sum`. Merged BA: `baLvl1StepIdentity_holds`, `baLvl1StepGood_holds`, `BALvl1A_integrable_val`, `_val_of_factor`, `_val_of_not`, `_reach_refl`. New: `BALvl1C_integrable_pval`, `BALvl1C_integral_comb`, private `BALvl1C_Ident`, `BALvl1C_aux`.
- §6 `549-560` <- `lvl1_lemma_size` `:4047-4071` (generic `lvl1_size_le`, `lvl1Cutoff` imported); §7 `562-623` instances.
(iv) Case table of target 2 as written (normal `P`, `¬ LocStd`; the case lemma at its line; `hwf` = no solid edge inside an atom):
| branch | constructor, selector `(c,t)` | hypotheses at `P.twist c t` |
|---|---|---|
| a self-loop `e` (`:278`) | `weight`, `(!σ, false)` | `p ∈ lwSplit`: `BASymm2_frame_mem`; `σ, circ, src = dst`: `lwSymm_twist_weight` and `Normal` |
| no self-loop, `e` with `sameAtom src dst` (`:294`) | `within`, `(!σ, false)` | `lwSymm_twist_out`; `sameAtom`: `BASymm1_twist_sameAtom`; `src ≠ dst` is the case hypothesis |
| `hwf`; internal atom, `atEdges ≠ []`, `len ≠ 2 ∨ charge ≠ 0` (`:312`) | `edge` at `e ∈ atEdges`, `x = u` its end in the atom, `lwSymm_selector_edge` | `hwf`: `BALvl1C_hwf_twist` (new); `hv`: `hwf` at the selected edge; `hint`: `BASymm1_twist_intAtom`, `BALvl1C_atom_congr`; `hbad`: `BALvl1C_hbad_twist` (new) |
| `hwf`, `hnb`; bad atom: `atEdges = [e1,e2]`, equal `σ`, ends `inr a`, `inr a'` in the atom, by `key` (`:339`) | `gg` (`a = a'`) or `ggSplit` (`a ≠ a'`); `BALvl1C_pair_selector` (new) | `BASymm2_pair_mem`; `BALvl1C_hnb_twist` (new); `hsame`: `BAAtomic_sameAtom_iff_atom_eq`; `j`: `List.mem_iff_getElem?`, `lwSymm_lwSplit_twistP` |
No case of `¬ LocStd` lacks a constructor. `baLvl1ExistsStep_holds` is at `:430`.
(v) Identity (`BALvl1C_aux :482-526`, strong induction `InvImage.wf (BALvl1Mu K) baLvl1Lt_wf`): `K ≤ ord`: `errs = [Γ]`; `LocStd`: `outs = [Γ]`; else `obtain ⟨L, hst⟩ := baLvl1ExistsStep_holds`, `hgood := baLvl1StepGood_holds`, then `lvl1_choose_list` with `ih Q (ba_lvl1_mu_lt hlt (hgood Q hQ).2)` (the spec contains the identity at all data). For the output lists: `rw [baLvl1StepIdentity_holds ..]` gives `∫ Γ.val = ∫ BAComb.val L`; `BALvl1C_integral_comb` turns both sides into list sums of `∫ Q.val` (integrability enters here, by `BALvl1C_integrable_pval`: `BALvl1A_val_of_factor` and `BALvl1A_integrable_val`, or `BALvl1A_val_of_not`); `List.map_append`, `lvl1_sum_flatMap` (for `fo`, `fe`), `List.sum_map_add`; for each `Q ∈ L` the identity of `hfo Q` read by `BALvl1C_integral_comb`. No pathwise rearrangement of `BAComb.val` is needed: the integrals are split, not the values. `baLvl1Lemma_holds` (`:532`) then carries normality, `ord`, `n_M`, `n_A - n_W` along `BAReach` by `ba_lvl1_induction` and `baLvl1StepGood_holds`.
(vi) Lines: the ticket expects 500-900 (T2395 priced 410/450/710); written 627, below the 1,500 split threshold and the 2,000 stop line.

## (c) Verified Mathlib and core names (all compiled in `BALvl1C.lean`, first line of use)
`Real.rpow_le_rpow_of_exponent_le` 617, `Real.rpow_neg_one` 618, `List.sum_map_mul_left` 170, `List.filter_map` 151, `List.filter_congr` 153, `List.exists_mem_of_length_pos` 316, `List.length_pos_iff` 316, `List.length_eq_two` 362, `List.length_eq_zero_iff` 361, `List.mem_iff_getElem?` 417, `List.getElem?_map` 419, `List.mem_flatMap` 506, `List.map_congr_left` 172, `List.sum_map_add` 522, `List.mem_filter` 173, `not_and_or` 350, `Bool.eq_false_or_eq_true` 245, `wellFounded_lt` and `WellFounded.prod_lex` (as `.prod_lex`) 103, `InvImage.wf` 486, `Prod.lex_def` 111, `integrable_zero` 463, `not_le` 498. Verified absent: none claimed.

## (d) Open issues and paper-delta candidates
- `RBM3D.lean`: the ticket lists it as writable; the branch does not edit it (the hub adds the import at merge, CLAUDE.md §3 (A) 4, as for T2443); the temporary import for the full build was restored from a copy (`git status --short` empty).
- Observation: the instances of targets 4 and 5 apply the theorems at concrete data (`d = 3, L = 4, W = 2`, `flowP_data`); the lists are existential (`lvl1_choose_list`), so `outs ++ errs ≠ []` is not exhibited by them. Section (a)'s script found 3 locally standard leaves at `baGGLhs`, `K = 2`.
- `d` is arbitrary (no `3 ≤ d` used); `3 ≤ L`, `BASelf`, `0 ≤ t < 1` are the pinned hypotheses of the identity (C1).
- Paper-delta candidate `T2446a`: the paper states the BA case only as "an analogue of `lvl1 lemma`" (`B_graphical_lemmas.tex:407`; the lemma is `7_8_light_weight.tex:392-399`). `BAlvl1Lemma`, `BAlvl1LemmaSize` are the pinned statements: atom-level `LocStd` and `ord`; lists independent of the data; `=_E` as one identity of integrals at the BA law `PF d L W 0` under `BASelf`, `0 ≤ t < 1`; "large `D`" as a real `D` at the cutoff `lvl1Cutoff c K0 d D`, constant `1`, in the window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`. No difference from the pins was found.
