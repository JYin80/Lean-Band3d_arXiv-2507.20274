Auditor model: claude-opus-5-5

# T2397 audit, round 2 (BA-L3b3 design gate G2; report only)

Written Sun Oct 11 02:47:05 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2397-audit2`, detached at `54ba7be` (`t/T2397`, merge-base `19fc8cf`). Inputs: ticket `docs/tickets/T2397.md`, **Amend 1** (binding), `docs/reports/T2397-design.md` (branch = main worktree copy), `docs/reports/T2397-prove.md` (incl. section Repair), merged `docs/reports/T2395-design.md` (`d859e60`), round-1 audit (overwritten by this file). Scratch: scratchpad `T2397/audit2/` (`build.log`, `ax.lean`, `inst.lean`, `rate.py`, `E13_seed2026.out`).

**Verdict: PASS** (no dispatcher sign-off needed). Round-1 defects D1 and D2 are repaired. Build, axioms, diff, sizes, statements/pins, the compiled instances, Amend 1 and paper-delta coverage all pass. The observations at the end are for the dispatcher's L4 REQ.

## 1. Build, axioms, diff, sizes (item 4)
```
$ lake build RBM3D.Probe.T2397Pins        # audit worktree; 285 warnings, 0 in T2397Pins.lean, 0 errors
info: RBM3D/Probe/T2397Pins.lean:383:0: 'RBM.Graph.T2397.ba_ord_ge_of_simC' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2397Pins.lean:385:0: 'RBM.Graph.T2397.inst_ba_ord_ge_of_simC_p2' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3390 jobs).
$ lake env lean ax.lean   # #print axioms of all 64 theorem/def/abbrev/inductive names of the probe (grep)
     63 [propext, Classical.choice, Quot.sound]
      1 none                         ('RBM.Graph.T2397.BAShape' does not depend on any axioms)
$ grep -cwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2397Pins.lean      -> 0
$ git diff --stat main...t/T2397
 RBM3D/Probe/T2397Pins.lean   | 385 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2397-design.md | 164 ++++++++++++++++++
$ diff <(git show t/T2397:docs/reports/T2397-design.md) docs/reports/T2397-design.md && echo same   -> same
$ wc -l: probe 385 (limit 400), design 164 (limit 300), prove 300 (limit 300)
```
PASS. Only the two sole writable files are touched, and no frozen file is touched. The probe stays on `t/T2397`.

## 2. D1 repair: the simulation is now up to relabelling (items 1-3)
- The literal `BAImgSim` (equality `img Q ∈ L'`) and everything built on it are gone (`grep -n BAImgSim` on the probe: only docstring line 128, "replaces the literal `BAImgSim`").
- **Successor `BASimC m T`** (probe 129) asks, for each tagged step `T P LT`, for a band graph `P'` and a band `LocStep m P' L'` with `P'` normal and `CircIffLoop`, and for two transfers: `locCostGeA far k P → P'.LocCostGe far k`, and for each `band` output `Q` some `R ∈ L'` with `R.LocCostGe far k → locCostGeA far k Q`. No packed-graph equality remains. The hypotheses of `locCostGe_locStep` are exactly what `baStep_of_simC` supplies:
```
@locCostGe_locStep : ∀ {m} {P} {outs}, LocStep m P outs → P.g.Normal → P.g.CircIffLoop →
  ∀ (far : Bool) (k : ℤ), PGraph.LocCostGe far k P → ∀ Q ∈ outs, PGraph.LocCostGe far k Q
```
- `ba_ord_ge_of_simC` (probe 148) has hypotheses `h0 : locReg6InvA p P0`, `BANormal`, `BASimC`, `∀ sh ≠ band, BAShapeLL sh T`, and `BAFinal (BReach …)`. All are explicit `Prop`s; no structure carries a hidden field. It is proved by `ba_ord_ge` ∘ `baStep_of_simC`, with no cycle.
- **Instance with every hypothesis discharged:** `inst_ba_ord_ge_of_simC_p2` (probe 364), at `p = 2`, `Γ_2 = fxyPowGraph 2`, strategy `liftStepT m 2`.
  - `BASimC` is discharged by `simC_liftStepT`, with `P' = P0`. `P0` is **not** `img (liftC P0)` (a different vertex type), so the pin works up to relabelling.
  - The shape pins hold because every lifted output is tagged `band` (`tag_liftStepT`).
  - `BAFinal` is discharged by `baFinal_lift`.
  - Auditor's nonvacuity checks:
```
$ lake env lean inst.lean        # exit 0, no output
example : locReg6InvA 2 (liftC (fxyPowGraph 2).pack) := (inst_ba_ord_ge_of_simC_p2 (mE 0) BReach.refl).1
example : ∃ LT, liftStepT (mE 0) 2 (liftC p2Graph.pack) LT :=
  ⟨_, _, _, lvl1_inst_locStep_weight, fxyPowGraph_locReg6Inv 2, rfl, rfl⟩            -- the step relation is inhabited
example (P0 : PGraph (Fin 2)) : (img (liftC P0)).E' = LGraph.ExtCls (promoteC (liftC P0).g) := rfl
```
  - `inst_step1_simC` (371) applies the instance after one merged Step 1 at `Γ_2`.
- Path half: `BASimP` (170) and `baPathStep_of_simP` (177) have the same shape. `BAPathLift` (355) remains in `inst_baPathStep_of_simP_p2` as a hypothesis. It is the map row's conservativity pin (T2395 R0 scope), not a degenerate premise. Band molecules use waved and `=`-dotted edges only (`LWVocab.lean:490-492`), so dropping and re-adding the `×`-edges in `promoteC` does not change molecules. See the observations.
- D1: **PASS.**

## 3. D2 repair: the S branch is T2395's S′ (items 1, 2)
```
$ git merge-base --is-ancestor d859e60 t/T2397 || echo "d859e60 not in branch"    -> d859e60 not in branch (T2395 read on main, as stated in design line 5)
$ sed -n 78p docs/reports/T2395-design.md | grep -o "For the G2 gate.*"
For the G2 gate (T2397 on `main`, P2): adopt S′; its new work is `ScostLL` for the BA-only shapes `S1`, `E1`, `E2` and the two macro intermediates.
$ sed -n 123p RBM3D/Probe/T2397Pins.lean
inductive BAShape | band | s1 | e1 | e2 | macroA | macroB
```
- **Shapes.** `BAShape` lists exactly the five shapes of T2395:78. T2395's `S2a` (T2395:37, :41) is the mirror of `S2b` "with the same invariants". In the auditor's reading of the term model (`steps.py` `ba_gg_terms`), `B1`, `B2` both have image `[y']→[y]` = band `R2`, so they are `band` outputs. Each shape has a `BAShapeLL` pin (134) and a `BAShapePath` pin (174).
- **Strategy.** Design line 1, §0, §2 (i)-(v) and §7 adopt S′ = S + K1-K4. They use `BALocStep` at atoms with priorities (1)-(3) (T2395:85), the macro steps K2(a)/(b) as single steps, and the `nExt` measure, used for termination only. (6) is an invariant along `BReach`.
- **Naming.** The first version's "S'" is renamed S+GG and argued to be subsumed by S′ (§2 (iii)): a GG pair with an edge inside an atom is an atom-level loop, and priority (1) removes it first (T2395:85 (1)).
- **Cost-step evidence at exactly these shapes** (E13): parents have at least one `M` edge; external `y`, `y'` are covered; merges across a parent edge are covered; 9,248,933 checks, 0 violations. Auditor's rerun at a fresh seed:
```
$ python3 r_shapes.py 3000 2026      # prover's script, seed not used by the prover
  S1 y,y' two atoms: both ext checks 304 violations 0 | one ext 430 v 0 | both int 60 v 0
  E1 [y] external 1,104 v 0 | internal 395 v 0;  E2 (GGGamma/lanlw/lweight) ext-ext and other: 18,795 checks v 0
  macro(a) P->intermediate 1,501 v 0, intermediate->stage 2 51,290 v 0; macro(b) intermediates 3,116 v 0, ->stage 2 75,279 v 0
  total checks 278,843, violations 0
  sensitivity (one waved edge dropped): S1 270/794, macro(a) 1,490/1,501, macro(b) 3,019/3,116 caught; E1 0/1,499 (slack 2)
```
- **Re-pricing** (§6, E14). The S′ rows L3b3′ + L3b4′ are 845 / 1,190 / 2,083, against T2395:150-151 (510 / 590 / 950). The +600 central difference is explained by four items: BA Lemma B, `BAInit`, the relabelling transfers in `BASimC`, and the atom-level final step. Auditor recompute from the E14 items (lo/hi = 0.71/1.75 × central):
```
L3b3p 575 810 1418 | L3b4p 270 380 665 | sum 845 1190 2083
```
- D2: **PASS.** The difference with T2395's pricing is stated with reasons. The dispatcher reconciles the two in the L4 REQ (ticket line 29).

## 4. Amend 1 / C1: κ uniform in L, rate at Λ = 𝔡⁻¹ = 10
```
$ python3 -I rate.py      # BAct_rate d Λ κ = min (log (1 + κ/(4dΛ))) (κ/2)   (BA/CombesThomas.lean:45)
g=0.01562  kappa=0.5    BAct_rate(3,10,k)=4.1580e-03  [Lambda=g: 2.5000e-01]  cutoff if c were the rate (p=2): 4810
g=1        kappa=0.25   BAct_rate(3,10,k)=2.0812e-03  [Lambda=g: 2.0619e-02]  cutoff if c were the rate (p=2): 9610
g=10       kappa=0.044  BAct_rate(3,10,k)=3.6660e-04  [Lambda=g: 3.6660e-04]  cutoff if c were the rate (p=2): 54556
g=10       kappa=0.04   BAct_rate(3,10,k)=3.3328e-04  [Lambda=g: 3.3328e-04]  cutoff if c were the rate (p=2): 60010
Im m(L=64)=0.0439 at g=10 vs kappa=0.044: False
$ sed -n 3991p RBM3D/Graph/LWLvl1.lean      # the cutoff's c is the Ψ-window exponent, not BAct_rate
    (hlow : (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) (hup : Ψ ≤ (W : ℝ) ^ (-c))
```
- Prove (a) row 10 uses κ = 0.5 / 0.25 / 0.04. These are uniform in L. At g = 10, 0.04 is below Amend 1's 0.044 and below `Im m(L=64)` = 0.0439, so it is conservative.
- Row 11 uses `BAct_rate(3, 10, κ)` = 4.158e-3 / 2.081e-3 / 3.333e-4, equal to the script above, with Λ = 10 and not Λ = g. The L = 4 values remain only as nonemptiness data, which Amend 1 allows.
- **Fixed-n closures that depend on κ or the rate: none.** (6), `scost` (6a:157), E5, E7 and E13 are counts with no `g`, κ, rate or ρ. `lvl1Cutoff` uses the window exponent `c = 1/4`. Even if `c` were the rate, the cutoff would be an n-independent finite constant (above), so it is not a failure.
- The atom truncation `B:317-319` fails at every value (prove (a) row 14), and the design does not use it (§5).
- **No REQ item.** C1: **PASS.**

## 5. Other targets (re-checked against the new probe and design)
- **P1** (design §1): the cited declarations stand at the lines given (6a:157/168/177/182/560/645/653/927, 6d:1077/1085/1107; probe build imports them). Unchanged since round 1. **PASS.**
- **P3** (`ba_ord_ge`, probe 95; instance `inst_ba_ord_ge_p2` 313, every hypothesis discharged at `p = 2`): unchanged since round 1. **PASS.**
- **P4** (19 Prop pins + `BALocReg`, 64 declarations compiled; table §4 with probe lines matching the file): **PASS.**
- **Row table** (twin 7,927 / 10,569 / 18,918, 8 rows after the split; S′ as in §3 above): **PASS.**
- **Line 1** gives the verdict on (6) under each branch, as the ticket's acceptance criterion requires: **PASS.**

## 6. Paper deltas (item 5)
The candidates are `T2397a`-`e` (design §7.3, prove (d)).
- `T2397a`: the atomic image keeps inside-atom edges (= T2395 K1).
- `T2397b`: `B:416` has no argument; reworded to "cost route on the image + five BA-only local lemmas".
- `T2397c`: `(eq:MolVW)` counts atoms.
- `T2397d`: the far corollary is read at atoms.
- `T2397e`: local standardness at vertex level vs atom level.

These cover every Lean/paper difference of the pins. The repair adds no new difference: the shapes are T2395's S′. None is in `docs/paper-deltas.md` yet (`grep -c T2397` = 0), as expected for candidates. **PASS.**

## 7. Per target
| target | verdict |
|---|---|
| build, axioms, diff, sizes | PASS |
| P1 band route | PASS |
| P2 under S′ (`ba_ord_ge_of_simC`, `BASimC`/`BASimP`, five shapes, map pins) | PASS (D1, D2 repaired) |
| P3 without S (`ba_ord_ge`, cost at atoms) | PASS |
| P4 pins | PASS |
| C1 / Amend 1 (κ uniform, rate at Λ = 10, fixed-n closures) | PASS, no REQ item |
| row table (twin, S′) | PASS |
| paper deltas | PASS |

## Observations (no RETURN; for the dispatcher's L4 REQ)
1. **Final step, vertex level vs atom level.** `BAFinal` and the second conjunct of `ba_ord_ge_of_simC` read vertex-level `locStdA`, but S′ stops at atom-level `BAGraph.LocStd` (T2395). The atom-level final step is neither compiled nor numerically checked here. It is priced (60 lines) in L3b4′ and disclosed in design §2 (v), prove Repair and `T2397e`. The invariant conjunct `locReg6InvA p Q` along all of `BReach` does not depend on this. The L3b4′ ticket should pin the final step at `BAGraph.LocStd`.
2. **`BASimC` is per step, `BAsim` is per output.** `BASimC` asks for one band `LocStep` per BA step for all `band` outputs. T2395's `BAsim` (`t/T2395` probe 263) has an existential per output. The design's row "BASimC from R1" therefore needs every band-tagged output of one BA step to be matched by one band step. E6 supports this ("of the same selection"), and the proof of `baStep_of_simC` would also accept the per-output form. The row ticket may pin either form.
3. **Lift instances and the BA-only shapes.** At the lift instances the BA-only shape pins hold vacuously (no `M` edge). Their content is E13, and the auditor's rerun reproduces it. `BAPathLift` (map row) is undischarged in `inst_baPathStep_of_simP_p2`.
4. **Two dependency statements differ.** T2395:156 says L3b3 "needs R1 and L3a5, not a BA cost argument". T2395:78 and this design give G2 a BA `ScostLL` for the five shapes, with start conditions L3b3′ after R0, L2c1, L2c2 and L3b4′ after L3a3, R1, L3b3′. The order to reconcile is in the REQ.
5. **Stale text in the prove report.** Prove (d) "Open (1) T2395 decides the selection rule (atom level, guard, or S')" is out of date: T2395 decided S′. Design §5 still says "κ from `Im m`", although the κ values actually used are the uniform constants of prove (a) row 10. Wording only.
