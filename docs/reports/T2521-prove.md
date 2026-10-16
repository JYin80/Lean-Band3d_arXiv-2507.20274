Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct 16 14:14:15 UTC 2026

Sources read: `docs/tickets/T2521.md`, `docs/tickets/checks/T2521-check.lean`, `RBM3D/Main/BandTerminal.lean` (whole), `RBM3D/BA/MAPins.lean:90-130, 205-225`, `RBM3D/Defs/Sizes.lean:138-182, 255-335`, `RBM3D/BA/UNPins.lean:776-890`, `RBM3D/Endpoints.lean:537-620`, `docs/tickets/T2520.md` (targets 6-7, Decision (12)), `docs/tickets/checks/T2520-pins.lean:215-226`, `docs/reports/T2520-prove.md`, `docs/queue/CONTROL.md` H327-H328 (hub compile of `T2521-check.lean` on `main` a925870b: exit 0, no error lines, as CONTROL H328 (2) records).

### (i) Exponent table

No new constant, exponent or threshold: every conjunct of `final_shape` is a merged theorem (`band_terminal`, `Main/BandTerminal:104`) or N2's `baThm27L_three` (T2520, not merged). The instance data the compiled instances of target 4 read are listed with their source lines.

| datum | value | constraint | slack / source |
|---|---|---|---|
| `d` | 3 | `3 ≤ d` (`le_rfl`) | `Endpoints:556-606`, `MAPins:213-224` |
| `(𝔠, 𝔡)` | `(1/6, 1/10)` | `Admissible`: `0<𝔠`, `0<𝔡`, `SizeTendsto`, `W ≥ N^𝔠` eventually, `(eq:WO)` `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` eventually (`Defs/Sizes:164-178`) | at `d=3`, `𝔡=1/10`: `W^{-7/5} ≤ lam ≤ 10`; script below |
| band size `sz0` | `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}` | `sz0_admissible` (`Defs/Sizes:331`) | `W ≥ N^{1/6}` since `N ≤ W^6` (`sz0_size_le_W_pow`, `Defs/Sizes:280`); `lam` slack at `n=0`: `1/64` vs `W^{-7/5}=1/128` (factor 2) |
| BA size `S0 = clsS 4 (3/10) = clsSz 4 g0` | `L=4`, `W=(2(n+1))^5`, `lam=g0 ∈ (0, 3/10]` (`FlowPt.g0_pos`, `g0_le`, `BA/MFixedPoint:877-882`) | `S0_adm` (`BA/UNPins:887`) via `clsSz_admissible` (`UNPins:846`) for `0<g0≤10`; WO lower half needs `n ≥ ⌈1/g0⌉` (`clsSz_WO`, `UNPins:821`) | `g0 ≤ 3/10 ≤ 10` slack `9.7`; the value `g0` of the flow point is not computed here; the script checks several `g0` |
| band instance args | decol `(κ,τ,D)=(1/10,1/10,1)`; locSC, QDiff `(κ,ε,τ,D)=(1/10,1/20,1/10,2)`; QUE `(κ,ε₀,c,τ)=(1/10,1/30,1/60,1/10)`; BUniv `k=1`, `E=0`, `𝒪=bump` | all `>0`; QUE: `0<ε₀<𝔡/2=1/20`, `0<c<ε₀`, `c<𝔡/5=1/50` | `ε₀`: slack `1/60` to `1/20`; `c`: slack `1/300` to `1/50` (`Endpoints:537-545`, `inst_*` `:561-600`) |
| BA instance args | `κ_*=clsκ 4 (3/10)=Im m₀/π>0`; decol `(τ,D)=(1/10,1)`; locSC, QDiff `(ε,τ,D)=(1/20,1/10,2)`; QUE `(ε₀,c,τ)=(1/30,1/60,1/300)`; BUniv `k=1`, `E_*=(fp 4 _).E` (`S0_bulk`), `E'=0`, `𝒪=bump` | all `>0`; `τ_Q=1/300 < 1/150` | `MAPins:213-224` (argument lists to copy) |
| `UNL32` | borrowed, LSY arXiv:1609.09011 Thm 2.2 (`Universality/Pins:281`) | the single external hypothesis of `final_shape` | n/a |

The check's text `T2521_FinalShape` is `UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ BAThm27L 3`; its band half is the exact type of `band_terminal` (the check's `example`, hub compile exit 0). `BAThm27L d := BAEnd_decolL d ∧ BAEnd_locSCL d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ BAEnd_QDiffL d` (`MAPins:126-127`), the order of `band_terminal`.

External hypothesis `UNL32` (TEAM §8 lesson 14): it enters only as the premise of the merged `band_terminal` and of N2's `baThm27L_three : UNL32 → BAThm27L 3`; the 1a has no limit computation of its own to make (no new hypothesis, no new constant). `final_shape` adds no hypothesis beyond `UNL32`.

### (ii) Concrete nondegenerate instance

`d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`; band on `sz0`, BA on `S0` (`L=4`, `W_n=(2(n+1))^5`, `lam=g0`). The script prints both sequences at `n = 0, 10`, checks `W ≥ N^{1/6}` and `W^{-7/5} ≤ lam ≤ 10` (`Admissible`'s two eventually clauses; `SizeTendsto` is `N_n ≥ n`, merged), the argument ranges of the instances, and, for `S0`, the eventually-threshold `⌈1/g0⌉` of `clsSz_WO` at `g0 ∈ {3/10, 1/100}` (`g0` of the flow point is `∈ (0, 3/10]`, not computed).

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d6ebe5cd-b9c4-4c2a-9b3c-fa912982a931/scratchpad/T2521/inst.py
sz0 n=0: L=4 W=32 N=2.0972e+06 lam=1.5625e-02 W^-1.4=7.813e-03 Bandwidth=True WO=True
sz0 n=10: L=44 W=5153632 N=1.1660e+25 lam=8.8199e-09 W^-1.4=4.009e-10 Bandwidth=True WO=True
S0[g0=0.3] n=0: L=4 W=32 N=2.0972e+06 lam=3.0000e-01 W^-1.4=7.813e-03 Bandwidth=True WO=True
   n>=ceil(1/g0)=4: False -> Admissible parts hold: True
S0[g0=0.3] n=4: L=4 W=100000 N=6.4000e+16 lam=3.0000e-01 W^-1.4=1.000e-07 Bandwidth=True WO=True
   n>=ceil(1/g0)=4: True -> Admissible parts hold: True
S0[g0=0.3] n=10: L=4 W=5153632 N=8.7603e+21 lam=3.0000e-01 W^-1.4=4.009e-10 Bandwidth=True WO=True
   n>=ceil(1/g0)=4: True -> Admissible parts hold: True
S0[g0=0.01] n=0: L=4 W=32 N=2.0972e+06 lam=1.0000e-02 W^-1.4=7.813e-03 Bandwidth=True WO=True
   n>=ceil(1/g0)=100: False -> Admissible parts hold: True
S0[g0=0.01] n=10: L=4 W=5153632 N=8.7603e+21 lam=1.0000e-02 W^-1.4=4.009e-10 Bandwidth=True WO=True
   n>=ceil(1/g0)=100: False -> Admissible parts hold: True
S0[g0=0.01] n=100: L=4 W=336323216032 N=2.4347e+36 lam=1.0000e-02 W^-1.4=7.287e-17 Bandwidth=True WO=True
   n>=ceil(1/g0)=100: True -> Admissible parts hold: True
QUE: 0<e0<dd/2: True  0<c<e0: True  c<dd/5: True  tau>0: True
band args: kappa=1/10>0, locSC/QDiff (eps,tau,D)=(1/20,1/10,2), decol (tau,D)=(1/10,1)>0; BA args: (1/20,1/10,2),(1/30,1/60,1/300),k=1,E'=0 >0: True
BA 3/10>0: True  g0<=3/10<=10: True
```

The `L ≥ 3`, `W ≥ 1` fields hold (`L=4`, `W ≥ 32`). `n = 0, 10` sizes are moderate (`N ≈ 2e6, 1e25`); no `N = 0`, no empty index set, no collapsed window. The compiled instances are `Inst.inst_*` (band, `Endpoints:561-600`) and the `MAPins:213-224` lines (BA); only `UNL32` stays a hypothesis.

### Decision (4): which case applies

The fallback of N2 did not fire. `docs/reports/T2520-prove.md:46`: "The fallback (`BAThm27L 3` to MA-06b) is not needed: the total landed forecast 1,106 is under 1,950 with it kept in N2"; `:199`: the 1a moves no pin and `1a-audit needed: no`. `docs/queue/T2520.state`: `held` (1b not started; probe commit `82ef67a8` on `t/T2520`, never merged). The probe has `T2520_baThm27L_three ... : UNL32 → BAThm27L 3` (`git show t/T2520:RBM3D/Probe/T2520Pins.lean:168`), and `docs/tickets/checks/T2520-pins.lean:223` `T2520_Thm27Three : Prop := UNL32 → BAThm27L 3`. So Decision (4)'s first case does not apply: target 2 is `baThm27L_three` by name (once T2520 has merged); nothing is assembled in T2521 from `baEnd_*_three`. As of `main` a925870b, `baThm27L_three` is absent from `RBM3D/` (grep `baThm27L_three|final_shape|Thm27_of_L32|Thm27\b` gives only comments at `BA/UNPins:753` and `Main/QUEFromQDiff:42`), so no name clash for `Thm27`, `Thm27_of_L32`, `final_shape`.

### Verdict

- Target 1 `Thm27`: PASS (a `def` over the merged `BAThm27L`, `MAPins:126`).
- Target 2 `Thm27_of_L32`: PASS, conditional on N2's `baThm27L_three : UNL32 → BAThm27L 3` merged with exactly the type of `T2520_Thm27Three` (ticket stop rule); not on `main` yet, 1b waits for T2520.
- Target 3 `final_shape`: PASS (band half is `band_terminal` at its exact type; BA half is target 2).
- Target 4 instances: PASS (arguments as `Inst.inst_*` and `MAPins:213-224`, ranges checked above).
- Target 5 greps and axioms: n/a at 1a.

1a-audit needed: no. The 1a moves no text: the `T2521_*` texts of the check are used unchanged, no pin, constant or stop line changes, N2's fallback did not fire, and no new constant exists.

## (b) Script output — Fri Oct 16 19:50:18 UTC 2026

```
$ git log --oneline -3 --first-parent  (branch t/T2521 after merging main, whose head is 9d2b0883)
  e4cfe86f T2521: whole-final_shape instance covers all ten conjuncts
  91db6aa9 T2521: final shape (Thm27, Thm27_of_L32, final_shape) and instances
  9d2b0883 T2520: merge M/N N2 Universality/PinsKD, GUEPhase/RandomLayerBGD, BA/UNBUniv (probe stays on the branch)
$ lake build RBM3D.Main.FinalShape   (tail)
Build completed successfully (4427 jobs).
$ lake build   (full, with a temporary uncommitted `import RBM3D.Main.FinalShape` in RBM3D.lean, then reverted; tail)
Build completed successfully (4443 jobs).
$ lake build   (full, committed tree; hub adds the root import at merge)
Build completed successfully (4442 jobs).
$ git diff --stat main...t/T2521
 RBM3D/Main/FinalShape.lean | 120 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 120 insertions(+)
$ lake env lean ax.lean
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -c "STStep5IIIgL\|UNMLOutBA\|UNLocAvgBA\|UNQueBA" ax.out  (the output of the two #check lines and the axiom lines)
0
$ #check @final_shape / Thm27_of_L32
RBM.Endpoints.final_shape : RBM.Univ.UNL32 →
  (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
    RBM.Endpoints.Thm27
RBM.Endpoints.Thm27_of_L32 : RBM.Univ.UNL32 → RBM.Endpoints.Thm27
$ sed -n 36,45p RBM3D/Main/FinalShape.lean   (targets 1-3 as in the file)
def Thm27 : Prop := RBM.BA.BAThm27L 3
theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_three
theorem final_shape : RBM.Univ.UNL32 →
    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27 := fun h32 =>
  ⟨band_terminal h32, Thm27_of_L32 h32⟩
$ grep -rn -E "Thm27|Thm27_of_L32|final_shape|FinalShape_hg" RBM3D (outside the new file)
RBM3D/BA/UNPins.lean:753:`inst_cls_Thm27*`, `inst_cls_gaps/odd/interval`, which need T2161's glue pin `BAThm27
RBM3D/Main/QUEFromQDiff.lean:42:* Consumers: MA-06 (`band_endpoints_of_pins`, `final_shape` with `hQ := QUE_of
$ grep -n "sorry|admit|native_decide|^axiom" RBM3D/Main/FinalShape.lean
(no match)
$ grep -n "^example" RBM3D/Main/FinalShape.lean  (target 4, all `UNL32` the only hypothesis)
59:example (h32 : UNL32) :=
63:example (h32 : UNL32) :=
67:example (h32 : UNL32) :=
71:example (h32 : UNL32) :=
75:example (h32 : UNL32) :=
84:example (h32 : UNL32) : True := by
98:example (h32 : UNL32) : True := by
```

Check file (ticket acceptance): the check with line 11 import and the line-50-53 block activated, plus examples
`T2521_FinalShape := final_shape`, `T2521_Thm27OfL32 := Thm27_of_L32`, `T2521_Thm27 = Thm27 := rfl`, compiled with
`lake env lean` in the worktree: exit 0, no error lines (scratch copy; the ticket check file is untouched). So targets 1-3 equal the `T2521_*` texts at exact type.

Instances (target 4): lines 59-75 each conjunct of `(final_shape h32).1` at `Inst.inst_*` (data `sz0`, d = 3, (c,d) = (1/6,1/10), as `BandTerminal` §Instances); lines 84-95 the five BA conjuncts of `(final_shape h32).2` at `S0`, `κ_* = clsκ 4`, `E_*` = `(fp 4 _).E` (`S0_bulk`), arguments copied from `BA/MAPins:213-224`; lines 98-114 the whole `final_shape h32` at all ten conjuncts at once. Every deterministic hypothesis is discharged; `UNL32` is the only hypothesis. The helper `FinalShape_hg : 0 < 3/10` is `private` (`UNPins_hg_3_10` is private in `BA/UNPins`, `MAPins_hg` in `BA/MAPins`).

Narrative: Decision (4) first case did not apply (see (a)); `Thm27_of_L32` is `baThm27L_three` by name; its type on `main` equals the `T2521_Thm27OfL32` text (the activated check example above elaborates). No hypothesis beyond `UNL32`; no merged statement changed; no registry line needed: the full build with the temporary root import passed `#assert_rbm_axioms` and the premise scan without an edit to `RBM3D/Test/Axioms.lean`. `#print axioms band_terminal` on `main` (main worktree, same command) is the standard three, equal to the branch output above.

## (c) Verified names
- `RBM.BA.baThm27L_three : UNL32 → BAThm27L 3` (`BA/UNBUniv:281`, on `main` 9d2b0883), checked by `#check` above.
- `RBM.Endpoints.band_terminal`, `Inst.inst_decol/locSC/QUE/BUniv/QDiff`, `RBM.BA.UNPinsInst.S0/S0_adm/S0_bulk/clsκ/clsκ_pos/fp`, `RBM.Univ.BAInst`, `RBM.Univ.UNInst.bump/bump_testFun`: all used in the compiled file.
- Absent/verified: no pre-existing `Thm27`, `Thm27_of_L32`, `final_shape` in `RBM3D/` (grep above: only comments).

## (d) Open issues and paper-delta candidates
- None. No paper-delta candidate `T2521a`: the assembled statement is `1_2:644-655` at `d = 3` (D723) with the borrowed `UNL32`.
- The file triggers the style-linter header warning (`set_option` before the module docstring), as other files do; no effect on acceptance.
- Not done here (ticket): N2's targets, M/N closing REQ, release clean-up, root import (hub at merge).
