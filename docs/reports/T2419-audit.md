Auditor model: claude-opus-5-5

# T2419 audit (round 2, after the rule-(B) repair under Amend 1), Sun Oct 11 12:14:00 UTC 2026

Branch `t/T2419` at `0de3517`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2419-audit3` (detached; rule-(H) rerun of the
round-2 audit, the earlier attempt died on an API limit). Scratch: scratchpad `T2419/`. Checked: Amend 1 targets 1-3 and round-1 items.

## 1. Diff, hygiene, build, axioms

```
$ git diff --name-only main...t/T2419 ; git rev-parse --short t/T2419
RBM3D/Graph/BAExpandId.lean
0de3517
$ git diff main...t/T2419 -- RBM3D.lean | wc -l ; wc -l < RBM3D/Graph/BAExpandId.lean    # stop line 2,000
       0
     772
$ grep -nE "sorry|admit|native_decide|^\s*axiom |@\[implemented_by|extern" RBM3D/Graph/BAExpandId.lean
  7 hits, all the word "external" in docstrings (lines 29, 335, 488, 535, 634, 726, 746); no sorry/admit/axiom/native_decide
$ lake build RBM3D.Graph.BAExpandId 2>&1 | grep -E "error|warning: .*BAExpandId|Build completed|sorry"
Build completed successfully (3911 jobs).
$ lake env lean docs/tickets/checks/T2419-check.lean >/dev/null 2>&1; echo "check exit $?"   ->   check exit 0
$ lake env lean ax.lean          # #print axioms
'RBM.Graph.baExpFrame_gg_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandId_gg_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandId_star_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandId_data_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baRCand_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baSelClassical_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BARCand.kids_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BARCand.kids_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baExpandIdentity_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.instCand_sizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.instCandRed_sizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baG5Graph_partition_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_gg_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_identity_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_kids_normal_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.baExpandId_inst_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.instPRed_selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandIdInst.instP_selected' depends on axioms: [propext, Classical.choice, Quot.sound]
$ for n in baExpFrame_gg_red BARCand BAexpand ... BAExpandId_flip; do git grep -lw $n main -- 'RBM3D/*.lean' RBM3D.lean | wc -l; done
baExpFrame_gg_red:0 BARCand:0 BAexpand:0 BAexpandRoot:0 BAselClassical:0 baG5Graph:0 BAG5Identity:0 baExpandIdentity_holds:0 BAExpandIdInst:0 BAExpandId_flip:0
```
Only the sole writable file is touched; no merged file (`LWExpTerm5`, `BAGGOp`, ...) is edited, so no frozen signature changes.

## 2. Target 1 (ticket): `baG5Graph`, `BAG5Identity` against the probe pin

```
$ git show t/T2398:RBM3D/Probe/T2398Pins.lean > probe.lean; (extract block to blank line, docstrings dropped; diff)
def baG5Graph: probe        9 file        9 diff        0
def BAG5Identity: probe        5 file        5 diff        0
```
Binders: `∀ L W [NeZero L] [NeZero W], 3 ≤ L → ∀ g0 E t m, BASelf d L g0 E m → 0 ≤ t → t < 1 → ∀ k s x y`, law `PF d L W 0`,
data `BAlwData`. C1 holds (no smallness of `g0`, no scalar `m`). **PASS** (unchanged from round 1).

## 3. Amend 1 target 1: the red-charge identity `baExpFrame_gg_red` (`:267`)

Statement script: the text of `baExpFrame_gg_red` with `σ = false ↦ σ = true`, `BAExpandId_gg2r/gg4r Γ p q ↦ Γ.gg2/gg4 p q`
against the merged `baExpFrame_gg` (`Graph/BAGGOp.lean`), whitespace-normalised:
```
blue: theorem baExpFrame_gg (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m
  → 0 ≤ t → t < 1 → ∀ {Ex Ix : Type} [...] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2,
  p.1.σ = true → p.1.circ = true → q.1.σ = true → q.1.circ = true → p.1.src = q.1.dst → ∫ ω, Γ.val (BAlwData ...) ℓe ∂(PF d L W 0) =
  ∫ ω, baSum (Γ.gg2 p q) (BAlwData ...) ℓe + baSum (Γ.gg4 p q) (BAlwData ...) ℓe ∂(PF d L W 0) := by
red(subst) vs blue diff lines:        0
```
So the red identity has exactly the blue hypotheses (same binders, law, data, C1) with both edges red, and the lists
`BAExpandId_gg2r Γ p q := ((flip Γ).gg2 (flipP p) (flipP q)).map flip` (likewise `gg4r`), i.e. the conjugated output lists.

Proof route (Lean-checked, no external input): `BAExpandId_star_val : star (Γ.val D ℓe) = (flip Γ).val D ℓe` for any `D` with
real `S` and Hermitian `gPsi`; `BAExpandId_data_real` discharges both for `BAlwData` (`BAlwS = t·svarF`; `PsiI_isHermitian`); then
`baExpFrame_gg` at `flip Γ` and `integral_conj` twice. The law `PF d L W 0` is not transformed (Amend 1: "conjugate the identity in
expectation directly"; the report says which). The conjugation matches the merged carrier conventions:
```
$ grep -A4 "^def SEdge.val\|^def WEdge.val" RBM3D/Graph/LWVocab.lean
def SEdge.val ... := let g : ℂ := D.G (ℓ e.src) (ℓ e.dst) - if e.circ then D.M ... else 0 ;  if e.σ then g else star g
def WEdge.val ... := if e.col then (if e.σ then D.Sp (ℓ e.x) (ℓ e.y) else star (D.Sp (ℓ e.y) (ℓ e.x))) else D.S (ℓ e.x) (ℓ e.y)
```
(`flipS` toggles `σ`; `flipW` toggles `σ`, swaps endpoints of a coloured edge.) Amend 1 stop rule not triggered. **PASS.**

## 4. Amend 1 target 2 / ticket target 2: `BARCand` with charge, `kids`, `kids_identity`, `kids_normal`

`BARCand P` (`:348`) fields: `σ : Bool`, `v`, `p`, `q`, `hp : p ∈ lwSplit P.g.solid`, `hq : q ∈ lwSplit p.2`, `hpσ : p.1.σ = σ`,
`hpc`, `hqσ : q.1.σ = σ`, `hqc` (circled), `hpv : p.1.src = v`, `hqv : q.1.dst = v`. This is the paper's step: "a vertex incident to
two solid edges of the same charge (two `G` edges or two `Ḡ` edges)" (`B_graphical_lemmas.tex:151, 391`), and agrees with the
design's charge-symmetric `HasGGCand` (probe 77-79); `baRCand_nonempty_iff` (`:387`) states exactly `p.1.σ = q.1.σ` (either charge).
`v` may be external or internal: `GGGamma` (`B:396-398`) has `x` free, not summed, so no restriction is lost.
`kids` (`:364`) = packed partitions of `BAExpandId_ggL2/ggL4 c.σ` (blue merged lists for `σ = true`, `gg2r/gg4r` for `false`).
`BARCand.kids_identity` (`:537`): hypotheses `3 ≤ L`, `BASelf`, `0 ≤ t`, `t < 1`, `c`, `x y`; conclusion
`∫ P.val ... ![x,y] = Σ_{r ∈ c.kids} ∫ r.2.val ...`; it calls `BAExpandId_gg_identity ... c.σ` (`:320`, case split onto
`baExpFrame_gg` / `baExpFrame_gg_red`), so it covers both charges with the statement unchanged from round 1. `kids_normal` (`:403`)
by `partition_normal`. The round-1 defect (blue-only step) is removed. **PASS.**

## 5. Ticket target 3: `BAexpand`, `baExpandIdentity_holds` (`:589`)

`BAexpand sel fuel := expandG (BAstep sel) fuel`, `BAstep sel P = (sel P).map BARCand.kids`; `BASel` ranges over candidates of
either charge. `baExpandIdentity_holds (d) (sel : BASel) (fuel) : BAG5Identity d (BAexpandRoot sel fuel)` via imported
`expandG_sum` with `Inv := Normal`, `w := fun _ => 1`. Holds for every selector and fuel; `LWG5Progress` not claimed (as pinned).
**PASS.**

## 6. Vacuity, hidden hypotheses, cycles

- `BAG5Identity`, `baExpFrame_gg_red` are explicit Props; `BASelf` is satisfiable (`BAExpandInst.baSelf_zero : BASelf 3 3 0 0 I`, merged).
- `BARCand` fields are the candidate's defining combinatorial data, discharged by `simp`/`rfl` at both instances; no structure
  carries an analytic hypothesis. `hS`/`hP` of `BAExpandId_star_val` are discharged for `BAlwData` by `BAExpandId_data_real`.
- Dependencies merged (`baExpFrame_gg`, `val_eq_partition`, `partition_normal`, `expandG_sum`, `PsiI_isHermitian`, `open private`); no cycle; no external hypothesis.

## 7. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 1`, `g0 = 0`, `E = 0`, `m = i`, `t = 1/2`)

| endpoint | instance | discharged | nondegenerate |
|---|---|---|---|
| `kids_identity` (blue) | `baExpandId_inst_kids_identity` | `3 ≤ 3`, `0 ≤ 1/2 < 1` (`norm_num`), `baSelf_zero`, `instCand` | 5 solid, 2 waved, `I' = Fin 3`; gg2/gg4/kids = 8/5/63 (`instCand_sizes`, `decide`) |
| `kids_identity` (red) | `baExpandId_inst_kids_identity_red` | same, `instCandRed` (`σ := false`) | all 5 solid edges red; gg2r/gg4r/kids = 8/5/63 (`instCandRed_sizes`, `decide`) |
| `baExpFrame_gg_red` | `baExpandId_inst_gg_red` | as above + `hp`, `hq`, five `rfl` | graph `baG5CircRed`, all labels `ℓe` |
| `kids_normal` (both) | `baExpandId_inst_kids_normal(_red)` | none needed | same candidates |
| `baExpandIdentity_holds` | `baExpandId_inst_identity` (fuel 1), `example` (fuel 2) | as above | root partition 32 terms (`decide`); `BAselClassical` selects (`instP_selected`, `instPRed_selected`) |

All compile (build of §1). `Idx 3 3 1` has 27 points, `t` interior, no empty index, no `False` premise. **PASS.** Amend 1 target 3
(one instance at a red candidate) is met by the red rows.

Observations (no RETURN): the fuel-1/2 root instance takes blue steps only (`baG5Graph k s` has at most one red solid edge); the
red step is exercised at `instCandRed` (Amend 1 target 3). The one-step instance uses `baG5Circ`, as in round 1.

## 8. Paper deltas

- T2419a (round 1, blue-only reading) is withdrawn in prove report (d): the Lean step now has both charges, matching the paper.
- T2419b proposed (prove report (d)): `GGGamma` (`B:393-405`) displays only the blue form; Lean takes the red form as its complex
  conjugate (`baExpFrame_gg_red`, coloured waved `S⁺_{xβ} ↦ S⁻_{βx}`, `M ↦ M̄`, conjugated lists). This is the only remaining
  Lean/paper statement difference. `grep -n T2419 docs/paper-deltas.md` is empty, as expected before merge. Coverage: **PASS**.

## Round-1 items

Item 1 (dispatcher decision): done, Amend 1 decision (b). Item 2 (charge in candidate, red identity, extensions, red instance,
build/axioms/instances re-run): done, §3-§7.

## Verdicts

| target | verdict |
|---|---|
| ticket 1. `baG5Graph`, `BAG5Identity` | PASS (0-line diff against probe pin) |
| ticket 2 / Amend 2. `BARCand` (with `σ`), `kids`, `kids_identity`, `kids_normal` | PASS |
| Amend 1. `baExpFrame_gg_red` | PASS (0-line diff against the merged blue statement after the charge/list substitution) |
| ticket 3. `BAexpand`, `baExpandIdentity_holds` | PASS |
| ticket 4 / Amend 3. instances (blue and red) | PASS |
| ticket 5. C1 | PASS |
| ticket 6. registry, build, axioms, diff, size (772 vs stop line 2,000) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
