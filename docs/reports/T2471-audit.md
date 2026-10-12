Auditor model: claude-opus-5-5
# T2471 audit, round 1: P1b-1 (targets 1-3; `Chain/GridRepTailGen`, `Chain/GridRepTailGen2`), Mon Oct 12 21:07:17 UTC 2026

Scope: P1b-1 only (pre-signed split, H255 (4)). Targets 4-7 (the BA leaf, P1b-2) are not part of this audit and are not a defect.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2471-audit1`, detached at `t/T2471` = `d6f59884`; `main` = `8ea70675`.

## 1. Build (audit worktree)
```
$ lake build RBM3D.Chain.GridRepTailGen RBM3D.Chain.GridRepTailGen2
exit=0
Build completed successfully (3860 jobs).
$ grep GridRepTailGen build.log | grep -v "exceeds the 100"   (warnings of the new files other than line length)
⚠ [3859/3860] Replayed RBM3D.Chain.GridRepTailGen
⚠ [3860/3860] Replayed RBM3D.Chain.GridRepTailGen2
$ lake env lean docs/tickets/checks/T2471-check.lean   (on the branch)
exit=0   error lines: 0
```

## 2. Statements against the pin, axioms, auditor's examples (`aud.lean`)
`aud.lean` = `import RBM3D` + both new modules; `AUD_WTail2` is `T2471-check.lean:187-206` verbatim (renamed), `AUD_Ker` is the
check's Ker shape `:211-218` verbatim. Its examples:
```
example : @STGridWTail2gL = @AUD_WTail2 := rfl
example : @GridRepTailGen_Ker = @AUD_Ker := rfl
example : ∀ {d Flow mk T0}, GridRepTailGen_Hyp d Flow mk T0 → AUD_WTail2 d Flow mk T0 := @stGridWTail2gL_of
example : ∀ d : ℕ, RBM.Ind.GridRepWTailNAt d 2 ↔
    AUD_WTail2 d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
      (fun _ z n => lemT (z n)) := bandStep2_STGridWTail2
-- the ticket's band re-derivation 3 (c), not through gridRepWTailN_holds
example : RBM.Ind.GridRepWTailNAt 3 2 := (bandStep2_STGridWTail2 3).2 (stGridWTail2gL_of (gridRepTailGen_hyp_band 3))
example : ∀ d, RBM.Ind.GridRepWTailNAt d 2 := fun d => (bandStep2_STGridWTail2 d).2 (stGridWTail2gL_of (gridRepTailGen_hyp_band d))
#print axioms … ; #assert_rbm_axioms
```
```
$ lake env lean aud.lean
exit=0
'RBM.BA.stGridWTail2gL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandStep2_STGridWTail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_ker_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_inc_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_hyp_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailGenInst.inst_stGridWTail2gL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 13664 theorems, 4365 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: …
```
(The premise scan of `#assert_rbm_axioms` passes with both modules imported: `GridRepTailGen_Hyp`, `_Inc`, `_Zfields`, `_Yfields`
are concluded by the band theorems, so no registry line is needed; `Test/Axioms.lean` untouched, §4.)

Clause-4 check against the merged pin (`Chain/Step2Gen.lean:994`, `STGridRepNAtgL`, read in full): clause 4 has
`fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω`; target 2 has the same text with
`Mart n (i.1,b) k ω := Σ_{j'<k} martIncNg … j' i.1 ω b` (canonical `Mart`, ticket D2). Quantifier order
`κ ε 𝔡 → 𝔠 sz z → Flow → s t → D → ∃ CK → ∀ K → ∀ ε' → ∀ᶠ n → ∀ i` equals the pin's (CK before K, ε' after K). m = 2, `Q = ∅`.

## 3. Per target

**Target 1 (classes `GridRepTailGen_Ker`, `_Window`, `_Zfields`, `_Yfields`, `_Inc`, `_Hyp`).** `Ker` = check shape (rfl, §2).
The other shapes are not binding (ticket D2 "defaults"); delivered as in prove report (a′): `Window` = `t n < 1 ∧ (1-u)⁻¹ ≤ 16N`
(ticket: `(1-t)⁻¹ ≤ cN`, here c = 16); `Inc` = probability measure, adapted Hermitian `Hpath`, measurable `STeeMg`, a.e. split
`martIncNg = Z + Y` with Z mgf proxy `2 Re ΣΣ κκ̄ STeeMg_{u_{j+1}}(H_j)` and Y centred/L² with `Δ²·2000((Σ|κ|)C₂)²N⁸`, crude bound
`2N(16N)^6` and shift `12·16^7 N^8 (u'-u)` (band N-form); `Hyp` = `SizeTendsto ∧ ∀ᶠ n, Ker ∧ Window ∧ ∀ K, K n ≠ 0 → Inc`.
No hypothesis hidden in a structure (all are `def … : Prop` conjunctions read in full, File 1 l.54-131). Non-vacuity: every class is
discharged at the band carrier (target 3 (b)) and instantiated at concrete data (§4). **PASS.**

**Target 2 (`STGridWTail2gL`, `stGridWTail2gL_of`).** Statement = `T2471_WTail2` (rfl, §2); the only premise is
`GridRepTailGen_Hyp d Flow mk T0`; CK = `3 * D + 40` (File 2 l.629) = `9m + 3D + 22` at m = 2, as (a) row (i). Dependencies: merged
band privates by `open private` (`Path/DifREP3`) and copies under the stem; no cycle (imports §5). **PASS.**

**Target 3 (`bandStep2_STGridWTail2`, `gridRepTailGen_ker_band`, `gridRepTailGen_hyp_band`).** (a) is the check's iff shape
(compiled against `AUD_WTail2`, §2). (b) `gridRepTailGen_hyp_band d` has no premise (all `d`); `gridRepTailGen_ker_band` has the
single deterministic premise `|E n| ≤ 2`. This exceeds dispatcher answer (5) (`Ker` only): `Inc` is also discharged at the band
(`gridRepTailGen_inc_band`, premises `|E n| < 2`, `0 ≤ s n ≤ t n < 1`, `η_u ≥ 1/(16N)`). (c), re-added by the auditor per the
acceptance criteria, compiles for every `d` and does not go through `gridRepWTailN_holds` (§2). **PASS.**

## 4. Compiled nonempty instances (File 2 l.849-926, namespace `RBM.BA.GridRepTailGenInst`, `d = 3`)
Data: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_0 = 2097152`), `z0 n = 1/2 + i N^{-4/5}` (`Induction/Defs.lean:413`),
`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (`:435`), `sInst ≡ 0`, `tInst ≡ 1/16` (`:439-440`), `D = 1`, `ε' = 1/10`,
`K_n = ⌈N_n^CK⌉₊ + 1` (the pin's `K ≥ N^CK`; ticket item 7 fixes this form).
| endpoint | instance (line) | open hypotheses |
|---|---|---|
| `Ker` (T1), `gridRepTailGen_ker_band` | `example : ∀ n, GridRepTailGen_Ker (bandStep2Mat sz0 (STflowE z0)).toFlowFM n` (l.857) | none |
| `Window` (T1) | `example : ∀ n, GridRepTailGen_Window … tInst n` (l.863) | none |
| `Inc` (T1), `gridRepTailGen_inc_band` | `example : ∀ K n, GridRepTailGen_Inc … sInst tInst K n` (l.869) | none |
| `Hyp` (T1), `gridRepTailGen_hyp_band` (T3 b) | `example : GridRepTailGen_Hyp 3 …` (l.878) | none |
| `bandStep2_STGridWTail2` (T3 a) | `STGridWTail2gL 3 …` from `gridRepWTailN_holds 3 2`, and back (l.884, 888) | none |
| `stGridWTail2gL_of` (T2) | l.894 `GridRepWTailNAt 3 2` through T2 + T3 (b) + T3 (a); l.899 `theorem inst_stGridWTail2gL_band` at `sz0, z0, s ≡ 0, t ≡ 1/16, D = 1, ε' = 1/10, K_n = ⌈N^CK⌉+1` | none |
Window `s < t` not collapsed, `N_n ≥ 2097152`, no `N = 0`, empty index or `False` premise; all compile (§1). The T2 instance is at
the band since `Chain` files may not import `BA/*` (Layout); the BA instance is P1b-2's target 7.

## 5. Diff, frozen files, greps (`greps.sh`)
```
$ git diff --stat main...t/T2471
 RBM3D/Chain/GridRepTailGen.lean  | 795 +++++++++++++++++++++++++++++++++
 RBM3D/Chain/GridRepTailGen2.lean | 929 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2471Pins.lean       | 400 +++++++++++++++++
 3 files changed, 2124 insertions(+)
$ git diff --stat main...t/T2471 -- RBM3D/Path RBM3D/Induction RBM3D/BA RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/GridDuhamelGen.lean RBM3D.lean RBM3D/Test
(exit 0, empty)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^ *axiom " F1 F2 P
(exit 1)
$ grep T2474 public names (H257 (4)) in F1 F2 P
(exit 1)
$ grep -nE "^import" F1 F2
RBM3D/Chain/GridRepTailGen.lean:6:import RBM3D.Chain.GridDuhamelGen
RBM3D/Chain/GridRepTailGen.lean:7:import RBM3D.Path.DifREP3
RBM3D/Chain/GridRepTailGen2.lean:6:import RBM3D.Chain.GridRepTailGen
$ grep -rlE "import RBM3D.Chain.GridRepTailGen" RBM3D RBM3D.lean
RBM3D/Chain/GridRepTailGen2.lean
$ 8(a) grep -nE "sz\.lam|withLam|lam0|BAflowLam0" F1 F2
(exit 1)
$ 8(b) X1-C1 regex: F1 hits; F2 hit line range; section 10 header
24:`STeeUQM`, `etaT`, `zt E u` or `pathH` are copied and adapted under
F2 hits 38 first line 658 last line 914
652:/-! ## 10. Target 3: the band
$ 8(c) grep -nE "Ring\.inverse|Matrix\.of|cycProd|Ugen" F1 F2
(exit 1)
$ 8(d) grep -nE "STGridRepNgL|∀ m|\{m |\(m :" F1 F2
(exit 1)
RBM3D/Chain/GridRepTailGen.lean public 36 private 0
RBM3D/Chain/GridRepTailGen2.lean public 14 private 0
public names not starting with `GridRepTailGen_`:
STGridWTail2gL stGridWTail2gL_of bandStep2_STGridWTail2 gridRepTailGen_ker_band gridRepTailGen_eta_band gridRepTailGen_window_band
gridRepTailGen_zfields_band gridRepTailGen_yfields_band gridRepTailGen_inc_band gridRepTailGen_hyp_band inst_stGridWTail2gL_band
$ git grep -cE "GridRepTailGen|STGridWTail2gL|bandStep2_STGridWTail2|gridRepTailGen_|inst_stGridWTail2gL_band" main -- RBM3D RBM3D.lean
(exit 1)
```
Reading: all three files are sole writable files of the ticket (the probe as "1a only, never merged"). X1-C1 hits: F1 l.24 is the
module docstring; every F2 hit is at l.658-914, i.e. in §10 (target 3, the band bridge) and §11 (band instances), after the
generic part l.1-651. No `BA/*` import in a `Chain` file; no outside importer. H257 (4): none of T2474's public names is defined
(0 hits, the probe included). Files < 2,000 lines.

## 6. Paper deltas
The only Lean/paper statement difference in P1b-1 is the slot-count factor 2 in the `Z` proxy of `GridRepTailGen_Inc`
(`2 Re ΣΣ κκ̄ STeeMg`, a cut-count factor in place of the paper's literal `(𝓔⊗𝓔)` QV): covered by `docs/paper-deltas.md` D202
(`qvPropagatedN` with factor `k`, cut count). Target 2 is the pin's clause 4 (rfl) and target 3 (a) proves it equivalent to the band's
`GridRepWTailNAt d 2`, so it adds no new difference. The class constants (`16N`, `2N(16N)^6`, `12·16^7N^8`, `2000(…)²N⁸`) are
premises of a carrier-generic intermediate; they are not paper statements. No new candidate is needed; the prove report proposes none.

## 7. Observations (no statement, instance, build, axiom or delta effect)
- O1. Rule (E): the unpinned public helpers `gridRepTailGen_{ker,eta,window,zfields,yfields,inc}_band` carry the file stem in
  lowerCamel form, and `inst_stGridWTail2gL_band` sits in namespace `RBM.BA.GridRepTailGenInst`. 0 clashes on `main`.
- O2. For P1b-2 (not a defect here): `Hyp` asks for `Inc` for every `K` with `K n ≠ 0` on one eventual set in `n`, and `Inc`'s
  Q1/Q2 hold for every Hermitian `H`, not only path values. The BA discharge (target 4) must give exactly these uniform forms. Until
  target 4 exists, the classes are shown non-vacuous only at the band carrier.
- O3. Hub merge: `RBM3D/Probe/T2471Pins.lean` is in the diff but must not be brought into `main` (ticket: never merged).
  Root imports for the two `Chain` modules go after the last `import` line.

## Verdict
Target 1 PASS, target 2 PASS, target 3 PASS. **P1b-1: PASS.** No dispatcher sign-off needed.
