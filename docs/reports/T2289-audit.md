Auditor model: claude-opus-5-5

# T2289 audit (round 1) — LW-13c, `RBM3D/Graph/LWMomExpFar.lean`

Written Tue Oct  6 11:58:56 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2289-audit1`, detached at `t/T2289` = `dee5e6e`.
Targets: `lwMomExpFar_head : ∀ d, AnpFarHead d`, `lwMomExpFar_and : ∀ d, AnpFarAnd d`, `lwMomExpFar_auxOwn : LWAuxNestedOwn`.

## 1. Statement against the pin (check file section 2, renamed vocabulary)
```
$ sed -n '94,150p' docs/tickets/checks/T2289-check.lean | grep -v '^ *--\|^/--\|^`\|-/$' \
    | sed 's/\bfarDAnd\b/lwMomExpFar_farDAnd/g; s/\bownExt\b/lwMomExpFar_ownExt/g; s/\bHeadFar\b/lwMomExpFar_HeadFar/g' > pin.txt
$ sed -n '40,104p' RBM3D/Graph/LWMomExpFar.lean | grep -v '^ *--\|^/--\|^`\|-/$' > lean.txt
$ diff -w pin.txt lean.txt
1c1
< def farDAnd (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
---
> def lwMomExpFar_farDAnd (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
5c5
< def ownExt {p q : ℕ} (Γ : NGraph p q) : Prop :=
---
> def lwMomExpFar_ownExt {p q : ℕ} (Γ : NGraph p q) : Prop :=
9c9,12
< def HeadFar (d L : ℕ) [NeZero L] {p q : ℕ} (Γ : NGraph p q) (a : Fin p → Zd d L) (ℓ : ℝ)
---
> instance lwMomExpFar_ownExt_dec {p q : ℕ} (Γ : NGraph p q) : Decidable (lwMomExpFar_ownExt Γ) := by
>   unfold lwMomExpFar_ownExt; infer_instance
> 
> def lwMomExpFar_HeadFar (d L : ℕ) [NeZero L] {p q : ℕ} (Γ : NGraph p q) (a : Fin p → Zd d L) (ℓ : ℝ)
20c23
<         ∀ (a b : Fin p → Zd d L) (S : Finset (Fin q → Zd d L)), HeadFar d L Γ a ℓ S →
---
>         ∀ (a b : Fin p → Zd d L) (S : Finset (Fin q → Zd d L)), lwMomExpFar_HeadFar d L Γ a ℓ S →
26c29
<   ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → ownExt Γ → AnpFarHeadAt d Γ
---
>   ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → AnpFarHeadAt d Γ
35c38
<           Γ.valOn ξ a b (Fintype.piFinset fun _ : Fin q => farDAnd d L a b ℓ) ≤
---
>           Γ.valOn ξ a b (Fintype.piFinset fun _ : Fin q => lwMomExpFar_farDAnd d L a b ℓ) ≤
40c43
<   ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → ownExt Γ → AnpFarAndAt d Γ
---
>   ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → AnpFarAndAt d Γ
45c48,49
<     ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ ownExt Γa ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
---
>     ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧
>       Γa.ordN = LGraph.auxOrd Q.g ∧
47a52
> 
```
Differences: the renames required by the ticket; one added instance `lwMomExpFar_ownExt_dec` (Decidable, prefixed, no
statement content); a line break inside `LWAuxNestedOwn`. No added hypothesis.

Definitional check: check-file section 2 copied verbatim (namespace `RBM.Graph.T2289Check`) into a scratch file that
imports the new module, then:
```
-- rfl examples: @T2289Check.farDAnd = @lwMomExpFar_farDAnd := rfl ; @T2289Check.ownExt = @lwMomExpFar_ownExt := rfl ; @T2289Check.HeadFar = @lwMomExpFar_HeadFar := rfl
-- rfl examples: @T2289Check.AnpFarHeadAt = @AnpFarHeadAt := rfl ; @T2289Check.AnpFarAndAt = @AnpFarAndAt := rfl ; T2289Check.LWAuxNestedOwn = LWAuxNestedOwn := rfl
example (d : ℕ) : T2289Check.AnpFarHead d := lwMomExpFar_head d
example (d : ℕ) : T2289Check.AnpFarAnd d := lwMomExpFar_and d
example : T2289Check.LWAuxNestedOwn := lwMomExpFar_auxOwn
$ lake env lean $SCRATCH/T2289/Check.lean; echo "exit $?"
exit 0
```
Against the ticket mathematics: "and" domain (both conjuncts, every `i`); factor `Π_i 𝖳_t(|a_i−b_i|_∞ ∧ ℓ)`;
exponent `ordN − p`; `θ^q`; `C` chosen before `L W g t θ ℓ ξ a b S` (§29 (5)); parameter conditions `0 < W`,
`t < 1`, `0 < θ`, `0 ≤ ℓ` only; no `3 ≤ d`; norm `zdistInf` throughout. Matches the ticket's Targets and §29 checklist.

## 2. Vacuity, hidden hypotheses, cycles
- The pins are `def ... : Prop` (no structure); every hypothesis is in the signature shown in §1.
- Graph premises (`NoGhost`, `IsNested`, `ownExt`) are discharged at `figAux`, `anpKey_oneEdge` and at the
  `auxGraph_ngraph` output (instances below); analytic premises are discharged at concrete data in the
  `example` at `:441-470` (`ξ = 𝖳_t(|α−β|_∞ ∧ 1)`, `θ` = total mass of `ξ²`, `L = 4`, `farDAnd` nonempty
  with witness `Pi.single 1 2`). Not vacuous.
- Dependencies are merged theorems, not hypotheses:
```
$ grep -n "anpDetGh_holds d\|auxGraph_ngraph Dt, auxGraph_noGhost" RBM3D/Graph/LWMomExpFar.lean
278:  obtain ⟨C, c, hC, hc, hc1, H⟩ := anpDetGh_holds d p q Γ' hG' hN'
406:  exact ⟨auxGraph_ngraph Dt, auxGraph_noGhost Dt, auxGraph_isNested hxy Dt h3.1 hnd hndr h4 h5,
$ grep -n "^theorem anpDetGh_holds" RBM3D/Graph/AnpKey6.lean
862:theorem anpDetGh_holds : ∀ d : ℕ, AnpDetGh d := by
```
  The new file imports only `RBM3D.Graph.AnpKey6`, `RBM3D.Graph.AuxGraph` (lines 6-7); no cycle. No external hypothesis.

## 3. Compiled nonempty instances (same file, `:414-472`)
```
$ grep -n "^theorem lwMomExpFar_inst\|^  lwMomExpFar_and 3\|^  lwMomExpFar_head 3\|lwMomExpFar_auxOwn 2" RBM3D/Graph/LWMomExpFar.lean
417:theorem lwMomExpFar_inst_figAux : AnpFarAndAt 3 figAux :=
418:  lwMomExpFar_and 3 2 2 figAux figAux_nested.2 figAux_nested.1 (by decide +kernel)
422:theorem lwMomExpFar_inst_oneEdge : AnpFarAndAt 3 anpKey_oneEdge :=
423:  lwMomExpFar_and 3 1 0 anpKey_oneEdge (by unfold NGraph.NoGhost; decide +kernel) anpKey_oneEdge_nested
427:theorem lwMomExpFar_inst_head : AnpFarHeadAt 3 figAux :=
428:  lwMomExpFar_head 3 2 2 figAux figAux_nested.2 figAux_nested.1 (by decide +kernel)
431:theorem lwMomExpFar_inst_aux :
434:  obtain ⟨Γa, h1, h2, h3, -⟩ := lwMomExpFar_auxOwn 2 localReg2_inst_Q.pack (by norm_num)
```
plus `example` `:441-470`: `lwMomExpFar_inst_figAux` applied at `d = 3, L = 4, W = 2, g = t = 1/2, ℓ = 1`,
`a = 0`, `b = e_0`, every premise discharged (`le_rfl` for the edge bound, `Finset.single_le_sum` for the row sum).
Endpoint coverage: `_head` → `inst_head`; `_and` → `inst_figAux`, `inst_oneEdge`, `inst_aux`, example;
`_auxOwn` → `inst_aux` (at `localReg2_inst_Q.pack`, `p = 2 > 0`). None degenerate (`p ≥ 1`, `L = 4`, `ℓ = 1`,
nonempty domain). The four instances requested by the ticket are present with the requested names and shapes.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.LWMomExpFar 2>&1 | tail -1
Build completed successfully (3393 jobs).
$ lake build RBM3D.Graph.LWMomExpFar 2>&1 | grep "LWMomExpFar.lean" | grep -v "exceeds the 100"
(no output: only long-line linter warnings in the new file)
$ lake env lean $SCRATCH/T2289/Check.lean     # #print axioms part
'RBM.Graph.lwMomExpFar_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_and' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_auxOwn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_figAux' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_oneEdge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "sorry|admit|native_decide|^axiom|set_option" RBM3D/Graph/LWMomExpFar.lean
(no output)
$ git diff --name-status main...t/T2289
A	RBM3D/Graph/LWMomExpFar.lean
$ grep -rnE "lwMomExpFar|AnpFarHead|AnpFarAnd|LWAuxNestedOwn" RBM3D | grep -v "^RBM3D/Graph/LWMomExpFar.lean" | wc -l
       0
$ grep -rn "AnpFarHead\|AnpFarAnd\|LWAuxNestedOwn\|lwMomExpFar" docs/tickets/T2288*.md | wc -l
       0
```
Only the sole writable file is touched; no merged file or frozen signature changed; no registry line (as expected).
Unpinned helpers are `private` or prefixed `lwMomExpFar_` (§3 (E)).

## 5. Paper deltas
Prove report (d) proposes `T2289a` ("and" split, `7_8:1607-1611`), `T2289b` (`𝐃_{>ℓ}` "and", long edge = first step
or `a_ib_i`, `7_8:1636-1640`), `T2289c` (`Π_i 𝖳_t(|a_i−b_i|∧ℓ)` for `𝖳_t(ℓ)^p`, `7_8:1622-1625`), `T2289d`
(domain through `a_1`, centre `α_i := β^{(k)}`, `7_8:1636`), `T2289e` (premise `ownExt`, arbitrary `S` with
`HeadFar`, `C = C(Γ, d)`). These cover the ticket's expected (a)-(d) and every Lean/paper difference of the pins.

Observation (no RETURN): the truncated edge premise `ξ ≤ 𝖳_t(|α−β|_∞ ∧ ℓ)` is weaker than the paper's untruncated
edge bound (`𝖳_t` antitone), so the pins are stronger there; it is not listed in T2289e. The dispatcher may add it
to T2289e when numbering. Observation: 31 long-line linter warnings in the new file (style only).

## Verdicts
- `lwMomExpFar_head` (`AnpFarHead`): **PASS**.
- `lwMomExpFar_and` (`AnpFarAnd`): **PASS**.
- `lwMomExpFar_auxOwn` (`LWAuxNestedOwn`): **PASS**.

Ticket T2289: **PASS**. No dispatcher sign-off needed. Open for LW-13b (not a defect here): supplying `HeadFar` /
`farDAnd` membership for the expansion of `|f^{>ℓ}|^p` (ticket S1; prove report (a) item 3, `T2289d`).

