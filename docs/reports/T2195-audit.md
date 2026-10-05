Auditor model: claude-opus-5-5

# T2195 audit (LW-10c2, `RBM3D/Graph/LocalRegular6b.lean`) — round 1 — Mon Oct  5 17:55:19 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2195-audit1`, detached at `t/T2195` = `a768e91`; merge-base with `main` `d783ee3`.
Scratch: `SP/T2195/` (`audit_pins.lean`, `audit_axioms.lean`, `audit_sigs.lean`, `precheck.lean`).

## 1. Build, diff scope, hygiene
```
$ git diff --name-status main...t/T2195
A	RBM3D/Graph/LocalRegular6b.lean
$ lake build RBM3D.Graph.LocalRegular6b 2>&1 | grep -E "error|warning: .*LocalRegular6b|sorry|Built RBM3D.Graph.LocalRegular6b|Build completed"
✔ [3386/3386] Built RBM3D.Graph.LocalRegular6b (5.3s)
Build completed successfully (3386 jobs).
$ ls -la .lake/build/lib/lean/RBM3D/Graph/LocalRegular6b.olean   # absent from main's cache: compiled here
-rw-r--r--@ 1 junyin  staff  3597792 Oct  5 10:52 (PDT = 17:52 UTC) .../LocalRegular6b.olean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^open Classical\s*$" RBM3D/Graph/LocalRegular6b.lean
(no output)
$ grep -n "^import" RBM3D/Graph/LocalRegular6b.lean
6:import RBM3D.Graph.LocalRegular6a
$ grep -nE "^(noncomputable )?(theorem|lemma|def|abbrev|instance|structure) " F | grep -vE "(theorem|def|lemma) (scostLL_|localReg6b_|LGraph\.ScostLL\.(trans|of_perm|of_relabel))"
13:lemma for the primitives ...      # docstring line only: every public name carries the ticket's prefixes
$ grep -nE "^(noncomputable )?def .*: Prop" F
(no output)                         # no new Prop-valued definition; no registry line owed
```
## 2. Axioms (every constant of the module) and registry pre-check
```
$ lake env lean SP/T2195/audit_axioms.lean   # Lean.collectAxioms over env.header.moduleData[LocalRegular6b].constNames
constants: 212; axioms used: [Quot.sound, Classical.choice, propext]; non-standard: 0
exit=0
$ cat SP/T2195/precheck.lean; lake env lean SP/T2195/precheck.lean > precheck.txt; echo exit=$?; head -c 300; grep -c error
import RBM3D
import RBM3D.Graph.LocalRegular6b
#assert_rbm_axioms
exit=0
axiom audit: 5848 theorems, 2066 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; ...
0
```
## 3. Statements — the seven pins (target 1 and target 6)
`audit_pins.lean` = `import RBM3D.Graph.LocalRegular6b` + section 2 of `docs/tickets/checks/T2195-check.lean` copied by script
(namespace `RBM.Graph.T2195Check`) + one `theorem chk_x : XPin := @name` per pin + the section-3 shapes discharged by the file's instances.
```
$ diff <(section 2 of T2195-check.lean, blank lines dropped) <(T2184-check.lean:316-357, blank lines dropped)
1,3d0
< noncomputable section
< namespace RBM.Graph.T2195Check
< open RBM RBM.Graph                 # only the wrapper differs; the 7 pin bodies are T2184's lines verbatim
$ sed -n 316,357p docs/tickets/checks/T2184-check.lean | md5
4826cdc5250a809ff964ec63d6442fa2      # = the ticket's md5
$ lake env lean SP/T2195/audit_pins.lean; echo exit=$?
'RBM.Graph.T2195Check.chk_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2195Check.chk_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2195Check.chk_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2195Check.chk_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2195Check.chk_addLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2195Check.chk_moveLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2195Check.chk_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Each pin is closed by `@name` with no wrapper, so no hypothesis is added. The same file also checks the 7 section-3 shapes
(`localReg6b_inst_loop`, `_addLoop`, `fun _ => _moveLoop` plus `_moveLoopPerm`, `_contract`, `_trans`, `_T2_all`, `_transfer`) and
`localReg6b_instCyc = {solid := [⟨true,false,inr 0,inr 1⟩, ⟨true,false,inr 1,inr 0⟩], waved := [], dotted := [], coeff := 1} := rfl`.
`LGraph.ScostLL` is the merged definition (`LocalRegular6a.lean:168`, a `∀ s, ∃ s₀` with separation and `≤`). It is not a structure, so no field can hide a hypothesis.

## 4. Statements — helper targets 2–5 against the ticket's mathematics
```
$ lake env lean SP/T2195/audit_sigs.lean   (instance binders elided)
@scostLL_split_comap : ∀ (s : Setoid (E ⊕ I ⊕ Fin 1)), Setoid.comap (owxEmb 1) (scostLL_split (Sum.inr (Sum.inr 0)) s) = Setoid.comap (owxEmb 1) s
@scostLL_split_inl : ∀ (s ...) (a b : E), (scostLL_split (Sum.inr (Sum.inr 0)) s) (Sum.inl a) (Sum.inl b) ↔ s (Sum.inl a) (Sum.inl b)
@scostLL_placement : ∀ (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I))) (Aα : List (SEdge (E ⊕ I ⊕ Fin 1))),
  T.solid.Perm (List.map (SEdge.map (owxEmb 1)) L ++ Aα) →
    ((∃ col, Aα = [{ σ := col, circ := true, src := α, dst := α }]) ∨
        ∃ e₁ e₂, Aα = [e₁, e₂] ∧ e₁.circ = false ∧ (e₁.src = α ∧ e₁.dst ≠ α ∨ e₁.dst = α ∧ e₁.src ≠ α) ∧
                 e₂.circ = false ∧ (e₂.src = α ∧ e₂.dst ≠ α ∨ e₂.dst = α ∧ e₂.src ≠ α)) →
      ∀ s, (∀ e₁ e₂, Aα = [e₁, e₂] → ¬(s e₁.src e₁.dst ∧ s e₂.src e₂.dst)) →
          T.scost (scostLL_split α s) ≤ T.scost s                       [α := Sum.inr (Sum.inr 0)]
@scostLL_repair : ∀ (Γ : LGraph E I) (L) (col : Bool) (z v u' z' u : E ⊕ I) (s : Setoid (E ⊕ I)),
  Γ.solid.Perm (⟨col,false,z,v⟩ :: ⟨col,false,u',z'⟩ :: L) → s u v → s u u' → s z z' → ¬s u z →
    ∃ s₀, (s₀ = s ∨ s₀ = scostLL_merge s u z) ∧ (∀ a b : E, ¬s (inl a) (inl b) → ¬s₀ (inl a) (inl b)) ∧
          Γ.scost s₀ ≤ { solid := L, waved := Γ.waved, dotted := Γ.dotted, coeff := Γ.coeff }.scost s + 2
scostLL_elem_E0 : ∀ (X R A : ℕ × ℕ × ℕ × ℕ), -1 ≤ el (X + A) - el (X + R) ∧ (el (X + A) - el (X + R) = -1 → lwElem (X + R) = true)
scostLL_elem_E3 : ∀ (X R : ℕ × ℕ × ℕ × ℕ), scostLL_el (X + R) - scostLL_el (X + R) = 0
def scostLL_split := fun a s => { r := fun u v => u = v ∨ u ≠ a ∧ v ≠ a ∧ s u v, ... }
def scostLL_merge := fun s u z => { r := fun a b => s a b ∨ s a u ∧ s z b ∨ s a z ∧ s u b, ... }
```
| ticket item | Lean (file line) | check |
|---|---|---|
| 2(a) class-sum form; `clsPat` filters as `skept` | `scostLL_kept` :137 = `L.filter fun e => e.circ \|\| !decide (s e.src e.dst)`, identical to `LGraph.skept` (`6a:139`); `scostLL_scost_eq` :325; `_clsPat_append` :190, `_perm` :196 | same formula as the ticket |
| 2(b) fresh vertex | `scostLL_qmap_range` :386 (image misses exactly `⟦α⟧` if alone), `_intCls_emb` :409, `_sum_intCls_emb` :442, `_kept_map` :341, `_clsPat_map` :350 (any `f`), `_clsPat_map_alpha` :375 | general, as the ticket asks |
| 2(c) identity, every `s'` | `scostLL_fresh_scost` :465 | term for term as the ticket's formula; `[α alone]` is an `if` |
| 2(c) localisation | `scostLL_local_diff` :500, `scostLL_local_diff_C` :1890 (any `C` containing the classes of the ends of `R`, `A`) | as required |
| 3 pattern facts | E0 :226 (with `H = X + R`, which avoids truncated `ℕ⁴` subtraction; same content), E1 :240, E5 :246, `ne_zero` :252, E4col/out/in :258-271, E6col/out/in :277-286 | components `(b-in, b-out, r-in, r-out)` agree with `lwHalfPat` (`6a:115`) |
| 4 placement | `scostLL_split` :1483, `_split_comap` :1576, `_split_inl` :1588, `scostLL_placement` :1848 (+ `_loop` :1732, `_two` :1826) | any `T` (no `owxExt` restriction); `hk` = `k ≤ 1` (for edges with one end `α`, `s e.src e.dst ↔ s α f`); `k = 2` excluded as the ticket says |
| 5 repair | `scostLL_merge` :685, `scostLL_repair` :1256 | hypotheses and conclusion as the ticket states them; no hypothesis on `Γ`/`L`; separation forbids merging two external classes |
Verdict for targets 2–5: the generality the ticket fixes for c3 is present. No `CircIffLoop`/`Normal`/shape hypothesis has been added.

## 5. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` is declared in the file and no Prop-valued `def` is added (grep in §1). The only hypotheses are the explicit binders listed above.
- Dependencies: the file imports only `RBM3D.Graph.LocalRegular6a` (merged, T2184). Every name used upstream is on `main`. There is no cycle, because the file is a new leaf.
- No external hypothesis is added, so no limit check is owed.

## 6. Compiled nonempty instances (in the same file; all compile, see §1–§3)
| endpoint | instance (file line) | data / hypotheses discharged |
|---|---|---|
| `scostLL_loop` | `localReg6b_inst_loop` :1940; `_T1` :1946 (general `owxT1`, via `of_perm`) | `fxyPowGraph 2`, `z = inl 0`, blue |
| `scostLL_addLoop` | `_inst_addLoop` :1951 | `Γ_2`, `z = inr 1`, blue |
| `scostLL_moveLoop` | `_inst_moveLoop` :1961 | `rest = Γ_2.solid.tail`; `Perm` by `List.Perm.refl` (head is `⟨true,true,inr 1,inr 1⟩` by defeq) |
| `scostLL_contract` | `_inst_contract` :1974 at `instCyc` (`u = v = inr 1`, `z = inr 0`, `u ≠ z`, `z ≠ v` by `decide`); `_inst_contractGamma2` :2343 (`Contract(α_0; x, y)` at `Γ_2`, `Perm` proved :2329); `_inst_R2` :2031 (general `oe2xR2`) | values `instCyc_bot = 0`, `contract_bot = -2`, `L_bot = -4`, `repair_forced` (the `s₀ = ⊥` witness fails) |
| `trans` / `of_relabel` / `of_perm` | `_inst_trans` :2044; `_inst_T2` :2063 (explicit onto `localReg6b_phi`, `phi_surj` :2056, `fun _ => rfl`); `_T2_all` :2074; `_T1`, `_R2` use `of_perm` | concrete |
| §55 transfer | `_inst_transfer` :2089 (proved); `_inst_s55` :2350, `_inst_s55_prims` :2360 (`4 ≤`, far `6 ≤` for the four primitives at `Γ_2`, from merged `localReg6a_inst_cost2`) | concrete |
| `scostLL_placement` | (8) `_moveSC/_moveOut/_dmoveBlue/_dmoveRed_placement` :2100-2143 (every `Γ`; shape `Or.inr` discharged by `rfl`/`scostLL_emb_ne_alpha`; the third `Dmove` edge is moved into `L` by `Perm`); concrete `_inst_moveSC_Gamma2` :2272 (`Γ_2`, `instS`: `α ~ x`, `α ≁ y`, `k = 1`, `hk` by `omega`); loop shape `_loop_placement` :2188, `_moveLoop_placement` :2194 | nondegenerate |
| `scostLL_repair` | `_inst_repair` :2017 (`instCyc`, `s = ⊥`, all 5 hypotheses discharged by `rfl`/`simp`); `_inst_moveSC_k2` :2163 (repair applied to `MoveSC` at `k = 2` after `scostLL_fresh_dropped`) | concrete; the repair branch is forced |
| 2(a)/(b)/(c), localisation, patterns | `_inst_scost_eq` :2243, `_inst_fresh_classes` :2252, `_inst_surgery` :2287, `_inst_localise` :2308, `_inst_patterns` :2204, `_inst_refl` :2239 | `Γ_2`, every setoid; concrete `ℕ⁴` values |
None of these is degenerate: there is no `N = 0`, no empty index type (`Fin 2`, `Fin (2*2)`, `Fin 1`), no `False` premise and no huge witness. The instances apply the theorems themselves; I read the proof terms at :1940-2382.

## 7. Paper deltas
The prove report (d) proposes `T2195a` (composition plus placement: 17 terms reduce to 7 primitives, not in `B:213-262`), `T2195b` (`R2` collapse,
`B:272-273` has no per-step counterpart; the repair by merge is backed by `localReg6b_instCyc_repair_forced`) and `T2195c` (on `T2184c`: the omitted
cases closed by c2). These are the three candidates the ticket expects. `docs/paper-deltas.md:1429` carries `T2184c`, which c2–c4 number.
The Lean/paper differences are the pins, which are T2184's, and the per-primitive bookkeeping, which these candidates cover. I found no uncovered difference.

## 8. Observations (no RETURN)
- O1. `scostLL_elem_E3` (:237) is the tautology `el (X + R) - el (X + R) = 0`. It carries no content. The ticket does not require E3, and the
  `contract` proof does not depend on it for correctness, because Lean checks the proof. It is harmless, but c3 should not cite it as "(E3)".
- O2. The file is 2382 lines, above the 1400–1900 estimate and below the 2500 stop line.
- O3. The `u ≠ z`, `z ≠ v` hypotheses of the `scostLL_contract` pin are not used by the proof (report says so). The pin is unchanged.

## Verdict
| target | verdict |
|---|---|
| 1 `LGraph.ScostLL.trans`, `.of_perm`, `.of_relabel`, `scostLL_refl` | PASS |
| 2 surgery identity (a)–(c), localisation | PASS |
| 3 pattern facts E0, E1, E5, ne_zero, E4, E6 | PASS |
| 4 placement (`scostLL_split`, `scostLL_placement`, both shapes) | PASS |
| 5 repair (`scostLL_merge`, `scostLL_repair`) | PASS |
| 6 `scostLL_loop`, `_addLoop`, `_moveLoop`, `_contract` | PASS |
**Ticket T2195: PASS.** No dispatcher sign-off is needed.
