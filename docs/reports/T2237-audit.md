Auditor model: claude-opus-5-5

# T2237 audit (round 1): BA-S1 `lem_ConArg_BA`, event form `BAConArg''` (`RBM3D/BA/ConArg.lean`)

Audited: branch `t/T2237` at `e258fb7` (merge base `05e5052`), detached worktree `RBM3D-wt/T2237-audit1`; started `Tue Oct  6 04:00:49 UTC 2026` (`date -u`).
Inputs: ticket `docs/tickets/T2237.md`, `docs/tickets/T2237-amend-1.md` (target 1 is the successor `BAConArg''`, S-B), check `docs/tickets/checks/T2237-check.lean`, prove report `docs/reports/T2237-prove.md`.

## 1. Statements against the pins (script diffs)

Target 1 (Amend 1): `BAConArg''` = `BAConArg'`'s hypotheses verbatim, then `∀ C₀ > 0`, `BAConArgLoop''` for `k ≥ 2` and `BAConArgVec`.
```
$ diff <(sed -n 630,636p RBM3D/BA/FlowPins.lean) <(sed -n 70,76p RBM3D/BA/ConArg.lean)    # BAConArg' vs BAConArg''
1c1
< def BAConArg' (d : ℕ) : Prop :=
---
> def BAConArg'' (d : ℕ) : Prop :=
7c7
<         (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t
---
>         ∀ C₀ : ℝ, 0 < C₀ → (∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz z s t k C₀) ∧ BAConArgVec sz z s t
$ diff <(sed -n 599,608p RBM3D/BA/FlowPins.lean) <(sed -n 61,66p RBM3D/BA/ConArg.lean)    # BAConArgLoop vs BAConArgLoop''
1,2c1
< max_a tr(Im G_t E_a)`, under the block Anderson law `seqP (sz.withLam 0)`. -/
< def BAConArgLoop {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (k : ℕ) : Prop :=
---
> def BAConArgLoop'' {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (k : ℕ) (C₀ : ℝ) : Prop :=
4,9c3,5
<     (fun n p ω => ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
<     (fun n p ω => ((etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
<           (baFMz sz z).eta n (t n)) * sz.Bctl n (s n)) ^ (k - 1) *
<         Finset.univ.sup' ⟨(0 : Zd d (sz.L n)), Finset.mem_univ _⟩
<           (fun a => ((baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω -
<             (baFMz sz z).L n (t n) (fun _ : Fin 1 => false) (fun _ => a) ω).im / 2))
---
>     (fun n p ω => (baFMz sz z).omegaC n (t n) C₀ ω * ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
>     (fun n _ _ => ((etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
>           (baFMz sz z).eta n (t n)) * sz.Bctl n (s n)) ^ (k - 1))
$ sed -n 55,56p RBM3D/BA/ConArg.lean    # FlowFM.omegaC, as Amend 1 bullet 1 (verbatim shape)
def FlowFM.omegaC {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t C₀ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n t ω x y‖ ≤ C₀ then 1 else 0
```
Reading: left side gains the indicator `1(Ω_t)`, right side loses the factor `max_a tr(Im G_t E_a)` (rate `((η_s/η_t)·Bctl_s)^{k−1}` unchanged); hypotheses, law `seqP (sz.withLam 0)`, `ε₁ ≤ s ≤ t < 1`, `κ ≤ Im m(E, g_s)`, `STLmaxgL` at `s`, and `BAConArgVec` are byte-identical to the merged pin. This is exactly Amend 1's S-B shape and the band `STConArg` shape (`Induction/Defs.lean:334-345`; there `C₀` is quantified up front, here after the hypotheses — logically equivalent).

Intermediate lemmas, `BAConArgHyp`, conjunct 2 and target 1 — compiled against the check file (check text, sections 1–3, with `import RBM3D.BA.ConArg` added):
```
$ cat accept.lean | tail -n +194 | head -11      # appended after the check file's section 3
example (d : ℕ) : BAhflow_scale_stmt d := RBM.BA.BAhflow_scale d
example : BAGres_smul_stmt := RBM.BA.BAGres_smul
example : BAimG_eta_mono_stmt := RBM.BA.BAimG_eta_mono
example : BAimG_poisson_stmt := RBM.BA.BAimG_poisson
example : BAself_norm_le_one_stmt := RBM.BA.BAself_norm_le_one
example : BAenergy_le_stmt := RBM.BA.BAenergy_le
example : BAztTilde_arith_stmt := RBM.BA.BAztTilde_arith
example (d : ℕ) : BAimTrace_compare_stmt d := RBM.BA.BAimTrace_compare d
example (d : ℕ) : baConArgVec_holds_stmt d := RBM.BA.baConArgVec_holds d
example : @RBM.BA.BAConArgHyp = @RBM.BA.T2237Check.BAConArgHyp := rfl
example (d : ℕ) : RBM.BA.BAConArg'' d := RBM.BA.baConArg''_holds d
$ lake env lean accept.lean ; echo exit=$?      # output = only the check file's own #check lines, then the #print axioms of §4
exit=0
```
`baConArgLoop_holds_stmt` (the `Φ_t` form) is superseded by Amend 1; its replacement `baConArgLoop''_holds` has the statement `∀ … , BAConArgHyp … → ∀ C₀ > 0, ∀ k ≥ 2, BAConArgLoop'' …` (`ConArg.lean:1241-1243`), i.e. conjunct 1 of `BAConArg''`; `baConArg''_holds` is assembled from it and `baConArgVec_holds` (`:1824-1828`).

| target | statement | verdict |
|---|---|---|
| `baConArg''_holds : BAConArg'' d` (target 1, Amend 1) | = Amend 1 shape (diff above), every `d` | PASS |
| `baConArgLoop''_holds`, `baConArgVec_holds`, `BAConArgHyp` | conjunct bodies; `BAConArgHyp` `rfl` to the check; Vec = check `_stmt` | PASS |
| `BAhflow_scale`, `BAGres_smul`, `BAimG_eta_mono`, `BAimG_poisson`, `BAself_norm_le_one`, `BAenergy_le`, `BAztTilde_arith`, `BAimTrace_compare` | = check `_stmt` bodies (term-mode `example`s above) | PASS |

## 2. Vacuity, hidden hypotheses, cycles

- No structure-field hypotheses: `BAConArgHyp` is a plain `def` conjunction (`rfl` to the check). `BAFlow`, `STLmaxgL`, `PrecL`, `BAConArgVec` are merged definitions (T2197, `b750bf3`), unchanged (`git diff --name-only main...t/T2237` lists no FlowPins file, §4).
- Imports: `RBM3D.BA.FlowPins`, `.BA.CouplingWindow`, `.Induction.ConArg`, `.Induction.ConArgDet`, `.Induction.Split` (all merged; within the ticket's allowed list; no `import RBM3D`). No cycle: the new module is imported by nothing.
- External hypothesis: only `STLmaxgL` at the `g_s` carrier (owed pin of the BA chain, `Axioms.lean` `owedProps`; registry pre-check below: `RBM.BA.STLmaxgL: 8 [no certificate]`). Its deterministic limits at the instance data are checked in the prove report (a)(ii) `det.py`/`sb.py` (`Bctl_s → 0`, `Bctl_s⁻¹ ≤ size`, `(eq:WO)`, `W ≥ N^𝔠`, `κ ≤ Im m_s`). No `STGbEXP*`/`STKbound*` input (P4).
- Non-vacuity of the conclusion: `C₀` is universally quantified; for `C₀ ≥ 1/η_t` the indicator is identically 1 (`‖G‖_max ≤ 1/Im z_t`), so the statement contains the unindicated bound at those thresholds.

## 3. Compiled nonempty instances (same file, `RBM.BA.ConArgInst`, `ConArg.lean:1841-1982`)

- `inst_baConArg''` (target 1): `baConArg''_holds 3` at `sz0` (`n = 0`: `L = 4, W = 32, g = 1/64`), `zSeq`, `κ = ε₁ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ t ≡ 1/2`, `C₀ = 2`; positivity by `norm_num`, `BAFlow` by `flow_sz0`, `κ ≤ Im m(E, g_s)` by `inst_premise_diag`, `s ≤ t`, `t < 1` discharged; sole hypothesis `hL : STLmaxgL …` (owed pin, allowed by CLAUDE.md §4 step 2 and the ticket).
- `inst_baConArgLoop''` (every `C₀ > 0`, `k ≥ 2`), `inst_baConArgVec`, `inst_BAConArgHyp`: same data, same sole hypothesis.
- Section-2 lemmas: `inst_hflow_scale` (`s = 1/2 < t = 3/4`, every `ω`); `example`s for `BAGres_smul` (`diag(1,−1)`, `r = 2`, both charges), `BAimG_eta_mono` (`y = 1 ≤ y' = 2`), `BAimG_poisson` (`x = 0, x' = 1, y = C = 1`), `BAself_norm_le_one`, `BAenergy_le` (flow point `MFixedPointInst.P`), `BAztTilde_arith` (`(c,κ,Λ) = (1/2,1/2,62)`, `E = 1/10, s = 1/2, t = 3/4, m₀ = 1/10 + i/2, m_s = i`), `inst_imTrace` (`sz0`, every `ω`, `a`). All hypotheses discharged; no `N = 0`, empty index, collapsed window or `False` premise; witnesses are not astronomically large.
- All of these compile (`lake build RBM3D.BA.ConArg` below).

## 4. Build, axioms, hygiene, scope

```
$ lake build RBM3D.BA.ConArg 2>&1 | grep -E 'error|BA/ConArg.lean|Build completed'
Build completed successfully (3745 jobs).
$ lake env lean accept.lean | grep axioms
'RBM.BA.baConArg''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baConArgLoop''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baConArgVec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAimTrace_compare' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAhflow_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGres_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAimG_eta_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAimG_poisson' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAself_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAenergy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAztTilde_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ConArgInst.inst_baConArg''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ConArgInst.inst_baConArgLoop''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ConArgInst.inst_baConArgVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ConArgInst.inst_imTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ConArgInst.inst_hflow_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/BA/ConArg.lean | wc -l
       0
$ git diff --name-only main...t/T2237
RBM3D/BA/ConArg.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2237 -- RBM3D/Test/Axioms.lean | grep '^[-+] ' | cut -c1-120
-   `RBM.BA.BAConArg', -- `lem_ConArg_BA` repaired (`7_8:1956-1987`, premise `κ ≤ Im m(E, g_s)`; Amend 1, DECISIONS §68
+   `RBM.BA.BAConArg',            -- `lem_ConArg_BA` in the `Φ_t` form (T2197 Amend 1): not refuted, not provable from it
$ git show t/T2237:RBM3D/Test/Axioms.lean | grep -n "def owedProps\|def supersededProps\|RBM.BA.BAConArg'\|RBM.BA.STLmaxgL"
101:def owedProps : List Name :=
149:   `RBM.BA.STLmaxgL, -- `(Eq:L-KGt2)` at a law `μ` over a flow carrier, ...
377:def supersededProps : List Name :=
379:   `RBM.BA.BAConArg',            -- `lem_ConArg_BA` in the `Φ_t` form (T2197 Amend 1): ...
$ lake build RBM3D 2>&1 | grep -E '^error|Build completed'; printf 'import RBM3D\nimport RBM3D.BA.ConArg\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean | grep -E 'axiom audit|premises found'; echo exit=$?
Build completed successfully (4048 jobs).
axiom audit: 7148 theorems, 2398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 97, structural 33, refuted 6, superseded 7).
exit=0
$ git merge-tree --write-tree main t/T2237 >/dev/null; echo exit=$?     # main moved past the merge base 05e5052 (Axioms.lean +9 lines on main)
exit=0
```
Registry: `BAConArg'` moved owed → `supersededProps` (Amend 1: `supersededProps` exists on main); `STLmaxgL` kept owed; `BAConArg''` has no line (proved). Frozen signatures untouched (no merged file other than the registry list is in the diff).
Name clash: each of the 22 new public names (`FlowFM.omegaC`, `BAConArgLoop''`, `BAConArg''`, `bandFM_omegaC`, `BAConArgHyp`, the 8 lemmas, 3 theorems, 6 `inst_*`) has `main-decls=0` (`git grep` of `def|theorem|lemma|abbrev <name>` on `main`, non-Probe). The other 47 declarations are `private` (`grep -c '^private'` = 47).

## 5. Paper deltas

| Lean/paper difference | coverage |
|---|---|
| event form `1(Ω_t)·max|𝓛^{(n)}_t| ≺ ((η_s/η_t)W^{-d}B_{s,0})^{n−1}`, `∀ C₀ > 0`, instead of the factor `max_a tr(Im G_t E_a)` (`7_8:1965`) | T2237a (prove report (d); also Amend 1) |
| premise `κ ≤ Im m(E, g_s)` | T2237a; merged D547 (T2197) |
| `z̃` arithmetic: `|E| ≤ 2+2d|g_s| ≤ Λ`, `‖m‖ ≤ 1`, `η_t ≤ C η_s` replace band `|E| ≤ 2−κ`, `η_t ≤ η_s` | T2237b |
| `Φ_t` pin `BAConArg'` not proved, superseded | T2237a, registry line |

Every statement difference introduced by this ticket is covered.

## Observations (no verdict effect)

- O1 (hub): `main` has moved past the merge base `05e5052`; `RBM3D/Test/Axioms.lean` differs on main (+9 lines). The branch change is one text-anchored line move; `git merge-tree` is clean. At merge, apply the line change, do not overwrite main's `Axioms.lean` with the branch copy.
- O2: `t < 1` (paper `t ≤ 1`, `7_8:1957`) is inherited unchanged from the merged pin `BAConArg'` (T2197), not introduced here.
- O3: `inst_baConArg''` fixes `C₀ = 2`, just below `1/η_t ≈ 2.001` at `n = 0` (prove report (a)), so `Ω_t` is not forced to be the whole space; `inst_baConArgLoop''` covers every `C₀ > 0`.

## Verdict

**PASS** (all targets: `baConArg''_holds` per Amend 1, `baConArgLoop''_holds`, `baConArgVec_holds`, `BAConArgHyp`, the 8 section-2 lemmas). No dispatcher sign-off needed beyond Amend 1, which is already issued.
