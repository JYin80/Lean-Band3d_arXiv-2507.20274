Auditor model: claude-opus-5-5

# T2210 audit (MA-01, `RBM3D/Endpoints.lean`), round 1 — Mon Oct  5 20:26:56 UTC 2026

Branch `t/T2210` 72ac37b (merge-base a42cad0 = `main` HEAD); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2210-audit1`.

## 1. Files touched (sole writable files)

```
$ git diff --stat main...t/T2210        |  $ grep -n import RBM3D/Endpoints.lean
 RBM3D/Endpoints.lean   | 799 +++++++   |  6:import RBM3D.Universality.Pins
 RBM3D/Test/Axioms.lean |   7 +-
```
Only the two sole writable files; import is a named merged module (not `RBM3D`, not `Probe.*`). PASS.

## 2. Statement: verbatim move (Targets 1) and check-file equality

Script: extract the nine probe ranges from `git show 97d958e:RBM3D/Probe/T2192Pins.lean`, test `block in text`
and order, then print the file with the nine blocks removed.
```
B1 48-210 lines=163 in=True order=True
B2 213-362 lines=150 in=True order=True
B3 365-462 lines=98 in=True order=True
B4 1094-1129 lines=36 in=True order=True
B5 2048-2070 lines=23 in=True order=True
B6 2104-2190 lines=87 in=True order=True
B7 2275-2384 lines=110 in=True order=True
B8 2395-2434 lines=40 in=True order=True
B9 2460-2474 lines=15 in=True order=True
```
Residual text (condensed): copyright (= probe `:1-5`); the import; a new module docstring (MA-01, D504, D500/D501/D503,
Thm 2.4 = `UNBUniv`, Thm 2.7 with BA, MA-02…MA-06); probe `:36-44` verbatim; `namespace RBM.Endpoints`; one `/-! -/`
header, `section Domain`, `variable {d : ℕ}`, `end Domain` around B4; `end Inst`, `end RBM.Endpoints`. Nothing else. PASS.

Check-file equality (scratch file = check import + `import RBM3D.Endpoints` + check-file lines 25–252
(sections 1–2) + 20 vocabulary `rfl` examples + 5 pin `rfl` examples; compiled in the audit worktree):
```
$ lake env lean RBM3D/AuditEqCheckT2210.lean >/dev/null 2>&1; echo "exit=$?"; grep -c "^example" …
exit=0
25
```
The 20 vocabulary definitions and the five pins are definitionally the pinned text (scratch deleted). PASS.

### Pins against the paper (`paper/tex/1_2_Intro_model_result.tex`)
- `decol` (Thm 2.1, `:357-370`): `∀ d ≥ 3, ∀ 𝔠 𝔡, ∀ sz, Admissible 𝔠 𝔡 → ∀ κ τ D > 0, ∀ᶠ n, P(decolBad) ≤ N^{-D}`.
  `Admissible` (`Defs/Sizes.lean:177`) = `0<𝔠 ∧ 0<𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 (W ≥ N^𝔠) ∧ WO 𝔡
  (W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹)`: `(Main_DEL_COND)` 359, `(eq:WO)` 363; event = negation of `(eq:psikLinfty)` 367 over every
  orthonormal eigenbasis (T2001h). Parameter order: fixed constants, then `∀ᶠ n`. PASS.
- `locSC` (Thm 2.2, `:386-395`): both events `≤ N^{-D}`, `∃ z ∈ 𝐃_{κ,ε}` inside the event (`∩_z` inside, T2001b);
  `calB` = `(lam²+η)⁻¹/(W²(K+W)^{d-2}) + (Nη)⁻¹` term by term with `(eq:calBetaK)` 384; `locDomain` =
  `(eq:spectral_domain)` 380; `|x−y|` read as `distB` (D501). PASS.
- `QUE` (Thm 2.3, `:406-420`): `0<ε₀<𝔡/2`, `0<c<ε₀`, `c<𝔡/5`, `τ>0`, `∀ᶠ n, ∀ E, |E| ≤ 2−κ` (sup_E, `N₀` uniform),
  `∀ a` for `(Meq:QUE)`, `∀ A, A.Nonempty` for `(Meq:QUE2)` (T2001f), bound merged `queBound`. PASS.
- `QDiff` (Thm 2.5, `:488-511`): `(eq:diffu1,2)` `≤ N^{-D}` with `z, a, b` inside (D503); `(Meq:QdS1,2)` per
  `z ∈ 𝐃_{κ,ε}`, `∀ a b`, `N₀` uniform (D500); `qdBound`, `qdBoundExp` match the right sides term by term. PASS.
- `BUniv := UNBUniv` (Thm 2.4; merged `Universality/Pins.lean:177`, unchanged). PASS.
- Bridges `locSC_to_UNLocAvgBand : locSC → UNLocAvgBand`, `QUE_to_UNQueBand : QUE → UNQueBand`: no extra hypotheses.
  PASS.

## 3. Hidden hypotheses, vacuity, cycles
- `Sizes` fields (`Defs/Sizes.lean:138-146`): `L, W, lam, three_le_L, W_pos` — data and `L ≥ 3`, `W > 0` only; no
  result is hidden in a structure. The pins are `def … : Prop` (owed, registered), not assumed anywhere as true.
- No cycle: only merged import; no theorem takes a pin it concludes. `explicit_of_stochDomAt` is for any `(Ω, P)`. PASS.

## 4. Compiled nonempty instances (B6–B9, namespace `RBM.Endpoints.Inst`)
Read from the file (`:545-797`). `d = 3`; deterministic hypotheses discharged by `le_rfl`, `sz0_admissible`,
`szLo_admissible`, `szUp_admissible`, `norm_num`:
- `inst_decol`, `inst_locSC`, `inst_QUE`, `inst_QDiff`, `inst_BUniv` (`k = 1`, `E = 0`, `bump`, `bump_testFun`),
  `inst_bridge_loc`, `inst_bridge_que` at `sz0` (`n = 0`: `L = 4`, `W = 32`), `(𝔠,𝔡) = (1/6,1/10)`; the only
  hypothesis left is the pin itself (allowed: another gate's pin).
- `(eq:WO)` edges: `szE` (`L_n = n+3`, `W_n = (n+2)^6`), `szLo` (`lam = W^{-3/2+1/5}`), `szUp` (`lam = 5`), with
  `szLo_admissible`, `szUp_admissible` proved; `inst_locSC_lo`, `inst_locSC_up`, `inst_QUE_up`.
- Extreme inputs: `domain_extreme` (`𝐃_{2,1} ∋ i`; empty at `κ = 3`, `ε = 2`), `locBad1_empty_kappa`, `im_mE_edge`,
  `que2BadMat_univ`, `que2BadMat_empty_zero`; `zI`, `zI_dom`, `zI_im_pos`, `zI_im_le`, `zI_re_le`; `inst_calB`,
  `inst_distB_compare` (factor `3^{-1}`).
No `N = 0`, empty index, collapsed window or `False` premise; all compile (§5). PASS.

## 5. Build, axioms, forbidden tokens
```
$ lake build RBM3D.Endpoints RBM3D.Test.Axioms
✔ [3330/3330] Built RBM3D.Endpoints (4.2s)
Build completed successfully (3330 jobs).
exit=0
$ lake env lean RBM3D/Endpoints.lean >/dev/null 2>&1; echo "exit=$?"; … | grep -c warning
exit=0
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Endpoints.lean
(no output)
```
`#print axioms` of every `theorem` of the file (46 public, generated by script; private helpers are not addressable):
```
$ grep -c "#print" RBM3D/AuditAxT2210.lean; lake env lean RBM3D/AuditAxT2210.lean > ax.txt; echo exit=$?
46
exit=0
$ grep -o "depends on axioms: \[.*\]" ax.txt | sort | uniq -c
  46 depends on axioms: [propext, Classical.choice, Quot.sound]
```
PASS.

## 6. Registry (Targets 3)
```
$ git diff main...t/T2210 -- RBM3D/Test/Axioms.lean   (hunk @@ -239,7 +239,12 @@)
-   `RBM.Gauss.Sizes.STExpWardII] -- `6:137-141` …
+   `RBM.Gauss.Sizes.STExpWardII, -- `6:137-141` …
+   `RBM.Endpoints.decol, -- Thm 2.1 `1_2:357-370`: MA-03 `decol_of_locSC` + MA-04; MA-01 (T2210, DECISIONS §16, §20: owed)
+   `RBM.Endpoints.locSC, -- Thm 2.2 `1_2:386-395`: MA-04 `MANetLoc` from MA-03; MA-01 (T2210, …: owed)
+   `RBM.Endpoints.QUE, -- Thm 2.3 `1_2:406-420`: MA-05 `MAQUE`; MA-01 (T2210, …: owed)
+   `RBM.Endpoints.QDiff, -- Thm 2.5 `1_2:488-511`: MA-04 `MANetQD` from MA-03; MA-01 (T2210, …: owed)
+   `RBM.Endpoints.BUniv] -- Thm 2.4 `1_2:452-459`, the `abbrev` of `UNBUniv`: UN-52, MA-06; MA-01 (T2210, …: owed)
```
Pre-check (scratch `import RBM3D` + `import RBM3D.Endpoints` + `#assert_rbm_axioms`, deleted afterwards):
```
exit=0
axiom audit: 6225 theorems, 2195 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Endpoints.decol: 1 [no certificate]
  RBM.Endpoints.locSC: 5 [no certificate]
  RBM.Endpoints.QUE: 4 [no certificate]
  RBM.Endpoints.QDiff: 1 [no certificate]
  RBM.Endpoints.BUniv: 1 [no certificate]
registry: 2 borrowed + 148 owed + 79 structural + 4 refuted; 101 registered premise(s) carry nothing yet: [...
 RBM.Univ.UNLocAvgBand,
 RBM.Univ.UNQueBand,
```
No unregistered premise; `UNLocAvgBand`, `UNQueBand` appear under "carry nothing yet" as the ticket expects; their
owed lines are kept. Exactly the five lines of Targets 3. PASS.

## 7. Name clash
```
$ grep -rn "namespace RBM.Endpoints\|namespace Endpoints\|RBM\.Endpoints" RBM3D | grep -v "^RBM3D/Endpoints.lean" \
    | grep -v "^RBM3D/Test/Axioms.lean"
RBM3D/Universality/FreeConvStability.lean:46:`open RBM.Endpoints` becomes `open RBM`; …   (docstring)
RBM3D/Universality/FreeConv.lean:29:… `open RBM.Endpoints` (no such …                  (docstring)
```
`RBM.Endpoints` is new on `main`; both hits are docstring text. No clash. PASS.

## 8. Paper deltas
`git show main:docs/paper-deltas.md | sed -n 1459,1465p`: D500 (QDiff 3rd/4th conjunct, `N₀` uniform), D501 (`L^∞`
block distance, `calB_distB_compare` factor `d^{-(d-2)}`), D502 (MA-03, not here), D503 (`a, b` inside), D504
(explicit form ≡ `Prec`), D505 (domain empty exactly at `κ>2`/`ε>1`), D506 (MA-02, not here) — all present. Together
with the signed T2001a/b/f/h (DECISIONS §10) they cover every Lean/paper difference found in §2. Prove report (d) 1
proposes no `T2210a`; none is needed. PASS.

## 9. Observations (no effect on verdict)
1. Lemma-level theorems of B2–B4 (`calB_antitone`, `calB_nonneg`, `calB_dist_compare`, `calB_blk_eq_STWB`,
   `explicit_of_prec`, `prec_of_explicit`, `eventually_forall_of_sections`, `det_of_prec`, `STWB_nonneg`, `Nsz_pos`,
   `locDomain_nonempty`) have no dedicated instance in this file. The ticket fixes the instance list (B6–B9) and
   forbids other lines; their hypotheses are deterministic and satisfiable (`sz0`, `η = 1/2`); not endpoint theorems.

## Verdict
Targets 1 (nine blocks, 78 declarations), 2 (imports), 3 (registry): PASS. T2210: **PASS**; no dispatcher sign-off.
