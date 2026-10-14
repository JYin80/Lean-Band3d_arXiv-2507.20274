Auditor model: claude-opus-5-5

# T2498b audit (round 1): row b, U3s3b, `Chain/QEndGridGen` (target 10)
`date -u`: Wed Oct 14 07:51:45 UTC 2026. Branch `t/T2498b` b3377663, `main` 41e55513, probe base `t/T2498` 5e8ef75a.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498b-audit1` (detached at b3377663). Ticket `docs/tickets/T2498.md` with Amend 1.
Target 10 has no pinned text (ticket :31, :55: only targets 11-12 are binding); the reference is the band `altGridEndQN'`
(`Induction/QEndGrid.lean:2176`) and the T2491 target 12 shape `nqGridEndLinNg` (`Chain/NQEndLinGen.lean:600`), per ticket :55.

## 1. Statement
### Conclusion: band `altGridEndQN'` vs `altGridEndQNg`, from `∀ Λ Φ₁ …` to `:= by`, carrier substitution by script
```
$ (band) sed 's/(pathP sz)/Cm.Pp/; s/pathH sz /Cm.Hpath /; s/sz.STLKM n (E n)/STLKMg Cm n/; s/altYSetN sz n (E n)/altYSetNg Cm n/;
         s/GoodLinN sz n (E n)/GoodLinNg Cm n/; sz.GoodSetN n (E n) … τ' D' -> {H | GoodSetNg Cm n … τ' D' H}' ; diff -w with generic
CONCLUSION IDENTICAL after carrier substitution
```
Levels, `v`, `ε₀`, `D₁`, `∃ ε₁ τ' D' C_K` (after the carrier, as ticket :55 and T2491 target 12), `∀ Φc K`, the grid
bounds `N^{C_K} ≤ K ≤ ⌈N^{C_K}⌉`, the event bound `N^{-D₁}`, the alternating sign condition `σ last = !σ 0`, the
initial bound at `N^{ε₁} Bctl(s)^{m+2}` and the endpoint loss `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃+X) Bctl(v)^{m+2}`: unchanged.

### Hypotheses (signature `QEndGridGen.lean:560-610`, compared with `nqGridEndLinNg` and the band)
| hypothesis of `altGridEndQNg` | source in the ticket | verdict |
|---|---|---|
| `hd h𝔠 hτ h𝔡 hsize hband hWO hs0 hst ht1 hcase hrange hWt` | band, verbatim | same order as band |
| `hL hW' hspec hm hSeq hS hRow hKK hKb hExp hKL hKT hU hcmp hA` | identical text to `nqGridEndLinNg` (T2491 tgt 12) | family rows 3-7, 10, 11 |
| `hspec : DecayGen_Spec`, `hm : ‖m‖ ≤ 1` replace `\|E n\| ≤ 2 - κ` | C1 (ticket :88) | allowed (loop-level, inline `‖m‖ ≤ 1`) |
| `hward hker hK₆ hrow hcol` (`K₆`) | fields of `B45Gen_Facts` (`B45Gen:60-70`), family row 9 | per-carrier; `1 ≤ K₆` is harmless: row c can take `K₆ = max C₆ 1` |
| `hTh : Step5KerGen_ThDecay Cm.toFlowFM gK 𝔡⁻¹ C₆`, `hC₆` | family row 9; Amend 1 | `C₆` a free per-carrier constant: compatible with `∃ C₆` after `κ` in row c |
| `∀ C4 Cv, 0 < C4 → C4 ≤ Cv → (C4 < Cv ∨ A = 1) →` `∀ᶠ n, QProxyG_KerEK4 … (m+2) (1/𝔠) C4 n` | D1 (target 1, row a), family row 8 | `KL = 1/𝔠` correct: `Bandwidth 𝔠` = `N^𝔠 ≤ W` ⇒ `L^d ≤ W^{1/𝔠}` (`Sizes.lean:168`, `QProxy.lean:681`) |
| `hExp hKL hKT hU` under `∀ᶠ n`; `hKK`, `hS` `∀ n` | D2 (`gridDriftQNg_envelope_ev`, `QEndA:1184`), row 11 | no `∀ n` drift premise |
| `hKb : STKboundgL` | inputs used as hypotheses only (ticket :89) | pin |
No pinned `∃` (`𝔠d`, `C4`, `C₆`, `Aof κ`) is quantified in target 10: those are row c's family quantifiers (ticket :78).
No `∀ (sz : Sizes d)` (U5S-C3: 0 hits). Verdict statement: consistent with ticket :55 and the band; not a special case.

## 2. Vacuity, hidden hypotheses, cycles
- No new `def`/`structure`/`class` in the file (outline: `grep -nE "^(theorem|def|abbrev|structure|…)"`: only `theorem`,
  `private theorem`, `private abbrev Cm1` (instance namespace), `example`). No hypothesis hidden in a structure field.
- Every class used is merged on `main` (`QProxyG_KerEK4` row a; `Step5KerGen_ThDecay`, `B45Gen` fields, `HierDriftGen_*`,
  `DecayGen_Spec`, `GridRepTailGen_Ker` merged Chain). Imports: `Induction/QEndGrid`, `Chain/QGridGen2`, `NQBudgetGen`,
  `GridAssemblyGen`, `NQEndLinGen` (all merged; build passes, so no cycle).
```
$ grep -rn "import RBM3D.Chain.QEndGridGen" RBM3D RBM3D.lean      -> RBM3D.lean:613:import RBM3D.Chain.QEndGridGen
$ grep -c "^import RBM3D.BA" QEndGridGen.lean                       -> 0
$ grep -cE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds|withLam" QEndGridGen.lean -> 0
$ C1/X1-C1 regex (ticket :92) over lines 560-610 | sort | uniq -c   ->       1 Lloop
$ (the hit) 568:      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)     # substring of KLloopOf in hKK, same as nqGridEndLinNg
```
- External hypotheses: none new; `hKb` and the family-row classes are inputs listed by the ticket (:62-78, :89), each
  discharged at the band carrier below (limit check = the band instance).

## 3. Compiled nonempty instance
`RBM.BA.QEndGridGenCheck.altGridEndQNg_instance (m : ℕ)` (`QEndGridGen.lean:1097-1152`), examples at `m = 0, 1, 2`
(`:1154-1160`). It applies `altGridEndQNg` at `d = 3`, `Cm1 = bandStep2Mat sz0 Einst` (`L = 4`, `W = 32`, `lam = 1/64` at
`n = 0`), `E ≡ 1/2`, `s ≡ 0 < v ≡ 1/32 ≤ t ≡ 1/16`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = 1/2`, `A = 1`, `gK = lam`, `K₆ = 1`,
`Cv = C4 = qProxy4C 3 (m+2) 10 κi 6 > 0`, `Λ = 3`, `Φ = (1, 12, 1)`, `X = 1`, `ε₀ = 1/10`, `D₁ = 1`, `K = KC C_K ≠ 0`.
Every hypothesis is discharged by a term (read in the proof text): `hKb` by `stKbound_holds`, D1 by
`qProxyG_kerEK4_band_at`, `hTh` by `step5KerGen_thDecay_band`, Ward/kernel sums by `zeroModeGen_*_band`, row/column sums
by private `b45_band_rowcol`, drift classes by `hierDriftGen_*_band`, R1 by `⟨mul_self_nonneg _, le_rfl, (one_mul _).ge⟩`.
No hypothesis of the example is left open. The conclusion is extracted with `.exists` to one index `n` with
`sInst n < vg n ∧ 0 < gridStep …` (`window_nondegenerate`): window not collapsed, `K n ≥ 1`. Independent re-use:
```
$ cat ax.lean   # scratch, uncommitted
import RBM3D.Chain.QEndGridGen
#print axioms RBM.BA.altGridEndQNg
#print axioms RBM.BA.QEndGridGenCheck.altGridEndQNg_instance
example (m : ℕ) := RBM.BA.QEndGridGenCheck.altGridEndQNg_instance (m + 5)
$ lake env lean ax.lean
'RBM.BA.altGridEndQNg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QEndGridGenCheck.altGridEndQNg_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Nondegenerate: yes.

## 4. Build, axioms, diff
```
$ lake build RBM3D.Chain.QEndGridGen        # audit worktree, 24 s
Build completed successfully (3913 jobs).     # grep error|declaration uses|✖ : none
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2498-check.lean   # audit worktree
exit 0; error lines: 0
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Chain/QEndGridGen.lean  -> 0
$ wc -l RBM3D/Chain/QEndGridGen.lean   ->  1168   (stop 2,000; ticket 1,700; reserve QEndGridGen2 not used)
$ git diff --stat main...t/T2498b
 RBM3D.lean                   |    1 +
 RBM3D/Chain/QEndGridGen.lean | 1168 ++++++++++
 RBM3D/Probe/T2498Pins.lean   |  397 ++++++
$ git diff main...t/T2498b -- RBM3D.lean     -> +import RBM3D.Chain.QEndGridGen   (after the last import, before #assert_rbm_axioms)
$ git diff t/T2498 t/T2498b -- RBM3D/Probe/T2498Pins.lean | wc -l   -> 0   (probe from the stack base t/T2498, not edited, never merged)
$ git diff --name-only main...t/T2498b -- RBM3D/Induction RBM3D/BA RBM3D/Test RBM3D/Chain/NQ* | wc -l   -> 0
```
All touched files are sole writable files of T2498 (`QEndGridGen.lean` row b, `RBM3D.lean` import lines, the probe on the
`t/T2498` stack only; the hub brings in exactly `QEndGridGen.lean` and the import line). Band `QEndGrid`, `QEndB1`,
`QtXiRoundLift` unedited; no frozen signature touched.

## 5. Paper deltas
Statement differences of target 10 against the band/paper and their coverage:
| difference | coverage |
|---|---|
| spectral classes (`κm`, `K₆`, `C₆`, `hward hker hrow hcol hTh`) replace `\|E\| ≤ 2 - κ` | candidate `T2498m` (prove (d)); continues D724 (g) |
| `Cv ≥ C4`, `C4 < Cv ∨ A = 1`, exponents at `Cv` | candidate `T2498l`; continues D724 (i) |
| D1 class `QProxyG_KerEK4` at `KL = 1/𝔠` replaces `qProxy4C` | D722 (`T2498a`) |
| `lam` patch kept internally (guard (g) derived from `hcmp`), not a statement change | candidate `T2498n` |
| `hKb : STKboundgL`, drift classes under `∀ᶠ n` | pins/D2 text: D724 (h); T2491 deltas for the shared hypothesis list |
Coverage complete.

## Observations (no RETURN)
- O1. Import `Chain/NQEndLinGen` is not on ticket :40's source list (prove (a′) 2); merged module, no cycle, `open private`
  of four model-free carrier lemmas, no text copied. Dispatcher may note it.
- O2. Ticket :55 says the `lam` patch "becomes the R1 guard (g)"; the proof keeps the band patch internally and derives (g)
  (`QEndGridGen_gK_win`). No statement effect (no `lam` premise in the signature beyond `hWO`, `hcmp`). Proposed `T2498n`.
- O3. `b45_band_rowcol` (private, instance namespace) re-proves the row/column part of `b45Gen_facts_band` for a general
  energy sequence; instance-only.
- O4. `open private B45_norm_colsum from RBM3D.Induction.B45` is used only by the instance helper.

## Verdict
Target 10 `altGridEndQNg`: **PASS**. Row b of T2498: **PASS**. No dispatcher sign-off needed.
