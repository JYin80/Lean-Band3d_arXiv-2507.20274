Auditor model: claude-opus-5-5

# T2273 audit (round 1): UN-21 `Universality/Jak.lean`. Written Tue Oct  6 09:27:53 UTC 2026 (`date -u`)

Branch `t/T2273` @ 9715ac7. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2273-audit1` (detached).
Scratch merge simulation (main 95a50be + the branch files + the root import): `/Users/junyin/Lean_proof/RBM3D-wt/T2273-audit1-mergesim`.

## 1. Diff scope and registry
```
$ git diff --stat main...t/T2273
 RBM3D/Test/Axioms.lean      |    2 +-
 RBM3D/Universality/Jak.lean | 1003 +++++++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2273 -- RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNJak, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
+   `RBM.Univ.UNOUClaims, -- bulk universality pin, the two 𝐇_t claims (T2273, UN-21: owed; owner UNOURow)
$ git merge-tree --write-tree main t/T2273 && echo CLEAN_MERGE     # main moved to 95a50be (T2270, T2275 deleted owed lines)
762b27f50ec3446026c609e6ff3ed129bfd3cc42
CLEAN_MERGE
```
Only the two sole writable files are touched. No frozen file changed. The new file imports only
`RBM3D.Universality.JakKernel` and `RBM3D.Universality.OU`, as the ticket requires.

## 2. Statements: script diff against check file §2.1–2.3
```
$ python3 stmt.py   # whitespace-normalized body of `def T2273_<name>` vs `theorem <name> :` in Jak.lean
un_cd_le_half IDENTICAL
unJak_of_ouClaims IDENTICAL
jakRow IDENTICAL
inst_row IDENTICAL
inst_window IDENTICAL
```
Elaborated check. Scratch file `T2273-auditcheck.lean` = `import RBM3D.Universality.Jak` + check §2 verbatim + the following lines:
```
example : T2273_un_cd_le_half := RBM.Univ.un_cd_le_half
example : T2273_unJak_of_ouClaims := RBM.Univ.unJak_of_ouClaims
example : T2273_jakRow := RBM.Univ.jakRow
example : T2273_inst_row := RBM.Univ.JakInst.inst_row
example : T2273_inst_window := RBM.Univ.JakInst.inst_window
example : T2273_jakRow = (UNLocAvgBand → UNOUClaims → … → UNJak sz E nf τU C (𝔠 * 𝔡 / 30)) := rfl
```
`lake env lean`: these lines raise no error. The only error is the trailing `#assert_rbm_axioms`, and it comes
from the partial import closure: 11 premises that theorems outside `Jak`'s closure prove, for example `STKbound` and
`ThetaDecay`. None of them is `UNJak`, `UNOUClaims`, `UNOUQUE`, `UNOUDiag` or `UNLocAvgBand`. The full-closure
check is in §4.

Token check against the consumers (Pins.lean, read in the audit worktree):
- `jakRow`'s statement is `UNJakUywRow` (`Pins.lean:805-809`) with the conjunct `∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)`
  removed. The hypotheses, the quantifier order (`∀ nf, ∃ C τ₀, 0 < τ₀ ∧ ∀ τU …`) and the `𝔠 * 𝔡 / 30` token are the same.
- `unJak_of_ouClaims` concludes `UNJak sz E nf τU (3 * nf + 16) (𝔠 * 𝔡 / 30)`. This is the `UNJak` conjunct shape of
  `UNClaimRow` (`:818`) and fits it.
- The pin `UNJak` (`:694-704`) is used as merged, with no successor. `UNOUQUE` quantifies `∀ κ τQ`, and the proof uses it at
  `(κ, 𝔡/30)` (`Jak.lean:900`). `UNOUDiag` is used at `(κ/2, δ, D)` (`:899`). Both premises are used, so they are not vacuous decoration.

| target | statement vs pin | hypotheses / quantifiers / exponent | verdict |
|---|---|---|---|
| `un_cd_le_half` (2.1) | identical | `1 ≤ d`, `Admissible 𝔠 𝔡` ⇒ `𝔠𝔡 ≤ 1/2` | PASS |
| `unJak_of_ouClaims` (2.2a) | identical | `3 ≤ d`, `0<τU≤1/4`, `UNOUQUE`, `UNOUDiag`; `C = 3nf+16`, `c' = 𝔠𝔡/30` | PASS |
| `jakRow` (2.2b) | identical | row form, `τ₀ = min τ₁ (1/4)` (`:937`) | PASS |
| `inst_row`, `inst_window` (2.3) | identical | instances (§3) | PASS |

## 3. No vacuity, no hidden hypothesis, no cycle; instances
```
$ grep -nE "structure|class " RBM3D/Universality/Jak.lean        # (no output: no structure-field hypotheses)
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Universality/Jak.lean   # (no output)
$ grep -n "hDiag\|hQUE" RBM3D/Universality/Jak.lean
858:  intro d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτ hτ4 hQUE hDiag C₀ ε hC₀ hε
899:  have evD := hDiag (κ / 2) δ D (half_pos hκ) hδ hD0
900:  have evQ := hQUE κ (𝔡 / 30) hκ (by positivity)
```
- Dependencies are merged on main: `JakKernel` (T2267), `JakSpectral` (T2251), `Pins` (T2174), `OU` (T2177) and `Sizes` (T2006).
  `jakRow` → `unJak_of_ouClaims` → `un_cd_le_half` and the private `Jak_*` lemmas. No target is used as its own premise, so there is no cycle.
- Premises of `jakRow`: `UNLocAvgBand` (owed, unused, as in the pinned row) and `UNOUClaims`. `UNOUClaims` is another gate's pin (owner `UNOURow`) and is now
  registered as owed. Neither is external. Both are owed pins, so TEAM §8 lesson 14 (concrete limit check for an external hypothesis) does not apply.
- Instances (namespace `RBM.Univ.JakInst`, `Jak.lean:952-993`), all at `sz0`. `sz0` has `d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, and
  `UNInst.sz0_adm : Admissible (1/6) (1/10)` (merged). The data are `κ = 1/2`, `E = 1` (`|1| ≤ 3/2`) and `nf = 2`.
  - `inst_row`: `jakRow hloc hOU 3 le_rfl (1/6) (1/10) sz0 UNInst.sz0_adm (1/2) (by norm_num) 1 (by norm_num) 2`.
    Every deterministic hypothesis is discharged. `UNLocAvgBand` and `UNOUClaims` stay as hypotheses; both are pins of other gates, which the ticket allows.
  - `inst_unJak`: applies `unJak_of_ouClaims` at the same data for `τU ∈ (0, 1/4]`. `UNOUQUE` and `UNOUDiag` stay as hypotheses (pins).
  - `inst_cd_le_half`: applies `un_cd_le_half` at `sz0` with no hypothesis left.
  - `inst_window`: for every `n` and every `τU > 0`, `z = 1 + i N⁻¹` is in `InWindow sz0 1 1 τU n` and `0 ≤ t*`.
    This shows that the premises of `UNJak` are satisfiable at these data, so the window is not empty. `N = (W L)^3 ≥ 1` is proved, so `N ≠ 0`.
  - No `N = 0`, no empty index, no collapsed window, no `False` premise, and no large witness: the instances are nondegenerate.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.Jak     (non-✔ lines, tail)
ℹ [3333/3333] Built RBM3D.Universality.Jak (19s)
info: RBM3D/Universality/Jak.lean:995:0: 'RBM.Univ.un_cd_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:996:0: 'RBM.Univ.unJak_of_ouClaims' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:997:0: 'RBM.Univ.jakRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:998:0: 'RBM.Univ.JakInst.inst_row' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:999:0: 'RBM.Univ.JakInst.inst_window' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:1000:0: 'RBM.Univ.JakInst.inst_unJak' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Jak.lean:1001:0: 'RBM.Univ.JakInst.inst_cd_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3333 jobs).
```
Registry pre-check in full closure. In the merge simulation (main 95a50be + `Jak.lean` + merged `Axioms.lean` blob of 762b27f +
`import RBM3D.Universality.Jak` after the last import line), `lake build` (whole library, root `#assert_rbm_axioms`, `Test/AuditNegative`) gives:
```
info: RBM3D.lean:320:0: axiom audit: 8001 theorems, 2619 definitions, 0 axioms in `RBM` (compiler-generated declarations
premises found by scanning: 156 (borrowed 1, owed 98, structural 40, refuted 6, superseded 11).
registry: 2 borrowed + 148 owed + 103 structural + 7 refuted + 12 superseded; 116 registered premise(s) carry nothing ye
Build completed successfully (4083 jobs).          # exit 0; `grep ^error` → no output
main 95a50be (same command, for comparison):
registry: 2 borrowed + 148 owed + 103 structural + 7 refuted + 12 superseded; 119 registered premise(s) carry nothing yet
```
The owed count is 148 both with and without the change (−1 `UNJak`, +1 `UNOUClaims`). There is no unregistered premise. The scan
finds 3 more owed premises: `UNOUClaims`, `UNOUQUE` and `UNOUDiag` are now carried by theorems.

Name clash (`git grep -nw <name> main -- RBM3D RBM3D.lean`, file itself excluded): `un_cd_le_half` 0, `unJak_of_ouClaims` 0,
`JakInst` 0, `inst_unJak` 0, `inst_cd_le_half` 0. `jakRow` has 3 hits, all in docstrings at `Pins.lean:636, 647, 658`. Every helper is
`private` with the prefix `Jak_`: `grep '^private' | grep -v Jak_` gives no output.

## 5. Paper deltas
- No Lean/paper statement difference: the targets are the merged pins `UNJak` and `UNJakUywRow` (first conjunct) verbatim.
- The prove report §(d) proposes **T2273a** (design table: `C = 3nf+16` confirmed at `d ≥ 3`, `20 → 4(2d+1)`, good
  exponent `𝔠𝔡/18`, bad exponent `𝔠𝔡/30` binds, registry entry `UNOUClaims`). This matches the ticket's expected candidate.
  T2273b: none. Coverage is complete.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. The ticket says "append" the `UNOUClaims` owed line. The branch puts it in the place of the deleted `UNJak` line inside `owedProps`.
   The list order has no meaning for `#assert_rbm_axioms`, and the merge with main is clean (§1).
2. Prove report line 249 gives "157 owed". That was main at the branch base (ed29a8b). Main has since moved to 95a50be (148 owed after
   T2270 and T2275). The invariant the report claims (count unchanged by this ticket) holds again at 95a50be (§4).
3. `inst_unJak` and `inst_cd_le_half` are extra public instances in `RBM.Univ.JakInst`. They are not pinned, but the namespace
   rule allows them.
4. The scratch worktree `RBM3D-wt/T2273-audit1-mergesim` remains for the hub to prune. It holds no commits.

## Verdict
| target | verdict |
|---|---|
| `un_cd_le_half` | PASS |
| `unJak_of_ouClaims` | PASS |
| `jakRow` | PASS |
| instances `inst_row`, `inst_window` (+ `inst_unJak`, `inst_cd_le_half`) | PASS |

**T2273: PASS.** No dispatcher sign-off needed. Merge note: the `Axioms.lean` hunk merges cleanly with main 95a50be (`git merge-tree`).
