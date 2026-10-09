Auditor model: claude-opus-5-5

# T2355 audit (round 1): UN-52a QUEFlow, `g2bRowk`, `g2bRow`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2355-audit1`, detached at `t/T2355` = `5661068`; merge-base with `main` `5869c29`. Scratch files are in the scratchpad under `T2355/`.

## 1. Statement (check-file equality)

```
$ { echo 'import RBM3D.Universality.QUEFlow'; cat docs/tickets/checks/T2355-check.lean;
    echo 'example : RBM.Univ.T2355Check.T2355_g2bRowk := RBM.Univ.g2bRowk'
    echo 'example : RBM.Univ.T2355Check.T2355_g2bRow := RBM.Univ.g2bRow'; <#print axioms x5>; } > chk.lean
$ lake env lean chk.lean > chk.out 2>&1; echo exit $?; grep -c error chk.out
exit 0
0
```
Both targets are the dispatcher-pinned Props, unchanged (`UNG2bRowk`, `OUInterfaceK.lean:109-111`; `UNG2bRow`, `ZeroModeProfile.lean:132-134`, both on `main`):
```
theorem g2bRowk : ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)), UNG2bRowk K P := by
theorem g2bRow : UNG2bRow :=
  unG2bRow_of_k (g2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d))
```
The ticket's mathematics, checked against the proof (`QUEFlow.lean:898-949`):
- the hypotheses are exactly those of the pin: `3 ≤ d`, `UNOUProfRowk`, `Admissible 𝔠 𝔡`, `0 < τU`, `UNOUEq747k`;
- the conclusion is `UNOUQUEk` at window `(𝔡/3, 𝔡/6)` with bound `queBound (sz.W n) 𝔡 (𝔡/3) (𝔡/6) τQ` (`PinsK.lean:326-332`);
- there is no `τU ≤ ouTauMax`, as supervisor 0956 O2 requires;
- `queChain` is applied at `(𝔡/3, 𝔡/6, τQ, C)` and `UNOUEq747k` at `τ = τQ/2`;
- `queDomain` is applied at `κ' = 1`, `E = 0` and only gives `0 < η_Q ≤ 1`. The bulk at the given `κ` comes from the hypothesis `hE`.

The quantifier order matches the pin: fixed parameters, then `∀ᶠ n`, then `t, E, a`.

**Statement: PASS (both targets).**

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -n '^import' RBM3D/Universality/QUEFlow.lean
6:import RBM3D.Universality.OUInterfaceK
7:import RBM3D.Main.QUEFromQDiff
$ sed -n 404,408p RBM3D/Universality/OUInterfaceK.lean
theorem unG2bRow_of_k :
    UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNG2bRow := by
  intro h d hd 𝔠 𝔡 sz hA τU hτ _ hE
  exact (UNOUQUEk_band sz 𝔡 τU).1
    (h d hd (unOUProfRowk_band hd) 𝔠 𝔡 sz hA τU hτ ((UNOUEq747k_band sz 𝔡 τU).2 hE))
$ sed -n 463,464p RBM3D/Main/QUEFromQDiff.lean
theorem queChain : ∀ {d : ℕ}, 3 ≤ d → ∀ {𝔠 𝔡 : ℝ} (sz : Sizes d), sz.Admissible 𝔠 𝔡 →
    ∀ ε₀ c τ C : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < τ → 0 < C →
```
- No new structure and no new `Prop` is introduced.
- Every non-private declaration is a target or an instance. Everything else is private, prefixed `QUEFlow_` (46 private declarations).
- All dependencies are merged on `main`: `queDomain`, `queChain`, `locDomain_im_pos`, `unG2bRow_of_k`, `ouMatC_isHermitian`, `measurable_ouMat`, `ZeroModeProfile_ouZeta_*`.
- No import of `RBM3D`, so no cycle.
- The private `QUEFlow_queFixed` (`:815-828`) is a proved generic lemma. Its hypotheses `hQ`/`hK` are discharged inside `g2bRowk` from `UNOUEq747k` and `UNOUProfRowk`; it is not a premise of any target.
- No external hypothesis is introduced. `UNOUEq747k` is an existing pin of the UN-51 gate (owed).

**PASS.**

## 3. Compiled nonempty instance

`QUEFlow.lean:967-980` (`namespace RBM.Univ.QUEFlowInst`). Both examples compile in the module build (§4):
```
example (hE : UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000)) :
    UNOUQUEk (UNKind.band 3) sz0 (1 / 10) (1 / 1000) :=
  g2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) 3 le_rfl
    (unOUProfRowk_band le_rfl) (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num) hE
example (hE : UNOUEq747 sz0 (1 / 10) (1 / 1000)) : UNOUQUE sz0 (1 / 10) (1 / 1000) :=
  g2bRow 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (by rw [show ouTauMax (1 / 6) (1 / 10) = 1 / 720 by unfold ouTauMax; norm_num [min_def]]
        norm_num) hE
$ sed -n 259,264p RBM3D/Defs/Sizes.lean
def sz0 : Sizes 3 where
  L := fun n => 4 * (n + 1)
  W := fun n => (2 * (n + 1)) ^ 5
  lam := fun n => ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
```
- The data is nondegenerate: `d = 3`, `L_n = 4(n+1) ≥ 4`, `W_n = (2(n+1))^5 ≥ 32`, `(𝔠, 𝔡) = (1/6, 1/10)`, `τU = 1/1000`.
- Every deterministic hypothesis is discharged: `3 ≤ d` by `le_rfl`, `UNOUProfRowk` by `unOUProfRowk_band`, `Admissible` by `sz0_admissible`, `0 < τU` by `norm_num`, and for `g2bRow` also `τU ≤ ouTauMax = 1/720`.
- Only the other gate's owed pin `UNOUEq747k`/`UNOUEq747` (UN-51) stays a hypothesis, which §4 allows.
- The ticket's exponent identity at `𝔡 = 1/10` is the premise-free `inst_exponent` (`-(min (2𝔡/3) (2𝔡/5)) + 𝔡/3 + τ = -𝔡/15 + τ`), with `inst_queBound` and `inst_ouEtaQ` (`rfl`) alongside.

**PASS.**

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Universality.QUEFlow RBM3D.Test.Axioms 2>&1 | grep -E 'error|warning: declaration uses|Build completed'
Build completed successfully (3747 jobs).
$ grep 'axioms' chk.out
'RBM.Univ.g2bRowk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.g2bRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.QUEFlowInst.inst_ouEtaQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.QUEFlowInst.inst_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.QUEFlowInst.inst_queBound' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' RBM3D/Universality/QUEFlow.lean; echo rc=$?
rc=1
$ git diff --stat main...HEAD
 RBM3D/Test/Axioms.lean          |    1 -
 RBM3D/Universality/QUEFlow.lean | 1003 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 1003 insertions(+), 1 deletion(-)
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep '^[-+][^-+]'
-   `RBM.Univ.UNG2bRowk, -- (T2282, UN-51g: owed; owner UN-52 `QUEFlow` `g2bRowk`, true for every kind and profile; premise of `ouRowk_of_pins`, `unG2bRow_of_k`)
```
Registry pre-check. Without the new import, the branch's root fails as expected, because the owed line is gone and `QUEFlow` is not yet imported. With the import the hub adds at merge, it passes:
```
$ lake build RBM3D 2>&1 | grep -A1 'axiom audit'      # branch root as is, no QUEFlow import
error: RBM3D.lean:398:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...
  [RBM.Univ.UNG2bRowk]
$ awk '{print} NR==395{print "import RBM3D.Universality.QUEFlow"}' RBM3D.lean > root2.lean   # 395 = last import line
$ lake env lean root2.lean > root2.out 2>&1; echo exit $?; grep -E 'error|axiom audit:|^registry:' root2.out | cut -c1-120
exit 0
axiom audit: 10496 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 130 owed + 109 structural + 7 refuted + 14 superseded; 124 registered premise(s) carry ...
$ grep -c UNG2bRowk root2.out
0
```
- Only the two sole writable files are touched, with exactly one registry line removed.
- No frozen signature is changed: there is no edit of `QUEFromQDiff.lean`, `QUECore.lean` or `OUInterfaceK.lean`.

**PASS.**

## 5. Paper deltas

The targets are the merged pins verbatim, so this ticket adds no Lean/paper statement difference. The prove report says "`T2355a`: none", and that is correct. The design of the generic interface these pins express (the bulk inside `∀ᶠ n`, the per-`(t, E, a)` bound, the scale `η_Q`) is already covered by `docs/paper-deltas.md:1552` (D593, T2282a-c).

**PASS.**

## Observations (no statement, instance, build, axiom or paper-delta effect)

- O1. The ticket asked for the private copy of `queFixed` to stay within 200 lines. `QUEFlow_queFixed` alone is `:815-845`, but the generic copy of `queX_core`/`queBad_sub` and their helpers spans `:48-846`. File total is 1003 lines: inside the ticket's 850/1200 envelope and below the 1400 stop rule.
- O2. The merge requires the hub's root import: as §4 shows, the branch's `RBM3D.lean` fails `#assert_rbm_axioms` until `import RBM3D.Universality.QUEFlow` is added (rule (A) step 4).
- O3. The instances of `g2bRowk`/`g2bRow` are anonymous `example`s, because `UNOUEq747k` and `UNOUEq747` appear in no `RBM.Audit` list. A later ticket should classify these two Props (the prove report already flags this in (d)).
- O4. `hτU` is unused in the proof of `g2bRowk`; this is consistent with the pin having no `ouTauMax` bound.

## Verdict

| target | verdict |
|---|---|
| `RBM.Univ.g2bRowk` | PASS |
| `RBM.Univ.g2bRow` | PASS |

Ticket verdict: **PASS**. No dispatcher sign-off needed.
