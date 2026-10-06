Auditor model: claude-opus-5-5

# T2298 audit (UN-42, `Universality/GUEPhase/EntryTailMain`) — round 1, Tue Oct  6 13:48:53 UTC 2026

Branch `t/T2298` at `58708cd`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2298-audit1` (detached).
Ticket: `docs/tickets/T2298.md` -> section "Ticket: T2293b" of `docs/tickets/T2293.md:46-57`; pins: check file
`docs/tickets/checks/T2298-check.lean` §2 "T2293b (UN-42) pins" (lines 330-365).
Targets: `mixCq_pos`, `mixBad_tail`, `mixEntry_event_subset`, `mixEntry_union`, `gueEntryMix`
(plus the ticket's vocabulary `mixCq`, `mixBad`, `mixEntry_tail_{row,quad,diag}_le`, `mixEntry_measurableSet_mixBad`).

## 1. Diff scope
```
$ git diff --name-only main...t/T2298
RBM3D/Universality/GUEPhase/EntryTailMain.lean
$ git diff main...t/T2298 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -n "^import" RBM3D/Universality/GUEPhase/EntryTailMain.lean
6:import RBM3D.Universality.GUEPhase.EntryTail
$ git log --oneline -1 -- RBM3D/Universality/GUEPhase/EntryTail.lean      # the only import: merged
e5c3253 T2293: merge UN-41 Universality/GUEPhase/EntryTail
$ git diff --name-only f9e070b ad9bb6d | grep -c EntryTailMain              # merge-base..main: no conflict
0
```
Only the sole writable file is touched; it is new, so no frozen signature changes. No registry line (ticket: "no line expected").

## 2. Statements against the pins (script: check-file §2 verbatim + the target terms, no tactic)
Scratch `T2298/pins.lean` = `import RBM3D.Universality.GUEPhase.EntryTailMain` + `sed -n 145,376p T2298-check.lean`
(vocabulary and all pins, verbatim) + these lines before `end RBM.Univ.T2293Check`:
```
example : T2293b_mixCq_pos := @RBM.Univ.mixCq_pos
example : T2293b_mixBad_tail := @RBM.Univ.mixBad_tail
example : T2293b_mixEntry_event_subset := @RBM.Univ.mixEntry_event_subset
example : T2293b_mixEntry_union := @RBM.Univ.mixEntry_union
example : T2293b_gueEntryMix := @RBM.Univ.gueEntryMix
example (q : ℕ) : RBM.Univ.mixCq q = mixCqV q := rfl
example (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) (z : ℂ) (Λ : ℝ) :
    RBM.Univ.mixBad d L W g a b z Λ = mixBadV d L W g a b z Λ := rfl
example (d : ℕ) : RBM.Univ.GUEEntryMix d = GUEEntryMixV d := rfl
example {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ) : RBM.Univ.mixMat sz n a b = mixMatV sz n a b := rfl
example {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ) : RBM.Univ.mixSample sz n a b = mixSampleV sz n a b := rfl
```
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2298-audit1 && lake env lean .../T2298/pins.lean > pins.out 2>&1; echo exit=$?
exit=0
$ grep -c error pins.out
0
```
Each pin is closed by the bare `@`-term of the target: binder order, implicit/explicit structure and every
hypothesis coincide up to definitional unfolding with the pin (pin = `∀ d, 3 ≤ d → GUEEntryMixV d` for the main
target; `GUEEntryMix d` is `rfl`-equal to the pinned text). Pinned content checked by eye against the ticket's
§29 list: `(W L)^d` squared pair count, `W^{-d}` error term, `N^{-D}` loss, `∀ᶠ n` only in `gueEntryMix` after
`𝔠 𝔡 sz κ E n0 K a b c₀ δ τ D` (fixed parameters first), `hd : 3 ≤ d`, coupling `sz.lam n` in `mixBad`.
`mixEntry_tail_{row,quad,diag}_le` and `mixCq` are the ticket's "verbatim" scalar lemmas (prove report
`compare.py`: text-identical to RBM2D `c9a24cf`); they are inputs of `mixBad_tail`, not separate pins.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|class|instance) " EntryTailMain.lean | cut -c1-70
50:def mixCq   52:theorem mixCq_pos   57/75/84:theorem mixEntry_tail_{row,quad,diag}_le
120:def mixBad   131,141:private theorem mixEntry_measurableSet_and / mixEntry_measure_and_le
151:theorem mixEntry_measurableSet_mixBad   175:theorem mixBad_tail   292:theorem mixEntry_event_subset
369:theorem mixEntry_union   431,439,453:private theorem EntryTail_eventually_{lam,delta,mixCdet}
462,503:private theorem mixEntry_final_arith / mixEntry_scalar_36   545:theorem gueEntryMix
622-756: namespace EntryTailMainCheck (instances, delta0, zeta3, aMix, bMix, mix_params_ok, ...)
```
- No `structure`/`class` introduced; no hypothesis lives in a field. `GUEEntryMix d` is a `Prop` concluded by
  `gueEntryMix`, not assumed.
- External input: none. The constants `mixDelta`, `mixCdet` (merged `EntryDet`, 7a8a4eb) involve `Kstab3`, a
  `Classical.choose` from a proved theorem; `gueEntryMix` needs only `mixDelta_pos` and finiteness, both merged.
- The coupling window `0 < sz.lam n ≤ 𝔡⁻¹` is derived inside the proof from `sz.Admissible 𝔠 𝔡` (field `WO 𝔡`)
  by `EntryTail_eventually_lam` (lines 431-436, read: `Real.rpow_pos_of_pos` + `sz.W_pos`), not added as a hypothesis.
- No cycle: the module imports only merged `EntryTail`; no other file imports it:
  `$ grep -rn EntryTailMain RBM3D --include='*.lean' | grep -v GUEPhase/EntryTailMain.lean`
  → `RBM3D/Universality/GUEPhase/EntryTail.lean:14:(\`EntryTailMain.lean\`).` (docstring only, no import).
- `mixEntry_event_subset`/`mixEntry_union` hypotheses jointly satisfiable at nondegenerate data (§4).

## 4. Compiled nonempty instances (in the module; compiled by the build in §5)
| target | instance (file line) | data | deterministic hypotheses |
|---|---|---|---|
| `mixCq_pos` | `inst_mixCq_pos` :622 | `q = 1` (`mixCq 1 = 5200`, `mixCq_one` :624) | none |
| `mixBad_tail` | `inst_mixBad_tail` :629, `inst_mixBad_tail_small` :637 | `Idx 3 3 2` (N = 216), `g = 1`, `a = b = 1/4`, `z = zt 0 (1/2)`, `Λ = 2` resp. `10^6`, `q = 1` | `norm_num`, `EntryTailCheck.inst_zt_im_ne` (merged); `_small` bound `≤ 1/1000` |
| `mixEntry_event_subset` | `inst_mixEntry_event_subset` :689 | `sz0`, `n = 0` (`L = 4, W = 32, lam = 1/64`), `Λ = 10, κ = 1, E = 0, a = b = 1/4, Φ = 2, δ = min(mixDelta 3 10 1, 1/12), T = mixCdet 3 10 1·4` | all discharged (`inst_lam_window`, `norm_num`, `min_le_left`, `delta0_36`, `le_rfl`) |
| `mixEntry_union` | `inst_mixEntry_union` :708 | as above, `K = 2`, mixtures `(1/2,0),(1/4,1/4),(0,1/2)`, `q = 1` | all discharged (`mix_params_ok 0`) |
| `gueEntryMix` | `inst_entryMix` :738, `inst_entryMix_quarter` :756 | `d = 3`, `sz0`, `(𝔠,𝔡) = (1/6,1/10)`, `κ = 1`, `E ≡ 0`, `n0 = 1`, `K ≡ 2`, three mixtures, `c₀ = 1/4`, `δ_n = N^{-1/4}`, `τ = 1/10`, `D = 2` | `sz0_admissible` (merged), `sz0_size_ge_two`, `mix_params_ok`, `positivity`, `Eventually.of_forall le_rfl`, `norm_num` |

No `N = 0`, no empty index (`Idx 3 3 2`, `Idx 3 4 32`), no collapsed window (`a+b = 1/2 ∈ (0,1)`), no `False`
premise, no pin-hypothesis left open. The witness data are small numbers; the eventual threshold of `gueEntryMix`
(prove report (a): `N ≥ 8·mixCq 239 ≈ 10^1504`) is internal to the `∀ᶠ` conclusion, not a hypothesis of the instance.
```
$ #print axioms of the 7 instances (pins.lean, §5): all "[propext, Classical.choice, Quot.sound]"
```

## 5. Build and axioms
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2298-audit1 && lake build RBM3D.Universality.GUEPhase.EntryTailMain 2>&1 | grep -E "error|EntryTailMain|Build completed" | tail -5
Build completed successfully (3361 jobs).
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/GUEPhase/EntryTailMain.lean
0
$ grep -vc "depends on axioms: \[propext, Classical.choice, Quot.sound\]" pins.out
0
$ cat pins.out
'RBM.Univ.mixCq_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mixBad_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mixEntry_event_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mixEntry_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueEntryMix' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mixEntry_measurableSet_mixBad' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_mixCq_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_mixBad_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_mixBad_tail_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_mixEntry_event_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_mixEntry_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_entryMix' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.EntryTailMainCheck.inst_entryMix_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(The build's warning lines are all in upstream merged files, e.g. `Defs/Tail.lean`, `Green/LDEQuad.lean` linters; none in `EntryTailMain`.)

## 6. Paper deltas
Pin-level Lean/paper differences (carrier `ouP (UNModel.band sz) n`, coupling `sz.lam n`, `sz.Admissible`
quantification, `(W^d)⁻¹`) are already in `docs/paper-deltas.md`:
```
$ grep -n "T2293\|T2278a" docs/paper-deltas.md | cut -c1-60
1548:- **D589（T2278a–c）**：（设计）混合剖面稳定常数 `mixK d Λ κ = Kstab3 d Λ
1562:- **D603（T2293a–c）**：（Lean 结构）d≥3 载体为 `ouP (UNModel.band sz)
```
New in this ticket and proposed in prove report (d): `T2298a` (coupling window derived from `WO 𝔡`, `n`-free
`mixDelta`/`mixCdet`, RBM2D `log L` asymptotics dropped), `T2298b` (`W^{-d}`, `(W L)^d` pair count),
`T2298c` (binder layout, private helpers). Coverage complete.

## 7. Observations (no verdict effect)
- O1. Unpinned public helpers in the instance namespace (`EntryTailMainCheck.mixCq_one`, `delta0`, `delta0_nonneg`,
  `delta0_le`, `delta0_36`, `sz0_size_ge_two`) are neither `private` nor stem-prefixed (§3 (E)); they live in the
  file-specific `EntryTailMainCheck` namespace, and the prove report's name-clash grep shows 0 clashes.
- O2. `inst_mixBad_tail` and `inst_mixEntry_union` have bounds `> 1` (true but weak); `inst_mixBad_tail_small`
  supplies a sub-1 bound for `mixBad_tail`. The data are nondegenerate either way.

## Verdicts
| target | verdict |
|---|---|
| `mixCq_pos` | PASS |
| `mixBad_tail` | PASS |
| `mixEntry_event_subset` | PASS |
| `mixEntry_union` | PASS |
| `gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
