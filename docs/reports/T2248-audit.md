Auditor model: claude-opus-5-5

# T2248 audit (MA-05b, `RBM3D/Main/QUEFromQDiff.lean`): round 1 — Tue Oct  6 03:52:57 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2248-audit1`, detached at `t/T2248` = f1fbd44; merge-base with `main` = 398ebe4.

## 1. Scope, hygiene, clash

```
$ git diff --stat main...HEAD
 RBM3D/Main/QUEFromQDiff.lean | 664 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 664 insertions(+)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^unsafe" RBM3D/Main/QUEFromQDiff.lean | wc -l
       0
$ for n in <18 public names>; do git grep -nE "^(private )?(noncomputable )?(def|theorem|lemma|abbrev) +$n\b" main -- 'RBM3D/*.lean' ':!RBM3D/Probe/*'; done | wc -l
       0
$ grep -n "^import" RBM3D/Main/QUEFromQDiff.lean
6:import RBM3D.Main.QUECore
7:import RBM3D.Green.LDE
```
Only the sole writable file; no merged file (frozen signatures) touched; imports exactly Targets 5. Unpinned helpers
`W_pos_real`, `L_pos_real`, `size_cast`, `queChain_real`, `queFromQDiff_inst_etaQ` are `private` (§3 (E)).

## 2. Build and axioms

```
$ lake build RBM3D.Main.QUEFromQDiff
⚠ [3728/3728] Built RBM3D.Main.QUEFromQDiff (10s)
Build completed successfully (3728 jobs).
$ grep -c error build.log
0
```
Warnings in this file: only `longLine` at lines 15-44 (module docstring, before the `set_option`).

```
$ lake env lean scratchT2248/eq.lean   # (section 3 file) + #print axioms of all 18 public names
exit=0
'etaQ' / 'queDomain' / 'calB_le_two_inv' / 'que_three_terms' / 'etaQ_le' / 'MAQUE' / 'queRowDiff' / 'queFixed' /
'queChain' / 'QUE_of_QDiff' / 'Inst.queDomain_edge' / 'Inst.inst_queDomain' / 'Inst.inst_BetaK' /
'Inst.inst_three_terms' / 'Inst.inst_queRowDiff' / 'Inst.inst_queChain' / 'Inst.inst_queFixed' /
'Inst.inst_QUE_of_QDiff' depends on axioms: [propext, Classical.choice, Quot.sound]     (18 lines, all identical)
$ printf 'import RBM3D\nimport RBM3D.Main.QUECore\nimport RBM3D.Main.QUEFromQDiff\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean
reg exit=0
axiom audit: 7330 theorems, 2475 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; ...
158:  RBM.Endpoints.QUE: 4 [no certificate]
159:  RBM.Endpoints.QDiff: 2 [no certificate]
```
Registry: no line added or deleted (`git diff` touches no `Test/Axioms.lean`); `QUE`, `QDiff` stay owed; pre-check exit 0.

## 3. Statements against the pins (script, compiled)

Verbatim blocks (probe `97d958e:RBM3D/Probe/T2192Pins.lean`, `main:RBM3D/Endpoints.lean`), python `block in text`:
```
$ python3 verb.py
Endpoints:218-227 True 387
probe:1864-2022 True 9463
probe:2386-2393 True 605
probe:2447-2451 True 333
probe:2476-2488 True 768
```
Check-file equality: scratch file = `docs/tickets/checks/T2248-check.lean` with `import RBM3D.Main.QUEFromQDiff` added
after its imports, then the 18 examples of the acceptance criteria:
```
example : @RBM.Endpoints.T2248Check.etaQ = @RBM.Endpoints.etaQ := rfl
example : RBM.Endpoints.T2248Check.MAQUE_pin = RBM.Endpoints.MAQUE := rfl
example : RBM.Endpoints.T2248Check.Y_pin := @RBM.Endpoints.Y      -- Y ∈ {queDomain, calB_le_two_inv,
   que_three_terms, etaQ_le, queRowDiff, queFixed, queChain, QUE_of_QDiff}
example : RBM.Endpoints.Inst.T2248Check.Z_pin := @RBM.Endpoints.Inst.Z   -- Z ∈ {queDomain_edge, inst_queDomain,
   inst_BetaK, inst_three_terms, inst_queRowDiff, inst_queChain, inst_queFixed, inst_QUE_of_QDiff}
$ python3 gen.py → "18 examples"; lake env lean scratchT2248/eq.lean
exit=0   (0 error lines)
```
So every target has exactly the dispatcher's pinned statement (sections 3a/3b/4 of the check file).

**Pin against the mathematics.** `MAQUE := QDiff → QUE` with `QUE`, `QDiff` the merged pins (`Endpoints.lean:182`,
`:197`, unchanged). `QUE` matches `MR:QUE` (`1_2:405-420`): `d ≥ 3`; `ε₀ ∈ (0, 𝔡/2)`; `0 < c < ε₀ ∧ 𝔡/5`; `τ > 0`;
`∀ᶠ n, ∀ |E| ≤ 2-κ` (sup over `E`, `N₀` uniform: D500 side); both `(Meq:QUE)` (`∀ a`) and `(Meq:QUE2)` (`A ≠ ∅`);
bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}` (`queBound`). The proof route is the paper's (`1_2:519-545`): `z = E + iη_Q`,
`η_Q = W^{-ε₀} ilambda W^{d/2}/N` (`etaQ`), `(ssfa2)` (`queX_core` at `δ_a`, `1_A/|A|`), `(ssfa2_deter)` with
`|ΔΘ| ≤ C ilambda^{-2}` (`queRowDiff` ← merged `thetaDiff : MAThetaDiff`, a proved theorem, `QUECore.lean:105`),
Markov (`queMarkov`), and the exponent count `W^τ(W^{-𝔡+ε₀}+W^{-2𝔡/5}+W^{-2ε₀})` (`queChain`, `que_three_terms`).
`QUE_of_QDiff` (lines 502-535) applies `QDiff` at `(κ, 𝔠(𝔡-ε₀), τ/2, 1)` and uses only its expectation conjunct
(`hQn.2`) at `z ∈ 𝐃_{κ,ε}` given by `queDomain`; the `filter_upwards` combines `QDiff`, `queDomain`, `queChain`
and `WO` (all `∀ᶠ n`), so the quantifier order is the pin's (constants, then `∀ᶠ n`, then `E`, `a`/`A`).
Intermediate pins: `queRowDiff` constant `C(d, 𝔡, κ)` before `sz, n` (uniform); `queFixed` at one `(sz, n, E)`,
all hypotheses explicit; `queChain` needs `ε₀ < 𝔡/2`, `τ > 0`, `C > 0`, `Admissible`; `c` any real (stronger in
`c` than needed — fine, it is a lemma).

No special case passes for the general target: the target *is* the conditional `MAQUE`, as the ticket pins;
`QUE` itself stays owed (ticket header, §20). That is a correct reading, not an adapter replacing `QUE`.

**Vacuity / hidden hypotheses / cycles.** No new structure or class; hypotheses sit in the signatures (`Sizes`
fields `three_le_L`, `W_pos` are merged structural fields). `QDiff` is an owed external pin of another gate;
its limit check at `sz0` (prove report §(a)(ii): `qdBoundExp` at `η_Q`, `τ/2` decays as `x^{-3.0167}`) shows
it is not satisfiable only by blow-up, and `QDiff` is not `False`-like (statement of a paper theorem,
`1_2:488-511`). Dependencies: `QUECore` (389ad9e), `Endpoints`, `Universality/Pins`, `Defs/Sizes`, `Green/LDE`, all
merged; the new file is not imported by any of them (new module): no cycle.

## 4. Compiled nonempty instances

| endpoint | instance (same file) | data | open hypotheses |
|---|---|---|---|
| `QUE_of_QDiff` | `inst_QUE_of_QDiff := fun h => inst_QUE (QUE_of_QDiff h)` (l. 651) | `d=3`, `sz0` (admissible, `sz0_admissible`), `κ=1/10`, `ε₀=1/30`, `c=1/60`, `τ=1/10` | `QDiff` (owed pin, allowed) |
| `queChain` | `inst_queChain` (l. 609) | same, `C = 1`, `∀ᶠ n` | none |
| `queFixed` | `inst_queFixed` (l. 621) | `sz0`, `n=0` (`L=4, W=32, N=2097152`), `E=0`, `0<η_Q≤1` proved (`queFromQDiff_inst_etaQ`) | expectation half of `QDiff` (owed pin) |
| `queRowDiff` | `inst_queRowDiff` (l. 600) | `sz0`, `n=0`, `z = zI`, `lam = 1/64 ≤ 10` | none |
| probe four | `queDomain_edge`, `inst_queDomain`, `inst_BetaK`, `inst_three_terms` | verbatim (section 3) | none |

Every deterministic hypothesis (`3 ≤ d`, `Admissible`, `0 < ε₀ < 𝔡/2`, `0 < c < ε₀ ∧ 𝔡/5`, `τ > 0`, `0 < lam ≤ 𝔡⁻¹`,
`0 < Im z ≤ 1`, `|Re z| ≤ 2-κ`, `K ≥ 0`) is discharged at the data; none is `N = 0`, an empty index, a collapsed
window or a `False` premise (`A.Nonempty` is a binder of the conclusion; `L = 4(n+1) ≥ 4`). All compile (section 2).

## 5. Paper deltas

No new Lean/paper statement difference is introduced: `MAQUE` and the conclusion `QUE` are the probe/merged pins;
the uniformity of `N₀` over `E`/`𝐃_{κ,ε}` is D500, `a, b` inside the probability D503, explicit `W^τ`/`N^{-D}`
forms D504 (`docs/paper-deltas.md:1459`, `:1462-1463`). The unused hypotheses `0 < c`, `c < ε₀`, `c < 𝔡/5` make the
proof stronger than needed, not a statement change (remark, as the ticket says). Coverage: complete.

## 6. Observations (no RETURN)

1. At the pinned instance numerals `(c, τ) = (1/60, 1/10)`, the `queBound` exponent is `-1/25 + 1/30 + 1/10 = 7/75 > 0`,
   so `queBound ≥ 1` and the conclusion of `inst_QUE_of_QDiff` holds trivially (probabilities are `≤ 1`). The
   hypotheses are nondegenerate and the data are the dispatcher's pin (identical to the merged `inst_QUE`,
   `Endpoints.lean:575`), so this is not a defect of the ticket; MA-06 may prefer `c = 1/200`, `τ = 1/100`
   (exponent `-1/50`) for an instance whose conclusion is informative. Prove report §(a) remark (b) records it.
2. `inst_queChain` is `∀ᶠ n`, as pinned; at `n = 0` the inequality is false (report §(a) remark (a)) — the
   eventual threshold comes from `tendsto_W`, not from a large witness constant.
3. Consumer check (MA-06 `hQ := QUE_of_QDiff`) is not compiled here (MA-06 unwritten); `QUE_of_QDiff : MAQUE` is
   the probe's pin type, verified by `rfl`/term in section 3.

## Verdict

| target | verdict |
|---|---|
| `etaQ`, `queDomain`, `calB_le_two_inv`, `que_three_terms`, `etaQ_le`, `MAQUE` (verbatim) | PASS |
| `queRowDiff`, `queFixed`, `queChain` | PASS |
| `QUE_of_QDiff : MAQUE` | PASS |
| instances (8) | PASS |

**T2248: PASS.** No dispatcher sign-off needed.
