Auditor model: claude-opus-5-5
# T2515 1a-audit (design gate D1; BA-C3) — Thu Oct 15 08:10:33 UTC 2026

Inputs: ticket `docs/tickets/T2515.md`; check `docs/tickets/checks/T2515-check.lean`; report `docs/reports/T2515-prove.md` §(a), §(a″);
branch `t/T2515` = 45195400 (base `main` b2326aac). Audit worktree: detached `../RBM3D-wt/T2515-1a-audit1` at 45195400.
Scratch: `<scratchpad>/T2515/audit1a/` (copies of `inst.py`, `census.py`, `textdiff2.py`, `closure2.py`; own `blk.py`).

## 1. Probe recompile (own worktree)
```
$ lake env lean RBM3D/Probe/T2515Pins.lean 2>&1 | grep -E "axioms|error|warning|sorry"; echo "exit ${pipestatus[1]}"
Thu Oct 15 08:04:44 UTC 2026
'RBM.BA.T2515Probe.probe_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_cmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_osc_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_thetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_profSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_profComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_profZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_rowk_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.kTwoGUEBA_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2515Probe.probe_kBridge_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ git diff --stat main...HEAD          ->  RBM3D/Probe/T2515Pins.lean | 287 +++  (1 file)
$ wc -l < probe -> 287 (cap 300)  |  grep -cwE 'sorry|admit|axiom|native_decide' -> 0  |  importers -> only itself
$ X1-C4 '(def|abbrev|structure) (UNOUProfRowk|RBG_ProfComp|BAProp8|BAprof|GUEEntryMix|SBtilde)\b' -> 0
$ C1 word-bounded (msc|mE|lemT|lemE|kTwoGUE|KLgen|UNModel.band; (?<![A-Za-z])Theta d ; SB d L [^0]) outside #check -> 0
$ closure2.py (rooted at the audit worktree): probe imports -> 201 modules, V modules []; row a planned -> 203, [];
  row b planned -> 102, []
```
## 2. Statement texts: check Part 2 vs probe (rerun + independent per-name compare)
```
$ python3 -I textdiff2.py <check> <probe>
IDENTICAL (check Part 2 vs probe, docstrings stripped): T2515_CmpBA T2515_ProfCompBA T2515_ProfSpec T2515_ProfZero T2515_ThetaDiffBA T2515_ThetaTransfer
DIFFERENT: -
in check only: T2515_ProfRowBA T2515_ThetaTildeOscBA | new in probe: T2515_KBridgeBA T2515_KDerivBA T2515_ThetaTildeOscBA_zero
T2515_ThetaTildeOscBA[`0 ≤ ζ → ζ ≤ 1` := `ζ = 0`] == T2515_ThetaTildeOscBA_zero: True
$ python3 -I blk.py <check> <probe>      (own script; line blocks from `def T2515_` to the next blank/decl line)
T2515_CmpBA equal | T2515_KBridgeBA probe only | T2515_KDerivBA probe only | T2515_ProfCompBA equal | T2515_ProfRowBA check only
T2515_ProfSpec equal | T2515_ProfZero equal | T2515_ThetaDiffBA equal | T2515_ThetaTildeOscBA check only
T2515_ThetaTildeOscBA_zero probe only | T2515_ThetaTransfer equal
```
Consumer forms read (signatures): `UNOUProfRowk` (`OUInterfaceK:56`: `∃ C` before `sz`, `0 ≤ ζ ≤ 1`, `C (lam²)⁻¹/W^d`, `K.bulk`);
`RBG_ProfComp` (`RandomLayerBG:123`); `queRowDiff` (`QUEFromQDiff:244`) — `T2515_ThetaDiffBA` has its quantifier order and bound
with `∀ σ` for the `∧`; `BAprof` (`git show 921369b:…T2449Pins.lean:164`) = `(PropThetaQ Q 1 * Q) a b / W^d`, the RHS of
`T2515_ProfZero` at `σ₁ = true`; `BAKsolve` (`KSolve:58`) 2-loop = RHS of `kTwoGUEBA_self`; `baProp8_holds (d Λ κ) : BAProp8 d Λ κ`
(`Prop6Path:1009`, no premise; `FlowPins:217`: no `W^τ`, no `≺`); `primRhsGUE_two` (`KPrim:110`): same charges `[σ₁,σ₂]` in both
glued loops, `SBgue = L^{-d}` (`Bootstrap:54`); `gueShift` (`KPrim:61`); `ztOf m E t = E + (1-t) m` (`GLoopFlow:55`).

## 3. Numerics rerun
```
$ cd <scratch>/T2515/audit1a && python3 inst.py > inst.out; echo "exit $?"     (numpy needs user site; not -I)
exit 0
$ diff <(sed -n '/^d=3 L=4/,/SM ++ zeta=1.0/p' docs/reports/T2515-prove.md) inst.out && echo IDENTICAL
inst.py output IDENTICAL to report (27 lines)
```
Script content checked: `Q = t₀Q₀` asserted; bridge tests `t₀ (Θ_{t₁}(Q₀) + β(t₀)J) Q₀ = Θ̃_ζ Q` with `β = gueShift(r₀)`, `t₁ = (1-ζ)t₀`;
ODE tests `K' = L^{-d} K J K` (= `primRhsGUE_two` with `W^d` scaling); asserts `rowdiff ≤ proof bound`, `bridge < 1e-9`, `ODE < 1e-5`.
Hand check of (7.33) n = 2 (independent of the script): `K = W^{-d}(Θ_{t₁}+βJ)Q₀`, `Q₀` symmetric, translation invariant,
row/column sums `r₀`, `|r₀| ≤ Σ|M₀|² = 1`; row sums of `(Θ_{t₁}+βJ)Q₀` are `r₀ p`, `p = (1-t₁r₀)⁻¹ + βL^d = (1-tr₀)⁻¹`;
`β' = L^{-d} r₀ p²`; so `∂_t K = W^{-d}β' r₀ J = W^d·W^{-2d}L^{-d}(r₀p)² J` = RHS. Bridge for all `ζ`: `α r = ζr²/((1-r)(1-sr))`
`= t₀ β(t₀) r₀`. Both identities hold for every `ζ ∈ [0,1]`, `t₁ ≤ t < 1`.
```
$ census.py (rerun on b2326aac twin sources; pure | wide)
KPrim 1-783: pure 458 19 246 central 512 | wide 573          ZeroModeProfile 220-528: pure 285 0 24 central 302 | wide 302
EntryDet 1-897: pure 508 102 232 central 626 | wide 797      EntryTail 1-908: pure 212 131 512 central 353 | wide 761
EntryTailMain 1-602: pure 139 288 126 central 369 | wide 423
cut lines = start of the instance sections: KPrim:784 "Compiled nonempty instances", EntryDet:898 "§8 Compiled instances",
EntryTail:909, EntryTailMain:603 (checked by sed)
```
Reproduces §(a)'s census exactly: row a 814 + 300 = **1,114**, row b 1,348 + 300 = **1,648**, total **2,762** (ticket 2,808, −1.6%).

## 4. Signatures (binding after this audit)
**D1 (i) — lossless: SIGNED.** `T2515_ThetaTransfer`, `T2515_CmpBA` compiled at full generality; oscillation compiled at `ζ = 0`
(`T2515_ThetaTildeOscBA_zero`, a range restriction of the check text, nothing else). `C = 2C₈/cT`, `C₈` from
`baProp8_holds d 𝔡⁻¹ κ'`, `∃ C` before `L, lam, z`; no `W^τ`, no `≺`; premises used are all coverage rows (4–10). All-`ζ` route
(1b): `Θ̃_ζ = Θ_s + αJ/L^d`, `|r| ≤ t₀ < 1`; the `J` term is constant, so osc `Θ̃_ζ` = osc `Θ_s` ≤ `2C₈(λ₀²+|1-st₀|)⁻¹ ≤ 2C₈/(cTλ²)`
(numerics: SM error ≤ 7e-15, both charges, `ζ ∈ {0,½,1}`). Stop rule D1 (i) not hit. Binding text: `T2515_ThetaTildeOscBA` (check).
**D1 (ii) — DELIVERED.** `probe_thetaDiff : T2515_ThetaDiffBA`, text identical to the check, consumer form of `queRowDiff`,
`C = 2C₈/cT + 𝔡⁻²`. Per DECISIONS §337 (7): C3 owns the BA `thetaDiff` (target 6); M3 needs no D1.
**D1 (iii) — SIGNED.** `T2515_ProfSpec`, `T2515_ProfZero`, `T2515_ProfCompBA`, `T2515_ProfRowBA` as in the check. One text feeds
N2 (`probe_rowk_zero`, ζ = 0 slice) and C5's bridge (`probe_kBridge_zero`, `Z = {0}`); all-`ζ` bridge holds by the identity in §3.
Target-4 route (§(a) row 9): `ζ ≤ ½`: `Θ_sQ = (Θ_s-1)/s`, `≤ 4C₈/(cTλ²) + 2`; `ζ > ½`: `‖Θ_sQ‖_{∞→∞} ≤ t₀/(1-st₀) < 2`, diff `≤ 4 ≤ 4𝔡⁻²λ⁻²`.
**D1 (iv) — SIGNED.** `kTwoGUEBA` (probe `:214`: `W^{-d}((BATheta g E m t₁ + gueShift d L (Σ_c Q₀ 0 c) t₁ t • Jmat) * Q₀)_{ab}`,
`Q₀ = BAMss (BAMB g E m) σ₁ σ₂`), `kTwoGUELoopBA`, start `kTwoGUEBA_self` (= `BAKsolve` 2-loop), `T2515_KDerivBA` (premises
`BAReal`, `0 ≤ t₁ ≤ t < 1`, `[NeZero W]`; true by §3), bridge `T2515_KBridgeBA d (fun ζ => 0 ≤ ζ ∧ ζ ≤ 1)` for the 1b.
**Row b entry pin `GUEEntryMixBA` — SIGNED** with §(a)'s open point decided: **`g` in `mixMatBA` is the free family `g n`, the same
coefficient as `M^{(B)} = BAMB (g n) (E n) (m n)`** (the ticket's `λ₀`), not `sz.lam n`. Reason: with `z_u = ztOf (m n) (E n) u
= E + (1-u)m` and self-energy `u m` (block profile `S^{(B)}(0) = I` plus `b/N`), `(gΨ - z_u - u m)⁻¹ = BAMB g E m` only when the
`Ψ`-coefficient of the matrix equals that of `M^{(B)}`; the consumer reaches `u < 1` by the scaling `√u(λΨ + V) = (√u λ)Ψ + √u V`,
so it instantiates `g n = λ₀ = √t₀ λ ≤ 𝔡⁻¹`, which a pin fixed at `sz.lam n` would not allow. Text: band `GUEEntryMix` (`EntryTail:94`)
binder for binder (`𝔠 𝔡 sz`, `sz.Admissible 𝔠 𝔡`, `κ`, `n0 K`, `a b` with `0 ≤ a,b`, `0 < a+b < 1`, `c₀ δ`, `τ D`, `∀ᶠ n`), with
`|E n| ≤ 2-κ` ↦ `∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal d (sz.L n) (g n) κ (E n) (m n)`; law `ouP (UNModel.band (sz.withLam 0)) n`
(= `ouP (UNModelC.ba sz).toUNModel n`, `UNPins:467`); matrix `(g n) • PsiI + mixMat (sz.withLam 0) n (a n k) (b n k) ω`;
`llErr`/`maxLoop` with `M^{(B)}(g n,E n,m n)` at `ztOf (m n) (E n) u`; no `∃ C`. Consumer: C5's PathBounds twin via the EntryGrid
twin (owner C5, §337 (5)). No registry line (band `GUEEntryMix`: 0 lines in `Test/Axioms.lean`).
**Census — SIGNED** (reproduced, §3). **Split — SIGNED: a | b at `GUEKPrim` | `GUEEntry`** (total central 2,762 > 1,950); row a
`t/T2515` (targets 1–8, central 1,114; 1,069–1,426 < stop 1,500); row b `t/T2515b` (targets 9–13, central 1,648 ≤ 1,950: **no b | b′**;
calibrated top 2,109 > 1,950 → forecast check at the 1b head). Row b files: `GUEEntry` ≤ 1,300 + `GUEEntry2` ≤ 700; 2,000 per file binds.

## 5. Stop lines
| stop line | status |
|---|---|
| file > 2,000; row central > 1,950 | not hit (1,114; 1,648 after split) |
| D1 (i) needs `W^{τ'}` or a premise outside coverage | not hit (compiled at ζ = 0; all-ζ route uses rows 8, 10, 11, 13) |
| D1 (iii)/(iv): no text serves N2 and C5 | not hit (one `T2515_ProfSpec`) |
| merged statement/file changed; `private` deleted | not hit (diff: probe only) |
| V module/name read | not hit (closures: 0 V modules) |
| public result with unregistered unproved `Prop` premise | not hit (probe: none) |

## 6. Verdict per deliverable
Fill-in rows (i)–(xi): all present (§(a) table, instance, D1 decisions, coverage as used, census, pin text, greps, registry,
imports, lines, name clash: 0 hits rechecked for the 13 planned names; `UNOUProfile.ba` 2 docstring hits only). Probe `lake env lean`
exit 0, standard axioms, no `sorry`. **PASS.** No dispatcher sign-off requested; the 1b rows may start per §337 (1).

## 7. Observations (no statement/instance/build/axiom effect)
1. Registry lines moved on `main` b2326aac: `UNG1Rowk` `:169`, `UNOUProfRowk` `:170` (`a47cf1e1`: `:170`, `:171`; `grep -n`). The 1b edits
   by content (the `UNG1Rowk` comment, the `UNOUProfRowk` line); §(a)'s "`:171` … checked by `sed`" is off by one on b2326aac.
2. Probe items over the ticket budget: oscillation 74/60, profile 27/25; budgeted items 184/200 by §(a″)'s count; cap 300 kept (287).
3. `$HOME/scr_c3/census2.py` absent; the reconstructed script reproduces within 2.1% of the ticket per row.
4. `stable_mixBA` (matrix `M^{(B)}` in place of scalar `m`) is unpriced BA-only work in row b (§(a)); margin to 1,950 is 302.
5. Paper deltas: none on file for T2515 (`grep -c T2515 docs/paper-deltas.md` → 0, expected at 1a). The 1b reports should cover,
   besides `T2515a`/`T2515b`, the matrix-valued GUE-phase 2-loop at the flow point (`kTwoGUEBA`, row-sum shift) and the free-`g`
   family form of `GUEEntryMixBA`.
6. Ticket Layout ("`GUEEntry2` past 1,800") and stop lines (1,300 + 700) disagree; signed reading: stop lines, 2,000 per file binding.
