Auditor model: claude-opus-5-5
# T2205 audit (round 1) — BA-D3: family `BAStep1`/`BAMainInd`, coupling window, ConArg from `s₀ = 1 − c₁`, regime gluing through (A)
Written Mon Oct  5 22:00:19 UTC 2026 (`date -u`).  Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2205-audit1` (detached at `t/T2205` = 96e4087, base cef761a); scratch `S=…/scratchpad/T2205`.  Report-only ticket: the probe `RBM3D/Probe/T2205Pins.lean` stays on the branch.

**Verdict: PASS** (all targets 0–8; observations O1–O5 below, none changes a statement, instance, build, axiom or delta coverage).

## 1. Diff scope, build, axioms, hygiene
```text
$ git diff --stat main...t/T2205
 RBM3D/Probe/T2205Pins.lean | 3989 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 3989 insertions(+)                       # the sole writable Lean file; no merged file touched
$ sed -n 6,14p RBM3D/Probe/T2205Pins.lean | grep import     # allowed imports only
import RBM3D.BA.MFixedPoint / RBM3D.Induction.Defs / .Step2Defs / .Step34Pins / .Step5Pins / .ScaleFacts3 / RBM3D.Loop.KLTree
import Mathlib.Topology.MetricSpace.Contracting / Mathlib.Data.Nat.Nth
$ lake build RBM3D.Probe.T2205Pins          # in the audit worktree
⚠ [3798/3798] Built RBM3D.Probe.T2205Pins (39s)
Build completed successfully (3798 jobs).    exit=0; warnings: linter only (line length, `show`, flexible `simp`); no error, no `sorry`
$ lake env lean $S/ax.lean                  # meta loop: collectAxioms over every constant whose module is the probe
decls=433 axioms_union=[Quot.sound, Classical.choice, propext] nonstd=[]
outside_ns = 5 `_private.RBM3D.Probe.T2205Pins.0.RBM.Probe.T2205.*` + 7 auto `eq_1`/`congr_simp` of merged defs (no public name outside RBM.Probe.T2205)
$ grep -nE "sorry|admit|native_decide|^axiom|[^A-Za-z_.]axiom " RBM3D/Probe/T2205Pins.lean
(no output)
```
Examples are anonymous; they elaborate in the same build with no `sorry` warning, so they add no axiom.

## 2. Statements against the check file (independent compiled comparison)
`$S/chk2.lean` = `import RBM3D.Probe.T2205Pins` + the check file's sections 2–4 **verbatim** (its own namespace `RBM.BA.T2205Check`, not the probe's `Check` copy) + 8 `rfl` equalities + the 5 proofs re-typed at the check statements:
```text
$ lake env lean $S/chk2.lean ; echo exit=$?
'aud1' depends on axioms: [propext, Classical.choice, Quot.sound]   # Check.BAgapReal d        := BAgapReal_holds d
'aud2' depends on axioms: [propext, Classical.choice, Quot.sound]   # Check.BAzztE_inv d       := BAzztE_inv_holds d
'aud3' depends on axioms: [propext, Classical.choice, Quot.sound]   # Check.BAFamCone_closed_stmt d := BAFamCone_closed d
'aud4' depends on axioms: [propext, Classical.choice, Quot.sound]   # Check.BAmWindow d Λ κ    := BAmWindow_holds d Λ κ
'aud5' depends on axioms: [propext, Classical.choice, Quot.sound]   # Check.BAWinBulk_of_dom_stmt d := BAWinBulk_of_dom_holds d
exit=0          # and the 8 `example : probe.X = T2205Check.X := rfl` (BAgapReal, BAmWindow, BAzztE_inv, BAWinBulk,
                #  BAWinBulk_of_dom_stmt, BAFamCone, BAFamCone_closed_stmt, BAFamZ) all elaborate
$ python3 $S/cmp.py     # whitespace/comment-normalised text: check file sections 2-4 vs the probe's `Check` copy
BAgapReal identical / BAmWindow identical / BAzztE_inv identical / BAWinBulk identical / BAWinBulk_of_dom_stmt identical
BAFamCone identical / BAFamCone_closed_stmt identical / BAFamZ identical / examples identical
```
All four deterministic pins of target 2 and the closure statement are **proved** (not owed), exactly at the check-file statements.

## 3. Target 0 (vocabulary) and target 4 (`BAConArg'`) — script against the T2161 (82e72b3) / T2173 (a543154) texts
```text
$ python3 $S/vocab.py      # defs of probe lines 45-478 vs `git show 82e72b3:…/T2161Pins.lean`, `a543154:…/T2173Pins.lean`
vocabulary decls (probe 45-478): 57;  identical to T2173/T2161 text: 30
differ: STMainIndG (L2), STMainInd_iff, STStep1_iff, 12 bandFM_* (L4, compile as Iff.rfl), BAGbEXPpre, BAGbEXPconcl, BAConArgLoop, BAConArgVec (L3)
not in T2161/T2173 (L1 renames): STDecayStronggL STLocalMaxgL STInitialGT2gL STKboundgL STStep1LoopgL STStep1WeakgL STLWassmExpgL, BAConArg'
BAMainInd / BAStep1 (deferred per-flow pins) present in vocabulary region: False / False
--- mechanical L1 (Prec sz ↦ PrecL sz μ, Xg ↦ XgL, argument μ) on the T2161 text
STDecayStronggL True; STLocalMaxgL True; STKboundgL True; STStep1LoopgL True; STStep1WeakgL True; STLWassmExpgL True
STInitialGT2gL False — only `STmaxLoop2g C n` (probe) vs my script's over-rename `STmaxLoop2gL C μ`; T2197 item 4 lists `STmaxLoop2g` law-free/verbatim: probe correct
--- mechanical L3 (law `Sizes.seqP (sz.withLam 0)`) on the T2161 text
BAGbEXPpre True; BAGbEXPconcl True; BAConArgLoop True; BAConArgVec True; BAGbEXP True
$ python3 $S/conarg.py    # T2161 `BAConArg` + L3 + the Amend-1 premise inserted after `(∀ n, t n < 1) →`
T2161 BAConArg + L3 + Amend-1 premise == probe BAConArg': True
```
`STMainIndG` (probe :318) differs from T2161 :1046 only by the law parameter and `…gL … (law sz)` (L2), read by eye.

## 4. Target 1 — family pins `BAStep1`, `BAMainInd` (probe :1695, :1715; statements in prove report b.2, confirmed in file)
Against the ticket shape, quantifier order: `κ ε 𝔡` > (`∀ 𝔠d`, resp. `∃ 𝔠d ∈ (0,1/100]`) > `𝔠 sz z`, `BAFlow` > `∀ c₁ ∈ (0,1/2]`, `BAWinBulk sz z c₁ κ` > `s t`, `0 ≤ s`, `s ≤ t₀`, `s < t`, `t ≤ t₀` > hypotheses for **every** `z'` with `BAFamZ sz z c₁ s z'` > `STConStInd sz 𝔠d s t` > conclusions for **every** `z'` with `BAFamZ sz z c₁ t z'`; law `Sizes.seqP (sz.withLam 0)` throughout.  `BAStep1` hypotheses `STKboundgL ∧ STLKgL s ∧ STLocalMaxgL s`, conclusions `STStep1LoopgL ∧ STStep1WeakgL` = T2161 `BAStep1` :1170 per member; `BAMainInd` hypotheses/conclusions = the five/six of `STMainIndG` per member.  As pinned.
- **One addition**: `(∀ n, 0 < sz.lam n)` in every family pin.  Checked: `WO` (`Defs/Sizes.lean:164`) is `∀ᶠ n`, so `BAFlow` does not give it for all `n`; conclusions are eventual (`PrecL`), consumers pass to a tail.  Weakens the pin harmlessly; proposed as **T2205d**.
- **No vacuity / junk members**: `baFMz sz z'` depends on `z'` only through `(BAflowLam0, BAflowEs)` = `(√τ' g, E)`; `BAt0 z m = Im m/(Im m + Im z)` (`MFixedPoint.lean:279`) with `BASelf` forcing `Im m > 0`, so `τ' ∈ (0,1)` forces `Im z' > 0`, and `BAm = 0` gives `τ' = 0`, below the floor `min(t₀, max(u,1−c₁)) > 0`.  Members at `s` have `τ' ≥ min(t₀, max(s,1−c₁)) ≥ s`: every hypothesis/conclusion is about a genuine flow within its horizon.  Main flow a member at every `u`: `BAFamZ_main` (unconditional, :1294).  `t₀ ≤ 1 − c₁`: family = main flow (`BAFamZ_main_only`, compiled).
- **`BAWinBulk` uses the `BAFlow` κ**; `BAWinBulk_of_dom` gives `κ/2`, so the chain applies the pins at `κ/2`; `BAdom` (`MFixedPoint.lean:435`) is `κ ≤ Im m ∧ …`, monotone in κ by definition.  `c₁` after `sz, z` (F-f) and the same `c₁` in `BAStep1`/`BAMainInd`: as the ticket asks.
- **Paper** (`7_8:1825-1832`, `:1956-1990`): one flow, hypotheses at `s` for that flow; `lem_ConArg_BA` assumes `(loopbound_s)` for the flow `(z_s, ilambda_s)` — another flow.  The family form is a Lean/paper difference, proposed as **T2205b**; the window premise and constants as **T2205c**.
- **Closure, independently** (exact rationals; Lean proofs `BAFamZ_closed` :1478, `BAFamCone_closed`, `BAzSrc_spec` :1420 compile):
```text
$ python3 $S/closure.py
random (t0,c1,u,tau,s), N=100000: violations [member range, source in Fam(s), Fam(u)⊆Fam(s2), main in Fam(u)] = [0, 0, 0, 0]
fixed window c1=3/10, u=4/5, s=3/4: target tau/t0 at bottom 7/10 -> source tau/t0 = 0.65625 < 7/10: True
```

## 5. Targets 3, 5 — skeletons; the (A) input discharged against `main`
- `BAStep1_of_pins d (hT : BATrivialLmax d) (hC : BAConArg' d) (hB : BABootstrap d) : BAStep1 d` (:2101) with `BAFlowMember_holds`, `BALmaxFromLK_holds` proved.  Not circular: `BABootstrap` (:1810) is per member, takes the ConArg outputs from `max(s,1−c₁)` as hypotheses and does not mention `BAStep1`.  Missing link stated: `BAGbEXP` in event form inside `BABootstrap` (**T2205e**).  `BATrivialLmax` (:1779): members of `Fam(0)` at time `1−c₁`; their couplings lie in the window, `η = c₁ Im m ≥ c₁κ`: plausible as an owed pin.
- `BA_mainInd_of_regimes 3 hlaw h₃ h₁ h₂ h₄ : BAMainInd 3` takes `hlaw : BAExactLaw 3`.  Discharged by the auditor with merged T2206 (`main` 5d313ca), compiling the whole probe text in main's environment:
```text
$ cd ~/Lean_proof/RBM3D && lake env lean $S/probe_main.lean ; echo exit=$?   # probe + `import RBM3D.Induction.SizesComp` + below
#   example : szComp sz φ = sz.comp φ := rfl ;  example : szReindex sz φ = Sizes.reindex sz φ := rfl
#   theorem audit_BAExactLaw (d) : BAExactLaw d := fun sz φ hφ =>
#     ⟨fun B => Sizes.seqP_withLam_reindex_preimage sz φ 0 hφ.injective B, fun g => Sizes.integral_reindex (sz.withLam 0) φ hφ.injective g⟩
#   example : BAMainIndR 3 STReg5III → … → BAMainIndR 3 STReg5IV → BAMainInd 3 := fun h₃ h₁ h₂ h₄ => BA_mainInd_of_regimes 3 (audit_BAExactLaw 3) h₃ h₁ h₂ h₄
'RBM.Probe.T2205.AuditExactLaw.audit_BAExactLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0      # the probe also compiles unchanged against main 5d313ca
```
So (A) gives `BAMainInd 3` from the four regime pins with no remaining (A) hypothesis.  `BAMainIndR d STAny ↔ BAMainInd d` (`BAMainInd_iff_any` :2377, proved): the regime form adds only `R sz s t`.

## 6. Compiled nonempty instances (in the probe; build of §1)
| endpoint | instance (line) | data; deterministic hypotheses |
|---|---|---|
| `BAStep1` | `inst_BAStep1` (3532) | `d=3`, `κ=ε=𝔡=1/10`, `sz0`, `zSeq`, `c₁=1/3` (`t₀≈0.694 > 2/3`: nontrivial family), `(s,t)=(0,1/16)`; `BAFlow` (`flow_sz0'`), `0<lam`, `BAWinBulk` (`sz0_win_third`, proved), ranges, `STConStInd` (`conStInd_inst`) discharged; stochastic member premises (other gates) kept |
| `BAMainInd` | `inst_BAMainInd` (3545) | same data, `𝔠d` from the pin |
| `BAgapReal_holds`, `BAzztE_inv_holds`, `BAmWindow_holds` | 3678, 3672, 3663 | one-point flow `(L,g)=(4,10)`, `zS 4 10` (explicit copy of `MFixedPointInst.P`'s construction, O2); no hypothesis |
| `BAWinBulk_of_dom_holds` | 3597 | `sz0`, `κ=1/2`, `Λ=1/64`; no hypothesis |
| `BAFamZ_closed`, `BAFamCone_closed`, `BAFamZ_main` | 3566-3594, 3847-3856 | `sz0`, `c₁ ∈ {1/3, 1/2}`, `s ∈ {2/3, 1/2}`, `u ∈ {17/25, 2/3}` (incl. `u = 1−c₁`), two closure steps |
| `BAFlowMember_holds` | 3762 (via `BAmember_transfer`) | `sz0`, `zSeq`, `c₁=1/3` |
| `BAConArg'` | 3521 | `sz0`, `(s,t)=(2/3,17/25)`; Amend-1 premise discharged (`sz0_conArg_bulk`) |
| `BAStep1_of_pins`, `BA_mainIndR_of_steps` ×4, `BAMainIndR_pat`, `BA_mainInd_of_regimes` | 3696-3726 | `d=3`; owed pins as hypotheses; patterns `(0,0)`, `(0,3)` realised at `sz0` (3733, 3743) |
None degenerate (`N_n ≥ 2.1·10⁶`, `L_n ≥ 4`, nonempty windows, true premises).

## 7. Target 6 (T2001g) — independent spot check (`d=3`, `L=4`, `g₀=2`, `κ=0.1`; exact polynomial roots, 7 distinct eigenvalues)
```text
$ python3 $S/t2001g.py
L=4 g0=2 kappa=0.1: energies |E|<=1.9 with Im m(E,g0)>=0.05 whose coupling path (0,g0] leaves the support: 2
  e.g. E=-1.045: Im m(E,g0=2)=0.1769, Im m(E,g'=0.891)=0.0e+00
iteration check L=4 g=2.000 E=-1.045: eta=1e-03 Im m=1.764e-01, eta=1e-04 Im m=1.769e-01, eta=1e-05 Im m=1.769e-01
iteration check L=4 g=0.891 E=-1.045: eta=1e-03 Im m=2.971e-03, eta=1e-04 Im m=2.971e-04, eta=1e-05 Im m=2.971e-05
```
Agrees with the prove report ((a) (iii), `gap.py`: `L=4, E=-1.045, Im m ∝ η`): `|E| ≤ 2 − κ` does not keep the path in the bulk at finite `L`; **T2205a** as proposed is supported.

## 8. Target 7 (count), target 8 (two data), paper deltas
- BA count at the top of the prove report: `4 used / 66 planned` (cap 70) — within the cap; rows and reasons in portmap P.1–P.4.
- Two-data table and the six extreme inputs: portmap P.6 (every pin row present; extremes `g'` at window bottom, `u = 1−c₁`, `t₀ < 1−c₁`, `c₁ = 1/2`, bulk-edge `E`, `s = 0` compiled or scripted; spot-checked at 3833-3856).
- Lean/paper differences and their candidates: family form and the other-flow ConArg source → T2205b; gap and window constants/premise → T2205c; `∀ n, 0 < lam n` → T2205d; `BAGbEXP` event form → T2205e; T2001g reclassification → T2205a.  `BAConArg'` premise: T2197 Amend 1 (already its delta).  No uncovered difference found.

## Observations (no RETURN)
- **O1** `BALmaxFromLK_holds` (proved helper, not a ticket target) has no concrete instance; it is used only inside `BAStep1_of_pins`.  The porting row (BA-S3) should add one.
- **O2** The one-point instances use an explicit copy `szP`/`zP = zS 4 10` of T2189's construction, since `MFixedPointInst.P` is `Nonempty.some` (`MFixedPoint.lean:893`); same data.
- **O3** `BAExactLaw` is a hypothesis inside the probe (base cef761a predates T2206); discharged here against main (§5).
- **O4** The proved window constant `c₁ = min(1/2, κ⁹/(64dΛ))` is very conservative (prove report b.4: down to `~10⁻¹⁵`); valid, since constants need not be optimal.
- **O5** `BAWinBulk` takes the same κ as `BAFlow`; consumers apply the family pins at `κ/2` (via `BAWinBulk_of_dom`).  BA-V2b/BA-M1 must write this step explicitly.

## Verdict per target
T0 PASS · T1 PASS · T2 PASS (all four proved) · T3 PASS (skeleton; missing link named, T2205e) · T4 PASS · T5 PASS ((A) discharged against main) · T6 PASS · T7 PASS (66 ≤ 70) · T8 PASS.  **Overall: PASS.**  No dispatcher sign-off needed beyond the supervisor re-check that the ticket already schedules (§68 (1)).
