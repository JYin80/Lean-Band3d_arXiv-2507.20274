Auditor model: claude-opus-5-5

# T2348 audit (round 1) — LW-13b-D design (report only) — Fri Oct  9 00:44:50 UTC 2026

Branch `t/T2348` at `9f3bd75` (merge-base `692a72b`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2348-audit1` (detached).
Inputs: ticket `docs/tickets/T2348.md`, `docs/reports/T2348-prove.md` (289 lines), `docs/reports/T2348-design.md` (332 lines).
Acceptance (ticket): report answers items 1–7 with file:line evidence; probe builds (`lake env lean`, exit 0), standard axioms,
no `sorry`; `git diff --stat main...t/T2348` lists only the sole writable files.

## 1. Build, axioms, hygiene, scope (script output)

```
$ lake env lean RBM3D/Probe/T2348Pins.lean        # exit 0, 6.4 s; grep -c error = 0
'RBM.Probe.T2348.WExp.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.WExp.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.ProvOut.Molecular.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.CoverBy.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.lwEngineProv_imp_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.gtoAGRooted_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.LWf_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.norm_add3_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.sum_ball_inf_min_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.sfT_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.lwTail32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2348.ProvOut.molecular_id' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D.Probe.T2348Pins | tail -1
Build completed successfully (3898 jobs).          # warnings only in merged files (longLine), none in the probe
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2348Pins.lean   # (no output)
$ git diff --stat main...t/T2348
 RBM3D/Probe/T2348Pins.lean | 598 +++++  1 file changed       # probe ≤ 600 lines; reports live in the main worktree
```

## 2. Statement checks per ticket item

**Item 1 (provenance).** `LocStepXProv` (probe 157), `WExp` (77), `WExp.prod` (111) compiled; constructor table in
design §2. Spot-check of the cited lines (all match):
```
LWEngine.lean:391  inductive LocStepX ... | weight :392 | edge :395 | gg :400
LWEngine.lean:418  theorem LocStepX.eval ... : LocStep m (lwEvX m (t0, P)) (...)   # list level, no labels (design §1 correct)
LWWeightExp.lean:1333-1340  hL: ∫ Γ.val = Σ_{ℓi} ∫ Γ.term (Sum.elim ℓe ℓi); simp_rw [owx_term_integral ... ℓe]  # pointwise
LWEdgeExp.lean:654 oe1x_term_integral; LWGGExp.lean:1243 oe2x_term_integral; LWVocab.lean:884-886 Φ, hlab (old = new ∘ vmap)
LWLvl1.lean:3236 lvl1EdgeOuts0; :3373 lvl1_val_zero_of_xself; :3590 lvl1_step_identity
```
`lwEngineProv_imp_localregularX` proves `LWEngineProv` strengthens the merged `lw_localregularX` (no weakening). PASS.

**Item 2 (domains).** Design proposes route (R) (rooted `GtoAG`, exact domains), with (E) (enlarge by `Rb`) worked out
as fallback; `gtoAGRooted_imp : LWGtoAGRooted d → LWGtoAG d` compiled (consistency with merged). The ticket's cost
`sT(ℓ-Rb)/sT(ℓ) ≤ e^{½√(Rb/ℓ_t)}` is shown false; independent check from `sfT` (`Kernel/PropT.lean:469-471`):
```
$ python3 -I -c '... sf(s)=((s+1)^(d-2))^-1/2 * exp(-1/2 sqrt(s/ℓ)) ...'
d=3 rho=100 ell_t=4: sfT(0)/sfT(rho)=122.4325  e^{1/2 sqrt(rho/ell_t)}=12.1825  (rho+1)^{(d-2)/2}e^{..}=122.4325
```
so `sfT_shift_le` (probe 407) is the sharp form (delta `T2348a`). Radius question answered: `lwMomExpFar_farDAnd`
(`LWMomExpFar.lean:42`) and `lwMomExp_nearD` (`LWMomExp.lean:532`) take `ℓ`, but `AnpFarAndAt :80` / `AnpDetNearAt :900`
use one `ℓ` for domain and cap (checked); `domFar_eq` compiled. PASS (route choice goes to the supervisor REQ, design §9 Q1).

**Item 3 (G4).** `LWf_split` (probe 313) is an exact identity for every sample; `dom_union`, `dom_disj` compiled;
domains nonempty at `d=3, L=4, a=0, b=(2,0,0), ℓ=1` (example, probe 569). Paper `7_8:1607-1611` uses `|a₁-a| ∨ |a₁-b|`
(far: max > ℓ; near: both ≤ ℓ); Lean uses the "and" far domain and single-centre near domains as the ticket asks;
covered by `T2344b`. PASS.

**Item 4 (G2).** `LWXiExpClaim` (probe 456) vs merged `LWXiClaim` (`AuxGraph2.lean:951`): `LWPsiAll`, `LWLoop2` replaced by
`LWAssmExp`; radius premise `∀τ>0, ∀ᶠn, √ρ ≤ τ log N` (stronger than merged `ρ+1 ≤ N^τ`); conclusion `LWXiE` (class
`sfT(|·|_∞∧ℓ)+W^{-D}`). `hcmp` is the only use of `LWPsiAll` in the merged proof (`AuxGraph2.lean:1019-1021`, checked).
`lwTail32` compiled with instance at `sz0`. PASS.

**Item 5 (Met).** `EKTTkInf`, `AnpNearInfAt` stated; `sum_ball_inf_min_pow_le` proved from `sum_ball_min_pow_le`
(`Defs/RadialSum.lean:367`, checked). Keyword list is 10 (design B6); I confirmed all 10 lines are `private` at the cited lines.
PASS (see O3).

**Item 6 ((A), assembly).** Token diff of the general pin against the target `LWMomentExp` (`LWPins.lean:342-355`):
```
$ python3 -I tokdiff.py tgt.txt on.txt
replace | target: {_q | probe: {q
replace | target: n}) | probe: n ∧ reg sz n (t n) (ℓ n) q})
replace | target: ‖LWf | probe: ‖LWfD
insert  | target:     | probe: (dom (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n))
```
i.e. `LWMomentExpOn d univ True` is the target up to `LWfD univ = LWf` (`h0` in `LWf_split`). Same RHS for all parts;
`ℓ ≤ (log W)^{10} ℓ_t` comes from `LWAssmExp` (`LWPins.lean:286`), `1 ≤ ellT` (`Defs/Params.lean:39`). PASS (see O2).

**Item 7 (rows).** Three rows with lo/central/hi, roles, sole writable files, dependencies, registry, cuts C1–C3, LW count
47→48→49–51, LW-01 = 52 (design §8). PASS.

## 3. Hidden hypotheses, vacuity, cycles

- No structure with Prop fields carries a hypothesis: `ProvOut`/`ProvOutX` are data only; `LWExpData` is a `Prop` def
  of the 9 merged conjunct-4 hypotheses (`LWEngine.lean:68-75`), discharged at concrete data in the `WExp.prod` example.
- Pins left as `Prop` defs without proof (listed, design §9 "Not claimed"): `LocStepXProv`, `LWEngineProv`, `LWGtoAGRooted`,
  `LWAuxNestedOwnOn`, `EKTTkInf`, `AnpNearInfAt`, `LWXiExpClaim`, `LWMomExpNoExp`, `LWMomExpFarPin`, `LWMomExpNearPin`,
  `LWMomentExpOfParts`. Non-vacuity: `WExp` is satisfiable (`WExp.refl`/`WExp.comp` example); `LWEngineProv`,
  `LWGtoAGRooted` imply merged theorems (compiled). No cycle: probe imports merged modules only.

## 4. Compiled instances (probe 541-593)

`WExp.prod` at the merged data of `lwEngine_inst_step1_identity` (every `LWExpData` conjunct discharged, weights `1`/`1/2`;
the expansion pin `h : WExp ...` stays a hypothesis — R1's pin); `WExp.comp`; `Molecular.comp`; `LWf_split` at `sz0`;
`sum_ball_inf_min_pow_le` at `d=3, L=ℓ=5`; `sfT_shift_le` at `s=10, ρ=4`; `norm_add3_pow_le`; `lwTail32` at `sz0`;
the two strengthenings at the data of `lwEngine_inst_localregularX`. All compile (§1). See O1.

## 5. Paper-delta coverage

Recorded in design §9: `T2344a` (rooted aux vertices / weight on `β^{(k)}`), `T2344b` (three-way split, "and" far
domain, single-centre near), `T2344c` (`(log W)^{3/2}` radius, shift comparability instead of `(eq:Psi)`), `T2344d`
(`claim:TTk` in `ℓ^∞`), `T2348a` (shift factor `(ρ+1)^{(d-2)/2}`), `T2348b` (free `K` in regime (A), `7_8:1602` has `K=1`),
`T2348c` (ticket correction, not a paper delta). Every Lean/paper difference found above is covered.

## 6. Observations (no statement, build, axiom or delta change; carry into the row tickets)

- **O1 (instance).** The `CoverBy.comp` example (probe 559) keeps the initial coverage of `fxyPowGraph 2` as a hypothesis
  `h` (deterministic, decidable at concrete data) and is applied at the identity map; `Molecular`/`Cover` of the real step
  maps are design claims, not compiled. Row R1 must discharge the initial `Cover` at `fxyPowGraph p` and prove `Molecular`
  per constructor (molecule preservation is argued from `nWS` counts, `LWEngine.lean:560`, not from edge identity).
- **O2 (quantifier of `K`).** `LWMomentExpOfParts` quantifies `K` before `p` (pins quantify `p` inside `LWMomentExpOn`),
  while design §7 says "`K` is the card bound of the engine lists", which in the merged proof is chosen after `p`
  (`LWMoment.lean:1805-1806`, `set K := ((outsX ++ errsX).map ...).sum`). The compiled pins remain consistent only if the
  far-pin proof takes the tail radius `r = K(log W)^{3/2}/K_card(p)` (tail `e^{-cr/2}` is still `≤ N^{-b}` eventually)
  rather than `K = K_card`. R3's ticket must fix this choice (or reorder: `∀ p, ∃ K`).
- **O3 (de-privatisation).** `lwMomExp_walk_chain` (`LWMomExp.lean:752`, in the list of 10) mentions the private def
  `lwMomExp_stepFn` (`:710`) in its statement; the twin may need `:710` public too (11 keywords). R2's keyword audit
  should list it.
- **O4 (route).** Route (R) departs from supervisor 2244 R1's enlargement reading and adds row G; it is raised as open
  question (1) for the REQ that the ticket already routes to the supervisor (2244 O2). No dispatcher sign-off needed
  for this audit.
- **O5.** Design Risk 5: `LWExpData` is an unproved premise in `#assert_rbm_axioms`' ledger; R1 must inline it (design §9).

## Verdict

Items 1–7: **PASS**. Probe builds (`lake env lean` exit 0; `lake build RBM3D.Probe.T2348Pins` OK), axioms standard,
no forbidden tokens, diff limited to the probe. Report-only merge of the reports; the probe stays on the branch.
