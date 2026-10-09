Auditor model: claude-opus-5-5

# T2356 audit, round 1: stage 1a (design report + probe, items (1)-(6)), CONTROL H146

Written Fri Oct  9 02:14:26 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2356-audit1`, detached at `t/T2356` = `fe9888f`.
Inputs: ticket `docs/tickets/T2356.md`, `docs/reports/T2356-design.md` (235 lines), `docs/reports/T2356-prove.md` (181 lines), probe `RBM3D/Probe/T2356Pins.lean` (398 lines).
Scope (H146): stage 1a only. The "targets" here are the 1a deliverables: the RBM3D statements of the three 1b targets (Prop pins), the exponent chain, the bridge, the MISS-list table, the token table, the sizes. `Eq729B.lean` is not part of this run and does not exist.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Probe.T2356Pins 2>&1 | grep -v "^✔\|^info\|Replayed" | tail -20
(no `error:` line; the only warnings printed are longLine warnings of the merged Main/QUEFromQDiff.lean:37-44)
Build completed successfully (3818 jobs).
$ ls .lake/build/lib/lean/RBM3D/Probe/T2356Pins.olean
.lake/build/lib/lean/RBM3D/Probe/T2356Pins.olean
$ lake env lean RBM3D/Probe/T2356Pins.lean; echo "probe exit=$?"
probe exit=0
$ lake env lean T2356/ax.lean | sed 's/^.*depends on axioms: //' | sort | uniq -c   # #print axioms of all 16 probe declarations
  16 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^\s*axiom" RBM3D/Probe/T2356Pins.lean | wc -l
       0
$ git diff --stat main...HEAD ; git diff --name-only main...HEAD
 RBM3D/Probe/T2356Pins.lean | 398 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 398 insertions(+)
RBM3D/Probe/T2356Pins.lean
$ wc -l RBM3D/Probe/T2356Pins.lean docs/reports/T2356-design.md
     398 (limit 400)      235 (limit 250)
```
Sole writable files of 1a: probe + design report. The branch touches only the probe; the reports live in the main worktree (hub convention). No frozen signature touched (no merged file in the diff).

## 2. Item 1: the statements (script comparison against the source under the port map)
`T2356/sdiff.py`: RBM2D `gueGrid_eq729` (`Eq729B.lean:531-553` @ 9e0f275) with the ticket's port map applied (`d.L`↦`sz.L`, `Z2`↦`Zd d`, `spectralZ`↦`zt`, `gloop … blockMat`↦`loopL d … (blockMat d …)`, `KLoop.mSig`↦`mSigma`, `kTwoGUE`/`primRhsGUE` gain `d`/`sz.lam n`, size cast ↦ `Nsz`) and each conjunct searched in probe `PinGueGrid729` (85-98) / `Eq729Concl` (53-55):
```
RBM2D gueGrid_eq729 hypothesis binders: ['hκ', 'hτU', 'hn0', 'hsize', 'hE', 'ht1', 'ht10', 'ht0', 'h730', 'hscale', 'hell', 'Kt', 'hKinit', 'hK', 'hK2', 'hB', 'hP']
src probe  Tendsto sz.size
--- probe  0 < sz.lam n
src probe  |E n| ≤ 2 - κ
src probe  0 ≤ t1 n
src probe  t1 n ≤ t0 n
src probe  t0 n < 1
src probe  t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E n) (t0 n)
src probe  (gueScale sz E n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU)
--- probe  ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2
--- probe  sz.STKbound E
--- probe  sz.STKloop n (E n) (t1 n)
src probe  primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I
src probe  kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) (t1 n) s
--- probe  sz.STExp2 E t1
src probe  GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt
--- probe  Nsz sz n ^ δ * ((gueScale sz E n (t0 n))⁻¹ ^ 3 + initTerm
```
The six `---` rows are exactly the departures the ticket names ((a)-(c)) and the design tables (design §1): `hlam` (required by the merged `gueGrid_expect_oneLoop`, `OneLoop.lean:1308`, read: `(hlam : ∀ᶠ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ)`); `hell`, `hKb`, `hKinit` in the form of the merged `Hyp_Kt_detDom` (`HypA.lean:690`, read: same three binders, token-equal); `hB := sz.STExp2 E t1`; loss `N^δ((Nη_{t₀})^{-3} + initTerm(t₁))`. `initTerm` (probe 42-43) is token-equal to the right side of `STExp2` (`Induction/Defs.lean:159-164`, read). Quantifier order kept (fixed `κ τU Λ n0` before `∀ δ > 0, ∀ᶠ n`).
Target 2 (`PinEq747OfEq729`, probe 102-105) vs `RBM2D:1041-1058`: `hE' ht0 ht1` become the eventual `FlowData` (probe 36-39); `H729` becomes `Eq729Concl`; conclusion `OUBody` (probe 58-72). Target 3 (`PinEq747OfInputs`, probe 109-119) vs `RBM2D:1384-1407`: same, plus `hgood : ∀ n, |E'| ≤ 2-κ ∧ 0 ≤ t₁ ≤ t₀ < 1` (RBM2D derives it by `Eq729B_pw`). The conclusion is the body of the merged pin:
```
theorem ueq747_iff (sz : Sizes d) (𝔡 τU : ℝ) : UNOUEq747 sz 𝔡 τU ↔ ∀ κ … ∀ τ : ℝ, 0 < τ → OUBody sz 𝔡 E t τ := Iff.rfl   (probe 75-77, compiles)
```
`hgood` is not a weakening in effect: `goodFlow : PinGoodFlow` (probe 177, proved, standard axioms) produces, for every `(κ, E, t)` admissible, data `E' t0 t1` satisfying `FlowData` and `hgood` at once, and F2 (design §0) shows why the `∀ n` formulas are false at the finitely many `n` with `η_Q ≤ 0` (`Sizes.lam` has no positivity field; `WO` eventual: `Defs/Sizes.lean:177`, read). Recorded as candidate `T2356c`.
Composition: `pin3_of_pins (P1 : PinGueGrid729) (P2 : PinEq747OfEq729) (P5 : PinDerived) : PinEq747OfInputs` (probe 384) compiles: target 3 is targets 1, 2 plus the derived inputs, with `hKb` discharged by the merged `Sizes.stKbound_holds` and `hlam` from `WO`. Verdict item 1: **PASS**.

## 3. Item 2: the exponent chain (links re-read against the merged signatures)
| link | probe / merged lemma | auditor check |
|---|---|---|
| (i) `Bctl(t₁) ≤ 2 calB(η_Q,0)` from `η_Q ≤ 2(1-t₁)` | `bctl_le_two_calB` (192), proved | `zRange` (`Main/ZTransfer.lean:74-79`, read) gives `z.im/2 ≤ 1 - lemT z`, and `t₁ ≤ t₀`: hypothesis holds eventually. F1 correct. |
| (i) initial term → `e₀` | `det_of_prec` (`Endpoints.lean:443`, read: `∀ᶠ n, ξ ≤ N^τ ζ` for deterministic `Prec`), `map_gueH_zero` (`Grid.lean:542`, read: law of step 0 = band flow at `t₁`) | `STExp2` quantifies over all `(σ, a) : (Fin 2 → Bool) × (Fin 2 → Zd)`: bounds `Bk` at `k = 0` for every `(s1,s2,x,y)` of `eq729_one_step`. |
| (i) evolution `t₁ → t₀` | `eq729_one_step` (`Eq729A.lean:731`, read: factor `(1 + Δ·(2NρΛ))`, `Λ = (N etaT(E,t₀))⁻¹`), `gronwall_factor` (364) | `exp(dt·2NρΛ) = exp(2ρ dt/η_{t₀}) ≤ e²` from `h730` and `ρN^{-τ_U} ≤ 1`: matches. `gueGrid_expect_oneLoop` gives `hX`; `gueGrid_loop_duhamel` unused (F4, observation O3). |
| (ii) GUE terms | `Eq729B_arith` (port, `N`-only), `final_729` (359) | `final_729` proved; the port of `Eq729B_arith` is 1b work (N-only, `9 ≤ N` from `N ≥ 3^d`). |
| (iii) (7.26), profiles | `map_gueH_last` (`Grid.lean:559`, read: needs `t1 = (1-ζ(τ))t0`, pointwise in `n` since `gueH` reads only `t1 n, t0 n`, `Grid.lean:77-81`), `lemT_mul_kTwoGUE_pm_eq_profPMTilde` / `_pp_eq_profPPTilde` (`KPrim.lean:275,285`, read: `t₀·kTwoGUE(…,(1-ζ)t₀,t₀,true,false/true) = profPMTilde/profPPTilde sz n ζ z`, need `0 < z.im`) | both profile bridges merged; `0 < η_Q` eventually. |
| (iii) scale and loss | `zt_im_lemma28` (`Semicircle.lean:344`), `lemma28_quant` (`:359`, `1/16 ≤ lemT z`), `qdBoundExp_eq` (322), `assembly_747` (328) | `etaT E u = (1-u) Im mE` (`Loop/GLoop.lean:75`) = `Im zt` (`zt_im`, `Semicircle.lean:182`), so `gueScale(t₀) = N√t₀η_Q` as `assembly_747` uses; constant 12 absorbed by `W^{τ/2}`. |
| derived inputs | `claimA` (279), `h730_hscale_real` (305), `hell_of_scales` (238), `Ld_mul_etaQ` (215) | `τ_U ≤ ouTauMax ≤ 𝔠𝔡/12` (`ZeroModeProfile.lean:78`, read); thresholds W-only, eventual: `PinDerived` (376) is a statement, its proof is 1b (sized in item 6). |
Independent evaluation at the design instance (`T2356/aud.py`, mpmath, own code; `L=4, W=32, ilambda=1/64, E=1/2, 𝔠=1/6, 𝔡=1/10, t = ouTStar`):
```
d=3 N=2097152 etaQ=1.2016e-06 t0=0.9999987590 1-t1=1.7275e-06 etaQ<=2(1-t1):True Bctl/calB=0.7677 I0/Tgt=0.5289 t0*Lam0^3/Tgt=0.1948 t0(Lam0^3+I0)/Tgt=0.7237(<=12) hell L^d(1-t1)/lam^2=0.4529 1/16<=t0<=1:True
d=4 N=268435456 etaQ=5.3102e-08 t0=0.9999999452 1-t1=5.8670e-08 etaQ<=2(1-t1):True Bctl/calB=0.9101 I0/Tgt=0.8146 t0*Lam0^3/Tgt=0.1558 t0(Lam0^3+I0)/Tgt=0.9705(<=12) hell L^d(1-t1)/lam^2=0.0615 1/16<=t0<=1:True
```
These agree to all printed digits with design B1 "the chain at the instance". No link is false; every link is a merged lemma, a compiled probe lemma, or a port of an `N`-only RBM2D lemma. Verdict item 2: **PASS**.

## 4. Item 3: bridge `UNMLOut` → `STExp2 sz E' t₁`
`UNMLOut d` (`Universality/Pins.lean:432-436`, read) needs `STFlow sz κ ε 𝔠 𝔡 z` (= `Admissible ∧ ∀ n, locDomain κ ε n (z n)`, `Induction/Defs.lean:286-287`, read) and `0 ≤ t ≤ lemT z`; its fourth conjunct is `STExp2 sz (STflowE z) t`. The probe proves `bridge : PinSTExp2OfUNMLOut` (182-187) via `goodFlow_aux` (modify `z_n` at finitely many `n`, `queDomain` eventual, `locDomain_nonempty`) and `STExp2_congr` (`STExp2` is `∀ τ D, ∀ᶠ n`). Axioms standard (§1). No new pin; only `STExp2` consumed. Verdict item 3: **PASS**.

## 5. Items 4-6
Item 4: 28 MISS names, each with a twin `file:line`, "not needed", or "re-derive (lines)" (design §4); the declaration-level absence grep is in the prove report B4 (all 0); the cited twin lines are echoed by script in design B4 ("124 citation lines, 26 files, missing lines: 0"). Spot checks (read): `Gres_conjTranspose'` is `private` at `Main/ZTransfer.lean:344` (re-derive, 12 lines: consistent); `STKbound` `Induction/Defs.lean:174`; `profPMTilde` `ZeroModeProfile.lean:88`. Item 5: token table, 16 classes, 48 lines with `^ 2` (design §5, script). Item 6: 1355 / 1687 / 2265, cut at `:784` sized A 658/778/984, B 697/909/1281 (design §6, script). Verdict items 4-6: **PASS**.

## 6. Instances, vacuity, cycles
- Hidden hypotheses: `FlowData` (probe 36) has three explicit eventual equations only; `GUEPathBounds` (`Grid.lean:89-102`, read) is the merged pin of UN-49/50/51 (fields `lk`, `localLaw`), kept as a hypothesis as in RBM2D. No other structure.
- Non-vacuity of the pins' deterministic hypotheses: (a)(ii) instance (`d = 3, 4`, `n = 0`, 27 checks True) and the auditor's run above; `hgood ∧ FlowData` jointly witnessed by the proved `goodFlow`; `hKb` by the merged `stKbound_holds`; `Kt` by `gueK_exists` (`KPrim.lean:749`, design risk 1). `STExp2`, `GUEPathBounds`, `UNMLOut` are other gates' pins (allowed as hypotheses).
- Cycle: none; `pin3_of_pins` composes pins downward; `bridge` consumes `UNMLOut` (owed by ST-6), not any pin of this ticket.
- Compiled instance: the endpoint theorems of this ticket are the three 1b targets; at 1a they are Prop pins (definitions), so §6 item 3 applies at 1b. The probe carries one example (`bctl_le_two_calB` at `SizesInst.sz0`, line 396-397, compiles, nondegenerate: `N = 2097152`, `η = 2^{-18}`). Observation O1.

## 7. Paper deltas
Proposed (design §7, prove (d)): `T2356a` ((7.29) at `t₀` carries `I₀(t₁)`), `T2356b` ((7.47) loss `W^τ𝓑²(X+𝓑)` at the new `η_Q`, profile `Θ̃_{ζ}` of the OU matrix), `T2356c` (`∀ n` facts replaced by good data, formal). `hell`, `hKb`, `hKinit` are the existing candidate `T2352a` (`docs/reports/T2352-prove.md:81`, not yet numbered in `docs/paper-deltas.md`: dispatcher bookkeeping). The new `hlam` of target 1 is the departure of the merged `gueGrid_expect_oneLoop` (T2353). Every statement difference in §2 is covered.

## 8. Observations (no RETURN)
- O1. Only one `example` in the probe; the proved `goodFlow`, `bridge`, `hell_of_scales`, `claimA`, `assembly_747` have no instance. Stage 1b must give each 1b endpoint (and these lemmas if moved into `Eq729B.lean`) a compiled nonempty instance (design §6 plans `Eq729BInst`).
- O2. (a) rows "(i) initial term" (`iff hell`, constant 512) and "(iii)" (`calB_le_two_inv` needed) are superseded by (a′) items 1, 3 and design F1; the probe agrees with (a′).
- O3. The ticket names `gueGrid_loop_duhamel` / `DuhamelC` as an ingredient and an import; the design shows it is not used by `Eq729B` (B2: one docstring hit in the source; consumer is `PathBounds.lean`). For the dispatcher when writing the 1b H-instruction (import list), not a defect.
- O4. Probe comment at line 147 cites `Endpoints.lean:485`; the declaration is at 486 (design cites 486).
- O5. The design's open questions (1)-(5) (design §7) go to the supervisor REQ that the ticket already prescribes after a 1a PASS; no separate dispatcher sign-off is needed for this audit.

## Verdict
Stage 1a, items (1)-(6): **PASS**. Probe builds (`lake build` and `lake env lean`, exit 0), 16 declarations on the three standard axioms, no forbidden tokens, branch diff = probe only, chain links true and grounded in merged lemmas, bridge proved with no new pin. Per H146: report-only merge; the probe stays on `t/T2356`; stage 1b waits for a later H-instruction.
