Auditor model: claude-opus-5-5

# T2457 1a-audit round 2 (design gate): RETURN, needs dispatcher sign-off

Date: Mon Oct 12 16:40:01 UTC 2026. Audited: (a‴) of `docs/reports/T2457-prove.md` (`:154-273`), against round-1 items 1-7,
CONTROL H249 (2) (decision (B)), H250 (3) (UBA-C1, DECISIONS §269 (2)), H250 (4) (fill-in table), H251 (2). Probe
`RBM3D/Probe/T2457Pins.lean` at `t/T2457` = ee3d8a0 (unchanged). My worktree: `../RBM3D-wt/T2457-1a-audit2`, detached at ee3d8a0,
with its own `.lake/build` (APFS clone). main = a1412ad. Scratch: scratchpad `T2457/aud2/`.

## 1. Probe recompile, diff, G1
```
$ cd ../RBM3D-wt/T2457-1a-audit2 && lake env lean RBM3D/Probe/T2457Pins.lean   -> exit 0; lines matching error|warning: 0
'RBM.BA.bandStep34_LCompat' / 'bandFM_STSEforLn' / 'stek_sumNdecaygL_band' / 'stek_sumRes2gL_band' / 'stNewPQgL_band' /
'probe_feed' / 'bandFM_STLmaxU' depends on axioms: [propext, Classical.choice, Quot.sound]   (7 lines, verbatim each)
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2457Pins.lean ; wc -l  -> 0 ; 296
$ git diff --stat main...t/T2457  -> RBM3D/Probe/T2457Pins.lean | 296 +   (1 file)
$ git diff main...t/T2457 -- RBM3D/Induction RBM3D/Chain/Carrier.lean RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean | wc -l -> 0
$ git diff --name-only ee3d8a0 main -- 'RBM3D/*.lean'  -> Chain/DecayGen, DecayGenTw, Step5Gen, Graph/BAS3Close{,B,C} (new), Test/Axioms
```
No probe import changed between the probe base and main.

## 2. Reruns of every (a)/(a‴) script (prover scripts, output diffed against the report)
```
$ python3 -I r3/layout.py; python3 -I r3/deps.py | diff - <(sed -n 174,189p T2457-prove.md)  -> identical
$ python3 -I r3/scope.py | diff - <(sed -n 193,209p ...)   -> identical
$ python3 -I r3/kinds.py | diff - <(sed -n 212p ...)       -> identical
$ python3 -I r3/uba.py   | diff - <(sed -n 232,241p ...)   -> identical
$ python3 -I r3/est.py   | diff - <(sed -n 257,268p ...)   -> identical
$ python3 -I inst.py | diff - <(sed -n 38,53p ...) ; python3 -I lim.py | diff - <(sed -n 58,63p ...)  -> identical, identical
$ bash r3/clash.sh  -> refs scanned 458 ; refs with hits: 4 (checks/T2457-check on a1412ad, t/T2458, t/T2459; t/T2205 probe) = report :251
```
Independent checks:
```
# (i) Step34Gen needs no BA/* import: probe :18-226 + :276-282 (all generic defs, bridges, band class, band instances,
#     sz0 instance) recompiled with ONLY the planned imports Chain.Step2Gen, Induction.Step34PinsP, Evolution.Prec,
#     Induction.NewPQ, Loop.GLoopFlow, plus the A=1 Nonzero threshold example below
$ lake env lean aud2/noBA.lean   -> exit 0; error|warning lines: 0
example (s lam L : ℝ) (hL : 0 < L) : (1 - s) * L ^ 2 ≤ 1 * lam ^ 2 ↔ 1 - lam ^ 2 / L ^ 2 ≤ s   -- compiles
# (iii) the scope table covers exactly the public declarations (auditor regexp of round 1)
$ grep -hE '^(theorem|lemma|def|abbrev|structure|noncomputable def|instance) ' Step34Pins.lean Step34PinsP.lean | names | sort
  vs. the names of the 14 classes of scope.r  -> 131 = 131, diff empty
```
Hand checks of UBA-C1 (c), (d): with `x = gK²`, `lam² ≤ A x`, `a = |1-v| ≥ b = |1-t|`, `r(gK)/r(lam) ≤ A` reduces to
`(A²-A)x² + b(A²-1)x + (A-1)ab ≥ 0` (report `:158`, correct for `A ≥ 1`); `ellT L g u = min (max (g/√|1-u|) 1) L`
(`Defs/Params.lean:32`) gives `ℓ(gK) ≥ ℓ(lam)/√A` when `gK ≥ lam/√A ≥ 0`. (e): `EKFastDecay` (`Evolution/Pins.lean:51`) and
`STEKDecayKgL` (probe :138) quantify `∀ ε D`, `HighProbAt` (`Defs/StochDomAt.lean:82`) is `∀ D, ∀ᶠ l`, and `twSteps` conjunct 4
(`BA/TwistPins.lean:139`) quantifies `∀ τ' > 0`: the step at `ε/2` with `√A ≤ W^{ε/2}` eventually is sound.

## 3. Round-1 items 1-7
| item | status | evidence |
|---|---|---|
| 1 (i) layout, cones, `BA/*` grep | met | §2 reruns; `noBA.lean` exit 0 with the planned imports only |
| 2 (iii) scope table 127 + 4 | met | 131 names, 0 unclassified, classes match ticket `:22-25` |
| 3 (iv) bridge table, one-direction `STEK*gL` | met | `:213-229`; P (probe-compiled) vs E (1b compile fact) marked |
| 4 (v) premise scan, registry | met | two `owedProps` lines `:249-250`; scan rule `Test/Axioms.lean:429-450` read |
| 5 (vi) forms U2 reads | met | `:253-254`, consistent with (B) (`STEKDecaygL = STEKDecayKgL sz.lam`) |
| 6 (vii) lines, `open private` | met | central 756, upper 1,134 < 1,800 < 2,000; `open private` empty |
| 7 record (B) | met | `:157` |
| H250 (4) fill-in table | met | `:160-171`, every row filled |

## 4. H251 (2): target 7 and the shared Ward text (T2457 reaches its 1a-audit first: T2462, T2463 `state: held`)
Target 7 stays the class pin `STNewPQgL d Cls` (probe ee3d8a0 `:192-204`), no Ward-family text in it. Compatibility with
T2463's target 9 compiled (scratch `aud2/ward.lean`: probe `:191-204` + `T2463-check.lean:198-202, 214-224, 228-234`):
```
theorem audit_newPQ_of_wardCls (d : ℕ) (h : T2463_NewPQExpansion d) : STNewPQgL d (fun sz C => T2463_WardCls sz C)
  -- coefficient step: (ξ α)/(2 i (sz.size n) η)^(m-k) = (ξ α) * ((L^d)⁻¹ * (2 i W^d η)⁻¹)^(m-k), `Sizes.size n = (W n * L n)^d`
$ lake env lean aud2/ward.lean  -> exit 0 ; 'RBM.BA.audit_newPQ_of_wardCls' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**Fixed shared text:** `STNewPQgL` exactly as probe ee3d8a0 `:192-204` (quantifiers `∀ m σ A, ∃ ℓ k ξ σ' ι A'`, then
`∀ sz C, Cls sz C → ∀ n τ, 0 ≤ τ → τ < 1 → ∀ ω a`, coefficient `(ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)`,
both the `C.L` and the `C.K` identity). The Ward family/class text (`WardFam`, `WardCls`) is T2463's, not fixed here
(T2462 D1 vs T2463 is between those two rows).

## 5. Decision (B) and UBA-C1
- (B) recorded; `STEKDecaygL` stays `STEKDecayKgL sz.lam` (probe :143); §269 (2) last bullets replace §268 (3)'s BAdom
  conversion owed by U3-BA with (e) generic in `Step34Gen`: the (a‴) reading at `:158`, `:271` agrees with DECISIONS `:2469`.
- A-form Nonzero (`(1 - s n) * L n ^ 2 ≤ Aof κ * gK n ^ 2`, band `Aof = 1` equivalent, §2 example): met. (c)-(e) in `Step34Gen`
  within the stop line ((vii) 115 lines): met. §269 (2) cited: met.
- **Defect: the comparison hypothesis is not the UBA-C1 text, and the (a‴) form fails at the band.**
```
$ grep -on 'Cmp(A): [^`]*' T2457-prove.md               -> 158: Cmp(A): ∀ n, 0 < gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2
$ grep -on '比较假设\*\*：`[^`]*`' DECISIONS.md            -> 2461: ∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2
$ grep -on 'one comparison hypothesis `[^`]*`' CONTROL.md -> 191: (H250 (3)) same text as DECISIONS:2461
$ grep -on 'literal `[^`]*`' T2462.md ; grep -on 'second comparison form' T2462.md
  74: literal `∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`   110: second comparison form   (T2462 reuses T2457's (c)-(e), :60, :145)
$ sed -n 138,146p;163,165p Defs/Sizes.lean   -> `lam : ℕ → ℝ` has no sign field; `WO 𝔡 := ∀ᶠ n in atTop, W^(-d/2+𝔡) ≤ lam n ∧ lam n ≤ 𝔡⁻¹`
$ python3 -I aud2/cmp.py
§269 Cmp at gK=-2lam: True | (a) t<=1-lam^2/L^2 => t<=1-gK^2/L^2: False
BA lam<0: g0<=lam: False | 0<g0: False | squares g0^2<=lam^2<=A g0^2: True
```
  1. (a‴) adds `∀ n, 0 < gK n`: a second comparison form against §269 (2) / H250 (3), and against T2462's binding literal (`:74`, stop line `:110`),
     which reuses this row's (c)-(e).
  2. Its claimed band instance "`gK = sz.lam, A = 1`" (`:158`) needs `∀ n, 0 < sz.lam n`, and `Admissible`/`WO` give that only eventually.
     So every downstream generic theorem with this hypothesis would lose its band reading for a general admissible `sz`.
     At BA, "U3-BA owes only `Cmp` from `TwistStep2_lam0_sq`" (`:158`) is false too: that lemma (`BA/TwistStep2.lean:740-741`)
     gives only the squares `lam0² ≤ lam² ≤ ((κ+1)/κ) lam0²`, not a sign.
  3. Without a sign, the §269 (2) text itself does not give (a) for every `n` (first script line). (a) needs `gK n ^ 2 ≤ sz.lam n ^ 2`
     for every `n`, because `STEKWinKgL`'s window is `∀ n` (probe :136). At BA, `gK n ≤ sz.lam n` also fails at any `n` with
     `sz.lam n < 0` (second line). So no repair inside the current rule text proves (a), (d) and (e) and discharges the hypothesis
     in both models. The fix picks the shared UBA-C1 text, which binds T2455 R2, T2459 and T2462: that is the dispatcher's decision.
  - Options (auditor's analysis; dispatcher decides):
    (α) the squares form `∀ n, gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (`TwistStep2_lam0_sq` verbatim at BA; trivial at
    the band). Signs come only eventually, from the forms' `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹` and `Admissible`. Then (a) holds for every `n`,
    (c) holds for every `n`, and (d) and (e) hold eventually.
    (β) keep the §269 text and read the five forms' window at `sz.lam` (`STEKWin`, §269 (2) first bullet: "windows of generic Step
    statements read `g = sz.lam`"). U3-BA then proves stage E's window at `lam0` from the squares. But `gK ≤ lam` at BA still needs
    `∀ n, 0 ≤ sz.lam n`.
    (γ) keep (a‴)'s form and add `∀ n, 0 < sz.lam n` to every band specialisation (precedent `BAFlowMember`, `BA/Step1Boot.lean:136`).
    T2462 `:74` then changes.

## 6. Binding stop lines (ticket `:85-92`)
No file passes 2,000 lines ((vii)). Content-binding pins and TLF-C5 are `Iff.rfl` (round 1 §2; probe unchanged). No forbidden item,
field or kernel (noBA.lean, §2). `Step34Pins`/`Step34PinsP` are untouched (G1 empty). D3 has a class shape fed by stage E (probe :229-274).
No unregistered premise is planned ((v)). **Not met: the UBA-C1 conformance in §5** (CONTROL H250 (3) is binding for every stage).

## 7. Paper deltas
`T2457a` (`:152`, `:272`) covers the coupling `gK`, the bulk `κ`, the A-form Nonzero and the comparison hypothesis. It must
follow the final comparison text.

## 8. Observations (no RETURN by themselves)
- `:159` "coefficient `ξ/(2 i N C.eta)^{m-k}` equals T2463's `(L^{-d} κ)^{m-k}`" drops the factor `ξ` on the right. The compiled form is in §4.
- Many bridge kinds are "E" (expected, `:217-227`). They are compile facts owed to 1b and are checked at stage 2.

## 9. Verdict
**RETURN, needs dispatcher sign-off** (§5 defect; H183 (3): 1b does not start). Round-1 items 1-7, (B), the A-form Nonzero,
(c)-(e) placement and H251 (2) are met. Probe: exit 0, standard axioms.

### Required for resubmission (append as (a⁗) with a `date -u` time; do not edit (a)-(a‴))
1. Dispatcher: fix the one comparison text for T2457's (a), (c)-(e) and its UBA-C1 sharers (options (α)/(β)/(γ), §5).
2. Prover: restate `Cmp` in (a⁗) as the dispatcher's literal text, and give, by script, its band discharge (`gK = sz.lam`,
   `A = 1`, for a general admissible `sz`) and its BA discharge (`gK = BAflowLam0 sz z`, `A = (κ+1)/κ`, from `TwistStep2_lam0_sq`,
   `TwistStep2_T0_ge`, `BAflow_lam0_window`, with any sign hypothesis named).
3. For each of (a), (c), (d), (e), state its hypotheses: `Cmp`, any sign condition, and whether it holds `∀ n` or eventually.
   Rerun `uba.py`, extended with a case `gK n < 0` (or `sz.lam n ≤ 0`) at finitely many `n`.
4. Update the `T2457a` paper-delta text and the (vii) line count if the form or the window placement changes.
