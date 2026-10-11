Auditor model: claude-opus-5-5

# T2408 (BA-G6a) 1a-audit: design gate — Sun Oct 11 05:24:08 UTC 2026

Inputs: ticket `docs/tickets/T2408.md`; `docs/reports/T2408-prove.md` (a), (G)(i)-(v), Verdicts, (a″), (d); branch `t/T2408` at `0547dc6` (parent `1c25de0`); detached audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2408-1a-audit`. Scratch: scratchpad `T2408/`.

**Verdict: PASS** (deliverables (i)-(v) met; no binding stop line hit; no dispatcher sign-off needed). One binding note for 1b (F1) and observations below.

## 1. Probe recompile (own worktree) and hygiene
```
$ git -C RBM3D-wt/T2408-1a-audit diff --stat main...HEAD
 RBM3D/Probe/T2408Pins.lean | 370 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 370 insertions(+)
$ lake env lean RBM3D/Probe/T2408Pins.lean      # 6.0 s
RBM.BA.GreenLocal_floor_sample_pin : Prop
RBM.BA.baGbEXPii_holds_pin : Prop
RBM.BA.GreenLocal_LocalLaw (d : ℕ) : Prop
RBM.BA.greenLocal_localLaw_pin : Prop
RBM.BA.GreenLocal_Floor (d : ℕ) : Prop
RBM.BA.greenLocal_floor_pin : Prop
RBM.BA.GreenLocal_omega (d : ℕ) : Prop
RBM.BA.greenLocal_omega_pin : Prop
RBM.BA.GreenLocal_Gav (d : ℕ) : Prop
RBM.BA.greenLocal_gav_of_fa_pin : Prop
RBM.BA.BAFAav (d : ℕ) : Prop
RBM.BA.GreenIBP_Omega {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t δ : ℕ → ℝ) (n : ℕ) : Set sz.SeqΩ
RBM.BA.GreenIBP_hll {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t Ψ : ℕ → ℝ) : Prop
exit code: 0
$ python3 -I ax.py RBM3D/Probe/T2408Pins.lean ax_audit.lean; lake env lean ax_audit.lean; echo $?
examples converted: 9
exit code: 0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax_audit.out   -> 9 ; other "depends on" lines -> 0
$ grep -nE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2408Pins.lean; echo grep-exit=$?
grep-exit=1
$ wc -l < RBM3D/Probe/T2408Pins.lean
     370            (limit 400)
$ lake env lean docs/tickets/checks/T2408-check.lean   -> check exit code: 0, error lines: 0
```
Copied premises against the current sibling heads (`t/T2401` is now `e5d286b`, its 1b `GreenMinor3` carries the registry def):
```
aec5a16:RBM3D/Probe/T2401Pins.lean def BAFAav (12 lines vs 12): identical
t/T2401:RBM3D/Probe/T2401Pins.lean def BAFAav (12 lines vs 12): identical
t/T2401:RBM3D/BA/GreenMinor3.lean def BAFAav (12 lines vs 12): identical
t/T2402:RBM3D/Probe/T2402Pins.lean def GreenIBP_Omega (2 lines vs 2): identical
t/T2402:RBM3D/Probe/T2402Pins.lean def GreenIBP_hll (3 lines vs 3): identical
$ git grep -e baGbEXPii_holds -e GreenLocal_ -e greenLocal_ main t/T2401 t/T2402 t/T2407 t/T2409 -- 'RBM3D/*.lean' ':!RBM3D/Probe/*' | wc -l
       0
```

## 2. Numerics rerun (prover's scripts, byte-diff against the pasted outputs)
```
$ for a in inst consts sample; do python3 g6a.py $a > re_$a.out; done; python3 est.py > re_est.out   # all exit 0
inst: identical to prover output
consts: identical to prover output
sample: identical to prover output
est: identical to prover output
```
Independent script (`aud.py`, mine): the GL5 bridge `N^ζW^{-ε₀} ≤ W^{-ε₀/2}` at `ζ = 𝔠ε₀/2` is `N^𝔠 ≤ W`; the (C1) term `ΦΔ` of `GreenCore_theta` (`26/κ²·Φδ²`, `GreenCore.lean:965`) at `Φ = N^{τ₀}`, `δ = W^{-ε'}`, `τ₀ ≤ 𝔠ε'` is `≤ W^{-ε'} → 0`; the floor equality case:
```
n=0: W>=N^c True; bridge True; log(Phi delta^2)=-0.51 <= -eps' log W=-0.35: True
n=10: W>=N^c True; bridge True; log(Phi delta^2)=-2.37 <= -eps' log W=-1.55: True
n=1000000: W>=N^c True; bridge True; log(Phi delta^2)=-11.22 <= -eps' log W=-7.25: True
kappa=0.5: W^-d=0.125 vs (4/kappa^2)*loop_min=0.125 equal: True
kappa=0.25: W^-d=0.125 vs (4/kappa^2)*loop_min=0.125 equal: True
kappa=0.04: W^-d=0.125 vs (4/kappa^2)*loop_min=0.125 equal: True
```

## 3. Design-gate items

**(i) Route — met.** Every band step of `Green/LocalLaw.lean` has a BA replacement with a merged name, "new in G6a", or an owner (FA: `BAFAav`/`BAFamGain`, owner BA-G5b per `T2401-prove.md:183` and T2401 Amend 1 D4; IBP: G5c held, not on the route). Stop condition not triggered. Checked the load-bearing merged signatures:
- GL2 (`BAGbEXPii`, `Step1Boot.lean:108`; `BAGiiGEX` `:79`) from `GreenCore_diag` (`GreenCore.lean:1361`): every hypothesis has a source — carrier facts and `G_uu ≠ 0` from `GreenCore_carrier` (`:1532`, every `ω`, `0 ≤ t ≤ T₀`); LDE events from `baLDEin_holds`; `hΩ` at `δ = W^{-ε'}` from `Ω(ε₀) ⊆ Ω(ε')`, `ε' = min(ε₀, d/2)`; `hwd : W^{-d} ≤ δ²` iff `ε' ≤ d/2`; `hδ`, `hC1`, `hKδ` eventually (`GreenOff_pin_consts :1198`, `GreenOff_ev_small :1235`, needs `τ₀ ≤ 𝔠ε'`); `hstab` from `baStab_holds` (`GreenOff.lean:809`). The right side `8K_BA²(9/4 A_b + X_b)` is linear in `(W^{-d}, Lm)` with coefficients `O(Φ²)` (`GreenCore_R0/Xb/Ab :1348-1357`), and GL1 turns `W^{-d}` into `(4/κ²)Lm` on `Ω`. Same skeleton as the merged `baGbEXPij'_holds` (`GreenOff.lean:1289-1368`).
- GL3: (A) at `ζ = 𝔠ε₀/2` ⇒ `Ω(ε₀/2)`; GL2 at `ε₀/2`; (B). `PrecL` is the uniform `∃ p` event (as used at `GreenOff.lean:1320`), so no extra union bound. Sound.
- GL4: on `{‖Δ‖ ≤ κ/2} ∩ {𝓛max ≤ N^νΨ²}` (probability `≥ 1 - 2N^{-D} > 0` eventually) GL1 gives the deterministic inequality. Sound.
- GL6: `GreenCore_E3` (`:1253`) needs `hG0 : ∀ u, G u u ≠ 0`; it is supplied for every `ω` by `GreenCore_carrier`'s last conjunct, so the averaged identity is deterministic and `GL6` needs no event. Averaging E3 at `x = y = (a,o)` gives `v̄_a − tΣ_b M^{(B)}_{ab}M^{(B)}_{ba}v̄_b = ⟨M𝒦⟩_a`, the form of `BAStab` (`:1268`, `BAMss true true a b = M_{ba}M_{ab}`); `K = 16κ⁻⁴` (`baStab_holds`, `t ≤ 1` from `ba_G_data`, `BA/GreenLDE.lean:55`). Sample residual `8.77e-16`.

**(ii) Interface — met, compiled.** Probe `:225`: `BAFAav d` + GL2 at `ε₀/2` + GL6 ⇒ `BAGbEXPav d` (one `intro`; T2401 Amend 1 D1 form). Probe `:232`: GL3 and GL5 give `GreenIBP_hll`, `∀ᶠ δ ≤ κ/2` and `HighProbAt (GreenIBP_Omega …)` — exactly the premises of `BAIBPDet` (read at `t/T2402:RBM3D/Probe/T2402Pins.lean:201-210`: `(∀ᶠ n, δ n ≤ κ/2) → HighProbAt … (GreenIBP_Omega sz z t δ) → GreenIBP_hll sz z t Ψ → …`).

**(iii) Floor — met.** GL1: `|G_uu| ≥ κ − κ/2`; `GreenCore_loop G a a = W^{-2d}Σ_{o,o'}|G_{(a,o)(a,o')}|² ≥ W^{-d}κ²/4` (def at `GreenCore.lean:374`). Not merged in G3a (grep `floor|inv_Wd` in `BA/Green{Core,Off,Stab}.lean`: 0 lines), so new in G6a; matches the T2390 G.3 sentence `W^{-d} ≤ 4κ⁻² max 𝓛`.

**(iv) Constants — met.** All constants are functions of `(d, κ, 𝔡)`; table at `g = 1/64, 1, 10`, `Λ = 10` reproduced byte-identically; `κ ≤ Im m` at `L = 64` with margins 1.67×/1.37×/1.10×. No `g ≤ W^{-ε}`, no smallness of `‖M − m₀I‖`, no `(Cλ)^{|a−b|}` in GL1-GL6's arguments (they use `|G_uu| ≥ κ/2`, event algebra and merged lemmas).

**(v) Pins, instance, split — met.**
- Pins compiled as closed `Prop`s (`*_pin`), quantifier prefix of `BAGbEXPii` (`κ ε 𝔡`, positivity, `𝔠 sz z`, `BAFlow`, `t`, `ε₀`), fixed parameters before `∀ᶠ n`.
- Nonempty instances: `d = 3`, `sz0`, `zSeq`, `flow_sz0` at `t ≡ 1/2` (GL2 fully discharged; `hinit` / `hFA` left as hypotheses, being the induction's output / G5b's pin), and at `t ≡ 0` (probe `:245-368`) with every hypothesis of GL1, GL3-GL6 discharged, including `STInitialGT2gL` (`G_0 = M`, `𝓛max ≤ W^{-3} ≤ W^{-2} = Ψ0²`) and `hFA` (`𝒦 = 0`). Not degenerate: `L = 4`, `W = 32`, `N = 2^21` at `n = 0`; `Ψ0 = W^{-1}` inside the window.
- Split: central 1235 ≤ 1500 ⇒ one file `BA/GreenLocal.lean`; `hi` 2010 > 2000 ⇒ the pre-fixed cut (S6+S7 → `BA/GreenLocal2.lean` past 1700 lines) respects the 2000-line stop line.

**Paper deltas.** `T2408a` (GL3 without window), `T2408b` (`2 ≤ d` guard), `T2408c` (`PrecL` per-sequence form; second display = `BAGavLGEX`) cover the Lean/paper differences of GL2-GL4, GL6. GL1, GL5 are internal lemmas with no paper statement.

## 4. Findings

- **F1 (binding note for 1b; not a deliverable defect).** (G)(v) "Registry" plans to **retire** `RBM.BA.BAGbEXPii` from `owedProps` at G6a's merge and so to edit `Test/Axioms.lean`. The ticket grants `Test/Axioms.lean` "only if (v) names owed lines" and target 5 says "none otherwise"; (v) names none. Supervisor `2026-10-10-2254.md` Q2 (`:71`, `:172`): "`BAGbEXPii` stays owed (owner BA-G6) until G6b proves it." So 1b proves `baGbEXPii_holds` (GL2) but **does not touch `RBM3D/Test/Axioms.lean`**; the line retires at G6b. The report's own O1 already gives this fallback. Keeping the owed line while a theorem proves it passes the registry check (`Test/Axioms.lean:490-503` only rejects unclassified or revived-refuted names).
- O1. `RBM.BA.BAFAav` is now a def on `t/T2401` (`BA/GreenMinor3.lean`); 1b must not declare a public `BAFAav` (use the literal premise, as GL6 does) to avoid a clash at union.
- O2. (a)(i) row "loss `C_gii N^{2τ₀}`" uses `τ₀ = min(τ/4, 𝔠ε')`, while the merged template uses `min(τ/2, 𝔠ε₀)`; either closes (`2τ₀ < τ`). No statement effect.
- O3. The "(C1) at `Φ = 1`" thresholds in (G)(iv) are illustrative; at `Φ = N^{τ₀}` (C1) still closes eventually (§2, `ΦΔ ≤ W^{-ε'}`). No statement effect.

## Verdict
T2408 1a (design gate): **PASS**. Items (i)-(v) answered with compiled pins, a nondegenerate instance (`t ≡ 0` fully discharged), standard axioms, probe 370 ≤ 400 lines, split plan within the 2000-line stop line, stop condition not hit. 1b proceeds under F1 (no `Test/Axioms.lean` edit).
