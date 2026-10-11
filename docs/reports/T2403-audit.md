Auditor model: claude-opus-5-5

# T2403 audit (round 1) — BA-G4 `BA/GreenOff.lean` (with Amend 1)
Time: Sun Oct 11 04:20:41 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2403-audit1`, detached at `b160f1c` (= `t/T2403`).

## Verdict
- Target 1 (D3.4 weighted closure; `GreenOff_close`, BA form `GreenOff_decay`): **PASS**
- Target 2 (`baStab_holds : BAStab d L g E m t (16 κ⁻⁴)`): **PASS**
- Target 3 (`baGbEXPij'_holds (d) (hd : 2 ≤ d) : BAGbEXPij' d`, Amend 1 D1): **PASS**
- Registry (Amend 1 D2): both owed lines removed; pre-check passes without them (case "remove" applies): **PASS**
- Overall: **PASS**. No dispatcher sign-off needed.

## 1. Diff scope, size, hygiene
```
$ git diff --name-only main...t/T2403
RBM3D.lean
RBM3D/BA/GreenOff.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2403 -- RBM3D/BA/GreenCore.lean RBM3D/BA/GreenStab.lean | wc -l
       0
$ wc -l RBM3D/BA/GreenOff.lean          # stop line 1,600
    1568 RBM3D/BA/GreenOff.lean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/BA/GreenOff.lean | wc -l
       0
$ git diff main...t/T2403 -- RBM3D.lean RBM3D/Test/Axioms.lean   (changed lines)
+import RBM3D.BA.GreenOff                      (after `import RBM3D.BA.KBound`, before `#assert_rbm_axioms`)
-   `RBM.BA.BAStab, -- stability ... (T2390, BA-G3a; owed; owner BA-G3b, `K = 16 κ⁻⁴`)
-   `RBM.BA.BAGbEXPij', -- `lem_GbEXP_BA` `(GijGEX_BA)` ... owner BA-G4 ...
$ git grep -c "baStab_holds\|GreenOff_" main -- RBM3D | wc -l     # name clash on current main
       0
```
Frozen signatures untouched (the pin `BAGbEXPij'` and `BAStab` are unchanged in `GreenCore.lean`).

## 2. Build, check file, axioms (audit worktree)
```
$ lake build RBM3D.BA.GreenOff
✔ [3790/3790] Built RBM3D.BA.GreenOff (12s)
Build completed successfully (3790 jobs).        # no warning line for GreenOff.lean
$ lake build                                      # full library, runs #assert_rbm_axioms
info: RBM3D.lean:445:0: axiom audit: 11378 theorems, 3423 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 119 (borrowed 1, owed 53, structural 46, refuted 6, superseded 13).
Build completed successfully (4213 jobs).
exit 0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2403-check.lean ; echo $?
check file exit 0
$ lake env lean <scratch>/ax.lean
'RBM.BA.GreenOff_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenOff_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStab_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenOff_carrier_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGbEXPij'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The full build passes with `BAStab` and `BAGbEXPij'` removed from `owedProps`: no unregistered-premise error, so the scan finds both proved (`baStab_holds`, `baGbEXPij'_holds`); `GreenCore_diag` (`GreenCore.lean:1378`, `hstab : BAStab …`) is now discharged by `baStab_holds`.

## 3. Statements against the pins (compiled in `<scratch>/ax.lean`, exit 0)
```lean
example : ∀ d : ℕ, 2 ≤ d → BAGbEXPij' d := RBM.BA.baGbEXPij'_holds              -- target 3 = Amend 1 D1 exactly
example (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
  BAStab d L g E m t (16 * κ⁻¹ ^ 4) := baStab_holds d L g κ E m hκ hr t h0 h1    -- target 2
```
- **Target 3.** The type is the merged pin `BAGbEXPij' d` (`GreenCore.lean:1644`, a `def`, not a structure: no hidden field) behind `2 ≤ d` only. Quantifier order is the pin's: `c := GreenStab_clam d 𝔡⁻¹ κ` is chosen after `(κ, ε, 𝔡)` and before `𝔠, sz, z, t, ε₀, D, Φ, Ψ` (`GreenOff.lean:1289-1294`). Inputs: `baLDEin_holds` (merged, unconditional), `GreenOff_carrier_decay`, and `GreenOff_pin_consts` ((C1), (C2), `δ ≤ κ/2`, `2C_ℓ' ≤ K_cl P` for `√P δ ≤ ε'`, constants depend on `(d, κ, 𝔡)` only). Then `τ₀ = min(τ/2, 𝔠ε₀)`, `HighProbAt.inter` over the 4 LDE events and the loop premise. The case `Ω` fails gives `indMax = 0`. Nothing is owed to G6a, and there is no fluctuation averaging. No circularity: `BAGbEXPij'` is not used as a hypothesis anywhere in the proof.
- **Target 2.** It is `baStab_of_real` (`GreenStab.lean:46`, signature printed above) restated as `BAStab` (body `GreenCore.lean:1268`). The hypotheses are identical.
- **Target 1** (ticket mathematics; no Lean pin). `GreenOff_close` (`:580-602`) has 25 explicit hypotheses:
  `hc₀ hγ0 hγ hφ hΨ hΨw hP hκ hδ0 hg ht0 ht1 hdec hS hM hvb hE3 hX hXi hA hD1 hDadj hΘ hΘw hC2`
  Checked against the ticket:
  - **(E3).** `hE3`: `Δ_xy = Σ_{b'} Mb_{[x]b'}[t v̄ M + (t v̄ − 𝒜')Δ − 𝒜'M − 𝔛]` (L1+L2+L3+Q).
  - **Block averages.** `hvb`: `v̄_a = W^{-d}Σ_o Δ_{(a,o)(a,o)}`. `hΘ` gives `Θ = 1 + tΘM^{(+,+)}`, so `v̄ = Θu`.
  - **Sources.** `hX` and `hXi` are the merged (X\*) and (Ξ) forms (`GreenCore_Xstar :1066`, `GreenCore_Xi :1130`).
  - **Kernel preservation.** It is derived from `hdec` and `hS`, with `γ ≤ c₀/4 ≤ c₀/2`.
  - **Θ weighted ℓ¹.** `hΘw`.
  - **(C2).** `(1 + ρ̂c₀⁻¹C_Θ̂)·ρ̂η ≤ ½` with `ρ̂ = c₀⁻¹S`. This equals the ticket's `η(ρ̂ + ρ̂²c₀⁻¹C_Θ̂) ≤ ½`.
  - **Conclusion.** `‖Δ x y‖ ≤ 2·GreenOff_Cl·GreenOff_T γ Ψ φ [x] [y]` for all `x, y`. `GreenOff_Cl` contains the factor `P = Φ_N`.

  `GreenOff_close` is general in `γ ≤ c₀/4` and `CΘ`. `GreenOff_decay` (`:718`) is the BA form. It takes `γ = GreenStab_clam` (`c_λ = min(c₀/12, μ/6)`), `c₀ = BAct_rate`, `C_Θ̂ = GreenStab_CTheta`, and discharges the hypotheses from merged results:
  - `hdec` from `BAMB_decay_large`; `hS` from `BAsum_exp_decay_le`; `ρ` from `baM_col_l1`;
  - `hX` from `GreenCore_Xstar`; `hXi` from `GreenCore_Xi`; `hE3` from `GreenCore_E3`;
  - `hΘ` from `BATheta_resolvent`; `hΘw` from `baTheta_weighted_l1`;
  - `hA` from `GreenOff_Arow_bd` (proved in the file).

  The event hypotheses (`hΩ`, `LDERow/Col/Quad`, diag, (C1), (C2)) are explicit. `GreenOff_decay` is the ticket's "on the event" statement with the D3.4 constants. `hA` (`|t v̄ − 𝒜'| ≤ α`) is not circular: `α = GreenOff_alpha d κ δ g₀` is an a priori bound from `‖G − M‖ ≤ δ`. It is proved, not assumed, at the BA data.

## 4. Compiled nonempty instances (`GreenOff.lean`, namespace `GreenOffInst`; compiled in the module build above)
- **Target 1** (`:1517`). Data: `GreenOff_close` at `d = 3`, `L = 4`, `W = 10^5`, `t = 1/2`, `κ = 1/2`, `c₀ = 1`, `S = 64`, `ρ = P = CΘ = 1`, `g₀ = 1/64`, `γ = 1/12`, `δ = α = 10⁻⁶`, `Θ = (2/3)I`, `Mb = iI`.
  - The array is `Δ = δ(1_{x=y} + ½·1_{x≠y, o(x)=o(y)})`; `Δ ≠ 0` is compiled at `:1526` (`∃ x y, Δ₁ x y ≠ 0`).
  - All 25 hypotheses are discharged by named lemmas (`hdec₁ hS₁ hvb₁ hE3₁ hX₁ hXi₁ hA₁ hD1₁ hDadj₁ hΘ₁ hΘw₁ hC2₁`, the rest by `norm_num`). No premise is `False`, the index sets are nonempty, and `t > 0`.
- **Target 2** (`:1530`). `baStab_holds 3 (sz0.L 0) g0I (1/2) E0I m0I … (t = 1/2)` is applied to the nonzero `δ_0` with `B = 3/2`. The premise is proved, and the `BAReal` datum comes from the merged `GreenStabInst.hr0I`.
- **Target 3** (`:1552`). Data: `baGbEXPij'_holds 3 (by norm_num)` at `sz0`, `flow_sz0` (`κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`), `t ≡ 1/2 ≤ T₀` (`half_lt_t0`), `ε₀ = 1/10`, `Φ ≡ W^{-1/10}`, `Ψ = W^{-1}`.
  - The three window hypotheses are discharged.
  - Only `GreenCore_loopPrem` remains a hypothesis. It is the lemma's own premise `(eq:def_Psit)`, supplied by the consumer. Its limit check is prove report (a)(ii) `prem.py`: `Bctl/Φ² = Bparam·W^{-2.8} → 0`.

## 5. Paper deltas
The prove report (d) proposes `T2403a`–`T2403d`:
- `T2403a`: `2 ≤ d` against the paper's `d ≥ 3`; harmless (Amend 1 D1).
- `T2403b`:
  - the rate `c_λ = min(BAct_rate/12, BAp5s_rate/6)`;
  - `zdistD` in the kernel, which is stronger than the paper's `zdistInf` (`GreenOff_T_le_decayRHS`);
  - the `W^{-D}` term, which is unused;
  - the loss `N^{3τ₀/2}`.
- `T2403c`: the row-form (A\*) and the merged (X\*)/(Ξ) coefficients.
- `T2403d`: the abstract form of target 1, `C_T`, and the shape of (C2).

The `1_Ω` event form of the pin against the paper's `(initialGT2)` setting (`7_8:1917`) belongs to the merged pin (T2390a). Every Lean/paper statement difference found above is covered.

## 6. Observations (no statement, instance, build, axiom or delta effect)
- O1. There is no concrete-data instance of the BA-form `GreenOff_decay` or `GreenOff_carrier_decay`. With the analytic `C_Θ̂ = GreenStab_CTheta` (about 1e162 at κ = 1/2), (C2) holds only for astronomically small `δ`. These two are exercised inside the proof of target 3, and target 3 has a compiled instance at `sz0`. The ticket's instance list (item 5) is met.
- O2. In the target-1 instance, `M = iI` is diagonal and `D` is not linked to `M`. The instance shows that the hypotheses can hold jointly at `t = 1/2` with `Δ ≠ 0`, but its bound is loose (`2C_ℓ' ≈ 3.2e6` against `|Δ| ≤ 1e-6`).
- O3. Kernel preservation is re-proved locally (`GreenOff_convA/convB`) rather than taken from the merged `baM_rhohat`/`baMfine_rhohat`. The prove report says it is the same bound.
- O4. `main` has moved since the branch point `561093a`. T2404 and T2406 edited other lines of `RBM3D/Test/Axioms.lean` and `RBM3D.lean`, so the merge is a rebase-union (H23 (b)). This audit's full build is on the branch, not on the rebased tree; the hub's merge build covers that.
- O5. The file has 1568 of 1600 lines (stop line). Amend 1 D3 (relabel `Test/Axioms.lean:133-135`) is not done here, as the amend directs.
