Auditor model: claude-opus-5-5

# T2427 audit (round 1): BA-TL TL1a, `BA/TwistAvgA`, `BA/TwistAvgA2`

Audit run Mon Oct 12 00:55-00:57 UTC 2026 (`date -u`), detached worktree `RBM3D-wt/T2427-audit1` at `t/T2427` = `fdb7420` (merge-base with main `0a8176c`).
Verdict: **PASS** for every target (1; 2 (i)-(iv); 3). No dispatcher sign-off needed.

## 1. Statements

**Pins against the probe** (`def` blocks in `RBM3D/Probe/T2427Pins.lean` against the two module files, docstrings excluded; script `pindiff.py`):
```
$ python3 -I pindiff.py
probe defs: 15  identical: twAvgGPM twAvgGPG twAvgS1 twAvgS2 twAvgX twAvgXmax twAvgMomentAt twAvgMoment twAvgSCS twAvgSPrec twAvgT6 twAvgReg BATwistAvgRecAt BATwistAvgRec T2427_TL1b
different: none
probe-only: none
```

**Target 1, frame against `BATwistAvgProd`** (`BA/TwistPins.lean:154-157`, read in the worktree). Merged `BATwistAvgRec` (`TwistAvgA.lean`):
```
3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ K : ℝ, 0 < K ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
    LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgRecAt (baFMz sz z) μ t K
```
`BATwistAvgProd`: the same text with `∃ K : ℝ, 0 < K ∧` absent and conclusion `BATwistAvgLaw`. So the frame and premises are exactly those of `BATwistAvgProd`; `K` sits after `κ ε 𝔡` and before `𝔠, sz, z`. That is the O2 form of `twK_bound` (`TwistPins.lean`, same quantifier position), which the ticket allows. `K` is chosen in the proof as `CM + 1` with `CM = (BAct_rate (k+2) 𝔡⁻¹ κ)⁻¹ * expC k (BAct_rate …)` (`TwistAvgA2.lean:1044-1045`), so it depends on `(d, κ, 𝔡)` only and does not depend on `p`. That matches C1 and TP:96.

**Target 1, conclusion against TP:89.** `BATwistAvgRecAt`: `∀ p : ℕ, 1 ≤ p → ∀ ε' D, 0 < ε' → 0 < D → ∀ᶠ n, ∀ c₁ c₂,`
`X^{2p} ≤ K(W^{ε'}·Bctl)(X^{2p-1} + Xmax·X^{2p-1}) + 2p·K(W^{ε'}·Bctl²)X^{2p-2} + N^{-D}`, where `X = twAvgX … c₁ c₂ = (∫‖twTr‖^{2p})^{1/(2p)}`, `Xmax` is the `sup'` over all ordered pairs, and `Bctl n t = W^{-d}·Bparam … t 0` (`Defs/Sizes.lean:214-215`, i.e. the proofs' `W^{-d}B_{u,0}`).
- This is TP:89 term by term with `C_M ↦ K`.
- Natural subtraction `2p-1`, `2p-2` is harmless because `p ≥ 1`.
- The quantifier order (fixed `p, ε', D` before `∀ᶠ n`, uniform over pairs) is the ticket's.
- It holds at one charge and at a fixed time sequence `t`, as in the merged `BATwistAvgProd`/`BATwistAvgLaw` (TL0). That is not a new delta.

**Target 2.**
- (i) `twAvgMomentAt`/`twAvgMoment` is TP:86-87 in the mirror form: `Ǧ = −M(V+tm)G`, sum `Σ_c M_{c₁c}·𝔼[X_c(M_{cc₂}+twTr c c₂)Φ]`, `𝒮₁, 𝒮₂` with `S°` and `t` outside, `twTr c₁ c₂ = T̃_{(c₂,c₁)}`. The ticket admits this as candidate T2427a. It has no `3 ≤ d`, which makes it more general.
- (ii) `twAvgSCS` is pathwise CS with the loop pairs of TP:83, mirrored (`(++−−),(c,c₂,c,c₁)` with `(+−),(c₂,c)`; `(−+−+),(c,c₂,c,c₂)` with `(+−),(c,c₁)`). `twAvgSPrec` is `‖𝒮₁‖+‖𝒮₂‖ ≺ Bctl²` uniformly in pairs, from `STLmaxgL` alone. `C_M` is absorbed by `≺` (`StochDomAt`), which is legitimate for a constant.
- (iii) `twAvgT6` is T.6 at an arbitrary probability law, at scale `N`, with no floor `Y' > N^{-C₁}` and with `R ≥ 0`. Its hypotheses are weaker than TP:60, so the conclusion is the same or stronger (T2427b). The threshold `∀ᶠ n` is uniform in `v` and `Y`.
- (iv) `twAvgReg` gives:
  - continuity of `twTr`, `𝒮₁`, `𝒮₂` and `𝓛¹−m`;
  - integrability of `‖twTr‖^p` for every `p`;
  - pathwise envelopes `η⁻¹+1` and `N(η⁻¹+1)³`;
  - eventually `η_t⁻¹+1 ≤ N`, uniformly in `t ≤ T₀`.

  This covers what TL1b's Markov step needs (TL1b plan, prove report (a″)(iv)).

**Interface** `T2427_TL1b := ∀ d, BATwistAvgRec d → BATwistAvgProd d` is statement only, with an `Iff.rfl` check (`TwistAvgA2.lean:1219-1222`). That is as the ticket requires.

## 2. Vacuity, hidden hypotheses, cycles
- No structure is introduced. Every hypothesis is in the signatures above.
- The premises `LWAvgLawgL` and `STLmaxgL` are other gates' pins, with the frame of the merged `BATwistAvgProd`. The prove report (a) gives their limit check along `sz0` (`Bctl_n → 0`, `C W^{ε'} Bctl_n ≤ 1/2` from `n = 6`).
- No cycle. `BATwistAvgProd`/`BATwistAvgLaw` occur only in the docstring line `TwistAvgA.lean:146` and in the statement-only `T2427_TL1b`:
```
RBM3D/BA/TwistAvgA.lean: lines=1085 sorry/admit/axiom/native_decide=0 Step2Gen_/STthetaOpg=0 BATwistAvgProd|Law=146
RBM3D/BA/TwistAvgA2.lean: lines=1228 sorry/admit/axiom/native_decide=0 Step2Gen_/STthetaOpg=0 BATwistAvgProd|Law=1219,1221,1222
```
- Imports are merged modules only. None of the imported upstream files changed between the merge-base and main:
```
$ git diff --stat 0a8176c main -- RBM3D/BA/TwistPins.lean RBM3D/Chain RBM3D/BA/FlowPins.lean RBM3D/Defs/Sizes.lean … RBM3D/BA/CombesThomas.lean | tail -3
(empty)
```

## 3. Compiled nonempty instances
The datum is `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`), `zSeq`, `flow_sz0`, `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`, `t ≡ 1/2` (`half_lt_t0`). Every deterministic hypothesis is discharged. Only `LWAvgLawgL`/`STLmaxgL` stay as hypotheses.
- `TwistAvgA.lean:1061, 1065`: `twAvgMoment_holds` at `n = 0`, `p = 1, 2`, `c₁ = 0`, `c₂ = ![1,0,0]`. `:1069` proves `![1,0,0] ≠ 0` in `Zd 3 4`. `:1075` gives `twAvgReg_holds` → `‖twTr‖ ≤ N` eventually.
- `TwistAvgA2.lean`:
  - `:1167` is `baTwistAvgRec_holds 3` applied to the datum.
  - `:1174` gives `∀ᶠ n, ∃ c₁ c₂, c₂ ≠ c₁ ∧ <recursion at p=1, ε'=1/10, D=1>`.
  - `:1189` is `twAvgSCS_holds` at `n=0` and a pair of distinct blocks.
  - `:1193` is `twAvgSPrec_holds`.
  - `:1202` is `twAvgT6_holds` with `ξ = ‖𝓛¹−m‖`, `R = Bctl > 0`, `Y ≡ 1`, and envelope from (iv).
  - `:1222` is the interface.

All of these compile (build below). None uses `N = 0`, an empty index, or a `False` premise.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.TwistAvgA RBM3D.BA.TwistAvgA2   (Mon Oct 12 00:56:01 UTC 2026)
Build completed successfully (4007 jobs).        # 0 lines starting with `error`
$ lake env lean ax.lean     # import RBM3D.BA.TwistAvgA2; #print axioms of the six theorems
'RBM.BA.twAvgMoment_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgReg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgSCS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgSPrec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgT6_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistAvgRec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean docs/tickets/checks/T2427-check.lean
check exit=0
$ git diff --name-only main...t/T2427
RBM3D/BA/TwistAvgA.lean
RBM3D/BA/TwistAvgA2.lean
RBM3D/Probe/T2427Pins.lean
$ public (non-stem) declarations of the two files
twAvgGPM twAvgGPG twAvgS1 twAvgS2 twAvgX twAvgXmax twAvgMomentAt twAvgMoment twAvgReg BATwistAvgRecAt BATwistAvgRec twAvgReg_holds twAvgMoment_holds twAvgSCS twAvgSPrec twAvgT6 twAvgSCS_holds twAvgSPrec_holds twAvgT6_holds baTwistAvgRec_holds T2427_TL1b
$ grep -rln -E 'twAvg|BATwistAvgRec|T2427_TL1b|TwistAvgA_|TwistAvgA2_' RBM3D (main worktree) | wc -l
0
```
- The diff touches only sole writable files. The probe is on the branch and is not to be merged.
- `RBM3D.lean` and `RBM3D/Test/Axioms.lean` are untouched (registry: none). The hub adds the two imports at merge.
- No frozen signature is changed.
- Line counts are 1085 and 1228, below the stop line of 2,000.

## 5. Paper deltas
The Lean/paper differences are each proposed as candidates in the prove report (d) (not yet in `docs/paper-deltas.md`: `grep -c T2427` = 0, as expected before merge):
- **T2427a**: mirror orientation `Ǧ = −M(V+tm)G`, the `twTr c₁ c₂ = T̃_{(c₂,c₁)}` labelling, and the mirrored loop pairs of TP:83.
- **T2427b**: T.6 at scale `N`, no floor `Y' > N^{-C₁}`, arbitrary law.
- **T2427c**: `K = C_M + 1` kept, fixed before `𝔠, sz, z`, instead of being absorbed into `W^ε`.

The fixed-time, one-charge form is inherited from the merged TL0 pins and is not new here. Coverage is complete.

## Observations (no verdict impact)
- The 115 helpers are public with the stems `TwistAvgA_`/`TwistAvgA2_`. That is allowed by CLAUDE.md §3 (E). The ticket's wording "private helpers carry the stems" is satisfied by the stem.
- `K` is quantified after `ε` (the window exponent), as in `twK_bound`. Its value is independent of `ε`.

## Verdicts
- Target 1 (`BATwistAvgRec`, `baTwistAvgRec_holds`): **PASS**.
- Target 2 (i) `twAvgMoment_holds`, (ii) `twAvgSCS_holds`/`twAvgSPrec_holds`, (iii) `twAvgT6_holds`, (iv) `twAvgReg_holds`: **PASS**.
- Target 3 (instances): **PASS**.
