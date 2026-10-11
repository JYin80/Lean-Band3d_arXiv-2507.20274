Amend 2 to T2398 (dispatcher V2, Sun Oct 11 07:41 UTC 2026; DECISIONS §223; Jun's choice of route R1, 2026-10-11 ~03:2x UTC; supervisor `docs/supervisor/2026-10-11-0652.md` (TL1, TL2: **PASS**, conditions C1–C4, paper delta T2398d); `docs/tickets/T2398-analysis-fable.md` §2, §6; `docs/tickets/T2398-TL-proofs.md`). Resumes T2398 from `held` (H195) for a short design update and then the report-only merge.

- **D1 (the §8 input is decided).** Route R1: the twisted loop laws TL1 (Lemma T.7) and TL2 (Theorem T.12), reviewed and passed. They enter the BA chain as **owed text pins**, with the standing of `STLKgL` (0652 Q3). Their producers form a new BA stage (0652 C4; its opening REQ is the dispatcher's); they are **not** stage-L rows.
- **D2 (probe: replace `BATwistLaw`).** In `RBM3D/Probe/T2398Pins.lean` (section `Twist`), replace `BATwistLaw` (probe `:276-287`, with its `∃ Kt`) by:
  - **`BATwistAvgLaw C μ τ`** (TL1): the first conjunct of `BATwistLaw` as it stands (`PrecL … ‖twTr C n (τ n) ω c₁ c₂‖ … Bctl`), for every ordered pair. One charge is enough (0652 C3: `T̃_−` is a conjugate of `T̃_+`).
  - **`twK`**, the explicit twisted tree (0652 C2; proofs T.1): `twK n σ a c₁ c₂ := (W^d)⁻¹ * Σ_{a'} Θ^{(σ₁σ₂)}_n(a,a') * M^{(B)}(σ₁)_{c₂a'} * M^{(B)}(σ₂)_{a'c₁}`. Take `Θ` from the carrier's propagator; the kernel of `Θ` is `M^{(σ₁σ₂)}`, the entrywise product (`|M^{(B)}|²` for `(−,+)`, not `M∘M`).
  - **`BATwistLoopLaw C μ τ`** (TL2): `PrecL … ‖twL2' C n (τ n) ω σ a c₁ c₂ − twK …‖ … (Bctl)^{3/2}`. Here `twL2'` is the **uncircled** twisted 2-loop `Tr(G(σ₁)E_aG(σ₂)P_{c₁c₂})`. Quantify over all `σ ∈ {±}²` and all `(a, c₁, c₂)`, per `τ` like `STLKgL`. The exponent is 3/2.
  - **Index convention (0652 C3).** The probe's `twTr n t ω c₁ c₂` is `T̃_{(c₂,c₁)}` of the proofs, and `twL2 … a c₁ c₂` is `L̃_{(a;c₁,c₂)}` (circled leg at `c₁`). Fix one convention in a docstring and use it in `twL2'`, `twK` and the circled/uncircled relation (proofs A.2).
  - **Statements only, no proofs required in the probe:** `twFold` (proofs T.2/(B.2)), `twWard` (T.3) and `twK_bound` (T.1(i)–(ii)). They are model-free and are priced as one stage-L row (below).

  Recompile the probe (exit 0, standard axioms). The probe limit is raised to 500 lines for this amend.
- **D3 (row table, design §7, rewritten under R1).**
  - **L4b2** becomes the twin of `LWExpI1K`/`LWExpI41K` (`LWExpTerm4.lean`) with `(twL2', twK, twTr)` in place of `(L^{(2)}, K^{(2)}, Tr(G̊E))`, assuming `BATwistAvgLaw`, `BATwistLoopLaw`. Re-price it; the analysis estimates 700 / 1,000 / 1,800.
  - **L4a2's assembly** gets the two pins as hypotheses.
  - Add one row **L4t** (`twFold`, `twWard`, `twK_bound`, the circled/uncircled lemma; about 450 lines, model-free; its kind and role are for you to set).
  - Re-state the order (design §7 last line). L4a, L4b and the L4a2 assembly no longer wait for §8; they wait only for their inputs.
  - Do not price the producers of TL1/TL2 here (the new stage).
- **D4 (paper delta).** Record **T2398d** in the supervisor's wording (0652 Q4): TL1 is a lemma in §8; TL2 is a fifth hypothesis and conclusion of Theorem 8.2.
- **Process.** `prover-max` (design update; the probe is compiled in the same step) → auditor (checks D2–D4) → rule (A) **report-only merge** (state, prove, design, audit reports; the probe stays on `t/T2398`). Report: append a section (b′) to `docs/reports/T2398-design.md`, ≤ 120 lines.
