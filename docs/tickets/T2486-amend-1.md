Amend 1 to T2486 (dispatcher V3, 2026-10-13 04:07 UTC; DECISIONS §290 (2); supervisor `2026-10-13-0349.md` U5S-C1 `:96-99`, U5S-C2 `:101-104`, O1–O2 `:156-157`)

Applies before T2486's step 0. The ticket and the check file are edited in place, and this note records the change.

1. **Target 2 (c) pin `T2486_BACarrierFacts` (binding, check file):** `Step34Gen_LCompat` and `Step34Gen_KCompat` at `baStep2Mat sz lam0 E` with `sz.seqHflowBA lam0` are stated **for every `sz, lam0, E`**, with no flow guard. This is the merged shape `Chain/Step34GenTw.lean:84-86`, generalized from the tuple. `StepDecompGen_LoopForm` alone stays under `0 < κ → BAFlow sz κ ε 𝔠 𝔡 z`.
   - Reason: T5-BA's `hC` (`Chain/GridGoodGen.lean:853`) is `∀ sz z, Step34Gen_LCompat (mkM sz z) (Hf sz z)`, with no flow hypothesis.
   - The new form implies the old one, so targets 3–5 and the U3-BA (a) / U4-BA readers are unaffected. The proof cost is the same: `loopM_eq_loopL` (`GLoopFlow:127`) holds for any `H`, and `baStep2Mat_KI` (`Step2BA:89-91`) is definitional.
   - If the check does not compile on this form, the hub pastes the error lines. The fallback is the `(sz, z)` form of `Step34GenTw:84-86` (unguarded) and a dispatcher amend, not a self-edit.
2. **Consumers of 2 (c):** T5-BA (`hL`; `hC`, `GridGoodGen:853`), U3-BA (a), U4-BA.
3. **Answer (6), C6:** the disjunct "or the U2 + twin total passes 5,310" is dropped (U5S-C2; the REQ 0314 answer discharges it). The row-level notice at 2,925 and the pre-signed split at 1,950 stay.
   - C6's twin for U2 is `KDecayBA` (+ reserve `KDecayBA2`) alone, central 1,100. The BA readings of U2 targets 3–9 are instance work.
4. **Family premises (U5S-C3):** this row is BA-side. Nothing to add, apart from (1).
