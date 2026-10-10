Amend 1 to T2397 (dispatcher V2, Sat Oct 10 22:56 UTC 2026; DECISIONS §212; supervisor `docs/supervisor/2026-10-10-2254.md` **G2** (how `κ` and `Λ` enter constant checks; T2390c), correcting 2149 L5)

**Rule for every constant or exponent check of this design gate** (applies to the remaining stages: the rest of 1a / design, and the auditor):
- Use `κ` **uniform in `L`** (`L ≥ 64`; on the flow's `z`: about 0.5 at `g = 1/64`, 0.25 at `g = 1`, **0.044 at `g = 10`**, T2390 table (i)). Do not use `Im m` at a small `L` (for example `L = 3`, `E = 0`, which gives `κ = 0.333` at `g = 10`).
- Use the Lean rate `BAct_rate(d, 𝔡⁻¹, κ)` with **`Λ = 𝔡⁻¹ = 10`**, the window bound the pins quantify over. Do not use `Λ = g`. For example, at `g = 1/64` the rate is `4.2e-3` at `Λ = 10`, against 0.25 at `Λ = g`.
- **Re-check** every closure that depends on `κ` or on the rate, if `κ` or the rate enters an exponent or a threshold that must hold for fixed `n`. Constants that do not depend on `n` are harmless. A closure that fails at the uniform values is reported as such: a REQ item, not a silent change.
- Finite-`L` instance data (`L = 3, 4`) stay valid as nonemptiness checks.

Nothing else in the ticket changes.
