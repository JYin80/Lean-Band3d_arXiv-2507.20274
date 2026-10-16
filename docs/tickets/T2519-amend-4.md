# T2519 Amend 4 (dispatcher V5, 2026-10-16 14:47 UTC; DECISIONS §360) — the coupling window is eventual in rows c, d; primed successors of the three `∀ n` inputs (owner: row c)

Answers row a's audit observation 2 (`docs/reports/T2519-audit.md` §6) = prove report (d) 1 (`docs/reports/T2519-prove.md`). Written after row c's start (14:42:49 UTC, wf_9ce94310-f95): an amend after the start (rework ledger).

1. **The gap.** Three merged inputs take the coupling window at **every** `n`:
   - C3 b's pin `GUEEntryMixBA` (`BA/GUEEntry2:738`, proof `gueEntryMixBA` `:785`): `∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal …`;
   - C4 a's `gueGrid_expect_oneLoopBA` (`BA/GUEOneLoop:1196`): `hg : ∀ n, 0 < g n ∧ g n ≤ Λ`;
   - row a's `gueGrid_entry_boundBA` (`BA/GUEEntryGridBA:296`): `hdata`, the text of `GUEEntryMixBA`.
   The BA producers (row d target 16: `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at `BAEd`, `BAfE`, `BAfT`) have `g n = √t₀ · λ_n` with `0 < g n ≤ Λ` only **eventually** (`(eq:WO)`; `Sizes.lam` is unsigned), and `BAReal` at **every** `n` (`BAEd` is `∀ n` in `RBG_Prod`). Row a's K lemmas are already eventual. Every conclusion involved is eventual in `n` (`StochDomAt`, `∀ᶠ n`).
2. **Decision: weaken the window to eventual at the source, by primed successors** (CLAUDE.md: never change a frozen signature; add a primed successor). Each successor has the text of its unprimed theorem with exactly one change, the family premise split into
   `(∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))` and `(∀ᶠ n in atTop, 0 < g n ∧ g n ≤ c)` (`c = 𝔡⁻¹` or `Λ`):
   - `GUEEntryMixBA'` (def) and `gueEntryMixBA'` (theorem) in `BA/GUEEntry2`;
   - `gueGrid_entry_boundBA'` in `BA/GUEEntryGridBA` (from `gueEntryMixBA'`);
   - `gueGrid_expect_oneLoopBA'` in `BA/GUEOneLoop` (`hr` stays `∀ n`).
   **The proof moves; it is not copied.** The body of each unprimed proof becomes the proof of its successor: the window is used at one `n` inside `filter_upwards` (`GUEEntry2:816`, `GUEEntryGridBA:323`, `GUEOneLoop:1240`), so add the eventual window to the filter list; `(hg 0)` at `GUEOneLoop:1227` (nonnegativity of `CM`) becomes a witness of the eventual window or a direct `positivity`. Each unprimed theorem becomes a wrapper `… (Filter.Eventually.of_forall …)`. Unprimed signatures, docstrings' signed texts and existing instances unchanged (the instances go through the wrappers). One compiled `example` per successor on the existing instance data.
3. **Rows c and d use the successors.** Every public statement of rows c and d that carries the coupling window takes it as `∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ` (or `≤ 𝔡⁻¹`) and `BAReal` as `∀ n`, as row a's K lemmas do. No padding, no `Sizes.comp` / reindexing of `Pgue`, no existence lemma of BA data. Row b′ (`gueGrid_twistBA`, F2 guard `0 < g n →`) is unaffected.
4. **Owner and order: row c.** The three successors and wrappers go in **row c's first commit**, so row d reads them from `main`. Row c's writable files are extended by `BA/GUEEntry2`, `BA/GUEEntryGridBA`, `BA/GUEOneLoop`, for item 2's edits only.
5. **Price.** ≤ 200 lines of diff in the three merged files, counted in row c's landing line **2,811 (not raised)**; C5 total line 12,000 unchanged. The report gives the diff count per file.
6. **Stop.** If one proof uses the window at an `n` outside its eventual filter in a way that needs more than 60 changed lines, or a successor needs a new `Prop` premise, or row c's own statements cannot take the eventual window: stop and write the question in `docs/queue/T2519c.state`.
7. **Registry.** `GUEEntryMixBA` has no registry line (`RBM3D/Test/Axioms.lean`); `GUEEntryMixBA'` gets none either (a proved pin, used by its own theorem). No owed line.
8. **Paper delta.** Row a's tag `T2519c` reads after this amend: "the coupling window `0 < g n ≤ Λ` is eventual in `n` throughout C5 (the paper's "`N` sufficiently large"); `BAReal` at every `n`". Lean bookkeeping; no paper change.
