Amend 1 to T2524 (dispatcher V5, 2026-10-16 23:59 UTC; DECISIONS §372; supervisor `docs/supervisor/2026-10-16-2346.md` PASS, conditions BAD-C1–C5, action item O2)

**Delivery.** This amend adds report items; it does not change the gate's targets. If stage 1a is still running, the prover adds them to `docs/reports/T2524-design.md` without restarting. The auditor (1a-audit) checks every item below; a missing item is a RETURN repaired once under rule (B) (report only).

1. **BAD-C2 (the T2523 interface).**
   - (a) For every name **outside the U5 chain** that D1, D2 or D4 cites (a `d`-generic twin in `Path/`, `Chain/`, `Graph/`, `Evolution/`, `BA/`, …), the report marks whether T2523 deletes it. Use `git --no-optional-locks diff main...t/T2523` (or `docs/reports/T2522-dead.md` (b), recomputed with G1–G4 as roots). One column "deleted by T2523: yes/no" in the D1 table and in D4.
   - (b) The 1a-audit re-derives the census with its own grep on post-T2523 `main` if T2523 has merged by then, otherwise on `afab243f`, and states which.
   - (c) A row that needs a declaration T2523 deleted restores it verbatim from `e3540151` inside the row; D4 prices it. No REQ for that.
2. **Closing condition (vii): a `d = 4` instance.** D5 prices one compiled instance: concrete `Sizes 4` data with `Admissible` proved, and the `d = 4` conjunct of the new `Thm27` applied to it with only `UNL32` as a hypothesis. If it costs more than about 150 lines, `Sizes 4` with `Admissible` alone is enough; say which. (Your preflight's row 16, `g²L^d ≤ 1/64` at `d = 4`, `n = 0`, is exactly the kind of instance fact to settle here: give the data that works, e.g. starting at `n ≥ 1`.)
3. **BAD-C3 (REQ triggers).** The report has a section "BAD-C3" answering yes/no, with file:line, for each:
   - a (c) item whose replacement changes a statement read outside the U5 files (another gate's statement, a premise of `STIngR5gL`, or `STStep5IIIgL` itself);
   - an input of the BA case (iii) chain that is merged only at `d = 3` outside the U5 files;
   - the BA-D forecast after this gate ≥ 8.
   Any "yes" → the dispatcher sends a REQ before any row.
4. **BAD-C4 (layout).** At comparable price prefer **in place** (the new-file layout leaves the 7,830 `d = 3` lines dead and doubles the names). In-place rows start only after T2523 merges.
5. **D5 must also give** the texts the assembly ticket's check will pin at exact type (closing (ix)): `baStep5III_holds_any (d) (hd : 3 ≤ d) : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0` (no premise beyond `3 ≤ d`), the new `Thm27`, `final_shape`; and the one-line `d = 3` recoveries of `baStep5III_holds`, `baThm27L_three`, `Thm27_of_L32`'s `d = 3` content (closing (iii)).
