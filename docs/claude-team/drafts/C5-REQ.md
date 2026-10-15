status: open
REQ-2026-10-15-HHMM-C5split (dispatcher V4, 2026-10-15 HH:MM UTC; **short REQ before C5's release: the M/N forecast passes 15**; supervisor 0643 Q1 `:26-27` (the 15 lines), MNO-C4 `:88`; 2049 GMN-C3 `:91-96`; 0658 UP-C2 `:201-210`; DECISIONS §57 (2), §129 (4), §337 (4), §339 (5), §340, §343; ticket draft `docs/claude-team/drafts/C5.md` (T2519), check `C5-check.lean`)

## Situation
- **M/N 12 / 15 used, flag 15.** Rows 1–3 (C5g T2475, N3b T2477, N3a T2476) merged before the opening. Rows 4–12 in release order:
  - merged: 4 T2513 MN-D3 (0deabaa8), 5–6 T2514 M1 a/b (3a67e18d, 242d669e), 7 T2515 C3 a (13b68cea), 9 T2516 M2 (dec8e150);
  - running: 8 T2515 C3 b, 10 T2517 C4 a (1b), 11 T2518 M3; booked: 12 T2517 C4 b (stacks on C4 a's first commit).
  - Left: **C5** (T2519) and **N2** (with MN-D3's implementation, §340 (1)–(2)). BA 199.
- **C5 re-priced bottom-up at release (MNO-C4): central 6,311 lines** (wide 8,301; ×0.96–1.28: 6,059–8,078) against T2449's 609 / 1,217 / 2,261 (**×5.2**; C3 came in at ×2.5, C4 at ×2.34). Census `1.24 (0.85 B + 0.6 P + 0.05 M)` of the twelve band files C5 twins, plus 1,385 lines of BA-only work, plus instances.
- **Why.** T2449's C5 is T2173's twin group G3 (`T2173-portmap.md:288`, `W_T` 1,739), priced under §57 (2): UN-25…52 model-generic, the P-class parametrisation (`W_P`) inside the UN gate. The UN gate then ported the GUE phase band-only (§129 (4): "`GUEPathBounds` band form; BA form → BA-C5"; on `main` only `Generator` has `ztOf` forms). So C5 carries:
  - the T-class twins T2449 priced (Eq729B, HypA, Proc, ProcK, PathBounds): 2,171, ×1.78 of T2449's central;
  - the unpriced P-class conversion (HypB, BoundsA, DuhamelA2/B/C, EntryGrid, LLTransfer): 2,090;
  - new BA mathematics: the `hoff` producer (C4's Decision (2), a twisted 1-loop law on the grid, ≈ 800 [500, 1,400]), the local law against the matrix `M^{(B)} ⊗ 1`, K̃ and eventual positivity at BA.
- **Rows (pre-signed, file boundaries, ≤ 1,950 each on the pure census):** a 1,726 (`GUEProcBA`, `GUEHypABA`, `GUEEntryGridBA`), b 1,517 (`GUEDuhamelBA`, `GUETwistBA`), c 1,650 (`GUEHypBBA`, `GUEPathBoundsBA`), d 1,418 (`GUELLBA`, `GUEHyp`); reserves a′, b′, c′ if the 1a takes the pure–wide mean (a 1,961, b 2,022).
- **Forecast: 17 (17–20) used at M/N's close** = 12 + C5 4 (4–7) + N2 1. The 15-line fires at this release. The HOLD line (15 used, not closed) is crossed when row c is booked at the 1a. BA ≈ 202 (202–205) at the close, inside 0643's 204 (203–206).
- **No route change is proposed.** C5 reads no V output. The `RBG_*` texts stay as merged (GMN-C3). N2's reading (`RandomLayerBGBA:199-212`, `T2513_n2_three`) is unchanged.

## Questions
- **Q1 (release, flag).** May C5 be released with the pre-signed split a | b | c | d (reserves a′, b′, c′, each booked at the 1a), the forecast going to 17 (17–20)?
  - Proposed: raise the M/N flag to 20, with the same two lines at 20.
  - Or name the condition under which you would HOLD at 15.
- **Q2 (layout, UP-C2).** Which layout?
  - Default: BA leaves, ten new files, no band edit.
  - Alternative: the generic `Of` forms **in place** in the twelve band files (the late execution of §57 (2); GMN-C2 (b)/(c)). Priced at 6,224–6,812 with the BA leaf. That ties at the pure census and saves ≈ 1,500–2,000 lines at the wide census.
  - Obstacles to in place: the `Main/BandTerminal` cone of every file, the 2,000 stop line for Eq729B, HypB and DuhamelC, 56 frozen public names, and no in-place calibration on B-dense carriers yet (UP-C2 (d)).
  - New generic files (6,679–8,632 + 1,595) are the dearest and are not proposed. The dispatcher proposes BA leaves, with in place for the Duhamel layer only if the 1a's rerun saves ≥ 500 lines. Do you want in place, given §57 (2)?
- **Q3 (new mathematics, `hoff`).** Approve D1 (i) as a narrow gate with a probe at C5's 1a?
  - Route R1: a fixed-time Stein moment bound on `twTr(q,a)` at the grid's one-time Gaussian law. Inputs are the two path-bound fields at the same grid time, so no V output and no TL name.
  - Stop: if R1 needs the twisted law at `t₁` (a V output not in `BAMO`) or a primed `RBG_Prod` (GMN-C3), stop at the 1a and send a short REQ.
- **Q4 (rules after V's close).** Keep the C-chain rule "no V module or name"?
  - It also excludes `BA/TwistAvg*` (they import `TwistPins`) and `unMLOutBA_three` in C5's instances.
  - Proposed: keep it. R1 lives at the grid's own law, and the instances keep `UNMLOutBA 3` as a hypothesis.

## Not affected
- Running: T2515 b (`BA/GUEEntry*`), T2517 a (`BA/GUEOneLoop`), T2518 (`BA/MADecolQUE`); C4 b booked. C5 writes only new `BA/GUE*BA` files, `BA/GUEHyp`, the probe, `RBM3D.lean`, and four owner comments plus one structural line in `Test/Axioms.lean` (`UNOULLk`, `UNG1Rowk`, `GUEPathBounds`, `UNOUQUEk`; new `GUEPathBoundsBA`).
- MN-D3's result (§340) and N2's scope (G1, G2, the BA leaf) are unchanged; C5 takes none of them.
