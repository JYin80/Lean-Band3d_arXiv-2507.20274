# U6-BA coverage check (draft; dispatcher helper, 2026-10-14, `main` 39db8072, read only)

Row: U6-BA, "the Step 5 vocabulary at BA" (`REQ-2026-10-12-1418-UBA.md:72-75`, Q3 `:91-96`). Answered by supervisor
`2026-10-12-1457.md` (UBA-C2 `:89`: `baFlowLam0_ge` deleted as a target; F1 row (h) `:79`: owner "T2459 1a and the U6-BA pin");
recorded in DECISIONS §269 (3). The REQ's "No merged lemma states this bound; U6-BA proves it" was already corrected by 1457 `:37`.
Inputs merged since: T2501 b (`BA/Step5CasesBA`, bbb1fd30), U5e = T2499 (`BA/Step5IIITargets`), T2503 (design), T2504 (`BA/MainIndOutBA`).

## Item table (all names public unless marked; BA tuple = `(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)` = `baPin`, `BA/LWPinsBA.lean:39`)

| # | U6-BA item | merged name (`file:line`) and statement head | status |
|---|---|---|---|
| 1 | `BAStep5R d R` := `STStep5RgL d R` at `baPin` | no BA abbreviation (0 hits in `RBM3D/`). Content at exact type: `baStep5I_holds` `BA/Step5CasesBA.lean:248` `∀ d, 3 ≤ d → STStep5IgL d (BA tuple)`; `baStep5II_holds` `:254` (`STStep5IIgL`); `baStep5IV_holds` `:260` `∀ d, STStep5IVgL d (BA tuple)`; `baStep5III_holds` `BA/Step5IIITargets.lean:57` `STStep5IIIgL 3 (BA tuple)` (d = 3 only: 0342 V-F2, Jun) | content covered; name missing and unread |
| 2 | regime abbreviations | generic `STStep5IgL` … `STStep5IVgL`, `STStep5gL` `Chain/Step5Gen.lean:226-230` at the BA tuple. `STStep5gL` (`STAny`) at BA: no theorem and no reader (V2a reads the four regimes, `docs/tickets/checks/T2503-check.lean:276-292`) | covered by the generic names |
| 3 | `STIngR5gL` at `baPin` (T2458 target 8) | generic `STIngR5gL` `Chain/Step5Gen.lean:191`; inline at the BA tuple in `BAStep5IIIWalk` `BA/Step5IIIWalk2.lean:73` and private `Step5CasesBA_apply` `BA/Step5CasesBA.lean:415`. Wrapped pins proved at the BA tuple: `baSTEtermsMidgL_holds` `:179`, `baSTDuhamelIgL_holds` `:194`, `baSTDuhamelIIgL_holds` `:208`, `baSTIniTermIgL_holds` `:223`, `baSTIniTermIIgL_holds` `:230`, `baSTWardIIgL_holds` `:236`; `baPfStep5_holds` `BA/Step5IIITargets.lean:52` | covered; no BA abbreviation, none read |
| 4 | `baFlowLam0_ge` (`g₀ ≤ g ≤ √((κ+1)/κ) g₀`) | deleted as a target (1457 UBA-C2 `:89`). `TwistStep2_lam0_sq` `BA/TwistStep2.lean:740`: `0 < κ → BAFlow … → BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2`; unsquared `baStep5III_lam0_le_lam` `BA/Step5IIIKer.lean:399`: `0 < BAflowLam0 sz z n → BAflowLam0 sz z n ≤ sz.lam n`; private copy `CltFlowBA_cmp` `BA/CltFlowBA.lean:83` | covered |
| 5 | `κ/(κ+1) ≤ t₀` (`≤ BAflowT0`) | `TwistStep2_T0_ge` `BA/TwistStep2.lean:731`: `0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → κ / (κ + 1) ≤ BAflowT0 sz z n`. Pointwise `(m, z)` form: private `KBound_t0_ge` `BA/KBound.lean:143` (1457: no third copy) | covered |
| 6 | `Step2Gen_UN = BAUN` | `Step2Kern_UN_BA` `Chain/Step2Kern.lean:124`: `(hIm : ((E n : ℂ) + BAmF sz lam0 E n).im ≠ 0) → Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A` | covered |
| 7 | `κ ≤ Im m` | `BAflow_real` `BA/GreenSchur.lean:59` (`→ BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) (BAmF …)`; `BAReal = BASelf ∧ κ ≤ m.im`, `BA/MFixedPoint.lean:432`); `EMn2BA_mF_data` `BA/EMn2BA.lean:125`: `κ ≤ (BAmF …).im ∧ (BAmF …).im ≤ 1`; `baStep5CasesGen_flowFacts` `BA/SEforLnBA.lean:152` (`κm = κ`) | covered |
| 8 | `STKboundgL`, `STKwardgL` at BA (K12) | `baKbound_holds` `BA/KBound.lean:245` `: BAKbound d` (`:196`: `3 ≤ d → … BAFlow sz κ ε 𝔠 𝔡 z → STKboundgL (baFMz sz z) (seqP (sz.withLam 0))`); `baKward_holds` `:302` `: BAKward d` (`:204`, `STKwardgL`) | covered |
| 9 | `d = 3` instances | (iii) at `sz0, zSeq`: `example`s `BA/Step5IIITargets.lean:88, 101, 106`. (i), (ii), (iv) at private data: `BA/Step5CasesBA.lean:514, 547, 490`; at `sz0` these regimes are empty (`:266-272`, T2501 Amend 1). Carrier pins stay hypotheses (as in every BA Step-5 instance) | covered |
| 10 | 1457 F1 (h): Step-5 kernel at `g₀`, regimes at `g` | (i), (ii): `baIniTermGen_kerFacts` `BA/Step5KerBA.lean:161` (`IniTermGen_KerFacts … baFMz BAflowLam0`, `A = (κ+1)/κ` at `:168`). (iii): `BAStep5IIIKernel` `BA/Step5IIIKer.lean:410` (premise `lam0 n ≤ sz.lam n`), `baStep5IIIKernel_holds` `:436`, `baStep5IIIKernel_at_flow` `:480` (also the BA TailtoTail that `T2462.md:70` lists for U6-BA; `∀ lam0, STTailtoTailgL' 3 (baFM · lam0)` is not a target, `T2459-design.md:170`) | covered |

## Readers of `BAStep5R`
- Lean: 0 hits in `RBM3D/` (`--include=*.lean`, `Probe/` excluded). `BA/MainIndOutBA` (T2504): no Step-5 name.
- Docs: `docs/tickets/T2503.md:51` and `docs/reports/T2503-design.md:143`: "U6-BA's abbreviation `BAStep5R` is not read"; V2a states Step 5 as `STStep5RgL` at the BA tuple (`T2503-check.lean:276`, `:292`). `T2499.md:56`: "a later U6-BA abbreviation, if wanted, bridges definitionally". `T2501.md:27`, `T2501b-prove.md:235`: list U6-BA as a consumer of `baStep5I/II/IV_holds` (no shape asked). T2504 ticket and reports: 0 hits.

## Registry (`RBM3D/Test/Axioms.lean`)
- 0 hits for `U6-BA`, `U6BA`, `BAStep5R`, `STStep5RgL`, `STIngR5gL`. No `owedProps` line is owned by U6-BA.
- The one Step-5 line, `:200` (`STStep5ConclgL`), already names producers T2501 / T2499 and reader V. No change.

## Verdict: (A) covered. U6-BA closes by bookkeeping, with no ticket.
Every data item is a merged public theorem. Item 4 was deleted by 1457. Every proved Step-5 target at BA (cases (i)–(iv), the wrapped pins) is merged at the BA tuple with compiled `d = 3` instances. The only thing not in the code is the abbreviation `BAStep5R` (with its regime names and an `STIngR5gL`-at-`baPin` name). Nothing reads it, and T2503 (7) says that is intended.

What a dispatcher records:
1. DECISIONS (new §): "U6-BA closed without a ticket (coverage table: `docs/claude-team/drafts/U6-BA-coverage.md`). `BAStep5R` is not introduced. Readers use `STStep5RgL d R` at the BA tuple (T2503 (7)). Data: `TwistStep2_lam0_sq`, `TwistStep2_T0_ge`, `baStep5III_lam0_le_lam`, `Step2Kern_UN_BA`, `BAflow_real`, `baKbound_holds`, `baKward_holds`. 1457 F1 (h): closed by `baIniTermGen_kerFacts` and `BAStep5IIIKernel`."
2. Forecast and count: drop the planned U6-BA row (0658 `:59` "U6-BA → 1"; §314 (6) U ≈ 45 → ≈ 44). The used count is unchanged, because no ticket number is spent.
3. V2a 1b gate (0342 Q2 `:53`; §314 Q2; `REQ-…-0330-Vopen.md:14, :89-91`): remove U6-BA from "after U3-BA (a)/(b), T2501 b, U6-BA, V1-BA".
4. `docs/HANDOFF.md:28` (U-BA list), and ROUTES BA cell "起草 U6-BA" (§320 (4)): mark U6-BA closed (bookkeeping).
5. U closing REQ (1152 `:165` item 1): cite this table for U6-BA. Note two points: case (iii) is at `d = 3` only (V-F2, waiting on Jun), and (i)/(ii)/(iv) are instanced at private data, because their regimes are empty at `sz0`.
6. Stale "consumer: U6-BA" notes (`T2501.md:27`, `T2501b-prove.md:235`, `T2462.md:70`, `T2458.md:38, :82`, 1457 `:79`): record only; do not edit.

Optional, not recommended: if the vocabulary is wanted anyway, it is about 10 lines plus `Iff.rfl` examples in the first V ticket that touches `BA/LWPinsBA`. For example, `abbrev BAStep5R (R) : ℕ → Prop := baPin (fun d => STStep5RgL d R)`, untested; `PinFam` is at `Chain/LWGen.lean:126`. No separate ticket.
