Auditor model: claude-opus-5-5

# T2452 audit (round 1): BA-U U-D, C10 coverage census (report only)
Written Mon Oct 12 13:53:10 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2452-audit1`, detached at `t/T2452` = cbcaf33 (merge-base 551fa94); `main` = 04118b1. Scratch: `$S/audit/` with `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2452`.
Targets: the design report `docs/reports/T2452-design.md` (D1-D6), and the D4 pin `BAKellStarEv` with its proof and consumer `example`s in the probe `RBM3D/Probe/T2452Pins.lean` (never merged).

**Verdict: PASS** (D1-D6 and D4). No dispatcher sign-off is needed for the report-only merge. Observations O1-O4 at the end.

## 1. Diff scope and sizes
```
$ git diff --stat main...t/T2452
 RBM3D/Probe/T2452Pins.lean   | 371 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2452-design.md | 207 ++++++++++++++++++++++++
$ git diff main...t/T2452 --name-only | grep -v '^docs/reports/T2452-design.md$\|^RBM3D/Probe/T2452Pins.lean$' | wc -l
       0
$ wc -l < docs/reports/T2452-design.md ; wc -l RBM3D/Probe/T2452Pins.lean
     207
     371 RBM3D/Probe/T2452Pins.lean
```
Both are within the stop limits (300 / 400). Only the two sole writable files are touched. No frozen signature is touched, because no library file changed.

## 2. Probe: build, axioms, forbidden tokens
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2452-audit1 && lake env lean RBM3D/Probe/T2452Pins.lean; echo exit=$?
'RBM.BA.baKellStarEv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_kellFarGen_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_kellFarGen_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_kellFarGen_ba_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_ba_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_bridge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_twMB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_K_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2452_etaOf_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom|^\s*(private )?inductive' RBM3D/Probe/T2452Pins.lean; echo grep_exit=$?
grep_exit=1
```
The probe has 11 theorems, but it prints axioms for 10 of them: `T2452_arith` has no `#print axioms`. The auditor ran a scratch copy, `$S/audit/pins_check.lean`: probe lines 1-370, then `#print axioms T2452_arith`, then the three D6 pin statements of the report elaborated as `Prop`s (`STNetLift2gL d (fun sz => Sizes.seqP (sz.withLam 0)) BAFlow baFMz BAflowT0`, `STScaleExistsgL d BAFlow BAflowT0`, `STGridMartgL d BAFlow (fun sz z => baStep2Mat …) BAflowT0`):
```
$ lake env lean $S/audit/pins_check.lean 2>&1 | grep -v 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$'; echo exit=${pipestatus[1]}
exit=0
$ lake env lean $S/audit/pins_check.lean 2>&1 | grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]'
11
```
All 11 theorems use only the standard three axioms, and every pin the report states elaborates.

## 3. D4 statement: `BAKellStarEv` (probe `:38-44`) against the ticket's D4 mathematics
Band source, `Path/KellStar.lean:54-63`: `∀ sz 𝔠 Λ τ δ D t, 3 ≤ d → 0<𝔠 → 0<Λ → 0<τ → 0<δ → SizeTendsto → Bandwidth 𝔠 → RangeCond τ t → (∀n, t n<1) → (∀ᶠ n, 0<lam n ≤ Λ) → ∀ᶠ n, ∀ s u, 0≤s≤u≤t n → ∀ a b, δ(log W)^{3/2}ℓ_u ≤ |a-b|_∞ → ‖Θ_u(a,b)‖ ≤ W^{-D} ∧ ‖ukerMat 1 s u a b‖ ≤ W^{-D}`.
The BA rate and constants come from `BAProp5` (`BA/FlowPins.lean:173-180`): `∃ C c >0, ∀ L≥3, g ∈ (0,Λ], E, m, BAReal d L g κ E m → ∀ t∈[0,1), σ₁ σ₂, a, ‖BATheta … t σ₁ σ₂ 0 a‖ ≤ C·Bparam·exp(-c|a|/ellT L g t)`.

| D4 requirement | Lean (probe) | Status |
|---|---|---|
| only the conjuncts the consumers read | Θ conjunct only; `s` and the `ukerMat` conjunct dropped | ok: readers checked below |
| every charge pair | `∀ σ₁ σ₂ : Bool` before `∀ᶠ n` | ok |
| BA data and rate as `BACompBound` / `baProp5_holds` | `(g E : ℕ → ℝ) (m : ℕ → ℂ)`, `∀ n, BAReal d L (g n) κ (E n) (m n)`, rate `ellT (sz.L n) (g n) u` | ok (`EMn2BA.lean:457-466`, `FlowPins.lean:173-180`) |
| C1: constants in `(d,Λ,κ)`, `κ ≤ Im m` a datum, no smallness of `g`, no scalar `m` | `C c` from `baProp5_holds d Λ κ` (`:84`); `κ ≤ m.im` is `BAReal`'s second conjunct (`MFixedPoint.lean:432`); only `0 < g n ≤ Λ`; `m` is a datum, not `mE E` | ok |
| no spectral premise | no `|E|<2`, `2-κ`, `mE`, `zt` anywhere in `:38-44` | ok |
| parameter order | fixed `(Λ κ sz 𝔠 τ δ D t g E m)` and `σ` before `∀ᶠ n`; then `u`, `a b` | ok, same as the band pin |

Readers of `kellStarEv` on `main` (grep): `FarEntry:712` (`.1` at `s = 0`, `:799`), `LemDecCalEPrec:990` (`.1`, `s = 0`, `:992`), `EMn2Exp1:1770`, and its own instance `KellStar:415`. None reads `.2` (`ukerMat`), so dropping it is justified. On `main`, `Path/UTransport` is imported only by the root `RBM3D.lean:140`: see O2.
Route: `baProp5_holds` + `EMn2BA_theta_shift` (`EMn2BA:424`, public) + `EMn2BA_bparam_le` (`:431`, public) + one copy of the closing inequality (`T2452_arith`, a copy of the private `EMn2BA_arith:597`). The amend route (un-private `:597`) is also named (design `:172`). That meets the ticket's "no copy beyond the one closing inequality". `EMn2BA` is not edited.

**Consumer shapes (compiled).**
- `KellFarGen` (`:48-52`) is the generic consumer hypothesis.
- `lemDecCalEPrec_kell` is applied directly at `KellFarGen … (1/8) D t` (`:172-175`), so the types match.
- The band implication from `kellStarEv` is `T2452_kellFarGen_band` (`:156`); the BA implication from `BAKellStarEv` is `T2452_kellFarGen_ba` (`:164`).
- End-to-end versions run from `STFlow` (`:216`) and from `BAFlow` (`:197`, `Λ = 𝔡⁻¹`, `τ = ε/2`, `g = BAflowLam0`).

**Compiled nonempty instance** (`:209-213`).
- Data: `d = 3`; the BA instance `sz0`, `zSeq`, `flow_sz0` (`FlowPins:1214`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`); `t ≡ 1/2` with `half_lt_t0` (`FlowPins:1254`); `δ = 1/8`; `D = 1`; charges `(true,false)`.
- The term is `T2452_kellFarGen_ba_flow (le_refl 3) (baKellStarEv 3) … flow_sz0 (half_lt_t0 ·).le …`. Every deterministic hypothesis is discharged.
- Nondegeneracy: `sz0.L n = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}` (`Defs/Sizes.lean:260-263`); `BAflowLam0 = √t₀·lam ≤ lam` (`FlowPins:386`), so `ellT = 1`. The auditor's check that far pairs exist:
```
$ python3 -I -c "...W=(2*(n+1))**5; L=4*(n+1); ell=min(max(lam/sqrt(.5),1),L); far=(1/8)*log(W)**1.5*ell..."
(output condensed to one line) n=0: W 32 L 4 ell 1 far 0.81 <= floor(L/2) 2 | n=1: W 1024 L 8 far 2.28 <= 4 | n=10: far 7.59 <= 22 | n=100: far 17.09 <= 202 | n=1000: far 29.29 <= 2002
```
These match design `:169`. The far set is nonempty, the window is not collapsed, and no witness is astronomically large.

## 4. Census reproducibility on `main` (D1, D2)
The scripts are the ones the prove report lists. Their sha256 prefixes match it:
```
$ shasum -a 256 <12 scripts> | cut -c1-12  -> 19496da7bbf7 cenlib, 971493906ecb census, f0b52a1a5123 b5b, 1d3b0df8f238 rowtable, 52d2482e6fdc report_tables, 8042984d728b bound, af9d5aa8642e cone, 69643ec94407 dens, 67ce6603c8f6 b5b_join, 8f284d55a4fb urows, 190cdce25b10 unresolved, 839fd54db9fb run_all.sh
```
The auditor reran them from the main worktree (`RBM3D/` clean, `git status --porcelain RBM3D/` empty), writing output to the auditor's own directory:
```
$ cd /Users/junyin/Lean_proof/RBM3D && bash $S/run_all.sh $S/audit/out_main     (55.6 s)
04118b1
B5b rebuilt: 147 distinct band-specific facts (3065 lines), 64 band defs; ...
B5b rebuilt: 147 distinct band-specific facts (3044 lines), 64 band defs; ...       [sorted walk]
declarations read from outside the row files by the scoped rows: 530 (theorems/lemmas: 345 )
index: 507 files, 26951 declarations; row files (scoped + merged T/V rows): 117; scoped rows: 19
total scoped files 85, lines 112527; distinct declarations read 530; over 200: 77; thresholds >100/>200/>300/>500: 122/77/56/40
joined to the index: 147  with > 200 lines below: 63  <= 200: 84
tokens whose last component names a library declaration: 23455  resolved: 21283  unresolved: 2172
classes: {'reuse': 21, 'covered': 44, 'noreader': 4, 'producer': 6, 'u5': 2} total 77 unassigned: []
over-200 names 77 nsof.sh agrees on full name and file:line: 77
$ diff $S/audit/out_main/facts.tsv $S/out_wt/facts.tsv && echo identical ; cmp $S/audit/out_main/facts.json $S/out_wt/facts.json && echo identical
identical
identical
```
The per-row table, the classes, the B5b comparison (147 / 3,065, the same as T2379) and the `nsof.sh` agreement (77/77) all match design `:27-51` line for line. Every one of the 77 facts has a BA status (`unassigned: []`).

## 5. Spot checks of the claims on `main` 04118b1 (grep and sed output, abridged)
```
Step2Iterate:1392-1394  ST_step2_of_pins (hNew …) (hMart : STGridMart d) … (hNet : STNetLift2 d) (hScale : STScaleExists d) …  -> T1 keeps them as hypotheses (D6)
Step2Iterate:1729-1730  theorem ST_gridMart_of_repN … := by obtain ⟨C₀, hC₀, hAt⟩ := h 2 le_rfl          -> m = 2
DuhamelI:1446 / DuhamelII:529   ST_gridMart_of_repN (RBM.Ind.stGridRepN_holds d hd)                         -> m = 2, via the bridge
PfStep5:2170  RBM.Ind.stGridRepN_holds d hd 2 le_rfl ; PfStep5:51 "conjuncts 1, 2, 4 of `STGridRepNAt` are used"
grep -c NetLift: GridDriftN 0, QGridA 0, EtermsMid 5 (comments/private copy) ; importers of Path.NetLift1: Path/NetLift2.lean only   -> F2 refuted
STLemDecCalE: def Step5Pins:193, producer LemDecCalEPrec:1550, inst_lemDecCalE Step5Pins:596; no other reader   -> D3 (iii)
etaT_le_of_le readers: CondDom:476 (own file), DifREP1:617, QEndA:565, NQGood2:467, QEndGrid:568, 667   -> D3 (iv)
FarEntry:425-444 uses KLK_two (𝒦 = W^{-d}Θ); EMn2BA_K_two:624 (BA 𝒦 = W^{-d}(ΘM)); baEMn2ExpHK:637 from baComp_holds   -> D4 finding
paper: 7_8:1994 "remain valid … except that (eq:MG_conclusion3) is modified"; 7_8:1999 label MG_conclusion3_BA; 7_8:2016 "together with lem:DIfREP";
       3_5:134 Sol_CalL (Lemma 5.3 of YY_25); 3_5:218 lem:DIfREP (Lemma 5.5); 1_2:1144 prop:ThfadC; 1_2:1399 "standard N^{-C}-net"
T2379-design:115  ST side = (1-f) S g + 245, g = 1.92 x density, f = 0.14  -> 1.65 x band lines + 245 (design D5 model: correct)
```
All 9 lines of the REQ table (`REQ-1104-U:24-34`) are answered (design `:119-127`), and so are the three F2 false positives. The D6 proposed pins elaborate (§2).

## 6. Per-target verdicts
- **D1 (scope, method, B5b): PASS.** The closure rule is stated (`:20`: name-level, non-row declarations, Mathlib excluded, a lower bound). The threshold is 200. The B5b list is rebuilt with 147 / 3,065. T4s1's `AzumaProxyN*` move to T4s2 is included. The census reproduces on `main` (§4).
- **D2 (census table): PASS.** One entry per fact over 200, grouped by layer. The full per-fact TSV (full name, producer file:line, lines below, spec flag, first use per reader, status) is in prove (b) `:168-246`, and it is byte-identical to the auditor's rerun. Counts under 200 per row are in the row table. The REQ lines and F2 are confirmed or refuted.
- **D3 (unowned layers): PASS.**
  - (i) Every consumer reads `m = 2`, and the conjuncts each reads are named. TL coverage: the shape is compiled (`T2452_bridge`), and the three identities stay as a `def … : Prop`, as the probe rule allows. Both options are sized. U-row inputs: the size of the restatement is given, so no C8 stop. Paper: the modification touches only the QV bound, not the pin.
  - (ii) Both NetLift routes are sized.
  - (iii) `STLemDecCalE` has no BA reader.
  - (iv) CondDom has one read; its carrier form is compiled.
  - (v) `Step2Scale` and `Step2Core` become targets.
- **D4 (`BAKellStarEv`): PASS** (§3).
- **D5 (producer rows): PASS.** Every producer P1-P7 has a route, lane, lo/c/hi with its method stated, a role and dependencies, a sub-stage, and a row-or-target decision. No producer has a spectral premise.
- **D6 (flags and gating): PASS.**
  - T: 28.5 → 31.5. U: 34.5. BA: +2.
  - The T1-BA producers are named (P1, P2, P3, P6), and their pin statements elaborate.
  - The ST-side T1 is unchanged.
  - Closing conditions are listed.
- **Stop rules: not fired.**
  - 2 new rows (≤ 3).
  - No producer is new mathematics. P1's identities H1-H3 are identifications of two Lean encodings of the same `𝓛^{(2)}`; their K-part is proved (`T2452_K_eq`), and the report gives a size-triggered fallback P1G.
  - No band fact is false at BA. No spectral reading is in play.
- **Paper deltas: covered.**
  - T2452a: the registry finding.
  - T2452b: the BA grid pin via the twisted pin, against `lem:DIfREP` at `7_8:2016`.
  - T2452c: `BAKellStarEv` is not stated in the paper (`prop:ThfadC` at the far scale).
  - `KellFarGen` and `T2452_Bridge` are probe-only proposals, not Lean/paper statement differences of merged code.

## 7. Observations (no statement, instance, build, axiom or delta-coverage change)
- **O1.** The probe has no `#print axioms` line for `T2452_arith`. The auditor checked it (§2: standard three). Prove (b) also lists "11 theorems" next to 10 printed lines.
- **O2.** Design `:165` and candidate T2452a say "`Path/UTransport` is imported by nothing". On `main` it is imported by the root `RBM3D.lean:140` (and by no module). The conclusion still holds, because no row reads the `ukerMat` conjunct. The dispatcher may reword T2452a when numbering it.
- **O3.** The census scripts live only in the session scratch (`$S`, under `/private/tmp`), which the ticket allows, with hashes in the prove report. They reproduce now (§4). If the dispatcher wants the census to stay reproducible later, it should keep a copy.
- **O4.** P1's sizes (450 / 760 / 1,500) come from analogy to merged TL files, not from the T2379 model; the report says so (`:176`, `:180`). The H1-H3 identities (loop part, drift, QV; same-charge pairs not compiled) are an execution risk that P1's own 1a must take up. The report already records the P1G fallback and its REQ trigger.
