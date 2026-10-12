Auditor model: claude-opus-5-5

# T2457 audit, round 1 (Mon Oct 12 18:53:24 UTC 2026)

Branch `t/T2457` at 676eef54, detached audit worktree `../RBM3D-wt/T2457-audit1`. Binding texts: CONTROL H254 (4) / DECISIONS §273 (1), (3) (R1);
H249 (2) decision (B); H250 (3); H251 (2). Scratch files are in scratchpad `T2457/` (not committed).

## 1. Diff, G1, build, axioms, hygiene

```
$ git diff --name-only main...t/T2457
RBM3D/Chain/Step34Gen.lean
RBM3D/Chain/Step34GenTw.lean
RBM3D/Probe/T2457Pins.lean          # 1a probe, sole writable "1a only, never merged"
RBM3D/Test/Axioms.lean              # +2 owedProps lines: RBM.BA.STLmaxUgL, RBM.BA.STLKUgL (after STGdecayWgL)
$ git diff --stat main...t/T2457 -- RBM3D/Induction RBM3D/Chain/Carrier.lean RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean | wc -l
0
$ git merge-tree --write-tree main t/T2457 ; echo $?      # main = c9f69dba (T2462a merged meanwhile; Axioms.lean +8 there)
0
$ wc -l RBM3D/Chain/Step34Gen.lean RBM3D/Chain/Step34GenTw.lean       # stop line 2,000; Step34GenB unused
    1255 RBM3D/Chain/Step34Gen.lean
      99 RBM3D/Chain/Step34GenTw.lean
$ lake build RBM3D.Chain.Step34Gen RBM3D.Chain.Step34GenTw RBM3D.Test.Axioms ; grep -c '^error' build.log
Build completed successfully (4003 jobs).
0
$ lake build RBM3D            # branch root (does not yet import the new modules; hub adds the import at merge)
Build completed successfully (4292 jobs).
$ # Ax.lean: `#print axioms` of every `theorem|def|abbrev` of both new files (99 names)
$ lake env lean Ax.lean ; grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' ax.out ; grep -vc 'propext, Classical.choice, Quot.sound' ax.out
99
0
$ grep -nE 'sorry|admit|native_decide|^axiom|open private' RBM3D/Chain/Step34Gen.lean RBM3D/Chain/Step34GenTw.lean
(no output)
$ grep -n '^import RBM3D.BA' RBM3D/Chain/Step34Gen.lean
(no output)
$ printf 'import RBM3D\nimport RBM3D.Chain.Step34Gen\nimport RBM3D.Chain.Step34GenTw\n#assert_rbm_axioms\n' > Reg.lean; lake env lean Reg.lean; echo $?
  RBM.BA.STLmaxUgL: 2 [no certificate]
  RBM.BA.STLKUgL: 2 [no certificate]
premises found by scanning: 122 (borrowed 1, owed 57, structural 45, refuted 6, superseded 13).
0
$ # name clash: 99 public names of Step34Gen vs `git grep` of def/theorem/abbrev lines on main c9f69dba (incl. Chain/Step5CasesGen)
clashes on main c9f69dba: 0
```

## 2. Statements against the pins (script)

`AuditBind.lean` = `import RBM3D.Chain.Step34GenTw` + the check file verbatim + these lines (exit 0, 0 errors):
```
example … : STLmaxUgL C μ s t ↔ T2457_LmaxUgL C μ s t := Iff.rfl
example … : STLKUgL C μ s t ↔ T2457_LKUgL C μ s t := Iff.rfl
example (d : ℕ) R law Flow mk T0 : STStep3RgL d R law Flow mk T0 ↔ T2457_Step3RgL d R law Flow mk T0 := Iff.rfl
example (d : ℕ) R law Flow mk T0 : STStep4RgL d R law Flow mk T0 ↔ T2457_Step4RgL d R law Flow mk T0 := Iff.rfl
example (d : ℕ) R law Flow mk T0 Concl : STIngRgL … Concl ↔ T2457_IngRgL … Concl := Iff.rfl
example … : STEKDecaygL μ s t 𝒜 ↔ T2457_EKDecaygL μ s t 𝒜 := Iff.rfl
example … : STEKLowgL μ s t X ↔ T2457_EKLowgL μ s t X := Iff.rfl
example (d : ℕ) R : STStep3R d R ↔ T2457_Step3RgL d R (seqP) (STFlow) (bandFM sz (STflowE z)) (lemT) := bandFM_STStep3R d R
example (d : ℕ) R : STStep4R d R ↔ T2457_Step4RgL d R … := bandFM_STStep4R d R
$ lake env lean AuditBind.lean; echo $?      ->  0
$ lake env lean docs/tickets/checks/T2457-check.lean; echo $?   ->  0   (0 error lines)
```
All six content-binding pins are definitionally the generic names (no D3 (b) re-reading needed: (B) keeps `STEKDecaygL = STEKDecayKgL sz.lam`).

Non-binding forms, read against the band text (`Step34Pins.lean:590-680`, `:330-350`) and the bridges:
- Targets 2, 3, 4 (except `STB45gL`): band bridges are `rfl` / `Iff.rfl` (`Step34Gen:128-134, 177-197, 326-333`), so each generic form is the band form at `bandFM` / `bandStep2Mat`, `seqHflow`. `STB45gL` reads `Step2Gen_ThetaN` (U-C4), bridge proved by `Step2Kern_ThetaN_band` (`:335-338`).
- Target 5 settings: `bandFM_STIngR`, `_STIterR`, `_STSEforLn`, `_STOeqNQ`, `_STWardTypePPin`, `_STB45Pin` are proved equivalences (`:447-489`). `STSEforLngL` takes `mkM : Step2Mat`-valued, `mk := (mkM sz z).toFlowFM` by construction (no hidden equation).
- Target 6 (D3): five forms over `Step2Gen_UN C`, abstract `Ker sz C gK κ`; the window `STEKWinKgL sz gK`, `EKFastDecay (gK n)`, ratio `(gK n ^ 2 + |1 - v|)/(gK n ^ 2 + |1 - t n|)`, Res1 cutoff `ellT (sz.L n) (gK n)`; extra binders vs band: `κ, 0 < κ` (Ndecay, Res1), `gK`, `Ker`, `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹`. `STEKNonzerogL` is the A-form: `1 ≤ Aof κ`, threshold `(1 - s n) * L n ^ 2 ≤ Aof κ * gK n ^ 2` (§269 (2)(b), H250 (3)). Band instances `stek_*gL_band` are one-direction, premise-free (`:617-655`); Nonzero at `Aof = 1` derives `1 - lam²/L² ≤ s` by `le_div_iff₀` (`:650-655`). Consistent with (B): consumer forms read `STEKDecayKgL gK`, `STEKDecaygL` stays at `sz.lam`.
- Target 7: `STNewPQgL d Cls` keeps the band quantifier order (`∀ m σ A, ∃ ℓ k ξ σ' ι A', … ∀ sz C, Cls sz C → ∀ n τ, 0 ≤ τ → τ < 1 → …`), `η = C.eta n τ`; band instance by `exact h3 sz n (E n) τ (hE n) …` (`:838-843`), so the coefficient is definitionally the band one. Class pin per H251 (2).
- Target 8 (leaf): `twSteps C μ s t Cd ↔ (STStep2ConclgL ∧ STLmaxUgL ∧ STLKUgL ∧ STDecayLoopUgL) := Iff.rfl`, projections `h.2.1`, `h.2.2.1` (`Step34GenTw:40-50`), compiled; BA statement-level `example : Prop` for targets 1, 3, 5 and `STSEforLngL` (`:70-95`).

### UBA-C1 text (R1, H254 (4)); nothing on the H252 (2) / §271 (4) text
```
$ grep -cF '0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2' RBM3D/Chain/Step34Gen.lean
8                       # 6 hypotheses `hcmp` (:684, :705, :712, :780, :786, :806) + 2 docstrings (:31, :661)
$ grep -cE '0 ≤ gK n ∧ gK n ≤ sz.lam n|0 < gK n ∧ gK n ≤ sz.lam n ∧' RBM3D/Chain/Step34Gen.lean
0
```
- (a) `step34Gen_winK_of_cmp` (`:683-690`) reads only `(hcmp n).2.1 : gK n ^ 2 ≤ sz.lam n ^ 2`, every n, no case split. As required.
- private `step34Gen_cmp_idx` (`:668-680`): `(0 < g → 0 < l ∧ g ≤ l) ∧ (l ≤ 0 → g ≤ 0)` from R1 at one index. As required.
- (d) `step34Gen_ellT_le/_ge` (`:779-788`) via private pointwise lemmas that `rcases le_or_gt l 0` (`:729`, `:748`). As required.
- (c) `step34Gen_ratio_le`, `_pow_le` (`:704-716`): R1, `1 ≤ A`, `t < 1`. (e) `step34Gen_decayK_of_cmp` (`:805-815`): R1, `1 ≤ A`, `Tendsto W atTop atTop` (discharged from `Admissible` by `step34Gen_W_tendsto`, `:610-613`); decay at `ε/2` → decay at `ε` at `gK`. Matches §269 (2)(c)-(e) in `Chain/Step34Gen` (H250 (3)).

## 3. Hidden hypotheses, vacuity, cycles
- No structure is introduced (D1 default: plain `Cm`, `Hf`; `Step34Gen_LCompat/KCompat` are named `Prop`s, not fields; band proofs `:194-197`).
- `Ker`, `Cls` are parameters; both band classes are inhabited at concrete data (`:1156-1158`), so the forms are not vacuous at the band.
- Dependencies are merged names only (Step2Gen, Step2Kern, Evolution/Prec, Induction/NewPQ, GLoopFlow, Step34Pins/P, DecayGen in the leaf). No import cycle (build passes); nothing imports the leaf.
- The two new unproved premises `STLmaxUgL`, `STLKUgL` (binders of the endpoint theorems) are registered (`owedProps`, registry check above). R1 is inline (no `def`), so no unregistered `Prop` premise.
- Spectral grep (ticket literal), 99 hit lines in `Step34Gen`: `165, 169` (`KLloopOf`, model-free, ticket target 3 text); `178-194, 315-334, 432-489` (band bridges); `586, 588` (`STEKBandKer`); `621-649` (band instances); `838, 859` (band instance / private band lemma); `208, 278, 293-294, 822, 837` (docstrings); `864-1193` (examples at band data). None in a generic definition or the R1 lemmas.

## 4. Compiled nonempty instances (61 examples in `Step34Gen`, 10 in the leaf; all built)
| endpoint | instance (file:line) | data | open hypotheses |
|---|---|---|---|
| `STLmaxgL_of_STLmaxUgL`, `STLKgL_of_STLKUgL` | `:864-882` | `bandFM sz0 (STflowE z0)`, `s ≡ 0`, `t ≡ 1/16`, `hst` from `sz0_hst` | owed `STLmaxUgL`/`STLKUgL` |
| `STStep3RgL`, `STStep4RgL` | `:886-909` (via `inst_step3R/4R`, and direct at `κ=ε=𝔡=1/10`, `𝔠=1/6`) | `sz0`, `z0`, `flow_z0`, `sz0_con` | the pins themselves; other gates' `STKbound/Kward/LK/Step1Loop/Step2Concl` |
| settings (`STSEforLngL`, `STOeqNQgL`, `STB45PingL`, `STWardTypePPingL`, `STIterRgL`) | `:912-939` | `sz0, z0` / `szB, zB, 7/8, 15/16` | the pins (owed) |
| ℰ-term / loop bridges, `LCompat`, `KCompat` | `:943-1030` | `sz0`, `n = 0`, `τ = 1/2`, loops of length 2-3 | none |
| `STEKDecaygL`, `STEKLowgL` | `:1146-1153` | `seqP sz0`, `δ₀`, `X ≡ 1` | none |
| five `stek_*gL_band` | `:1164-1189` | `d = 3`, `n_ = 2`, `κ = 1/10`, `sz0` (`Admissible (1/6) (1/10)`); sum-zero `Az = δ₀⊗(δ₀-δ_e)`; Nonzero at `szB`, `s = 15/16`, `t = 31/32`, `(1-s)L² = 1 ≤ 1·1` | none |
| `stNewPQgL_band` | `:1193-1205` | `m = 3`, `σ = (+,-,+)`, `A = ∅`, `bandFM sz0 0`, `τ = 1/2` | none |
| R1 lemmas (a), (c), (d), (e) | `:1225-1249` | band `gK = sz0.lam, A = 1`; non-band `gK = sz0.lam/2, A = 4`; negative `lam` branch `sz0.withLam (-lam)`, `gK = -lam/2` | none |
| target 8 | leaf `:40-66` | abstract and at `bandFM sz0 0`, `seqP sz0`, `0`, `1/16` | `twSteps` / its four conjuncts (owed pins) |
No `N = 0`, empty index, collapsed window (`0 < 1/16 < 1`), `False` premise or huge witness.

## 5. Paper deltas
Prove report (d) proposes `T2457a` (coupling `gK` and bulk `κ` in the `STEK` forms; also for `(sum_res_Ndecay)`, `(sum_res_1)`), `T2457b` (A-form Nonzero and R1 comparison), `T2457c` (regime `R` as a parameter of the settings). `docs/paper-deltas.md:1598` lists `T2457a` as pending. Every Lean/paper statement difference found in §2 is covered by these three.

## 6. Observations (no verdict effect)
- O1. The prove report is 294 lines (ticket limit 200; CLAUDE.md limit 300); its (b) output is in a companion file `docs/reports/T2457-prove-b.txt` (main worktree, untracked; not a sole writable file of the branch). The hub decides whether to commit it with the report.
- O2. The leaf imports `Chain/DecayGen` and `BA/FlowPins` beyond the ticket's "may import" list (`BA/TwistPins`, `BA/Step2BA`, `Chain/Step2Kern`); harmless (leaf, imported by nobody; needed for `STDecayLoopUgL`, `baFMz`).
- O3. `RBM3D/Probe/T2457Pins.lean` is on the branch; per the ticket it is never merged (rule A step 3 brings in only the merged files).
- O4. `RBM3D.lean` is not edited on the branch; the hub adds `import RBM3D.Chain.Step34Gen` and `import RBM3D.Chain.Step34GenTw` at merge. `Test/Axioms.lean` merges cleanly with main's T2462a lines (merge-tree exit 0).

## Verdict
| target | verdict |
|---|---|
| 1 `STLmaxUgL`, `STLKUgL`, endpoints, bridges | PASS |
| 2 loop maxima | PASS |
| 3 D1 loops, ℰ-terms, `LCompat`/`KCompat` | PASS |
| 4 ingredient conclusions | PASS |
| 5 `STStep3RgL`, `STStep4RgL`, settings (D2) | PASS |
| 6 `STEK*` (D3, `gK`, A-form Nonzero) and the R1 lemmas (a), (c)-(e) | PASS |
| 7 `STNewPQgL` (class pin) | PASS |
| 8 leaf TLF-C5 and BA readings | PASS |
| 9 instances | PASS |

**T2457: PASS.** No dispatcher sign-off needed.
