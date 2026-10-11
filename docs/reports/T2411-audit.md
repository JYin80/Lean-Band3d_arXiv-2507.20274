Auditor model: claude-opus-5-5

# T2411 audit (round 1) — BA-G5b: threshold families, (m5), R6, `baFamGain_holds`, `baFAav_holds`
Written Sun Oct 11 10:21:24 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2411-audit1`, detached at `b26d2ec` (= `t/T2411`).

## 1. Diff, sizes, forbidden tokens
```
$ git diff --name-only main...t/T2411
RBM3D.lean
RBM3D/BA/GreenCond.lean
RBM3D/BA/GreenCond2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2411 -- RBM3D.lean   (only additions, after the last import, before #assert_rbm_axioms)
+import RBM3D.BA.GreenCond
+import RBM3D.BA.GreenCond2
$ git diff main...t/T2411 -- RBM3D/Test/Axioms.lean | grep -E "^[+-] " | cut -c1-60
-   `RBM.BA.BAFamGain, -- the family gain interface `famGain
-   `RBM.BA.BAFAav, -- the averaged law `|W^{-d} Σ_o Σ_{b'}
+   `RBM.BA.STInitialGT2gL, -- `(initialGT2)` (`3_5:28-30`)
$ wc -l RBM3D/BA/GreenCond*.lean     (stop line 2,000 per file)
    1989 RBM3D/BA/GreenCond.lean
    1990 RBM3D/BA/GreenCond2.lean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/BA/GreenCond.lean RBM3D/BA/GreenCond2.lean | wc -l
       0
$ grep -nE "^(theorem|def|abbrev|noncomputable def|structure) " RBM3D/BA/GreenCond*.lean | grep -vE " (GreenCond2?_|baFamGain_holds|baFAav_holds)"
(no declaration line; one docstring hit at GreenCond2.lean:694)
```
All four files are sole writable files; the pinned definitions (`BAFamGain`, `BAFAav`, `GreenMinor_famGain`, `GreenMinor_famA/X`, `BA/GreenMinor3.lean:812-870`) are not touched (no other file in the diff).

## 2. Builds, check file, axioms (audit worktree)
```
$ lake build RBM3D.BA.GreenCond RBM3D.BA.GreenCond2 2>&1 | grep -c "^error"; ... | tail -3
0
✔ [3788/3789] Built RBM3D.BA.GreenCond (11s)
✔ [3789/3789] Built RBM3D.BA.GreenCond2 (12s)
Build completed successfully (3789 jobs).
$ lake build 2>&1 | grep -E "^error|axiom audit|unclassified|Build completed"     (full library = registry pre-check)
info: RBM3D/Test/AuditNegative.lean:30:0: audit reverse test: an unclassified premise is caught (RBM.Audit.Fixture.FakePremise).
info: RBM3D.lean:455:0: axiom audit: 11712 theorems, 3533 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4223 jobs).
$ lake env lean docs/tickets/checks/T2411-check.lean; echo check_exit=$?
check_exit=0
$ lake env lean scratch/T2411/ax.lean
'RBM.BA.baFamGain_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFAav_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCond_famGain_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCond_m5_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCond_m5_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCond2_famAvg_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenCond2_graded' depends on axioms: [propext, Classical.choice, Quot.sound]
baFamGain_holds : ∀ (d : ℕ), BAFamGain d
baFAav_holds : ∀ (d : ℕ), BAFAav d
```
(`ax.lean` also contains `example : ∀ d, RBM.BA.BAFamGain d := RBM.BA.baFamGain_holds` and the same for `BAFAav`; both elaborate.)

## 3. Statements (script: `ext.py` lists each target's explicit hypotheses from the file)
```
$ python3 ext.py /Users/junyin/Lean_proof/RBM3D-wt/T2411-audit1
GreenCond.lean:666 GreenCond_famGain_slice: hyps=['hκ', 'h', 'ht0', 'ht', 'hg0', 'hδ0', 'hδ4', 'hMδ', 'hδ2', 'hEnv', 'hEnv1', 'hcM', 'hB1', 'hsmall', 'hβα']
GreenCond.lean:1866 GreenCond_m5_A: hyps=['hκ', 'h', 'ht0', 'ht', 'hg0', 'ht1', 'hδ0', 'hδ2', 'hslice']
GreenCond.lean:1879 GreenCond_m5_X: hyps=['hκ', 'h', 'ht0', 'ht', 'hg0', 'ht1', 'hδ0', 'hδ2', 'hα', 'hslice']
GreenCond2.lean:52 GreenCond2_graded: hyps=['hX', 'hXd', 'hB', 'hρ', 'hgain']
GreenCond2.lean:242 GreenCond2_famAvg_moment: hyps=['hY', 'hYd', 'hg', 'hM', 'hK', 'hρ1', 'hcρ', 'hw', 'hp']
GreenCond2.lean:696 baFamGain_holds: hyps=[]
GreenCond2.lean:1730 baFAav_holds: hyps=[]
```
(The regex skips primed names: the slice and m5 theorems also carry `hε' : 0 ≤ ε'` / `0 < ε'`.)

- **T4 `baFamGain_holds (d : ℕ) : BAFamGain d`, T5 `baFAav_holds (d : ℕ) : BAFAav d`.** The type is the pinned `Prop` itself, for every `d` (no guard, no extra hypothesis). Quantifier order, `ρ = 4δ_n`, `B = Cδ_n`, `M = K = 2p`, `A = [β]`, `BAGiiGEX` at `ε₀/2`, window, `STInitialGT2gL`, `∃ C` before `∀ᶠ n`, `PrecL … Ψ²` are the pin's (dispatcher text, `GreenMinor3.lean:840,858`). Statement check: exact.
- **T1 `GreenCond_famGain_slice`.** Conclusion: `GreenMinor_famGain (sz.withLam 0) n (Iblk β) (GreenMinor_famA …)` and the same for `GreenMinor_famX … α`, at `B = 2(2c_M(2δ)+cost)`, `ρ = 2(2δ) = 4δ`, general `M, K`, every `β ≠ α`, with `Bad = badTower … (GreenCond_badBase …) (M+1)` (base = hull of `{‖G_t−M‖_max > δ}`, `GreenCond.lean:645`). `hsmall`, `hB1` are explicit numerical premises, as in the band twin (`Green/MinorDiffCond`). This is the ticket's target 1 (threshold families for `Y^A`, `Y^X`). The ticket's route for `hsmall` (`baLDEin_holds`) is replaced by the local law from `BAGiiGEX(ε₀/2)` + `(initialGT2)` inside `baFamGain_holds` (`GreenCond2.lean:818`); this changes no statement.
- **T2 `GreenCond_m5_A/X`.** `‖condRow … (GreenCond_FA …) ω‖ ≤ c_A δ² + √(ε'·Q_A)` and the `𝔛` analogue, where `GreenCond_FA = A_u (G_uu − m)`, `GreenCond_FX = 𝔛_{u,(α,o(u))}(G_uu − m)` (`:1786-1795`), the premise `hslice` is the row-slice mass `P_u(badBase) ≤ ε'` at the sample `ω`, and `Q_A, Q_X` are explicit polynomials in `N` and `η_t⁻¹` (`:1796-1803`). Ticket mathematics `|E_u[·]| ≲ δ²` via Cauchy–Schwarz with the row slice: matched in the Lean form `cδ² + √(ε'Q)`; the `≲ δ²` form at `ε' = N^{-(2d+9)}` is applied at `GreenCond2.lean:995,1060`. Difference covered by candidate `T2411d`.
- **T3 `GreenCond2_famAvg_moment`.** Same hypotheses (`hg, hM, hK, hρ1, hcρ, hw, hp`) and the same bound `(2p+1)(2p)^{2p}(2^{2p−1}ρB)^{2p}` as the band `integral_norm_flucAvg_pow_le_iter_budget` (`Green/FlucIterGain.lean:823`), with `FlucGainUpTo'` replaced by `GreenMinor_famGain … A` (rows in `A`, as the ticket's R6 requires) and `BddMeas`/`FinDep` of the family as explicit premises. `GreenCond2_graded` is the twin of `:566` whose `hgain` is asked only for words with rows among the slots (`∀ x ∈ L i, ∃ j, x.2 = k j`) — the ticket's "T2401b" point. Statement check: matches.
- **C1 / G2 (item 6).** The pins carry no `g ≤ W^{-ε}`, no smallness of `‖M − m₀I‖`, no `(Cλ)^{|a−b|}` premise (pin text above); `∃ C` precedes `∀ᶠ n`, so `C` is uniform in `n` and in `L = sz.L n`.

## 4. Hidden hypotheses, vacuity, cycles
```
$ grep -n "^structure" RBM3D/BA/GreenCond*.lean | cut -c1-80
RBM3D/BA/GreenCond.lean:211:structure GreenCond_Data (sz : Sizes d) (z : ℕ → ℂ) 
RBM3D/BA/GreenCond.lean:808:structure GreenCond_RowLaw (P : Measure Ω') (s : Fin
$ grep -n "^import" RBM3D/BA/GreenCond.lean RBM3D/BA/GreenCond2.lean
RBM3D/BA/GreenCond2.lean:6:import RBM3D.BA.GreenCond
RBM3D/BA/GreenCond.lean:6:import RBM3D.BA.GreenMinor3
RBM3D/BA/GreenCond.lean:7:import RBM3D.Green.MinorDiffCond
RBM3D/BA/GreenCond.lean:8:import RBM3D.Green.LDE
$ grep -n "GreenCond_famGain_slice\|theorem baFamGain_holds\|theorem baFAav_holds\|GreenCond2_famAvg_moment\|GreenCond_m5_\|GreenCond2_graded\|baFamGain_holds" RBM3D/BA/GreenCond2.lean   (call sites only, excerpt)
818:  have hslice := GreenCond_famGain_slice hκ sz hflow t n (ht0 n) (htT n) hg0 (δ := δ) ...
995:  have h2 := GreenCond_m5_A hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' u ω hslice
1060:  have h2 := GreenCond_m5_X hκ h ht0 ht hg0 ht1 hδ0 hδ2 hε' u hα ω hslice
1226:  have hmom := GreenCond2_famAvg_moment (p := p) hY hYd hg hM hK hρ1 hcρ hw hp
1761:  obtain ⟨C₀, hC₀, hfam⟩ := baFamGain_holds d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hii Ψ hΨlo hΨhi hinit τ hτ0 hτε p
```
- No target takes a structure as a hypothesis (§3 lists); the two structures are produced by theorems `GreenCond_data` (`:227`) and `GreenCond_rowLaw` (`:1199`).
- No cycle: the only modules naming `BAFamGain`/`BAFAav` outside the new files are `GreenMinor3` (definitions), `GreenLocal` (consumer, not imported by `GreenCond*`), `Test/Axioms`. All dependencies are merged modules.
- The external premises of the pins (`BAGiiGEX` at `ε₀/2`, `STInitialGT2gL`) are the pin's own (dispatcher text, audited at T2401); the concrete limit check is the prove report's R8 (`W^{-d}B/Ψ² = 6.3e-2` at `n=0`, `→ 0` along `sz0`).
- The slice, (m5) and R6 theorems are all used by `baFamGain_holds`/`baFAav_holds` at `t ≡ t_n` general, so their hypotheses are discharged in the nondegenerate regime (`t = 1/2`, large `n`) by Lean, conditionally on the pin premises only.

## 5. Compiled nonempty instances (all compile with their modules, §2)
| target | file:line | data | premises left |
|---|---|---|---|
| T2 `m5_A` | `GreenCond.lean:1923` | `d=3`, `sz0`, `n=0` (`L=4, W=32`), `κ=1/2`, `t=1/2 ≤ T₀`, `δ=1/10 ≤ κ/2`, `ε'=1`, every row `u`, every `ω` | none |
| T2 `m5_X` | `GreenCond.lean:1928` | same; `u = (0,0)`, `α = (1,1,1) ≠ 0` (by `decide`) | none |
| T1 slice | `GreenCond.lean:1949` | `sz0`, `n=0`, `t=0`, `M=K=2`, `β=0 ≠ α=(1,1,1)`, `c_M, Env = max 1 (closed forms)`, `δ = 1/(64c_M) > 0`, `ε' = δ²/(192Env) > 0`; `hB1` (value `1/16+1/32`) and `hsmall` (`P(badTower)=0` since `G_0 = M`, `GreenCondInst_G0`) proved | none |
| T4 `baFamGain_holds` | `GreenCond2.lean:1940` | `d=3`, `sz0`, `zSeq`, `flow_sz0`, `t≡1/2`, `ε₀=1/10`, `Ψ=W^{-1}` (window by `rpow` monotonicity), `τ=1/20`, `p=1` | `BAGiiGEX(1/20)`, `STInitialGT2gL` (owed pins) |
| T5 `baFAav_holds` | `GreenCond2.lean:1949` | same | same |
| T3 `famAvg_moment` | `GreenCond2.lean:1958` | same flow, `Y = famA` on block `0`, uniform block weights (`c = W^{-3}`), `p=1`, `2 ≤ #[0]`, `ρ = 4δ ≤ 1`, `c ≤ ρ²` proved; `n` from the `∀ᶠ` of `baFamGain_holds` | `BAGiiGEX`, `STInitialGT2gL` |
None is degenerate in the CLAUDE.md §4 sense: `N = 2,097,152` at `n=0`, nonempty blocks and rows, nonempty window, no `False` premise. Every deterministic premise is discharged.

## 6. Paper deltas
Prove report (d) proposes `T2411a` (p formula for `N^{-D}`), `T2411b` (`‖s‖ ≤ (1+2dg₀)/κ`), `T2411c` (no `2 ≤ d` guard, `GreenCond2_row_l1`), `T2411d` ((m5) as `cδ² + √(ε'Q)`), `T2411e` (exponent bookkeeping as built). The Lean/paper differences found in §3 (m5 form; slice with explicit `hB1`, `hsmall`; family on `A = [β]` with `BddMeas`/`FinDep` premises — the latter two are G5a's interface, `T2401a`) are covered.

## 7. Verdicts
- T1 threshold families (`GreenCond_famGain_slice`): **PASS**
- T2 (m5) (`GreenCond_m5_A`, `GreenCond_m5_X`): **PASS**
- T3 R6 (`GreenCond2_graded`, `GreenCond2_famAvg_moment`): **PASS**
- T4 `baFamGain_holds : BAFamGain d`: **PASS**
- T5 `baFAav_holds : BAFAav d`: **PASS**
- T6 C1/G2: **PASS** (no forbidden premise; `C` uniform in `n`, `L`)
- T7 instances: **PASS**
- T8 registry: **PASS** (two owed lines removed; full-build pre-check passes)

**Ticket verdict: PASS.**

## 8. Observations (no change to statement, instance, build, axioms or delta coverage)
1. The slice instance is at `t = 0`, not at the ticket's `t ≡ 1/2`: there `G_0 = M`, so the families vanish and the conclusion holds trivially at that point. The `t = 1/2` slice cannot have `hsmall` discharged at `n = 0` (prove report (a) rows 6, 8); its premises are discharged at `t = 1/2`, large `n`, inside `baFamGain_holds` (`GreenCond2.lean:818`), whose instance compiles. Preflight flagged this as a dispatcher choice. `δ = 1/(64c_M)` is very small because `hB1` and Route-A `c_M` require it, not because a size is huge.
2. Registry: besides the two removals, `RBM.BA.STInitialGT2gL` is added to `owedProps` (owner BA-G6b). This is outside the literal "(the two removals or comments)". It matches the existing classification of `STInitialGT2` and the other `…gL` carrier pins as owed, and the pre-check passes. The dispatcher may reclassify it.
3. The m5 instances use `ε' = 1` (`hslice` by `measureReal_le_one`), the weakest admissible slice bound; the small-`ε'` use is in `baFAav_holds`.
4. `GreenCond2_graded` and the other lower-level public lemmas have no standalone `example`; they are exercised by the instances of their callers (prove report (d)).
5. The ticket names `baLDEin_holds` and `baStab_holds` as inputs; neither is used (route via the local law; `baStab_holds` serves G6b). This changes no statement.
