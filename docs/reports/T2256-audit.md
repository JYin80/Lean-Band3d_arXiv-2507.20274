Auditor model: claude-opus-5-5

# T2256 audit (round 1) — BA-S2b1 `RBM3D/BA/Step1Boot.lean` (with Amend 1)

Time: Tue Oct  6 05:49:36 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2256-audit1`, detached at
`t/T2256` = 092370e. Pins: `docs/tickets/checks/T2256-check.lean` (lines 162, 210 changed by Amend 1, recompiled exit 0
per CONTROL H92 done-line).

## 1. Diff scope (sole writable files)

```
$ git diff main...t/T2256 --name-only
RBM3D/BA/Step1Boot.lean
RBM3D/Test/Axioms.lean
$ git diff -U2 main...t/T2256 -- RBM3D/Test/Axioms.lean | grep "^@@"
@@ -249,4 +249,9 @@ def owedProps : List Name :=
$ (added lines, cut at 110 chars)
+   `RBM.BA.BAGbEXPii, -- `lem_GbEXP_BA` `(GiiGEX)` event form `1(Ω(t, ε₀)) ‖G_t - M‖²_max ≺ max 𝓛^{(2)}` over
+   `RBM.BA.BAGbEXPij, -- `lem_GbEXP_BA` `(GijGEX)` event form on `(G_t - M)_{xy}`, `x ≠ y`, over the BA carri
+   `RBM.BA.BAGbEXPav, -- `lem_GbEXP_BA` `(GavLGEX)` over the BA carrier under `(initialGT2)`, `7_8:1916-1946`
+   `RBM.BA.BAFlowMember, -- finite modification of a member of `Fam(0)` is a `BAFlow` sequence (route (A), pr
+   `RBM.BA.BABootstrap', -- BA Step 1 bootstrap for one member of `Fam(t)`, event form, `7_8:1987-1990` (T225
```
Only the two writable files; registry lines are inside `owedProps` and are exactly the five the ticket lists. The new
file imports `RBM3D.BA.ConArg`, `.Step1Trivial`, `.CouplingWindow`, `.FlowPins`, `RBM3D.Induction.Step1Setup` (allowed
list); no existing file other than the registry is touched, so no frozen signature changes.

## 2. Build, hygiene, axioms (audit worktree)

```
$ lake build RBM3D.BA.Step1Boot > build.log 2>&1; echo exit=$?
Build completed successfully (3753 jobs).
exit=0
$ grep "Step1Boot" build.log | grep -c "warning\|error"
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/BA/Step1Boot.lean | wc -l
0
```
`scratchpad/T2256/audit_check.lean` = the check file + `import RBM3D.BA.Step1Boot` + the acceptance `rfl`/`example`s
(§3 below) + `#print axioms` of every public theorem of the file; `lake env lean` in the audit worktree:
```
exit=0          (grep -c "error" audit_check.out: 0)
'RBM.BA.bandFM_indMax' / 'RBM.BA.bandFM_gexRHS' / 'RBM.BA.BAFamZ_mono' / 'RBM.BA.BAFamZ_horizon'
'RBM.BA.PrecL_congr' / 'RBM.BA.baGii_member' / 'RBM.BA.baGij_member' / 'RBM.BA.baM_entry_le'
'RBM.BA.baOmegaC_eq_one' / 'RBM.BA.baBoot_LI'
'RBM.BA.Step1BootInst.inst_baGii_member' / '…inst_baGij_member' / '…inst_baM_entry_le' / '…inst_baOmegaC_eq_one'
'…inst_hcon' / '…inst_baBoot_LI_a' / '…inst_baBoot_LI_b' / '…inst_BAFamZ_mono' / '…inst_BAFamZ_horizon'
'…inst_PrecL_congr'
  -> each line: "depends on axioms: [propext, Classical.choice, Quot.sound]"   (20 of 20; uniq -c output, 1 each)
```

## 3. Statements against the pins (script)

Appended to the check file and compiled (exit 0 above):
```
example : @RBM.BA.FlowFM.indMax  = @RBM.BA.T2256Check.indMax  := rfl
example : @RBM.BA.FlowFM.gexRHS  = @RBM.BA.T2256Check.gexRHS  := rfl
example : @RBM.BA.BAGiiGEX       = @RBM.BA.T2256Check.BAGiiGEX := rfl
example : @RBM.BA.BAGijGEX       = @RBM.BA.T2256Check.BAGijGEX := rfl
example : @RBM.BA.BAGavLGEX      = @RBM.BA.T2256Check.BAGavLGEX := rfl
example : @RBM.BA.BAGbEXPii      = @RBM.BA.T2256Check.BAGbEXPii := rfl
example : @RBM.BA.BAGbEXPij      = @RBM.BA.T2256Check.BAGbEXPij := rfl
example : @RBM.BA.BAGbEXPav      = @RBM.BA.T2256Check.BAGbEXPav := rfl
example : @RBM.BA.BAFlowMember   = @RBM.BA.T2256Check.BAFlowMember := rfl
example : @RBM.BA.BABootstrap'   = @RBM.BA.T2256Check.BABootstrap' := rfl
example (d : ℕ) : T2256Check.baGii_member_stmt d    := baGii_member d
example (d : ℕ) : T2256Check.baGij_member_stmt d    := baGij_member d
example (d : ℕ) : T2256Check.baM_entry_le_stmt d    := baM_entry_le d
example (d : ℕ) : T2256Check.baOmegaC_eq_one_stmt d := baOmegaC_eq_one d
example (d : ℕ) : T2256Check.baBoot_LI_stmt d       := baBoot_LI d
```
All 15 elaborate: every pin is definitionally the check text (Amend 1 range `u n ≤ max (t n) (1 - c₁)` included), and
every target has exactly the `_stmt` type. Mathematics of the pins (read against the ticket): `BAGbEXP*` = band
`STGbEXP*` with `BAFlow`, `BAflowT0`, carrier `baFMz sz z`, law `seqP (sz.withLam 0)`, `0 ≤ t ≤ t₀(z)`, `ε₀ > 0`;
`(GijGEX)` on `(G−M)_{xy}`, `x ≠ y`; `BABootstrap'` has the ConArg-output premise on `[s₁, max(t, 1−c₁)]`,
`s₁ = max(s, 1−c₁)`, for all `C₀ > 0`, `k ≥ 2`, plus `BAConArgVec`. Targets 3: `0 ≤ u ≤ t ≤ t₀(z)`, member of `Fam(t)`;
target 5: `0 ≤ s ≤ u ≤ t ≤ t₀(z)`, all `C₀ > 0`, `k ≥ 1`, right side `((1−s)/(1−u))^{k−1} Bctl_s^{k−1}` (band
`s1_LI`, `Step1Setup.lean:774-777`, same right side; band has fixed `C₀ = 2`, BA every `C₀ > 0`: stronger).
Parameter order: fixed `κ ε 𝔡` (and `𝔠`, `sz`, `z`) before sequences; no `3 ≤ d`, no `L`–`W` relation (checklist (3)).

Moved targets (probe `t/T2205:RBM3D/Probe/T2205Pins.lean`, `git show … | sed -n 1299,1310p; 1508,1516p`): the bodies of
`BAFamZ_mono`, `BAFamZ_horizon`, `PrecL_congr` are character-identical to the probe; `PrecL_congr` writes the probe's
section variable `{sz : Sizes d}` into the binder list (same statement).

## 4. Hidden hypotheses, vacuity, cycles

- No structure-typed hypothesis is introduced; all pins are `Prop`-valued `def`s with explicit `∀`/`→`.
- Dependencies: `BAGbEXPii/ij/av`, `BAFlowMember`, `BABootstrap'` are owed pins (registered in `owedProps`), used only
  as explicit premises (`baGii_member : BAGbEXPii d → BAFlowMember d → …`). `baBoot_LI` takes no pin: its ConArg
  premise is the output of the merged `baConArg''_holds` (T2237) and is discharged from it in `inst_hcon`. No target
  uses `BABootstrap'` (S2b2 proves it); no cycle. All other used names are merged on `main`.
- Non-emptiness of the Amend-1 premise range: at `s ≡ 1/2`, `t ≡ 2/3`, `c₁ = 1/3` the range is `{u ≡ 2/3}` (nonempty;
  `inst_hcon` proves the premise there from `baConArg''_holds 3` + `BATrivialLmax_holds`, only `hwin` assumed).
- External/deterministic hypothesis left open: `hwin : BAWinBulk sz0 zSeq (1/3) (1/2)` (ticket allows it, "as T2238's
  instance"; precedent `BA/Step1Trivial.lean:200`, `grep -rn "BAWinBulk sz0" RBM3D` gives only that line). Limit check
  in the prove report (a)(ii): min `Im m(E, g')` on the window `0.99949` (n=0), `1.00000` (n=1, 5) `≥ κ = 1/2`,
  limit `g → 0`, `m → i`. Accepted.

## 5. Compiled nonempty instances (namespace `RBM.BA.Step1BootInst`, same file, built above)

Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6} > 0`), `zSeq` with `flow_sz0`,
`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `c₁ = 1/3`, `z' = zSeq` via `BAFamZ_main`, `t₀ ≥ 2/3` by `t0_sz0`.

| target | instance | data | open hypotheses |
|---|---|---|---|
| `baGii_member` | `inst_baGii_member` | `t ≡ 2/3`, `u ≡ 1/2`, `ε₀ = 1` | `hii` (owed pin), `hmem` (owed pin), `hwin` |
| `baGij_member` | `inst_baGij_member` | same | `hij`, `hmem`, `hwin` |
| `baM_entry_le` | `inst_baM_entry_le` | every `n`, `x`, `y`; `0 < Im m` by `BAmF_sz0_im_pos` | none |
| `baOmegaC_eq_one` | `inst_baOmegaC_eq_one` | `n = 0`, `u = 0`, every `ω` (`G_0 = M`, `Boot_GM_zero`) | none |
| `baBoot_LI` (a) | `inst_baBoot_LI_a` | `s ≡ 1/2`, `t ≡ u ≡ 2/3` (`u ≥ s₁`), all `C₀ > 0`, `k ≥ 1` | `hwin` |
| `baBoot_LI` (b) | `inst_baBoot_LI_b` | `s ≡ u ≡ 1/2 < s₁ = 2/3`, `t ≡ 2/3` | `hwin` |
| moved lemmas | `inst_BAFamZ_mono`, `inst_BAFamZ_horizon`, `inst_PrecL_congr` | `Fam(2/3) ⊆ Fam(1/2)`; `2/3 ≤ t₀`; tail from `n = 5` | none |

No `N = 0`, empty index, collapsed window or `False` premise; every deterministic hypothesis except the ticket-allowed
`hwin` is discharged by a term (`norm_num`, `flow_sz0`, `sz0_lam_pos`, `t0_sz0`, `BAFamZ_main`). Both branches of
`baBoot_LI` are exercised, case (a) with a nonempty ConArg range.

## 6. Paper deltas

Lean/paper differences and their coverage (prove report (d)):
- event form of `lem_GbEXP_BA` vs printed global form `7_8:1916-1946`, `(GijGEX)` on `G − M`: **T2256a** (and D539).
- pinned `gexRHS` (band `3_5:24` nearest-neighbour form, `W^{-d}1_{|a−b|≤1}`, squared) vs printed `(GijGEX_BA)`
  `7_8:1940-1944` (`Φ_t e^{-c(|a'−a|+|b'−b|)} + Ψ_t e^{-c|a−b|} + W^{-D}`, linear): **T2256b**. Verified by reading
  `paper/tex/7_8_light_weight.tex:1916-1946`: the printed (b) carries `Ψ_t e^{-c|a−b|}` at every distance; the pin has
  no such term for `|a−b| ≥ 2`, so the owed pin is stronger than the printed lemma there.
- ConArg premise on `[s₁, max(t, 1−c₁)]` (Amend 1), Lean-only reading of "same as [RBSO1D, §7.1]": **T2256c**.
- `Ω` threshold `1 + (Im m)⁻¹` vs band fixed `C₀ = 2`: **T2256d**.
- Route (A) member transfer (`BAFlowMember`, `Fam(u)`): existing D536 (T2205b). Every difference is covered.

## 7. Verdicts

| target | verdict |
|---|---|
| 1 pins `FlowFM.indMax`, `FlowFM.gexRHS`, `BAGiiGEX`, `BAGijGEX`, `BAGavLGEX`, `BAGbEXPii/ij/av`, `BAFlowMember`, `BABootstrap'` (+ `bandFM_indMax`, `bandFM_gexRHS` rfl bridges) | PASS |
| 2 `BAFamZ_mono`, `BAFamZ_horizon`, `PrecL_congr` | PASS |
| 3 `baGii_member`, `baGij_member` | PASS |
| 4 `baM_entry_le`, `baOmegaC_eq_one` | PASS |
| 5 `baBoot_LI` | PASS |

**Overall: PASS.**

Observations (no RETURN):
- O1 (for the dispatcher, T2256b): the owed pin `BAGbEXPij` (dispatcher text, supervisor 2252 Q2) is stronger than the
  printed `(GijGEX_BA)` for `|a − b| ≥ 2` (no `Ψ_t e^{-c|a−b|}` term); whether [RBSO1D, L6.1]'s argument gives the
  nearest-neighbour form for the BA operator is unverified in the repository. This changes no statement of this
  ticket (the pin matches its check text) but is a risk for BA-G6.
- O2: `inst_baOmegaC_eq_one` is at `u = 0` (`G_0 = M`); a positive-time instance needs an `ω`-wise bound on `G − M`,
  which no deterministic data supply. Nondegenerate as an instance (the conclusion is evaluated at concrete data).
- O3: the instances of targets 3 use the trivial member `z' = zSeq` (as the ticket prescribes); the `n < n₀`/`n ≥ n₀`
  split is exercised separately by `inst_PrecL_congr` (modification below `n = 5`).
