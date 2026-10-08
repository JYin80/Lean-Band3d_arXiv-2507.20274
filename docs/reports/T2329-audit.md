Auditor model: claude-opus-5-5

# T2329 audit (round 1) — S5-16 `stIniTermI_holds` (Step 5 initial term, case (i))

Written Thu Oct  8 12:31:23 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2329-audit1`, detached at `t/T2329` = `906f8a9`; `main` = `d760deb`.

## 1. Diff scope and registry
```
$ git diff --stat main...t/T2329
 RBM3D/Induction/IniTermI.lean | 3823 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
$ git diff main...t/T2329 -- RBM3D/Test/Axioms.lean   (the one removed line)
-   `RBM.Gauss.Sizes.STIniTermI, -- initial term `(iksjuwjx0)`, case (i); S5-01 (T2138, DECISIONS §40: owed)
```
Only the two sole writable files are touched; in `Axioms.lean`, only the `STIniTermI` line changed. No merged file is edited, so no frozen signature changes. Imports (file lines 6-8): `RBM3D.Induction.IniTermII`, `RBM3D.Evolution.CltFar`, `RBM3D.Induction.B45`. These are exactly the ones the ticket allows.

## 2. Build, axioms, hygiene
```
$ lake build RBM3D.Induction.IniTermI 2>&1 | grep -E "IniTermI.lean|error|Build completed"
Build completed successfully (3826 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Induction/IniTermI.lean | wc -l
       0
$ grep -n maxHeartbeats RBM3D/Induction/IniTermI.lean   -> 1935, 2249, 2485, 2976, 3094 (1000000); 3505 (4000000)
```
Check-file equality and axioms. Scratch file = the check file's imports + `import RBM3D.Induction.IniTermI` + check section 2 + `example : RBM.Gauss.Sizes.T2329Check.T2329_stIniTermI_holds := RBM.Gauss.Sizes.stIniTermI_holds` + `#print axioms`.
```
$ lake env lean AuditCeq.lean ; echo "exit $?"
'RBM.Gauss.Sizes.stIniTermI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermI_core_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermI_core_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stIngR5_hyps_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stCltFar_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_iniTermI_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermI_core_same_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermI_core_mixed_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermI_restrict_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_cltFarU_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_cltFarU_CL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermI_cltFarU_index_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Step5Inst.inst_iniTermI : RBM.Gauss.Sizes.STIniTermI 3 → ∀ (Cd : ℝ), 0 < Cd →
      RBM.Gauss.Step5Inst.InstIng5Concl (fun {d} sz E s t => sz.STIniTermConcl ∅ RBM.Gauss.Sizes.STSigAll E s t)
        RBM.Gauss.Step34Inst.szB RBM.Gauss.Step34Inst.zB (fun x => 7 / 8) (fun x => 15 / 16) Cd
exit 0
```
Registry pre-check. I built the dependencies with `lake build RBM3D`. As expected, it stops at the root: `RBM3D.lean:371:0: axiom audit: 1 premise(s) that no theorem ... proves`, because the registry line is deleted and the root import is not yet added; the hub adds it at merge. I then ran a scratch file with every `import` of `RBM3D.lean`, plus `import RBM3D.Induction.IniTermI`, plus `#assert_rbm_axioms`:
```
$ lake env lean AuditRoot.lean     # exit 0
axiom audit: 10021 theorems, 2989 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```

## 3. Statements (per target)

**`stIniTermI_holds (d : ℕ) : STIniTermI d`** (file line 3715). The check-file equality above compiles, so the statement is the merged pin `STIniTermI` verbatim: `STIngR5 d STReg5I (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t)` (`Step5Pins.lean:322`).
- The pin's hypotheses, quantifier order (`∃ 𝔠d` before `𝔠 sz z s t`), the loss `A^{-1/5}`, the profile `STprof` at `u = p.1` and the floor `W^{-D}` are all inherited unchanged.
- The theorem has no extra hypothesis. Proof (lines 3716-3723): `stCltFar_uniform` → `iniTermI_concl`. The arguments of `iniTermI_concl` (3509-3515) are only the pin's own premises (`hflow hs0 hst ht hR hDec hCon hS2`) plus `hCLT`. `hCLT` is the conclusion of `stCltFar_uniform`, which is itself proved here and not assumed.
- `stCltFar_uniform` (2005) calls the merged `stCltFar_holds` (CltFar.lean:1757, `theorem stCltFar_holds (d : ℕ) : STCltFar d`) at line 2008.
- No cycle: the dependencies are merged on `main` (CltFar, IniTermII, B45, Step5Pins). No new structure field.

**`stCltFar_uniform : STIngR5 d STReg5I (fun sz E s t => STCltFarUConcl sz E s t)`** (2005). I compared the new defs `STCltFarIdx`/`STCltFarZeta`/`STCltFarUConcl` (1772-1790) with the merged `STCltFarConcl` (Step5Pins:387).
- The condition `(log W)^5 ℓ_s ≤ ℓ_v`, the window `½(log W)^{3/2}ℓ_v + (log W)^{5/2}ℓ_s`, the control `A^{-6/5}/(r^{d-2}+1)` and `σ₀ ≠ σ₁` are textually those of `STCltFarConcl`, with `t n ↦ v`.
- The index set is `Σ u : TimeIcc s t n, STCltFarIdx sz s n u`, and `STfFar` is taken at `u`.
- At `u = t n` it contains `STCltFarConcl` (`iniTermI_cltFarU_index_nonempty` uses exactly this element). So it is a uniform-in-`u` strengthening, as the ticket's route (7) asks. It is not weaker.
- PASS.

**`stIngR5_hyps_restrict`** (1577). Hypotheses: `0 < 𝔠d`, `s < t' ≤ t < 1` pointwise, `STReg5I s t`, `STConStInd 𝔠d s t`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU` at `(s,t)`. Conclusion: the same six at `(s,t')`. This is route (7)(d). The hypotheses that do not depend on `t` (`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`) need no restriction. PASS.

**`iniTermI_core_same`** (1229). Deterministic: `σ 0 = σ 1`, `X` bounded by the `STDecay`-profile at `s` ⇒ `‖Ugen X a‖ ≤ C M (λ W^{-d} 𝒯_u + W^{-D})`.
- Hypotheses: `g²/L² ≤ 1-u`, `0 ≤ s ≤ u < 1`, `κm ≤ Im m(E)`, `|E| ≤ 2`. The ticket's `1-s ≤ g²` is not required, which makes the lemma stronger.
- `C` depends only on `(d, Λ, κm)`, quantified before `L g W D E s u M lam`.
- PASS.

**`iniTermI_core_mixed`** (1143). This is the exact `(eq:decompU)` split: `∃ c ∈ [0,1], ‖Ugen X a − c·(1−s)²(ΘXΘ)_a‖ ≤ C M (λ W^{-d}𝒯_u + ρ_u W^{-D})`, with `iniTermI_Sfull` (1137) = `(1-s)² Σ Θ_u Θ_u X`.
- The statement is not trivial: `c` is existential, but the left side still has to bound `Ugen X − c·Sfull` for an exact `c`. `c = 0` is not available, because the mixed term is not small.
- Steps (3)-(6) of the ticket are in the further public lemmas `iniTermI_core_lossy` (1191; `ρ`-lossy bound, step (3)), `iniTermI_mixed_tail`, `iniTermI_mixed_bound` and `iniTermI_near` (steps (4)-(6)). They are not inside `core_mixed`. The ticket does not pin the shape of these helpers. See observation O2.
- PASS.

## 4. Compiled nonempty instances (namespace `RBM.Gauss.Step5Inst`, file 3756-3821; all compile, axioms above)
| endpoint | instance | data / discharged hypotheses |
|---|---|---|
| `stIniTermI_holds` | `inst_iniTermI_proved` = `inst_iniTermI (stIniTermI_holds 3)` | the merged pattern: `szB` (`d=3,L=4,ilambda=1`), `zB`, `s=7/8`, `t=15/16` (`g²/L²=1/16 ≤ 1-t=1/16`, `1-s=1/8 ≤ 1`). Regime discharged inside `inst_iniTermI`. The Step 1-4 `Prec` premises are the `InstIng5Concl` antecedent (other gates' pins). |
| `stCltFar_uniform` | `inst_cltFarU_proved` (szB), `inst_cltFarU_CL` (szCL, `L_n → ∞`) | `iniTermI_cltFarU_index_nonempty`: the `Σ u` index set is nonempty at every `n`, so the conclusion is not over an empty index |
| `stIngR5_hyps_restrict` | `iniTermI_restrict_inst` | `szB`, `t=15/16`, `t'=29/32`, `𝔠d=1/100`. `STReg5I` (`szB_reg5I`) and `STConStInd` (`conStInd_const`) discharged. The 4 Step 1-4 pins stay as hypotheses. |
| `iniTermI_core_same` | `iniTermI_core_same_inst` | `d=3, L=8, g=1/2, W=2, D=2, E=1` (`Im m = √3/2 ≥ 1/2`), `s=7/8, u=15/16`, `M=λ=1`, `σ=(+,+)`, `X_b = W^{-d}𝒯_s + W^{-D} > 0` (nonzero). All hypotheses closed by `norm_num`/`iniTermI_inst_X`. |
| `iniTermI_core_mixed` | `iniTermI_core_mixed_inst` | same data, `σ=(+,-)` |

The ticket's instance requirement is met: `d=3`, `L=8`, `g=1/2` with `1-s=1/8 ≤ 1/4` and `1/256 ≤ 1-u=1/16`, and a nonzero `X`. No `N=0`, empty index, collapsed window or `False` premise.

## 5. Name clashes (public new names, `git grep -lw <name> main -- RBM3D | grep -v Probe/ | wc -l`)
```
STCltFarIdx 0   STCltFarZeta 0   STCltFarUConcl 0   stIngR5_hyps_restrict 0   stCltFar_uniform 0   stIniTermI_holds 0
```

## 6. Paper-delta coverage
The Lean/paper statement differences are each proposed in prove report (d):
- `T2329a`: the `e^{√m}`-shifted tail comparison in regime (i).
- `T2329b`: `lem;CLT` used uniformly in `u ∈ [s,t]`, via the new `STCltFarUConcl`.
- `T2329c`: the factor `((u-s)/u)² ≤ (1-s)²`, i.e. `c ∈ [0,1]` in `core_mixed`.
- `T2329d`: the worst-sequence/grid argument.
- `T2329e`: the window complement uses the linear-exponential `prop:ThfadC`.

The pin itself is unchanged, and no other difference was found. Coverage is complete.

## 7. Observations (no statement, instance, build, axiom or coverage effect)
- O1: the file has 3823 lines. The ticket's stop rule is 2200 (estimate 1100/1400/1900). The prove report states this (lines 241-242) and gives the split points (§13 l.1556, §16 l.2131, §18 l.2590). Splitting it would be a dispatcher matter; it is not an acceptance defect.
- O2: the ticket's description "`iniTermI_core_mixed` (deterministic, for (1) and (2)-(6))" is spread over `iniTermI_core_mixed` (2), `iniTermI_core_lossy` (3), `iniTermI_mixed_tail`/`iniTermI_mixed_bound`/`iniTermI_near` (4)-(6). Step (1) is `iniTermI_core_same`. (a′) of the prove report records this.
- O3: `STCltFarIdx`, `STCltFarZeta` and `STCltFarUConcl` are public, unprefixed new defs (§3 (E)). They appear in the statement of the target `stCltFar_uniform`, the "`u`-uniform form" the ticket asks for, and they have 0 clashes. The registry pre-check passes with `STCltFarUConcl` present.
- O4: the five `maxHeartbeats 1000000` and one `4000000` overrides compile within the module build above.

## Verdict
| target | verdict |
|---|---|
| `stIniTermI_holds` | PASS |
| `iniTermI_core_same` | PASS |
| `iniTermI_core_mixed` | PASS |
| `stIngR5_hyps_restrict` | PASS |
| `stCltFar_uniform` | PASS |

Ticket T2329: **PASS**. No dispatcher sign-off is needed for the merge. The file-size split (O1) is optional.
