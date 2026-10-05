Auditor model: claude-opus-5-5

# T2206 audit (round 1): `RBM3D/Induction/SizesComp.lean`, branch `t/T2206` at ed7841f

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2206-audit1` (detached at `t/T2206`). Time `Mon Oct  5 19:59:33 UTC 2026` (`date -u`).
Scratch scripts: `$SCRATCH/T2206/{mkpin.py,AuditPin.lean,mkax.py,Ax.lean,Clash.lean}` (outside the repo).

## 1. Diff, build, hygiene
```
$ git diff --stat main...t/T2206
 RBM3D/Induction/SizesComp.lean | 812 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 812 insertions(+)
$ mb=$(git merge-base main t/T2206); git diff --stat $mb main -- RBM3D/Induction/Defs.lean RBM3D/Defs/StochDomAt.lean \
    RBM3D/Gauss/FineModel.lean RBM3D/Defs/Sizes.lean RBM3D/Loop/GLoopFlow.lean RBM3D/Defs/Params.lean RBM3D/Gauss/DominationAt.lean
(empty: upstream definitions unchanged on main since merge-base 98e6d5b)
$ lake build RBM3D.Induction.SizesComp 2>&1 | tail     # in the audit worktree
Build completed successfully (3316 jobs).
exit=0
$ grep -cE 'sorry|admit|native_decide|^axiom|^private axiom|implemented_by|unsafe' RBM3D/Induction/SizesComp.lean
0
$ grep -nE 'set_option' RBM3D/Induction/SizesComp.lean
38:set_option linter.style.longLine false
```
Only the sole writable file is touched; no frozen signature is changed; no `maxHeartbeats` override. Imports: `RBM3D.Induction.Defs` + six Mathlib modules, not `RBM3D`.
Private helpers: `sizesComp_split`, `sizesComp_split_apply`, `sizesComp_indepFun_split`, `sizesComp_map_split`,
`sizesComp_eventually_of_cover`, `sizesComp_STExp2_comp`, `badSetAt_zero`, `stochDomAt_zero`, `perTimeDomAt_zero`.

## 2. Statements: check-file equality (independent script, compiled)
`mkpin.py` (written by the auditor): the check file up to section 4 with `import RBM3D.Induction.SizesComp` added, then
`comp_voc = comp` and `reindex_voc = reindex` by `rfl`, `example : T2206Check.<X>_pin := @<lib X>` for every
`def …_pin : Prop` it finds (library names per ticket Targets 1-6: `RBM.Gauss.Sizes.X`; `RBM.Gauss.infinitePi_preimage_comp`,
`RBM.Gauss.integral_infinitePi_comp`, `RBM.nth_cover`, `RBM.StochDomAt.of_map`, `{RBM.StochDomAt, RBM.Path.PerTimeDomAt,
RBM.Gauss.HighProbAt}.{map_iff, subseq, iff_cover}`), and for the 9 section-4 instance statements
`example : <statement> := RBM.Gauss.SizesCompInst.<inst_name>`.
```
$ python3 mkpin.py
53 pins; 9 instance statements
$ lake env lean AuditPin.lean > AuditPin.out 2>&1; echo exit=$?; grep -c '^example' AuditPin.lean; grep -c error AuditPin.out
exit=0
64
0
```
64 = 2 vocabulary `rfl`s + 53 pins + 9 instance statements, all accepted. Hence every target's type is the pinned
body (binder order and hypotheses included), and the 9 ticket instances have exactly the check-file statements.
Manual read of the pins against the ticket mathematics (Targets 1-6, hypothesis table): `Tendsto φ atTop atTop` for the
transfers and `subseq`; `Function.Injective` for `MeasurePreserving`, exact image laws (every set, every integrand, no
measurability), `*_comp_iff`; `StrictMono` + `Finite ι` + `∀ᶠ n, ∃ k, n ∈ range (φ k)` for `iff_cover`, `Prec_comp`, the
six composites; law hypothesis `∀ s, μ (f ⁻¹' s) = ν s` (all sets) in `map_iff` and the law-generic composites;
`of_map` with `Measurable f`, `μ.map f = ν`. Scale `(sz.comp φ).size = sz.size ∘ φ`. No special case or weaker variant.

## 3. Target 3 `rfl`s
```
$ sed -n 273,320p RBM3D/Induction/SizesComp.lean | grep -cE 'rfl$'
12
```
`slice/seqXmat/seqHflow/Gt/Lloop/STGM _reindex`, `STKloop/Bctl/STWB/STblk/ellT/STflowE _comp`: all `:= rfl`.
`integral_Lloop_reindex` is `integral_reindex` + `integral_congr_ae` with `Lloop_reindex` (lines 318-319).

## 4. No vacuity, no hidden hypothesis, no cycle
- No new `structure`/`class`/`Prop`-valued `def`: hypotheses are all inline in the signatures (section 2).
  `comp`, `reindexCoord`, `reindex` are data definitions (body = `comp_voc`/`reindex_voc` by `rfl`, section 2).
- Dependencies: only merged modules (`Induction/Defs` and its imports) plus Mathlib; nothing imports an unmerged file.
- No external hypothesis is introduced (no paper citation taken as input), so no limit check is required.
- Generic lemmas reach concrete data through the chain (where each is applied in the file):
```
infinitePi_preimage_comp  233 (seqP_reindex_preimage)     integral_infinitePi_comp  256 (integral_reindex)
seqP_reindex_preimage     242 250 493 500 508 514 603 613 621
integral_reindex          313 318                          map_iff  499 507 513 551 573 589 751
iff_cover                 546 567 586                      comp_sizeTendsto/bandwidth/WO  95-96 (comp_admissible)
stochDomAt/perTimeDomAt/highProbAt_iff_comp_cover  602 / 612 / 620 (the model-law composites)
```

## 5. Compiled nonempty instances (namespace `RBM.Gauss.SizesCompInst`, `d = 3`, `sz0`, `φ = (2 * ·)`)
The 9 ticket instances (statements = check-file section 4, section 2 above) and 6 extra ones compile in the module build:
| endpoint(s) | instance | open premise |
|---|---|---|
| `comp`, field values | `inst_comp_values` (`L 1 = 12`, `W 1 = 7776`, `lam 1 = 1/46656`) | none |
| `comp_admissible` (→ `comp_sizeTendsto/bandwidth/WO`) | `inst_comp_admissible` (`1/6`, `1/10`, from `sz0_admissible`) | none |
| `STFlow_comp` | `inst_flow_comp` (`κ=ε=𝔡=1/10`, `𝔠=1/6`, from `flow_z0`) | none |
| `STConStInd_comp` | `inst_conStInd_comp` (every `𝔠d > 0`, from `conStInd_inst`) | none |
| `measurePreserving_reindex` | `inst_reindex_mp` | none |
| `seqP_withLam_reindex_preimage` (→ `seqP_reindex_preimage`, `infinitePi_preimage_comp`) | `inst_reindex_BA` (`g = 0`, every set) | none |
| `Prec_comp`, target-3 `rfl`s | `inst_STLK_comp` | `STLK sz0 …` (stochastic) |
| `integral_Lloop_reindex` (→ `integral_reindex`, `integral_infinitePi_comp`) | `inst_STExp2_comp` | `STExp2 sz0 …` (stochastic) |
| `Prec_iff_comp_cover` (→ `stochDomAt_iff_comp_cover`, `StochDomAt.iff_cover`, `map_iff`) | `inst_STLK_parity` (parity classes, `Nat.nth`) | `STLK` on both classes (stochastic) |
| `Prec_comp_iff`; `PrecPT_comp_iff`, `Whp_comp_iff` | `inst_Prec_comp_iff`; `inst_PrecPT_Whp_comp_iff` (`0 ≺ 1`, `Whp univ`) | none |
| `StochDomAt.of_map`, `measurable_reindex` | `inst_of_map` | `Prec (sz0.comp (2*·)) ξ ζ` (satisfiable: `inst_Prec_comp_iff`) |
| three `subseq` | `inst_subseq` | none |
| `nth_cover` | `inst_nth_cover` (`c m = m % 2`, `ι = Fin 2`) | none |
| `PrecPT_iff_comp_cover`, `Whp_iff_comp_cover` (→ `perTime`/`highProbAt_iff_comp_cover`, `iff_cover`) | `inst_parity_PrecPT_Whp` | none |

Data are nondegenerate: `sz0` has `L n = 4(n+1) ≥ 3`, `W n > 0`; `φ = 2·` is `StrictMono`; the cover index `Fin 2` is
nonempty and both parity classes are infinite (`parity_infinite`); `U = Unit` is nonempty; no `False` premise, no
collapsed window. Open premises are the stochastic `≺` statements of merged pins (`STLK`, `STExp2`), which CLAUDE.md §4
allows. The hypothesis-free `rfl` lemmas (`comp_L` … `comp_locDomain`, target 3) need no instance to be non-vacuous.

## 6. Axioms (every public declaration, enumerated from the file by `mkax.py`)
```
$ python3 mkax.py
76 public names
$ lake env lean Ax.lean > Ax.out 2>&1; echo exit=$?; grep -c "depends on axioms" Ax.out; grep -c error Ax.out
exit=0
76
0
$ grep -o "\[.*\]" Ax.out | sort | uniq -c
  75 [propext, Classical.choice, Quot.sound]
   1 [propext, Quot.sound]
```

## 7. Name clash against `main` (cda3bb2), full names in the elaborated environment
```
$ cat Clash.lean   # import RBM3D; run_cmd: filter the 76 full names by `env.contains`
$ (cd /Users/junyin/Lean_proof/RBM3D && lake env lean Clash.lean) | tail -1
checked 76 names; present on main: []
```

## 8. Paper deltas
The Lean statements are infrastructure with no paper statement of their own. The two Lean/paper differences are
proposed in the prove report (d): `T2206a` (subsequence stability and finite-cover recovery of `(stoch_domination)`,
used tacitly in the proof of `lem:main_ind`) and `T2206b` (exact image law for every set and integrand, Lean-only),
both as the ticket proposes; `T2206c` (tooling note) is extra and harmless. Coverage complete.

## 9. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. Unpinned public helpers `reindexCoord`, `reindexCoord_injective`, `reindex_eq` (allowed by Target 2(a)) and
  `two_mul_strictMono`, `two_mul_tendsto`, `parity_infinite` (in the instance namespace `SizesCompInst`, which carries
  the file stem); none clash (section 7).
- O2. Instances of the generic lemmas (`infinitePi_preimage_comp`, `map_iff`, `iff_cover`, the law-generic composites)
  are reached through the model-law lemmas applied at `sz0` (section 4), not by separate `example`s.
- O3. Prove report Finding 2 (a `whnf` timeout when closing `inst_STExp2_comp` directly at `sz0`) is worth carrying into
  the regime-assembly ticket: state predicate transfers for abstract `sz`.

## Verdict
| Target | Verdict |
|---|---|
| 1 `Sizes.comp`, field lemmas, 6 transfers | PASS |
| 2 `reindex`, `measurable_reindex`, `measurePreserving_reindex`, exact image laws, `integral_reindex` | PASS |
| 3 13 commutation lemmas (12 `rfl`), `integral_Lloop_reindex` | PASS |
| 4 `Prec_comp_iff`, `PrecPT_comp_iff`, `Whp_comp_iff`, `Prec_comp` | PASS |
| 5 `map_iff` ×3, `of_map`, `subseq` ×3, `iff_cover` ×3, `nth_cover` | PASS |
| 6 law-generic and model-law gluing composites (6) | PASS |

**T2206: PASS.** No dispatcher sign-off needed.
