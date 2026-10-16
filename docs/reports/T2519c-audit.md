Auditor model: claude-opus-5-5
# T2519 row c — audit round 1 (t/T2519c @ 2142049b; worktree RBM3D-wt/T2519c-audit1; Fri Oct 16 15:57:03 UTC 2026)
Inputs: ticket T2519.md, Amends 1-4, prove report T2519c-prove.md. Scratch: scratchpad T2519c/ (sigdiff.py, win.py, c1.py, cmp.py, audit.lean, t0.lean; not committed).

## 1. Scope, size, hygiene
```
$ git diff --name-only main...t/T2519c          # merge-base 9f044e2c; main 544c8a4b differs only in docs
RBM3D.lean  RBM3D/BA/GUEEntry2.lean  RBM3D/BA/GUEEntryGridBA.lean  RBM3D/BA/GUEHypBBA.lean
RBM3D/BA/GUEOneLoop.lean  RBM3D/BA/GUEPathBoundsBA.lean  RBM3D/Test/Axioms.lean
$ git diff --numstat main...t/T2519c -- <3 merged files>      (Amend 4 item 5: <= 200)
56+9=65 RBM3D/BA/GUEEntry2.lean | 43+11=54 RBM3D/BA/GUEEntryGridBA.lean | 55+13=68 RBM3D/BA/GUEOneLoop.lean | total 187
$ git show --stat 86645224   # first commit (Amend 4 item 4): only the three merged files, 154+/33-
$ wc -l: GUEHypBBA 1422, GUEPathBoundsBA 778; GUEHypBBA2 absent (1422 < 1,500)
  row c landed 1422 + 778 + 187 = 2387 <= landing line 2,811; every file < 2,000
$ private decls main -> branch: GUEEntry2 23 -> 23, GUEEntryGridBA 14 -> 14, GUEOneLoop 22 -> 22   (none deleted)
$ examples main -> branch:      GUEEntry2 11 -> 12, GUEEntryGridBA 2 -> 3, GUEOneLoop 7 -> 8       (one new per successor)
$ git diff main...t/T2519c | grep '^+' | grep -cE 'sorry|admit|native_decide|^\+\s*axiom '   -> 0
$ direct imports BA.(MainInd|TwistPins|Step6|TwistStep|TwistAvg) in the two files -> 0; 'TwistAvg' occurrences -> 0, 0
$ grep -cE 'Sizes\.comp|\.comp |pad' GUEHypBBA GUEPathBoundsBA -> 0, 0
```
Registry diff (Axioms.lean): only the `:383` `GUEPathBounds` tail, "BA instance: the registered `UNG1Rowk` at `UNKind.ba` (owed; producer BA-C5)" -> "BA twin `GUEPathBoundsBA` (T2519), instance `gueGrid_pathBoundsBA` (`BA/GUEPathBoundsBA`)", the ticket's Registry text verbatim. RBM3D.lean: two import lines after the last import, before `#assert_rbm_axioms`.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.GUEEntry2 RBM3D.BA.GUEEntryGridBA RBM3D.BA.GUEOneLoop RBM3D.BA.GUEHypBBA RBM3D.BA.GUEPathBoundsBA
Build completed successfully (4011 jobs).   exit=0   (no warning/error line from the five files)
$ lake env lean T2519c/audit.lean   (#print axioms)
HypB_entry_leBA HypB_eG_745BA HypB_eG_746BA HypB_fixedBA Bounds_pathBA pathBounds_of_forall_highProbAtBA
gueBds_h745EBA gueBds_h746BA gueGrid_pathBoundsBA gueEntryMixBA' gueEntryMixBA gueGrid_entry_boundBA'
gueGrid_entry_boundBA gueGrid_expect_oneLoopBA' gueGrid_expect_oneLoopBA : each [propext, Classical.choice, Quot.sound]
exit=0
```
Full `lake build` (with `#assert_rbm_axioms`) is the hub's at merge; the prove report shows it green at 2142049b.

## 3. Amend 4 item 2 (primed successors, wrappers)
```
$ python3 -I T2519c/sigdiff.py      # docstring + signature up to ':=' extracted from `git show main:` and `git show t/T2519c:`
GUEEntryMixBA: signature identical main vs t/T2519c: True; docstring identical: True
gueEntryMixBA: signature identical main vs t/T2519c: True; docstring identical: True
gueGrid_entry_boundBA: signature identical main vs t/T2519c: True; docstring identical: True
gueGrid_expect_oneLoopBA: signature identical main vs t/T2519c: True; docstring identical: True
GUEEntryMixBA def body identical: True
```
From the diff (read in full):
- `GUEEntryMixBA'` = `GUEEntryMixBA` with `0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal …` (every `n`) split into `(∀ n, BAReal …) → (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹)`. That is the only change.
- `gueGrid_entry_boundBA'`: `hdata` becomes `hr : ∀ n, BAReal …` plus `hwin : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹`.
- `gueGrid_expect_oneLoopBA'`: `(∀ n, 0 < g n ∧ g n ≤ Λ)` becomes `(∀ᶠ n in atTop, …)`, and `hr` stays `∀ n`.
- **Moved, not copied.** The old proof bodies now sit under the primed names. In each, the window is one more entry of `filter_upwards` (`hwin`/`hg`). `(hg 0)` in `hCM0` was replaced by `BAct_rate_pos` + `positivity`. Each unprimed theorem is a 2-4 line wrapper through `Filter.Eventually.of_forall`.
- The existing examples are untouched, and each successor has one new `example` on the existing instance data (`GUEEntry2:1008`, `GUEEntryGridBA:444`, `GUEOneLoop:1427`). All of them compile in the build above.
- Stop rule item 6 was not hit: no new `Prop` premise, and the changed proof lines are well under 60. **PASS.**

## 4. Targets 9-11: statements
Target 9 is the HypB twins, target 10 is `Bounds_pathBA` and `pathBounds_of_forall_highProbAtBA`, and target 11 is `gueBds_h745EBA`, `gueBds_h746BA` and `gueGrid_pathBoundsBA`. There is no verbatim pin, so they are checked against the band source and the ticket's mathematics.
```
$ python3 -I T2519c/cmp.py     # conclusion token diff, band -> BA
gueBds_h745E -> gueBds_h745EBA : etaT->etaOf, E->m, loop length m->l, gueLproc/gueDproc -> ...BA (+ g, m args)
gueBds_h746  -> gueBds_h746BA  : same renames only
Bounds_path  -> Bounds_pathBA  : BoundsACheck.Concl -> BoundsBA_Concl (+ g, m)
HypB_entry_le -> HypB_entry_leBA: centre mE•1 -> Mres (gΨ_I) E m; constant 1+2lam² -> 1+4/κ²; loopMax inline -> gueLmaxBA _ 2
HypB_fixed   -> HypB_fixedBA   : (no conclusion change)
$ python3 -I T2519c/win.py     # coupling-window forms in public statements (Amend 4 item 3)
gueBds_h745EBA / gueBds_h746BA / gueGrid_pathBoundsBA: `∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹` x1; `∀ n, BAReal` x1; guard `0 < g n →` x2
all other public declarations: per-`n` lemmas, no window; `∀ n, 0 < g n ∧` occurs in no row-c statement
$ python3 -I T2519c/c1.py      # ticket rule C1 tokens; Pgue/PathΩ/filt only at (sz.withLam 0)
public statements scanned in 2 files; C1 hits: 0
```
- **`gueGrid_pathBoundsBA`** concludes `GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz 4) 4 Kt`, with `hK` at lengths `≤ 4 * 4`. That is `n₀ = 4` (Amend 1 item 1 (a)); the general-`n₀` proof is the private `GUEPathBoundsBA_main`.
- **Premises against the band `gueGrid_pathBounds` (`PathBounds:550`):**
  - `hE` is replaced by `BAReal` at every `n` (coverage row 15).
  - `hKb : STKbound` is dropped. Row a's `Hyp_Kt_detDomBA` supplies the K-bound (coverage row 12), so the statement is stronger in that respect.
  - `hKinit` is `BAKsol` at `t₁`, guarded by `0 < g n`.
  - `hLK` and `hLoc` are `STLKgL`/`STLocalEntrygL` on `baFM sz g E`, i.e. `BAMO` conjuncts 1-2.
  - One added premise, `hellg : L^d (1-t₁) ≤ 2 g²`.
- The quantifier order matches the band: fixed parameters first, then the eventual premises, then `Kt`.

Exact-type fit to row d, and `hellg` (the scratch file compiles, exit 0, as above):
```
example … (hKF : BAKFam d sz E' t1 t0 Kt) (hr …) (hlam …) … (hLK …) (hLoc …) : BAPB d sz E' t1 t0 Kt :=
  gueGrid_pathBoundsBA sz hd hadm hκ hτU hr hlam ht1 ht10 ht0 h730 hscale hell hell1 hellg Kt hKF.1 hKF.2.1 hLK hLoc
example … : (L:ℝ)^d*(1-t1) ≤ 2*(Real.sqrt t0*lam)^2 := GUEHypABA_hell_of_hell hd hL ht10 hell hell1
```
So `BAKFam` clauses 1-2 are exactly `hKinit`/`hK` at `g = √t₀ λ`, `m = BAm …`. The conclusion is `BAPB` at exact type. `hellg` follows from `RBG_Prod`'s `hell`, `hell1` by row a's lemma, so it is not a new deterministic burden. Hidden hypotheses: none. `GUEPathBoundsBA` is row a's merged `def` (two conjuncts, no structure field). `BoundsBA_Concl` is a transparent `abbrev`, used only inside `hmain`. No row-c theorem takes `GUEPathBoundsBA` as a hypothesis, so there is no cycle. Every dependency is on `main` (rows a and b merged; C3, C4 merged).

## 5. Target 12: compiled nonempty instances
All instances are at `d = 3`, `sz0` (`N₀ = 2^21`, `L₀ = 4`, `W₀ = 32`), with the flow datum `(BAflowLam0, BAflowEs, BAmF)` of `flow_sz0` (`BAReal` at `κ = 1/2` for every `n`).
- **Endpoint `gueGrid_pathBoundsBA`** (`GUEPathBoundsBA:765`), data: `n₀ = 4`, `τ_U = 1/20`, `1 - t₀ = λ²/(4L³)`, `t₀ - t₁ = x/(2N)`.
  - `hlam` comes from `BAflow_lam0_window` (eventual). `hscale` is eventual (`j_hscale`, `n ≥ 1`). `h730`, `hell`, `hell1` and `hellg` are discharged for every `n`.
  - `Kt`, `hKinit` and `hK` come from `gueK_existsBA` (row a's `GUEHypABAInst_K`).
  - Only `hLK` and `hLoc` stay as hypotheses: they are BAMO conjuncts 1-2, the consumer form of the V3 pin `UNMLOutBA`.
  - `gueBds_h745EBA` (`:736`) and `gueBds_h746BA` (`:750`) use the same data; only `hLK` stays.
- **GUEHypBBA** (`:1326-1415`), data: `n = 0`, `t₀ = 199/200`, `t₁ = t₀ - 10⁻⁶`, `τ_U = 1/2`, `n₀ = 4`, `A = 17`. Every deterministic premise is discharged (`hm`, `hm1`, `ht*`, `h730`, `hscN`, `hellN`, `hsmallN`, `h4N`, the grid conditions, `hbig`, the K-family premises).
  - Left open are the pathwise event hypotheses: `hD4`, `hj`, `hdiag`, `hA`-`hF`, `h0`, `hM`, `hq`, `heG`, i.e. the outputs of other lemmas at one `ω`.
  - `pathBounds_of_forall_highProbAtBA` is applied at concrete data, with its only premise (`hmain`) probabilistic.
- None of the instances is degenerate: no `N = 0`, no empty index, no collapsed window, no `False` premise. **PASS.**

## 6. Paper-delta coverage
Each Lean/paper difference found above is covered by a candidate in prove report (d) item 4:
- `T2519ca`: the A3 constant `1 + 4/κ²`, and D4a without a zero-mode premise.
- `T2519cb`: the step-0 inputs are BAMO conjuncts 1-2, and there is no `STKbound` premise.
- `T2519cc`: the three zero-mode forms, `hellg` included.
- `T2519cd`: the eventual window (Amend 4 item 8).
- `n₀ = 4` is Amend 1's `T2519a`.

No uncovered difference found.

## 7. Observations (no verdict effect)
1. The instance time `t₁` of `GUEPathBoundsBA:736-765` lies above the flow horizon:
   ```
   $ lake env lean T2519c/t0.lean   # example (n) : BAflowT0 sz0 zSeq n ≤ 5/6   (BAm_norm_le_one, Im z + Im m = 6/5) -> exit 0
   $ python3 -I -c '…'            # it1 n = 1 - x - x/(2N): n=0 0.999999046325 > 5/6; n=1..3 > 5/6
   ```
   So at this data `hLK`/`hLoc` are not consequences of `UNMLOutBA 3` at `flow_sz0`, whose range is `t ≤ BAflowT0`. They are local-law statements of the pin's type at a mesoscopic `η` (`N η_{t₀} ≥ (n+1)³`). This is the same shape as the merged band instance (`PathBounds:893`, `sz0.STLK Ei tw1`). The prove report's phrase "`hLK`, `hLoc` are the pin `UNMLOutBA`" is accurate only as to type.
   - For row d: with `hell` (`L^d(1-t₁) ≤ λ²`), `t₁ ≤ T0` forces `T0` close to 1, so the producer instance needs a `z`-sequence with small `Im z`, not `zSeq`.
2. The prove report puts the per-file diff count 187 on 9f044e2c..HEAD, which equals the main...t/T2519c count above.

## 8. Verdicts
| Target | Verdict |
|---|---|
| 9 HypB twins (`HypB_entry_leBA`, `HypB_eG_745BA`/`746BA`, `HypB_fixedBA`, grid facts) | PASS |
| 10 `Bounds_pathBA`, `pathBounds_of_forall_highProbAtBA` | PASS |
| 11 `gueBds_h745EBA`, `gueBds_h746BA`, `gueGrid_pathBoundsBA` (n₀ = 4, eventual window) | PASS |
| 12 instances | PASS |
| Amend 4 item 2 (`GUEEntryMixBA'`, `gueEntryMixBA'`, `gueGrid_entry_boundBA'`, `gueGrid_expect_oneLoopBA'`, wrappers) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
