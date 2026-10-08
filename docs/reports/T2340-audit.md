Auditor model: claude-opus-5-5

# T2340 audit (round 1) — ST-6 R1–R3, `lem:main_ind` → `UNMLOut`

Written Thu Oct  8 19:46:50 UTC 2026 (`date -u`). Branch `t/T2340` at 5d07707 (base 74cdcb9); `main` at 1546ef7.
Worktrees: `RBM3D-wt/T2340-audit1` (detached at 5d07707) and `RBM3D-wt/T2340-audit1m` (detached at `main` 1546ef7,
the branch's three new files and `AzumaProxyN.lean` checked out, the branch's `Test/Axioms.lean` patch applied 3-way).

## 1. Files touched

```
$ git diff --numstat main...t/T2340
1	1	RBM3D/Induction/AzumaProxyN.lean
164	0	RBM3D/Induction/MainIndBase.lean
251	0	RBM3D/Induction/MainIndChain.lean
223	0	RBM3D/Induction/MainIndOut.lean
10	0	RBM3D/Test/Axioms.lean
$ git diff main...t/T2340 -- RBM3D/Induction/AzumaProxyN.lean | grep "^[-+][^-+]"
-private theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m)
+theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m)
$ git diff main...t/T2340 | grep -nE "^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom " ; echo "hits: $?"
hits: 1          (grep exit 1 = no match)
$ git merge-tree --write-tree main t/T2340; echo $?
c51ef9f233cc26d0371cba1dd80b5beeee99c6e5
0
```
Only the sole writable files; the `AzumaProxyN.lean` edit is the one keyword at line 597; no frozen signature changed.
Sizes 164 + 251 + 223 = 638 (ticket 650 / 900 / 1100; stop rule 1200 not reached).

## 2. Statements against the pins (check file equality, script)

Scratch file = the check file `docs/tickets/checks/T2340-check.lean` verbatim (imports + `import RBM3D.Induction.MainIndOut`),
then:
```
example : @RBM.T2340Check.T2340_STConclgL = @RBM.BA.STConclgL := rfl
example : @RBM.T2340Check.T2340_STLK0 = @RBM.BA.STLK0 := rfl
example : @RBM.T2340Check.T2340_STG0M = @RBM.BA.STG0M := rfl
example : @RBM.T2340Check.T2340_STBaseG = @RBM.BA.STBaseG := rfl
example : @RBM.T2340Check.T2340_STHorizonG = @RBM.BA.STHorizonG := rfl
example : @RBM.T2340Check.T2340_STMLOutG = @RBM.BA.STMLOutG := rfl
example : @RBM.T2340Check.T2340_stChainTime = @RBM.BA.stChainTime := rfl
example : RBM.T2340Check.T2340_stBase_band := RBM.BA.stBase_band
example : RBM.T2340Check.T2340_stHorizon_band := RBM.BA.stHorizon_band
example : RBM.T2340Check.T2340_stMLOutG_of_mainIndG := RBM.BA.stMLOutG_of_mainIndG
example : RBM.T2340Check.T2340_unMLOut_of_mainInd := RBM.Univ.unMLOut_of_mainInd
example : RBM.T2340Check.T2340_unMLOutBA_of_pins := RBM.Univ.unMLOutBA_of_pins
example : RBM.T2340Check.T2340_stMainInd_of_LW := RBM.Gauss.Sizes.stMainInd_of_LW
example : RBM.T2340Check.T2340_unMLOut_of_LW := RBM.Univ.unMLOut_of_LW
```
`$ lake env lean eq.lean; echo "exit $?"` (audit1 worktree) → the section-1 `#check` lines, the axiom lines of §4, `exit 0`.
All seven definitions are definitionally the pins; all seven pinned targets have exactly the pinned types.
`stBase_band` has no hypothesis; `unMLOut_of_mainInd` has only `STMainInd d` (no `STLoopZeroId`; that name is not defined).

Unpinned-by-text targets (ticket names, no check pin), read against the ticket's mathematics:
- `stBaseG_of_init`: `IsProbabilityMeasure (law sz)`, `STLK0`, `STG0M` at every flow point, `STKboundgL` under `3 ≤ d`, `0 < κ`
  → `STBaseG`. Matches R1 (`𝓛_0 = 𝒦_0`, `G_0 = M`, `ML:Kbound`; delta `T2338d`).
- `stChainSteps`: `K·𝔠_d·min(2𝔠𝔡, τ) ≥ 2` with `K` fixed (not depending on `n` or `t`), `Bandwidth`, `WO`, `SizeTendsto`, `T < 1`,
  `N^{-1+τ} ≤ 1 - T` eventually, `0 < t ≤ T`, `k < K` → `STConStInd 𝔠d p_k p_{k+1}`. Matches `(con_st_ind)` `1_2:1296-1298`.
- `STLocalMaxgL_of_STLocalEntrygL`: no hypothesis beyond the premise; twin of `STLocalMax_of_STLocalEntry`.
- `stPosConclG_of_mainIndG`: `STMainIndG`, `STHorizonG`, `STBaseG` → the six conclusions at every `0 < t_n ≤ T0`. Order
  `3 ≤ d → ∀ κ ε 𝔡 𝔠 …` as `UNMLOut`. Uses `STMainIndG` with `s = p_k < t = p_{k+1} ≤ T0` (`Flow sz κ ε 𝔠 𝔡 z` passed through).
- `unMLOut_iff`: `Iff.rfl` (compiles; `UNMLOut` is literally `STMLOutG` at the band data, `Universality/Pins.lean:432`).

## 3. Hidden hypotheses, vacuity, cycles

- No new structure; the carriers (`FlowFM`, `STFlow`, `BAFlow`, `bandFM`, `baFMz`) are merged. `STHorizonG`, `STBaseG` are
  explicit `Prop` premises, discharged at the band data (`stHorizon_band`, `stBase_band`); owed at the BA data (BA-V).
- `stMainInd_of_LW` hypotheses are only `LWterm d`, `LWtermExp d` (owed, LW-01); every other premise is a merged `_holds`
  theorem; axioms standard (§4), so no premise is smuggled. No dependency on a T2340 declaration from upstream (one-way
  imports R1 → R2 → R3; `MainIndBase` imports `BA.FlowPins`, `Induction.AzumaProxyN`, `Graph.LWExpTerm3`).
- Registry pre-check on `main` + branch (audit1m):
```
$ lake build RBM3D RBM3D.Induction.MainIndOut 2>&1 | grep -E "error|^Build"
Build completed successfully (4156 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.MainIndOut\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean | tail -2; echo $?
non-vacuity certificates: 0 of 133 premises in the two ledgers; the rest are not known to be satisfiable (...)
0
```

## 4. Build and axioms

```
$ lake build RBM3D.Induction.AzumaProxyN RBM3D.Induction.MainIndBase RBM3D.Induction.MainIndChain \
    RBM3D.Induction.MainIndOut RBM3D.Test.Axioms 2>&1 | grep -E "error|^Build"      (audit1, branch tip)
Build completed successfully (4040 jobs).
'RBM.BA.stMLOutG_of_mainIndG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stBase_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stHorizon_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stBaseG_of_init' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stChainSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STLocalMaxgL_of_STLocalEntrygL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stPosConclG_of_mainIndG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMLOut_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMLOut_of_mainInd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMLOutBA_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stMainInd_of_LW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMLOut_of_LW' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Name-clash grep (`grep -rlE "(theorem|def|lemma|abbrev) <name>( |$)" RBM3D`, outside the three files and `Probe/`, on main+branch):
every new public name `:0` (23 names, incl. `mainIndBase_bctl_nonneg`, `stChainTime_{zero,top,facts}`). The now-public
`azumaProxy_loopFine_sub_STKloop` is defined only at `AzumaProxyN.lean:597`.

## 5. Compiled nonempty instances (all in the target files, compiled by the builds above)

Data: merged `sz0`, `z0` (band, `d = 3`, `𝔠 = 1/6`, `κ = ε = 𝔡 = 1/10`, `flow_z0`), `zSeq` (BA, `flow_sz0`, `t0_sz0`).
| target | instance | open hypotheses |
|---|---|---|
| `stBase_band` | `MainIndBase` §4 ex. 1: `STConclgL (bandFM sz0 …) (seqP sz0) 0` | none |
| `stBaseG_of_init` | §4 ex. 2 at BA `sz0`, `zSeq`; fully discharged through `stBase_band` (band) | BA carrier facts `STLK0`/`STG0M`/`STKboundgL` (BA-V) |
| `stChainTime` facts | `MainIndChain` §5, `t = 1/2`, `K = 2`, `k = 1` | none |
| `stHorizon_band` | §5 at `sz0`, `z0` | none |
| `stChainSteps` | §5 `K = 6000`, `𝔠_d = 1/100`, `τ = ε/2`, `t = lemT z0/2 > 0`, `k = 5999` | none |
| `STLocalMaxgL_of_STLocalEntrygL` | §5 at band data, `t ≡ 0` (premise from `stBase_band`) | none |
| `stPosConclG_of_mainIndG` | §5 at `t = lemT z0/2` | `STMainInd 3` (owed pin) |
| `stMLOutG_of_mainIndG` | `MainIndOut` §6 at `t ≡ 0` (the mixing class) | `STMainInd 3` |
| `unMLOut_of_mainInd` | §6 at `t = lemT z0/2` | `STMainInd 3` |
| `unMLOutBA_of_pins` | §6 at BA `sz0`, `zSeq`, `t = 1/2 ≤ 2/3 ≤ t₀` | the three BA pins (BA-V) |
| `stMainInd_of_LW`, `unMLOut_of_LW` | §6, `d = 3`; second at `t = lemT z0/2` | `LWterm 3`, `LWtermExp 3` (owed) |

No `N = 0`, empty index set, collapsed window or `False` premise; all open hypotheses are other gates' pins.

## 6. Paper deltas

Lean/paper differences: uniform grid chain vs the paper's two phases (`1_2:1310`); `t = 0` handled as a separate
base case since `lem:main_ind` needs `s < t`; "uniformly in `t`" read per time sequence; the base case uses `ML:Kbound`.
These are candidates `T2338a`–`T2338d` (`docs/reports/T2338-design.md:161-164`), carried in the prove report (d) item 4;
`grep -c T2338 docs/paper-deltas.md` → `0`, i.e. still candidates awaiting dispatcher numbering. The internal horizon
`N^{-1+ε/2} ≤ 1 - T0` of `STHorizonG` is a pinned Lean device (check section 2), discharged at the band from
`Im z ≥ N^{-1+ε}`; it changes no paper statement. No further candidate needed.

## 7. Observations (no RETURN)

- O1 (merge mechanics, for the hub). `main` changed `Test/Axioms.lean` after the branch base (T2297: removes the
  `LWMoment` line, reclassifies `LWMomentExp`, adds `LWMomentCtx`). Copying the branch's file wholesale (`git checkout
  t/T2340 -- RBM3D/Test/Axioms.lean`) would revert that, and the registry then fails, as seen in the stale-base
  worktree: `error: axiom audit: 1 premise(s) … [RBM.Gauss.Sizes.LWMomentCtx]`. Bring the file in by its diff
  (`git diff main...t/T2340 -- RBM3D/Test/Axioms.lean | git apply --3way` applied cleanly; registry exit 0, §3).
- O2. Beyond the ticket's six classifications, `Test/Axioms.lean` also adds the existing pins `RBM.BA.STMainIndG`
  and `RBM.BA.STLocalEntrygL` to `owedProps` (needed by the registry once `MainIndOut` is imported). Consistent with
  the band forms `STMainInd` (line 108), `STLocalEntry` (line 181), all in `owedProps` (lines 101-244); no deletion.
- O3. The stMLOutG_of_mainIndG example is at `t ≡ 0`; positive `t` reaches the same theorem through the
  `unMLOut_of_mainInd` example (`t = lemT z0/2`).

## Verdict

All targets: **PASS**. No dispatcher sign-off required for the statements (O1 is a merge instruction to the hub).
