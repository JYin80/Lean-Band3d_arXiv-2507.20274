Auditor model: claude-opus-5-5
# T2354 audit, round 2 (UN-49 + UN-50a: GUEPhase/HypB, GUEPhase/LLTransfer)
Branch `t/T2354` @ 08b8c81 (repair of round-1 RETURN), audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2354-audit2` (detached). Round 1 audited 70371d1.

## 1. Files, hygiene, build, axioms
```
$ git diff --name-only main...HEAD
RBM3D/Universality/GUEPhase/HypB.lean
RBM3D/Universality/GUEPhase/LLTransfer.lean
$ git diff --stat 70371d1 HEAD
 RBM3D/Universality/GUEPhase/HypB.lean | 68 ++++++++++++++++++-----------------
 1 file changed, 36 insertions(+), 32 deletions(-)
$ grep -nE "sorry|admit|native_decide|^\s*axiom " HypB.lean LLTransfer.lean; echo hyg=$?
hyg=1
$ lake build RBM3D.Universality.GUEPhase.HypB RBM3D.Universality.GUEPhase.LLTransfer | grep -E "error|^Build"
Build completed successfully (3781 jobs).
$ lake env lean ax.lean   (#print axioms of the 14 public targets) | sed | sort | uniq -c
  14 [propext, Classical.choice, Quot.sound]
$ wc -l (both)  -> 1508 + 503 = 2011  (< 2050 binding stop)
```
Only the two sole writable files are touched; no frozen signature touched.

## 2. Statements (unchanged since round 1)
The repair touches only the `HypBInst` namespace (`HypB.lean:1093-1506`); every hunk starts at line >= 1398:
```
$ git diff -U0 70371d1 HEAD | grep "^@@"
@@ -1398,3 +1398,14 @@ private abbrev Qj (j : ℕ) : ℝ :=
@@ -1408,4 +1419,8 @@ private theorem scj_pos ...
@@ -1414,7 +1429,3 @@ private theorem AM_le_Cm ...
@@ -1423,4 +1434,2 @@ private theorem L0_le_Cm ...
@@ -1434,2 +1443,2 @@ private theorem lt_K ...
@@ -1444 +1453 @@ example : ∃ τ : ℝ, 0 < τ ∧ gueDproc ...   (and 5 more hunks inside this example)
```
`LLTransfer.lean` is unchanged. The round-1 statement diff against the RBM2D source (9e0f275) under the
ticket's port map therefore stands: all 13 HypB targets and `oull_of_pathBounds` match, with the departures
`hd : 2 ≤ d`, `hellN : L^d(1-t₁) ≤ lam²`, `(W^d)⁻¹`, `A = 1 + 2 lam²` (T2354a), `hKinit` with `STKloop`
(T2354b, inherited T2352a(3)), and the `UNOULL` body form / `0 ≤ t n` (T2354c, weaker hypothesis, so
the pin instantiates without a bridge). **Statements: PASS.**

## 3. Hidden hypotheses, vacuity, cycles
Unchanged since round 1: no new structure/def/class; the only external hypothesis is the merged
`GUEPathBounds` (`Grid.lean:89`, UN-50b output) with its limit check in prove report (a)(ii); imports are
merged modules, no cycle. **PASS.**

## 4. Compiled nonempty instances
Round-1 instance table stands for 13 targets (all hypotheses discharged on `szT` = `sz0` with `lam ≡ 8`,
`d = 3`, `L = 4`, `W = 32`, `N = 2097152`, window `[0, 1/1000]`, `gueStop = K > 1`). Round-1 defect:
the `HypB_fixed` instance had `Cm`, `g₃`, `g₄` as sums over the grid `range (K+1)`, `K = (N+1)^128`.

Repair (`HypB.lean:1398-1409`), every grid sum replaced by `Finset.sup'`:
```
private def Cm : ℝ :=
  max (Finset.univ.sup' X2_ne fun x => ‖Lj 0 x - Kt0 0 (uj 0) (loopOf x.1 x.2)‖ / scj 0)
    ((Finset.range (Kg 0 + 1)).sup' rg_ne fun k => Finset.univ.sup' X2_ne fun x => AMj k x / scj k)
private abbrev g3v : ℝ := (Finset.range (Kg 0 + 1)).sup' rg_ne fun j => Finset.univ.sup' X2_ne (AEj j)
private abbrev g4v : ℝ := (Finset.range (Kg 0 + 1)).sup' rg_ne Qj
```
`hq`, `heG`, `h0`, `hM` are now discharged by `Finset.le_sup'` (`:1499`, `:1501`, `AM_le_Cm`,
`L0_le_Cm`); the example applies `HypB_fixed` with `(fun _ => g3v) (fun _ => g4v) (Ce := 1)` and
compiles (build above). `grep -n "∑ .*Finset.range (Kg 0 + 1)" HypB.lean` -> no hits.

Witness sizes, independent re-check (`gueScale = N·etaT`, `Grid.lean:84`; `E0 ≡ 0`, `tA ≡ 0`,
`tB ≡ 1/1000`, `HypB.lean:1099-1101`; `exists_tau` `:1376` gives `τ = 2 log(max C 1)/log N + 2`;
at `ω₀ = 0`, `η₀ = 1`, `|L₀(x00)| = W^{-d}`, `scj 0 = N^{-2}`):
```
$ python3 -I chk.py
N=2097152 h0=1.34218e+08 hM_bound=8.101e+05 Cm=1.34218e+08 tau=4.5714 N^(tau/2)=2.815e+14 N^tau=10^28.9
log10(K+1)=809.2
```
This agrees with the repairer's `sizes.py` output (prove report, Repair section): `Cm = 2^27`, `τ ≈ 4.57`,
`g₃ ≤ 3.9e-6`, `g₄ ≈ 1.17e-10`. None scales with `K` (`log10(K+1) = 809`). `τ` is fixed by the `h0`
term (`K̃ = toyK` vanishes on 2-loops), not by a grid-sized quantity. The round-1 "astronomically large
witness" defect is fixed.

| target | instance | verdict |
|---|---|---|
| 12 HypB targets other than `HypB_fixed` | round-1 instances, unchanged | PASS |
| `HypB_fixed` | `HypB.lean:1445` example, maxima witnesses, τ ≈ 4.57 | PASS |
| `oull_of_pathBounds` | `LLTransfer.lean:490`, unchanged; `GUEPathBounds` kept (other gate) | PASS |

## 5. Paper-delta coverage
No statement changed in the repair. T2354a/b/c in prove report (d) cover every difference found in §2.
**PASS.**

## 6. Observations (no verdict effect)
- O1-O3 of round 1 stand (`τU = 4/7`, `lam ≡ 8` in path instances; `Ξ ≡ univ`; `Kt0 = toyK`).
- O5: prove report Open 2 / item 7 (b) still describe `g₃`, `g₄`, `Cm` as sums (pre-repair text); the
  Repair section states the current maxima. Report text only.
- O6: prove report §(b) item 9 says "τ is existential"; the example's τ is `≈ 4.57`, not the preflight's 3
  (explained in the Repair section).

## 7. Verdict
All 14 targets: statement PASS, instance PASS, build and axioms PASS, paper deltas covered.
Ticket T2354: **PASS**. No dispatcher sign-off needed.
