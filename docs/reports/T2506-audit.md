Auditor model: claude-opus-5-5

# T2506 row a audit (round 2): Wed Oct 14 13:14:29 UTC 2026

Branch `t/T2506` 6d6dde16 (round-1 head a990102c + the repair commit; merge base d3104f3b). `main` 1e0c2368 (row b merged c9b3f490). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2506-audit2` (detached at 6d6dde16).
Scope: rule-(B) repair of round-1 defect (1) (CONTROL H309 (2)), with T2506 Amend 1 in force. Amend 1 accepts `hK1` (row 19's `K^(1) = m_σ` conjunct, guarded `0 < κ → Flow …`) as a premise of targets 4 and 5, so round 1's sign-off item is closed.
Scratch (uncommitted, outside the worktree): `scratchpad/T2506/AuditScratch2T2506.lean`, which is the check file `docs/tickets/checks/T2506-check.lean` (unchanged) plus `import RBM3D.Chain.ExpEtermsBGen`, the round-1 auditor examples A1–A3, and 18 `#print axioms`.

## Repair diff (the only change since round 1)
```
$ git diff --stat a990102c t/T2506
 RBM3D/Chain/ExpEtermsAGen.lean | 16 ++++++++++------
 1 file changed, 10 insertions(+), 6 deletions(-)
$ git show 6d6dde16 -- RBM3D/   (excerpt, hunk @@ -580,16 +580,20 @@)
+set_option maxRecDepth 20000 in
-example (ω : szB.SeqΩ) (cK : ℝ)
-    (hK : ∀ b : Fin 2 → Zd 3 (szB.L 0), ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖ ≤ cK) :
+example (ω : szB.SeqΩ) :
...
-      ((szB.W 0 : ℕ) : ℝ) ^ 3 * ((szB.L 0 : ℕ) : ℝ) ^ 3 * ((etaT (STflowE zB 0) (7 / 8))⁻¹ ^ 2 + cK) ^ 2 :=
+      ((szB.W 0 : ℕ) : ℝ) ^ 3 * ((szB.L 0 : ℕ) : ℝ) ^ 3 * ((etaT (STflowE zB 0) (7 / 8))⁻¹ ^ 2 +
+        ∑ b : Fin 2 → Zd 3 (szB.L 0), ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖) ^ 2 :=
+    (∑ b : Fin 2 → Zd 3 (szB.L 0), ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖)
-      (by norm_num : (7 / 8 : ℝ) < 1) (k := 1) ![true, false] b ω) hK
+      (by norm_num : (7 / 8 : ℝ) < 1) (k := 1) ![true, false] b ω)
+    (fun b => Finset.single_le_sum (f := fun b : Fin 2 → Zd 3 (szB.L 0) =>
+      ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b))
```
The signature of `expLK_envg` (`ExpEtermsAGen:93-96`) takes `hcol`, `hL` and `hK`. The instance now discharges all three at the concrete data: `hcol` by `ExpEtermsAGen_band_col`, `hL` by `szB.norm_Lloop_le`, and `hK` by `Finset.single_le_sum` with `cK := Σ_b ‖K b‖`. The only remaining binder is `ω : szB.SeqΩ`, a sample point, not a hypothesis. This matches round-1 Required item 1 and Amend 1 exactly. No theorem statement changed: the diff touches only this example.

Binders of every `example` in both files, re-listed:
```
$ awk '/^example/{p=1;s=""} p{s=s" "$0} p&&/:=/{print F":"NR": "substr(s,1,90);p=0}' A B   (open binders only)
ExpEtermsAGen:575  (ω)                     ExpEtermsAGen:589  (ω)            <- repaired instance
ExpEtermsAGen:600  none                    ExpEtermsAGen:610  none
ExpEtermsAGen:623/633/651  hLKU : STLKUgL, hGd : STGdecayWgL … 0   (Step-2 pins, allowed)
ExpEtermsAGen:662  none (band tuple)       ExpEtermsAGen:675  generic re-derivation (implicit tuple)
ExpEtermsAGen:681/684/687  none (3 band regimes)
ExpEtermsBGen:945  hAvg : STExpAvgUgL (T2502 pin)   ExpEtermsBGen:956  hLKU, hAvg (pins)
ExpEtermsBGen:968  none   ExpEtermsBGen:977  hGd (pin)   ExpEtermsBGen:992  none   ExpEtermsBGen:1011 generic re-derivation
ExpEtermsBGen:1018/1022  none
```
None of them has an open deterministic hypothesis. Data: `d = 3`, `Zd 3 4`, windows `[7/8,15/16]`, `[5/8,3/4]`, `[15/16,31/32]`. There is no `N = 0`, no empty index, no collapsed window and no `False` premise.

## Build, axioms, hygiene, scope
```
$ lake build RBM3D.Chain.ExpEtermsAGen RBM3D.Chain.ExpEtermsBGen      (audit worktree, 6d6dde16)
exit=0
Build completed successfully (3911 jobs).
$ lake env lean AuditScratch2T2506.lean > audit2_scratch.out; echo exit=$?; grep -c error audit2_scratch.out
exit=0
0
$ grep 'depends on axioms' audit2_scratch.out | sed -E 's/.*depends on axioms: //' | sort | uniq -c   (18 = every public theorem of A and B)
  18 [propext, Classical.choice, Quot.sound]
$ git grep -nwE "sorry|admit|native_decide|axiom" t/T2506 -- RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | wc -l
       0
$ git diff --stat main...t/T2506
 RBM3D.lean                     |    2 +
 RBM3D/Chain/ExpEtermsAGen.lean |  692 +++++++++++++++++++++++++++
 RBM3D/Chain/ExpEtermsBGen.lean | 1027 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    8 +-
 4 files changed, 1725 insertions(+), 4 deletions(-)
$ git diff main...t/T2506 --name-only -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Probe | wc -l
       0
```
All four files are row a's sole writable files. No band file and no frozen signature is touched.

**Registry vs current main.** The H307 header retitle and the three owner texts remain on the branch, and main has not changed those lines since the merge base:
```
$ git diff main...t/T2506 -- RBM3D/Test/Axioms.lean | grep -c 'generic, new files, supervisor 0843'
1
$ git diff main...t/T2506 -- RBM3D/Test/Axioms.lean RBM3D.lean | grep -E '^[-+][^-+]' | cut -c1-70
+import RBM3D.Chain.ExpEtermsAGen
+import RBM3D.Chain.ExpEtermsBGen
-   -- T2502 (BA-V V1s1, DECISIONS §314): the generic Step-6 pins that th
+   -- T2502 (BA-V V1s1, DECISIONS §314): the generic Step-6 pins that th
-/+ `RBM.BA.STExpLKLKHigL, -- … ; -/+ `RBM.BA.STExpDriftLogL, -- … ; -/+ `RBM.BA.STExpDriftDecaygL, -- …
$ git diff d3104f3b main -- RBM3D/Test/Axioms.lean | grep -E '^[-+]' | grep -cE 'STExpLKLKHigL,|STExpDriftLogL,|STExpDriftDecaygL,|T2502 \(BA-V V1s1'
0
$ git merge-tree --write-tree --name-only main t/T2506
CONFLICT (content): Merge conflict in RBM3D.lean
CONFLICT (content): Merge conflict in RBM3D/Test/Axioms.lean
```
The conflicts come only from adjacent lines: main added row b and T2505 import and registry lines next to row a's lines. They resolve by union, which keeps main's lines plus row a's 2 imports, the retitle and the 3 owner texts (see O1).

## Statements (carried from round 1; nothing changed)
No target declaration changed in 6d6dde16 (diff above), so the round-1 statement checks still hold. I recompiled them in this worktree (exit 0 above):
- **A2:** `T2506_FamBase → STExpLKLKHigL` by `stExpLKLKHigL_of`. This is conjunct 1 of `T2506_RowAOf` exactly.
- **A1:** `T2506_FamWard → T2506_RowAOf`. Conjuncts 2 and 3 use `hK1`, which Amend 1 now accepts for targets 4 and 5. Row 18 is discharged inside A1.
- **A3:** the band pins `STExpLKLKHi`, `STExpDriftLo`, `STExpDriftDecay` are re-derived for all `d` with no hypothesis. So no premise is vacuous, and `hK1` is discharged at the band.

No hidden structure-field hypothesis: there is no new def or structure. No cycle. Every import is merged on d3104f3b.

## Paper deltas
Unchanged from round 1: none needed. The repair changes an instance only. Amend 1 records `hK1` as "not a paper delta" (`Def_Ktza`).

## Verdicts
- Target 1 (kit, `ExpEtermsAGen`): **PASS**. The `expLK_envg` instance (A:589) now discharges `hK`. The other kit instances were unchanged and already ok.
- Target 2 (`STExpLKLKHiConclgL_of_LKU`, `stExpLKLKHigL_of`): **PASS**.
- Target 3 (`expDr_EGtK_precg`): **PASS**.
- Target 4 (`STExpDriftLoConclgL_of_LKU`, `stExpDriftLogL_of`): **PASS** (`hK1` accepted by Amend 1).
- Target 5 (`STExpDriftDecayConclgL_of_GdecayW`, `stExpDriftDecaygL_of`): **PASS** (`hK1` accepted by Amend 1; row 18 and W-d already ok).

**Overall: PASS.**

## Observations
- O1 Merge: two content conflicts (`RBM3D.lean`, `Test/Axioms.lean`), from adjacent lines only. The hub resolves them by union: row a's two `import` lines go after the last `import` line, and the registry gets the retitle plus three owner texts. Main has not changed those four registry lines since d3104f3b.
- O2: the prove report is 259 lines, against the ticket's ≤ 250 (T2502b O6) but within CLAUDE.md §6's 300. Its repair section (`:228`, `Wed Oct 14 13:12:46 UTC 2026`) matches the commit. This does not affect any statement.
- O3 (from round 1): the public stem helpers `ExpEtermsAGen_Bctl_le_two` and `ExpEtermsAGen_norm_L_le` have no example of their own. They are not targets.
