Auditor model: claude-opus-5-5

# T2450 audit (round 1) — Mon Oct 12 15:33:22 UTC 2026 (`date -u`)

Branch `t/T2450` at `195837c`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2450-audit1` (detached, cache cloned);
scratch `$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2450/audit`.

## 1. Diff, size, hygiene
```
$ git diff --name-only main...t/T2450
RBM3D/Graph/BAS3Close.lean
RBM3D/Graph/BAS3CloseB.lean
RBM3D/Graph/BAS3CloseC.lean
$ wc -l RBM3D/Graph/BAS3Close*.lean          # stop line 2,000 per file
    1953 BAS3Close.lean     837 BAS3CloseB.lean    1661 BAS3CloseC.lean    4451 total
$ git diff main...HEAD --stat -- RBM3D/Test RBM3D.lean      # (empty: Test/Axioms.lean and RBM3D.lean untouched)
$ git diff --quiet main...HEAD -- docs/tickets/checks/T2450-check.lean && echo "check file same on branch"
check file same on branch
$ grep -nE '\b(sorry|admit|axiom|native_decide)\b|^(structure|inductive|class) |\bopaque\b|implemented_by|@\[extern|\bunsafe\b' RBM3D/Graph/BAS3Close*.lean | wc -l
0
$ git grep -nE 'BAS3|baS3|BAFoldLeaf|baFoldLeaf' main -- RBM3D | wc -l
0
```
All three files are sole writable files (`BAS3CloseC` is the named reserve). No new `structure`/`inductive`/`class`.
Imports: `BAG5Leaf`, `BALvl1B`, `TwistFold2B`, `BAExp14bB`, `GreenStab` (each a file on `main` and root-imported in `main:RBM3D.lean`), plus the chain `BAS3Close → BAS3CloseB → BAS3CloseC`. No cycle.

Public declarations (script: every `theorem|def|abbrev|instance|structure` line not starting with `private`):
```
BAS3Close.lean:56 def baS3RootM   :66 def baS3Root1   :78 def baS3RootD   :88 def BAS3expandRoot   :95 def BAS3Identity
BAS3Close.lean:130 theorem baS3Identity_holds
BAS3CloseB.lean:326 def baS3Stuck   :827 theorem baS3Close_mod
BAS3CloseC.lean:965 def BAFoldLeaf  :985 theorem baFoldLeaf_congr  :1364 def BAS3Xprec  :1374 theorem baS3Xprec_holds
BAS3CloseC.lean:1427 theorem baS3Fold_holds  :1448 theorem baS3Stuck0_val  :1483 def BAS3Close  :1486 theorem baS3Close_holds
BAS3CloseC.lean:1493 def BAS3Expand'  :1497 theorem baS3Expand'_holds
BAS3CloseC.lean:1508,1523,1525,1550,1584,1637 BAS3CloseInst.{baS3_inst_identity, _fold, _congr, _rho0, _expand', _close}
```
Every new `Prop` def (`BAS3Identity`, `BAFoldLeaf`, `BAS3Xprec`, `BAS3Close`, `BAS3Expand'`) is concluded by a public theorem.
No public theorem has a `BACtx`/`BAG5Leaf`/`BAG5Tgt`/`BAG5Attached`/`BAG5LeafProps` hypothesis (helpers private: 149/106/114
`private` lines). `BAS3Close_Inv`, `BAS3Close_rho`, `BAS3Close_Bd` are private.

## 2. Build in the audit worktree
```
$ time lake build RBM3D.Graph.BAS3Close RBM3D.Graph.BAS3CloseB RBM3D.Graph.BAS3CloseC
✔ [4026/4028] Built RBM3D.Graph.BAS3Close (12s)
✔ [4027/4028] Built RBM3D.Graph.BAS3CloseB (62s)
✔ [4028/4028] Built RBM3D.Graph.BAS3CloseC (16s)
Build completed successfully (4028 jobs).
... 1:34.80 total ; exit 0
$ grep -cE '^(warning|error): RBM3D/Graph/BAS3' build.log
0
```
(The full `lake build` with `#assert_rbm_axioms` is the hub's at merge.)

## 3. Statements against the pins (script: the check file + the three imports + a closing block, compiled)
`$S/check_closed.lean` = `docs/tickets/checks/T2450-check.lean` with `import RBM3D.Graph.BAS3Close{,B,C}` added and this block
inserted before `end RBM.Graph.T2450Check` (not committed). Definitional equality of every pinned `Prop` def is checked by `Iff.rfl`,
the data pins by `rfl`, every theorem pin by the theorem as a term:
```
example : T2450_rootM_eq baS3RootM := fun s => rfl
example : T2450_root1_eq baS3Root1 := fun s => rfl
example : T2450_rootD_eq baS3RootD := fun s => rfl
example : T2450_expandRoot_eq baS3RootM baS3Root1 baS3RootD BAS3expandRoot := fun _ _ _ => ⟨rfl, rfl, rfl⟩
example : ∀ q, BAFoldLeaf q ↔ T2450_BAFoldLeaf q := fun _ => Iff.rfl
example : ∀ d Ls, BAS3Identity d Ls ↔ T2450_BAS3Identity baS3RootM baS3Root1 baS3RootD d Ls := fun _ _ => Iff.rfl
example : BAS3Close ↔ T2450_BAS3Close BAS3expandRoot := Iff.rfl
example : ∀ d, BAS3Expand' d ↔ T2450_BAS3Expand' baS3RootM baS3Root1 baS3RootD d := fun _ => Iff.rfl
example : ∀ d, BAS3Xprec d ↔ T2450_BAS3Xprec d := fun _ => Iff.rfl
example : T2450_identity baS3RootM baS3Root1 baS3RootD BAS3expandRoot := baS3Identity_holds
example : T2450_foldCongr := baFoldLeaf_congr
example : ∀ d : ℕ, T2450_BAS3Xprec d := baS3Xprec_holds
example : T2450_stuck0_val baS3Stuck := baS3Stuck0_val
example : T2450_reductions baS3Stuck := baS3Fold_holds
example : T2450_BAS3Close BAS3expandRoot := baS3Close_holds
example : ∀ d : ℕ, T2450_BAS3Expand' baS3RootM baS3Root1 baS3RootD d := baS3Expand'_holds
$ cd RBM3D-wt/T2450-audit1 && lake env lean $S/check_closed.lean ; echo "exit $?"
exit 0          (0 error lines)
```
So each target equals its pin (hypotheses, quantifier order — `∃ Cρ` before `∀ᶠ n`, uniform in `t ∈ [0,T₀]` and `(a,b)` —,
`W^{-2d}` normalisation, `X = W^{-d}Σ_{u∈[c₂],v∈[c₄]}Ǧ_{uv}Ǧ_{vu}` (= `W^d Tr`, not `W^{2d}`), `X ≺ W^d·Bctl`, selector
`BAselStar`, fuel 2, both charges, three roots with coefficient 1) up to `Iff.rfl`/`rfl`. The roots are the pin's data literally.

## 4. Vacuity, hidden hypotheses, cycles
- `BAFoldLeaf`: `ρ` has type `d → sz → z → n → t → a b c₁..c₄ → ℂ` (no `ω`), so clause (i) is a genuine pathwise identity; clause (ii)
  bounds come from merged `baM_row_l1`, `baM_col_l1`, `BAExp14a_theta_l1`, `BAExp14a_theta_col` (private `BAS3Close_Bd_of`).
- The 13 non-anchor catalogue entries are unpinned data, but they are not free: `baS3Close_holds` is proved from `baS3Close_mod`
  (every output of the three trees is a `BAG5LeafProps` leaf or value-equal to some `baS3Stuck k j s`) plus `baS3Fold_holds`, so the
  catalogue is forced to cover the real stuck outputs.
- Stochastic inputs: `STLocalEntrygL`, `STLmaxgL` occur only inside `BAS3Xprec` (as pinned) and as hypotheses of the two `example`s.
  Both are registered owed pins of other gates; prove report (a)(ii) gives a limit check at `sz0` (leading term of `W^d L^{(2)}` max
  entry 1.9959 vs `B_0 = 2.0303`). No other external hypothesis.
- No structure field carries a hypothesis (no new structure). Dependencies: merged modules only (§1).

## 5. Compiled nonempty instances (`BAS3CloseC.lean:1502-1657`, built above)
| target | instance | data | deterministic hyps |
|---|---|---|---|
| 1 identity | `baS3_inst_identity` | `d=3, L=3, W=1, g₀=0, E=0, t=1/2, m=i`, all `x y`, both `s` (ticket's data) | `baSelf_zero`, `norm_num` |
| 2, 3 | `baS3_inst_fold`, `baS3_inst_congr` | `baS3Stuck false 0 false` | none left |
| 3 consumed | `example` :1530 | `sz0`, `zSeq`, `t ≡ 1/2`, via `twFold2PrecDet_holds` | `flow_sz0`, `half_lt_t0`; only `hE hL` kept |
| 3 weight | `baS3_inst_rho0` | anchor weight = `TwistFold2_rho2` (`ρ₀ = t²1[c₃=c₁∧c₄=c₂](M^B_{c₁c₂})²`) | — |
| 3′ | `example` :1573 | `d=3`, `sz0`, `zSeq`, `t ≡ 1/2` | `flow_sz0`, `half_lt_t0`; only `hE hL` kept |
| 4 | `baS3_inst_close` | 6 lists nonempty; a `BAG5LeafProps` leaf and a `BAFoldLeaf` in `MERGED`/`false` | `decide +kernel` |
| 5 | `baS3_inst_expand'` | `d = 3` | — |
None is degenerate (`sz0`: `L=4, W=32, N=2097152`; no empty index, no `False` premise; target 1 uses the ticket-pinned `W=1` data).

## 6. Axioms (same scratch file, `#print axioms`)
```
'RBM.Graph.baS3Identity_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baS3Close_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baFoldLeaf_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baS3Fold_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baS3Stuck0_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baS3Xprec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baS3Close_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baS3Expand'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAS3CloseInst.baS3_inst_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAS3CloseInst.baS3_inst_fold' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAS3CloseInst.baS3_inst_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAS3CloseInst.baS3_inst_rho0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAS3CloseInst.baS3_inst_expand'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAS3CloseInst.baS3_inst_close' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 7. Paper-delta coverage
Lean statements equal the dispatcher's pins (§3). The differences from the sources are proposed in the prove report (d):
T2450a (black waved `σ = false` in the pins vs `true` in T2433's `roots.py`; inert since `WEdge.val` ignores `σ` when `col = false`),
T2450b (Fable §4 table's `W^{2d}` at #17/#47 is `W^d`; Lean `BAS3Close_cK3_blk`, `baS3Xprec_holds`), T2450c (the six `T3C-tr_1`
kid weights, not in Fable), T2450d (`Cρ` from crude merged ℓ¹ bounds). No uncovered statement difference found.

## 8. Verdicts
| target | verdict |
|---|---|
| 1 roots, `BAS3expandRoot`, `BAS3Identity`, `baS3Identity_holds` | PASS |
| 2 `BAFoldLeaf`, `baFoldLeaf_congr` | PASS |
| 3 `baS3Stuck`, `baS3Fold_holds`, anchor `baS3Stuck0_val`; 3′ `BAS3Xprec`, `baS3Xprec_holds` | PASS |
| 4 `BAS3Close`, `baS3Close_holds` | PASS |
| 5 `BAS3Expand'`, `baS3Expand'_holds` | PASS |
| 6 instances | PASS |
**Ticket verdict: PASS.** No dispatcher sign-off needed.

## 9. Observations (no RETURN)
1. Extra public names beyond the pins: `baS3Close_mod` (lowercase `baS3Close_` rather than the stem `BAS3Close_`; rule (E)) and
   `baS3Stuck0_val`; both are concluded theorems with no `BACtx`/`BAG5*` hypothesis. Cosmetic.
2. Ticket (i) says "margin at the 12 nodes with `e = false`"; the catalogue has 14 nodes, 4 with `e = true`, so 10 (prove report (a)(i)
   says the same). Ticket arithmetic only; no statement affected.
3. The `S3A-C5 (a)`/(c) numerics of the 1a (rel. err ≤ 2.7e-15; closure counts) were not re-run by the auditor; the Lean theorems
   (pathwise identity in `baS3Fold_holds`, `baS3Close_mod` by `decide +kernel`) supersede them.
4. `RBM3D.lean` is not edited on the branch; the hub adds the three imports at merge (rule A.4).
