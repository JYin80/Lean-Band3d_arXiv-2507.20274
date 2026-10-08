Auditor model: claude-opus-5-5
# T2349 audit (round 1) — Thu Oct  8 23:25:31 UTC 2026

Ticket UN-38, port of RBM2D `Universality/GUEPhase/DuhamelB.lean` (9e0f275) to `RBM3D/Universality/GUEPhase/DuhamelB.lean`.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2349-audit1`, detached at `t/T2349` = a9a3406.

## 1. Statements against the pin (source statements under the ticket's port map)
The pin is "the source's statements with the port map". Script `stmt.py` extracts every public
target (7 defs incl. their section `variable` lines, 8 theorems) from both files, applies the ticket's
token map mechanically to the source (`d : Sizes` -> `{d : ℕ} {sz : Sizes d}`, `d.L/W/size n` ->
`sz.L/W/size n`, `Idx (L)` -> `Idx d (L)`, `Z2` -> `Zd d`, `BlockIndex` -> `Vtx`,
`gloop L W (blockMat` -> `loopL d L W (blockMat d L W`, `(blockMat M)` -> `(blockMat d L W M)`,
`spectralZ/M` -> `zt/mE`, `RBM.Path.etaT` -> `RBM.Gauss.etaT`, `loopMax (` -> `loopMax d (`,
`genMatGUE (` -> `genMatGUE d (`, `X d` -> `X sz` for the Sizes-indexed objects), then compares strings.
```
$ python3 -I stmt.py RBM2D/.../DuhamelB.lean RBM3D-wt/T2349-audit1/.../DuhamelB.lean
SAME DuhamelPhi
  variables: SAME
SAME Duhamelv
  variables: SAME
SAME DuhamelVp
  variables: SAME
SAME DuhamelZinc
  variables: SAME
SAME DuhamelZst
  variables: SAME
SAME DuhamelYst
  variables: SAME
SAME Duhamelr
  variables: SAME
SAME Duhamel_azuma_Z
SAME Duhamel_azuma_Y
SAME Duhamel_bddC2C_Phi
SAME Duhamel_step_decomp
SAME Duhamel_exists_level
SAME Duhamel_Vp_le
SAME Duhamel_qv_le_crude
SAME Duhamel_grid_facts
```
All 15 targets: the source statement under the port map, character for character (hypotheses, quantifier
order, constants `32`, `4`, exponents `I.length + 2`, `2 * I.length + 4`, `m + 2`, ranges `j < K n`,
`j ≤ K n`, `k ≤ K n`). The `d`-lines named by the ticket: the Taylor constant
`m (m+1) · sz.size n · η^{-(m+2)}` in `Duhamel_bddC2C_Phi`, the `(sz.size n)⁻¹` factor in `Duhamel_Vp_le`/
`Duhamel_qv_le_crude`, and `Duhamelv = Δ / sz.size n`, with `sz.size n = (W L)^d` (`Defs/Sizes.lean`).
No target carries `3 ≤ d`; no `d = 2` closed form survives in a statement.

## 2. Vacuity, hidden hypotheses, cycles
- No structure/class is introduced; the only binders are explicit numeric/matrix hypotheses (§1). `Sizes`
  carries only `three_le_L`, `W_pos`. `HermTestFun` appears in a conclusion, not a hypothesis.
- No external hypothesis (no Prop pin is assumed), so no limit check is needed.
- Imports are the six merged modules named in the ticket; new file, so no cycle.
```
$ git -C RBM3D merge-base main t/T2349; git -C RBM3D rev-parse main
692a72bed634c4b9d95a5608ccd2ab6a49ef5f36
692a72bed634c4b9d95a5608ccd2ab6a49ef5f36
```

## 3. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.DuhamelBInst`)
Data: `SizesInst.sz0` (d = 3, L = 4, W = 32, size = 2097152, `sz0_values`), `e = 0`, GridCheck grid
`t0 = 9/10`, `t1 = (1 - ouZeta(1/20))·9/10`, `K ≡ 4`, loop `⟨[true,false],[0,1]⟩` (m = 2, `I.WF` by `rfl`).
The ticket asks for two instanced targets; all 8 theorems are instanced. Types as elaborated (remaining
binders only):
```
$ lake env lean Chk.lean    # #check @...DuhamelBInst.<name>; exit=0, no errors
grid_facts_check   : <closed proposition>             (x = 10, x⁻¹ = η_{t0} = 1/10)
bddC2C_Phi_check   : ∀ j < 4, ...
step_decomp_check  : ∀ j < 4, ...                     (ω = 0, hgood by DuhamelA2Inst.zero_mem_good)
Vp_le_check        : ∀ j < 4, ∀ (ω : PathΩ sz0), ...  (M = gueH .. j ω Hermitian, z = z_j, z' = z_{j+1})
qv_le_crude_check  : ∀ (ω : PathΩ sz0), ...           (m = 2)
exists_level_check : ∃ ℓ ≤ 6, 4 ≤ firstHit (fun _ _ => 1/4) (2^ℓ*(1/100)) 4 0 ∧ 2^ℓ*(1/100) ≤ 1/100 + 2*(1/2)
azuma_Z_check      : (Pgue sz0).real {...} ≤ ...      (lam = 1/100, k = 4, ε = 1)
azuma_Y_check      : (Pgue sz0).real {...} ≤ ...      (b = 3·10⁴·v·N⁵, hb proved, k = 4, ε = 1)
```
Every deterministic hypothesis is discharged at the concrete data; none is `N = 0`, an empty index, a
collapsed window (`Δ ≈ 0.011 > 0`, `K = 4`) or a `False` premise. `j < 4` is satisfiable.

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Universality.GUEPhase.DuhamelB > build.log 2>&1; echo exit=$? >> build.log; tail -2 build.log
Build completed successfully (3784 jobs).
exit=0
$ grep -c "DuhamelB.lean" build.log          # no warning/error line in the new file
0
$ lake env lean Ax.lean > ax.out; sed 's/.*depends on axioms: //' ax.out | sort | uniq -c   # 15 targets + 8 instances
  23 [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom |@\[implemented_by|unsafe" DuhamelB.lean | wc -l
       0
$ git diff --name-status main...t/T2349
A	RBM3D/Universality/GUEPhase/DuhamelB.lean
```
Only the sole writable file is touched; no frozen signature is modified (no existing file changes).

## 5. Paper deltas
The targets are Lean-internal lemmas of §7.2's Duhamel step (no paper statement is restated); the only
paper-level scale is `N = (WL)^d` = merged `Sizes.size`. The prove report proposes no candidate; I find no
Lean/paper statement difference introduced by this ticket.
```
$ grep -n "DuhamelB" docs/paper-deltas.md | wc -l
0
```

## 6. Observations (no verdict impact)
- O1. `azuma_Y_check` uses `b = 3·10⁴·v·N⁵ ≈ 6.4e27`, so its tail is ≈ 4 (numerically uninformative).
  The hypothesis `hb` is a genuine constraint, discharged by the merged frozen `Duhamel_norm_T_le`
  (`DuhamelA2.lean:594-601`, bound `C₂/2·v·N⁴`, from the truncation `DuhamelGood`: entries ≤ N); the size
  of `b` is the merged API at the ticket's GridCheck sizes, not an instance choice. The seven other
  instances (including `azuma_Z_check`, tail ≈ 0.0077) exceed the ticket's "two targets" requirement.
  Consumers (UN-39/40) should note that `Duhamel_norm_T_le`'s `N⁴` makes the Y tail usable only with
  `ε` of order `b√k`.
- O2. `ht1 : 0 ≤ t1 n` in `Duhamel_bddC2C_Phi`/`Duhamel_step_decomp` is unused (as in the source; kept by pin).

## Verdict
| target | statement | instance | build/axioms | verdict |
|---|---|---|---|---|
| DuhamelPhi, Duhamelv, DuhamelVp, DuhamelZinc, DuhamelZst, DuhamelYst, Duhamelr | SAME | used by all checks | ok | PASS |
| Duhamel_azuma_Z | SAME | azuma_Z_check | ok | PASS |
| Duhamel_azuma_Y | SAME | azuma_Y_check (O1) | ok | PASS |
| Duhamel_bddC2C_Phi | SAME | bddC2C_Phi_check | ok | PASS |
| Duhamel_step_decomp | SAME | step_decomp_check | ok | PASS |
| Duhamel_exists_level | SAME | exists_level_check | ok | PASS |
| Duhamel_Vp_le | SAME | Vp_le_check | ok | PASS |
| Duhamel_qv_le_crude | SAME | qv_le_crude_check | ok | PASS |
| Duhamel_grid_facts | SAME | grid_facts_check | ok | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
