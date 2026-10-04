Auditor model: claude-opus-5-5

# T2142 audit (LW-10a, `lem:localregular` first half) — Sun Oct  4 18:05:47 UTC 2026

Audit worktree `RBM3D-wt/T2142-audit1`, detached at `t/T2142` = `5f33854`. The ticket pins no Lean text (check file = `#check` of
merged names only), so statements are checked against the ticket's mathematics and `7_8:786-821`, `B:172-201`.

## Build, axioms, scope
```
$ lake build RBM3D.Graph.LocalRegular 2>&1 | grep -E "^error|LocalRegular|Build completed"; echo "exit=$?"
✔ [3383/3383] Built RBM3D.Graph.LocalRegular (5.4s)
Build completed successfully (3383 jobs).
exit=0
$ git diff --name-only main...t/T2142
RBM3D/Graph/LocalRegular.lean
$ git grep -nE "\b(sorry|admit|native_decide)\b|^axiom " t/T2142 -- RBM3D/Graph/LocalRegular.lean | wc -l
       0
$ lake env lean ax.lean     (#print axioms, 16 declarations; every line identical)
'RBM.Graph.fxyPowGraph_two' / fxyPowGraph_val_eq / fxyPowGraph_normal / fxyPowGraph_counters / fxyPowGraph_ord /
fxyPowGraph_pathInv / pathInv_locStep / PGraph.PathInv.exists_walks / LGraph.molNV_le_molNW_add_one /
lw_localregular_expansion / lw_fxyPow_integral_eq / localReg_inst_val2 / localReg_inst_val4 / localReg_inst_step1 /
localReg_inst_expansion / localReg_inst_noX_not  depends on axioms: [propext, Classical.choice, Quot.sound]
$ for n in fxyPowGraph molNV molNW PathInv LocReg1 LocReg2 LocReg35 pathInv_locStep lw_localregular_expansion lw_fxyPow_integral_eq localReg_; do git grep -lw "$n" main -- RBM3D | wc -l; done
0 0 0 0 0 0 0 0 0 0 0      (no clash on main)
```
No merged file is touched, so no frozen signature changes. `RBM3D/Test/Axioms.lean` is unchanged (no registry line, as the ticket expects).
Imports: `Graph/{LWLvl1,LWSymm,LWVocab,LWStein,LWWeightExp,LWEdgeExp,LWGGExp,ScalingOrder}` (all merged) and
`Mathlib.Combinatorics.SimpleGraph.Acyclic`; not `RBM3D`. No external hypothesis, no structure with Prop fields (`PGraph` fields are data
plus `ext_surj`, merged).

## Supporting definitions read (`#print`, audit worktree)
```
LGraph.nM Γ = (Finset.image Γ.mol {v | ∀ w ∈ Γ.mol v, w.isRight = true}).card      -- number of internal molecules
LGraph.IsExtMol Γ c = ∃ a, Γ.molOf (Sum.inl a) = c
@pathInv_locStep : LocStep m P outs → ∀ {k}, PGraph.PathInv k P → ∀ B ∈ outs, PGraph.PathInv k B
@lvl1_lemma_induction ... (∀ Pred, Pred Γ → (∀ A L, LocStep m A L → Pred A → ∀ B ∈ L, Pred B) → ∀ Q ∈ outs ++ errs, Pred Q) ...
LocStep constructors: weight | edge | gg   (pathInv_locStep does `cases hst` on all three; Lean checks exhaustiveness)
```

## Target 1 — `fxyPowGraph` (`(eq:originGamma)`, `B:174-176`, `(eq:initial_scaling)`)
Lean (file l.1348-1359): block `i` = `[Ǧ_{β_iβ_i}` circled loop, `G_{xα_i}`, `G_{α_i y}]`, colour `decide (i < p/2)` (paper: `G^{(i)} = G`
for `1 ≤ i ≤ p/2`, 0-indexed `i < p/2`), waved `S_{α_iβ_i}`, `×`-dotted `(α_i,x)`, `(α_i,y)`, coeff 1. `fxyPowGraph_two : fxyPowGraph 2 =
p2Graph` by `rfl` (exact, same vertex order), so the edge conventions are those of the merged `p2Graph`.
- `fxyPowGraph_val_eq (D) (hS : S real) (p) (hp : Even p) (x y) : val D ![x,y] = fxyVal^(p/2) * star fxyVal^(p/2)` — matches `|f_xy|^p`.
- `fxyPowGraph_normal`, `fxyPowGraph_counters` (`n_S=3p, n_W=p, n_V=2p, n_M=p`), `fxyPowGraph_ord : ord = p` — match `B:201`.
Verdict: PASS.

## Target 2 — predicates (1)–(6) (`7_8:794-818`)
| paper | Lean (l.1925-1959) | check |
|---|---|---|
| (1) locally standard, ext. `x,y` | `LocReg1 Q := Q.LocStd`; `x = inl (Q.ext 0)`, `y = inl (Q.ext 1)` | equal |
| (2) `q ≤ p` internal molecules; `n_V(M) ≤ n_W(M)+1` for every molecule | `Q.g.nM ≤ p ∧ ∀ c, molNV c ≤ molNW c + 1`; `nM` = #internal molecules (above); `molNV` counts all vertices of `c` | equal / `n_V` incl. external vertices (stronger: delta `T2142c`) |
| (3) `p` edge-disjoint paths `M_x → M_y` via solid edges in the molecular graph | `LocReg3 Q p W`: each `W i` a step list from `M_x` to `M_y`; `∑ stepEdges (W i) ≤ molEdgeMS` (= `molSolid`, solid edges between distinct molecules, `localReg_offDiag_edgeMS`) | walks, not simple paths; `(eq:far_ab)` not assumed (closed walks if `M_x = M_y`) — delta `T2142a`; ticket allows "or prove they hold without it; say which" (said) |
| (4) every internal molecule on two different paths | `LocReg4`: `∀ c, ¬IsExtMol c → ∃ i ≠ j, Visits (W i) c ∧ Visits (W j) c` | equal (proof in LW-10b) |
| (5) `∀ A ⊂ [q]`, `#{j : V(P_j) ∩ A ≠ ∅} ≥ |A|` | `LocReg5`: `∀ A : Finset Mol, (∀ c ∈ A, ¬IsExtMol c) → A.card ≤ #{i | ∃ c ∈ A, Visits (W i) c}` | equal |
| (6) `ord ≥ 2p` | `LocReg6 Q p := 2p ≤ Q.g.scalingOrder` | equal (proof in LW-10b) |
| common family | `LocReg35 := ∃ W, LocReg3 ∧ LocReg5`; `LocReg345 := ∃ W, LocReg3 ∧ LocReg4 ∧ LocReg5` | as the ticket asks |
`Visits u l c := c = u ∨ ∃ st ∈ l, st.2 = c` (start plus step ends): the molecule set `V(P_j)`. Non-vacuity of (3)/(5): with
`M_x = M_y` empty walks satisfy (3) but (5) still requires every internal molecule to be visited; with `M_x ≠ M_y` each walk needs an
edge out of `M_x` (negative control `localReg_inst_noX_not` compiles: no family when `x` has no solid edge leaving its molecule).
Verdict: PASS.

## Target 4 — path invariant (`B:178-196`)
`PGraph.PathInv p Q := localReg_Fam p (molOf x) (molOf y) (¬IsExtMol ·) Q.g.localReg_edgeMS`: `p` walks, non-loop steps within the
multiset of molecular edges, loop steps free, Hall condition. `PathInv.exists_walks : Q.PathInv p → Q.LocReg35 p` (strips loop steps)
links it to the strict (3)∧(5). `fxyPowGraph_pathInv : ∀ p, (fxyPowGraph p).pack.PathInv p` (walks `x → α_i → y`).
`pathInv_locStep` has exactly the shape of `lvl1_lemma_induction`'s step hypothesis (signatures above) and is proved for all three
`LocStep` constructors via 17 per-term lemmas plus `localReg_pathFam_partition` (the dotted partition). No counterexample reported.
Verdict: PASS.

## Target 3 — `lw_localregular_expansion` (`(eq:local_Gs)`, items (1),(2),(3),(5))
Statement = the merged `lvl1_lemma_size` at `Γ = (fxyPowGraph p).pack` (its four conjuncts verbatim: same parameter order `p m c hc K0 d D`,
then `∃ outs errs`; size bound `≤ W^{-D}` under `1 ≤ W, 1 ≤ L, L^d ≤ W^K0, W^{-d/2} ≤ Ψ ≤ W^{-c}`; the expectation identity with all
of `lvl1_lemma_size`'s hypotheses) plus `∀ Q ∈ outs, LocReg1 ∧ LocReg2 p ∧ LocReg35 p` and `∀ Q ∈ outs ++ errs, PathInv p`, as item 3
asks. `lw_fxyPow_integral_eq` (p even) rewrites the left side as `E[f^{p/2} conj(f)^{p/2}] = E|f_xy|^p`. Valid for all `p`; evenness
only in the two value lemmas (delta `T2142d`). (4), (6) and the assembly are LW-10b by the ticket's split (DECISIONS §42).
Verdict: PASS.

## Compiled nonempty instances (same file, section 10; all built above)
```
2071: theorem localReg_inst_val2 : (fxyPowGraph 2).val lwD ![0, 1] = 67081        -- via fxyPowGraph_val_eq, hS discharged (259^2)
2076: theorem localReg_inst_val4 : (fxyPowGraph 4).val lwD ![0, 1] = 4499860561   -- 259^4
2081/2088: counters at p = 2, 4      2084/2091: ord = 2, 4      2086/2093: Normal at p = 2, 4      2095: fxyPowGraph 2 = p2Graph
2098/2100: (fxyPowGraph 2).pack.PathInv 2, (fxyPowGraph 4).pack.PathInv 4
2103: molNV ≤ molNW + 1 at (fxyPowGraph 4), molecule {α_0, β_0}, normality discharged
2108: localReg_inst_step1 := pathInv_locStep lvl1_inst_locStep_weight (fxyPowGraph_pathInv 2)   -- a concrete weight LocStep at p2Graph
2113: (fxyPowGraph 2).pack.LocReg2 2      2117: ...LocReg35 2 := (fxyPowGraph_pathInv 2).exists_walks
2119: ¬ (fxyPowGraph 2).pack.LocReg6 2   2125: lvl1ExStd.pack.LocReg1   2127: figGraph.pack.LocReg6 2
2192: localReg_inst_noX_not : ¬ localReg_inst_noX.pack.PathInv 1                -- negative control
2222: localReg_inst_expansion := lw_localregular_expansion 2 (mE 0) (1/4) _ 1 3 10, size part at W = 27, L = 3, Ψ = 27^(-1/4)
      (27 ≤ 27^1, 27^(-3/2) ≤ Ψ ≤ 27^(-1/4) discharged); identity at lwWxInstSz (d = 3) with gaussIBP, Im z > 0, u = 1/2,
      mE 0 ≠ 0, flow identity, Sp eq., Spᵀ = Sp, M diag/off-diag all discharged by merged lemmas
2246: example := lw_fxyPow_integral_eq lwWxInstSz 0 (zt 0 (1/2)) (1/2) lwWxInstM lwWxInstSp 2 (by decide) lwSymmInstL
```
Every endpoint theorem (targets 1–4, `exists_walks`, `molNV_le_molNW_add_one`, `lw_fxyPow_integral_eq`) is applied at concrete data
`d = 3`, `p ∈ {2,4}`, with every hypothesis discharged; no `N = 0`, empty index, collapsed window, or `False` premise.

## Paper-delta coverage
Differences found: walks instead of paths and `(eq:far_ab)` dropped → `T2142a`; (5) carried by a Hall invariant instead of the labelled
path–molecule correspondence (proof route) → `T2142b`; `(eq:MolVW)` for all vertices incl. external → `T2142c`; all `p`, evenness only
in the value lemmas → `T2142d`. All proposed in the prove report (d). No uncovered difference found.

## Observations (no effect on verdict)
1. `localReg_inst_step1` does not compile a proof that the output list of that `LocStep` is nonempty (the partition uses a classical
   filter); its premises are a concrete merged `LocStep` and a proved `PathInv`, so it is not degenerate in the §4 sense.
2. Helpers are public with the `localReg_` prefix rather than `private` (prove report (d) item 4); CLAUDE.md §3 (E) allows either.
3. Public non-target names `LGraph.molNV`, `LGraph.molNW` are unprefixed; they are the `n_V(M)`, `n_W(M)` of predicate (2) and clash
   with nothing on `main`.

## Verdict
Target 1 PASS; Target 2 PASS; Target 3 PASS; Target 4 PASS. Ticket T2142: **PASS**. No dispatcher sign-off needed.
