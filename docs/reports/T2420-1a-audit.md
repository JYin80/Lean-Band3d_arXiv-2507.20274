Auditor model: claude-opus-5-5

# T2420 1a-audit (design gate) — BA-L L3c1 `BAAtom`, G3 / G4

Written Sun Oct 11 12:34 UTC 2026 (`date -u`). Inputs: ticket `docs/tickets/T2420.md`; section (a) and (a″) of
`docs/reports/T2420-prove.md`; branch `t/T2420` at `f18b4fa`; audit worktree `../RBM3D-wt/T2420-1a-audit` (detached,
build cache cloned). Scratch: scratchpad `T2420/audit/`.

## Verdict: **PASS** (every stage-1a deliverable met; no binding stop line hit; no sign-off request)

| 1a deliverable (ticket "Design gate") | where in (a) | result |
|---|---|---|
| G3 written argument, constants tracked, exponent `ord G − ord G^aux ≥ 0` | E1, E3–E7, A1–A5 | met (checked below) |
| where atoms enter; band steps of `lwGtoAG_holds` reused unchanged | E4, E8, A1, A3; "Reused unchanged" | met; reused names exist and are public |
| G4 pin for L3d1 (statement only, in the probe) | E9, `BAAnpAux`, `baAuxNested_pin` | met (probe 169-191) |
| `scaleatom`, `Gyiyjatom`, `Gyiyjatom2` as statements | E8, `baAtom_*` | met (probe 83-111) |
| C1/L5: constants at `g = 1/64, 1, 10`, `κ = Im m`; no small `g`, no `‖M−m₀I‖` small, no `M = mI` | E3, E6, E7; script | met (rerun below; `BAGtoAG` has no such hypothesis) |
| probe ≤ 400 lines compiles G3, G4 pin, vocabulary | (a″) | met: 395 lines, exit 0 |
| stop lines: "G3 does not close → stop"; probe ≤ 400; 2,000/file (1b) | — | not hit (G3 closes; 395 ≤ 400; 1b not started) |

## 1. Probe recompiled in the audit worktree

```
$ git -C ../RBM3D-wt/T2420-1a-audit log -1 --format=%h        -> f18b4fa
$ git diff --stat main...t/T2420
 RBM3D/Probe/T2420Pins.lean | 395 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 395 insertions(+)
$ lake env lean RBM3D/Probe/T2420Pins.lean; echo exit=$?
Sun Oct 11 12:29:53 UTC 2026
@BAGraph.shadow : {E I : Type} → BAGraph E I → LGraph E I
@BAGraph.auxVal : ... → BAGraph E I → (κ → κ → ℝ) → (E → κ) → ℝ
@BAGraph.auxOrd : ... → BAGraph E I → ℤ
BAShadowPG : BAPGraph (Fin 2) → PGraph (Fin 2)
RBM.Graph.BAGraph_shadow_mol_pin : Prop   ... (12 Prop pins) ...   RBM.Graph.BAAnpAux (d : ℕ) : Prop
lake env lean RBM3D/Probe/T2420Pins.lean  8.35s user 2.25s system 125% cpu 8.456 total
exit=0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Probe/T2420Pins.lean | wc -l      -> 0
$ sed "s/2000/1/g" T2420Pins.lean > probe_mut.lean; lake env lean probe_mut.lean   # window A=1: 1/8 ≤ 1·(1/100)² false
exit=1
probe_mut.lean:301:63: error: unsolved goals      (⊢ False, the window argument of the G3 instance)
probe_mut.lean:346:46: error: unsolved goals      (⊢ False, the window argument of the model-form instance)
$ lake env lean docs/tickets/checks/T2420-check.lean (copy, audit worktree); echo exit=$?   -> exit=0, no error/warning line
```

## 2. Numerics rerun (copies of the prover's scripts in `T2420/audit/`)

```
$ python3 counters.py | tail -2; python3 consts.py; python3 g3inst.py; python3 g3inst.py coh
forest: waved gate edges nA-nM = 2 ; dotted tree nV-nA = 2 ; non-tree waved nW-(nA-nM) = 1 ; #mdot+#psi = 2
counters_le: nM<=nA: True ; nA-nM<=nW: True ; |molSolid|<=nS: True
g  kappa  c_M=BAct_rate  mu=BAp5s_rate  c=min(c_M,mu)  A=g^2+1  log10(logW0), D=3, eps1=1/20
0.015625  0.9993  0.5  1.93e-09  1.93e-09  1.00024  190
1  0.5959  0.0485  2.17e-22  2.17e-22  2  449
10  0.5594  0.00465  8.66e-32  8.66e-32  101  637
(random phases)  g=0.015625: confined/main=4.57e-07 nonconf/tail=7.84e-12 | g=1: 4.07e-06, 5.85e-07 | g=10: 7.85e-10, 1.02e-08
   (each g) total |val| <= main+tail: True; confined<=main: True; nonconf<=tail: True
(coherent G-M=Psi) g=0.015625: confined/main=4.02e-04 nonconf/tail=1.10e-08 | g=1: 3.49e-03, 3.58e-04 | g=10: 6.93e-07, 6.16e-06
   (each g) total |val| <= main+tail: True; confined<=main: True; nonconf<=tail: True
```
Matches (a)(ii) line for line (the counters header lines, `ord G = 4`, `auxOrd = 1`, exponent 3, also reproduce).

## 3. The G3 argument against the merged signatures

```
$ grep -n "theorem BAGraph.exists_forest" -A4 RBM3D/Graph/BASizeClaim.lean
727: ∃ (C : Finset I) (par) (edge : I → Option Γ.Jx) (ρ), C.card + Γ.nM = Fintype.card I ∧
      (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card + Γ.nM = Γ.nA ∧ (rank decreases along par) ∧ ...
$ sed -n 65,67p RBM3D/Graph/BASizeClaim2.lean
def BAGraph.sizeConst ... := ‖Γ.coeff‖ * K₁ ^ (Γ.nA - Γ.nM) * K₀ ^ (Γ.nW - (Γ.nA - Γ.nM)) * Kd ^ (Γ.mdot.length + Γ.psi.length)
$ grep -n "def LGraph.adj" -A2 RBM3D/Graph/LWVocab.lean; grep -n "def BAGraph.adj" -A2 RBM3D/Graph/BAVocab.lean
157: Γ.waved.any (...) || Γ.dotted.any (fun e => e.eq && ...)
116: Γ.toLGraph.adj u v || Γ.atomAdj u v          -- atomAdj: =-dotted, Ψ-dotted, M-dotted
$ for n in auxGraph_bdist_triangle auxGraph_bdist_self auxGraph_sum_blocks auxGraph_one_le_prod auxGraph_prod_exp_ge; do grep -n "theorem $n" AuxGraph.lean; done
145: theorem auxGraph_bdist_triangle | 151: auxGraph_bdist_self | 663: auxGraph_sum_blocks | 709: auxGraph_one_le_prod | 718: auxGraph_prod_exp_ge
$ grep -c "^private" RBM3D/Graph/AuxGraph.lean -> 4 (none of the reused names)
```
Auditor checks (each against the lines above):
- **Shadow molecules (A1).** `shadow.waved = waved ++ mdot ++ psi`, `shadow.dotted = dotted`: `LGraph.adj` of the shadow is
  `BAGraph.adj` edge for edge, so `shadow.mol = Γ.mol`, `shadow.nM = Γ.nM` (pins 64-70) are true by definition-chasing.
- **Exponent (E1).** `ord Γ = n_S + 2(n_W − n_A)` (`BAVocab.lean:146`, slot `nV = n_A`), `auxOrd = |𝒢_ℳ| − 2n_M`
  (`AuxGraph.lean:86`): difference `(n_S − |𝒢_ℳ|) + 2(n_W − n_A + n_M)`; `≥ 0` by `counters_le` (`n_A − n_M ≤ n_W`) and
  `molSolid_length_le` (`:124`). Per molecule: `n_W − n_A + n_M = Σ_i e_i + Σ_ext (k_i^{ext} − 1)` (independently re-derived), i.e. T2387
  row 15 at `r^{ext} = 1`, as E2 says.
- **Roots (A3).** From `exists_forest`: `|I∖C| = n_M`; following `par` from `c ∈ C` stays in the molecule (J-edges) with strictly
  decreasing rank, so every internal molecule holds a vertex of `I∖C`; by counting, exactly one each and none in an external
  molecule. Tree waved edges `= n_A − n_M` (second conjunct), non-tree waved `= n_W − n_A + n_M`, each `≤ K₀W^{-d} ≤ K₀AΨ²`:
  the constant is `sizeConst (K₀A) K₁ Kd` and the `Ψ`-power is the exponent above. Roots summed as `(W^d)^{n_M}·Σ_blocks`
  (`auxGraph_sum_blocks`) = `(W^d)^{n_M} auxVal`. Closes.
- **Tail (A4).** `G' := G − M + M'` keeps the circled solid factors `G' − M' = G − M` (`SEdge.val`, `LWVocab.lean:115-117`);
  weighted `M'`, `gΨ'` stay offset-diagonal, entries `≤ C`, row sums `≤ C·expC(d−2,c/2)`: the `Kd`-slot `C(1+expC)` covers both.
  The peeling must be applied to absolute values (`Σ|term|`), as in the band's `auxGraph_tail_sum`; (a) says "peeling", not
  `baClaimSize` itself — consistent.
- **No forbidden hypothesis.** `BAGtoAG` (probe 120-140): no `M = mI`, no smallness of `g`, no `‖M − m₀I‖` bound; window
  `W^{-d} ≤ AΨ²` with free `A ≥ 0` (at BA `A = g²+1`: `STBctl_ge`, `Induction/ScaleFacts.lean:126`,
  `W^{-d}(λ²+1)^{-1} ≤ Bctl`).

## 4. G4 pin and the nested form

`baAuxNested_pin` (probe 169-174) is `LWAuxNested` (`AuxGraph.lean:1597`) at `BAShadowPG P` with `P.g.mol` in place of
`molOf` (bridged by `shadow_mol`); `lwAuxNested_holds` (`:1606`) is merged, so the reduction is direct. `BAAnpAux`
(probe 179-191) is `LWAnp` (`LWPins.lean:409`) for `P.g.auxVal` with `0 < p`, `n_M ≤ p`; `lwAnp_holds`
(`AnpKey6.lean:952`) is merged. Inputs from this row: `shadow`, `auxVal`, `auxOrd`, `baAuxNested`. The BA-flow-carrier form is
deferred to L3c3's 1a (stated in (a), E9 and A5).

## 5. Instances in the probe (for the 1a; 1b must redo them in `BAAtom*.lean`)

Seven `example`s, `d = 3, L = 4, W = 2`: G3 at `G*` (normal, `n_M = 1`, exponent 3) with merged `D0`, `Ψ = 1/100`, `A = 2000`,
`r = 1`, `R = 7`, `ξ ≡ 1/100`, kernel constants from `baKBound_E`/`baSpDecay`/`BAMB_decay_large`, all deterministic
hypotheses discharged; the negative control shows the window argument is live. G4 at `baPQ` (`p = 2`, `n_M = 1`) with `LWXi`
left as a hypothesis (another gate's pin, allowed).

## 6. Sibling scan

```
$ git merge-base --is-ancestor 1dc7516 t/T2420 || echo "T2417 NOT in t/T2420 base"   -> T2417 NOT in t/T2420 base
$ for n in BAGraph.shadow auxVal auxOrd BAShadowPG BAGtoAG BAAnpAux baAuxNested baAtom_ baGtoAG BAAtom_; do git grep -n "$n" main -- 'RBM3D/Graph/BA*.lean' | wc -l; done
0 0 0 0 0 0 0 0 0 0      (main includes T2417's BAAtomic, BAAtomic2)
```

## 7. Paper deltas

Proposed in (a) Verdicts: `T2420a` (aux graph at molecule centres, retained atoms of `B:445-449` folded into the centre via the
`R`-ball domination), `T2420b` (window `W^{-d} ≤ AΨ²`, `A = g²+1`), `T2420c` (exponent identity E1). These cover every
statement difference between `BAGtoAG`/`BAAnpAux` and `B:420-497` found in this audit.

## Observations (no verdict change)

1. **O1 (consumer obligation from T2420a).** The paper bounds inter-atom solid edges by the vertex-level `ζ(x_{i,j},x_{i',j'})`
   (`B:424-431`); the centre-level design instead needs one block-level `ξ` that dominates `‖G − M‖` at **all offsets and on
   the diagonal** over `R`-balls (G3's `hξ`) and satisfies `LWXi` (G4). The paper supports this through `GijGEX_BA`
   (`7_8_light_weight.tex:1942-1944`, max over `x ∈ [a], y ∈ [b]`), but (a) does not check it; L3c3's 1a, which fixes the
   carrier form, should state the joint limit check.
2. E3 cites `STBctl_ge` at `LWExpTerm6.lean:34` (a docstring use); the declaration is `Induction/ScaleFacts.lean:126`.
3. `t/T2420` branches from `6c42b16`, before T2417's merge `1dc7516`; no name clash with main (§6). 1b builds against the branch.
4. The probe's G4 instance `baPQ` has no `M`- or `Ψ`-dotted edge (its shadow is the band graph). 1b's instances of
   `baAuxNested`/G3 should use a graph with `M`/`Ψ`-dotted edges (as `G*`).
5. (a″)(iv): the Lean G3 instance uses `Ψ = 1/100, A = 2000` instead of (a)(ii)'s `Ψ = 1/2`; both satisfy the window.
