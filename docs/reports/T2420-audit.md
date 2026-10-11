Auditor model: claude-opus-5-5

# T2420 audit (round 1) — BA-L L3c1 `Graph/BAAtom`, `Graph/BAAtom2`: atoms, the auxiliary graph, G3 `(G_by_auxG_BA)`, G4 pin

Sun Oct 11 13:45 UTC 2026 (`date -u`); `t/T2420` at `32a1b69`; worktree `../RBM3D-wt/T2420-audit1`; pins: probe `RBM3D/Probe/T2420Pins.lean` (1a-audit PASS).

## Verdict: **PASS** (all targets). No dispatcher sign-off requested.

| target | Lean | statement vs pin | instance | axioms |
|---|---|---|---|---|
| 1 vocabulary, order comparison | `BAGraph.shadow/auxVal/auxOrd`, `BAShadowPG`, `shadow_mol`, `shadow_nM`, `scalingOrder_sub_auxOrd`, `auxOrd_le_scalingOrder` | identical / `@thm : pin` | BAAtom.lean:984 at `G*` | std 3 |
| 2 pointwise, `scaleatom`, `Gyiyjatom(2)` | `baAtom_offset/dist/sedge_xi/wedge`, `BAAtom_term_conf` | `@thm : pin` (4 pins) | :1025, 1031, 1038, 1051, 1080 | std 3 |
| 3 tail, **G3** | `BAGtoAG`, `baGtoAG_holds`, `baGtoAG_E` | def text identical; `rfl`; `@thm : pin` | BAAtom2.lean:725, 756 | std 3 |
| 4 nested form, **G4 pin** | `baAuxNested_holds`, `BAAnpAux` (owner L3d1), `baAnpAux_holds` | `@thm : pin`; def identical; `rfl` | :775, 784 | std 3 |
| 5, 6 | instances at `MFixedPointInst.P : FlowPt 4 10`, `d=3,L=4,W=2,t=1/2` (11 `example`s); registry: none (G4 proved) | — | — | — |

## 1. Build, hygiene, axioms (audit worktree)

```
$ lake build RBM3D.Graph.BAAtom RBM3D.Graph.BAAtom2 > build2.txt 2>&1; echo exit=$?; grep -E "error|BAAtom|Build completed" build2.txt
exit=0
Build completed successfully (3825 jobs).
$ grep -nE "sorry|admit|native_decide|^\s*axiom|set_option.*(maxHeartbeats 0|debug)" RBM3D/Graph/BAAtom.lean RBM3D/Graph/BAAtom2.lean; echo "grep exit=$?"
grep exit=1
$ lake env lean ax.lean     (import RBM3D.Graph.BAAtom2; #print axioms of 15 public theorems)
'RBM.Graph.BAGraph.shadow_mol' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.shadow_nM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.scalingOrder_sub_auxOrd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.auxOrd_le_scalingOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAtom_offset' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAtom_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAtom_sedge_xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAtom_wedge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baGtoAG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baGtoAG_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAuxNested_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAnpAux_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAAtom_term_conf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAAtom_tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAAtom_decay_E' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean T2420-check.lean (copy); lake env lean RBM3D/Probe/T2420Pins.lean   ->   check exit=0 errors=0 | probe exit=0 errors=0
$ git diff --name-status main...t/T2420 | paste -sd' ' -      (Probe: sole writable, 1a only, not merged)
A	RBM3D/Graph/BAAtom.lean A	RBM3D/Graph/BAAtom2.lean A	RBM3D/Probe/T2420Pins.lean
$ wc -l RBM3D/Graph/BAAtom.lean RBM3D/Graph/BAAtom2.lean | head -2 | paste -sd' ' -     (stop line 2,000 per file)
    1098 RBM3D/Graph/BAAtom.lean      797 RBM3D/Graph/BAAtom2.lean
```
No existing file is modified (all `A`), so no frozen signature is touched. `RBM3D.lean` is not edited (hub adds the imports).

## 2. Statements against the pins (script)

`conf.py` compares the probe's definitions with the files (whitespace-normalised text) and writes `conf.lean`
(`import RBM3D.Graph.BAAtom2`): each probe `X_pin` copied verbatim as `AUD_X_pin` with `example : AUD_X_pin := @X`; for
`BAGtoAG`, `BAAnpAux` the probe text as `AUD_*` with `AUD_* d = * d := rfl` and `AUD_* d := *_holds d`.
```
$ python3 -I conf.py $PWD conf.lean && lake env lean conf.lean > conf.out 2>&1; echo "lean exit=$? bytes=$(wc -c < conf.out)"
def BAGraph.shadow       identical: True
def BAGraph.auxVal       identical: True
def BAGraph.auxOrd       identical: True
def BAShadowPG           identical: True
def BAGtoAG              identical: True
def BAAnpAux             identical: True
examples: 14
lean exit=0 bytes=       0
$ negative control: `example : AUD_baAtom_dist_pin := @baAtom_offset`
conf_neg.lean:45:33: error: Type mismatch
```
Pins covered: 8 vocabulary/atom pins, `baGtoAG_E_pin`, `baAuxNested_pin`, `BAGtoAG`, `BAAnpAux`: all hold with the pinned text.

**Against the ticket's mathematics (`B:405-497`, `7_8:870-960`).**
- G3 `BAGtoAG` (BAAtom2.lean:392): twin of `LWGtoAG` (`AuxGraph.lean:979`) with `hM : M = m I` removed; `‖G−M‖ ≤ Ψ` on all
  entries; window `W^{-d} ≤ AΨ²`, `A ≥ 0` free (band: `W^{-d/2} ≤ Ψ`, i.e. `A = 1`); `LWKBound`s of `S, S⁺` (`K₀W^{-d}, K₁`)
  and `M, gΨ` (`Kd`); one decay `(C, c)` for all four kernels, `M`, `gΨ` offset-diagonal; `ξ ≥ 0` dominating `‖G−M‖` on
  `R`-balls, `R ≥ |E⊕I| r`. Conclusion: `C_Γ(K₀A,K₁,Kd) Ψ^{ord Γ − ord Γ^aux} (W^d)^{n_M} Γ^aux + e^{-cr/2} C'_Γ size(Γ)`:
  the deterministic form of `(G_by_auxG_BA)` (the `W^{-D}` is the tail at `r = (log W)^{1+ε₁}`, as for the band).
  No smallness of `g`, no `‖M − m₀I‖` small, no `M = mI` (C1/L5). Exponent `ord Γ − ord Γ^aux = (n_S − |𝒢_ℳ|) + 2(n_W − n_A + n_M)`
  (`scalingOrder_sub_auxOrd`), `≥ 0` for normal `Γ` (`auxOrd_le_scalingOrder`): the ticket's identity (row 15) at `r^{ext}=1`.
- `baGtoAG_E` (:606): `∃ K₀ K₁ Kd C c` before `∀ L W g₀ E t m` (fixed parameters first); constants of `(d, Λ, κ)` only;
  hypotheses `3 ≤ L`, `0 < g₀ ≤ Λ`, `BAReal`, `0 ≤ t < 1`; every kernel hypothesis of `BAGtoAG` is discharged from the merged
  `baKBound_E` and the proved `BAAtom_decay_E`. Not a special case: `G` is any matrix with `‖G − M‖ ≤ Ψ`.
- G4 `BAAnpAux` (:677, docstring "Owner: L3d1 (stage L)"): `LWAnp`'s conclusion for `P.g.auxVal`, hypotheses `0 < p`,
  `n_M ≤ p`, `LocReg345` of the shadow, `𝓜_x ≠ 𝓜_y`, `STFlow`, `LWPsiAll`, `LWXi`. Proved (`baAnpAux_holds`) beyond the
  ticket from the merged `lwAnp_holds` (`AnpKey6.lean:952`, `∀ d, LWAnp d`, no extra hypothesis) and `baAuxNested_holds`.

## 3. Hidden hypotheses, vacuity, cycles

```
$ grep -rn "structure BALData" -A2 RBM3D/Graph/BAVocab.lean; grep -n "def LWKBound" -A1 RBM3D/Graph/LWSizeClaim.lean
39:structure BALData (ι : Type*) extends RBM.Graph.LData ι where
40-  gPsi : Matrix ι ι ℂ
388:def LWKBound {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) (a K₁ : ℝ) : Prop :=
389-  (∀ x y, ‖K x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖K x y‖ ≤ K₁) ∧ (∀ y, ∑ x, ‖K x y‖ ≤ K₁)
$ for f in Graph/AnpKey6 Graph/AuxGraph Graph/LWPins Graph/BASizeClaim2 BA/GreenSchur; do git cat-file -e main:RBM3D/$f.lean && echo "on main: $f"; done | paste -sd' ' -
on main: Graph/AnpKey6 on main: Graph/AuxGraph on main: Graph/LWPins on main: Graph/BASizeClaim2 on main: BA/GreenSchur
$ grep -n "theorem lwAnp_holds\|theorem lwAuxNested_holds" RBM3D/Graph/AnpKey6.lean RBM3D/Graph/AuxGraph.lean
AnpKey6.lean:952:theorem lwAnp_holds : ∀ d : ℕ, LWAnp d := fun d => lwAnp_of_key d (lwAnpKey_holds d)
AuxGraph.lean:1606:theorem lwAuxNested_holds : LWAuxNested := by
```
No `Prop` field in `BALData`, `BAPGraph` (only `ext_surj`); imports are merged modules only (`AuxGraph`, `BASizeClaim2`,
`GreenSchur`, `LWPins`, `AnpKey6`); no cycle. No external hypothesis is added (G3, G4 are theorems; `LWXi` is an existing pin).

## 4. Compiled nonempty instances (in the files; they compile in the module build above)

- G3 `baGtoAG_holds` (BAAtom2.lean:725): `d=3, L=4, W=2`, `G*` (2 external, 5 internal; `n_S,n_W,n_A,n_M = 4,3,3,1`; one `M̄`-
  and one `Ψ`-dotted edge; exponent 3), BA model data `D0` at `P` (`M = BAlwM`, `S`, `S⁺ = S W`, `g₀Ψ`; `G = M + 1/100`),
  `Ψ = 1/100`, `A = 2000` (`1/8 ≤ 2000·10⁻⁴`), `r = 1`, `R = 7`, `ξ ≡ 1/100`; constants from `baKBound_E`, `BAAtom_decay_E`;
  the conclusion also proves `auxVal = 64·(1/100)³ > 0`. Every hypothesis discharged.
- `baGtoAG_E` (:756): same data, `D0` fields by `rfl`. Nested form (:775) at `baPQ` (`p = 2`, `n_M = 1`, `LocReg345` from
  `localReg2_inst_Q_locReg345`). G4 (:784) at `baPQ` with the band flow data of `inst_Anp`; only `LWXi` (pin of stage G / L3c3)
  stays a hypothesis (allowed).
- Atom statements: `baAtom_offset` at toy `D1` with `term ≠ 0` and four distinct offsets (:1025) and at `D0` (:1031);
  `baAtom_dist` (:1038), `baAtom_sedge_xi`/`baAtom_wedge` at `D0` (:1051); `BAAtom_term_conf` at a confined labelling (:1080).
```
$ sed 's/2000/1/g' RBM3D/Graph/BAAtom2.lean > BAAtom2_mut.lean; lake env lean BAAtom2_mut.lean; echo exit=$?   (window A = 1: 1/8 ≤ 10⁻⁴ false)
exit=1
BAAtom2_mut.lean:744:51: error: unsolved goals          (window argument of the G3 instance)
BAAtom2_mut.lean:765:25: error: unsolved goals          (window argument of the baGtoAG_E instance)
```
No `N = 0`, empty index, collapsed window or `False` premise; `A = 2000` is moderate and the window is live (above).

## 5. Name clashes

```
$ (57 public names of the two files; git grep "(theorem|def|abbrev|lemma|structure) [..]<name>( |$)" main -- RBM3D ':!RBM3D/Probe')
public names: 57
total hits on main: 0
```

## 6. Paper deltas

Proposed in the prove report (d): `T2420a` (aux graph at molecule centres, retained atoms `x_{i,j}` of `B:445-449` folded in
by `R`-ball domination), `T2420b` (window `W^{-d} ≤ AΨ²`), `T2420c` (exponent identity), `T2420d` (`scaleatom`, `Gyiyjatom`,
`Gyiyjatom2` deterministic; `e^{-c(log W)^{1+ε₁}}` is G3's tail), `T2420e` (`hext` unused), `T2420f` (G4 corollary of `lwAnp_holds`). They cover every difference above; wording: O2.

## Observations (no verdict change)

1. **O1 (scope for the dispatcher).** `BAAnpAux` (owner L3d1) is proved here in the band-flow form (`baAnpAux_holds`). The
   substance of `B:491-497` moves to whether a block-level BA `ξ` dominating `‖G − M‖` on all offsets and the diagonal over
   `R`-balls (G3's `hξ`) also satisfies `LWXi` (1a-audit O1); that joint check belongs to L3c3's 1a. L3d1's scope should be
   re-read against `T2420f`.
2. **O2 (delta wording).** `T2420a` should state explicitly: (i) centre-level `ord Γ^aux = |𝒢_ℳ| − 2n_M` versus
   `(eq:ordGaux_BAM)`: paper order = centre order `+ 2Σ_ext(r_i^{ext} − 1)` (prove report (a) E2), equal iff each external
   vertex is retained; (ii) block-level aux vertices with the factor `(W^d)^{n_M}` (the band's `(G_by_auxG)` form), whereas
   `(G_by_auxG_BA)` has fine-lattice atom centres and no `W^{qd}`.
3. **O3.** The nested-form and G4 instances use `baPQ` (`BAGraph.ofLGraph`: no `M`/`Ψ`-dotted edge, shadow = band graph), as
   1a-audit O4 foresaw; the shadow with `M`/`Ψ`-dotted edges is exercised at `G*` (vocabulary, G3). Nondegenerate, not a defect.
4. **O4 (§3 (E)).** Two unpinned public lemmas lack the stem: `BAGraph.auxVal_nonneg`, `BAGraph.molSolid_length_le`
   (BAAtom.lean:105, 155); no clash on main (§5). Instance names live in `namespace BAAtomInst`/`BAAtomInst2`.
5. **O5.** Target 3 named `baClaimSize`/`baClaimSizeG` as tools; the proof copies their private internals instead (prove report
   "Notes"). No statement effect. **O6.** `RBM3D/Probe/T2420Pins.lean` is on the branch; per the ticket it is never merged.
