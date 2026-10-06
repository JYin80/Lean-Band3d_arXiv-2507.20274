Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 04:29:19 UTC 2026

### (i) Exponent table (`π i j = true` iff `α_i` strictly closer to `b_j`; `q = q'+1`; `K_j` = segments of old path `j` in `Γ'` = visits of `α_{i₀}` + 1, `k_j = K_j - 1`; `n_j` = ghost-free segments of `j` in `Γ''`)

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| `j₁ ≠ j₂`, `r₁ ≠ r₂`, `em k₁ ≠ em k₂` | `own r_t = j_t` (F7) | `anpKey2_caseI_ne`; `IsNested` conj. 4 of `Γ'` (edge-disjoint paths) | sweep: 0 failures |
| `Γ'.noGhostPath r_t` | `true` | edge `em k_t` solid: (F2), A1 (`noGhostPath j_t`) or B1 (by def.) | holds for A1 and for B1 |
| `nSolid''` | `nSolid - 2` | 2 ghostifications (`anpKey_ghostify_nSolid` twice), (F8) | exact |
| `ordN''` | `ordN` | `ord = nS + 2(nW - nV)`, `nV = q' = q - 1`: `-2 + 2 = 0` | exact (all 1808 cases) |
| `nngh''` | `nngh + Σ_j k_j - 2` | `Γ''.noGhostPath r ↔ Γ'.noGhostPath r ∧ r ∉ {r₁,r₂}`, (F6) | `m := nngh''-nngh = Σ k_j - 2 ∈ {0,1,2}` seen; `m ≥ 0` since `k_{j₁},k_{j₂} ≥ 1` |
| `n_j` by type | A1 end: `K_j-1`; B1 end: `K_j-2`; other ghost-free: `K_j`; other ghost: `K_j-1` | (F6), one-step `r_t` removed | formula: 0 mismatches |
| `n_j - χ_j ≥ 0` (natural subtraction) | min 0 for every type | `K_j ≥ 2` on `j_t` (path arrives at `α`), `K_j ≥ 1` otherwise | slack 0..2; tight for A1 end with `K_j=2` |
| exponent of `ψ(0)` | `(ordN''-nngh'') + (nngh''-nngh) = ordN - nngh` | `zpow_add₀`, `ψ 0 > 0`; each factor of a fibre `≤ ψ(0)` | exact |
| far-segment factor | `2` (`\|a_j-b_j\| ≤ 2\|a''_{r*}-b''_{r*}\|`) | (a) split: triangle `a_j→x→b_j`; (b) A1: `anpKey2_half` with `z = x ∈ regionOne`; `r_a=r_b`: factor 1 | none lost beyond triangle |
| `θ` power | `θ^{q'}·θ = θ^q` | `Σ_x ξ(e₁,x)ξ(e₂,x) ≤ ½(Σ_x ξ(e₁,x)² + Σ_x ξ(e₂,x)²) ≤ θ` (`2xy ≤ x²+y²`, sum over `regionOne ⊆ univ`, `ξ ≥ 0`) | max ratio to `θ` 0.9505 (L=3), 0.7842 (L=5) |
| `C` | `C''` (from `hIH p' q' _ Γ''`) | `> 0` | none lost |
| `c` | `c''/2 ∈ (0, 1/2]` | `0 < c ≤ 1`; `ψ(c''·D'') ≤ ψ((c''/2)·D)` as `D ≤ 2D''`, antitone | `1 - c ≥ 1/2` |
| `ψ`-product (step 5) | `Π_r ψ(c''D''_r)^{χ''} ≤ ψ(0)^m Π_j ψ((c''/2)D_j)^{χ_j}` | fibrewise: `r*` gets the half-distance bound, the other `n_j-1` factors `≤ ψ(0)` | max ratio 1.0000, no violation |
| IH index | `k = q' < q = q'+1`, any `p'` | `AnpIH d q` | exact |
| per-graph (i₀=0) | `figAuxGh` (π≡F, B1+B1): `p'=4`, `own=[0,0,1,1]`, `r₁,r₂=0,2`, `nSolid''=2`, `ordN''=0`, `nngh''=nngh=0`, `m=0`, no ghost-free `j`. `figAux` (π₀, A1+A1): `nSolid''=4`, `ordN''=2`, `nngh''=nngh=2`, `m=0`, `r*=1,3` (subcase b, `s=F`). `figAuxMix` (π₀, B1+A1): `nSolid''=3`, `ordN''=1`, `nngh''=nngh=1`, `m=0`, `j=1`: `r*=3` (b, `s=F`) | all pins | exact; `ea,eb` in output |

### (ii) One concrete nondegenerate instance
`d = 3`, `L = 5` (125 sites), `p = q = 2`, `i₀ = 0` (`q' = 1`, `p' = 4`), `ψ(r) = 1/(1+r)`, random `ξ = ψ(D)·U` (`U` symmetric in `[0,1]`), `θ = 7.8801`, `c'' = 1/4`; `Γ ∈ {figAuxGh (B1+B1), figAux (A1+A1), figAuxMix (A1+B1)}`.
Deterministic hypotheses (`ψ>0` antitone, `ξ ≥ 0`, symmetric, `ξ ≤ ψ(|·|)`, `θ>0`, `Σ_β ξ² ≤ θ`, `GhostOK`, `IsNested`, `NoA2`, `AnpCaseI`, `Γ''` `GhostOK`/`IsNested`) are checked in the output. The IH (`AnpIH 3 2`) is another gate's pin: it is the hypothesis; its constant `C''` is taken as the empirical maximum over 300 samples (a lower bound for the true constant), so the last column is a consistency check of steps 3-6, not a proof of the IH. No external or limit hypothesis (all targets are deterministic, `d, L` arbitrary). The sweeps also include non-`NoA2` `π` (1154 of 1808 cases), since `NoA2` is not used. Scratch: `<scratchpad>/T2252/` (Python only).
Command: `cd <scratchpad>/T2252 && for f in "pre.py" "sweep.py 200" "num.py 3 200 2" "num.py 5 100 3" "table.py" "inst.py"; do echo "$ python3 $f"; python3 ${=f}; done > all.out` (zsh); output verbatim:
```
$ python3 pre.py
== (i) per-graph table (d-independent combinatorics; i0=0)
-- figAuxGh: GhostOK True IsNested True NoA2 True nSolid 4 ordN 0 nngh 0 types ['B1', 'B1']
   pair ((0, False, 0), (1, False, 1)): p'=4 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)] r1,r2=[0, 2]
   Gamma'': nSolid 2 (=nSolid-2: True) ordN'' 0 (=ordN: True) nngh'' 0 nngh 0 m=nngh''-nngh=0 (sum k_j - 2 = 0; k=[1, 1]) GhostOK True IsNested True F1-F8 True
   j=0 has a ghost: chi=0, no r* needed; n_j=0
   j=1 has a ghost: chi=0, no r* needed; n_j=0
-- figAux: GhostOK True IsNested True NoA2 True nSolid 6 ordN 2 nngh 2 types ['A1', 'A1']
   pair ((0, False, 0), (1, False, 1)): p'=4 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)] r1,r2=[0, 2]
   Gamma'': nSolid 4 (=nSolid-2: True) ordN'' 2 (=ordN: True) nngh'' 2 nngh 2 m=nngh''-nngh=0 (sum k_j - 2 = 0; k=[1, 1]) GhostOK True IsNested True F1-F8 True
   ghost-free j=0: r*=1 subcase b:s=F
   ghost-free j=1: r*=3 subcase b:s=F
-- figAuxMix: GhostOK True IsNested True NoA2 True nSolid 5 ordN 1 nngh 1 types ['B1', 'A1']
   pair ((0, False, 0), (1, False, 1)): p'=4 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)] r1,r2=[0, 2]
   Gamma'': nSolid 3 (=nSolid-2: True) ordN'' 1 (=ordN: True) nngh'' 1 nngh 1 m=nngh''-nngh=0 (sum k_j - 2 = 0; k=[1, 1]) GhostOK True IsNested True F1-F8 True
   j=0 has a ghost: chi=0, no r* needed; n_j=0
   ghost-free j=1: r*=3 subcase b:s=F
$ python3 sweep.py 200
graphs: 200 (nested, GhostOK, q>=1; q=1: 169, q=2: 31, p=3: 146)
pairs/graphs checked: {'(graph,i0,pi,pair)': 1808, 'b:s=F': 897, 'b:s=T': 893, 'surplus m>0': 672, 'a:whole': 626, 'a:split': 210}  of which not NoA2 at pi: 1154
structural failures: none
$ python3 num.py 3 200 2
L=3 (|Z_L^3|=27), graphs=200: 3616 (graph,i0,pi,pair,psi,xi,a,b) cases, 13718 (case,x) points
  violations: none
  max valOn(Gamma,region pi)/sum_x xi(e1,x)xi(e2,x)Gamma''.val = 1.0000 (<=1)
  max |Gamma'.val - xi xi Gamma''.val|/max(1,.) = 4.56e-16
  max product-bound ratio P(x)/(psi0^m prod_j psi(c''/2|a_j-b_j|)): c''=1: 1.0000, c''=1/4: 1.0000 (<=1)
  max sum_x xi(e1,x)xi(e2,x)/theta = 0.9505 (<=1)
$ python3 num.py 5 100 3
L=5 (|Z_L^3|=125), graphs=100: 2170 (graph,i0,pi,pair,psi,xi,a,b) cases, 39459 (case,x) points
  violations: none
  max valOn(Gamma,region pi)/sum_x xi(e1,x)xi(e2,x)Gamma''.val = 1.0000 (<=1)
  max |Gamma'.val - xi xi Gamma''.val|/max(1,.) = 1.34e-15
  max product-bound ratio P(x)/(psi0^m prod_j psi(c''/2|a_j-b_j|)): c''=1: 1.0000, c''=1/4: 1.0000 (<=1)
  max sum_x xi(e1,x)xi(e2,x)/theta = 0.7842 (<=1)
$ python3 table.py
1808 (graph,i0,pi,pair) cases; m = nngh''-nngh = sum_j k_j - 2 histogram: {0: 1136, 1: 518, 2: 154}
n_j formula (K, K-1, K-1, K-2 by type) mismatches: 0
  A1 end (chi=1): min..max of n_j - chi_j = 0..1
  K_j (A1 end (chi=1)): min..max of K_j = 2..3
  B1 end (chi=0): min..max of n_j - chi_j = 0..1
  K_j (B1 end (chi=0)): min..max of K_j = 2..3
  other, ghost-free: min..max of n_j - chi_j = 0..2
  K_j (other, ghost-free): min..max of K_j = 1..3
  other, ghost: min..max of n_j - chi_j = 0..2
  K_j (other, ghost): min..max of K_j = 1..3
$ python3 inst.py
d=3 L=5 |Z_L^3|=125 psi(r)=1/(1+r) theta=7.8801 c''=0.25 (c=c''/2=0.125)
hyps: psi>0 antitone True; xi>=0 True symmetric True xi<=psi(|.|) True theta>0 True; row-sums xi^2 <= theta: True
-- figAuxGh (B1+B1) at i0=0: GhostOK True IsNested True NoA2 True CaseI True; p=2 q=2; Gamma'': p'=4 q'=1 GhostOK True IsNested True ordN''-nngh''=0 (=ordN-nngh=0)
   empirical C''(Gamma'', c''=0.25) = 1.0000; conclusion with (C,c)=(C'',c''/2): max valOn/(C theta^q psi0^(ord-nngh) prod psi(c|a-b|)) = 0.3643 (<=1); with C=1: 0.3643
-- figAux (A1+A1) at i0=0: GhostOK True IsNested True NoA2 True CaseI True; p=2 q=2; Gamma'': p'=4 q'=1 GhostOK True IsNested True ordN''-nngh''=0 (=ordN-nngh=0)
   empirical C''(Gamma'', c''=0.25) = 0.0815; conclusion with (C,c)=(C'',c''/2): max valOn/(C theta^q psi0^(ord-nngh) prod psi(c|a-b|)) = 0.0631 (<=1); with C=1: 0.0051
-- figAuxMix (A1+B1) at i0=0: GhostOK True IsNested True NoA2 True CaseI True; p=2 q=2; Gamma'': p'=4 q'=1 GhostOK True IsNested True ordN''-nngh''=0 (=ordN-nngh=0)
   empirical C''(Gamma'', c''=0.25) = 0.2553; conclusion with (C,c)=(C'',c''/2): max valOn/(C theta^q psi0^(ord-nngh) prod psi(c|a-b|)) = 0.0543 (<=1); with C=1: 0.0139
```
(`pre.py`: fixes via T2242's `fixvertex`/`checkF`, copied; `sweep.py`: step 1-4 structure on 200 random nested GhostOK graphs, every `(i₀, π)` and every A1/B1 pair; `num.py`: steps 3, 5, 6 and `Σ_x ξξ ≤ θ` numerically.)

### Checks by inspection (against `7_8:1152-1244`, merged statements)
1. Step 4 covers every ghost-free `j`: `j ∉ {j₁,j₂}` splits into `r_a = r_b` (a_j→b_j) and `r_a ≠ r_b` (then `eb r_a = ea r_b = none` by (F4) uniqueness; triangle gives one of the two `≥ |a_j-b_j|/2`); `j = j_t` is A1 (B1 has a ghost, so `χ = 0`), `r_t ∈ {r_a, r_b}` by `s_t`, and `r*` is the other one, `≠ r_t` because (F7) gives `eb r_a = none` (resp. `ea r_b = none`) while the other end is `some`; its far end is `x`, `x ∈ regionOne (π i₀)` and `π i₀ j_t = s_t` give the half-distance; `own r* = j_t ∉ {j_{3-t}}`, so `r* ∉ {r₁,r₂}`, and it is ghost-free in `Γ'` by (F6). Counts in the output: `a:whole` 626, `a:split` 210, `b:s=F` 897, `b:s=T` 893, no failure.
2. `em k₁ ≠ em k₂` and the one-step paths are ghost-free in `Γ'` also in the B1 case: only the flag of the edge `em k_t` matters (F2), and a B1 edge is solid by definition.
3. `NoA2 π` and `(eq:Psi)` are not used; `ψ > 0` antitone, `ξ ≥ 0` symmetric, `ξ ≤ ψ`, `Σ_β ξ² ≤ θ` only. The merged `AnpDetGhCaseI` is true as stated; no primed successor is needed.
4. Paper differences (candidates for the report (d)): the auxiliary path `(a_1 ⇒ a_2)` is replaced by two ghostified one-step paths; `nngh'' = nngh + Σ k_j - 2` (the paper's `n_ngh(𝒢^new) = n_ngh(𝒢)` is the case `Σ k_j = 2`, 1136 of 1808 cases; `m ∈ {1,2}` in 672); both sides `a_j`/`b_j` allowed; `c ↦ c/2` per step.

### Verdicts
- `anpDetGhCaseI_holds : ∀ d, AnpDetGhCaseI d` (cases (I)+(II)): **PASS** (hypotheses satisfiable at the instance, exponents close with slack above, no false statement found).
- Instances (1)-(5): **PASS** (shapes satisfiable: B1+B1, A1+A1, A1+B1 above; `figAuxMix` `GhostOK`, `IsNested`, `NoA2 piMix`, `AnpCaseI piMix` True in the script; (5) `Γ''.ordN = ordN`, `Γ''.nngh = nngh = 0` at `figAuxGh`).

### §29 checklist
(1) no time variable. (2) no `1 - ilambda²/L²`. (3) no `L^d ≤ W^K`. (4) no `∀ᶠ n`. (5) uniform in `(a,b)`: `∀ a b` inside, `(C, c)` before `L`. (6) no parameter lower bound (`d`, `L` arbitrary, `[NeZero L]`). (7) no scale: `ψ`, `θ` abstract. §64 (4): no grid lift.

## (b) Script output and narrative (stage 1b, written Tue Oct  6 04:53:28 UTC 2026)

```
$ date -u; git log --oneline -3; git status --short
Tue Oct  6 04:52:22 UTC 2026
f6b9f8f T2252: register AnpIH (premise of the LW-12c instances) in the owed table
96fe516 T2252: LW-12c cases (I)+(II) of lem:Anp_key_gh (Graph/AnpKey3)
88183b6 T2251: merge UN-19 Universality/JakSpectral
$ git diff --stat main...t/T2252
 RBM3D/Graph/AnpKey3.lean | 714 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   1 +
 2 files changed, 715 insertions(+)
$ git diff main...t/T2252 -- RBM3D/Test/Axioms.lean | grep '^[+-][^+-]' | cut -c1-330
+   `RBM.Graph.AnpIH, -- the induction hypothesis of `AnpDetGhStep` (`7_8:1107`) for `k < q`, premise of the compiled instances of LW-12c (`anpKey3_inst_*`, T2252); proved inside `anpDetGh_of_step` (T2234) once LW-12f proves `AnpDetGhStep` (DECISIONS §20: owed)
$ wc -l RBM3D/Graph/AnpKey3.lean; grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/AnpKey3.lean
     714 RBM3D/Graph/AnpKey3.lean
grep exit 1
$ lake build RBM3D.Graph.AnpKey3   # saved log of the real build, filtered
224:✔ [3348/3348] Built RBM3D.Graph.AnpKey3 (4.1s)
225:Build completed successfully (3348 jobs).
(build.out above: `lake build RBM3D.Graph.AnpKey3 > build.out`, run at Tue Oct  6 04:44:20 UTC 2026 before the commit; the file is unchanged since)
$ lake build RBM3D.Graph.AnpKey3 2>&1 | tail -1
Build completed successfully (3348 jobs).
$ lake build   # full library, root RBM3D.lean unchanged (the hub adds the import); saved log, tail
non-vacuity certificates: 0 of 160 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4056 jobs).
```

Axioms of every public declaration of the file:
```
$ lake env lean axioms.lean | python3 group_axioms.py   # axioms.lean: `#print axioms RBM.Graph.<n>` for the 25 declarations of decls.txt
25 declarations printed; distinct axiom sets: 4
[propext]:  3 decls: anpKey3_endAt_mem, anpKey3_pi, anpKey3_figAuxMix
[propext, Quot.sound]:  3 decls: anpKey3_end_solid, anpKey3_noGhost_single, anpKey3_gh2
[]:  1 decls: anpKey3_endAt_of
[propext, Classical.choice, Quot.sound]:  18 decls: anpKey3_gh2_props, anpKey3_endFactor, anpKey3_far_end, anpKey3_far_gen, anpKey3_far, anpKey3_prod, anpKey3_sum_xx, anpDetGhCaseI_holds, anpKey3_inst_figAuxGh_hyp, anpKey3_inst_figAuxGh, anpKey3_inst_figAux_hyp, anpKey3_inst_figAux, anpKey3_inst_figAuxMix, anpKey3_inst_chain, anpKey3_inst_types, anpKey3_fixV_ng_iff, anpKey3_figAuxGh_seg, anpKey3_inst_gh2
```

Target and instance statements, extracted from the file by script (`stmt.py <names>`):
```
-- RBM3D/Graph/AnpKey3.lean:431
theorem anpDetGhCaseI_holds : ∀ d : ℕ, AnpDetGhCaseI d := by
-- RBM3D/Graph/AnpKey3.lean:590
theorem anpKey3_inst_figAuxGh :
    AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false) := fun hIH =>
-- RBM3D/Graph/AnpKey3.lean:602
theorem anpKey3_inst_figAux :
    figAux.NoA2 anpKey3_pi ∧ AnpCaseI figAux anpKey3_pi ∧ (AnpIH 3 2 → AnpDetGhRegAt 3 figAux anpKey3_pi) :=
-- RBM3D/Graph/AnpKey3.lean:609
theorem anpKey3_inst_figAuxMix :
    anpKey3_figAuxMix.GhostOK ∧ anpKey3_figAuxMix.IsNested ∧ anpKey3_figAuxMix.NoA2 anpKey3_pi ∧
      AnpCaseI anpKey3_figAuxMix anpKey3_pi ∧
      (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey3_figAuxMix anpKey3_pi) := by
-- RBM3D/Graph/AnpKey3.lean:620
theorem anpKey3_inst_chain : AnpDetGhCaseIII 3 → AnpDetGhCaseIV 3 → LWAnpKeyGh 3 :=
-- RBM3D/Graph/AnpKey3.lean:659
theorem anpKey3_inst_gh2 :
    ∃ (p' : ℕ) (Γ'' : NGraph p' 1), Γ''.GhostOK ∧ Γ''.IsNested ∧
      Γ''.ordN = anpKey2_figAuxGh.ordN ∧ Γ''.nngh = anpKey2_figAuxGh.nngh := by
-- RBM3D/Graph/AnpKey3.lean:625
theorem anpKey3_inst_types :
    (anpKey2_figAuxGh.IsB1 (fun _ _ => false) 0 false (anpKey2_eGh 0) 0 ∧
      anpKey2_figAuxGh.IsB1 (fun _ _ => false) 1 false (anpKey2_eGh 1) 0) ∧
    (figAux.IsA1 anpKey3_pi 0 false (anpKey2_eAux 0) 0 ∧ figAux.IsA1 anpKey3_pi 1 false (anpKey2_eAux 1) 0) ∧
    (anpKey3_figAuxMix.IsB1 anpKey3_pi 0 false ⟨0, by decide⟩ 0 ∧
      anpKey3_figAuxMix.IsA1 anpKey3_pi 1 false ⟨1, by decide⟩ 0) := by
-- RBM3D/Graph/AnpKey3.lean:581
theorem anpKey3_inst_figAuxGh_hyp :
    anpKey2_figAuxGh.GhostOK ∧ anpKey2_figAuxGh.IsNested ∧ anpKey2_figAuxGh.NoA2 (fun _ _ => false) ∧
      AnpCaseI anpKey2_figAuxGh (fun _ _ => false) := by
-- RBM3D/Graph/AnpKey3.lean:596
theorem anpKey3_inst_figAux_hyp :
    figAux.GhostOK ∧ figAux.IsNested ∧ figAux.NoA2 anpKey3_pi ∧ AnpCaseI figAux anpKey3_pi := by
-- RBM3D/Graph/AnpKey3.lean:570
def anpKey3_pi : Fin 2 → Fin 2 → Bool := fun i _ => decide (i = 1)
-- RBM3D/Graph/AnpKey3.lean:574
def anpKey3_figAuxMix : NGraph 2 2 where
  es := [⟨false, .inl (.inl 0), .inr 0⟩, ⟨false, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inr 1⟩,
         ⟨false, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inl (.inr 0)⟩, ⟨false, .inr 1, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (2, .inr 1), (4, .inl (.inr 0))]
    else [(1, .inr 0), (3, .inr 1), (5, .inl (.inr 1))]
```

Pin check (check file section 2 and section 3 `figAuxMix`/`piMix` copied into a scratch namespace, `pin_check.lean`):
```
$ lake env lean pin_check.lean
def AnpKey3CaseIHoldsPin : Prop := ∀ d : ℕ, AnpDetGhCaseI d
example : AnpKey3CaseIHoldsPin := @anpDetGhCaseI_holds
example : figAuxMix = anpKey3_figAuxMix := rfl
example : piMix = anpKey3_pi := rfl
exit 0
```

Registry pre-check (`registry_pre.lean` = `import RBM3D`, `import RBM3D.Graph.AnpKey3`, `#assert_rbm_axioms`, after `lake build RBM3D.Test.Axioms`):
```
$ lake env lean registry_pre.lean
Tue Oct  6 04:52:32 UTC 2026
Build completed successfully (2 jobs).
exit 0
axiom audit: 7520 theorems, 2533 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
75:  RBM.Graph.AnpDetGhCaseI: 3 [no certificate]
78:  RBM.Graph.AnpIH: 3 [no certificate]
registry: 2 borrowed + 158 owed + 98 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
199: RBM.Graph.AnpDetGhCaseI,
```

Name-clash grep (`clash.sh decls.txt`: each new public name over worktree `RBM3D/`, `RBM3D.lean`, main `RBM3D/`, drafts and check files of T2253-T2256):
```
$ bash clash.sh decls.txt | counts; public declarations (line:name)
names checked:       25; names with a hit: 0
62:anpKey3_endAt_mem  75:anpKey3_end_solid  84:anpKey3_endAt_of  89:anpKey3_noGhost_single  106:anpKey3_gh2  112:anpKey3_gh2_props  173:anpKey3_endFactor  202:anpKey3_far_end  268:anpKey3_far_gen  318:anpKey3_far  352:anpKey3_prod  405:anpKey3_sum_xx  431:anpDetGhCaseI_holds  570:anpKey3_pi  574:anpKey3_figAuxMix  581:anpKey3_inst_figAuxGh_hyp  590:anpKey3_inst_figAuxGh  596:anpKey3_inst_figAux_hyp  602:anpKey3_inst_figAux  609:anpKey3_inst_figAuxMix  620:anpKey3_inst_chain  625:anpKey3_inst_types  636:anpKey3_fixV_ng_iff  652:anpKey3_figAuxGh_seg  659:anpKey3_inst_gh2  
```

### Narrative
1. Delivered: `anpDetGhCaseI_holds : ∀ d : ℕ, AnpDetGhCaseI d` (`RBM3D/Graph/AnpKey3.lean:431`), the merged pin unchanged; the pin check above elaborates `@anpDetGhCaseI_holds : AnpKey3CaseIHoldsPin`. No hypothesis added, `d` arbitrary, `Γ.NoA2 π` is bound as `_` (unused), `(eq:Psi)` is not used, no private declaration (helpers carry the prefix `anpKey3_`). No port: no RBM1D/RBM2D file was read or used.
2. Route (ticket steps 1-6), file sections: §1 (`:55`) A1/B1 ending edges are solid; §2 (`:99`) `anpKey3_gh2 Γ e₁ e₂ := (Γ.ghostify e₁).ghostify (Γ.ghostifyIdx e₁ e₂)` and `anpKey3_gh2_props`: `GhostOK`, `IsNested`, `nSolid'' + 2 = nSolid`, `noGhostPath'' r ↔ noGhostPath r ∧ r ≠ r₁ ∧ r ≠ r₂`, and the edge product splits off `ξ·ξ`, all from the merged `anpKey_ghostify_*`, `anpKey_gf_*`, `anpKey2_ep_ghostify`; §3 (`:167`) `anpKey3_endFactor`: the factor of an ending edge at the fixed vertex is `ξ(e_t, x)`, `e_t = if s_t then b j_t else a j_t` (`anpKey2_endAt_ends`, `Fin.insertNth_apply_same`, symmetry of `ξ`); §4 (`:193`) the far segment: `anpKey3_far_end` (subcase (b), A1 end, `anpKey2_half` with `x ∈ regionOne`), `anpKey3_far_gen` (subcase (a), whole path or triangle `anpKey_zdistInf_tri`), `anpKey3_far` (assembly; `r* ∉ {r₁, r₂}` because `own r* = j` and `own r₁ ≠ own r₂`); §5 (`:345`) `anpKey3_prod`; §6 (`:400`) `anpKey3_sum_xx` (`2xy ≤ x² + y²`, rows `e₁`, `e₂`, `regionOne ⊆ univ`); §7 (`:423`) the target.
3. Deviation from the ticket's route in step 5 (not a statement difference): `anpKey3_prod` does not use the fibres of `own` (`Finset.prod_fiberwise`, `card_eq_sum_card_fiberwise`, `n_j`). It takes an injective choice `ρ : Fin p → Fin p'` of one ghost-free segment per ghost-free old path (from step 4), splits the product over the ghost-free segments `T` of `Γ''` as `ρ(J) ⊔ (T \ ρ(J))`, bounds the first part by the `j`-factors and each factor of the second by `ψ(0)`; the exponent is `|T \ ρ(J)| = |T| - |J|` (`Finset.card_sdiff_of_subset`, `card_image_of_injOn`), so `nngh ≤ nngh''` is a by-product.
4. The target: `q = q' + 1`; `anpKey2_fix` gives (F1)-(F8); (F7) gives `r_t` with `own r_t = j_t`, hence `r₁ ≠ r₂` from `anpKey2_caseI_ne`; the IH `hIH p' q' _ Γ''` gives `(C, c)`, the new constants are `(C, c/2)`; `ordN'' = ordN` by `unfold NGraph.ordN; simp only [ord]; omega` from `nSolid'' + 2 = nSolid` and (F8); the pointwise bound `Γ'.val ≤ ξ(e₁,x) ξ(e₂,x) K`, `K := C θ^{q'} ψ(0)^{ordN - nngh} Π_j (…)`, then `valOn ≤ Σ_x ξξ K ≤ θ K`. The `ψ(0)` exponents combine by `zpow_add₀`.
5. Instances (§8, `:565`): (1)-(3) apply the target at `d = 3`, `q = p = 2`; every deterministic hypothesis (`GhostOK`, `IsNested`, `NoA2`, `AnpCaseI`) is a compiled theorem by `decide +kernel` (`anpKey3_inst_figAuxGh_hyp`, `anpKey3_inst_figAux_hyp`, `anpKey3_inst_figAuxMix`); `anpKey3_inst_types` states B1+B1 (`figAuxGh`), A1+A1 (`figAux`), B1+A1 (`anpKey3_figAuxMix`) at `ℳ₁`; the only premise is `AnpIH 3 2`. (4) is `anpKey2_inst_chain` with the target. (5) uses the explicit `anpKey2_fixV` (with `s₀` from `anpKey2_exists_s₀`), `anpKey2_fixV_end`, `anpKey3_gh2_props`; `ordN` from `anpKey2_fixV_nSolid`; `nngh'' = 0 = nngh` because a ghost-free segment of `Γ''` is a ghost-free segment of `Γ'` other than `r₀, r₁`, which by `anpKey3_figAuxGh_seg` (a `decide +kernel` fact over the segments) contains edge 0 or 1, contradicting edge-disjointness (`IsNested` conjunct 4).
6. Registry (`RBM3D/Test/Axioms.lean`, sole writable file): the first pre-check run after stating the instances in the pinned shape (started 04:45:19 UTC) failed with `1 premise(s) ... [RBM.Graph.AnpIH]`, exit 1, because `AnpIH 3 2 →` is a theorem premise; one line registering `RBM.Graph.AnpIH` in `owedProps` was added (shown above, commit f6b9f8f); the pre-check above then exits 0. No line deleted; the `AnpDetGhCaseI` line stays and is listed as "registered, carries nothing" (info, output line 199 of the pre-check).
7. Section (a) was not edited; no (a′): every claim of (a) that the proof uses (exponent table rows `nSolid''`, `ordN''`, far-segment factor `2`, `c/2`, `θ` power, IH index) was reproduced by the Lean proof; (a)'s `nngh''` formula and the `n_j` table are script findings that the Lean proof does not use.

## (c) Verified Mathlib names used
- `Fin.insertNth_apply_same`: `Mathlib/Data/Fin/Tuple/Basic.lean:856`.
- `Finset.prod_filter` (`Algebra/BigOperators/Group/Finset/Basic.lean:333`), `Finset.prod_sdiff` (`:192`), `Finset.prod_image` (`:95`).
- `Finset.card_le_card` (`Data/Finset/Card.lean:66`), `Finset.card_image_of_injOn` (`:239`), `Finset.card_sdiff_of_subset` (`:598`), `Finset.card_eq_zero` (`:76`).
- `Finset.prod_le_prod₀` (`Algebra/Order/BigOperators/GroupWithZero/Finset.lean:39`, hypotheses `0 ≤ f i` and `f i ≤ g i`); verified NOT the right name: `Finset.prod_le_prod` (`Algebra/Order/BigOperators/Group/Finset.lean:111`) has only `f i ≤ g i` (ordered monoid).
- `Finset.sum_le_sum_of_subset_of_nonneg` (additive of `prod_le_prod_of_subset_of_one_le`, `Group/Finset.lean:171`), `Finset.filter_eq_empty_iff` (`Data/Finset/Filter.lean:159`), `Finset.sum_mul`, `Finset.mul_sum` (`Algebra/BigOperators/Ring/Finset.lean:56,59`).
- `two_mul_le_add_sq` (`Algebra/Order/Ring/Unbundled/Basic.lean:690`), `zpow_add₀` (`Algebra/GroupWithZero/Basic.lean:508`).
- Compiled uses, not re-located: `Finset.prod_nonneg`, `Finset.sum_add_distrib`, `Finset.sum_div`, `zpow_natCast`, `Nat.cast_sub`, `List.mem_of_mem_head?`, `List.mem_of_getLast?` (core, as at `AnpKey2.lean:587-589`).
- Listed in the ticket, exist (check file compiled), not needed: `Finset.prod_fiberwise`, `Finset.card_eq_sum_card_fiberwise`, `Finset.mul_prod_erase`, `Finset.prod_pow_eq_pow_sum`, `Finset.sum_tsub_distrib`.

## (d) Open issues and paper-delta candidates
- T2252a: no auxiliary ghost path `(a_1 ⇒ a_2)` (`7_8:1161`, `:1227`): the two ending edges at `α_{i₀}` become one-step paths `r₁`, `r₂` of the fixed graph and are made ghost (`anpKey3_gh2`).
- T2252b: both sides allowed, no WLOG `(a_1, α_q)`, `(a_2, α_q)`: the factor is `ξ(e_t, x)` with `e_t = a_{j_t}` (`s_t = false`) or `b_{j_t}` (`s_t = true`) (`anpKey3_endFactor`).
- T2252c: `ord(Γ'') = ord(Γ)` exactly (proved inside the target, `hordeq`); the paper's second half of `(eq:change_of_order)`, `n_ngh(𝒢^new) = n_ngh(𝒢)`, is not used: Lean proves only `nngh ≤ nngh''` (injective `ρ`) and absorbs the surplus `nngh'' - nngh` by `ψ(c·|·|) ≤ ψ(0)` as in `:1237-1239`. The formula `nngh'' = nngh + Σ_j k_j - 2` (m = 0 in 1136 of 1808 cases) is the preflight script's finding, not proved in Lean.
- T2252d: `c ↦ c/2` per step; Cauchy-Schwarz as `2xy ≤ x² + y²` with the same `θ`.
- T2252e: Cases (I) and (II) are one proof (any number of visits `K_j`, any `deg α_q ≥ 4`, any `i₀`).
- Registry: `RBM.Graph.AnpIH` added to `owedProps` (one line, `RBM3D/Test/Axioms.lean`, DECISIONS §20; the dispatcher may reclassify it as structural). The line is needed as long as an instance theorem has `AnpIH 3 2 →` as premise.
- Root import `import RBM3D.Graph.AnpKey3` is the hub's at merge; LW-12f (`AnpKey6`) closes `anpDetGhStep_holds` from `anpDetGhCaseI_holds` as in the ticket and deletes the registry lines `AnpDetGhCaseI` etc.
- No blocker, no negative statement needed: the pin is true as stated and no primed successor was added.
