Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 02:13:12 UTC 2026

Scripts live in the scratchpad `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2367` (not in the repository): `mirror.py` (Lean-style mirror of targets 2-4), `compare.py`, `draw.py`, `instance.py`, `api.py`, `counts.py`. `mgraph.py`, `kode.py` are copies of T2365's, which `diff` shows identical to T2360's.

**Definitions (prose), `F` with `KLIsTSP F`, arcs `[i,j)` as in `KLInArc`, `σ_x` read at `x mod n`.**
- Slots `BAslot F := Fin n ⊕ ↥F ⊕ ↥F` (leaf `v`; chord side `out J` = the slot in `KLnodePar F J`; chord side `in J` = the slot in `J`). No hypothesis: `BAslot_card` is `n + 2|F|` (cardinality of a sum type).
- Node: `leaf v ↦ KLleafPar F v`, `out J ↦ KLnodePar F J`, `in J ↦ J` (type `Fin n × Fin n`).
- Start `x(s)` (first vertex of the edge's vertex range): `leaf v ↦ v`, `out J ↦ J.1`, `in J ↦ J.2` (`J = (i,j)`: the parent edge's range is `[j .. i]` wrapped).
- Within a node the starts are pairwise distinct (needs `KLIsTSP F`: laminarity, `KLleafPar_spec`, `KLnodePar_spec`, `KLwholeP_not_mem`; no other hypothesis). `BAnextSlot s` = the slot of the same node with the next larger start, or the smallest start if `s` has the largest (`Finset.exists_min_image`-style choice, total on every `F`). Node cycle length `≥ 3` and key injectivity are asserted for all `F ∈ TSP n`, `n ≤ 7`, in `mirror.py`/`counts.py`.
- Charge: `BAMcharge F σ s := σ (x (BAnextSlot s))`. In arcs: the `M`-edge `s → s'` carries `σ_x`, the boundary edge `(a_{x-1}, a_x)` ending at the first vertex `x` of the next range = K00 convention `BAMLoop_apply`: `σ_i` on `(a_{i-1}, a_i)`, `∏ M(σ_i)_{a_{i-1} a_i}`. Wrap: next of the last slot is the first, `x = i` (node `(i,j)`) or `0` (root).
- Value `KLgval` with `Nd = BAslot F`, `Lf = Fin n`, `Ed = ↥F ⊕ BAslot F`: leaf `v`: `Θ^{(σ_v,σ_{v+1})}(a_v, b(leaf v))`; chord `J=(i,j)`: `(tΘ^{(σ_i,σ_j)})(b(in J), b(out J))`; `M`-edge `s`: `M(charge s)(b s, b(next s))`. Indices `(σ v, σ (v+1))` and `(σ i, σ j)` are NOT changed by K00 (`(Kn3sol)` `1_2:1176` has `Θ^{(σ_k,σ_{k+1})}(a_k,·)`).
- `BAGamma := BACactusVal` for every `F` (same formula, no `if`; K05b uses it only on `TSP n`). W-power: `F(b_i) = W^{(k_i-1)d} 𝓜^{(k_i)} = ∏ M` (`A` `eq:Mloop_defgen`, `BAMLoop_apply`), so `Γ` carries no `W`; the `W^{-d(n-1)}` is outside, as in `BATreeRep`. (`W = 1` in the mirror does not test this; it is read from the two statements.)
- Hypotheses: none beyond `KLIsTSP F` and `2 ≤ n` (from `3 ≤ n`) for the `BAnextSlot` facts; symmetric `M` (`∀σ, (M σ)ᵀ = M σ`) for 5 (c). No amend needed. External hypotheses: none (no registry; no limit check owed).

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| `n` | `≥ 3`; `BACactusVal_three` at `n = 3` | `BATreeRep` `3 ≤ n`; `KLnodePar_spec` `2 ≤ n` | 1 above `2`; 0 at 3 (one tree) |
| `|F|` | `0 ≤ \|F\| ≤ n-3` (`counts.py`: 0,1,2,3,4 at `n = 3..7`) | `F ∈ TSP n` | `n=4: F ∈ {∅,{(0,2)},{(1,3)}}` |
| slots / `M`-edges | `n + 2\|F\|` (3,6,9,12,15 max) | `BAslot_card` | exact |
| edges of `KLgval` | `\|F\| + n + 2\|F\| = n + 3\|F\|` | `Ed = ↥F ⊕ BAslot F` | exact |
| nodes / cycles | `\|F\|+1`; each cycle length `≥ 3` (`counts.py`) | `M`-loop with `k_i ≥ 3` sides | min 3 = bound |
| `W` power | outside: `(W^d)⁻¹^{n-1}`; inside `Γ`: `W^0` | `BATreeRep` prefactor | exact |
| `t` | `[0,1)`; defs need none; `Θ` invertible at `t = 1/10` (4 dets in `instance.py`) | `PropThetaQ = Ring.inverse` | `det ≠ 0`: -13/250, -121/25, -793/25 |
| `L, d` | `L = 3`, `d = 1` (`BAMLoop_witM`) | `3 ≤ L`; `d` free, no `3 ≤ d` | `L`: 0; `d`: none |
| tol (α) | measured `1.9e-15` | `≤ 1e-12` | factor 5e2 |
| tol (β) | `n ≤ 5`: `6.8e-10`; `n = 6`: `1.24e-9` | `≤ 1e-8` | factor 15 (n ≤ 5), 8 (n = 6) |
| stop line | estimate 1070 (iv) | `wc -l ≤ 1300` | 230 |

### (ii) Concrete nondegenerate instance
`d = 1, L = 3, M = BAMLoop_witM` (`BA/KBase.lean:102`), `t = 1/10`, `n = 3` and `4`, `σ = (+,+,-,+)`, `a = (0,1,2,0)`; every hypothesis: `KLIsTSP F` for `F ∈ {∅,{(0,2)},{(1,3)}}`, `3 ≤ n`, `3 ≤ L`, `M σ` symmetric, `det(1 - tM^{(σσ')}) ≠ 0`. Command `cd $S; python3 instance.py` (exact `Fraction`s; `Γ` = brute-force sum over slot labels; output excerpted, the `det` rows and the `KLIsTSP` rows merged onto one line each, numbers verbatim):
```
t = 1/10  (t in [0,1)); witM symmetric: True
  det(1 - t M^(1,1)) = -13/250  (nonzero => PropThetaQ = true inverse)
  det(1 - t M^(1,0)) = -121/25 ;  det(1 - t M^(0,1)) = -121/25 ;  det(1 - t M^(0,0)) = -793/25
n=3, F=empty, sigma=(+,+,-), a=(0,1,2):  t=0: Gamma = 15 ;  t=1/10: Gamma = 104425/6292
   closed form (Kn3sol) at t=1/10: 104425/6292  equals cactus value: True
n=4, sigma=(+,+,-,+), a=(0,1,2,0), t=1/10:
   F=[]        #slots=4  Gamma = 21025500/1859  (~11310.1)  nonzero: True
   F=[(0, 2)]  #slots=6  Gamma = 2622270125/1799512  (~1457.21)  nonzero: True
   F=[(1, 3)]  #slots=6  Gamma = 5602354125/531674  (~10537.2)  nonzero: True
t=0 check vs BAMLoop_apply formula (n=4, a=(0,1,2,1)):  sum_F Gamma_F(t=0) = 10  prod_i M(sig_i)_{a_{(i+3)%4} a_i} = 10  equal: True
KLIsTSP [] True / [(0, 2)] True / [(1, 3)] True   TSP sizes n=3..6: [1, 3, 11, 45]
```
`Γ(∅, t=0) = 15` is `BAMLoop_witness`. Lean 5 (b) closed form: `Γ(∅) = Σ_b ∏_v Θ^{(σ_v,σ_{v+1})}(a_v,b_v) ∏_v M(σ_{v+1})_{b_v b_{v+1}}`; `n = 3` is `(Kn3sol)` (`1_2:1176`): `M(σ_0)_{b_2b_0}M(σ_1)_{b_0b_1}M(σ_2)_{b_1b_2} = 𝓜^{(3)}_{σ,b}` (`1_2:1003`); D634. `BAslot_card` at `n=4, F={(0,2)}` = 6 (`draw.py` below).

**Mirror (target 6).** Command `cd $S; python3 mirror.py; python3 compare.py` (`mirror.py` builds slots, `next`, `charge`, `KLgval` as the Lean text; `mgraph.gamma_value` is the B8 reference). Combinatorics `mirror.py`:
```
n=3  |TSP|=1  combinatorics (card n+2|F|, next = permutation, preserves node, one cycle per node, keys injective): OK
n=4  |TSP|=3 ... OK  n=5  |TSP|=11 ... OK  n=6  |TSP|=45 ... OK  n=7  |TSP|=197 ... OK
```
`compare.py` (RK4 600 steps, K00/paper `make_system(..,'paper')`, all `σ`, all `a`; columns n, #trees, (α) `max|mirror-mgraph|`, fixed-`a` vs open-`a`, (β) `max|Σ_F mirror - K_ODE|`, `max|K|`, worst σ):
```
--- q=5 g=0.8 E=0.3 t=0.5 (d=1, W=1)      --- q=4 g=0.6 E=-0.4 t=0.7             --- q=3 g=1.1 E=0.0 t=0.6
 3  1 0.00e+00 2.78e-17 6.08e-14 6.42e-01  3  1 0.00e+00 2.22e-16 8.21e-12 1.83e+00  3  1 0.00e+00 0.00e+00 1.84e-12 1.45e+00
 4  3 5.56e-17 2.79e-17 9.32e-13 7.60e-01  4  3 8.88e-16 4.45e-16 2.11e-10 3.81e+00  4  3 4.97e-16 2.22e-16 4.54e-11 2.98e+00
 5 11 1.67e-16 3.18e-17 1.73e-12 7.34e-01  5 11 1.81e-15 1.78e-15 6.76e-10 5.96e+00  5 11 6.28e-16 4.58e-16 1.58e-10 5.07e+00
                                                                                       6 45 1.91e-15 8.88e-16 1.24e-09 1.12e+01
```
(Rows reflowed side by side; numbers verbatim from `compare_out.txt`.) **(α) max `1.9e-15` ≤ 1e-12; (β) max `1.24e-9` (n = 6), `6.76e-10` (n ≤ 5) ≤ 1e-8. Stop line not triggered.** `api.py` (q=4): `(5b)` closed form vs `F=∅` value `0.00e+00` (n=3..6); `(5c)` random per-edge orientation flips, all `F`, `n=3..6`: `0.00e+00`; `(5a)` random slot relabelling: `1.14e-16`. Orientation of chord/`M`-edge matters only for non-symmetric `M`; untested there (BA is symmetric, `BATheta_isSymm`).

### (iii) `n = 4`, slot cycles and charges (`cd $S; python3 draw.py`; `M(σ_x)` on the arrow `s → next s`)
```
F=[]      root(0,3): leaf0 -M(s1)-> leaf1 -M(s2)-> leaf2 -M(s3)-> leaf3 -M(s0)-> leaf0
F=[(0,2)] root(0,3): out(0,2)[x=0] -M(s2)-> leaf2 -M(s3)-> leaf3 -M(s0)-> out(0,2)
          node(0,2): leaf0 -M(s1)-> leaf1 -M(s2)-> in(0,2)[x=2] -M(s0)-> leaf0
F=[(1,3)] root(0,3): leaf0 -M(s1)-> out(1,3)[x=1] -M(s3)-> leaf3 -M(s0)-> leaf0
          node(1,3): leaf1 -M(s2)-> leaf2 -M(s3)-> in(1,3)[x=3] -M(s1)-> leaf1
```
Against `A:552-583` (figure `example`, 6-gon, `b1` joined to `a6,a1,a2,a3,b2`, `b2` to `a4,a5,b1`; with `a_k ↔ leaf k-1`, `b1 = root`, `b2 = (3,5)`; M-loop 1 order `c11..c15 = a6,a1,a2,a3,b2`, M-loop 2 `c21..c23 = b1,a4,a5`; the TeX draws `c_{i1}→…→c_{ik}→cycle`): `draw.py` prints `root cycle equals paper M-loop 1 up to rotation: True`, `node (3,5) cycle equals paper M-loop 2 up to rotation: True`. Rule `A:571` (edge `b_{j-1}→b_j` carries `σ_j`, `a_j = b_j`): for consecutive legs the region between them contains the boundary edge `(a_{x-1}, a_x)`, `x` = start of the next range, as above. The figure fixes the cyclic orders; the charges are not printed there (D633).

### (iv) Plan (lines against stop line 1300; `wc -l` at each section commit)
| section | content | lines |
|---|---|---|
| header, §1 | `BAMssOf`, `BAThetaOf`, bridges `rfl` | 55 |
| §2 | `BAslot`, `BAslotNode`, `BAslotStart`, `BAslot_card` | 45 |
| §3 | starts injective per node under `KLIsTSP` (9 leaf/out/in cases) | 140 |
| §4 | generic cyclic successor (`BAKCactus_succ`): bijective, node-preserving, one cycle (rank induction); `BAnextSlot`, `BAMcharge` | 250 |
| commit 1 | ≈ 490 | |
| §5 | `BACactusVal` (edge type `↥F ⊕ BAslot F`), `BAGamma`, check-file pins | 80 |
| §6 | `BACactusVal_congr` 60; `F=∅` closed form 110; `_three` 40 | 210 |
| commit 2 | ≈ 780 | |
| §6 (c) | orientation invariance (`KLgval` flip lemma, `Θ`,`M` symmetric) | 170 |
| instances | `BAslot_card`, `n=3,4` values at `BAMLoop_witM`, one `≠ 0` | 120 |
| **total** | central ≈ 1070 (row K04: 500 / 700 / 1000) | 230 below 1300 |
Risks: §4 (one cycle) and §6 (c); if over 1300 at a boundary, commit and RETURN. For K-c: items (i) and (iii) come from the Lean API and the rule above; (iv) K05 sizes unchanged here.

**Verdicts.** Target 1 PASS; 2 PASS; 3 PASS (rule in arcs above); 4 PASS (`BAGamma` = same formula); 5 (a)(b)(c) PASS (`BACactusVal_three` = `(Kn3sol)`); 6 PASS: (α) 1.9e-15, (β) 1.24e-9. **Overall: PASS.** Candidate `T2367a`: `BAGamma` is total (junk-valued off `TSP n`); the paper's "counterclockwise order" (`A` `m-loop-tsp` item 1) is realised by sorting on first vertices of ranges; charge rule = D633, no new difference.

## (b) Script output, stage 1b (section assembled Sat Oct 10 03:13:41 UTC 2026; each command carries its own run time); worktree `RBM3D-wt/T2367`, branch `t/T2367`, HEAD `a72fdbe`
Scripts (`report_b.sh`, `report_mirror.sh`, `stmts.py`, `insts.py`, `gen_axioms.py`, `compare.py`, `mirror.py`, ...) are in the scratchpad `S` of (a), not in the repository. Commands and outputs below are verbatim; long lines are single lines.

$ date -u: Sat Oct 10 03:11:44 UTC 2026;  for c in $(git rev-list --reverse main..t/T2367): commit time (UTC) and wc -l of KCactus.lean at c
9934c37 02:27:56  wc -l =      488
aa94467 02:31:55  wc -l =      769
91b9e26 02:43:18  wc -l =     1189
48190c8 02:46:52  wc -l =     1194
48b4f07 02:58:16  wc -l =     1194
7824796 03:04:01  wc -l =     1262
a72fdbe 03:09:15  wc -l =     1263
$ lake build RBM3D.BA.KCactus 2>&1 | tail -1
Build completed successfully (3740 jobs).
$ grep -c 'RBM3D/BA/KCactus.lean' <build log> = 0 (warnings or errors in the file);  wc -l =     1263
$ grep -cE 'sorry|admit|native_decide|axiom' KCactus.lean = 0;  grep -cE 'RBM1D|RBM2D' KCactus.lean = 0 (no port)
$ name clash: grep -rnE '(BAMssOf|BAThetaOf|BAslot|BAnextSlot|BAMcharge|BACactusVal|BAGamma|BAKCactus_)' RBM3D outside KCactus.lean: 0 hits
$ full library, run 03:09:15-03:10:13 UTC on the last commit: import RBM3D.BA.KCactus added to RBM3D.lean in the worktree (not committed, restored from HEAD), lake build > full_build.log; grep -E 'axiom audit: |Build completed' full_build.log; grep -c KCactus.lean full_build.log (warnings in the file) = 0:
info: RBM3D.lean:410:0: axiom audit: 10768 theorems, 3165 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4178 jobs).
0 modified files in the worktree
$ git diff --stat main...t/T2367
 RBM3D/BA/KCactus.lean | 1263 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1263 insertions(+)
$ python3 gen_axioms.py; lake env lean axioms.lean  (#print axioms of every public declaration), summarised
53 public declarations
53 declarations with axioms [propext, Classical.choice, Quot.sound]
output lines of another form: 0
$ lake env lean T2367-pin-check.lean (the check file + the auditor's two pin examples): exit 0, lines with error: 0
example (d : ℕ) : Prop := RBM.BA.T2367Check.BATreeRep d (@RBM.BA.BAGamma d)
noncomputable example (d : ℕ) : RBM.BA.T2367Check.BAGammaType d := @RBM.BA.BAGamma d
$ python3 stmts.py RBM3D/BA/KCactus.lean <names>   (definitions in full, theorems cut at :=; BAslot_start_inj etc.: see the #check lines below)
  50: def BAMssOf (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun a b => M σ₁ b a * M σ₂ a b
  70: def BAThetaOf (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ := PropThetaQ (BAMssOf M σ₁ σ₂) t
  54: theorem BAMssOf_BAMsigma (B : Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) : BAMssOf (BAMsigma d L B) σ₁ σ₂ = BAMss d L B σ₁ σ₂ := …
  76: theorem BAThetaOf_BAMsigma (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) : BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ₁ σ₂ = BATheta d L g E m t σ₁ σ₂ := …
 100: abbrev BAslot (F : Finset (Fin n × Fin n)) : Type := Fin n ⊕ ↥F ⊕ ↥F
 113: theorem BAslot_card (F : Finset (Fin n × Fin n)) : Fintype.card (BAslot F) = n + 2 * F.card := …
 120: def BAslotStart (F : Finset (Fin n × Fin n)) : BAslot F → Fin n | Sum.inl v => v | Sum.inr (Sum.inl J) => J.1.1 | Sum.inr (Sum.inr J) => J.1.2
 137: def BAslotNode (F : Finset (Fin n × Fin n)) : BAslot F → Fin n × Fin n | Sum.inl v => KLleafPar F v | Sum.inr (Sum.inl J) => KLnodePar F J.1 | Sum.inr (Sum.inr J) => J.1
 347: def BAnextSlot (F : Finset (Fin n × Fin n)) (s : BAslot F) : BAslot F := BAKCactus_succ (BAslotNode F) (fun x => (BAslotStart F x).val) s
 351: theorem BAslotNode_nextSlot (F : Finset (Fin n × Fin n)) (s : BAslot F) : BAslotNode F (BAnextSlot F s) = BAslotNode F s := …
 357: theorem BAnextSlot_spec (F : Finset (Fin n × Fin n)) (s : BAslot F) : (BAslotStart F s < BAslotStart F (BAnextSlot F s) ∧ ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F s < BAslotStart F x → BAslotStart F (BAnextSlot F s) ≤ BAslotStart F x) ∨ ((∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F x ≤ BAslotStart F s) ∧ ∀ x, BAslotNode F x = BAslotNode F s → BAslotStart F (BAnextSlot F s) ≤ BAslotStart F x) := …
 434: def BAMcharge (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (s : BAslot F) : Bool := σ (BAslotStart F (BAnextSlot F s))
 450: def BACactusValLeafW (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) : Fin n → Matrix (Zd d L) (Zd d L) ℂ := fun v => BAThetaOf M t (σ v) (σ (v + 1))
 457: def BACactusValEdgeW (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) : ↥F ⊕ BAslot F → Matrix (Zd d L) (Zd d L) ℂ := Sum.elim (fun J => (t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) (fun s => M (BAMcharge F σ s))
 462: def BACactusValSrc (F : Finset (Fin n × Fin n)) : ↥F ⊕ BAslot F → BAslot F := Sum.elim (fun J => BAslotIn F J) id
 467: def BACactusValTgt (F : Finset (Fin n × Fin n)) : ↥F ⊕ BAslot F → BAslot F := Sum.elim (fun J => BAslotOut F J) (BAnextSlot F)
 477: def BACactusVal (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ := KLgval d L (Nd := BAslot F) (Lf := Fin n) a (BACactusValLeafW M t σ) (BAslotLeaf F) (BACactusValEdgeW M t F σ) (BACactusValSrc F) (BACactusValTgt F)
 488: def BAGamma (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ := BACactusVal d L M t F σ a
 497: theorem BAGamma_of_mem_TSP (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) {F : Finset (Fin n × Fin n)} (_hF : F ∈ TSP n) (σ : Fin n → Bool) (a : Fin n → Zd d L) : BAGamma d L n M t F σ a = BACactusVal d L M t F σ a := …
 511: theorem BACactusVal_congr (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) {Nd' Ed' : Type*} [Fintype Nd'] [DecidableEq Nd'] [Fintype Ed'] (eN : BAslot F ≃ Nd') (eE : (↥F ⊕ BAslot F) ≃ Ed') {p' : Fin n → Nd'} {E' : Ed' → Matrix (Zd d L) (Zd d L) ℂ} {c' q' : Ed' → Nd'} (hp : ∀ v, p' v = eN (BAslotLeaf F v)) (hE : ∀ e, E' (eE e) = BACactusValEdgeW M t F σ e) (hc : ∀ e, c' (eE e) = eN (BACactusValSrc F e)) (hq : ∀ e, q' (eE e) = eN (BACactusValTgt F e)) : BACactusVal d L M t F σ a = KLgv…
 542: theorem BAnextSlot_empty (hn : 2 ≤ n) (v : Fin n) : BAnextSlot (∅ : Finset (Fin n × Fin n)) (BAslotLeaf ∅ v) = BAslotLeaf ∅ (v + 1) := …
 571: theorem BAMcharge_empty (hn : 2 ≤ n) (σ : Fin n → Bool) (v : Fin n) : BAMcharge (∅ : Finset (Fin n × Fin n)) σ (BAslotLeaf ∅ v) = σ (v + 1) := …
 578: theorem BACactusVal_empty (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) : BACactusVal d L M t (∅ : Finset (Fin n × Fin n)) σ a = ∑ b : Fin n → Zd d L, (∏ v, BAThetaOf M t (σ v) (σ (v + 1)) (a v) (b v)) * ∏ v, M (σ (v + 1)) (b v) (b (v + 1)) := …
 628: theorem BACactusVal_three (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin 3 → Bool) (a : Fin 3 → Zd d L) : BACactusVal d L M t (∅ : Finset (Fin 3 × Fin 3)) σ a = ∑ b₀, ∑ b₁, ∑ b₂, (BAThetaOf M t (σ 0) (σ 1) (a 0) b₀ * BAThetaOf M t (σ 1) (σ 2) (a 1) b₁ * BAThetaOf M t (σ 2) (σ 0) (a 2) b₂) * (M (σ 0) b₂ b₀ * M (σ 1) b₀ b₁ * M (σ 2) b₁ b₂) := …
 664: theorem BACactusVal_orient {M : Bool → Matrix (Zd d L) (Zd d L) ℂ} (hM : ∀ σ, (M σ)ᵀ = M σ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) (o : ↥F ⊕ BAslot F → Bool) : BACactusVal d L M t F σ a = KLgval d L a (BACactusValLeafW M t σ) (BAslotLeaf F) (BACactusValEdgeW M t F σ) (fun e => if o e then BACactusValTgt F e else BACactusValSrc F e) (fun e => if o e then BACactusValSrc F e else BACactusValTgt F e) := …
 712: theorem BACactusVal_sum_zero (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ∑ F ∈ TSP n, BACactusVal d L M 0 F σ a = ∏ v, M (σ (v + 1)) (a v) (a (v + 1)) := …
 736: theorem BACactusVal_sum_zero_BAMLoop (hn : 2 ≤ n) (W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ : Fin n → Bool) (a : Fin n → Zd d L) : (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, BACactusVal d L M 0 F σ a = BAMLoop d L W M (KLloopOf d L σ a) := …
 763: theorem BACactusVal_three_BAMLoop (W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin 3 → Bool) (a : Fin 3 → Zd d L) : (((W : ℂ) ^ d)⁻¹) ^ 2 * BACactusVal d L M t (∅ : Finset (Fin 3 × Fin 3)) σ a = ∑ b₀, ∑ b₁, ∑ b₂, BAThetaOf M t (σ 0) (σ 1) (a 0) b₀ * BAThetaOf M t (σ 1) (σ 2) (a 1) b₁ * BAThetaOf M t (σ 2) (σ 0) (a 2) b₂ * BAMLoop d L W M (KLloopOf d L σ ![b₀, b₁, b₂]) := …
  81: theorem BAThetaOf_isSymm {M : Bool → Matrix (Zd d L) (Zd d L) ℂ} (hM : ∀ σ, (M σ)ᵀ = M σ) (t : ℝ) (σ₁ σ₂ : Bool) : (BAThetaOf M t σ₁ σ₂)ᵀ = BAThetaOf M t σ₁ σ₂ := …
$ lake env lean checks.lean  (#check, lines joined: hypotheses KLIsTSP F, 2 ≤ n of the section variables)
@BAslot_start_inj : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)}, RBM.Loop.KLIsTSP F → 2 ≤ n → ∀ {s t : BAslot F}, BAslotNode F s = BAslotNode F t → BAslotStart F s = BAslotStart F t → s = t
@BAnextSlot_eq_of_above : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)}, RBM.Loop.KLIsTSP F → 2 ≤ n → ∀ {s u : BAslot F}, BAslotNode F u = BAslotNode F s → BAslotStart F s < BAslotStart F u → (∀ (x : BAslot F), BAslotNode F x = BAslotNode F s → BAslotStart F s < BAslotStart F x → BAslotStart F u ≤ BAslotStart F x) → BAnextSlot F s = u
@BAnextSlot_eq_of_wrap : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)}, RBM.Loop.KLIsTSP F → 2 ≤ n → ∀ {s u : BAslot F}, BAslotNode F u = BAslotNode F s → (∀ (x : BAslot F), BAslotNode F x = BAslotNode F s → BAslotStart F x ≤ BAslotStart F s) → (∀ (x : BAslot F), BAslotNode F x = BAslotNode F s → BAslotStart F u ≤ BAslotStart F x) → BAnextSlot F s = u
@BAnextSlot_bijective : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)}, RBM.Loop.KLIsTSP F → 2 ≤ n → Function.Bijective (BAnextSlot F)
@BAnextSlotPerm : {n : ℕ} → [NeZero n] → {F : Finset (Fin n × Fin n)} → RBM.Loop.KLIsTSP F → 2 ≤ n → Equiv.Perm (BAslot F)
@BAnextSlot_orbit : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)}, RBM.Loop.KLIsTSP F → 2 ≤ n → ∀ (s t : BAslot F), BAslotNode F s = BAslotNode F t ↔ ∃ k, (BAnextSlot F)^[k] s = t
@BAnextSlot_sameCycle_iff : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)} (hF : RBM.Loop.KLIsTSP F) (hn : 2 ≤ n) (s t : BAslot F), (BAnextSlotPerm hF hn).SameCycle s t ↔ BAslotNode F s = BAslotNode F t
@BAnextSlot_injective : ∀ {n : ℕ} [inst : NeZero n] {F : Finset (Fin n × Fin n)}, RBM.Loop.KLIsTSP F → 2 ≤ n → Function.Injective (BAnextSlot F)
$ python3 insts.py RBM3D/BA/KCactus.lean 150   (the compiled instances, namespace KCactusInst; statements up to :=)
 795: example (F : Finset (Fin 4 × Fin 4)) : Fintype (BAslot F)
 797: example (F : Finset (Fin 4 × Fin 4)) : DecidableEq (BAslot F)
 800: example : Fintype.card (BAslot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4))) = 6
 810: example : ∑ F ∈ TSP 3, BACactusVal 1 3 BAMLoop_witM 0 F ![true, true, false] ![![0], ![1], ![2]] = 15
 820: example : BACactusVal 1 3 BAMLoop_witM 0 (∅ : Finset (Fin 4 × Fin 4)) ![true, true, false, true] ![![0], ![1], ![2], ![1]] = 10
 833: example : BAGamma 1 3 4 BAMLoop_witM 0 {((0 : Fin 4), (2 : Fin 4))} ![true, true, false, true] ![![0], ![1], ![2], ![1]] = 0
 837: example : BAGamma 1 3 4 BAMLoop_witM 0 {((1 : Fin 4), (3 : Fin 4))} ![true, true, false, true] ![![0], ![1], ![2], ![1]] = 0
 841: example : ∑ F ∈ TSP 4, BAGamma 1 3 4 BAMLoop_witM 0 F ![true, true, false, true] ![![0], ![1], ![2], ![1]] = 10
 930: example : BAnextSlot BAKCactus_F02set (BAslotOut _ ⟨_, BAKCactus_F02mem⟩) = BAslotLeaf _ 2 ∧ BAnextSlot BAKCactus_F02set (BAslotLeaf _ 2) = BAslotLeaf…
 942: example (σ : Fin 4 → Bool) : BAMcharge BAKCactus_F02set σ (BAslotOut _ ⟨_, BAKCactus_F02mem⟩) = σ 2 ∧ BAMcharge BAKCactus_F02set σ (BAslotLeaf _ 2) = …
 954: example : (∃ k : ℕ, (BAnextSlot BAKCactus_F02set)^[k] (BAslotLeaf _ 0) = BAslotIn _ ⟨_, BAKCactus_F02mem⟩) ∧ ¬ ∃ k : ℕ, (BAnextSlot BAKCactus_F02set)^…
 963: example : (BAnextSlotPerm BAKCactus_F02 (by norm_num : 2 ≤ 4)).SameCycle (BAslotLeaf _ 0) (BAslotIn _ ⟨_, BAKCactus_F02mem⟩) ∧ ¬ (BAnextSlotPerm BAKCa…
 972: example : Function.Bijective (BAnextSlot BAKCactus_F02set)
 974: example : ∀ s t : BAslot BAKCactus_F02set, BAslotNode _ s = BAslotNode _ t → BAslotStart _ s = BAslotStart _ t → s = t
1048: example (σ : Fin 4 → Bool) : (BAnextSlot BAKCactus_F13set (BAslotLeaf _ 0) = BAslotOut _ ⟨_, BAKCactus_F13mem⟩ ∧ BAnextSlot BAKCactus_F13set (BAslotOu…
1064: example : Function.Bijective (BAnextSlot BAKCactus_F13set)
1070: example : BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false = BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false
1073: example : BAMssOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) true false = BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false
1087: example : (BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) true false)ᵀ = BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 /…
1091: example : (BAMssOf BAMLoop_witM true false)ᵀ = BAMssOf BAMLoop_witM true false
1095: example : BACactusVal 3 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) BAKCactus_F02set ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], …
1105: example : BACactusVal 1 3 BAMLoop_witM (1 / 10) BAKCactus_F13set ![true, true, false, true] ![![0], ![1], ![2], ![1]] = KLgval 1 3 ![![0], ![1], ![2],…
1114: example : let eN : BAslot BAKCactus_F02set ≃ Fin 6
1128: example : BACactusVal 1 3 BAMLoop_witM (1 / 10) (∅ : Finset (Fin 4 × Fin 4)) ![true, true, false, true] ![![0], ![1], ![2], ![1]] = ∑ b : Fin 4 → Zd 1…
1135: example : BACactusVal 1 3 BAMLoop_witM (1 / 10) (∅ : Finset (Fin 3 × Fin 3)) ![true, true, false] ![![0], ![1], ![2]] = ∑ b₀, ∑ b₁, ∑ b₂, (BAThetaOf B…
1144: example : (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ 2 * BACactusVal 1 3 BAMLoop_witM (1 / 10) (∅ : Finset (Fin 3 × Fin 3)) ![true, true, false] ![![0], ![1], ![2]] = ∑ …
1151: example : BAGamma 1 3 3 BAMLoop_witM (1 / 10) ∅ ![true, true, false] ![![0], ![1], ![2]] = BACactusVal 1 3 BAMLoop_witM (1 / 10) ∅ ![true, true, false…
1157: example : BAnextSlot (∅ : Finset (Fin 4 × Fin 4)) (BAslotLeaf _ 3) = BAslotLeaf _ 0
1160: example : BAnextSlot (∅ : Finset (Fin 4 × Fin 4)) (BAslotLeaf _ 1) = BAslotLeaf _ 2
1163: example (σ : Fin 4 → Bool) : BAMcharge (∅ : Finset (Fin 4 × Fin 4)) σ (BAslotLeaf _ 3) = σ 0
1168: example : BAslotNode BAKCactus_F02set (BAnextSlot BAKCactus_F02set (BAslotLeaf _ 1)) = KLleafPar BAKCactus_F02set 1
1171: example : BAslotStart _ (BAslotLeaf BAKCactus_F02set 1) < BAslotStart _ (BAnextSlot BAKCactus_F02set (BAslotLeaf _ 1))
1178: example : BAslotNode BAKCactus_F02set (BAslotLeaf _ 3) ∈ KLnodes BAKCactus_F02set
1180: example : Function.Injective (BAnextSlot BAKCactus_F13set)
1183: example : BAThetaOf BAMLoop_witM 0 true false = 1
1185: example : BACactusVal 1 3 BAMLoop_witM 0 (∅ : Finset (Fin 3 × Fin 3)) ![true, true, false] ![![0], ![1], ![2]] = 15
1253: example : BACactusVal 1 3 BAKCactus_Msh (1 / 2) BAKCactus_F02set ![true, true, false, true] ![![0], ![1], ![0], ![1]] = 1 / 2
1256: example : BAGamma 1 3 4 BAKCactus_Msh (1 / 2) BAKCactus_F02set ![true, true, false, true] ![![0], ![1], ![0], ![1]] ≠ 0
38 examples

$ python3 compare.py  (run 03:09:15 to 03:11:36 UTC, after the last commit; K00 convention, RK4 600 steps). Columns: n, #trees, (alpha) max|mirror-mgraph|, fixed-a vs open-a, (beta) max|sum_F mirror - K_ODE|, max|K|, worst sigma
--- q=5 g=0.8 E=0.3 t=0.5 (d=1, W=1), RK4 steps=600; m=0.036646+0.699866j
 3       1  0.00e+00   2.78e-17   6.08e-14   6.42e-01   ++-
 4       3  5.56e-17   2.79e-17   9.32e-13   7.60e-01   -+-+
 5      11  1.67e-16   3.18e-17   1.73e-12   7.34e-01   +--+-
--- q=4 g=0.6 E=-0.4 t=0.7 (d=1, W=1), RK4 steps=600; m=0.157685+0.783233j
 3       1  0.00e+00   2.22e-16   8.21e-12   1.83e+00   ++-
 4       3  8.88e-16   4.45e-16   2.11e-10   3.81e+00   -+-+
 5      11  1.81e-15   1.78e-15   6.76e-10   5.96e+00   --+-+
--- q=3 g=1.1 E=0.0 t=0.6 (d=1, W=1), RK4 steps=600; m=-0.476392+0.555796j
 3       1  0.00e+00   0.00e+00   1.84e-12   1.45e+00   ++-
 4       3  4.97e-16   2.22e-16   4.54e-11   2.98e+00   +-+-
 5      11  6.28e-16   4.58e-16   1.58e-10   5.07e+00   +--+-
 6      45  1.91e-15   8.88e-16   1.24e-09   1.12e+01   +-+-+-
elapsed 140s
$ python3 draw.py  (slot cycles of mirror.py; M(sig_x) on the arrow s -> next s)
n=4, F=[]: #slots=4 = n+2|F| = 4
  node (0, 3): leaf0[start 0] --M(sig_1)--> leaf1[start 1] --M(sig_2)--> leaf2[start 2] --M(sig_3)--> leaf3[start 3] --M(sig_0)--> leaf0
n=4, F=[(0, 2)]: #slots=6 = n+2|F| = 6
  node (0, 3): out(0, 2)[start 0] --M(sig_2)--> leaf2[start 2] --M(sig_3)--> leaf3[start 3] --M(sig_0)--> out(0, 2)
  node (0, 2): leaf0[start 0] --M(sig_1)--> leaf1[start 1] --M(sig_2)--> in(0, 2)[start 2] --M(sig_0)--> leaf0
n=4, F=[(1, 3)]: #slots=6 = n+2|F| = 6
  node (0, 3): leaf0[start 0] --M(sig_1)--> out(1, 3)[start 1] --M(sig_3)--> leaf3[start 3] --M(sig_0)--> leaf0
  node (1, 3): leaf1[start 1] --M(sig_2)--> leaf2[start 2] --M(sig_3)--> in(1, 3)[start 3] --M(sig_1)--> leaf1
  root cycle equals paper M-loop 1 up to rotation: True
  node (3,5) cycle equals paper M-loop 2 up to rotation: True
$ python3 api.py | grep -E "n=6|5c|5a|Theta"  (relabelling 5a, closed form 5b, orientation 5c, symmetry)
BAMss bridge/symmetry data: M(+) symmetric: True  M(-)=conj M(+) symmetric: True  Theta symmetric (all sigma pairs): True
(5b) n=6: max|closed form - cactus value(F=empty)| so far = 0.00e+00
(5c) n=3..6, all F, random sigma/a, random per-edge orientation flips: max|diff| = 0.00e+00
(5a) random slot relabelling: max|diff| = 1.14e-16
$ python3 instance.py | grep -E "Gamma|equal"  (exact Fractions, brute force over slot labels; d=1, L=3, M=BAMLoop_witM)
   t=0: Gamma = 15
   t=1/10: Gamma = 104425/6292
   closed form (Kn3sol) at t=1/10: 104425/6292  equals cactus value: True
   F=[]        #slots=4  Gamma = 21025500/1859  (~11310.1)  nonzero: True
   F=[(0, 2)]  #slots=6  Gamma = 2622270125/1799512  (~1457.21)  nonzero: True
   F=[(1, 3)]  #slots=6  Gamma = 5602354125/531674  (~10537.2)  nonzero: True
   sum_F Gamma_F(t=0) = 10  prod_i M(sig_i)_{a_{(i+3)%4} a_i} = 10  equal: True
$ diff <(grep -v "^ n  #trees\|elapsed" compare_out.txt) <(grep -v "^ n  #trees\|elapsed" compare_out_final.txt)   (1a table against this run)
no difference (exit 0)

**Narrative** (sources: the file, the script output above).
1. `RBM3D/BA/KCactus.lean` (new, 1263 lines; `wc -l` at the seven commits 488, 769, 1189, 1194, 1194, 1262, 1263; stop line 1300 never exceeded) defines in `RBM.BA`: `BAMssOf`, `BAThetaOf` (`rfl` bridges to `BAMss`, `BATheta` at `BAMsigma (BAMB ..)`); the slots `BAslot F := Fin n ⊕ ↥F ⊕ ↥F` (leaf `v`; chord `J` seen from `KLnodePar F J` = `BAslotOut`; chord `J` seen from `J` = `BAslotIn`), `BAslotStart` (first vertex of the vertex range: `v`, `J.1`, `J.2`), `BAslotNode`; `BAnextSlot`; `BAMcharge F σ s := σ (BAslotStart F (BAnextSlot F s))` (D633); `BACactusVal` = `KLgval` with `Nd = BAslot F`, `Lf = Fin n`, `Ed = ↥F ⊕ BAslot F` (leaf `v`: `Θ^{(σ_v,σ_{v+1})}`; chord `(i,j)`: `tΘ^{(σ_i,σ_j)}` from `in J` to `out J`; `M`-edge `s`: `M(BAMcharge F σ s)` from `s` to `BAnextSlot F s`); `BAGamma` = the same formula for every `F`, of type `BAGammaType d` (pin check exit 0, with `noncomputable example` for the second pin example: `BAGamma` depends on the noncomputable `KLgval`, `BAnextSlot`).
2. Hypotheses: `KLIsTSP F` and `2 ≤ n` (implied by `3 ≤ n`) only, for `BAslot_start_inj` and the `BAnextSlot` facts for general `F` (`_eq_of_above`, `_eq_of_wrap`, `_injective`, `_bijective`, `BAnextSlotPerm`, `_orbit`, `_sameCycle_iff`); `BAslotNode_nextSlot`, `BAnextSlot_spec`, `BAslot_card` need none (`BAslot_card` is stronger than the ticket's "under `KLIsTSP F`"); the `F = ∅` facts need `2 ≤ n` only. No amend.
3. `BAnextSlot` is a choice for every `F`: a private generic successor (next larger key in the fibre of `node`, else the smallest; exists by `Finset.exists_min_image`, unique when keys are injective, injective, one orbit per fibre by strong induction on `key t - key s`). Keys are injective on each node by `BAslot_start_inj` (9 constructor cases from `KLleafPar_spec`, `KLnodePar_spec`, `KLnodePar_arcLe`, `KLnot_arcLe_nodePar_self`, `KLwholeP_not_mem`). Targets of 3: permutation `BAnextSlot_bijective`/`BAnextSlotPerm`, node preserved `BAslotNode_nextSlot`, one cycle per node `BAnextSlot_orbit`, `BAnextSlot_sameCycle_iff` (Mathlib `SameCycle`).
4. API 5 (a) `BACactusVal_congr` (slot and edge relabelling, from `KLgval_congr`); 5 (b) `BAnextSlot_empty`, `BAMcharge_empty`, `BACactusVal_empty`, `BACactusVal_three` = `(Kn3sol)` (`1_2:1176`): `∑_{b₀b₁b₂} Θ^{(σ₀σ₁)}(a₀,b₀) Θ^{(σ₁σ₂)}(a₁,b₁) Θ^{(σ₂σ₀)}(a₂,b₂) · M(σ₀)_{b₂b₀} M(σ₁)_{b₀b₁} M(σ₂)_{b₁b₂}`, the last factor being `∏_i M(σ_i)_{b_{i-1}b_i} = W^{2d} 𝓜^{(3)}_{σ,b}` of `(eq:KMloop)` (`1_2:1003`, 0-indexed), and `BACactusVal_three_BAMLoop`: `W^{-2d} Γ(∅) = ∑_b ΘΘΘ · BAMLoop(σ,b)`; 5 (c) `BACactusVal_orient` (any set of edges reversed when `∀σ, (M σ)ᵀ = M σ`; `BAThetaOf_isSymm`).
5. Beyond the ticket (same file): `BACactusVal_sum_zero`, `BACactusVal_sum_zero_BAMLoop`: at `t = 0` only `F = ∅` survives and `W^{-d(n-1)} ∑_{F ∈ TSP n} Γ_F = BAMLoop(σ,a)` for every `n ≥ 2`: the charge rule agrees with K00's `BAMLoop_apply` (`σ_i` on `(a_{i-1}, a_i)`), checked in Lean (`BATreeRep` at `t = 0`).
6. Instances (section 7, 38 `example`s): `d = 1, L = 3, M = BAMLoop_witM`: `n = 3`, `t = 0`: tree sum `= 15 = BAMLoop_witness`; `n = 4`, `t = 0`: `Γ(∅) = 10 ≠ 0`, the two diagonal trees `= 0` (the chord carries `0·Θ`), sum over `TSP 4` `= 10`; slot cycles and the six charges of `{(0,2)}` and `{(1,3)}` computed from the definitions (computable model + `decide`), equal to the `draw.py` lines; `BAslot_card = 6`; bijectivity, orbits, `SameCycle` (two cycles) at both trees; the other API theorems at `t = 1/10`, `1/2` and at the flow point `P` of `(d, L) = (3, 4)` (`BAThetaOf_BAMsigma`, `BACactusVal_orient`). A chord tree with `t ≠ 0` and a nonzero value: the directed datum `M(σ)_{xy} = 1(y = x+1)` on `Z_3` (`M^{(σ₁σ₂)} = 0`, `Θ ≡ 1`, not symmetric, not BA data), `F = {(0,2)}`, `n = 4`, `a = (0,1,0,1)`, `t = 1/2`: `BACactusVal = 1/2`, so `BAGamma ≠ 0` (unique solution `b_out = b_in = 2` of the six directed `M`-edges and the chord, `decide` over the 729 labellings). Not shown in Lean: a nonzero chord-tree value for the K00 witness at `t ≠ 0` (exact `Fraction` values at `t = 1/10`, `n = 4` from `instance.py`: `21025500/1859`, `2622270125/1799512`, `5602354125/531674`).
7. Mirror (target 6; `mirror.py` was written in 1a from the ticket text and mirrors the Lean definitions of targets 2-4, compared by reading with the final file; it is checked against `mgraph.gamma_value` and the ODE): (α) max over all σ, a, trees, `n ≤ 6` `1.91e-15` ≤ 1e-12; (β) `6.76e-10` (`n ≤ 5`), `1.24e-9` (`n = 6`) ≤ 1e-8; the table equals the 1a table (`diff` empty); the stop line of the ticket is not triggered.

## (c) Verified Mathlib names (`#check`, 0 errors, scratch `names.lean`; all used in `KCactus.lean`)
`Matrix.nonsing_inv_eq_ringInverse`, `Matrix.transpose_nonsing_inv`, `Matrix.{transpose_sub,transpose_one,transpose_smul,transpose_apply,of_apply,one_apply,smul_apply,zero_apply,cons_val_zero,cons_val_one,cons_val_two,head_cons,tail_cons}`, `Finite.injective_iff_bijective`, `Fintype.ofFinite`, `Fintype.{sum_unique,prod_unique,sum_prod_type,prod_sum_type,prod_equiv,card_sum,card_coe,card_fin,equivFinOfCardEq}`, `Finset.{exists_min_image,exists_max_image,mem_filter,mem_univ,sum_congr,prod_congr,sum_eq_single,sum_eq_zero,prod_eq_zero,prod_boole,sum_ite,sum_const,sum_const_zero,mul_sum,prod_range_succ,nonempty_iff_ne_empty,notMem_empty,mem_singleton,mem_singleton_self}`,
`Function.{iterate_succ_apply,iterate_add_apply,iterate_one,ne_iff}`, `Equiv.{sumEmpty,emptySum,addRight,ofBijective}`, `Equiv.Perm.SameCycle.exists_nat_pow_eq`, `Equiv.Perm.iterate_eq_pow`, `zpow_natCast`, `Fin.{consEquiv,val_add,val_one',prod_univ_three,prod_univ_four,prod_univ_eq_prod_range,le_def,lt_def,val_zero}`, `Nat.{strong_induction_on,mod_eq_of_lt,add_mod_right,mod_self}`, `List.{getD_eq_getElem?_getD,ofFn_succ}`, `Classical.{choose,choose_spec}`, `lt_trichotomy`, `lt_or_gt_of_ne`, `forall_true_left`, `one_smul`, `smul_eq_mul`.
Verified absent: `Finset.not_mem_empty` (now `Finset.notMem_empty`), `Equiv.piFinSucc` (use `Fin.consEquiv`); `push_neg` is deprecated (use `push Not`).

## (d) Open issues and paper-delta candidates
- `T2367a`: `BAGamma` is total and junk-valued off `TSP n` (paper: defined on `Γ ∈ TSP(P_a)` only); `BATreeRep` uses it on `TSP n` only (`BAGamma_of_mem_TSP`).
- `T2367b`: the planar `M`-graph of `A:380-598` is realised combinatorially: slots `Fin n ⊕ ↥F ⊕ ↥F`; the "counterclockwise order" of `m-loop-tsp` item 1 is the order by `BAslotStart`; chords are oriented child to parent and `M`-edges `s → BAnextSlot s` (the paper does not fix an orientation for the chord value `(tSΘ)(b₁,b₂)`, `A:561-563`; its `M`-loops are oriented, `A:567-575`); `BACactusVal_orient` shows the orientation is immaterial for symmetric `M`. The charge rule is D633 verbatim (`σ_x`, `x` the first vertex of the next range): no new candidate for it; D634 (`n ≥ 3`) unchanged.
- K-e: `BATreeRep` is stated on `BAKsol` (`0` when there is no solution, `BA/FlowPins.lean:281-286`): proving it (K05b) needs the cactus sum to solve `IsKLoopS`; K04 proves nothing about `BAKsol`.
- K-c (i), the compiled API: slots `BAslot`, `BAslotLeaf/Out/In`, `BAslotStart`, `BAslotNode`, `BAslot_card`, `BAslot_start_inj`; `BAnextSlot` (`_spec`, `_eq_of_above`, `_eq_of_wrap`, `_injective`, `_bijective`, `BAnextSlotPerm`, `_orbit`, `_sameCycle_iff`, `_empty`), `BAslotNode_nextSlot`; `BAMcharge`, `BAMcharge_empty`; `BACactusVal` with `BACactusValLeafW/EdgeW/Src/Tgt`, `BAGamma`; `BACactusVal_congr/_empty/_three/_orient/_zero_of_nonempty/_empty_zero/_sum_zero/_sum_zero_BAMLoop/_three_BAMLoop`; `BAMssOf`, `BAThetaOf` (`_BAMsigma`, `_isSymm`, `BAThetaOf_zero`).
- K-c (iii), the rule in arcs: the slots of a node, ordered by the first vertex `x(s)` of their vertex range (`v` for the leaf `v`; `i` for the chord `(i,j)` seen from its parent node, `j` seen from `(i,j)`), form one cycle; the `M`-edge `s → s'` (`s'` next, last to first) carries `σ_{x(s')}`, the boundary edge `(a_{x-1}, a_x)` ending at the first vertex of the range of `s'`. Re-checked against K00's `BAMLoop`: Lean `BACactusVal_sum_zero_BAMLoop` (all `n ≥ 2`, `t = 0`), the compiled cycles of `{(0,2)}`, `{(1,3)}`, and the mirror (α), (β).
- Limits: no Lean value of a chord tree at `t ≠ 0` for the K00 witness or BA data (item 6: only the directed datum); `BAnextSlot` is noncomputable (a choice), so instances use a computable model of the tree and `decide` (`set_option maxRecDepth 100000` for the 729-labelling count).
