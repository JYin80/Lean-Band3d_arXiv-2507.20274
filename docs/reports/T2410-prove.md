Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct 11 07:57:54 UTC 2026

Notation: Γ a normal BA graph with counters (n_S, n_W, n_A, n_M), ord = n_S + 2(n_W − n_A); p.1 = Ǧ_{xy}, q.1 = Ǧ_{y'x}, q.2 = the other solid edges of Γ, [v] = the atom of v, κ = number of internal atoms lost
when [y], [y'] are merged (κ = 0 if [y] = [y'] or both external, else 1), κ' the same for [x], [y]. Term labels: gg2#1..#5 are the five leading items of `gg2`, gg2D the derivative items; gg4#1, gg4#2, gg4D likewise.

### (i) Exponent table

| row | value | constraint | slack |
|---|---|---|---|
| D402 coefficient | W − 1 = M⁺S⁺, S⁺ = S·W, W = (1 − M⁺S)⁻¹ | identity used for the first two sums and for splitting W = 1 + (W − 1) in the third sum (`ba_W_sub_one`, `BAGGExp.lean:51`) | residual 5.6e-17, 1.2e-15, 4.4e-16 at g0 = 0, 1/64, 1 (inst.out below) |
| data window | 0 ≤ t < 1, L ≥ 3, BASelf d L g0 E m, Im m > 0 | hypotheses of `baGGGamma_holds` (`BAGGExp.lean:358`) and of `BAexpFrameE` | max row sum of the absolute values of M⁺S = 0.500 < 1 at t = 1/2 (slack 0.5; inst.out) |
| frame hypotheses | p ∈ lwSplit Γ.solid, q ∈ lwSplit p.2, σ = circ = true for both, p.1.src = q.1.dst | second conjunct of `BAexpFrameE` (T2395 probe :244-251); no hypothesis on x, y, y' being distinct | in the random draws x, y, y' are drawn independently from all vertices, so coincidences are included |
| gg2#1 (first sum, W−1) | Δn_S = −2, Δn_W = +1, Δn_A = −κ, Δord(T°) = 2κ ∈ {0, 2} | needs ≥ 0 | = 0 iff [y] = [y'] or both external; n_Ext falls by 1 if both external and distinct |
| gg2#2, gg2#3 (second sum) | Δn_S = −1, Δn_W = +1, Δn_A = 0, Δord = +1 | ≥ 0 | 1; no uncircled edge, so ordG = ord |
| gg2#4, gg2#5 (third sum, W = 1) | Δn_S = +1, Δn_W = +1, Δn_A = +1, Δord(T°) = +1 | ≥ 0 | #4 has 1 uncircled edge G_{αy}: members Δord ∈ {1, 2κ'(x,y)} (0 iff κ' = 0); #5 has 2: members ⊂ {1,2,3}, min 1 |
| gg2D (derivative, per r ∈ lwSplit q.2) | Δn_S = +1, Δn_W = +1, Δn_A = +1, Δord(T°) = +1 | ≥ 0 | 3 uncircled edges: member Δord ∈ {0,…,4}; 0 attained (sample) |
| gg4#1, gg4#2 (third sum, W−1) | Δn_S = +1, Δn_W = +2, Δn_A = +2, Δord(T°) = +1 | ≥ 0 | members Δord ⊂ {1,2,3}, min 1 (never 0 in the sample) |
| gg4D | Δn_S = +1, Δn_W = +2, Δn_A = +2, Δord(T°) = +1 | ≥ 0 | members Δord ∈ {1,…,4}, min 1 |
| BAstepMono counters | for every partition member of every term: ord ≥ ord Γ, n_M ≤ n_M(Γ), n_A − n_W ≤ (n_A − n_W)(Γ), n_Ext ≤ n_Ext(Γ) (members have all solid edges circled by construction) | pin `BAstepMono` (T2395 probe :269) | 0 violations in 4000 random Γ (gg.out) |

Which terms keep or gain the order (all verified on the script's sample, not only at the instance):
- gg2#1 (first sum) is the only term whose raw counters are not a constant offset: (n_S − 2, n_W + 1) are fixed, n_A and n_M depend on the atoms of y, y'. It keeps the order of Γ iff κ = 0 (this includes the instance baGGLhs, where y, y' are external), otherwise it gains 2. This is the (eq:GGraisesord) obstruction of the ticket (T2398b); the Lean form is `ord Γ ≤ ordG T`, not strict.
- gg2#2..#5, gg2D, gg4#1, gg4#2, gg4D: raw order exactly ord Γ + 1. Counters, constant offsets: gg2#2/#3 (−1, +1, 0), gg2#4/#5/gg2D (+1, +1, +1), gg4 (+1, +2, +2).
- After the partition G = Ǧ + M: gg2#4 and gg2D can again keep the order (member with κ' = 0 resp. the equal-order members of the derivative term), gg2#2/#3 and all gg4 terms have ordG ≥ ord Γ + 1.
- The term lists `gg2`, `gg4` as printed in T2395 probe :129-148 are correct against the three sums of (B.20) with the D402 coefficient (script A: 3.0e-15 relative error, all 9 terms at a rest edge r = Ǧ_{ab}; no change needed). The script tests a blue (σ = true) rest edge only; the red branch of `owxDE` is the merged one.
- No external input and no smallness of g or of ‖M − m₀I‖ is used: only BASelf, 0 ≤ t < 1, L ≥ 3 (C1, L5).

### (ii) One concrete nondegenerate instance

Data: d = 3, L = 3, W = 1 (27 sites), E = 0, t = 1/2, g0 = 0, m = i for the instance dischargeable in Lean (`baSelf_zero`, `BAExpand.lean:865`, used by the instances `BAGGExpInst`, `BAGGExp.lean:470-492`); the same hypotheses hold numerically with g0 = 1/64 and 1 (M non-scalar). Graph Γ = baGGLhs (`BAVocab.lean:1181`: external y' = inl 0, y = inl 1, internal x = inr 0, solid [Ǧ_{y'x}, Ǧ_{xy}]); p = (Ǧ_{xy}, [Ǧ_{y'x}]), q = (Ǧ_{y'x}, []), p.1.src = q.1.dst = inr 0, both blue and circled; ℓe = (e₁, e₀) for (y', y), x summed. Then gg2 has 5 terms, gg4 has 2 terms (q.2 = [], no derivative terms).
No external hypothesis occurs (`baGGGamma_holds` is merged), so no limit computation is needed.

Command 1 (pointwise identity Σ terms = BAGGGammaR, counters, partition orders; scratch script, no Lean):
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2410 && python3 -I gg.py 4000`
```
A: max rel. err. sum(terms) vs BAGGGammaR over 20 seeds, #terms: 3.0297513982347633e-15 9
('gg2', '3a') raw dord [1] dnS [1] dnW [1] dnA [1] | partition dord [0, 1, 2] min-per-term [0, 1]
('gg2', '3b') raw dord [1] dnS [1] dnW [1] dnA [1] | partition dord [1, 2, 3] min-per-term [1]
('gg2', 'Dq') raw dord [1] dnS [1] dnW [1] dnA [1] | partition dord [0, 1, 2, 3, 4] min-per-term [0, 1]
('gg2', 'S2a') raw dord [1] dnS [-1] dnW [1] dnA [0] | partition dord [1] min-per-term [1]
('gg2', 'S2b') raw dord [1] dnS [-1] dnW [1] dnA [0] | partition dord [1] min-per-term [1]
('gg2', 'T1') raw dord [0, 2] dnS [-2] dnW [1] dnA [-1, 0] | partition dord [0, 2] min-per-term [0, 2]
('gg4', '3a') raw dord [1] dnS [1] dnW [2] dnA [2] | partition dord [1, 2] min-per-term [1]
('gg4', '3b') raw dord [1] dnS [1] dnW [2] dnA [2] | partition dord [1, 2, 3] min-per-term [1]
('gg4', 'Dq') raw dord [1] dnS [1] dnW [2] dnA [2] | partition dord [1, 2, 3, 4] min-per-term [1]
BAstepMono violations on partition members: 0 ; kappa-formula errors for gg2 T1: 0
baGGLhs counters (nS,nW,nA,nM,nExt) = (2, 0, 1, 1, 2)  ord = 0
  gg2 T1  counters (nS,nW,nA,nM,nExt)=(0, 1, 1, 0, 1)  ord T - ord Gamma = 0  partition members ord - ord Gamma = [0]
  gg2 S2a counters (nS,nW,nA,nM,nExt)=(1, 1, 1, 0, 2)  ord T - ord Gamma = 1  partition members ord - ord Gamma = [1]
  gg2 S2b counters (nS,nW,nA,nM,nExt)=(1, 1, 1, 0, 2)  ord T - ord Gamma = 1  partition members ord - ord Gamma = [1]
  gg2 3a  counters (nS,nW,nA,nM,nExt)=(3, 1, 2, 1, 2)  ord T - ord Gamma = 1  partition members ord - ord Gamma = [1, 2]
  gg2 3b  counters (nS,nW,nA,nM,nExt)=(3, 1, 2, 1, 2)  ord T - ord Gamma = 1  partition members ord - ord Gamma = [1, 2, 2, 1]
  gg4 3a  counters (nS,nW,nA,nM,nExt)=(3, 2, 3, 1, 2)  ord T - ord Gamma = 1  partition members ord - ord Gamma = [1, 2]
  gg4 3b  counters (nS,nW,nA,nM,nExt)=(3, 2, 3, 1, 2)  ord T - ord Gamma = 1  partition members ord - ord Gamma = [1, 2, 2, 1]
gg2 item 4: members' Delta ord == {1, 2 kappa'(x,y)} failures: 0 of 3000 ; cases with kappa'=0 (order kept): 1772
```
Command 2 (BASelf, Im m > 0, W − 1 = M⁺S⁺ at the data, S = t·I since S^(B)(0) = I and W = 1):
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2410 && python3 -I inst.py`
```
g0=0.0      m=0.000000+1.000000j  Im m=1.0000>0  |BASelf residual|=0.0e+00  max|M_xy| offdiag=0.000e+00  row-sum |M+ S|=0.500<1  |W-1-M+S+|max=5.6e-17
g0=0.015625 m=-0.000011+0.999269j  Im m=0.9993>0  |BASelf residual|=3.3e-16  max|M_xy| offdiag=1.559e-02  row-sum |M+ S|=0.500<1  |W-1-M+S+|max=1.2e-15
g0=1.0      m=-0.009172+0.686025j  Im m=0.6860>0  |BASelf residual|=2.2e-16  max|M_xy| offdiag=1.571e-01  row-sum |M+ S|=0.500<1  |W-1-M+S+|max=4.4e-16
```
Reading of command 1: baGGLhs counters (2,0,1,1) and gg2#1 counters (0,1,1,0) agree with the merged `baGGLhs_counters`, `baGGT1_counters` (`BAVocab.lean:1237,1245`); gg2#1 has ord T − ord Γ = 0 with n_Ext 2 → 1; every other term has Δord = +1 and partition members ≥ +1.
Per target: instance of `gg2`/`gg4` at baGGLhs: the 7 terms above; `baExpFrame_gg` and `baExpFrameE_holds 3`: the data of Command 2 with this Γ, p, q, from `baGGGamma_holds 3` at every labelling; counters: the table rows.

### Verdicts
- Target 1 (term lists gg2, gg4): PASS (correct against (B.20) with D402; no change).
- Target 2 (baExpFrame_gg): PASS (hypotheses satisfiable at the instance; the pointwise assembly equals BAGGGammaR).
- Target 3 (BAexpFrameE, baExpFrameE_holds): PASS.
- Target 4 (counters, order): PASS, with the exact statement of which terms keep or gain the order given above; gg2#1 has no constant n_A offset.
- Targets 5, 6: PASS (uniform BA facts only; the instance above).

## (b) Script output (stage 1b) — Sun Oct 11 08:42:00 UTC 2026
Line count against the stop line: `wc -l RBM3D/Graph/BAGGOp.lean` = 1852 of 2000 (section commits at 845, 1512, 1725, 1852 lines). Branch t/T2410 at b763c11 (`git log main..t/T2410`: 5 commits); `git diff --stat main...t/T2410`: `RBM3D.lean | 1 +`, `RBM3D/Graph/BAGGOp.lean | 1852 +`. No port from RBM1D/RBM2D (`grep -c 'RBM1D\|RBM2D' RBM3D/Graph/BAGGOp.lean` = 0).
```
$ lake build RBM3D.Graph.BAGGOp 2>&1 | grep -E "BAGGOp|Build completed|error"
Build completed successfully (3785 jobs).
$ lake build 2>&1 | tail -2     # full library: RBM3D.lean imports the module, `#assert_rbm_axioms` runs
non-vacuity certificates: 0 of 91 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4222 jobs).
$ lake env lean docs/tickets/checks/T2410-check.lean; echo exit $?   -> exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom " RBM3D/Graph/BAGGOp.lean | wc -l   -> 0
$ lake env lean axioms.lean | sed 's/^.*depends on axioms: //' | sort | uniq -c     # 18 `#print axioms` lines
     18 [propext, Classical.choice, Quot.sound]
  (BAGraph.gg2, gg4, BAGGOp_gg2_eq, BAGGOp_gg4_eq, baExpFrame_gg, BAexpFrameE, baExpFrameE_holds, BAGGOp_kappa, BAGGOp_nExt, BAGGOp_Mono,
   gg_counters, gg_raw, gg_scalingOrderG, gg_mono, BAGGOpInst.lists_baGGLhs, .lists_baGG3, .A1_keeps, .A1_gains)
$ python3 -I vdiff.py <git show t/T2395:RBM3D/Probe/T2395Pins.lean> RBM3D/Graph/BAGGOp.lean      # whitespace-normalised
gg2+gg4 probe lines: 22 mine lines: 22 identical: True
BAexpFrameE probe lines: 8 mine lines: 8 identical: True
nExt body identical to probe BAGraph.nExt: True      # `BAGGOp_nExt` is the probe's `BAGraph.nExt` (`:33`)
$ python3 -I extract.py RBM3D/Graph/BAGGOp.lean baExpFrame_gg baExpFrameE_holds gg_counters gg_raw gg_scalingOrderG gg_mono   # statements, one line each
theorem baExpFrame_gg (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = true → p.1.circ = true → q.1.σ = true → q.1.circ = true → p.1.src = q.1.dst → ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, baSum (Γ.gg2 p q) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.gg4 p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
theorem baExpFrameE_holds (d : ℕ) : BAexpFrameE d
theorem gg_counters {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : ((BAGGOp_A1 Γ p q).nS + 2 = Γ.nS ∧ (BAGGOp_A1 Γ p q).nW = Γ.nW + 1 ∧ (BAGGOp_A1 Γ p q).nA + BAGGOp_kappa Γ q.1.src p.1.dst = Γ.nA ∧ (BAGGOp_A1 Γ p q).nM ≤ Γ.nM) ∧ (∀ T ∈ [BAGGOp_A2 Γ p q, BAGGOp_A3 Γ p q], T.nS + 1 = Γ.nS ∧ T.nW = Γ.nW + 1 ∧ T.nA = Γ.nA ∧ T.nM ≤ Γ.nM) ∧ (∀ T ∈ [BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++ (lwSplit q.2).map (BAGGOp_AD Γ p q), T.counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩) ∧ (∀ T ∈ Γ.gg4 p q, T.counters = ⟨Γ.nS + 1, Γ.nW + 2, Γ.nA + 2, Γ.nM, 0, 0⟩)
theorem gg_raw {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : (BAGGOp_A1 Γ p q).scalingOrder = Γ.scalingOrder + 2 * (BAGGOp_kappa Γ q.1.src p.1.dst : ℤ) ∧ (∀ T ∈ (Γ.gg2 p q).tail, (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) ∧ (∀ T ∈ Γ.gg4 p q, (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1)
theorem gg_scalingOrderG {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hN : Γ.Normal) : (∀ T ∈ Γ.gg2 p q, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧ (∀ T ∈ Γ.gg4 p q, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)
theorem gg_mono {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : (∀ T ∈ Γ.gg2 p q, BAGGOp_Mono Γ T) ∧ (∀ T ∈ Γ.gg4 p q, BAGGOp_Mono Γ T)
$ grep -rnE '<new public names>' RBM3D RBM3D.lean --include='*.lean' | grep -v '^RBM3D/Graph/BAGGOp.lean' | wc -l   -> 4
  (the 4 matches are comment lines of RBM3D/Graph/BAWeightOp.lean :21, :676, :1923, :1933 that mention `BAexpFrameE`; no declaration clashes)
```
Compiled nonempty instances (namespace `RBM.Graph.BAGGOpInst`, `d = 3`, `L = 3`, `W = 1`, `g0 = 0`, `E = 0`, `m = i`, `t = 1/2`, `BASelf` by `BAExpandInst.baSelf_zero`; 27 sites, `y' = e1`, `y = e0`; every hypothesis discharged; `BAGGOp.lean:1730-1848`):
- `:1827` and `:1838`, the frame identity at `baGGLhs` (5 + 2 terms) and at `baGG3` (6 + 3 terms, derivative terms `AD`, `BD` present): proof terms `(baExpFrameE_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num) baGGLhs _).2 p0 hp0 q0 hq0 rfl rfl rfl rfl rfl` and `baExpFrame_gg 3 3 1 ... baGG3 _ p3 hp3 q3 hq3 rfl rfl rfl rfl rfl`.
- `lists_baGGLhs`: `(baGGLhs.gg2 p0 q0).length = 5 ∧ (baGGLhs.gg4 p0 q0).length = 2 ∧ Cnt A1 0 1 1 0 ∧ Cnt A2 1 1 1 0 ∧ Cnt A3 1 1 1 0 ∧ Cnt A4 3 1 2 1 ∧ Cnt A5 3 1 2 1 ∧ Cnt B1 3 2 3 1 ∧ Cnt B2 3 2 3 1` (`Cnt T a b c d` = `(n_S, n_W, n_A, n_M) = (a, b, c, d)`; `decide`; `A1` agrees with `baGGT1_counters`).
- `lists_baGG3`: lengths 6 and 3, `Cnt baGG3 3 0 1 1`, `Cnt A1 1 1 1 0`, `Cnt AD 4 1 2 1`, `Cnt BD 4 2 3 1`.  `:1803-1809`: `gg_counters`, `gg_raw`, `gg_scalingOrderG`, `gg_mono` applied at `baGGLhs`/`baGG3`.
- `A1_keeps : (BAGGOp_A1 baGGLhs p0 q0).scalingOrder = baGGLhs.scalingOrder` (`κ = 0`, `y`, `y'` external) and `A1_gains : (BAGGOp_A1 baGG4 p4 q4).scalingOrder = baGG4.scalingOrder + 2` (`κ = 1`, `y`, `y'` internal and distinct).

Narrative.
- Route of target 2: the verbatim lists give, at every labelling, `K` times the right side of `BAGGGammaR` (`BAGGOp_pathwise`: the nine term values `BAGGOp_*_term`, the derivative sums by `owx_list_aux`, the sum identity `BAGGOp_alg` with `W = 1 + M⁺(S W)` and `W = δ + W1`), transported to the sequence space and to `PF d L W 0` by `lwWx_integral` exactly as `baExpFrame_lw`; `t = 0` is separate (both sides `0`).  The 1a verdict on target 1 (lists correct, no change) is confirmed: the lists are used unchanged.
- Target 3 is the pair `baExpFrame_lw` (T2407) and `baExpFrame_gg`.  No smallness of `g` or `‖M - m₀I‖`, no `(Cλ)^{|a-b|}`: only `BASelf`, `0 ≤ t < 1`, `L ≥ 3` (C1, L5).
- Target 4: `A4, A5, AD` are definitionally `BAExpandWOrd_ext` and `B1, B2, BD` are `BAWeightOp_ext4`, so counters, `ordG` and `BAstepMono` counters come from the merged private lemmas, reached with `open private` (Batteries, precedent `Induction/DuhamelII.lean:42`); the `M`-splits of the new solid edges are new (`BAGGOp_hs_*`, `BAGGOp_D4_split`).  `A1, A2, A3` (new vertices joined to old atoms) are new: the pendant lemma `BAGGOp_pend` (atoms of `T` are those of `Γ'`), the merge lemma `BAGGOp_cnt_merge` (adding `M_{y'y}` lowers the count of internal atoms by exactly `κ`), the cover lemma `BAGGOp_cnt_le` for `n_M`.
- **Which terms keep or gain the order** (`gg_raw`, `gg_counters`): `ord A1 = ord Γ + 2κ`, `κ = BAGGOp_kappa Γ y' y ∈ {0, 1}`, `κ = 0` iff `Γ.atom y = Γ.atom y'` or both atoms contain an external vertex (so the first sum keeps the order of its parent in that case, gains `2` otherwise); every other term has `ord T° = ord Γ + 1` (`A2, A3`: `n_S - 1`, `n_W + 1`, `n_A`; `A4, A5, AD`: `(+1, +1, +1)`; `B1, B2, BD`: `(+1, +2, +2)`).  `gg_scalingOrderG`: `ord Γ ≤ ordG T` for all terms, `Γ` normal (non-strict, as `lw_scalingOrderG`).  `gg_mono`: `n_M`, `n_A - n_W`, `nExt` of `T°` do not exceed those of `Γ`.
- Hypotheses of `gg_counters`, `gg_raw`, `gg_mono`: only `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2` (the circle/colour/`src = dst` flags are not used by the counting); `gg_scalingOrderG` adds `Γ.Normal`.  Not proved in Lean (as for `lw`): the order of individual partition members (the table of T2395 design §3 (b)); only the lower bound `ord Γ ≤ ordG T`.
- Scope: `RBM3D.lean` has one import line (`import RBM3D.Graph.BAGGOp` after `RBM3D.BA.GreenLocal`), as the ticket's file scope allows; the hub's merge step finds it present.

## (c) Verified Mathlib names (each checked by `#check` in `lake env lean names.lean`, and used in `BAGGOp.lean`)
`Finset.card_filter_add_card_filter_not` (`Mathlib/Data/Finset/Card.lean:661`), `Finset.filter_or`, `Finset.filter_eq'` (`Data/Finset/Basic.lean:376,414`), `Finset.card_union_of_disjoint`, `Finset.card_image_le`, `Finset.card_le_card`, `Finset.sum_eq_single`, `Finset.sum_comm`, `Relation.ReflTransGen.lift` (`Logic/Relation.lean:753`; used as `lift f h _ _ hab`), `Relation.ReflTransGen.mono`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integral_const_mul`, `WithTop.coe_le_coe`, `List.prod_eq_zero`, `List.mem_flatMap`, `continuous_list_sum`, `Matrix.one_apply`.  Verified absent: `Bool.true_eq_true` (`unknown constant`).  In this Mathlib `if_true`, `if_false`, `if_pos`, `if_neg` give deprecation warnings (suggested: `ite_true`, `ite_false`, `ite_eq_left`, `ite_eq_right`); the file uses `ite_true`, `ite_false` and `split_ifs`.

## (d) Open issues and paper-delta candidates
- Open issues: none for targets 1-6.  Not covered (not a target): the order of single partition members of the terms (T2395 design §3 (b) table), and `BAstepMono` itself (L3a4 assembles `gg_counters`, `gg_raw`, `gg_scalingOrderG`, `gg_mono` with the `lw_*` theorems and `lanlw_*`).
- **T2410a**: `(eq:GGraisesord)` (`B:100`, "strictly increases the scaling order") read at BA, with `n_A` and external atoms: the first sum of `(B.20)` has `ord A1 = ord Γ + 2κ`, so it keeps the order iff `κ = 0` (`gg_raw`, `A1_keeps`, `A1_gains`); the other eight kinds of terms gain exactly `1` at `T°`.  Lean states `ord Γ ≤ ordG T`, not `<` (same difference as T2398b, `lw_scalingOrderG`).
- **T2410b**: the third sum of `(B.20)` carries `(1 + M⁺S⁺)_{xw}` and is split as `δ_{xw}` (`gg2`: `A4, A5, AD`) plus `(M⁺S⁺)_{xw}` (`gg4`), the first two sums carry `(W - 1) = M⁺S⁺` (paper delta D402); no mathematical change, a bookkeeping difference of the term lists.
