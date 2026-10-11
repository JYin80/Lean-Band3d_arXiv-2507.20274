Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 22:50:45 UTC 2026

Citations: `B:N`, `7_8:N` = lines of `paper/tex/B_graphical_lemmas.tex`, `7_8_light_weight.tex`; `file:N` = `RBM3D/Graph/file.lean` (main 19fc8cf); `T2387:N` = `docs/reports/T2387-design.md`; `2149:N` = `docs/supervisor/2026-10-10-2149.md`. Scripts `initcost.py`, `inst.py` (with `stab.py`, a copy of `docs/reports/T2390/stab.py`) are in the scratchpad `T2397/`. No Lean was written. Counters are `(nS, nW, nA, nM)`; `ord = nS + 2(nW - nA)` (`B:353`). `scost` is `LocalRegular6a.lean:157`: `#kept + 2(nW - #internal classes) + #elementary internal classes`.

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | counters and `ord` of the start `Γ_p = fxyPowGraph p` (no `M` edge) | `(3p, p, 2p, p)`, `ord = p` (p = 2: `(6,2,4,2)`, ord 2; p = 4: `(12,4,8,4)`, ord 4) | `fxyPowGraph_counters` (`LocalRegular.lean:1978`); the BA counters of a graph without `=`-dotted edges are the band counters (`BAVocab.lean:533`) | 0 |
| 2 | (6) thresholds, band | `Φ^all(Γ_p) = 2p`, `Φ^far(Γ_p) = 3p` exactly: `(4,6)` at p = 2, `(8,12)` at p = 4 (script) | `fxyPowGraph_locCostGe` (`LocalRegular6a.lean:927`): `≥ 2p`, `≥ 3p` | 0 (sharp) |
| 3 | (6) thresholds at BA, all `2^{2p}` splits `G -> Ǧ or M` (`B:339-340`) of the `2p` edges `x -> α_i`, `α_i -> y`, through the atomic image (vertices = atoms, `M` edge joins atoms, edge `circ := same atom`, all waved edges kept) | min over terms: `Φ^all = 2p` (4, 8), `Φ^far = 3p` (6, 12); min `ord = p` (2, 4) | same inequalities as row 2 | 0 (sharp) |
| 4 | terms whose image has one external atom (`x`, `y` joined through one `α_i`: `M_{xα_i}`, `M_{α_i y}`) | 7 of 16 (p = 2), 175 of 256 (p = 4) | `Φ^far` needs two external classes; for these only `Φ^all ≥ 2p` is available (holds, row 3) | the BA far corollary must read `atom(x) ≠ atom(y)`, not vertex-level `x ≠ y` |
| 5 | circle flag of the image | BA normal: every solid edge `circ = true` (`BAVocab.lean:158-160`); band invariant needs `circ ⇔ src = dst` (`CircIffLoop`, `LocalRegular6a.lean:162`) | image sets `circ := (atom src = atom dst)`; within-atom solid edges stay loops (`T2395-prove.md` row 6; `B:308-313` would discard them, `nS` counts them) | needed correction, not slack |
| 6 | `lvl1Cutoff` (`LWLvl1.lean:3981`), `c = 1/4`, `K0 = 2`, `D = 10`, `d = 3` | `K = 4(D + K0·nM + d·(nA - nW)^+)`: p = 2 -> 80, p = 4 -> 120 | `L^d ≤ W^{K0}`: `64 ≤ 32^2` | `K0 = 1` fails (`64 > 32`); `K - 2p = 76, 112` |
| 7 | `Ψ` window (`lvl1_size_le`, `LWLvl1.lean:3989`) | `W^{-d/2} = 2^{-7.5} ≤ Ψ = 2^{-5} ≤ W^{-c} = 2^{-1.25}` (`W = 32`) | as stated | `2^{2.5}` left, `2^{3.75}` right |
| 8 | size of a graph at the cutoff, `Q = (K+2(nA-nW), nW, nA, nM)` with `nM = p`, `nA - nW = p` (the start values, `ord Q = K`) | `log2 size = -378 / -588 / -63` at `Ψ = W^{-1} / W^{-3/2} / W^{-1/4}` (p = 2); `-556 / -876 / -76` (p = 4) | `≤ W^{-D} = 2^{-50}` | `2^{328} / 2^{538} / 2^{13}`; `2^{506} / 2^{826} / 2^{26}` |
| 9 | `Admissible` (`docs/reports/T2390-prove.md`): `W ≥ N^{1/6}`; `W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}` (`𝔡 = 1/10`, `Λ = 10`) | `32` vs `11.314` (`N = 2097152`); `2^{-7} ≤ g ≤ 10` | as stated | `2.83x`; `g / 2^{-7} = 2 / 128 / 1280` at `g = 1/64, 1, 10` |
| 10 | `κ ≤ Im m` (`BAReal`), `κ = 0.5 / 0.25 / 0.04` at `g = 1/64 / 1 / 10` | `Im m` (L = 64) `0.8325 / 0.3435 / 0.0439`; (L = 4) `0.8325 / 0.3777 / 0.2620` | `κ ≤ Im m` | `1.67x / 1.37x / 1.10x` (L = 64) |
| 11 | `c = BAct_rate(3, 10, κ)` (`BA/CombesThomas.lean:45`) | `4.158e-3 / 2.081e-3 / 3.333e-4` | `‖M_xy‖ ≤ c⁻¹ e^{-c|b|}` | observed ratio `5.4e-5 / 3.8e-4 / 2.8e-5` |
| 12 | `ρ = Σ_b ‖M_ab‖` (`BAMB_row_l1`), Ward `Σ_b |M_0b|² = 1` | `ρ_obs = 1.083 / 15.91 / 245`; Ward error `≤ 1.8e-14` | enters value bounds only; the cost computation of rows 2-3 uses no `g`, `κ`, `c` or `ρ` | uniform in `W` |
| 13 | `Lvl1Ident`-type hypothesis of the identity conjunct of `lw_localregular` (`LocalRegular6d.lean:1117-1118`: `M a a = m`, `M a b = 0`) | fails at BA data with `g ≠ 0` (`T2395-prove.md` row 15, probe 253; not re-derived here) | the counters, `Normal` and cost conjuncts have no such hypothesis | the identity conjunct is not transportable; it comes from the BA expansions (T2395, T2396) |
| 14 | atom truncation `B:317-319`, `ε₁ = 1/10`, `D = 10` | `e^{-c(log W)^{1+ε₁}} ≤ W^{-D}` needs `log10 log W ≥ 10·log10(D/c) = 33.8 / 36.8 / 44.8` | forbidden by L5 (`2149`, L5: exponential rate `BAct_rate` only) | not usable; same-atom terms (row 4) are handled by the `M`-decay of rate `c`, not by truncation |
| 15 | row table L3b1-L3b6 (`T2387:140-145`), no S | lo / central / hi: `7,927 / 10,569 / 18,918`; each row `1,330/1,549/2,933`, `1,186/1,381/2,616`, `1,478/2,087/3,652`, `1,556/2,197/3,845`, `1,093/1,543/2,701`, `1,284/1,812/3,171` | rows with central `> 1,500`: L3b1, L3b3, L3b4, L3b5, L3b6 (five of six; `2149` budget note lists the same five) | split decision belongs to the report |
| 16 | file length | `wc -l` of `LocalRegular6a`-`6d` = `1188 + 2382 + 1759 + 1510 = 6839`; ticket and `T2387:166` say 6,366 (a census count, not `wc -l`; files unchanged since 2026-10-05, last commit `37289f6`) | | report should use one stated count |

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 4`, `W = 32` (`N = 2097152`), `K0 = 2`, `c = 1/4`, `D = 10`, `Ψ = W^{-1}`, `𝔡 = ε = 1/10`, `Λ = 10`, `g = 1/64, 1, 10` with `κ` of row 10; `p = 2` and `p = 4`; the BA graphs are the `2^{2p}` splits of `Γ_p` (16 and 256 terms), `Γ_p` the band graph, and one external-hypothesis block (`Im m`, rate, `ρ`, Ward at `L = 64` as the proxy for `L -> ∞`, and at `L = 4`; the proxy is not a proof of the limit).

```
$ python3 -I initcost.py
p=2: band Gamma_p (no M): Phi^all, Phi^far = (4, 6) (Lean fxyPowGraph_locCostGe: >= 4, >= 6);  ord = 2
   BA terms: 16 (x,y same atom: 7, different: 9); min over terms: Phi^all = 4 (need >= 4: True), Phi^far = 6 (need >= 6: True); min ord = 2
p=4: band Gamma_p (no M): Phi^all, Phi^far = (8, 12) (Lean fxyPowGraph_locCostGe: >= 8, >= 12);  ord = 4
   BA terms: 256 (x,y same atom: 175, different: 81); min over terms: Phi^all = 8 (need >= 8: True), Phi^far = 12 (need >= 12: True); min ord = 4
$ python3 inst.py
N=2097152  N^(1/6)=11.314 <= W=32: True;  L^d=64; K0=2: L^d<=W^K0: True; K0=1: False
p=2: counters (nS,nW,nA,nM)=(6, 2, 4, 2) ord=2; lvl1Cutoff K=80; (6) needs ord>=2p=4, far 3p=6; K - 2p = 76 (the cutoff exceeds (6))
   Q=(84, 6, 8, 2) ord=80>=K: Psi=W^-1: log2 size=-378.00 <= log2 W^-D=-50: True; slack 2^328.00
   Q=(84, 6, 8, 2) ord=80>=K: Psi=W^-3/2: log2 size=-588.00 <= log2 W^-D=-50: True; slack 2^538.00
   Q=(84, 6, 8, 2) ord=80>=K: Psi=W^-1/4: log2 size=-63.00 <= log2 W^-D=-50: True; slack 2^13.00
p=4: counters (nS,nW,nA,nM)=(12, 4, 8, 4) ord=4; lvl1Cutoff K=120; (6) needs ord>=2p=8, far 3p=12; K - 2p = 112 (the cutoff exceeds (6))
   Q=(128, 8, 12, 4) ord=120>=K: Psi=W^-1: log2 size=-556.00 <= log2 W^-D=-50: True; slack 2^506.00
   Q=(128, 8, 12, 4) ord=120>=K: Psi=W^-3/2: log2 size=-876.00 <= log2 W^-D=-50: True; slack 2^826.00
   Q=(128, 8, 12, 4) ord=120>=K: Psi=W^-1/4: log2 size=-76.00 <= log2 W^-D=-50: True; slack 2^26.00
window W^-d/2 <= Psi <= W^-c: 2^-7.5 <= 2^-5 <= 2^-1.25; Admissible W^(-d/2+dd)=2^-7.0

C1: g, kappa, Im m [L=64], c=BAct_rate(3,10,kappa), rho_obs, Ward err, max|M|/(c^-1 e^-c|b|)  | at the instance size L=4: Im m, Im z in window, W^(-d/2+dd)<=g<=1/dd, t0
g=0.015625  kappa=0.5: Im m=0.8325>=kappa: True; c=4.158e-03; rho_obs=1.083; Ward err=1.1e-16; ratio=5.4e-05<=1: True  | L=4: Im m=0.8325>=kappa: True; Im z=0.368 in [2.04e-06,1]: True; 7.81e-03<=g<=10: True; t0=0.6937
g=1         kappa=0.25: Im m=0.3435>=kappa: True; c=2.081e-03; rho_obs=15.91; Ward err=1.3e-15; ratio=3.8e-04<=1: True  | L=4: Im m=0.3777>=kappa: True; Im z=0.822 in [2.04e-06,1]: True; 7.81e-03<=g<=10: True; t0=0.3148
g=10        kappa=0.04: Im m=0.0439>=kappa: True; c=3.333e-04; rho_obs=245; Ward err=1.8e-14; ratio=2.8e-05<=1: True  | L=4: Im m=0.2620>=kappa: True; Im z=0.938 in [2.04e-06,1]: True; 7.81e-03<=g<=10: True; t0=0.2183

row table L3b1-L3b6 (T2387-design.md:140-145): sum lo/central/hi = 7927/10569/18918; rows with central > 1500: ['L3b1', 'L3b3', 'L3b4', 'L3b5', 'L3b6']
```

### Verdicts

- **P1 (band route, pins):** PASS. `lw_localregular` `LocalRegular6d.lean:1107`, `locReg6Inv_locStep` `:1085`, `locCostGe_locStep` `:1077`, `scost` `LocalRegular6a.lean:157`, `PGraph.LocReg6Inv` `:182`, `fxyPowGraph_locCostGe` `:927` exist; rows 1-2 hold with slack 0.
- **P2 (under S):** PASS for the counters, `Normal` and cost halves (rows 1, 3, 5); the identity-in-expectation conjunct does not transport (row 13). The map needs: counter preservation (`BAVocab.lean:533`), `circ := same atom`, within-atom solid edges kept as loops (row 5), distinct external atoms for the far part (row 4).
- **P3 (without S):** PASS as to hypotheses and exponents: the BA cost of a merge is the band cost of the atomic image, and the start values are sharp at BA (row 3, script). The step lemma `Φ(child) ≥ Φ(parent)` for the BA `lanlw`, `lweight`, `GGGamma` outputs is not checked here; it is the step stage 1b must write or name.
- **P4 (pins):** PASS; the far corollary is pinned with `atom(x) ≠ atom(y)` (row 4). The twin statements of L3b1-L3b2 (invariant (1)-(5)) are not computed in this section.
- **C1/L5:** PASS: rows 7-12 hold at `g = 1/64, 1, 10`; row 14 excludes the atom truncation.
- **Row table:** PASS (rows 15-16 as numbers; the S branch is priced by the report).
- **Overall: PASS.**

## (b) Script output — Sun Oct 11 01:03:45 UTC 2026

Scripts (own code; Python 3.9, numpy; Lean 4.34.0) are in the scratchpad `T2397/` (not in the repository): `phi.py` (the band `scost` of `LocalRegular6a.lean:157` over all set partitions), `steps.py`, `stepsw.py` (band terms = the Lean builders `owxT1-4`, `oe1xD`, `oe2xR2-R8`; BA terms = `B:359-405`), `run.py`, `slack.py`, `dord.py`, `simcheck*.py`, `strat.py`, `strat_w.py`, `paths.py`, `init_ba.py`, `final_ident.py`, `molvw_vertex.py`, `cyc.py`, `rows2.py`, `mutant*.py`; outputs in `ev/`. The design report is `docs/reports/T2397-design.md` (branch `t/T2397`, commits `329703b`, `f32f904`, `0e2bb41`, `416232c`; the same file in this directory).

### L. Lean (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2397`, branch `t/T2397`, commits `17853aa`, `17295e2`, `329703b`, `f32f904`, `0e2bb41`, `416232c`)
**L1** build, size, forbidden tokens, diff, axioms (`bash ev/lean_ev2.sh`):
```
$ lake build RBM3D.Probe.T2397Pins 2>&1 | tail -1
Build completed successfully (3390 jobs).
$ lake env lean RBM3D/Probe/T2397Pins.lean | grep -vc "depends on axioms"   # lines that are not axiom lines: warnings, errors
0
$ lake env lean RBM3D/Probe/T2397Pins.lean > /dev/null; echo "exit $?"
exit 0
$ wc -l RBM3D/Probe/T2397Pins.lean docs/reports/T2397-design.md; grep -cwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2397Pins.lean
     390 RBM3D/Probe/T2397Pins.lean
     112 docs/reports/T2397-design.md
     502 total
0
$ git diff --stat main...t/T2397
 RBM3D/Probe/T2397Pins.lean   | 390 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2397-design.md | 112 +++++++++++++
 2 files changed, 502 insertions(+)
$ (#print axioms of every def/theorem/inductive of the probe, 51 names, grouped by the answer)
51
  51 X depends on axioms: [propext, Classical.choice, Quot.sound]
```
**L3** target statements (`python3 ev/extract1.py <names>`; `line: statement`):
```
80: def BAInit (p : ℕ) : Prop := ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, locReg6InvA p P
85: def BAFinal (R : BAPGraph (Fin 2) → Prop) : Prop := ∀ (P : BAPGraph (Fin 2)) (k : ℤ), R P → locStdA P.g → (locCostGeA false k P → k ≤ P.scalingOrder) ∧ (¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → locCostGeA true k P → k ≤ P.scalingOrder)
92: def BAStep (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop := ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), BStep P L → ∀ (far : Bool) (k : ℤ), locCostGeA far k P → ∀ Q ∈ L, locCostGeA far k Q
97: def BANormal (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop := ∀ P L, BStep P L → ∀ Q ∈ L, Q.g.Normal
102: def BAScostLL {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E I) (T : BAGraph E I') : Prop := ∀ s : Setoid (E ⊕ I'), atomSetoid T ≤ s → ∃ s₀ : Setoid (E ⊕ I), atomSetoid Γ ≤ s₀ ∧ (∀ a b : E, ¬ s (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧ scostA Γ s₀ ≤ scostA T s
118: theorem ba_ord_ge {p : ℕ} {BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop} {P0 : BAPGraph (Fin 2)} (h0 : locReg6InvA p P0) (hN : BANormal BStep) (hS : BAStep BStep) (hF : BAFinal (BReach BStep P0)) {Q : BAPGraph (Fin 2)} (hQ : BReach BStep P0 Q) : locReg6InvA p Q ∧ (locStdA Q.g → 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))
136: def BAImgNormal : Prop := ∀ P : BAPGraph (Fin 2), P.g.Normal → (img P).g.Normal ∧ LGraph.CircIffLoop (img P).g
139: def BABridge : Prop := ∀ (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k P ↔ PGraph.LocCostGe far k (img P)
144: def BAImgCounters : Prop := ∀ Q : BAPGraph (Fin 2), (img Q).g.counters = Q.g.counters
147: def BAImgMol : Prop := ∀ (Q : BAPGraph (Fin 2)) (u v : Q.E' ⊕ Q.I'), (promoteC Q.g).merge.molOf ((promoteC Q.g).vmap u) = (promoteC Q.g).merge.molOf ((promoteC Q.g).vmap v) ↔ v ∈ Q.g.mol u
152: def BAImgSim (m : ℂ) (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop := ∀ P L, BStep P L → ∀ Q ∈ L, ∃ L' : List (PGraph (Fin 2)), LocStep m (img P) L' ∧ img Q ∈ L'
165: theorem ba_ord_ge_of_sim {m : ℂ} {p : ℕ} {BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop} {P0 : BAPGraph (Fin 2)} (h0 : locReg6InvA p P0) (hB : BABridge) (hI : BAImgNormal) (hNin : ∀ P L, BStep P L → P.g.Normal) (hNout : BANormal BStep) (hsim : BAImgSim m BStep) (hF : BAFinal (BReach BStep P0)) {Q : BAPGraph (Fin 2)} (hQ : BReach BStep P0 Q) : locReg6InvA p Q ∧ (locStdA Q.g → 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))
177: def BAPathInit (p : ℕ) : Prop := ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, PGraph.PathInv2 p (img P)
181: def BAPathStep (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop := ∀ P L, BStep P L → ∀ k : ℕ, PGraph.PathInv2 k (img P) → ∀ Q ∈ L, PGraph.PathInv2 k (img Q)
186: def BAPathFinal (R : BAPGraph (Fin 2) → Prop) : Prop := ∀ (P : BAPGraph (Fin 2)) (p : ℕ), R P → locStdA P.g → PGraph.PathInv2 p (img P) → PGraph.LocReg345 (img P) p
190: def BAMolVW : Prop := ∀ Q : BAPGraph (Fin 2), Q.g.Normal → ∀ c : (img Q).g.Mol, (img Q).g.molNV c ≤ (img Q).g.molNW c + 1
200: def BALocReg (p : ℕ) (Q : BAPGraph (Fin 2)) : Prop := locStdA Q.g ∧ PGraph.LocReg2 (img Q) p ∧ PGraph.LocReg345 (img Q) p ∧ 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder)
```
**L4** compiled instances (nonempty: `p = 2`, `d = 3` data of the merged band instances; every deterministic hypothesis discharged; only the map pins stay hypotheses where marked):
```
352: theorem inst_ba_ord_ge_p2 (m : ℂ) {Q : BAPGraph (Fin 2)} (hQ : BReach (liftStep m 2) (liftC (fxyPowGraph 2).pack) Q) : locReg6InvA 2 Q ∧ (locStdA Q.g → 2 * ((2 : ℕ) : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * ((2 : ℕ) : ℤ) ≤ Q.scalingOrder))
360: theorem inst_step1_p2 : ∀ Q ∈ (lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)).map liftC, locReg6InvA 2 Q
366: theorem baStart2_orders : (BAGraph.ofLGraph p2Graph).splitG.map BAGraph.scalingOrder = [2, 3, 3, 2, 3, 4, 4, 3, 3, 4, 4, 3, 2, 3, 3, 2]
369: theorem baStart2_xy_atom : ((BAGraph.ofLGraph p2Graph).splitG.filter fun Δ => decide (Δ.atom (Sum.inl 0) = Δ.atom (Sum.inl 1))).length = 7
373: theorem inst_ba_ord_ge_of_sim_p2 (m : ℂ) (hB : BABridge) (hI : BAImgNormal) (hsim : BAImgSim m (liftStep m 2)) {Q : BAPGraph (Fin 2)} (hQ : BReach (liftStep m 2) (liftC (fxyPowGraph 2).pack) Q) : locReg6InvA 2 Q
379: theorem inst_baPathStep_p2 (m : ℂ) (hsim : BAImgSim m (liftStep m 2)) : BAPathStep (liftStep m 2)
```
**L5** name clash of the new public names (all in `RBM.Graph.T2397`): `bash ev/clash2.sh` greps `def|theorem|structure|inductive|abbrev|lemma|instance` + each new short name over `RBM3D/**/*.lean` outside the probe (first number), then `T2397` in any other `.lean` file (second number):
```
       0 0
```
Ports: none (`RBM1D`, `RBM2D` not used). `atom_ofLGraph` copies the private `BAVocab_atom_ofL` within RBM3D (`BAVocab.lean`).

### E. Numeric evidence (mathematics of the design; the Lean statements above carry the pins)
```
2-cycle Z->U->Z (blue, uncircled)  cost at the trivial merge =   0   Phi^all =  -2   (n_S, n_W) = (2, 0)
Contract(Z; U, U): loop dropped    cost at the trivial merge =  -2   Phi^all =  -2   (n_S, n_W) = (0, 1)
Contract(Z; U, U): loop kept (circled) cost at the trivial merge =   0   Phi^all =   0   (n_S, n_W) = (1, 1)
```
E0: the 2-cycle collapse (`localReg6b_instCyc`, `6b:1966-2025`). E1-E3 (`run.py MODE KIND NPARENTS SEED`; random parents, all terms of the step; violation = `Φ^all` or `Φ^far` of the child below the parent's), compact view (`ev/compact.py`):
```
$ python3 ev/compact.py ev/E1_band.out ev/E2_ba.out ev/E3_baout.out
band w parents=300000  (term:checks/violations)  T1:300,000/0 T2:300,000/0 T3:599,017/0 T4:599,017/0
band e parents=300000  (term:checks/violations)  D:600,018/0 R3:300,000/0
band g parents=300000  (term:checks/violations)  R2:300,000/0 R3:300,000/0 R4:300,000/0 R5:300,000/0 R6:300,000/0 R7:599,004/0 R8:599,004/0
ba w parents=1000000  (term:checks/violations)  W1:1,000,000/0 W2:1,999,085/0 W3:1,000,000/0 W4:1,999,085/0
ba e parents=1000000  (term:checks/violations)  L1:1,000,000/0 L2:1,998,888/0
ba g parents=1000000  (term:checks/violations)  A:1,000,000/0 B1:1,000,000/0 B2:1,000,000/0 C1:1,000,000/0 C1w:1,000,000/0 C2:1,000,000/0 C2w:1,000,000/0 C3:1,998,836/0 C3w:1,998,836/0
ba-out w parents=150000  (term:checks/violations)  W1/out:150,000/0 W2/out:2,399,632/0 W3/out:150,000/0 W4/out:2,399,632/0
ba-out e parents=150000  (term:checks/violations)  L1/out:300,000/0 L2/out:2,397,824/0
ba-out g parents=150000  (term:checks/violations)  A/out:150,000/0 B1/out:150,000/0 B2/out:150,000/0 C1/out:300,000/0 C1w/out:300,000/0 C2/out:600,000/0 C2w/out:600,000/0 C3/out:2,405,176/0 C3w/out:2,405,176/0
E1_band: term checks 5,396,060, violations 0
E2_ba: term checks 19,994,730, violations 0
E3_baout: term checks 14,857,440, violations 0
```
E2b, E4 (minimum slack `Φ(child) - Φ(parent)` per term, `Φ^all / Φ^far`), E5 (initial values at BA, `2^{2p}` terms):
```
200000 GG parents: {'x~y': 73380, "x~y'": 72200, "x~y and x~y'": 61495, "y~y'": 136727, "y, y' both in the atom of x": 0, 'all 16 classes seen': 16}
slack.py w 200000 (term: min slack Phi^all / Phi^far)  W1:2/2 W2:0/0 W3:2/2 W4:0/0
slack.py e 200000 (term: min slack Phi^all / Phi^far)  L1:0/0 L2:0/0
slack.py g 200000 (term: min slack Phi^all / Phi^far)  A:0/0 B1:0/0 B2:0/0 C1:0/0 C1w:2/2 C2:0/0 C2w:2/2 C3:0/0 C3w:0/0
$ python3 init_ba.py
p=1: terms 4 (x,y in one atom: 1); min Phi^all = 2 (2p = 2), min Phi^far = 3 (3p = 3); ord of the terms {1: 2, 2: 2}, min ord = 1 (p = 1)   [0s]
p=2: terms 16 (x,y in one atom: 7); min Phi^all = 4 (2p = 4), min Phi^far = 6 (3p = 6); ord of the terms {2: 4, 3: 8, 4: 4}, min ord = 2 (p = 2)   [0s]
p=3: terms 64 (x,y in one atom: 37); min Phi^all = 6 (2p = 6), min Phi^far = 9 (3p = 9); ord of the terms {3: 8, 4: 24, 5: 24, 6: 8}, min ord = 3 (p = 3)   [0s]
p=4: terms 256 (x,y in one atom: 175); min Phi^all = 8 (2p = 8), min Phi^far = 12 (3p = 12); ord of the terms {4: 16, 5: 64, 6: 96, 7: 64, 8: 16}, min ord = 4 (p = 4)   [1s]
```
E6, E6b, E6c (image of each BA term versus the band terms, up to renaming; `simcheck*.py`), E7 (final step), E11 (`(eq:MolVW)` at the start terms):
```
$ python3 simcheck.py 3000
w {'W1': '3000/3000', 'W2': '6033/6033', 'W3': '3000/3000', 'W4': '6033/6033'}
e {'L1': '3000/3000', 'L2': '6023/6023'}
g {'A': '2525/2525', 'B1': '2525/2525', 'B2': '2525/2525', 'C1': '2525/2525', 'C1w': '2525/2525', 'C2': '2525/2525', 'C2w': '2525/2525', 'C3': '5074/5074', 'C3w': '5074/5074'}
$ python3 simcheck2.py 3000   # parents with atoms of several vertices
w {'W1': '3000/3000', 'W2': '5904/5904', 'W3': '3000/3000', 'W4': '5904/5904'}
e {'L1': '3000/3000', 'L2': '5981/5981'}
g {'C1': '3000/3000', 'C1w': '3000/3000', 'C2': '3000/3000', 'C2w': '3000/3000', 'C3': '5977/5977', 'C3w': '5977/5977'}
$ python3 simcheck3.py 3000   # selected edge inside the atom of x
parents with x ~ v (selected edge inside the atom): 3000 ; terms L2: 5954
  L2                                 5954/5954
  L1 -> MoveLoop (loop dropped)      3000/3000
  L1 -> T1 (loop circled)            3000/3000
$ python3 final_ident.py
(i) random BA-normal graphs: 20000, scost(atoms) != ord + #elem in 0
(ii) vertex-level locally standard BA graphs: 3000 (of 121034 sampled), #elem != 0 or scost(atoms) != ord in 0
$ python3 molvw_vertex.py
p=2: 16 start terms; molecules violating n_V <= n_W + 1: vertices 17, atoms 0; first vertex-level violation (mdot, molecule, n_V, n_W) = ([(4, 1)], 2, 3, 1)
p=4: 256 start terms; molecules violating n_V <= n_W + 1: vertices 305, atoms 0; first vertex-level violation (mdot, molecule, n_V, n_W) = ([(8, 1)], 4, 3, 1)
```
E8a (`Φ` along the deterministic strategy of `B:135-157`, all states of `ord ≤ 4`), E8b (paths and `(3)-(5)`, all states of `ord ≤ 5`, waved edges tracked), E8c (executed steps by class), E9 (`ord` monotone), E10 (mutants: harness sensitivity), E12 (rows):
```
$ python3 strat.py 2 5
p=2 ORDMAX=5: states 1002 (by ord {2: 4, 3: 54, 4: 944}), locally standard 47; min ord over locally standard 4, over those with x,y in different atoms -
violations: {'viol_inv': 0, 'viol_ord': 0, 'viol_mono': 0, 'viol_std': 0, 'viol_far': 0}
$ python3 strat_w.py 2 6 400000   # path invariants + (3)-(5), waved edges tracked
p=2 ORDMAX=6: stored states 40337 (by ord {2: 4, 3: 56, 4: 1570, 5: 38707}), generated leaves with ord >= 6: 2652294, locally standard 626
PathInv2 failures: 0 | (3)(4)(5) failures at locally standard states: 0 | (eq:MolVW) on atoms failures: 0 | states with more than p internal molecules: 0
locally standard states: min ord 4 ; with x, y in different atoms: 0 min ord - (3p = 6 )
$ python3 strat_w_stats.py 2 6
p=2, states with ord < 6 expanded: 39711; executed steps by class:
    6268  step 1 weight
    3445  step 2 edge: selected edge INSIDE the atom of x
   15952  step 2 edge: selected edge between atoms
   13052  step 3 GG: x~y 0, x~y' 0, y~y' 0
     994  step 3 GG: x~y 0, x~y' 0, y~y' 1
$ python3 strat_w_stats.py 4 6
p=4, states with ord < 6 expanded: 282; executed steps by class:
     282  step 1 weight
$ python3 dord.py {w,e,g} 50000   # E9
kind w parents 50000  min ord(child)-ord(parent): {'W1': 1, 'W2': 0, 'W3': 1, 'W4': 1}  outputs: 1701408
kind e parents 50000  min ord(child)-ord(parent): {'L1': 0, 'L2': 0}  outputs: 894648
kind g parents 50000  min ord(child)-ord(parent): {'A': 0, 'B1': 1, 'B2': 1, 'C1': 0, 'C1w': 1, 'C2': 1, 'C2w': 1, 'C3': 0, 'C3w': 1}  outputs: 2342784
$ python3 mutant.py   # band mutants of R2, R4, R5
{'R2-nowaved': 2653, 'R4-noweight': 0, 'R5-noloop': 0}
$ python3 mutant_ba.py   # BA mutants (a waved edge or a weight dropped)
w {'W1-nowaved': '0/3000', 'W2-nowaved': '5364/5828', 'W3-nowaved': '0/3000', 'W4-nowaved': '2785/5828'}
e {'L1-nowaved': '1087/3000', 'L2-nowaved': '4693/5937'}
g {'A-nowaved': '2290/3000', 'B1-nowaved': '2361/3000', 'B2-nowaved': '2361/3000', 'C1-noweight': '1068/3000', 'C2-nowaved': '1251/3000'}
$ python3 rows2.py --short
wc -l: LocalRegular 2258, LocalRegular2 2068, 6a 1188, 6b 2382, 6c 1759, 6d 1510; 6a-6d total 6839
twin (T2387 section 6): sum lo/central/hi 7,927 / 10,569 / 18,918; rows with central > 1500: ['L3b1', 'L3b3', 'L3b4', 'L3b5', 'L3b6']
twin, split at section boundaries (central = basis x 1.20): L3b3a=6a 1,426, L3b4a=6b 1-1316 1,579, L3b4b=6b 1317-2382 1,279, L3b6a=6d 1-749 899, L3b6b=6d 750-1510 913 ; sums 4,284 = 2,087 + 2,197 and 1,812 = 1,812
6d sections 3-10 (decompositions, step, assembly) = 905 lines; section 11 (instances) = 374
  S L3b-S1  lo/central/hi    497 /    700 /  1,225   BAImg: promoteC, img, map lemmas (m0)-(m3), conservativity
  S L3b-S2  lo/central/hi    604 /    850 /  1,488   BACostEnds: BA Lemma B, BAInit (16/256 terms), BAFinal, BAScostLL
  S L3b-S3  lo/central/hi    863 /  1,216 /  2,128   BAStepImg: 15 image lemmas (6d s3-s10 x 1.20 + 130), BAStep, ba_ord_ge
  S L3b-S4  lo/central/hi    710 /  1,000 /  1,750   BAPathImg: (1)-(5) through the image, (4) at vertex level, BAMolVW
  S sum 2,674 / 3,766 / 6,591  (saving at central 6,803 = 64%)
  S' = S + (400 / 550 / 1000, new local lemmas for GG inside an atom) = 3,074 / 4,316 / 7,591
```

### Narrative
- Deliverables: the probe `RBM3D/Probe/T2397Pins.lean` (390 lines, limit 400) and the design report `docs/reports/T2397-design.md` (112 lines, limit 300; line 1 is the verdict on (6) under each branch); `git diff --stat main...t/T2397` is exactly these two files (L1). The report answers P1-P4, C1 and the row table.
- The probe compiles (`lake build` and `lake env lean`: no warning, standard axioms for all 51 declarations, L1): the BA cost vocabulary (`atomSetoid`, `promoteC`, `scostA`, `img`, `locCostGeA`, `locReg6InvA`), 15 Prop pins for L3b1-L3b6 (L3), five theorems that assemble them (`ba_ord_ge`, `ba_ord_ge_of_sim`, `baStep_of_sim`, `baPathStep_of_sim`, `BAScostLL.trans`), the lift `liftC` of a band graph with the lemmas that make `scostA` the band cost there, and the instances (L4).
- Instances: `ba_ord_ge` at `p = 2` has every hypothesis discharged (the band lift, the merged theorems `fxyPowGraph_locReg6Inv`, `locReg6Inv_locStep`, `locReg6_of_locCostGe`, `locReg6far_of_locCostGe`); `ba_ord_ge_of_sim` and `baPathStep_of_sim` keep only the map pins (`BABridge`, `BAImgNormal`, `BAImgSim`), which are the rows' targets; the BA-specific instance with atoms of several vertices is `decide`: the 16 start terms of `Γ_2` and their orders (`baStart2_orders`), 7 with `x`, `y` in one atom.
- Mathematics, by brute force on the band cost (`LGraph.scost` of `6a:157`, re-implemented in `phi.py`; the band builders reproduce the Lean local lemma: E1 5.4e6 term checks, 0 violations; the harness is sensitive, E10): the 15 BA terms transcribed from `B:359-405` satisfy `Φ(child) ≥ Φ(parent)` on 2.0e7 pre-partition terms and 1.5e7 partition outputs, sharply (E2-E4); their images equal band terms for non-degenerate selections (E6-E6c); initial values at BA (E5), final step (E7), `ord` monotone (E9); the deterministic strategy at `p = 2` is exhaustive (E8a-c).
- Two findings beyond the preflight: the literal simulation by `LocStep` (`BAImgSim`) holds only if the strategy selects by atom (`hwf`, `hnb` of `LocStep` are image-level conditions), so the vertex-level rule needs the term-level lemmas (design report §2); a GG pair with an edge inside an atom is outside the hypotheses of the band primitives (9 BA terms), numerically fine, executed 0 times in 14,046 GG steps at `p = 2`, `ord ≤ 5` (E8c).
- Differences from the preflight: none changes a verdict. (a) row 16 (6,839 against 6,366 lines) agrees with `wc -l` (E12); the circle flag of the image ((a) row 5) is `promoteC`, difference (ii) of `T2397a`.
- Not claimed: the Lean proofs of (m0)-(m3), `BAImgSim`, `BAStep`, `BAInit` (pins); the random numerics are evidence, not proofs; `p = 4` was run only to `ord 5` (weights only, E8c).

## (c) Verified Mathlib and core names used (`#check`, `ev/names.lean`; none verified absent)
```
@Setoid.ker : {α : Type u_1} → {β : Type u_2} → (α → β) → Setoid α
@Setoid.bot_def : ∀ {α : Type u_1}, ⇑⊥ = fun x1 x2 => x1 = x2
@Finset.singleton_inj : ∀ {α : Type u_1} {a b : α}, {a} = {b} ↔ a = b
@Finset.mem_singleton : ∀ {α : Type u_1} {a b : α}, b ∈ {a} ↔ b = a
@List.filter_map : ∀ {β : Type u_1} {α : Type u_2} {f : β → α} {p : α → Bool} {l : List β}, List.filter p (List.map f l) = List.ma
@List.map_map : ∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ} {f : α → β} {l : List α}, List.map g (List.map f l) = L
@List.map_id : ∀ {α : Type u_1} (l : List α), List.map id l = l
@List.map_congr_left : ∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.
@List.mem_map : ∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : List α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
@List.mem_map_of_mem : ∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α} {f : α → β}, a ∈ l → f a ∈ List.map f l
@Relation.ReflTransGen : {α : Type u_1} → (α → α → Prop) → α → α → Prop
@bot_le : ∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ a
@Bool.eq_false_iff : ∀ {b : Bool}, b = false ↔ b ≠ true
@List.any_eq_true : ∀ {α : Type u_1} {p : α → Bool} {l : List α}, l.any p = true ↔ ∃ x ∈ l, p x = true
Bool.and_eq_true : ∀ (a b : Bool), ((a && b) = true) = (a = true ∧ b = true)
@List.any_nil : ∀ {α : Type u_1} {f : α → Bool}, [].any f = false
Bool.or_false : ∀ (b : Bool), (b || false) = b
@Function.comp_def : ∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β → δ) (g : α → β), f ∘ g = fun x => f (g x)
```

## (d) Open issues and paper-delta candidates

- `T2397a` (on `B:308-313`): the atomic graph discards solid edges inside an atom, but `ord` (`B:353`) counts them: the image keeps them as circled loops, drops the circle of an edge between atoms and adds `×`-dotted edges (probe `promoteC`).
- `T2397b` (on `T2387c`): `B:416` asserts (1)-(6) at BA with no argument; (6) is the band cost route on the atomic image (design report §2, §3).
- `T2397c`: `(eq:MolVW)` at BA counts atoms: the vertex count fails at the start (17 molecules at `p = 2`, 305 at `p = 4`, E11).
- `T2397d`: the far corollary reads `atom(x) ≠ atom(y)` (7 of 16 start terms at `p = 2`, 175 of 256 at `p = 4` have `x`, `y` in one atom; `baStart2_xy_atom`).
- `T2397e`: local standardness at BA, vertex level (`deflvl1` as written) versus atom level (the image's); (6) is insensitive (E7), the selection rule is not (design report §2).
- Open: (1) T2395 decides the selection rule (atom level, guard, or S'); (2) the map lemmas (m0)-(m3), (m5) and BA Lemma B are the proofs of the rows; (3) the S row estimates are bottom-up; (4) the BA term builders (L2c1, L2c2) do not exist: the images were checked against the paper formulas; (5) `Ψ`-dotted edges are not produced by the three expansions and are not modelled.

## Repair (audit round 1, `docs/reports/T2397-audit.md`: D1, D2, items 1-4) — Sun Oct 11 02:40:40 UTC 2026
Repairer `claude-opus-5-5`. Commits `005474a` (probe), `54ba7be` (design report; copied unchanged to this directory). Sections (b) L1-L5 above describe the first version (`416232c`); the probe's state is below.
```
$ lake build RBM3D.Probe.T2397Pins 2>&1 | tail -2
info: RBM3D/Probe/T2397Pins.lean:385:0: 'RBM.Graph.T2397.inst_ba_ord_ge_of_simC_p2' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3390 jobs).
$ lake env lean RBM3D/Probe/T2397Pins.lean > out; echo "exit $?"; grep -vc "depends on axioms" out
exit 0
0
$ echo "$(wc -l < RBM3D/Probe/T2397Pins.lean) $(wc -l < docs/reports/T2397-design.md); $(grep -cwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2397Pins.lean)"
385 164; 0
$ git diff --stat main...t/T2397 | tail -1
 2 files changed, 549 insertions(+)
$ lake env lean $SCRATCH/T2397/r_ax.lean | sed -E "s/'[^']+'/X/" | sort | uniq -c   # #print axioms of all 64 declarations (grep of the probe)
63 X depends on axioms: [propext, Classical.choice, Quot.sound]
1 X does not depend on any axioms
$ bash $SCRATCH/T2397/r_clash.sh
19 names, files outside the probe declaring one of them: 0
$ python3 -I $SCRATCH/T2397/r_extract.py <names>   # new targets and instances, line: statement
129: def BASimC (m : ℂ) (T : BTStep) : Prop := ∀ P LT, T P LT → ∃ (P' : PGraph (Fin 2)) (L' : List (PGraph (Fin 2))), LocStep m P' L' ∧ P'.g.Normal ∧ LGraph.CircIffLoop P'.g ∧ (∀ far k, locCostGeA far k P → P'.LocCostGe far k) ∧ ∀ Q, (BAShape.band, Q) ∈ LT → ∃ R ∈ L', ∀ far k, R.LocCostGe far k → locCostGeA far k Q
134: def BAShapeLL (sh : BAShape) (T : BTStep) : Prop := ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT → ∀ far k, locCostGeA far k P → locCostGeA far k Q
137: theorem baStep_of_simC {m : ℂ} {T : BTStep} (hS : BASimC m T) (hX : ∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) : BAStep (untag T)
148: theorem ba_ord_ge_of_simC {m : ℂ} {p : ℕ} {T : BTStep} {P0 : BAPGraph (Fin 2)} (h0 : locReg6InvA p P0) (hN : BANormal (untag T)) (hS : BASimC m T) (hX : ∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) (hF : BAFinal (BReach (untag T) P0)) {Q : BAPGraph (Fin 2)} (hQ : BReach (untag T) P0 Q) : locReg6InvA p Q ∧ (locStdA Q.g → 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))
170: def BASimP (m : ℂ) (T : BTStep) : Prop := ∀ P LT, T P LT → ∃ (P' : PGraph (Fin 2)) (L' : List (PGraph (Fin 2))), LocStep m P' L' ∧ (∀ k, (img P).PathInv2 k → P'.PathInv2 k) ∧ ∀ Q, (BAShape.band, Q) ∈ LT → ∃ R ∈ L', ∀ k, R.PathInv2 k → (img Q).PathInv2 k
174: def BAShapePath (sh : BAShape) (T : BTStep) : Prop := ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT → ∀ k, (img P).PathInv2 k → (img Q).PathInv2 k
177: theorem baPathStep_of_simP {m : ℂ} {T : BTStep} (hS : BASimP m T) (hX : ∀ sh, sh ≠ BAShape.band → BAShapePath sh T) : BAPathStep (untag T)
355: def BAPathLift : Prop := ∀ P0 : PGraph (Fin 2), P0.g.Normal → ∀ k, (img (liftC P0)).PathInv2 k ↔ P0.PathInv2 k
364: theorem inst_ba_ord_ge_of_simC_p2 (m : ℂ) {Q : BAPGraph (Fin 2)} (hQ : BReach (untag (liftStepT m 2)) (liftC (fxyPowGraph 2).pack) Q) : locReg6InvA 2 Q ∧ (locStdA Q.g → 2 * ((2 : ℕ) : ℤ) ≤ Q.scalingOrder ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * ((2 : ℕ) : ℤ) ≤ Q.scalingOrder))
371: theorem inst_step1_simC : ∀ Q ∈ (lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)).map liftC, locReg6InvA 2 Q
377: theorem inst_baPathStep_of_simP_p2 (m : ℂ) (hL : BAPathLift) : BAPathStep (untag (liftStepT m 2))
```
- D1: `BAImgSim` (equality of packed graphs) and the theorems and instances built on it are removed; `BASimC`/`BASimP` relate `P`, `Q` to band graphs only through the transfer of the cost bounds and of `PathInv2` (up to relabelling). `inst_ba_ord_ge_of_simC_p2` discharges every hypothesis at the lifted band strategy (`simC_liftStepT`; the shape pins hold because every lifted output is tagged `band`, so they are vacuous there); `inst_baPathStep_of_simP_p2` keeps only `BAPathLift`, a conservativity pin of the map row.
- D2: the design follows T2395's S′; the five BA-only shapes are pinned (`BAShape`, `BAShapeLL`, `BAShapePath`), their cost step is E13 (9,248,933 checks, 0 violations), the rows are re-priced (E14: G2 845 / 1,190 / 2,083 against T2395's 590 central, reasons in design §6); "S'" is renamed S+GG and subsumed (design §2 (iii)). Amend 1: no κ- or rate-dependent closure was added (E13, E14 are counts and line estimates).
- Paper-delta candidates: no new tag; `T2397b`, `T2397e` are re-worded in design §7 (five BA-only local lemmas; S′ stops at atom level). Open: the atom-level final step (design §2 (v)) and `BAShapePath` are not compiled or checked here.
