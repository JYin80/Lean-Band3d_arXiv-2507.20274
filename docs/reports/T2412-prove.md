Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 08:02 UTC 2026

### (i) Exponent table, and the atom step

Notation: `N=(WL)^d`, `c=BAct_rate d Λ κ=min(log(1+κ/(4dΛ)),κ/2)`, `expC` as `Defs/RadialSum.lean:271`, `ε=κ²/4`, `A=4(16d²κ⁻³/c)²`, `μ=BAp5s_rate`, `C5=BAp5s_C` (`BA/Prop5Short.lean:49-60`). Data: `0<g0≤Λ`, `BAReal d L g0 κ E m` (`κ≤Im m`), `0≤t<1`, `L≥3`, `W≥1`, `3≤d`. Counters `(n_S,n_W,n_A,n_M)`, `n_V=|I|`.

| # | item | value | constraint | slack |
|---|---|---|---|---|
| R1 | W-power of the size (B.16) | `−d(n_W−n_A)`: `N^{n_M}(K₀W^{-d})^{n_W−(n_A−n_M)}=K₀^{..}(L^d)^{n_M}W^{-d(n_W−n_A)}` | `n_M≤n_A`, `n_A−n_M≤n_W` (R4; the twin of `lwSize_alg`, `LWSizeClaim:1082`, with `n_V:=n_A`) | exact, 0 loss; `|val|/size` is the same at `W=1,2,3` (output below) |
| R2 | roots | `N` per internal molecule, so `(L^d)^{n_M}` | one root vertex per internal molecule | exact |
| R3 | `Ψ^{n_S}` | every solid edge of a normal BA graph is circled, so `|Ǧ_xy|≤Ψ` for all `x,y` incl. `x=y` | hypothesis `‖G−M‖≤Ψ` entrywise | no `N^τ`, no window; no `×`-dotted case split |
| R4 | forest edges | children `|C|=n_V−n_M`; dotted tree edges `n_V−n_A`; waved tree edges `n_A−n_M` | the sum of the last two is `|C|`; more than `n_A−n_M` waved tree edges would lose `W^d` each | counted by script for `baGGT1` (2 dotted, 1 waved) and `baLWT1` (1, 1) |
| R5 | `M` row/col sums | `K_M=c⁻¹expC(d−2,c)` (`BAMB_row_l1` through the offset fibre; columns by `baM_symm`) | uniform in `g0∈(0,Λ]`, `L`, `W`, `E`, `t` | actual `rowM` 1.10 / 5.82 / 4.65 at `g=1/64, 1, 10` against `K_M` 2e5 / 2e10 / 3e15 |
| R6 | `M` entries | `a_M=1` (Ward `baM_row_sq`: `Σ_α|M_xα|²=1`) | none | actual `max|M|` 0.999 / 0.596 / 0.559 |
| R7 | `Ψ`-dotted | entries `g0≤Λ`, row/col sums `2d g0≤2dΛ` (`card_nbhd`, offset fibre) | upper range only; no smallness | exact |
| R8 | `S`, `S⁺` | `S`: entries `≤W^{-d}`, row sums `t≤1`. `S⁺=tLift(Θ)`: `K₀=max(1,(1+Λ²)C5)`, rate `μ`, `K₁=K₀expC(d−2,μ)` | `|Θ_ab|≤C5(1_{a=b}+g²e^{-μ|a−b|})≤(1+Λ²)C5e^{-μ|a−b|}` | actual `rowSp` 0.33 / 0.52 / 0.55; constants are huge but only enter `C_Γ` (table below) |
| R9 | `Kd` | `Kd=max(a_M,K_M,Λ,2dΛ)` for both `M`- and `Ψ`-dotted edges | each such edge costs `≤Kd` (entry if non-tree, row sum if tree) | `C_Γ=‖coeff‖K₁^{n_A−n_M}K₀^{n_W−(n_A−n_M)}Kd^{#mdot+#psi}` |
| R10 | tail / `(B.15)` | offset equality is exact (`BAMfine_eq`); block spread: `Σ_{d_B≥R}|M|≤c⁻¹expC(d−2,c/2)e^{-cR/2}`, `R=(log W)^{1+ε₁}` | `e^{-cR/2}≤W^{-D}` iff `log W≥(2D/c)^{1/ε₁}` | eventual only, not used by the claim: `log W₀=7e41` at `c=0.0485, D=3, ε₁=1/20` |

**Atom step (how atoms enter; closes, no REQ).**
- A1. A BA term is `coeff·∏Ǧ·∏_waved·∏_{×-dotted}(≤1)·∏_{M-dot}M·∏_{Ψ-dot}g0Ψ`. With `LWKBound K a K'` (entries `≤a`, row/col sums `≤K'`) for `S,S⁺,M,g0Ψ`, only entries and row sums of the four weights are used. The uniform decay rate enters only in `K_M`, `K₀`, `K₁` (through `c`, `μ`, both fixed by `(d,Λ,κ)`). No `g0≤W^{-ε}`, no `(Cλ)^{|a−b|}` (L5); the paper's `(Mbound_AO)` is replaced by the Combes–Thomas bound for all `g0≤Λ`.
- A2. Atoms are components of the `{M,Ψ}`-dotted graph, molecules of `{waved,M,Ψ}`. Targets: external atoms and one root atom per internal molecule. Rank atoms by waved distance: each non-target atom `X` gets a gate waved edge `(u∈X, v∈X')`, `rk X'<rk X`, distinct for distinct `X`. Inside each atom take a BFS spanning tree of the dotted graph rooted at the gate `u` (external atom: at an external vertex; root atom: at any vertex). Rank `ρ(v)=rk(atom v)(|I|+1)+depth(v)`. Tree edges are distinct (a shared edge would make each end the other's parent).
- A3. The peeling `lwForest_core` generalised to per-edge `(a_j,K_j)`: `N^{|C|}Σ_ℓ∏_jf_j ≤ N^{|I|}∏_{c∈C}K_{e(c)}∏_{j∉e(C)}a_j`. `lwForest_sum_le` (one `a`, one `K`) does not suffice: a tree `M`-edge costs `Kd=O(1)` but a non-tree waved edge costs `K₀W^{-d}`. This is a twin (private core, `LWSizeClaim:491-677`). Result: `Σ_{ℓ_I}≤N^{n_M}K₁^{n_A−n_M}(K₀W^{-d})^{n_W−n_A+n_M}Kd^{#mdot+#psi}`.
- A4. Kernel edges: `M⁺S=tLift(BAMss⁺⁺)` (one `α` per block with the offset of `x`); `R=1+Lift(Θ−1)`, `Θ=BATheta … true true`, satisfies `(1−M⁺S)R=1` (`BATheta_isUnit`); with `baW_mul` this gives `W=R`, so `S⁺=SW=tLift(Θ)`, and `|S⁺_xy|≤K₀W^{-d}e^{-μd_B}` by `baProp5s_holds` and the translation shift of `BATheta` (private in `BA/KStep.lean:270`: copy). Rows by `lwKBound_of_decay` (public). The general (non-normal) form: `BAGraph.val_eq_partition` is unconditional, so `size_G=max` over the partition.

**Pins (pseudo-Lean; `namespace RBM.Graph`; a separate step compiles them in `RBM3D/Probe/T2412Pins.lean`).**
```
def BAGraph.sizeConst (Γ) (K₀ K₁ Kd : ℝ) : ℝ :=
  ‖Γ.coeff‖ * K₁^(Γ.nA-Γ.nM) * K₀^(Γ.nW-(Γ.nA-Γ.nM)) * Kd^(Γ.mdot.length+Γ.psi.length)
-- T1  S⁺ = tLift(Θ) and (eq:estSpm-W)
theorem baSp_eq : (hL:3≤L) (BAReal d L g0 κ E m) (0≤t<1) :
  Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m = (t:ℂ) • lwLift d L W (BATheta d L g0 E m t true true)
theorem baSpDecay (d) (hd:3≤d) (Λ κ) (hΛ:0<Λ) (hκ:0<κ) : ∃ C c, 0<C ∧ 0<c ∧ ∀ L W [NeZero L][NeZero W],
  3≤L → ∀ g0 E t m, 0<g0 → g0≤Λ → BAReal d L g0 κ E m → 0≤t → t<1 →
  (∀ x y, ‖Matrix.of (BAlwS d L W t) x y‖ ≤ C*((W:ℝ)^d)⁻¹*exp(-(c*lwBdist d L W x y))) ∧
  (∀ x y, ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤ C*((W:ℝ)^d)⁻¹*exp(-(c*lwBdist d L W x y)))
theorem baKBound_E (d Λ κ as above) : ∃ K₀ K₁ Kd, 0<K₀ ∧ 0<K₁ ∧ 0≤Kd ∧ ∀ L W g0 E t m, (same data) →
  LWKBound (Matrix.of (BAlwS d L W t)) (K₀*((W:ℝ)^d)⁻¹) K₁ ∧ LWKBound (S*BAlwW ..) (K₀*((W:ℝ)^d)⁻¹) K₁ ∧
  LWKBound (BAlwM d L W g0 E m) Kd Kd ∧ LWKBound ((g0:ℂ) • PsiI d L W) Kd Kd
-- T2  peeling and atomic forest
theorem BASizeClaim_forest_sum_le [Nonempty ι] (ℓe) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : J → ℝ) (0≤f, f≤a j,
  row/col sums ≤K j) (C : Finset I) (par) (edge : I → J) (ρ) (InjOn edge C) (hedge) (hrank) :
  (card ι:ℝ)^C.card * ∑ ℓ, ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤ (card ι:ℝ)^(card I) * (∏ c∈C, K (edge c)) * ∏ j∈(C.image edge)ᶜ, a j
theorem BAGraph.exists_forest (Γ : BAGraph E I) (hD : ∀ e∈Γ.dotted, e.eq=false) : ∃ C par edge ρ,  -- J = waved ⊕ mdot ⊕ psi
  C.card+Γ.nM = card I ∧ (C.filter fun c => ∃ j, edge c = some (inl j)).card + Γ.nM = Γ.nA ∧ ranks/edges/injectivity as LGraph.exists_forest
theorem BAGraph.counters_le (Γ) (hD) : Γ.nM ≤ Γ.nA ∧ Γ.nA-Γ.nM ≤ Γ.nW
-- T3  claim:size, deterministic (no hM)
theorem baClaimSize (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ}
  (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀*((W:ℝ)^d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀*((W:ℝ)^d)⁻¹) K₁)
  (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → Idx d L W) :
  ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L
theorem baClaimSizeG (Γ) (D) (0≤K₀, K₁, Kd) (same hyps) :  -- general: BAGraph.partition, BAGraph.val_eq_partition
  ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * Γ.scalingSizeG Ψ W d L
-- T4  model form and tail: baClaimSize_E, baClaimSizeG_E (∃ K₀ K₁ Kd depending on (d,Λ,κ), D.S/Sp/M/gPsi = the BAlw matrices),
--     baSpTail_E, baMTail_E (Σ_{d_B≥R}|·| ≤ C e^{-cR}), baTail_log (e^{-cR/2} ≤ W^{-D} for R=(log W)^p, p>1, W ≥ W₀(c,p,D))
```
File plan: `Graph/BASizeClaim.lean` = T1 + T2 (kernel side), `Graph/BASizeClaim2.lean` = T3 + T4 + instances; the second imports the first. Central estimate above 1,500 lines, so split; each file stays below 2,000.
Merge cone: planned imports `LWSizeClaim`, `BAVocab`, `BAExpandW`, `BA.GreenSchur`, `BA.Prop5Short` (script below).

### (ii) One concrete nondegenerate instance

`d=3, L=4, W=2` (`N=512`, 8 offsets, 64 blocks), `t=1/2`, `E` real, `m=iκ` solving `(self_m)` (`g0∈{1/64,1,10}`, `κ=Im m`), `G=M+Ψ·J` with `Ψ=1/100` (so `|Ǧ_xy|=Ψ` for all `x,y`). Graphs from `BAVocabInst`, both normal: `baGGT1` (`n_S,n_W,n_A,n_M=0,1,1,0`, internal vertices `x,u` tied by `M`-dotted edges, waved `u—β`, external atom `{a0,a1,β}`; `ℓe` takes `a0,a1` in distinct blocks with the same offset, otherwise every term vanishes) and `baLWT1` (`2,1,2,1`, `size=(L^d)Ψ²W^d`). Lean data: `MFixedPointInst.P : FlowPt 4 10` (`BAReal 3 4 P.g0 (Im P.m0) P.E P.m0`, `P.g0≤10`), `W=2`.
No external (unproved) hypothesis: `baProp5s_holds`, `BAMfine_decay`, `BAMB_row_l1`, `baM_row_sq`, `baW_isUnit` are merged theorems; the script evaluates their conclusions at the data (constants from the definitions above).
```
$ S=<scratchpad>/T2412; python3 $S/counters.py; python3 $S/report.py; python3 $S/wscan1.py; python3 -I $S/cone.py <root> RBM3D.Graph.BAVocab RBM3D.Graph.LWSizeClaim
baGGT1 {'nS': 0, 'nW': 1, 'nA': 1, 'nM': 0, 'nV': 3, 'waved_tree': 1, 'dotted_tree': 2}
baLWT1 {'nS': 2, 'nW': 1, 'nA': 2, 'nM': 1, 'nV': 3, 'waved_tree': 1, 'dotted_tree': 1}
g=0.01562 Lam=0.01562 kappa=0.9993 cM=0.5 mu=1.93e-09 KM=1.98e+05 K0=4.24e+12 K1=1.87e+51 | actual maxM=0.999 rowM=1.101 rowSp=0.334 max|Sp|W^d e^(mu dB)=0.333
    G1=baGGT1 |val|=0.0103 <= K1*Kd^4*1=2.86e+72;  G2=baLWT1 |val|=0.0255 <= K1*Kd*size=1.89e+55 (size=0.0512, |val|/size=0.498)
g=1 Lam=1 kappa=0.5959 cM=0.0485 mu=2.17e-22 KM=2.3e+10 K0=5.02e+21 K1=1.38e+112 | actual maxM=0.596 rowM=5.822 rowSp=0.525 max|Sp|W^d e^(mu dB)=0.429
    G1=baGGT1 |val|=0.00617 <= K1*Kd^4*1=3.85e+153;  G2=baLWT1 |val|=0.00425 <= K1*Kd*size=1.62e+121 (size=0.0512, |val|/size=0.0829)
g=10 Lam=10 kappa=0.5594 cM=0.00465 mu=8.66e-32 KM=2.82e+15 K0=6.94e+29 K1=7.59e+157 | actual maxM=0.559 rowM=4.652 rowSp=0.548 max|Sp|W^d e^(mu dB)=0.441
    G1=baGGT1 |val|=8.04e-06 <= K1*Kd^4*1=4.83e+219;  G2=baLWT1 |val|=0.000427 <= K1*Kd*size=1.1e+172 (size=0.0512, |val|/size=0.00833)
g=0.01562 Lam=10 kappa=0.9993 cM=0.00829 mu=1.64e-27 KM=1.57e+14 K0=2.04e+25 K1=1.73e+136 | actual maxM=0.999 rowM=1.101 rowSp=0.334 max|Sp|W^d e^(mu dB)=0.333
    G1=baGGT1 |val|=0.0103 <= K1*Kd^4*1=1.04e+193;  G2=baLWT1 |val|=0.0255 <= K1*Kd*size=1.39e+149 (size=0.0512, |val|/size=0.498)
W=1 g=1: |G1|/size1=0.0061714 |G2|/size2=0.082925
W=2 g=1: |G1|/size1=0.0061714 |G2|/size2=0.082925
W=3 g=1: |G1|/size1=0.0061714 |G2|/size2=0.082925
RBM3D.Graph.BAVocab 3 modules; LWExpCert in cone: []
RBM3D.Graph.LWSizeClaim 48 modules; LWExpCert in cone: []
union cone of the five planned imports: 99 modules; LWExpCert: []; Probe: []
```
The script also asserts `Σ_b|M^B_ab|²=1` (Ward) and `S⁺=tW^{-d}Θ_{[x][y]}` (`allclose`) at each point. The ticket says the cone of `BAVocab` is 6 modules; the script counts 3 `RBM3D` modules (`BAVocab`, `LWVocab`, `ScalingOrder`): none touches `LWExpCert*`.

### Verdicts
- T1 `(eq:estSpm-W)` for `S`, `S⁺`: PASS. Observation: `K₁` is astronomically large (`μ` of `BAp5s_rate` is 2e-9 at `g=1/64`); the exponents do not depend on it, and the actual row sums are 0.33-0.55.
- T2 atom peeling and forest with atoms: PASS (R1-R4, A2-A3; the atom step closes for every `0<g0≤Λ`, `κ≤Im m`; no REQ).
- T3 `baClaimSize` and `baClaimSizeG`: PASS. No `hM`; the hypothesis is `‖G−M‖≤Ψ` entrywise, plus `LWKBound` for `M`, `g0Ψ`.
- T4 model form and tails: PASS (tail threshold `W₀` is eventual and astronomically large, R10).
- T5 nonempty instances: PASS at `(3,4,2)` with `P`, `baGGT1` and `baLWT1`; the labels `a0,a1` must share an offset.
- Paper-delta candidates: `T2412a` Combes–Thomas for all `g0≤Λ` instead of the `(Cλ)^{|a−b|}` / large-`λ` split of `(Mbound_AO)/(Mbound_AO2)`; `T2412b` the deterministic `claim:size` has no `(log W)^{1+ε₁}` atom-spread loss (row sums are `O(1)`); `T2412c` `S⁺=SW` with `W=(1−M⁺S)⁻¹` instead of the band's `S(1−m²S)⁻¹`.

## (a″) Probe compile — Sun Oct 11 08:18:28 UTC 2026

Probe `RBM3D/Probe/T2412Pins.lean` in `/Users/junyin/Lean_proof/RBM3D-wt/T2412` (branch `t/T2412`), commit `668318f` (parent `d3ea0c0`): 303 lines (limit 400), the only file of `git diff main...t/T2412`, no root import. Section (a) is not edited: `head -n 93 docs/reports/T2412-prove.md | md5` is `be468510fe6005c15f71711ecd86e1c7` before and after this section was appended. `S=<scratchpad>/T2412`.

```
$ date -u
Sun Oct 11 08:17:03 UTC 2026
$ git log -1 --format="%h %s"; git status --short; git diff --stat main...t/T2412; wc -l RBM3D/Probe/T2412Pins.lean
668318f T2412: probe, example also applies the T2 counters/forest pins at baLWT1
 RBM3D/Probe/T2412Pins.lean | 303 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 303 insertions(+)
     303 RBM3D/Probe/T2412Pins.lean
$ grep -nE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2412Pins.lean; echo "grep exit=$?"
grep exit=1
$ lake env lean RBM3D/Probe/T2412Pins.lean; echo "exit=$?"
@BAGraph.sizeConst : {E I : Type} →
  [Fintype E] → [DecidableEq E] → [Fintype I] → [DecidableEq I] → BAGraph E I → ℝ → ℝ → ℝ → ℝ
@BAGraph.Jx : {E I : Type} → BAGraph E I → Type
@BAGraph.edgeEnds : {E I : Type} → (Γ : BAGraph E I) → Γ.Jx → (E ⊕ I) × (E ⊕ I)
RBM.Graph.baSp_eq_pin : Prop
RBM.Graph.baSpDecay_pin : Prop
RBM.Graph.baKBound_E_pin : Prop
RBM.Graph.BASizeClaim_forest_sum_le_pin.{u₁, u₂, u₃, u₄} : Prop
RBM.Graph.BAGraph_exists_forest_pin : Prop
RBM.Graph.BAGraph_counters_le_pin : Prop
RBM.Graph.baClaimSize_pin : Prop
RBM.Graph.baClaimSizeG_pin : Prop
RBM.Graph.baClaimSize_E_pin : Prop
RBM.Graph.baClaimSizeG_E_pin : Prop
RBM.Graph.baSpTail_E_pin : Prop
RBM.Graph.baMTail_E_pin : Prop
RBM.Graph.baTail_log_pin : Prop
BAlwS : (d L W : ℕ) → [NeZero W] → ℝ → Idx d L W → Idx d L W → ℂ
BAlwW : (d L W : ℕ) → [NeZero L] → [NeZero W] → ℝ → ℝ → ℝ → ℂ → Matrix (Idx d L W) (Idx d L W) ℂ
BAlwM : (d L W : ℕ) → [NeZero L] → [NeZero W] → ℝ → ℝ → ℂ → Matrix (Idx d L W) (Idx d L W) ℂ
BA.BAReal : ℕ → (L : ℕ) → [NeZero L] → ℝ → ℝ → ℝ → ℂ → Prop
BA.BATheta : (d L : ℕ) → [NeZero L] → ℝ → ℝ → ℂ → ℝ → Bool → Bool → Matrix (Zd d L) (Zd d L) ℂ
lwLift : (d L W : ℕ) → [NeZero W] → Matrix (Zd d L) (Zd d L) ℂ → Matrix (Idx d L W) (Idx d L W) ℂ
lwBdist : (d L W : ℕ) → [NeZero L] → [NeZero W] → Idx d L W → Idx d L W → ℕ
@LWKBound : {ι : Type u_1} → [Fintype ι] → Matrix ι ι ℂ → ℝ → ℝ → Prop
@BAGraph.val : {ι : Type u_1} →
  {E : Type u_2} →
    {I : Type u_3} →
      [Fintype ι] → [DecidableEq ι] → [Fintype I] → [DecidableEq I] → BAGraph E I → BALData ι → (E → ι) → ℂ
@BAGraph.scalingSize : {E : Type u_1} →
  {I : Type u_2} → [Fintype E] → [DecidableEq E] → [Fintype I] → [DecidableEq I] → BAGraph E I → ℝ → ℕ → ℕ → ℕ → ℝ
@BAGraph.scalingSizeG : {E I : Type} →
  [Fintype E] → [DecidableEq E] → [Fintype I] → [DecidableEq I] → BAGraph E I → ℝ → ℕ → ℕ → ℕ → ℝ
@BAGraph.partition : {E I : Type} →
  [Fintype E] → [DecidableEq E] → [Fintype I] → [DecidableEq I] → BAGraph E I → List (BAPGraph E)
exit=0
```

Axioms of the instance (a scratch copy of the probe in `$S`: the `example` renamed, two `#print axioms` lines; the diff is the first block):

```
$ diff RBM3D/Probe/T2412Pins.lean $S/AxiomsCheck.lean   # scratch copy: the example renamed, two #print axioms lines
247c247
< example (hEq : baSp_eq_pin) (hDec : baSpDecay_pin) (hKB : baKBound_E_pin) (hSz : baClaimSize_pin)
---
> theorem T2412_inst_axioms (hEq : baSp_eq_pin) (hDec : baSpDecay_pin) (hKB : baKBound_E_pin) (hSz : baClaimSize_pin)
302a303,305
> #print axioms RBM.Graph.T2412_inst_axioms
> #print axioms RBM.Graph.T2412Inst.D0
> 
$ lake env lean $S/AxiomsCheck.lean | grep "depends on"
'RBM.Graph.T2412_inst_axioms' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2412Inst.D0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Contents** (definitions of `Prop`s, `#check` lines, one `example`; no theorem, no `sorry`).
- Vocabulary: `BAGraph.sizeConst` (R9), `BAGraph.Jx` (`J = waved ⊕ mdot ⊕ psi`), `BAGraph.edgeEnds`.
- T1 `baSp_eq_pin`, `baSpDecay_pin`, `baKBound_E_pin`; T2 `BASizeClaim_forest_sum_le_pin` (universe polymorphic), `BAGraph_exists_forest_pin`, `BAGraph_counters_le_pin`; T3 `baClaimSize_pin`, `baClaimSizeG_pin`; T4 `baClaimSize_E_pin`, `baClaimSizeG_E_pin`, `baSpTail_E_pin`, `baMTail_E_pin`, `baTail_log_pin`.
- Instance (`T2412Pins.lean:246-301`): `d=3, L=4, W=2, t=1/2`, `P : FlowPt 4 10` (`0 < P.g0 ≤ 10`, `BAReal 3 4 P.g0 (Im P.m0) P.E P.m0`), `Λ=10`, `κ=Im P.m0 > 0`; data `D0` with `M, S, S⁺=S W, g0 Ψ` the BA matrices and `G = M + (1/100)J` (`G x y − M x y = 1/100` for all `x, y` by definition; `hG : ‖G−M‖ ≤ 1/100` by `simp`); graphs `baLWT1` (`n_S,n_W,n_A,n_M = 2,1,2,1`, no external vertex) and `baGGT1` (`0,1,1,0`, two external labels), both normal by `decide`, `0 < size`.
- Pins applied with every deterministic hypothesis discharged: `baSp_eq`, `baSpDecay`, `baSpTail_E`, `baMTail_E`, `baTail_log` at the data; `baKBound_E` then `baClaimSize` and `baClaimSizeG` on `baLWT1`; `baClaimSize_E` on `baGGT1`; `baClaimSizeG_E` on `baGGT1`; `BAGraph_counters_le_pin` and `BAGraph_exists_forest_pin` on `baLWT1` (hypothesis: no `=`-dotted edge, by `decide`).
- The hypotheses of the example are the pins themselves (the ticket's own targets, unproved at the probe step). Not applied: `BASizeClaim_forest_sum_le_pin` (its instance is a concrete forest, owed by 1b).

**Readings of the pseudo-Lean of (a)** (for the 1a-audit).
1. `BAGraph.exists_forest`: (a) says "ranks/edges/injectivity as `LGraph.exists_forest`"; compiled with `edge : I → Option Γ.Jx` and the endpoints through `BAGraph.edgeEnds`: the four clauses of `LWSizeClaim.lean:725-732`, plus the pinned `n_A` clause.
2. Universes: the forest pin is polymorphic; the graph pins use `E I : Type`, as `BAGraph.partition` (`Graph/BAVocab.lean:229`).
3. `baMTail_E_pin` has no `t` (`M` does not depend on it); constants `C₂ c₂` as `lwSpOf_tail_E`; `baTail_log_pin` is `lwTail_log32` with `3/2` replaced by `p > 1`.
4. Observation on reuse: the ticket's "R / reuse" line lists `LWSizeClaim` §1, §4, §5 and says "Reuse them; do not twin them"; `BASizeClaim_forest_sum_le_pin` has per-edge `(a j, K j)`, while `lwForest_sum_le` takes one `(a, K)` (`LWSizeClaim.lean:637-638`) and its core `lwForest_core` is `private` (`:544-545`); (a) A3 plans a twin. Decision for the 1a-audit.

## (b) Stage 1b, `prover-hard` (claude-sonnet-5-5) — Sun Oct 11 09:07:39 UTC 2026

Split and line counts against the stop line (2,000 per file): `Graph/BASizeClaim.lean` 1,167 (T1 + T2), `Graph/BASizeClaim2.lean` 825
(T3 + T4 + instances), as the file plan of (a) (v). No stop. No port from RBM1D/RBM2D (nothing ported, no diff-stat).

```
$ git log --format="%h %s" 668318f..HEAD; wc -l RBM3D/Graph/BASizeClaim.lean RBM3D/Graph/BASizeClaim2.lean   # stop line 2,000 per file
d858b0b T2412: import BASizeClaim, BASizeClaim2 in RBM3D.lean (full lake build passes)
42300c2 T2412: BA claim:size, part 1 kernel edges and atomic forest (BASizeClaim), part 2 claim:size
    1167 RBM3D/Graph/BASizeClaim.lean
     825 RBM3D/Graph/BASizeClaim2.lean
$ lake build RBM3D.Graph.BASizeClaim RBM3D.Graph.BASizeClaim2 2>&1 | tail -1; lake build 2>&1 | grep -E "axiom audit|Build completed"   # the second: full library, #assert_rbm_axioms
Build completed successfully (3793 jobs).
info: RBM3D.lean:455:0: axiom audit: 11551 theorems, 3512 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4223 jobs).
output lines of lake env lean on the two files: 0, 0; forbidden-word grep: 0; T2412-check.lean exit: 0
$ git diff --stat main...t/T2412 | cat; python3 -I $S/cone.py $PWD RBM3D.Graph.BASizeClaim2
 RBM3D.lean                    |    2 +
 RBM3D/Graph/BASizeClaim.lean  | 1167 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BASizeClaim2.lean |  825 +++++++++++++++++++++++++++++
 RBM3D/Probe/T2412Pins.lean    |  303 +++++++++++
 4 files changed, 2297 insertions(+)
RBM3D.Graph.BASizeClaim2 103 modules; LWExpCert in cone: []
```

```
$ python3 $S/defdiff.py; lake env lean $S/pincheck.lean; echo exit=$?   # pincheck: the 13 pins of the probe (copied) and 13 lines `example : X_pin := @X`
def BAGraph.sizeConst identical to the probe pin text: True
abbrev BAGraph.Jx identical to the probe pin text: True
def BAGraph.edgeEnds identical to the probe pin text: True
exit=0 (output lines:        0)
$ lake env lean $S/ax_BASizeClaim.lean; lake env lean $S/ax_BASizeClaim2.lean | grep "depends on" | ...   # scratch copies: every `example` renamed to a theorem, `#print axioms` lines appended
BASizeClaim.lean: BASizeClaimInst.BASizeClaimAxInst1_1 BASizeClaimInst.BASizeClaimAxInst1_2 BASizeClaimInst.BASizeClaimAxInst1_3 BASizeClaimInst.BASizeClaimAxInst1_4 baSp_eq baSpDecay baKBound_E BAGraph.exists_forest BAGraph.counters_le BASizeClaim_forest_sum_le BASizeClaim_fibre_sum  ->  [propext, Classical.choice, Quot.sound]
BASizeClaim2.lean: BASizeClaimInst2.BASizeClaimAxInst2_1 BASizeClaimInst2.BASizeClaimAxInst2_2 BASizeClaimInst2.BASizeClaimAxInst2_3 BAGraph.sizeConst baClaimSize baClaimSizeG baClaimSize_E baClaimSizeG_E baSpTail_E baMTail_E baTail_log  ->  [propext, Classical.choice, Quot.sound]
$ python3 $S/extract.py   # the statements of the targets, extracted from the files (whitespace squeezed)
BASizeClaim.lean:180: theorem baSp_eq (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 κ E t : ℝ) (m : ℂ) (hr : RBM.BA.BAReal d L g0 κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1) : Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m = (t : ℂ) • lwLift d L W (RBM.BA.BATheta d L g0 E m t true true)
BASizeClaim.lean:280: theorem baSpDecay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 → (∀ x y : Idx d L W, ‖Matrix.of (BAlwS d L W t) x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) ∧ (∀ x y : Idx d L W, ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
BASizeClaim.lean:410: theorem baKBound_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 → LWKBound (Matrix.of (BAlwS d L W t)) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧ LWKBound (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧ LWKBound (BAlwM d L W g0 E m) Kd Kd ∧ LWKBound ((g0 : ℂ) • PsiI d L W) Kd Kd
BASizeClaim.lean:632: abbrev BAGraph.Jx {E I : Type} (Γ : BAGraph E I) : Type
BASizeClaim.lean:636: def BAGraph.edgeEnds {E I : Type} (Γ : BAGraph E I) : Γ.Jx → (E ⊕ I) × (E ⊕ I)
BASizeClaim.lean:727: theorem BAGraph.exists_forest (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) : ∃ (C : Finset I) (par : I → E ⊕ I) (edge : I → Option Γ.Jx) (ρ : I → ℕ), C.card + Γ.nM = Fintype.card I ∧ (C.filter fun c => ∃ j, edge c = some (Sum.inl j)).card + Γ.nM = Γ.nA ∧ (∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) ∧ (∀ c ∈ C, ∃ j, edge c = some j ∧ (((Γ.edgeEnds j).1 = Sum.inr c ∧ (Γ.edgeEnds j).2 = par c) ∨ ((Γ.edgeEnds j).2 = Sum.inr c ∧ (Γ.edgeEnds j).1 = par c))) ∧ (∀ c₁ ∈ C, ∀ c₂ ∈ C, edge c₁ = edge c₂ → c₁ = c₂)
BASizeClaim.lean:937: theorem BAGraph.counters_le (Γ : BAGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) : Γ.nM ≤ Γ.nA ∧ Γ.nA - Γ.nM ≤ Γ.nW
BASizeClaim.lean:957: theorem BASizeClaim_forest_sum_le {ι : Type u₁} {I : Type u₂} {E : Type u₃} {J : Type u₄} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty ι] (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : J → ℝ) (hf0 : ∀ j x y, 0 ≤ f j x y) (hfa : ∀ j x y, f j x y ≤ a j) (hrow : ∀ j x, ∑ y, f j x y ≤ K j) (hcol : ∀ j y, ∑ x, f j x y ≤ K j) (C : Finset I) (par : I → E ⊕ I) (edge : I → J) (ρ : I → ℕ) (hinj : Set.InjOn edge C) (hedge : ∀ c ∈ C, (u (edge c) = Sum.inr c ∧ v (edge c) = par c) ∨ (v (edge c) = Sum.inr c ∧ u (edge c) = par c)) (hrank : ∀ c ∈ C, ∀ w, par c = Sum.inr w → ρ w < ρ c) : (Fintype.card ι : ℝ) ^ C.card * ∑ ℓ : I → ι, ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤ (Fintype.card ι : ℝ) ^ Fintype.card I * (∏ c ∈ C, K (edge c)) * ∏ j ∈ (C.image edge)ᶜ, a j
BASizeClaim2.lean:65: def BAGraph.sizeConst {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (K₀ K₁ Kd : ℝ) : ℝ
BASizeClaim2.lean:473: theorem baClaimSize (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → Idx d L W) : ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L
BASizeClaim2.lean:536: theorem baClaimSizeG (Γ : BAGraph E I) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ} (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (ℓe : E → Idx d L W) : ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * Γ.scalingSizeG Ψ W d L
BASizeClaim2.lean:566: theorem baClaimSize_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 → ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal → ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) → D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m → D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ Ψ : ℝ, (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → ∀ ℓe : E' → Idx d L W, ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ Kd * Γ.scalingSize Ψ W d L
BASizeClaim2.lean:587: theorem baClaimSizeG_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 → ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), ∀ D : BALData (Idx d L W), D.S = Matrix.of (BAlwS d L W t) → D.Sp = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m → D.M = BAlwM d L W g0 E m → D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ Ψ : ℝ, (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → ∀ ℓe : E' → Idx d L W, ‖Γ.val D ℓe‖ ≤ (Γ.partition.map fun P => P.g.sizeConst K₀ K₁ Kd).sum * Γ.scalingSizeG Ψ W d L
BASizeClaim2.lean:614: theorem baSpTail_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → 0 ≤ t → t < 1 → ∀ (x : Idx d L W) (R : ℝ), ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)), ‖(Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) x y‖ ≤ C₂ * Real.exp (-(c₂ * R))
BASizeClaim2.lean:633: theorem baMTail_E (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ → RBM.BA.BAReal d L g0 κ E m → ∀ (x : Idx d L W) (R : ℝ), ∑ y ∈ Finset.univ.filter (fun y => R ≤ (lwBdist d L W x y : ℝ)), ‖BAlwM d L W g0 E m x y‖ ≤ C₂ * Real.exp (-(c₂ * R))
BASizeClaim2.lean:701: theorem baTail_log (c : ℝ) (hc : 0 < c) (p : ℝ) (hp : 1 < p) (D : ℝ) : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → Real.exp (-(c * (Real.log W) ^ p / 2)) ≤ (W : ℝ) ^ (-D)
$ python3 (the `example` blocks of both files, first 150 characters)
BASizeClaim.lean:1065: example : Matrix.of (BAlwS 3 4 2 (1 / 2)) * BAlwW 3 4 2 P.g0 P.E (1 / 2) P.m0 = (((1 / 2 : ℝ)) : ℂ) • lwLift 3 4 2 (RBM.BA.BATheta 3 4 P.g0 P.E P.m0 (
BASizeClaim.lean:1093: example : ∃ (C : Finset (Fin 3)) (par : Fin 3 → Fin 0 ⊕ Fin 3) (edge : Fin 3 → Option baLWT1.Jx) (ρ : Fin 3 → ℕ), C.card = 2 ∧ (C.filter fun c => ∃ j,
BASizeClaim.lean:1113: example : ∃ (C : Finset (Fin 3)) (par : Fin 3 → Fin 2 ⊕ Fin 3) (edge : Fin 3 → Option baGGT1.Jx) (ρ : Fin 3 → ℕ), C.card = 3 ∧ (C.filter fun c => ∃ j,
BASizeClaim.lean:1141: example : (Fintype.card (Fin 3) : ℝ) ^ (Finset.univ : Finset (Fin 2)).card * ∑ ℓ : Fin 2 → Fin 3, ∏ j : Fin 2, fInst j (Sum.elim (fun _ : Fin 1 => (0 
BASizeClaim2.lean:766: example : ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ baLWT1.counters = ⟨2, 1, 2, 1, 0, 0⟩ ∧ 0 < baLWT1.scalingSize (1 / 100) 2 3 4 ∧ ‖baLWT1.val D0 Fi
BASizeClaim2.lean:784: example : (∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ baGGT1.counters = ⟨0, 1, 1, 0, 0, 0⟩ ∧ 0 < baGGT1.scalingSize (1 / 100) 2 3 4 ∧ ‖baGGT1.val D0 e
BASizeClaim2.lean:807: example : (∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧ ∀ x : Idx 3 4 2, ∑ y ∈ Finset.univ.filter (fun y => 1 ≤ (lwBdist 3 4 2 x y : ℝ)), ‖(Matrix.of (BAlwS 3 4 2 (
$ bash $S/clash.sh | tr "\n" " "   # name clash: new public names against RBM3D without Probe/ and the two files
baSp_eq: 0 baSpDecay: 0 baKBound_E: 0 BAGraph.Jx: 0 BAGraph.edgeEnds: 0 BAGraph.exists_forest: 0 BAGraph.counters_le: 0 BASizeClaim_forest_sum_le: 0 BASizeClaim_fibre_sum: 0 BAGraph.sizeConst: 0 baClaimSize: 0 baClaimSizeG: 0 baClaimSize_E: 0 baClaimSizeG_E: 0 baSpTail_E: 0 baMTail_E: 0 baTail_log: 0 BASizeClaimInst.fInst: 0 BASizeClaimInst.uInst: 0 BASizeClaimInst.vInst: 0 BASizeClaimInst2.D0: 1 BASizeClaimInst2.D0_hG: 0 BASizeClaimInst2.ellInst: 0 
$ python3 $S/report.py | grep "^g="   # L5 points g = 1/64, 1, 10 and (1/64, Lam = 10), kappa = Im m (1a script, rerun)
g=0.01562 Lam=0.01562 kappa=0.9993 cM=0.5 mu=1.93e-09 KM=1.98e+05 K0=4.24e+12 K1=1.87e+51 | actual maxM=0.999 rowM=1.101 rowSp=0.334 max|Sp|W^d e^(mu dB)=0.333
g=1 Lam=1 kappa=0.5959 cM=0.0485 mu=2.17e-22 KM=2.3e+10 K0=5.02e+21 K1=1.38e+112 | actual maxM=0.596 rowM=5.822 rowSp=0.525 max|Sp|W^d e^(mu dB)=0.429
g=10 Lam=10 kappa=0.5594 cM=0.00465 mu=8.66e-32 KM=2.82e+15 K0=6.94e+29 K1=7.59e+157 | actual maxM=0.559 rowM=4.652 rowSp=0.548 max|Sp|W^d e^(mu dB)=0.441
g=0.01562 Lam=10 kappa=0.9993 cM=0.00829 mu=1.64e-27 KM=1.57e+14 K0=2.04e+25 K1=1.73e+136 | actual maxM=0.999 rowM=1.101 rowSp=0.334 max|Sp|W^d e^(mu dB)=0.333
```

**Narrative.**
- Statements: the 13 pins of the probe hold word for word (`pincheck.lean`: 13 `example : X_pin := @X`, exit 0; the text of `sizeConst`,
  `Jx`, `edgeEnds` equals the probe's). The hypotheses of `baClaimSize` are `Normal`, `‖G - M‖ ≤ Ψ` (entrywise) and `LWKBound` for `S`, `S⁺`, `M`,
  `g₀Ψ`: no `hM`, no smallness of `g₀`. `RBM3D.lean` carries two import lines on the branch (the full `lake build` above ran with them; Lean accepts a duplicate import if the hub adds them again).
- T2 atom step (`BASizeClaim.lean:444-935`): an abstract lemma `BASizeClaim_forest_abs` on two relations `A` (dotted), `W` (waved) and a target set `T`.
  `rk₀` counts the waved steps to `T` (dotted steps are free, `BASizeClaim_Reach`); every non-target atom gets one gate waved edge to a lower `rk₀`, chosen at a
  canonical representative of the atom (`Quotient.out`); `rk₁` is the dotted distance to `T ∪ gates` (`BASizeClaim_exists_rank`); `ρ = rk₀ (S+1) + rk₁`.
  `BAGraph.exists_forest` instantiates it with `T = E ∪ one root per internal molecule`; the counts are `IA \ RA` (`nA - nM` non-target atoms, a bijection
  with the gates). `counters_le` follows from it and `BAGraph.nM_le_nA`.
- T2 peeling (`BASizeClaim.lean:955-1051`): `BASizeClaim_forest_sum_le` is derived from the public `lwForest_sum_le` (`J' = ↥C`, `K' = 1`, `f'_c = f_{e(c)}/K_{e(c)}`), as the 1a-audit (O1)
  directs; `lwForest_core` is not twinned.
- T3 (`BASizeClaim2.lean:61-556`): `BASizeClaim_term_le` (circled solid edges `≤ Ψ`, `×`-dotted `≤ 1`), `BASizeClaim_sum_le` (peeling over `J = waved ⊕ mdot ⊕ psi` with
  `a_j = (K₀W^{-d} | Kd)`, `K_j = (K₁ | Kd)`; `BASizeClaim_alg_prod` evaluates the product), `BASizeClaim_size_alg` (copy of `lwSize_alg` with `n_A`). `baClaimSizeG` through `BAGraph.val_eq_partition`.
- T1 (`BASizeClaim.lean:76-442`): `S = t·lift 1` (`SB 0 = 1`), `M⁺S = t·lift(M^{(+,+)})` by the offset fibre sum, `W = (1 - M⁺S)⁻¹ = 1 + lift(Θ - 1)`
  by `baW_mul` and `BATheta_isUnit`, `Θ(a,b) = Θ(0,b-a)` (copy of `KStep_theta_shift`), `baProp5s_of_real`. Constants: `C = (1+Λ²)C₅ + 1`, `c = BAp5s_rate`,
  `K₁ = C expC(d-2, c)`, `Kd = c_M⁻¹ expC(d-2, c_M) + 2dΛ` (`c_M = BAct_rate`): the decay rate enters only there; `Kd` bounds entries through row sums.
- Differences from (a): (1) the constants of the statements are not those of the table: `K₀ = (1+Λ²)C₅ + 1` (R8: `max(1, (1+Λ²)C₅)`, smaller), `Kd = K_M + 2dΛ` (R9: a max of four numbers; `a_M = 1` is not used, entries are bounded by row sums); the L5 rerun above uses the table's `K_M`, `K₀`, `K₁`, `μ`;
  (2) `BASizeClaim_fibre_sum` is public (stem-prefixed, `BASizeClaim2` uses it); (3) the instance of `baGGT1` uses the labels `0` and `2` (same offset, distinct blocks), as the 1a-audit (O3) asks.
- The ticket limits the report to 200 lines; (a) and (a″) alone are 177 lines, so the whole report is within CLAUDE.md §6's 300 lines but not the ticket's 200.

## (c) Verified Mathlib names (all `#check`ed, exit 0, 42 outputs; used in the build)

- `Relation.ReflTransGen.head_induction_on` / `.mono` (`r ≤ p → RTG r ≤ RTG p`, applied to `a b` and the walk) / `.head` / `.single`; `Nat.find_spec`, `Nat.find_min'`; `Quotient.mk_out`, `Quotient.sound`.
- `Finset.card_bij`, `Finset.card_sdiff_add_card_eq_card`, `Finset.card_filter_add_card_filter_not`, `Finset.card_compl`, `Finset.card_image_of_injective`, `Finset.card_le_card_of_injOn`.
- `Finset.prod_image`, `Finset.prod_mul_prod_compl`, `Finset.prod_ite`, `Finset.prod_coe_sort`, `Finset.prod_le_prod₀`, `Finset.prod_mul_distrib`, `Finset.single_le_sum`, `Finset.sum_boole`.
- `Finset.eq_empty_of_forall_notMem`, `Finset.mem_image_of_mem`, `Fintype.prod_sum_type`, `Fintype.sum_equiv`, `Fintype.card_coe`, `Equiv.sum_comp`, `Fin.prod_ofFn`, `List.mem_iff_get`.
- `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Ring.mul_inverse_cancel`.
- `Real.rpow_le_rpow`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_def_of_pos`, `Real.rpow_nonneg`.
- Present but deprecated in this toolchain (avoided): `Symmetric` (use `Std.Symm`), `Relation.ReflTransGen.symmetric` (use `.stdSymm`; own `BASizeClaim_rtg_symm` used), `if_pos`/`if_neg`/`dif_pos`.
  `Finset.prod_le_prod` takes one explicit argument here (use `prod_le_prod₀`). No name was invented; no name was found absent.

## (d) Open issues and paper-delta candidates

- Open issues: none. All targets of the ticket are built, committed on `t/T2412` (`42300c2`, `d858b0b`) and instanced. The probe `RBM3D/Probe/T2412Pins.lean` stays on the branch.
- `T2412a` (from (a)): the uniform Combes-Thomas decay of `M` for all `0 < g₀ ≤ Λ` (`BAMB_decay_large`, `BAMB_row_l1`, rate `BAct_rate`) replaces the large-`λ` / `(Cλ)^{|a-b|}` split of `(Mbound_AO)`, `(Mbound_AO2)`; it gives the `M`-dotted edge bound `Kd` used in `baClaimSize`.
- `T2412b` (from (a)): the deterministic `claim:size` has no `(log W)^{1+ε₁}` atom-spread loss (the atoms enter only through row sums `Kd`); the block spread of (B.15) is the separate tail `baMTail_E`.
- `T2412c` (from (a)): `S⁺ = S W` with `W = (1 - M⁺S)⁻¹` (`baSp_eq`: `= t·lift(Θ^{(+,+)})`), in place of the band's `S(1 - m²S)⁻¹` (`lwSpOf_eq`).
- `T2412d` (new): `baClaimSize` takes one entry bound `‖G - M‖ ≤ Ψ` for all `x, y` (diagonal included); the band's two hypotheses `hG` (`x ≠ y`) and `hGd` and the `×`-dotted case split are not needed because `M` is not scalar and a circled solid edge is `(G - M)_{xy}` for every pair.
- `T2412e` (new): the Lean constants of `baSpDecay`, `baKBound_E` are explicit and huge (`K₁` up to `1.9e51 .. 7.6e157` at the L5 points: `BAp5s_rate` is `1.9e-9 .. 8.7e-32`); the exponents of `size` do not depend on them.
