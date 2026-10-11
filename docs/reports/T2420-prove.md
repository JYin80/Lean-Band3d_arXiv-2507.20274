Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 11:01 UTC 2026

### (i) Exponent table, and the G3 argument

Notation: `N=(WL)^d`, `Idx = Zd d L × offsets`, `[x]` the block of `x`, `d_B = lwBdist`. Counters `(n_S,n_W,n_A,n_M)`, `n_V=|I|`, `|E⊕I| = 7` in the instance. `c_M=BAct_rate`, `μ=BAp5s_rate`, `κ ≤ Im m` (`BAReal`), `0<g≤Λ`, `0≤t<1`, `L≥3`, `3≤d` (formulas of `T2412-prove.md` (a)). `B:n` = `paper/tex/B_graphical_lemmas.tex:n`. Scripts: scratchpad `T2420/`.

| # | item | value | constraint | slack |
|---|---|---|---|---|
| E1 | `Ψ`-exponent of (G_by_auxG_BA) | `ord G − auxOrd = (n_S−|𝒢_ℳ|) + 2(n_W−n_A+n_M) = n_S^{within} + 2Σ_i e_i + 2Σ_{ext}(k_i^{ext}−1)`, `e_i = n_W^{(i)}−(k_i−1)` | `≥ 0` by `BAGraph.counters_le` (`n_A−n_M ≤ n_W`) and `|𝒢_ℳ| ≤ n_S` | exact (0 loss); `=3` for `G*` below; 0 iff no solid edge inside a molecule, every molecule a waved tree on its atoms, one external atom per external molecule |
| E2 | `auxOrd` (centre level) vs paper `(eq:ordGaux_BAM)` (`B:486`) | paper: `n_S^{aux}+2Σ(r_i−1)−2(Σ_int r_i+Σ_ext(r_i−r_i^{ext}))`; centre level: `|𝒢_ℳ|−2n_M` | paper order = centre order `+2Σ_ext(r_i^{ext}−1)`; equal iff `r_i^{ext}=1`, i.e. the external atom is the centre (band convention `α_x≡x`, `7_8:897`; BA `B:421-422` has `α_i≡x_{i,1}`) | for `r_i^{ext}≥1` the centre-level exponent is `≥` the paper's, so the centre-level G3 is the stronger; T2387 row 15's `k^{ext}−r^{ext}` is `k^{ext}−1` at `r^{ext}=1` |
| E3 | `Ψ`-count of one non-tree waved edge | `K₀W^{-d} ≤ K₀AΨ²`, window `W^{-d} ≤ AΨ²`, `A = g²+1 = 1.00024 / 2 / 101` at `g=1/64, 1, 10` (`STBctl_ge`: `W^{-d} ≤ (ilambda²+1)B`, `ilambda=g`, `LWExpTerm6.lean:34`; band window `W^{-d/2}≤Ψ` is `A=1`) | `A≥0` only; no smallness of `g`; `A^{n_W−n_A+n_M}` enters `C_Γ` | instance: `W^{-d}=0.125 ≤ AΨ²=0.25A`, slack factor `2A` |
| E4 | forest edge counts (`BAGraph.exists_forest`, `BASizeClaim.lean:727`) | `|C|=n_V−n_M`: gate waved edges `n_A−n_M`, dotted tree edges `n_V−n_A`; non-tree waved `n_W−(n_A−n_M)`; non-tree `M`/`Ψ`-dotted `#mdot+#psi−(n_V−n_A)` | tree waved edge costs `K₁` (offset sum included), tree dotted `Kd`, non-tree entry `K₀AΨ²` resp. `Kd`; any extra tree waved edge would lose `W^d` | counted by script on `G*`: 2 gate, 2 dotted tree, 1 non-tree waved |
| E5 | `W`, `L` power | `(W^d)^{n_M}·auxVal`, `auxVal=Σ_{b:AuxIMol→Zd}∏_{𝒢_ℳ}ξ` (one fine root per internal molecule gives `N=W^dL^d`; the blocks are summed in `auxVal`) | roots-as-externals use of `BASizeClaim_forest_sum_le` (`I:=C`, `E:=E⊕roots`) gives `Σ_children ≤ ∏K∏a` | exact |
| E6 | kernel constants | `(K₀,K₁,Kd)` of `baKBound_E` (`BASizeClaim.lean:410`), `(d,Λ,κ)` only. Formula values `g=1/64,1,10` (`Λ=g`): `K₀=4.2e12/5.0e21/6.9e29`, `K₁=1.9e51/1.4e112/7.6e157`, `Kd=2.0e5/2.3e10/2.8e15`; actual (instance): `K₀=.5/.5/.5`, `K₁=.500/.525/.548`, `Kd=1.10/6/60` | `K₀W^{-d}`: entries; `K₁`: row and col sums of `S,S⁺`; `Kd`: entries and row/col sums of `M`, `gΨ` | formula constants only enter `C_Γ`; astronomically large but never a hypothesis of an instance |
| E7 | confinement radius, tail | confined: every `J=waved⊕mdot⊕psi` edge has `d_B ≤ r`, then every vertex is within `|E⊕I|r ≤ R` of its molecule's root block (path of `≤|E⊕I|` edges, triangle); else tail `e^{-cr/2}C'size` | decay rate `c=min(c_M,μ)=1.9e-9 / 2.2e-22 / 8.7e-32` at `g=1/64,1,10`; `R ≥ |E⊕I|r` | tail uses weights `e^{(c/2)d_B}` on all four kernels, `Kᵂ = C·expC(d−2,c/2)`; `r=(log W)^{1+ε₁}`: `e^{-cr/2} ≤ W^{-D}` iff `log W ≥ (2D/c)^{1/ε₁}`: `log₁₀ log W₀ = 190/449/637` (`D=3, ε₁=1/20`) — eventual only, not used by G3 |
| E8 | `scaleatom` (`B:317-318`) | offset equality exact: `M_{xy}=1(o_x=o_y)M^B` (`BAMfine_eq`, `GreenSchur.lean:93`), `gΨ_{xy}=g1(o_x=o_y)1(adj)`; block spread `≤|E⊕I|r` on the support up to `c_M^{-1}e^{-c_M r}` per `M`-edge (`BAMB_decay_large`), block distance `≤1` per `Ψ`-edge (nearest neighbour) | deterministic; the paper's `e^{-c(log W)^{1+ε₁}}` is the `r` above | no `g`-smallness, no `(Cλ)^{|a−b|}` (L5) |
| E9 | nested form, G4 | `p` walks, `q=n_M`, `Γa.ordN = auxOrd`, `NoGhost`, `IsNested`; needs `n_M ≤ p` (`LWAnp` hyp `q ≤ p`) | the walks are properties of the molecular graph only | `n_M ≤ p` is a hypothesis of the G4 pin, as in `LWAnp` (`LWPins.lean:409`) |

**G3 argument (closes, no REQ).** Reused unchanged from `lwGtoAG_holds` (`AuxGraph.lean:1018`): `auxGraph_bdist_triangle/_self` (§3), the list lemmas (§4), `auxGraph_sum_blocks` (§7), `auxGraph_one_le_prod`, `auxGraph_prod_exp_ge` (§8), the assembly of the final `calc` (§10). New twins: vocabulary, `confinement`, pointwise bound, forest with roots, tail data.
- A1 (aux graph). `BAGraph.shadow` = `Γ` with every `M`-/`Ψ`-dotted edge also a waved edge: same adjacency as `BAGraph.adj`, so the molecules, `n_M`, `IsExtMol`, `molSolid` coincide; `auxVal`, `auxOrd := shadow`'s. The retained atoms `x_{i,j}` (`B:448`) are folded into the centre: a solid edge at an atom `β` of `𝓜_i` is `≤ ξ([α_i],·)` by the `hξ`-domination on `R`-balls (`(Gyiyjatom)`, `B:424`), `α_i` = the forest root. Orders agree (E2); the retained atoms are not needed for the bound (they were for the Ward step of G4, which only sees `ξ`).
- A2 (pointwise, confined). Normal ⇒ every solid edge circled, `|Ǧ_{xy}| ≤ Ψ` (`‖G−M‖≤Ψ` entrywise, no `x≠y` case). Inside a molecule: `Ψ` each (`n_S^{within}`); between molecules: `ξ(a_i,a_j)`; waved/`M`/`Ψ`-dotted/`×`-dotted factors as in `BASizeClaim_term_le` (`×`: `≤1`).
- A3 (sum over the labels). Roots `r_i` (internal molecule ↔ non-`C` vertex: each internal molecule has a non-`C` vertex by following `par` to decreasing rank, and `|I∖C| = n_M`, so exactly one each, none in an external molecule) fixed; `BASizeClaim_forest_sum_le` with per-edge `(a_j,K_j)` for the children gives `(∏_{C}K)∏_{non-tree}a`, then `Σ_{roots}=(W^d)^{n_M}Σ_{blocks}` (`auxGraph_sum_blocks`). Result `C_Γ(K₀A,K₁,Kd)·Ψ^{n_S^{within}+2(n_W−n_A+n_M)}(W^d)^{n_M}auxVal`.
- A4 (tail). Some `J`-edge `>r`: weight `S,S⁺,M,gΨ` by `e^{(c/2)d_B}` (`G' := G−M+M'` keeps `G'−M' = G−M`); the product of weights `≥e^{(c/2)r}`; apply `baClaimSize`'s peeling to the weighted data (offset-diagonal `M`, `gΨ` give row sums `C·expC(d−2,c/2)` through the fibre sum, as `baMTail_E`, `BASizeClaim2.lean:633`).
- A5 (what the BA graph has that the band has not): the `M`/`Ψ`-dotted tree edges inside atoms (`Kd`), gate waved edges (`K₁`), no `hM : M=mI`. `G4` needs no non-centre sums: with the centre-level `auxVal` the NGraph is `lwAuxNested_holds` (`AuxGraph.lean:1606`) on `shadow`.

**Pins (pseudo-Lean, `namespace RBM.Graph`; a separate step compiles them in `RBM3D/Probe/T2420Pins.lean`).**
```
def BAGraph.shadow (Γ : BAGraph E I) : LGraph E I := ⟨Γ.solid, Γ.waved ++ Γ.mdot.map toW ++ Γ.psi.map toW, Γ.dotted, Γ.coeff⟩
theorem BAGraph.shadow_mol : Γ.shadow.mol v = Γ.mol v ;  theorem BAGraph.shadow_nM : Γ.shadow.nM = Γ.nM
def BAGraph.auxVal Γ ξ be := Γ.shadow.auxVal ξ be ; def BAGraph.auxOrd Γ := Γ.shadow.auxOrd   -- = ord ⟨|molSolid|,0,nM,0,0,0⟩
theorem BAGraph.scalingOrder_sub_auxOrd : Γ.scalingOrder - Γ.auxOrd = ((Γ.nS:ℤ) - |molSolid|) + 2*((Γ.nW:ℤ) - Γ.nA + Γ.nM)
theorem BAGraph.auxOrd_le_scalingOrder (hN : Γ.Normal) : Γ.auxOrd ≤ Γ.scalingOrder
-- scaleatom, Gyiyjatom, Gyiyjatom2 (deterministic)
theorem baAtom_offset (hM : ∀ x y, (offset x ≠ offset y) → D.M x y = 0) (hP : same for D.gPsi) (h : Γ.term D ℓ ≠ 0) (hv : v ∈ Γ.atom u) :
  (split (ℓ u)).2 = (split (ℓ v)).2
theorem baAtom_dist (hmdot : ∀ e ∈ Γ.mdot, d_B(ℓ e.x)(ℓ e.y) ≤ r) (hpsi : same) (hv : v ∈ Γ.atom u) : (lwBdist (ℓ u) (ℓ v):ℝ) ≤ card (E⊕I) * r
theorem baAtom_sedge_xi (hξ : ∀ x y a b, zdistD([x]-a) ≤ R → zdistD([y]-b) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) (e : SEdge) (circ) (confined) : ‖SEdge.val D ℓ e‖ ≤ ξ (lab e.src) (lab e.dst)
theorem baAtom_wedge (hS : ‖D.S x y‖ ≤ C*(W^d)⁻¹*exp(-(c*d_B))) : ‖D.S x y‖ ≤ C*(W^d)⁻¹*((if d_B x y ≤ r then 1 else 0) + exp(-(c*r)))   -- same for Sp
-- G3, deterministic (twin of LWGtoAG)
def BAGtoAG (d : ℕ) : Prop := 3 ≤ d → ∀ (L W) [NeZero L] [NeZero W] {E I} (Γ : BAGraph E I), Γ.Normal →
  (∀ a b : E, Γ.mol (inl a) = Γ.mol (inl b) → a = b) → ∀ (D : BALData (Idx d L W)) (Ψ A K₀ K₁ Kd C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
  (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W:ℝ)^d)⁻¹ ≤ A * Ψ^2 →
  LWKBound D.S (K₀*((W:ℝ)^d)⁻¹) K₁ → LWKBound D.Sp (K₀*((W:ℝ)^d)⁻¹) K₁ → LWKBound D.M Kd Kd → LWKBound D.gPsi Kd Kd →
  0 ≤ C → 0 < c → (∀ x y, ‖D.S x y‖ ≤ C*((W:ℝ)^d)⁻¹*exp(-(c*d_B x y))) → (same for D.Sp) →
  (∀ x y, ‖D.M x y‖ ≤ C*exp(-(c*d_B x y)) ∧ ‖D.gPsi x y‖ ≤ C*exp(-(c*d_B x y))) → (∀ x y, offset x ≠ offset y → D.M x y = 0 ∧ D.gPsi x y = 0) →
  0 ≤ r → (card (E⊕I):ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) → (hξ as in baAtom_sedge_xi) → ∀ ℓe,
  ‖Γ.val D ℓe‖ ≤ Γ.sizeConst (K₀*A) K₁ Kd * Ψ^(Γ.scalingOrder - Γ.auxOrd) * (((W:ℝ)^d)^Γ.nM * Γ.auxVal ξ (fun a => [ℓe a]))
      + exp(-(c*r/2)) * Γ.sizeConst C (C*expC (d-2) (c/2)) (C*(1+expC (d-2) (c/2))) * Γ.scalingSize Ψ W d L
theorem baGtoAG_holds (d) : BAGtoAG d ;  theorem baGtoAG_E (d hd Λ κ hΛ hκ) : ∃ K₀ K₁ Kd C c, ... ∀ L W g0 E t m, BAReal .. → D = BAlw data → same conclusion
-- nested form and G4 (owner L3d1)
def BAShadowPG (P : BAPGraph (Fin 2)) : PGraph (Fin 2) := ⟨P.E', P.I', P.ext, P.ext_surj, P.g.shadow⟩
theorem baAuxNested_holds : ∀ p (P : BAPGraph (Fin 2)), 0<p → (BAShadowPG P).LocReg345 p → P.g.mol (inl (P.ext 0)) ≠ P.g.mol (inl (P.ext 1)) →
  ∃ Γa : NGraph p P.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = P.g.auxOrd ∧ ∀ ξ symm, ∀ be, Γa.val ξ (fun _ => be (P.ext 0)) (fun _ => be (P.ext 1)) = P.g.auxVal ξ be
def BAAnpAux (d : ℕ) : Prop := -- G4, B:491-497: the conclusion of LWAnp (LWPins.lean:409) for P.g.auxVal, same hypotheses (STFlow, LWPsiAll, LWXi) plus P.g.nM ≤ p
  3 ≤ d → ∀ κ ε 𝔡 ..., ∀ p (P : BAPGraph (Fin 2)), P.g.nM ≤ p → (BAShadowPG P).LocReg345 p → (mol-distinct) → ∀ ε₀ C₁ C₂ C₃ Cc, ∃ c>0, ∀ 𝔠 sz z, STFlow .. → ∀ t Φ ξ, LWXi sz (STflowE z) t Φ ξ →
    Prec sz (fun n ab ω => P.g.auxVal (ξ n · · ω) (fun e => if e = P.ext 0 then ab.1 else ab.2)) (fun n ab _ => ((W^d)*etaT ..)⁻¹^P.g.nM * Φ n (c*|a-b|)^p * Φ n 0 ^ (P.g.auxOrd - p))
```
G4 inputs from this row: `baAuxNested_holds`, `shadow`, `auxVal`, `auxOrd`. `BAAnpAux d` is the pin of L3d1 (then `LWAnp d → BAAnpAux d` by `baAuxNested_holds`); the BA-flow carrier (`PinFam`) form is fixed by L3c3's 1a (2149 L7), not here.

### (ii) One concrete nondegenerate instance

`d=3, L=4, W=2` (`N=512`, 64 blocks, 8 offsets), `t=1/2`, `E=0`, `m` solving `(self_m)` for `g∈{1/64,1,10}` (`Λ=g`, `κ=Im m`), `M,S,S⁺` the exact BA matrices (`M=M^B⊗I`, `S=tW^{-d}1([x]=[y])`, `S⁺=SW`), `gΨ=g·Ψ^{(B)}⊗I`, `Ψ=1/2` (window `W^{-3/2}=0.354 ≤ 0.5`), `G−M = Ψ·e^{iθ_{xy}}` (`|G−M|=Ψ` for all `x,y`, so `‖G−M‖≤Ψ` is tight; `ξ≡Ψ`, `R=7=|E⊕I|r`, `r=1`, `c=0.2`). No external hypothesis: every datum is computed. Graph `G*` (normal, all solid edges circled, no `=`-dotted): externals `a` (block 0), `b` (block `(1,1,0)`, `d_B=2`), internals `u₁..u₅`; solid `a→u₁`, `u₅→b` (red), `u₃→u₂`, `u₁→u₄`; waved `S(a,u₃)`, `S⁺(u₂,u₄)`, `S(u₁,u₅)`; `M̄`-dotted `u₁u₂`, `Ψ`-dotted `u₄u₅`. Atoms `{a},{b},{u₁,u₂},{u₃},{u₄,u₅}`; molecules `{a,u₃}`, `{b}`, `{u₁,u₂,u₄,u₅}` (internal, `k=2` atoms, `e=1`, one solid edge inside); `hext` holds.
```
$ cd <scratchpad>/T2420; python3 counters.py; python3 consts.py; python3 g3inst.py; python3 g3inst.py coh
nS,nW,nA,nM,nV = 4 3 3 1 5 | |molSolid| = 3 | n_S^within = 1
ord G = 4 | auxOrd(centres) = 1 | exponent ordG-auxOrd = 3 | n_S^within+2(nW-nA+nM) = 3
n_S^within + 2*sum_int e_i + 2*sum_ext(e_i+k_ext-1) = 3
forest: waved gate edges nA-nM = 2 ; dotted tree nV-nA = 2 ; non-tree waved nW-(nA-nM) = 1 ; #mdot+#psi = 2
counters_le: nM<=nA: True ; nA-nM<=nW: True ; |molSolid|<=nS: True
g  kappa  c_M  mu  c=min  A=g^2+1  log10(logW0), D=3, eps1=1/20
0.015625  0.9993  0.5  1.93e-09  1.93e-09  1.00024  190  |  1 0.5959 0.0485 2.17e-22 2.17e-22 2 449  |  10 0.5594 0.00465 8.66e-32 8.66e-32 101 637
phases: random unimodular (seed 7)   [d=3 L=4 W=2 N=512 t=1/2 E=0 Psi=0.5 r=1.0 c=0.2 R=7.0]
g=0.015625 kappa=0.9993 |val|=5.537e-07 |confined|=5.537e-07 |nonconf|=4.387e-12
   actual K0=0.500 K1=0.500 Kd=1.101 A=1: main=1.212e+00 confined/main=4.57e-07; weighted(c/2) K0w=.500 K1w=.500 Kdw=1.112: tail=5.596e-01 nonconf/tail=7.84e-12
g=1 kappa=0.5959 |val|=3.378e-04 |confined|=3.224e-04 |nonconf|=2.123e-05
   actual K0=0.500 K1=0.525 Kd=6.000 A=2: main=7.929e+01 confined/main=4.07e-06; K0w=.500 K1w=.574 Kdw=7.801: tail=3.627e+01 nonconf/tail=5.85e-07
g=10 kappa=0.5594 |val|=3.591e-04 |confined|=3.428e-04 |nonconf|=3.055e-05
   actual K0=0.500 K1=0.548 Kd=60.000 A=101: main=4.365e+05 confined/main=7.85e-10; K0w=.500 K1w=.614 Kdw=66.310: tail=2.995e+03 nonconf/tail=1.02e-08
   (each g) total |val| <= main+tail: True; confined<=main: True; nonconf<=tail: True; Lean-formula main = 1e127 / 1e268 / 1e379
phases: coherent (G-M = Psi everywhere): confined/main = 4.0e-04 / 3.5e-03 / 6.9e-07, nonconf/tail = 1.1e-08 / 3.6e-04 / 6.2e-06, all three inequalities True at g=1/64,1,10
```
The confined part is the exact sum with every `M`-, `S`-, `S⁺`-, `gΨ`-factor masked to `d_B ≤ r`; `main = C_Γ(K₀A,K₁,Kd)·Ψ^3·(W^d)^{n_M}·64Ψ^3`, `tail = e^{-cr/2}K₁ʷ²K₀ʷKdʷ²·size`, `size=(L^d)^{n_M}Ψ^{n_S}W^{-d(n_W-n_A)}=4`. The constants `K₀,K₁,Kd` are the actual `LWKBound` constants of the matrices at the point (E6), so every hypothesis of `BAGtoAG` holds with them; the Lean (formula) constants only enlarge the right side. The Lean instance is at `MFixedPointInst.P : FlowPt 4 10` (`T2412`), `Ψ=1/2` is the window point of `AuxGraph.lean` §12 (`W^{-3/2}≤1/2`).

### Verdicts
- **G3 `BAGtoAG` (targets 1-3, 5): PASS.** Exponent `n_S^{within}+2(n_W−n_A+n_M) ≥ 0` closes by `counters_le`; window constant `A=g²+1` (no smallness); tail through weighted `M`, `S`, `S⁺`, `gΨ`.
- **G4 `BAAnpAux` and `baAuxNested_holds` (target 4): PASS** as pins; the BA aux graph at centre level is the band's, so the nested form is `lwAuxNested_holds` on `shadow` (no sum over non-centre atoms remains; paper `B:494` is not needed). Open for the probe: the form of `BAAnpAux` on the BA flow carrier (L3c3's 1a).
- **`scaleatom`, `Gyiyjatom`, `Gyiyjatom2`: PASS** as the four `baAtom_*` statements above.
- Paper-delta candidates (for the report (d)): `T2420a` the aux graph at molecule centres (retained atoms folded in; same order, E2); `T2420b` the window `W^{-d} ≤ AΨ²`, `A=g²+1`; `T2420c` the exponent identity E1 (`T2387f`).
- No BLOCKED input; no REQ.

## (a″) Probe compile — Sun Oct 11 12:28:33 UTC 2026

Probe `RBM3D/Probe/T2420Pins.lean` in `/Users/junyin/Lean_proof/RBM3D-wt/T2420`, branch `t/T2420`, commit `f18b4fa` (never merged, no root import). Scripts: scratchpad `T2420/`.

```
$ date -u; git log -1 --format=%h; git hash-object RBM3D/Probe/T2420Pins.lean; git rev-parse HEAD:RBM3D/Probe/T2420Pins.lean; git status --short
Sun Oct 11 12:27:55 UTC 2026
f18b4fa T2420: probe docstring wording (Prop naming of the pins, molecul
ec0582443bc7c16cf6272dab9268b4d0b9573f59
ec0582443bc7c16cf6272dab9268b4d0b9573f59
$ lake env lean RBM3D/Probe/T2420Pins.lean; echo "exit=$?"
@BAGraph.shadow : {E I : Type} → BAGraph E I → LGraph E I
@BAGraph.auxVal : {E I : Type} →
  [Fintype E] →
    [DecidableEq E] → [Fintype I] → [DecidableEq I] → {κ : Type} → [Fintype κ] → BAGraph E I → (κ → κ → ℝ) → (E → κ) → ℝ
@BAGraph.auxOrd : {E I : Type} → [Fintype E] → [DecidableEq E] → [Fintype I] → [DecidableEq I] → BAGraph E I → ℤ
BAShadowPG : BAPGraph (Fin 2) → PGraph (Fin 2)
RBM.Graph.BAGraph_shadow_mol_pin : Prop
RBM.Graph.BAGraph_shadow_nM_pin : Prop
RBM.Graph.BAGraph_scalingOrder_sub_auxOrd_pin : Prop
RBM.Graph.BAGraph_auxOrd_le_scalingOrder_pin : Prop
RBM.Graph.baAtom_offset_pin : Prop
RBM.Graph.baAtom_dist_pin : Prop
RBM.Graph.baAtom_sedge_xi_pin : Prop
RBM.Graph.baAtom_wedge_pin : Prop
RBM.Graph.BAGtoAG (d : ℕ) : Prop
RBM.Graph.baGtoAG_E_pin : Prop
RBM.Graph.baAuxNested_pin : Prop
RBM.Graph.BAAnpAux (d : ℕ) : Prop
exit=0
Sun Oct 11 12:28:03 UTC 2026
$ wc -l RBM3D/Probe/T2420Pins.lean; grep -nE "sorry|admit|native_decide|^axiom|^theorem|^lemma" RBM3D/Probe/T2420Pins.lean; echo "grep exit=$?"
     395 RBM3D/Probe/T2420Pins.lean
grep exit=1
$ grep -c "^#check" RBM3D/Probe/T2420Pins.lean; grep -c "^example" RBM3D/Probe/T2420Pins.lean
16
7
$ clash.sh /Users/junyin/Lean_proof/RBM3D
tree: /Users/junyin/Lean_proof/RBM3D  HEAD=631b8f4
BAGraph.shadow=0 BAGraph.auxVal=0 BAGraph.auxOrd=0 BAShadowPG=0 BAGtoAG=0 BAAnpAux=0 baAuxNested_pin=0 baAtom_=0 baGtoAG_E_pin=0 BAGraph_shadow_=0 BAGraph_scalingOrder_sub_auxOrd_pin=0 BAGraph_auxOrd_le_scalingOrder_pin=0 
total hits outside RBM3D/Probe/: 0
$ clash.sh /Users/junyin/Lean_proof/RBM3D-wt/T2420
tree: /Users/junyin/Lean_proof/RBM3D-wt/T2420  HEAD=f18b4fa
BAGraph.shadow=0 BAGraph.auxVal=0 BAGraph.auxOrd=0 BAShadowPG=0 BAGtoAG=0 BAAnpAux=0 baAuxNested_pin=0 baAtom_=0 baGtoAG_E_pin=0 BAGraph_shadow_=0 BAGraph_scalingOrder_sub_auxOrd_pin=0 BAGraph_auxOrd_le_scalingOrder_pin=0 
total hits outside RBM3D/Probe/: 0
$ sed "s/2000/1/g" RBM3D/Probe/T2420Pins.lean > $SP/probe_mut.lean; lake env lean $SP/probe_mut.lean > $SP/mut2.out 2>&1; echo "exit=$?" >> $SP/mut2.out; grep "error\|⊢\|^exit" $SP/mut2.out
# negative control: A = 2000 -> 1 makes the window W^{-3} = 1/8 <= A Psi^2 false
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2420/probe_mut.lean:301:63: error: unsolved goals
⊢ False
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2420/probe_mut.lean:346:46: error: unsolved goals
⊢ False
exit=1
```
Result: the probe compiles, exit 0, no warning and no error; the only output is that of the 16 `#check` commands. The compiled file is the blob of the commit shown (the two hashes agree, `git status --short` empty).

Pins (probe lines): vocabulary `BAGraph.shadow` 42, `auxVal` 50, `auxOrd` 54, `BAShadowPG` 59; vocabulary pins 64-80; `scaleatom` offset 83 and distance 92, `Gyiyjatom` 100, `Gyiyjatom2` 108; **G3** `BAGtoAG` 120-140 and its model form `baGtoAG_E_pin` 144-162; nested form `baAuxNested_pin` 169-174; **G4** `BAAnpAux` 179-191 (owner L3d1).

Instances (7 `example`s at `d = 3`, `L = 4`, `W = 2`; `G*` at line 219, `baPQ` at 230): 238 the four vocabulary pins at `G*` with the computed counters `(n_S, n_W, n_A, n_M) = (4, 3, 3, 1)`, `|𝒢_ℳ| = 3`, `ord Γ = 4`, `ord Γ^aux = 1`, exponent 3; 256 G3 at `G*` with the merged `D0` (`G = M + 1/100`), `Ψ = 1/100`, `A = 2000` (window `W^{-3} = 1/8 ≤ A Ψ²`), `r = 1`, `R = 7 = |E ⊕ I| r`, `ξ ≡ 1/100`, `(K₀, K₁, Kd)` of `baKBound_E`, `(C, c)` from `baSpDecay`, `BAMB_decay_large`, `BAMres_fine_apply`; 337 the model form at the same data; 352 `Gyiyjatom`, `Gyiyjatom2`; 365 `scaleatom` distance; 379 the nested form at `baPQ`; 386 G4 at `baPQ`. The negative control shows the window hypothesis is checked: both errors sit at the window argument (probe lines 301 and 346), goal `False`.
Hypotheses left in the examples: the pins themselves (`h`, `hO`, `hX`, `hW`, `hN`, `p1`-`p4`) and, in 386, the edge variables `ξ` with `LWXi` (`(eq:Gbyxi3)`, the pin of stage G / L3c3), as in the merged `inst_Anp` (`LWPins.lean:699`); every other hypothesis is discharged at the data.

Differences from the pseudo-Lean of (a), block "Pins": (i) `BAAnpAux` carries `0 < p` (as `baAuxNested_pin` and `LWAuxNested`, `AuxGraph.lean:1597`); (a)'s `BAAnpAux` line omits it; (ii) `baAtom_dist_pin` carries `0 ≤ r` and "no `=`-dotted edge", `baAtom_wedge_pin` carries `0 ≤ c` and is stated for a general matrix `K` (applied to `S`, `S⁺`); (iii) `baAtom_offset_pin` states `hM`, `hP` of (a) as one conjunction; (iv) the Lean G3 instance has `Ψ = 1/100`, `A = 2000`, not the `Ψ = 1/2` of (a)(ii); (v) each theorem of (a) is a `Prop` definition (`X_pin`; `BAGtoAG`, `BAAnpAux` as the band's `LWGtoAG`, `LWAnp`). No verdict of (a) changes; no new paper-delta candidate (those of (a): `T2420a`-`T2420c`).
Not done by the probe: no pin is proved (G3 is the argument of (a)); `LocReg345` of a general BA shadow and the form of `BAAnpAux` on the BA flow carrier (L3c3's 1a) are not touched.

## (b) Stage 1b: result and script output — Sun Oct 11 13:35:51 UTC 2026 (`date -u`)

**G3 verdict: PROVED, no REQ.** `baGtoAG_holds : BAGtoAG d` (deterministic form), `baGtoAG_E` (constants of `(d, Λ, κ)` only), the nested form `baAuxNested_holds`, the vocabulary and order theorems and the four `baAtom_*` statements are proved; no `sorry`, no hypothesis added, no pin changed (conformance below). No correction to (a) is needed.
**Lines against the stop line (2000 per file, never reached):** `RBM3D/Graph/BAAtom.lean` 1098, `RBM3D/Graph/BAAtom2.lean` 797; branch `t/T2420`, HEAD `32a1b69`.
**G4 pin:** `BAAnpAux d` (`BAAtom2.lean:677-689`, docstring owner L3d1; statement text identical to the probe's, commit `f18b4fa`) is fixed and, beyond the ticket, **proved** in the band-flow form: `baAnpAux_holds : BAAnpAux d` from the merged `lwAnp_holds` (`AnpKey6.lean:952`) and `baAuxNested_holds` (the nested graph has the value `Γ^aux` for symmetric `ξ`, `LWXi` carries the symmetry; no sum over non-centre atoms occurs at centre level). No registry line: the `#assert_rbm_axioms` scan is identical with and without the two modules (below).
**Section map.** `BAAtom.lean`: §1 vocabulary `BAGraph.shadow`, `auxVal`, `auxOrd`, `BAShadowPG` (l.55); §2 order comparison (141); §3 `baAtom_offset/dist/sedge_xi/wedge` (167); §4 pointwise bounds, `BAAtom_term_conf` (366); §5 roots of the forest and per-edge sums `BAAtom_exists_roots`, `BAAtom_forest_roots`, `BAAtom_sum_J` (602); §6 instances (951). `BAAtom2.lean`: §1 tail, `BAAtom_term_tail`, `BAAtom_tail_sum` (55); §2 `BAAtom_main_sum`, `BAGtoAG`, `baGtoAG_holds` (329); §3 `BAAtom_decay_E`, `baGtoAG_E` (528); §4 `baAuxNested_holds`, `BAAnpAux`, `baAnpAux_holds` (640); §5 instances (712).

```
$ date -u; git log -1 --format="%h %s"; git status --short; wc -l RBM3D/Graph/BAAtom.lean RBM3D/Graph/BAAtom2.lean
Sun Oct 11 13:35:51 UTC 2026
32a1b69 T2420: BAAtom2 section numbering
    1098 RBM3D/Graph/BAAtom.lean
     797 RBM3D/Graph/BAAtom2.lean
    1895 total
section commits (BAAtom.lean/BAAtom2.lean lines): adda5a8 337/0, 5acbe9e 573/0, 48fe15b 922/0, 993f6f6 922/521, 08bec49 925/693, 85119f3 1092/682, 7df9f18 1092/766, 2f5af82 1098/797, 32a1b69 1098/797
$ lake build RBM3D.Graph.BAAtom RBM3D.Graph.BAAtom2 2>&1 | grep -E "BAAtom|error|Build completed"   (replayed warnings of other modules are not shown)
Build completed successfully (3825 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Graph/BAAtom.lean RBM3D/Graph/BAAtom2.lean; echo "grep exit=$?"
grep exit=1
$ #print axioms (lake env lean axall.lean): the four theorems of G3, G3_E, nested form, G4; then the summary over all public declarations
'baGtoAG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'baGtoAG_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'baAuxNested_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'baAnpAux_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
public declarations: 57; exactly [propext, Classical.choice, Quot.sound]: 55; others: ['BAAtomInst.ell1 [propext, Quot.sound]', 'BAAtomInst.ellI1 [propext, Quot.sound]']
$ python3 -I final4.py   (statements of the targets, whitespace-collapsed, from the files)
theorem BAGraph.shadow_mol (Γ : BAGraph E I) (v : E ⊕ I) : Γ.shadow.mol v = Γ.mol v
theorem BAGraph.shadow_nM (Γ : BAGraph E I) : Γ.shadow.nM = Γ.nM
theorem BAGraph.scalingOrder_sub_auxOrd (Γ : BAGraph E I) : Γ.scalingOrder - Γ.auxOrd = ((Γ.nS : ℤ) - (Γ.shadow.molSolid.length : ℤ)) + 2 * ((Γ.nW : ℤ) - (Γ.nA : ℤ) + (Γ.nM : ℤ))
theorem BAGraph.auxOrd_le_scalingOrder (Γ : BAGraph E I) (hN : Γ.Normal) : Γ.auxOrd ≤ Γ.scalingOrder
theorem baAtom_offset (Γ : BAGraph E I) (D : BALData (Idx d L W)) (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0) (ℓ : E ⊕ I → Idx d L W) (h : Γ.term D ℓ ≠ 0) (u v : E ⊕ I) (hv : v ∈ Γ.atom u) : (split d L W (ℓ u)).2 = (split d L W (ℓ v)).2
theorem baAtom_dist (Γ : BAGraph E I) (ℓ : E ⊕ I → Idx d L W) (r : ℝ) (hr : 0 ≤ r) (hD : ∀ e ∈ Γ.dotted, e.eq = false) (hm : ∀ e ∈ Γ.mdot, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r) (hp : ∀ e ∈ Γ.psi, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r) (u v : E ⊕ I) (hv : v ∈ Γ.atom u) : (lwBdist d L W (ℓ u) (ℓ v) : ℝ) ≤ (Fintype.card (E ⊕ I) : ℝ) * r
theorem baAtom_sedge_xi {V : Type} (D : BALData (Idx d L W)) (ξ : Zd d L → Zd d L → ℝ) (R : ℝ) (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R → (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) (ℓ : V → Idx d L W) (lab : V → Zd d L) (hlab : ∀ v, (zdistD d L ((split d L W (ℓ v)).1 - lab v) : ℝ) ≤ R) (e : SEdge V) (he : e.circ = true) : ‖SEdge.val D.toLData ℓ e‖ ≤ ξ (lab e.src) (lab e.dst)
theorem baAtom_wedge (K : Matrix (Idx d L W) (Idx d L W) ℂ) (C c r : ℝ) (hc : 0 ≤ c) (hK : ∀ x y, ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) (x y : Idx d L W) : ‖K x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * ((if (lwBdist d L W x y : ℝ) ≤ r then 1 else 0) + Real.exp (-(c * r)))
theorem baAuxNested_holds : ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → (BAShadowPG P).LocReg345 p → P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) → ∃ Γa : NGraph p P.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = P.g.auxOrd ∧ ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : P.E' → κ, Γa.val ξ (fun _ => be (P.ext 0)) (fun _ => be (P.ext 1)) = P.g.auxVal ξ be
$ python3 -I final3.py   (positions of the long statements; text identity with the probe)
BAGtoAG 392-412; baGtoAG_holds 418-418; baGtoAG_E 606-624; BAAnpAux 677-689; baAnpAux_holds 694-694
BAGtoAG: statement text (def line to end) identical to the probe after whitespace normalisation: True
BAAnpAux: statement text (def line to end) identical to the probe after whitespace normalisation: True
$ python3 -I conform.py; lake env lean conform.lean   (probe pins X_pin + `example : X_pin := @X` for the 8 vocabulary/atom pins, `baGtoAG_E_pin`, `baAuxNested_pin`, and `BAGtoAG_probe d = BAGtoAG d := rfl`, `BAAnpAux_probe d = BAAnpAux d := rfl`)
exit=0 output bytes=0 examples=13
$ negative control: pin shadow_mol_pin := @BAGraph.shadow_nM
conform_neg.lean:143:36: error: Type mismatch
$ sed -n 725,732p RBM3D/Graph/BAAtom2.lean   (the compiled instance of baGtoAG_holds)
example : ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
    Gstar.scalingOrder - Gstar.auxOrd = 3 ∧
    Gstar.auxVal xiInst (fun a => (split 3 4 2 (ellInst a)).1) = 64 * (1 / 100 : ℝ) ^ 3 ∧
    ‖Gstar.val D0 ellInst‖ ≤
      Gstar.sizeConst (K₀ * 2000) K₁ Kd * (1 / 100 : ℝ) ^ (Gstar.scalingOrder - Gstar.auxOrd) *
          ((((2 : ℕ) : ℝ) ^ 3) ^ Gstar.nM * Gstar.auxVal xiInst (fun a => (split 3 4 2 (ellInst a)).1)) +
        Real.exp (-(c * 1 / 2)) * Gstar.sizeConst C (C * expC (3 - 2) (c / 2)) (C * (1 + expC (3 - 2) (c / 2))) *
          Gstar.scalingSize (1 / 100) 2 3 4 := by
$ grep -n "^example" (all compiled instances)
BAAtom.lean: 984 1025 1031 1038 1051 1062 1080 
BAAtom2.lean: 725 756 775 784 
$ lake env lean docs/tickets/checks/T2420-check.lean
exit=0 error lines=0 #check outputs=7
$ clash2.sh (57 public names vs main f3a7401 and this tree, outside Probe/ and the two files)
names checked: 57; total hits outside RBM3D/Probe/ and the two files: 0
names checked: 57; total hits outside RBM3D/Probe/ and the two files: 0
$ git diff --stat main...t/T2420 | tail -4
 RBM3D/Graph/BAAtom.lean    | 1098 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAAtom2.lean   |  797 ++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2420Pins.lean |  395 ++++++++++++++++
 3 files changed, 2290 insertions(+)
$ date -u; lake env lean precheck0.lean (import RBM3D) and precheck.lean (import RBM3D, BAAtom, BAAtom2); both end with #assert_rbm_axioms
Sun Oct 11 13:36:47 UTC 2026
without the two modules: exit=0; axiom audit: 11805 theorems, 3578 definitions, 0 axioms in `RBM` (compiler-generated declaratio; premises found by scanning: 117 (borrowe
with the two modules:    exit=0; axiom audit: 11850 theorems, 3592 definitions, 0 axioms in `RBM` (compiler-generated declaratio; premises found by scanning: 117 (borrowe
diff of the two audit outputs (declaration counts masked): empty
$ lake build   (RBM3D.lean with the two import lines added for the run, restored after; git status clean)
exit=0; Build completed successfully (4231 jobs).; axiom audit: 11850 theorems, 3592 definitions, 0 axioms; git status --short: []
```
Narrative (how G3 closes; every name is in the files above).
1. *Shadow.* `BAGraph.shadow` makes every `M`-/`Ψ`-dotted edge also a waved edge; `BAAtom_shadow_adj` gives the adjacency of `Γ`, so molecules, `n_M` and external molecules agree (`shadow_mol`, `shadow_nM`); `auxVal`, `auxOrd` are the band's on the shadow and the band lemmas of `AuxGraph` (`auxGraph_lab_close`, `auxGraph_sum_blocks`, `auxGraph_auxVal_eq`, `auxGraph_prod_filter`) are reused unchanged. The exponent is `(n_S - |𝒢_ℳ|) + 2 (n_W - n_A + n_M) ≥ 0` (`scalingOrder_sub_auxOrd`, `BAGraph.counters_le`).
2. *Pointwise.* `BAAtom_term_le0`: `‖term‖ ≤ |coeff| ∏_solid ‖·‖ ∏_J f_j`, `J = waved ⊕ mdot ⊕ psi`; on a confined labelling a solid edge inside a molecule is `≤ Ψ`, between two molecules `≤ ξ` of their blocks (`hξ`, `baAtom_sedge_xi`): `BAAtom_term_conf`.
3. *Sum.* From the merged `BAGraph.exists_forest` (unchanged) `BAAtom_exists_roots` derives an injective root map with children `C = (range root)ᶜ`; `BAAtom_forest_roots` is `BASizeClaim_forest_sum_le` with the roots as external labels and a weight `Φ` of their blocks; `BAAtom_sum_J` gives `(Σ_x Φ x) K₁^{n_A-n_M} a^{n_W-(n_A-n_M)} Kd^{#M+#Ψ}`; the window `W^{-d} ≤ A Ψ²` turns `a^t` into `(K₀A)^t Ψ^{2t}`.
4. *Tail.* A `J`-edge `> r` gives `∏_J e^{(c/2) d_B} ≥ e^{(c/2) r}` (`BAAtom_term_tail`); the weighted kernels are bounded by `lwKBound_of_decay` (`S`, `S⁺`) and `BAAtom_offdiag_kbound` (`M`, `g Ψ`, offset-diagonal, fibre sum); `BAAtom_tail_sum` is `BAAtom_sum_J` with `Φ = 1`.
5. *Model form.* `(K₀, K₁, Kd)` from `baKBound_E`; `(C, c)` from `BAAtom_decay_E` (`baSpDecay`, `BAMB_decay_large`, `BAMres_fine_apply`, `g₀ ≤ Λ`, no smallness).
Notes. `baClaimSize`/`baClaimSizeG` are not called (they bound `‖val‖` and carry no root weight `Φ`); the private helpers `BASizeClaim_alg_prod`, `BASizeClaim_size_alg`, `BASizeClaim_PsiI_apply` (`BASizeClaim2.lean:193, 446`, `BASizeClaim.lean:367`) are copied as `BAAtom_alg_prod`, `BAAtom_size_alg`, `BAAtom_PsiI_apply`; `auxGraph_forest_roots`, `auxGraph_term_conf` (`AuxGraph.lean:551, 325`) are adapted. No port from RBM1D/RBM2D (nothing read there), so no diff-stat. `hext` of `BAGtoAG` is unused. `RBM3D.lean` is not edited (CLAUDE.md §1: hub); the full `lake build` above was run with the two imports added to it for the run only. The probe stays on the branch, not merged. `BAAtom2` also imports `RBM3D.Graph.LWPins` and `RBM3D.Graph.AnpKey6`.

## (c) Verified Mathlib names (all `#check`ed, exit 0: scratch `names.lean`, 22 names)
`Finset.eq_of_subset_of_card_le`, `Finset.card_compl`, `Finset.card_image_of_injective`, `Finset.card_bij` (counts of roots and children); `Finset.prod_mul_distrib`, `Finset.single_le_sum`, `Real.exp_sum` (tail product); `Equiv.subtypeEquivRight`, `Equiv.sumCompl`, `Equiv.ofInjective`, `Equiv.sumArrowEquivProdArrow` (`BAAtom_forest_roots`); `SimpleGraph.ConnectedComponent.eq`, `.ind`, `List.mem_iff_get`, `List.prod_eq_zero`, `List.any_append`, `List.any_map`, `Bool.eq_iff_iff`, `Function.iterate_succ_apply'`, `Nat.strong_induction_on`, `mul_nonneg_iff_of_pos_right`, `pow_le_pow_left₀`. Deprecated in this toolchain (warnings in the tool log): `if_pos`, `if_neg`, `if_true`, `if_false`; used `simp only [h, ↓reduceIte]`, `ite_true`, `ite_false`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates (tags `T2420x`, numbered by the dispatcher)
- `T2420a`, `T2420b`, `T2420c` as in (a): the auxiliary graph at the molecule centres (retained atoms `x_{i,j}` of `B:448` folded in, `B:436-449`); the window `W^{-d} ≤ A Ψ²` with `A ≥ 0` a parameter (`A = g² + 1` per (a), replacing `W^{-d/2} ≤ Ψ`); the exponent identity `BAGraph.scalingOrder_sub_auxOrd`.
- `T2420d`: `scaleatom`, `Gyiyjatom`, `Gyiyjatom2` are deterministic: exact offset equality on non-zero terms (`baAtom_offset`), block distance `≤ |E ⊕ I| r` under confinement (`baAtom_dist`), `ξ`-domination on `R`-balls (`baAtom_sedge_xi`, the hypothesis `hξ`), the `S` decay split at `r` (`baAtom_wedge`); the paper's "up to `e^{-c (log W)^{1+ε₁}}`" is the tail term of G3 at `r = (log W)^{1+ε₁}`, and the sum `ζ` of `B:424` is the sup-form `ξ`.
- `T2420e`: `hext` of `BAGtoAG` is not used by the proof (cf. `T2170f`). `T2420f`: G4 at centre level is a corollary of `lwAnp_holds` (`baAnpAux_holds`): L3d1 may shrink to the BA flow carrier form (L3c3's 1a), not touched here.
- Open: G3 is stated for normal BA graphs only (no `BAGraph.partition` form, cf. `baClaimSizeG`); the retained atoms of `B:448` are not modelled (needed only if a later row reads the paper's auxiliary graph with atoms); `LocReg345` of a general BA shadow (the hypothesis of `baAuxNested_holds`; BA `lem:localregular`, rows L3b of `T2387-design.md` §1) is not touched.
