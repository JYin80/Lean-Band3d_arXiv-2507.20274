Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 00:04:25 UTC 2026

### (i) Exponent table

Sources: paper `1_2_Intro_model_result.tex` (`eq:KMloop` l.1003, `eq:Msig` l.1070, `WI_calK` l.1039, `Kn2sol`/`Kn3sol` l.1175-1176, `eta` l.720), `A_deterministic_estimates.tex` (`eq_Ktree` l.370, `f-external`/`f-internal`/`M-graph-value-unsummed` l.340-366). `E_a` is the rescaled block identity (`Tr E_a = 1`, `Tr E_aE_a = W^{-d}`), so `𝓜^{(k)} = Tr ∏ m(σ_i)E_{a_i} = W^{-(k-1)d} ∏m 1(a_1=…=a_k)` (1_2:1007).

| Quantity | Value (d=3, L=5, W=2, g=1/2, E=0, t=9/10) | Constraint | Slack |
|---|---|---|---|
| `W^{-d(n-1)}` in `(eq_Ktree)`; `n=2`: `W^{-d}`; `n=3`: `W^{-2d}`; `n=4`: `W^{-3d}` | `1/8`, `1/64`, `1/512` | exponent is `d(n-1)` = (number of `M`-loop vertices − 1)·d, d-dependence only through `W^d`; `n≥3` for the tree branch of `KLgen` (paper states `eq_Ktree` for `n≥4`; `n=3` is the star, `TSP(3)={∅}`, same value as `Kn3sol`, see (ii)) | exact |
| `(Kn2sol)` spectral parameter `ξ = t m(σ₁)m(σ₂)` | `(+,-)`: `0.9`; `(+,+)`: `-0.9` | `‖ξ‖<1` (needed for `Θ_ξ=(1-ξS)^{-1}` to exist; `‖SB‖=1`) | `1-t = 1/10` |
| `m(±)` at `E=0` | `±i`, `|m|=1` | `|m|=1` for `\|E\|≤2` | exact |
| `M^{(σ₁,σ₂)}` (`eq:Msig`) | `m(σ₁)m(σ₂) I` | `W^dTr(m₁E_a m₂E_b) = m₁m₂ δ_{ab}` | exact |
| `η_t = (1-t) Im m(E)` (`eta`) | `1/10` | `η_t ≠ 0` (Ward divides by `2iW^dη_t`) | `1/10 > 0` |
| `(WI_calK)` n=2 LHS `Σ_{a₂}K^{(2)}_{(s,-s)}` | `W^{-d}(1-t)^{-1} = 1.25` | row sum `Σ_bΘ_t(a,b)=(1-t)^{-1}` and `m(s)m(-s)=|m|²=1` | exact |
| `(WI_calK)` n=2 RHS `(2iW^dη_t)^{-1}(m(+)-m(-))` | `(1.6i)^{-1}(2i) = 1.25` | `m(+)-m(-)=2i Im m` | exact |
| `KLPar` fields (`KLinstPar : KLPar 1 1`): `L≥3`, `W≥1`, `0<g≤gmax=1`, `\|E\|≤2-κ=1`, `0≤t<1` | `L=5`, `W=2`, `g=1/2`, `E=0`, `t=9/10` | each as listed | `2`, `1`, `1/2`, `1`, `1/10` |
| `KLward_two` hypotheses: `3≤L`, `1≤W`, `\|E\|<2`, `t∈[0,1)` | as above | as listed | `2`, `1`, `2`, `1/10` |
| `KLK_eq_sum_Kpi`: `3 ≤ n` | `n=4` | `n≥3` | `1` |
| `SB` row sum: `a₀ = (1+2dg²)^{-1}`, neighbour weight `g²a₀`, `2d` neighbours (`L≥3`) | `a₀=0.4`, nbr `0.1`, `0.4+6·0.1=1` | `‖SB‖=1` (hypothesis `hS` of `Theta` lemmas; holds for `L≥3`) | exact |
| `TSP(n)` sizes (Schröder) | `1,3,11,45` for `n=3..6` | matches `TSP_three`, `TSP_four` | exact |
| `KLTSPlong` at `σ=(+,+,-,-)`, `n=4` | per `π∈P(diag)`: `∅:1, {(0,2)}:1, {(1,3)}:1, both:0` | each tree has one long-edge set; fibres partition `TSP(4)` (3 = 1+1+1) | exact |
| `KLTSPlong` at `σ=(+,-,+,-)` (probe's instance) | `∅:3`, others `0` | both diagonals join equal charges (not long) | exact |
| Kernel-generic successors (item 3): `treeEqRhsS S`, `MLoopM`, `IsKLoopS` | `S := SB d L g`, `M := MLoop` | `treeEqRhs = treeEqRhsS (SB d L g)`, `MLoop = MLoopM …`, `IsKLoop ↔ IsKLoopS …`: definitional unfoldings (same sums, `K 0 I = M I`, `K t ⟨[s],[a]⟩ = m s`), no exponent | none |

No exponent other than `n-1` (power of `W^{-d}`) enters the targets; the propagator shapes `KLDecay/KLShort/KLDiffOne/KLDiffTwo/KLZero` are `Prop` definitions (existential constants, never hypotheses of a target here). The range `|r| ≤ c|a|`, `c<1` is paper-delta `T2004c` (signed, DECISIONS §15; cited, not re-proposed).

### (ii) One concrete nondegenerate instance

`d=3, L=5` (125 blocks), `W=2` (`W^d=8`), `g=1/2`, `E=0`, `t=9/10`, charges `(+,-,+)`, labels `![0,1,2] : Fin 3 → Zd 3 5`. Note `(1 : Zd 3 5)` is the constant function `(1,1,1)`, so the labels are the three distinct blocks `(0,0,0),(1,1,1),(2,2,2)`; for `n=4` also `(3,3,3)`. Hypotheses of every target hold: `3≤L`, `1≤W`, `|E|=0<2`, `t=0.9∈[0,1)`, `n=4≥3`, `‖ξ‖=0.9<1`. The script builds `SB` and `Θ_ξ=(1-ξSB)^{-1}` as `125×125` matrices, evaluates the paper's `M`-loop sums for `(Kn2sol)` (`Σ_bΘ(a₁,b)𝓜^{(2)}_{(b,a₂)}`) and `(Kn3sol)` (triple sum with dense `𝓜^{(3)}`), the probe's tree sum `KLn` (nodes `{root}∪F`, leaf/node parents as in `KLleafPar`/`KLnodePar`) and `kTwo`, checks `(WI_calK)` at `n=2` for both `s` and all 125 `a₁`, the regrouping `(eq_K-Kpi)` at `n=4` for the probe's `σ=(+,-,+,-)` and the discriminating `σ=(+,+,-,-)`, and (extra check of the normalisations) the tree equation `(pro_dyncalK)` `d/dt K^{(n)} = W^d Σ_{1≤k<l≤n}Σ_{a,b}K(cutL)S_{ab}K(cutR)` by central difference at `n=2,3,4` with `cutL/cutR` exactly as in `Loop/TreeRep.lean:84-91`.

Command (Python only; no Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2008_check.py`

```
rowsum min/max 0.9999999999999999 1.0000000000000002  ||S||_2 = 1.0  d*? a0= 0.4
m(+)= 1j  |m|= 1.0  eta_t= 0.09999999999999998
xi values: +-: (0.9+0j)  ++: (-0.9+0j)  |xi|<1 slack 0.09999999999999998
Kn2sol max err over 4 charge pairs, all (a1,a2): 0  sample K2(+-,0,P1)= (0.009049508076167577+0j)
TSP sizes n=3..6: [1, 3, 11, 45]
Kn3sol: paper triple sum = 7.923446443664855e-06j  tree sum KLn(3) = 7.923446443664858e-06j  |diff|= 3.3881317890172014e-21
Ward n=2: LHS(s=+,a1=0) = (1.2500000000000029+0j)  RHS = (1.2500000000000002+0j) ; max |LHS-RHS| over s, all a1: 3.774758283725532e-15
ODE n=2 sig=+-: dK/dt(fd)=(0.11571336+0j)  treeEqRhs=(0.11571336+0j)  |diff|=1.05e-09
ODE n=3 sig=+-+: dK/dt(fd)=0.00033205j  treeEqRhs=0.00033205j  |diff|=1.22e-11
ODE n=4 sig=+-+-: dK/dt(fd)=(-1.92e-06+0j)  treeEqRhs=(-1.92e-06+0j)  |diff|=1.88e-14
ODE n=4 sig=++--: dK/dt(fd)=(2.42e-06+0j)  treeEqRhs=(2.42e-06+0j)  |diff|=1.64e-13
eq_K-Kpi n=4 sig=+-+-: #TSPlong per pi (powerset order)=[3, 0, 0, 0] |K - W^{-3d} sum_pi K^pi|=0.00e+00 |K|=5.9602e-08
eq_K-Kpi n=4 sig=++--: #TSPlong per pi (powerset order)=[1, 1, 1, 0] |K - W^{-3d} sum_pi K^pi|=0.00e+00 |K|=4.1514e-08
```

The values are nonzero and nondegenerate (`|K^{(3)}|≈7.9e-6`, `|K^{(4)}|≈6e-8`, `K^{(2)}=0.00905`); `(Kn2sol)` and `(Kn3sol)` agree with the paper's `M`-loop form and the tree sum; `(WI_calK)` at `n=2` holds with `1.25 = 1.25` for both `s`; the tree sum solves `(pro_dyncalK)` at `n=2,3,4` at this data (relative error `≤ 1e-7`, finite-difference limited). The powerset order of `diagonals 4 = {(0,2),(1,3)}` in the script is `∅,{(0,2)},{(1,3)},{both}`.

External hypotheses: none (every target is a definition or an identity; `KLPT` and the pins are not hypotheses of any target of this ticket, so no limit computation is owed).

### Verdicts

- Target 1 (probe sections 1-5, verbatim: `KLK`, `KLgen_loopOf`, `KLK_one/two/three`, `KLK_two_eq_kTwo`, `KLPar`, `KL{Decay,Short,DiffOne,DiffTwo,Zero,PT}`, molecule layer, `KLK_eq_sum_Kpi`, `KLtreeValW_eq_sum_selfW`, `KLKpi_eq_sum_SigmaPi`, `KLward_two`): **PASS**. Normalisations (i) hold at the instance, all hypotheses hold at once.
- Target 2 (ports with `Z2→Zd d`, `W²→W^d`): **PASS** (mathematics: no exponent beyond `W^{-d(n-1)}`; the dimension enters only through `W^d`, `Θ d L g`, `SB d L g`; checked at `d=3`).
- Target 3 (`treeEqRhsS`, `MLoopM`, `IsKLoopS`): **PASS** (definitional generalisations; the ticket does not pin the shape of `MLoopM`, only that `MLoop … = MLoopM …`: any shape with that equality provable is mathematically admissible; observation, not a block).
- Instances: `KLinst_two`, `KLinst_three`, `KLinst_Kpi`, `KLinst_ward_two`, `KLinstPar` at the data above are nondegenerate (values above). `IsKLoop ↔ IsKLoopS` is an `iff` without hypotheses, so its instance cannot discharge `IsKLoop (KLK …)` (that is `KLisKLoopPin`, ticket KL3); the instance is the `iff` applied at `K := KLK` data, with `T = Set.Ico 0 1`, `m = mSigma 0`.

Overall verdict: **PASS**.

## (b) Script output

Branch t/T2008, commit `ee4c726` (two commits on `main@6a555f7`), file `RBM3D/Loop/KLTree.lean`,      976 lines. Time of this section: Sat Oct  3 00:11:55 UTC 2026.

### Build, axioms, hygiene
```
$ lake build RBM3D.Loop.KLTree 2>&1 | tail -3
Build completed successfully (3236 jobs).
$ # names.txt = the non-private theorem/def/structure/instance names of the file (script); one "#print axioms" line each
names:       97   printed: 97   outside {propext, Classical.choice, Quot.sound}: 0
  82 axioms: [propext, Classical.choice, Quot.sound]
   9 axioms: [propext, Quot.sound]
   1 axioms: [propext]
'RBM.Loop.IsKLoop_iff_IsKLoopS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLinst_ward_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_eq_sum_Kpi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLKpi_eq_sum_SigmaPi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLMLoop_eq_MLoopM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSigmaPi_empty_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLward_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.treeEqRhs_eq_treeEqRhsS' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Loop/KLTree.lean; echo "exit=$?"
exit=1
$ for n in $(cat names.txt); do grep -rlw "$n" RBM3D --include="*.lean" | grep -v Loop/KLTree.lean; done | sort -u | wc -l   # name clash of the new names with every other RBM3D file
       0
$ git diff --stat main...t/T2008
 RBM3D/Loop/KLTree.lean | 976 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 976 insertions(+)
```

### Item 1: pinned text against the probe at 64b58eb (lines 41-501)
```
$ git --no-optional-locks show 64b58eb:RBM3D/Probe/T2004Pins.lean | sed -n 41,501p > p41.lean
$ awk "/^namespace RBM.Loop/{f=1} f" RBM3D/Loop/KLTree.lean | sed -n 1,461p > mine.lean; diff p41.lean mine.lean; echo "diff exit=$?"
diff exit=0
$ wc -l p41.lean mine.lean; sed -n 489p RBM3D/Loop/KLTree.lean
     461 p41.lean
     461 mine.lean
     922 total
end Proofs2
```

### Ports (item 2), RBM2D read with `git show c9a24cf:...`
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf; git -C ../RBM2D --no-optional-locks log -1 --format=%h
c9a24cf
bcc2c11
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/TreeRep.lean RBM2D/Loop/Kcal.lean
 RBM2D/Loop/Kcal.lean    | 326 +++++++-----------------------------------------
 RBM2D/Loop/TreeRep.lean |  54 +++-----
 2 files changed, 63 insertions(+), 317 deletions(-)
```
| Lean (`KLTree.lean`) | RBM2D source at c9a24cf | change |
|---|---|---|
| sec. 1-5: `KLwholeP` .. `KLward_two` | Kcal.lean:77-149, 183-210, 243-293, 376-571, 704-778 (design row KL1) | via the probe, verbatim (diff above) |
| sec. 6: `KLwholeP_mem_nodes`, `KLminNode_le` .. `KLnot_arcLe_nodePar_self` | Kcal.lean:103; TreeRep.lean:185-413 | `private` dropped, prefix `KL` (perl rename), no other change |
| `KLTheta_reflect` | Kcal.lean:498-507 | `Z2 L` to `Zd d L`; `Theta_apply_add_right`, `Theta_transpose` to the merged `_of_three_le` forms |
| `KLselfW_reflect` | Kcal.lean:509-525 | `Z2 L` to `Zd d L` |
| `KLSigmaPi_empty_symm` | Kcal.lean:759-777 | `Z2 L` to `Zd d L`; premises as binders; `norm_xi` replaced by merged `norm_mul_mSigma_lt_one`; `prod m` factor inside `KLSigmaPi` (`congr 1`) |

### Statements of item 3 and of the added port (script extraction; `...` = proof omitted)
```
noncomputable def treeEqRhsS (S : Matrix (Zd d L) (Zd d L) ℂ) (K : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  ...
noncomputable def MLoopM (m : Bool → ℂ) (R : List Bool → List (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  ...
def KLallEq : List Bool → List (Zd d L) → ℂ :=
  ...
def IsKLoopS (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  ...
theorem treeEqRhs_eq_treeEqRhsS (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    treeEqRhs d L W g K I = treeEqRhsS d L W (SB d L g) K I := rfl
  ...
theorem KLMLoop_eq_MLoopM (m : Bool → ℂ) :
    MLoop d L W m = MLoopM d L W m (KLallEq d L) := rfl
  ...
theorem IsKLoop_iff_IsKLoopS (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) :
    IsKLoop d L W g m T K ↔ IsKLoopS d L W (SB d L g) m (MLoopM d L W m (KLallEq d L)) T K :=
  ...
theorem KLSigmaPi_empty_symm (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (σ : Fin n → Bool) (d₁ : Zd d L)
    (s : Fin n → Zd d L) (_ : s 0 = 0) :
    KLSigmaPi d L g (mSigma E) t σ ∅ (fun i => d₁ + s i)
      = KLSigmaPi d L g (mSigma E) t σ ∅ (fun i => d₁ - s i) := by
  ...
```

### Compiled instances at d=3, L=5, W=2, g=1/2, E=0, t=9/10 (statements, script extraction; all built in the same file)
```
noncomputable def KLinstPar : KLPar 1 1 where
  L := 5
  W := 2
  hL := by norm_num
  hW := by norm_num
  g := 1 / 2
  hg0 := by norm_num
  hg1 := by norm_num
  E := 0
  hE := by norm_num
  t := 9 / 10
  ht0 := by norm_num
  ht1 := by norm_num

/-- A nondegenerate loop: charges `(+,-,+)`, labels three distinct blocks of `Z_5^3`. -/
def KLinstσ : Fin 3 → Bool := ![true, false, true]

def KLinsta : Fin 3 → Zd 3 5 := ![0, 1, 2]

/-- The scales at the instance data: `η_t = 1/10`,
`B_{t,0} = 514/175 = 2.9371`. -/
theorem KLinst_scales :
    Gauss.etaT 0 (9 / 10) = 1 / 10 ∧ Bparam 3 5 (1 / 2) (9 / 10) 0 = 514 / 175 := by
  ...
theorem KLinst_two :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, 1]⟩
      = ((2 : ℂ) ^ 3)⁻¹ * (mSigma 0 true * mSigma 0 false)
          * Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) 0 1 := by
  ...
theorem KLinst_three :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩
      = (((2 : ℂ) ^ 3)⁻¹) ^ 2 * (mSigma 0 true * mSigma 0 false * mSigma 0 true) *
          ∑ b : Zd 3 5,
            Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) 0 b *
              Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 false * mSigma 0 true)) 1 b *
                Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 true)) 2 b := by
  ...
theorem KLinst_ward_two :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false], [0]⟩) := by
  ...
theorem KLinst_Kpi :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])
      = (((2 : ℂ) ^ 3)⁻¹) ^ 3 * ∑ π ∈ (diagonals 4).powerset,
          KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, false, true, false] ![0, 1, 2, 3] π := by
  ...
theorem KLinst_treeEqRhsS :
    treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        (KLloopOf 3 5 KLinstσ KLinsta)
      = treeEqRhsS 3 5 2 (SB 3 5 (1 / 2)) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        (KLloopOf 3 5 KLinstσ KLinsta) :=
  ...
theorem KLinst_IsKLoopS :
    IsKLoop 3 5 2 (1 / 2) (mSigma 0) (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I)
      ↔ IsKLoopS 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoopM 3 5 2 (mSigma 0) (KLallEq 3 5))
          (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) :=
  ...
theorem KLinst_SigmaPi_symm :
    KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun i => (1 : Zd 3 5) + KLinsta i)
      = KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun i => (1 : Zd 3 5) - KLinsta i) :=
  ...
```

### Narrative (stage 1b)

- No preflight correction was needed: section (a) was not edited and there is no (a'). (a) already notes that `IsKLoop (KLK ..)` is not dischargeable here (`KLisKLoopPin` is ticket KL3).
- Item 1: probe lines 41-501 are in the file character for character (diff exit 0 above); all of it compiled on current `main` without a proof change. The imports are `RBM3D.Loop.Primitive` and `RBM3D.Loop.GLoop` only.
- Item 2: the probe already contains the laminar API definitions, `KLK`, `KLKpi`, `KLSigmaPi`, the molecule first stage and Ward at `n = 2`. What it lacks and is ported here: the laminarity lemmas of `TreeRep.lean:185-413` (public, prefix `KL`, because ticket KL3 needs them from another file) and `SigmaPi_empty_symm` with its two helpers. `selfE` (Kcal.lean:280-283) is not ported: `KLSigmaPi` unfolds it. The laminar lemmas are not used inside this file; they are API.
- Item 3: the ticket fixes only the equalities `treeEqRhs = treeEqRhsS (SB d L g)`, `MLoop = MLoopM ..`, `IsKLoop <-> IsKLoopS ..`. Shape chosen: `treeEqRhsS` takes any kernel `S`; `MLoopM` takes a free label profile `R : List Bool -> List (Zd d L) -> ℂ` (so the charge-dependence of a block-Anderson initial value can enter) and keeps the prefactor `W^{-(k-1)d} ∏ m`; `IsKLoopS` takes the initial data `M` as an arbitrary function on loop indices (strictly more general than `MLoopM ..`). If gate BA needs a different prefactor, `IsKLoopS` already allows it and only `MLoopM` would be replaced. The three equalities are `rfl`/`Iff.rfl`.
- Instances: the five pinned ones, plus `KLinst_Kpi_SigmaPi`, `KLinst_SigmaPi_symm` (`d₁ = 1`, `s = (0,1,2)`: the two arguments differ), `KLinst_treeEqRhsS`, `KLinst_MLoopM`, `KLinst_IsKLoopS`, `KLinst_one_two_kTwo`, `KLinst_gen_loopOf`. They apply the target at the data of (a) (`n = 2, 3, 4`; 125 blocks), no premise is a pin, none is a hypothesis of the instance. `KLinst_IsKLoopS` is an `iff` (as the target is): its left side is not asserted.
- The numeric checks of (a) (script, Python) were not rerun; the Lean instances `KLinst_two`, `KLinst_three`, `KLinst_Kpi`, `KLinst_ward_two` are the exact statements of (a)'s formulas at the same data.

## (c) Verified Mathlib and project names (all used in the compiled file)

- `Fintype.sum_equiv`, `Equiv.piCongrRight`, `Equiv.piCongrRight_apply`, `Equiv.subLeft`, `sub_sub_cancel`, `sub_right_inj`, `Matrix.sub_apply`, `Matrix.one_apply`, `Matrix.transpose_apply`, `Finset.prod_congr`, `Finset.sum_congr`, `Finset.mem_insert_self` (via `mem_insert_self`): compile in `KLSigmaPi_empty_symm`, `KLselfW_reflect`, `KLwholeP_mem_nodes`.
- Project names (merged): `Theta_apply_add_right_of_three_le` and `Theta_transpose_of_three_le` (`Propagator/Props4.lean:100, 95`; `d L g` implicit there, pass `(g := g)`), `norm_mul_mSigma_lt_one` (`Defs/Semicircle.lean:91`), `sum_Theta_row_of_three_le`, `Gauss.etaT`, `kTwo`, `thetaEdge`, `TSP`, `diagonals`, `mem_TSP`, `IsDiag`, `CrossingFree`, `Crossing`.
- Not usable as is: the merged `Theta_apply_add_right` / `Theta_transpose` (`Propagator/Basic.lean:154, 104`) take the hypothesis `‖SB d L g‖ = 1`, not `3 ≤ L`; the first compile attempt with `d L g` passed explicitly to the `_of_three_le` forms failed (`d L g` are implicit there).

## (d) Open issues and paper-delta candidates

- Paper-delta candidates: none new. T2004a-e (signed, DECISIONS §15) cover the definition choice (`KLK` = tree sum, `eq_Ktree` for `n ≥ 3`) and the range `|r| ≤ c|a|` of `KLDiffOne/KLDiffTwo`; cited, not re-proposed.
- `KLPar`, `KLPT`, `KLDecay` .. `KLZero` are definitions only: no target of this ticket takes them as a hypothesis, so no limit check is owed.
- For KL3 (ODE for the tree sum): the lemmas `KLleafPar_spec`, `KLnodePar_spec`, `KLnot_arcLe_*` of section 6 are the laminar API of `TreeRep.lean:185-413`; the generic-value part `TreeRep.lean:415-540` (`gval`, `gval_split`, ...) and the derivative `hasDerivAt_treeValW` (TreeRep.lean:555 on) are not in this file (the ticket's port range ends at 540 and names the laminar part).
- Hub notes: the ticket names the only writable file `RBM3D/Loop/KLTree.lean`; the root import is added by the hub at merge, after the last `import` line of `RBM3D.lean`.
