/-
Release check for T2488 (dispatcher V3, 2026-10-13 04:05 UTC; DECISIONS §290).  BA-L L3d1 `BAAnpLift`: G4 on the BA carrier, i.e. `lem:Anp`
(`7_8:933-1077`) at the BA law, carrier and horizon, giving L3d1's pin `BAAnpAuxG` (`Graph/BAAuxGraph2B.lean:865`) for every `d`;
twin of `Graph/AnpKey.lean` §5–§6 (`:658-836`) and of `baAnpAux_holds` (`Graph/BAAtom2.lean:694-708`) in the new file `Graph/BAAnpLift`.
Narrow design gate G4 (T2387 `:88`, `:177`), no probe step.
Part 1: merged names (the band chain, the merged BA inputs, the consumers, the instance data).  Part 2: the target statements that merged
names fix (prefix `T2488_`; content binding up to the name), then shapes (not binding; fixed at the 1a-audit).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2488-check.lean
-/
import RBM3D.Defs.StochDomAt
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWPsi
import RBM3D.Graph.AnpKey
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BALocReg2B
import RBM3D.Graph.BAMomentGen
import RBM3D.Graph.BAMomentGenB
import RBM3D.Graph.BAMomentExpGen
import RBM3D.Chain.Carrier
import RBM3D.BA.FlowPins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band pins of `lem:Anp` (`Graph/LWPins.lean:355-424`)
#check @RBM.Gauss.Sizes.LWXi
#check @RBM.Gauss.Sizes.LWAnpKey
#check @RBM.Gauss.Sizes.LWAnpKeyGh
#check @RBM.Gauss.Sizes.LWAnp
#check @RBM.Gauss.Sizes.LWPsiAll
-- the deterministic chain (model-free, imported as is: `AnpKey2`-`AnpKey6` read no law)
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.anpDetGh_holds
-- the basis: the `≺`-lift and the reductions (`Graph/AnpKey.lean:658-836`; private `anpKey_prod_ite_mul`, `anpKey_rescale`, `anpKey_stochDomAt_congr`)
#check @RBM.Graph.lwAnpKeyGh_of_det
#check @RBM.Graph.lwAnpKey_of_gh
#check @RBM.Graph.lwAnp_of_key
#check @RBM.Graph.anpKey_ghostOK_of_noGhost
#check @RBM.Graph.anpKey_noGhostPath_of_noGhost
#check @RBM.Graph.anpKey_nngh_of_noGhost
#check @RBM.Graph.lwAnpKeyGh_holds
#check @RBM.Graph.lwAnpKey_holds
#check @RBM.Graph.lwAnp_holds
#check @RBM.Graph.anpKey_oneEdge
-- the probability tools of the lift (band, law-generic, BA)
#check @RBM.Gauss.Sizes.Prec.whp
#check @RBM.Gauss.HighProbAt.inter
#check @RBM.StochDomAt.precomp_param
#check @RBM.BA.BAMomentGen_whp_of_prec
#check @RBM.BA.BAMomentGen_prec_of_whp
-- L3c1 = T2420 (`Graph/BAAtom`, `BAAtom2`): shadow, centre-level aux graph, nested form, G3, the band-flow G4
#check @RBM.Graph.BAGraph.shadow
#check @RBM.Graph.BAGraph.auxVal
#check @RBM.Graph.BAGraph.auxOrd
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.baAuxNested_holds
#check @RBM.Graph.BAAnpAux
#check @RBM.Graph.baAnpAux_holds
-- L3c3a = T2435 (`Graph/BAAuxGraph2`, `BAAuxGraph2B`): the carrier form of `LWXi`, the block variable ζ, its `hξ`, L3d1's pin
#check @RBM.Graph.LWXigL
#check @RBM.Graph.LWXigL_bandFM
#check @RBM.Graph.baZetaVar
#check @RBM.Graph.BAZetaClaim
#check @RBM.Graph.baZetaClaim_holds
#check @RBM.Graph.baGbyZeta_hxi
#check @RBM.Graph.BAAnpAuxG
-- the carrier, the BA flow, `η > 0` (`Chain/Carrier`, `BA/FlowPins`, `Graph/BAExp14a`)
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFMz
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAExp14a_eta_pos
-- the consumers: L3d2a = T2470 target 4, L3d2b-1 = T2483 targets 2, 3 (L3d2b-2's `BALWMomentExpOfAnp` is on `t/T2483b`, not merged)
#check @RBM.BA.BALWMoment
#check @RBM.BA.BALWMomentOfAnp
#check @RBM.BA.baLWMoment_of_anp
#check @RBM.BA.BALWMomentExp
#check @RBM.BA.baLWMomentOfAnp_closed
#check @RBM.Graph.baPathBinder_holds
-- the instance data (`BA/FlowPins` §Inst; the aux-graph instance graph of `BAAtom2` §5)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.Graph.BAAtomInst2.baPQ

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

noncomputable section

namespace RBM.BA.T2488Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- **Target 3** (`baAnpAuxG_holds`; content binding; the binding conclusion of L3d1): G4 on the BA carrier for every `d`, the merged pin
`BAAnpAuxG` (`BAAuxGraph2B:865`) unchanged (one text, X1-C4).  This is exactly what L3d2a (`BALWMomentOfAnp`, `BAMomentGenB:362`) and
L3d2b (`BALWMomentExpOfAnp`, `t/T2483b`) take as antecedent and what `T2483_MomentExpClosed` waits for. -/
def T2488_AnpAuxG : Prop := ∀ d : ℕ, BAAnpAuxG d

/-- **Target 4 (a)** (`baLWMoment_closed`; content binding; supervisor 2246 L40-F2): `lem:LW_moment` at BA with no antecedent left
(T2470 target 4 after the path binder, T2483 target 3, and G4, target 3 here). -/
def T2488_MomentClosed : Prop := ∀ d : ℕ, BALWMoment d

/-- **Target 4 (b)** (`baLWMomentExp_closed`; content binding; only under the start decision "L3d2b-2 merged"): `lem:LW_moment_exp` at BA with
no antecedent; equal to `T2483_MomentExpClosed` up to the name (`BALWMomentExp := baPin LWMomentExpG`, `BAMomentExpGen:183`). -/
def T2488_MomentExpClosed : Prop := ∀ d : ℕ, BALWMomentExp d

/-- Statement level (not binding): target 4 (a) from target 3 and the merged path-binder discharge `baLWMomentOfAnp_closed`. -/
example : Prop := T2488_AnpAuxG → (∀ d : ℕ, BALWMomentOfAnp d) → T2488_MomentClosed

/-- Statement level (not binding): target 4 (b) from target 3 and L3d2b-2's `baLWMomentExp_of_anp` (its statement def, unfolded). -/
example : Prop := (∀ d : ℕ, BAAnpAuxG d → BALWMomentExp d) → T2488_AnpAuxG → T2488_MomentExpClosed

/-- Statement level (not binding): the band `lem:Anp`, its band-flow BA form (merged, T2420) and the carrier form of this row, next to
each other. -/
example : Prop := (∀ d : ℕ, RBM.Gauss.Sizes.LWAnp d) ∧ (∀ d : ℕ, BAAnpAux d) ∧ T2488_AnpAuxG

/-- Shape (not binding; fixed at the 1a-audit) of target 1 `BAAnpKeyGhG d` (`∀ d` of it is `baAnpKeyGhG_holds`): `LWAnpKeyGh`
(`LWPins:389`) with `STFlow → BAFlow`, `lemT → BAflowT0`, `Prec sz → PrecL sz (seqP (sz.withLam 0))`, `LWXi sz (STflowE z) → LWXigL (baFMz sz z)
(seqP (sz.withLam 0))`, `etaT (STflowE z n) → (baFMz sz z).eta n`: the substitution that takes `BAAnpAux` to `BAAnpAuxG` (T2435-audit `:68`).
The band route `lwAnpKeyGh_of_det` (`AnpKey:689-770`) at `anpDetGh_holds` reads the flow only for `η > 0` and `size → ∞`. -/
example : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.GhostOK → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ q *
                    Φ n 0 ^ (Γ.ordN - Γ.nngh) *
                    ∏ i, (if Γ.noGhostPath i = true then
                      Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1))

/-- Shape (not binding; optional public statement def) of target 2 `BAAnpG d`: `LWAnp` (`LWPins:409`) under the same substitution
(no ghost edge, all `a_i = [a]`, `b_i = [b]`); target 3 applies it at the nested graph of `baAuxNested_holds`. -/
example : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ q *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p *
                    Φ n 0 ^ (Γ.ordN - p))

/-- Shape (not binding) of the facts the lift reads from the BA data (G4-a (iv)): `η > 0` at every `n` on the horizon (`BAExp14a_eta_pos`) and
`size → ∞` (the `Admissible` part of `BAFlow`).  Nothing else of the flow enters target 1. -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → 0 < (baFMz sz z).eta n t

end RBM.BA.T2488Check

end
