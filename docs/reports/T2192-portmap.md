# T2192 portmap (MA-D1: endpoint freeze and assembly chain), companion of `docs/reports/T2192-prove.md`

Written by script `make_portmap.py` (verbatim outputs, hand-written tables marked) at Mon Oct  5 18:04:57 UTC 2026; probe `RBM3D/Probe/T2192Pins.lean` on branch `t/T2192` at commit `97d958e` (2492 lines, base `76b840e`).  Every table marked `script` is the verbatim output of the command above it; tables marked `analysis` are hand-written and every file:line in them is verified by the scripts of P.2, P.7, P.8.  RBM2D citations are at `c9a24cf` (`git -C ../RBM2D --no-optional-locks`), RBM3D citations are at the worktree base `76b840e` (the merges T2187 `fdbb6f0`, T2189 `ae63e74` are in it).

## P.1 The pinned statements, extracted from the probe by script (`stmts.py <names>`)

```
$ python3 stmts.py decol locSC QUE QDiff BUniv calB distB Mband avg2 ThetaPM ThetaPP profPM profPP qdBound qdBoundExp decolBad locBad1z locBad2z qd1Badz locBad1 locBad2 que2BadMat MAZRange MAZGreen MAZLocal MAZAve MAZTrace MAZProfile MABtBt MAThetaDiff locSCFixed QDiffFixed MAFixed MANetLoc MANetQD MADecol MAQUE explicit_of_stochDomAt prec_of_explicit eventually_forall_of_sections det_of_prec calB_zero_eq_Bctl calB_blk_eq_STWB calB_dist_compare calB_distB_compare STWB_compare decol_spectral_core decol_of_locSC floor_X qd_core qd_exp_core locSCFixed_of_ML QDiffFixed_of_ML fixed_of_ML locSC_to_UNLocAvgBand QUE_to_UNQueBand band_endpoints_of_pins final_shape
-- RBM3D/Probe/T2192Pins.lean:164-167 decol
def decol : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
-- RBM3D/Probe/T2192Pins.lean:171-175 locSC
def locSC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
-- RBM3D/Probe/T2192Pins.lean:181-190 QUE
def QUE : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
        (∀ a : Zd d (sz.L n),
          Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ) ∧
        (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
          Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ)
-- RBM3D/Probe/T2192Pins.lean:196-205 QDiff
def QDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      (Sizes.seqP sz {ω | qd1Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, sz.locDomain κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im
-- RBM3D/Probe/T2192Pins.lean:208-208 BUniv
abbrev BUniv : Prop := UNBUniv
-- RBM3D/Probe/T2192Pins.lean:57-59 calB
def calB (sz : Sizes d) (n : ℕ) (η K : ℝ) : ℝ :=
  (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) +
    (((sz.size n : ℕ) : ℝ) * η)⁻¹
-- RBM3D/Probe/T2192Pins.lean:66-67 distB
def distB (sz : Sizes d) (n : ℕ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)
-- RBM3D/Probe/T2192Pins.lean:70-71 Mband
def Mband (sz : Sizes d) (n : ℕ) (z : ℂ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if x = y then msc z else 0
-- RBM3D/Probe/T2192Pins.lean:74-76 avg2
def avg2 (sz : Sizes d) (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (a b : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y
-- RBM3D/Probe/T2192Pins.lean:79-80 ThetaPM
def ThetaPM (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ)
-- RBM3D/Probe/T2192Pins.lean:83-84 ThetaPP
def ThetaPP (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (msc z ^ 2)
-- RBM3D/Probe/T2192Pins.lean:87-88 profPM
def profPM (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaPM sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d
-- RBM3D/Probe/T2192Pins.lean:91-92 profPP
def profPP (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaPP sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d
-- RBM3D/Probe/T2192Pins.lean:95-97 qdBound
def qdBound (sz : Sizes d) (n : ℕ) (τ η : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b))
    (calB sz n η 0 ^ 2)
-- RBM3D/Probe/T2192Pins.lean:100-102 qdBoundExp
def qdBoundExp (sz : Sizes d) (n : ℕ) (τ η : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n η 0 ^ 2 *
    ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 5) + calB sz n η 0)
-- RBM3D/Probe/T2192Pins.lean:106-109 decolBad
def decolBad (sz : Sizes d) (n : ℕ) (κ τ : ℝ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqXmat n ω) μ ψ → ∀ k, |μ k| ≤ 2 - κ → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)
-- RBM3D/Probe/T2192Pins.lean:113-116 locBad1z
def locBad1z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
      ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2
-- RBM3D/Probe/T2192Pins.lean:119-121 locBad2z
def locBad2z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖
-- RBM3D/Probe/T2192Pins.lean:124-126 qd1Badz
def qd1Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b‖
-- RBM3D/Probe/T2192Pins.lean:135-136 locBad1
def locBad1 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad1z sz τ n z ω
-- RBM3D/Probe/T2192Pins.lean:139-140 locBad2
def locBad2 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad2z sz τ n z ω
-- RBM3D/Probe/T2192Pins.lean:153-159 que2BadMat
def que2BadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (A : Finset (Zd d L))
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ k, queWindow d L W lam ε₀ E (μ k) ∧
      (W : ℝ) ^ ((d : ℝ) - c) * (A.card : ℝ) / (((W * L) ^ d : ℕ) : ℝ) ≤
        |(∑ a ∈ A, ∑ x ∈ Iblk d L W a, ‖ψ k x‖ ^ 2) -
            (W : ℝ) ^ d / (((W * L) ^ d : ℕ) : ℝ) * (A.card : ℝ)|
-- RBM3D/Probe/T2192Pins.lean:492-495 MAZRange
def MAZRange : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ →
    |lemE z| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧ lemT z < 1 ∧
      1 - lemT z = z.im / ((msc z).im + z.im) ∧ z.im / 2 ≤ 1 - lemT z
-- RBM3D/Probe/T2192Pins.lean:519-521 MAZGreen
def MAZGreen : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ω : sz.SeqΩ,
    (Real.sqrt (lemT z) : ℂ) • sz.Gt n (lemE z) (lemT z) true ω = sz.Gn n z ω
-- RBM3D/Probe/T2192Pins.lean:528-530 MAZLocal
def MAZLocal : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2 = lemT z * ‖STGM sz n (lemE z) (lemT z) ω x y‖ ^ 2
-- RBM3D/Probe/T2192Pins.lean:890-893 MAZAve
def MAZAve : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x =
      (Real.sqrt (lemT z) : ℂ) * sz.Lloop n (lemE z) (lemT z) (fun _ : Fin 1 => true) (fun _ => a) ω
-- RBM3D/Probe/T2192Pins.lean:914-919 MAZTrace
def MAZTrace : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
    avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, true] ![b, a] ω ∧
    avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, false] ![b, a] ω
-- RBM3D/Probe/T2192Pins.lean:993-996 MAZProfile
def MAZProfile : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ a b : Zd d (sz.L n),
    profPM sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, false] ![b, a] ∧
    profPP sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, true] ![b, a]
-- RBM3D/Probe/T2192Pins.lean:582-586 MABtBt
def MABtBt : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (κ : ℝ), 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → ∀ k : ℕ,
      STWB sz n (lemT z) k ≤ 2 * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt (κ * (4 - κ)) / 8) * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ≤ STWB sz n (lemT z) k
-- RBM3D/Probe/T2192Pins.lean:677-684 MAThetaDiff
def MAThetaDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b - Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b'‖ ≤
            C * (g ^ 2)⁻¹ ∧
        ‖Theta d L g (msc z ^ 2) a b - Theta d L g (msc z ^ 2) a b'‖ ≤ C * (g ^ 2)⁻¹
-- RBM3D/Probe/T2192Pins.lean:1070-1074 locSCFixed
def locSCFixed : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      Sizes.seqP sz {ω | locBad1z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
-- RBM3D/Probe/T2192Pins.lean:1078-1087 QDiffFixed
def QDiffFixed : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ z : ℂ, sz.locDomain κ ε n z →
      (Sizes.seqP sz {ω | qd1Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Badz sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im
-- RBM3D/Probe/T2192Pins.lean:1092-1092 MAFixed
def MAFixed : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed ∧ QDiffFixed
-- RBM3D/Probe/T2192Pins.lean:2043-2043 MANetLoc
def MANetLoc : Prop := locSCFixed → locSC
-- RBM3D/Probe/T2192Pins.lean:2046-2046 MANetQD
def MANetQD : Prop := QDiffFixed → QDiff
-- RBM3D/Probe/T2192Pins.lean:1843-1843 MADecol
def MADecol : Prop := locSC → decol
-- RBM3D/Probe/T2192Pins.lean:2020-2020 MAQUE
def MAQUE : Prop := QDiff → QUE
-- RBM3D/Probe/T2192Pins.lean:375-380 explicit_of_stochDomAt
theorem explicit_of_stochDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → Ω → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : StochDomAt P sz.size ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, P {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D)) := by
-- RBM3D/Probe/T2192Pins.lean:400-405 prec_of_explicit
theorem prec_of_explicit (hd : 0 < d) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (h : ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))) :
    sz.Prec ξ ζ := by
-- RBM3D/Probe/T2192Pins.lean:422-424 eventually_forall_of_sections
theorem eventually_forall_of_sections {Z : ℕ → Type*} (hne : ∀ n, Nonempty (Z n))
    {Q : ∀ n, Z n → Prop} (h : ∀ s : ∀ n, Z n, ∀ᶠ n in atTop, Q n (s n)) :
    ∀ᶠ n in atTop, ∀ z : Z n, Q n z := by
-- RBM3D/Probe/T2192Pins.lean:442-445 det_of_prec
theorem det_of_prec (hsz : sz.SizeTendsto) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω ω', ξ n u ω = ξ n u ω') (hζ : ∀ n u ω ω', ζ n u ω = ζ n u ω')
    (h : sz.Prec ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
-- RBM3D/Probe/T2192Pins.lean:230-231 calB_zero_eq_Bctl
theorem calB_zero_eq_Bctl (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) :
    calB sz n η 0 = sz.Bctl n (1 - η) := by
-- RBM3D/Probe/T2192Pins.lean:245-246 calB_blk_eq_STWB
theorem calB_blk_eq_STWB (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    calB sz n η (((sz.W n : ℕ) : ℝ) * (k : ℝ)) = STWB sz n (1 - η) k := by
-- RBM3D/Probe/T2192Pins.lean:301-303 calB_dist_compare
theorem calB_dist_compare (hd : 2 ≤ d) {η K K' : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (hKK : K ≤ K')
    (hKd : K' ≤ (d : ℝ) * K) :
    (((d : ℝ) ^ (d - 2))⁻¹) * calB sz n η K ≤ calB sz n η K' ∧ calB sz n η K' ≤ calB sz n η K := by
-- RBM3D/Probe/T2192Pins.lean:344-347 calB_distB_compare
theorem calB_distB_compare (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (a b : Zd d (sz.L n)) :
    (((d : ℝ) ^ (d - 2))⁻¹) * calB sz n η (distB sz n a b) ≤
        calB sz n η (((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)) ∧
      calB sz n η (((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)) ≤ calB sz n η (distB sz n a b) := by
-- RBM3D/Probe/T2192Pins.lean:592-594 STWB_compare
theorem STWB_compare (sz : Sizes d) (n : ℕ) {u η C : ℝ} (hη : 0 < η) (hu0 : 0 < u) (hu : η ≤ 2 * u)
    (hC1 : 1 ≤ C) (huC : u ≤ C * η) (k : ℕ) :
    STWB sz n (1 - u) k ≤ 2 * STWB sz n (1 - η) k ∧ STWB sz n (1 - η) k ≤ C * STWB sz n (1 - u) k := by
-- RBM3D/Probe/T2192Pins.lean:1789-1792 decol_spectral_core
theorem decol_spectral_core {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {μ : ι → ℝ}
    {ψ : ι → ι → ℂ} (hψ : IsOrthoEigenbasis H μ ψ) {η CM B : ℝ} (hη : 0 < η) {k x : ι} {M : ℂ}
    (hloc : ‖Gres H ((μ k : ℂ) + η * Complex.I) true x x - M‖ ≤ 1) (hM : M.im ≤ CM)
    (hB : η * (CM + 1) ≤ B) : ‖ψ k x‖ ^ 2 ≤ B := by
-- RBM3D/Probe/T2192Pins.lean:1845-1845 decol_of_locSC
theorem decol_of_locSC : MADecol := by
-- RBM3D/Probe/T2192Pins.lean:1278-1280 floor_X
theorem floor_X (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {𝔠 η K : ℝ} (h𝔠 : 0 < 𝔠)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1) (hK : 0 ≤ K) :
    ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠))) ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η K := by
-- RBM3D/Probe/T2192Pins.lean:1315-1323 qd_core
theorem qd_core (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {𝔠 κ τ e Δ : ℝ} (h𝔠 : 0 < 𝔠) (hκ : 0 < κ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1)
    (hre : |z.re| ≤ 2 - κ) (hW : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (a b : Zd d (sz.L n))
    (hΔ : 0 ≤ Δ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (h1 : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (lemT z) ^ ((1 : ℝ) / 5) * STWB sz n (lemT z) (zdistInf d (sz.L n) (b - a)) * e +
        ((sz.W n : ℕ) : ℝ) ^ (-(6 / (5 * 𝔠)))))
    (h2 : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (lemT z) ^ 2) :
    lemT z * Δ ≤ qdBound sz n τ z.im a b := by
-- RBM3D/Probe/T2192Pins.lean:1429-1433 qd_exp_core
theorem qd_exp_core (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ τ Δ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) (hre : |z.re| ≤ 2 - κ) (hW : 8 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (hΔ : 0 ≤ Δ)
    (h : Δ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (lemT z) ^ 2 *
      ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (lemT z)))) :
    lemT z * Δ ≤ qdBoundExp sz n τ z.im := by
-- RBM3D/Probe/T2192Pins.lean:1156-1156 locSCFixed_of_ML
theorem locSCFixed_of_ML (hML : ∀ d, UNMLOut d) : locSCFixed := by
-- RBM3D/Probe/T2192Pins.lean:1475-1475 QDiffFixed_of_ML
theorem QDiffFixed_of_ML (hML : ∀ d, UNMLOut d) : QDiffFixed := by
-- RBM3D/Probe/T2192Pins.lean:1594-1594 fixed_of_ML
theorem fixed_of_ML : MAFixed := fun hML => ⟨locSCFixed_of_ML hML, QDiffFixed_of_ML hML⟩
-- RBM3D/Probe/T2192Pins.lean:2055-2055 locSC_to_UNLocAvgBand
theorem locSC_to_UNLocAvgBand : locSC → UNLocAvgBand := by
-- RBM3D/Probe/T2192Pins.lean:2066-2066 QUE_to_UNQueBand
theorem QUE_to_UNQueBand : QUE → UNQueBand := by
-- RBM3D/Probe/T2192Pins.lean:2079-2080 band_endpoints_of_pins
theorem band_endpoints_of_pins (hML : ∀ d : ℕ, UNMLOut d) (hNL : MANetLoc) (hNQ : MANetQD)
    (hQ : MAQUE) : decol ∧ locSC ∧ QUE ∧ QDiff := by
-- RBM3D/Probe/T2192Pins.lean:2090-2094 final_shape
theorem final_shape (rI : UNInfty1Row) (rU : UNUnivMainRow) (rC : UNClaimRow) (rE : UNEMCTE2Row)
    (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow)
    (Thm27 : Prop) (hBA : Thm27) (hML : ∀ d : ℕ, UNMLOut d) (hNL : MANetLoc) (hNQ : MANetQD)
    (hQ : MAQUE) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) :
    UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff ∧ Thm27 := by
```

## P.2 Differences of the frozen pins from every copy (analysis; the cited lines are verified by `copies.py`, lesson 26)

```
$ python3 copies.py
| copy | ref:file:line | verified |
|---|---|---|
| T2001_decol | t/T2001:RBM3D/Probe/T2001Endpoints.lean:128 | yes |
| T2001_locSC | t/T2001:RBM3D/Probe/T2001Endpoints.lean:158 | yes |
| T2001_QUE | t/T2001:RBM3D/Probe/T2001Endpoints.lean:195 | yes |
| T2001_BUniv | t/T2001:RBM3D/Probe/T2001Endpoints.lean:230 | yes |
| T2001_QDiff | t/T2001:RBM3D/Probe/T2001Endpoints.lean:297 | yes |
| UNQueBand (T2162 probe) | t/T2162:RBM3D/Probe/T2162Pins.lean:403 | yes |
| UNLocAvgBand (T2162 probe) | t/T2162:RBM3D/Probe/T2162Pins.lean:415 | yes |
| UNBUniv (T2162 probe) | t/T2162:RBM3D/Probe/T2162Pins.lean:176 | yes |
| BAcalB | t/T2161:RBM3D/Probe/T2161Pins.lean:1483 | yes |
| BAlocSCConcl | t/T2161:RBM3D/Probe/T2161Pins.lean:1503 | yes |
| BAqdConcl | t/T2161:RBM3D/Probe/T2161Pins.lean:1516 | yes |
| BAEnd_locSC | t/T2161:RBM3D/Probe/T2161Pins.lean:1543 | yes |
| BAEnd_QDiff | t/T2161:RBM3D/Probe/T2161Pins.lean:1548 | yes |
| BAEnd_decol | t/T2161:RBM3D/Probe/T2161Pins.lean:1565 | yes |
| BAEnd_QUE | t/T2161:RBM3D/Probe/T2161Pins.lean:1602 | yes |
| BAEnd_BUniv | t/T2161:RBM3D/Probe/T2161Pins.lean:1652 | yes |
| BAThm27 | t/T2161:RBM3D/Probe/T2161Pins.lean:1659 | yes |
| UNQuek (T2173 probe) | t/T2173:RBM3D/Probe/T2173Pins.lean:2378 | yes |
| UNLocAvgk (T2173 probe) | t/T2173:RBM3D/Probe/T2173Pins.lean:2390 | yes |
| UNQueBA | t/T2173:RBM3D/Probe/T2173Pins.lean:2405 | yes |
| UNLocAvgBA | t/T2173:RBM3D/Probe/T2173Pins.lean:2407 | yes |
| UNMLOutBA | t/T2173:RBM3D/Probe/T2173Pins.lean:2414 | yes |
| BAEnd_BUnivL | t/T2173:RBM3D/Probe/T2173Pins.lean:3230 | yes |
| BAEnd_QUEL | t/T2173:RBM3D/Probe/T2173Pins.lean:3249 | yes |
| UNBUniv (merged) | main(76b840e):RBM3D/Universality/Pins.lean:177 | yes |
| UNQueBand (merged) | main(76b840e):RBM3D/Universality/Pins.lean:404 | yes |
| UNLocAvgBand (merged) | main(76b840e):RBM3D/Universality/Pins.lean:416 | yes |
| UNMLOut (merged) | main(76b840e):RBM3D/Universality/Pins.lean:432 | yes |
| UNQuek (merged) | main(76b840e):RBM3D/Universality/PinsK.lean:398 | yes |
| UNLocAvgk (merged) | main(76b840e):RBM3D/Universality/PinsK.lean:406 | yes |
| UNQuek_band (merged) | main(76b840e):RBM3D/Universality/PinsK.lean:552 | yes |
| UNLocAvgk_band (merged) | main(76b840e):RBM3D/Universality/PinsK.lean:554 | yes |
| docs check copy UNQuek | docs/tickets/checks/T2187-check.lean:280 | yes |
| docs check copy UNLocAvgk | docs/tickets/checks/T2187-check.lean:288 | yes |
| RBM2D decol | c9a24cf:RBM2D/Endpoints.lean:88 | yes |
| RBM2D locSC | c9a24cf:RBM2D/Endpoints.lean:99 | yes |
| RBM2D QUE | c9a24cf:RBM2D/Endpoints.lean:145 | yes |
| RBM2D QDiff | c9a24cf:RBM2D/Endpoints.lean:173 | yes |
| RBM2D BUniv | c9a24cf:RBM2D/Endpoints.lean:209 | yes |

copies listed and verified by git show at the cited ref: 39; mismatches: 0 []
BAcalB (T2161:1483) and calB (probe) bodies identical after whitespace normalisation: True
  T2161 body: (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) + (((sz.size n : ℕ) : ℝ) * η)⁻¹
  probe body: (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) + (((sz.size n : ℕ) : ℝ) * η)⁻¹
```

Quantifier order of the freeze, for all four band endpoints: `(d, 𝔠, 𝔡, sz : Sizes d)` with `Admissible 𝔠 𝔡` (`0 < 𝔠, 0 < 𝔡`, `N → ∞`, `W ≥ N^𝔠`, `(eq:WO)`), then `(κ, [ε,] [τ,] D)` or `(κ, ε₀, c, τ)`, then `∀ᶠ n`; the energy `E`, the block `a`, the set `A` and the point `z` are inside `∀ᶠ n` (`N₀` uniform).

| freeze | copy | differences (quantifiers, carrier, metric, scale, exponents) |
|---|---|---|
| `decol` | `T2001_decol` (t/T2001:128) | same order and bound `N^{-1+τ}`, `N^{-D}`.  T2001: probe-local `SizeSeq`, `Admissible d 𝔠 𝔡 s` with `0 < 𝔠 → 0 < 𝔡 →` outside, carrier `Hmat` on `Vtx`; freeze: merged `Sizes`, `Admissible` (positivity inside), `seqXmat` on `Idx`, merged `IsOrthoEigenbasis`. |
| `decol` | RBM2D `decol` (Endpoints.lean:88) | RBM2D: `(𝔠, d : Sizes)`, no `𝔡`, no dimension, no `(eq:WO)`; `N = (WL)²`; `μ ∈ Icc (-2+κ) (2-κ)`. |
| `locSC` | `T2001_locSC` (:158) | same `∩_z` inside (T2001b).  T2001: block `ℓ¹` distance `zdistD`, `bulkDomain N edge κ ε z`, `Gof (Hmat)`; freeze: block `L^∞` distance `zdistInf` (`distB`; T2001e with the paper's metric `1_2:274`, as merged `STLocalEntry`), `Sizes.locDomain`, `Gn`, `msc`. |
| `locSC` | RBM2D `locSC` (Endpoints.lean:99) | RBM2D: pointwise in `z` (`∀ z` outside `P`); threshold `W^τ/√Meta` (`Meta = W² ℓ(z)² η`, d = 2 scales); domain `locDomain N κ τ z` with ONE parameter (`N^{-1+τ} ≤ η`); freeze: threshold `W^τ 𝓑_{η,|x-y|}` (two terms, `ilambda`), domain `(κ, ε)` independent of `τ`, `∩_z` inside. |
| `QUE` | `T2001_QUE` (:195) | same shape and bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}`; T2001 `QueBad`/`Que2Bad` on `Vtx`/`blockSet`, own `queWindow g`; freeze: merged `queBadMat`, `queBound`, `queWindow` (`lam`) on `Idx`/`Iblk`, new `que2BadMat` (same formula as `Que2Bad`); `A.Nonempty` in both (T2001f). |
| `QUE` | RBM2D `QUE` (Endpoints.lean:145) | not comparable: the d = 2 paper's QUE has window `N^{-1-τ}W^{2/3}`, threshold `N^{-τ/6}`, constraint `τ < 𝔠/2`, bound `N^{-τ/6}` (an `N`-power); the d = 3 statement has `(ε₀, c, τ)` and a `W`-power bound. |
| `QDiff` | `T2001_QDiff` (:297) | same `∩_z` and blocks `a, b` inside; T2001 `profBand1/2` on `Theta`, `qdBound` with `zdistD`, `QDExp` inline; freeze: merged `Theta`, `profPM/profPP`, `distB` (L^∞), expectation half inline, `N₀` uniform over `𝐃_{κ,ε}`. |
| `QDiff` | RBM2D `QDiff` (Endpoints.lean:173) | RBM2D: pointwise in `z`; `trGEGE` (trace form); bounds `W^τ/Meta²`, `Meta^{-3}W^τ`; freeze: sum form `avg2` (the loop indices swap, see `MAZTrace`), bounds `W^τ[(𝓑_{η,0})^{1/5}𝓑_{η,W|a-b|} ∧ (𝓑_{η,0})²]`, `W^τ(𝓑_{η,0})²((ilambda²W^d)^{-1/5}+𝓑_{η,0})`. |
| `BUniv := UNBUniv` | `T2001_BUniv` (:230), RBM2D `BUniv` (:209) | identical to the merged UN pin (Pins.lean:177); T2001: `eigs` (junk `0` off Hermitian), `Vtx`; merged: `IsHermitian.eigenvalues`, `Idx`. |
| `QUE` first conjunct | `UNQueBand` (Pins.lean:404) | a projection (`QUE_to_UNQueBand`: 3 lines including the statement, 2 of proof; compiled). |
| `locSC` second conjunct | `UNLocAvgBand` (Pins.lean:416) | threshold `sz.Bctl n (1 - z.im)` there, `calB sz n z.im 0` here: equal for `0 < z.im` (`calB_zero_eq_Bctl`); `Gres (seqXmat) z true = Gn` by `rfl`; the bridge `locSC_to_UNLocAvgBand` is 8 lines including the statement, 7 of proof (compiled), not a projection. |
| both | `UNQuek`, `UNLocAvgk` (PinsK.lean:398, 406) and their T2173 probe copies (:2378, :2390), `docs/tickets/checks/T2187-check.lean:280, 288` | model-generic over `K : ∀ d, UNKind d`; at `K = UNKind.band` they are `UNQueBand`, `UNLocAvgBand` by `Iff.rfl` (PinsK.lean:552, 554); BA: `UNQueBA`, `UNLocAvgBA` (t/T2173:2405, 2407). |
| `locSC` | `BAEnd_locSC` (t/T2161:1543), `BAlocSCConcl` (:1503) | `Prec` form (scale `N^τ`) with `BAcalB` (= `calB`, body identical by script above); block `ℓ¹` distance `zdistD`; domain `BAendDom` (ρ-bulk); `M = BAMz`; law `seqP sz` (T2173a: must be `seqP (sz.withLam 0)`).  Bridge to the explicit form: `explicit_of_stochDomAt` (any law, compiled).  `zdistD ≥ zdistInf` makes the `ℓ¹` threshold smaller (a stronger statement); the two agree up to `d^{d-2}`: compiled `calB_distB_compare` (`d^{-(d-2)} 𝓑_{η,W|a-b|_∞} ≤ 𝓑_{η,W|a-b|_1} ≤ 𝓑_{η,W|a-b|_∞}`, from the merged `zdistInf_le_zdistD`, `zdistD_le_mul_zdistInf`, `Defs/Sizes.lean:117, 122`). |
| `QDiff` | `BAEnd_QDiff` (:1548), `BAqdConcl` (:1516) | `Prec` form, four conjuncts incl. the two expectation halves as `Prec` of a deterministic `ξ` (bridge: `det_of_prec`), profile `BAprof = (ΘM)_{ab}`, `∩_z` and `(a,b)` inside through the index type. |
| `decol` | `BAEnd_decol` (:1565) | explicit form with `BAbulk`, law `seqP sz`. |
| `QUE` | `BAEnd_QUE` (:1602), `BAEnd_QUEL` (t/T2173:3249) | explicit `W`-power bound (the freeze's `queBound` formula), `BAqueWindow` (the freeze's window formula), bulk `BAbulk`; `QUEL` corrects the law. |

## P.3 The assembly-chain pins (analysis; consumer lines verified by the scripts of P.2, P.7)

Last column, the seven points of the ticket: (1) time domain `0 ≤ s`, `t < 1`, `t ≤ lemT z`; (2) the case (ii) boundary `1 - ilambda²/L²` (DECISIONS §29 (2)); (3) the polynomial relation `L^d ≤ W^K` between `L` and `W` (§29 (3)); (4) `∀ n` against `∀ᶠ n` (§29 (4)); (5) `Prec`/`PrecPT` and where `∩_z` sits; (6) lower bounds from `(eq:WO)`, `SizeTendsto`, `(Main_DEL_COND)`; (7) the scales of the consumers.  No pin uses (2) or (3): the time is `t = lemT z` with `1 - t = Im z/(Im m + Im z) ≥ Im z/2` (`zRange`), and no relation of `L` and `W` is used beyond `W ≥ N^𝔠` (inside `Admissible`) and the identity `N = (WL)^d`.

| pin (probe line) | status | owed by | consumer (file:line) | RBM2D source (c9a24cf) | §29 (1)-(7) |
|---|---|---|---|---|---|
| `MAZRange` (492), `zRange` | compiled | - | `MABtBt`, `locSCFixed_of_ML` (uses `lemT z < 1`), net (`‖Θ‖ ≤ 2/η`) | `ZRange` (ZRescale.lean:52), `zRange` :183 | (1) `0<Im z≤1`, `\|Re z\|≤2-κ` give `t₀∈[1/16,1)`, `1-t₀ = Im z/(Im m+Im z) ≥ Im z/2`; (2)-(3) not used; (4) pointwise in `z`; (5) -; (6) `Im m > 0` (`msc_im_pos`); (7) - |
| `MAZGreen` (519), `zGreen` | compiled (merged `Gt_lemT`, Loop/GLoopFlow.lean:181) | - | `zLocal`, `zAve`, `zTrace` | `ZGreen` :61, `zGreen` :151 | (1) `t = lemT z`, the endpoint value of the flow time of `UNMLOut` (`t_n ≤ lemT z_n` is used with `le_rfl`); one time only, no coupling; (4) pointwise in `ω`; others - |
| `MAZLocal` (528), `zLocal` | compiled | - | `locSCFixed_of_ML` (Universality/Pins.lean:432 `UNMLOut`: `STLocalEntry`) | `EndpointsFromSTO_gEntry_le` (EndpointsFromSTO.lean:264) | `\|G-M\|² = t₀ \|STGM\|²` with `t₀<1`; (7) `STGM` is the merged `Induction/Defs.lean` quantity |
| `MAZAve` (890), `zAve` | compiled | - | `locSCFixed_of_ML`; `STLK` `k=1` | `ZAve` :79, `zAve` :307 | `E_a` has weight `W^{-d}` (`Eblk`); (7) `W^{-d}Σ_{x∈[a]}G_xx = √t₀ 𝓛^{(1)}` |
| `MAZTrace` (914), `zTrace` | compiled | - | `QDiffFixed_of_ML` | `ZTrace` :90, `zTrace` :316 | **loop indices swap**: `W^{-2d}Σ_{x∈[a],y∈[b]}G_xy G^σ_yx = t₀ 𝓛^{(2)}_{(+,σ),(b,a)}`; RBM2D uses `trGEGE` (trace form), so no swap there |
| `MAZProfile` (993), `zProfile` | compiled | - | `QDiffFixed_of_ML` | `ZProfile` :99, `zProfile` :210 | uses `KLK_two` (Loop/KLTree.lean:211), `mE_lemE`, `Theta_transpose`; `(b,a)` order as `MAZTrace` |
| `MABtBt` (582), `btBt`, `STWB_compare`, `calB_distB_compare` (T2001e: `zdistInf`/`zdistD`, factor `d^{-(d-2)}`) | compiled | - | `locSCFixed_of_ML`, `QDiffFixed_of_ML`, net | `ZMeta` :71, `zMeta` :416 (d = 2 scales) | constants `2` and `√(κ(4-κ))/8` (verified, preflight numeric lower ratio 0.312-0.295 at `κ=0.1`: the analytic constant is not sharp); (6) `Im m ≥ √(κ(4-κ))/8` (`im_msc_ge`) |
| `MAThetaDiff` (677), `thetaDiff` | compiled | - | `MAQUE` | `QUEFromQDiff_profile_diff` (QUEFromQDiff.lean:465), `norm_Theta_sub_le_log` | `g ≤ 𝔡⁻¹` (=`Λ` of `Prop8ZeroMode`), `κ' = √(κ(4-κ))/2 ≤ Im m'`, `t=t₀<1`; no `log L`; (6) `L ≥ 3` |
| `locSCFixed` (1070), `locSCFixed_of_ML` | compiled | - (MA-03 ports it) | `MANetLoc` | pointwise `locSC` (Endpoints.lean:99), `locSC_of_pins` :518 | (4) `∀ᶠ n, ∀ z` (uniform `N₀`, sections lemma); (5) `Prec` over `x,y`/`a` inside, `z` outside, from `UNMLOut` at section sequences; (6) `W→∞` (`RBM.Green.tendsto_W`), `N>1`; (7) `W^τ` vs `N^τ`: `explicit_of_prec` at `τ/2`, `W^{τ/2} ≥ 2` |
| `QDiffFixed` (1078), `QDiffFixed_of_ML` (1475) | compiled (`qd_core`, `qd_exp_core`, `floor_X`, `prob_union_le`) | - (MA-03 ports it) | `MANetQD` | pointwise `QDiff` (Endpoints.lean:173), `QDiff_of_pins` :565 | (1) `t = lemT z`; (5) both options of `qdBound` from `STDecay` (`D'' = 6/(5𝔠)`, the additive `W^{-D''} ≤ 𝓑_{η,0}^{1/5}𝓑_{η,K}` by `floor_X`) and `STLK 2`, `min (2aX, aY) ≤ 2a min (X, Y)`, union of two events with `D+1`; (6) `W^{τ/2} ≥ 8`, `N ≥ 2`; (7) `W^{τ/2}` for the probability halves, `N^{𝔠τ/2} ≤ W^{τ/2}` for the expectation halves (`STExp2` through `det_of_prec`) |
| `MAFixed` (1092), `fixed_of_ML` | compiled | - (MA-03 ports it) | `band_endpoints_of_pins` | `locSC_of_pins`, `QDiff_of_pins` | input `∀ d, UNMLOut d`: `STLK`, `STDecay`, `STExp2`, `STLocalEntry` used, `STLmax` not used |
| `MANetLoc`, `MANetQD` (2043, 2046) | pin | MA-04 | `locSC`, `QDiff`, hence `UNLocAvgBand` | `RegionUnifOfPT` (RegionUnif.lean:815), `regionUnif_core` :85 | (4) eventually; (5) union over a net of `≤ 25N^{14}` points inside; (6) `η ≥ N^{-1+ε}`, `ε>0` fixed; (7) per-point `D+15`, `τ/2` |
| `MADecol` (1843), `decol_of_locSC` | compiled | - (MA-03 ports it) | `final_shape` | `decol_of_locSC` (DecolFromLocal.lean:239) | (5) `∩_z` inside makes the energy net unnecessary (`decol_core`); (6) `lam ≥ W^{-d/2+𝔡}` (`decol_scalars`), `W→∞`; (7) `ε = min(τ/2,1/2)`, `τ_L = min(𝔡,dε/2)` |
| `MAQUE` (2020) | pin | MA-05 | `final_shape`, `QUE_to_UNQueBand` | `QUE_of_QDiff` (QUEFromQDiff.lean:1048) | uses `QDiff` at `ε = 𝔠(𝔡-ε₀)` (`queDomain`) uniformly in `E`; (6) `ε₀ < 𝔡/2`, `c < ε₀∧𝔡/5`, `lam ≤ 𝔡⁻¹` |

## P.4 The d = 2 facts of the RBM2D `Main/*` files and their d ≥ 3 replacements (script `d2.py`; the diff-stat shows that RBM2D HEAD differs from `c9a24cf`, in particular `RegionUnif.lean` is absent at HEAD)

```
$ python3 d2.py
| file (RBM2D @c9a24cf) | lines | Z2 | Meta/ellz/scaleM/cMeta | log L | ^2 (W^2, N=(WL)^2) | Epaper |
|---|---|---|---|---|---|---|
| RBM2D/Endpoints.lean | 268 | 9 | 6 | 0 | 13 | 3 |
| RBM2D/Main/Endpoints.lean | 71 | 0 | 1 | 0 | 0 | 0 |
| RBM2D/Main/P7FromSTO.lean | 183 | 1 | 1 | 0 | 0 | 0 |
| RBM2D/Main/ZRescale.lean | 459 | 9 | 16 | 0 | 27 | 12 |
| RBM2D/Main/EndpointsFromSTO.lean | 811 | 34 | 76 | 0 | 15 | 0 |
| RBM2D/Main/DecolFromLocal.lean | 361 | 0 | 7 | 0 | 31 | 0 |
| RBM2D/Main/QUEFromQDiff.lean | 1084 | 33 | 7 | 17 | 88 | 15 |
| RBM2D/Main/RegionUnif.lean | 950 | 7 | 14 | 0 | 84 | 0 |
| RBM2D/Main/BUniv.lean | 71 | 0 | 0 | 0 | 0 | 0 |
| RBM2D/Main/BUnivHolds.lean | 76 | 0 | 0 | 0 | 0 | 0 |

d=2 facts beyond tokens (file:line; the d>=3 replacement is in the probe):
- RBM2D/Main/QUEFromQDiff.lean:27: Fourier bound with 90(1+log L) on Theta differences  =>  thetaDiff (probe): |Theta_ab - Theta_ab'| <= 2 C8 ilambda^-2 from prop5to8_holds (Prop8ZeroMode) + Theta_apply_add_right; no log
- RBM2D/Main/QUEFromQDiff.lean:914: absorb log L into L^{c/12}  =>  not needed: no log L at d>=3
- RBM2D/Main/QUEFromQDiff.lean:813: QUE scale eta=W^{2/3}/N and the Meta lower bound  =>  etaQ = W^{-eps0} lam W^{d/2}/N, queDomain, calB_le_two_inv, etaQ_le, que_three_terms (probe)
- RBM2D/Main/ZRescale.lean:416: Meta <= cMeta * scaleM (d=2 scales ellz, scaleM)  =>  btBt (probe): STWB <= 2 calB, (sqrt(kappa(4-kappa))/8) calB <= STWB
- RBM2D/Main/EndpointsFromSTO.lean:236: control comparison M_u^{-1} <= c_kappa M_eta^{-1}  =>  btBt + calB_zero_eq_Bctl
- RBM2D/Main/RegionUnif.lean:10: Gaussian entry-tail event Xi (H_t = sqrt(t) X unbounded)  =>  not needed: z-net in the direct parametrization is deterministic (preflight row 6)
- RBM2D/Main/DecolFromLocal.lean:132: energy net E_j (pointwise locSC)  =>  not needed once the union over z is inside (decol_core, probe)
```

```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Endpoints.lean RBM2D/Main/ZRescale.lean RBM2D/Main/EndpointsFromSTO.lean RBM2D/Main/DecolFromLocal.lean RBM2D/Main/QUEFromQDiff.lean RBM2D/Main/RegionUnif.lean RBM2D/Main/P7FromSTO.lean
 RBM2D/Endpoints.lean             |  66 +--
 RBM2D/Main/DecolFromLocal.lean   |  43 +-
 RBM2D/Main/EndpointsFromSTO.lean | 226 +---------
 RBM2D/Main/P7FromSTO.lean        |  22 +-
 RBM2D/Main/QUEFromQDiff.lean     |  37 +-
 RBM2D/Main/RegionUnif.lean       | 950 ---------------------------------------
 RBM2D/Main/ZRescale.lean         |  51 +--
 7 files changed, 100 insertions(+), 1295 deletions(-)
```

## P.5 The split table and the count against DECISIONS §9 O2 (script `split.py`; lines are estimates built from measured probe sections and measured RBM2D line ranges, not measured Lean)

```
$ python3 split.py
probe sections (lines): {'Endpoints': 161, 'Scalars': 148, 'Form': 96, 'Transfer': 192, 'ThetaDiff': 106, 'Loops': 284, 'Fixed': 69, 'FixedProof': 131, 'QDFixed': 330, 'Spectral': 83, 'Decol': 178, 'QUE': 157, 'Bridges': 21, 'Skeleton': 28, 'Inst': 379}
Inst theorem lines by ticket (script): {'MA-01': 254, 'MA-02': 41, 'MA-03': 37, 'MA-05': 28, 'MA-06': 14}  unassigned: []

| id | file | content | components (lines) | deps | role | lo | central | hi |
|---|---|---|---|---|---|---|---|---|
| MA-01 | `RBM3D/Endpoints.lean` | freeze: calB, distB, events, decol, locSC, QUE, QDiff, BUniv; calB lemmas; Prec<->explicit; bridges to UN; instances, edges, extremes; Axioms rows | probe Endpoints 161; probe Scalars 148; probe Form 96; probe Bridges 21; probe Inst (MA-01 part) 254; domain lemmas (Fixed part) 40; registry rows + docstrings 40 | - | prover-hard | 610 | 760 | 990 |
| MA-02 | `RBM3D/Main/ZTransfer.lean` | zztE transfer (zRange, zGreen, zLocal, zAve, zTrace, zProfile) and (eq:BtBt) (btBt, STWB_compare, calB_distB_compare uses MA-01); all compiled in the probe | probe Transfer 192; probe Loops 284; probe Inst (MA-02 part) 41; docstrings, registry-free 20 | MA-01 | prover | 430 | 540 | 700 |
| MA-03 | `RBM3D/Main/FixedZ.lean` | fixed-z statements locSCFixed, QDiffFixed from UNMLOut (sections lemma, UNMLOut at t = lemT z, STLK/STDecay/STExp2, W^{-6/(5c)} floor, union bound) and decol from locSC (ukx, spectral core, no net); all compiled in the probe | probe Fixed (pins, domain lemmas) 69; probe FixedProof 131; probe QDFixed 330; probe Spectral 83; probe Decol 178; probe Inst (MA-03 part) 37 | MA-01, MA-02 | prover | 660 | 830 | 1080 |
| MA-04 | `RBM3D/Main/ZNet.lean` | z-net: MANetLoc, MANetQD (direct parametrization: Lipschitz of G, msc, Theta, calB ratio; 2D grid; union bound) | abstract net core (RBM2D regionUnif_core 54-~200) 150; 2D grid + cover (new) 120; msc Lipschitz (new) 60; Theta_xi Lipschitz (new) 120; calB ratio, floor (new, uses calB_antitone etc.) 60; entry/resolvent wrappers (merged cont_green_diff) 60; assembly MANetLoc 150; assembly MANetQD 250; instances 60 | MA-01 | prover-max | 820 | 1030 | 1340 |
| MA-05 | `RBM3D/Main/QUEFromQDiff.lean` | QUE from QDiff: spectral (ssfa2), observable B_c, integrability, core, queBad/que2Bad subsets, Markov, d=3 chain (queDomain, BetaK, three terms, thetaDiff) | probe QUE 157; probe ThetaDiff 106; RBM2D QUEFromQDiff 44-797 + 798-812 (port) 754; d=3 chain assembly (replaces RBM2D 813-1046) 280; final QUE_of_QDiff 60; instances 88 | MA-01 | prover-hard | 1160 | 1440 | 1880 |
| MA-06 | `RBM3D/MainTheorems.lean` | terminal: UNL32 -> decol and locSC and QUE and BUniv and QDiff and Thm27 (final_shape), instances; may merge into the final cleanup ticket (DECISIONS 45 O5) | probe Skeleton 28; probe Inst (MA-06 part) 14; wiring to UN-52, BA terminals, registry, instances 300 | MA-01..05, ST-6, UN-52, BA-M3, BA-N2 | prover | 270 | 340 | 440 |
| total | | | | | | 3950 | 4940 | 6430 |

COUNT (DECISIONS 9 O2: 25 / 40 / 50): MA band chain = 6 tickets (MA-01..MA-05 plus the terminal MA-06; 5 if MA-06 merges into the final cleanup ticket, DECISIONS 45 O5; lo 5, hi 7 if MA-05 or MA-04 splits); 6 < 25: no threshold is reached.
Tickets above 1500 central lines: []  with hi above 1500: ['MA-05']
```

Against the dispatcher's lead (ticket item 5): MA-01 freeze 760 (lead ~700); the lead's MA-02 "fixed-`z` statements" (~1400) is now MA-02 (the transfer `zRange ... zProfile` and `(eq:BtBt)`, 540) plus the fixed-`z` statements themselves, which the probe compiles from `UNMLOut` (`locSCFixed_of_ML`, `QDiffFixed_of_ML`, `fixed_of_ML`: sections `FixedProof`, `QDFixed`) and which go with `decol` from `locSC` (compiled `decol_of_locSC`, sections `Spectral`, `Decol`, 261 lines, no net) into MA-03 (830, hi 1080); `decol` therefore leaves the lead's MA-04 ("decol and QUE", ~1450) and QUE (MA-05, 1440, hi 1880) stands alone; the net (MA-04, 1030, `prover-max`: new route, no RBM2D template) is the lead's MA-03 (~1000); the terminal (MA-06, 340 < 500) merges into the final cleanup ticket (§45 O5) if the dispatcher prefers: count 5.  If MA-05 exceeds 1500 in its first round, split at the carrier-free boundary (RBM2D `QUEFromQDiff.lean` 44-402 and 798-812 against the rest): count 7.  Dependencies: MA-02, MA-04, MA-05 need only MA-01 (hypothesis-based statements); MA-03 needs MA-01, MA-02; MA-06 needs MA-01..05 and ST-6, UN-52, BA-M3, BA-N2.  The critical path is ST-6 (`UNMLOut`), not MA.  MA-02 and MA-03 are ports of compiled text (role `prover`); the uncompiled risk is MA-04 (net) and MA-05 (QUE deduction).

## P.6 Interfaces (analysis + scripts `carrier.py`, `price.py`)

**MA consumes** (merged unless stated):

| consumed | producer | form (file:line) | class |
|---|---|---|---|
| `∀ d, UNMLOut d` | ST-6 (design ST-D6 unwritten) | Universality/Pins.lean:432: `STLK`, `STLmax`, `STDecay`, `STExp2`, `STLocalEntry` (Induction/Defs.lean:104, 112, 121, 159, 151) at every `0 ≤ t_n ≤ lemT z_n` along `STFlow` (:286) | owed (ST-6) |
| PT facts | merged | `prop5to8_holds` (Propagator/Prop6Hold.lean:433), `Theta_apply_add_right` (Basic.lean:154), `Theta0_apply` (:229), `norm_SB` (Defs/Block.lean:136), `Theta_transpose` | proved |
| flow, loops | merged | `Gt_lemT` (Loop/GLoopFlow.lean:181), `lemma28_quant` (Defs/Semicircle.lean:359), `msc_eq_sqrt_mul_mE` (:264), `KLK_one`, `KLK_two` (Loop/KLTree.lean:206, 211), `cont_green_diff` (Induction/ContinuityNet.lean:448) | proved |
| `UNL32` | - | not consumed by MA (only by UN, through `UNBUniv`) | borrowed |

**Where the iteration `STMainInd → UNMLOut` belongs**: ST-D6 (ST-6), not MA.  The inputs of the iteration (`STMainInd` Induction/Defs.lean:294, `STKbound`, `STLK` at `t = 0`, `STConStInd`) are ST vocabulary; RBM2D keeps the iteration in `Induction/` (`mlConcl_of_R3`, Induction/MainInd.lean:144, with `chainTarget`, `mainIndPinV3_of_R3` :110) and its MA file `Main/P7FromSTO.lean` adds only the `t`-modification (`P7FromSTO_tmod` :89) and the universal closure (`STOAll` :63, `p7Out_of_STOAll` :139), neither of which exists in RBM3D: `UNMLOut` is already stated for all `0 ≤ t_n ≤ lemT z_n` and `STMainInd` is already closed over `κ, ε, 𝔡, 𝔠`.  MA uses four of the five outputs (`STLmax` is not used; it is in `UNMLOut` for UN).

**MA gives UN**: `locSC_to_UNLocAvgBand` (8 lines including the statement), `QUE_to_UNQueBand` (3 lines), both compiled in the probe; UN-25..52 take them as hypotheses of `UNOURow`, `UNJakUywRow`, `UNTrLocalBandRow`; `BUniv := UNBUniv` is not re-pinned.

**MA gives BA** (BA-M1..M3 keep their own endpoint tickets in the BA budget, T2161 portmap P.9): the compiled bridges `explicit_of_stochDomAt` (any law `P`, so for `seqP (sz.withLam 0)`), `prec_of_explicit`, `det_of_prec` (the expectation halves as `Prec` of a deterministic `ξ`), `calB_distB_compare` (the `ℓ¹` block distance of T2161 against the freeze's `L^∞`), `STWB_compare`, `decol_spectral_core`/`ukx`, `eventually_forall_of_sections`, `floor_X`, `prob_union_le`; `BAcalB` is `calB` (body identical, `copies.py`), so BA's `Prec` conclusions bridge to the explicit form without a new lemma.

Abstract carrier (bulk predicate, `m`, `M`, profile, `Θ`-difference as hypotheses): the compiled proofs split as follows (script `carrier.py`, lines of the declaration ranges without the instance section):

```
$ python3 carrier.py
| compiled declaration | lines | carrier-free? | why |
|---|---|---|---|
| explicit_of_stochDomAt | 19 | yes | any law P, any Omega |
| prec_of_explicit | 20 | yes | Prec at seqP sz (law-parametric by the same proof) |
| eventually_forall_of_sections | 22 | yes | any family Z n |
| det_of_prec | 34 | yes | Prec at seqP sz (law-parametric by the same proof) |
| STWB_compare | 44 | yes | scalar, any u, eta |
| decol_spectral_core | 17 | yes | any Hermitian matrix, any deterministic M |
| ukx | 40 | yes | any Hermitian matrix |
| Gres_apply_self | 43 | yes | any Hermitian matrix |
| calB_antitone | 18 | yes | calB scalar |
| calB_nonneg | 7 | yes | calB scalar |
| inv_size_mul_le_calB | 12 | yes | calB scalar |
| calB_le_two_inv | 29 | yes | calB scalar |
| que_three_terms | 13 | yes | scalar |
| calB_zero_eq_Bctl | 15 | yes | calB scalar |
| calB_blk_eq_STWB | 18 | yes | calB scalar |
| calB_dist_compare | 43 | yes | calB scalar |
| floor_X | 35 | yes | calB scalar and Bandwidth (no msc, no model) |
| prob_union_le | 13 | yes | any law, any index type |
| two_rpow_le | 14 | yes | scalar |
| zdistInf_neg' | 5 | yes | lattice |
| calB_distB_compare | 30 | yes | calB scalar and the block distances (no msc, no model) |
| decol_scalars | 93 | yes | only Sizes, (eq:WO), (Main_DEL_COND): no msc, no model |
| Gres_blockMat' | 12 | yes | any Hermitian/any matrix (blockMat) |
| trace_two | 25 | yes | any matrix |
| trace_four | 50 | yes | any matrix |
| sum_vtx | 4 | yes | any function |
| zRange | 19 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| zGreen | 2 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| zLocal | 13 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| zAve | 14 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| zTrace | 68 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| zProfile | 67 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| btBt | 39 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| im_msc_ge | 25 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| im_identity | 15 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| thetaDiff | 74 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| locSCFixed_of_ML | 119 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| qd_core | 89 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| qd_exp_core | 44 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| QDiffFixed_of_ML | 122 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| fixed_of_ML | 13 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| decol_core | 37 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| decol_of_locSC | 25 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| queDomain | 76 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| etaQ_le | 24 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| STKloop_one | 10 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| locSC_to_UNLocAvgBand | 12 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| QUE_to_UNQueBand | 12 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| band_endpoints_of_pins | 10 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |
| final_shape | 26 | no (band: msc / seqXmat / Theta / lemT / locDomain) | |

carrier-free compiled lines: 675; band-specific compiled lines: 955; (declaration ranges incl. docstrings, excluding the instances section)
```

```
$ python3 price.py
BA rows read from docs/reports/T2161-portmap.md:1048-1052 (lo/central/hi): {'BA-M1': (700, 1000, 1500), 'BA-M2': (700, 1000, 1500), 'BA-M3': (900, 1300, 1900), 'BA-N1': (700, 1200, 2000), 'BA-N2': (500, 800, 1500)}
BA-M1..M3 total lo/central/hi = 2300/3300/4900
carrier-free lines (compiled in the probe, carrier.py): 675  plus RBM2D carrier-free ranges (not compiled here): {'QUE spectral (QUEFromQDiff 44-339)': 296, 'QUE observable (340-402)': 63, 'Markov (798-812)': 15, 'net core (RegionUnif regionUnif_core 54-~200)': 150}
reusable by BA-M1..M3 if stated carrier-free in MA: 1199
saving in lines, after a 25% instantiation overhead on the uncompiled part: 1068 of 3300 central (32%)
in tickets at the BA-M mean central size 1100: 0.97 ticket
BA total (T2173 prove report, top line): 62 (61..66) if UN-25..52 are model-generic; cap 70 (DECISIONS 52, 57). Effect of the saving: 62 -> 61..62 (<= 1 ticket); the cap is not binding with or without it.
cost to MA of stating the QUE core and the net core carrier-free: about 20% of the reusable uncompiled part = 105 lines, inside MA-04, MA-05 (no change of the MA count 6).
```

Reading: the carrier-free part is already carrier-free by construction (statements over any Hermitian matrix, any law, scalar `calB`); the band-specific part is the transfer (`msc`, `seqXmat`, `lemT`), `thetaDiff` (band `Θ`), the domain (`locDomain`).  BA-M1..M3 become instances only if MA's net core and QUE core are stated over a hypothesis bundle; the saving (about 32% of BA-M1..M3 central, under one ticket) leaves the BA total at 61-62 of cap 70 (§52, §57) with or without it.  Recommendation: state in MA the cores that are carrier-free anyway (the compiled list above, the QUE spectral/observable/Markov part, the net union-bound core), keep the transfer, `thetaDiff` and the domain band-specific; no carrier structure.

## P.7 Coverage (script `coverage.py`: the labels of `paper/tex/1_2_Intro_model_result.tex` lines 250-669, comments stripped, and the chain labels; every Lean location verified by grep)

```
$ python3 coverage.py
| # | paper line | label / claim | kind | Lean name | location (verified by grep) |
|---|---|---|---|---|---|
| 1 | 1_2:250 | `sec_model-results` | section | - | - |
| 2 | 1_2:256 | `def:ilambda` | def | Sizes.lam (structure field) | RBM3D/Defs/Sizes.lean:144 |
| 3 | 1_2:266 | `eq:blockIa` | def | Idx, Iblk; Idx | RBM3D/Defs/Sizes.lean:92; RBM3D/Defs/Sizes.lean:46 |
| 4 | 1_2:273 | `representativeL` | def | zdistInf (L^inf periodic distance) | RBM3D/Defs/Sizes.lean:115 |
| 5 | 1_2:291 | `subsec:main` | section | - | - |
| 6 | 1_2:295 | `bandcw0` | def | Sizes.seqXmat; Sizes.seqP | RBM3D/Gauss/FineModel.lean:218; RBM3D/Gauss/FineModel.lean:169 |
| 7 | 1_2:303 | `eq:variancematrix` | def | svarF; SB | RBM3D/Gauss/FineModel.lean:47; RBM3D/Defs/Block.lean:44 |
| 8 | 1_2:335 | `def_Green` | def | Sizes.Gn | RBM3D/Loop/GLoopFlow.lean:165 |
| 9 | 1_2:339 | `eq:defmzsc` | def | msc; msc_eq_integral | RBM3D/Defs/Semicircle.lean:116; RBM3D/Defs/SemicircleIntegral.lean:189 |
| 10 | 1_2:343 | `eq:defMzsc` | def | Mband | RBM3D/Probe/T2192Pins.lean:70 |
| 11 | 1_2:357 | `MR:decol` | thm | decol | RBM3D/Probe/T2192Pins.lean:164 |
| 12 | 1_2:359 | `Main_DEL_COND` | hyp | Sizes.Bandwidth | RBM3D/Defs/Sizes.lean:168 |
| 13 | 1_2:363 | `eq:WO` | hyp | Sizes.WO | RBM3D/Defs/Sizes.lean:164 |
| 14 | 1_2:367 | `eq:psikLinfty` | claim | decolBad, decol | RBM3D/Probe/T2192Pins.lean:106 |
| 15 | 1_2:380 | `eq:spectral_domain` | def | Sizes.locDomain | RBM3D/Defs/Sizes.lean:186 |
| 16 | 1_2:384 | `eq:calBetaK` | def | calB; calB_zero_eq_Bctl | RBM3D/Probe/T2192Pins.lean:57; RBM3D/Probe/T2192Pins.lean:230 |
| 17 | 1_2:386 | `MR:locSC` | thm | locSC | RBM3D/Probe/T2192Pins.lean:171 |
| 18 | 1_2:388 | `G_bound` | claim | locSC (1st conjunct), locBad1 | RBM3D/Probe/T2192Pins.lean:135 |
| 19 | 1_2:391 | `G_bound_ave` | claim | locSC (2nd conjunct), locBad2; locSC_to_UNLocAvgBand | RBM3D/Probe/T2192Pins.lean:139; RBM3D/Probe/T2192Pins.lean:2055 |
| 20 | 1_2:399 | `eq:ukx` | proof step | ukx; decol_spectral_core | RBM3D/Probe/T2192Pins.lean:1652; RBM3D/Probe/T2192Pins.lean:1789 |
| 21 | 1_2:406 | `MR:QUE` | thm | QUE | RBM3D/Probe/T2192Pins.lean:181 |
| 22 | 1_2:408 | `eq:defIE` | def | queWindow (merged UN) | RBM3D/Universality/Pins.lean:380 |
| 23 | 1_2:411 | `Meq:QUE` | claim | QUE (1st conjunct), queBadMat, queBound; QUE_to_UNQueBand | RBM3D/Universality/Pins.lean:392; RBM3D/Probe/T2192Pins.lean:2066 |
| 24 | 1_2:417 | `Meq:QUE2` | claim | QUE (2nd conjunct), que2BadMat; que2BadMat_univ (A = univ) | RBM3D/Probe/T2192Pins.lean:153; RBM3D/Probe/T2192Pins.lean:2397 |
| 25 | 1_2:452 | `Thm: B_Univ` | thm | BUniv := UNBUniv; UNBUniv | RBM3D/Probe/T2192Pins.lean:208; RBM3D/Universality/Pins.lean:177 |
| 26 | 1_2:454 | `eq:universality` | claim | UNBUniv body | RBM3D/Universality/Pins.lean:177 |
| 27 | 1_2:472 | `def:Theta` | def | ThetaPM, ThetaPP, profPM, profPP; Theta | RBM3D/Probe/T2192Pins.lean:79; RBM3D/Propagator/Basic.lean:70 |
| 28 | 1_2:488 | `MR:QuDiff` | thm | QDiff | RBM3D/Probe/T2192Pins.lean:196 |
| 29 | 1_2:494 | `eq:diffu1` | claim | QDiff (1st probability conjunct), qd1Bad | RBM3D/Probe/T2192Pins.lean:143 |
| 30 | 1_2:498 | `eq:diffu2` | claim | QDiff (2nd probability conjunct), qd2Bad | RBM3D/Probe/T2192Pins.lean:147 |
| 31 | 1_2:504 | `Meq:QdS1` | claim | QDiff (expectation half, 1st), qdBoundExp | RBM3D/Probe/T2192Pins.lean:100 |
| 32 | 1_2:507 | `Meq:QdS2` | claim | QDiff (expectation half, 2nd), qdBoundExp | RBM3D/Probe/T2192Pins.lean:100 |
| 33 | 1_2:514 | `eq:BetaK` | proof step | calB_le_two_inv, inv_size_mul_le_calB; etaQ_le | RBM3D/Probe/T2192Pins.lean:1952; RBM3D/Probe/T2192Pins.lean:1994 |
| 34 | 1_2:524 | `ssfa2` | proof step | MAQUE (pin), etaQ, queDomain; queDomain | RBM3D/Probe/T2192Pins.lean:2020; RBM3D/Probe/T2192Pins.lean:1877 |
| 35 | 1_2:531 | `ssfa2_deter` | proof step | que_three_terms, thetaDiff; thetaDiff | RBM3D/Probe/T2192Pins.lean:1982; RBM3D/Probe/T2192Pins.lean:706 |
| 36 | 1_2:600 | `sec:main_BA` | section | - | - |
| 37 | 1_2:605 | `bandcwV` | def (BA) | Sizes.withLam (V is the model of sz.withLam 0) | RBM3D/Defs/Sizes.lean:182 |
| 38 | 1_2:610 | `eq:H_blocka` | def (BA) | Sizes.seqHBA | RBM3D/Gauss/BlockAnderson.lean:96 |
| 39 | 1_2:614 | `eq:Psi3D` | def (BA) | PsiB | RBM3D/Gauss/BlockAnderson.lean:45 |
| 40 | 1_2:626 | `self_m` | def (BA) | BASelf, BAm | RBM3D/BA/MFixedPoint.lean:193 |
| 41 | 1_2:631 | `def_G0` | def (BA) | BAMB (merged), BAMz (t/T2161); BAMz | RBM3D/BA/MFixedPoint.lean:190; t/T2161:RBM3D/Probe/T2161Pins.lean:1479 |
| 42 | 1_2:644 | `MR:decol_BA` | thm (BA) | BAThm27 (t/T2161, T2173a: law seqP (sz.withLam 0)) | t/T2161:RBM3D/Probe/T2161Pins.lean:1659 |
| 43 | 1_2:658 | `def:Theta_BA` | def (BA) | BAprof (t/T2161); BATheta (merged) | t/T2161:RBM3D/Probe/T2161Pins.lean:1494; RBM3D/BA/MFixedPoint.lean:515 |
| 44 | 1_2:651 | Thm 2.7 bullet 1 (decol, 2-kappa -> BAbulk) | claim (BA) | BAEnd_decol | t/T2161:RBM3D/Probe/T2161Pins.lean:1565 |
| 45 | 1_2:653 | Thm 2.7 bullet 2 (locSC: G_bound, G_bound_ave with M of def_G0) | claim (BA) | BAEnd_locSC | t/T2161:RBM3D/Probe/T2161Pins.lean:1543 |
| 46 | 1_2:655 | Thm 2.7 bullet 3a (QUE, Meq:QUE, Meq:QUE2) | claim (BA) | BAEnd_QUE; law-corrected BAEnd_QUEL; BAEnd_QUEL | t/T2161:RBM3D/Probe/T2161Pins.lean:1602; t/T2173:RBM3D/Probe/T2173Pins.lean:3249 |
| 47 | 1_2:655 | Thm 2.7 bullet 3b (bulk universality, DECISIONS 11/51) | claim (BA) | BAEnd_BUniv; law-corrected BAEnd_BUnivL; BAEnd_BUnivL | t/T2161:RBM3D/Probe/T2161Pins.lean:1652; t/T2173:RBM3D/Probe/T2173Pins.lean:3230 |
| 48 | 1_2:657-666 | Thm 2.7 bullet 4 (quantum diffusion with Theta M) | claim (BA) | BAEnd_QDiff | t/T2161:RBM3D/Probe/T2161Pins.lean:1548 |
| 49 | 1_2:619 | Remark (after `eq:Psi3D`) | not a claim | - | - |

labels scanned in 1_2:250-669 (comments stripped): 43; mapped: 43; unmapped (gaps): 0 []; Thm 2.7 bullets: 5; locations not found: 0 []

Chain labels outside 1_2:250-669 (the assembly chain of the ticket), same scan:

| paper line | label | Lean name (role in the chain) | location (verified by grep) |
|---|---|---|---|
| 1_2:787 | `zztE` | zRange (flow data); zGreen = Gt_lemT; zt_im_lemma28 | RBM3D/Probe/T2192Pins.lean:497; RBM3D/Loop/GLoopFlow.lean:181; RBM3D/Defs/Semicircle.lean:344 |
| 1_2:789 | `eq:t0E0` | zRange: 1 - t0 = Im z/(Im m + Im z); im_identity; lemma28_quant | RBM3D/Probe/T2192Pins.lean:497; RBM3D/Probe/T2192Pins.lean:476; RBM3D/Defs/Semicircle.lean:359 |
| 1_2:791 | `eq:zztE` | zGreen; zLocal; msc_eq_sqrt_mul_mE | RBM3D/Probe/T2192Pins.lean:523; RBM3D/Probe/T2192Pins.lean:532; RBM3D/Defs/Semicircle.lean:264 |
| 1_2:1105 | `defi:ofB` | Bparam, Bctl | RBM3D/Defs/Params.lean:36 |
| 1_2:1107 | `eq_B_param` | Bparam; STWB | RBM3D/Defs/Params.lean:36; RBM3D/Induction/Defs.lean:69 |
| 1_2:1111 | `eq:BtBt` | btBt; STWB_compare; calB_blk_eq_STWB | RBM3D/Probe/T2192Pins.lean:632; RBM3D/Probe/T2192Pins.lean:592; RBM3D/Probe/T2192Pins.lean:245 |
| 1_2:1175 | `Kn2sol` | zProfile; KLK_two | RBM3D/Probe/T2192Pins.lean:1000; RBM3D/Loop/KLTree.lean:211 |
| 1_2:1193 | `ML:GLoop` | UNMLOut (STLK, STLmax); used: locSCFixed_of_ML; locSCFixed_of_ML | RBM3D/Universality/Pins.lean:432; RBM3D/Probe/T2192Pins.lean:1156 |
| 1_2:1195 | `Eq:L-KGt` | STLK | RBM3D/Induction/Defs.lean:104 |
| 1_2:1197 | `Eq:L-KGt2` | STLmax | RBM3D/Induction/Defs.lean:112 |
| 1_2:1203 | `ML:GLoop_expec` | UNMLOut (STDecay, STExp2); used: QDiffFixed_of_ML; QDiffFixed_of_ML | RBM3D/Universality/Pins.lean:432; RBM3D/Probe/T2192Pins.lean:1475 |
| 1_2:1205 | `Eq:Gdecay` | STDecay | RBM3D/Induction/Defs.lean:121 |
| 1_2:1210 | `Eq:Gtlp_exp` | STExp2 | RBM3D/Induction/Defs.lean:159 |
| 1_2:1217 | `ML:GtLocal` | UNMLOut (STLocalEntry); used: locSCFixed_of_ML | RBM3D/Universality/Pins.lean:432 |
| 1_2:1220 | `Gt_bound` | STLocalEntry | RBM3D/Induction/Defs.lean:151 |
| 1_2:1228 | `[net] (sentence, no label)` | MANetLoc, MANetQD (pins); MANetQD | RBM3D/Probe/T2192Pins.lean:2043; RBM3D/Probe/T2192Pins.lean:2046 |

chain labels listed: 16; locations not found: 0
```

## P.8 The preflight exponent table against the signatures (script `exptab.py`)

```
$ python3 exptab.py
| preflight row | quantities / constraint | Lean location (compiled where named) | declaration at | substring check |
|---|---|---|---|---|
| 1 | (c, d) = (𝔠, 𝔡), lam; W >= N^c, (eq:WO), N -> infinity | Admissible 𝔠 𝔡 in every endpoint pin | probe:164 `decol` | all 1 found |
| 1 | ... edges lam = W^{-d/2+𝔡}, lam = 𝔡⁻¹ | szLo_admissible, szUp_admissible (compiled) | probe:2328 `szUp_admissible` | all 1 found |
| 2 | Prec at N^τ vs W^τ: τ' = 𝔠 τ, τ = d τ' | explicit_of_stochDomAt (𝔠), prec_of_explicit (d) | probe:375 `explicit_of_stochDomAt` | all 2 found |
| 2 | ... (other direction) | prec_of_explicit | probe:400 `prec_of_explicit` | all 1 found |
| 3 | (eq:BtBt): constants 2 and sqrt(κ(4-κ))/8; t0 = lemT z, η = Im z | MABtBt | probe:582 `MABtBt` | all 2 found |
| 3 | ... scalar core: eta <= 2u, u <= C eta | STWB_compare | probe:592 `STWB_compare` | all 2 found |
| 4 | zdistInf vs zdistD (T2001e): factor d^{d-2} | calB_dist_compare, calB_distB_compare (compiled): d^{-(d-2)} B_K <= B_K' <= B_K | probe:344 `calB_distB_compare` | all 2 found |
| 5 | additive W^{-D} of (Eq:Gdecay): D = 6/(5𝔠) suffices (a: D0 = 2/𝔠) | floor_X, QDiffFixed_of_ML (compiled; D free in STDecay) | probe:1278 `floor_X` | all 1 found |
| 6 | z-net: mesh N^-7, |net| <= 25 N^14, error <= N^-2/2 | pins MANetLoc, MANetQD; floor inv_size_mul_le_calB | probe:263 `inv_size_mul_le_calB` | all 1 found |
| 7 | (eq:ukx): ε = min(τ/2, 1/2), τ_L = min(𝔡, dε/2) | decol_scalars (ε, τ_L explicit) | probe:1695 `decol_scalars` | all 1 found |
| 8 | η_Q = W^{-ε0} lam W^{d/2}/N in D_{κ,ε_Q}, ε_Q = 𝔠(𝔡 - ε0) | queDomain | probe:1877 `queDomain` | all 2 found |
| 9 | (eq:BetaK): η_Q <= lam^2/L^d, B <= 2 (Nη)^-1 | etaQ_le, calB_le_two_inv | probe:1994 `etaQ_le` | all 1 found |
| 10 | (ssfa2_deter): ε0 <= 3𝔡/5, three terms | que_three_terms | probe:1982 `que_three_terms` | all 2 found |
| 11 | Markov: bound W^{-(2ε0)∧(2𝔡/5)+2c+τ} | QUE (queBound W 𝔡 ε₀ c τ) | probe:181 `QUE` | all 2 found |
| 12 | Theta differences <= C lam^-2, g <= 𝔡⁻¹, κ' = sqrt(κ(4-κ))/2 | MAThetaDiff | probe:677 `MAThetaDiff` | all 2 found |

rows checked: 15  failures: 0
```

## P.9 Hygiene and names

```
$ python3 axioms.py
declarations printed: 146  lines of axiom output: 146
146 [propext, Classical.choice, Quot.sound]
other output lines: 0
```

```
$ python3 clash.py
new public names in the probe: 146
CLASH zI
    RBM3D/Green/FlucVanish.lean:1355:private noncomputable def zI : ℂ := (1 / 2 : ℂ) + Complex.I / 2
CLASH zdistInf_zero
    RBM3D/Green/Pins.lean:1303:private theorem zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
names with a match outside Probe/: 2
namespace RBM.Endpoints outside Probe/: 0
6:import RBM3D
36:set_option linter.style.longLine false
37:set_option linter.unusedSectionVars false
38:set_option linter.unusedVariables false
42:open MeasureTheory ProbabilityTheory Filter Matrix Topology
43:open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
44:open scoped NNReal ENNReal
46:namespace RBM.Probe.T2192
669:open scoped Matrix.Norms.Operator
988:open scoped Matrix.Norms.Operator in
998:open scoped Matrix.Norms.Operator in
999:open RBM.Loop in
1141:open RBM.Loop in
1151:open RBM.Loop in
1470:open RBM.Loop in
2112:namespace Inst
2114:open RBM.Gauss.SizesInst RBM.Univ.UNInst
2492:end RBM.Probe.T2192

sorry/admit/native_decide/axiom lines in the probe: 0
```

```
$ python3 names.py   # Mathlib/core names typed in the probe, resolved by Lean (`names_mathlib.txt`, one line each)
candidate tokens: 395; constants resolved: 229; from Mathlib/core: 227; from RBM3D (merged): 2
error lines: 0
```

```
Bool.false_eq_true [Init.Data.Bool] : (false = true) = False
Bool.not_false [Init.SimpLemmas] : (!false) = true
Bool.not_true [Init.SimpLemmas] : (!true) = false
Classical.arbitrary [Mathlib.Basic.Nonempty] : (α : Sort u_3) → [h : Nonempty α] → α
Complex.I [Mathlib.Basic.Complex.Basic] : ℂ
Complex.I_im [Mathlib.Basic.Complex.Basic] : Complex.I.im = 1
Complex.I_re [Mathlib.Basic.Complex.Basic] : Complex.I.re = 0
Complex.add_im [Mathlib.Basic.Complex.Basic] : ∀ (z w : ℂ), (z + w).im = z.im + w.im
Complex.conj_conj [Mathlib.Algebra.Star.Basic] : ∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
Complex.conj_mul' [Mathlib.Analysis.Complex.Basic] : ∀ (z : ℂ), (starRingEnd ℂ) z * z = ↑‖z‖ ^ 2
Complex.conj_ofReal [Mathlib.Basic.Complex.Basic] : ∀ (r : ℝ), (starRingEnd ℂ) ↑r = ↑r
Complex.im [Mathlib.Basic.Complex.Basic] : ℂ → ℝ
Complex.im_le_norm [Mathlib.Analysis.Complex.Norm] : ∀ (z : ℂ), z.im ≤ ‖z‖
Complex.im_ofReal_mul [Mathlib.Basic.Complex.Basic] : ∀ (r : ℝ) (z : ℂ), (↑r * z).im = r * z.im
Complex.im_sum [Mathlib.Basic.Complex.BigOperators] : ∀ {α : Type u_1} (s : Finset α) (f : α → ℂ), (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im
Complex.inv_im [Mathlib.Basic.Complex.Basic] : ∀ (z : ℂ), z⁻¹.im = -z.im / Complex.normSq z
Complex.mul_conj [Mathlib.Basic.Complex.Basic] : ∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑(Complex.normSq z)
Complex.mul_im [Mathlib.Basic.Complex.Basic] : ∀ (z w : ℂ), (z * w).im = z.re * w.im + z.im * w.re
Complex.neg_im [Mathlib.Basic.Complex.Basic] : ∀ (z : ℂ), (-z).im = -z.im
Complex.normSq [Mathlib.Basic.Complex.Basic] : ℂ →*₀ ℝ
Complex.normSq_apply [Mathlib.Basic.Complex.Basic] : ∀ (z : ℂ), Complex.normSq z = z.re * z.re + z.im * z.im
Complex.normSq_eq_conj_mul_self [Mathlib.Basic.Complex.Basic] : ∀ {z : ℂ}, ↑(Complex.normSq z) = (starRingEnd ℂ) z * z
Complex.normSq_eq_norm_sq [Mathlib.Analysis.Complex.Norm] : ∀ (z : ℂ), Complex.normSq z = ‖z‖ ^ 2
Complex.normSq_nonneg [Mathlib.Basic.Complex.Basic] : ∀ (z : ℂ), 0 ≤ Complex.normSq z
Complex.normSq_pos [Mathlib.Basic.Complex.Basic] : ∀ {z : ℂ}, 0 < Complex.normSq z ↔ z ≠ 0
Complex.norm_real [Mathlib.Analysis.Complex.Norm] : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
Complex.ofReal_im [Mathlib.Basic.Complex.Basic] : ∀ (r : ℝ), (↑r).im = 0
Complex.ofReal_mul [Mathlib.Basic.Complex.Basic] : ∀ (r s : ℝ), ↑(r * s) = ↑r * ↑s
Complex.ofReal_ne_zero [Mathlib.Basic.Complex.Basic] : ∀ {z : ℝ}, ↑z ≠ 0 ↔ z ≠ 0
Complex.ofReal_re [Mathlib.Basic.Complex.Basic] : ∀ (r : ℝ), (↑r).re = r
Complex.star_def [Mathlib.Basic.Complex.Basic] : star = ⇑(starRingEnd ℂ)
Complex.sub_im [Mathlib.Basic.Complex.Basic] : ∀ (z w : ℂ), (z - w).im = z.im - w.im
ENNReal.ofReal [Mathlib.Basic.ENNReal.Basic] : ℝ → ENNReal
ENNReal.ofReal_add [Mathlib.Basic.ENNReal.Real] : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
ENNReal.ofReal_le_ofReal [Mathlib.Basic.ENNReal.Real] : ∀ {p q : ℝ}, p ≤ q → ENNReal.ofReal p ≤ ENNReal.ofReal q
ENNReal.ofReal_lt_one [Mathlib.Basic.ENNReal.Real] : ∀ {p : ℝ}, ENNReal.ofReal p < 1 ↔ p < 1
Equiv.sum_comp [Mathlib.Algebra.BigOperators.Group.Finset.Defs] : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ → M), ∑ i, g (e...
Equiv.symm_apply_apply [Mathlib.Logic.Equiv.Defs] : ∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α), e.symm (e x) = x
Filter.Eventually.of_forall [Mathlib.Order.Filter.Basic] : ∀ {α : Type u} {p : α → Prop} {f : Filter α}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
Filter.Eventually.of_forall [Mathlib.Order.Filter.Basic] : ∀ {α : Type u} {p : α → Prop} {f : Filter α}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
Filter.not_eventually [Mathlib.Order.Filter.Basic] : ∀ {α : Type u} {p : α → Prop} {f : Filter α}, (¬∀ᶠ (x : α) in f, p x) ↔ ∃ᶠ (x : α) in f, ¬p x
Fin.succ [Init.Data.Fin.Basic] : {n : ℕ} → Fin n → Fin (n + 1)
Finset.card_univ [Mathlib.Data.Fintype.Card] : ∀ {α : Type u_1} [inst : Fintype α], Finset.univ.card = Fintype.card α
Finset.mem_univ [Mathlib.Data.Fintype.Defs] : ∀ {α : Type u_1} [inst : Fintype α] (x : α), x ∈ Finset.univ
Finset.mul_sum [Mathlib.Algebra.BigOperators.Ring.Finset] : ∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R),   a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
Finset.single_le_sum [Mathlib.Algebra.Order.BigOperators.Group.Finset] : ∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s, 0 ≤ f i) → ∀ {a...
Finset.sum_comm [Mathlib.Algebra.BigOperators.Group.Finset.Sigma] : ∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y...
Finset.sum_congr [Mathlib.Algebra.BigOperators.Group.Finset.Basic] : ∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [inst : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g
Finset.sum_filter [Mathlib.Algebra.BigOperators.Group.Finset.Basic] : ∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst : AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a ∈ s with p a, f a...
Finset.sum_mul [Mathlib.Algebra.BigOperators.Ring.Finset] : ∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R),   (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
Finset.sup_congr [Mathlib.Data.Finset.Lattice.Fold] : ∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s₁ s₂ : Finset β} {f g : β → α},   s₁ = s₂ → (∀ a ∈ s₂, f a = g a) → ...
Finset.univ [Mathlib.Data.Fintype.Defs] : {α : Type u_1} → [Fintype α] → Finset α
List.ofFn_succ [Init.Data.List.OfFn] : ∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofFn f = f 0 :: List.ofFn fun i => f i.succ
List.ofFn_zero [Init.Data.List.OfFn] : ∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
List.prod_cons [Init.Data.List.Basic] : ∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {l : List α}, (a :: l).prod = a * l.prod
List.prod_nil [Init.Data.List.Basic] : ∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod = 1
Matrix.conjTranspose_apply [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Star α] (M : Matrix m n α) (i : m) (j : n),   M.conjTranspose j i = star (M i j)
Matrix.conjTranspose_nonsing_inv [Mathlib.LinearAlgebra.Matrix.NonsingularInverse] : ∀ {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α)   [inst_3 : StarRing α], A⁻¹.conjTra...
Matrix.conjTranspose_one [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : NonAssocSemiring α] [inst_2 : StarRing α],   Matrix.conjTranspose 1 = 1
Matrix.conjTranspose_smul [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {m : Type u_2} {n : Type u_3} {R : Type u_5} {α : Type v} [inst : Star R] [inst_1 : Star α] [inst_2 : SMul R α]   [StarModule R α] (c : R) (M : Matr...
Matrix.conjTranspose_sub [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : AddGroup α] [inst_1 : StarAddMonoid α] (M N : Matrix m n α),   (M - N).conjTranspose = M.conjTran...
Matrix.inv_eq_right_inv [Mathlib.LinearAlgebra.Matrix.NonsingularInverse] : ∀ {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] {A B : Matrix n n α},   A * B = 1 → A⁻¹ = B
Matrix.inv_submatrix_equiv [Mathlib.LinearAlgebra.Matrix.NonsingularInverse] : ∀ {m : Type u} {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α]   [inst_3 : Fintype m] [inst_4 : Decidable...
Matrix.mul_apply [Mathlib.Data.Matrix.Mul] : ∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Fintype m] [inst_1 : Mul α]   [inst_2 : AddCommMonoid α] {M : Matrix l m α} {N : M...
Matrix.mul_assoc [Mathlib.Data.Matrix.Mul] : ∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2 : Fintype n] (L...
Matrix.mul_diagonal [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   [inst_2 : DecidableEq n] (d : n → α) (M : Mat...
Matrix.mul_one [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonAssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n α), M * 1 = M
Matrix.mul_smul [Mathlib.Data.Matrix.Mul] : ∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Type u_5} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintype n] [inst_3 : ...
Matrix.mul_sub [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (N N' : Matrix ...
Matrix.nonsing_inv_eq_ringInverse [Mathlib.LinearAlgebra.Matrix.NonsingularInverse] : ∀ {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α),   A⁻¹ = Ring.inverse A
Matrix.of [Mathlib.LinearAlgebra.Matrix.Defs] : {m : Type u_2} → {n : Type u_3} → {α : Type v} → (m → n → α) ≃ Matrix m n α
Matrix.of_apply [Mathlib.LinearAlgebra.Matrix.Defs] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} (f : m → n → α) (i : m) (j : n), Matrix.of f i j = f i j
Matrix.one_apply [Mathlib.Data.Matrix.Diagonal] : ∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] {i j : n},   1 i j = if i = j then 1 else 0
Matrix.one_mul [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonAssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n α), 1 * M = M
Matrix.smul_apply [Mathlib.LinearAlgebra.Matrix.Defs] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [inst : SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n),   (r • A) i j = r • A i j
Matrix.smul_mul [Mathlib.Data.Matrix.Mul] : ∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Type u_5} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintype n] [inst_3 : ...
Matrix.star_apply [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {n : Type u_3} {α : Type v} [inst : Star α] (M : Matrix n n α) (i j : n), star M i j = star (M j i)
Matrix.sub_mul [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M M' : Matrix m n α) (N : Matrix ...
Matrix.submatrix_smul [Mathlib.LinearAlgebra.Matrix.Defs] : ∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} {R : Type u_8} [inst : SMul R α] (r : R)   (A : Matrix m n α), (r • A).subm...
Matrix.submatrix_sub [Mathlib.LinearAlgebra.Matrix.Defs] : ∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : Sub α] (A B : Matrix m n α),   (A - B).submatrix = A.submatrix - B....
Matrix.trace [Mathlib.LinearAlgebra.Matrix.Trace] : {n : Type u_3} → {R : Type u_6} → [Fintype n] → [AddCommMonoid R] → Matrix n n R → R
Nat.cast_nonneg [Mathlib.Data.Nat.Cast.Order.Ring] : ∀ {α : Type u_3} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] (n : ℕ), 0 ≤ ↑n
Nat.cast_zero [Mathlib.Data.Nat.Cast.Defs] : ∀ {R : Type u_1} [inst : AddMonoidWithOne R], ↑0 = 0
Nat.le_mul_of_pos_left [Init.Data.Nat.Lemmas] : ∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
Nat.le_mul_of_pos_right [Init.Data.Nat.Lemmas] : ∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
Nat.le_self_pow [Init.Data.Nat.Lemmas] : ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
Nat.mul_le_mul_left [Init.Data.Nat.Basic] : ∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
Nat.pos_of_ne_zero [Init.Data.Nat.Basic] : ∀ {n : ℕ}, n ≠ 0 → 0 < n
Nat.pow_le_pow_left [Init.Data.Nat.Basic] : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
NeZero.ne [Init.Data.NeZero] : ∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 0
Pi.single [Mathlib.Algebra.Notation.Pi.Basic] : {ι : Type u_1} → {M : ι → Type u_4} → [(i : ι) → Zero (M i)] → [DecidableEq ι] → (i : ι) → M i → (j : ι) → M j
Pi.smul_apply [Mathlib.Algebra.Notation.Pi.Defs] : ∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst : (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a • f i
Pi.star_apply [Mathlib.Algebra.Notation.Pi.Defs] : ∀ {ι : Type u_1} {R : ι → Type u_6} [inst : (i : ι) → Star (R i)] (x : (i : ι) → R i) (i : ι), star x i = star (x i)
RCLike.star_def [Mathlib.Analysis.RCLike.Basic] : ∀ {K : Type u_1} [inst : RCLike K], star = ⇑(starRingEnd K)
Real.exp [Mathlib.Analysis.Complex.Exponential] : ℝ → ℝ
Real.exp_le_one_iff [Mathlib.Analysis.Complex.Exponential] : ∀ {x : ℝ}, Real.exp x ≤ 1 ↔ x ≤ 0
Real.exp_nonneg [Mathlib.Analysis.Complex.Exponential] : ∀ (x : ℝ), 0 ≤ Real.exp x
Real.mul_rpow [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → (x * y) ^ z = x ^ z * y ^ z
Real.mul_self_sqrt [Mathlib.Analysis.Real.Sqrt] : ∀ {x : ℝ}, 0 ≤ x → √x * √x = x
Real.norm_eq_abs [Mathlib.Analysis.Normed.Group.Real] : ∀ (r : ℝ), ‖r‖ = |r|
Real.one_lt_rpow [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x z : ℝ}, 1 < x → 0 < z → 1 < x ^ z
Real.pow_rpow_inv_natCast [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
Real.rpow_add [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_le_one_of_one_le_of_nonpos [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.rpow_le_rpow [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
Real.rpow_le_rpow_of_exponent_le [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.rpow_le_rpow_of_nonpos [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_mul [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_natCast [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_neg [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ (x : ℝ), x ^ (-1) = x⁻¹
Real.rpow_nonneg [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Real.rpow_one [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ (x : ℝ), x ^ 1 = x
Real.rpow_pos_of_pos [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
Real.rpow_sub [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y - z) = x ^ y / x ^ z
Real.sq_sqrt [Mathlib.Analysis.Real.Sqrt] : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
Real.sqrt [Mathlib.Analysis.Real.Sqrt] : ℝ → ℝ
Real.sqrt_le_one [Mathlib.Analysis.Real.Sqrt] : ∀ {x : ℝ}, √x ≤ 1 ↔ x ≤ 1
Real.sqrt_le_sqrt [Mathlib.Analysis.Real.Sqrt] : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
Real.sqrt_nonneg [Mathlib.Analysis.Real.Sqrt] : ∀ (x : ℝ), 0 ≤ √x
Real.sqrt_pos [Mathlib.Analysis.Real.Sqrt] : ∀ {x : ℝ}, 0 < √x ↔ 0 < x
Real.sqrt_sq [Mathlib.Analysis.Real.Sqrt] : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
Set.mem_ofPred_eq [Mathlib.Data.Set.Operations] : ∀ {α : Type u} {x : α} {p : α → Prop}, (x ∈ {y | p y}) = p x
Set.mem_union [Mathlib.Data.Set.Basic] : ∀ {α : Type u} (x : α) (a b : Set α), x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
Set.mem_univ [Mathlib.Data.Set.Operations] : ∀ {α : Type u} (x : α), x ∈ Set.univ
Set.univ [Mathlib.Data.Set.Defs] : {α : Type u} → Set α
abs_le [Mathlib.Algebra.Order.Group.Abs] : ∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
abs_neg [Mathlib.Algebra.Order.Group.Unbundled.Abs] : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : α), |(-a)| = |a|
abs_nonneg [Mathlib.Algebra.Order.Group.Unbundled.Abs] : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
abs_of_nonneg [Mathlib.Algebra.Order.Group.Unbundled.Abs] : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
abs_of_pos [Mathlib.Algebra.Order.Group.Unbundled.Abs] : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a : α} [AddLeftMono α], 0 < a → |a| = a
abs_zero [Mathlib.Algebra.Order.Group.Unbundled.Abs] : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddLeftMono α], |0| = 0
add_le_add [Mathlib.Algebra.Order.Monoid.Unbundled.Basic] : ∀ {α : Type u_1} {a b c d : α} [inst : Add α] [inst_1 : Preorder α] [AddLeftMono α] [AddRightMono α],   a ≤ b → c ≤ d → a + c ≤ b + d
add_nonneg [Mathlib.Algebra.Order.Monoid.Unbundled.Basic] : ∀ {α : Type u_1} {a b : α} [inst : AddZeroClass α] [inst_1 : Preorder α] [AddLeftMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a + b
add_zero [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : AddZeroClass M] (a : M), a + 0 = a
by_cases [Mathlib.Basic.Logic.Basic] : ∀ {p q : Prop}, (p → q) → (¬p → q) → q
by_contra [Mathlib.Basic.Logic.Basic] : ∀ {p : Prop}, (¬p → False) → p
Matrix.diagonal_mul_diagonal [Mathlib.Data.Matrix.Mul] : ∀ {n : Type u_3} {α : Type v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (d₁ d₂ : n → α), Matrix.diagonal d₁...
Matrix.diagonal_one [Mathlib.Data.Matrix.Diagonal] : ∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α],   (Matrix.diagonal fun x => 1) = 1
Matrix.diagonal_sub [Mathlib.Data.Matrix.Diagonal] : ∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : SubNegZeroMonoid α] (d₁ d₂ : n → α),   Matrix.diagonal d₁ - Matrix.diagonal d₂ = Matrix...
dite_true [Init.SimpLemmas] : ∀ {α : Sort u} {x : Decidable True} {t : True → α} {e : ¬True → α}, dite True t e = t True.intro
div_eq_mul_inv [Mathlib.Algebra.Group.DivInvMonoid] : ∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b = a * b⁻¹
div_le_div_iff_of_pos_right [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀},   0 < c → (a / c ≤ b / c ↔ a ≤ b)
div_le_div_iff₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : CommGroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀},   0 < b → 0 < d → (a / b ≤ c / d ↔ a *...
div_le_div_of_nonneg_left [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀]   {a b c : G₀}, 0 ≤ a → 0 < c → c ≤ b...
div_le_div_of_nonneg_right [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀},   a ≤ b → 0 ≤ c → a / c ≤ b / c
div_le_iff₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀},   0 < c → (b / c ≤ a ↔ b ≤ a * c)
div_nonneg [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a b : G₀},   0 ≤ a → 0 ≤ b → 0 ≤ a / b
eq_div_iff [Mathlib.Algebra.GroupWithZero.Units.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a b c : G₀}, b ≠ 0 → (c = a / b ↔ c * b = a)
Filter.eventually_ge_atTop [Mathlib.Order.Filter.AtTopBot.Defs] : ∀ {α : Type u_2} [inst : Preorder α] (a : α), ∀ᶠ (x : α) in Filter.atTop, a ≤ x
iff_true [Init.SimpLemmas] : ∀ (p : Prop), (p ↔ True) = p
MeasureTheory.integral_congr_ae [Mathlib.MeasureTheory.Integral.Bochner.Basic] : ∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {f g ...
MeasureTheory.integral_const_mul [Mathlib.MeasureTheory.Integral.Bochner.Basic] : ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {L : Type u_6} [inst : RCLike L] (r : L)   (f : α → L), ∫ (a : α), r * f a ∂μ =...
inv_anti₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀]   {a b : G₀}, 0 < b → b ≤ a → a⁻¹ ≤ b...
inv_le_one_of_one_le₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 1 ≤ a → a⁻¹ ≤ 1
inv_lt_one_of_one_lt₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 1 < a → a⁻¹ < 1
inv_mul_le_iff₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀},   0 < c → (c⁻¹ * b ≤ a ↔ b ≤ c * a)
inv_one [Mathlib.Algebra.Group.DivInvMonoid] : ∀ {G : Type u_1} [inst : InvOneClass G], 1⁻¹ = 1
inv_pos [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
ite_false [Init.SimpLemmas] : ∀ {α : Sort u_1} {x : Decidable False} (a b : α), (if False then a else b) = b
ite_true [Init.SimpLemmas] : ∀ {α : Sort u_1} {x : Decidable True} (a b : α), (if True then a else b) = a
le_div_iff₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀},   0 < c → (a ≤ b / c ↔ a * c ≤ b)
le_min [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, c ≤ a → c ≤ b → c ≤ min a b
le_of_eq [Mathlib.Order.Defs.PartialOrder] : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
le_refl [Mathlib.Order.Defs.PartialOrder] : ∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
le_rfl [Mathlib.Order.Defs.PartialOrder] : ∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ≤ a
le_total [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤ a
le_trans [Mathlib.Order.Defs.PartialOrder] : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c
lt_min [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a < b → a < c → a < min b c
lt_of_le_of_lt [Mathlib.Order.Defs.PartialOrder] : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b < c → a < c
lt_of_lt_of_le [Mathlib.Order.Defs.PartialOrder] : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b ≤ c → a < c
map_inv₀ [Mathlib.Algebra.GroupWithZero.Units.Lemmas] : ∀ {G₀ : Type u_3} {G₀' : Type u_5} {F : Type u_6} [inst : GroupWithZero G₀] [inst_1 : GroupWithZero G₀']   [inst_2 : FunLike F G₀ G₀'] [MonoidWithZero...
MeasureTheory.measure_mono [Mathlib.MeasureTheory.OuterMeasure.Basic] : ∀ {α : Type u_1} {F : Type u_3} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   {s t : Set α}, s ⊆ t → μ s ≤ μ t
MeasureTheory.measure_union_le [Mathlib.MeasureTheory.OuterMeasure.Basic] : ∀ {α : Type u_1} {F : Type u_3} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   (s t : Set α), μ (s ∪ t) ≤ μ s + μ ...
min_eq_left [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → min a b = a
min_eq_right [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → min a b = b
min_le_left [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), min a b ≤ a
min_le_right [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), min a b ≤ b
mul_add [Mathlib.Algebra.Ring.Defs] : ∀ {R : Type v} [inst : Mul R] [inst_1 : Add R] [LeftDistribClass R] (a b c : R), a * (b + c) = a * b + a * c
mul_apply [Mathlib.Data.FunLike.IsApply] : ∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Type u_3)} {inst : FunLike F α β} {inst_1 : Mul β}   {inst_2 : Mul F} [self : IsMulApply F α...
mul_assoc [Mathlib.Algebra.Group.Semigroup] : ∀ {G : Type u_1} [inst : Semigroup G] (a b c : G), a * b * c = a * (b * c)
mul_comm [Mathlib.Algebra.Group.Semigroup] : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a
Matrix.mul_diagonal [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   [inst_2 : DecidableEq n] (d : n → α) (M : Mat...
mul_inv [Mathlib.Algebra.Group.Basic] : ∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α), (a * b)⁻¹ = a⁻¹ * b⁻¹
mul_inv_cancel₀ [Mathlib.Algebra.GroupWithZero.Defs] : ∀ {G₀ : Type u} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a * a⁻¹ = 1
mul_le_mul [Mathlib.Algebra.Order.GroupWithZero.Defs] : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b →...
mul_le_mul_of_nonneg_left [Mathlib.Algebra.Order.GroupWithZero.Defs] : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α],   b ≤ c → 0 ≤ a → a * b ≤ a * c
mul_le_mul_of_nonneg_right [Mathlib.Algebra.Order.GroupWithZero.Defs] : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α],   b ≤ c → 0 ≤ a → b * a ≤ c * a
mul_le_of_le_one_left [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b : α} [inst_2 : Preorder α] [MulPosMono α],   0 ≤ b → a ≤ 1 → a * b ≤ b
mul_nonneg [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
mul_one [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : MulOneClass M] (a : M), a * 1 = a
mul_pos [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
mul_pow [Mathlib.Algebra.Group.Basic] : ∀ {M : Type u_4} [inst : CommMonoid M] (a b : M) (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
mul_sub [Mathlib.Algebra.Ring.Defs] : ∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a * (b - c) = a * b - a * c
Matrix.mul_zero [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n α), M * 0 = 0
neg_add [Mathlib.Algebra.Group.Basic] : ∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -(a + b) = -a + -b
neg_nonpos [Mathlib.Algebra.Order.Group.Unbundled.Basic] : ∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
neg_sub [Mathlib.Algebra.Group.Basic] : ∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - b) = b - a
norm_mul [Mathlib.Analysis.Normed.Ring.Basic] : ∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
norm_nonneg [Mathlib.Analysis.Normed.Group.Basic] : ∀ {E : Type u_4} [inst : SeminormedAddGroup E] (a : E), 0 ≤ ‖a‖
norm_num [Mathlib.Tactic.NormNum.Core] : ParserDescr
norm_pow [Mathlib.Analysis.Normed.Ring.Basic] : ∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneClass α] [NormMulClass α] (a : α) (n : ℕ), ‖a ^ n‖ = ‖a‖ ^ n
norm_sub_le [Mathlib.Analysis.Normed.Group.Basic] : ∀ {E : Type u_4} [inst : SeminormedAddGroup E] (a b : E), ‖a - b‖ ≤ ‖a‖ + ‖b‖
not_exists [Init.PropLemmas] : ∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
not_lt [Mathlib.Order.Defs.LinearOrder] : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ a
not_or [Init.PropLemmas] : ∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
one_div [Mathlib.Algebra.Group.DivInvMonoid] : ∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), 1 / a = a⁻¹
one_le_pow₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 ≤ a → ∀ {n : ℕ}, 1 ≤ a ^ n
one_pos [Mathlib.Algebra.Order.ZeroLEOne] : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
one_pow [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : Monoid M] (n : ℕ), 1 ^ n = 1
pow_add [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
pow_le_pow_left₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b...
pow_nonneg [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a ^ n
pow_one [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 1 = a
pow_two [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
smul_eq_mul [Mathlib.Algebra.Group.Action.Defs] : ∀ {α : Type u_9} [inst : Mul α] (a b : α), a • b = a * b
Matrix.smul_one_eq_diagonal [Mathlib.Data.Matrix.Mul] : ∀ {m : Type u_2} {α : Type v} [inst : NonAssocSemiring α] [inst_1 : DecidableEq m] (a : α),   a • 1 = Matrix.diagonal fun x => a
sq_nonneg [Mathlib.Algebra.Order.Ring.Unbundled.Basic] : ∀ {R : Type u} [inst : Semiring R] [inst_1 : LinearOrder R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a : R),   0 ≤ a ^ 2
Matrix.star_apply [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {n : Type u_3} {α : Type v} [inst : Star α] (M : Matrix n n α) (i j : n), star M i j = star (M j i)
Matrix.star_mul [Mathlib.LinearAlgebra.Matrix.ConjTranspose] : ∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s : R), star (r * s) = star s * star r
sub_self [Mathlib.Algebra.Group.Defs] : ∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
sub_sub_cancel [Mathlib.Algebra.Group.Basic] : ∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a - b) = b
Filter.tendsto_atTop_mono [Mathlib.Order.Filter.AtTopBot.Tendsto] : ∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] {l : Filter α} {f g : α → β},   (∀ (n : α), f n ≤ g n) → Filter.Tendsto f l Filter.atTop → Filter....
tendsto_natCast_atTop_atTop [Mathlib.Order.Filter.AtTopBot.Archimedean] : ∀ {R : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [Archimedean R],   Filter.Tendsto Nat.cast Filter.atTop Filter.atTop
tendsto_rpow_atTop [Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics] : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
zero_add [Mathlib.Algebra.Group.Monoid] : ∀ {M : Type u_2} [inst : AddZeroClass M] (a : M), 0 + a = a
zero_le_one [Mathlib.Algebra.Order.ZeroLEOne] : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : LE α] [ZeroLEOneClass α], 0 ≤ 1
```

```
$ python3 absent.py   # names verified absent or deprecated (Lean `#check` of each)
absent (Lean `#check`: unknown constant): Matrix.trace_submatrix_equiv, Matrix.trace_reindex, Matrix.cons_val_succ?
deprecated in this Mathlib/core (Lean warning): Set.mem_setOf_eq (use Set.mem_ofPred_eq), if_true (use ite_true)
```
