Prover model: claude-sonnet-5-5

# T2498c prove report: row c (U3s3c), new `Chain/QEndB1Gen` (targets 11-13)
Branch `t/T2498c` (stacked on `t/T2498b`, `main` merged at `2c0bc232`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498c`), ticket `docs/tickets/T2498.md` with Amend 1. First `date -u` of this stage: Wed Oct 14 07:54:49 UTC 2026. Commits (`TZ=UTC git log`): `55a6a800` 08:08:21 (checkpoint: texts, helpers, initial loops, core, section), `7bfe5a58` 08:23:08 (endpoint theorem, band re-derivation, instances, `RBM3D.lean` import), `04fe369f` 08:27:31 (comments of the target 12 signature). Rows a, a′, b are merged on `main`; `RBM3D/Probe/T2498Pins.lean` stays on the stack base.

## (a) Math preflight
Not rewritten: `docs/reports/T2498-prove.md` (a), (a′), (a″) and `docs/reports/T2498-1a-audit.md` (PASS) stand for row c (1a (xii): row c `QEndB1Gen` 1120 lines, ticket 1,250). Amend 1 (family row 9, `∃ C₆` after `κ`) is applied in hypothesis `hTh`.

## (a′) Preflight corrections and design deviations — Wed Oct 14 08:29:08 UTC 2026
No number or verdict of (a) is corrected. The bundle fixed at the 1a-audit (22 premises of `stOeqNQPTgL''_of` + D1 + `∃ C₆` after `κ` + `B45Gen_Facts`) is the signature of target 12 (`premdiff.py` output below). Deviations of the Lean text from the ticket, none changes a pinned text (paper-delta candidates in (d)):
1. **D1 at `KL = 1/𝔠`.** The family `QProxyG_KerEK4Fam` takes `KL` before `∃ C4`; `stOeqQtRoundPTgL''_of` calls it with `KL := 1/𝔠`, `k := n_`, after the flow's `𝔠` is introduced (so `C4` depends on `𝔠`); row b's endpoint reads `QProxyG_KerEK4 … (1/𝔠) C4 n`. Vocabulary constant `Cv = C4 + 1`, `Or.inl`.
2. **`K₆ = max C₆' 1`.** `startLevelQNg` and `altGridEndQNg` ask `1 ≤ K₆`; `B45Gen_Facts` gives row/column sums at most `C₆'/(1-t)`, which is at most `max C₆' 1/(1-t)`.
3. **Initial event.** The generic flow matrix `Hf` has no Hermitian field, so `QEndB1Gen_initQ` is stated for `Hf n (s n) ω` Hermitian, and its transfer to the walk uses `Cm.Hpath s v K n 0` Hermitian everywhere (`QEndB1Gen_Hpath_herm`, from `StepDecompGen_WalkForm`) with the measurable set `{M | M.IsHermitian → bound}`; band: `seqHflow_isHermitian`.
4. **Spectral constants of the initial loops.** `Γ = κm⁻¹` (`DecayGen_Spec`) and `K₆` replace the band's `2/√κ'`: `c₀ = (2m+5) K₆ (3·4^{dm} κm⁻¹ C)`. No import beyond the ticket's list; `nqEnd_rangeCond_mono` (private, `Induction/NQEndLin`, imported through `NQEndFlowGen`) is opened.

## (b) Script output (stage 1b)
### Builds (all times `date -u`)
```
$ lake build   # whole library, RBM3D.lean carries `import RBM3D.Chain.QEndB1Gen`; at 7bfe5a58 08:21:14 -> 08:22:58, exit 0; on the tree committed later as 04fe369f (comment-only change; the log below) 08:26:46 -> 08:27:02, exit 0; lines matching ": error": 0
RBM3D.lean:617:0: axiom audit: 15178 theorems, 4698 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14).
Build completed successfully (4387 jobs).
baseline (hub merge build of row b, `scratchpad/T2498b-merge-build.log`): axiom audit: 15172 theorems, 4696 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).; premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14).
here +6 theorems, +2 definitions (the 8 public names below), no new premise
$ lake build RBM3D.Chain.QEndB1Gen   # at 04fe369f, 08:27:31 -> 08:27:33 (already built by the full build above)
Build completed successfully (3920 jobs).
$ lake env lean docs/tickets/checks/T2498-check.lean   # branch worktree, 08:27:43 -> 08:27:48, exit 0, 1705 output lines, 0 containing "error"
```
### Axioms (`ax.lean`: `collectAxioms` over the 8 public new names and over every non-internal or private constant of the module)
```
(non-internal or private) constants in the module; modules found 1; declarations 76; [([Classical.choice, Quot.sound, propext], 51), ([Quot.sound, propext], 15), ([propext], 10)]
RBM.BA.STXiRoundPTgL'': [propext, Classical.choice, Quot.sound]
RBM.BA.STOeqQtRoundPTgL'': [propext, Classical.choice, Quot.sound]
RBM.BA.bandFM_STXiRoundPT'': [propext, Classical.choice, Quot.sound]
RBM.BA.bandFM_STOeqQtRoundPT'': [propext, Classical.choice, Quot.sound]
RBM.BA.stOeqQtRoundPTgL''_of: [propext, Classical.choice, Quot.sound]
RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band: [propext, Classical.choice, Quot.sound]
RBM.BA.QEndB1GenCheck.stOeqQtRoundPTgL''_band3: [propext, Classical.choice, Quot.sound]
RBM.BA.stOeqQtRoundPT''_holds_of_gen: [propext, Classical.choice, Quot.sound]
new public names checked: 8; with a non-standard axiom: 0
```
### Statements against the check (`verb.py`; scratch `chk.lean`, uncommitted)
```
$ python3 -I verb.py   # `T2498_XiRoundPTgL''`, `T2498_OeqQtRoundPTgL''` of docs/tickets/checks/T2498-check.lean against `QEndB1Gen.lean` (comments stripped, whitespace collapsed, name mapped)
T2498_XiRoundPTgL'' -> STXiRoundPTgL'' IDENTICAL up to the name 680 680
T2498_OeqQtRoundPTgL'' -> STOeqQtRoundPTgL'' IDENTICAL up to the name 319 319
$ python3 -I premdiff.py   # hypotheses of `stOeqNQPTgL''_of` (NQEndFlowGen) against `stOeqQtRoundPTgL''_of`
stOeqNQPTgL''_of hypotheses: 22  stOeqQtRoundPTgL''_of hypotheses: 25
hypotheses of the NQ pin with an identical text in the new theorem: 22 of 22
new hypotheses: ['hEK4', 'hTh', 'hB45']
different text: []
$ lake env lean chk.lean   # the check's three defs copied verbatim + `rfl` between check text and new text (target 11), the conclusion `T2498_OeqQtRoundPTgL''` (target 12), and `example : T2498_OeqQtRoundPTOf (fun d law Flow mkM T0 => ∃ Hf E lam' gK Ψ Aof, <the 25 premises>, True)` proved by `stOeqQtRoundPTgL''_of`: exit 0, 0 output lines
```
### Target 11: statements (`sed -n 67,83p`; defs to the blank line) and band bridges
```
def STXiRoundPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **Target 11, `STOeqQtRoundPTgL''`** (= `T2498_OeqQtRoundPTgL''`, binding; band `STOeqQtRoundPT''`, `QEndB1.lean:121`): the round in the setting
`STIngRgL d STCaseI` of a carrier family. -/
def STOeqQtRoundPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => STXiRoundPTgL'' (mk sz z) (law sz) s t)
```
```
theorem bandFM_STXiRoundPT'' : STXiRoundPT'' sz E s t ↔ STXiRoundPTgL'' (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STOeqQtRoundPT'' (d : ℕ) :
    STOeqQtRoundPT'' d ↔ STOeqQtRoundPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  bandFM_STIngR d STCaseI (fun sz E s t => STXiRoundPT'' sz E s t)
```
### Target 12: statement (`sed -n 886,944p`; conclusion = `T2498_OeqQtRoundPTgL''`, binding)
```
theorem stOeqQtRoundPTgL''_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- ticket rows 1-6: the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- ticket rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- ticket row 8 (D1 of the non-alternating half, `∃ Ck` before `(sz, z)`), row 10 (R1, the pinned `Aof κ`), row 12 (the flow window)
    (hKerFam : NQGoodGen_KerNALFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      1 ≤ Aof κ ∧ ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- ticket row 8 (D1 of the alternating endpoint, `∃ C4` before `(sz, z)`) and row 9 (the `Θ`-decay class, `∃ C₆` after `(𝔡, κ)`, Amend 1; `B45Gen_Facts`)
    (hEK4 : QProxyG_KerEK4Fam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hTh : ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
      Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM)) :
    STOeqQtRoundPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
```
### Compiled nonempty instances (`d = 3`, `sz0` windows, flow `z0`, `s ≡ 0`, `t ≡ 1/16`, `C_d = 1`; `sed -n 1103,1109p`; the other two examples are at lines 1112 and 1117)
```
example (hKb : STKboundgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0)) (hKw : STKwardgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0))
    (hLK : STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst)
    (hStep2 : STStep2ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst 1) :
    STXiRoundPTgL'' (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst := by
  obtain ⟨𝔠d, h0, -, hC⟩ := stOeqQtRoundPTgL''_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact hC (1 / 6) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI hKb hKw hLK (sz0_con 𝔠d h0) hStep2
```
The examples' hypotheses `hKb hKw hLK hStep2` are the four stochastic pins of `STIngRgL` (other gates' pins); every deterministic row (25 hypotheses of the theorem) is discharged at the band family by `stOeqQtRoundPTgL''_band` (all `d ≥ 3`; `Hf = seqHflow`, `E = STflowE`, `lam' = gK = sz.lam`, `Ψ = 0`, `Aof = 1`). Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`), `z0 = 1/2 + i N^{-4/5}` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`, window `[0, 1/16]` non-collapsed.
### Name-level tables (1b start; scripts `scope.py`, `prem.py`, `premdiff.py`, `stmts.py`, `greps.sh`)
```
public declarations of Induction/QEndB1 (line, status):
  STXiRoundPT'               :84    superseded duplicate (D4: `n_ ≥ 3`), band only
  STXiRoundPT''              :100   converted -> `STXiRoundPTgL''` (target 11); band bridge `bandFM_STXiRoundPT''`
  STOeqQtRoundPT'            :117   superseded duplicate (D4), band only
  STOeqQtRoundPT''           :121   converted -> `STOeqQtRoundPTgL''` (target 11); band bridge `bandFM_STOeqQtRoundPT''`
  stOeqQtRoundPT'_holds      :1790  superseded duplicate (D4), band only
  stOeqQtRoundPT''_holds     :1841  converted -> `stOeqQtRoundPTgL''_of` (target 12); band re-derivation `stOeqQtRoundPT''_holds_of_gen`; band theorem unedited (U3s4 reads it)
  inst_OeqQtRoundPT'         :1905  band instance, unedited
  inst_OeqQtRoundPT''        :1975  band instance, unedited; the new instances are in `QEndB1GenCheck`
private declarations of QEndB1 (all sections): 40
opened by `open private` (model-free, used by name): 18
   altQFlow_conStInd_exp_mono altQFlow_level_le altQFlow_phi_nonneg altQFlow_phiC_ge altQFlow_phiC_one_le altQFlow_K altQFlow_K_ne_zero altQFlow_K_low altQFlow_K_up altQFlow_K_card altQFlow_bootRHS_one_le altQFlow_bootRHS_two_le_one altQFlow_W_le_size altQFlow_Zd_le_size altQFlow_card_Zd altQFlow_two_pow_le altQFlow_union2 altQFlow0_Ylow_le_bootRHS
(the opened names are model-free: `STConStInd`, the levels `Λ_s, Φ₁..Φ₃, Φc`, the grid `K_n`, `STbootRHS`, sizes, the union bound)
```
Replaced / inside / not read (22): `altQFlow_prec_of_le_right` -> `NQEndFlowGen_prec_of_le_right`, `altQFlow_step2_restrict` -> `NQEndFlowGen_step2_restrict`, `altQFlow_hQ` -> `NQEndFlowGen_hQ` (opened, over `PrecL`); `altQFlow_meas_STLKM`, `_STQop`, `_initSet`, `_xi_le`, `_collapsed`, `_nq_half`, `altQFlow0_initQ`, `altQFlow0_core`, `altQFlow0_section` -> `QEndB1Gen_*` (new, private); `altQFlow_meas_pathH`, `_seqHflow`, `_transfer` -> the law field `hLaw`; `altQFlow_initQ`, `_core`, `_section`, `_Ylow_le_bootRHS` superseded duplicates (D4), not read; `altQFlow_lam_sqrt`, `_phi3_le` inside the opened `altQFlow_level_le`. `open private` lines: 4 (QEndB1: 18 names; NQEndFlowGen: 5; GridGoodGen: 2; NQEndLin: 1). Copies of a private text of a band file: none.
Hypotheses of target 12 (band fact -> generic hypothesis -> band discharge in `stOeqQtRoundPTgL''_band` -> BA source; ticket family row, owner):
| band fact (`stOeqQtRoundPT''_holds`) | generic hypothesis | band discharge | BA source (row) |
|---|---|---|---|
| `\|E n\| ≤ 2 - κ'`, `Im m ≤ 1`, `2/√κ'` of `startLevelQN` | `hSpec` (`∃ κm, DecayGen_Spec`), `hm` | `DecayGen_bandSpec` (`κm = √κ/2`), `norm_mE` | `EMn2BA_mF_data`, `ba_G_data` (3, 6) |
| `LoopForm`, walk, `S = SB`, row sums | `hL hW hSeq hS` | `stepDecompGen_loopForm_band`, `…walkForm_band`, `rfl`, `hierDriftGen_SB_row` | U2-BA, T5-BA (3, 4) |
| law of the flow matrix, `LCompat` | `hLaw hC` | `Step2EventsGen_bandLaw`, `bandStep34_LCompat` | `Step2EventsGenTw_baLaw`, `Step34GenTw` (5) |
| inputs of `gridGoodN_holds`, `nqLinGood_holds`, `stDecayLoopU_of_step2` | `hSE hFlow hWard hKcal hEK` | `bandFM_STSEforLn`, `Step2EventsGen_bandFlow`, `DecayGen_bandWardPair`, `bandFM_STKcalDecay`, `stEtermDecay` | `Step2EventsGenTw_baFlow`, `DecayGenTw_baWardPair`, U2-BA (1, 2, 6) |
| `GridRepTail` kernel | `hRow` | `gridRepTailGen_ker_band` | `gridRepTailGen_ker_BA` (7) |
| `qProxy4C d k 𝔡⁻¹ κ' (1/𝔠)` of `altGridEndQN'`; D1 of the non-alternating half | `hEK4` (`k = m+2`, `KL = 1/𝔠`); `hKerFam` | `qProxyG_kerEK4_band d`; `nqGoodGen_kerNAL_band d` | `baEKSumDecay2_holds`, `baEKSumDecayNAL_holds` (8; U3-BA (a)) |
| `Θ`-decay `step5Kernel_theta_decay` | `hTh` (`∃ C₆` after `(𝔡, κ)`) | `step5KerGen_thDecay_band` | U4-BA (a) (9) |
| Ward, kernel sums, `Θ` row/column sums `2/√κ` | `hB45` (`B45Gen_Facts`, `K₆ = max C₆' 1`) | `b45Gen_facts_band` | `baB45Gen_facts` (9) |
| R1 (band `gK = lam`, `A = 1`) | `hR1` | `⟨le_rfl, fun n => ⟨mul_self_nonneg _, le_rfl, (one_mul _).ge⟩⟩` | `TwistStep2_lam0_sq`, `BAflow_lam0_window` (10) |
| drift classes of `gridDriftQN_envelope'` | `hExp hKL hKT hU` (`∀ᶠ n`), `hKK` | `hierDriftGen_*_band`, `rfl` | `baHierDrift_*`, `baStep2Mat_KI` (11) |
| flow window | `hT0` | `Green.v3_premises_of_stFlow` | `EMn2BA_one_sub_T0` (12) |

Family-premise table as used (`prem.py`, 25 hypotheses): guarded (`∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow … →`, 14): `hSpec hL hW hKcal hEK hm hRow hExp hKL hKT hU hR1 hT0 hTh`; unguarded (`∀ sz z`, 6): `hLaw hC hWard hSeq hS hKK`; family-level text (5): `hSE hFlow hKerFam hEK4 hB45`. Eventual (`∀ᶠ n`): `hExp hKL hKT hU`; the link `hKK` is `∀ n`. Pinned `∃`: `𝔠d` (conclusion, before the flow), `C4` inside `hEK4` and `Ck` inside `hKerFam` (after `(k, κ, ε, 𝔡[, KL])`, before `(sz, z)`), `C₆` in `hTh` (after `(𝔡, κ)`, before `(sz, z)`), `Aof κ` (before `(sz, z)`); none after `(sz, z)`; no `∀ n` drift or hierarchy premise. `grep -cE '∀ \(sz : Sizes d\)'` = 27: lines 81-82 (binder types of the family parameters of `STOeqQtRoundPTgL''`), 887-891 (family parameters of the theorem), 20 hypotheses `hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hR1 hT0 hTh`; each hit is a row above.
UBA-C1 as used: R1 enters only through `hR1` into the facts `hcmp`, `hA` of `altGridEndQNg` (and its D1, `C4 ≤ Cv`, `C4 < Cv` at `Cv = C4 + 1`); the guard (g) is derived inside it from `hWO` (`QEndGridGen_gK_win`); the initial loops read `lam` only through the size-level mollifier; no second comparison form. C1: no `|E| < 2`, `M = mI`, `‖m‖ = 1` (inline `‖m‖ ≤ 1`, `hm`); TN-C4: 0 hits (below).
### Hygiene (`stmts.py`: C1/X1-C1 regex of `T2498.md:92` over the statements to `:=`; `greps.sh`)
```
STXiRoundPTgL''                       67-76    public  hits=[]
STOeqQtRoundPTgL''                    80-83    public  hits=[]
bandFM_STXiRoundPT''                  92-92    public  hits=['seqP']
bandFM_STOeqQtRoundPT''               97-99    public  hits=['STFlow', 'STflowE', 'lemT', 'seqP']
QEndB1Gen_Facts                      247-275   private hits=['Lloop']
QEndB1Gen_initQ                      282-294   private hits=[]
QEndB1Gen_core                       474-494   private hits=[]
QEndB1Gen_section                    684-706   private hits=[]
stOeqQtRoundPTgL''_of                886-944   public  hits=['Lloop']
flow_abs_le                         1029-1030  private hits=['2 - κ', 'STFlow', 'STflowE']
stOeqQtRoundPTgL''_band             1035-1037  public  hits=['STFlow', 'STflowE', 'lemT', 'seqP']
stOeqQtRoundPTgL''_band3            1072-1073  public  hits=['STFlow', 'STflowE', 'lemT', 'seqP']
stOeqQtRoundPT''_holds_of_gen       1080-1080  public  hits=[]
generic statements (`stOeqQtRoundPTgL''_of`, `QEndB1Gen_Facts`): only hit `Lloop` = substring of `KLloopOf` in the link `hKK` (model-free label list); the other private `QEndB1Gen_*`: 0 hits; `bandFM_*`, `*_band*`, `flow_abs_le`: band bridges, discharges, instance helper (labelled by design)
$ wc -l RBM3D/Chain/QEndB1Gen.lean                                                               ->     1126
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom" <file>                                     -> 0
$ grep -cE "^import RBM3D\.BA" <file>                                                            -> 0
$ grep -cE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" <file>                            -> 0
$ grep -c withLam <file>                                                                         -> 0
$ X1-C4: (def|abbrev|structure) GoodSetNg|GoodLinNg|...|Step5KerGen_ThDecay|B45Gen_Facts|NQGoodGen_KerNAL|STNQConclPTgL|STOeqNQPTgL in <file> -> 0
$ T2497 QGrid names (aTrueQNg|dGridQNg|aFrozQNg|rGridQNg|qErrQNg|gridDriftQNg|...) defined in <file> -> 0
$ grep -cE "∀ \(sz : Sizes d\)" <file>   (U5S-C3: each hit is a family parameter or a row of the table above) -> 27
$ same grep, hits by line range: <= 82 (binder types of the family parameters of the def) / 887-891 (family parameters of the theorem) / >= 893 (hypotheses) -> 2 / 5 / 20
$ grep -rln "import RBM3D.Chain.QEndB1Gen" RBM3D RBM3D.lean                                      -> RBM3D.lean 
$ grep -n "^import" <file> | cut -d: -f2 | tr "\n" " "                                           -> import RBM3D.Induction.QEndB1 import RBM3D.Chain.QEndGridGen import RBM3D.Chain.NQEndFlowGen import RBM3D.Chain.NQL
$ git diff --name-only main...t/T2498c                                                           -> RBM3D.lean RBM3D/Chain/QEndB1Gen.lean RBM3D/Probe/T2498Pins.lean 
$ git diff --name-only 2c0bc232 HEAD                                                             -> RBM3D.lean RBM3D/Chain/QEndB1Gen.lean 
$ git diff --name-only 2c0bc232 HEAD -- QEndGrid QEndB1 QtXiRoundLift QGridA QGridB NQ* Chain/NQ* BA | wc -l -> 0
$ git diff --numstat 2c0bc232 HEAD                                                               -> 1 0 RBM3D.lean;1126 0 RBM3D/Chain/QEndB1Gen.lean;
```
### Name clash (`clash.sh`: `git grep -w -F -l` of the 20 new final components, public and private, in `RBM3D RBM3D.lean`)
```
      20 names: new public + private final components (flow_abs_le is private in QEndB1GenCheck; it exists privately in other check namespac
main 051e596f: 0; t/T2498 5e8ef75a: 0; t/T2498a2 39fd68bb: 0; t/T2498b b3377663: 0; t/T2499 0c272838: 0; t/T2500 fc90ad3a: 0; t/T2501 0d98bc2b: 0; t/T2501a2 3f8e9624: 0; t/T2501b df731125: 0; t/T2502 b0d28f34: 0; t/T2502b 94db77fa: 0; t/T2502c 0f0ad532: 0; t/T2503 93bd54cd: 0; t/T2504 43f2230d: 0 (hits per ref: all 0)
this branch, other files with a hit: none
```
### Lines (stop rule), numstat, calibration
```
$ wc -l RBM3D/Chain/QEndB1Gen.lean  -> 1126 (stop size: file over 2,000; reserve `QEndB1Gen2` not needed; checkpoint 55a6a800: 870 lines before the endpoint theorem, 1,126 final)
$ git diff --numstat 2c0bc232 HEAD  -> 1 0 RBM3D.lean; 1126 0 RBM3D/Chain/QEndB1Gen.lean  (added 1,127 = 1,126 + 1 import line, removed 0, moved 0)
1a central 1,120 (`T2498-prove.md` (xii)): realized / forecast = 1126 / 1120 = 1.005; ticket 1,250: x0.90
```
### Narrative
- The file follows the band proof of `stOeqQtRoundPT''_holds` (`QEndB1:1841`, `altQFlow0_*` of §5′) with each band ingredient replaced by its merged carrier twin: `gridGoodN_holds` -> `gridGoodNgL_of`, `nqLinGood_holds` -> `nqLinGoodgL_of`, `stOeqNQPT''_holds` -> `stOeqNQPTgL''_of` (U3s2c), `stDecayLoopU_of_step2` -> `stDecayLoopUgL_of_step2`, `startLevelQN` -> `startLevelQNg`, `altYGridN` -> `altYGridNg`, `altGridEndQN'` -> `altGridEndQNg` (row b).
- Sections: 1 texts and bridges (`:60-100`), 2 helpers (`:102-239`), `QEndB1Gen_Facts`, `QEndB1Gen_initQ`, `QEndB1Gen_core` (`:241-674`), `QEndB1Gen_section` (`:676-868`), 3 target 12 (`:870-1014`), 4 band re-derivation (`:1016-1085`), 5 instances (`:1087-1122`).
- The grid walk lives on `Cm.Pp`; the flow matrix `Hf` lives on the law `μ`: the initial event (index `0`) and the terminal event (index `K_n`) are transferred by `Step2EventsGen_Law`, and `LM = L` by `GridGoodGen_LM_eq_L` (`LoopForm`, `LCompat`).
- The initial loops use `startLevelQNg` at `u = s_n` with levels from `STLKgL s` (lengths `m+1`, `m+2`) and the far decay `STDecayLoopUgL` (window `W^{e/(8d(m+1))}`, `D_F = (2m+5)/𝔠`), `Γ = κm⁻¹`.
- The section lemma combines the alternating part (core at `v_n`), the non-alternating part (`QEndB1Gen_nq_half`, bound `STbootRHS 2 ≤ STbootRHS 1`) and the collapsed indices (`STLKgL s`), as the band `altQFlow0_section`.
- The band re-derivation `stOeqQtRoundPTgL''_band` discharges all 25 hypotheses at the band family for every `d ≥ 3` (no open hypothesis), so target 12 is a theorem there and `stOeqQtRoundPT''_holds_of_gen` re-derives the band pin `STOeqQtRoundPT'' d` for every `d`.
- No band file, frozen signature or `def` is changed; no `BA/*` import; no copy of a T2491 pin text; the premise scan of the full build is the baseline (144).

## (c) Verified Mathlib names (every identifier of the code lines, comments stripped, resolved by `resolveGlobalConst` under the file's `open`s in a file importing the module, script `resolve.lean`: 134 resolved outside `RBM`; the 101 non-trivial ones)
`Classical.{not_imp, not_not}`
`Complex.{im_le_norm}`
`ENNReal.{ofReal, ofReal_le_ofReal}`
`Filter.Eventually.{of_forall}`
`Filter.{atTop, eventually_ge_atTop}`
`Fin.{castAdd, last, natAdd}`
`Finset.{measurable_sum, mem_Icc, mem_univ, sum_nonneg, sup'_le}`
`Fintype.{card_fin, card_fun, card_prod, card_subtype_le}`
`List.{ofFn}`
`Measurable.{mul_const, norm}`
`MeasurableSet.{iInter, iUnion, univ}`
`MeasureTheory.{measure_mono, measure_ne_top, ofReal_measureReal}`
`Nat.{cast_nonneg, le_succ, mul_le_mul, mul_le_mul_left, mul_le_mul_right, mul_pos, pow_le_pow_left}`
`Real.{exp, exp_le_one_iff, one_le_rpow, rpow_add, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_mul, rpow_natCast, rpow_neg, rpow_neg_one, rpow_nonneg, rpow_one, rpow_pos_of_pos, sqrt}`
`Set.{mem_compl_iff, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_union, univ}`
`continuous_id, div_le_div_of_nonneg_right, div_le_iff₀, div_nonpos_of_nonpos_of_nonneg, finRotate, finRotate_last, half_pos, imp_iff_not_or, inv_anti₀, inv_pos, isClosed_eq, le_add_of_nonneg_left, le_antisymm, le_max_left, le_max_right, le_mul_of_one_le_left, le_of_eq, le_rfl, le_trans, lt_div_iff₀, lt_min, lt_of_lt_of_le, measurableSet_le, measurableSet_lt, measurable_const, min_le_left, min_le_right, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_one, mul_self_nonneg, norm_nonneg, not_exists, not_lt, not_or, one_mul, one_pos, pow_add, pow_pos, pow_succ, sq, tendsto_rpow_atTop, true_and, true_imp_iff`
Absent or deprecated: `Set.mem_setOf_eq` is deprecated in this Mathlib (`Use Set.mem_ofPred_eq instead`, build warning); the file uses `Set.mem_ofPred_eq`.

## (d) Open issues and paper-delta candidates
- BA readings of targets 11-12 are not proved here (sources in the table: `baEKSumDecay2_holds`, `baHierDrift_*`, `baB45Gen_facts`, U4-BA (a), U3-BA (a)); the instances are at the band family only. For D1 the BA source must give `C4` after `KL` (`baEKSumDecay2_holds` takes `KL`): `stOeqQtRoundPTgL''_of` uses it at `KL = 1/𝔠` (deviation 1).
- Registry: `Test/Axioms.lean` is not edited (the ticket assigns row c no registry text; the scan found no new premise). Observation for the dispatcher: the `STXiBootgL'` line (`Test/Axioms.lean:218`) still reads "proofs: U3s3, U3s4"; U3s3 now proves the per-time round `STOeqQtRoundPTgL''` and U3s4 lifts it (decision (4)).
- `RBM3D.lean`: one import line after the last `import` (the hub unions it with the T2502 rows); `Probe/T2498Pins.lean` is untouched and stays on the stack base `t/T2498`. Ports: none from `../RBM1D` or `../RBM2D`; the source texts are the band files of this project (`QEndB1`, `NQEndFlowGen`). Module header lines 16-30 exceed 100 characters (10 `longLine` warnings in the build output; the `set_option` follows the header).
- Paper-delta candidates (Lean devices; no paper statement changes), continuing `T2498a`-`n`: `T2498o` hypotheses of `stOeqQtRoundPTgL''_of` beyond the band's: D1 `hEK4` replaces `qProxy4C`, `hTh` and `hB45` replace the band energy bounds `|E n| ≤ 2 - κ'` and the constants `2/√κ'` (continues `T2498f`, `T2498g`, `T2498m`); `T2498p` initial-loop constants `Γ = κm⁻¹`, `K₆ = max C₆' 1` (deviations 2, 4); `T2498q` the initial event is stated for Hermitian flow matrices and transferred through the Hermitian grid walk (deviation 3); `T2498r` D1 is used at `KL = 1/𝔠` after the flow's `𝔠` is introduced, so `C4` depends on `𝔠` (deviation 1; the family order of `QProxyG_KerEK4Fam` is unchanged).
