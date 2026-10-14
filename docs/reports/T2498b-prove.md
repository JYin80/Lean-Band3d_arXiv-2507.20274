Prover model: claude-sonnet-5-5

# T2498b prove report: row b (U3s3b), new `Chain/QEndGridGen` (target 10)
Branch `t/T2498b` (stacked on `t/T2498a2`, `main` merged at `0975e15a`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498b`), ticket `docs/tickets/T2498.md` with Amend 1. First `date -u` of this stage: Wed Oct 14 07:15:13 UTC 2026. Commits (`TZ=UTC git log`): `8987d9ea` 07:33:34 (checkpoint, sections 1-3), `86a6c76b` 07:41:16, `b3377663` 07:46:22 (final). Rows a, a′ are merged on `main`; row c is not touched.

## (a) Math preflight
Not rewritten: `docs/reports/T2498-prove.md` (a), (a′), (a″) and `docs/reports/T2498-1a-audit.md` (PASS) stand for row b (1a (xii): row b `QEndGridGen` 1171 lines, ticket 1,700). Amend 1 (`∃ C₆` after `κ`) concerns the family premise of row c; target 10 takes `C₆`, `K₆` as explicit constants.

## (a′) Preflight corrections and design deviations — Wed Oct 14 07:46:57 UTC 2026
No number or verdict of (a) is corrected. Deviations of the Lean text from the ticket, none changes a pinned text (1, 3, 4 are paper-delta candidates in (d)):
1. **The `lam` patch is kept, not replaced by a guard.** The ticket says the patch (T2302c) "becomes the R1 guard (g)". Row a's `yMomentsQUnifNg` asks `STMollifierProps (sz.lam n)` for every `n`, so the Y-moment constant uses the band patch family `altGrid_mol` (opened, private, model-free). The guard (g) enters as `QEndGridGen_gK_win`: `0 < lam n ≤ Λg` (from `hWO`) and `hcmp` give `0 < gK n ≤ Λg` at the indices of `∀ᶠ n`.
2. **Import added:** `Chain/NQEndLinGen` (not on the ticket's source list) for the carrier lemmas `NQEndLinGen_ev_hη`, `_ev_hδ`, `_Hpath_collapse`, `_eta_win` by `open private`; no text of it is copied.
3. **Constants:** the vocabulary constant `Cv ≥ C4` replaces `qProxy4C` in `ε` and `D''` (as `nqGridEndLinNg`: hypothesis `C4 < Cv ∨ A = 1`); the two radii of row a are `ε₁ := ε'` (`subGaussStop_altQNg`) with `d√A W^{ε'} ≤ W^ε`, `d W^{τ'} ≤ W^{ε'}` eventual from `hband`.
4. **Spectral hypotheses:** `DecayGen_Spec` (`κm`) and `‖m‖ ≤ 1` replace `|E n| ≤ 2 - κ`; the `B45Gen_Facts` fields (`hward`, `hker`, `hrow`, `hcol`, `K₆`) and `Step5KerGen_ThDecay` (`hTh`, `C₆`) replace the band energy facts of `altEnd_unQ`, `alt_hdriftGridQN`, `alt_hDclsGridQN`.

## (b) Script output (stage 1b)
### Builds (all times `date -u`)
```
$ lake build RBM3D.Chain.QEndGridGen   # 07:44:29 -> 07:44:49, exit 0 (first build of this file 07:37:48 -> 07:38:07, same text but 5 more `open private` names)
✔ [3913/3913] Built RBM3D.Chain.QEndGridGen (17s)
Build completed successfully (3913 jobs).
$ lake build   # whole library, RBM3D.lean carries `import RBM3D.Chain.QEndGridGen`; 07:44:53 -> 07:46:04, exit 0; lines matching ": error": 0
info: RBM3D.lean:616:0: axiom audit: 15172 theorems, 4696 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14).
Build completed successfully (4386 jobs).
baseline (hub merge build of row a′, `T2498a2-merge-build.log`): 15170 theorems, 4696 definitions; premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14): here +2 theorems (the two public ones below), no new premise
$ lake env lean docs/tickets/checks/T2498-check.lean   # branch worktree, 07:47:58 -> 07:48:02, exit 0, 1705 output lines, 0 containing "error"
```
### Axioms (`ax.lean`: `collectAxioms` over the 2 public new names, and over every non-internal or private constant of the module)
```
(non-internal or private) constants in the module; modules found 1; declarations 19; [([Classical.choice, Quot.sound, propext], 16), ([Quot.sound, propext], 3)]
RBM.BA.altGridEndQNg: [propext, Classical.choice, Quot.sound]
RBM.BA.QEndGridGenCheck.altGridEndQNg_instance: [propext, Classical.choice, Quot.sound]
new public names checked: 2; with a non-standard axiom: 0
```
### Target 10: statement (`sed -n 560,610p RBM3D/Chain/QEndGridGen.lean`; no band pin: the binding `T2498_*` texts are targets 11-12 of row c)
```
theorem altGridEndQNg (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm 𝔠 τ 𝔡 A C₆ K₆ : ℝ} (s t : ℕ → ℝ) (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτ : 0 < τ) (h𝔡 : 0 < 𝔡)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n)
    (hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n) (hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n)
    (hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hTh : Step5KerGen_ThDecay Cm.toFlowFM gK 𝔡⁻¹ C₆) (hC₆ : 0 ≤ C₆)
    (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τ t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) :
    ∀ m : ℕ, ∀ C4 Cv : ℝ, 0 < C4 → C4 ≤ Cv → (C4 < Cv ∨ A = 1) →
      (∀ᶠ n : ℕ in atTop, QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) (1 / 𝔠) C4 n) →
    ∀ Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) → (∀ n, 1 ≤ X n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetNg Cm n (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                  (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                    STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
                  (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
```
Quantifier order: carrier and window hypotheses first; `∀ m, ∀ C4 Cv`, D1 `hKer` (`QProxyG_KerEK4` at `KL = 1/𝔠`, `∀ᶠ n`), levels, `v`, `ε₀`, `D₁`; then `∃ ε₁ τ' D' C_K` after the carrier (as `nqGridEndLinNg`), then `∀ Φc K`. No pinned `∃` of the ticket (`𝔠d`, `C4`, `C₆`, `Aof κ`) is quantified here: they are family quantifiers of row c.
### Compiled nonempty instance (`RBM.BA.QEndGridGenCheck.altGridEndQNg_instance`, `d = 3`, band carrier `bandStep2Mat sz0 Einst`; `sed -n 1097,1116p`)
```
theorem altGridEndQNg_instance (m : ℕ) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, sInst n < vg n ∧ 0 < gridStep sInst vg (KC C_K) n ∧
        ∃ G : Set (PathΩ sz0), Cm1.Pp.real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          (∀ j ≤ KC C_K n, Cm1.Hpath sInst vg (KC C_K) n j ω ∈
            {H | GoodSetNg Cm1 n (gridTime sInst vg (KC C_K) n j) (m + 1 + 1) (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Λ3 n)
                (Φ1 n) τ' D' H} ∩
              GoodLinNg Cm1 n (gridTime sInst vg (KC C_K) n j) (m + 1 + 1) (((sz0.size n : ℕ) : ℝ) ^ ε₁) (Φ1 n) (12 : ℝ)
                (Φ1 n) ∩
              altYSetNg Cm1 n (gridTime sInst vg (KC C_K) n j) (m + 1) (((sz0.size n : ℕ) : ℝ) ^ ε₁ * 1)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 → ∀ a : Fin (m + 1 + 1) → Zd 3 (sz0.L n),
            ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) (m + 1) (sz0.lam n)) (sInst n)
                (fun b : Fin (m + 1 + 1) → Zd 3 (sz0.L n) =>
                  STLKMg Cm1 n (sInst n) (Cm1.Hpath sInst vg (KC C_K) n 0 ω) σ b) a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ ε₁ * (sz0.Bctl n (sInst n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 → ∀ a : Fin (m + 1 + 1) → Zd 3 (sz0.L n),
            ‖STLKMg Cm1 n (vg n) (Cm1.Hpath sInst vg (KC C_K) n (KC C_K n) ω) σ a‖ ≤
              ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (Λ3 n ^ ((1 : ℝ) / 2) + Φ1 n + 12 + Φ1 n + 1) *
                (sz0.Bctl n (vg n)) ^ (m + 1 + 1) := by
1154:example := altGridEndQNg_instance 0
1157:example := altGridEndQNg_instance 1
1160:example := altGridEndQNg_instance 2
```
Data (module doc §4): `m` arbitrary (examples `m = 0, 1, 2`), `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`), `E ≡ 1/2`, `s ≡ 0 < v ≡ 1/32 ≤ t ≡ 1/16` (`window_nondegenerate`: `Δ > 0` on every grid `KC C_K`), `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = 1/2`, levels `Λ = 3`, `Φ₁ = Φ₃ = 1`, `Φ₂ = 12`, `X = 1`, `ε₀ = 1/10`, `D₁ = 1`, `A = 1`, `Cv = C4 = qProxy4C 3 (m+2) 10 κi 6` (abstract, positive). Every hypothesis is discharged (no pin left open: `STKboundgL` by `stKbound_holds`, D1 by `qProxyG_kerEK4_band_at`, `hTh` by `step5KerGen_thDecay_band`, Ward and kernel sums by `zeroModeGen_*_band`, rows and columns by the private `b45_band_rowcol`).
### Name-level tables (1b start; scripts `scope.py`, `greps_c.sh`)
Scope (public band names of `QEndGrid` → status): `altGridEndQN'` → converted `altGridEndQNg`; `altGridEndQN` (unprimed) → superseded duplicate (D4), band only; band text of `QEndGrid` and its `QEndGridInst` instances → unedited. Private helpers of `QEndGrid` §0-§5 (script, `private` decls before line 1700):
```
private declarations of QEndGrid §0-§5 (before the public altGridEndQN, line 1700): 52
opened by `open private` (model-free, used by name): 31
  altGrid_ev_rpow_le altGrid_one_le_size altGrid_size_cast altGrid_W_le_size altGrid_ev_W_rpow_ge altGrid_step_le altGrid_K_mul_step altGrid_hΔη altGrid_gridTime_nonneg alt ...
replaced by a carrier text: 20: `altGrid_ev_hη`, `_ev_hδ`, `_pathH_collapse` → opened `NQEndLinGen_ev_hη`, `_ev_hδ`, `_Hpath_collapse`; `altGrid_stepErrN_nonneg` → `altEnd_stepErrNg_nonneg` (QEndA, opened) inside `QEndGridGen_qErrQNg_nonneg`;
  `altGrid_u_facts`, `_Nv`, `_crude_N`, `_yMomentsMax`, `_qErrQN_nonneg`, `_assembly'` → new `QEndGridGen_u_facts`, `_Nv`, `_crude_N`, `_yMomentsMax`, `_qErrQNg_nonneg`, `_assembly`; `altGrid_kappa_nonneg` → `altEnd_kappag_nonneg` (QEndA, opened); `altGrid_eps_nonneg` → `Real.rpow_nonneg`;
  `altGrid_etaT_inv_le`, `_eeShiftErrN_le`, `_gridTime_succ_sub`, `_delta`, `_ellT_nonpos`, `_delta_props` → inside the opened carrier lemmas / `altGrid_mol_props`; `altGrid_assembly`, `altGrid_arith` → superseded duplicates (D4), not read; `AltGridArith` → destructured by `obtain` (its fields are private).
```
`open private` list (`grep -n "^open private"`): 31 names `altGrid_*` from `Induction/QEndGrid` (model-free, `scope.out`); `altEnd_kappag_nonneg altEnd_stepErrNg_nonneg` from `QEndA`; `B45_norm_colsum` from `Induction/B45` (instance helper only); `NQEndLinGen_ev_hη _ev_hδ _Hpath_collapse _eta_win` from `Chain/NQEndLinGen`. Copies of a private text of a band file: none; `b45_band_rowcol` (instance namespace) re-proves the row and column sums of `b45Gen_facts_band` for a general energy sequence.
Hypotheses of target 10 (band fact → generic hypothesis → band discharge in the instance → BA source, family row of the ticket):
| band fact | generic hypothesis | band discharge | BA source (family row) |
|---|---|---|---|
| `\|E n\| ≤ 2 - κ`, `κ' ≤ Im m` | `hspec : DecayGen_Spec`, `hm : ‖m‖ ≤ 1` | `DecayGen_bandSpec`, `norm_mE` | `EMn2BA_mF_data`, `ba_G_data` (3, 6) |
| `LoopForm`, walk, `S = SB`, row sums | `hL hW' hSeq hS` | `stepDecompGen_loopForm_band`, `…walkForm_band`, `rfl`, `hierDriftGen_SB_row` | U2-BA, T5-BA (3, 4) |
| `GridRepTailGen_Ker` | `hRow` | `gridRepTailGen_ker_band` | `gridRepTailGen_ker_BA` (7) |
| D1 `qProxy4C` | `hKer`, `C4 ≤ Cv`, `C4 < Cv ∨ A = 1` | `qProxyG_kerEK4_band_at` | `baEKSumDecay2_holds` (8) |
| R1 (band `A = 1`, `gK = lam`) | `hcmp`, `hA`; guard (g) derived | `⟨mul_self_nonneg _, le_rfl, (one_mul _).ge⟩` | `TwistStep2_lam0_sq`, `BAflow_lam0_window` (10) |
| `STKbound E` | `hKb : STKboundgL` | `stKbound_holds` | pin (U2-BA / T1-BA) |
| drift classes of `gridDriftQN_envelope'` | `hExp hKL hKT hU` (`∀ᶠ n`), `hKK` | `hierDriftGen_*_band`, `rfl` | `baHierDrift_*`, `baStep2Mat_KI` (11) |
| Ward, kernel sums, `Θ` row/column sums (`2/√κ` of `altEnd_unQ`) | `hward hker hK₆ hrow hcol` | `zeroModeGen_*_band`, `b45_band_rowcol` | `baB45Gen_facts` (9) |
| `Θ`-decay (`step5Kernel_theta_decay`) | `hTh : Step5KerGen_ThDecay`, `hC₆` | `step5KerGen_thDecay_band` | U4-BA (a) (9) |
UBA-C1 as used: R1 (`hcmp`, `hA`, `C4 ≤ Cv`, `hdW2`, `hAk`) enters only through `subGaussStop_altQNg`, `alt_hkerGridQNg` (D1) and `alt_hDclsGridQNg` (`A`, `C₆`) inside `QEndGridGen_assembly`; the ℓ-crossings `hdW1`, `hdW2` are eventual from `hband`; the guard (g) is `QEndGridGen_gK_win`. Nothing of R1, D1, D2 enters the level split, the collapsed window or the union bound. C1: no `|E n| < 2`, `M = mI`, `‖m‖ = 1`; TN-C4: 0.
### Hygiene (`stmts.py`, `greps_c.sh`; statements to `:= by`)
```
QEndGridGen_gK_win                          79-80    private hits=[]
QEndGridGen_u_facts                        100-103   private hits=[]
QEndGridGen_Nv                             116-117   private hits=[]
QEndGridGen_crude_N                        128-136   private hits=['Lloop']
QEndGridGen_qErrQNg_nonneg                 171-174   private hits=[]
QEndGridGen_yMomentsMax                    197-207   private hits=[]
QEndGridGen_assembly                       238-335   private hits=['Lloop']
altGridEndQNg                              560-610   public  hits=['Lloop']
altGridEndQNg_instance                    1097-1116  public  hits=[]
C1/X1-C1 regex of `T2498.md:92` over these statements: 3 hits, all the substring `Lloop` of `KLloopOf` in the link `hKK` (model-free label list; the same single hit as row a′); 0 elsewhere (the `Cm1`/`STFlow` extraction line spans the doc comment above `b45_band_rowcol`)
$ wc -l RBM3D/Chain/QEndGridGen.lean                                                               ->     1168
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom" <file>                                       -> 0
$ grep -cE "^import RBM3D\.BA" <file>                                                              -> 0
$ grep -cE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" <file>                              -> 0
$ grep -c withLam <file>                                                                           -> 0
$ X1-C4: defs/abbrevs/structures named GoodSetNg|GoodLinNg|...|NQGoodGen_KerNAL|STNQConclPTgL|STOeqNQPTgL in <file> -> 0
$ T2497 QGrid names (aTrueQNg|dGridQNg|aFrozQNg|rGridQNg|qErrQNg|gridDriftQNg|...) defined in <file> -> 0
$ grep -cE "∀ \(sz : Sizes d\)" <file>   (U5S-C3)                                                -> 0
$ grep -rln "import RBM3D.Chain.QEndGridGen" RBM3D RBM3D.lean                                      -> RBM3D.lean 
$ git diff --name-only 0975e15a HEAD                                                               -> RBM3D.lean RBM3D/Chain/QEndGridGen.lean 
$ git diff --name-only main...t/T2498b                                                             -> RBM3D.lean RBM3D/Chain/QEndGridGen.lean RBM3D/Probe/T2498Pins.lean 
$ git diff --name-only 0975e15a HEAD -- QEndGrid QEndB1 QtXiRoundLift QGridA QGridB NQ* Chain/NQ* BA Test | wc -l -> 0
$ git diff --numstat 0975e15a HEAD                                                                 -> 1 0 RBM3D.lean;1168 0 RBM3D/Chain/QEndGridGen.lean;
```
G1 (check Part 3): the band reader of `QEndGrid` outside the writable files is `QEndB1` (`altGridEndQN'`); `QEndGrid` is not edited, so no band corollary is owed, and `#check @RBM.Ind.altGridEndQN'` (Part 3 of the check) compiles (exit 0 above). Ports: none from `../RBM1D` or `../RBM2D`; the source texts are the band files of this project (`QEndGrid`, `NQEndLinGen`).
Layering: `QEndGridGen` imports `QEndGrid`, `Chain/QGridGen2`, `NQBudgetGen`, `GridAssemblyGen`, `NQEndLinGen` (5 imports, all merged, no `BA/*`); no in-place file imports it; it is imported only by `RBM3D.lean`; no cycle (the build passed). Registry: `Test/Axioms.lean` not edited (row a′ edited the `GoodSetNg` owner text; the scan found no new premise); `RBM3D.lean` gets one import line after the last import.
### Name clash (`clash.sh`: `git grep -w -F -l` of the 11 new names in `RBM3D RBM3D.lean`)
```
names: altGridEndQNg altGridEndQNg_instance QEndGridGenCheck QEndGridGen_gK_win QEndGridGen_u_facts QEndGridGen_Nv QEndGridGen_crude_N QEndGridGen_qErrQNg_nonneg QEndGridGen_yMomentsMax QEndGridGen_assembly b45_band_rowcol
main 41e55513: names with a hit: 0
t/T2498a2 39fd68bb: names with a hit: 0
t/T2498 5e8ef75a: names with a hit: 0
t/T2499 0c272838: names with a hit: 0
t/T2500 fc90ad3a: names with a hit: 0
t/T2501 0d98bc2b: names with a hit: 0
t/T2501a2 3f8e9624: names with a hit: 0
t/T2501b df731125: names with a hit: 0
t/T2502 b0d28f34: names with a hit: 0
t/T2502b bd5531ea: names with a hit: 0
t/T2502c 0f0ad532: names with a hit: 0
t/T2503 93bd54cd: names with a hit: 0
```
### Lines (stop rule), numstat, calibration
```
$ wc -l RBM3D/Chain/QEndGridGen.lean  -> 1168 (stop size 1,700; reserve `QEndGridGen2` not needed; at the checkpoint 8987d9ea: 1,050 before the instance section)
$ git diff --numstat 0975e15a HEAD  -> added 1,169 (1,168 + 1 import line), removed 0, moved 0
1a central 1,171 (`T2498-prove.md` (xii)): realized / forecast = 1168 / 1171 = 1.00; ticket 1,700: x0.69
```
### Narrative
- `altGridEndQNg` is the band `altGridEndQN'` over `Cm : Step2Mat sz`. The structure follows `NQEndLinGen` (T2491): the per-sign assembly `QEndGridGen_assembly` feeds the merged `assembledNg` at `altExitTauNg`; the bundle `GridAssemblyHypNg` takes its fields from the row-a twins (`altEnd_hexpg`, `alt_hkerGridQNg`, `alt_hA0clsGridQNg`, `alt_hdriftGridQNg`, `alt_hDclsGridQNg`, `subGaussStop_altQNg`, `altEnd_stronglyMeasurable_zVecQNg`); the remainder is D2 `gridDriftQNg_envelope_ev`, bridged by `assembledRHSAltQNg_qErr_le` and `sum_weighted_qErrQNg_le` (T2497).
- The endpoint chooses the exponents in the band order with `altGrid_arith'` (opened) at `C₄ := Cv`, splits the levels (big: `QEndGridGen_crude_N` from `STmaxLKMg_crudeNg` and the wing bound `exists_norm_KI_le_wing`; small: `altBudgetNumQNg_eventually`, `budgetAltQNg`, `dDriftAltLinQNg_le_shape`), treats the collapsed window by `altEnd_unQg`, and takes the union bound over alternating `σ`.
- No band file, frozen signature or `def` is changed; no `BA/*` import; the premise scan of the full build is the baseline (144). Calibration: 1,168 lines (forecast 1,171, ticket 1,700).

## (c) Verified Mathlib names (36 names of the code lines, comments stripped, regex over `Real|Finset|Filter|Nat|Set|Complex|Fin|NNReal|Eventually|…`; `#check @name` in a file importing the module: exit 0, 0 errors; none absent)
`Complex.{norm_of_nonneg}`; `Eventually.{of_forall}`; `Fin.{last}`; `NNReal.{coe_pos}`; `Nat.{cast_nonneg, pos_of_ne_zero, zero_le}`; `Set.{Icc, compl_iInter, compl_univ, univ}`
`Finset.{le_sup', mem_univ, range, sum_le_sum, sum_pos, sup'_le, univ.sup', univ_nonempty}`
`Real.{log, one_le_rpow, rpow_add, rpow_add', rpow_le_one_of_one_le_of_nonpos, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_mul, rpow_natCast, rpow_neg, rpow_nonneg, rpow_one, rpow_pos_of_pos, rpow_zero, sqrt, sqrt_nonneg, toNNReal_pos}`

## (d) Open issues and paper-delta candidates
- Row c (`QEndB1Gen`, targets 11-13) reads `altGridEndQNg` by name: its hypotheses are the family rows of the ticket (3, 4, 6-11); the family quantifiers `∃ C4`, `∃ C₆` (after `κ`, Amend 1) and `K₆` of `B45Gen_Facts` are instantiated there. `KL = 1/𝔠` is the flow's own `𝔠`: row c chooses it after `𝔠` is introduced (the family `QProxyG_KerEK4Fam` takes `KL` before `∃ C4`).
- BA readings of target 10 are not proved here (sources in the table above: `baEKSumDecay2_holds`, `baHierDrift_*`, `baB45Gen_facts`, U4-BA (a)); the instance is at the band carrier only.
- `b45_band_rowcol` (private, instance namespace) repeats the row/column part of the proof of `b45Gen_facts_band` for a general energy sequence, because that theorem is stated for `STFlow` energies; dispatcher: accept, or have `b45Gen_facts_band` expose the per-index fact.
- `RBM3D.lean`: one import line (the hub unions it with the T2502 rows); `Probe/T2498Pins.lean` is untouched and stays on the stack base `t/T2498`.
- Paper-delta candidates (Lean devices; no paper statement changes), continuing `T2498a`-`k`: `T2498l` endpoint exponents at the vocabulary constant, `ε = min (e₂/(8 max(Cv, C_n))) (1/2)`, `D'' = 2C_n + 2 + 2Cv + k + (4k+1)/𝔠` with `Cv ≥ C4` and `C4 < Cv ∨ A = 1` (continues `T2498a`); `T2498m` spectral hypotheses of `altGridEndQNg` (`κm`, `K₆`, `C₆`, `hward`, `hker`, `hrow`, `hcol`, `hTh`) replace the band energy bound `|E n| ≤ 2 - κ`, `κ' = min κ (4/5)`, `2/√κ` (continues `T2498g`); `T2498n` the `lam` patch of T2302c is kept inside the endpoint (private `altGrid_mol*` opened) because `yMomentsQUnifNg` asks the mollifier properties at every `n`; the guard (g) is derived from `hcmp` at the eventual window.
