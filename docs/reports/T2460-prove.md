Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 16:50:25 UTC 2026
Base: worktree T2460 = main a1412ad. Scripts (numpy, scratchpad T2460/): `h123.py`, `instance.py`. Notation: c := a 1, b0 := a 0, G(σ)=Gres(H_k, z_u, σ), u=u_k, S=1 (`baFM.S n = 1`, FlowPins:327).

### (i) Exponent table
| quantity | value (source) | constraint | slack |
|---|---|---|---|
| C₀ | 11 (TwistGridRem2:395) | ≥ 0; clause (ii) ‖Rem‖ ≤ N^{C₀}√Δ passes through the glue unchanged | none needed |
| CK parts | Rem 6 (:397); Tail 2D+20 (TwistGridTail2:306); WTail 3D+40 (TwistGridWTail2:1236) | assembled CK = max (baTwistGridAssemble_holds, TwistGrid2:265) = 3D+40; D=1: 43 | max is the WTail value; stays 43 via baTwistGridMart_holds (22 from the parts alone, if clause 4 leaves) |
| K_n | ⌈N_n^{43}⌉+1 | K≠0, N^{CK} ≤ K | +1; K_0 has 272 digits: forced by the pin (∀K ≥ N^{CK}), not by the identities (they need K≠0 only) |
| window | s≡1/10, t≡1/2, T0∈[2/3,25/36] | 0≤s≤t≤T0<1; u_k∈[s,t]⊂[0,1) (gridTime_last, Walk:160) | t≤T0: ≥1/6; T0<1: ≥11/36 |
| lam0 > 0 (H1 K-part) | BAflowLam0=√T0·lam ≥ √(2/3)·lam | baKsol_two needs 0<g; BAflow_lam0_window gives it eventually (GreenSchur:72) | instance: every n (n₀=0); BAReal every n (BAflow_real :59) |
| Im m | ≥ 4/5 (mS_im_half, FlowPins:1147) | κ=1/2 ≤ Im m; Im(E+m)≠0 for twTheta_eq_thetaKer | 3/10 |
| ε′-shift (new, H3′ below) | N^{ε′/2}/√2 ≥ 1 ⟺ N ≥ 2^{1/ε′} | eventually in n (SizeTendsto) | ε′=1/10: N ≥ 2^{10}; N_0=2^{21} |
| constant in H3′ | 2 (= number of slots) | ‖twEEk‖ ≤ c‖STEEMg‖ | sharp: ratio 2 at H=0, σ=(+,+), a0=a1 (below); the paper's lem:DIfREP carries a constant C_{n,p} (3_5:218-222) |
| external hypotheses | none (every input is merged) | TEAM §8 lesson 14: no limit computation owed | — |

### (ii) Instance (d=3, sz0, (κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10), D=1, ε′=1/10; no N=0, all index sets nonempty)
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2460/instance.py`  (T0 bounds are the Lean theorems t0_sz0 FlowPins:1227 and mS.im ≤ 5/6, FlowPins:1123; Im m+Im z=6/5)
```
n= 0 L=4 W=32 lam=1/64 N=2097152 T0 in [0.6667,0.6944] lam0 in [1.276e-02,1.302e-02] K_n has 272 digits
      all hypotheses hold: True []
n= 1 L=8 W=1024 lam=1/4096 N=549755813888 T0 in [0.6667,0.6944] lam0 in [1.993e-04,2.035e-04] K_n has 505 digits
      all hypotheses hold: True []
n=10 L=44 W=5153632 lam=1/113379904 N=11659991713824860234842112 T0 in [0.6667,0.6944] lam0 in [7.201e-09,7.350e-09] K_n has 1078 digits
      all hypotheses hold: True []
```
### (iii) H1–H3 at c₁=c₂=c (S=1, W^d=Wd). Numerics: random Hermitian H, nb=3 blocks, W=2, all 4 charge pairs, all (a0,c) incl. a0=c
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2460/h123.py`
```
Step2Kern_Mss(fine M) = BAMss      : max err 0.0
(BAMss s s')^T = BAMss s' s        : max err 1.1102230246251565e-16
twK(b,c,c) = K2(b,c)  (baKsol_two) : max err 3.56109548082593e-15
thetaKer(s1,s0)(c,b) = W^d K2(b,c) : max err 1.788625797146843e-15
H2 drift identity (all sigma, a)   : max err 5.685991419351191e-14
H1 loop part  max|twL2M(c1=c2=a1) - loopFine|      : 2.1138016631127878e-16
Etilde^G loop max|twL3M(c1=c2=c) - loopFine(3)|     : 1.4033044459902308e-16
H3 as stated (twEEk = STEEMg): holds in 0 of 216 random cases; ratio twEEk/STEEMg in [0.036, 2.000]
H3' (k0,k1 real >= 0 and 0 <= twEEk <= 2*STEEMg): violations = 0
H=0, sigma=(+,+), a0=a1: twEEk = 1.2813153471, STEEMg = 0.6406576735; 4|z|^-6 W^-4d = 1.2813153471, 2|z|^-6 W^-4d = 0.6406576735
```
* **H1** (observable). L-part: twL2M σ b c c = Wd⁻²Σ_{x∈[b],w∈[c]} G(σ₁)_{xw}G(σ₀)_{wx} (twShift c w = w) = tr(G(σ₀)E_bG(σ₁)E_c) = loopFine σ ![b,c]; uses only G(−)=G(+)^* (H_k Hermitian: pathH_isHermitian Walk:98, PsiI_isHermitian, real lam0), so σ₀=σ₁ is included. K-part: twK σ b c c = Wd⁻¹Σ_{a′}Θ(b,a′)M(σ₀)_{c a′}M(σ₁)_{a′c} = Wd⁻¹(Θ M^{(σ₀σ₁)})(b,c) = baKsol_two (needs 0<lam0, BAReal, u∈[0,1)). TRUE.
* **H2** (drift), term by term (all TRUE, numerics above): slot 0 of STthetaOpg: Σ_b thetaKer(σ₀,σ₁)(b0,b)·Z(b) = Θ̃∘Z (twTheta_eq_thetaKer, with H1 at ![b,c]). Slot 1: thetaKer(σ₁,σ₀)(c,b) = Wd·K̃(b,c,c) (B̃₁) because thetaKer(σ,σ′)=M^{σσ′}(1−uM^{σσ′})⁻¹ at S=1 and (M^{(σσ′)})ᵀ=M^{(σ′σ)} (Msig(σ)_{ba}Msig(σ′)_{ab} swaps; any charges, so σ₀=σ₁ is the symmetric case). STELKLKMg at S=δ: Wd Σ_x LK(![x,c])LK(![b0,x]) = B̃₂ (with H1). STEGtMg = Ẽ^G: twL3M σ₃ a₁ a₂ c c = tr(G(σ₀)E_{a₁}G(σ₁)E_{a₂}G(σ₂)E_c) (same reindexing as H1). No charge-order mismatch.
* **H3** (quadratic variation). ∂_{xy}L̃(b)=−(Q₁+Q₂)_{yx}, Q₁=G(σ₀)E_bG(σ₁)E_cG(σ₀), Q₂=G(σ₁)E_cG(σ₀)E_bG(σ₁). So twEEk = Wd⁻¹Σ_{[x]=[y]}|Q₁+Q₂|²_{yx} (twEEM:101, S=δ), whereas STEEkMg k=0,1 (Step2Gen:389) are the 6-loops Wd Σ_{c′}tr(Q_kE_{c′}Q_k^*E_{c′}) = Wd⁻¹Σ_{[x]=[y]}|Q_k|²_{yx}, k=1,2 (labels (b,c,c′,c,b,c′), (c,b,c′,b,c,c′); Q_k^*: G(σ)^*=G(!σ)). The paper's (defEOTE, 3_5:172-190) also has only these diagonal terms. The cross terms 2Re(Q₁ conj Q₂) are absent. **H3 as pinned (equality) is FALSE**: 0 of 216 random cases; closed form at H=0, σ=(+,+), a0=a1: Q₁=Q₂=−z⁻³Wd⁻² 1_{[b]}, twEEk=4|z|⁻⁶Wd⁻⁴ ≠ 2|z|⁻⁶Wd⁻⁴=STEEMg. H=0 is a value of Hpath at k=0, s>0: Hpath=lam0·PsiI+√s·X(ω 0) and Xmat has two free real coordinates per off-diagonal pair (FineModel:105-114), so X ranges over all Hermitian matrices (PsiI is Hermitian); the pinned identity is pathwise ∀ω, so it fails at every n.
* **Amended H3′** (true, numerics: 0 violations): ‖twEEk‖ ≤ 2‖STEEMg‖, because |Q₁+Q₂|² ≤ 2|Q₁|²+2|Q₂|² and both 6-loops are sums of |Q_k|² (real ≥ 0, H Hermitian). The probe glue `T2452_bridge` rewrites the sum in clause (iii) by equality; with H3′ it is replaced by this step: pin event {N^{ε′}(ΣΔ‖STEE‖+N^{-D})^{1/2} < ‖Mart‖} ⊂ TL event at ε′/2, since ‖tw‖ ≤ 2‖STEE‖ and N^{ε′/2} ≥ √2 eventually (table). The glue calls `htail (ε′/2)` and `measure_mono`; H1, H2 and clauses (i), (ii) of the glue are unchanged.

### (iv) Target 4 (b): clause 4 of STGridRepNAtgL d 2 from TL clause (iv): **does not follow**
At c₁=c₂=c, U=uKer(σ₀,σ₁), U′=uKer(σ₁,σ₀) (Step2Gen:202 `UN`, 1017-1028), ΔM_j(σ,b,c) := Mart_{j+1}−Mart_j at TL index (σ,b,c,c):
* TL (BATwistGridMartAt clause iv, TwistGrid2:214-221): Y^{TL}_k(b0;c) = Σ_{j<k}Σ_b twU_{u_j,u_k}(b0,b)ΔM_j(σ,b,c); threshold Σ_jΔ‖Σ_{b,b′}twU(b0,b)conj(twU)(b0,b′)twEEM_{u_j}(b,b′;c,c)‖. One slot, one fixed c.
* Pin: Y^{pin}_k(a) = Σ_{j<k}Σ_{b0,b1}U_{jk}(a0,b0)U′_{jk}(a1,b1)ΔM_j(σ,![b0,b1]) = Σ_c U′_{jk}(a1,c)·Y-summand(b0;c); threshold STeeUMg = Σ_{b,b′∈(Zd)²}(U⊗U′)(a,b)conj(U⊗U′)(a,b′)STeeMg(σ,b,b′), b=(b0,b1), b′=(b0′,b1′).
* Two obstructions: (1) U′_{jk}(a1,c) depends on j, so Y^{pin} is not a c-sum of fixed-c TL sums Y^{TL} (a triangle inequality over c would not reproduce the coherent threshold STeeUMg); (2) STeeMg(σ,b,b′) with b1≠b1′ is a cross covariance between twisted observables at different c, which twEEM(b,b′;c,c) does not contain. No identity at c₁=c₂ links them. Hence target 4 (b) does not follow; (a) leaves with it (pre-signed, note (3)).
* Producer for the dispatcher: the two-slot twin of TwistGridWTail/WTail2 at BAUN (EKPins:53), i.e. coarse grid + peeling for the label-summed martingale with 2-slot kernels, cross-label QV. The one-slot TL files have 1822+1334 = 3156 lines (wc); band twin gridRepWTailQN_holds DifREP3:2343 (DifREP3 = 2567 lines). A new T row (2-slot BA tail), size of that order; far over 400.

### (v) Predicted lines (ticket item (v); predictions, basis in brackets) and importer scan
H1 ≈ 130 [U-D 100 + 26 compiled K-part], H2 ≈ 250 [five term matches + transposition], H3′ ≈ 300 [two 6-loop expansions + Cauchy–Schwarz], glue ≈ 130 [82 compiled + ε′/2 change], statements/instances ≈ 140: ≈ 950 total; H2 and H3′ < 400 each (trigger not expected); stop line 2000. Names/importer scan (`git grep`, hits; `RBM3D/BA/GridMartBA.lean` absent): main: 0 hits; t/T2454: 0 hits; t/T2461: no-branch; file exists: no.

### Verdicts
* Target 1 (T2460_Bridge): **FAIL** — conjunct H3 is false as stated (equality; counterexample above). H1, H2 hold (TRUE, routes above). Required amendment of the check file: replace the third conjunct by `‖twEEk … (a 0) (a 1) (a 1) k ω‖ ≤ 2 * ‖STEEMg … σ a‖`; glue as in (iii). Target 2 is unchanged.
* Target 2 (T2460_GridMart): **PASS** — the statement is true and not weakened; route = amended Bridge + baTwistGridMart_holds + private glue; no spectral premise, no new Prop premise.
* Target 3 (every d): **PASS** — no 3 ≤ d occurs in H1–H3, TL's pins, or the glue.
* Target 4: **FAIL** (route) — leaves before 1b per dispatcher note (3); (a)+(b) go together.
* Target 5 instances: **PASS** — numbers above.
* Overall: **FAIL** (target 1 as pinned).

## (a′) Preflight corrections — Mon Oct 12 18:56:32 UTC 2026 (Amend 1 item 4; section (a) not edited)
Binding: `docs/tickets/T2460-amend-1.md`; amended check `docs/tickets/checks/T2460-check.lean:167-169` (compiled on main, `docs/queue/CONTROL.md:213`: "T2460 (amended) exit 0 errors 0"). The numerics of (iii) (`h123.py`, rerun at this time with the same output) count for H3′: 0 violations of `0 ≤ twEEk ≤ 2 STEEMg` in 216 cases, ratio ≤ 2.000 attained at H=0, σ=(+,+), a0=a1.

**H3′ as in the amended check** (third conjunct of `T2460_Bridge`): `‖twEEk … σ (a 0) (a 1) (a 1) k ω‖ ≤ 2 * ‖STEEMg … (gridTime s t K n k) (Hpath s t K n k ω) σ a‖`, ∀ k ≤ K n, ∀ ω. Mathematics: ∂L̃ = −(Q₁+Q₂), `|Q₁+Q₂|² ≤ 2|Q₁|²+2|Q₂|²`, and STEEkMg (k=1,2) are the sums of |Q_k|² (see (iii)), so H3′ holds with constant 2 (sharp, (a) table row "constant in H3′"). H1, H2 unchanged (TRUE, (iii)).

**Glue of target 2 under H3′** (pin clause (iii), `Step2Gen:871-879`, against TL clause (iii), `TwistGrid2:210-214`; both read `∀ε′>0, ∀ᶠ n, ∀ i`, sum over j<k of gridStep·‖·‖ plus N^{-D}, power 1/2, event `∃ k ≤ K n`). For i=(σ,a0,a1,a1), S_p := Σ_j Δ‖STEEMg_j‖, S_t := Σ_j Δ‖twEEk_j‖. H3′ gives 0 ≤ S_t ≤ 2 S_p, so S_t+N^{-D} ≤ 2(S_p+N^{-D}) and
N^{ε′/2}(S_t+N^{-D})^{1/2} ≤ √2·N^{ε′/2}(S_p+N^{-D})^{1/2} ≤ N^{ε′}(S_p+N^{-D})^{1/2}  iff N^{ε′/2} ≥ √2 iff N ≥ 2^{1/ε′}.
Hence pin event(ε′) ⊂ TL event(ε′/2) pointwise in ω, for n large (`SizeTendsto`: N_n → ∞), and `measure_mono` with TL's bound at ε′/2 (same probability bound N^{-D}) closes clause (iii). Clauses (i), (ii) are as in (a) (H1, H2 equalities; C₀ unchanged). No new exponent beyond the row "ε′-shift" of (a) (ε′=1/10: N ≥ 2^{10}; N_0 = 2^{21}, margin N_0^{ε′/2}/√2 = 1.464).
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2460/glue.py`
```
eps'=0.1  N_min=2^(1/eps')=1024  cases so far 20000  violations 0
eps'=0.05  N_min=2^(1/eps')=1.04858e+06  cases so far 40000  violations 0
eps'=0.25  N_min=2^(1/eps')=16  cases so far 60000  violations 0
eps'=0.5  N_min=2^(1/eps')=4  cases so far 80000  violations 0
boundary N=2^10, St=2Sp: lhs-rhs = -0.00048810253786246705
N_0=2^21: N^(eps'/2)/sqrt2 = 1.4640856959456254  (>=1 required)
```
(Randomised check of the pointwise inclusion; at the boundary N=2^{10}, S_t=2S_p, D=1 the inequality is strict by 4.9e-4.)

**Remaining targets, unchanged from (a):** exponent table and instance (n=0,1,10: all hypotheses True) are not touched by H3′ (only the new ε′ row is added). Target 3 (every d): no `3 ≤ d` in H1–H3′ or the glue. Target 4 left the row (Amend 1 item 3); (iv) stays as a record for the dispatcher. Target 5 instance covers targets 1 (amended), 2, 3, 6; target 6 (no spectral premise): H3′ introduces none.

### Verdicts (after Amend 1)
* Target 1 (amended `T2460_Bridge`: H1, H2 equalities and H3′ with constant 2): **PASS** — H1, H2 TRUE, H3′ TRUE with 0 violations; routes in (iii).
* Target 2 (`T2460_GridMart`): **PASS** — glue via H3′ as above, event inclusion eventually in n.
* Target 3 (every d): **PASS**.  Target 5 (instances): **PASS**.  Target 6 (C1/spectral rule): **PASS**.
* Target 4: not in this row.
* Overall: **PASS**.

## (b) Script output — Mon Oct 12 19:26:26 UTC 2026
Branch t/T2460 at `79339380`; one file `RBM3D/BA/GridMartBA.lean`; `RBM3D.lean` not edited (CLAUDE.md §1: the hub adds the import at merge). Scratch scripts: `S` = scratchpad `T2460/` (`ax.lean`, `chk.lean`, `audit.lean`, `stmt_diff.py`).
### Size, build, axioms, library audit
```
$ wc -l RBM3D/BA/GridMartBA.lean; echo "lake env lean on the file: $(lake env lean RBM3D/BA/GridMartBA.lean 2>&1 | wc -l) output lines"; lake build RBM3D.BA.GridMartBA 2>&1 | grep -v '^$' | tail -1; lake env lean $S/ax.lean; lake env lean $S/audit.lean 2>&1 | head -1; echo "audit.lean = import RBM3D, import RBM3D.BA.GridMartBA, #assert_rbm_axioms: exit ${PIPESTATUS[0]}; lines naming GridMartBA/BAGridBridge/baGridMart/BATwistGridMartAt in its report: $(lake env lean $S/audit.lean 2>&1 | grep -c 'GridMartBA\|BAGridBridge\|baGridMart\|BATwistGridMartAt')"
     747 RBM3D/BA/GridMartBA.lean
lake env lean on the file:        0 output lines
Build completed successfully (4049 jobs).
'RBM.BA.BAGridBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridBridge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridMart_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 13341 theorems, 4213 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
audit.lean = import RBM3D, import RBM3D.BA.GridMartBA, #assert_rbm_axioms: exit 0; lines naming GridMartBA/BAGridBridge/baGridMart/BATwistGridMartAt in its report: 0
```
Landed 747 lines against the ticket estimate 450 / 760 (central) / 1,500 and the stop line 2,000. The build run after the last source edit (started 19:20:10 UTC, `date -u`) printed `✔ [4049/4049] Built RBM3D.BA.GridMartBA (5.4s)`.
### Target statements, extracted by script
```
$ sed -n 55,65p RBM3D/BA/GridMartBA.lean; sed -n 673,676p RBM3D/BA/GridMartBA.lean
def BAGridBridge (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) =
            STgAg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
            STgDriftg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω‖ ≤
            2 * ‖STEEMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n k)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n k ω) σ a‖
theorem baGridMart_holds (d : ℕ) :
    STGridMartgL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
  obtain ⟨C₀, hC₀, hAt⟩ := baTwistGridMart_holds d
  exact ⟨C₀, hC₀, GridMartBA_bridge C₀ (baGridBridge_holds d) hAt⟩
```
### Statement diff against the amended check `docs/tickets/checks/T2460-check.lean` (main, CONTROL H252)
```
$ python3 -I $S/stmt_diff.py | grep -v '^$'; lake env lean $S/chk.lean > $S/chk.out 2>&1; echo "chk.lean = check file + [∀ d, T2460_Bridge d := baGridBridge_holds; ∀ d, T2460_GridMart d := baGridMart_holds; BAGridBridge d = T2460_Bridge d := rfl]: exit $?, error lines $(grep -c error $S/chk.out)"
target 1 diff lines: 0
target 2 diff lines: 0
chk.lean = check file + [∀ d, T2460_Bridge d := baGridBridge_holds; ∀ d, T2460_GridMart d := baGridMart_holds; BAGridBridge d = T2460_Bridge d := rfl]: exit 0, error lines 0
```
### H1-H3 table (lines = size of the section of the file; `S = 1` is `baFM.S n = 1`, `FlowPins:327`)
| identity | lines | route | same-charge pair `σ 0 = σ 1` |
|---|---|---|---|
| H1 observable | §2: 106 (with the 3-loop helpers used by H2) | loop: `TwistGrid_twL2M_trace`, `P_cc = E_c` (`GridMartBA_Pb_diag`), `TwistGrid_LM_two`; `K`: `twK_diag` + `baKsol_two` | included: only `G(-) = G(+)^*` is used |
| H2 drift | §3: 112 | slot 0 `twTheta_eq_thetaKer`; slot 1 = `B̃₁`: `thetaKer_swap` (`(M^{σσ'})ᵀ = M^{σ'σ}`, `S = 1`) + `baKsol_two`; `B̃₂ = STELKLKMg`, `Ẽ^{G̊} = STEGtMg` (`S = δ`, `twL3M_diag`) | included: the swap holds for all charges |
| H3′ QV | §4: 248 | `∂L̃ = -(Q₁+Q₂)` (`twDerM_eq`); `twEEM = Φ(Q₁+Q₂)`; `STEEkMg_{0,1} = Φ(Q₁), Φ(Q₂)` (`loop6_*`, `sum_trace`); `Φ(Q+Q') ≤ 2(ΦQ+ΦQ')` | included: the instance example at line 709 runs over all four `σ` |
Glue 108 lines (§6, with `tail_mono`), `baGridMart_holds` 10, instances 70. H2 and H3′ are below the 400-line trigger (P1G not triggered).
### Nonempty instances (d = 3, `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `s ≡ 1/10`, `t ≡ 1/2 < BAflowT0`, `D = 1`, `K n = ⌈N_n^{CK}⌉₊+1`)
```
$ grep -n '^example' RBM3D/BA/GridMartBA.lean | cut -c1-72; sed -n 726,737p RBM3D/BA/GridMartBA.lean
695:example : ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 
709:example : ∃ n : ℕ, ∀ (σ : Fin 2 → Bool) (ω : PathΩ sz0), let a : Fin
725:example : True := by
739:example (d : ℕ) : STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => (baStep2Data s
  obtain ⟨C₀, hC₀, H⟩ := baGridMart_holds 3
  obtain ⟨CK, hCK, H2⟩ := H (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) 1 one_pos
  obtain ⟨Mart, Rem, h1, h2, h3⟩ := H2 (GridMartBA_Kinst CK) (GridMartBA_Kinst_ne CK)
    (Filter.Eventually.of_forall fun n => GridMartBA_Kinst_ge CK n)
  have : IsProbabilityMeasure ((baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).Pp) := by
    rw [baStep2Mat_Pp]; exact isProbabilityMeasure_pathP _
  have c1 := (h1 0 (![false, true], fun _ => 0)).exists
  have c2 := (h2.and (Filter.Eventually.of_forall fun _ : ℕ => True.intro)).exists
  have c3 := (h3 (1 / 10) (by norm_num)).exists
  trivial
```
(a) line 695: target 1 applied at the data (the eventual three identities); line 709: the identities at one `n`, `k = 1`, `a = (0,0)`, every sample and every `σ`. (b) line 725. (c) line 739: the `baStep2Data` reading, definitional.
### Name clash, importer, item-6 and hygiene
```
$ grep -rn --include='*.lean' -E 'BAGridBridge|baGridBridge_holds|baGridMart_holds|GridMartBA' RBM3D RBM3D.lean | grep -v '^RBM3D/BA/GridMartBA.lean' | wc -l; for r in main t/T2454 t/T2461; do echo "$r: $(git --no-optional-locks grep -n -E 'BAGridBridge|baGridBridge_holds|baGridMart_holds|GridMartBA' $r -- 'RBM3D/*.lean' 'RBM3D.lean' | wc -l) hits"; done; grep -c -E '\|E\||\bmE\b|etaT|\bzt\b|mSigma|sz\.lam' RBM3D/BA/GridMartBA.lean; grep -c -E 'sorry|admit|^axiom|native_decide' RBM3D/BA/GridMartBA.lean; git --no-optional-locks diff main...t/T2460 --stat | cat; git --no-optional-locks diff main...t/T2460 --name-only -- RBM3D/BA/Twist* RBM3D/BA/Step2BA.lean RBM3D/Chain RBM3D/Path RBM3D/Induction | wc -l
       0
main:        0 hits
t/T2454:        0 hits
t/T2461:        0 hits
0
0
 RBM3D/BA/GridMartBA.lean | 747 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 747 insertions(+)
       0
```
Output order: library hits (new names, outside the file; no importer), hits on main / t/T2454 / t/T2461, item-6 matches (`|E|`, `mE`, `etaT`, `zt`, `mSigma`, `sz.lam`), `sorry|admit|axiom|native_decide` matches, diff stat, edits to the files of the 'Not here' list.
Ports: none from RBM1D/RBM2D (no diff-stat owed). Copied from RBM3D: probe `20d5f15:RBM3D/Probe/T2452Pins.lean:241-306` (glue, changed as below) and `:316-342` (`twMB`, `K_eq`); `BA/KTreeDeriv.lean:112, 118` (`Mss_swap`, `Theta_swap`). Opened private (`open private`, no edit): `TwistGrid.lean:229, 731, 746, 764`; `TwistKer.lean:650, 654, 659, 708, 806`.
### Narrative
* Delivered: targets 1 (amended H3′), 2, 3, 5, 6. Target 4 is not in this row (Amend 1 item 3); 1a (iv) (report lines 47-52): TL weights one slot, the pin two, so clause 4 does not follow from TL.
* `BAGridBridge` and `baGridMart_holds` equal `T2460_Bridge` and `T2460_GridMart` text for text after the head (diff 0, `rfl` in `chk.lean`); both hold for every `d` (no `3 ≤ d`).
* H1, H2 are proved for every Hermitian `H`, `u ∈ [0,1)`, `0 < BAflowLam0`, `BAReal`; H3′ for every Hermitian `H`. `baGridBridge_holds` supplies `0 < BAflowLam0` eventually (`BAflow_lam0_window`), `BAReal` at every `n` (`BAflow_real`) and `gridTime ∈ [0,1)`.
* The glue `GridMartBA_bridge` is private and copies the probe's `T2452_bridge`; changes: `Pn` carries the inequality H3′; clause (iii) uses `htail (ε'/2)` and `measure_mono`; the inclusion of the events is `GridMartBA_tail_mono`, valid once `2 ≤ N^{ε'/2}` (eventually: `SizeTendsto`, `tendsto_rpow_atTop`), a stronger eventual condition than (a′)'s `N^{ε'/2} ≥ √2`, same conclusion.
* The public theorems take no `Prop` premise; the premise scan of `Test/Axioms.lean` does not list `BATwistGridMartAt` (count 0 above).
## (c) Verified Mathlib names (each `#check` elaborates; scratch `names.lean`)
`Matrix.mul_apply`, `Matrix.mul_diagonal`, `Matrix.conjTranspose_mul`, `Matrix.conjTranspose_apply`, `Matrix.transpose_mul`, `Matrix.transpose_nonsing_inv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.one_apply`, `Finset.sum_ite_eq`, `Finset.sum_filter`, `Finset.sum_comm`, `Fin.sum_univ_two`, `Complex.mul_conj'`, `Complex.norm_real`, `Complex.ofReal_add`, `Real.norm_of_nonneg`, `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_one`, `Real.rpow_add`, `Real.rpow_nonneg`, `tendsto_rpow_atTop` (root namespace), `Filter.Tendsto.eventually_ge_atTop`, `Filter.Eventually.exists`, `MeasureTheory.measure_mono`.
Verified absent: `Real.tendsto_rpow_atTop` (unknown constant; the name is the root `tendsto_rpow_atTop`). `Set.mem_setOf_eq` is deprecated (hint `Set.mem_ofPred_eq`); not used.
## (d) Open issues and paper-delta candidates
* **T2460a** (confirms U-D's `T2452b` and adds a fact): at BA the grid martingale pin follows from the twisted pin and three identities, not from `lem:DIfREP` (`7_8:1994` "remain valid"). The probe's third identity `twEEk = STEEMg` is false ((a), lines 28-58); the true one is `‖twEEk‖ ≤ 2‖STEEMg‖` (slot count 2), which costs `ε' → ε'/2` in clause (iii). `STGridMartgL` itself is unchanged.
* Consumers of `baGridBridge_holds` (for example `docs/tickets/checks/T2471-check.lean:171` on main) must read H3 as the inequality H3′, not an equality.
* Target 4 (`T2460_GridRepN2`, the `m = 2` list form with the two-slot clause 4) has no producer yet; the dispatcher decides after T2459 (Amend 1 item 3; sizing in (a) (iv)). A later clause-4 row can re-run the glue with the canonical `Mart`, `Rem` through the public `baGridBridge_holds`; the file does not import `RBM3D.Chain.GridDuhamelGen`.
