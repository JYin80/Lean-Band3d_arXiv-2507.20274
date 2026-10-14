Prover model: claude-sonnet-5-5
## (a) Math preflight — Wed Oct 14 02:49:02 UTC 2026

Row a2 only (target 2 `baIniTermGen_cltFlow` = `T2501_CltFlowBA`, its five registry heads, instance 8). Tuple
`(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `d ≥ 3`, `Λ = 𝔡⁻¹`, `g = sz.lam`, `g₀ = BAflowLam0 = √t₀ g`, `E = BAflowEs`,
`m_F = BAmF` (real-axis datum, `BAflow_real` `GreenSchur:59`: `BAReal d L g₀ κ E m_F`, so `Im m_F ≥ κ` for every `n`).

### (i) Exponent table
| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | `κ'` (before `(𝔠,sz,z)`) | `min(κ,1)` | `0<κ'≤1`; `κ' ≤ Im m_F` ∀n (`BAReal.2`, `κ ≤ Im m_F`) | `Im m_F − κ'`: 0.4993 at instance n=0 (script) |
| 2 | `δ` | `ε/2` | ∀ᶠn `N^{-1+δ} ≤ 1−T0`; `1−T0 = Im z/(Im m+Im z) ≥ N^{-1+ε}/2` (BAdom; `Im m ≤ 1` by `BAm_norm_le_one` `Ward:136`, `Im z ≤ 1`) | need `N^{ε/2} ≥ 2` (`N→∞`, `SizeTendsto`); sz0, ε=1/10: `N^{1/20} ≥ 2^{21/20} = 2.07` at n=0, growing |
| 3 | `A` (R1) | `(κ+1)/κ` (=3 at κ=1/2) | `g² ≤ A g₀²` ⇔ `A t₀ ≥ 1`; `t₀ ≥ κ/(κ+1)` (`TwistStep2_T0_ge` `TwistStep2:731`, `TwistStep2_lam0_sq` `:740`) | equality iff `Im m=κ, Im z=1`; instance `A t₀ = 3.0000` |
| 4 | `STThPropsg` constants `C₅',c₅,C₆',C₇'` (after the flow, before `∀ᶠ n`) | `A·C₅, c₅, A·C₆, A·C₇` from `baProp5to8_holds d 𝔡⁻¹ κ (1/2)` (`Prop6Path:1049`) at `BAReal d L g₀ κ E m_F`, `0<g₀≤𝔡⁻¹` ∀ᶠn | decay: `Bparam d L g₀ t K ≤ A·Bparam d L g t K` (first summand `(g₀²+x)⁻¹ ≤ A(g²+x)⁻¹` ⇐ `g²+x ≤ A(g₀²+x)`, from row 3 and `A≥1`; second summand has no `g`); exp factor: `ℓ_t(g₀) ≤ ℓ_t(g)` (row 6) so `e^{-c₅|a|/ℓ(g₀)} ≤ e^{-c₅|a|/ℓ(g)}`; BD1/BD2: `(g₀²+x)⁻¹ ≤ A(g²+x)⁻¹`; `c = 1/2 ∈ (0,1)` | constants depend on `(d,κ,𝔡)` only; loss exactly one factor `A` (script: max `Bparam(g₀)/Bparam(g)` = 1.0000 ≤ 3 at n=0..2) |
| 5 | window `0<g₀≤𝔡⁻¹` | ∀ᶠn (`BAflow_lam0_window` `GreenSchur:72`) | `g₀ ≤ g`, `lam>0` from `WO` | sz0: `g₀ ≤ 1/64` vs `𝔡⁻¹ = 10` |
| 6 | `ℓ_t(g)=min(max(g/√|1−t|,1),L)` | monotone in `g≥0` | `ℓ(g₀) ≤ ℓ(g)` (`EMn2BA_ellT_mono_g` `EMn2BA:591`, as in `baEMn2ExpHK`) | script: True n=0..2 |
| 7 | `c₁` of `STKpropsg` (size clause, ∀ᶠn, at `s` under `STReg5I`) | `(4/3)·A·C₅` (K=2 closed form `K^{(2)}=W^{-d}(ΘMss)`, `baKsol_two` `KInduct:88`) | `sup_a|Θ_s(0,a)| ≤ C₅'·Bparam(g,s,0)`; `Bparam(g,s,0)=(g²+x)⁻¹+(L^d x)⁻¹ ≤ lam⁻²(1+L^{2-d})`, using `x=1−s ≥ 1−t ≥ lam²/L²` (regime) and `L^{2-d} ≤ 1/3`; `Σ_c|Mss(c,b)| = Σ_c|M_cb|² = 1` (Ward, `BAMB_ward_row` `Ward:108`, `z.im=0`) so `|(ΘMss)(a,b)| ≤ sup|Θ|` | script: `lam²·W^d·‖K^{(2)}‖_∞ = 0.1742 / 0.1706 / 0.1705` (n=0,1,2); the bound `1−s ≤ lam²` is not used here |
| 8 | Ward row `Σ_y|M_xy|²` (`mk.M`, `z.im=0`) | `= 1` | `≤ 1` | 0 (sharp; script 1.0000000000) |
| 9 | `STMfarg` decay (`baPropM_holds` `CombesThomas:562`, clause (3)) | `C_M = BAct_C = 16d²/κ³ = 1152`, `c = BAct_rate = min(log(1+κ/(4dΛ)),κ/2) = 0.004158` at `(3,10,1/2)`; small branch `g₀<(2C)⁻¹=4.3e-4`: `‖M_ab‖ ≤ (C g₀)^{|a−b|} ≤ 2^{-|a−b|}`; else `≤ c⁻¹e^{-c|a−b|}`; uniform rate `c_M=min(c,log 2)` | for `c₀,D>0` ∀ᶠn: `‖M_xy‖ ≤ W^{-D}` once `|blk x − blk y| ≥ c₀ log³W·ℓ ≥ c₀ log³W`, i.e. `c₀ c_M (log W)² ≥ D + log(max(c⁻¹,1))/log W` | eventually (`log W→∞`); at `c₀=D=1` holds once `log W ≥ 17.8`, i.e. sz0 index `k=n+1 ≥ 18` (script). Needs `zdistInf ≤ zdistD` comparison only |
| 10 | `STKfargL` | merged `baEMn2ExpHK` (`EMn2BA:637`), `emn2ExpHK d BAFlow baFMz BAflowT0`, no new constant | needs `t ≤ T0`: here `s ≤ T0` | none |
| 11 | `H₀`, `g'`, `E` of `CltRepg`/`CltInvg` | `H₀ = g₀•PsiI`, `g' = 0`, `E = BAflowEs` | `μ = seqP(sz.withLam 0)`; `seqHflowBA g₀ = g₀•PsiI + Hflow(withLam 0)` (`BlockAnderson:83`) so `BAGt`, `BALloop` are the `CltRepg` right sides by unfolding; `H₀` Hermitian (`g₀` real); `CltInvg`: `Adj d L a b` depends on `zdistD(a−b)` | none (identities) |
| 12 | `STKpropsg` invariance (∀n, **including `g₀ n ≤ 0`**) | translation: `baK_translate` `KSolve:591` + `baKcac_isKLoopS` `KTreeRep:1674` + `baK_unique` `KSolve:568` (BAReal only, no `0<g`); reflection: see below | `BAKsol` is a `choose` of any `IsKLoopS` solution; existence from `baKcac_isKLoopS` at every `n`; `baKsol_two`/`baKsolve` need `0<g` and are used only in the ∀ᶠ size clause | reflection is NOT merged: `K^{(2)}=W^{-d}(ΘMss)` (`(Kn2sol)` = `BAKcac_spliced` clause 2 + `baK_unique`, no `0<g`); `Θ(x,y)=Θ(0,y−x)` (`baP8_BATheta_shift` `Prop6Path:497`), `Θ(0,u)=Θ(0,−u)` from `BATheta_isSymm` (`KBase:371`, BAReal); same for `Mss` (`BAMB_shift`, `BAMB_symm`); then `(ΘMss)(−x,−y) = Σ_b Θ(−x,−b)Mss(−b,−y) = (ΘMss)(x,y)`; est. ≤ 50 lines |
| 13 | regime `STReg5I sz s t` | `lam²/L² ≤ 1−t`, `1−s ≤ lam²`, `s<t≤T0` | window nonempty ⇔ `1−T0 < lam²` | **EMPTY at the ticket's instance** `(sz0, zSeq, flow_sz0)`: `1−T0 ≥ 11/36 > 1/4096 ≥ lam²` (see (ii)); nonempty at flow `z'` below |

Ticket corrections (for 1b): (c1) the ticket names `baOffDiag_holds` (`Ward:303`, rate `κ²/4`) as the source of `STMfarg`; its statement
(`BAoffDiag`, `MFixedPoint:583`) is `ε ≤ ‖1−t m²‖ ∧ Σ_{a≠0}|Mss(0,a)| ≤ (1−ε)‖1−t m²‖`, which is not a pointwise decay. The source is
`baPropM_holds` (`CombesThomas:562`, `BAPropM` clause (3), row 9) and the file needs `import RBM3D.BA.CombesThomas` (absent from the ticket's row-a2 list;
the check file imports it). (c2) the regime window is empty at `flow_sz0` (row 13), so instance 8 for the `∀ s t` block needs the flow `z'` of (ii).

### (ii) One concrete nondegenerate instance
`d=3`, `sz0` (`L=4k, W=(2k)^5, lam=(2k)^{-6}`, `k=n+1`; `Admissible 1/6 1/10` merged `sz0_admissible`), `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`, class output `κ'=1/2`, `δ=1/20`.
(1) `t`-free fields (κ', δ, `CltRepg`, Ward row, `STThPropsg`, `STExpInvgL`) at the merged flow `flow_sz0` (`z_n=zS L g`, `Im z ∈ [11/30,7/10]`).
(2) the `∀ s t` block (`STMfarg, STGijDecgL, STKfargL, STKpropsg`) is vacuous at `flow_sz0`: `T0 ≤ (5/6)/(6/5)=25/36` (`mS_im_upper`, `wI.im=6/5`), `1−t ≥ 11/36`, but `STReg5I` needs `1−s ≤ lam² ≤ 1/4096`, `s<t`. Nonempty flow
`z'_n = i·η_n`, `η_n = N_n^{-9/10}` (the lower edge of `BAdom`), data `1−s_n = lam_n²`, `1−t_n = lam_n²/L_n²`, `Cd` any:
- `BAdom`: `Im z'=η ≤ 1`, `η ≥ N^{-1+ε}` (equality); `Im m(z',g) ≥ √(1−36g²) − η ≥ 0.9955 ≥ κ` for `g ≤ 1/64`. Derivation: `L` even so the spectrum of `Ψ^B` (adjacency of `Z_L^3`, `|μ|≤6`) is symmetric, hence `Re m=0` (uniqueness of the `Im m>0` solution); with `u=Im m`, `u = (u+η)·avg 1/(g²μ²+(u+η)²) ≥ (u+η)/(36g²+(u+η)²)` gives `u((u+η)²+36g²−1) ≥ η > 0`.
- `t₀ = u/(u+η)`, `1−t₀ = η/(u+η) ≤ η/0.99`; `t ≤ t₀` ⇔ `η/0.99 ≤ lam²/L²`: `(2k)^{-16.2}·8^{-0.9}/0.99 ≤ (2k)^{-14}/4` holds for all `k ≥ 1` (script: ratio ≤ 0.1353 for `k ≤ 2·10^5`; exponent gap `(2k)^{2.2}`).
- `s<t`: `lam²/L² < lam²` (`L ≥ 4`); `0≤s`; `g₀ ≤ g ≤ 1/64 ≤ 𝔡⁻¹`.
No external hypothesis: every input (`baPropM_holds`, `baProp5to8_holds`, `baKcac_isKLoopS`, `baEMn2ExpHK`, `baSTGijDecgL_holds`, `stExpInvgL_of_rep`) is a merged proof, so no limit computation applies.

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2501a2/inst.py` (pure Python; solves the self-consistent equation on `Z_L^3` by Newton, DFT for `M`, `Mss=|M|²`, `Θ̂=(1−s M̂ss)⁻¹`, `K^{(2)}=W^{-d}ΘMss`):
```
A=(kap+1)/kap = 3.0  d=3, (kappa,eps,c,D)=(1/2,1/10,1/6,1/10), z_n=i*N_n^(-9/10)
n=0 L=4 W=32 lam=1.562e-02 N=2.097e+06 eta=N^-.9=2.044e-06 resid=0.0e+00
   Im m=0.99926807 (>=1/2; bound sqrt(1-36g^2)-eta=0.99559373) Re m=-1.8e-18 E_n=3.6e-24
   t0=0.9999979543 1-t0=2.046e-06 <= lam^2/L^2=1.526e-05: True; lam^2=2.441e-04; A*t0=3.0000>=1
   Ward sum_y|M_xy|^2=1.0000000000; ell(g0,s)<=ell(g,s): True; max Bparam(g0)/Bparam(g)=1.0000<=A
   at 1-s=lam^2, 1-t=lam^2/L^2: lam^2*max|K2/W^-d|=0.1742  (c1 candidate)
n=1 L=8 W=1024 lam=2.441e-04 N=5.498e+11 eta=N^-.9=2.715e-11 resid=1.1e-16
   Im m=0.99999982 (>=1/2; bound sqrt(1-36g^2)-eta=0.99999893) Re m=-4.0e-20 E_n=1.1e-30
   t0=1.0000000000 1-t0=2.715e-11 <= lam^2/L^2=9.313e-10: True; lam^2=5.960e-08; A*t0=3.0000>=1
   Ward sum_y|M_xy|^2=1.0000000000; ell(g0,s)<=ell(g,s): True; max Bparam(g0)/Bparam(g)=1.0000<=A
   at 1-s=lam^2, 1-t=lam^2/L^2: lam^2*max|K2/W^-d|=0.1706  (c1 candidate)
n=2 L=12 W=7776 lam=2.143e-05 N=8.125e+14 eta=N^-.9=3.812e-14 resid=1.5e-14
   Im m=1.00000000 (>=1/2; bound sqrt(1-36g^2)-eta=0.99999999) Re m=3.7e-21 E_n=-1.4e-34
   t0=1.0000000000 1-t0=3.812e-14 <= lam^2/L^2=3.190e-12: True; lam^2=4.594e-10; A*t0=3.0000>=1
   Ward sum_y|M_xy|^2=1.0000000000; ell(g0,s)<=ell(g,s): True; max Bparam(g0)/Bparam(g)=1.0000<=A
   at 1-s=lam^2, 1-t=lam^2/L^2: lam^2*max|K2/W^-d|=0.1705  (c1 candidate)
k=1..2e5: max over k of (N^-.9/0.99)/(lam^2/L^2) = 0.1353249321384208 <=1: True
existing zSeq n=0: Im z=0.36751 Im m=0.83249 t0=0.69374 1-t0=0.30626 lam^2=2.441e-04; STReg5I needs 1-t0<=1-s<=lam^2: False
analytic (FlowPins zSeq_im_ge, mS_im_upper): Im z>=11/30, T0<=(5/6)/(6/5)=25/36, 1-T0>=11/36=0.30556 > 1/4096=2.441e-04
BAct_C=1152 (2C)^-1=4.340e-04 c=0.004158 c_M=0.004158; STMfarg (c0=D=1) holds once log W>=17.8, i.e. sz0 index k=n+1>=18
```
Consequence for 1b and row b: the compiled instance of target 2 must use a flow whose `∀ s t` block is nonempty (`z'` above, or any `BAFlow` with `1−T0 < lam²`);
`half_lt_t0`/`t ≡ 1/2` (case (iii) times) cannot serve cases (i), (ii). The same remark applies to row b's target-12 regime times (fill-in (ii)).

### Verdicts
- Target 2 `baIniTermGen_cltFlow` (row a2, instance 8): **PASS** — hypotheses hold simultaneously at the data above; constants close (rows 1–13); two corrections (c1, c2) and the reflection of `K^{(2)}` (row 12) to be written by 1b.

## (a′) Preflight corrections — Wed Oct 14 03:17:11 UTC 2026
Three differences from (a); none changes the verdict (target 2 stays PASS).
1. Row 7: the size constant is `c₁ = A·C₅·(1+2^(d-1))` (`meanFar_T1`, `Evolution/MeanFar.lean:762`, with the unit column sum of `M^(σσ')`), not `(4/3)·A·C₅`.
2. (ii)/(c2): the datum whose `∀ (s,t)` block is nonempty is not the flow `z'` of (a) (not built) but the private datum of instance (B) below (pattern of `TwistStep2_flowII`, `BA/TwistStep2.lean:1353`).
3. Ticket target 2 names `BAK_row_sum` (`KKernel:124`) for the Ward row (row 8 of (a)); the file uses the equality `Σ_y |M_xy|² = 1` from `BAMB_row_sq_real` (`BA/Ward.lean:125`) through the `split` reindexing (`CltFlowBA_Mfine_row`, l.196).

## (b) Script output — Wed Oct 14 03:17:11 UTC 2026
```
$ lake build RBM3D.BA.CltFlowBA 2>&1 | grep -E "CltFlowBA|Build completed|error"
ℹ [4129/4129] Replayed RBM3D.BA.CltFlowBA
info: 'RBM.BA.baSTThPropsg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'RBM.BA.baSTMfarg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'RBM.BA.baSTKfargL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'RBM.BA.baCltRepg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'RBM.BA.baCltInvg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'RBM.BA.baSTKpropsg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'RBM.BA.baIniTermGen_cltFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (4129 jobs).
$ lake build   # whole library, root `RBM3D.lean` with `#assert_rbm_axioms`
non-vacuity certificates: 0 of 116 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/In
Build completed successfully (4378 jobs).
axiom audit: 14964 theorems, 4631 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 122 (borrowed 1, owed 55, structural 46, refuted 6, superseded 14).
registry: 2 borrowed + 114 owed + 123 structural + 7 refuted + 18 superseded; 142 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ wc -l RBM3D/BA/CltFlowBA.lean; git log --oneline -2; git diff --stat main...t/T2501a2
     778 RBM3D/BA/CltFlowBA.lean
3f8e9624 T2501a2: BA/CltFlowBA (IniTermGen_CltFlow at the BA tuple, five registry heads)
74574b10 T2501a2 WIP: CltFlowBA main section
 RBM3D.lean              |   1 +
 RBM3D/BA/CltFlowBA.lean | 778 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   9 +-
 3 files changed, 781 insertions(+), 7 deletions(-)
$ lake env lean docs/tickets/checks/T2501-check.lean > out; echo exit=$?
exit=0
error lines: 0
$ lake env lean pinchk.lean   # scratch, uncommitted: def T2501_CltFlowBA (text copied from the check by script) + example : T2501_CltFlowBA := baIniTermGen_cltFlow + the three shapes of the check
exit=0
$ git diff --name-only main...t/T2501a2 ; git diff --stat main...t/T2501a2 -- RBM3D/Chain RBM3D/Induction RBM3D/Evolution RBM3D/Graph
RBM3D.lean
RBM3D/BA/CltFlowBA.lean
RBM3D/Test/Axioms.lean
(the second command prints nothing)
$ registry line before (`lake env lean RBM3D.lean` on this branch before the edit) / after (`lake build`)
registry: 2 borrowed + 119 owed + 123 structural + 7 refuted + 18 superseded; 146 registered premise(s) carry nothing yet: [RBM.Loop.KL
registry: 2 borrowed + 114 owed + 123 structural + 7 refuted + 18 superseded; 142 registered premise(s) carry nothing yet: [RBM.Loop.KL
$ git diff main...t/T2501a2 -- RBM3D/Test/Axioms.lean | grep -E "^[-+]   " | cut -c1-60
-   -- T2455 (BA-U X1a, DECISIONS §265): the generic inputs 
+   -- T2455 (BA-U X1a, DECISIONS §265): the generic inputs 
-   `RBM.BA.STKfargL, -- the K-level far field of `𝒦^{(2)}` 
-   `RBM.BA.STMfarg, -- the entries of `M` across far blocks
-   `RBM.BA.CltInvg, -- `H₀ n` is invariant under the lift t
-   -- T2479 (BA-U X1b-1, DECISIONS §279): the premises of t
-   `RBM.BA.STThPropsg, -- shift, symmetry, `(prop:ThfadC)`,
-   `RBM.BA.STKpropsg, -- invariance of `𝒦^{(2)}` under tran
+   -- T2479 (BA-U X1b-1, DECISIONS §279): the premises of t
$ hypothesis-rule greps on RBM3D/BA/CltFlowBA.lean (hit counts)
C1 pattern: 0; X1-C4 '^(noncomputable )?(def|abbrev|structure) ': 0; local copies of the class/pin names: 0; T24xx_ text: 0; sorry|admit|axiom|native_decide: 0; withLam outside seqP (..withLam 0): 0
$ grep -nE "^private (def|abbrev|structure) " ...   # instance data of (B), private
597:private def CltFlowBA_szI : Sizes 3 where
604:private def CltFlowBA_wI : ℂ := ⟨0, 5003 / 5000⟩
605:private def CltFlowBA_mI : ℂ := BAmSubord 3 4 1 CltFlowBA_wI
606:private def CltFlowBA_zI : ℕ → ℂ := fun _ => CltFlowBA_wI - CltFlo
$ name clash: for n in <the 7 public names>; grep -rn "\bn\b" RBM3D RBM3D.lean | grep -v RBM3D/BA/CltFlowBA.lean | cut -d: -f1,2   # (n = each name)
baSTThPropsg_holds: RBM3D/Test/Axioms.lean:217 | baSTMfarg_holds: RBM3D/Test/Axioms.lean:200 | baSTKfargL_holds: RBM3D/Test/Axioms.lean:200 | baCltRepg_holds: | baCltInvg_holds: RBM3D/Test/Axioms.lean:200 | baSTKpropsg_holds: RBM3D/Test/Axioms.lean:217 | baIniTermGen_cltFlow: | 
private stem hits outside the file: 0
```
Target statements, extracted by script (`python3 -I`: from the line `theorem NAME` to the first line ending in `:=`):
```
-- CltFlowBA.lean:566
theorem baIniTermGen_cltFlow (d : ℕ) : IniTermGen_CltFlow d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := …
-- CltFlowBA.lean:135
theorem baSTThPropsg_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → STThPropsg (baFMz sz z) := …
-- CltFlowBA.lean:456
theorem baSTKpropsg_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STReg5I sz s t → STKpropsg (baFMz sz z) s := …
-- CltFlowBA.lean:259
theorem baSTMfarg_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ τ : ℕ → ℝ, STMfarg (baFMz sz z) τ := …
-- CltFlowBA.lean:310
theorem baSTKfargL_holds (d : ℕ) (hd : 3 ≤ d) : ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STKfargL (baFMz sz z) t := …
-- CltFlowBA.lean:316
theorem baCltRepg_holds {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) :
    CltRepg (baFMz sz z) (Sizes.seqP (sz.withLam 0))
      (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun _ => 0) (BAflowEs sz z) := …
-- CltFlowBA.lean:340
theorem baCltInvg_holds {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) :
    CltInvg (sz := sz) (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) := …
```
Compiled nonempty instances (file lines 694-701, 731-742; (A) datum `(sz0, zSeq, flow_sz0)`, `d = 3`, `n = 0`: `L = 4`, `W = 32`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`):
```
example : ∃ κ' δ : ℝ, 0 < κ' ∧ κ' ≤ 1 ∧ 0 < δ ∧ (∀ n, κ' ≤ ((baFMz sz0 zSeq).m n).im) ∧
    (∀ n x, ∑ y, ‖(baFMz sz0 zSeq).M n x y‖ ^ 2 ≤ 1) ∧ STThPropsg (baFMz sz0 zSeq) ∧
    STExpInvgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) := by
  obtain ⟨κ', δ, hκ', hκ1, hδ, H⟩ := baIniTermGen_cltFlow 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨H₀, g', E, hm, hev, hrep, hM, hTh, hX, -⟩ := H (1 / 6) sz0 zSeq flow_sz0
  exact ⟨κ', δ, hκ', hκ1, hδ, hm, hM, hTh, hX⟩

-- (B): the same theorem, the ∀ (s,t) block applied at the regime datum (s ≡ 0 < t ≡ 1/100):
example : STMfarg (baFMz CltFlowBA_szI CltFlowBA_zI) (fun _ => 0) ∧
    STGijDecgL (baFMz CltFlowBA_szI CltFlowBA_zI) (Sizes.seqP (CltFlowBA_szI.withLam 0)) (fun _ => 0) ∧
    STKfargL (baFMz CltFlowBA_szI CltFlowBA_zI) (fun _ => 0) ∧ STKpropsg (baFMz CltFlowBA_szI CltFlowBA_zI) (fun _ => 0) := by
  obtain ⟨κ', δ, hκ', hκ1, hδ, H⟩ := baIniTermGen_cltFlow 3 le_rfl (1 / 70) (1 / 2) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨H₀, g', E, hm, hev, hrep, hM, hTh, hX, hst⟩ := H (1 / 9) CltFlowBA_szI CltFlowBA_zI CltFlowBA_flowI
  exact hst (fun _ => 0) (fun _ => 1 / 100) (fun _ => le_rfl) (fun _ => by norm_num) CltFlowBA_tI CltFlowBA_regI

-- (B): the head STKpropsg alone:
example : STKpropsg (baFMz CltFlowBA_szI CltFlowBA_zI) (fun _ => 0) :=
  baSTKpropsg_holds 3 le_rfl (1 / 70) (1 / 2) (1 / 9) (1 / 10) (by norm_num) (by norm_num) CltFlowBA_szI CltFlowBA_zI
    CltFlowBA_flowI (fun _ => 0) (fun _ => 1 / 100) (fun _ => le_rfl) (fun _ => by norm_num) CltFlowBA_tI CltFlowBA_regI
```
Discharged in both: (A) `flow_sz0`; (B) `CltFlowBA_flowI` (`BAFlow` at `L ≡ 4`, `W_n = n+25`, `lam ≡ 1`, `w = (5003/5000) i`, `(κ,ε,𝔠,𝔡) = (1/70,1/2,1/9,1/10)`), `STReg5I` by `CltFlowBA_regI` (`lam²/L² = 1/16 ≤ 99/100`, `1 - s = 1 ≤ lam²`), `t ≡ 1/100 ≤ κ/(κ+1) ≤ T₀` by `CltFlowBA_tI`. No external hypothesis remains. Instance (A) has an empty `∀ (s,t)` block (`Im z_n ≥ 11/30`, (a) row 13), so that block is applied at (B). Ports are from this project (file header); RBM1D/RBM2D are not used, so no sister diff-stat applies.

### Narrative (routes; `CltFlowBA.lean` line numbers)
- Constants (fill-in (i)), all before `(sz, z)`, in `(d, κ, 𝔡)` only: `A = (κ+1)/κ`; `κ' = min κ 1`, `δ = ε/2`; `(C₅', c₅, C₆', C₇') = (A·C₅, c₅, A·C₆, A·C₇)` from `baProp5to8_holds d 𝔡⁻¹ κ (1/2)`; `c₁ = A·C₅(1+2^(d-1))`; `K = max(c⁻¹,1)`, `c_M = min(c, log 2)` for `STMfarg` from `baPropM_holds`.
- Target 2 `baIniTermGen_cltFlow` (l.566): `H₀ = g₀•Ψ`, `g' = 0`, `E = BAflowEs`; `κ' ≤ Im m_F` ∀n (`EMn2BA_mF_data`); `N^(-1+δ) ≤ 1-T₀` eventually (l.543: `EMn2BA_one_sub_T0`, `BAdom`, `N^(ε/2) ≥ 2`); `CltRepg` l.316; Ward row ∀n l.196; `STExpInvgL` = `stExpInvgL_of_rep` (`ExpInv:534`); `STGijDecgL` = merged `baSTGijDecgL_holds` (`Step2CloseBA:66`); the other four fields are the producers below.
- `baSTThPropsg_holds` (l.135): `STThg (baFMz sz z) = BATheta` at `g₀` (`Step2Kern_Mss_BA`, `S = 1`, l.72); shift `baP8_BATheta_shift`, symmetry `BATheta_isSymm`; decay, BD1, BD2 from `baProp5to8_holds` on the window `BAflow_lam0_window`; R1 conversions l.94-120.
- `baSTMfarg_holds` (l.259): source `baPropM_holds` (`CombesThomas:562`, clause (3)), not `baOffDiag_holds` ((a) c1; `import RBM3D.BA.CombesThomas` added); one profile for the small and the large branch (l.221); `log W → ∞` from `W ≥ N^𝔠`; R1 not used.
- `baSTKfargL_holds` (l.310) = merged `baEMn2ExpHK` (`EMn2BA:637`). `baCltRepg_holds` (l.316): definitional plus Hermiticity of `g₀Ψ`. `baCltInvg_holds` (l.340): `Ψ = Ψ^(B) ⊗ I`, `Adj` is invariant under `neg` and `addRight` (l.325).
- `baSTKpropsg_holds` (l.456): translation = `baK_translate` (`KSolve:591`) with `BAKsol` solving `IsKLoopS` through `baKcac_isKLoopS` (l.362); reflection written here (l.388-428: `MB(-x,-y) = MB(x,y)`, `Mss(-a,-b) = Mss(a,b)`, `Θ(-a,-b) = Θ(a,b)` by the submatrix argument, `(ΘMss)(-a,-b) = (ΘMss)(a,b)`); `(Kn2sol)` for `BAKsol` at every `g` is l.373 (`baKsol_two` without `0 < g`: `baK_unique` + `BAKcac_spliced`); size clause from the decay of `STThPropsg` at `s`, `meanFar_T1` (regime `STReg5I`) and the unit column sum `Σ_c |M^(σσ')_cb| = 1` (l.430).
- Crossing (g), UBA-C1: `withLam` occurs only in `seqP (… .withLam 0)`; the comparison is R1 through `TwistStep2_lam0_sq` (l.83), both conjuncts (`g₀ ≤ g` for `ℓ_t(g₀) ≤ ℓ_t(g)`, `EMn2BA_ellT_mono_g`, and `g² ≤ A g₀²`).
- `∀ n` clauses at indices with `g₀ n ≤ 0` (fill-in (vi)): `κ' ≤ Im m_F` (`BAflow_real`, every `n`), Ward row (`BASelf` only), `CltRepg`, `CltInvg`, `STExpInvgL` (every `n`), invariance of `𝒦^(2)` (`baKcac_isKLoopS`, `BAReal` only; `Θ`, `Mss` identities unconditional). No clause needs `0 < g₀`; `0 < g₀ ≤ 𝔡⁻¹` is used only inside `∀ᶠ n` clauses (`BAflow_lam0_window`). Stop rules: none triggered.
- A9 (fill-in (vii)) and the other targets of the ticket belong to rows a1/b; not touched. Lines: 778 against the bottom-up 790 and the stop line 1,200 (row a2).
- No sorry/admit/axiom/native_decide; axioms of the 7 public declarations: the standard three (build output above).

## (c) Verified Mathlib names (each compiled in `CltFlowBA.lean`)
`Real.exp_nat_mul`, `Real.exp_neg`, `Real.exp_log`, `Real.exp_add`, `Real.exp_le_exp`, `Real.rpow_def_of_pos`, `Real.rpow_add`, `Real.rpow_pos_of_pos`, `Real.sqrt_le_iff`, `Real.tendsto_log_atTop`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`.
`Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.mul_apply`, `Matrix.kroneckerMap_apply`, `Matrix.conjTranspose_apply`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.submatrix_apply`.
`Equiv.sum_comp`, `Fintype.sum_equiv`, `Fintype.sum_prod_type`, `Finset.sum_ite_eq'`, `Finset.sum_le_sum`, `Finset.mul_sum`, `Equiv.neg_apply`, `Equiv.coe_addRight`.
`sq_le_sq₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `div_le_div_iff₀`, `div_le_div_of_nonneg_left`, `le_div_iff₀`, `div_le_iff₀`, `div_le_self`, `norm_sum_le`, `neg_inj`, `mul_nonpos_of_nonneg_of_nonpos`, `le_mul_of_one_le_left`, `le_mul_of_one_le_right`.
Deprecated here (replaced): `push_neg` (used `not_lt.1`), `if_true` (used `ite_true`).

## (d) Open issues and paper-delta candidates
- Paper deltas: none proposed. The Lean statements are the merged class and pin texts; the producers carry the hypotheses `3 ≤ d`, `0 < κ`, `0 < 𝔡` (and `0 < ε` for `STKfargL`) and the regime `STReg5I` for `STKpropsg`; no premise beyond the family table.
- T2501a2a (ticket text, not a statement): the UBA-C1 table says crossing (g) is "R1's `lam² ≤ A g₀²` only"; the proof also uses `g₀² ≤ lam²` (the first R1 conjunct), which is in the R1 text of the check (`0 ≤ g₀·lam ∧ g₀² ≤ lam² ∧ lam² ≤ A g₀²`).
- Row b (target 12) cannot use `flow_sz0` or `half_lt_t0` for cases (i), (ii) (empty window, (a) row 13). The datum (B) of this file is `private` (4 `private def` lines; the public-`def` grep is 0); row b needs its own datum or a dispatcher decision to publish one.
- The branch carries two commits (`74574b10` WIP, `3f8e9624` final); the merge takes the three files by name.
