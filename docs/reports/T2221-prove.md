Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:51:23 UTC 2026
Notation: `B := (1-u_k)^{-1} ≥ 1`; `‖·‖` the `∞→∞` operator norm / sup norm of 2-index tensors; `Δ`; `𝒰_{v,w} = Ugen = UN`; `X_j := 𝒰_{u_j,u_{j+1}}`; `W_j := 𝒰_{j+1,k} - 𝒰_{j,k}`; `Θ_v := ThetaN … v`. No external hypothesis occurs in any target (all five are deterministic, per `n`, per sample), so no limit computation is needed.

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 0 | consumer check, hyp. of target 4 vs `STGridRepNAt` conj. 1 (`Step2Defs.lean`, def at `:817`) | `A j b = STgAN … (σ,b) j ω`, `ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) (gridTime … k) (fun a' => STgAN … a' k ω)` is the first summand of `STgDriftN` (`:784`), `F j b = STelklkM + STegtM` (the `Σ_{l∈Icc 3 2}` term is an empty sum, `+0` by `simp`, not `rfl`) | conj. 1 is `∀ᵐ ω, ∀ k ≤ K n` for one label `i`; target 4 needs all labels `b` at once: `Fin 2 → Zd d L` finite, `ae_all_iff` | none needed |
| 0′ | martingale sum vs conj. 4 | target 4: `Ugen d L g E σ (u j) (u k) (fun b => Mart (j+1) b - Mart j b) a`; conj. 4: `UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i')) (gridTime … j) (gridTime … k) (fun b => Mart n (i.1,b) (j+1) ω - Mart n (i.1,b) j ω) i.2` | `Ugen := UN d L g (fun i => mSigma E (σ i))` (`GridDuhamelN.lean:65-67`): `rfl`; same argument order `(u_j, u_k)`, no index shift | exact |
| 0″ | grid shape | `gridTime s t K n j = s n + j * gridStep s t K n` for **all** `j` (`Walk.lean:70`), `gridStep = (t-s)/K` | pin needs `u(j+1)=u j+Δ ∀ j` (`ring`), `0 ≤ u 0 = s n`, `0 ≤ Δ` (`s ≤ t`, any `K`), `u k < 1` | exact |
| 0‴ | `|E| ≤ 2` for `E = STflowE z n = lemE (z n) = -2 Re msc / ‖msc‖` (`Semicircle.lean:190`) | `|Re m| ≤ ‖m‖` | needed by `norm_mSigma` (`:87`) and `GridDuhamelN_Ugen_self/_comp` | S5-11b input, not this ticket |
| 0⁗ | `J♯` vs `LemDecCalELip_Jsharp` (`:925`) | same `max 1 (univ.sup' ⟨((fun _ => true),(fun _ => 0)), _⟩ (fun p => · / STtailTD sz n u D p.2))`; numerator `STLK2 = ‖Lloop … - STKloop …‖` (`Step5Pins.lean:143`) vs `‖STLKM sz n E u H p.1 p.2‖`, `STLKM = STLM - STKloop` (`Step2Defs.lean:68`), `STLM_seqHflow` is `rfl` (`:64`) | target 2 closes by `unfold; rfl` | exact |
| 0⁵ | `PfStep5Grid_stopIdx` vs `STstopIdx` (`Step2Defs.lean:544`) | both `firstHit (fun j ω => F_j (pathH … j ω)) θ (K n)`; here `F_j H = JsharpM sz n (E n) (level W Dst (gridTime j)) (gridTime j) H`, `θ = W^ε` | `isStoppingTime_firstHit_grid` needs `∀ j, Measurable (F_j)` (`Stop.lean:175`) | — |
| 1 | `D_u := D* + 2 log(1-u)/log W` (`PfStep5Grid_level`) | `W^{-D_{u'}} = exp(-D* log W - 2 log(1-u')) = (1-u')^{-2} W^{-D*}` (`u'<1`, `W>1`) | target 1 conj. 1 | exact identity |
| 2 | monotone, `u ≤ u'<1` | `1-u' ≤ 1-u`, both `>0`, `log` monotone, `log W>0` | conj. 2 | exact (equality at `u=u'`) |
| 3 | `0 ≤ u ≤ u' < 1` ⇒ `D_u ≤ D*` | `log(1-u) ≤ 0` since `0<1-u ≤ 1` (`u ≥ 0`; `1-u>0` from `u ≤ u'<1`) | conj. 3 | `D* - D_u = -2 log(1-u)/log W` |
| 4 | `D_{u'} ≥ D* - 2d` | `W^{-d} ≤ 1-u'` ⇒ `log(1-u') ≥ -d log W` | conj. 4 | zero at `1-u' = W^{-d}` (attained at `W=32, d=3, u'=1-2^{-15}`: `D_{u'} = 49 = D* - 6`, script 1) |
| 5 | one-slot, `0≤v≤w≤u_k`, `‖μ‖=1`, `θ_w = thetaKer μ w` | `u_{v,w} = 1 + (w-v)θ_w` (`uKer_eq_one_add`, `hξ: ‖wμ‖<1`); `‖θ_w‖ ≤ ‖SB‖‖Θ_w‖ ≤ B` (`norm_SB = 1`, `norm_Theta_le`); `‖u_{v,w}‖ ≤ (1-v)/(1-w) ≤ B` (`norm_uKer_le`); `Θ_w - Θ_v = (w-v) μ Θ_w SB Θ_v` (resolvent identity from `Theta = (1-ξ SB)^{-1}`, `Basic.lean:70`, and `mul_Theta_of_three_le`) ⇒ `‖θ_w-θ_v‖ ≤ (w-v)B²`, `‖u_{v,w}-1-(w-v)θ_v‖ = (w-v)‖θ_w-θ_v‖ ≤ (w-v)²B²` | — | max numeric ratio 0.978 (script 3) |
| 6 | two slots (`Ugen` = product of slot kernels, `ThetaN` = sum of the two slot operators), `‖P⊗Q‖ ≤ ‖P‖‖Q‖` (row sums multiply) | `‖𝒰_{v,w}‖ ≤ B²` (`norm_UN_le`, `(1-v)/(1-w) ≤ B` for `v ≥ 0`, `w ≤ u_k`); `‖𝒰-1‖ ≤ Δ_{vw}B(B+1) ≤ 2Δ_{vw}B²` from `X_1⊗X_2 - 1 = (X_1-1)⊗X_2 + 1⊗(X_2-1)`; `𝒰-1-Δ_{vw}Θ_v = Δ_{vw}[(θ_w-θ_v)⊗1 + 1⊗(θ_w-θ_v)] + Δ_{vw}²θ_w⊗θ_w`, norm `≤ 3Δ_{vw}²B²` (**ticket states `B³`; `B²` is true and stronger, `B ≥ 1`**); `‖Θ_v‖ ≤ 2B`; `‖Θ_v-Θ_w‖ ≤ 2Δ_{vw}B²` | ticket's bounds | max ratios 0.92, 0.95, 0.986, 0.98, 0.98 (script 3) |
| 7 | telescope | `𝒰_{j,k}(A_{j+1}-A_j) + (𝒰_{j+1,k}-𝒰_{j,k})A_{j+1} = 𝒰_{j+1,k}A_{j+1} - 𝒰_{j,k}A_j` (semigroup `GridDuhamelN_Ugen_comp`, `𝒰_{j,k}=𝒰_{j+1,k}X_j`); sum over `j<k` = `A_k - 𝒰_{0,k}A_0` (`Ugen_self`, `Ugen_add`). Inserting `A_{j+1}-A_j = Δ(Θ_jA_j+F_j) + ΔRem_j + ΔMart_j` (hyp. at `j+1` minus at `j`) gives LHS of pin `= Σ_j 𝒰_{j,k}ΔRem_j + Σ_j T2_j`, `T2_j = Δ𝒰_{j,k}Θ_jA_j + W_jA_{j+1}` | `u_j<1`, `0 ≤ u_j` for `j ≤ k` | exact identity |
| 8 | remainder `S_R = Σ_{j<k}𝒰_{j,k}ΔRem_j` | Abel: `𝒰_{k-1,k}Rem_k - 𝒰_{0,k}Rem_0 + Σ_{j=1}^{k-1}(𝒰_{j-1,k}-𝒰_{j,k})Rem_j`, `𝒰_{j-1,k}-𝒰_{j,k} = 𝒰_{j,k}(𝒰_{j-1,j}-1)`: `≤ 2B²R + (k-1)·2ΔB⁴R ≤ 4B⁴R` (`kΔ = u_k-u_0 < 1`) | constant `4` | `2B²R + 2B⁴R ≤ 4B⁴R`: slack `2B²(B²-1)R` |
| 9 | drift mismatch, first two parts | `T2_j = 𝒰_{j+1,k}[(ΔΘ_j + 1 - X_j)A_j + Δ(X_j-1)Θ_jA_j] + W_j(A_{j+1}-A_j)` (identity by `𝒰_{j,k}=𝒰_{j+1,k}X_j`, `W_j = 𝒰_{j+1,k}(1-X_j)`); `‖·‖ ≤ B²(3Δ²B²M + Δ·2ΔB²·2BM) = B²(3Δ²B²+4Δ²B³)M ≤ 7Δ²B⁵M`; sum over `j<k`: `≤ 7ΔB⁵M` | constant `7` | uses rows 5-6 with `v=u_j, w=u_{j+1}` |
| 10 | last part `Σ_{j<k}W_j(A_{j+1}-A_j)` | Abel: `W_{k-1}A_k - W_0A_0 - Σ_{j=1}^{k-1}(W_j-W_{j-1})A_j`; `‖W_j‖ ≤ B²·2ΔB² = 2ΔB⁴`; `W_j-W_{j-1} = 𝒰_{j+1,k}(1-2X_j+X_jX_{j-1})`, `1-2X_j+X_jX_{j-1} = (1-X_j)² + X_j(X_{j-1}-X_j)`, `‖X_{j-1}-X_j‖ ≤ Δ‖Θ_{j-1}-Θ_j‖ + 3Δ²B²·2 ≤ 8Δ²B²` (equal steps), so `‖W_j-W_{j-1}‖ ≤ B²(4Δ²B⁴ + 8Δ²B⁴) = 12Δ²B⁶ ≤ 12Δ²B⁷`; total `≤ 4ΔB⁴M + 12ΔB⁷M ≤ 16ΔB⁷M` | constants `12`, `16` | no increment bound on `A_{j+1}-A_j` used |
| 11 | total | `4B⁴R + 7ΔB⁵M + 16ΔB⁷M ≤ 4B⁴R + 23ΔB⁷M ≤ 64B⁷(R+ΔM)` | pin constant `64` | `64 - 23 = 41` on `ΔM`, `64-4 = 60` on `R` (as `B ≥ 1`); measured max ratio 0.42 vs `4B⁴R+23ΔB⁷M`, 0.041 vs the pin (script 2) |
| 12 | `M, R ≥ 0` | not hypotheses of the pin; `‖A 0 b‖ ≤ M`, `‖Rem 0 b‖ ≤ R` at an existing `b` (`Fin 2 → Zd d L` inhabited, `NeZero L`) give them | `k = 0`: LHS `= A_0 - 𝒰_{0,0}A_0 = 0` (`Ugen_self`) | — |
| 13 | S5-11b dependency (recorded, not proved here) | pin needs `‖A_j b‖ ≤ M` for **all** `j ≤ k`, including `j = k = T` where the stopping bound `J♯ < W^ε` (target 3b) holds only for `j < T`; so `M` must be an a priori deterministic loop bound; `R = N^{C₀}Δ^{1/2}` (conj. 2), `ΔM` small by `K ≥ N^{C_K}` | `B ≤ lam^{-2}` (polynomial in `W`) absorbed by `W^{-D*}` | S5-11b's sketch (report T2209 (a) "(3) Consumer chain") is consistent with the shape `64B⁷(R+ΔM)` |

### (ii) One concrete nondegenerate instance
Scripts are Python in `<scratchpad>/T2221/` (no Lean). Dense matrices: `SB = circulant(sbKernel)` (`Block.lean:34-44`) on `Zd 3 4` (64 points), `Theta = (1-ξ SB)^{-1}`, `thetaKer μ t = μ SB Θ_{tμ}`, `uKer μ s t = (1 - sμ SB)Θ_{tμ}`, `cycProd` with `finRotate 2` the swap, `mE E = (-E + √(4-E²) i)/2`.

**Target 1** at `d=3, W=32, D*=55`; `u,u' ∈ {0, 1/16, 1-2^{-15}}` (`W^{-d} = 2^{-15}`). Script 1: `python3 t1.py`
```
u=0 u'=0  D_u=55.000000 D_u'=55.000000  c1..c4=(True, True, True, True)  W^-d<=1-u': True
u=0 u'=0.0625  D_u=55.000000 D_u'=54.962756  c1..c4=(True, True, True, True)  W^-d<=1-u': True
u=0 u'=0.99996948  D_u=55.000000 D_u'=49.000000  c1..c4=(True, True, True, True)  W^-d<=1-u': True
u=0.0625 u'=0.0625  D_u=54.962756 D_u'=54.962756  c1..c4=(True, True, True, True)  W^-d<=1-u': True
u=0.0625 u'=0.99996948  D_u=54.962756 D_u'=49.000000  c1..c4=(True, True, True, True)  W^-d<=1-u': True
u=0.999969 u'=0.99996948  D_u=49.000000 D_u'=49.000000  c1..c4=(True, True, True, True)  W^-d<=1-u': True
instance u=0,u'=1/16: W^{-D_u'} = 1.8741685232409819065508576091146700458151042457542e-83  (16/15)^2*32^-55 = 1.8741685232409819065508576091146700458151042457544e-83
ALL OK: True
```
**Targets 2, 3a, 3b** at `SizesInst.sz0`, `n=0` (`L=4, W=32, lam=1/64` by `sz0_values`, `Defs/Sizes.lean:260-270`), `s=0, t=1/16, K≡8, D*=55, ε=1/50`. Script 4: `python3 t3.py`
```
W^eps = 1.0717734625362931  Delta = 0.0078125  lam^2 = 1/4096 <= 1-t = 0.9375
j=0: u_j=0.000000  D_u=55.000000  1-u_j>=W^-3: True
j=1: u_j=0.007812  D_u=54.995474  1-u_j>=W^-3: True
j=8: u_j=0.062500  D_u=54.962756  1-u_j>=W^-3: True
```
Targets 2, 3a have no hypotheses beyond the data. Target 3b at `j=0` keeps the hypothesis `0 < T(ω)` (as the ticket allows). Facts from the files: `pathH sz s t K n 0 ω = (√(s n))•X_0 + √Δ•Σ_{Icc 1 0} = 0` since `s = 0` (`Walk.lean:75-77`), so `H_0 = 0` for every `ω` and `0 < T(ω)` means the `ω`-independent inequality `J♯(0, D_0)(0) < W^{1/50}` (`W^{1/50} = 1.0718 > 1`). At `u = 0`: `zt E 0 = E + mE E` (`Semicircle.lean:179`), `kTwo` has `Theta_0 = 1` (`Primitive.lean:46-52`, `Theta_zero`), so `𝒦^{(2)}_{0,σ,a} = W^{-d} m₁m₂ δ_{a₁a₂}`; that `𝓛^{(2)}(H=0) = 𝒦^{(2)}_0` (i.e. `J♯ = 1`) I have not verified from `Gres`/`Eblk`: stage 1b either proves it or keeps `0<T(ω)` as a hypothesis of the example.

**Target 4** at `d=3, L=4, g=1/64, E=0, σ=(+,-)` (`μ = i·(-i) = 1`), `u j = j/48`, `k=3` (`Δ=1/48`, `u_3=1/16<1`, `B=16/15`), `A≡0, F≡0`, `Rem j = j/10`, `Mart j = -j/10` (constant tensors), `M=0, R=3/10`. Every hypothesis is asserted in the script (`|E|≤2`, `0≤Δ`, `0≤u 0`, equal steps, `‖Rem j‖ ≤ R` for `j ≤ 3`, `‖A j‖ ≤ M`, and the additive hypothesis `A j = A 0 + ΔΣ(Θ_iA_i+F_i)+Rem j+Mart j` holds identically). Conclusion LHS `= ‖Σ_j 𝒰_{j,3}(1/10)‖ = (1/10)Σ_{j<3}((48-j)/45)²` (constants are fixed by the slot kernels: `(1-v)/(1-w)` per slot at `μ=1`). Script 2b: `python3 t4inst.py`
```
mu = [np.complex128(1+0j), np.complex128(1+0j)]  B = 1.0666666666666667 (16/15 = 1.0666666666666667 )
LHS (dense, max entry) = 0.3273580246913581  exact (1/10)(48^2+47^2+46^2)/45^2 = 0.32735802469135805
RHS 64 (16/15)^7 (3/10) = 30.164928059698212  LHS<=RHS: True
```
**Truth of target 4 on random data** (not only the instance): random `A, F, Rem` (and alternating-sign worst cases for the Abel sums), `Mart` defined by the identity, `E ∈ {0, 1.3, -1.9, 2}` with several `σ`, `k ∈ {0,1,3,5,8,12}`, `u_k` up to `1-2^{-3}`, `u_0 ∈ {0, 1/48, 0.1, 0.2, 0.5}`. Script 2: `python3 t4.py`
```
n = 64  row sums of S in [1.000000000000, 1.000000000000]; ||S||_inf = 0.9999999999999999
cases: 280  max LHS/(64 B^7 (R+Dl M)) = 0.041150119816905015  max LHS/(4B^4 R + 23 Dl B^7 M) = 0.42163705809693713
```
**Truth of rows 5-10** with the full `4096×4096` two-slot operators (`kron`), `g ∈ {1/64, 1}`, `E,σ ∈ {(0,(+,-)), (1.3,(+,+)), (-1.9,(-,+))}`, `(u_k,k) ∈ {(1/16,3),(0.9,6),(15/16,5)}`; each line is `max(norm / claimed bound)` (must be `≤ 1`). Script 3: `python3 t4b.py`
```
1slot ||u-1-(w-v)th_v||/((w-v)^2 B^2)                        max = 0.978261
1slot ||th_w-th_v||/((w-v)B^2)                               max = 0.978261
1slot ||u_vw||/B                                             max = 0.958333
2slot ||U_vw||/B^2                                           max = 0.918403
2slot ||U-1||/(2 D B^2)                                      max = 0.947917
2slot ||U-1-D Th_v||/(3 D^2 B^2)                             max = 0.985507
2slot ||Th_v||/(2B)                                          max = 0.978261
2slot ||Th_v-Th_w||/(2 D B^2)                                max = 0.978261
||W_j||/(2 D B^4)                                            max = 0.85144
||W_j-W_{j-1}||/(12 D^2 B^7)                                 max = 0.120699
||X_{j-1}-X_j||/(8 D^2 B^2)                                  max = 0.249941
identity check |W_j-W_{j-1}-U_{j+1,k}(1-2X_j+X_jX_{j-1})|    max = 7.80313e-12
```

### Verdicts
- Target 1 (`pfStep5Grid_level`): PASS. Target 2 (`pfStep5Grid_Jsharp`): PASS (`rfl` after unfolding). Target 3a (`pfStep5Grid_stop`): PASS. Target 3b (`pfStep5Grid_below`): PASS (`lt_firstHit_imp`; instance keeps `0<T(ω)` as ticket allows, see the note above).
- Target 4 (`pfStep5Grid_duhamel`): PASS: the statement is true with constants `4`, `7`, `12`, `16` (`23` in total) against `64`; hypotheses (rows 0-0‴) match `STGridRepNAt` conjuncts 1 and 4 token for token. The two-slot remainder bound in the ticket (`3(w-v)²B³`) holds with `B²`; no change of any statement. One input of S5-11b noted in row 13 (a priori `M` at `j = k`), not a defect of this ticket.
- Ticket verdict: PASS.

## (b) Script output
Paths: `T=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2221` (scratch scripts), `F=RBM3D/Induction/PfStep5Grid.lean` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2221`).
**B1 branch, size** (Mon Oct  5 23:26:30 UTC 2026)
```
$ git log --oneline -3; git diff --stat main...t/T2221; wc -l $F | cut -d' ' -f1-5
2232c1c T2221: consumer check of target 4 against STGridRepNAt, docstring
2aae25b T2221: instance of target 3b with the stopping-index hypothesis discharged (H = 0, u = 0)
e9f3bbb T2221: S5-11a Induction/PfStep5Grid (level, J-sharp, grid stopping index, Duhamel form)
 RBM3D/Induction/PfStep5Grid.lean | 1292 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 1292 insertions(+)
    1292
```
**B2 module build** (`lake build RBM3D.Induction.PfStep5Grid > $T/build_final.out`, started Mon Oct  5 23:20:02 UTC 2026, after the last edit of $F)
```
$ tail -2 $T/build_final.out; grep -c 'warning: RBM3D/Induction/PfStep5Grid' $T/build_final.out
✔ [3847/3847] Built RBM3D.Induction.PfStep5Grid (9.4s)
Build completed successfully (3847 jobs).
0
```
**B3 axioms** (`#print axioms` of the 5 targets and the 6 instances, `lake env lean $T/axioms.lean`)
```
$ lake env lean $T/axioms.lean | sed -e 's/^.RBM.Gauss.Sizes.//' -e "s/' depends on axioms:.*//" | paste -sd' ' -; lake env lean $T/axioms.lean | sed 's/.*depends on axioms: //' | sort | uniq -c
pfStep5Grid_level pfStep5Grid_Jsharp pfStep5Grid_stop pfStep5Grid_below pfStep5Grid_duhamel pfStep5Grid_inst_level pfStep5Grid_inst_Jsharp pfStep5Grid_inst_stop pfStep5Grid_inst_below pfStep5Grid_inst_duhamel pfStep5Grid_inst_below_flow
  11 [propext, Classical.choice, Quot.sound]
```
**B4 hygiene** (forbidden tokens; line numbers of the public declarations)
```
$ grep -c 'sorry\|admit\|native_decide\|^axiom' $F; grep -nE '^(noncomputable )?(theorem|def|abbrev|instance)' $F | sed 's/:.*//' | paste -sd' ' -
0
71 76 85 97 106 112 118 130 149 191 213 222 892 1137 1150 1157 1169 1184 1210
```
**B5 vocabulary and the five pins against the check file** (`diff`, empty = identical)
```
$ diff <(sed -n 35,110p /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2221-check.lean) <(sed -n "$(grep -n '^/-! ## 0. Vocabulary' $F | cut -d: -f1),$(( $(grep -n '^/-! ## 2. Targets 1-3b' $F | cut -d: -f1) - 1 ))p" $F); echo "diff exit: $?"
diff exit: 0
```
**B6 the five target theorems** (statement = the pin; theorem lines and pin bodies extracted by script)
```
$ grep '^theorem pfStep5Grid_\(level\|Jsharp\|stop\|below\|duhamel\) ' $F | sed 's/ := by//'; awk '/^def PfStep5Grid_[A-Za-z]*_pin/{p=1} /^$/{p=0} p' $F
theorem pfStep5Grid_level : PfStep5Grid_level_pin
theorem pfStep5Grid_Jsharp {d : ℕ} (sz : Sizes d) : PfStep5Grid_Jsharp_pin sz
theorem pfStep5Grid_stop {d : ℕ} (sz : Sizes d) : PfStep5Grid_stop_pin sz
theorem pfStep5Grid_below {d : ℕ} (sz : Sizes d) : PfStep5Grid_below_pin sz
theorem pfStep5Grid_duhamel (d : ℕ) : PfStep5Grid_duhamel_pin d
def PfStep5Grid_level_pin : Prop :=
  ∀ (d : ℕ) (W Dst u u' : ℝ), 1 < W → u ≤ u' → u' < 1 →
    W ^ (-(PfStep5Grid_level W Dst u')) = ((1 - u')⁻¹) ^ 2 * W ^ (-Dst) ∧
    PfStep5Grid_level W Dst u' ≤ PfStep5Grid_level W Dst u ∧
    (0 ≤ u → PfStep5Grid_level W Dst u ≤ Dst) ∧
    (W ^ (-(d : ℝ)) ≤ 1 - u' → Dst - 2 * (d : ℝ) ≤ PfStep5Grid_level W Dst u')
def PfStep5Grid_Jsharp_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ),
    LemDecCalELip_Jsharp sz E D n u ω = PfStep5Grid_JsharpM sz n (E n) D u (sz.seqHflow n u ω)
def PfStep5Grid_stop_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (Dst ε : ℝ) (n : ℕ),
    IsStoppingTime (filt sz) (fun ω => (PfStep5Grid_stopIdx sz s t K E Dst ε n ω : ℕ))
def PfStep5Grid_below_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (Dst ε : ℝ) (n j : ℕ) (ω : PathΩ sz),
    j < PfStep5Grid_stopIdx sz s t K E Dst ε n ω →
      PfStep5Grid_JsharpM sz n (E n) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s t K n j))
          (gridTime s t K n j) (pathH sz s t K n j ω) <
        ((sz.W n : ℕ) : ℝ) ^ ε
def PfStep5Grid_duhamel_pin (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d L) → ℂ),
    |E| ≤ 2 → 0 ≤ Δ → 0 ≤ u 0 → (∀ j, u (j + 1) = u j + Δ) → u k < 1 →
    (∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) → (∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R) →
    (∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (ThetaN d L g (fun i' => mSigma E (σ i')) (u i) (A i) b + F i b) + Rem j b + Mart j b) →
    ∀ a, ‖A k a - RBM.Ind.Ugen d L g E σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k,
          RBM.Ind.Ugen d L g E σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)
```
**B7 the compiled nonempty instances** (statements extracted by script, proofs omitted; `below_flow`: first 3 lines)
```
$ awk '/^theorem pfStep5Grid_inst_/{p=1;c=0;fl=($0 ~ /below_flow/)} p{c++; if(!(fl&&c>3)) print} p&&/:=( by)?$/{p=0}' $F
theorem pfStep5Grid_inst_level :
    (32 : ℝ) ^ (-(PfStep5Grid_level 32 55 (1 / 16))) = (16 / 15 : ℝ) ^ 2 * (32 : ℝ) ^ (-(55 : ℝ)) ∧
      PfStep5Grid_level 32 55 (1 / 16) ≤ PfStep5Grid_level 32 55 0 ∧
      PfStep5Grid_level 32 55 0 ≤ 55 ∧
      (55 : ℝ) - 2 * ((3 : ℕ) : ℝ) ≤ PfStep5Grid_level 32 55 (1 / 16) := by
theorem pfStep5Grid_inst_Jsharp :
    LemDecCalELip_Jsharp sz0 (STflowE z0) 55 0 (1 / 16) (fun _ => 0) =
      PfStep5Grid_JsharpM sz0 0 (STflowE z0 0) 55 (1 / 16) (sz0.seqHflow 0 (1 / 16) (fun _ => 0)) :=
theorem pfStep5Grid_inst_stop :
    IsStoppingTime (filt sz0)
        (fun ω => (PfStep5Grid_stopIdx sz0 (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8)
          (STflowE z0) 55 (1 / 50) 0 ω : ℕ)) ∧
      gridStep (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 = 1 / 128 := by
theorem pfStep5Grid_inst_below_flow
    (h : 0 < PfStep5Grid_stopIdx sz0 (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8)
      (STflowE z0) 55 (1 / 50) 0 (fun _ _ => 0)) :
theorem pfStep5Grid_inst_duhamel (a : Fin 2 → Zd 3 4) :
    ‖(fun _ : Fin 2 → Zd 3 4 => (0 : ℂ)) a -
        RBM.Ind.Ugen 3 4 (1 / 64) 0 ![true, false] (((0 : ℕ) : ℝ) / 48) (((3 : ℕ) : ℝ) / 48)
          (fun _ => 0) a -
        ∑ j ∈ Finset.range 3, ((1 / 48 : ℝ) : ℂ) *
          RBM.Ind.Ugen 3 4 (1 / 64) 0 ![true, false] (((j : ℕ) : ℝ) / 48) (((3 : ℕ) : ℝ) / 48)
            (fun _ => 0) a -
        ∑ j ∈ Finset.range 3,
          RBM.Ind.Ugen 3 4 (1 / 64) 0 ![true, false] (((j : ℕ) : ℝ) / 48) (((3 : ℕ) : ℝ) / 48)
            (fun _ => -(((j + 1 : ℕ) : ℂ) / 10) - -(((j : ℕ) : ℂ) / 10)) a‖ ≤
      64 * (((1 - ((3 : ℕ) : ℝ) / 48)⁻¹) ^ 7) * (3 / 10 + 1 / 48 * 0) := by
theorem pfStep5Grid_inst_below :
    0 < PfStep5Grid_stopIdx sz0 (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8) (fun _ => 0) 55
      (1 / 50) 0 (fun _ _ => 0) ∧
    PfStep5Grid_JsharpM sz0 0 0
        (PfStep5Grid_level ((sz0.W 0 : ℕ) : ℝ) 55
          (gridTime (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8) 0 0))
        (gridTime (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8) 0 0)
        (pathH sz0 (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8) 0 0 (fun _ _ => 0)) <
      ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 50 : ℝ) := by
```
**B8 name clash, registry pre-check, full build**
```
$ (cd /Users/junyin/Lean_proof/RBM3D && grep -rn 'PfStep5Grid\|pfStep5Grid' RBM3D RBM3D.lean | wc -l); lake env lean $T/registry.lean > $T/registry.out 2>&1; echo "registry exit: $?"; head -1 $T/registry.out | cut -c1-90; grep -c 'pfStep5Grid\|PfStep5Grid' $T/registry.out; lake build > $T/fullbuild.out 2>&1; echo "lake build exit: $?"; tail -1 $T/fullbuild.out
       0
registry exit: 0
axiom audit: 6526 theorems, 2243 definitions, 0 axioms in `RBM` (compiler-generated declar
0
lake build exit: 0
Build completed successfully (4025 jobs).
```
**B9 consumer check** (the `example` at the end of section 6, compiled in B2; first 5 lines) and ports (none from RBM1D/RBM2D; private text copied from RBM3D)
```
$ sed -n '/^example {d : ℕ} (sz : Sizes d) (s t/,$p' $F | head -5; git log -1 --format='RBM3D/Path/LemDecCalE.lean (copied lines 1204-1317) last commit %h' -- RBM3D/Path/LemDecCalE.lean
example {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E M R : ℝ)
    (Rem Mart : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    (σ : Fin 2 → Bool) (hE : |E| ≤ 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (k : ℕ)
    (hk : gridTime s t K n k < 1)
    (hω : ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), ∀ j, j ≤ k →
RBM3D/Path/LemDecCalE.lean (copied lines 1204-1317) last commit 6e63fbc
```

**Narrative (b)** (stage 1b started at the first `date -u` of the session, Mon Oct  5 22:52:32 UTC 2026)
1. The five targets are proved with the pins of the check file verbatim: B5 diff empty, each theorem's type is its pin (B6); no hypothesis added, no signature changed. One new file, 1292 lines (ticket estimate 700/950/1250, stop rule 1500); imports exactly the three of the ticket; public names exactly B4; every helper `private` with prefix `pfStep5Grid_`. No registry line (B8: pre-check exit 0, 0 hits).
2. **Preflight line (0), consumer check** (B9): the `example` at the end of section 6 derives the hypothesis of target 4 from conjunct 1 of `STGridRepNAt` at `m = 2` (`A_j b = STgAN`, `F_j b = STelklkM + STegtM`, `Rem`, `Mart`; the `Σ_{l ∈ Icc 3 2}` term of `STgDriftN` is an empty sum, closed by `Finset.Icc_eq_empty_of_lt`, not by `rfl`; the `ThetaN` term and the martingale sum `UN … (fun i' => mSigma E (σ i'))` of conjunct 4 are `Ugen` by `rfl`) and concludes the bound of target 4 at `u = gridTime s t K n`, `Δ = gridStep s t K n`. It needs `|E| ≤ 2`, `0 ≤ s n ≤ t n`, `gridTime … k < 1`, and `|A_j b| ≤ M`, `|Rem_j b| ≤ R` for all `j ≤ k` including `j = k` ((a) row 13: S5-11b supplies these).
3. Targets 1-3b: target 1 by `Real.rpow_def_of_pos`, `Real.exp_log`, `Real.log_le_log`, `Real.log_nonpos`; target 2 by `unfold; rfl`; 3a by `isStoppingTime_firstHit_grid` with the measurability of `J♯` in `H` (`STLKM_measurable`, `Finset.measurable_sup'`, `Measurable.max`); 3b by `lt_firstHit_imp`.
4. Target 4 (route in the file docstring; no port). Generic lemma `pfStep5Grid_abs` on `E →L[ℂ] E` (any normed ℂ-space `E`): telescope with `P_k = 1`, per-term identity (`pfStep5Grid_term`), summation by parts (`pfStep5Grid_abel`) for the remainder and for `Σ ΔP_j ΔA_j`; proved bounds `‖ΔP_j‖ ≤ 3ΔB⁴`, `‖P_{j+2} - 2P_{j+1} + P_j‖ ≤ 17Δ²B⁶`, the three sums `≤ 5B⁴R`, `9ΔB⁵M`, `23ΔB⁶M`, total `≤ 64B⁷(R + ΔM)`. Kernel input: slot operators `pfStep5Grid_slot i K` (`‖·‖ ≤ ‖K‖`), `Ugen = slot 0 u₀ * slot 1 u₁` (sum over `Fin 2 → Zd` through `finTwoArrowEquiv`), `ThetaN = slot 0 θ₀ + slot 1 θ₁`, `uKer = 1 + (w-v) thetaKer` (`uKer_eq_one_add`), resolvent identity `Θ_w - Θ_v = (w-v)μ Θ_w SB Θ_v` (`Theta_mul_of_three_le`, `mul_Theta_of_three_le`) giving `‖thetaKer_w - thetaKer_v‖ ≤ (w-v)B²`; semigroup law and `𝒰_{v,v} = 1` are `GridDuhamelN_Ugen_comp`, `_self`. `‖𝒰-1‖ ≤ 3(w-v)B²` and `‖𝒰-1-(w-v)Θ_v‖ ≤ 3(w-v)²B²` are `pfStep5Grid_norm_Uc_sub_one`, `…_Tc`.
5. Differences from (a): the constants of rows 8-11 (4, 7, 12, 16) are not those of the Lean proof (5, 9, 17, 23) because `𝒰 = 1 + δΘ_w + δ²S₀S₁` gives `3(w-v)B²` where (a) row 6 gets `2(w-v)B²` from the other split; both are below the pin's 64, and the second-order bound holds with `B²` (the ticket's `B³` is weaker), as (a) says. (a) is not wrong: no (a′).
6. Instances (B7), all deterministic hypotheses discharged: 1 at `(d, W, D*, u, u') = (3, 32, 55, 0, 1/16)`; 2 at `sz0`, `n = 0`, `u = 1/16`, `ω ≡ 0`; 3a at `sz0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 8` (`Δ = 1/128`), `STflowE z0`; 4 at the ticket's data. Target 3b twice: at the flow energy with `0 < T(ω)` kept (`pfStep5Grid_inst_below_flow`, as the ticket allows) and at `E ≡ 0` with it discharged (`pfStep5Grid_inst_below`): (a)'s open point `𝓛^{(2)}(H=0) = 𝒦^{(2)}_0` is proved for `|E| ≤ 2` (`pfStep5Grid_STLKM_zero`, a private copy of `lemDecCalE_STLKM_zero_time`, section 5b), so `J♯ = 1 < 32^{1/50}` at `j = 0` and `0 < firstHit` by `MeasureTheory.hittingBtwn_le_iff_of_lt`.
7. `IsScalarTower ℂ (E →L[ℂ] E) (E →L[ℂ] E)` and `SMulCommClass` are not synthesized for `E = (Fin 2 → Zd d L) → ℂ` (error in the first draft), so `smul_mul_smul_comm` is used in a generic space (`pfStep5Grid_alg`) and instantiated.

## (c) Verified Mathlib names (every name used, `#check`ed by `lake env lean $T/names.lean`)
```
$ grep -c '^#check' $T/names.lean; grep -c error $T/names.out; grep -c deprecated $T/names.out
46
0
0
```
- `Real.`: `rpow_def_of_pos`, `exp_log`, `exp_neg`, `exp_nat_mul`, `exp_add`, `log_le_log`, `log_nonpos`, `log_pos`, `log_rpow`, `rpow_neg`, `rpow_natCast`, `one_lt_rpow`, `rpow_pos_of_pos`.
- Order and algebra: `div_le_div_of_nonneg_right`, `div_nonpos_of_nonpos_of_nonneg`, `le_div_iff₀`, `inv_anti₀`, `one_le_inv₀`, `pow_le_pow_right₀`, `mul_le_of_le_one_left`, `monotone_nat_of_le_succ`, `smul_mul_smul_comm`.
- Operators: `mul_apply_eq_comp`, `one_apply_eq_self`, `_root_.sub_apply`, `_root_.add_apply`, `_root_.smul_apply`, `ContinuousLinearMap.opNorm_le_bound`, `.le_opNorm`, `.ext`, `LinearMap.toContinuousLinearMap`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`.
- Sums, measurability, probability: `finTwoArrowEquiv`, `Fintype.sum_prod_type'`, `Fintype.sum_equiv`, `Finset.measurable_sup'`, `Finset.sup'_le`, `Finset.smul_sum`, `Finset.sum_range_succ`, `Function.update_eq_self`, `MeasureTheory.hittingBtwn_le_iff_of_lt`, `Matrix.trace_diagonal`, `Matrix.diagonal_mul_diagonal`, `Matrix.isHermitian_zero`, `Complex.norm_real`.
- Deprecated in this Mathlib (`#check` warnings of the session, "Use … instead"): `ContinuousLinearMap.sub_apply`, `.add_apply`, `.smul_apply`, `.mul_apply` (use `mul_apply_eq_comp`), `.one_apply` (use `one_apply_eq_self`), `.sum_apply`. With `open Matrix` the bare `sub_apply`, `add_apply`, `smul_apply` are ambiguous with `Matrix.*`: write `_root_.`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- **T2221a**: `(eq:def_TTT)` is a grid stopping index at the time-dependent level `D_{u_j} = D* + 2 log_W(1-u_j)` (DECISIONS §70), `PfStep5Grid_level`, `PfStep5Grid_stopIdx`, not a continuous stopping time at one `D`.
- **T2221b**: the Duhamel form `(int_K-L_ST)` (`3_5:134`) is derived from the additive grid decomposition with the explicit deterministic remainder `64(1-u_k)^{-7}(R + ΔM)`, two summations by parts, no increment bound; the martingale is weighted by `𝒰_{u_j,u_k}` as in `(alu9_STime)`. No further Lean/paper difference found (no T2221c).
- For S5-11b: `M` must bound `‖A_j‖` for all `j ≤ k`, also `j = k = T` where the stopping bound holds only for `j < T` (a priori loop bound, (a) row 13); `Rem` and `Mart` are per label `b`, a.e. in `ω` (`ae_all_iff` over the finite label set, (a) row 0); conjunct 4 is used as the right side of the martingale sum of target 4 (B9).
- Zero-time loop values at `H = 0`, `u = 0` are private lemmas in `Path/LemDecCalE.lean:1299` (`lemDecCalE_STLM_zero_time`), `Path/LemDecCalEdif.lean:1285` (`lemDecCalEdif_STLM_zero_time`) and, copied, here (section 5b); a public version would remove the copies (optional ticket).
- Process: the first draft of the report script ran `lake build` once in the main worktree (`cd` inside the script; exit 0, 4027 jobs); build products only, `git status` of tracked Lean files in the main worktree shows no change.
