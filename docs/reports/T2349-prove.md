Prover model: claude-sonnet-5-5
## (a) Math preflight — Thu Oct  8 23:05:01 UTC 2026

Targets (RBM2D `DuhamelB.lean` HEAD, ported to `d = 3`-general `sz : Sizes d`): `Duhamel_azuma_Z`, `Duhamel_azuma_Y`, `Duhamel_bddC2C_Phi`, `Duhamel_step_decomp`, `Duhamel_exists_level`, `Duhamel_Vp_le`, `Duhamel_qv_le_crude`, `Duhamel_grid_facts` (+ defs). All are deterministic or Azuma-from-merged-inputs; there is no external hypothesis (so no limit computation is needed). Sources of the formulas below: source file lines 322-361 (Z), 601-655 (Y), 668-720, 735-778, 790-810, 824-932, 934-958, 961-1018; merged `DuhamelA1.lean:955-957, 1053-1058`, `DuhamelA2.lean:166, 594-603`, `Induction/LoopC2N.lean:460-464`, `Defs/Sizes.lean:157` (`size n = (W L)^d`).

### (i) Exponent table  (`s := sz.size n = (W L)^d`, `m := I.length`, `η_u := etaT e u = (1-u)·Im mE e`, `Δ := gridStep = (t0-t1)/K`)

| quantity | value (source, d=2 → d) | constraint | slack / remark |
|---|---|---|---|
| `s` (= card Idx = card Vtx) | `(L W)^2` → `(L W)^d = sz.size n` (`Sizes.size`, `card_Idx`) | `s ≥ 1` (`W_pos`, `three_le_L`) | d-dependence enters ONLY here; at `sz0`, n=0: `s = 2097152` vs `(LW)^2 = 16384` |
| Taylor constant `C₂` (bddC2C) | `m(m+1) s η_{u_{j+1}}^{-(m+2)}` (`hermTestFunLoopN`, `LoopC2N:460-464`, same in d) | needs `0 ≤ u`, `u < 1`, `|e|<2` | `m = 0` case is trivial (constant observable: `C₂ = 0`); exponent `m+2` unchanged |
| `v = Δ/s` (Duhamelv) | `Δ/s` | `v ≥ 0` iff `Δ ≥ 0` iff `t1 n ≤ t0 n`, `K n > 0` | at the instance `v = 5.2e-9` |
| Azuma-Z proxy | `4·exp(-ε²/(4 k λ))`, `λ>0` | `ε ≥ 0`; `v ≥ 0` | exponent constants `4, 4` are `azuma_complex` output; no `d` |
| Azuma-Y proxy | `P = (‖4b‖/2)² = 4b²`; tail `4 exp(-ε²/(4 k·4b²))` | `b ≥ 0`, `k ≤ K n`, `‖T‖ ≤ b` at Hermitian base points | `Duhamel_norm_T_le` gives `b = (C₂/2) v s⁴` (exponent 4: `‖X‖ ≤ card·B = s·s`, squared; d-free in form, `s` carries `d`) |
| `Duhamel_Vp_le` constant | `32 m² Δ (s⁻¹ η_z⁻² loopMax(2m) + 2m η_{z'}^{-(2m+4)} Δ)` | `0<Im z' ≤ Im z ≤ 2 Im z' `, `Im z' ≤ 1`, `Δ ≥ 0`, `‖z'-z‖ ≤ Δ`, `M` Hermitian, `I.WF` | `32 = 8 (vGue_gradMat_le) · 4 (ratio `K'² ≤ 4 (Im z)⁻²`)`; `s` cancels: `Δ/s · s` from `shift_le` factor `((L:ℝ)W)^d` (`DuhamelA1:1058`) `= s`, via `((L:ℝ) W)^d = (size:ℝ)` (= `Sizes.size` by `push_cast`) |
| `K'` exponents in shift step | `K'^{2m}·K'^2 = K'^{2m+2}`, `a² K'^{2m+2} ≤ K'^{2m+4}` | `K' = (Im z')⁻¹ ≥ 1` (needs `Im z' ≤ 1`), `a=(Im z)⁻¹ ≤ K'` | exact equalities of exponents; no slack needed |
| `qv_crude` | `s⁻¹ η⁻² loopMax(m) ≤ η^{-(m+2)}` | `Im z > 0`, `M` Hermitian | from `loopMax_le_crude`: `loopMax ≤ (L W)^d |Im z|^{-m}`; `s⁻¹ s = 1`; exponent `2 + m` |
| dyadic level | `ℓ ≤ L₀`, `k ≤ firstHit J (2^ℓ λ₀)`, `2^ℓ λ₀ ≤ λ₀ + 2Q` | `λ₀>0`, `Q ≥ 0`, `Q < 2^{L₀} λ₀`, `k ≤ K'` | minimal `ℓ`: `2^{ℓ-1}λ₀ ≤ Q` so `2^ℓ λ₀ ≤ 2Q` (ℓ>0) or `= λ₀` (ℓ=0); slack `λ₀` |
| grid `K Δ` | `K Δ = t0 - t1` | `≤ 1` (`0 ≤ t1 ≤ t0 < 1`) | instance: `0.0439 ≤ 1`, slack 0.956 |
| `Im z_j` range | `η_{u_j}`, `u_j = t1 + jΔ` | `x⁻¹ ≤ η_{t0} ≤ Im z_j ≤ 1` for `j ≤ K` (`heta : x⁻¹ ≤ etaT e (t0 n)`) | instance `x = 10`: `x⁻¹ = η_{t0} = 1/10` (equality, exact), `Im z_j ∈ [0.1, 0.1439]` |
| `‖z_{j+1} - z_j‖` | `Δ ‖mE e‖ = Δ` (`‖mE e‖ = 1`, `|e| ≤ 2`) | equality | no slack, none needed |
| `Im z_j - Im z_{j+1}` | `Δ · Im mE ∈ [0, Δ]` | `0 ≤ ... ≤ Δ` (`Im mE ≤ 1`) | instance `Im mE = 1`, equality at the upper end |

### (ii) One concrete nondegenerate instance
Data (merged `RBM.Gauss.SizesInst.sz0`, `Defs/Sizes.lean:260`, `sz0_values`: `L 0 = 4`, `W 0 = 32`, `size 0 = 2097152`; `GridCheck` data of `Grid.lean:~795-895` / `DuhamelA2Inst`: `t0 = 9/10`, `t1 = (1 - ouZeta(1/20))·9/10 = e^{-1/20}·9/10`, `K ≡ 4`), `d = 3`, `n = 0`, `e = 0` (`mE 0 = I`, `Im = 1`, `‖·‖ = 1`), loop `I = ⟨[true,false], [(0,0,0),(1,0,0)]⟩ ∈ LoopIdx (Zd 3 4)` (`m = 2`, `I.WF`: both lists have length 2), `M = 0` (Hermitian), `j ∈ {0,1,2,3}` (`j < K 0 = 4`), `z = z_j`, `z' = z_{j+1}`; Azuma-Z: `λ = 1/100, k = 4, ε = 1`; Azuma-Y: `b = (C₂/2) v s⁴`, `k = 4`; level: `J ≡ 1/4`, `λ₀ = 1/100`, `Q = 1/2`, `L₀ = 6`, `k = 4 ≤ K' = 4`. The script mirrors every hypothesis listed in the table.

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2349/inst.py`
```
L,W,s=(W L)^d: 4 32 2097152 | (LW)^2 would be 16384
t1=0.856106 t0=0.90 K=4 Delta=0.010973  K*Delta=0.043894 (<=1)
x=10: x^-1=0.100 <= etaT e t0 = 0.100
j=0 Im z_j=0.14389 Im z_{j+1}=0.13292 C2=4.0310e+10 Vp-bound(crude loopMax)=7.9097e+05
j=1 Im z_j=0.13292 Im z_{j+1}=0.12195 C2=5.6898e+10 Vp-bound(crude loopMax)=1.5153e+06
j=2 Im z_j=0.12195 Im z_{j+1}=0.11097 C2=8.2967e+10 Vp-bound(crude loopMax)=3.1075e+06
j=3 Im z_j=0.11097 Im z_{j+1}=0.10000 C2=1.2583e+11 Vp-bound(crude loopMax)=6.9173e+06
v=Delta/s=5.2325e-09 ; Azuma-Y b=C2/2*v*s^4=6.3677e+27
Azuma-Z tail bound 4exp(-eps^2/(4 k lam)) at lam=0.01,k=4,eps=1: 0.0077
Azuma-Y tail denominators 4*k*4b^2 = 2.5950e+57
exists_level: lam0=0.01 Q=0.5 L0=6: ell=6<=L0, 2^ell lam0=0.64 <= lam0+2Q=1.01
qv_crude: z.im=0.1439 m=2 : eta^-(m+2)=2.3326e+03 (>=0, M Hermitian = 0 matrix)
ALL OK
```
Hypotheses discharged per target at this data (asserted in the script): `|e| < 2`; `0 ≤ t1 0 ≤ t0 0 < 1`; `0 < K 0`; `j < K 0`; `I.WF`; `x⁻¹ ≤ etaT e (t0 0)` (`1/10 ≤ 1/10`); `0 < Im z' ≤ Im z ≤ 2 Im z'`, `Im z' ≤ 1`, `Δ ≥ 0`, `‖z'-z‖ = Δ ≤ Δ`; `λ > 0`, `ε ≥ 0`, `v ≥ 0`; `b ≥ 0`; `0 < λ₀`, `0 ≤ Q < 2^{L₀} λ₀`. `Duhamel_step_decomp` additionally needs `ω (j+1) ∈ DuhamelGood`; the set is nonempty (merged `zero_mem_good`, `DuhamelA2.lean:1115`: `0 ∈ DuhamelGood sz0 0`), so the hypothesis is satisfiable at this data.

Observation (not a defect): in this instance `b ≈ 6.4e27` is forced by the available bound `(C₂/2) v s⁴` (`s⁴ ≈ 1.9e25`), so the Azuma-Y *conclusion* is numerically vacuous (the tail denominator is `2.6e57`); the *hypotheses* of `Duhamel_azuma_Y` are satisfied and any larger `b` also works, so the instance is nondegenerate as a hypothesis check. The Azuma-Z conclusion is non-vacuous (tail bound `0.0077`). The prover may pick any `b` with `hb` provable.

### Verdicts
- `Duhamel_azuma_Z`: PASS. `Duhamel_azuma_Y`: PASS. `Duhamel_bddC2C_Phi`: PASS. `Duhamel_step_decomp`: PASS. `Duhamel_exists_level`: PASS. `Duhamel_Vp_le`: PASS. `Duhamel_qv_le_crude`: PASS. `Duhamel_grid_facts`: PASS.
- Reason: every exponent closes with equality or explicit slack (table); the only `d`-dependence is `s = (L W)^d`, which matches `Sizes.size` and the merged `DuhamelA1:1058, 957` statements (`((L:ℝ)*W)^d`); no hypothesis set is empty.
- Overall verdict: PASS.

## (a′) Preflight corrections — Thu Oct  8 23:21:39 UTC 2026
Neither changes a verdict.  (1) (a)(ii) names the loop labels `(0,0,0),(1,0,0)`; the instance loop is `⟨[true,false],[0,1]⟩` over `Zd 3 4` (`0, 1` the constant labels `(0,0,0)`, `(1,1,1)`, as in `DuhamelA2Inst`), `m = 2`, `I.WF` by `rfl`.  (2) (a)(ii) takes `b = (C₂/2) v s⁴` at one `j`; `hb` of `Duhamel_azuma_Y` quantifies over all `j < K n`, so the instance uses the uniform `b = 3·10⁴·v·s⁵` (`C₂ ≤ 6 s 10⁴` as `η_{u_{j+1}} ≥ 1/10`); the observation that the Y tail is numerically weak stands (`b ≈ 6e27`).

## (b) Script output

### b.1 Build, registry pre-check, hygiene
```
$ lake build RBM3D.Universality.GUEPhase.DuhamelB > b1.log 2>&1; echo "exit=$?" >> b1.log; tail -3 b1.log   # at commit a9a3406
info: RBM3D/Universality/GUEPhase/DuhamelA1.lean:1266:0: 'RBM.Univ.GUEPhase.DuhamelA1Inst.contDiffAt_loop_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3784 jobs).
exit=0
$ grep -c "DuhamelB.lean" <build log>            ->  0
$ wc -l RBM3D/Universality/GUEPhase/DuhamelB.lean   ->  1271   (ticket stop line 1500)
$ lake env lean registry_precheck.lean > pre.log 2>&1; echo "exit=$?" >> pre.log; head -2 pre.log; tail -1 pre.log   # temp file, not in the repo: import RBM3D; import RBM3D.Universality.GUEPhase.DuhamelB; #assert_rbm_axioms
axiom audit: 10444 theorems, 3073 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
exit=0
$ lake build > fullbuild.log 2>&1; echo "exit=$?" >> fullbuild.log; tail -2 fullbuild.log   # whole library in the worktree (root does not import DuhamelB yet; the hub adds the import at merge)
Build completed successfully (4161 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^ *axiom " DuhamelB.lean | wc -l  ->  0
```
### b.2 Axioms (`#print axioms`, 7 defs + 8 theorems + 8 instance checks)
```
$ sed "s/.*depends on axioms: //" axioms.out | sort | uniq -c
  23 [propext, Classical.choice, Quot.sound]        (23 of 23 declarations; `sorryAx` count 0)
```
### b.3 Targets: statements extracted from the file by script (one line each, whitespace joined)
```
def DuhamelPhi (j : ℕ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ := fun M => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt e (gridTime t1 t0 K n (j + 1))) I
def Duhamelv : ℝ := gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)
def DuhamelVp (j : ℕ) (ω : PathΩ sz) : ℝ := Duhamelv sz t1 t0 K n * max (vGue sz n (gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) : ℝ) (vGue sz n (-Complex.I • gradMat (DuhamelPhi sz t1 t0 K n e I j) (gueH sz t1 t0 K n j ω)) : ℝ)
def DuhamelZinc (j : ℕ) (ω : PathΩ sz) : ℂ := DuhamelZ sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω) (ω (j + 1))
def DuhamelZst (lam : ℝ) : ℕ → PathΩ sz → ℂ | 0 => fun _ => 0 | j + 1 => {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I) lam (K n) ω}.indicator (DuhamelZinc sz t1 t0 K n e I j)
def DuhamelYst : ℕ → PathΩ sz → ℂ | 0 => fun _ => 0 | j + 1 => fun ω => if j < K n then DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω) (ω (j + 1)) - ∫ y, DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω) y ∂(gueUnit sz) else 0
def Duhamelr (j : ℕ) (ω : PathΩ sz) : ℂ := (∫ y, DuhamelPhi sz t1 t0 K n e I j (gueH sz t1 t0 K n j ω + Sizes.seqHflow sz n (Duhamelv sz t1 t0 K n) y) ∂(gueUnit sz)) - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt e (gridTime t1 t0 K n j)) I - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) I
theorem Duhamel_azuma_Z {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))} {lam : ℝ} (hlam : 0 < lam) (hv : 0 ≤ Duhamelv sz t1 t0 K n) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : (Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, DuhamelZst sz t1 t0 K n e I lam (j + 1) ω‖} ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * lam)))
theorem Duhamel_azuma_Y {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))} {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ j < K n, ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian → ∀ y, ‖DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b) {k : ℕ} (hk : k ≤ K n) {ε : ℝ} (hε : 0 ≤ ε) : (Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, DuhamelYst sz t1 t0 K n e I (j + 1) ω‖} ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * (4 * b ^ 2))))
theorem Duhamel_bddC2C_Phi {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))} (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {j : ℕ} (hj : j < K n) : (zt e (gridTime t1 t0 K n (j + 1))).im ≠ 0 ∧ HermTestFun sz n (DuhamelPhi sz t1 t0 K n e I j) ∧ ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (DuhamelPhi sz t1 t0 K n e I j)) M y y‖ ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * (sz.size n : ℝ) * (RBM.Gauss.etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) * ‖y‖ ^ 2
theorem Duhamel_step_decomp {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))} (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {j : ℕ} (hj : j < K n) (ω : PathΩ sz) (hgood : ω (j + 1) ∈ DuhamelGood sz n) : loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (j + 1) ω)) (zt e (gridTime t1 t0 K n (j + 1))) I - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt e (gridTime t1 t0 K n j)) I - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) I = DuhamelZinc sz t1 t0 K n e I j ω + DuhamelYst sz t1 t0 K n e I (j + 1) ω - DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω) + Duhamelr sz t1 t0 K n e I j ω
theorem Duhamel_exists_level {Ω' : Type*} {J : ℕ → Ω' → ℝ} {K' k L₀ : ℕ} {ω : Ω'} {lam0 Q : ℝ} (hlam0 : 0 < lam0) (hQ : 0 ≤ Q) (hQL : Q < 2 ^ L₀ * lam0) (hk : k ≤ K') (hJ : ∀ j < k, J j ω ≤ Q) : ∃ ℓ : ℕ, ℓ ≤ L₀ ∧ k ≤ firstHit J (2 ^ ℓ * lam0) K' ω ∧ 2 ^ ℓ * lam0 ≤ lam0 + 2 * Q
theorem Duhamel_Vp_le {d : ℕ} {sz : Sizes d} {n : ℕ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {z z' : ℂ} (hz'pos : 0 < z'.im) (hzz' : z'.im ≤ z.im) (hz2 : z.im ≤ 2 * z'.im) (hz'1 : z'.im ≤ 1) {Δ : ℝ} (hΔ : 0 ≤ Δ) (hzd : ‖z' - z‖ ≤ Δ) {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF) : Δ / ((sz.size n : ℕ) : ℝ) * max (vGue sz n (gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z' I) M) : ℝ) (vGue sz n (-Complex.I • gradMat (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M') z' I) M) : ℝ) ≤ 32 * (I.length : ℝ) ^ 2 * Δ * (((sz.size n : ℕ) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z (2 * I.length) + 2 * I.length * (z'.im)⁻¹ ^ (2 * I.length + 4) * Δ)
theorem Duhamel_qv_le_crude {d : ℕ} {sz : Sizes d} {n : ℕ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {z : ℂ} (hz : 0 < z.im) (m : ℕ) : ((sz.size n : ℕ) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z m ≤ (z.im)⁻¹ ^ (m + 2)
theorem Duhamel_grid_facts {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} (he : |e| < 2) (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n) {x : ℝ} (heta : x⁻¹ ≤ RBM.Gauss.etaT e (t0 n)) : 0 ≤ gridStep t1 t0 K n ∧ (K n : ℝ) * gridStep t1 t0 K n ≤ 1 ∧ (∀ j ≤ K n, x⁻¹ ≤ (zt e (gridTime t1 t0 K n j)).im ∧ (zt e (gridTime t1 t0 K n j)).im ≤ 1) ∧ (∀ j, ‖zt e (gridTime t1 t0 K n (j + 1)) - zt e (gridTime t1 t0 K n j)‖ = gridStep t1 t0 K n) ∧ (∀ j, (zt e (gridTime t1 t0 K n (j + 1))).im ≤ (zt e (gridTime t1 t0 K n j)).im ∧ (zt e (gridTime t1 t0 K n j)).im ≤ (zt e (gridTime t1 t0 K n (j + 1))).im + gridStep t1 t0 K n) ∧ (∀ k, gridTime t1 t0 K n k - t1 n = k * gridStep t1 t0 K n)
```
### b.4 Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.DuhamelBInst`, extracted by script)
Data: `sz0` (`d = 3`, `n = 0`, `L = 4`, `W = 32`, `N = 2097152`), `e = 0`, `Grid.lean` §GridCheck grid (`t₀ = 9/10`, `t₁ = e^{-1/20} t₀`, `K = 4`), loop `(+,-; 0, 1)`; `x = 10` (`x⁻¹ = η_{t₀} = 1/10`).  All 8 targets; every deterministic hypothesis discharged (no pin is left as a hypothesis).
```
theorem grid_facts_check : 0 ≤ DuhamelBInst_Δ ∧ (DuhamelBInst_K 0 : ℝ) * DuhamelBInst_Δ ≤ 1 ∧ (∀ j ≤ DuhamelBInst_K 0, (10 : ℝ)⁻¹ ≤ (DuhamelBInst_z j).im ∧ (DuhamelBInst_z j).im ≤ 1) ∧ (∀ j, ‖DuhamelBInst_z (j + 1) - DuhamelBInst_z j‖ = DuhamelBInst_Δ) ∧ (∀ j, (DuhamelBInst_z (j + 1)).im ≤ (DuhamelBInst_z j).im ∧ (DuhamelBInst_z j).im ≤ (DuhamelBInst_z (j + 1)).im + DuhamelBInst_Δ) ∧ (∀ k, gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 k - DuhamelBInst_t1 0 = k * DuhamelBInst_Δ) := Duhamel_grid_facts (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0) (K := DuhamelBInst_K) (n := 0) (e := 0) (by norm_num) DuhamelBInst_t1_nonneg DuhamelBInst_t1_le_t0 (by norm_num) (by norm_num) DuhamelBInst_eta
theorem bddC2C_Phi_check (j : ℕ) (hj : j < 4) : (DuhamelBInst_z (j + 1)).im ≠ 0 ∧ HermTestFun sz0 0 (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j) ∧ ∀ M y : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ, M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j)) M y y‖ ≤ ((DuhamelBInst_loop.length * (DuhamelBInst_loop.length + 1) : ℕ) : ℝ) * (sz0.size 0 : ℝ) * (RBM.Gauss.etaT 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 (j + 1)))⁻¹ ^ (DuhamelBInst_loop.length + 2) * ‖y‖ ^ 2 := Duhamel_bddC2C_Phi (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0) (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (by norm_num) rfl DuhamelBInst_t1_nonneg DuhamelBInst_t1_le_t0 (by norm_num) hj
theorem step_decomp_check (j : ℕ) (hj : j < 4) : loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 (j + 1) 0)) (DuhamelBInst_z (j + 1)) DuhamelBInst_loop - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j 0)) (DuhamelBInst_z j) DuhamelBInst_loop - (DuhamelBInst_Δ : ℂ) * genMatGUE 3 (sz0.L 0) (sz0.W 0) 0 (gridTime DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j) (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j 0) DuhamelBInst_loop = DuhamelZinc sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j 0 + DuhamelYst sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop (j + 1) 0 - DuhamelB sz0 0 (DuhamelPhi sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j) (Duhamelv sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0) (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j 0) + Duhamelr sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j 0 := Duhamel_step_decomp (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0) (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (by norm_num) rfl DuhamelBInst_t1_nonneg DuhamelBInst_t1_le_t0 (by norm_num) hj 0 DuhamelA2Inst.zero_mem_good
theorem Vp_le_check (j : ℕ) (hj : j < 4) (ω : PathΩ sz0) : DuhamelVp sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop j ω ≤ 32 * (DuhamelBInst_loop.length : ℝ) ^ 2 * DuhamelBInst_Δ * (((sz0.size 0 : ℕ) : ℝ)⁻¹ * (DuhamelBInst_z j).im⁻¹ ^ 2 * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j ω)) (DuhamelBInst_z j) (2 * DuhamelBInst_loop.length) + 2 * DuhamelBInst_loop.length * (DuhamelBInst_z (j + 1)).im⁻¹ ^ (2 * DuhamelBInst_loop.length + 4) * DuhamelBInst_Δ) := by have h1 := DuhamelBInst_im_ge (j + 1) (by omega) have hz'pos : 0 < (DuhamelBInst_z (j + 1)).im := lt_of_lt_of_le (by norm_num) h1 have hfac := grid_facts_check.2.2.2.2.1 j have hle1 := (grid_facts_check.2.2.1 (j + 1) (Nat.succ_le_of_lt hj)).2 have hΔ := DuhamelBInst_Δ_le exact Duhamel_Vp_le (sz := sz0) (M := gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 j ω) (gueH_isHermitian sz0 _ _ _ 0 j ω) (z := DuhamelBInst_z j) (z' := DuhamelBInst_z (j + 1)) hz'pos hfac.1 (by linarith [hfac.2]) hle1 DuhamelBInst_Δ_nonneg (grid_facts_check.2.2.2.1 j).le (I := DuhamelBInst_loop) rfl
theorem qv_le_crude_check (ω : PathΩ sz0) : ((sz0.size 0 : ℕ) : ℝ)⁻¹ * (DuhamelBInst_z 0).im⁻¹ ^ 2 * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 ω)) (DuhamelBInst_z 0) 2 ≤ (DuhamelBInst_z 0).im⁻¹ ^ (2 + 2) := Duhamel_qv_le_crude (sz := sz0) (gueH_isHermitian sz0 _ _ _ 0 0 ω) (lt_of_lt_of_le (by norm_num) (DuhamelBInst_im_ge 0 (by norm_num))) 2
theorem exists_level_check : ∃ ℓ : ℕ, ℓ ≤ 6 ∧ 4 ≤ firstHit (fun (_ : ℕ) (_ : PathΩ sz0) => (1 / 4 : ℝ)) (2 ^ ℓ * (1 / 100)) 4 (0 : PathΩ sz0) ∧ (2 : ℝ) ^ ℓ * (1 / 100) ≤ 1 / 100 + 2 * (1 / 2) := Duhamel_exists_level (J := fun (_ : ℕ) (_ : PathΩ sz0) => (1 / 4 : ℝ)) (K' := 4) (k := 4) (L₀ := 6) (ω := (0 : PathΩ sz0)) (lam0 := 1 / 100) (Q := 1 / 2) (by norm_num) (by norm_num) (by norm_num) le_rfl (fun _ _ => by norm_num)
theorem azuma_Z_check : (Pgue sz0).real {ω | 1 ≤ ‖∑ j ∈ Finset.range 4, DuhamelZst sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop (1 / 100) (j + 1) ω‖} ≤ 4 * Real.exp (-1 ^ 2 / (4 * (((4 : ℕ) : ℝ) * (1 / 100)))) := Duhamel_azuma_Z (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0) (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (lam := 1 / 100) (by norm_num) DuhamelBInst_v_nonneg 4 (ε := 1) (by norm_num)
theorem azuma_Y_check : (Pgue sz0).real {ω | 1 ≤ ‖∑ j ∈ Finset.range 4, DuhamelYst sz0 DuhamelBInst_t1 DuhamelBInst_t0 DuhamelBInst_K 0 0 DuhamelBInst_loop (j + 1) ω‖} ≤ 4 * Real.exp (-1 ^ 2 / (4 * (((4 : ℕ) : ℝ) * (4 * DuhamelBInst_b ^ 2)))) := Duhamel_azuma_Y (sz := sz0) (t1 := DuhamelBInst_t1) (t0 := DuhamelBInst_t0) (K := DuhamelBInst_K) (n := 0) (e := 0) (I := DuhamelBInst_loop) (b := DuhamelBInst_b) (by unfold DuhamelBInst_b; have := DuhamelBInst_v_nonneg; positivity) DuhamelBInst_hb (k := 4) (by norm_num) (ε := 1) (by norm_num)
```
### b.5 Name-clash, scope
```
$ grep -rnE "\b(DuhamelPhi|Duhamelv|DuhamelVp|DuhamelZinc|DuhamelZst|DuhamelYst|Duhamelr|Duhamel_azuma_Z|Duhamel_azuma_Y|Duhamel_bddC2C_Phi|Duhamel_step_decomp|Duhamel_exists_level|Duhamel_Vp_le|Duhamel_qv_le_crude|Duhamel_grid_facts|DuhamelBInst)\b" RBM3D --include=*.lean | grep -v "^RBM3D/Probe/" | grep -v "^RBM3D/Universality/GUEPhase/DuhamelB.lean" | wc -l   ->  0
$ git diff --stat main...t/T2349
 RBM3D/Universality/GUEPhase/DuhamelB.lean | 1271 +++++++++++++++++++++++++++++
 1 file changed, 1271 insertions(+)
$ git log --format="%h %s" main..t/T2349 | cat
a9a3406 T2349: DuhamelB docstring fixes (d-lines)
db9b26a T2349: DuhamelB section 6 (compiled nonempty instances)
d5fc71f T2349: DuhamelB sections 4-5 (variance proxy bounds, grid facts)
097d55b T2349: DuhamelB section 3 (step decomposition, dyadic level)
63ad64d T2349: DuhamelB section 2 (Azuma Y)
853f1fd T2349: DuhamelB sections 0-1 (Azuma Z)
$ grep -n "^private" DuhamelB.lean | grep -v "DuhamelB_\|DuhamelBInst_" | wc -l  ->  0   # every unpinned helper is private with the file prefix (CLAUDE.md 3 (E))
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h  ->  9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/DuhamelB.lean  ->  (empty: source unchanged since the port commit; 1020 lines)
```
### b.6 Port: translation table (source `RBM2D/Universality/GUEPhase/DuhamelB.lean` lines 61-1018 -> this file, lines 80-1032; `bash table.sh`: occurrences by `grep -oF`)
```
RBM2D token (source body)         n    RBM3D token (this file's body)        n
d.L n                           141 -> sz.L n                              162
d.W n                           132 -> sz.W n                              153
d.size n                         15 -> sz.size n                            15
Idx (d.L n)                     104 -> Idx d (sz.L n)                      104
Z2 (d.L n)                        9 -> Zd d (sz.L n)                         9
BlockIndex (d.L n)                2 -> Vtx d (sz.L n)                        0
gloop (                          10 -> loopL d (                            10
blockMat                         23 -> blockMat d (sz.L n) (sz.W n)         23
spectralZ e                      19 -> zt e                                 19
spectralZ_im                      4 -> zt_im                                 4
spectralM e                       5 -> mE e                                  5
spectralM_im_pos                  2 -> mE_im_pos                             2
norm_spectralM                    2 -> norm_mE                               2
RBM.Path.etaT                     3 -> RBM.Gauss.etaT                        3
RBM.Ind.loopMax (                 9 -> RBM.Ind.loopMax d (                   9
genMatGUE (                       3 -> genMatGUE d (                         3
measurable_Xentry (               1 -> measurable_Xentry d (                 1
Pgue d                           18 -> Pgue sz                              18
filt d                           55 -> filt sz                              55
PathΩ d                         19 -> PathΩ sz                            19
gueUnit d                        17 -> gueUnit sz                           17
gueH d                           31 -> gueH sz                              31
vGue d                           11 -> vGue sz                              11
Sizes.seqXmat d                  16 -> Sizes.seqXmat sz                     16
Sizes.SeqΩ d                    14 -> Sizes.SeqΩ sz                       14
Sizes.seqHflow d                  5 -> Sizes.seqHflow sz                     5
Duhamel_gueH_succ d               1 -> gueH_succ sz                          1
hermTestFunLoopN d                1 -> hermTestFunLoopN sz                   1
HermTestFun d                     1 -> HermTestFun sz                        1
{d : Sizes}                       8 -> {d : ℕ} {sz : Sizes d}              8
 norm_green_le                    0 -> DuhamelB_norm_green_le                3
```
Counts differ only where stated: `sz.L n`/`sz.W n` gain 23 each from the `blockMat d (sz.L n) (sz.W n)` expansion and lose 2 from the removed `BlockIndex` branch (141+23-2 = 162; 132+23-2 = 153); `BlockIndex` 2 -> 0 (branch removed, see hand edits).  The `d = 2` token audit of the source: `^ 2` occurs in 51 lines; the `d`-lines are `818` (`((L : ℝ) W) ^ 2`) and `815` (`pow_pos .. 2`, no `^`), here `DuhamelB_size_eq`/`DuhamelB_size_pos` with `d`; the other `^ 2` are squares of `η⁻¹`, `m`, `‖y‖`, `b`, `ε` (`833, 937, 944, 946` also mention `d.size n`, their `^ 2` is `(Im z)⁻¹ ^ 2` or `m ^ 2`); `W ^ 2`, `L ^ 2`, `(W * L) ^ 2` do not occur.
```
$ diff (source body after the mechanical token map) (this file body)   # hunks = hand edits; line numbers in the mapped body
597c597 636,655c636,640 667c652 683c668 715c700 755c740 756a742 758c744 760a747,756 763c759 794c790 796c792 900c896 956a953
```
Hand edits (the whole list): (H1) `597`: `DuhamelB_loopOf_eq` over `{d L}`, `LoopIdx (Zd d L)`; (H2) `667, 683, 715`: the port-map token `genMatGUE L W ↦ genMatGUE d L W` (in `Duhamelr`, the statement of `Duhamel_step_decomp`, and its proof); (H3) `636-655`: the case split `I.a.length = 0` of `Duhamel_bddC2C_Phi` is dropped, `hermTestFunLoopN` (`LoopC2N.lean:469`) has no `[NeZero k]`, so one branch covers `m = 0`; (H4) `755-760`: `DuhamelB_size_pos`/`_size_eq` carry the `d`-lines (`^ d`); (H5) `760a`: private `DuhamelB_norm_green_le` (twin of RBM2D `norm_green_le`) from the merged `norm_Gsig_le_inv_eta` (`Gauss/FlowCalculus.lean:644`), used at `794, 796`; (H6) `763, 900, 956a`: two docstrings and one blank line.  No other hunk touches a def or target statement, so the 7 defs and 8 theorems are the source's under the map of the table plus H2.

### b.7 Numbers and narrative
```
$ python3 -I numbers.py   # Delta = (t0 - t1)/K, v = Delta/N, b = 3e4 v N^5, N = 2097152; Z, Y tails at the instance data
Delta=0.010973 v=5.2325e-09 s=2097152 s^4=1.9343e+25 b=6.3677e+27
Z tail 4*exp(-eps^2/(4*k*lam)) = 0.00772
Y exponent eps^2/(4*k*4b^2) = 3.854e-58 ; tail = 4.000000
```
- Port of RBM2D `DuhamelB.lean` (9e0f275, 1020 lines) to `sz : Sizes d`: 1271 lines, 5 stage commits (`wc -l` at each: 384, 673, 815, 1035, 1271) and one docstring commit, `a9a3406`; ticket stop line 1500 not reached.
- All 7 defs and 8 theorems are public, statements = source under the token map of b.6; `hermTestFunLoopN`, `Duhamel_Z_re_im`, `Duhamel_measurable_R`, `Duhamel_integral_step`, `Duhamel_norm_T_le`, `Duhamel_vGue_gradMat_le`, `Duhamel_loopMax_le_crude`, `Duhamel_loopMax_shift_le`, `gueH_succ`, `gueHasCondSubgaussianMGF_linear`/`_of_frozen`, `azuma_complex`, `lt_firstHit_measurableSet`, `lt_firstHit_imp` are the merged ones.
- `d`-lines: only `s = sz.size n = (W L)^d`.  `Duhamel_Vp_le` rewrites `((L:ℝ) W)^d` of `Duhamel_loopMax_shift_le` to `s` (`DuhamelB_size_eq`) and cancels `Δ/s · s`; `Duhamel_qv_le_crude` the same with `Duhamel_loopMax_le_crude`; the Taylor constant `m(m+1) s η^{-(m+2)}` is the merged `hermTestFunLoopN` pin (`LoopC2N.lean:453`, theorem `:469`); the truncation `N = sz.size n` is `DuhamelGood` (`DuhamelA2.lean:166`).  No statement uses `3 ≤ d`.
- Instances (b.4): each of the 8 targets applied at the `GridCheck` data.  `Vp_le_check` holds for every `j < 4` and every path `ω`; `step_decomp_check` for `ω = 0` (`DuhamelA2Inst.zero_mem_good`) and `j < 4`; `azuma_Y_check` discharges `hb` by `Duhamel_bddC2C_Phi` + `Duhamel_norm_T_le` (`b = 3·10⁴·v·N⁵`); `exists_level_check` is on `PathΩ sz0` with the constant process `J ≡ 1/4`.
- Observation (not a defect): at the instance the Y tail `4 exp(-ε²/(4k·4b²))` is numerically `≈ 4` (`b ≈ 6.4e27`): the hypotheses are met, the conclusion is weak; the Z tail at `λ = 1/100, k = 4, ε = 1` is `4 exp(-6.25) ≈ 0.0077` (numbers: b.7 script).
- Observation: `hermTestFunLoopN` does not use `0 ≤ u` (`LoopC2N.lean:466`), so `ht1 : 0 ≤ t1 n` of `Duhamel_bddC2C_Phi`/`Duhamel_step_decomp` is not used either; kept as in the source (the ticket freezes the statements).
- Paper: the lemmas are internal to the Lean development of section 7.2; no statement of the paper is restated, the only paper-level scale is `N = (WL)^d` (`Defs/Sizes.lean:157`).
- Registry: no `Prop` predicate is defined or assumed; the pre-check exits 0 with the module imported.

## (c) Verified Mathlib names (script: 50 `#check` lines, 48 resolve, 2 are the expected absences below; `names.lean`)
`MeasureTheory.hittingBtwn_lt_iff`, `measurable_fderiv_apply_const`, `Measurable.of_eval_matrix`, `Matrix.measurable_apply`, `Measurable.eval_matrix`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, `ProbabilityTheory.HasSubgaussianMGF.zero`, `memLp_top_of_bound`, `norm_integral_le_of_norm_le_const`, `integral_re`, `integral_im`, `integral_sub`, `Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`, `Complex.continuous_re`, `MeasureTheory.StronglyMeasurable.integral_prod_right'`, `Nat.find_min'`, `Nat.find_spec`, `inv_anti₀`, `pow_le_pow_left₀`, `div_le_div_of_nonneg_right`, `Real.add_one_le_exp`, `Real.sqrt_sq`, `Real.sq_sqrt`, `Real.exp_pos`, `Real.exp_le_one_iff`, `Nat.mul_pos`, `pow_pos`, `Matrix.isHermitian_zero`, `Nat.succ_le_of_lt`, `one_le_inv₀`, `inv_mul_cancel₀`, `Matrix.nonsing_inv_eq_ringInverse`, `List.ofFn_getElem`, `List.ext_getElem`, `Finset.sum_range_succ'`, `Complex.coe_smul`, `Complex.re_ofReal_mul`, `Complex.im_ofReal_mul`, `Complex.norm_real`, `Matrix.trace_smul`, `Complex.re_sum`, `Finset.measurable_sum`, `Measurable.ite`, `Set.indicator_of_notMem`, `NNReal.coe_sum`, `abs_of_pos`, `le_of_abs_le`.
Verified absent (error `unknownIdentifier`): `RBM.Gauss.norm_green_le` (re-derived, H5), `RBM.Univ.GUEPhase.Duhamel_gueH_succ` (the merged `gueH_succ` is used).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (no Lean/paper statement difference arises: the targets are the RBM2D statements under the map; the paper-level scale `N = (WL)^d` is the merged `Sizes.size`).
- DECISIONS §29 (pin boundary, one line each; the targets are deterministic or Azuma statements at one fixed `n`): (1) time domain: `0 ≤ t1 n ≤ t0 n < 1` is in the hypotheses of `Duhamel_bddC2C_Phi`, `Duhamel_step_decomp`, `Duhamel_grid_facts`, and holds at the instance (`0 ≤ 0.856 ≤ 0.9 < 1`); (2) the case-(ii) boundary `1 - ilambda²/L²` does not occur (no `ilambda`); (3) no `L`-`W` polynomial relation is used: `L ≥ 3`, `W ≥ 1` only through `Sizes`, and `s = (LW)^d` is exact; (4) no `∀ n` / `∀ᶠ n`: every statement is at a fixed `n`.
- Consumers (UN-39/40 `DuhamelC`): `Duhamel_azuma_Y` asks `hb` at Hermitian base points only (as in the source); `Duhamel_grid_facts` is generic in `x` with `x⁻¹ ≤ etaT e (t0 n)`.
