Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct 11 09:09:13 UTC 2026

Pseudo-Lean only; `W^d := ((W n : ℕ) : ℂ)^d`, `[a] = Iblk d (L n) (W n) a`, `S := C.S n`, `C : FlowFM sz`. No Lean written. Base main@c33ef56.

### (i) Exponent table and design choices
| Item | Value | Constraint it must satisfy | Slack / evidence |
|---|---|---|---|
| **(a) kernel: block kernel, not the cut** | `Mss C n σ σ' a b := (W^d)⁻¹ Σ_{x∈[a]} Σ_{y∈[b]} Msig σ y x * Msig σ' x y`; `Msig true x y = C.M n x y`, `Msig false x y = conj (C.M n y x)` (`M(−)=M*`) | reads only `FlowFM.M`: no new field, `Carrier.lean` untouched; band `M=mE·I` gives `m_σ m_σ' I`; BA `M=B⊗I` gives `BAMss` | exact (algebra in (b), (c); script below). Cut rejected: `C.K` at BA is `BAKsol` = `Classical.choose` of a solution on `Set.Ico 0 1`, else `0` (`FlowPins:283-288`) |
| charge / index order | `M^{(σσ')}_{ab} = M(σ)_{ba} M(σ')_{ab}` (paper `1_2:663-664`, `eq:Msig` `1_2:1070`; Lean `BAMssOf` `KCactus:50`, `BAMss` `MFixedPoint:511`) | equals `BAMss d L B σ σ'` at `M = B⊗I` | non-symmetric test: swapped charges or transpose differ by 1.36e+01, this order by 1.8e-15 |
| slot kernel of the n-loop | slot `i` uses `(σ i, σ (finRotate n i))` (`3_5` `def:op_thn`, `def_Ustz`; `BAUN` `EKPins:53`; `cycProd` `Evolution:49`) | `n=2`: slot 0 is `(σ0,σ1)`, slot 1 is `(σ1,σ0)`, and `BAMss σ1 σ0 = (BAMss σ0 σ1)ᵀ` | reusing `(σ0,σ1)` at slot 1 differs by 2.36e+01 (non-symmetric `B`); no difference at band (`mul_comm`) or at BA (`B` symmetric) |
| drift kernels | `thetaKer C n σ σ' t := (Mss*S) * Step2Gen_Theta (Mss*S) t`; `uKer … s t := (1 − (s:ℂ)•(Mss*S)) * Step2Gen_Theta (Mss*S) t`; `Step2Gen_Theta X ξ = Ring.inverse (1 − ξ•X)` | band = old `(μ•S)*Θ_{tμ}`; BA (`S=1`) = `Mss * BATheta`, `uKer` = `BAuKer` | no size hypothesis: bridges equate `Ring.inverse` of one matrix. Order `(MS)*Θ` costs one lemma `Commute (Ring.inverse (1 − t•X)) X` (BA only, to reach the `Θ*Mss` of `BAKsolve`) |
| `u` | `0 ≤ u < 1` (pins unchanged) | `1−u>0` in `K_c/(1−u)` | row sums of `M^{(+,−)}` are 1 (Ward; supervisor 0853 BAT-F1), so `Θ` rows sum to `(1−u)⁻¹`; `K_c` is T3-BA's |
| hypotheses of (c) | `(E n + BAmF n).im ≠ 0` (`BAMres_fine_kron`, `FlowPins:72`); `NeZero (sz.L n)`, `NeZero (sz.W n)` are instances (`Sizes:152-153`) | from `BAFlow`: `κ ≤ Im m`, `κ>0`, `E` real | `Im m` at `E=0`, `L ≤ 128`: 0.9993 / 0.4106 / 0.0553 at `g = 1/64, 1, 10`; the identity does not use `κ` |
| `κ` (2254 G2: uniform in `L`) | `κ = 0.9993, 0.4106, 0.05` | `Im m ≥ κ` for all `L` | at `g=10` `Im m` still falls (0.0764 at `L=64`, 0.0553 at 128): the script does not give its limit; `κ` enters no constant of this ticket |
| `δ₀, C` of `stNewKLKAtgL'_of` | `δ₀ = κ/2`, `C = 2K_c + 2C_s(4+C_K) + C_s C_T` | unchanged | `μ` moves inside the kernel: `hms, hmσ` (F6 `‖m‖≤1`, `NewKLKGen:451-457`) disappear; F6 stays in `NewKLKGenHyp`, unused (statement stable) |
| F7 restated | `∀ s s' : Bool, Σ_b ‖thetaKer C n s s' u a b‖ tailW … ≤ K_c/(1−u) tailW …`, `C = mk sz (fun _ => E)` | covers both slot pairs of every `σ` | band: `‖μ‖=1` (existing `hm`) gives the old F7; BA: the real `Θ_BA M^{(σσ')}` convolution (T3-BA) |
| `STK2decaygL'` (BAT-F2) | `STK2decaygL` with `\|E\| ≤ 2−κ` replaced by `κ ≤ ((mk sz (fun _=>E)).m n).im`; `stK2decaygL_of_primed` (domain fact `\|E\| ≤ 2−κ → κ/2 ≤ Im m`, as `stNewKLKgL_of_primed`, `NewKLKGen:644`) | `K` is a carrier field, no kernel | `STK2decay d` bridge stays `Iff.rfl` |

**In place vs new names.** In place, same names, no re-pin: `STthetaOpg`, `Step2Gen_thetaKer`, `_uKer`, `_ThetaN`, `_UN` (they take `C` and charges `σ σ'` / `σ` instead of `S` and `μ`), and also `STeeUMg` (uses `uKer` at `σ` and `!σ`; **not in the ticket's list**). `STGridMartAtgL/gL`, `STGridRepNAtgL/gL`, `STNewKLKAtgL/gL`, `STNewKLKAtgL'/gL'`, `STgDriftg`, `STgDriftNg` keep their text (they unfold through the redefined operators), so the band statements are untouched (G1). New public names carry `Step2Kern_` (`_Msig, _Mss, _Mss_of_kron, _Mss_band`, `_thetaKer_band`…) plus `STK2decaygL'`, `stK2decaygL_of_primed`; `grep -rn Step2Kern RBM3D RBM3D.lean` returns 0 lines. Definitions and band lemmas go in `Step2Gen.lean`; the BA identities go in the new `Chain/Step2Kern.lean`, which imports `BA.FlowPins`, `BA.EKPins` (both import `Step2Gen`, so `Step2Gen` cannot import it); `import RBM3D.Chain.Step2Kern` after the last import line of `RBM3D.lean`.

**Consumers on main** (grep `-w`, files containing the name): `STthetaOpg`: NewKLKGen, Step2Gen. `STgDriftg, STgDriftNg, STeeUMg, Step2Gen_thetaKer/_uKer/_ThetaN/_UN, STGridMartAtgL/gL, STGridRepNAtgL/gL, STK2decaygL`: Step2Gen only. `STNewKLKAtgL/gL`: Step2Gen, NewKLKGen. `NewKLKGenHyp`, `stNewKLKAtgL_of_primed`: NewKLKGen only. The band pins used by `Path/DifREP*` are the merged band definitions, unchanged. Reverse cone of `Chain.Step2Gen`: 75 modules by script (the ticket's 76 counts `Step2Gen`); none is `Graph/LWExpCert*`.
**Bridges that stop being `rfl`/`Iff.rfl`** (`Step2Gen`): `bandStep2_STthetaOp` :241 (`Fin.sum_univ_two`, `mul_comm` at slot 1), `_STgDrift` :694, `_STgDriftN` :871, `_STeeUM` :874 (`σ`, `!σ`), `_STGridMartAt` :698, `_STGridMart` :701, `_STGridRepNAt` :876, `_STGridRepN` :879, `_STNewKLKAt` :917, `_STNewKLK` :919. Stay `rfl`/`Iff.rfl`: `_STK2decay` :920, `_STgA`, `_STstopIdx`, the `STLM…` family. `newKLKGenHyp_band` (`NewKLKGen:664`) re-discharges F7 through `Step2Kern_thetaKer_band`.

**(b) written out.** `Mss_of_kron`: if `C.M n x y = Bm (blk x) (blk y) * (if ofs x = ofs y then 1 else 0)` (`blk` `Sizes:50`, `split` `:64`) then `Mss C n σ σ' = of fun a b => Bsig σ b a * Bsig σ' a b` (`Bsig true = Bm`, `Bsig false = Bmᴴ`): reindex `[a]×[b]` by `splitEquiv`; the offset diagonal leaves `W^d` terms; `(W^d)⁻¹ W^d = 1` (`card_Iblk` `Sizes:95`). Band: `Bm a b = if a = b then mE else 0` and `x = y ⇔ blk x = blk y ∧ ofs x = ofs y` (`split_injective` `:67`), so `Mss (bandFM sz E) n σ σ' = (m_σ m_σ') • 1`. Then `(μ•1)*S = μ•S`, `u•(μ•S) = (u*μ)•S` give `thetaKer/uKer/ThetaN/UN` = band `thetaKer/uKer/ThetaN/UN` (`Evolution:52-67`); `cycProd (fun i => mSigma E (σ i)) i = mSigma (σ i) * mSigma (σ (finRotate n i))` is `rfl`.
**(c) written out.** `BAMfine = Mres (lam0•PsiI) E m = (BAMB ⊗ₖ 1).submatrix e e` (`BAMres_fine_kron`), so `Bm = BAMB`, `Bsig = BAMsigma` (`MFixedPoint:507`): `Mss (baFM sz lam0 E) n σ σ' = BAMss d L (BAMB d L (lam0 n) (E n) (BAmF n)) σ σ'`. With `S = 1` (`FlowPins:327`): `Mss*1 = Mss` and `Step2Gen_Theta Mss u = PropThetaQ Mss u = BATheta`, so `thetaKer = Mss * BATheta = BATheta * Mss` (commutation lemma), i.e. `(W^d)⁻¹ * thetaKer σ.1 σ.2 u a₁ a₂ =` the RHS of `BAKsolve` (`KSolve:63-66`), for all four `σ`. n-loop: `uKer = BAuKer` (`EKPins:49`, same order, `mul_one`) and `UN (baFM …) n σ s t A a = BAUN d (sz.L n) (lam0 n) (E n) (BAmF n) σ s t A a`: **the `BAUN` identity holds, no obstacle** (both products use `finRotate n i`); `BA/*.lean` has no `ThetaN` twin (grep), so only `UN` is stated.

### (ii) One concrete nondegenerate instance
`d = 3`. (b) band at `sz0` (`L=4, W=32, N=2097152`, `Sizes:260-267`), `E ≡ 0` (`m = i`), all four charge pairs. (c) BA at `sz0` along `zSeq` (`BAMfine_sz0_kron`; `BAmF_sz0_im_pos` gives `Im m > 0`, hence `(E+m).im ≠ 0`), all four pairs (the identity is proved for every charge, no stand-in). Numeric check of the algebra (`d=3`, `E=0`, `S=1`, `L=4`, `W=2`, `N=512`, `g = 1/64, 1, 10`, `u ∈ {0, .5, .9}`; `Ψ_{ab}=1(|a−b|₁=1)`, `m` solves `(self_m)`, `B = (gΨ−(E+m))⁻¹`, `M = B⊗I_{W^d}`); `ker` is `M S (1−uMS)⁻¹` built from the fine matrix, `Th = (1−u Mss)⁻¹`:
```
$ cd <scratchpad>/T2414 && python3 check.py
== (c) BA identity, d=3, E=0, S=1: derived drift kernel vs BATheta*BAMss; Im m uniform in L
g=0.015625: Im m (E=0): L=4 0.9993 L=8 0.9993 L=16 0.9993 L=64 0.9993 L=128 0.9993 | max|Mfine-BAMss|=1.1e-16 max|ker-Th*Mss|=1.4e-14 max|ker-Mss*Th|=1.4e-14 | |1-|m|^2|=1.461e-03, max|old diag - BA ker|(+,-,u=.9)=2.367e-02
g=1: Im m (E=0): L=4 0.5959 L=8 0.4665 L=16 0.4160 L=64 0.4106 L=128 0.4106 | max|Mfine-BAMss|=5.6e-17 max|ker-Th*Mss|=1.3e-15 max|ker-Mss*Th|=5.6e-16 | |1-|m|^2|=6.449e-01, max|old diag - BA ker|(+,-,u=.9)=6.333e-01
g=10: Im m (E=0): L=4 0.5594 L=8 0.3654 L=16 0.2028 L=64 0.0764 L=128 0.0553 | max|Mfine-BAMss|=5.6e-17 max|ker-Th*Mss|=2.3e-15 max|ker-Mss*Th|=6.7e-16 | |1-|m|^2|=6.871e-01, max|old diag - BA ker|(+,-,u=.9)=9.178e-01
== convention test: non-symmetric complex block matrix B (fine M = B (x) I), W=2, L=3
(s1,s2)=(+,+): |fine - BAMss(s1,s2)|=9.9e-16  |fine - BAMss(s2,s1)|=9.93e-16  |fine - BAMss(s1,s2)^T|=9.93e-16
(s1,s2)=(+,-): |fine - BAMss(s1,s2)|=1.8e-15  |fine - BAMss(s2,s1)|=1.36e+01  |fine - BAMss(s1,s2)^T|=1.36e+01
(s1,s2)=(-,+): |fine - BAMss(s1,s2)|=1.8e-15  |fine - BAMss(s2,s1)|=1.36e+01  |fine - BAMss(s1,s2)^T|=1.36e+01
(s1,s2)=(-,-): |fine - BAMss(s1,s2)|=9.9e-16  |fine - BAMss(s2,s1)|=9.93e-16  |fine - BAMss(s1,s2)^T|=9.93e-16
BAMss(-,+) = BAMss(+,-)^T: True
trace-cyclicity K_(-,+)(a1,a0) = K_(+,-)(a0,a1) (slot-1 kernel is (s1,s0)): True
slot-1 kernel (s1,s0) vs wrong reuse of (s0,s1) at slot 1: max diff = 2.357e+01
== (b) band: M = mE I fine, block kernel = m(s1) m(s2) I, E=0.5, L=3, W=2
(+,+): max|block - m m' I| = 5.6e-17
(+,-): max|block - m m' I| = 0.0e+00
(-,+): max|block - m m' I| = 0.0e+00
(-,-): max|block - m m' I| = 5.6e-17
```
Reading: `max|ker−Th*Mss|` and `max|ker−Mss*Th|` are `≤ 1.4e-14` at all three `g` (the BA kernel is `Θ·Mss`); the old scalar-`m` diagonal kernel differs from it by 2.4e-02 / 6.3e-01 / 9.2e-01 (BAT-F1). (b) holds to 5.6e-17.

### Predicted lines (stop line 1,400) and verdicts
`Step2Gen`: kernels +45 −19 (old `:715-733`), `STthetaOpg`/`STeeUMg` ±10, `Mss_of_kron` and band lemmas +95, bridge proofs +95, `STK2decaygL'` + bridge +25: about +250. `NewKLKGen`: F7, `hB1` re-proof, band F7, instances: about +100. `Step2Kern.lean` (header, BA lemmas, commutation, BA and band instances): about +200. Total about 550 (range 450–750); margin to 1,400 about 650.
Paper-delta candidates: `T2414a` — `eq:Msig` (`1_2:1070`) reads `W^d tr(M(σ1)E_a M(σ2)E_b)`, `def:Theta_BA` (`1_2:663-664`) reads `W^{-d}Σ_{x∈[a],y∈[b]}…`; Lean uses the latter (matches `BAMss` and the band, script above), no claim about the paper's `tr` normalisation. `T2414b` — extends `T2405a` (`T2405-prove.md:63`): `STthetaOpg`/`Step2Gen_*` become the block-kernel forms.
Verdicts: target 1 (a) PASS; 2 (n-loop kernels, drifts) PASS; 3 (b) PASS; 4 (c) PASS, `BAUN` identity holds; 5 (e) PASS; 6 (BAT-F2) PASS; 7, 8, 9 PASS (nothing blocks). Condition for 1b: `STeeUMg` is added to the redefined set (it is absent from the ticket's list).

## (a″) Probe compile — Sun Oct 11 09:49:30 UTC 2026

Probe `RBM3D/Probe/T2414Pins.lean` in `/Users/junyin/Lean_proof/RBM3D-wt/T2414` (branch `t/T2414`), commit `6111b33` (parent `c33ef56`): 769 lines, the only file of `git diff main...t/T2414`, no root import; imports `Chain.NewKLKGen`, `BA.FlowPins`, `BA.KSolve`, `BA.EKPins`, `BA.KTreeRep` (for the merged `baKsolve`). Section (a) is not edited: `md5` of its 55 lines is `c5d77fcd92458604b5b85714f983a1a9` before and after this section was appended. `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2414`.

```
$ date -u
Sun Oct 11 09:48:38 UTC 2026
$ git log -1 --format="%h %s"; git status --short; git diff --stat main...t/T2414; wc -l RBM3D/Probe/T2414Pins.lean
6111b33 T2414: probe pins compiled (1a probe step, CONTROL H209; never merged)
 RBM3D/Probe/T2414Pins.lean | 769 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 769 insertions(+)
     769 RBM3D/Probe/T2414Pins.lean
$ grep -nE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2414Pins.lean; echo "grep exit=$?"
grep exit=1
$ lake env lean RBM3D/Probe/T2414Pins.lean; echo "exit=$?"
RBM.BA.T2414Pins.Step2Kern_Msig {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (σ : Bool)
  (x y : Idx d (sz.L n) (sz.W n)) : ℂ
RBM.BA.T2414Pins.Step2Kern_Bsig.{u_1} {Λ : Type u_1} (Bm : Matrix Λ Λ ℂ) (σ : Bool) : Matrix Λ Λ ℂ
RBM.BA.T2414Pins.Step2Kern_Mss {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) :
  Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
RBM.BA.T2414Pins.Step2Gen_thetaKer {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (t : ℝ) :
  Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
RBM.BA.T2414Pins.Step2Gen_uKer {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (s t : ℝ) :
  Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
RBM.BA.T2414Pins.Step2Gen_ThetaN {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ)
  (A : (Fin k → Zd d (sz.L n)) → ℂ) : (Fin k → Zd d (sz.L n)) → ℂ
RBM.BA.T2414Pins.Step2Gen_UN {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ)
  (A : (Fin k → Zd d (sz.L n)) → ℂ) : (Fin k → Zd d (sz.L n)) → ℂ
RBM.BA.T2414Pins.STthetaOpg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool)
  (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) : ℂ
RBM.BA.T2414Pins.STgDriftg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
  (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ
RBM.BA.T2414Pins.STgDriftNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
  (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ
RBM.BA.T2414Pins.STeeUMg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (v w : ℝ)
  (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {m : ℕ} (σ : Fin m → Bool)
  (a : Fin m → Zd d (sz.L n)) : ℂ
RBM.BA.T2414Pins.STGridMartAtgL (d : ℕ) (C₀ : ℝ) (Flow : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
  (mk : (sz : Sizes d) → (ℕ → ℂ) → Step2Mat sz) (T0 : Sizes d → (ℕ → ℂ) → ℕ → ℝ) : Prop
RBM.BA.T2414Pins.STGridMartgL (d : ℕ) (Flow : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
  (mk : (sz : Sizes d) → (ℕ → ℂ) → Step2Mat sz) (T0 : Sizes d → (ℕ → ℂ) → ℕ → ℝ) : Prop
RBM.BA.T2414Pins.STGridRepNAtgL (d m : ℕ) (C₀ : ℝ) (Flow : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
  (mk : (sz : Sizes d) → (ℕ → ℂ) → Step2Mat sz) (T0 : Sizes d → (ℕ → ℂ) → ℕ → ℝ) : Prop
RBM.BA.T2414Pins.STGridRepNgL (d : ℕ) (Flow : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
  (mk : (sz : Sizes d) → (ℕ → ℂ) → Step2Mat sz) (T0 : Sizes d → (ℕ → ℂ) → ℕ → ℝ) : Prop
RBM.BA.T2414Pins.STNewKLKAtgL (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : (sz : Sizes d) → (ℕ → ℝ) → Step2Mat sz) : Prop
RBM.BA.T2414Pins.STNewKLKgL (d : ℕ) (mk : (sz : Sizes d) → (ℕ → ℝ) → Step2Mat sz) : Prop
RBM.BA.T2414Pins.STNewKLKAtgL' (d : ℕ) (κ 𝔡 C δ₀ : ℝ) (mk : (sz : Sizes d) → (ℕ → ℝ) → Step2Mat sz) : Prop
RBM.BA.T2414Pins.STNewKLKgL' (d : ℕ) (mk : (sz : Sizes d) → (ℕ → ℝ) → Step2Mat sz) : Prop
RBM.BA.T2414Pins.NewKLKGenHyp (d : ℕ) (κ 𝔡 : ℝ) (mk : (sz : Sizes d) → (ℕ → ℝ) → Step2Mat sz) : Prop
RBM.BA.T2414Pins.STK2decaygL' (d : ℕ) (mk : (sz : Sizes d) → (ℕ → ℝ) → Step2Mat sz) : Prop
RBM.BA.T2414Pins.Step2Kern_Mss_of_kron_pin : Prop
RBM.BA.T2414Pins.Step2Kern_Mss_band_pin : Prop
RBM.BA.T2414Pins.Step2Kern_thetaKer_band_pin : Prop
RBM.BA.T2414Pins.Step2Kern_uKer_band_pin : Prop
RBM.BA.T2414Pins.Step2Kern_ThetaN_band_pin : Prop
RBM.BA.T2414Pins.Step2Kern_UN_band_pin : Prop
RBM.BA.T2414Pins.bandStep2_STthetaOp_pin : Prop
RBM.BA.T2414Pins.bandStep2_STgDrift_pin : Prop
RBM.BA.T2414Pins.bandStep2_STgDriftN_pin : Prop
RBM.BA.T2414Pins.bandStep2_STeeUM_pin : Prop
RBM.BA.T2414Pins.bandStep2_STGridMartAt_pin : Prop
RBM.BA.T2414Pins.bandStep2_STGridMart_pin : Prop
RBM.BA.T2414Pins.bandStep2_STGridRepNAt_pin : Prop
RBM.BA.T2414Pins.bandStep2_STGridRepN_pin : Prop
RBM.BA.T2414Pins.bandStep2_STNewKLKAt_pin : Prop
RBM.BA.T2414Pins.bandStep2_STNewKLK_pin : Prop
RBM.BA.T2414Pins.Step2Kern_Theta_comm_pin : Prop
RBM.BA.T2414Pins.Step2Kern_Mss_BA_pin : Prop
RBM.BA.T2414Pins.Step2Kern_thetaKer_BA_pin : Prop
RBM.BA.T2414Pins.Step2Kern_BAKsolve_form_pin : Prop
RBM.BA.T2414Pins.Step2Kern_uKer_BA_pin : Prop
RBM.BA.T2414Pins.Step2Kern_UN_BA_pin : Prop
RBM.BA.T2414Pins.stNewKLKAtgL'_of_pin : Prop
RBM.BA.T2414Pins.stNewKLKAtgL'_holds_pin : Prop
RBM.BA.T2414Pins.stNewKLKgL'_of_pin : Prop
RBM.BA.T2414Pins.newKLKGenHyp_band_pin : Prop
RBM.BA.T2414Pins.stNewKLKgL_of_primed_pin : Prop
RBM.BA.T2414Pins.stK2decaygL_of_primed_pin : Prop
exit=0
```

Axioms of the examples, the files of the branch that mention the redefined names, and the scratch feasibility runs (`$S/final2.sh`, `$S/final3.sh`; `$S/AxiomsCheck.lean` is the probe with each `example` renamed `def T2414_inst_<k>` and one `#print axioms` line per example, so the 25 changed lines are 12 + 12 + one blank line):

```
$ date -u
Sun Oct 11 09:48:43 UTC 2026
$ python3 $S/mkaxioms.py   # scratch copy: each `example` renamed `def T2414_inst_<k>`, one `#print axioms` line per example
$ grep -c "^example" RBM3D/Probe/T2414Pins.lean; diff RBM3D/Probe/T2414Pins.lean $S/AxiomsCheck.lean | grep -c "^>"
12
25
$ lake env lean $S/AxiomsCheck.lean | grep "depends on" | sed "s/^.*depends on axioms: //" | sort | uniq -c
  12 [propext, Classical.choice, Quot.sound]
$ grep -c "^def .*_pin : Prop" RBM3D/Probe/T2414Pins.lean
28
$ grep -rlwE "Step2Gen_thetaKer|Step2Gen_uKer|Step2Gen_ThetaN|Step2Gen_UN|STthetaOpg|STgDriftg|STgDriftNg|STeeUMg|STGridMartAtgL|STGridMartgL|STGridRepNAtgL|STGridRepNgL|STNewKLKAtgL|STNewKLKgL|STK2decaygL|NewKLKGenHyp" RBM3D RBM3D.lean --include="*.lean" | grep -v "^RBM3D/Probe/"
RBM3D/Chain/NewKLKGen.lean
RBM3D/Chain/Step2Gen.lean
$ cd $S (scratch, outside the repo); wc -l f6.lean f5b.lean; grep -c "^example : .*_pin" f6.lean f5b.lean
     799 f6.lean
    1053 f5b.lean
    1852 total
f6.lean:23
f5b.lean:5
$ lake env lean $S/f6.lean; echo "exit=$?"
exit=0
$ lake env lean $S/f5b.lean > $S/f5b.out 2>&1; echo "exit=$?"; grep -c error $S/f5b.out; grep -nE "sorry|admit|native_decide" $S/f6.lean $S/f5b.lean; echo "grep exit=$?"
exit=0
0
grep exit=1
$ date -u
Sun Oct 11 09:49:05 UTC 2026
$ awk: lines of `section Proofs` .. `end Proofs` in $S/f6.lean; of `section Vocab` .. `end Vocab` in the probe
Proofs block: 274
Vocab block: 44
$ diff <(NewKLKGen.lean, "## 1. The primed pins" .. "## 7.") <($S/f5.lean, "## 1. The primed pins" .. end) | grep "^[<>]" | cut -c1 | sort | uniq -c
  42 <
  38 >
```

**Contents.** Definitions of the new objects (`Step2Kern_Msig`, `_Bsig`, `_Mss`; the kernels `Step2Gen_thetaKer`, `_uKer`, `_ThetaN`, `_UN` over `C : FlowFM sz`); the operators and predicates that read them at their final text (`STthetaOpg`, `STgDriftg`, `STgDriftNg`, `STeeUMg`, `STGridMartAtgL/gL`, `STGridRepNAtgL/gL`, `STNewKLKAtgL/gL`, `STNewKLKAtgL'/gL'`, `NewKLKGenHyp` with F7 restated, `STK2decaygL'`); 28 `Prop` pins `X_pin`, the statements of the theorems 1b proves (6 kernel pins and 10 bridges of (b), 6 of (c), 5 of (e), 1 of BAT-F2); 12 `example`s; no theorem, no placeholder proof. Namespace `RBM.BA.T2414Pins`: an object that 1b redefines in place carries its final name and shadows the merged one, which is written `RBM.BA.X`.

**Instances** (`d = 3`; `sz0` has `L = 4`, `W = 32`; the pins are the hypotheses of the examples, every deterministic hypothesis is discharged):
- (b) band, `E ≡ 0` (`m = i`), four charge pairs, `k = 3` loops: the `kron` hypothesis of `Mss_of_kron` is proved from `split_injective`; `‖m(σ) m(σ')‖ = 1`; the `kron` route and the `band` route to `M^(σσ')` agree; the ten bridges at `bandStep2Mat sz0 (STflowE z0)` (window `[0, 1/16]`, 8 grid steps).
- (c) BA along `zSeq`, `n = 0`: `(E + m).im ≠ 0` from `BAmF_sz0_im_pos`, the `kron` hypothesis from `BAMfine_sz0_kron`, `Bsig = BAMsigma` by `rfl`; the `Mss`, `thetaKer`, `uKer`, `UN` identities for every `σ σ' : Bool`; with the merged `baKsolve 3` (`BAReal` from `hrI`) a `K` that solves the tree equations and has two-loop value `W^(-d) thetaKer`.
- (e) at the band (`κ = 𝔡 = 1/10`, `δ₀ = 1/20`) and pointwise at `n = 0`, `E = 0`, `u = 1/32`, `D = 1`, `ℓ = 2`, `H = 0`; G1 (`STNewKLK d` through the generic route and the bridge); BAT-F2 (`STK2decay d` through `STK2decaygL'`).

**Readings of the pseudo-Lean of (a)** (module docstring `T2414Pins.lean:12-55`, for the 1a-audit).
1. (a) uses `Bsig` without a definition; the probe has `Step2Kern_Bsig Bm σ := if σ then Bm else Bmᴴ`, equal to `BAMsigma` by `rfl`; `Mss_of_kron` states the `kron` hypothesis with `split` (`blk x = (split x).1`, `ofs x = (split x).2`).
2. (a) says `STgDriftNg` and `STGridRepNAtgL` "keep their text". Compiled: their signatures and clauses are unchanged, but the calls of `ThetaN` and `UN` read `Cm.toFlowFM n σ` instead of `Cm.S n` and `fun i => STmsigg Cm n (σ i)`.
3. "The current ones" of (b) are the merged band kernels `RBM.thetaKer`, `uKer`, `ThetaN`, `UN` (`Kernel/Evolution.lean:52-67`); the in-place redefinition replaces the merged generic `Step2Gen_thetaKer S μ t` etc., so the `_band` pins are stated against `RBM.*` (the two agree by `rfl` at `S = SB`, §8 of the probe).
4. In `Chain/Step2Gen.lean`, `STthetaOpg` (`:195`) comes before the kernels (`:715-733`): in 1b the block kernel and `thetaKer`, `uKer` go above it, after `Step2Gen_Theta` (`:191`).
5. F7 quantifies `s s' : Bool` (all four pairs); F6 stays and is unused; `stNewKLKAtgL'_holds_pin` is the `choose_spec` form over a proof `hof` of `stNewKLKAtgL'_of_pin`.

**Scratch feasibility** (outside the repo, not committed, not required by the probe step). `$S/f6.lean` is the probe's §1-§6 plus a block of theorems (274 lines: `count_ofs`, `Mss_of_kron`, `Theta_comm`, the band and BA identities, the ten bridges, `stK2decaygL_of_primed`); 23 of the 28 pins are proved verbatim in it (`example : X_pin := fun ... => X ...`), exit 0. `$S/f5b.lean` is a scratch copy of `Chain/NewKLKGen.lean` over the new kernel (the probe's vocabulary prepended; F7 of `NewKLKGenHyp`, the `hK1`-`hB1` block of `stNewKLKAtgL'_of` and F7 of `newKLKGenHyp_band` changed, instance section dropped); the other 5 pins are proved verbatim in it, exit 0, no error line. Neither file contains a placeholder proof (grep above). Technical note: for `bandStep2_STNewKLKAt` the `simp` rewrite needs the constant-`E` form of the operator bridge (`STthetaOp sz n E u ... = STthetaOpg (bandStep2Mat sz (fun _ => E)) ...`); with the bridge stated for `E n`, `simp only` did not rewrite there. Measured in scratch: vocabulary 44 lines, proof block 274 lines, `NewKLKGen` §1-§6 42 lines removed and 38 added; (a)(iv) predicts about +250 (`Step2Gen`), +100 (`NewKLKGen`), +200 (`Step2Kern`).

**Result.** The probe compiles with exit 0; all 28 pins and 12 examples elaborate; the examples depend on the standard three axioms. No correction to (a) (no `(a′)`): the verdicts of (a) stand (reading 2 refines a phrase of (a), it changes no verdict), and the paper-delta candidates `T2414a`, `T2414b` are unchanged; no new candidate.

## (a′) Preflight corrections — Sun Oct 11 10:22:27 UTC 2026

One row of (i) is corrected; no verdict changes (section (a) is untouched: `head -55 | md5` is still `c5d77fcd92458604b5b85714f983a1a9`).
Row "κ (2254 G2: uniform in `L`)": "`κ = 0.9993, 0.4106, 0.05`" at `g = 1/64, 1, 10` is not supported at `g = 10`: the independent script of the 1a-audit
(`audit1a/indep.py`, §4 of `docs/reports/T2414-1a-audit.md`, rerun by this stage) prints, for `g = 10, E = 0`, `Im m`: `L=16 0.2028  L=64 0.0764  L=128 0.0553  L=256 0.0477` (still falling).
`κ` enters no statement, constant or threshold of this ticket (the identities of (c) are `κ`-free and proved for every datum with `(E + m).im ≠ 0`); read the row as "not used here".

## (b) Script output — Sun Oct 11 10:35:20 UTC 2026

```
$ date -u; git log --oneline 6111b33..HEAD | paste -sd" " -; git status --short | wc -l
Sun Oct 11 10:33:27 UTC 2026
0684439 cb6cba0 ef345e1 6e940e5 c8371bf 843c627 5b02c87
       0
$ git diff --numstat main...t/T2414 -- RBM3D/Chain   # stop line 1,400 = wc -l new file + net in-place
89	49	RBM3D/Chain/NewKLKGen.lean
323	53	RBM3D/Chain/Step2Gen.lean
207	0	RBM3D/Chain/Step2Kern.lean
inserted 619 deleted 102 net 517 (incl. the 207 lines of Step2Kern.lean), two-sided 721
$ git diff --name-only main...t/T2414 | paste -sd" " -
RBM3D/Chain/NewKLKGen.lean RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Probe/T2414Pins.lean
$ lake build RBM3D.Chain.Step2Gen RBM3D.Chain.NewKLKGen RBM3D.Chain.Step2Kern 2>&1 | tail -1
Build completed successfully (3769 jobs).
$ whole-library `lake build` (RBM3D.lean with one TEMPORARY import line for Step2Kern, uncommitted, restored): start, end, exit, error lines, tail
Sun Oct 11 10:29:00 UTC 2026 | Sun Oct 11 10:33:21 UTC 2026 | exit=0 | errors 0 | Build completed successfully (4223 jobs).
$ the first whole-library build of this worktree (before stK2decaygL'_band was public): grep -A1 "axiom audit"
error: RBM3D.lean:454:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structural
  [RBM.BA.STK2decaygL']
$ #print axioms: 45 new/changed public declarations, and the 20 examples (each renamed to a def in a scratch copy); lines with exactly [propext, Classical.choice, Quot.sound] / other
decls: 45 / 0
examples Step2Gen: 10 / 0
examples NewKLKGen: 7 / 0
examples Step2Kern: 3 / 0
$ grep -cE "sorry|admit|native_decide|^axiom" on the three files
RBM3D/Chain/Step2Gen.lean:0 RBM3D/Chain/NewKLKGen.lean:0 RBM3D/Chain/Step2Kern.lean:0
$ pin check: 28 `X_pin` Props of the probe (sections 3-6) vs the final theorems, `example : X_pin := fun .. => X ..` in $S/PinCheck.lean
pins 28, examples 28, exit=0, output lines        0, errors 0
$ lake env lean docs/tickets/checks/T2414-check.lean   # G1: STNewKLK d, STK2decay d as merged
exit=0, output lines       44, errors 0
$ name clash: git grep on main for the new public names; duplicates in the branch
main:        0 matches; branch duplicates:        0
$ ports: grep -c "RBM1D|RBM2D" Step2Gen NewKLKGen Step2Kern
RBM3D/Chain/Step2Gen.lean:0 RBM3D/Chain/NewKLKGen.lean:1 RBM3D/Chain/Step2Kern.lean:0
$ python3 extract.py defs   # statements of the new/redefined data, from the files
Step2Gen.lean:181: def Step2Kern_Mss (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
Step2Gen.lean:188: def Step2Gen_thetaKer (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
Step2Gen.lean:192: def Step2Gen_uKer (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (s t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
Step2Gen.lean:197: def Step2Gen_ThetaN (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) : (Fin k → Zd d (sz.L n)) → ℂ
Step2Gen.lean:202: def Step2Gen_UN (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) : (Fin k → Zd d (sz.L n)) → ℂ
Step2Gen.lean:383: def STthetaOpg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) : ℂ
Step2Gen.lean:1118: def STK2decaygL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop
$ python3 extract.py names   # the 29 theorems (file:line name); their statements are the pins, compiled by PinCheck above
Step2Gen:238 Step2Kern_Mss_of_kron Step2Gen:268 Step2Kern_Mss_band Step2Gen:293 Step2Kern_thetaKer_band Step2Gen:305 Step2Kern_uKer_band
Step2Gen:317 Step2Kern_ThetaN_band Step2Gen:328 Step2Kern_UN_band Step2Gen:428 bandStep2_STthetaOp Step2Gen:893 bandStep2_STgDrift
Step2Gen:901 bandStep2_STGridMartAt Step2Gen:907 bandStep2_STGridMart Step2Gen:1056 bandStep2_STgDriftN Step2Gen:1064 bandStep2_STeeUM
Step2Gen:1071 bandStep2_STGridRepNAt Step2Gen:1079 bandStep2_STGridRepN Step2Gen:1129 bandStep2_STNewKLKAt Step2Gen:1138 bandStep2_STNewKLK
Step2Kern:57 Step2Kern_Theta_comm Step2Kern:73 Step2Kern_Mss_BA Step2Kern:90 Step2Kern_thetaKer_BA Step2Kern:104 Step2Kern_BAKsolve_form
Step2Kern:112 Step2Kern_uKer_BA Step2Kern:124 Step2Kern_UN_BA NewKLKGen:416 stNewKLKAtgL'_of NewKLKGen:610 stNewKLKAtgL'_holds
NewKLKGen:617 stNewKLKgL'_of NewKLKGen:669 newKLKGenHyp_band NewKLKGen:637 stNewKLKgL_of_primed NewKLKGen:648 stK2decaygL_of_primed
NewKLKGen:749 stK2decaygL'_band   
$ python3 bridges.py   # (ii) as finally proved (name:line in Step2Gen.lean)
proved, no longer rfl/Iff.rfl (10): STthetaOp:428 STgDrift:893 STgDriftN:1056 STeeUM:1064 STGridMartAt:901 STGridMart:907 STGridRepNAt:1071 STGridRepN:1079 STNewKLKAt:1129 STNewKLK:1138
still rfl/Iff.rfl (5): STmsig:414 STLM:415 STgA:890 STstopIdx:898 STK2decay:1141
$ G1: cone of RBM3D.Chain.Step2Gen in this branch (cone.py), and the modules of main outside the branch that name a changed declaration (git grep -lw on main)
cone: RBM3D.Chain.Step2Gen 77; LWExpCert in cone: 0
main:RBM3D/BA/Step2BA.lean main:RBM3D/Chain/NewKLKGen.lean main:RBM3D/Chain/Step2Gen.lean
main's BA/Step2BA.lean (git show main:...) compiled against this branch's oleans: exit=0, errors 0
$ line numbers of the `example`s (20 in all; the narrative maps them to the targets)
Step2Gen: 1159 1165 1180 1197 1203 1210 1217 1232 1242 1275
NewKLKGen: 772 776 785 794 801 815 850
Step2Kern: 151 183 190
$ Mathlib names used (c): #check of 20 names in names.lean
exit=0, #check lines 20, errors 0
```

**Narrative.**
1. *Choice and convention* (docstring of `Step2Kern_Mss`, `Step2Gen.lean:181`): the block kernel, not the cut; `M(+) = M`, `M(−)_{xy} = conj M_{yx}`; `M^{(σσ')}_{ab} = W^{-d} Σ_{x∈[a],y∈[b]} M(σ)_{yx} M(σ')_{xy}`; slot `i` of a `k`-loop uses `(σ_i, σ_{i+1})` (`finRotate`), so slot 1 of `STthetaOpg` has `(σ₁, σ₀)` (the bridge uses `mul_comm`). `thetaKer = (M S) Θ_t(M S)`; `Step2Kern_Theta_comm` turns it into `BATheta * BAMss` at `S = 1`. Only `FlowFM.M`, `S` are read: no field, `Carrier.lean` is not in the diff list.
2. *In place.* Redefined: `Step2Gen_thetaKer/_uKer/_ThetaN/_UN` (now over `C : FlowFM sz` and charges), `STthetaOpg`, and the call sites in `STgDriftNg`, `STeeUMg`, `STGridRepNAtgL` (last clause). `Step2Gen_Theta` moved up with unchanged text. `STgDriftg`, `STGridMartAtgL/gL`, `STGridRepNgL`, `STNewKLK*`, `STNewKLKAtgL'` keep their text. The ten bridges (list above) are proved; `STeeUMg` (not in the ticket's list) was added as (a) required.
3. *(e) `NewKLKGen`.* F7 is over `Step2Gen_thetaKer` for all four `(s, s')`; F6 stays in `NewKLKGenHyp` and is no longer read by the proof of `stNewKLKAtgL'_of`; `δ₀ = κ/2` and `C` are unchanged; the band F7 goes through `Step2Kern_thetaKer_band` and `‖μ‖ = 1`. F7 at BA (the real Θ-convolution) is T3-BA's.
4. *BAT-F2.* `STK2decaygL'` is next to `STK2decaygL`; `stK2decaygL_of_primed` is in `NewKLKGen.lean` §5, beside `stNewKLKgL_of_primed`, because its band instance uses `Ind.half_le_mE_im` (`Induction/ConArgDet`, imported by `Induction/NewKLK`). `stK2decaygL'_band` (public, `NewKLKGen.lean:749`) is not a pin of (a): the first whole-library build failed the axiom-audit scan, which found the premise `STK2decaygL'` proved by no theorem (output above); the band proof (`STK2decay d` at `κ' = κ²`; `κ ≤ Im m` gives `|E| ≤ 2 - κ²`) removes it. No registry file was edited (not writable; ticket: Registry none).
5. *Instances* (all `d = 3`, `sz0`): (b) `Step2Gen:1242` (four charge pairs, `E ≡ 0`; `Step2Kern_Mss_of_kron`, `_Mss_band`, `_thetaKer_band`, `_uKer_band`, `_ThetaN_band`, `_UN_band` applied, the `kron` hypothesis discharged by `split_injective`), `:1275` (the `kron` route); bridges at `bandStep2Mat sz0 (STflowE z0)`: `:1165` (`STthetaOp`), `:1210` (`STgDrift`, `STGridMartAt`, `STGridMart`), `:1217` (`STgDriftN`, `STeeUM`, `STGridRepNAt`, `STGridRepN`), `:1232` (`STNewKLKAt`, `STNewKLK`). (c) `Step2Kern:151` (all four charge pairs and `UN` at `k = 3`, no numeric stand-in: `Im m > 0` from `BAmF_sz0_im_pos`, `kron` from `BAMfine_sz0_kron`), `:183`, `:190` (the merged `baKsolve`'s `K` has two-loop value `W^{-d} thetaKer`). (e) `NewKLKGen:772, 776, 785, 815` (pointwise: `n = 0, E = 0, u = 1/32, D = 1, ℓ = 2, H = 0`), `:850` (BA family, statement level, F5-F9 as hypothesis). G1: `NewKLKGen:794` (`STNewKLK d` through the generic route and `bandStep2_STNewKLK`), `:801` (`STK2decay d` through `stK2decaygL'_band`, `stK2decaygL_of_primed`).
6. *Root import and probe.* `RBM3D.lean` is not edited (hub rule A step 4: `import RBM3D.Chain.Step2Kern` after the last import line); the whole-library build above used one temporary import line, restored (`git status --short`: 0 lines). `lake env lean RBM3D/Probe/T2414Pins.lean` now has 4 errors (lines 578-581: the example that refers to the removed merged generic kernels `RBM.BA.Step2Gen_thetaKer (SB d L g) μ t`, ...); the probe is the 1a artefact, never merged, not edited.
7. *G1 cone.* The branch cone of `Chain.Step2Gen` is 77 modules = 75 existing + `Step2Kern` + the probe, no `LWExpCert*`; all built by the whole-library build. Of the modules on `main` that are not in the branch, only `BA/Step2BA` names a changed declaration (docstrings; its text compiles against this branch, exit 0 above); `BASizeClaim*` and `EMn2BA` name none.

## (c) Verified Mathlib names

`Real.le_sqrt'`, `abs_le_of_sq_le_sq`, `Ring.inverse_unit`, `Ring.inverse_non_unit`, `Commute.units_inv_right`, `Commute.sub_right`, `Commute.smul_right`, `Finset.sum_boole`, `Finset.mul_sum`, `Matrix.conjTranspose_apply`, `Matrix.smul_mul`, `Matrix.smul_apply`, `Matrix.kroneckerMap_apply`, `Matrix.submatrix_apply`, `Matrix.one_apply`, `Fin.sum_univ_two`, `le_div_iff₀`, `smul_mul_assoc`, `Equiv.apply_symm_apply`, `pow_ne_zero`: each `#check`ed (script above: 20 lines, exit 0). Names verified absent: none searched. The numeric check of (c) at `g = 1/64, 1, 10` is in (a) (`max|ker - Th*Mss| ≤ 1.4e-14`); the Lean identity (`Step2Kern_thetaKer_BA`, `_uKer_BA`, `_UN_BA`) holds for every datum with `(E n + m).im ≠ 0` and is instantiated at `sz0` (`Step2Kern:151`); the `BAUN` identity (E-C1) is `Step2Kern_UN_BA`, no obstacle.

## (d) Open issues and paper-delta candidates

- `T2414a` (from (a), unchanged): `eq:Msig` (`1_2:1070`) reads `W^d tr(M(σ₁)E_a M(σ₂)E_b)`, `def:Theta_BA` (`1_2:663-664`) reads `W^{-d}Σ_{x∈[a],y∈[b]}…`; Lean uses the latter (`Step2Kern_Mss`, as `BAMss`).
- `T2414b` (from (a), extends `T2405a`, `T2405-prove.md:63`): `STthetaOpg`, `Step2Gen_thetaKer/_uKer/_ThetaN/_UN` are block-kernel forms over the carrier; also (1a-audit O5) F7 of `NewKLKGenHyp` quantifies over all four `(s, s')`, and `STK2decaygL'` has the premise `κ ≤ Im m` in place of `|E| ≤ 2 - κ` (as `STNewKLKgL'`, T2405 Amend 1).
- Open: the primed `K^{(2)}` decay `STK2decaygL'` at BA and F7 at BA are not proved here (T3-BA / the BA `K^{(2)}` ticket); the dispatcher may classify `STK2decaygL'` in `Test/Axioms.lean` (not writable here). The root needs `import RBM3D.Chain.Step2Kern` (hub). The probe stays on `t/T2414`.
- Length: (a), (a″), (a′) are 200 lines of this report (not editable here), so the whole exceeds the ticket's 200 lines; CLAUDE.md §6's limit is 300.
