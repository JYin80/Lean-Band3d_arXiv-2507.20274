Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  2 17:56:14 UTC 2026

Notation: the paper's coupling is the TeX macro `\ilambda` = `g` (paper/tex/main.tex:199), with `g = λ^{-1}` (`def:ilambda`, 1_2_Intro_model_result.tex:256). The ticket's "λ" is the paper's `\ilambda`, the quantity in `(eq:WO)`; below `lam` denotes it. `m = m_sc`, `t0 = |m(z)|^2`.

### (i) Exponent table (d = 3; constants 𝔠 = 1/6, 𝔡 = 1/10, κ = ε = 1/10; sequence `W_n=(2n)^5, L_n=4n, lam_n=(2n)^{-6}=W_n^{-6/5}`)

| Quantity | Value / source | Constraint | Slack |
|---|---|---|---|
| `N` | `(W L)^d` (TeX 1_2:`N=(W·L)^d`) | `N → ∞` | `N_1 = 2097152`, `N_n = (128 n^6)^3` |
| block size | `W^d` (`eq:blockIa`) | `d`-power, not `W^2` | `W_1^3 = 32768` |
| `W ≥ N^𝔠` (`Main_DEL_COND`, l.359) | `W^6 ≥ N` at 𝔠 = 1/6; for d = 3 equals `L ≤ W` | all n | `W_n/L_n = 8 n^4 ≥ 8` (exact: `W^6 = 2^30 n^30 ≥ 2^21 n^18`) |
| `lam` window `(eq:WO)`, l.363 | `W^{-d/2+𝔡} = W^{-7/5} ≤ lam ≤ 𝔡^{-1} = 10` | all n | `lam / W^{-7/5} = W^{1/5}` (= 2 at n=1, → ∞); `lam_n → 0` is allowed |
| `lam^2 W^d ≥ W^{2𝔡}` | equivalent to the `lam` lower bound (`lam^2 W^d ≥ W^{-d+2𝔡+d}`) | all n | `lam^2 W^d = W^{3/5} ≥ W^{1/5}`; n=1: 8 ≥ 2 |
| `(lam^2 W^d)^{-1}` (small parameter in `B_{t0,0}`, `Eq:Gtlp_exp`) | `≤ W^{-2𝔡}` | `→ 0` | n=1: 1/8; `W^{-3/5}` in general |
| Scale conversion `W^τ ↔ N^τ'` | `N = W^d L^d`, `L ≥ 1`, `W ≥ N^𝔠` ⇒ `N^𝔠 ≤ W ≤ N^{1/d}` | `W^τ ≤ N^{τ/d}`, `N^{τ'} ≤ W^{τ'/𝔠}`; so `≺` with `W^τ` and with `N^τ` coincide (all τ>0, D>0) | `log W/log N` = 0.2381 (n=1) → 5/18 ≈ 0.2778, inside `[1/6, 1/3]`; probabilities: `W^{-D/𝔠} ≤ N^{-D}` and `N^{-D'} ≤ W^{-dD'}` |
| `D_{κ,ε}` (`eq:spectral_domain`, l.380) | `|Ê| ≤ 2-κ`, `N^{-1+ε} ≤ η ≤ 1` | nonempty | n=1: `η ∈ [2.04e-6, 1]`; `Ê = 1/2 ≤ 1.9` |
| `t0`, `E` (`eq:t0E0`, l.789) | `t0 = |m|^2 = Im m/(Im m+Im z)`, `E = -2 Re m/|m|` | `|E|<2`; `1-t0 = Im z/(Im m+Im z) ≍ η` | `E ∈ [0.4449, 0.5]` over `η ∈ [N^{-0.9},1]`; `Im m(E) ∈ [0.968, 0.975]` |
| `z_t, η_t` (`eq:zt`, `eta`, l.716/720) | `z_t = E+(1-t)m(E)`, `η_t = (1-t) Im m(E)`, `|m(E)|=1` | `η_t ≍ 1-t` | `Im m(E) = |Im m(z)|/|m(z)| ≥ 0.968` on the instance; ratio `η_{t0}/(1-t0) = Im m(E) ∈ [0.9682, 0.9749]` |
| `eq:zztE` identities (l.791) | `√t0 m(E)=m(z)`, `z_{t0}(E)=√t0 z` | exact | script errors ≤ 3e-16 |
| `ℓ_t` (`eq:ellt`, l.1121) | `min(max(lam (1-t)^{-1/2},1),L)` | `1 ≤ ℓ_t ≤ L` | `ℓ_{t0} = 4 = L` (η small), `1` (η ≥ λ^2 regime) |
| `B_{t,K}` (`eq_B_param`, l.1107) | `(lam^2+1-t)^{-1}(K+1)^{-(d-2)} + L^{-d}(1-t)^{-1}`; exponent `d-2 = 1` (d=2: 0) | `ℬ_{η_t,K} ≍ W^{-d}B_{t,K/W}` (`eq:BtBt`) | with `η = 1-t0` the identity is exact: rel diff 0 (script, K = 3W) |
| `B_{0,0}` | `(lam^2+1)^{-1} + L^{-d}` | `≍ 1` | n=1: 1.0154 |
| `B_{t0,0}` | `(lam^2+1-t0)^{-1} + L^{-d}(1-t0)^{-1}` | `W^{-d}B_{t0,0} ≲ (lam^2W^d)^{-1} + (Nη)^{-1}` | n=1: `η_min`: 1.146e4, `W^{-d}B = 0.350` (≈ 0.124 + 0.226); `η=1`: 1.62 |
| `η`-regimes (l.514 `eq:BetaK`; DECISIONS §7) | `η ≤ lam^2/L^d` (`B ≍ (Nη)^{-1}`), `lam^2/L^d < η ≤ lam^2/L^2`, `η > lam^2/L^2` | each regime nonempty and meets `D_{κ,ε}` | n=1: `N^{-0.9}=2.04e-6 < 3.81e-6 < 1.53e-5 < λ^2=2.44e-4`; all three regimes realized below |
| BA flow `eq:t0E0_BA` (7_8:1798) | `λ0 = √t0 λ`, `E = (t0 Re z-(1-t0)Re m(z,λ))/√t0` | `√t0 m(E,λ0)=m(z,λ)`, `z_{t0}(E,λ0)=√t0 z` | n=1, L=4: errors ≤ 7e-16; `λ0/λ ∈ [0.611, 1)`; `λ0 ≥ 0.611 λ ≥ 1.22 W^{-7/5}` so `(eq:WO)`'s lower bound holds for `λ0` at n=1 |
| Energy along sequence (TEAM §8 lesson 23) | `E_n : ℕ → ℝ`, `E_n=E(z_n)`, `z_n = 1/2 + i N_n^{-4/5}` | `η_n ≥ N_n^{-9/10}`, `|E_n| ≤ 1.9` | `E_n = 0.5` to 8 digits for n = 1..4; `η_n/N_n^{-9/10} = N_n^{1/10} ≥ 4.2` |

Notes: `W^{-d}` replaces `W^{-2}` of RBM2D in `S`, `E_a`, `ℬ`; `B_{t,K}` carries `(K+1)^{d-2}`; none of `d`, `λ`, `E` is fixed by any row (λ → 0 and `E_n` vary along the sequence).

### (ii) Concrete nondegenerate instance

`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `W_n = (2n)^5`, `L_n = 4n` (`L ≥ 3`), `lam_n = (2n)^{-6}`, `N_n = (W_n L_n)^3`; `z = 1/2 + iη ∈ D_{κ,ε}`, κ = ε = 1/10; n = 1 below (`W=32, L=4, lam=1/64, N=2097152`).

Commands (pure-Python, scratchpad only; files `pre_compact.py`, `t2002_ba.py` in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/`):
`python3 pre_compact.py` and `python3 t2002_ba.py`

```
A: n W L lam N | W>=N^(1/6) | lam^5>=W^-7 & lam<=10 | (lam^2 W^d)^5>=W | logW/logN
1 32 4 1/64 2097152 True True True 0.2381
2 1024 8 1/4096 549755813888 True True True 0.2564
3 7776 12 1/46656 812479653347328 True True True 0.261
6 248832 24 1/2985984 212986666247081951232 True True True 0.2654
B: 1/6 <= logW/logN <= 1/3, limit 5/18: True
C: band model, n=1, Ehat=0.5, kappa=eps=0.1; columns eta, t0, E, errs[sqrt(t0)m(E)-m(z), z_t0-sqrt(t0)z]
   N^(-1+eps)=2.0442e-06 lam^2/L^d=3.8147e-06 lam^2/L^2=1.5259e-05 lam^2=2.4414e-04
   eta_min: eta=2.0442e-06 inD=True t0=0.9999978887 1-t0=2.1113e-06 E=0.50000000 errs=1e-16,2e-16,2e-16
      Im m(E)=0.9682 eta_t0=2.0442e-06 B00=1.01538 B_t0,0=1.1462e+04 W^-d*B_t0,0=0.350 ell_t0=4.00 (L=4) eta<=lam^2/L^d BtBt reldiff=0e+00
   eta_mid: eta=7.6294e-06 inD=True t0=0.9999921204 1-t0=7.8796e-06 E=0.50000000 errs=0e+00,1e-16,1e-16
      Im m(E)=0.9682 eta_t0=7.6294e-06 B00=1.01538 B_t0,0=5.9509e+03 W^-d*B_t0,0=0.182 ell_t0=4.00 (L=4) lam^2/L^d<eta<=lam^2/L^2 BtBt reldiff=0e+00
   eta=0.1: eta=1.0000e-01 inD=True t0=0.9019244075 1-t0=9.8076e-02 E=0.49933478 errs=1e-16,3e-16,1e-16
      Im m(E)=0.9683 eta_t0=9.4970e-02 B00=1.01538 B_t0,0=1.0330e+01 W^-d*B_t0,0=0.000 ell_t0=1.00 (L=4) eta>lam^2/L^2 BtBt reldiff=0e+00
   eta=1: eta=1.0000e+00 inD=True t0=0.3733080358 1-t0=6.2669e-01 E=0.44490338 errs=0e+00,1e-16,6e-17
      Im m(E)=0.9749 eta_t0=6.1099e-01 B00=1.01538 B_t0,0=1.6200e+00 W^-d*B_t0,0=0.000 ell_t0=1.00 (L=4) eta>lam^2/L^2 BtBt reldiff=0e+00
D: E_n for z_n=1/2+i*N_n^(-4/5): [(1, 0.5, True), (2, 0.5, True), (3, 0.5, True), (4, 0.5, True)]

eta=1.0000e-03 Im m(z,lam)=0.967086 resid=0.0e+00 t0=0.9989670338 E=0.4999995563 lam0/lam=0.9994833835
   Im m(E,lam0)=0.967586 resid=1.1e-16 err[sqrt(t0)m(E,lam0)=m(z,lam)]=6.7e-16 err[z_t0=sqrt(t0)z]=7.4e-17
eta=2.0442e-06 Im m(z,lam)=0.967584 resid=1.2e-16 t0=0.9999978873 E=0.4999999992 lam0/lam=0.9999989437
   Im m(E,lam0)=0.967585 resid=1.1e-16 err[sqrt(t0)m(E,lam0)=m(z,lam)]=1.2e-16 err[z_t0=sqrt(t0)z]=4.4e-17
eta=1.0000e-01 Im m(z,lam)=0.919031 resid=2.5e-16 t0=0.9018675290 E=0.4993000310 lam0/lam=0.9496670622
   Im m(E,lam0)=0.967740 resid=1.1e-16 err[sqrt(t0)m(E,lam0)=m(z,lam)]=4.5e-16 err[z_t0=sqrt(t0)z]=6.2e-17
eta=1.0000e+00 Im m(z,lam)=0.595469 resid=2.0e-16 t0=0.3732251100 E=0.4447699764 lam0/lam=0.6109215252
   Im m(E,lam0)=0.974706 resid=5.6e-16 err[sqrt(t0)m(E,lam0)=m(z,lam)]=1.1e-16 err[z_t0=sqrt(t0)z]=1.1e-16
```

External hypotheses: none in this ticket's targets (the only authorized external input, Landon–Sosoe–Yau Thm 2.2 of DECISIONS §5, is not a hypothesis of any pin here).
`eq:zztE` is a cited lemma (Lemma 2.8 of [YY_25]); the output above is its concrete verification at the instance (errors ~1e-16) and `eq:zztE_BA` likewise (BA, L=4, self-consistent `m` by Newton, residual of `(self_m)` ≤ 6e-16).

### Verdicts (stage 1a)

- Targets (item 2 pins, item 3 probe, item 6 instances): PASS. All hypotheses of the scale table hold at once at `n = 1` and, via the exact integer checks (A), at `n = 1, 2, 3, 6`; the inequalities `W^6 ≥ N`, `lam^5 ≥ W^{-7}`, `(lam^2W^d)^5 ≥ W` hold for all `n ≥ 1` by the closed forms above.
- Paper-delta candidate (naming): `T2002a` — Lean's `lam` is the paper's `\ilambda = g = λ^{-1}`; the paper's text also uses `λ` for the unscaled coupling (1_2:253, "λ ≫ W^{d/2}").

## (a′) Preflight corrections — Fri Oct  2 23:02:20 UTC 2026
One correction in (i); no verdict changes. The row "`(lam^2 W^d)^{-1}` (small parameter in `B_{t0,0}`, `Eq:Gtlp_exp`)": `Eq:Gtlp_exp` (1_2:1211) carries `(\ilambda^2 W^d)^{-1/5}`; `(\ilambda^2 W^d)^{-1}` is the quantity of `(eq:BetaK)` (1_2:514) and bounds the first term of `W^{-d}B_{t,0}` (`eq_B_param`, 1_2:1108). The row's bound `(lam^2 W^d)^{-1} <= W^{-2𝔡}` (hence `(lam^2 W^d)^{-1/5} <= W^{-2𝔡/5}`) and all verdicts stand.
```
$ sed -n "515p;1211p" paper/tex/1_2_Intro_model_result.tex | cut -c1-200
\cal B_{\eta,K}\asymp (N\eta)^{-1} \ge (\ilambda^2W^d)^{-1}, \quad \forall K\ge 0 .
 \max_{\bsig, \ba}\left|\E{\cal L}^{(2)}_{t, \bsig, \ba}-{\cal K}^{(2)}_{t, \bsig, \ba}\right|\prec \p{W^{-d}B_{t,0}}^2 \p{(\ilambda^2W^d)^{-1/5}+W^{-d}B_{t,0}}
```

## (b) Script output (commands run Fri Oct  2 22:32:21 UTC 2026 .. Fri Oct  2 22:54:47 UTC 2026; composed Fri Oct  2 23:02:20 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2002`, branch `t/T2002`)
Blocks are pasted by the generator; `cut`/`sed`/`grep` in a command is applied to the output shown; the scratch-directory paths of the commands are shortened; every command is in portmap part J (`final_run.py`, `final_extra.py`). Full signatures (item 1), one row per RBM2D file (item 4), all pins, all instances and the scripts: `docs/reports/T2002-portmap.md` (parts A, C, G, H, J). Probe: `RBM3D/Probe/T2002Vocab.lean`.

### b.1 Build, axioms (every printed declaration: portmap part F), hygiene, name clash
```
$ git rev-parse --short HEAD && git diff --stat main...t/T2002
5d2a4a8
 RBM3D/Probe/T2002Vocab.lean | 1469 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1469 insertions(+)
$ lake build RBM3D.Probe.T2002Vocab 2>&1 | grep -v "depends on axioms" | tail -3
ℹ [3294/3294] Replayed RBM3D.Probe.T2002Vocab
Build completed successfully (3294 jobs).
$ lake env lean RBM3D/Probe/T2002Vocab.lean > probe_raw.txt 2>&1; echo "exit=$?"; wc -l < probe_raw.txt; grep -c "<S>" probe_raw.txt; grep -vc "<S>" probe_raw.txt; tail -2 probe_raw.txt   # <S> = depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
      60
60
0
'RBM.Gauss.T2002Inst.W_le_size_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.size_le_W_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom " RBM3D/Probe/T2002Vocab.lean; echo "grep exit=$?"; wc -l RBM3D/Probe/T2002Vocab.lean
grep exit=1
    1469 RBM3D/Probe/T2002Vocab.lean
$ lake env lean Clash.lean   # import RBM3D and import RBM3D.Probe.T2002Vocab together (worktree = 3c11d7b): a clash would be a Lean error
import RBM3D + RBM3D.Probe.T2002Vocab: ok; constants of the probe module: 263
$ for each short name N of the 153 public pins and lemmas of the probe (T2002Inst excluded): grep -rnE "(def|theorem|abbrev|structure|instance|class|inductive|lemma) N" RBM3D --exclude-dir=Probe   # in the worktree and by git grep in main 709c5c7
same short name declared elsewhere in the worktree: 0; in main 709c5c7: 0
```
### b.2 Central pins (statements extracted by script from the compiled probe, elaborated types; all 69 pin lines: portmap part G)
```
$ lake env lean Pins.lean | sed ... | grep -E "^[0-9]+ (def|structure) RBM\.(Gauss\.|Path\.)?(<central names>) :" | sed ... | cut -c1-205   # exact command: portmap part J, final_run.py, step pins_central; 22 lines
133 structure Sizes : ℕ → Type
158 def Sizes.size : {d : ℕ} → Sizes d → ℕ → ℕ
166 def Sizes.WO : {d : ℕ} → Sizes d → ℝ → Prop
178 def Sizes.Admissible : {d : ℕ} → Sizes d → ℝ → ℝ → Prop
326 def Xmat : (d L W : ℕ) → [NeZero L] → [NeZero W] → Ω d L W → Matrix (Idx d L W) (Idx d L W) ℂ
380 def Sizes.seqP : {d : ℕ} → (sz : Sizes d) → Measure sz.SeqΩ
435 def Sizes.seqHflow : {d : ℕ} →  (sz : Sizes d) →   (n : ℕ) → ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
490 def Sizes.seqHflowBA : {d : ℕ} →  (sz : Sizes d) →   (ℕ → ℝ) → (n : ℕ) → ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
507 def ztOf : ℂ → ℝ → ℝ → ℂ
524 def Gres : {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → ℂ → Bool → Matrix ι ι ℂ
532 def Mres : {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → ℂ → ℂ → Matrix ι ι ℂ
544 def loopM : (d L W : ℕ) →  [NeZero L] →   Matrix (Vtx d L W) (Vtx d L W) ℂ → ℂ → {n : ℕ} → (Fin n → Bool) → (Fin n → RBM.Zd d L) → ℂ
557 def blockMat : (d L W : ℕ) →  [NeZero L] →   [NeZero W] →    Matrix (Idx d L W) (Idx d L W) ℂ → Matrix (Vtx d L W) (Vtx d L W) ℂ
604 def Sizes.Gt : {d : ℕ} →  (sz : Sizes d) →   (n : ℕ) → ℝ → ℝ → Bool → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
611 def Sizes.Lloop : {d : ℕ} →  (sz : Sizes d) → (n : ℕ) → ℝ → ℝ → {k : ℕ} → (Fin k → Bool) → (Fin k → RBM.Zd d (sz.L n)) → sz.SeqΩ → ℂ
869 def Sizes.Prec : {d : ℕ} →  (sz : Sizes d) → {U : ℕ → Type u_1} → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → Prop
875 def Sizes.PrecPT : {d : ℕ} →  (sz : Sizes d) → {U : ℕ → Type u_1} → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → Prop
879 def Sizes.Whp : {d : ℕ} → (sz : Sizes d) → (ℕ → Set sz.SeqΩ) → Prop
882 def Sizes.LocalLawPT : {d : ℕ} → Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
966 def RBM.Path.pathH : {d : ℕ} →  (sz : Sizes d) →   (ℕ → ℝ) →    (ℕ → ℝ) →     (ℕ → ℕ) →      (n : ℕ) →       ℕ → RBM.Path.PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
974 def RBM.Path.TransferLaw : {d : ℕ} → Sizes d → Prop
1013 def Sizes.PrecGrid : {d : ℕ} →  (sz : Sizes d) →   {U : ℕ → Type u_1} → ((n : ℕ) → U n → RBM.Path.PathΩ sz → ℝ) → ((n : ℕ) → U n → RBM.Path.PathΩ sz → ℝ) → Prop
```
### b.3 Compiled nonempty instances at the preflight sequence (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L=4, W=32, lam=1/64, N=2097152`; `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = ε = 1/10`)
```
$ lake env lean Pins_thms.lean | sed ... | grep -E "^[0-9]+ theorem RBM\.Gauss\.T2002Inst\.(<central names>) :" | sed ... | cut -c1-215   # exact command: portmap part J, final_run.py, step inst_central; 13 of 41 instance statements; every deterministic hypothesis of the applied pins is discharged; `TransferLaw`, `IndepIncr` (MD-4 targets) stay hypotheses of `transfer_at`, `indep_at`; `lam0`, `m0`, `hzt` (MA gate) of `Gt_BA_sz0`
1118 theorem sz0_admissible : sz0.Admissible (1 / 6) (1 / 10)
1143 theorem sz0_lam_tendsto : Filter.Tendsto sz0.lam Filter.atTop (nhds 0)
1168 theorem z0_mem : sz0.locDomain (1 / 10) (1 / 10) 0 z0
1175 theorem z0_zztE : (|RBM.lemE z0| ≤ 2 - 1 / 10 ∧   1 / 16 ≤ RBM.lemT z0 ∧    1 / 16 * z0.im ≤      (RBM.zt (RBM.lemE z0) (RBM.lemT z0)).im ∧     (RBM.zt (RBM.lemE z0) (RBM.lemT z0)).im ≤      (1 / 16)⁻¹ * z0.im)
1206 theorem card_Idx_sz0 : Fintype.card (Idx 3 (sz0.L 0) (sz0.W 0)) = 2097152
1238 theorem Gt_prec : sz0.Prec  (fun (n : ℕ) (x : Unit) (ω : sz0.SeqΩ) ↦   ‖sz0.Gt n (Eseq n) (1 / 2) true ω 0 0‖)  fun (n : ℕ) (x : Unit) (x_1 : sz0.SeqΩ) ↦ (etaT (Eseq n) (1 / 2))⁻¹
1261 theorem localLaw_sz0 : sz0.LocalLawPT Eseq (fun (x : ℕ) ↦ 1 / 2) fun (n : ℕ) ↦  2 * (etaT (Eseq n) (1 / 2))⁻¹
1294 theorem gridRes_prec : sz0.PrecGrid  (fun (n : ℕ) (x : Unit) (ω : PathΩ sz0) ↦   ‖Gres     (pathH sz0 (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) (fun (x : ℕ) ↦ 4) n 2 ω)     (RBM.zt (Eseq n) (1 / 2)) true 0 0‖)  f
1312 theorem Gt_timeIcc_prec : sz0.PrecPT  (fun (n : ℕ) (u : TimeIcc (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) n) (ω : sz0.SeqΩ) ↦   ‖sz0.Gt n (Eseq n) (↑u) true ω 0 0‖)  fun (n : ℕ) (u : TimeIcc (fun (x : ℕ) ↦ 0) (fu
1331 theorem loop_envelope : ∀ (ω : Omega 3 4 32),  ‖loopM 3 4 32 (Hmat 3 4 32 ω) (RBM.zt (1 / 2) (1 / 2)) ![true, false] ![0, 0]‖ ≤   (etaT (1 / 2) (1 / 2))⁻¹ ^ 2
1353 theorem Lloop_sz0 : ∀ (ω : sz0.SeqΩ) (a : RBM.Zd 3 (sz0.L 0)),  sz0.Lloop 0 (1 / 2) 0 (fun (x : Fin 1) ↦ true) (fun (x : Fin 1) ↦ a) ω = RBM.mE (1 / 2)
1362 theorem transfer_at : TransferLaw sz0 →  Measure.map    (pathH sz0 (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) (fun (x : ℕ) ↦ 4) 0 2)    (pathP sz0) =   Measure.map    (sz0.seqHflow 0     (gridTime (fun (x : ℕ) ↦ 0
1384 theorem Gt_BA_sz0 : ∀ (lam0 : ℕ → ℝ) (m0 : ℂ) (E t0 : ℝ),  0 < t0 →   lam0 0 = √t0 * sz0.lam 0 →    ztOf m0 E t0 = ↑√t0 * z0 →     ∀ (ω : sz0.SeqΩ),      ↑√t0 • Gres (sz0.seqHflowBA lam0 0 t0 ω) (ztOf m0 E t0) 
```
### b.4 Inventory (item 1; full signatures in portmap part A)
```
$ python3 invcompact.py   # RBM3D from Inv.lean (tree of `t/T2002` = main 3c11d7b), RBM2D from inv.py at c9a24cf; names and signatures: portmap A.1, A.2
RBM3D (main 3c11d7b, public definitions): Defs 11 files 2615 lines 39 defs; Gauss 5 files 1088 lines 12 defs; Loop 1 files 293 lines 5 defs; Analysis 1 files 180 lines 0 defs
RBM2D c9a24cf (file: lines, public defs): RBM2D/Gauss/Model.lean: 574 lines, 26 defs; RBM2D/Defs/StochDom.lean: 611 lines, 8 defs; RBM2D/Defs/Semicircle*.lean: 601 lines, 8 defs; RBM2D/Path/Scales.lean: 344 lines, 5 defs; RBM2D/Hierarchy/ (47 files): 5718 lines, 38 defs; RBM2D/Induction/Defs.lean: 453 lines, 36 defs; RBM2D/Induction/HierVocab.lean: 664 lines, 47 defs; RBM2D/Evolution/Defs.lean: 219 lines, 13 defs; RBM2D/Endpoints.lean: 268 lines, 20 defs
```
### b.5 Port map (item 4; one row per RBM2D file in the portmap, part C) and the sub-gates of ST
```
$ python3 mkportmap.py summary   # classes a/b/c/d defined in portmap part B; "kept" = lines at RBM2D 0c1330a, after its own dead-code deletion T2274
| RBM2D dir -> RBM3D dir | files | lines c9a24cf | lines kept 0c1330a | files a/b/c/d | lines a/b/c/d |
| Defs -> RBM3D/Defs | 7 | 2028 | 1361 | 1/1/0/5 | 611/285/0/1132 |
| Gauss -> RBM3D/Gauss | 47 | 7427 | 4669 | 19/13/0/15 | 3549/2410/0/1468 |
| Green -> RBM3D/Green | 34 | 26927 | 20318 | 9/24/1/0 | 5847/20665/415/0 |
| Hierarchy -> RBM3D/Hierarchy | 47 | 5718 | 2639 | 8/17/0/22 | 774/2457/0/2487 |
| Path -> RBM3D/Path | 42 | 31716 | 25041 | 6/19/15/2 | 2418/17704/10723/871 |
| Induction -> RBM3D/Induction | 60 | 69835 | 53876 | 2/55/2/1 | 1510/67729/492/104 |
| Evolution -> RBM3D/Evolution | 24 | 24625 | 21947 | 0/17/7/0 | 0/16772/7853/0 |
| Main -> RBM3D/Main | 9 | 4066 | 2847 | 2/7/0/0 | 147/3919/0/0 |
| Universality -> RBM3D/Universality | 56 | 60867 | 51486 | 9/47/0/0 | 7771/53096/0/0 |
| TOTAL | 326 | 233209 | 184184 | 56/200/25/45 | 22627/185037/19483/6062 |
$ python3 mkportmap.py dirlevel   # directory level only (Loop: T2004, Propagator: T2003); files / lines c9a24cf / kept / files reachable from the endpoints
Analysis: 4 / 513 / 0 / 0; (root files): 3 / 459 / 415 / 2; Loop: 16 / 16475 / 15073 / 16; Propagator: 87 / 17266 / 9553 / 56; Test: 2 / 293 / 51 / 0
$ python3 mkportmap.py groups   # sub-gates of ST in dependency order: files / lines kept at 0c1330a / files a/b/c/d (full table: portmap E)
MD: 18 / 4568 / 14/4/0/0; ST-1: 86 / 29932 / 29/56/1/0; ST-2: 46 / 31831 / 0/30/16/0; ST-3: 40 / 38991 / 2/37/1/0; ST-4: 17 / 15101 / 0/17/0/0; ST-5: 7 / 6846 / 0/0/7/0; ST-6: 9 / 3233 / 0/9/0/0; UN: 58 / 51594 / 11/47/0/0; none: 45 / 2088 / 0/0/0/45
```
### b.6 Split table (MD vocabulary tickets; sizes by `python3 mkportmap.py split`) and the first ST design tickets
* **MD-1** (`RBM3D/Defs/Sizes.lean, RBM3D/Gauss/FineModel.lean`): sources Defs/Model, Gauss/Model, Gauss/LinearForm (1141 / 910 lines, probe 407, est. 1317); needs none; prover-max (interface, every ST/UN ticket consumes it).
* **MD-2** (`RBM3D/Defs/StochDomAt.lean, RBM3D/Gauss/DominationAt.lean`): sources Defs/StochDom, Path/PerTime, Gauss/Domination, Gauss/MomentBridge, Gauss/Envelope, Gauss/SteinMatrix (2409 / 1108 lines, probe 142, est. 1250); needs MD-1; prover-hard.
* **MD-3** (`RBM3D/Loop/GLoopFlow.lean, RBM3D/Gauss/BlockAnderson.lean`): sources Hierarchy/Loops, Hierarchy/Operations, Hierarchy/OperationsPairWord, Path/Step2Props (849 / 728 lines, probe 347, est. 1075); needs MD-1; prover-max (interface: loops and flow data).
* **MD-4** (`RBM3D/Path/Walk.lean`): sources Path/Walk, Path/Transfer (820 / 708 lines, probe 100, est. 808); needs MD-1, MD-2; prover-hard.
* **MD-5** (`RBM3D/Path/Markov.lean, RBM3D/Path/Stop.lean, RBM3D/Path/Azuma.lean`): sources Path/Markov, Path/Stop, Path/Azuma (1361 / 1114 lines, probe 0, est. 1114); needs MD-4; prover (generic, class a).
The statements of each MD ticket are the probe pins of the same sections (portmap part E.2); `Defs/SemicircleIntegral` is T2005's, merged. `PrecGrid` sits with the carrier (MD-4); `LocalLawPT` needs `Gt` (MD-3) and `PrecPT` (MD-2) and is the pin shape for the ST design tickets, not an MD item. First ST design tickets (after this audit; each ends in pins compiled in a probe, an exponent table with the regimes `1-t ≥ g²`, `g²/L² ≤ 1-t ≤ g²`, `g²/L^d ≤ 1-t ≤ g²/L²`, and a split table):
* **ST-D1** Step 1 (`lem_GbEXP`, `lem_ConArg`, 3_5:14, 42): Green, Gauss calculus, Hierarchy, Induction/{Continuity,ConArg*,Step1}, 86 files / 29932 lines kept; new for d ≥ 3: exponents only (3_5:29-40 says the proofs are dimension-independent). **ST-D2** Step 2 (`Eq:Gdecay_w`, `eq:def2_stopping`, `lem:newKLK`, `lem: EMn2_N`, 3_5:302-899): Path, Induction/Grid*, 46 files / 31831 lines kept; new: the d ≥ 3 argument (16 class-c files), written together with the light-weight design (LW).
* **ST-D3** Steps 3-4 (`lem:STOeq_NQ`, `Def:QtPt`, `lem:iterations`, 3_5:900-1934): Induction, 40 files / 38991 lines kept; new: the case `1-s ≤ g²/L²` (`def;zero_mode_remove`, `lem: newPQ`). Later: ST-D4 Step 5 (17 files / 15101 lines kept), ST-D5 Step 6 (7 files / 6846 lines kept), ST-D6 assembly with T2001 (9 files / 3233 lines kept). Order: MD-1 first (every ticket consumes it), then MD-2 and MD-3 in parallel, MD-4, MD-5; ST-D1..D3 together once MD-1 is merged; ST-D4..D6 after the ST-D2 pins.
### b.7 Evidence: RBM2D movement and usage, `main` since the branch point, the merged Vtx model, the endpoint form, the merged norm (run in `~/Lean_proof/RBM3D` resp. the worktree)
```
$ git -C ../RBM2D --no-optional-locks log --format="%h %s" c9a24cf..HEAD | cut -c1-150; echo "RBM2D HEAD: $(git -C ../RBM2D --no-optional-locks rev-pars ...
79985ee Dispatcher V2: DECISIONS 247, T2279 and its check file
0c1330a Dispatcher V2: DECISIONS 246, bookkeeping (T2273, T2274), T2275-T2278 and their check files
99d6fe0 T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)
RBM2D HEAD: 79985ee; lines of diff --stat 0c1330a HEAD -- RBM2D RBM2D.lean: 0
 410 files changed, 104 insertions(+), 59125 deletions(-)
 RBM2D/Defs/Model.lean       |  35 ----
 RBM2D/Defs/StochDom.lean    | 480 --------------------------------------------
 RBM2D/Gauss/Domination.lean | 385 -----------------------------------
 RBM2D/Gauss/Model.lean      | 118 -----------
 RBM2D/Hierarchy/Loops.lean  |   8 -
 RBM2D/Path/PerTime.lean     |  69 -------
 RBM2D/Path/Step2Props.lean  |  95 ---------
 RBM2D/Path/Walk.lean        |  30 ---
 8 files changed, 1220 deletions(-)
c9a24cf: blockMat: 1256 lines in 81 files
c9a24cf: splitEquiv: 383 lines in 51 files
$ git log --format="%h %s" --grep="^T2005" 3c11d7b..709c5c7 | cut -c1-100; git diff --stat 3c11d7b 709c5c7 -- RBM3D RBM3D.lean | cut -c1-90; echo "public definitions in Def ...
709c5c7 T2005: merge msc equals the semicircle integral (eq:defmzsc)
 RBM3D.lean                         |   1 +
 RBM3D/Defs/SemicircleIntegral.lean | 255 +++++++++++++++++++++++++++++++++++++
 2 files changed, 256 insertions(+)
public definitions in Defs/SemicircleIntegral.lean at 709c5c7: 0
189:theorem msc_eq_integral {z : ℂ} (hz : 0 < z.im) :
$ git grep -lE "Vtx|Hmat|Omega d L W|Gauss.Model" 709c5c7 -- RBM3D | sed "s/^709c5c7://" | sort; git grep -nE "Vtx|Hmat|Gauss.Model" 709c5c7 -- RBM3D/Ba ...
RBM3D/Basic.lean
RBM3D/Gauss/Model.lean
RBM3D/Gauss/SteinMatrix.lean
RBM3D/Loop/GLoop.lean
RBM3D/Basic.lean:49:* `RBM3D.Gauss.Model`        — `(bandcw0)`/`(eq:variancematrix)`: the ensemble, and resamp
RBM3D/Gauss/SteinMatrix.lean:37:`S^(B)` -- which this project does not have yet.  It is not a port: `RBM1D/Gau
uses of Gauss.P outside Gauss/Model.lean: exit=1
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Endpoints.lean | sed -n "99p;102p;104p" | cut -c1-110; sed -n "389p" paper/tex/1_2_Intro_model_result.tex | cut -c1-150
def locSC : Prop :=
      ∀ᶠ n in atTop, ∀ z : ℂ, locDomain (d.size n) κ τ z →
        seqP d {ω | ¬ ∀ x y : Idx (d.L n) (d.W n),
&\bigcap_{z=\hat{E}+\ii\eta\in \mathbf D_{\kappa,\e}}\bigcap_{x,y\in \ZL} \left\{ |G_{xy}(z) - M_{xy}(z)|^2  \le W^\tau  \mathcal B_{\eta,|x-y|}\right
$ sed -n "14,15p;71p" RBM3D/Defs/Lattice.lean | cut -c1-110
`|a - b|` for the distance between two points.  Section 2.1 notes that the choice of
norm is immaterial, so we fix the periodic `ℓ¹` distance: coordinatewise graph
def zdistD (d L : ℕ) (x : Zd d L) : ℕ := ∑ i, zdist L (x i)
```
### b.8 The hard constraints of item 2 and the pins that meet them (the auditor checks each against the probe; instances not shown in b.3: portmap H)
| constraint | met by |
|---|---|
| `d` a parameter, `3 ≤ d` only where needed; `N = (WL)^d`; block size `W^d` | `Sizes d`, `Sizes.size`, `Sizes.card_Idx` (`#Idx = size`), `card_Iblk` (`#block = W^d`); the grep below finds `3 ≤ d` nowhere and `0 < d` only in `W_rpow_le`; instances at `d = 3` |
| `λ` a sequence with `(eq:WO)`, never fixed | field `Sizes.lam : ℕ → ℝ`, `Sizes.WO`, `Sizes.Admissible`; instances `sz0_admissible`, `sz0_lam_tendsto` (`lam → 0`), `sz0_lam_sq` |
| energies are `E : ℕ → ℝ` | `Sizes.LocalLawPT (E t : ℕ → ℝ)`, instance `localLaw_sz0` along the non-constant `Eseq n = 1/(n+2)`; `Gt_prec`, `Gt_whp`, `gridRes_prec`, `Gt_timeIcc_prec` also use `Eseq`; matrix-level `Gt`, `Lloop`, `Gn` take one `E` (TEAM §8 lesson 23) |
| one scale for every `≺`; conversion of `W^τ` | `Prec`, `PrecPT`, `PrecGrid`, `Whp`, `LocalLawPT` all at `sz.size`; merged `StochDom` is `StochDomAt id` (`stochDom_iff_at_id`); `W_rpow_le`, `size_rpow_le_W_rpow`; instances `W_le_size_sz0`, `size_le_W_sz0` |
| names: `d` is the dimension | `sz : Sizes d` (rule R1 in b.9); new public names and clashes: b.1 |
| block Anderson fits or gets a layer | same vocabulary: `seqHflowBA`, `seqHBA`, `PsiI`, `Mres`; `Gt_BA` compiled; the deterministic layer is separate (b.9) |
```
$ grep -nE "3 ≤ d|0 < d|^  (lam|three_le_L) : " RBM3D/Probe/T2002Vocab.lean | cut -c1-90
147:  lam : ℕ → ℝ
148:  three_le_L : ∀ n, 3 ≤ L n
223:theorem W_rpow_le (hd : 0 < d) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
```
### b.9 Decisions, one row per object (keep = merged RBM3D, port = RBM2D `c9a24cf`, bridge = both)

| object | decision (probe pins) | reason, paper line |
|---|---|---|
| Index type, blocks | **bridge both**: fine lattice `Idx d L W = Zd d (W*L)` carries the model and the statements (port RBM2D `Idx`); block-product `Vtx d L W = Zd d L × Fin (W^d)` (keep) carries `E_a`, `S`, loops; bridges `splitEquiv`, `blockMat`, `svarF_eq_svar` | `(G_bound)` is at `x,y ∈ Z_{WL}^d` with `|x-y|` (1_2:262-275, 388-389); RBM2D's chain: `blockMat` in 81 files (b.7); probe `Idx, split(Equiv), Iblk`, `card_Iblk = W^d`, `Sizes.card_Idx` |
| Distance `\|x\|` | **keep both**: `zdistD` (l1, merged, propagator side); new `zdistInf` (L^inf) for stochastic and endpoint statements | paper fixes L^inf (1_2:274); merged `Defs/Lattice.lean:14-15` fixes l1 (b.7); `zdistInf ≤ zdistD ≤ d·zdistInf` compiled; T2002b |
| Size sequence, `λ` | **port + extend**: `Sizes d {L W lam three_le_L W_pos}`, `size n = (W n·L n)^d`, `WO`, `Bandwidth`, `SizeTendsto`, `Admissible 𝔠 𝔡`, `withLam`; `lam : ℕ → ℝ` unconstrained except `WO` | RBM2D `Sizes` (Gauss/Model.lean:405) has no coupling; `lam` = paper's `\ilambda` (macro for `g`, `main.tex:199`) = the `g` of merged `SB, ellT, Bparam` |
| Probability space, model | **port**: one countable product `seqP sz` over `Σ n, CoordF d (L n) (W n)`; one-size law `PF`; merged `Gauss.P` (Vtx, finite `Measure.pi`, fixed sizes) kept, not used outside `Gauss/Model.lean` (b.7) | `StochDom` needs one probability space while merged `Gauss.P` has one per size (RBM3D DECISIONS §10 T2001i-k); RBM2D has the same `seqP` (`Gauss/Model.lean:434`); `seqP_map_slice` compiled; `S` from merged `SBR` (`svarF_eq_svar`) |
| `H`, flow `H_t`, path carrier | **port**: `Xmat`, `seqXmat sz n ω`; single time `seqHflow sz n u ω = √u • seqXmat` (the definition here; RBM2D has `Hflow` at `Gauss/Model.lean:327` and `seqHflow_eq_smul` = `rfl` at `:499`); grid walk `PathΩ, pathP, filt, gridStep, gridTime, pathH` with pins `TransferLaw`, `IndepIncr`; stopping times only where the paper stops (`Sol_CalL`, `lem:DIfREP`, `eq:def2_stopping`); Azuma+Doob replace BDG | DECISIONS §7; (bandcw0) 1_2:296, (MBM) 1_2:686; merged `Hmat` kept; the single-time law makes `zztE` pointwise (`Gt_lemT`) |
| `m`, `z_t`, `η_t` | **keep + bridge**: merged `mE`, `msc`, `lemE`, `lemT`, `zt`, `Gauss.etaT`; generic `ztOf m E t`, `etaOf m t` (`zt_eq_ztOf` is `rfl`); `m(z)` as the integral: ported by T2005 (`msc_eq_integral`, merged after this branch point, b.7) | BA: `m(E, λ_0)` is data; RBM2D `Path.etaT` not ported: merged `Gauss.etaT` is the single `η_t` (RBM2D kept two equal copies, `RBM.KLoop.etaT` and `RBM.Path.etaT`, bridged by its T2042; RBM2D DECISIONS §14) |
| `G_t(σ)`, `G(z)`, `E_a` | **bridge**: generic `Gres H z σ`; `Sizes.Gt`, `Gn` (entries on `Idx`); merged `Gsig` is `Gres (Hmat ω) (zt E t)` (`Gsig_eq_Gres`, `rfl`): the time-one matrix only; `E_a`: keep merged `Gauss.Eblk` (`trace_Eblk = 1`) | (def_Green) 1_2:336, (Eq:defGLoop) 1_2:824 |
| `𝓛^{(n)}_{t,σ,a}` | **bridge**: `loopM d L W H z σ a` (`Fin`-indexed; merged `gloop` = `loopM (Hmat ω) (zt E t)`, `rfl`); `loopFine` via `blockMat`; `Sizes.Lloop`; list form `loopL`, `loopOf` ↔ merged `RBM.Loop.LoopIdx` | `Lloop_zero_one`: `𝓛^{(1)}_{0,σ,a} = m(σ)`, i.e. `K^{(1)}` (Def_Ktza, 1_2:988) |
| Hierarchy, `Def:oper_loop` | **port, no Itô**: `cutGlue` (RBM2D `Hierarchy/Operations.lean:27`, class a); merged `cutGlueL/R`; `lem:SE_basic` replaced by the one-step expansion on the grid walk (RBM2D Path/OneStep, Expansion; b) and per-time Stein identities (b) | DECISIONS §7 |
| `≺`, scale, w.h.p. | **port + one scale**: `StochDomAt P size`, `HighProbAt`, `PerTimeDomAt`; `Sizes.Prec`, `PrecPT`, `PrecGrid`, `Whp` all at `N = sz.size n = (W n L n)^d`; merged `StochDom`, `HighProb` are the case `size = id` (`stochDom_iff_at_id`, `highProb_iff_at_id`) | `(stoch_domination)` itself uses `N^τ`, `N^{-D}` (1_2:229); RBM2D re-pinned its chain once (DECISIONS §214, §216); `W^τ ≤ N^{τ/d}` always and `N^τ ≤ W^{τ/𝔠}` under `W ≥ N^𝔠`, so `≺` at scale `N` ⟺ the paper's `W^τ` statements |
| Energies | sequences `E : ℕ → ℝ`, `\|E n\| ≤ 2-κ` in every sequence-level statement (`LocalLawPT`); matrix-level objects take one real `E` (RBM2D practice) | TEAM §8 lesson 23 |
| Block Anderson | **same vocabulary**, three differences: law `seqP (sz.withLam 0)` (`S^{(B)}(0)=I`), shift `H_0 = lam0•PsiI` (`seqHflowBA`, `seqHBA`), data `m, M` from `(self_m)`, `(def_G0)` (`Mres (lam•Ψ) z m`, `M ≠ m I`); separate layer only for the deterministic `m(z,g)`, `M^{(B)}`, `e_g` (MA gate) | 1_2:606-633; `Gt_BA` compiled; `Mres_zero_msc`: band `M = m I` |
| Controls | **keep merged** `ellT`, `Bparam`, `BparamR`, `tailT`; add `Bctl = W^{-d}B_{t,0}` as the single control; RBM2D `scaleM`, `Path.ellT` (d=2) not ported | (Eq:L-KGt) 1_2:1196, (con_st_ind) 1_2:1296, (eq:ellt), (eq_B_param) |

Renaming rules for ports: **R1** `d : Sizes` → `sz : Sizes d`; the dimension `d : ℕ` is a leading explicit argument of every ported declaration that mentions `Z2`, `Idx`, `Sizes`, `W^2`, `L^2`, `(W*L)^2` (fields `sz.L n`, `sz.W n`, `sz.lam n`, `sz.size n`). **R2** `Z2 L → Zd d L`, `Idx L W → Idx d L W`, `BlockIndex L W → Vtx d L W`, `zdist2 → zdistD` (l1) or `zdistInf` (L^inf), `LoopIdx → RBM.Loop.LoopIdx`, `spectralM, spectralZ → mE, zt`, `Path.etaT → Gauss.etaT`, list `Gsig/gloop → Gres/loopL`. **R3** `W^2 → W^d`, `(W⁻¹)^2 → ((W:ℝ)^d)⁻¹`, `L^2 → L^d`, `(W*L)^2 → (W*L)^d`, five-point `S^(B)` → `S^(B)(g)` with `g := sz.lam n`, `Path.ellT L u → ellT L (sz.lam n) u`, `scaleM → (Bctl)⁻¹`. **R4** clashes with merged `RBM.Gauss.*`: `Coord → CoordF`, `svar → svarF`, `gvar → gvarF`, `P → PF`; other public names keep their RBM2D name; unpinned helpers `private` or stem-prefixed (CLAUDE.md §3 (E)).
### Narrative (at most 40 lines)
1. Delivered: probe `RBM3D/Probe/T2002Vocab.lean` (1469 lines; `lake build` prints "Build completed successfully" and `lake env lean` exits 0 (b.1); 69 pin lines and 41 instance theorems of `T2002Inst`, central ones in b.2-b.3; axioms standard on every printed declaration), hard-constraint table (b.8), decision table (b.9), inventories (b.4, portmap A), port map of 326 RBM2D files (233209 lines at `c9a24cf`) with classes a/b/c/d = 56/200/25/45 (b.5, portmap C), split tables (b.6).
2. Route: RBM2D's (DECISIONS §7): one countable Gaussian product over the sizes, the single-time flow `H_u = √u X` wherever the paper uses no stopping time, the grid walk on `pathP` where it stops. The carrier is on the fine lattice `Z_{WL}^d`, the loops on the block-product index, bridged by `splitEquiv`; `svarF_eq_svar` and `Sizes.card_Idx` (`#Idx = N`) tie the fine-lattice model to the merged one.
3. Finding (merged code): `Gauss.Gsig`/`gloop`/`loopMax` are built on `Hmat ω`, the time-one matrix (`Gsig_eq_Gres` is `rfl`); they are not the `G_t` of a flow matrix. The generic `Gres`/`loopM` removes this and `gloop_eq_loopM` is `rfl`, so the merged envelope `norm_gloop_le` applies at the merged model (`loop_envelope`). The Vtx model (`Gauss.Model`) is used in code only by `Loop/GLoop.lean` (the other two files of the b.7 grep mention it in comments); it is kept.
4. Finding (RBM2D and main moved): RBM2D `HEAD` was `79985ee` when b.7 was run, 3 commits after the ticket's `c9a24cf`; `99d6fe0` is its own dead-code deletion (82 modules removed, 328 trimmed), and its Lean tree equals that of `0c1330a` (diff lines: 0). The port map keeps `c9a24cf` as ticketed and adds the kept-line column at `0c1330a`: 184184 of 233209 lines in the nine directories survive. Of the 326 files of the nine directories, 17 are unreachable in my import closure (`closure.py`), 17 of them were deleted by `99d6fe0`, and 21 further files that my closure reaches by imports were deleted as whole-dead modules (T2274 report: 82 whole-dead modules in all). `main` was at `709c5c7` then; T2005 added `Defs/SemicircleIntegral.lean` (`msc_eq_integral`, no definition; b.7), so the portmap lists the RBM2D file of that name as class d and MD-3 does not own it.
5. Finding (endpoint form): the paper's `(G_bound)` intersects over `z ∈ D_{κ,ε}` inside the probability (1_2:388-389, b.7); RBM2D's `locSC` has `∀ z` outside the probability (b.7), the inside form being the endpoint gate's duty (RBM2D DECISIONS §16, §17: `RegionUnifOfPT`), and `99d6fe0` deleted as dead code `Path/NetLift.lean` (1784 lines, lift from per time to uniform in `u`) and `Main/RegionUnif.lean` (950 lines, lift over the spectral region). With T2001b of RBM3D (DECISIONS §10: paper form) these two return (marked b in the portmap).
6. Compiled consistency checks: `Lloop_zero_one`: `𝓛^{(1)}_{0,σ,a} = m(σ)` under `E_a = W^{-d}1(x=y∈[a])`, `z_0 = E+m^{(E)}`, `tr`; `Gt_lemT`: the third clause of `(eq:zztE)` holds pointwise for `H_u = √u X` (an identity, not a coupling); `Gt_BA`: the same for the block Anderson flow given `λ_0 = √t_0 λ`, `z_{t_0}(E,λ_0) = √t_0 z`; `Mres_zero_msc`: band `M = m I`; `stochDom_iff_at_id`: merged `StochDom` is `StochDomAt id`.
7. Scale and `λ`: the one scale is `N = sz.size n = (W n L n)^d` (the paper's own `≺` uses `N^τ`, `N^{-D}`); `W_rpow_le`, `size_rpow_le_W_rpow` convert `W^τ ↔ N^τ'`; `Sizes.lam : ℕ → ℝ` is constrained only by `WO` (`lam_n → 0` in the instance). Block Anderson fits the band vocabulary (b.9); the deterministic layer (`m(z,g)`, `M^{(B)}`, `e_g`) supplies `m0`, `hzt`, `hlam0` of `Gt_BA`.
8. Limits: (a)/(b) is a token rule (portmap B), (c) is a hand list to be confirmed by the ST design tickets; `kept` is RBM2D's own dead-code result for the d = 2 route; no RBM2D proof was checked beyond its header and token statistics; `three_le_L` and `W_pos` are fields of `Sizes` (all `n`), not eventual conditions.

## (c) Verified Mathlib names used (`#check`; all names of the probe in the portmap part I)
`finFunctionFinEquiv` : {m n : ℕ} → (Fin n → Fin m) ≃ Fin (m ^ n)
`MeasureTheory.Measure.eq_infinitePi` : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → MeasureTheory.
`Matrix.inv_smul` : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : M
`Matrix.nonsing_inv_eq_ringInverse` : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : M
`Matrix.IsHermitian.submatrix` : ∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : Star α] {A : Matrix n n α}, A.IsHermitian → ∀ (f 
`Matrix.conjTranspose_kronecker` : ∀ {R : Type u_1} {l : Type u_2} {m : Type u_3} {n : Type u_4} {p : Type u_5} [inst : CommMagma R] [inst_
`Matrix.conjTranspose_sum` : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : StarAddMonoid α] {ι : 
`Matrix.IsHermitian.add` : ∀ {α : Type u_1} {n : Type u_2} [inst : AddMonoid α] [inst_1 : StarAddMonoid α] {A B : Matrix n n α}, A.
`Matrix.conjTranspose_smul` : ∀ {m : Type u_2} {n : Type u_3} {R : Type u_4} {α : Type u_1} [inst : Star R] [inst_1 : Star α] [inst_2 
`Real.one_le_rpow` : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
`MeasureTheory.measure_empty` : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α]
```
$ lake env lean Deprec.lean 2>&1 | grep -o "warning: .*" | cut -c1-120   # #check @Set.mem_setOf_eq; #check @if_true; #check @ite_true; #check @Set.mem_ofPred_eq
warning: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: `if_true` has been deprecated: Use `ite_true` instead
```

## (d) Open issues and paper-delta candidates
* **O1 port source commit**: the ticket pins RBM2D `c9a24cf`; `HEAD` (`79985ee` when b.7 was run) has the trimmed Lean tree of `0c1330a` (b.7). The dispatcher should fix the commit that MD/ST tickets cite (CLAUDE.md §5.2), with the NetLift/RegionUnif caveat (narrative 5). **O2 endpoint form**: DECISIONS §10 (T2001b) fixes the paper's form (`∩_z` inside `P`), so the two lifts RBM2D deleted (`Path/NetLift.lean`, `Main/RegionUnif.lean`) are needed (class b in the portmap; MA-gate obligation); the vocabulary has `Prec` (union inside `P`) and `PrecPT` (per time).
* **O3 Step 2**: the d ≥ 3 argument has no sister-project source (DECISIONS §7; the 16 class-c files of ST-D2 are the d = 2 version to be replaced) and needs the light-weight design (§7, `lem:LWterm`, `lem: EMn2_N`) at the same time. **O4 MA gate**: `m(z,g)`, `M^{(B)}`, `e_g` and the clauses `λ_0 = √t_0 λ`, `z_{t_0}(E,λ_0) = √t_0 z` are inputs of `Gt_BA`; no probe pin proves them. **O5 merged files**: `Gauss/Model.lean` (Vtx model, finite `Measure.pi`) and the `ω`-based part of `Loop/GLoop.lean` stay; supersede only with the dead-code tool at the end (TEAM §9.13).
* **T2002a** (naming): `lam` is the paper's `\ilambda`, printed `g` (`main.tex:199`, `def:ilambda` 1_2:256); the text also uses `λ` for `\ilambda^{-1}` (1_2:253). **T2002b** (norm): the paper uses L^inf (1_2:274), merged `Defs/Lattice.lean:14-15` says the norm is immaterial and fixes l1; `e^{-(|a|/ℓ)^{1/2}}` and `B_{t,|a|}` carry fixed constants, so statements use `zdistInf`. **T2002c** (necessary condition): `three_le_L` in `Sizes` (as merged `Defs/Block.lean` and RBM2D); the paper only says `L` even (1_2:269); already signed as part of T2001a (DECISIONS §10). **T2002d** (convention): `ZMod (W*L)` with zero-based blocks `[a] = a.val·W + {0..W-1}` versus the paper's `⟦-WL/2+1, WL/2⟧` and `⟦(a(i)-1)W+1, a(i)W⟧` (1_2:262-267): equivalent by a translation, the model reads only block labels. **T2002e** ("N sufficiently large", 1_2:366) is `∀ᶠ n` along the sequence and `N → ∞` is explicit (signed as T2001a, DECISIONS §10). **T2002f** (merged docstring): the module doc of `Loop/GLoop.lean` (line 17) writes `G_t(+) = (H_t - z_t)^{-1}`, but `Gsig` takes `Hmat ω`, the matrix `H` at time one, for every `t` (narrative 3). **T2002g** (Lean writing, route of DECISIONS §7): the flow `(MBM)` (1_2:686) is carried by the single-time law `seqHflow` and, where the paper uses stopping times, by the grid walk `pathH` on `pathP` (independent increments; BDG replaced by Azuma and Doob); all sizes live on one product space `seqP` (every size has the one-size law, `seqP_map_slice`); per-time `≺` (`PrecPT`) has the union over `u` outside `P`; the paper lifts to all `z` by an `N^{-C}`-net (1_2:1228), RBM2D by `Path/NetLift.lean` (time) and `Main/RegionUnif.lean` (spectral region) (narrative 5; MA gate, DECISIONS §10 T2001b). **T2002h** (Lean writing): `G(z) = (H - z)⁻¹` is `Ring.inverse (H - z • 1)` in `Gres` and `Mres` (a total function, equal to the inverse whenever it exists, in particular for Hermitian `H` and `Im z ≠ 0`, `isUnit_sub_smul_of_isHermitian`). **T2002i** (equivalent form): the paper's `(G_bound)`, `(G_bound_ave)` carry `W^τ` (1_2:388-393) while its `≺` carries `N^τ` (1_2:229); the pins use `N^τ` throughout, and under `W ≥ N^𝔠` with `W^d ≤ N` the two are equivalent (`size_rpow_le_W_rpow`, `W_rpow_le`).
