Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 01:27:18 UTC 2026

Scripts (Python, no Lean) in `$SCR` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2483/`: `inst.py`, `c2.py`, `rad.py`, `lines.py`. `BASelf`: `m = L^-d tr(gΨ-(z+m))^-1`, `Ψ` = adjacency of `Z_L^d` (`MFixedPoint:193,197`).

### (i) Exponent table (`d = 3`; Λ = 𝔡⁻¹; `a` = lwTail32 exponent `n_M+n_V+1`, `b` = D)
| # | quantity (source) | value | constraint | slack |
|---|---|---|---|---|
| 1 | `BAct_rate d Λ κ = min(log(1+κ/(4dΛ)), κ/2)` (`CombesThomas:45`; `BAct_rate_pos :52`) | `4.158e-3` at `(3, 10, 1/2)` | `>0` for all `d,Λ,κ>0`; decreasing in Λ, so the sup of every threshold is at `Λ = 𝔡⁻¹` | 168 grid points, 0 violations (c2.py) |
| 2 | `c = min(min c₁ BAp5s_rate) 1` of `BAMomentGen_consts :364` (`c₁` existential, `BAAtom_decay_E`) | `≤ BAp5s_rate = 1.287e-32` at `(3,10,1/2)` | depends on `(d,Λ,κ)` only; used as tail rate `e^{-c r/2}` | `c ≤ BAct_rate` by 10²⁹ here (so O4 numbers understate, row 6) |
| 3 | quantifier of the coupling: `BAflow_real` (`GreenSchur:59`): `BAReal` for **every** `n`; `BAflow_lam0_window` (`:72`): `0<g₀ₙ≤𝔡⁻¹` for `∀ᶠ n`; `PrecL` puts `∀ᶠ n` after all constants | L40-C2 **case (b)** | constants `(C,c,Kd)` from `(d,Λ,κ)`, `K_c` from `(p,ε₀,𝔠,D)`: none depends on `n`, `t`, `E`, `g₀ₙ` | no threshold depends on a sequence element; L5 reads `lwMomentExp_holds` only (T2472-1a-audit §7), i.e. the pin as stated (`∀ κ ε 𝔡>0`) with constants fixed before the sequence; no uniformity in `𝔡` and no wider range |
| 4 | radius `r = Krad (log W)^{3/2}`, `Krad = K/K_c`, `K = 1`; `K_c = 1 + Σ card(E'⊕I')` over `outs++errs` of `ba_localregularXP p (ε₁/2) ⌈1/𝔠⌉ d ((D+1)/𝔠)` (band `LWMomentExp:1325-1327`) | finite, fixed before the sequence | `card·r ≤ K(log W)^{3/2} ≤ K(log W)^{3/2} ℓ_t < zdistInf ≤ lwBdist` (`one_le_ellT Params:39`, `zdistInf_le_zdistD`) | `ℓ_t = 1.0000` at the instance (equality case of `ℓ_t ≥ 1`) |
| 5 | `lwTail32` (`LWXiExp:81`): `ln W ≥ (2A/(𝔠·c·Krad))²`, `A = a+b` | `1.5e21 / 2.4e47 / 2.8e66` (`𝔠=1`, `A=16`, `K_c=1`, `g=1/64,1,10`, `c = BAp5s_rate`); `×36` at `𝔠 = 1/6`; scales as `K_c²` | `∀ᶠ n` only (`W ≥ N^𝔠`, `N → ∞`) | used by no instance: `PrecL` is eventual |
| 6 | O4 recomputed (`c2.py`, `c = BAct_rate`, `κ = Im m`, `Λ = g`, `D = 10`, `N = 5`) | `ln W0 = 4.4e2 / 4.9e4 / 5.5e6` (η = 0.1), `1.0e3 / 1.2e5 / 2.3e7` (η = 1): the T2472 numbers reproduce | with `c = BAp5s_rate` (row 2): `1.5e20 / 2.4e46 / 2.8e65` (η = 0.1), `3.4e26 / 8.3e52 / 8.5e76` (η = 1) | finite for each `(d,Λ,κ)`; asymptotic only |
| 7 | `ρ = (2K+1)(log W)^{3/2}`, `R = K (log W)^{3/2}` (`lwMomentExp_rad :738`; `BAZetaExpClaim :83`) | `√ρ ≤ τ log N` for all `τ` eventually (rad.py: `τ=0.1` from `m ~ 10^46`) | `BAGbyZeta` (`BAAuxGraph2B:586-594`): `ρ-2R = (log W)^{3/2} ≥ K' log W` | holds once `log W ≥ K'²` (`K'=10`: `m ~ 10^8.4`) |
| 8 | `ℓ ≤ (log W)^10 ℓ_t` (`LWAssmExpgL`, `Chain/LWGen:72`); `Λ_ℓ = (log W)^10`, `X ≥ Λ_ℓ²` (`lwMomentExp_arith :780`, imported) | `(log W)^10 = 2.5e5` at `W = 32` | polynomial in `log W`, absorbed by `N^σ` | `ℓ = (log W)^{3/2} = 6.45 ≤ 2.5e5` |
| 9 | regime (A) `regA d K` (`LWMomentExpA:49`), loss `(C e^{√(K(log W)^{3/2})})^q ≤ N^σ` (`lwMEA_loss :270`, model-free) | pair part of `¬regA` nonempty along `sz0` from `n = 57` (`ℓ` up to `(log W)^10 ℓ_t`) (`L=232`, `⌊L/2⌋=116 > 115.874`) | `K>0` arbitrary; assembly at `K = 1` | at `n = 0` (`L=4`) every pair is in `regA`: the instance is the sequence, not a single `n` |
| 10 | window: `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` (`LWWindow`, `LWPsi:47`); `ε₁ = min(ε₀, dc/2)`, `c = min(2𝔡𝔠,ε)/2` (`lwMEA_assm :127`) | `ε₀ = 1/10`: `W^{-1.5} = 5.5e-3 ≤ W^{-0.1} = 0.71` at `W = 32` | `ε₀ ≤ d/2` | 1.4 |
| 11 | black waved edges `p ≤ n_{W,black}` (`BAEngineProv`, `BAProv`), `t<1`, `p` even | `t^{n_W-p} ≤ 1` | `n_W ≥ p` | exact (`p=2`: `n_W ≥ 2`) |
| 12 | `2p ≤ ord`, `n_M ≤ p` (`BALocRegConcl`), only for `𝓜_x ≠ 𝓜_y`; `x ~ y` has `ext1 ∈ mol(ext0)` (`BALocReg1:304`), so it goes to row 4 | — | `BAMomentGen_scalemole :738` needs only `Sum.inl b ∈ Γ.mol (Sum.inl a)` and `card·r < lwBdist` | weighted form: `‖valW‖ ≤ Σ‖term‖` since `\|Wt\| ≤ 1` (`BAGraph.valW`, `BAProv:52`) |

### (ii) One concrete nondegenerate instance
`d=3`, `sz0` at `n=0` (`L=4`, `W=32`, `lam=1/64`, `N=2097152`; `Defs/Sizes:260-267`), `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`FlowPins:1214`), `z=z_S(4,1/64)`, `t ≡ 1/2`, `p = 2`, `D = 1`, `Dm = {0}` (and `univ`), `Wt = Π_k 1_{Dm}`, `ℓ = 1`; `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `Λ = 10`. Targets 1 (a)-(e), 4 (a), 5 use the data-level flow point `(g₀,E,m₀)` below; 2, 3, 9 use `flow_sz0`.
```
$ cd $SCR && python3 inst.py
size N = 2097152 (sz0_values: 2097152) | W >= N^c: True N^c = 11.314
z0 = 0.000000+0.367512i  Im z0 in [N^(-1+eps), 1]: True (N^(-1+eps) = 2.044e-06)
Im m(z0) = 0.832488 >= kappa=1/2: True
t0 = 0.693740  (t = 1/2 <= t0: True, t0 < 1: True)
g0 = 0.013014  (0 < g0 <= Lam = 1/dd = 10: True)   E = 0.000000   |E|<2: True
BASelf residual at (g0, E, m0): 4.44e-16 ; m0 = -0.000000+0.999493i ; Im m0 >= kappa: True
window lam^2/L^2 = 1.526e-05 < 1 - t = 0.50: True
ellT = 1.0000 (>=1), (log W)^10 = 2.500e+05  => l=1 and l=(log W)^(3/2) are admissible l in LWAssmExpgL
BAct_rate(3, 10, 1/2) = 0.004158 > 0 ; BAp5s_rate = 1.287e-32
p = 2: 2 | p ; Dm = {0}: |Wt| <= 1 (indicator) ; D = 1 > 0
first n+1 = m with some |a-b|_inf > K (log W)^(3/2) ell_t (K=1): m = 58 (n = 57), L = 232, W = 21003416576, floor(L/2) = 116 > 115.874
```
Hypotheses hold at once for: target 4 (a) (`BAReal d L g₀ κ E m` with `0 ≤ t<1`, any real `Wt`); target 5 (`g₀ ≤ Λ`, `\|Wt\| ≤ 1`, `rep` from `BACoverBy.rep`, `Dm={0}`); targets 2, 3, 9 (`3 ≤ d`, `κ,ε,𝔡>0`, `2 ∣ p`, `t ≤ BAflowT0`, `ε₀>0`, window, `ℓ` bounds); `BAAnpAuxG 3`, `STInitialGT2gL`, `LWLoopExpgL` stay hypotheses. **Limit computations** (external/eventual hypotheses):
```
$ cd $SCR && python3 c2.py
grid points 168; rate<=0 or p5rate<=0 at 0; rate(Lam) > rate(g0) for some g0 <= Lam at 0
   g=Lam   eta      Im m         rate       p5rate lam0_O4(rate) lam0_O4(p5rate)
 0.01562   0.1  0.950589   4.7529e-01   8.2740e-10    4.4341e+02      1.4607e+20
 0.01562   1.0  0.617784   3.0889e-01   5.4554e-13    1.0492e+03      3.3601e+26
 1.00000   0.1  0.554668   4.5186e-02   6.5009e-23    4.8980e+04      2.3662e+46
 1.00000   1.0  0.354845   2.9142e-02   3.4641e-26    1.1776e+05      8.3331e+52
10.00000   0.1  0.511681   4.2549e-03   1.9048e-32    5.5235e+06      2.7560e+65
10.00000   1.0  0.251349   2.0924e-03   1.0836e-37    2.2841e+07      8.5167e+75
lwTail32 threshold ln W >= (2A/(frakc*Krad*c))^2, c = p5rate (eta = 0.1), A = a+b = 6+10 = 16, Krad = 1/K_c (K_c = 1 here; scales as K_c^2):
   g= 0.01562: frakc = 1: 1.496e+21 ; frakc = 1/6 (flow_sz0): 5.385e+22
   g= 1.00000: frakc = 1: 2.423e+47 ; frakc = 1/6 (flow_sz0): 8.723e+48
   g=10.00000: frakc = 1: 2.822e+66 ; frakc = 1/6 (flow_sz0): 1.016e+68
$ cd $SCR && python3 rad.py
tau=1     sqrt(rho) <= tau log N from u = 1, m = e^u/2 ~ 10^0.1333
tau=0.1   sqrt(rho) <= tau log N from u = 106.7, m = e^u/2 ~ 10^46.04
tau=0.01  sqrt(rho) <= tau log N from u = 1.072e+06, m = e^u/2 ~ 10^4.654e+05
K'=1    rho - 2R = (log W)^(3/2) >= K' log W from u = 0.2 (log W = 1), m ~ 10^-0.2142
K'=10   rho - 2R = (log W)^(3/2) >= K' log W from u = 20 (log W = 100), m ~ 10^8.385
K'=100  rho - 2R = (log W)^(3/2) >= K' log W from u = 2000 (log W = 1e+04), m ~ 10^868.3
bandwidth c = 1/6 at m = 1: W = 32 >= N^(1/6) = 11.314; large m: (log W) / (log N) -> 5/18 = 0.2778 > 1/6
```
The thresholds are eventual (`∀ᶠ n`, `∀ τ`); no instance hypothesis uses them. The O4 numbers (raw `BAct_rate`) understate the Lean threshold by 17-70 orders of magnitude (row 2).

### Lines, split, switches
```
$ cd $SCR && python3 lines.py      # basis = band lines kept as twins (ranges in lines.py), TW 0.73/0.85/1.61, new = estimates
file  target  basis   new  central
A     hdr         0    40       40
A     1          23    90      110
A     2           0    45       45
A     3           0    12       12
A     4         121    70      173
A     5         244   260      467
A     10         78    40      106
file A: basis 466 new 557 -> low 897 / central 953 / high 1307
B     hdr         0    40       40
B     6         163    20      159
B     7         143    30      152
B     8         677    30      605
B     9          64    25       79
B     10        122    30      134
file B: basis 1169 new 175 -> low 1028 / central 1169 / high 2057
total low/central/high = 1925 / 2122 / 3364 ; split line 1950: central exceeds ; stop (third row) 3900: central below ; stop line per file 2000: central max 1169, high max 2057 ; reserve C if file > 1800: central no
TLC-4 2.6 x central = 5517 (reference only); L40-C4 fold: lighter half (central) = 953 vs 750: no fold
realized/central 1.62  T2470 (BAMomentGen+B realized 2396 vs ticket central 1480)
realized/central 0.99  T2472 (BAProv+B 877+1238 vs central 2142)
realized/central 0.71  T2469 (BALocReg2+B 886+624 vs central 2130)
central x realized/central of T2470 / T2472 / T2469: 3435 / 2095 / 1504
```
**Central 2,122 total (A 953, B 1,169)** (ticket: 2,150; ≈900 / ≈1,250). It exceeds 1,950: **the pre-signed split applies** (L3d2b-1 = `BAMomentExpGen`, targets 1-5; L3d2b-2 = `BAMomentExpGenB`, targets 6-10; own instances: (iv), (v) in A, (i)-(iii) in B). It is below 3,900: no third row, no stop. No file reaches 1,800 at central: no reserve `BAMomentExpGenC`; at TW 1.61 file B is 2,057 (> 2,000): the 1b stop line applies. L40-C4: no fold of L3d1.

**Target 5 route (correction of the ticket's route text; the pinned statement is unchanged).** `lwAuxRoot_exists_forest` on `Γ.shadow` (`AuxGraphRooted:62`) does not give the exponent count: `shadow.waved = waved ++ mdot ++ psi` (`BAAtom:65`), so a tree may use a `K₁`-waved edge where an `M`-dot (atom) edge exists; `BAAtom_sum_J` (`BAAtom:896`): the bound `K₁^{n_A-n_M} a^{n_W-(n_A-n_M)}` that it gives needs exactly `n_A - n_M` waved tree edges, which `BAGraph.exists_forest` (`BASizeClaim:727-933`, atom-first, roots by `choose`) provides. With roots `rep` given by `BACoverBy.rep`, the 1b needs a copy of `exists_forest` with `rootI := rep` (its proof uses only `Γ.mol (inr (rootI m)) = m.1`; helpers `BASizeClaim_*` private: `open private`), the rooted `sum_J` (`BAAtom_forest_roots :722` takes `root, par, edge, ρ` as parameters), then `BAAtom_solid_prod_conf` with `root := rep` and the tail of `baGtoAG_holds`. This is the 260 "new" lines of row A5 (467 central; the dispatcher's ≈480 in T2472's answer). `lwAuxNestedOwnOn_holds` applies at `BAShadowPG Q` unchanged (`PGraph (Fin 2)`, `LocReg345 p` from `baLocRegConcl_upto5` at `Q ∈ outs`; `ordN = auxOrd Q.g.shadow` by `BAGraph.auxOrd :75`).

**Switch conditions to `prover-max`.** (a) **holds as worded**: the rooted G3 needs more than `BAAtom_solid_prod_conf` + the band forest on `Γ.shadow` + the `baGtoAG_holds` tail, namely the rooted atom-first forest and rooted `sum_J` above (≈ 260 lines). It is a parameterization of merged proofs (`rep` in place of `choose`) with no new lemma content and no change of any binding `T2483_*` text; priced in row A5. The decision under the pre-signed rule is the hub's/dispatcher's. (b) does **not** hold: every `𝓜_x = 𝓜_y` output, `x ~ y` included, is covered by the weighted scale-mole tail at radius `Krad (log W)^{3/2}` (rows 4, 12). (c) does **not** hold: `lwAuxNestedOwnOn_holds` applies at `BAShadowPG Q`, and the far/near pins are the model-free `lwMomentExp_pinN_far/near`; no L3d1 content.

### Verdict per target
| target | verdict | reason |
|---|---|---|
| 1 (a)-(e) carrier `LWfgD` | PASS | band `LWfD` over `bandFM`; `baFMz` form as `LWfg_baFMz` |
| 2 `LWMomentExpG`, iff, `BALWMomentExp` | PASS | `PinFam` shape; rows 3, 10 |
| 3 `baLWMomentOfAnp_closed` | PASS | `baPathBinder_holds` (`BALocReg2B:338`) |
| 4 (a)-(d) weighted lemmas | PASS | `BAReal` at the instance; rows 4, 12 |
| 5 `BAGtoAGTRooted` | PASS | statement true; route as corrected above; switch (a) as worded |
| 6 regime (A) | PASS | `BALWMoment` for `LWPhiB`; rows 9, 10 |
| 7 weighted expansion | PASS | row 11 |
| 8 far/near pins | PASS | rows 1-4, 7, 8, 12; L40-C2 case (b) (row 3), no stop rule fires |
| 9 `BALWMomentExpOfAnp`, `baLWMomentExp_of_anp` | PASS | `BAAnpAuxG` only as antecedent |
| 10 instances | PASS | (ii) above; far set nonempty from `n = 57` |

### (a′) Preflight corrections — Tue Oct 13 02:30:06 UTC 2026
No verdict changes. (a)(ii) says targets 1 (a)-(e), 4 (a), 5 use the flow point `z_S(4,1/64)`; 1b uses `sz0`/`zSeq`/`flow_sz0` for 1, 2 (BA reading), 3 (data of T2470; the band transport of 2 uses the band data of `LWMomentExp` §12) and the merged T2472 flow
point `g0P, EP, t0P, m0P` (`L = 4`, `W = 2`, `Λ = 10`, `κ = Im m_S 4 10`; ticket 10 (v)) for 4 (a)-(d), 5; all hypotheses hold there (`flowP_real`, `g0P_le`, `flowP_data`).

## (b) Script output — Tue Oct 13 02:30:06 UTC 2026
**Delivered: L3d2b-1 = `RBM3D/Graph/BAMomentExpGen.lean`: targets 1-5, target 5 by the rooted atom-first forest route of (a); ten compiled instances.** Targets 6-10 (L3d2b-2) are not in this stage.
**Start decision (L3d1):** `git grep -E "(theorem|lemma) .*BAAnpAuxG"` finds 0 theorems on `650a122d` (branch base) and 0 on `main` `1e73b1b8`: L3d1 is not merged, target 9 stays as pinned (part B),
`T2483_MomentExpClosed` is not proved. In part A `BAAnpAuxG` occurs in code only as the hypothesis of the instance at line 982 (three docstring lines mention it).
**Line counts vs the stop line (2,000 per file, binding; split pre-signed since the central 2,122 > 1,950, this file = targets 1-5):**
```
$ TZ=UTC; for h in $(git log --reverse --format=%h 650a122d..t/T2483); do git log -1 $h ...; git show $h:RBM3D/Graph/BAMomentExpGen.lean | wc -l; done
05b10c6d Oct 13 01:39:52 UTC lines=362 T2483: BAMomentExpGen sections 1-4 (carrier LWfgD, pin LWMomentExpG,
4f7b2b8e Oct 13 01:46:35 UTC lines=884 T2483: BAMomentExpGen section 5 (rooted atom-first forest, rooted su
2ceb1e4c Oct 13 01:55:48 UTC lines=1131 T2483: BAMomentExpGen section 6-7 (compiled instances of targets 1-5
77f7be5b Oct 13 02:09:58 UTC lines=1147 T2483: BAMomentExpGen final (docstring, binder order of the pinned s
```
**L40-C2 / O4 / L4-C4 (b):** these belong to target 8 (part B); (a) rows 3, 5, 6, 12 are not used by part A, which has no threshold: `grep -nE "∀ᶠ|lwTail32|BAct_rate|atTop|Eventually"` hits only `Eventually.of_forall` in the
instance data (lines 917, 928, 929, 931); the tail `BAMomentExp_scalemole` takes `r, c, C` as parameters and covers every output with `b ∈ Γ.mol a`, every `x ~ y` among them (shape check below).

**Build, check file, full-library audit with this module imported** (scratch file `import RBM3D`, `import RBM3D.Graph.BAMomentExpGen`, `#assert_rbm_axioms`; `Test/Axioms.lean` unchanged):
```
$ lake build RBM3D.Graph.BAMomentExpGen | tail -1 ; ... | grep -c BAMomentExpGen.lean   # warnings of this file
Build completed successfully (4066 jobs). ; warnings of this file: 0
$ lake env lean docs/tickets/checks/T2483-check.lean ; echo exit=$?   ->  exit=0 (no error line)
$ lake env lean full_ax.lean | head -3 ; ... | grep -c error
axiom audit: 14278 theorems, 4503 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rat ; error lines: 0
$ sed 's/^.* depends on axioms: //' axioms.out | sort | uniq -c        # #print axioms of the 25 public declarations of the file
  25 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom " RBM3D/Graph/BAMomentExpGen.lean ; echo exit=$?   ->  exit=1 (no hit)
```
**Target statements, extracted by script** (`line`, signature on one line, cut at 165 characters):
```
$ python3 -I stmt_extract.py
  65 def LWfgD {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) : ℂ
  73 theorem LWfgD_bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) : LWfgD (bandFM s … [211 chars]
  91 theorem LWfgD_univ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : LWfgD C n t ω Finset.univ x y = LWfg C n t  … [170 chars]
  96 theorem LWfgD_union {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) {D₁ D₂ : Finset (Zd d (sz.L n))} (h : Disjoint D₁ D₂) (x y : Idx d (sz.L n)  … [250 chars]
 112 theorem LWfgD_baFMz {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) : (t : ℂ) * LWfgD  … [354 chars]
 145 theorem LWfg_split {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t ℓ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : LWfg C n t ω x y = LWfgD C n t ω (domFar  … [345 chars]
 157 def LWMomentExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM … [219 chars]
 176 theorem LWMomentExp_iff_bandPin (d : ℕ) : RBM.Gauss.Sizes.LWMomentExp d ↔ bandPin LWMomentExpG d
 183 abbrev BALWMomentExp : ℕ → Prop := baPin LWMomentExpG
 189 theorem baLWMomentOfAnp_closed : ∀ d : ℕ, BALWMomentOfAnp d := baLWMoment_of_anp baPathBinder_holds
 201 theorem BAMomentExp_valW_scale : ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), BAReal d L g0 κ E m → 0 ≤ t → t < 1 → ∀ (ω : Ω d L W) (P : BA … [349 chars]
 233 theorem BAMomentExp_valW_norm_le [Nonempty ι] (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData ι) {Ψ a K₁ Kd : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound  … [478 chars]
 257 theorem BAMomentExp_claimSize (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ K₀ K₁ Kd : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBound D.S ( … [435 chars]
 281 theorem BAMomentExp_pvalW_claim {K₀ K₁ Kd Ψ : ℝ} (Q : BAPGraph (Fin 2)) (hQ : Q.g.Normal) (D : BALData (Idx d L W)) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hS : LWKBo … [503 chars]
 304 theorem BAMomentExp_scalemole (hd : 3 ≤ d) (Γ : BAGraph E I) (hN : Γ.Normal) (D : BALData (Idx d L W)) {Ψ C c r : ℝ} (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hC : 0 ≤  … [944 chars]
 345 def BAMomentExp_wt (n : ℕ) (Dm : Finset (Zd d (sz.L n))) {p : ℕ} (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) : (o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W  … [172 chars]
 350 theorem BAMomentExp_wt_abs (n : ℕ) (Dm : Finset (Zd d (sz.L n))) {p : ℕ} (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) (ℓ : o.Q.E' ⊕ o.Q.I' → Idx d (sz.L … [213 chars]
 361 theorem BAMomentExpGen_rep {p : ℕ} (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) (hcov : BACoverBy (P := o.Q) (fun k : Fin p => o.π (Sum.inr (localReg_fx … [214 chars]
 861 def BAGtoAGTRooted (d : ℕ) : Prop
 887 theorem baGtoAGTRooted_holds (d : ℕ) : BAGtoAGTRooted d
```
**Statement diff against `T2483_*`.** Text: the normalized bodies (whitespace, `RBM.Gauss.`/`RBM.BA.` prefixes, name) of the three pinned statements are identical to the check file.
Lean: `T2483_eq3.lean` = check file Part 2 + `import RBM3D.Graph.BAMomentExpGen` + the lines below proves each pinned `T2483_*` (and the shapes of 1 (d), 4 (c), the nested form) from the new names.
```
$ python3 -I stmt_diff.py
LWMomentExpG: check 932 chars, file 932 chars, identical=True
GtoAGRooted: check 1446 chars, file 1446 chars, identical=True
ValWScale: check 316 chars, file 316 chars, identical=True
$ lake env lean T2483_eq3.lean ; echo exit=$?   ->  exit=0 ; grep "^theorem match_" T2483_eq3.lean | cut -c1-96
theorem match_1a : T2483_LWfgDBand := @LWfgD_bandFM
theorem match_1b : T2483_LWfgDUniv := @LWfgD_univ
theorem match_1c : T2483_LWfgDUnion := fun {d} {sz} C n t ω D₁ D₂ h x y => LWfgD_union C n t ω h
theorem match_2a : T2483_MomentExpBand := LWMomentExp_iff_bandPin
theorem match_2b : T2483_BALWMomentExp = BALWMomentExp := rfl
theorem match_2c : ∀ d, T2483_BALWMomentExp d ↔ BALWMomentExp d := fun d => Iff.rfl
theorem match_2d : T2483_LWMomentExpG = LWMomentExpG := rfl
theorem match_3 : T2483_MomentClosed := baLWMomentOfAnp_closed
theorem match_4a : T2483_ValWScale := BAMomentExp_valW_scale
theorem match_5 : ∀ d, T2483_GtoAGRooted d ↔ BAGtoAGTRooted d := fun d => Iff.rfl
theorem match_5b : ∀ d, T2483_GtoAGRooted d := baGtoAGTRooted_holds
theorem match_1d : (∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (Dm : Fin
theorem match_4c :
theorem match_nested :
```
**Compiled nonempty instances** (all in the file, `example`s; `ω` is any sample; hypotheses left: `STInitialGT2gL`, `LWLoopExpgL`/`LWLoop2gL`, `BAAnpAuxG 3`, the pin `BALWMomentExp 3`):
```
$ python3 -I inst_extract.py
ex 1 line  943 /-- **Instance (iv) of target 1** at `n = 0` of the data above, `x = 0`, `y = 1`, `t = 1/2`, for every sample `ω`: (b
ex 2 line  956 /-- **Instances (a) and (e) of target 1** at the same data: the band bridge at `Dm = {0}` and the exact three-way spl
ex 3 line  959 (continues the docstring above) example (ω : sz0.SeqΩ) : LWfg (baFMz sz0 zSeq) 0 (1 / 2) ω 0 1 =
ex 4 line  968 /-- **Instance (ii) of target 2**: the band instance of the generic pin at `d = 3` from the merged `lwMomentExp_holds
ex 5 line  974 /-- **Instance of the BA reading of target 2**: `BALWMomentExp 3` (a pin; its proof is part B) applied at the data ab
ex 6 line  982 /-- **Instance (iii) of target 3**: `baLWMomentOfAnp_closed` at `d = 3` (no path binder), `p = 2`, the data above: th
ex 7 line 1075 /-- **Instance of target 4 (a) and (d)** at the flow point: for a start term `o` and the weight `Π_k 1_{0}` (taking t
ex 8 line 1086 /-- **Instance of target 4 (b)** at the flow point: the weighted claim `size` for the packed start term `o.Q` at the 
ex 9 line 1100 /-- **Instance of target 4 (c)**: the weighted scale-mole tail at the graph `G0` of `Graph/BASymm1.lean` (externals `
ex10 line 1117 /-- **Instance (v) of target 5** (the BA rooted G3): a start term `o` of the partition of `fxyPowGraph 2`, the roots 
examples: 10
```
**Greps** (ticket acceptance):
```
$ clash.sh   # git grep -w of the 25 new public names over every local branch except t/T2483
refs scanned: 490 (main 1e73b1b8); refs with a hit: 0
$ grep -nE "sz\.lam|withLam|gK" RBM3D/Graph/BAMomentExpGen.lean | cut -c1-72      # (`Sizes`: 17 hits: the type `Sizes d`, `open`/namespace names, `Sizes.seqP`, `RBM.Gauss.Sizes.LWMomentExp`)
167:                  sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
170:                  sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
181:/-- **Target 2**: the block Anderson reading (law `seqP (sz.withLam 
908:local notation "μ0" => Sizes.seqP (sz0.withLam 0)
$ grep -c BAShapePath RBM3D/Graph/BAMomentExpGen.lean ; grep -n BAAnpAuxG ... | grep -E "^[0-9]+:(example|theorem|def)"
0   ;  982:example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz
$ git diff main...t/T2483 --stat | tail -2 ; grep -rln BAMomentExpGen RBM3D RBM3D.lean | grep -v "^RBM3D/Graph/BAMomentExpGen.lean" | wc -l
RBM3D/Graph/BAMomentExpGen.lean | 1147 +++++++++++++++++++++++++++++++++++++++ 1 file changed, 1147 insertions(+)  ; outside importers: 0
```
**UBA-C1 table** (R1 not used: the file has no `gK`, no `Sizes` read beyond the pin vocabulary):
| targets | `sz.lam` read | coupling `g₀` read | crossing |
|---|---|---|---|
| 2 | lines 167, 170 only: the regime `λ²/L² < 1 - t` and `sfT`, in the statement def `LWMomentExpG` (as `LWMomentExp`) | none | none |
| 1, 3, 4, 5 | none | `g0` with `BAReal d L g0 κ E m` and `0 < g0 ≤ Λ` (target 5) or none | none |
**Hypothesis table** (premise -> band discharge -> BA discharge): `LWAssmExpgL` (2) -> `LWAssmExp` by `Iff.rfl` -> pin hypothesis (`STInitialGT2gL`, `LWLoopExpgL` stay); path binder (3) -> none -> `baPathBinder_holds`
(T2469, discharged, not carried); `BAReal`, `0 ≤ t < 1` (4 a, 5) -> `ba_G_data` data -> `flowP_real`, `flowP_data` at the instance; kernel equalities `D.S = svarF 0`, `D.Sp = lwLift (BATheta ..)`, `D.M`, `D.gPsi` (5) -> `rfl`
at `BAExp14d_dataT`; roots `rep` (5) -> `BACoverBy.rep` (`BAMomentExpGen_rep`); weight `|Wt| ≤ 1` -> `BAMomentExp_wt_abs`; `Wt ≠ 0 -> [ℓ(rep c)] ∈ Dm` -> `BAMomentExpGen_rep`; `3 ≤ d` (2) -> `le_rfl`.
**Section map as written** (band `LWMomentExp` §, `AuxGraphRooted` § -> this file; the rest is part B or imported):
| band | here |
|---|---|
| `LWMomentExp` §1 `:28-107` (domains, `LWf_split`) | domains imported; `LWfg_split` (e) in §1 (lines 145-150); `LWMomentExpOn`, `LWMomExp*Pin`, `OfParts` -> B |
| §3 `:240-374` weighted | §4: `BAMomentExp_valW_scale` (`pvalW_smul`), `valW_norm_le`, `claimSize`, `pvalW_claim`, `scalemole`; `valW_smul`, `pvalW_evX` not twinned (no `ev`, no tags) |
| §4 `:375-460` weight, expansion | §4 (d): `BAMomentExp_wt`, `_abs`, `BAMomentExpGen_rep`; `expand` -> B; §2, §5-§12 `:108-239, 461-1509` -> B or imported (model-free §6-§8) |
| `AuxGraphRooted` §1 `:21-39` `auxValOn` | imported |
| §2 `:40-130` forest; §3 `:131-222` main sum | §5: `BAMomentExpGen_exists_forest` (copy of `BAGraph.exists_forest`, not of the band forest), `_sum_J`, `_main_sum` |
| §4 `:223-374` `LWGtoAGRooted` | §5: `_G3Rooted` (lines 707-853), `BAGtoAGTRooted` (861), `baGtoAGTRooted_holds` (887) |
| §5 `:375-491` nested form | no twin: `lwAuxNestedOwnOn_holds` at `BAShadowPG Q` (`match_nested` compiles); §6 instances -> §6, §7 here |
**Input table of targets 5 (and 4), `file:line` on the base `650a122d`:** `BAGraph.exists_forest` BASizeClaim:727 (copied), `BASizeClaim_forest_abs` :515, `BASizeClaim_atomAdj_comm/wAdj/adj_cases/atomAdj_cases/atom_eq/self_mem_atom`
(`open private`); `BAAtom_forest_roots` BAAtom:722, `BAAtom_alg_prod` :832, `BAAtom_term_conf` :573, `BAAtom_shadow_molOf_eq_iff` :100; `BAAtom_term_tail` BAAtom2:82, `BAAtom_tail_sum` :274;
`BAMomentGen_consts` BAMomentGen:364; `auxGraph_sum_blocks` AuxGraph:663, `auxGraph_card_aux` :873; `LGraph.forall_mol_isRight_iff` LWVocab:595; `BACoverBy.rep` BAProv:130, `BAProv_start` :520;
`baClaimSize`-route: `BASizeClaim_term_le` BASizeClaim2:120, `_sum_le` :317, `_size_alg` :446; `BAExp14d_term_scale` BAExp14d:93, `baSp_eq` BASizeClaim:180; `lwAuxNestedOwnOn_holds` AuxGraphRooted:457.
**Scratch files** (not in the repo; absolute path `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2483/`): `T2483_eq3.lean` (check file Part 2 + import + the `match_*` theorems), `stmt_diff.py`, `stmt_extract.py`, `inst_extract.py`, `axioms.lean`, `full_ax.lean`, `names_chk.lean`, `clash.sh`.

**Narrative.**
- *Target 5 is the one new argument.* The band forest `lwAuxRoot_exists_forest` on `Γ.shadow` is not used: the shadow waved edges include the `M`- and `Ψ`-dotted edges (`BAAtom:65`), so a tree may use a waved edge where an atom
  edge exists, and the count `n_A - n_M` of waved tree edges behind `K₁^{n_A-n_M} a^{n_W-(n_A-n_M)}` fails. `BAMomentExpGen_exists_forest` (lines 394-585) is a copy of `BAGraph.exists_forest` (`BASizeClaim:727-933`) with the given
  `rep : AuxIMol Γ.shadow → I` in place of `choose` (targets `T = ext ∪ range rep`, children `= (range rep)ᶜ`, the atom count redone for `RA = {atom (rep m)}`); `BASizeClaim_forest_abs` and the helpers are reached by `open private`.
  `BAMomentExpGen_sum_J` is `BAAtom_sum_J` on that forest, `_main_sum` adds the indicator `1[∀ c, [ℓ(rep c)] ∈ Dm]` and `auxValOn`, `_G3Rooted` is the proof of `BAExp14d_G3` with the weight (as `lwGtoAGRooted_holds`);
  `baGtoAGTRooted_holds` is 10 lines (887-896): the constants and kernel bounds are `BAMomentGen_consts`, so the kernel setup of `baGtoAGT_holds` is not copied. Target 5 occupies lines 376-896 (521 lines with docstrings).
- *Switch conditions.* (a) applied as worded in (a). (b), (c) did not fire: the `𝓜_x = 𝓜_y` tail is `BAMomentExp_scalemole` (any `b ∈ Γ.mol a`, so every `x ~ y`), `lwAuxNestedOwnOn_holds` applies at `BAShadowPG Q`
  unchanged (`match_nested` compiles), and no L3d1 content is read.
- *Scope.* The names proposed in the ticket are kept (`LWfgD`, `LWMomentExpG`, `BALWMomentExp`, `baLWMomentOfAnp_closed`, `BAMomentExp_valW_scale`, `BAMomentExp_scalemole`, `BAMomentExp_wt`, `BAGtoAGTRooted`, `baGtoAGTRooted_holds`);
  the 4 (b) results are `BAMomentExp_valW_norm_le`, `_claimSize` and `_pvalW_claim` (the packed claim for an output). No merged file is edited, no `private` is deleted, `RBM3D.lean` and `Test/Axioms.lean` are untouched (hub).
  Nothing is ported from `../RBM1D` or `../RBM2D` (twins of merged RBM3D files only; nothing there was read or run), so no RBM1D/RBM2D diff-stat applies.
- *Interface for part B.* Target 7: `LWfgD_baFMz`, `BAMomentExp_valW_scale`, `BAMomentExp_wt(_abs)`. Target 8: errors `BAMomentExp_pvalW_claim` with `BAMomentGen_consts`; `𝓜_x = 𝓜_y`: `BAMomentExp_scalemole`; `𝓜_x ≠ 𝓜_y`: `BAMomentExpGen_rep` (roots and
  `hWt0`), `baGtoAGTRooted_holds`, `lwAuxNestedOwnOn_holds p (BAShadowPG Q)` (its value `auxValOn (BAShadowPG Q).g` is `auxValOn Q.g.shadow` by `rfl`). Target 6 uses T2470's `BALWMoment`; target 9 uses `baLWMomentOfAnp_closed`.
  `BAMomentExp_wt sz n Dm o` is stated at the `Sizes` level; the data-level instances use `szP` (`CouplingWindowInst`: `L ≡ 4`, `W ≡ 2`) through `szP.L 0 = 4`, `szP.W 0 = 2`.
- *Instances.* Nondegenerate: `n = 0` of `sz0` (`L = 4`, `W = 32`, `N = 2097152`) for targets 1-3; the T2472 flow point (`L = 4`, `W = 2`, `g₀ ≤ 10`, `0 < t₀ < 1`), a start term of `fxyPowGraph 2` and `Dm = {0}` (1 of 64 blocks; the weight
  takes the values `1` and `0`) for 4 (a), (b), (d), 5; `G0` (externals joined by a waved edge, `ℓ0` at block distance 1 > 5 · 1/10) for 4 (c). Limit: the instance does not assert `0 < n_M` of the start term (`decide +kernel` on the packed term is stuck).

## (c) Verified Mathlib names (`env.contains`, `names_chk.lean`: 26 checked, 25 true; the false one is `LGraph.forall_mol_isRight_iff` without its namespace, `RBM.Graph.LGraph.forall_mol_isRight_iff` is true)
`Finset.card_sdiff_add_card_eq_card`, `Finset.card_image_of_injective`, `Finset.card_bij`, `Finset.card_univ`, `Finset.single_le_sum`, `Finset.prod_ne_zero_iff`, `Finset.prod_le_one₀`, `Finset.prod_nonneg`, `Finset.sum_ite_mem`, `Finset.univ_inter`,
`Finset.mul_sum`, `Finset.sum_add_distrib`, `Finset.sum_le_sum`, `Fintype.mem_piFinset`, `Fintype.ofFinite`, `List.getElem_mem`, `List.prod_nonneg`, `Equiv.apply_symm_apply`, `norm_sum_le`, `mul_le_of_le_one_left`, `Complex.norm_real`,
`Real.norm_eq_abs`, `ite_true`, `Sum.inr_injective`. Deprecated in this toolchain (build warnings seen, replaced): `if_true`, `if_false`, `if_pos`, `if_neg` (use `ite_true`, `ite_false`, `simp`). Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Open: part B (targets 6-10, instance (i) of target 9; `T2483_MomentExpClosed` once L3d1 merges) on `t/T2483b`; the `RBM3D.lean` import line is the hub's. No `T2483_*` content changed; no finding against the ticket.
- `T2483a` (`B:486-490`, `7_8:860`): the paper's "repeat the argument of GtoAG" has no weight and no choice of roots; `BAGtoAGTRooted` is the band's `LWGtoAGRooted` (T2364 delta) at BA: roots `rep` prescribed, `|Wt| ≤ 1` vanishing unless the root blocks
  are in `Dm`, `Γ^aux` of the shadow summed over `Dm` (`auxValOn`). Content unchanged.
- `T2483b` (`7_8:922-925`, the forest): the paper chooses a root in each molecule; Lean proves the atom-first forest for every choice (`BAMomentExpGen_exists_forest`), which the weight on the provenance vertices needs (T2289d).
