Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 19:16:09 UTC 2026
Notation: `x=1-u`, `g=ilambda`, `b_u=Bctl=W^{-d}B_{u,0}`, `B_{u,K}=(g²+x)^{-1}(K+1)^{2-d}+(L^d x)^{-1}`, `T_u(r)=B_{u,r}e^{-√(r/ℓ_u)}` (merged `Defs/Params.lean:32-37`, `Defs/Tail.lean:44-52`). `1_2`, `3_5` = `paper/tex/1_2_Intro_model_result.tex`, `3_5_Loop_Hierarchy.tex`. `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2066` (python only; `$S/probe.txt` = `git show 0362cbc:RBM3D/Probe/T2039Pins.lean`). "derived" = my algebra from the cited lines.
### (i) Exponent table
| item | value | constraint (source) | slack |
|---|---|---|---|
| d, L, κ, ε, 𝔡, 𝔠 | 3, ≥3, 1/10, 1/10, 1/10, 1/6 | `W≥N^𝔠`, L≥3 force 𝔠<1/d and `L^d ≤ W^{1/𝔠-d}` (derived); `(eq:WO)` `W^{-d/2+𝔡}≤g≤𝔡⁻¹` (1_2:359-363) | `L=W` admissible with equality (`N^{1/6}=W`, last line of S1) |
| ε₀ of `(initialGT2)` | 1/10 | `0<ε₀<d/2`: `STPsiClass` clause 3 `W^{-d/2}≤c⁻¹Ψ(0)` contradicts clause 1 `Ψ≤W^{-ε₀}` eventually if `ε₀>d/2` | 1.4 |
| 1/4, 1/5, 1/6 | `(Gtmwc)` 1_2:1327; `(Eq:Gdecay_w)` 1_2:1349; scale step and stopping 3_5:533, 571 | `1/6<1/5<1/4`; `J^{3/2}≤Δ^{(1/6)(3/2)}=Δ^{1/4}` closes with equality (T2039-prove.md (a), 3_5:542) | 1/30, 1/20, 0 |
| `C_d`, `𝔠_d` | `C_d=3C+1`, `𝔠_d=min(1/100,1/(60C_d),𝔠₀)`, `C_d𝔠_d≤1/60` (T2039-prove.md (b) narr. 3) | 3_5:507-509: `b^{1/4}r^{C₀+5/4}≪1`, `r=(1-s)/(1-t)≤b^{-𝔠_d}`, i.e. `𝔠_d(C₀+5/4)<1/4` with `C₀:=C_d` (derived) | `≤1/60+1/48=0.0375`, slack 0.2125 (`C_d≥1`) |
| `c'`, `M(D)` | `c'=min(2𝔡,dε)=0.2`; `M>6((D+d)/c'-1)`: D=10 → 384 | `b_u≤W^{-2𝔡}+4N^{-ε}≤5W^{-c'}` on `[0,lemT]` (T2039-portmap P.4 row `STBdata`; `N≥W^d`); then `b^{1+M/6}≤W^{-D-d}` (3_5:355, 571-578) | szC n=0: `3.71e-2≤3.79` |
| `δ₀` of `STNewKLK` | `√(4κ-κ²)/2=0.312` | `δ₀≤Im m(E)` (`|E|≤2-κ`) gives `Σ_c|𝓛^{(2)}(a,c)|≤(Im m+δ₀)/(W^dη_u)≤2/(W^d(1-u))` (3_5:640-646; Cauchy–Schwarz+Ward, any Hermitian H, derived) | H=0, u=1/16: `|G-M|=0.066`, slack 0.246 |
| `C` (`STNewKLK`), `C` (`STK2decay`) | functions of `(d, Λ=𝔡⁻¹)` only (δ₀ also of κ) | `∃C δ₀` / `∃C` stand before `∀ sz n` (probe 587, 778-779; script S4); `Prop5Decay d Λ` (constants `(d,Λ)`, all `L≥3, 0<g≤Λ, t∈[0,1)`, `Pins.lean:35-45`) is **proved**: `prop5Decay_holds`, `Prop5Hold.lean:784` | scan S2: `max|Θ|/T=120.8` at g=10 (at `u=0,a=0` it is `1/B_{0,0}≤1+g²`) |
| `3^d` of `STContractPt` | 27 | proof 3_5:754-795: `𝓛⁶≤(𝓛⁴_{alt})^{1/2}𝓛⁴'`, each `c` has ≤3^d neighbours `c'`, Ward `Σ_c𝓛⁴'≤max|𝓛³|/(W^dη)` | **0: sharp**, ratio→1.000000 (script S3) |
Pins (class: DECISIONS §28, T2039-portmap P.7; proving ticket: P.5/P.7; lines: probe docstrings, checked against the TeX labels):
| pin | paper line | class | proved by |
|---|---|---|---|
| `STStep2` (+`Local/Avg/Decay`) | 1_2:1340-1357 (1342, 1344, 1349) | owed | ST2-04 (`ST_step2_of_pins`) |
| `STNewKLK` | 3_5:371-378, proof 610-654 | owed | ST2-07 (+ST2-06b: `(TTT2)` in `|·|_∞`, 3_5:333) |
| `STContractPt` | 3_5:751-797 (`ygdhmsgq0`) | owed | ST2-08 |
| `STLWB`, `STLWT` | 3_5:385-404, 406-415 | owed | LW gate (T2040); bridges ST2-03 (§29 O3) |
| `STEMn2Poly`, `STEMn2Exp` | 3_5:427-432 (800-825), 437-440 (829-888) | owed | ST2-09; ST2-10, 11 |
| `STGridRepN` (`STGridMart`: m=2) | 3_5:134-148, 218-240 | owed | ST2-12, 13 (+27, 34, 35) |
| `STK2decay` | 3_5:457, 518 | owed (no borrowed input, finding F1) | ST2-06 |
| `STNetLift2` | 1_2:1400 | owed | ST2-18, 19 |
| `STScaleExists` | 3_5:521-527, 571-577 | owed | ST2-05 |
| `STOptL2` | 3_5:470 (466-512) | owed | ST2-14, 15 |
| `STLocalAvgOfL2` | 3_5:455-465 | owed | ST2-16, 17 |
| `STInitialGT2`, `STLWassm`, `STLWassmExp` | 3_5:28-30, 387, 408 | owed | Step 1 / ST-6 chain (no ST2 ticket) |
| `STPsiClass` | 3_5:385-393 (`eq:Psi` 391) | structural | — |
| `STScaleOk/Adm`, `STL2decayPT` | 3_5:521-527, 571-577, 460 | not registered (internal) | — |
### (ii) One concrete nondegenerate instance, and the four boundary checks of DECISIONS §29
Instance `szC` (new; merged `Sizes` constructions have `lam` = `(2(n+1))^{-6}` (`sz0`), 1 (`szB`), 1/2 (`LWStein.lean:1684`), 0 (`ScaleFacts.lean:616`): none has `g>L`): `d=3`, `L_n=3`, `W_n=n+4`, `ilambda=4>L`, `𝔡=κ=ε=1/10`, `𝔠=1/6`, `z=1/2+i/64` (as `zB`), `E=lemE z`, `(s,t)=(0,1/16)`, `ε₀=1/10`, `Ψ_n(r)=(W^{-d}B_{t,r∧L})^{1/2}`.
```
$ python3 $S/inst2.py
flow: m(z)=-0.2480+0.9605i lemT=0.983992 lemE=0.500 |E|<=2-kappa: True;  0=s<t=0.0625<=lemT<1: True
Admissible(c=1/6,fd=1/10) + locDomain(kappa=eps=1/10) at n=0,7,14,..<1e5: True; ilambda=4>L=3: 1-g^2/L^2=-0.778<0; ell_u={3} for u in [0,1/16]
Bctl_n(t=1/16): n=0 1.54e-03, n=10 3.59e-05, n=100 8.76e-08 (<=0.11 W^-3);  con_st_ind (1-t)/(1-s)=15/16 vs Bctl^c_d, c_d=1/100: n=0 0.937<=0.9375 ;  c_d=1e-3 needs W>=1.02e+09
delta_0 := Im m(E)-lower bound sqrt(4k-k^2)/2 = 0.312 <= Im m(E)=0.968; H=0 (Hermitian): max|G_u-M| = |-1/z_u - m(E)| = 0.000 (u=0), 0.066 (u=1/16) <= delta_0: True
size data: sup_u Bctl(u)=3.71e-02 at W=4 (u=lemT) <= 5W^-c'=3.789, c'=min(2fd,d eps)=0.20 ; M(D=10)>384
$ python3 $S/inst.py | grep "extreme L=W=4"      # S1
extreme L=W=4: N^(1/6)=4.000<=W: True ; L^d=64 <= W^((1-d c)/c)=W^3.0=64: True
```
External hypothesis `STConStInd` (`(con_st_ind)`, 1_2:1296; the pin picks `𝔠_d≤1/100` itself): limit: `b_n≤0.11W_n^{-3}→0`, so `b_n^{𝔠_d}→0<15/16` for every fixed `𝔠_d>0`; `n₀` is explicit (`W≥1.02e9` at `𝔠_d=1e-3`, n=0 already at 1/100); a window `(s,t)` with `t` near `lemT` makes `n₀` astronomical for any `𝔠_d≤1/100`, so the instance keeps `t=1/16`. Stochastic premises (`STLK, STDecay, STStep1*, STInitialGT2, STLWassm*`, PT premises) stay hypotheses.
| pin | (1) time `0≤s`, `t<1` | (2) `1-g²/L²`, `g>L` | (3) `L`–`W` relation | (4) `∀n` vs `∀ᶠn` |
|---|---|---|---|---|
| `STStep2` | `0≤s<t≤lemT<1` in hyp. (`lemT_lt_one`, `Semicircle.lean:209`) | window ⊂[0,lemT]; `ℓ_u≡L` for `g>L` (szC) | `STFlow.Admissible` (`L^d≤W^{1/𝔠-d}`) | premises ∀n; `STConStInd` ∀ᶠ; all `Prec` are ≺ |
| `STNewKLK` | `0≤u<1` in hyp. | every `u∈[0,1)`; `(TTT2)` at `u=t` has no regime condition (`EKPropT`, `Evolution/Pins.lean:142`); `R=0.81` at `g=10>L=4` (S2) | not used: `∀L W`, `C=C(d)`, Ward `2/(W^d(1-u))`; `T̃≥W^{-D}` reduction 3_5:612-616 | per-n deterministic; `ℓ∈(0,1)`: linear term suffices (`T(ℓ)≥2^{2-d}e^{-1}T(0)`, derived) |
| `STContractPt` | none | none | `∀L≥3, W`; constant exact (3^d neighbours need `L≥3`) | single `(L,W,H,z)` |
| `STLWB/STLWT/STEMn2Poly/STEMn2Exp` | `0≤t≤lemT` in hyp. | no `ℓ_t` in text except range `ℓ≤(log W)^{10}ℓ_t` (`=L` if `g>L`; `STprof` sees only `r∧ℓ`, `r≤L/2`) | `Admissible` | `STPsiClass` ∀n is premise-side: consumer redefines finitely many n; ε₀<d/2 needed; LW-range ∀ᶠ |
| `STGridRepN` | `0≤s≤t≤lemT`; `s=t` ok (Δ=0, Rem=Mart=0) | same window | `η_u≥Im z≥N^{-1+ε}`, `W^d≤N`: losses `N^{C₀}`, `C₀=C₀(d,m)` | identity ∀n only with `∃Rem Mart` (free at small n); bounds ∀ᶠ |
| `STK2decay` | `0≤u<1` in hyp. | every `u`; `g=10>L`: ratio 21.3 (L=3), 39.2 (L=4); scan max 120.8 (S2) | none: `C=C(d,𝔡⁻¹)`, `ℓ¹≥ℓ^∞` right direction (`B_{u,K}` decreasing), `e^{-cx}≤e^{1/(4c)}e^{-√x}` | pointwise, ∀n |
| `STNetLift2` | `0≤s≤t≤lemT` | same | `Admissible`; `N^{-C}` net polynomial | PT premises → `Prec`; every real `C_d` |
| `STScaleExists` | `u∈[s_n,t_n]⊂[0,lemT]` | `g>L`: `K_m` is cut at `L` by m=2, 0 violations (S5) | `K_m≤ℓ_u(m/6)²(d ln W+ln101)²` (derived: `b≥W^{-d}/101`) needs only `W→∞` | `K_0=0` ∀n, clauses ∀ᶠ; n=0 data `W=L=3,g=.01,x=.01`: `b=3.80>1` makes ∀n impossible |
| `STOptL2` | `0≤s≤t≤lemT`; `STConStInd` forces `s<t` | same | `𝔠₀` independent of 𝔠; `b≤5W^{-c'}` gives `c₀≳1` (3_5:469) | `STConStInd` ∀ᶠ; conclusion `PrecPT` |
| `STLocalAvgOfL2` | same | same | `B_{u,r-2}≤3^{d-2}B_{u,r}` (`r≥2`); `B_{u,0}≥1/(1+𝔡^{-2})` so `Ψ=(C·W^{-d}B_{u,0})^{1/2}≥W^{-d/2}` | `Prec/PrecPT` |
| `STInitialGT2`, `STLWassm`, `STLWassmExp` | predicates; consumers carry `0≤t≤lemT` | n/a | n/a | `Prec`, asymptotic |
```
$ python3 $S/pinmatrix2.py | awk 'NR>1{n++; if($2=="yes")a++; if($3=="yes")b++; if($0~/absent/)c++} END{print n" windowed pins: 0<=s|t|u in hypotheses: "a"; t<=lemT or u<1: "b"; case-(ii) bound (lam n ^ 2 / L^2) in pin text: "n-c}'
12 windowed pins: 0<=s|t|u in hypotheses: 12; t<=lemT or u<1: 12; case-(ii) bound (lam n ^ 2 / L^2) in pin text: 0
$ python3 $S/bd_ttt2_theta.py | grep -E '^rows|^TTT2|^Theta_uM|^L=3 g=10|^L=4 g=10'      # S2: d=3, L∈{3..32}, g∈{.05,.5,2,L,2.5L,10}≤10, x from 1 to 1e-9; R=(1-u)max_a(T_u*T_u)/T_u, u=t
rows 375
TTT2 (u=t): max_a (1-u)(T_u*T_u)(a)/T_u(|a|_inf)  max over scan = 425.884 at (L,g,x)=(32, 0.05, 1.0)
Theta_uM decay: max_a |Theta_{uM}(0,a)|/T_u(|a|_inf), M in {1,e^{i pi/3},e^{2i pi/3},-1,i}: max = 120.840 at (L,g,x)=(32, 10.0, 0.0244140625)
L=3 g=10 (g>L: True): max R_TTT2=0.683  max Theta ratio=21.305
L=4 g=10 (g>L: True): max R_TTT2=0.812  max Theta ratio=39.176
$ python3 $S/sat.py | tail -n 3      # R at g=.05, x=1; R(L=3,4,8,16,32)=7,15,55,170,426: grows with L and saturates slowly, not proved uniform (that is ST2-06b)
 L= 64  R=849.5
 L= 96  R=1130.8
 L=128  R=1307.7
$ python3 $S/contract.py | sed -n '1,2p'; python3 $S/contract2.py | sed -n '1p;6p'      # S3: arbitrary Hermitian H (0, GUE, 10·GUE, diag, rank-one), W∈{1,2}, L=3, η down to 1e-3 (contract.py) / 1e-6 (contract2.py)
STContractPt stress test: max over (sigma,a,b, level sets of A) of LHS/RHS  (pin says <= 1); rows=120
overall max ratio = 0.9999 at (1, 'rank-one', 3.0, 0.001)
H = 3*uniform rank-one projector; z = E + i eta; ratio = LHS/RHS maximised over sigma,a,b,level sets (pin: <= 1)
 eigenvalue 3  eta=1e-06  E=eigenvalue : ratio=1.000000   E=eigenvalue+0.3: ratio=0.000001
$ python3 $S/scale.py | sed -n '1p;4p;5p' | sed 's/window.*violations/violations/'      # S5: STScaleAdm clauses (1)-(5), K_{m+1} by bisection, cut at L; 120 u-points, windows [0,lemT] and [0,1/16]
szC (g>L), full violations of clauses (1)(2)(3)(4) = [0, 0, 0, 0]; (5) first m with T<=W^-D or K>=L (D=5) = 2 (<= 236)
szC (g>L), violations of clauses (1)(2)(3)(4) = [0, 0, 0, 0]; (5) first m with T<=W^-D or K>=L (D=5) = 2 (<= 236)
sz0 n=0 (g<<1), violations of clauses (1)(2)(3)(4) = [0, 0, 0, 0]; (5) first m with T<=W^-D or K>=L (D=5) = 3 (<= 236)
$ grep -n '∃ C δ₀ : ℝ\|∃ C : ℝ, 0 < C ∧$\|∀ (sz : Sizes d) (n' $S/probe.txt | sed -n '1,4p'      # S4: constants before `∀ sz` (STNewKLK 587, STK2decay 778-779; 573 is STNewKLKAt, which takes C δ₀ as parameters)
573:  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
587:  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAt d κ 𝔡 C δ₀
778:  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
779:    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
```
Ward/Cauchy–Schwarz and `3^d` steps are derived from 3_5:640-646, 754-795; the numerics are evidence, not proofs (no explicit `≺` constants).
**Copy and binding checks the ticket asks for (scripts `closure.py`, `bind_all.py`, `clash.py`, `concl.py`, `summ.py` in `$S`).**
```
$ python3 $S/summ.py ; python3 $S/bind_all.py | tail -n 1 ; python3 $S/clash.py | sed -n '1,2p' ; python3 $S/concl.py | head -n 3 | cut -c1-104
copy set: 56 decls in probe 248-818,4106-4149,5119-5156 (45 defs + 11 theorems of sections 1-2: measurability, STLM_seqHflow, STGMM_seqHflow, STstopIdx_isStoppingTime)
defs of sections 3-12 the pins mention (to copy): STScaleOk:2277 STScaleAdm:2288 STL2decayPT:4133 STeeLoop:4965 STLIM:4997 STLKIM:5002 STksimLKM:5007 STelklkM:5021 STavgErrM:5029 STegtM:5034 STeeM:5041 STgAN:5079 STgDriftN:5086 STeeUM:5099
total 28, identical 28, not identical []
closure names (70) that already exist as declarations of the same name in non-Probe RBM3D files: 1
  STeeLoop     probe:4965  merged: [('RBM3D/Induction/Step34Pins.lean', 152)]
STStep2Local (probe 457)  vs STLocalEntryU (probe 4760 = merged Step34Pins:199): bodies equal: True
STStep2Decay (probe 472)  vs STGdecayW   (probe 4770 = merged Step34Pins:208): bodies equal: True
STStep2Avg   (probe 464)  vs STAvgU      (probe 4752 = merged Step34Pins:192): bodies equal: False (diff
```
§0/§12.1: the 12 definitions the copied text uses (`STKloop STWB STblk STGM STmaxLoop2 STLK STDecay STConStInd STFlow STStep1Loop STStep1Weak STflowE`) bind to `Induction/Defs.lean:64-286`, identical; all 28 §0+§12.1 copies are identical to `Defs.lean`/`Step34Pins.lean`. `STStep2Avg` ≠ `STAvgU` (single charge vs `Fin 1` pair; T2039g, equal by `L^{(1)}_-=conj L^{(1)}_+`). The text diff against the probe is a stage-1b output (no Lean written here); expected renamings: only `open … RBM.Probe.T2039` lines, and the `STStep2` conclusion `STStep2Concl sz (STflowE z) s t Cd`.
**Findings.** F1: `Prop5Decay` is proved (`prop5Decay_holds`, `Axioms.lean:76` says it left `borrowedProps`); DECISIONS §28 and T2039 (d).7 "borrowed in ST2-06/07" are stale: no borrowed premise, no registry line. F2: `STeeLoop` (probe 4965, used by `STeeM`) is a copy of merged `Step34Pins.lean:152` (identical): bind, do not copy (the ticket's range `STLIM..STeeM` starts at 4997, but `STeeM` needs it); `STL2decayPT` (probe 4133, §12) is mentioned by `STLocalAvgOfL2` and must be copied though the ticket lists §3–§11 only. F3: `STContractPt`'s `3^d` is attained (S3), so the pin is exactly the paper's inequality; no weaker constant is true.
### Verdict per target
1 (copy §1, §2, §12 pins + §12.2 vocabulary + defs): PASS (with F2). 2 (bind §0/§12.1): PASS (28/28 identical). 3 (`STStep2` with `STStep2Concl`; `Local`, `Decay` bodies equal `STLocalEntryU`, `STGdecayW`): PASS. 4 (registry: 16 owed, `STPsiClass` structural; `Prop5Decay` not borrowed, F1): PASS. 5 (instances at the §1/§2 definitions): PASS (szC data above).
Boundary checks (DECISIONS §29) for the 16 owed pins: no pin false at a boundary; no stop. `STScaleExists`, `STNewKLK`, `STGridRepN`, `STOptL2`, `STK2decay` rest on derived arguments above, not on Lean-checked instances (Lean-checked instances are stage 1b).

## (b) Script output — Sat Oct  3 19:24:15 UTC 2026
```
$ git log --oneline -1 t/T2066; git diff --stat main...t/T2066
0685e06 T2066: ST2-01 Step 2 vocabulary and pins (Induction/Step2Defs) with registry lines
 RBM3D/Induction/Step2Defs.lean | 1213 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   19 +-
 2 files changed, 1231 insertions(+), 1 deletion(-)
$ lake build RBM3D.Induction.Step2Defs 2>&1 | tail -2   # in the worktree
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3716 jobs).
$ lake build 2>&1 | tail -1
Build completed successfully (3782 jobs).
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Induction.Step2Defs; #assert_rbm_axioms  (§20 pre-check, not committed)
exit 0
1:axiom audit: 2184 theorems, 942 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
71:premises found by scanning: 60 (borrowed 2, owed 46, structural 12).
72:registry: 5 borrowed + 59 owed + 27 structural; 31 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
55:  RBM.Gauss.Sizes.STNewKLK: 1 [no certificate]
56:  RBM.Gauss.Sizes.STContractPt: 1 [no certificate]
57:  RBM.Gauss.Sizes.STEMn2Poly: 1 [no certificate]
58:  RBM.Gauss.Sizes.STEMn2Exp: 1 [no certificate]
59:  RBM.Gauss.Sizes.STGridRepN: 1 [no certificate]
60:  RBM.Gauss.Sizes.STK2decay: 1 [no certificate]
62:  RBM.Gauss.Sizes.STScaleExists: 1 [no certificate]
63:  RBM.Gauss.Sizes.STOptL2: 1 [no certificate]
65:  RBM.Gauss.Sizes.STStep2: 2 [no certificate]
66:  RBM.Gauss.Sizes.STLWB: 1 [no certificate]
67:  RBM.Gauss.Sizes.STLWT: 1 [no certificate]
68:  RBM.Gauss.Sizes.STInitialGT2: 4 [no certificate]
69:  RBM.Gauss.Sizes.STLWassm: 2 [no certificate]
70:  RBM.Gauss.Sizes.STLWassmExp: 2 [no certificate]
$ git diff --numstat main...t/T2066 -- RBM3D/Test/Axioms.lean; git diff main...t/T2066 -- RBM3D/Test/Axioms.lean | grep -c "^+   .RBM"
19	1	RBM3D/Test/Axioms.lean
18   # added list lines: 16 owed + STPsiClass (structural) + the re-commaed STB45Pin line
$ grep -c "sorry\|admit\|native_decide\|^axiom" Step2Defs.lean
0
$ lake env lean axioms.lean   (#print axioms of all 88 def/theorem declarations of the file)
prints: 88; depends exactly on [propext, Classical.choice, Quot.sound]: 88; other lines: 0
'RBM.Gauss.Sizes.STstopIdx_isStoppingTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2DefsInst.inst_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2DefsInst.inst_newKLK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step2DefsInst.inst_stop' depends on axioms: [propext, Classical.choice, Quot.sound]
$ bash clash2.sh   # git grep on main: same-stem def/theorem declarations of the 88 names, outside Step2Defs
checked 88 names, 0 with same-stem declarations on main
$ python3 bind_all.py | tail -1   # (preflight script) §0 + §12.1 copies vs merged Defs/Step34Pins
total 28, identical 28, not identical []
$ diff -B <probe ranges 248-818,2274-2296,4101-4149,4995-5045,5077-5156 of 0362cbc> <Step2Defs.lean lines 39-861> | scaffolding removed
< open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
< open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
< open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
< open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
< open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
< strong form of `(b)` are not used by Step 2. -/
> strong form of `(b)` are not used by Step 2.  The conclusion is the merged bundle `STStep2Concl`
> (`Induction/Step34Pins.lean:221`: `STLocalEntryU ∧ STAvgU ∧ STGdecayW`); `STStep2Local ∧ STStep2Avg ∧
> STStep2Decay` below are the three parts in the single-charge form of the probe, which ST2-04 proves
> and turns into `STStep2Concl` (`STStep2Avg` ≠ `STAvgU` as a statement: paper-delta T2039g). -/
<             STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
<               STStep2Decay sz Cd (STflowE z) s t
>             STStep2Concl sz (STflowE z) s t Cd
> /-! ## 3. Definitions the pins mention: the scale family, the per-time `(eq:L2_decay)`, the list-loop matrix functionals -/
$ the merged STStep2 (sed -n 599,608p Step2Defs.lean)
def STStep2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
            STStep2Concl sz (STflowE z) s t Cd

$ grep -n "^def ST\(NewKLK\|ContractPt\|LWB\|LWT\|EMn2Poly\|EMn2Exp\|GridRepN\|K2decay\|NetLift2\|ScaleExists\|OptL2\|LocalAvgOfL2\|InitialGT2\|LWassm\|LWassmExp\|PsiClass\|ScaleAdm\|GridMart\) " Step2Defs.lean
323:def STInitialGT2 (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
333:def STPsiClass (ε₀ : ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
342:def STLWassm (E t : ℕ → ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
349:def STLWassmExp (E t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
377:def STNewKLK (d : ℕ) : Prop :=
391:def STContractPt (d : ℕ) : Prop :=
406:def STLWB (d : ℕ) : Prop :=
421:def STLWT (d : ℕ) : Prop :=
441:def STEMn2Poly (d : ℕ) : Prop :=
456:def STEMn2Exp (d : ℕ) : Prop :=
537:def STGridMart (d : ℕ) : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAt d C₀
568:def STK2decay (d : ℕ) : Prop :=
581:def STNetLift2 (d : ℕ) : Prop :=
635:def STScaleAdm (s t : ℕ → ℝ) (Kseq : ℕ → ℕ → ℝ → ℝ) : Prop :=
656:def STScaleExists (d : ℕ) : Prop :=
667:def STOptL2 (d : ℕ) : Prop :=
694:def STLocalAvgOfL2 (d : ℕ) : Prop :=
854:def STGridRepN (d : ℕ) : Prop := ∀ m : ℕ, 2 ≤ m → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAt d m C₀
$ grep -n "^theorem inst_\|^example" Step2Defs.lean
880:theorem inst_step2 (h : STStep2 3) :
893:theorem inst_step2_lowg (h : STStep2 3) :
931:theorem inst_newKLK (h : STNewKLK 3) :
959:theorem inst_contractPt (h : STContractPt 3) :
1009:theorem inst_LWB (h : STLWB 3)
1021:theorem inst_EMn2Poly (h : STEMn2Poly 3)
1044:theorem inst_LWT (h : STLWT 3)
1056:theorem inst_EMn2Exp (h : STEMn2Exp 3)
1072:example (h : STGridMart 3) :
1096:theorem inst_stop :
1102:theorem inst_K2decay (h : STK2decay 3) :
1116:example (h : STNetLift2 3) (Cd : ℝ)
1127:theorem inst_scaleExists (h : STScaleExists 3) : ∃ Kseq : ℕ → ℕ →
1134:theorem inst_optL2 (h : STOptL2 3) :
1149:example (h : STLocalAvgOfL2 3) :
1161:theorem inst_gridRepN (h : STGridRepN 3) :
1184:example (ω : sz0.SeqΩ) :
1189:example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
1193:example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (
1197:example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (
1201:example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (
1205:example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (
1209:example (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : Measurable fun H : Ma
```

Narrative (stage 1b; every number above is script output).
- Source: `git --no-optional-locks show 0362cbc:RBM3D/Probe/T2039Pins.lean` (checked byte-identical to the scratch copy by `cmp`). Not a port from RBM1D/RBM2D: this stage read no RBM1D/RBM2D file, so no RBM1D/RBM2D diff-stat applies.
- `Step2Defs.lean` imports `RBM3D.Induction.{Defs,Step34Pins}`, `Kernel.Evolution`, `Path.{Walk,Stop}` (the modules that define `pathH`, `firstHit`, `uKer`, `ThetaN`, ...). It does not import `RBM3D`. The file was assembled by script from the five probe ranges of the diff header, then built; the diff against the probe shows only the listed `open` renamings, the docstring/body of `STStep2`, and the section heading of section 3.
- Copied: probe §1 and §2 (248-818, including its 11 theorems: `STLM_seqHflow`, `STGMM_seqHflow`, eight `ST*M_measurable`, `STstopIdx_isStoppingTime`), `STScaleOk`/`STScaleAdm` (2274-2296), `STScaleExists`, `STOptL2`, `STL2decayPT`, `STLocalAvgOfL2` (4101-4149), `STLIM..STeeM` (4995-5045), `STgAN..STGridRepN` (5077-5156). Not copied: probe §0, the §12.1 copies of `STStep2Concl` and parts, `STeeLoop` (merged `Step34Pins.lean:152`), every theorem of §3-§12.
- `STStep2` as merged: the `def` printed above; the hypotheses are the probe's, the conclusion is the merged bundle `STStep2Concl` (`Step34Pins.lean:221`). `STStep2Local`, `STStep2Avg`, `STStep2Decay` stay as definitions (ST2-04 proves them and turns them into `STStep2Concl`).
- Registry: 16 owed lines and `STPsiClass` (structural) in `RBM3D/Test/Axioms.lean`; the §20 pre-check exits 0. The pre-check first failed on six names (`STStep2{Local,Avg,Decay}PT`, `STL2decayPT`, `STStep1Weak`, `STGridMart`), because instance theorems took them as hypotheses; the instances that need them (`STGridMart`, `STNetLift2`, `STLocalAvgOfL2`) are `example`s, not theorems, so the registry holds exactly the ticket's list. Consequence in the pre-check output: `STNetLift2`, `STLocalAvgOfL2`, `STPsiClass` "carry nothing yet" (information, not an error); the other registered pins of this ticket show 1-4 carrying theorems.
- Instances (item 5), compiled here: `inst_step2` (the new `STStep2`, conclusion `STStep2Concl`, at `sz0`), `inst_step2_lowg` (at `sz1`, `ilambda = W^{-d/2+𝔡}`), `inst_newKLK`, `inst_contractPt`, `inst_LWB`, `inst_EMn2Poly`, `inst_LWT`, `inst_EMn2Exp`, `inst_stop` (= `STstopIdx_isStoppingTime`), `inst_K2decay`, `inst_scaleExists`, `inst_optL2`, `inst_gridRepN`, `Ψ0_class` (= `STPsiClass` at `sz0`, `ε₀ = 1/20`), and the examples for `STGridMart`, `STNetLift2`, `STLocalAvgOfL2`, `STLM_seqHflow`, `STGMM_seqHflow` and the five `*_measurable`. The hypotheses left open are the pin itself or stochastic premises of the pin (`STLK`, `STDecay`, `STStep1*`, `STInitialGT2`, `STLWassm*`, per-time statements); `STFlow`, the time ranges (`0 ≤ s`, `s < t ≤ lemT`), `STConStInd`, `STPsiClass`, the Hermitian `H = 0`, `‖G - M‖_max = 0 ≤ δ₀` are discharged. Not moved here (they use theorems of §3-§12): `inst_Bdata`, `inst_skeleton`, `inst_skeleton_concl`, `inst_skeletonN`, `inst_step2_concl`, `ST_scaleAdm_congr`, `inst_scaleAdm_szX` go with ST2-02 to ST2-04.
- Preflight (a) boundary checks (DECISIONS §29) are the preflight's numerical and paper arguments; this stage added no Lean instance at `ilambda > L` (the compiled `inst_step2_lowg` is the other extreme of `(eq:WO)`).

## (c) Verified Mathlib names (compiled in the instance code; no new ones beyond the probe's)
`Nat.ceil_pos`, `Nat.le_ceil`, `Real.rpow_pos_of_pos`, `Finset.range`, `Matrix.isHermitian_zero` (all resolve in the build above). Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
1. Docstrings of `STNewKLK`, `STK2decay` still say `Prop5Decay (borrowed)`: stale (preflight F1, `prop5Decay_holds` is proved); kept verbatim, the header of the file says so. DECISIONS §28 (registry line 232: `Prop5Decay` borrowed) is stale for the same reason: no borrowed premise, no registry line.
2. Paper-delta candidates: T2039a-j (DECISIONS §28) apply to the pins of this file, numbered at this merge. New: T2066a, the library `STStep2` concludes the merged bundle `STStep2Concl` (`STLocalEntryU ∧ STAvgU ∧ STGdecayW`), not `STStep2Local ∧ STStep2Avg ∧ STStep2Decay` (equivalent up to T2039g; ST2-04 proves the bundle).
3. Hub: add `import RBM3D.Induction.Step2Defs` after the last `import` line of `RBM3D.lean`; `RBM3D/Test/Axioms.lean` differs from main only in the registry tables.
4. Stage-2 notes: `STStep2` keeps the probe's `∀ n, s n ≤ lemT (z n)` hypothesis; the preflight found no pin false at a boundary. `STScaleAdm` has no Lean instance in this file (needs `ST_scaleAdm_congr`, which goes with ST2-02 to ST2-04).
