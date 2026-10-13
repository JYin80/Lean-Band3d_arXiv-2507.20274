Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct 13 05:13:16 UTC 2026
Base: `t/T2486` = `main` 66b2ab97 (T2487 merged 268e07d4: `baStep2_oneLoop`, `BA/Step2IterBA.lean:74`). Amend 1 read first (pin `T2486_BACarrierFacts`: LCompat/KCompat unguarded). Scripts (Python only, no Lean): `scratchpad/T2486/{slot,pt,cactus,inst,lines,bandlines}.py`. Targets below = items 1-8 of the ticket's list (1 `BAKcalDecay`; 2 (a) Ward, (b) one-loop, (c) carrier facts; 3 `SEforLnGen_Facts`; 4 (a)(b); 5 ℰ-term decay; 6 KerSums + `B45Gen_Facts`; 7 per-carrier Ward/B45; 8 the two pins).
**Verdicts: 1, 2 (a)(b)(c), 3, 4, 5, 6, 7, 8 PASS** (no pin false; stop rules on pins, slot diameter, comparison text, new kernel, edit of a merged file not hit). **Split decision: the pre-signed 1,950 split APPLIES** (central 2,014 > 1,950; (a) = `KDecayBA` + `SEforLnBA` 1,599 on `t/T2486`, (b) = `B45BA` 415 on `t/T2486b`); C6 notice (2,925) not due at central. Traps for the 1b: rows 11 and 13.
### (i) Exponent table
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | R1 `A=(κ+1)/κ` (T1, crossing 1457 F1 (f)) | 3 at κ=1/2 | `g0²≤g²≤A g0²`, `t0≥κ/(κ+1)` (`TwistStep2_lam0_sq:740`); `ellT` monotone in g, so `ℓ(g0)≤ℓ(g)` where `0<g0` (`baStep5III_lam0_le_lam:399`); only the forward comparison is used | instance `g²/g0²=1.44≤3` (`t0=0.694` vs `1/3`); `ℓ(g0)≤ℓ(g)` on the grid below |
| 2 | `Q` of `W^{-Q}≤g0` (T1) | `Q=d/2=3/2` | WO (`Defs/Sizes:164`): `g0=√t0·lam≥√(κ/(κ+1))W^{-d/2+𝔡}≥W^{-d/2}` iff `W≥W0=((κ+1)/κ)^{1/(2𝔡)}` | `W0=243` at (1/2,1/10); `g0/W^{-3/2}`=2.4 (n=0), 859 (n=50), 2392 (n=100) |
| 3 | far window (T1) | `W^τ>d` | `ℓ(g0)W^τ≤ℓ(g)W^τ≤maxDist≤dL` ⇒ `ℓ(g0)<L` ⇒ `B_{u,0}(g0)≤2g0⁻²≤2W^{2Q}` (`KDecay_B0_le`, `0<g0` eventually) | τ=1/20, n=100: `W^τ=3.77>3`; far `a` exists (`KLmaxDist=8≥3.77`, max 606) |
| 4 | Θ edge | BAProp5 (`FlowPins:173`): `‖Θ(0,a)‖≤C_Θ B_{t,|a|}e^{-c_Θ|a|/ℓ}`, all four charge pairs, `0<g0≤Λ=𝔡⁻¹` (`BAflow_lam0_window`), `(C_Θ,c_Θ)(d,Λ,κ)` before n | translation `‖Θ(a,c)‖=‖Θ(0,c-a)‖` (`EMn2BA:423`); `BAProp5s` not needed (the band needed the short form for equal charges only) | constants are ∃ (not numeric) |
| 5 | M edge (`baPropM_holds`, `MFixedPoint:567`) | `C=16d²/κ³=1152`, `(2C)⁻¹=4.34e-4`, `rate=min(log(1+κ/(4dΛ)),κ/2)=0.004158` | small `g0<(2C)⁻¹`: `‖M_ab‖≤(Cg0)^{|a-b|}≤2^{-|a-b|}`; large: `rate⁻¹e^{-rate|a-b|}`; uniform `B_M=240.5`, `c_M=0.004158`; `M(-)=Mᴴ` by `BAMB_symm`; `ℓ≥1` ⇒ `e^{-c_M|x|}≤e^{-c_M|x|/ℓ}` | instance small branch: `C g0=1.4e-11≤1/2` |
| 6 | one edge bound | `‖edge(x,y)‖≤B e^{-κ'|x-y|}`, `B=C_1W^{2Q}`, `κ'=c/ℓ(g0,u)`, `c=min(c_Θ,c_M)` | leaf Θ, chord `tΘ` (`t<1`), M-edge | — |
| 7 | slot-graph lemma (T1) | vertices: n labels + `n+2|F|` slots; edges: n leaf + |F| chord + `n+2|F|` M: `V=2n+2|F|`, `E=2n+3|F|` | M-edges alone give `|F|+1` components (= nodes, `BAnextSlot_orbit`); chord `J` joins node J to `KLnodePar J` (widths grow), leaf v sits in `KLleafPar v` ⇒ connected; label-label graph distance `≤2n-3` (all F, n=3..7: slot.py), crude `≤V-1≤2n+2n²` | Lean: connectivity + simple walk ⇒ `maxDist ≤ (V-1)·max_e len` (`Σ`-free) |
| 8 | counting exponent | `#TSP(n)`=1,3,11,45,197 (≤2^{n²}); slots ≤k² (actual 3k-6); edges ≤k+k² (actual 5k-9) | `P_k=k²+2Q(k+k²)=k²+d(k+k²)`; `A_k=2^{k²}C_1^{k+k²}`; k=3: P=45 | `|F|≤n-3` seen n≤7 (script), not needed |
| 9 | absorption | `A_kN^{P_k+D}e^{-c_eff N^{𝔠τ}}≤1` eventually (`KDecay_eventually`), `c_eff=c/(V-1)` | N0 (k=3, D=τ=1, 𝔠=1/6): 1e26.7 (c_eff=.1), 1e33.3 (.01), 1e44.6 (1.7e-4) | inside `∀ᶠ`, not an instance hypothesis |
| 10 | 𝒦 numerics at P (T1) | cactus n=3,4 (`baTreeRep`): n=3 equals (Kn3sol)/`BAMLoop` to 1.2e-16; `max|K|` 1.4e-2 (n=3), 3.4e-3 (n=4) at t=0.9 | `|K^{(n)}|≤W^{-d(n-1)}Σ_F(L^d)^{slots}B^{edges}e^{-κ'maxDist/(V-1)}` | ratio `≤7.7e-10` (n=3), `1.9e-18` (n=4), κ'=0.3, t∈{.2,.9,.999} |
| 11 | WardCls ∀n (2 (a)) | route uses `BAReal` only: TK=`BAKsol` (`baKcac_isKLoopS`, `baK_unique`, `baK_rotate`, `baK_ward`), `κ_W=(2iW^dη)⁻¹`, `η=(1-t)Im m` (`ztOf_im`) | Ward defect ≤1e-16 at P, at `g0→-g0` and at `g0=0,E=0,m=i` (n=3,4) ⇒ no `0<g0` | **Trap**: `lam n` is arbitrary before WO; WardCls, KerSums, Θ-sums are ∀n. Use the lemma level (`BAMB_shift`, `BAMB_symm`, `BAMB_row_sq_real`, `BAK_row_sum`, `BATheta_row_sum_pm`: `BASelf`/`BAReal` only), not `baPropM12_holds`/`baPropM_holds`/`baWard_holds` (binders `0<g`, `g≤Λ`) |
| 12 | KerSums, C6 (6) | S=1; mixed: `X=|M|²`, c=1; equal: `c=tr M²/N` (shift+symm), `|c|≤1`; Θ sums: `Σ_b|XΘ|≤(1-t)⁻¹` (Neumann, `‖X‖_∞≤1`), `|Σ_aXΘ|=|c|/|1-tc|≤(1-t)⁻¹` | `C₆=1` | row `(1-t)·max=1.000000` (slack 0, t=0), col 0.988 (equal), 1.000 (mixed) |
| 13 | pins (8), `d<3` | `stWardTypePPingL_of`/`stB45PingL_of` take `hKcal` with no `3≤d`; `BAKcalDecay d` has `3≤d→` | **Trap**: `by_cases 3≤d`; `d<3` is the `3≤d→` of `STIngRgL` (`Step34Gen:377`); `baB45Gen_facts d` is for every d: row 12 facts and `DecayGenTw_baWardPair` are d-free | case split, about 5 lines |
| 14 | ε-free `STKboundgL` (5) | `BAKbound_of_uniform` (`KBound:213-244`) reads `𝔡>0` (`Admissible`, `hflow.1.2.1`), never `hε`; constant `C·A^{k-1}` | `B(g0)≤A·B(g)` | `max B(g0)/B(g)=1.437≤3` (n=100) |
| 15 | Amend 1 (2 (c)) | LCompat: `baStep2Mat_LM` is `rfl` + `loopM_eq_loopL` (any H); KCompat: `baStep2Mat_KI` `rfl`; both for every `sz,lam0,E`; LoopForm needs `0<Im m` (`EMn2BA_mF_data`), so under the flow | check pin consistent; no fallback | — |
| 16 | lines (file lines, lo/central/hi) | `KDecayBA` 851/1,144/1,696; `SEforLnBA` 338/455/710; `B45BA` 295/415/650; row 1,484/**2,014**/3,056 | split `>1,950`: **applies (+64)**; C6 `2,925`: central no, hi yes; stop 2,000/file: none; reserve `KDecayBA2` (`>1,800`): no (hi 1,696) | peers' realized/central 0.78-1.62: row 1,561-3,262 |
### (ii) One concrete nondegenerate instance
`d=3`, `sz0` (`Defs/Sizes:260`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`), `zSeq`, `flow_sz0` (`FlowPins:1181, 1214`) at `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`, `E_n=0` (symmetric spectrum of the adjacency matrix): premises of T1, 2 (a)-(c), 3, 5, 6 (`3≤d`, `0<κ`, `BAFlow`) hold at all n; `s≡1/10<t≡1/2`. T4 (a), T7 keep `STStep2ConclgL`/`STGdecayWgL`, `STConStInd` as hypotheses (T1-BA / window). External hypotheses: none (every merged input is a theorem). Concrete limit: `g²L³=64(n+1)³/(2(n+1))^{12}→0` (1.4e-20 at n=100) ⇒ `Im m→5/6`, `t0→25/36`, `g0/g→5/6` (script uses the Fourier formula for n≤50 and the limit at n=100). The merged flow point `P` (`MFixedPoint:893`, L=4, W=2) carries the kernel numerics. All `∀ᶠ` thresholds (rows 9, 2) are inside the proofs.
```
$ cd scratchpad/T2486; python3 slot.py   # slot graph of the cactus, all F in TSP(n), n=3..7
n  #TSP  |F|max  Vmax=2n+2|F|  Emax=2n+3|F|  max label-label distance  (2n-3)  asserts: one cycle/node, |F|+1 M-components, parent widths grow, connected
3 1 0 6 6 3 3 | counts V,E,slots as formulas: True | max dist == 2n-3: True | <= V-1: True
4 3 1 10 11 5 5 | counts V,E,slots as formulas: True | max dist == 2n-3: True | <= V-1: True
5 11 2 14 16 7 7 | counts V,E,slots as formulas: True | max dist == 2n-3: True | <= V-1: True
6 45 3 18 21 9 9 | counts V,E,slots as formulas: True | max dist == 2n-3: True | <= V-1: True
7 197 4 22 26 11 11 | counts V,E,slots as formulas: True | max dist == 2n-3: True | <= V-1: True
$ python3 pt.py   # merged flow point P=(d,L,g,w)=(3,4,10,6i/5); M=(g0 A-(E+m0))^-1; Ward, KerSums (target 6), C6
P: Im mS=0.261969 t0=0.218307 E=0.0e+00 g0=4.672337 kappa=Im m0=0.560680 (<=1: True) | self_m defect 1.1e-16, M symmetric 1.9e-15, M_aa=m0 4.4e-16
   translation defect 2.7e-15 (5 shifts); Ward sum_b|M_ab|^2 in [1.000000000,1.000000000], column sums in [1.000000000,1.000000000]
   KerSums (+,+): row sums = col sums = c = -0.988190+0.000000j (constant: True); max_t (1-t)*max_a sum_b|thetaKer| = 1.000000, (1-t)*max_b|sum_a thetaKer| = 0.988190 (<= C6=1)
   KerSums (+,-): row sums = col sums = c = 1.000000+0.000000j (constant: True); max_t (1-t)*max_a sum_b|thetaKer| = 1.000000, (1-t)*max_b|sum_a thetaKer| = 1.000000 (<= C6=1)
   KerSums (-,+): row sums = col sums = c = 1.000000+0.000000j (constant: True); max_t (1-t)*max_a sum_b|thetaKer| = 1.000000, (1-t)*max_b|sum_a thetaKer| = 1.000000 (<= C6=1)
   KerSums (-,-): row sums = col sums = c = -0.988190+0.000000j (constant: True); max_t (1-t)*max_a sum_b|thetaKer| = 1.000000, (1-t)*max_b|sum_a thetaKer| = 0.988190 (<= C6=1)
$ python3 cactus.py {P,neg,zero}   # cactus sums K^(3),K^(4) (baTreeRep), Ward (WI_calK), far bound; neg: g0->-g0; zero: g0=0,E=0,m=i
P    self_m defect 1.1e-16 | cactus(F=empty, n=3) vs (Kn3sol)/BAMLoop 1.2e-16 | Ward (WI_calK) defect n=3: 1.0e-16, n=4: 1.4e-17 (2 charge vectors each)
P  n=3  (t, max|K^(n)|, B): (0.2, 3.21e-03, 3.36); (0.9, 1.44e-02, 4.89); (0.999, 4.37e+00, 106) ; max ratio |K|/RHS = 7.7e-10 (<=1: True)
P  n=4  (t, max|K^(n)|, B): (0.2, 2.58e-04, 3.36); (0.9, 3.36e-03, 4.89); (0.999, 1.89e+01, 106) ; max ratio |K|/RHS = 1.9e-18 (<=1: True)
neg  self_m defect 1.1e-16 | cactus(F=empty, n=3) vs (Kn3sol)/BAMLoop 1.2e-16 | Ward (WI_calK) defect n=3: 1.0e-16, n=4: 1.4e-17 (2 charge vectors each)
zero self_m defect 0.0e+00 | cactus(F=empty, n=3) vs (Kn3sol)/BAMLoop 0.0e+00 | Ward (WI_calK) defect n=3: 0.0e+00, n=4: 1.4e-17 (2 charge vectors each)
$ python3 inst.py   # sz0 + flow_sz0 at (1/2,1/10,1/6,1/10): g0, Q=d/2, ell crossing, edge constants, absorption
R1: A=(kappa+1)/kappa=3.0, t0>=kappa/(kappa+1)=0.3333
sz0: n, L, W, lam, t0 (Fourier), g0, g^2/g0^2, W^-3/2, g0/W^-3/2, ell(g),ell(g0) at 1-u=1e-30, ell(g0)<=ell(g) on the 1-u grid
0   4   32             0.01562           0.69374 1.3014e-02   1.4415    5.524e-03  2.356e+00  1 | 4 4 | monotone ell(g0)<=ell(g) on 1-u grid: True
50  204 1.104e+10      8.88e-13          0.69444 7.3998e-13   1.4400    8.620e-16  8.585e+02  1 | 204 204 | monotone ell(g0)<=ell(g) on 1-u grid: True
n=100 (limit t0=25/36 since g^2L^3=1.4e-20): L=404 W=3.363e+11 N=(WL)^3=10^42.40 g=1.4719e-14 g0=1.2266e-14  W^-3/2=5.127e-18  g0/W^-3/2=2392.5 ; WO: W^(-3/2+dd)=7.287e-17 <= lam: True ; sqrt(kappa/(kappa+1))=0.577 >= W^-dd=7.036e-02: True
W0 = ((kappa+1)/kappa)^(1/(2dd)) = 243  (W>=W0 gives W^-3/2<=sqrt(kappa/(kappa+1))W^(-3/2+dd)<=g0); W(n)=(2(n+1))^5 >= W0 from n=1
far set nonempty at n=100: tau=1/20: W^tau=3.770 > d=3; ell(g,1-u=1/2)=1.0; a=(0,(4,0,0),(0,4,0)) has KLmaxDist=8 >= ell*W^tau=3.77 : True (max possible d*L/2=606)
B_{u,0}(g0)/B_{u,0}(g) max over u grid (n=100) = 1.4371 <= A=3 ; 1/t0 = 1.4400
BAPropM: C=16d^2/kappa^3=1152.0, (2C)^-1=4.340e-04, rate=min(log(1+kappa/(4 d Lam)),kappa/2)=0.004158 ; M-edge uniform bound ||M_ab||<=BM exp(-cM|a-b|): cM=min(ln2,rate)=0.004158 BM=max(1,1/rate)=240.50
instance g0=1.227e-14 < (2C)^-1: small branch ||M_ab||<=(C g0)^|a-b|, C g0=1.413e-11 <= 1/2 : True
absorption A_k N^(P_k+D) exp(-c_eff N^(cc*tau)) <= 1 (tau=D=1, cc=1/6, C1=1; a threshold inside the eventually-statement, not an instance hypothesis):
  k=3 P_k=k^2+d(k+k^2)=45 c_eff=1.00e-01 N0=10^26.7
  k=3 P_k=k^2+d(k+k^2)=45 c_eff=1.00e-02 N0=10^33.3
  k=3 P_k=k^2+d(k+k^2)=45 c_eff=1.73e-04 N0=10^44.6
$ python3 lines.py   # lines per file, split, C6, calibration
KDecayBA raw lo/c/hi [740, 995, 1475] x1.15 (slot/NeZero/flow plumbing) -> [851, 1144, 1696] ; band S1-S8 code lines 789 (bandlines.py); S2 band 104 -> 230 (new)
SEforLnBA [338, 455, 710] ; B45BA [295, 415, 650]
row lo/central/hi = [1484, 2014, 3056] ; split line 1950 (central): APPLIES ; (a)=KDecayBA+SEforLnBA central 1599, (b)=B45BA central 415 ; ticket 1100+475+380=1955
C6 notice 1.5*1950 = 2925: central 2014 -> not due ; high 3056 -> due
stop 2000/file on central: KDecayBA 1144, SEforLnBA 455, B45BA 415 -> none above ; reserve KDecayBA2 if KDecayBA > 1800: central 1144, hi 1696 -> not triggered
TLC-4 2.6x central: KDecayBA 2974, SEforLnBA 1183, B45BA 1079, row 5236
realized/central of peers (reports): T2481 0.98, T2487 0.78, T2479b (like for like) 0.99, T2488 0.91, T2470 (T2483 report) 1.62
calibrated row: x0.78 = 1561 ; x1.62 = 3262 ; (a) alone x0.78..x1.62 = 1240..2590
```
### Registry check (`RBM3D/Test/Axioms.lean`, 646 lines in this tree)
`scanPremises` (`:471-492`, `binderConsts` `:451`) collects the Prop-valued `RBM` defs occurring in the binder types of public theorems and drops those that are the conclusion head of some theorem; only an unregistered remainder fails `#assert_rbm_axioms`. Binder constants of the planned public theorems: T1 `baKcalDecay_holds`, T3, T4 (b), T6 `baB45Gen_facts`, T8 both pins, `baStep34_LCompat/KCompat`, `baStep5CasesGen_flowFacts`: none. T2 (a)(b), `baStep2Mat_loopForm`, `baZeroModeGen_kerSums`: `BAFlow` (concluded by `flow_sz0`, `FlowPins:1214`). T4 (a): `BAFlow`, `STStep2ConclgL` (registered `:232`), `STConStInd` (registered `:272`). T5: `BAFlow`, `STDecayLoopUgL` (not registered: head of `stDecayLoopUgL_of_step2`, `DecayGen:583`). T7: `BAFlow`, `STGdecayWgL` (registered `:197`). The private ε-free copy is not scanned. **Lines needed: none added or removed.** Owner-text edits are comment text only (re-locate by name; this tree: `STKcalDecaygL :195`, `STSEforLnConclgL :234`, `STSEforLngL :235`, `STEKDecaygL :236`; the ticket's `:231-233` is 3 lower).
### Per-target verdict and decisions for the 1b
T1 PASS (slot-graph lemma stated in rows 7-8 from merged names, checked on all 257 trees n=3..7; no switch to D1). T2 (a) PASS (row 11), (b) PASS (one-line bridge to `baStep2_oneLoop`, merged), (c) PASS (row 15). T3 PASS. T4 PASS. T5 PASS (row 14). T6 PASS (row 12). T7 PASS (needs row 12 and T1). T8 PASS (row 13 case split).
Decisions: (D1) split applies as above; (b) starts after (a)'s 1a-audit PASS and merges after (a). (D2) no `KDecayBA2` (hi 1,696 < 1,800); the 1b watches 1,800. (D3) C6: U2's twin figure for the ROUTES U line is `KDecayBA` central 1,144 (reserve none); whole-row central 2,014 < 2,925, no notice REQ. (D4) paper-delta candidate T2486a as worded in the ticket (BA far decay of 𝒦 for every charge vector through the cactus with M-edges); numbered at merge. Name-level tables (hypothesis table, `open private` list, clash grep) are left to the start of the 1b (0149 `:98`).
## (b) Script output — part (a) of the pre-signed split: targets 1-5 (`BA/KDecayBA.lean`, `BA/SEforLnBA.lean`); part (b) `B45BA` runs on `t/T2486b`
Branch `t/T2486`, commits `78c19b4d` (05:29:05 UTC, KDecayBA) and `19c7f4c7` (05:42:25 UTC, SEforLnBA, root imports, registry texts); scratch in `scratchpad/T2486/`.
```
$ lake build RBM3D.BA.KDecayBA RBM3D.BA.SEforLnBA 2>&1 | tail -2        # 05:43:41 UTC
Build completed successfully (4097 jobs).
$ lake build 2>&1 | tail -2           # full library with the two import lines in RBM3D.lean, 05:41:19-05:42:25 UTC (runs #assert_rbm_axioms)
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` ...)
Build completed successfully (4347 jobs).
$ lake env lean axioms.lean | sed 's/.*depends on axioms: //' | sort | uniq -c ; grep -c '#print axioms' axioms.lean
  22 [propext, Classical.choice, Quot.sound]
22
$ grep -cE 'sorry|admit|native_decide|^axiom ' RBM3D/BA/KDecayBA.lean RBM3D/BA/SEforLnBA.lean
RBM3D/BA/KDecayBA.lean:0
RBM3D/BA/SEforLnBA.lean:0
```
`axioms.lean` prints the 22 public declarations of both files (14 target declarations including the defs `BAKcalDecay`, `BASEforLn`, and 8 `inst_*`; the `example`s are anonymous).
### (0) Name-level tables of the 1b start (produced late, after `78c19b4d`: the first clash grep, 05:31 UTC, used an unsplit zsh variable and searched nothing; the valid runs are 05:46:24 and 05:46:31 UTC; no name changed because of them)
| field of `SEforLnGen_Facts` (`Chain/SEforLnGen.lean:57`) | BA source (file:line) |
|---|---|
| `∃ E, LoopForm` | `baStep2Mat_loopForm` (SEforLnBA:135) from `EMn2BA_mF_data` (EMn2BA:125) |
| Hermitian | `EMn2BA_seqHflowBA_herm` (EMn2BA:68) |
| `LCompat` / `KCompat` | `baStep34_LCompat` (:122) from `loopM_eq_loopL` (Loop/GLoopFlow:127); `baStep34_KCompat` (:129), `rfl` (`baStep2Mat_KI`, Step2BA:89) |
| `WardCls` | `baZeroModeGen_wardCls` (:66): `zeroModeGen_loopL_wardFam` (ZeroModeGen:234), `baKcac_isKLoopS` (KTreeRep:1674), `baK_unique` (KSolve:568), `baK_rotate` (KSolve:582), `baK_ward` (KWard:305), `BAKcac_spliced` (KTreeDeriv:411) |
| row/col sums, support of `S` | `S n = 1` (`baFM`, FlowPins:322) |
| `Im m ≤ 1` | `EMn2BA_mF_data` (EMn2BA:125) |
| one-loop value | `baKsol_oneLoop` (:113): `.1` of `baStep2_oneLoop` (Step2IterBA:74) |

Target 1 inputs: `baTreeRep` (KTreeRep:1709), `baProp5to8_holds` (Prop6Path:1049), `baPropM_holds` (CombesThomas:562), `BAnextSlot_orbit` (KCactus:403), `EMn2BA_theta_shift` (EMn2BA:424), `baStep5III_lam0_le_lam` (Step5IIIKer:399), `TwistStep2_T0_ge` (TwistStep2:731), `BAflow_real`/`BAflow_lam0_window` (GreenSchur:59, 72).
`open private`: `KDecay_zdistD_symm KDecay_zdistD_tri KDecay_B0_le KDecay_card_TSP KDecay_eventually KDecay_anc_step KDecay_maxDist_two_le` from `Induction.KDecay` (KDecayBA); `KBound_precL_of_loss KBound_B_le` from `BA.KBound` (SEforLnBA). No private deleted, no merged file edited.
Final-name clash grep (declaration lines of the 14 names `^(theorem|def|...) NAME` and the file stems `KDecayBA KDecayBA2 SEforLnBA B45BA`, on `main t/T2473b t/T2482 t/T2482b t/T2483b t/T2484 t/T2484b t/T2485 t/T2489 t/T2490`, 05:46:31 UTC): one hit, the never-merged probe `t/T2473b:RBM3D/Probe/T2473Pins.lean:334: theorem baStep2Mat_loopForm` (as the ticket says); no hit on `main`, no file-stem hit.
### (1) Lines against the stop line, split and C6 decisions
`wc -l`: `KDecayBA.lean` 885, `SEforLnBA.lean` 371 (total 1,256); stop 2,000 per file, reserve `KDecayBA2` not used. Against (a): KDecayBA lo/central/hi 851/1,144/1,696 (realized/central 0.77), SEforLnBA 338/455/710 (0.82), part (a) central 1,599 (0.79). `B45BA` (central 415) is not part of this run, so the whole-row figure is open; with (b) at its central the row would be 1,256 + 415 = 1,671, below 2,925 (no C6 notice). Figure for the ROUTES U line: `KDecayBA` realized 885.
### (2) Numerics
Not rerun: rows 1-16 of (a) stand. Lean-side data: `d = 3`, `sz0`, `zSeq`, `flow_sz0` at `(1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2`, `𝔠_d = 1/100`, `C_d = 1`. One figure differs from (a): Lean uses the crude counts `#slots ≤ n + 2n²`, `#factors ≤ 2n + 3n²` (so `P_k = (k + 2k²) + 2Q(2k + 3k²)`), not row 8's `3k-6`, `5k-9`; the threshold is inside the `∀ᶠ`, the verdicts stand.
### (3) The slot-graph lemma and the route of target 1
Route (`KDecayBA.lean`): `k = 1` vacuous (`maxDist = 0`, `ℓ > 0`); `k = 2`: `BAKsol = BAKcac` (`baK_unique`) so `(Kn2sol)`, the convolution `Θ M^{(σσ')}` bounded by `L^d B³ e^{-κ'|a₁-a₂|}` (`KDecayBA_two_bound`); `k ≥ 3`: `baTreeRep`, each `Γ_M(F)` by `KDecayBA_cactus_bound`, `|TSP k| ≤ 2^{k²}` (`KDecay_card_TSP`). Edges: `KDecayBA_edge_const`, `C₁ W^{2Q} e^{-(c/ℓ_u(g₀))|x-y|}` from `baProp5to8_holds`, `baPropM_holds` and `B_{u,0} ≤ 2 g₀⁻² ≤ 2 W^{2Q}`. Crossing: `ℓ_u(g₀) ≤ ℓ_u(g)` (`KDecayBA_ellT_mono`, `g₀ ≤ g` from `baStep5III_lam0_le_lam`), `ℓ_u(g) < L` from `W^τ > d`. `W^{-Q} ≤ g₀`, `Q = d/2`: `√t₀ ≥ √(κ/(κ+1))` and `W ≥ W₀ = (√(κ/(κ+1)))⁻¹^{1/𝔡}` eventually (`W ≥ N^𝔠`, `N → ∞`). Absorption: `KDecay_eventually`.
Slot-graph lemma (as stated and proved, not as in (a) row 7): `KDecayBA_labels_conn` — any two labels are joined in the graph (leaf `Θ`, chord `In J — Out J`, `M`-edges `s — BAnextSlot s`): slots of one node by `BAnextSlot_orbit` (`KDecayBA_node_conn`), every node to the root node by strong induction on `|F.filter (ArcLe x)|` (`KDecay_anc_step`, `KDecayBA_root_conn`), leaves to their `KLleafPar` node. The walk length is bounded uniformly in `F ∈ TSP n` by a finite supremum (`KDecayBA_walk_bound`, `choose!` + `Finset.sup`), so no explicit diameter formula (`2n-3`) is used; `KDecayBA_gval_bound` turns an `R`-step walk into `e^{-κ' maxDist/(R+1)}`.
### (4) Statement diff against `T2486_*`
```
$ lake env lean pins.lean     # check-file Part 2 defs + imports of both modules + `example (d) : T2486_X d := name d` for X in
$                             # BAKcalDecay BAWardCls BAOneLoop BACarrierFacts BAFlowFacts BASEforLnFacts BASEforLn BAEtermDecay (+ a `fun R =>` variant of BASEforLn),
$                             # and the (4a) shape (as a Prop and as a term proof): 11 examples
exit=0 lines=0 errors=0 examples=11            # 05:43:44 UTC; a deliberately wrong example (Ward for Kcal) fails with `Type mismatch`
$ python3 stmts.py 175 | cut -c1-205     # statements extracted from the files (truncated; exactness is the `example`s above)
KDecayBA.lean:688: def BAKcalDecay (d : ℕ) : Prop := 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z) 
KDecayBA.lean:692: theorem baKcalDecay_holds (d : ℕ) : BAKcalDecay d
SEforLnBA.lean:66: theorem baZeroModeGen_wardCls (d : ℕ) : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (baFMz sz z)
SEforLnBA.lean:113: theorem baKsol_oneLoop (d : ℕ) : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L...
SEforLnBA.lean:122: theorem baStep34_LCompat (d : ℕ) : ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ), Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0)
SEforLnBA.lean:129: theorem baStep34_KCompat (d : ℕ) : ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ), Step34Gen_KCompat (baStep2Mat sz lam0 E)
SEforLnBA.lean:135: theorem baStep2Mat_loopForm (d : ℕ) : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflow...
SEforLnBA.lean:143: theorem baStep2Mat_carrierFacts (d : ℕ) : (∀ (sz : Sizes d) (lam0 E : ℕ → ℝ), Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0) ∧ Step34Gen_KCompat (baStep2Mat sz ...
SEforLnBA.lean:152: theorem baStep5CasesGen_flowFacts (d : ℕ) : Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
SEforLnBA.lean:163: theorem baSEforLnGen_facts (d : ℕ) : SEforLnGen_Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz...
SEforLnBA.lean:198: theorem baSEforLnConclgL_of (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 Cd 𝔠d : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hCd : 0 ...
SEforLnBA.lean:213: def BASEforLn (d : ℕ) : Prop := ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), STSEforLngL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε...
SEforLnBA.lean:221: theorem baSEforLn_holds (d : ℕ) : BASEforLn d := fun R => stSEforLngL_of d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baSte...
SEforLnBA.lean:271: theorem baEtermDecaygL (d : ℕ) : 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n...
```
Compiled nonempty instances (`d = 3`, `sz0`, `zSeq`, `flow_sz0`; extracted by script, heads and first proof line):
```
KDecayBA.lean:823 theorem inst_baKcalDecay : STKcalDecaygL (baFMz sz0 zSeq) := baKcalDecay_holds 3 le_rfl sz0 (1/2) (1/10) (1/6) (1/10) zSeq (by norm_num) flow_sz0
KDecayBA.lean:875 theorem inst_baKcalDecay_far : ∃ n, ellT (sz0.L n) (sz0.lam n) 0 * (W n)^(1/20) ≤ KLmaxDist 3 (sz0.L n) (instA n) ∧ ‖(baFMz sz0 zSeq).K n 0 ![+,-,+] (instA n)‖ ≤ (W n)^(-1)
SEforLnBA.lean:314 theorem inst_wardCls : ZeroModeGen_WardCls sz0 (baFMz sz0 zSeq) := baZeroModeGen_wardCls 3 sz0 (1/2) (1/10) (1/6) (1/10) zSeq (by norm_num) flow_sz0
SEforLnBA.lean:318 theorem inst_oneLoop : ∀ᶠ n ..., K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then m n else conj (m n) := baKsol_oneLoop 3 sz0 ... flow_sz0
SEforLnBA.lean:325 theorem inst_carrierFacts : (LCompat ∧ KCompat) ∧ LoopForm := ⟨(baStep2Mat_carrierFacts 3).1 sz0 _ _, (baStep2Mat_carrierFacts 3).2 sz0 ... flow_sz0⟩
SEforLnBA.lean:333 theorem inst_flowFacts : ∃ κm, 0 < κm ∧ sz0.Admissible (1/6) (1/10) ∧ ... := by obtain ⟨κm, hκm, hF⟩ := baStep5CasesGen_flowFacts 3 (1/2) ...; exact ⟨κm, hκm, hF sz0 ... flow_sz0⟩
SEforLnBA.lean:340 example := baSEforLnGen_facts 3 sz0 (1/2) (1/10) (1/6) (1/10) zSeq (by norm_num) flow_sz0
SEforLnBA.lean:344 theorem inst_seforLnConclgL (hStep2 : STStep2ConclgL (baFMz sz0 zSeq) (seqP (sz0.withLam 0)) (fun _ => 1/10) (fun _ => 1/2) 1) : STSEforLnConclgL ... := baSEforLnConclgL_of 3 le_rfl sz0 ... 1 (1/100) zSeq ... (s1Setup_conStInd_const ..) hStep2
SEforLnBA.lean:354 theorem inst_baSEforLn : STSEforLngL 3 STAny ... := baSEforLn_holds 3 STAny
SEforLnBA.lean:361 example (hU : STDecayLoopUgL ... (fun _ => 1/10) (fun _ => 1/2)) := baEtermDecaygL 3 le_rfl sz0 ... flow_sz0 (fun _ => 1/10) (fun _ => 1/2) ... hU 3 (by norm_num) ![true, false, true]
```
`instA n = ![0, fun _ => ((L n / 2 : ℕ) : ZMod (L n)), 0]`; `maxDist ≥ 3 (2(n+1)) ≥ W^{1/20}` at every `n` (`inst_far`), so the far set of `STKcalDecaygL` is nonempty at `k = 3`, `τ = 1/20`, `u = 0` (`ℓ_0 = 1`). Hypotheses left in instances: `STStep2ConclgL` (T1-BA's pin), `STDecayLoopUgL` (T7-BA's); `STConStInd`, the times, `𝔠_d C_d ≤ 1/30`, `BAFlow`, `0 < κ, ε` are discharged.
### (5) Hypotheses as used, copies, `open private`
Theorems with hypotheses: `baSEforLnConclgL_of` (`0 < ε` for `baKward_holds`, `STConStInd`, `𝔠_d C_d ≤ 1/30`, times, `STStep2ConclgL` of T1-BA); `baEtermDecaygL` (times, `STDecayLoopUgL`: the consumer's input); every other target takes only `3 ≤ d`, `0 < κ`, `BAFlow` (`baStep34_*`: nothing; `baSEforLn_holds`, `BASEforLn`: every regime `R`).
Copies (private, `SEforLnBA_`): `Ksol_isKLoopS` = `BAKsol_isKLoopS` (KSolve:606) with existence from `baKcac_isKLoopS`, so `BAReal` only (no `0 < g₀`, no `BAKsolve`); `Kbound` = body of `BAKbound_of_uniform` (KBound:213-244) without the unused binder `0 < ε` (it uses `0 < 𝔡` of `BAFlow`). No RBM1D/RBM2D port (no `git diff --stat` there); `KDecayBA` follows this repository's `Induction/KDecay.lean` §1-§8, whose privates are reached by `open private`.
### (6) UBA-C1 table and greps
Crossing (target 1 only): `ℓ_u(g₀) ≤ ℓ_u(g)` in `KDecayBA_far_const` (`KDecayBA_ellT_mono`, `g₀ ≤ g` from `baStep5III_lam0_le_lam`); `W^{-Q} ≤ g₀` from `TwistStep2_T0_ge` and `(eq:WO)`; no comparison text, R1 not used. Targets 2-5: no crossing.
```
$ grep -nE '\|E\||norm_mE|mSigma|SB d|zt E|etaT|STFlow|STflowE|seqHflow [^B]|lemT' KDecayBA.lean SEforLnBA.lean        -> 0 hits
$ grep -n withLam ... | grep -v 'seqP (sz.withLam 0)\|seqP (sz0.withLam 0)'  -> 1 hit, SEforLnBA.lean:20, module docstring (`seqP ∘ withLam 0`)
$ grep -nE 'gK|≤ A \*' ...    -> 0 hits (the local absorption constant `A` was renamed `Ak`; it is not R1's `A`)
$ grep -n STGridRepNgL ...    -> 0 hits;   X1-C4 `(def|abbrev|structure) (ZeroModeGen_WardCls|...|Step5CasesGen_FlowFacts)` -> 0 hits
$ grep -cE 'KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP' SEforLnBA.lean KDecayBA.lean  -> 0 and 18 (KDecayBA only)
$ git diff main...t/T2486 --stat -- RBM3D/Chain RBM3D/Induction RBM3D/Loop | wc -l -> 0 ;  git diff main...t/T2486 --name-only -> RBM3D.lean, BA/KDecayBA.lean, BA/SEforLnBA.lean, Test/Axioms.lean
$ grep -rn 'import RBM3D.BA.KDecayBA\|import RBM3D.BA.SEforLnBA' RBM3D RBM3D.lean -> SEforLnBA.lean:9 (KDecayBA), RBM3D.lean:575, :576
```
### (7) Registry lines
`RBM3D/Test/Axioms.lean`: owner texts only (comment text): `STKcalDecaygL` (:195) "owner U2-BA (`BAKcalDecay`)" became "BA: `baKcalDecay_holds` (T2486)"; `STSEforLnConclgL`, `STSEforLngL`, `STEKDecaygL` (:234-236) "BA: U2-BA" became "BA: `baSEforLnConclgL_of`, `baSEforLn_holds`, `baEtermDecaygL` (T2486)" (4 lines changed). No registry line added or removed; the full `lake build` (above) passed `#assert_rbm_axioms` with the two import lines.
## (c) Verified Mathlib names (`#check` of 65 names in `scratchpad/T2486/mathlib.lean`, no error)
`Relation.ReflTransGen.{head_induction_on,head,tail,trans,single,refl}`, `Finset.{single_le_sum,sum_le_sum,sup_le,le_sup,card_le_univ,sum_const,prod_le_prod₀,prod_mul_distrib,prod_const}`, `Real.{exp_sum,exp_le_exp,exp_le_one_iff,exp_add,rpow_def_of_pos,log_inv,log_pos,rpow_natCast,rpow_inv_rpow,pow_rpow_inv_natCast,one_le_rpow,rpow_le_rpow,rpow_le_rpow_of_exponent_le,rpow_mul,rpow_add,rpow_neg,sqrt_le_sqrt,sqrt_pos,sq_sqrt}`, `Function.iterate_succ_apply'`, `Matrix.{one_apply,conjTranspose_apply,smul_apply}`, `norm_sum_le`, `pow_le_pow_{left,right}₀`, `le_self_pow₀`, `one_le_pow₀`, `pow_le_one₀`, `inv_le_one_of_one_le₀`, `inv_anti₀`, `div_le_div_of_nonneg_right`, `le_div_iff₀`, `div_le_iff₀`, `Complex.{norm_real,norm_natCast}`, `Filter.Eventually.exists`, `tendsto_rpow_atTop`, `Nat.{le_self_pow,pow_le_pow_left}`, `ZMod.val_natCast_of_lt`, `Fintype.{card_fun,card_sum,card_coe}`. Absent or deprecated: `Relation.ReflTransGen.symm` (absent); `Relation.ReflTransGen.symmetric`, `Symmetric` (deprecated for `stdSymm`, `Std.Symm`; replaced by the private `KDecayBA_rtg_symm`, `KDecayBA_adj_symm`).
## (d) Open issues and paper-delta candidates
- Part (b) (`B45BA`, targets 6-8: `KerSums`, `B45Gen_Facts`, per-carrier Ward/B45, the two pins) is not delivered here: the 1a's pre-signed split applies; it runs on `t/T2486b`, importing `SEforLnBA` and `KDecayBA`.
- Late start tables: (0) was produced after the first Lean file (see (0)). The `T2486_EtermDecay` helper def is not added: `baEtermDecaygL` states the four conjuncts inline; the pin's `example` compiles by unfolding.
- Observation for the dispatcher: the merged pins `BAKbound`, `baKbound_holds` carry `0 < ε`, which their proof never uses; this row keeps an ε-free private copy (ticket note (2)); a merged ε-free successor would remove the copy.
- Observation: at `sz0` (`W ≫ L`) the far set of `STKcalDecaygL` is empty for `τ = 1`; the instance uses `τ = 1/20` (a property of the data, as in `Induction/KDecay.lean` §8).
- Paper-delta candidates: `T2486a` (ticket): BA far decay of `𝒦` for every charge vector through the cactus with `M`-edges (the paper proves only the pure loop, `lem_pureloop`, `A:643-660`). `T2486b`: `W^{-Q} ≤ g₀`, `Q = d/2`, holds only for `W ≥ W₀(κ,𝔡)`, i.e. eventually in `n` (the paper's "N large", `1_2:366`). `T2486c`: the cutoff of `STKcalDecaygL` is at `ℓ_u(g)` while the proof runs at `ℓ_u(g₀) ≤ ℓ_u(g)`, `0 < g₀` (UBA-C1 crossing). `T2486d`: Lean's walk bound `R_k` and the counts `#slots ≤ n + 2n²`, `#factors ≤ 2n + 3n²` are existential/crude, not the diameter `2n-3` of the preflight script.
