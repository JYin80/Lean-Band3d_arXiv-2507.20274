Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 19:28:16 UTC 2026

Notation: g = ilambda, x = 1-u, A = g²W^d, B_{u,0} = (g²+x)^{-1} + (L^d x)^{-1} (`Defs/Params.lean:35-36`, `1_2:1107-1110`), d = 3. Paper-delta ids D485-D489 = T2191a-e (`docs/paper-deltas.md:1444-1448`). Scratch scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2204/{blocks,shape,pins,table,final}.py`.

### (i) Exponent table

| quantity | value | constraint (source) | slack |
|---|---|---|---|
| d | 3 | `3 ≤ d →` in every pin; `(K+1)^(d-2)` = 1 at K = 0 | 0 |
| κ, ε, 𝔡 | 1/10 each | `> 0` | - |
| 𝔠_d | ∃ in (0, 1/100], chosen before 𝔠 | `1_2:1295`; d𝔠_d < 1 so `(1-t)/(1-s) ≥ (W^{-d}B)^{𝔠_d} ≥ W^{-1}` eventually (`3_5:1637`) | d𝔠_d ≤ 3/100: 97/100 |
| 𝔠 | 1/6 | `W ≥ N^𝔠`; sz0 n=0: N = 2^21, N^{1/6} = 11.31 ≤ W = 32 | factor 2.83 |
| WO | 𝔡 = 1/10 | `W^{-d/2+𝔡} ≤ g ≤ 1/𝔡`: sz0 n=0 `W^{-1.4}` = 0.0078 ≤ 1/64; szB g = 1; szG g = 5 ≤ 10 | 2.0 / 7 / 2.0 |
| target | exponents 2, 1/5 | `(Eq:Gtlp_exp_flow)` `1_2:1392`: `B²(A^{-1/5} + B)`, B := W^{-d}B_{u,0}; `lam n > 0` from WO (`0^{-1/5} = 0` in Mathlib) | sz0 n=0: A = 8, A^{-1/5} = 0.6598 > 0 |
| LK×LK drift | 11/5 = 2 + 1/5 | (iii) `x ≥ g²`: `∫((1-v)/(1-u))² x_v^{-1}B_v^{11/5} ≲ x^{-2-1/5}W^{-11d/5}` vs `B²A^{-1/5}`; ratio `(g²/x)^{1/5} ≤ 1` (kernel `3_5:1622`, power n = 2) | 0 at x = g²; at u = t (sz0): 0.1919 |
| LW drift | 5/2 | (iii): ratio to `B²A^{-1/5}` is `A^{1/5}(W^d x)^{-1/2} ≤ A^{-3/10}` for x ≥ g², A ≥ W^{2𝔡} ≥ 1 | 5/2 - 11/5 = 3/10; A = 8: 0.5359 |
| (iii) initial term | ratio `(1-s)B_s / ((1-u)B_u)` | ≤ `(1+L^{-3})/(1/2+L^{-3})` < 2, squared ≤ 4 | L = 4: 1.9697 |
| (iv) kernel | `∫ x^{-1}(Nx)^{-3}((1-v)/(1-u))² dv` | ≲ `(Nx)^{-3}`; drift `W^dL^d(Nx)^{-4} = x^{-1}(Nx)^{-3}` (`6:65`, `6:77`); `(W^{-d}B)=(Nx)^{-1}` so target ≥ `(Nx)^{-3}` | factor 1 - x_u/x_s = 1/3 at (5/8, 3/4) |
| (i), (ii) | B ≍ g^{-2} (both windows) | `B^{11/5} ≍ B²A^{-1/5}`; `∫x^{-1}dv ≤ 2 log L` (i), `(d-2) log L` (ii), absorbed by `W^{Cε}` | order 0 (log L ≤ W^ε eventually) |
| kernel windows | (i) `3_5:1649` `t ≤ 1-g²/L²`; (ii) `3_5:1667` `1-s ≤ g²/L²` | (i) `1-t ≥ g²/L²`; (ii) `1-s ≤ g²/L²` hold in the regime; (ii), σ₁=σ₂: NAL excluded (D485) | 0 at the boundary data |

Pins vs paper (verdict of each of the 40 `Prop`s; paper lines `1_2:`, `3_5:`, `6:`; mode U = uniform in u ∈ [s_n,t_n] (union inside `Prec`), T = per time sequence, F = deterministic, fixed n). §29 (3)-(7) for all: `L^d ≤ W^K` is no premise (`Bandwidth` in `STFlow`); premises `∀ n`, `∀ᶠ n` only for mollifier properties and `STExpDuhEqQ`; `0 < lam n` eventually from WO; scale `N = sz.size` via `Prec`.

| pin(s) | paper | class (ticket) | mode | verdict and check |
|---|---|---|---|---|
| `STExp2U` | `1_2:1392-1396`, endpoint `1396` | owed (S6-13) | U | PASS; diff vs `STExp2` (`Defs.lean:159-165`): only the index `TimeIcc s t n ×…` and `τ n ↦ p.1` |
| `STIngR6` | `1_2:1281`, `1295-1297`; `6:58-79` | struct | - | PASS; vs `STIngR5` dropped `STKbound STKward STDecayStrong STStep1Loop`, `STStep2Concl→STStep2Core`, no `∀ Cd` (D486); `grep` of `6:93-152` for `Gdecay+IND_s<g`, `lRB1`, `Gtmwc`, `Gt_bound+IND`: 0 hits; Step-1 range excluded from `6:84` (`Gt_bound_flow` is Step 2) |
| `STStep2Core STStep6R STStep6Concl STRegSeq` | `1_2:1342-1344` | struct | U/- | PASS (shapes) |
| `STStep6I..IV` | `6:97`; `6:94-96` | owed (S6-02 skeleton + ingredient tickets) | U | PASS; regimes are the merged `STReg5I..IV` (`Step5Pins.lean`), rows in (ii) |
| `STStep6` | `6:93-97` | owed (S6-13) | U | PASS; `STAny` = `True`; implies each regime (`ST_step6R_of_any`) |
| `STImproveExpAver STExpAvgAt` | `6:12-17` | owed (S6-03) | T | PASS; premises `LWAvgLaw`=`(Gt_avgbound_flow)`, `STLK`=`(Eq:L-KGt-flow)` at u (D487) |
| `STExpAvgU` | `6:14-16` | struct | U | PASS |
| `STExpHier` | `3_5:73` at n=2 (sum over `3 ≤ ℓ ≤ n` empty), `6:90` | owed (S6-04) | F | PASS; `∂_u f = Θf + D`, D = E ℰ^{LK×LK} + E ℰ^{Gc}, martingale term has mean 0 |
| `STExpDuhamelZ STExpDuhEq` | `6:3-7`, `142-146` | owed (S6-05) / struct | F / along seqs | PASS; `A=∅` plain, `A={1,2}` regime (ii) |
| `STExpDuhamelQ STExpDuhEqQ` | `6:109-116` | owed (S6-05) / struct | F / `∀ᶠ n` | PASS; source `STExpQsrc` = `Q D + [Q,Θ]f - (Pf)∂ϑ`, sign `-` as printed `6:115` |
| `STDriftHi` | `6:58`, `6:83` | struct | - | PASS; `g²/L^d ≤ 1-t`: true at (i),(ii),(iii), false at (iv) (table in (ii)) |
| `STExpLKLKHi (+Concl)` | `6:58-62` | owed (S6-06) / struct | U | PASS; `(1-u)^{-1}B^{11/5}`; `Σ_b B_{u,|a-b|}e^{-(|a-b|/ℓ)^{1/2}} ≲ ℓ²/(g²+x) + 1 ≲ x^{-1}` from `ℓ² ≤ g²/x` (`1_2:1121`) |
| `STExpEGtHiConcl STExpDriftHiConcl` | `6:83-88` | struct | U | PASS; `5/2`, `(1-u)^{-1}` |
| `STExpDriftLo (+Concl)` | `6:63-66`, `73-79` | owed (S6-07) / struct | U | PASS; F-iv: `(Exp(L-K)1)` unusable in (iv) since `g²B ≥ g²/(L^d x) → ∞` |
| `STExpDriftDecay (+Concl)` | `3_5:1634` | owed (S6-07) / struct | U | PASS; `(deccA0)` for deterministic D_u, `∀ ε D` w.h.p. |
| `STExpWardI (+Concl)` | `6:104-107`, `121-131` | owed (S6-10) / struct | U | PASS; uniform in u, paper at t (D488) |
| `STExpWardII (+Concl)` | `6:137-141` | owed (S6-12) / struct | U | PASS; `(Nη_u)^{-1} ≤ W^{-d}B` since `B ≥ (L^d x)^{-1}`, bulk `Im m ≥ c(κ)` (D488) |
| `STExpIntConcl STExpIntQConcl` | `6:94-132` | struct | U | PASS; `Q^{(A)}f_u ≺ F + B²(A^{-1/5}+B)` |
| `STExpIntIII STExpIntIV` | `6:94-96` | owed (S6-08) | U | PASS; rows (iii), (iv) above |
| `STExpIntII` | `6:97`, `142-147` | owed (S6-12) | U | PASS; σ₁=σ₂ via `(sum_res_Ndecay_nonzero)` at A=∅ (D485) |
| `STExpIntI STExpIniI (+IniIConcl)` | `6:97`, `104-132`, `117`; `3_5:1649,1659` | owed (S6-09, S6-11) / struct | U | PASS; row (i); `L^∞`-only kernel would lose `((1-s)/(1-t))²` |

### (ii) Concrete nondegenerate instance (d = 3, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6)

Data: szB (L=4, W_n=n+4, g=1) with zB; sz0 (L_n=4(n+1), W_n=(2(n+1))^5, g_n=(2(n+1))^{-6}) with z0; szG (szB with g=5) with zB (`Step34Pins.lean:710-785`, `Step5Pins.lean:495-520`, `Sizes.lean:260`).
```
$ python3 …/T2204/final.py
(i)   szB  g2=1 g2/L2=1/16 g2/L3=1/64 1-t=1/16 1-s=1/8 in=['i'] DriftHi=True 0<=s<t:True
(ii)  szB  g2=1 g2/L2=1/16 g2/L3=1/64 1-t=1/32 1-s=1/16 in=['ii'] DriftHi=True 0<=s<t:True
(iii) sz0  g2=1/4096 g2/L2=1/65536 g2/L3=1/262144 1-t=15/16 1-s=1 in=['iii'] DriftHi=True 0<=s<t:True
(iv)  szG  g2=25 g2/L2=25/16 g2/L3=25/64 1-t=1/4 1-s=3/8 in=['iv'] DriftHi=False 0<=s<t:True
lemT(zB)=0.983992 >= 31/32; lemT(z0,n=0)=0.999991 >= 1/16
sz0 n=0: L=4 W=32 lam=1/64 N=2097152  lam^2 W^3 = 8 ; WO: W^(-1.4)=0.0078 <= lam,  szB/szG lam=1,5 <= 1/dd=10
(i)   szB  (1-t)/(1-s)=0.5000<1; W^-d B_t0 at n=0,10,1000: 1.86e-02 4.34e-04 1.18e-09 (->0); (W^-d B)^(1/100)<=ratio from n>=11472512971 on
(ii)  szB  (1-t)/(1-s)=0.5000<1; W^-d B_t0 at n=0,10,1000: 2.30e-02 5.36e-04 1.45e-09 (->0); (W^-d B)^(1/100)<=ratio from n>=12304834824 on
(iii) sz0  (1-t)/(1-s)=0.9375<1; W^-d B_t0 at n=0,10,1000: 3.31e-05 7.91e-21 3.26e-50 (->0); (W^-d B)^(1/100)<=ratio from n>=0 on
(iv)  szG  (1-t)/(1-s)=0.6667<1; W^-d B_t0 at n=0,10,1000: 1.60e-03 3.72e-05 1.01e-10 (->0); (W^-d B)^(1/100)<=ratio from n>=346246 on
iii closure at u=t: 11/5-term (g2/(1-u))^(1/5)=0.1919; 5/2-term <= (g2W^d)^(-3/10)=0.5359 (g2W^d=8); init ratio sup (1+L^-3)/(1/2+L^-3)=1.9697<2
iv: 1-(1-u)/(1-s)=1/3 at (5/8,3/4); xB in [L^-3,2L^-3] => init ratio<=2
d*c_d <= 3/100 < 1 ; 5/2-11/5 = 3/10 ; 11/5-2 = 1/5
```
Each datum lies in its own regime and in no other; (i) has `1-t = g²/L²` and (ii) has `1-s = g²/L²` exactly (boundary data); `0 ≤ s` is explicit in `STIngR6`; the window `STDriftHi` holds at (i)-(iii) and fails at (iv). Time bounds `t ≤ lemT z`: szB/zB `t ≤ 31/32 ≤ lemT = 0.9840`; z0 `t = 1/16 ≤ lemT`.
`(con_st_ind)` is `∀ᶠ n` and must hold for every 𝔠_d > 0 (merged `conStInd_const`, `sz0_con`): the limit is `W_n^{-3}B_{t,0} → 0` (B bounded: ≤ 1/(1-t) + L^{-3}/(1-t)) with `(1-t)/(1-s)` fixed < 1; the table gives thresholds for 𝔠_d = 1/100 (n ≥ 1.1e10, 1.2e10, 3.5e5, 0), as already in `T2191-prove.md:(d)` item 3. This is a property of the asymptotic statement, not of a witness: the instances are sequences, every deterministic hypothesis is a closed-form statement for all n.
Stochastic premises left as hypotheses in the instances (other gates' pins, with limits above): `LWAvgLaw`, `STLK` at `tInst`, `STDecay`, `STExp2`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW` at s; sz0 has `g_n² W_n^3 = (2(n+1))^3 → ∞` (A = 8 at n = 0), szB `(n+4)^3`, szG `25(n+4)^3`. The deterministic pins at sz0, n=0, E=1/2: `|E| < 2`, `0 ≤ 1/4 ≤ 1/2 < 1`, nonempty index sets (`s n ∈ TimeIcc`, `![true,false]`, `0`), mollifier from `stMollifierEx_holds` with `g_0 = 1/64 ≤ 1`.

Move checks (`python3 …/blocks.py`, `…/pins.py`; git grep on HEAD b3c37aa):
```
blocks (probe 96c6b4c) 46-165:120 401-717:317 1644-1646:3 1737-1836:100 1838-1843:6 1860-1906:47 2077-2127:51 2226-2229:4 2259-2279:21 2281-2289:9 total 678
decls in blocks 80 = 47 def + 33 theorem; outside the blocks 114
S6-02 names referenced inside blocks (comments stripped): []   st6_ idents: st6_idx2_nonempty st6_idxMixed_nonempty st6_idxSame_nonempty
Prop defs: 40 owed listed 20 struct listed 20 union equal: True disjoint: True ; non-Prop defs: STExpErr STExpELKLK STExpEGt STExpDrift STExpTarget STExpQsrc
name-clash: 80 names, hits on HEAD b3c37aa (git grep -lwF RBM3D RBM3D.lean): 0 ; "Step6Pins" in docs/tickets: T2204, T2206 (reads only), check file
```
Consumers (§45 O2): every consumer of the ticket's list (`ST_step6_caseI..IV_of_pins` :1452 :1370 :1242 :1291, `ST_mainInd_of_steps` :351, `st6_expAvgU_of_pin` :1062, `st6_duhEq_of_pin` :866, `st6_duhEqQ_of_pin` :1338, `st6_EGtHi_of_LW` :1076, `ST_step6_compose` :1650) is a probe declaration outside the ten blocks that mentions the moved pins (`table.py`); the probe compiled against exactly the moved text (`T2191-audit.md` §1: 142 theorems on the three standard axioms). S6-03..S6-12 each prove one or two pins with this statement (table above).
Registry plan: append 20 owed + 20 structural lines (lists equal the `pins.py` partition); `InstIng6Concl` is a `def … : Prop` (`Step6Inst`) like the unregistered `InstIng5Concl`; if the pre-check flags it, register it owed (§20) and list it.

### Verdicts
- Target 1 (verbatim move of ten blocks, no S6-02 name): PASS. Target 2 (imports): PASS (closure per ticket; no math dependence). Target 3 (registry, 20 + 20): PASS. Instances (30 theorems at the four data): PASS.
- All 40 pins vs their paper lines: PASS (no FAIL). Observations (not failures): structural pins other than `STRegSeq` carry no "Registry class" tag in their docstrings (text must stay verbatim); `STExp2_of_STExp2U`, `STExp2U_iff`, `STExpLKLKHi`, `STDriftHi`, `STRegSeq`, `STExpEGtHiConcl` have no instance in this file by the ticket (S6-02 compiles `inst_endpoints`, `inst_hiI..III`, `inst_compose`); their hypotheses are jointly satisfiable at (iii) data (`s ≤ t`: 0 ≤ 1/16; the stochastic premise is the pin STExp2U itself).
- Overall: PASS.

## (b) Script output — Mon Oct  5 19:33:40 UTC 2026

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2204 && git log --oneline -1 && git diff --stat b3c37aa HEAD
a0e4ad8 T2204: S6-01 Induction/Step6Pins (Step-6 pins, verbatim move from T2191 probe 96c6b4c) and registry
 RBM3D/Induction/Step6Pins.lean | 734 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |  44 ++-
 2 files changed, 776 insertions(+), 2 deletions(-)
$ lake build RBM3D.Induction.Step6Pins RBM3D.Test.Axioms   (tail; warnings from upstream files omitted)
⚠ [3801/3805] Replayed RBM3D.Induction.NewPQ


Build completed successfully (3805 jobs).
$ lake build   (full library, worktree root has no Step6Pins import; runs #assert_rbm_axioms)
Build completed successfully (4007 jobs).
lake build  30.67s user 6.14s system 109% cpu 33.484 total
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Induction.Step6Pins; #assert_rbm_axioms) -> exit 0
axiom audit: 6043 theorems, 2154 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
154:registry: 2 borrowed + 144 owed + 79 structural + 4 refuted; 100 registered premise(s) carry nothing yet: [RBM.Loop.
unregistered / error / InstIng6 hits in pre-check output: 0
$ #print axioms of the 33 theorems (ax.lean), summarised
theorems printed: 33; lines with exactly [propext, Classical.choice, Quot.sound]: 33; sorryAx lines: 0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/Step6Pins.lean | wc -l
       0
$ python3 verb.py   (each probe block via git show 96c6b4c:RBM3D/Probe/T2191Pins.lean | sed -n a,bp; `block in text`)
46 165 True;401 717 True;1644 1646 True;1737 1836 True;1838 1843 True;1860 1906 True;2077 2127 True;2226 2229 True;2259 2279 True;2281 2289 True;
$ diff concat-of-blocks Step6Pins.lean : lines only in the file / only in the blocks
56 / 0  (the added lines are: copyright, 4 imports, module docstring, :39-44, namespace/open/variable scaffolding, 3 x end, blank lines)
$ check-file equality: eq.lean = check imports + Step6Pins + check sections 1-2 + 46 `example : @T2204Check.X = @X := rfl`; lake env lean eq.lean
exit 0; error lines: 0; examples: 46
$ name-clash: git grep -lwF <name> main -- RBM3D RBM3D.lean, for the 80 new public names (47 def + 33 theorem), main = 98e6d5b
hits: 0 (script printed 'hits 0'; 80 distinct names)
$ registry diff (git diff b3c37aa HEAD -- RBM3D/Test/Axioms.lean): added lines / removed lines
42 / 2   (40 new lines; the 2 changed lines are the old last entries of owedProps and structuralProps, only `]` -> `,`)
owed new: 20; structural new: 20
$ statements of the 33 theorems (script: signature up to `:=`, whitespace collapsed, cut at 190 chars)
L79: theorem STExp2U_iff (E s t : ℕ → ℝ) : STExp2U sz E s t ↔ Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p _ => ‖STExpErr sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ))   [`sed -n 79,86p`; the script's cut at the first `:=` truncated this line]
L87: theorem STExp2_of_STExp2U {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2U sz E s t) : STExp2 sz E t
L149: theorem ST_step6R_of_any {d : ℕ} (h : STStep6 d) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : STStep6R d R
L513: theorem inst_ing6 (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (sz : Sizes 3) (z : ℕ → 
L525: theorem inst_ing6_I (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R szB (fun _ => 
L534: theorem inst_ing6_II (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R szB (fun _ =>
L543: theorem inst_ing6_III (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R sz0 sInst tI
L550: theorem inst_ing6_IV (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR6 3 R Concl) (hR : R szG (fun _ =>
L560: theorem inst_step6I (h : STStep6I 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
L564: theorem inst_step6II (h : STStep6II 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)
L568: theorem inst_step6III (h : STStep6III 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst
L572: theorem inst_step6IV (h : STStep6IV 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
L577: theorem inst_step6 (h : STStep6 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst
L582: theorem inst_step6_atI (h : STStep6 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
L596: theorem inst_expDriftLo (h : STExpDriftLo 3) : InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
L602: theorem inst_expDriftDecay (h : STExpDriftDecay 3) : InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
L607: theorem inst_expWardI (h : STExpWardI 3) : InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
L613: theorem inst_expWardII (h : STExpWardII 3) : InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpWardIIConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)
L619: theorem inst_expIniI (h : STExpIniI 3) : InstIng6Concl (fun sz E s t => STExpIniIConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
L624: theorem inst_expIntI (h : STExpIntI 3) : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl sz E s t → ST
L629: theorem inst_expIntII (h : STExpIntII 3) : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed 
L634: theorem inst_expIntIII (h : STExpIntIII 3) : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t) sz0 z0 sInst tInst
L638: theorem inst_expIntIV (h : STExpIntIV 3) : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftLoConcl sz E s t → STExpIntConcl sz ∅ STSigAll E s t) szG zB (fun _ => 5 / 8) 
L653: theorem inst_improveExpAver (h : STImproveExpAver 3) (hA : LWAvgLaw sz0 (STflowE z0) tInst) (hK : STLK sz0 (STflowE z0) tInst) : STExpAvgAt sz0 (STflowE z0) tInst
L659: theorem inst_expHier (h : STExpHier 3) : ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧ ContinuousOn (fun u => sz0.STExpDrift 0 (1 
L668: theorem inst_duhamelZ (h : STExpDuhamelZ 3) : zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2)) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] = ze
L681: theorem inst_duhamelQ (h : STExpDuhamelQ 3) : ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d
L700: theorem inst_A_value : sz0.lam 0 ^ 2 * ((sz0.W 0 : ℕ) : ℝ) ^ 3 = 8
L703: theorem st6_idx2_nonempty {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ) : Nonempty (STIdx2 sz s t n)
L707: theorem st6_idxSame_nonempty {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ) : Nonempty (STIdx2P sz STSigSame s t n)
L711: theorem st6_idxMixed_nonempty {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (n : ℕ) : Nonempty (STIdx2P sz STSigMixed s t n)
L716: theorem inst_normQA2 (T : (Fin 2 → Zd 3 4) → ℂ) : ‖zeroModeSet 3 4 (Finset.univ : Finset (Fin 2)) T‖ ≤ 4 * ‖T‖
L730: theorem inst_step6R_of_any (h : STStep6 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
```

### Narrative

- Stage 1b assembled `RBM3D/Induction/Step6Pins.lean` (734 lines) by a script (`assemble.py`) from the ten probe blocks of Targets 1, plus the lines Targets 1 allows: copyright, four imports (`Step5Pins`, `LWPins`, `ZeroModeCalc`, `QopAlgebra`), a new module docstring, probe `:39-44`, the scaffolding `namespace/open/variable` before `STRegSeq`, and the three `end` lines. No statement or proof text was edited.
- The ten blocks occur byte-equal in the file (ten `True` above). The 33 theorems (3 pure theorems plus the 30 instances of the ticket) are on the three standard axioms. The 47 definitions are the 6 non-`Prop` vocabulary defs, 40 `Prop` pins and `InstIng6Concl`.
- Compiled nonempty instances (CLAUDE.md §4 step 2): the 30 instance theorems are the instances. Every deterministic hypothesis (flow, `0 ≤ s < t ≤ lemT z`, regime, `(con_st_ind)` for every `𝔠_d > 0`) is discharged inside `inst_ing6_I..IV`, `inst_ing6_III` and `inst_ing6` at the data of section (a)(ii). What stays a hypothesis is a stochastic or other-gate premise: the pins `STStep6I..IV`, `STStep6`, `STExpDriftLo`, `STExpDriftDecay`, `STExpWardI/II`, `STExpIniI`, `STExpIntI..IV`, `STImproveExpAver`, `STExpHier`, `STExpDuhamelZ/Q` (the pins of this file), and `LWAvgLaw`, `STLK` at `tInst` in `inst_improveExpAver`. `inst_A_value`, `st6_idx*_nonempty`, `inst_normQA2` have no premise at all.
- As the ticket fixes, no instance in this file for `STExp2U_iff`, `STExp2_of_STExp2U`, `STExpLKLKHi`, `STDriftHi`, `STRegSeq`, `STExpEGtHiConcl` (S6-02).
- Registry: 20 owed + 20 structural lines appended (Targets 3). The pre-check reported no unregistered name, so `InstIng6Concl` needed no registration (like `InstIng5Concl`).
- The full `lake build` of the worktree does not import `Step6Pins` (the root import is added by the hub at merge); the module itself was built by `lake build RBM3D.Induction.Step6Pins`, and the pre-check file imports it together with `RBM3D`.
- No port from RBM1D/RBM2D in this ticket: the text is moved from the probe at 96c6b4c (RBM3D branch `t/T2191`), so no RBM1D/RBM2D diff-stat applies.
- The build emits only linter warnings (long lines are disabled in the file; upstream files warn on `show`).

## (c) Verified Mathlib names

None new: the file moves compiled probe text; the names it uses are those of the probe (compiled against this Mathlib, `lake build` above).

## (d) Open issues and paper-delta candidates

- No `T2204a` candidate: the preflight found no pin at odds with its paper line; D485-D489 (T2191a-e) are cited, not re-proposed.
- Observation: the docstrings of the moved pins keep probe cross-references ("§7 of this file", names that will live in `Step6Kit`), as Targets 1 requires; the structural pins other than `STRegSeq` carry no registry tag in their docstrings, their class is in `RBM3D/Test/Axioms.lean`.
- Observation: main moved from b3c37aa (branch base) to 98e6d5b during the run; the registry edit touches only the ends of `owedProps` and `structuralProps`, so a merge conflict is possible only if another ticket also appends there.
