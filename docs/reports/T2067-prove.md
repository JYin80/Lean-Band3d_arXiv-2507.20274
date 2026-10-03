Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 19:10:33 UTC 2026

### (i) Exponent table (pins, constants, slack).  Scripts: scratchpad `T2067/*.py`; paper cited `file:line`; no Lean written.
Registry class by DECISIONS §20/§24 (random premises and the pins: owed; data conditions: structural).  LW tickets = T2040 b.9.
| pin (probe line) | paper | class | proved by | content |
|---|---|---|---|---|
| LWweightExp (789) | 7_8:294-306 (Owx) | owed | LW-05 (+S1-19) | 4 terms: m ΣS_xα Ǧxx Ǧαα f; m³ΣS⁺_xα S_αβ Ǧαα Ǧββ f; −m ΣS_xα G_αx ∂_{h_αx}f; −m³ΣS⁺S G_βα ∂_{h_βα}f; `=` is equality of integrals |
| LWedgeExp (814) | 7_8:309-330 (Oe1x) | owed | LW-06 | 9 terms in 7_8:316-319 order (mδ; mΣSǦ𝒢; k₂×|m|²; k₃×m²; k₂×mǦ^-xx; k₃×mǦxx; k₁ m; k₄ m; −mΣS𝒢/(Gf)·G∂f); Lean `k₁+1` = paper `k₁` (T2040o) |
| LWggExp (847) | 7_8:334-349 (Oe2x) | owed | LW-07 | 8 terms of 7_8:337-339 |
| LWterm / LWtermB (949 / 964) | 3_5:385-404 / 393-397 | owed | LW-01 (+LW-15 merged, LWPhiB_psiAll) | `≺ η⁻¹Ψ(0)Ψ(|a-b|)²`; B class `Ψ=(W^-c₀B_{t,|a-b|∧K})^½` |
| LWtermExp (999) ⇐ LWtermExpS (1406) ∧ LWtermExpN (1421) | 3_5:406-415; regime 7_8:20 | owed | LW-01 (S, via LWMomentExp+LWReduceT); LW-16 (N, T2040k) | S: `lam²/L² < 1-t`, N: `1-t ≤ lam²/L²`; the probe defines S, N, ReduceT at **lines 1406-1457 (probe §7)**, not §5-6 |
| LWtermEXP (1020) | 6:83-88 | owed | LW-14 | index `lam²/L^d ≤ 1-t` (6:84), bound `(1-t)⁻¹Bctl^{5/2}` |
| LWMoment / LWMomentExp (1034 / 1050) | 7_8:72-77 / 78-83 | owed | LW-02 (LW-08,10-13) / LW-02,13 | `∃c` before `𝔠,sz,z`; index `lam²/L² < 1-t` (7_8:79) |
| LWAnpKey / LWAnpKeyGh / LWAnp (1084 / 1101 / 1121) | 7_8:960-985 / 1041-1077 / 933-939 | owed | LW-12 | nested `NGraph` (merged LWVocab:311), `∃c` |
| LWReduceB (1140) / LWReduceT (1437) | 7_8:20-91 (not numbered, T2040o) | owed | LW-01 | reductions to the moment bounds |
Premises: LWInteg (896), LWInit, LWLoop2, LWLoopExp, LWXi (1069), LWAvgLaw (1012): owed (random; ST chain); `STLocalEntry` is not in `Test/Axioms.lean` at HEAD 65ccfb3: owed, first used here; LWAssm/LWAssmExp (conjunctions with random parts): owed (§20 "unsure: owed"); LWWindow/LWClass/LWPsiRel/LWPsiAll (merged T2051, unregistered in `Axioms.lean`), `NGraph.{IsNested,NoGhost,GhostOK}`: structural.
Derivative convention of the three expansions: T2060a = D65 `dhSample` (Wirtinger in the real coordinates of `X_αw`, `∂h_αw=1`, `∂h_wα=0`; at `α=w` the real derivative); at `u=0` it is `0`, and every derivative term of the three pins carries a factor `S = t·svarF = 0` there.
| constant | value at the instance | constraint | slack |
|---|---|---|---|
| d, κ=ε=𝔡, 𝔠 | 3, 1/10, 1/6 | `3≤d`; `Admissible`: `W ≥ N^𝔠`, `W^(-d/2+𝔡) ≤ lam ≤ 𝔡⁻¹` | `W ≥ N^(1/6)=(WL)^½ ⟺ W ≥ L`: 32 vs 4 at n=0; `W^-1.4 ≤ lam=W^-1.2 ≤ 10` |
| ε₀, Ψ, Φ | 1/20, `W⁻¹` | `0<ε₀ ≤ d/2` (else LWWindow impossible: vacuous), `W^-3/2 ≤ Ψ ≤ W^-ε₀` | 3/2−1/20; exponents 3/2 ≥ 1 ≥ 1/20 |
| C₁,C₂,C₃,Cc | 2,2,1,1 (B class: 2^d, d, (1+Λ²)^½) | `C₁,C₂>1`, `C₃>0` | — |
| c₀ (LWtermB) | at `t₀`: `c₀ ≥ 2.5941` (n=0), → 2.50; at `t=1/16`: `≥ 0.123` | `0<c₀≤d`, `W^-c₀ B_{t,0} ≤ W^-2ε₀` (LWClass_B, LWPsi:366) | to `d=3`: 0.406 (n=0), 0.50 in the limit (table below) |
| t, E | `t∈{0,1/16,t₀=lemT z_n}`, `E=lemE z_n` | `0 ≤ t ≤ lemT z_n < 1` (Semicircle:209), `|E|<2` (:229), `η_t=(1-t)Im m(E)>0` | `1-t₀ = 9e-6 … 6e-39` (n=0…200) |
| `∃c` (Moment, Anp*) | any | (eq:Psi) ⇒ `Φ(cr) ≍ Φ(r)` up to constants (monotone, `Φ(0)≤Cc(C)Φ(ℓ)`, `Φ(ℓ₁)≤C₁(ℓ₂/ℓ₁)^C₂Φ(ℓ₂)`): the place of `c` is immaterial | no `𝔠,W,L,lam` in a constant |
| `ℓ_n`, `p`, `ξ` | `ellT(L,lam,t)`, `2`, `ξ=(Nη_t)^-½` | `0≤ℓ≤(log W)^10·ellT`, `2∣p`, LWXi: `Σ_βξ²=(W^dη)⁻¹`, `ξ ≤ W⁻¹` | `(log W)^10 ≥ 1` for `W ≥ 32` (probe ℓT_window:1650); `ξ≤W⁻¹` checked (script) |

### (ii) One nondegenerate instance and the boundary checks (DECISIONS §29)
Data = merged `sz0`, `z0` (Induction/Defs.lean:413): `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^-6`, `z_n=1/2+iN^-4/5`.  `cd scratchpad/T2067; python3 inst2.py`:
```
n   L    W              lam       N          STFlow  |E|<2 z_t0(E)=sqrt(t0)z  1-t0      S@1/16 EXPidx@t0 N-reg@t0 window xi<=1/W  1-t0<1 eta_t0>0
0   4    32             0.0156    2.1e+6     True    True  True               9.05e-6   True    True      True     True   True     True    True
1   8    1024           0.000244  5.5e+11    True    True  True               4.19e-10  True    True      True     True   True     True    True
2   12   7776           2.14e-5   8.12e+14   True    True  True               1.22e-12  True    True      True     True   True     True    True
5   24   248832         3.35e-7   2.13e+20   True    True  True               5.64e-17  True    True      True     True   True     True    True
10  44   5153632        8.82e-9   1.17e+25   True    True  True               9.13e-21  True    True      True     True   True     True    True
50  204  11040808032    8.88e-13  1.14e+37   True    True  True               2.33e-30  True    True      True     True   True     True    True
200 804  10498572832032 2.37e-16  6.01e+47   True    True  True               6.18e-39  True    True      True     True   True     True    True
```
columns: STFlow = WO ∧ Admissible-bandwidth ∧ locDomain; `S@1/16` = `lam²/L² < 1-1/16`; `EXPidx@t0` = `lam²/L^d ≤ 1-t₀`; `N-reg@t0` = `1-t₀ ≤ lam²/L²`.  `z_t0(E)=√t0·z` is Lemma 2.8 (1_2:792); `window` = `W^-3/2 ≤ W^-1 ≤ W^-1/20`.  Regime `g>L` (`d=3,L=3,g=5`) and invertibility of `1-m²tS` (`S=B`, rows sum 1; `|E|` up to 1.999, `t` up to 0.999):
```
L=3 g=5 (g>L), d=3, 1/delta=10 >= g:
  t=0.0     S-regime 1-t>g^2/L^2: False  N-regime: True   EXP-index g^2/L^d<=1-t: True   ellT=3
  t=0.07407 S-regime 1-t>g^2/L^2: False  N-regime: True   EXP-index g^2/L^d<=1-t: True   ellT=3
  t=0.25    S-regime 1-t>g^2/L^2: False  N-regime: True   EXP-index g^2/L^d<=1-t: False  ellT=3
  t=0.99    S-regime 1-t>g^2/L^2: False  N-regime: True   EXP-index g^2/L^d<=1-t: False  ellT=3
min singular value of (1 - m^2 t B), E in {-1.999,0,1.999}, t in {0,.5,.9,.999}: 6.321e-02
```
B-class exponents `2ε₀ + ln B_{t,0}/ln W` (needed `c₀`), and `Bctl = W^-d B` at `t=1/16`:
```
n    min c0 at t0 (c0<=d=3)   min c0 at t=1/16   Bctl(1/16)<=W^-2   Bctl(1/16)^(1/2)<=W^-eps0
0       2.5941                  0.12302            True               True
1       2.5346                  0.10959            True               True
10      2.5062                  0.10418            True               True
200     2.5006                  0.10215            True               True
```
Random premises at the instance (limit computations): at `t=1/16`, `B_{t,0}→(15/16)⁻¹` so `Bctl ≤ 1.1·W^-3 ≤ W^-2` and `Bctl^½ ≈ W^-3/2 ≤ W^-1/20` (columns 3-4), i.e. LWInit/LWLoop2 with `Ψ=W^-1` are consistent with the local laws `STLocalEntry/STLK` at `t=1/16`; at `t₀`: `B_{t₀,0} ≈ W^2.4` (min c₀ → 2.50, table above).
Expansions, numerically, 3×3 Hermitian Gaussian `S=tB` (rows sum t), `z_t=E+(1-t)m`, `S⁺=S(1-m²S)⁻¹`; `f∈{1, G_01, G*_12 G_20}`, matrix-level derivative; 27 identities per row (1.2×10⁶ samples per row), `python3 exp_mc.py`:
```
E=0.5 t=0.0: 27 identities; max|mean diff|=0.00e+00; max (|mean|/se)=0.00; typical se=0.00e+00
E=0.5 t=0.4: 27 identities; max|mean diff|=1.75e-03; max (|mean|/se)=2.44; typical se=1.29e-04
E=1.5 t=0.7: 27 identities; max|mean diff|=2.78e-02; max (|mean|/se)=1.46; typical se=3.64e-03
E=-1.9 t=0.5: 27 identities; max|mean diff|=3.16e-02; max (|mean|/se)=1.53; typical se=5.23e-03
negative control (k1+1 and |m|^2->m^2 in the edge expansion), E=0.5 t=0.4: max(|mean|/se) = 355.4
```
Merged derivative vs the pin's matrix-level `dH` (`python3 dh_check.py`, keys 0<1<2, u=0.37):
```
max |dhSample - dH| over 3 test functions x 9 (alpha,w) = 1.75e-10
```
Probe objects against merged (`python3 bind.py probe.lean`, run in the main worktree):
```
probe decl == merged text (verbatim, not recopied): LWWindow@LWPsi.lean:47 LWClass@LWPsi.lean:52 LWPsiRel@LWPsi.lean:59 LWPsiAll@LWPsi.lean:66 nSolid@LWVocab.lean:355 ordN@LWVocab.lean:365 nngh@LWVocab.lean:361 noGhostPath@LWVocab.lean:358
merged name exists, text differs (clash -> LWPins_ prefix): lwG@LWStein.lean:474 lwS@LWStein.lean:998
merged only (no probe def): LWPhiB@LWPsi.lean:73 NGraph@LWVocab.lean:311 NEdge@LWVocab.lean:305 NV@LWVocab.lean:302
probe-only (to copy): dH resPoly lwGb lwGc lwGcb lwSp lwf lwdf oe1xRest LWS LWf LWInteg LWcut LWE LWInit LWLoop2 LWAssm LWLoopExp LWAssmExp LWAvgLaw LWXi LWweightExp LWedgeExp LWggExp LWterm LWtermB LWtermExp LWtermExpS LWtermExpN LWtermEXP LWMoment LWMomentExp LWAnpKey LWAnpKeyGh LWAnp LWReduceB LWReduceT
```
Boundary checks per pin group (1) time `0≤t<1`, `t≤lemT`; (2) regime `1-t ≤ g²/L²`, `g>L`; (3) L–W relation; (4) `∀n` vs `∀ᶠn`:
- LWweightExp/EdgeExp/GGExp (exact, stated `|E|<2`, `0≤t<1`, `3≤L`, any `g,W≥1`): (1) `t=0`: `G=M`, every `Ǧ=0`, every `S=Sp=0`: both sides equal (MC row t=0: diff 0); `t→1`: `Im z_t=(1-t)Im m>0`, `|m|=1`, `1-m²tS` invertible (`lwS_isUnit` needs `‖m‖²u<1`; min singular value 0.063 at t=0.999). (2),(3) no `g,L,W` relation used (identities; integrands bounded by `(Im z_t)⁻¹` powers, so the integrals exist). (4) no sequence: n/a.
- LWterm, LWtermB, LWMoment, LWReduceB (index: all `n`): (1) `t=0`: `LWE=0`, `f_xy=0` (Ǧ=0), true; `t=t₀`: `η=√t₀·Im z ≥ N^-4/5·√t₀ >0`, instance above. (2) no regime split. (3) `STFlow` carries `Bandwidth`; `lam≤𝔡⁻¹`; B-class `c₀≤d` table. (4) premises `∀n`: STFlow, `0≤t`, `t≤lemT`, LWPsiRel-antitone, `K≤L`; conclusions `Prec` (eventual): `∀n` is the stronger premise ⇒ pins not false, satisfiable (instance). ST2-03 needs the finite-modification lemma (§29).
- LWtermExp(S/N), LWReduceT, LWMomentExp: (1) as above, `ℓ∈[0,(log W)^10 ellT]`, `ℓ=0` is the paper's `min(r,0)=0` (`tailW = max(B_{t,0}, W^-D)`, constant in `r`), no Lean division artefact (`ellT≥1`). (2) S empty and N full when `g>L` (`1-t ≤ 1 < g²/L²`, `t≥0`: the DECISIONS §27 negative-time defect cannot occur); instance: S at `t=1/16`, N and EXP-index at `t₀` both nonempty (`g²/L^d ≤ 1-t₀ ≤ g²/L²`). (3),(4) as above (`ℓ` ranges `∀n`: satisfiable by `ℓ=ellT`).
- LWtermEXP: (2) paper index `1-t ≥ ĝ²/L^d` (6:84) = probe; with `g=5,L=3`: nonempty iff `t ≤ 2/27`; empty (vacuous, true) beyond. (1) `t≥0` ⇒ `1-t ≤ 1`. (3) `Bandwidth` from STFlow. (4) premises STLocalEntry/LWAvgLaw/STLmax/STLK/STDecay at the sequence, eventual `Prec`.
- LWAnpKey/Gh/Anp and LWInteg: no time/regime use beyond `η_t>0`; LWInteg: `t<1` and `|E|<2` ⇒ `‖G_t‖≤η_t⁻¹`, integrand bounded and measurable (finitely many coordinates): true; `p=0` trivially.

### Findings and verdicts
- F1 (ticket text): `LWtermExpS`, `LWtermExpN`, `LWReduceT` are definitions in probe §7 (1406-1457); the ticket names LWReduceT but cites §5-6, and does not list S/N (DECISIONS §24 does). Copy these three definitions (no §7 theorem).
- F2: merged `RBM.Graph.lwG` (LWStein:474) and `lwS` (:998) differ from the probe's `lwG`, `lwS` (fixed-size `Ω d L W`, arguments `E t`/`g t`): clash ⇒ prefix `LWPins_`; `lwSp = lwSplus` and `dH = dhSample`, `resPoly = lwPoly` (variable `(b,x,y)` ↔ `(y,x,b)` for `b=false`) agree as functions on Hermitian samples (script above), but on different probability spaces (`PF d L W g` vs `sz.seqP`).
- F3 (stop condition of target 1 not triggered): binding the expansions to `lwPoly/dhSample/lwS/lwSplus` over `Sizes d, n` (as `owx_integral`, LWStein:1239, needs `0<u`, `0<z.im`, `GaussIBP sz`) does not change what they assert: `Sizes` has no asymptotic field (Defs/Sizes.lean:138-145), so fixed `(L,W,g)` = a constant sequence; the `t=0` case is separate (all derivative terms carry `S=0`).  It changes the form (`∀ sz n`) ⇒ either rebind (recommended: LW-05 is then `owx_integral` + the `t=0` case) or keep the fixed-size text with `LWPins_` objects; say which in the report.  (Oe1x),(Oe2x) are not in T2060 (its (d).2).
- F4: `LWPhiB sz c₀ K t` (LWPsi:73) is the lambda of LWtermB; `LWWindow/Class/PsiRel/PsiAll` are text-identical to the probe: use them, do not recopy.
- F5 (probe §8, 63 declarations, script): 60 use no §7 skeleton theorem: 13 of them (`inst_owx_*`, `owxDefect_M0`, `S0 Sp0 G0 D0 hS0 hSp0 hzm0 hM0`) are the merged `LWInstOwx` (LWStein:1902-1983), 47 are new (`inst_LWterm`, `…Exp`, `…Moment(Exp)`, `…EXP`, `…AnpKey(Gh)`, `…Anp`, `…LWtermB`, `…LWtermExpS/N`, `…_endT`, `inst_ssl/edge/gg`, window/class data); 3 wait for LW-01: `inst_chain_LWterm:2007`, `inst_chain_LWtermExp:2016`, `inst_chain_Anp:2158`.
- Verdict target 1 (binding): PASS (with F2, F3).  Target 2 (verbatim copy of pins and premises): PASS (F1, F4).  Target 3 (registry): PASS (table in (i); `STLocalEntry`, LWWindow/Class/PsiRel/PsiAll are to be registered by this ticket).  Target 4 (instances): PASS (F5).  No pin is false at a boundary; no hypothesis set is empty (instance above, deterministic parts discharged; random premises are owed).

## (b) Script output — Sat Oct  3 19:20:06 UTC 2026

### b.1 Builds (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2067, branch t/T2067, commit 6958dbd)
```
$ lake build RBM3D.Graph.LWPins
Build completed successfully (3345 jobs).
$ lake build   (whole library, runs #assert_rbm_axioms; LWPins is not yet imported by RBM3D.lean: hub adds the root import)
Build completed successfully (3782 jobs).
$ lake env lean precheck.lean   [import RBM3D; import RBM3D.Graph.LWPins; #assert_rbm_axioms]  (registry pre-check)
exit code 0
error lines: 0
axiom audit: 2192 theorems, 930 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 64 (borrowed 2, owed 50, structural 12).
registry: 5 borrowed + 68 owed + 33 structural; 42 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
non-vacuity certificates: 4 of 73 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
```

### b.2 Files touched, hygiene
```
$ git diff --stat main...t/T2067
 RBM3D/Graph/LWPins.lean | 972 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |  36 +-
 2 files changed, 1007 insertions(+), 1 deletion(-)
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/LWPins.lean
0
$ git log -1 --format="%h %an <%ae>"
6958dbd Jun Yin <321276894+JYin80@users.noreply.github.com>
```

### b.3 #print axioms (all 84 new declarations: names.py -> axioms.lean)
```
standard three axioms: 83; other lines:
'RBM.Gauss.LWInst.figAux_ghostOK' depends on axioms: [propext]
'RBM.Graph.LWweightExp' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWedgeExp' : [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWggExp' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWterm' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWtermB' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWtermExp' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWtermEXP' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWMoment' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWMomentExp' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWAnpKey' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWAnpKeyGh' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWAnp' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWReduceB' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWtermExpS' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWtermExpN' : [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWReduceT' : [propext, Classical.choice, Quot.sound]
```

### b.4 Target statements (pins): file:line of each, extracted by script (full text: RBM3D/Graph/LWPins.lean)
```
 106-116  def LWweightExp (d : ℕ) : Prop :=
          ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
 131-160  def LWedgeExp (d : ℕ) : Prop :=
          ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
 164-181  def LWggExp (d : ℕ) : Prop :=
          ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
 240-249  def LWterm (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 255-270  def LWtermB (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 290-300  def LWtermExp (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 447-458  def LWtermExpS (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 462-473  def LWtermExpN (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 311-320  def LWtermEXP (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 325-336  def LWMoment (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 341-354  def LWMomentExp (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 372-385  def LWAnpKey (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 389-403  def LWAnpKeyGh (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 409-422  def LWAnp (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 428-441  def LWReduceB (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
 478-496  def LWReduceT (d : ℕ) : Prop :=
          3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
```

### b.5 Copy check: each probe declaration (eeda441) occurs verbatim in LWPins.lean after the renames
```
renames (probe -> LWPins.lean), RBM.Graph objects only: dH resPoly lwG lwGb lwGc lwGcb lwS lwSp lwf lwdf oe1xRest -> LWPins_<name>
omitted (merged, text identical): LWWindow LWClass LWPsiRel LWPsiAll   |  omitted (section 7 theorems, LW-01): none copied
decl           probe:l  new:l    probe text (renamed per list) occurs verbatim in LWPins.lean
not verbatim: 0
39 declarations verbatim
$ python3 bind.py probe.lean   (in the main worktree)
probe decl == merged text (verbatim, not recopied): LWWindow@LWPsi.lean:47 LWClass@LWPsi.lean:52 LWPsiRel@LWPsi.lean:59 LWPsiAll@LWPsi.lean:66 nSolid@LWVocab.lean:355 ordN@LWVocab.lean:365 nngh@LWVocab.lean:361 noGhostPath@LWVocab.lean:358
merged name exists, text differs (clash -> LWPins_ prefix): lwG@LWStein.lean:474 lwS@LWStein.lean:998
merged only (no probe def): LWPhiB@LWPsi.lean:73 NGraph@LWVocab.lean:311 NEdge@LWVocab.lean:305 NV@LWVocab.lean:302
probe-only (to copy): dH resPoly lwGb lwGc lwGcb lwSp lwf lwdf oe1xRest LWS LWf LWInteg LWcut LWE LWInit LWLoop2 LWAssm LWLoopExp LWAssmExp LWAvgLaw LWXi LWweightExp LWedgeExp LWggExp LWterm LWtermB LWtermExp LWtermExpS LWtermExpN LWtermEXP LWMoment LWMomentExp LWAnpKey LWAnpKeyGh LWAnp LWReduceB LWReduceT
```

### b.6 Name-clash grep: every new declaration name against main (git grep on main, LWPins.lean excluded)
```
names checked: 84 ; bare-name hits in main: 0
import RBM3D + import RBM3D.Graph.LWPins in one file (no duplicate-declaration error): exit code of the pre-check above
```

### b.7 Compiled instances (probe section 8, lines 1566-2168): ported / not ported, by script
```
probe section-8 declarations: 63 ; in LWPins.lean: 45
not ported:
  probe:2007 inst_chain_LWterm -- section-7 skeleton (waits for LW-01)
  probe:2016 inst_chain_LWtermExp -- section-7 skeleton (waits for LW-01)
  probe:2038 S0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2041 Sp0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2044 G0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2047 D0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2049 hS0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2053 hSp0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2057 hzm0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2059 hM0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2064 inst_owx_smallest -- merged LWInstOwx (LWStein:1902-1983)
  probe:2071 inst_owx_second -- merged LWInstOwx (LWStein:1902-1983)
  probe:2081 inst_owx_smallest_E -- merged LWInstOwx (LWStein:1902-1983)
  probe:2096 owxDefect_M0 -- merged LWInstOwx (LWStein:1902-1983)
  probe:2102 inst_owx_smallest_E_unit -- merged LWInstOwx (LWStein:1902-1983)
  probe:2116 inst_figGraph_val -- statement about merged `figGraph_val`/`D0` (LWVocab, LWInstOwx), no definition of this file
  probe:2119 inst_p2Graph_val_eq -- statement about merged `figGraph_val`/`D0` (LWVocab, LWInstOwx), no definition of this file
  probe:2158 inst_chain_Anp -- section-7 skeleton (waits for LW-01)
ported instance declarations (names):
inst_LWterm inst_LWtermExp inst_LWMoment inst_LWMomentExp inst_LWtermEXP inst_AnpKey inst_Anp inst_ssl inst_edge inst_gg 
inst_LWterm_endT inst_LWtermExp_endT inst_LWtermExpN inst_LWMoment_endT inst_AnpKey_endT inst_LWtermEXP_endT inst_LWtermB 
inst_LWtermExpS inst_AnpKeyGh inst_shift 
The three expansion instances (LWInstFixed, d=3, L=3, W=2, g=1, E=0, t=1/2; every deterministic hypothesis discharged by norm_num):
def inst_ssl (h : LWweightExp 3) (x : Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) P01 x

def inst_edge (h : LWedgeExp 3) (x : Idx 3 3 2) (y : Fin 2 → Idx 3 3 2) (y' : Fin 1 → Idx 3 3 2)
    (w : Fin 1 → Idx 3 3 2) (w' : Fin 1 → Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 1 1 1 1 x y y' w w' P01

def inst_gg (h : LWggExp 3) (x y y' : Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) x y y' P01

```

#### b.7 Repair (audit round 1, items 1-3) — Sat Oct  3 19:28:08 UTC 2026 (repairer model: claude-opus-5-5, commit 626f3a7 on t/T2067)
Added `inst_LWReduceB`, `inst_LWReduceT` (namespace `RBM.Gauss.LWInst`, explicit result types = the pins'
conclusions at the data). Hypotheses left: the pin, `hI : LWInit …`, `hL : LWLoop2 …` / `LWLoopExp …`, the
`Prec … LWf …` premise (and `D`, `hD : 0 < D` for `T`); index set of `T` nonempty for all `n` (`strict_all`).
```
$ lake build RBM3D.Graph.LWPins 2>&1 | grep -E "error|LWPins|Build" | tail -8
✔ [3345/3345] Built RBM3D.Graph.LWPins (5.9s)
Build completed successfully (3345 jobs).
$ lake env lean T2067/ax_repair.lean   [import RBM3D.Graph.LWPins; #print axioms of the two]
'RBM.Gauss.LWInst.inst_LWReduceB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWReduceT' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -rn "inst_LWReduce" RBM3D/   (main worktree)        -> no output, exit 1
$ grep -nE "^theorem inst_LWReduce|^  h le_rfl|hf$" RBM3D/Graph/LWPins.lean | awk -F: '$1>=970'
972:theorem inst_LWReduceB (h : LWReduceB 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
982:  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
983:    tInst tInst_range.1 tInst_range.2 (1 / 20) 2 2 1 (fun _ => 1) Ψ0 Φ0 (assm_of hI hL) hf
988:theorem inst_LWReduceT (h : LWReduceT 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
1003:  h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
1004:    flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD hf
$ git diff --stat HEAD~1 HEAD
 RBM3D/Graph/LWPins.lean | 36 ++++++++++++++++++++++++++++++++++++
```

### b.8 Narrative (Sat Oct  3 19:20:58 UTC 2026)
- File: `RBM3D/Graph/LWPins.lean` (new, imports LWVocab, LWPsi, LWStein and the probe's four imports, never `RBM3D`) and 35 inserted, 1 changed registry lines in `RBM3D/Test/Axioms.lean` (b.2). Branch `t/T2067`, one commit.
- Content: 3 expansions + 11 fixed-size objects (RBM.Graph), the premises/data/pins of section 6 and the three section-7 definitions `LWtermExpS`, `LWtermExpN`, `LWReduceT` (preflight F1; the section-7 theorems are not copied), instances of section 8. Every copied declaration is verbatim after the renames (b.5, 39 of 39; the `LWPins_lwG..lwSp` rows share one probe block).
- Binding (target 1). Used from the merged files without recopying: `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll` (LWPsi:47-66, text identical to the probe, b.5), `NGraph` with `IsNested/NoGhost/GhostOK/ordN/nngh/noGhostPath` (LWVocab), and `LWPhiB` (LWPsi:73): the `example` before `end RBM.Gauss.Sizes` proves by `rfl` that `LWPhiB sz c₀ K t` is the lambda that `LWtermB` writes inline (the pin text is kept verbatim).
- Binding the three expansions to `dhSample`/`lwPoly`/`lwS`/`lwSplus` was NOT done. Reason (files): the merged objects take `(sz, n, u, ω)` and live on `Sizes.seqP sz`; `owx_integral` (LWStein:1239) carries the premises `GaussIBP sz`, `0 < z.im`, `0 < u`, `hm0`, `hzm`, `hSp` and a polynomial in `Idx × Idx × Bool`; the probe pin is an unconditional statement over `PF d L W g` for all `L W g E t` with `|E| < 2`, `0 ≤ t < 1`, polynomials in `Bool × Idx × Idx`. Rebinding would add hypotheses and change the form, so the pins keep the probe's text with the objects prefixed `LWPins_` (the probe's `dH resPoly lwG lwGb lwGc lwGcb lwS lwSp lwf lwdf oe1xRest`; `lwG`, `lwS` clash with merged names, the others differ in arguments). Numerical agreement of `dhSample`, `lwPoly`, `lwSplus` with `LWPins_dH`, `LWPins_resPoly`, `LWPins_lwSp` was checked in (a) (`dh_check.py`: 1.75e-10); it is not a Lean theorem. No pin was changed, so the stop condition of target 1 was not triggered; the bridge is for LW-05/06/07 (d.1).
- Registry (target 3): the pre-check before the edit failed with 17 unregistered premises (LWAvgLaw, STLocalEntry, LWtermEXP, LWLoopExp, LWInit, LWMomentExp, LWLoop2, LWXi, LWAnpKeyGh, LWAnpKey, LWAnp, LWtermB, LWtermExpN, LWterm, LWtermExp, LWMoment, LWtermExpS); added to `owedProps`: the 16 pins, `LWInteg LWInit LWLoop2 LWLoopExp LWXi LWAvgLaw LWAssm LWAssmExp STLocalEntry`; to `structuralProps`: `LWWindow LWClass LWPsiRel LWPsiAll NGraph.IsNested NGraph.NoGhost NGraph.GhostOK`. After the edit the pre-check exits 0 (b.1).
- Instances (target 4, b.7): 45 declarations of probe section 8 ported (instances at `t ≡ 1/16` and `t = lemT z_n`, the B class, the three fixed-size expansion applications at `d=3, L=3, W=2, g=1, E=0, t=1/2`); not ported: 3 `inst_chain_*` (they apply section-7 skeleton theorems: wait for LW-01), 13 declarations that are the merged `LWInstOwx`, 2 statements about merged `figGraph_val`. What stays a hypothesis of an instance is a premise registered as owed (the pin itself, `LWInit`, `LWLoop2`, `LWLoopExp`, `LWXi`, `STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay`).
- Boundary checks of DECISIONS §29: in (a) (instance table, regime `g > L`, `1-m²tS` invertibility, Monte Carlo identities, B-class exponents); no pin was found false; this stage changed no statement, so (a) needed no (a′).

## (c) Verified Mathlib names (used in the ported instance proofs; verified by the build of b.1, none invented, none found absent)
- `Real.exp_one_lt_d9`, `Real.le_log_iff_exp_le`, `Real.one_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`, `Real.rpow_add`, `Real.rpow_mul`, `Real.sqrt_eq_rpow`, `Real.le_sqrt_of_sq_le`
- `one_le_pow₀`, `inv_anti₀`, `pow_le_pow_left₀`, `div_le_self`, `inv_le_comm₀`, `le_inv_comm₀`, `inv_le_one_of_one_le₀`, `one_le_div`, `Eventually.of_forall`, `MvPolynomial.X`

## (d) Open issues and paper-delta candidates
1. T2067a (candidate): the Lean expansion pins (`LWweightExp`, `LWedgeExp`, `LWggExp`) are fixed-size identities over `PF d L W g` with `LWPins_` objects and polynomials in `Bool × Idx × Idx`; the merged Stein layer (`owx_integral`, LWStein:1239) is on `Sizes.seqP` with `GaussIBP sz`, `0 < u`, `0 < z.im` and polynomials in `Idx × Idx × Bool`. LW-05 must prove the `t = 0` case separately and bridge the two spaces; (Oe1x), (Oe2x) are not in T2060 (its (d).2, as noted in (a) F3).
2. Cited as required by the ticket, numbered at this merge: T2040a, T2040e-h, T2040j-o (DECISIONS §24). No other Lean/paper difference was introduced by this ticket: the pins are the probe's.
3. Waiting for LW-01: `inst_chain_LWterm`, `inst_chain_LWtermExp`, `inst_chain_Anp` (b.7) and the skeleton theorems of probe section 7.
4. The ticket text cites section 5-6 for `LWReduceT`; it is in probe section 7 (a, F1). Copied with `LWtermExpS`, `LWtermExpN`.
