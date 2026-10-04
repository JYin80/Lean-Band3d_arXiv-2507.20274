Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 16:23:16 UTC 2026

Notation: `n` = loop length (Lean `k`), `B = sz.Bctl n u = W^{-d}B_{u,0}`, `η = etaT`, `Ξ = STXiL`, `Ξ^{LK} = STXiLK`, `N = (WL)^d`, `ρ_u = (1-s)/(1-u)`, `LK = 𝓛-𝒦`, `u ∈ [s,t]`.

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | pieces of `STelklk` (`TreeRep.lean:75-92`) | `cutGlueL k l' a`: length `k+n-l'+1`, glued label at position `k` (not last); `cutGlueR`: length `l'-k+1`, glued label last | lengths sum to `n+2`, both `≥ 2`; long piece `n' ∈ [⌈n/2⌉+1, n]` | script: all pairs, `k=2..5` |
| 2 | case `n'=n` (short piece a 2-loop; covers `k∈{2,3}` and `k≥4`) | `max|LK^{(n)}|·W^dΣ_b|LK^{(2)}| ≤ B^nΞ^{LK}_n·C B^{1/6}η⁻¹` | pin: `B^n η⁻¹ B^{1/6} Ξ^{LK}_n` | 0 (exact) |
| 3 | case `⌈n/2⌉+1 ≤ n' ≤ n-1` (`n ≥ 4`) | `W^d·B^{n+2-n'}Ξ^{LK}_{n+2-n'}·[(W^dη)⁻¹(B^{n'_1-1}Ξ B^{n'_2-1}Ξ)^{1/2} + (W^dη)⁻¹B^{n'-2}]` | `B` exponent `(n+2-n')+(n'-2)=n`, one `η⁻¹`; `𝒦` term `≤ Ξ^{LK}_{n+2-n'}≤ Ξ^{LK}(ΞΞ)^{1/2}` (`Ξ ≥ 1`) | 0 |
| 4 | contraction index `k'=⌈n'/2⌉=(n'+1)/2` of `stContract_holds` conj. 1 | `(2k'-1, 2n'-2k'-1) = STn12 n'` as a multiset (`(n'-1,n'-1)` even, `(n',n'-2)` odd; `B`-exp `(n'_1+n'_2-2)/2 = n'-2`) | `1 ≤ k'`, `k'+1 ≤ n'`, i.e. `n' ≥ 3`; here `n' ≥ ⌈n/2⌉+1 ≥ 3` | `n'-3 ≥ 0` |
| 5 | pin range `Icc ((n+1)/2+1) (n-1)` | empty for `n=2,3`; `n'` ↔ the long piece; nat. subtraction safe | `n+2-n' ≥ 3` | — |
| 6 | `(eq:sumtwoloop)` exponent | `ρ_u^{Cd}B^{1/5} ≤ B^{1/5-𝔠_dC_d} ≤ B^{1/6}` | `𝔠_dC_d ≤ 1/30` (`1/5-1/6=1/30`), `B ≤ 1` | `𝔠_d=min(1/100,1/(30C_d))`: `𝔠_dC_d=1/30` for `C_d ≥ 10/3` (`C_d=4` in (ii)), slack 0 |
| 7 | `(con_st_ind)` at `u` from `t` | `Bparam(u,0)` increasing in `u` ⇒ `B(u) ≤ B(t)`; `(1-t)/(1-s) ≤ (1-u)/(1-s)` ⇒ `B(u)^{𝔠_d} ≤ (1-u)/(1-s)`, `B(u)<1`, `ρ_u ≤ B(u)^{-𝔠_d}` | `u ≤ t < 1`, `𝔠_d>0` | `stSumTwoLoop` (`KDecay.lean:1262`) needs `(1-t)/(1-s)<1` for the pair `(s,u)`: false at `u=s` ⇒ private pointwise copy of its proof (hypothesis `B(u)^{𝔠_d} ≤ (1-u)/(1-s)`) |
| 8 | first `≺` of `(eq:sumtwoloop)` | `STGdecayW` at `D`: `W^d·STWB·e^{-(r/ℓ)^{1/2}} = tailT d L g u r`, `r=zdistInf` (`STWB = W^{-d}Bparam`, `Defs.lean:69`; `BparamR_natCast`, `Tail.lean:57`); `Σ_x tailT ≤ KDecay_tailC d/(1-u)` (`KDecay_sum_tailT_le`, `KDecay.lean:1241`); `(1-u)⁻¹ ≤ η⁻¹` | `KDecay_tailC 3 = 4.03e8` (value in (ii)) | constant only |
| 9 | `W^{-D}` term | `W^dL^dW^{-D} = N W^{-D} ≤ N^{1-𝔠D}` (`Bandwidth 𝔠`, `W ≥ N^𝔠`) vs `B^{1/6}η⁻¹ ≥ B^{1/6} ≥ N^{-1/6}` (`B ≥ (WL)^{-d}`, `η ≤ 1`) | `1-𝔠D ≤ -1/6`, i.e. `D ≥ 7/(6𝔠)` | take `D = 2/𝔠`: exponent `-1` vs `-1/6`, slack `5/6` |
| 10 | `≺` losses | constants `≤ n²` cut pairs, `2`: `≤ N^{τ/2}`; 2-loop input used at `τ/2`: `N^{τ/2}N^{τ/2}=N^τ` | eventually in `n` | any `τ>0` |
| 11 | inputs | `STGdecayW` (`STStep2Concl.2.2`, uniform in `u`, with `((1-s)/(1-u))^{Cd}`, DECISIONS §29, §39) is the only `ω`-dependent input; `(wardineq_K)` (deterministic left side) from `stKward_timeIcc` (`KDecay.lean:1081`, flow facts as `SEforLn1.lean:702-725`) | `STKbound, STLK, STLocalEntryU, STAvgU, STKward` not used by (3),(4); `STKward`'s left side does not depend on `ω` | the bad sets to unite: the `STGdecayW` one and the `ω`-independent Ward ones |
| 12 | rotations | `L`-piece (`cutGlueL`): glued label at position `k <` length ⇒ rotate by `k` (`SEforLn1.lean:109,115`: `STLI`, `STKI` rotation) before `stContract_holds` / `stKward_timeIcc`; `cutGlueR` last. 2-loops: `STGdecayW` depends on `zdistInf(a_0-a_1)`, needs `zdistInf(-x)=zdistInf x` (private at `Green/Pins.lean:501`: re-prove) | trace cyclicity, `KLK_rotate` (`|E|<2`, `L ≥ 3`) | script: rotation error 1.5e-20 (`n=3,4,5`) |
| 13 | `S` sums | `Σ_a S_ab = Σ_b S_ab = 1`, `S ≥ 0` real, `S ≤ 1` (`Block.lean:38,118`) | the `S`-sum is taken on the piece that is NOT the max factor | `L ≥ 3` |
| 14 | part (4) label map | `STeeLoop` labels `a.drop(c-1)++a.take(c-1)` (`n` labels) `++[b']++…++[b]`: `b'` at 0-based index `n = j.val`, `b` last ⇒ exactly `List.ofFn (Function.update a₀ j y) ++ [x]`, `x=b`, `y=b'`; `σ'` has length `2n+2`; no rotation | `m'=2n+2` | — |
| 15 | part (4) contraction (`stContract_holds` conj. 2) | `m'=2n+2`, `k=n`, `j.val+1=n+1`, `l=n+2`, `p=q`: lengths `2k-1=2n-1`, `2m'-2l-1=2n-1`, `2(l-k)q=4q` | `4 ≤ m'`, `k<j+1<l`, `l+1 = n+3 ≤ 2n+2` | `n-1 ≥ 1` |
| 16 | `𝒜 b = {b' : zdistD(b-b') ≤ 1}` | `S_{bb'}=0` off `𝒜 b`, `S ≤ 1`; `#𝒜 ≤ 2d+1` (`card_nbhd`, `Neighbours.lean:158`, plus `b`) | `C = 2d+1 = 7` | script max `#𝒜 = 7` |
| 17 | part (4) exponent | `W^d(W^dη)⁻¹ = η⁻¹`; `maxL_{2n-1} ≤ B^{2n-2}Ξ_{2n-1}`, `maxL_{4q}^{1/(2q)} ≤ B^{(4q-1)/(2q)}Ξ_{4q}^{1/(2q)}`; total `B^{2n-2+2-1/(2q)}`, constant `n(2d+1)` | pin `B^{2n-1/(2q)}η⁻¹Ξ_{2n-1}Ξ_{4q}^{1/(2q)}` | 0 (all `q ≥ 1`); no stochastic input (needs only `|E|<2`, `0 ≤ u < 1`, `L ≥ 3`) |
| 18 | assembly | `STIngR` gives `C_d>0` before `𝔠_d`; `𝔠_d = min(1/100,1/(30C_d))` (`stSumTwoLoop_exists`, `KDecay.lean:1339`); parts (1),(2) (`SEforLn1.lean:466,702`) take `hflow,hs,ht,hAvg=(STStep2Concl).2.1` and `hκ,hst`, all supplied by `STIngR` | `0<𝔠_d ≤ 1/100`, `𝔠_dC_d ≤ 1/30` | no missing hypothesis |

### (ii) One concrete nondegenerate instance
(A) Pins (3), (4) at `d=3, L=5, W=1, g=1/2, E=0, u=1/2` (`W^d=1`: checks the inequalities, not the `≺` asymptotics), sampled `H`; `K^{(n)}` by the tree sum over `TSP(n)` (`Loop/Partition.lean`, 1/3/11 trees at `n=3,4,5`); `maxL_m` exact; `maxLK_2` exact, `maxLK_{3,4,5}` sampled lower bounds (so the RHS is smaller: conservative); `STelklk`, `STee` implemented from `Step34Pins.lean:133,152-163` verbatim; LHS = max over sampled `(σ,a)` (all `2^k` signs). The ratio `1.175` in line 5 is the constant `C` of `(eq:sumtwoloop)` at `W=1`, covered by `C=KDecay_tailC 3`.
Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2139; python3 check.py`
```
d=3 L=5 W=1 g=0.5 E=0.0 u=0.5: V=125, eta_u=0.5, B=W^-d B_(u,0)=1.349333, max_b #A(b)=7 (<=2d+1=7), max SB=0.4000
max |K - K∘rot|, |L - L∘rot| over 30 random loops (n=3,4,5): 1.52e-20  (K^(5) via TSP(5): 11 trees)
max_{sigma,a}|L^(m)| m=1..8 (exact): {1: 1.6537, 2: 2.7346, 3: 4.5221, 4: 7.478, 5: 12.366, 6: 20.4491, 7: 33.8159, 8: 55.92}
max|(L-K)^(m)|: m=2 exact; m=3,4,5 SAMPLED lower bounds: {2: 2.048772, 3: 4.019873, 4: 6.273047, 5: 11.434652} 
max_(sigma,a1) W^d sum_x |LK^(2)| = 2.4713 ; B^(1/6)/eta = 2.1024 ; ratio first/second = 1.175

== Part (3): |E^{(L-K)x(L-K),(k)}| <= B^k/eta (sum_{n'=ceil(k/2)+1}^{k-1} XiLK_{k+2-n'} (XiL_{n'1} XiL_{n'2})^(1/2) + B^(1/6) XiLK_k) ==
k=2 #samples=48 max|LHS|=9.4953e-01 | RHS=8.1352e+00 (sum-part 0.000, B^(1/6)XiLK_k=2.234; (n',n'1,n'2)=[]) | LHS/RHS=0.1167 
   1 cut pairs; lenL+lenR=k+2 for all: True; long-piece length n' range [2] within [ceil(k/2)+1,k]: True
k=3 #samples=64 max|LHS|=2.2792e+00 | RHS=1.3616e+01 (sum-part 0.000, B^(1/6)XiLK_k=2.771; (n',n'1,n'2)=[]) | LHS/RHS=0.1674 
   3 cut pairs; lenL+lenR=k+2 for all: True; long-piece length n' range [3] within [ceil(k/2)+1,k]: True
k=4 #samples=48 max|LHS|=5.1902e+00 | RHS=7.3300e+01 (sum-part 8.016, B^(1/6)XiLK_k=3.040; (n',n'1,n'2)=[(3, 1, 3)]) | LHS/RHS=0.0708 
   6 cut pairs; lenL+lenR=k+2 for all: True; long-piece length n' range [3, 4] within [ceil(k/2)+1,k]: True
k=5 #samples=96 max|LHS|=2.0705e+01 | RHS=1.1560e+02 (sum-part 9.184, B^(1/6)XiLK_k=3.738; (n',n'1,n'2)=[(4, 3, 3)]) | LHS/RHS=0.1791 
   10 cut pairs; lenL+lenR=k+2 for all: True; long-piece length n' range [4, 5] within [ceil(k/2)+1,k]: True

== contraction (yi2oslxj2) at index ceil(n'/2) gives STn12(n') ==
n'=3: k'=2 lengths (3,1) vs STn12=(1, 3): same multiset True; B-exp (n'1+n'2-2)/2=1.0=n'-2=1
n'=4: k'=2 lengths (3,3) vs STn12=(3, 3): same multiset True; B-exp (n'1+n'2-2)/2=2.0=n'-2=2
n'=5: k'=3 lengths (5,3) vs STn12=(3, 5): same multiset True; B-exp (n'1+n'2-2)/2=3.0=n'-2=3
n'=6: k'=3 lengths (5,5) vs STn12=(5, 5): same multiset True; B-exp (n'1+n'2-2)/2=4.0=n'-2=4

== Part (4), q=1: |(E⊗E)^{M,(k)}| <= B^(2k-1/2)/eta XiL_{2k-1} XiL_4^(1/2) ==
k=2 q=1 loop length 2k+2=6 #samples=240 max|LHS|=1.7470e+01 | det. bound k(2d+1) eta^-1 maxL_(2k-1) maxL_(4q)^(1/2q)=3.4625e+02; sampled sum_{b'in A(b)} |.|-form max=5.1505e+01 <= det: True | RHS=3.9984e+01 | LHS/RHS=0.4369
k=3 q=1 loop length 2k+2=8 #samples=480 max|LHS|=5.8402e+01 | det. bound k(2d+1) eta^-1 maxL_(2k-1) maxL_(4q)^(1/2q)=1.4203e+03; sampled sum_{b'in A(b)} |.|-form max=1.7825e+02 <= det: True | RHS=9.8851e+01 | LHS/RHS=0.5908
done
```
(B) Lean-level data (merged `sz0`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `z0`, `s≡0`, `t≡1/16`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `d=3`), `C_d=4`, `𝔠_d=1/120`: `(con_st_ind)` at every `u ∈ [s,t]`, the deterministic `(eq:sumtwoloop)` inequality, the `W^{-D}` absorption (`D=8`), `B ≥ 1/N`, and, as the external-hypothesis limit (TEAM §8 lesson 14), the profile of `K^{(2)}` (the deterministic part of `STGdecayW`) against `B_{u,r}e^{-√(r/ℓ)}` as `L` grows. `STGdecayW` itself stays a hypothesis of the compiled instances; `sz0_con` (`Step34Pins.lean:944`) supplies `(con_st_ind)` for every `𝔠_d>0`.
Command: `cd .../scratchpad/T2139; python3 inst.py`
```
C_d=4.0, c_d=min(1/100,1/(30 C_d))=0.008333, c_d*C_d=0.033333 (<=1/30), KDecay_tailC(3)=4.031086e+08

n L W N | u | Bctl(u) | Bctl(u)^c_d <= (1-u)/(1-s) | rho^Cd B^(1/5) sum_a tailT / (B^(1/6)/eta_u) | N W^-8 <= B^(1/6) | Bctl(u)<=Bctl(t)
0 4 32 2097152 | u=0.0625 | 3.305e-05 | True (B^c=0.9176 vs 0.9375) | 8.073e+00 (<= C_inf(3)=4.03e+08: True) | True | True
1 8 1024 549755813888 | u=0.0625 | 9.954e-10 | True (B^c=0.8414 vs 0.9375) | 1.767e+01 (<= C_inf(3)=4.03e+08: True) | True | True
2 12 7776 812479653347328 | u=0.0625 | 2.270e-12 | True (B^c=0.7998 vs 0.9375) | 2.542e+01 (<= C_inf(3)=4.03e+08: True) | True | True
10 44 5153632 11659991713824860234842112 | u=0.0625 | 7.793e-21 | True (B^c=0.6799 vs 0.9375) | 4.576e+01 (<= C_inf(3)=4.03e+08: True) | True | True
for u in {s,(s+t)/2,t} (assert) the con, sumtwoloop, absorption, monotonicity and B>=1/N (N=(WL)^d) checks hold; Bandwidth c=1/6: N^(1/6)<=W so N W^-D <= N^(1-D/6), D>=7 closes against B^(1/6)>=N^(-1/6)

limit check of the decay profile of K^(2) (the deterministic part of STGdecayW) at E=0, g=1/2, W=1, d=3:
u=0.5 L=5: max_(xi,r) |Theta(r)|/(B_(u,r)exp(-sqrt(r/ell))) = 0.949
u=0.5 L=17: max_(xi,r) |Theta(r)|/(B_(u,r)exp(-sqrt(r/ell))) = 0.961
u=0.99 L=5: max_(xi,r) |Theta(r)|/(B_(u,r)exp(-sqrt(r/ell))) = 0.764
u=0.99 L=17: max_(xi,r) |Theta(r)|/(B_(u,r)exp(-sqrt(r/ell))) = 0.592
```

## Verdicts
* Target 1 `stSEforLn_part3`: PASS. Exponents close with slack 0 (rows 2, 3, 6), `STn12` matches the contraction index (row 4); script `LHS/RHS = 0.12, 0.17, 0.07, 0.18` for `k=2..5`. Needs a pointwise-in-`u` copy of `stSumTwoLoop` (row 7: the pair `(s,u)` has ratio `1` at `u=s`), the rotation copies (row 12) and `zdistInf(-x)=zdistInf x` (row 12).
* Target 2 `stSEforLn_part4`: PASS. Label map exact, no rotation (row 14); lengths and exponent close with slack 0 (rows 15, 17); script `LHS/RHS = 0.44, 0.59` for `k=2,3`, `q=1`.
* Target 3 `stSEforLn_holds`: PASS. `𝔠_d` from `stSumTwoLoop_exists`; parts (1), (2) need nothing beyond `STIngR` (row 18); no stop condition of the ticket triggers.

## (b) Script output (stage 1b, `prover-hard`, Sonnet 5.5; first command of the stage at Sun Oct  4 16:24:42 UTC 2026, `date -u`)
Branch `t/T2139`, commit `8ee0941`, files `RBM3D/Induction/SEforLn2.lean` (new), `RBM3D/Test/Axioms.lean` (registry line). All commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2139`.
```
$ date -u; lake build RBM3D.Induction.SEforLn2 2>&1 | grep -E "Built|Build completed|error|SEforLn2"   (fresh build of the committed content)
Sun Oct  4 16:52:37 UTC 2026
✔ [3770/3770] Built RBM3D.Induction.SEforLn2 (7.2s)
Build completed successfully (3770 jobs).
$ date -u; git log --oneline -1
Sun Oct  4 16:53:21 UTC 2026
8ee0941 T2139: S3-09 Induction/SEforLn2 (lem:SEforLn parts 3, 4; stSEforLn_holds)
$ lake env lean ax.lean   (#print axioms RBM.Gauss.Sizes.{stSEforLn_part3,stSEforLn_part4,stSEforLn_holds})
'RBM.Gauss.Sizes.stSEforLn_part3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stSEforLn_part4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stSEforLn_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom " RBM3D/Induction/SEforLn2.lean; echo exit=$?
exit=1
$ grep -nE "^(theorem|def|lemma|abbrev|instance) [A-Za-z_]" RBM3D/Induction/SEforLn2.lean   (every non-private declaration)
1007:theorem stSEforLn_part3 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 Cd 𝔠d : ℝ} {z 
1264:theorem stSEforLn_part4 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : S
1287:theorem stSEforLn_holds (d : ℕ) : STSEforLn d := by
$ wc -l RBM3D/Induction/SEforLn2.lean; grep -c "^private" RBM3D/Induction/SEforLn2.lean
    1401 RBM3D/Induction/SEforLn2.lean
56
$ git grep -nE "stSEforLn_part3|stSEforLn_part4|stSEforLn_holds|SEforLn2Inst|SEforLn2_" main -- 'RBM3D/*.lean' RBM3D.lean; echo exit=$?   (name clash; main = c8e4f17)
exit=1
$ git diff --stat main...t/T2139
 RBM3D/Induction/SEforLn2.lean | 1401 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
 2 files changed, 1401 insertions(+), 1 deletion(-)
$ git diff 7f82dd6 t/T2139 -- RBM3D/Test/Axioms.lean | grep -E "^[-+]"   (registry edit; owedProps)
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STSEforLn, -- `lem:SEforLn` (DECISIONS §25)
$ git status --short
(end)
$ python3 - <<EOF ... EOF   (inline script: target statements, verbatim from the file, up to ":= by")
-- SEforLn2.lean:1007-1018
theorem stSEforLn_part3 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 Cd 𝔠d : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hCd : 0 < Cd) (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hcon : STConStInd sz 𝔠d s t) (hG : STGdecayW sz (STflowE z) s t Cd) (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklk sz n (STflowE z n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (STflowE z n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLK sz n (STflowE z n) (p.1 : ℝ) (k + 2 - n') ω *
              (STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz n (STflowE z n) (p.1 : ℝ) k ω)) := by
-- SEforLn2.lean:1264-1273
theorem stSEforLn_part4 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n)) (k : ℕ) (hk : 2 ≤ k) :
    ∀ q : ℕ, 1 ≤ q →
      Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) ×
          (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STee sz n (STflowE z n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) /
            etaT (STflowE z n) (p.1 : ℝ) *
          (STXiL sz n (STflowE z n) (p.1 : ℝ) (2 * k - 1) ω *
            STXiL sz n (STflowE z n) (p.1 : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ))))) := by
-- SEforLn2.lean:1287-1287
theorem stSEforLn_holds (d : ℕ) : STSEforLn d := by

$ sed -n "$((a-1)),$((b-2))p" SEforLn2.lean | grep -v -E "^$|^/--"   (the compiled instances of section 11, docstrings dropped)
-- SEforLn2.lean:1328-1384
example (hG : STGdecayW sz0 (STflowE z0) sInst tInst 4) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STelklk sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 2 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((2 + 1) / 2 + 1) (2 - 1),
            STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) (2 + 2 - n') ω *
              (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 2 ω)) :=
  stSEforLn_part3 (by norm_num) sz0 (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (Cd := 4)
    (𝔠d := 1 / 120) (by norm_num) (by norm_num) (by norm_num) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht
    (sz0_con (1 / 120) (by norm_num)) hG 2 le_rfl
example (hG : STGdecayW sz0 (STflowE z0) sInst tInst 4) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 4 → Bool) × (Fin 4 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STelklk sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 4 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((4 + 1) / 2 + 1) (4 - 1),
            STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) (4 + 2 - n') ω *
              (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 4 ω)) :=
  stSEforLn_part3 (by norm_num) sz0 (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (Cd := 4)
    (𝔠d := 1 / 120) (by norm_num) (by norm_num) (by norm_num) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht
    (sz0_con (1 / 120) (by norm_num)) hG 4 (by norm_num)
example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) ×
        (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STee sz0 n (STflowE z0 n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ ((2 * ((2 : ℕ) : ℝ)) - 1 / (2 * ((1 : ℕ) : ℝ))) /
          etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (2 * 2 - 1) ω *
          STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (4 * 1) ω ^ (1 / (2 * ((1 : ℕ) : ℝ))))) :=
  stSEforLn_part4 sz0 flow_z0 sz0_hs0 sz0_ht 2 le_rfl 1 le_rfl
example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 4 → Bool) × (Fin 4 → Zd 3 (sz0.L n)) ×
        (Fin 4 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STee sz0 n (STflowE z0 n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ ((2 * ((4 : ℕ) : ℝ)) - 1 / (2 * ((2 : ℕ) : ℝ))) /
          etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (2 * 4 - 1) ω *
          STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (4 * 2) ω ^ (1 / (2 * ((2 : ℕ) : ℝ))))) :=
  stSEforLn_part4 sz0 flow_z0 sz0_hs0 sz0_ht 4 (by norm_num) 2 (by norm_num)
instance `Step34Inst.inst_SEforLn` at `(sz0, z0, 0, 1/16)`, `C_d = 4`. -/
example : STSEforLn 3 := stSEforLn_holds 3
example : InstIngConcl (fun sz E s t => STSEforLnConcl sz E s t) sz0 z0 sInst tInst 4 :=
  inst_SEforLn (stSEforLn_holds 3) 4 (by norm_num)
$ cat precheck.lean   (uncommitted temp file; registry pre-check, DECISIONS §20)
import RBM3D
import RBM3D.Induction.SEforLn2
#assert_rbm_axioms
$ lake env lean precheck.lean > precheck.out 2>&1; echo exit=$?
exit=0
axiom audit: 4368 theorems, 1512 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 74 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ grep -c STSEforLn precheck.out
0

$ full build with a temporary (uncommitted) root import of the new module
+import RBM3D.Induction.SEforLn2
lake build exit=0
info: RBM3D.lean:187:0: axiom audit: 4368 theorems, 1512 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 74 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3888 jobs).
$ git status --short   (root file restored)
(end)
```

### Narrative (facts from the files and the logs above)
1. Delivered: `stSEforLn_part3`, `stSEforLn_part4`, `stSEforLn_holds` (3 public theorems), 56 private helpers `SEforLn2_*`, instances in section 11. The conclusions of parts (3), (4) are the third and fourth conjuncts of `STSEforLnConcl` definitionally (two `rfl` examples at the end of the file).
2. Part (3), deterministic core `SEforLn2_det3` (every sample, `u in [0,1)`, `|E| < 2`): the pieces of a cut `(j, l')` are `cutGlueL` of length `j+k-l'+1` and `cutGlueR` of length `l'-j+1` (sum `k+2`); `SEforLn2_pair_left/right` (column/row sums of `S`) bound a pair by (max of one piece) x (sum over the glued label of the other). If a piece is a 2-loop it is summed (the other has length `k`), otherwise the longer piece `n'` in `[(k+1)/2+1, k-1]` is summed: contraction at index `n'/2` (floor), whose lengths are exactly `STn12 n'`, plus the Ward bound for `K` (`SEforLn2_sumLK`). `cutGlueL` pieces are rotated so the glued label is last (`SEforLn2_sumL`); hence `zdistInf(-x) = zdistInf x` (row 12 of (a)) is not needed.
3. Stochastic input of part (3): only `STGdecayW`, at `D_w = 2/c`; the `W^{-D}` term is absorbed by `N W^{-2/c} <= N^{-1} <= B` (`SEforLn2_WD`, `SEforLn2_Bctl_ge_inv`, `Bandwidth c` from `STFlow`). The Ward bound is the deterministic `stKward_timeIcc`, turned into an eventual bound by `SEforLn2_det_of_prec`. The `<=` of the `Prec`s is by inclusion of bad events (`SEforLn2_of_subset`), one source, loss `N^{tau/2}`.
4. `(con_st_ind)` at `u in [s,t]` (row 7 of (a)): `SEforLn2_conU` derives `B_u^{c_d} <= (1-u)/(1-s)`, `B_u <= 1` from the pair `(s,t)` with `STBctl_mono` (ScaleFacts.lean:74). The merged `stSumTwoLoop` (KDecay.lean:1262) needs `(1-t)/(1-s) < 1` for its pair, false for `(s,u)` at `u = s`, so `SEforLn2_sumTwo_pt` is a private pointwise copy of its proof.
5. Constants: `C_s = KDecay_tailC d + 1`, per pair `(C_s+2) delta`, at most `k^2` pairs, `delta = N^{tau/2}`, `k^2 (C_s+2) <= N^{tau/2}` eventually; `c_d = min (1/100) (1/(30 C_d))`, `c_d C_d <= 1/30`. Exponent slacks are those of (a) rows 2, 3, 6, 17 (all 0).
6. Part (4): `SEforLn2_eeLoop` shows `STeeLoop` is exactly `<ofFn s'', ofFn (update a0 <k,_> y) ++ [x]>` (no rotation, row 14); `SEforLn2_eeSum` applies the second inequality of `stContract_holds` with `m = 2k+2`, `l = k+2`, `p = q`, `A x = {y : |x-y|_D <= 1}` (`C = 2d+1`, `SEforLn2_nbhd_card` from `card_adj`); `|S| <= 1` and `S` vanishes off `A`; the sum over the `k` cut edges gives the factor `k`; no stochastic input (`StochDomAt.of_eventually_empty`).
7. Assembly: parts (1), (2) of `SEforLn1.lean` need `STAvgU` (`hStep2.2.1`) and flow facts; `STKbound`, `STKward`, `STLK s` and the regime `STAny` are not used by any of the four parts.
8. Registry: the line `RBM.Gauss.Sizes.STSEforLn` is deleted from `owedProps`; pre-check exit 0; the audit line reads "0 of 75 premises" before the edit and "0 of 74" after (tool log of this session).
9. Section (a) needed no correction. Deviations from its wording are choices of indices (floor instead of ceiling in the contraction index, same pair as a multiset) and the rotation above.
10. Ports: nothing from `../RBM1D` or `../RBM2D` (no diff-stat); copies of the private helpers of merged `SEforLn1.lean` (commit 7f82dd6, prefix `SEforLn1_` to `SEforLn2_`) and of the proof of `stSumTwoLoop` (`KDecay.lean:1262-1334`).

## (c) Verified Mathlib/core names newly used (`#check`, one line each; the other names are already used by merged files)
```
@Filter.eventually_all_finset : ∀ {α : Type u_1} {ι : Type u_2} (I : Finset ι) {l : Filter α} {p : ι → α → Prop}, [...
@Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s 
@Finset.sum_subset : ∀ {ι : Type u_1} {M : Type u_2} {s₁ s₂ : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, [...]
@Finset.card_insert_le : ∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s : Finset α), (insert a s).card ≤ s.card + 
@Finset.card_le_card : ∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.card ≤ t.card
@List.set_append_right : ∀ {α : Type u_1} {s t : List α} (i : ℕ) (x : α), s.length ≤ i → (s ++ t).set i x = s ++ t.set
@List.getElem_set : ∀ {α : Type u_1} {l : List α} {i j : ℕ} {a : α} (h : j < (l.set i a).length), (l.set i a)[j] = if 
@List.getElem_ofFn : ∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h : i < (List.ofFn f).length), (List.ofFn f)[i]
@List.ext_getElem : ∀ {α : Type u_1} {l₁ l₂ : List α}, [...]
@Function.update_apply : ∀ {α : Sort u_1} [inst : DecidableEq α] {β : Sort u_2} (f : α → β) (a' : α) (b : β) (a : α), 
@Real.rpow_le_rpow_of_exponent_ge : ∀ {x y z : ℝ}, 0 < x → x ≤ 1 → z ≤ y → x ^ y ≤ x ^ z
@Real.sqrt_mul_self : ∀ {x : ℝ}, 0 ≤ x → √(x * x) = x
@inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflec
@le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀
Nat.card_Icc : ∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
@MeasureTheory.measure_univ : ∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureT
@mul_le_of_le_one_left : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b : α} [inst_2 : Preorder α] [Mu
@one_le_mul_of_one_le_of_one_le : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [Zero
```
Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
* **T2139a** (candidate): `(eq:sumtwoloop)` is used under `(con_st_ind)` at the running time `u in [s,t]`; from the pair `(s,t)` only the weak form `B_u^{c_d} <= (1-u)/(1-s)`, `B_u <= 1` holds at `u` (the strict `< 1` of `STConStInd` fails at `u = s`). The uniform-in-`u` statement of the pin needs exactly this form. A weak-form variant of `stSumTwoLoop` would remove the private copy `SEforLn2_sumTwo_pt` (dispatcher decision).
* **T2139b** (candidate): the absorption of the `W^{-D}` term uses `D = 2/c` and `W >= N^c` (`Sizes.Bandwidth`, `(Main_DEL_COND)`), not `(eq:WO)` (the ticket text names `(eq:WO)`; `WO` is the two-sided bound of `lam`; here it gives `0 <= lam` and the hypothesis `lam <= 1/d` of `stKward_timeIcc`, both via the flow).
* Observation: the merged `Step34Inst.inst_SEforLn` still takes `STSEforLn 3` as a hypothesis; the instance `inst_SEforLn (stSEforLn_holds 3) 4 _` compiles (section 11).
* Observation: `STGdecayW` stays a hypothesis of the part (3) examples (another gate, registered owed); its limit check is the profile table of (a)(ii)(B) (ratios 0.949, 0.961, 0.764, 0.592).
* Observation: `main` is at `c8e4f17` (T2138, T2140 merged after the base `7f82dd6` of this branch); the `Axioms.lean` hunk of `main` (`@@ -163,7 +163,24 @@`, from `git diff 7f82dd6 main`) does not overlap the deleted line (112). No merge was attempted here.
* No other Lean/paper statement difference beyond those already in the docstrings of `STSEforLnConcl` (constants absorbed by `<`, sum over `O(1)` terms, `(n'_1, n'_2) = STn12 n'`).
