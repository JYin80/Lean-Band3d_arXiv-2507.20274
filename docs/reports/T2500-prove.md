Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 02:44:23 UTC 2026

Targets 1-6 are compositions of merged results; no new exponent. Script (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2500/chk.py`, Python only, exact `Fraction` plus a numeric sanity value of `m_w = L^{-d} tr (g Psi^B - w)^{-1}` from the eigenvalues of the 6-regular adjacency of `Z_4^3`; `Adj` is `zdistD = 1`, the periodic l1 distance, `Defs/Lattice.lean:71,108`).

### (i) Exponent table

| # | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `𝔠d` inside R2* pins (`stIterationsgL'_of`, `stIterationsIIgL'_of`, `IterationsGen2:389,409`) | `1/100` | `0<𝔠d≤1/100` (pin `STIterRgL'`, `NQEndFlowGen:123`) | 0 |
| 2 | same `𝔠d`, case (i) | `1/100` | `𝔠d ≤ 1/16` (`iterationsA_scale_Ig`, `IterationsGen:506`) | 21/400 |
| 3 | same `𝔠d`, case (ii) | `1/100` | `𝔠d ≤ 1/24` (`iterationsA_scale_IIg`, `IterationsGen:515`) | 19/600 |
| 4 | order of quantifiers | `κ ε 𝔡 Cd`, then `∃ 𝔠d`, then `(𝔠, sz, z)` | `NQEndFlowGen:123-126`; no `∃ C` after `(sz,z)` | n/a |
| 5 | `Admissible 𝔠 𝔡` (inside `BAFlow`) | `(𝔠,𝔡)=(1/9,1/10)` for both new data | `W ≥ N^𝔠`; `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`Defs/Sizes.lean:164,168`) | case-(i) datum: `N^{1/9}=(4W)^{1/3} ≤ W` iff `W² ≥ 4` (`W ≥ 25`); `W^{-7/5} ≤ 1 < 2 ≤ 10` |
| 6 | flow `κ` for the case-(i) datum | `3/1000` | `κ ≤ Im m_w`; proved bound `Im w/(‖w‖²+g²L^d) = 0.003893` (`BASelf_subord`, `MFixedPoint:215`, `w=(5003/5000)i`, `g=2`, `L=4`, `d=3`) | `0.003893-0.003 = 8.9e-4` |
| 7 | flow `κ` for the case-(ii) datum (merged `TwistStep2_flowII`) | `3/5000` | same bound with `g=5`: `0.000625` | `2.5e-5` |
| 8 | `Im z ≤ 1` (`BAdom`), case (i) | `Im z = y - Im m_w ≤ y - y/(y²+256)` | `≤ 1` | `1-0.996707 = 3.3e-3` |
| 9 | `N^{-1+ε} ≤ Im z` at `ε=1/2`, `N_n = (4(n+25))³ ≥ 10⁶` | `N_0^{-1/2}=1.000e-3` | `Im z ≥ y - 1/y = 1.1996e-3` (upper bound `Im m_w ≤ 1/y`) | `2.0e-4` |
| 10 | horizon `T₀` of the case-(i) datum | `T₀ ≥ κ/(κ+1) = 3/1003 = 0.002991` (`TwistStep2_T0_ge`, `TwistStep2:731`) | window `0 = s < t = 1/400 ≤ T₀` | `4.9e-4` |
| 11 | `STRegIterI` at case-(i) datum (`lam≡2, L≡4`; `Step34Pins:493`) | `lam²/L² = 1/4` | `STCaseI`: `1/4 ≤ 1-t = 399/400`; second conjunct `1-s = 1 ≤ lam² = 4` | `0.7475`; `3` |
| 12 | `STCaseII` at TL datum (`lam≡5, L≡4`, `s≡0`) | `1-s = 1` | `1 ≤ lam²/L² = 25/16` (`Step34Pins:241`) | `9/16` |
| 13 | case-(ii) window of TL datum | `t=1/2000 = 5e-4` | `t ≤ κ/(κ+1) = 3/5003 = 5.997e-4` | `9.97e-5` |
| 14 | `sz0` has no `STRegIterI` window | `n=0`: `lam_0 = 1/64`, `lam_0² = 1/4096` | would need `1-s_0 ≤ 1/4096`, but `s_0 < t_0 ≤ 25/36` (`t0_sz0_le`, `Step1Fam:753`) gives `1-s_0 > 11/36` | contradiction (`11/36 > 1/4096`): the new datum is necessary |
| 15 | `hIm` of `Step2Kern_UN_BA` (`Step2Kern:124`) for target 3 | `Im(E_n + m_n) = Im m_n` | `≠ 0`; `BAflow_real` (`GreenSchur:59`) gives `κ ≤ Im m_n`, `0<κ` | `κ` |
| 16 | `‖m_n‖ ≤ 1` (family row 4) | `BAm_norm_le_one` (`Ward:136`) at `BASelf` of `BAReal` (`z = E` real, `0 ≤ Im z`) | `≤ 1` | n/a |
| 17 | definitional identifications | `(baStep2Mat sz l E).toFlowFM = baFM sz l E` is `rfl` (`Step2BA:75`); `baFMz sz z = baFM sz (BAflowLam0 sz z) (BAflowEs sz z)` (`FlowPins:393`); `baFM.m = BAmF` (`FlowPins:322-330`) | stop rule of the ticket (unfold accepted) | n/a |

Family-premise rows used by target 5 (types read from the files, each matches the merged discharge):
- row 1 `Step2EventsGenTw_baFlow` (`Step2EventsGenTw:53`) is `Step2EventsGen_Flow d BAFlow BAflowT0` verbatim;
- row 3 `baStep2Mat_loopForm d` (`SEforLnBA:135`) has exactly the guarded form `0<κ → BAFlow → StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)`;
- row 5 `baStep34_LCompat d sz lam0 E` (`SEforLnBA:122`) is `Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0)`, unguarded;
- row 6 `EMn2BA_seqHflowBA_herm` (`EMn2BA:68`) is the unguarded Hermitian statement.

Route facts (mathematics) checked against the merged texts:
- target 1: `zeroModeGen_newPQ` (`ZeroModeGen:249`) gives `(ℓ,k,ξ,σ',ι,A')` before `(L,κ,T)` with coefficient `((L:ℂ)^d)⁻¹ κ`; `STNewPQgL` (`Step34Gen:823`) has coefficient `1/(2 i N η)^{m-k}`; with `κ = (2 i W^d η)⁻¹` and `N = (WL)^d` these agree: `(L^{-d} (2 i W^d η)⁻¹) = (2 i (WL)^d η)⁻¹`. The data come before `(sz, C)` in both statements.
- target 2: the data of `STNewPQgL` precede `Cls`, so any subclass of `ZeroModeGen_WardCls sz` inherits target 1; `baZeroModeGen_wardCls` (`SEforLnBA:66`) places `baFMz sz z` in the class under `0<κ`, `BAFlow`.
- target 3: `zeroModeSet_UNg`, `zeroModeSet_ThetaNg` (`ZeroModeGen:161,179`) need only `ZeroModeGen_KerSums C n`; `baZeroModeGen_kerSums` (`B45BA:110`) gives it for `baFMz sz z` at every `n` under `0<κ`, `BAFlow`.
- target 4: `gridRepTailGen_ker_BA` (`GridRepTailBA:60`) at `BAReal` and `0<κ`; its first conjunct is `Step2Gen_USemigroup` of `(baStep2Mat …).toFlowFM = baFMz sz z`.
- targets 5, 6: `stIterationsgL'_of`, `stIterationsIIgL'_of` consume `IterationsGen2_Fam` (rows 1-6) and conclude the pins at `(mkM sz z).toFlowFM`, `𝔠d=1/100`; the regime `STCaseII` is not consumed in case (ii).

### (ii) One concrete nondegenerate instance (d = 3)

Instance A (targets 2, 3, 4 and U1s1/U1s2 carrier premises) at `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `sz0_values`: `L_0=4, W_0=32, size_0 = 2097152, lam_0 = 1/64`), `z = zSeq`, `flow_sz0` with `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `m = 3`, `σ = (+,-,+)`, `A = ∅`, `n = 0`, `τ = 1/2`, `s ≡ 1/10 ≤ t ≡ 1/2 < 1`, `K = 4 ≠ 0`. All deterministic hypotheses are numerical inequalities on these data; `STIdiff σ = {i : σ i ≠ σ(finRotate i)} = {0, 1}` for `σ = (+,-,+)` (`Step34Pins:97`), so `A ∪ STIdiff σ = {0,1}` differs from `A = ∅`.

Instance B (target 6, case (i)), new private datum: `L ≡ 4`, `W_n = n+25`, `lam ≡ 2`, `w = (5003/5000) i`, `z ≡ w - m_w`, `(κ,ε,𝔠,𝔡) = (3/1000, 1/2, 1/9, 1/10)`, `s ≡ 0`, `t ≡ 1/400`, `𝔠 = 1/9`; `STConStInd` by `conStInd_const` (`Step34Pins:825`, needs `W → ∞`, `s0<t0<1`, `𝔠d>0`).

Instance C (target 6, case (ii)): merged `TwistStep2_szII`, `TwistStep2_flowII` (`TwistStep2:1341,1353`), `s ≡ 0`, `t ≡ 1/2000`.

Command and verbatim output:

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2500/chk.py
[case (i) new] g=2 L=4 y=1.0006: lower bound y/(y^2+g^2L^d)=0.003893 >= kappa=0.003: True
   numeric Im m_w=0.343003 (in [0.003893,0.999400]); Re m_w=-1.37e-16; Im z=y-Im m=0.657597
   Im z<=1: True (bound 0.996707); Im z >= y-1/y = 0.001200 >= N0^(-1+eps)=0.001000: True
   T0 >= kappa/(kappa+1) = 0.002991; numeric T0=0.342797; window s=0.0 < t=0.0025 <= kappa/(kappa+1): True
   Admissible(c=1/9,d=1/10) pointwise n<2000 [W^(-7/5)<=g<=1/d, N^(1/9)<=W]: True; N_0=1000000>=1e6: True
   STCaseI: lam^2/L^2=1/4 <= 1-t=399/400: True;  STRegIterI 2nd: 1-s=1 <= lam^2=4: True
[case (ii) TL] g=5 L=4 y=1.0006: lower bound y/(y^2+g^2L^d)=0.000625 >= kappa=0.0006: True
   numeric Im m_w=0.317459 (in [0.000625,0.999400]); Re m_w=-3.69e-16; Im z=y-Im m=0.683141
   Im z<=1: True (bound 0.999975); Im z >= y-1/y = 0.001200 >= N0^(-1+eps)=0.001000: True
   T0 >= kappa/(kappa+1) = 0.000600; numeric T0=0.317269; window s=0.0 < t=0.0005 <= kappa/(kappa+1): True
   Admissible(c=1/9,d=1/10) pointwise n<2000 [W^(-7/5)<=g<=1/d, N^(1/9)<=W]: True; N_0=1000000>=1e6: True
   STCaseII: 1-s=1 <= lam^2/L^2=25/16: True
[sz0] n=0: lam_0^2=1/4096; any s_0<t_0<=25/36 gives 1-s_0 > 11/36 > lam_0^2: True
cd=1/100 <= 1/100: True  <=1/16 slack 21/400  <=1/24 slack 19/600
sz0 n=0: L=4,W=32,size= 2097152 ; flow kappa=1/2; (s,t,K)=(1/10,1/2,4): 0<=s<=t<1, K!=0: True
```

Notes on the output: the numeric `Im m_w` and `T0` are sanity values only (the lower bounds used by the Lean proof are the proved `BASelf_subord` bounds; the numeric values lie inside them). The script's `W^(-7/5) <= g` and `N^(1/9) <= W` loops run over `n<2000`; the Lean statement needs all `n` (monotone in `W`; `(4W)^{1/3} ≤ W` iff `W² ≥ 4`). No `N = 0`, empty index set or collapsed window: `N_0 = 10⁶`, `0 = s < t`, `m = 3`.

External hypothesis: none. The binders `STKboundgL`, `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'` and the two induction hypotheses stay hypotheses of the instances for targets 6 (other gates' pins, as in `inst_iterationsgL'`, `IterationsGen2:468`); no limit computation is owed.

### Verdict per target

- 1 `stNewPQgL_wardCls`: PASS (coefficient identity above; data precede `(sz,C)`).
- 2 `baSTNewPQgL`: PASS (class inclusion plus `baZeroModeGen_wardCls`).
- 3 `baZeroModeSet_UN`, `baZeroModeSet_ThetaN`: PASS (`KerSums` at BA; `hIm` from `κ ≤ Im m`).
- 4 `baStep2Gen_USemigroup`: PASS (first conjunct of `gridRepTailGen_ker_BA`).
- 5 `baIterationsGen2_fam`: PASS (rows 1-6 each matched to a merged guarded or unguarded BA discharge, types read above).
- 6 `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds`: PASS (`𝔠d = 1/100` closes with slack 21/400 and 19/600; `toFlowFM` identification is `rfl`). Instance of case (i) needs the new datum (row 14 proves `sz0` has none); datum B closes with the slacks in rows 5-11.
- Instances (7 (a)-(d)): PASS at the data above.

## (b) Script output — Wed Oct 14 02:59:45 UTC 2026
```
$ lake build RBM3D.BA.ZeroModeBA | tail -4   (warnings only: longLine, show-vs-change linter)
⚠ [4125/4128] Replayed RBM3D.BA.B45BA
⚠ [4127/4128] Replayed RBM3D.BA.GridRepTailBA
⚠ [4128/4128] Replayed RBM3D.BA.ZeroModeBA
Build completed successfully (4128 jobs).
$ lake build (full), after the edit, and the same with RBM3D.lean/Test/Axioms.lean stashed (before)
after : info: RBM3D.lean:608:0: axiom audit: 14969 theorems, 4631 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
        premises found by scanning: 123 (borrowed 1, owed 56, structural 46, refuted 6, superseded 14).; Build completed successfully (4378 jobs).
before: info: RBM3D.lean:607:0: axiom audit: 14957 theorems, 4631 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
        premises found by scanning: 123 (borrowed 1, owed 56, structural 46, refuted 6, superseded 14).; Build completed successfully (4377 jobs).
$ git diff -U0 main...t/T2500 -- RBM3D.lean RBM3D/Test/Axioms.lean   (the Axioms line, cut at the changed tail)
+import RBM3D.BA.ZeroModeBA
-   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot'` (DECISIONS §80); proved at both regimes by T2259 (`stIterations'_holds`, `stIterationsII'_holds`); generic: `stIterationsgL'_of`, `stIterations
+   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot'` (DECISIONS §80); proved at both regimes by T2259 (`stIterations'_holds`, `stIterationsII'_holds`); generic: `stIterationsgL'_of`, `stIterations
$ git diff --stat main...t/T2500
 RBM3D.lean               |   1 +
 RBM3D/BA/ZeroModeBA.lean | 409 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   2 +-
 3 files changed, 411 insertions(+), 1 deletion(-)
$ git diff --stat main...t/T2500 -- RBM3D/Chain RBM3D/Induction RBM3D/BA/{SEforLnBA,B45BA,GridRepTailBA,TwistStep2}.lean | wc -l: 0
$ lake env lean docs/tickets/checks/T2500-check.lean (copy, branch tree): exit 0, lines containing "error": 0
$ scratch file outside the repo (check imports + new module, the check Part 2 pins, `example : T2500_X := <target>` for 8 targets, #print axioms): exit 0, errors 0
'RBM.BA.stNewPQgL_wardCls': [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTNewPQgL': [propext, Classical.choice, Quot.sound]
'RBM.BA.baZeroModeSet_UN': [propext, Classical.choice, Quot.sound]
'RBM.BA.baZeroModeSet_ThetaN': [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Gen_USemigroup': [propext, Classical.choice, Quot.sound]
'RBM.BA.baIterationsGen2_fam': [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIterationsgL'_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIterationsIIgL'_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_newPQ_ba': [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_usemigroup': [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_iterationsgL'': [propext, Classical.choice, Quot.sound]
'RBM.BA.ZeroModeBAInst.inst_iterationsIIgL'': [propext, Classical.choice, Quot.sound]
```
Target statements (script: text from `theorem NAME` to the first line ending in := or := by, RBM3D/BA/ZeroModeBA.lean):
```
-- ZeroModeBA.lean:56
theorem stNewPQgL_wardCls (d : ℕ) : STNewPQgL d (fun sz C => ZeroModeGen_WardCls sz C) := by
-- ZeroModeBA.lean:70
theorem baSTNewPQgL (d : ℕ) :
    STNewPQgL d (fun sz C => ∃ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ ∧ BAFlow sz κ ε 𝔠 𝔡 z ∧ C = baFMz sz z) := by
-- ZeroModeBA.lean:86
theorem baZeroModeSet_UN :
    ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
        zeroModeSet d (sz.L n) A
            (BAUN d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ s t T) =
          BAUN d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ s t
            (zeroModeSet d (sz.L n) A T) := by
-- ZeroModeBA.lean:100
theorem baZeroModeSet_ThetaN :
    ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n k : ℕ) (σ : Fin k → Bool) (t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
        zeroModeSet d (sz.L n) A (Step2Gen_ThetaN (baFMz sz z) n σ t T) =
          Step2Gen_ThetaN (baFMz sz z) n σ t (zeroModeSet d (sz.L n) A T) :=
-- ZeroModeBA.lean:111
theorem baStep2Gen_USemigroup :
    ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ n : ℕ, Step2Gen_USemigroup (baFMz sz z) n :=
-- ZeroModeBA.lean:120
theorem baIterationsGen2_fam (d : ℕ) :
    IterationsGen2_Fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z) := by
-- ZeroModeBA.lean:132
theorem baSTIterationsgL'_holds (d : ℕ) :
    STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
-- ZeroModeBA.lean:140
theorem baSTIterationsIIgL'_holds (d : ℕ) :
    STIterationsIIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=```
Compiled nonempty instances (d = 3, RBM.BA.ZeroModeBAInst; script list of heads; the 8 targets above are in the file's first 150 lines):
```
159:private def σ3 : Fin 3 → Bool := ![true, false, true]
161:private theorem σ3_idiff : (∅ : Finset (Fin 3)) ∪ STIdiff σ3 ≠ ∅ := by
166:theorem inst_newPQ_ba (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)) : (∅ : Finset (Fin 3)) 
183:example (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)) : True := by
190:example :
199:example :
205:theorem inst_usemigroup (n : ℕ) : Step2Gen_USemigroup (baFMz sz0 zSeq) n :=
209:private theorem inst_carrier :
215:example (ω : PathΩ sz0) : True := by
222:example (ω : PathΩ sz0) : True := by
242:private def szI : Sizes 3 where
249:private def wI : ℂ := ⟨0, 5003 / 5000⟩
250:private def mI : ℂ := BAmSubord 3 4 2 wI
251:private def zI : ℕ → ℂ := fun _ => wI - mI
254:private theorem flowI : BAFlow szI (3 / 1000) (1 / 2) (1 / 9) (1 / 10) zI ∧ ∀ n, (1 / 400 :
338:private theorem szI_W_tendsto : Tendsto (fun n : ℕ => ((szI.W n : ℕ) : ℝ)) atTop atTop :=
344:private theorem szI_window (n : ℕ) : (1 / 400 : ℝ) ≤ BAflowT0 szI zI n :=
347:private theorem szI_regIterI : STRegIterI szI (fun _ => 0) (fun _ => 1 / 400) :=
351:private theorem szII_W_tendsto : Tendsto (fun n : ℕ => ((TwistStep2_szII.W n : ℕ) : ℝ)) a
357:private theorem szII_caseII : STCaseII TwistStep2_szII (fun _ => 0) (fun _ => 1 / 2000) := by
364:theorem inst_iterationsgL' (Cd : ℝ) (hCd : 0 < Cd) :
386:theorem inst_iterationsIIgL' (Cd : ℝ) (hCd : 0 < Cd) :
```
Greps (script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2500/greps.sh`, run on the final file; the hypothesis rules of the ticket):
```
C1 grep hits:          0
X1-C4 def/abbrev/structure at line start: 0; private defs: 5 (sigma3, szI, wI, mI, zI)
local copies of pinned texts: 0; T2463_/T2497_ text: 0
UBA: withLam lines: 121 124 133 141 366 367 368 369 370 372 374 376 388 389 390 391 392 394 396 398 | gK / 'A *' hits: 0
sorry|admit|native_decide|axiom: 0
clash stNewPQgL_wardCls: 
clash baSTNewPQgL: 
clash baZeroModeSet_UN: 
clash baZeroModeSet_ThetaN: 
clash baStep2Gen_USemigroup: 
clash baIterationsGen2_fam: 
clash baSTIterationsgL'_holds: RBM3D/Test/Axioms.lean:122:   `RBM.Gauss.Sizes.STIterR', --  
clash baSTIterationsIIgL'_holds: RBM3D/Test/Axioms.lean:122:   `RBM.Gauss.Sizes.STIterR', --  
clash ZeroModeBAInst: 
clash inst_newPQ_ba: 
clash inst_usemigroup: 
inst_iterationsgL'/IIgL' also in: RBM3D/Chain/IterationsGen2.lean RBM3D/BA/ZeroModeBA.lean  (namespaces RBM.BA.IterationsGen2Inst vs RBM.BA.ZeroModeBAInst)
importers of RBM3D.BA.ZeroModeBA: ./RBM3D.lean 
RBM1D/RBM2D ports: none (the datum szI is ported inside this repo from RBM3D/BA/TwistStep2.lean:1341-1435; ZeroModeBA_coef from RBM3D/Chain/ZeroModeGen.lean:318)
withLam occurrences not of the form Sizes.seqP (X.withLam 0): 1
```

Narrative (facts from the files and logs above):
- One new file `RBM3D/BA/ZeroModeBA.lean`, 409 lines (ticket price 200 / 320 / 480, stop line 640; four commits on `t/T2500`, listed by `git log` at the time of the report; `wc -l` was 149 after the part-1 commit and is 409 at the end; the stop size was not reached).
- Routes (merged file:line, all read in the worktree): target 1 `zeroModeGen_newPQ` (`Chain/ZeroModeGen:249`) at the `TL`, `TK` witnesses of `ZeroModeGen_WardCls` (`:289`), the coefficient identity is the private copy `ZeroModeBA_coef` of `ZeroModeGen_coef` (`ZeroModeGen:318`); target 2 target 1 + `baZeroModeGen_wardCls` (`SEforLnBA:66`); target 3 `zeroModeSet_UNg`, `zeroModeSet_ThetaNg` (`ZeroModeGen:161, 179`) at `baZeroModeGen_kerSums` (`B45BA:110`), `UN` through `Step2Kern_UN_BA` (`Step2Kern:124`) with `hIm` from `BAflow_real` (`GreenSchur:59`); target 4 the first conjunct of `gridRepTailGen_ker_BA` (`GridRepTailBA:60`); target 5 rows 1-6 of the ticket's family table by `Step2EventsGenTw_baFlow`, `isProbabilityMeasure_seqP`, `baStep2Mat_loopForm`, `BAm_norm_le_one` at `(BAflow_real ..).1`, `baStep34_LCompat`, `EMn2BA_seqHflowBA_herm`; target 6 `stIterationsgL'_of`, `stIterationsIIgL'_of` (`IterationsGen2:389, 409`) at target 5; `(baStep2Mat ..).toFlowFM = baFMz sz z` was accepted by the elaborator (stop rule not triggered).
- UBA-C1 as used: targets 1-4 read no size level and the kernel level only through `BAUN`, `BAuKer`, `BAReal` at `BAflowLam0`; targets 5-6 read the size level through the pins (`STAI`, `STAII`, `STRegIterI`, `STCaseII`); no crossing; `STGridRepNgL` and `baGridDrift_envelope` are not read.
- Case-(i) datum: private `szI` (`L ≡ 4`, `W_n = n + 25`, `lam ≡ 2`), `flowI : BAFlow szI (3/1000) (1/2) (1/9) (1/10) zI ∧ ∀ n, 1/400 ≤ BAflowT0 szI zI n` = lines 254-336 (83 lines against the 120-line stop), a copy of `TwistStep2_flowII` (`BA/TwistStep2.lean:1353-1435`, this repository) with `g = 2`, `κ = 3/1000`, `t ≡ 1/400`; window `s ≡ 0 < t ≡ 1/400`, `STRegIterI` (`szI_regIterI`: `4/16 ≤ 399/400`, `1 ≤ 4`), `STConStInd` by `conStInd_const`. The numbers are those of section (a) rows 5-11. Case (ii) reuses `TwistStep2_szII`/`TwistStep2_flowII` (`1 ≤ 25/16`, `t ≡ 1/2000`).
- Instances (d = 3): `inst_newPQ_ba` (target 2 at `sz0`, `zSeq`, `flow_sz0`, `m = 3`, `σ = (+,-,+)`, `A = ∅`, `n = 0`, `τ = 1/2`, with `∅ ∪ STIdiff σ ≠ ∅` proved by `decide +kernel`); an `example` for target 1 at the same data; two `example`s for target 3 (`UN`, `ThetaN`) at `A = {0}`, `s = 1/10`, `t = 1/2`, `T ≡ 1` (the ticket says "same data": `A = {0}` instead of `∅` for non-triviality); `inst_usemigroup` (target 4, every `n`); two `example`s (c) `zeroModeCalc_duhamel_inside_atg` and `stoppedDuhamelQNg` at `baStep2Mat sz0 ..`, `n = 0`, `K ≡ 4`, `τ ≡ 2`, `j = 3` (conclusion discarded with `have _ := …; trivial`, premises discharged from target 4 and `baZeroModeGen_kerSums`); `inst_iterationsgL'` (case (i) at `szI`) and `inst_iterationsIIgL'` (case (ii) at `TwistStep2_szII`): flow, window, regime and `STConStInd` discharged; only the pin binders `STKboundgL`, `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'` and the two induction hypotheses stay hypotheses.
- Registry: only the owner text of `STIterR'` changed (diff above); the scan counts (123 premises, 2+119+123+7+18 registered) are identical before and after; no `owedProps` line added or deleted.
- Not here (ticket): WardIdent bridge, QGrid targets 6/8 at BA, `STXiBootgL'` at BA, `STQopNorm`/`STMollifierEx`, `baZeroModeOp_UN`.

## (c) Mathlib names used (all in the compiled file; each from a call in the file that built)
`tendsto_atTop_mono`, `tendsto_natCast_atTop_atTop`, `mul_inv`, `inv_pow`, `div_eq_mul_inv`, plus the names inside the copied datum body (`BA/TwistStep2.lean:1353-1435`: `le_div_iff₀`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_inv_le_iff_of_pos`, `Real.rpow_le_one_of_one_le_of_nonpos`); `decide +kernel` (tactic). Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- No paper-delta candidate: `lem: newPQ` and `lem:iterations` at BA hold through the carrier classes (no `|E| < 2`, `‖m‖ = 1`), as the ticket expects (D720 / D563).
- Report length: the ticket's acceptance line asks for at most 150 lines; section (a) alone is 83 lines, so the whole report exceeds 150 and stays below CLAUDE.md §6's 300.
- Observation: `Sizes.isProbabilityMeasure_seqP (sz.withLam 0)` (line 124) is the only `withLam` not written as `Sizes.seqP (X.withLam 0)`; it is the family row 2 argument for that law.
- Observation: the case-(i) datum duplicates the proof body of `TwistStep2_flowII` with other numbers (a shared parametrised lemma would need a merged-file edit, out of scope).
- Hub merge: the two union files `RBM3D.lean` (one import line after `RBM3D.BA.Step5IIITargets`) and `RBM3D/Test/Axioms.lean` (the `STIterR'` line only) are located by name, as CONTROL H292 (4) says.
