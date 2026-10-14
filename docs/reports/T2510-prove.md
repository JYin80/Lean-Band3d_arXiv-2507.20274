Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 15:03:55 UTC 2026

Row a (targets 1-10). Data: d = 3, `(sz0, zSeq, flow_sz0)`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `E_n = 0`; `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^-6`, `k = n+1`. Numbers are from `inst.py` (below).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `κ`, `κm = κ` (F2) | 1/2 | `κ ≤ Im m_n` (BAdom, `BAReal`) | `Im m_0 = 0.8325`: 0.332 |
| 2 | `ε` | 1/10 | `N^(-1+ε) ≤ Im z ≤ 1` | `N_0^-0.9 = 2.0e-6` vs `Im z_0 = 0.3675`; `Im z ≤ 0.7` |
| 3 | `𝔠` | 1/6 | `W ≥ N^𝔠` | `W/N^(1/6) = 2^(3/2) k^2` (2.83 at `n = 0`) |
| 4 | `𝔡` (window `WO`) | 1/10 | `W^(-3/2+𝔡) ≤ lam ≤ 𝔡^-1` | `lam/W^-1.4 = 2k` (2 at `n = 0`); `lam ≤ 1/64 ≤ 10` |
| 5 | horizon `T0_n` | 0.6937 (n=0), 0.6944 (n≥1) | `T0 ≥ κ/(κ+1) = 1/3`, and `2/3 ≤ T0` (`t0_sz0`) | `T0 - 1/3 = 0.36` |
| 6 | times `s ≡ 1/2 < t ≡ 3/5` (targets 4, 9 (iii)) | `t ≤ 2/3` | `0 ≤ s < t ≤ T0` | `2/3 - t = 1/15`; `t - s = 1/10` |
| 7 | `g₀ = √T0 · lam` | `1.30e-2` (n=0), `2.0345e-4` (n=1) | `0 < g₀ ≤ 𝔡^-1` (eventual window) | `g₀ ≤ 1/64` vs 10 |
| 8 | R1 `Aof κ = (κ+1)/κ` (`baEKKer_flow`) | 3 | `1 ≤ Aof κ`; `g₀² ≤ lam²`; `lam² ≤ Aof κ · g₀²` | `lam²/g₀² = 1/T0 = 1.44`: factor 2.08 to 3; `1 ≤ 3` |
| 9 | `κ' = min(κ,1)`, `δ = ε/2` (`baIniTermGen_cltFlow`) | 1/2, 1/20 | `κ' ≤ Im m`; `N^(-1+δ) ≤ 1 - T0` | `N_0^-0.95 = 9.9e-7` vs `1 - T0 ≥ 11/36` |
| 10 | `𝔠d` per pin | LKLK, DriftLog, DriftDecay, WardI, WardI′, IntII: 1/100; IniI′: `1/(100 d)` = 1/300 | `0 < 𝔠d ≤ 1/100`; IniI′: `d 𝔠d = 1/100 < 1` | slack 0 (LKLK) |
| 11 | `𝔠d` per regime (target 9) | (iii) `min(1/100, c_IntIII)`; (iv) `min(1/100, c_IntIV)`; (ii) `min(1/100, 1/100, c_WardII)` | `∈ (0, 1/100]` | `1/100 - min ≥ 0`; `c_*` = the T2508 pin's own constant (binder) |
| 12 | `STConStInd`, ratio `(1-t)/(1-s)` | 4/5 (iii) | `Bctl^𝔠d ≤ (1-t)/(1-s) < 1` eventually; `Bctl = W^-3 B_{t,0}` | holds for `n ≥ 2` at `𝔠d = 1/100` (`n ≥ 53` at `(s,t) = (0,1/2)`) |
| 13 | `CM` (target 2) | `K · ((1+e^-cM)/(1-e^-cM))^3`, `K = max(c^-1,1)`, `cM = min(c, log 2)`, `(C,c)` of `baPropM_holds d 𝔡^-1 κ` (∃); explicit alternative `GreenCond2_row_l1`: `c0 = min(log(1+κ/(4 d 𝔡^-1)), κ/2) = 4.158e-3`, `CM = 2.676e10` | `0 < CM`; `Σ_q ‖M^(B)_aq‖ ≤ CM` eventually; `CM` depends on `(d, κ, 𝔡)` only | true row sums 1.32 (n=0), 1.20 (n=1) |
| 14 | `Cs` (target 3) | `baEKSameRow_holds d 𝔡^-1 κ` (∃, before `𝔠, sz, z`) | `0 < Cs`; `Cs(CM+1) ≤ N^(τ/3)` is eventual inside merged `stImproveCoregL_of` | no value enters an instance |
| 15 | row-17 constant | `C · ((κ+1)/κ)^(k-1) = C · 3^(k-1)` (`SEforLnBA_Kbound`) | `∃` before `sz, z` | n/a |
| 16 | regime (iii) window (sz0) | `lam² ≤ 1 - t` | `2^-12 ≈ 2.4e-4 ≤ 2/5` | 0.4 |
| 17 | index set of `BALWtermEXPTw` at `u ≤ 3/5` | `lam²/L^d ≤ 1 - u` | `3.8e-6` at `n = 0` (script: `≤ 1/2` for all `n < 400`) | nonempty, slack ≥ 0.39 |
| 18 | pinned exponents `3/2` (TL2), `5/2` (LW), `-1/5` (`STExp2UgL`) | carried by the merged texts | none recomputed in row a | n/a |

Corrections to the ticket's tables (none moves a pin, a row or a stop line; no new mathematics):
- **F5 (target 8, row 13, all d).** `STExpDuhamelZgL`/`QgL` (`Chain/Step6Gen:323-330`) carry no `3 ≤ d →`, and `baIniTermGen_kerFacts d` starts `intro d hd`. So `Step2Gen_USemigroup` for `d < 3` is not "conjunct 1 of `baIniTermGen_kerFacts`" (needs `3 ≤ d`); it is the body of that conjunct (`Step5KerBA:172-177`): `BAuKerSemigroup_holds d` (`TwistGrid:199`, no `hd`) + `Step2Kern_uKer_BA` + `BAflow_real`. `baHierDrift_classes`, `baCltRepg_holds`, `baStep2Mat_loopForm d`, `baStep2Mat_S` have no `hd`. No new fact.
- **F6 (target 7).** `stExpLKLKHigL_of`, `stExpDriftLogL_of`, `stExpIniIgL'_of` take `hK`/`hKb : … → STKboundgL` unguarded in `d`; `SEforLnBA_Kbound` needs `3 ≤ d`. Every target-7 pin starts `3 ≤ d →` (`STIngR6gL`), so `hK` is supplied under that `hd`.
- **F7 (target 1).** No range premise `u ≤ BAflowT0` is needed: `0 < Im m` is `BAflow_real` (all `n`, `0 < κ`); the pin text stands.

### (ii) One concrete nondegenerate instance

Per target (every deterministic hypothesis holds at the numbers; stochastic pins of other gates and TL1/TL2, the Step 1/2 conclusions and the T2508 pins stay binders):
- Targets 1, 3 (16a): `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `u ≡ 1/2 ≤ 2/3 ≤ T0`, `flow_sz0`. Target 2: `(κ, 𝔡) = (1/2, 1/10)`, `CM` of row 13. Target 4: `s ≡ 1/2 < t ≡ 3/5`. Target 6: a def.
- Target 7 pins, by regime (the pin's own `R`; 6 of the 7 are empty at `sz0`): LKLK `R = STDriftHi` at `sz0` (`lam²/L³ ≤ 1 - t`). WardI, WardI′, DriftDecay, IniI′ `R = STReg5I`: needs `lam²/L² ≤ 1 - t ∧ 1 - s ≤ lam²`; datum (i) `(L, W₀, lam, κ) = (4, 25, 2, 3/1000)`, `s ≡ 0`, `t ≡ 1/400`. DriftLog `R = STReg5IV`: needs `1 - s ≤ lam²/L³`; datum (iv) `(3, 40, 6, 1/1000)`, `s ≡ 0`, `t ≡ 1/2000`. IntII `R = STReg5II`: public `TwistStep2_szII/flowII`, `s ≡ 0`, `t ≡ 1/2000`.
- **F8 (instance data).** The ticket's pointer (`TwistStep2_szII` for (i), (ii), (iv)) fails for (i) and (iv): at `szII` `lam²/L² = 25/16 > 1 - t`, and `s ≥ 39/64` is needed for (iv) but `T0 = 0.3173` (script). Data for (i), (iv): the parametrised private family of `BA/Step5CasesBA.lean` (`_sz`, `_z`, `_flow`, `_conStInd`, `_Datum`; text copied, `L, W₀, lam, κ` as parameters; side conditions `1 ≤ lam ≤ 10`, `3/5000 ≤ κ`, `κ(‖w‖² + lam² L³) ≤ Im w`, `100 ≤ W₀ L`, `L ≤ W₀`: (i) `3e-3 · 257 = 0.77 ≤ 1.0006`; (iv) `1e-3 · 973 = 0.97 ≤ 1.0006`), `w = (5003/5000) i`, `(ε, 𝔠, 𝔡) = (1/2, 1/9, 1/10)`. Decision (10) covers private data; fallback not needed.
- Target 8 (O5): index `n = 1` at `sz0`: `L = 8`, `W = 1024`, `lam = 1/4096`, `g₀ = 2.0345e-4`, `H₀ = g₀ Ψ ≠ 0` (`inst_lam0_pos`), `Im m = 0.8333`, `S = SB d L 0 = 1`; `KLoop`, `KTwo` at `n = 1` need `0 < g₀`, `BAReal` (`GridDriftBA:726-731`); `KLink`, USemigroup every `n`.
- Target 9: (iii) `sz0`, `s ≡ 1/2`, `t ≡ 3/5` (`R = lam² ≤ 1 - t`); (ii) `szII`, `(0, 1/2000)`, `1 - s = 1 ≤ lam²/L² = 25/16`, `lam²/L³ = 25/64 ≤ 1 - t`; (iv) datum (iv). `STConStInd` at every `𝔠d > 0` is `conStInd_const` (public, `sz : Sizes 3`) at `sz0`/`szII`, or the copied `_conStInd`.
- Targets 5, 10: private glue and the instance list above.
- Identity of target 1 (`t_aq - M^(++)_aq = M^(B)_aq · twTr(q, a)`, transposed pair `(q, a)`: TL1 is over all ordered pairs) was checked by random matrices:

```
$ python3 -I .../scratchpad/T2510/ident.py
max |(t - M++)_{aq} - MB_{aq} twTr(q,a)| = 3.3306690738754696e-16
max |(t - M++)_{aq} - MB_{aq} twTr(a,q)| = 2.374979318206039 (transposed pair: not an identity)
```

Numbers (`inst.py`: Fourier spectrum of `Ψ^(B)` on `Z_L^3`, `m_w = L^-3 tr(gΨ - w)^-1`, `z = w - m`, `T0 = Im m/Im w`, `Bctl = W^-3((lam² + |1-t|)^-1 + (L³|1-t|)^-1)`):

```
$ python3 -I .../scratchpad/T2510/inst.py
== sz0: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6; flow (kappa,eps,c,dd)=(1/2,1/10,1/6,1/10), z=zSeq, E=0
n=0: W=32 L=4 N=2097152 lam=0.015625 | Im m=0.832488 (kappa=.5, slack 0.332) | N^(-1+eps)=2.04e-06 <= Im z=0.3675 <= 1 | T0=0.693740 (>=2/3) | W/N^c=2.828 | lam/W^(-3/2+dd)=2 | g0=0.0130142 | lam^2/g0^2=1.441 (<=3)
n=1: W=1024 L=8 N=549755813888 lam=0.000244141 | Im m=0.833333 (kappa=.5, slack 0.333) | N^(-1+eps)=2.72e-11 <= Im z=0.3667 <= 1 | T0=0.694444 (>=2/3) | W/N^c=11.314 | lam/W^(-3/2+dd)=4 | g0=0.00020345 | lam^2/g0^2=1.440 (<=3)
n=2: W=7776 L=12 N=812479653347328 lam=2.14335e-05 | Im m=0.833333 (kappa=.5, slack 0.333) | N^(-1+eps)=3.81e-14 <= Im z=0.3667 <= 1 | T0=0.694444 (>=2/3) | W/N^c=25.456 | lam/W^(-3/2+dd)=6 | g0=1.78612e-05 | lam^2/g0^2=1.440 (<=3)
regime (iii) at sz0, s=1/2, t=3/5 (<=2/3<=T0): lam^2<=1-t=2/5 for n<400: True ; (1-t)/(1-s)=4/5, Bctl^(1/100)<=4/5 for n>= 2 ; (s,t)=(0,1/2): n>= 53
TL1 at u=1/2: lam^2/L^3<=1-u (index set nonempty) for n<400: True
regime (ii) at TwistStep2_szII (L=4,W=n+25,lam=5,kappa=3/5000), s=0,t=1/2000: Im m=0.31746, T0=0.31727; lam^2/L^3=0.39062<=1-t; 1-s=1<=lam^2/L^2=1.5625
   regime (iv) at szII needs s>=1-lam^2/L^3=39/64=0.6094 but t<=T0=0.3173: window EMPTY; (i) needs lam^2/L^2=25/16<=1-t: EMPTY
regime (i) datum (pattern ZeroModeBA szI: L=4,W=n+25,lam=2,kappa=3/1000), s=0,t=1/400: Im m=0.34300>=.003, Im z=0.65760>=N0^(-1/2)=0.00100 (N0=1000000), T0=0.34280>=1/400; STReg5I: lam^2/L^2=0.25<=1-t=0.9975, 1-s=1<=lam^2=4
   (con_st_ind) Bctl^(1/300)<=399/400 for n>= 0
regime (iv) datum (L=3,W=n+40,lam=6,kappa=1/1000), s=0,t=1/2000: Im m=0.44580>=.001, Im z=0.55480>=N0^(-1/2)=0.00076 (N0=1728000), T0=0.44554>=1/2000; STReg5IV: 1-s=1<=lam^2/L^3=1.3333
   (con_st_ind) Bctl^(1/100)<=1999/2000 for n>= 0
CM (W1iv): c0=min(log(1+kappa/(4 d Lambda)),kappa/2)=0.00415801 (Lambda=1/dd=10), CM=c0^-1((1+e^-c0)/(1-e^-c0))^3=2.676e+10
  n=0: sum_b |M^(B)_(0,b)| = 1.32102 <= CM
  n=1: sum_b |M^(B)_(0,b)| = 1.20176 <= CM
```

External hypothesis: none is added (no authorized external input enters row a). The only limits are `Bctl^𝔠d → 0` (row 12: `W^-3 → 0`, thresholds in the output) and the eventual windows `0 < g₀ ≤ 𝔡^-1` (`g₀_n ≤ 0.013` for all `n`); TL1, TL2 are owed pins that stay binders.

### Verdicts
- Targets 1-10: **PASS** (each hypothesis set holds at the data above; the exponents close with the slacks of (i)).
- (iii) needs only TL1 at `u` and `0 < Im m` (identity above, `BAflow_real`, `twMB_ba`); no range premise. The cut grep and name-clash grep move to the 1b head (ticket fill-in (viii)).
- No pin, row or stop line moves: F5-F8 change the discharge name or the private datum, not a pin text or row set. No 1a-audit needed.

## (a′) Preflight corrections — Wed Oct 14 15:32:21 UTC 2026

Three differences from section (a); none moves a pin, a row, a stop line or a statement.
- **Instance data of regimes (i), (ii), (iv)** (a) (ii) names the public `TwistStep2_szII/flowII` for (ii) and a copied parametrised family for (i), (iv).  The built instances read the one parametrised private datum of `BA/Step5CasesBA.lean` by `open private` (`Step5CasesBA_sz`, `_z`, `_Datum`, `_datum`) for all three, at the numbers of (a): (i) `(L, W₀, lam, κ, t) = (4, 25, 2, 3/1000, 1/400)`, (iv) `(3, 40, 6, 1/1000, 1/2000)`, (ii) `(4, 25, 5, 3/5000, 1/2000)` (the numbers of `TwistStep2_szII`, `TwistStep2_flowII`), `s ≡ 0`, `(ε, 𝔠, 𝔡) = (1/2, 1/9, 1/10)`.  `Step5CasesBA_Datum` also carries `(con_st_ind)` at every `𝔠d > 0`.  No text was copied.
- **Imports of file 2**: `Chain/ExpEtermsAGen` (the module of `stExpLKLKHigL_of`) and `BA/Step5CasesBA` (the instance data above) are added to the ticket's list; `BA/Step5CasesBA` is read only through `open private`, and the cut grep stays 0.
- F5, F6, F7 of (a) hold as written (F5: `Step6PinsBA_USemigroup` is the body of the first conjunct of `baIniTermGen_kerFacts`; F6: `SEforLnBA_Kbound d hd` is applied after `intro hd`; F7: target 1 has no range premise).

## (b) Script output — Wed Oct 14 15:32:21 UTC 2026

```
$ lake build RBM3D.BA.Step6BridgeBA RBM3D.BA.Step6PinsBA 2>&1 | grep -v "longLine|exceeds the 100|^$" | tail -4
⚠ [4239/4240] Replayed RBM3D.BA.Step5CasesBA
You can use "string gaps" to format long strings: within a string quotation, using a '\' at the end of a line allows you to continue the string on the following line, removing all intervening whitespace.
⚠ [4240/4240] Replayed RBM3D.BA.Step6PinsBA
Build completed successfully (4240 jobs).
$ wc -l RBM3D/BA/Step6BridgeBA.lean RBM3D/BA/Step6PinsBA.lean; git diff --stat d1839622 HEAD; git diff --stat d1839622 HEAD -- RBM3D/Chain RBM3D/Induction RBM3D/Graph | wc -l
     395 RBM3D/BA/Step6BridgeBA.lean
     488 RBM3D/BA/Step6PinsBA.lean
     883 total
 RBM3D.lean                  |   2 +
 RBM3D/BA/Step6BridgeBA.lean | 395 +++++++++++++++++++++++++++++++++++
 RBM3D/BA/Step6PinsBA.lean   | 488 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |  22 +-
 4 files changed, 896 insertions(+), 11 deletions(-)
       0
$ lake env lean ax.lean   # #print axioms of every new public declaration
18 declarations, each `[propext, Classical.choice, Quot.sound]`: baExpAvgGen_W1iii_of_tl1 baExpAvgGen_W1iv baExpAvgGen_W1fam baImproveCoregL baExpAvgUgL_of_tl1 BAStep6R baExpLKLKHigL baExpDriftLogL baExpDriftDecaygL baExpWardIgL baExpWardIgL' baExpIniIgL' baExpIntIIgL baExpDuhamelZgL baExpDuhamelQgL baStep6RegIII_of_pin baStep6RegIV_of_pin baStep6RegII_of_pin
```

Target statements (script `stmts.py`: public `theorem`/`def` header through `:=`, whitespace collapsed; file:line):
```
Step6BridgeBA.lean:108: theorem baExpAvgGen_W1iii_of_tl1 (d : ℕ) : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u → ExpAvgGen_W1iii (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u :=
Step6BridgeBA.lean:134: theorem baExpAvgGen_W1iv (d : ℕ) : 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ CM : ℝ, 0 < CM ∧ ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ExpAvgGen_W1iv (baFMz sz z) CM :=
Step6BridgeBA.lean:186: theorem baExpAvgGen_W1fam (d : ℕ) : ExpAvgGen_W1fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
Step6BridgeBA.lean:202: theorem baImproveCoregL (d : ℕ) : STImproveCoregL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6BridgeBA.lean:258: theorem baExpAvgUgL_of_tl1 (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STStep2CoregL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → STExpAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t :=
Step6PinsBA.lean:83: theorem baExpLKLKHigL (d : ℕ) : STExpLKLKHigL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:91: theorem baExpDriftLogL (d : ℕ) : STExpDriftLogL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:100: theorem baExpDriftDecaygL (d : ℕ) : STExpDriftDecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:109: theorem baExpWardIgL (d : ℕ) : STExpWardIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:117: theorem baExpWardIgL' (d : ℕ) : STExpWardIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:125: theorem baExpIniIgL' (d : ℕ) : STExpIniIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:135: theorem baExpIntIIgL (d : ℕ) : STExpIntIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
Step6PinsBA.lean:176: theorem baExpDuhamelZgL (d : ℕ) : STExpDuhamelZgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
Step6PinsBA.lean:182: theorem baExpDuhamelQgL (d : ℕ) : STExpDuhamelQgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
Step6PinsBA.lean:196: theorem baStep6RegIII_of_pin (d : ℕ) : STExpIntIIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5III :=
Step6PinsBA.lean:224: theorem baStep6RegIV_of_pin (d : ℕ) : STExpIntIVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5IV :=
Step6PinsBA.lean:251: theorem baStep6RegII_of_pin (d : ℕ) : STExpWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5II :=
```
`BAStep6R` (the one new public `def`, `Step6PinsBA.lean`):
```
def BAStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
    (fun sz z s t => (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
      STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
```

Statement diff against the pins (`T2510_*` of `docs/tickets/checks/T2510-check.lean`; every target is accepted at the pin's type by the elaborator, so it equals the pin up to the name; `T2510_LWAvgEv` is a shape, read by the private twin `Step6BridgeBA_LWAvg_ev`, not binding; `T2510_RowB` is row b):
```
$ lake env lean pindiff.lean; echo "exit: $?"   # check Part 2 (T2510_* defs copied verbatim from docs/tickets/checks/T2510-check.lean:133-217, one example per target); uncommitted scratch
exit: 0
89:example (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : T2510_Step6BA d R = BAStep6R d R := rfl
90:example : ∀ d, T2510_W1iiiOfTL1 d := baExpAvgGen_W1iii_of_tl1
91:example : ∀ d, T2510_W1ivBA d := baExpAvgGen_W1iv
92:example : ∀ d, T2510_W1famBA d := baExpAvgGen_W1fam
93:example : ∀ d, T2510_CoreBA d := baImproveCoregL
94:example : ∀ d, T2510_ExpAvgUBA d := baExpAvgUgL_of_tl1
95:example : ∀ d, T2510_IngBA d := fun d => ⟨baExpLKLKHigL d, baExpDriftLogL d, baExpDriftDecaygL d, baExpWardIgL d, baExpWardIgL' d,
97:example : ∀ d, T2510_RegIIIOfPin d := baStep6RegIII_of_pin
98:example : ∀ d, T2510_RegIVOfPin d := baStep6RegIV_of_pin
99:example : ∀ d, T2510_RegIIOfPin d := baStep6RegII_of_pin
```

Compiled nonempty instances (`d = 3`; script `exs.py`: each `example` collapsed, cut at 235 characters; all `example`s sit in the files, after the section header "Compiled nonempty instances"; every deterministic hypothesis is discharged, the binders left are other gates' owed pins):
```
Step6BridgeBA.lean:358: example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) : ExpAvgGen_W1iii (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) :=
Step6BridgeBA.lean:363: example : ∃ CM : ℝ, 0 < CM ∧ ExpAvgGen_W1iv (baFMz sz0 zSeq) CM :=
Step6BridgeBA.lean:368: example : ∃ Cs CM : ℝ, 0 < Cs ∧ 0 < CM ∧ ∃ (H₀ : ∀ n, Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) (g' E : ℕ → ℝ), CltRepg (baFMz sz0 zSeq) μ0 H₀ g' E ∧ (∀ n, ExpAvgGen_W1i (baFMz sz0 zSeq) H₀ g' E n) ∧ ExpAvgGe...
Step6BridgeBA.lean:376: example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) : STExpAvgAtgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) :=
Step6BridgeBA.lean:383: example (hS2 : STStep2CoregL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 3 / 5)) (hLKU : STLKUgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 3 / 5)) (hTL1 : ∀ u : ℕ → ℝ, (∀ n, (1 / 2 : ℝ) ≤ u n) → (∀ n, u n ≤ 3 / 5) → BATwistA...
Step6PinsBA.lean:345: example (hp : Step6PinsBA_prem sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 5)) : STExpLKLKHiConclgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 3 / 5) :=
Step6PinsBA.lean:397: example (hp : Step6PinsBA_prem Step6PinsBA_szIV Step6PinsBA_zIV (fun _ => 0) (fun _ => 1 / 2000)) : STExpAvgUgL (baFMz Step6PinsBA_szIV Step6PinsBA_zIV) (Sizes.seqP (Step6PinsBA_szIV.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) → ST...
Step6PinsBA.lean:403: example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400)) : STExpDriftDecayConclgL (baFMz Step6PinsBA_szI Step6PinsBA_zI) (Sizes.seqP (Step6PinsBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) :=
Step6PinsBA.lean:408: example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400)) : STExpAvgUgL (baFMz Step6PinsBA_szI Step6PinsBA_zI) (Sizes.seqP (Step6PinsBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) → STExpWard...
Step6PinsBA.lean:414: example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400)) : STExpAvgUgL (baFMz Step6PinsBA_szI Step6PinsBA_zI) (Sizes.seqP (Step6PinsBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) → STExpWard...
Step6PinsBA.lean:420: example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400)) : STExpIniIConclgL' (baFMz Step6PinsBA_szI Step6PinsBA_zI) (Sizes.seqP (Step6PinsBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) :=
Step6PinsBA.lean:425: example (hp : Step6PinsBA_prem Step6PinsBA_szII Step6PinsBA_zII (fun _ => 0) (fun _ => 1 / 2000)) : STExpDuhEqgL (baFMz Step6PinsBA_szII Step6PinsBA_zII) (Sizes.seqP (Step6PinsBA_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) → S...
Step6PinsBA.lean:437: example : 0 < BAflowLam0 sz0 zSeq 1 ∧ STExpHierAtgL (baFMz sz0 zSeq) μ0 1 ∧ STExpDuhamelZAtgL (baFMz sz0 zSeq) μ0 1 ∧ STExpDuhamelQAtgL (baFMz sz0 zSeq) μ0 1 :=
Step6PinsBA.lean:451: example : (∃ n, STExpDuhamelZAtgL (baFMz sz0 zSeq) μ0 n) ∧ ∃ n, STExpDuhamelQAtgL (baFMz sz0 zSeq) μ0 n :=
Step6PinsBA.lean:461: example (hInt : STExpIntIIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (hp : Step6PinsBA_prem sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 5))...
Step6PinsBA.lean:469: example (hInt : STExpIntIVgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (hp : Step6PinsBA_prem Step6PinsBA_szIV Step6PinsBA_zIV (fun _ => 0...
Step6PinsBA.lean:477: example (hWd : STExpWardIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (hp : Step6PinsBA_prem Step6PinsBA_szII Step6PinsBA_zII (fun _ => 0...
```

Greps and name-clash check:
```
$ greps (statements = public theorem/def headers through ":=" by stmts.py, plus the body of BAStep6R; files = both row-a files)
# C1  grep -cE "mE|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM" on statements:
0
# X1-C4  grep -nE "^(noncomputable )?(def|abbrev|structure) " on both files:
RBM3D/BA/Step6PinsBA.lean:59:def BAStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
# UBA  grep -n withLam | grep -v "seqP (sz.withLam 0)" (hits: instance sizes only, all of the form `Sizes.seqP (X.withLam 0)`):
0
# V1L-C1  grep -cE "STImproveExpAver|st6_expAvgU_of_ping|LWtermEXPG" on statements:
0
# cut  grep -cE "T2508|ExpWardIIGen|ExpIntEasyGen|ExpIntIGen|QopDecayGen|ExpIntIQGen" on both files:
RBM3D/BA/Step6BridgeBA.lean:0
RBM3D/BA/Step6PinsBA.lean:0
# sorry/admit/axiom/native_decide in both files:
RBM3D/BA/Step6BridgeBA.lean:0
RBM3D/BA/Step6PinsBA.lean:0
$ git grep -nE "(theorem|def|abbrev|structure|lemma) (<18 public names>|Step6BridgeBA_|Step6PinsBA_)" <ref> -- RBM3D ":!<my two files>" | wc -l   # declarations; a plain-name grep finds 1 hit on each ref, the registry comment at Test/Axioms.lean:226 (`BAStep6R`)
main (beefb80b): 0
t/T2508b (8c23f0ba): 0
t/T2509 (0768f64d): 0
t/T2503 (93bd54cd): 0
t/T2502c (7cf02a5f): 0
t/T2507 (dff84231): 0
```

Registry (`RBM3D/Test/Axioms.lean`, owner texts of lines 227-229, 230, 231-234, 236, 239, 242 by name; no list membership changed) and the `#assert_rbm_axioms` scan, `lake build RBM3D` before (worktree at `d1839622`) and after the root imports and the registry edit:
```
$ python3 scan_cmp.py scan_before.txt scan_after.txt   # `lake build RBM3D` log, "theorems resting on each premise THIS FORMALIZATION owes", changed entries only
  BATwistAvgLaw: 1 -> 3; STLKUgL: 11 -> 12; ExpAvgGen_W1fam: 3 -> 4; ExpAvgGen_W1iii: 2 -> 3; STExpLKLKHigL: 7 -> 8; STExpDriftLogL: 3 -> 4; STExpDriftDecaygL: 5 -> 6; STExpWardIgL: 3 -> 4; STExpWardIIgL: 3 -> 4; STExpIntIIgL: 3 -> 4; STExpIntIIIgL: 3 -> 4; STExpIntIVgL: 3 -> 4
  [before] info: RBM3D.lean:637:0: axiom audit: 15353 theorems, 4727 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  [before] premises found by scanning: 131 (borrowed 1, owed 57, structural 53, refuted 6, superseded 14).
  [before] registry: 2 borrowed + 123 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet
  [after] info: RBM3D.lean:639:0: axiom audit: 15370 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  [after] premises found by scanning: 130 (borrowed 1, owed 56, structural 53, refuted 6, superseded 14).
  [after] registry: 2 borrowed + 123 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet
$ lake build   # whole library, final state: "Build completed successfully (4409 jobs)" (the full scan passes)
```
Ports: none from RBM1D or RBM2D (the probe `T2502c_ba_W1i`, `T2502c_ba_W1fam`, `t/T2502c` 0f0ad532 `Probe/T2502Pins.lean:227-262`, is of this project), so no RBM1D/RBM2D diff-stat.

Narrative.
1. Sizes: `Step6BridgeBA` 395, `Step6PinsBA` 488 lines against the bottom-up 500 / 500 (row a 883 against 1,000 central, calibrated 960-1,280) and the stop lines 800 / 800.  Stop rule at each commit (`wc -l`): 17e4357e 340 + 289 = 629; 63db4b1e 395 + 488 = 883; fa334570, eb8a998b 395 + 488.
2. Routes.  T1 `Step6BridgeBA_iii_ident` (`:53-103`): `BAMfine_eq`; `twLoopX n G M a q q` by `TwistPins_circ_term`; `Tr(M P) = M^{(B)}_{qa}` by `card_Iblk`; `Step2Kern_Mss_BA`; then `precomp_param` (swap), `StochDomAt.mul` with `refl`, `of_le_left` (TL1 at `u` and `0 < Im m` only; no probe needed, no 1a-audit).  T2 `CltFlowBA_MB_decay` + `GreenCond2_sum_exp_le`, `CM = K ((1+e^{-c_M})/(1-e^{-c_M}))^d`, window `BAflow_lam0_window`.  T3 probe port with `CM` of T2; `baImproveCoregL = stImproveCoregL_of (baStep5CasesGen_flowFacts d) (baExpAvgGen_W1fam d)`.  T4 `:211-270` (section `Avg`; F1 below).  T5 `Step6BridgeBA_LW` (`:276-296`, `baLWtermEXPTw_holds`, TL1/TL2 at `u` from the `Concl` slot) and `Step6BridgeBA_decay` (`:298-334`: `baDecayLoopU_of`; `baEtermDecaygL` at `k = 2` through `STELKLKMg_eq_STelklkMg`, `STEGtMg_eq_STegtMg`, `Step2EventsGen_STEGtMg_eq`, `baStep2Mat_listLink`).  T6 the def.  T7 the seven merged producers (`stExpLKLKHigL_of`, `stExpDriftLogL_of`, `stExpDriftDecaygL_of`, `stExpWardIgL_of`, `stExpWardIgL'_of`, `stExpIniIgL'_of`, `stExpIntIIgL_of`).  T8 `stExpDuhamelZgL_ev`, `stExpDuhamelQgL_ev` with `Step6PinsBA_rep`, `_cls` (`baHierDrift_classes`), `_USemigroup`.  T9 the bodies of `Step6KitGen:676, 715, 746` with the cores `st6_caseIII/IV/II_coreg` (`:505, 520, 536`), `𝔠d = min` of the input pins' constants.
3. Tables as used.  Coverage rows read: 1-4 (`isProbabilityMeasure_seqP`, `Step2EventsGenTw_baFlow`, `baStep5CasesGen_flowFacts`, `Step2EventsGenTw_baRot3`); 5 (`baEKSumNdecaygL_holds`); 6, 16 (`baEKNonzerogL_holds`, `baEKSumRes2NALgL_holds`, `baEKSumRes2gL_holds`, `baEKKer_flow` with `Aof κ = (κ+1)/κ`); 7 cores; 9, 9′ (`baCltRepg_holds`, `baIniTermGen_cltFlow`); 9 + 14, (iii), (iv) (T1-T3); 10-13 (`baStep2Mat_loopForm`, `baStep2Mat_S`, `baHierDrift_classes`); 17 (`SEforLnBA_Kbound`); 18 (T5); 19 eventual (`baKsol_oneLoop`); 19′ (`baB45Gen_facts`); 20 (`baSEforLnGen_facts`, column sums); 21 (T4).  Rows 22, 23 and the T2508 pins are not read (row b).  Pin table: the nine pins of T7, T8 and the three regimes of T9 as in the ticket's pin table, rows a.
4. F1 as used: `Step6BridgeBA_K1` (`:213-218`, from `baKsol_oneLoop`), `Step6BridgeBA_LWAvg_ev` (`:220-234`) and `Step6BridgeBA_expAvgU_of_core` (`:236-253`) are private twins of `LWAvgLawgL_of_STAvgUgL_at`, `stExpAvgUgL_of_core` with `hK1 : ∀ᶠ n, …`; `baExpAvgUgL_of_tl1` (`:255-268`) and `Step6BridgeBA_LW` use them; no `STImproveExpAvergL`, no every-`n` `hK1`, no `LWtermEXPG` in a statement.
5. Instances: `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^-6`), `zSeq`, `flow_sz0`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`; targets 1-4, regime (iii) and `STDriftHi` at `s ≡ 1/2 < t ≡ 3/5 ≤ 2/3 ≤ T₀` (`t0_sz0`), `lam² ≤ 2/5` by `lam ≤ 1/64`; TL1 at `u ≡ 1/2` is `baTwistAvgProd_holds` (binders `LWAvgLawgL`, `STLmaxgL`).  O5 (target 8): index `n = 1` (`L = 8`, `W = 1024`), `0 < g₀` (`inst_lam0_pos`), `stExpHiergL_at`, `stExpDuhamelZgL_at`, `stExpDuhamelQgL_at` with `KLoop`, `KTwo` (`baHierDrift_kLoop`, `_kTwo`), `KLink`, loop form, `S = SB d L 0`, the semigroup law all discharged; plus the family forms are true at some index (`Eventually.exists`).  Regime data as in (a′); `STIngR6gL`'s seven stochastic premises (`Step6PinsBA_prem`), TL1, TL2 and the three T2508 pins stay binders.
6. Registry: the scan finds no new unregistered premise; `BAStep6R` is not listed, so `structuralProps` is unchanged; `ExpAvgGen_W1iii` now carries nothing in the scan (it is concluded by theorems, not removed from `owedProps`).
7. Stop rules: no target differs from its pin; no merged file changed; one public def; no file near its stop line; row a reads no T2508 name (cut grep 0).

## (c) Verified Mathlib names

`Real.exp_lt_one_iff` (`Mathlib/Analysis/Complex/Exponential.lean:336`, used in `baExpAvgGen_W1iv`); `Filter.Eventually.exists` (`baExpDuhamelZgL` instance); `inv_anti₀`, `pow_le_pow_left₀`, `div_le_self`, `one_le_pow₀`, `le_div_iff₀`, `Finset.sum_add_distrib`, `Finset.sum_const`, `nsmul_eq_mul`, `norm_mul` (all compiled in the files).  Verified absent: `Real.exp_lt_one` (the compiler: unknown constant).

## (d) Open issues and paper-delta candidates

1. No obstruction.  Every target is proved and every instance compiled; the 1b changed the instance data pointer of (a) (a′).
2. Paper-delta candidates: none (`T2510a` not used).  F1 is Lean-internal (the every-`n` `hK1` has no BA discharge; the eventual twins replace it); D725, D727 are the ticket's.
3. Row b reads from this row: `BAStep6R`, `baExpAvgUgL_of_tl1`, `baExpAvgGen_W1iii_of_tl1`, `baExpLKLKHigL`, `baExpDriftDecaygL`, `baExpWardIgL'`, `baExpIniIgL'`, `baExpDuhamelQgL`, `baExpIntIIgL` and the private `Step6BridgeBA_LW` (by `open private`); V2a reads `BAStep6R d R` by name.
4. `RBM3D.lean` (two import lines after `import RBM3D.Chain.ExpIntIGen`) and `Test/Axioms.lean` (eleven owner texts) are a union with T2508 row b and T2509 at merge, located by name.
