Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 06:26:00 UTC 2026

Scripts in `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2181` (`tok.py rows.py inst.py cons.py label.py matrix.py chain.py`). Notation as the ticket; `d = 3` numbers; `M_u = W^d(1-u)`, `P = L^d W^{6d}`, `Y = (log W)^{3/4}`, `S = e²e^{2Y}`, `T(x) = M_u^{-2}e^{-√x} + W^{-D}`.

### (i) Exponent table
| # | quantity | derivation | constraint | slack |
|---|---|---|---|---|
| 1 | `d=2` tokens → `d≥3` | `Z2→Zd d L`, `zdist2→zdistInf d L`, `(W:ℝ)^2→(W:ℝ)^d`, `scaleM→W^d(1-u)`, `etaT, ellT, ρ` dropped (`ℓ_u=1`), `ellStar→(log W)^{3/2}`, `tailT→tailTD d W u D`, `L²W¹²→P`, `81→9^d` ((2ℓ**+1)^d), `162→2·9^d` (N1), `200→3^{d+1}` (inside `c_near`), `12800→2c_near` (N2), `50→c_e=2·9^d`, `2500ℓ²M⁻²→(2S_d+1)M_u⁻²` (`sum_tail_tail`), `180000(log W)³→8(2ℓ*+3)^d c_e²` (F1), `625000000→2c_e³(2S_d+1)` (F2), `404` kept, `card_Z2→card_Zd`, `(2R+1)²→(2R+1)^d` | counts below | — |
| 2 | sums | `Σ_{b'}‖SB b b'‖=1` (`sum_norm_SB_row`, `L≥3`); every summand of the near/far cut bounds depends on `b` only, or is `‖SB‖·(…)` with `SB≠0 ⇒ |b-b'|_∞≤1` (copied `SB_support`) | `Σ_b 1(|c-b|≤R) ≤ (2R+1)^d` (`e10a`, `R≥0`) | exact |
| 3 | near count | `Σ_b[1(|a₀-b|≤ℓ**)+1(|a₁-b|≤ℓ**)] ≤ 2(2ℓ**+1)^d`, `2ℓ**+1=8(log P)²+1 ≤ 9(log P)²` | `log P ≥ 6d log W ≥ 72` | `(log P)² ≥ 5184 ≥ 1` |
| 4 | near tail | `x ≤ 4ℓ* ⇒ √x ≤ 2Y`, `T(x) ≥ M_u⁻²e^{-2Y}`, `M_u⁻⁴ ≤ e^{4Y}T(x)²`; `W^dM_u⁻⁵=(1-u)⁻¹M_u⁻⁴` (`e1_rpow`) | `M_u>0` | exact |
| 5 | near long edge (no `J≤W`) | `W^dL^d·2c_nearΛ⁶JP⁻¹ = 2c_nearΛ⁶J W^{-5d}`; `M_u ≤ W^d` (`e2`) ⇒ `W^{-5d} ≤ W^{-9d/2} ≤ M_u^{-9/2}=M_u^{-1/2}M_u⁻⁴ ≤ M_u^{-1/2}e^{4Y}T²`; `J ≤ J³`, `(1-u)⁻¹ ≥ 1` | `W ≥ 1`, `J ≥ 1`, `0 ≤ u` | `W^{-5d}/W^{-9d/2}=W^{-d/2}` (a) `2^{-15}`, (b) `2^{-36}` |
| 6 | near rows | `N1=2·9^dΛ(log P)^{2d}e^{4Y}`, `N2=2c_nearΛ⁶e^{4Y}`, `c_near=32·3^{d+1}=2592` | `≤ lossE2dif` | table below |
| 7 | far counts | per cut four indicators, radius `ℓ*+1`, `(2(ℓ*+1)+1)^d=(2ℓ*+3)^d ≤ 3^d(1+log P)^{2d}`; cut₁, cut₂ share the centres `{a₀,a'₀,a₁,a'₁}` ⇒ 8 counts | `ℓ*≥8` (`log W≥4`), `2ℓ*+3≤3ℓ*`, `ℓ*≤(log W)²≤(log P)²` | `ℓ*=8` at `log W=4`: `19 ≤ 24` |
| 8 | far scale | `W^dM_u^{-3/2}=(1-u)⁻¹M_u^{-1/2}` (`e1_rpow`, `a=3/2`, `inv_rpow`); `J²≤J³` | `J ≥ 1` | exact |
| 9 | far conv | `Σ_bT(|A₁-b|)T(|b-A₂|) ≤ (2S_d+1)M_u⁻²T(|A₁-A₂|)`, `A=(M_u⁻¹)²`, `w=W^{-D}`, `wL^d ≤ A` (`floor_A`), `1≤d`; `W^dM_u⁻²=(1-u)⁻¹M_u⁻¹ ≤ (1-u)⁻¹M_u^{-1/2}` (`1≤M_u`) | `wL^d ≤ A` | script `chain.py` below |
| 10 | far rows | `F1=8(2ℓ*+3)^dc_e²Λ³S³`, `F2=2c_e³(2S_d+1)Λ³S³`; `S³ ≤ 404e^{6Y}`; `2S_d+1 ≤ 3(1600d⁴)^d` (`1+1536d⁴≤1600d⁴`) | `≤ lossE2dif` | table below |
| 11 | constant `κ_dif=729^d` | `c_e³=8·729^d` ⇒ `F2 ≤ 48·404·729^d(1600d⁴)^dΛ³e^{6Y}`; `lossE2dif ≥ 10¹²·125·(1600d⁴)^d·729^d(1+log P)^{2d}Λ⁶e^{8Y}` (`(1+log W)³≥125`, `K₀²,(1+log(L^dW^{2d}))⁴≥1`) | `48·404 ≤ 10¹²·125` | factor `6.45e9` (all `d`) |
| 12 | label bookkeeping | `label.py` below: `cut₁` = pattern at `(σ₀,σ₁;a₀,a₁,a'₀,a'₁)`, `cut₂` at `(σ₁,σ₀;a₁,a₀,a'₁,a'₀)`; `h1,h2` from the range premise at `i=0,1` (swapped for `cut₂`); `hB` from `SB` support; `hd` for `cut₂` via `zdistInf(a₁-a₀)=zdistInf(a₀-a₁)` (`zd_neg`) | — | — |
| 13 | floor | `(L^dW^{6d})² ≤ W^D` is a premise of `E2HypDif` (merged `inst_a/_b`) | exact integers below | (a) `2^378≤2^380`, (b) `2^1007.55≤2^1008` |

Rows against `lossE2dif` (log10(loss/row), `Λ=K₀=1`, `κ=729^d`; "chain" = the proof's intermediate bounds `S³≤404e^{6Y}`, `(2ℓ*+3)^d≤3^d(1+log P)^{2d}`, `2S_d+1≤3(1600d⁴)^d`, `e^{4Y},e^{6Y}≤e^{8Y}`):
```
$ python3 rows.py
d=3: c_e=1458 c_near=2592 S_d=1925924135219713 2S_d+1<=3(1600d^4)^d: 3851848270439427 <= 6530347008000000 ; 48*404=19392 <= 1e12 ; kappa_dif=729^d=(c_e/2)^3=387420489
worst     log10 lossE2dif=65.0 | exact rows log10(loss/row): N1=45.6 N2=56.3 F1=43.9 F2=29.6 | chain rows: N1=40.7 N2=51.4 F1=32.6 F2=26.9
(a)       log10 lossE2dif=72.9 | exact rows log10(loss/row): N1=49.7 N2=61.8 F1=47.2 F2=33.8 | chain rows: N1=42.2 N2=54.4 F1=34.1 F2=29.9
(b)       log10 lossE2dif=92.3 | exact rows log10(loss/row): N1=59.5 N2=74.2 F1=54.5 F2=42.8 | chain rows: N1=45.2 N2=59.9 F1=37.1 F2=35.4
scan d=3..60, L in {3,1e3,1e9}, log W in [4,1e5], Lam in {1,10,1e6}: min log10(loss/row) per row:
   chainF1 (32.56, (3, 3, 4.0, 1))   chainF2 (26.91, (3, 3, 4.0, 1))   chainN1 (40.67, (3, 3, 4.0, 1))   chainN2 (51.41, (3, 3, 4.0, 1))
   exactF1 (43.91, (3, 3, 4.0, 1))   exactF2 (29.6, (3, 3, 4.0, 1))   exactN1 (45.61, (3, 3, 4.0, 1))   exactN2 (56.32, (3, 3, 4.0, 1))
```
(worst case `d=3, L=3, log W=4`; minimum is the chain row `F2` at 26.91; the exact-row minimum `29.6` equals T2171's. `κ_dif` needs no enlargement.)

### (ii) Concrete nondegenerate instance
```
$ python3 tok.py     # RBM2D LemDecCalEdif.lean:1002-1691 @c9a24cf, tokens/lines
Z2 60/42; zdist2 44/44; (W : R) ^ 2 25/25; scaleM 46/45; etaT 31/30; ellT 67/53; ellStar 19/19; tailT 24/24; jStarMat 26/23; L^2*W^12 14/14; 81 8/8; 162 18/18; 200 7/7; 12800 15/15; 50 7/7; 2500 4/4; 180000 8/8; 625000000 7/6; 404 7/7; convTailT 1/1; card_Z2 2/2; (2R+1)^2 1/1; rho 48/36; J<=W (hJ) 5/5
$ awk 'NR>=1002&&NR<=1691 && /jStarMat L W E D u M ≤ W|hJ\b/' RBM2D/Path/LemDecCalEdif.lean   # the only use of J ≤ W
1167:   have hJ : jStarMat L W E D u M ≤ W := h.2.2.2.2.2.2.2.2.2.2.2.2.1
$ python3 inst.py
(a) sz0 n=1: d=3 L=8 W=1024 D=38  floor (L^d W^6d)^2<=W^D exact-int: True ; log W=6.931>=4: True ; l*=18.249 ; 4l*=72.996
   |a0-a1|=1 -> near branch (ind=1); |a_i-a_i'|=[0, 0] <= l*: True
   lossE2dif=8.796e+72  T(x)=3.191e-19  R=loss*[ind+(W^d)^-1/2]T^2 = 8.956e+35 > 0: True
(b) szCL n=0: d=3 L=15925248 W=16777216 D=42  floor (L^d W^6d)^2<=W^D exact-int: True ; log W=16.636>=4: True ; l*=67.851 ; 4l*=271.403
   |a0-a1|=300 -> far branch (ind=0); |a_i-a_i'|=[1, 0] <= l*: True
   lossE2dif=1.823e+92  T(x)=1.347e-51  R=loss*[ind+(W^d)^-1/2]T^2 = 4.815e-21 > 0: True
M=0: |L6| = W^{-5d} iff the six labels (a0,a1,b',a'1,a'0,b) [cut1] / (a1,a0,b',a'0,a'1,b) [cut2] coincide, else 0;
   ticket instance (a): a0!=a1 -> every loop = 0 -> ||STeeM|| = 0 ; (b): a0!=a1 -> 0.
alternative nonzero near instance a=a'=(0,0) at (a): ||STeeM|| = 2*SB00*W^{-4d} = 1.505e-36 <= R = 6.617e+36 (R/lhs=4.398e+72); unloss R0=7.523e-37, lhs/R0=2.000e+00
$ python3 cons.py
Step5Pins.lean:178-186 third-conjunct RHS (u:=q.1.1.1, a:=q.1.1.2.2, Jst n u D:=J) == LemDecCalE_dif RHS after the loss: True
pin range clause q.1.2.2 i - q.2 i present: True | LemDecCalE_dif has (a i - a' i): True
check file target type: def lemDecCalE_difTarget : Prop := ∀ d : ℕ, LemDecCalE_dif d
$ git diff --stat 7d9f111 HEAD -- RBM3D/Path/LemDecCalEdif.lean RBM3D/Induction/Step5Pins.lean | wc -l
0
$ python3 label.py
cut1 matches cut_near/cut_far pattern with (sg0,sg1):=(sg0,sg1), A1=a0 A2=a1 A1'=a'0 A2'=a'1 : True
   h1 pairs (A1,A1') -> range index 0 = 0 ; h2 pairs (A2,A2') -> range index 1 = 1 ; hd distance |A1-A2| = |a0-a1| (zdist symmetric for cut2) ; four indicator centres {A1,A1',A2,A2'} = ["a'0", "a'1", 'a0', 'a1']
cut2 matches cut_near/cut_far pattern with (sg0,sg1):=(sg1,sg0), A1=a1 A2=a0 A1'=a'1 A2'=a'0 : True
   h1 pairs (A1,A1') -> range index 1 = 1 ; h2 pairs (A2,A2') -> range index 0 = 0 ; hd distance |A1-A2| = |a1-a0| (zdist symmetric for cut2) ; four indicator centres {A1,A1',A2,A2'} = ["a'0", "a'1", 'a0', 'a1']
$ python3 matrix.py 7 2 1   # d=3 L=7 W=2 N=2744 random Hermitian M (block variances SB/W^d), Lambda from M, J_e from (e7) only; all 4 sigma, a0=0, a1 at every distance, a'=a (l*=0.577)
d=3 L=7 W=2 N=2744 u=0.3 lam=0.8 D=53 Mu=5.60 l*=0.577 4l*=2.308 diam=3 Lambda=1.964 J_e=1.000 loss=7.765e+52
near branch: 28 (sigma,a,a') tuples: max lhs/(R without loss)=2.639e-02 ; max lhs/(lossE2dif R)=3.399e-55
far  branch: 12 (sigma,a,a') tuples: max lhs/(R without loss)=1.241e-04 ; max lhs/(lossE2dif R)=1.598e-57
$ python3 matrix.py 5 3 2   # L=5 W=3 N=3375: l*=1.152, a'_i in the radius-1 cube around a_i (random), near only (4l*=4.61 > diam 2)
d=3 L=5 W=3 N=3375 u=0.3 lam=0.8 D=45 Mu=18.90 l*=1.152 4l*=4.606 diam=2 Lambda=5.993 J_e=1.000 loss=1.295e+58
near branch: 56 (sigma,a,a') tuples: max lhs/(R without loss)=8.623e-04 ; max lhs/(lossE2dif R)=6.657e-62
far  branch: no tuple on this torus (4l*=4.61 vs diam 2)
$ python3 chain.py   # scalar chain (cut bounds -> pin) with exact lattice sums on Z_L^3, mpmath 60 digits, random (W,u,lam,D,Lambda,J<=W,L): near L<=20 (150 draws), far L in [90,100], log W in [4,4.8] (60 draws; far needs L/2 > 4l*)
near samples 150 max B/(loss*R) = 9.024e-61 ; max B/R (loss needed) = 5.904e+21 ; stage inequalities all hold: True ; max conv/(bound) = 0.000e+00
far samples 60 max B/(loss*R) = 3.761e-45 ; max B/R (loss needed) = 3.705e+34 ; stage inequalities all hold: True ; max conv/(bound) = 3.613e-12
```
(`chain.py` stage inequalities: `M⁻⁴≤e^{4Y}T²`, the long-edge chain, `(2R+1)^d` bounds, `Σ_bTT ≤ (2S_d+1)M_u⁻²T`, `W^{-D}L^d ≤ (M_u⁻¹)²`. `matrix.py` uses `J_e` only: the full `J` needs `K`, not computable for random `M`; the tuples are structure tests with huge slack, not sharp constants.)

Instances (all premises of `lemDecCalE_dif` hold at once; the `E2HypDif` premises are the merged `LemDecCalEdif_inst_a/_b`, T2171 (a) `zero.py`, `Λ=K₀=J=1`, `M=0`, `u=0`, `E=1/2`, floor exact integers above):
- (a) `sz0, n=1` (`L=8, W=1024, D=38`), `σ=(+,+)`, `a=a'=(0,e₁)`: `|a₀-a₁|_∞=1 ≤ 4ℓ*=72.996`, near, `R=8.956e35>0`; `‖STeeM‖=0` at `M=0` (all six loop labels cannot coincide). A nonzero near instance at the same data is `a=a'=(0,0)`: `‖STeeM‖=2·SB₀₀·W^{-4d}=1.505e-36 ≤ R=6.617e36`.
- (b) `szCL, n=0` (`L=2·24⁵, W=2^24, D=42`), `σ=(+,-)`, `a=(0,300e₁)`, `a'=(e₂,300e₁)`: `|a₀-a₁|=300>271.403`, far (indicator 0), `|a₀-a'₀|=1, |a₁-a'₁|=0 ≤ ℓ*=67.851`, `R=4.815e-21>0`; `‖STeeM‖=0` at `M=0` (`a₀≠a₁`).
- External-type hypotheses: none new; the `E2HypDif` loop clauses ← `STLmaxU` and the missing floor/`GijGEX`/`J≤W` of S5-09 are T2171's table, unchanged (below).

### Consumer check (§45 O2)
The pin `LemDecCalE_dif` is merged and unchanged (`git diff --stat 7d9f111 HEAD` on `Path/LemDecCalEdif.lean`, `Induction/Step5Pins.lean`: 0 lines); its right side equals `Step5Pins.lean:178-186` after the loss (`cons.py`: True), with `M := sz.seqHflow n u ω` (`STeeM_seqHflow`), `J := Jst n u D`. No new premise: the premise table of T2171 (a) stands (loop clauses ← `STLmaxU` `k=4,6`; floor missing; `GijGEX` missing; `J≤W` missing, unused by this ticket: the only RBM2D use is `near_far_small` `:1167`, replaced by row 5).

### Verdicts
- Target 1 `lemDecCalE_dif (d) : LemDecCalE_dif d` (every `σ`, `a`, `a'` in range): **PASS**. All rows close with `κ_dif=729^d` (min slack 26.91 log10 over `d=3..60`; `F2` is the tightest and needs `48·404 ≤ 10¹²·125`); the long-edge term closes without `J ≤ W` (row 5); the far case has the single pin term `(W^d|1-u|)^{-1/2}J³` (rows 8–10).
- Flag (not blocking): the ticket's instances (a), (b) have `‖STeeM‖=0` at `M=0`, so they exercise the hypotheses and `R>0` only; a nonzero left side is available at `a=a'=(0,0)` (above). `lossE2dif` carries `(1+log P)^{2d}` where the rows need only `(log P)^{2d}`/`(2ℓ*+3)^d`: slack as in the table.

## (b) Script output (stage 1b; times are the `date -u` lines below)

```
$ date -u
Mon Oct  5 06:48:28 UTC 2026
$ git log --oneline -3; git status --short; git diff --stat main...t/T2181
67118f1 T2181: drop an unused private helper from Path/LemDecCalEdif2
9c69578 T2181: Path/LemDecCalEdif2 lemDecCalE_dif (S5-07)
a52eb85 T2177: merge Universality/OU + Universality/EigenMeasurable
 RBM3D/Path/LemDecCalEdif2.lean | 1035 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1035 insertions(+)
$ git diff --stat 7d9f111 HEAD -- RBM3D/Path/LemDecCalEdif.lean | wc -l   # merged file unchanged
       0
$ lake build RBM3D.Path.LemDecCalEdif2 2>&1 | tail -1
Build completed successfully (3818 jobs).
$ lake env lean RBM3D/Path/LemDecCalEdif2.lean > fresh.out 2>&1; echo $?; wc -l < fresh.out   # fresh elaboration of the file: exit code, warning lines
exit 0
       0
$ lake env lean ax.lean   # import RBM3D.Path.LemDecCalEdif2; #print axioms RBM.Path.lemDecCalE_dif; #check @RBM.Path.lemDecCalE_dif
'RBM.Path.lemDecCalE_dif' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Path.lemDecCalE_dif : ∀ (d : ℕ), RBM.Path.LemDecCalE_dif d
$ lake env lean ty.lean   # example : ∀ d : ℕ, RBM.Path.LemDecCalE_dif d := RBM.Path.lemDecCalE_dif   (§29 (7))
RBM.Path.lemDecCalE_dif : ∀ (d : ℕ), RBM.Path.LemDecCalE_dif d
exit 0
$ registry pre-check, lake env lean pre.lean   # import RBM3D; import RBM3D.Path.LemDecCalEdif2; #assert_rbm_axioms
exit 0
axiom audit: 5335 theorems, 1886 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake build   # full, in the worktree (the root RBM3D.lean imports the new module only at the hub merge)
Build completed successfully (3978 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Path/LemDecCalEdif2.lean; grep -n "maxHeartbeats" RBM3D/Path/LemDecCalEdif2.lean | wc -l
0
       0
$ wc -l RBM3D/Path/LemDecCalEdif2.lean; grep -nE "^theorem|^example" RBM3D/Path/LemDecCalEdif2.lean
    1035
852:theorem lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d := by
944:example :
986:example :

$ target statement: sed -n 852p ; the merged pin sed -n 80,92p RBM3D/Path/LemDecCalEdif.lean
852:theorem lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d := by
def LemDecCalE_dif (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2HypDif sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (a i - a' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E u M σ a a'‖ ≤ lossE2dif d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ *
          ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
                4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
          STtailTD sz n u D a ^ 2)


$ J ≤ W: grep -nE "J ≤ W|hJW|hJ_le" ; the E2Hyp destructuring (sed -n 79,80p)
26:  `J ≤ W` (RBM2D `near_far_small` `:1164` uses it): `W^{-5d} ≤ M_u^
27:  `J ≤ J³`; the conjunct `J ≤ W` of `E2Hyp` is not used;
493:`J ≤ W`: `W^{-5d} ≤ M_u⁻⁵ ≤ M_u^{-1/2} M_u⁻⁴ ≤ M_u^{-1/2} e^{4Y} T
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -⟩ := h

$ python3 instdiff.py   # bodies of the two examples vs docs/tickets/checks/T2181-check.lean instNear, instFar
examples at lines [944, 986]
instNear check lines 10 mine lines 10 IDENTICAL
instFar check lines 11 mine lines 11 IDENTICAL
$ the two examples, statements (awk from `example :` to `:= by`)
example :
  let a : Fin 2 → Zd 3 (sz0.L 1) := ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]
  let R : ℝ := lossE2dif 3 (sz0.L 1) (sz0.W 1) 1 1 *
    ((1 - (0 : ℝ))⁻¹ *
      ((if ((zdistInf 3 (sz0.L 1) (a 0 - a 1) : ℕ) : ℝ) ≤
            4 * Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
        (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 : ℝ)) *
      STtailTD sz0 1 0 38 a ^ 2)
  0 < R ∧
    ‖STeeM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true] a a‖ ≤ R := by
example :
  let a : Fin 2 → Zd 3 (szCL.L 0) := ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 300]
  let a' : Fin 2 → Zd 3 (szCL.L 0) := ![(Pi.single 1 1 : Zd 3 (szCL.L 0)), Pi.single 0 300]
  let R : ℝ := lossE2dif 3 (szCL.L 0) (szCL.W 0) 1 1 *
    ((1 - (0 : ℝ))⁻¹ *
      ((if ((zdistInf 3 (szCL.L 0) (a 0 - a 1) : ℕ) : ℝ) ≤
            4 * Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
        (((szCL.W 0 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 : ℝ)) *
      STtailTD szCL 0 0 42 a ^ 2)
  0 < R ∧
    ‖STeeM szCL 0 (1 / 2) 0
        (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) ![true, false] a a'‖ ≤ R := by
$ python3 rows_lean.py   # slack of lossE2dif/Z >= 1e12 over each bound (preflight (a) rows N1, N2, F1, F2 are the unsimplified forms)
row bound (x Z)   lossE2dif/Z >= 1e12   log10 slack
  N1 <=      2 Z     slack factor 5.000e+11  (log10 11.70)
  N2 <=    192 Z     slack factor 5.208e+09  (log10 9.72)
  F1 <=  12928 Z     slack factor 7.735e+07  (log10 7.89)
  F2 <=  19392 Z     slack factor 5.157e+07  (log10 7.71)
  F1+F2 <= 32320 Z     slack factor 3.094e+07  (log10 7.49)
8*4*404 = 12928  (3232*4 = 12928): 12928
$ ports from this repo (copied private helpers): source file:line (grep -n) -> new name
RBM3D/Path/LemDecCalEdif.lean:489 lemDecCalEdif_W_pos
RBM3D/Path/LemDecCalEdif.lean:492 lemDecCalEdif_L_pos
RBM3D/Path/LemDecCalEdif.lean:502 lemDecCalEdif_basic
RBM3D/Path/LemDecCalEdif.lean:508 lemDecCalEdif_zd_neg
RBM3D/Path/LemDecCalEdif.lean:514 lemDecCalEdif_zd_comm
RBM3D/Path/LemDecCalEdif.lean:593 lemDecCalEdif_logP_ge
RBM3D/Path/LemDecCalEdif.lean:616 lemDecCalEdif_logP_ge72
RBM3D/Path/LemDecCalEdif.lean:1560 lemDecCalEdif_inst_dist
RBM3D/Path/LemDecCalEdif.lean:1576 lemDecCalEdif_inst_ell
RBM3D/Path/LemDecCalE.lean:770 lemDecCalE_SB_support
$ RBM2D (read-only), cd ~/Lean_proof/RBM3D: git -C ../RBM2D --no-optional-locks log -1 --format=%h; diff --stat c9a24cf HEAD -- RBM2D/Path/LemDecCalEdif.lean
9e0f275
 RBM2D/Path/LemDecCalEdif.lean | 68 ++++++++++++-------------------------------
 1 file changed, 18 insertions(+), 50 deletions(-)
$ RBM2D sources at c9a24cf (grep -n): EE_le sum_SB_le count_le S3_le loss_ge tail_lower near_far_small near_sum near_const near_case far_sum far_const far_case lemDecCalE_dif
1010:private theorem EE_le 1033:private theorem sum_SB_le 1048:private theorem count_le 1072:private theorem S3_le 1086:private theorem loss_ge 1124:private theorem tail_lower 1164:private theorem near_far_small 1197:private theorem near_sum 1268:private theorem near_const 1306:private theorem near_case 1378:private theorem far_sum 1482:private theorem far_const 1538:private theorem far_case 1632:theorem lemDecCalE_dif : 
$ name clash on the main worktree (merged declarations): lemDecCalE_dif / prefixes LemDecCalEdif2_, lemDecCalEdif2_
decls named lemDecCalE_dif:        0
decls with the prefixes:        0
file RBM3D/Path/LemDecCalEdif2.lean on main worktree: ls: RBM3D/Path/LemDecCalEdif2.lean: No such file or directory
public decls in the new file: 1; private decls: 29; private not prefixed lemDecCalEdif2_: 0
$ merged upstream names used by the new file (grep -oE | sort | uniq -c)
card_Zd x1; LemDecCalE_e10a x1; LemDecCalE_e2 x6; LemDecCalE_floor_A x1; LemDecCalE_sum_tail_tail x3; LemDecCalEdif_cut_far x3; LemDecCalEdif_cut_near x3; LemDecCalEdif_inst_a x2; LemDecCalEdif_inst_b x2; LemDecCalEdif_STeeM_le x3; sum_norm_SB_row x1; szCL_log_W x1; szCL_one_le_log_W x1; tailTD_nonneg x4; 
uses of LemDecCalE_e1 / LemDecCalE_e1_rpow / LemDecCalE_tailT_anti (named by the ticket): 0
$ lake env lean chk_names.lean   # 43 #check lines: Mathlib and merged names used
exit 0 ; error lines: 0
```

Narrative (stage 1b):
1. Deliverable: `RBM3D/Path/LemDecCalEdif2.lean` (1035 lines, commits 9c69578 and 67118f1 on `t/T2181`): one public declaration `lemDecCalE_dif (d : ℕ) : LemDecCalE_dif d`, 29 private helpers (prefix `lemDecCalEdif2_`), two `example`s. Sections: copied helpers, sums over `b, b'`, scalar facts and the constant rows, near, far, the theorem, instances.
2. Route as the ticket (i)-(vi): `LemDecCalEdif_STeeM_le`, then `cut_near` / `cut_far` for both cuts (the label patterns of the two cuts of `STeeM_le` match the cut lemmas' arguments, `(σ₀,σ₁;a₀,a₁,a'₀,a'₁)` and `(σ₁,σ₀;a₁,a₀,a'₁,a'₀)`), `sum_norm_SB_row` with the copied `SB_support`, counts by `LemDecCalE_e10a`, `#Zd = L^d` by `card_Zd`. `σ` is never specialised.
3. Near: `W^d M_u⁻⁵ = (1-u)⁻¹ M_u⁻⁴` (from `W^d m = (1-u)⁻¹`, `m = M_u⁻¹`), `M_u⁻⁴ ≤ e^{4Y} T²` for `x ≤ 4ℓ*` (`√(4ℓ*) ≤ 2Y`, `Y² = ℓ*`), rows `N1 ≤ 2Z`, `N2 ≤ 192 Z`.
4. Near long edge without `J ≤ W`: `W^d L^d P⁻¹ = (W^d)⁻⁵ ≤ m⁵ ≤ m^{1/2} m⁴ ≤ m^{1/2} e^{4Y} T²` (`(W^d)⁻¹ ≤ m` from `M_u ≤ W^d`, `LemDecCalE_e2`; `m ≤ 1`), then `J ≤ J³`, `1 ≤ (1-u)⁻¹`. The file names no `J ≤ W` hypothesis (grep above: 3 docstring hits; `E2Hyp` is destructured with a trailing `-`).
5. Far: the four indicators per cut are counted by `count_le` at radius `ℓ*+1`, `(2ℓ*+3)^d ≤ 3^d (1+log P)^{2d}`; `W^d m^{3/2} = (1-u)⁻¹ m^{1/2}` by `Real.rpow_add`; `J² ≤ J³`. The tail product is `LemDecCalE_sum_tail_tail` with `A = m²`, `w = W^{-D}`, `w L^d ≤ A` from `LemDecCalE_floor_A`; `W^d m² = (1-u)⁻¹ m ≤ (1-u)⁻¹ m^{1/2}`. For `cut₂` the tails `T(|a₁-a₀|)`, `T(|a₁-b|)`, `T(|b-a₀|)` are rewritten by the symmetry of `zdistInf`; `hd` for `cut₂` likewise. Rows `F1 + F2 ≤ 32320 Z`.
6. `κ_dif = 729^d` suffices, with the slack of the table above (`F1 + F2` is the tightest of the chain, factor 3.1e7 below `lossE2dif/Z ≥ 10^12`). `lossE2dif ≥ 10^12 Z` uses only `K₀², (1+log(L^dW^{2d}))⁴, (1+log W)³ ≥ 1`; the `(1+log W)³ ≥ 125` of (a) row 11 is not needed.
7. Differences from the ticket's suggested route (no pin change): `LemDecCalE_e1`, `_e1_rpow`, `_tailT_anti` are not used (grep: 0); the two identities are `field_simp` and `Real.rpow_add` on `W^d m = (1-u)⁻¹`. The merged `Path/LemDecCalEdif.lean` is unchanged (diff above: 0 lines); no premise is added.
8. Instances: both example bodies are identical to `instNear` / `instFar` of the check file (script diff above). `0 < R` is proved by the private `lemDecCalEdif2_R_pos` (indicator `≥ 0`, either branch); the branch itself is proved inside each example (`hbr`): (a) `|a₀-a₁|_∞ = 1 ≤ 4(log W)^{3/2}`, near; (b) `|a₀-a₁|_∞ = 300 > 4(log W)^{3/2}` by `lemDecCalEdif2_inst_ell`, far. Range premises: (a) `a = a'`; (b) `|a₀-a'₀|_∞ = 1 ≤ ℓ*` by `szCL_one_le_log_W`, `|a₁-a'₁|_∞ = 0`. The only premise is the merged `LemDecCalEdif_inst_a` / `_inst_b`.
9. No `(a′)` section: I found no error in (a).

## (c) Verified names (one `#check` script over the 43 names below: exit 0, 0 error lines)
Real.rpow_le_rpow_of_exponent_ge, Real.rpow_le_rpow_of_exponent_le, Real.rpow_natCast, Real.rpow_add, Real.rpow_one,
Real.rpow_nonneg, Real.rpow_pos_of_pos, Real.rpow_mul, Real.sqrt_le_iff, Real.sqrt_lt', Real.exp_one_lt_d9,
Real.log_two_lt_d9, Real.log_two_gt_d9, Real.exp_nat_mul, Real.exp_le_exp, Real.log_nonneg, Real.log_mul,
Real.log_pow, one_le_inv₀, inv_le_one_of_one_le₀, inv_anti₀, le_self_pow₀, pow_le_pow_left₀, pow_le_pow_right₀,
one_le_pow₀, Finset.sum_boole, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
nsmul_eq_mul, abs_of_pos, add_pos_of_nonneg_of_pos, one_le_mul_of_one_le_of_one_le, RBM.sum_norm_SB_row, RBM.SB_apply,
RBM.Gauss.zdistInf_le_zdistD, RBM.card_Zd, RBM.tailTD_nonneg, RBM.Path.LemDecCalE_e2, RBM.Path.LemDecCalE_e10a,
RBM.Path.LemDecCalE_sum_tail_tail, RBM.Path.LemDecCalE_floor_A
Absent: `RBM.zdistInf_le_zdistD` (first run: `Unknown identifier`); the name is `RBM.Gauss.zdistInf_le_zdistD`. Deprecated in this toolchain (warnings on the first compile of the main theorem with `rw [if_pos hn]` / `rw [if_neg hn]`, replaced by `simp only [hn, ↓reduceIte]`): `if_pos`, `if_neg`.

## (d) Open issues and paper-delta candidates
- None blocking: statement, instances, axioms, registry pre-check, full build all pass above.
- For S5-09 the premise table of T2171 stands (ticket "Consumers"): `E2HypDif`'s loop clauses from `STLmaxU`; the floor `(L^dW^{6d})² ≤ W^D`, `GijGEX` (T2164 M2) and `J ≤ W` (T2164 M3) are inputs decided at S5-09 (§53). This proof does not consume the `J ≤ W` conjunct; it remains a conjunct of the merged `E2Hyp` that `E2HypDif` inherits.
- The examples exercise the hypotheses and `R > 0` at the T2171 data (`M = 0`); preflight (a) flags that the left side is `0` there for `a₀ ≠ a₁` (not compiled here).
- Paper-delta candidates, all proof-level (the statement is T2171's; nothing beyond T2171a-e at statement level):
  - T2181a: the conjunct `J ≤ W` of `E2Hyp` (T2164 M3) is unused: RBM2D `near_far_small` (`:1164`) uses it; here `W^d L^d P⁻¹ = W^{-5d} ≤ M_u^{-1/2} M_u⁻⁴`.
  - T2181b: single far term `(1-u)⁻¹ M_u^{-1/2} J³` where RBM2D `far_case` (`:1538`) has `η_u⁻¹ ρ³ M_u^{-1/2} J² + η_v⁻¹ M_v⁻¹ J³` (`J² ≤ J³`, `M_u⁻¹ ≤ M_u^{-1/2}`).
  - T2181c: RBM2D `convTailT` (`2500 ℓ_v² M_v⁻²`, `:1440`) is replaced by `LemDecCalE_sum_tail_tail` (`(2 S_d + 1) M_u⁻²`, `S_d = (1 + 1536 d⁴)^d`); its constant is in row F2 under `κ_dif = 729^d`.
