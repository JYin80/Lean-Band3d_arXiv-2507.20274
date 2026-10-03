Prover model: claude-sonnet-5-5

## (a) Math preflight — 2026-10-03 06:00:59 UTC (`date -u`: Sat Oct  3 06:00:59 UTC 2026)

Target: `RBM.Green.highProb_norm_rowSum_sq_le` (RBM2D `Green/RowIndep.lean:1330` at `c9a24cf`; the file has 1759 lines there, 1298 at HEAD `9e0f275`; the ticket pins `c9a24cf`). Mathematics: with `S = ∑_{k≠i} H_{ik} C_k`, `V = u ∑_{k≠i} S_{ik}|C_k|²` (`rowSum`, `rowVarSum`), `C` reading only the off-row coordinates `{(k,l,b): k≠i, l≠i}`, for every `τ>0`, `P(∃q: |S_q|² > N^{2τ} V_q) ≤ N^{-D}` eventually, `N = sz.size n = (W L)^d`, uniformly over an index set `U n` with `#U n ≤ N^Ccard`. Hypotheses: `0 ≤ u`, `Tendsto sz.size atTop atTop`, `hcard`, `hCmeas`, off-row `hC`, `0 < τ`.
Proof route (RBM2D:1317-1430): rows `{(i,k,b),(k,i,b)}` are independent of off-row coordinates (product measure, `Xentry` oriented by `idxKey`); given the off-row block `S` is a centred circular complex Gaussian of variance `V`, so `E|S/√V|^{2p} = p! ≤ 2(2p-1)!!`; Markov + union over `U n` (`stochDomAt_of_momentDomAt`, `RBM3D/Gauss/DominationAt.lean:75-99`); degenerate fibres `V=0` are null.

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| independence structure | σ-algebras `σ(ω_c : c ∈ rowSet i)` vs `σ(ω_c : c ∈ offRowCoord i)`, disjoint coordinate sets of the one product measure `seqP` | `C`, and the minor `G^{(i)}`, read only `offRowCoord i` | dimension-free (index-set argument; no `d`) |
| row Gaussian law | `Re,Im H_{ik}` ~ `N(0, u·svarF/2)` independent, `k≠i` (`gvarF` off-diag = `svarF/2`, `FineModel.lean:89`) | `E|S|² = V` | exact |
| variance profile | `svarF d L W g i j = W^{-d}·SBR(blk i − blk j)`, `g = sz.lam n` (`FineModel.lean:47`); `∑_{k≠x} svarF = 1 − W^{-d}(1+2dg²)^{-1}` | `sum_sbKernelR` (`Block.lean:93`, `3 ≤ L`) | script: 0.95 at `d=3,W=2,g=1/2` = formula |
| `W^d` (row length / block size) | enters only via `svarF = W^{-d}·SBR`; the bound is relative to `V`, no `W^d` appears in exponent or constants | none | n/a |
| `N = (W L)^d` | `size n = (W n·L n)^d` = `#Idx d L W` (`Sizes.card_Idx`, `Sizes.lean:160`); the scale of `StochDomAt/HighProbAt` | `Tendsto sz.size atTop atTop` (hypothesis `hsize`) | `sz0`: N grows (`sz0_tendsto`) |
| `Ccard` | any real; `hcard: #U n ≤ N^Ccard`; row LDE: `U = Σ i, {a // a≠i}`, `#U = N(N−1) ≤ N²` | `Ccard = 2` | `N(N−1) ≤ N²` (script) |
| `τ`, `D` | `τ>0`, `D>0` arbitrary | `p ≥ (D+Ccard+1)/τ` (`DominationAt.lean:80`) | `τp−(D+Ccard) ≥ 1` (so `N^{-(D+Ccard)}·C_p·N^{-(τp−D−Ccard)}`-type tail closes once `C_p ≤ N^{τp−D−Ccard}`); `τ=.1,D=5,Ccard=2`: `p=80`, slack `1.00` |
| moment constant | `E|S/√V|^{2p} = p! ≤ (2p−1)!! ≤ 2(2p−1)!!` (Lean uses `C_p = 2·dfac p + 1`) | `p! ≤ 2(2p−1)!!` | script p=1..4: 1,2,6,24 vs 2,6,30,210 |
| `u` | `0 ≤ u` | `rowVarSum ≥ 0` | `u=1` |
| `d`-dependent changed items vs RBM2D | (1) `svar L W` (fixed five-point profile) → `svarF d L W (sz.lam n)`; (2) `Z2` → `Zd d` (card by `Sizes.card_Idx`); (3) `1/5` (below); (4) `d : Sizes` → `sz : Sizes d`, `W²`→`W^d`, `Idx`→`Idx d`. **No exponent changes**: `Ccard`, `τ`, `D`, `p`, `N^{2τ}` are the same as in RBM2D. |
| `d=2` token `Z2` ×2 (portmap P.1 row 59) | RBM2D:1135 `simp [Idx, Z2, Sizes.size, ZMod.card, sq]` (proof of `card_LdeIdx_le`), RBM2D:1422 (docstring `Idx 3 1 = Z2 3`) | replaced by `Sizes.card_Idx`; docstring dropped | forced by R2/R3 |
| `d=2` token `zdist2` | no match in `RBM2D/Green/RowIndep.lean@c9a24cf` (grep for `Z2\|zdist2` returns only the two `Z2` lines); the portmap's second token is not present in this file | none | none |
| `d=2` token `1/5` ×1 (portmap) | RBM2D:1581,1586,1603,1612, only in the private `Checks` section (lines 1425-1759): the row of `x=(0,0)` at `L=3,W=1` has 5 sites of weight `1/5` (`= 1/(1+2d)` at `g=1`), off-diagonal sum `4/5`. It is a **d=2 neighbour count `2d+1`**, not an exponent and not in the key statement (all `private`). | `d≥3`: weight `(1+2dg²)^{-1}`, `g²` times it on `2d` neighbours; at `d=3,g=1`: `1/7`, off-diag `6/7` (script) | replaced, forced by R2/R3 + `svarF` carrying `g`; checks are private, may be redone at `sz0` or dropped |
| `RBM2D` statement change (residual) | `svar (d.L n) (d.W n) i k` → `svarF d (sz.L n) (sz.W n) (sz.lam n) i k` in `rowVarSum`; `hsize : Tendsto sz.size atTop atTop` (ℕ-valued, as `tendsto_sz0_size`) | MD layer `svarF` carries `g` (`FineModel.lean:47`) | report as paper-delta candidate `T2038a` if not already signed (FineModel's `lam` is merged) |

### (ii) Concrete instance, `d=3, W=2, L=3` (Monte Carlo, 10⁴ samples) and the sequence `sz0`
Fixed-size sanity of the probabilistic content (the theorem itself is asymptotic, so `hsize` is checked on `sz0` below). `N=216`, `g=1/2`, `u=1`, Hermitian `H` with `E|H_{xy}|²=svarF`, row support 56 sites (7 blocks × 2³). Case (a): `C≡1`, all 216 rows, 10⁴ samples = 2 160 000 pair-draws; case (b): `C_k = [(H^{(0)}−z)^{-1}]_{k1}`, `z=0.5+0.1i`, row 0 (off-row coefficients), 10⁴ samples. `R = |S|²/V` should be Exp(1).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/mc.py` (numpy only, Python, no Lean); relevant verbatim output:
```
N= 216 rowsum S= 1.0 1.0 offdiag rowsum= 0.9500000000000001 expected 1-W^-d a= 0.95
distinct row-support sizes: [np.int64(56)]
case a samples 2160000 time 7.9
case (a) C=1, all 216 rows mean R=1.0004 (theory 1) KS distance to Exp(1) D=0.0004 (n=2160000, 5% crit 0.0009)
  p=1 E R^p=1.000  p!=1  2(2p-1)!!=2
  p=2 E R^p=2.004  p!=2  2(2p-1)!!=6
  p=3 E R^p=6.025  p!=6  2(2p-1)!!=30
  p=4 E R^p=24.211  p!=24  2(2p-1)!!=210
  P(R>1)=3.680e-01  exp(-1)=3.679e-01
  P(R>3)=4.999e-02  exp(-3)=4.979e-02
  P(R>5)=6.749e-03  exp(-5)=6.738e-03
  P(R>8)=3.463e-04  exp(-8)=3.355e-04
  P(R>10)=5.139e-05  exp(-10)=4.540e-05
case b time 18.5
case (b) C_k=G^(0)_{k1}(z=0.5+0.1i), row 0 mean R=1.0052 (theory 1) KS distance to Exp(1) D=0.0076 (n=10000, 5% crit 0.0136)
  p=1 E R^p=1.005  p!=1  2(2p-1)!!=2
  p=2 E R^p=2.006  p!=2  2(2p-1)!!=6
  p=3 E R^p=5.984  p!=6  2(2p-1)!!=30
  p=4 E R^p=23.811  p!=24  2(2p-1)!!=210
  P(R>1)=3.708e-01  exp(-1)=3.679e-01
  P(R>3)=5.010e-02  exp(-3)=4.979e-02
  P(R>5)=6.400e-03  exp(-5)=6.738e-03
  P(R>8)=4.000e-04  exp(-8)=3.355e-04
  P(R>10)=0.000e+00  exp(-10)=4.540e-05
card LdeIdx=N(N-1)= 46440  N^2= 46656
tau=0.10 N^{2tau}=2.93  MC per-pair P(R>N^{2tau}) (2160000 pair-draws)=5.4e-02  exact-tail bound N^2 exp(-N^2tau)=1.00e+00  largest D with bound<=N^-D: -1.45
tau=0.25 N^{2tau}=14.70  MC per-pair P(R>N^{2tau}) (2160000 pair-draws)=9.3e-07  exact-tail bound N^2 exp(-N^2tau)=1.93e-02  largest D with bound<=N^-D: 0.73
tau=0.50 N^{2tau}=216.00  MC per-pair P(R>N^{2tau}) (2160000 pair-draws)=0.0e+00  exact-tail bound N^2 exp(-N^2tau)=7.27e-90  largest D with bound<=N^-D: 38.18
max R observed 16.871677386118442 9.974322408048256
d=2 L=3 W=1 g=1: support 5, weight 0.200000, off-diag sum 0.800000
d=3 L=3 W=1 g=1: support 7, weight 0.142857, off-diag sum 0.857143
```
Hypothesis check on the admissible sequence `sz0` (`RBM3D/Defs/Sizes.lean:259`, `L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{-6}`, `d=3`), command `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/inst.py`:
```
n=0 L=4 W=32 lam=1.562e-02 N=2097152 card=4398044413952 <= N^2: True  Ccard=2  sum_k!=x svarF=0.999969527060
n=1 L=8 W=1024 lam=2.441e-04 N=549755813888 card=302231454903107537862656 <= N^2: True  Ccard=2  sum_k!=x svarF=0.999999999069
n=2 L=12 W=7776 lam=2.143e-05 N=812479653347328 card=660123187103393462475351392256 <= N^2: True  Ccard=2  sum_k!=x svarF=0.999999999998
n=3 L=16 W=32768 lam=3.815e-06 N=144115188075855872 card=20769187434139310370006797241024512 <= N^2: True  Ccard=2  sum_k!=x svarF=1.000000000000
tau=0.1 D=5.0 Ccard=2.0: p=80, tau*p-(D+Ccard)=1.00 >= 1 (slack), need C_p=2*(2p-1)!!+1 <= N^ex eventually
1 True
2 True
3 True
4 True
d=3,g=1,L=3,W=1: sites in support of row x = 7 weight 1/7 each; off-diag sum 6/7 (d=2: 1/5, 4/5)
```
All hypotheses hold at once for `sz0`, `u=1`, `U n = Σ i, {a // a≠i}`, `Ccard=2`, `row n q = q.1`, `C n q ω k = 1` (measurable, off-row-determined), `τ=1/10`; `N` is nondegenerate (`N ≥ 2097152`, `W ≥ 32`, `lam ≤ 1/64`). External hypotheses: none (no `Step2LocalPT`-type pin; the MD lemmas `stochDomAt_of_momentDomAt`, `FineModel`, `LinearForm`, `Markov/Stop/Azuma` exist merged), so no limit computation beyond `sz0_tendsto`.
Reading of the MC: `R` matches Exp(1) (KS distance 0.0004 < crit 0.0009 in (a); 0.0076 < 0.0136 in (b)); `E R^p ≈ p!` ≤ `2(2p−1)!!`; the per-pair tail `P(R>N^{2τ})` is 5.4e-2 at `τ=.1` (not yet high-probability at fixed `N=216`, as expected for an eventual statement), 9.3e-7 at `τ=.25`, 0 at `τ=.5` (`exact-tail bound N²e^{-N^{2τ}} = 7.3e-90`, `D ≤ 38`).

### Verdict
- `highProb_norm_rowSum_sq_le` (and the chain `stochDom_rowSum_general` → `stochDomAt_of_momentDomAt`): **PASS** — hypotheses jointly satisfiable at `sz0`; exponents close with `Ccard=2`, `p ≥ (D+3)/τ`; no exponent changes from RBM2D; all `d=2` tokens accounted for (`Z2` ×2 replaced via `Sizes.card_Idx`; `1/5` = `1/(2d+1)` neighbour count in private checks, replaced by `(1+2dg²)^{-1}`; `zdist2` absent in this file).

## (a′) Preflight corrections — Sat Oct  3 06:25:09 UTC 2026
Line references of (a) that were off, checked by `grep -n` in the worktree: `stochDomAt_of_momentDomAt` is `DominationAt.lean:75`, its choice of `p` (`exists_nat_ge ((D + Ccard + 1) / τ)`) is `DominationAt.lean:85` (not :80); `SizesInst.sz0` is `Sizes.lean:260` (not :259). No verdict changes. In (a) the `d=2` token `1/5` is at RBM2D `RowIndep.lean:1581` (docstring) and `:1586` (code `(1 : ℝ) / 5`); `4/5` is at 1582, 1603, 1608, 1609, 1612, 1621 (see b.11); all in the private `Checks` section.

## (b) Script output — Sat Oct  3 06:25:09 UTC 2026
### b.1 Commit scope
$ git log --oneline -2 t/T2038; git diff --stat main...t/T2038; git diff --name-only main...t/T2038; git status --short
9d784bf T2038: RowIndep header: exact RBM2D line ranges of the port
11d7bd2 T2038: S1-11 Green/RowIndep (row independence, row LDE high-probability bound) + registry line
 RBM3D/Green/RowIndep.lean | 1595 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    3 +-
 2 files changed, 1597 insertions(+), 1 deletion(-)
RBM3D/Green/RowIndep.lean
RBM3D/Test/Axioms.lean
status-lines:        0
### b.2 Module build (started Sat Oct  3 06:23:09 UTC 2026)
$ lake build RBM3D.Green.RowIndep   # complete output
✔ [3253/3253] Built RBM3D.Green.RowIndep (9.1s)
Build completed successfully (3253 jobs).
exit=0
### b.3 Full build (root `#assert_rbm_axioms` included; the root does not yet import the new module)
$ lake build | tail -2
Build completed successfully (3735 jobs).
exit=0
### b.4 Registry pre-check (ST1-COMMON item 8): scratch file outside the repository, `lake env lean`
$ cat precheck2038.lean; lake env lean precheck2038.lean; echo exit=$?   # lines of the audit message that list premise names are cut by `cut -c1-130`; the full output is in the scratchpad (`precheck.out`)
import RBM3D
import RBM3D.Green.RowIndep
#assert_rbm_axioms
axiom audit: 1255 theorems, 440 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
premises found by scanning: 13 (borrowed 2, owed 0, structural 11).
registry: 5 borrowed + 2 owed + 19 structural; 13 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
precheck exit=0
Registry line added: `RBM.Green.AgreeOffRow` in `structuralProps` (a `Prop`-valued relation on two sample points, taken as hypothesis by `Xentry_congr_of_ne`, `Hflow_submatrix_congr`; DECISIONS §20). The scan found it (13 premises found, structural 11; it is not in the "carry nothing" list).
### b.5 Axioms of every new public declaration (68 in `RBM.Green`, 6 in `RBM.Green.RowIndepInst`)
$ lake env lean axioms2038.lean   # one `#print axioms` per public name, generated from the file by script
lines in script: 78
'RBM.Green.stochDom_rowSum_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.highProb_norm_rowSum_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
--- all 74 lines, grouped (74 = 68 + 6):
  72 depends on axioms: [propext, Classical.choice, Quot.sound]
   2 does not depend on any axioms
axioms exit=0
$ grep -nE "\b(sorry|admit|native_decide)\b|^ *axiom " RBM3D/Green/RowIndep.lean | wc -l
       0
### b.6 Target statements, extracted by script from the file
$ python3 extract.py highProb_norm_rowSum_sq_le   # theorem header up to `:=`
theorem highProb_norm_rowSum_sq_le (hu : 0 ≤ u)
    (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω')
    {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ q : U n,
      ‖rowSum sz n u (row n q) (C n q) ω‖ ^ 2
        ≤ (sz.size n : ℝ) ^ (2 * τ) * rowVarSum sz n u (row n q) (C n q) ω}) :=
Section variables (file): `variable {d : ℕ} {sz : Sizes d} {n : ℕ}` and `variable {u : ℝ} {i : Idx d (sz.L n) (sz.W n)} {p : ℕ}`; `Sizes d`, `Idx d L W`, `HighProbAt`, `StochDomAt` are the merged MD-1/MD-2 definitions.
$ diff of the key statement, RBM2D c9a24cf `RowIndep.lean:1330` vs this file `:1360` (unified, difflib)
--- RBM2D c9a24cf RowIndep.lean:1330
+++ RBM3D t/T2038 RowIndep.lean:1360
@@ -2 +2 @@
-    (hsize : Filter.Tendsto d.size Filter.atTop Filter.atTop)
+    (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
@@ -4,3 +4,3 @@
-    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (d.size n : ℝ) ^ Ccard)
-    (row : ∀ n, U n → Idx (d.L n) (d.W n))
-    (C : ∀ n, U n → Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
+    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
+    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
+    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
@@ -8,2 +8,2 @@
-    (hC : ∀ n q (ω ω' : Sizes.SeqΩ d),
-      (∀ c ∈ offRowCoord d n (row n q), ω c = ω' c) → C n q ω = C n q ω')
+    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
+      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω')
@@ -11,3 +11,3 @@
-    HighProbAt (Sizes.seqP d) d.size (fun n => {ω | ∀ q : U n,
-      ‖rowSum d n u (row n q) (C n q) ω‖ ^ 2
-        ≤ (d.size n : ℝ) ^ (2 * τ) * rowVarSum d n u (row n q) (C n q) ω})
+    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ q : U n,
+      ‖rowSum sz n u (row n q) (C n q) ω‖ ^ 2
+        ≤ (sz.size n : ℝ) ^ (2 * τ) * rowVarSum sz n u (row n q) (C n q) ω})
### b.7 Declaration-level comparison with RBM2D (statement and proof text, whitespace-normalised, after the renaming R1-R4 as regexes)
$ python3 fulldiff.py   # the slice 56-1424 of RBM2D contains no declaration after line 1418
declarations RBM2D 56-1424 (renamed by R1-R4 regexes): 82  RBM3D before Instances: 82
statement+proof text identical after renaming: 77
text differs: ['gvar_rowCoord', 'card_LdeIdx_le', 'stochDom_rowSum_generalTime', 'highProb_norm_rowSum_sq_le']
only in RBM2D: ['one_le_size']  only in RBM3D: ['rowIndep_gvarF_offDiag']
The four differing declarations: `gvar_rowCoord` (calls the private `rowIndep_gvarF_offDiag` for RBM2D `gvar_offDiag`), `card_LdeIdx_le` (`Sizes.card_Idx sz n` for the `Z2` unfolding), `stochDom_rowSum_generalTime` and `highProb_norm_rowSum_sq_le` (`Sizes.one_le_size sz n` for the private `one_le_size`). Statements: all 68 public statements are identical after renaming; the definitions that differ in meaning only through `svarF`:
652:noncomputable def rowVarSum {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
653-    (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
654-    (ω : Sizes.SeqΩ sz) : ℝ :=
655-  u * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖C ω k.1‖ ^ 2
--- RBM2D c9a24cf:
noncomputable def rowVarSum (d : Sizes) (n : ℕ) (u : ℝ) (i : Idx (d.L n) (d.W n))
    (C : Sizes.SeqΩ d → Idx (d.L n) (d.W n) → ℂ)
    (ω : Sizes.SeqΩ d) : ℝ :=
  u * ∑ k : {k : Idx (d.L n) (d.W n) // k ≠ i}, svar (d.L n) (d.W n) i k.1 * ‖C ω k.1‖ ^ 2
### b.8 Compiled nonempty instances (`SizesInst.sz0`, `d = 3`, `N = 2097152` at `n = 0`, all deterministic hypotheses discharged, no external hypothesis)
$ grep -n "^theorem .*_sz0\|^theorem LdeIdx_nonempty_sz0" RBM3D/Green/RowIndep.lean
1473:theorem LdeIdx_nonempty_sz0 (n : ℕ) : Nonempty (LdeIdx sz0 n) := by
1483:theorem highProb_norm_rowSum_sq_le_sz0 (z : ℂ) :
1495:theorem stochDom_rowSum_general_sz0 (z : ℂ) :
1507:theorem stochDom_rowSum_generalTime_sz0 (z : ℂ) :
1539:theorem integral_norm_row_sum_pow_le_sz0 :
1587:theorem exists_agreeOffRow_ne_sz0 :
$ python3 -c (print the text of `theorem highProb_norm_rowSum_sq_le_sz0` up to the next blank line)   # instance of the key target
theorem highProb_norm_rowSum_sq_le_sz0 (z : ℂ) :
    HighProbAt (Sizes.seqP sz0) sz0.size (fun n => {ω | ∀ q : LdeIdx sz0 n,
      ‖rowSum sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2) ω‖ ^ 2
        ≤ (sz0.size n : ℝ) ^ (2 * (1 / 10 : ℝ)) *
          rowVarSum sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2) ω}) :=
  highProb_norm_rowSum_sq_le (U := fun n => LdeIdx sz0 n) (Ccard := 2) zero_le_one
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ q => q.1)
    (fun n q => minorCol sz0 n 1 z q.1 q.2) (fun _ q => measurable_minorCol 1 z q.1 q.2)
    (fun _ q _ _ h => minorCol_congr 1 z q.2 h) (by norm_num)
Instance data: `u = 1`, `τ = 1/10`, `Ccard = 2`, `U n = LdeIdx sz0 n = Σ i, {a // a ≠ i}` (nonempty for every `n`: `LdeIdx_nonempty_sz0`; `#U = N(N-1) ≤ N²` by `eventually_card_LdeIdx_le`), `row n q = q.1`, `C n q = minorCol sz0 n 1 z q.1 q.2` (measurable: `measurable_minorCol`; off-row: `minorCol_congr`), `hsize` from `sz0_tendsto` (`tendsto_natCast_atTop_iff`), `z` arbitrary. `integral_norm_row_sum_pow_le_sz0` gives `E‖∑_{k≠x} H_{xk}‖⁴ ≤ 6` at `x = 0`, `c ≡ 1` using `∑_{k≠x} S_{xk} = 1 - S_{xx} ≤ 1` (`sum_svarF_row`); `exists_agreeOffRow_ne_sz0`: two samples agree off row `0` and `H` differs in the entry `(0, y)`.
### b.9 Name-clash grep of the new public names
$ python3 clash.py   # for each public name n: grep -rnE "(theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+(\S*\.)?(n)(\s|$)" RBM3D, in the main worktree and in the .lean files each other T20xx worktree changes against main
public names checked: 74 (distinct short names 73); declaration lines matching under RBM3D/ of the main worktree (HEAD 6231342): 0
other ticket worktrees (34, audit copies skipped), .lean files they change against main: matching lines 0
### b.10 Port sources
$ git -C ../RBM2D --no-optional-locks log -1 --format="%h %ci" c9a24cf; git -C ../RBM2D --no-optional-locks log -1 --format=%h
c9a24cf 2026-10-02 09:03:18 -0700
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/RowIndep.lean
 RBM2D/Green/RowIndep.lean | 503 ++--------------------------------------------
 1 file changed, 21 insertions(+), 482 deletions(-)
Ported text: RBM2D `Green/RowIndep.lean:56-1418` at `c9a24cf` (header 1-55, the `Checks` docstring and section 1420-1659 and the `#print axioms` lines 1661-1759 not ported); RBM1D enters only through RBM2D's own port (its header cites RBM1D `86573b9`); no RBM1D text was read or copied directly.
### b.11 `d = 2` tokens of the portmap row 59 (`Z2/zdist2:2`, `1/5:1`)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/RowIndep.lean | grep -nE "Z2|zdist2|1 ?/ ?5|\(1 : ℝ\) / 5|4 ?/ ?5"
1135:    simp [Idx, Z2, Sizes.size, ZMod.card, sq]
1422:Two checks at the concrete sizes `L n = 3`, `W n = 1` (nine lattice points, `Idx 3 1 = Z2 3`):
1581:/-- At `L = 3`, `W = 1` the profile row of `x = (0,0)` sums to `1` (five sites of weight `1/5`),
1582:so the off-diagonal part sums to `4/5`. -/
1586:      = if k ∈ ({(0, 0), (1, 0), (2, 0), (0, 1), (0, 2)} : Finset (Idx 3 1)) then (1 : ℝ) / 5
1603:    ∑ k : {k : Idx 3 1 // k ≠ (0, 0)}, svar 3 1 (0, 0) k.1 = 4 / 5 := by
1608:`c ≡ 1` and `∑_{k≠x} svar(x,k) = 4/5` the bound reads `E‖∑_{k≠x} H_{xk}‖⁴ ≤ 96/25`
1609:(`(2·2-1)!! = 3`, `2 · 3 · (4/5)² = 96/25`). -/
1612:      svar (checkSizes.L n) (checkSizes.W n) x k.1 = 4 / 5) :
1621:has off-diagonal sum `4/5`, so `E‖∑_{k≠x} H_{xk}‖⁴ ≤ 96/25`. -/
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Gauss/Model.lean | sed -n 42,44p   # the d = 2 profile
noncomputable def svar (i j : Idx L W) : ℝ :=
  if (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L
  then (5 : ℝ)⁻¹ * (W : ℝ)⁻¹ ^ 2 else 0
$ grep -nE "Z2|zdist2|1 ?/ ?5|\(1 : ℝ\) / 5|4 ?/ ?5" RBM3D/Green/RowIndep.lean | cut -c1-120   # this file: only the docstring mentions of `Z2`
68:* the private `one_le_size` of RBM2D is the merged `Sizes.one_le_size`; the `Z2` unfolding in
1161:`Sizes.card_Idx`, so the `Z2` unfolding of RBM2D is not needed). -/
### b.12 Narrative
1. Ported RBM2D `Green/RowIndep.lean:56-1418` at `c9a24cf` (82 declarations: 68 public, 14 private) to `Z_{WL}^d`; the new file is `RBM3D/Green/RowIndep.lean` (1595 lines incl. header and instances). 77 of the 82 declarations are text-identical (statement and proof) to RBM2D after the regex renaming R1-R4 (b.7); one private declaration is dropped (`one_le_size`: replaced by the merged `Sizes.one_le_size`), one private helper is added (`rowIndep_gvarF_offDiag`).
2. Dropped from the port: the private `Checks` docstring and section (RBM2D 1420-1659: `checkSizes`, `green_diag_ne_zero`, `greenMinor_congr_of_offRow`, `check_*`, `growSizes`) and the `#print axioms` lines. `green_diag_ne_zero` needs `im_green_apply_self`, absent in RBM3D ((c)); the constant-size checks are replaced by the `sz0` instances (b.8). No public declaration is dropped (68 public in both).
3. Independence structure (dimension-free): the row block `rowSet i = {(i,k,b), (k,i,b)}` and `offRowCoord i` are disjoint finite coordinate sets of the one product measure `seqP sz`, so `IndepFun` follows from `LinearForm.iIndepFun_coord` and `indepFun_finset`; the minor `G^(i)` and every coefficient `C` read only `offRowCoord i`.
4. Changes forced by the renaming rules, nothing else: `Idx d L W`, `sz : Sizes d`, `Sizes.seqP sz`, and the profile `svarF d (sz.L n) (sz.W n) (sz.lam n)` in `rowVarSum` (b.7), which carries the coupling `lam n`, the merged `FineModel` convention. The scale is `N = sz.size n = (W L)^d` (`Sizes.card_Idx`). No exponent changes: `Ccard`, `τ`, `D`, `p`, `N^{2τ}` are RBM2D's; the `2` in `#LdeIdx ≤ N²` counts (row, column) pairs and is dimension-free.
5. `d = 2` tokens (b.11): `Z2` ×2 = RBM2D 1135 (proof of `card_LdeIdx_le`: replaced by `Sizes.card_Idx`) and 1422 (docstring of the `Checks` section: dropped); `zdist2`: no occurrence in this file at `c9a24cf` (the portmap token is not present); `1/5` = RBM2D 1581 (docstring) and 1586 (code `(1 : ℝ) / 5`), with `4/5` at 1582, 1603, 1608, 1609, 1612, 1621, all in the private `Checks` section (1420-1659): the weight `5⁻¹` of RBM2D's fixed five-point profile `svar` (`Model.lean:44`), i.e. a `d = 2` neighbour count `2d + 1 = 5`, not an exponent and not in any public statement. For `d ≥ 3` the profile is `svarF` (diagonal `W^{-d}(1 + 2 d g²)⁻¹`, `svarF_diag`), forced by R4; the check was not ported, so no `1/5` remains in the file.
6. No hypothesis was added, weakened or removed against RBM2D: `highProb_norm_rowSum_sq_le` has RBM2D's hypotheses `hu`, `hsize`, `hcard`, `hCmeas`, `hC`, `hτ` (b.6 diff shows only the renaming). The paper does not state this file as a lemma (`3_5_Loop_Hierarchy.tex:37`: "standard arguments based on resolvent identities and large deviation estimates"); `hsize` (`N → ∞`) is the explicit form of "N sufficiently large", as in RBM2D.
7. Instances (b.8) are at `SizesInst.sz0` (`d = 3`, `W = (2(n+1))^5`, `lam → 0`) with the minor-resolvent columns `minorCol` as coefficients (the application in `lem_GbEXP`), `Ccard = 2`; all deterministic hypotheses are discharged, none is an unproved pin of another gate.
8. Registry: `AgreeOffRow` is the only `Prop`-valued definition of the file that a theorem takes as a hypothesis and none proves; registered structural in `RBM3D/Test/Axioms.lean` (one appended line; the previous list entry gets a comma). Pre-check exit 0 (b.4). `set_option linter.style.longLine false` is set as in `Loop/KLCut.lean:45`; the build prints no warning (b.2).
9. Hub: after merge add `import RBM3D.Green.RowIndep` after the last `import` line of `RBM3D.lean`; the module imports only merged files (`Gauss/{DominationAt,FineModel,LinearForm}`, `Green/EntryCore`, Mathlib).

## (c) Verified Mathlib names (those new relative to the RBM2D port, `env.contains` by `run_cmd`; the other names are the port's and compile, b.2)
tendsto_natCast_atTop_iff: present
Fintype.sum_equiv: present
Equiv.subLeft: present
Fintype.sum_prod_type: present
mul_inv_cancel₀: present
inv_mul_le_iff₀: present
Fintype.card_sigma: present
Fintype.card_subtype_le: present
zero_ne_one: present
ZMod.nontrivial: present
Real.one_le_rpow: present
Function.update_of_ne: present
Function.update_self: present
Verified absent in RBM3D (same run): `RBM.Gauss.gvar_offDiag`, `RBM.Gauss.gvarF_offDiag` (public; the merged `fineModel_gvarF_offDiag` is private), `RBM.im_green_apply_self`, `RBM.isUnit_sub_smul_one_of_im_ne_zero`.

## (d) Open issues and paper-delta candidates
- `T2038a`: the row LDE is stated as `HighProbAt` / `StochDomAt` at the scale `N = (W L)^d` along a size sequence with the explicit hypothesis `Tendsto sz.size atTop atTop`, uniformly over an index set with `#U n ≤ N^Ccard`; the paper states no such lemma (it refers to `[YY_25]`, `3_5_Loop_Hierarchy.tex:37`). Same shape as RBM2D's delta T2001b (explicit `N → ∞`).
- `T2038b`: the variance in `rowVarSum` is `u ∑_{k≠i} S_{ik} ‖C_k‖²` with `S = svarF d L W (sz.lam n)` (the merged `(eq:variancematrix)` carrying the coupling). No residual difference from the paper statement of `(eq:variancematrix)`; recorded only because RBM2D's `svar` had no `g`.
- Registry: `RBM.Green.AgreeOffRow` appended to `structuralProps` (DECISIONS §20 class: a predicate on samples taken as hypothesis by deterministic lemmas); the dispatcher may reclassify. Since the branch point `55f30d1`, main (`1678ea4`, T2034) changed the same two lines of `structuralProps` (appended `RBM.EKFastDecay]`), so the two registry edits conflict textually; union of both lines expected (DECISIONS §20 (3)).
- Not ported (not in lines 56-1418): the RBM1D check `greenMinor_congr_of_offRow` (private in RBM2D `Checks`); it needs `im_green_apply_self`, absent here. A later ticket that needs "row independence of `G^(i)`" as a statement has `Hflow_submatrix_congr_offRowCoord`, `minorCol_congr`, `minorCol_eq_greenMinor` here.
