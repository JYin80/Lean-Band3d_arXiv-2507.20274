Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 12:55:29 UTC 2026

Setting: row a (targets 1-6, 8), `d = 3`, BA tuple `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `gK = BAflowLam0 = g0`, `g0^2 = t0 lam^2`
(`TwistStep2:740`), `N = (W L)^d`. Instance `(kappa, eps, c, delta) = (1/2, 1/10, 1/6, 1/10)`, `Aof kappa = (kappa+1)/kappa = 3`,
`Lambda = delta^-1 = 10`, `sz0` (`Defs/Sizes.lean:260`: `L = 4m, W = (2m)^5, lam = (2m)^-6`, `m = n+1`), `BAFlow sz0 (1/2)(1/10)(1/6)(1/10) zSeq`
= merged `flow_sz0` (`BA/FlowPins.lean:1214`). No external hypothesis occurs: every input is a merged theorem
(`baEKSum*_holds`, `baEKSumDecayNonzero_holds`, `baTwKerZero_holds`, `baKBoundAt_holds`, `baKsolve` `KTreeRep:1699`,
`BAKsol_isKLoopS` `KSolve:606`); the stochastic data `(PrecL, STEKDecayKgL, STEKLowgL)` stay binders of the forms.

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `kappa_m` (target 2) | `= kappa = 1/2` | `kappa_m <= Im m_F` (`EMn2BA_mF_data` `EMn2BA:125`), class `BAReal .. kappa_m ..` (`BAflow_real` `GreenSchur:59`) | `Im m_S >= 4/5` (`mS_im_half` `FlowPins:1147`): 3/10 |
| 2 | R1 at `kappa_m` | `0 <= g0 lam`, `g0^2 <= lam^2`, `lam^2 <= ((kappa_m+1)/kappa_m) g0^2` | `t0 >= kappa/(kappa+1)` (`TwistStep2_T0_ge` `:731`), `t0 < 1` | `kappa/(kappa+1) = 1/3` vs `t0 >= 2/3` (`t0_sz0` `FlowPins:1227`): factor 2 |
| 3 | `Aof kappa` (3 (e), 4) | `3` | form hypothesis `1 <= Aof kappa`; target 4 needs only `A > 0` (`BATwKerZero` `TwistPins:209`: `forall A > 0`) | `3 - 1 = 2` |
| 4 | window `Lambda` | `delta^-1 = 10` | `0 < g0 n <= delta^-1` eventually (`BAflow_lam0_window` `GreenSchur:72`; `0 < delta` from `Admissible`) | `g0 <= lam <= 1/64` at `n = 0`; `10` |
| 5 | pin constants `C` (3 (a)-(d), 5a, 5b) | positive, depend on `(d, n_, Lambda, kappa[, K])` only (`EKPins:97-134`) | fixed before `sz, n` (`forall` order: `exists C` after `(d,n,Lambda,kappa[,K])`) | n/a (no numeric size needed) |
| 6 | target 4 constant | `C = Ci^n`, `Ci = max Cs (2 + A C0 E_k)`, `A = 3` (route `EKNonzero:261-300`, projected factor by `baTwKerZero_holds` `TwistKer:256`) | threshold `(1-s) L^2 <= A g^2`, `0 <= s <= t < 1`, `0 < g <= Lambda` | pin `BAEKSumDecayNonzero` is the case `A = 1` (`EKPins:134`); `A = 3` same proof |
| 7 | lift `eps_lift` | `min(1/2, tau d/(4C))` | `C eps_lift / d <= tau/4` so `W^{C eps} <= N^{tau/4}` (`W <= N^{1/d}` = `Sizes.W_rpow_le` `Defs/Sizes:220`; absorption as `prec_core` `Evolution/Prec:130`) | `0` on the 2nd branch, `>0` on the 1st; `eps_lift < 1` slack 1/2 |
| 8 | lift `D0` | `C + 1 + D/c` | `D0 > 1`; `W^{-D0+C} <= N^{-D}` (`W >= N^c`): exponent `-(c + D) <= -D` | `c = 1/6`; `D0 - 1 = C + 6D` |
| 9 | absorption | `N^{tau/4} N^{tau/4} <= N^tau` | `N >= 1` | exponent `tau/2` |
| 10 | `K = 1/c` (3 (d), 5b) | `6` | `L^d <= N <= W^{1/c}` (`prec_L_pow_le`); `log L <= W^eps` needs `W^{eps/2} >= 2K/(eps d) = 4/eps` | at `eps = 1/2`: `W >= 8^4 = 4096`, reached at `n = 2` in `sz0` (script) |
| 11 | `4 <= W^eps`, `1 < W` | eventual | `W >= N^c -> infinity` | eventual only |
| 12 | `(1-u)^-1`, `u <= t0` (target 6) | `<= 2/Im z <= 2 N^{1-eps} <= 2N` | `1 - t0 >= Im z/2` (`EMn2BA_one_sub_T0` `:111`), `N^{-1+eps} <= Im z` (`BAdom` `MFixedPoint:435`), `eps > 0` | instance: `(1 - t0)^-1 <= 60/11` (`Im z >= 11/30`) vs `2 N^{0.9}`, `N >= 2097152` |
| 13 | tree-RHS count (target 6) | `W^d L^{2d} (Cm L)^2 X^k`, `X = W^-d Bparam <= 4N` | `W^d L^{2d+2} <= N^3` (uses `L^2 <= L^d`, `d >= 3`); `‖treeEqRhsS‖ <= c_k N^{k+3}`, `c_k = k^2 Cm^2 4^k`; `S = 1`: `\|1_{ab}\| <= 1` | |
| 14 | Lip exponent | `2k + 2` | `c_k N^{k+3} <= N^{2k+2}` iff `N^{k-1} >= c_k`; equivalently (`c_k <= N`) `k+4 <= 2k+2` iff `k >= 2` | `N^{k-1}`, exponent `k-1 >= 1`; in the `k+4` count slack `k-2` (0 at `k = 2`, absorbed by `N >= c_2`, `N -> infinity`) |

Hypothesis-set checks (statements as in `docs/tickets/checks/T2507-check.lean`; check compiled, CONTROL H308 (2): exit 0):
- Target 1 `BAEKKer`: `exists E, C = baFM sz gK E /\ forall n, BAReal d (L n) (gK n) kappa (E n) (BAmF sz gK E n)`; at the flow `E = BAflowEs`, `baFMz = baFM sz (BAflowLam0 sz z) (BAflowEs sz z)` (`FlowPins:393`), so `BAflow_real` is the second clause. `hIm` of `Step2Kern_UN_BA` (`Step2Kern:124`): `(E + m).im = m.im >= kappa > 0`.
- Target 3: after `Step2Kern_UN_BA` the five goals are `BAEKSumNdecay/Decay1/DecayNAL/Decay2` (`EKPins:97-134`, `EKSum`) at `Lambda = delta^-1`, `g = g0 n`; the ratios `ellT(t)^2/ellT(v)^2 >= 1` (`ellT_mono`, `g >= 0`) and `((g^2+|1-v|)/(g^2+|1-t|))^m >= 1` hold for `v <= t < 1`, so the absorption of rows 7-9 is the band one with `lam` replaced by `gK n`. The measure enters only through `P` in `StochDomAt`: the lemmas used (`of_subset` `:325`, `mul` `:439`, `const_mul_left` `:462`, `highProb` `:534`, `HighProbAt.inter` `:571`, `of_highProbAt_add_rpow_neg` `:697`) are stated for arbitrary `P : Measure Ω`; `grep -c "IsProbabilityMeasure\|IsFiniteMeasure\|SigmaFinite" RBM3D/Defs/StochDomAt.lean` prints `0`. So no premise beyond the merged texts is needed (stop rule "lift needs a premise" does not fire).
- Target 4 / 3 (e): `(1-s) L^2 <= A g0^2` with `A = Aof kappa >= 1 > 0`; the non-projected factors (`sigma_i = sigma_{i+1}`) use `baEKSameRow_holds` (`EKPins:568`), which has no threshold; the projected ones `baTwKerZero_holds` (public). No private lemma of `EKNonzero` is needed.
- Targets 5a, 5b: `NQGoodGen_KerNAL`, `QProxyG_KerEK4` (`NQGood1Gen:54`, `QProxy:680`) are the pins `BAEKSumDecayNAL`, `BAEKSumDecay2` verbatim at `gK = g0 n` (windows `t <= 1 - g0^2/L^2`, `W^-1 <= (1-t)/(1-s)`, `EKFastDecay (g0 n)`), eventually in `n`.
- Target 6: `HasDerivAt` of `K n . sigma a` on `[0,1)` with `treeEqRhsS .. 1 ..` from `BAKsol_isKLoopS (baKsolve d)` (`baKcac_isKLoopS` `KTreeRep:1674` is premise-free); cut loops of length `2..k` by `baKBoundAt_holds` (`KBound:85`, `tau = 1`, `Lambda = delta^-1`, `kappa`); `t n <= BAflowT0 < 1` (`EMn2BA_T0_lt_one`); mean value on `[0, t n]` as `NQEndFlowLift:640-690`.

### (ii) Concrete nondegenerate instance (`d = 3`, `sz0`, `n_ = 2` and `k = 3`, `A = 3`, `Lambda = 10`)

Data: windows `s = 0, t = 1/2` (forms (a)-(d)); `s_n = 1 - (2/3) lam^2/L^2`, `t_n = (1+s_n)/2` (form (e), target 4 at `A = 3`; `(1-s) L^2 = (2/3) lam^2 <= 3 g0^2` since `g0^2 = t0 lam^2`, `t0 >= 2/3`); `t_n = 1/2 <= t0` (target 6); `X = 1`, `A n v w = delta_0` (deterministic, `‖A‖ = 1 <= X`) as in the band examples `Step34Gen:1164-1190`.
Facts taken from merged lemmas: `Im z in [11/30, 7/10]` (`zSeq_im_ge/le` `FlowPins:1197, 1205`), `Im m_S >= 4/5`, `Im m + Im z = 6/5`, `Im m <= 1` (`EMn2BA_mim_le_one` `EMn2BA:99`), so `t0 in [2/3, 5/6]`; `sz0.size 0 = 2097152`, `lam 0 = 1/64` (`sz0_values`).
The script (Python, no Lean) checks each hypothesis at `n = 0, 1, 2, 9, 99, 9999` (both ends of `t0`) and the exponent rows:

```
$ cd <scratchpad>/T2507 && python3 -I inst.py > out.txt; sed -n '1,12p' out.txt; echo ...; sed -n '/exponent rows/,$p' out.txt | sed -n '1,6p;$p'; grep -c '^OK' out.txt; grep -c '^FAIL' out.txt
kappa,eps,c,delta= 1/2 1/10 1/6 1/10   Aof(kappa)=(k+1)/k= 3   kappa/(kappa+1)= 1/3
--- n=0: L=4 W=32 N=(WL)^3=2097152
OK   Admissible Bandwidth W>=N^(1/6)
OK   WO  W^(-d/2+delta)<=lam<=1/delta
OK   BAdom  N^(-1+eps)<=1/4<=11/30<=Im z<=7/10<=1
OK   BAdom  kappa<=4/5<=Im m_S
OK   R1 t0=2/3: g0^2<=lam^2, lam^2<=A g0^2, g0*lam>=0, 0<g0<=1/delta
OK   R1 t0=5/6: g0^2<=lam^2, lam^2<=A g0^2, g0*lam>=0, 0<g0<=1/delta
OK   window s=0<=t=1/2<=1-g0^2/L^2 ; 1/W<=(1-t)/(1-s)=1/2
OK   A-form A=3: 0<=s<=t<1, (1-s)L^2=(2/3)lam^2<=A*g0^2 (g0^2>=2/3 lam^2)
OK   KLip: t_n=1/2<=2/3<=t0<1 ; (1-t0)^-1<=60/11<=2N^(0.9)
OK   hcount W^d L^(2d+2)<=N^3
...
--- exponent rows
OK   Lip k=2: k+4<=2k+2 (const absorbed in one N) ; slack in N^(k-1)>=N
OK   Lip k=3: k+4<=2k+2 (const absorbed in one N) ; slack in N^(k-1)>=N
OK   Lip k=4: k+4<=2k+2 (const absorbed in one N) ; slack in N^(k-1)>=N
OK   K=1/c=6 ; log L<=W^eps needs W^(eps/2)>=2K/(eps d)=8 at eps=1/2, i.e. W>=8^4=4096
   first n with W=(2(n+1))^5>=4096: 2
ALL OK
75
0
```

Script path: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2507/inst.py` (39 lines; blocks for `n = 1, 2, 9, 99, 9999` in `out.txt` lines 13-67 are all `OK`: 75 `OK`, 0 `FAIL` in total).
Nondegeneracy: `N >= 2097152`, `L >= 4`, `W >= 32`, every window nonempty (`s < t < 1`, `0 <= s`), `0 < g0 <= 10`; the only eventual quantities are `4 <= W^eps`, `log L <= W^eps` (`n >= 2` at `eps = 1/2`) and `N >= c_k` (the constants `Cm, C` of the pins are not numeric: they enter only as the threshold of `forall^f n`).

### Verdict per target (row a)
- 1 `BAEKKer`: PASS (hypothesis set satisfiable at the flow; class equals `T2507_EKKer`).
- 2 `baEKKer_flow` (`kappa_m = kappa`, R1 factor 2 at the instance): PASS.
- 3 (a)-(e) five forms at `@BAEKKer`: PASS (no new premise; `Aof` any with `1 <= Aof kappa`).
- 4 `baEKSumDecayNonzeroA_holds`: PASS (route through public `baEKSameRow_holds`, `baTwKerZero_holds`).
- 5 (a), (b) `baNQGoodGen_kerNAL`, `baQProxyG_kerEK4`: PASS.
- 6 `baKloop_lip`, every `k >= 2`: PASS (`2k+2` closes for `k >= 2`; slack zero only in the `k+4` count at `k = 2`, absorbed by `N -> infinity`).
- 8 instances: PASS (data above; `PrecL` inputs deterministic `delta_0`, `X = 1`).
No pin, row or stop line is moved by this section: verdict PASS; no 1a-audit needed.

---

## (b) Script output (stage 1b) — Wed Oct 14 13:24:24 UTC 2026

Branch `t/T2507`, base `5f6270cd`, HEAD `dff84231`:
```
$ git log --format="%h %s" 5f6270cd..HEAD
dff84231 T2507: KLipBA docstring line cites
4d0a76ee T2507: BA/KLipBA (baKloop_lip, every k >= 2), import lines in RBM3D.lean
949a6a28 T2507: BA/EKGenBA (class BAEKKer, hKer bundle, five STEK forms, A-form Nonzero, D1 
$ lake build RBM3D.BA.EKGenBA RBM3D.BA.KLipBA 2>&1 | tail -1
Build completed successfully (4123 jobs).
$ lake build > full3.log 2>&1; echo $?; tail -1 full3.log; grep "axiom audit" full3.log; grep -o "non-vacuity.*ledgers" full3.log   (HEAD dff84231)
0
Build completed successfully (4400 jobs).
info: RBM3D.lean:630:0: axiom audit: 15285 theorems, 4721 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 124 premises in the two ledgers
$ wc -l RBM3D/BA/EKGenBA.lean RBM3D/BA/KLipBA.lean   (bottom-up 690 / 335; stop lines 1,050 / 520; central 1,025, stop 1,550)
     706 RBM3D/BA/EKGenBA.lean;     324 RBM3D/BA/KLipBA.lean;    1030 total;
$ git diff --stat main...t/T2507
 RBM3D.lean            |   2 +
 RBM3D/BA/EKGenBA.lean | 706 ++++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/KLipBA.lean  | 324 +++++++++++++++++++++++
 3 files changed, 1032 insertions(+)
$ git diff --name-only main...t/T2507 -- RBM3D/Test/Axioms.lean | wc -l   (registry scan: no line closed, none added)
0
$ grep -nE 'sorry|admit|native_decide|^axiom' (both files) | wc -l
0
$ lake env lean ax2.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"   (one #print axioms line per name below)
11
BAEKKer baEKKer_flow baEKSumNdecaygL_holds baEKSumRes1gL_holds baEKSumRes2NALgL_holds baEKSumRes2gL_holds baEKNonzerogL_holds baEKSumDecayNonzeroA_holds baNQGoodGen_kerNAL baQProxyG_kerEK4 baKloop_lip 
```

Target statements, extracted by script (`awk` from the declaration line to `:=`; the `def` shows its body line):
```
def BAEKKer {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, C = baFM sz gK E ∧ ∀ n, BAReal d (sz.L n) (gK n) κ (E n) (BAmF sz gK E n)
theorem baEKKer_flow (d : ℕ) : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ n, κm ≤ ((baFMz sz z).m n).im) ∧ BAEKKer sz (baFMz sz z) (BAflowLam0 sz z) κm ∧
      (∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹) ∧
      ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
        sz.lam n ^ 2 ≤ (κm + 1) / κm * BAflowLam0 sz z n ^ 2 := by
theorem baEKSumNdecaygL_holds (d : ℕ) : STEKSumNdecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
theorem baEKSumRes1gL_holds (d : ℕ) : STEKSumRes1gL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
theorem baEKSumRes2NALgL_holds (d : ℕ) : STEKSumRes2NALgL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
theorem baEKSumRes2gL_holds (d : ℕ) : STEKSumRes2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
theorem baEKNonzerogL_holds (d : ℕ) (Aof : ℝ → ℝ) :
    STEKNonzerogL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) Aof := by
theorem baEKSumDecayNonzeroA_holds (d n : ℕ) (Λ κ : ℝ) :
    3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ s t : ℝ, 0 ≤ s → (1 - s) * (L : ℝ) ^ 2 ≤ A * g ^ 2 → s ≤ t → t < 1 →
        ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
          BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ Aset : Finset (Fin n), (∀ i, σ i ≠ σ (finRotate n i) → i ∈ Aset) →
            ∀ 𝒜 : (Fin n → Zd d L) → ℂ, ‖zeroModeSet d L Aset (BAUN d L g E m σ s t 𝒜)‖ ≤ C * ‖𝒜‖ := by
theorem baNQGoodGen_kerNAL (d : ℕ) :
    NQGoodGen_KerNALFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) := by
theorem baQProxyG_kerEK4 (d : ℕ) :
    RBM.Ind.QProxyG_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) := by
theorem baKloop_lip (d : ℕ) : NQEndFlowGen_KLipFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
    (fun sz z => BAflowT0 sz z) := by
```

Check compiles in the worktree: `lake env lean docs/tickets/checks/T2507-check.lean` gave exit 0, 0 error lines.  Statement check against the pins (scratch `pins_check.lean`, uncommitted: Part 2 of `docs/tickets/checks/T2507-check.lean` up to target 6, then these lines):
```
74:example {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : T2507_EKKer sz C gK κ ↔ BAEKKer sz C gK κ := 
75:example (d : ℕ) : T2507_KerFlowBA d := baEKKer_flow d
76:example (d : ℕ) : T2507_SumNdecayBA d := baEKSumNdecaygL_holds d
77:example (d : ℕ) : T2507_SumRes1BA d := baEKSumRes1gL_holds d
78:example (d : ℕ) : T2507_SumRes2NALBA d := baEKSumRes2NALgL_holds d
79:example (d : ℕ) : T2507_SumRes2BA d := baEKSumRes2gL_holds d
80:example (d : ℕ) : T2507_NonzeroBA d := fun Aof => baEKNonzerogL_holds d Aof
81:example : ∀ d n Λ κ, T2507_EKNonzeroA d n Λ κ := baEKSumDecayNonzeroA_holds
82:example (d : ℕ) : T2507_KerNALBA d := baNQGoodGen_kerNAL d
83:example (d : ℕ) : T2507_KerEK4BA d := baQProxyG_kerEK4 d
84:example (d : ℕ) : T2507_KLipBA d := baKloop_lip d
$ lake env lean pins_check.lean > pins_check.out 2>&1; echo "exit $?"; grep -c error pins_check.out
exit 0 ; errors: 0
```

Compiled nonempty instances, `d = 3` (heads of the `example`s; every deterministic hypothesis discharged; bodies at the cited lines):
```
EKGenBA.lean:587:example : ∃ κm : ℝ, 0 < κm ∧ (∀ n, κm ≤ ((baFMz sz0 zSeq).m n).im) ∧ BAEKKer sz0 (baFMz sz0 zSe
EKGenBA.lean:594:example : BAEKKer sz0 (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) (1 / 2) := inst_kernel
EKGenBA.lean:597:example := baEKSumNdecaygL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 s
EKGenBA.lean:603:example := baEKSumRes1gL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0
EKGenBA.lean:609:example := baEKSumRes2NALgL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 
EKGenBA.lean:615:example := baEKSumRes2gL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0
EKGenBA.lean:650:example := baEKNonzerogL_holds 3 (fun κ => (κ + 1) / κ) le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10
EKGenBA.lean:661:example : ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ,
EKGenBA.lean:677:example : ∃ Ck : ℝ, 0 < Ck ∧ (∀ᶠ n in atTop, NQGoodGen_KerNAL (baFMz sz0 zSeq) (BAflowLam0 sz0 
EKGenBA.lean:691:example : ∃ C4 : ℝ, 0 < C4 ∧ ∃ n : ℕ, RBM.Ind.QProxyG_KerEK4 (baFMz sz0 zSeq) (BAflowLam0 sz0 z
EKGenBA.lean:698:example (n : ℕ) (u u' : ℝ) (hu : u ≤ u') :
KLipBA.lean:312:example : NQEndFlowGen_KLip (baFMz sz0 zSeq) (fun _ => (1 / 2 : ℝ)) 3 ∧
$ scratch copies with each `example` renamed to `theorem`/`def`, `#print axioms`, `| sort | uniq -c`
  11 'RBM.BA.EKGenBAInst.exa_*' deps: [propext, Classical.choice, Quot.sound];   1 'RBM.BA.KLipBAInst.exa_*' deps: [propext, Classical.choice, Quot.sound];
```

Name clash, hypothesis rules, ports:
```
$ bash clash2.sh   (grep -rnw of each new public name over RBM3D/*.lean, the two new files excluded; hits per name)
 BAEKKer=0 baEKKer_flow=0 baEKSumNdecaygL_holds=0 baEKSumRes1gL_holds=0 baEKSumRes2NALgL_holds=0 baEKSumRes2gL_holds=0 baEKNonzerogL_holds=0 baEKSumDecayNonzeroA_holds=0 baNQGoodGen_kerNAL=0 baQProxyG_kerEK4=0 baKloop_lip=0 EKGenBAInst=0 KLipBAInst=0
$ grep -rlw (five main names) /Users/junyin/Lean_proof/RBM3D/RBM3D | wc -l   (merged files)     0
C1 grep -c (EKGenBA, KLipBA): RBM3D/BA/EKGenBA.lean:0 RBM3D/BA/KLipBA.lean:0 | X1-C4 grep (def|abbrev|structure): RBM3D/BA/EKGenBA.lean:64:def BAEKKer {d : ℕ} (sz : Sizes d) (C : FlowF
withLam hits other than `seqP (sz.withLam 0)`: 0 | U5S-C3 grep: RBM3D/BA/EKGenBA.lean:70:theorem baEKKer_flow (d : ℕ) : ∀ κ : ℝ,
RBM1D/RBM2D mentions (EKGenBA, KLipBA): RBM3D/BA/EKGenBA.lean:0 RBM3D/BA/KLipBA.lean:0   -> no sister-project port; copies are of private RBM3D helpers:
Prec.lean prec_W_rpow_ge:54 prec_one_lt_W:66 prec_L_pow_le:73 prec_log_le:86 prec_window:107 prec_ratio_ge_one:112 prec_core:130 
NQEndFlowLift.lean nqLift_loopOf_eq:457 nqLift_KLK_bound:472 nqLift_treeEq_bound:487 nqLift_Bctl_le:553 Step5KerBA_one_sub_inv:416
last commits Evolution/Prec fc765260;Induction/NQEndFlowLift d0484be4;BA/Step5KerBA 4c9a9311;Chain/Step34Gen 6e7d2602;
48:open private step34Gen_win_sz0 step34Gen_Az step34Gen_Az_sumZero step34Gen_Az_decay step34Gen_norm_Az_le 49-  step34Gen_norm_delta0_le from RBM3D.Chain.Step34Gen 
```

**Narrative (stage 1b; every figure is in the script output above or in the files).**
1. One row, no split: `EKGenBA` 706 lines (bottom-up ~690, stop 1,050), `KLipBA` 324 (~335, stop 520); 1,030 against the central 1,025. Targets 1-6 and 8 only; target 7 and `BA/QtNZBA` are U3-BA (b)'s (Decision (2)). `RBM3D.lean` gets two import lines after the last import.
2. Routes. T1 `BAEKKer` (`EKGenBA:64`): the pinned text, `STEKKer`-typed as `@BAEKKer d`. T2 `baEKKer_flow` (`:70`): `κm = κ`; `EMn2BA_mF_data` (`EMn2BA:125`), `BAflow_real` (`GreenSchur:59`),
   `BAflow_lam0_window` (`:72`), R1 by `TwistStep2_lam0_sq` (`TwistStep2:740`) with `0 ≤ g₀ λ` (the pattern of `baIniTermGen_kerFacts`, `Step5KerBA`). T3: unpack the class, `Step2Kern_UN_BA` (`Step2Kern:124`)
   with `hIm` from `BAReal` (`EKGenBA_hIm`), the stage-E pin at `Λ = 𝔡⁻¹`, `g = gK n` (`baEKSumNdecay_holds` `EKPins:218`, `baEKSumDecay1_holds` `EKSum:200`, `baEKSumDecayNAL_holds` `:290`,
   `baEKSumDecay2_holds` `:1772`, T4), then `EKGenBA_core` for (b)-(d), `StochDomAt.mul`/`of_subset` for (a), `const_mul_left` for (e). T4: the product step of `baEKSumDecayNonzero_holds`
   (`EKNonzero:261-300`) with `baEKSameRow_holds` (same-sign index) and `baTwKerZero_holds` (`TwistKer:256`, projected index, any `A > 0`), constant `Ci^n`, `Ci = max Cs Cz`; no private lemma of `EKNonzero` is used.
   T5: the stage-E pins at `g = BAflowLam0 n` on the eventual window, `Ck`, `C4` from `baEKSumDecayNAL_holds d k 𝔡⁻¹ κ`, `baEKSumDecay2_holds d k 𝔡⁻¹ κ … KL`. T6: `BAKsol_isKLoopS (baKsolve d)` (`KSolve:606`, `KTreeRep:1699`),
   `baKBoundAt_holds` (`τ = 1`, `Λ = 𝔡⁻¹`) for each length `m ≤ k`, `KLipBA_treeEq_bound` (`S = 1`), `KLipBA_X_le`, `KLipBA_one_sub_inv` (`EMn2BA_one_sub_T0`), `KLipBA_mvt`; for `N ≥ max 1 (k² Cm² 4^k)`:
   `‖treeEqRhsS‖ ≤ k² Cm² 4^k N^{k+3} ≤ N^{k+4} ≤ N^{2k+2}` (`k + 4 ≤ 2k + 2` iff `k ≥ 2`).
3. Statements: each target is its `T2507_*` pin (11 `example : T2507_X := name` compile; `T2507_EKKer ↔ BAEKKer` is `Iff.rfl`). No hypothesis added, no pin or merged file changed.
4. Family / `∃` table and UBA-C1 as used: the `∃` placements are the pinned ones (T2: `κm` after `κ`, before `(sz, ε, 𝔠, 𝔡, z)`; T4: `C` after `(d, n, Λ, κ, A)`; T5: `Ck` after `(k, κ, ε, 𝔡)`, `C4` after `(k, κ, ε, 𝔡, KL)`;
   T3, T6: none). R1 is stated once (T2) and used in no proof of T3-T6; the instances use it (`inst_R1`) for the window crossing `step34Gen_winK_of_cmp`. No `∀ n` drift or hierarchy premise.
5. Lift core: the seven private band helpers of `Evolution/Prec.lean` (lines above) are copied as `EKGenBA_*` at a law `μ` and a coupling `gK` (`Prec.whp` read as `StochDomAt.highProb`); no `IsProbabilityMeasure` is needed
   (the stop rule does not fire; `grep -c "IsProbabilityMeasure\|IsFiniteMeasure\|SigmaFinite" RBM3D/Defs/StochDomAt.lean` prints 0 in this worktree). `open private` is used only by the instances (6 names of `Chain/Step34Gen`).
6. `∀ n` sources: the class and R1 at every `n` come from `BAflow_real`, `EMn2BA_mF_data`, `TwistStep2_lam0_sq` (no `0 < g₀`); `0 < g₀ ≤ 𝔡⁻¹` is only `∀ᶠ n` (`BAflow_lam0_window`); T6 also uses `EMn2BA_T0_lt_one`, `EMn2BA_one_sub_T0` at every `n`.
7. Instances in numbers (`d = 3`, `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `zSeq`, `flow_sz0`; `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `Aof (1/2) = 3`): T3 at `n_ = 2`, `σ = (+,-)` (NAL: `(+,+)`),
   window `(s, t) = (0, 1/16)` moved from `sz0.lam` to `g₀` by R1, `𝒜 = δ₀` (sum-zero `δ₀ ⊗ (δ₀ - δ_e)` for (d)), `X ≡ 1`, the `PrecL` inputs discharged by deterministic domination at `seqP (sz0.withLam 0)`; (e): `s = 1 - lam²/L²`,
   `t = (1+s)/2`, `Aset = univ`, `Aof κ = (κ+1)/κ`. T4 at `Λ = 10`, `A = 3`, the same `s`, `t`, at an index of the eventual window. T5a at `k = 3`, `ε = 1/2`, `D = 2`, `(s, t) = (0, 1/16)`, `σ = (+,+,-)`, `𝒜 = δ₀`: the bound at an index `n`;
   T5b at `k = 3`, `KL = 6 = 1/𝔠`: the class at an index `n`. T6 at `k = 3`, `t ≡ 1/2 ≤ t₀` (`t₀ ≥ 2/3`), `u = 0`, `u' = 1/2`: the bound `N^8 · 1/2` at an index `n`. The indices come from `Filter.Eventually.exists` along `atTop`.
8. Paper deltas: none new; the A-form threshold in `g₀` carries `(κ+1)/κ` through R1 (`g² ≤ ((κ+1)/κ) g₀²`, merged `TwistStep2_lam0_sq`), a D-ledger note only.

## (c) Verified Mathlib names (script `#eval env.contains`, 42 names probed)
```
present: 40; absent as written: [StochDomAt.highProb, StochDomAt.of_eventually_empty]   (both live in `RBM.StochDomAt`, probed and present as `RBM.StochDomAt.*`)
```
Present: `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`; `convex_Icc`; `Real.log_le_rpow_div`; `Real.rpow_le_rpow_of_nonpos`; `Real.rpow_le_rpow_of_exponent_le`; `Real.rpow_natCast`; `Real.rpow_mul`; `Real.rpow_add`;
`Real.rpow_le_one`; `Real.one_le_rpow`; `Real.rpow_neg`; `Real.sqrt_eq_rpow`; `Real.sqrt_sq`; `Real.rpow_pos_of_pos`; `Real.rpow_nonneg`; `tendsto_rpow_atTop`; `inv_anti₀`; `inv_le_one_of_one_le₀`; `div_mul_cancel₀`;
`sub_sub_cancel`; `pow_le_pow_left₀`; `pow_le_pow_right₀`; `one_le_pow₀`; `one_le_mul_of_one_le_of_one_le`; `Finset.single_le_sum`; `Finset.prod_le_prod₀`; `Nat.card_Icc`; `Nat.card_Ioc`; `Matrix.one_apply`;
`Complex.add_im`; `Complex.ofReal_im`; `Filter.Eventually.exists`; `Filter.Tendsto.eventually_ge_atTop`; `div_le_div_of_nonneg_left`; `div_le_div_of_nonneg_right`. Verified absent: none searched.

## (d) Open issues and paper-delta candidates
1. T5b's instance applies the class `QProxyG_KerEK4 … 3 6 C4 n` at an eventual index only; the merged helpers have no length-3 sum-zero tensor (`step34Gen_Az` has length 2), so the pin `baEKSumDecay2_holds` is exercised with a tensor by the T3(d) example (`n_ = 2`).
2. The instances read six private names of `Chain/Step34Gen` by `open private` (line 48-49); a rename there breaks the instances, no statement.
3. Preflight (a) gives form (e) the data `s_n = 1 - (2/3) lam²/L²`; the instance uses `s_n = 1 - lam²/L²` (`(1-s) L² = lam² ≤ 3 g₀²` by R1). Not a correction: no statement, verdict or pin changes, so no (a′).
4. Ticket 8 says the `PrecL` inputs stay binders; they are discharged (stronger).
5. Row b / target 7 / `BA/QtNZBA` not started (Decision (2)); T4 is the lemma behind it. Paper-delta candidates: none (`T2507a` unused).
