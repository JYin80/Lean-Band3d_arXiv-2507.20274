Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 19:39:28 UTC 2026 (`date -u`)

Scratch (Python only, no Lean): `P2465` = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2465 (`census0.py j1.py j2.py`). Engines read, unmodified: T2464 `s4_exponents.py` (instance header up to its first `print`), `common.py`/`tree.py`/`ba.py`/`roots.py` (the leaf walk of `s5_census.py`). Notation: `N=(WL)^d`, `B=Bctl`, `Wi=W^-d`, `A=𝔡⁻²+1`, `k=n_W-n_A`, `ord=n_S+2k` (`BAGraph.scalingOrder`, slot `nV` holds `n_A`, `BAVocab:143-147`). T2464 (9e1d5f15) and T2466 (03109267) are merged on `main`; S1-S3 are tested below.

### (i) Exponent table (target 1; values from `j1.out`, instance of (ii))
| quantity | value | constraint | slack |
|---|---|---|---|
| `K₀,K₁` of `S'=svarF(0)` (rescaled: `S=t·S'`, `BAlwS`) | 1, 1 (`W^-d` on a block, block size `W^d`) | `LWKBound D'.S (K₀W^-d) K₁` for `baClaimSize` | exact |
| `K₀,K₁` of `S⁺'=lift(ω_t)`, `ω_t=Θ_t^{++}` | max entry 0.6669, row/col `ℓ¹` 0.6671 (ω symmetric) | `BAExp14a_theta_l1` (public, `d=k+2`, `k=d-2≥1`), `t`-uniform on `[0,1)`; `K₀=K₁=max(1,S)` | proxy 1.0 vs 0.667 |
| `K_d` (`M`, `g₀Ψ`) | `M^B`: row/col `ℓ¹` 1.0828, entry ≤ 0.9995; `g₀·2d`=0.078 | `baKBound_E` (existential) | proxy 1.0828 |
| `t^{n_W}` | `val(BAlwData_t)=t^{n_W} val(BAExp14d_dataT)` | `BAExp14d_val_scale` (merged, `t=0` incl.) | exact |
| window `W^-d ≤ A·B` | 3.05e-5 ≤ 6.26e-3 | `twB0_ge_holds` (needs `sz.WO 𝔡`, eventually) | x205.1 |
| `Ψ=N^τ' B^{1/2}`, `τ'=τ/(2(n_S+1))` | n_S=0..6: `τ/2` slack `τ/(2(n_S+1))`: 0.5,0.25,0.167,0.125,0.1,0.083,0.071 at τ=1 | `τ' n_S ≤ τ/2` | `τ/(2(n_S+1))` |
| arithmetic `K A^k ≤ N^{τ/2}` (`lwExpTerm6_arith`) | least τ closing the chain at this N over 58 classes: 0.0213 | eventual in n for each `τ>0` (`K` depends on `d,𝔡,κ,P`) | see (ii) |
| `η` | `η=0.49975`, `η⁻¹=2.001` | `η ≤ 1` (`BAExp14c_eta_le_one`) | `η⁻¹ ≤ 4=1/(κ(1-t))` x2.0 |
| `B` | 6.196e-5 | `B ≤ 2` (`BAExp14a_eventual_scalars`, the BA form; no `B ≤ 1`), `N⁻¹ ≤ B` | x3.2e4, x130 |
| floor `N^-ord/2 ≤ η⁻¹B^{ord/2}` (`BAExp14c_floor`; fails for `t^{n_W}R`) | ord=3..8: x3.0e3 … x5.7e8 | `N ≥ 2`, `B ≤ 2`, `expAvg_Bctl_ge` | ≥ 3.0e3 |
| envelope `‖X‖ ≤ N^{K}` (`BAExp14c_val_env`) | `K=|I'|+c(n_S+n_W+#M)+1`, `c=|1-ε|+1=1.9`: max 58.7 over classes, baAllM 15.3 | any finite `K` (`BAExp14a_prec_integral` takes `D=|K|+|K_f|+1`) | none needed |
| `ord` range on `n_M=0` leaves | 3..8; `k∈{0..3}`, `n_S∈{0..6}`, `n_A≤n_W` always | `ord ≥ 0` for the floor integer `o` | min 3 |

Route (all merged names; stop rule S1 not triggered): `X:=t^{-n_W}P_{xy}` (0 at `t=0` when `n_W≠0`; `BAExp14c_val_zero`); for `t>0`, `val_scale` then `baClaimSize` at `BAExp14d_dataT` with `hG` on the entry event (`STLocalEntrygL`, `BAExp14d_entry_whp` is private in `BAExp14dB`: copy), `hM`,`hP` from `baKBound_E`, `hS`,`hSp` as in the table; `ord`-arithmetic as `lwExpTerm6_arith`; `≺ → 𝔼` by `BAExp14a_prec_integral`+`BAExp14a_det_iff`. `n_W=0` (no hypothesis `2≤n_W` in target 1): `t^0=1`, `n_A=0`, `val_scale` is the identity, no division.

### (ii) Instance and leaf census
`d=3`, `sz0` n=0 (`L=4,W=32,N=2097152,λ=1/64`), `zSeq`, `t≡1/2`, `𝔡=1/10`, `κ=1/2`, `ε=1/10`, `𝔠=1/6` (`flow_sz0`, `half_lt_t0`; as T2464 (ii): `BAFlow` holds, `t<T₀=0.6937`).
```
$ cd P2465 && python3 census0.py          # n_M=0 BAG5Leaf-type leaves, fuel 2, all BACtx choices (engine of T2464 s5_census.py)
MERGED    s=1 n_M=0 leaves: 1487
MERGED    s=0 n_M=0 leaves: 1427
T3C-tr_1  s=1 n_M=0 leaves: 1378
T3C-tr_1  s=0 n_M=0 leaves: 1318
D2X       s=1 n_M=0 leaves: 109
D2X       s=0 n_M=0 leaves: 109
distinct (nS,nW,nA,#mdot,n_int) over the six lists (counts summed): 58 ; leaves 5828
nS range 0 6 ; k=nW-nA range 0 3 ; nA range 0 7 ; ord range 3 8 ; #mdot max 14 ; n_int max 14
by (nS, k): (0,2):4 (1,2):20 (2,1):40 (2,2):168 (2,3):24 (3,0):20 (3,1):280 (3,2):368 (4,0):64 (4,1):996 (4,2):416 (5,0):540 (5,1):1608 (6,0):1280
nA>nW anywhere: False ; k=0 anywhere: True
$ cd P2465 && python3 j1.py               # the table of (i) at the instance; chain K(P) Psi^nS Wi^k <= N^tau eta^-1 B^(ord/2), K(P)=Kd^#M K1^nA K0^k
instance: N=2097152 W^d=32768 L^d=64 lam^2W^d=8.0 t=0.50 eta=(1-t)Im m=0.49975 Bctl=6.1959e-05 W^dBctl=2.0303 Wi=W^-d=3.0518e-05 A=dd^-2+1=101
K0(S)=1.000 K1(S)=1.000 | omega_t: max|omega_ab|=0.6669 max row/col l1=0.6671 (omega symmetric: True) | M^B: row/col l1 1.0828 max entry 0.9995 ; g0*2d=0.0781 | proxies K0=1.0000 K1=1.0000 Kd=1.0828
window: W^-d=3.0518e-05 <= A*Bctl=6.2579e-03 (twB0_ge: W^dB=2.0303 >= 1/A=0.00990): slack x205.1 ; eta^-1=2.0010 <= 1/(kappa(1-t))=4.0 ; eta=0.49975<=1 ; Bctl=6.196e-05 <= 2 ; N^-1=4.768e-07 <= Bctl
classes (nS,nW,nA,#mdot,n_int) in the n_M=0 leaves of the six lists: 58 ; leaves 5828 ; max over classes of the least tau closing the chain at N=2097152: 0.0213 (class (5, 7, 7, 11, 14)) ; at tau=1 max ratio LHS/RHS = 2.703e-04
ratio at tau->0 (no N-slack) for the leaf baAllM (0,2,0,5,1): 0.1804 ; for the worst class: 1.1987
table by (nS, k): nS tau' n_S <= tau/2 slack tau/(2(nS+1)) at tau=1: nS=0: 0.5000, nS=1: 0.2500, nS=2: 0.1667, nS=3: 0.1250, nS=4: 0.1000, nS=5: 0.0833, nS=6: 0.0714
floor N^(-ord/2) <= eta^-1 B^(ord/2), ord=3..8: 3: 3.29e-10 <= 9.76e-07 (x3.0e+03) ; 4: 2.27e-13 <= 7.68e-09 (x3.4e+04) ; 5: 1.57e-16 <= 6.05e-11 (x3.9e+05) ; 6: 1.08e-19 <= 4.76e-13 (x4.4e+06) ; 7: 7.49e-23 <= 3.75e-15 (x5.0e+07) ; 8: 5.17e-26 <= 2.95e-17 (x5.7e+08)
envelope (BAExp14c_val_env): K = |I'| + c(n_S+n_W+#mdot) + 1, c=|1-eps|+1=1.9 ; max over the classes = 58.7 ; baAllM: 15.3
RHS t^nW eta^-1 B^(ord/2) at the instance leaf baAllM (nW=2, ord=4): 1.9204e-09 ; pathwise chain: t^2 Kd^5 W^-2d = 3.4654e-10
STLocalEntrygL leading term W^d E|G-M|^2 -> [(1-tA)^-1 A]_ab: max 1.9959 vs W^d Bctl=2.0303 (ratio 0.983 < 1); Ward row sums of A: 1.000000
```
Reading: the leaf `baAllMP` (`nS=0,nW=2,nA=0,#M=5`, `ord=4`, `x~y`, `baAllM_leaf`) has pathwise `t²Kd⁵W^-2d=3.47e-10 ≤ 1.92e-9=t²η⁻¹B²` (ratio 0.18, no `N`-slack used). The worst class `(5,7,7,11,14)` (`k=0`) has ratio 1.199 at `τ→0`, so it needs `N^{τ/2} ≥ 1.2`: closes for every `τ ≥ 0.0213` at this `N`; for smaller `τ` it is the usual eventual threshold. Counts agree with T2464 (1487/1427/1378/1318/109/109 `n_M=0`) and T2466 (b). External hypothesis `STLocalEntrygL`: leading term `W^dE|G-M|²→[(1-tA)⁻¹A]_ab` max 1.9959 vs `W^dB=2.0303` (ratio 0.983 < 1, last line). `STLocalEntrygL` is the only one of the five used; the other four stay inside the statement def.

### (iii) Inputs by name and text (`python3 j2.py`)
```
S3  T2465_BAG5LeafPrec (check) vs RBM.BA.BAG5LeafPrec (Graph/BAExp14c.lean:884), names normalised: identical = True
S2  T2465_Q1Need (check) vs RBM.BA.BAG5LeafPrec1 (Graph/BAExp14dB.lean:806), names normalised: identical = True
join vs leaf: conclusion (from PrecL) identical = False ; join hypotheses block before PrecL, join has nM = 0 and no LWAvgLawgL/STLmaxgL/STLKgL/STDecaygL: True
join vs leaf: conclusion (from PrecL) identical after unfolding the let mu := Sizes.seqP (sz.withLam 0) = True
```
- `baExp14bS3_of_leaf : ∀ d, BAExp14bS3OfLeaf d` (`BAExp14cB:832`), `BAExp14bS3OfLeaf d := BAG5LeafPrec d → BAExp14bS3 d` (`BAExp14c:915`): matches target 3 (`baExp14bS3_of_leaf d (baG5LeafPrec_holds d)`).
- `baG5LeafPrec1_holds (d) : BAG5LeafPrec1 d` (`BAExp14dB:820`) is unconditional; `BAG5LeafPrec1` = `T2465_Q1Need` (premises: the five of `BAExp14bS3`, no distinct-molecule hypothesis, `P.g.nM = 1`), so every `n_M=1` leaf of the census (212 tied one-molecule, 4236 two-molecule; T2466 (b)) is covered. Target 2 is the case split `P.g.nM ≤ 1` (`BAG5LeafProps` conjunct 2): `=0` target 1 (needs `Normal`, conjunct 1), `=1` `Q1`. The join pin's conclusion equals the leaf pin's (line 4 of `j2.out`); its hypotheses are the leaf pin's with `STLocalEntrygL` only.
- Name clash: `git grep -nwE 'BAExp14e|BAGraphPrecJoin|baGraphPrecJoin_holds|baG5LeafPrec_of|baG5LeafPrec_holds|baExp14bS3_holds' HEAD -- RBM3D RBM3D.lean`: 2 hits, both comments (`BAExp14c.lean:882`, `BAExp14dB.lean:22`); no declaration on `main` or on the 72 `t/T24*` refs (same grep per ref, `cut -d: -f2-3 | sort | uniq -c`: `4 BAExp14c.lean:882`, `6 BAExp14dB.lean:22`, i.e. the same two comments); `RBM3D/Graph/BAExp14e.lean` absent.

### (v) Section map and predicted lines
Basis `LWExpTerm6` §1-§4 `:51-352` (302 lines) + instances `:634-754` (121) + case split and chain (≈ 40) = 463; Lean/band ratio measured on T2466 (1528 Lean lines / 1081 band lines) = 1.41, so ≈ 654; ×2.6 upper reference ≈ 1,204; plus BA additions (kernel assembly of `D'_t`, entry-event copy, `BAG5LeafProps` destructuring) 100-250: **≈ 750-900 central, ≤ 1,450 upper**, below the 1,800 rule and the 2,000 stop line: one file `Graph/BAExp14e`, no `BAExp14eB`.
Sections: §1 pins (`BAGraphPrecJoin`) · §2 kernels of `D'_t` and the pathwise bound (`baClaimSize`) · §3 arithmetic (copy of `lwExpTerm6_arith`) · §4 `baGraphPrecJoin_holds` · §5 `baG5LeafPrec_of`, `baG5LeafPrec_holds` · §6 `baExp14bS3_holds` · §7 instances `BAExp14eInst`.

### Verdicts
- Target 1 (`BAGraphPrecJoin`, `baGraphPrecJoin_holds`): **PASS** (all rows close; S1 not triggered: `val_scale` + `BAExp14a_theta_l1` give the `t`-free kernel bounds of `D'_t`, `t^{n_W}` is exact).
- Target 2 (`baG5LeafPrec_of`, `baG5LeafPrec_holds`): **PASS** (S3 and S2 not triggered: texts identical, `baG5LeafPrec1_holds` unconditional).
- Target 3 (`baExp14bS3_holds`): **PASS**. Target 4 (instances at `baAllMP`, `d=3`): **PASS** (leaf, window, floor, envelope numbers above).

## (a′) Preflight corrections — Mon Oct 12 20:15:11 UTC 2026
1. Row 11 and the Route paragraph of (a): the kernel bounds of `S⁺' = lift(ω_t)` and `S' = svarF(0)` come from `BASizeClaim_theta_decay` (private, `open private`, as
   `BAExp14d.lean:347`) with `lwKBound_of_decay` (`K₀ = (1+Λ²)C₅+1`, `K₁ = K₀ expC(d-2,c)`), not from `BAExp14a_theta_l1` (row sums only); `BAExp14d_entry_whp` is used by
   `open private`, not copied; the arithmetic is the public band lemma `lwExpTerm6_arith` (reached through `BAExp14a → BA/LWPinsBA → LWExpTerm6`). No verdict changes.

## (b) Script output — Mon Oct 12 20:15:11 UTC 2026; branch `t/T2465` at `a90e3aaf` (commits 8fc2cfa0, 5c68bbfe, dd7f3d2d, 32e67fef, a90e3aaf on base ad52b370)
Stage 1b: targets 1-4 built and committed. **Line count: 433 against the stop line 2000** (the 1,800 prediction rule of the ticket is not reached; one file, no `BAExp14eB`).
1a verdict (S1-S3): none occurs. S1: the kernel facts of `D'_t` are merged (`baKBound_E`, `BASizeClaim_theta_decay`) and `t^{n_W}` is exact (`BAExp14d_val_scale`). S2, S3: T2466's
`BAG5LeafPrec1` and T2464's `BAG5LeafPrec` equal the pins (rows 3 and 2 of the diff below). No `T2465_*` pin changed, no new `inductive`, `Test/Axioms.lean` untouched.
```
$ wc -l RBM3D/Graph/BAExp14e.lean; git diff --name-only main...t/T2465   # stop line 2000 per file; only the new file differs
     433 RBM3D/Graph/BAExp14e.lean
RBM3D/Graph/BAExp14e.lean
$ lake build RBM3D.Graph.BAExp14e 2>&1 | tail -1;  lake env lean RBM3D/Graph/BAExp14e.lean 2>&1 | wc -l   # build; warnings+errors of the file itself
Build completed successfully (4046 jobs).
       0
$ lake env lean axioms.lean | python3 sumax.py   # import RBM3D.Graph.BAExp14e; #print axioms of every new public declaration
7 declarations: BAGraphPrecJoin baGraphPrecJoin_holds baG5LeafPrec_of baG5LeafPrec_holds baExp14bS3_holds BAExp14eInst.leafPrecInst BAExp14eInst.baAllMP_counters
axiom lists: [propext, Classical.choice, Quot.sound]
$ (temporary root: RBM3D.lean plus `import RBM3D.Graph.BAExp14e` after the last import line, restored afterwards by `git checkout -- RBM3D.lean`; not committed)
$ lake build 2>&1 | grep -E "axiom audit|Build completed|error"
info: RBM3D.lean:535:0: axiom audit: 13603 theorems, 4347 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4303 jobs).
$ lake env lean assert.lean > assert.out; diff assert0.out assert.out   # assert.lean: import RBM3D, RBM3D.Graph.BAExp14e, #assert_rbm_axioms; assert0.lean: import RBM3D only
1c1 < axiom audit: 13598 theorems, 4345 definitions, 0 axioms   --- > axiom audit: 13603 theorems, 4347 definitions, 0 axioms   (no other line differs; exit 0)
```
Target statements, comparison with the pins of the check file, and the instances:
```
$ python3 -I extract_stmts.py   # the statements (docstrings and proofs omitted)
60: def BAGraphPrecJoin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → ∀ P : BAPGraph (Fin 2), P.g.Normal → P.g.nM = 0 →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂(Sizes.seqP (sz.withLam 0))‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))
180: theorem baGraphPrecJoin_holds (d : ℕ) : BAGraphPrecJoin d := ...
331: theorem baG5LeafPrec_of : ∀ d : ℕ, BAGraphPrecJoin d → BAG5LeafPrec1 d → BAG5LeafPrec d := ...
340: theorem baG5LeafPrec_holds : ∀ d : ℕ, BAG5LeafPrec d := ...
347: theorem baExp14bS3_holds : ∀ d : ℕ, BAExp14bS3 d := ...
$ python3 -I stmt_diff.py   # normalised text: pin of the check file / merged name against the Lean statement
BAGraphPrecJoin (target 1): identical = True  (chars 700 / 700)
T2465_BAG5LeafPrec vs merged BAG5LeafPrec (T2464): identical = True  (chars 777 / 777)
T2465_Q1Need vs merged BAG5LeafPrec1 (T2466): identical = True  (chars 790 / 790)
$ python3 -I extract_inst.py   # the instances (hE..hD: the five Step 1/2 pins at sz0, zSeq, t = 1/2, kept as hypotheses); leafPrecInst (:365) = the pin conclusion at that data
386: example (hE..hD) : leafPrecInst BAG5LeafInst.baAllMP := baGraphPrecJoin_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) ...
      ... (BAG5LeafInst.baAllM_leaf.2.1 true true _ (List.mem_singleton_self _)).1 baAllMP_counters.1
393: example (hE..hD) : leafPrecInst BAG5LeafInst.baAllMP := baG5LeafPrec_of 3 (baGraphPrecJoin_holds 3) (baG5LeafPrec1_holds 3) le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) ...
      ... (fun n => (half_lt_t0 n).le) hE hA hL hK hD BAG5LeafInst.baAllMP BAG5LeafInst.baAllM_leaf.2.1
401: example (hE..hD) : leafPrecInst BAG5LeafInst.baAllMP := baG5LeafPrec_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) ...
      ... BAG5LeafInst.baAllMP BAG5LeafInst.baAllM_leaf.2.1
410: example (hE..hD) : leafPrecInst BAExp14dInst.leaf1P := baG5LeafPrec_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) ...
      ... BAExp14dInst.leaf1P BAExp14dInst.leaf1_props.1
419: example (hE..hD) := baExp14bS3_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) ...
      ... (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hL hK hD
```
Name clashes, C1 / forbidden-token greps, and the scratch copy of the check file:
```
$ git grep -nwE "BAExp14e|BAGraphPrecJoin|baGraphPrecJoin_holds|baG5LeafPrec_of|baG5LeafPrec_holds|baExp14bS3_holds" main -- RBM3D RBM3D.lean | cut -c1-100
main:RBM3D/Graph/BAExp14c.lean:882:the probe's `BAGraphPrecJoin`): for every `P` with the leaf prope
main:RBM3D/Graph/BAExp14dB.lean:22:   leaf pin `BAG5LeafPrec` of L4c1 (`T2464`); the `n_M = 0` half 
$ (same grep on every ref t/T23* t/T24* except t/T2465: counts of file:line; sumrefs.sh)
   4 RBM3D/Graph/BAExp14c.lean:882;   5 RBM3D/Graph/BAExp14dB.lean:22;   1 RBM3D/Probe/T2398Pins.lean:444;   1 RBM3D/Probe/T2398Pins.lean:479;
$ grep -nwE "mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus|sorry|admit|axiom|native_decide" RBM3D/Graph/BAExp14e.lean | wc -l; grep -cE "^(inductive|structure|class|axiom)" RBM3D/Graph/BAExp14e.lean
       0
0
$ lake env lean T2465-scratch-check.lean > scratch-check.out; echo exit=$?; grep -c error scratch-check.out   # check file + imports of BAExp14cB/dB/e + 8 term examples (`example : P := theorem`), not committed
exit=0
0
$ grep -E "^RBM.BA.(BAG5LeafPrec |baExp14bS3_of_leaf|baGraphPrecJoin_holds|baG5LeafPrec_of|baG5LeafPrec_holds|baExp14bS3_holds)" scratch-check.out
RBM.BA.BAG5LeafPrec : ℕ → Prop
RBM.BA.baExp14bS3_of_leaf : ∀ (d : ℕ), RBM.BA.BAExp14bS3OfLeaf d
RBM.BA.baGraphPrecJoin_holds : ∀ (d : ℕ), RBM.BA.BAGraphPrecJoin d
RBM.BA.baG5LeafPrec_of : ∀ (d : ℕ), RBM.BA.BAGraphPrecJoin d → RBM.BA.BAG5LeafPrec1 d → RBM.BA.BAG5LeafPrec d
RBM.BA.baG5LeafPrec_holds : ∀ (d : ℕ), RBM.BA.BAG5LeafPrec d
RBM.BA.baExp14bS3_holds : ∀ (d : ℕ), RBM.BA.BAExp14bS3 d
```
Narrative.
- One new file, 7 sections (pin; kernels of `D'_t`; pathwise bound; `baGraphPrecJoin_holds`; `baG5LeafPrec_of`/`_holds`; `baExp14bS3_holds`; instances). `RBM3D.lean` is not edited: the import line is
  the hub's at merge (CLAUDE.md §1, §3 (A) 4; the branches of T2464 and T2466 touch only their own files); the temporary-root build above is the full `lake build` with that line.
- Ports: none (nothing copied from `../RBM1D` or `../RBM2D`); the twin is the in-repo band file `Graph/LWExpTerm6`, reused by name where public (`lwExpTerm6_arith`) and re-derived for BA otherwise.
- Target 1 (twin of `lwGraphPrecJoin_holds`): `X := (t^{n_W})⁻¹ P_{xy}` equals `P_{xy}` at T2466's rescaled data `D'_t` when `t^{n_W} ≠ 0` (`BAExp14d_val_scale`) and is `0` otherwise;
  envelope and floor from T2464 (`BAExp14c_val_env`, `BAExp14c_floor`); on the entry event of `STLocalEntrygL` (`BAExp14d_entry_whp`), `Ψ = N^{τ'}B^{1/2}`, `τ' = τ/(2(n_S+1))`,
  `‖X‖ ≤ C_Γ Ψ^{n_S}(W^{-d})^{n_W-n_A}` by one `baClaimSize` at `D'_t` (private `BAExp14e_pathwise`; `(L^d)^{n_M} = 1`), then `lwExpTerm6_arith` with `W^{-d} ≤ (𝔡⁻²+1)B` (`BAExp14a_Wd_le`) and
  `K A^k ≤ N^{τ/2}` eventually, then `BAExp14a_prec_integral` and `BAExp14a_det_iff`. Only `STLocalEntrygL` of the five Step 1/2 pins is a hypothesis; at the instance data its leading term has
  ratio 0.983 < 1 against `W^d B` ((a)(ii), last line).
- Target 2 splits `BAG5LeafProps` conjunct 2 (`n_M ≤ 1`): `n_M = 0` goes to target 1 (with `Normal`, conjunct 1), `n_M = 1` to `baG5LeafPrec1_holds` (T2466, unconditional, no distinct-molecule hypothesis).
  Target 3 is `baExp14bS3_of_leaf d (baG5LeafPrec_holds d)`; the five premises sit inside the defs, not as binders of the theorems (the audit differs from the baseline only in the counts).
- Instances: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `zSeq`, `flow_sz0`, `t ≡ 1/2`; the leaf `baAllMP` (`n_M = 0`, `n_W = 2`, `ord = 4`, `baAllMP_counters`) for target 1 and both forms of
  target 2, T2466's `n_M = 1` leaf `leaf1P` for the other branch, target 3 at `d = 3`; the five pins `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL` stay hypotheses (other gates' inputs).
- Private names reused by `open private` (precedent `BAExp14c.lean:35-43`, `BAExp14d.lean:43-44`): `BASizeClaim_theta_decay`, `BAVocab_val_of_factor`, `BAVocab_val_of_not`, `BAExp14d_svar0`, `BAExp14d_entry_whp`.
- The 1a size prediction (≈ 750-900 lines central) was high: the pathwise step is one `baClaimSize` application, the envelope and floor are T2464's, the entry event and the `val_scale` identity are T2466's.

## (c) Verified Mathlib names (`#check` of each in `names.lean`, import `RBM3D.Graph.BAExp14e`: exit 0, 0 errors; none verified absent)
`Nat.le_one_iff_eq_zero_or_eq_one`, `List.mem_singleton_self`, `_root_.zpow_neg` (bare `zpow_neg` is ambiguous under `open Matrix`: `Matrix.zpow_neg`), `zpow_natCast`, `pow_mul`, `inv_pow`,
`Nat.cast_ne_zero`, `NeZero.ne`, `norm_mul`, `norm_pow`, `norm_inv`, `Complex.norm_real`, `Real.norm_of_nonneg`, `Complex.ofReal_inv`, `Complex.ofReal_pow`, `Complex.ofReal_zero`,
`inv_mul_cancel₀`, `mul_inv_cancel_left₀`, `lt_of_le_of_ne`, `le_of_mul_le_mul_left`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.sqrt_nonneg`, `div_mul_eq_mul_div`, `div_le_div_iff₀`,
`tendsto_rpow_atTop`, `Filter.Tendsto.eventually_ge_atTop`, `pow_le_pow_left₀`, `le_add_of_nonneg_right`, `pow_eq_zero_iff`, `integral_congr_ae`, `integral_const_mul`, `Filter.Eventually.of_forall`,
`Real.exp_zero`, `Complex.norm_natCast`.

## (d) Open issues and paper-delta candidates
- No obstruction; no hypothesis added, no target weakened, no pin or frozen signature changed; the file is within the stop line (433 of 2000).
- Paper-delta candidates: none new. The pins differ from the paper by the explicit factor `t^{n_W}` (compiled: `BAExp14d_val_scale`; registry D573 = T2255a-d, `docs/paper-deltas.md:1532`) and by T2398a (`BAG5Leaf.lean:79`, carried by `BAG5LeafPrec`).
  Observation only: `BAGraphPrecJoin` is stated for every normal packed graph with `n_M = 0`; the band's `LWJoined` also ties the two external vertices into one molecule, which the proof does not use.
- The unmerged probe `t/T2398:RBM3D/Probe/T2398Pins.lean:444` defines `BAGraphPrecJoin` with `sz.slice n ω` and `BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n` in place of `BAExp14a_slc sz n ω` and `(baFMz sz z).m n`;
  `lake env lean defeq.lean` (two `example ... := rfl`, import `RBM3D.Graph.BAExp14e`): exit 0. `RBM3D/Probe` is not on `main` (`git ls-tree -r main --name-only | grep -c RBM3D/Probe/`: 0).
- Dependence for the dispatcher: the five `open private` names live in the merged files `Graph/BASizeClaim`, `Graph/BAVocab`, `Graph/BAExp14d`, `Graph/BAExp14dB`; renaming them there breaks this file.
