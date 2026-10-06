Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 09:50:17 UTC 2026

Fixed `n`: `t0 = t₀(z) ∈ (0,1)` (`BAflow_T0_bounds`, `BAFlow` with `κ > 0`), `T' = t₀(z')`, `E = E(z) = E(z')`, `g = lam n ≥ 0`,
`τ'' = T' s/u` (`BAtauS`), `1/2 ≤ 1 − c₁` (`c₁ ≤ 1/2`), `s₁ = max(s, 1 − c₁)`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | ConArg source time | `s₁ = max(s, 1−c₁) ≥ 1/2 = ε₁` | `ε₁ ≤ s₁` (`BAConArg''`) | `1−c₁−1/2 = 1/6` at `c₁ = 1/3`; 0 at `c₁ = 1/2` |
| 2 | ConArg target range | `u ∈ [s₁, max(t, 1−c₁)]` (§86) | `u ≤ max(t0, s₁)`: `t ≤ t0` and `1−c₁ ≤ s₁` | none needed; `u < 1`: `t ≤ t0 < 1`, `1−c₁ < 1` |
| 3 | lower end of `Fam(u)` | `T' ≥ min(t0, max(u, 1−c₁)) = min(t0, u)` (`u ≥ s ≥ 1−c₁`) | | |
| 4 | case 1 `u ≤ t0` | `T' ≥ u`, `τ'' ≥ u·s/u = s`, `min(t0,s) = s` | `min(t0,s) ≤ τ''` | 0 (equality at `T' = u`) |
| 5 | case 2 `t0 < u` | `u ≤ max(t0,s)` forces `u = s`, `s/u = 1`; `T' ≥ min(t0,u) = t0`, so `T' = τ'' = t0` | `min(t0,s) = t0 ≤ τ''` | 0; then `√τ'' g = g₀(z)` (top of the window) |
| 6 | window (squared) | `(1−c₁) t0 ≤ min(t0,s) ≤ τ'' ≤ t0` | `√(1−c₁) g₀ ≤ √τ'' g ≤ g₀`; `τ'' ≤ T' ≤ t0` since `s ≤ u` | `(1−c₁)t0 ≤ t0` by `c₁ t0`; `(1−c₁)t0 ≤ 1−c₁ ≤ s` by `(1−c₁)(1−t0)` |
| 7 | `τ'' > 0`, `τ'' < 1` | `τ'' ≥ (1−c₁)t0 > 0`; `τ'' ≤ t0 < 1` | hypotheses of `BAzztE_inv_core` | — |
| 8 | source coupling | `BAlamS = √(s/u)√T' g = √τ'' g` | needs `T' ≥ 0` (`T' ≥ min(t0, 1/2) > 0`) | — |
| 9 | `Bctl ≤ 1` | `Bctl_n(t)^{𝔠d} ≤ (1−t)/(1−s) < 1` ⇒ `Bctl(t) < 1` ⇒ `Bctl(s) ≤ Bctl(t) < 1` | `𝔠d > 0`, `t < 1` | eventual; (iii) below |
| 10 | `BALmaxFromLK` | `Bctl^k + Bctl^{k−1} ≤ 2 Bctl^{k−1} ≤ N^ε Bctl^{k−1}` | `N^ε ≥ 2` eventually, every `ε > 0` (`SizeTendsto`) | eventual |
| 11 | `STLmaxgL_max` | at `n`, `max(s n, c)` is `s n` or `c`; both bounds hold eventually | — | — |
| 12 | `c_κ` | `c_κ = √min(κ/(κ+1), 1/2)`, `T' ≥ min(t0, 1−c₁) ≥ c_κ²`, `t0 ≥ κ/(κ+1)` (`Im m ≥ κ`, `Im z ≤ 1`) | `c_κ ≤ 1` | `κ = 1/2`: `c_κ² = 1/3`; `t0 ≥ 41/60` |
| 13 | member constants | `κ' = c_κ κ ≤ κ`, `ε' = ε/2 ≤ ε` | `N^{−ε/2} < κ'` for `n ≥ n₀` (`Im z' ≥ κ' Im z`) | `n₀ = 1` at the instance, (iii) |
| 14 | `mS_im_ge` | `Im m_S ≥ 1.2/(1.44 + g²L³) ≥ 41/50` | `g²L³ ≤ 1/64` | `0.82439 − 0.82 = 4.4e-3`; merged `4/5` is too weak (gives `t0 ≥ 2/3` only) |
| 15 | `t0_sz0_ge` | `t0 = Im m/(6/5) ≥ 41/60 = 0.6833` | `≥ u = 17/25 = 0.68` | `0.0033` |
| 16 | `sz0_win`, floor/budget | `3/5 + 6·(3/640)/(3/5)⁴ = 0.81701` | `≤ 41/50 = 0.82`; floor `3/5 ≥ κ = 1/2` | `0.00299`; floor slack `1/10` |
| 17 | `sz0_win` range of `c₁` | `1−√(1−c₁) ≤ ρ ≤ 3/10` | `c₁ = 1/3`: 0.1835; `c₁ = 1/2`: 0.2929; `c₁ = 1/10`: 0.0513 | `0.1165` / `0.0071` / `0.2487` |
| 18 | ConArg instance `(s,u) = (2/3, 17/25)` | `√(s/u) = 0.99015` | `∈ [√(2/3), 1] = [0.81650, 1]`; `s < u`; `u ≤ 17/25 ≤ t0` | `0.0098` to the top end |
| 19 | `Step1` instances | `(1/2, 2/3)` and `(0, 1/16)`, `c₁ = 1/3`: `s₁ = 2/3`, `u ≡ 2/3` | `1/2 ≤ s₁`, `u ≤ max(t0,s₁)`, `u < 1`, `t ≤ t0` | `u = 2/3 < 41/60 ≤ t0`: case 1 only |

### (ii) One concrete nondegenerate instance

`d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{−6}`, `N ≥ 2^21`), `zSeq` (`z + m_S = w = 6i/5`),
`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`, `c₁ = 1/3`, `(s,t) = (1/2, 2/3)` and `(0, 1/16)`, ConArg `(s,u) = (2/3, 17/25)`.
Hypotheses of `BAStep1` that are deterministic are checked below; the owed pins `BAGbEXPii/ij` and the family premise (`STKboundgL`, `STLKgL`,
`STLocalMaxgL` at `s`) stay hypotheses of the examples (other gates' pins, CLAUDE.md §4 step 2).

P1: pointwise content of generalized targets 2, 3, 4 and the range facts of target 9 (exact `Fraction`s, 300000 samples; both `t0 < 1−c₁` and `t0 ≥ 1−c₁`).

```
$ python3 scratchpad/T2277/p1.py
samples 300000 violations of generalized target 2/3 pointwise facts: 0 {'case1_u<=t0': 49364, 'case2_t0<u': 250636, 't0<1-c1': 194969, 't0>=1-c1': 105031}
case t0<u example: t0=1/2<1-c1=2/3=s=u; Tp forced = 1/2 ; tau''= 1/2 ; s<=tau''? False ; min(t0,s)<=tau''? True
forced: 1/2 <=Tp<= 1/2
mono_max violations: 0
target 9 range violations: 0
```

The probe's conclusion `s ≤ τ''` is false in case 2 (`1/2 ≥ 2/3` fails); the generalized `min(t0,s) ≤ τ''` is what holds (rows 4, 5).

P3: whitespace-normalised text diff of the merged pins against the probe (`t/T2205` = 96e4087, `git show` text of `RBM3D/Probe/T2205Pins.lean`).

```
$ bash scratchpad/T2277/p3.sh
BAFlowMember: EQUAL (whitespace-normalised)        # Step1Boot.lean:133-139 vs probe :1796-1803
BATrivialLmax: EQUAL (whitespace-normalised)       # Step1Trivial.lean:139-145 vs probe :1779-1785
```

P4: instance numbers and the eventual thresholds (limit computations of the deterministic hypotheses).

```
$ python3 scratchpad/T2277/p4.py
max_n lam^2 L^3 = 1/64 (= 1/64 at n=0)
Im m_S >= 1.2/(1.44+1/64) = 0.8243881494203521 >= 41/50: True ; (4/5 only gives t0>=2/3: 2/3 )
t0 >= (41/50)/(6/5) = 0.6833333333333333 >= 17/25: True >= 2/3: True < 1 (Im z>0)
loss 6*(3/640)/(3/5)^4 = 0.2170138888888889 ; budget = 0.8170138888888889 <= 41/50: True ; floor 3/5 >= kappa=1/2: True
c1= 1/3 : 1-sqrt(1-c1) = 0.18350341907227397 <= 3/10: True
c1= 1/2 : 1-sqrt(1-c1) = 0.2928932188134524 <= 3/10: True
sqrt(s/u) = 0.9901475429766743 in [sqrt(2/3)= 0.816496580927726 , 1]: True ; s<u: True ; u<=t0 bound 17/25: True
c_kappa(1/2) = 0.5773502691896257 ; kappa' = 0.28867513459481287 <= kappa; eps'=1/20
(s,t)= ('1/2', '2/3') s1= 2/3 u-range [ 2/3 , 2/3 ]; 0<=s<t<=t0(>=41/60): True ; 1/2<=s1: True ; u<1: True ; u<=max(t0,s1): True
(s,t)= ('0', '1/16') s1= 2/3 u-range [ 2/3 , 2/3 ]; 0<=s<t<=t0(>=41/60): True ; 1/2<=s1: True ; u<1: True ; u<=max(t0,s1): True
$ python3 scratchpad/T2277/p4b.py
con_st_ind (s,t)=(0.5,0.6667) cd=1/100: ratio=0.6667; last failing n=7 (eventually true from n=8)
con_st_ind (s,t)=(0,0.0625) cd=1/100: ratio=0.9375; last failing n=-1 (eventually true from n=0)
kappa'=0.2887; N_0^(-1/20)=0.4830; last n with N^(-eps/2)>=kappa': 0 => n0 = 1
N_0^(-9/10) = 2.044e-06 <= 11/30 = 0.3667
```

(`p4b.py` uses `Bctl_n(t) = W^{−3}[(g² + 1 − t)^{−1} + (L³(1−t))^{−1}]`, i.e. `Bparam d L g t 0` with `K = 0`, `d = 3`, from `Defs/Sizes.lean:214`, `Defs/Params.lean:36`.)
At `n ≥ 8` both `STConStInd` are met at `𝔠d = 1/100` (eventual, as the definition requires; the instance takes `s1Setup_conStInd_const` / `conStInd_inst`).

P2: walk of target 9 through `BABootstrap'` (`Step1Boot.lean:148-166`) and `BAConArg''` (`ConArg.lean:70-76`), with `z3 = (n < n₀ ? z : z')` from `BAFlowMember` at `z' ∈ Fam(t) ⊆ Fam(0)`.
- `BABootstrap'` premises at `z'`: `Fam(t)`, `s ≤ t0`, `s < t`, `t ≤ t0`, `STConStInd`: premises of `BAStep1`; `STKboundgL`, `STLKgL`, `STLocalMaxgL` of `z'` at `s`: the family premise at `z' ∈ Fam(s)` (`Fam(t) ⊆ Fam(s)`, `s ≤ t`).
- ConArg premise for each `u ∈ [s₁, max(t, 1−c₁)]`, to be shown at `z3 ∈ Fam(u)` (`z ∈ Fam(u)` main; `z' ∈ Fam(u)` by `max(u,1−c₁) ≤ max(t,1−c₁)`; pointwise modification stays in `Fam(u)`): `BAFlow sz κ' ε' 𝔠 𝔡 z3` (`BAFlowMember`); `ε₁ = 1/2 ≤ s₁` (row 1); `s₁ ≤ u`; `u < 1` (row 2);
  `κ' ≤ κ ≤ Im m(E, g_s)` from target 2 at `z3` (premises: `0 ≤ lam`, `0 < t0 < 1`, `1−c₁ ≤ s₁ ≤ u ≤ max(t0, s₁)`, `E(z3) = E(z)`, `min(t0, max(u,1−c₁)) ≤ T(z3) ≤ t0`: all from `z3 ∈ Fam(u)` and row 2);
  `STLmaxgL` at `s₁` of the carrier with coupling `BAlamS sz z3 s₁ u`, equal pointwise (target 2, conclusions 4–6) to `baFMz sz zs`, `zs = BAzSrc sz z3 s₁ u ∈ Fam(s₁) ⊆ Fam(s) ⊆ Fam(0)` (target 3 then monotonicity): at `s` from `BALmaxFromLK` (`τ = s`, `0 ≤ s < 1`, `Bctl ≤ 1` row 9, `STKboundgL` and `STLKgL` of `zs` from the family premise at `zs ∈ Fam(s)`), at `1 − c₁` from `BATrivialLmax` (`zs ∈ Fam(0)`), joined by `STLmaxgL_max` (row 11).
- `BAConArg''` returns for every `C₀ > 0` the loops at `(z3, s₁, u)` and `BAConArgVec` (independent of `C₀`; take `C₀ = 1`); `z3 n = z' n` for `n ≥ n₀`, so both transfer to `z'` by the tail congruences (targets 6, 7), which are exact since each quantity at index `n` is a function of `z n` alone.
- Every hypothesis of `BABootstrap'` is supplied; no new hypothesis beyond `BAStep1`'s own. Conclusions `STStep1LoopgL`, `STStep1WeakgL` of `baFMz sz z'`: those of `BABootstrap'`.

Optional extra nondegenerate instance of case 2 of targets 2–3 (the listed instances only exercise case 1, since `u = 2/3 < t0` at `c₁ = 1/3`): along `sz0`, `t0 ∈ [41/60, 25/36]` (`Im z ≥ 11/30`, `zSeq_im_ge`), so `c₁ = 1/10`, `s = u = 9/10 > t0`:

```
$ python3 scratchpad/T2277/p5.py
t0 in [41/60, 25/36] = [0.6833, 0.6944]; u=s=9/10 > t0: True; u<=max(t0,s): True
window c1=1/10: 1-sqrt(1-c1)=0.0513 <= 3/10: True ; forced Tp=t0, tau''=t0 (s/u=1); min(t0,s)=t0<=tau'': True
```
(`sz0_win` at `c₁ = 1/10`, `κ = 1/2`: same proof as at `1/3`, `ρ = 3/10`.)

External hypotheses: `BAGbEXPii`, `BAGbEXPij` (owed, BA-G6) are universally quantified pins over all `(sz, z, t, ε₀)`; no concrete limit computation applies to them and none is claimed here; they and the family premise stay hypotheses of `inst_baStep1`, `inst_baStep1_low`, as the ticket states.

### Verdicts
- Targets 1 (`BAm_self_of_im_pos`, `BAtauS`, `BAzSrc`, `BAlamS_eq`, `*_congr`): PASS.
- Target 2 `BAzSrc_spec` generalized (P1, decisive): PASS in both cases (rows 4–8; script 0 violations).
- Target 3 `BAFamZ_closed` generalized: PASS (`min(t0, max(s, 1−c₁)) = min(t0,s) ≤ τ''`, `τ'' ≤ t0`, `E` preserved).
- Target 4 `BAFamZ_mono_max`: PASS.
- Targets 5–8 (`FlowFM.EqAt/EvEq`, congruences, `PrecL_ite`, `STLmaxgL_max`, pins `BAStep1`, `BALmaxFromLK`, `BAConArgLoop''_congr`): PASS.
- Target 9 `BAStep1_of_parts'` (P2): PASS.  Target 10 `baStep1_holds`: PASS (conditional on `BAGbEXPii/ij`, §90).
- Targets 11–12 (`BAmember_dom_at`, `BAFlowMember_holds`, `BALmaxFromLK_holds`; P3 verbatim equality): PASS; constants rows 12–13, 10.
- Instances (P4): PASS; `mS_im_ge` must be re-proved at `41/50` (rows 14–16 close only with `41/50`, not the merged `4/5`).

## (b) Script output (stage 1b)

```
$ date -u
Tue Oct  6 10:08:04 UTC 2026
$ git log --oneline -1 t/T2277; git diff --stat main...t/T2277
4632a75 T2277: BA-S3 BA/Step1Fam (BAStep1 family assembly, BAFlowMember_holds, BALmaxFromLK_holds, baStep1_holds)
 RBM3D/BA/Step1Fam.lean | 1028 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |    2 +-
 2 files changed, 1029 insertions(+), 1 deletion(-)
$ grep -nwc "sorry\|admit\|native_decide\|axiom" RBM3D/BA/Step1Fam.lean
0
$ lake build RBM3D.BA.Step1Fam 2>&1 | grep -v "^trace" | tail -3  (after touch)

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3757 jobs).
$ lake env lean scratchpad/T2277/precheck.lean  (import RBM3D; import RBM3D.BA.Step1Fam; #assert_rbm_axioms)
exit 0
axiom audit: 8096 theorems, 2643 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
non-vacuity certificates: 0 of 150 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/In
$ grep -c BAFlowMember scratchpad/T2277/precheck.out
0
$ owed entries (text count of owedProps) main vs branch
/Users/junyin/Lean_proof/RBM3D/RBM3D/Test/Axioms.lean 149
RBM3D/Test/Axioms.lean 148
$ full lake build with `import RBM3D.BA.Step1Fam` added to RBM3D.lean temporarily (restored afterwards; the hub adds the import at merge)
non-vacuity certificates: 0 of 150 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4085 jobs).
lake build  40.16s user 4.33s system 103% cpu 42.798 total
$ full lake build with RBM3D.lean unchanged (branch state): fails with exactly one unclassified premise, BAFlowMember, whose proof is in the not-yet-imported module
error: RBM3D.lean:321:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.BA.BAFlowMember]
$ lake env lean scratchpad/T2277/axioms.lean   (#print axioms of the 63 new public declarations)
exit 0
declarations printed: 63
lines other than [propext, Classical.choice, Quot.sound]: 0
'RBM.BA.BAm_self_of_im_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzSrc_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_mono_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAConArgLoop''_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAConArgVec_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STLmaxgL_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep1_of_parts'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFlowMember_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BALmaxFromLK_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.sz0_win' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_BAFamZ_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_conArg_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_BAFlowMember' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_BALmaxFromLK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_baStep1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_baStep1_low' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_baBootstrap'_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Targets (statements extracted by script from `RBM3D/BA/Step1Fam.lean`, whitespace-normalised, up to `:= by`):

```
$ python3 scratchpad/T2277/extract.py <target names>
L48: theorem BAm_self_of_im_pos {d L : ℕ} [NeZero L] {g : ℝ} {z : ℂ} (h : 0 < (BAm d L g z).im) : BASelf d L g z (BAm d L g z)
L85: theorem BAzSrc_spec (sz : Sizes d) (z z' : ℕ → ℂ) (c₁ κ : ℝ) (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hwin : BAWinBulk sz z c₁ κ) (s u : ℕ → ℝ) (n : ℕ) (hlam : 0 ≤ sz.lam n) (hT0 : 0 < BAflowT0 sz z n) (hT1 : BAflowT0 sz z n < 1) (hs : 1 - c₁ ≤ s n) (hsu : s n ≤ u n) (hu : u n ≤ max (BAflowT0 sz z n) (s n)) (hE : BAflowEs sz z' n = BAflowEs sz z n) (hlo : min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n) (hhi : BAflowT0 sz z' n ≤ BAflowT0 sz z n) : min (BAflowT0 sz z n) (s n) ≤ BAtauS sz z' s u n ∧ BAtauS sz z' s u n ≤ BAflowT0 sz z n ∧ κ ≤ (BAm d (sz.L n) (BAlamS sz z' s u n) (BAflowEs sz z' n : ℂ)).im ∧ BAflowT0 sz (BAzSrc sz z' s u) n = BAtauS sz z' s u n ∧ BAflowEs sz (BAzSrc sz z' s u) n = BAflowEs sz z' n ∧ BAflowLam0 sz (BAzSrc sz z' s u) n = BAlamS sz z' s u n
L158: theorem BAFamZ_closed (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hlam : ∀ n, 0 ≤ sz.lam n) (hwin : BAWinBulk sz z c₁ κ) (hT0 : ∀ n, 0 < BAflowT0 sz z n) (hT1 : ∀ n, BAflowT0 sz z n < 1) (s u : ℕ → ℝ) (hs : ∀ n, 1 - c₁ ≤ s n) (hsu : ∀ n, s n ≤ u n) (hu : ∀ n, u n ≤ max (BAflowT0 sz z n) (s n)) (z' : ℕ → ℂ) (hz' : BAFamZ sz z c₁ u z') : BAFamZ sz z c₁ s (BAzSrc sz z' s u)
L172: theorem BAFamZ_mono_max (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u t : ℕ → ℝ) (z' : ℕ → ℂ) (hut : ∀ n, max (u n) (1 - c₁) ≤ max (t n) (1 - c₁)) (h : BAFamZ sz z c₁ t z') : BAFamZ sz z c₁ u z' := fun n => ⟨(h n).1, le_trans (min_le_min le_rfl (hut n)) (h n).2.1, (h n).2.2⟩
L297: theorem BAConArgLoop''_congr (sz : Sizes d) (z₁ z₂ : ℕ → ℂ) (h : ∀ᶠ n in atTop, z₁ n = z₂ n) (s t : ℕ → ℝ) (k : ℕ) (C₀ : ℝ) : (BAConArgLoop'' sz z₁ s t k C₀ ↔ BAConArgLoop'' sz z₂ s t k C₀)
L310: theorem BAConArgVec_congr (sz : Sizes d) (z₁ z₂ : ℕ → ℂ) (h : ∀ᶠ n in atTop, z₁ n = z₂ n) (s t : ℕ → ℝ) : (BAConArgVec sz z₁ s t ↔ BAConArgVec sz z₂ s t)
L335: theorem STLmaxgL_max (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s : ℕ → ℝ) (c : ℝ) (h₁ : STLmaxgL C μ s) (h₂ : STLmaxgL C μ (fun _ => c)) : STLmaxgL C μ (fun n => max (s n) c)
L421: theorem BAStep1_of_parts' (d : ℕ) (hmem : BAFlowMember d) (hL : BALmaxFromLK d) (hT : BATrivialLmax d) (hC : BAConArg'' d) (hB : BABootstrap' d) : BAStep1 d
L624: theorem BAFlowMember_holds (d : ℕ) : BAFlowMember d
L665: theorem BALmaxFromLK_holds (d : ℕ) : BALmaxFromLK d
L695: theorem baStep1_holds (d : ℕ) : BAGbEXPii d → BAGbEXPij d → BAStep1 d := fun hii hij => BAStep1_of_parts' d (BAFlowMember_holds d) (BALmaxFromLK_holds d) (BATrivialLmax_holds d) (baConArg''_holds d) (baBootstrap'_holds d (BAFlowMember_holds d) hii hij)
```

Compiled nonempty instances in the same file (namespace `RBM.BA.Step1FamInst`; statements extracted by script):

```
$ python3 scratchpad/T2277/extract.py <instance names>
L723: theorem mS_im_ge (L : ℕ) [NeZero L] (g : ℝ) (h : g ^ 2 * (L ^ 3 : ℕ) ≤ 1 / 64) : 41 / 50 ≤ (mS L g).im
L748: theorem t0_sz0_ge (n : ℕ) : (17 / 25 : ℝ) ≤ BAflowT0 sz0 zSeq n
L769: theorem sz0_win (c₁ ρ : ℝ) (hρ : 1 - Real.sqrt (1 - c₁) ≤ ρ) (hρ' : ρ ≤ 3 / 10) : BAWinBulk sz0 zSeq c₁ (1 / 2)
L820: theorem inst_BAFamZ_closed : BAFamZ sz0 zSeq (1 / 3) (fun _ => 2 / 3) (BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)) :=
L921: theorem inst_conArg_lt (C₀ : ℝ) (hC₀ : 0 < C₀) : (∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25) k C₀) ∧ BAConArgVec sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)
L952: theorem inst_BAFlowMember : ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ 1 / 2 ∧ 0 < ε' ∧ ε' ≤ 1 / 10 ∧ ∃ n₀ : ℕ, BAFlow sz0 κ' ε' (1 / 6) (1 / 10) (fun n => if n < n₀ then zSeq n else BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25) n)
L962: theorem inst_BALmaxFromLK : STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) → STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI → STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI :=
L982: theorem inst_baStep1 : BAGbEXPii 3 → BAGbEXPij 3 → (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) sI z' → STKboundgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) ∧ STLKgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sI ∧ STLocalMaxgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sI) → STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧ STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI :=
L1000: theorem inst_baStep1_low : BAGbEXPii 3 → BAGbEXPij 3 → (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) sInst z' → STKboundgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) ∧ STLKgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sInst ∧ STLocalMaxgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sInst) → STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sInst tInst ∧ STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sInst tInst :=
L1018: theorem inst_baBootstrap'_full (hii : BAGbEXPii 3) (hij : BAGbEXPij 3) (hK : STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0))) (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) : STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧ STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI :=
```

`example`s at lines (`grep -n '^example' RBM3D/BA/Step1Fam.lean`): 827 839 847 862 877 880 890 894 899 946 975: second closure step `(2/3)` from `(203/300)`; `BAFamZ_closed` at `c₁ = 1/10`, `s = u = 9/10` (case `t₀ < u`); `BAzSrc_spec` at `n = 0` in case `u ≤ t₀` and in case `t₀ < u` (with `t₀_0 ≤ 25/36 < 9/10` shown by `t0_sz0_le`); `BAFamZ_mono_max` at the source member; `BAConArgVec_congr`, `BAConArgLoop''_congr` along the modification `zMod` (differs from `zSeq` for `n < 3`); `BAm_self_of_im_pos`; `STLmaxgL_max`; `BAWinBulk_of_dom_holds` along `sz0`.
Hypotheses left in the instances: `BAGbEXPii 3`, `BAGbEXPij 3` (owed pins, BA-G6), the family premise (`STKboundgL`, `STLKgL`, `STLocalMaxgL`), and `STKboundgL`, `STLKgL` in `inst_BALmaxFromLK`; the window `BAWinBulk sz0 zSeq c₁ (1/2)` is proved (`sz0_win`), `STConStInd` by `s1Setup_conStInd_const` / `conStInd_inst`, `BAConArg''` and `BATrivialLmax` premises discharged (`inst_conArg_lt`: no hypothesis).

Text diffs and statement checks:

```
$ python3 scratchpad/T2277/textdiff_compact.py
36 probe-verbatim declarations compared with probe T2205Pins.lean @96e4087 (whitespace-normalised):
 whole text EQUAL (32): BAm_self_of_im_pos, BAtauS, BAzSrc, BAlamS_eq, BAflowT0_congr, BAflowEs_congr, FlowFM.EqAt, FlowFM.EvEq, FlowFM.EqAt.GM, STLKgL_congr, STLmaxgL_congr, STDecaygL_congr, STDecayStronggL_congr, STLocalMaxgL_congr, STLocalEntrygL_congr, STExp2gL_congr, STKboundgL_congr, STStep1LoopgL_congr, STStep1WeakgL_congr, baFM_eqAt, baFMz_eqAt, BAlamS_congr, HighProbAt_congr, PrecL_ite, BAStep1, BALmaxFromLK, Bctl_le_one_of_conStInd, BAFamZ_ite, cκ, cκ_pos, cκ_le_one, BAmember_dom_at
 statement EQUAL, proof differs only by `show`->`change` (2): BAFlowMember_holds, BALmaxFromLK_holds
 statement differs only in binder explicitness, to match the check file (2): BAConArgVec_congr, STLmaxgL_max (BAConArgVec_congr: z₁ z₂ explicit, same body; STLmaxgL_max: sz explicit, and the unused simp argument `max_eq_left hA` dropped)
vocabulary against docs/tickets/checks/T2277-check.lean (whitespace-normalised text): BAtauS: differs (check has {d : ℕ} binder; rfl example below), BAzSrc: differs (check has {d : ℕ} binder; rfl example below), cκ: EQUAL, BALmaxFromLK: EQUAL, BAStep1: EQUAL
$ lake env lean scratchpad/T2277/stmts.lean   (check file with `import RBM3D.BA.Step1Fam`, plus 22 `example`s: `rfl` for BAzSrc, BAtauS, cκ, BAStep1, BALmaxFromLK; `fun ... => RBM.BA.X ...` for BAzSrc_spec, BAFamZ_closed, BAFamZ_mono_max, BAConArgLoop''_congr, BAConArgVec_congr, STLmaxgL_max; `RBM.BA.BAStep1_of_parts' d`, `baStep1_holds d`, `BAFlowMember_holds d`, `BALmaxFromLK_holds d`; instance statements mS_im_ge, t0_sz0_ge, sz0_win, inst_conArg_lt, inst_BALmaxFromLK, inst_baStep1, inst_baStep1_low against check section 4)
exit 0
$ python3 scratchpad/T2277/clash.py
63 new public names (theorem|def|structure) in RBM3D/BA/Step1Fam.lean; names with a declaration of the same short name elsewhere in RBM3D/ (outside Step1Fam.lean): 0 []
```

Ports: all from the compiled probe `t/T2205:RBM3D/Probe/T2205Pins.lean` at `96e4087` (cited per declaration in the docstrings and the file header); nothing is ported from RBM1D or RBM2D, so there is no RBM1D/RBM2D diff-stat.

Narrative:
- `RBM3D/BA/Step1Fam.lean` has 1028 lines (`git diff --stat` above); sections 1 to 6 follow the ticket; `baStep1_holds` is placed after section 5 because it uses `BAFlowMember_holds` and `BALmaxFromLK_holds`.
- New relative to the probe: `BAzSrc_spec` and `BAFamZ_closed` in the §86 form (hypotheses `0 < t₀(z)`, `u ≤ max(t₀, s)`, first conclusion `min(t₀, s) ≤ τ''`; case `t₀ < u` forces `u = s`, `s/u = 1`, `T' = t₀` in the proof); `BAFamZ_mono_max`; `BAConArgLoop''_congr`; `BAStep1_of_parts'` (event form, hypotheses `BAConArg'' d`, `BABootstrap' d`); `baStep1_holds`; the instances of section 6.
- The probe's conclusion `s ≤ τ''` fails when `t₀ < u` (section (a), P1 script: `s<=tau''? False ; min(t0,s)<=tau''? True`); the generalized statement is what is proved.
- `BAStep1_of_parts'` supplies `BABootstrap'` as in the D581 map of the ticket: `STKboundgL`, `STLKgL`, `STLocalMaxgL` of `z'` at `s` come from the family premise `hmemb z' hz's` and are passed to `hB` only; `hmemb zs` (the source member) feeds `BALmaxFromLK` (`hLs`); `BAConArg''` is applied to the finite modification `z3` of `z'`, never to `z'`.
- `baStep1_holds` is conditional on the owed `BAGbEXPii d`, `BAGbEXPij d` (§90): a conditional assembly, not an unconditional proof of Step 1.
- `mS_im_ge` is proved at `41/50` (the merged `mS_im_half` gives `4/5`; `t0_sz0_ge` needs `41/50`, section (a) row 14); `sz0_win` is proved at `κ = 1/2` (final step `1/2 ≤ 3/5`).
- Registry (`RBM3D/Test/Axioms.lean`, text-anchored): the `BAFlowMember` line of `owedProps` deleted; `RBM.BA.FlowFM.EvEq` added to `structuralProps` (the first pre-check run, before the edit, reported `[RBM.BA.FlowFM.EvEq]` as unregistered); the pre-check now exits 0, `BAFlowMember` not listed, owed lines 149 on main, 148 on the branch.
- The full `lake build` of the branch as committed fails with the single unclassified premise `BAFlowMember` (its theorem is in the module that `RBM3D.lean` does not import yet); with the one line `import RBM3D.BA.Step1Fam` added to `RBM3D.lean` temporarily (not committed, file restored) it completes with 4085 jobs; the hub adds that import at merge.

## (c) Verified Mathlib names (`#check` in scratchpad/T2277/names.lean, all resolve)

`div_le_one`, `le_div_iff₀`, `div_le_iff₀`, `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_pow_of_le_one`, `Real.sqrt_le_sqrt`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_le_one`, `Real.sqrt_mul`, `max_eq_left`, `max_eq_right`, `min_le_min`, `lt_min`, `max_lt`, `Filter.eventually_atTop`, `Filter.Eventually.of_forall`, `mul_le_mul_of_nonneg_right`, `div_self`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `tendsto_rpow_neg_atTop`, `tendsto_rpow_atTop`, `norm_le_norm_sub_add`, `Complex.div_ofReal_im`.
Names verified absent: none checked.

## (d) Open issues and paper-delta candidates

- Open: `BAGbEXPii`, `BAGbEXPij`, `BAGbEXPav` stay owed (BA-G6); `STKboundgL`, `STLKgL`, `STLocalMaxgL` stay owed and are hypotheses of `BAStep1`; `RBM3D.lean` needs `import RBM3D.BA.Step1Fam` at merge (hub, CLAUDE.md §3 (A) 4); `BAStep1` for every member is not yet unconditional.
- **T2277a**: the ConArg step of Step 1 (`7_8:1956-1990`) is used from `s₁ = max(s, 1 - c₁)` up to `max(t, 1 - c₁)`; when `t₀(z) < 1 - c₁` the ConArg source is the target itself (`u = s₁`, `s₁/u = 1`), which the paper does not mention (Lean: `BAzSrc_spec` case `t₀ < u`).
- **T2277b** (D581, family form): in `BAStep1` the premises `STKboundgL`, `STLKgL` are used for the ConArg source member (through `BALmaxFromLK`), not for `z'`; `s ≤ t₀(z)` is passed to `BABootstrap'` but unused in `BAStep1_of_parts'` apart from that, and `s < t` is used only to obtain `s n < 1` (`hs1`) and passed on.
