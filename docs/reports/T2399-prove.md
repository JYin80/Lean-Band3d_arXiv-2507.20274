Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 00:23:00 UTC 2026

Sources (all on `main` 30abc87, read-only): `BA/KInduct.lean`, `BA/KStep.lean`, `BA/KWardIneq.lean`, `BA/KMolecule.lean`, `BA/KWard.lean`,
`BA/FlowPins.lean`, `BA/GreenSchur.lean`, `Chain/Carrier.lean`, `Induction/Step34Pins.lean`, `Loop/KLInduct.lean`; probe `t/T2360:RBM3D/Probe/T2360Pins.lean:30-140`.

### (i) Exponent table (constants and exponents the targets depend on)

| quantity | value | constraint | slack |
|---|---|---|---|
| `Λ` (coupling window of `BAKBoundAt`) | `𝔡⁻¹ = 10` at `𝔡 = 1/10` | `0 < g₀_n ≤ Λ` eventually (`BAflow_lam0_window`, `GreenSchur.lean:72`) | `g₀ = √t₀ λ ≤ λ ≤ 1/64`; slack `10 - 1/64` |
| `κ` | `1/2` (`flow_sz0`, `FlowPins.lean:1214`) | `κ ≤ Im m_F` (`BAflow_real`, `GreenSchur.lean:59`) | `Im m_S ≥ 4/5` (`FlowPins.lean:1147`): slack `3/10` |
| `t₀_n` | `∈ [17/25, 25/36]` (`Step1Fam.lean:748,753`) | `t₀ ≥ κ/(κ+1) = 1/3` (probe `t0_ge`) | slack `17/25 - 1/3 = 26/75` |
| `c = (κ+1)/κ` | `3` | `1 ≤ c` and `g² ≤ c g₀²` with `g₀² = t₀ g²` (`bparam_comp`: `B(g₀) ≤ c B(g)`) | `c t₀ ≥ 51/25 ≥ 1`; slack `26/25` |
| time `t` / `τ n` | `[0,1)` | `|1-t| = 1-t > 0` (so `B ≥ 0` and `η_t > 0`) | strict `<` is used, no horizon `BAflowT0` |
| loss exponent `s` (`L^s`) | every `s > 0` | `L^s ≤ N^{s/d}` (`Sizes.L_rpow_le`, `Loop/KLFinal.lean:194`), `C ≤ N^{τ/2}` eventually | use `s = d τ/2`: `L^s ≤ N^{τ/2}`, `N → ∞` (`SizeTendsto`) |
| pin constant for `BAKbound` | `C_pin = C c^{k-1}` | `(W^{-d} B(g₀))^{k-1} ≤ (c W^{-d} B(g))^{k-1}` | `k`-dependent, uniform in `n` |
| pin constant for `BAKward` | `C_pin = C c^{k-2}`, `k ≥ 2` | same, exponent `k-2` (`0` at `k = 2`) | `η` is identical on both sides: no `c` on `η` |
| layers for `n ≥ 4` | `2^{|diagonals n|} = 2^{n(n-3)/2}`; `n=4: 4`, `n=5: 32`, `n=6: 512` | prefactor `((W^d)⁻¹)^{n-1}` is layer independent (`baK_eq_sum_Kpi`) | constant depends on `n` only |
| `n ≤ 3` bounds | `BAKBoundAt d n Λ κ`, `n = 1,2,3` | `baKBoundAt_one` (no `hd`), `baKBoundAt_two/three` (`3 ≤ d`, `0<Λ`, `0<κ`) | merged |
| Ward premises | `KWardIneq_IndAt d k Λ κ`, `3 ≤ k ≤ n` | from `KWardIneq_IndAt_of_abs (KStep_baIndStepAbs_holds k hd hk hΛ hκ)` | all `k ≥ 3`, no hypothesis left |
| `W` | `≥ 1`, `W^d` in `(W^d η)⁻¹` | `sz.W_pos` | none needed |

**Findings on the ticket text (no change to any target):**
- F1. For `n ≤ 3` the merged bounds are `baKBoundAt_one/two/three` (`KInduct.lean:270, 291, 425`), already of type `BAKBoundAt d n Λ κ`. `baKsol_one/two/three` (`:77, 88, 105`) are the identities they use.
- F2. Two meanings of `BAKward`. `BA/KWard.lean:31,304` (K02) uses "`BAKward`" for the Ward identity on `BAKsol` (`baK_ward`, `KWard.lean:305`, band: `KLK_ward`, `Loop/KLWard.lean:1318`). Ticket target 3 defines `BAKward d` as the flow-level pin `STKwardgL (baFMz sz z) (seqP (sz.withLam 0))`. Plan: keep target 3 (`BAKward d` is the pin). In the Q5 table `KLK_ward ↦ baK_ward` (K02, public) with `BAKsol_isKLoopS` and `baKsol_two` as inputs; no new identity theorem. `grep` finds no declaration `BAKward` on `main`.
- F3. The probe's `BAKbound_of_uniform` takes `U` with no `3 ≤ d`, but `baKBoundAt_two/three` need `hd`. So `U` must be `3 ≤ d → ∀ Λ κ n, 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt d n Λ κ` (the `hd` is introduced by `BAKbound`'s own `3 ≤ d →`). Same for `BAKward_of_uniform`.

### (i-b) Statements (full hypotheses)

**T1** `baKBoundAt_holds (d : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∀ n : ℕ, 1 ≤ n → BAKBoundAt d n Λ κ`.
`BAKBoundAt d n Λ κ` (`KInduct.lean:55`): `∀ τ > 0, ∃ C > 0, ∀ L ≥ 3, ∀ W ≥ 1, ∀ g ∈ (0, Λ], ∀ E m, BAReal d L g κ E m → ∀ t ∈ [0,1), ∀ σ a,
‖BAKsol d L W (BAMsigma d L (BAMB d L g E m)) (PropSpin m) t (KLloopOf d L σ a)‖ ≤ C L^τ (W^{-d} Bparam d L g t 0)^{n-1}`.

**T2** `BAKbound d := 3 ≤ d → ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∀ 𝔠 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STKboundgL (baFMz sz z) (seqP (sz.withLam 0))`
(`STKboundgL`, `Carrier.lean:147`: `∀ τ, 0 ≤ τ n < 1 → ∀ k ≥ 1, PrecL sz μ (‖C.K n (τ n) σ a‖) ((sz.Bctl n (τ n))^{k-1})`);
`BAKbound_of_uniform (d) (U : 3 ≤ d → ∀ Λ κ n, 0<Λ → 0<κ → 1≤n → BAKBoundAt d n Λ κ) : BAKbound d`; `baKbound_holds (d) : BAKbound d`.

**T3** `BAKward d := 3 ≤ d → ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∀ 𝔠 sz z, BAFlow sz κ ε 𝔠 𝔡 z → STKwardgL (baFMz sz z) (seqP (sz.withLam 0))`; `baKward_holds (d) : BAKward d`.
Input: `baWardIneq_holds (d n) (hd : 3 ≤ d) (hn : 2 ≤ n) (hΛ) (hκ) (hInd : ∀ k, 3 ≤ k → k ≤ n → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ) : BAWardIneqAt d n Λ κ` (`KWardIneq.lean:1183`); `BAWardIneqAt` at `KWardIneq.lean:93`.

### (ii) Layer decomposition for `n ≥ 4` (merged source)

`baK_eq_sum_Kpi` (`BA/KMolecule.lean:133`; from `baTreeRep`, `KTreeRep.lean:1709`, and the fibres of the tree set, `KMolecule.lean:110` `baKpi_eq_sum_SigmaPi` for the first stage):
`BAKsol(KLloopOf σ a) = ((W:ℂ)^d)⁻¹^{n-1} * ∑_{π ∈ (diagonals n).powerset} BAKpi d L n (BAMsigma ..) t σ a π` (`3 ≤ n`, `[NeZero n]`, `BAReal`, `t ∈ [0,1)`).
Each layer: `baKpiBoundAt_holds (d n) (hd) (hn : 3 ≤ n) (hΛ) (hκ) : BAKpiBoundAt d n Λ κ` (`KStep.lean:597`), `‖BAKpi‖ ≤ C L^τ B^{n-1}`.
Triangle inequality gives constant `2^{|diagonals n|} C` with `((W^d)⁻¹)^{n-1} B^{n-1} = (W^{-d}B)^{n-1}`: the BA twin of `KLInduct_BoundAt_of_Kpi` (`Loop/KLInduct.lean:1154`), whose proof is the same computation. `n = 4`: `diagonals 4 = {(0,2),(1,3)}`, 4 layers (the crossing layer is empty).

### (iii) `STKwardgL` and the bridge

Proposed text for `Chain/Carrier.lean`, next to `STKboundgL` (section `Generic`, variables `C : FlowFM sz`, `μ`):
```
def STKwardgL : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → ∀ k : ℕ, 2 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
      (fun n p _ => ∑ x : Zd d (sz.L n),
        ‖C.K n (τ n) p.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2 ⟨i, h⟩ else x)‖)
      (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2))
```
`FlowFM.K` takes `Fin k`-indexed `σ a` (`Carrier.lean:59`), while `STKward` (`Step34Pins.lean:229`) uses the list `⟨List.ofFn p.1, List.ofFn p.2 ++ [x]⟩` through `STKI`. So the bridge is **not `Iff.rfl`**: `bandFM_STKward : STKward sz E ↔ STKwardgL (bandFM sz E) (seqP sz)` is an `Iff` proved from the list identity `List.ofFn (fun i : Fin k => if i < k-1 then a i else x) = List.ofFn a ++ [x]` (`2 ≤ k`; `STKloop = KLK .. (KLloopOf ..)`, `Induction/Defs.lean:64`) and `C.eta = etaT` (`bandFM`, `Carrier.lean:186`, definitional).
Site: `Chain/Step2Gen.lean` (its import cone contains `Induction/Step34Pins`, measured below; it holds the other `bandFM_*` bridges). Fallback: `KBound.lean`.
BA side: `baFM.eta n t = etaOf (BAmF ..) t = (1-t) * (BAmF ..).im` (`FlowPins.lean:328`, `GLoopFlow.lean:58`), which is verbatim the factor `((1-t) * m.im)` of `BAWardIneqAt` at `m = BAmF`. Same list identity turns `⟨List.ofFn σ, List.ofFn a ++ [x]⟩` into `KLloopOf d L σ (ext a x)` inside `BAKloop` (`FlowPins.lean:298`).

Reduction (T2, T3): apply `U`/`baWardIneq_holds` at `(L, W, g, E, m) = (sz.L n, sz.W n, BAflowLam0, BAflowEs, BAmF)`; `BAReal` by `BAflow_real` for every `n`; `g₀ ∈ (0, Λ]` eventually by `BAflow_lam0_window`; `ζ ≥ 0` because `Bparam ≥ 0` and `η = (1-τ n) Im m_F > 0` (`Im m_F ≥ κ`); loss `C L^s ↦ ≺` by the law-free `precL_of_loss` (probe, `StochDomAt.of_eventually_empty`); `B(g₀) ≤ c B(g)` by `bparam_comp`.

### (iv) One concrete nondegenerate instance per target

Common data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`), `zSeq` (`FlowPins.lean:1181`), `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`FlowPins.lean:1214`, proved, no hypothesis).
- **T1:** `baKBoundAt_holds 3 (Λ := 10) (κ := P.m0.im) le_rfl _ _ 4 _` at the flow point `P` of `(L, g) = (4, 10)` (`MFixedPoint.lean:893`, `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`, `0 < P.g0 ≤ 10`), `W = 2`, `t = 1/2`, `τ = 1`, `n = 4`, the evaluation at `σ = (+,+,-,+)`, distinct labels. `P.g0` is a `Classical.choose`, so the script tabulates the bound for `g₀ ∈ {0.01, 1, 10}`.
- **T2 (`inst_BAKbound`):** `baKbound_holds 3 le_rfl (1/2) (1/10) (1/10) _ _ _ (1/6) sz0 zSeq flow_sz0`; `U` is discharged (`baKBoundAt_holds`), no hypothesis left. `N_0 = 2097152`.
- **T3:** `baKward_holds 3 le_rfl (1/2) (1/10) (1/10) _ _ _ (1/6) sz0 zSeq flow_sz0`, `BAKward 3`; no hypothesis left (`hInd` from `KWardIneq_IndAt_of_abs`).
- No external hypothesis is used (all inputs are merged theorems), so no limit computation is needed; the only limits are `N → ∞`, `SizeTendsto` (merged `sz0_tendsto`) and the eventual windows, checked below for `n = 0..5`.

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2399/inst.py
c=(k+1)/k = 3  k/(k+1) = 1/3  Lambda=1/dd = 10
n=0 L=4 W=32 lam=1/64 N=2097152 ALL OK
n=1 L=8 W=1024 lam=1/4096 N=549755813888 ALL OK
n=2 L=12 W=7776 lam=1/46656 N=812479653347328 ALL OK
n=3 L=16 W=32768 lam=1/262144 N=144115188075855872 ALL OK
n=4 L=20 W=100000 lam=1/1000000 N=8000000000000000000 ALL OK
n=5 L=24 W=248832 lam=1/2985984 N=212986666247081951232 ALL OK
{3: (0, 1, 0), 4: (2, 4, 2), 5: (5, 32, 5), 6: (9, 512, 9), 7: (14, 16384, 14)}
g0=0.01  B_{1/2,0}=2.030850  W^-d B=0.253856  (W^-d B)^(n-1)=1.636e-02  L^tau=4
g0=1  B_{1/2,0}=0.697917  W^-d B=0.087240  (W^-d B)^(n-1)=6.640e-04  L^tau=4
g0=10  B_{1/2,0}=0.041200  W^-d B=0.005150  (W^-d B)^(n-1)=1.366e-07  L^tau=4
k=2: Ward exponent k-2=0, IndAt premises needed at k'=[]
k=3: Ward exponent k-2=1, IndAt premises needed at k'=[3]
k=4: Ward exponent k-2=2, IndAt premises needed at k'=[3, 4]
{2: (Fraction(3, 1), Fraction(1, 1)), 3: (Fraction(9, 1), Fraction(3, 1)), 4: (Fraction(27, 1), Fraction(9, 1))}
```
"ALL OK" checks, per `n`: `3 ≤ L`, `W ≥ 1`, `λ²L³ ≤ 1/64`, `W^{-d/2+𝔡} ≤ λ ≤ 𝔡⁻¹`, `N^{1/6} ≤ W`, `N^{-1+ε} ≤ Im z ≤ 1` (with `Im z ∈ [11/30, 2/5]` from `Im m_S ∈ [4/5, 5/6]`), `Im m ≥ κ`, `t₀ ≥ κ/(κ+1)`, `g² ≤ c g₀²`, `g₀ ≤ 𝔡⁻¹` (the `Im m_S`, `t₀` ranges are the merged facts cited in the table).

Cone check (command: transitive-import script over `RBM3D/`; scratch `cone.py`-style, no Lean): `Chain/Carrier` 36 modules, `Chain/Step2Gen` 61, `BA/KStep` 103; no `LWExpCert` module in any cone; `Induction/Step34Pins` is in the cone of `Step2Gen` and of `KStep`, and `Step34Pins` does not import `Carrier`, `Step2Gen` or `FlowPins` (no cycle).

### (v) Plan against the stop line 1,300 (`wc -l BA/KBound.lean` + net diff of `Chain/Carrier.lean`)

Estimate (lines): `KBound.lean` ≈ 520 = `baKBoundAt_holds` 45, `precL_of_loss`/`bparam_comp`/`t0_ge` 70, `BAKbound` + `_of_uniform` + `baKbound_holds` 85, list lemma + `BAKward` pieces 130, three instances 60, docstrings 130. `Carrier.lean` net +12; `Step2Gen.lean` +25 (not counted by the stop line). Total ≈ 535 against 1,300 (slack 765). Registry: no K-stage premise is owed (`KWardIneq_IndAt`, `BAKpiBoundAt` absent from `Test/Axioms.lean`, grep empty).
Target 4 (`BAProp5to8`): `grep -rn BAProp5to8 RBM3D` outside `Prop6Path.lean` gives only `FlowPins.lean:20` (a docstring) and `FlowPins.lean:226` (the structure); no theorem or pin takes it as a hypothesis. Verdict: not needed (the bundle is proved, `Prop6Path.lean:1049`).

### Verdict per target
- T1 `baKBoundAt_holds`: PASS (hypotheses `3 ≤ d`, `0 < Λ`, `0 < κ` hold; `n ≤ 3` and `n ≥ 4` inputs all merged).
- T2 `BAKbound`, `baKbound_holds`: PASS (with the `U` shape of F3).
- T3 `STKwardgL`, `bandFM_STKward` (an `Iff` proof, not `Iff.rfl`), `BAKward`: PASS (with F2).
- T4 bundle: PASS (not needed). T5 instances: PASS (data above). T6 table: PASS (see F2 for `KLK_ward`). T7 registry: PASS (nothing owed).

## (a′) Preflight corrections — Sun Oct 11 00:51:52 UTC 2026
- (a) F2 and (v) said no new identity theorem for the Ward identity on `BAKsol`; `docs/tickets/T2369.md:31` and `BA/KWard.lean:304` assign that composite (`baK_ward` at `BAKsol_isKLoopS (baKsolve d)` and `baKsol_two`) to K12. It is added as `KBound_baKsol_ward` (`BA/KBound.lean:312`). No verdict changes.
- (a) (v) planned the list lemma inside `KBound.lean` (estimate 520 lines, `Carrier` net +12); it is `Carrier_ofFn_ext` (`Chain/Carrier.lean:155`), shared by `Step2Gen` and `KBound`; `KBound.lean` has 418 lines, `Carrier` net +23.

## (b) Script output — Sun Oct 11 00:51:52 UTC 2026
Lines: `BA/KBound.lean` 418 + net `Chain/Carrier.lean` 23 = 441 against the stop line 1,300 (first command below).
```
$ wc -l RBM3D/BA/KBound.lean; git diff --numstat 30abc87 HEAD -- RBM3D/Chain/Carrier.lean   # stop line 1,300 = KBound + net Carrier
418 RBM3D/BA/KBound.lean
23	0	RBM3D/Chain/Carrier.lean
$ lake build RBM3D.BA.KBound | tail -1; lake build | tail -1   # (the full build runs #assert_rbm_axioms of RBM3D.lean, the registry pre-check)
Build completed successfully (3780 jobs).
Build completed successfully (4210 jobs).
$ lake env lean ax2.lean   # #print axioms of the 8 new public theorems, grouped by axiom set
[propext, Quot.sound] <- Carrier_ofFn_ext
[propext, Classical.choice, Quot.sound] <- baKBoundAt_holds BAKbound_of_uniform baKbound_holds baKward_holds KBound_baKsol_ward inst_BAKbound bandFM_STKward
$ lake env lean docs/tickets/checks/T2399-check.lean; echo exit $?; grep -c "sorry\|native_decide\|^axiom" KBound Carrier Step2Gen
exit 0
RBM3D/BA/KBound.lean:0 RBM3D/Chain/Carrier.lean:0 RBM3D/Chain/Step2Gen.lean:0 
$ python3 -I extract.py   # statements of the targets, extracted from the files
RBM3D/Chain/Carrier.lean:169
def STKwardgL : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → ∀ k : ℕ, 2 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
      (fun n p _ => ∑ x : Zd d (sz.L n),
        ‖C.K n (τ n) p.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2 ⟨i, h⟩ else x)‖)
      (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2))
RBM3D/Chain/Step2Gen.lean:612
theorem bandFM_STKward : STKward sz E ↔ STKwardgL (bandFM sz E) (Sizes.seqP sz) := by
RBM3D/BA/KBound.lean:85
theorem baKBoundAt_holds (d : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∀ n : ℕ, 1 ≤ n → BAKBoundAt d n Λ κ := by
RBM3D/BA/KBound.lean:196
def BAKbound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))
RBM3D/BA/KBound.lean:213
theorem BAKbound_of_uniform (d : ℕ)
    (U : 3 ≤ d → ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt d n Λ κ) : BAKbound d := by
RBM3D/BA/KBound.lean:245
theorem baKbound_holds (d : ℕ) : BAKbound d :=
RBM3D/BA/KBound.lean:204
def BAKward (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      STKwardgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))
RBM3D/BA/KBound.lean:302
theorem baKward_holds (d : ℕ) : BAKward d :=
RBM3D/BA/KBound.lean:312
theorem KBound_baKsol_ward (d : ℕ) {Λ κ g : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {W : ℕ}
    (hW : 1 ≤ W) (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: μ ++ [!s], a ++ [x]⟩
  ... (the identity continues for 3 more lines)
$ sed -n 333,337p RBM3D/BA/KBound.lean; sed -n 378,385p RBM3D/BA/KBound.lean   # inst_BAKbound, and baKBoundAt_holds at the flow point (n = 4)
/-- **`inst_BAKbound`**: the pin `BAKbound` at `d = 3`, `sz0`, `zSeq`; no hypothesis left. -/
theorem inst_BAKbound :
    STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) :=
  baKbound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0
/-- **`baKBoundAt_holds`** at the flow point, `n = 4` (`n ≥ 4`: the layers), `σ = (+,+,-,+)`, distinct labels, `W = 2`, `t = 1/2`, `τ = 1`:
`|𝒦^{(4)}| ≤ C L^τ (W^{-d} B_{t,0})^{3}`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_holds 3 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) P.real.1.1 4 (by norm_num) 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩
$ grep -n "^example\|^theorem inst_" RBM3D/BA/KBound.lean | cut -d: -f1 | tr "\n" " "   # line of every instance of section 3
334 340 345 348 356 370 380 388 397 406 
$ git grep -cE "(theorem|def) +(baKBoundAt_holds|BAKbound|BAKbound_of_uniform|baKbound_holds|BAKward|baKward_holds|KBound_[A-Za-z_]*|inst_BAKbound|STKwardgL|bandFM_STKward|Carrier_ofFn_ext)( |$)" 30abc87 -- RBM3D | wc -l
0
$ git diff --stat main...t/T2399 | tail -5; ls RBM3D/Loop/KBound.lean RBM3D/BA/KBound.lean   # module names differ
 RBM3D.lean                |   1 +
 RBM3D/BA/KBound.lean      | 418 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/Carrier.lean  |  23 +++
 RBM3D/Chain/Step2Gen.lean |  28 ++++
 4 files changed, 470 insertions(+)
RBM3D/BA/KBound.lean RBM3D/Loop/KBound.lean 
$ python3 -I cone.py RBM3D.BA.KBound RBM3D.Chain.Carrier RBM3D.Chain.Step2Gen
RBM3D.BA.KBound: 107 modules in RBM3D, certificate modules: none
RBM3D.Chain.Carrier: 36 modules in RBM3D, certificate modules: none
RBM3D.Chain.Step2Gen: 61 modules in RBM3D, certificate modules: none
$ grep -c "KWardIneq_IndAt\|BAKpiBoundAt" RBM3D/Test/Axioms.lean; grep -rn BAProp5to8 RBM3D | grep -v Prop6Path.lean | cut -c1-72
0
RBM3D/BA/FlowPins.lean:20:2. the propagator pins `BAProp5 … BAProp5to8`,
RBM3D/BA/FlowPins.lean:226:structure BAProp5to8 (Λ κ c : ℝ) : Prop where
```
Narrative.
- Files: `BA/KBound.lean` (new); `Chain/Carrier.lean` `STKwardgL` (:169) and `Carrier_ofFn_ext` (:155); `Chain/Step2Gen.lean` `bandFM_STKward` (:612); `RBM3D.lean` one import line (the ticket lists it as writable; the branches of T2396 and T2392 did the same).
- Target 1: `baKBoundAt_holds` (`KBound.lean:85`). `n = 1, 2, 3` are `baKBoundAt_one/two/three`; `n ≥ 4` is the private `KBound_of_Kpi`: `baK_eq_sum_Kpi` (`KMolecule.lean:133`) and `baKpiBoundAt_holds` (`KStep.lean:597`), constant `2^|diagonals n| C`, the twin of `KLInduct_BoundAt_of_Kpi`.
- Target 2: `BAKbound` (:196), `BAKbound_of_uniform` (:213), `baKbound_holds` (:245): `BAflow_real`, `BAflow_lam0_window`, private `KBound_B_le` (`B(g₀) ≤ ((κ+1)/κ) B(g)`), private `KBound_precL_of_loss` (the probe's `precL_of_loss`); constant `C ((κ+1)/κ)^(k-1)`.
- Target 3: `STKwardgL`, `BAKward` (:204), private `KBound_BAKward_of_uniform`, `baKward_holds` (:302); `η` is the same on both sides, constant `C ((κ+1)/κ)^(k-2)`; the premises of `baWardIneq_holds` are `KWardIneq_IndAt_of_abs (KStep_baIndStepAbs_holds ..)`. `bandFM_STKward` is an `Iff` proved with `Carrier_ofFn_ext`, not `Iff.rfl`.
- Target 4: outside `Prop6Path.lean`, `BAProp5to8` occurs only in a `FlowPins.lean` docstring (:20) and its structure (:226): not needed. Target 7: no owed K-stage premise (grep 0 in `Test/Axioms.lean`); the full `lake build` passes.
- Target 5: `inst_BAKbound` and the `BAKward` examples apply `baKbound_holds`/`baKward_holds` at `sz0`, `zSeq`, `flow_sz0` with no hypothesis left, then at `τ ≡ 1/2` with `k = 4` resp. `k = 3`; `baKBoundAt_holds` is applied at the flow point `P` of `(3, 4)` for `n = 3, 4, 5`; `KBound_baKsol_ward` at `P`, `n = 4`.

## (c) Verified Mathlib and core names (each quoted as a double-backtick name in `names.lean`, which fails to elaborate for a missing name; module:line from `findDeclarationRanges?`)
Real.rpow_nonneg (Pow.Real:163)  Real.rpow_pos_of_pos (Pow.Real:116)  Real.rpow_add' (Pow.Real:211)  Real.sq_sqrt (Real.Sqrt:177)
tendsto_rpow_atTop (Pow.Asymptotics:37)  Finset.sum_le_sum (Group.Finset:110)  Finset.sum_const (Finset.Basic:636)  Finset.card_powerset (Finset.Powerset:101)
Finset.sum_congr (Finset.Basic:103)  nsmul_eq_mul (Ring.Defs:187)  norm_sum_le (Group.Basic:808)  Complex.norm_natCast (Complex.Norm:114)
pow_le_pow_left₀ (GroupWithZero.Basic:513)  mul_le_mul_of_nonneg_left (GroupWithZero.Defs:225)  div_le_div_iff₀ (GroupWithZero.Basic:1424)  le_div_iff₀ (GroupWithZero.Basic:1128)
abs_pos (Unbundled.Abs:227)  add_halves (Field.Basic:83)  inv_eq_one_div (Group.DivInvMonoid:261)  List.ext_getElem (List.Lemmas:303)
List.getElem_ofFn (List.OfFn:50)  List.length_ofFn (List.OfFn:43)  List.getElem_append (List.Lemmas:1621)  List.ofFn_succ (List.OfFn:80)
Names verified absent: none of the new names (`baKBoundAt_holds`, `BAKbound*`, `baKbound_holds`, `BAKward`, `baKward_holds`, `KBound_*`, `inst_BAKbound`, `STKwardgL`, `bandFM_STKward`, `Carrier_ofFn_ext`) is declared on `30abc87` (the `git grep` count above is 0).

## (d) Open issues and paper-delta candidates
- T2399a (naming, no mathematics). Two statements carry the name `BAKward`: the ticket's flow estimate (`KBound.lean:204`, `STKwardgL` at `baFMz`) and the probe's Ward identity on `BAKsol` (`t/T2360:RBM3D/Probe/T2360Pins.lean:306`; K02's row of the design, 2051 Q5 and `T2369.md:31` mean this one). The identity is `KBound_baKsol_ward` (:312, stem-prefixed because unpinned, rule E). The dispatcher decides the name used in the closing REQ.
- T2399b. `STKwardgL` takes the first `k - 1` labels and sums the last as a `Fin k` vector (`if i < k - 1 then a i else x`); the band `STKward` uses the list `a ++ [x]`. The bridge is an `Iff` with a proof, not `Iff.rfl` as the ticket expected.
- T2399c. `U` of `BAKbound_of_uniform` is `3 ≤ d → ∀ Λ κ n, ..` (the probe's had no `3 ≤ d`): `baKBoundAt_two/three` need it.
- `inst_BAKward` is not a named theorem (rule E, not pinned): the `BAKward` instances are `example`s.
- The instances at `sz0` are `PrecL` statements (asymptotic in `n`); their numeric content is section (a) (iv) and the deterministic examples at `P`.

## Q5 table for the closing REQ (declaration lines from `q5.sh`, a `grep -nE` of the declarations, at `84d1997`)
| band name (outside `Loop/`) | public BA counterpart |
|---|---|
| `KLK_one` (`Loop/KLTree.lean:206`) | `baKsol_one` (`BA/KInduct.lean:77`) |
| `KLK_two` (`Loop/KLTree.lean:211`) | `baKsol_two` (`BA/KInduct.lean:88`), `baKsol_three` (`:105`), K03 `baKsolveLe3_holds` (`BA/KSolve.lean:478`) |
| `KLK_rotate` (`Loop/KLUnique.lean:713`) | `BAKsol_rotate` (`BA/KSolve.lean:619`), K01 `baK_rotate` (`:582`) |
| `KLK_isKLoop` (`Loop/KLTreeDeriv.lean:1049`) | `BAKsol_isKLoopS` (`BA/KSolve.lean:606`) at `baKsolve` (`BA/KTreeRep.lean:1699`) |
| `KLK_ward` (`Loop/KLWard.lean:1318`) | `baK_ward` (`BA/KWard.lean:305`, K02, for any family) and `KBound_baKsol_ward` (`BA/KBound.lean:312`, on `BAKsol`, unconditional); see T2399a |
| `stKbound_of_flow` (`Loop/KLFinal.lean:302`) | `baKbound_holds` (`BA/KBound.lean:245`), pin `BAKbound` (`:196`), carrier form `STKboundgL` (`Chain/Carrier.lean:147`) |
| `stKward_of_flow` (`Loop/KLFinal.lean:308`) | `baKward_holds` (`BA/KBound.lean:302`), pin `BAKward` (`:204`), carrier form `STKwardgL` (`Chain/Carrier.lean:169`) |
| `KLbound_holds` (`Loop/KLFinal.lean:154`) | `baKBoundAt_holds` (`BA/KBound.lean:85`), `BAKBoundAt` for all `n ≥ 1` |
| `lem_pureloop` (K07) | `baPure_loop` (`BA/KPure.lean:813`) |
| `lem_wardineq_K` (K11) | `baWardIneq_holds` (`BA/KWardIneq.lean:1183`) |
| `BATreeRep` (K05b) | `BATreeRep` (`BA/KTreeRep.lean:48`), `baTreeRep` (`:1709`) |
