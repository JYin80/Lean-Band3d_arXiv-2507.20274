Auditor model: claude-opus-5-5
# T2172 audit (round 1) — S5-08 `res_deccalE_wG` (`RBM3D/Path/LemDecCalEwG.lean`)
Time (`date -u`): Mon Oct  5 05:21:46 UTC 2026.  Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2172-audit1` (detached at `t/T2172` = `ac6a3f6`). Scratch: scratchpad `T2172/` (`sdiff.py`, `AuditT2172.lean`, `PrecheckT2172.lean`, logs).

**Verdict: PASS** (all four targets).

## 1. Scope of the diff
```
$ git diff --stat main...t/T2172 ; git log --oneline main..t/T2172
 RBM3D/Path/LemDecCalEwG.lean | 2510 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2510 insertions(+)
ac6a3f6 T2172: LemDecCalEwG docstring: sources of the square-root convolution and line cites
c3e8b95 T2172: S5-08 res_deccalE_wG (E2HypWG, lossE2wG, LemDecCalE_wG, lemDecCalE_wG, sqrt convolution, hyp_zero)
$ grep -n '^import' RBM3D/Path/LemDecCalEwG.lean
6:import RBM3D.Path.LemDecCalE
```
Only the sole writable file (new); `Test/Axioms.lean` untouched; no frozen signature touched. Only merged module imported (no cycle).

## 2. Build, hygiene, axioms
```
$ lake build RBM3D.Path.LemDecCalEwG
✔ [3781/3781] Built RBM3D.Path.LemDecCalEwG (26s)
Build completed successfully (3781 jobs).
$ grep -nE 'sorry|admit|native_decide|\baxiom\b|implemented_by|extern|unsafe|opaque' RBM3D/Path/LemDecCalEwG.lean
(no output)
$ lake env lean AuditT2172.lean        # (import RBM3D.Path.LemDecCalEwG; check-file section 2; rfl checks below)
'RBM.Path.lemDecCalE_wG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_sum_sqrt_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_hyp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEwG_inst_CL' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Path.lossE2wG : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ
exit=0
$ lake env lean PrecheckT2172.lean     # import RBM3D; import RBM3D.Path.LemDecCalEwG; #assert_rbm_axioms
exit=0
axiom audit: 5308 theorems, 1878 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines mentioning E2HypWG/LemDecCalE_wG/lossE2wG: 0
```
Public names (all others `private`): `E2HypWG lossE2wG LemDecCalE_wG LemDecCalEwG_sum_sqrt_tail lemDecCalE_wG LemDecCalEwG_hyp_zero LemDecCalEwG_inst LemDecCalEwG_inst_CL`; `git grep -lw <name> main -- 'RBM3D/*.lean'`: 0 hits each.

## 3. Statements against the pins
```
$ python3 sdiff.py
E2HypWG: branch 6 lines, check 6 lines, identical: True
LemDecCalE_wG body vs Shape body (loss d -> lossE2wG d): 9 vs 9 identical: True
exact (outer paren of loss*(...) removed): True     # RHS vs Step5Pins.lean:170-177, u:=p.1, a:=p.2.2, J:=Jst n u D
```
Kernel check (in `AuditT2172.lean`, compiled exit 0 above, check-file section 2 pasted verbatim):
```
example (d : ℕ) : @RBM.Path.E2HypWG d = @RBM.Path.T2172Check.E2HypWG d := rfl
example (d : ℕ) : RBM.Path.LemDecCalE_wG d = RBM.Path.T2172Check.LemDecCalE_wGShape d RBM.Path.lossE2wG := rfl
```
Paper `3_5:2322-2325` (`res_deccalE_wG`): `(1−u)⁻¹[1(|a₁−a₂| ≤ (log W)^{3/2}) + (W^d|1−u|)^{-1/2}(J*)^{3/2}] T_{u,D}`, every `σ ∈ {±}²`; the Lean RHS has the same indicator radius, the power `1/2` of `(W^d|1−u|)⁻¹`, `J^{3/2}` (rpow), `STtailTD` at `u`, and `∀ σ : Fin 2 → Bool`. The `≺` is replaced by an explicit loss under a deterministic premise bundle (the S5-05 design, D374–D377).

**Target 1 (vocabulary).** `E2HypWG` = check file (identical text and `rfl`). `lossE2wG d L W Λ K₀ = lossE2 d L W Λ K₀ * (1000^d * (1 + log (L^d W^{6d}))^{2d})`: the pinned shape with closed form `κ_wG d = 1000^d`; polylog in `N` times the `lossE2` factor. `LemDecCalE_wG` = shape body with `loss := lossE2wG` (`rfl`). PASS.

**Target 2 (`LemDecCalEwG_sum_sqrt_tail`, `:318`).**
```
theorem LemDecCalEwG_sum_sqrt_tail {d L : ℕ} [NeZero L] (hd : 1 ≤ d) {A w : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ w) (hfl : w * (L : ℝ) ^ (2 * d) ≤ A) (a₀ a₁ : Zd d L) :
    ∑ x : Zd d L, Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
        Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
      5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * Real.sqrt A *
        Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w)
```
Hypotheses exactly the ticket's (`1 ≤ d`, `0 ≤ A`, `0 ≤ w`, `w L^{2d} ≤ A`, any `a₀ a₁`); `[NeZero L]` is the standing condition for `Zd d L` sums; `C_sq(d) = 5(1+24576d⁴)^d` explicit. PASS.

**Target 3 (`lemDecCalE_wG (d : ℕ) : LemDecCalE_wG d`, `:1995`).** Pinned type, all `d` (with `3 ≤ d` inside `E2Hyp`), all `σ : Fin 2 → Bool`, all `a`; `J^{3/2}`. `J ≤ W` (M3) is not used by name:
```
$ for each `obtain ⟨hd3, …, h9, hJ1,` in the file, the next line:      # lines 982 1103 1226 1257 1306 1356 1419 1618 2004 2348
-, hLK, hK14, hK15⟩ := hE|h          (10/10: the `J ≤ W` slot is `-`)
$ grep -n 'J ≤ ((sz.W n' RBM3D/Path/LemDecCalEwG.lean
2239:    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :          # premise of target 4 only
```
PASS.

**Target 4 (`LemDecCalEwG_hyp_zero`, `:2233`).**
```
theorem LemDecCalEwG_hyp_zero (sz : Sizes d) (n : ℕ) {E D Λ K₀ J : ℝ} (hd : 3 ≤ d)
    (hE : |E| < 2) (hlam : 0 < sz.lam n) (hlam1 : sz.lam n ^ 2 ≤ 1)
    (hlamW : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hΛ : 1 ≤ Λ) (hK : 1 ≤ K₀)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hfloor : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
    E2HypWG sz n E 0 D Λ K₀ J (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
```
Compared with merged `LemDecCalE_e2Hyp_zero` (`LemDecCalE.lean:1321-1327`): identical premise list except `hfloor` replaced by `(L^dW^{6d})² ≤ W^D` (the ticket's instruction; `L^dW^{2d} ≤ W^D` derived at `:2250-2256`); `1 ≤ Λ` is the ticket's first option. The three-loop conjunct is proved exactly at `M = 0`, `u = 0` (`lemDecCalEwG_STLM_zero_three`, `‖𝓛^{(3)}‖ ≤ W^{-2d}`). PASS.

## 4. Hidden hypotheses, vacuity, cycles
- `E2HypWG` is a `Prop`-valued conjunction (`E2Hyp ∧ floor ∧ three-loop`), no structure; every premise is visible in the pin. No new `structure`/`class` in the file.
- Non-vacuity: `E2HypWG` is inhabited at two nondegenerate data sets (§5), `LemDecCalEwG_inst` (`L = 8, W = 1024`) and `LemDecCalEwG_inst_CL` (`L = 2·24⁵, W = 2²⁴`, the `szCL` sequence, `L_n → ∞`).
- New premises vs consumer (§29 (7), ticket Consumers paragraph): the three-loop clause ← `STLmaxU` (`Step34Pins.lean:176`) at `k = 3`; the floor `(L^dW^{6d})² ≤ W^D` has **no** `STIngR5` source (`Step5Pins.lean:163` gives only `size ≤ W^D`). This is a pinned premise that the ticket itself lists as "missing" for S5-09; it is not a defect of T2172 (observation O1 below). Limit check: for `L ≤ W^C`, `(L^dW^{6d})² ≤ W^{2d(C+6)}`, so the floor holds for every fixed `D ≥ 2d(C+6)`, consistent with the paper's "large enough `D`"; checked numerically at the `szCL` data (`2^{1007.55} ≤ 2^{1008}`, compiled in `LemDecCalEwG_inst_CL`).
- No cycle: the module imports only `RBM3D.Path.LemDecCalE` (merged, 6e63fbc); the `Step2Iterate`/`Split` lemmas it needs are copied as `private lemDecCalEwG_*`.

## 5. Compiled nonempty instances (all in `LemDecCalEwG.lean`, built in §2)
| endpoint | instance (line) | data | hypotheses |
|---|---|---|---|
| `LemDecCalEwG_hyp_zero` | `LemDecCalEwG_inst` `:2283` | `sz0`, `n=1`: `d=3, L=8, W=1024, lam=1/4096, E=1/2, u=0, D=38, Λ=K₀=J=1, M=0` | all discharged (`norm_num`, `exp 1 < 2.7182818286`, floor `2^{378} ≤ 2^{380}` in ℕ-powers) |
| `LemDecCalEwG_hyp_zero` | `LemDecCalEwG_inst_CL` `:2313` | `szCL`, `n=0`: `L=2·24⁵, W=2²⁴, lam=1, D=42, Λ=2` | all discharged (`szCL_*_real`, `log 2` bounds) |
| `lemDecCalE_wG` | `example` `:2388` (+ RHS `> 0` `:2401`, indicator `= 1` branch `:2442`) | `(a)`, `σ = ![true,true]`, `a = ![0, Pi.single 0 1]` | premise = `LemDecCalEwG_inst` |
| `lemDecCalE_wG` | `example` `:2411` (+ RHS `> 0` `:2424`, `¬(100 ≤ ℓ*)` far branch `:2459`) | `(b)`, `σ = ![true,false]`, `a = ![0, Pi.single 0 100]` | premise = `LemDecCalEwG_inst_CL` |
| `LemDecCalEwG_sum_sqrt_tail` | `example` `:2490` | `d=3, L=8, A=2^{-60}, w=2^{-380}, a₀=0, a₁=Pi.single 0 1` | `w L^6 = 2^{-362} ≤ 2^{-60}` proved |

No `N = 0`, empty index, collapsed window or `False` premise; witnesses are moderate (largest `W = 2²⁴`). `M = 0` is the data prescribed by the ticket (instances (a)–(c)). Matches ticket items (a)–(d) exactly. PASS.

## 6. Paper-delta coverage
Lean/paper differences and their coverage:
| difference | coverage |
|---|---|
| deterministic `E2Hyp`-bundle form with explicit loss in place of `≺` and `W^D ≥ N`; `M_u = W^d(1−u)`, `tailTD` | D374, D376, D377 (S5-05, merged) |
| three-loop premise `‖𝓛^{(3)}‖ ≤ Λ M_u^{-2}` (not in `E2Hyp`) | candidate T2172a |
| floor `(L^dW^{6d})² ≤ W^D` (stronger than D374 and the paper's `W^D ≥ N`) | candidate T2172b |
| every `σ ∈ {±}²` (paper: yes; RBM2D: `(+,−)`) | candidate T2172c |
| `J^{3/2}` (paper: yes; RBM2D pin: `J²`) | candidate T2172d |
| `lossE2wG = lossE2 · 1000^d (1 + log P)^{2d}` | candidate T2172e |
| `C_sq(d) = 5(1+24576d⁴)^d` under `w L^{2d} ≤ A` | candidate T2172f |
| `J ≤ W` not used | candidate T2172g |
All differences covered. PASS.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The floor conjunct of `E2HypWG` has no source in `STIngR5` (ticket Consumers paragraph and prove report (d)); S5-09 must supply it (extends T2164 M1), together with T2164's M2 (`GijGEX` conjunct) and M3 (`J ≤ W`, still a conjunct of `E2Hyp` though unused here). For the dispatcher's S5-09 ticket, not a T2172 defect.
- O2. Three `set_option maxHeartbeats` raises (`:1600` 1000000, `:1772` 400000, `:1989` 1000000), each scoped with `in`.
- O3. At `M = 0` the left sides of the `lemDecCalE_wG` examples are `0`; the examples test that the hypotheses are satisfiable and the branches are exercised, not sharpness (stated in the prove report).
- O4. Module length 2510 lines (estimate 1600–1800).
- O5. Prove report's pre-check count (5120 theorems) differs from this audit's (5308) because the audit cache is from the current `main`; both runs exit 0.

## Per-target verdict
| target | verdict |
|---|---|
| 1 `E2HypWG`, `lossE2wG`, `LemDecCalE_wG` | PASS |
| 2 `LemDecCalEwG_sum_sqrt_tail` | PASS |
| 3 `lemDecCalE_wG` | PASS |
| 4 `LemDecCalEwG_hyp_zero` | PASS |
Overall: **PASS**. No dispatcher sign-off needed for T2172 itself (O1 goes to S5-09).
