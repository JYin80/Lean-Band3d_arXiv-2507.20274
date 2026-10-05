Auditor model: claude-opus-5-5

# T2183 audit (round 1), UN-02b `Universality/Step1Cond`: written at the time below
```
$ date -u
Mon Oct  5 07:08:37 UTC 2026
```
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2183-audit1` (detached at `t/T2183` = `4f681fa`). Source: RBM2D `c9a24cf:RBM2D/Universality/Step1Cond.lean` (947 lines), extracted with `git show`.

## 1. Statements against the pin (the RBM2D source with `L W -> d L W`), by script
Script `stmt.py`: it extracts each `theorem` header up to `:=`, normalises the RBM2D text by `(L W : ℕ) -> (d L W : ℕ)`, `X L W -> X d L W`, `Ω L W -> Ω d L W`, and compares.
```
$ python3 stmt.py src.lean RBM3D/Universality/Step1Cond.lean <8 targets>
== gueP_prod_map_ouMat DIFFERS
  RBM2D : ... ((gueP d L W).prod (gueP d L W)).map (ouMat d L W t) = (gueP d L W).map (Xmat d L W)
  RBM3D : ... ((gueP d L W).prod (gueP d L W)).map (fun ω : Ω d L W × Ω d L W => Real.exp (-t / 2) • Xmat d L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω.2) = (gueP d L W).map (Xmat d L W)
== integral_kPoint_ouMat_cond DIFFERS
  RBM2D : theorem integral_kPoint_ouMat_cond (d L W : ℕ) [NeZero L] [NeZero W] (μ : Measure (Ω d L W)) [IsProbabilityMeasure μ] (t : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (hOc : HasCompactSupport O) (E : ℝ) : ∫ ω, kPoint k O E (ouMat_isHermitian d L W t ω).eigenvalues ∂(μ.prod (gueP d L W)) = ∫ ω₁, (∫ ω₂, kPoint k O E (dbmMat_isHermitian d L W (fun i => Real.exp (-t / 2) * (Xmat_isHermitian d L W ω₁).eigenvalues i) (1 - Real.exp (-t)) ω₂).eigenvalues ∂(gueP d L W)) ∂μ
  RBM3D : theorem integral_kPoint_ouMat_cond {d : ℕ} {sz : Sizes d} (M : UNModel sz) (n : ℕ) (t : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (hO : Continuous O) (hOc : HasCompactSupport O) (E : ℝ) : ∫ ω, kPoint k O E (ouMat_isHermitian M n t ω).eigenvalues ∂(ouP M n) = ∫ ω₁, (∫ ω₂, kPoint k O E (dbmMat_isHermitian d (sz.L n) (sz.W n) (fun i => Real.exp (-t / 2) * (M.herm n ω₁).eigenvalues i) (1 - Real.exp (-t)) ω₂).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ
== Step1Cond_gueMatPairing_eq_integral IDENTICAL after L W -> d L W
== Step1Cond_scaledPairing_lipschitz IDENTICAL after L W -> d L W
== Step1Cond_exists_dominating_testFun IDENTICAL after L W -> d L W
== Step1Cond_corrPairing_le_count IDENTICAL after L W -> d L W
== Step1Cond_exists_le_indicator IDENTICAL after L W -> d L W
== Step1Cond_corrPairing_le_count_smul IDENTICAL after L W -> d L W
```
Analysis of the two differences. Both come from the merged pin `ouMat`, which the ticket says to use and not re-declare.
- RBM2D `ouMat` (`c9a24cf:RBM2D/Universality/Pins.lean:59`): `Real.exp (-t / 2) • Xmat L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat L W ω.2`. The RBM3D `gueP_prod_map_ouMat` writes out exactly this matrix with `d` added. The hypotheses (`0 ≤ t`) and the conclusion are the same. **No mathematical difference.**
- Merged RBM3D `ouMat` is indexed by a model (`RBM3D/Universality/Pins.lean:150`: `e^{-t/2} • M.H n ω.1 + √(1-e^{-t}) • Xmat … ω.2`, with `ouP M n = M.μ.prod gueP` at `:145`). `UNModel` (`Pins.lean:104-111`) has the fields `μ`, `prob`, `H`, `herm`, `meas`: a probability law and a measurable Hermitian family, with no hidden mathematical hypothesis. In RBM2D the first block is `Xmat` under an arbitrary `μ` on `Ω L W`; in RBM3D it is an arbitrary measurable Hermitian `M.H n` under `M.μ` on `SeqΩ sz`. This is the paper's Step 1 statement, conditioning on `H` (1_2:566-581), and it is the shape the design fixed: portmap `T2162-portmap.md:196`, "conditioning on H (integral_kPoint_ouMat_cond) … on the abstract UNModel". The RBM2D consumer (`c9a24cf:RBM2D/Universality/Step1Band.lean:22`) uses it at `μ = P` (the band model), which is `UNModel.band` here. The `μ = gueP` use goes through `Step1Cond_gueMatPairing_eq_integral`, whose statement is unchanged. All quantifiers, `t`, `k`, `O`, `E`, `hO`, `hOc` are as in the source.
- Proof route (checked by reading the signatures): both theorems go through the private `Step1Cond_cond_general` (an arbitrary probability space and a measurable Hermitian `H₀`). `integral_kPoint_ouMat_cond` is that lemma at `M.μ`, `M.H n`, with measurability from `M.meas`. The match between `ouMat M n t` and the lemma's integrand is definitional (the proof is an `exact`, which compiles).

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "^(private )?def .*: Prop|^structure|^class" RBM3D/Universality/Step1Cond.lean
grep exit 1          (no new Prop definitions or structures; no registry entry needed)
$ git diff --stat main...t/T2183 -- RBM3D/Test/Axioms.lean RBM3D.lean
(empty)
```
- Imports: only the merged `Universality/{GUEInvariance,EigenMeasurable,OU}` and Mathlib, so there is no cycle. The upstream results used (`gueP_map_unitary_conj`, `integral_kPoint_eq_of_map_eq`, `measurable_kPoint_eigenvalues`) are proved and merged, and their axioms are printed in the build log below.
- No external hypothesis is introduced, so no limit check applies.

## 3. Compiled nonempty instances (namespace `RBM.Univ.Step1CondCheck`, `Step1Cond.lean:916-998`)
`step1Cond_szC : Sizes 3` is the constant sequence `L = 3`, `W = 1`, `lam = 1`, with `three_le_L` and `W_pos` discharged. `step1Cond_card_Idx331 : Fintype.card (Idx 3 3 1) = 27`. The test functions are `step1Cond_hat` (continuous, compact support) and `step1Cond_bump` (a `ContDiffBump`, radii 1 and 2).

| endpoint | instance (data) | hypotheses discharged |
|---|---|---|
| `integral_kPoint_ouMat_cond` | `:916`, `UNModel.band step1Cond_szC`, `n=0`, `t=1`, `k=1`, `O=hat`, `E=0` | `hat_cont`, `hat_cpt` |
| `gueP_prod_map_ouMat` | `:928`, `d=3,L=3,W=1`, `t=1` | `zero_le_one` |
| `Step1Cond_gueMatPairing_eq_integral` | `:936`, `t=1`, `k=1`, `O=bump`, `E=0` | `zero_le_one`, `bump_testFun` |
| `Step1Cond_scaledPairing_lipschitz` | `:947`, `ρmin=1/2`, `ρmax=2`, then applied at `Pm=gueP 3 3 1`, `Hm=Xmat 3 3 1`, `ρ=1`, `ρ'=3/2` | `0<1/2`, `1/2≤2`, measurability, `ρ,ρ'∈[1/2,2]` |
| `Step1Cond_exists_dominating_testFun` | `:964`, `Q=bump`, window `[1/2,2]` | `bump_testFun` |
| `Step1Cond_corrPairing_le_count` | `:971`, `gueP 3 3 1`, `k=1`, `Q=hat`, `R=1` | `1 < 27`, `hat_nonneg`, `hat_le_indicator` |
| `Step1Cond_exists_le_indicator` | `:982`, `Q=bump` | `bump_testFun` |
| `Step1Cond_corrPairing_le_count_smul` | `:987`, `Q=2·hat`, `B=2`, `R=1` | `1<27`, nonneg, `0<2`, `Q≤2·1_{[-1,1]}` |

None of these instances is degenerate: `N = 27`, `k = 1 < N`, a nonzero test function, a window of positive length, and no `False` premise. All of them compile (§4).

## 4. Build, axioms and hygiene (audit worktree)
```
$ lake build RBM3D.Universality.Step1Cond     (error count; Step1Cond lines; tail)
0
⚠ [3348/3348] Built RBM3D.Universality.Step1Cond (10s)
warning: RBM3D/Universality/Step1Cond.lean:21:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Universality/Step1Cond.lean:25:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Universality/Step1Cond.lean:31:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Universality/Step1Cond.lean:33:100: This line exceeds the 100 character limit, please shorten it!
Step1Cond.lean:1002:0: 'RBM.Univ.integral_kPoint_ouMat_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1003:0: 'RBM.Univ.gueP_prod_map_ouMat' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1004:0: 'RBM.Univ.Step1Cond_gueMatPairing_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1005:0: 'RBM.Univ.Step1Cond_scaledPairing_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1006:0: 'RBM.Univ.Step1Cond_exists_dominating_testFun' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1007:0: 'RBM.Univ.Step1Cond_corrPairing_le_count' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1008:0: 'RBM.Univ.Step1Cond_exists_le_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
Step1Cond.lean:1009:0: 'RBM.Univ.Step1Cond_corrPairing_le_count_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3348 jobs).
exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b" RBM3D/Universality/Step1Cond.lean
grep exit 1
$ git diff --name-status main...t/T2183
A	RBM3D/Universality/Step1Cond.lean
$ git merge-base main t/T2183 ; git rev-parse --short main
a34c2171ee368bc47193f473c3fff6c74664c8ad
c2609b9            (main moved by the report-only merge T2173; no conflict with this file)
$ for n in <public names>; do git grep -w $n main -- RBM3D | wc -l; done
gueP_prod_map_ouMat 0 / integral_kPoint_ouMat_cond 0 / Step1Cond_gueMatPairing_eq_integral 0 /
Step1Cond_scaledPairing_lipschitz 0 / Step1Cond_exists_dominating_testFun 0 / Step1Cond_corrPairing_le_count 0 /
Step1Cond_exists_le_indicator 0 / Step1Cond_corrPairing_le_count_smul 0 / step1Cond_szC 0 / step1Cond_hat 0 /
step1Cond_bump 0 / step1Cond_bump_testFun 0 / step1Cond_card_Idx331 0 / step1Cond_measurable_Xmat_331 0
```
The diff touches only the sole writable file. The file adds new declarations only, so no frozen signature is touched. Unpinned helpers are `private` or carry the `Step1Cond_`/`step1Cond_` prefix (§3 (E)).

## 5. Paper-delta coverage
- The two shape differences of §1 (`ouMat` indexed by the model; the explicit matrix in `gueP_prod_map_ouMat`) are proposed as candidate `T2183a` in the prove report §(d). They are not mathematical differences from the paper or from RBM2D. Not yet in `docs/paper-deltas.md` (grep `T2183`: no match); the dispatcher appends it.
- The other six statements are identical to the source after `d`-replacement, so no delta is needed.

## Observations (not RETURN)
- O1. The ticket's acceptance line asks for "only renamings and `d`-replacements". That cannot hold literally for the two targets that mention `ouMat`, because the merged pin `Pins.lean:150` is model-indexed. The adaptation matches the design row UN-02 ("on the abstract UNModel") and is covered by `T2183a`.
- O2. `Step1Cond_cond_general` (any probability space and measurable Hermitian family) is `private`. A consumer that needs conditioning outside a `UNModel` needs it promoted by a new ticket (prove report §(d)).
- O3. RBM2D's `T1Stmt`/`T2Stmt` and their `_holds` theorems are not ported. They were statement checks, not endpoints, and the `example`s replace them.
- O4. Lint warnings for long lines (docstring lines 21-33), even though the file sets `linter.style.longLine false` after the module docstring. These do not affect the build.

## Verdict
| target | verdict |
|---|---|
| `gueP_prod_map_ouMat` | PASS |
| `integral_kPoint_ouMat_cond` | PASS |
| `Step1Cond_gueMatPairing_eq_integral` | PASS |
| `Step1Cond_scaledPairing_lipschitz` | PASS |
| `Step1Cond_exists_dominating_testFun` | PASS |
| `Step1Cond_corrPairing_le_count` | PASS |
| `Step1Cond_exists_le_indicator` | PASS |
| `Step1Cond_corrPairing_le_count_smul` | PASS |

Ticket T2183: **PASS**. No dispatcher sign-off is needed; the dispatcher records `T2183a`.
