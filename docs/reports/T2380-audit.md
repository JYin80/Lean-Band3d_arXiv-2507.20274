Auditor model: claude-opus-5-5
# T2380 (BA-K07, `RBM3D/BA/KPure.lean`): stage-2 audit, round 1. Sat Oct 10 12:07:23 UTC 2026

The audit worktree is `/Users/junyin/Lean_proof/RBM3D-wt/T2380-audit1`, detached at t/T2380 = 88476fa. Its merge-base with main is 442d3aa; main is now 306957f (T2381 `BA/KInduct.lean`, which is a disjoint file).
Inputs: the ticket `docs/tickets/T2380.md`; the prove report `docs/reports/T2380-prove.md`; the 1a-audit `docs/reports/T2380-1a-audit.md` (PASS), which fixes the public statements against their consumers.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.KPure ; echo exit $?
✔ [3753/3753] Built RBM3D.BA.KPure (5.8s)
Build completed successfully (3753 jobs).
exit 0
$ grep -cE "KPure.lean:[0-9]+:[0-9]+: (warning|error)" build.out ; grep -c error build.out
0
0
$ lake build RBM3D 2>&1 | grep -E "error:|Build completed"
Build completed successfully (4196 jobs).
$ lake env lean axioms.lean   (import RBM3D.BA.KPure; #print axioms of every public declaration)
baPureB: [propext, Classical.choice, Quot.sound]
baPureRate: [propext, Classical.choice, Quot.sound]
baPureB_one_le: [propext, Classical.choice, Quot.sound]
baPureRate_pos: [propext, Classical.choice, Quot.sound]
baPure_edge: [propext, Classical.choice, Quot.sound]
baSlot_path_le: [propext, Classical.choice, Quot.sound]
baSigmaTree_bound: [propext, Classical.choice, Quot.sound]
baSigmaTree_bound_of_entries: [propext, Classical.choice, Quot.sound]
baSigmaTree_bound_maxDist: [propext, Classical.choice, Quot.sound]
baSigmaPi_empty_bound: [propext, Classical.choice, Quot.sound]
baSig_decay: [propext, Classical.choice, Quot.sound]
baK_pure_eq: [propext, Classical.choice, Quot.sound]
baPure_loop: [propext, Classical.choice, Quot.sound]
$ grep -nE "^(noncomputable )?(theorem|lemma|def|abbrev|structure|class|instance) " KPure.lean   (public declarations)
105 baPureB 110 baPureRate 113 baPureB_one_le 116 baPureRate_pos 205 baPure_edge 377 baSlot_path_le 414 baSigmaTree_bound
537 baSigmaTree_bound_of_entries 551 baSigmaTree_bound_maxDist 589 baSigmaPi_empty_bound 632 baSig_decay 670 baK_pure_eq 813 baPure_loop
$ awk 'NR<852' KPure.lean | grep -nE "^private " | grep -v KPure_     (unpinned helpers outside the instance namespace)
(none)
$ grep -cE "\bsorry\b|\badmit\b|native_decide|\baxiom\b" RBM3D/BA/KPure.lean ; wc -l RBM3D/BA/KPure.lean
0
    1016 RBM3D/BA/KPure.lean        (stop line 2000)
$ git diff --name-status main...t/T2380
A	RBM3D/BA/KPure.lean
$ git grep -nE '\b(baPureB|baPureRate|…|baK_pure_eq|KPureInst)\b' main -- RBM3D RBM3D.lean | wc -l
       0
$ printf 'import RBM3D\nimport RBM3D.BA.KPure\n#assert_rbm_axioms\n' > with.lean; (without the KPure import) > without.lean; lake env lean …
with exit 0
without exit 0
axiom audit: 11012 theorems, 3223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
axiom audit: 11000 theorems, 3221 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
$ lake env lean docs/tickets/checks/T2380-check.lean ; echo exit $? ; grep -c error check.out
exit 0
0
```
Result of section 1: the module builds with no warning or error in the file; the axioms are standard; there is no `sorry`, `admit`, `axiom` or `native_decide`; the diff touches only the sole writable file, and no frozen file is touched; the registry adds no premise (113 vs 113); the check file compiles on the branch.

## 2. Statements: Lean against the 1a-fixed statements and the paper (`A:640-700`)
`python3 -I sig.py RBM3D/BA/KPure.lean …` prints the top-level hypotheses and the conclusion. Conclusions are cut at 330 characters; the full text is at `KPure.lean:205-818`.
```
baPure_edge: HYPS (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ) (hr : BAReal d L g κ E m) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
   CONCL (∀ σ x y, ‖BAMsigma … σ x y‖ ≤ baPureB d Λ κ * exp(-(baPureRate d Λ κ * |x-y|))) ∧ (∀ s x y, ‖BAThetaOf … t s s x y‖ ≤ …) ∧ (∀ s x y, ‖(t:ℂ) * BAThetaOf … t s s x y‖ ≤ …)
baSlot_path_le: HYPS (hF : KLIsTSP F) (hn : 2 ≤ n)
   CONCL zdistD d L (β s - β t) ≤ ∑ e : ↥F ⊕ BAslot F, zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e))
baSigmaTree_bound: HYPS (hd : 2 ≤ d) (hF : KLIsTSP F) (hn : 2 ≤ n) (hr : 0 < r) (hΓ : 0 ≤ Γ) (hprod : ∀ β, (∀ v, β (BAslotLeaf F v) = δ v) → ∏ e, ‖BACactusValEdgeW M t F σ e (β src) (β tgt)‖ ≤ Γ * exp(-(r * T β)))
   CONCL ‖BASigmaTree d L M t F σ δ‖ ≤ Γ * (expC (d - 2) (r / (4 * (n + 2 * (n * n))))) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (zdistD d L (δ i - δ j) : ℝ)))
baSigmaTree_bound_maxDist: HYPS (hd : 2 ≤ d) (hF : KLIsTSP F) (hn : 2 ≤ n) (hB : 1 ≤ B) (hr : 0 < r) (hE : ∀ e x y, ‖BACactusValEdgeW M t F σ e x y‖ ≤ B * exp(-(r*|x-y|)))
   CONCL ‖BASigmaTree d L M t F σ δ‖ ≤ B ^ (n + 3 * (n * n)) * (expC …) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ)))
baSigmaPi_empty_bound: HYPS (hd : 2 ≤ d) (hn : 2 ≤ n) (hB : 1 ≤ B) (hr : 0 < r) (hM : ∀ s x y, ‖M s x y‖ ≤ B * exp(-(r*|x-y|))) (hΘ : ∀ s x y, ‖(t : ℂ) * BAThetaOf M t s s x y‖ ≤ B * exp(-(r*|x-y|)))
   CONCL ‖BASigmaPi d L n M t σ ∅ δ‖ ≤ ((TSP n).card : ℝ) * (B ^ (n + 3 * (n * n)) * (expC …) ^ (n + 2 * (n * n)) * Real.exp (-(r / 4 * (KLmaxDist d L δ : ℝ))))
baSig_decay: HYPS (hd : 3 ≤ d) (hn : 3 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
   CONCL SigDecayAbs d n L (BASig d n L g E m t)
baK_pure_eq: HYPS (hκ : 0 < κ) (hg : 0 < g) (hL : 3 ≤ L) (hr : BAReal d L g κ E m) (ht : t ∈ Set.Ico (0 : ℝ) 1) (hn : 3 ≤ n)
   CONCL BAKsol d L W (BAMsigma …) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a) = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ δ, BASigmaPi d L n (BAMsigma …) t (fun _ => σ₀) ∅ δ * ∏ v, BAThetaOf (BAMsigma …) t σ₀ σ₀ (a v) (δ v)
baPure_loop: HYPS (hd : 3 ≤ d) (hn : 3 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ)
   CONCL ∃ C, 0 < C ∧ ∃ c, 0 < c ∧ ∀ L (hL : 3 ≤ L) W g, 0 < g → g ≤ Λ → ∀ E m, BAReal d L g κ E m → ∀ t, 0 ≤ t → t < 1 → ∀ σ₀ a,
         ‖BAKsol d L W (BAMsigma …) (PropSpin m) t (KLloopOf d L (fun _ => σ₀) a)‖ ≤ C * (((W : ℝ) ^ d)⁻¹) ^ (n - 1) * Real.exp (-(c * (KLmaxDist d L a : ℝ)))
$ sed -n 1050,1053p RBM3D/Loop/KLIndStepA.lean     (the consumer's target shape)
def SigDecayAbs … (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)),
    ‖Sig i σ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d (L i) δ : ℝ)))
$ sed -n 74,76p RBM3D/BA/KMolecule.lean   (BASig = Σ^{(∅)} at the BA data, merged K06)
  BASigmaPi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ ∅ δ
$ grep -n "def BAReal" RBM3D/BA/MFixedPoint.lean
432:def BAReal (g κ E : ℝ) (m : ℂ) : Prop := BASelf d L g (E : ℂ) m ∧ κ ≤ m.im
```
Comparison with the 1a statement table (`T2380-prove.md` (a)(i), audited PASS):
- **`baPure_edge`.** The hypothesis list and the three conjuncts (a) `M(σ)`, (b) `Θ^{ss}` and (c) `tΘ^{ss}` are those of the table. The constants `baPureB = max(max 1 c₀⁻¹)(C₅(1+Λ²))` and `baPureRate = min(min c₀ (log 2)) c_s` are the table's, read at `KPure.lean:105-111`. PASS.
- **`baSlot_path_le`.** The table states the reference-slot form `|β s − β r₀| ≤ T`. Lean proves every pair with factor one, which is stronger, and (a′) 2 records this. PASS.
- **`baSigmaTree_bound`, `_of_entries`, `_maxDist`.** `N₀ = n+2n²`, `E₀ = n+3n²`, `S₀ = expC(d−2)(r/(4N₀))`, the rate `r/4`, the pair form and the `KLmaxDist` form are all as in the table. The `hprod` interface is kept for K08b. PASS.
- **`baSigmaPi_empty_bound`.** It holds for every σ, with the factor `|TSP n|`. PASS.
- **`baSig_decay`.**
  - The conclusion is exactly `SigDecayAbs d n L (BASig …)` and covers every σ, as the ticket's K-b form requires. The constants are uniform over `ι`.
  - The family hypotheses are implied by the `hr` of `indStepAbs_of` (`t i < 1` ⇒ `t i ≤ 1`). This is shown compiled at `KPure.lean:1000-1012`.
  - It is not a special case. PASS.
- **`baK_pure_eq`, `baPure_loop`.**
  - The order is ∃C,c first, then ∀L,W,g,E,m,t,σ₀,a. The factor is `W^{−d(n−1)}`, the decay is `e^{−c·maxdist(a)}`, and σ is constant. This matches `(res_pureKes)` (`A:643-647`) and the 1a fix.
  - The domain is `n ≥ 3` and `t ∈ [0,1)`: see §4. PASS.

## 3. Hidden hypotheses, vacuity, cycles
No `structure`, `class` or `instance` is declared in the file (§1 grep), so no hypothesis is hidden in a field. `IndStepTH` and `SigSumZeroAbs` appear only as hypotheses of the K09b interface example; they are the pins of K12 and K08, other gates. Every input is merged (1a-audit §2 hits, `BAPropM3_of_real`, `baProp5s_of_real`, K06 `baK_eq_sum_Kpi` and `baKpi_eq_sum_SigmaPi`), and KPure is a new leaf module, so there is no cycle. There is no external hypothesis, so no limit check is owed. `BAReal` is satisfiable: `P.real` discharges it in §3a.

### 3a. Compiled nonempty instances (`KPure.lean:852-1014`, namespace `KPureInst`; compiled in the build above)
The datum is the merged flow point `P` of `(d,L) = (3,4)`, with `Λ = 10`, `κ = P.m0.im`, `t = 1/2` and `W = 2`. Every deterministic hypothesis is discharged by `norm_num`, `P.real`, `P.g0_pos`, `P.g0_le` or `decide`. The labels are not collapsed: `example : KLmaxDist 3 4 δ3 = 2 := by decide` and the same for `δ4`.

| target | instance (line) | data |
|---|---|---|
| `baPure_edge` | 877-899 | entry `(0,(1,0,0))` of `M(+)`, `Θ^{−−}`, `tΘ^{++}` |
| `baSlot_path_le` | 905, 909 | `F={(0,2)}`, `n=4`, 6 slots, 7 edges (921: `card = 7`); star `n=3` |
| `baSigmaTree_bound` (core, `hprod` discharged) | 914 | `F={(0,2)}`, `σ=(+,−,+,+)` (chord short), pair (0,2) |
| `baSigmaTree_bound_of_entries` | 926, 932 | `σ=(+,+,+,+)`, `F={(0,2)}`; star `n=3` |
| `baSigmaTree_bound_maxDist` | 939 | `F={(0,2)}`, `σ=(+,−,+,+)` |
| `baSigmaPi_empty_bound` | 946, 950 | `n=3`, `σ=+++`; `n=4`, `σ=+−+−` |
| `baSig_decay` | 955, 963, 1000 | `ι=Unit`, `n=3` (as `SigDecayAbs`); `n=4` applied at `σ=+−+−`, `δ4`; fed to `indStepAbs_of` |
| `baK_pure_eq` | 973, 977 | `n=3,4`, `σ₀=+`, `W=2` |
| `baPure_loop` | 983, 990 | `n=3,4`, `L=4`, `W=2`, `σ₀=+`, `t=1/2` |

There is no `N = 0`, no empty index set, no collapsed window, no `False` premise and no large witness. The constants `B` and `r` are outputs of the theorems (1a-audit O4), not hypotheses. PASS.

## 4. Paper deltas (candidates in `T2380-prove.md` (d))
| difference | coverage |
|---|---|
| `c, C` explicit, depending on `(d,n,Λ,κ)` and uniform in `L ≥ 3`, `g ≤ Λ`, `E`, `m`, `t`, `σ`, `δ`, `W`, `a` (paper: "some `c,C>0`") | T2380a |
| rate `r/4`, not optimal | T2380b |
| BA chord `tΘ^{σσ}` without `−I`; its `1_{x=y}` term is absorbed into `B` | T2380c |
| `n ≥ 3` (paper `lem_pureloop`: every `n`); `t ∈ [0,1)` explicit in `baPure_loop` | T2380d; tree range `n ≥ 3` vs `A:593` `n ≥ 4` already D634 |
| domain `BAReal` (real `E`, `κ ≤ Im m`), `0 < g ≤ Λ` | D626 (T2335c, same domain for `kBA_le`); T2380a names `E, m` |

Every statement difference is covered.

## 5. Observations (no RETURN)
- O1. T2380a could name the `BAReal d L g κ E m` domain explicitly, as D626 does. This is wording only: the coverage exists through D626 and T2380a.
- O2. The ticket lists `BAK_off_le`, `sum_exp_decay_conv`, `sum_exp_decay_centre` and `norm_sum_prod_le` as inputs, but they are unused; the lattice sum uses `BAsum_exp_decay_le`. The imports of `BA.KKernel` and `Loop.PureLoop` are kept as the ticket lists them. This is harmless.
- O3. The branch base is 442d3aa and main is 306957f. The only change on main since then is T2381 (`BA/KInduct.lean`, plus one `RBM3D.lean` import line), which is disjoint from KPure's imports. The hub's full build at merge decides.
- O4. `#edges` enters as the uniform bound `n+3n²`, not the exact count `n+3|F|`. Since `B ≥ 1` this only weakens the constant, and it was fixed in the 1a.

## 6. Verdict
| target | verdict |
|---|---|
| `baPureB`, `baPureRate`, `baPure_edge` | PASS |
| `baSlot_path_le` | PASS |
| `baSigmaTree_bound`, `baSigmaTree_bound_of_entries`, `baSigmaTree_bound_maxDist`, `baSigmaPi_empty_bound` | PASS |
| `baSig_decay` (`SigDecayAbs` at `BASig`, every σ) | PASS |
| `baK_pure_eq`, `baPure_loop` | PASS |
| instances at `P`, `n = 3, 4` | PASS |

**Overall: PASS.** No repair list is needed, and no dispatcher sign-off is needed.
