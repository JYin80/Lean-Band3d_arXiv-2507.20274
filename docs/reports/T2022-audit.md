Auditor model: claude-opus-5-5

# T2022 audit (EK-1: EK vocabulary, seven EK pins, three bridges) — round 1

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2022-audit1`, detached at `62fe565` (`t/T2022`). Written 2026-10-03 04:30 UTC (`date -u`).
Targets: the pinned text (probe `c961e62:RBM3D/Probe/T2016Pins.lean` lines 44-198), i.e. 3 vocabulary defs, 7 pin defs, 3 endpoint theorems `ekSumNdecay_holds`, `ekPropT_holds`, `ekTTk_holds`; plus the instances.

## 1. Scope of the branch

```
$ git diff --stat main...t/T2022
 RBM3D/Evolution/Pins.lean | 414 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 414 insertions(+)
$ git merge-base main t/T2022 ; git rev-parse --short main
e2aa5fe57cbf682897ad44e940fcb057ddbc42e1   main: e2aa5fe
```
Only the sole writable file (new); no frozen signature touched; branch is based on current `main`.

## 2. Statement: script diff against the pin (probe text at c961e62)

```
$ git show c961e62:RBM3D/Probe/T2016Pins.lean > probe.lean ; git show t/T2022:RBM3D/Evolution/Pins.lean > pins.lean
$ diff <(sed -n 44,198p probe.lean) <(sed -n 40,194p pins.lean); echo "diff exit $?"
diff exit 0
```
Probe lines 44-198 (vocabulary `EKsgn`, `ek_norm_spin`, `EKFastDecay`, `EKSumZero`; pins `EKSumNdecay`, `EKSumDecay1`, `EKSumDecayNAL`, `EKSumDecay2`, `EKSumDecayNonzero`, `EKPropT`, `EKTTk`; bridges with proofs) are copied verbatim; only the placement differs (offset 4 lines).
Helper copied for the instances:
```
$ diff <(sed -n 506,513p probe.lean) <(sed -n 196,203p pins.lean); echo "fin_two diff exit $?"
fin_two diff exit 0
```
Spot check against the paper (statements as pinned by DECISIONS §18):
```
3_5_Loop_Hierarchy.tex:1620  lem:sum_Ndecay: for any 0≤s≤t<1, ‖U^{(n)}_{s,t,σ}∘A‖_∞ ≤ ((1-s)/(1-t))^n ‖A‖_∞
3_5_Loop_Hierarchy.tex:328   lem:propT: 0≤u≤t<1 with (i) 1-u≥1-t≥λ²/L² or (ii) 1-t≤1-u≤λ²/L²: Σ_c T_u T_t ≤ C_d/(1-u) T_t
7_8_light_weight.tex:1662    claim:TTk: 1-t ≥ λ²/L², k≥2, 0≤ℓ≤(log W)^{10} ℓ_t, ≺ bound with Ψ_t
```
`EKSumNdecay` = (sum_res_Ndecay), no constant; `EKPropT` keeps both regimes (i),(ii) with `C` depending on `d` only (quantified after `d`, before `L`); `EKTTk` makes `≺` explicit with `C Λ²` (T2016d). Quantifier order: constants after `(d,n,Λ,κ)`, before `L,g,W,ε,D,s,t,m,σ,A` in every pin. Statement: PASS for all ten defs and the three theorems.

## 3. Vacuity, hidden hypotheses, cycles; dependencies

- No structures: every hypothesis is in the signature. The pins' antecedents `Prop5Decay`, `Prop5Short`, `Prop6Diff1`, `Prop8ZeroMode` are other gates' pins (allowed); no theorem of this file assumes an EK pin or `Prop6Diff1`, so no premise enters the axiom registry (ticket, DECISIONS §16, §18).
- The three bridges use only merged theorems, all on `main`:
```
$ git grep -nwE "theorem (norm_UN_le|propT|key_T_reduce_absorbed)" main -- RBM3D
main:RBM3D/Kernel/Evolution.lean:157:theorem norm_UN_le (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1)
main:RBM3D/Kernel/PropT.lean:409:theorem propT (k : ℕ) :
main:RBM3D/Kernel/PropT.lean:1056:theorem key_T_reduce_absorbed {L : ℕ} [NeZero L] {W g t : ℝ} (hW : 0 < W) {k n : ℕ}
```
- Signatures (from `#check`, see §5): `norm_UN_le` has exactly the hypotheses of `EKSumNdecay` (`‖EKsgn m σ i‖ = 1` from `ek_norm_spin`); `propT k` is `EKPropT (k+2)` verbatim; `key_T_reduce_absorbed` gives `keyC k n * (3 * Λ²·…)`, closed by `C = 3 * keyC k n` and `ring`. No circularity (Evolution/Pins imports only Kernel.SumDecay, Propagator.Prop5Short).
- Public names grepped on `main` (all 0 hits):
```
EKsgn 0  EKFastDecay 0  EKSumZero 0  EKSumNdecay 0  EKSumDecay1 0  EKSumDecayNAL 0  EKSumDecay2 0
EKSumDecayNonzero 0  EKPropT 0  EKTTk 0  ekSumNdecay_holds 0  ekPropT_holds 0  ekTTk_holds 0
ek_norm_spin 0  ek_sum_fin_two 0
```

## 4. Compiled nonempty instances

Instance section vs probe lines 861-1076:
```
$ diff <(sed -n 6,222p probeInst.lean) <(sed -n 205,410p pins.lean)     # probeInst = probe 855-1080
2d1 / 3a3,4   (section header text "(item 9)" dropped)
139,150d139   (probe ekInstDecay1 omitted: it applies ekSumDecay1_two, the EK-2 skeleton)
```
Instances present (all `private theorem`, compiled):
```
339: ekInstNdecay   -- ekSumNdecay_holds 3 2 at L=5, g=1/2, m=I, σ=(+,-), s=1/2, t=9/10, A=ekA0=δ_0 (no hypotheses left)
387: ekInstPropT    -- ekPropT_holds 3 at L=5, g=1/2, u=1/2, t=9/10, regime (i) (1/100 ≤ 1/10), a=0, b=ekE=(1,0,0)
397: ekInstTTk      -- ekTTk_holds 3 2 at L=5, W=25, g=1/2, t=9/10, ℓ=Λ=1, D = ℓ¹-ball radius 1 about 0 (nonempty), x=(0,e), y=(e,0)
346: ekInstNAL      -- pin as hypothesis (+ Prop5Decay 3 1); Prop5Short discharged by prop5Short_holds; σ=(+,+)
359: ekInstDecay2   -- pin (+ Prop5Decay, Prop6Diff1) hyp.; EKSumZero ekAz, EKFastDecay ekAz, log 5 ≤ 25^{1/2} discharged
374: ekInstNonzero  -- pin (+ Prop8ZeroMode) hyp.; window s=0.995, t=0.999 ≥ 1-g²/L²=0.99, A=univ ⊇ I_diff
268: ek_far_point_exists -- far premise of (deccA0) is inhabited: W^ε ℓ_s = 5·1 ≤ zdistD((2,2,1)) = 5
276/288/316: ek_fastDecay_A0, ek_fastDecay_Az, ek_sumZero_Az
```
Every deterministic hypothesis of the three endpoint theorems is discharged at concrete data: `d=3`, `n=2`, `L=5`, `g=1/2>0`, nonzero tensors, `t<1`, nonempty `D`. Not degenerate (no `N=0`, empty index, collapsed window, `False` premise; `W=25` is moderate). `ekInstTTk` uses `n=2`, so `Ψ_t^{n-2}=1`; `n=2` is the paper's minimum `k≥2` — nondegenerate. Instances: PASS.

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.Evolution.Pins 2>&1 | grep -E "error|warning|sorry|Build completed|✖"
Build completed successfully (2544 jobs).
EXIT 0
$ lake env lean ax.lean
'RBM.ekSumNdecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekPropT_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekTTk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_norm_spin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_sum_fin_two' depends on axioms: [propext, Classical.choice, Quot.sound]
@norm_UN_le : ∀ {d L : ℕ} [inst : NeZero L] {g : ℝ}, 3 ≤ L → ∀ {n : ℕ} {m : Fin n → ℂ}, (∀ (i : Fin n), ‖m i‖ = 1) →
  ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t < 1 → ∀ (A : (Fin n → Zd d L) → ℂ), ‖UN d L g m s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖
propT : ∀ (k : ℕ), ∃ C > 0, ∀ (L : ℕ) [inst : NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
  g ^ 2 / ↑L ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / ↑L ^ 2 → ∀ (a b : Zd (k + 2) L), ∑ c, tailT … ≤ C / (1 - u) * tailT …
@key_T_reduce_absorbed : … 0 < W → 2 ≤ n → 1 ≤ ℓ → 1 ≤ ↑L → 0 ≤ g → t < 1 → g ^ 2 ≤ ↑L ^ 2 * (1 - t) → ℓ ≤ Λ * ellT L g t → …
  ≤ keyC k n * (3 * Λ ^ 2 * ((W ^ (k + 2))⁻¹ / (1 - t))) * (PsiT … ^ (n - 2) * ∏ i, sfT …)
EXIT 0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " pins.lean; echo "forbidden grep exit $?"
forbidden grep exit 1
```
(`ax.lean` = `import RBM3D.Evolution.Pins` + the `#print axioms`/`#check` lines above, in the scratchpad.) Build and axioms: PASS. The full `lake build` with `#assert_rbm_axioms` is run by the hub at merge.

## 6. Paper deltas

Every Lean/paper difference of these statements is one of the signed candidates T2016a-f (DECISIONS §18: `log L ≤ W^ε`; `4 ≤ W^ε`; propT regimes (i)/(ii) only; TTk `D` in an `ℓ`-ball, `ℓ ≥ 1`, explicit `Λ²`; loss-free both-charge nonzero bound; uniform constants in `g ∈ (0,Λ]`, `ℓ¹` distances). The prove report cites them (line 34, 252) and proposes no new candidate; the copied text adds no new difference (diff exit 0). The additional hypotheses `3 ≤ L`, `0 < g`, `‖m‖ = 1` of `EKSumNdecay` are the paper's standing setting (`m` on the unit circle, `λ > 0`), covered by T2016f. Coverage: PASS.

## 7. Observations (no verdict effect)

- O1. `EKSumDecay1` has no instance in this file: the probe's `ekInstDecay1` applies the skeleton `ekSumDecay1_two`, which the ticket assigns to EK-2. Its premise set is a subset of the data discharged in `ekInstNAL` (same `L, g, W, ε, D, s, t, m`, `ekA0`, `ek_fastDecay_A0`), so its hypotheses are jointly satisfiable at that data. EK-2/EK-3 should add the instance.
- O2. `ek_sum_fin_two` and `ek_norm_spin` are public but `ek`-prefixed (CLAUDE.md §3 (E)): compliant.

## Verdict

| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| vocabulary `EKsgn`, `EKFastDecay`, `EKSumZero` | verbatim | none | used in instances; far premise inhabited | ok | T2016f | PASS |
| pins `EKSumDecay1`, `EKSumDecayNAL`, `EKSumDecay2`, `EKSumDecayNonzero` | verbatim | antecedents = other gates' pins | NAL/Decay2/Nonzero compiled; Decay1 see O1 | ok | T2016a,b,e,f | PASS |
| `ekSumNdecay_holds` / `EKSumNdecay` | verbatim | merged `norm_UN_le` | `ekInstNdecay` | ok | — | PASS |
| `ekPropT_holds` / `EKPropT` | verbatim | merged `propT` | `ekInstPropT` | ok | T2016c | PASS |
| `ekTTk_holds` / `EKTTk` | verbatim | merged `key_T_reduce_absorbed` | `ekInstTTk` | ok | T2016d | PASS |

**T2022: PASS.** No dispatcher sign-off needed.
