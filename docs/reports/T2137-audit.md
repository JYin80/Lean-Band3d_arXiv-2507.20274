Auditor model: claude-opus-5-5

# T2137 audit (round 1) — S3-08 `Induction/SEforLn1`: `stSEforLn_part1`, `stSEforLn_part2`

Written: Sun Oct  4 15:54:31 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2137-audit1`, detached at `2a7a856` (t/T2137).

## 1. Diff scope and hygiene
```
$ git diff --name-only main...HEAD
RBM3D/Induction/SEforLn1.lean
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide" RBM3D/Induction/SEforLn1.lean; echo grep-exit=$?
grep-exit=1
$ grep -nE "^(theorem|lemma|def|abbrev|instance)" RBM3D/Induction/SEforLn1.lean   # public declarations
466:theorem stSEforLn_part1 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
702:theorem stSEforLn_part2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
$ git -C ~/Lean_proof/RBM3D grep -c "stSEforLn_part" main -- RBM3D; echo exit=$?   # name clash on main
exit=1
```
Only the sole writable file is touched (`Test/Axioms.lean` untouched; the one new hypothesis Prop `STAvgU` is already registered, `Test/Axioms.lean:117`). No merged file changed, so no frozen signature changed. All other declarations are `private SEforLn1_*`.

## 2. Build and axioms
```
$ lake build RBM3D.Induction.SEforLn1
151:✔ [3768/3768] Built RBM3D.Induction.SEforLn1 (4.3s)
153:lake build RBM3D.Induction.SEforLn1  10.58s user 4.75s system 227% cpu 6.731 total
Build completed successfully (3768 jobs).
lake build RBM3D.Induction.SEforLn1  10.58s user 4.75s system 227% cpu 6.731 total
exit=0
$ lake env lean scratchpad/T2137/ax.lean   (#print axioms, #check)
'RBM.Gauss.Sizes.stSEforLn_part1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stSEforLn_part2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pin (`STSEforLnConcl`, `Step34Pins.lean:363`; `STSEforLn` = `STIngR d STAny …`, `:456`)

Signatures (`#check`, scratch file `ax.lean`):
```
@stSEforLn_part1 : ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ},
  sz.STFlow κ ε 𝔠 𝔡 z →
    ∀ {s t : ℕ → ℝ},
      (∀ (n : ℕ), 0 ≤ s n) →
        (∀ (n : ℕ), t n ≤ lemT (z n)) →
          sz.STAvgU (STflowE z) s t →
            ∀ (k : ℕ),
              2 ≤ k →
                sz.Prec
                  (fun n p ω => ‖sz.STegt n (STflowE z n) (↑p.1) ω { σ := List.ofFn p.2.1, a := List.ofFn p.2.2 }‖)
                  fun n p ω =>
                  sz.Bctl n ↑p.1 ^ k / etaT (STflowE z n) ↑p.1 *
                    (sz.STXiL n (STflowE z n) (↑p.1) (STn12E k).1 ω * sz.STXiL n (STflowE z n) (↑p.1) (STn12E k).2 ω) ^
                      (1 / 2)
@stSEforLn_part2 : ∀ {d : ℕ},
  3 ≤ d →
    ∀ (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ},
      0 < κ →
        sz.STFlow κ ε 𝔠 𝔡 z →
          ∀ {s t : ℕ → ℝ},
            (∀ (n : ℕ), 0 ≤ s n) →
              (∀ (n : ℕ), s n < t n) →
                (∀ (n : ℕ), t n ≤ lemT (z n)) →
                  ∀ (k l : ℕ),
                    3 ≤ l →
                      l ≤ k →
                        sz.Prec
                          (fun n p ω =>
                            ‖sz.STksimLK n (STflowE z n) (↑p.1) ω l { σ := List.ofFn p.2.1, a := List.ofFn p.2.2 }‖)
                          fun n p ω =>
                          sz.Bctl n ↑p.1 ^ k / etaT (STflowE z n) ↑p.1 * sz.STXiLK n (STflowE z n) (↑p.1) (k - l + 2) ω
```
Script check that, under exactly the hypotheses `STIngR` provides (`3 ≤ d`, `0 < κ`, `STFlow`, `0 ≤ s`, `s < t`, `t ≤ lemT z`, `STStep2Concl … Cd`), the two terms have the types of conjuncts 1 and 2 of `STSEforLnConcl sz (STflowE z) s t` at `k` (`type_of%` ascription; `STAvgU` taken as `h2.2.1` from `STStep2Concl`, `Step34Pins.lean:221`):
```
$ sed -n 5,12p scratchpad/T2137/fit.lean; lake env lean scratchpad/T2137/fit.lean > fit.out 2>&1; echo exit=$?; grep -c error fit.out
example {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 Cd : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (h2 : STStep2Concl sz (STflowE z) s t Cd)
    (hc : STSEforLnConcl sz (STflowE z) s t) (k : ℕ) (hk : 2 ≤ k) : True := by
  have e1 : type_of% ((hc k hk).1) := stSEforLn_part1 sz hflow hs ht h2.2.1 k hk
  have e2 : type_of% ((hc k hk).2.1) := stSEforLn_part2 hd sz hκ hflow hs hst ht k
  trivial
exit=0
0
```
The file itself also checks this by `rfl` (`SEforLn1.lean:792-802`: `stSEforLn_part1 … = (hconcl k hk).1`, `stSEforLn_part2 … = (hconcl k hk).2.1`), compiled in the build above.

Against the paper (`3_5:1017-1027`, `(bEwGn)`, `(eq:KsimL-K)`):
- Part (1): `k ≥ 2` fixed before `Prec`; uniform over `TimeIcc s t × (Fin k → Bool) × (Fin k → Zd d L)` (the paper's `max_{σ,a}`, time uniform as DECISIONS §39 asks); right side `B^k/η · (Ξ̂^𝓛_{n₁} Ξ̂^𝓛_{n₂})^{1/2}` with `B = Bctl = W^{-d}B_{u,0}`, `(n₁,n₂) = STn12E k` = `(k-1,k+1)` even / `(k,k)` odd (`Step34Pins.lean:347`; examples `STn12E 2 = (1,3)`, `STn12E 3 = (3,3)` by `decide`, `SEforLn1.lean:747-748`). Matches `3_5:1020-1023`.
- Part (2): `∀ l, 3 ≤ l → l ≤ k`, right side `B^k/η · Ξ̂^{𝓛-𝒦}_{k-l+2}`. Matches `3_5:1025-1031`.
- Hypotheses: part (1) uses only `STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STAvgU` (= `(Gt_avgbound_flow)`, a conjunct of `STStep2Concl`); part (2) uses `3 ≤ d`, `0 < κ`, `STFlow`, `0 ≤ s < t ≤ lemT z` and no stochastic input (`(wardineq_K)` enters as the merged theorem `stKward_timeIcc`, T2129). Each is a subset of `STIngR`'s hypotheses, so both are at least as strong as the pinned conjuncts; no special case, no conditional adapter.

## 4. Hidden hypotheses, vacuity, cycles
- No new structure, class or `def`: the only public declarations are the two theorems (§1). Hypotheses are explicit in the signatures above.
- Dependencies are merged theorems, axiom-clean (§2): `stContract_holds : ∀ d, STContract d` (T2054, used at `SEforLn1.lean:263`), `stKward_timeIcc` (T2129, `:720`; its signature has only deterministic hypotheses, all discharged from `STFlow` at `:711-718`), `KLK_rotate`, `sum_norm_SB_row`, `SB_isSymm`. No dependency on S3-09 or on `STSEforLn` itself: no cycle.
- The one external input `STAvgU` is a Step-2 pin (owed by the Step-2 chain, registered at `Test/Axioms.lean:117`), i.e. another gate's pin; it is not discharged here, as allowed. Its form (`Prec` of `‖𝓛^{(1)}-𝒦^{(1)}‖` vs `Bctl^1`, uniform in `u`) is the merged pin, not a new hypothesis, so no new limit check is owed by this ticket.

## 5. Compiled nonempty instances (`SEforLn1.lean:735-784`, compiled in §2)
```
$ grep -n "^def sInst\|^def tInst\|^theorem flow_z0\|^def z0" RBM3D/Induction/Defs.lean; grep -n "^theorem sz0_h" RBM3D/Induction/Step34Pins.lean
413:def z0 (n : ℕ) : ℂ := ⟨1 / 2, ((sz0.size n : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))⟩
435:theorem flow_z0 : STFlow sz0 (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0 :=
439:def sInst : ℕ → ℝ := fun _ => 0
440:def tInst : ℕ → ℝ := fun _ => 1 / 16
941:theorem sz0_hs0 : ∀ n, 0 ≤ sInst n := fun _ => le_rfl
942:theorem sz0_hst : ∀ n, sInst n < tInst n := fun n => by simp only [sInst, tInst]; norm_num
943:theorem sz0_ht : ∀ n, tInst n ≤ lemT (z0 n) := fun n => sixteenth_le_lemT n
$ grep -n "stSEforLn_part[12] (by\|stSEforLn_part1 sz0\|^example" RBM3D/Induction/SEforLn1.lean
742:example (n : ℕ) :
747:example : STn12E 2 = (1, 3) := by decide
748:example : STn12E 3 = (3, 3) := by decide
751:example (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) :
757:  stSEforLn_part1 sz0 flow_z0 sz0_hs0 sz0_ht hAvg 2 le_rfl
760:example (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) :
766:  stSEforLn_part1 sz0 flow_z0 sz0_hs0 sz0_ht hAvg 3 (by norm_num)
769:example :
774:  stSEforLn_part2 (by norm_num) sz0 (κ := 1 / 10) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht 3 3
778:example :
783:  stSEforLn_part2 (by norm_num) sz0 (κ := 1 / 10) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht 4 3
792:example {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
798:example {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
```
- Data: `d = 3`, merged `sz0`, `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, window `[0, 1/16]` (`s ≡ 0 < t ≡ 1/16 ≤ lemT z0` by merged `sz0_hst`, `sz0_ht`): a genuine window. The index type is shown nonempty (`:742-744`).
- Part (1) at `k = 2` (`(n₁,n₂)=(1,3)`) and `k = 3` (`(3,3)`): every deterministic hypothesis discharged; `STAvgU sz0 (STflowE z0) sInst tInst` stays a hypothesis (Step-2 pin, allowed by CLAUDE.md §4 step 2).
- Part (2) at `(k,l) = (3,3)` and `(4,3)`: every hypothesis discharged (`3 ≤ 3`, `0 < 1/10`, flow, window), no hypothesis left. `k = 2` is empty for part (2) (`3 ≤ l ≤ 2`), so `(3,3)` is the ticket's requested instance.
- Not degenerate: no `N = 0`, no empty index, no collapsed window, no `False` premise. `sz0` has large `N` but is the merged instance the ticket prescribes; the conclusions are asymptotic `Prec` statements whose proofs do not exploit the size of the witness.

## 6. Paper deltas
- Conclusions are the merged pin's conjuncts verbatim (§3); the pin's own deltas (sum for `max` etc.) belong to T2041 and are not reopened.
- Prove report (d) proposes `T2137a`, `T2137b` (proof details: the cyclic rotations before `(yi2oslxj2)` and `(wardineq_K)`; no statement difference).
- The hypothesis sets are smaller than the paper's setting (part (1): only `(Gt_avgbound_flow)`; part (2): none stochastic). This is a strengthening, not a paper/Lean difference in the result consumed by S3-09; no further candidate needed.

## 7. Observations (no effect on verdict)
- The ticket lists `Loop/KLFinal` among the imports; the file imports `Induction/{Step34Pins,Contract,KDecay,DecayLoopB}` only (KLFinal is reached transitively, build log line 27). No effect.
- Prove report line 1 is `Prover model: claude-sonnet-5-5`; 233 lines (≤ 300).

## Verdict
- `stSEforLn_part1`: **PASS**.
- `stSEforLn_part2`: **PASS**.
- Ticket T2137: **PASS**. No dispatcher sign-off needed.
