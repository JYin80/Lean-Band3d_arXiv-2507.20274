Auditor model: claude-opus-5-5

# T2139 audit (round 1), S3-09 `Induction/SEforLn2`: `lem:SEforLn` parts (3), (4), `stSEforLn_holds`
Written Sun Oct  4 17:02:44 UTC 2026 (`date -u`). Branch `t/T2139` at `8ee0941`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2139-audit1` (detached). `main` = `c8e4f17`, merge base `7f82dd6`.

## 1. Diff scope
```
$ git diff --stat main...t/T2139
 RBM3D/Induction/SEforLn2.lean | 1401 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
$ git diff main...t/T2139 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STSEforLn, -- `lem:SEforLn` (DECISIONS §25)
$ git merge-tree --write-tree main t/T2139 >/dev/null; echo merge_tree_exit=$?
merge_tree_exit=0
$ grep -nE "^(noncomputable )?(theorem|lemma|def|abbrev|instance|structure|class) " SEforLn2.lean; grep -c "^private " SEforLn2.lean
1007:theorem stSEforLn_part3 ...
1264:theorem stSEforLn_part4 ...
1287:theorem stSEforLn_holds (d : ℕ) : STSEforLn d := by
56
$ git grep -nE "stSEforLn_part3|stSEforLn_part4|stSEforLn_holds|SEforLn2" main -- RBM3D RBM3D.lean; echo exit=$?
exit=1
```
Only the two sole writable files; the registry edit is the one deletion the ticket orders; no merged
file or frozen signature touched; imports `Induction/SEforLn1`, `Induction/ScaleFacts` (both on `main`, root-imported).

## 2. Statements (pin diff by script)
Script `scratchpad/T2139/stmt.sh`: whitespace-normalise, substitute `(STflowE z n)` → `(E n)`, `diff`
against the merged pin `STSEforLnConcl` (`Step34Pins.lean:363`).
```
$ sh stmt.sh
part3 concl == STSEforLnConcl conj.3 (Step34Pins:374-380), E n := STflowE z n
part4 concl == STSEforLnConcl conj.4 (Step34Pins:381-385), E n := STflowE z n
```
The file also contains two `rfl` examples (`stSEforLn_part3 … = (hconcl k hk).2.2.1`,
`stSEforLn_part4 … = (hconcl k hk).2.2.2`), which compile (§4), so the conclusions are the pinned conjuncts definitionally.

* **`stSEforLn_part3`** hypotheses: `3 ≤ d`, `0 < κ`, `0 < Cd`, `0 < 𝔠d`, `𝔠d * Cd ≤ 1/30`, `STFlow`, `0 ≤ s`,
  `s < t`, `t ≤ lemT z`, `STConStInd sz 𝔠d s t`, `STGdecayW sz (STflowE z) s t Cd`; then `∀ k ≥ 2`.
  A subset of the `STIngR` hypotheses (as the ticket allows: "take only those the proof uses"), plus
  `𝔠d·Cd ≤ 1/30`, which is a constraint on the existential `𝔠d` of `STIngR` and is discharged in the assembly.
  Range `n' ∈ Icc ((k+1)/2+1) (k-1)` = `⌈k/2⌉+1..k-1`, `B^k η⁻¹`, `B^{1/6}`, `STn12` as in paper `3_5:1035-1039`.
* **`stSEforLn_part4`** hypotheses: `STFlow`, `0 ≤ s`, `t ≤ lemT z`; `∀ k ≥ 2, ∀ q ≥ 1`; exponent
  `2k − 1/(2q)`, `Ξ_{2k-1} Ξ_{4q}^{1/(2q)}` as in paper `3_5:1043-1045` (sum over the `k` cut edges: the merged pin's convention, D54).
  Fewer hypotheses than the pin context: a stronger statement.
* **`stSEforLn_holds (d : ℕ) : STSEforLn d`** is the pin itself, unconditional:
```
  refine ⟨min (1 / 100) (1 / (30 * Cd)), h𝔠d, min_le_left _ _, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht _ _ _ _ hcon hStep2 k hk
  exact ⟨stSEforLn_part1 sz hflow hs ht hStep2.2.1 k hk, stSEforLn_part2 hd sz hκ hflow hs hst ht k,
    stSEforLn_part3 hd sz hκ hCd h𝔠d hcc hflow hs hst ht hcon hStep2.2.2 k hk,
    stSEforLn_part4 sz hflow hs ht k hk⟩
```
  Quantifier order of `STIngR` kept (`Cd` before `∃ 𝔠d`, `𝔠d` before `sz, z, s, t`); `𝔠d = min(1/100, 1/(30 Cd))`
  as ticket; `STKbound`, `STKward`, `STLK s`, `STAny` unused (underscores), which only weakens the needs.

Paper `lem:SEforLn` (`3_5:1017-1046`, read): hypotheses `(Gt_bound_flow)`, `(Gt_avgbound_flow)`,
`(Eq:Gdecay_w)` = `STStep2Concl`; statement (3), (4) match the pin text above.

## 3. Hidden hypotheses, vacuity, cycles
* No new `structure`/`class`; no hypothesis carried in a field. Inputs: merged `stSEforLn_part1/2` (T2137),
  `stContract_holds`, `stKward_timeIcc` (merged), `STGdecayW` from `STStep2Concl.2.2`. No cycle: the module
  imports only merged modules and no file imports it.
* `STGdecayW` is another gate's pin, registered owed:
```
$ grep -n "STGdecayW" RBM3D/Test/Axioms.lean | cut -c1-90
122:   `RBM.Gauss.Sizes.STGdecayW, -- `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]` (`1_2:1349`, `Step34Pins
```
  Its limit check is in the prove report (a)(ii)(B) (deterministic `K^{(2)}` profile against
  `B_{u,r}e^{-√(r/ℓ)}`, ratios 0.949/0.961/0.764/0.592 at `L = 5, 17`), not re-run here.

## 4. Build, axioms, hygiene (audit worktree)
```
$ date -u; lake build RBM3D.Induction.SEforLn2 2>&1 | grep -E "error|Built RBM3D.Induction.SEforLn2|Build completed"
Sun Oct  4 16:55:10 UTC 2026
✔ [3770/3770] Built RBM3D.Induction.SEforLn2 (7.2s)
Build completed successfully (3770 jobs).
$ lake env lean RBM3D/Induction/SEforLn2.lean > src.out 2>&1; echo exit=$?; grep -c error src.out   (re-elaboration from source)
exit=0
0
$ lake env lean ax.lean     (#print axioms of the three targets)
'RBM.Gauss.Sizes.stSEforLn_part3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stSEforLn_part4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stSEforLn_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|implemented_by|extern" SEforLn2.lean; echo exit=$?
exit=1
```
Registry pre-check: a scratch copy of `RBM3D.lean` with `import RBM3D.Induction.SEforLn2` inserted
after the last `import` (what the hub does at merge), compiled with `lake env lean`:
```
$ diff RBM3D.lean root.lean
183a184
> import RBM3D.Induction.SEforLn2
$ lake env lean root.lean 2>&1 | head -3; echo exit=$?
axiom audit: 4368 theorems, 1512 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit=0
$ lake build RBM3D 2>&1 | grep -A1 "axiom audit"     (branch as committed, no root import)
error: RBM3D.lean:186:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Gauss.Sizes.STSEforLn]
```
The second output is expected: `STSEforLn` leaves the owed list and is proved only once the hub adds the root
import at merge (DECISIONS §20). With the import the full registry check passes.

## 5. Compiled nonempty instances (same file, §11, all compile in §4)
| endpoint | instance | data / discharged hypotheses | kept hypotheses |
|---|---|---|---|
| `stSEforLn_part3` | `k = 2` (empty `n'` sum) and `k = 4` (`n' = 3`, `STn12 3 = (1,3)` by `decide`) | `d = 3`, merged `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `Cd=4`, `𝔠d=1/120` (`𝔠d·Cd = 1/30` by `norm_num`), `sz0_con (1/120)` for `STConStInd` | `hG : STGdecayW sz0 (STflowE z0) sInst tInst 4` (owed Step 2 pin; allowed) |
| `stSEforLn_part4` | `(k,q) = (2,1)` and `(4,2)` | same data; no stochastic hypothesis | none |
| `stSEforLn_holds` | `example : STSEforLn 3 := stSEforLn_holds 3`; `inst_SEforLn (stSEforLn_holds 3) 4 _` (merged `Step34Pins.lean:988`) | as above | those of the merged `InstIngConcl` |
Nonemptiness: `example (n) : Nonempty (TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 _) × (Fin 2 → Zd 3 _))`
compiles (window point `0 ∈ [0, 1/16]`). Window not collapsed (`s < t`), `L ≥ 4`, no `False` premise, no huge witness.

## 6. Paper deltas
* Statement differences of the targets from the paper are those of the merged pin (`max` → sum over `O(1)`
  terms; `(ℰ⊗ℰ)^M` summed over the `k` cut edges): already `D54` (T2041g) in `docs/paper-deltas.md:355`.
* Proposed by the prover: `T2139a` (weak form of `(con_st_ind)` at the running time `u ∈ [s,t]`; a private
  pointwise copy of `stSumTwoLoop`), `T2139b` (the `W^{-D}` absorption uses `Sizes.Bandwidth`, not `(eq:WO)` as the
  ticket text says). Both are proof-route notes; no target statement differs from the pin. Coverage complete.

## 7. Observations (no effect on the verdict)
* O1. The prove report's registry pre-check uses `import RBM3D` + `import RBM3D.Induction.SEforLn2`; in a fresh
  worktree `RBM3D.olean` cannot be built from the branch alone (§4 second block), so that command needs an olean built
  with the root import. The prover's full build with a temporary root import, and this audit's root copy, both pass.
* O2. `main` moved to `c8e4f17` after the branch base `7f82dd6` (T2138, T2140); `merge-tree` is clean, and the new
  public names are absent from `main`. The hub's full build at merge is the check against the moved `main`.

## Verdicts
* `stSEforLn_part3`: **PASS**.
* `stSEforLn_part4`: **PASS**.
* `stSEforLn_holds`: **PASS** (the pin `STSEforLn d` for every `d`; registry line removed correctly).

Ticket T2139: **PASS**. No dispatcher sign-off needed.
