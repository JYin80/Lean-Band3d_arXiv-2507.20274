Auditor model: claude-opus-5-5

# T2160 audit (round 1) — ST2-35 `Induction/AzumaProxyN2` — Sun Oct  4 21:41:18 UTC 2026

Audited commit `aafa0ab` (branch `t/T2160`), detached worktree `RBM3D-wt/T2160-audit1`.
Ticket pins no statement text; targets are ports of RBM2D `Induction/AzumaProxyN.lean` at `c9a24cf`
with the merged pins `YMomentsN`, `YMomentBoundsN` (`GridAssemblyN.lean:141,173`) as the acceptance shape.

## 1. Statements (script diff against the RBM2D source after the ticket's dictionary)

`sdiff.py` extracts each declaration header from `git show c9a24cf:RBM2D/Induction/AzumaProxyN.lean`,
applies only the dictionary (`Sizes.size d n→sz.size n`, `Z2 (d.L n)→Zd d (sz.L n)`,
`Idx (d.L n) (d.W n)→Idx d (sz.L n) (sz.W n)`, `SizeTendsto d→sz.SizeTendsto`, `RangeCond d τ' t→sz.RangeCond τ' t`,
`PathΩ/filt/pathP/YvecN/… d→… sz`, ` [NeZero k]→''`) and diffs against the 3D file:
```
$ python3 sdiff.py
== YMomentsUnifN: 9 vs 9 lines, diff lines: 0
== yMomentsN_of_unif: 2 vs 2 lines, diff lines: 0
== AzumaProxyN_stopW: 3 vs 3 lines, diff lines: 0
== AzumaProxyN_YfieldsW: 21 vs 21 lines, diff lines: 0
== integrable_normPow8: 2 vs 2 lines, diff lines: 0
== integral_normPow8: 3 vs 3 lines, diff lines: 0
```
The only non-dictionary change is dropping `[NeZero k]` (a hypothesis removed: the 3D statements are
at least as strong; matches the merged `YMomentsN`, which has `∀ (k : ℕ) (σ : Fin k → Bool)`).

`yMomentsN` and `yMomentsUnifN` against the pins (elaborated types, audit worktree):
```
$ lake env lean aud.lean   # import RBM3D, RBM3D.Induction.AzumaProxyN2; #check; #assert_rbm_axioms
@yMomentsN : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) (K : ℕ → ℕ), YMomentsN sz κ τ' E s t K
@yMomentsUnifN : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ), YMomentsUnifN sz κ τ' E s t
```
`yMomentsN` has exactly the merged pin type `YMomentsN` (no added hypothesis). `YMomentsUnifN`
(`AzumaProxyN2.lean:894`): hypotheses `0<κ`, `|E n|≤2−κ`, `0≤s≤t<1`, `SizeTendsto`, `RangeCond τ' t`;
quantifier order `∀ k σ, ∃ C_P ≥ 0, ∀ K, (∀ n, K n ≠ 0) → ∀ᶠ n, ∃ P, 0≤P≤N^{C_P} ∧ ∀ τ …`, i.e.
`C_P` before `K` as the ticket and DECISIONS §45 require; the conclusion is the merged `YMomentBoundsN`
with `v_j = Δ²P`, `w_j = Δ⁴P²`, which is what `AssembledN` (`GridAssemblyN.lean:227`) consumes
(`P ≤ N^{C_P}`, `v j ≤ Δ²P`, `w j ≤ Δ⁴P²`, `hY : YMomentBoundsN …`). `yMomentsN_of_unif : YMomentsUnifN →
YMomentsN` matches its 2D source exactly. The eighth-moment bound keeps `6881280·N^16` with `N = (WL)^d`;
`C_P = 11 + (4k+4)·max 0 (1−τ')` is the explicit witness in the compiled proof (`AzumaProxyN2.lean:921`),
unchanged from RBM2D as the ticket asked to check (report (a) row 10).
Public helpers `AzumaProxyN_{c0_pos,inv_one_sub_le,etaT_inv_le,P_le}_pub`: text-identical to RBM2D
`:2426-2447`. `AzumaProxyN_rowsum_Ugen_pub`: 2D kernel `ukerMat L (mSig·mSig)` on `Z2 L` replaced by the
merged `uKer d L g (cycProd …)` on `Zd d L` (general `d`, `g`), same bound `(1+(1−w)⁻¹)^k`.

## 2. Vacuity, hidden hypotheses, cycles

- No new structure: the only structure in the signatures is the merged `Sizes d` (fields `L, W, lam,
  three_le_L, W_pos`; `three_le_L` is what `gvarF ≤ 1` uses). No hypothesis hidden in a field.
- `yMomentsUnifN`, `yMomentsN`, `AzumaProxyN_YfieldsW` are unconditional theorems (no pin of another gate
  as hypothesis). `yMomentsN := yMomentsN_of_unif sz (yMomentsUnifN …) K`; `yMomentsUnifN` is proved
  directly (`:915-977`). Imports: merged `RBM3D.Induction.AzumaProxyN` and Mathlib only. No cycle.
- External hypotheses: none (`SizeTendsto`, `RangeCond` are deterministic and discharged at `sz0`).
- Registry: `grep -c YMoments RBM3D/Test/Axioms.lean` = 0 on `main` and on the branch; the scanner lists no
  `YMoments*` premise (`grep -n YMoments aud.out` hits only the two `#check` lines above):
```
premises found by scanning: 83 (borrowed 0, owed 64, structural 19).
```

## 3. Compiled nonempty instances (namespace `AzumaProxyN2Inst`, `d = 3`, merged `sz0`)

Data: `κ=1`, `E≡1/2`, `τ'=1/2`, `s≡0`, `t≡1/32`, `K≡4` (`Δ=1/128>0`), `k=3`, every `σ`; `τ ≡ K n` (no
stopping); `RangeCond (1/2) vg` proved in-file (`azumaProxy2_rangeCond_vg`), `SizeTendsto` = merged
`sz0_tendsto`. No hypothesis left open.

| endpoint | instance (line) | data / nondegeneracy |
|---|---|---|
| `AzumaProxyN_integrable_normPow8_incr`, `…_integral_normPow8_incr_le` | `normPow8_instance` (1306) | `n=0`, `j=0`, `N=2097152` |
| `yMomentsUnifN` | `yMomentsUnifN_instance` (1315), `yMomentsUnifN_instance_nonzero` (1860) | all 7 hyps discharged; `n` from `.exists` of the filter (threshold fails at `n=0`, report (a) PART C); `0<Δ`; `YvecN` not a.e. zero at that `n` |
| `yMomentsN_of_unif` | `yMomentsN_of_unif_instance` (1329) | grid `Kg`, `hK` = `azumaProxy2_Kg_ne_zero` |
| `yMomentsN` | `yMomentsN_instance` (1345) | all 8 hyps discharged; extracts the 4th-moment fields at `j=0`, `m=1` |
| `AzumaProxyN_YfieldsW` (+ `stopW`) | `yfieldsW_instance` (1375) | `n=0`, `j=0≤…`, `j+1≤Kg 0=4`, every weight `κ`, `C₂` from `hermTestFunLoopN`, `P = 2000(SC₂)²N⁸` |
| five `_pub` helpers | `example`s (1412-1443) | concrete reals, `rowsum` at `d=3`, `L=4` |
| §8b | `yvecN_not_ae_zero` (1800) | every `n`, `j=0`, `σ=(+,−,+)`, `b=0` |

Instance construction (verbatim, `:1320-1323`):
```lean
  obtain ⟨C_P, hC, hev⟩ := yMomentsUnifN sz0 1 (1 / 2) Einst sInst vg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto azumaProxy2_rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg azumaProxy2_Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, azumaProxy2_gridStep_pos n, hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩
```
No `N = 0`, empty index, collapsed window or `False` premise; the witness `n` is not chosen large by hand
(the filter gives existence; report (a) shows `n = 1` already satisfies the threshold).

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Induction.AzumaProxyN2      # Sun Oct  4 21:39:22 → 21:39:40 UTC 2026
ℹ [3791/3791] Built RBM3D.Induction.AzumaProxyN2 (14s)
Build completed successfully (3791 jobs).
EXIT 0
$ grep -E "^(error|warning).*AzumaProxyN2" build.out | wc -l
0
$ grep "AzumaProxyN2.lean.*depends on axioms" build.out | sed 's/.*axioms: //' | sort | uniq -c
  19 [propext, Classical.choice, Quot.sound]
```
(the 19 = 12 public targets/helpers + 7 instances, list as in prove report (b); none "does not depend").
```
$ lake env lean aud.lean   (tail)
axiom audit: 4823 theorems, 1711 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
EXIT 0
$ git show t/T2160:RBM3D/Induction/AzumaProxyN2.lean | grep -nE "\bsorry\b|\badmit\b|native_decide|^ *axiom " | wc -l
       0
$ git diff --name-only main...t/T2160
RBM3D/Induction/AzumaProxyN2.lean
```
Only the sole writable new file is touched; `RBM3D.lean`, merged pins (`GridAssemblyN.lean`) and
`Test/Axioms.lean` are unchanged, so no frozen signature is altered. The file imports
`RBM3D.Induction.AzumaProxyN` and Mathlib, not `RBM3D`.

## 5. Paper deltas

`grep -n T2160 docs/paper-deltas.md` → no entry yet; the report (d) proposes:
- `T2160a`: Lean-only `Y`-remainder moment pins (`v=Δ²P`, `w=Δ⁴P²`, `P≤N^{C_P}`, explicit `C_P`) in
  place of the paper's BDG step (`3_5:166`, `3_5:216`) — covers `YMomentsUnifN`/`yMomentsN`/`YfieldsW`.
- `T2160b`: `gvarF ≤ 1` needs `3 ≤ L` (`sz.three_le_L`).
- `T2160c`: the uniform order `C_P → C_K → K` (`YMomentsUnifN`) vs the merged `YMomentsN`.
Every Lean/paper statement difference found above is covered by these candidates.

## 6. Observations (no statement, instance, build, axiom or delta effect)

- O1. The ticket asks to delete the `YMomentsN` registry line; no such line exists on `main` (grep = 0),
  so nothing was deleted; the report states this.
- O2. `AzumaProxyN_rowsum_Ugen_pub` takes `L` implicitly (RBM2D: explicit) and adds `d`, `g`; no 3D
  consumer yet, so a future port of `AltProxyQ` must adapt its call sites.
- O3. The prove report's axiom-audit line reads 4818 theorems; this audit's run reads 4823 (cause not
  investigated); both report 0 axioms in `RBM`, so acceptance is unaffected.

## Verdict

| target | verdict |
|---|---|
| 1. §3-§7 port, `AzumaProxyN_integrable_normPow8_incr`, `…_integral_normPow8_incr_le`, `yMomentsN` | PASS |
| 2. `YMomentsUnifN`, `yMomentsN_of_unif`, `yMomentsUnifN` (`C_P` before `K`, unchanged witness) | PASS |
| 3. `AzumaProxyN_stopW`, `AzumaProxyN_YfieldsW`, `AzumaProxyN_*_pub` | PASS |
| 4. instances §8 and §8b (`yvecN_not_ae_zero`) at `d = 3`, `sz0` | PASS |

**T2160: PASS.** No dispatcher sign-off needed.
