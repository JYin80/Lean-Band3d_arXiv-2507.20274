Auditor model: claude-opus-5-5
# T2039 audit, round 2 (after repair `0362cbc`); written Sat Oct  3 14:15 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2039-audit2`, detached at `0362cbc` (`t/T2039`). Report-only design ticket; the probe stays on the branch.
Scope: the round-1 RETURN (`STScaleExists` false, so the skeleton `ST_step2_of_pins*` / `inst_skeleton*` had a false premise) and its four repair items; a re-run of build, hygiene, axioms and diff scope; and a check that no other statement changed.
**Verdict: PASS.**

## 1. Build, hygiene, diff scope, axioms
```
$ lake build RBM3D.Probe.T2039Pins            # 14:11:27 -> 14:12:34 UTC
Build completed successfully (3739 jobs).      exit 0   (86 warning lines: linter only; no error lines)
$ lake env lean RBM3D/Probe/T2039Pins.lean > env.log; echo exit $?; grep -c error env.log
exit 0
0
$ grep 'depends on axioms' env.log | sed 's/.*: //' | sort | uniq -c
     33 [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/Probe/T2039Pins.lean | wc -l
       0
$ git diff --stat main...HEAD
 RBM3D/Probe/T2039Pins.lean | 6041 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 6041 insertions(+)
```
Only the sole writable probe file is touched (the reports are in the main worktree). No frozen signature is touched; the probe is never imported. There are 33 axiom prints, against 31 in round 1: the two new ones are `ST_scaleAdm_congr` and `inst_scaleAdm_szX`.

## 2. What the repair changed (by script)
```
$ git diff --stat 509cf7d 0362cbc ; git diff 509cf7d 0362cbc | grep '^@@'
 RBM3D/Probe/T2039Pins.lean | 171 ++++++++++++++++++++++++++++++++++++++++-----
@@ -2273,22 +2273,22 @@ def STSelfImp ...            (STScaleOk, STScaleAdm)
@@ -2345,8 +2345,8 @@ theorem ST_next ...           (hrange/hstep now ∀ᶠ n)
@@ -2401,13 +2401,13 @@ theorem ST_next ...         (proof)
@@ -3803,8 +3803,8 @@ theorem ST_selfImprove_section (proof)
@@ -3875,7 +3875,7 @@ theorem ST_selfImprove_section (proof)
@@ -4046,7 +4046,7 @@ theorem ST_iterate ...        (proof)
@@ -4071,8 +4071,8 @@ theorem ST_decay_pt ...       (proof)
@@ -5900,3 +5900,142 @@ end RBM.Probe.T2039.Inst  (new §15)
```
No other pin statement changed. `STStep2` and the ingredient pins `STNewKLK`, `STContractPt`, `STLWB`, `STLWT`, `STEMn2Poly`, `STEMn2Exp`, `STGridMart`, `STGridRepN`, `STstopIdx`, `STK2decay`, `STNetLift2`, `STOptL2` and `STLocalAvgOfL2` are byte-identical to round 1. Their statement checks in round 1 (§3–§4 there: quantifier order `∀ κ ε 𝔡, ∃ C_d, ∃ 𝔠_d ≤ 1/100, ∀ 𝔠 sz z`, ranges `0 ≤ s < t ≤ lemT z`, the three conclusions per `u ∈ [s,t]`, the factor `((1−s)/(1−u))^{C_d}(W^{-d}B_{u,0})^{1/5}`, `∀ D > 0`, `σ ∈ {±}²`) therefore stand. The signatures of `ST_step2_of_pins` (:4639) and `ST_step2_of_pinsN` (:5341) are outside every hunk, so they are unchanged.

New statements (probe :2277–2296):
```
def STScaleOk (s t) (Kf) : Prop :=
  (∀ᶠ n, ∀ u ∈ [s n, t n], 0 ≤ Kf n u ∧ Kf n u ≤ L_n ∧ Kf n u ≤ (log W_n)^10 * ellT L_n λ_n u) ∧
  (∀ᶠ n, ∀ u v, s n ≤ u → u ≤ v → v ≤ t n → tailT u (Kf n u) ≤ tailT v (Kf n v))
def STScaleAdm (s t) (Kseq) : Prop :=
  (∀ n u, Kseq 0 n u = 0) ∧ (∀ m, STScaleOk s t (Kseq m)) ∧
  (∀ m, ∀ᶠ n, ∀ u ∈ [s n,t n], 0 ≤ Kseq m n u ∧ Kseq m n u ≤ Kseq (m+1) n u) ∧
  (∀ m, ∀ᶠ n, ∀ u ∈ [s n,t n], Bctl n u ^ (1/6) * tailT u (Kseq m n u) ≤ tailT u (Kseq (m+1) n u)) ∧
  (∀ D > 0, ∃ M, ∀ᶠ n, ∀ u ∈ [s n,t n], tailT u (Kseq M n u) ≤ W_n^(-D) ∨ L_n ≤ Kseq M n u)
```
(This is a paraphrase of the file text with the `sz.` prefixes and casts dropped. The quantifier structure is exactly that of :2279–2296.)

## 3. Repair items of round 1
| item | requirement | evidence | result |
|---|---|---|---|
| 1 | clauses not forcing `Bctl ≤ 1` at small `n` | clauses 3, 4 and the u-monotonicity are now `∀ m, ∀ᶠ n`. Only `K_0 = 0` is required at every `n`, and it constrains nothing (`Bctl` does not appear in it) | done |
| 2 | recompile skeleton and instances | §1: build exit 0; `inst_skeleton`, `inst_skeleton_concl`, `inst_skeletonN` have the three standard axioms | done |
| 3 | compiled check that eventual-only sequences do not refute | `ST_scaleAdm_congr` (:5917) proves that changing `sz.L/W/lam`, `s`, `t` and `K_{m≥1}` at finitely many `n` preserves `STScaleAdm`. `inst_scaleAdm_szX` applies it at the round-1 data (`szX`, `zX`, `s ≡ 0`, `t = lemT ∘ zX`, `Bctl 0 0 = 65/64 > 1`), including the family with `K_m(0,·) = 0` that was refuted before | done |
| 4 | record fix and new statement by script in the prove report | prove report :260–299 (`sed -n '2277,2281p;2288,2296p'` paste) and candidate T2039j | done |

## 4. No vacuity: `STScaleExists` is now satisfiable (auditor construction)
The repair item 3 check only shows that the round-1 refutation no longer applies. To confirm that the owed pin `STScaleExists` (:4106) is not false for some other reason, the auditor built a witness, checked it on paper, and checked it numerically.

Construction. Let `b_u = Bctl n u` and `f_u(r) = tailT u r = B_{u,r}·exp(−√(r/ℓ_u))`; `f_u` is continuous and strictly decreasing on `[0,∞)`. Set `K_0 = 0` and, for `m ≥ 1`, `K_m(u) = min(sol_m(u), L)`, where `f_u(sol_m(u)) = b_u^{m/6}B_{u,0}` (by the IVT; take any value at the finitely many `n` where `b > 1`). Then:
- (3) and (4): equality holds when the cap is inactive. When the cap is active, `f(L) ≥ b^{1/6}f(L)`, because `b ≤ 1` eventually by the merged-in-probe `ST_Bdata_holds`: `Bctl ≤ N^{-c}`.
- u-monotonicity: `f_u(K_m(u)) = max(b_u^{m/6}B_{u,0}, f_u(L))`. Both terms are non-decreasing in `u < 1`, because `B_{u,r}` grows as `1−u` shrinks and `ℓ_u` is non-decreasing.
- `K ≤ (log W)^{10}ℓ_u` for each fixed `m`, eventually: `√(K/ℓ_u) ≤ (m/6)·log(1/b_u) ≤ (m/6)(d log W + log(1/c_B))`, by the lower bound of `STBdata`.
- Floor: `b^{M/6}B_{u,0} ≤ N^{-cM/6}W^d ≤ W^{-D}` once `M ≥ 6(1 + D/d)/c`.
```
$ python3 scratchpad/T2039/scale_exists.py   # d=3, sz0 (= szX for n ≥ 1), z_n = 1/2 + i N^{-4/5}, s=0, t_n=lemT z_n, u-grid incl. u→t_n
n=  1 L=8 W=1.024e+03 N=5.498e+11 1-t=4.187e-10 grid=39 max_u Bctl=1.986e-02 | m<=60: K_m<=K_m+1 True, step True, u-monotone True, K<=(logW)^10*ell True, floor(D=1) M=7
n=  9 L=40 W=3.200e+06 N=2.097e+24 1-t=3.603e-20 grid=79 max_u Bctl=1.382e-04 | m<=60: K_m<=K_m+1 True, step True, u-monotone True, K<=(logW)^10*ell True, floor(D=1) M=7
n= 99 L=400 W=3.200e+11 N=2.097e+42 1-t=1.435e-34 grid=137 max_u Bctl=1.283e-07 | m<=60: K_m<=K_m+1 True, step True, u-monotone True, K<=(logW)^10*ell True, floor(D=1) M=10
```
At `n = 99` we have `1−t = 1.4e-34`, which is below `g²/L² = 1.5e-33` and above `g²/L^d = 3.8e-36`. So the window reaches the third regime of the ticket, and the extreme input `u → t`, `L` large holds.
**Conclusion: `STScaleExists 3` is consistent and, by the argument above, true.** The skeleton premises are no longer known to be false. `STScaleExists` remains owed (ST2-05), and the construction above is a route for that ticket.

## 5. Compiled nonempty instances (endpoints)
| endpoint | instance | status |
|---|---|---|
| `ST_step2_of_pins`, `ST_step2_of_pinsN` | `inst_skeleton`, `inst_skeleton_concl`, `inst_skeletonN` at `(sz0, z0, s ≡ 0, t ≡ 1/16)`; the remaining hypotheses are the owed pins of item 5 (taken as hypotheses by design) | ok |
| `ST_scaleAdm_congr` (new) | `inst_scaleAdm_szX` at `szX`, `zX` with `STFlow` and `Bctl 0 0 = 65/64` discharged; `hK` is an owed-pin output for `sz0` | ok |
| `STStep2` and the other pins, `ST_Bdata_holds`, `STstopIdx_isStoppingTime`, `ST_gridMart_of_repN` | unchanged instances from round 1 (`inst_step2`, `inst_step2_lowg`, `inst_Bdata`, `inst_stop`, `inst_gridRepN`, …), recompiled in §1 | ok |

## 6. Cycles, hidden hypotheses
No new structure fields. `ST_scaleAdm_congr` depends only on `STScaleAdm`, `STScaleOk` and `Sizes.Bctl`. Since round 1 the set of skeleton premises has not changed, and it is acyclic.

## 7. Paper deltas
T2039a–i (round 1) and T2039j (new: the clauses of `(eq:def_ell1)` and `(eq:monotone_Ku)` are required only eventually in `n`, per level `m`) cover the differences of the repaired pins.
Still uncovered (round-1 observation O2, kept as an observation): `STStep2` takes `STLK` and `STDecay` at `s` together with Step 1, not (c), (d) or the strong form of (b) of `lem:main_ind`. This is a stronger pin.
The dispatcher has precedents for the same kind of difference: `paper-deltas.md:281` (Step 1) and D56 (`paper-deltas.md:357`, Steps 3–4). Proposed candidate text for the dispatcher: "T2039k: `STStep2` is stated under (a) and (b) at `s` (`STLK`, `STDecay`) and Step 1's conclusions only; (c) and (d) of `lem:main_ind` are dropped (`3_5:454–609` uses only these)."

## 8. Verdict per target
- Pins `STStep2`, `STNewKLK`, `STContractPt`, `STLWB`, `STLWT`, `STEMn2Poly`, `STEMn2Exp`, `STGridMart`, `STGridRepN`, `STstopIdx`, `STK2decay`, `STNetLift2`, `STOptL2`, `STLocalAvgOfL2`: PASS (unchanged since round 1).
- `STScaleOk`, `STScaleAdm`, `STScaleExists`: PASS (restated; satisfiable, §4).
- Skeleton `ST_step2_of_pins`, `ST_step2_of_pinsN` and `inst_skeleton*` (items 5, 8): PASS.
- Build, hygiene, axioms, diff scope: PASS.

### Observations (no RETURN)
- O1 (from round 1): `STOptL2` is taken as a pin, so `STLWB` and `STEMn2Poly` are not consumed by a compiled theorem. ST2-14/15 should compile `STOptL2` from them.
- O2: candidate T2039k above.
- O3 (from round 1): `inst_newKLK` and `inst_contractPt` are at `H = 0`.
- O4 (from round 1): `STNewKLK` and `STK2decay` are uniform over all `sz` and `n` without `(eq:WO)`. Their proof tickets should check that the constants are free of `W`, `L` and `λ`.
- O5: `inst_scaleAdm_szX` is conditional on an `STScaleAdm` family for `sz0` (an owed-pin output). The unconditional content is `ST_scaleAdm_congr`, and §4 supplies satisfiability.

Needs dispatcher sign-off: no.
