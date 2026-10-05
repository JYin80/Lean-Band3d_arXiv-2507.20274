Auditor model: claude-opus-5-5

# T2171 audit (round 1) — S5-06 `Path/LemDecCalEdif`

Audit time (`date -u`): Mon Oct  5 04:58:41 UTC 2026. Branch `t/T2171` = `a86773c` (merge-base `cc96b69`, main `f8ad4b4`).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2171-audit1` (detached at `a86773c`). Scripts in `scratchpad/T2171/` (`adiff.py`, `acons.py`, `ax.lean`).

## 1. Diff scope and build

```
$ git diff --name-status main...t/T2171
A	RBM3D/Path/LemDecCalEdif.lean
$ lake build RBM3D.Path.LemDecCalEdif   (audit worktree)
✔ [3817/3817] Built RBM3D.Path.LemDecCalEdif (15s)
Build completed successfully (3817 jobs).
exit=0
$ grep -E "^(warning|error).*LemDecCalEdif" build.out | wc -l
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Path/LemDecCalEdif.lean | wc -l
0
```
Only the sole writable file is touched; `RBM3D/Test/Axioms.lean` unchanged (none expected by the ticket). No frozen signature touched (new file only).

## 2. Axioms

```
$ lake env lean ax.lean   # import RBM3D.Path.LemDecCalEdif; #print axioms ...
'RBM.Path.E2HypDif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.lossE2dif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_dif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_STeeM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_cut_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_cut_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_hyp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_inst_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalEdif_inst_b' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Public declarations of the file (grep of non-`private` `theorem|def`): exactly the nine above; every unpinned public name carries the prefix `LemDecCalEdif_`.

## 3. Target 1 — pinned vocabulary (script diff against `docs/tickets/checks/T2171-check.lean` §2)

```
$ python3 adiff.py
E2HypDif identical (whitespace-normalised): True
LemDecCalE_dif body == difShape body [loss d -> lossE2dif d]: True
occurrences of bare "loss " in shape body: 1
def lossE2dif (d L W : ℕ) (Λ K₀ : ℝ) : ℝ := lossE2 d L W Λ K₀ * ((729 : ℝ) ^ d * (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (6 * d))) ^ (2 * d))
$ python3 acons.py   # consumer, Step5Pins.lean:178-186 (third conjunct of STLemDecCalEConcl)
consumer RHS (u:=q.1.1.1, a:=q.1.1.2.2, Jst n u D:=J) == LemDecCalE_dif RHS after loss: True
pin range clause: True | file range clause: True
```
`lossE2dif` has the pinned shape, `κ_dif d = 729^d` (closed form, numerals and a power of `d`); polylog in `N` times the `e^{O((log W)^{3/4})}` already in `lossE2`. `E2HypDif` is a `def` (conjunction), `E2Hyp` is a merged `def` (`Path/LemDecCalE.lean:69`), no structure field. `LemDecCalE_dif` is a `Prop` stated only (proved by S5-07), as the ticket requires; it is not an endpoint theorem.
Verdict target 1: **PASS**.

## 4. Targets 2–5 — statements against the ticket's mathematics

Statements read from the file (`:1155`, `:688`, `:873`, `:1354`):
- **Target 2 `LemDecCalEdif_STeeM_le`** (no hypothesis; all `σ : Fin 2 → Bool`, all `a a'`):
  `‖STeeM sz n E u M σ a a'‖ ≤ W^d * Σ_b Σ_b' ‖SB b b'‖ * (‖STLM … ![σ0,σ1,σ0,!σ0,!σ1,!σ0] ![a0,a1,b',a'1,a'0,b]‖ + ‖STLM … ![σ1,σ0,σ1,!σ1,!σ0,!σ1] ![a1,a0,b',a'0,a'1,b]‖)`.
  Matches the ticket's `𝓛⁶_{σ₀σ₁}(a₀,a₁,b',a'₁,a'₀,b) + 𝓛⁶_{σ₁σ₀}(a₁,a₀,b',a'₀,a'₁,b)` with `W^d` and `|SB|`. **PASS**.
- **Target 3 `LemDecCalEdif_cut_near`** (`h : E2HypDif sz n E u D Λ K₀ J M`, all `σ₀ σ₁`, all six labels):
  `‖𝓛⁶_{σ₀σ₁}(A₁,A₂,B',A₂',A₁',B)‖ ≤ Λ (W^d(1−u))⁻¹^5 · 1(|A₁−B|_∞ ≤ 4 (log P)²) + 32·3^{d+1} Λ⁶ J P⁻¹`, `P = L^d W^{6d}`.
  Matches the ticket (`ℓ** = 4(log P)²`, `c_near(d) = 32·3^{d+1}`, RBM2D `32·200`). **PASS**.
- **Target 4 `LemDecCalEdif_cut_far`** (`h : E2HypDif …`, `|A₁−A₁'| ≤ ℓ*`, `|A₂−A₂'| ≤ ℓ*`, `|B−B'| ≤ 1`, `4ℓ* < |A₁−A₂|`; all `σ₀ σ₁`):
  RHS `(2·9^d ΛJ)² S³ T(|A₁−A₂|)² · Λ ((W^d(1−u))⁻¹)^{3/2} · Σ_{X∈(A₁,A₁',A₂,A₂')} 1(|X−B| ≤ ℓ*+1) + (2·9^d ΛJ)³ S³ T(|A₁−A₂|) T(|A₁−B|) T(|B−A₂|)`,
  `S = e²·e^{2(log W)^{3/4}}`, `T = tailTD d W u D`, `ℓ* = (log W)^{3/2}` (rpow). Matches the ticket with `c_e = 2·9^d`; the four-loop factor is written as `(M_u⁻¹)^{3/2}` (same value; candidate T2171e). Hypotheses are exactly the ticket's four. **PASS**.
- **Target 5 `LemDecCalEdif_hyp_zero`**: concludes `E2HypDif sz n E 0 D Λ K₀ J 0`. Premise script diff against `LemDecCalE_e2Hyp_zero` (`Path/LemDecCalE.lean:1321`):
```
premise names upstream: ['hd', 'hE', 'hlam', 'hlam1', 'hlamW', 'hΛ', 'hK', 'hlog', 'hJ', 'hJW']
premise names T2171 : ['hd', 'hE', 'hlam', 'hlam1', 'hlamW', 'hΛ', 'hK', 'hlog', 'hJ', 'hJW']
```
  (no textual difference among these); `hfloor` (outside the regex, read from the source) is `(L^d W^{6d})^2 ≤ W^D` here vs `L^d W^{2d} ≤ W^D` upstream, the latter derived in the proof (`:1366-1381`), exactly the ticket's replacement. Loop clauses via the exact route (`1 ≤ Λ`). **PASS**.

General `σ`: targets 2–4 quantify over all `σ` / `σ₀ σ₁ : Bool` (not RBM2D's `(+,−)` only); instance (d) is a same-sign loop.

## 5. Vacuity, hidden hypotheses, cycles

- The only hypotheses of targets 3–4 are `E2HypDif` (a `def`, shown inhabited by `LemDecCalEdif_inst_a`/`_inst_b`, which are proved, not assumed) and the explicit distance premises. No `structure`/`class` in the file.
- Imports: `Path/LemDecCalE`, `Induction/Step2Iterate`, `Induction/Split` — all merged on `main`; nothing from `RBM3D` root; `LemDecCalE_dif` (S5-07 pin) is used by no theorem here (no cycle).
- `J ≤ W` (T2164 M3) is not destructured by any proof here:
```
$ grep -nE "hJW|J ≤ \(\(sz" RBM3D/Path/LemDecCalEdif.lean
1360:    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
1383:  refine ⟨LemDecCalE_e2Hyp_zero sz n hd hE hlam hlam1 hlamW hΛ hK hlog hfloor2 hJ hJW, hfloor,
```
  (only as the inherited premise of `hyp_zero`, forwarded to `LemDecCalE_e2Hyp_zero`).
- External-type premises (floor, loop clauses): the prove report has a limit computation along `sz0` and `szCL` (`limit.py`: the floor holds for `1 ≤ n ≤ 3000` resp. `0 ≤ n ≤ 3000`, closed-form ratios) and the `STLmaxU` → loop-clause chain with `Bctl ≤ 2 M_u⁻¹`; the floor's S5-09 source is reported **missing** (flag for the dispatcher, not a defect of this ticket: the ticket itself records it as missing).

## 6. Compiled nonempty instances (all in the file, compiled by the build in §1)

| target | instance | data | hypotheses discharged |
|---|---|---|---|
| 1/5 | `LemDecCalEdif_inst_a` (theorem) | `sz0`, `n=1`: `d=3, L=8, W=1024, lam=1/4096`, `E=1/2, u=0, D=38, Λ=K₀=J=1, M=0` | all premises of `hyp_zero` by `norm_num` (incl. floor `(8^3·1024^18)^2 ≤ 1024^38`, `4 ≤ log 1024`) |
| 1/5 | `LemDecCalEdif_inst_b` (theorem) | `szCL`, `n=0`: `L=2·24^5, W=2^24, lam=1`, `D=42` | same, floor at `2^{1007.55} ≤ 2^{1008}` |
| 2 | example (c) `:1470` | (a), `σ=(+,+)`, `a=a'=(0,e₁)` | none needed |
| 2 | example (c′) `:1490` | (a), `σ=(+,+)`, `a=a'=(0,0)` | none; also proves RHS `> 0` |
| 3 | example (d) `:1546` | (a), `σ₀=σ₁=+`, `A₁=A₁'=B=B'=0`, `A₂=A₂'=e₁` | `E2HypDif` by `LemDecCalEdif_inst_a` |
| 4 | example (e) `:1598` | (b), `σ₀=+, σ₁=−`, `A₁=A₁'=B=B'=0`, `A₂=A₂'=300e₁` | `E2HypDif` by `_inst_b`; `h1,h2` (dist 0), `hB` (dist 0), `hd`: `4(24 log 2)^{3/2} < 300` (`lemDecCalEdif_inst_ell`), `|0−300e₁|_∞ = 300` by `decide`; RHS `> 0` proved |

Data are the ticket's (no `N=0`, nonempty torus, `L/2 > 300` at (b)); `M = 0`, `u = 0` are prescribed by the ticket. No deterministic hypothesis is left open. **PASS** for all endpoints.

## 7. Paper-delta coverage

Prove report (d) proposes T2171a (loop premises in `E2HypDif`), T2171b (floor `(L^dW^{6d})² ≤ W^D`, stronger than D374 and the paper's `W^D ≥ N`), T2171c (every `σ ∈ {±}²`), T2171d (`lossE2dif` explicit with `729^d(1+log P)^{2d}`), T2171e (rpow form of the four-loop factor). These cover every statement difference listed by the ticket's acceptance criteria. Inherited `E2Hyp` differences (`J ≤ W`, `L^dW^{2d}` floor, `M_u`, `tailTD`) are D374–D377 / T2164 open items. Covered.

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. Example (c) at the ticket's data `a = a' = (0, e₁)` does not prove its RHS positive; (c′) at `a = a' = (0,0)` does. Both compile; the endpoint has a nondegenerate instance.
- O2. Branch base `cc96b69` is behind `main` (`f8ad4b4`); the diff adds one new file only. The registry pre-check / `#assert_rbm_axioms` with the root import is left to the hub's full build at merge (the prover reports exit 0 for `precheck.lean` and the whole-library build in its worktree).
- O3. The part-2 constant chain (`κ_dif = 729^d` sufficiency, no `J ≤ W`) is preflight script evidence only (row 6); it is first proved in S5-07. Spot-check of row 6 by hand: `F2 = 16·729^d(2S_d+1)Λ³e⁶e^{6Y} ≤ lossE2dif` via `2S_d+1 ≤ 3(1600d⁴)^d`, `48e⁶ ≤ 10¹²`; near long-edge `2c_near Λ⁶ J W^{-5d} ≤ (1−u)⁻¹M_u^{-1/2}J³·M_u^{-4}e^{-4Y}·(…)` since `M_u ≤ W^d`; consistent.
- O4. For S5-09 (dispatcher): the floor and `E2Hyp`'s `GijGEX` / `J ≤ W` conjuncts have no `STIngR5` source yet (reported in the prove report's Consumer table).

## Verdict

| target | verdict |
|---|---|
| 1 `E2HypDif`, `lossE2dif`, `LemDecCalE_dif` | PASS |
| 2 `LemDecCalEdif_STeeM_le` | PASS |
| 3 `LemDecCalEdif_cut_near` | PASS |
| 4 `LemDecCalEdif_cut_far` | PASS |
| 5 `LemDecCalEdif_hyp_zero` | PASS |

**T2171: PASS.** No dispatcher sign-off needed for merge (O4 is a downstream flag for S5-09).
