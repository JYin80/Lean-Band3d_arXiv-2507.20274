Auditor model: claude-opus-5-5

# T2416 audit (round 1) — Sun Oct 11 10:06:34 UTC 2026

Branch `t/T2416` at `4c09836`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2416-audit1` (detached); main `88d1b63`.
Scratch: `<scratchpad>/T2416/` (`ax.lean`, `pin.lean`, `build.log`).

## 1. Diff scope, build, hygiene, axioms

```
$ git diff --stat main...HEAD
 RBM3D.lean           |    1 +
 RBM3D/BA/EMn2BA.lean | 1090 ++++++++++++++++++++++++++++++++++++++++++++++++++
$ git diff main...HEAD -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.BA.EMn2BA
$ wc -l RBM3D/BA/EMn2BA.lean           ->  1090   (stop line 1,800; one file <= 2,000)
$ lake build RBM3D.BA.EMn2BA  (grep error|Build completed|exit)
Build completed successfully (3825 jobs).
exit 0
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/BA/EMn2BA.lean | wc -l   ->  0
$ lake env lean docs/tickets/checks/T2416-check.lean   ->  check file exit 0; error lines: 0
$ ax.lean = import + `#print axioms RBM.BA.<n>` for every non-private theorem/def of the file (33)
$ lake env lean ax.lean; grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]"
exit 0
33
```
Only the two sole writable files are touched; no frozen signature edited (no existing file changed).

## 2. Statements against the pins (script)

`pin.lean` restates each target at exactly the ticket's BA reading (law `seqP (sz.withLam 0)`, `Flow = BAFlow`,
`mk = baFMz`, `T0 = BAflowT0`, `Hf = seqHflowBA (BAflowLam0 sz z)`, `ζf = ztOf (BAmF …) (BAflowEs …)`) with the
pinned definitions `emn2PolyFacts` (`EMn2Poly:835`), `emn2ExpFacts` (`EMn2Exp1:811`), `emn2ExpHK` (`EMn2Exp2:934`),
`STEMn2PolygL`, `STEMn2ExpgL` (`Chain/Step2Gen`), and the `J` form as the literal output type of
`stEMn2ExpJgL_of` (`EMn2Exp2:1226`) elaborated against `BAEMn2ExpJ d`:
```
$ lake env lean pin.lean   ->  pin.lean exit 0; errors 0
example (d) : emn2PolyFacts d BAFlow baFMz BAflowT0 (fun sz z n u ω => sz.seqHflowBA (BAflowLam0 sz z) n u ω)
    (fun sz z n u => ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u) := baEMn2PolyFacts d
example (d) : emn2ExpFacts d BAFlow baFMz BAflowT0 (…same Hf, ζf…) := baEMn2ExpFacts d
example (d) (hd : 3 ≤ d) : emn2ExpHK d BAFlow baFMz BAflowT0 := baEMn2ExpHK hd
example (d) : STEMn2PolygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) := baSTEMn2Poly d
example (d) (hd : 3 ≤ d) : STEMn2ExpgL d (…same…) := baSTEMn2Exp d hd
example (d) (hd : 3 ≤ d) : BAEMn2ExpJ d :=
  stEMn2ExpJgL_of (fun sz => Sizes.seqP (sz.withLam 0)) hd (baEMn2ExpFacts d) (baEMn2ExpHK hd)
```
T6-BA: `EMn2BA_contract_iff : STContractM d ↔ ∀ L W … H z, H.IsHermitian → 0 < z.im → BAContractAt d L W H z`
is proved by `Iff.rfl` (compiled), so `BAContractAt` is the body of `STContractM` (`Contract:1011`) verbatim.
```
@baSTContractM : ∀ {d} (sz : Sizes d) (lam0 : ℕ → ℝ) (n) (u) (ω) (m : ℂ) (E : ℝ),
  0 < m.im → u < 1 → BAContractAt d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω) (ztOf m E u)
```
BAT-C2 (`BACompBound`, `EMn2BA:457`, extracted in the prove report and re-read): `3 ≤ d → 0 < Λ → 0 < κ → ∃ C > 0, ∃ c > 0,
∀ L ≥ 3, ∀ g, 0 < g ≤ Λ, ∀ E m, BAReal d L g κ E m → ∀ t ∈ [0,1), ∀ σ₁ σ₂ : Bool,` row sums `≤ (1-t)⁻¹`, column sums
`≤ (1-t)⁻¹`, and `‖(Θ M^{(σ₁σ₂)})(a,b)‖ ≤ C (1-t)⁻¹ exp(-c·zdistD(a-b)/ellT L g t)`. `BAReal = BASelf ∧ κ ≤ Im m`
(`#print`). Constants fixed before `L, g, E, m`; all four charge pairs (mixed included); marginal constant 1 is stronger
than the ticket's `C/(1-u)`; rate `ellT L g t` is the `BAProp5` rate. `baComp_holds : BACompBound d Λ κ` for all `d, Λ, κ`.

| target | pin / ticket mathematics | verdict on statement |
|---|---|---|
| 1 `baEMn2PolyFacts` | `emn2PolyFacts` at the BA reading, no extra hypothesis | matches |
| 2 `baEMn2ExpFacts` | `emn2ExpFacts` at the BA reading; (B) eventually in `n`, `u ∈ [0,T0]`, as pinned; no `0 < d` | matches |
| 3 `BACompBound`/`baComp_holds` | ticket item 3: mixed pair and every `σ`, decay at `ℓ_t(g)`, marginals | matches (stronger marginal) |
| 4 `baEMn2ExpHK` | `emn2ExpHK` at the BA reading; extra `3 ≤ d` (from `baProp5_holds`) | matches with `3 ≤ d` (T2118a) |
| 5 pins | `stEMn2PolygL_of`, `stEMn2ExpJgL_of`, `stEMn2ExpgL_of` at BA; L-pins stay premises | matches |
| 6 `baSTContractM(_flow)` | `STContractM` body at `H = seqHflowBA`, `z = ztOf`, `Im m > 0`, `u < 1` | matches |

Item 5, "second estimate": paper `3_5:427-440` lists `(eq:MG_conclusion)`, then "In particular … `(eq:MG_conclusion2)`"
(specialisation `Ψ = (W^{-c₀}B)^{1/2}` of the first), then "Second, … `(eq:MG_conclusion3)`". The second estimate is
the `J`/`Ĵ` pair, delivered; `MG_conclusion2` has no generic Lean form (`grep -rn MG_conclusion2 RBM3D | wc -l` -> 0).
Accepted; recorded as delta T2416c.

C1: BAT-C2 constants depend on `(d, Λ, κ)`; (HK) uses `Λ = 𝔡⁻¹`; (B) uses `cB = (𝔡⁻²+1)⁻¹` and the exponent
`c = min(2𝔡𝔠, ε)/2`, which the pin quantifies after `𝔠, ε` (same as the band `ST_Bdata_holds`). No scalar `m`, no
smallness of `g` (BAT-C2 instance at `g₀` from `(L,g) = (4,10)`), `κ ≤ Im m` enters only through `BAdom`/`BAReal`.

## 3. Vacuity, hidden hypotheses, cycles

- Every target's hypotheses are in its signature; the fact blocks are pinned `def`s of T2404 and `BAFlow`/`baFMz`
  are merged definitions (main `88d1b63`); no new structure carries a hypothesis field.
- The `g` vs `g₀` reading (ticket (iii)): `Bctl`, `emn2ExpEllStar` read `sz.lam n`; the carrier kernel `K` is at
  `g₀ = BAflowLam0 ≤ g` (`EMn2BA_K_two` = `baKsol_two`); the transfer uses `EMn2BA_ellT_mono_g : g₀ ≤ g → ellT L g₀ t ≤ ellT L g t`
  (proved, `EMn2BA:591`), so the far window at `g` is contained in the far window at `g₀`. Consistent.
- No cycle: imports are merged modules only (`EMn2Exp2`, `Contract`, `FlowPins`, `KSolve`, `KInduct`, `Prop6Path`,
  `KKernel`, `GreenSchur`, `Ward`); nothing imports `EMn2BA` except the root line.
- External hypotheses: none added. The stage-L premises `STInitialGT2gL`, `STLWassmgL`, `STLWassmExpgL` are premises of
  the pins as pinned in `Step2Gen`, not new.

## 4. Compiled nonempty instances (`d = 3`; all inside `EMn2BA.lean`, built above)

| target | example (line) | data | deterministic hypotheses |
|---|---|---|---|
| 1 | :854 | `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔡,𝔠)=(1/2,1/10,1/10,1/6)`, `n=3` (`L=16`, `W=32768`), `u=1/2 ≤ t₀` | all discharged |
| 2 | :871 | same; (T), (E) at `u=1/2` and `u=t₀`; (B) at an `n` from `∀ᶠ` | all discharged |
| 3 | :886, :902 | `MFixedPointInst.P` (`L=4`, `Λ=10`, `BAReal` proved), `t=1/2`, every `σ`, `a=0`, `b=(2,0,0)`, `zdistD=2` (`decide`) | all discharged |
| 4 | :968 | `sz0` flow, `t≡1/2`, any `D>0`; `n` from `∀ᶠ` ∧ `(log W)^{3/2} ≤ L/2`, `a=(L/2,L/2,L/2) ≠ b=0`, far condition proved | all discharged |
| 5 | :1024, :1035, :1053 | `sz0` flow, `t≡1/2`, `ε₀=1/20`, `Ψ0`/`W^{-1}` (`Ψ0_class`, `Ψ1_window`), `ℓ = ellT` (`EMn2BAInst_ell_range`) | discharged; `hI`, `hA` (stage-L pins), `J`, `hJ` stay hypotheses |
| 6 | :1074, :1086 | `sz0` flow `n=3`, `u=1/2`, `(m,k)=(2,1)`, `σ=(+,-)`; generic form at `m=i`, `E=0` | all discharged |

No `N = 0`, empty index, collapsed window or `False` premise; the (HK) far window is shown nonempty (`a ≠ b` and
`ℓ* ≤ |a-b|_∞` proved), so (HK) is not applied vacuously.

## 5. Paper deltas

| Lean/paper difference | coverage |
|---|---|
| (HK)/BAT-C2 used at flow coupling `g₀ = √t₀ g` with transfer to `ℓ*_t(g)` | candidate T2416a |
| marginals of `Θ M^{(σσ')}` with constant exactly 1; explicit `(C,c)` in `(d,Λ,κ)` | candidate T2416b |
| `3 ≤ d` on the `J`/`Ĵ` forms and (HK) | T2118a (in `docs/paper-deltas.md` D269) and T2416c |
| `J` form: random `J ≥ 0`, `J ≥ W^{-d}` dropped (paper `7_8:1996`: deterministic, `≥ W^{-d}`) | T2404a (proposed in T2404 report), re-proposed in T2416c |
| `(eq:MG_conclusion2)` has no Lean form | candidate T2416c |

```
$ grep -n "T2404" docs/paper-deltas.md | head -1   ->  (no hit: T2404a not yet appended by the dispatcher)
```
All statement differences are covered by candidates.

## 6. Observations (no verdict effect)

- O1. Unpinned public helpers without the stem `EMn2BA_`: `baComp_Q_row`, `baComp_Q_col`, `baTheta_row_le`,
  `baTheta_col_le`, `baComp_row_le`, `baComp_col_le` (§3 (E)); `git grep -w <name> main -- RBM3D` -> 0 hits for each,
  so no clash at `88d1b63`. They are the components of the public BAT-C2 lemma the ticket asks for.
- O2. `set_option maxHeartbeats 800000 in` on `baEMn2ExpFacts` (allowed; same limit as `ST_Bdata_holds`).
- O3. The full `lake build` was not rerun here (hub runs it at merge).

## Verdicts

| target | verdict |
|---|---|
| 1 `baEMn2PolyFacts` | PASS |
| 2 `baEMn2ExpFacts` | PASS |
| 3 BAT-C2 `BACompBound` / `baComp_holds` | PASS |
| 4 `baEMn2ExpHK` | PASS |
| 5 `baSTEMn2Poly`, `BAEMn2ExpJ`/`baSTEMn2ExpJ`, `baSTEMn2Exp` | PASS |
| 6 `baSTContractM`, `baSTContractM_flow` | PASS |
| 7 C1 / 8 instances / 9 no registry | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed.
