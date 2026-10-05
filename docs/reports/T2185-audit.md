Auditor model: claude-opus-5-5

# T2185 audit (round 1) — LW-11b `Graph/AuxGraph2` (claim:xi, (eq:Gbyxi), radii)

Started `Mon Oct  5 14:47:54 UTC 2026` (`date -u`). Branch `t/T2185` = `7435b5a`; merge-base with `main` = `7771372`
(`main` = `f23811b`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2185-audit1` (detached at `7435b5a`).

## 1. Files touched

```
$ git diff --name-status main...t/T2185
A	RBM3D/Graph/AuxGraph2.lean
$ git diff main...t/T2185 | grep -nE "^\+.*\b(sorry|admit|native_decide|axiom)\b" ; echo $?
1
$ git diff main...t/T2185 | grep -nE "^\+.*(LocCost|scost|locCost)" ; echo $?
1
```
Only the sole writable file; no merged file (frozen signature) touched; `RBM3D/Test/Axioms.lean` unchanged (none expected).

## 2. Statements against the pin (check file `docs/tickets/checks/T2185-check.lean`, section 2)

Text diff (declaration block from `def NAME` to the first blank line, both files):
```
== lwXiSq: check 6 lines, file 6 lines      IDENTICAL
== lwXiVar: check 2 lines, file 2 lines     IDENTICAL
== LWXiClaim: check 13 lines, file 13 lines IDENTICAL
== LWGbyXi: check 15 lines, file 15 lines   IDENTICAL
== LWEntryPsi: check 13 lines, file 13 lines IDENTICAL
== LWXiRad: check 4 lines, file 4 lines     IDENTICAL
```
Elaboration check: scratch file = `import RBM3D.Graph.AuxGraph2` + the check file's `namespace RBM.Graph.T2185Check … end`
block verbatim + the lines below (`lake env lean`, audit worktree):
```
example : @RBM.Graph.lwXiSq = @RBM.Graph.T2185Check.lwXiSq := rfl
example : @RBM.Graph.lwXiVar = @RBM.Graph.T2185Check.lwXiVar := by rfl
example : RBM.Graph.LWXiClaim = RBM.Graph.T2185Check.LWXiClaim := by rfl
example : RBM.Graph.LWGbyXi = RBM.Graph.T2185Check.LWGbyXi := by rfl
example : RBM.Graph.LWEntryPsi = RBM.Graph.T2185Check.LWEntryPsi := by rfl
example : RBM.Graph.LWXiRad = RBM.Graph.T2185Check.LWXiRad := rfl
example : ∀ d, RBM.Graph.T2185Check.LWXiClaim d := RBM.Graph.lwXiClaim_holds
example : ∀ d, RBM.Graph.T2185Check.LWGbyXi d := RBM.Graph.lwGbyXi_holds
example : ∀ d, RBM.Graph.T2185Check.LWEntryPsi d := RBM.Graph.lwEntryPsi_holds
example : RBM.Graph.T2185Check.LWXiRad := RBM.Graph.lwXiRad_holds
--> exit 0, no error lines
```
So the four `*_holds` prove exactly the dispatcher's pinned `Prop`s (no extra hypothesis; `3 ≤ d` only inside the pins).

Target 2 (deterministic; statements read from `AuxGraph2.lean:135-200, 507-511, 1160-1175`) against the ticket text:
- `lwXiVar_nonneg` (`0 ≤ lwXiVar …`), `lwXiVar_symm` (`… n a₁ a₂ ω = … n a₂ a₁ ω`): as described, no hypothesis.
- `lwXiSq_ge_W (hρ : 0 ≤ ρ n) a ω : (W^d)⁻¹ ≤ lwXiSq … n a a ω`: as described.
- `lwXi_gexRHS_le {R} (hR : 0 ≤ R) (hρ : 2R+1 ≤ ρ n) x y a b ω (hx : zdistD([x]-a) ≤ R) (hy : zdistD([y]-b) ≤ R) :
  STgexRHS sz n (E n) (t n) ω (STblk x) (STblk y) ≤ lwXiSq sz E t ρ n a b ω`: as described (note: no `x ≠ y` needed).
- `lwXi_ward_sum (hE : |E n| < 2) (ht1 : t n < 1) (hρ : 0 ≤ ρ n) ω {A} (hA : ∀ x y, ‖STGM … x y‖ ≤ A) a₁ :
  Σ a₂ lwXiSq … ≤ 2(2ρ+1)^(2d)((W^d·etaT)⁻¹(1+A)) + (2ρ+1)^d (W^d)⁻¹`: the ticket's bound with constants as pinned;
  the hypothesis `0 ≤ t n` is dropped (a strengthening; prove report (d) records it).
- `lwGbyXi_hxi`: for `0 ≤ c` and the sample event on the `R n`-balls, returns `0 ≤ ξ` and the premise `hξ` of `LWGtoAG` at
  `D = lwSampleData sz n (zt (E n) (t n)) (t n) M S Sp ω`, `ξ = c·lwXiVar`. Its fit is verified by compilation: the composed
  instance (§4 below) feeds `.1`, `.2` directly to `lwGtoAG_holds`.

Paper check (`7_8:876-890`): `(eq:xia1a2)` uses `max_σ` over the two charges and radius `(log W)^{1+2ε₁}`; Lean sums the two
charges and takes `ρ` as a parameter with `ρ+1 = N^{o(1)}` (covered by T2185a, T2185b). `(eq:Gbyxi)` with `ξ([x],[y]) + W^{-D}`
is split into `LWEntryPsi` and `LWGbyXi` on the `R`-balls (covered by T2185c). `(eq:Gbyxi2)` is the merged `LWXi`
(`LWPins.lean:360`): symmetric/non-negative, `ξ ≺ Φ(zdistInf)`, `Σ ξ² ≺ (W^d η)⁻¹` — the conclusion of `LWXiClaim`. The extra
input `‖G−M‖_max ≺ W^{-ε₁}` is covered by T2185d.

Verdict on statements: all six pinned blocks verbatim; target 2 as described in the ticket (one harmless strengthening).

## 3. Hidden hypotheses, vacuity, cycles

- No new structure; the pins are `Prop` definitions whose hypotheses are all explicit binders (pinned by the dispatcher).
  `LWLoop2`, `LWPsiAll`, `STFlow` and the entry law are the inputs the ticket decided ("Probabilistic input").
- Imports (`AuxGraph2.lean:6-11`): `Graph.AuxGraph`, `Graph.LWPins`, `Green.GbEXP`, `Induction.ConArgDet`,
  `Induction.PerTimeCalc`, `Induction.DecayLoopB` — all merged on `main`; not `RBM3D`. No cycle.
- `lwGbyXi_holds`/`lwEntryPsi_holds` use `lem_GbEXP` via the merged proved `stGbEXP_holds` (axioms below are clean, so no
  owed premise is smuggled in).
- External-hypothesis limit check: no new external hypothesis is introduced (the `Prec` entry law is the first half of
  `(initialGT2)`, i.e. merged `LWInit`'s first conjunct, per the ticket).

## 4. Compiled nonempty instances (`AuxGraph2.lean:1304-1498`)

Data: `d = 3`, `sz0`, `z0`, `flow_z0`, `tInst` (`tInst_range`), `Φ0`, `psiAll0` (`ε₀ = 1/20`, `C₁ = C₂ = 2`, `C₃ = 1`,
`Cc ≡ 1`), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `ε₁ = 1/20`, `R0 n = (log W_n)^{3/2}`, `ρ0 n = 2(log W_n)^{3/2}+1`.

| Target | Example (line) | Deterministic hyps discharged | Kept as hypothesis |
|---|---|---|---|
| `lwXiSq_ge_W`, `0 < lwXiVar` | 1348 | `0 ≤ ρ0 n` (proved), all `n, a, ω` | — |
| `lwXiVar_nonneg/_symm` | 1359 | — | — |
| `lwXi_gexRHS_le` | 1367 | `0 ≤ R0 0`, `2R0+1 ≤ ρ0`, `x ≠ y` exhibited (`auxGraph2_exists_ne`), `hx`,`hy` at `a=[x]`,`b=[y]` | — |
| `lwXi_ward_sum` | 1381 | `|E| < 2` (`abs_lemE_lt_two`), `tInst 0 < 1`, `0 ≤ ρ0 0`, `hA` with `A = Σ‖(G−M)_{xy}‖` | — |
| `lwXiClaim_holds` | 1392 | `STFlow` (`flow_z0`), `t` range, `LWPsiAll` (`psiAll0`), radius (`lwXiRad_holds … 2 1 (3/2)`) | `LWLoop2 … Φ0`, entry law |
| consumer `inst_Anp` | 1400 | as above | `LWAnp 3`, `LWLoop2`, entry law |
| `lwGbyXi_holds` | 1423 | `0 ≤ R0`, `2R0+1 ≤ ρ0`; index set nonempty at every `n` (proved) | entry law |
| `lwEntryPsi_holds` | 1440 | as for `lwXiClaim_holds` | `LWLoop2`, entry law |
| `lwGbyXi_hxi` | 1450, 1468 | composed into `lwGtoAG_holds` at `lwSampleData sz0 0 …` | `0 ≤ c`, the sample event `h`; LW-02's premises of `lwGtoAG_holds` |
| `lwXiRad_holds` | 1495 (via 1327) | `C=2, C'=1, K=3/2 ≥ 0`, `sz0_tendsto` | — |

The kept hypotheses are the other gates' stochastic inputs the ticket names (`LWLoop2`, the entry law, `LWAnp`) or a sample
event. No `N = 0`, empty index or collapsed window: `W_n ≥ 1`, `L_n ≥ 3`, `ρ0 ≥ 1`, `x ≠ y` exhibited at every `n`.
All compile (build in §5).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.AuxGraph2
✔ [3845/3845] Built RBM3D.Graph.AuxGraph2 (9.0s)
Build completed successfully (3845 jobs).
exit 0
$ grep -c "^error" build.log
0
$ grep AuxGraph2 build.log            # no warning line for the new file
✔ [3845/3845] Built RBM3D.Graph.AuxGraph2 (9.0s)
```
`#print axioms` (same scratch file as §2, `lake env lean`, exit 0):
```
'RBM.Graph.lwXiClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwGbyXi_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwEntryPsi_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiRad_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXi_ward_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXi_gexRHS_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiSq_ge_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiVar_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwXiVar_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwGbyXi_hxi' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Name clashes (`git grep -w <name> main -- RBM3D`): 0 hits for each of the 16 new public names. Every other declaration
in the file is `private` and prefixed `auxGraph2_` (grep for unprefixed `theorem|def|abbrev` outside the pinned names: none).

## 6. Paper-delta coverage
Prove report (d) proposes `T2185a` (sum vs max of the two charges), `T2185b` (parameter radius `ρ`, `zdistInf` ball,
LW-02 radii `(log W)^{3/2}` vs `(log W)^{1+ε₁}`, `(log W)^{1+2ε₁}`), `T2185c` (split of `(eq:Gbyxi)`, no `W^{-D}`),
`T2185d` (extra input `‖G−M‖_max ≺ W^{-ε₁}`). These are exactly the four the ticket expects and cover every Lean/paper
difference found in §2. No further delta needed.

## 7. Observations (no effect on verdict)
- O1. The `lwGbyXi_hxi` instance keeps `c` general with `0 ≤ c` as a hypothesis instead of a concrete `c` (e.g. `c = 1`);
  the theorem is a type-match, the example is at concrete data and the composed example (1468) shows the fit with
  `lwGtoAG_holds`. Not a degeneracy.
- O2. `lwXi_ward_sum` omits `0 ≤ t n` (stronger than the ticket's description); recorded in prove report (d).

## Verdict
| Target | Verdict |
|---|---|
| 1 `lwXiSq`, `lwXiVar` (verbatim) | PASS |
| 2 `lwXiVar_nonneg`, `lwXiVar_symm`, `lwXiSq_ge_W`, `lwXi_gexRHS_le`, `lwXi_ward_sum` | PASS |
| 3 `LWXiClaim` / `lwXiClaim_holds` | PASS |
| 4 `LWGbyXi` / `lwGbyXi_holds`, `lwGbyXi_hxi` | PASS |
| 5 `LWEntryPsi` / `lwEntryPsi_holds` | PASS |
| 6 `LWXiRad` / `lwXiRad_holds` | PASS |
**T2185: PASS.** No dispatcher sign-off needed.
