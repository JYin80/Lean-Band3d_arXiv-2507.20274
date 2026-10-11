Auditor model: claude-opus-5-5

# T2418 audit, round 1 (stage 2): Sun Oct 11 14:50:21 UTC 2026 (`date -u`)
Inputs: ticket `docs/tickets/T2418.md`, Amend 1 (`T2418-amend-1.md`, CONTROL H216, H219; binding), prove report `docs/reports/T2418-prove.md`,
branch `t/T2418` at 3bccf41; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2418-audit1` (detached at 3bccf41, fresh). Scratch: scratchpad `T2418/`.
Endpoint targets: Target 1 (S1 pin `BAExp14aS1`), Target 3 (`baExp14a_S1_holds`), Target 4 (instances). Target 2 (toolbox twins) and Target 5 (constants)
are checked as part of these; Target 6: no registry entry.

## 1. Statement (Target 1 / 3)
S1 is the probe def, which the 1a-audit round 2 passed (`docs/reports/T2418-1a-audit.md`, verdict PASS). The final text against the probe (H219 says "verbatim"):
```
$ diff <(sed -n 35,112p RBM3D/Probe/T2418Pins.lean) <(sed -n 52,129p RBM3D/Graph/BAExp14aB.lean) && echo IDENTICAL
IDENTICAL
```
Against the consumer `BALWCutExpTw` (`t/T2398:RBM3D/Probe/T2398Pins.lean:434-440`):
```
$ diff <(git show t/T2398:RBM3D/Probe/T2398Pins.lean | sed -n '434,440p') <(sed -n '123,129p' RBM3D/Graph/BAExp14aB.lean)
1c1,2
< def BALWCutExpTw (d : ℕ) : Prop :=
---
> It does **not** cover the `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM` (L4b2) nor the `∂tr` children (S3). -/
> def BAExp14aS1 (d : ℕ) : Prop :=
4,7c5,7
<       STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
<       STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
<       PrecL sz μ (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
<         (fun n p _ => ‖∫ ω, LWcutg (baFMz sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
---
>       STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
>       PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
>         (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
```
Point by point, against the ticket and Amend 1:
- The binders, their order (`3 ≤ d`, `κ ε 𝔡 > 0`, `𝔠`, `sz`, `z`, `BAFlow`, `0 ≤ t ≤ BAflowT0`, `μ = seqP (sz.withLam 0)`), the carrier `baFMz`, the `U_n` side condition
  and the bound `(1-t)⁻¹ B^{5/2}` are all identical to the consumer's. The only extra index is the family tag `Fin 6`, so each family is bounded separately (stronger than a bound on the sum).
- Premises: `STLocalEntrygL` and `LWAvgLawgL` only. As Amend 1 D1 requires, there is no `|𝔼 tr| ≺ B²` premise. There is also no
  `STKboundgL`/`STKwardgL` (D3), no `tw*` name and no `BATwist*`:
  `sed -n '123,129p' … | grep -c "STKboundgL\|STKwardgL\|BATwist"` gives `0`.
- Families against design §1 table (`T2398-design.md:34-38`) and `lanlw` (`paper/tex/B_graphical_lemmas.tex:361-372`, `(eq:BE)`). I read them off the def at B:52-120:
  `MM`: `X_{[α]} M_{xα}M_{αy}`. `T1`: `Σ_β (W-1)_{αβ} M_{xβ}M_{βy}`. `T3A_k`: `W^{(k)}_{αw} M_{wγ} (t X_{[γ]}) G_{γy} Ǧ_{xw}`, where `Σ_δ S_{γδ}Ǧ_{δδ} = tX_{[γ]}`.
  `C1`: `M_{xα}·tX_{[α']}·M_{αα'}G_{α'y}`, the first term of `(eq:BE)` on `Ǧ_{αy}`. `C2`: `tX_{[α']}·M_{xα'}G_{α'α}·M_{αy}`, the same term on `Ǧ_{xα}`.
  Every family carries the outer weight `W^{-2d}Σ_{x∈[a],y∈[b]}` and the tail `Ḡ_{xy}` (σ = false) or `G_{yx}` (σ = true).
  The `W − 1` coefficient is D402's corrected `M⁺S⁺`, through `BAlwW`. The scope agrees with D2 and D4: the `∂Ḡ_{xy}` children go to L4b2, and the `∂tr`, `T2a/b`, `T3B`, `T3C` terms are absent.
- The red charge `σc = false` is defined as the conjugate of the blue family at the swapped blocks (`BAExp14aS1Fam`). This is a labelling choice. The link
  `LWcutg … false = star (LWcutg … true …)` is owed by L4a2 (prove report (d) O4). It does not weaken S1 as a pin.
- Target 3 `baExp14a_S1_holds (d : ℕ) : BAExp14aS1 d` (B:1692) proves the pin for every `d`, with no extra hypothesis.
- C1 (Target 5): `BAExp14a_facts_of_flow (hk : 1 ≤ k) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) : ∃ CM S, … ∀ᶠ n, … BAExp14a_Facts …` (B:633):
  no smallness of `g`; the constants depend on `(k, κ, 𝔡)`.
Verdict on the statement: **PASS**.

## 2. Vacuity, hidden hypotheses, cycles
- `BAExp14aS1` mentions only merged defs (`BAFlow`, `BAflowT0`, `baFMz`, `PrecL`, `STLocalEntrygL`, `LWAvgLawgL`, `BAlwW`, `Iblk`, `STblk`) and the families of this file.
  It does not refer to itself.
- The structure `BAExp14a_Facts` (B:391, fields `ht0`, `ht1`, `hη`, …) is not a premise of S1. `baExp14a_S1_holds` discharges it from `BAFlow` through
  `BAExp14a_facts_of_flow`.
- `PrecL` is `StochDomAt μ sz.size` of a deterministic quantity `‖∫…‖`, so the conclusion is a real `N^ε`-bound and not trivially true.
- Dependencies: every import of both files is on `main` except `RBM3D.Graph.BAExp14a`, which is file A of this ticket:
```
RBM3D/Graph/BAExp14aB.lean <- RBM3D.Graph.BAExp14a NOT on main
(all other 12 import lines: "on main")
```
- External hypotheses: none. `STLocalEntrygL` and `LWAvgLawgL` are Step 1/2 pins (other gates). Verdict: **PASS**.

## 3. Compiled nonempty instance (Target 4)
`RBM3D/Graph/BAExp14aB.lean` §B10 (compiled in the module build of §4):
```
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  baExp14a_S1_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA
example (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - (1 / 2 : ℝ) := by …   -- U_n nonempty for every n
```
- Every deterministic hypothesis is discharged: `3 ≤ 3`, the positivity conditions, `flow_sz0`, `0 ≤ 1/2` and `1/2 ≤ BAflowT0`. Both data lemmas are merged:
```
main:RBM3D/BA/FlowPins.lean:1214:theorem flow_sz0 : BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq := by
main:RBM3D/BA/FlowPins.lean:1254:theorem half_lt_t0 (n : ℕ) : (1 / 2 : ℝ) < BAflowT0 sz0 zSeq n := by
```
- Only `hE` and `hA` stay as hypotheses. They are the stochastic Step 1/2 pins, which the ticket allows at statement level (§10 pattern).
- The data are nondegenerate: `d = 3`; at `n = 0`, `L = 4`, `W = 32`, `λ = 1/64`; `t = 1/2`. The index set `U_n` is proved nonempty for every `n`, and a further example shows `BAExp14a_Facts` holds eventually along `sz0`.
Verdict: **PASS**.

## 4. Build, axioms, hygiene, diff
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2418-audit1 && lake build RBM3D.Graph.BAExp14a RBM3D.Graph.BAExp14aB   # error/result lines only
Build completed successfully (3981 jobs).
EXIT=0
$ grep -c "^warning: RBM3D/Graph/BAExp14a" build.out
0
$ lake build RBM3D   # full library on the branch, audit worktree
Build completed successfully (4226 jobs).
EXIT=0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2418-check.lean > /dev/null 2>&1; echo "check EXIT=$?"
check EXIT=0
$ ax.lean: import RBM3D.Graph.BAExp14aB; #print axioms RBM.BA.<n> for all 157 top-level names of the two files
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
157
'RBM.BA.baExp14a_S1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14aS1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14aS1Fam' depends on axioms: [propext, Classical.choice, Quot.sound]
$ assert.lean: import RBM3D; import RBM3D.Graph.BAExp14aB; #assert_rbm_axioms
$ lake env lean assert.lean > assert.out 2>&1; echo "assert EXIT=$?"; grep -c error assert.out; grep -c Exp14a assert.out
assert EXIT=0
0
0
axiom audit: 11753 theorems, 3580 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -nE "sorry|admit|native_decide|^axiom |^\s*axiom " RBM3D/Graph/BAExp14a.lean RBM3D/Graph/BAExp14aB.lean | wc -l
       0
$ wc -l RBM3D/Graph/BAExp14a.lean RBM3D/Graph/BAExp14aB.lean      # stop line 2,000 per file (binding)
    1307 RBM3D/Graph/BAExp14a.lean
    1771 RBM3D/Graph/BAExp14aB.lean
$ git diff --name-status main...t/T2418
A	RBM3D/Graph/BAExp14a.lean
A	RBM3D/Graph/BAExp14aB.lean
A	RBM3D/Probe/T2418Pins.lean
$ git diff main...t/T2418 -- RBM3D.lean | wc -l
       0
$ name clash: git grep -lw <n> main (46120c3) -- RBM3D RBM3D.lean, for the 157 names
public names: 157, with hits on main: 0      (every name starts with BAExp14a / baExp14a)
```
- A note on the axiom run: a first run without `import RBM3D` failed `#assert_rbm_axioms` with 44 premises proved only in modules it did not import, none of them `Exp14a`. The run above, with `import RBM3D`, passes.
- `RBM3D/Probe/T2418Pins.lean` is in the diff but is not a sole writable file. It is the probe that H219 authorizes ("the probe stays on the branch", never merged). The hub brings in only the two
  `Graph/` files and adds the two root imports (rule (A) 3-4). No frozen signature changed: the diff adds three new files and modifies none.
Verdict: **PASS**.

## 5. Paper deltas
| Lean/paper difference | coverage |
|---|---|
| bound `(1-t)⁻¹B^{5/2}` vs paper `η_t⁻¹B^{5/2}` (`η = (1-t)Im m`, `κ ≤ Im m`): equal up to the constant `κ⁻¹` | proposed `T2418b` (prove (d)) |
| no improved average `O(B²)` (`lem:improve_exp_aver`) used; `|𝔼X_c| ≺ B^{3/2}(1-t)⁻¹` from `lanlw` with `f = 1` | proposed `T2418a` (Amend 1 D1; prove (d)) |
| `W - 1` coefficient `M⁺S⁺`, not the printed `S⁺` of `GGGamma` (`B:393-405`) | existing D402 (`docs/paper-deltas.md:1361`) |
| `U_n` side condition `λ²/L^d ≤ 1-t` | inherited verbatim from the consumer pin `BALWCutExpTw` (T2398); not new here |
| families tagged separately (`Fin 6`), red charge by conjugation | Lean labelling, stronger than the summed bound; no paper difference |
Coverage is complete. Verdict: **PASS**.

## Observations (no verdict effect)
1. The prove report has 371 lines, above the 300 of CLAUDE.md §6 and the ticket's 200 (its O1). Its section (b) does not open with the per-file line count as
   the ticket asks: the count comes second, after `git diff --stat`. Neither point changes a statement, the instance, the build or the axioms.
2. Target 2 is narrower than the ticket text. As the 1a-audit round 2 recorded (observation 1), it omits the twins of `ward2`, `kward`, §7 and `lwExpTerm4_L3`/`R23`, and `lwExpTerm4_kerSum` is not imported.
   This follows Amend 1 D2/D3. No sibling ticket consumes `BAExp14a*`, and L4b2 prices its own helpers.
3. The stochastic lemmas that carry `LWAvgLawgL` are `private`. L4a2/L4b2 can therefore reuse only the public toolbox and `baExp14a_S1_holds`.
4. L4a2 owes the six-family decomposition of `LWcutg` and the identity `LWcutg … false σo ac ao = star (LWcutg … true (!σo) ao ac)` (prove (d) O4). These belong to the assembly, not to S1.

## Verdict
- Target 1 (S1 pin `BAExp14aS1`): **PASS**.
- Target 2 (toolbox, reduced by Amend 1): **PASS**.
- Target 3 (`baExp14a_S1_holds`): **PASS**.
- Target 4 (instances): **PASS**.
- Target 5 (C1): **PASS**.
- Target 6 (registry): none needed; **PASS**.
- Overall: **PASS**. No dispatcher sign-off is needed.
