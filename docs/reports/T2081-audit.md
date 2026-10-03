Auditor model: claude-opus-5-5
# T2081 audit (round 1) — ST2-05 `stScaleExists_holds`
Branch `t/T2081` @ 5f12e8f; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2081-audit1` (detached). Single target.

## 1. Statement against the pin
```
$ grep -n "^theorem stScaleExists_holds" RBM3D/Induction/Step2Scale.lean | sed 's/ := by//;s/^[0-9]*://' > a.txt
$ grep -o 'theorem stScaleExists_holds (d : ℕ) : STScaleExists d' docs/tickets/T2081.md > b.txt
$ diff a.txt b.txt && echo IDENTICAL
IDENTICAL
$ lake env lean ax.lean     (import RBM3D.Induction.Step2Scale)
stScaleExists_holds : ∀ (d : ℕ), STScaleExists d
$ git diff --stat 4128ef0 main -- RBM3D/Induction/{Step2Defs,Step2Core,ScaleFacts,Defs}.lean RBM3D/Green/Pins.lean RBM3D/Defs/Tail.lean RBM3D/Test/Axioms.lean
 RBM3D/Test/Axioms.lean | 3 +++          (pin file Step2Defs.lean unchanged between branch base and main)
```
The target is the merged pin `STScaleExists d` (`Step2Defs.lean:656`) verbatim, for every `d`, no added
hypothesis. The pin quantifies `κ ε 𝔡 > 0, 𝔠, sz, z, STFlow, s t, 0 ≤ s ≤ t ≤ lemT z`, then `∃ Kseq,
STScaleAdm`; all of `STScaleAdm`'s clauses other than `K_0 = 0` are `∀ m, ∀ᶠ n` (DECISIONS §29 (4)), as
the ticket requires. Not a special case or conditional adapter. **Statement: PASS.**

## 2. Hidden hypotheses, vacuity, cycles
- The theorem's only binder is `d : ℕ`; no structure carries a proof obligation (the `Kseq` is constructed:
  `private def st2sStep`/`st2sSeq`, lines 126–133; choice via `Classical.choose` on an IVT existence).
- Upstream facts used are merged theorems: `RBM.Green.v3_premises_of_stFlow`, `RBM.Ind.scaleFacts_R1`,
  `STBctl_ge`, `STBctl_mono`, `ST_tailT_mono_time`, `tailT_antitone` (imports: `Step2Core`, `ScaleFacts`,
  `Green.Pins`, Mathlib). New continuity lemma `st2s_tailT_continuousOn` proved in the file.
- No external hypothesis (none to limit-check). No cycle: the file is new and nothing imports it; the
  axiom print below is clean, so no owed premise enters as an assumption.
- The pin's premise `STFlow` is satisfiable: merged `flow_z0`, `flow_z1` (axioms clean, below).

## 3. Compiled nonempty instances (`d = 3`)
```
$ sed -n 573,592p RBM3D/Induction/Step2Scale.lean   (excerpt)
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq :=
  stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => sixteenth_le_lemT n)
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz1 sInst tInst Kseq :=
  stScaleExists_holds 3 ... (1 / 6) sz1 z0 flow_z1 sInst tInst ...
example : ∃ Kseq ..., STScaleAdm sz0 sInst tInst Kseq ∧
    ∀ᶠ n in atTop, 0 ≤ Kseq 1 n (1 / 32) ∧ Kseq 1 n (1 / 32) ≤ Kseq 2 n (1 / 32) := ...
$ lake env lean ax.lean   (instance data)
flow_z0 : sz0.STFlow (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0
flow_z1 : sz1.STFlow (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0
sixteenth_le_lemT : ∀ (n : ℕ), 1 / 16 ≤ RBM.lemT (z0 n)
def RBM.Gauss.InductionDefsInst.sInst : ℕ → ℝ := fun x => 0
def RBM.Gauss.InductionDefsInst.tInst : ℕ → ℝ := fun x => 1 / 16
def RBM.Gauss.SizesInst.sz0 : RBM.Gauss.Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
def RBM.Gauss.InductionDefsInst.sz1 : RBM.Gauss.Sizes 3 := sz0.withLam fun n => ↑(sz0.W n) ^ (-3 / 2 + 1 / 10)
'RBM.Gauss.InductionDefsInst.flow_z0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.InductionDefsInst.flow_z1' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Every hypothesis is discharged at concrete data (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `L_n = 4(n+1)
≥ 4`, `W_n = (2(n+1))^5`, nondegenerate window `s ≡ 0 < t ≡ 1/16 ≤ lemT(z0 n)`); no stochastic pin left as
hypothesis; no `N = 0`, empty index, collapsed window or `False` premise. Instance 3 reads a clause at
the interior time `u = 1/32`. They compile with the file (below). **Instance: PASS.**

## 4. Build, hygiene, axioms, scope
```
$ lake build RBM3D.Induction.Step2Scale 2>&1 | grep -E "error|Step2Scale|Build completed"
Build completed successfully (3721 jobs).
$ lake env lean RBM3D/Induction/Step2Scale.lean 2>&1 | grep -E "^RBM3D.*(error|warning)"; echo exit=$?
exit=0          (no error or warning lines from the file; warnings seen in the build are in other merged modules)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/Step2Scale.lean || echo none
none
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stScaleExists_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-only main...t/T2081
RBM3D/Induction/Step2Scale.lean
$ grep -n "^theorem\|^def\|^lemma" RBM3D/Induction/Step2Scale.lean     (public declarations)
430:theorem stScaleExists_holds (d : ℕ) : STScaleExists d := by
```
Only the sole writable file is touched (the optional `Test/Axioms.lean` registry file is not edited);
no frozen signature changed; all 23 helpers are `private` with prefix `st2s` (§3 (E)). The full
`lake build` is the hub's at merge (the prove report records one with a temporary root import).
**Build/axioms: PASS.**

## 5. Paper deltas
```
$ grep -n "STScaleAdm\|STScaleExists\|def_ell1\|STScaleOk" docs/paper-deltas.md | cut -c1-80
400:- **D87（T2039e）**：`(eq:def_ell1)` 的尺度族在 `L` 处截断（`STScaleAdm`）。
405:- **D92（T2039j）**：`STScaleAdm`/`STScaleOk` 的条款（`(eq:def_ell1)`、`(eq:monotone_Ku)`）只对大 `N` 要求...
```
Paper `3_5:570–571` defines `K'_u` as "the unique positive solution" of `𝒯_u(K'_u) = 𝒯_u(K_u)(W^{-d}B_{u,0})^{1/6}`.
Differences between the target and the paper: the cut at `L` (D87), the eventual-in-`n` clauses (D92),
both from the pin. The proof's own differences are proposed as candidates in the prove report §(d):
T2081a (a solution `r ≥ K`, uniqueness not proved, fallback `K` outside `n ≥ n₀`), T2081b (`M(D) =
6⌈(2+D)/c₀⌉`, `c₀ = min(2𝔠𝔡, ε/2)`, against the docstring's `(D+d)/c`), T2081c (the cap's `n₀` depends on
`m`). **Coverage: PASS.**

## Observations (no verdict effect)
- O1. Clause 4 of `STScaleAdm` is the inequality `β^{1/6}𝒯(K_m) ≤ 𝒯(K_{m+1})`, not the paper's equality.
  This is the pin's form (it follows from the cut at `L`, D87), not something this ticket introduced. The
  dispatcher may want D87's wording to mention it explicitly.
- O2. In `sz0`, `L_n ≪ (log W_n)^{10}`, so at the instance data the cap clause and the floor (through
  `K_M = L`) do not bind; the general proof covers the uncut chain (`st2s_floor_arith`, `st2s_cap_arith`).
  The instance requirement is about nondegeneracy, which holds.
- O3. The owed registry line for `RBM.Gauss.Sizes.STScaleExists` (`Test/Axioms.lean`) can be removed after
  the merge (cleanup ticket), and `inst_scaleExists` (`Step2Defs.lean`) can then be discharged by
  `stScaleExists_holds 3`. Both are outside this ticket.

## Verdict
`stScaleExists_holds`: **PASS**. No dispatcher sign-off needed.
