Auditor model: claude-opus-5-5

# T2010 audit (round 1) — PT-E Laplace–Gauss lemmas — Sat Oct  3 00:39:58 UTC 2026

Branch `t/T2010` at `c29212e`, merge-base with `main` = `01b7ed8` (= `main`). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2010-audit1` (detached at `c29212e`). Scratch scripts in
`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/`.

## 1. Diff scope, build, hygiene

    $ git diff --stat main...HEAD
     RBM3D/Propagator/LaplaceGauss.lean | 895 +++++++++++++++++++++++++++++++++++++
     1 file changed, 895 insertions(+)
    $ lake build RBM3D.Propagator.LaplaceGauss 2>&1 | grep -E "^(warning|error)|Build|rror"
    warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
    Build completed successfully (2808 jobs).
    $ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^\s*(set_option|@\[implemented_by|unsafe|opaque)" $F; echo "hyg exit $?"
    hyg exit 1
    $ sed -n '1,20p' $F | grep -E "^import"
    import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
    import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
    import Mathlib.MeasureTheory.Integral.Gamma
    import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
    import RBM3D.Defs.Params
    $ grep -cE "^private (theorem|lemma|def)" $F ; public non-pinned decls (grep, filtered):
    23
    (none)

Only the sole writable file is touched; no frozen signature exists in a new file. The one extra
import is Mathlib (allowed by the ticket). The linter warning is on the pinned `lgEps` docstring.

## 2. Statements against the pins (script diff + Lean cross-check)

Text diff (docstrings removed, whitespace normalised) of `docs/tickets/checks/T2010-check.lean`
(namespace `RBM.Heat.T2010Check`) against the file:

    lgIntegrand def text identical: True
    lgGam def text identical: True
    lgEps def text identical: True
    LGKey def text identical: True      LGBulk def text identical: True
    LGZero def text identical: True     LGTail def text identical: True
    LGConvA def text identical: True    LGConvB def text identical: True
    LGConvC def text identical: True
    lg_key type == pin body: True       lg_bulk type == pin body: True
    lg_zero type == pin body: True      lg_tail type == pin body: True
    lg_convA type == pin body: True     lg_convB type == pin body: True
    lg_convC type == pin body: True

Lean cross-check: a scratch file importing `RBM3D.Propagator.LaplaceGauss`, containing the check
file's namespace body verbatim (its own copies of `lgIntegrand/lgGam/lgEps/LG*`), then

    example : RBM.Heat.T2010Check.LGKey := by unfold RBM.Heat.T2010Check.LGKey; exact RBM.Heat.lg_key
    ... (same for LGBulk/lg_bulk, LGZero/lg_zero, LGTail/lg_tail, LGConvA/lg_convA,
         LGConvB/lg_convB, LGConvC/lg_convC)
    #print axioms RBM.Heat.<each target>
    $ lake env lean a2.lean; echo "exit $?"
    exit 0

So each theorem proves the dispatcher's pin as written in the check file (not only the in-file copy).

Mathematics (ticket "Mathematics" bullet): checked by reading the pins.
- `LGKey`: `∫ τ^{-m/2} e^{-ετ - c n²/τ} ≤ Γ(m/2−1)((c/2)n²)^{-(m−2)/2} e^{-√(cε) n}`, `m ≥ 3`, `c, n > 0`, `ε ≥ 0`: the ticket's Key with `A = (c/2)n²`.
- `LGBulk`: `∃ C > 0, ∃ c' > 0` after `(m, c)` and before `(n, ε)`; `n ≥ 1`, `ε ≥ 0`; the `ε ≤ 1` and `ε ≥ 1` forms of the ticket (loss `n^{-(m−2)}`, decay `e^{-c' n √ε}` resp. `(2/ε) e^{-c' n}`). Quantifier order as in the ticket.
- `LGZero`, `LGTail`: the `n = 0` bound and (L2) exactly as in the ticket (tail with/without the gap `κ`, head `≤ min(T, 1/ε)` as two clauses).
- `LGConvA/B/C`: (L3a)–(L3c); `ellT` on `main` is `min (max (g / √|1 − t|) 1) L` (`RBM3D/Defs/Params.lean:32-33`), as the ticket's (L3b) uses it.
No special case or conditional adapter: every target is the pinned general statement.

## 3. Vacuity, hidden hypotheses, cycles

- No `structure`/`class` in the file; every hypothesis is in the theorem signatures (numeric
  inequalities on `m, c, n, ε, T, κ, d, Λ, g, t, L`). No external hypothesis; no limit check needed.
- Dependencies: Mathlib and `RBM.ellT` (merged on `main`). No other ticket's declaration; no cycle.
- Name clashes of the 17 public names:

    $ git grep -nwE "$PUB" main -- RBM3D RBM3D.lean | wc -l      -> 0
    $ git grep -nwE "$PUB" t/T2009 -- RBM3D RBM3D.lean | wc -l   -> 0   (t/T2009 = c9fd239)

## 4. Compiled nonempty instances (file lines 828–893; compiled in the build of §1)

| target | instance (all hypotheses discharged by `norm_num`/`le_rfl`/`one_pos`) | nondegenerate |
|---|---|---|
| `lg_key` | `m=3,c=1,n=1,ε=1/2`; `m=5,c=0.18,n=5,ε=0` | yes |
| `lg_bulk` | `lg_bulk 3 _ 0.18 _`, then `ε≤1` clause at `n=5, ε=1/2` and `ε≥1` clause at `n=2, ε=2` | yes, both branches |
| `lg_zero` | `lg_zero 3 _ 1 0 le_rfl`; clause 3 at `ε=1` | yes |
| `lg_tail` | `lg_tail 9 _`: clause 1 at `ε=1/2, κ=16`; clause 2 at `ε=κ=1/2`; head at `ε=1/2` both parts | yes |
| `lg_convA` | `lg_convA 3 1 one_pos` at `g=1/2,t=1/2` (`ε=10`, clause a) and `t=0.999` (`ε<1`, clause b), premises proved by `norm_num [lgEps, lgGam]` | yes, both clauses |
| `lg_convB` | `lg_convB 3 5 (1/2) (1/2)` with its four side conditions, clause (a) premise proved; clause (b) at `t=0.999` (`ℓ_t = 5`) | yes, both clauses |
| `lg_convC` | `d=3,L=5,g=t=1/2,n=7 ≤ 7.5`, all seven hypotheses proved | yes |

Every instance required by the ticket ("Instances to compile") is present. No `N = 0`, empty
range, `False` premise, or astronomically large witness; each clause's implication premise is
discharged at the concrete data (no clause is exercised only vacuously).

## 5. Axioms (from the cross-check file of §2, worktree build)

    'RBM.Heat.lg_key' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_convA' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_convB' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_convC' depends on axioms: [propext, Classical.choice, Quot.sound]

## 6. Paper deltas

    $ grep -n "T2010\|Laplace\|(L1)" docs/paper-deltas.md   -> (no match)

The targets are route-H (Fable F5/S5) lemmas, not paper statements. The one Lean/route difference
(Fable's (L1) bulk bound holds only for `ε ≤ 1`; the `(2/ε)e^{-c'n}` form replaces it for `ε ≥ 1`)
is proposed as candidate **T2010a** in the prove report §(d), as the ticket expected. No other
statement difference found. Coverage: complete.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. The prove report's §(b) narrative says `lg_convA` uses `C = 3 + 4dΛ² + 2Λ²` (smaller than
  §(a)'s table); the pin is existential in `C`, so this changes nothing.
- O2. Linter warning (line length) at line 36 is inside the verbatim-pinned docstring of `lgEps`.

## Verdicts

| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `lg_key` | = pin | none | yes | ok | n/a | PASS |
| `lg_bulk` | = pin | none | yes | ok | T2010a | PASS |
| `lg_zero` | = pin | none | yes | ok | n/a | PASS |
| `lg_tail` | = pin | none | yes | ok | n/a | PASS |
| `lg_convA` | = pin | none | yes | ok | n/a | PASS |
| `lg_convB` | = pin | none | yes | ok | n/a | PASS |
| `lg_convC` | = pin | none | yes | ok | n/a | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed.
