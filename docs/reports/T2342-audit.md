Auditor model: claude-opus-5-5

# T2342 audit (round 1) — LW-16 `lwtermExpN_of_LWterm`

Written Thu Oct  8 19:12:02 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2342-audit1`,
detached at `t/T2342` = `994900f`. Target: `RBM.Gauss.Sizes.lwtermExpN_of_LWterm : ∀ d, LWterm d → LWtermExpN d`.

## 1. Statement against the pin (check file, by script)

Scratch file = check file `docs/tickets/checks/T2342-check.lean` verbatim + `import RBM3D.Graph.LWTermExpN` + the equality `example`:

    $ grep -nE "^import|^namespace|^def|^end|^example|^#print" chk.lean
    8:import RBM3D.Graph.LWPins
    9:import RBM3D.Graph.LWTermExpN
    33:namespace RBM.Gauss.Sizes.T2342Check
    38:def T2342_lwtermExpN_of_LWterm : Prop := ∀ d : ℕ, LWterm d → LWtermExpN d
    40:end RBM.Gauss.Sizes.T2342Check
    41:example : RBM.Gauss.Sizes.T2342Check.T2342_lwtermExpN_of_LWterm := RBM.Gauss.Sizes.lwtermExpN_of_LWterm
    42:#print axioms RBM.Gauss.Sizes.lwtermExpN_of_LWterm
    43:#print axioms RBM.Gauss.LWTermExpNInst.inst_lwtermExpN_of_LWterm
    $ lake env lean chk.lean 2>&1 | grep -E "error|axioms"; echo "exit $?"
    'RBM.Gauss.Sizes.lwtermExpN_of_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Gauss.LWTermExpNInst.inst_lwtermExpN_of_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
    exit 0

    $ sed -n 414p RBM3D/Graph/LWTermExpN.lean
    theorem lwtermExpN_of_LWterm (d : ℕ) (hLW : LWterm d) : LWtermExpN d := by

The conclusion is the merged `Prop` `LWtermExpN d` (`Graph/LWPins.lean:462`, unchanged on the branch:
`git diff main...t/T2342 -- RBM3D/Graph/LWPins.lean | wc -l` = `0`), so quantifier order (fixed `κ ε 𝔡 𝔠 sz z t ε₀ Ψ ℓ`, then
`∀ D > 0`, then `Prec`), the regime subtype `1 - t n ≤ lam² / L²`, the window `ℓ` and the loss
`η⁻¹ Bctl^{1/2} W^{-d} tailW_D` are exactly those of the pin. The only extra hypothesis is `LWterm d`, which is the
ticket's statement. Matches the ticket's mathematics (`7_8:20`, `3_5:385-415`). **Statement: PASS.**

## 2. Vacuity, hidden hypotheses, cycles

- Hypotheses of the target: `LWterm d` (owed pin, LW-01) only. No structure carries new fields; the proof destructures the merged
  `LWAssmExp` (`⟨hε₀, hwin, hinit, hℓ0, hℓt, hloop⟩`) and builds the merged `LWAssm` (`⟨hε₁pos, hwin', hinit', hcls, hrel, hL2⟩`)
  for `Φ = LWPhiB sz d K t`, `K n = min ⌊ℓ n⌋₊ (L n)`, `c₀ = d`, `ε₁ = min(ε₀, d c/2)`, `c = min(2𝔡𝔠, ε)/2` (lines 414-525).
  Every component of `LWAssm` is proved from `STFlow` + `LWAssmExp` (`LWPhiB_psiAll` for class/`(eq:Psi)`; `hup` from the
  copied size bound `lwN_Bctl_le`; `LWLoop2` from `LWLoopExp` at `D' = 1/𝔠` via `lwN_tailW_le`, `lwN_Wneg_le`).
- `LWterm` is used at one specific `Φ`; it is not assumed in a weakened or trivial form. The `tailW` class is not used as `Φ`
  (ticket §152 (3) respected).
- No cycle: single import.

      $ grep -n "^import" RBM3D/Graph/LWTermExpN.lean
      6:import RBM3D.Graph.LWPins

- Dependencies are merged names on `main` (check file section 1 elaborates; the scratch compile above includes it).
- External hypothesis `LWterm`: limit check in the prove report (a) (ratio of `Φ(0)Φ(r)²` to the `tailW` bound is `1` at `r = 0`
  and `e` at `r = L`, `n`-independent). The constant `e·2^{d-2}` is `n`-independent and absorbed by `≺` (`lwN_prec_mono`,
  using `eventually_le_rpow c` and `size → ∞`). Accepted.

## 3. Compiled nonempty instance

    $ sed -n 535,544p RBM3D/Graph/LWTermExpN.lean   (abridged: hypotheses)
    theorem inst_lwtermExpN_of_LWterm (h : LWterm 3)
        (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
        (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) (D : ℝ) (hD : 0 < D) : ...
      inst_LWtermExpN (lwtermExpN_of_LWterm 3 h) hI hL D hD

This is the ticket's prescribed instance (merged `inst_LWtermExpN`, `LWPins.lean:783`, with `LWtermExpN 3` replaced by
`LWterm 3`). Remaining hypotheses `LWterm 3`, `LWInit`, `LWLoopExp` are other gates' pins (allowed). Deterministic data
(`d = 3`, `sz0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z0`, `tEnd`, `ε₀ = 1/20`, `ℓ = ℓT tEnd`, flow, `0 ≤ t ≤ lemT z`, window,
`ℓ ≤ (log W)^{10} ℓ_t`) is discharged in the merged `inst_LWtermExpN` (`flow_z0`, `tEnd_range`, `assmExpT_of`). Compiles
(build below; `#print axioms` above).

Non-emptiness of the regime subtype at `sz0` (independent numerical check by the auditor, 200 digits, `msc` = root of
`m² + z m + 1` with `Im m > 0`, `tEnd = |m|²`, `z_n = 1/2 + i N_n^{-4/5}`):

    $ python3 reg.py
    0 4 32 9.05125e-6 1.52588e-5 True
    5 24 248832 5.64069e-17 1.94716e-16 True
    500 2004 1010040080080032 1.19963e-44 2.43104e-43 True
    1000000000 4000000004 32000000160000000320000000320000000160000000032 2.27358e-135 1.52588e-131 True
    max over n of (1-tEnd)/(lam^2/L^2): 0.593183 at n = 0

(columns: `n, L, W, 1 - tEnd, lam²/L², regime`; the max is over `n ∈ [0, 2000] ∪ {10⁴, 10⁶, 10⁹}`.) The regime holds at
every tested `n` with ratio `≤ 0.594`, so the subtype is the full index set `{±}² × (Z_L³)²`, not empty. **Instance: PASS.**

## 4. Build, axioms, hygiene, diff scope

    $ lake build RBM3D.Graph.LWTermExpN > b2.txt 2>&1; echo "exit $?"; grep -c error b2.txt; grep LWTermExpN b2.txt; tail -1 b2.txt
    exit 0
    0
    ⚠ [3346/3346] Replayed RBM3D.Graph.LWTermExpN
    warning: RBM3D/Graph/LWTermExpN.lean:11:100: This line exceeds the 100 character limit, please shorten it!
    warning: RBM3D/Graph/LWTermExpN.lean:15:100: This line exceeds the 100 character limit, please shorten it!
    warning: RBM3D/Graph/LWTermExpN.lean:22:100: This line exceeds the 100 character limit, please shorten it!
    Build completed successfully (3346 jobs).

    $ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/LWTermExpN.lean; echo "grep exit $?"
    grep exit 1

    $ git diff --stat main...HEAD
     RBM3D/Graph/LWTermExpN.lean | 546 ++++++++++++++++++++++++++++++++++++++++++++
     1 file changed, 546 insertions(+)

Axioms of target and instance: `[propext, Classical.choice, Quot.sound]` (section 1). Only the sole writable file is touched;
no frozen signature changed. Full `lake build` is the hub's at merge. **Build/axioms: PASS.**

## 5. Paper deltas

Lean/paper differences and their coverage in `T2342-prove.md` (d):
- B class `W^{-d} B_{t,|a-b|∧K}` (`K = ⌊ℓ⌋∧L`, `c₀ = d`) used in `lem:LWterm` instead of `Ψ² = W^{-d}𝒯̃` (`7_8:20`), with the
  smaller window `ε₁ = min(ε₀, dc/2)`: candidate `T2342a`.
- `(LW_assm)` for the B class from `(LW_assm_exp)` at the single `D' = 1/𝔠` (`W^{-D'} ≤ L^{-d}` from `N^𝔠 ≤ W`): `T2342b`.
- Constant `e·2^{d-2}` between the B class and `tailW` in the regime ("immediate consequence" in the paper): `T2342c`.
- Ticket finding (`hup` comes from the size data, not from `LWWindow_max_Bctl`/`LWInit`): recorded in (a) and (d); a ticket
  wording fix, not a statement difference.
All differences are covered. **Paper deltas: PASS.**

## 6. Observations (no effect on statement, instance, build, axioms or coverage)

- O1. Lines 219 and 222: `set_option maxHeartbeats 800000 in` appears twice (the first wraps the second); harmless.
- O2. Public helpers `lwN_prec_mono`, `lwN_etaT_nonneg`, `lwN_BparamR_floor_le`, `lwN_tailT_le`, `lwN_tailW_le`,
  `lwN_B_le_tail`, `lwN_Bctl_le`, `lwN_size_rpow_neg_le`, `lwN_Wneg_le` carry the ticket's prefix `lwN_` (rule (E) satisfied).
  `lwN_Bctl_le`, `lwN_size_rpow_neg_le` and private `lwN_one_sub_lemT` duplicate merged `ST_*` lemmas
  (`Induction/Step2Iterate.lean`, `Step2Events.lean`) to keep the import at `LWPins`; the report flags this for a later move.
- O3. Regime non-emptiness at `sz0` is numerical (report (a), and section 3 above), not a Lean lemma; the ticket prescribes the
  merged instance in this form.
- O4. Prove report (d) says the registry still lists `RBM.Gauss.Sizes.LWtermExpN` as owed; consistent with the ticket
  ("Registry: none").

## Verdict

`lwtermExpN_of_LWterm`: **PASS** (statement equals the pin, no hidden hypothesis or cycle, nondegenerate compiled instance,
module builds, standard axioms only, single-file diff, paper deltas `T2342a`-`c` proposed). No dispatcher sign-off needed.
