Auditor model: claude-opus-5-5

# T2116 audit (round 1): ST2-15 `Induction/OptL2b`, target `stOptL2_of_pins`

Written Sun Oct  4 06:44:37 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2116-audit1`, detached at `02d54f2` (= `t/T2116`).

**Verdict: PASS** (one target).

## 1. Statement against the pin

```
$ diff <(grep -o 'stOptL2_of_pins (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d' docs/tickets/T2116.md | head -1) \
       <(sed -n 195p RBM3D/Induction/OptL2b.lean | sed 's/^theorem //; s/{d : ℕ} //; s/ := by$//'); echo diff-exit $?
diff-exit 0
$ lake env lean ax.lean   # #check
@RBM.Gauss.Sizes.stOptL2_of_pins : ∀ {d : ℕ},
  3 ≤ d → RBM.Gauss.Sizes.STLWB d → RBM.Gauss.Sizes.STGridMart d → RBM.Gauss.Sizes.STOptL2 d
```
The conclusion is the merged pin `STOptL2` (`Step2Defs.lean:667`), which the branch does not touch (see §4 diff). Its
quantifier order: `∀ κ ε 𝔡 > 0, ∃ 𝔠₀ > 0, ∀ 𝔠d ∈ (0,𝔠₀], ∀ 𝔠 sz z, STFlow → ∀ s t, 0 ≤ s ≤ t ≤ lemT z →
STLK → STConStInd → STStep1Loop → STStep1Weak → PrecPT (per time, U = TimeIcc s t × σ × a)` — the ticket's step 3
and DECISIONS §29 (1),(2),(4). The proof supplies `𝔠₀ = 1/(8 C₀ + 10)` with `C₀` from `stOptL2a_gronwall`
(chosen after `κ ε 𝔡`, before `𝔠`, the sequences, `𝔠d`): free of `W, L, λ`.
Premise `3 ≤ d` is the ticket's own pin (needed by `stOptL2a_gronwall`, `OptL2a.lean:1260`).

## 2. Vacuity, hidden hypotheses, cycles

- No structure-field hypotheses: the only inputs are `STLWB d`, `STGridMart d` (owed pins, `Step2Defs:406`, `:537`,
  registered in `Test/Axioms.lean` `owedProps`) and the premises of the pin itself.
- Dependency `stOptL2a_gronwall` is merged on `main` (`6f8ca5b T2110: merge ST2-14 Induction/OptL2a`). Signature
  (`OptL2a.lean:1260–1275`) takes exactly `hd, STLWB, STGridMart, κ ε 𝔡`, and per pair `(s,T)` the premises
  `STLK s`, `𝔠d ≤ 1/2`, the first conjunct of `(con_st_ind)` on `[s,T]`, `STStep1Loop/Weak` on `[s,T]`.
  The new file discharges these from the `[s,t]` premises via `OptL2b_{loop,weak,con}_restrict`, and `𝔠d ≤ 1/2` from
  `𝔠d ≤ 1/(8C₀+10)`. No cycle: `STOptL2` is not an input of any dependency (imports only `RBM3D.Induction.OptL2a`).
- Restriction lemmas: `OptL2b_con_restrict` restricts only the first conjunct (`B_T^{𝔠d} ≤ (1−T)/(1−s)`), as the ticket
  requires (second conjunct fails at `T = s`, T2110d).
- The ticket's step 2 is carried out in the proof: `ST_gronwall`, `ST_prod_le_rpow` (product ≤ `ρ^{C₀}`),
  `OptL2b_arith` (`(eq:L-K2max)`), `ST_model_le_path`, `ST_PT_of_sections`. No `N^{-C}`-net in `u`.
- No new external hypothesis.

## 3. Compiled nonempty instances (`OptL2b.lean:334–400`, namespace `RBM.Gauss.OptL2bInst`)

```
$ grep -n "^theorem\|^example" RBM3D/Induction/OptL2b.lean
42:theorem OptL2b_rho_pow_mul ...      57:theorem OptL2b_arith ...
101:theorem OptL2b_loop_restrict ...   111:theorem OptL2b_weak_restrict ...
120:theorem OptL2b_con_restrict ...    146:theorem OptL2b_J_measurable ...
163:theorem OptL2b_badSet_eq ...       195:theorem stOptL2_of_pins ...
334:example (hLWB : STLWB 3) (hGM : STGridMart 3) :            -- via merged inst_optL2
349:example (hLWB : STLWB 3) (hGM : STGridMart 3) :            -- direct application
364:example (hS1L : STStep1Loop sz0 ...) (hS1W : STStep1Weak sz0 ...) :  -- restrictions to [0,1/32]
377:example : ... ≤ 2 * 2 * (1/10)                              -- OptL2b_arith, ρ = 1 (T = s)
387:example : ... ≤ 2 * 2 * (1/10)                              -- OptL2b_arith, ρ = 32/31 > 1
```
- Endpoint `stOptL2_of_pins` at `d = 3`, line 349: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, merged `sz0`
  (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`), flow `z0` (`flow_z0`), window `s ≡ 0`, `t ≡ 1/16` (`s < t`, not collapsed).
  Discharged at the data: `3 ≤ 3`, `0 < 1/10` ×3, `STFlow` (`flow_z0`), `0 ≤ s`, `s ≤ t` (`norm_num`),
  `t ≤ lemT (z0 n)` (`sixteenth_le_lemT`), `(con_st_ind)` (`conStInd_inst h1`) for every `0 < 𝔠d ≤ 𝔠₀`.
  Left as hypotheses: `STLWB 3`, `STGridMart 3` (owed pins of other gates) and the stochastic Step-1/induction
  premises `STLK`, `STStep1Loop`, `STStep1Weak` (premises of the pin, as in the merged `inst_optL2`,
  `Step2Defs.lean:1134`, which the ticket names as an acceptable reading). No `N = 0`, empty index, `False` premise
  or huge witness. The `OptL2b_arith` instances are concrete numeric with all hypotheses discharged.
- The examples compile (module build below exits 0 and contains them).

## 4. Build, axioms, hygiene, diff scope

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2116-audit1 && lake build RBM3D.Induction.OptL2b 2>&1 | grep -E "OptL2b|error|Build completed"
Build completed successfully (3767 jobs).
```
(no error lines; no warning line mentions `OptL2b`.)
```
$ lake env lean ax.lean     # import RBM3D.Induction.OptL2b; #print axioms ...
'RBM.Gauss.Sizes.stOptL2_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_con_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_loop_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_weak_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_badSet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.OptL2b_J_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom" RBM3D/Induction/OptL2b.lean; echo grep-exit $?
grep-exit 1
$ git diff --name-only main...t/T2116
RBM3D/Induction/OptL2b.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2116 -- RBM3D/Test/Axioms.lean   # one changed line, comment of the existing owedProps entry
-   `RBM.Gauss.Sizes.STOptL2, -- `(eq:opt_L2)` (`3_5:470`): ST2-14, ST2-15 (T2066, DECISIONS §28)
+   `RBM.Gauss.Sizes.STOptL2, -- ... ; `stOptL2_of_pins` (T2116) proves it from `STLWB` and `STGridMart`, so it stays owed through those two
```
- Only the two sole writable files; no frozen signature touched (`Step2Defs.lean` unchanged); the new file imports
  only `RBM3D.Induction.OptL2a` (not `RBM3D`).
- New public names: all helpers prefixed with the file stem `OptL2b_` (rule (E)); clash check on `main`:
```
$ for n in OptL2b_rho_pow_mul OptL2b_arith OptL2b_loop_restrict OptL2b_weak_restrict OptL2b_con_restrict \
    OptL2b_J_measurable OptL2b_badSet_eq stOptL2_of_pins; do git grep -c "$n" main -- RBM3D | wc -l; done
0 0 0 0 0 0 0 0   (0 files on main for each)
```
- The full `lake build` (with `#assert_rbm_axioms`) is run by the hub at merge.

## 5. Paper deltas

Prove report §(d) (`T2116-prove.md:243–245`) proposes:
- `T2116a`: `3_5:508–509` "choose `𝔠_d` small depending on `C₀`" → explicit `𝔠₀ = 1/(8C₀+10)`, `∃ 𝔠₀` placed after
  `κ ε 𝔡`, before `𝔠`, sequences, `𝔠d`.
- `T2116b`: `(eq:L-K2max)` — Lean bounds `B_s ≤ B_T` (`STBctl_mono`) and each term `≤ B_T` by the exponent count,
  factor `2` absorbed in `N^{τ'/2}`.
The remaining Lean/paper differences (per-time `PrecPT`; restriction of only the first conjunct of `(con_st_ind)`;
`3 ≤ d` premise) are the pin's own form, fixed upstream (T2066/T2110, DECISIONS §29, T2110d/f), not introduced here.
Coverage: complete.

## 6. Observations (no effect on verdict)

- O1. `STOptL2` remains conditional on the owed pins `STLWB`, `STGridMart` (by the ticket's design); the registry
  comment records this correctly.

## Verdict

| Target | Verdict |
|---|---|
| `RBM.Gauss.Sizes.stOptL2_of_pins` | **PASS** |

No dispatcher sign-off needed.
