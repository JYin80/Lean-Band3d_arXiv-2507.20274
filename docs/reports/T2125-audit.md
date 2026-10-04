Auditor model: claude-opus-5-5

# T2125 audit (round 1) — KL14a `Loop/KLFinal.lean`

Audit time (`date -u`): Sun Oct  4 10:08:27 UTC 2026; 9 long-line linter warnings only (style). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2125-audit1`,
detached at `t/T2125` = `c4b40f5` (merge base `45ca385`; `main` = `aa6e061` adds only `Green/FlucThreshold` + root import;
`git merge-tree --write-tree main t/T2125` exit 0).

## 1. Files touched

```
$ git diff --name-only main...t/T2125
RBM3D/Loop/KLFinal.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2125 | grep -nE "^\+.*\b(sorry|admit|axiom|native_decide)\b" ; echo "grep exit $?"
grep exit 1
```
Registry edit: only `` `RBM.Loop.KLoopBound `` removed from `owedProps` (plus its docstring). `STKbound` stays; `STKward`
was never in the registry (`grep -n STKward RBM3D/Test/Axioms.lean` → no output). Both files are the sole writable files.

## 2. Statements against the ticket (from `#check` in the audit worktree)

```
@KLPT_holds : ∀ {d : ℕ} {κ gmax : ℝ}, 3 ≤ d → 0 < κ → 0 < gmax → KLPT d κ gmax
KLbound_holds : ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax → KLBoundAt d n κ gmax
KLwardIneq_holds : ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax → KLwardIneqAt d n κ gmax
@KLoopBound_KLK : ∀ {d L W : ℕ} [inst : NeZero L] {g E : ℝ},
  3 ≤ d → 3 ≤ L → 1 ≤ W → 0 < g → |E| < 2 → KLoopBound d L W g fun t => KLK d L g W E t
@L_rpow_le : ∀ {d : ℕ} (sz : Sizes d), 0 < d → ∀ (n : ℕ) {τ : ℝ}, 0 ≤ τ → ↑(sz.L n) ^ τ ≤ ↑(sz.size n) ^ (τ / ↑d)
@stKbound_holds : ∀ {d : ℕ} (sz : Gauss.Sizes d), 3 ≤ d → ∀ {E : ℕ → ℝ} {κ gmax : ℝ}, 0 < κ → 0 < gmax →
  sz.SizeTendsto → (∀ᶠ n in atTop, |E n| ≤ 2 - κ) → (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) → sz.STKbound E
@stKward_holds : (same hypotheses) → sz.STKward E
@stKbound_of_flow : ∀ {d} (sz : Gauss.Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ},
  sz.STFlow κ ε 𝔠 𝔡 z → sz.STKbound (STflowE z)
@stKward_of_flow : (same) → sz.STKward (STflowE z)
```

| Target | Ticket pin | Lean | Result |
|---|---|---|---|
| 1 `KLPT_holds` | `(hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) : KLPT d κ gmax` | identical; `KLPT` is the merged structure (`KLTree.lean:321`), unchanged | match |
| 2 `KLbound_holds` | `∀ d n κ gmax, 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax → KLBoundAt d n κ gmax` | identical | match |
| 2 `KLwardIneq_holds` | same for `KLwardIneqAt`, `2 ≤ n` | identical | match |
| 2 `KLoopBound` for `K = KLK` | bridge, unspecified form | `KLoopBound_KLK`, fixed `(d,L,W,g,E)`, `|E| < 2` (κ = 2-|E|, gmax = g) | match (`KLoopBound` is itself a fixed-`L` Prop, `KBound.lean:74`) |
| 3 `stKbound_holds` | `STKbound sz E` under consumers' hypotheses; conditional form allowed if pin false | conditional: `SizeTendsto`, eventual bulk, eventual `0 < lam ≤ gmax`; flow form `stKbound_of_flow` | match (conditional form authorised by the ticket; falsity of the bare pin compiled, §3) |
| 4 `stKward_holds` | likewise | likewise | match |

Field-by-field (target 1): `KLDecay`←`prop5Decay_holds` at `m = I`, charges `(true,false)`, `PropSpin I true * PropSpin I false = 1`;
`KLShort`←`prop5Short_holds d gmax (min κ 1 / 2)` at `m = mE E` with `min κ 1 / 2 ≤ Im mE E` on `|E| ≤ 2 - κ`
(`κ'` stated explicitly, private lemma `KLFinal_mE_im_ge`); `KLDiffOne/Two` (range `0 < c < 1`, loss `L^τ`) ← `prop6Diff1_holds`/
`prop7Diff2_holds` at `κ = 1`, `m = I`, absorbed by `1 ≤ L^τ`; `KLZero` ← `prop8ZeroMode_holds` likewise. Quantifier order of the
`KL*` pins (constants before `L, g, t, a`) is the merged one; the proofs are Lean-checked. The D174 issue does not arise: the
merged `KLDiffOne/Two` and `Prop6Diff1/Prop7Diff2` both carry `c < 1`.

DECISIONS §29: (1) `STKbound`/`STKward` quantify `τ n ∈ [0,1)` and `KLPar.t ∈ [0,1)`; (3) `L_rpow_le` uses only `W ≥ 1`
(`Nat.le_mul_of_pos_left`, no `L^d ≤ W^K`); (4) `Prec` is eventual (`StochDomAt.of_eventually_empty`). Constants: `C` of
`KLBoundAt`/`KLwardIneqAt` is chosen before `p : KLPar κ gmax`, i.e. depends on `(d,n,κ,gmax,τ)` only.

## 3. Vacuity, hidden hypotheses, cycles

- No new structure carries a hypothesis; `KLPar` (merged) holds only the parameter ranges.
- Dependencies are merged results: `prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`,
  `prop8ZeroMode_holds`, `KLboundPin_holds` (T2115), `KLwardIneqPin_holds` (T2122 `1cd777f`). No cycle (KLFinal is imported by nothing).
- Conditional form justified by a compiled negative: `KLFinal_not_stKbound : ¬ STKbound KLFinal_szConst (fun _ => 0)`
  (`L ≡ 3, W ≡ 1, lam ≡ 1/2, N ≡ 27`, `k = 2`, `τ ≡ 0`), axioms standard (§5). So `SizeTendsto` cannot be dropped.
- Consumers can supply the hypotheses. `STFlow` consumers (`STStep1`, `Defs.lean:349–357`; `Step34Pins`) via the flow forms.
  The `S1Std` consumers (`s1_Kbound_seq`, `s1_h55`, `Step1Setup.lean:671,693`) were not checked by the prover; auditor check:

```
$ cat audit2.lean   (excerpt; scratchpad T2125/)
example {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ 𝔠 𝔡 τ 𝔠d : ℝ} {E s t : ℕ → ℝ}
    (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : STKbound sz E ∧ STKward sz E := by
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [h.hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  exact ⟨stKbound_holds sz hd h.hκ (inv_pos.2 h.h𝔡) h.hN (Eventually.of_forall h.hE) hlam,
    stKward_holds sz hd h.hκ (inv_pos.2 h.h𝔡) h.hN (Eventually.of_forall h.hE) hlam⟩
$ lake env lean audit2.lean; echo "exit $?"
exit 0          (only the #check lines printed, §2)
```

## 4. Compiled nonempty instances (`KLFinal.lean` §5, compiled by the module build)

| Endpoint | Instance | Data | Hypotheses |
|---|---|---|---|
| `KLPT_holds` | `example : KLPT 3 (1/10) 1` (l.399) + the five fields applied (l.405–449) | `L=5, g=1/2, t=9/10, E=0`, `a=(1,1,1)`, `(2,2,2)`, `r=(1,1,1)`, `c=1/2`, `τ=1` | all discharged (`decide` for `zdistD`) |
| `KLbound_holds` | l.453 | `n=4`, `KLinstPar` (`L=5,W=2,g=1/2,E=0,t=9/10,κ=gmax=1`), loop `KLInduct_instσ/insta` | none left (`τ>0` is the pin's own ∀) |
| `KLwardIneq_holds` | l.462 | same, `n=4` | none left |
| `KLoopBound_KLK` | l.475, l.479 | `d=3,L=5,W=2,g=1/2,E=0`; applied at `n=4,τ=1,t=9/10` | none left |
| `L_rpow_le` | l.498 | `sz0`, `τ=3/2` | none left |
| `stKbound_holds` / `stKward_holds` | l.505, l.516 | merged `sz0`, `E = STflowE z0`, `κ=1/10`, `gmax=1` | `sz0_tendsto`, bulk via `abs_lemE_le`+`z0_locDomain`, `lam_n=(2(n+1))^{-6}∈(0,1]` |
| `*_of_flow` | l.528, l.534 | `flow_z0`, `k=3`, `τ ≡ 1/2` | none left |

No `N = 0`, empty index, collapsed window or `False` premise; `sz0` has `L_n = 4(n+1)`, `N_n → ∞`.
## 5. Build and axioms

```
$ lake build RBM3D.Loop.KLFinal ; echo "exit $?"
⚠ [3713/3713] Built RBM3D.Loop.KLFinal (4.0s)
Build completed successfully (3713 jobs).
exit 0
$ grep -n "error" build.log        → (none); warnings in KLFinal.lean: 9 × "line exceeds the 100 character limit"
$ lake build RBM3D ; echo "exit $?"        (root, with the branch's registry edit)
Build completed successfully (3872 jobs).
exit 0
$ cat audit.lean: import RBM3D; import RBM3D.Loop.KLFinal; #print axioms <10 names>; #assert_rbm_axioms
$ lake env lean audit.lean
'RBM.Loop.KLPT_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLbound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLwardIneq_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLoopBound_KLK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.L_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKbound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKward_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKbound_of_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKward_of_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.KLFinal_not_stKbound' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 3852 theorems, 1346 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 77 (borrowed 1, owed 61, structural 15).
registry: 5 borrowed + 100 owed + 39 structural; 67 registered premise(s) carry nothing yet: [...]
exit 0
```
The registry scan with KLFinal imported finds no unregistered premise (removing `KLoopBound` is safe: `KLoopBound_KLK`
concludes it, and no theorem takes it as a binder). The same compile shows no name clash between the 12 new public names
and the merged library.

## 6. Paper deltas

Prove report (d) proposes `T2125a` (sequence-level `ML:Kbound`/`lem_wardineq_K` need `N → ∞`, bulk `|E_n| ≤ 2-κ`, `0 < lam_n ≤ gmax`;
the pinned `STKbound sz E` without them is false) and `T2125b` (bridge constants `κ' = min κ 1 / 2`, `m = I`, `κ'' = 1`).
These cover every Lean/paper difference introduced here. `KLoopBound_KLK`'s restriction to the family `KLK` is the ticket's request
and is said in its docstring and the report.

## 7. Observations (no RETURN)

- O1. Report (a)(i) says `STFlow` "is not checked for the other consumers (`s1_Kbound_seq` takes `S1Std`)"; the auditor check in §3
  shows `S1Std` supplies the hypotheses (via `hWO`, `hN`, `hE`, `hκ`, `h𝔡`). The consumers stay unchanged (outside this ticket).
- O2. The `STKbound` line stays in `owedProps`; the registry now lists it among premises that carry nothing (it is concluded by
  `stKbound_holds`). Consumers still take it as a binder; re-plumbing is KL14b / consumer work, as the report says.

## Verdict

| Target | Verdict |
|---|---|
| 1 `KLPT_holds` | PASS |
| 2 `KLbound_holds`, `KLwardIneq_holds`, `KLoopBound_KLK` | PASS |
| 3 `stKbound_holds` (+ `stKbound_of_flow`, `L_rpow_le`) | PASS (conditional form, authorised by the ticket, negative compiled) |
| 4 `stKward_holds` (+ `stKward_of_flow`) | PASS (conditional form) |
| Registry edit | PASS (`KLoopBound` only; `STKbound` kept with reason) |

**T2125: PASS.** No dispatcher sign-off needed.
