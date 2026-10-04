Auditor model: claude-opus-5-5

# T2136 audit (round 1) — Sun Oct  4 14:56:44 UTC 2026

Branch `t/T2136` at `7f5e5e9` (main `549a62d` is an ancestor). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2136-audit1` (detached).
Targets: `stWardTypePPin_holds : STWardTypePPin d`, `stB45Pin_holds : STB45Pin d` (`RBM3D/Induction/B45.lean`).

## 1. Files touched

```
$ git diff --name-status main...t/T2136
A	RBM3D/Induction/B45.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...t/T2136 -- RBM3D/Test/Axioms.lean   (only change: two owed lines removed)
-   `RBM.Gauss.Sizes.STWardTypePPin, -- `(eq:Ward_typeP)` (DECISIONS §25)
-   `RBM.Gauss.Sizes.STB45Pin, -- `(y27kasdfg)` (DECISIONS §25)
```
Both are sole writable files. No merged file (in particular `Step34Pins.lean`) is changed: frozen signatures untouched.

## 2. Statement (both targets)

The targets are typed by the merged pins themselves, so the statement equals the pin by construction:
```
$ lake env lean ax.lean     (scratch: #check, rfl unfolding, #print axioms)
stWardTypePPin_holds : ∀ (d : ℕ), STWardTypePPin d
stB45Pin_holds : ∀ (d : ℕ), STB45Pin d
-- example (d) : STWardTypePPin d = STIngR d STCaseI (fun sz E s t => STWardTypeP sz E s t) := rfl   -- compiles
-- example (d) : STB45Pin d = STIngR d STCaseI (fun sz E s t => STB45 sz E s t) := rfl              -- compiles
```
Pin vs paper (`3_5:1264`): paper `[𝒫∘(𝓛−𝒦)^{(n)}_{u,σ}]_{a₁} ϑ^{(n)}_{u,a} ≺ (W^{-d}B_{u,0})^n Ξ^{𝓛−𝒦}_{u,n−1}`, uniformly in `u∈[s,t]`.
Lean (`Step34Pins.lean:549`): tensors on `Fin (m+1)` (`n = m+1`), `Ξ̂_{u,m} ≺ X`, control `(sz.Bctl n u)^(m+1) * X` with
`Bctl = (W^d)⁻¹ * Bparam d L g u 0` (`Defs/Sizes.lean:214`) = `W^{-d}B_{u,0}`; `Prec` over `TimeIcc s t × alternating σ × a`
(uniform in `u` inside the probability). `STB45` (`:560`): `‖ℬ₄‖+‖ℬ₅‖ ≺ η_u⁻¹ (W^{-d}B_{u,0})^{m+1} X` with
`ℬ₄ = 𝒬Θ(𝓛−𝒦) − Θ𝒬(𝓛−𝒦)`, `ℬ₅ = 𝒫(𝓛−𝒦)·∂_uϑ` (`3_5:1692-1702`). Index ranges, exponent `m+1`, η-loss, case (i) wrapper
`STIngR d STCaseI` and `3 ≤ d` (inside `STIngR`) all as pinned. **Statement: PASS (both).**

## 3. Vacuity, hidden hypotheses, cycles

- The proofs take every `STIngR` premise but use only `STFlow`, `0 ≤ s < t ≤ lemT z`, `STStep2Concl` (its part `STGdecayW`),
  the mollifier props, `1 ≤ X` and `Ξ̂ ≺ X` (`B45_pins` signature, `B45.lean:2872`). Unused: case (i), `STKbound`,
  `STKward`, `STLK`, `STConStInd` (names `_hR _hKb _hKw _hLK _hcon` in the target proofs). Using fewer premises makes the
  proved statement stronger; not a defect. Covered by candidates T2136b, T2136c.
- Why case (i) is not needed (auditor's check against `Defs/Params.lean:32,36`): `ℓ = min(max(g/√(1−u),1),L)`,
  `B_{u,0} = (g²+|1−u|)⁻¹ + (L^d|1−u|)⁻¹`. If `ℓ = L`: `(L^d(1−u))⁻¹ ≤ B`. If `ℓ = 1` (`g² ≤ 1−u`): `(1−u)⁻¹ ≤ 2(g²+1−u)⁻¹`.
  If `ℓ = g/√(1−u) ∈ [1,L]`: `ℓ^d ≥ ℓ²`, so `(ℓ^d(1−u))⁻¹ ≤ g⁻² ≤ 2(g²+1−u)⁻¹`. So `(ℓ^d(1−u))⁻¹ ≤ 2B_{u,0}` for all `u<1`, `d ≥ 2`
  (`B45_scale`, `:459`). Sound.
- Non-triviality: `STXiLK k = 1 + max|𝓛−𝒦|^{(k)}/Bctl^k` (`Step34Pins.lean:68`), so `Ξ̂_m ≺ X` controls m-index loops only; the
  conclusion on `(m+1)`-index `𝒫(𝓛−𝒦)ϑ` needs the Ward gain — not a restatement of the hypothesis.
- No structure field carries a hypothesis: the targets have no hypotheses beyond the pin; `Sizes`, `STFlow` are merged.
- No cycle: imports are merged modules only (`Induction/{DecayLoopA,KDecay,QopAlgebra,Step34Pins,ConArgDet}`, `Loop/KLWard`);
  neither target nor any `B45_*` lemma assumes `STWardTypePPin`/`STB45Pin`/`STWardTypeP`/`STB45`.
- External hypotheses: none new (the paper's cited inputs stay inside the merged `STIngR`).
- At even pin `m` the index type `{σ // STAlternating σ}` on `Fin (m+1)` is empty (odd cycle); this is the paper's own
  restriction `(NALsig_diff)`, not a Lean artefact (T2136d). Odd `m` is nonempty (instances below). **PASS.**

## 4. Compiled nonempty instances (`B45.lean:2959-3065`, namespace `RBM.Gauss.B45Inst`)

```
example : Nonempty {σ : Fin (1 + 1) → Bool // STAlternating σ}   -- (+,-)
example : Nonempty {σ : Fin (3 + 1) → Bool // STAlternating σ}   -- (+,-,+,-)
example (Cd) (hCd : 0 < Cd) : ∃ 𝔠d, 0 < 𝔠d ∧ 𝔠d ≤ 1/100 ∧ (STKbound sz0 .. → STKward sz0 .. → STLK sz0 .. sInst →
    STStep2Concl sz0 .. sInst tInst Cd → Prec (Ξ̂_{u,m} ≤ 1) → Prec (... pin conclusion at m ...))
  -- stWardTypePPin_holds 3 at m = 1 and m = 3; stB45Pin_holds 3 at m = 1 and m = 3 (four examples)
  -- via merged inst_WardTypeP / inst_B45 (Step34Pins.lean:1013,1019) = inst_ing STCaseI ... flow_z0 sz0_hs0
  --    sz0_hst sz0_ht sz0_caseI sz0_con
  -- mollifier: QopAlgebra_mollifier 3 (sz0.L n) m (sz0.lam n), props by QopAlgebra_mollifier_props
  --    (sz0.three_le_L n) (B45_sz0_lam_pos n); X ≡ 1, 1 ≤ X by le_rfl; 1 ≤ m by le_rfl / norm_num
```
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `flow_z0`, `s ≡ 0`, `t ≡ 1/16` — nondegenerate
(no `N = 0`, nonempty windows and σ-types, `s < t`). Discharged at the data: `3 ≤ d`, `STFlow`, `0 ≤ s < t ≤ lemT z`, case (i),
`STConStInd`, `STMollifierProps`, `1 ≤ X`, `1 ≤ m`. Kept as hypotheses: `STKbound`, `STKward`, `STLK`, `STStep2Concl`, `Ξ̂ ≺ 1`
— the `STIngR` premises the ticket allows to stay ("with the `STIngR` hypotheses kept as hypotheses"), plus the pin's own
induction input. All compile (build §5). **PASS.**

## 5. Build, axioms, hygiene

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2136-audit1 && lake build RBM3D.Induction.B45
Build completed successfully (3736 jobs).          (B45.olean written 14:53 UTC by this run; no error lines)
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stWardTypePPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stB45Pin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "sorry\|admit\|native_decide\|^axiom\|set_option" RBM3D/Induction/B45.lean
13:set_option linter.style.longLine false
14:set_option linter.unusedSectionVars false
15:set_option linter.unusedVariables false
2684:set_option maxHeartbeats 400000 in
```
Merge simulation (registry pre-check): `RBM3D.lean` copied to scratch with `import RBM3D.Induction.B45` inserted after the last
`import` line; all its imports built in the audit worktree (`Build completed successfully (3882 jobs)`), then
```
$ lake env lean merge_sim.lean ; echo exit=$?
axiom audit: 4158 theorems, 1435 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 1 borrowed + 73 owed + 39 structural; ...
exit=0
```
Names: `git grep` on `main` for `stWardTypePPin_holds`, `stB45Pin_holds`, `B45_sz0_lam_pos`: 0 hits each. Every other
declaration is `private` (42) or prefixed `B45_` (rule (E)). **PASS.**

## 6. Paper deltas

Lean/paper differences and their coverage (prove report (d)):
- mollifier constant `c` quantified over `ℝ` in the merged pin (paper `c > 0`, `3_5:1214`): T2136a.
- `(ℓ^dη)⁻¹ ≲ B_{u,0}` holds for all `u < 1` (paper states it under case (i)); pins proved without case (i): T2136b.
- only `STGdecayW` of `STStep2Concl` used; `STKbound/STKward/STLK/STConStInd` unused: T2136c.
- pins empty at even `m` (alternating σ on an odd cycle): T2136d (observation, matches the paper).
All differences covered. **PASS.**

## Observations (no verdict effect)

- O1. `STKbound sz0` and `STKward sz0` are deterministic facts with merged proofs (`stKbound_holds`, `stKward_holds`,
  `Loop/KLFinal.lean:243,260`); the instances could discharge them instead of keeping them. The ticket allows keeping the
  `STIngR` premises, and the targets do not use them.
- O2. The module imports `Induction/ConArgDet` (not in the ticket's list; covered by "and what they need") and does not
  import `QopNorm`/`KLFinal`, which it does not need.

## Verdict

| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Paper deltas | Verdict |
|---|---|---|---|---|---|---|
| `stWardTypePPin_holds` | PASS | PASS | PASS | PASS | PASS | **PASS** |
| `stB45Pin_holds` | PASS | PASS | PASS | PASS | PASS | **PASS** |

T2136: **PASS**. No dispatcher sign-off needed.
