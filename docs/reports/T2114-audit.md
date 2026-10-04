Auditor model: claude-opus-5-5

# T2114 audit (round 1) — S1-29 `Green/IBPRem`, endpoint `perTimeDomAt_ibpRem`

Date: Sun Oct  4 06:07:49 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2114-audit1`,
detached at `0d5259a` (`t/T2114`). Branch base `f590e74`; `main` is now `778bdf7` (T2113 `Green/MinorDiff`,
T2110 `Induction/OptL2a` added since; neither touches this file).

## 1. Scope of the diff

`$ git diff --name-only main...t/T2114` → `RBM3D/Green/IBPRem.lean` only (sole writable; `Test/Axioms.lean` unchanged).

## 2. Statements against the ticket's pin (RBM2D `Green/IBPRem.lean` at `c9a24cf`, renamed by R1–R3)

Independent script (`scratchpad/T2114/audit_diff.py`): extracts each declaration up to `:=` from
`git -C ../RBM2D show c9a24cf:RBM2D/Green/IBPRem.lean` and from the branch file, applies only
`d : Sizes → sz : Sizes d`, `Idx/IBPRemOffPair/llErrMat (d.L n)` → `… d (sz.L n)`, `d.size/L/W → sz.…`,
`spectralZ/spectralM → zt/mE`, and diffs token-wise.
```
$ python3 audit_diff.py rbm2d_IBPRem.lean RBM3D/Green/IBPRem.lean
IDENTICAL  IBPRemOffPair
IDENTICAL  perTimeDomAt_green_diag_sub
IDENTICAL  perTimeDomAt_green_offdiag
IDENTICAL  perTimeDomAt_prod_green_diag_sub
IDENTICAL  perTimeDomAt_condRow_prod_green_diag
DIFFERS    perTimeDomAt_greenDiagCentered_sub_minor
     insert old: - | new: (hd : 1 ≤ d)
DIFFERS    perTimeDomAt_condRow_greenDiagCentered_sub_self
     insert old: - | new: (hd : 1 ≤ d)
DIFFERS    perTimeDomAt_ibpRem_offdiag
     insert old: - | new: (hd : 1 ≤ d)
IDENTICAL  perTimeDomAt_greenDiagCentered_one
IDENTICAL  perTimeDomAt_condExpDiag_one
IDENTICAL  perTimeDomAt_ibpRem_diag
DIFFERS    perTimeDomAt_ibpRem
     insert old: - | new: (hd : 1 ≤ d)
```
Section variables: RBM2D `{d : Sizes} …` (138/193/380/450) vs `{d : ℕ} {sz : Sizes d} …` (149/204/391/461): R1 only.

The only residual difference is `hd : 1 ≤ d`, inherited from the merged lemma the proof calls:
```
$ grep -n "theorem perTimeDomAt_of_le_left_on" RBM3D/Green/CondDom.lean
401:theorem perTimeDomAt_of_le_left_on {sz : Sizes d} (hd : 1 ≤ d) {V : ℕ → Type*}
```
It is harmless at every consumer (`d ≥ 3`) and is D200 (ticket item "propagate and say where": done, 4 theorems).

Mathematics (ticket, `(GavLGEX)` `3_5:33`): `ibpRem(i,k) = E_i[G_ii(G_kk − m)] − m(G_kk − m)` (merged def,
`IBP.lean:1331`) is `≺ Ψ²` for `i ≠ k` and `≺ 1` for `i = k`. The endpoint's control is
`if q.1 = q.2 then 1 else Ψ n * Ψ n` over `Idx d L W × Idx d L W`, all pairs: matches. Quantifier order:
fixed `Kenv B` and sequences before `∀ᶠ n` / `Tendsto`, as in RBM2D. `hE : |E n| < 2`, `ht1 : t n < 1` are
weaker than the pin premises `|E n| < 2 − κ`, `0 ≤ t n`, `t n < 1` of `IBPDetThm` (`LocalLaw.lean:186`).

**`d`-exponents.** No statement exponent contains `d`; every power of `N` is a power of
`sz.size n = (W L)^d` (R3). Agreed by reading all 12 statements above.

**Floor check (ticket).** No statement takes `W^{-1} ≤ Ψ` or any `W`-floor; the floor enters as
`hΨlow : size^{-B} ≤ Ψ²`, `B ≥ 0` free. The new public `IBPRem_hΨlow_of_floor` (stem-prefixed, rule (E)):
```
theorem IBPRem_hΨlow_of_floor {d : ℕ} (sz : Sizes d) (n : ℕ) {Ψ : ℝ}
    (hfloor : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) :
    ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ Ψ * Ψ
```
proves the bridge from the T2108 floor `W^{-d/2} ≤ Ψ` (D213) to `hΨlow` at `B = 1` for every `d`, `n`.
So every statement is usable at the new floor; the old floor is not needed. PASS.

## 3. Vacuity, hidden hypotheses, cycles

- No new structure or `class`; hypotheses are explicit binders. `LocalLawDetSeq`, `AsGMcSeq`, `llErrMat`,
  `ibpRem`, `PerTimeDomAt`, `HighProbAt` are merged `def`s (read: `LocalLaw.lean:104`, `Pins.lean:73,149`,
  `IBP.lean:1331`), no hidden fields.
- Imports: `RBM3D.Green.IBP`, `RBM3D.Green.CondDom`, `RBM3D.Green.LocalLaw` (all merged: T2091, T2101,
  T2108); no `import RBM3D`, no ST-2…ST-6 file. No cycle (new leaf module).
- External hypotheses of the targets (`hll`, `hΩ`, `hEnv`, `hΨlow`, `hΨ1`, `hδ1`) are the RBM2D ones; the
  pin `IBPDetThm d` (S1-30) supplies `hll`, `hΨ0`, floor, `Ψ ≤ size^{-a}`. Limit check of `hll`/`hΩ` at
  `d = 3`, `Ψ = W^{-3/2}` is in the prove report (a)(ii): `rms|G_ii − m|·W^{3/2} ≈ 0.53` for `W = 1..4`,
  `max|G−m|` → 0. Accepted as the TEAM §8 l.14 check.

## 4. Compiled nonempty instances

Each of the 11 theorems has a private instance `IBPRem_inst_*` (lines 683–810), `IBPRemOffPair` has
`IBPRemCk_offPair_nonempty`, `IBPRem_hΨlow_of_floor` is applied in `IBPRemCk_hΨlow`. Data
(lines 556–566): `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`; ST1-COMMON item 7), `E = 0`, `t = 1/2`,
`Ψ = W^{-3/2}` (exactly the floor), `δ = 1/4`, `Kenv = B = 1`. Endpoint:
```
802: private theorem IBPRem_inst_ibpRem
803:     (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
 ...
808:   perTimeDomAt_ibpRem (δ := IBPRemCkDelta) (Kenv := 1) (B := 1) (by norm_num) tendsto_sz0_size IBPRemCk_hE
809:     IBPRemCk_ht1 IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hΨlow IBPRemCk_hΨ1
810:     IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)
```
Every deterministic hypothesis (`hd` by `norm_num`, `hsize`, `hE`, `ht1`, `hΨ0`, `hKenv`, `hB`, `hEnv`
(`9 ≤ W³ ≤ size`), `hΨlow`, `hΨ1`, `hδ1`) is a proved term, for all `n`. The only premise is
`AsGMcSeq … (3/2)`, the paper's `(asGMc)` (`3_5:30`), a pin of other gates (premise of `LocalLawDetThm`,
`GbEXPHypV3`); `hll` is it by `asGMcSeq_iff` (`Iff.rfl`), `hΩ` is derived through the merged
`entryDom_goodSet_highProb_of_asGMc` (`W^{-3/4} ≤ 1/4`). Not `False`: `‖G−m‖_max ≺ W^{-d/2}` at `η ≍ 1` is
the expected sharp size (limit check above). Index type nonempty (≥ 2·10⁶ sites at `n = 0`), window not
collapsed, `N ≠ 0`. All compile (build below). PASS.

## 5. Build, axioms, hygiene

```
$ lake build RBM3D.Green.IBPRem 2>&1 | grep -E "error|IBPRem|Build"; echo exit=$?
⚠ [3338/3338] Replayed RBM3D.Green.IBPRem
warning: RBM3D/Green/IBPRem.lean:14:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3338 jobs).
exit=0
$ lake env lean scratchpad/T2114/ax.lean | (one line per decl) | sed 's/.*depends on axioms: //' | sort | uniq -c
#   ax.lean = import RBM3D.Green.IBPRem + #print axioms of the 12 public theorems
  12 [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Green/IBPRem.lean; echo "grep exit=$?"
grep exit=1
$ lake build RBM3D | grep -E "error|Build completed"
Build completed successfully (3857 jobs).
$ lake env lean scratchpad/T2114/precheck.lean   (import RBM3D; import RBM3D.Green.IBPRem; #assert_rbm_axioms)
axiom audit: 3383 theorems, 1223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0
```
Name clash against current `main` (`778bdf7`), `git grep -wc <name> main -- 'RBM3D/*.lean' | wc -l`:
0 files for each of the 13 public names (`IBPRemOffPair`, `IBPRem_hΨlow_of_floor`, the 11 `perTimeDomAt_*`).
Frozen signatures: no merged file touched.

## 6. Paper deltas

| Lean/paper difference | Coverage |
|---|---|
| `hd : 1 ≤ d` on 4 theorems | D200 (`docs/paper-deltas.md:811`, T2101a) |
| floor `W^{-d/2} ≤ Ψ` (consumer side), bridged by `IBPRem_hΨlow_of_floor` | D213 (`docs/paper-deltas.md:863`, T2108a) |
| `hsize : Tendsto size` | RBM2D T2156a (cited in prove report (d)) |
| `IBPRemOffPair` over `Idx d L W` (merged `OffPair` over `Vtx`) | Lean-internal indexing, not a paper statement difference |
No uncovered difference; no new candidate needed.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. Header line 14 exceeds 100 characters (linter warning; `set_option linter.style.longLine false`
  comes after the module docstring). Cosmetic.
- O2. Prove report (b) cites the `d = 2` docstring phrases as "RBM2D lines 51 and 53" in the narrative and
  "53, 54, 100" in (a); the grep output shows 53/54/100. Cosmetic.

## Verdict

All 13 declarations (`IBPRemOffPair`, the 11 `perTimeDomAt_*` incl. the endpoint `perTimeDomAt_ibpRem`,
and `IBPRem_hΨlow_of_floor`): PASS.

**T2114: PASS.** No dispatcher sign-off needed.
