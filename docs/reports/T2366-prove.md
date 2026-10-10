Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 23:16:23 UTC 2026

Targets (mathematics only): over `IsKLoopS d L W S m M T K` (clauses: `K' = W^d Σ K S K` for WF `I`, `2 ≤ |I|`; `K 0 I = M I`; `K t ⟨[s],[a]⟩ = m s`), with `‖S a b‖ ≤ 1` as the only fact on `S` for `UniqS`, `RetireS`.
`RotS` adds `S` symmetric and `M ⟨s::σ,b::a⟩ = M ⟨σ++[s],a++[b]⟩`; `TranslS` adds `S (a+c) (b+c) = S a b` and `M (shift_c I) = M I`.

### (i) Exponent table (no exponents occur; the constants and thresholds the targets depend on)

| Quantity | Value / form | Constraint | Slack |
|---|---|---|---|
| `s₀ = sup‖S a b‖` (pin hypothesis) | `SB` (d=3, L=5, g=1/2): 0.4; `S = 1`: 1 | `≤ 1` (enters only via `‖X-X'‖‖Y‖` splitting, `norm_mul_mul_sub_le`) | `SB`: 0.6; `S = 1`: 0 (saturated, still allowed) |
| `3 ≤ L` | needed only to discharge `‖SB a b‖ ≤ 1` (`norm_SB_apply_le`) | disappears from every generic statement; stays in band wrappers | `S = 1`: no condition on `L` beyond `NeZero L` |
| `T₀` | `T₀ = t < 1`, `Icc 0 T₀ ⊆ Ico 0 1` | `T₀ < 1` | instance `T₀ = 9/10`: 0.1 |
| `R` (2-loop bound) | `RetireS`: `∃ R ≥ 0`, from continuity of the finitely many `s ↦ K s I`, `|I| = 2`, on compact `[0,T₀]` | `0 ≤ R` only | instance `R = W^{-d}(1-T₀)^{-1} = 1.25`; sampled max `‖kTwo‖ = 0.2322` |
| Grönwall constant, uniqueness (`eq_on_levelS`, n ≥ 2) | `C_n = W^d · (n(n-1)/2) · L^{2d} · 2R` (`Unique.lean:157`: pairs `(k,l) ∈ Icc 1 n × Ioc k n`, count `n(n-1)/2`) | finite, `≥ 0`; no relation to `S` | n=2,3,4: 312500, 937500, 1875000 |
| Grönwall constant, rotation (`KLUnique.lean:435`) | `C'_n = W^d ((n-1) + (n-1)(n-2)/2) L^{2d} 2R = C_n` | finite, `≥ 0` | equal to `C_n` (script below) |
| Induction base | `n = 2`: `hlow` vacuous, Riccati Lipschitz from the same estimate | `2 ≤ n` | none needed |
| `1 ≤ W`, `|E| < 2`, `g` | do not occur in the five targets | — | — |

Use-by-use map (G segments; every use is replaced by a pin hypothesis; none needs a fact outside the pins):

| Use (file:line) | Replaced by |
|---|---|
| `Unique.lean:142,144,153,178,179,214-216,219,220` `treeEqRhs d L W g`, `SB d L g a b` | `treeEqRhsS d L W S`, `S a b` (`IsKLoop` is `IsKLoopS` at `SB`, `MLoopM d L W m (KLallEq d L)`, by `Iff.rfl`, `KLTree.lean:846-848`; `MLoop = MLoopM …` is `rfl`, `KLTree.lean:842`) |
| `Unique.lean:196` `norm_SB_apply_le hL a b` (only use of `SB` facts in `eq_on_level`) | pin hypothesis `∀ a b, ‖S a b‖ ≤ 1` |
| `Unique.lean:260-266` `hK.1`, `hK.2.1` | clauses 1, 2 of `IsKLoopS` (`K 0 J = M J`, no `M` fact used) |
| `Unique.lean:294-307` `KLretire_twoLoopBounded` | `RetireS`: only clause 1 of `IsKLoopS`; no `SB`, `MLoop`, `m`, `hL` is used |
| `Unique.lean:350` `eq_on_level` inside `kTwoFormula_of_isKLoop`, `328` `norm_SB` | unchanged (wrapper `eq_on_level` keeps its statement) |
| `KLUnique.lean:156` `SB_apply_add_right` (translation) | translation hypothesis `S (a+c) (b+c) = S a b` |
| `KLUnique.lean:159-164` `KLUnique_MLoop_shift` | hypothesis `M (shift_c I) = M I`; band supplies it by the existing lemma (`KLUnique_shift` unfolds to `⟨I.σ, I.a.map (·+c)⟩`) |
| `KLUnique.lean:178` clause 3 `hK.2.2 r hr s (a+c)` | no `S`, `M`: `m s` is constant in the label |
| `KLUnique.lean:357` `SB_transpose` | symmetry hypothesis `S a b = S b a` |
| `KLUnique.lean:405-411,594` `KLUnique_MLoop_rot` | hypothesis `M ⟨s::σ,b::a⟩ = M ⟨σ++[s],a++[b]⟩`; used at `h0` for WF `J`, `|J| = n ≥ 2`: write `J = ⟨s::ss, c::cs⟩`, `ss.length = cs.length` (from WF), `rot J = ⟨ss++[s], cs++[c]⟩` (`KLUnique_rot_mk_cons`); band supplies it from `KLUnique_MLoop_rot` |
| `KLUnique.lean:495,517` `norm_SB_apply_le` | norm hypothesis |
| `KLUnique.lean:615` `KLretire_twoLoopBounded` | `retireS_holds`, at `T₀ = t` |
| `KLUnique.lean:90-92,202` (`KLK_unique`, `KLK_translate`) | unchanged: wrappers `isKLoop_unique`, `KLretire_twoLoopBounded` keep statements |
| `TranslS` proof (new) | `K_c := K ∘ shift_c` is `IsKLoopS S m M (Ico 0 1)` (clause 1: reindex `Σ_{a,b}` by `+c` with translation hypothesis and `cutGlue_shift`, S-free; clause 2: `M` invariance; clause 3: `m s`); `retireS_holds` bounds `K`, `K_c` on `[0,t]`; `uniqS_holds` gives `K_c = K` for `|I| ≥ 2`; `|I| = 1`: both equal `m s` (clause 3); `|I| = 0`, WF: `I = ⟨[],[]⟩`, `rfl` |
| `RotS` proof (new) | the band proof with the above replacements; `|I| = 1` (`σ = []`, `a = []`) is `rfl`; `K` bound from `retireS_holds`, uniqueness not used |

Verdicts on the ticket's questions:
- (ii) `RetireS` needs no fact about `S`, `m`, `M`: the proof is `hK.1` (a derivative, hence continuity) at each of the finitely many length-2 loops (`LoopVec d L 2` finite) on `Icc 0 T₀ ⊆ Ico 0 1`, plus `isCompact_Icc.exists_bound_of_continuousOn`. Confirmed.
- (iii) hypotheses of `RotS`, `TranslS` on `S`: at `S = 1`: `1 a b = 1 b a`, `1 (a+c) (b+c) = 1 a b` (`a+c = b+c ↔ a = b`), `‖1 a b‖ ≤ 1`; at `S = SB d L g`: `SB_transpose`, `SB_apply_add_right`, `norm_SB_apply_le` (`3 ≤ L`). Both are scripted below. `S = 1` needs nothing about `L`.
- K03 hand-off (`BAMLoop`, `BA/FlowPins.lean:274-276`: `W^{-d(n-1)} ∏_i M σ_i a_i a_{i+1}` over `zip σ (zip a (rotate a 1))`): rotation hypothesis holds for every `M` (factor multiset is rotated, scripted); translation hypothesis holds iff `M_s (x+c)(y+c) = M_s x y` (scripted: 0 violations circulant, 297 non-circulant). This is a K03 hypothesis on `M`, not on `S`.
- The generic statements need no fact beyond the pins: no amend is required.
- Import structure (a ticket-level fact): `UniqS` and `RetireS` use `IsKLoopS`, which is defined in `Loop/KLTree.lean:828`; `Unique.lean` currently imports only `Loop.Primitive`. `Unique.lean` therefore needs `import RBM3D.Loop.KLTree` (not `RBM3D`, not `BA/`); no cycle (script: `KLTree` does not depend on `Unique`; `KLUnique` already depends on both). Importers of `Unique` (`TreeThree`, `Test/InterfaceShape`, `Induction/NQEndFlowLift`) then see `KLTree`; the full `lake build` decides any name clash.

### (ii) Concrete nondegenerate instance: `d = 3`, `L = 5` (N = 125), `W = 2`, `g = 1/2`, `E = 0`, `m(+) = i`, `m(−) = −i`, `t = T₀ = 9/10`, `R = 1.25`

Family hypotheses: `K = 𝒦 = KLK 3 5 (1/2) 2 0` satisfies `IsKLoop 3 5 2 (1/2) (mSigma 0) (Ico 0 1) K` (merged `KLTreeDerivInst_isKLoop`, `RBM3D/Loop/KLTreeDeriv.lean:1080`), which is `IsKLoopS (SB) (MLoopM …)` by `Iff.rfl`; a second, different-as-function family is `K ∘ shift_{e₁}` (`KLUniqueInst_unique_shifted`). External hypotheses: none (no external input in the five targets); existence of an `IsKLoopS` family at `S = 1` is the K03 pin `BAKexists`, outside this ticket.

```
$ lake env lean docs/tickets/checks/T2366-check.lean ; echo exit=$?     (cwd main worktree)
exit=0
$ python3 -I .../scratchpad/T2366/deps.py RBM3D.Loop.KLTree RBM3D.Loop.Unique RBM3D.Loop.KLUnique
RBM3D.Loop.KLTree depends on Unique: False  on KLTree: False  on KLUnique: False
RBM3D.Loop.Unique depends on Unique: False  on KLTree: False  on KLUnique: False
RBM3D.Loop.KLUnique depends on Unique: True  on KLTree: True  on KLUnique: False
$ python3 -I .../scratchpad/T2366/inst.py
N= 125 a0= 0.4 b0= 0.1 a0+2d*b0= 1.0
S=SB symm: True transl-inv: True max|entry|: 0.4 <=1: True row sums: {1.0}
S=1 symm: True transl-inv: True max|entry|: 1.0 <=1: True row sums: {1.0}
MLoop rot/shift-invariance on 1200 random loops (nonzero values: 617 ) violations: 0
BAMLoop-form data (product over (s_i,a_i,a_{i+1}), as BA/FlowPins.lean:274): rotation violations: 0 ; shift violations (circulant M_s): 0 ; shift violations (non-circulant M_s): 297
max|kTwo| over sampled t<=0.9, charges, labels = 0.23219078500910123  R=W^-d/(1-T0)=1.25  ok: True
n= 2 C_unique= 312500.00000000006 C_rot= 312500.00000000006 equal: True
n= 3 C_unique= 937500.0000000001 C_rot= 937500.0000000001 equal: True
n= 4 C_unique= 1875000.0000000002 C_rot= 1875000.0000000002 equal: True
```
(`inst.py` computes, in pure Python: the circulant `SB` from `sbKernel` (`Defs/Block.lean`: `a₀ = (1+2dg²)⁻¹` at 0, `g²a₀` at `zdistD = 1`), the `S = 1` kernel, the `MLoop` formula (`TreeRep.lean:142`, `mE 0 = i`), `kTwo = W^{-d} μ Θ_{tμ}`, `Θ = (1 − ξ SB)⁻¹` by DFT on `Z_5^3`, `μ = m σ₁ m σ₂`.)

Nondegeneracy: `MLoop` is nonzero on 617 of the 1200 test loops (those with all labels equal); `‖kTwo‖` is nonzero; the shifted family differs from `K` as a function; `n = 3, 4` are reached by the band instances `KLUniqueInst_*` of `KLUnique.lean:644-710` (compiled on main).

### (iv) Plan of edits and line budget (base 374 + 766 = 1140; stop line 1560 at a section boundary)

| Section | Edit | Est. net lines | Running total |
|---|---|---|---|
| 1 `Unique.lean` | `import RBM3D.Loop.KLTree`; pins `UniqS`, `RetireS` (≈ 26); `eq_on_levelS` (generalise in place, ≈ +6); wrapper `eq_on_level` (≈ +22); `uniqS_holds` (strong induction, ≈ +14), `isKLoop_unique` becomes a 3-line wrapper (≈ −8); `retireS_holds` plus `KLretire_twoLoopBounded` wrapper (≈ +8) | ≈ +68 | ≈ 1208 |
| 2 `KLUnique.lean`, translation | pin `TranslS` (≈ 11); `treeEqRhsS` shift, `isKLoopS` shift (≈ +10); `translS_holds` (≈ +30); `KLK_translate` unchanged | ≈ +51 | ≈ 1259 |
| 3 `KLUnique.lean`, rotation | pin `RotS` (≈ 11); add `S`, hypotheses to `split`, `rot`, `rot_eq_on_level`, `isKLoop_rot` (≈ +14); `rotS_holds` (≈ +28); `KLK_rotate` wrapper (≈ +8) | ≈ +61 | ≈ 1320 |
| 4 instances | `kernel_one_rot_transl`, `kernel_SB_rot_transl` (≈ +30) | ≈ +30 | ≈ 1350 |

Total ≈ +210 (ticket's range 213–311 gives ≤ 1451 < 1560). Private helpers `KLUnique_treeEqRhs_shift`, `KLUnique_isKLoop_shift`, `KLUnique_treeEqRhs_split/rot`, `KLUnique_rot_eq_on_level`, `KLUnique_isKLoop_rot` change signature (private; every public declaration of Part 2 of the check file keeps its statement, check file exit 0 on main).

### Verdicts
- Pins (`UniqS`, `RetireS`, `RotS`, `TranslS`): PASS (all hypotheses hold at once at the instance; the check file compiles with exit 0).
- `uniqS_holds`, `retireS_holds`: PASS (only `‖S a b‖ ≤ 1`; two-loop bound needs no fact about `S`).
- `rotS_holds`, `translS_holds`: PASS (every use of `SB` or `MLoop` is replaced by a pin hypothesis, table above).
- Re-derivation (G1): PASS in principle (each band statement is the pin at `S = SB d L g`, `M = MLoop d L W m`; `IsKLoop` is `IsKLoopS` by `Iff.rfl`); the one structural note is the added `import RBM3D.Loop.KLTree` in `Unique.lean`.

## (a′) Preflight corrections — Sat Oct 10 00:43:39 UTC 2026

One correction to the last bullet of the verdict block of (a) (import structure): `Loop/Unique.lean` imports `RBM3D.Loop.KLTreeDeriv` (not `RBM3D.Loop.KLTree`), because the instances of `uniqS_holds` and `retireS_holds` must sit in the same file (CLAUDE.md §4 step 2) and the family they need, `KLTreeDerivInst_isKLoop`, is in `KLTreeDeriv`. Script (deps.py of (a), root pointed at the worktree, run at Sat Oct 10 00:44:07 UTC 2026):
```
$ python3 -I .../scratchpad/T2366/deps.py RBM3D.Loop.KLTreeDeriv RBM3D.Loop.KLTree
RBM3D.Loop.KLTreeDeriv depends on Unique: False  on KLTree: True  on KLUnique: False
RBM3D.Loop.KLTree depends on Unique: False  on KLTree: False  on KLUnique: False
```
`Unique.lean` lines 6-10 import `Primitive`, `KLTreeDeriv`, `Mathlib.Analysis.ODE.Gronwall`, `Mathlib.Analysis.Calculus.Deriv.Prod`, `Mathlib.Data.Fintype.Vector`. No verdict of (a) changes: no cycle, and the full `lake build` below succeeded.

## (b) Script output (cwd /Users/junyin/Lean_proof/RBM3D-wt/T2366, branch t/T2366)
```
# --- scope, stop rule (2 files, base 374+766=1140, stop line 1560), public names
$ git status --short ; git diff --stat main...t/T2366
 RBM3D/Loop/KLUnique.lean | 339 +++++++++++++++++++++++++++++++++++------------
 RBM3D/Loop/Unique.lean   | 165 +++++++++++++++++------
 2 files changed, 379 insertions(+), 125 deletions(-)
$ for c in b1f0988 e39bb7e 9e00b10 005deab f4e179e; do wc -l of the two files at the commit; done
b1f0988  Unique=     374 KLUnique=     766 total=1140
e39bb7e  Unique=     459 KLUnique=     766 total=1225
9e00b10  Unique=     459 KLUnique=     817 total=1276
005deab  Unique=     459 KLUnique=     848 total=1307
f4e179e  Unique=     459 KLUnique=     935 total=1394
$ python3 -I .../pubdecls.py main t/T2366     (public declarations of the two files)
RBM3D/Loop/Unique.lean main public: 17 branch public: 24
  removed/renamed on branch: []
  added on branch: ['RBM.Loop.RetireS', 'RBM.Loop.UniqS', 'RBM.Loop.UniqueInst_retireS', 'RBM.Loop.UniqueInst_uniqS', 'RBM.Loop.eq_on_levelS', 'RBM.Loop.retireS_holds', 'RBM.Loop.uniqS_holds']
RBM3D/Loop/KLUnique.lean main public: 16 branch public: 25
  removed/renamed on branch: []
  added on branch: ['RBM.Loop.KLUniqueInst_rotS', 'RBM.Loop.KLUniqueInst_translS', 'RBM.Loop.KLUniqueInst_uniqS_shifted', 'RBM.Loop.RotS', 'RBM.Loop.TranslS', 'RBM.Loop.kernel_SB_rot_transl', 'RBM.Loop.kernel_one_rot_transl', 'RBM.Loop.rotS_holds', 'RBM.Loop.translS_holds']
# --- builds (full `lake build` at commit f4e179e = HEAD; output saved to fullbuild.out)
$ cat fullbuild.start fullbuild.end ; tail -2 fullbuild.out ; grep -c "^error" fullbuild.out
Fri Oct  9 23:25:59 UTC 2026
Sat Oct 10 00:39:10 UTC 2026
Build completed successfully (4173 jobs).
exit=0
0
$ lake build --no-build 2>&1 | tail -1     (at HEAD, after the full build)
All targets up-to-date (4173 jobs).
$ lake build RBM3D.Loop.Unique RBM3D.Loop.KLUnique 2>&1 | tail -1
Build completed successfully (3620 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Loop/Unique.lean RBM3D/Loop/KLUnique.lean | wc -l
       0
# --- check file on the branch; pin equalities (check-file copy + 4 lines  example : @RBM.Loop.X = @RBM.Loop.T2366Check.X := rfl)
$ lake env lean docs/tickets/checks/T2366-check.lean >/dev/null; echo exit=$?
exit=0
$ lake env lean .../scratchpad/T2366/pins_eq.lean >/dev/null; echo exit=$?
exit=0
161:example : @RBM.Loop.UniqS = @RBM.Loop.T2366Check.UniqS := rfl
162:example : @RBM.Loop.RetireS = @RBM.Loop.T2366Check.RetireS := rfl
163:example : @RBM.Loop.RotS = @RBM.Loop.T2366Check.RotS := rfl
164:example : @RBM.Loop.TranslS = @RBM.Loop.T2366Check.TranslS := rfl
# --- axioms: #print axioms of 24 declarations (axioms.lean), compacted by axsum.py
$ lake env lean .../axioms.lean | python3 -I axsum.py
24 declarations with axioms [propext, Classical.choice, Quot.sound]:
  UniqS, RetireS, RotS, TranslS, eq_on_levelS, uniqS_holds, retireS_holds, rotS_holds, translS_holds, eq_on_level, isKLoop_unique, KLretire_twoLoopBounded, kTwoFormula_of_isKLoop, pureLoop_two_of_isKLoop, KLK_unique, KLK_translate, KLK_rotate, kernel_one_rot_transl, kernel_SB_rot_transl, UniqueInst_retireS, UniqueInst_uniqS, KLUniqueInst_uniqS_shifted, KLUniqueInst_rotS, KLUniqueInst_translS
# --- targets, extracted by script (python3 -I .../extract.py)
== pin blocks: text of the def block in the file vs in the check file
UniqS: RBM3D/Loop/Unique.lean:98-103  vs  docs/tickets/checks/T2366-check.lean:23-28  identical text: True
RetireS: RBM3D/Loop/Unique.lean:106-110  vs  docs/tickets/checks/T2366-check.lean:31-35  identical text: True
RotS: RBM3D/Loop/KLUnique.lean:94-101  vs  docs/tickets/checks/T2366-check.lean:39-46  identical text: True
TranslS: RBM3D/Loop/KLUnique.lean:105-111  vs  docs/tickets/checks/T2366-check.lean:50-56  identical text: True
== target statements (extracted from the files)
-- RBM3D/Loop/Unique.lean:98-103
def UniqS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b, ‖S a b‖ ≤ 1) → ∀ {T : Set ℝ} {K K' : ℝ → LoopIdx (Zd d L) → ℂ},
      IsKLoopS d L W S m M T K → IsKLoopS d L W S m M T K' → ∀ {T₀ R : ℝ}, Set.Icc 0 T₀ ⊆ T → 0 ≤ R →
      (∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) →
      ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I
-- RBM3D/Loop/Unique.lean:106-110
def RetireS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R
-- RBM3D/Loop/KLUnique.lean:94-101
def RotS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b, S a b = S b a) → (∀ a b, ‖S a b‖ ≤ 1) →
    (∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      M ⟨s :: σ, b :: a⟩ = M ⟨σ ++ [s], a ++ [b]⟩) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length → K t ⟨s :: σ, b :: a⟩ = K t ⟨σ ++ [s], a ++ [b]⟩
-- RBM3D/Loop/KLUnique.lean:105-111
def TranslS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b c : Zd d L, S (a + c) (b + c) = S a b) → (∀ a b, ‖S a b‖ ≤ 1) →
    (∀ (c : Zd d L) (I : LoopIdx (Zd d L)), M ⟨I.σ, I.a.map (· + c)⟩ = M I) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      K t ⟨I.σ, I.a.map (· + c)⟩ = K t I
-- RBM3D/Loop/Unique.lean:291-291
theorem uniqS_holds : UniqS := by
-- RBM3D/Loop/Unique.lean:347-347
theorem retireS_holds : RetireS := by
-- RBM3D/Loop/KLUnique.lean:693-693
theorem rotS_holds : RotS := by
-- RBM3D/Loop/KLUnique.lean:236-236
theorem translS_holds : TranslS := by
# --- the compiled nonempty instances, extracted by script (python3 -I .../inst_extract.py)
-- RBM3D/Loop/Unique.lean:440
theorem UniqueInst_retireS :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) (9 / 10), ∀ I : LoopIdx (Zd 3 5), I.WF → I.length = 2 →
      ‖KLK 3 5 (1 / 2) 2 0 t I‖ ≤ R :=
  retireS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
-- RBM3D/Loop/Unique.lean:448
theorem UniqueInst_uniqS :
    ∀ t ∈ Set.Icc (0 : ℝ) (9 / 10), ∀ I : LoopIdx (Zd 3 5), I.WF → 2 ≤ I.length →
      KLK 3 5 (1 / 2) 2 0 t I = KLK 3 5 (1 / 2) 2 0 t I := by
  obtain ⟨R, hR0, hR⟩ := UniqueInst_retireS
  exact uniqS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
-- RBM3D/Loop/KLUnique.lean:886
theorem KLUniqueInst_uniqS_shifted :
    (fun r (J : LoopIdx (Zd 3 5)) =>
        KLK 3 5 (1 / 2) 2 0 r ⟨J.σ, J.a.map (· + (![1, 0, 0] : Zd 3 5))⟩) (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ := by
-- RBM3D/Loop/KLUnique.lean:911
theorem KLUniqueInst_rotS :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false, true], (0 : Zd 3 5) :: [1, 2]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false, true] ++ [true], [1, 2] ++ [(0 : Zd 3 5)]⟩ :=
  rotS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
-- RBM3D/Loop/KLUnique.lean:921
theorem KLUniqueInst_translS :
    KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true],
          ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5)).map (· + (![1, 0, 0] : Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ :=
  translS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
-- RBM3D/Loop/KLUnique.lean:866
theorem kernel_one_rot_transl {d L : ℕ} [NeZero L] :
    (∀ a b : Zd d L, (1 : Matrix (Zd d L) (Zd d L) ℂ) a b = (1 : Matrix (Zd d L) (Zd d L) ℂ) b a) ∧
    (∀ a b : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a b‖ ≤ 1) ∧
    (∀ a b c : Zd d L, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a + c) (b + c)
      = (1 : Matrix (Zd d L) (Zd d L) ℂ) a b) :=
-- RBM3D/Loop/KLUnique.lean:876
theorem kernel_SB_rot_transl {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) :
    (∀ a b : Zd d L, SB d L g a b = SB d L g b a) ∧ (∀ a b : Zd d L, ‖SB d L g a b‖ ≤ 1) ∧
    (∀ a b c : Zd d L, SB d L g (a + c) (b + c) = SB d L g a b) :=
# --- name clashes of the 16 new public names (this branch outside the two files; and on main, whole tree)
$ for n in <16 names>; do grep -rnw $n RBM3D RBM3D.lean --include=*.lean | grep -v <the two files> | wc -l; done | sort | uniq -c
  16        0
$ git grep -nw -e UniqS -e RetireS -e RotS -e TranslS -e uniqS_holds -e retireS_holds -e rotS_holds -e translS_holds -e eq_on_levelS main -- RBM3D RBM3D.lean | wc -l
       0
```

### Narrative (at most 40 lines; facts as in the script output above and in the files)
- `Unique.lean` (374 -> 459 lines): pins `UniqS`, `RetireS` (text-identical to the check file); `eq_on_level` generalised in place to `eq_on_levelS` (`hL : 3 ≤ L` replaced by `S` and `hS : ∀ a b, ‖S a b‖ ≤ 1`; `treeEqRhs d L W g` -> `treeEqRhsS d L W S`, `SB d L g a b` -> `S a b`); `uniqS_holds` (strong induction over `eq_on_levelS`), `retireS_holds` (the continuity proof of `KLretire_twoLoopBounded`, moved).
- Band statements kept with their old statements as wrappers: `eq_on_level` (`eq_on_levelS` at `SB d L g`), `isKLoop_unique` (`uniqS_holds` at `SB d L g`, `MLoop`), `KLretire_twoLoopBounded` (`retireS_holds`). `kTwoFormula_of_isKLoop`, `pureLoop_two_of_isKLoop`, `KLK_unique` are textually unchanged.
- `KLUnique.lean` (766 -> 935 lines): pins `RotS`, `TranslS`; `translS_holds` (shifted family is `IsKLoopS` via the private `KLUnique_isKLoopS_shift`, both families bounded by `retireS_holds`, equal by `uniqS_holds`; length 0 and 1 by hand); `rotS_holds` (private `KLUnique_rot_eq_on_level`, `KLUnique_isKLoopS_rot`, `KLUnique_treeEqRhsS_split/rot` now take `S`; `hsymm` replaces `SB_transpose`, `hS` replaces `norm_SB_apply_le`, `KLUnique_M_rot` turns the `RotS` hypothesis on `M` into `M (rot J) = M J`). The cut combinatorics of section 4 is unchanged.
- `KLK_translate` and `KLK_rotate` are now one-term instances of `translS_holds`, `rotS_holds` at `S = SB d L g`, `M = MLoop` (`SB_apply_add_right`, `SB_transpose`, `norm_SB_apply_le`, `KLUnique_MLoop_shift`, `KLUnique_MLoop_rot_cons`, family `KLK_isKLoop`). The old inline translation proof (via `KLK_unique`) is deleted; the private `KLUnique_isKLoop_shift` stays as a wrapper for `KLUniqueInst_unique_shifted`.
- No fact about `S` or `M` beyond the pins was needed (no amend). `3 ≤ L` occurs only in the band wrappers and the instances.
- Instances (d = 3, L = 5, W = 2, g = 1/2, E = 0, m = mSigma 0, t = 9/10, K = 𝒦 from the merged `KLTreeDerivInst_isKLoop`): `UniqueInst_retireS`, `UniqueInst_uniqS` (here `K = K' = 𝒦`, so its conclusion is a reflexive equation; every hypothesis is discharged), `KLUniqueInst_uniqS_shifted` (`K = 𝒦 ∘ shift_{e₁}` and `K' = 𝒦`, different as functions), `KLUniqueInst_rotS` (n = 3), `KLUniqueInst_translS` (n = 3). The band instances `KLUniqueInst_*` (old) are untouched and compile (full build).
- `kernel_one_rot_transl` (`S = 1`, any `d`, any `L` with `NeZero L`) and `kernel_SB_rot_transl` (`S = SB d L g`, `3 ≤ L`) compile the three hypotheses on `S` of `RotS`/`TranslS`. No `IsKLoopS` family at `S = 1` is built here (the K03 pin `BAKexists`).
- `Unique.lean` got `set_option linter.style.longLine false` after its module docstring (the pins are verbatim lines; the longest line of `Unique.lean` has 120 characters).
- No port from RBM1D/RBM2D was added in this ticket (it restates merged proofs in this project), so there is no RBM1D/RBM2D diff-stat.

## (c) Verified Mathlib names used in new or moved code (`#check` in scratchpad/T2366/names.lean, exit 0)
- `Nat.strong_induction_on`: `∀ {p : ℕ → Prop} (n : ℕ), (∀ n, (∀ m < n, p m) → p n) → p n`
- `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`: Grönwall step, `Mathlib.Analysis.ODE.Gronwall`
- `IsCompact.exists_bound_of_continuousOn`: `IsCompact s → ContinuousOn f s → ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C`
- `continuousOn_pi`, `hasDerivAt_pi`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`: coordinatewise statements for `LoopVec`
- `List.length_eq_zero_iff : l.length = 0 ↔ l = []`; `List.length_eq_one_iff : l.length = 1 ↔ ∃ a, l = [a]`
- `List.exists_cons_of_length_pos : 0 < l.length → ∃ h t, l = h :: t`
- `Equiv.sum_comp (e : ι ≃ κ) (g : κ → M) : ∑ i, g (e i) = ∑ i, g i`; `Equiv.addRight`; `add_left_inj`
- `Matrix.one_apply : (1 : Matrix n n α) i j = if i = j then 1 else 0`; `if_congr`
- `Finset.sum_nbij'`, `Finset.sum_Ioc_succ_top`, `Finset.sum_Icc_succ_top`, `Finset.sum_insert`, `norm_sum_le`, `List.rotate_perm`, `List.map_rotate` (unchanged private proofs)
- Names verified absent: none searched for.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2366a` not used): the statements are the band ones over a general kernel.
- K03 hand-off: the hypotheses on `S` of `RotS`/`TranslS` at `S = 1` are `kernel_one_rot_transl`; the hypotheses on `M = BAMLoop` (rotation for every `M`, translation iff `M_s (x+c) (y+c) = M_s x y`; scripted in (a)) stay K03's.
- `Loop/Unique.lean` now imports `KLTreeDeriv` (see (a′)); importers of `Unique` (`TreeThree`, `Test/InterfaceShape`, `Induction/NQEndFlowLift`, ...) see that import. The full `lake build` shows no clash.
- Style observation: `lake build RBM3D.Loop.KLUnique` prints 4 long-line warnings (`KLUnique.lean` lines 71, 72, 73, 76, in the module docstring paragraph added by this ticket); `Unique.lean` prints none of its own. A docstring-only rewrap made the importer `RBM3D.Loop.KLWard` out of date in `lake build --no-build`, so it was reverted (HEAD is the fully built commit f4e179e; full build 23:25:59 to 00:39:10 UTC) instead of rerunning the full build.
