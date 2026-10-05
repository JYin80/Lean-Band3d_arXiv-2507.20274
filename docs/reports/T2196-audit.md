Auditor model: claude-opus-5-5

# T2196 audit (round 1) — UN-25 Universality/GUEPhase/AuxCarrier

Time: Mon Oct  5 16:46:00 UTC 2026. Branch t/T2196 at a726626, main at d783ee3. Audit worktree: /Users/junyin/Lean_proof/RBM3D-wt/T2196-audit1 (detached at a726626).
Scratch: $S = scratchpad/T2196/ (pins.lean, neg.lean, ax.lean, reg.lean, src.lean).

## 1. Diff scope and hygiene
```
$ git diff --name-only main...t/T2196
RBM3D/Universality/GUEPhase/AuxCarrier.lean
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Universality/GUEPhase/AuxCarrier.lean | wc -l
       0
$ grep -nE "^(structure|class)" RBM3D/Universality/GUEPhase/AuxCarrier.lean | wc -l
       0
```
Only the sole writable file is touched (RBM3D/Test/Axioms.lean unchanged, no merged file edited: no frozen signature touched).
The file imports exactly PinsK, OU, Green.IBP, Induction.ConArgDet, Gauss.Domination (lines 6-10).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.GUEPhase.AuxCarrier
✔ [3357/3357] Built RBM3D.Universality.GUEPhase.AuxCarrier (11s)
Build completed successfully (3357 jobs).
exit 0
$ lake env lean $S/reg.lean      (import RBM3D + import ...AuxCarrier + #assert_rbm_axioms)
reg exit=0
axiom audit: 5748 theorems, 2054 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; ...
$ lake env lean $S/ax.lean       (#print axioms, 8 targets + 3 carrier lemmas + 15 instances)
'RBM.Univ.svarF_pos_of_block_eq' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.exists_seqP_map_eq_gaussLaw' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.sum_Smix_row' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.chaos_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.gaussLaw_quad_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_quad_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.kind_quad_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.aux_lin_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.svarF_aux_pos' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.auxT_law' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.auxHG_law' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_svarF_pos_of_block_eq' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_aux_pos' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_auxT_law' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_auxHG_law' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_exists_seqP_map_eq_gaussLaw' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_chaos_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_gue_quad_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_band_quad_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_shift_quad_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_kind_quad_tail_band' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_kind_quad_tail_band_size' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_aux_lin_tail' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_sum_Smix_row' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_mixVar_exp_eq_ouVar' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_bounds' : [propext, Classical.choice, Quot.sound]
ax exit=0
```
All 26 printed: only `propext`, `Classical.choice`, `Quot.sound`.

## 3. Statements against the check-file pins
`$S/pins.lean` = `import RBM3D.Universality.GUEPhase.AuxCarrier` + the check file's §2 (from `/-! ## 2. Pinned statements -/`
through `end RBM.Univ.T2196Check`, copied by `awk`, verbatim) + one example per pin:
```
example : T2196_svarF_pos_of_block_eq := fun d L W _ _ g i j h => svarF_pos_of_block_eq d L W g i j h
example : T2196_exists_seqP_map_eq_gaussLaw := fun d L W _ _ v => exists_seqP_map_eq_gaussLaw d L W v
example : T2196_sum_Smix_row := fun d L W _ _ hL g a b i => sum_Smix_row d L W hL g a b i
example : T2196_chaos_tail := fun {d} {sz} {κ} _ _ C {lam} hlam q => chaos_tail C hlam q
example : T2196_gaussLaw_quad_tail := fun d L W _ _ v hv A hA z hz i lam hlam q => gaussLaw_quad_tail hv hA hz i hlam q
example : T2196_gue_quad_tail := fun d L W _ _ z hz i lam hlam q => gue_quad_tail hz i hlam q
example : T2196_quad_tail_kind := fun {d} K sz n a b z hz i lam hlam q => kind_quad_tail K sz n a b hz i hlam q
example : T2196_aux_lin_tail := fun {d} {sz} {κ} _ _ C Y R hR0 hch hV Λ hΛ q => aux_lin_tail C Y R hR0 hch hV hΛ q
example : T2196_inst_bounds := AuxCarrierCheck.inst_bounds
$ lake env lean $S/pins.lean; echo "pins exit=$?"
pins exit=0
$ (negative control: aux_lin_tail example with `(q+1)` in place of `q`)  lake env lean $S/neg.lean
neg.lean:125:80: error: (deterministic) timeout at ...            neg exit=1
```
Every pin is matched by its target up to unfolding of `gaussLaw`, `quadVqS`, `quadQS`, `sigRow`, `rowCoordF`, `TagFree`,
`mixVar` (definitional, checked by the elaborator). Binder differences (`{d L W}`, `{v}`, `{A}` implicit in
`gaussLaw_quad_tail`/`gue_quad_tail`; `κ : Type*` in `chaos_tail`/`aux_lin_tail`) are as the check file allows.

Mathematics of the pins, read from the Lean definitions (`AuxCarrier.lean:649-788`):
- `quadQS` = `∑_{k,l≠i} X_ik G^{(i)}_kl X_li − ∑_{k≠i} σ_ik G^{(i)}_kk`, `G^{(i)} = green ((A + X).submatrix val val) z`,
  `σ_ik = sigRow = 2 v(rowCoordF i k true)`; `quadVqS = ∑ σ_ik |G_kl|² σ_il`. Row entries are from the centred `X`;
  the shift enters only through the minor (ticket target 6). Hypotheses: `TagFree v`, `A.IsHermitian`, `z.im ≠ 0`, `0 < lam`;
  no `3 ≤ d`, no `3 ≤ L` (only `sum_Smix_row`, `sum_Smix_col` take `3 ≤ L`, as pinned), no lower bound on `N` or `lam`.
- `gue_quad_tail`: `sigRow_gueVar` (`:938`) gives `σ_ik = ((W L)^d)⁻¹` off the diagonal, `A = 0`; exact RBM2D shape with `^d`.
- `kind_quad_tail`: `v = mixVar d L W (K.lamV sz n) a b`, `A = (K.M sz).mean n`; discharged by `mixVar_tagFree`, `mean_herm`.
- Ported generic statements compared with RBM2D `c9a24cf` (`git show c9a24cf:... > $S/src.lean`): `chaos_tail` (src `:472`),
  `aux_lin_tail` (src `:1076`) identical up to `{d : Sizes} ↦ {d : ℕ} {sz : Sizes d}`; `gaussLaw_quad_tail` (src `:836`)
  = source + `{A} (hA : A.IsHermitian)` + `A` in `quadVqS/quadQS` (the ticket's generalisation; source is `A = 0`).

## 4. Hidden hypotheses, vacuity, cycles
- No `structure`/`class` is introduced. The merged `RowChaos` (`Green/LDEQuad.lean:338`) has data/structural fields only
  (`co`, `co_inj`, `gvar_tag`, `eps`, `eps_sq`, `r`, `B`, `B_cont`, `Bbd`, `B_bdd`, `Ifree`, `Ifree_free`, `B_free`);
  `auxQuadChaos` (`:711`) and `auxLinChaos` (`:1014`) construct it, so the tails of targets 6-8 assume nothing beyond their signature.
- `chaos_tail`/`aux_lin_tail` are for an arbitrary `RowChaos` (pinned shape); the GaussIBP input is the merged `gaussIBP sz`.
- No external hypothesis is introduced, so no limit check is owed. Dependencies are merged modules only (imports above).
- Registry pre-check exit 0 (§2): `TagFree` not flagged; no new owed premise.

## 5. Compiled nonempty instances (namespace `RBM.Univ.AuxCarrierCheck`, `AuxCarrier.lean:1212-1362`)
All in the module build of §2, axioms printed in §2. Data `d = 3, L = 3, W = 2` (`N = 216`), `z = Complex.I`, row `0`.
| target | instance | data / hypotheses discharged |
|---|---|---|
| 1-2 | `inst_svarF_pos_of_block_eq`, `inst_aux_pos` | points `0`, `![1,0,0]` (same block by `fin_cases k <;> decide`); `0`, `![1,2,3]` |
| 3 | `inst_auxT_law`, `inst_auxHG_law`, `inst_exists_seqP_map_eq_gaussLaw` | `v = gueVar 3 3 2`; `mixVar 3 3 2 (1/2) (1/2) (1/2)` |
| 4 | `inst_sum_Smix_row`, `inst_mixVar_exp_eq_ouVar` | `3 ≤ 3` by `norm_num`, `g = a = b = 1/2` |
| 5 | `inst_chaos_tail` | `auxQuadChaos` at `gueVar`, `A = 0` (`isHermitian_zero`), `Im I ≠ 0` by `simp`, `λ = 4`, `q = 0` |
| 6 | `inst_band_quad_tail`, `inst_shift_quad_tail` | `gvarF 3 3 2 (1/2)`, `A = 0`; `mixVar 3 3 2 0 (1/2) (1/2)`, `A = 1` (`isHermitian_one`); tag-free by lemma |
| 7 | `inst_gue_quad_tail` | `λ = 4`, `q = 0` |
| 8 | `inst_kind_quad_tail_band` (+ `_size`) | `UNKind.band 3`, `SizesInst.sz0`, `a = b = 1/2`, `n`, `i` variables (as the ticket requires); `sz0` at `n = 0`: `(4, 32)`, size `2^21` |
| 9 | `inst_aux_lin_tail` | `auxLinChaos` with `c ≡ 1`, `Cb = 1`, `Y, R` explicit, `R ≥ 0` proved, `Λ = 3`, `q = 0` |
| bounds | `inst_bounds` (= pin `T2196_inst_bounds`) | `hwConst 0/4 = 1/2`, `hwConst 0/(3−1)² = 1/2`: no instance conclusion is trivial |
No `N = 0`, no empty index type, no `False` premise; every deterministic hypothesis is discharged.

## 6. Paper deltas
`grep -n T2196 docs/paper-deltas.md` → 0 hits (main worktree); the prove report (d) proposes `T2196a` (LDE for the minor of
`A + X`, deterministic Hermitian `A`; paper `3_5_Loop_Hierarchy.tex:13-38` states no shifted form), `T2196b` (aux positivity from
`sbKernelR 0 = (1+2dg²)⁻¹`, `lam ≡ 0`; Lean structure), `T2196c` (coupling `g` in `mixVar`/`Smix`; Lean parametrisation),
exactly the three candidates the ticket asks for. The tail form `P(λV < |Q|²) ≤ A_q/λ^{q+1}` (vs the paper's `≺`) is the merged
LDE layer's form (S1-12..S1-19), not introduced here. Coverage complete.

## 7. Verdict per target
| # | target | verdict |
|---|---|---|
| 1 | auxiliary carrier (`auxSizes`, `auxEmb`, `split_auxEmb_fst`, `auxRho`) | PASS |
| 2 | `svarF_pos_of_block_eq`, `svarF_aux_pos`, `seqGvar_aux_rho_pos` | PASS |
| 3 | `auxT_law`, `auxHG_law`, `exists_seqP_map_eq_gaussLaw` | PASS |
| 4 | `gaussLaw`, `mixVar`, `Smix`, `sum_Smix_row`, `mixVar_exp_eq_ouVar`, `TagFree`, `mixVar_tagFree` | PASS |
| 5 | `chaos_tail` | PASS |
| 6 | `gaussLaw_quad_tail` (shift `A`) | PASS |
| 7 | `gue_quad_tail` | PASS |
| 8 | `kind_quad_tail` | PASS |
| 9 | `aux_lin_tail` | PASS |

Observations (no effect on statement, instance, build, axioms or delta coverage):
- My negative control fails by a heartbeat timeout rather than a type mismatch (same as the prover's); the positive file compiles,
  so the pins are matched definitionally.
- The full `lake build` is the hub's at merge (root import not yet added).

**Overall: PASS.** No dispatcher sign-off needed.
