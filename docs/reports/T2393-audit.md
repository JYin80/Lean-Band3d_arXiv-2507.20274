Auditor model: claude-opus-5-5

# T2393 audit (round 1): STContractM, stContractM_holds, stContract_holds as corollary

Branch `t/T2393` @ 915114c; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2393-audit1`; scratch `<scratchpad>/T2393/`.

## 1. Diff scope and stop line

```
$ git diff --numstat main...t/T2393
130	53	RBM3D/Induction/Contract.lean
$ git merge-base --is-ancestor main t/T2393 && echo "main is ancestor"
main is ancestor
$ git show main:RBM3D/Induction/Contract.lean | grep -n "^theorem stContract_holds"
1046:theorem stContract_holds (d : ℕ) : STContract d := by
$ git show t/T2393:RBM3D/Induction/Contract.lean | grep -nE "^(theorem|def|private lemma Contract_|example)" | tail -12
1003:def Contract_maxLoopM (d L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ)
1011:def STContractM (d : ℕ) : Prop :=
1039:private lemma Contract_loopL_eq_trace_wd (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
1046:private lemma Contract_norm_trace_wd_le (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
1062:private lemma Contract_maxLoopM_nonneg (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (k : ℕ) :
1069:theorem stContractM_holds (d : ℕ) : STContractM d := by
1123:theorem stContract_holds (d : ℕ) : STContract d := by
1152:example :   1164:example :   1180:example :   1197:example :
```
Only the sole writable file is touched; 130 + 53 = 183 changed lines (< stop line 600). `stContract_holds` keeps
name and type `STContract d`; `Step34Pins.lean` (`STContract`, `STLI`, `STmaxL`) and `Step2Defs.lean` (`STContractPt`)
are not in the diff. The four removed declarations (`blockMat_flow_isHermitian`, `STLI_eq_trace_wd`,
`norm_trace_wd_le_STmaxL`, `STmaxL_nonneg`) were `private`; grep outside `Contract.lean` finds only the unrelated
private `SEforLn1_STmaxL_nonneg` / `SEforLn2_STmaxL_nonneg`. New public `Contract_maxLoopM` carries the file stem (§3 (E)).

## 2. Statement: `STContractM` against the pin `STContract` (script diff)

Ticket target 1: `STContract` parts (1),(2) with `STLI ↦ loopL`, `STmaxL ↦ max_{σ,a} ‖loopFine d L W H z σ a‖`,
`(W^d etaT E τ)⁻¹ ↦ (W^d z.im)⁻¹`, binders `∀ L W [NeZero L] [NeZero W] H z, H.IsHermitian → 0 < z.im →` (shape of
`STContractPt`). Script: take the body of `STContract` (from `Step34Pins.lean`, after the `sz n E τ ω` binder line),
apply exactly the ticket's substitutions, and compare with the body of `STContractM`:
```
$ awk '/^def STContract \(d/{f=1} f&&/^$/{exit} f' RBM3D/Induction/Step34Pins.lean | tail -n +3 > pin.txt
$ awk '/^def STContractM \(d/{f=1} f&&/^$/{exit} f' RBM3D/Induction/Contract.lean | tail -n +4 > m.txt
$ sed -E -e 's/STLI sz n E τ ω /loopL d L W (blockMat d L W H) z /g' -e 's/STmaxL sz n E τ/Contract_maxLoopM d L W H z/g' \
    -e 's/\) ω/)/g' -e 's/\(sz\.L n\)/L/g; s/sz\.W n/W/g; s/etaT E τ/z.im/g' pin.txt > pin_sub.txt
$ diff -w <(tr -s ' \n' ' ' < pin_sub.txt) <(tr -s ' \n' ' ' < m.txt) && echo IDENTICAL
IDENTICAL
$ awk '/^def STContractM \(d/{f=1} f' RBM3D/Induction/Contract.lean | sed -n 1,3p
def STContractM (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ),
    H.IsHermitian → 0 < z.im →
```
- Hypotheses/quantifiers/ranges: identical to the pin after substitution (part (1): `1 ≤ k`, `k+1 ≤ m`; part (2):
  `4 ≤ m`, `1 ≤ p`, `1 ≤ k < j+1 < l`, `l+1 ≤ m`, `0 ≤ C`, `|𝒜 x| ≤ C`); losses `(W^d Im z)⁻¹`, exponents `1/2`,
  `1/(2p)`, word lengths `2k-1`, `2m-2k-1`, `2m-2l-1`, `2(l-k)p` unchanged. No `E`, `τ`, `|E|<2` in the matrix form.
- `Contract_maxLoopM d L W H z k` (`:1003`) is the same `Finset.univ.sup'` as `STmaxL` (`Step34Pins.lean:50-52`) with
  `Lloop sz n E v` = `loopFine … (seqHflow …) (zt E v)` (`GLoopFlow.lean:158`) replaced by `loopFine d L W H z`: it is
  the ticket's `max_{σ,a} ‖loopFine d L W H z σ a‖`.
- Ticket text `loopL d L W H z` is ill-typed (`loopL` takes a `Vtx` matrix, `GLoopFlow.lean:123`); the Lean uses
  `loopL d L W (blockMat d L W H) z`, which is what `STLI` is at `H = seqHflow …` (`Step34Pins.lean:107-108`). The
  ticket's "corollary at `H = blockMat (seqHflow …)`" likewise reads correctly as `H = seqHflow …` (H is a fine-lattice
  matrix). Both are ticket-wording corrections recorded in prove report (a); they change no statement.
Target 1: **PASS**.

## 3. Proof, corollary, G1, no hidden hypothesis / cycle

`stContractM_holds` uses only `hHerm : H.IsHermitian`, `hz : 0 < z.im` and the band-free §1–§6 lemmas
(`part1_matrix`, `part2_matrix`, `list_split1/2`, …; diff hunks show §1–§6 untouched). `STContractM` is a `def … : Prop`
(no structure, no hidden fields); it depends on nothing downstream (`Contract.lean` imports unchanged).
`stContract_holds` is derived from `stContractM_holds` at `seqHflow sz n τ ω`, `zt E τ`, with `Im z > 0` from
`etaT_pos hE h1`. An independent derivation `STContractM d → STContract d` was compiled by the auditor:
```
$ cat g1.lean        # import RBM3D; open RBM.Gauss RBM.Gauss.Sizes; variable (d : ℕ)
example : STContract d := stContract_holds d
example : STContractPt d := stContractPt_holds d
example : STContractM d := stContractM_holds d
example : STContractM d → STContract d := fun h sz n E τ hE _ h1 ω => by
  have hzim := (etaT_eq_zt_im (E := E) (t := τ)).symm
  have := h (sz.L n) (sz.W n) (seqHflow sz n τ ω) _ (seqHflow_isHermitian sz n τ ω)
    (by rw [hzim]; exact etaT_pos hE h1)
  rw [hzim] at this; exact this
#print axioms stContractM_holds
#print axioms stContract_holds
#print axioms Contract_maxLoopM
$ lake env lean g1.lean; echo "exit=$?"
'RBM.Gauss.Sizes.stContractM_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stContract_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Contract_maxLoopM' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
So `|E| < 2` enters only through `Im (zt E τ) > 0`; `0 ≤ τ` is unused. G1 (target 4): both band pins elaborate
against the unchanged names. Targets 2, 3, 4: **PASS**.

## 4. Compiled nonempty instances (target 5)

`Contract.lean:1180` and `:1197` apply `stContractM_holds 3 3 2 _ Complex.I` at
`H = coordinateMatrix 3 3 2 (0,1,true) + coordinateMatrix 3 3 2 (1,0,true)` (the `LoopGenN_M0` matrix of
`LoopGenN.lean:683`), with `H.IsHermitian` by `(coordinateMatrix_isHermitian …).add (…)` and `0 < Complex.I.im` by
`simp`. Part (1) at `m=2, k=1, σ=(+,-), a=(0)`; part (2) at `m=4, k=1, l=3, p=1, j=⟨1,_⟩` (so `k=1 < j+1=2 < l=3`,
`l+1=4 ≤ m`), `C=1`, `𝒜 x = {x}`. Every hypothesis is discharged; no open premise. Data: `d=3`, `L=3`, `W=2`,
216 sites, 27 blocks, `Im z = 1`, `𝒜 x` nonempty. `H` is non-scalar (auditor check, `nz.lean`):
```
$ cat nz.lean   # import RBM3D; open RBM.Gauss RBM.Gauss.Sizes
example : (coordinateMatrix 3 3 2 ((0 : Idx 3 3 2), (1 : Idx 3 3 2), true) +
    coordinateMatrix 3 3 2 ((1 : Idx 3 3 2), (0 : Idx 3 3 2), true)) (0 : Idx 3 3 2) (1 : Idx 3 3 2) = 1 := by
  … (same proof as LoopGenN_M0_apply, LoopGenN.lean:690-698)
$ lake env lean nz.lean; echo "nz exit=$?"
nz exit=0
```
A nonzero off-diagonal entry, so `H` is not a multiple of `1` and is not a band-flow matrix. The band examples
`:1152`, `:1164` (of `stContract_holds`) are unchanged in the diff. Target 5: **PASS**.

## 5. Build, axioms, hygiene, check file

```
$ lake build RBM3D.Induction.Contract 2>&1 | grep -E "error|Built RBM3D.Induction.Contract|Build completed" | tail -5
✔ [3706/3706] Built RBM3D.Induction.Contract (5.4s)
Build completed successfully (3706 jobs).
$ lake build RBM3D.Induction.SEforLn1 RBM3D.Induction.SEforLn2 RBM3D.Induction.ContractPt \
    RBM3D.Induction.EMn2Poly RBM3D.Induction.EMn2Exp1 RBM3D.Induction.EMn2Exp2 2>&1 | grep -E "error|Build completed"
Build completed successfully (3814 jobs).
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2393-check.lean >/dev/null; echo "check exit=$?"
check exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/Contract.lean; echo "grep exit=$?"
grep exit=1
```
Registry pre-check (`import RBM3D` + `#assert_rbm_axioms`, run in an earlier version of `g1.lean`) printed
`axiom audit: 11209 theorems, 3358 definitions, 0 axioms in RBM … All within [propext, Classical.choice, Quot.sound]`
with no error from the `#assert_rbm_axioms` line. (Full `lake build` is the hub's at merge.)

## 6. Paper deltas

`STContract` (the paper's `ygdhmsgq`, `(yi2oslxj2)`, `(u2jzooi-2)`, `3_5_Loop_Hierarchy.tex`) is unchanged. `STContractM`
is a Lean-only generalisation of the same inequality (any Hermitian `H`, `η_t ↦ Im z`), prescribed by DECISIONS §205 (3);
the paper's proof is deterministic and uses only Hermiticity and `Im z > 0`. Precedent: `STContractPt` is matrix-generic
and its delta entry D180 records only the constant, not the generality. No statement difference with the paper's pinned
lemma is introduced; coverage is adequate.

## Observations (no effect on verdict)

- O1. Docstring of `STContractM` (`:1007-1009`) says the band data `(blockMat (seqHflow …), zt E τ)` is replaced by `H`;
  in the Lean `H` replaces `seqHflow …` (the `blockMat` stays inside). Docstring only.
- O2. Optional for the dispatcher: a one-line paper-delta note `T2393a` — "`STContractM` (`Induction/Contract.lean`)
  states `(yi2oslxj2)`, `(u2jzooi-2)` for any Hermitian `H` on `Z_{WL}^d` and `Im z > 0`, with `η_t` replaced by
  `Im z`; `STContract` is its corollary at `(H_τ, z_τ)`." Not required (see §6).
- O3. Prove report (b) gives "+77 net"; measured as 130 + 53 = 183 changed lines it is also far under 600.
## Verdict
Targets 1 `STContractM` PASS; 2 `stContractM_holds` PASS; 3 `stContract_holds` (old name/statement, corollary) PASS;
4 G1 PASS; 5 non-band instance at `d = 3` PASS; 6 registry pre-check PASS.

**T2393: PASS.** No dispatcher sign-off needed.
