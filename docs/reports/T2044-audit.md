Auditor model: claude-opus-5-5

# T2044 audit (round 1) — S1-13 port `Green/LDEQuadMom.lean`

Audited: `t/T2044` at `d329c31`, detached worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2044-audit1`; written Sat Oct  3 10:35:42 UTC 2026.
Targets: `RowChaos.Vq_eq_ldeQuadRHS` (RBM2D :765), `RowChaos.integrable_norm_pow` (:509), and the other 35 public declarations of the source (ST1-COMMON item 6; `mom_succ_le` is used by S1-14).

## 1. Statement (script diff against the pin = RBM2D `c9a24cf` after rule R1)

```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/LDEQuadMom.lean > src.lean
$ sed -n '70,786p' src.lean | perl -Mutf8 -CSD -pe 's/variable \{d : Sizes\}/variable {d : ℕ} {sz : Sizes d}/;
    s/\(d := d\)/(sz := sz)/g; s/\b(Tame|GaussIBP|RowChaos|Sizes\.SeqΩ|Sizes\.seqP|Sizes\.seqGvar) d\b/$1 sz/g' > src_r1.lean
$ sed -n '66,782p' new.lean > new_body.lean ; diff src_r1.lean new_body.lean
653c653
< `RBM.Green.LDEQuad` (`RBM2D/Green/EntryCore.lean`), once the row chaos is indexed by
---
> `RBM.Green.LDEQuad` (`RBM3D/Green/EntryCore.lean`), once the row chaos is indexed by
diff exit 1
```
The whole ported body (namespace `RBM.Green` to `end RowChaos`, statements and proofs) equals the source after R1; the only residual is a docstring path. Declaration sets:
```
$ grep -oE "^(theorem|noncomputable def|def|lemma) [^ ]+" {src_r1,new_body}.lean | sort ; wc ; diff
37
37
decl-set diff exit 0
$ sed -n '921,970p' src.lean | grep -E "^(theorem|lemma|def|noncomputable def|abbrev|instance)"   -> exit 1 (none)
```
No public declaration dropped; source lines 787–970 are the d = 2 private `Checks` and `#print` lines, replaced by a d = 3 section.

Key statements as compiled (`RBM3D/Green/LDEQuadMom.lean`):
```
theorem integrable_norm_pow (q : ℕ) :                      -- variables: C : RowChaos sz κ, hG : GaussIBP sz
    Integrable (fun ω => ‖C.chaos ω‖ ^ (2 * q)) (Sizes.seqP sz)
theorem mom_succ_le (q : ℕ) :
    C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1)
theorem Vq_eq_ldeQuadRHS (C : RowChaos sz {k : n // k ≠ i}) (ω : Sizes.SeqΩ sz)
    (G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1)
    (hsg' : ∀ k : {k : n // k ≠ i}, C.sg k = t * S k.1 i) :
    C.Vq ω = t ^ 2 * ldeQuadRHS S G i
```
Against the ticket's mathematics: `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` for all `p = q+1 ≥ 1`; `Vq = Σ_{k,l≠i} σ_k|G^{(i)}_{kl}|²σ_l = t²·Σ S_ik|G^{(i)}_kl|²S_li` (`ldeQuadRHS`, EntryCore:537). Quantifiers, constants and index ranges (`{k // k ≠ i}` ↔ `univ.erase i`) match. Dimension-free:
```
$ grep -nE "d = 2|Z2|W \^ 2|Idx L W|svar |scaleM|ellT|Meta" RBM3D/Green/LDEQuadMom.lean ; echo $?
1
```
**Statement: PASS** (all 37 declarations).

## 2. Hidden hypotheses, vacuity, cycles

- Hypotheses carried: `hG : GaussIBP sz` (`structure GaussIBP (sz : Sizes d) : Prop`, LDEQuad.lean:302, fields `stein`, `polyInt`) on the integrating lemmas only. It is a registered **owed** premise, to be proved by S1-19:
```
RBM3D/Test/Axioms.lean:90:   `RBM.Green.GaussIBP,  -- Stein identity and finite polynomial moments of `Sizes.seqP`; proved by S1-19 (RBM2D `IBPPoly:299`), taken by `Tame.integrable` (T2031)
```
- `RowChaos` (LDEQuad.lean:338, merged T2031) is a data structure; its proof fields (`co_inj`, `gvar_tag`, `eps_sq`, `B_cont`, `B_bdd`, `Ifree_free`, `B_free`) are all discharged in the instance below; no new structure is introduced by this file.
- Imports: `RBM3D.Green.EntryCore`, `RBM3D.Green.LDEQuad` (both merged on `main`); no import of `RBM3D` or of an ST-2..ST-6 file; no cycle.
**PASS.**

## 3. Compiled nonempty instances (file lines 783–975)

Data: `SizesInst.sz0` slice 0 (`d = 3`, `L = 4`, `W = 32`, `lam = 1/64`); `n = Fin 3`, `i = 0`, `κ = {k // k ≠ 0}` (two elements); coordinates at lattice points `(1,0,0)` (same block) and `(32,0,0)` (neighbour block), injective by `decide`; `B = G^{(0)}` with `G = !![1,0,0;0,2,1;0,0,3]`, `Bbd = 3`, `Ifree = ∅`. Nondegeneracy is proved, not asserted:
```
private theorem chkM_svarF_one : svarF … (chkMPos 0) (chkMPos 1) = ((32:ℝ)^3)⁻¹ * (1 + 2*3*(1/64:ℝ)^2)⁻¹
private theorem chkM_svarF_two : svarF … (chkMPos 0) (chkMPos 2) = ((32:ℝ)^3)⁻¹ * ((1/64:ℝ)^2 * (1 + 2*3*(1/64:ℝ)^2)⁻¹)
private theorem chkM_sg_pos (k : {k : Fin 3 // k ≠ 0}) : 0 < chkMChaos.sg k
```
| Endpoint | Instance | Hypotheses |
|---|---|---|
| `Vq_eq_ldeQuadRHS` | `example (ω) : chkMChaos.Vq ω = 1 ^ 2 * ldeQuadRHS chkMS chkMG 0` | `hB` by `rfl`, `hsg`/`hsg'` by `chkM_sg`/`chkM_sg'`; none left |
| `norm_chaos_sq_eq_ldeQuadLHS` | at row matrix `chkMH ω` | all discharged |
| `integrable_norm_pow` | `example (q) : Integrable (‖chkMChaos.chaos ω‖^(2q)) (seqP sz0)` | `GaussIBP sz0` (S1-19 pin) only |
| `mom_succ_le` | `q = 0, 1`: `mom 1 ≤ 1·momTpow 1 ∧ mom 2 ≤ 9·momTpow 2` | `GaussIBP sz0` only |
| `two_mul_mom_succ_le`, `integral_chaos_mul`, `moment_recursion` | `q = 0,1`; `F = 1`; `q = 0` | `GaussIBP sz0` only |

No `N = 0`, empty index, collapsed window or `False` premise; `σ_k > 0` at both columns and `G ≠ 0`, so `ldeQuadRHS chkMS chkMG 0 > 0`. All compile (build below). **PASS.**

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Green.LDEQuadMom 2>&1 | grep -E "error|sorry|Build completed|✖|declaration uses"
Build completed successfully (3246 jobs).
$ lake env lean scratch/ax.lean      # import RBM3D; import RBM3D.Green.LDEQuadMom; #print axioms …; #assert_rbm_axioms
'RBM.Green.RowChaos.Vq_eq_ldeQuadRHS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.integrable_norm_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.mom_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.two_mul_mom_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.moment_recursion' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.integral_chaos_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.norm_chaos_sq_eq_ldeQuadLHS' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 1517 theorems, 547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Green.GaussIBP: 10 [no certificate]
premises found by scanning: 28 (borrowed 2, owed 14, structural 12).
exit 0
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Green/LDEQuadMom.lean ; echo $?
1
$ git diff --name-only main...t/T2044
RBM3D/Green/LDEQuadMom.lean
$ for n in mom momT momTpow Vq Vq_eq_ldeQuadRHS integrable_norm_pow mom_succ_le two_mul_mom_succ_le \
    moment_recursion integral_chaos_mul norm_chaos_sq_eq_ldeQuadLHS sum_erase_eq integral_ofReal'; do
    git grep -nE "(theorem|def|lemma) $n\b" main -- 'RBM3D/*.lean' | wc -l; done
0 0 0 0 0 0 0 0 0 0 0 0 0
```
(the `#assert_rbm_axioms` output above is trimmed to its axiom line, the `GaussIBP` line and the summary.) The diff touches only the sole writable file (new); `RBM3D/Test/Axioms.lean` is unchanged, consistent with no new `Prop` premise predicate; no frozen signature touched; every helper not in the source is `private` (`chkM*`). **PASS.**

## 5. Paper deltas

```
$ grep -nEi "LDE|LDEQuad|RowChaos|Vq|GaussIBP|mom_succ" docs/paper-deltas.md   -> no LDE/RowChaos entry
$ sed -n '36,37p' paper/tex/3_5_Loop_Hierarchy.tex
These estimates have been proven as Lemma 4.1 in \cite{YY_25} … large deviation estimates as in \cite{erdHos2012rigidity,erdos2013delocalization}.
```
The paper (arXiv:2507.20274) does not state the quadratic large-deviation estimate or its moments; they enter only through the citation at 3_5:37. The Lean statements therefore have no paper statement to differ from, and the R1 diff above shows no statement change against the pinned RBM2D source. No paper-delta candidate is required. **PASS.**

## Observations (no effect on statement, instance, build, axioms or delta coverage)

1. The file header has a section "Deviations from the paper" (factor `t²`, extra hypothesis `hsg'`, centring `Σσ_kB_kk` vs `tΣS_ikB_kk`), while report (d) says "No paper-delta candidate". The deviations are relative to the cited LDE form (RBM1D/RBM2D's (4.7)), which this paper does not display; the dispatcher may choose to note in `docs/paper-deltas.md` that the LDE layer formalizes the input cited at 3_5:37 with these conventions. Not a RETURN.
2. Report (b) says "lines 1-787"; the ticket says "796 kept lines". The diff above (source 70–786) and the declaration-set diff show nothing public outside that range, so the count difference is immaterial.
3. `mom_succ_le` bounds by `E[T^p]`, not by `E[Vq^p]`; the positive-chaos step `E[T^p] ≤ C_p E[Vq^p]` is stated as outside this file (header "What is not in this file", item 2), as in RBM2D. S1-14 must supply it.
4. The compiled instance uses `sz0` (ST1-COMMON item 7) rather than the preflight's `W = 2, L = 3`; this is permitted.

## Verdict

| Target | Verdict |
|---|---|
| `RowChaos.Vq_eq_ldeQuadRHS` | PASS |
| `RowChaos.integrable_norm_pow` | PASS |
| remaining 35 public declarations (incl. `mom_succ_le`) | PASS |

**T2044: PASS.** No dispatcher sign-off needed.
