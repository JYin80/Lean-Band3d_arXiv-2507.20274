Auditor model: claude-opus-5-5

# T2052 audit (round 1) — S1-14 port of `Green/LDEQuadT` (`mom_le_momVpow`)

Time (`date -u`): Sat Oct  3 15:12:29 UTC 2026. Branch `t/T2052` at `5842329`, merge-base = `main` = `7c3072a`.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2052-audit1` (detached at `5842329`). Scratch: `scratchpad/T2052/`.

## 1. Statement

Ticket pin: portmap P.7 key statement "LDEQuadT:995 `mom_le_momVpow`" (RBM2D `c9a24cf`), plus every other
public declaration of the source unless the portmap marks it unused; rule R1 renaming (ST1-COMMON).
Check: whole-body diff of the source namespace block (RBM2D :56-1008), R1-renamed by perl, against the new file :70-1023.
```
$ sed -n 56,1008p src.lean | perl -pe 's/\{d : Sizes\}/{d : ℕ} {sz : Sizes d}/g; s/RowChaos d κ/RowChaos sz κ/g;
    s/Sizes\.SeqΩ d/Sizes.SeqΩ sz/g; s/Sizes\.seqP d/Sizes.seqP sz/g; s/Sizes\.seqGvar d/Sizes.seqGvar sz/g;
    s/Tame d /Tame sz /g; s/GaussIBP d\b/GaussIBP sz/g; s/\(d := d\)/(sz := sz)/g' > src_r.lean
$ sed -n 70,1023p RBM3D/Green/LDEQuadT.lean > new_r.lean; diff src_r.lean new_r.lean
278c278
<     show (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
---
>     change (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
707c707
<           show C.w l * _ = 2 * C.r ^ 2 * C.w l * _
---
>           change C.w l * _ = 2 * C.r ^ 2 * C.w l * _
803c803,804
<       Integrable (fun ω : Sizes.SeqΩ sz => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ)) (Sizes.seqP sz) := by
---
>       Integrable (fun ω : Sizes.SeqΩ sz => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
>         (Sizes.seqP sz) := by
$ diff <(public decl names of source :56-1008) <(public decl names of new :70-1023); echo rc=$?
rc=0
```
Every statement (all 61 public declarations) is the source's verbatim after R1; the three diffs are proof-internal
(`show`→`change`, a line wrap). None dropped (portmap row 52 has no "unused" marker). Target as built:
```
theorem mom_le_momVpow (hG : GaussIBP sz) (q : ℕ) :
    C.mom (q + 1)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * C.momVpow (q + 1) := by
```
General in `q : ℕ` (all moments `p = q+1 ≥ 1`), any `d`, any `sz : Sizes d`, any `RowChaos sz κ`; constant
`((2p−1)(4p−2))^p`, which is `mom_succ_le`'s `(2q+1)^{q+1}` times `momTpow_le`'s `(4q+2)^{q+1}` (no loss). Definitions it
uses (merged): `mom q = ∫‖chaos‖^(2q)` (LDEQuadMom:434), `Vq = Σ_k Σ_l sg k ‖B k l‖² sg l` (LDEQuadMom:592);
new `momVpow q = ∫ Vq^q` (LDEQuadT:854). Dimension-free: R1 is the only change, so no `d = 2` token can survive.

## 2. Hidden hypotheses, vacuity, cycles

- Only hypothesis beyond the data: `hG : GaussIBP sz` (LDEQuad.lean:13, `Prop` structure: `stein`, `polyInt`).
  It is registered as owed, proved by S1-19:
```
$ sed -n 88,90p RBM3D/Test/Axioms.lean
   `RBM.Green.GaussIBP,  -- Stein identity and finite polynomial moments of `Sizes.seqP`; proved by S1-19 (RBM2D `IBPPoly:299`), taken by `Tame.integrable` (T2031)
```
- `RowChaos` (merged T2031, LDEQuad.lean:49-76): data plus consistency fields (`co_inj`, `gvar_tag`, `eps_sq`,
  `B_cont`, `B_bdd`, `Ifree_free`, `B_free`); none is a conclusion of this file, and all are discharged at the
  instance below (`chkTChaos`), so the structure is inhabited.
- No cycle: the file imports only `RBM3D.Green.LDEQuadMom` (merged), uses merged `mom_succ_le` (LDEQuadMom:646,
  signature `(q : ℕ)` under section variable `hG`), and introduces no new predicate:
```
$ grep -n "^import" RBM3D/Green/LDEQuadT.lean
6:import RBM3D.Green.LDEQuadMom
```

## 3. Compiled nonempty instance

File section `Checks` (:1034-1198), data `SizesInst.sz0` slice 0 (`d = 3`, `L = 4`, `W = 32`, `lam = 1/64`),
`κ = {k : Fin 3 // k ≠ 0}` (2 elements), `co` injective (`chkTCo_injective`, proved), `eps = 1`, `r = 1`,
`B = greenMinor !![1,0,0;0,2,1;0,0,3] 0` (`Bbd = 3` proved by `chkT_green`), `Ifree = ∅`.
Nondegeneracy proved in Lean: `chkT_sg_pos : 0 < chkTChaos.sg k` for both `k` (via exact `svarF` values
`chkT_svarF_one/_two`), `chkT_Vq_pos : 0 < chkTChaos.Vq ω` for every `ω`. Instances (only `hG : GaussIBP sz0`,
the owed S1-19 premise, left as hypothesis):
```
example : chkTChaos.mom 1 ≤ ... ∧ chkTChaos.mom 2 ≤ ... ∧ chkTChaos.mom 3 ≤ ... :=
  ⟨chkTChaos.mom_le_momVpow hG 0, chkTChaos.mom_le_momVpow hG 1, chkTChaos.mom_le_momVpow hG 2⟩
example : ... := ⟨chkTChaos.momTpow_le hG 0, chkTChaos.momTpow_le hG 1⟩
example : ... := chkTChaos.momTpow_succ_le hG 1
example (ω : Sizes.SeqΩ sz0) : ‖chkTChaos.crossT 0 ω‖ ≤ ... := chkTChaos.norm_crossT_le 0 ω
```
No `N = 0`, empty index, collapsed window or `False` premise; `Vq > 0` so the bound is not `0 ≤ 0`-trivial on
the right. These compile as part of the module build (section 4). Instance: PASS.

## 4. Build, axioms, hygiene, scope

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2052-audit1 && lake build RBM3D.Green.LDEQuadT 2>&1 | grep -E "error|Build completed"
Build completed successfully (3247 jobs).
$ (scratch ax.lean: import RBM3D.Green.LDEQuadT + #print axioms of all 61 public decls of :70-1023)
$ lake env lean ax.lean > ax.out; echo exit=$?; grep -c "\[propext, Classical.choice, Quot.sound\]" ax.out
exit=0
61
$ grep -E "mom_le_momVpow|momTpow_le|momTpow_succ_le'|norm_crossT_le" ax.out
'RBM.Green.RowChaos.norm_crossT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.momTpow_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.momTpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.mom_le_momVpow' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide" RBM3D/Green/LDEQuadT.lean
0
$ git diff --name-status main...t/T2052
A	RBM3D/Green/LDEQuadT.lean
```
Registry pre-check (ST1-COMMON item 8), rerun by the auditor:
```
$ printf 'import RBM3D\nimport RBM3D.Green.LDEQuadT\n#assert_rbm_axioms\n' > precheck.lean
$ lake env lean precheck.lean > pre.out; echo exit=$?; grep -nE "error|GaussIBP|axiom audit|All within" pre.out
exit=0
1:axiom audit: 1909 theorems, 828 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
2:All within [propext,
14:  RBM.Green.GaussIBP: 17 [no certificate]
```
Name-clash scan (each of the 61 public names as a `theorem|lemma|def|abbrev` elsewhere in `RBM3D/`):
```
$ for x in <61 names>; do grep -rnE "(theorem|lemma|def|abbrev) +(RBM\.Green\.)?(RowChaos\.)?$x\b" RBM3D --include='*.lean' | grep -v LDEQuadT.lean; done
(no output)
```
Only a sole writable file is touched (new file; `RBM3D/Test/Axioms.lean` untouched, consistent with no new
premise); no frozen signature changed; checks section helpers are `private`. Build/axioms: PASS.

## 5. Paper deltas

The file is abstract Gaussian calculus for a `RowChaos`; the paper (arXiv:2507.20274) states no lemma of this
form (it cites the quadratic LDE inside `lem_GbEXP`, portmap row 52). The statements are RBM2D's verbatim
(section 1), and the inherited `t²`/`hsg'` concerns `Vq_eq_ldeQuadRHS` (merged T2044), not this file. No
Lean/paper statement difference is introduced here; "no candidate" (report (d)) is correct. PASS.

## Observations (no effect on verdict)

- File docstring says "lines 1-1008" of the source; the ported block is :56-1008 (header/imports differ). Cosmetic.
- Preflight (a) row "GaussIBP ... structural" is corrected in (a′) to owed; consistent with Axioms.lean:88-90.

## Verdict

| Target | Statement | No vacuity/hidden hyp/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `mom_le_momVpow` (key) | = source after R1 | `hG` owed (S1-19) only | yes, q=0,1,2, `Vq>0` | PASS | none needed | **PASS** |
| `momTpow_le`, `momTpow_succ_le`, `norm_crossT_le` | = source | same | yes | PASS | none | **PASS** |
| other 57 public decls | = source | same | (lemmas, used by the above) | PASS | none | **PASS** |

T2052: **PASS**. No dispatcher sign-off needed.
