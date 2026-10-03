Auditor model: claude-opus-5-5

# T2047 audit (S1-33, `RBM3D/Induction/ContinuityNet.lean`), round 1 — written Sat Oct  3 14:56:51 UTC 2026

Branch `t/T2047` at `f486e99` (merge-base with main `6ef5d49`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2047-audit1` (detached).
Targets: the pin `RBM.Ind.GopboundPin` (RBM2D `Continuity:65`) and the cut part (RBM2D `Continuity:1-764`), 34 public declarations (2 defs, 32 theorems).

## 1. Statement

### 1.1 `GopboundPin` against RBM2D `c9a24cf` `Continuity:65-75` (renaming R1-R4, `spectralZ -> zt`, applied by sed)
```
$ sed -n 65,75p cont2d.lean | sed -E 's/Sizes\.seqP d /sz.seqP /; s/SizeTendsto d/sz.SizeTendsto/; s/d\.size/sz.size/g;
    s/Idx \(d\.L n\) \(d\.W n\)/Idx d (sz.L n) (sz.W n)/; s/Sizes\.seqHflow d /sz.seqHflow /g; s/spectralZ/zt/g;
    s/def GopboundPin \(/def GopboundPin {d : ℕ} (sz : Sizes d) (/' > pin2d.txt
$ awk '/^def GopboundPin/{f=1} f{print} /ENNReal.ofReal/{if(f){exit}}' ContinuityNet.lean > pin3d.txt
$ diff pin2d.txt pin3d.txt && echo "PIN IDENTICAL after R1-R4 + spectralZ->zt"
PIN IDENTICAL after R1-R4 + spectralZ->zt
```
The renamed vocabulary means the same thing:
```
RBM2D Gauss/SpectralWindow.lean:21  spectralM (E) := (-E + Real.sqrt (4 - E ^ 2) * I) / 2
RBM3D Defs/Semicircle.lean:38       mE (E)        := (-E + Real.sqrt (4 - E ^ 2) * I) / 2
RBM2D Gauss/SpectralWindow.lean:34  spectralZ (E u) := E + (1 - u) * spectralM E
RBM3D Defs/Semicircle.lean:179      zt (E t)        := E + (1 - t) * mE E
RBM3D Gauss/FineModel.lean:225      seqHflow n u ω := (Real.sqrt u : ℂ) • seqXmat sz n ω   (RBM2D Gauss/Model.lean:495)
RBM3D Defs/Sizes.lean:173           SizeTendsto := Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop
```
Quantifier order `∀ C > 0, ∃ C' > 0, ∀ D > 0, ∀ᶠ n`, window `0 ≤ u,u' ≤ 1 - N⁻¹`, `|u-u'| ≤ N^{-C'}`, max over all `i j : Idx d (L n) (W n)`, bound `N^{-D}` with `N = sz.size n = (W L)^d`: as RBM2D. No `3 ≤ d` (the pin is for every `d`); recorded in T2047a.

### 1.2 Cut part: every RBM2D 1-764 declaration against the new file (independent script `adiff.py`: statements up to `:=`, `private` stripped)
```
$ python3 adiff.py
RBM2D 1-764 decls 42 | identical after renaming 24 | differ 11 | not carried 7
NOT CARRIED: cont_card_Z2:289 cont_abs_min_sub_min_le:609 cont_scaleM_diff:618 cont_im_le_scaleM:631 cont_scaleM_le:640 cont_one_div_sqrt_diff:662 cont_ellT_diff:687
NEW: cont_Gres_true_eq_green:430 cont_Gres_false_eq_green:434 cont_norm_green_le:441 cont_inv_add_one_sub_ratio:676 cont_Bctl_eq:691 cont_inv_size_le_Bctl:701 cont_Bctl_ratio:725
```
The script's 11 "differ" entries, checked one by one (full output in scratch `adiff.out`), are all renaming residue the script's regexes do not cover:
```
GopboundPin            binder  (variable (d : Sizes))  ->  {d : ℕ} (sz : Sizes d)
contGood               Set (sz.SeqΩ)                ->  Set sz.SeqΩ                       (parentheses)
cont_seqGvar_le_one    Sizes.seqGvar d c            ->  sz.seqGvar c                     (R1)
cont_card_coord        Coord (d.L n) (d.W n)        ->  CoordF d (sz.L n) (sz.W n)       (R4); RHS 2 * N^2 unchanged
cont_good_compl, cont_highProbAt_good   contGood d  ->  contGood sz                      (R1)
cont_norm_blockMat_Xmat_le, cont_blockMat_sub, cont_blockMat_smul   blockMat  ->  blockMat d L W
cont_norm_spectralZ_sub, cont_spectralM_im_nonneg   (name rewritten by my own regex; statements equal)
```
Not carried (7: the 5 d = 2 scale lemmas of `scaleM`/`ellT`/`1/√(1-u)`, `cont_card_Z2`, `cont_abs_min_sub_min_le`) are RBM2D `private` helpers whose objects do not exist at d ≥ 3 (ST1-COMMON item 2: the d = 2 scales become `Bctl`). New (7): two `Gres`/`green` bridges, `cont_norm_green_le`, and the `Bctl` facts. Statements of the new scalar facts, checked by hand against `Defs/Sizes.lean:214` (`Bctl = W^{-d}·Bparam(d,L,lam,t,0)`):
```
cont_Bctl_eq          (t<1):        Bctl n t = (W^d)⁻¹ * ((lam² + (1-t))⁻¹ + (L^d (1-t))⁻¹)
cont_inv_size_le_Bctl (0≤s<1):      N⁻¹ ≤ Bctl n s        [second term = (W L)^{-d}(1-s)⁻¹ ≥ N⁻¹]
cont_inv_add_one_sub_ratio (γ≥0, u,u'≤t<1): (γ+1-u)⁻¹ ≤ (1 + (1-t)⁻¹|u-u'|)(γ+1-u')⁻¹   [ratio = 1+(u-u')/(γ+1-u)]
cont_Bctl_ratio       (u,u'≤t<1):   Bctl n u ≤ (1 + (1-t)⁻¹|u-u'|) * Bctl n u'
```
All four are true with the stated hypotheses and are what the merged controls of `STStep1Loop`/`STStep1Weak` (`Induction/Defs.lean`) need. No PT/propagator pin occurs in the file (`grep -c 'PropTH\|Prop5\|Prop6\|ThetaDecay\|KLPT'` = 0, report b.7), so the ticket's "discharge PT pins" clause is empty here.

Cut: RBM2D `Continuity:1-764` (through `end Assembly`, portmap CONT1 = 764/1644), the section boundary before `## 4. Deterministic estimates along the flow` (:765). The second part (`cont_entry_diff` :776 ... `step1NetLift` :1331) compiles against this file alone (see 2).

## 2. Vacuity, hidden hypotheses, cycles
* No structure is introduced; `GopboundPin` is a `Prop` with three premises (`0 < κ`, `|E n| ≤ 2-κ`, `SizeTendsto`), `contGood` is an event (`∀ c, |ω c| ≤ N`). `cont_core` takes `PerTimeDomAt`, `HighProbAt`, closeness and `ε ≤ ζ` as explicit hypotheses (as RBM2D `Continuity:147`).
* Imports: `Gauss.FlowCalculus`, `Gauss.Domination`, `Defs.StochDomAt`, `Green.EntryCore` (all merged), Mathlib; not `RBM3D`, no ST-2..6 file. No cycle.
* The pin is not `False`/vacuous: its premises are discharged at `sz0` (section 3), and the prover's uncommitted S1-34 scratch proves it against this file only:
```
$ cd RBM3D-wt/T2047-audit1 && lake env lean scratchpad/T2047/gop_scratch.lean   # import RBM3D.Induction.ContinuityNet only; 0 sorry/admit/native_decide/axiom
47:theorem gopbound {d : ℕ} (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : GopboundPin sz κ E := by
'RBM.Ind.gopbound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
* No external hypothesis is added; `GopboundPin` is assumed by no theorem here, so no registry line (`Test/Axioms.lean` untouched).

## 3. Compiled nonempty instances (file section 5, lines 811-1006; compiled by the build in 4)
* `GopboundPin sz0 (1/10) (fun _ => 1/2)` (`d = 3, L = 4, W = 32, N = 2^21`): `h (by norm_num) (fun _ => by norm_num) sz0_tendsto` — all three deterministic premises discharged; the pin itself (S1-34's `gopbound`) stays a hypothesis.
* `cont_core`: window `[0, 1/16]`, `V n = Idx 3 × Idx 3` (N² labels), `A = 4`, `Cv = 2`, `ε = 2N⁻¹`, `ξ = |H_u(i,j)|`, `ζ ≡ 1`, `Ξ = contGood`; `#V ≤ N^2`, `ε ≤ ζ` (eventually, `N ≥ 2`), closeness on `contGood` are proved; `HighProbAt` by `cont_highProbAt_good`. Only `PerTimeDomAt` (a stochastic premise; satisfiable: Gaussian entries of variance ≤ 1 against `N^τ`) stays.
* Every other public theorem is applied at `sz0`, `n = 0`, the all-ones sample `ω₁ ∈ contGood sz0 0`, `E = 1/2`, `t = 1/2`, `u = 1/4`, `u' = 1/8` or `3/8`, or a `Fin 4` matrix; no `N = 0`, empty index, collapsed window or `False` premise:
```
$ grep -cE '^example' ContinuityNet.lean
33
$ tail -n +811 ContinuityNet.lean > inst.txt; for n in <each ^theorem name>; do grep -qw $n inst.txt ...; done
public theorems applied in section 5: 32 of 32; missing: none
```

## 4. Build, axioms, hygiene, scope
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2047-audit1 && lake build RBM3D.Induction.ContinuityNet | grep -E 'error|warning|Built RBM3D.Induction.ContinuityNet|Build completed'
✔ [3306/3306] Built RBM3D.Induction.ContinuityNet (6.5s)
Build completed successfully (3306 jobs).
exit=0
$ lake env lean aud_axioms.lean   # import RBM3D.Induction.ContinuityNet; #print axioms for each of the 34 public names
exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" aud_axioms.out ; grep -v <that line> aud_axioms.out
34
(nothing)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' RBM3D/Induction/ContinuityNet.lean | wc -l
       0
$ lake build RBM3D | grep -E 'error|Build completed'
Build completed successfully (3770 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.ContinuityNet\n#assert_rbm_axioms\n' > aud_precheck.lean; lake env lean aud_precheck.lean; echo exit=$?
exit=0
axiom audit: 1799 theorems, 812 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 51 (borrowed 2, owed 35, structural 14).
$ git diff --name-status main...t/T2047
A	RBM3D/Induction/ContinuityNet.lean
$ name-clash scan: git grep -nwE "(theorem|def|lemma|abbrev) <name>" main -- 'RBM3D/*.lean' for the 34 public names
clash scan done (34 names, declarations on main a68a954)      # no hit
```
Only the sole writable file is touched (new); no frozen signature changed; the premise count (51) equals the base library's (report b.3).

## 5. Paper deltas
* `T2047a` (report (d)): the pin's readings inherited from RBM2D (`0 < κ →`, `1 - u ≥ N^{-1}`, "exponentially small" as `≤ N^{-D}` for all `D`) and the pin stated for every `d`. The absence of `Gopboundu` in the d ≥ 3 paper is signed D29 (T2015e; `docs/paper-deltas.md:271`).
* The cut part's other statements are deterministic/abstract lemmas with no paper counterpart, or renamings; the `Bctl` facts are true identities/bounds of the merged `Bctl` (no delta needed). Coverage complete.

## Observations (no RETURN)
* O1. The ticket asks the `scaleM`-type definitions (Continuity:621-634) to be "restated with N = (WL)^d"; they are dropped and replaced by `Bctl` lemmas. This follows ST1-COMMON item 2 (d = 2 scales become `Bctl`) and the merged `STStep1Loop`/`STStep1Weak` controls; it changes no pinned statement.
* O2. Report b.6 counts "identical after renaming: 34, differ: 1"; with the script above the residue is renaming-only too (1.2), so the conclusion stands.
* O3. The `cont_core` instance keeps `PerTimeDomAt` as a hypothesis; it is a stochastic premise of the theorem itself (not deterministic), so this meets CLAUDE.md §4 step 2.

## Verdict
* `GopboundPin`: **PASS**.
* Cut part (`cont_core`, good event, resolvent/flow moduli, spectral, `Eblk`, `Bctl` facts, bulk/gap; 32 theorems + `contGood`): **PASS**.
* Ticket T2047: **PASS**. No dispatcher sign-off needed.
