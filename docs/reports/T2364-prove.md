Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 02:13:27 UTC 2026

Scripts (mathematics only, no Lean) are in the scratchpad `T2364/`: `forest.py`, `inst.py`, `table.py`. Paper `7_8:N` = `paper/tex/7_8_light_weight.tex:N`.

### (i) Exponent table

**C5 (rooted forest, route (R); no snag).** `auxGraph_exists_forest` (`AuxGraph.lean:459`) picks the roots by `choose rootI hroot` (`:476`). Everything after only uses `T = {inl _} ∪ range rootI` and the identity `molOf (inr (rootI c)) = c.1`. This identity is used in two places: every vertex reaches `T` (`hreach`, `:478`), and `hroot` in `auxGraph_term_conf`. Take `rep` with `∀ c, molOf (inr (rep c)) = c.1` as a hypothesis. Then `rank`, `par`, `edge` (strictly smaller rank, hence an injective edge map), `hnT`, `hnT'` and the injectivity of the roots are unchanged. `auxGraph_main_sum` (`:901`) is already generic in `root` and calls `auxGraph_forest_roots` (`:551`) with an arbitrary nonnegative `Φ`. Put `Φ·1[∀c, blk(x c) ∈ Dm]` there; `auxGraph_sum_blocks` (`:663`) then gives `(W^d)^{nM} · Σ_{b ∈ piFinset Dm}` = `auxValOn`. The weight satisfies `|Wt| ≤ 1`, so `‖Σ Wt·term‖ ≤ Σ_{ℓi: roots in Dm} ‖term‖`. The pointwise bound `hpt` (`:1070-1085`) and the tail sum `auxGraph_tail_sum` (`:798`, sums over all `ℓi`) are unchanged. `LWAuxNestedOwnOn`: the proof of `auxGraph_val_eq` (`:1526`) is `Fintype.sum_equiv` along `Dt.e.arrowCongr`; this bijection maps `piFinset Dm` onto itself. Not mergeable as is: `auxGraph_exists_rank` (`:436`) is `private`, so G copies it.

| # | quantity | value / range | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `d`, `p` | `d ≥ 3` (instance 3); `p` even, `p ≥ 2` (instance 2) | `lwGtoAG` needs `3 ≤ d`; `lwProv_bridge` needs `Even p`; `p = 0` is degenerate | none |
| 2 | domains | `domFar`, `domNearA`, `domNearB`; `d=3, L=4, a=0, b=(2,0,0), ℓ=1`: `28 + 27 + 9` | partition of `Z_L^d` (`dom_union`, `dom_disj`): `64 = 4³` (`inst.py`) | exact identity |
| 3 | regime `¬regA K` | `\|a−b\|_∞ > K(log W)^{3/2}ℓ_t` and `ℓ > K(log W)^{3/2}ℓ_t` | `one_le_ellT` (`Params.lean:39`), `zdistInf ≤ zdistD = lwBdist` (`Sizes.lean:117`) give `lwBdist(x,y) > K(log W)^{3/2}` | `ℓ_t − 1 ≥ 0` |
| 4 | **K quantifier (C6)** | see finding F1: `K_card` depends on `(p, ⌈1/𝔠⌉, c_eng, D_eng)`, not on `p` alone | `LWMoment.lean:1799-1802`, `LWProv.lean:168-170` | literal "`∀ p, ∃ K` before `𝔠, sz, D`" is not closable; two closable readings below |
| 5a | reading (α′) (the ticket's (α) with `∃K` placed after `D`) | `K := max(1, K_card)`; `r = (log W)^{3/2}`, tail constant `c`; `R = K_card (log W)^{3/2}`; `ρ = 2R+1` | `K_card·r ≤ K(log W)^{3/2} < lwBdist`; `\|E⊕I\|·r ≤ R` | `R − \|E⊕I\|r ≥ 0` (0 at `\|E⊕I\| = K_card`) |
| 5b | reading (β) (supervisor 0143 C6 (β)) | any fixed `K > 0` (`K = 1` is the paper's regime); `r = K(log W)^{3/2}/K_card`; tail constant `c' = cK/K_card`; `R = K(log W)^{3/2}` | `lwTail32` has a free constant (`LWXiExp.lean:81`); pins keep the form `∀K>0` of probe 529-534 | same |
| 6 | far radius for G2 | `ρ = 2R+1`; `√ρ ≤ τ log N` eventually | `lwXiExpClaim_holds` hypothesis; at `K = 8`: `τ=0.5` from `log W ≥ 50.9`, `τ=0.1` from `3.18e4`, `τ=0.05` from `5.06e5` | asymptotic (`∀τ ∀ᶠ n`) |
| 7 | tail | `e^{-c r/2}N^{a} ≤ N^{-b}`, `a = nM+nV+1`, `b = D` (floor `R ≥ W^{-D} ≥ N^{-D}`) | `lwTail32`: eventually, from `log W ≥ (2(a+b)/(𝔠c))²` (`c=1, a=9, b=4`: `24336`) | asymptotic |
| 8 | near pin | `1 ≤ ℓ ≤ Λℓ_t`, `Λ = (log W)^{10}`; `g² ≤ L²(1−t)` | `AnpNearInfAt`; `LWAssmExp` gives `ℓ ≤ (log W)^{10}ℓ_t`; target has `<`, so the hypothesis holds strictly; `ℓ ≥ 1` from `¬regA` once `K(log W)^{3/2} ≥ 1` | strict; `Λ^{2q} = (log W)^{20q} ≤ N^τ` eventually (`q = nM ≤ p`) |
| 9 | `θ` | far: `θ = N^{2τ}(W^dη_t)^{-1}`; near: `Λ²(W^d)^{-1}/(1−t)` | `η_t = (1−t)·Im m ≤ 1−t` (`Loop/GLoop.lean:75`), so `(1−t)^{-1} ≤ η_t^{-1}` | direction correct, no `≍` needed |
| 10 | closure of exponents | `(W^d)^{nM}(W^dη)^{-nM} = η^{-nM} ≤ η^{-p}` (`nM ≤ p`, `η ≤ 1`); `𝖳0^{o−p} ≤ 𝖳0^{p}` (`o ≥ 2p`, `𝖳0 = sfT 0 ≤ 1`); `sfT0² ≤ Bctl` | `Bctl = W^{-d}B_{t,0} ≥ W^{-d}(g²+\|1−t\|)^{-1} = sfT0²`; the target prefactor `Bctl^{1/2}` is `≥ 𝖳0` | slacks `η^{p−nM}`, `𝖳0^{o−2p}`; `Bctl/sfT0² ≤ 3` in the regime (scan max `1.27`) |
| 11 | entry scale `Ψ'` | `Ψ' = N^{τ₁}·C·Φ_E(0)`, `Φ_E(0)² = W^{-d}tailW(0)`; `τ₁ = 𝔠𝔡/4`; `c_eng = 𝔡/2` | window `W^{-d/2} ≤ Ψ'` (`lwXE_window`, `LWXiExp.lean:244`); `Ψ' ≤ W^{-c_eng}`: `Φ_E(0)² ≤ 2W^{-d}g^{-2} ≤ 2W^{-2𝔡}` (`(eq:WO)`, `Sizes.lean:193`; `L^d(1−t) ≥ g²` in the regime) | `Ψ' ≲ W^{-3𝔡/4}` vs `W^{-𝔡/2}`: slack `W^{𝔡/4}` |
| 12 | engine `(c, K0, d, D)` | `c = c_eng`, `K0 = ⌈1/𝔠⌉`, `D_eng ≥ D + 1/𝔠` | errors: `K'·W^{-D_eng} ≤ W^{-D}` for `K' ≤ N ≤ W^{1/𝔠}` | `D_eng − D − 1/𝔠 ≥ 0` |
| 13 | `ξ` floor | G2 gives `ξ ≺ 𝖳 + W^{-D'}` | terms with a floor edge are `≤ 2^{\|E\|}N^q W^{-D'}`; need `D' ≥ D + (q+1)/𝔠` | free (`LWAssmExp` is `∀D`) |
| 14 | split | `3^{p-1}` (`norm_add3_pow_le`), `p` fixed | pointwise; integrability: `‖G‖ ≤ η⁻¹` (`lwMoment_norm_Gt_le`) + continuity in `ω` (`continuous_green_comp`) | constant factor |

**Findings (not named in the ticket; all provable from merged public lemmas).**
- **F1 (C6).** The engine list `outs ++ errs` is obtained after `(p, c, K0 = ⌈1/𝔠⌉, D)` (`LWEngineProv`, `lwMoment_holds` `:1799-1802`). Hence `K_card` cannot be chosen before `𝔠, sz, D`. A far or near pin stated at a K fixed before the data cannot be proved by this expansion when `K < K_card`: the `𝓜_x = 𝓜_y` outputs are then not tail-negligible (`lwScalemole` needs `\|E⊕I\|·r < lwBdist`). Both readings in rows 5a/5b close with the same exponents. I recommend 5b: it keeps the probe's pins verbatim and has no `∃K`. The dispatcher should confirm which reading the audit expects.
- **F2.** The weighted sums need twins of three merged statements about `‖Γ.val‖` (`‖valW‖ ≤ Σ|Wt|·‖term‖ ≤ Σ‖term‖`, with `|Wt| ≤ 1`):
  - `lwScalemole_holds` (the `𝓜_x = 𝓜_y` outputs);
  - `lwClaimSize` (the error lists);
  - the polynomial envelope of `lwMoment_env`.

  Their proofs go through `Σ‖term‖` via the public `auxGraph_term_tail`, `auxGraph_tail_sum`, `auxGraph_mol_dist`, `LGraph.term_norm_le`, `LGraph.waved_sum_le`; no weighted twin exists in merged code.
- **F3.** There is no merged exp-class entry bound (`‖G_t − M‖_max ≺ Φ_E(0)`, the exp analogue of `lwEntryPsi_holds`, `AuxGraph2.lean:1191`). `lwEntryPsi_holds` uses only `hΦ.2.1.1` and `hΦ.2.2.1`, so it applies to the constant class `Φ̃ n r := Φ_E n 0` (at `n` outside the regime, `Ψ n`). The loop hypothesis follows from `LWLoopExp` at `2D` and `tailW_antitone` (`Tail.lean:109`). Row 11 is the exponent bookkeeping.
- **F4.** Integrability of `‖LWfD‖^p`. `LWInteg` (`LWPins.lean:205`) is a premise with no proof in merged code; 1b must derive it from the bound and continuity of row 14.

### (ii) Concrete nondegenerate instance
`d = 3, p = 2`, merged data `auxGraph_instD` (`L=4, W=2`, `G = m(0)I + ½J`, `Ψ = ½`, `r = 1`, `R = 8`, `ξ ≡ ½`), `figGraph` (`E = Fin 2`, `I = Fin 6`, `nM = 2`, `\|𝒢_ℳ\| = 6`), nested instance `localReg2_inst_Q` (`nM = 1`, `\|𝒢_ℳ\| = 4`), pins `AnpFarAndAt 3 figAux` and `AnpNearInfAt 3 figAux` (merged, `LWMomExpFar.lean:417`, `LWMomExpInf.lean:589`), `Dm` = 8 points of `Z_4^3`, `rep c` = the roots of the molecules (`auxGraph_exists_forest` supplies them: `forest.py` confirms 20000 random graphs with arbitrary root choices).
```
$ python3 -I inst.py
domains |far|,|nearA|,|nearB| = 28 27 9 sum = 64 of 64 disjoint: True
figGraph: auxVal(full)=64.0  auxValOn(|Dm|=8)=1.0  |E+I|=8
localReg2_inst_Q: auxVal(full)=4.0  auxValOn(|Dm|=8)=0.5  |E+I|=4
window W^(-d/2) = 0.3535533905932738 <= Psi: True | card*r <= R: True | |G_xy|=1/2 <= xi=1/2: True | |G_xx-m|=1/2 <= Psi: True
$ python3 -I forest.py
20000 random graphs, arbitrary root choices: all asserts passed; internal molecules total 35155 non-root internal vertices 64225
```
The restriction is active (`1 < 64`, `0.5 < 4`); the weight `Wt = Π_c 1[blk ℓ(rep c) ∈ Dm]` is nonzero at labels with all root blocks in `Dm`, `|Wt| ≤ 1`. The hypotheses of `LWGtoAGRooted` are those of the merged `lwGtoAG` instance (`AuxGraph.lean:1740-1760`, instance 3) plus `rep` and `Wt`: `Γ.Normal`, `hext`, `0 ≤ C`, `0 < c` and the decay of `S, S^±` (`lwSpOf_decay_E`), `0 ≤ r`, `|E⊕I| r = 8 ≤ R = 8`, and the equality case `|G_xy| = ½ = ξ`.

The assembly at `d = 3, p = 2`: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `λ_n = (2(n+1))^{-6}`, `𝔠 = 1/6`, `𝔡 = 1/10`), `t ≡ 1/16`, and the near-critical `1−t = 2λ²/L²`. The stochastic pins (`LWInit`, `LWLoopExp`, `STFlow`) stay hypotheses; their deterministic parts are computed (limits, TEAM §8 lesson 14):
```
$ python3 -I table.py   (columns: n, W, L, lam | lam/W^(-d/2+dd) | W/N^c | ell_t, Bctl/sfT0^2, PhiE(0)/W^-dd at 1-t = 2 lam^2/L^2)
    0 W=3.200e+01 L=4    lam=1.56e-02 | 2     | 2.83    | ell_t=2.828 ratio=1.1406 PhiE0/W^-dd=0.503
   10 W=5.154e+06 L=44   lam=8.82e-09 | 22    | 342     | ell_t=31.11 ratio=1.0114 PhiE0/W^-dd=0.0457
 1000 W=3.216e+16 L=4004 lam=1.55e-20 | 2e+03 | 2.83e+06| ell_t=2831  ratio=1.0001 PhiE0/W^-dd=0.0005
regime check at t=1/16, n=0: lam^2/L^2 = 1.52587890625e-05 < 1-t = 0.9375
max Bctl/sfT0^2 over scan (<=3): 1.265625
first n with some |a-b|_inf <= L/2 above K (log W)^{3/2} ell_t, K=8: 922  L/2 = 1846  K(logW)^1.5 = 1844.7563337139068
(beta) r = 230.59454171423835  card*r = 1844.7563337139068 < dist > 1844.7563337139068 (strict from not-regA)
```
- `(eq:WO)`: `λ/W^{-d/2+𝔡} = 2(n+1) → ∞`. `W/N^𝔠 = (2(n+1))²/√2 → ∞` (column 3).
- The regime `¬regA 8` is nonempty from `n = 922` (`ℓ_t = 1` at `t = 1/16`; some `|a−b|_∞ ≤ 1846 > 1844.76`; `ℓ` with `1845 ≤ ℓ ≤ (log W)^{10}`).
- The `∀ᶠ` conclusions (rows 6, 7) are asymptotic; no finite witness of the conclusion is claimed, as for every merged `≺`.
- The index set of the target is nonempty: `λ²/L² < 1 − t` holds at both `t`.

### Verdicts
- **`AuxGraphRooted.lean` (`LWGtoAGRooted`, `LWAuxNestedOwnOn`, rooted forest, main sum): PASS.** C5 holds with no snag (route (R) stays). The private `auxGraph_exists_rank` is copied; the statements are the probe's.
- **`LWMomentExp.lean` (domains, `LWf_split`, pins, assembly, `lwMomentExp_holds`): PASS, with conditions.** Rows 1-14 close. Conditions for 1b: (1) F1, fix reading 5a or 5b; literal "`∃K` before the data" is not closable; (2) F2, F3, F4 are proofs 1b must supply, from the merged public lemmas named above, in `lwAuxRoot_`/`lwMomentExp_` private helpers; (3) the far-pin and near-pin forms other than the probe-verbatim `LWMomentExpOn`/`regA` are internal.
- **`Test/Axioms.lean` (delete the owed line `RBM.Gauss.Sizes.LWMomentExp`, `:155`): PASS** (registry edit; blocked by nothing).

## (b) Script output (evidence runs Sat Oct 10 05:38:29 to 05:49:15 UTC; branch tip 0b74a90; scripts in the scratchpad `T2364/r2/`)
### b1 Commits, scope, size (stop line 2100), builds, registry, axioms
```
tip: 0b74a90 (branch t/T2364); main: c0a7747; merge base: 010cad9
$ per commit on main..t/T2364: UTC commit time, wc -l of the two new files (git show <c>:<file>), lines of LWMomentExp.lean with lwMomentExp_perP / "∃ K", subject
9bb3736 02:33:17 UTC  645+   0= 645 perP=0 exK=0  T2364: AuxGraphRooted (rooted GtoAG, restricted nested v
8b53152 03:41:52 UTC  569+1509=2078 perP=0 exK=1  T2364: LWMomentExp (R3 = G + F): lwMomentExp_holds, far/
9bc3afc 03:51:16 UTC  569+1517=2086 perP=1 exK=2  T2364: file-stem prefix for the unpinned public helpers 
2350da3 04:10:41 UTC  569+1515=2084 perP=4 exK=5  T2364: assembly in form (alpha) of C6 (lwMomentExp_of_pa
9ca7389 04:14:29 UTC  569+1513=2082 perP=0 exK=1  T2364: restore form (beta) of C6 (Amend 1): assembly and
0b74a90 05:31:32 UTC  569+1509=2078 perP=0 exK=0  T2364: lwMomentExp_env private (no public existential ov
$ git diff --stat main...t/T2364; git status --short
RBM3D/Graph/AuxGraphRooted.lean |  569 +++++++++++++++
RBM3D/Graph/LWMomentExp.lean    | 1509 +++++++++++++++++++++++++++++++++++++++
RBM3D/Test/Axioms.lean          |    1 -
3 files changed, 2078 insertions(+), 1 deletion(-)
?? PEER-NOTE-T2364.txt
$ git diff --stat 9ca7389 HEAD; python3 -I trimcheck.py <file at 9ca7389> <tip file>   (9ca7389 = tip of the previous stage-1b run)
RBM3D/Graph/LWMomentExp.lean | 14 +++++---------
code tokens 20910 -> 20907, 6 non-equal blocks: insert `private`; `Kenv` -> `envExp` x2; `⟨Kenv,` -> `⟨envExp,`; `Kenv)` -> `envExp)`; delete `namespace RBM.Graph end RBM.Graph`
$ git diff main...t/T2364 -- RBM3D/Test/Axioms.lean | grep "^-[^-]"; git log --format=%h 010cad9..main -- RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-13b
commits on main since the merge base that touch RBM3D/Test/Axioms.lean: c0a7747 79dec34 0347cb8
$ lake build RBM3D.Graph.AuxGraphRooted RBM3D.Graph.LWMomentExp   (at the committed tip)
Sat Oct 10 05:38:37 UTC 2026
exit=0
Sat Oct 10 05:38:42 UTC 2026
Build completed successfully (3904 jobs).
warnings of the two files: 27 (AuxGraphRooted 13, LWMomentExp 14); errors: 0
$ lake env lean registry.lean   [import RBM3D; import RBM3D.Graph.AuxGraphRooted; import RBM3D.Graph.LWMomentExp; #assert_rbm_axioms]
Sat Oct 10 05:38:42 UTC 2026
exit=0
Sat Oct 10 05:40:23 UTC 2026
axiom audit: 10775 theorems, 3161 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 132 (borrowed 1, owed 70, structural 42, refuted 6, superseded 13).
occurrences of LWMomentExp in the whole output: 0
$ grep -n LWMomentExp RBM3D/Test/Axioms.lean   [main / branch]
main:   156:   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-13b
branch: 
$ lake build   [RBM3D.lean + the two imports after the last import line; temporary, restored after]
RBM3D.lean | 2 ++
1 file changed, 2 insertions(+)
Sat Oct 10 05:40:24 UTC 2026
exit=0
Sat Oct 10 05:40:30 UTC 2026
RBM3D.lean restored: git status --short:
?? PEER-NOTE-T2364.txt
4212:info: RBM3D.lean:411:0: axiom audit: 10775 theorems, 3161 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
4344:premises found by scanning: 132 (borrowed 1, owed 70, structural 42, refuted 6, superseded 13).
4470:Build completed successfully (4179 jobs).
$ lake env lean axall.lean   [one #print axioms per public declaration of the two files: 59 lines]
Sat Oct 10 05:40:30 UTC 2026
exit=0
lines: 59; exactly [propext, Classical.choice, Quot.sound]: 59; other lines: 0
'RBM.Graph.lwGtoAGRooted_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAuxNestedOwnOn_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWf_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_farPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_nearPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwMomentExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomentExp_inst_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b2 Target statements, extracted from the files by script (`file:line`)
```
$ python3 -I stmt.py <file> NAME:body|sig ...   (run Sat Oct 10 05:40:42 UTC)
AuxGraphRooted.lean:225: def LWGtoAGRooted (d : ℕ) : Prop :=
      3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
        (Γ : LGraph E I), Γ.Normal → (∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b) →
        ∀ (rep : LGraph.AuxIMol Γ → I), (∀ c, Γ.molOf (Sum.inr (rep c)) = c.1) →
        ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ) (Dm : Finset (Zd d L)),
          (∀ x y, D.M x y = if x = y then m else 0) →
          (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) → 0 ≤ C → 0 < c →
          (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
          (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
          (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → 0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
          (∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y → (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
            (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y‖ ≤ ξ a b) →
          ∀ (Wt : (E ⊕ I → Idx d L W) → ℝ), (∀ ℓ, |Wt ℓ| ≤ 1) →
            (∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (split d L W (ℓ (Sum.inr (rep c)))).1 ∈ Dm) → ∀ ℓe : E → Idx d L W,
              ‖valW Γ D Wt ℓe‖ ≤
                Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - LGraph.auxOrd Γ) *
                    (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm) +
                  Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L
AuxGraphRooted.lean:449: def LWAuxNestedOwnOn : Prop :=
      ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
        Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
        ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
          ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
            ∀ Dm : Finset κ, Γa.valOn ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1))
              (Fintype.piFinset fun _ : Fin Q.g.nM => Dm) = auxValOn Q.g ξ be Dm
AuxGraphRooted.lean:244: theorem lwGtoAGRooted_holds (d : ℕ) : LWGtoAGRooted d
AuxGraphRooted.lean:457: theorem lwAuxNestedOwnOn_holds : LWAuxNestedOwnOn
LWMomentExp.lean:99: def LWMomExpFarPin (d : ℕ) (K : ℝ) : Prop :=
      LWMomentExpOn d (fun L _ a b ℓ => domFar d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q
LWMomentExp.lean:102: def LWMomExpNearPin (d : ℕ) (K : ℝ) : Prop :=
      LWMomentExpOn d (fun L _ a _ ℓ => domNearA d L a ℓ) (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q) ∧
        LWMomentExpOn d (fun L _ a b ℓ => domNearB d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q
LWMomentExp.lean:106: def LWMomentExpOfParts (d : ℕ) : Prop :=
      ∀ K : ℝ, 0 < K → LWMomExpNoExpF d K → LWMomExpFarPin d K → LWMomExpNearPin d K → RBM.Gauss.Sizes.LWMomentExp d
LWMomentExp.lean:179: theorem lwMomentExp_of_parts (d : ℕ) : LWMomentExpOfParts d
LWMomentExp.lean:1422: theorem lwMomentExp_farPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : LWMomExpFarPin d K
LWMomentExp.lean:1426: theorem lwMomentExp_nearPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : LWMomExpNearPin d K
LWMomentExp.lean:1436: theorem lwMomentExp_holds : ∀ d : ℕ, LWMomentExp d
```
### b3 Probe diff, name clash, hygiene, Amend 1, compiled nonempty instances (compiled by the module build of b1)
```
$ python3 -I verb.py probe.lean <files>   (probe = git show t/T2348:RBM3D/Probe/T2348Pins.lean; statement text up to :=, comments stripped, whitespace normalised)
auxValOn=True in AuxGraphRooted.lean; LWGtoAGRooted=True in AuxGraphRooted.lean; LWAuxNestedOwnOn=True in AuxGraphRooted.lean; domFar=True in LWMomentExp.lean;
  domNearA=True in LWMomentExp.lean; domNearB=True in LWMomentExp.lean; domFar_eq=True in LWMomentExp.lean; dom_union=True in LWMomentExp.lean; dom_disj=True in LWMomentExp.lean;
  LWf_split=True in LWMomentExp.lean; norm_add3_pow_le=True in LWMomentExp.lean; LWMomentExpOn=True in LWMomentExp.lean; regA=True in LWMomentExpA.lean;
  LWMomExpFarPin=True in LWMomentExp.lean; LWMomExpNearPin=True in LWMomentExp.lean
$ python3 -I names2.py main   (grep -w every new name, public and private, over the worktree and over main; outside the two files and Probe/)
public: 59  private: 15
public names neither pinned in the ticket nor prefixed lwAuxRoot_/lwMomentExp_: ['lwGtoAGRooted_holds', 'lwAuxNestedOwnOn_holds']
worktree: hits outside the two files and Probe/ (public+private names): 0
main: hits (public+private names): 0
names with hits: []
$ grep -nE "sorry|admit|native_decide|axiom " both files | wc -l
0
$ grep -n "∃ K" both files; grep -n "lwMomentExp_perP" both files
(no match)
(no match)
$ grep -n "^private theorem lwMomentExp_env\|∃ envExp"
861:private theorem lwMomentExp_env (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₁ C₁ C₂ C₃ Cc Ψ Φ) (Q : PGraph 
862:    ∃ envExp : ℝ, ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ)
$ grep -c "RBM1D\|RBM2D" both files; grep -c PEER-NOTE in git ls-files
RBM3D/Graph/AuxGraphRooted.lean:0 RBM3D/Graph/LWMomentExp.lean:0 
0
$ upstream use (grep -c: LWMomentExp.lean / AuxGraphRooted.lean)
lw_localregularXP 2/0; lwProv_locStepXProvPos_holds 0/0; lwMomExpFar_and 4/0; lwMomExp_nearInf 4/0; lwXiExpClaim_holds 3/0; lwGbyXi_holds 1/0; lwGtoAGRooted_holds 1/3;
  lwAuxNestedOwnOn_holds 1/3; lwMomExpNoExp_holds 2/0; lwExpTerm_prec_integral 1/0; lwTail32 3/0
$ the far radius r = (K/Kc)(log W)^{3/2}, the tail constant c K/Kc, R = K (log W)^{3/2}, Kc >= |E+I| of the engine list (Amend 1, reading 5b)
1059:  set Rr : ℕ → ℝ := fun n => K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hRr
1083:    lwTail32 sz h𝔠 (mul_pos hc (div_pos hK hKc)) hsz hband ((o.Q.g.nM + o.Q.g.nV + 1 : ℕ) : ℝ) D,
1158:  have hr0 : 0 ≤ K / Kc * L32 := mul_nonneg (div_nonneg hK.le hKc.le) (Real.rpow_nonneg (hlog n) _)
1327:  set Kc : ℝ := (Kn : ℝ) + 1 with hKc
1357:      · have hs := lwMomentExp_prec_scale H hd0 hD (V := V) (Krad := K / Kc) (div_pos hK hKc0) (fun n v => v.1) dom o hQ hmol
$ locations of the ticket targets (grep -n of the declaration line)
AuxGraphRooted:24 auxValOn; AuxGraphRooted:62 lwAuxRoot_exists_forest; AuxGraphRooted:136 lwAuxRoot_main_sum; AuxGraphRooted:225 LWGtoAGRooted; AuxGraphRooted:244 lwGtoAGRooted_holds;
  AuxGraphRooted:449 LWAuxNestedOwnOn; AuxGraphRooted:457 lwAuxNestedOwnOn_holds
LWMomentExp:32 domFar; LWMomentExp:35 domNearA; LWMomentExp:38 domNearB; LWMomentExp:48 dom_union; LWMomentExp:57 dom_disj; LWMomentExp:42 domFar_eq; LWMomentExp:68 LWf_split;
  LWMomentExp:76 norm_add3_pow_le; LWMomentExp:86 LWMomentExpOn; LWMomentExp:99 LWMomExpFarPin; LWMomentExp:102 LWMomExpNearPin; LWMomentExp:106 LWMomentExpOfParts;
  LWMomentExp:179 lwMomentExp_of_parts; LWMomentExp:1302 lwMomentExp_pin_gen; LWMomentExp:1422 lwMomentExp_farPin_holds; LWMomentExp:1426 lwMomentExp_nearPin_holds;
  LWMomentExp:1436 lwMomentExp_holds
LWMomentExpA:49 regA (merged, not redefined: 0 definitions in LWMomentExp.lean)
$ uses of hK in the proof of lwMomentExp_of_parts (lines 179-238 of LWMomentExp.lean)
1
$ grep -c sorry in the build logs of this stage: build of the working tree (compiled), tip re-run, full build
0 0 0
AuxGraphRooted:509: example : ∃ (rep : LGraph.AuxIMol figGraph → Fin 6) (Wt : (Fin 2 ⊕ Fin 6 → Idx 3 4 2) → ℝ) (C c : ℝ), 0 < C ∧ 0 < c ∧
    (∀ c, figGraph.molOf (Sum.inr (rep c)) = c.1) ∧ (∃ ℓ, Wt ℓ = 1) ∧ (∃ ℓ, Wt ℓ = 0) ∧
    auxValOn figGraph (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1) ({0, Pi.single 0 1} : Finset (Zd 3 4)) = 1 / 16 ∧
    ‖valW figGraph auxGraph_instD Wt lwSizeEll‖ ≤
    figGraph.sizeConst C (C * expC (3 - 2) c) * (1 / 2 : ℝ) ^ (figGraph.scalingOrder - figGraph.auxOrd) *
    ((((2 : ℕ) : ℝ) ^ 3) ^ figGraph.nM *
    auxValOn figGraph (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1)
    ({0, Pi.single 0 1} : Finset (Zd 3 4))) +
    Real.exp (-(c * 1 / 2)) * figGraph.sizeConst C (C * expC (3 - 2) (c / 2)) * figGraph.scalingSize (1 / 2) 2 3 4 := by
AuxGraphRooted:554: example : ∃ Γa : NGraph 2 localReg2_inst_Q.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧ Γa.ordN = 2 ∧
    Γa.valOn (fun _ _ => (1 / 2 : ℝ)) (fun _ => (0 : Zd 3 4)) (fun _ => 0)
    (Fintype.piFinset fun _ : Fin localReg2_inst_Q.nM => ({0, Pi.single 0 1} : Finset (Zd 3 4))) = 1 / 8 := by
LWMomentExp:1447: theorem lwMomentExp_inst_nonempty :
    Nonempty {q : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0) //
    sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 < 1 - tInst 0 ∧ ¬ regA 3 (1 / 100) sz0 0 (tInst 0) (ℓT tInst 0) q} := by
LWMomentExp:1475: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
    RBM.Gauss.Sizes.lwMomentExp_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2) (1 / 6) sz0 z0
LWMomentExp:1478: example (n : ℕ) : Nonempty {_q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
    sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n} := ⟨⟨(0, 0), strict_all n⟩⟩
LWMomentExp:1481: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
    lwMomentExp_farPin_holds 3 (K := 1 / 100) (by norm_num) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2)
LWMomentExp:1485: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
    (lwMomentExp_nearPin_holds 3 (K := 1 / 100) (by norm_num)).1 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2
LWMomentExp:1488: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
    (lwMomentExp_nearPin_holds 3 (K := 1 / 100) (by norm_num)).2 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2
LWMomentExp:1492: example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
    lwMomentExp_of_parts 3 (1 / 100) (by norm_num) (lwMomExpNoExp_holds 3 (1 / 100) (by norm_num)) (lwMomentExp_farPin_holds 3 (by norm_num))
LWMomentExp examples at lines 1497, 1502, 1503, 1504, 1505, 1506 (domains nonempty, dom_union, dom_disj, domFar_eq, LWf_split, norm_add3_pow_le)
$ lines applying the G targets inside the examples
548:  · have hmain := lwGtoAGRooted_holds 3 le_rfl 4 2 figGraph (by decide) auxGraph_figGraph_hext rep hrep auxGraph_instD (mE 0)
557:  obtain ⟨Γa, h1, h2, h3, h4, h5⟩ := lwAuxNestedOwnOn_holds 2 localReg2_inst_Q.pack (by norm_num)
```
### Narrative
- Claim check (hub message: every target delivered in form (beta), both modules and the full build at exit 0). It holds at the final tip `0b74a90`, re-checked against the ticket and Amend 1. Targets: every ticket target is a declaration of the three sole writable files (b3 locations); the `Test/Axioms.lean` change is the one deleted owed line (b1); the probe statements are identical, whitespace and comments aside, and `regA` is the merged definition, not redefined (b3).
- Amend 1: both pins and `lwMomentExp_of_parts` hold for every `K > 0` (b2); the far tail radius is `r = (K/Kc)(log W)^{3/2}` with tail constant `c K/Kc` and `R = K (log W)^{3/2}`, `Kc` bounding `|E + I|` of the engine list (b3: `LWMomentExp.lean` lines 1083, 1158, 1327, 1357); the string `∃ K` occurs in neither file (b3). Builds, registry pre-check and full build exit 0 (b1).
- Rule 0243 L1: the engine list comes from `lw_localregularXP` (2 mentions in `LWMomentExp.lean`, the call is at line 1325); `lwProv_locStepXProvPos_holds` has 0 mentions in both files (b3).
- This stage changed one file in one commit, `0b74a90` (token diff in b1). The uncommitted edit (`lwMomentExp_env` made `private`) is kept: the module builds with it (b1) and rule E allows it (the ticket does not pin the lemma). On top of it, the bound variable `Kenv` of that lemma is renamed `envExp`, so that no `∃ K` string remains, and an empty `namespace RBM.Graph ... end RBM.Graph` block is removed. `PEER-NOTE-T2364.txt` stays untracked and is not committed (b1 status; `git ls-files` count in b3).
- Two stage-1b sessions wrote in this worktree. `PEER-NOTE-T2364.txt` lines 3-4 and 73 (the note does not name its model) say that one session committed `9bb3736` and `9ca7389` and that `LWMomentExp.lean` appeared at 02:41 UTC without that session having written it. The perP and exK columns of b1 show the form-(alpha) material in `9bc3afc` and `2350da3` (lines with `lwMomentExp_perP` and `∃ K`) and none at the tip; the subjects of `2350da3` and `9ca7389` name forms (alpha) and (beta); note lines 64-73 give the reason. Note lines 84-86 announce a `PRIVATE DONE` line, which never appears.
- G (`AuxGraphRooted.lean`): `lwAuxRoot_exists_forest` takes the roots `rep` as a hypothesis (C5, no snag); `lwAuxRoot_exists_rank` is a private copy of the private `auxGraph_exists_rank` (section (a)). F (`LWMomentExp.lean`): `lwMomentExp_pin_gen` expands `E|f^D|^p` by the weighted expansion `lwMomentExp_expand`, bounds the three kinds of outputs (errors, `M_x = M_y`, `M_x != M_y`) and sums over `outs ++ errs`; the far pin uses `lwMomExpFar_and`, the near pins `lwMomExp_nearInf`, the exponential class `lwXiExpClaim_holds` and `lwGbyXi_holds`; `LWfD ... univ = LWf` is `h0` in `LWf_split`.
- Instances (b3): G at `d = 3`, `L = 4`, `W = 2` with `figGraph`: `Dm` has 2 of the 64 points, `Wt` takes the values 1 and 0, restricted main term `1/16`. F at `d = 3`, `p = 2`, `sz0`: the target `lwMomentExp_holds 3`, the assembly and the pins at `K = 1/100`; the only hypotheses of these examples are `LWInit` and `LWLoopExp` (other gates' stochastic pins); the index set is nonempty at every `n` for the target and at `n = 0` for the pins (`lwMomentExp_inst_nonempty`).
- Sections (b)-(d) are rewritten from this stage's output at the final tip; the text for tip `9ca7389` is not kept. Section (a) is unchanged.
- The first run of the full `lake build` at the tip (tool log: 05:33:22 to 05:34:13 UTC, exit 0, 4179 jobs) had the temporary imports in `RBM3D.lean`; a repeat run is in b1 (05:40:24 to 05:40:30, exit 0). No port from RBM1D or RBM2D: neither name occurs in the two files (b3).
## (c) Verified Mathlib names (`#check @name`, chk_all.lean, run Sat Oct 10 05:41:54 UTC; groups by newnames.py, run Sat Oct 10 05:50:07 UTC 2026; instance arguments omitted)
```
$ python3 -I newnames.py chk_all.out   (a name counts as used elsewhere if another RBM3D file outside Probe/ contains its last two components or its last one)
names #checked: 25 (the last, Real.log_two_pos, is a verified-absent name); used by the new files and by no other RBM3D file: 7; by one other file: 3; by more: 13; exist, not used: ['Finset.prod_le_one']
```
- Equiv.coe_refl : ∀ {α : Sort u_1}, ⇑(Equiv.refl α) = id
- Int.eq_nat_or_neg : ∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
- Int.natAbs_natCast : ∀ (n : ℕ), (↑n).natAbs = n
- Int.natAbs_neg : ∀ (a : ℤ), (-a).natAbs = a.natAbs
- Nat.cast_le_one : ∀ {α : Type u_1} {n : ℕ}, ↑n ≤ 1 ↔ n ≤ 1
- Real.self_le_rpow_of_one_le : ∀ {x y : ℝ}, 1 ≤ x → 1 ≤ y → x ≤ x ^ y
- zpow_neg : ∀ {α : Type u_1} (a : α) (n : ℤ), a ^ (-n) = (a ^ n)⁻¹
- Finset.prod_ne_zero_iff : ∀ {ι : Type u_1} {M₀ : Type u_2} {f : ι → M₀} {s : Finset ι}, ∏ x ∈ s, f x ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0
- Int.toNat_of_nonneg : ∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
- pow_sum_le_card_mul_sum_pow : ∀ {ι : Type u_1} {α : Type u_2} {s : Finset ι} {f : ι → α}, (∀ i ∈ s, 0 ≤ f i) → ∀ (n : ℕ), (∑ i ∈ s, f i) ^ (n + 1) ≤ ↑s.card ^ n * ∑ i ∈ s, f i ^ (n + 1)
- also `#check`ed, used in other merged files (signatures in chk_all.out): Finset.prod_le_one₀, MeasureTheory.Integrable.of_bound, MeasureTheory.integral_mono_of_nonneg, Finset.sum_ite_mem, Fintype.card_piFinset, Real.rpow_add_one, Real.le_log_iff_exp_le, Finset.measurable_sum, Real.rpow_le_rpow_of_nonpos, Measurable.pow_const, Measurable.norm, Real.log_two_lt_d9, Real.log_two_gt_d9
- ABSENT: `Real.log_two_pos` (`#check`: Unknown constant `Real.log_two_pos`, chk_all.out)
- `Finset.prod_le_one` exists (needs `[CommMonoid N] [MulLeftMono N]`, hypothesis only `f i ≤ 1`): not used; `Finset.prod_le_one₀` is.
## (d) Open issues and paper-delta candidates
- Observations (no statement, instance, axiom or paper-delta coverage is affected): (i) `lake build` prints 27 style-linter warnings for the two files and no error (b1): `set_option` lines merged on one line, long lines, no comment on `set_option maxHeartbeats 3200000 in` (`LWMomentExp.lean:1029`, before `lwMomentExp_prec_anp`; 13 other files of `RBM3D/` set `maxHeartbeats`); (ii) `hK : 0 < K` of `lwMomentExp_of_parts` is not used in its proof (b3: one occurrence in lines 179-238), kept for the `∀ K > 0` shape of Amend 1; (iii) `LWMomentExpOfParts` differs from probe 536-538 by `0 < K →` and by `LWMomExpNoExpF` (merged (A), ticket §162 (2)) in place of the probe-local `LWMomExpNoExp`; (iv) the F examples keep `LWInit` and `LWLoopExp` as hypotheses.
- Merge note for the hub: `RBM3D/Test/Axioms.lean` was changed on `main` after the merge base by the commits listed at the end of b1 (c0a7747, 79dec34, 0347cb8). Apply the one deleted line (`RBM.Gauss.Sizes.LWMomentExp`, b1) as a three-way merge of that hunk (cf. H23 (b)); do not copy the branch's version of the file over `main`'s. A trial `git merge-tree --write-tree --name-only main t/T2364` (tool log, 05:51:31 UTC) printed only a tree id (`e5d0548`) and no conflict line.
- Paper-delta candidates:
  - T2364a, scale `K`: the paper fixes `K = 1` (`7_8:1602-1605`); Lean states the pins and the assembly for every `K > 0` (probe `regA d K`) and applies them at `K = 1` in `lwMomentExp_holds`.
  - T2364b, cut of `Z_L^d`: the paper splits `f` into `f^{>ℓ}` and `f^{≤ℓ}` (`7_8:1606-1612`; domains `D_{>ℓ}`, `D_{≤ℓ}` at `7_8:1633`, `1648`; `∨` is the maximum, `1_2_Intro_model_result.tex:218`); Lean splits it into three exact parts `domFar`, `domNearA`, `domNearB` (probe 248-320, pinned; `LWf_split`, `dom_union`, `dom_disj`); `domFar` asks both distances `> ℓ`, `D_{>ℓ}` asks the maximum `> ℓ`.
  - T2364c, rooted weighted `GtoAG`: lemma `GtoAG` (`7_8:907`) bounds the full sum `Γ_{μ,xy}` with a centre chosen in each internal molecule (`7_8:860`); `LWGtoAGRooted` takes the roots `rep`, a weight `Wt` with `|Wt| ≤ 1` and the restricted value `auxValOn` (probe 197-224, pinned), which encode the domain restriction of `7_8:1633`, `1648`.
