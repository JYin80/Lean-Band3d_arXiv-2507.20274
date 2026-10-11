Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct 11 10:47:13 UTC 2026

Targets restated as far as needed (probe `t/T2413:RBM3D/Probe/T2413Pins.lean` @76c586e, §1; math source `docs/tickets/T2398-TL-proofs.md` A.2, T.1-T.3). Notation: `W^{-d}`-normalised block traces, `twLoopX X1 X2 a c1 c2 = W^{-2d} Σ_{x∈[a]} Σ_{w∈[c1]} X2[x,w] X1[(c2,o_w),x]`, `twSq X b a = W^{-2d} Σ_{y∈[b],x∈[a]} |X[y,x]|²`.

### (i) Exponent table
| # | quantity (target) | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `twFold` constant (T.2, B.2) | 1 (Cauchy-Schwarz over pairs `(x,w)`; `w ↦ (c2,o_w)` is a bijection `[c1]→[c2]`, so `Σ|X1[(c2,o_w),x]|² = W^{2d} twSq X1 c2 a`) | `|twLoopX|² ≤ twSq X1 c2 a · twSq X2 a c1`, `W^{-4d}·W^{2d}·W^{2d} = 1` | none lost; sharp (CS); random test max ratio 0.074 |
| 2 | `twWard` factor (T.3) | `(2i W^d η)⁻¹`; `Σ_a E_a = W^{-d}`, `Σ_a twLoopX(G,G*) = W^{-2d} Σ_{w∈[c1]} (GG*)[(c2,o_w),w]` | `η ≠ 0`, both resolvent identities (2.53); `σ=true` uses `GG*`, `σ=false` uses `G*G` | exact identity, residual 1.6e-16 |
| 3 | `twCirc` (A.2) | `Σ_{w∈[c1]} M[x,w] = MB[a,c1]` per `x∈[a]` (one `w=(c1,o_x)`), `shift c2 w = shift c2 x` | tie `M w γ = 1[o_w=o_γ] MB[[w],[γ]]` | exact identity, residual 2.2e-18, subtracted term 7.1e-3 ≠ 0 |
| 4 | `twK_bound` (ii) constant `C_ii` | 1: `Σ_a|Θ^σ(a,a')| ≤ Σ_aΘ^{(+,-)}(a,a') = (1-t)⁻¹` (BATheta_row_sum_pm; `|M^{(σ)}_{ab}| = |M_ab|²` as `M` is complex symmetric), `Σ_{a'}|M_{c2a'}||M_{a'c1}| ≤ 1` (CS, `Σ_b|M_ab|²=1`), `(W^dη)⁻¹ = W^{-d}(1-t)⁻¹/Im m_F` | `Im m_F ≤ 1` (`BAself_im_le_one`, `CouplingWindow.lean:328`, `Im z = 0`) | sz0 datum: max `C_ii` = 0.9995 ≤ 1; with `L=4`, g up to 1e6: ≤ 0.9995 |
| 5 | `twK_bound` (i) constant `C_i` | `C_P5(d,𝔡⁻¹,κ)·C_M(d,𝔡⁻¹,κ)·(κ+1)/κ`: `|Θ(a,a')| ≤ C_P5 B_{t,0}(g0)` (`BAProp5` `FlowPins.lean:173`, `B_{t,K}` decreasing in `K`), `Σ_{a'}|M_{c2a'}||M_{a'c1}| ≤ max|M|·C_M`, `B(g0) ≤ ((κ+1)/κ) B(g)` (`KBound_B_le`, `KBound.lean:160`) | `0<g0≤Λ=𝔡⁻¹` **at the index n** | sz0 n=0: max `C_i` = 0.984 (c1=c2), 0.013 (c1≠c2); constants in `(d,κ,ε,𝔡)` only, no `g` smallness |
| 6 | `t0` window | `t ≤ T0 = Im m/(Im m+Im z) < 1`, `T0 ≥ κ/(κ+1)` (`KBound_t0_ge`, `KBound.lean:143`) | `t<1` for `Θ`; `g² ≤ ((κ+1)/κ) g0²` | sz0 n=0: `T0=0.6937 ≥ 1/3`; `1-T0 = 0.3063`; `g²=2.44e-4 ≤ 5.08e-4` |
| 7 | `κ`, `Im m_F` | `κ ≤ Im m_F ≤ 1` (`BAflow_real`, `GreenSchur.lean:59`; `≤ 1`: row 4) | `κ>0` datum | sz0: `Im m_F = 0.9995 ≥ 1/2`; slack 0.4995 |
| 8 | **g-window at index n** (`WO`, `BAFlow`) | `Sizes.WO 𝔡` is `∀ᶠ n` (`Defs/Sizes.lean:164`), `Admissible` uses it (`:177`), `BAFlow = Admissible ∧ ∀ n BAdom` (`FlowPins.lean:389`); `BAflow_lam0_window` is `∀ᶠ` (`GreenSchur.lean:72`); `BAProp5`, `BAMB_row_l1` need `0<g≤Λ` (`FlowPins.lean:173-179`, `GreenSchur.lean:139-141`) | `twK_bound` as pinned quantifies **every** `n` (`∀ n σ c1 c2`, probe :119) with `C` before `sz,z` | **negative**: for `n` below the eventual threshold `g0_n` is unconstrained (table B below: `L=4`, `g` up to 1e6, `z_S = 6i/5 - m_S` satisfy `Im m_S ≥ κ=0.2604`, `Im z_S = 6/5 - Im m_S ≤ 1`; `C_i` = 18.2 there, ≤ `L^d`=64) |

Proof plan (sources only): `twFold` = CS as row 1 (T.2, TP:`Lemma T.2`); `twWard` = row 2 (T.3); `twCirc` = row 3 (A.2 "Relation circled/uncircled"); `twK_bound` = T.1 (i) without the exponential factor, plus (ii) = rows 4-5 (T.1 proof of (i), (ii), TP). Row 8: for a proof at all `n` one needs either (a) the new statement `L ≥ L0(κ,d) ⇒ g ≤ Λ(κ,d)` for `BAReal` data (density of states of `Ψ`: from `1 = L^{-d} Σ_k |gλ_k-E-m|⁻²`, `Im m ≥ κ`; not in the repository, not in the ticket) and, for `L<L0`, the crude bound `|K̃| ≤ W^{-d}(1-t)⁻¹ ≤ L0^d W^{-d}B_{t,0}`; or (b) the quantifier `∀ᶠ n in atTop` (as every merged stage-K pin, `BAKbound_of_uniform`, `KBound.lean:213-223`, uses `filter_upwards [BAflow_lam0_window …]`).

### (ii) One concrete nondegenerate instance
Targets 1-3 at `d=3, L=3, W=2` (`N=216`, 27 blocks, 8 offsets), `c1=0 ≠ c2=1`, `H = gΨ⊗I + V` (random Hermitian `V`, `g=0.7`), `z = 0.3+0.2i`, `G=(H-z)⁻¹`, `MB = (gΨ-E-m)⁻¹` with `m` solving `(self_m)`. Target 4 at the repository datum `sz0, n=0` (`L=4, W=32, g=1/64`, `z_S = w - m_S`, `w=6i/5`; `κ=1/2, ε=𝔡=1/10, 𝔠=1/6`; `flow_sz0`, `FlowPins.lean:1214`), `g0=√T0·g`, `E_n=BAflowE`, `m_F = m_S/√T0`, `t ∈ {0,1/2,2/3} ≤ T0`, all four charges, `c2=(1,0,0) ≠ c1=0` and `c1=c2`.
Command: `python3 inst.py; python3 m.py; python3 gwin.py > all.out` (scratch `T2421/`); output:
```
twFold: max LHS/RHS over 40 random (X1,X2,a,c1,c2) = 0.0744  (must be <=1)
twFold at G,G*, c1=0 c2=1 a=5: |LHS|=1.7549e-06 RHS=5.6917e-05 ratio=0.0308
twWard hypotheses: eta=0.2 !=0; max|G-G*-2i eta G G*|=6.64e-15; max|G-G*-2i eta G* G|=6.91e-15
 sigma=True: LHS=(-0.014237-0.001152j) RHS=(-0.014237-0.001152j) |diff|=1.59e-16  |LHS|=1.428e-02 (nonzero)
 sigma=False: LHS=(-0.014237-0.001152j) RHS=(-0.014237-0.001152j) |diff|=3.83e-16  |LHS|=1.428e-02 (nonzero)
BASelf at (g,E)=(0.7,0.3): m=(-0.146702+0.688895j), residual |m-avg|=4.7e-16, Im m=0.6889
twCirc: max_a |LHS-RHS| =2.17e-18 ; the subtracted term |W^-d MB[a,c1] twTrP|(a=0)=7.109e-03 (nonzero)

--- twK_bound at sz0 n=0 (FlowPins.lean:1181, Sizes.lean:260; wI=6i/5, MFixedPoint.lean:849) ---
n=0: Im mS=0.832488 Im zS=0.367512 t0=0.693740 (need >=2/3, Lean t0_sz0) g0=0.013014 E=1.04e-18 mF=0.999493j
     Im mF=0.9995 >= kappa=1/2: True ; self-consistency residual |mF-avg|=1.1e-16 ; Im mF<=1: True
     sum_b|M_0b|^2=1.000000000000 (=1, (8.4)); max|M_ab|=0.9995 (<=1); |M-M^T|max=1.0e-17 (symmetric)
     comparison g^2 <= ((kappa+1)/kappa) g0^2: 2.441e-04 <= 5.081e-04 ; t0 >= kappa/(kappa+1)=1/3: True
     B(g0)/B(g) at t=1/2: 1.0001 (<= (kappa+1)/kappa = 3)
t      c2!=c1  max over 4 charges: C_i=max|K|/(W^-d B_t0(g))  C_ii=sum|K|/(W^d eta)^-1   max|Theta^s|/Theta^(+-)
0.000  False   0.9839                                             0.9995                    1.0000
0.000  True    0.0128                                             0.0260                    1.0000
0.500  False   0.9831                                             0.9995                    1.0000
0.500  True    0.0128                                             0.0260                    1.0000
0.667  False   0.9823                                             0.9995                    1.0000
0.667  True    0.0128                                             0.0260                    1.0000
sz0 n=0: C_M=max_a sum_b|M_ab|=1.0828 ; max_{c1,c2} sum_a'|M_c2a'||M_a'c1| = 1.0000 (<=1 by CS and sum_b|M_ab|^2=1); 1-T0=0.3063; kappa/(kappa+1)=0.3333 <= t0=0.6937
A. Im m_S(L,g) = Im L^-3 tr (g Psi - 6i/5)^-1 (the repo's zS construction, MFixedPoint.lean:864-868), z_S=w-m_S, kappa:=Im m_S, t0=Im m_S/(6/5)
   L   g=1/64   g=1     g=10     g=1e2    g=1e4    g=1e6
   3  0.8325  0.4312  0.3711  0.3704  0.3704  0.3704
   4  0.8325  0.3777  0.2620  0.2604  0.2604  0.2604
   6  0.8325  0.3370  0.0976  0.0926  0.0926  0.0926
   8  0.8325  0.3464  0.1168  0.1107  0.1107  0.1107
  12  0.8325  0.3437  0.0804  0.0677  0.0675  0.0675
  16  0.8325  0.3435  0.0558  0.0337  0.0334  0.0334
  24  0.8325  0.3435  0.0514  0.0237  0.0229  0.0229
   fraction of zero eigenvalues of Psi (L^-3 #{lambda=0}): {4: 0.3125, 6: 0.1111, 8: 0.1328, 12: 0.081, 16: 0.04, 24: 0.0275}
B. twK bound ratios at L=4, W=32, E_n from z_S, t=T0=t0 (the largest admissible time), charges (-,+), c1=0, c2=(1,0,0) and c1=c2=0; kappa=Im m_S
   g        kappa   t0      g0       C_i(c1=c2)  C_i(c1!=c2)  C_ii(c1=c2)  Im mF  L^d
  0.01562  0.8325  0.6937  0.01301  0.9821      0.0128       0.9995       0.9995  64
  1        0.3777  0.3148  0.561    0.8705      0.2053       0.6732       0.6732  64
  10       0.2620  0.2183  4.672    12.2009      0.4779       0.5607       0.5607  64
  100      0.2604  0.2170  46.59    18.1134      0.0714       0.5590       0.5590  64
  1e+04    0.2604  0.2170  4658     18.2036      0.0007       0.5590       0.5590  64
  1e+06    0.2604  0.2170  4.658e+05 18.2036      0.0000       0.5590       0.5590  64
```
External hypotheses: none (all inputs are the repository's own definitions; `Bparam d L g t 0 = (g²+|1-t|)⁻¹ + (L^d|1-t|)⁻¹`, `Defs/Params.lean:36`). Limit computation for the one asymptotic input: `Sizes.WO`/`BAflow_lam0_window` give `g0 ≤ 𝔡⁻¹` only for `n ≥ n0(sz)`; block B above is the finite-`n` counterexample to "all `n` with a bounded `g`".

### Verdicts
- `twFold`: PASS. `twWard`: PASS (both charges; `η≠0`). `twCirc`: PASS. `twTr_eq`, `twMB_ba`, `twK_ba`: PASS (definitional/`BAMfine_eq`; no new math).
- `twK_bound` as pinned (every `n`): BLOCKED. Missing input: `0 < g0_n ≤ 𝔡⁻¹` (equivalently `g_n ≤ Λ(κ,d)` for `L_n ≥ L0`) for **all** `n`; `BAFlow` gives it only eventually and no repository lemma gives it from `BAdom`. The statement is not shown false: the numerics above (n=0 datum and `L=4`, `g` up to 1e6) satisfy both bounds, with `C_i` ≤ 18.2 ≤ `L^d`. Required amendment (dispatcher): state `twK_bound` as `∀ᶠ n in atTop, ∀ σ c1 c2, …` (constant `C(d,κ,ε,𝔡)` still before `sz,z`) — then rows 4-7 close by the cited lemmas with constants `C_i = C_P5·C_M·(κ+1)/κ`, `C_ii = 1` — and check that L4b2 consumes it eventually (inside `PrecL`); or add the premise `∀ n, 0 < lam n ∧ lam n ≤ 𝔡⁻¹`. The ticket lets a prover change a copied statement only as a finding; this change alters the quantifier of a pin, so it is the dispatcher's call (L4b2's use of `twK_bound` was not checked here).
- Overall: BLOCKED (one target blocked; stage 1b must not start until the dispatcher amends the pin).

## (a′) Preflight corrections — Sun Oct 11 11:02:00 UTC 2026 (resume under Amend 1, `docs/tickets/T2421-amend-1.md`, CONTROL H217)

**Item 1: `twK_bound` restated eventually in `n` (resolves the (a) block, row 8).** Probe form (`t/T2413:RBM3D/Probe/T2413Pins.lean:116-121`, checked by `git show`): `∃ C, 0 < C ∧ ∀ 𝔠 sz z, BAFlow … → ∀ t, … → ∀ (n : ℕ) (σ) (c₁ c₂), (∀ a, ‖twK …‖ ≤ C * sz.Bctl n (t n)) ∧ ∑ a, ‖twK …‖ ≤ C * (W^d * eta n (t n))⁻¹` (the `∀ n` is at probe line 119). New form: same `∃ C(d, κ, ε, 𝔡)` placed before `sz`, `z` (T2398 audit O2 unchanged), then `∀ᶠ n in atTop, ∀ σ c₁ c₂, (…) ∧ (…)` in place of `∀ n σ c₁ c₂, …`; the two conclusions are unchanged. Difference from the T2413 probe: quantifier `∀ n` becomes `∀ᶠ n in atTop` (paper-delta candidate T2421a).

| source | fact |
|---|---|
| `RBM3D/Defs/Sizes.lean:164` | `WO 𝔡 := ∀ᶠ n in atTop, W^(-d/2+𝔡) ≤ lam n ∧ lam n ≤ 𝔡⁻¹` |
| `RBM3D/BA/GreenSchur.lean:72` | `BAflow_lam0_window … : ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹` |

With the window `0 < g₀_n ≤ 𝔡⁻¹` supplied by `filter_upwards [BAflow_lam0_window …]`, rows 4-7 of (i) close by the cited lemmas (`BAProp5`, `BAMB_row_l1`, `BATheta_row_sum_pm`, `KBound_B_le`, `KBound_t0_ge`) with `C_i = C_P5·C_M·(κ+1)/κ`, `C_ii = 1` (unchanged from (a)). Row 8 of (i) is replaced: constraint `0 < g₀_n ≤ 𝔡⁻¹` holds for `n ≥ n0(sz)` by `BAflow_lam0_window`; slack at the instance below: `g₀ = 0.013014` against `𝔡⁻¹ = 10`. Per Amend 1 (not re-checked here), L4b2's terms (iii), (iv) and every TL row use `twK_bound` inside `≺`/`PrecL` statements, which are eventual in `n`, so nothing is lost for consumers.

**Instance restated at the eventual form (target 4).** Data as in (a)(ii): repository datum `sz0`, `n = 0` (`L=4, W=32, g=1/64`, `κ=1/2, ε=𝔡=1/10, 𝔠=1/6`), `c₂=(1,0,0) ≠ c₁=0` and `c₁=c₂`, `t ∈ {0,1/2,2/3} ≤ T0 = 0.693740`. The eventual statement is applied at the single index `n = 0`: the window is checked there by the (a) output (`g0=0.013014`, so `0 < g0 ≤ 10 = 𝔡⁻¹`), and the bounds are the (a) table values at `n=0`: `C_i` ≤ 0.9839 (c₁=c₂), 0.0128 (c₁≠c₂); `C_ii` ≤ 0.9995; no new numerics. Targets 1-3 instances (O3 `c₂≠c₁` with `c₁=0, c₂=1`; O4 non-vacuity of `twWard`, `|LHS|=1.428e-02`) are unchanged from (a)(ii) and are not eventual statements. The (a) block B (`L=4`, `g` up to 1e6) is no longer a hypothesis set of any target.

**Item 2: registry texts (TLF-C4, replaces the ticket's item-4 proposed text).** Two lines in `owedProps` (`RBM3D/Test/Axioms.lean`, list at line 102; `grep -n "BATwist" RBM3D/Test/Axioms.lean` currently returns no line):
- `RBM.BA.BATwistAvgLaw`: owner text "TL stage (TL1b: `BATwistAvgProd`)";
- `RBM.BA.BATwistLoopLaw`: owner text "TL stage (TL2a–TL2e: one step `BATwistLoopStep`, closed in TL2e; TL-V: base case and chain) + BA-V (V2a/V2b: the step and the regime glue with the fifth conjunct; `GLoopAtT0`)".
Each line in the format of the neighbouring entries (paper reference `(B.1)`/Theorem 8.2, T2398d), as in ticket item 4.

### Verdicts (after (a′))
- `twFold`, `twWard`, `twCirc`, `twTr_eq`, `twMB_ba`, `twK_ba`: PASS (unchanged).
- `twK_bound` in the eventual form (item 1): PASS; the (a) BLOCKED is resolved.
- Registry lines (item 2): PASS.
- Overall: PASS.

## (b) Script output — Sun Oct 11 12:16:36 UTC 2026 (stage 1b rerun under Amend 1; branch t/T2421 at HEAD 6e83091, no Lean edit in this session: `git status --short` empty)

Line count against the stop line, builds, axioms, grep, scope (scripts in scratchpad `T2421/`; `axioms.lean`, `clash.sh`, `mk_b.sh`):
```
$ git rev-parse --short HEAD; git status --short | wc -l   # worktree /Users/junyin/Lean_proof/RBM3D-wt/T2421, branch t/T2421
6e83091 0
$ wc -l RBM3D/BA/TwistPins.lean   # stop line 2000 (ticket, binding)
     962 RBM3D/BA/TwistPins.lean
$ git diff main...t/T2421 --stat
 RBM3D.lean              |   1 +
 RBM3D/BA/TwistPins.lean | 962 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   3 +
 3 files changed, 966 insertions(+)
$ lake build RBM3D.BA.TwistPins 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3997 jobs).
$ lake env lean RBM3D/BA/TwistPins.lean   # direct compile: exit code, output lines
exit 0, 0 output lines (no warnings, no errors)
$ lake build 2>&1 | tail -1   # full library, runs #assert_rbm_axioms with the two new owed lines
Build completed successfully (4229 jobs).
$ lake env lean docs/tickets/checks/T2421-check.lean; echo exit $?
exit 0
$ lake env lean axioms.lean   # import RBM3D.BA.TwistPins; #print axioms of each public theorem and the two owed pins
'RBM.BA.twTr_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twMB_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twK_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twWard_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twCirc_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twK_bound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twK_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATwistAvgLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATwistLoopLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom|Step2Gen_|STthetaOpg" RBM3D/BA/TwistPins.lean
0
$ bash clash.sh   # every new non-private top-level name (48; the 28 private decls all carry the stem TwistPins_), whole-word grep over RBM3D/ and RBM3D.lean outside the file
HIT BATwistAvgLaw 1
HIT BATwistAvgProd 1
HIT BATwistLoopLaw 1
HIT BATwistLoopStep 1
names checked:       48; total hits outside RBM3D/BA/TwistPins.lean: 4
$ grep -nE "RBM1D|RBM2D" RBM3D/BA/TwistPins.lean | wc -l   # ports from the sister projects
       0
```

The 4 name hits are the registered owed lines of `RBM3D/Test/Axioms.lean` (the registry of item 4); no other file defines or uses a new name.

**Verbatim-copy check** (probe `t/T2413:RBM3D/Probe/T2413Pins.lean` at 76c586e = `git rev-parse t/T2413`; §1-§3 from `open RBM RBM.Path…` to `end Twist`, 245 lines in the probe, 247 in the file; lines cut to 150 columns):
```
$ diff probe_s123.txt file_s123.txt | cut -c1-150
80c80,82
< /-- **`twK_bound`** (proofs T.1 (i)-(ii); from `BAProp5`, `BAProp5mixed`, `BATheta_row_sum_pm`, `BAMB_row_l1`): at the BA flow `‖K̃‖ ≤ C W^{-d} B_{t
---
> /-- **`twK_bound`** (proofs T.1 (i)-(ii); from `BAProp5`, `BAProp5mixed`, `BATheta_row_sum_pm`, `BAMB_row_l1`): at the BA flow `‖K̃‖ ≤ C W^{-d} B_{t
> **Eventual in `n`** (T2421 Amend 1, paper-delta candidate T2421a; the probe `T2413Pins.lean:116-121` has `∀ n`): the window
> `0 < g₀_n ≤ 𝔡⁻¹` that `BAProp5` and `BAMB_row_l1` need holds only eventually along `BAFlow` (`BAflow_lam0_window`, `Sizes.WO`). -/
84c86
<       ∀ (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
---
>       ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
```

**Target statements** (extracted by `python3 -I stmt.py RBM3D/BA/TwistPins.lean <names>`; proofs elided as `...`):
```lean
-- RBM3D/BA/TwistPins.lean:68
theorem twTr_eq (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : twTr C n t ω c₁ c₂ = twTrP n (C.GM n t ω) c₂ c₁ := rfl
-- RBM3D/BA/TwistPins.lean:80
theorem twMB_ba (z : ℕ → ℂ) (n : ℕ) (hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) :
    twMB (baFMz sz z) n = BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) := by ...
-- RBM3D/BA/TwistPins.lean:279
theorem twK_ba (z : ℕ → ℂ) (n : ℕ) (hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) (t : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    twK (baFMz sz z) n t σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a', BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁ := by ...
-- RBM3D/BA/TwistPins.lean:103
def twFold (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (a c₁ c₂ : Zd d (sz.L n)),
    ‖twLoopX n X₁ X₂ a c₁ c₂‖ ^ 2 ≤ twSq n X₁ c₂ a * twSq n X₂ a c₁
-- RBM3D/BA/TwistPins.lean:352
theorem twFold_holds (sz : Sizes d) : twFold sz := by ...
-- RBM3D/BA/TwistPins.lean:107
def twWard (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (G : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (η : ℝ), η ≠ 0 →
    G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G * G.conjTranspose) → G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G) →
    ∀ (σ : Bool) (c₁ c₂ : Zd d (sz.L n)), ∑ a, twLoopX n (twChg G σ) (twChg G (!σ)) a c₁ c₂ =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (η : ℂ))⁻¹ * (twTrP n (twChg G true) c₁ c₂ - twTrP n (twChg G false) c₁ c₂)
-- RBM3D/BA/TwistPins.lean:412
theorem twWard_holds (sz : Sizes d) : twWard sz := by ...
-- RBM3D/BA/TwistPins.lean:113
def twCirc (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (X₁ X₂ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) →
    ∀ a c₁ c₂ : Zd d (sz.L n), twLoopX n X₁ (fun x y => X₂ x y - M x y) a c₁ c₂ =
      twLoopX n X₁ X₂ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB a c₁ * twTrP n X₁ a c₂
-- RBM3D/BA/TwistPins.lean:467
theorem twCirc_holds (sz : Sizes d) : twCirc sz := by ...
-- RBM3D/BA/TwistPins.lean:122
def twK_bound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
        (∀ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * sz.Bctl n (t n)) ∧
        ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹

-- RBM3D/BA/TwistPins.lean:692
theorem twK_bound_holds (d : ℕ) : twK_bound d := by ...
```

**Compiled nonempty instances** (`RBM3D/BA/TwistPins.lean`, all inside `section Inst`, `d = 3`, datum `sz0` (`L=4, W=32`), `flow_sz0`, `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`; every deterministic hypothesis discharged):
```
$ sed -n 807,817p RBM3D/BA/TwistPins.lean   # O3, twK_bound_holds at the eventual form, c₂ = (1,0,0) ≠ c₁ = 0
/-- D3, O3 (`c₂ ≠ c₁`), at the eventual form of `twK_bound` (Amend 1): `twK_bound_holds 3` at the datum `sz0` (`flow_sz0`, `s ≡ 1/2`) with `σ = (-,+)`
and a pair `c₂ ≠ c₁` of blocks (`c₁ = 0`, `c₂ = (1,0,0)`): for every `n` of the window (an eventual set; non-vacuous since `atTop` on `ℕ` is `NeBot`),
both bounds with the constant. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∃ c₁ c₂ : Zd 3 (sz0.L n), c₂ ≠ c₁ ∧
    (∀ a, ‖twK (baFMz sz0 zSeq) n (1 / 2) ![false, true] a c₁ c₂‖ ≤ C * sz0.Bctl n (1 / 2)) ∧
    ∑ a, ‖twK (baFMz sz0 zSeq) n (1 / 2) ![false, true] a c₁ c₂‖ ≤ C * ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ := by
  obtain ⟨C, hC, hall⟩ := twK_bound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hall (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)] with n hn
  have : Fact (1 < sz0.L n) := ⟨by have := sz0.three_le_L n; omega⟩
  exact ⟨0, ![1, 0, 0], fun hh => by simpa using congrFun hh 0, (hn ![false, true] 0 ![1, 0, 0]).1, (hn ![false, true] 0 ![1, 0, 0]).2⟩
```
- `twTr_eq`, `twMB_ba`, `twK_ba`: examples at :821, :823, :825 (`n = 0`, `Im m_F > 0` is `BAmF_sz0_im_pos`, `a = 0`, `c₁ = 0`, `c₂ = (1,0,0)`).
- `twWard_holds` (O4): example at :842, `G = i·1`, `η = 1` (both resolvent identities proved in the example), both charges, sum `= W^{-d} ≠ 0` at `c₁ = c₂ = 0`.
- `twCirc_holds`: example at :870 (hypothesis from `BAMfine_eq` at the carrier's `M 0`), and the non-degeneracy example at :911 (the subtracted term `≠ 0`).
- `twFold_holds`: example at :897 (pairwise distinct blocks `0, (1,0,0), (2,0,0)`, nonzero twisted datum, left side `W^{-d} > 0`).
- Statement-level examples kept from the probe §4 (items 5): :776-781 (`BATwistLoopStep`, `BATwistSrc1`-`5`), :785-803 (`BATwistAvgProd`, `BATwistLoopBase`, `BAMainIndTL`, `BAMLOutTL`, `BAChainTL`), :929-955 (`BATwKer*`, `BATwistZeroMode`); other gates' pins stay hypotheses there.

**Registry (item 2 of Amend 1)**, `git diff 913f555..HEAD -- RBM3D/Test/Axioms.lean`, added lines (names; owner text verbatim):
```
+   -- T2421 (BA-TL TL0, DECISIONS §234, §236): the twisted-loop pins of stage TL (`RBM3D/BA/TwistPins.lean`)
+   `RBM.BA.BATwistAvgLaw, ... owner: TL stage (TL1b: `BATwistAvgProd`)
+   `RBM.BA.BATwistLoopLaw, ... owner: TL stage (TL2a–TL2e: one step `BATwistLoopStep`, closed in TL2e; TL-V: base case and chain) + BA-V (V2a/V2b: the step and the regime glue with the fifth conjunct; `GLoopAtT0`)
```

**Narrative** (facts from the output above and the files).
- Stop rule (CONTROL H134): `wc -l` = 962 against the stop line 2000; not triggered. One file; `TwistPins2.lean` not created. The diff against `main` (three-dot) touches exactly the three sole writable files.
- Verbatim copy: §1-§3 equal the probe except `twK_bound` (two hunks above: docstring lines added, `∀ n` replaced by `∀ᶠ n in atTop`; Amend 1 item 1; paper-delta candidate T2421a, section (d)). Further differences from the probe, all in §4 and none a pinned statement: `twFrame_inst` is `private TwistPins_frame_inst` and `Pf` is `private TwistPins_Pf` (§3 (E)); the probe's O3/O4/`twCirc`/`twFold` examples took `h : twK_bound 3` etc. as hypotheses, here they apply the proved `twK_bound_holds`, `twWard_holds`, `twCirc_holds`, `twFold_holds`.
- The four model-free proofs and their sources (`docs/tickets/T2398-TL-proofs.md`):

| declaration | file:line | source | method |
|---|---|---|---|
| `twFold_holds` | :352 | Lemma T.2 (`T2398-TL-proofs.md:41`) | Cauchy-Schwarz over pairs `(x,w)`; `twShift` is a bijection `[c₁] → [c₂]` (`TwistPins_sum_shift` :318, `TwistPins_sum_twist` :341) |
| `twWard_holds` | :412 | Lemma T.3 (`:49`), `n = 2` | `Σ_a E_a = W^{-d}` (`TwistPins_sum_blk` :383, `TwistPins_ward_core` :388); both charges from the two identities (2.53) |
| `twCirc_holds` | :467 | A.2 (`:22`), circled/uncircled | `twLoopX` is linear in the second slot; the `M`-term collapses by the offset tie (`TwistPins_circ_term` :440, `TwistPins_shift_comp` :434) |
| `twK_bound_holds` | :692 | Lemma T.1 (i)-(ii) (`:35`) | `∀ᶠ n` from `BAflow_lam0_window`; `baProp5_holds` and `BAMB_row_l1` (via `TwistPins_alg` :581), `TwistPins_theta_col_le` :570 (column sums of `Θ`), `TwistPins_B_le` :665, `BAself_im_le_one`; constant `C = C_d C_M (κ+1)/κ + C_M` |

- `twTr_eq` (`rfl`), `twMB_ba`, `twK_ba` are as in the probe (`twK_ba` proof unchanged in the diff above).
- The constant `C` of `twK_bound_holds` is fixed before `sz`, `z` and is built from `(d, κ, 𝔡)` (`ε` and `𝔠` are not used); there is no smallness of `g` and no `Step2Gen_*`/`STthetaOpg` (grep 0 above). T2398 audit O2 (`C` before `sz`, `z`), O3 (`c₂ ≠ c₁`, :810), O4 (`twWard` non-vacuity, :842): all three are compiled examples.
- Registry (Amend 1 item 2): the two `owedProps` lines carry the TLF-C4 owner texts verbatim; the full `lake build` passes with them (the owed ledger lists both names, no certificate). The supervisor's verdict file `REQ-2026-10-11-1013-TLF.md` was not needed: Amend 1 supersedes the proposed text of ticket item 4.
- Ports: none from RBM1D/RBM2D (grep 0 above), so no RBM1D/RBM2D diff-stat; the copied text is the probe on `t/T2413`.

## (c) Verified Mathlib names (all compile in `TwistPins.lean`; `#check @name` after `import RBM3D.BA.TwistPins` exits 0; none searched and found absent)
`Finset.sum_comm`, `Finset.sum_const`, `Finset.sum_congr`, `Finset.sum_eq_single`, `Finset.mul_sum`; `nsmul_eq_mul`, `norm_mul`, `norm_pos_iff`, `inv_pos`, `mul_inv`, `one_le_inv₀`, `mul_le_mul_of_nonneg_left`, `sub_eq_self`; `Real.one_le_rpow`; `Matrix.conjTranspose_smul`, `Matrix.one_apply`.

## (d) Open issues and paper-delta candidates
- **T2421a** (Lean/paper difference): `twK_bound` quantifies `∀ᶠ n in atTop, ∀ σ c₁ c₂, …` where the T2413 probe (`T2413Pins.lean:116-121`) and the proofs' T.1 have all `n`. Reason: the window `0 < g₀_n ≤ 𝔡⁻¹` needed by `BAProp5`/`BAMB_row_l1` holds only eventually (`Sizes.WO` is `∀ᶠ`, `Defs/Sizes.lean:164`; `BAflow_lam0_window`, `GreenSchur.lean:72`); preflight (a) row 8 shows the all-`n` form is not provable from the repository's lemmas. Consumers: per Amend 1, L4b2's terms (iii), (iv) and the TL rows use it inside `≺`/`PrecL`; I did not re-check L4b2.
- Observation: the proofs' `C = 1` (T.1 (ii)) is not reproduced; `C = C_d C_M (κ+1)/κ + C_M` (the docstring of `twK_bound` still says "`C = 1` in the proofs", which is the source's claim, not the Lean constant).
- Merge: `RBM3D.lean` (one import line after the last `import`, before `#assert_rbm_axioms`) and `Test/Axioms.lean` (two added `owedProps` entries and one comment line) are additions to shared lists; T2420 may add one `owedProps` line (union on merge, hub).
- Report length: sections (a), (a′) alone are 112 lines; this report is within CLAUDE.md §6's 300 lines but not the ticket's 150.
