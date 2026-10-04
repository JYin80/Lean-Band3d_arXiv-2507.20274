Auditor model: claude-opus-5-5
# T2087 audit (round 1) — S3-24a `RBM3D/Induction/IterationsA.lean`
Written Sun Oct  4 00:55:58 UTC 2026 (`date -u`). Branch `t/T2087` at `8e442ed`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2087-audit1` (detached).
`$S` = auditor scratchpad `.../scratchpad/T2087`.

## 1. Scope, build, axioms, forbidden tokens
```
$ git diff --name-only main...t/T2087
RBM3D/Induction/IterationsA.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   # registry lines only (owedProps)
+   `RBM.Gauss.Sizes.STXiBoot, -- `(am;asoi222)` ... hypothesis of `iterationsA_step` (T2087)
+   `RBM.Gauss.Sizes.STAvgU, -- `(Gt_avgbound_flow)` uniform in `u` ... hypothesis of `iterationsA_avg_of_STAvgU` (T2087)
$ lake build RBM3D.Induction.IterationsA   # warnings/errors mentioning IterationsA.lean: none
✔ [3709/3709] Built RBM3D.Induction.IterationsA (16s)
Build completed successfully (3709 jobs).   exit 0
$ lake build RBM3D | grep -E "error|Build completed"
Build completed successfully (3829 jobs).
$ lake env lean $S/pre.lean   # import RBM3D; import RBM3D.Induction.IterationsA; #assert_rbm_axioms
non-vacuity certificates: 4 of 99 premises in the two ledgers; ...      exit=0
$ lake env lean $S/ax.lean    # #print axioms of all 31 public declarations
exit=0; lines "depends on axioms: [propext, Classical.choice, Quot.sound]": 31; other lines: none
$ grep -cwE "sorry|admit|native_decide|axiom" RBM3D/Induction/IterationsA.lean
0
```
Frozen signatures: no merged file is touched (diff above). Names: unpinned public names carry the file stem (`iterationsA_*`, `IterationsAScale`); pinned `st_*` kept.
```
$ python3 $S/inst.py   # per public name: occurrences in §9 (lines 1782-2033) / files on main containing the name
31 public; every name inst>=1, main0 (no clash)
```

## 2. Target 2 — four probe helpers, verbatim (ticket item 2)
```
$ python3 (compare 3c58211:RBM3D/Probe/T2041Pins.lean blocks with the file, `private theorem`→`theorem`)
st_prec_one_add_sup probe:840 file:103 lines 25 25 IDENTICAL(after private->public)
st_prec_of_xi probe:866 file:129 lines 20 20 IDENTICAL(after private->public)
st_one_le_XiL probe:1068 file:151 lines 8 8 IDENTICAL(after private->public)
st_one_le_XiLK probe:1077 file:160 lines 9 9 IDENTICAL(after private->public)
```
`st_iterate`, `st_Bctl_ge`, `st_Bctl_pos` are imported (ScaleFacts3/Step34Pins), not copied. Instances: lines 1888-1902 (`szB`, `d = 3`, `v = 1/2`, `Bctl > 0` from `st_Bctl_pos`; `U = Unit`, `V = Fin 2`, `f ≡ 1/2`, `B ≡ 1`). **PASS.**

## 3. Target 1 — the `d ≥ 3` part of RBM2D `Step3.lean:1-777` (Ψ-calculus, chain bound, step)
**Statement vs the ticket's mathematics.** The check file pins no Lean text for the new targets (it `#check`s merged names only), so the statements are judged against the ticket (Ψ-calculus, `(xiu2n+2psi)` with `(5.118)`, class-b `d`-dimensional exponents) and the paper `3_5:1380-1417`, `3_5:1772-1864` (read in this audit).
- `STPsi` (merged, `Step34Pins:76`) = `A^{3/4} + ρ^{n-1} A^{1-k/8}` = paper `(adsyzz0s8d6)` `3_5:1396`. RBM2D `step3_Psi = As^{1/2}+R^{n-1}As^{1-k/4}` is not this function; the file uses `STPsi` and proves `iterationsA_STPsi_eq` (`= (A^{1/8})^6 + ...`), as the ticket asks ("use `STPsi`"). Class b: the `d = 2` exponents `b^3, b^4, R^2` (`b = As^{1/4}`) become `b = A^{1/8}`, `A^{3/4} = b^6`, `A^{7/8} = b^7`: the ticket's "dimension-free" premise is false; proposed as `T2087a`. No ported statement was found false at `d ≥ 3` (the RBM2D real lemmas are restated, not copied), so the ticket's stop condition is not triggered; the class-b instruction covers the restatement.
- `iterationsA_chain_term` (`:542`) vs `(xiu2n+2psi)` + `(auskoppw2)` + `(sef8w483r324)`: `∃ C > 0` depending on `(cB,cv,K,N,k)` only, then `∀ A ρ T Bu x y p`, `p ≥ 2`; `x ≤ 1 + cv A((1+cB) + T ρ^N A^{1-(k-1)/8})^2` is `Ξ_{2n-1}^{1/2} ≺ A^{1/2}(1+ρ^n A^{-(k-1)/8})` with `T ≍ A^{-1}`; `y ≤ 1+ρ^{4p-1}` is `(sef8w483r324)` at `4p`; `(cvA)^{-1} ≤ Bu` gives `Bu^{-1/(4p)} ≤ (cvA)^{1/(4p)}`; conclusion `≤ C·STPsi A ρ N k`. Matches; `p ≥ 2` is weaker than the paper's `p ≥ 4` (the step uses `p = N+4 ≥ 6`). Fixed parameters before the universally quantified data: yes.
- `iterationsA_xiL_odd_le` (`:740`), `(5.118)` via `RBM.Ind.loopXi_le` (`:772`) and `loopMax_odd_sq_le` (`:755`) as the ticket asks: `Ξ_{2N-1} ≤ 1 + B^{-1}((Ξ_{2l1}Ξ_{2l2})(Ξ_{2l3}Ξ_{2l4}))^{1/2}`, `l1=(N+1)/2`, `l2=l3=N/2`, `l4=(N-1)/2`, `N ≥ 3` = `(suauwiioo1)`+`(eq:boundtwochains)` (`l3 = ⌈(N-1)/2⌉ = ⌊N/2⌋`). Matches (paper uses it for `n ≥ 4`).
- `iterationsA_boot_bound` (`:630`): `STbootRHS 1 XL XLK Bu N p ≤ C·Ψ(N,k)` under the parameter choices of the paper's proof (`XL m ≤ 1+TΨ(m,k-1)` for `m ≤ N+1`, `≤ 1+TΨ(m,k)` for `m ≤ N-1`, `XLK m ≤ 1+Ψ(m,k)`): the deterministic content of `(sadui_w0)` → `Ψ(n,k)`. Matches.
- `iterationsA_step` (`:1283`): conclusion `STIterHyp sz E s t A N k`; `IH1 : ∀ r, 2 ≤ r → r+1 ≤ N → STIterHyp … r k`, `IH2 : ∀ r, 2 ≤ r → r ≤ N+2 → STIterHyp … r (k-1)`, `2 ≤ N`, `1 ≤ k` — identical to the induction clause of the merged `STIterR` (`Step34Pins:478`) and to `lem:iterations` `3_5:1407-1417`. Other hypotheses: `hS : IterationsAScale` (deterministic, see below), `hboot : STXiBoot` (pin, S3-18b/S3-22), and the paper's displayed ingredients `(rela_XILXILK)` (`hrela`), the averaged law (`havg`), `(sef8w483r324)` (`hapri`), uniformly in `(v,u) ∈ STPair`.
- Ψ-calculus lemmas (`:473-510`): equalities/monotonicities of `STPsi` with explicit `A ≥ 0/1`, `ρ ≥ 0/1`, `k ≥ 1`; correct as stated.

**Hidden hypotheses / vacuity / cycles.**
- `IterationsAScale` (`:1058`) is a `Prop` structure of scale facts (`0 ≤ cB`, `1 ≤ cv, K`, `A, T ≥ 0`, `t < 1`, `∀ᶠ n`: `1 ≤ A`, `1 ≤ ρ ∧ ρ² ≤ K A^{1/8} ∧ Tρ²A^{7/8} ≤ cB K`, `T A^{3/4} ≤ cB`, `(cvA)^{-1} ≤ B_w ≤ T` on `[s,t]`). It is not an assumed hypothesis: it is **proved** from merged predicates by `iterationsA_scale_I` (`STRegIterI`, `STConStInd 𝔠d`, `WO`, `t<1`, `|E|<2`, `2 ≤ d`, `𝔠d ≤ 1/16`; output `A = STAI`, `T = 2A^{-1}`, `cB=cv=K=2`) and `iterationsA_scale_II` (`STConStInd 𝔠d`, `t<1`, `|E|<2`, `𝔠d ≤ 1/24`; `A = STAII`, `T = A^{-1+𝔠d}`, constants 1). Both bounds on `𝔠d` are compatible with `STIterR`'s `∃ 𝔠d ≤ 1/100`.
- `hrela`, `havg`, `hapri` are stochastic. `havg` follows from the merged pin `STAvgU` (`iterationsA_avg_of_STAvgU`), `hapri` from `STStep1Loop` (`iterationsA_apriori_of_lRB1`), `hrela` from a `𝒦`-loop bound uniform in `(v,u)` and labels (`iterationsA_rela_of_K`); `STKloop` is deterministic (`Defs.lean:64`, no `ω`), so the per-sequence `STKbound` (`Defs.lean:174`) yields the uniform form by a choice-of-violators argument — S3-24b's job, listed in the prove report (d).
- No cycle: imports `ScaleFacts3`, `Split` (merged); `STXiBoot`, `STAvgU` registered as owed premises (pre-check exit 0).

**Compiled nonempty instances (§9, lines 1782-2033; all built).**
```
real data  A = 256 (b = 2), ρ = 3/2, T = 1/256, cB = 1, cv = K = 2:
  iterationsA_ineq_long :1800 (N=3,m=4) | ineq_quad :1807 (N=6,m=3,j=5) | ineq_chain :1815 (N=3,p=1,w=3/2,x=5,y=2)
  boot_bound :1825 and chain_term :1846 at N=3, k=2, p=7, Bu=1/100, controls XLv/XLKv, every hypothesis by norm_num/lemma
  Ψ-calculus :1864-1879 at (A,ρ,m,k) = (256,3/2,3,2)
model data szB (merged Step34Pins:710: d=3, L=4, W_n=n+4, ilambda=1), flow zB:
  scale_I  :1944 at (s,t) = (7/8,15/16), 𝔠d=1/100, 𝔡=1/10 (szB_regIterI, szB_WO, conStInd_const: merged)
  scale_II :1947 at (s,t) = (15/16,31/32), 𝔠d=1/100
  step case (i) :1954 at (N,k)=(3,2) [chain branch]; case (ii) :1971 at (N,k)=(2,1); hS discharged by scale_I/II;
    hypotheses kept: STXiBoot (pin), hrela, havg, hapri, IH1, IH2 (stochastic)
  avg_of_STAvgU :1990, apriori_of_lRB1 :1996 (m=3), rela_of_K :2003 (m=2): the pin stays a hypothesis
  xiL_odd_le :1914 (N=3), STXiL_eq/STmaxL_eq :1905-1909, prec helpers :2012-2029
```
No `N = 0`, empty index, collapsed window (`s < t` in both cases, `W_n → ∞`) or `False` premise; all deterministic hypotheses discharged at concrete data.

**Paper deltas.** Proposed in the prove report (d): `T2087a` (`d = 2` exponents of the ticket/RBM2D; `d ≥ 3` `Ψ`), `T2087b` (merged `hBA` with `δ = 1/4` too weak; the step needs `B_v ≤ c_B A^{-1+δ}`, `ρ²A^δ ≤ K A^{1/8}`: the fields of `IterationsAScale`, hence `𝔠d ≤ 1/16`/`1/24`), `T2087c` (case (ii) loss `T = A^{-1+𝔠d}`, paper omits case (ii) `3_5:1594`). The `2 ≤ d` of `scale_I` is the existing D75 (T2058c). `STXiBoot`'s constant-in-`v` controls: existing D48 (T2041a).

**Verdict Target 1: PASS.**

## 4. Observations (no statement, instance, build, axiom or coverage change)
- O1. `p ≥ 2` in `iterationsA_chain_term`/`iterationsA_boot_bound` (paper `p ≥ 4`, `3_5:1785`) is a weaker hypothesis than the paper's, so the Lean statement is stronger. The module docstring and prove report (a) mention it but give it no `T2087x` tag. The dispatcher may fold it into `T2087a`.
- O2. The API differs from the ticket's planned list (none of RBM2D's 44 declarations is copied; `IterationsAScale` and `iterationsA_step` replace `Step3Scales`/`Step3Hyp`/`step3_S_of_S`). The cut line and the map are given (module docstring, report b.2). S3-24b's ticket should name the delivered API and the open `hrela` source (uniform `𝒦` bound from `STKbound`).
- O3. The report's §b.5 statement that `IterationsAScale`'s `∀ n` fields hold "in both cases" is correct: `scale_I/II` prove them for every `n`.

## 5. Verdict
| target | verdict |
|---|---|
| 1. `d ≥ 3` Ψ-calculus, chain bound `(xiu2n+2psi)`/`(5.118)`, step (`iterationsA_*`, `IterationsAScale`) | PASS |
| 2. `st_prec_one_add_sup`, `st_prec_of_xi`, `st_one_le_XiL`, `st_one_le_XiLK` (verbatim) | PASS |

Ticket T2087: **PASS**. No dispatcher sign-off is needed.
