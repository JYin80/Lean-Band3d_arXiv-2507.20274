Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 01:05:55 UTC 2026

Sources read (worktree `t/T2355` at `5869c29`): `Universality/OUInterfaceK.lean:107-111` (`UNG2bRowk`), `:48-72` (`UNOUProfRowk`), `:76-103` (`UNOUEq747k`); `Universality/PinsK.lean` (`UNKind`, `UNOUQUEk`); `Main/QUEFromQDiff.lean:85-87` (`etaQ`), `:91` (`queDomain`), `:285-330` (`queFixed`), `:463-` (`queChain`); `Universality/ZeroModeProfile.lean:55,84,140-151`; `Universality/Pins.lean:384-395`; `Main/QUECore.lean:805,966,1013`.

### (i) Exponent table (d >= 3, `eps0 = D/3`, `c = D/6`, D = `𝔡`; `tauQ` = `τ_Q`; `tauE = tauQ/2` the `τ` of `UNOUEq747k`)

| quantity | value | constraint | slack |
|---|---|---|---|
| `eps0` (window `UNOUQUEk`) | `D/3` | `0 < eps0` (`queChain`, `queDomain`); `eps0 < D/2` (`queChain`); `eps0 <= 3D/5` (`queChain_real`, `que_three_terms`); `eps0 < D` (`queDomain`) | `D/2-eps0 = D/6`; `3D/5-eps0 = 4D/15`; `D-eps0 = 2D/3` |
| `c` | `D/6` | `queChain`/`queFixed` impose **no** hypothesis on `c` (Markov scale `W^{-2c} > 0` always); `c = D/6 > 0` anyway | none needed |
| `η_Q` | `ouEtaQ sz D n = etaQ sz n (D/3)` | `0 < η_Q <= 1` eventually; the two defs are the same term (`ouEtaQ`: `W^(-(D/3)) * (lam*W^(d/2)/Nsz)`; `etaQ sz n ε₀`: `W^(-ε₀) * (...)`, `ε₀ := D/3`), so `rfl` | eq. |
| min in exponent | `min(2 eps0, 2D/5) = min(2D/3, 2D/5) = 2D/5` | `queBound` (`Pins.lean:384`) literal `-(min (2*ε₀) (2*𝔡/5)) + 2*c + τ` | gap `2D/3-2D/5 = 4D/15` |
| Markov exponent | `-2D/5 + 2c + tauQ = -D/15 + tauQ` | `queChain` at `(ε₀,c,τ,C) = (D/3, D/6, tauQ, C)` is syntactically `queBound (W) D (D/3) (D/6) tauQ` (`ENNReal.ofReal` of the same `W`-power) | `< 0` iff `tauQ < D/15`; for `tauQ >= D/15` the target bound is `>= 1` (still true) |
| `τ` of `qdBoundExp` | `tauE = tauQ/2 > 0` | `queChain` uses `qdBoundExp sz n (τ/2) η_Q`; `UNOUEq747k` is `∀ τ > 0` | any |
| `C` | from `UNOUProfRowk (K d) (P d)` at `(D, κ)` | `0 < C` (`queChain`); `K_row = C lam^{-2} W^{-d}` | none |
| `ζ(t)` | `ouZeta t = 1 - e^{-t}` | `UNOUProfRowk` needs `0 <= ζ <= 1`: `ZeroModeProfile_ouZeta_nonneg (0 <= t)`, `ZeroModeProfile_ouZeta_le_one` (all t) | `ζ ∈ [0,1)` |
| `lam` | `0 < lam n`, `lam n <= D⁻¹` | `UNOUProfRowk` side conditions; both eventually from `Admissible` field `WO` (`hA.2.2.2.2`: `W^(-d/2+D) <= lam ∧ lam <= D⁻¹`, `W^(...) > 0`) | `lam >= W^{-d/2+D}` |
| `z = E + iη_Q` | `0 < z.im = η_Q <= 1`, `K.bulk sz κ z.re n` | `UNOUProfRowk` side conditions; `im` bounds: `queDomain` at `κ' = 1`, `E = 0` (`|0| <= 2-1`) gives `locDomain` hence `0 < η_Q <= 1` for **every** `κ` (bulk of a kind is abstract and `κ` may exceed 2, so `queDomain` at the given `κ` cannot be used); `z.re = E` by `simp`; bulk is the hypothesis `K.bulk sz κ (E n) n` | `E=0, κ'=1`: `\|E\| <= 2-κ'` slack 1 |
| `t` window | `0 <= t <= ouTStar sz τU n = N^{-1+τU}` | only enters via `UNOUEq747k`; `UNOUQUEk` has no `τU <= ouTauMax` | `τU > 0` arbitrary |
| `3 <= d` | `d >= 3` | `calB_le_two_inv` needs `2 <= d`; `queChain` needs `3 <= d` | 1 |
| absorption threshold | `W^{tauQ/2} >= 3 max(16C,128)` | inside `queChain` (eventual; `∀ᶠ`) | eventual |

### (i-a) Preflight items asked for in the ticket

1. **`queFixed` (merged) vs the generic copy.** Merged hypotheses (`QUEFromQDiff.lean:285-300`): `z = E + η I` and `0 < η` (generic copy: `z` given; `η = etaQ sz n ε₀` where `ε₀ = D/3`, `0 < η` from `queDomain` at `κ'=1`); expectation half `hQ`, with `∫ ... ∂(Sizes.seqP sz)` and `profPM/profPP` (generic copy: `∫ ... ∂(ouP (K.M sz).toUNModel n)` of the integrands in `UNOUEq747k`, profiles `P.pm/pp sz n (ouZeta t) z`, `ε = qdBoundExp sz n tauE η_Q`; supplied by `UNOUEq747k` at `(κ, E, t, tauE)`; `Gres H z true` replaces `sz.Gn n z ω`, `Gn := Gres (seqXmat) z true` by definition, `GLoopFlow.lean:165`); row differences `hK` with `K = C lam^{-2} W^{-d}` (supplied by `UNOUProfRowk` at `(D, κ)` after the side conditions above; the merged proof takes them from `queRowDiff`). Conclusion: two Markov bounds. **`UNOUQUEk` (PinsK) has only the `queBadMat` event, no `que2BadMat`**: the copy needs only the first conjunct (ticket says "both bad events"). Generic data needed from the OU layer: `ouP (K.M sz).toUNModel n` is a probability measure (`isProbabilityMeasure_ouP`, `OU.lean:44`), `ouMatC (K.M sz) n t` is Hermitian (`ouMatC_isHermitian`, `PinsK.lean`) and measurable (private `OUInterfaceK_measurable_ouMatC`, `OUInterfaceK.lean`; copy).
2. **Dependency of the merged `queFixed` that is sz-specific** (a Lean-side finding, mathematics unchanged): `queFixed` calls `queX_core`, `queBad_sub` (`QUECore.lean:805, 966`), which are stated for `Sizes.seqP`/`sz.Gn`/`sz.seqXmat`, and use private lemmas (`queCore_obs_herm`, `queCore_obs_eq` (`:542,548`), `queCore_blk_cross`, `queCore_quad_blk`, `queCore_sub_of_normSq`, `queCore_rpow_sub` (`:918-958`) and the `queCore_Tp/Tm/F_integrable`, `queCore_trace_eq_sum` chain `:661-795`). So "private generic copy of `queFixed`" means a generic copy of `queX_core` + `queBad_sub` + their private helpers too. Public and already generic (reusable): `normSq_le_trace` (`:422`, any `H`), `queMarkov` (`:1087`, any probability space), `queImG`, `queObs`, `queBlk`, `queX` is **not** (stated with `sz.seqXmat`): the copy defines its own `X_c` on `ouMatC`.
3. **`ouEtaQ sz D n = etaQ sz n (D/3)`**: by `rfl` (same term, see table).
4. **Side conditions of `UNOUProfRowk` and `queChain`** at `eps0 = D/3`, `c = D/6`: `queChain`: `0 < D/3`, `D/3 < D/2` (from `D > 0`, `hA.2.1`), `0 < tauQ`, `0 < C`; no condition on `c`. `UNOUProfRowk`: `0 < lam`, `lam <= D⁻¹` (`hA.2.2.2.2` of `Admissible`, as in `QUE_of_QDiff`), `0 < z.im <= 1` (`queDomain` + `locDomain_im_pos`, `Endpoints.lean:481`, `locDomain` third component), bulk (hypothesis), `ζ ∈ [0,1]` (`ZeroModeProfile_ouZeta_nonneg/le_one`). `W -> ∞` from `RBM.Green.tendsto_W` (`Green/LDE.lean:444`, from `hA.1, hA.2.2.1, hA.2.2.2.1`), used in `queDomain`/`queChain`.
5. **Uniformization**: `UNOUEq747k` is per sequence `(E_n, t_n)` with bulk inside `∀ᶠ n`; target is `∀ᶠ n, ∀ t ∈ [0, ouTStar], ∀ E, bulk → ...`. Take `T n = {(t,E) | 0 <= t <= ouTStar sz τU n}` (nonempty: `(0,0)`, `ouTStar >= 0` as `rpow` of a nonneg base), `P n (t,E) := bulk → ∀ a b, (expectation half at tauE)`; the merged private `OUInterfaceK_eventually_forall_mem_of_forall_seq` (`OUInterfaceK.lean:116`) gives `∀ᶠ n, ∀ (t,E) ∈ T n, P`. The probability bound is then per fixed `(t, E, a)` (no union over `t, E, a` inside the probability), matching `UNOUQUEk`.
6. **§29 (DECISIONS lines 237-241; items (5)-(7) from §45 O2 at `:332`)**: (1) time domain: only `0 <= t` (for `ζ >= 0`) is used, no `1 - t`, no `t < 1`: OK. (2) boundary `1 - lam²/L²`: not used (inside `UNOUProfRowk`, a hypothesis). (3) `L`-`W` relation: not used (`η <= lam²/L^d` uses only `(eq:WO)` and `W >= 1`; `W^d <= N` uses `L >= 1`). (4) `∀ n` vs `∀ᶠ n`: all conclusions and hypotheses `∀ᶠ n` (bulk inside); `Eq747k` is stated that way: OK. (5) per time, union outside probability: bound is per `(t,E,a)`; union is not needed: OK. (6) `0 < lam` and `W -> ∞` come from `Admissible` (`WO`, `SizeTendsto`, `Bandwidth`): used, listed above. (7) scale: `W^τ` throughout (`qdBoundExp`, `queBound`): consistent.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `Defs/Sizes.lean:260-266`), `(𝔠, D) = (1/6, 1/10)` (`sz0_admissible`), `κ = 1/10`, `τ_U = 1/1000` (no upper bound used; `ouTauMax 1/6 1/10 = 1/720`), `tauQ = 1/1000`, `tauE = 1/2000`, `eps0 = 1/30`, `c = 1/60`, `C = 1`, kind `UNKind.band 3`, profile `UNOUProfile.band 3` (`UNOUProfRowk` holds: `unOUProfRowk_band`, `OUInterfaceK.lean:329`, no hypothesis). External hypothesis: `UNOUEq747k (band 3) (band 3) sz0 (1/10) (1/1000)` (UN-51's pin, equivalent to `UNOUEq747 sz0 ...` by `UNOUEq747k_band`); its limit computation is in the script (exponent in `m = 2(n+1)`: `W = m^5`, `lam = m^{-6}`, `N = 8 m^18`, `Nη_Q = m^{4/3}`, `(lam² W³)^{-1/5} = m^{-3/5}`, error `qdBoundExp ~ m^{5 tauE - 8/3 - 3/5} = m^{-3.26} -> 0`, row term `C lam^{-2} W^{-3} = m^{-3}`).

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2355/inst.py` (floats on logs; `LHS` is the left side of `queChain`, `RHS = W^{-D/15+tauQ}`; columns: n, W, `(eq:WO)`+`W>=N^c`, `η_Q<1`... as printed).

```
eps0,c = 1/30 1/60 | eps0<dd/2: True slack 1/60 | eps0<=3dd/5: True slack 2/75 | 0<c: True
exponent -min(2e0,2dd/5)+2c+tauQ = -17/3000 = -dd/15+tauQ = -17/3000 equal: True ; min= 1/25
n | W | admissible(WO,W>=N^c) | eta_Q<1 | log eta_Q | log LHS | log RHS | LHS<=RHS
0 W=32 True True True -13.63 logLHS=3.93 logRHS=-0.02 False
10 W=5.15e+06 True True True -53.60 logLHS=2.66 logRHS=-0.09 False
1000 W=3.22e+16 True True True -128.78 logLHS=1.63 logRHS=-0.22 False
100000 W=3.2e+26 True True True -205.51 logLHS=0.78 logRHS=-0.35 False
100000000 W=3.2e+41 True True True -320.64 logLHS=-0.41 logRHS=-0.54 False
1000000000000 W=3.2e+61 True True True -474.15 logLHS=-1.95 logRHS=-0.80 True
100000000000000000000 W=3.2e+101 True True True -781.16 logLHS=-5.02 logRHS=-1.32 True
queChain threshold: W >= (384)^(2/tau)=10^5168.7
Eq747k error exponent in m: 5t - 8/3 - 3/5 = -3.2641666666666667 (<0 so error->0)
K term C lam^-2 W^-3 ~ m^ -3
Markov K-term exponent in W: -2e0+2c = -0.03333333333333333  vs RHS exponent -0.005666666666666667
```

Reading: at every printed `n` the hypotheses hold (`(eq:WO)`, `W >= N^{1/6}`, `0 < η_Q < 1`, `0 < lam <= 10`; `eps0 < D/2`, `0 < τ`). The Markov bound (`queChain` LHS) is `<=` RHS from `n ~ 10^12` on in this sequence (log-scale values, `C = 1`); the sufficient absorption threshold used inside the merged `queChain` proof (`W^{tauQ/2} >= 384`) is `W >= 10^{5168}`, so no finite-`n` witness of the `∀ᶠ` statement is extracted: the Lean instance applies `g2bRowk` at `sz0` with `UNOUEq747k` left as hypothesis (another gate's pin) and every deterministic hypothesis (`3 <= d`, `UNOUProfRowk` by `unOUProfRowk_band`, `Admissible` by `sz0_admissible`, `τ_U > 0`) discharged at the concrete data; the conclusion is `∀ᶠ`. Exponent identity at `D = 1/10`: `-min(2/30, 2/50) + 1/30 + tau = -1/25 + 1/30 + tau = -1/150 + tau = -D/15 + tau` (script line 2, `tauQ = 1/1000`: `-17/3000`).

### Verdicts

- `g2bRowk` (`∀ K P, UNG2bRowk K P`): **PASS** (every hypothesis available at the data above; exponents close with slack `D/6` at `eps0 < D/2`; no `τ_U` bound needed). Notes for stage 1b: use `queDomain` at `κ' = 1`, `E = 0` for `0 < η_Q <= 1` (not at the given `κ`); only the `queBadMat` half of `queFixed` is needed; the generic copy needs generic versions of `queX_core` and `queBad_sub` plus their private helpers (item 2).
- `g2bRow : UNG2bRow` (`unG2bRow_of_k`, `OUInterfaceK.lean:404`, from `g2bRowk` at `UNKind.band`, `UNOUProfile.band`): **PASS** (merged bridges `UNOUQUEk_band`, `UNOUEq747k_band`, `unOUProfRowk_band` exist).
- Registry: `RBM.Univ.UNG2bRowk` is at `Test/Axioms.lean:194`; no `RBM.Univ.UNG2bRow` registry entry (grep `RBM.Univ.UNG2bRow[ ,]` on `Test/Axioms.lean`: no hit). Name-clash grep (`RBM3D/` outside `Probe/`, declarations `g2bRowk`, `g2bRow`, `QUEFlow`): 0; `QUEFlowInst`, `QUEFlow_`: 0; `RBM3D/Universality/QUEFlow.lean` absent.
- Paper-delta candidate `T2355a`: none from 1a.

## (b) Script output (branch `t/T2355`, final commit 5661068; evidence run starts at the `date -u` shown)

```
$ date -u; git log -1 --format=%h; wc -l RBM3D/Universality/QUEFlow.lean
Fri Oct  9 01:22:49 UTC 2026
5661068
    1003 RBM3D/Universality/QUEFlow.lean
$ lake build RBM3D.Universality.QUEFlow 2>&1 | grep -v 'exceeds the 100\|^$\|Note: This linter\|string gaps' | tail -4
Build completed successfully (3746 jobs).
$ lake env lean ax.lean   # import RBM3D.Universality.QUEFlow + #print axioms of the five public theorems
'RBM.Univ.g2bRowk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.g2bRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.QUEFlowInst.inst_ouEtaQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.QUEFlowInst.inst_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.QUEFlowInst.inst_queBound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ lake build RBM3D.Test.Axioms   # after the one-line registry deletion
Build completed successfully (2 jobs).
$ cat reg.lean   # registry pre-check: root + new module + #assert_rbm_axioms
import RBM3D
import RBM3D.Universality.QUEFlow
#assert_rbm_axioms
$ lake env lean reg.lean > reg.out; echo exit $?; <selected lines>
exit 0
axiom audit: 10496 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
premises found by scanning: 138 (borrowed 1, owed 76, structural 42, refuted 6, superseded 13).
registry: 2 borrowed + 130 owed + 109 structural + 7 refuted + 14 superseded; 124 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
non-vacuity certificates: 0 of 132 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what e
$ grep -c 'UNG2bRowk' reg.out   # the deleted owed name
0
$ cat chk_full.lean (tail) ; lake env lean chk_full.lean   # check-file equality
example : RBM.Univ.T2355Check.T2355_g2bRowk := RBM.Univ.g2bRowk
example : RBM.Univ.T2355Check.T2355_g2bRow := RBM.Univ.g2bRow
exit 0
0
$ temp uncommitted 'import RBM3D.Universality.QUEFlow' after RBM3D.lean:395; lake build (whole library, runs #assert_rbm_axioms); RBM3D.lean then restored
 RBM3D.lean | 1 +
 1 file changed, 1 insertion(+)
exit 0
non-vacuity certificates: 0 of 132 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what e
Build completed successfully (4167 jobs).
0
```

```
$ sed -n '898p;953,954p' RBM3D/Universality/QUEFlow.lean   # the two targets
theorem g2bRowk : ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)), UNG2bRowk K P := by
theorem g2bRow : UNG2bRow :=
  unG2bRow_of_k (g2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d))
$ sed -n '109,111p' RBM3D/Universality/OUInterfaceK.lean; sed -n '132,134p' RBM3D/Universality/ZeroModeProfile.lean   # the pinned Props
def UNG2bRowk (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) : Prop :=
  ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (K d) (P d) → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → UNOUEq747k (K d) (P d) sz 𝔡 τU → UNOUQUEk (K d) sz 𝔡 τU
def UNG2bRow : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUEq747 sz 𝔡 τU → UNOUQUE sz 𝔡 τU
$ sed -n '/^def T2355_g2bRowk/,/^def T2355_g2bRow :/p' docs/tickets/checks/T2355-check.lean   # (main worktree)
def T2355_g2bRowk : Prop :=
  ∀ (K : ∀ d, RBM.Univ.UNKind d) (P : ∀ d, RBM.Univ.UNOUProfile (K d)), RBM.Univ.UNG2bRowk K P
/-- Target `g2bRow` (band). -/
def T2355_g2bRow : Prop := RBM.Univ.UNG2bRow
$ sed -n '815,828p' RBM3D/Universality/QUEFlow.lean   # statement of the private generic copy QUEFlow_queFixed (proof ends line 845)
private theorem QUEFlow_queFixed (P : Measure Ω) [IsProbabilityMeasure P]
    (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (ε₀ c E ε K : ℝ) (z : ℂ)
    (PM PP : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hz : z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) (hη : 0 < etaQ sz n ε₀)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b ∂P) - PM a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) a b ∂P) -
          PP a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n),
      ‖PM a b - PM a b'‖ ≤ K ∧ ‖PP a b - PP a b'‖ ≤ K) (a : Zd d (sz.L n)) :
    P {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (Hm ω)} ≤
      ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))) := by
$ sed -n '956,1003p' RBM3D/Universality/QUEFlow.lean | <drop doc comments, blank lines>   # the instances, compiled in the builds above
/-! ## 6. Compiled instances (`d = 3`, `sz0`, band kind; the owed pin `UNOUEq747k` stays a hypothesis) -/
namespace QUEFlowInst
open RBM.Gauss.SizesInst
example
    (hE : UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000)) :
    UNOUQUEk (UNKind.band 3) sz0 (1 / 10) (1 / 1000) :=
  g2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) 3 le_rfl
    (unOUProfRowk_band le_rfl) (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num) hE
example (hE : UNOUEq747 sz0 (1 / 10) (1 / 1000)) :
    UNOUQUE sz0 (1 / 10) (1 / 1000) :=
  g2bRow 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (by rw [show ouTauMax (1 / 6) (1 / 10) = 1 / 720 by unfold ouTauMax; norm_num [min_def]]
        norm_num) hE
theorem inst_ouEtaQ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ) (n : ℕ) :
    ouEtaQ sz 𝔡 n = etaQ sz n (𝔡 / 3) := rfl
theorem inst_exponent (τ : ℝ) :
    -(min (2 * ((1 / 10 : ℝ) / 3)) (2 * (1 / 10 : ℝ) / 5)) + 2 * ((1 / 10 : ℝ) / 6) + τ =
      -((1 / 10 : ℝ) / 15) + τ := by
  norm_num [min_def]
theorem inst_queBound (W : ℕ) (τ : ℝ) :
    queBound W (1 / 10) ((1 / 10) / 3) ((1 / 10) / 6) τ =
      ENNReal.ofReal ((W : ℝ) ^ (-((1 / 10 : ℝ) / 15) + τ)) := by
  unfold queBound
  rw [inst_exponent]
end QUEFlowInst
end RBM.Univ
end
$ grep -rn 'g2bRowk\|g2bRow\|QUEFlowInst\|QUEFlow_' RBM3D | grep -v 'Probe/' | grep -v 'RBM3D/Universality/QUEFlow.lean' | cut -c1-70   # name clash: only docstrings
RBM3D/Universality/ZeroModeProfile.lean:131:/-- **Row `UNG2bRow`** (UN
RBM3D/Universality/OUInterfaceK.lean:107:/-- **Row `UNG2bRowk`** (UN-5
$ grep -n '^theorem\|^def\|^example' RBM3D/Universality/QUEFlow.lean | cut -c1-40; grep -c '^private' RBM3D/Universality/QUEFlow.lean   # non-private declarations; private count
898:theorem g2bRowk : ∀ (K : ∀ d, UNKind
953:theorem g2bRow : UNG2bRow :=
967:example
974:example (hE : UNOUEq747 sz0 (1 / 10)
982:theorem inst_ouEtaQ {d : ℕ} (sz : Si
987:theorem inst_exponent (τ : ℝ) :
993:theorem inst_queBound (W : ℕ) (τ : ℝ
46
$ grep -n 'sorry\|admit\|native_decide\|^axiom' RBM3D/Universality/QUEFlow.lean   # (no output = none)
$ grep -n 'UNG2bRow' RBM3D/Test/Axioms.lean | cut -c1-60   # UNG2bRow is no registry name; the two hits are comments of other entries
193:   `RBM.Univ.UNG1Rowk, -- (T2282, UN-51g: owed; owner UN
195:   `RBM.Univ.UNOUClaims, -- bulk universality pin, the t
$ git diff --stat main...t/T2355; git diff main...t/T2355 -- RBM3D/Test/Axioms.lean | grep '^[-+][^-+]' | cut -c1-60
 RBM3D/Test/Axioms.lean          |    1 -
 RBM3D/Universality/QUEFlow.lean | 1003 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 1003 insertions(+), 1 deletion(-)
-   `RBM.Univ.UNG2bRowk, -- (T2282, UN-51g: owed; owner UN-5
$ diff <(QUECore.lean 197-355,405-418,430-516,520-589,595-657, queCore_->QUEFlow_) <(RBM3D/Universality/QUEFlow.lean:50-451)   # copied part vs source
401a402
> 
$ git log -1 --format=%h main -- RBM3D/Main/QUECore.lean RBM3D/Universality/OUInterfaceK.lean; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h
5b55824
9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/QUEFlow.lean   # (no output)
```

Narrative (b):
1. `g2bRowk : ∀ K P, UNG2bRowk K P` and `g2bRow : UNG2bRow` are proved in the new file `RBM3D/Universality/QUEFlow.lean` (1003 lines; commits 0121e07, 6bbcb2a, 5661068). `wc -l` at the section commits: 996 (0121e07), 1003 after; stop size 1400 not reached. Axioms: the three standard ones. No hypothesis added, no signature changed: `UNG2bRowk` is the pinned Prop, and the check-file equality compiles (exit 0).
2. Layout: 1-47 header; §1 (48-451) private copies of the spectral lemmas, trace algebra, observable `B_c` and block-trace lemmas of `QUECore.lean` (diff above: renaming `queCore_`→`QUEFlow_` plus one blank line); §2 (452-721) generic core `QUEFlow_core` = `queX_core` for any probability measure `P` and Hermitian-valued measurable `Hm`, profiles `PM`, `PP` abstract; §3 (722-846) `QUEFlow_queBad_sub` and `QUEFlow_queFixed` (generic `queFixed`, first conjunct only: `UNOUQUEk` has only the `queBadMat` event); §4 (848-891) uniformization lemma and measurability of `ouMatC` (copies of `OUInterfaceK.lean:115-145` and `:159-166`); §5 (892-955) targets; §6 (956-1003) instances.
3. Size against the ticket: `QUEFlow_queFixed` itself is 815-845, within the ticket's 200 lines. As 1a (i-a) item 2 reported, the merged `queX_core`/`queBad_sub` are stated for `Sizes.seqP`/`sz.Gn`/`sz.seqXmat` and use file-private helpers, so §1-§3 (404 + 270 + 126 lines, 44 private declarations) are copies or adaptations; 1003 lies between the ticket's 850 and 1200.
4. Proof of `g2bRowk` (898-949): `UNOUProfRowk` at `(𝔡, κ)` gives `C`; `UNOUEq747k` at `τ = τ_Q/2` is uniformized over `T n = {(t, E) | 0 ≤ t ≤ ouTStar sz τ_U n}` (nonempty by `(0, 0)`); `queDomain` at `κ' = 1`, `ε₀ = 𝔡/3`, `E = 0` gives `0 < η_Q ≤ 1` (independent of the given `κ`); `queChain` at `(𝔡/3, 𝔡/6, τ_Q, C)` gives the exponent bound `queBound (sz.W n) 𝔡 (𝔡/3) (𝔡/6) τ_Q`; `hA.2.2.2.2` gives `0 < lam ≤ 𝔡⁻¹`; `ouZeta t ∈ [0, 1]` by `ZeroModeProfile_ouZeta_nonneg`/`_le_one`; then `QUEFlow_queFixed` at `ouP (K.M sz).toUNModel n`, `ouMatC (K.M sz) n t`. `ouEtaQ sz 𝔡 n = etaQ sz n (𝔡/3)` is `rfl` (`inst_ouEtaQ`). `hτU : 0 < τU` occurs only in the `intro` (grep, line 899); no `τ_U ≤ ouTauMax` is used.
5. Instances: `example`s of `g2bRowk` and `g2bRow` at `d = 3`, `sz0`, `UNKind.band 3`, `(𝔠, 𝔡) = (1/6, 1/10)`, `τ_U = 1/1000`: `3 ≤ d`, `UNOUProfRowk` (`unOUProfRowk_band`), `Admissible` (`sz0_admissible`), `τ_U > 0` (and `τ_U ≤ ouTauMax = 1/720` for `g2bRow`) discharged; `UNOUEq747k`/`UNOUEq747` (UN-51's pin; limit check in 1a (ii)) stay hypotheses. They are anonymous `example`s because the first version (commit 0121e07) had named theorems and failed the registry pre-check with `error: axiom audit: 2 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`: [RBM.Univ.UNOUEq747k, RBM.Univ.UNOUEq747]`; adding them to `Test/Axioms.lean` is outside the ticket's one line. Named and premise-free: `inst_ouEtaQ`, `inst_exponent` (the identity of the ticket at `𝔡 = 1/10`), `inst_queBound` (the same in `queBound` form).
6. Registry: the owed line `RBM.Univ.UNG2bRowk` is deleted (diff above). The scan printed `131 owed` before and `130 owed` after rebuilding `RBM3D.Test.Axioms` (tool log); `grep -c UNG2bRowk` on the scan output is 0. `UNG2bRow` is not a registry name. The whole-library `lake build` above ran with `import RBM3D.Universality.QUEFlow` added temporarily to `RBM3D.lean` (the hub adds it at merge) and `RBM3D.lean` restored afterwards (`git status --short` empty).
7. No edit of `QUEFromQDiff.lean`, `QUECore.lean`, `OUInterfaceK.lean` (diff stat above). Ports: no RBM1D/RBM2D text copied; RBM2D `Universality/QUEFlow.lean` (HEAD `9e0f275`) was used only as a route (`grep -n` of its declaration names, no diff to report); all copied text is from RBM3D `Main/QUECore.lean` and `OUInterfaceK.lean` (last commit on main touching them: `5b55824`).

## (c) Verified names (each `#check`ed in `names.lean`, exit 0; plus compiled in the build)

Mathlib: `MeasureTheory.Integrable.of_bound`, `Finset.measurable_sum`, `Measurable.add_const`, `Measurable.pow_const`; `MeasureTheory.integral_finsetSum`, `MeasureTheory.integrable_finsetSum`, `MeasureTheory.integral_const_mul`; root-namespace `integral_re`, `integral_conj` (with `open MeasureTheory`); `MeasureTheory.integral_sub`, `MeasureTheory.integral_add`; `RCLike.norm_conj`, `Complex.conjCLE`, `Complex.measurable_ofReal`, `Complex.re_le_norm`; `Finset.sum_le_card_nsmul`; `Matrix.IsHermitian.eigenvectorBasis`, `Matrix.IsHermitian.mulVec_eigenvectorBasis`; `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `ENNReal.ofReal_le_ofReal`.
RBM3D: `RBM.Gauss.walk_measurable_Gres_apply`, `RBM.Ind.norm_apply_le_l2_opNorm`, `RBM.Ind.ContinuityNet.cont_Gres_true_eq_green`, `RBM.Endpoints.{normSq_le_trace, queMarkov, queDomain, queChain, locDomain_im_pos}`, `RBM.Univ.{ZeroModeProfile_ouZeta_nonneg, ouMatC_isHermitian, measurable_ouMat, ouMatC_eq_ouMat_add}`.
Verified absent (unknown identifier in `names.lean`): `MeasureTheory.integral_re`, `MeasureTheory.integral_conj`, `RBM.walk_measurable_Gres_apply` (the first two live in the root namespace, the third in `RBM.Gauss`).

## (d) Open issues, paper-delta candidates

- `T2355a`: none. `g2bRowk` is the pinned `UNG2bRowk`; no Lean/paper difference arises here.
- `UNOUEq747k` and `UNOUEq747` are in no list of `RBM.Audit` (error text in narrative 5). Any named theorem with either as a hypothesis fails the registry scan until a later ticket classifies them (they are UN-51's pins, owed); the instances here are `example`s for that reason. No action is needed for this merge.
- The generic copy is private. A consumer that needs a generic `queX_core` or `queBad_sub` on a non-`Sizes.seqP` carrier (UN-52b, BA) would need a ticket that makes it public; `g2bRowk` already covers every kind and profile.
- Observation: `hτU` is unused in the proof of `g2bRowk` (the range `t ≤ ouTStar` enters only through the hypothesis `UNOUEq747k`).
