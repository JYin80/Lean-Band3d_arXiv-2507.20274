Auditor model: claude-opus-5-5
# T2428 1a-audit (design gate) — Sun Oct 11 23:27:21 UTC 2026
Inputs: ticket `docs/tickets/T2428.md`; report `docs/reports/T2428-prove.md` §(a), §(a″); branch `t/T2428` at `f6c3866`; detached audit worktree `../RBM3D-wt/T2428-1a-audit`. Scratch: scratchpad `T2428/audit/`.

**Verdict: BLOCKED — needs dispatcher sign-off.** Deliverables (i)–(iv), (vi) and section (a) reproduce and are sound. The probe reports in item (v) that the ticket's binding stop line is hit. Clauses (ii)–(iv) of target 4 (b) do not fit the two named files: 3,445 lines predicted for those clauses alone, against a limit of 2,000 per file. I confirm the stop. **Missing input:** the dispatcher's decision on the split of 4 (b) (ii)–(iv). The ticket says "Stop and report (no 1b) … the dispatcher decides the split". Stage 1b must not start until that decision is made. This is not a prover defect, so there is no repair list.

## 1. Probe recompiled (item (i))
```
$ git diff --name-only main...HEAD
RBM3D/Probe/T2428Pins.lean
$ lake env lean RBM3D/Probe/T2428Pins.lean > probe.out 2>&1; echo "exit: $?"      (5.9 s, cached oleans)
exit: 0
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/Probe/T2428Pins.lean ; grep -c 'error\|warning' probe.out
0
0
$ grep -E '^(BATwist|BAuKerSemigroup)' probe.out
BATwistGen : ℕ → Prop
BATwistHier : ℕ → Prop
BAuKerSemigroup : ℕ → Prop
BATwistDuhamel : ℕ → Prop
BATwistGridMartAt : ℕ → ℝ → Prop
BATwistGridMart : ℕ → Prop
$ lake env lean docs/tickets/checks/T2428-check.lean   → exit 0, errors 0
$ lake env lean <scratch>/p1.lean | p2.lean | assemble.lean   (prover's scratch, cited in (a″))
p1.lean exit 0 lines 89 sorry=0 errs=0       (P1_second: line Hessian of Tr(G₁ E G₂ P), Hermitian H, C)
p2.lean exit 0 lines 48 sorry=0 errs=0       (BAuKer_self', BAuKer_comp' = the BAuKerSemigroup pin)
assemble.lean exit 0 lines 351 sorry=0 errs=0 (assemble_scratch : BATwistGridAssemble; file includes copies of the pins)
```

## 2. Statements against the ticket (targets 1–4)
I read the statements against the ticket's mathematics and the merged band pins:
- **Target 1.** The seven TL0 bridges (`twL2'`, `twL3`, `twEG`, `twB1`, `twB2`, `twDer`, `twEE`, probe 102-108) all close by `rfl` at `H = seqHflowBA`, so the conventions are TL0's. `twEEM` uses `(baFM ..).S n`, and `baFM` has `S := fun n => 1` (`BA/FlowPins.lean:327`). This is the coupling-0 walk, as the ticket requires.
- **Target 2 `BATwistGen`.** Hypotheses are `0 < Im m`, `u < 1` and `H` Hermitian, as the ticket specifies. `twGenM` is `genMatOf` (`Induction/LoopGenN.lean:554-560`) with `g = 0` and `L̃` in place of `loopL`. The right side is `W^d Σ_b L̃(b) LM σ ![a,b] + Ẽ^{G̊}`, with `a` first, which is (D.1) at TP:104-108.
- **Target 3 `BATwistHier`.** Hypotheses are `BAReal`, `0 < g₀`, `0 ≤ u < 1` and `H` Hermitian. The drift `twDriftM` is `(BATheta·BAMss) *ᵥ Z + B̃₁ + B̃₂ + Ẽ^{G̊}`. It uses the one-slot kernel, never the diagonal operator.
- **Semigroup pin.** `BAuKer = (1 - sM)Θ_t` (`BA/EKPins.lean:49`), so `Ũ_{v,w}Ũ_{u,v} = Ũ_{u,w}` needs `0 ≤ v,w < 1` only. The pin has exactly that, and scratch `p2.lean` proves it.
- **4 (a) `BATwistDuhamel`.** The identity is pathwise and holds for every `n, σ, c, τ, j` with `j∧τ ≤ K`. It is the exact telescope (`P_i + ξ_{i+1} = A_{i+1} - Ũ A_i`) plus the semigroup law. This matches the ticket.
- **4 (b) `BATwistGridMartAt` / `BATwistGridMart`.** I compared it clause by clause with `STGridMartAtgL` (`Chain/Step2Gen.lean:857-879`) and with the fourth conjunct of `STGridRepNAtgL` (`:994-1028`). The binder order is the same: `κ ε 𝔡`, `𝔠 sz z`, Flow, `s t`, `D`, `∃ CK`, `K`, `∃ Mart Rem`. Clauses (i)–(iii) are the same, and clause (iv) has the same shape, with `STeeUMg` replaced by `twEEUM` (`twU σ ⊗ twU (!σ)` on one slot). `∃ C₀ ≥ 0` sits in front, as in `STGridMartgL` (`:882`). The label is `(σ, a, c₁, c₂)`.
- **"Every d" decision.** It is backed by the compiled `#check` of `baKsol_two`, `BAflow_real` and `BATheta_hasDerivAt`, none of which carries `3 ≤ d`. `3 ≤ L` comes from `Sizes.three_le_L` (`Defs/Sizes.lean:145`).

## 3. Item (iii): drift kernel
```
$ grep -c -E "STthetaOpg|STgDriftg|Step2Gen_ThetaN|Step2Gen_UN" RBM3D/Probe/T2428Pins.lean
0
```
`Step2Gen_thetaKer` and `Step2Gen_uKer` occur only in a section comment (257-258) and in the two compiled bridge `example`s (263-267). Those bridges come from `Step2Kern_thetaKer_BA` and `Step2Kern_uKer_BA`, under the hypothesis `(E n + m).im ≠ 0`. Met.

## 4. Compiled instances (probe 277-299, `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `n = 0`, `σ = (false,true)`, `c₁ = 0`, `c₂ = (1,0,0)`)
- **T.8.** Instantiated at `u = 1/2`, Hermitian `seqHflowBA`, with `BAmF_sz0_im_pos`.
- **T.9.** `BAReal` comes from `BAflow_real` at `(1/2, 1/10, 1/6, 1/10)` and `0 < g₀` from `gI_pos`.
- **Semigroup.** Instantiated at `u, v, w = 2/3, 1/4, 1/2`.
- **4 (a).** Grid `K ≡ 4` on `[1/2, 2/3]`, with `τ ≡ 3` and `j = 3`.
- **4 (b).** `K_n = ⌈N^{CK}⌉ + 1`.
- **Degeneracy.** In every instance the window is `s < t ≤ T0` (`t0_sz0`). None has `N = 0`, an empty index set or a `False` premise.

## 5. Numerics of (a) and (a″) rerun
Command: `python3 <script>` (and `bash neg.sh`) in scratchpad `T2428/`. The outputs match the report digit for digit:
```
datum: N=(WL)^d=2097152  Im m=0.832488 (kappa=1/2 ok: True)  Im z=0.367512 ... T0=0.693740 (>=2/3: True) ... g0=1.301423e-02
datum: mF=...0.999493j: Im mF=0.999493 >= kappa=1/2: True;  self-consistency |mF - tr M^B/L^d| = 2.22e-16 ; Ward 1.55e-15
datum: sigma=(-,+) u=0.6667: max row sum |M^(ss')|=1.000000 <=1, spectral radius=1.000000, ||Theta_u||_inf=3.0000 <= 1/(1-u)=3.0000
datum: window s=0.5<t=0.6667<=T0=0.693740; ... 1/eta_T0=3.267 <= 16N=33554432
duh  : sigma=(-,+): semigroup 2.0e-15; U=1+(u-v)M Theta_u 2.4e-15; dTheta=Theta M Theta 7.0e-09; telescope 1.1e-14; mismatch/D^2 = 8.13
duh  : sigma=(+,+): semigroup 1.6e-15; U=1+(u-v)M Theta_u 1.0e-15; dTheta=Theta M Theta 3.7e-11; telescope 6.8e-15; mismatch/D^2 = 0.43
toy  : (D.1) max rel. residual 3.21e-06 ; (A.3) 4.02e-10 ; (D.4) 3.12e-05 ; (D.2) 6.59e-10
toy  : nondegeneracy: Im m=0.7355, |L~|~1.701e-01, |Z|max~3.004e-01, |EG|~1.989e-02
toy  : (iv) |U~^(!s) - conj U~^(s)|max=2.2e-16; |(U(x)U)o(EE) - sum S|sum U d f|^2|max=5.6e-17; EE min eig=4.15e-02
neg  : control 1 (drop -m(sigma0) in E^G): 7.11e+00 ; control 2 (L^(2) index order (b,a)): 1.06e+00
t8check: worst rel residual 4.5510814467687774e-06 ; control 1 6.730e+00 ; control 2 2.443e-01
qvcheck: (True, False) (0, 0, 1) MC 0.00755 vs twEEM 0.00752 ratio 1.0052 ; (True, True) (1, 2, 0) ratio 1.0000
thr  : need N >= 9.896e+15 ; n= 9 N=2.097e+24 Rem/hbig budgets: True hZ: True ; n_* = 9 ; log10 K_* = 1045.8
```
How to read these: the identities (D.1), (D.2), (D.4) and (A.3) hold at the toy, at the finite-difference precision `h²`. Both negative controls fail by `O(1)`, so the checks discriminate. The `‖Θ_u‖ ≤ (1-u)⁻¹` bound is attained (equality) at `(-,+)`, which agrees with the `u < 1` binding noted at KBase:321. `K_*` is never evaluated: it is a function argument of the pin, as in the band instances.

## 6. Items (ii), (iv), (v), (vi)
```
$ python3 tab2.py | tail -1 ;  python3 pred.py | tail -3
sum of pred: 4945 (pred.py: 4945)
clause (ii) 1380 (966..1932); (iii) 915 (640..1235); (iv) 1150 (805..1552)
as named (two files): TwistGrid 1035, TwistGrid2 465 + clauses (ii)-(iv) 3445 = 3910  vs stop line 2000 per file
T2428 without (ii)-(iv): TwistGrid 1035 (799..1412), TwistGrid2 465 (368..636), both files 1500 vs row estimate 995 / 1404 / 2457
$ wc -l (band basis of clauses (ii)-(iv), main)
Path/DifREP1 1458 ; Path/DifREP2 2623 ; Path/DifREP3 2567 ; Path/OneStep 2429
$ grep -n (item (iv) and the (v) reasons)
RBM3D/Path/Walk.lean:685:theorem gridTransferPT ...
RBM3D/Induction/Step2Core.lean:400:theorem ST_pathP_eq_seqP ...
RBM3D/Induction/Step2Core.lean:422:theorem ST_whp_grid ...
RBM3D/Path/OneStep.lean:2205:theorem oneStepEnvelope : OneStepEnvelope := by
probe.out:232: @Ind.difRepTail_condMGF_Z : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ), |E n| < 2 → ...   (band loops)
$ bash clash.sh names.txt          (main worktree; 47 names × main + 428 branches + T2427/29/30/31 tickets and checks)
names:       47; local branches other than main:      428
NONZERO TwistGrid main=0 other-branches=0 sibling-tickets=4
done
```
- **(ii).** The table covers every range the ticket lists. It also adds `OneStep`, the envelope basis of the Rem clause. The T.8 route is the direct `n = 2` computation (TP:108) with the compiled Hessian `P1_second`. The word calculus is not generalised, and the reason is stated: `P_{c₁c₂}` is not an E-block letter. Met.
- **(iv).** It gives the import list, the `rfl` bridges to TL0's sources and QV, and three merged transfer lemmas, and the line numbers check out. Met.
- **(v).** The lows alone, 966 + 640 + 805 = 2,411, already exceed 2,000. The merged envelope and the conditional-MGF/Y-tail lemmas are stated for loop functionals (above), so the twisted versions are new proofs. Most of 4 (b) (ii)–(iv) rests on `Path/DifREP1` §3–§4, `DifREP2`, `DifREP3` and `OneStep`, and the ticket says these lie outside the row's basis. The stop line is therefore hit, credibly. A split is proposed: T2428 keeps targets 1–3, the semigroup, 4 (a), clause (i) and the assembly, about 1,500 lines over two files, and there are three new rows for (ii), (iii) and (iv), with the pins `BATwistGridRem/Tail/WTail` already compiled (probe 221-251). **The dispatcher decides.**
- **(vi).** No clash. The only hit is `TwistGrid`, which is this ticket's own file stem as it appears in the sibling scans. Met.

## 7. Paper deltas
The difference between the clause (iv) weights at `(u_j, u_k)` and the exact 4 (a) weights `Ũ_{u_{i+1},·}` is assigned to TL2d. This is the band's grid convention, as in `STGridRepNAtgL`. No candidate is proposed yet. The Lean grid form (Azuma in place of BDG) is the existing D90/§7 delta. 1b (or the new rows) must still propose a `T2428a` if any statement departs from (D.1)/(D.4)/(D.5).

## 8. Observations (not defects)
- Probe docstring line 116 lists `3 ≤ L` among T.9's hypotheses, but the pin omits it. This is correct: `Sizes.three_le_L` supplies it.
- The 4 (b) instance leaves `D > 0` as a variable instead of fixing `D = 1`. All deterministic hypotheses are still discharged. 1b should fix `D = 1`.
- §(a) row 7 (the `Z₁^{tw}`, `Z₂^{tw}` budgets) is a hand count and is labelled so. It bears only on clause (ii), which goes to the split.

## Per-target verdict
| target | statement | instance | status |
|---|---|---|---|
| 1 vocabulary + 7 bridges | `rfl` to TL0 | n/a (defs) | design met |
| 2 `BATwistGen` | matches ticket/(D.1) | compiled | design met |
| 3 `BATwistHier` (+ `BAuKerSemigroup`) | matches ticket/(D.4) | compiled | design met |
| 4 (a) `BATwistDuhamel` | matches ticket | compiled | design met |
| 4 (b) `BATwistGridMart` | shape matches band pins | compiled | **BLOCKED: stop line (v) hit; split of (ii)–(iv) needs dispatcher sign-off** |
