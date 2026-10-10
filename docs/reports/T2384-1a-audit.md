Auditor model: claude-opus-5-5

# T2384 (BA-K11, `BA/KWardIneq.lean`) — 1a-audit (design gate) — Sat Oct 10 12:22:51 UTC 2026

Input: section (a) of `docs/reports/T2384-prove.md` (68 non-empty lines, limit 120), ticket `docs/tickets/T2384.md`.
`t/T2384` = `2192dea`, `main` = `8609423`; `git diff main...t/T2384` = 0 lines (no Lean yet, as expected at 1a).
Scripts rerun from copies in `scratchpad/T2384/audit/` (sha1 of `k11.py` `012b05cc`, `k11_lattice.py` `adae8a2b`).

## 1. Numerics rerun (binding deliverable (iii))

```
$ cd $A && python3 k11_lattice.py      # (d,L)=(3,4), N=64, W=2, t=1/2, last label summed over Z_4^3
-- (d,L)=(3,4) N=64 g=0.5 E=0.3 t=0.5 W=2: kappa=Im m=0.6814 |m|=0.6881 rowsum|M|^2=1.000000000 |M-M^T|=5e-16 eta_t=0.3407 B_t0=1.3646
   n=2 sg=+-,++: sum_x|K2| = 0.25000, 0.08562 <= W^-d (1-t)^-1 = 0.25000 <= (W^d eta)^-1 = 0.36689
   n=3 sg=+-+,+++,++-: measured C = ... = 0.0444, 0.0135, 0.0431
   n=4 sg=++--,++-+,++++: measured C = ... = 0.0033, 0.0030, 0.0012
   cut n=4 sg=++-+ pi={(0,2)} J=(0,2): sum_x|K^pi(a[x])| = 2.276e-03 <= ... = 6.950e-03 <= ... = 5.252e-02; sum_u|A_u| = 0.093 B (sg_in=++-, n_in=3)
-- (d,L)=(3,4) N=64 g=1.2 E=-0.4 t=0.5 W=2: kappa=Im m=0.5431 |m|=0.5728 rowsum|M|^2=1.000000000 |M-M^T|=1e-15 eta_t=0.2716 B_t0=0.5467
   n=2 sg=+-,++: sum_x|K2| = 0.25000, 0.09039 <= W^-d (1-t)^-1 = 0.25000 <= (W^d eta)^-1 = 0.46029
   n=3 sg=+-+,+++,++-: measured C = ... = 0.0291, 0.0141, 0.0242
   n=4 sg=++--,++-+,++++: measured C = ... = 0.0056, 0.0042, 0.0028
   cut n=4 ... = 5.266e-04 <= ... = 2.487e-03 <= ... = 1.805e-02; sum_u|A_u| = 0.081 B (sg_in=++-, n_in=3)
$ python3 k11_limit.py
t=0.7 n=3 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 0.472/0.634  q=8: 0.503/0.610  q=12: 0.534/0.642  q=16: 0.553/0.663  q=24: 0.572/0.687
t=0.7 n=4 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 0.355/0.129  q=6: 0.354/0.135  q=8: 0.395/0.147  q=12: 0.447/0.166
t=0.99 n=3 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 0.556/1.323  q=8: 0.566/1.274  q=12: 0.580/1.153  q=16: 0.611/1.072  q=24: 0.690/1.007
t=0.99 n=4 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 1.008/0.014  q=6: 1.022/0.017  q=8: 1.045/0.016  q=12: 1.134/0.016
$ python3 k11.py struct
n=4..9, all 77 diagonals J=(i,j): w=j-i in [2,n-2]; n_in=w+1, n_out=n-w+1 in [3,n-1]; (n_in-2)+(n_out-2)=n-2; j<=n-1; inner labels a_i..a_(j-1) avoid a_(n-1); glue vertex != last; last outer vertex = vertex n-1. violations: 0
$ for m in theta empty cut target; do python3 k11.py $m > out_$m.txt; python3 k11.py $m big > out_big_$m.txt; done; python3 summ2.py
q=4 g=0.5 t=0.7 | 0.828 | 1.0000,1.0000 | 0.77 | 0.828 | 0.47/0.35/0.03 | 0.63/0.13/0.08 | 0.39/0.29/0.02 | -/0.10/0.08 | 0.39/0.29/0.18 | -/0.91/0.94
q=3 g=1.1 t=0.6 | 0.556 | 1.0000,1.0000 | 1.11 | 0.556 | 0.87/1.17/0.40 | 1.01/0.50/0.71 | 0.48/0.65/0.22 | -/0.21/0.28 | 0.48/0.65/0.76 | -/0.90/0.96
q=5 g=0.8 t=0.95 | 0.700 | 1.0000,1.0000 | 0.92 | 0.700 | 0.63/0.81/- | 1.44/0.11/- | 0.44/0.53/- | -/0.24/- | 0.44/0.53/- | -/0.99/-
q=4 g=0.5 t=0.3 | 0.828 | 1.0000,1.0000 | 0.89 | 0.828 | 0.63/0.49/0.19 | 0.72/0.36/0.22 | 0.52/0.41/0.16 | -/0.07/0.06 | 0.52/0.41/0.27 | -/0.74/0.85
q=4 g=4.67 t=0.7 | 0.693 | 1.0000,1.0000 | 1.00 | 0.693 | 1.59/4.30/0.78 | 2.61/2.10/1.30 | 1.10/2.98/0.54 | -/1.22/3.30 | 1.10/2.98/6.12 | -/1.00/1.00
q=4 g=0.05 t=0.9 | 0.986 | 1.0000,1.0000 | 0.54 | 0.986 | 0.42/0.33/0.05 | 0.75/0.03/0.09 | 0.41/0.32/0.05 | -/0.15/0.12 | 0.41/0.32/0.19 | -/0.99/1.00
max relative identity defect (K0 = sum_b Theta X_b; K^pi = form1; sum_F Gamma = sum_pi K^pi) over all runs: 1.5e-14
$ for f in out_{theta,empty,cut,target} out_big_{theta,empty,cut,target}; do cmp -s audit/$f.txt ../$f.txt && echo "$f identical"; done
out_theta identical / out_empty identical / out_cut identical / out_target identical
out_big_theta identical / out_big_empty identical / out_big_cut identical / out_big_target identical
```
All scripts exit 0 with their `assert`s active (identities `< 1e-12`, chains `lhs <= rhs`). Every number in (a) reproduces.
Coverage vs (iii): n = 2..5 (q <= 4), every sigma, every layer, every innermost J, every a; identities 1.5e-14 <= 1e-12; bounds as
measured constants; mirrors are T2381's (`k6.py`, `k10.py`, `k10_lattice.py`, ...). `(d,L)=(3,4)` run is a genuine Z_4^3 lattice.

## 2. Written argument (deliverable (ii)) against the paper and the merged signatures

Paper `A_deterministic_estimates.tex:811-826` (proof of `lem_wardineq_K`): (eq_K-Kpi) + (eq:THETAinftinf) + (eq:ind-step-bound) + induction
on molecules; no Ward identity. `1_2:721`: `eta_t = (1-t) Im m`. So (a)'s D3 ("`baK_ward` does not enter") is borne out; `BA/KWard.lean:303-305`
uses the same `eta_t = (1-t) Im(PropSpin m true)`.

Signatures checked on `t/T2384` (script `grep -n`):
```
BA/KInduct.lean:55  def BAKBoundAt (d n) (Λ κ) : ∀τ>0 ∃C>0 ∀ L≥3, W≥1, g∈(0,Λ], E m, BAReal → t∈[0,1) → ∀σ a, ‖BAKsol …‖ ≤ C L^τ (W^-d B)^(n-1)
BA/KInduct.lean:88  theorem baKsol_two … = W^-d (BATheta … σ0 σ1 * BAMss …) a0 a1
BA/KInduct.lean:627 theorem baKpi_cut (hn: 3≤n) (M) (t) σ hF₀ hπ (hJπ) (hinner) a : BAKpi … π = Σ_u t * (A u) * BAKpi (n-w+1) (sigmaOut) (BAdeltaOut J a u) π'
BA/KInduct.lean:758 theorem baKpi_empty_slice M t σ a r : BAKpi … ∅ = Σ_b BAThetaOf … (σ r) (σ (r+1)) (a r) b * X_b
BA/KMolecule.lean:133 theorem baK_eq_sum_Kpi … (hn : 3 ≤ n) σ a : BAKsol … = (W^-d)^(n-1) * Σ_{π ⊆ diagonals n} BAKpi … π
Loop/KLIndStepB.lean:77 def IndStepAbs … : ∀τ>0 ∃C>0 ∀ i σ r, σ r ≠ σ (r+1) → ∀ a, Σ_b ‖Σ_{δ r=b} Sig δ ∏_{j≠r} TH‖ ≤ C L^τ Bp^(n-2)
Loop/KLIndStepB.lean:879 theorem indStepAbs_of … (hTH : IndStepTH …) (hD : SigDecayAbs …) (hS : SigSumZeroAbs …) : IndStepAbs …
BA/FlowPins.lean:171,182 BAProp5 (all σ1 σ2, sup C·B_{t,|a|}), BAProp5s (σσ, C(1_{a=0}+g² e^{-c|a|}));  BA/Prop5.lean:987 baP5_neumann (private, copyable)
BA/KBase.lean:371 BATheta_isSymm (BAReal);  BA/KKernel.lean:102,128 BAMss_norm_eq_BAK, BAK_col_sum;  BA/Ward.lean:136 BAm_norm_le_one
BA/MFixedPoint.lean:893 def P : FlowPt 4 10;  :883 field real : BAReal 3 L g0 m0.im E m0;  Loop/PureLoop.lean:144 sum_exp_decay_centre
Loop/KLSumZeroWard.lean:577,594 exists_innermost, Flong_subset_diagonals (public);  BA/KPure.lean:632 (main only) baSig_decay
```
Step-by-step check (auditor's own derivation, matched against band `Loop/KLWardIneq.lean:430,662,675,851,863,898`):
- n = 2: `Σ_x‖K2(a0,x)‖ ≤ W^-d ‖Θ‖_{ℓ∞→ℓ∞} ‖M^{σσ'}‖_{ℓ∞→ℓ∞} ≤ W^-d (1-t)^-1 ≤ (W^d η)^-1` since `‖M^{σσ'}‖ rows = Σ_b BAK = 1` and
  `t‖M^{σσ'}‖ = t < 1` (Neumann for `PropThetaQ = Ring.inverse (1 - t•Q)`, `Propagator/Pins.lean:214`). Attained 1.0000 (rerun). OK.
- Empty layer, root `Fin.last`: `X_b` does not depend on `a_last`; column ℓ¹ of `Θ` = row ℓ¹ (BA symmetry, allowed at BA data by 0350 C2).
  Long last leaf (`σ_last ≠ σ_0` = the `IndStepAbs` root condition at `r = Fin.last`, `r+1 = 0`): `IndAt` at k = n, `η^-1` from `(1-t)^-1 ≤ η^-1`.
  Short last leaf: `S · (1-t)^-1 · (C_d B)^{n-2} · expC^{n-1}`; exponent n-2 correct; short-leaf sup ≤ const ≤ C·B since `B ≥ (Λ²+1)^-1`. OK.
- Cut at innermost long `J`: `σ_i ≠ σ_j` gives the `IndStepAbs` root condition of `sigmaIn`; `A(u)` uses labels `a_i..a_{j-1}` only (struct: 0
  violations), last outer label = `x`; IH at `m'' = n_out-1 ∈ [2,m-1]` over all `π'`; `B^{(n_in-2)+(n_out-2)} = B^{n-2}`, `L^{τ/2}L^{τ/2}`, `η^-1` once. OK.
- Assembly: `(W^-d)^{n-1} η^-1 B^{n-2} = (W^d η)^-1 (W^-d B)^{n-2}`, `2^{|diagonals n|}` layers. OK.
- Orientation (0350 C2): symmetric facts only at BA data (`BATheta_isSymm` under `BAReal`); `baKpi_cut` has no hypothesis on `M`. Not hit.
- Range-uniform (1155 C1): constants from `BAProp5`, `BAProp5s`, Neumann, `IndAt`, `MolAt`, all uniform on `g ∈ (0,Λ]`; no `g ≤ W^-ε`,
  no `‖M - m₀‖` smallness, no `(Cλ)^{|a-b|}`; measured at g = 0.05..4.67. Not hit.

## 3. Statements (deliverable (i)) and consumers

`BAWardIneqAt d n Λ κ` matches `KLwardIneqAt` (`Loop/KLWardIneq.lean:90`) and `(wardineq_K)` (`3_5:1001-1012`): `∀τ ∃C`, binders as
`BAKBoundAt`, `∀σ`, `a : Fin (n-1)`, sum over the last label, `C L^τ (W^d η)^-1 (W^-d B)^{n-2}`, `η = (1-t) Im m`; and the shape of `STKward`
(`Induction/Step34Pins.lean:229`), so K12's `STKwardgL` carrier form can consume it. Consumers listed: K12 and the stage-K close (1155 Q4).
`baWardIneq_holds` is conditional on `KWardIneq_IndAt` (`(eq:ind-step-bound)`, K09b/K12) and `KWardIneq_MolAt` (K07); this matches the paper's
own dependency (`A:809`) and the design order (K11 depends on K02, K10; K12 on K09b, K11: `T2360-design.md:130-133`). Flagged by (a) as
conditional (`T2384c`), not the unconditional lemma — correct labelling. The unconditional form is K12's.
Paper-delta candidates `T2384a` (η, uniform constants), `T2384b` (short last leaf, absent from `A:816-818` which writes `Θ^{(+,-)}`),
`T2384c` (conditional form), reuse `T2381a` (not yet in `docs/paper-deltas.md`: `grep -n T2381a docs/paper-deltas.md` = 0 lines; T2381's).

Instance plan: `P : FlowPt 4 10`, `(d,L)=(3,4)`, W = 2, t = 1/2, τ = 1, n = 2 (no premise), n = 3, 4 at spread labels, n = 4 also
`baWardKpi_step` at layers `∅, {(0,2)}, {(1,3)}`. Nondegenerate; only `IndAt`/`MolAt` (other gates' pins) stay as hypotheses. OK.

## 4. Plan (deliverable (iv)) vs stop line 2000

Section sums recomputed: 120 + 200 = 320; +330 = 650; +65 = 715; +420 = 1135; +140 = 1275; +45 = 1320. Band file `wc -l` = 1083;
band empty layer `:155-523` (368) vs plan 330; band step `:675-851` (176) vs plan 230. 1320 ≤ 1800 (ticket high) < 2000. Not hit.

## 5. Name clash

```
$ grep -rn -e KWardIneq_ -e BAWardIneqAt -e BAWardKpiAt -e baWardIneq_ -e baWardKpi_ -e baWardMol_holds RBM3D | wc -l
       0
```

## 6. Items that need the dispatcher (not defects of the 1a)

- **D1 (registry; differs from the ticket's "Registry: none expected").** Verified: `scanPremises` (`Test/Axioms.lean:416-440`) collects every
  public `RBM` `Prop` def that a theorem assumes and no theorem concludes; `unregistered` fails the build (`:506-510`). The 1a's public premise
  def `KWardIneq_IndAt` is assumed by `baWardKpi_*`/`baWardIneq_holds` and concluded by no theorem until K12, so the full `lake build` at merge
  fails without one `owedProps` line in `Test/Axioms.lean`, which is not a sole writable file (precedent `79dec34` T2368 Amend 1, removed
  at `ab54184`). The alternative (premises stated as `IndStepAbs … (BASig …)` directly, as K10 did, `BA/KInduct.lean:729-951`) needs no line,
  because `indStepAbs_of` concludes `IndStepAbs`; (a) rejects it as hiding the premise from the ledger. Choosing between them changes a
  public statement and a file outside the ticket: dispatcher decision.
- **D2 (branch base).** `t/T2384` = `2192dea` lacks K07 (`baSig_decay`, `BA/KPure.lean:632`, merged at `8609423`). Discharging `MolAt`
  needs `main` merged into the branch before 1b; otherwise `KWardIneq_MolAt` is a second unconcluded premise (a second registry line).
- **D3** (drop `import RBM3D.BA.KWard`, `baK_ward` unused): consistent with the paper; the ticket listed the import as required.

## 7. Observations (no effect on statements, instances, build or deltas)

- Ticket says `Loop/KLWardIneq.lean` has 878 lines; `wc -l` = 1083 (878 is the design's T-line count).
- `T2381a` is cited as reused but is not yet numbered in `docs/paper-deltas.md`.

## Verdict

Every stage-1a deliverable (i)-(iv) is met; numerics reproduce exactly; no binding stop line (2000, 0350 C2, 1155 C1) is hit; no false
statement on the target domain. **PASS**, conditional design (premises `IndAt`, `MolAt`) correctly labelled.
**Needs dispatcher sign-off** before 1b: D1 (owed registry line vs inline `IndStepAbs` premises) and D2 (merge `main` into `t/T2384`).
