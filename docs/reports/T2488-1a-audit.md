Auditor model: claude-opus-5-5

# T2488 (L3d1 `BAAnpLift`): 1a-audit (design gate G4): Tue Oct 13 04:34:03 UTC 2026

Input: `docs/reports/T2488-prove.md` section (a) (92 lines), ticket `docs/tickets/T2488.md`, check `docs/tickets/checks/T2488-check.lean`.
`main` = `t/T2488` = 2cc78196. `git diff --stat main...t/T2488` is empty, so there is no Lean on the branch (correct for stage 1a). No probe step.

## 1. The numerics script, rerun
`python3 -I .../scratchpad/T2488/inst.py` (the preflight's script, rerun unchanged):
```text
n=0: L,W,N = 4 32 2097152 = 2^21
baPQ: nM = 1 |molSolid| = 4 auxOrd = 2 p = 2 nM<=p: True
C = 4 c = 1/5 | nngh = 2 k = ord-nngh = 0 M = q+|k|+p = 3
eta_t >= (1-t)*kappa = 1/4  (T0>1/2: half_lt_t0, so (1-T0)kappa < 1/4)
theta_0 = (W^d eta)^-1 <= 1.2207e-04 ; (W^d)^nM*(W^d eta)^-nM = eta^-nM: True
D1 floor = 12
1/10  1/80   True (1/80)  1.1996  1.726<=2.071     2.071 vs 4     2
1/2   1/16   True (1/16)  2.4837  15.322<=38.055   38.055 vs 4    0
1     1/8    True (1/8)   6.1688  234.753<=1448.155 1448.155 vs 4 0
final inequality C*x^(q+k+nngh) <= N^tau at tau=1/2,n=0: 61.29 <= 1448.15
xi=c0=9.766e-04: xi<=Phi0=W^-1/2=0.1768, sum_b xi^2=6.104e-05<=theta=1.221e-04 ; Gamma_a.val=5.821e-11 <= C theta^q psi^k prod psi = 2.338e-04 : True
```
This matches the report's lines 29-41 (spacing differs only). The script's inputs, checked against the merged texts:
- `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5` (`Defs/Sizes.lean`; `sz0_values`: `size 0 = 2097152`).
- `localReg2_inst_Q` (`LocalRegular2:1934-1938`): 4 solid edges `inl0-inr0` (2), `inr1-inl1` (2); waved `inr0-inr1`. So there is one internal molecule `{α,β}` and `n_M = 1`, which the merged `baPQ` example (`BAAtom2`, `baPQ.g.nM ≤ 2` by `decide`) confirms.
- `C = ∏ max 1 |𝔓_j|`, `c = (1+Σ|𝔓_j|)⁻¹` (`AnpKey6:862-868`).
- `η = (1-t) Im m` (`etaOf`, `GLoopFlow:58`; `ztOf_im`).
- `half_lt_t0` (`FlowPins:1254`) and `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`:1214`).
- The threshold `C ≤ N_0^{τ/2} ⇔ τ ≥ 4/21` holds: `4 ≤ 2^{21τ/2}`.

## 2. Check file and census (name level, ticket "At the 1a-audit")
```text
$ lake env lean docs/tickets/checks/T2488-check.lean   (main worktree)   -> exit=0, error lines: 0
$ for f in AnpKey AnpKey2..6: grep -cE 'Prec|STFlow|etaT|lemT|seqP'; wc -l
AnpKey 9 945 | AnpKey2 0 2057 | AnpKey3 0 714 | AnpKey4 0 878 | AnpKey5 0 1427 | AnpKey6 4 1136 | total 7157
```
The report's census correction of the ticket's "10 / 5" to 9 / 4 is right. Visibility of each lift ingredient (`grep -nE "^(private )?theorem <n>"`):

| ingredient | file:line | use in 1b |
|---|---|---|
| `anpKey_prod_ite_mul`, `anpKey_rescale`, `anpKey_stochDomAt_congr` | `AnpKey:661, 672, 806` (**private**) | `open private … from RBM3D.Graph.AnpKey` or `BAAnpLift_` stem copies |
| `anpKey_ghostOK_of_noGhost`, `anpKey_noGhostPath_of_noGhost`, `anpKey_nngh_of_noGhost` | `AnpKey:782, 793, 799` | public, imported |
| `anpDetGh_holds` (model-free: `AnpDetGhAt` quantifies `L ψ θ ξ`, no law) | `AnpKey6:862`; def `AnpKey:41-57` | public |
| `BAMomentGen_whp_of_prec` (any `μ`, `PrecL`) | `BAMomentGen:179` | public (replaces `Prec.whp`) |
| `HighProbAt.inter` (needs `Tendsto size`), `StochDomAt.precomp_param` | `Defs/StochDomAt:571, 335` | public, law-generic |
| `BAExp14a_eta_pos (hκ) (hflow : BAFlow …) n (0 ≤ t) (t ≤ BAflowT0 …)` | `BAExp14a:1266` | public (replaces `etaT_pos`) |
| `baAuxNested_holds` | `BAAtom2:647` | public |
| `baLWMomentOfAnp_closed : ∀ d, BALWMomentOfAnp d` | `BAMomentExpGen:189` | public (4 (a)) |
| `baLWMomentExp_of_anp : ∀ d, BALWMomentExpOfAnp d` | `BAMomentExpGenB:1207` (on `main`) | public (4 (b)) |

`PrecL sz μ := StochDomAt μ sz.size` (`Chain/Carrier:51`). `BAFlow := sz.Admissible 𝔠 𝔡 ∧ …` (`FlowPins:389`). `Admissible := 0<𝔠 ∧ 0<𝔡 ∧ SizeTendsto ∧ …` (`Sizes:177-178`). So `hflow.1.2.2.1 : SizeTendsto`, as in the band (`STFlow`, `Induction/Defs:286`).

Name clash (the names fixed here: `BAAnpKeyGhG`, `baAnpKeyGhG_holds`, `BAAnpG`, `baAnpG_holds`, `baAnpAuxG_holds`, `baLWMoment_closed`, `baLWMomentExp_closed`, stem `BAAnpLift`, `T2488`):
```text
$ git grep -cE '<names>' <b> -- RBM3D RBM3D.lean   for b in main and every t/T246*..t/T2488 (40 refs)
main files_with_hits=0 ... t/T2483b 0, t/T2484b 0, t/T2485 0, t/T2487 0, t/T2488 0   (all 40: 0)
```

## 3. Statement-level checks of the plan
- **Target 3 = the merged pin.** `BAAnpAuxG` (`BAAuxGraph2B:865-878`) is the `BAAnpAux` text (`BAAtom2:677-687`) with these substitutions: `STFlow→BAFlow`, `lemT→BAflowT0`, `LWXi→LWXigL (baFMz sz z) (seqP (sz.withLam 0))`, `Prec→PrecL … (seqP (sz.withLam 0))`, `etaT→(baFMz sz z).eta`. The rest is identical: `∃ c` before `∀ 𝔠 sz z`, `n_M ≤ p`, the exponents `nM`, `p`, `auxOrd - p`. The route of `baAnpAux_holds` (`BAAtom2:694-708`) uses only `baAuxNested_holds`, the band statement at `Γa`, and `(hξ.1 n u v ω).2` (symmetry). `LWXigL`'s first conjunct is the same `0 ≤ ξ ∧ ξ αβ = ξ βα` (`BAAuxGraph2:1036`). So the route transfers once target 2 holds at the carrier.
- **Target 1 lift.** The band lift `lwAnpKeyGh_of_det` (`AnpKey:689-770`) reads the flow at only two points: `hflow.1.2.2.1` (size) and `etaT_pos` via `hflow.2 n`, `htT` (lines 693-702). Every other step is `HighProbAt.inter` of two `Prec.whp`, then the deterministic bound and `measure_mono`. `BAExp14a_eta_pos` takes exactly the premises `hκ, hflow, ht0 n, htT n` of the `BAAnpKeyGhG` shape. So the switch condition (a) is **not met**.
- **G4-a against `B:491-497`** (paper text read). `B:494` "summation over non-centre vertices" and `B:496` "Cauchy–Schwarz with `(eq:Gbyxi2_BA)` … factor `η_t^{-1}`" map as follows:
  - G3 (`baGtoAG_holds`, `BAAtom2:395-412`) bounds every solid edge with endpoints in the `R`-balls by `ξ a b` (premise `:404-406`). Its output is `(W^d)^{nM} · auxVal ξ (centre labels)`. `auxVal`/`auxOrd` are the shadow's (`BAAtom:71, 75`). No atom sum is left in `auxVal`.
  - The row sum `Σ_β ξ² ≺ (W^d η)⁻¹` is the third conjunct of `LWXigL` (`BAAuxGraph2:1041-1042`) and the hypothesis `Σ_β ξ² ≤ θ` of `AnpDetGhAt`.
  - Then `(W^d)^{nM}(W^d η)^{-nM} = η^{-nM}` (script True). That is the paper's `η_t^{-1}` per molecule.
  - No term of `B:491-497` falls outside these. The stop line "G4 fails" is **not hit**, and switch condition (b) is **not met**: the proof is the nested form plus the band lift, and no new estimate is needed.
- **G4-c.** `BALWMomentOfAnp d := BAAnpAuxG d → BALWMoment d` (`BAMomentGenB:362`) and `BALWMomentExpOfAnp d := BAAnpAuxG d → BALWMomentExp d` (`BAMomentExpGenB:1202`) read exactly the pin. The 4 (a)/(b) closures are one-line compositions with `baLWMomentOfAnp_closed` / `baLWMomentExp_of_anp`. 4 (b) uses only the statement of `baLWMomentExp_of_anp`, so that stop line is not hit.
  - Every `BAAnpAuxG` occurrence on `main` is a def or an `example` hypothesis (`grep -rn`: `BAAuxGraph2B:865, 979`; `BAMomentGenB:362, 473`; `BAMomentExpGen:982`; `BAMomentExpGenB:1202, 1288, 1294, 1317`).
  - `grep -c "BAAnpAuxG\|BALWMoment\|BAAnpKeyGhG" Test/Axioms.lean` = 0. Registry: none.
- **Start decision.** L3d2b-2 is merged: `git log -1 main -- RBM3D/Graph/BAMomentExpGenB.lean` = `2cc78196 T2483: merge L3d2b-2 …`, and `RBM3D.lean:571 import RBM3D.Graph.BAMomentExpGenB`. So 4 (b) is **included**, as the report states (line 5).
- **UBA-C1.** `grep -cE "sz\.lam|withLam|gK|lam0"` returns 0 on `AnpKey:658-836`, 0 on `BAAtom2:677-708` and 0 on `LWPins:355-424`. In `BAAuxGraph2B:865-880` the only hits are the law `seqP (sz.withLam 0)` (lines 874-875).
  - `LWPsiAll`/`LWClass` read `sz.W` only (`LWPsi:52-66`).
  - No crossing, so R1 is not needed.
- **Instance plan 5 (i).** T2435's example `BAAuxGraph2B:979` already applies `h6 : BAAnpAuxG 3` at `baPQ` with `ζ` from `baZetaClaim_holds`. Its data (`BAAuxGraph2B_Φ0`, `_R0`, `_ρ0`, `_psiAll`, `:900-940`) is **private**, so the planned re-derivation (40 lines) is needed and feasible. 5 (iii)/(iv) take their data from the instances at `BAMomentGenB:473` and `BAMomentExpGenB:1288`. Only other gates' pins stay hypotheses (`LWLoop2gL`, the entry law, `STInitialGT2gL`, `LWLoopExpgL`). None is degenerate (`N = 2^21`, `p = 2`, `n_M = 1`).

## 4. H250 (4) deliverables table and design gate G4
| # | deliverable | report line | audit |
|---|---|---|---|
| (i) | exponent table: `τ'`, `M`, `C ≤ N^{τ/2}`, `c ≤ 1`, `(W^d)^{nM}(W^dη)^{-nM}`, `η_t ≥ (1-T₀)κ` | 7-23 | met; values reproduced (§1) |
| (ii) | instance + script (`N=2^21`, `t=1/2`, `baPQ`: `p=2`, `nM=1`, `ord^aux=2`) | 25-43 | met; rerun identical |
| (iii) | G4-a (i)-(iv) against `B:491-497` and merged texts | 45-50 | met (§3) |
| (iv) | G4-c consumer table + start-decision rule of 4 (b) | 5, 52-57 | met; 4 (b) included at 2cc78196 |
| (v) | UBA-C1 and hypothesis tables | 59-67 | met (§3) |
| (vi) | lines vs 2,000; 1,950 split; L40-C3; L40-C4 | 69-79 | met; `wc -l` 847 / 1147 / 1344 reproduced |
| (vii) | switch conditions (a), (b) | 90 | met; both not met (agreed, §3) |

G4 gate: **passes**. No term is left over (§3).

**Switch to `prover-max`.** Conditions (a) and (b) are both **not met**, so the role stays `prover-hard`.

**Pre-signed split L3d1a (1-3) / L3d1b (4-5).** The re-priced central is 425 lines (range 360-560; TLC-4 upper bound 1,105). That is below 1,950 by 1,525. The split is **not triggered**, and the reserve `BAAnpLiftB` (above 1,800) is not needed. The prediction is consistent with the census basis: band references of 113 + 31 + 19 + 35 lines, plus header, closures and re-derived instance data. Stage L stays at 43 / 50, with projection 47.

## 5. Observations (no effect on any deliverable or stop line)
- O1. The script's `ξ = c₀` is a deterministic stand-in that is Ward-admissible, not `ζ`. Its job is to evaluate `AnpDetGhAt` at `Γa`, and that is adequate for (ii). The Lean instance 5 (i) uses `baZetaVar` via `baZetaClaim_holds`.
- O2. The limit check of the entry law cites the T2470 script without rerunning it (report line 43). The entry law is another gate's input and stays a hypothesis here.
- O3. Line-reference drift with no content change: the target-3 route is `BAAtom2:689-708` in (vi) and `694-708` in the ticket; the pin's lines are `BAMomentExpGenB:1202/1207` on `main` against the ticket's `1196-1203` on `t/T2483b`.
- O4. The start decision was recorded at stage 1a (base 2cc78196). It cannot revert, but the 1b report should restate it with the commit, as the ticket requires.
- O5. Paper-delta candidate `T2488a` (`B:494` atom sums live in G3, not in G4) covers the only Lean/paper difference found. The closures 4 (a)/(b) are compositions and add no delta.

## Verdict
**PASS.** Every stage-1a deliverable is met, no binding stop line is hit, and the role stays `prover-hard`. The pre-signed split is not taken. No dispatcher sign-off is needed, so stage 1b may start.
