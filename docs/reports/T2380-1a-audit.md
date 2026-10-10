Auditor model: claude-opus-5-5
# T2380 (BA-K07, `BA/KPure.lean`) — 1a-audit (design gate), Sat Oct 10 11:11:48 UTC 2026

Input: `docs/reports/T2380-prove.md` section (a) (108 lines, ≤ 120), ticket `docs/tickets/T2380.md`. main = 06f6e38, t/T2380 = 442d3aa.
No Lean on the branch: `git diff --stat main...t/T2380` prints nothing. Stop line 2000 not reachable yet (no file).

## 1. Numerics rerun (binding deliverable (iii), instance (ii))
Scripts copied from the prover's `$S=…/scratchpad/T2380` into `$S/audit/` and rerun there; outputs diffed against the prover's saved outputs (which are the blocks pasted in the report):
```
$ cd $S/audit; for f in inst3d decay pure conn term; do python3 $f.py > $f.out 2>&1; done
$ for f in inst3d decay pure conn term; do echo "== $f"; diff $f.out $S/${f}_out.txt && echo identical; done
== inst3d
identical
== decay
identical
== pure
identical
== conn
identical
== term
identical
```
All five outputs match the report byte for byte. Rows checked against the claims (from the rerun output):
- `decay.py`: 16 rows (BA-A, BA-B × n = 3..6). Observed `min slope_obs` is 1.21..1.41 (BA-A) against the claimed `c = 0.164`, and 0.26..0.36 (BA-B) against `0.045`. `max C_obs` is ≤ 4.92e-01 against log10 C = 55..277. Pure σ is in every row; alternating σ is in n = 4, 6 (none exists cyclically for odd n).
- `pure.py`: `layers pi!=empty (nonempty): []` for constant σ in all 8 rows; first-stage err ≤ 1.4e-16; `slope_obs` 1.15..1.51 / 0.32..0.38 ≥ claimed `c_K` 0.164 / 0.045.
- `conn.py`: slot graph (chords + M-edges) has 1 component for n = 3..8. Controls: M only gives up to n−2 components, chords only up to 2n−3. `edges = n+3|F|`, `slots = n+2|F|`.
- `term.py`: 0 violations of (1) edge product, (2) reference-slot path bound, (3) the `e^{-rT}` split, over 1800/4200/8400/20100 cases; max ratios ≤ 1.00.
- `inst3d.py` (d=3, L=4, g=.5, E=.3, t=.5, W=2): hypotheses hold (κ = 0.681 > 0, BASelf residual 2.3e-16); edge ratios `max|entry|e^{r|x-y|}/B` ≤ 4.08e-29 ≤ 1.
Tolerance is stated (identities 1e-12, inequalities exact). No ODE. Data are the T2374/T2376 mirrors (`mirror.py`, `mgraph.py`, `kode.py`, `k6.py`).

Independent hand check of the Lean constants at `(d,Λ,κ) = (3,10,0.6814)`:
- c₀ = min(log(1+κ/120), κ/2) = 5.662e-3;
- C_M = 144/κ³ = 455.1, A = 4(C_M/c₀)² = 2.58e10;
- S = expC 1 c₀ = 256·(1+24/c₀⁴) = 5.98e12;
- BAp5s_rate = (κ²/4)²c₀/(2AΛ²S) = 2.47e-30.
These agree with the table.

## 2. Statements vs consumers (deliverable (i)): Lean signatures read on main
```
$ grep -n … (verbatim hits)
RBM3D/Loop/KLIndStepA.lean:1050:def SigDecayAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)]
RBM3D/Loop/KLIndStepB.lean:879:theorem indStepAbs_of (d n : ℕ) [NeZero n] (gmax : ℝ) {ι : Type} (L : ι → ℕ) [∀ i, NeZero (L i)]
RBM3D/Loop/KLIndStepB.lean:882:    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH)
RBM3D/Loop/KLIndStepB.lean:883:    (hD : SigDecayAbs d n L Sig) (hS : SigSumZeroAbs d n L g t Sig) :
133:theorem baK_eq_sum_Kpi (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ)
134:    {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n]
135:    (hn : 3 ≤ n) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
RBM3D/Loop/KLTree.lean:337:  F.filter fun J => σ J.1 ≠ σ J.2
RBM3D/BA/KCactus.lean:452:  fun v => BAThetaOf M t (σ v) (σ (v + 1))
RBM3D/BA/KCactus.lean:459:  Sum.elim (fun J => (t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) (fun s => M (BAMcharge F σ s))
RBM3D/BA/Prop5Short.lean:609:    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
RBM3D/BA/CombesThomas.lean:546:        (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) := by
RBM3D/Loop/PureLoop.lean:144:theorem sum_exp_decay_centre (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
RBM3D/BA/KCactus.lean:113:theorem BAslot_card (F : Finset (Fin n × Fin n)) : Fintype.card (BAslot F) = n + 2 * F.card := by
RBM3D/BA/KCactus.lean:403:theorem BAnextSlot_orbit (s t : BAslot F) :
RBM3D/Loop/KLTree.lean:606:theorem KLleafPar_root (F : Finset (Fin n × Fin n)) {v : Fin n} (hv : v.val = n - 1) :
RBM3D/Loop/KLMolecule.lean:86:private theorem KLMolecule_anc_step {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
RBM3D/Loop/KLMolecule.lean:584:theorem KLMolecule_exists_pair (a : Fin n → Zd d L) :
RBM3D/BA/KSolve.lean:558:theorem BAMsigma_shift (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
RBM3D/BA/MFixedPoint.lean:893:def P : FlowPt 4 10 := (exists_flowPt 4 (g := 10) (by norm_num)).some
```
Checks:
- **`baSig_decay`.**
  - `SigDecayAbs` quantifies `∀ i σ δ` with one `(C,c)`. The 1a fixes **every σ**, uniformly over the family under `∀ i, 3 ≤ L i, 0<g i≤Λ, BAReal, 0≤t i≤1`. This is exactly what `indStepAbs_of` (hD) consumes, and its `hr` (t<1) implies the family hypotheses.
  - Every σ is sound: `BASig = BASigmaPi … σ ∅`; on the layer π = ∅, `KLFlong F σ = ∅`, so every chord is same-charge (`KLMolecule_same_charge`). Each chord weight is then `t·Θ^{σσ}`, which `baProp5s_of_real` bounds for `t ≤ 1`.
  - Not a special case: it covers the general target.
- **`baPure_loop`.**
  - The quantifier order (∃C,c, then ∀L≥3, W, g∈(0,Λ], E, m, BAReal, t∈[0,1), σ₀, a) matches the probe pin `BAKBoundAt` (`t/T2360:RBM3D/Probe/T2360Pins.lean:38`, read): constants first, `t<1`, `g ≤ Λ`.
  - The factor `((W:ℝ)^d)⁻¹^(n−1)` matches `(eq_K-Kpi)` in `baK_eq_sum_Kpi`. For constant σ, `KLTSPlong n σ π = ∅` for π ≠ ∅ (filter at KLTree:337; `pure.py` confirms that no layer is nonempty). The leaf weights are `Θ^{σ₀σ₀}` (KCactus:452).
- **Edge bounds `baPure_edge`.**
  - (a) Both branches of `BAPropM3_of_real` are dominated by `B e^{-r|x−y|}`, because `B ≥ max(1, c₀⁻¹)` and `r ≤ min(c₀, log 2)`. `M(−) = Mᴴ` uses `zdistD_neg`.
  - (b, c) `C₅(1_{a=0} + g²e^{-c_s|a|}) ≤ C₅(1+Λ²)e^{-c_s|a|}`, with translation via `BAMsigma_shift` and `|t| ≤ 1`. Correct.
- **Reduction.**
  - `λ = r/(4N₀)` with `|δ_i − β s| ≤ 2T` gives `Σ_s λ|δ_i−β s| ≤ 2N₀λT = (r/2)T`. Together with `(r/4)D ≤ (r/2)T`, this gives `rT ≥ (r/4)D + Σλ|…|` (verified by hand).
  - `S₀ = expC (d−2) λ ≥ 1` (from the definition of `expC`), and `|F| ≤ n²`, so `N ≤ N₀` and `E ≤ E₀`, using `B ≥ 1`.
  - The pure-loop convolution `c = r/4`, `r − c ≥ r/2` holds by `KLMolecule_exists_pair` and the triangle inequality.
  - Each cited merged name exists (hits above).
- **No hidden hypothesis or cycle in the design.** No structure-field hypotheses are introduced. Inputs are merged (`baPropM_holds`/`BAPropM3_of_real`, `baProp5s_of_real`, K06 `KMolecule`, `PureLoop`). There is no external hypothesis, so no limit check is owed.
- **Names.** `git grep` on main gives 0 hits each for `KPure_ baPureB baPureRate baPure_edge baSlot_path_le baSigmaTree_bound baSigmaPi_empty_bound baSig_decay baK_pure_eq baPure_loop`.
- **Check file.** `lake env lean docs/tickets/checks/T2380-check.lean` in the main worktree reports 0 `error` lines (4.1 s).

## 3. Deliverables (ii) argument, (iv) table, (v) plan
- (ii) Present:
  - the edge bounds with their named constants (`baPureB`, `baPureRate`);
  - the spanning-tree reduction with one label per slot, via the cycle per node (`BAnextSlot_orbit`) plus induction on the chord ancestry (`KLMolecule_anc_step`);
  - the edge count `E = n+3|F|` and slot count `N = n+2|F|`, with the observed max |F| = n−3.
- (iv) The table lists κ, c₀, c_s, C₅, B, r, N₀, E₀, λ, S₀, c, C_Σ, C_K with values at P-like data, constraints and slack.
- (v) The plan has §0–§6 with cumulative estimates of 60 / 260 / 560 / 820 / 950 / 1180 / 1270 lines (central 1250, high 1700), against the binding stop line 2000. It has an internal stop at 1700 before §5 and a fallback for the §2 risk (`baCactus_cut`). The registry pre-check is planned in 1b.
- The 1b instances are planned at `P` (`MFixedPoint.lean:893`), `ι = Unit`, `n = 3, 4`, t = 1/2, W = 2, with distinct labels. These are nondegenerate, and no deterministic hypothesis is left undischarged.

## 4. Observations (no RETURN; carry to 1b)
- O1 (paper-delta coverage, for the 1b report). `baPure_loop` and `baSig_decay` assume `3 ≤ n`, where the paper's `lem_pureloop` (`A:643-647`) gives `c_n, C_n` for every n. `t ∈ [0,1)` is also explicit in Lean. The listed candidates T2380a–c do not include these. The 1b report must add a candidate (e.g. T2380d: n ≥ 3, the range of `baK_eq_sum_Kpi`; the cases n ≤ 2 are K03/K12's explicit formulas, per `A:663`).
- O2. `inst3d.py` labels σ = `+-+` (n=3) as "alternating", but no cyclically alternating σ exists at odd n. The real alternating coverage is n = 4, 6 in `decay.py`. Label only.
- O3. Section (i) cites `indStepAbs_of` as `KLIndStepA.lean:1050`. That line is `SigDecayAbs`; `indStepAbs_of` is at `KLIndStepB.lean:879`. Citation only.
- O4. The Lean rate at Λ = 10 is r = 2.47e-30 (it comes from the merged `BAp5s_rate`), and log10 C_Σ is 3577 or more. These are outputs, not hypotheses, so the instance is not vacuous. Consumers use ∃C,c only.
- O5. `BAK_off_le` is listed as an input by the ticket but is not used by the design. That is harmless.

## 5. Verdict
| target (as fixed by 1a) | verdict |
|---|---|
| `baPureB`, `baPureRate`, `baPure_edge` | PASS |
| `baSlot_path_le`, `baSigmaTree_bound`, `baSigmaPi_empty_bound` | PASS |
| `baSig_decay` (`SigDecayAbs` at `BASig`, every σ) | PASS |
| `baK_pure_eq`, `baPure_loop` | PASS (O1 to be covered in the 1b report) |
| instances at `P`, n = 3, 4 (planned) | PASS (design) |

**Overall: PASS.** All stage-1a deliverables (i)–(v) are met. The numerics reproduce identically and contradict no claimed rate or prefactor. No binding stop line is hit. No pin repair and no REQ is needed. No dispatcher sign-off is needed.
