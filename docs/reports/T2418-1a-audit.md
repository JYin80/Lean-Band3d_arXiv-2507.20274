Auditor model: claude-opus-5-5

# T2418 1a-audit round 2 (design gate) — Sun Oct 11 13:24:18 UTC 2026 (`date -u`)

Inputs: ticket `docs/tickets/T2418.md`; Amend 1 `docs/tickets/T2418-amend-1.md` (D1-D4, items (i)-(v), namespace/grep); CONTROL H216, H219 (probe step `RBM3D/Probe/T2418Pins.lean`, never merged, <= 400 lines); round-1 list (this file, previous version, items 1-7);
`docs/reports/T2418-prove.md` sections (a), (a′), (a′) probe step. Audit worktree (detached): `/Users/junyin/Lean_proof/RBM3D-wt/T2418-1a-audit2` at `1d302bb`.
Scratch: scratchpad `T2418/aud2_*`.

## 1. Probe compile (repair item (i))
```
$ cd RBM3D-wt/T2418-1a-audit2 && lake build RBM3D.BA.LWPinsBA RBM3D.Graph.BAExpandW | tail -1    # refresh imports (main moved past the merge base)
Build completed successfully (3967 jobs).
$ lake env lean RBM3D/Probe/T2418Pins.lean; echo EXIT=$?
@BAExp14a_F : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (n : ℕ) → ℝ → sz.SeqΩ → Fin 6 → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ
@BAExp14aS1Fam : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (n : ℕ) → ℝ → sz.SeqΩ → Fin 6 → Bool → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ
BAExp14aS1 : ℕ → Prop
'RBM.BA.BAExp14aS1Fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14aS1' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
$ grep -nE "sorry|admit|native_decide|^axiom|^theorem|^lemma" RBM3D/Probe/T2418Pins.lean ; wc -l < RBM3D/Probe/T2418Pins.lean
168
$ git diff --name-only main...t/T2418
RBM3D/Probe/T2418Pins.lean
```
Matches (a′) probe step. The only diff is the H219-authorized probe (168 <= 400 lines). Cited `LWExpTerm4` lines 391/488/746/781/828/1394 checked by `sed`.

## 2. S1 against the consumer `BALWCutExpTw` (Amend 1 (i): carrier, law, `U`, `PrecL`, family list)
```
$ diff <(git show t/T2398:RBM3D/Probe/T2398Pins.lean | sed -n '434,440p') <(sed -n '107,112p' RBM3D/Probe/T2418Pins.lean)
1c1
< def BALWCutExpTw (d : ℕ) : Prop :=
---
> def BAExp14aS1 (d : ℕ) : Prop :=
4,7c4,6
<       STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
<       STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
<       PrecL sz μ (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
<         (fun n p _ => ‖∫ ω, LWcutg (baFMz sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
---
>       STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
>       PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
>         (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
```
- Binders, `3 ≤ d`, `BAFlow`, range `0 ≤ t n ≤ BAflowT0`, `μ = seqP (sz.withLam 0)`, carrier `baFMz`, `U`'s constraint and the bound are identical (lines 2-3 of each block equal).
  Premises: the first two of the consumer's seven, same order; no `𝔼 tr` premise (D1). No hypothesis in a structure field; `BAExp14aS1` is a `def`, no cycle.
- Bound `(1-t)⁻¹B^{5/2}` vs ticket `η⁻¹B^{5/2}`: `η = (1-t) Im m₀ ≤ 1-t`, so the S1 bound is the stronger one (row 1 of (a)). Acceptable.
- Family list in the def: `Fin 6` tags `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2` (`rfl` example, probe :126). Definitions used, by grep:
```
RBM3D/Chain/Carrier.lean:76  def FlowFM.GM ... := C.G n t ω x y - C.M n x y
RBM3D/Graph/BAExpand.lean:82 def BAlwW (g0 E t : ℝ) (m : ℂ) ... := Ring.inverse (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t))
RBM3D/Induction/Defs.lean:73 def STblk ... := (split d (sz.L n) (sz.W n) x).1 ;  RBM3D/Defs/Sizes.lean:92 def Iblk ... filter (split ..).1 = a
```
  Hand check against `GGGamma` (`B:393-405`, with `x↦α, y'↦x`; D402 coefficient `W−1`) and `lanlw` (`B:361-372`): `F_T3A^{(k)} = W^{(k)}_{αw}M_{wγ}(Σ_δS_{γδ}Ǧ_{δδ})G_{γy}Ǧ_{xw}`
  with `Σ_δ S_{γδ}Ǧ_{δδ} = tX_{[γ]}`; `F_C1` = `Ǧ_{ββ}`-child of `lanlw` on `Ǧ_{αy}` (prefactor `M_{xα}`); `F_C2` = tail-form child on `Ǧ_{xα}`. Consistent with design `:34-38`, `:57`.
- `σc = false` is defined as `star` of the `σc = true` family at `(!σo, ac↔ao)`; by hand `tr((G*E_{a₂}G*E_{ac}G(σo)E_{ao})^*) = tr(GE_{a₂}GE_{ao}G(!σo)E_{ac})`, i.e. the
  same reading as (a′). The identity `LWcutg … false σo ac ao = star (LWcutg … true (!σo) ao ac)` is owed by the L4a2 assembly (stated in (a′)); not S1's business.

Rerun of the numerical checks of the probe step (scratch `T2418/`):
```
$ python3 cutcheck.py
(1) max |LWcut(true,so,ac,ao) - sum form| over so, ac, ao = 1.2e-16
(2) max |LWcut(false,so,ac,ao) - conj LWcut(true,!so,ao,ac)| = 2.8e-16   (control, blocks not swapped: 6.8e-02)
$ python3 s1check.py 18 > aud2_s1check18.out    # 2^18 points (the report used 2^20); 83 s
x=0 y=2 sigma=-  |LHS_GG|=0.013
   residuals  C1 2.9e-05 (wrong 7.9e-05, |F_C1|=2.2e-03)  C2 3.8e-05 (wrong 5.2e-05, |F_C2|=2.2e-03)  GG 5.9e-05
   GG with the first two sums printed (S+ for W-1): 8.2e-03; with W for W-1 in T1: 1.4e-02  (|T1|=1.9e-03)
   GG with one S1 term wrong: T1 5.9e-05 (|T1|=1.9e-03), T3A0 5.9e-04/5.6e-04 (|T3A0|=1.7e-03), T3A1 1.6e-04/1.5e-04 (|T3A1|=3.6e-04)
(max correct residual over the 6 cases: C1 9.4e-05, C2 6.8e-05, GG 2.2e-04; printed-S⁺ variant 3.5e-03..8.2e-03 in all 6 cases)
```
Reproduces the report's conclusion at QMC noise (the term list completes `BAlanlwR`/`BAGGGammaR`; the printed `S⁺` coefficient does not, D402).

## 3. Compiled nonempty instance (pin level)
Probe :143-146: `BAExp14aS1 3` applied at `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`, `t ≡ 1/2` with `half_lt_t0`; only
`STLocalEntrygL`, `LWAvgLawgL` (other gates' pins) stay hypotheses. Probe :149-162 proves `U_n` nonempty for every `n` (`λ_n²/L_n³ ≤ 1/2`). Compiled (§1, EXIT=0).

## 4. Numerics of (a) rerun
```
$ python3 inst.py | grep -E "THE INSTANCE|>= kappa|C_M=|B_t0|W\^-d|omega:|lam\^2/L|N\^"     # (needs user-site numpy: no -I)
--- g=0.015625: sz0 n=0 (L=4,W=32): THE INSTANCE
  Im m0=0.9995 >= kappa=0.5: True; Im m_S=0.8325 >= kappa: True; t=0.5 <= t0: True
  C_M=max row l1(M^B)=1.0828; ||~|M^B|~||_2=1.0828 <= C_M: True
  B_t0=Bparam=2.03027; B=Bctl=6.1959e-05; Psi=B^(1/2)=7.8714e-03; B<=1: True
  c_g=lam^2+1=1.000244; W^-d=3.0518e-05 <= c_g*B=6.1974e-05: True; ratio=0.4924
  omega: rho(tM^+)=0.5000; max l1 row/col=0.6671; l1 of (omega-1)=0.3333; (1-t)^-1=2.00; omega-1 - tM^+ omega max=2.3e-15
  lam^2/L^d=3.815e-06 <= 1-t=0.5: True
  Im m0=0.6732 >= kappa=0.25: True; Im m_S=0.3777 >= kappa: True; t=0.3 <= t0: True          (g = 1 row)
  C_M=max row l1(M^B)=5.9153; ||~|M^B|~||_2=5.9153 <= C_M: True
  omega: rho(tM^+)=0.3000; max l1 row/col=0.9931; l1 of (omega-1)=0.2308; (1-t)^-1=1.43; omega-1 - tM^+ omega max=1.5e-15
    N^(-1+eps)=2.044e-06 <= Im z_S=0.3675 <= 1 (BAdom): True
$ python3 -I budget.py | tail -1 ; python3 -I limit.py
min slack: 0
sum_y [premise bound on |(G-M)_xy|^2] = 54.6410  >=  leading Ward value sum_y|G_xy|^2 - sum_y|M_xy|^2 = 2.000 - 1.0 = 1.000: True
```
Same as (a). Instance nondegenerate (`d=3, L=4, W=32, N=2^21, t=1/2 < t₀=0.694`); `g=1` row (C1: no smallness of `g`).

## 5. Round-1 "Required for resubmission" and Amend 1 items
| item | where | check | status |
|---|---|---|---|
| 1 dispatcher decision | Amend 1 D1-D4 | applied in (a′) "Decisions applied"; S1 docstring states D4 (probe :20, :106) | met |
| 2 / (i) S1 `def` compiled, shape, family list, consumer premise quoted | (a′) probe step; §1-§3 here | EXIT=0, standard axioms; diff §2; premise lines 436-438 quoted | met |
| 3 / (ii) section map `LWExpTerm4` → planned decl. | (a′)(ii) | rows for §1-§10 with file A/B and change (`ω`, ties, atoms); §6, §9 out | met |
| 4 / (iii) band input → BA source / owing | (a′)(iii) | includes `st5_Bctl_le_one` (owing), `ω` `ℓ¹` (owing, from `baProp5s_holds`), improved average (derived, `T2418a`); cites below | met |
| 5 / (iv) lines per file | (a′)(iv) | `lines.py` rerun below; rows 2, 6, 7 priced | met |
| 6 / (v) scope line | (a′)(v) | explicit: nothing of §6 `:828-939`, §9 `:1394-1721`, twisted `T3B`; no `tw*` | met |
| 7 namespace + grep | (a′) "Namespace and names" | `RBM.BA` with reason; grep below | met |
```
$ python3 -I lines.py | tail -3
BAExp14a.lean    low   744  central   930  high  1245  stop line 2000: high<2000 = True
BAExp14aB.lean   low   865  central  1145  high  1660  stop line 2000: high<2000 = True
both files        low 1609 central 2075 high 2905   (ticket: 1,020 / 1,190 / 2,250)
$ for p in Induction/Step5Kit.lean:362 BA/Step1Fam.lean:382 BA/KStep.lean:350 BA/KInduct.lean:203 Induction/Step6Pins.lean:177 Loop/KLFinal.lean:302 ...; do sed -n ${l}p; done
Induction/Step5Kit.lean:362      theorem st5_Bctl_le_one {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ} (hflow : STFlo
BA/Step1Fam.lean:382             theorem Bctl_le_one_of_conStInd (sz : Sizes d) {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hst
BA/KStep.lean:350                private theorem KStep_theta_l1 {k : ℕ} (hd : 3 ≤ k + 2) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ
Induction/Step6Pins.lean:177     def STExpAvgAt (E u : ℕ → ℝ) : Prop :=
Loop/KLFinal.lean:302            theorem stKbound_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
$ bash names.sh | tail -3 ; bash cites.sh | wc -l
stems baExp14a|BAExp14a|BAS1 on main: 0 hits
rejected name baS1_holds: 38 existing baS1_* hits (BA/Step1.lean, Step1Setup.lean: Step-1 theorems)
26
$ grep -rn "BAExp14a\|baExp14a" RBM3D RBM3D.lean | wc -l ; for b in t/T2417 t/T2419 t/T2420 t/T2421 t/T2422 t/T2423 t/T2425; do git grep -e BAExp14a -e baExp14a $b -- RBM3D | wc -l; done
0
0 0 0 0 0 0 0
$ grep -c "BAExp14a\|baExp14a" docs/tickets/T24{17,19,20,21,23,25}.md    # each hit is the sibling-scan line "Graph/BAExp14a*" (file name)
1 1 1 1 1 1
```
All ten planned public names and the probe's `BAExp14a_*` stem: 0 hits on `main` and on the sibling branches; no sibling ticket names them.

## 6. Binding stop lines
- 2,000 per file: predicted high A 1,245, B 1,660 (< 2,000). Not hit.
- H183 (3) sign-off: answered by Amend 1; no new scope change in (a′) needs a decision (see observation 1). TL0 (no `tw*`, no `BATwistAvgLaw`/`BATwistLoopLaw` defined): probe defines none.
- Sole writable files: unchanged by Amend 1; the probe file is H219's; 1b copies `BAExp14aS1` verbatim into `Graph/BAExp14aB.lean` (H219).

## 7. Paper deltas
`T2418a` (the improved average `O(B²)` of `lem:improve_exp_aver` is not needed at BA for S1; exponent 3/2 derived via `lanlw`, `f = 1`) proposed in (a), confirmed by Amend 1 D1.
`W − 1` for the printed `S⁺` in `GGGamma`: existing D402. The `σc = false` convention is a Lean labelling, not a paper difference. Coverage complete.

## Observations (no verdict effect)
1. (a′)(ii) drops the twins of `ward2` (`:250-412`), `kward` (`:743-777`) and §7 (`:940-1103`) beyond the names in D2. Each is a consequence of D2/D3 (consumers of
   `ward2`/`L3` are §8 `R23`, §9, §10 only, script in (a′)(ii); `kward` is the `STKwardgL` route of D3; §7 sums are replaced inline). No sibling ticket consumes
   `BAExp14a*` (grep §5) and the L4b2 basis prices its own 14 helpers (design `:255`), so nothing moves to another row. Recorded for the dispatcher, not a sign-off item.
2. Line risk: with the ticket's measured stage-L ratio 1.5-2.1 applied to the 1a's central, B is 1,717-2,404 (A 1,395-1,953); the 1a's mitigation (bridges move to A if B
   passes 1,700) and the copied S1 def (probe :35-112, ~75 lines vs priced 45/55/70) should be watched at 1b.
3. `BAlwW` is a `Ring.inverse`: the 1b needs invertibility of `1 − M⁺S` (`BATheta_isUnit`, (iii)). Scripts need user-site numpy (no `-I`), noted in (a′)(c4).

## Verdict: **PASS**
Every stage-1a deliverable of the ticket and every repair item of Amend 1 / round 1 is met (§5); S1 compiles with standard axioms and has the consumer's
shape (§1-§2); the pin-level instance is nondegenerate and compiles (§3); numerics reproduce (§2, §4); no binding stop line is hit (§6). Stage 1b may start.
