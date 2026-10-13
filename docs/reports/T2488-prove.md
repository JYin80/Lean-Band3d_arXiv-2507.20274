Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 04:28:12 UTC 2026

Base `main` 2cc78196 = worktree HEAD (`git log -1`: "T2483: merge L3d2b-2 Graph/BAMomentExpGenB"), so **start decision: 4 (b) is included**. Instance graph `baPQ` (`BAAtom2:770`) = `BAGraph.ofLGraph localReg2_inst_Q` (`LocalRegular2:1935-1939`). **Verdict (all targets 1, 2, 3, 4 (a), 4 (b), 5): PASS.** G4 holds; no switch to `prover-max`; no split.

### (i) Exponent table (instance `baPQ`: `p=2`, `q=n_M=1`, `ord^aux=2`, no ghost edge; `d=3`, `sz0`, `n=0`)
| exponent / constant | value | constraint (source) | slack |
|---|---|---|---|
| `p`, `n_M` | 2, 1 | `0<p`, `n_M ≤ p` (hyp. of `BAAnpAuxG`, `BAAuxGraph2B:867`) | `p-n_M = 1` |
| `ord^aux = |molSolid| - 2n_M` | `4-2 = 2` (script) | `LocReg345 p` (hyp.) | `ord^aux - p = 0` (exponent of `Φ(0)`) |
| `n_ngh`, `k = ord - n_ngh` | `2` (= `p`, no ghost: `anpKey_nngh_of_noGhost` `AnpKey:799`), `0` | none | none |
| `M = q + abs(k) + p` | 3 | `q+k+n_ngh ≤ M` (`AnpKey:747`) | `(abs k - k) + (p - n_ngh) = 0` (tight) |
| `τ' = τ/(2(M+1))` | `τ/8` = `1/80, 1/16, 1/8` at `τ = 1/10, 1/2, 1` | `τ'M ≤ τ/2` (`AnpKey:711`) | `τ/2 - τ'M = τ'` exactly |
| `C = ∏_j max(1,|𝔓_j|)`, `c = (1+Σ_j|𝔓_j|)⁻¹` | `4`, `1/5`: paths of lengths `(2,2)` (2 edge-disjoint paths, no direct `ext0–ext1` solid edge, 4 edges; `AnpKey6:868-869`) | `C ≤ N^{τ/2}` eventually (`AnpKey:720`); `c ≤ 1` is dropped by the lift (`AnpKey:691`, pattern `-`) | `N^{τ/2}/C = 0.52, 9.5, 362` at `n=0`, `τ = 1/10, 1/2, 1`; first `n` with `C ≤ N_n^{τ/2}`: 2, 0, 0; at `n=0` iff `τ ≥ 4/21` |
| `x = N^{τ'}`: `x^{q+k+n_ngh}` | `x^3 = N^{3τ/8}` | `≤ N^{τ/2}` (`AnpKey:746`) | factor `N^{τ/8}`: `15.32 ≤ 38.06` (`τ=1/2`, `n=0`) |
| `C x^{q+k+n_ngh}` | `61.29` | `≤ N^τ` (`AnpKey:761`) | `N^τ = 1448.15`, factor 23.6 |
| `(W^d)^{n_M}(W^dη_t)^{-n_M}` | `η_t^{-n_M}` (= 4 at the instance) | identity: G3 factor `BAAtom2:409-410` times the pin `BAAuxGraph2B:877` | equality |
| `η_t` | `(1-t) Im m₀ ≥ (1-t)κ ≥ (1-T₀_n)κ`, `T₀_n<1` (`BAt0_lt_one`); instance `η ≥ 1/4`, `θ_0 = (W^dη)⁻¹ ≤ 1.22e-4` | the lift uses only `η_n(t_n) > 0` (`BAExp14a_eta_pos` `BAExp14a:1266`; `ba_G_data` `GreenLDE:55`); no uniform bound `(1-T₀)κ` is used | n/a |
| `size → ∞` | `N_n = (L_n W_n)^3 = 2^21 (n+1)^18` | `hflow.1.2.2.1` = `SizeTendsto` (`Sizes:178`) | `N_0 = 2097152` |
| `D₁` (ζ of 5 (i)) | `max(d + 2C₂/(𝔠d) + 1, 1/𝔠) = max(12, 6)` | `D₁ ≥ 12` (`BAAuxGraph2B:80`) | 0 (`D₁ = 12`) |
| `ε₁` (entry law) | `1/20` | `‖G_t-M‖_max ≺ W^{-ε₁}` (hyp. of `BAZetaClaim`) | exponent `0.699…0.745` (`T2470-prove.md:50-52`), slack `≥ 0.649` |
| target 1 at `anpKey_oneEdge` (`AnpKey:843`; `p=1`, `q=0`) | `ord = 1`, `n_ngh = 1`, `k = 0`, `M = 1`, `τ' = τ/4`, `C = 1`, `c = 1/2` | `q+k+n_ngh = 1 ≤ M` | 0; `C = 1 ≤ N^{τ/2}` for all `n` |

### (ii) One concrete nondegenerate instance (target 5 (i): targets 1-3 at `baPQ`)
Data: `d=3`; `sz0`, `n=0`: `L=4`, `W=32`, `N=2^21` (`Defs/Sizes:260-267`); `flow_sz0` (`κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`; `FlowPins:1214`); `z=zSeq`; `t≡1/2 ≤ T₀` (`half_lt_t0` `FlowPins:1254`); `Φ0≡W^{-1/2}`, `ε₀=1/10`, `C₁=C₂=2`, `C₃=1`, `Cc≡1`; `ε₁=1/20`; `D₁=12`; `P=baPQ`, `p=2`. `ξ = c₀` constant on `Z_4^3` is a Ward-admissible stand-in for `ζ` (`Σ_β ξ² = θ_0/2`, `ξ ≤ Φ0`), used to evaluate the deterministic bound of `anpDetGh_holds` at `Γa`.
Command (stdlib only; molecules and `ord^aux` recomputed from the lists of `localReg2_inst_Q`): `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2488/inst.py`
```text
n=0: L,W,N = 4 32 2097152 = 2^21
baPQ: nM = 1 |molSolid| = 4 auxOrd = 2 p = 2 nM<=p: True
C = 4 c = 1/5 | nngh = 2 k = ord-nngh = 0 M = q+|k|+p = 3
eta_t >= (1-t)*kappa = 1/4  (T0>1/2: half_lt_t0, so (1-T0)kappa < 1/4)
theta_0 = (W^d eta)^-1 <= 1.2207e-04 ; (W^d)^nM*(W^d eta)^-nM = eta^-nM: True
D1 floor = 12
tau  tau'=tau/(2(M+1))  tau'*M<=tau/2 (slack)  x=N0^tau'  x^(q+k+nngh)<=N^(tau/2)  C<=N^(tau/2)@n=0  n_*(tau)
1/10  1/80              True (1/80)            1.1996     1.726<=2.071             2.071 vs 4        2
1/2   1/16              True (1/16)            2.4837     15.322<=38.055           38.055 vs 4       0
1     1/8               True (1/8)             6.1688     234.753<=1448.155        1448.155 vs 4     0

final inequality C*x^(q+k+nngh) <= N^tau at tau=1/2,n=0: 61.29 <= 1448.15
xi=c0=9.766e-04: xi<=Phi0=W^-1/2=0.1768, sum_b xi^2=6.104e-05<=theta=1.221e-04 ; Gamma_a.val=5.821e-11 <= C theta^q psi^k prod psi = 2.338e-04 : True
```
The instance is nondegenerate (`N=2^21`, `p=2`, `n_M=1`, nonempty graph); at `n=0` the `≺` thresholds hold for `τ ≥ 4/21` (for `τ = 1/10` from `n=2`: `N_2 = 2^21·3^18`). Hypotheses left in the Lean instances (other gates' pins; none for targets 1-4): `LWLoop2gL`, entry law `‖G_t-M‖_max ≺ W^{-1/20}`, `STInitialGT2gL` (5 (iii), (iv)). Limit check (external hypothesis, TEAM §8 lesson 14): the T2470 script (`T2470-prove.md:50-52`, same `sz0`, `t=1/2`, not rerun) gives `Bctl^{1/4} = W^{-0.699}, W^{-0.739}, W^{-0.745}` at `n=0, 10, 1000`, against `W^{-1/20}` and `W^{-1/10}`: not contradicted.

### G4-a (`B:491-497`; each step against the merged texts)
- **(i) Centre-level aux graph.** `BAGraph.auxVal := Γ.shadow.auxVal`, `auxOrd := Γ.shadow.auxOrd` (`BAAtom:71, 75`); `baAuxNested_holds` (`BAAtom2:647`) gives `Γa : NGraph p n_M`, `NoGhost`, `IsNested`, `ordN = auxOrd`, `Γa.val ξ = auxVal ξ` for symmetric `ξ`. At `baPQ`: 4 molecular solid edges, `n_M = 1`, `ord^aux = 2` (script).
- **(ii) `B:494`, "summation over non-centre vertices": not a G4 step.** Atoms of `𝓜_i` lie within `card(E⊕I)·r ≤ R` of the root (premise `BAAtom2:404`; T2420-prove.md:22, A1); the premise `hξ` of `baGtoAG_holds` (`BAAtom2:404-406`: `‖G_xy-M_xy‖ ≤ ξ(a,b)` for `a,b` in the `R`-balls) bounds each solid edge at an atom by `ξ([α_i],·)`; G3's output is `(W^d)^{n_M}·auxVal ξ(centre labels)` (`BAAtom2:409-412`); `baGbyZeta_hxi` (`BAAuxGraph2B:769`) gives `hξ` from `ξ = c·baZetaVar`. `BAAnpAuxG` is stated for every `ξ` with `LWXigL`, so no atom sum enters G4.
- **(iii) `B:496` Cauchy–Schwarz = Ward row sum.** `Σ_β ξ_{αβ}² ≺ (W^dη_t)⁻¹` is the third conjunct of `LWXigL` (`BAAuxGraph2:1039-1040`), supplied by `BAZetaClaim` (`BAAuxGraph2B:69`); it is the hypothesis `Σ_β ξ² ≤ θ` of the model-free `anpDetGh_holds` (`AnpKey6:862`), which performs the Cauchy–Schwarz steps (`AnpKey2`-`5` have 0 hits of `Prec|STFlow|etaT|lemT|seqP`). Factor: `(W^d)^{n_M}(W^dη_t)^{-n_M} = η_t^{-n_M}` (table, script).
- **(iv) `lem:Anp_key_gh` (`7_8:1041-1077`) at the BA law.** `Ξ_n = {ξ ≤ N^{τ'}Φ_n} ∩ {Σ_β ξ² ≤ N^{τ'}θ_n}` has `μ(Ξ_nᶜ) ≤ N^{-D}` by `BAMomentGen_whp_of_prec` (`BAMomentGen:179`, any `μ`) twice and `HighProbAt.inter` (`StochDomAt:571`, needs `Tendsto size` only); on `Ξ_n` the deterministic bound at `ψ = N^{τ'}Φ_n`, `θ = N^{τ'}θ_n` (ψ antitone positive from `LWPsiAll`; `θ>0` from `η>0`) with `anpKey_rescale` (`AnpKey:672`) gives `C N^{τ'(q+k+n_ngh)} ≤ N^τ` (rows 5-8); `measure_mono` closes at `μ`. Changes vs the band lift (`AnpKey:689-770`): law `seqP (sz.withLam 0)`, `η = (baFMz sz z).eta`, `BAFlow`/`BAflowT0` (the flow is read only at `AnpKey:693-701`: `SizeTendsto`, `Im z>0 → η>0`), `PrecL`. Target 2: imported `anpKey_*_of_noGhost` (`AnpKey:782-799`) plus twins of `:814`, `:825`. Target 3: route of `baAnpAux_holds` (`BAAtom2:694-708`): `Γa` from `baAuxNested_holds`, target 2 at `Γa`, `q = n_M ≤ p`, transport by `(hξ.1 n u v ω).2` and `ordN = auxOrd`.
- **Result:** no term of `B:491-497` lies outside G3's `R`-ball premise and the Ward sum of `LWXigL`; stop rule "G4 fails" not triggered.

### G4-c consumers; hypothesis, UBA-C1 and registry tables
| consumer | reads | closure |
|---|---|---|
| L3d2a (T2470) target 4 | `BALWMomentOfAnp d := BAAnpAuxG d → BALWMoment d` (`BAMomentGenB:362`); `hAnp` applied at `:418` with `ξ` as the `LWXigL` triple (`:405-416`) | 4 (a): `fun d => baLWMomentOfAnp_closed d (baAnpAuxG_holds d)` (`BAMomentExpGen:189`) |
| L3d2b-2 (T2483b, merged) | `BALWMomentExpOfAnp d := BAAnpAuxG d → BALWMomentExp d` (`BAMomentExpGenB:1202`), `baLWMomentExp_of_anp` (`:1207`) | 4 (b): `fun d => baLWMomentExp_of_anp d (baAnpAuxG_holds d)` |
| T2435 instance | `h6 : BAAnpAuxG 3` (`BAAuxGraph2B:979`) | 5 (i) discharges it |

| premise (band `LWAnpKeyGh`, `LWPins:389`) | band discharge | BA discharge |
|---|---|---|
| `STFlow`, `t ≤ lemT` | `hflow.1.2.2.1`; `etaT_pos` (`AnpKey:693-702`) | `BAFlow`: `hflow.1.2.2.1`; `BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)` |
| `LWPsiAll sz …` | `hΦ.2.1.1` (positivity), `hΦ.2.2.1` (antitone) | same (reads `sz.W` only) |
| `LWXi` (+ `Prec.whp`) | triple `⟨hξnn, hξ1, hξ2⟩` | `LWXigL` triple; `BAMomentGen_whp_of_prec sz` |
| `AnpDetGh d` | `anpDetGh_holds d` | same (model-free) |
| `q ≤ p`, `0<p`, `n_M ≤ p`, `LocReg345`, mol-distinct | `lwAnp_holds` | `baAuxNested_holds`, then `hq` of target 2 |

UBA-C1: `grep -cE "sz\.lam|withLam|gK|lam0"` = 0 on `AnpKey:658-836`, `BAAtom2:677-708`, `LWPins:355-424`; `withLam` occurs only as the law `seqP (sz.withLam 0)` in `BAAuxGraph2B:874-875`; R1 not needed, no crossing. Registry (`Test/Axioms.lean:467` `scanPremises`: `Prop` defs in binders of theorems): all new public theorems are `∀ d : ℕ, P d` (binders: `ℕ`); `BAAnpAuxG` occurs only in defs and `example`s (`BAAuxGraph2B:865, 979`; `BAMomentGenB:362, 473`; `BAMomentExpGen:982`; `BAMomentExpGenB:1202, 1288, 1294, 1317`), and `grep -c "BAAnpAuxG\|BALWMoment\|BAAnpKeyGhG" RBM3D/Test/Axioms.lean` = 0, so no line is needed in `Test/Axioms.lean`; `BAAnpAuxG` becomes proved (target 3). Cores taking `LWXigL`/`LWPsiAll` stay `private`.

### (vi) Line prediction (new lines in `Graph/BAAnpLift.lean`)
| block (band reference lines) | new lines |
|---|---|
| header, docstring, premise scan | 55 |
| T1 `BAAnpKeyGhG` (`LWPins:389-407`, 19) + proof (`AnpKey:689-770`, 82) | 115 |
| T2 `BAAnpG` (`LWPins:409-424`, 16) + proof (`AnpKey:814-835`, 22) | 53 |
| T3 `baAnpAuxG_holds` (`BAAtom2:689-708`, 20) | 38 |
| T4 (a), (b) | 24 |
| T5 data (ρ, R, `LWPsiAll`; private in `BAAuxGraph2B`, re-derived: 40) + examples (i) 30, (ii) 30, (iii) 22, (iv) 18 | 140 |
| **central** | **425** (range 360-560; TLC-4 upper `2.6 × 425 = 1,105`) |
The ticket's 290 / 360 / 630 is re-priced to 360 / 425 / 560. Against the pre-signed 1,950 split: below by 1,525; stop line 2,000 and the reserve `BAAnpLiftB` (>1,800) not reached; no split. Public `LWInst.Φ0`, `psiAll0`, `window0`, `Ψ0` (`LWPins:521-552`) can replace the re-derived class data of 5 (iii), (iv) (about -35). L40-C3: stage L 43 / 50, projection 47 unchanged. L40-C4 fold check: `wc -l` of `BAMomentGenB` 847, `BAMomentExpGen` 1147, `BAMomentExpGenB` 1344, all above 750: no fold. Census note: `grep -cE 'Prec|STFlow|etaT|lemT|seqP'` gives 9 (`AnpKey`) and 4 (`AnpKey6`), not 10 and 5; all hits are the lift (`AnpKey:685-727`) or instances; `AnpKey2`-`5` give 0; family size 7,157 lines (`wc -l`).

### Ticket fill-in table (H250 (4))
| # | deliverable | line / n/a |
|---|---|---|
| (i) | exponent table | lines 7-23 |
| (ii) | instance with script | lines 25-43 (script and output: 27-41) |
| (iii) | G4-a (i)-(iv) | lines 45-50 |
| (iv) | G4-c consumers; start decision (L3d2b-2 merged at 2cc78196, 4 (b) included) | line 4; lines 52-57 |
| (v) | UBA-C1, hypothesis tables, registry | lines 59-67 |
| (vi) | lines vs 2,000, 1,950 split, L40-C3, L40-C4 | lines 69-79 |
| (vii) | line 90 (this row): switch conditions: (a) not met: the lift reads the law/flow only through `η>0` at every `n` and `size→∞` (`AnpKey:693-702` → `BAExp14a_eta_pos`, `hflow.1.2.2.1`); (b) not met: `BAAnpAuxG` = nested form + target 2, the route of `baAnpAux_holds` (`BAAtom2:694-708`), no further estimate. Role stays `prover-hard`. | this row |

Paper-delta candidates: `T2488a`: the "summation over non-centre vertices" of `B:494` is in G3 (centre-level `auxVal`, `R`-ball `hξ`), not in G4; the Lean `BAAnpAuxG` has no atom sums. `T2488b`: none (closures 4 (a), (b) are compositions of merged results, no paper statement).

## (b) Script output, stage 1b — Tue Oct 13 04:51:59 UTC 2026
`$S` below is `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2488` (prefix shortened). Section (a) above is unchanged; no correction was needed, so there is no (a′).

```text
$ git log -1 --format="%h %s" main -- RBM3D/Graph/BAMomentExpGenB.lean; git merge-base main t/T2488 | cut -c1-8; git log --format="%h %s" main..t/T2488
2cc78196 T2483: merge L3d2b-2 Graph/BAMomentExpGenB (second half of the split, t/T2483b)
2cc78196
63baa94a T2488: BAAnpLift instances (iii)-(iv) of the closures
e1fcc8d2 T2488: BAAnpLift targets 1-4 and instances (i)-(ii) (wip)
$ git rev-parse --short main; git diff --name-only 2cc78196 main -- RBM3D RBM3D.lean | tr "\n" " "; echo
89df2d82
RBM3D.lean RBM3D/BA/Step2CloseBA.lean RBM3D/BA/Step2IterBA.lean RBM3D/Test/Axioms.lean 
$ lake build RBM3D.Graph.BAAnpLift 2>&1 | grep -E "BAAnpLift|rror|Build completed"; lake env lean RBM3D/Graph/BAAnpLift.lean; echo "lean exit=$? (no warning, no message)"; wc -l RBM3D/Graph/BAAnpLift.lean
Build completed successfully (4070 jobs).
lean exit=0 (no warning, no message)
     388 RBM3D/Graph/BAAnpLift.lean
$ lake build   (full; worktree RBM3D.lean with the extra line `import RBM3D.Graph.BAAnpLift`, removed before the commit; log $S/fullbuild.log)
info: RBM3D.lean:575:0: axiom audit: 14516 theorems, 4547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4343 jobs).
EXIT=0
premise-ledger lines naming BAAnpAuxG|BAAnpKeyGhG|BAAnpG|LWXigL: 0
$ lake env lean $S/ax2488.lean
'RBM.Graph.baAnpKeyGhG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAnpG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAnpAuxG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWMoment_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWMomentExp_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
$ diff -U0 <(sed -n 389,403p RBM3D/Graph/LWPins.lean) <(sed -n 73,87p RBM3D/Graph/BAAnpLift.lean) | grep -v "^@@\|^---\|^+++" | cut -c1-165 | tee $S/d1.tmp | cat
-def LWAnpKeyGh (d : ℕ) : Prop :=
+def BAAnpKeyGhG (d : ℕ) : Prop :=
-    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.GhostOK → Γ.IsNested →
+    ∀ (p q : ℕ), q ≤ p → ∀ Γ : NGraph p q, Γ.GhostOK → Γ.IsNested →
-        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
-          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
+        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
+          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
-                LWXi sz (STflowE z) t Φ ξ →
-                Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
+                LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
+                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
-                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
+                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ q *
$ diff -U0 <(sed -n 409,422p LWPins.lean) <(sed -n 193,206p BAAnpLift.lean)   (lines not already shown above)
-def LWAnp (d : ℕ) : Prop :=
+def BAAnpG (d : ℕ) : Prop :=
-    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested →
+    ∀ (p q : ℕ), q ≤ p → ∀ Γ : NGraph p q, Γ.NoGhost → Γ.IsNested →
-                Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
+                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
$ grep -nE "^theorem (baAnpKeyGhG_holds|baAnpG_holds|baAnpAuxG_holds|baLWMoment_closed|baLWMomentExp_closed)" RBM3D/Graph/BAAnpLift.lean | cut -c1-150
182:theorem baAnpKeyGhG_holds : ∀ d : ℕ, BAAnpKeyGhG d := by
211:theorem baAnpG_holds : ∀ d : ℕ, BAAnpG d := by
229:theorem baAnpAuxG_holds : ∀ d : ℕ, BAAnpAuxG d := by
255:theorem baLWMoment_closed : ∀ d : ℕ, BALWMoment d := fun d => baLWMomentOfAnp_closed d (baAnpAuxG_holds d)
258:theorem baLWMomentExp_closed : ∀ d : ℕ, BALWMomentExp d := fun d => baLWMomentExp_of_anp d (baAnpAuxG_holds d)
$ lake env lean $S/diffcheck.lean   (= docs/tickets/checks/T2488-check.lean + import BAAnpLift + the 10 lines below, made by script)
example : T2488_AnpAuxG := RBM.Graph.baAnpAuxG_holds
example : T2488_MomentClosed := RBM.BA.baLWMoment_closed
example : T2488_MomentExpClosed := RBM.BA.baLWMomentExp_closed
example : T2488_AnpAuxG = (∀ d : ℕ, RBM.Graph.BAAnpAuxG d) := rfl
example : T2488_MomentClosed = (∀ d : ℕ, BALWMoment d) := rfl
example : T2488_MomentExpClosed = (∀ d : ℕ, BALWMomentExp d) := rfl
example : T2488_shape1 = (∀ d : ℕ, RBM.Graph.BAAnpKeyGhG d) := rfl
example : T2488_shape2 = (∀ d : ℕ, RBM.Graph.BAAnpG d) := rfl
example : T2488_shape1 := RBM.Graph.baAnpKeyGhG_holds
example : T2488_shape2 := RBM.Graph.baAnpG_holds
exit=0 error lines: 0
$ lake env lean docs/tickets/checks/T2488-check.lean -> exit=0 error lines: 0
$ instances (the 5 `example`s; example 1 in full, the others head and last line)
--- example 1: lines 298-304
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
    (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n ab ω => BAAtomInst2.baPQ.g.auxVal (fun α β => ζ0 n α β ω) (fun e => if e = BAAtomInst2.baPQ.ext 0 then ab.1 else ab.2))
      (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ ^ BAAtomInst2.baPQ.g.nM *
        Φb n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 * Φb n 0 ^ (BAAtomInst2.baPQ.g.auxOrd - 2)) := by
--- example 2: lines 312-320
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
          Φb n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) := by
--- example 3: lines 327-333
example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
        Φb n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 1 * Φb n 0 ^ (anpKey_oneEdge.ordN - (1 : ℕ))) := by
--- example 4: lines 364-369
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
        BAMomentExpGen_Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ 2) := by
--- example 5: lines 378-379
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 20) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ℓh) (D : ℝ) (hD : 0 < D) :=
$ git grep -lE <final names> | git ls-tree .. grep BAAnpLift, over 40 refs (main + t/T246*..t/T2487): files with hits 0, BAAnpLift* files 0
$ greps on the new file: sz.lam|gK: 0; sorry|admit|native_decide|axiom: 0; BAShapePath: 0
  code lines with withLam: 81 82 201 202 277 355 
  code lines with Sizes:   77 81 82 95 109 197 201 202 277 355 
  code lines with LWXigL|LWLoop2gL|BAAnpAuxG: 81 98 201 229 287 290 298 312 327 365 
```

Narrative (facts as in the output above and in section (a)):
- **Role and split.** Switch conditions (a), (b) of the ticket are not met (row (vii), line 90 of this report, and `T2488-1a-audit.md` §4), so Lean was written and no `SWITCH prover-max` is returned. No split: 388 lines against the 1a central 425 (range 360-560, line 78), the 1,950 split line and the 2,000 stop line; `BAAnpLiftB` is not used.
- **Start decision.** L3d2b-2 is merged at `2cc78196`, which is the merge-base of `t/T2488` (output above), so target 4 (b) is delivered with 4 (a). `main` has moved since (`268e07d4`; `git diff --name-only` output above); none of the four files is imported by the new file. The full build above was run on the base `2cc78196` with the final file and the import line, not at `268e07d4`.
- **Files.** Only `RBM3D/Graph/BAAnpLift.lean` is committed (2 commits on `t/T2488`). The import line `import RBM3D.Graph.BAAnpLift` was added to `RBM3D.lean` in the worktree for the full `lake build` (registry check) and removed before the commit; the hub adds it at merge (CLAUDE.md §3 (A) 4). `Test/Axioms.lean` is unchanged and needs no line: the premise ledgers of the full build name none of the new pins.
- **Public declarations** (file lines): `BAAnpKeyGhG` 73, `baAnpKeyGhG_holds` 182, `BAAnpG` 193, `baAnpG_holds` 211, `baAnpAuxG_holds` 229 (namespace `RBM.Graph`), `baLWMoment_closed` 255, `baLWMomentExp_closed` 258 (namespace `RBM.BA`). Private: `BAAnpLift_core` 94, `BAAnpLift_zeta0` 287. Five `example`s (298, 312, 327, 364, 378). No new `inductive` (`grep -c inductive` = 0); `sz.lam` is not read (UBA-C1 below).
- **Targets 1-2 (the lift).** `BAAnpLift_core` is the `≺`-lift of `lwAnpKeyGh_of_det` (`AnpKey.lean:689-770`) stated over any law `μ`, any carrier `C : FlowFM sz` with `size → ∞` and `η > 0` as hypotheses (ticket target 1: "the core may be a private lemma over any `(C, μ)`"). Changes against the band text: `Prec.whp` -> `BAMomentGen_whp_of_prec` (`BAMomentGen.lean:179`); `etaT_pos` -> `BAExp14a_eta_pos` (`BAExp14a.lean:1266`, called in `baAnpKeyGhG_holds`); `hsz'` is `hflow.1.2.2.1`. `lwAnpKey_of_gh` and `lwAnp_of_key` are folded into `baAnpG_holds` (`precomp_param`, then the congruence).
- **Target 3.** `baAnpAuxG_holds` is the route of `baAnpAux_holds` (`BAAtom2.lean:694-708`): `baAuxNested_holds` (`BAAtom2.lean:647`), `baAnpG_holds` at `Γa` with `q = n_M ≤ p`, then value and order transported with `(hξ.1 n u v ω).2` and `Γa.ordN = auxOrd`. The pin `BAAnpAuxG` (`BAAuxGraph2B.lean:865`) is unchanged and no second `Prop` was named (diff against the check: `rfl`, output above).
- **Census G4-b (file:line; kind).** `anpDetGh_holds` (`AnpKey6:862`; public); `anpKey_rescale` (`AnpKey:672`) and `anpKey_stochDomAt_congr` (`AnpKey:806`; `open private`, line 65); `anpKey_prod_ite_mul` (`AnpKey:661`; not opened, used only inside `anpKey_rescale`); `anpKey_ghostOK_of_noGhost`, `anpKey_noGhostPath_of_noGhost`, `anpKey_nngh_of_noGhost` (`AnpKey:782, 793, 799`; public); `HighProbAt.inter` (`StochDomAt:571`) and `StochDomAt.precomp_param` (`:335`; public); `baZetaClaim_holds` (`BAAuxGraph2B:83`; public). Instance data by `open private`: `BAAuxGraph2B_Φ0`, `_ρ0`, `_psiAll`, `_ρ0_nonneg`, `_ρ0_rad` (`BAAuxGraph2B` §7, line 279) and `BAMomentExpGen_Φ0`, `_Ψ0`, `_Ψ0_window`, `_psiAll0` (line 358). No stem copy (the ticket's "re-derived" is replaced by `open private`, as `BAMomentExpGen:195` does; see (d)).
- **Instances.** Example 1 is target 3 at `baPQ` (`p = 2`, `n_M = 1`, `ord^aux = 2`), `ξ = baZetaVar … 12` from `baZetaClaim_holds 3`, with `BAAnpAuxG 3` not a hypothesis. Example 2: target 1 and example 3: target 2, both at `anpKey_oneEdge` (`p = 1`, `q = 0`), same data. Example 4: target 4 (a); example 5: target 4 (b). Data: `d = 3`, `sz0` (`N_0 = 2^21`), `flow_sz0`, `zSeq`, `t ≡ 1/2 ≤ BAflowT0`, `Φ ≡ W^(-1/2)`, `ε₀ = 1/10` (examples 1-4) and `Ψ0`, `ℓ_t`, `ε₀ = 1/20`, `p = 2`, every `D > 0` (example 5); numbers in section (a), lines 7-43. Hypotheses left, all other gates' pins: `LWLoop2gL` and the entry law `‖G_t - M‖_max ≺ W^(-1/20)` (examples 1-3); `STInitialGT2gL`, `LWLoop2gL` (example 4); `STInitialGT2gL`, `LWLoopExpgL` (example 5). The statements of targets 1-4 have the single binder `d : ℕ`.
- **UBA-C1.** `sz.lam`, `gK`: 0 hits. `withLam` (lines 81, 82, 201, 202, 277, 355) occurs only inside the law `Sizes.seqP (sz.withLam 0)` of the statement defs and of the instance notation, as in `BAAuxGraph2B:874-875`. `Sizes` hits are the type `Sizes d` (77, 95, 197), `Sizes.seqP` and `Sizes.tendsto_size` (109). No crossing, R1 not used.
- **Hypothesis table.** Every public theorem has the one binder `d : ℕ`. `LWXigL` occurs in the two statement defs (81, 201), in the private core (98) and as the conclusion of `BAAnpLift_zeta0` (290); `LWLoop2gL` in the private helper (287) and in examples; `BAAnpAuxG` as the conclusion of line 229 only; `BAShapePath` nowhere. Premise -> band discharge -> BA discharge: section (a), lines 59-65, unchanged.
- **Not done.** The optional instance of 5 (i) at a reached BA output with `M`-dotted edges (ticket, target 5) was not written; `baPQ` has no such edge (ticket, dispatcher answer (7), citing the T2420 1a-audit O4).

## (c) Verified Mathlib names
Each name occurs in `RBM3D/Graph/BAAnpLift.lean` (`name:grep -c` below) and the file builds, so each exists with the used signature:
```text
tendsto_rpow_atTop:1 Real.one_le_rpow:1 zpow_le_zpow_right₀:1 Real.rpow_le_rpow_of_exponent_le:1 Real.rpow_natCast:1 Real.rpow_mul:1 Real.rpow_add:1 Real.rpow_nonneg:1 div_le_div_iff₀:1 div_mul_eq_mul_div:1 Int.le_natAbs:1 Finset.card_filter_le:1 zpow_nonneg:2 Finset.prod_nonneg:1 Finset.prod_const:1 Finset.card_univ:1 Fintype.card_fin:1 ite_true:2 mul_right_comm:1 MeasureTheory.measure_mono:1 Nat.zero_le:2 dvd_refl:2 inv_pos:1 pow_pos:1
```
Names verified absent: none searched. Observed deprecated: `if_true` (build warning "Use `ite_true` instead", replaced by `ite_true`).

## (d) Open issues and paper-delta candidates
- `T2488a` (from (a), confirmed by the Lean text): the "summation over non-centre vertices" of `B:494` is not a step of G4. In Lean it sits in G3 (`baGtoAG_holds`: centre-level `auxVal`, `R`-ball premise `hξ`); `BAAnpAuxG` carries no atom sum and `baAnpAuxG_holds` is the nested form plus `lem:Anp` at the carrier.
- `T2488b`: none. Closures 4 (a), 4 (b) are compositions of merged results.
- Fragility: the file depends on 11 `private` names of merged files through `open private` (2 in `AnpKey`, 5 in `BAAuxGraph2B`, 4 in `BAMomentExpGen`); renaming one there breaks this file. Re-deriving the instance data was priced at 40 lines in section (a), line 77; the dispatcher may ask for it.
- Consumers: `BALWMomentOfAnp`, `BALWMomentExpOfAnp` and the `h6`/`hAnp` hypotheses of the merged examples are merged text and unchanged; L5 and the last terminal ticket read `baLWMoment_closed`, `baLWMomentExp_closed` and need no `BAAnpAuxG` premise.
- The stage-1b merge needs: the import line in `RBM3D.lean` (hub), the full `lake build` on current `main`.
