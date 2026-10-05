Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 20:13:06 UTC 2026

Sources read: probe `97d958e:RBM3D/Probe/T2192Pins.lean` (the nine blocks), `paper/tex/1_2_Intro_model_result.tex:270-280, 340-520`, `bd95cc9:RBM3D/Probe/T2001Endpoints.lean:99-310`, merged `Defs/Sizes.lean`, `Defs/Params.lean`, `Defs/StochDomAt.lean`, `Universality/Pins.lean`, `D500-D506` (`docs/paper-deltas.md:1459-1465`). Paper line numbers below are those of `1_2_Intro_model_result.tex` (labels confirmed by grep: `MR:decol` 357, `Main_DEL_COND` 359, `eq:WO` 363, `eq:psikLinfty` 367, `eq:spectral_domain` 380, `eq:calBetaK` 384, `G_bound` 388, `G_bound_ave` 391, `MR:QUE` 406, `eq:defIE` 408, `Meq:QUE` 411, `Meq:QUE2` 417, `Thm: B_Univ` 452, `MR:QuDiff` 488, `eq:diffu1` 494, `eq:diffu2` 498, `Meq:QdS1` 504, `Meq:QdS2` 507).

### (i) Exponent table

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| `d` | 3 | `3 ≤ d` (pins), `2 ≤ d` (`calB_*`, `W²·W^{d-2}=W^d`) | 1 resp. 0 |
| `sz0` at `n` (`m=n+1`) | `L=4m, W=(2m)^5, lam=(2m)^{-6}, N=(WL)^3`; `n=0`: `4, 32, 1/64, 2^21` | `3 ≤ L`, `0 < W` | `L=4≥3` |
| `𝔠` | 1/6 | `W ≥ N^𝔠` (`1_2:359`) | `W/N^{1/6} = 2.83 m²`: 2.83 at `n=0`, `→∞` |
| `𝔡` | 1/10 | `W^{-3/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`1_2:363`) | `lam/W^{-7/5} = 2m` (2 at `n=0`); admissible for every `𝔡 ≤ 3/10` (equality at 3/10) |
| second pair, same `sz0` | `(𝔠',𝔡')=(1/5,3/10)` | `W^5 ≥ N`, `W^{-6} ≤ lam`, `lam ≤ 10/3` | `W^5≥N`: `(2m)^10 ≥ 64m³`; `W^{-6}=lam` (edge) |
| `κ` | 1/10 | `0<κ`; `|E|,|Re z| ≤ 2-κ` | `Re zI = 1/2 ≤ 19/10`, slack 7/5 |
| `ε` | 1/20 (`zI` check: 1/10) | `0<ε`; `D_{κ,ε}`: `N^{-1+ε} ≤ Im z ≤ 1` (`1_2:380`) | `zI.im = N^{-4/5}`: `N^{-19/20}=9.9e-7 ≤ N^{-9/10}=2.0e-6 ≤ 8.8e-6 ≤ 1` |
| `D` (domain edges) | empty iff `κ>2` or `ε>1` (`N>1`), nonempty at `κ=2, ε=1` (point `i`) | D505 | `κ=3`: `2-κ=-1<0`; `ε=2`: `N^1=2.1e6>1` |
| `τ, D` (decol, locSC, QDiff) | `1/10, 1` / `1/10, 2` | `0<τ, 0<D`; failure `≤ N^{-D}` | free |
| `ε₀, c` (QUE) at `𝔡=1/10` | `1/30, 1/60` | `0<ε₀<𝔡/2=1/20`; `0<c<ε₀ ∧ 𝔡/5=1/50` (`1_2:407-412`) | `1/20-1/30=1/60`; `1/50-1/60=1/300` |
| `queBound` exponent `-(2ε₀)∧(2𝔡/5)+2c+τ` | `τ=1/10`: `7/75 > 0` (Lean instance); `τ=1/200`: `-1/600`; at `𝔡'=3/10`, `τ=1/200`: `-17/600` | `queBound = ofReal(W^e)` (`1_2:416`); nonvacuous iff `e<0` iff `τ < (2ε₀)∧(2𝔡/5) - 2c` | Lean's `inst_QUE` (`τ=1/10`) has a conclusion `≤ W^{7/75} ≥ 1`: true trivially (observation, not a defect of the pin; the ticket mandates that instance verbatim). `inst_QUE_up` (`𝔡=1/5, ε₀=1/15, c=1/30, τ=1/10`): `e=13/150>0`, same. Its docstring says `ε₀ = 1/20·(2/3)` (= 1/30) but the code has `1/15` (docstring slip, constraints hold at 1/15: `1/15<1/10`, `1/30<min(1/15,1/25)`) |
| `explicit ↔ Prec` (D504) | `N^{𝔠τ} ≤ W^τ ≤ N^{τ/d}` | `Bandwidth 𝔠` for `⇒explicit`; `W^d ≤ N` for `⇒Prec` (no `Bandwidth`) | `τ=1/10, n=0`: `1.275 ≤ 1.414 ≤ 1.625` |
| `calB` at `η=1/2, n=0` | `6.1959e-5` | `calB η 0 = W^{-d}Bparam(1-η,0)` (`d≥2`); floor `(Nη)⁻¹ ≤ calB` | `(Nη)⁻¹=9.54e-7`; slack factor 65 |
| `distB` factor | `d^{-(d-2)} = 1/3` | `K ≤ K' ≤ dK` from `zdistInf ≤ zdistD ≤ d·zdistInf` | all 64 differences of `Z_4^3` checked |
| `(eq:WO)` edges on `szE` | `L=n+3, W=(n+2)^6`, `(𝔠,𝔡)=(1/4,1/5)` | `N ≤ W^4` (`L³ ≤ W`) | `n=0`: `27 ≤ 64` (2.37); lower edge `lam=W^{-13/10}=4.5e-3 ≤ 5`; upper edge `lam=5=𝔡⁻¹` (equality) |

Pin table (what each says; class owed; union placement; consumer):
- `decol` (Thm 2.1, `1_2:357-370`): `P(∃ orthonormal eigenbasis, k, x: |μ_k|≤2-κ ∧ ‖ψ_k(x)‖² > N^{-1+τ}) ≤ N^{-D}`; union inside; consumer `decol_of_locSC` (MA-03), `final_shape` (MA-06). Body = `T2001_decol` (`bd95cc9:...:128`) modulo vocabulary (`DecolBad`→`decolBad`, `Pn/failBound`→`seqP/ofReal(Nsz^{-D})`); PASS.
- `locSC` (Thm 2.2, `1_2:386-395`): `(G_bound)`, `(G_bound_ave)` each `≤ N^{-D}`, `∩_z` and `∪_{x,y}`, `∪_a` inside; `M = m I` = `Mband` (`1_2:343`). `calB` term by term: `(lam²+η)⁻¹/(W²(K+W)^{d-2}) + (Nη)⁻¹`, `N=(WL)^d=sz.size` = `1_2:384`. PASS. `|x-y|` read as `W|[x]-[y]|_∞` (D501): `K ∈ [W(k-1), W(k+1)]` gives `K+W ∈ [Wk, W(k+2)]`, hence `K+W ∈ [1/2, 2]·W(k+1)`, so `𝓑_{η,K}` and `𝓑_{η,Wk}` agree up to `2^{d-2}`, absorbed by `W^τ` (`W→∞` by `W ≥ N^𝔠`); the fine-lattice literal form stays uncompiled (D501). Consumers: `locSC_to_UNLocAvgBand` (here), MA-03/04, MA-06.
- `QUE` (Thm 2.3, `1_2:406-420`): per `(E,a)` resp. `(E,A≠∅)`, `N₀` uniform (`∀ᶠ n, ∀ E, ∀ a/A`), window = `queWindow` (`1_2:408`), bound = `queBound` (`1_2:416`), `(Meq:QUE2)` event is `≥` with `W^{d-c}|A|/N` (`1_2:417-419`) = `que2BadMat`. `A ≠ ∅` needed: `que2BadMat_empty_zero` (zero matrix, `E=0`, `A=∅`: `|0-0| ≥ 0` and the window contains `0`). PASS. Consumers `QUE_to_UNQueBand` (here), MA-05 `MAQUE`, MA-06.
- `QDiff` (Thm 2.5, `1_2:488-511`): `(eq:diffu1,2)` `≤ N^{-D}` with `∩_z`, `a,b` inside (D503), then `(Meq:QdS1,2)` per `z ∈ D_{κ,ε}`, `N₀` uniform over `D_{κ,ε}` (D500), `max_{a,b}` as `∀ a b`. `qdBound = W^τ·min(𝓑0^{1/5}𝓑_{W|a-b|}, 𝓑0²)` and `qdBoundExp = W^τ𝓑0²((lam²W^d)^{-1/5}+𝓑0)` equal `1_2:494-510` term by term; profiles `|m|²Θ^{(+,-)}/W^d` (`Theta` at `ξ=‖msc z‖²`, `def:Theta` `1_2:472`; merged `Theta ξ = (1-ξ S^{(B)})⁻¹`) and `m²Θ^{(+,+)}/W^d` (`ξ=msc²`). PASS (vs `T2001_QDiff`: only `blockSet→Iblk`, `bulkDomain→locDomain`, `prof z a b/W^d → profPM/PP` and `QDExp` unfolded). Consumers MA-03 `QDiffFixed_of_ML`, MA-04 `MANetQD`, MA-05 `MAQUE`.
- `BUniv := UNBUniv` (Thm 2.4, `1_2:452-459`): `abbrev`, merged `Universality/Pins.lean:177`; data only the test function `O ∈ C_c^∞`, `k ≥ 1`, `E`. PASS. Consumer `final_shape` (MA-06), UN-52.
- D500: `QDiff` 3rd/4th conjunct. D501: `distB`, `locBad1z`, `qdBound`, `calB_dist_compare`, `calB_distB_compare` (`d^{-(d-2)}` from `K+W ≤ d(K+W)` and `(Nη)⁻¹` term). D503: `qd1Badz`, `qd2Badz`. D504: `explicit_of_stochDomAt` (`N^{𝔠τ} ≤ W^τ` on `{W^τζ<ξ}` gives `{N^{𝔠τ}ζ<ξ}` via `ζ ≥ 0`), `explicit_of_prec`, `prec_of_explicit` (`W^{dτ} ≤ N^τ`). D505: `locDomain_nonempty` (`z=i`, needs `N ≥ 1`), `_empty_kappa`, `_empty_eps`, `domain_extreme`. D502, D506: not in this file. Signed T2001a (`N→∞` in `Admissible`), b (`∩_z` inside), f (`A.Nonempty`), h (`m=msc`, any eigenbasis in `decolBad`, `que2BadMat`).
- §29 (1)-(7): no flow time in any endpoint; no `L^d ≤ W^K` premise (only `W ≥ N^𝔠`); `∀ᶠ n` throughout; `(eq:WO)` and `SizeTendsto` inside `Admissible`; `UNLocAvgBand` uses `W^τ Bctl n (1-Im z)` = `W^τ calB η 0` by `calB_zero_eq_Bctl` (`Bctl = W^{-d}[(lam²+η)⁻¹ + (L^dη)⁻¹] = calB η 0`, exact equality checked below) and `UNQueBand` uses `queBound` literally.
- "Two data, one model": every pin quantifies over `sz` and deterministic constants only. `Admissible` observes `(𝔠,𝔡)` through `Bandwidth`, `WO`; the conclusions of `decol/locSC/QDiff/BUniv` do not contain `𝔠, 𝔡`; `QUE` contains `𝔡` only through `ε₀<𝔡/2, c<𝔡/5` and `queBound`. For `sz0` and the two admissible pairs `(1/6,1/10)`, `(1/5,3/10)`, with `ε₀=1/30, c=1/60, τ=1/200` the exponents are `-1/600` and `-17/600`: the bound at the stronger hypothesis is the stronger one (the exponent is nonincreasing in `𝔡`), so both conclusions hold together. PASS.
- Thm 2.7 is not stated here. `explicit_of_stochDomAt` is stated for an arbitrary `(Ω, P)` (hypotheses `0<𝔠`, `ζ ≥ 0`, `Bandwidth 𝔠`, `StochDomAt P sz.size ξ ζ`), and `(sz.withLam g).{L,W,size} = sz.{L,W,size}` by `withLam := {sz with lam := g}` (merged example `⟨rfl, rfl, rfl⟩`, `Defs/Sizes.lean`), so BA can apply it to `(sz.withLam 0).seqP` (D504).

### (ii) One concrete nondegenerate instance (`d=3`, `sz0`, `n=0`, script output)

Instance: `L=4, W=32, lam=1/64, N=2^21`; `(𝔠,𝔡)=(1/6,1/10)`; `κ=1/10`; `locSC/QDiff`: `ε=1/20, τ=1/10, D=2`; `decol`: `τ=1/10, D=1`; `QUE`: `ε₀=1/30, c=1/60, τ=1/10`; point `zI = 1/2 + i N^{-4/5}`; the endpoint pins `decol, locSC, QUE, QDiff, BUniv` stay hypotheses (owed to MA-03..05, UN-52). External-hypothesis limits (`N→∞`, `W ≥ N^𝔠`, `(eq:WO)`) are computed for all `n` (exact integer checks to `n<5000`, closed forms: `W/N^{1/6} = 2^{3/2} m²`, `lam/W^{-7/5} = 2m`, `N ≥ n`).

Command: `python3 .../scratchpad/T2210/inst.py` (exact `Fraction` arithmetic; floats only for `rpow`). Output:
```
n=0: L,W,lam,N = 4 32 1/64 2097152 N==2^21: True
Admissible(1/6,1/10) n<5000: True
n=0: W/N^(1/6)=2.828  lam/W^(-7/5)=2 (=2m=2)  N=2.1e+06
n=9: W/N^(1/6)=282.8  lam/W^(-7/5)=20 (=2m=20)  N=2.1e+24
n=99: W/N^(1/6)=2.828e+04  lam/W^(-7/5)=200 (=2m=200)  N=2.1e+42
n=9999: W/N^(1/6)=2.828e+08  lam/W^(-7/5)=2e+04 (=2m=20000)  N=2.1e+78
n=999999: W/N^(1/6)=2.828e+12  lam/W^(-7/5)=2e+06 (=2m=2000000)  N=2.1e+114
Admissible(1/5,3/10) n<5000: True
QUE ranges at d=1/10: True True True  (e0<1/20, c<min(1/30,1/50))
queBound exponent, tau=1/10: 7/75 = 0.09333333333333334 (>0: W^+ >=1, bound vacuous)
queBound exponent, tau=1/200: d=1/10: -1/600  d'=3/10: -17/600  monotone: True
QUE ranges at d'=3/10: True True
QUE_up (d=1/5): e0=1/15<1/10: True  c=1/30<min(1/15,1/25): True  exponent tau=1/10: 13/150
D_{1/10,1/10}: |Re|=1/2<=19/10: True  N^-0.9=2.04e-06 <= Im=8.76e-06 <= 1: True
D_{1/10,1/20} (eps of inst_locSC): N^-0.95=9.87e-07 <= Im: True
extreme kappa=2,eps=1, z=i: |0|<=0: True  N^0=1<=1<=1: True | kappa=3: 2-kappa=-1<0 ->empty | eps=2: N^1=2.09715e+06>1 -> empty
N^(c tau)=1.2746 <= W^tau=1.4142 <= N^(tau/d)=1.6245: True
calB(1/2,0)= 6.195904278883183e-05  Bctl(1/2)= 6.195904278883183e-05  equal: True  floor 1/(N eta)= 9.5367431640625e-07  <=: True
calB_blk=STWB for k=0..3: True
Z_4^3 differences checked: 64  violations of 3^-1 B_K<=B_K'<=B_K: 0
szE: L^3<=W and N<=W^4 (W>=N^(1/4)) n<5000: True  n=0: 27<=64, slack 64/27=2.370
szLo lam=W^(-13/10)=0.004487 (<=1/d=5), szUp lam=5=1/d (equality edge)
```
(The `szE` line checks `L³ ≤ W`, `N ≤ W⁴`; the `inst_QUE_up` line uses `𝔡 = 1/5`, whose `(eq:WO)` upper edge `lam=5=𝔡⁻¹` holds with equality.)

### Verdicts

- Target 1, pins `decol`, `locSC`, `QUE`, `QDiff`, `BUniv`: PASS (each matches its paper statement up to the signed readings D500, D501, D503, D504, T2001a/b/f/h; no `T2210a` candidate; no pin fails the "two data" test).
- Target 1, lemmas (`calB_*`, `explicit_of_*`, `prec_of_explicit`, `eventually_forall_of_sections`, `det_of_prec`, domain lemmas) and bridges `locSC_to_UNLocAvgBand`, `QUE_to_UNQueBand` (mathematically: `calB η 0 = Bctl(1-η)` exactly, `0<Im z` on `D_{κ,ε}`; the QUE bridge is a projection): PASS.
- Target 1, instances (`inst_*`, `(eq:WO)` edges, extreme inputs): PASS (all hypotheses hold simultaneously in the table above). Observation for the dispatcher: `inst_QUE` and `inst_QUE_up` have `τ=1/10`, so their conclusion bound is `W^{7/75}` resp. `W^{13/150} ≥ 1` (vacuous conclusion, nondegenerate hypotheses; a nonvacuous choice is `τ ≤ 1/200` at `𝔡=1/10`); `inst_QUE_up`'s docstring has `ε₀ = 1/20·(2/3)` against `1/15` in the code. Both are verbatim moves, so no action unless the dispatcher wants an amendment.
- Targets 2 (imports) and 3 (registry): no mathematical content; not assessed here.

Overall verdict: PASS.

## (b) Script output (stage 1b, claude-sonnet-5-5; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2210`, branch `t/T2210`, commit `72ac37b` made at Mon Oct  5 20:19:47 UTC 2026 (`date -u`, same tool call))

Command: `git diff --stat main...t/T2210`
```
RBM3D/Endpoints.lean   | 799 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   7 +-
 2 files changed, 805 insertions(+), 1 deletion(-)
```
Command: `lake build RBM3D.Endpoints 2>&1 | grep -E "Endpoints|Build completed|error"` (cached rerun at the commit) and, from the tool log, the same build run right after the last edit of the file (line `✔ [3329/3329] Built RBM3D.Endpoints (3.9s)`, no warning on `RBM3D/Endpoints.lean`):
```
Build completed successfully (3329 jobs).
```
Command: `lake build` (whole library; root `RBM3D.lean` does not yet import `RBM3D.Endpoints`, the hub adds it at merge): `Build completed successfully (4013 jobs).`

Registry pre-check: scratch file (outside the repo) `import RBM3D` / `import RBM3D.Endpoints` / `#assert_rbm_axioms`; command `lake env lean precheck.lean > precheck.out; echo $?` gave exit 0 (35.7 s). Selected lines of `precheck.out` (259 lines; `grep`/`sed` by script):
```
axiom audit: 6225 theorems, 2195 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 132 (borrowed 1, owed 103, structural 24, refuted 4).
registry: 2 borrowed + 148 owed + 79 structural + 4 refuted; 101 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
  RBM.Endpoints.decol: 1 [no certificate]
  RBM.Endpoints.locSC: 5 [no certificate]
  RBM.Endpoints.QUE: 4 [no certificate]
  RBM.Endpoints.QDiff: 1 [no certificate]
  RBM.Endpoints.BUniv: 1 [no certificate]
  RBM.Univ.UNLocAvgBand: 17 [no certificate]
  RBM.Univ.UNQueBand: 15 [no certificate]
191:  RBM.Univ.UNLocAvgBand,
192:  RBM.Univ.UNQueBand,
non-vacuity certificates: 0 of 150 premises in the two ledgers; the rest are not known to  ...
```
Registry diff (`git diff -U0 main...t/T2210 -- RBM3D/Test/Axioms.lean`, `+`/`-` lines cut at 110 columns):
```
-   `RBM.Gauss.Sizes.STExpWardII] -- `6:137-141` Ward term, regime (ii): S6-12; S6-01 (T2204, DECISIONS §67: o
+   `RBM.Gauss.Sizes.STExpWardII, -- `6:137-141` Ward term, regime (ii): S6-12; S6-01 (T2204, DECISIONS §67: o
+   `RBM.Endpoints.decol, -- Thm 2.1 `1_2:357-370`: MA-03 `decol_of_locSC` + MA-04; MA-01 (T2210, DECISIONS §1
+   `RBM.Endpoints.locSC, -- Thm 2.2 `1_2:386-395`: MA-04 `MANetLoc` from MA-03; MA-01 (T2210, DECISIONS §16, 
+   `RBM.Endpoints.QUE, -- Thm 2.3 `1_2:406-420`: MA-05 `MAQUE`; MA-01 (T2210, DECISIONS §16, §20: owed)
+   `RBM.Endpoints.QDiff, -- Thm 2.5 `1_2:488-511`: MA-04 `MANetQD` from MA-03; MA-01 (T2210, DECISIONS §16, §
+   `RBM.Endpoints.BUniv] -- Thm 2.4 `1_2:452-459`, the `abbrev` of `UNBUniv`: UN-52, MA-06; MA-01 (T2210, DEC
```

`#print axioms` of the 46 public theorems (scratch file `import RBM3D.Endpoints` + 46 lines `#print axioms RBM.Endpoints.<name>`, `lake env lean`, exit 0). Lines ending `depends on axioms: [propext, Classical.choice, Quot.sound]`: **46 of 46**. Names (prefix `RBM.Endpoints.` stripped by script):
```
calB_zero_eq_Bctl calB_blk_eq_STWB inv_size_mul_le_calB calB_antitone calB_nonneg calB_dist_compare calB_distB_compare
explicit_of_stochDomAt explicit_of_prec prec_of_explicit eventually_forall_of_sections det_of_prec STWB_nonneg Nsz_pos locDomain_im_pos
locDomain_nonempty locDomain_empty_kappa locDomain_empty_eps locSC_to_UNLocAvgBand QUE_to_UNQueBand Inst.zI_dom Inst.zI_im_pos Inst.zI_im_le
Inst.zI_re_le Inst.inst_decol Inst.inst_locSC Inst.inst_QUE Inst.inst_QDiff Inst.inst_BUniv Inst.inst_bridge_loc Inst.inst_bridge_que
Inst.szE_size_le Inst.szE_bandwidth Inst.szE_tendsto Inst.szLo_admissible Inst.szUp_admissible Inst.inst_locSC_lo Inst.inst_locSC_up
Inst.inst_QUE_up Inst.domain_extreme Inst.locBad1_empty_kappa Inst.im_mE_edge Inst.que2BadMat_univ Inst.que2BadMat_empty_zero Inst.inst_calB
Inst.inst_distB_compare
```
`sorry`/`admit`/`native_decide`/`axiom` in `RBM3D/Endpoints.lean`: `grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Endpoints.lean` gave no line.

Verbatim criterion (`git show 97d958e:RBM3D/Probe/T2192Pins.lean`, `sed -n` ranges, python `block in text`):
```
B1 probe:48-210 (163 lines) in Endpoints.lean: True (offset 2230)
B2 probe:213-362 (150 lines) in Endpoints.lean: True (offset 11967)
B3 probe:365-462 (98 lines) in Endpoints.lean: True (offset 20133)
B4 probe:1094-1129 (36 lines) in Endpoints.lean: True (offset 25347)
B5 probe:2048-2070 (23 lines) in Endpoints.lean: True (offset 26826)
B6 probe:2104-2190 (87 lines) in Endpoints.lean: True (offset 27898)
B7 probe:2275-2384 (110 lines) in Endpoints.lean: True (offset 33272)
B8 probe:2395-2434 (40 lines) in Endpoints.lean: True (offset 39375)
B9 probe:2460-2474 (15 lines) in Endpoints.lean: True (offset 41674)
order B1..B9 increasing: True ; total moved lines: 722
```
The remainder of `Endpoints.lean` after replacing the nine blocks by markers (python, blank lines dropped; module docstring body elided) is: copyright `:1-5`; `import RBM3D.Universality.Pins`; module docstring; the three `set_option`s, `noncomputable section`, three `open` lines (probe `:36-44`); `namespace RBM.Endpoints`; `B1 B2 B3`; one header line `/-! ## 4. The domain lemmas for `𝐃_{κ,ε}` and the positivity of `𝓑` -/`; `section Domain`; `variable {d : ℕ}`; `B4`; `end Domain`; `B5 … B9`; `end Inst`; `end RBM.Endpoints`. File length: `wc -l` = 799 (ticket estimate about 780, split range 610 to 990).

Check-file equality: scratch file = `docs/tickets/checks/T2210-check.lean` cut before its section 3 (`/-! ## 3.`), plus `import RBM3D.Endpoints`, `end RBM.Endpoints.T2210Check`, 20 `example : @RBM.Endpoints.T2210Check.X = @RBM.Endpoints.X := rfl` (the 20 vocabulary defs) and 5 `example : RBM.Endpoints.T2210Check.X_pin = RBM.Endpoints.X := rfl` (`X` in `decol locSC QUE QDiff BUniv`); `grep -c "^example"` = 25; `lake env lean checkeq.lean`: `exit 0`; lines containing `error`: 0.

Name-clash grep (`bash clash.sh`: `grep -rn --include=*.lean` for `RBM.Endpoints` outside `Endpoints.lean`, then the head of every `theorem|lemma|def|abbrev|structure|instance` with each of the 78 names, outside `Endpoints.lean`; lines cut at 120 columns). The 78 names: 29 `def`/`abbrev`, 49 `theorem` (3 `private`, 46 public; script count from the file):
```
--- grep -rn 'RBM.Endpoints' RBM3D (other files than Endpoints.lean), --include='*.lean':
RBM3D/Test/Axioms.lean:243:   `RBM.Endpoints.decol, -- Thm 2.1 `1_2:357-370`: MA-03 `decol_of_locSC` + MA-04; MA-01 (T22
RBM3D/Test/Axioms.lean:244:   `RBM.Endpoints.locSC, -- Thm 2.2 `1_2:386-395`: MA-04 `MANetLoc` from MA-03; MA-01 (T2210,
RBM3D/Test/Axioms.lean:245:   `RBM.Endpoints.QUE, -- Thm 2.3 `1_2:406-420`: MA-05 `MAQUE`; MA-01 (T2210, DECISIONS §16, 
RBM3D/Test/Axioms.lean:246:   `RBM.Endpoints.QDiff, -- Thm 2.5 `1_2:488-511`: MA-04 `MANetQD` from MA-03; MA-01 (T2210, 
RBM3D/Test/Axioms.lean:247:   `RBM.Endpoints.BUniv] -- Thm 2.4 `1_2:452-459`, the `abbrev` of `UNBUniv`: UN-52, MA-06; M
RBM3D/Universality/FreeConvStability.lean:46:`open RBM.Endpoints` becomes `open RBM`; RBM2D's `spectralM`, `spectralM_im
RBM3D/Universality/FreeConv.lean:29:`RBM3D.Universality.Pins` (`mV` `:237`, `IsFreeConv32` `:249`) and `open RBM.Endpoin
--- name-clash grep of the 78 declaration names (declaration heads in other files of RBM3D):
RBM3D/Green/FlucVanish.lean:1355:private noncomputable def zI : ℂ := (1 / 2 : ℂ) + Complex.I / 2
--- done; distinct names:       78 of       77
```
The seven `RBM.Endpoints` hits outside the file are the five new registry lines and two port-note docstrings (RBM2D's `open RBM.Endpoints`); `grep -rn --include=*.lean "^open.*RBM.Endpoints" RBM3D` gave no line. The one head hit is the `private def zI` in `RBM3D/Green/FlucVanish.lean:1355` (other namespace, `private`): no clash.

Ports: no RBM1D/RBM2D text copied in this ticket (the move source is the T2192 probe at `97d958e`); RBM1D/RBM2D were not touched.

Target statements, extracted by script from `RBM3D/Endpoints.lean` (`python3 extract.py whole decol locSC QUE QDiff BUniv`; `:n` is the file line):
```
-- :165
def decol : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
-- :172
def locSC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
-- :182
def QUE : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
        (∀ a : Zd d (sz.L n),
          Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ) ∧
        (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
          Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ)
-- :197
def QDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      (Sizes.seqP sz {ω | qd1Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, sz.locDomain κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im
-- :209
abbrev BUniv : Prop := UNBUniv
```
Form bridge and UN bridges (`extract.py stmt …`, cut at `:=`):
```
-- :376
theorem explicit_of_stochDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → Ω → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : StochDomAt P sz.size ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, P {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))
-- :519
theorem locSC_to_UNLocAvgBand : locSC → UNLocAvgBand
-- :530
theorem QUE_to_UNQueBand : QUE → UNQueBand
```
Compiled nonempty instances at `sz0` (`n = 0`; `d = 3`; the endpoint pin is the hypothesis `h`, every deterministic hypothesis discharged inside the proof; `extract.py stmt …`). `inst_bridge_loc` (`:608`), `inst_bridge_que` (`:618`), `inst_calB`, `inst_distB_compare`, the `zI` point and the `(eq:WO)` edge and extreme-input theorems are the other 21 of the 26 instance theorems, in the file at the lines given by `grep -n "^theorem" RBM3D/Endpoints.lean`:
```
-- :561
theorem inst_decol (h : decol) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))
-- :567
theorem inst_locSC (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))
-- :575
theorem inst_QUE (h : QUE) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
      (∀ a : Zd 3 (sz0.L n),
        Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) ∧
      (∀ A : Finset (Zd 3 (sz0.L n)), A.Nonempty →
        Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E A (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10))
-- :587
theorem inst_QDiff (h : QDiff) :
    ∀ᶠ n in atTop,
      (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im
-- :600
theorem inst_BUniv (h : BUniv) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0)
```

### Narrative
- The file was assembled by a python script (`assemble.py`, scratch) from `git show 97d958e:RBM3D/Probe/T2192Pins.lean` line ranges; the nine blocks were not edited. The only imports added are `RBM3D.Universality.Pins`; no block needed another module, and the first build succeeded with no error.
- Registry: the five lines of Targets 3 were appended (the preceding last entry `STExpWardII]` became `STExpWardII,`); no other name was flagged by the pre-check (`premises found by scanning: 132 (borrowed 1, owed 103, structural 24, refuted 4)` is the sum of the four classes; an unregistered premise would be a `throwError` (`RBM3D/Test/Axioms.lean:486-490`), and the pre-check exited 0).
- Lines 191-192 of `precheck.out` list `RBM.Univ.UNLocAvgBand` and `RBM.Univ.UNQueBand` among the registered premises that carry nothing yet, as the ticket expects; their owed lines were not deleted.
- `RBM.Endpoints.BUniv` is carried by `inst_BUniv (h : BUniv)`; the pre-check shows it with 1 resting theorem, consistent with the fifth registry line.
- No obstruction; no hypothesis added; no statement, docstring or signature changed.

## (c) Verified Mathlib and project names
Names appearing in the proof terms of the moved blocks (script: regex over the file with docstrings and comments stripped; 34 names). All resolve: `lake build RBM3D.Endpoints` compiles the file. No name was checked as absent.
```
Complex.I Complex.I_im Complex.I_re Complex.conj_mul' Complex.star_def ENNReal.ofReal ENNReal.ofReal_lt_one Eventually.of_forall
Filter.not_eventually Finset.card_univ Finset.sum_comm Finset.sum_congr Finset.sum_filter Finset.univ Nat.cast_nonneg Nat.cast_zero
Nat.le_mul_of_pos_left Nat.le_self_pow Nat.mul_le_mul_left Nat.pos_of_ne_zero Nat.pow_le_pow_left Pi.single Pi.star_apply Real.one_lt_rpow
Real.pow_rpow_inv_natCast Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow Real.rpow_mul Real.rpow_neg_one Real.rpow_nonneg
Real.rpow_pos_of_pos Real.sqrt Set.mem_univ Set.univ
```

## (d) Open issues and paper-delta candidates
1. No paper-delta candidate `T2210a…` (every pin matches its paper line up to the signed readings D500, D501, D503, D504, T2001a/b/f/h; section (a) verdict PASS, not re-assessed).
2. Observation (section (a) and this run): `inst_QUE` (`τ = 1/10`) and `inst_QUE_up` (`𝔡 = 1/5`, `ε₀ = 1/15`, `c = 1/30`, `τ = 1/10`) have `queBound` exponent `7/75` resp. `13/150`, positive (arithmetic of the exponent `-(2ε₀)∧(2𝔡/5)+2c+τ` from the arguments in the statements), so their conclusions are weak (`≤ W^e` with `W^e ≥ 1`); hypotheses are nondegenerate and the theorems are the ticket-mandated verbatim text. The exponent is negative iff `τ < (2ε₀)∧(2𝔡/5) - 2c`, which is `1/25 - 1/30 = 1/150` at `(𝔡, ε₀, c) = (1/10, 1/30, 1/60)` (section (a) lists `τ = 1/200` with exponent `-1/600`); not done here (no statement change allowed).
3. Observation: the docstring of `inst_QUE_up` (`Endpoints.lean:702`) says `ε₀ = 1/20·(2/3)` while the statement uses `1/15` (`:707`); the move is verbatim, so the docstring was not changed.
4. Observation: `RBM3D/Universality/FreeConv.lean:29` and `FreeConvStability.lean:46` say "no such namespace in RBM3D" about RBM2D's `open RBM.Endpoints`; those are port-note docstrings and no code opens `RBM.Endpoints`; after the merge the namespace exists.
5. The literal fine-lattice comparison `𝓑_{η,|x-y|} ≍ 𝓑_{η,W|[x]-[y]|_∞}` (factor `2^{d-2}`) is not compiled here (ticket Not-targets; D501).
6. Hub at merge: add `import RBM3D.Endpoints` after the last `import` line of `RBM3D.lean`, run the full `lake build`, and union the registry lines of `RBM3D/Test/Axioms.lean` with the other open tickets (ticket start condition, §20 (3)).
