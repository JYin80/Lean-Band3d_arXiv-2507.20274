Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  2 17:55:48 UTC 2026

Notation: the ticket's `λ` is the paper's `\ilambda`, which `paper/tex/main.tex:199` defines as `g`; it is the `g` of `(eq:variancematrix)` (`1_2_Intro_model_result.tex:303`) and of `(eq:WO)`. Below `g` means this quantity. `d = 3`, `N = (WL)^d`. Source lines are in `paper/tex/1_2_Intro_model_result.tex` ("1_2:").

### (i) Exponent table

Size sequence used below: `L_n = W_n = 4n` (`n ≥ 1`), `g_n = W_n^{-1}`, so `N_n = W_n^6`, `W_n = N_n^{1/6}`.

| Constant | Value | Constraint (source) | Slack |
|---|---|---|---|
| `𝔠` | 1/7 | `W ≥ N^𝔠` (1_2:359). On the sequence `W = N^{1/(2d)} = N^{1/6}`, so `𝔠 ≤ 1/6` | 1/6 − 1/7 = 1/42 |
| `𝔡` | 2/5 | `W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}` (1_2:363). With `g = W^{-1}`: `𝔡 ≤ 1/2`; `g_n ≤ 1/4 ≤ 5/2` | 1/2 − 2/5 = 1/10 |
| `κ` | 1/10 | `0 < κ < 2` for the band model (1_2:380); for `MR:decol_BA` `κ < e_g` (1_2:649; `e_g` is only defined as the edge of `supp μ_N`, 1_2:624, no formula) | band: 19/10; BA: not evaluated, see verdict |
| `ε` | 1/25 | domain `D_{κ,ε}`, `N^{-1+ε} ≤ η ≤ 1` (1_2:380). The QUE `η_E` lies in it iff `N^ε ≤ N η_E`; in general `N η_E ≥ W^{𝔡−ε₀} ≥ N^{𝔠(𝔡−ε₀)}`, so `ε ≤ 𝔠(𝔡−ε₀) = 3/70` | 3/70 − 1/25 = 1/350 (generic); on the sequence `N η_E = W^{2/5} = N^{1/15}`, slack 1/15 − 1/25 = 2/75 |
| `τ` (local law, QD) | 1/50 | any `τ > 0`; the bound `W^τ B_{η,0}` is nontrivial at `η = N^{-1+ε}` iff `τ/6 < ε` (`B ≈ N^{-ε} + W^{-1}` there) | ε − τ/6 = 1/25 − 1/300 = 11/300 |
| `D` | 10 | any `D > 0` (probability `1 − N^{-D}`), `N ≥ N₀(𝔠,𝔡,κ,ε,τ,D)` | none |
| `ε₀` | 1/10 | `0 < ε₀ < 𝔡/2` (1_2:407) = 1/5 | 1/10 |
| `c` (QUE) | 1/20 | `0 < c < ε₀ ∧ 𝔡/5` (1_2:410) = 2/25 | 2/25 − 1/20 = 3/100 |
| `τ` (QUE) | 1/50 | exponent `(2ε₀)∧(2𝔡/5) − 2c − τ > 0` (1_2:411–414), i.e. `τ < 2(ε₀∧𝔡/5 − c) = 3/50` | exponent = 4/25 − 1/10 − 1/50 = 1/25; τ slack 1/100 |
| QUE Markov terms | `𝔡−ε₀, 2𝔡/5, 2ε₀` = 3/10, 4/25, 1/5 | proof (1_2:541–543): `W^{-𝔡+ε₀} + W^{-2𝔡/5} + W^{-2ε₀}`. `ε₀ < 𝔡/2` gives `𝔡−ε₀ > 𝔡/2 > 2𝔡/5`, so the minimum is `(2ε₀)∧(2𝔡/5)`, as stated in (Meq:QUE) | 3/10 − 4/25 = 7/50 |
| `I_E(ε₀)` width | `η_E = W^{-ε₀} g W^{d/2}/N`, `N η_E = W^{2/5}` on the sequence | `N η_E ≥ W^{𝔡−ε₀} > 1`: many eigenvalues in the window. `η_E ≤ g²/L^d` iff `W^{-ε₀} ≤ g W^{d/2}`; `g²W^d/(N η_E) = g W^{d/2+ε₀} ≥ W^{𝔡+ε₀}` | on the sequence `W^{3/5}` (2.30 at `n=1`) |
| `B_{η,K}` at `η = N^{-1+ε}` (1_2:384) | `K=0`: `≈ W^{-1} + N^{-ε}` | `(g²+η)^{-1}/(W²(K+W)^{d-2}) + 1/(Nη)`; here `η ≪ g²`, first term `g^{-2}W^{-d} = W^{-1}` | `W^τ B → 0` (output below) |
| `B_{η,K}` at `η = 1` | `K=0`: `≈ W^{-3} + N^{-1}` | `(1+g²)^{-1}/W^d + 1/N` | far below the other end |
| `(eq:BetaK)` (1_2:514) | `B_{η,K} ≍ (Nη)^{-1} ≥ (g²W^d)^{-1}` for `η ≤ g²/L^d` | holds at `η_E` since `η_E ≤ g²/L^d`; `(g²W^d)^{-1} = W^{-1}` | at `n=100`: `B = 0.0935`, `(Nη)^{-1} = 0.0910`, `W^{-1} = 0.0025` |
| universality choice | `ε₀ = 𝔡/3`, `c = 𝔡/6` (1_2:570–575) | `ε₀ < 𝔡/2`, `c < ε₀ ∧ 𝔡/5` hold; exponent `(2ε₀)∧(2𝔡/5) − 2c = 𝔡/15` (paper: `W^{-𝔡/15+τ}`); the bad window `N^{-1}W^{𝔡/3}` lies inside `I_E(𝔡/3)` | `𝔡/15 = 2/75` (τ < 2/75; 1/50 < 2/75) |

### (ii) One concrete nondegenerate instance

`d = 3`, `(L_n, W_n, g_n) = (4n, 4n, 1/(4n))`, `𝔠 = 1/7`, `𝔡 = 2/5`, `κ = 1/10`, `ε = 1/25`, `ε₀ = 1/10`, `c = 1/20`, `τ = 1/50`. Here `g_n → 0` and `N_n = (4n)^6 → ∞`, `L_n ≥ 3`. Largest `N` shown is `4.1e15` at `n = 100`; the sequence is not astronomically large at `n=1`. The script checks `W^7 ≥ N` and `W^{-11/10} ≤ W^{-1}` by exact integer comparisons (10th powers), the other lines in floating point.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/pre.py`

```
QUE constraints: 0<e0<fd/2: True | 0<c<min(e0,fd/5): True min= 2/25
QUE prob exponent min(2e0,2fd/5)-2c-tau = 1/25 0.04 >0: True
Markov terms exps (fd-e0, 2fd/5, 2e0): 3/10 4/25 1/5 ; fd-e0 > 2fd/5: True
eps <= fc*(fd-e0): True 0.04285714285714286  0<kap<2: True
n=1: L=W=4 N=4096 g=0.25 | W>=N^(1/7):True lower W^(-3/2+fd)=0.2176<=g:True g<=1/fd:True L>=3:True
   QUE eta=W^-e0*g*W^(d/2)/N=0.0004251; N*eta=1.741 (=W^0.4=1.741); N^(-1+eps)=0.0003405 <=eta:True; eta<=g^2/L^d=0.0009766:True; eta<=1
   eta=N^(-1+eps)  B_(eta,0)=0.9656  B_(eta,Kmax=24)=0.7525  W^tau*B_(eta,0)=0.9928  (N*eta)^-1=0.717
   eta_QUE         B_(eta,0)=0.8227  B_(eta,Kmax=24)=0.6098  W^tau*B_(eta,0)=0.8458  (N*eta)^-1=0.5743
   eta=1           B_(eta,0)=0.01495  B_(eta,Kmax=24)=0.002345  W^tau*B_(eta,0)=0.01537  (N*eta)^-1=0.0002441
   QUE bound W^(-min(2e0,2fd/5)+2c+tau) = 0.9461
n=10: L=W=40 N=4.096e+09 g=0.025 | W>=N^(1/7):True lower W^(-3/2+fd)=0.01729<=g:True g<=1/fd:True L>=3:True
   QUE eta=W^-e0*g*W^(d/2)/N=1.068e-09; N*eta=4.373 (=W^0.4=4.373); N^(-1+eps)=5.917e-10 <=eta:True; eta<=g^2/L^d=9.766e-09:True; eta<=1
   eta=N^(-1+eps)  B_(eta,0)=0.4376  B_(eta,Kmax=2400)=0.413  W^tau*B_(eta,0)=0.4711  (N*eta)^-1=0.4126
   eta_QUE         B_(eta,0)=0.2537  B_(eta,Kmax=2400)=0.2291  W^tau*B_(eta,0)=0.2731  (N*eta)^-1=0.2287
   eta=1           B_(eta,0)=1.562e-05  B_(eta,Kmax=2400)=2.562e-07  W^tau*B_(eta,0)=1.681e-05  (N*eta)^-1=2.441e-10
   QUE bound W^(-min(2e0,2fd/5)+2c+tau) = 0.8628
n=100: L=W=400 N=4.096e+15 g=0.0025 | W>=N^(1/7):True lower W^(-3/2+fd)=0.001373<=g:True g<=1/fd:True L>=3:True
   QUE eta=W^-e0*g*W^(d/2)/N=2.682e-15; N*eta=10.99 (=W^0.4=10.99); N^(-1+eps)=1.028e-15 <=eta:True; eta<=g^2/L^d=9.766e-14:True; eta<=1
   eta=N^(-1+eps)  B_(eta,0)=0.2399  B_(eta,Kmax=240000)=0.2374  W^tau*B_(eta,0)=0.2705  (N*eta)^-1=0.2374
   eta_QUE         B_(eta,0)=0.09353  B_(eta,Kmax=240000)=0.09103  W^tau*B_(eta,0)=0.1054  (N*eta)^-1=0.09103
   eta=1           B_(eta,0)=1.562e-08  B_(eta,Kmax=240000)=2.6e-11  W^tau*B_(eta,0)=1.761e-08  (N*eta)^-1=2.441e-16
   QUE bound W^(-min(2e0,2fd/5)+2c+tau) = 0.7869
--- universality specialisation (paper 1_2_Intro_model_result.tex:577-578): e0=fd/3, c=fd/6
0<e0<fd/2: True | 0<c<min(e0,fd/5): True | exponent min(2e0,2fd/5)-2c = 2/75 = fd/15: 2/75 | tau=1/50 < fd/15: True
n=1: bad-window half-width N^-1 W^(fd/3)=0.0002937 <= I_E(e0=fd/3) half-width=0.0004059: True
n=10: bad-window half-width N^-1 W^(fd/3)=3.993e-10 <= I_E(e0=fd/3) half-width=9.442e-10: True
n=100: bad-window half-width N^-1 W^(fd/3)=5.427e-16 <= I_E(e0=fd/3) half-width=2.196e-15: True
--- asymptotics of B at eta=N^(-1+eps), K=0 along L=W=4n: terms (g^2+eta)^-1/W^d and 1/(N eta)
n=1000: first=0.00025 (W^-1=0.00025) second=N^-eps=0.1366  W^tau*(sum)=0.1616
n=1000000: first=2.5e-07 (W^-1=2.5e-07) second=N^-eps=0.02603  W^tau*(sum)=0.03528
n=1000000000000: first=2.5e-13 (W^-1=2.5e-13) second=N^-eps=0.0009452  W^tau*(sum)=0.001689
```

External hypothesis: none of the targets (the `Prop` pins of the ticket, `MR:decol` … `MR:decol_BA`) has Landon–Sosoe–Yau Thm 2.2 as a hypothesis; it enters only in the proof of `Thm: B_Univ` (DECISIONS §5), so no limit computation for it belongs to this ticket's pins. The LSY text is not in the repository, so its limit computation is not done here.

### Verdict

- Endpoint pins for `MR:decol`, `MR:locSC`, `MR:QUE`, `MR:QuDiff`, `Thm: B_Univ` (band model, `g` a sequence with `(eq:WO)`): **PASS**. All hypotheses hold at once on the sequence above at `n = 1, 10, 100`; every exponent closes with the slack in (i).
- `MR:decol_BA`: **PASS** for the shared hypotheses `(Main_DEL_COND)`, `(eq:WO)` (same sequence). The paper gives no formula for `e_g` (1_2:624, 7_8:1818) and `M^{(B)}`, `m` of `(self_m)` are defined in the proofs (not evaluated here); the pin must take `e_g` as an explicit argument with `0 < κ < e_g`, as the ticket allows. Not a blocker for the Prop pins.
- Generic-`ε` note: `ε ≤ 𝔠(𝔡−ε₀)` is derived from `W ≥ N^𝔠`; the paper fixes `ε` only as "arbitrarily small" (1_2:807), so a pin keeps `ε` a universally quantified positive constant.

## (b) Script output and survey — Fri Oct  2 18:51:23 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2001`, branch `t/T2001`, probe commit `bd95cc9` (`main` = `3c11d7b`). RBM2D read at `c9a24cf` (its HEAD is now `0c1330a`). Coverage table: `docs/reports/T2001-coverage.md` (scripts in its appendix).

```
$ lake env lean RBM3D/Probe/T2001Endpoints.lean | (group the `depends on axioms` lines by axiom list)
[propext, Classical.choice, Quot.sound]: T2001_decol T2001_locSC T2001_QUE T2001_BUniv T2001_QDiff T2001_decol_BA T2001_BA_BUniv_literal admissible_witnessSeq
$ lake build RBM3D.Probe.T2001Endpoints 2>&1 | tail -2
info: RBM3D/Probe/T2001Endpoints.lean:509:0: 'RBM.Probe.admissible_witnessSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3254 jobs).
$ grep -nE "sorry|admit|native_decide|^[[:space:]]*axiom[[:space:]]" RBM3D/Probe/T2001Endpoints.lean | wc -l
0
$ git diff --stat main...t/T2001
 RBM3D/Probe/T2001Endpoints.lean | 511 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 511 insertions(+)
$ pin extents (script on the file)
RBM3D/Probe/T2001Endpoints.lean:128-133 (6 lines) def T2001_decol : Prop
RBM3D/Probe/T2001Endpoints.lean:158-165 (8 lines) def T2001_locSC : Prop
RBM3D/Probe/T2001Endpoints.lean:195-204 (10 lines) def T2001_QUE : Prop
RBM3D/Probe/T2001Endpoints.lean:230-238 (9 lines) def T2001_BUniv : Prop
RBM3D/Probe/T2001Endpoints.lean:297-307 (11 lines) def T2001_QDiff : Prop
RBM3D/Probe/T2001Endpoints.lean:353-358 (6 lines) def T2001_BA_decol : Prop
RBM3D/Probe/T2001Endpoints.lean:362-370 (9 lines) def T2001_BA_locSC : Prop
RBM3D/Probe/T2001Endpoints.lean:373-383 (11 lines) def T2001_BA_QUE : Prop
RBM3D/Probe/T2001Endpoints.lean:389-403 (15 lines) def T2001_BA_BUniv : Prop
RBM3D/Probe/T2001Endpoints.lean:408-418 (11 lines) def T2001_BA_BUniv_literal : Prop
RBM3D/Probe/T2001Endpoints.lean:422-445 (24 lines) def T2001_BA_QDiff : Prop
RBM3D/Probe/T2001Endpoints.lean:448-449 (2 lines) def T2001_decol_BA : Prop
RBM3D/Probe/T2001Endpoints.lean:464-498 (35 lines) theorem admissible_witnessSeq : Admissible 3 (1 / 7) (2 / 5) witnessSeq
$ sed -n 128,133p RBM3D/Probe/T2001Endpoints.lean     # the shortest pin, in full
def T2001_decol : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, 0 < 𝔠 → 0 < 𝔡 → ∀ s : SizeSeq, Admissible d 𝔠 𝔡 s →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
      ∀ᶠ n in atTop,
        Pn d s n {ω | DecolBad d (s.L n) (s.W n) 2 κ τ (Hmat d (s.L n) (s.W n) ω)} ≤
          failBound (s.N d n) D
$ sed -n 464p RBM3D/Probe/T2001Endpoints.lean         # instance: the shared hypotheses are satisfiable
theorem admissible_witnessSeq : Admissible 3 (1 / 7) (2 / 5) witnessSeq := by
$ name-clash grep (grep -rnE '(def|theorem|structure|abbrev|class|inductive|instance) (\S+\.)?<name>\b' RBM3D --exclude-dir=Probe, 53 new public names)
0 clashes
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Endpoints.lean
(empty: the ported file is unchanged between c9a24cf and HEAD)
ports (copy and change, RBM2D/RBM2D/Endpoints.lean @c9a24cf): lines 51-52 mSC, 56-59, 63-65, 74-75, 81-93, 117-154, 159-162, 190-197, 202-218
coverage file (Summary and Checks): 172 rows (170 TeX + 2 pseudo): class i=17, ii=3, iii=18, iv=134; labels 617 = 333 (Part A) + 284 (Part B); 87 further labels occur only in commented-out TeX (Part C)
RBM3D citations: 138 distinct declarations, 138 verified at the cited file:line, 0 mismatches
RBM2D citations: 128 distinct declarations in 72 files, 128 verified by git grep -n at c9a24cf, 0 mismatches
```

### Endpoint table (ticket item 1)

H0 = `d ≥ 3` (1_2:358); `(Main_DEL_COND)` `W ≥ N^𝔠` (1_2:359-361); `(eq:WO)` `W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}` (1_2:363), `g = \ilambda = λ^{-1}` (1_2:256); `N = (WL)^d` (1_2:263); `S(g)` of `(eq:variancematrix)` (1_2:303-306); `D_{κ,ε} = {|Ê| ≤ 2-κ, N^{-1+ε} ≤ η ≤ 1}` (1_2:380-382); `𝓑_{η,K} = (g²+η)^{-1}/(W²(K+W)^{d-2}) + 1/(Nη)` (1_2:384). "Lean on main" lists what states any part of the endpoint (class and signatures in the coverage file); pins are in the probe.

| endpoint | TeX | extra hypotheses and conclusion | Lean on main | pin |
|---|---|---|---|---|
| `(eq:psikLinfty)` Thm 2.1 | 1_2:366-369 | any small κ,τ>0, large D, N≥N₀: P(max_{k:\|λ_k\|≤2-κ}‖ψ_k‖²_∞ ≤ N^{-1+τ}) ≥ 1-N^{-D} | none (resolvent norm only: Analysis/Resolvent.lean:110) | `T2001_decol` |
| `(G_bound)` Thm 2.2 | 1_2:388-390 | κ,ε,τ>0, D: ∩_{z∈D_{κ,ε}}∩_{x,y}{\|G_xy-M_xy\|² ≤ W^τ 𝓑_{η,\|x-y\|}} w.p. ≥ 1-N^{-D}, M=mI | none | `T2001_locSC` |
| `(G_bound_ave)` | 1_2:391-393 | same; ∩_z{max_a\|W^{-d}Σ_{x∈[a]}G_xx - m\| ≤ W^τ 𝓑_{η,0}} | none | `T2001_locSC` |
| `(Meq:QUE)` Thm 2.3 | 1_2:411-415 | ε₀∈(0,𝔡/2), 0<c<ε₀∧𝔡/5, any τ>0, N large: sup_{\|E\|≤2-κ}max_a P(max_{i,j:λ_i,λ_j∈𝓘_E}\|Σ_{x∈[a]}ψ̄_iψ_j - (W^d/N)δ_ij\| ≥ W^{d-c}/N) ≤ W^{-(2ε₀)∧(2𝔡/5)+2c+τ}, 𝓘_E: \|x-E\|≤W^{-ε₀}gW^{d/2}/N (1_2:408) | none | `T2001_QUE` |
| `(Meq:QUE2)` | 1_2:417-420 | any A⊂Z_L^d (A≠∅, T2001f): sup_E P(max_{k:λ_k∈𝓘_E}\|Σ_{a∈A}Σ_{x∈[a]}\|ψ_k\|² - W^d\|A\|/N\| ≥ W^{d-c}\|A\|/N) ≤ same bound | none | `T2001_QUE` |
| `(eq:universality)` Thm 2.4 | 1_2:454-457 | O∈C_c^∞(ℝⁿ), \|E\|≤2-κ, n fixed: lim_{N→∞}∫O(α)[p_H^{(n)} - p_GUE^{(n)}](E+α/N)dα = 0 | none | `T2001_BUniv` |
| `(eq:diffu1)` Thm 2.5 | 1_2:490-494 | κ,ε,τ>0,D, ∀a,b: ∩_z{\|W^{-2d}Σ_{x∈[a],y∈[b]}\|G_xy\|² - \|m\|²Θ^{(+,-)}_{ab}/W^d\| ≤ W^τ[(𝓑_{η,0})^{1/5}𝓑_{η,W\|a-b\|} ∧ (𝓑_{η,0})²]} w.p. ≥ 1-N^{-D}; Θ^{(+,-)}=(1-\|m\|²S^{(B)})^{-1} (1_2:472-474) | `Theta` (Propagator/Basic.lean:70), Θ only | `T2001_QDiff` |
| `(eq:diffu2)` | 1_2:495-499 | same with G_xyG_yx, m²Θ^{(+,+)}, Θ^{(+,+)}=(1-m²S^{(B)})^{-1} | `Theta` | `T2001_QDiff` |
| `(Meq:QdS1)`, `(Meq:QdS2)` | 1_2:504-509 | each z∈D, N large: max_{a,b}\|W^{-2d}Σ E\|G_xy\|² (resp. E G_xyG_yx) - profile/W^d\| ≤ W^τ(𝓑_{η,0})²((g²W^d)^{-1/5}+𝓑_{η,0}) | `Theta` | `T2001_QDiff` |
| `MR:decol_BA` bullet 1 | 1_2:651 | H=V+gΨ (1_2:610-616), (Main_DEL_COND), (eq:WO); `(eq:psikLinfty)` with 2-κ → e_g-κ | none | `T2001_BA_decol` |
| bullet 2 | 1_2:653 | `(G_bound)`,`(G_bound_ave)` with m of `(self_m)` (1_2:626-629), M of `(def_G0)` (1_2:631-633), D^{BA} (7_8:1817) | none | `T2001_BA_locSC` |
| bullet 3 | 1_2:655 | `(Meq:QUE)`,`(Meq:QUE2)` with e_g-κ; `(eq:universality)` | none | `T2001_BA_QUE`, `T2001_BA_BUniv` (T2001c) |
| bullet 4 | 1_2:657-666 | `(eq:diffu1)`-`(Meq:QdS2)` with (Θ^{(+,-)}M^{(+,-)})_{ab}, (Θ^{(+,+)}M^{(+,+)})_{ab}, S^{(B)}=I (1_2:658-663) | none | `T2001_BA_QDiff` |

Not vacuous at the preflight sequence (one sentence per pin; `witnessSeq` is `L_n=W_n=4(n+1)`, `g_n=1/W_n`):
- `T2001_decol`, `T2001_locSC`, `T2001_QDiff`: `admissible_witnessSeq` (compiled) gives `Admissible 3 (1/7) (2/5) witnessSeq`, κ,ε,τ,D are free positive reals, and the bound concerns a genuine event of an `N×N` Gaussian matrix, `N_n=(4(n+1))^6 ≥ 4096`.
- `T2001_QUE`: same, with ε₀=1/10, c=1/20, τ=1/50 inside `(0,𝔡/2)=(0,1/5)` and `(0,ε₀∧𝔡/5)`, and exponent `-(4/25)+2/20+1/50 = -1/25 < 0`, so the bound `W^{-1/25}` is below 1 (preflight (a): "QUE prob exponent ... 0.04 >0: True").
- `T2001_BUniv`: same `Admissible`; `E=0`, κ=1 give `|E|≤2-κ`, and bump functions `O∈C_c^∞` exist (k=1 gives a nonconstant statistic).
- the five BA pins: `BAData` needs `μ_n` with Stieltjes transform `m_n` solving `(self_m)` and `supp μ_n=[-e_n,e_n]`; at `witnessSeq` every `L_n` is even, so the torus is bipartite and the free convolution has a symmetric support (existence from [Biane], not proved in Lean: BA pins are non-vacuous modulo this literature fact). `BAData d s` is empty, and the five BA pins are vacuous, on the admissible sequences with some `L_n` odd (T2001d) and on those where `supp μ_n` is not an interval, e.g. `d=3`, `L_n=4`, `g_n=10`, `W_n→∞` (T2001l, `## Repair`): the BA pins are non-vacuous only where `supp μ_n` is a symmetric interval.

### Gap list (ticket item 3: every row of class ii-iv with a gate, grouped by gate; `python3 gaps.py` (coverage appendix) checks that these lines list exactly the 151 rows, each once; remarks/examples and class i omitted)

| gate | rows by class | what is missing |
|---|---|---|
| F0 | iv: `eq:defmzsc#integral`, `defi:ofB#BtBt` | integral form of `m`; `𝓑_{η_t,K} ≍ W^{-d}B_{t,K/W}` |
| F0 | iii: `representativeL`, `def_Theta` | l¹ block distance (D2); band-only Θ (BA matrix `M^{(σ1,σ2)}`) |
| MD | iii: `def_flow`, `Def:G_loop`, `def_Green`; iv: `MBM`, `zztE#law`, `def_G0t`, `eq:opS` | `H_t` absent: `Gsig`/`gloop` read the time-1 `Hmat`; the law identity of `zztE`; `M_t` |
| MD | iii: `bandcw0`, `eq:blockIa` | one `Gauss.P` per size: no sequence, no common space for `StochDom`, no fine-lattice geometry |
| MD | iii: `Def:oper_loop`; iv: `lem:SE_basic`, `eq:defMzsc` | loop hierarchy (grid walk, DECISIONS 7), single-edge cut, `M=mI` |
| PT | iv: `lem_propTH#5a`, `lem_propTH#5b`, `lem_propTH#6`, `lem_propTH#7`, `lem_propTH#8` | Props with (g,m)-dependent constants: need g- and E-uniform statements and d≥3 proofs |
| KL | iv: `eq_Ward0`, `eq_Ward`, `lem_WI_K`, `lem_wardineq_K` | Ward identities: no declaration on main |
| KL | iv: `ML:Kbound`, `tree-representation#n>=4`, `lem_pureloop#n>=4` | `KLoopBound`, `KTreeRep` are Props; general n |
| KL | iii: `Def_Ktza`, `f-external`, `def:canpnical_part`, `lem_pureloop#n<=3`; ii: `Kn2sol`, `Kn3sol`, `tree-representation#n<=3` | `TwoLoopBounded`; band-only M-loop; only the + charge; explicit solutions n≤3 |
| EK | iv: `lem:sum_decay` | cases 1-5 (W^{C_nε}); only kernel ingredients, conditional on `ThetaDecay` (fixed g) |
| EK | iii: `lem:sum_decay_nonzero`, `DefTHUST` | `hmi` excludes charge -, g-dependent constants, band only |
| ST | iv: `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`, `lem:main_ind`, `lRB1`, `Gtmwc`, `Gt_bound_flow`, `Gt_avgbound_flow`, `Eq:Gdecay_w`, `Eq:LGxb`, `Eq:L-KGt-flow`, `Eq:Gdecay_flow`, `Eq:Gdecay+s<g_flow`, `Eq:Gtlp_exp_flow` | the whole induction and its six step statements |
| ST | iv: `eq_L-Keee`, `DefKsimLK`, `def_ELKLK`, `Sol_CalL`, `def:CALE`, `lem:DIfREP`, `LK_simple`, `defCALJ`, `lem: EMn2_N`, `ygdhmsgq0`, `ygdhmsgq` | hierarchy, Duhamel with stopping time, grid path + Azuma/Doob (DECISIONS 7), martingale and contract inequalities |
| ST | iv: `lem_GbEXP`, `lem_ConArg`, `awi2iks`, `lem:newKLK`, `eq:opt_L2`, `eq:simpleboundK`, `eq:Gronwall_dervJuD`, `eq:def2_stopping`, `Gronwall_inequality` | Steps 1-2 for d≥3 (J-Gronwall with stopping time, `lem:newKLK`); Gronwall is in Mathlib |
| ST | iv: `def:XiL`, `def:XIL-K`, `lem:SEforLn`, `Def_decay`, `lem_decayLoop`, `lem:STOeq_NQ`, `Def:QtPt`, `lem_+Q`, `lem:STOeq_Qt`, `lem:iterations`, `lem: newPQ`, `lem:STOeq_Qt_nonzero` | Steps 3-4 for d≥3: sum-zero and zero-mode removal, new time intervals |
| ST | iv: `lem;CLT`, `lem_dec_calE`, `TailtoTail`, `lem:pf_step5`, `lem:improve_exp_aver` | Step 5 CLT cancellation (d≥3), Step 6 |
| LW | iv: `lem:LWterm`, `lem: EWGn2_N`, `lem:LWterm_EXP`, `lem:LW_moment`, `lem:LW_moment_exp`, `lem:LW_moment_exp_far`, `lem:LW_moment_exp_near` | the light-weight estimates |
| LW | iii: `def scaling`, `def scaling order`; iv: `def_graph1`, `ValG`, `def_poly`, `defnlvl0`, `dot-def`, `deflvl1`, `def: BM2`, `def_auxgraph`, `strat_local` | graph vocabulary; main has counters-only `ord` |
| LW | iv: `ssl`, `Oe14`, `T eq0`, `lvl1 lemma`, `lem:localregular`, `eq:Gbyxi2`, `GtoAG`, `lem:Anp`, `lem:Anp_key`, `lem:Anp_key_gh` | expansions and graph bounds; main has only `∂G_ij/∂h` and the Gaussian IBP |
| MA | iii: `[net]`; iv: `MR:decol`, `MR:locSC`, `MR:QUE`, `MR:QuDiff`, `eq:ukx`, `ssfa2`, `ssfa2_deter`, `eq:BetaK`, `eq:spectral_domain`, `eq:calBetaK` | endpoints and their derivations; the net lemma on main is one-parameter, not for z in `D_{κ,ε}` |
| UN | iv: `Thm: B_Univ`, `[Thm2.4-proof]` | Green-function comparison, LSY Thm 2.2 (authorized), QUE at ε₀=𝔡/3, c=𝔡/6 |
| BA | iv: `self_m`, `def_G0`, `MR:decol_BA`, `bandcwV`, `eq:H_blocka`, `eq:Psi3D`, `eq:spectral_domainBA`, `zztE_BA` | BA model, `m(z,g)`, `e_g`; T2001c, T2001d, T2001g |
| BA | iv: `lem:propM`, `lem_GbEXP_BA`, `lem_ConArg_BA`, `lem:main_ind_BA` | BA induction, Combes-Thomas |
| BA | iii: `def scalingBA`; iv: `m-loop-tsp`, `M-graph-value-definition`, `tree-representation_BA`, `def_atom`, `defn_normalBA`, `lanlw`, `lem_lweight`, `GGGamma` | BA M-loop trees and graph expansions |
| BA | band-only Lean rows (scope `band`, class i-iii, 20): `bandcw0`, `eq:variancematrix`, `def:Theta`, `def_flow`, `zztE#alg`, `Def:G_loop`, `Def_Ktza`, `def_Theta`, `lem_propTH#1`, `lem_propTH#2`, `lem_propTH#3`, `lem_propTH#4`, `Kn2sol`, `Kn3sol`, `DefTHUST`, `lem:sum_Ndecay`, `lem:sum_decay_nonzero`, `f-external`, `tree-representation#n<=3`, `lem_pureloop#n<=3` | BA versions or generalisations (matrix `M^{(σ,σ')}`) |
| flag | `[net]` (1_2:1228, 1400), `eq_Ward0`/`eq_Ward`, `lem_wardineq_K`, `def_G0t`/`eq:opS`, `eq:ukx` | consumed on the Step 2-4, `zztE` and `MR:decol` paths; named by no gate row of ROUTES.md (grep: no `Ward`, `ukx`, `net`, `opS`, `def_G0t`); 118 of the 166 rows with a gate are not literally named (ST 46, LW 20, BA 16, MA 10, F0 8, MD 6, EK 6, KL 5, UN 1), most lie in a gate's section range |

### Old-mode claims (ticket item 4; signatures only)

| statement (file:line) | old claim | class | constants / restriction (paper: 1_2:1143-1150) |
|---|---|---|---|
| `ThetaDecay` (Interface.lean:77) | D5, D13: Prop, constants may depend on g, m | Prop only | `∃ Cd cd` after `(d g m)`: depend on d,g,m, not L,t,a; paper: `C_d,c_d` depend on d (BA: also on g^{-1} for 1≤g≤𝔡^{-1}) |
| `ThetaDecayShort` (:101) | same | Prop only | `C_κ,c_κ` depend on g and on m (`0<m.im`); paper: d and κ, uniform in E with \|E\|≤2-κ |
| `ThetaDiffOne`, `ThetaDiffTwo`, `ThetaZeroMode` (:118, :133, :149) | Q41/Q53/Q54: "certificates" | Prop only | `∃ C` after `(d g m c τ)`, `L^τ` for `N^τ` (D5); paper: `≺`, N₀(τ) free of g |
| `PropTH` (:168), `propTH_fixedL` (Test/InterfaceShape.lean:552) | "certificate 6 of 9" (Q54) | Prop; certificate iii | certificate: fixed `L`, constant depends on `L`; does not make the Props true for all L |
| (eq:WO) allows `g_n ≥ W_n^{-d/2+𝔡} → 0` | — | — | a constant depending on g gives no bound along the sequence: the five Props cannot serve any endpoint as stated |
| `Gsig`, `gloop` (Loop/GLoop.lean:87,92), `norm_gloop_le` | Q49/Q50: G-loops and envelope (5.2) | iii | resolvent of the time-1 `Hmat` at `z_t`, not `L_t` (needs `H_t`, variance `tS`) |
| `StochDom` (Defs/StochDom.lean:80) | convention "fixed (Ω,P)" | i | `Gauss.P d L W g` is one law per size: no `Ω` carries a size sequence |
| `kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop` | Q22a/Q22b: "hypothesis became theorem" | ii | needs `TwoLoopBounded`; `(eq_Ktree)` n≥4 is the Prop `KTreeRep` |
| `norm_zeroModeSet_UN_le`, `pureLoop_two/three` | Q13, Q25-26: proved | iii | `hmi: 0<Im m` excludes charge - (m(-)=m̄), ThetaDecayShort/ThetaZeroMode at fixed g |
| `lem_propTH` 1-4, `propT`, `norm_UN_le`, `key_T_reduce_absorbed` | Q5, Q9, Q11, Q20/29: theorems | i | band model; explicit constants; `claim:TTk` with ℓ≥1 (D15) |
| scan of merged signatures (`propscan.py`, coverage Checks) | borrowed/owed Props are "in use" | — | carried by theorems: `ThetaDecayShort` 7, `ThetaDecay` 3, `ThetaZeroMode` 2, `TwoLoopBounded` 4; by none: `PropTH`, `KTreeRep`, `KLoopBound`, `ThetaDiffOne`, `ThetaDiffTwo` |
| `#assert_rbm_axioms` "0 axioms" | STATUS Q19 | true, but | borrowed statements are Props: the count does not say which endpoint rests on them |

### Proposed first tickets (ticket item 6; a proposal, the dispatcher writes tickets)

| title | file | start condition | role |
|---|---|---|---|
| F0-T1 integral form `msc = ∫ρ/(x-z)` (port RBM2D Defs/SemicircleIntegral) | `RBM3D/Defs/SemicircleIntegral.lean` | now | prover |
| MD-T3 model on a size sequence: `H_t`/grid path, common space, link to `StochDom` | per T2002 | after T2002 | prover-hard |
| MD-T2 resolvent and loop Ward identities (port RBM2D Hierarchy/WardResolvent, Loop/Ward) | `RBM3D/Loop/Ward.lean` | after T2002 | prover |
| PT-T2 g- and E-uniform Props 5-8 and their d≥3 proofs (internal by DECISIONS 5) | `RBM3D/Propagator/Decay.lean` | after T2003 | prover-max |
| KL-T2 K-loop tree representation all n, `KLoopBound` (internal) | `RBM3D/Loop/TreeRepGeneral.lean` | after T2004 | prover-max |
| EK-T2 `lem:sum_decay` cases (port RBM2D Evolution/Case*, d≥3 with `propT`) | `RBM3D/Kernel/SumDecayCases.lean` | after PT-T2 | prover-hard |
| ST-D1 Steps 2-4 for d≥3 (J-Gronwall, stopping time, contract inequalities) design | docs | after MD-T3 | design |
| MA-T1 `decol` from `locSC`, `QUE` from `QDiff` (port RBM2D Main/DecolFromLocal, QUEFromQDiff) | `RBM3D/Main/*.lean` | after pin freeze | prover |
| MA-T2 net lemma for z in `D_{κ,ε}` (port RBM2D Main/RegionUnif) | `RBM3D/Main/RegionUnif.lean` | after MD-T3 | prover |
| LW-D1 graph vocabulary and expansions design | docs | after T2002 | prover-max |
| UN-D1 universality with LSY (complex Hermitian, unit density) and the BA statement | docs | after Jun decides T2001c | design |
| BA-D1 `m(z,g)`, `e_g`, `M`, Θ^{BA} (port RBM2D Universality/FreeConv, Combes-Thomas) | `RBM3D/BA/*.lean` | after T2002, T2003 | prover-hard |
| SV-2 freeze `RBM3D/Endpoints.lean` from the probe | `RBM3D/Endpoints.lean` | after T2002 and T2001b-d | prover |

### Narrative

- Main covers only a deterministic base: of 172 rows, 17 are class i (model vocabulary, `lem_propTH` 1-4, `lem:propT`, `lem:sum_Ndecay`, `claim:TTk`, the algebra of `zztE`), 3 class ii, 18 class iii, 134 class iv.
- None of the six endpoints, none of Steps 1-6, none of the light-weight layer (28 rows, 2 of them as counters only), none of the block Anderson layer (21 rows) is on main; the five `Theta*` Props are Props, not theorems.
- The Props' constants depend on `(g,m)` while `(eq:WO)` lets `g_n → 0`: as stated they supply no bound along a size sequence (item 4); the "certificates" are fixed-`L`.
- `Gsig`/`gloop` are loops of the time-1 matrix, not of `H_t`; `StochDom` needs one probability space while `Gauss.P` is per size: T2002 must supply `H_t` or the grid path and a common space before any loop statement is stated.
- `norm_zeroModeSet_UN_le` and `pureLoop_*` exclude the charge `-` (hypothesis `0<Im m`), and `Kn2sol`, `Kn3sol`, `tree-representation` (n≤3) need `TwoLoopBounded`.
- No Ward identity (`eq_Ward0`, `eq_Ward`, `lem_WI_K`), no `eq:ukx`, no 2-dimensional net lemma, no single-edge cut (`Def:oper_loop`) on main; ROUTES.md names `lem_WI_K` but none of the others (grep).
- Paper-side findings: BA bulk universality as written fails when `ρ_N(E) ≠ ρ_sc(E)` (T2001c, Appendix B of the coverage file: ratio 0.4106 at g=1, E=0); BA support `[-e_g,e_g]` is symmetric only for even L (T2001d); `zztE_BA` uses 2-κ (T2001g).
- RBM2D's frozen pins are pointwise in z; the paper's events contain the union over z: the probe pins the paper form and proves nothing (T2001b).
- Pins: twelve closed `Prop`s (eleven pins and the literal BA universality) compile (`lake build RBM3D.Probe.T2001Endpoints`); the only theorem is the satisfiability of `Admissible`.

## (c) Verified Mathlib names

`#check` in the worktree (probe imports `RBM3D`); file:line by grep.
- `Nat.le_self_pow : n ≠ 0 → ∀ a, a ≤ a ^ n`; `Filter.tendsto_atTop_mono` (Order/Filter/AtTopBot/Tendsto.lean:72); `div_le_iff₀` (Algebra/Order/GroupWithZero/Basic.lean:1133)
- `Real.rpow_le_rpow_of_exponent_le` (Analysis/SpecialFunctions/Pow/Real.lean:617); `Real.rpow_natCast` (:62); `Real.rpow_mul` (:415); `Real.rpow_one` (:149); `Real.rpow_neg_one`
- `Matrix.IsHermitian.eigenvalues` (Analysis/Matrix/Spectrum.lean:67); `Matrix.trace`; `dotProduct`; `Ring.inverse`; `Nat.descFactorial` (Data/Nat/Factorial/Basic.lean:332)
- `MeasureTheory.Measure.support` (MeasureTheory/Measure/Support.lean:59, used as `(μ n).support`); `MeasureTheory.Measure.pi`; `ProbabilityTheory.gaussianReal` (Probability/Distributions/Gaussian/Real.lean:222)
- `ContDiff`, `HasCompactSupport`, `intervalIntegral`
- absent (grep -rln 'GUE\|GaussianUnitaryEnsemble\|StieltjesTransform\|semicircle' Mathlib): no GUE, no Stieltjes transform of a measure, no semicircle law (one unrelated hit, Geometry/Euclidean/Angle/Sphere.lean)

## (d) Open issues and paper-delta candidates

| tag | kind | statement |
|---|---|---|
| T2001a | equivalent, necessary | "∃N₀" as a statement along a size sequence; `size n → ∞` listed in `Admissible`; `3 ≤ L` explicit (D1) (as RBM2D T2001a,b) |
| T2001b | stronger than RBM2D's pin | `∩_z` inside the probability for `(G_bound)`,`(G_bound_ave)`,`(eq:diffu1)`,`(eq:diffu2)` (1_2:388-399, 490-499); RBM2D Endpoints.lean:99-113, 173-184 are pointwise in z: dispatcher decides; the net argument (1_2:1228) is a proof obligation |
| T2001c | substantive (Jun) | BA `(eq:universality)` (1_2:655) compares with `p_GUE` at the same E: false if `ρ_N(E) ≠ ρ_sc(E)` (n=1: by `(G_bound_ave)` p_H^{(1)}(E)→ρ_N(E)); the commented-out earlier condition `g ≤ W^{-𝔡}` (1_2:364-365, 646-648) made it true as `g→0`, the final `(eq:WO)` allows `g ≤ 𝔡^{-1}`; probe: `T2001_BA_BUniv` matches `ρ_sc(E'_n)=ρ_N(E)`, `T2001_BA_BUniv_literal` is the paper text |
| T2001d | necessary | BA `supp μ_N=[-e_g,e_g]` (1_2:624) holds for even L only (bipartite torus); odd L has two edges; `BAData` takes a symmetric `e` |
| T2001e | equivalent | `\|x-y\|` (fine lattice, L^∞) in `𝓑_{η,\|x-y\|}` read as `W·\|[x]-[y]\|` (block l¹, D2); constants absorbed by `W^τ` |
| T2001f | necessary | `(Meq:QUE2)` needs `A≠∅` (for A=∅ the event is `0 ≥ 0`) |
| T2001g | typo | `zztE_BA` (7_8:1797) says `\|Re z\|≤2-κ`; `D^{BA}` (7_8:1817) uses `e_g-κ` |
| T2001h | reading (RBM2D T2001d,g,h) | `m` by the integral `mSC`; eigenvalue-sum form of `p^{(k)}`; any orthonormal eigenbasis |
| T2001i | finding | Interface Props (Interface.lean:77-168) have (g,m)-dependent constants (D13), weaker than 1_2:1143-1150 and unusable for `g_n → 0`: replace by g- and E-uniform statements (T2003) |
| T2001j | finding | `Gsig`/`gloop` are time-1 (GLoop.lean:87-95); `StochDom` fixed `(Ω,P)` vs per-size `Gauss.P` (T2002) |
| T2001k | finding | `norm_zeroModeSet_UN_le`, `pureLoop_*` exclude charge - (`0<Im m`) |
| T2001l | necessary | 1_2:624 `supp μ_N=[-e_g,e_g]` fails also when `supp μ_N` is not an interval, which `(Main_DEL_COND)`, `(eq:WO)` allow with `L` fixed and `g` large: `d=3`, `L=4`, `g=10` gives `ρ_N≈0` on `(0,20)` (script in `## Repair`); there `e_g` is undefined, `BAData d s` is empty and every `T2001_BA_*` pin is vacuous |

Proposal for the freeze ticket (dispatcher decides; T2001l): a non-vacuous BA pin form either (1) drops `BAData.supp`, takes `μ_N` from `(self_m)` alone, and replaces the bulk condition `|E| ≤ e_g-κ` by "`dist(E, ℝ∖supp μ_N) ≥ κ`" (and `D^{BA}` accordingly), or (2) keeps the paper's `e_g` and adds to the BA admissibility the restriction `L_n → ∞` with `L_n` even, or `g_n ≤ 1`, under which the support is the interval of 1_2:624 (to be checked, not done here).

Open: the existence of `BAData` (free convolution, [Biane]) and the LSY limit computation (preflight (a), "External hypothesis" paragraph) are not done here; the T2001b-d decisions block `RBM3D/Endpoints.lean`.

## Repair — Fri Oct  2 19:02:00 UTC 2026

Report-only repair of audit round 1 (`docs/reports/T2001-audit.md`, "Required for resubmission" 1-3); no `.lean` file changed. Items: (1) candidate T2001l in (d); (2) the BA "Not vacuous" bullet in (b); (3) the freeze-ticket proposal under the (d) table. Support split (self_m at 1_2:626-629, `z=E+iη`; in the gap `ρ_N` scales with `η`, in the bulk it does not), and admissibility of the sequence `L_n=4`, `g_n=10`, `W_n=10^n`, `𝔠=1/20`, `𝔡=1/10`:
```
$ python3 ba_support.py
d=3 L=4 g=10 eigenvalues of Psi^(B) (value:weight): {-6.0: 0.0156, -4.0: 0.0938, -2.0: 0.2344, 0.0: 0.3125, 2.0: 0.2344, 4.0: 0.0938, 6.0: 0.0156}
eta=0.001 rho_N(E) for E=0,5,10,15,20: ['1.78e-01', '4.63e-06', '1.88e-06', '3.61e-06', '1.54e-01']
eta=1e-06 rho_N(E) for E=0,5,10,15,20: ['1.78e-01', '4.63e-09', '1.88e-09', '3.61e-09', '1.54e-01']
$ python3 ba_adm.py
2 N=6.4e+07 N^c<=W: True W^{-d/2+dd}<=g<=1/dd: True
4 N=6.4e+13 N^c<=W: True W^{-d/2+dd}<=g<=1/dd: True
8 N=6.4e+25 N^c<=W: True W^{-d/2+dd}<=g<=1/dd: True
```

Script `ba_support.py`:
```python
# free convolution of semicircle with empirical measure of g*Psi^(B) on Z_L^d (self_m, 1_2:626-629)
import itertools, math, cmath
from collections import Counter
def eigs(d, L):
    c = Counter()
    for k in itertools.product(range(L), repeat=d):
        c[round(sum(2*math.cos(2*math.pi*ki/L) for ki in k), 9)] += 1
    return {lam: n / L**d for lam, n in c.items()}
def m_of(z, ev, g, it=200000):
    m = 1j
    for _ in range(it):
        new = sum(w / (g*lam - z - m) for lam, w in ev.items())
        if abs(new - m) < 1e-15: return new
        m = 0.5*m + 0.5*new
    return m
d, L, g = 3, 4, 10.0
ev = eigs(d, L)
print("d=%d L=%d g=%g eigenvalues of Psi^(B) (value:weight):" % (d, L, g), {k: round(v, 4) for k, v in sorted(ev.items())})
for eta in (1e-3, 1e-6):
    rho = [m_of(E + 1j*eta, ev, g).imag / math.pi for E in (0, 5, 10, 15, 20)]
    print("eta=%g rho_N(E) for E=0,5,10,15,20:" % eta, ["%.2e" % r for r in rho])
```
