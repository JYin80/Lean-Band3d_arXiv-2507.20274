Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 23:10:12 UTC 2026

Setting: `d ≥ 3`, `p ∈ 2ℕ`, regime `ĝ²/L² < 1-t`, `ℓ_t = min(max(ĝ/√(1-t),1),L) ≥ 1`, window `(log W)^{3/2}ℓ_t ≤ ℓ ≤ (log W)^{10}ℓ_t`, `N=(WL)^d`, `K ≥ |E'|+|I'|` (card bound of `lwMoment_prec_anp`, `LWMoment.lean:1034-1038`), `Rb = K(log W)^{3/2}`, `ρ = 2Rb+1`, `𝖳 = sfT = (W^d)^{-1/2}(ĝ²+|1-t|)^{-1/2}(r+1)^{-(d-2)/2}e^{-½√(r/ℓ_t)}` (`PropT.lean:469`). `S=…/scratchpad/T2348` (scripts `cost.py`, `ttk.py`, `inst.py`). No Lean written; the probe is not produced at this stage.
Targets (mathematics): **P** weighted identity `E[Π_k f^{w_k}] = Σ_r E[Σ_{ℓ_i}Π_k w_k(ℓ(π_r β^{(k)})) term_r]`; **Dom** far/near pins on domains enlarged by `Rb`; **G4** `f = f^{>}+f^{(a)}+f^{(b)}`; **G2** exp-class `ξ ≺ 𝖳(|·|∧ℓ)` at radius `Rb`; **Met** `claim:TTk` in `ℓ^∞`; **A/Asm**.

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | molecule radius `R' = (log W)^{3/2}`, `Rb = K R'` | tail `e^{-cR'/2}N^{a} ≤ N^{-b}` (copy of `lwMoment_tail`, `LWMoment.lean:471-476`, `(log W)²↦(log W)^{3/2}`) | `Lg·A/𝔠 ≤ c Lg^{3/2}/2` ⇔ `Lg ≥ M²`, `M = 2A/(𝔠c)`, `A=|a|+|b|` | original needs `Lg ≥ M`; asymptotic in both |
| 2 | **Dom cost** `𝖳(max(r-Rb,0))/𝖳(r)` | `≤ (Rb+1)^{(d-2)/2}e^{½√(Rb/ℓ_t)}` (script (2)) | the ticket's `≤ e^{½√(Rb/ℓ_t)}` is **false for sfT, d ≥ 3** (poly factor `((r+1)/(r-Rb+1))^{(d-2)/2}`; at `r=Rb`, `d=3`: log ratio 21.01 vs 17.45) | corrected form `e^{o(log N)}`: `√K(log W)^{3/4}/2 + O(log log W)`, power `p` |
| 3 | `√r-√(r-ρ) ≤ √ρ` (`0≤ρ≤r`) | script (1): max ratio 0.9981 | exact (`√r ≤ √(r-ρ)+√ρ`) | 0.2% at sampling; tight at `r=ρ` |
| 4 | **G2** comparability `Φ(m) ≤ Kn Φ(ℓ')`, `ℓ' ≤ m+2ρ`, `Φ=(W^{-d}max(tailT(·∧ℓ),W^{-D}))^{1/2}` | `Kn = (2ρ+1)^{(d-2)/2}e^{½√(2ρ/ℓ_t)}` (script (3): max 0.856 of the bound for `tailT`) | replaces `LWPsiAll` (`Φ(ℓ₁) ≤ C₁(ℓ₂/ℓ₁)^{C₂}Φ(ℓ₂)`, false for `e^{-½√·}`); needs `Kn ≤ X^{τ/8}` (`AuxGraph2.lean:1019-1021`) | exponent `~√K(log W)^{3/4}` vs `τ log N`, ratio `→0` |
| 5 | G2 radius | `Rb=K(log W)^{3/2}` closes; Lean's `K(log W)²` (`LWMoment.lean:1048`) does not | for `(log W)²` loss exponent / `log N → K√K/3.6 = 4.08` (K edges, sz0, K=6) `> τ` (T2344: `0.68`, one edge); `(log W)^{3/2}`: first crossing `log W ≈ 4.45e7` (K=6 edges, τ=0.05), `∝ τ^{-4}` (script (4)) | closure is `∀τ ∀ᶠ n`, as every merged `≺`; no finite witness of the **conclusion** is claimed |
| 6 | Dom exp-part, `p=2`, `K=6`, τ=0.05 | first crossing `log W = 3.43e4` (`log₁₀n = 2.98e3`) | `p·½√(K)(log W)^{3/4} ≤ τ log N` | asymptotic |
| 7 | (A) split `R_A=(log W)^{3/2}ℓ_t` | loss `e^{p·½(log W)^{3/4}}` | `≤ N^τ` | first at `log W = 951` (`p=2`, τ=0.05; T2344 row 1 had `p=1`: 57.2) |
| 8 | **Met** twin, `D ⊆ ball_∞(c,λℓ)`, cap `ℓ` | `λ = (ℓ+Rb)/ℓ ≤ 1+K/ℓ_t ≤ 1+K` | LHS/RHS `≤ C(λ)`, `C ≤ λ^d C₁` (volume) | numerics `6.4, 30.4, 197` at `λ=1,2,4` (script ttk): `λ^{2..3}` growth |
| 9 | Near radius vs cap | merged `lwMomExp_nearD`/`lwMomExp_tau` share one `ℓ` (`LWMomExp.lean:532,521`; used `640-669`) | enlarged radius `λℓ` with cap `ℓ` needs a `λ` parameter in the twin | not a one-line restatement |
| 10 | Far radius | `lwMomExpFar_farDAnd … (ℓ : ℝ)` (`LWMomExpFar.lean:42`) | take `ℓ := max(ℓ-Rb,0)`; every path's first edge `>ℓ-Rb`, `𝖳(|·|∧ℓ) ≤ 𝖳(ℓ-Rb)` | row 2 clamp covers `ℓ<Rb` |
| 11 | G4 | `f=f^{>}+f^{(a)}+f^{(b)}` exact (`|a_1-a|>ℓ∧|a_1-b|>ℓ` / `≤ℓ` from `a` / `>ℓ` from `a`, `≤ℓ` from `b`); `E|Σ|^p ≤ 3^{p-1}Σ` | `3^{p-1}` constant; `f^{(b)}` ⊆ `ball(b,ℓ)`, symmetric in `a↔b` | script: `p=2,4,6` sampled OK |
| 12 | pins `n_M ≤ p`, `2p ≤ ord`, `Λ^{2q}=(log W)^{20q}≤N^τ`, `η_t ≍ 1-t`, `c₀=d` | unchanged from T2344 rows 2-8 | as T2344 | as T2344 |

### (ii) One concrete nondegenerate instance
Data: `d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `ĝ=(2(n+1))^{-6}`), `n=2000`, `t=1/16`, `p=2`, `K=6`, `ℓ=2000`, `a=0`, `b=(3000,0,0)` (`|a-b|_∞=3000`). Command: `cd $S && python3 inst.py`
```
n=2000 L=8004 W=1.027e+18 g=2.43e-22 logW=41.473 logN=151.38  1-t=0.9375  strict g^2/L^2<1-t: True  l_t=1
window: (logW)^1.5 l_t=267.1 <= ell=2000 <= (logW)^10 l_t=1.51e+16 : True
Rb=K(logW)^1.5=1602.5  rho=2Rb+1=3206.0  ell-Rb=397.5>0: True ; ell+Rb=3602.5 < L/2=4002 (no wrap): True ; r=|a-b|_inf=3000 in (ell, L/2]: True
exact counts: |f^(a) domain|=64048012001  |f^(b) domain|=48024003000  |f^> domain|=400696369063  sum=512768384064  L^3=512768384064  all>0: True
enlarged: ball(a,3602) has 374026140125 pts (<= L^3=512768384064); far' (both > 397) has 511763464314 pts
radius ratio lam=(ell+Rb)/ell=1.801 <= 1+K/l_t=7 : True
dom cost exponent p*[1/2 sqrt(Rb/lt)+(d-2)/2 log(Rb+1)]=47.41 ; G2 shift K*1/2 sqrt(2rho/lt)=240.22 ; tau*logN=7.57  (instance does not close the loss: asymptotic)
Bctl=W^-3 B_0=9.860e-55 (->0, <= N^-c_B); tailT(ell=2000)=2.016e-23 vs W^-1=9.741e-19 ; Psi^2=W^-3 B_0 ; sfT(ell)/sfT(ell-Rb) exp-part e^{-12.39}
Bctl limit: n=1e2,1e4,1e8,1e16 -> ['2.80e-35', '3.25e-65', '3.26e-125', '3.26e-245']
Asm: |x+y+z|^p <= 3^(p-1) sum |.|^p for p=2,4,6, 6e4 samples: True
provenance, partition constructor (3 vertices, 4 labels, weight on vertex 0): lhs=22572 rhs=22572 equal=True
```
All deterministic hypotheses (regime, window, `ℓ±Rb` inside the torus, the three domains nonempty and partitioning `Z_L^3`, `λ ≤ 1+K`) hold at this one point. The loss rows 2, 4, 6, 7 are limits (`≺`: `∀τ ∀ᶠ n`), not statements about `n=2000`; the printed line shows the loss exceeds `N^{0.05}` there, exactly as for the merged pins.
External hypotheses (the target's own premises `LWInit`, `LWLoopExp`, as T2342 row 7): concrete limit computation = the `Bctl` line above (`Bctl = W^{-d}B_{t,0}`, `→ 0`, the prefactor `Bctl^{1/2}` of the target) and `tailT(ℓ)=2.0e-23 < W^{-1}`, so `tailW_1 = W^{-1}` there (floor active).

Command: `cd $S && python3 cost.py`
```
(1) max (sqrt r - sqrt(r-rho))/sqrt(rho) over 2e5 samples = 0.998111 (<=1)
(2) log[sfT(max(r-Rb,0))/sfT(r)] vs 1/2 sqrt(Rb/lt) (ticket) and (d-2)/2 log(Rb+1)+1/2 sqrt(Rb/lt) (corrected)
   216 tuples (d,lt,Rb,r): ticket bound violated 99 times, corrected bound violated 0 times
   example d=3 lt=1 Rb=1218.6 r=Rb: log ratio=21.0074, 1/2 sqrt(Rb/lt)=17.4542, diff=3.5531 = (d-2)/2 log(Rb+1)=3.5531
(3) max over 1e5 random draws of [tailT(m^lc)/tailT(l'^lc)] / [(2rho+1)^(d-2) e^sqrt(2rho/lt)] = 0.8563 (<=1 expected; Phi = sqrt)
(4) first log W with loss exponent <= tau*log N (tau=0.05, sz0 sizes, l_t=1, K=6, p=2); n = W^(1/5)/2 - 1, log10 n = logW/(5 ln10) - 0.3:
   dom exp-part  p*1/2*sqrt(Rb), Rb=K lW^(3/2)   : logW=3.43e+04  log10(n)=2.98e+03
   G2 shift  K*1/2*sqrt(4Rb+2), Rb=K lW^(3/2)    : logW=4.45e+07  log10(n)=3.86e+06
   G2 shift, Lean Rb=K lW^2                      : never (loss exponent/log N -> 2.45*K/3.6 > tau)
   (A) split p*1/2*lW^(3/4)                      : logW=951  log10(n)=82.3
   tau-dependence, G2 with Rb=K lW^(3/2): need lW^(1/4) >= K*sqrt(K)/(tau*3.6) approx; tau=0.5: lW>=4.44e+03, tau=0.05: lW>=4.44e+07, tau=0.005: lW>=4.44e+11
```
Command: `cd $S && python3 ttk.py` (single-centre `ℓ^∞` domain, cap `ℓ`, `d=3`, `L=30`, `W=2`, RHS with `(ℓ/ℓ_t)²`)
```
claim:TTk in l^inf, single-centre domain ball_inf(c, lam*ell), cap ell; d=3 L=30 W=2; RHS carries (ell/l_t)^2; max LHS/RHS over 12 params x 40 configs
  lam=1: 6.393
  lam=2: 30.448
  lam=4: 197.116
```

### Verdicts
- **P** (provenance): **PASS** as mathematics. The identities behind the steps are summand identities at fixed labels of the surviving vertices: the dotted-edge partition is a partition of unity on labellings (toy check above, exact), Gaussian IBP at a fixed entry `h_{xw}`, the resolvent identity at fixed `x`; IBP only attaches a new vertex by a waved edge `S_{xw}` to an old one, so every molecule keeps an initial `β^{(k)}`. The weights are real, so the twists `(c,t)` do not change them. Not decided here (Lean side, stage 1b): that every `lwSymm*` term of `LWExpTerm*` keeps old labels; a constructor that does not is the 1500–2500 twin of the ticket.
- **Dom/Far**: **PASS** with a correction to the ticket: the cost is `(Rb+1)^{(d-2)/2}e^{½√(Rb/ℓ_t)}` (row 2), not `e^{½√(Rb/ℓ_t)}`; `farDAnd` accepts the radius (row 10).
- **Dom/Near**: **PASS** with a `λ`-twin (rows 8-9): domain radius `λℓ`, cap `ℓ`, `λ ≤ 1+K`.
- **G4**: **PASS** (row 11).
- **G2**: **PASS** at radius `K(log W)^{3/2}` with the comparability of row 4 (asymptotic closure, rows 5-6); at Lean's `K(log W)²` it **FAILS** for every `τ < 0.68` (row 5, script (4) `never`).
- **Met** (`zdistInf` twin): **PASS** (row 8; constant `O(λ^d)`).
- **A / Asm**: **PASS** (rows 7, 11, 12; the route of T2344 (a)).
- Paper-delta candidates carried: `T2344a` (weight on `β^{(k)}` carried by the expansion), `T2344b` (G4 split), `T2344c` (G2 radius `(log W)^{3/2}`, shift comparability instead of `LWPsiAll`), `T2344d` (`ℓ^∞`); new `T2348a`: the ticket's cost bound for `sT(ℓ-Rb)/sT(ℓ)` needs the factor `(Rb+1)^{(d-2)/2}`.

## (a′) Preflight corrections — Fri Oct  9 00:40:33 UTC 2026
No statement of (a) is false and no verdict of (a) changes (design section 0: P, Dom, G4, G2, Met, A all PASS). Refinements, each decided by the compiled or scripted evidence in (b):
1. Row 7 and the verdict on A: regime (A) is split at `K (log W)^{3/2} ℓ_t` with a free `K` ≥ the card bound of the engine lists (`regA`, design section 7), not at `K = 1`; the (A) loss exponent is `(p/2)√K (log W)^{3/4}`, first crossing `log W = 3.43·10⁴` at `p = 2`, `K = 6`, `τ = 0.05` (the number of row 6; row 7's `951` is the `K = 1` value). Still `∀τ ∀ᶠ n`.
2. Targets line, rows 8-10 (`λ`-twin, enlarged domains): not needed under route (R) (rooted `GtoAG`, exact domains, design section 3): the near pin is `AnpNearInfAt` at `λ = 1`, constant `d^{k+2} ballC_k` (compiled, `sum_ball_inf_min_pow_le`); the `λ`-twin and the cap conversion of row 10 belong to route (E), the fallback.
3. Rows 2, 4: the corrected cap-shift factor `(ρ+1)^{(d-2)/2} e^{½√(ρ/ℓ_t)}` is now the compiled lemma `sfT_shift_le`; with `ρ ↦ 2ρ` it is the comparability of row 4.
4. Verdict P ("not decided here: that every `lwSymm*` term keeps old labels"): decided, every `LocStepX` constructor is pointwise in the old labels (design section 2, table).

### (b) Script output

**B1 build** (run Fri Oct  9 00:39:18 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2348`, branch `t/T2348`)
```
$ git log --oneline -1; git status --short | wc -l; wc -l RBM3D/Probe/T2348Pins.lean; grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2348Pins.lean
9f3bd75 T2348: probe 598 lines (WExp.prod instance takes the expansion pin as hypothesis, data discharged); builds
0
     598 RBM3D/Probe/T2348Pins.lean
0
$ lake build RBM3D.Probe.T2348Pins > build.txt 2>&1; echo "exit $?"; grep T2348Pins build.txt | grep -v "depends on axioms"; tail -1 build.txt
exit 0
ℹ [3898/3898] Replayed RBM3D.Probe.T2348Pins
Build completed successfully (3898 jobs).
$ lake env lean RBM3D/Probe/T2348Pins.lean > out.txt 2>&1; echo "exit $?"; grep -vc "depends on axioms" out.txt; grep -c "depends on axioms" out.txt
exit 0
0
12
$ git diff --stat main...t/T2348
 RBM3D/Probe/T2348Pins.lean | 598 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 598 insertions(+)
```

**B2 axioms of the proved declarations** (run Fri Oct  9 00:39:25 UTC 2026; the 12 `#print axioms` lines of `lake env lean`, B1)
```
$ sed -E "s/.*depends on axioms: //" out.txt | sort | uniq -c
  12 [propext, Classical.choice, Quot.sound]
$ sed -E "s/^'RBM.Probe.T2348.([^']*)'.*/\1/" out.txt | paste -sd' ' -
WExp.comp WExp.prod ProvOut.Molecular.comp CoverBy.comp lwEngineProv_imp_localregularX gtoAGRooted_imp LWf_split norm_add3_pow_le sum_ball_inf_min_pow_le sfT_shift_le lwTail32 ProvOut.molecular_id
$ lake env lean axprobe.lean   # Lean.collectAxioms of every constant of RBM.Probe.T2348 in the imported probe (14-line script, scratch directory)
119 constants of RBM.Probe.T2348 (58 theorems); with an axiom outside propext/Classical.choice/Quot.sound: 0 []
```

**B3 statements extracted from the probe** (run Fri Oct  9 00:39:38 UTC 2026; `python3 -I extract2.py RBM3D/Probe/T2348Pins.lean <names>`; the long statements `LWEngineProv`, `LWGtoAGRooted`, `LWAuxNestedOwnOn`, `LWMomentExpOn`, `regA`, `LWXiE` are in `T2348-design.md` section 10, B4)
```
 157| def LocStepXProv : Prop :=
 158|   ∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))), LocStepX P LX →
 159|     ∃ π : ∀ r ∈ LX, P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I', ∀ (m : ℂ) (t0 : ℕ × ℕ),
 160|       (∀ r (hr : r ∈ LX), (mkProv m t0 P r (π r hr)).ExtOK ∧ (mkProv m t0 P r (π r hr)).Molecular) ∧
 161|       WExp m (lwEvX m (t0, P)) (stepOuts m t0 P LX π)
  77| def WExp (m : ℂ) (P : PGraph (Fin 2)) (outs : List (ProvOut P)) : Prop :=
  78|   ∀ {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
  79|     (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), LWExpData sz n z u m Sp M →
  80|     ∀ (W : (P.E' ⊕ P.I' → Idx d (sz.L n) (sz.W n)) → ℝ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)),
  81|       ∫ ω, pvalW P (lwSampleData sz n z u M (lwS sz n u) Sp ω) W ℓe ∂(Sizes.seqP sz) =
  82|         (outs.map fun o => ∫ ω, pvalW o.Q (lwSampleData sz n z u M (lwS sz n u) Sp ω)
  83|           (fun ℓ => W (ℓ ∘ o.π)) ℓe ∂(Sizes.seqP sz)).sum
 111| theorem WExp.prod {m : ℂ} {p : ℕ} {outs : List (ProvOut (fxyPowGraph p).pack)} (h : WExp m (fxyPowGraph p).pack outs)
 112|     {d : ℕ} {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ} (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
 113|     (hD : LWExpData sz n z u m Sp M) (w : Fin p → Idx d (sz.L n) (sz.W n) → ℝ) (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) :
 114|     ∫ ω, pvalW (fxyPowGraph p).pack (lwSampleData sz n z u M (lwS sz n u) Sp ω)
 115|         (fun ℓ => ∏ k, w k (ℓ (Sum.inr (localReg_fxyBeta k)))) ℓe ∂(Sizes.seqP sz) =
 116|       (outs.map fun o => ∫ ω, pvalW o.Q (lwSampleData sz n z u M (lwS sz n u) Sp ω)
 117|         (fun ℓ => ∏ k, w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓe ∂(Sizes.seqP sz)).sum := h Sp M hD _ ℓe
 248| def domFar (a b : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
 249|   Finset.univ.filter fun c => ℓ < ((zdistInf d L (a - c) : ℕ) : ℝ) ∧ ℓ < ((zdistInf d L (b - c) : ℕ) : ℝ)
 252| def domNearA (a : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
 253|   Finset.univ.filter fun c => ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ ℓ
 256| def domNearB (a b : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
 257|   Finset.univ.filter fun c => ℓ < ((zdistInf d L (a - c) : ℕ) : ℝ) ∧ ((zdistInf d L (b - c) : ℕ) : ℝ) ≤ ℓ
 313| theorem LWf_split {d : ℕ} (sz : Sizes d) (n : ℕ) (E t ℓ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
 314|     LWf sz n E t ω x y =
 315|       LWfD sz n E t ω (domFar d (sz.L n) (STblk sz n x) (STblk sz n y) ℓ) x y +
 316|       LWfD sz n E t ω (domNearA d (sz.L n) (STblk sz n x) ℓ) x y +
 317|       LWfD sz n E t ω (domNearB d (sz.L n) (STblk sz n x) (STblk sz n y) ℓ) x y := by
 346| def AnpNearInfAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
 347|   ∃ C : ℝ, 0 < C ∧
 348|     ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
 349|       ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
 350|         (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
 351|         ∀ (c a b : Zd d L) (D : Finset (Zd d L)), (∀ α ∈ D, ((zdistInf d L (c - α) : ℕ) : ℝ) ≤ ℓ) →
 352|           lwMomExp_valOnD Γ ξ (fun _ => a) (fun _ => b) D ≤
 353|             C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
 354|               sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p
 335| def EKTTkInf (d n : ℕ) : Prop :=
 336|   3 ≤ d → 2 ≤ n → ∃ C : ℝ, 0 < C ∧
 337|     ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
 338|       ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
 339|       ∀ (D : Finset (Zd d L)) (c : Zd d L), (∀ α ∈ D, (zdistInf d L (c - α) : ℝ) ≤ ℓ) → ∀ x y : Fin n → Zd d L,
 340|         ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistInf d L (x i - α) : ℝ) ℓ) * sfT d L W g t (min (zdistInf d L (y i - α) : ℝ) ℓ))
 341|           ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
 342|               (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))
 358| theorem sum_ball_inf_min_pow_le {L : ℕ} [NeZero L] (k : ℕ) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (D : Finset (Zd (k + 2) L))
 359|     (c x : Zd (k + 2) L) (hD : ∀ α ∈ D, ((zdistInf (k + 2) L (c - α) : ℕ) : ℝ) ≤ ℓ) :
 360|     ∑ α ∈ D, ((min ((zdistInf (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹ ≤ ((k + 2 : ℕ) : ℝ) ^ (k + 2) * (ballC k * ℓ ^ 2) := by
 407| theorem sfT_shift_le {d L : ℕ} {W g t : ℝ} (hL : 1 ≤ (L : ℝ)) {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ) :
 408|     sfT d L W g t (max (s - ρ) 0) ≤
 409|       Real.sqrt ((ρ + 1) ^ (d - 2)) * Real.exp ((1 / 2) * Real.sqrt (ρ / ellT L g t)) * sfT d L W g t s := by
 456| def LWXiExpClaim (d : ℕ) : Prop :=
 457|   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
 458|     ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
 459|       ∀ ε₁ : ℝ, 0 < ε₁ → sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
 460|           (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
 461|         ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
 462|           (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
 463|           LWXiE sz (STflowE z) t ℓ D (lwXiVar sz (STflowE z) t ρ)
 467| theorem lwTail32 {d : ℕ} (sz : Sizes d) {𝔠 c : ℝ} (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto)
 468|     (hband : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (a b : ℝ) :
 469|     ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * ((sz.size n : ℕ) : ℝ) ^ a ≤
 470|       ((sz.size n : ℕ) : ℝ) ^ (-b) := by
 527| def LWMomExpNoExp (d : ℕ) (K : ℝ) : Prop := LWMomentExpOn d (fun _ _ _ _ _ => Finset.univ) (regA d K)
 529| def LWMomExpFarPin (d : ℕ) (K : ℝ) : Prop :=
 530|   LWMomentExpOn d (fun L _ a b ℓ => domFar d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q
 532| def LWMomExpNearPin (d : ℕ) (K : ℝ) : Prop :=
 533|   LWMomentExpOn d (fun L _ a _ ℓ => domNearA d L a ℓ) (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q) ∧
 534|     LWMomentExpOn d (fun L _ a b ℓ => domNearB d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q
 537| def LWMomentExpOfParts (d : ℕ) : Prop :=
 538|   ∀ K : ℝ, LWMomExpNoExp d K → LWMomExpFarPin d K → LWMomExpNearPin d K → LWMomentExp d
-- total lines printed: 73
```

**B4 compiled nonempty instances** (run Fri Oct  9 00:39:38 UTC 2026; `python3 -I inst2.py RBM3D/Probe/T2348Pins.lean`; the proofs of the tactic blocks are elided, the term proofs are kept; all compile, B1)
```
 544| example : pvalW (fxyPowGraph 2).pack auxGraph_instD (fun _ => 1) auxGraph_instEll =
 545|     (fxyPowGraph 2).pack.val auxGraph_instD auxGraph_instEll := pvalW_one _ _ _
 547| example (m : ℂ) : ∃ outs : List (ProvOut (fxyPowGraph 2).pack), WExp m (fxyPowGraph 2).pack outs :=
 548|   ⟨_, WExp.comp (WExp.refl m _) (fun o => [⟨o.Q, id⟩]) fun o _ => WExp.refl m o.Q⟩
 551| example (outs : List (ProvOut (fxyPowGraph 2).pack)) (h : WExp (mE 0) (fxyPowGraph 2).pack outs) :=
 552|   WExp.prod h lwWxInstSp lwWxInstM
 553|     ⟨gaussIBP lwWxInstSz, lwWx_inst_im, by norm_num, lwWx_mE_ne 0 lwWx_inst_hE, lwWx_flow 0 (1 / 2) lwWx_inst_hE, lwWx_inst_hSp,
 554|       lwSymm_inst_hSpT, lwWx_inst_hM, lwSymm_inst_hM0⟩ (fun _ x => if x = 0 then 1 else 1 / 2) lwSymmInstL
 556| theorem ProvOut.molecular_id (P : PGraph (Fin 2)) : (⟨P, id⟩ : ProvOut P).Molecular :=
 557|   ⟨fun _ _ h => h, fun c hc => by induction c using SimpleGraph.ConnectedComponent.ind with | h v => exact ⟨v, hc, rfl⟩⟩
 558| example : ((⟨_, id⟩ : ProvOut (fxyPowGraph 2).pack).comp ⟨_, id⟩).Molecular := (ProvOut.molecular_id _).comp (ProvOut.molecular_id _)
 559| example (h : CoverBy (P := (fxyPowGraph 2).pack) fun k : Fin 2 => Sum.inr (localReg_fxyBeta k)) :
 560|     CoverBy (P := (fxyPowGraph 2).pack) fun k : Fin 2 => Sum.inr (localReg_fxyBeta k) := CoverBy.comp h (ProvOut.molecular_id _)
 562| example (h : LWEngineProv) := lwEngineProv_imp_localregularX h 2 (1 / 4) (by norm_num) 1 3 10
 563| example (h : LWGtoAGRooted 3) : LWGtoAG 3 := gtoAGRooted_imp h
 565| example : AnpFarAndAt 3 figAux := lwMomExpFar_inst_figAux
 566| example : lwMomExpFar_farDAnd 3 4 (fun _ : Fin 2 => (0 : Zd 3 4)) (fun _ => ![2, 0, 0]) 1 = domFar 3 4 0 ![2, 0, 0] 1 :=
 567|   domFar_eq (by norm_num) _ _ _
 569| example : (domFar 3 4 (0 : Zd 3 4) ![2, 0, 0] 1).Nonempty ∧ (domNearA 3 4 (0 : Zd 3 4) 1).Nonempty ∧
 570|     (domNearB 3 4 (0 : Zd 3 4) ![2, 0, 0] 1).Nonempty := by ...
 576| example : domFar 3 4 (0 : Zd 3 4) ![2, 0, 0] 1 ∪ domNearA 3 4 0 1 ∪ domNearB 3 4 0 ![2, 0, 0] 1 = Finset.univ := dom_union _ _ _
 577| example := dom_disj (d := 3) (L := 4) 0 ![2, 0, 0] 1
 579| example (ω : sz0.SeqΩ) := LWf_split sz0 0 0 (1 / 2) 1 ω 0 1
 581| example : ∑ α : Zd (1 + 2) 5, ((min ((zdistInf (1 + 2) 5 (0 - α) : ℕ) : ℝ) 5 + 1) ^ 1)⁻¹ ≤
 582|     ((1 + 2 : ℕ) : ℝ) ^ (1 + 2) * (ballC 1 * 5 ^ 2) :=
 583|   sum_ball_inf_min_pow_le 1 (by norm_num) Finset.univ 0 0 fun α _ => Nat.cast_le.2 (lwMoment_zdistInf_le 5 _)
 585| example : sfT 3 4 2 (1 / 2) (1 / 2) (max (10 - 4) 0) ≤ Real.sqrt ((4 + 1) ^ (3 - 2)) *
 586|     Real.exp ((1 / 2) * Real.sqrt (4 / ellT 4 (1 / 2) (1 / 2))) * sfT 3 4 2 (1 / 2) (1 / 2) 10 :=
 587|   sfT_shift_le (by norm_num) (by norm_num) (by norm_num)
 588| example : ‖(1 : ℂ) + 2 + 3‖ ^ 2 ≤ 3 ^ (2 - 1) * (‖(1 : ℂ)‖ ^ 2 + ‖(2 : ℂ)‖ ^ 2 + ‖(3 : ℂ)‖ ^ 2) :=
 589|   norm_add3_pow_le 1 2 3 (by norm_num)
 591| example : ∀ᶠ n in atTop, Real.exp (-(1 * Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * ((sz0.size n : ℕ) : ℝ) ^ (2 : ℝ) ≤
 592|     ((sz0.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) :=
 593|   lwTail32 sz0 (by norm_num) one_pos sz0_admissible.2.2.1 sz0_admissible.2.2.2.1 2 3
-- 17 examples and 1 helper theorem(s); lines 541-594 of the file
```

**B5 name-clash** (run Fri Oct  9 00:39:38 UTC 2026; every new public declaration of the probe against `RBM3D/` outside `Probe/`, whole word, full name and last component)
```
$ clash.sh <worktree> | grep -v "^note:"
new public declarations: 54; full-name hits outside Probe/: 0
$ clash.sh <worktree> | grep -c "^note:"   # last components that also occur elsewhere (e.g. comp, prod, refl): harmless, the probe namespace is RBM.Probe.T2348
8
```

**B6 the project audit with the probe imported** (run Fri Oct  9 00:39:29 UTC 2026; the command `#assert_rbm_axioms` of `RBM3D/Test/Axioms.lean:483` walks every handwritten declaration of the namespace `RBM`; its order of checks: the axioms of all handwritten declarations (`:504-514`), then the classification of the premises (`:540-542`))
```
$ cat axall.lean; lake env lean axall.lean | sed "s|^/[^ ]*/axall.lean|axall.lean|"
import RBM3D
import RBM3D.Probe.T2348Pins
#assert_rbm_axioms
axall.lean:3:0: error: axiom audit: 3 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Probe.T2348.LWGtoAGRooted, RBM.Probe.T2348.LWEngineProv, RBM.Probe.T2348.LWExpData]
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed).
```

Narrative (every number is in B1-B6 or in `docs/reports/T2348-design.md`; nothing was copied from RBM1D or RBM2D, so no port diff-stat applies):
1. Deliverables: `docs/reports/T2348-design.md` answers items 1-7 (section 0 table; sections 2-8; section 10 is script output: long statements, sizes and rows, the de-privatisation list, the echo of every citation). The probe `RBM3D/Probe/T2348Pins.lean` is on branch `t/T2348` at the commit of B1: 598 of the 600 lines, `lake build` exit 0, 12 `#print axioms` standard, `collectAxioms` over every constant of the probe namespace finds no non-standard axiom (B2), no `sorry`. The project audit `#assert_rbm_axioms` with the probe imported passes its axiom step and stops at its premise classification (B6): `LWGtoAGRooted`, `LWEngineProv`, `LWExpData` are premises of probe theorems that no theorem proves, expected for a probe that is never merged (see (d)). The reports live in the main worktree, so the branch diff is the probe only (B1).
2. Proved in the probe, each with an instance in B4: `WExp.comp` (recursion step, maps compose), `WExp.prod` (the ticket's weighted identity; instance at the merged data of `lwEngine_inst_step1_identity`, every deterministic hypothesis discharged; the expansion pin `WExp` of row R1 is the hypothesis `h` of the instance, satisfiable by the `WExp.comp` instance), `ProvOut.Molecular.comp` and `CoverBy.comp` (instances at the identity maps of `fxyPowGraph 2`; the initial coverage is a hypothesis), `lwEngineProv_imp_localregularX` and `gtoAGRooted_imp` (the engine pin and the rooted pin are hypotheses of the instance: they are rows R1 and R3), `LWf_split`, `norm_add3_pow_le`, `sum_ball_inf_min_pow_le`, `sfT_shift_le`, `lwTail32`, `domFar_eq`, `dom_union`, `dom_disj`.
3. Statements only (`Prop` definitions without proof or instance; their proofs are the proving rows): `LocStepXProv`, `LWEngineProv`, `LWGtoAGRooted`, `LWAuxNestedOwnOn`, `EKTTkInf`, `AnpNearInfAt`, `LWXiExpClaim`, `LWMomExpNoExp`, `LWMomExpFarPin`, `LWMomExpNearPin`, `LWMomentExpOfParts`.
4. Results (design section 0): item 1: every `LocStepX` constructor is pointwise in the old labels, no real twin; item 2: route (R) roots each internal molecule at its weighted vertex, so the pins need no radius, at the price of a rooted `GtoAG` (new row G); route (E) needs a cap conversion with the factor `(Rb+1)^{(d-2)/2}`, which the ticket (`T2348.md:7`), supervisor 2244 R1 and T2344 (a) row 11 omit; item 3: the three-way split is an exact identity; item 4: the G2 radius `(log W)^{3/2}` closes asymptotically, Lean's `K(log W)²` never; item 5: ten `private` keywords, not two; item 6: assembly stated; item 7: three rows 1003/1440/2170, 1182/1573/2344, 1183/1567/2337 lines (lo / central / hi), LW-01 = 52.
5. Limits: no finite witness of the G2 conclusion or of the pins is claimed (`≺` closes as `∀τ ∀ᶠ n`, as every merged pin); the row sizes are estimates (measured bases times multipliers, B5 of the design); the weighted `|f|^p` bridge (`pvalW (fxyPowGraph p).pack … = ‖LWfD …‖^p`) is stated in the design, not compiled.

### (c) Verified Mathlib names (run Fri Oct  9 00:40:32 UTC 2026)
```
$ lake env lean names.lean   # Lean.resolveGlobalName of every identifier token of the probe (comments stripped) that contains "." or "_", under the probe's `open`s
$ python3 -I group_names.py names_out.txt 2   # Mathlib/Init constants by module prefix; RBM3D constants, tactics and data constructors omitted
Init.Core: Function.comp_def
Init.Data: List.map_append, List.map_congr_left, List.map_map
Init.SimpLemmas: iff_true, true_and
Mathlib.Algebra: Fin.sum_univ_three, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_congr, Finset.sum_le_sum, add_div, add_zero, div_le_div_iff₀, div_le_div_of_nonneg_right, inv_eq_one_div, le_abs_self, le_of_mul_le_mul_right, mul_assoc, mul_le_mul, mul_le_mul_of_nonneg_left, mul_min_of_nonneg, mul_one_div, mul_pow, neg_add_cancel, one_div, one_pos, pow_le_pow_left₀, pow_pos, pow_sum_le_card_mul_sum_pow, sq_nonneg
Mathlib.Analysis: Real.exp_add, Real.exp_le_exp, Real.exp_pos, Real.le_log_iff_exp_le, Real.le_sqrt, Real.rpow_add, Real.rpow_def_of_pos, Real.rpow_le_rpow_of_exponent_le, Real.rpow_one, Real.rpow_pos_of_pos, Real.rpow_zero, Real.sqrt_div, Real.sqrt_eq_rpow, Real.sqrt_le_sqrt, Real.sqrt_mul, Real.sqrt_pos, Real.sqrt_zero, norm_add_le, norm_nonneg, tendsto_rpow_atTop
Mathlib.Combinatorics: SimpleGraph.ConnectedComponent, SimpleGraph.ConnectedComponent.ind
Mathlib.Data: Finset.card_univ, Finset.disjoint_left, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, Fintype.card_fin, Fintype.piFinset_univ, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_le, Nat.cast_le_one, Nat.cast_nonneg, Nat.cast_ofNat, Nat.one_lt_cast
Mathlib.Order: Filter.eventually_ge_atTop, le_max_right, le_min, le_rfl, le_total, le_trans, max_eq_left, max_eq_right, min_le_min, not_le
-- 78 names in 8 module groups
$ lake env lean absent.lean | sed "s|.*/||"   # guessed names that do not exist
absent.lean:2:8: error(lean.unknownIdentifier): Unknown constant `List.sum_flatMap`
absent.lean:3:8: error(lean.unknownIdentifier): Unknown constant `Real.sqrt_le_add`
absent.lean:4:8: error(lean.unknownIdentifier): Unknown identifier `pow_sum_le_card_mul_sum_pow'`
absent.lean:5:8: error(lean.unknownIdentifier): Unknown constant `List.sum_flatMap'`
```

### (d) Open issues and paper-delta candidates
Paper-delta candidates (the dispatcher numbers them; `T2344a`-`T2344d` are those of supervisor 2244 O3, `2026-10-08-2244.md:63`):
- `T2344a` (`7_8:1631-1648`, `7_8:860`): "all internal vertices lie in `D`" holds because every internal molecule contains a vertex `π β^{(k)}` that carries the weight; Lean carries the weight through the expansion (`WExp`, `Molecular`, `Cover`) and roots the auxiliary vertex there (the paper's free centre, `7_8:860`).
- `T2344b` (`7_8:1607-1611`): `f = f^> + f^(a) + f^(b)`, "and" far domain, single-centre near domains (`LWf_split`).
- `T2344c` (`7_8:95-97`, `7_8:1653`): molecule/tail radius `(log W)^{3/2}`; shift comparability `Φ(m) ≤ Kn Φ(ℓ)` (`sfT_shift_le`) replaces the polynomial `(eq:Psi)` of `LWPsiAll`.
- `T2344d` (`7_8:1662`, `1_2:274`): `claim:TTk` in `ℓ^∞` (`EKTTkInf`, constant `d^{k+2} ballC_k`).
- `T2348a`: the cost of shifting the cap is `(ρ+1)^{(d-2)/2} e^{½√(ρ/ℓ_t)}`, not `e^{½√(ρ/ℓ_t)}`; sharp ((a) script (2), `sfT_shift_le`).
- `T2348b` (`7_8:1602`): regime (A) at the scale `K (log W)^{3/2} ℓ_t` with a free `K`, because the expansion needs `|a-b| > K r`.
- `T2348c` (a correction of the ticket and of supervisor 2244 O1, not a paper delta): the `ℓ^∞` twin needs ten `private` keywords removed (design B6), not two.
Open questions for the REQ (design section 9): (1) route (R) (rooted `GtoAG`, exact domains) or route (E) (enlargement by `Rb`)? (2) accept the three-row packing, the cuts C1-C3 and LW-01 = 52? (3) release R1 and R2 together (no shared file)?
Premise ledger (B6): in merged code a `Prop` that a theorem assumes must be proved by some theorem or classified in `Test/Axioms.lean`. `LWGtoAGRooted` and `LWEngineProv` are the pins of rows R3 and R1 and become theorems there; `LWExpData` (assumed by `WExp.prod`) is not provable, so R1 spells its nine conjuncts inline, as `LWLocRegConcl` conjunct 4 does (R1's only writable file, design section 8, is `Graph/LWProv.lean`, not `Test/Axioms.lean`).
Open issues: the initial coverage `CoverBy (fxyPowGraph p)` (every initial molecule is `{α_k, β_k}`, `Graph/LocalRegular.lean:1354`) and the weighted `|f|^p` bridge are not compiled; `LWClass` for the exp class `Φ_E` is checked only through (a) rows 4-6.
Not claimed: any proof of `LocStepXProv`, `LWEngineProv`, `LWGtoAGRooted`, `LWAuxNestedOwnOn`, `EKTTkInf`, `AnpNearInfAt`, `LWXiExpClaim`, the three pins or the assembly; these are statements that elaborate.
