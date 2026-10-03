Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 22:21:37 UTC 2026

Target: `stScaleExists_holds (d : ℕ) : STScaleExists d` (`Step2Defs.lean:656`). Notation: `T_u(r)=tailT d L lam u r = B_{u,r} e^{-√(r/ℓ_u)}`, `β_u := sz.Bctl n u = W^{-d}B_{u,0}`, `Y^m_u := T_u(K^m_u)`, `γ := min(2𝔡, dε/2)`, `γ' := γ/2`.

### (i) Exponent table and construction
Construction (per n, per u in [0,1); elsewhere `K:=0`): K^0=0; y_m := β_u^{1/6} T_u(K^m); if some r ≥ K^m has T_u(r)=y_m (IVT on [K^m,R], R = ℓ(log(B_0/y_m))² gives T(R) ≤ B_0 e^{-√(R/ℓ)} ≤ y_m), pick it as r_m, else r_m:=K^m; K^{m+1}:=min(r_m, L). Never uses `∀ n`: all properties hold for n ≥ n₀ (table), u ∈ [s_n,t_n].

| # | quantity | value / source | constraint | slack |
|---|---|---|---|---|
| 1 | t_n<1, 0≤s_n≤u≤t_n | `lemT_lt_one` (needs Im z>0: `locDomain` gives Im z ≥ N^{-1+ε}>0); merged `v3_premises_of_stFlow` (Green/Pins.lean:1048) gives `t n<1` ∀n and RangeCond(ε/2): eventually 1-t_n ≥ N^{-1+ε/2} | B,T defined with 1-u>0; ℓ_u>0 | 1-u ≥ 1-t_n ≥ N^{-1+ε/2}; 1-lemT ≥ Im z/4 |
| 2 | continuity of r↦T_u(r) on [0,∞) | **not merged** (grep: no `tailT` continuity in Defs/Tail.lean, Step2Core); prove here: (r+1)^{d-2} ≠ 0 on r ≥ 0, √, exp continuous | ContinuousOn (Ici 0); used only for IVT in r_m | none (exact) |
| 3 | antitone, T_u(r)>0 | `tailT_antitone` (Defs/Tail.lean:88), B_r ≥ (L^d(1-u))^{-1}>0 | y_m>0 needs β_u>0: `STBctl_pos` (ScaleFacts.lean:64) | exact |
| 4 | T_u(r) nondecreasing in u (fixed r ≥ 0) | merged `ST_tailT_mono_time` (Step2Core.lean:276), needs lam ≥ 0 (eventually, from WO: lam ≥ W^{-d/2+𝔡} ≥ 0) | ℓ_u,B_{u,r} both increase in u | exact |
| 5 | β_u nondecreasing in u | `STBctl_mono` (ScaleFacts.lean:74) | | exact |
| 6 | Smallness: β_u ≤ β_{t_n} ≤ 2W^{-γ} ≤ W^{-γ'} | term1: W^{-d}(lam²+1-u)^{-1} ≤ (lam²W^d)^{-1} ≤ W^{-2𝔡} (`lam_sq_mul_pow_ge`, WO); term2: (WL)^{-d}(1-u)^{-1} = N^{-1}/(1-u) ≤ N^{-ε/2} (RangeCond) ≤ W^{-dε/2} (N=(WL)^d ≥ W^d since L ≥ 3); last step needs W^{γ'} ≥ 2 | γ=min(2𝔡,dε/2); eventually: W→∞ (Bandwidth W ≥ N^𝔠, N→∞) | at 𝔡=ε=1/10, d=3: γ=3/20, γ'=3/40, W^{3/40} ≥ 2 iff W ≥ 10321 (n ≥ 3 at sz0) |
| 7 | β ≤ 1 (needed for K^m ≤ K^{m+1}, y_m ≤ T(K^m) ≤ B_0) | from row 6 for W ≥ 2^{1/γ'} | | same n₀ |
| 8 | Lower bound β_u ≥ c W^{-d}, c=(1+𝔡^{-2})^{-1} | B_0 ≥ (lam²+1-u)^{-1} ≥ (𝔡^{-2}+1)^{-1} (u ≥ 0, lam ≤ 1/𝔡 by WO) | log(1/β) ≤ d log W + log(1+𝔡^{-2}) | uses 0 ≤ s |
| 9 | Y^m ≥ β^{m/6} B_0 (all m) | induction: Y^{m+1}=T(min(r_m,L)) = max(y_m,T(L)) ≥ y_m = β^{1/6}Y^m | β ≥ 0 | exact |
| 10 | STScaleOk clause K ≤ (log W)^{10} ℓ_u | K^{m+1} ≤ r_m; T(r_m)=y_m ≥ β^{(m+1)/6}B_0 and B_r ≤ B_0 ⇒ e^{-√(r_m/ℓ)} ≥ β^{(m+1)/6} ⇒ r_m ≤ ℓ((m+1)/6)²log²(1/β) ≤ ℓ((m+1)/6)²(d log W + C)² | ≤ (log W)^{10}ℓ eventually (W→∞), each fixed m | exponent 2 vs 10: slack 8 powers of log W |
| 11 | K^m ≤ K^{m+1}, K ≤ L, K ≥ 0 | r_m ≥ K^m by IVT interval; K^m ≤ L by induction (K^0=0) | | exact |
| 12 | clause-4: β^{1/6}T(K^m) ≤ T(K^{m+1}) | K^{m+1} ≤ r_m, antitone ⇒ T(K^{m+1}) ≥ T(r_m)=y_m | | exact (≥, equality unless cut) |
| 13 | `u↦T_u(K_u)` nondecreasing | Y^{m+1}_u = max(β_u^{1/6}Y^m_u, T_u(L)); Y^0=B_{u,0} nondecreasing; products/max of nonneg nondecreasing (rows 4,5) | β ≤ 1 only for the IVT existence | exact |
| 14 | Cut absorbing: K^m=L ⇒ K^{m+1}=L | y_m=β^{1/6}T(L) ≤ T(L); IVT interval [L,R], r_m ≥ L ⇒ min = L | β ≤ 1, T(L)>0 | exact |
| 15 | Floor, D>0 | by induction K^m=L ∨ Y^m ≤ β^{m/6}B_0 (rows 9,14); if K_M<L: Y^M ≤ β^{M/6}·W^dβ = W^dβ^{1+M/6} ≤ W^{d-γ'(1+M/6)} ≤ W^{-D} | M(D)=⌈6(d+D)/γ'⌉, so γ'(1+M/6) ≥ d+D; W ≥ 1 | at D=10, d=3: M=1040, γ'(1+M/6)=523/40=13.075 ≥ 13 (slack 0.075 in the exponent of W); M ≍ (D+d)/γ' as in the pin's docstring |
| 16 | DECISIONS §29 (1) time domain | 0≤s, t<1 (row 1); boundary s=0: u=0 fine (1-u=1); t=lemT: 1-lemT ≥ Im z/4>0 | | holds |
| 17 | §29 (2) boundary 1-lam²/L², lam>L | not used: ℓ_u=ellT=min(max(·,1),L) ∈ [1,L] for every lam, u<1; only ℓ_u>0 (`ellT_pos`) and `ellT_mono` (lam ≥ 0) enter; no negative time arises | | holds |
| 18 | §29 (3) L^d ≤ W^K | not used: only N=(WL)^d ≥ W^d (row 6) | | holds |
| 19 | §29 (4) ∀ vs ∀ᶠ | every clause but K^0=0 is eventual in n (pin as restated); rows 6–7,10,13 hold for n ≥ n₀(m or D) only; for n<n₀ the definition is the `else` branch and nothing is asserted (the T2039 round-1 counterexample forced β ≤ 1 at all n) | | holds |
| 20 | Exactness of the pin | statement true as written for every d (d<3 included: (r+1)^{d-2} with natural subtraction is still ≥1 and antitone; `3 ≤ d` not needed; for d=0 the hypothesis STFlow is unsatisfiable, N=1, so the statement is vacuous there) | | holds |

### (ii) Concrete instance (d=3): `sz0` (L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{-6}), 𝔠=1/6, 𝔡=1/10, κ=ε=1/10, z0 n = 1/2 + i N^{-4/5}, s=sInst=0, t=tInst=1/16 (hypotheses: `flow_z0` Induction/Defs.lean:435, `sixteenth_le_lemT` :429, 0 ≤ 0 ≤ 1/16 ≤ lemT(z0 n)); u ∈ {0,1/32,1/16}; K^m, m ≤ 4, by bisection at 60 digits (scratch `probe.py` outside the repo; no Lean):
```
$ python3 probe.py          (output trimmed to n=0 and u=0, 1/16; n=3 rows are analogous, all flags True)
n=0: L=4 W=32 lam=1.562e-02 N=2097152
 u=0.00000 Bctl=3.0987e-05 B0=1.0154 ell=1.0000 (logW)^10*ell=2.500e+05
   K^m   = ['0.000000', '1.053978', '3.798896', '4.000000', '4.000000']  r_m = ['1.0540', '3.7989', '9.0717', '9.4301']
   T(K^m)= ['1.0154e+00', '1.7995e-01', '3.1893e-02', '2.9175e-02', '2.9175e-02']
   K monotone/<=L/<=(logW)^10 ell: True   clause4: True
 u=0.03125 K^m = [0, 1.048468, 3.775452, 4, 4]   T(K^m)= [1.0481e+00, 1.8674e-01, 3.3271e-02, 3.0116e-02, 3.0116e-02]  T_u(K_u) nondecreasing in u: all True
 u=0.06250 K^m = [0, 1.042793, 3.751338, 4, 4]   T(K^m)= [1.0831e+00, 1.9402e-01, 3.4758e-02, 3.1120e-02, 3.1120e-02]  T_u(K_u) nondecreasing in u: all True
n=3: L=16 W=32768 lam=3.815e-06 N=1.44e17 ; u=1/16: K^m = [0, 8.583848, 16, 16, 16], T(K^m)=[1.0669, 5.958e-03, 1.154e-03, ...]; flags True
n=0 D=10: first m with T(K_m)<=W^-10 or K_m>=L: m=3, K_m=4.0000 (cut), T=3.112e-02 vs W^-10=8.882e-16
n=3 D=10: first m: m=2, K_m=16.0000 (cut), T=1.154e-03 vs W^-10=7.006e-46
```
Note ℓ_u=1 here (lam tiny): the cap (log W)^{10}ℓ is far from binding; the cut at L is what produces the floor disjunct `L ≤ K_M`. The uncut-chain floor of row 15 (asymptotic, general n):
```
$ python3 floor.py
gamma = 3/20  gamma' = 3/40  M(D=10) = 1040  gamma'(1+M/6) = 523/40  >= d+D = 13
n=3: 2W^-gamma<=W^-gamma' : True  Bctl<=2W^-gamma: True  term1<=W^-2dd: True  term2<=N^-eps/2: True  RangeCond 1-t>=N^(-1+eps/2): True  W^d Bctl^(1+M/6) <= W^-D: True  log10 LHS=-2343.1 log10 RHS=-45.2
n=4 and n=10: all same flags True (log10 LHS=-2595.1, -3485.4; RHS=-50.0, -67.1)
```
External hypotheses: none (all inputs are merged: `lemT_lt_one`, `v3_premises_of_stFlow`, `ST_tailT_mono_time`, `STBctl_mono`, `lam_sq_mul_pow_ge`); no limit computation owed. Hypotheses of the pin at this instance (`STFlow`, 0≤s, s≤t, t≤lemT) hold as listed; the first n at which rows 6–7 hold is n=3 (W=32768 ≥ 10321), and n=0 already has β ≤ 1 (3.3e-5).

### Verdict
- `stScaleExists_holds`: **PASS** (true as written for all d; no counterexample at the boundaries of §29 (1)–(4); row 2 is the only new analytic lemma, continuity on [0,∞)).
- Registry: the owed line `RBM.Gauss.Sizes.STScaleExists` (Test/Axioms.lean:139) can go once this merges (cleanup ticket removes it).

## (b) Script output (stage 1b, written Sat Oct  3 22:36:02 UTC 2026; branch `t/T2081`)

No (a′) written: no mistake in (a) that affects the file was found.  The file does not use (a)'s W-based route (`γ`, `M(D)=⌈6(d+D)/γ'⌉`, rows 6, 15); it uses the N-based route of the merged `scaleFacts_R1` (below).

### Build, hygiene, axioms
```
$ lake env lean RBM3D/Induction/Step2Scale.lean > out.txt 2>&1; echo "exit=$?"; wc -l < out.txt
exit=0
       0
$ lake build RBM3D.Induction.Step2Scale 2>&1 | tail -1
Build completed successfully (3721 jobs).
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/Step2Scale.lean || echo none
none
$ lake env lean ax2.lean   (import RBM3D.Induction.Step2Scale; #print axioms; #check)
'RBM.Gauss.Sizes.stScaleExists_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stScaleExists_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STScaleExists d
```

### Registry pre-check = full `lake build` with the module imported (the hub adds the import at merge; here reverted)
```
$ [temporary `import RBM3D.Induction.Step2Scale` after the last import of RBM3D.lean; reverted below] lake build 2>&1 | tail -2
non-vacuity certificates: 4 of 92 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3820 jobs).
$ lake env lean RBM3D.lean 2>&1 | grep -n "axiom audit\|All within\|^registry\|error\|unclassified\|STScaleExists" | cut -c1-150
1:axiom audit: 2541 theorems, 1073 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
2:All within [propext,
63:  RBM.Gauss.Sizes.STScaleExists: 2 [no certificate]
100:registry: 5 borrowed + 87 owed + 36 structural; 46 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
116: RBM.Gauss.Sizes.STScaleExists,
$ git status --short   (RBM3D.lean restored)
(empty = clean)
```

### Target statement against the pin
```
$ sed -n 656,660p RBM3D/Induction/Step2Defs.lean   (the merged pin, verbatim)
def STScaleExists (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz s t Kseq
$ grep -n "^theorem stScaleExists_holds" RBM3D/Induction/Step2Scale.lean
430:theorem stScaleExists_holds (d : ℕ) : STScaleExists d := by
```
`#check` (above): `stScaleExists_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STScaleExists d`; the pin is not touched and has no added hypothesis.

### Compiled nonempty instances (`d = 3`)
```
$ sed -n '569,595p' RBM3D/Induction/Step2Scale.lean   (the compiled instances; they build with the file)
section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- **Instance 1** (`d = 3`, `sz0`, `s ≡ 0`, `t ≡ 1/16`): the scale family exists. -/
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq :=
  stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => sixteenth_le_lemT n)

/-- **Instance 2** (`d = 3`, `sz1`: the coupling at the lower end of `(eq:WO)`). -/
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz1 sInst tInst Kseq :=
  stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz1 z0 flow_z1 sInst tInst (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => sixteenth_le_lemT n)

/-- **Instance 3**: two clauses of `STScaleAdm` at the interior time `u = 1/32 ∈ (0, 1/16)`. -/
example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq ∧
    ∀ᶠ n in atTop, 0 ≤ Kseq 1 n (1 / 32) ∧ Kseq 1 n (1 / 32) ≤ Kseq 2 n (1 / 32) := by
  obtain ⟨K, hK⟩ := stScaleExists_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by norm_num [sInst, tInst]) (fun n => sixteenth_le_lemT n)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hK.2.2.1 1] with n hn
  exact hn (1 / 32) (by norm_num [sInst]) (by norm_num [tInst])

end Instances
```

### Name clash, ports, scope
```
$ grep -rn "stScaleExists_holds" RBM3D --include="*.lean" | grep -v "Induction/Step2Scale.lean" || echo "no other occurrence"
no other occurrence
$ grep -rn "st2s" RBM3D --include="*.lean" | grep -v "Induction/Step2Scale.lean" || echo "no other occurrence"
no other occurrence
$ grep -c "^private \(theorem\|def\) st2s" RBM3D/Induction/Step2Scale.lean   (all helpers are private, prefixed st2s)
23
$ grep -n "^theorem\|^def\|^lemma" RBM3D/Induction/Step2Scale.lean   (the only public declaration)
430:theorem stScaleExists_holds (d : ℕ) : STScaleExists d := by
$ grep -rln "def_ell1\|ScaleFamily\|ScaleExists\|scaleStep" ../../RBM2D/RBM2D ../../RBM1D/RBM1D || echo "none (no port from RBM1D/RBM2D)"
none (no port from RBM1D/RBM2D)
$ git diff --stat main...t/T2081
 RBM3D/Induction/Step2Scale.lean | 597 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 597 insertions(+)
$ git log --oneline main..t/T2081
5f12e8f T2081: docstring of st2sStep (uniqueness is not used)
df9c6dc T2081: ST2-05 scale family of (eq:def_ell1), proves STScaleExists (stScaleExists_holds)
```

### Narrative
- Construction (file header and §2): `K^(0)=0`; `K^(m+1) = min(r, L)` for a solution `r ≥ K^(m)` of `𝒯_u(r) = β^{1/6} 𝒯_u(K^(m))`, `β = W^{-d}B_{u,0}` (`st2sStep`, `st2sSeq`); if no solution exists the level stays `K^(m)` (this branch is never taken when `0<β≤1`, `u<1`: `st2s_step_exists`).
- Continuity of `r ↦ tailT d L g u r` on `[0,∞)` was not merged: `st2s_tailT_continuousOn` proves it here; it is used only by `st2s_exists_eq` (IVT on `[K, R]`, `R = max K (ℓ_u (log(B_{u,0}/y))²)`).
- Per `(n,u)` facts (`st2sSeq_*`): `0 ≤ K^(m) ≤ L`, `K^(m) ≤ K^(m+1)`, `T(K^(m+1)) = max(q T(K^(m)), T(L))` (so `qT(K^(m)) ≤ T(K^(m+1))`), the cut is absorbing, `K^(m)=L ∨ T(K^(m)) ≤ q^m B_{u,0}`, `K^(m) ≤ ℓ_u((m/6)(-log β))²`, and `u ↦ T_u(K^(m)_u)` nondecreasing (`ST_tailT_mono_time`, `STBctl_mono`).
- Where `STFlow` enters (`stScaleExists_holds`): `v3_premises_of_stFlow` gives `t_n<1` and `RangeCond(ε/2)`; `Admissible` gives `N→∞`, `W ≥ N^𝔠`, `(eq:WO)`; `scaleFacts_R1` gives `β_u ≤ 2N^{-c₀}`, `c₀=min(2𝔠𝔡, ε/2)`.  `d ≥ 1` is derived (`d=0` has `N=1`, contradicting `N→∞`).
- Eventuality (DECISIONS §29 (4)): `hgood` (`lam ≥ 0`, `lam ≤ 𝔡⁻¹`, `0<β≤1`, `β ≤ 2N^{-c₀}` for `u ∈ [s_n,t_n]`) holds for `n ≥ n₀`; the cap clause adds `W ≥ max(e^{max(1,A_m)}, 𝔡⁻²+1)`, `A_m=(m(d+1)/6)²`; the floor adds `N ≥ 2^{j+1}`.  Only `K^(0)=0` is for every `n`.
- Floor: `M(D) = 6j`, `j = ⌈(2+D)/c₀⌉`: `T(K^(M)) ≤ β^j B_{u,0} = W^d β^{j+1} ≤ W^{-D}` (`st2s_floor_arith`: `W^d ≤ N`, `W ≤ N`, `2^{j+1} ≤ N`), or `K^(M)=L`.
- Cap: `log(1/β) ≤ (d+1) log W` from `STBctl_ge` (`β ≥ (W^d(𝔡⁻²+1))⁻¹`), then `((m/6)(d+1))² log²W ≤ (log W)^{10}` once `log W ≥ max(1,A_m)` (`st2s_cap_arith`).
- Imports: `Step2Core`, `ScaleFacts`, and `Green.Pins` (for `v3_premises_of_stFlow`); no RBM1D/RBM2D port; `Test/Axioms.lean` is not edited; `RBM3D.lean` was edited only temporarily for the full build and restored (`git status` clean above).
- Instances: three `example`s at `d=3` (`sz0` and `sz1`, `s ≡ 0 < t ≡ 1/16`, `𝔠=1/6`, `𝔡=κ=ε=1/10`): every hypothesis of `stScaleExists_holds` is a merged deterministic fact; no stochastic hypothesis is involved; the third reads the third conjunct of `STScaleAdm` (`0 ≤ K_m ≤ K_{m+1}`, `m = 1`) at `u = 1/32`.
- Registry: the scan output above reports `STScaleExists: 2 [no certificate]` and lists it among the 46 registered premises that "carry nothing yet" (`scanPremises`, `Test/Axioms.lean:295-297`, counts a theorem with that conclusion head as proving the premise); the full build passes.  The owed line `Test/Axioms.lean:139` (at the branch base 4128ef0) can go once this merges (cleanup ticket).  `Step2Defs.lean:1127` `inst_scaleExists (h : STScaleExists 3)` can then be discharged by `stScaleExists_holds 3` (not done here: outside the sole writable files).

## (c) Verified Mathlib / core names used (`#check` at this commit, script `names.lean`)
```
@intermediate_value_Icc' : ∀ [OrderTopology α] [DenselyOrdered α] {δ : Type u_2} [OrderClosedTopology δ] {a b : α}, a ≤ b → ∀ {f : α → δ}, ContinuousOn f (Set.Icc a 
@ContinuousOn.inv₀ : ∀ {G₀ : Type u_2} [ContinuousInv₀ G₀] {f : α → G₀} {s : Set α} , ContinuousOn f s → (∀ x ∈ s, f x ≠ 0) → ContinuousOn f⁻¹ s
Real.sqrt_sq_eq_abs : ∀ (x : ℝ), √(x ^ 2) = |x|
@Real.exp_log : ∀ {x : ℝ}, 0 < x → Real.exp (Real.log x) = x
Real.exp_neg : ∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
@Real.log_rpow : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), Real.log (x ^ y) = y * Real.log x
Real.log_pow : ∀ (x : ℝ) (n : ℕ), Real.log (x ^ n) = ↑n * Real.log x
Real.log_inv : ∀ (x : ℝ), Real.log x⁻¹ = -Real.log x
@Real.log_mul : ∀ {x y : ℝ}, x ≠ 0 → y ≠ 0 → Real.log (x * y) = Real.log x + Real.log y
@Real.log_le_log : ∀ {x y : ℝ}, 0 < x → x ≤ y → Real.log x ≤ Real.log y
@Real.log_nonpos : ∀ {x : ℝ}, 0 ≤ x → x ≤ 1 → Real.log x ≤ 0
@Real.le_log_iff_exp_le : ∀ {x y : ℝ}, 0 < y → (x ≤ Real.log y ↔ Real.exp x ≤ y)
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_le_rpow_of_nonpos : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
@Real.rpow_one_add' : ∀ {x y : ℝ}, 0 ≤ x → 1 + y ≠ 0 → x ^ (1 + y) = x * x ^ y
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
@tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ y) atTop atTop
@tendsto_rpow_neg_atTop : ∀ {y : ℝ}, 0 < y → Tendsto (fun x => x ^ (-y)) atTop (nhds 0)
@Iic_mem_nhds : ∀ [ClosedIciTopology α] {a b : α}, b < a → Set.Iic a ∈ nhds b
@Nat.le_ceil : ∀ {R : Type u_1} (a : R), a ≤ ↑⌈a⌉₊
@Nat.le_self_pow : ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
@Nat.pow_le_pow_left : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
@pow_le_pow_right₀ : ∀ {M₀ : Type u_1} {a : M₀} {m n : ℕ} [ZeroLEOneClass M₀] [PosMulMono M₀], 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n
@dite_eq_left : ∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u_1} {t : c → α} {e : ¬c → α}, dite c t e = t hc
```
Deprecated in Lean core 4.34 (build warnings seen while writing): `dif_pos` (use `dite_eq_left`), `dite_cond_eq_true` (use `dite_eq_left_of_eq_true`).

## (d) Open issues and paper-delta candidates
- **T2081a** (`(eq:def_ell1)`, `3_5:570-571`): the paper takes "the unique positive solution `K'_u`"; Lean's `st2sStep` takes a solution `r ≥ K` of `𝒯_u(r) = q 𝒯_u(K)` cut at `L` (`min r L`; the paper handles `K_u ≥ L` by the remark `𝒯̃^K ≍ 𝒯̃^L`), and keeps `K` where no solution exists (outside `n ≥ n₀`).  Uniqueness is not proved (not needed).
- **T2081b** (`3_5:575-577`): the pin leaves `M(D)` as `∃ M`; the file's `M(D) = 6⌈(2+D)/c₀⌉`, `c₀ = min(2𝔠𝔡, ε/2)`, depends on `𝔠, 𝔡, ε`, not only on `(D+d)/c` as in the pin's docstring (the pin's statement is unchanged; docstring wording only).
- **T2081c**: the pin's cap `K ≤ (log W)^{10} ℓ_u` holds per fixed `m` with `n₀` depending on `m` (as the pin's `∀ᶠ n` after `∀ m`); no uniformity in `m` is claimed.
- Registry cleanup after merge: remove `RBM.Gauss.Sizes.STScaleExists` (`Test/Axioms.lean:139` at the branch base 4128ef0); optionally discharge `inst_scaleExists` (`Step2Defs.lean:1127`).
- Hub at merge: add `import RBM3D.Induction.Step2Scale` after the last `import` line of `RBM3D.lean` (verified to build in section (b)).
