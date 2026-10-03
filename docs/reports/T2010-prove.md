Prover model: claude-sonnet-5-5

## (a) Math preflight — 2026-10-03 00:24:13 UTC

### (i) Exponent table

Notation: e = 1 - t, γ = lgGam d g t = t g²/(1+2dg²), ε = e/γ, k = m - 1, Γ = Real.Gamma.

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| Key exponent | A^{-(m/2-1)} = (c n²/2)^{-(m-2)/2} | pin writes -((m:ℝ)-2)/2 = -(m/2-1) | equal |
| Gamma integrand exponent | q = m/2 - 2 | q > -1 (needed by integral_rpow_mul_exp_neg_mul_rpow, p=1) | m=3: q=-1/2 (slack 1/2); m=4: 0; m=5: 1/2 |
| Gamma argument | m/2 - 1 | > 0 | m=3: 1/2; m=4: 1; m=5: 3/2 |
| Γ(m/2-1) | m=3: √π ≈ 1.7725; m=4: 1; m=5: √π/2 ≈ 0.8862 | value in the Key bound | printed by script below |
| Tail of ∫_1^∞ τ^{-m/2} | 1/(m/2-1) = 2/(m-2) | m/2 > 1 | m=3: 2 |
| AM-GM | ετ + (c/2)n²/τ ≥ √(2cε)·n ≥ √(cε)·n | τ>0, c,ε ≥ 0 | factor √2 in the exponent (dropped); measured Key LHS/RHS max 0.7071 = 2^{-1/2} at ε=0, m=3 (exact value there is Γ(m/2-1)(cn²)^{-(m-2)/2}) |
| LGBulk c' | min(c/2, 1) | c' ≤ c/2 (ε≤1 branch, absorbs e^{-cn} = e^{-(c/2)n}e^{-(c/2)n}); c' ≤ √c (Key); c' ≤ min(c,1) (ε≥1 branch) | c<4: c/2 ≤ √c ⇔ c ≤ 4; c ≥ 4: c' = 1 ≤ √c; c' ≤ c/2 ≤ c and c' ≤ 1 |
| LGBulk C | C1 + C2, C1 = (2(m-1)/(c e))^{m-1} (= sup_{x≥0} x^{k}e^{-(c/2)x}), C2 = Γ(m/2-1)(c/2)^{-(m-2)/2}; any larger C also valid, e.g. C1' = (m-1)!(2/c)^{m-1} ≥ C1 (from y^k/k! ≤ e^y) | C > 0; n e^{-cn} ≤ C1 n^{-(m-2)} e^{-(c/2)n}; Key part ≤ C2 n^{-(m-2)} e^{-√(cε)n} | m=3,c=0.18: C = 72.74; max measured LHS/RHS = 0.454 (ε≤1), 0.493 (ε≥1) |
| LGBulk ε=1 | both bullets must hold | ε≤1 and 1≤ε both | both proved on their own, no overlap issue |
| Bulk split | ∫_{(0,n]} ≤ e^{-cn} min(n,1/ε); ∫_{(n,∞)} ≤ Key(c) for ε≤1, ≤ e^{-εn}/ε ≤ e^{-n}/ε for ε≥1 | τ ≤ n ⇒ n²/τ ≥ n; τ > n ⇒ min = n²/τ | needs 1 ≤ n only for e^{-εn} ≤ e^{-n} (ε≥1), n>0 for Key |
| LGZero | 1 + 2/(m-2); 1/ε | min(0²/τ,0) = 0, so the integrand is independent of c (c ∈ ℝ arbitrary is fine) | m=3: 3; equality up to rounding at c=0 and ε=0 |
| LGTail | (1) e^{-εT}e^{-κ}T/(κ+εT) ≤ e^{-εT}T/κ; (2) same ≤ e^{-εT}/ε; head (1-e^{-εT})/ε ≤ min(T,1/ε) | denominator ε+κ/T > 0 in each form | e^{-κ} ≤ 1; measured max ratios 0.607, 1, 1 |
| LGConvA C | C(d,Λ) = 3+4dΛ²+2Λ²+2(1+Λ²)(1+2dΛ²) = 5+8dΛ²+4Λ²+4dΛ⁴ | (a) ε≥1 needs C ≥ max(3+4dΛ², 1+2Λ²); (b) ε<1 needs C ≥ 3(1+2dΛ²) if d≥1 (t>2/3), C ≥ 2(1+Λ²) if d=0 (t>1/(1+Λ²)) | d=3, Λ=1: C=45 vs needed ≤ 21, measured max ratio 0.399 (a), 0.399 (b) |
| LGConvA (b) steps | e<γ ≤ t g² ≤ g² so g²+e < 2g²; γ ≥ t g²/(1+2dΛ²) | d≥1: g²/(1+2dg²) ≤ 1/(2d) ≤ 1/2 ⇒ 1-t < t/2 ⇒ t>2/3 | d=0: 1-t < t g² ≤ tΛ² |
| LGConvB (a) | ε^{-1/2} = √(γ/e) ≤ g/√e (γ ≤ g²); ε ≥ L^{-2} ⇔ ε^{-1/2} ≤ L | ellT = min(max(g/√e,1),L) ≥ ε^{-1/2}; |1-t| = 1-t | measured max (ellT⁻¹)/√ε = 0.99999999950 ≤ 1 |
| LGConvB (b) | ε < L^{-2} ⇒ g/√e ≥ ε^{-1/2} > L ≥ 1 ⇒ ellT = L | strict, no equality case | 0 violations |
| LGConvC | n/ℓ ≤ n√ε ≤ (dL/2)√ε = (d/2)L√ε ≤ (d/2)εL² | L√ε ≥ 1 | measured max ratio 0.985; d=0 forces n=0 |

### (ii) Concrete nondegenerate instance and numeric check

Command (script is Python/numpy only; log-substitution Gauss-Legendre on [1e-14, 1e14] with crude analytic remainders added only at ε=0; ratios are LHS/bound, must be ≤ 1):

    python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2010_pre.py

Grid: LGKey and LGBulk (both regimes): m ∈ {3,4,5}, c ∈ {0.03,0.18,1}, n ∈ {1,2,5,20,100}, ε ∈ {0,1e-6,1e-3,0.1,0.5,1,2,10,100} (405 cases); LGZero: ε ∈ {0,0.01,1,10}, c ∈ {-1,0,1}; LGTail: T ∈ {0.5,9,100}, ε ∈ {0,0.01,1}, κ ∈ {0,0.5,16} (the form needed by each bullet); LGConvA/B/C: 200000 random (d ∈ 0..6, Λ ∈ [1e-2,1e2], g/Λ ∈ [1e-3,1], t or 1-t log-uniform down to 1e-6 resp. 1e-9, L ∈ 1..200, n ∈ [0,dL/2]).

Output (verbatim):

    Gamma(m/2-1), m=3,4,5: [1.7724538509055159, 1.0, 0.8862269254527578]
    C(m,c) c=0.18: [72.74, 1855.077, 71497.593] c'(c): [0.015, 0.09, 0.5]
    cases 405 max LGKey ratio LHS/RHS 0.707106781186549 max LGBulk(eps<=1) ratio 0.45398880824689475 max LGBulk(eps>=1) ratio 0.4925559698015313
    LGZero max ratio to 1+2/(m-2): 0.9999999999999961 ; to 1/eps: 0.9999944733639095
    LGTail max ratios (kappa>0 form, eps>0 form, head<=T, head<=1/eps): [0.6065306597126332, 1.0, 1.0000000000000002, 0.9999999999999901]
    ConvA/B/C samples 200000 violations (A_a,A_b,B_a,B_b,C): [0, 0, 0, 0, 0] max ratios A_a,A_b,B_a,C: 0.39946073004869975 0.3992155656330827 0.9999999994954173 0.9847609618869602
    lg_convB instance d=3,L=5,g=1/2,t=1/2: gamma 0.05 eps 10.0 L^-2 0.04 ellT 1.0 ellT^-1<=sqrt(eps): True
    alt regime-b data t=0.999: eps 0.010010010010010019 <L^-2: True ellT 5.0
    lg_convA d=3,Lam=1: C = 45.0 ; eps at g=.5,t=.5: 10.0

Instances to compile (hypotheses of each target hold at these numbers):
- lg_bulk 3 _ 0.18 _: m=3, c=0.18, C=72.74, c'=0.09; ranges n ≥ 1, ε ≥ 0 are inhabited (n=5, ε=0.5 measured ratio < 0.46).
- lg_zero 3 _ 1 0 le_rfl: c=1, ε=0; integral = 3 at c arbitrary, bound 1+2/(3-2) = 3 (nonvacuous: equality).
- lg_tail 9 _: T=9, all three clauses have inhabited ε, κ ranges (T=9 measured).
- lg_convA 3 1 one_pos: d=3, Λ=1, C=45; data g=1/2, t=1/2 gives γ=0.05, ε=10 ≥ 1 (clause a active, 1/e = 2 ≤ 45/(0.25+0.5) = 60); clause b needs ε<1, e.g. g=1/2, t=0.999 (ε ≈ 0.01).
- lg_convB 3 5 (1/2) (1/2): γ=0.05, ε=10, L⁻²=0.04, ellT=1: premise of (a) holds (1/ellT = 1 ≤ √10); premise of (b) fails, so (b) is a vacuous implication at these data. Nonvacuous (b): t=0.999, g=1/2, d=3, L=5: ε ≈ 0.01001 < 0.04, ellT = 5 = L.
- External hypotheses: none (the targets use only Mathlib and RBM.ellT); no limit computation needed.

### Verdicts
- LGKey: PASS. AM-GM plus Γ integral; exponent bookkeeping closes for all m ≥ 3; integrable at ε = 0 too (Gauss factor kills τ → 0, tail τ^{-m/2} integrable).
- LGBulk: PASS with C, c' of the table; the two branches use the same c'.
- LGZero: PASS (integrand independent of c; for ε = 0 the bound 1/ε is not asserted).
- LGTail: PASS (all clauses closed form via integral_exp_mul_Ioi; clause (1) divides by κ > 0, clause (2) by ε > 0).
- LGConvA: PASS with C = 5+8dΛ²+4Λ²+4dΛ⁴ (any C at least max(3+4dΛ², 1+2Λ², 3(1+2dΛ²), 2(1+Λ²)) also works).
- LGConvB: PASS.
- LGConvC: PASS (uses LGConvB (a) argument, ε > 0).
- Pin hazards (all benign): the ε ≤ 1 / ε ≥ 1 split of LGBulk is already in the pin; integrals over Ioi 0 only see τ > 0, so no junk value of τ^{-m/2} or n²/τ at τ ≤ 0 enters; Lean's x/0 = 0 does not occur since γ > 0 under g, t > 0.

## (b) Script output — 2026-10-03 00:36:25 UTC

Branch t/T2010, commit `c29212e`, sole file `RBM3D/Propagator/LaplaceGauss.lean` (`wc -l`:      895).

### Build

    $ touch RBM3D/Propagator/LaplaceGauss.lean; lake build RBM3D.Propagator.LaplaceGauss 2>&1 | grep -E "^(warning|error)|Build"
    warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
    Build completed successfully (2808 jobs).

    $ git diff --name-only main...t/T2010
    RBM3D/Propagator/LaplaceGauss.lean
    $ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Propagator/LaplaceGauss.lean; echo "exit $?"
    exit 1

### Axioms (`lake env lean ax.lean`, `#print axioms RBM.Heat.<t>`; scripts `ax.lean`, `extract.py`, `stmt.py`, `names2.lean` in the session scratchpad `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/`)

    'RBM.Heat.lg_key' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_convA' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_convB' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RBM.Heat.lg_convC' depends on axioms: [propext, Classical.choice, Quot.sound]

### Public declarations

    $ grep -E "^(noncomputable def|def|theorem) " RBM3D/Propagator/LaplaceGauss.lean | sed -E "s/^(noncomputable def|def|theorem) ([A-Za-z_0-9]+).*/\2/"
    lgIntegrand lgGam lgEps LGKey LGBulk LGZero LGTail LGConvA LGConvB LGConvC lg_convB lg_convC lg_convA lg_tail 
    lg_key lg_zero lg_bulk 
    private declarations: 23; examples: 17

### Target statements, extracted by script (`python3 extract.py`)

    theorem lg_key : ∀ m : ℕ, 3 ≤ m → ∀ c n ε : ℝ, 0 < c → 0 < n → 0 ≤ ε →
        IntegrableOn (fun τ : ℝ => τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)) (Ioi 0) ∧
        ∫ τ in Ioi (0 : ℝ), τ ^ (-(m : ℝ) / 2) * Real.exp (-ε * τ - c * n ^ 2 / τ)
          ≤ Real.Gamma ((m : ℝ) / 2 - 1) * (c / 2 * n ^ 2) ^ (-((m : ℝ) - 2) / 2)
              * Real.exp (-Real.sqrt (c * ε) * n) := …
    
    theorem lg_bulk : ∀ m : ℕ, 3 ≤ m → ∀ c : ℝ, 0 < c →
        ∃ C : ℝ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧
          ∀ n ε : ℝ, 1 ≤ n → 0 ≤ ε →
            IntegrableOn (lgIntegrand m c n ε) (Ioi 0) ∧
            (ε ≤ 1 → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ
                ≤ C * n ^ (-((m : ℝ) - 2)) * Real.exp (-c' * n * Real.sqrt ε)) ∧
            (1 ≤ ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c n ε τ ≤ 2 / ε * Real.exp (-c' * n)) := …
    
    theorem lg_zero : ∀ m : ℕ, 3 ≤ m → ∀ c ε : ℝ, 0 ≤ ε →
        IntegrableOn (lgIntegrand m c 0 ε) (Ioi 0) ∧
        ∫ τ in Ioi (0 : ℝ), lgIntegrand m c 0 ε τ ≤ 1 + 2 / ((m : ℝ) - 2) ∧
        (0 < ε → ∫ τ in Ioi (0 : ℝ), lgIntegrand m c 0 ε τ ≤ 1 / ε) := …
    
    theorem lg_tail : ∀ T : ℝ, 0 < T →
        (∀ ε κ : ℝ, 0 ≤ ε → 0 < κ →
          IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
          ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T) ≤ Real.exp (-ε * T) * (T / κ)) ∧
        (∀ ε κ : ℝ, 0 < ε → 0 ≤ κ →
          IntegrableOn (fun τ : ℝ => Real.exp (-ε * τ - κ * τ / T)) (Ioi T) ∧
          ∫ τ in Ioi T, Real.exp (-ε * τ - κ * τ / T) ≤ Real.exp (-ε * T) / ε) ∧
        (∀ ε : ℝ, 0 ≤ ε →
          ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ T ∧
          (0 < ε → ∫ τ in Ioc 0 T, Real.exp (-ε * τ) ≤ 1 / ε)) := …
    
    theorem lg_convA : ∀ (d : ℕ) (Λ : ℝ), 0 < Λ → ∃ C : ℝ, 0 < C ∧
        ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 < t → t < 1 →
          (1 ≤ lgEps d g t → 1 / (1 - t) ≤ C / (g ^ 2 + (1 - t))) ∧
          (lgEps d g t < 1 → 1 / lgGam d g t ≤ C / (g ^ 2 + (1 - t))) := …
    
    theorem lg_convB : ∀ (d L : ℕ) (g t : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 →
        (((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t → (ellT L g t)⁻¹ ≤ Real.sqrt (lgEps d g t)) ∧
        (lgEps d g t < ((L : ℝ)⁻¹) ^ 2 → ellT L g t = (L : ℝ)) := …
    
    theorem lg_convC : ∀ (d L : ℕ) (g t n : ℝ), 1 ≤ L → 0 < g → 0 < t → t < 1 → 0 ≤ n →
        n ≤ (d : ℝ) * (L : ℝ) / 2 → ((L : ℝ)⁻¹) ^ 2 ≤ lgEps d g t →
          n / ellT L g t ≤ (d : ℝ) / 2 * (lgEps d g t * (L : ℝ) ^ 2) := …

### Pin comparison (`python3 stmt.py`: whitespace-normalised pins of docs/tickets/checks/T2010-check.lean vs the file)

    noncomputable def lgIntegrand IDENTICAL
    noncomputable def lgGam IDENTICAL
    noncomputable def lgEps IDENTICAL
    LGKey pin body == theorem type: True | def in file == pin: True
    LGBulk pin body == theorem type: True | def in file == pin: True
    LGZero pin body == theorem type: True | def in file == pin: True
    LGTail pin body == theorem type: True | def in file == pin: True
    LGConvA pin body == theorem type: True | def in file == pin: True
    LGConvB pin body == theorem type: True | def in file == pin: True
    LGConvC pin body == theorem type: True | def in file == pin: True
    ALL OK

### Compiled nonempty instances (every `example` after the marker, docstrings and blank lines removed; all compile in the build above)

    $ sed -n '/^\/-! ### The theorems are the pinned/,$p' RBM3D/Propagator/LaplaceGauss.lean | grep -vE '^/--|^\s*$|^/-!|^`|^-/|^at |^`t|^example : LG|^end RBM'
    example := lg_key 3 (by norm_num) 1 1 (1 / 2) one_pos one_pos (by norm_num)
    example := lg_key 5 (by norm_num) 0.18 5 0 (by norm_num) (by norm_num) le_rfl
    example : ∃ C : ℝ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧
        IntegrableOn (lgIntegrand 3 0.18 5 (1 / 2)) (Ioi 0) ∧
        (∫ τ in Ioi (0 : ℝ), lgIntegrand 3 0.18 5 (1 / 2) τ
          ≤ C * (5 : ℝ) ^ (-(((3 : ℕ) : ℝ) - 2)) * Real.exp (-c' * 5 * Real.sqrt (1 / 2))) ∧
        (∫ τ in Ioi (0 : ℝ), lgIntegrand 3 0.18 2 2 τ ≤ 2 / 2 * Real.exp (-c' * 2)) := by
      obtain ⟨C, hC, c', hc', h⟩ := lg_bulk 3 (by norm_num) 0.18 (by norm_num)
      obtain ⟨h1, h2, -⟩ := h 5 (1 / 2) (by norm_num) (by norm_num)
      obtain ⟨-, -, h3⟩ := h 2 2 (by norm_num) (by norm_num)
      exact ⟨C, hC, c', hc', h1, h2 (by norm_num), h3 (by norm_num)⟩
    example := lg_zero 3 (by norm_num) 1 0 le_rfl
    example : ∫ τ in Ioi (0 : ℝ), lgIntegrand 3 1 0 1 τ ≤ 1 / 1 :=
      (lg_zero 3 (by norm_num) 1 1 zero_le_one).2.2 one_pos
    example : (IntegrableOn (fun τ : ℝ => Real.exp (-(1 / 2 : ℝ) * τ - 16 * τ / 9)) (Ioi 9) ∧
          ∫ τ in Ioi (9 : ℝ), Real.exp (-(1 / 2 : ℝ) * τ - 16 * τ / 9)
            ≤ Real.exp (-(1 / 2 : ℝ) * 9) * (9 / 16)) ∧
        (IntegrableOn (fun τ : ℝ => Real.exp (-(1 / 2 : ℝ) * τ - (1 / 2) * τ / 9)) (Ioi 9) ∧
          ∫ τ in Ioi (9 : ℝ), Real.exp (-(1 / 2 : ℝ) * τ - (1 / 2) * τ / 9)
            ≤ Real.exp (-(1 / 2 : ℝ) * 9) / (1 / 2)) ∧
        (∫ τ in Ioc (0 : ℝ) 9, Real.exp (-(1 / 2 : ℝ) * τ) ≤ 9 ∧
          ∫ τ in Ioc (0 : ℝ) 9, Real.exp (-(1 / 2 : ℝ) * τ) ≤ 1 / (1 / 2)) := by
      obtain ⟨h1, h2, h3⟩ := lg_tail 9 (by norm_num)
      exact ⟨h1 (1 / 2) 16 (by norm_num) (by norm_num), h2 (1 / 2) (1 / 2) (by norm_num) (by norm_num),
        (h3 (1 / 2) (by norm_num)).1, (h3 (1 / 2) (by norm_num)).2 (by norm_num)⟩
    example : ∃ C : ℝ, 0 < C ∧
        1 / (1 - (1 / 2 : ℝ)) ≤ C / ((1 / 2 : ℝ) ^ 2 + (1 - 1 / 2)) ∧
        1 / lgGam 3 (1 / 2) 0.999 ≤ C / ((1 / 2 : ℝ) ^ 2 + (1 - 0.999)) := by
      obtain ⟨C, hC, h⟩ := lg_convA 3 1 one_pos
      refine ⟨C, hC, ?_, ?_⟩
      · exact (h (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
          (by norm_num [lgEps, lgGam])
      · exact (h (1 / 2) 0.999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
          (by norm_num [lgEps, lgGam])
    example : (ellT 5 (1 / 2) (1 / 2))⁻¹ ≤ Real.sqrt (lgEps 3 (1 / 2) (1 / 2)) :=
      (lg_convB 3 5 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
        (by norm_num [lgEps, lgGam])
    example : ellT 5 (1 / 2) 0.999 = (5 : ℕ) :=
      (lg_convB 3 5 (1 / 2) 0.999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
        (by norm_num [lgEps, lgGam])
    example : (7 : ℝ) / ellT 5 (1 / 2) (1 / 2)
        ≤ ((3 : ℕ) : ℝ) / 2 * (lgEps 3 (1 / 2) (1 / 2) * ((5 : ℕ) : ℝ) ^ 2) :=
      lg_convC 3 5 (1 / 2) (1 / 2) 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [lgEps, lgGam])

### Instances (continued): the type-identity checks and name clashes

    $ grep -n "^example : LG" RBM3D/Propagator/LaplaceGauss.lean
    820:example : LGKey := lg_key
    821:example : LGBulk := lg_bulk
    822:example : LGZero := lg_zero
    823:example : LGTail := lg_tail
    824:example : LGConvA := lg_convA
    825:example : LGConvB := lg_convB
    826:example : LGConvC := lg_convC

### Name-clash grep of the 17 new public names (`PUB` = `lgIntegrand|lgGam|lgEps|LGKey|…|lg_bulk`; refs: `main`, `t/T2009` at c9fd239, all other `t/*`)

    $ git grep -nwE "$PUB" main -- RBM3D RBM3D.lean | wc -l
    0
    $ git grep -nwE "$PUB" t/T2009 -- RBM3D RBM3D.lean | wc -l
    0
    $ for b in $(git branch --format="%(refname:short)" | grep "^t/" | grep -v T2010); do git grep -lwE "$PUB" $b -- RBM3D RBM3D.lean; done | wc -l
    0
    ports: none (no RBM1D/RBM2D text copied; the RBM1D/RBM2D diff-stat is not applicable)

### Narrative (≤ 40 lines)

- No hypothesis added, no pin changed, no frozen signature touched; `LaplaceGauss.lean` is the only file in `git diff --name-only main...t/T2010`. The seven `LG*` Props and `lgIntegrand/lgGam/lgEps` are in the file with the pinned text (script comparison above); each `lg_*` theorem is stated with the pin body, and `example : LGX := lg_x` checks the two types agree.
- `lg_key`: AM–GM `lg_amgm` (`√(cε)n ≤ ετ + (c/2)n²/τ` via `(pτ)² + (pτ − qn)² ≥ 0`), pointwise domination by `e^{-√(cε)n}·τ^{-m/2}e^{-(c/2)n²/τ}`, then `lg_inv_gamma`: `integral_comp_rpow_Ioi` with `p = -1` and `integral_rpow_mul_exp_neg_mul_rpow` with `p = 1`, `q = m/2 − 2 > −1`.
- `lg_bulk`: `m = k + 2`; split `Ioi 0 = Ioc 0 n ∪ Ioi n` (`lg_bulk_split`); head `≤ e^{-cn}∫_{(0,n]}e^{-ετ}` (`lg_bulk_head`); tail through `lg_key` (`lg_bulk_tail_key`) for `ε ≤ 1`, or `≤ e^{-εn}/ε` from `lg_tail` with `κ = 0` (`lg_bulk_tail_exp`) for `ε ≥ 1`.
- Constants as in the file: `c' = min (c/2) 1`; `C = C1 + C2` with `C1 = (m−1)!·(2/c)^{m−1}` (the larger constant `C1'` that section (a) lists as valid, not the supremum `C1`) and `C2 = Γ(m/2−1)·(c/2)^{-(m−2)/2}`; the `ε ≤ 1` step uses `n^{k+1}e^{-(c/2)n} ≤ (k+1)!(2/c)^{k+1}` (`Real.pow_div_factorial_le_exp`), `c' ≤ c/2`, `c' ≤ √c`, `√ε ≤ 1`; the `ε ≥ 1` step uses `c' ≤ c`, `c' ≤ 1`, `εn ≥ n`.
- `lg_zero` is proved for every real `c` (also `c ≤ 0`): at `n = 0` the integrand does not depend on `c`, so the proof rewrites `lgIntegrand m c 0 ε = lgIntegrand m 0 0 ε`.
- `lg_convA`: `C = 3 + 4dΛ² + 2Λ²`, smaller than the `C` of section (a)'s table (`5 + 8dΛ² + 4Λ² + 4dΛ⁴`); (a) is not wrong, its `C` is only sufficient. Regime `ε ≥ 1`: `tg² ≤ s·e` (`s = 1 + 2dg²`), cases `t ≥ 1/2` / `t < 1/2`. Regime `ε < 1`: `s·e < t g²` gives `s < t(s + g²)`, hence `s(g² + e) ≤ t g²(s + g² + 1) ≤ C t g²`, with no `d ≥ 1` / `d = 0` case split.
- `lg_convB/C`: `ε^{-1/2} ≤ g/√e` (from `γ ≤ g²`), `ε ≥ L^{-2} ⇒ ε^{-1/2} ≤ L`; hence `ℓ_t⁻¹ ≤ √ε` (`lg_ell_inv_le`), `ℓ_t = L` when `ε < L^{-2}`, and `n/ℓ_t ≤ n√ε ≤ (d/2)(L√ε)² = (d/2)εL²`.
- Instances: `lg_convB 3 5 (1/2) (1/2)` has `ε = 10 ≥ L^{-2} = 0.04`, so clause (a) is the active one there; clause (b) is exercised at `t = 0.999` (`ε < L^{-2}`, `ℓ_t = 5`). `lg_convA 3 1` is applied at `t = 1/2` (`ε = 10 ≥ 1`) and `t = 0.999` (`ε < 1`); `lg_zero` clause 3 at `ε = 1`.
- One import beyond the ticket's list: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, which declares `integrableOn_rpow_mul_exp_neg_mul_rpow`; with the ticket's imports the name was unknown (first `lake env lean` run). The ticket allows added Mathlib imports.
- The one linter warning (line 36, > 100 characters) is the docstring of `lgEps`, kept verbatim from the check file; section (a) was not edited and needs no (a′).

## (c) Verified Mathlib names (script: `#chk` over the open namespaces of the file, all "present" unless listed absent)

Present, each used in the file: `Real.pow_div_factorial_le_exp`; `Set.Ioc_union_Ioi_eq_Ioi`, `Set.Ioc_disjoint_Ioi_same`; `MeasureTheory.setIntegral_union`, `.setIntegral_mono_set`, `.setIntegral_mono_on`, `.setIntegral_const`, `.integral_const_mul`, `.integral_mul_const`, `.Integrable.mono'`, `.IntegrableOn.congr_fun`, `.IntegrableOn.union`, `.integral_comp_rpow_Ioi`, `.integrableOn_Ioi_comp_rpow_iff`; root-level `integrableOn_rpow_mul_exp_neg_mul_rpow` (import `Gaussian.GaussianIntegral`), `integral_rpow_mul_exp_neg_mul_rpow`, `integral_exp_mul_Ioi`, `integrableOn_exp_mul_Ioi`, `integrableOn_Ioi_rpow_of_lt`, `integral_Ioi_rpow_of_lt`; `Continuous.integrableOn_Ioc`; `Real.Gamma_pos_of_pos`, `Real.sqrt_lt'`, `Real.le_sqrt`, `Real.sqrt_le_sqrt`, `Real.sqrt_le_one`, `Real.sqrt_mul`, `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.rpow_le_rpow_of_exponent_le`, `Real.volume_real_Ioc`, `Real.inv_rpow`, `Real.rpow_neg_one`, `Real.rpow_natCast`, `Real.mul_rpow`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_neg`; `inv_le_comm₀`, `lt_inv_comm₀`, `one_div_le_one_div_of_le`, `div_le_div_iff₀`, `div_le_iff₀`, `le_div_iff₀`, `lt_div_iff₀`, `div_lt_one`, `div_eq_div_iff`.
Verified absent: `Real.integrableOn_rpow_mul_exp_neg_mul_rpow`, `Real.integral_rpow_mul_exp_neg_mul_rpow` (the names are root-level); `integrableOn_rpow_mul_exp_neg_mul_rpow` is not visible from the three Mathlib imports of the ticket's list.

## (d) Open issues and paper-delta candidates

- No obstruction; all seven targets proved as pinned; no `sorry`; axioms are the three standard ones.
- **T2010a** (proof-internal, route correction, not a paper correction): Fable's (L1) first bound `≲ n^{-(m-2)}e^{-c'n√ε}` for all `ε ≥ 0` is replaced by `lg_bulk`: that form for `ε ≤ 1` and `(2/ε)e^{-c'n}` for `ε ≥ 1`, as the ticket (line 8) records (`n = 1`: the integral is `≥ e^{-c}(1 − e^{-ε})/ε`); Lean proves the split form.
- No other Lean/paper statement difference: the file contains no statement taken from the paper beyond the pins.
