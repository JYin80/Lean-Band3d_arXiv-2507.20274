Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 02:38:22 UTC 2026

Notation: `g = sz.lam n`, `L = sz.L n ≥ 3`, `d ≥ 3`; cuts `c₁ = 1-g²`, `c₂ = 1-g²/L²`, `c₃ = 1-g²/L^d`; regimes as merged (`Step5Pins.lean:44-63`): (iii) `g² ≤ 1-t` i.e. `t ≤ c₁`; (i) `s ≥ c₁ ∧ t ≤ c₂`; (ii) `s ≥ c₂ ∧ t ≤ c₃`; (iv) `s ≥ c₃`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠_d` of `ST_mainIndR_of_steps` | `min c₂ (c₃ c₄ c₅ c₆)`; `C_d` from `STStep2` first (`∃ Cd ∃ c₂`), then `c₃,c₄,c₅` (`∀ Cd ∃ c`, `Step34Pins:250,261`, `Step5Pins:82`), `c₆`, Step 1 independent of `C_d` | `0 < · ≤ 1/100`; Step 1 needs every `𝔠d ∈ (0,1/100]` | `· ≤ c₂ ≤ 1/100`; `> 0` finite min |
| 2 | `𝔠_d` of `ST_mainIndR_seq` | `min c₁ c₂` | `STConStInd (min) s t` ⇒ `[s,m]`, `[m,t]` (`st_conStInd_sub`: `s ≤ s'<t' ≤ t < 1`, `ScaleFacts3:478`) ⇒ `c_i` (`st5_conStInd_mono`: smaller exponent is stronger, `t<1`, `0<c`) | `[m,t]`: `(1-t)/(1-m) ≥ (1-t)/(1-s)`; `[s,m]`: `B_m ≤ B_t` (`STBctl_mono`) |
| 3 | global `𝔠_d*` of `ST_mainInd_of_regimes` | min of the 4 regime constants (chain directly; each pattern constant `c_P` = min over its stages, `c_P ≥ 𝔠_d*`) | `STConStInd 𝔠_d*` ⇒ `STConStInd c_P` by mono, `0 < 𝔠_d* ≤ 1/100` | one `𝔠_d*` for all 10 patterns |
| 4 | cut order | `c₁ ≤ c₂ ≤ c₃ ≤ 1` for all `g`; strict iff `g ≠ 0` | `c₂-c₁ = g²(1-L⁻²) ≥ (8/9)g²` (`L ≥ 3`); `c₃-c₂ = g²(L⁻²-L^{-d}) > 0` (`d ≥ 3`, `L ≥ 3`; only positivity, no uniform gap) | `i<j ⇒ g ≠ 0` (else `c_k=1 > t`, `t<1`) |
| 5 | intermediate times | pattern `(i,j)`: `m_k = c_k`, `k = i+1..j` | `s < c_{i+1}` (stage of `s` is `i`), `c_j < t` (stage of `t` is `j`), `c_{i+1}<…<c_j` (row 4) | strict; `0 ≤ s < m`, `m < t ≤ lemT z` |
| 6 | regime at a cut | stage `k` on `[c_k, c_{k+1}]` | closed regimes: `s ≥ c_k`, `t ≤ c_{k+1}` | slack `0` (equality at the cut), `<`/`≤` of the classifier excludes point-stages |
| 7 | `d` thresholds | `3 ≤ d` all pins; `2 ≤ d` for `st_caseII_of_reg5IV` | `g²/L^d ≤ g²/L²` needs `L^d ≥ L²`; `g²/L² ≤ g²` needs `L² ≥ 1`; `L ≥ 3` is `three_le_L` | `L² ≥ 9` |
| 8 | `t < 1` | `t ≤ lemT z < 1` (`lemT_lt_one`, `Semicircle:209`; `st5_t_lt_one`) | `st_conStInd_sub`, `st5_conStInd_mono` | `zB`: `lemT = 0.98399` vs `31/32`: 0.0152; vs `49/50`: 0.0040 |
| 9 | bridge exponent `θ` | `θ = 1/2`: `(‖x‖²)^{1/2} = ‖x‖`; `STWB … K ≤ Bctl` (`LocalAvg1:94`, `((K+1)^{d-2})⁻¹ ≤ 1`) | `iterationsA_prec_rpow` (`IterationsA:850`) needs `0 ≤ ξ, ζ`, `θ>0`; `Bctl ≥ 0` (inverses of nonnegatives) | loss `0` (no `N^τ` loss, none in `τ`) |
| 10 | Step-6 decay input | `STGdecayW … 0` (loss `((1-s)/(1-u))^{C_d}` absent, `C_d = 0`) | from Step 5 conclusion `hS5.1`; `STStep2Core` = first two conjuncts of `STStep2Concl` | none of `((1-s)/(1-s'))^{C_d}`, `(L^d/4)^{k-1}` enters the chain (each stage reruns Steps 1-2 from its start) |
| 11 | patterns | `(i,j)`, `i ≤ j` ⇒ 10 of 16; classifier `ℕ → Fin 4 × Fin 4`, cover index `{p // class infinite}` finite | `i>j` empty: `s ≥ c_i`, `t ≤ c_{j+1} ≤ c_i ≤ s` contradicts `s<t` (`i ≥ 1`, `j<i`) | stage counts: 4 single, 3 pairs, 2 triples, 1 quadruple |
| 12 | cover transfer | 7 predicates, `sz.comp φ` vs `sz` at `φ j` | `rfl` for `Lloop_reindex`, `STKloop_comp`, `Bctl_comp`, `STGM_reindex`, `STWB_comp`, `STblk_comp`, `ellT_comp` (`SizesComp:285-305`); `STExp2`: `integral_Lloop_reindex` (`:314`, pattern `sizesComp_STExp2_comp :683`) | `StrictMono φ ⇒ Tendsto φ atTop atTop` for `STFlow_comp`, `STConStInd_comp` |

Registry (text count of list entries by script over `RBM3D/Test/Axioms.lean`): borrowed 2, owed 154, structural 91, refuted 7; the six names `STStep3, STStep4, STStep5, STStep6, STExpIniI, STExpIntI` are all in `owedProps`; `STRegSeq` in `structuralProps`, `STMainIndR` in none. After: owed 148, structural 92, superseded 6.
Successor check (`grep -rn "STStep3R'\|STStep4R'\|STStep3I'\|STStep3II'\|STStep4I'\|STStep4II'" RBM3D`): no output, exit 1.

### (ii) Concrete instance

Data: `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, flow `(szB, zB)` (merged `flow_zB`, `Step34Pins:785`; `lemT zB ≥ 31/32` merged `lemT_zB`; `lemT zB ≥ 49/50` is probe-only `t/T2191` `lemT_zB_hi`). Chain data: `R₁ = STReg5I`, `R₂ = STReg5II`, `(s,t) = (7/8, 31/32)`, `m = 15/16`; 3-stage data `(szFour, 0, 31/32)`. Hypotheses: `0 ≤ s < m < t ≤ lemT`, regimes, `(con_st_ind)` (eventual: `Bctl → 0`, merged `conStInd_const`, `Step34Pins:825`, every `𝔠_d > 0` at constant times `s<t<1`). No external hypothesis occurs. Command (Python, no Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2245/final.py`

```
== (i) 16 cells (s-stage row, t-stage column): exact-Fraction grid search, bad=#(i>j or failed regime/strict-order check)
bad = 0
 s-stage iii ['g,L,d,s,t=0,3,3,0,1/64', 'g,L,d,s,t=1/5,3,3,0,961/1000', 'g,L,d,s,t=1/5,3,3,0,8969/9000', 'g,L,d,s,t=1/5,3,3,0,26987/27000']
 s-stage i   ['EMPTY', 'g,L,d,s,t=1/5,3,3,24/25,961/1000', 'g,L,d,s,t=1/5,3,3,24/25,8969/9000', 'g,L,d,s,t=1/5,3,3,24/25,26987/27000']
 s-stage ii  ['EMPTY', 'EMPTY', 'g,L,d,s,t=1/5,3,3,224/225,8969/9000', 'g,L,d,s,t=1/5,3,3,224/225,26987/27000']
 s-stage iv  ['EMPTY', 'EMPTY', 'EMPTY', 'g,L,d,s,t=1/5,3,3,674/675,26987/27000']
== g=0 row (L=3,d=3): all cuts = (Fraction(1, 1), Fraction(1, 1), Fraction(1, 1)) ; patterns: [('iii', 'iii'), ('iii', 'iii'), ('iii', 'iii')]
== g=5/4 row (L=3,d=3): cuts ['-9/16', '119/144', '407/432'] c1<0; stage lists [['i'], ['i', 'ii', 'iv']]
== sizes at the five (s,t), pattern at n=0 [same for n=1,5 where n varies]; cuts at n=0
  szB cuts ['0', '15/16', '63/64'] ['(i,ii)', '(i,i)', '(ii,ii)', '(i,i)', '(i,i)']
  szG cuts ['-24', '-9/16', '39/64'] ['(ii,iv)', '(iv,iv)', '(iv,iv)', '(iv,iv)', '(ii,ii)']
  szFour cuts ['9/25', '209/225', '659/675'] ['(iii,iv)', '(i,ii)', '(ii,ii)', '(i,i)', '(iii,iii)']
  sz0 cuts ['4095/4096', '65535/65536', '0.999996'] ['(iii,iii)', '(iii,iii)', '(iii,iii)', '(iii,iii)', '(iii,iii)']
== lemT(zB), zB=1/2+i/64: 0.9839922868819404 >= 31/32 (merged lemT_zB); >= 49/50 only numerically
== instance for ST_mainIndR_seq / ST_mainInd_of_regimes data (d=3, kappa=eps=dd=1/10, c=1/6, flow zB; every t <= 31/32 <= lemT zB)
  szB (L=4,g=1,W=n+4) (s,t)=(7/8,31/32) stages=['i', 'ii'] times=['7/8', '15/16', '31/32'] ok=True
     [7/8,15/16] ratio=1/2  log10 W_thr(c_d=1/100)=10.06
     [15/16,31/32] ratio=1/2  log10 W_thr(c_d=1/100)=10.09
     [7/8,31/32] ratio=1/4  log10 W_thr(c_d=1/100)=20.12
  szFour (L=3,g=4/5,W=n+6) (s,t)=(0,31/32) stages=['iii', 'i', 'ii'] times=['0', '9/25', '209/225', '31/32'] ok=True
     [0,9/25] ratio=16/25  log10 W_thr(c_d=1/100)=6.44
     [9/25,209/225] ratio=1/9  log10 W_thr(c_d=1/100)=31.90
     [209/225,31/32] ratio=225/512  log10 W_thr(c_d=1/100)=12.05
     [0,31/32] ratio=1/32  log10 W_thr(c_d=1/100)=50.31
== classes (n even g=1, n odd g=2/5, L=4,d=3) at (0,49/50): [(0, 'i', 'ii'), (1, 'iii', 'i'), (2, 'i', 'ii'), (3, 'iii', 'i')]
```

`Bctl` thresholds: the table's `log10 W_thr` is where `(Bctl)^{1/100} ≤ ratio` starts for `W_n = n+4` (resp. `n+6`); `(con_st_ind)` is `∀ᶠ n`, discharged by the limit `Bctl → 0` (`conStInd_const`), not by a witness `n`. The thresholds are large because `𝔠_d ≤ 1/100` (a smaller exponent is the stronger hypothesis) and the thresholds of the pieces are below those of the whole interval (`st_conStInd_sub` direction). Class glue (target 5/6): the last printed line is a two-class example (`n` even/odd), both classes infinite, `φ_r = Nat.nth (· = r)` strictly monotone, covering all `n`.

### Findings (not FAIL)
1. **Target 4 route.** `StochDomAt.trans` needs `Tendsto size atTop atTop` (`StochDomAt.lean:411-412`), while the pin `STLocalMax_of_STLocalEntry` (∀ `d sz E τ`) has no size hypothesis. The statement is true without it: `‖G-M‖² ≺ STWB(K)` and `STWB(K) ≤ Bctl` pointwise give `‖G-M‖² ≺ Bctl` because the bad set `{N^τ·Bctl < ξ} ⊆ {N^τ·STWB < ξ}` (`N^τ ≥ 0`), i.e. `StochDomAt.of_subset` (`:325`) with `τ' = τ`; then `iterationsA_prec_rpow` (no size hypothesis). The ticket's "`prec_of_le`/`StochDomAt.trans`" must not be used as is. (`of_le_left`, `:347`, is monotone in `ξ`, not `ζ`.)
2. **Data.** The ticket's pair `(0, 49/50)` needs `49/50 ≤ lemT zB`, merged only as `31/32`; the Prop-only instances (5, 7, 8) do not use it; the compiled-hypothesis data above stay below `31/32`.
3. Paper-delta candidates as in the ticket (`T2245a`: whole-induction step per cut, composition of single-time conclusions; `T2245b`: `(Gt_bound+IND)` of the next stage from `(Gt_bound)`): consistent with (i).

### Verdicts
- Target 1 (`STMainIndR`, `ST_mainInd_iff_any`, `STMainIndR_mono`): PASS (bodies agree up to `True →`; mono direction `R' ⊆ R`).
- Target 2 (four alignments): PASS (rows 4, 7).
- Target 3 (generic step, four regimes): PASS (row 1; each regime pair of Steps 3/4/5/6 matches the four `ST_mainIndR_*_of_steps` pins; `R ⊆ R34` from target 2, `2 ≤ d` from `3 ≤ d`).
- Target 4 (`STLocalMax_of_STLocalEntry`, `ST_mainIndR_seq`): PASS (rows 2, 5, 8, 9; use finding 1).
- Target 5 (seven cover transfers): PASS (row 12).
- Target 6 (`ST_mainInd_of_regimes`, 10 patterns): PASS (rows 3-6, 11 and the table above: 10 cells nonempty, 6 empty, `bad = 0`).
- Target 7 (`ST_mainInd_of_pins`): PASS (owed pins: `STStep2, 3I, 3II, 4I, 4II, 5I, 5II, 6I, 6II, 6III`; `STStep1, 5III, 5IV, 6IV` discharged by `stStep1_holds`, `stStep5III_holds`, `stStep5IV_holds`, `stStep6IV_holds`).
- Registry items (1)-(4): PASS (rows above).
Overall verdict: PASS.

### (a′) Preflight corrections — Tue Oct  6 03:00:24 UTC 2026
1. (a) Registry line "After: owed 148, structural 92, superseded 6": measured after = owed 148, structural 93, superseded 6. The scan reports `RBM.Gauss.Sizes.STStep5R` (a hypothesis of the pinned `ST_mainIndR_of_steps`, in none of the five lists) as unregistered; I registered it as structural, as `STStep6R` (Registry item (3) names only `STMainIndR`). Pre-check with the new module and the registry of `main` (command: `lake env lean precheck_before.lean`, exit 1):
```
precheck_before.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this developm
  [RBM.Gauss.Sizes.STStep5R]
```
2. (a) did not predict that `STLocalMax` and `STMainInd` leave the scan's found set (a theorem now concludes each: `STLocalMax_of_STLocalEntry`, `ST_mainInd_of_regimes`); they stay in `owedProps` and are reported as "carry nothing yet". No verdict of (a) changes (owed -6, superseded 6, `STRegSeq` structural all hold).

## (b) Script output

Targets 1-7: statements extracted by script (`python3 stmts.py <names>`, line number in `RBM3D/Induction/MainIndRegimes.lean`, signature up to `:=`; the seven cover statements share the signature of the first, only the conclusion is printed).
```
92: theorem ST_mainInd_iff_any (d : ℕ) : STMainInd d ↔ STMainIndR d STAny
105: theorem STMainIndR_mono (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STMainIndR d R) : STMainIndR d R'
125: theorem st_caseI_of_reg5III (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5III sz s t) : STCaseI sz s t
137: theorem st_caseI_of_reg5I (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5I sz s t) : STCaseI sz s t
141: theorem st_caseII_of_reg5II (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5II sz s t) : STCaseII sz s t
145: theorem st_caseII_of_reg5IV (d : ℕ) (hd : 2 ≤ d) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5IV sz s t) : STCaseII sz s t
165: theorem ST_mainIndR_of_steps (d : ℕ) (R R34 : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (hR : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3R d R34) (h4 : STStep4R d R34) (h5 : STStep5R d R) (h6 : STStep6R d R) : STMainIndR d R
217: theorem ST_mainIndR_III_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3I d) (h4 : STStep4I d) (h5 : STStep5III d) (h6 : STStep6III d) : STMainIndR d STReg5III
222: theorem ST_mainIndR_I_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3I d) (h4 : STStep4I d) (h5 : STStep5I d) (h6 : STStep6I d) : STMainIndR d STReg5I
227: theorem ST_mainIndR_II_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3II d) (h4 : STStep4II d) (h5 : STStep5II d) (h6 : STStep6II d) : STMainIndR d STReg5II
232: theorem ST_mainIndR_IV_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3II d) (h4 : STStep4II d) (h5 : STStep5IV d) (h6 : STStep6IV d) : STMainIndR d STReg5IV
244: theorem STLocalMax_of_STLocalEntry (d : ℕ) (sz : Sizes d) (E τ : ℕ → ℝ) (h : STLocalEntry sz E τ) : STLocalMax sz E τ
289: theorem ST_mainIndR_seq (d : ℕ) (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h₁ : STMainIndR d R₁) (h₂ : STMainIndR d R₂) : STMainIndR d (STRegSeq R₁ R₂)
311: theorem STLK_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) : STLK sz E τ ↔ ∀ k, STLK (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
321: theorem STLmax_iff_comp_cover (same signature as above): STLmax sz E τ ↔ ∀ k, STLmax (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
331: theorem STDecay_iff_comp_cover (same signature as above): STDecay sz E τ ↔ ∀ k, STDecay (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
341: theorem STDecayStrong_iff_comp_cover (same signature as above): STDecayStrong sz E τ ↔ ∀ k, STDecayStrong (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
352: theorem STLocalMax_iff_comp_cover (same signature as above): STLocalMax sz E τ ↔ ∀ k, STLocalMax (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
363: theorem STLocalEntry_iff_comp_cover (same signature as above): STLocalEntry sz E τ ↔ ∀ k, STLocalEntry (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
374: theorem STExp2_iff_comp_cover (same signature as above): STExp2 sz E τ ↔ ∀ k, STExp2 (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j))
616: theorem ST_mainInd_of_regimes (d : ℕ) (h₀ : STMainIndR d STReg5III) (h₁ : STMainIndR d STReg5I) (h₂ : STMainIndR d STReg5II) (h₃ : STMainIndR d STReg5IV) : STMainInd d
674: theorem ST_mainInd_of_pins (d : ℕ) (h2 : STStep2 d) (h3I : STStep3I d) (h3II : STStep3II d) (h4I : STStep4I d) (h4II : STStep4II d) (h5I : STStep5I d) (h5II : STStep5II d) (h6I : STStep6I d) (h6II : STStep6II d) (h6III : STStep6III d) : STMainInd d
```
Target 1 body of `STMainIndR` (`sed -n '64,75p'`):
```
def STMainIndR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) → R sz s t →
          (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
            STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
          STConStInd sz 𝔠d s t →
          STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
            STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
            STDecayStrong sz (STflowE z) t
```
Instances (statements; the eight pinned ones are the check-file section 4 statements, proved by the instance of the same name; the extras apply targets 3, 4, 6, 7 at data):
```
702: theorem inst_caseI_III : STCaseI sz0 sInst tInst
705: theorem inst_caseI_I : STCaseI szB (fun _ => 7 / 8) (fun _ => 15 / 16)
709: theorem inst_caseII_II : STCaseII szB (fun _ => 15 / 16) (fun _ => 31 / 32)
713: theorem inst_caseII_IV : STCaseII szG (fun _ => 5 / 8) (fun _ => 3 / 4)
718: theorem inst_regSeq_szB : STRegSeq STReg5I STReg5II szB (fun _ => 0) (fun _ => 49 / 50)
724: theorem inst_localMax_sz0 : STLocalEntry sz0 (STflowE z0) sInst → STLocalMax sz0 (STflowE z0) sInst
729: theorem inst_regimes3 : STMainIndR 3 STReg5III → STMainIndR 3 STReg5I → STMainIndR 3 STReg5II → STMainIndR 3 STReg5IV → STMainInd 3
735: theorem inst_mainInd3 : STStep2 3 → STStep3I 3 → STStep3II 3 → STStep4I 3 → STStep4II 3 → STStep5I 3 → STStep5II 3 → STStep6I 3 → STStep6II 3 → STStep6III 3 → STMainInd 3
744: theorem inst_pattern_szB (n : ℕ) : STPattern szB (fun _ => 0) (fun _ => 49 / 50) n = ((1 : Fin 4), (2 : Fin 4))
756: theorem inst_chain_szB : STRegChain 1 1 (szB.comp id) (fun j => (fun _ => (0 : ℝ)) (id j)) (fun j => (fun _ => (49 / 50 : ℝ)) (id j))
851: theorem inst_mainIndR_seq (hI : STMainIndR 3 STReg5I) (hII : STMainIndR 3 STReg5II) : InstMainIndRConcl (STRegSeq STReg5I STReg5II) szB zB (fun _ => 7 / 8) (fun _ => 31 / 32)
892: theorem inst_mainInd3_data (h2 : STStep2 3) (h3I : STStep3I 3) (h3II : STStep3II 3) (h4I : STStep4I 3) (h4II : STStep4II 3) (h5I : STStep5I 3) (h5II : STStep5II 3) (h6I : STStep6I 3) (h6II : STStep6II 3) (h6III : STStep6III 3) : InstMainIndRConcl STAny sz
```
Extra instances not shown: `inst_STLK_iff` .. `inst_STExp2_iff` (target 5, `sz0` along the two parity classes, `ι = Fin 2`), `inst_mono_I` (target 1), `inst_steps_III/I/II/IV` (target 3 at the four data), `inst_mainIndR` (helper).
```
$ date -u; git log --oneline -3; git status --short
Tue Oct  6 02:59:45 UTC 2026
12d8feb T2245: registry supersededProps, STMainIndR/STStep5R structural, comment updates (DECISIONS 76 (3))
307a098 T2245: MainIndRegimes (main-induction regime assembly, targets 1-7, instances)
389ad9e T2240: merge MA-05a Main/QUECore
$ lake build RBM3D.Induction.MainIndRegimes 2>&1 | grep -E "MainIndRegimes|Build completed"
Build completed successfully (3905 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/MainIndRegimes.lean; wc -l RBM3D/Induction/MainIndRegimes.lean
grep exit=1
     901 RBM3D/Induction/MainIndRegimes.lean
$ git diff --stat main...t/T2245
 RBM3D/Induction/MainIndRegimes.lean | 901 ++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean              |  75 ++-
 2 files changed, 951 insertions(+), 25 deletions(-)
$ #print axioms of all 67 public declarations (axioms.lean): lines / standard-3 / no-axiom; distinct axiom sets of the 22 targets
      67
67
0
  22 [propext, Classical.choice, Quot.sound]

## check-file equality (scratch = T2245-check.lean sections 1-3 + import RBM3D.Induction.MainIndRegimes + 1 rfl + 22 pin examples; python mkcheck.py)
$ lake env lean check_eq.lean > check_eq.out 2>&1; echo exit=$?; grep -c error check_eq.out; tail -1 check_eq.out
exit=0
0
22
$ grep -c "^example" check_eq.lean
23
$ lake env lean check_inst.lean   (the 8 section-4 statements of the check file, each proved by the named instance)
exit=0
0
8

## name clash: the 67 new public names against RBM3D (other files), RBM1D, RBM2D
new public names: 67 ; occurring in another RBM3D file: [('STMainIndR', ['RBM3D/Test/Axioms.lean']), ('ST_mainIndR_of_steps', ['RBM3D/Test/Axioms.lean']), ('ST_mainInd_of_regimes', ['RBM3D/Test/Axioms.lean'])]
occurrences in ../RBM2D/RBM2D, ../RBM1D/RBM1D: 0
(the three RBM3D hits are the registry lines/docstring of Test/Axioms.lean written by this ticket)

## registry pre-check: scratch RBM3D/PrecheckTmp.lean = import RBM3D + import RBM3D.Induction.MainIndRegimes + #assert_rbm_axioms (deleted afterwards)
$ lake env lean RBM3D/PrecheckTmp.lean ; echo exit=$?  [after: Test/Axioms.lean at 12d8feb]
exit=0
axiom audit: 7130 theorems, 2394 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 144 (borrowed 1, owed 98, structural 33, refuted 6, superseded 6).
registry: 2 borrowed + 148 owed + 93 structural + 7 refuted + 6 superseded; 112 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
[before: Test/Axioms.lean at main, scratch = import RBM3D + #assert_rbm_axioms, from precheck_main.out]
axiom audit: 7071 theorems, 2386 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 145 (borrowed 1, owed 106, structural 32, refuted 6).
registry: 2 borrowed + 154 owed + 91 structural + 7 refuted; 109 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,

$ git status --short   (PrecheckTmp removed)

## reverse test and full build
$ lake build RBM3D.Test.AuditNegative 2>&1 | grep -E "reverse test|Build completed"
info: RBM3D/Test/AuditNegative.lean:30:0: audit reverse test: an unclassified premise is caught (RBM.Audit.Fixture.FakePremise).
Build completed successfully (3 jobs).
$ lake build 2>&1 | grep -E "^axiom audit|premises found by scanning|^registry:|Build completed|error"  (root RBM3D.lean unchanged: the hub adds the import at merge)
premises found by scanning: 145 (borrowed 1, owed 100, structural 32, refuted 6, superseded 6).
registry: 2 borrowed + 148 owed + 93 structural + 7 refuted + 6 superseded; 111 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4047 jobs).
```
R2* agnosticism (preflight (vi)), re-run at 1b:
```
$ grep -rn "STStep3R'\|STStep4R'\|STStep3I'\|STStep3II'\|STStep4I'\|STStep4II'" RBM3D
grep exit=1
```
Pattern table (python3 pattern.py; generated from the indexing `STRegChain i (j-i)`, cuts `c1=1-g^2`, `c2=1-g^2/L^2`, `c3=1-g^2/L^d`; stages (iii),(i),(ii),(iv) = 0..3):
```
pattern (i,j) = (stage of s, stage of t)  |  stages i..j  |  cuts  c_{i+1..j} (STRegChain i (j-i))  |  nesting
(0,0) | (iii)                  | -          | (iii)
(0,1) | (iii) (i)              | c1         | Seq((iii), (i))
(0,2) | (iii) (i) (ii)         | c1,c2      | Seq((iii), Seq((i), (ii)))
(0,3) | (iii) (i) (ii) (iv)    | c1,c2,c3   | Seq((iii), Seq((i), Seq((ii), (iv))))
(1,1) | (i)                    | -          | (i)
(1,2) | (i) (ii)               | c2         | Seq((i), (ii))
(1,3) | (i) (ii) (iv)          | c2,c3      | Seq((i), Seq((ii), (iv)))
(2,2) | (ii)                   | -          | (ii)
(2,3) | (ii) (iv)              | c3         | Seq((ii), (iv))
(3,3) | (iv)                   | -          | (iv)
patterns: 10 ; i>j empty: 6
```

Narrative. Verdict PASS: targets 1-7, Registry items (1)-(4), the eight pinned instances (+ extras). Size: 901 lines in `MainIndRegimes.lean` (ticket estimate 900 / 1150 / 1450; the 1500-line stop not reached), `Test/Axioms.lean` +50/-25.
1. Port: `ST_mainIndR_of_steps` is the T2191 probe `ST_mainInd_of_steps` (`git show 96c6b4c:RBM3D/Probe/T2191Pins.lean`, lines 351-404, branch `t/T2191`, never merged) with `R` threaded: `trivial` replaced by `hR hd sz s t hRst` (Steps 3-4) and `hRst` (Steps 5-6); Step 6 is fed `⟨hS2.1, hS2.2.1⟩` and `hS5.1`; constant = min of c₂..c₆. No RBM1D/RBM2D source (0 occurrences of the new names there), so no diff-stat.
2. Target 4 follows finding 1 of (a): `StochDomAt.of_subset` (the failure event of `Bctl` lies in that of `STWB`, same exponent, by `localAvg1_STWB_le`), then `iterationsA_prec_rpow` with `θ = 1/2`; `StochDomAt.trans` (needs `size → ∞`) is not used. `ST_mainIndR_seq`: constant `min c₁ c₂`, `(con_st_ind)` on `[s,m]`, `[m,t]` by `st_conStInd_sub` then `st5_conStInd_mono`.
3. Constant of `ST_mainInd_of_regimes`: the minimum of the four regime constants (chained directly, not the minimum of ten pattern constants). Private helpers: `STMainIndRAt` (the body of `STMainIndR` after `𝔠_d`), `STMainIndRAt_mono` (lower the constant), `_seq`, `_stage`, `_chain`; every `STRegChain i m` is proved at the common constant.
4. Classifier (public): `STCutK`, `STStageS`, `STStageT` (ℕ-valued; `STStageS_spec`, `STStageT_spec`), `STPattern : ℕ → Fin 4 × Fin 4`, `STRegK`, `STRegChain`, `STRegK_iff`, `STRegChain_holds`, `STRegChain_of_class`, `STStage_le` (`i > j` empty: 6 cells), `STCutK_mono/_lt/_comp`. Row `g = 0`: `i < j` forces `1 - g² < t < 1`, hence `0 < g²` and `STCutK_lt` applies (inside `STRegChain_of_class`).
5. Glue: the index type is the subtype of patterns with an infinite fibre (`Nat.nth` enumeration, `nth_cover`); flow by `STFlow_comp`, `(con_st_ind)` by `STConStInd_comp`; premises forward and conclusions back by the seven transfers of target 5.
6. Instances keep as hypotheses only other gates' pins (`STStep2`, `STStep3I`, ..., `STMainIndR 3 R`) and the stochastic premises (a)-(d) at `s`. Flows: `(szB, zB)` with `t ≤ 31/32` (`lemT_zB`), `(sz0, z0)`, `(szG, zB)`; `(0, 49/50)` is used only in the Prop-level `inst_regSeq_szB`, `inst_pattern_szB`, `inst_chain_szB` (preflight finding 2).
7. Registry: owed 154 -> 148, superseded 6, structural 91 -> 93 (`STMainIndR` as ticketed; `STStep5R` not ticketed: (a′) 1, (d) 1). `STRegSeq` stays structural; `STExpWardI` is in no list.

## (c) Verified Mathlib names (`#check`, script mathlib.lean, exit 0; verified absent: none needed)
- `div_le_self : 0 ≤ a → 1 ≤ b → a / b ≤ a`; `div_lt_self : 0 < a → 1 < b → a / b < a`
- `div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c`; `div_lt_div_of_pos_left : 0 < a → 0 < c → c < b → a / b < a / c`
- `pow_le_pow_right₀ : 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n`; `pow_lt_pow_right₀ : 1 < a → m < n → a ^ m < a ^ n`
- `one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n`; `one_lt_pow₀ : 1 < a → n ≠ 0 → 1 < a ^ n`
- `Real.sqrt_eq_rpow : √x = x ^ (1 / 2)`; `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`; `Real.rpow_nonneg : 0 ≤ x → ∀ y, 0 ≤ x ^ y`
- `Nat.nth_strictMono : (Set.ofPred p).Infinite → StrictMono (Nat.nth p)`; `Nat.nth_mem_of_infinite : … → ∀ n, p (Nat.nth p n)`
- `Nat.range_nth_of_infinite : … → Set.range (Nat.nth p) = Set.ofPred p`; `StrictMono.tendsto_atTop : StrictMono φ → Tendsto φ atTop atTop`
- `min_self : min a a = a`; `forall_congr' : (∀ a, p a ↔ q a) → ((∀ a, p a) ↔ ∀ a, q a)`; tactics `interval_cases`, `split_ifs`, `positivity`, `linarith` used.

## (d) Open issues and paper-delta candidates
1. `STStep5R` (hypothesis of the pinned `ST_mainIndR_of_steps`) was in no registry list, so the scan failed (pre-check output in (a′) 1); registered structural, as `STStep6R`. Alternative: owed, as `STStep3R`/`STStep4R`. Dispatcher to confirm (one line of `Test/Axioms.lean`).
2. Scan artefact: `STMainInd` and `STLocalMax` (owed) and `STMainIndR` (structural) are now conclusion heads of theorems, so the registry line lists them under "carry nothing yet"; they stay in their lists.
3. Hub at merge: add `import RBM3D.Induction.MainIndRegimes` after the last import line of `RBM3D.lean`. The root is unchanged here, so the full `lake build` above does not import the new module; the pre-check file does.
4. Paper-delta candidates: `T2245a` (as in the ticket: `lem:main_ind` proof applies Steps 1-6 on `[s,t]`; the formal proof reruns the induction step from each cut `1-g²`, `1-g²/L²`, `1-g²/L^d`, composes single-time conclusions, over the ten stage patterns; classifier convention `<` at `s`, `≤` at `t`); `T2245b` (the input `(Gt_bound+IND)` of the next stage from the conclusion `(Gt_bound)`: `STLocalMax_of_STLocalEntry`). No other.

