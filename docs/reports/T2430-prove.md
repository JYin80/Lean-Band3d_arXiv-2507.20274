Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 23:36 UTC 2026

Notation: `B := Bctl_v = W^{-d}B_{v,0}`; `e(p,q) := 4 − 1/(2p) − 1/q`; `E_a = W^{-d}1_a`, `P = P_{c1c2} = W^{-d}τ_{c1c2}`; `C₁ = G₁E_bG₂PG₁`, `C₂ = G₂PG₁E_bG₂`; `twDer x y = −(C₁+C₂)_{yx}` (script check, below); `Q(b) = twEE b b`.
Proof used (TP:140-144 = `docs/tickets/T2398-TL-proofs.md`, T.11 (iii)): `Q ≤ 2(S₁+S₂)`, `S_i = W^dΣ_c Tr(E_cC_iE_cC_i^*)`, and the two chains
- C₁: `S₁ ≤ η⁻¹ |L^{(1)}_b| · (L^{(2q)}_{(b,c1,…)})^{1/q} · max_c (L^{(4p)}_{(c2,c,…)})^{1/(2p)}` (Ward at x₂, `𝒜 = YY^*`, `P^*𝒲P ≤ W^{-d}‖𝒲_{c1c1}‖E_{c2}`, `‖A‖ ≤ Tr(A^k)^{1/k}` for `A ≥ 0`; here `Im Tr(GE_b)` replaces `Σ_{x∈[b]}Im G_xx/η`).
- C₂: `S₂ ≤ max_c (L^{(4p)}_{(b,c,…)})^{1/(2p)} · η⁻¹ (L^{(2)}_{(c1,c1)} L^{(4)}_{(c2,b,c2,b)})^{1/2}` ((2.53) `G₂^*G₂ = (G₂−G₂^*)/(2iη)`, then (B.3) for the two-twist trace).
All powers of `W^d` cancel exactly (checked numerically below).

### (i) Exponent table

| row | value | constraint | slack |
|---|---|---|---|
| target exponent `e(p,q)` | `[5/2, 4)`; `(1,1): 5/2`, `(2,2): 13/4` (consumer point, T2413 §4), `(3,3): 7/2` | `p,q ∈ ℕ_{≥1}` fixed | — |
| C₁ loop lengths | `L^{(1)}`, `L^{(2q)}` (Schatten `q` on `𝒲_{c1c1}`), `L^{(4p)}` (Schatten `2p`, i.e. the relabelling `p ↦ 2p` of TP) | all `k ≥ 1` available from `twSteps` conjunct 2 | — |
| C₁ exponent | `0 + (2q−1)/q + (4p−1)/(2p) = 4 − 1/q − 1/(2p) = e(p,q)` | `= e` | `0` (table: p,q ∈ {1,2,3}) |
| C₂ loop lengths | `L^{(2)}, L^{(4)}` (via (B.3)), `L^{(4p)}` | k ∈ {2,4,4p} | — |
| C₂ exponent | `(1+3)/2 + (4p−1)/(2p) = 4 − 1/(2p) = e(p,q) + 1/q` | `≥ e` for `B ≤ 1` | `1/q ∈ {1, 1/2, 1/3}`, absorbed as `B^{4−1/(2p)} ≤ B^{e}` |
| `k` set used | `{1, 2, 4, 2q, 4p}`; only conjunct 2 of `twSteps` (`TwistPins.lean:135-136`, (I3)); no `STStep2ConclgL`, no Claim 4.5, no conjuncts 3-4 | — | `R`, `Cd` unused |
| `η` power | one `η⁻¹` per chain (C₁: `G*G = Im G/η`; C₂: `(2η)⁻¹`), so `Q ≺ Ξ η⁻¹ B^e`, `Ξ = 1` | `η_v = Im ztOf = C.eta` (`ztOf_im`; `baEMn2PolyFacts` (R), `EMn2BA.lean:141-150`: `η_v > 0` on `[0,T0]`) | exact; no `Im m ≥ κ` quantity beyond `η_v > 0` |
| `B ≤ 1` on `[s,t]` | `STConStInd 𝔠d` (`Induction/Defs.lean:168`): `(B_t)^{𝔠d} ≤ (1−t)/(1−s) < 1` ⇒ `B_t < 1`; `t ≤ BAflowT0 < 1` (`EMn2BA_T0_lt_one`, `EMn2BA.lean:106`); `B_v ≤ B_t` (`STBctl_mono`, `Induction/ScaleFacts.lean:74`) | `𝔠d > 0`, eventually in n | choose `𝔠d = 1/100` (frame: `0 < 𝔠d ≤ 1/100`). Note: the merged `Bctl_le_one_of_conStInd` (`BA/Step1Fam.lean:382`) gives `B_s ≤ 1` only; the `t`-version is its inner `hlt` |
| ≺ calculus | factors: ≤ 5 ≺-bounds multiplied, `x ↦ x^{1/q}, x^{1/(2p)}` of nonnegative alternating loops, `max_c` over `L^d ≤ N` blocks (c is a free vertex of the `L^{(4p)}` index set, so each `c` is covered) | no `ε`-loss, no change of `p,q` | `0` |
| constants | `Q ≤ 2(S₁+S₂)`, `S₁ ≤ η⁻¹…`, `S₂ ≤ η⁻¹…` (factor `(2η)⁻¹·2 = η⁻¹`); depend on nothing: no `d, κ, ε, 𝔡`, no smallness of `g` | — | numeric `Q/(2(B₁+B₂)) ≤ 0.197` below |
| conjunct 2 | weight `w_{xy} = (W^d)⁻¹ S_{[x][y]}`, `S = 1 : Matrix` (identity) at `baFMz` (`FlowPins.lean:327`, `S := fun n => 1`): `w ∈ {0, W^{-d}} ≥ 0`; `twEE b b = Σ w|D_b|²` is real `≥ 0`, so `‖twEE b b‖ = twEE b b` | Cauchy–Schwarz, no hypothesis | CS ratio `≤ 0.2759` below |
| unused data | `R`, `Cd`, `STConStInd` beyond `B_t < 1`, `Θ`, `M` | not among the inputs of TP:140-144 | — |

### (ii) One concrete nondegenerate instance

(1) Deterministic chain at `d = 3, L = 3, W = 2` (`N = 216`, 27 blocks), BA-like `H = 0.7·Ψ + V` (Ψ = nearest-neighbour block hopping ⊗ I₈, V block-diagonal GOE, variance `W^{-d}`), `z = 0.3 + 0.05 i` (Hermitian, `Im z = η = 0.05`; `G − G^* = 2iη GG^* = 2iη G^*G` asserted in the script). Script `T2430/pre.py` (scratchpad; python3 + numpy 2.0.2) builds `twDer` from the entrywise formula of `TwistPins.lean:240-243`, `twEE` with weight `(W^d)⁻¹·1([x]=[y])`, the matrices `C₁, C₂, P`, every loop `Tr∏G(σ_i)E_{a_i}` as a trace, and runs all 4 charge pairs, `b ∈ {0,13}`, all 729 ordered `(c1,c2)` (702 with `c1 ≠ c2`), `(p,q) ∈ {1,2}×{1,2,3}` with `p ↦ 2p` as in TP:
```
$ python3 pre.py
check twDer x y = -(C1+C2)_{y x}: max err 0.0          (the same test against C1-C2 gives 2.6e-02, so it is not vacuous)
N = 216  eta = 0.05  Im m-free static resolvent, H = g Psi + V, g = 0.7
combos (sigma,b,c1,c2) checked: 5832
Q range over combos: min 2.812e-04 max 2.056e-02
max ratio Q/(2(S1+S2))             = 1.000000  (<= 1 required)   [equality where C1 = C2, e.g. sigma=(+,+), b=c1=c2=5: max|D1-D2| = 0.00e+00 (script chk3.py)]
max ratio S1/B1                    = 0.174542  (<= 1 required)   [B1 = eta^-1 |ImTr(GE_b)| (L^(2q))^(1/q) max_c (L^(4p)_c)^(1/2p)]
max ratio F/Fb                     = 0.760665  (<= 1 required)   [F = Tr(G2 P G1 E_b G1^* P^* G2^*), Fb = eta^-1 (L2 L4)^(1/2)]
max ratio S2/B2                    = 0.274641  (<= 1 required)   [B2 = max_c (L^(4p)_{b,c})^(1/2p) Fb]
max ratio Q/(2(B1+B2))             = 0.197021  (<= 1 required)
max ratio Q/(2(B1+B2)) [c1!=c2]    = 0.105043  (<= 1 required)
CS: 48 cases, max |EE(b,b')|^2/(EE(b,b)EE(b',b')) = 0.2759 ; max |Im EE(b,b)| = 1.91e-20
one value: sigma=(-,+), b=0, b'=13, c1=0, c2=9: |EE(b,b')| = 3.0851e-04, sqrt(EE(b,b)EE(b',b')) = 2.5768e-03
```
All hypotheses of the chain hold at once (Hermitian `H`, `Im z > 0`, `b ≠ b'`, `c1 ≠ c2`, nonzero `Q ∈ [2.8e-4, 2.1e-2]`); the chain is deterministic, so this is the identity-level check of TP:140-144 with loops in place of (I3). Exponent table (`python3`, exact fractions): `(p,q) = (1,1): e = C₁ = 5/2, C₂ = 7/2`; `(2,2): 13/4, 15/4`; `(3,2): 10/3, 23/6`; `C₂ − e = 1/q` in all 9 cases of `{1,2,3}²`.

(2) The Lean datum of the instance (`TwistPins.lean:759-781` pattern): `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`, `Defs/Sizes.lean:260-265`), `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)` (`flow_sz0`, `BA/FlowPins.lean:1214`), `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`, `FlowPins.lean:1227`; also `17/25 ≤ T0 ≤ 25/36`, `Step1Fam.lean:748-753`), `𝔠d = 1/100`. `B ≤ 1` and `STConStInd` at this datum (`Bparam`, `Defs/Params.lean:36`, `K = 0`):
```
$ python3 datum.py            (excerpt; Bctl n t = W^-3 ((g^2+|1-t|)^-1 + (L^3|1-t|)^-1))
STConStInd(cd=1/100) at s=1/2,t=2/3: Bctl_n(t)^cd <= (1-t)/(1-s)=0.6667
 n= 0 Bctl_n(2/3)=9.292e-05  Bctl^cd=0.9113  holds=False
 n= 7 Bctl_n(2/3)=2.602e-18  Bctl^cd=0.6670  holds=False
 n= 8 Bctl_n(2/3)=4.447e-19  Bctl^cd=0.6554  holds=True
 n=11 Bctl_n(2/3)=5.942e-21  Bctl^cd=0.6277  holds=True
n=8: Bctl_n(v) on v in [1/2,2/3]: ['2.96e-19', '3.29e-19', '3.71e-19', '4.45e-19'] all <= 1: True
n=8: L=36 W=1889568 size=(WL)^3=3.148e+23
 (p,q)=(1,1): e=2.5000  Bctl^e=1.319e-46  Bctl^(4-1/2p)=5.863e-65  absorbed: True
 (p,q)=(2,2): e=3.2500  Bctl^e=2.271e-60  Bctl^(4-1/2p)=1.514e-69  absorbed: True
 n= 1000 Bctl_n(2/3)=9.019e-50  ratio Bctl*(2(n+1))^15 = 3.0000
```
`STConStInd` is an eventually-in-n hypothesis; for `𝔠d ≤ 1/100` it forces `B_t ≤ (2/3)^{100}` and holds from `n = 8` on (the size is astronomical only because `(con_st_ind)` at `𝔠d = 1/100` demands it; the statement itself is `∀ᶠ n`, and the merged `s1Setup_conStInd_const` proves it for every `𝔠d > 0`). Conjunct 2 is a deterministic statement; its datum shape (`σ = (−,+)`, `b ≠ b'`, `c1 = 0 ≠ c2 = (1,0,0)`, block index 9 at `L = 3`) is the last printed row of (1): `b = 0, b' = 13, c1 = 0, c2 = 9`, ratio `|EE(b,b')|/√(EE(b,b)EE(b',b')) = 3.0851e-04/2.5768e-03 = 0.12`, with `S = 1` by `rfl` (`FlowPins.lean:327`).

External hypothesis `twSteps` (the only one left; Steps 1-4 owed by other gates), concrete limit computation: its conjunct 2 needs `‖L^{(k)}‖ ≺ B^{k−1}` with `B_n(2/3) = 3·(2(n+1))^{-15}(1+o(1)) → 0` (last line of the output: `B·(2(n+1))^{15} = 3.0000` for n = 10, …, 10^4), so the right-hand sides are positive, finite and decreasing, `B ≤ 1` from `n ≥ 8`; `k = 1` reads `|Tr(GE_b)| ≺ 1`, which is the trivial bound at the static resolvent (`|Tr(GE_b)| ≤ ‖G‖ ≤ η⁻¹`, finite). No other part of `twSteps` is used.

### Verdicts
- Target 1, conjunct 1 (`baTwistSrc3_holds`, `∀ R`, `∀ p q ≥ 1`): **PASS**. All exponents close (C₁ with slack 0 at `e(p,q)`, C₂ with slack `1/q`); `𝔠d = 1/100` works; `R`, `Cd` are not used.
- Target 1, conjunct 2 (deterministic Cauchy–Schwarz): **PASS** (`S = 1`, weight `≥ 0`, `twEE b b = ‖twEE b b‖`).
- Target 3 (instance at the `TwistPins` datum with `twSteps` as the only hypothesis): **PASS** (datum above; `twSteps` is a hypothesis of the example).
- Points for stage 1b (not blockers): (1) `B_t < 1` must be taken from `STConStInd` directly (`Bctl_le_one_of_conStInd` is at `s`); (2) the ticket's preflight items (iii) reuse table and (v) line prediction are outside stage-1a scope (CLAUDE.md §4 step 1) and are not written here.

## (b) Script output — Mon Oct 12 00:23:57 UTC 2026 (stage 1b started Sun Oct 11 23:37 UTC 2026)

Line count against the stop line: `RBM3D/BA/TwistQV.lean` 1429 lines (stop line 2000, split threshold 1700): no `TwistQV2.lean`, no probe file.
`wc -l` at the four section commits 3f8e049, b70b0b6, bf9718c, 66632ff: 793, 1044, 1291, 1429.

Reuse table (every copied lemma, source file:line, as finally used), exponent table (i), statement of the target:
```
$ python3 reuse.py
copied (source file:line)                          -> here (TwistQV.lean:line)
sum_mul_pow_le               RBM3D/Induction/Contract.lean:82               -> TwistQV_sum_mul_pow_le :75
psd_quad_pow_le              RBM3D/Induction/Contract.lean:101              -> TwistQV_psd_quad_pow_le :93
sum_norm_sq_vecMul           RBM3D/Induction/Contract.lean:161              -> TwistQV_sum_norm_sq_vecMul :153
rowbound_of_pow              RBM3D/Induction/Contract.lean:177              -> TwistQV_rowbound_of_pow :169
Gres_conjTranspose           RBM3D/Induction/Contract.lean:225              -> TwistQV_Gres_conjTranspose :196
Gres_sub                     RBM3D/Induction/Contract.lean:240              -> TwistQV_Gres_sub :211
sub_conj_eq                  RBM3D/Induction/Contract.lean:271              -> TwistQV_sub_conj_eq :242
Gres_ward_left               RBM3D/Induction/Contract.lean:277              -> TwistQV_Gres_ward_left :248
wd                           RBM3D/Induction/Contract.lean:310              -> TwistQV_wd :273
wd_nil                       RBM3D/Induction/Contract.lean:312              -> TwistQV_wd_nil :275
wd_cons                      RBM3D/Induction/Contract.lean:314              -> TwistQV_wd_cons :277
wd_append                    RBM3D/Induction/Contract.lean:317              -> TwistQV_wd_append :280
wd_singleton                 RBM3D/Induction/Contract.lean:320              -> TwistQV_wd_singleton :283
wd_pow                       RBM3D/Induction/Contract.lean:410              -> TwistQV_wd_pow :286
length_replicate_flatten     RBM3D/Induction/Contract.lean:416              -> TwistQV_length_replicate_flatten :292
trace_pow_proj               RBM3D/Induction/Contract.lean:487              -> TwistQV_trace_pow_proj :301
Pm                           RBM3D/Induction/Contract.lean:707              -> TwistQV_Pm :326
Eblk_eq_smul_Pm              RBM3D/Induction/Contract.lean:712              -> TwistQV_Eblk_eq_smul_Pm :331
Pm_eq_smul_Eblk              RBM3D/Induction/Contract.lean:720              -> TwistQV_Pm_eq_smul_Eblk :339
Pm_conjTranspose             RBM3D/Induction/Contract.lean:725              -> TwistQV_Pm_conjTranspose :344
Pm_mul_self                  RBM3D/Induction/Contract.lean:729              -> TwistQV_Pm_mul_self :348
norm_ward_trace_le           RBM3D/Induction/Contract.lean:744              -> TwistQV_norm_ward_trace_le :359
norm_Ward_const              RBM3D/Induction/Contract.lean:752              -> TwistQV_norm_Ward_const :367
Contract_norm_trace_wd_le    RBM3D/Induction/Contract.lean:1046             -> TwistQV_norm_trace_wd_le :380
Contract_maxLoopM_nonneg     RBM3D/Induction/Contract.lean:1062             -> TwistQV_maxLoopM_nonneg :396
lemDecCalEdif_Gres_blockMat  RBM3D/Path/LemDecCalEdif.lean:444              -> TwistQV_Gres_blockMat :978
$ python3 exptable.py
p q | k-set            | e=4-1/(2p)-1/q | C1=(2q-1)/q+(4p-1)/(2p) | C2=2+(4p-1)/(2p) | C1-e | C2-e
1 1 | {1,2,4,2,4}        | 5/2             | 5/2                     | 7/2              | 0 | 1
1 2 | {1,2,4,4,4}        | 3               | 3                       | 7/2              | 0 | 1/2
1 3 | {1,2,4,6,4}        | 19/6            | 19/6                    | 7/2              | 0 | 1/3
2 1 | {1,2,4,2,8}        | 11/4            | 11/4                    | 15/4             | 0 | 1
2 2 | {1,2,4,4,8}        | 13/4            | 13/4                    | 15/4             | 0 | 1/2
2 3 | {1,2,4,6,8}        | 41/12           | 41/12                   | 15/4             | 0 | 1/3
3 1 | {1,2,4,2,12}       | 17/6            | 17/6                    | 23/6             | 0 | 1
3 2 | {1,2,4,4,12}       | 10/3            | 10/3                    | 23/6             | 0 | 1/2
3 3 | {1,2,4,6,12}       | 7/2             | 7/2                     | 23/6             | 0 | 1/3
$ grep -n -A1 "^theorem baTwistSrc3_holds" RBM3D/BA/TwistQV.lean
1385:theorem baTwistSrc3_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc3 d R := by
1386-  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
$ grep -n "^def BATwistSrc3\|^def BATwFrame" -A5 RBM3D/BA/TwistPins.lean   # the pin, unchanged
def BATwFrame (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Q : ∀ sz : Sizes d, FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
      (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t → sz.STConStInd 𝔠d s t → twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        Q sz (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

def BATwistSrc3 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  (∀ p q : ℕ, 1 ≤ p → 1 ≤ q → twSrc C μ s t (fun n v ω σ b c₁ c₂ => ‖twEE C n v ω σ b b c₁ c₂‖) (fun _ _ => 1)
    (4 - 1 / (2 * (p : ℝ)) - 1 / (q : ℝ))) ∧
  ∀ n v ω σ b b' c₁ c₂, ‖twEE C n v ω σ b b' c₁ c₂‖ ≤ Real.sqrt (‖twEE C n v ω σ b b c₁ c₂‖ * ‖twEE C n v ω σ b' b' c₁ c₂‖)
```

Build, checks, axioms, instance, hygiene:
```
$ date -u
Mon Oct 12 00:20:21 UTC 2026
$ wc -l RBM3D/BA/TwistQV.lean   # stop line 2000 (binding), split threshold 1700, no TwistQV2
    1429 RBM3D/BA/TwistQV.lean
$ git log --oneline 0a8176c..HEAD; git diff --name-only 0a8176c...HEAD; git status --short
66632ff T2430: TwistQV conjunct 2, target baTwistSrc3_holds, instance, docstrings (part 4)
bf9718c T2430: TwistQV BA bound, exponent arithmetic and the conjunct-1 assembly (part 3)
b70b0b6 T2430: TwistQV deterministic core, chains and the carrier bridge (part 2)
3f8e049 T2430: TwistQV tools, Schatten row bounds, Ward sums, first chain (part 1)
RBM3D/BA/TwistQV.lean
(status above: empty = clean)
$ lake build RBM3D.BA.TwistQV 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (4010 jobs).
$ lake env lean (lakefile linter options) RBM3D/BA/TwistQV.lean   # warnings/errors of this file
exit=0
$ lake env lean docs/tickets/checks/T2430-check.lean; echo $?
check-file exit code: 0
$ #print axioms (the example is compiled as a named theorem in a scratch copy of the file)
'RBM.BA.TwistQV_inst_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistSrc3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ check file + import TwistQV + `example : T2430_Target 3 := RBM.BA.baTwistSrc3_holds 3`
exit code: 0
$ sed -n 1412,1425p RBM3D/BA/TwistQV.lean   # the instance
example {Cd : ℝ} (hC : 0 < Cd) (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd) :
    twSrc (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3)
      (fun n v ω σ b c₁ c₂ => ‖twEE (baFMz sz0 zSeq) n v ω σ b b c₁ c₂‖) (fun _ _ => 1) (13 / 4) ∧
    ∀ ω : sz0.SeqΩ, ∃ b b' c₁ c₂ : Zd 3 (sz0.L 0), b ≠ b' ∧ c₁ ≠ c₂ ∧
      ‖twEE (baFMz sz0 zSeq) 0 (1 / 2) ω ![false, true] b b' c₁ c₂‖ ≤
        √(‖twEE (baFMz sz0 zSeq) 0 (1 / 2) ω ![false, true] b b c₁ c₂‖ *
          ‖twEE (baFMz sz0 zSeq) 0 (1 / 2) ω ![false, true] b' b' c₁ c₂‖) := by
  have h := TwistQV_frame_inst (baTwistSrc3_holds 3 STAny) hC hS
  have hL : Fact (1 < sz0.L 0) := ⟨by have := sz0.three_le_L 0; omega⟩
  refine ⟨?_, fun ω => ⟨0, ![1, 0, 0], 0, ![1, 0, 0], fun hh => by simpa using congrFun hh 0,
    fun hh => by simpa using congrFun hh 0, h.2 0 (1 / 2) ω ![false, true] 0 ![1, 0, 0] 0 ![1, 0, 0]⟩⟩
  have h22 := h.1 2 2 (by norm_num) (by norm_num)
  norm_num at h22
  exact h22
$ hygiene
sorry/admit/native_decide/axiom hits: 0
Step2Gen_/STthetaOpg hits: 0
$ name clash: public declarations of the new file; hits of baTwistSrc3_holds on main
1385:theorem baTwistSrc3_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
1412:example {Cd : ℝ} (hC : 0 < Cd) (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fu
hits on main:        0
ports from ../RBM1D, ../RBM2D: none (copies are from RBM3D/Induction/Contract.lean@915114c, RBM3D/Path/LemDecCalEdif.lean@7d9f111)
$ mathlib names: #check of every Mathlib-qualified name occurring in the file
126 names
errors: 0
$ git diff --name-only main...t/T2430
RBM3D/BA/TwistQV.lean
$ ls RBM3D/Probe/T2430Pins.lean; ls RBM3D/BA/TwistQV2.lean   # probe / split files
ls: RBM3D/BA/TwistQV2.lean: No such file or directory
ls: RBM3D/Probe/T2430Pins.lean: No such file or directory
$ pre-check: import RBM3D; import RBM3D.BA.TwistQV; #assert_rbm_axioms   (exit 0)
axiom audit: 12222 theorems, 3792 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
$ lake build   # with a TEMPORARY, uncommitted `import RBM3D.BA.TwistQV` in RBM3D.lean (restored afterwards; git status clean)
5174:info: RBM3D.lean:475:0: axiom audit: 12222 theorems, 3792 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4243 jobs).
```

Narrative:
- **Delivered.** `baTwistSrc3_holds (d) (R) : BATwistSrc3 d R` (file line 1385): both conjuncts, every regime `R`, no `sorry`; the instance (line 1412) keeps `twSteps` as its only hypothesis. Axioms: the standard three.
- **Route.** All work is on the block-product index `Vtx d L W`: offsets make `τ_{c₁c₂}` free, so the `TwistPins` twisted-sum helpers (`:292-345`) are not needed. `W^{2d}` times `C₁`, `C₂` of TP:140 are `TwistQV_CC1`, `TwistQV_CC2`. The Schatten trick is the copied `rowbound_of_pow` (`TwistQV_rowbound_off`); `tr[(AA^*)^p]` is a word of length `2p` (`TwistQV_Tbound`), hence `≤ (W^d)^{2p} M_{2p}`.
- **C₁** (`TwistQV_chain1_row`, `TwistQV_ward_sum`): the paper's `‖𝒜_{bb}‖ ≤ ‖𝒲_{c₁c₁}‖ ‖E_c^{1/2} G₁^* E_{c₂} G₁ E_c^{1/2}‖` chain, read row by row (two Schatten bounds, `L^{(2q)}` and `L^{(4p)}`), then Ward at the summed offset (`L^{(1)}`). **C₂** (`TwistQV_chain2_row`, `TwistQV_R2`): one Schatten bound (`L^{(4p)}`), then `(2.53)` and Cauchy-Schwarz over the offset pair with `L^{(2)}`, `L^{(4)}`. This is (B.3) inlined (`TwistQV_cs2`, `TwistQV_hsG`, `TwistQV_hsX`); (B.3) is not a stand-alone lemma.
- **Core** (`TwistQV_core`): `Σ_y Σ_{x∈[y]} |C₁+C₂|² ≤ 2 (W^d)^5 η⁻¹ [M₁ M_{2q}^{1/q} M_{4p}^{1/(2p)} + M_{4p}^{1/(2p)} (M₂M₄)^{1/2}]`, all powers of `W^d` cancelling exactly. `‖twEE b b‖` is this sum times `(W^d)^{-5}` (`TwistQV_twEE_diag`, `S = 1` by `rfl`).
- **`≺` assembly**: `TwistQV_dom` (five inputs, `HighProbAt.biInter`), `TwistQV_arith` (exponents `= e` for C₁, `= e + 1/q` for C₂, absorbed by `B ≤ 1`; constant `4 X³`, `X = N^{τ/6}`, absorbed as `4 ≤ N^{τ/2}` eventually), `TwistQV_src`.
- **Bridge** (new, not copied): `TwistQV_sum_blk`, `TwistQV_shift_symm`, `TwistQV_twChg_vtx`, `TwistQV_twDer_vtx`, `TwistQV_twEE_diag` (entries on `Idx`, sums over `twBlk`, to offsets on `Vtx`); `(baFMz sz z).L = loopFine` by `rfl` (`TwistQV_Mx_le`). `≺` lemmas used: `StochDomAt.highProb` (`Defs/StochDomAt.lean:534`), `Gauss.HighProbAt.biInter` (`:589`), `Sizes.tendsto_size` (`:735`), `eventually_le_rpow` (`Defs/Domination.lean:68`).
- **Inputs used**: the second conjunct of `twSteps` at `k ∈ {1,2,4,2q,4p}`; `EMn2BA_seqHflowBA_herm`, `EMn2BA_mF_data`, `EMn2BA_T0_lt_one`, `ztOf_im` (`η_v > 0`); `STConStInd` only through `Bctl n (t n) < 1` (then `STBctl_mono`, `STBctl_pos`). The ticket's sentence "the proof uses neither `Cd`, nor `STConStInd`, nor `R`" is wrong for `STConStInd` (section (a), row `B ≤ 1`, says so); `Cd`, `R`, `hd`, `hst` are unused; `𝔠d = 1/100`.
- **Conjunct 2** (`TwistQV_cs`): weighted Cauchy-Schwarz, deterministic, for any carrier with `S = 1`.
- **Reuse**: 25 private tools of `Induction/Contract.lean` and 1 of `Path/LemDecCalEdif.lean` are copied (table above; section headers of the file give the source line ranges); `Induction/ContractPt.lean:73-116` is not used. Nothing is ported from RBM1D or RBM2D.
- `RBM3D.lean` is not edited (the hub adds the import at merge, CLAUDE.md §3 (A) step 4); the full `lake build` above used a temporary import, restored afterwards. Section (a) needed no correction (no (a′)).

## (c) Verified Mathlib names used (script: `#check` of all 126 Mathlib-qualified names occurring in the file, 0 errors; unqualified names are not listed)
- `Bool.`: false_eq_true, not_false, not_true
- `Complex.`: I, conj_conj, conj_mul', im_le_norm, im_sum, mul_conj', norm_I, norm_conj, norm_natCast, norm_real, ofReal_pow, ofReal_re, re_le_norm, re_sum, star_def, sub_conj
- `Equiv.`: sum_comp
- `Filter.`: eventually_all
- `Finset.`: exists_max_image, le_sup', mem_univ, mul_sum, single_le_sum, sum_add_distrib, sum_comm, sum_congr, sum_eq_single, sum_filter, sum_le_sum, sum_mul, sum_mul_sum, sum_nonneg, sum_sub_distrib, sup'_le, univ, univ_nonempty
- `Fintype.`: sum_prod_type
- `Function.`: comp_def
- `List.`: ext_getElem, flatten_cons, length_cons, length_flatten, length_nil, map_cons, map_nil, map_replicate, ofFn, prod_cons, prod_nil, replicate, replicate_succ, sum_replicate
- `Matrix.`: conjTranspose_apply, conjTranspose_conjTranspose, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_one, conjTranspose_smul, conjTranspose_sub, diag_apply, diagonal, diagonal_mul, diagonal_mul_diagonal, diagonal_pow, dotProduct_mulVec, inv_submatrix_equiv, isHermitian_diagonal_iff.mpr, isUnit_iff_isUnit_det, mulVec, mulVec_diagonal, mulVec_mulVec, mul_apply, mul_assoc, mul_diagonal, mul_nonsing_inv, mul_one, mul_smul, mul_sub, nonsing_inv_eq_ringInverse, nonsing_inv_mul, one_apply, one_mul, one_mulVec, posSemidef_self_mul_conjTranspose, smul_apply, smul_mul, star_eq_conjTranspose, star_mulVec, sub_apply, sub_mul, submatrix_apply, submatrix_smul, submatrix_sub, trace, trace_diagonal, trace_mul_comm, trace_mul_cycle, trace_smul
- `Nat.`: cast_le, cast_ne_zero, cast_sub, pos_iff_ne_zero.mp
- `Real.`: mul_rpow, mul_self_sqrt, norm_of_nonneg, one_le_rpow, pow_rpow_inv_natCast, rpow_add, rpow_inv_natCast_pow, rpow_le_rpow, rpow_le_rpow_of_exponent_ge, rpow_le_rpow_of_exponent_le, rpow_mul, rpow_natCast, rpow_nonneg, rpow_one, sq_sqrt, sqrt_le_sqrt, sqrt_mul, sqrt_nonneg, sqrt_sq, sum_mul_le_sqrt_mul_sqrt
- `Set.`: mem_iInter
- Names verified absent: none searched (no name was invented). One deprecation met in the tool log: `if_true` (use `ite_true`); the file uses `ite_true`.

## (d) Open issues and paper-delta candidates
- **T2430a** (paper-delta candidate): T.11 (iii), TP:144 gives the `C₂` term `η⁻¹ (W^{-d}B)^{4-1/(2p)}`, which is `≤ η⁻¹ (W^{-d}B)^{4-1/(2p)-1/q}` only if `W^{-d}B_{v,0} ≤ 1`; the text does not say so. Lean takes `B_t < 1` from `STConStInd` (`(con_st_ind)`, `1_2:1296`) and `B_v ≤ B_t` (`TwistQV_src`).
- Open: `twSteps` (Steps 1-4 at BA, conjunct 2 = `(I3)`) is owed by other gates and stays a hypothesis of the instance; the limit check is in section (a)(2).
- Consumer note for TL2d: `h.1 p q` at `(p, q) = (2, 2)` has exponent `13/4` (instance, line 1423-1425).
- No obstruction; no pin was changed; no new public statement was needed, so no probe step.
