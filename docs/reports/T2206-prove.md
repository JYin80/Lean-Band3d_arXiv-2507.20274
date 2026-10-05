Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 19:32:07 UTC 2026

### (i) Exponent table

Constants/thresholds the 53 pins depend on (ticket `docs/tickets/T2206.md`, check file `docs/tickets/checks/T2206-check.lean`). T2206 has no paper exponent of its own; it transfers hypotheses along `φ`, so every row is a constraint on `φ` or a merged-instance constant.

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| `φ` for field lemmas, `measurable_reindex`, 13 commutation `rfl`s | any `φ : ℕ → ℕ` | none (`comp`, `reindex` are field/coordinate compositions; `Defs/Sizes.lean:138`, `FineModel.lean:156-176`) | n/a |
| `φ` for `comp_sizeTendsto/bandwidth/WO/admissible`, `STFlow_comp`, `STConStInd_comp`, `*.subseq` | `Tendsto φ atTop atTop` | `∀ᶠ n` predicates pull back by `Tendsto.eventually`; `∀ n` ones restrict pointwise | `φ = const` fails `SizeTendsto` (`size ∘ const` bounded): the hypothesis is necessary |
| `φ` for the image law, `MeasurePreserving`, `Prec_comp_iff`, `integral_*_reindex` | `Function.Injective φ` | `reindexCoord ⟨j,c⟩ = ⟨φ j,c⟩` is injective iff `φ` is | `φ = const`: `reindex` forces `ω'⟨0,c⟩ = ω'⟨1,c⟩`, a null set of the comp law when `seqGvar > 0`, of full `seqP sz` measure: necessary |
| `φ k` for `iff_cover`, `Prec_comp`, `*_comp_cover` | `StrictMono (φ k)`, `ι` finite, `∀ᶠ n, ∃ k, n ∈ range (φ k)` | gives `Tendsto` and injective; `φ k j ≥ φ k J_k ⇒ j ≥ J_k` | threshold `N = max(N₀, max_k φ k (J_k))`; `∀ τ D` stand before `∀ᶠ`, so `J_k = J_k(τ,D)` is allowed |
| `ι` empty in cover | — | `atTop` on `ℕ` is `NeBot`, so the cover hypothesis is false; no vacuous case | n/a |
| `nth_cover` | `c : ℕ → ι`, `ι` finite | finite classes have a common bound `B`; for `n > B`, the class of `n` is infinite, and `Nat.nth` enumerates it (`range_nth_of_infinite`) | n/a |
| scale | `(sz.comp φ).size j = (W(φj) L(φj))^d = sz.size (φ j)` | `rfl` | exact |
| law hypothesis `∀ s, μ (f⁻¹' s) = ν s` | every `s ⊆ Ω₁` (not only measurable) | provided by the exact image law (ii) for `seqP`, `(withLam g).seqP` | exact equality |
| `sz0` bandwidth `𝔠` (ticket instance 2) | `1/6` | `N^𝔠 ≤ W` eventually | `j=1`: `N^{1/6} = 305.5 ≤ 7776` (ratio 25.5); general `sz0`: `N ≤ W^6` (`sz0_size_le_W_pow`) |
| `sz0` `(eq:WO)` `𝔡` | `1/10`, `d = 3` | `W^{-d/2+𝔡} = W^{-7/5} ≤ lam ≤ 𝔡⁻¹ = 10` | `j=1`: `3.572e-06 ≤ 2.143e-05` (ratio 6); `lam ≤ 10` slack `2.1e5` |
| `sz0` locDomain `κ, ε` | `1/10, 1/10` | `|Re z| ≤ 2-κ`, `N^{-1+ε} ≤ Im z ≤ 1`, `z0 n = 1/2 + i N^{-4/5}` | `1/2 ≤ 1.9`; `N^{-9/10}` vs `N^{-4/5}`: factor `N^{1/10}` (`j=1`: `3.81e-14 ≤ 1.18e-12`) |
| `(con_st_ind)` `𝔠_d` (instance 4, every `𝔠_d > 0`; `STMainInd` has `𝔠_d ≤ 1/100`) | `s=0`, `t=1/16`, `(1-t)/(1-s) = 15/16` | `Bctl(j,t)^{𝔠_d} ≤ 15/16 < 1`, eventually in `j` | `𝔠_d = 1/100`: holds for all `j ≥ 0` (`j=1`: `0.7648`); `𝔠_d = 1/1000`: from `j ≥ 19` (`j=1`: `0.9735`); `Bctl → 0` gives a threshold for every `𝔠_d > 0` |
| `φ` of instances 1-8 | `φ j = 2 j` | `StrictMono`, injective, `Tendsto` | `sz0.comp φ` at `j` is `sz0` at `n = 2j` |
| `φ k` of instance 9 | `Nat.nth (· % 2 = r)`, `r ∈ {0,1}`: `2j`, `2j+1` | `StrictMono`; ranges cover all `n` | thresholds `J = (5,3)` give `N = 10` |
| Per-`n` objects (preflight (iii)) | depend on `sz` only through `L n, W n, lam n`, and on `ω` only through `slice sz n ω` | needed for the `rfl`s | read from `FineModel.lean:176-230`, `GLoopFlow.lean:152-158`, `Induction/Defs.lean:64-77,104-165`, `Params.lean:32-36`, `Sizes.lean:157-214`; `STExp2` integrates over the whole law `sz.seqP`, handled by `integral_reindex` |

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6}`, `Defs/Sizes.lean:260`), `φ j = 2j` (instances 1-8), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z0(n) = 1/2 + i N_n^{-4/5}`, `s ≡ 0`, `t ≡ 1/16` (`Induction/Defs.lean:413-440`). Every deterministic hypothesis of targets 1-6 (field values, `Tendsto/StrictMono/Injective φ`, `Admissible`, `locDomain`, `STConStInd`, the finite `StrictMono` cover) is checked by the script below. There is no external hypothesis (T2206 imports no unmerged file, no cited result), so no external limit computation arises.

```
cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2206 && python3 inst.py
j=1: L,W,lam = 12 7776 1/46656
Bandwidth (N^(1/6)<=W), WO(1/10) and size>=j hold for j=0..300; j=1: N^(1/6)=305.5 <= W=7776 ; W^(-7/5)=3.572e-06 <= lam=2.143e-05
size(j) increasing: True
locDomain(1/10,1/10) at z0(2j), j=0..300 ok; j=1: N^(-9/10)=3.812e-14 <= Im z=1.181e-12 <= 1
cd=0.01: Bctl(j)^cd<=15/16 from j>=0 on (checked 50 consecutive); Bctl(1)=2.270e-12, Bctl(1)^cd=0.7648
cd=0.001: Bctl(j)^cd<=15/16 from j>=19 on (checked 50 consecutive); Bctl(1)=2.270e-12, Bctl(1)^cd=0.9735
parity cover: phi_0=2j, phi_1=2j+1 strictly increasing, ranges cover every n<5000; classes infinite: card subtype=2
thresholds J= [5, 3] => N= 10
every n>=N in range(phi_k) has index j>=J_k: True
phi=0 const: reindex image law lives on {w'<0,c>=w'<1,c>}, a null set for the independent comp law (if variance>0); phi=2j injective: True
```

(The script is Python, not Lean; it checks sampled `j`, the asymptotic statements are the analytic rows of (i): `N ~ n^18`, `W ~ n^5`, `lam ~ n^{-6}`, `Bctl → 0`.)

Mathematical arguments the targets rest on (each checked against the cited file lines):

1. **Measure preservation (target 2b).** `reindex sz φ = (ω ↦ ω ∘ f)` with `f = reindexCoord`, injective when `φ` is. `Measure.map_infinitePi_infinitePi_of_inj` (`Mathlib/Probability/Independence/InfinitePi.lean:142`, hypotheses: probability measures, `f` injective) gives `(infinitePi P).map (· ∘ f) = infinitePi (P ∘ f)`. With `P c = gaussianReal 0 (seqGvar sz c)` and `seqGvar (sz.comp φ) ⟨j,c⟩ = gvarF d (L (φ j)) (W (φ j)) (lam (φ j)) c = seqGvar sz ⟨φ j,c⟩` (`FineModel.lean:164`, `rfl` on field projections) this is `seqP (sz.comp φ)`. For `sz.withLam g`, `seqGvar` reads `lam c.1 = g c.1`, giving `((sz.comp φ).withLam (fun j => g (φ j))).seqP`; `gvarF` takes values in `ℝ≥0` for every coupling (`FineModel.lean:89`), so for any `g`, including `g = 0`, each factor is a probability measure (`gaussianReal 0 v`, a Dirac at `v = 0`) and the hypotheses of the Mathlib lemma hold.
2. **Exact image law (target 2c), route taken: product splitting.** `Π_I ≃ᵐ Π_R × Π_{I∖R}` with `R = range f` (`MeasurableEquiv.piEquivPiSubtypeProd`); `infinitePi P = ν_R ⊗ ρ` by independence of disjoint coordinate blocks (`iIndepFun_infinitePi`, `InfinitePi.lean:125`); `Π_R ≃ᵐ Π_J` along `Equiv.ofInjective`. For arbitrary `s ⊆ Π_J`: `reindex⁻¹ s = e⁻¹(s' × univ)`, so `μ(reindex⁻¹ s) = (μ.map e)(s' × univ) = ν_R(s')·ρ(univ) = ν(s)` by `MeasurableEquiv.map_apply` (all sets) and `Measure.prod_prod` (`Mathlib/MeasureTheory/Measure/Prod.lean:231`, "we do not need the sets to be measurable"). Paper proof of the outer-measure identity: `≤` by monotonicity to a measurable hull `A ⊇ s'` with `ν(A) = ν(s')`. `≥`: for measurable `B ⊇ s' × Y`, `x ↦ ρ(B_x)` is measurable and equals `1` on `s'`, so `ν(s') ≤ ν{ρ(B_x) = 1} ≤ ∫ρ(B_x)dν = μ(B)`; take `inf` over `B`. Needs `ρ(univ) = 1`, which holds (probability).
3. **Integrals, every integrand (target 2c).** `integral_fun_fst` (`Prod.lean:548`, from `integral_prod_smul :524`, no measurability hypothesis) gives `∫ g(z.1) d(ν⊗ρ) = ρ.real univ • ∫ g dν = ∫ g dν` for every `g`, `E` any real normed space; for `g` a.e. equal to a measurable `g̃`, the null set `{g ≠ g̃}` pulls back to a null set by item 2, so both sides agree with the integral of `g̃`; the statement of `integral_fun_fst` carries no measurability hypothesis, so the non-measurable case is that lemma's. This is why `MeasurePreserving` alone (only `μ(f⁻¹ s) ≤ (μ.map f)(s)`, `Measure.le_map_apply`) is the direction `comp → sz` and the exact law is needed for `sz → comp` (premises forward), for the uncountable `TimeIcc` unions of `badSetAt` (`StochDomAt.lean:53`).
4. **`map_iff`, `subseq`, `iff_cover`, `nth_cover`.** `badSetAt` of the pulled-back family `= f⁻¹'(badSetAt)`, so `μ(·) = ν(·)` by the law hypothesis; `HighProbAt` complement likewise. `subseq`: `∀ᶠ l` pulls back along `φ` with `Tendsto φ atTop atTop`. `iff_cover` `⇐`: for fixed `τ, D` each `k` gives `J_k`; for `n ≥ N`, `n = φ k j` and strict monotonicity gives `j ≥ J_k` (if `j < J_k` then `φ k j < φ k J_k ≤ N ≤ n`). `⇒` by `subseq` with `StrictMono.tendsto_atTop`. Non-monotone injective `φ` with `Tendsto` suffices for `subseq` only. `StochDomAt_of_map`: `μ(f⁻¹ s) ≤ (μ.map f)(s)` for every `s` (`Measure.le_map_apply`), so a measurable `f` with `μ.map f = ν` carries `≺` forward.
5. **Commutation (target 3), consumer check (vii).** `STLK`, `STLmax`, `STDecay`, `STDecayStrong`, `STLocalMax`, `STLocalEntry`, `STExp2` at `(sz.comp φ, E∘φ, τ∘φ)` unfold to `Prec` with index `U' j = U (φ j)` (including the subtype `{p // lam n ^ 2 ≤ 1 - τ n}` at `lam (φ j)`), `ξ' j u (reindex ω) = ξ (φ j) u ω` because `Gt/Lloop/STGM` read `ω` only through `seqHflow (φ j)`/`slice (φ j)`; `STKloop`, `STWB`, `Bctl`, `ellT`, `STblk` read `sz` only through `L, W, lam`; `STExp2`'s left side is `∫ Lloop … d(seqP)`, transferred by item 3 with `Lloop_reindex`. `STFlow = Admissible ∧ ∀ n, locDomain`, `STConStInd = ∀ᶠ n, Bctl n (t n)^𝔠d ≤ (1-t n)/(1-s n) ∧ … < 1`, with `Bctl` pulled back by `rfl`.

### Verdicts

| Target | Verdict | Reason |
|---|---|---|
| 1 (`comp`, field lemmas, 6 transfers) | PASS | hypotheses `Tendsto φ atTop atTop` suffice; instances 1-4 verified numerically above |
| 2 (`reindex`, `measurePreserving_reindex`, exact image law, `integral_reindex`) | PASS | arguments 1-3; the pins `infinitePi_preimage_comp_pin` and `integral_infinitePi_comp_pin` are true statements (probability measures, `f` injective, all sets and integrands) |
| 3 (13 commutation lemmas, `integral_Lloop_reindex`) | PASS | argument 5 |
| 4 (`Prec_comp_iff`, `PrecPT_comp_iff`, `Whp_comp_iff`, `Prec_comp`) | PASS | arguments 2-4 with `Injective φ` / `StrictMono φ` |
| 5 (`map_iff`, `of_map`, `subseq`, `iff_cover`, `nth_cover`) | PASS | argument 4 |
| 6 (law-generic and model-law gluing composites) | PASS | `map_iff` per `k` plus `iff_cover`; law hypothesis from item 1 and 2 (instances 6, 9) |

## (b) Script output
### b.1 Build, hygiene, diff
```
$ date -u; git log -2 --format='%h %cI %an'; git diff --stat main...t/T2206
Mon Oct  5 19:55:27 UTC 2026
ed7841f 2026-10-05T12:52:00-07:00 Jun Yin
882d39d 2026-10-05T12:47:54-07:00 Jun Yin
 RBM3D/Induction/SizesComp.lean | 812 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 812 insertions(+)
```
```
$ lake build RBM3D.Induction.SizesComp 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3316 jobs).
```
```
$ lake build 2>&1 | tail -2   # whole worktree at ed7841f (started 19:52:45 UTC); root import of the new module is the hub's
Build completed successfully (4009 jobs).
exit=0
```
```
$ wc -l RBM3D/Induction/SizesComp.lean; grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/SizesComp.lean
     812 RBM3D/Induction/SizesComp.lean
0
```
### b.2 `#print axioms` of all 76 public declarations (Axioms.lean: one `#print axioms` per name; grouped; prefixes Sizes./RBM.Gauss. dropped, I. = SizesCompInst)
```
$ lake env lean Axioms.lean
[propext, Classical.choice, Quot.sound]: 75 declarations
  comp, comp_L, comp_W, comp_lam, comp_size, withLam_comp, comp_locDomain, comp_sizeTendsto, comp_bandwidth, comp_WO, comp_admissible, STFlow_comp,
  STConStInd_comp, infinitePi_preimage_comp, integral_infinitePi_comp, reindexCoord, reindexCoord_injective, reindex, reindex_eq, measurable_reindex,
  seqP_reindex_preimage, seqP_withLam_reindex_preimage, measurePreserving_reindex, integral_reindex, slice_reindex, seqXmat_reindex, seqHflow_reindex,
  Gt_reindex, Lloop_reindex, STGM_reindex, STKloop_comp, Bctl_comp, STWB_comp, STblk_comp, ellT_comp, STflowE_comp, integral_Lloop_reindex,
  R.StochDomAt.map_iff, R.StochDomAt.of_map, R.StochDomAt.subseq, R.StochDomAt.iff_cover, R.Path.PerTimeDomAt.map_iff, R.Path.PerTimeDomAt.subseq,
  R.Path.PerTimeDomAt.iff_cover, HighProbAt.map_iff, HighProbAt.subseq, HighProbAt.iff_cover, R.nth_cover, Prec_comp_iff, PrecPT_comp_iff,
  Whp_comp_iff, Prec_comp, stochDomAt_iff_comp_cover, perTimeDomAt_iff_comp_cover, highProbAt_iff_comp_cover, Prec_iff_comp_cover,
  PrecPT_iff_comp_cover, Whp_iff_comp_cover, I.two_mul_tendsto, I.inst_comp_values, I.inst_comp_admissible, I.inst_flow_comp, I.inst_conStInd_comp,
  I.inst_reindex_mp, I.inst_reindex_BA, I.inst_STLK_comp, I.inst_STExp2_comp, I.parity_infinite, I.inst_STLK_parity, I.inst_Prec_comp_iff,
  I.inst_PrecPT_Whp_comp_iff, I.inst_of_map, I.inst_subseq, I.inst_nth_cover, I.inst_parity_PrecPT_Whp
[propext, Quot.sound]: 1 declarations
  I.two_mul_strictMono
```
### b.3 Statements of the main targets (script extracts the text up to `:=` from the file; `variable {d : ℕ} (sz : Sizes d)` supplies the leading binders)
```
theorem infinitePi_preimage_comp (hf : Function.Injective f) (s : Set (∀ a, X (f a))) : Measure.infinitePi μ ((fun (ω : ∀ i, X i) (a
    : α) => ω (f a)) ⁻¹' s) = Measure.infinitePi (fun a => μ (f a)) s
theorem integral_infinitePi_comp (hf : Function.Injective f) {E : Type u'} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : (∀ a, X (f
    a)) → E) : ∫ ω : (∀ i, X i), g (fun a => ω (f a)) ∂(Measure.infinitePi μ) = ∫ y, g y ∂(Measure.infinitePi fun a => μ (f a))
theorem seqP_withLam_reindex_preimage (φ : ℕ → ℕ) (g : ℕ → ℝ) (hφ : Function.Injective φ) (s : Set (SeqΩ ((sz.comp φ).withLam fun j
    => g (φ j)))) : seqP (sz.withLam g) (reindex sz φ ⁻¹' s) = seqP ((sz.comp φ).withLam fun j => g (φ j)) s
theorem measurePreserving_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ) : MeasurePreserving (reindex sz φ) (seqP sz) (seqP
    (sz.comp φ))
theorem Prec_comp_iff (φ : ℕ → ℕ) (hφ : Function.Injective φ) {U : ℕ → Type u} (ξ ζ : ∀ j, U j → SeqΩ (sz.comp φ) → ℝ) : Prec
    (sz.comp φ) ξ ζ ↔ RBM.StochDomAt (seqP sz) (fun j => sz.size (φ j)) (U := U) (fun j u ω => ξ j u (reindex sz φ ω)) (fun j u ω =>
    ζ j u (reindex sz φ ω))
theorem Prec_comp (φ : ℕ → ℕ) (hφ : StrictMono φ) {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) (ξ' ζ' : ∀ j, U (φ j) → SeqΩ
    (sz.comp φ) → ℝ) (hξ : ∀ j u ω, ξ' j u (reindex sz φ ω) = ξ (φ j) u ω) (hζ : ∀ j u ω, ζ' j u (reindex sz φ ω) = ζ (φ j) u ω) (h
    : Prec sz ξ ζ) : Prec (sz.comp φ) (U := fun j => U (φ j)) ξ' ζ'
theorem nth_cover {ι : Type w} [Finite ι] (c : ℕ → ι) : ∀ᶠ n in atTop, ∃ i : {i : ι // {m : ℕ | c m = i}.Infinite}, n ∈ Set.range
    (Nat.nth (fun m => c m = i.1))
theorem iff_cover {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) {U : ℕ → Type v} (ξ ζ : ∀ l, U l → Ω₀ → ℝ) {ι :
    Type w} [Finite ι] (φ : ι → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    RBM.StochDomAt μ size ξ ζ ↔ ∀ k, RBM.StochDomAt μ (fun j => size (φ k j)) (U := fun j => U (φ k j)) (fun j => ξ (φ k j)) (fun j
    => ζ (φ k j))
theorem stochDomAt_iff_comp_cover (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ) (ν : ∀ k, Measure (SeqΩ (sz.comp
    (φ k)))) (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (hlaw : ∀ k (s : Set (SeqΩ (sz.comp (φ
    k)))), μ (reindex sz (φ k) ⁻¹' s) = ν k s) {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ
    (sz.comp (φ k)) → ℝ) (hξ : ∀ k j u ω, ξ' k j u (reindex sz (φ k) ω) = ξ (φ k j) u ω) (hζ : ∀ k j u ω, ζ' k j u (reindex sz (φ k)
    ω) = ζ (φ k j) u ω) : RBM.StochDomAt μ sz.size ξ ζ ↔ ∀ k, RBM.StochDomAt (ν k) (sz.comp (φ k)).size (U := fun j => U (φ k j))
    (ξ' k) (ζ' k)
```
### b.4 Check-file equality: sections 1-3 of the check file + `example : pin := @library_theorem` for all 53 pins + the two vocabulary `rfl`s
```
$ cat genpins.py   (12 lines)
import re
C="/Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2206-check.lean"; S=open(__file__).name.rsplit("/",1)[0]+"/"
chk=open(C).read(); body=chk[:chk.index("/-! ## 4. Instance statements")].replace("import RBM3D\n","import RBM3D\nimport RBM3D.Induction.SizesComp\n",1)
pins=re.findall(r"^def (\w+_pin) : Prop",body,re.M)
sp={"StochDomAt_map_iff":"RBM.StochDomAt.map_iff","PerTimeDomAt_map_iff":"RBM.Path.PerTimeDomAt.map_iff","HighProbAt_map_iff":"RBM.Gauss.HighProbAt.map_iff","StochDomAt_of_map":"RBM.StochDomAt.of_map","nth_cover":"RBM.nth_cover","infinitePi_preimage_comp":"RBM.Gauss.infinitePi_preimage_comp","integral_infinitePi_comp":"RBM.Gauss.integral_infinitePi_comp"}
for a,ns in (("StochDomAt","RBM.StochDomAt"),("PerTimeDomAt","RBM.Path.PerTimeDomAt"),("HighProbAt","RBM.Gauss.HighProbAt")):
    for t in ("subseq","iff_cover"): sp[f"{a}_{t}"]=f"{ns}.{t}"
lib=lambda p: sp.get(p[:-4],"RBM.Gauss.Sizes."+p[:-4])
out=body+"\nend RBM.Gauss.Sizes.T2206Check\n\nend\n\n"
out+="example : @RBM.Gauss.Sizes.T2206Check.comp_voc = @RBM.Gauss.Sizes.comp := rfl\nexample : @RBM.Gauss.Sizes.T2206Check.reindex_voc = @RBM.Gauss.Sizes.reindex := rfl\n"
out+="".join(f"example : RBM.Gauss.Sizes.T2206Check.{p} := @{lib(p)}\n" for p in pins)
open(S+"PinCheck.lean","w").write(out); print(len(pins),"pins")
```
```
$ python3 genpins.py; lake env lean PinCheck.lean > PinCheck.out 2>&1; echo exit=$?; grep -c '^example' PinCheck.lean; grep -c error PinCheck.out; sed -n '471p;523p' PinCheck.lean
53 pins
exit=0
55
0
example : RBM.Gauss.Sizes.T2206Check.comp_L_pin := @RBM.Gauss.Sizes.comp_L
example : RBM.Gauss.Sizes.T2206Check.Whp_iff_comp_cover_pin := @RBM.Gauss.Sizes.Whp_iff_comp_cover
```
### b.5 Compiled nonempty instances (namespace `RBM.Gauss.SizesCompInst`, `d = 3`, `sz0`, `φ = (2 * ·)`; 9 ticket instances + 6 extra)
```
$ python3 geninst.py; lake env lean InstCheck.lean > InstCheck.out 2>&1; echo exit=$?; grep -c '^example' InstCheck.lean; grep -c error InstCheck.out   # each of the 9 check-file section-4 statements := the library instance
9 instance statements
exit=0
9
0
```
Instances 7, 8, 9 and `of_map` (the others, and their check-file equality, are in the run above); the premises left open are stochastic `≺` statements:
```
theorem inst_STLK_comp : STLK sz0 (STflowE z0) sInst → STLK (sz0.comp (2 * ·)) (STflowE (fun j => z0 (2 * j))) (fun j => sInst (2 *
    j))
theorem inst_STExp2_comp : STExp2 sz0 (STflowE z0) sInst → STExp2 (sz0.comp (2 * ·)) (STflowE (fun j => z0 (2 * j))) (fun j => sInst
    (2 * j))
theorem inst_STLK_parity : (∀ r : Fin 2, STLK (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ)))) (fun j => STflowE z0 (Nat.nth (fun m
    => m % 2 = (r : ℕ)) j)) (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j))) → STLK sz0 (STflowE z0) sInst
theorem inst_of_map (ξ ζ : ℕ → Unit → SeqΩ (sz0.comp (2 * ·)) → ℝ) (h : Prec (sz0.comp (2 * ·)) ξ ζ) : RBM.StochDomAt (seqP sz0)
    (sz0.comp (2 * ·)).size (U := fun _ => Unit) (fun l u ω => ξ l u (reindex sz0 (2 * ·) ω)) (fun l u ω => ζ l u (reindex sz0 (2 *
    ·) ω))
```
Extra instances: `inst_of_map` (premise `Prec (sz0.comp (2 * ·)) ξ ζ` for arbitrary `ξ ζ`; satisfiable: `inst_Prec_comp_iff`) and five with the zero family `ξ = 0 ≺ ζ = 1`, no premise open: `inst_Prec_comp_iff`, `inst_PrecPT_Whp_comp_iff`, `inst_subseq` (3 predicates), `inst_nth_cover` (parity partition, 2 infinite classes), `inst_parity_PrecPT_Whp` (`PrecPT_iff_comp_cover`, `Whp_iff_comp_cover`).
### b.6 Name clash
```
$ python3 nameclash.py
76 new public declarations, 70 distinct short names; scanned 248 files of main cda3bb2
declared on main with the same bare short name: []
declared on main as <Prefix>.<short name> (other namespace): [('FinDepOffRow.comp', 'RBM3D/Green/FlucVanish.lean'), ('FinDepOffRows.comp', 'RBM3D/Green/MinorGoodLe.lean')]
exact full-name clash (RBM.Gauss.* / RBM.* names written in full): []
```
### b.7 Registry pre-check (temporary uncommitted scratch file outside the repo)
```
$ printf 'import RBM3D\nimport RBM3D.Induction.SizesComp\n#assert_rbm_axioms\n' > Registry.lean; lake env lean Registry.lean > Registry.out 2>&1; echo exit=$?; head -3 Registry.out; tail -1 Registry.out
exit=0
axiom audit: 6134 theorems, 2119 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
non-vacuity certificates: 0 of 126 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
```

### b.8 Narrative (route, hypotheses, size, findings)

* **Stage 1b**: first `date -u` of the stage Mon Oct 5 19:34:48 UTC 2026; commits `882d39d`, `ed7841f` on `t/T2206` (b.1); only `RBM3D/Induction/SizesComp.lean` changed.
* **Route of preflight (ii)** (section (a) item 2): product splitting. `sizesComp_split : Π_ι X ≃ᵐ Π_α X(f ·) × Π_{¬ range f} X` is
  `MeasurableEquiv.piEquivPiSubtypeProd` then the inverse of `piCongrLeft` along `Equiv.ofInjective`; its value at `ω` is `(ω ∘ f, ω|_{¬ range f})` by `rfl`.
  Independence of the two coordinate blocks: `iIndepFun_infinitePi` + `indep_iSup_of_disjoint` + `indep_of_indep_of_le_left/right` (the `comap` of each block map is `≤ ⨆ i ∈ block, comap (eval i)`).
  Joint law: `IndepFun.map_prod_eq_prod_map_map` with marginals `map_infinitePi_infinitePi_of_inj`, `infinitePi_map_restrict'`. Every set: `MeasurableEquiv.map_apply` + `Measure.prod_prod`
  (second factor `univ`); every integrand: `integral_map_equiv` + `integral_fun_fst`. The generic section `InfinitePiComp` is file lines 114-202 (89 lines), below the preflight's 400-line stop.
* **Size**: 812 lines (b.1) against the ticket's 700 / 950 / 1300 (lo / central / hi), below 1500.
* **Hypothesis table** (as pinned): field lemmas, `measurable_reindex`, the 12 `rfl` commutation lemmas: none. `comp_sizeTendsto`, `comp_bandwidth`, `comp_WO`, `comp_admissible`, `STFlow_comp`,
  `STConStInd_comp`, the three `subseq`: `Tendsto φ atTop atTop`. `measurePreserving_reindex`, `seqP_reindex_preimage`, `seqP_withLam_reindex_preimage`, `integral_reindex`, `integral_Lloop_reindex`,
  `*_comp_iff`, the two generic image laws: `Function.Injective φ` (resp. `f`). `Prec_comp`, the three `iff_cover`, the six `*_iff_comp_cover`: `StrictMono (φ k)`, `Finite ι`, `∀ᶠ n, ∃ k, n ∈ range (φ k)`.
  No pin was changed, weakened or given an extra hypothesis (b.4).
* **Target 3**: the 12 expected-`rfl` lemmas (`slice`, `seqXmat`, `seqHflow`, `Gt`, `Lloop`, `STGM` `_reindex`; `STKloop`, `Bctl`, `STWB`, `STblk`, `ellT`, `STflowE` `_comp`) are all `rfl`; no fallback proof was needed.
  The 13th, `integral_Lloop_reindex` (hypothesis `Injective φ`), is `integral_reindex` + `integral_congr_ae` with `Lloop_reindex`; `RBM3D.Path.Walk` is not imported, `walk_measurable_Lloop` is not used.
* **BA law**: `seqP_withLam_reindex_preimage` is `seqP_reindex_preimage (sz.withLam g) φ hφ s` (`SeqΩ` does not see `lam`; `(sz.withLam g).comp φ = (sz.comp φ).withLam (g ∘ φ)` is `rfl`), for every `g`.
* **Finding 1 (name clash, found by the compiler)**: `RBM.Gauss.splitEquiv` already exists (`RBM3D/Defs/Sizes.lean:87`, another object), so the private helpers carry the prefix `sizesComp_`;
  `RBM.Gauss.highProbAt_univ` (`RBM3D/Gauss/DominationAt.lean:160`) is reused, not redeclared.
* **Finding 2 (for the BA analogues and the regime assembly)**: the first version of `inst_STExp2_comp` closed the implication with an `exact` against a `Prec_comp` term at `sz0`; the elaborator stopped with
  `(deterministic) timeout at whnf` (200000 heartbeats). Stating the transfer for an abstract `sz` (private `sizesComp_STExp2_comp`) and applying it at `sz0` compiles at once. The cause was not isolated
  (presumably unfolding of the literal fields of `sz0`). `inst_STLK_comp`, with explicit `rfl` arguments, did not need the workaround.
* **Finding 3 (Mathlib v4.34.0)**: `Nat.nth` lemmas are stated for `Set.ofPred p` (`{m | p m}` elaborates to it); `Set.mem_setOf_eq` is deprecated, `Set.mem_ofPred_eq` is used.
* **Section (a)**: no correction needed (nothing in it was contradicted; `integral_fun_fst` is used as (a) item 3 says).
* **Hub**: root import to add after the last `import` line of `RBM3D.lean`: `import RBM3D.Induction.SizesComp`. No `Prop`-valued definition is introduced (b.7): no registry line, no `RBM3D/Test/Axioms.lean` edit.
* **Special cases**: instances 7-9 and `inst_of_map` are at `sz0` with stochastic premises; predicate-level transfers of the seven `STMainInd` predicates as general theorems are ticket "Not targets" and are not provided.

## (c) Verified Mathlib names (all present: `#check` run `Names.lean`, exit 0, no error line; file:line by `grep -n`)

`Measure.map_infinitePi_infinitePi_of_inj` (`Probability/Independence/InfinitePi.lean:142`), `iIndepFun_infinitePi` (`:125`), `iIndepFun_iff_iIndep` (`Probability/Independence/Basic.lean:232`),
`indep_iSup_of_disjoint` (`:511`), `indep_of_indep_of_le_left` (`:371`), `indep_of_indep_of_le_right` (`:375`), `IndepFun.map_prod_eq_prod_map_map` (`:708`, alias),
`Measure.infinitePi_map_restrict'` (`Probability/ProductMeasure.lean:413`), `MeasurableEquiv.piEquivPiSubtypeProd` (`MeasureTheory/MeasurableSpace/Embedding.lean:580`), `MeasurableEquiv.piCongrLeft` (`:495`),
`MeasurableEquiv.map_apply` (`MeasureTheory/Measure/Map.lean:306`, every set), `Measure.le_map_apply` (`:218`), `Measure.prod_prod` (`MeasureTheory/Measure/Prod.lean:231`),
`integral_map_equiv` (`MeasureTheory/Integral/Bochner/Basic.lean:1100`), `integral_fun_fst` (`MeasureTheory/Integral/Prod.lean:548`), `Filter.eventually_all` (`Order/Filter/Finite.lean:247`),
`Nat.cofinite_eq_atTop` (`Order/Filter/Cofinite.lean:207`), `Set.Finite.eventually_cofinite_notMem` (`:85`), `Nat.nth_strictMono` (`Data/Nat/Nth.lean:145`), `Nat.range_nth_of_infinite` (`:161`),
`StrictMono.tendsto_atTop` (`Order/Filter/AtTopBot/Tendsto.lean:84`), `Set.infinite_of_injective_forall_mem` (`Data/Set/Finite/Basic.lean:907`),
`MeasurableSpace.comap_iSup` (`MeasureTheory/MeasurableSpace/Basic.lean:136`), `MeasurableSpace.comap_comp` (`:104`).
Verified absent: an infinite-index-set analogue of `iIndepFun.indepFun_finset` (`grep -rn "indepFun_set\|iIndepFun.indepFun_of_disjoint\|indepFun_iSup" Probability/Independence/Basic.lean` printed nothing; the proof uses `indep_iSup_of_disjoint` on the `comap` sigma-algebras).

## (d) Open issues and paper-delta candidates

* No open obstruction: every target is built, committed on `t/T2206`, and has an instance (b.5).
* `T2206a` (math): `(stoch_domination)` (`1_2:227-231`) along a sequence is stable under subsequences and is recovered from finitely many subsequences covering all large `n`; `lem:main_ind`
  (`1_2:1256-1330`) splits `[s, t]` at `1-g^2`, `1-g^2/L^2`, `1-g^2/L^d` in an `n`-dependent order, handled formally by regime classes with `Prec_iff_comp_cover` + `nth_cover`; the paper uses this tacitly (as the ticket proposes).
* `T2206b` (Lean-only): the model law of a subsequence of sizes is the image of `seqP` under the coordinate reindexing for every set and every integrand (`seqP_reindex_preimage`, `integral_reindex`),
  including the block Anderson law (`seqP_withLam_reindex_preimage`).
* `T2206c` (Lean-only, tooling): Finding 2 (state predicate-level transfers for abstract `sz`).
* For the regime assembly: the commutation hypotheses `ξ' k j u (reindex ω) = ξ (φ k j) u ω` of `Prec_iff_comp_cover` for the seven `STMainInd` predicates follow from the `rfl` lemmas of target 3
  (`inst_STLK_comp` shows the pattern); `STDecayStrong`'s subtype index at `sz.comp φ` is not exercised by an instance here.
