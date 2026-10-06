Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 05:08 UTC 2026

Targets restated only as needed: `STExpIntQConcl'` (σ₁≠σ₂, regime (i)) by route (d): `ϑ* = QopAlgebra_mollifier d L 1 λ`, `R_s = (𝒫f_s)(ϑ_s−ϑ*_s)`, bound for `ϑ*`, back-transfer. Notation as the ticket: `x_v=1-v`, `B_v=Bctl n v`, `T_v=STExpTarget`, `N=(WL)^d`, `e=1+|ε|`, `c₀=√(2κ)/2`.

### (i) Exponent table

| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | `𝔠d` | `1/(100 d)` | `0<𝔠d≤1/100` (STIngR6) and `d·𝔠d<1` (kernel `hdc`) | `d𝔠d=1/100` for all `d≥3`. **Ticket's "e.g. 1/100" fails for `d≥100`** (`d𝔠d=1`); `1/(100 d)` is what `stExpIniI'_holds` uses (`ExpIniI.lean:1110-1113`); instance `1/300` |
| 2 | mollifier constants | `C*=(1+40d)6^d`, `c=1/2` (m=1) | `0<C*`, `0<c` (what `STExpWardIConcl'` needs); `QopAlgebra_mollifier_props` gives `c=1/2`; `1/4` is only the exponent of `…_derivDecay` | `d=3`: `C*=26136`; both positive |
| 3 | kernel ratio² | `≤4` | `ratio=(λ²+x_v)/(λ²+x_u)≤2` for `s≤v≤u<1`, `x_s≤λ²` (`expIntI_ratio_le`), at `v=s` | instance `ratio²=1.121`, slack `×3.57` |
| 4 | `K` | `1/𝔠+d` | `L^d≤W^K`, `x_v⁻¹≤W^K` (`v∈[s,t]`): `L^d≤N≤W^{1/𝔠}` (Bandwidth); regime (i): `x_v⁻¹≤L²/λ²`, `λ⁻²≤W^{d-2𝔡}≤W^d` (`(eq:WO)`), `L²≤L^d` | instance `K=9`: `L^d=64`, `x_v⁻¹≤16` |
| 5 | `C₀` (sup-norm envelope) | `(4e+5)/𝔠` | `‖f_v‖,‖𝒫f_v‖,‖f−𝒬*f‖,‖Θf_v‖,‖D_v‖ ≤ W^{C₀}` (row 5a-5e) | instance `C₀=56.4`; largest needed exponent `16.5` (table below) |
| 5a | `‖f_v‖` | `≤(4N^e/c₀)²+4N^e` | `‖f‖≤η_v⁻²+‖𝒦‖`; `η_v=x_v Im m(E)≥x_v c₀` (bulk, `st6_flowE_le`, `st6_mE_im_ge`); `x_v⁻¹≤(1-lemT)⁻¹≤4N^e` (`expIniI_inv_one_sub_le`, any `u≤lemT`); `‖𝒦‖≤x_t⁻¹` | `≤N^{2e+4}`; precedent `expIniI_env_poly` (`ExpIniI.lean:564`, private, time `s` only) |
| 5b | `‖𝒫f‖,‖f−𝒬*f‖` | `≤L^d‖f‖`, `≤C*L^d‖f‖` | `|ϑ*|≤C*` (clause 2, `ℓ≥1`) | `N^{2e+5}`·const |
| 5c | `‖Θf_v‖` | `≤2x_v⁻¹‖f‖` | row sums of `SB·Θ` (`norm_Theta_le`, `Σ_b SB=1`) | `N^{3e+4}`·const; any polynomial suffices |
| 5d | `‖D_v‖` | `≤N·4N^e·2(8N^e)^{5/2}` | `STExpDriftHiConcl` at `τ=1` (`st6_prec_det_iff`), `B≤2x_v⁻¹` (`expIniI_Bctl_le`) | `N^{2+3.5e}` ≤ `N^{4e+5}` |
| 6 | decay indices | `R`: `(ε',D'+1)` each; `Θ`: input `(ε'/2, D'+K+1)` | difference of two decays `≤2W^{-(D'+1)}≤W^{-D'}` needs `W≥2`; `QopDecay_STthetaOp_fastDecay` output `(2ε,D-(K+1))`; all need `W≥W₀(d,K,C₀,ε',D')`, `0<λ≤𝔡⁻¹` | `W→∞`, `0<λ_n` eventually from `(eq:WO)` |
| 7 | `ϑ*` source decay at `ℓ_v` | `EKFastDecay λ v W ε' D'` | `𝒬*D`: `D−(D−𝒬*D)` (`STExpDriftDecayConcl` deterministic, `stQop_sub_fastDecay`); commutator `Θ(f−𝒬*f)−(Θf−𝒬*Θf)` (`QopAlgebra_ThetaN_sub`); `(𝒫f)∂ϑ*` (`QopDecay_deriv_fastDecay`, `B=𝒫f_v`, no `L^d` needed) | eventual, uniform `v∈[s,t]`, all `σ` |
| 8 | sup bound of `A*_v` | `X_v=x_v⁻¹(B^{11/5}+B^{5/2}+B³)` | `lem_+Q` on `D_v` (`C_n` indep. of `ε,D`; `ε=τ/(3C_n)`, `W^{C_nε}≤N^{τ/3}`, `W≤N`; tail `W^{-D+C_n}≤N^{-b}≤X_v`); commutator+`(𝒫f)∂ϑ*` by Ward conjunct 2 for `ϑ*` | `X_v≥x_v⁻¹B³≥N^{-b}` (T2239 §4 pattern) |
| 9 | integral | `∫_s^u 4X_v≤32 T_u log L` | `B_v≤B_u`, `B^{11/5}+B^{5/2}≤3T` (`expIntII_rates_le_target`), `B³≤T`, `∫x_v⁻¹=log((1-s)/(1-u))≤2log L` | instance (below): `8.6e-205 ≤ 1.6e-203`, slack `×18` |
| 10 | Prec absorptions | target 6: `8`; 7: `32 log L`; 8: `3`; 9: `3` | each `≤N^{τ/2}` eventually (`SizeTendsto`, `expIntII_log_eventually`) | eventual, no condition on `τ` |
| 11 | `(con_st_ind)` | `B_t^{𝔠d}≤x_t/x_s<1` (eventual hypothesis) | `W³≥Bparam(t)·(x_s/x_t)^{1/𝔠d}` | instance: `W≥1.3e30` for `𝔠d=1/300` (`1.1e10` for `1/100`); see (ii) |

Time/regime lines (ticket §29/§45 O2, one each): (1) `0≤s≤v≤u≤t≤lemT<1` used for `Duhamel`, `x_v>0`; (2) regime (i) used for `x_v⁻¹≤L²/λ²`, kernel window, `∫x⁻¹≤2log L`, rates (`λ²/L^d≤x_u` since `L^d≥L²`); (3) `L^d≤W^K` and `x_v⁻¹≤W^K` derived (row 4), never assumed; (4) hypotheses `∀n`, conclusions eventual; `ϑ`'s clauses eventual only, so guards (below); (5) uniformity in `u` only inside `expIntI_kernel_unif`; (6) `0<λ_n≤𝔡⁻¹` eventually from `(eq:WO)`, `|E_n|≤2−κ` for all `n`; (7) one scale `N`.

Bookkeeping hazards of the ticket, resolved on paper:
- **(iv) kernel interface.** `hcase` is `∀ n v, EKSumZero (𝒜 n v)`. Target 6: `𝒜 n v := if (0<λ_n ∧ STMollifierProps … (ϑ n) ∧ STMollifierProps … (ϑ* n) ∧ v=s n) then R_{s n} else 0`. The guard must carry `ϑ*`'s clauses too (target 3 is stated with both `STMollifierProps`), or clause 1 of `ϑ*` for every `n` (`QopAlgebra_mollifier_sum` holds for all real `g,t`). `X n v := 2B_{s n}³` (constant in `v`), `hbd` from Ward conjunct 1 at the index `⟨s n,·⟩∈TimeIcc` for `ϑ` and `ϑ*` (`‖R‖≤‖(𝒫f)ϑ‖+‖(𝒫f)ϑ*‖`). Target 7: `𝒜 n v := if (0<λ_n ∧ s n≤v ∧ v≤t n) then A*_v else 0`; target 4 needs only `0<λ_n`, `0≤v<1` (guard), `|E_n|≤2` (all `n`, row 6). Guards hold eventually on the integration range, so the integrands agree.
- **Time scale.** `R_s` decays at `ℓ_s`; the guard `v=s n` makes `hdec` ask at `ℓ_{s n}`, so `RBM.ellT_mono` is not needed.
- **Finite unions.** `σ` ranges over four values; the kernel lemma is per `σ`, combine by a finite intersection of eventualities. `STSigMixed σ` is `σ 0≠σ 1` by `def`, matching the subtype of `STExpWardIConcl'`.
- **Assembly.** `G=F+B³` (6), `+T` (7), `+B³` (8): `F+2B³+T ≤ F+3T ≤ 3(F+T)` (`B³≤T`), absorbed by row 10.

### (ii) One concrete nondegenerate instance

Data: `d=3`, `szB` (`L=4, λ=1, W_n=n+4`), `zB=1/2+i/64`, flow `(κ,ε,𝔠,𝔡)=(1/10,1/10,1/6,1/10)`, `s=7/8`, `t=15/16` (`t≤31/32≤lemT(zB)`, `Step34Pins.lean:789`), `𝔠d=1/300`; `ϑ*` as above, `ϑ`: a second admissible mollifier. Command and output (script `…/scratchpad/T2257/pre2.py`; the large-`W` instance `W=10^31`, i.e. `n=10^31−4`, satisfies every hypothesis at once):

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2257/pre2.py
regime(i): lam^2/L^2=0.0625<=1-t=0.0625 ; 1-s=0.125<=lam^2=1.0 ; t<=31/32<=lemT ; d*c_d=0.01 ; C*=26136, c=1/2 ; ratio=1.05882 ratio^2=1.12111<=4
K=1/c+d=9.0  C0=(4e+5)/c=56.4  e=1+|eps|=1.1  c0=sqrt(2k)/2=0.22361
W=1.0e+6: N=10^19.806 | log_W: f=7.68 Pf=10.98 f-Q*f=11.72 Thf=11.46 D=16.54 <= C0 | B_t=1.19e-18 T_t=3.56e-40 B^3<=T | int4X=8.58e-40<=32 T log L=1.58e-38 | (con_st_ind) B_t^{1/300}=0.8715<=1/2: False | others ok: True
W=1.0e+31: N=10^94.806 | log_W: f=6.809 Pf=9.867 f-Q*f=10.01 Thf=10.2 D=14.93 <= C0 | B_t=1.19e-93 T_t=3.56e-205 B^3<=T | int4X=8.58e-205<=32 T log L=1.58e-203 | (con_st_ind) B_t^{1/300}=0.4901<=1/2: True | others ok: True
(con_st_ind) needs W >= (Bparam(t) 2^{1/c_d})^{1/3} = 1.344e+30 (c_d=0.00333)
(con_st_ind) needs W >= (Bparam(t) 2^{1/c_d})^{1/3} = 1.147e+10 (c_d=0.01)
c_d=1/100 gives d*c_d>=1 at d=100; c_d=1/(100 d) gives d*c_d=1/100 for every d>=3
algebra n=64: |P theta*-1|=2.2e-16  target2 err=8.9e-16  target3 |P R|=4.2e-15  |P Q f|=1.1e-14  |P d_t theta*|=2.6e-10
```

The script asserts (`ok`): Bandwidth `N^{1/6}≤W`, `(eq:WO)` `W^{-7/5}≤λ=1≤10`, `L^d=64≤W^9`, `x_v⁻¹=16≤W^9`, `B_s≤B_t`, `B_t³≤T_t`, `B^{11/5}+B^{5/2}≤3T`, `∫_s^t(1−v)⁻¹=log 2≤2log 4`. The last line checks on `Z_4^3` (64 points, explicit `ϑ*_t(a)=exp(−u|a₁−a₀|₁)/Z₁(u)³`, `u=(1+g/√(1−t))⁻¹+1/L`, and a second normalized mollifier plus a zero-sum oscillation) the identities of targets 2 and 3, `𝒫𝒬=0`, `𝒫∂_tϑ*=0` (finite difference).

External hypothesis (TEAM §8 lesson 14): the only asymptotic hypothesis not introduced by this ticket is `STConStInd` (`(con_st_ind)`, `1_2:1296`) at constant times. Limit computation: `B_t=Bparam(t)W⁻³=(16/17+1/4)W⁻³→0`, so `B_t^{𝔠d}→0<1/2=x_t/x_s` for every `𝔠d>0` (`Step34Inst.conStInd_const`, merged). It forces `W≥1.3e30` at `𝔠d=1/300` (row 11); this is intrinsic to the hypothesis (fixed `x_t/x_s=1/2`, `B_t~W⁻³`, `𝔠d≤1/100`), not to T2257. The other hypotheses already hold at `W=10^6` (the `others ok: True` flag of the `W=1.0e+6` line).

### Verdicts

- Step 3 and step 5 (ticket (v)): (a) `STExpWardIConcl'` conjunct 1 at `u=s` (`s n∈TimeIcc s t n`) bounds `‖(𝒫f_s)ϑ_s‖` and `‖(𝒫f_s)ϑ*_s‖` by `B_s³`, for the index set `σ₁≠σ₂` (= `STSigMixed`), `ϑ` and `ϑ*` each admissible with `0<C,0<c`; (b) `R_s` and the back-transfer use only `ϑ_s`, `ϑ_u`; `∂ϑ*` appears only inside the `ϑ*` source (Ward conjunct 2 for `ϑ*`); (c) ratio² `≤4` applies at `v=s` (row 3). **PASS (transfer); fallback (b) and `T2257a` not triggered.**
- Targets 1 `expIntIQ_star_props`, 2 `expIntIQ_Qop_sub`, 3 `expIntIQ_diff_sumZero`, 4 `expIntIQ_src_sumZero`, 5 `expIntIQ_src_decay`, 6 `expIntIQ_ini`, 7 `expIntIQ_star_bound`, 8 `expIntIQ_back`, 9 `expIntIQ_concl`, 10 `stExpIntI'_holds`, 11 `stStep6I_of_LW`, 12 instances: **PASS** (all rows close; no hypothesis set empty).
- Findings for the dispatcher (none changes a statement): (1) `𝔠d` must be `1/(100 d)`, not `1/100` (row 1); (2) the guard of target 6 includes `ϑ*`'s clauses (iv); (3) envelope 5c `‖Θf‖≤2x⁻¹‖f‖` is not among the T2249 lemmas and needs a short private proof in stage 1b (any polynomial bound suffices, margin in the `W`-exponent about 40 at the instance); envelope 5a needs the pointwise-in-`v` copies of the private `ExpIniI` lemmas; (4) instance `inst_expIntI'_mixed` discharges `(con_st_ind)` by the limit lemma, its witness `n` is astronomical by nature (above).

## (a′) Preflight corrections — Tue Oct  6 05:56:47 UTC 2026
Verdicts of (a) stand (PASS; transfer; fallback (b) and `T2257a` not triggered). Entries of (a) that are not the value or route used (none changes a verdict):
- Row 1, finding 1: used `𝔠d = 1/(100 d)` (as `stExpIniI'_holds`); the ticket's "e.g. `1/100`" fails `d𝔠d < 1` at `d ≥ 100`.
- Row 4: `K = 1/𝔠` suffices (not `1/𝔠 + d`): `N = W^d L^d` exactly, `ilambda² W^d ≥ 1` (`st5_eventually_A_ge_one`), `L² ≤ L^d`, so in regime (i) `(1-v)⁻¹ ≤ L²/ilambda² ≤ N ≤ W^{1/𝔠}` (`expIntIQ_inv_le`); `L^d ≤ N`.
- Rows 5, 5a-5e: the envelope is a power of `N`, `C₀ = 6/𝔠` (not `(4e+5)/𝔠`): `‖f_v‖ ≤ N³` (`norm_Lloop_le` + `LemDecCalELip_STKloop_two_norm`, no copy of the private `ExpIniI` lemmas), `‖𝒫f‖ ≤ N⁵`, `‖(𝒫f)ϑ*‖ ≤ N⁶`, `‖Θf‖ ≤ 2N⁴` by the merged `B45_norm_ThetaN_le` (finding 3's "short private proof" is not needed), `‖D_v‖ ≤ N⁶`.
- Finding 2 (the guard of target 6 carries `ϑ*`'s clauses) is used as stated.

## (b) Script output (stage 1b), written Tue Oct  6 05:56:47 UTC 2026
Branch `t/T2257`, head `4d984b5` (base `a18620d`), worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2257`. `date -u` of the runs: Tue Oct  6 05:52:13 UTC 2026 → Tue Oct  6 05:53:15 UTC 2026 (module build, axioms, equality, pre-check, diffs); Tue Oct  6 05:53:22 UTC 2026 → Tue Oct  6 05:54:04 UTC 2026 (full build).

```
$ lake build RBM3D.Induction.ExpIntIQ 2>&1 | tail -3
✔ [3875/3875] Built RBM3D.Induction.ExpIntIQ (10s)
Build completed successfully (3875 jobs).
v1 exit 0
$ lake env lean axioms.lean     # `#print axioms` of the 23 public declarations: 12 in RBM.Gauss.Sizes, 11 in RBM.Gauss.Step6Inst
'RBM.Gauss.Sizes.expIntIQ_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_star_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_Qop_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_diff_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_src_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_src_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_ini' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_star_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_back' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expIntIQ_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpIntI'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep6I_of_LW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntI'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_star_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntI'_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_stStep6I_of_LW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_Qop_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_diff_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_src_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_src_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_ini' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_star_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expIntIQ_back' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/ExpIntIQ.lean   -> 0      (wc -l: 1545)
```

Targets 1-11 as in the file (script `stmts.py`: the text of each declaration up to `:=`, whitespace collapsed, wrapped at 230 columns):
```
def expIntIQ_star {d : ℕ} (sz : Sizes d) : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ
theorem expIntIQ_star_props (d : ℕ) (sz : Sizes d) (𝔡 : ℝ) (h : sz.WO 𝔡) : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2) (expIntIQ_star sz n)
theorem expIntIQ_Qop_sub (d L : ℕ) [NeZero L] (ϑ ϑ' : ℝ → (Fin 2 → Zd d L) → ℂ) (s : ℝ) (A : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) : STQop (d := d) ϑ' s A a = STQop (d := d) ϑ s A a + STPsum (d := d) A (a 0) * (ϑ s a - ϑ' s
    a)
theorem expIntIQ_diff_sumZero (d L : ℕ) [NeZero L] (g C c C' c' : ℝ) (ϑ ϑ' : ℝ → (Fin 2 → Zd d L) → ℂ) (h : STMollifierProps (d := d) g C c ϑ) (h' : STMollifierProps (d := d) g C' c' ϑ') (s : ℝ) (A : (Fin 2 → Zd d L) → ℂ) :
    EKSumZero (fun a : Fin 2 → Zd d L => STPsum (d := d) A (a 0) * (ϑ s a - ϑ' s a))
theorem expIntIQ_src_sumZero (d : ℕ) (_hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| ≤ 2) (hl : 0 < sz.lam n) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (σ : Fin 2 → Bool) : EKSumZero (STExpQsrc sz n E v σ (expIntIQ_star sz n))
theorem expIntIQ_src_decay (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (_hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (_hst : ∀ n, s n < t n) (htT : ∀ n,
    t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t) (hdd : STExpDriftDecayConcl sz (STflowE z) s t) (ε' D : ℝ) (hε' : 0 < ε') (hD : 0 < D) : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ :
    Fin 2 → Bool, EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (STExpQsrc sz n (STflowE z n) v σ (expIntIQ_star sz n))
theorem expIntIQ_ini (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 𝔠d : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hW : STExpWardIConcl' sz (STflowE z) s t) (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n))
    → ℂ) (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) (F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (hF : ∀ n p, 0 ≤ F n p) (hF1 : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖RBM.Ind.Ugen d (sz.L
    n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ) (STQop (d := d) (ϑ n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p)) : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ =>
    ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1 (s n) (p.1 : ℝ) (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p + sz.Bctl n (p.1 : ℝ) ^
    3)
theorem expIntIQ_star_bound (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 𝔠d : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0
    ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t) (hdd : STExpDriftDecayConcl sz (STflowE z) s t) (hW :
    STExpWardIConcl' sz (STflowE z) s t) (G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (_hG : ∀ n p, 0 ≤ G n p) (hG1 : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1
    (s n) (p.1 : ℝ) (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErr sz n (STflowE z n) (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => G n p)) : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖STQop (d := d)
    (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErr sz n (STflowE z n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖) (fun n p _ => G n p + STExpTarget sz n (p.1 : ℝ))
theorem expIntIQ_back (d : ℕ) (sz : Sizes d) (hsz : sz.SizeTendsto) (E s t : ℕ → ℝ) (_hst : ∀ n, s n < t n) (_ht1 : ∀ n, t n < 1) (hW : STExpWardIConcl' sz E s t) (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d
    (sz.L n)) → ℂ) (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) (hstar : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2) (expIntIQ_star sz n)) (G : ∀
    n, STIdx2P sz STSigMixed s t n → ℝ) (hG : ∀ n p, 0 ≤ G n p) (hG1 : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b)
    p.2.2‖) (fun n p _ => G n p)) : Prec sz (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErr sz n (E n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖) (fun n p _ => G n p + sz.Bctl n (p.1 : ℝ) ^ 3)
theorem expIntIQ_concl (d : ℕ) (hd : 3 ≤ d) (κ ε 𝔠 𝔡 𝔠d : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (sz : Sizes d) (z : ℕ → ℂ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s
    n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t) (hdd : STExpDriftDecayConcl sz (STflowE z) s t) (hW : STExpWardIConcl' sz
    (STflowE z) s t) : STExpIntQConcl' sz (STflowE z) s t
theorem stExpIntI'_holds (d : ℕ) : STExpIntI' d
theorem stStep6I_of_LW (d : ℕ) (h : LWtermEXP d) : STStep6I d
```

Instances (same script; the four required by the ticket). Seven more apply targets 2-8 at `szB` data: `inst_expIntIQ_{Qop_sub,diff_sumZero,src_sumZero,src_decay,ini,star_bound,back}`. Every deterministic hypothesis is discharged (flow `flow_zB`, times `7/8 < 15/16 ≤ lemT`, regime `szB_reg5I`, `(con_st_ind)` `conStInd_const` at `𝔠d = 1/300`, `ϑ*` by `expIntIQ_star_props`, the `𝒬`-Duhamel identity by `st6_duhEqQ_of_pin`); what stays a hypothesis is another gate's pin: `STExpDriftHiConcl`, `STExpDriftDecayConcl`, `STExpWardIConcl'`, `LWtermEXP 3`, the stochastic premises inside `InstIng6Concl`.
```
theorem inst_expIntI' : InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t → STExpDriftDecayConcl sz E s t → STExpWardIConcl' sz E s t → STExpIntConcl sz ∅ STSigSame E s t ∧ STExpIntQConcl' sz E s t)
    szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
theorem inst_expIntIQ_star_props : ∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1)) (1 / 2) (expIntIQ_star szB n)
theorem inst_expIntI'_mixed : STExpDriftHiConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) → STExpDriftDecayConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) → STExpWardIConcl' szB (STflowE zB) (fun _ => 7 / 8)
    (fun _ => 15 / 16) → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ, (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) C c (ϑ n)) ∧ STExpDuhEqQ szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 /
    16) ϑ ∧ ∀ F : ∀ n, STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n → ℝ, (∀ n p, 0 ≤ F n p) → Prec szB (U := STIdx2P szB STSigMixed (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16)) (fun n p _ => ‖RBM.Ind.Ugen 3
    (szB.L n) (szB.lam n) (STflowE zB n) p.2.1.1 (7 / 8) (p.1 : ℝ) (STQop (d := 3) (ϑ n) (7 / 8) (fun b => STExpErr szB n (STflowE zB n) (7 / 8) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p) → Prec szB (U := STIdx2P szB STSigMixed (fun
    _ => (7 / 8 : ℝ)) (fun _ => 15 / 16)) (fun n p _ => ‖STQop (d := 3) (ϑ n) (p.1 : ℝ) (fun b => STExpErr szB n (STflowE zB n) (p.1 : ℝ) p.2.1.1 b) p.2.2‖) (fun n p _ => F n p + STExpTarget szB n (p.1 : ℝ))
theorem inst_stStep6I_of_LW : LWtermEXP 3 → InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
```

```
$ python3 mkeq.py; lake env lean checkeq.lean    # check imports + `import RBM3D.Induction.ExpIntIQ` + sections 1-2 of T2257-check.lean + the equalities below; exit 0
example : @RBM.Gauss.Sizes.T2257Check.expIntIQ_star = @RBM.Gauss.Sizes.expIntIQ_star := rfl
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_star_props := @RBM.Gauss.Sizes.expIntIQ_star_props
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_Qop_sub := @RBM.Gauss.Sizes.expIntIQ_Qop_sub
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_diff_sumZero := @RBM.Gauss.Sizes.expIntIQ_diff_sumZero
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_src_sumZero := @RBM.Gauss.Sizes.expIntIQ_src_sumZero
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_src_decay := @RBM.Gauss.Sizes.expIntIQ_src_decay
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_ini := @RBM.Gauss.Sizes.expIntIQ_ini
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_star_bound := @RBM.Gauss.Sizes.expIntIQ_star_bound
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_back := @RBM.Gauss.Sizes.expIntIQ_back
example : RBM.Gauss.Sizes.T2257Check.expIntIQ_concl := @RBM.Gauss.Sizes.expIntIQ_concl
example : RBM.Gauss.Sizes.T2257Check.stExpIntI'_holds := @RBM.Gauss.Sizes.stExpIntI'_holds
example : RBM.Gauss.Sizes.T2257Check.stStep6I_of_LW := @RBM.Gauss.Sizes.stStep6I_of_LW
(+ 4 `example : <statement of section 3> := @RBM.Gauss.Step6Inst.<name>` for inst_expIntI', inst_expIntIQ_star_props, inst_expIntI'_mixed, inst_stStep6I_of_LW)
v3 exit 0
$ git diff main -- RBM3D/Induction/ExpIntI.lean RBM3D/Induction/Step6Pins.lean RBM3D/Induction/QopDecay.lean RBM3D/Induction/ExpWardI.lean | wc -l
0
$ git diff --stat main...HEAD
 RBM3D/Induction/ExpIntIQ.lean | 1545 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    2 +-
 2 files changed, 1546 insertions(+), 1 deletion(-)
$ git grep -n -E "expIntIQ_|stExpIntI'_holds|stStep6I_of_LW|inst_expIntI'|inst_expIntIQ_|inst_stStep6I_of_LW|T2257Check|ExpIntIQ" main -- RBM3D RBM3D.lean   -> exit 1, 0 hits (CONTROL.md: only the ticket's own list line)
```

Registry pre-check (CLAUDE.md §20 (2)) and full build with a temporary root import of `RBM3D.Induction.ExpIntIQ` (removed afterwards: `git status --short` empty):
```
first pre-check, with `STExpIntI'` deleted and before the `STSigMixed` line: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`: [RBM.Gauss.Sizes.STSigMixed]
$ python3 count_registry.py      # owedProps lists, base a18620d vs branch
base a18620d: {'borrowedProps': 2, 'owedProps': 158, 'structuralProps': 98, 'refutedProps': 7, 'supersededProps': 12}
branch HEAD : {'borrowedProps': 2, 'owedProps': 157, 'structuralProps': 99, 'refutedProps': 7, 'supersededProps': 12}
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Induction.ExpIntIQ; #assert_rbm_axioms
axiom audit: 7599 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 97, structural 38, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 99 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
v5 exit 0
$ lake build     # RBM3D.lean with the temporary extra import
info: RBM3D.lean:301:0: axiom audit: 7599 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 97, structural 38, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 99 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4061 jobs).
v4 exit 0
```
Ports: none from RBM1D/RBM2D (no `git diff --stat` needed). Four private helpers are copies of merged RBM3D lemmas, restated for this file: `expIntIQ_integral_le` (from `expIntI_drift_integral_le`, `ExpIntI.lean:283`, with the extra term `B³`), `expIntIQ_Bctl_nonneg` (`ExpIntI.lean:422`), `expIntIQ_drift_pi` (`ExpIntI.lean:429`), `expIntIQ_Bctl_le` (`ExpIniI.lean:79`); sources last changed in `25362ad` (T2239) and `f2766db` (T2223).

### Narrative
1. Result: targets 1-11 and 11 instances (the 4 required and 7 for targets 2-8) are in `RBM3D/Induction/ExpIntIQ.lean` (1545 lines; estimate 950/1250/1500). `stExpIntI'_holds d : STExpIntI' d`; `stStep6I_of_LW d h := ST_step6I_of_LW_Int d h (stExpIntI'_holds d)`. No new `Prop` pin; the merged files are unchanged.
2. Preflight (v), one line: PASS (transfer): `STExpWardIConcl'` at `u = s` bounds `(𝒫f_s)ϑ_s` and `(𝒫f_s)ϑ*_s` by `B_s³` for `σ₁ ≠ σ₂` (`STSigMixed`), `R_s` and the back-transfer use `ϑ_s`, `ϑ_u` only, ratio² `≤ 4` at `v = s`; fallback (b) not triggered. Stage 1b needed no hypothesis a statement lacks (no `T2257b`).
3. Envelope route of (iii)(a): `‖f_v‖ ≤ η_v⁻² + ‖𝒦‖` (`norm_Lloop_le` pointwise in `v`, the expectation is over a probability measure), `η_v ≥ (1-v) c₀`, `‖𝒦‖ ≤ (1-t)⁻¹ ≤ N` (`LemDecCalELip_STKloop_two_norm`), `(1-v)⁻¹ ≤ N` from `STReg5I` and `(eq:WO)`; then `N^k ≤ W^{k/𝔠}` (`size_rpow_le_W_rpow`): `K = 1/𝔠`, `C₀ = 6/𝔠` (`3/𝔠` in target 6, which needs only `‖f_s‖`) (`expIntIQ_inv_le`, `_f_le`, `_D_le`, `_Psum_pi_le`, `_Pvth_le`, `_theta_le`).
4. Kernel interface (iv): `expIntI_kernel_unif` is applied per mixed `σ` to guarded families: target 6 `if (0 < ilambda_n ∧ props ϑ_n ∧ props ϑ*_n ∧ v = s_n) then R_{s_n} else 0` with `X = 2 B_{s_n}³` (the guard `v = s_n` also settles the time scale of `R_s`: `ellT_mono` is not used); target 7 `if (0 < ilambda_n ∧ s_n ≤ v ≤ t_n) then A*_v else 0` with `X = |1-v|⁻¹ (B^{11/5} + B^{5/2} + B³)`. No new lift over `u`.
5. Sup bound of `A*_v` (`expIntIQ_src_sup`): `lem_+Q` (`stQopNorm_holds`, `m = 1`, `ε_Q = min(1/2, τd/(4C_n))`, `D_Q = C_n + 5/𝔠 + 1`) on `D_v`, plus the second Ward conjunct for `ϑ*`; the constants are absorbed by `3 ≤ N^{τ/2}`. The decay of `A*_v` (target 5) uses the five-piece identity `A* = D - (D - 𝒬*D) + (Θ(f - 𝒬*f) - (Θf - 𝒬*Θf)) - (𝒫f)∂ϑ*` (`QopAlgebra_commutator_ThetaN`).
6. Mollifier constants: explicit only in the statements of targets 1, 8 and in the instances; the proofs use `expIntIQ_star_abs` (abstract `C, c > 0`, §73 (3)).
7. Registry (`Test/Axioms.lean`): `STExpIntI'` deleted from `owedProps` by text. The pre-check then flagged `STSigMixed` (it occurs in binders of targets 6-8 through `STIdx2P sz STSigMixed`); registered in `structuralProps` as a data predicate (the sign class `σ₁ ≠ σ₂`; §20 data condition, not an unsure case), one line inserted after `STExpIntQConcl'`. Counts (borrowed/owed/structural/refuted/superseded): base 2/158/98/7/12, branch 2/157/99/7/12.
8. The ticket's equality script needs `@` on the left of the vocabulary equality (`T2257Check.expIntIQ_star` has an implicit `d`): `example : @T2257Check.expIntIQ_star = @expIntIQ_star := rfl`; all 11 theorem equalities and the 4 instance equalities then compile (exit 0).
9. Lean 4.34.0 core deprecates `if_pos`, `if_neg`, `if_true`, `dif_pos` (replacements `ite_eq_left`, `ite_eq_right`, `ite_true`, `dite_eq_left`); the file uses `ite_eq_left`.

## (c) Verified Mathlib / core names used (script `resolve.lean`: every non-RBM3D constant of the file, resolved under the file's `open`s; name : defining module; M. = Mathlib.)
```
ContinuousOn.intervalIntegrable : M.MeasureTheory.Integral.IntervalIntegral.Basic
ContinuousOn.inv₀ : M.Topology.Algebra.GroupWithZero
ContinuousOn.mul : M.Topology.Algebra.Monoid.Defs
Filter.Eventually.of_forall : M.Order.Filter.Basic
Filter.eventually_ge_atTop : M.Order.Filter.AtTopBot.Defs
Finset.card_filter_le : M.Data.Finset.Card
Finset.card_univ : M.Data.Fintype.Card
Finset.mul_sum : M.Algebra.BigOperators.Ring.Finset
Finset.sum_add_distrib : M.Algebra.BigOperators.Group.Finset.Basic
Finset.sum_congr : M.Algebra.BigOperators.Group.Finset.Basic
Finset.sum_const : M.Algebra.BigOperators.Group.Finset.Basic
Finset.sum_le_sum : M.Algebra.Order.BigOperators.Group.Finset
Finset.sum_nonneg : M.Algebra.Order.BigOperators.Group.Finset
Finset.sum_sub_distrib : M.Algebra.BigOperators.Group.Finset.Defs
MeasureTheory.IsProbabilityMeasure.measure_univ : M.MeasureTheory.Measure.Typeclasses.Probability
MeasureTheory.norm_integral_le_of_norm_le_const : M.MeasureTheory.Integral.Bochner.Basic
Nat.le_mul_of_pos_left : Init.Data.Nat.Lemmas
Nat.pow_le_pow_left : Init.Data.Nat.Basic
Real.exp_le_one_iff : M.Analysis.Complex.Exponential
Real.log_nonneg : M.Analysis.SpecialFunctions.Log.Basic
Real.one_le_rpow : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_add : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_le_one : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_le_rpow : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_le_rpow_of_exponent_le : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_le_rpow_of_nonpos : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_mul : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_natCast : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_neg : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_neg_one : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_nonneg : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_one : M.Analysis.SpecialFunctions.Pow.Real
Real.rpow_pos_of_pos : M.Analysis.SpecialFunctions.Pow.Real
Set.uIcc_of_le : M.Order.Interval.Set.UnorderedInterval
ZMod.card : M.Data.ZMod.Defs
div_le_div_iff₀ : M.Algebra.Order.GroupWithZero.Basic
div_le_div_of_nonneg_left : M.Algebra.Order.GroupWithZero.Basic
div_le_iff₀ : M.Algebra.Order.GroupWithZero.Basic
intervalIntegral.integral_const_mul : M.MeasureTheory.Integral.IntervalIntegral.Basic
intervalIntegral.norm_integral_le_of_norm_le : M.MeasureTheory.Integral.IntervalIntegral.Basic
inv_anti₀ : M.Algebra.Order.GroupWithZero.Basic
inv_le_one_of_one_le₀ : M.Algebra.Order.GroupWithZero.Basic
ite_eq_left : Init.Core
le_mul_of_one_le_left : M.Algebra.Order.GroupWithZero.Basic
le_mul_of_one_le_right : M.Algebra.Order.GroupWithZero.Basic
norm_le_pi_norm : M.Analysis.Normed.Group.Constructions
norm_sum_le : M.Analysis.Normed.Group.Basic
one_div_le_one_div_of_le : M.Algebra.Order.Field.Basic
one_le_inv₀ : M.Algebra.Order.GroupWithZero.Basic
one_le_mul_of_one_le_of_one_le : M.Algebra.Order.GroupWithZero.Basic
one_le_pow₀ : M.Algebra.Order.GroupWithZero.Basic
pi_norm_le_iff_of_nonneg : M.Analysis.Normed.Group.Constructions
pow_le_pow_left₀ : M.Algebra.Order.GroupWithZero.Basic
pow_le_pow_right₀ : M.Algebra.Order.GroupWithZero.Basic
tendsto_rpow_atTop : M.Analysis.SpecialFunctions.Pow.Asymptotics
```
Verified absent: `RBM.etaT_pos` (the name is `RBM.Gauss.etaT_pos`); deprecated, present: `if_pos`, `if_neg`, `if_true`, `dif_pos` (Init.Core, since 2026-07-21). Elementary order/ring lemmas (`add_le_add`, `mul_le_mul`, `le_trans`, `norm_add_le`, `mul_inv`, ...) are not listed.

## (d) Open issues and paper-delta candidates
- Candidate (a) (ticket): `6:104-132`: the `𝒬` conjunct for the paper's whole mollifier class follows from one decaying mollifier by the transfer `R_s = (𝒫 f_s)(ϑ_s - ϑ*_s)` (D556 / T2239a, its "formalization keeps the paper's class" half): targets 6-9. No `T2257a` (not triggered), no `T2257b…` (no step needed a hypothesis a statement lacks).
- Hypotheses of the pinned statements that the proofs do not use (not weakenings of the pins; successors could drop them): `0 < ε`, `∀ n, s n < t n` (target 5); `∀ n p, 0 ≤ G n p` (target 7); `∀ n, s n < t n`, `∀ n, t n < 1` (target 8); the premise `STExpDuhEqQ … ϑ` of `STExpIntQConcl'` (target 9: the identity used is the one of `ϑ*`).
- Open after this ticket: `STStep6I` follows from `LWtermEXP` (`stStep6I_of_LW`). The instances keep as hypotheses `STExpDriftHiConcl`, `STExpDriftDecayConcl` (S6-06, LW-14, S6-07) and `STExpWardIConcl'` (S6-10: `stExpWardI'_holds` gives it from `STExpAvgU`).
- For the dispatcher: (i) `Axioms.lean` hunks: one deletion (`STExpIntI'`, owed region after `STStep6III`) and one forced insertion (`STSigMixed`, structural region after `STExpIntQConcl'`); (ii) `docs/mathlib-api.md`: (c) and the deprecation note; (iii) ticket text: `𝔠d = 1/(100 d)`, `@` in the equality script; (iv) root import `import RBM3D.Induction.ExpIntIQ` is added by the hub at merge.
