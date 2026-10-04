Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 16:15:29 UTC 2026

Source: `git show 7b2b789:RBM3D/Probe/T2134Pins.lean` (2434 lines; `7b2b789` = tip of `t/T2134`). Paper refs `3_5:line` as in the probe docstrings. `STIngR5 d R Concl` = for `3 ≤ d`, all `κ ε 𝔡 Cd > 0`, `∃ 𝔠d ∈ (0, 1/100]`, for all flows/sizes/times `0 ≤ s < t ≤ lemT`, regime `R`, the Step 1-4 stochastic premises (`STKbound, STKward, STLK, STDecay, STDecayStrong` at `s`, `STConStInd, STStep1Loop, STStep2Concl, STLmaxU, STLKU`) imply `Concl`.

### (i) Exponent table and pin table

Exponents / thresholds the pins depend on (`A = ilambda² W^d`, `ρ ≤ (2A)^{𝔠d}`):

| item | value | constraint | slack |
|---|---|---|---|
| `𝔠d` (`STIngR5`) | `∃ 𝔠d ≤ 1/100`, chosen after `Cd` | `ρ³A^{-1/4} ≤ A^{-1/5}` needs `3𝔠d ≤ 1/20` i.e. `𝔠d ≤ 1/60` | `3/100 ≤ 1/20`, slack `1/50` |
| `ρ A^{-1/3} ≤ A^{-1/5}` | exponent `𝔠d - 1/3 ≤ -1/5` | `𝔠d ≤ 2/15` | `37/300` at `𝔠d=1/100` |
| `ρ A^{-1/2} ≤ A^{-1/5}` | `𝔠d - 1/2 ≤ -1/5` | `𝔠d ≤ 3/10` | `29/100` |
| `𝔠d·Cd` (`ρ^{Cd}Δ^{1/5} ≤ Δ^{1/6}`, `STEtermsMid` docstring) | `𝔠d ≤ 1/(30 Cd)` | `∃` after `Cd`: free | none needed; at `Cd=3`: `3/100 ≤ 1/30` |
| `STEtermsMid` exponents | `A^{-1/3}, A^{-1/2}, A^{-1/2}` (`LK×LK`, `G̃`, `(E⊗E)^M`) | window `λ²/L^d ≤ 1-t ≤ 1-s ≤ λ²` | window nonempty at `szB` (script) |
| `STDuhamelI/II`, `STIniTermI/II` | target `A^{-1/5}`; hyp `STEtermsMidConcl` (Duhamel only) | `A^{-1/3},A^{-1/2},ρ³A^{-1/4} ≤ A^{-1/5}` as above | see rows 1-3 |
| `STCltFar` | `A^{-6/5}/(|a₁-a₂|^{d-2}+1)`, window `(log W)^5 ℓ_s ≤ ℓ_t` | moment sum needs `(d-1)k > d`: `k ≥ 2` at `d=3` (`k=1` fails, singletons removed by `STCltIso`); cluster count `d-(d-2)k+(d+2)(k-1)+2 = 4k` | script line `CltFar moment exponent` |
| `STCltIso` | isolation `≥ 10 (log W)³ ℓ_s`, window `(log W)³ ℓ_s`, bound `W^{-D}` | eventually in `n`, every `p ≥ 1`, `D > 0` | n/a (data: `szCL_cltIso_witness`) |
| `STDecayStrongU` | `(W^{-d}B_{u,0})² e^{-|a₁-a₂|^{1/2}} + W^{-D}` | index set `λ² ≤ 1-t` (empty otherwise) | n/a |
| `STStep5Concl` | `STGdecayW sz E s t 0 ∧ STDecayStrongU` (loss exponent `Cd = 0`) | n/a | n/a |
| `STTailtoTail` | `C·T_{t,D}(|a₁-a₂|) + ((1-s)/(1-t))² W^{-D}`; `T_{u,D}(r) = (W^d|1-u|)^{-2}e^{-√r}+W^{-D}` | `g² ≤ 1-t`, `0 ≤ s ≤ t < 1`; `ρ²(W^d(1-s))^{-2} = (W^d(1-t))^{-2}` iff `ℓ_s=ℓ_t=1` | boundary `g²=1-t` attained at the instance |
| `STNewKLKL` | `C/(1-u)(Ĵ²W^{-d}𝒯̃^L + Ĵ W^{-d}W^{-D})` (`ℓ = L`, floor kept) | `λ ≤ 𝔡⁻¹`, `|E| ≤ 2-κ`, `‖G-M‖_max ≤ δ₀` | `λ=1/64 ≤ 10`, `1/2 ≤ 19/10`, `‖G_0-M‖=0` |
| `STExpInv` | translation `a↦a+c`, reflection `a↦-a` invariance of `𝔼𝓛^{(2)}` | `|E|<2`, `0 ≤ u < 1` | no `3 ≤ d` guard (model invariance is dimension free) |
| regimes `STReg5I..IV, Mid` | thresholds `λ²/L²`, `λ²/L^d`, `λ²` on `1-t`, `1-s` | data inequalities (all four cases nonempty at `d=3`) | script, first block |

Pin table (all `Prop`s of the form `STIngR5 3.. R Concl` unless stated; class from ticket / DECISIONS §40; copied to `Induction/Step5Pins.lean`, namespace `RBM.Gauss.Sizes`):

| pin | says | regime `R` | premise of | class |
|---|---|---|---|---|
| `STReg5I/II/III/IV/Mid` | the four regimes (`3_5:1939`) and window of cases (i)+(ii) | data predicates | every `STIngR5` use | structural |
| `STIngR5`, `STStep5R`, `STStep5Concl`, `STDecayStrongU`, `STIdx2`, `STIdx2P`, `STSig*` | shape / conclusion / index vocabulary | n/a | all pins below | structural (vocabulary) |
| `STStep5I/II/III`, `STStep5` (`STAny`) | `STStep5Concl` in regime i / ii / iii / general | Reg5I/II/III/Any | `inst_step5*`, S5-02/03/29 | owed |
| `STStep5IV` | same, regime iv; proved in S5-02 (`stStep5IV_holds`) | Reg5IV | `inst_step5IV` only | not in the ticket's class list (see N1) |
| `STEtermsMid` | `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1979`) | Reg5Mid | `STDuhamelI/II` hyp.; S5-02/03 | owed |
| `STDuhamelI`, `STDuhamelII` | integrated hierarchy `(iois-mtx2)`; with `Q^{(1)}` for mixed signs | I / II | skeletons I/II | owed |
| `STIniTermI`, `STIniTermII` | initial term `(iksjuwjx0)`, `(zYU2)` | I / II | skeletons I/II | owed |
| `STWardII` | `(zYU1)` Ward, `σ₁≠σ₂` | II | skeleton II | owed |
| `STNewKLKL` (`STNewKLKLAt`) | sharp `lem:newKLK` at `ℓ=L` (paper-delta `T2134a`) | none (`∀ sz`) | S5-13 | owed |
| `STCltFar` | `lem;CLT` (`f^{far}`) | I | S5-16, S5-25 | owed |
| `STCltIso` | `(eq:bound_isolated)` | I | S5-25 | owed (§40 overrides "borrowed") |
| `STExpInv` | translation/reflection invariance | none | S5-22 | owed |
| `STTailtoTail` | `(neiwuj)`, tail `T_{u,D}` | none | proved by S5-04 | owed |
| `STLemDecCalE`, `STPfStep5` | `lem_dec_calE`, `lem:pf_step5` | III | skeleton III | owed (§40 overrides "borrowed") |

`tailTD d W u D r := ((W^d|1-u|)⁻¹)² e^{-√r} + W^{-D}` (`def_WTuD`, `3_5:2297`) plus `tailTD_nonneg` go to `RBM/Defs/Tail.lean`.

### (ii) One concrete nondegenerate instance (all hypotheses at once, `d = 3`)

Data (merged `sz0, szB, z0, zB, sInst, tInst`; probe-new `szG, szCL, zCL`), `κ=ε=𝔡=1/10`, `𝔠=1/6`: case (i) `szB, zB, (7/8,15/16)`; (ii) `szB, zB, (15/16,31/32)`; (iii) `sz0, z0, (0,1/16)`; (iv) `szG (λ=5), zB, (5/8,3/4)`; CLT pins `szCL` (`m=n+24, L=2m^5, W=2^m, λ=1`, `z=1/2+i/(2L²)`, `(s,t)=(0,1-L^{-2})`); `STTailtoTail` at `L=5, g=1/2, W=25, D=2, s=1/2, t=3/4`; `STNewKLKL` at `sz0`, `n=0, E=1/2, u=0, D=1, H=0`. No `N=0`, no empty index set (the `szCL` index sets are nonempty at every `n`: `(log W)^5 ≤ L`, `10(log W)³ ≤ L/2 = m^5`). Merged lemmas used: `STGMM_zero` (`Induction/Step2Defs.lean:907`: `G_0 = M` at `H=0, u=0`), `lemT_zB` (`Step34Pins.lean:789`).

Command (script in my scratchpad, `python3 inst.py`; Fractions and mpmath at 80 digits; `msc` = branch of `(-z+√(z²-4))/2` with `Im>0`, `lemT = |msc|²`):

```
$ python3 T2138/inst.py
szB L=4 lam=1; lam^2/L^2 = 1/16  lam^2/L^3 = 1/64
(i)   (s,t)=(7/8,15/16): lam^2/L^2<=1-t<=1-s<=lam^2: ok
(Mid) lam^2/L^3<=1-t<=1-s<=lam^2: ok
(ii)  (s,t)=(15/16,31/32): lam^2/L^3<=1-t<=1-s<=lam^2/L^2: ok
(iii) sz0 lam_n^2<=1-t=15/16 for all n (lam_n^2=(2(n+1))^-12, max at n=0): ok
(iv)  szG L=4 lam=5: 1-t<=1-s<=lam^2/L^3: ok 25/64
szG WO: W^(-3/2+1/10)<=5<=10 for W>=4: ok
s<t, t<=lemT(zB)=?  zB=1/2+i/64: 0.983992286882 ok
 zB locDomain n=0: |Re z|=1/2<=1.9, N^(-0.9)=0.0005609<=1/64<=1: ok
 zB locDomain n=1: |Re z|=1/2<=1.9, N^(-0.9)=0.0003071<=1/64<=1: ok
 zB locDomain n=50: |Re z|=1/2<=1.9, N^(-0.9)=4.977e-7<=1/64<=1: ok
sz0 n=0 size= 2097152  z0=1/2+i size^-4/5; lemT(z0)>=t=1/16: ok  locDomain: ok
c_d=1/100 <= 1/60 (3c<=1/4-1/5): 3c=3/100 <= 1/20 slack 1/50
rho A^-1/3<=A^-1/5 needs c<=2/15 slack 37/300 ; rho A^-1/2<=A^-1/5 needs c<=3/10 slack 29/100
c_d*C_d<=1/30 (STIngR5 picks c_d after C_d): c_d=min(1/100,1/(30 C_d)); at C_d=3 c_d=1/100, c_d*C_d= 3/100 <=1/30: ok
szCL: m=n+24, L=2m^5, W=2^m, lam=1; 2m^5<=2^m for m>=24, fails m=23: ok ok 15925248 16777216
szCL m in 24..199,500,1000: W>=L, t<=lemT(zCL), locDomain, (log W)^5<=L, 10(log W)^3<=L/2, log W<=m: ok
 m=24: L= 15925248  1-t=L^-2=3.94301e-15  lemT(zCL)=1-2.03616e-15
 m=24 W^-3 B_t0=2.118e-22 <= 4^-m=3.553e-15 : ok
 m=40 W^-3 B_t0=7.523e-37 <= 4^-m=8.272e-25 : ok
 m=100 W^-3 B_t0=4.909e-91 <= 4^-m=6.223e-61 : ok
CltFar moment exponent (d-1)k>d at d=3: k=2 holds: True ; k=1 fails (as the paper's isolation bound handles singletons): True ; cluster d-(d-2)k+(d+2)(k-1)+2=4k at d=3,k=2..5: [True, True, True, True]
TailtoTail d=3 L=5 g=1/2 W=25 D=2 s=1/2 t=3/4: 3<=L, 0<g, W>0, 0<=s<=t<1, g^2=1/4<=1-t=1/4: ok  rho= 2
 rho^2 (W^d(1-s))^-2 == (W^d(1-t))^-2 : ok  (1-s)/(1-t))^2 W^-D = 4/625
NewKLKL at sz0 n=0: lam=1/64<=1/dd=10, |E|=1/2<=2-kappa=19/10, u=0<1, D=1>=0, l=L=4, H=0 Hermitian, ||G_0-M||=0 (STGMM_zero, Step2Defs.lean:907) ok
(con_st_ind) at szCL, c_d=0.01: holds from m=4063 on (checked m..m+100): index n>=4039
(con_st_ind) at szCL, c_d=0.1: holds from m=278 on (checked m..m+100): index n>=254
```

`ℓ_s=ℓ_t=1` at the `STTailtoTail` instance (`ellT(L=5,g=1/2,u)` with `u=1/2` and `u=3/4`, both `=1`, python `min(max(g/√|1-u|,1),L)`), so the exact amplitude identity above is the hypothesis used. `(con_st_ind)` is an eventual (`∀ᶠ n`) hypothesis of `STIngR5`; at `szCL` it holds from `n ≥ 4039` for `𝔠d = 1/100`, and the instances take it for every `𝔠d > 0` (`szCL_con` in the probe), not at one witness.

Ranges at `7b2b789` (script: `bash T2138/ranges.sh`; no Lean written, `git show` piped to `sed`):

```
probe lines:     2434   t/T2134 tip: 7b2b789
range 1,476:      476 lines; first: /- | last nonblank: end RBM.Gauss.Sizes
range 1704,1818:      115 lines; first: /-! ## 8. Compiled nonempty instances at `d = 3` | last nonblank:     hR (fun _ h𝔠 => conStInd_const szG szG_W_tendsto (by nor
range 1856,2254:      399 lines; first: /-! ### The ingredients -/ | last nonblank:   inst_ing5_II STReg5II _ h szB_reg5II Cd hCd
range 2275,2331:       57 lines; first: /-! ### The deterministic pins -/ | last nonblank:   h sz0 0 (1 / 2) (1 / 2) (by norm_num [abs_of_pos]) (by nor
left out (S5-02/03): 477-1703 skeletons; 1819-1855 four targets + assembly (      37 lines); 2255-2274 skeleton instances; 2334-end print axioms
sum copied = 1047
theorem/def count in copied ranges: 109
```

Script diff of the copied text against `7b2b789`: none exists yet (stage 1a writes no Lean). Stage 1b must pass `diff <(git --no-optional-locks show 7b2b789:RBM3D/Probe/T2134Pins.lean | sed -n '1,476p;1704,1818p;1856,2254p;2275,2331p') <(<same line selection of Step5Pins.lean>)` with only the differences N2, N3 below.

Notes (no verdict impact; for the prover and the dispatcher):
- N1 (scope). New ranges at `7b2b789`: `1-476`, `1704-1818`, `1856-2254`, `2275-2331` (1047 lines; the repair's `szCL` data adds about 340 lines to the portmap's 702). Lines `1819-1855` (`inst_step5I/II/III/IV/IV_proved`, `inst_step5`, `inst_assembly`) are S5-02's in the portmap (old `1816-1852`); the ticket's list omits them. `inst_step5IV` has `STStep5IV 3` as a hypothesis, which would make `STStep5IV` an unclassified premise (it is not in the ticket's class list), and `inst_step5IV_proved`/`inst_assembly` need S5-02's `stStep5IV_holds`, `ST_step5_assembly`. Prover: follow the ticket's ranges (leave `1819-1855` to S5-02) unless the dispatcher says otherwise.
- N2. `tailTD_nonneg` (probe `2278`, in `RBM.Gauss.T2134Inst`) is a lemma on `RBM.tailTD`: ticket item 2 puts it in `Defs/Tail.lean` (namespace `RBM`); `inst_tailtoTail` then reaches it through `open RBM`. The range `2275-2331` therefore loses lines `2277-2282` (docstring and lemma).
- N3. Namespace `RBM.Gauss.T2134Inst` is renamed `RBM.Gauss.Step5Inst` (ticket); docstring headers naming T2134/probe are otherwise kept.
- Imports available on main: `RBM3D/Induction/KDecay.lean`, `NewKLK.lean`, `GridDuhamelN.lean` exist; no declaration of `STReg5*`, `tailTD`, `STStep5*`, `STCltFar`, `STTailtoTail`, `Step5Inst` in `RBM3D/` (`grep -rln`, no hits).

### Verdict

- Item 1 (pins, regimes, `STIngR5`, `STStep5R/Concl`, `STDecayStrongU`): PASS. All hypothesis sets are satisfiable at the data above; exponents close with slack `1/50` (`𝔠d ≤ 1/100` vs `1/60`).
- Item 2 (`tailTD` and `tailTD_nonneg`): PASS (`tailTD ≥ 0` for `W ≥ 0`, the `rpow`/`exp` imports are in `Defs/Tail.lean`).
- Item 3 (instances `inst_*` and `szCL` data, `szCL_cltFar_index_nonempty`, `szCL_cltIso_witness`): PASS (all deterministic hypotheses hold at the concrete data; index sets nonempty).
- Registry classes (§40): consistent with the table; no FAIL or BLOCKED.

## (b) Script output — Sun Oct  4 16:27:50 UTC 2026

Commit: `c9f5c46` on `t/T2138`, files `RBM3D/Induction/Step5Pins.lean` (new,     1042 lines), `RBM3D/Defs/Tail.lean` (+13), `RBM3D/Test/Axioms.lean` (+27/-2, registry lines only). No port from RBM1D/RBM2D (the source is the T2134 probe `7b2b789`); no RBM1D/RBM2D diff-stat.

### b.1 Builds

```
$ lake build RBM3D.Defs.Tail RBM3D.Induction.Step5Pins 2>&1 | grep -v '^$' | tail -3
Build completed successfully (3774 jobs).
$ (registry pre-check: root import `import RBM3D.Induction.Step5Pins` added temporarily to RBM3D.lean after the last import; restored afterwards, `git status`: only the 3 writable files differ)
$ lake build   # first run, before the registry lines: fails with the audit error
error: RBM3D.lean:187:0: axiom audit: 14 premise(s) that no theorem of this development proves are in none of ...:
  [STIngR5, STDuhamelI, STIniTermII, STIniTermI, STDuhamelII, STWardII, STCltIso, STTailtoTail, STPfStep5, STExpInv, STNewKLKL, STEtermsMid, STCltFar, STLemDecCalE]  (all RBM.Gauss.Sizes.)
$ lake build   # after the registry lines
registry: 1 borrowed + 91 owed + 49 structural; 53 registered premise(s) carry nothing yet: [...]
premises found by scanning: 88 (borrowed 0, owed 68, structural 20).
Build completed successfully (3888 jobs).
```

Registered (appended, with class): owed `STStep5I/II/III`, `STStep5`, `STEtermsMid`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`, `STNewKLKL`, `STCltFar`, `STCltIso`, `STExpInv`, `STTailtoTail`, `STLemDecCalE`, `STPfStep5` (17); structural `STIngR5`, `STReg5I/II/Mid/III/IV` (6). `STStep5IV` is not registered (not in the ticket's list; no theorem of this file takes it as a hypothesis). The scan reported `STIngR5` and 13 of the owed pins as unclassified; the other 4 owed and 5 structural entries are registered as the ticket lists them and carry nothing yet.

### b.2 Axioms of every new public declaration (106, script-generated `#print axioms`, file `axs.lean`)

```
$ lake env lean axs.lean | grep -c 'depends on axioms\|does not depend'
106
$ lake env lean axs.lean | grep -v 'propext, Classical.choice, Quot.sound\]'
'RBM.Gauss.Sizes.STSigSame' depends on axioms: [propext]
'RBM.Gauss.Sizes.STSigMixed' depends on axioms: [propext]
'RBM.Gauss.Sizes.STSigAll' does not depend on any axioms
$ grep -c 'sorry\|admit\|native_decide' RBM3D/Induction/Step5Pins.lean
0
```

(The other 103 declarations depend on exactly `propext, Classical.choice, Quot.sound`; the full list includes `tailTD`, `tailTD_nonneg`, every pin, every `inst_*`.)

### b.3 Copied text against the probe (script diff)

```
$ diff <(git --no-optional-locks show 7b2b789:RBM3D/Probe/T2134Pins.lean | sed -n '1,476p;1704,1818p;1856,2254p;2275,2331p') RBM3D/Induction/Step5Pins.lean | grep -c '^[<>]'
51
```

Copied: probe lines 1-476, 1704-1818, 1856-2254, 2275-2331 (1047 lines; 1042 in the file). The complete list of differences (the diff hunks, as headers):

```
11c11 12a13 17,23c18,24 34,46d34 474a463,471 476a474 492c490 590a589 991d989 993,997c991 1047a1042 
```

* `11c11, 12a13, 17,23c18,24`: module docstring (title; "design probe, never imported" replaced by the S5-01 title and a pointer to the probe; section list without 1, 7, 9).
* `34,46d34`: probe section 1 (`tailTD`, probe lines 34-45) moved to `Defs/Tail.lean` (ticket item 2; the def there is `noncomputable def`, otherwise verbatim).
* `474a463,471`: the lemma `st5_reg5I_mid` (probe line 732, 8 lines, plus one docstring line added), see (d) N1; `476a474, 590a589`: blank lines.
* `492c490`: namespace `RBM.Gauss.T2134Inst` renamed `RBM.Gauss.Step5Inst`; `1047a1042`: closing `end RBM.Gauss.Step5Inst`.
* `991d989, 993,997c991`: `tailTD_nonneg` (probe 2277-2282) moved to `Defs/Tail.lean` (docstring kept); the heading `### The deterministic pins` kept.

Tail.lean diff: see `git diff 7f82dd6..c9f5c46 -- RBM3D/Defs/Tail.lean` (13 added lines before the final `end RBM`: docstring, `noncomputable def tailTD`, docstring, `tailTD_nonneg`).

### b.4 Target statements (extracted by script from `Step5Pins.lean`, `def` blocks, at most 8 lines each)

```
L82: def STIngR5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STDecayStrong sz (STflowE z) s →
  ...
L101: def STStep5R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR5 d R (fun sz E s t => STStep5Concl sz E s t)
L97: def STStep5Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  STGdecayW sz E s t 0 ∧ STDecayStrongU sz E s t
L69: def STDecayStrongU (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖Lloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - STKloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1.1 : ℝ)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2.2 0 - p.1.2.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
L121: def STTailtoTail (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (_hL : 3 ≤ L) (g W D s t : ℝ), 0 < g → 0 < W → 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin 2 → Bool, ∀ A : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) →
        haveI : NeZero L := ⟨by omega⟩
        ∀ a, ‖UN d L g (EKsgn m σ) s t A a‖ ≤
          C * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D)
L245: def STNewKLKL (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKLAt d κ 𝔡 C δ₀
L396: def STCltFar (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STCltFarConcl sz E s t)
L426: def STCltIso (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STCltIsoConcl sz E s t)
L441: def STExpInv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
      (∫ ω, Lloop sz n E u σ (fun i => a i + c) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) ∧
      (∫ ω, Lloop sz n E u σ (fun i => -a i) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP))
L191: def STLemDecCalE (d : ℕ) : Prop := STIngR5 d STReg5III (fun sz E s t => STLemDecCalEConcl sz E s t)
L209: def STPfStep5 (d : ℕ) : Prop := STIngR5 d STReg5III (fun sz E s t => STPfConcl sz E s t)
L273: def STEtermsMid (d : ℕ) : Prop := STIngR5 d STReg5Mid (fun sz E s t => STEtermsMidConcl sz E s t)
L315: def STDuhamelI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t)
L320: def STIniTermI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t)
L346: def STWardII (d : ℕ) : Prop := STIngR5 d STReg5II (fun sz E s t => STWardIIConcl sz E s t)
L451: def STStep5I (d : ℕ) : Prop := STStep5R d STReg5I
L461: def STStep5 (d : ℕ) : Prop := STStep5R d STAny
```

The regime predicates `STReg5*`, `STNewKLKLAt`, `STCltFarConcl`, `STCltIsoConcl` etc. are in the file with their docstrings (probe text).

### b.5 Compiled nonempty instances (all in `RBM.Gauss.Step5Inst`, compiled, axioms in b.2)

```
$ grep -n '^theorem inst_\|^theorem szCL_cltFar_index_nonempty\|^theorem szCL_cltIso_witness' RBM3D/Induction/Step5Pins.lean | cut -c1-110
545:theorem inst_ing5 (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
557:theorem inst_ing5_I (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
566:theorem inst_ing5_II (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
575:theorem inst_ing5_III (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
582:theorem inst_ing5_IV (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
594:theorem inst_lemDecCalE (h : STLemDecCalE 3) (Cd : ℝ) (hCd : 0 < Cd) :
599:theorem inst_pfStep5 (h : STPfStep5 3) (Cd : ℝ) (hCd : 0 < Cd) :
604:theorem inst_etermsMid (h : STEtermsMid 3) (Cd : ℝ) (hCd : 0 < Cd) :
609:theorem inst_duhamelI (h : STDuhamelI 3) (Cd : ℝ) (hCd : 0 < Cd) :
615:theorem inst_iniTermI (h : STIniTermI 3) (Cd : ℝ) (hCd : 0 < Cd) :
898:theorem szCL_cltFar_index_nonempty (n : ℕ) :
927:theorem szCL_cltIso_witness (n : ℕ) :
961:theorem inst_cltFar (h : STCltFar 3) (Cd : ℝ) (hCd : 0 < Cd) :
967:theorem inst_cltIso (h : STCltIso 3) (Cd : ℝ) (hCd : 0 < Cd) :
973:theorem inst_duhamelII (h : STDuhamelII 3) (Cd : ℝ) (hCd : 0 < Cd) :
980:theorem inst_iniTermII (h : STIniTermII 3) (Cd : ℝ) (hCd : 0 < Cd) :
986:theorem inst_wardII (h : STWardII 3) (Cd : ℝ) (hCd : 0 < Cd) :
996:theorem inst_tailtoTail (h : STTailtoTail 3) :
1013:theorem inst_newKLKL (h : STNewKLKL 3) :
1035:theorem inst_expInv (h : STExpInv 3) (a : Fin 2 → Zd 3 (sz0.L 0)) (c : Zd 3 (sz0.L 0)) :
```

Each `inst_X (h : STX 3)` applies the pin to the concrete data of (a)(ii): `inst_etermsMid`, `inst_duhamelI`, `inst_iniTermI` at `(szB, zB, 7/8, 15/16)`; `inst_duhamelII`, `inst_iniTermII`, `inst_wardII` at `(szB, zB, 15/16, 31/32)`; `inst_lemDecCalE`, `inst_pfStep5` at `(sz0, z0, 0, 1/16)`; `inst_cltFar`, `inst_cltIso` at `szCL, zCL` (index sets nonempty at every `n`: `szCL_cltFar_index_nonempty`, `szCL_cltIso_witness`); `inst_tailtoTail` at `L=5, g=1/2, W=25, D=2, s=1/2, t=3/4`; `inst_newKLKL` at `sz0, n=0, E=1/2, u=0, D=1, H=0`; `inst_expInv` at `sz0, n=0, E=1/2, u=1/2`. Every deterministic hypothesis (flow, `s<t≤lemT`, regime, `(con_st_ind)`, locDomain, window) is discharged by `norm_num`/merged lemmas; the pin itself stays a hypothesis of the example (it is the unproved pin of this gate, registered owed). No `N = 0`, no empty index set. `inst_ing5`, `inst_ing5_I..IV` are the generic instance of `STIngR5` (hypothesis `STIngR5 3 R Concl`, regime `R`).

### b.6 Name-clash grep (script `clash.sh`)

```
declarations named like one of the 106 new public names, outside Step5Pins.lean:
RBM3D/Green/FlucIterGain.lean:977:private def szG : Sizes 3 where
(end: nothing listed above means no clash)
tailTD in Defs/Tail.lean and elsewhere:
RBM3D/Defs/Tail.lean:173:noncomputable def tailTD (d : ℕ) (W u D r : ℝ) : ℝ :=
RBM3D/Defs/Tail.lean:176:/-- `tailTD ≥ 0` for `W ≥ 0`. -/
RBM3D/Defs/Tail.lean:177:theorem tailTD_nonneg {d : ℕ} {W u D r : ℝ} (hW : 0 ≤ W) : 0 ≤ tailTD d W u D r := by
RBM3D/Defs/Tail.lean:178:  unfold tailTD
git merge-base main HEAD: 7f82dd6; main tip: f22c63c
files changed on main since the merge-base that this ticket touches:
 RBM3D.lean | 1 +
 1 file changed, 1 insertion(+)
```

`szG` in `RBM3D/Green/FlucIterGain.lean:977` is `private` (namespace `RBM.Green`, not `RBM.Gauss.Step5Inst`); the full `lake build` above passed.

### b.7 Narrative

* Source: `git show 7b2b789:RBM3D/Probe/T2134Pins.lean`, ranges of (a), copied by a script and edited as in b.3. The module compiled except one unknown identifier: `inst_etermsMid`, `inst_duhamelI` use `st5_reg5I_mid` (probe line 732, deterministic regime comparison, in the S5-02 skeleton region); copied with its docstring line to the end of the probe's section 6 (`RBM.Gauss.Sizes`), no statement of a pin changed.
* Statements of all pins and instances compile unchanged against main `7f82dd6` (merge-base). Main tip is now `f22c63c`; it differs from the merge-base on the files this ticket touches only by one line of `RBM3D.lean` (root import).
* The root import `import RBM3D.Induction.Step5Pins` is left to the hub; the registry pre-check was run with it temporarily added.
* Instances `inst_step5I/II/III/IV`, `inst_step5`, `inst_assembly` (probe 1819-1855) are not copied (S5-02, preflight N1). `STStep5I/II/III`, `STStep5` are registered owed as the ticket says; in this file no theorem takes them as a hypothesis yet.

## (c) Verified Mathlib names used (by the compile of b.1)

`Real.rpow_nonneg`, `Real.exp`, `Real.sqrt` (`tailTD`, `tailTD_nonneg`); `pow_le_pow_right₀`, `div_le_div_of_nonneg_left`, `sq_nonneg` (`st5_reg5I_mid`); the other names are those of the probe, unchanged. No name verified absent.

## (d) Open issues and paper-delta candidates

* N1 (scope). `st5_reg5I_mid` (probe 732) is copied into this file because two copied instances use it; S5-02 must not copy it again (name clash) when it moves probe lines 477-1703.
* N2. Instances of `STStep5I/II/III/IV`, `STStep5` and the assembly (probe 1819-1855) are for S5-02: `STStep5IV` is proved there (`stStep5IV_holds`), and has no registry class in this ticket.
* N3. The module docstring is rewritten (b.3); the docstrings of all declarations are the probe's. They name the probe in places; docstrings are not evidence (CLAUDE.md §5.7).
* Paper-delta candidates: none new. D315-D324 (DECISIONS §40) cover `tailTD` (amplitude `η_u^{-2}`), the sharp `STNewKLKL` (T2134a) and the registry classes.
