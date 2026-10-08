Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 14:56:07 UTC 2026

Notation: `v = 1-t`, `Bctl(t) = W^{-d}B_{t,0} = W^{-d}[(λ²+v)^{-1} + (L^d v)^{-1}]` (`Defs/Sizes.lean:214`, `Defs/Params.lean:36`; paper `(eq_B_param)` `1_2:1107`), `N = (WL)^d` (`Defs/Sizes.lean:157`), `λ = ilambda`, `lemT z = |m(z)|²` (`(eq:t0E0)` `1_2:789`). Targets (mathematics): (T1) the six answers Q1-Q6 of the ticket; (T2) the candidate pin `STMainInd d → UNMLOut d` (check file section 2): from `lem:main_ind` (one step `s→t` under `(con_st_ind)`, `1_2:1295-1297`) to the conclusions `STLK, STLmax, STDecay, STExp2, STLocalEntry` at every sequence `0 ≤ t_n ≤ lemT z_n`.

### (i) Exponent table

| # | quantity | value (instance) | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠_d` (`STMainInd`, `Induction/Defs.lean:294`) | any value in `(0, 1/100]`; instance `1/100` | `ρ_n := Bctl(t0)^{𝔠_d} < 1` eventually; step count `K ∝ 1/𝔠_d`, so a smaller `𝔠_d` only lengthens the chain | `𝔠_d` is quantified before `𝔠` and `sz`; the chain length may depend on both (it is built after them) |
| 2 | `𝔠` (`W ≥ N^𝔠`, `1_2:359`) | `1/6` | `N^{1/6} ≤ W` | n=0: `11.3 ≤ 32`; n=1: `90.5 ≤ 1024` (script) |
| 3 | `𝔡` (`(eq:WO)` `1_2:363`) | `1/10` | `W^{-d/2+𝔡} ≤ λ ≤ 𝔡^{-1}` | n=0: `32^{-1.4} = 2^{-7} = 0.0078125 ≤ λ = 1/64 = 0.015625` (factor 2) |
| 4 | `ε` (`𝐃_{κ,ε}` `1_2:380`), `κ` | `1/10`, `1/10` | `N^{-1+ε} ≤ Im z ≤ 1`, `|Re z| ≤ 2-κ` | n=0: `N^{-0.9} = 2.04e-06 ≤ Im z = 0.05`; also `1e-05` (script) |
| 5 | `1 - t0` (`t0 = lemT z`) | `Im z/(Im m + Im z)` (from `(eq:t0E0)`, `1_2:789`) | `Im m ≤ |m| < 1` (`norm_msc_lt_one`, `Defs/Semicircle.lean:152`) and `Im z ≤ 1` give `1-t0 ≥ Im z/2 ≥ N^{-1+ε}/2` | instance `0.0503 ≥ 0.025`; `lemT < 1` (`Semicircle.lean:209`) so `t < 1` for every `t ≤ lemT` |
| 6 | `μ = min(2𝔠𝔡, ε)` | `1/30` | for all `0 ≤ t ≤ t0`: `Bctl(t) ≤ W^{-2𝔡} + 1/(N(1-t0)) ≤ N^{-2𝔠𝔡} + 2N^{-ε} ≤ 3N^{-μ}` (`λ²W^d ≥ W^{2𝔡}` by (eq:WO); `Bctl` is increasing in `t`) | the bound is uniform in `t_n`: one eventual threshold in `n` serves every sequence `t` |
| 7 | `ρ_n` (uniform step ratio) | asymptotic `ρ_n ≤ (3N^{-μ})^{𝔠_d}`; instance uses the true `Bctl(t0)^{𝔠_d}` | `ρ_n < 1` | crude bound is `<1` only for `N > 3^{1/μ} = 3^{30} ≈ 2.06e14`; true values: n=0 `0.9287`, n=1 `0.8369`, n=2 `0.7875` (η = 0.05), n=0 η=1e-5 `0.9822` |
| 8 | `K` (steps `0 → t_n`) | `K = min{k : (1-t_n) ρ_n^{-k} ≥ 1}` | `K ≤ ln(1/(1-t0))/ln(1/ρ_n) + 1 → (1-ε)/(𝔠_d μ) + 1` as `N → ∞` (rows 5-7) | asymptotic cap `2700 + 1` (`𝔠_d = 1/100`, `μ = 1/30`); a constant independent of `n` and of `t_n`; instance: `K = 41` (n=0, t_n=t0), `17`, `13` (n=1, 2), `640` (η=1e-5) |
| 9 | chain times | `v_K = 1-t_n`, `v_{k} = v_{k+1}/ρ_n` for `k ≥ 1`, `p_0 = 0` (clip) | step `k`: `Bctl(p_{k+1})^{𝔠_d} ≤ ρ_n ≤ (1-p_{k+1})/(1-p_k) < 1`; first step ratio `v_1 ∈ [ρ_n, 1)` by minimality of `K` | holds with equality in the middle steps; uses row 6 (monotone `Bctl`) |
| 10 | exponent `1/2` of `(c)` vs exponent `1` of `(Gt_bound)` | `STLocalMax` (`Defs.lean:144`) vs `STLocalEntry` (`:151`) | `|(G-M)_{xy}|² ≺ W^{-d}B_{t,K}` and `B_{t,K} ≤ B_{t,0}` (K = block distance; `(K+1)^{-(d-2)}` nonincreasing since `d-2 ≥ 1`) give `‖G-M‖_max ≺ Bctl(t)^{1/2}` | slack `0` in the exponent; the monotonicity in `K` needs `d > 2` (`d=3`: exponent `1`; script prints `True`) |
| 11 | exponent `1/5` of `(b)` | `1/5` | paper: any positive constant `< 1/4` (`1_2:1214`, remark after `(Eq:Gtlp_exp)`) | `1/20` |
| 12 | strong-decay threshold `1-t ≥ λ²` | n=0: `λ² = 2.44e-4` | `STDecayStrong` (`:134`) has the empty index set when `1-t < λ²`; hypothesis at `s` and conclusion at `t` live on the same kind of set | the paper's `t_1 = (1-λ²)∨1/2` stage (`1_2:1310`) is not a separate row in the Lean pins |
| 13 | Step-2 loss `((1-s)/(1-t))^{C_d}` (`1_2:1352`) | `C_d` independent of `𝔠_d` (paper) | inside the merged `STMainInd`; the assembly supplies only `(con_st_ind)` | not an assembly row |

Boundary one-liners (DECISIONS §29): **`t = 0`**: `G_0 = M`, so `𝓛^{(k)}_0 = 𝒦^{(k)}_0` exactly (`1_2:1240-1243`); `STLK, STDecay, STExp2` (left sides `0`), `STLocalMax` (`‖G_0-M‖ = 0`) and `STDecayStrong` hold at `s ≡ 0` for every `n`; `s < t` (all `n`) is impossible at `t_n = 0`, so `t_n = 0` is the base class, not a step. **`t → lemT z`**: `1-t ≥ 1-t0 ≥ Im z/2 > 0`, so `t < 1`, `Bctl(t) ≤ 3N^{-μ}` and `(con_st_ind)` holds eventually. **`1-t` small (`≈ N^{-1+ε}`)**: `1/(N(1-t)) ≤ 2N^{-ε}` (row 6), the number of steps stays `≤ 2701` (row 8) because `ρ_n` is uniform; the first step from `s = 0` has ratio `1-s_1 ∈ [ρ_n, 1)`. For `n` where the clipped chain degenerates (`p_k = p_{k+1}`), the sequence hypothesis `s_n < t_n` (all `n`) fails, so the design must split `n` into finitely many classes by the number of nondegenerate steps (`≤ K+1`), as `ST_mainInd_of_regimes` does with the stage patterns (`MainIndRegimes.lean:616`).

### (ii) One concrete nondegenerate instance

Data (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠_d = 1/100`): the merged sizes `sz0` of `Induction/Step4.lean:228-229` (`L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`), `z_n = 0.5 + 0.05 i` (and `0.5 + 1e-5 i` at n=0), `t_n ∈ {0, 0.3, lemT z_n}`. All hypotheses: `Admissible` (`W ≥ N^{1/6}`, `(eq:WO)`, `N → ∞`), `z_n ∈ 𝐃_{κ,ε}`, `0 ≤ t_n ≤ lemT z_n`, `(con_st_ind)` at each chain step. No external hypothesis occurs in the assembly (it only composes the merged `STMainInd`), so no external limit is needed; the limit used is `N → ∞` of rows 6-8 (`SizeTendsto`, inside `Admissible`).

Command: `python3 -I $S/pre.py` (`S` = scratchpad `T2338/`; script below).
```
import cmath, math
d=3; kap=eps=dd=0.1; cfr=1/6; cd=1/100          # kappa, eps, fd, fc, fc_d (largest allowed value 1/100)
def msc(z):
    r=cmath.sqrt(z*z-4)
    return next(m for m in ((-z+r)/2,(-z-r)/2) if m.imag>0)
def Bctl(W,L,lam,v):                              # W^{-d} B_{t,0}, v = 1-t
    return W**(-d)*(1/(lam**2+v)+1/(L**d*v))
def Bpar(L,lam,v,K): return 1/((lam**2+v)*(K+1)**(d-2))+1/(L**d*v)
def run(n,eta,tns):
    L=4*(n+1); W=(2*(n+1))**5; lam=(2*(n+1))**-6.0; N=(W*L)**d
    z=complex(0.5,eta); m=msc(z); v0=eta/(m.imag+eta); t0=1-v0   # 1-t0 = Im z/(Im m+Im z)
    print(f"n={n} eta={eta}: L={L} W={W} lam={lam:.3e} N=2^{math.log2(N):.1f}; "
          f"Bandwidth(1/6): {N**cfr<=W}; WO: {W**(-d/2+dd)<=lam<=1/dd}; z in D: {abs(z.real)<=2-kap and N**(-1+eps)<=eta<=1}")
    print(f"  |m|={abs(m):.6f} lemT=|m|^2={abs(m)**2:.6f} vs Im m/(Im m+eta)={m.imag/(m.imag+eta):.6f}; 1-t0={v0:.4e} >= eta/2: {v0>=eta/2}")
    B0=Bctl(W,L,lam,v0); rho=B0**cd
    print(f"  Bctl(t0)={B0:.4e}; rho=Bctl(t0)^cd={rho:.5f}<1: {rho<1}; B_(t0,K) nonincreasing in K (K<50): "
          f"{all(Bpar(L,lam,v0,K+1)<=Bpar(L,lam,v0,K) for K in range(50))}")
    for tn in tns:
        vn=v0 if tn=='t0' else 1-tn
        if vn==1: print("  t_n=0: no step (base case)"); continue
        u=[vn]
        while u[-1]<1: u.append(u[-1]/rho)
        K=len(u)-1; v=[1.0]+[u[K-k] for k in range(1,K+1)]   # v_k = 1 - p_k, p_0=0, p_K=t_n
        ok=all(Bctl(W,L,lam,v[k+1])**cd<=v[k+1]/v[k]*(1+1e-12) and v[k+1]/v[k]<1 and v[k+1]<v[k] and v[k+1]>=v0*(1-1e-12) for k in range(K))
        print(f"  t_n={1-vn:.5f}: K={K} steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: {ok}")
for n in (0,1,2): run(n,0.05,(0.0,0.3,'t0'))
run(0,1e-5,('t0',))
mu=min(2*cfr*dd,eps); print(f"asymptotic: mu=min(2*fc*fd,eps)={mu:.5f}; K_inf=(1-eps)/(cd*mu)={(1-eps)/(cd*mu):.0f}")
```
Output (verbatim):
```
n=0 eta=0.05: L=4 W=32 lam=1.562e-02 N=2^21.0; Bandwidth(1/6): True; WO: True; z in D: True
  |m|=0.974514 lemT=|m|^2=0.949677 vs Im m/(Im m+eta)=0.949677; 1-t0=5.0323e-02 >= eta/2: True
  Bctl(t0)=6.1299e-04; rho=Bctl(t0)^cd=0.92870<1: True; B_(t0,K) nonincreasing in K (K<50): True
  t_n=0: no step (base case)
  t_n=0.30000: K=5 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
  t_n=0.94968: K=41 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
n=1 eta=0.05: L=8 W=1024 lam=2.441e-04 N=2^39.0; Bandwidth(1/6): True; WO: True; z in D: True
  |m|=0.974514 lemT=|m|^2=0.949677 vs Im m/(Im m+eta)=0.949677; 1-t0=5.0323e-02 >= eta/2: True
  Bctl(t0)=1.8543e-08; rho=Bctl(t0)^cd=0.83692<1: True; B_(t0,K) nonincreasing in K (K<50): True
  t_n=0: no step (base case)
  t_n=0.30000: K=3 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
  t_n=0.94968: K=17 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
n=2 eta=0.05: L=12 W=7776 lam=2.143e-05 N=2^49.5; Bandwidth(1/6): True; WO: True; z in D: True
  |m|=0.974514 lemT=|m|^2=0.949677 vs Im m/(Im m+eta)=0.949677; 1-t0=5.0323e-02 >= eta/2: True
  Bctl(t0)=4.2288e-11; rho=Bctl(t0)^cd=0.78752<1: True; B_(t0,K) nonincreasing in K (K<50): True
  t_n=0: no step (base case)
  t_n=0.30000: K=2 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
  t_n=0.94968: K=13 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
n=0 eta=1e-05: L=4 W=32 lam=1.562e-02 N=2^21.0; Bandwidth(1/6): True; WO: True; z in D: True
  |m|=0.999995 lemT=|m|^2=0.999990 vs Im m/(Im m+eta)=0.999990; 1-t0=1.0328e-05 >= eta/2: True
  Bctl(t0)=1.6610e-01; rho=Bctl(t0)^cd=0.98221<1: True; B_(t0,K) nonincreasing in K (K<50): True
  t_n=0.99999: K=640 steps; every step has Bctl(t)^cd<=(1-t)/(1-s)<1, s<t<=lemT: True
asymptotic: mu=min(2*fc*fd,eps)=0.03333; K_inf=(1-eps)/(cd*mu)=2700
```

### Verdicts
- **(T1) design Q1-Q6: PASS.** No merged pin contradicts the chain: `STConStInd` (`Defs.lean:168`) is exactly `(con_st_ind)`; hypotheses (a)-(d) at `s` are `STLK, STDecay, STDecayStrong, STLocalMax, STExp2` and the conclusions at `t` give all five (`STLocalMax` from `STLocalEntry` by row 10, the other four directly), so the induction closes; the chain length is a constant (rows 5-9). Interpolating between fixed chain times is not needed: the chain can be run to each `t_n` (rows 8-9), with `n` split into finitely many classes of equal step pattern.
- **(T2) pin `STMainInd d → UNMLOut d` (check-file section 2): PASS** (true and non-vacuous at the instance above: `UNMLOut` (`Universality/Pins.lean:432`) concludes `STLK, STLmax, STDecay, STExp2, STLocalEntry` at every `0 ≤ t_n ≤ lemT z_n`, all among the conclusions of `STMainInd` at `t`, or at `t = 0` from the base case; its quantification order `κ ε 𝔡 𝔠 sz z t` does not contain `𝔠_d`, which is existential inside `STMainInd`).

## (a′) Preflight corrections — Thu Oct  8 17:03:23 UTC 2026

Rows 8-9 of the exponent table and the last sentence of the boundary one-liners of (a) (a chain with ratio `ρ_n`, `K ≤ 2701` steps built per `n`, and a split of `n` into `≤ K+1` classes by the number of nondegenerate steps) describe a chain other than the compiled one. The compiled design (probe 175-254, 262-287) uses the uniform grid `1 - p_k = (1-t_n)^{k/K}` with one fixed `K = ⌈2/(𝔠_d μ)⌉` (`6000` at the data of (ii), `μ = min(2𝔠𝔡, ε/2) = 1/30`); every step is strict when `t_n > 0`, so only the class `{t_n = 0}` is split off (the base case), by `StochDomAt.of_subset_union` (probe 140-173). The verdicts (T1), (T2) of (a) do not change.
The compiled examples use the merged `sz0` (`Defs/Sizes.lean:260`) and `z0 n = 1/2 + i N_n^{-4/5}` (`Induction/Defs.lean:413`), not the points `0.5 + 0.05 i` of (ii); the numbers for both are in `docs/reports/T2338-design.md` section 10 (B5). The sentence of (ii) "no external hypothesis occurs in the assembly" is about external inputs; besides `STMainInd` the compiled assembly takes two deterministic inputs: the merged `ML:Kbound` and the owed identity `STLoopZeroId` (`𝓛_0 = 𝒦_0`, B9 of the design).

## (b) Script output — Thu Oct  8 17:03:23 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2338`, branch `t/T2338`; B-numbers are those cited in `docs/reports/T2338-design.md` (B5, B6, B8, B9, B11, B13 are in its section 10; B1-B4, B7, B10, B12 are below).
**B1** `lake env lean RBM3D/Probe/T2338Pins.lean`, exit code, `tail -4` of the output (the four `#print axioms` of the probe), `wc -l` — Thu Oct  8 17:03:23 UTC 2026
```
exit code: 0
'RBM.Probe.T2338.stMLOutG_of_mainIndG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2338.stBase_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2338.unMLOut_of_mainInd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2338.unMLOutBA_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
lines of output:       13 (six #check lines and four #print axioms lines, no warning, no error)
     399 RBM3D/Probe/T2338Pins.lean
```
**B2** `lake build RBM3D.Probe.T2338Pins` — Thu Oct  8 17:03:27 UTC 2026
```
exit code: 0
Build completed successfully (4038 jobs).
warning lines from RBM3D/Probe/T2338Pins.lean: 0; lines containing 'error': 0
```
**B3** `lake env lean axioms.lean` (scratch script: `collectAxioms` over every declaration of `RBM.Probe.T2338`, among them `stChainSteps`, `stHorizon_band`, `stPosConclG_of_mainIndG`; the four targets are also printed in B1) — Thu Oct  8 17:03:29 UTC 2026
```
declarations of RBM.Probe.T2338 (without compiler auxiliaries): 34, of which theorems: 26; union of the axioms they depend on: [Classical.choice, Quot.sound, propext]
```
**B4** statements extracted from the probe by `sed -n 'a,bp'` (ranges a-b: STConclgL 43-45, STLK0 48-49, STG0M 52-53, STBaseG 56-59, STHorizonG 63-67, STMLOutG 70-76, stChainTime 79-79, STLoopZeroId 340-342, stMLOutG_of_mainIndG 291-293, unMLOut_of_mainInd 361-362, unMLOutBA_of_pins 365-369) — Thu Oct  8 17:03:33 UTC 2026
```
def STConclgL {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧
    STDecayStronggL C μ τ
def STLK0 {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ), 1 ≤ k → C.L n 0 σ a ω = C.K n 0 σ a
def STG0M {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)), C.G n 0 ω x y = C.M n x y
def STBaseG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → STConclgL (mk sz z) (law sz) (fun _ => 0)
def STHorizonG (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
    sz.Admissible 𝔠 𝔡 ∧ (∀ n, 0 < T0 sz z n ∧ T0 sz z n < 1) ∧
      ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - T0 sz z n
def STMLOutG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
      STLKgL (mk sz z) (law sz) t ∧ STLmaxgL (mk sz z) (law sz) t ∧ STDecaygL (mk sz z) (law sz) t ∧
        STExp2gL (mk sz z) (law sz) t ∧ STLocalEntrygL (mk sz z) (law sz) t
noncomputable def stChainTime (t : ℕ → ℝ) (K k : ℕ) : ℕ → ℝ := fun n => 1 - (1 - t n) ^ ((k : ℝ) / K)
def STLoopZeroId (d : ℕ) : Prop := ∀ (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ {m : ℕ}, 1 ≤ m → ∀ (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)), loopFine d (sz.L n) (sz.W n) (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (zt E 0) σ a - sz.STKloop n E 0 σ a = 0
theorem stMLOutG_of_mainIndG (hmain : STMainIndG d law Flow mk T0) (hhor : STHorizonG d Flow T0)
    (hbase : STBaseG d law Flow mk) :
    STMLOutG d law Flow mk T0 := by
theorem unMLOut_of_mainInd (hpriv : STLoopZeroId d) (hmain : STMainInd d) : RBM.Univ.UNMLOut d :=
  (unMLOut_iff d).2 (stMLOutG_of_mainIndG ((STMainInd_iff d).1 hmain) (stHorizon_band d) (stBase_band hpriv))
theorem unMLOutBA_of_pins
    (hmain : STMainIndG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0)
    (hhor : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0)
    (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) :
    RBM.Univ.UNMLOutBA d := stMLOutG_of_mainIndG hmain hhor hbase
```
**B12** compiled nonempty instances (probe 373-392, `sed -n '373,392p' RBM3D/Probe/T2338Pins.lean | grep -v '^$'`; the unproved pins `LWterm`, `LWtermExp`, `STDuhamelII`, `STMainInd 3`, `STLoopZeroId 3` stay hypotheses, every deterministic hypothesis is discharged at the merged data `sz0`, `z0`, `flow_z0`) — Thu Oct  8 17:03:33 UTC 2026
```
/-- R4a: `STMainInd d` from exactly three owed pins (`LWterm`, `LWtermExp`, `STDuhamelII`); every other premise of
`ST_mainInd_of_pins'` is proved. -/
example (hLW : LWterm d) (hLWE : LWtermExp d) (hD2 : STDuhamelII d) : STMainInd d := fun hd =>
  have hEM : STEtermsMid d := stEtermsMid_of_LWT d (STLWT_of_LWtermExp hd hLWE)
  ST_mainInd_of_pins' d (ST_step2_of_pinsLW' hd (stNewKLK_holds d) hLWE (stEMn2Exp_holds d hd) (stGridRepN_holds d hd)
      (stOptL2_of_pins hd (STLWB_of_LWterm hd hLW) (stGridMart_holds d hd)) (stLocalAvgOfL2_holds hd))
    (stStep3RegIII_holds d) (stStep3RegI_holds d) (stStep3II_holds d) (ST_step5_caseI_of_pins hEM (stDuhamelI_holds d) (stIniTermI_holds d))
    (ST_step5_caseII_of_pins hEM hD2 (stIniTermII_holds d) (stWardII_holds d)) (stStep6I_holds d) (stStep6II_holds d) (stStep6III_holds d) hd
open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst in
/-- `stChainSteps` at the merged data `sz0`, `z0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = ε = 1/10`, `𝔠_d = 1/100`, `τ = ε/2`), `K = 6000`, `t = lemT z/2`. -/
example : sz0.STConStInd (1 / 100) (stChainTime (fun n => lemT (z0 n) / 2) 6000 5999) (stChainTime (fun n => lemT (z0 n) / 2) 6000 6000) := by
  obtain ⟨⟨-, -, hsz, hbw, hWO⟩, hT, hr⟩ := stHorizon_band 3 (1 / 10) (1 / 10) (1 / 6) (1 / 10) sz0 z0 (by norm_num) (by norm_num) flow_z0
  exact stChainSteps sz0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (K := 6000) (by norm_num [min_def]) hbw hWO hsz
    (fun n => (hT n).2) hr (fun n => half_pos (hT n).1) (fun n => by linarith [(hT n).1]) (by norm_num)
open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst in
example (hpriv : STLoopZeroId 3) (hmain : STMainInd 3) : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2) :=
  (unMLOut_of_mainInd hpriv hmain (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 z0 flow_z0 _
    (fun n => (half_pos (lemT_pos (z0_im_pos n))).le) (fun n => by linarith [lemT_pos (z0_im_pos n)])).1
```
**B7** name-clash grep, `zsh clash2.sh` (`grep -rn -w` of each of the 34 public names of the probe and of the 4 names proposed for the rows in the branch worktree without the probe, the main worktree, RBM2D, RBM1D) — Thu Oct  8 17:03:33 UTC 2026
```
public names in the probe: 34; proposed row names: stMainInd_holds unMLOut_holds stMainInd_of_LW unMLOut_of_LW
branch worktree (probe excluded): 0 clashes
main worktree (0853ac1): 0 clashes
RBM2D: 0 clashes
RBM1D: 0 clashes
```
**B10** ported ideas (no RBM2D text is copied): `chainTime` (`RBM2D/Induction/Defs.lean:318`), shape of `chainStepCond` (`RBM2D/Induction/ScaleFacts.lean:171`) and `chainTarget` (`RBM2D/Induction/Chain.lean:368`); RBM2D read-only; `git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the three files>` — Thu Oct  8 17:03:57 UTC 2026
```
RBM2D HEAD: 9e0f275; port source c9a24cf
 RBM2D/Induction/Chain.lean      |  90 ++++----------
 RBM2D/Induction/Defs.lean       | 259 ++++++++++------------------------------
 RBM2D/Induction/ScaleFacts.lean | 170 ++++----------------------
 3 files changed, 114 insertions(+), 405 deletions(-)
chainTime at c9a24cf: line 318; at HEAD: line 312
```
**Hygiene** (`grep -c -E 'sorry|admit|native_decide|^axiom'` on the probe; `git diff --stat 3f750b6 t/T2338`; `git log --oneline 3f750b6..t/T2338`; `git status --short | wc -l` in the worktree) — Thu Oct  8 17:03:58 UTC 2026
```
sorry/admit/native_decide/axiom lines in the probe: 0
 RBM3D/Probe/T2338Pins.lean | 399 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 399 insertions(+)
854aa29 T2338: probe: named base identity STLoopZeroId, instance of unMLOut_of_mainInd at sz0/z0, R4a example without a separate hd, show -> change (no linter warning)
92e6280 T2338: probe: generic STLocalMax-from-STLocalEntry bridge replaces the bridge premise; chainTime citation
a112ba4 T2338: probe docstring: the private zero-time chain is 120 lines (AzumaProxyN.lean:353-606)
1aa9016 T2338: probe sections 6-8 (assembly over a carrier, band and block Anderson instances, compiled examples)
2c2b2ec T2338: probe sections 4-5 (mixing at t_n = 0, chain times and the (con_st_ind) count)
58e440c T2338: probe sections 1-3 (merged-name checks, pins over a carrier, base case t = 0)
       0
```

**Narrative.** The probe (399 lines, branch only, never merged) compiles with exit 0 and no warning under `lake env lean` and `lake build`. It holds the pins of the ST-6 assembly over a carrier (`STConclgL`, `STLK0`, `STG0M`, `STBaseG`, `STHorizonG`, `STMLOutG`), the generic proofs (base case at `t ≡ 0`, mixing on the class `{t_n = 0}`, the chain of `K` strict steps with `(con_st_ind)` from `scaleFacts_R1`, the closure bridge, the assembly `stMLOutG_of_mainIndG`), the band instances (`stHorizon_band`, `stBase_band`, `unMLOut_of_mainInd`) and the block Anderson wrapper `unMLOutBA_of_pins`.
The only hypothesis beyond the pins is the named identity `STLoopZeroId` (`𝓛_0 = 𝒦_0`, private in the repository, 120 lines: B9). `STMainInd` follows from three owed pins (B12). All declarations depend on `propext`, `Classical.choice`, `Quot.sound` only (B3). No merged file is touched (hygiene). Counts, numbers and the echo of every citation of the design report are in its section 10.

## (c) Verified Mathlib names used — Thu Oct  8 17:03:58 UTC 2026

Script `usedm5.lean` (scratch; imports the built probe): the Mathlib theorems among the constants of the proof terms of `RBM.Probe.T2338.*` whose short name is written in the source (63), minus 4 that only the tactics `positivity`, `linarith`, `ext` introduce (`Even.pow_nonneg`, `pow_pos`, `Mathlib.Tactic.Linarith.zero_lt_one`, `Set.ext`): 59 names, each with its type (first 90 characters) as Lean prints it. All resolved. Names verified absent: none (no name was invented).
```
Complex.norm_le_abs_re_add_abs_im : ∀ (z : ℂ), ‖z‖ ≤ |z.re| + |z.im|
Filter.Eventually.of_forall : ∀ {α : Type u} {p : α → Prop} {f : Filter α}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
Filter.Tendsto.comp : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {g : β → γ} {x : Filter α} {y :
Filter.Tendsto.eventually_ge_atTop : ∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] {f : α → β} {l : Filter α}, Filter.Ten
LE.le.trans : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c
LE.le.trans_lt : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b < c → a < c
LT.lt.le : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
LT.lt.ne' : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
MeasureTheory.integral_const : ∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {
Nat.cast_ne_zero : ∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
Nat.cast_nonneg : ∀ {α : Type u_3} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] (n : ℕ), 
Nat.cast_ofNat : ∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.AtLeastTwo], ↑(OfNat.ofNat n) = Of
Real.exp_pos : ∀ (x : ℝ), 0 < Real.exp x
Real.mul_rpow : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → (x * y) ^ z = x ^ z * y ^ z
Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_le_one : ∀ {x z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ z → x ^ z ≤ 1
Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.rpow_lt_one : ∀ {x z : ℝ}, 0 ≤ x → x < 1 → 0 < z → x ^ z < 1
Real.rpow_lt_rpow_of_exponent_gt : ∀ {x y z : ℝ}, 0 < x → x < 1 → z < y → x ^ y < x ^ z
Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
Real.rpow_sub : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y - z) = x ^ y / x ^ z
Real.self_le_rpow_of_le_one : ∀ {x y : ℝ}, 0 ≤ x → x ≤ 1 → y ≤ 1 → x ≤ x ^ y
Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
Real.sqrt_eq_rpow : ∀ (x : ℝ), √x = x ^ (1 / 2)
Set.mem_empty_iff_false : ∀ {α : Type u} (x : α), x ∈ ∅ ↔ False
abs_of_pos : ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a : α} [AddLeftMono α], 0 < a →
add_nonneg : ∀ {α : Type u_1} {a b : α} [inst : AddZeroClass α] [inst_1 : Preorder α] [AddLeftMono α], 
div_le_div_of_nonneg_left : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀
div_le_iff₀ : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀
div_le_one : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b :
div_lt_div_of_pos_right : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀
div_nonneg : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀
div_self : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a / a = 1
exists_nat_ge : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [Archimed
half_pos : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a : α
le_rfl : ∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ≤ a
lt_min : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a < b → a < c → a < min b c
lt_of_le_of_ne : ∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ b → a ≠ b → a < b
lt_of_lt_of_le : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b ≤ c → a < c
mul_comm : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a
mul_le_mul_of_nonneg_left : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMu
mul_le_mul_of_nonneg_right : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [MulPo
mul_nonneg : ∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulMono α], 0
mul_pos : ∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulStrictMono
mul_pow : ∀ {M : Type u_4} [inst : CommMonoid M] (a b : M) (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
norm_zero : ∀ {E : Type u_4} [inst : SeminormedAddGroup E], ‖0‖ = 0
not_lt : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ a
pow_lt_pow_left₀ : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a b : M₀} [PosMul
pow_nonneg : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneCla
sub_eq_zero : ∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔ a = b
sub_self : ∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
tendsto_natCast_atTop_iff : ∀ {α : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder R] [IsStrictOrd
tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
two_ne_zero : ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], 2 ≠ 0
zero_lt_one : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : PartialOrder α] [ZeroLEOneClas
```

## (d) Open issues and paper-delta candidates

Paper-delta candidates (the dispatcher appends and numbers them; text in design section 8): `T2338a` organisation (uniform grid instead of the paper's two phases; same conclusion); `T2338b` (`lem:main_ind` does not cover `t = 0`; the base case `1_2:1240-1243` supplies it; "uniformly in `t ∈ [0,t_0]`" includes `t = 0`); `T2338c` ("uniformly in `t`" read per time sequence; the `N^{-C}`-net of `1_2:1400` in `t` is not formalised); `T2338d` (the base case needs `ML:Kbound` for `STLmax`).
Open issues for the dispatcher: (1) R1: port the 120-line private chain of `𝓛_0 = 𝒦_0` or drop `private` at `Induction/AzumaProxyN.lean:597` (one token; precedent for `private` removals: T2318, `a2c8dd6`); (2) one ticket or three for R1-R3 (sizes are estimates: design section 7); (3) registry classes of the new pins (design section 7 table, for sign-off); (4) after R4 the six owed predicate lines `STLK ... STExp2` (`Test/Axioms.lean:102-107`); (5) the BA instances of `STMainIndG`, `STBaseG`, `STHorizonG` are BA-V work (`Im m ≤ 1` for `BAm` follows from `BAm_norm_le_one`, `BAm_spec`).
Status after the branch base (design B13): T2339 is merged on main (`0853ac1`): `STDuhamelII` is proved, so `STMainInd` rests on `LWterm`, `LWtermExp` alone (both still in the registry of main) and R4 waits for LW-01 only.
Report-only merge: `docs/reports/T2338-design.md` and this report; the probe stays on `t/T2338`.
