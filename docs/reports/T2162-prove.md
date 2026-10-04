Prover model: claude-sonnet-5-5
**Size against DECISIONS §9 O2 (item 6): 52 UN proof tickets, 53614 estimated lines (mean 1031); above 50 under every packing rule (cap 1500/1300/1000 lines: 52/55/64): the dispatcher asks Jun before any UN proof ticket starts (b.6, portmap P.3).**
## (a) Math preflight — Sun Oct  4 21:25:16 UTC 2026

Scripts (scratch, no Lean): `.../scratchpad/T2162/pre.py` (table), `.../scratchpad/T2162/inst.py` (instance); stdlib Python, exact `Fraction` / float logs.
Targets here: Thm 2.4 (`1_2:444-460`) and its proof parameters (`1_2:566-581`); `(Meq:QUE)` (`1_2:407-419`) is consumed.

### (i) Exponent table at d = 3 (W-powers; N = (WL)^d; paper `𝔠,𝔡` of `1_2:358-363`)

| quantity | value | constraint | slack |
|---|---|---|---|
| `𝔠` (W ≥ N^𝔠) | any in (0, 1/d) | W ≥ N^𝔠 = (WL)^{d𝔠} ≥ (3W)^{d𝔠} forces d𝔠 < 1 (L ≥ 3, `Sizes.three_le_L`); sequence: L = W^{1/(d𝔠)-1} (ticket text says W^{1/𝔠-1}: that is the d = 1 form) | at 𝔠 = 1/6: L = W (script) |
| `𝔡` (eq:WO) | any in (0, d/2) | W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹ with W → ∞ (from W ≥ N^𝔠): 𝔡 > d/2 gives lower bound → ∞ > 𝔡⁻¹; 𝔡 = d/2 gives 1 ≤ lam ≤ 2/d < 1 | extreme row 𝔡 = 7/5 < 3/2 in script |
| `ε₀ = 𝔡/3` | 𝔡/3 | ε₀ ∈ (0, 𝔡/2) (`1_2:407`) | 𝔡/6 |
| `c = 𝔡/6` | 𝔡/6 | 0 < c < ε₀ ∧ 𝔡/5 = 𝔡/5 (`1_2:410`) | 𝔡/30 (vs 𝔡/5); 𝔡/6 (vs ε₀) |
| QUE exponent | −(2ε₀ ∧ 2𝔡/5) + 2c = −2𝔡/5 + 𝔡/3 = **−𝔡/15** | matches paper `1_2:577`: ℙ(𝓑) ≤ W^{-𝔡/15+τ} | any τ < 𝔡/15; design τ_Q = 𝔡/30 → W^{-𝔡/30} |
| 𝓑(y) energy window | `N⁻¹ W^{𝔡/3}` | ⊂ I_E(ε₀), half-width W^{-ε₀}·lam·W^{d/2}/N ≥ W^{2𝔡/3}/N by (eq:WO) | W-exponent 𝔡/3 (script col. cont.slack) |
| window in N-scale | −1 + (𝔡/3) log_N W ∈ [−1 + 𝔠𝔡/3, −1 + 𝔡/(3d)) | > −1 and < 0 (bulk stays bulk); ≥ C₀/N eventually since W → ∞ | e.g. 𝔠 = 1/6, 𝔡 = 1/10: [−1+1/180, −1+1/90) |
| 𝓑(y) threshold | `W^{-𝔡/6}` = W^{-c} (M_{y,α} normalised as N ψ*(E_a − N⁻¹)ψ = (N/W^d)(Σ_{x∈[a]}|ψ|² − W^d/N)) | ≥ W^{-c} ⇔ QUE bad event (`1_2:414`) | equality (c = 𝔡/6) |
| conversion W→N | W^{-x} ≤ N^{-𝔠x}; a smaller window / larger threshold in N-scale gives a **subset** of the W-scale event | direction checked: events in N-scale have probability ≤ W-scale ones | no loss |
| θ (good-event factor) in N | N^{-𝔠𝔡/6} | exponent of the `Jak` bound | 𝔠𝔡/6 |
| ℙ(𝓑) in N | ≤ 7 N^{-𝔠(𝔡/15−τ_Q)} (7 = 2d+1 blocks, see (iii) F3) | constant 7 ≤ W^{τ'} eventually | 𝔠𝔡/30 at τ_Q = 𝔡/30 |
| `c'_N` (Claim 417 exponent) | min(𝔠𝔡/6, 𝔠(𝔡/15−τ_Q)) = **𝔠𝔡/30** | > 0; RBM2D value 𝔠/36 (`Jak.lean:831,903`) is θ-binding (θ² = ℙ), here **ℙ(𝓑) binds** (𝔡/15 < 𝔡/6) | 𝔠𝔡/30 − 0 |
| `τ_U` | ≤ c'_N/(2(C_max+1)), C_max = 21 at k = 1 (RBM2D: `GreenCorr.lean:46-48`, Cn' = Cn + C + 1 = 1 + 19 + 1, `UnivMain.lean:355-363`, `Jak.lean:831`) | the d = 2 constants C = 3nf+16, Cn = 1 are RBM2D values, to be redone | at (𝔠,𝔡) = (1/6,1/10): τ_U ≤ 1/79200 |
| `ℙ(𝓑)` at `W ≥ N^𝔠` vs 𝔡 | the paper remark `1_2:579` ("only signs matter") | what is used: W → ∞ (window ≥ C₀/N), window < κ/2, I_E containment, c'_N > 0; **W ≥ N^𝔠 enters only in W→N conversion (c'_N = 𝔠·(W-exponent)) and in W → ∞** | 𝔠 and 𝔡 appear as the product 𝔠𝔡 |

Script `python3 pre.py` (rows (𝔠,𝔡) = (1/6,1/10), (1/4,1/5), (3/10,1/100), (1/6,7/5)), verbatim:
```
c=1/6 d=1/10: e0=1/30(slack 1/60) c_Q=1/60(slack 1/300) QUEexp=-1/150 tauQ=1/300 P(B)exp=-1/300 | cont.slack(W-exp)=1/30 | wN in[-1+1/180, -1+1/90) | P(B)->N^-1/1800 theta->N^-1/360 c'=1/1800 tau_U<=1/79200
c=1/4 d=1/5: e0=1/15(slack 1/30) c_Q=1/30(slack 1/150) QUEexp=-1/75 tauQ=1/150 P(B)exp=-1/150 | cont.slack(W-exp)=1/15 | wN in[-1+1/60, -1+1/45) | P(B)->N^-1/600 theta->N^-1/120 c'=1/600 tau_U<=1/26400
c=3/10 d=1/100: e0=1/300(slack 1/600) c_Q=1/600(slack 1/3000) QUEexp=-1/1500 tauQ=1/3000 P(B)exp=-1/3000 | cont.slack(W-exp)=1/300 | wN in[-1+1/1000, -1+1/900) | P(B)->N^-1/10000 theta->N^-1/2000 c'=1/10000 tau_U<=1/440000
c=1/6 d=7/5: e0=7/15(slack 7/30) c_Q=7/30(slack 7/150) QUEexp=-7/75 tauQ=7/150 P(B)exp=-7/150 | cont.slack(W-exp)=7/15 | wN in[-1+7/90, -1+7/45) | P(B)->N^-7/900 theta->N^-7/180 c'=7/900 tau_U<=7/39600
L=W^(1/(d c)-1): {'1/6': '1', '1/4': '1/3', '3/10': '1/9'}
```

### (ii) One nondegenerate instance (d = 3)
Data: `RBM.Gauss.SizesInst.sz0` (`RBM3D/Defs/Sizes.lean`, checks section): L_n = 4(n+1), W_n = (2(n+1))^5, lam_n = (2(n+1))^{-6}, N_n = (W_n L_n)^3 (n = 0: L = 4, W = 32, N = 2097152); 𝔠 = 1/6, 𝔡 = 1/10, κ = 1/10, k = 1, ε₀ = 𝔡/3, c = 𝔡/6, τ_Q = 𝔡/30.
Hypotheses checked: Admissible (W ≥ N^𝔠, (eq:WO), L ≥ 3, N → ∞), QUE parameters, 𝓑(y)-window ⊂ I_E, and the premises of the external L32 (the limit computation: see below). The ℙ(𝓑) bound is an "eventually" statement (7 W^{-1/300} < 1 needs W > 7^{300}); it is a conclusion, not a hypothesis of the instance.
Command `python3 inst.py`, verbatim:
```
n=0: L=4 W~32 lam=1.56e-02 log10N=6.32 | W>=N^c:True WO:True bad-window<=I_E:True(log slack 0.81) QUEparams:True L32prem:(True, True, True, True)
n=1: L=8 W~1.02e+03 lam=2.44e-04 log10N=11.74 | W>=N^c:True WO:True bad-window<=I_E:True(log slack 1.62) QUEparams:True L32prem:(True, True, True, True)
n=100: L=404 W~3.36e+11 lam=1.47e-14 log10N=42.40 | W>=N^c:True WO:True bad-window<=I_E:True(log slack 6.19) QUEparams:True L32prem:(True, True, True, True)
n=1000000: L=4000004 W~3.2e+31 lam=1.56e-38 log10N=114.32 | W>=N^c:True WO:True bad-window<=I_E:True(log slack 16.93) QUEparams:True L32prem:(True, True, True, True)
n=0 exact: N= 2097152 W^(-d/2+D)= 0.007812500000000002 lam= 0.015625 N^(1/6)= 11.31370849898476
rho_sc lower bound on |E|<=2-kappa: 0.09939223010440976 = sqrt(4k-k^2)/2pi: 0.09939223010440974 ; rho_sc(0)= 0.3183098861837907
L32 exps tau=1.26e-05: sigma=3.157e-06; sigma<=tau/4:True; (-1+tau/4)<=-sigma:True; 3sigma<=1-tau:True; N^(tau/2)>=2 needs N>=2^(2/tau): log10=4.77e+04
L32 exps tau=0.5: sigma=0.125; sigma<=tau/4:True; (-1+tau/4)<=-sigma:True; 3sigma<=1-tau:True; N^(tau/2)>=2 needs N>=2^(2/tau): log10=1.2
ev5 threshold (RBM2D Jak.lean:872 shape) N>=10^1.412e+05: an 'eventually' threshold, not a witness
all instance checks: True
```
L32 limit computation at d = 3 (external input, DECISIONS §5; RBM2D `Universality/Pins.lean:156` `L32`, applied at `GUETranslation.lean:827` with q = 1/2, c = min κ 1/960, C = CV = 2, δ = σ = min(τ/4, (1−τ)/3), g = N^{-1+τ/4}, G = N^{-σ}, t = 1 − e^{-N^{-1+τ}} ≥ N^{-1+τ}/2, E = 0). Premises: N^σ/N ≤ g (σ ≤ τ/4), g ≤ N^{-σ} (σ ≤ 1 − τ/4), g N^σ ≤ t (needs N^{τ/2} ≥ 2), t ≤ N^{-σ}G² = N^{-3σ} (3σ ≤ 1 − τ), |E| ≤ qG. They involve only the size N (not d, W, L): the printed lines show them at τ = 1/2 and τ = 1/79200; the only d-dependence is the carrier `Idx`/`gueP` of an N×N GUE with N = (WL)^3. Density: L32's conclusion already carries a sequence ρ_n (dilation by each side's own density), so it serves ρ = ρ_sc (band) and ρ = ρ_N (BA, DECISIONS §11); lower bound ρ_sc ≥ sqrt(4κ−κ²)/(2π) = 0.0994 on |E| ≤ 2 − κ (script) gives the abstract positive lower bound for target 2(b).

### (iii) d = 2 facts in the RBM2D universality closure beyond tokens (c9a24cf; closure of `Main/BUnivHolds.lean`: 58 files / 61014 lines by script)
- F1 `Universality/QUEFlow.lean:463,473,568` and `ZeroModeProfile.lean:393`: the 𝐇_t QUE (`OUQUE`, `QUEFlow.lean:12`) uses the **d = 2 propagator oscillation bound 90(1 + log L)** (`ZeroModeProfile.lean:387-393`) and the QUE scale η_Q = W^{2/3}/N. At d = 3 the paper has no log: the oscillation is ≺ lam^{-2} (`1_2:537`, from `prop:ThfadC`, `prop:BD1`), and the scale is W^{-ε₀} lam W^{d/2}/N. Also `OneLoop.lean:1151-1272`, `EntryDet.lean:631-633` (cShortRow·(1 + log L), (1 + log L)): critical-dimension log factors of the GUE-phase loop bounds; they need the d = 3 form.
- F2 `ZeroModeProfile.lean:197` ("no admissible band profile is flat in d = 2", card sbSupport = 5 < L²) and `Pins.lean:189` `GUELocal` remark: the argument is about the support size; at d = 3, `flucVanish_card_sbSupport` = 2d+1 = 7 (`RBM3D/Green/FlucVanish.lean:63-65`) < L³ for L ≥ 3 is the d = 3 version, to be rechecked (L = 3: 7 < 27).
- F3 `JakSpectral.lean:182-196,535-570`, `Jak.lean:702`, `Uyw.lean` header: M_{y,α} is the **equal-weight 1/5 average** over the 5-point support {0, ±e₁, ±e₂} (RBM2D S^(B) at lam = 1), union bound 5ε'. At d = 3 the paper's S^(B)_{ab} = 1_{a=b}/(1+2d lam²) + lam² 1_{a∼b}/(1+2d lam²) (`1_2:303-306`) has **lam-dependent weights**, 2d + 1 = 7 blocks; M_{y,α} for d ≥ 3 is not defined in the TeX (it cites (2.24) of [DYYY25]). A convex weighted average still gives ℙ(𝓑) ≤ (2d+1)·ℙ(QUE bad) (a convex combination of block quantities is ≥ θ only if some block quantity is ≥ θ); the definition (S^(B)-weighted vs uniform) must be fixed in the pin, paper-delta candidate T2162a.
- F4 \`Universality/GUEPhase/*\` (25 files, 278–2355 lines each, Z2-token counts 0–124 per file) is the UN-side loop expansion on the Z2 index and must be re-derived at d = 3 (Z2 → \`Zd d\`, N = (WL)^d). \`Pins.lean:238,250\` (\`P7Out\`, \`P7ExpOut\`: the ML:GLoop / ML:GLoop_expec / ML:GtLocal outputs for every time sequence with 1 − t ≥ N^{-1+τ}) are consumed from MA. The d = 3 paper states these at fixed z ∈ D_{κ,ε} uniformly in t ∈ [0, t_0] (\`1_2:1193-1226\`); the interface shape (fixed-z vs time-sequence) is "MA pin to be frozen". Beyond (Meq:QUE) the 2D chain also consumes QUE and a diagonal local law for 𝐇_t, t ≤ t* = N^{-1+τ_U} (\`OUQUE\`, \`OUDiag\`, \`Pins.lean:206,218\`); the paper lists only MR:decol, MR:locSC, (Meq:QUE) as inputs (\`1_2:567-568\`) and says the rest "proceeds exactly as in" [DYYY25] Thm 2.6 (\`1_2:579\`): paper-delta candidate T2162b (the interface is larger than the paper's list).
- F5 (Meq:QUE) at d ≥ 3 has the window W^{-ε₀} lam W^{d/2}/N with lam possibly > 1 (up to 𝔡⁻¹); the footnote at `1_2:372` replaces lam by lam ∧ 1 there. Only the lower bound W^{-ε₀}·(lam ∧ 1)·W^{d/2} ≥ W^{2𝔡/3} is used (true since 𝔡 < d/2), so the table is unchanged.

### Verdict per target
1 Inventory: PASS (closure computed: 58 universality files, 61014 lines; per-file d = 2 token counts are scriptable; outside-layer imports: 325 other files in the transitive closure, mapped in stage 1b).
2(a) PASS; 2(b) PASS (abstract density ρ with ρ ≥ sqrt(4κ−κ²)/(2π) at ρ_sc; BA bulk condition abstract per ticket); 2(c) PASS (L32 premises close at d = 3); 2(d) PASS (parameters of 𝓑(y) close, table rows 3-8).
3 Exponent table: PASS. 4 Interfaces: PASS with "MA/BA pin to be frozen" entries (F4). 5 Skeleton, 6 Split, 7 Instances: not testable here; instance of (ii) shows the hypothesis set is nonempty and nondegenerate.
Overall: **PASS** (no hypothesis set is empty, every exponent closes; findings F1–F5 are inputs for stage 1b, none is a missing input).

## (a′) Preflight corrections — Sun Oct  4 22:35:05 UTC 2026
- (a) (iii) F2: `flucVanish_card_sbSupport` is at `RBM3D/Green/FlucVanish.lean:1079` (the cited `:63-65` is the module docstring that mentions it).  No number, instance or verdict of (a) changes.  Replay of the two scripts of (a) (`python3 pre.py`, `python3 inst.py`, compared with the two code blocks of (a)): identical (5 and 10 lines).

## (b) Script output — Sun Oct  4 22:35:05 UTC 2026; probe `RBM3D/Probe/T2162Pins.lean` (branch `t/T2162`, commit `73b451c`, base `a21a819`); tables, split, scripts: `docs/reports/T2162-portmap.md` (P.1-P.5)
### b.1 Build, axioms, hygiene
```
$ git log --oneline a21a819..HEAD | wc -l; git diff --name-only a21a819 HEAD; git status --short | wc -l
6
RBM3D/Probe/T2162Pins.lean
0
$ lake build RBM3D.Probe.T2162Pins > build.out 2>&1; tail -1 build.out; grep -c "error\|warning: RBM3D/Probe" build.out
Build completed successfully (3328 jobs).
0
$ lake env lean RBM3D/Probe/T2162Pins.lean > lean.out 2>&1; echo exit=$?   (the acceptance command of the ticket)
exit=0
0  (lines of lean.out that are not `#print axioms` output: no warning, error or other message)
$ tail -1 lean.out
'RBM.Univ.UNInst.inst_core_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep "depends on axioms" lean.out | sed "s/.*axioms: //" | sort | uniq -c
 139 [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2162Pins.lean; grep -c "^import RBM3D" RBM3D/Probe/T2162Pins.lean; wc -l < RBM3D/Probe/T2162Pins.lean
0
6
2041
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the six ported files: Universality/{Pins,Step1RegularityA,Step1RegularityB,GUETranslation,GreenCorr}.lean, Endpoints.lean> | tail -3   (every RBM2D citation is at c9a24cf; HEAD differs from it, statements not re-compared at HEAD)
9e0f275
 RBM2D/Universality/Step1RegularityA.lean |  90 ++-----
 RBM2D/Universality/Step1RegularityB.lean | 133 ++--------
 6 files changed, 299 insertions(+), 816 deletions(-)
$ grep -c "^def UN" RBM3D/Probe/T2162Pins.lean; grep -c "^theorem inst_" RBM3D/Probe/T2162Pins.lean; grep -c "^theorem " RBM3D/Probe/T2162Pins.lean   (pins; instance theorems; all theorems)
37
28
76
$ python3 clash.py   (grep -rnE "(def|theorem|structure|abbrev) (<every name declared in the probe, 109, except inst_*>)\b" RBM3D, Probe excluded: number of matches on main)
names checked: 111
0
```
### b.2 Item 1: inventory of the closure of `Main/BUnivHolds.lean` at RBM2D `c9a24cf` (per-file table P.1, declaration-level replacement table P.2)
```
$ python3 inv.py | grep -E "^TOTAL|^CLOSURE"   (58 files = `Universality/**` + `Main/BUniv*.lean` in the closure; kept = lines at 0c1330a, T2002 portmap)
TOTAL files=58 lines=61014 kept=51594 tokens(Z2,W^2,L^2,N=(WL)^2,ell_t,logL)=[1085, 169, 429, 280, 134, 75]
CLOSURE 383 files 260575 lines; by layer: {'Path': 42, 'Gauss': 41, 'Universality': 56, 'Hierarchy': 37, 'Induction': 59, 'Propagator': 56, 'Green': 34, 'Main': 9, 'Defs': 7, 'Loop': 16, 'Evolution': 24, 'root': 2}
$ python3 deps.py | sed -n "1p;12p"   (declarations of the 325 other closure files used by the 58 files; per layer in portmap P.2; found = same bare name on main)
layer | modules used | declarations used | found by name on main | missing by name
root | | | 2 | 20 | 3 | 17
```
Missing by name on main (131 of 415 used declarations; portmap P.2 lists every one): d = 2 vocabulary with a d >= 3 replacement (`sbSupport`->`flucVanish_sbSupport`, `Spaper`->`svarF`, `Meta`/`ellz`/`scaleM`->`Sizes.Bctl`/`ellT`), the endpoint vocabulary of RBM2D `Endpoints.lean` (`BUniv`, `locSC`, `QDiff`, `queBad`, `window`: MA freeze; `kPoint`, `gueP`, `gueVar` are redefined in the probe), the ML outputs of ST-6 (`MLConcl`, `MLExpConcl`), and `Main/ZRescale`, `Main/QUEFromQDiff` (MA).
| row of RBM2D `Universality/Pins.lean` | files | lines | kept | tickets (P.3) |
|---|---|---|---|---|
| OURow: `GUEPhase/*` (25 files), `ZeroModeProfile`, `QUEFlow` | 27 | 34765 | 27919 | UN-25 .. UN-52 |
| Infty1Row (Step 1, `L32`): `Step1*`, `GUEInvariance`, `GUETranslation`, `GUELocal*`, `FreeConv*` | 11 | 10965 | 9981 | UN-06 .. UN-14 |
| EMCTE2Row: `OUGenerator`, `OUHessian`, `OUContraction`, `EMCTE2` | 4 | 4300 | 3973 | UN-15 .. UN-18 |
| JakUywRow: `Jak*`, `Uyw*` | 5 | 5186 | 4632 | UN-19 .. UN-23 |
| GreenCorr + UnivMainRow + ClaimRow: `GreenCorr`, `Poisson`, `InjSum`, `Eigen*`, `Apriori`, `UnivMain` | 7 | 4669 | 4234 | UN-03 .. UN-05, UN-18, UN-24 |
| pins, OU carrier, final: `Pins`, `OU`, `Main/BUniv*` | 4 | 1129 | 855 | UN-01, UN-02, UN-52 |
| total | 58 | 61014 | 51594 | 52 tickets |
d = 2 tokens by file (regex, P.1): `Z2` 1085 (`GUEPhase/*`: 965), `W^2` 169, `L^2`/`(WL)^2` 429/280, scales (`ellT`, `scaleM`, `Meta`, `tailT`) 134, `log` 75; the d = 2 *arguments* beyond tokens are the findings F1-F5 of (a) (iii): `log L` oscillation (`QUEFlow`, `ZeroModeProfile`, `OneLoop`, `EntryDet`), the five-point support (`JakSpectral`, `Jak`, `Uyw*`, `AuxCarrier`), the GUE-phase carrier on `Z2`.
### b.3 Items 2 and 5: the pins (probe) and the skeleton; statements extracted by script
```
$ grep -n "^def UN" RBM3D/Probe/T2162Pins.lean | sed "s/(.*//;s/ : Prop.*//" | tr "\n" " "   (pins with their line)
UNModel:115 UNModel:124 UNBUniv:176 UNUnivDilAt:194 UNL32:280 UNQueBand:403 UNLocAvgBand:415 UNMLOut:431 UNTrLocal:446 UNDens:461 UNNormBound:476 UNGUELocal:488 UNClaim417:507 UNClaimAll:515 UNApriori:521 UNGreenCorr:534 UNGreenCorrAll:545 UNInfty1:551 UNUnivMain:562 UNStep1Good:583 UNOUQUE:636 UNOUDiag:647 UNOUClaims:658 UNEMCTE2:668 UNJak:693 UNUyw:707 UNInfty1Row:732 UNUnivMainRow:744 UNCore:759 UNOURow:792 UNEMCTE2Row:796 UNJakUywRow:804 UNClaimRow:814 UNDensBandRow:825 UNNormBandRow:833 UNTrLocalBandRow:841 UNBadY:1146 
$ sed -n "176,184p" RBM3D/Probe/T2162Pins.lean
def UNBUniv : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        Tendsto (fun n =>
          (∫ ω, kPoint k O E (Sizes.seqXmat_isHermitian sz n ω).eigenvalues ∂(Sizes.seqP sz)) -
          (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))))
          atTop (𝓝 0)
$ sed -n "759,766p" RBM3D/Probe/T2162Pins.lean
def UNCore : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAll →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          UNClaimAll sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M ρ E E' k O
$ sed -n "636,642p" RBM3D/Probe/T2162Pins.lean
def UNOUQUE (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ τQ : ℝ, 0 < κ → 0 < τQ → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
      ouP (UNModel.band sz) n
          {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a
            (ouMat (UNModel.band sz) n t ω)} ≤
        queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ
$ sed -n "1204,1208p" RBM3D/Probe/T2162Pins.lean
theorem unBadY_subset (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (y : Idx d L W)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : UNBadY d L W lam 𝔡 E y M) :
    ∃ b : Zd d L, SBR d L lam b (split d L W y).1 ≠ 0 ∧
      queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b M := by
```
Not pasted (statement in the probe at the line above): `UNL32` (port of RBM2D `Pins.lean:156`), `UNStep1Good`, `UNTrLocal`, `UNDens`, `UNClaim417`, `UNEMCTE2`, `UNJak`, `UNUyw`, `UNGreenCorr`, the rows, `UNBadY`, `unBadY_measure_le`.  Sources, consumers (file:line at c9a24cf), registry class and the §29 items (5)-(7) per pin: portmap P.4.  Compiled skeleton (`inst_bUniv_band`, `inst_core_band`, `inst_core_ba`, `inst_claimAll_band`, `inst_core_of_rows`): `un_bUniv_of_rows` gives `UNBUniv` at `sz0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `k = 1`, `κ = 1/10`, `E = 0`, `𝒪 = bump`) from the rows, `UNL32`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNGUELocal`, `UNGreenCorrAll`; `UNCore` is applied to `UNModel.band sz0` (density `UNDens` discharged by the proved `un_dens_msc_zero`, `ρ = ρ_sc(0)`) and to `UNModel.ba sz0` (BA data as hypotheses).
| pin (probe line) | RBM2D source (c9a24cf) | consumer there | class | §29 (5) | (6) | (7) |
|---|---|---|---|---|---|---|
| `UNBUniv` (176) | `Endpoints.lean:209` | `Main/BUnivHolds.lean:32` | owed | - | `Admissible` | `kPoint` | 
| `UNL32` (280) | `Pins.lean:156` | `GUETranslation.lean:827` | borrowed | - | `Tendsto size` | `N` only |
| `UNGUELocal` (488) | `Pins.lean:189` | `GUETranslation.lean:60` | owed | `∩_z` inside | `Tendsto size` | `N^τ(Nη)^{-1/2}` |
| `UNTrLocal` (446) | `Step1RegularityA.lean:748` | `Step1RegularityB.lean:339` | owed | `∩_z` inside | via `Bctl` (`un_Bctl_le`) | `W^τ` |
| `UNDens` (461) | new (DECISIONS §11) | `Step1RegularityB.lean:228, 470` (`Step1RegularityB_msc_im_ge`, its use) | structural | - | - | - |
| `UNStep1Good` (583) / `UNNormBound` (476) | `Step1RegularityB.lean:817`; `Step1RegularityB_eigenvalue_le` | `Step1Band.lean:1037` | owed | `x`, `z`, `i` inside | `τ_s ≤ 𝔠𝔡`; `CV₀ ≥ 0` | `N^{-3τ_s/8}`, `N^{CV₀+1}` |
| `UNClaim417` (507) / `UNGreenCorr` (534) | `Pins.lean:267`, `:359` | `GreenCorr.lean:644` | owed | per `t` | `c' > 0` | `N^{-c'+C_nτ_U}` |
| `UNOUQUE` (636) / `UNOUDiag` (647) | `Pins.lean:206`, `:218` | `Jak.lean:904` | owed | per `(t,E,a)` / `x` inside | `Admissible` | `W^{-𝔡/15+τ}` / `N^ε` |
| `UNEMCTE2` (668) / `UNJak` (693) / `UNUyw` (707) | `Pins.lean:288`, `:313`, `:331` | `UnivMain.lean:362` | owed | - | `0 ≤ B`; `c' = 𝔠𝔡/30` | `N^ε N^{1-c'+Cτ_U}` |
| `UNLocAvgBand` (415) / `UNQueBand` (403) / `UNMLOut` (431) | `Endpoints.lean` `locSC`, `QUE`; `Pins.lean:238, 250` | `Step1RegularityA.lean`; `ZeroModeProfile.lean:712`; `RandomLayerA.lean:738` | owed (MA, ST-6) | `∩_z` inside / sequences | `Admissible`, `STFlow` | `W^τ` |
Ticket 2(b) inputs -> pins: local law on `D_{κ,ε}` -> `UNTrLocal` (window `|Re z - E| ≤ δ`; band: from `UNLocAvgBand`); delocalization -> `UNOUDiag` (of `𝐇_t`, `t ≤ t*`); `(Meq:QUE)` at `(ε₀,c)` -> `UNOUQUE` (of `𝐇_t`, `t ∈ [0,t*]`, used by `UNJak`, `UNUyw` through `UNBadY`; `t = 0` is `UNQueBand`); density with positive lower bound and regularity -> `UNDens` (`c ≤ Im m ≤ C`, Lipschitz, `ρ_n = π⁻¹ Im m_n(E+i0) ≥ c/π`).
LSY [32] check of `UNL32` (target 2(c)): arXiv:1609.09011, latest version v4 (`Wed, 30 Sep 2026 15:17:09 UTC`, from `arxiv.org/abs/1609.09011`, fetched today); text of v4 from `arxiv.org/html/1609.09011v4` (command and output):
```
$ python3 lsycheck.py   (substring checks of lsy.txt; script verbatim in portmap P.5)
True | N^{-\delta}\geq g\geq N^{\delta}/N and G\leq N^{-\delta}
True | c\leq\mathrm{Im}\mbox{ }[m_{V}(E+\mathrm{i}\eta)]\leq C for |E|\
True | ||V||\leq N^{C_{V}}
True | gN^{\sigma}\leq t\leq N^{-\sigma}G^{2}
True | \frac{1}{V_{i}-z-tm_{\mathrm{fc},t}(z)}
True | \rho_{\mathrm{fc},t}(E):=\lim_{\eta\downarrow 0}\frac{1}{\pi}\ma
True | hold also for the compl
(2.9) has rho_fc,t(E)^k on the left and rho_sc(E)^k, p_GOE on the right at the same E: True
```
Reading: the premises of `UNL32` are Def 2.1 `(2.2)`, `(2.3)`, `(2.5)`, `(2.6)`, `(2.8)` of v4; `(2.9)` compares both sides at the same `E` with the dilations `ρ_fc,t(E)`, `ρ_sc(E)` as in `UNL32`; the Remark states the complex Hermitian case.  The condition `|E| ≤ qG`, `q < 1` of Thm 2.2 is garbled in the HTML export (`Let 0 0`) and is read as in RBM2D `Pins.lean:158` (not re-verified here).  The arithmetic premises at the OU time `t = 1 - e^{-N^{-1+τ}}` are `un_L32_arith` (b.7); the regularity premise is `UNStep1Good` (b.4).
### b.4 Item 3: additions to the exponent table of (a) (d = 3, exact fractions; `python3 exps2.py`)
```
c,d | Step1 range tau_s<=cd (sharp 16cd/(3+c)) | floor N^-(2cd) vs target 15tau_s/16 at tau_s=cd | window exps in N [cd/3, d/(3d)) | theta exp cd/6, P(B) exp c(d/15-tQ), c' | R1 c'<=a_w=cd/3 | R2 tau_U<=c'/44 < a_w/2 | sigma at tau_s=cd
1/6,1/10 | 1/60 (0.08421) | 0.03299 >= 0.01562: True | [1/180, 1/90) | 1/360, 1/1800, 1/1800 | True | 1/79200 < 1/360: True | 1/240
1/4,1/5 | 1/20 (0.24615) | 0.09844 >= 0.04688: True | [1/60, 1/45) | 1/120, 1/600, 1/600 | True | 1/26400 < 1/120: True | 1/80
3/10,1/100 | 3/1000 (0.01455) | 0.00589 >= 0.00281: True | [1/1000, 1/900) | 1/2000, 1/10000, 1/10000 | True | 1/440000 < 1/2000: True | 3/4000
1/6,7/5 | 7/30 (1.17895) | 0.46181 >= 0.21875: True | [7/90, 7/45) | 7/180, 7/900, 7/900 | True | 7/39600 < 7/180: True | 7/120
```
| parameter | RBM2D (d = 2) | this paper (d ≥ 3) | source |
|---|---|---|---|
| window of `𝓑` | `|λ_α-E| ≤ N^{-1+𝔠/6}` | `N^{-1}W^{𝔡/3} ⊂ 𝓘_E(𝔡/3)`, half-width `≥ W^{2𝔡/3}/N`; in `N`: `[-1+𝔠𝔡/3, -1+𝔡/(3d))` | `1_2:570-575`, `un_window_sub`, `un_window_N_scale` |
| threshold of `|M_{y,α}|` | `N^{-𝔠/18}` (paper), `N^{-𝔠/36}` (RBM2D, squared quantity) | `W^{-𝔡/6}` | `1_2:571` |
| `ℙ(𝓑)` | `O(N^{-𝔠/18})` | `W^{-𝔡/15+τ}`, `2d+1 = 7` blocks, `≤ N^{-𝔠(𝔡/15-τ)}` | `1_2:577`, `unBadY_measure_le`, `un_que_exponent` |
| QUE input | `τ = 𝔠/3`, bound `N^{-τ/6}` | `(ε₀,c) = (𝔡/3,𝔡/6)`, `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}` | `1_2:407-417`, `un_que_params` |
| `c'` of Jak/Uyw | `𝔠/36` (`θ` binds) | `𝔠𝔡/30` at `τ_Q = 𝔡/30` (`ℙ(𝓑)` binds; any value `< 𝔠𝔡/15`) | `un_cprime` |
| Step-1 range | `τ_s ≤ 𝔠` | `τ_s ≤ 𝔠𝔡` | `un_step1_floor` |
| `τ_U` of `(417)` | `≤ c'/(2(C_max+1))` | same shape; `1/79200` at `(1/6, 1/10)`, `C_max = 21`, RBM2D constants | `un_claim_exponent` |
- Where `W ≥ N^𝔠` matters (compiled: `un_W_neg_le`, `un_step1_floor`, `un_window_N_scale`): the conversions `W^{-x} ≤ N^{-𝔠x}` of `ℙ(𝓑)`, `θ` and of the local-law floor `W^{-2𝔡}` (Step 1: `τ_s ≤ 𝔠𝔡`, RBM2D `τ_s ≤ 𝔠` where the floor is `W^{-2}`), and `W → ∞`.  `𝔡` matters through `lam ≥ W^{-d/2+𝔡}` (floor `W^{2𝔡} ≤ lam² W^d`, `un_Bctl_le`) and through `ε₀ = 𝔡/3`, `c = 𝔡/6`.  Ranges proved: `𝔠 d < 1` (`un_dc_lt_one`), `𝔡 < d/2` (`un_d_lt_half`).
- The remark `1_2:579` ("only signs of the exponents matter") holds in the form: the final statement needs `τ_U` small depending on `(𝔠,𝔡)`, but the argument uses three orderings, all with slack at `d = 3` (columns R1, R2 above; R3 = `un_window_sub`): (R1) `θ`-exponent `c'` ≤ window exponent `𝔠𝔡/3` (RBM2D `Jak.lean:137-180`, `Jak_alpha1_le`: `w' = N^{-1+c/6}/2`, `θ = N^{-c/36}`, final exponent `2 - c/36 + 4τ + 2δ`); (R2) `2τ_U` < window exponent; (R3) the `𝓑(y)` window `N^{-1}W^{𝔡/3}` lies in `𝓘_E(𝔡/3)`.  `ℙ(𝓑)` (exponent `𝔠(𝔡/15-τ_Q)`) binds, not `θ` (RBM2D: `θ` binds).
### b.5 Item 4: interfaces consumed (exact statements in the probe; producer pin = file:line when merged, else "to be frozen")
| consumed by UN | from | probe pin | producer |
|---|---|---|---|
| `(G_bound_ave)` with `∩_z` inside (`1_2:391-399`) | MA | `UNLocAvgBand` (:415) | MA pin to be frozen (`T2001_locSC` second half, `bd95cc9:RBM3D/Probe/T2001Endpoints.lean:147-166`) |
| `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` at `z`-sequences, `t ≤ lemT z` (`1_2:1193-1226`) | ST-6/MA | `UNMLOut` (:431), shape = conclusions of merged `STMainInd` (`Induction/Defs.lean:294`: `STLK`, `STLmax`, `STDecay`, `STExp2`, `STLocalEntry`) | ST-6 pin to be frozen |
| `(Meq:QUE)`, `ε₀ ∈ (0,𝔡/2)`, `c < ε₀ ∧ 𝔡/5` (`1_2:407-417`) | MA | `UNQueBand` (:403) | MA pin to be frozen (`T2001_QUE` first half, `:195`).  **Not used by the RBM2D route**: `OURow` does not use `QUE`, `locSC` (RBM2D `ZeroModeProfile.lean:712-713`: the pins already include `t = 0`); kept as the paper's list (`1_2:568`) |
| `MR:decol` | MA | none | `decol` occurs in RBM2D `Universality/` only in a docstring (`Pins.lean:217`); delocalization of `𝐇_t` is `UNOUDiag` |
| propagator `Θ_ξ`, `Θ̊`: properties 5-8 | PT (merged) | - | `prop5to8_holds` (`Propagator/Prop6Hold.lean:433`), `Prop8ZeroMode` (`Propagator/Pins.lean:87`); replaces RBM2D `norm_ThetaTilde_sub_le` `90(1+log L)` (`ZeroModeProfile.lean:391`) by `λ^{-2}` (`1_2:537`) |
| `2d+1` support, row sums of `S^{(B)}` | merged | - | `flucVanish_card_sbSupport` (`Green/FlucVanish.lean:1079`), `sum_SBR_row` (`Propagator/Gap.lean:206`), `svarF_diag` (`Gauss/FineModel.lean:61`) |
| from BA-D1 for `UNCore` (2(b)) | BA | `UNModel.ba sz`; `m n = m(·, λ_n)`, `ρ n = π⁻¹ Im m_n(E+i0)`; `UNDens m E ρ δ` (bulk condition of T2001d/l); `UNTrLocal sz (ba) m E δ`; `UNNormBound sz (ba) CV₀` (`‖V‖ + λ‖Ψ‖ ≤ N^{CV₀}` w.h.p.); `UNClaimAll sz (ba) E` (BA analogues of `UNOUQUE`, `UNOUDiag`, `UNEMCTE2` with drift, `UNJak`, `UNUyw`) | BA-D1 pins to be frozen |
### b.6 Item 6: split table (full table P.3: files, statements, RBM2D sources with line, deps, role)
```
$ python3 split.py | tail -6
| UN-52 | GUE phase / OU claims + final assembly: QUEFlow, Main/BUniv, Main/BUnivHolds | g2bRow: OUQUE for H_t from (7.47) at the QUE scale, Markov step; FINAL: un_bUniv_of_rows (UNBUniv from the rows
TOTAL tickets 52 est lines 53614
GUE-phase tickets at caps 1000/1300/1500: {1000: 40, 1300: 31, 1500: 28}  non-GUE-phase tickets: 24
count at cap 1000/1300/1500: {1000: 64, 1300: 55, 1500: 52}
min/mean/max est 724 1031 1455
Counter({'prover-hard': 39, 'prover': 7, 'prover-max': 6})
```
- UN-01 .. UN-07: pins, OU carrier, spectral/GreenCorr/Poisson, free convolution (band UN-06; NEW regular density UN-07)
- UN-08 .. UN-14: GUE side: invariance, local law (Schur, bootstrap), Step 1 (regularity, Band, translation)
- UN-15 .. UN-24: Green comparison: OU generator/Hessian/contraction, EMCTE2, Jak/Uyw kernels, UnivMain
- UN-25 .. UN-52: GUE phase (OU claims): 25 files `GUEPhase/*` + `ZeroModeProfile` + `QUEFlow` (+ final assembly in UN-52)
- Estimated lines = RBM2D kept lines plus adjustments that are estimates, not measured: `Pins` +350, `GreenCorr` +100, `Step1RegularityA` -577, `Step1RegularityB` +500, `JakSpectral` +300, `GUETranslation` +150, `UnivMain` +250, UN-07 800 (new), final assembly +258 (portmap P.3).
- Roles: prover-hard 39, prover 7, prover-max 6.  Risk: UN-07 (new mathematics, only for the BA consumption), UN-12 (`UNStep1Good` at `d ≥ 3` and `msc` regularity for every bulk `E`), UN-31 `Proc`, UN-45 `OneLoop` (`log L` factors, d ≥ 3 form), UN-51/52 (`Θ̃` oscillation, QUE for `𝐇_t`).
### b.7 Item 7: compiled instances at `d = 3` (all in the probe, `namespace RBM.Univ.UNInst`; `#print axioms`: b.1)
inst_dc_lt_one inst_d_lt_half inst_L32_arith_half inst_L32_arith_sharp inst_que_exponent inst_que_params inst_cprime inst_claim_exponent inst_window_sub_lower_edge inst_window_sub_inst inst_window_sub_upper_edge inst_W_neg_le inst_step1_floor inst_window_N_scale inst_Bctl_le inst_const_absorb inst_rhoSC_lower inst_rhoSC_edge inst_rhoSC_lip inst_dens_msc inst_badY_subset inst_badY_measure inst_badY_card inst_bUniv_band inst_core_band inst_core_ba inst_claimAll_band inst_core_of_rows 
Data: `sz0` (`L=4`, `W=32`, `lam=1/64`, `N=2097152` at `n=0`), `𝔠=1/6`, `𝔡=1/10`, `κ=1/10`, `E=0`, `𝒪=bump` (`bump 0 = 1`, `bump = 0` at `‖x‖ ≥ 2`: `bump_nondegenerate`).  Other-gate pins stay hypotheses of the skeleton instances; every deterministic hypothesis is discharged, including `UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1/2)` (`un_dens_msc_zero`: `9/100 ≤ Im msc ≤ 1`, Lipschitz `10000/81`, limit `1/π`) and a nonempty bad event (`badY_zero`: the zero matrix with the standard basis, `|M_{y,y}| ≈ 62.9 ≥ 1 ≥ W^{-𝔡/6}`).
Extreme inputs tried (per pin: portmap P.4): `|E| = 2-κ` (`un_rhoSC_edge`: the lower bound is attained), `lam = W^{-d/2+𝔡}` and `lam = 𝔡⁻¹` (`inst_window_sub_*`), `τ = 1/2` and the threshold `N = 2^{2/τ}` of `UNL32` (`inst_L32_arith_*`), `τ_s = 𝔠𝔡` (`inst_step1_floor`), `k = 0` (`unUnivDilAt_zero`, `kPoint_zero`), `k > N` (`kPoint_eq_zero_of_card_lt`), `W^{τ/2} ≥ 2d+1` of `un_const_absorb` (asymptotic: instantiated at `W = 2^{200}`, not at `sz0`), `n_f = 0` (`un_emcte2_zero`; `un_not_emcte2_zero_noB`: without `0 ≤ B` false), `n_f = 1` (`un_uyw_one`).
### b.8 Narrative
1. Verdict: targets 1-7 delivered; the probe compiles (b.1) with 137 declarations on the three standard axioms; nothing is left as `sorry`.  The count of UN proof tickets is above 50 (top line).
2. Design: the core `UNCore` is stated for an abstract model `UNModel` (law + Hermitian matrix family on `SeqΩ sz`; `UNModel.band`, `UNModel.ba` compile) and an abstract density `m n`, `ρ n`.  It takes the Claim `(417)` (`UNClaimAll`) as input, not the paper's three inputs: the weighted `(EMCTE2)` of RBM2D is the generator identity of a centred Gaussian OU path (`OUGenerator.lean` header), so the band model produces `(417)` from `UNMLOut` through the rows `UNOURow`, `UNEMCTE2Row`, `UNJakUywRow`, `UNClaimRow` (`un_claimAll_of_rows`, compiled), while BA-D1 supplies its own (open issue d.3).
3. The paper lists `MR:decol`, `MR:locSC`, `(Meq:QUE)` as inputs (`1_2:568`); the formal chain also needs the `𝐇_t` claims (QUE and diagonal local law of `𝐇_t`, `t ≤ t* = N^{-1+τ_U}`, "identical to Section 7.2 of [YY_25]"), whose proof is the 25-file GUE-phase random layer and consumes `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` along `z`-sequences (`UNMLOut`), and the weak GUE local law `UNGUELocal`: paper-deltas T2162b.  RBM2D `OURow` does not use `locSC`, `QUE` (b.5).
4. `Thm 2.4` follows from the core at `ρ = ρ_sc(E)`, `E' = E` by the dilation `𝒪 ↦ 𝒪(ρ_sc(E)⁻¹ ·)` (`unBUniv_diff_eq`); the composition `un_bUniv_of_rows` fixes the quantifier order of all pins (constants `d, 𝔠, 𝔡` before `sz`; `κ, ε, τ, D` after; `∃ τ₀` before `𝒪` in `UNGreenCorr`, `∃ τ₁` after `𝒪` in `UNInfty1Row`).  Against `T2001_BUniv` (`bd95cc9:RBM3D/Probe/T2001Endpoints.lean:230`) the order `d, 𝔠, 𝔡, sz, k, κ, E, 𝒪` is the same; differences: fine-lattice carrier `Idx` (`seqXmat`, DECISIONS §12) instead of `Vtx`, the merged `Sizes.Admissible`, `IsHermitian.eigenvalues` instead of `eigs`.
5. `UNGreenCorr` is stated for dilation sequences `r_n ∈ [a,b]` (the block Anderson density `ρ_N(E)` varies with `n`; `r ≡ 1` is RBM2D): paper-delta T2162d.
6. `ℙ(𝓑(y))`: `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}` is a weighted average of block QUE quantities with weights `SBR b a` (sum 1, support `≤ 2d+1` blocks, `unBadY_card_le`); `unBadY_subset` and `unBadY_measure_le` prove `𝓑(y) ⊆ ⋃_b {QUE bad at b}` and `ℙ(𝓑) ≤ (2d+1)·p` for the `d ≥ 3` weights (RBM2D: five equal weights, `JakSpectral.lean:182-196`); the window inclusion is `un_window_sub`; paper-delta T2162a (the paper cites `[DYYY25]` (2.24) for `M_{y,α}`).
7. Step 1 at `d ≥ 3`: the local-law floor is `W^{-d}(lam²+η)^{-1} ≤ W^{-2𝔡}` (`un_Bctl_le`), so the free-convolution step holds for `τ_s ≤ 𝔠𝔡` (`un_step1_floor`; sharp up to `16𝔠𝔡/(3+𝔠)`), RBM2D `τ_s ≤ 𝔠`.  The `L32` arithmetic premises depend only on `N`, `τ` (`un_L32_arith`).
8. The RBM2D pin `locSC` is pointwise in `z` (`Endpoints.lean:99-113`), hence the grid/interpolation half of `Step1RegularityA`; if MA freezes `UNLocAvgBand` in the T2001b form (`∩_z` inside the probability) that half is not needed: UN-10 is then *estimated* at 928 instead of 1505 lines (the grid half is taken as 577 of 927 lines: an estimate, not measured).
9. The free convolution of RBM2D (`FreeConvStability`) is exact for `m = msc`; for a regular density `ν_N` (BA) the stability `ρ_{ν⊞sc_t}(E) = ρ_ν(E) + O(t)` is new mathematics (UN-07, needed only for BA); `UNStep1Good` is stated for abstract `m, ρ`.
10. Extreme-input finding: the abstract `UNStep1Good` is false without the norm bound `(2.3)` of [32] (a deterministic diagonal model with the semicircle quantiles plus one eigenvalue `N^{10}` has the local law and `UNDens` but `|v_i| > N^{CV}`); added `UNNormBound` (hypothesis of `UNStep1Good`, `UNInfty1Row`, `UNCore`; row `UNNormBandRow`, band `CV₀ = 1`); the counterexample is argued, not compiled.
11. Not done here: `UNDens` for every bulk `E` (row `UNDensBandRow`; proved at `E = 0`), any proof of an owed pin, the Axioms registry (UN-01), the BA-side pins (BA-D1).

## (c) Verified Mathlib names (script `names.lean`: `#check`, output shortened)
```
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_sub : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y - z) = x ^ y / x ^ z
Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
Real.add_one_le_exp : ∀ (x : ℝ), x + 1 ≤ Real.exp x
inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀]
Finset.sum_fiberwise : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : DecidableEq κ
Finset.sum_lt_sum : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] [inst_1 : Preorder M]
Finset.abs_sum_le_sum_abs : ∀ {ι : Type u_1} {G : Type u_2} [inst : AddCommGroup G] [inst_1 : LinearOrder G]
Finset.card_le_card_of_injOn : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β} (f : α → β),
MeasureTheory.measure_biUnion_finset_le : ∀ {α : Type u_1} {ι : Type u_2} {F : Type u_3}
ContDiffBump.one_of_mem_closedBall : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
ContDiffBump.zero_of_le_dist : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
Complex.conj_mul' : ∀ (z : ℂ), (starRingEnd ℂ) z * z = ↑‖z‖ ^ 2
Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
Complex.abs_im_le_norm : ∀ (z : ℂ), |z.im| ≤ ‖z‖
Complex.re_le_norm : ∀ (z : ℂ), z.re ≤ ‖z‖
Complex.abs_re_le_norm : ∀ (z : ℂ), |z.re| ≤ ‖z‖
Homeomorph.smulOfNeZero : {α : Type u_1} →
HasCompactSupport.comp_isClosedEmbedding : ∀ {α : Type u_1} {α' : Type u_2} {β : Type u_3} [inst : TopologicalSpace α]
contDiff_const_smul : ∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {F : Type u_1}
MeasureTheory.Measure.infinitePi : {ι : Type u_1} →
ProbabilityTheory.gaussianReal : ℝ → NNReal → MeasureTheory.Measure ℝ
MeasureTheory.prob_le_one : ∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}
pi_norm_const : ∀ {ι : Type u_1} {E : Type u_2} [inst : Fintype ι] [inst_1 : SeminormedAddGroup E] [Nonempty ι]
mul_le_one₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [MulPosMono M₀],
```
Verified absent or deprecated (same run): `Real.abs_sqrt_sub_sqrt_le` and `Nat.pos_pow_of_pos` do not exist (replaced by a direct proof, `pow_pos`); `mul_le_one₀` is deprecated (replaced by `mul_le_mul` + `one_mul`); `push_neg` is replaced by `push Not`.

## (d) Open issues and paper-delta candidates
1. **Count above 50** (top line): by DECISIONS §9 O2 the dispatcher asks Jun before any UN proof ticket starts.  The 28 GUE-phase tickets (UN-25 .. UN-52) are about 53% of the estimated lines; they re-prove for `d ≥ 3` the random layer that the paper omits ("details identical to Section 7.2 of [YY_25]").
2. Interfaces to freeze: MA must freeze `UNLocAvgBand` and `UNQueBand` in the form of `T2001_locSC`, `T2001_QUE`; ST-6/MA `UNMLOut` (b.5); BA-D1 supplies the five items of the last row of b.5.
3. BA: the OU generator of `(EMCTE2)` has a first-order drift term for a model with mean `λΨ` (to be checked by BA-D1, not verified here); until then `UNClaimAll` is an input of the core for BA.  The bulk condition of BA is `UNDens` (abstract), the free-convolution step needs UN-07.
4. Registry (DECISIONS §16, §20) for UN-01, from the docstrings: borrowed `UNL32`; structural `UNDens`, `IsRegular32`, `IsFreeConv32`, `InWindow`, `queBadMat`, `UNBadY`; owed all other `UN*` pins and rows (`UNBUniv`, `UNGUELocal`, `UNTrLocal`, `UNStep1Good`, `UNClaim417`, `UNApriori`, `UNGreenCorr`, `UNOUQUE`, `UNOUDiag`, `UNEMCTE2`, `UNJak`, `UNUyw`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, the six rows).
5. Paper-delta candidates: **T2162a** (reading: `M_{y,α}` for `d ≥ 3` with the weights of `S^{(B)}`, union over `2d+1` blocks); **T2162b** (the proof of Thm 2.4 needs, beyond `decol`, `locSC`, `(Meq:QUE)`, the `𝐇_t` claims, the ML outputs `UNMLOut` and the weak GUE local law `UNGUELocal`, none stated in the paper; `UNGUELocal` = RBM2D paper-delta #95/#139); **T2162c** (`(Meq:QUE)` window `lam` or `lam ∧ 1`, footnote `1_2:372`: only `W^{-ε₀}(lam∧1)W^{d/2} ≥ W^{2𝔡/3}` is used); **T2162d** (design: `UNGreenCorr` for dilation sequences); **T2162e** (range of `τ_U`: `τ_s ≤ 𝔠𝔡` in Step 1, `τ_U ≤ c'/(2(C_n+1))`, `c' = 𝔠𝔡/30`, with the RBM2D constants `C = 3n_f+16`, `C_n = 1` to be redone); **T2162f** (the BA form of DECISIONS §11 is `UNUnivDilAt` with `ρ_n = π⁻¹ Im m_n(E+i0)`); **T2162g** (the ticket text `L ∈ {W^{1/𝔠-1}}` is the `d = 1` form: `L ≤ W^{1/(d𝔠)-1}`, `un_dc_lt_one`; no paper statement affected).
