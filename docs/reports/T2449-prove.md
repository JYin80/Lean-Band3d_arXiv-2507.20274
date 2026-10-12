Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 11:37 UTC 2026 (date -u 11:37:08)
Scripts (Python, scratch only): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2449` (`pre.py`, `bridge.py`, `t6.py`, `t2.py`). `m(z,g)` solves `(self_m)` `m = L^{-d} tr(gΨ-z-m)^{-1}` (`BASelf`, `MFixedPoint.lean:193`) on `d=3`, `L=4`, `Ψ` spectrum `2Σcos(2πk_i/L)`; `ρ=Im m/π` (`BArho`, `:429`/`BAbulk`); `fT=BAt0=Im m/(Im m+Im z)`, `fE=BAflowE` (`MFixedPoint.lean:279-280`).
### (i) Exponent table
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| `(𝔠,𝔡)` at `clsSz 4 (3/10)` (`UNPins.lean:776`: `W_n=(2(n+1))^5`, `g≡3/10`, `N=(4W)^3`) | `(1/6, 1/10)` | `W≥N^𝔠`, `W^{-3/2+𝔡}≤g≤1/𝔡` (`Sizes.lean:164-169`) | `ln W/ln N ≥ 0.2381` (n=0) vs `1/6`: 0.0714; `W^{-1.4}=0.0078 ≤ 0.3 ≤ 10` (B below) |
| `ε₀, c` (QUE) | `1/30, 1/60` | `0<ε₀<𝔡/2=1/20`, `0<c<ε₀`, `c<𝔡/5=1/50` (`Endpoints.lean:184`) | `1/20-1/30=1/60`; `1/50-1/60=1/300` |
| `τ` (QUE), exponent of `W` | `1/300`; `-min(2ε₀,2𝔡/5)+2c+τ = -1/300` | `<0` iff `τ < min(2ε₀-2c, 2𝔡/5-2c)=1/150` (`queBound`, `Pins.lean:384`) | `1/300`. The merged instance `Endpoints.lean:541` (comment of the instance data) uses `τ=1/10`: exponent `+0.0933`, bound `W^{0.0933}=1.38>1` (B below), i.e. vacuous: do not copy |
| `τ` (locSC, QDiff, decol), `D` | `1/10`; `D=2` (decol: `D=1`) | arbitrary `>0` (`Endpoints.lean:165-205`); `W^τ ≥ N^{𝔠τ}=N^{1/60}` converts the band `W^τ` form to a `Prec` (scale `N`) form (`StochDomAt.lean:118-121`) | none needed |
| `ε` (domain), `η` | `1/20`; `η=N^{-4/5}` | `N^{-1+ε}=N^{-0.95} ≤ η ≤ 1` | `N^{-0.95}` vs `N^{-0.8}`: factor `N^{0.15}` |
| `𝓑_{η,0}` at `η=N^{-4/5}` (`Endpoints.lean:58`) | `5.47e-2` (n=0), `4.09e-5` (n=10) | `<1`, so `𝓑^{1/5}𝓑_{η,K}` and `𝓑²` are nontrivial | `1/5`, `2` powers as `(eq:diffu1)`-`(Meq:QdS2)` (`Endpoints.lean:94-103`) |
| `(g²W^d)^{-1/5}` | `0.2023` (n=0) | `≤ W^{-2𝔡/5}` from `(eq:WO)` (`lam_sq_mul_pow_ge`, `Sizes.lean:193`) | `0.2023` vs `0.8706` |
| `(Meq:QdS1/2)` bound `W^τ𝓑²((g²W^d)^{-1/5}+𝓑)` | `1.09e-3` (n=0) | `<1` (nonvacuous) | `1e-3` |
| decol `N^{-1+τ}` | `2.0e-6` (n=0) | `τ<1` | — |
| `τ_U` (OU time `N^{-1+τ_U}`) | `1/720` | `0<τ_U ≤ ouTauMax(𝔠,𝔡)=min(𝔠/12,𝔠𝔡/12,1/100)=1/720` (`ZeroModeProfile.lean:78`) | 0 (forced by `𝔠𝔡/12`); needed so `L^d(1-t₁) ≲ N^{2τ_U}W^{-d}/c ≤ λ²` under `λ²≥W^{-d+2𝔡}` |
| `τ_D` (T2 loss) | `1/1440` | derived: `(fT-t₁)/η_{t₀} ≈ N^{-τ_U}`, `(Nη_{t₀})^{-1}=N^{-2τ_U}` so `τ_D ≤ τ_U` | ratio `0.980` vs `0.990` at n=0 (D below): small but strict |
| `c` (T1 conj. 5) | `1-fT ≤ Im z/c` holds with `c=Im m(z)` lower bound | `Im m(E+iη)/Im m(E+i0) ≥ 0.6628` on grid (C below, `g=0.3` only); `BAdom` needs `Im m(z) ≥ κ` while `BAbulk κ` gives `Im m(E) ≥ πκ` | needs ratio `≥ 1/π=0.318`: factor 2.08 (grid evidence, not a proof) |
| `fT ≥ 1/16` (T1 conj. 2) | grid min `0.2029` | `Im m(z) ≥ Im z/15` | factor 3.2 (grid) |
| T6 (`RandomLayerB_Bulk`) | **fails** | bulk set nonempty at every `n` or at no `n`, for **every** `Sizes d` (`RandomLayerB.lean:117`) | see E below |
| T1 conj. 1 and 3 | **fail** | `|fE|≤2-κ`; `etaT(fE,fT)=√fT·Im z` | see A below |
### (ii) One concrete instance and the E5 computations
`d=3`, `sz=clsSz 4 (3/10)`, `(𝔠,𝔡)=(1/6,1/10)`, `κ=1/10` (`ρ(0)=0.2636`, `ρ(1/2)=0.2565`), `ε=1/20`, `z=1/2+iN^{-4/5}`, QUE `(ε₀,c,τ)=(1/30,1/60,1/300)`, BUniv `k=1`, `E=E'=0`, `τ_U=1/720`, `τ_D=1/1440`. Command: `cd $S && python3 pre.py` (verbatim output; sections A, B, C):
```
== A. T1 at UNKind.ba (d=3,L=4,g=3/10): fE=BAflowE, fT=BAt0, m=BAm(.,g)
z=0.5j bulk rho(Re z)=0.2636>=kappa=0.25: True | selfres=5.6e-16 t0=0.5727 fE=0.0000
   C1 |fE|<=2-kappa=1.7500: True | C2 1/16<=fT<1: True | C3 etaT(fE,fT)=0.42726 vs sqrt(fT)Im z=0.37840: equal? False
   C4 1-fT=0.42726<=Imz/kappa=2.00000: True | BA identity (1-t0)Im m(fE,g0)=0.37840 (err 1.7e-09); Im m(fE,g0)=0.8856 vs Im m(z)/sqrt(t0)=0.8856
z=(2.5+0.2j) bulk rho(Re z)=0.0527>=kappa=0.05: True | selfres=1.0e-15 t0=0.4728 fE=2.1430
   C1 |fE|<=2-kappa=1.9500: False | C2 1/16<=fT<1: True | C3 etaT(fE,fT)=0.00000 vs sqrt(fT)Im z=0.13752: equal? False
   C4 1-fT=0.52717<=Imz/kappa=4.00000: True | BA identity (1-t0)Im m(fE,g0)=0.13752 (err 8.0e-10); Im m(fE,g0)=0.2609 vs Im m(z)/sqrt(t0)=0.2609
z=(0.5+0.0011j) bulk rho(Re z)=0.2565>=kappa=0.1: True | selfres=8.3e-17 t0=0.9986 fE=0.4999
   C1 |fE|<=2-kappa=1.9000: True | C2 1/16<=fT<1: True | C3 etaT(fE,fT)=0.00132 vs sqrt(fT)Im z=0.00110: equal? False
   C4 1-fT=0.00136<=Imz/kappa=0.01100: True | BA identity (1-t0)Im m(fE,g0)=0.00110 (err 4.7e-12); Im m(fE,g0)=0.8059 vs Im m(z)/sqrt(t0)=0.8059
-- control g=0 (band twin, semicircle exact):
   etaT=0.390388 sqrt(t0)Imz=0.390388
-- etaT mismatch vs g at z=0.5i:
   g=0.01: etaT-sqrt(t0)Imz = +7.136e-05
   g=0.1: etaT-sqrt(t0)Imz = +6.836e-03
   g=0.3: etaT-sqrt(t0)Imz = +4.886e-02
== B. class sequence clsSz 4 (W_n=(2(n+1))^5, g=3/10), (c,dd)=(1/6,1/10)
Admissible checks n=0..2999: True; ln W/ln N min=0.2381 (->1/3), slack over c=1/6: 0.0714; n=0: W=32, N=2097152, W^(-3/2+dd)=0.00781 <= g=0.3 <= 1/dd=10
QUE exponent -min(2e0,2dd/5)+2c+tau at tau=0.10000: +0.09333  (e0=1/30<dd/2=0.05, c=1/60<e0, c<dd/5=0.020); W^exp at n=0: 1.38191
QUE exponent -min(2e0,2dd/5)+2c+tau at tau=0.00333: -0.00333  (e0=1/30<dd/2=0.05, c=1/60<e0, c<dd/5=0.020); W^exp at n=0: 0.98851
tau window: 0<tau<min(2e0-2c,2dd/5-2c)= 0.006666666666666668  -> slack at tau=1/300: 0.0033333333333333344
n=0: N=2.097e+06 eta=N^-4/5=8.764e-06 B0=5.4748e-02 (g^2W^d)^(-1/5)=0.2023 (<=W^(-2dd/5)=0.8706) QdS bound W^tau B0^2(..)=1.090e-03; N^(-1+eps)<=eta: ok; decol N^(-1+tau)=2.044e-06
n=10: N=8.760e+21 eta=N^-4/5=2.792e-18 B0=4.0879e-05 (g^2W^d)^(-1/5)=0.0002 (<=W^(-2dd/5)=0.5389) QdS bound W^tau B0^2(..)=1.512e-12; N^(-1+eps)<=eta: ok; decol N^(-1+tau)=1.785e-20
n=1000: N=2.129e+51 eta=N^-4/5=8.659e-42 B0=5.4247e-11 (g^2W^d)^(-1/5)=0.0000 (<=W^(-2dd/5)=0.2186) QdS bound W^tau B0^2(..)=3.370e-29; N^(-1+eps)<=eta: ok; decol N^(-1+tau)=6.378e-47
kappa=1/10 bulk at Re z=1/2 and E=0: True rho(0.5)=0.2565 rho(0)=0.2636
== C. BUniv k=1 normalisation (external UNL32 limit check), d=3,L=4,W=2,N=512, O(a)=exp(-a^2/2), int O=sqrt(2pi)=2.5066
rho_N(0)=0.2636; mean BAkPoint(k=1)=2.5562; mean GUE=2.5366; difference=+0.0195 (std err ~0.054)
```
Bridge ρ-bulk to `Im m(z)`, flow constants (`cd $S && python3 bridge.py`), then the T6 test (`python3 t6.py`):
```
g=0.3: min over grid {E: rho(E)>=0.05, eta in (0,1]} of Im m(E+i eta)/Im m(E+i0) = 0.6628 at (E,eta,rho)=(np.float64(-1.0), 1.0, np.float64(0.2361))
min fT=BAt0 over the same grid: 0.2029  (>=1/16=0.0625 required by T1)
T6 test, kappa=0.30; RandomLayerB_Bulk quantifies over every Sizes d (3<=L n, W n>0), no admissibility
  (L,g)=(4,0.3): sup_E rho on grid step 0.01 = 0.26361 at E=-0.0  -> bulk set for kappa=0.30 nonempty: False
  (L,g)=(8,0.001): sup_E rho on grid step 0.01 = 0.31831 at E=-0.0  -> bulk set for kappa=0.30 nonempty: True
  (L,g)=(12,0.001): sup_E rho on grid step 0.01 = 0.31831 at E=-0.0  -> bulk set for kappa=0.30 nonempty: True
  1/pi = 0.31831
```
T2/T3 side conditions at the instance (`python3 t2.py`, `t=N^{-1+τ_U}`, `ζ=1-e^{-t}`, `t₁=(1-ζ)fT`, `z=iη_LL`, `η_LL=N^{-1+2τ_U}`, `ouEtaLL` `ZeroModeProfile.lean:81`):
```
n=0 N=2.097e+06 eta_LL=4.965e-07 fT=0.99999940: L^d(1-t1)=6.951e-05 <= lam^2=0.09 and <=1: True | (fT-t1)/eta_t0=9.800e-01 <= N^-tD=9.899e-01: True | (N eta_t0)^-1=9.604e-01 <= N^-tD: True
n=3 N=2.252e+15 eta_LL=4.899e-16 fT=1.00000000: L^d(1-t1)=6.395e-14 <= lam^2=0.09 and <=1: True | (fT-t1)/eta_t0=9.065e-01 <= N^-tD=9.757e-01: True | (N eta_t0)^-1=9.065e-01 <= N^-tD: True
```
External hypothesis `UNL32` (LSY Thm 2.2, borrowed) and the normalisation of `(eq:universality)` (lesson 14): section C above, `k=1`, `N=512`, 60 samples: `BAkPoint` mean `2.5562`, GUE mean `2.5366`, both `≈ ∫O = 2.5066` within the standard error `0.054`; this checks the `O(ρ_N α)` dilation of `BAunivConcl` at `k=1`.
### Findings and verdicts
1. **MN0 / E5 (a): T1 `RandomLayerB_Flow` is false at `UNKind.ba` with `fE=BAflowE`, `fT=BAt0`, `m=BAm(·,g)`.** Conj. 1: `z=2.5+0.2i`, `κ=0.05` (`ρ(2.5)=0.0527`): `fE=2.1430 > 1.95`. Conj. 3: `z=0.5i`, `κ=0.25`: `etaT=0.42726 ≠ 0.37840=√fT Im z`; mismatch `+7.1e-5, +6.8e-3, +4.9e-2` at `g=0.01, 0.1, 0.3`, zero at `g=0` (band twin). Cause: `etaT` uses the semicircle `mE` (`Semicircle.lean:38`, `GLoop.lean:75`), while `zztE_BA` gives `(1-t₀)Im m(E,g₀)=√t₀ Im z` with the BA `m` (printed: err `≤1.7e-9`, and `Im m(fE,g₀)=Im m(z)/√t₀`). Conj. 2 and 5 hold in the tested cases.
2. **E5 also fails at T6** (`hT6` of `g1Rowk_of_inputs`): `Sizes` with `(L,g)=(4,0.3)` at `n=0` and `(8,0.001)` for `n≥1`, `κ=0.30`: `sup ρ=0.2636<0.30` at `n=0`, `0.3183≥0.30` at `n≥1` (T6 output; grid step 0.01), so the bulk is empty at one `n` and nonempty at another. `RandomLayerB_pad` (`:186`) needs T6; a repair is a subsequence/tail form of the padding (only `∀ᶠ` conclusions).
3. **(b) T2, T3, T4, T5.** T2 contains `etaT` and `gueScale` (`Grid.lean:84`, `=N·etaT`) in `fT-t₁ ≤ N^{-τD}etaT(fE,fT)` and `(gueScale)^{-1}≤N^{-τD}` and `|fE|≤2-κ`: same defect as T1, repaired by the same `η`-parameter. T4 carries `|fE|≤2-κ` as a hypothesis: the BA producer must supply the BA bulk form instead. T3 has no semicircle quantity in its statement (`ouEtaLL`, `ouZeta`, `K.bulk`): not refuted. T5 takes `fT`, `Fl`, `MO` as parameters: `Fl=BAFlow`, `fT=BAt0` is the shape fed by `BAMLOutTL`; the bridge needs the ratio row above. KF in T2 is a parameter, so the band `kTwoGUE`/`mSigma` need not be touched; only the producer (BA twin of `gueK_exists`) has to use `m(E,g₀)`.
4. **(c) Repair sketch (mathematics).** `T1'`: replace `|fE|≤2-κ` by `κ ≤ Im m(fE,√fT g)` (equal to `Im m(z)/√fT`) and `etaT(fE,fT)` by `η_{t₀}(z):=(1-fT)Im m(fE,√fT g)`; T2 gets the same `η` in place of `etaT`/`gueScale`; T6 gets the subsequence padding. All of this lives inside `RandomLayerB`-generic definitions (C5's file); the U statement `UNG1Rowk` (`OUInterfaceK.lean:101`) has no `etaT`, `fE`, `fT`, so by inspection no U statement changes. V (`BAMLOutTL`) enters only through T5. To be confirmed in the probe.
5. **Instance (ii):** every deterministic hypothesis of locSC/QDiff/decol/QUE/BUniv holds at the data above (Admissible checked numerically for `n=0..2999`); the `τ=1/300` row replaces the vacuous `τ=1/10` for QUE.
**Verdicts.** MN0-E5 (design question): PASS as answerable, answer **fails** (T1 conj. 1, 3; T6), repair preview changes no U/V statement. Law-corrected end pins `BAEnd_locSCL/QDiffL/decolL`, `BAEnd_QUEL`, `BAEnd_BUnivL`, `BAThm27L`: PASS (exponents close with the slacks above; instance nonvacuous with `τ=1/300`). MN2 interfaces (`BAMLOutTL`, bridge): PASS for the numbers, the ratio constant is grid evidence only. MN3/MN4: no exponents beyond the rows above; PASS.
## (a′) Preflight corrections — Mon Oct 12 12:55:09 UTC 2026 (`date -u`)
The verdict of (a) stands (E5 fails); three corrections of detail. Conjunct numbers follow the Lean statement (`RandomLayerB.lean:106-107`: 1 `|fE| ≤ 2-κ`, 2 `1/16 ≤ fT`, 3 `fT < 1`, 4 `etaT = √fT Im z`, 5 `1-fT ≤ Im z/c`); (a)'s "conj. 3" is conjunct 4.
1. (a) finding 1 says conjuncts 2 and 5 hold in the tested cases; conjunct 2 fails at admissible data (g = 10, `z = 60+i`, `κ = 0.02`: `fT = 0.0156 < 1/16`, B3 E3), (a)'s grid had `g = 0.3` only. Conjuncts 1 and 4 fail as in (a).
2. (a)'s row "c (T1 conj. 5) ... grid evidence, factor 2.08" is superseded by a theorem: `ba_dom_of_bulk` (probe 98, from the merged `BAm_im_lower_window`, `BA/MReg.lean:227`) gives `Im m(E+iη, g) ≥ (πκ)^5/2048` for every `L`, `g`; the bulk-to-domain bridge needs no ratio constant.
3. (a) finding 2 (T6) used `(L,g) = (4,0.3)` at n = 0 and `(8,0.001)` for n ≥ 1; the sharper fact is an admissible oscillating `λ_n` (B4): the bulk is empty for infinitely many `n`, so an "eventually" repair of T6 is not enough (padding by subsequence, probe 79).

## (b) Script output
Commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2449` (branch `t/T2449`) unless stated; `S` is the scratchpad subdirectory `T2449/` (scripts and logs, not committed); `P` is the probe path; a command line starting with `$` is the command as run, the lines below it are its verbatim output; a block headed by a script name is that script's output file. Narrative at the end of (b).
### B0 provenance, build, hygiene, axioms, name clash
```
$ cd RBM3D-wt/T2449; P=RBM3D/Probe/T2449Pins.lean; S=<scratchpad>/T2449
$ date -u
Mon Oct 12 13:12:40 UTC 2026
$ git log --oneline -4 | cut -c1-100
921369b T2449: repair (audit round 1): RBG_Que (Que') pinned with a d = 3 instance at S0; Prod' inst
5c0c593 T2449: probe 395 lines: docstring names Flow'/Dom'/Prod'/MLout (no code change)
917be55 T2449: probe 395 lines (clean build): E5 inputs T1'/T1''/T2' + pad_subseq, BA end pins, M1-M
c8dc676 T2449: probe 397 lines: BA end pins (law-corrected), E5 repaired inputs T1'/T1''/T2' with T1
$ git diff --stat main...t/T2449
 RBM3D/Probe/T2449Pins.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 397 insertions(+)
$ lake build RBM3D.Probe.T2449Pins > $S/build_r.out 2>&1; echo "exit $?"; tail -1 $S/build_r.out; grep -c "T2449Pins.lean:" $S/build_r.out
exit 0
Build completed successfully (4174 jobs).
0
$ lake env lean $P; echo "exit $?"
exit 0
$ grep -cwE "sorry|admit|axiom|native_decide|inductive" $P; wc -l < $P
0
     397
$ (cat $P; echo; grep -E "^(def|theorem) " $P | sed -E 's/^(def|theorem) ([^ ]+).*/#print axioms RBM.BA.\2/') > $S/ax_r.lean; lake env lean $S/ax_r.lean 2>&1 | sed -E "s/'RBM.BA.([^']*)' depends on axioms: /\1 /" > $S/ax_r.out; cut -d" " -f2- $S/ax_r.out | sort | uniq -c; grep "^RBG_Que " $S/ax_r.out
  37 [propext, Classical.choice, Quot.sound]
RBG_Que [propext, Classical.choice, Quot.sound]
$ names=$(grep -E "^(def|theorem) " $P | sed -E "s/^(def|theorem) ([^ ]+).*/\2/" | tr "\n" "|" | sed "s/|$//"); grep -rnwE "($names)" RBM3D --include="*.lean" | grep -v "RBM3D/Probe/T2449Pins.lean"; echo "exit $?"
exit 1
```
### B1 target statements extracted from the probe (`stmts_r.sh` = `stmts.sh` + `show RBG_Que 1`; the whole statement is T4 plus the diff; number = probe line) and the token diff T4 → `Que′`
```
35: def RBG_Flow (K : UNKind d) (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fT : Sizes d → ℕ → ℂ → ℝ) : Prop :=
36:   ∀ κ : ℝ, 0 < κ → ∃ κ' c cT : ℝ, 0 < κ' ∧ 0 < c ∧ 0 < cT ∧ ∀ (sz : Sizes d) (n : ℕ) (z : ℂ),
37:     K.bulk sz κ z.re n → 0 < z.im → z.im ≤ 1 →
38:       Ed κ' sz n z ∧ cT ≤ fT sz n z ∧ fT sz n z < 1 ∧ 1 - fT sz n z ≤ z.im / c
40: def RBG_Dom (K : UNKind d) (Fl : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) : Prop :=
41:   ∀ κ : ℝ, 0 < κ → ∃ κ' : ℝ, 0 < κ' ∧ ∀ (𝔠 𝔡 ε : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < ε → ∀ E η : ℕ → ℝ,
42:     (∀ n, K.bulk sz κ (E n) n) → (∀ n, Nsz sz n ^ (-1 + ε) ≤ η n) → (∀ n, η n ≤ 1) →
43:       Fl sz κ' ε 𝔠 𝔡 (fun n => (E n : ℂ) + (η n : ℂ) * Complex.I)
45: def RBG_Prod (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : Sizes d → ℕ → ℂ → ℝ)
58: def RBG_Que (K : UNKind d) (P : UNOUProfile K) (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : Sizes d → ℕ → ℂ → ℝ)
192: def BAEnd_locSCL (d : ℕ) : Prop :=
193:   3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
200: def BAEnd_QDiffL (d : ℕ) : Prop :=
213: def BAEnd_decolL (d : ℕ) : Prop :=
214:   3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
217: def BAThm27L (d : ℕ) : Prop :=
218:   BAEnd_decolL d ∧ BAEnd_locSCL d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ BAEnd_QDiffL d
249: def BAMAFixed (d : ℕ) : Prop := UNMLOutBA d → BAlocSCFixed d ∧ BAQDiffFixed d
251: def BAMANetLoc (d : ℕ) : Prop := BAlocSCFixed d → BAEnd_locSCL d
253: def BAMANetQD (d : ℕ) : Prop := BAQDiffFixed d → BAEnd_QDiffL d
255: def BAMADecol (d : ℕ) : Prop := BAEnd_locSCL d → BAEnd_decolL d
257: def BAMAQUE (d : ℕ) : Prop := BAEnd_QDiffL d → BAEnd_QUEL d
259: theorem unMLOutBA_of_BAMLOutTL (d : ℕ) (h : BAMLOutTL d) : UNMLOutBA d := by
264: theorem unMLOutBA_of_V (d : ℕ) (hmain : BAMainIndTL d STAny)
116: theorem ba_flowG (d : ℕ) : RBG_Flow (UNKind.ba d) (BAEd d) (BAfT d) := by
131: theorem ba_domG (d : ℕ) : RBG_Dom (UNKind.ba d) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) := by
144: theorem ba_mlout (d : ℕ) (hd : 3 ≤ d) (h : UNMLOutBA d) :
145:     RandomLayerB_MLout (BAfT d) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (BAMO d) := by
$ python3 -I $S/quediff.py <(sed -n 166,181p RBM3D/Universality/GUEPhase/RandomLayerB.lean) <(sed -n 58,69p $P)
replace: [RandomLayerB_Que] -> [RBG_Que]
insert: [] -> [(Ed : ℝ → Sizes d → ℕ → ℂ → Prop)]
delete: [∀ _ :] -> []
replace: [d,] -> [d →]
insert: [] -> [κ']
insert: [] -> [→ 0 < κ']
replace: [|fE] -> [Ed κ']
replace: [n)| ≤ 2 - κ] -> [n)]
```
### B2 compiled nonempty instances (the nine `example`s; all compile, B0; descriptions in the design §6)
```
$ grep -n "^example" RBM3D/Probe/T2449Pins.lean | cut -d: -f1 | tr "\n" " "
277 286 295 301 320 330 378 391 393 
```
### B3 E5 numerics at d = 3, L = 4 (`e5tab.py`; exact solver: degree-8 polynomial in m, `ba.py`)
```
[E1] (d,L,g)=(3,4,0.3) z=(2.5+0.2j) kappa=0.05: rho(Re z)=0.0527 bulk=True  Im z<=1=True
   T1: C1 |fE|=2.1430<=2-kappa=1.9500: False | C2 fT=0.4728>=1/16: True | C4 etaT=0.00000 vs sqrt(fT)Im z=0.13752: False | C5 1-fT=0.5272<=Imz/c
   BA identity (1-fT) Im m(fE,g0)=0.13752 (= sqrt(fT) Im z up to 4.2e-14); Im m(fE,g0)=0.26087, Im m(z)/sqrt(fT)=0.26087
   T1': kappa'=(pi kappa)^5/2048=4.669e-08<=Im m(z)=1.7938e-01: True | Ed: kappa'<=Im m(fE,g0): True | cT=kappa'/(kappa'+1)=4.669e-08<=fT: True | 1-fT<=Imz/kappa': True
[E2] (d,L,g)=(3,4,0.3) z=0.5j kappa=0.25: rho(Re z)=0.2636 bulk=True  Im z<=1=True
   T1: C1 |fE|=0.0000<=2-kappa=1.7500: True | C2 fT=0.5727>=1/16: True | C4 etaT=0.42726 vs sqrt(fT)Im z=0.37840: False | C5 1-fT=0.4273<=Imz/c
   BA identity (1-fT) Im m(fE,g0)=0.37840 (= sqrt(fT) Im z up to 2.8e-16); Im m(fE,g0)=0.88564, Im m(z)/sqrt(fT)=0.88564
   T1': kappa'=(pi kappa)^5/2048=1.459e-04<=Im m(z)=6.7025e-01: True | Ed: kappa'<=Im m(fE,g0): True | cT=kappa'/(kappa'+1)=1.459e-04<=fT: True | 1-fT<=Imz/kappa': True
rho(g=10, E=60)=0.03967
[E3] (d,L,g)=(3,4,10.0) z=(60+1j) kappa=0.02: rho(Re z)=0.0397 bulk=True  Im z<=1=True
   T1: C1 |fE|=7.6588<=2-kappa=1.9800: False | C2 fT=0.0156>=1/16: False | C4 etaT=0.00000 vs sqrt(fT)Im z=0.12510: False | C5 1-fT=0.9844<=Imz/c
   BA identity (1-fT) Im m(fE,g0)=0.12510 (= sqrt(fT) Im z up to 1.1e-16); Im m(fE,g0)=0.12708, Im m(z)/sqrt(fT)=0.12708
   T1': kappa'=(pi kappa)^5/2048=4.782e-10<=Im m(z)=1.5898e-02: True | Ed: kappa'<=Im m(fE,g0): True | cT=kappa'/(kappa'+1)=4.782e-10<=fT: True | 1-fT<=Imz/kappa': True
-- control g=0 (band twin): etaT - sqrt(fT) Im z at z=0.5i: +4.44e-16
-- etaT - sqrt(fT) Im z at z=0.5i for g=0.01,0.1,0.3: g=0.01: +7.136e-05; g=0.1: +6.836e-03; g=0.3: +4.886e-02; 
Dom: g=10, kappa=0.02: min over {E in [50,62], rho(E)>=kappa} x eta in {.01,.1,.5,1} of Im m(E+i eta) = 0.01545 at (E,eta,rho)=(60.20,1.0,0.0276); BAdom(kappa) needs Im m >= kappa: False
grid check of kappa'<=Im m(z), cT<=fT, 1-fT<=Im z/kappa' at g in (0.3,3,10), E step .25 with rho>=.01, eta in 5 values: 485 points, violations 0, min Im m/kappa' = 9.0
```
### B4 Bulk at an admissible oscillating `λ_n` (`t6b.py`) and the QUE exponent of the instances (`que.py`)
```
T6 at UNKind.ba, kappa=0.3, d=3, L=4: B_kappa(n) = {E: rho_n(E) >= kappa}; 1/pi = 0.31831
  g=0.3: sup_E rho (E grid step 0.01 on [-3.6,3.6]) = 0.26361 at E=-0.0: B_kappa nonempty: False
  g=0.001: sup_E rho (E grid step 0.01 on [-3.6,3.6]) = 0.31831 at E=-0.0: B_kappa nonempty: True
  oscillating lam_n=(0.3,0.001,0.3,...): Admissible(1/6,1/10) checks n=0..2999 (WO from n>=1): True; min ln W/ln N = 0.2381
  => B_kappa(n) is empty for even n and nonempty for odd n: (forall n, exists e, bulk) fails and (forall n e, not bulk) fails: True
QUE exponent -min(2e0,2dd/5)+2c+tau at (e0,c,dd)=(1/30,1/60,1/10); the bound is W^exponent, nonvacuous iff exponent < 0:
  Endpoints.lean Inst / BandTerminal instance data (tau=1/10)    tau=1/10   exponent=7/75    = +0.09333  nonvacuous: False
  BA/UNPins.lean inst_BAEnd_QUEL (tau=1/100)                     tau=1/100  exponent=1/300   = +0.00333  nonvacuous: False
  probe T2449Pins (tau=1/300)                                    tau=1/300  exponent=-1/300  = -0.00333  nonvacuous: True
```
### B5 band MA text: carrier-free vs band-token blocks (`carrier2.py`) and carrier-token lines of the N3 producers (`n3.py`)
```
file                        lines decl blocks carrier-free band-token instances  other(imports,docs)
Endpoints.lean                800          78          279        381       140                    0
   free public 270, free private 9
Main/ZTransfer.lean           578          31          127        345       106                    0
   free public 93, free private 34
Main/FixedZ.lean              852          27          270        518        64                    0
   free public 270, free private 0
Main/ZNet.lean               1189          69          420        610       159                    0
   free public 99, free private 321
Main/QUECore.lean            1236          55          588        522       126                    0
   free public 14, free private 574
Main/QUEFromQDiff.lean        665          23          288        241       136                    0
   free public 121, free private 167
Main/BUniv.lean                53           2            0         53         0                    0
   free public 0, free private 0
Main/BUnivHolds.lean          262          10           33        187        42                    0
   free public 0, free private 33
Main/BandTerminal.lean        160          22           46         70        44                    0
   free public 46, free private 0
TOTAL carrier-free 2051 (public 913 , private 1138 ) band-token 2927 instances 817
item           file lines code lines  carrier-token lines  share
E1 EMCTE2             779        620                   82  0.132
E2 Jak               2097       1756                    6  0.003
E2 Uyw                969        823                    7  0.009
E3 Step1Band         1241       1028                   40  0.039
E3 UnivMain           691        492                   25  0.051
E4 GreenCorr         1005        826                   39  0.047
```
### B6 landed/central ratio of the band twin (`ratio.py`) and the MN4 row table (`rows.py`; excerpt: the lo and hi bottom-up lines omitted)
```
row       T2192 lo/central/hi  landed  landed/central
MA-01     610/   760/   990     799           1.051
MA-02     430/   540/   700     577           1.069
MA-03     660/   830/  1080     851           1.025
MA-04     820/  1030/  1340    1188           1.153
MA-05    1160/  1440/  1880    1899           1.319
MA-06     270/   340/   440     159           0.468
MA-01..05 total: landed 5314, central 4600, ratio 1.155   (MA-06 is split: MA-06a landed 159 of the 340 central; MA-06b not written)
row      lo  central     hi  ratio landed c.  tickets lo/c/hi  role / content
M1      735     1360   2550  1.155      1571     1/2/2       prover-hard: BA/MALocal (+ UNTrLocalBARow, UNTrLocalInitBARow')
M2      490     1000   1950  1.155      1155     1/1/2       prover-hard: BA/MAQDiff
M3      630     1300   2470  1.155      1502     1/2/2       prover-hard: BA/MADecolQUE
N2      200      230    440  1.155       266     1/1/1       prover: BA/UNBUniv (+ UNNormBARow, UNOURowBA assembly)
N3a     400      650   1050  1.500       975     1/1/2       prover-hard: E1+E2: EMCTE2 shift, two-coupling Jak/Uyw (edits Jak.lean, Uyw.lean, EMCTE2 twin)
N3b     350      550    900  1.500       825     1/1/1       prover-hard: E3+E4: UNCoreC'', UNGreenCorrAllC (C-form of GreenCorr, UnivMain, Step1Band)
C3      552     1102   2048  1.155      1273     1/1/2       prover-max: BA/GUEKPrim, GUEEntry
C4      434      868   1612  1.155      1003     1/1/2       prover-max: BA/GUEOneLoop
C5      609     1217   2261  1.155      1406     1/1/2       prover-max: BA/GUEHyp (BA producers of Prod', LL, Que'; Flow', Dom', MLout proved in the probe)
C5g     400      530    760  1.500       795     1/1/1       prover-hard: Universality/GUEPhase/RandomLayerBG (new, generic successor of UN-51)
M/N rows (M1 M2 M3 N2 N3a N3b): central 5090  [lo 2805, hi 9360]  landed-scale 6293  rows 6  flag 1.5x = 9.0
+ C3 C4 C5 C5g:               central 8807  [lo 4800, hi 16041]  landed-scale 10769  rows 10  flag 1.5x = 15.0
prior (T2325 revised, N1 dropped): 7 rows M1 M2 M3 N2 C3 C4 C5, central 6927; before the revision (T2161/T2173 portmaps, with N1): M1+M2+M3+N1+N2 = 5300, C3+C4+C5 = 3187
N1: UNTrLocalBARow (45, 60, 100) -> M1;  UNTrLocalInitBARow' (200, 300, 500) -> M1;  UNNormBARow (50, 70, 110) -> N2   sum (295, 430, 710)
bottom-up M1+M2+M3 (central): alpha*2236 band-token + 0.5*591 instance + 90 probe vocabulary = 1951; x1.155 = 2253
prior M1+M2+M3 (T2325 revised lo/central/hi): (1610, 3300, 6370)
```
### B7 greps (`b7b.sh`)
```
$ grep -rn unMLOutBA_of_pins RBM3D | grep -v Probe/ | cut -d: -f1,2
RBM3D/Induction/MainIndOut.lean:28
RBM3D/Induction/MainIndOut.lean:144
RBM3D/Induction/MainIndOut.lean:203
RBM3D/Induction/MainIndOut.lean:210
$ for f in OUInterfaceK BA/UNPins BA/TwistPins BA/FlowPins Induction/MainIndOut: grep -cwE "etaT|gueScale|fE|fT|Fl|RandomLayerB_Flow|RandomLayerB_Prod|RandomLayerB_Bulk"
0 0 0 0 0 
$ sed -n 561,590p RBM3D/Universality/Jak.lean | grep -n lam      # Jak_fixed_time is private; Uyw_fixed_time (Uyw.lean:497) likewise
1:private theorem Jak_fixed_time {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
7:    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam)
19:      P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤
26:        ‖∑ x, (Gres (Hr ω) u b₁ * Gres (Hr ω) u b₁) x x * scirc d L W lam x y *
$ sed -n 497,540p RBM3D/Universality/Uyw.lean | grep -n lam
1:private theorem Uyw_fixed_time {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
7:    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam)
18:      P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤
26:        ‖∑ x, (Gres (Hr ω) u₁ b₁ * Gres (Hr ω) u₁ b₁) x y * scirc d L W lam x y *
$ awk "NR>=172 && NR<=192 && /^   .RBM/" RBM3D/Test/Axioms.lean | wc -l
20
```
### B8 N1(a) `UNTrLocalBARow` proved from `UNLocAvgBA` in a scratch file (`b8.sh`; merged names only; not committed, the probe is at its line limit)
```
$ cd $S && wc -l trlocal.lean && sed -n 10,39p trlocal.lean | wc -l && sed -n 42,52p trlocal.lean | wc -l
56 trlocal.lean
30
11
$ cd RBM3D-wt/T2449 && lake env lean $S/trlocal.lean 2>&1 | grep -E ": (warning|error):|axioms" | sed "s|$S/||"
trlocal.lean:10:70: warning: Variable name `hδ` is not explicitly referenced.
trlocal.lean:50:2: warning: `push_neg` has been deprecated. Prefer using `push Not` instead.
'T2449Scratch.ba_trLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Narrative** (every number is in B0-B8 or in the files)
1. Delivered: the probe `RBM3D/Probe/T2449Pins.lean` (397 lines, limit 400; 37 public declarations, 9 private, 9 `example`s; commits in B0) and the design report `docs/reports/T2449-design.md` (158 lines, limit 400; untracked in the main worktree, as `T2379-design.md`, `T2360-design.md`). The branch diff is the probe only (B0).
2. B0: `lake build RBM3D.Probe.T2449Pins` exit 0, no warning names the probe; no `sorry`/`admit`/`axiom`/`native_decide`/`inductive`; the 37 public declarations use the three standard axioms; no name clash on `main`.
3. Proved in the probe from merged names: `ba_dom_of_bulk`, `ba_Ed_of_im`, `ba_flowG`, `ba_domG`, `pad_subseq`, `flowG_of_band`, `UNLocAvgBA_of_BAEnd_locSCL`, `unMLOutBA_of_BAMLOutTL`; `ba_mlout` and `unMLOutBA_of_V` take V's outputs as hypotheses. Pins stated as `Prop`: `RBG_Flow`, `RBG_Dom`, `RBG_Prod`, `RBG_Que`, `BAEnd_locSCL`, `BAEnd_QDiffL`, `BAEnd_decolL`, `BAThm27L`, `BAlocSCFixed`, `BAQDiffFixed`, `BAMAFixed`, `BAMANetLoc`, `BAMANetQD`, `BAMADecol`, `BAMAQUE`, with the vocabulary `BAGz`, `BAMz`, `BAprof`, `BAendDom`, `BAlocBad1z`, `BAlocBad2z`, `BAqdBadz`, `BAdecolBad`.
4. E5 (B3, B4) uses an exact solver (degree-8 polynomial in `m`, `d = 3`, `L = 4`) and reproduces (a)'s values at the shared points (`fE = 2.1430`; the `etaT` mismatches 7.136e-05, 6.836e-03, 4.886e-02). New: conjunct 2 and `Dom` at `g = 10`, Bulk at an admissible oscillating `λ_n`. These are numerics for `L = 4`; the negative statements are not compiled (they need the explicit solution of `(self_m)`).
5. The repaired inputs are proved at `UNKind.ba` (probe 116, 131) from `BAm_im_lower_window` and `BAdom_real`; the `Prod′` instance (probe 330) proves every deterministic premise, scale rows included, and keeps `UNMLOutBA`, `KF`, `PB` as hypotheses; the `Que′` instance (probe 378) proves every deterministic premise and leaves `KF`, `PB`, `BAMO` at each `Kt`.
6. Not done: the kind-compat lemma and the repaired `g1Rowk_of_inputs′` are described (design §1.3), not pinned (400-line limit); E1-E4, N1(b), N1(c) and the M1-M3 steps are designs with estimates (B5, B6), not proofs; N1(a) is proved in a scratch file (B8), which fixes its estimate at ≈ 60 lines (design §5). The E1-E4 estimates rest on token densities and the factor 1.9 measured on the chain by T2379 (not validated on UN files).
7. Ports: none from RBM1D/RBM2D (nothing under `../RBM1D`, `../RBM2D` read or run). Re-typed from the unmerged T2161 probe (`git show t/T2161:RBM3D/Probe/T2161Pins.lean`, commit `82e72b3`): `BAGz` (`:1475`), `BAMz` (`:1479`), `BAprof` (`:1494`), the shapes of the end pins (`:1543-1659`), with law, form and vocabulary changed.
8. Stop rules: probe 397 ≤ 400, design 158 ≤ 400; E5 fails but changes no U or V statement and no merged pin (design §1.5, B7); every endpoint has a compiled Lean form.

## (c) Verified Mathlib names
All elaborate in the probe (B0): `Filter.not_eventually`, `not_imp`, `Nat.frequently_atTop_iff_infinite`, `Nat.nth_mem_of_infinite`, `Nat.nth_strictMono` (need `import Mathlib.Data.Nat.Nth`, not in the closure of `RandomLayerB`), `Set.ofPred` (this Mathlib's name; `setOf` is deprecated), `Filter.Eventually.exists`, `Filter.Eventually.of_forall`, `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.sqrt_nonneg`, `div_le_div_iff₀`, `div_le_div_of_nonneg_left`, `Complex.re_add_im`, `measure_mono`. Verified absent: `Filter.frequently_iff_not_eventually` (unknown constant); a root `import Mathlib` (no olean in this build).

## (d) Open issues and paper-delta candidates
Open: (1) the decisions of design §7 (C5g, N1 re-homing, writable files of N3a/N3b, V3, opening REQ). (2) `Prod′`, `Que′` are producers owed by BA-C5; the kind-compat lemma by C5g, whose 1a must pin the compat lemma and `g1Rowk_of_inputs′` (`Que′` is pinned: probe 58). (3) The BA `thetaDiff` of M3 has no named producer (design §2). (4) The estimates of E1-E4 and the ratios 1.155 / 1.5 are judgments; the hi bounds cover them. (5) Merged instances with QUE exponent > 0 (B4): `Endpoints.lean:541`, `Main/BandTerminal.lean:110`, `BA/UNPins.lean:1225` (no change made). (6) The window hypothesis of `UNTrLocalBARow` and `UNTrLocalInitBARow'` is pointwise in `x` (`UNPins.lean:172, :184`); the uniformisation lemma costs ≈ 30 lines in M1 (B8); no pin change is proposed.
Paper-delta candidates: `T2449a` BA end pins in the explicit form with law `seqP (sz.withLam 0)`, not T2161's `Prec` with `sz.seqP` (equivalent on admissible sizes by the merged `explicit_of_stochDomAt`; `prec_of_explicit` is band-law only). `T2449b` the UN-51 interface Flow, Dom, Bulk (`T2363b`) is false at BA; the repaired inputs carry a margin `κ' = (πκ)^5/2048`, a constant `cT` for `1/16` and `η_{t₀} := √fT Im z` (lossy constants from `BAm_im_lower_window`); the paper's `|Re z| ≤ 2-κ` in `zztE_BA` is the typo of T2001g. `T2449c` `(G_bound)` uses `distB = W|[x]-[y]|_∞` as the band (`T2192b`).

## Repair (audit round 1) — Mon Oct 12 13:15:52 UTC 2026 (`date -u`)
Repairer `claude-opus-5-5`; commit `921369b` (probe 397 ≤ 400 lines); evidence B0-B2 above. D1: `RBG_Que` (probe 58; token diff against T4 in B1: the margin `κ'`, `0 < κ'`, `Ed κ'` for `|fE| ≤ 2-κ`; `∀ _ : Sizes d,` ↦ `Sizes d →` is the same type) with the `d = 3` instance probe 378 (deterministic premises proved; `KF`, `PB`, `BAMO` remain at each `Kt`; `P` a variable). D2: the `RBG_Prod` instance (probe 330) proves `r2`, `r3`, `r4` from `S0_pt` (probe 311: `κ₀/(κ₀+1) ≤ fT`, `1-fT ≤ η/κ₀`), `η_n = N^{-19/20}` and `SizeTendsto` (`S0_adm.2.2.1`, `tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop`); B3b is dropped. Probe line numbers in this report and the design are those of `921369b`. New Mathlib names (elaborated): `tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop`, `ge_mem_nhds`, `Filter.Tendsto.eventually_ge_atTop`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_le_rpow_of_exponent_le`, `Real.exp_le_one_iff`, `Real.sqrt_le_sqrt`, `inv_le_inv₀`, `le_div_iff₀`, `mul_le_of_le_one_left`, `Real.rpow_natCast`, `mul_inv_cancel₀`, `div_le_one`, `Real.exp_pos`, `Real.sqrt_pos`, `le_of_mul_le_mul_right`; `mul_le_one₀` is deprecated in this Mathlib (warning; not used).
