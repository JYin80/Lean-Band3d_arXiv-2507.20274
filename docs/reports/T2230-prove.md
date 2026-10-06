Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 00:07:45 UTC 2026

Notation: `N = Nsz sz n = (W L)^d`, `s = W^{τ/2}`, `η_z = Im z`, `𝓑_{η,K}` = `calB`, `e` = the `z → w` error.
Pins read from `docs/tickets/checks/T2230-check.lean` §2–§3 and `RBM3D/Endpoints.lean:136-212`, `RBM3D/Main/FixedZ.lean:51-66`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | mesh `h` | `N^{-7}` | `h ≤ η_z/2` (shift lemma) with `η_z ≥ N^{-1+ε} ≥ N^{-1}` (`ε>0`, `N ≥ 1`) | `N^{-7} ≤ N^{-1}/2` iff `N^6 ≥ 2`; at `N=32`: `2^{-35}` vs `2^{-6}` |
| 2 | `‖z−w‖` | `≤ √2 N^{-7}` (box `\|ΔRe\|,\|ΔIm\| ≤ N^{-7}`); crude `≤ 2N^{-7}` | — | both versions close below |
| 3 | resolvent/`msc` Lipschitz base `η_*` | `η_* = N^{-1}` (valid: `Im z, Im w ≥ N^{-1+ε} ≥ N^{-1}`) | `η_* ≤ Im z, Im w` | Lipschitz const `N²`, entry bound `N` |
| 4 | entry/average error `e` | `e ≤ 2·N²·√2N^{-7} = 2√2 N^{-5}` (crude `4N^{-5}`) | `2e² ≤ N^{-1} ≤ 𝓑_z`, `e ≤ N^{-1}` (floor `𝓑 ≥ (Nη)^{-1} ≥ N^{-1}`, `η_z ≤ 1`) | `N=32`: `2e² = 2.8e-14` vs `N^{-1} = 3.1e-2` |
| 5 | `𝓑` shift factor | `𝓑_{η'} ≤ 2𝓑_η` for `\|η'−η\| ≤ η/2` (`(λ²+η')^{-1} ≤ 2(λ²+η)^{-1}`, `(Nη')^{-1} ≤ 2(Nη)^{-1}`) | `η'≥η/2>0`, `K ≥ 0` | factor exactly 2; random test max `1.9928` |
| 6 | `qdBound` shift factor | `min(a_w^{1/5}b_w, a_w²) ≤ min(2^{6/5}…, 4…) ≤ 4 min_z` | `2^{6/5} ≤ 4` | `2^{6/5} = 2.2974` vs 4 |
| 7 | entries (`locBad1`) | `\|G−M\|²(z) ≤ 2s𝓑_w+2e² ≤ (4s+1)𝓑_z ≤ s²𝓑_z = W^τ𝓑_z` | `s ≥ 5`: `s²−4s−1 ≥ 4` | `4` at `s=5` (needs `s ≥ 2+√5 = 4.236`) |
| 8 | averages (`locBad2`) | `\|avg−m\|(z) ≤ s𝓑_{w,0}+e ≤ (2s+1)𝓑_z ≤ s²𝓑_z` | `s²−2s−1 ≥ 0` | `s=5`: `14` (needs `s ≥ 2.414`) |
| 9 | `avg2` error | `\|G_xy(z)\|²−\|G_xy(w)\|²` and `G_xyG_yx` diffs `≤ N²·h·2N·√2` ⇒ `≤ 2√2 N^{-4}` (crude `4N^{-4}`) | `avg2_lip`: `(W^d)^{-2}·#(I_a×I_b)=1` | included in row 10 |
| 10 | profile error `E_p` | `12η_*^{-4}·h = 12√2 N^{-3}` (crude `24N^{-3}`) plus row 9 | `E_p ≤ N^{-2} ≤ min(𝓑_0^{1/5}𝓑_K, 𝓑_0²)` (floor: `N^{-6/5} ≥ N^{-2}`, `N^{-2}`) | `N=32`: `(2.83N^{-4}+16.97N^{-3})N² = 0.533`; crude `0.754` |
| 11 | qd cover | `‖avg−prof‖(z) ≤ 4s·m_z + N^{-2} ≤ (4s+1)m_z ≤ s²m_z = qdBound(τ,z)` | `s ≥ 5` | as row 7 |
| 12 | `profPM_lip`, `profPP_lip` constant | `4η^{-3}+8η^{-4} ≤ 12η^{-4}` (`η ≤ 1`) from `‖Θ‖ ≤ (1−t)^{-1}`, `1−t ≥ Im z/(1+Im z) ≥ η/2` (`η ≤ Im z ≤ 1`), `‖Θ_ζ−Θ_ξ‖ ≤ \|ζ−ξ\|(2/η)²` (`‖S^B‖=1`), `\|t−t'\|,\|m²−m'²\| ≤ 2\|m−m'\| ≤ 2η^{-2}‖z−z'‖` | `η ≤ 1`, `3 ≤ L` (`sz.three_le_L`) | numeric ratio to `12η^{-4}` at most `2.0e-6` (L=4, d=3) |
| 13 | grid size | `(4N^7+2)(N^7+2) = 4N^{14}+10N^7+4 ≤ 18N^{14} ≤ 25N^{14}` | `N^7 ≥ 1`, `0<κ` (Re length `2(2−κ) < 4`), Im length `≤ 1`; empty if either interval empty (also `ε>1`) | `25/18` |
| 14 | `net_count` | `25N^{14}·N^{-(D+15)} = 25N^{-1}·N^{-D} ≤ N^{-D}` | `N ≥ 25` | threshold used `N ≥ 32` (slack `32/25`) |
| 15 | per-point parameters | `(τ/2, D+15)` from `locSCFixed`/`QDiffFixed` at `0<τ/2`, `0<D+15` | eventually uniform on `𝐃_{κ,ε}` | no loss in `ε, κ` |
| 16 | thresholds | `32 ≤ N` (`SizeTendsto`), `5 ≤ W^{τ/2}` (`tendsto_W`, `0<𝔠`, `0<τ`); both eventually | — | at `sz0`, `τ=1/10`: `n ≥ 312` (script) |
| 17 | `QDiff` expectation half | `QDiffFixed` at `(κ,ε,τ,D)`, projection, no lift | `∀ᶠ` intersection with row 15/16 | — |

Per-pin §29 lines (all derived, no extra premise):
- `MANetLoc`, `MANetQD`: (1) no time variable; (2) no case-(ii) boundary; (3) no `L^d ≤ W^K`; `3 ≤ d` is the pin's, `3 ≤ L` from `Sizes.three_le_L`;
  (4) `∀ᶠ n` from `Admissible`, `N₀` of `locSCFixed`/`QDiffFixed` at `(τ/2,D+15)` uniform over `𝐃_{κ,ε}` (`FixedZ.lean:51,59` have `∀ᶠ n, ∀ z ∈ locDomain`);
  (5) union over `≤ 25N^{14}` points inside the probability, `x,y`/`a`/`a,b` inside per point (inherited from `locBad1z`…`qd2Badz`);
  (6) `ε>0` gives `η ≥ N^{-1+ε} ≥ N^{-1}`; `κ>0`; `W → ∞`, `N → ∞` from `Admissible`; (7) per point `τ/2`, `D+15`; mesh `N^{-7}` vs floors `N^{-1}`, `N^{-2}`.
- Pin against paper: `1_2:1226-1228` gives the fixed-`z` estimates, then "a standard `N^{-C}`-net and perturbation argument"; `locDomain` = `𝐃_{κ,ε}` of `1_2:380`
  (`|Re| ≤ 2−κ`, `N^{-1+ε} ≤ Im ≤ 1`, matches `Sizes.lean:186`). `locSCFixed → locSC`, `QDiffFixed → QDiff`: PASS (readings D500, D503, D504, not re-proposed).
- Two data, one model: pins quantify `d, 𝔠, 𝔡, sz, κ, ε, τ, D, n` (`z, a, b` inside); everything else a function of these: PASS.
- Consumer check: MA-06 probe `band_endpoints_of_pins` (`97d958e:RBM3D/Probe/T2192Pins.lean:2079-2085`) uses the same pin text; no merged consumer.
- §64 (4): only the deterministic floored right sides `W^τ𝓑_{η,distB}`, `W^τ𝓑_{η,0}`, `qdBound` are lifted (rows 5-6, floors rows 4, 10); random left sides
  move by a deterministic amount for every `ω` (`seqXmat_isHermitian`); expectation half not lifted (row 17): PASS.
- Registry plan: `scanPremises` binders `locBad1`(registered `Axioms.lean:330`), `locBad2`, `qd1Bad`, `qd2Bad` (cover lemmas); append the last three to
  `structuralProps` (§20); no owed line deleted (`locSC`, `QDiff` remain owed: `Axioms.lean:237,239` in the main worktree).

### (ii) One concrete nondegenerate instance

Cover lemmas and grid: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `Defs/Sizes.lean:260`), `n = 0`: `L=4, W=32, lam=1/64,
N = 2097152 = 2^21`, `κ = 1/10`, `ε = 1/20`, `τ = 1` (not `1/10`: at `τ=1/10`, `W^{τ/2} = 1.189 < 5` at `n=0`), `s = 32^{1/2} = 5.657 ≥ 5`, `N ≥ 32`,
net `|S| ≤ 18N^{14} ≤ 25N^{14}` (`N^7 = 2^{147}`, exact integers), `D = 2`, `D+15 = 17`.
Pins `netLoc`/`netQD`: `(d,𝔠,𝔡,κ,ε,τ,D) = (3,1/6,1/10,1/10,1/20,1/10,2)`, an `∀ᶠ` statement: the thresholds hold from `n ≥ 312` on (no witness is needed).
External hypothesis `locSCFixed`/`QDiffFixed` (not proved here, `Admissible` part computed): `Admissible sz0 (1/6) (1/10)` = `N → ∞`, `W ≥ N^{1/6}`, `(eq:WO)`.

Command (Python, no Lean; scratch `…/scratchpad/T2230/pre.py`): `python3 pre.py > out.txt; grep -c '^PASS' out.txt; grep -c '^FAIL' out.txt; grep -E '…' out.txt`

```
PASS=45 FAIL=0
PASS worst N=32,s=5: (4s+1)<=s^2 s=5.0 s^2-4s-1=4.0
PASS worst N=32,s=5 sqrt2: avg 2.828N^-4 + prof 16.97N^-3 <= N^-2 ratio=0.53309
PASS worst N=32,s=5 crude2: avg 4.0N^-4 + prof 24.0N^-3 <= N^-2 ratio=0.75391
n=0 tau= 0.1  W^(tau/2)= 1.1892071  >=5: False
n=0 tau= 1.0  W^(tau/2)= 5.6568542  >=5: True
n=0 tau= 2.0  W^(tau/2)= 32.0  >=5: True
PASS sz0 n=0,tau=1: (4s+1)<=s^2 s=5.65685 s^2-4s-1=8.37258
first n with W_n^(1/20)>=5 (tau=1/10): 312 W= 96132816409376 W^(1/20)= 5.0019988 N= 1743524220262986973199869982705630167311164540715008
PASS sz0 n=312,tau=1/10: (4s+1)<=s^2 s=5.002 s^2-4s-1=4.012
n=0: N=2.097e+06 W>=N^(1/6): True WO: True W^(1/20)=1.189 L<=W:True
n=312: N=1.744e+51 W>=N^(1/6): True WO: True W^(1/20)=5.002 L<=W:True
n=10000: N=2.101e+78 W>=N^(1/6): True WO: True W^(1/20)=11.892 L<=W:True
SB row sums min/max: 0.9999999999999999 0.9999999999999999  ||SB||_inf= 0.9999999999999999
PASS msc_lip: max |m-m'|/(|z-z'| eta^-2) <= 1 max ratio=0.2774
PASS ||Theta||_inf <= 2/eta (ratio) max ratio=0.8085
PASS profPM_lip: max ratio to 12 eta^-4 <= 1 max=2.049e-06
PASS profPP_lip: max ratio to 12 eta^-4 <= 1 max=6.317e-07
PASS Gn_entry_lip/le: ratios <=1 (random 40x40 Hermitian) max=0.7120
PASS calB_shift_le: max ratio <= 2 max=1.9928
ALL OK
```
The 45 `PASS` lines also cover: grid count at `N = 32` and `N = 2097152` (exact integers), `net_count` at `N=25`, toy clamped 1D grid (cover within mesh, `#pts ≤ len/h+2`),
rows 1, 4, 6, 7, 8, 10 at `N = 32, s = 5`, at `sz0, n = 0, τ = 1` and at `sz0, n = 312, τ = 1/10`, and `one_sub_lemT_ge` (0 violations in 1500 samples).
The Lipschitz/`calB` tests are random-sample sanity checks (`sz0`, `n=0`: `d=3, L=4, g=1/64`); the proofs are the arguments in rows 5, 12.

Finding (not a failure): `inst_netLoc`/`inst_netQD` at `τ = 1/10` need `n ≥ 312` for `W^{τ/2} ≥ 5`; they are `∀ᶠ` statements discharged by `tendsto_W`, with no witness.
The cover-lemma `example`s, if written, should use `τ = 1`, `n = 0` above.
Route note for `msc_lip`: the identity `(m−m')(1−mm') = (z−z')mm'` gives no lower bound on `|1−mm'|`; use the Stieltjes form `msc_eq_integral` (`∫ρ = 1`, `|x−z|,|x−z'| ≥ η`).

### Verdicts

- `MANetLoc` / `netLoc`: PASS. `MANetQD` / `netQD`: PASS (probability halves at `(τ/2, D+15)`, expectation half projected at `(τ, D)`).
- Intermediate pins `net_union_le`, `net_count`, `zNet_exists`, `calB_shift_le`, `one_sub_lemT_ge`, `msc_lip`, `Gn_entry_le`, `Gn_entry_lip`, `avg2_lip`, `profPM_lip`,
  `profPP_lip`, `locBad1_net`, `locBad2_net`, `qd1Bad_net`, `qd2Bad_net`: PASS (statements true with the constants of rows 1-14; no correction proposed).
- `inst_netLoc`, `inst_netQD`, `inst_zNet`: PASS (hypothesis sets satisfiable; `inst_zNet` at `n=0`, `N=2097152`).
- Overall: PASS.

## (b) Script output (stage 1b; commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2230`, branch `t/T2230`)
```
$ date -u; git log --oneline -1; git diff --stat main...t/T2230; git status --short; wc -l RBM3D/Main/ZNet.lean; grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Main/ZNet.lean; grep -c '^example' RBM3D/Main/ZNet.lean; grep -c '^private theorem' RBM3D/Main/ZNet.lean   # (wc; then 0 forbidden tokens; examples; private helpers)
Tue Oct  6 00:41:58 UTC 2026
f8e9124 T2230: MA-04 Main/ZNet (prove MANetLoc, MANetQD: the deterministic z-net)
 RBM3D/Main/ZNet.lean   | 1188 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |    5 +-
 2 files changed, 1192 insertions(+), 1 deletion(-)
    1188 RBM3D/Main/ZNet.lean
0
15
32
```
```
$ lake build RBM3D.Main.ZNet 2>&1 | grep -E 'ZNet|Build completed'; <same> | grep -c 'ZNet.lean:'   # warnings/errors of the file (committed state; the build is cached)
Build completed successfully (3355 jobs).
0
$ lake build > fullbuild.txt 2>&1; echo exit: $?   # whole library at the committed state; last lines and the audit line
Build completed successfully (4033 jobs).
exit: 0
info: RBM3D.lean:273:0: axiom audit: 6703 theorems, 2268 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
```
$ [00:35:06-00:35:48 UTC; Test/Axioms.lean temporarily at dc2d99b, ZNet.lean as committed] lake env lean precheck.lean   # precheck.lean: import RBM3D, import RBM3D.Main.ZNet, #assert_rbm_axioms
precheck.lean:3:0: error: axiom audit: 3 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`:
  [RBM.Endpoints.locBad2, RBM.Endpoints.qd2Bad, RBM.Endpoints.qd1Bad]
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, or refuted (shown false and superseded).
precheck exit: 1
$ [committed state] lake env lean precheck.lean; echo exit: $?   # then the registry diff (changed lines, first 70 chars)
axiom audit: 6723 theorems, 2270 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 90, structural 30, refuted 6).
exit: 0
-   `RBM.Endpoints.locBad1] -- the bad event of `(G_bound)` in `locSC`
+   `RBM.Endpoints.locBad1, -- the bad event of `(G_bound)` in `locSC`
+   `RBM.Endpoints.locBad2, -- the bad event of `(G_bound_ave)` in `lo
+   `RBM.Endpoints.qd1Bad, -- the bad event of `(eq:diffu1)` in `QDiff
+   `RBM.Endpoints.qd2Bad] -- the bad event of `(eq:diffu2)` in `QDiff
```
```
$ lake env lean axioms.lean   # one '#print axioms' per public declaration of ZNet.lean; count with exactly [propext, Classical.choice, Quot.sound]; count of declarations; their names
22
22
MANetLoc MANetQD net_union_le net_count calB_shift_le one_sub_lemT_ge msc_lip zNet_exists Gn_entry_le Gn_entry_lip avg2_lip profPM_lip profPP_lip locBad1_net locBad2_net qd1Bad_net qd2Bad_net netLoc netQD Inst.inst_netLoc Inst.inst_netQD Inst.inst_zNet 
```
```
$ python3 extract.py RBM3D/Main/ZNet.lean stmt MANetLoc MANetQD net_union_le net_count zNet_exists calB_shift_le one_sub_lemT_ge msc_lip Gn_entry_le Gn_entry_lip avg2_lip profPM_lip profPP_lip locBad1_net locBad2_net qd1Bad_net qd2Bad_net netLoc netQD   # up to ':=', whitespace collapsed
def MANetLoc : Prop := locSCFixed → locSC
def MANetQD : Prop := QDiffFixed → QDiff
theorem net_union_le {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Finset ι) (A : Set Ω) (B : ι → Set Ω) (p : ℝ≥0∞) (hA : A ⊆ ⋃ i ∈ S, B i) (hB : ∀ i ∈ S, P (B i) ≤ p) : P A ≤ (S.card : ℝ≥0∞) * p
theorem net_count {N D : ℝ} (c : ℕ) (hN : 25 ≤ N) (hc : (c : ℝ) ≤ 25 * N ^ (14 : ℕ)) : (c : ℝ≥0∞) * ENNReal.ofReal (N ^ (-(D + 15))) ≤ ENNReal.ofReal (N ^ (-D))
theorem zNet_exists {d : ℕ} (sz : Sizes d) {κ ε : ℝ} (hκ : 0 < κ) (n : ℕ) : ∃ S : Finset ℂ, (S.card : ℝ) ≤ 25 * Nsz sz n ^ (14 : ℕ) ∧ (∀ w ∈ S, sz.locDomain κ ε n w) ∧ ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S, |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)
theorem calB_shift_le {d : ℕ} (sz : Sizes d) (n : ℕ) {η η' K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (h : |η' - η| ≤ η / 2) : calB sz n η' K ≤ 2 * calB sz n η K
theorem one_sub_lemT_ge {z : ℂ} (hz : 0 < z.im) : z.im / (1 + z.im) ≤ 1 - lemT z
theorem msc_lip {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz' : η ≤ z'.im) : ‖msc z - msc z'‖ ≤ η⁻¹ * η⁻¹ * ‖z - z'‖
theorem Gn_entry_le (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (x y : Idx d (sz.L n) (sz.W n)) : ‖sz.Gn n z ω x y‖ ≤ η⁻¹
theorem Gn_entry_lip (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz' : η ≤ z'.im) (x y : Idx d (sz.L n) (sz.W n)) : ‖sz.Gn n z ω x y - sz.Gn n z' ω x y‖ ≤ η⁻¹ * η⁻¹ * ‖z - z'‖
theorem avg2_lip {d : ℕ} (sz : Sizes d) (n : ℕ) (F F' : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) {c : ℝ} (h : ∀ x y, ‖F x y - F' x y‖ ≤ c) (a b : Zd d (sz.L n)) : ‖avg2 sz n F a b - avg2 sz n F' a b‖ ≤ c
theorem profPM_lip (sz : Sizes d) (n : ℕ) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz1 : z.im ≤ 1) (hz' : η ≤ z'.im) (hz1' : z'.im ≤ 1) (a b : Zd d (sz.L n)) : ‖profPM sz n z a b - profPM sz n z' a b‖ ≤ 12 * η⁻¹ ^ 4 * ‖z - z'‖
theorem profPP_lip (sz : Sizes d) (n : ℕ) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz1 : z.im ≤ 1) (hz' : η ≤ z'.im) (hz1' : z'.im ≤ 1) (a b : Zd d (sz.L n)) : ‖profPP sz n z a b - profPP sz n z' a b‖ ≤ 12 * η⁻¹ ^ 4 * ‖z - z'‖
theorem locBad1_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n) (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w) (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S, |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) (ω : sz.SeqΩ) (hω : locBad1 sz κ ε τ n ω) : ∃ w ∈ S, locBad1z sz (τ / 2) n w ω
theorem locBad2_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n) (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w) (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S, |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) (ω : sz.SeqΩ) (hω : locBad2 sz κ ε τ n ω) : ∃ w ∈ S, locBad2z sz (τ / 2) n w ω
theorem qd1Bad_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n) (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w) (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S, |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) (ω : sz.SeqΩ) (hω : qd1Bad sz κ ε τ n ω) : ∃ w ∈ S, qd1Badz sz (τ / 2) n w ω
theorem qd2Bad_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n) (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w) (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S, |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) (ω : sz.SeqΩ) (hω : qd2Bad sz κ ε τ n ω) : ∃ w ∈ S, qd2Badz sz (τ / 2) n w ω
theorem netLoc : MANetLoc
theorem netQD : MANetQD
```
```
$ python3 extract.py ZNet.lean full inst_netLoc inst_netQD inst_zNet   # the three instances (statement and proof term); then the 15 further `example`s as lemma@line
theorem inst_netLoc (h : locSCFixed) : ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧ Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) := netLoc h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_netQD (h : QDiffFixed) : ∀ᶠ n in atTop, (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧ Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧ ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n), ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) - profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧ ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) - profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im := netQD h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_zNet : ∃ S : Finset ℂ, (S.card : ℝ) ≤ 25 * Nsz sz0 0 ^ (14 : ℕ) ∧ (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧ ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) 0 z → ∃ w ∈ S, |z.re - w.re| ≤ Nsz sz0 0 ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz0 0 ^ (-7 : ℝ) := zNet_exists sz0 (by norm_num) 0
inst_zNet(nonempty)@1093 locBad1_net@1113 locBad2_net@1119 qd1Bad_net@1125 qd2Bad_net@1131 net_union_le@1138 net_count@1150 calB_shift_le@1154 one_sub_lemT_ge@1157 msc_lip@1159 Gn_entry_le@1162 Gn_entry_lip@1165 avg2_lip@1170 profPM_lip@1174 profPP_lip@1180
```
```
$ lake env lean T2230-eq-check.lean   # = docs/tickets/checks/T2230-check.lean with `import RBM3D.Main.ZNet` after line 22, plus 22 examples (2 `X_pin = X := rfl`, 17 + 3 `Y_pin := @Y`); names
exit: 0; error lines: 0; examples: 22
MANetLoc MANetQD net_union_le net_count zNet_exists calB_shift_le one_sub_lemT_ge msc_lip Gn_entry_le Gn_entry_lip avg2_lip profPM_lip profPP_lip locBad1_net locBad2_net qd1Bad_net qd2Bad_net netLoc netQD inst_netLoc inst_netQD inst_zNet 
$ git show 97d958e:RBM3D/Probe/T2192Pins.lean | sed -n '2031,2046p' > block.txt; python3 -c "block in text"
block in text: True ; block lines: 16
sed -n 2031,2046p of the probe == block.txt
$ bash clash.sh   # grep -rnE '^\s*(private )*(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+NAME\b' RBM3D --include=*.lean, minus Main/ZNet.lean and Probe/; 23 names (22 + zNet)
MANetLoc: 0 MANetQD: 0 net_union_le: 0 net_count: 0 zNet_exists: 0 zNet: 0 calB_shift_le: 0 one_sub_lemT_ge: 0 msc_lip: 0 Gn_entry_le: 0 Gn_entry_lip: 0 avg2_lip: 0 profPM_lip: 0 profPP_lip: 0 locBad1_net: 0 locBad2_net: 0 qd1Bad_net: 0 qd2Bad_net: 0 netLoc: 0 netQD: 0 inst_netLoc: 0 inst_netQD: 0 inst_zNet: 0 
lines not 0 hit: 0
```

### Narrative (stage 1b)
- Delivered (all targets): `RBM3D/Main/ZNet.lean`, 1188 lines (ticket estimate 1260, range 950-1500: no split), commit `f8e9124` on `t/T2230`; `git diff --stat main...t/T2230` lists `ZNet.lean` and `Test/Axioms.lean` only. No obstruction, no hypothesis added, no pinned signature changed; the only edit outside `ZNet.lean` is the registry lines of `Test/Axioms.lean` that the ticket allows.
- Targets 1-3: probe `:2031-2046` byte-equal; the 2 pins, the 17 theorems and the 3 instances are accepted by the 22 compiled equality examples of the check file; `netLoc`, `netQD` carry no hypothesis beyond the pin (`locSCFixed`, resp. `QDiffFixed`).
- Imports exactly `RBM3D.Main.FixedZ`, `RBM3D.Induction.ContinuityNet` (Targets 5). Ports: none (no file of `../RBM1D`, `../RBM2D` was opened or copied). Helpers are `private theorem znet_*` (32); public names are `RBM.Endpoints.*` as pinned.
- Route (new mathematics; deterministic, no good event, no random control):
  - `zNet_exists`: two 1D grids `lo + k h`, `k <= floor((hi-lo)/h)`, `h = N^{-7}`, no clamping; `|S| <= (4N^7+1)(N^7+1) <= 25 N^14`; `S = {}` if `2-κ < 0` or `N^{-1+ε} > 1`.
  - `msc_lip` without the Stieltjes integral: `z - z' = (m - m')((m+z)(m'+z') - 1)` (`linear_combination` of the two `msc_mul`), and `|q q' - 1| >= Im q Im q'` from `Im((q q' - 1) conj q) = |q|^2 Im q' + Im q`; `msc_eq_integral` is not used (this replaces the route note of (a)).
  - `profPM_lip`, `profPP_lip`: `‖ξ Θ_ξ(a,b) - ξ' Θ_ξ'(a,b)‖ <= |ξ-ξ'| (B + B^2)` (`Theta_sub_Theta`, `norm_SB`, entries <= the `ℓ^∞` norm), `B = 2/η` (`norm_Theta_le`, `one_sub_lemT_ge`), `|ξ-ξ'| <= 2|m-m'|`, `4η^-3 + 8η^-4 <= 12η^-4` for `η <= 1`, `W^d >= 1`.
  - cover lemmas, `u = N^-1 <= 1/32`: `‖z-w‖ <= 2u^7`, `|Im w - Im z| <= Im z/2`; entry/average error `4u^5 <= u`, `2e^2 <= u <= 𝓑` (floor `inv_size_mul_le_calB`); averages of `|G|^2`, `G_xy G_yx`: `4u^4`; profiles `24u^3`; `4u^4 + 24u^3 <= u^2`; `calB_shift_le` factor 2, factor 4 under the `min` (`2^{1/5} <= 2`); `4s+1`, `2s+1 <= s^2` for `s = W^{τ/2} >= 5`.
  - `netLoc`, `netQD`: `locSCFixed`/`QDiffFixed` at `(κ, ε, τ/2, D+15)`, thresholds `32 <= N` (`SizeTendsto`) and `5 <= W^{τ/2}` (`tendsto_W`, `tendsto_rpow_atTop`) by `filter_upwards`, `zNet_exists`, `net_union_le` over the events `locBad1z`, `locBad2z`, `qd1Badz`, `qd2Badz`, `net_count`; the expectation half of `QDiff` is the projection `(hn' z hz).2 a b` of `QDiffFixed` at `(κ, ε, τ, D)`.
- Instances: `inst_netLoc`, `inst_netQD` at `d = 3`, `sz0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`, `ε = 1/20`, `τ = 1/10`, `D = 2` (`Admissible` by `sz0_admissible`, positivity by `norm_num`); `locSCFixed`, `QDiffFixed` stay hypotheses (they follow from `∀ d, UNMLOut d`, owed by ST-6, by `fixed_of_ML`). `inst_zNet` at `n = 0` (`N = 2097152`). The 15 `example`s: a nonempty grid, the four cover lemmas at `n = 0`, `τ = 1` (`W^{1/2} = √32 >= 5`, the net of `inst_zNet`), and each intermediate lemma at concrete data.
- Registry: the pre-check run before the registry lines (00:35:06-00:35:48 UTC, `Axioms.lean` temporarily at `dc2d99b`, restored afterwards: `git status` clean) flagged exactly `locBad2`, `qd1Bad`, `qd2Bad`; they are appended to `structuralProps` (DECISIONS §20: event predicates used by deterministic lemmas); after: exit 0. The registry diff is 4 added lines and the `locBad1]` line changed to `locBad1,`; no owed line deleted (`locSC`, `QDiff` stay owed at `Axioms.lean:237`, `:239`; `MANetLoc`, `MANetQD` occur in those two comments only).
- The full `lake build` (whole library with `#assert_rbm_axioms`) exits 0 at the committed state; `import RBM3D.Main.ZNet` is added to `RBM3D.lean` by the hub at merge (not touched here).
- Section (a): no mistake found, no (a′). Differences from its table: grid count `(4N^7+1)(N^7+1)` (no clamp) instead of `(4N^7+2)(N^7+2)`, and the `msc_lip` route; its constants (`12η^-4`, `N >= 32`, `W^{τ/2} >= 5`, `τ = 1` for the cover instances) are the ones used.

## (c) Verified Mathlib names (all resolve: `lake build RBM3D.Main.ZNet` exit 0; each occurs in the committed file, script `mathlib_names.py`)
- measure / sums: measure_mono measure_biUnion_finset_le ENNReal.ofReal_natCast ENNReal.ofReal_mul ENNReal.ofReal_le_ofReal Set.mem_biUnion Finset.sum_le_sum Finset.sum_const nsmul_eq_mul Finset.sum_sub_distrib Finset.single_le_sum Finset.le_sup 
- rpow / sqrt: Real.rpow_natCast Real.rpow_add Real.rpow_mul Real.rpow_neg Real.rpow_neg_one Real.rpow_one Real.rpow_nonneg Real.rpow_pos_of_pos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_exponent_ge Real.mul_rpow Real.sq_sqrt Real.sqrt_eq_rpow Real.le_sqrt_of_sq_le tendsto_rpow_atTop 
- floor / finset: Nat.floor_le Nat.lt_floor_add_one Nat.floor_le_floor Finset.card_image_le Finset.card_product Finset.mem_image Finset.mem_product Finset.mem_range 
- complex / norm: Complex.norm_le_abs_re_add_abs_im Complex.im_le_norm Complex.norm_conj Complex.norm_real Complex.norm_natCast Complex.sq_norm Complex.normSq_pos Complex.normSq_nonneg Complex.inv_im abs_norm_sub_norm_le Matrix.linfty_opNorm_def Matrix.sub_apply Matrix.smul_apply 
- order / field: inv_anti₀ one_le_inv₀ inv_le_one_of_one_le₀ div_le_iff₀ le_div_iff₀ div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_mul_cancel₀ mul_min_of_nonneg min_le_min pow_le_pow_left₀ one_le_pow₀ le_of_mul_le_mul_right mul_lt_mul_of_pos_right Filter.Tendsto.eventually_ge_atTop
- Absent or different (tool log): `Real.tendsto_rpow_atTop` unknown (root `tendsto_rpow_atTop` is used); `one_le_inv_of_le_one_of_pos` unknown (`one_le_inv₀ : 0 < a → (1 ≤ a⁻¹ ↔ a ≤ 1)`); `Real.le_sqrt` has two hypotheses `(hx : 0 ≤ x) (hy : 0 ≤ y)` (`Real.le_sqrt_of_sq_le` is used); `zero_le` takes no explicit argument for `ℝ≥0` (`fun _ _ => zero_le`).

## (d) Open issues and paper-delta candidates
- Paper deltas: none (`T2230a…`: none). The pins are the signed design (D500, D503, D504, not re-proposed); no pin is at odds with `1_2:1228` ("a standard `N^{-C}`-net and perturbation argument, whose details we omit", `paper/tex/1_2_Intro_model_result.tex:1228`, read in the main worktree).
- Findings, no repair needed: (1) the verbatim docstring cites `msc_eq_integral` and RBM2D `regionUnif_core`; neither is used here (docstrings are not evidence). (2) `3 ≤ d` of the cover lemmas is used only as `2 ≤ d` (pinned, kept). (3) At `sz0`, `τ = 1/10`, `W^{τ/2} >= 5` holds from `n >= 312` ((a) script), so `inst_netLoc`, `inst_netQD` are `∀ᶠ` statements without a witness `n`; the cover examples use `τ = 1`, `n = 0`.
- For the hub: add `import RBM3D.Main.ZNet` after the last `import` line of `RBM3D.lean`; the registry hunk is the end of `structuralProps` (siblings T2197, T2227, T2228 may append to `Test/Axioms.lean`: union at merge, §20 (3), per the ticket).
- No open mathematical issue; `locSC`, `QDiff` stay owed until ST-6 proves `∀ d, UNMLOut d` and MA-06 assembles (ticket, Downstream).
