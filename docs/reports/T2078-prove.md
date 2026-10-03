Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 22:06:08 UTC 2026

Sources: `git -C ../RBM2D show c9a24cf:RBM2D/Green/{FlucAvg,LDE}.lean`; `RBM3D/Green/{FlucVanish,EntryDom,RowIndep,Pins}.lean`, `RBM3D/Gauss/{FineModel,Model}.lean`, `RBM3D/Defs/{Sizes,Block}.lean`, `docs/DECISIONS.md` §29, §30, `docs/reports/T2061-prove.md`.

### (i) Exponent table

Uniform-weight occurrences in the two sources (`grep -n "UniformWeight\|uniformWeight"` at c9a24cf): only docstrings (`FlucAvg:348`, `:355`, `:362`; none in `LDE`). No declaration of `FlucAvg`/`LDE` takes `UniformWeight`; `card_Sblk_support` uses only the support count (`flucVanish_card_svarSupport_eq`), merged as `(2d+1) W^d`. So `BoundedWeight` is needed in this ticket nowhere as a hypothesis; `≤ c` vs `= c` never arises (the weight values are used downstream, `FlucAvgDet`/`FlucIter`, S1-20+). Here `norm_flucAvg_le` takes arbitrary `T`, bound `(∑|T k|) B`, and for the bounded weight `boundedWeight_svarF` (`∑ t ≤ 1`, merged) gives `≤ B`.

| RBM2D declaration (line) | `d = 2` token | `d ≥ 3` replacement | why it holds | verdict |
|---|---|---|---|---|
| `card_blockAvg_support` (FlucAvg:357) | `W^2`, `Z2 L` | `W^d`, `Zd d L`; merged `flucVanish_card_blockSupport` | block = `W^d` sites (`card_Iblk`) | PASS |
| `card_Sblk_support` (365) | `5 * W^2`, `sbSupport L` | `(2*d+1) * W^d`, `flucVanish_sbSupport d L`; merged `flucVanish_card_svarSupport_eq` (`3 ≤ L`) | `2d` unit neighbours distinct for `L ≥ 3` (`card_nbhd`), plus `0` | PASS (constant `5 = 2·2+1` becomes `2d+1`) |
| `flucAvg_card_Idx_eq_size` (374) | `sq`, `Z2` | `Fintype.card (Idx d L W) = (W L)^d = size n`; merged `Sizes.card_Idx`; keep a public alias (consumers: Eq45Small, FlucThreshold, IBP, IBPDet, MinorDiffCond, ...) | `card_Idx` | PASS |
| `flucAvg_card_Z2_le_size` (380) | `L² ≤ (WL)²` | `L^d ≤ (W L)^d` (`Nat.pow_le_pow_left`, `L ≤ W L` since `W ≥ 1`) | monotone in `d` | PASS |
| `tendsto_W` (390), `eventually_le_W` (396, **key**) | none | unchanged in form; `sz.Bandwidth 𝔠` (`W ≥ N^𝔠`, `∀ᶠ n`), `sz.SizeTendsto`, `0 < 𝔠` | `N^𝔠 → ∞`, `W ≥ N^𝔠` eventually ⇒ `W → ∞` ⇒ `∀ᶠ n, p ≤ W n` | PASS |
| envelope/`FlucBound`/`flucBound_env`/measurability (FlucAvg:96-345) | none (`η = (1-t) Im m(E)`, `B = 2(η⁻¹+1)`, `ε = 4η⁻¹`) | index `Idx d (sz.L n) (sz.W n)`, `spectralZ → zt`, `spectralM → mE` | `‖G‖ ≤ η⁻¹` for Hermitian `H`, `|m(E)| = 1` for `\|E\| ≤ 2` | PASS (dimension-free) |
| `stochDom_ldeRow`, `stochDom_ldeCol` (LDE:410, 451) | `Sblk2 L W`, `BlockIndex L W` | `svar d (sz.L n) (sz.W n) (sz.lam n)`, `Vtx d L W`, `OffPair d L W` (as pinned by `EntryDom` `hLrow`/`hLcol`); card `≤ N²` (`eventually_card_LdeIdx_le`, `Ccard = 2`) | algebraic identities (`ldeRowLHS_eq`, `rowVarSum_eq`) are dimension-free; `svar_comm` | PASS |
| `Sblk_diag_pos` (564), `Sblk2_diag_eq` (576) | `1/(5 W²)` | `svar d L W g i i = W^{-d}(1+2dg²)⁻¹ > 0` (`svarF_diag`, `Defs/Block.lean:74` `sbKernelR 0`) | `1 + 2dg² > 0` for every real `g`; depends on `g = lam n` | PASS (statement changes: `g` enters) |
| `eventually_card_Idx_le` (649) | `(W L)²` | `Fintype.card (Vtx d L W) = (L W)^d = size n` (`card_BlockIndex`), `Ccard = 1` | exact equality, no `L ≤ W^K` | PASS |
| `integral_norm_Hflow_diag_pow` (622) | `u^p (2p-1)!! S_xx^p` | same, `S_xx = svarF d L W g x x` | `H_xx = √u ω_{(x,x,true)}`, `ω ~ N(0, gvarF) = N(0, svarF x x)` (`FineModel.lean:89`, diagonal case) | PASS |
| **`stochDom_normSq_Hflow_diag`** (659, **key**) | `Sblk2`, `BlockIndex` | `PerTimeDomAt (seqP sz) sz.size (U := Vtx d (sz.L n) (sz.W n)) (‖blockMat H i i‖²) (svar d L W (sz.lam n) i i)` (= `sz.PrecPT`, the `hLdiag` text of `EntryDom.diag_bound_stochDom`) | below | PASS |

Moment bound of the key diagonal target (no dimension enters): `E‖H_xx‖^{4p} = u^{2p} (4p-1)!! S_xx^{2p}`, and `MomentDomAt` asks `∫|Y|^{2p} ≤ C N^{εp} Φ^{2p}` with `Y = ‖H_xx‖²`, `Φ = S_xx`. Hence `C = (4p-1)!! + 1` (`RowIndep_dfac (2p) + 1`), independent of `d`, `W`, `L`, `g`, `n`, and `u^{2p} ≤ 1` for `0 ≤ u ≤ 1`. The `d`-dimensional exponents are only `Ccard`: `#Vtx = N` (`Ccard = 1`), `#LdeIdx ≤ N²` (`Ccard = 2`), the same as `d = 2` (counted in `N`, not `W`). The `#A` dependence of a moment bound (`(2d+1) W^d`) sits in S1-20's `FlucIter`, not in these targets.

Constants and windows the targets depend on:

| item | value | constraint | slack |
|---|---|---|---|
| `𝔠` (`eventually_le_W`, `sz0`) | `1/6` | `0 < 𝔠`; `W ≥ N^𝔠` eventually | `N^{1/6}/W = √(L/W) → 0` (script: `0.354` at `n=0`, `3.5e-13` at `n=10^6`) |
| threshold `n0(p)` of `p ≤ W n` | `sz0`: `n0(10)=0`, `n0(10^3)=1`, `n0(10^6)=7` | `∀ᶠ n`, depends on the sequence and `p` only | none needed; no constant carries `W`, `L`, `lam` |
| time `t n` | `t ∈ [0,1)` (`ht0`, `ht1`) | `Im z_t = (1-t) Im m(E) ≠ 0` (`zt_im_ne_zero`); diagonal bound needs only `0 ≤ t ≤ 1` | `t = 1/2`: `Im z_t = 0.5` |
| `\|E n\| ≤ 2-κ` (`ldeRow/Col`) | `E = 0`, `κ = 1/10` | `κ > 0` | `1.9` vs `0` |
| `W ≥ 1`, `3 ≤ L` | `W = 2`, `L = 3` | `sum_sbKernelR`, `card_nbhd` | `L = 3` is tight, allowed |
| `g` (`lam n`) | any real; `1/2` | `1 + 2dg² > 0` | `S_ii = 1/20` at `g = 1/2` |

§29 items for `eventually_le_W` (and the other targets): (1) time domain `0 ≤ t < 1`: used as stated, never `s < 0`; (2) the boundary `1 − ilambda²/L²` and `ilambda > L`: no target has a hypothesis on `lam` against `L` (only `3 ≤ L` from `Sizes`); (3) `L^d ≤ W^K`: not used, since `#Vtx = N` exactly and `#LdeIdx ≤ N²`; (4) `∀ n` vs `∀ᶠ n`: `eventually_le_W` is `∀ᶠ n` from `Bandwidth` (itself `∀ᶠ`) and `SizeTendsto`; the diagonal bound takes `∀ᶠ n` (`N ≥ 1`). No constant depends on `W`, `L`, `lam`.

### (ii) One concrete nondegenerate instance

Sample (ticket): `d = 3, L = 3, W = 2, g = 1/2, u = t = 1/2` (`N = (WL)^3 = 216`, `#Zd = 27`); sequence level: merged `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `d = 3`), `E = 0`, `κ = 1/10`, `t = 1/2`. Command (Python `fractions`, no Lean; file `scratchpad/T2078/check.py`): `python3 check.py`. Output, verbatim:

```
d,L,W,g = 3 3 2 1/2 | #Zd = 27 = L^d 27 | #Idx = #Vtx = (WL)^d = 216 = 216 | L^d <= N: True
sum_b S^B row = 1 | distinct values [Fraction(0, 1), Fraction(1, 10), Fraction(2, 5)] | support blocks 7 = 2d+1 = 7 | fine support 56 = (2d+1)W^d = 56
BoundedWeight: 0<=t<=c=W^-d on A: True | sum t over fine row = 1 <= 1 | max t = 0.05 c = 0.125
S_ii = W^-d/(1+2dg^2) = 1/20 = 0.05 | formula 1/20
N = 216
p=1: E|Y|^(2p) = E|H_ii|^4 = u^2*dfac(2)*S^2 = 3/1600 = 0.001875 <= C*Phi^(2p) = 4*S^2 = 0.01 (<= C N^(eps p) Phi^(2p)): True; slack 5.333
p=2: E|Y|^(2p) = E|H_ii|^8 = u^4*dfac(4)*S^4 = 21/512000 = 4.10156e-05 <= C*Phi^(2p) = 106*S^4 = 0.0006625 (<= C N^(eps p) Phi^(2p)): True; slack 16.152
MC E x^4 = 0.0018769539713089202 exact 3 (uS)^2 = 0.001875
P(Y > N^1 S) = erfc(sqrt(N^tau/(2u))) = 5.965e-96 <= N^-1 = 4.630e-03: True
P(Y > N^0.5 S) = erfc(sqrt(N^tau/(2u))) = 5.906e-08 <= N^-1 = 4.630e-03: True
--- sz0 (d=3), Bandwidth 1/6, SizeTendsto, eventually p<=W
n=0: L=4 W=32 N^(1/6)=11.3137 <= W: True ratio N^(1/6)/W = 3.536e-01 (=sqrt(L/W)) logN/logW = 4.2000 S_ii=3.0473e-05
n=1: L=8 W=1024 N^(1/6)=90.5097 <= W: True ratio N^(1/6)/W = 8.839e-02 (=sqrt(L/W)) logN/logW = 3.9000 S_ii=9.3132e-10
n=2: L=12 W=7776 N^(1/6)=305.47 <= W: True ratio N^(1/6)/W = 3.928e-02 (=sqrt(L/W)) logN/logW = 3.8321 S_ii=2.1268e-12
n=10: L=44 W=5153632 N^(1/6)=15058.5 <= W: True ratio N^(1/6)/W = 2.922e-03 (=sqrt(L/W)) logN/logW = 3.7345
n=1000: L=4004 W=32160320320160032 N^(1/6)=1.13477e+10 <= W: True ratio N^(1/6)/W = 3.528e-07 (=sqrt(L/W)) logN/logW = 3.6547
n=1000000: L=4000004 W=32000160000320000320000160000032 N^(1/6)=1.13137e+19 <= W: True ratio N^(1/6)/W = 3.536e-13 (=sqrt(L/W)) logN/logW = 3.6287
p=10: first n with p<=W(n): n0=0, W(n0)=32; all n>=n0 ok (W increasing)
p=1000: first n with p<=W(n): n0=1, W(n0)=1024; all n>=n0 ok (W increasing)
p=1000000: first n with p<=W(n): n0=7, W(n0)=1048576; all n>=n0 ok (W increasing)
|E| <= 2-kappa: True | 0<=t<1: True | Im z_t = (1-t) Im m(E) = 0.5 != 0
```

Reading: line 1 `#Vtx = #Idx = N`; lines 2-3 `#A = (2d+1) W^d = 56`, bounded weight `0 ≤ t ≤ W^{-d}`, mass `1`, two nonzero values `0.05`, `0.0125` (`g² ≠ 1`); line 4 `S_ii = 1/20`; `p = 1, 2` lines the moment bound `E|H_ii|^{4p} ≤ ((4p-1)!!+1) Φ^{2p}` with slack `5.3` and `16.2`, Monte Carlo confirming `E x^4 = 3(uS)²`; tail lines the resulting `N^{-D}` probability at one sample; `sz0` lines: `Bandwidth (1/6)` holds at every `n` with limit `N^{1/6}/W = √(L/W) → 0` (`W/L → ∞`, `L = 4(n+1)`, `W = (2(n+1))^5`), `SizeTendsto` (`N ≥ n`, `sz0_tendsto` merged), `∀ᶠ n, p ≤ W n` at three `p`. External hypotheses: `Bandwidth` and `SizeTendsto` are the only limit-type hypotheses and are computed above at `sz0` (merged `sz0_bandwidth`, `sz0_tendsto`, `W_tendsto_sz0`); all others are deterministic.

### Verdict per target

* `eventually_le_W` (FlucAvg:396): **PASS** (`∀ᶠ n`; no constant depends on `W`, `L`, `lam`; §29 items (1)-(4) above).
* `stochDom_normSq_Hflow_diag` (LDE:659): **PASS** (`C = (4p-1)!! + 1`, dimension-free; `svar` replaces `Sblk2`; diagonal `W^{-d}(1+2dg²)⁻¹ > 0` for all real `g`).
* Remaining public declarations (measurability, envelopes, `FlucBound`, `flucBound_env`, `condExpDiag`, counting facts, `stochDom_ldeRow/Col` and their private helpers): **PASS**; no declaration is dropped for the two sources except the RBM2D `Sblk2`/`sbKre2`-based ones, replaced by merged `svar` (`EntryDom.lean:40-43`).
* Paper-delta candidates for the report: `T2078a`: `card_Sblk_support` orientation (`(split j).1 - (split i).1 ∈ …`, as `boundedWeight_svarF`, instead of RBM2D `blk i - blk j`; same set, `sbSupport` symmetric) and constant `5 → 2d+1`; `T2078b`: `Sblk2_diag_eq` becomes `svar … i i = W^{-d}(1+2dg²)⁻¹` (`g = lam n` enters; RBM2D has none).

Overall verdict: **PASS**.

## (a′) Preflight corrections — Sat Oct  3 22:31:00 UTC 2026

* Section (a), last bullet of "Verdict per target", says the RBM2D `Sblk2`/`sbKre2`-based declarations are replaced by the merged `svar`; the table row for `Sblk_diag_pos`/`Sblk2_diag_eq` says they are ported with a changed statement. The table row is what was done: both are ported public declarations (RBM2D names kept, stated for `svar d L W g`); no declaration of the two sources is dropped (b.5). No verdict changes.

## (b) Script output

### b.1 Build, hygiene, scope
$ date -u
Sat Oct  3 22:31:00 UTC 2026
$ lake build RBM3D.Green.LDE   # run after the last edit; lines of its output with the module, the result, or an error
80:✔ [3331/3331] Built RBM3D.Green.LDE (4.0s)
81:Build completed successfully (3331 jobs).
$ lake build   # whole library, root #assert_rbm_axioms included (the root does not import Green/LDE yet)
Build completed successfully (3819 jobs).  [exit 0]
$ git log --oneline -1; git diff main...t/T2078 --stat; wc -l RBM3D/Green/LDE.lean
df28c0e T2078: port Green/FlucAvg and Green/LDE (S1-18): fluctuation averaging layer, row/column/diagonal LDE inputs
 RBM3D/Green/LDE.lean | 1404 ++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1404 insertions(+)
    1404 RBM3D/Green/LDE.lean
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom ' RBM3D/Green/LDE.lean | wc -l
0
### b.2 Axioms of every public declaration (64: 45 in RBM.Green, 19 in RBM.Green.LDEInst)
$ python3 axlist.py > axioms_check.lean   # import RBM3D.Green.LDE + one #print axioms per public name
$ lake env lean axioms_check.lean | sed "s/.*depends on axioms: //" | sort | uniq -c
  64 [propext, Classical.choice, Quot.sound]
$ grep -E 'RBM.Green.(eventually_le_W|stochDom_normSq_Hflow_diag)' axioms.out
'RBM.Green.eventually_le_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_normSq_Hflow_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
### b.3 Target statements, extracted from RBM3D/Green/LDE.lean by script
-- RBM3D/Green/LDE.lean:450
theorem eventually_le_W {d : ℕ} (sz : Sizes d) {c : ℝ} (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hbw : sz.Bandwidth c) (p : ℕ) : ∀ᶠ n : ℕ in atTop, p ≤ sz.W n :=
-- RBM3D/Green/LDE.lean:1099
theorem stochDom_normSq_Hflow_diag {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i) :=
-- stochDom_ldeRow RBM3D/Green/LDE.lean:850 (statement 7 lines, first 3 shown; hypotheses hκ hsz hE ht0 ht1 as RBM2D)
theorem stochDom_ldeRow {κ : ℝ} (hκ : 0 < κ) (hsz : sz.SizeTendsto) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
$ python3 pincmp.py   # conclusions against the hypotheses hLrow hLcol hLdiag of EntryDom.diag_bound_stochDom
hLrow   (EntryDom.diag_bound_stochDom) vs conclusion of stochDom_ldeRow             : IDENTICAL after whitespace normalisation
hLcol   (EntryDom.diag_bound_stochDom) vs conclusion of stochDom_ldeCol             : IDENTICAL after whitespace normalisation
hLdiag  (EntryDom.diag_bound_stochDom) vs conclusion of stochDom_normSq_Hflow_diag  : IDENTICAL after whitespace normalisation
### b.4 Compiled nonempty instances (at `sz0`: d=3, L n=4(n+1), W n=(2(n+1))^5, lam n=(2(n+1))^-6; E=0, t=1/2), extracted by script
-- LDE.lean:1183
theorem eventually_le_W_sz0 (p : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, p ≤ sz0.W n :=
  eventually_le_W sz0 (c := 1 / 6) (by norm_num) sz0_tendsto sz0_bandwidth p
-- LDE.lean:1187
theorem eventually_le_W_sz0_million : ∀ᶠ n : ℕ in Filter.atTop, 1000000 ≤ sz0.W n :=
  eventually_le_W_sz0 1000000
-- LDE.lean:1195
theorem stochDom_normSq_Hflow_diag_sz0 :
    sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω) i i‖ ^ 2)
      (fun n i _ => svar 3 (sz0.L n) (sz0.W n) (sz0.lam n) i i) :=
  stochDom_normSq_Hflow_diag sz0 sz0_tendsto (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num)
-- LDE.lean:1242  stochDom_ldeRow_sz0 (conclusion = hLrow text), proof term:
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2) :=
  stochDom_ldeRow sz0 (κ := 1) one_pos sz0_tendsto (E := fun _ => 0) (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
-- LDE.lean:1253  stochDom_ldeCol_sz0 (conclusion = hLcol text), proof term:
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2) :=
  stochDom_ldeCol sz0 (κ := 1) one_pos sz0_tendsto (E := fun _ => 0) (t := fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
-- LDE.lean:1264
example : GijOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  entry_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) one_pos sz0_admissible
    (E := fun _ => 0) (t := fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) one_pos
    stochDom_ldeRow_sz0 stochDom_ldeCol_sz0
-- LDE.lean:1279  example : GiiOmegaSeq sz0 ... := diag_bound_stochDom sz0 ... stochDom_ldeRow_sz0 stochDom_ldeCol_sz0 hLquad stochDom_normSq_Hflow_diag_sz0  (hLquad, the S1-12..S1-19 pin, is the only hypothesis)
-- LDE.lean:1205 (n=0: L=4, W=32, lam=1/64: S_ii = 32^-3 (1+6/64^2)^-1 > 0)
theorem diag_variance_sz0 (i : Vtx 3 (sz0.L 0) (sz0.W 0)) :
    svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i i
      = ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * (3 : ℝ) * (1 / 64) ^ 2)⁻¹ ∧
    0 < svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i i := ...
-- LDE.lean:1228 (d=3, L=3, W=2, g=1/2, u=1/2: S_xx=1/20, E|H_xx|^4 = u^2 * 3 * S_xx^2)
theorem integral_norm_Hflow_diag_pow_szT (x : Idx 3 (szT.L 0) (szT.W 0)) :
    ∫ ω, ‖szT.seqHflow 0 (1 / 2) ω x x‖ ^ (2 * 2) ∂(Sizes.seqP szT) = 3 / 1600 := by ...
$ python3 -c "[print(n,(2*(n+1))**5) for n in (6,7)]"
6 537824
7 1048576
### b.5 Statement diff against RBM2D c9a24cf (python3 stmtdiff.py: RBM2D text renamed by R1-R4, Sblk2 -> svar, spectralZ/M -> zt/mE; token diff of the signatures)
RBM2D public declarations (FlucAvg+LDE): 44 | RBM3D file public declarations: 64
identical after renaming (40) ; dropped: none
added (public in RBM3D only, 20) (instances in b.4 and one corollary LDE_norm_flucAvg_le_of_boundedWeight)
different after renaming (4); token diff (- RBM2D renamed, + RBM3D):
  card_blockAvg_support: - [(blk] [k.1, blk (sz.L n) (sz.W n) k.2)] [2]  ==>  + [(split d] [k).1] [d]
  card_Sblk_support: - [(blk] [i.1, blk] [i.2) - (blk (sz.L n) (sz.W n) j.1, blk (sz.L n) (sz.W n) j.2)] [sbSupport] [5] [2]  ==>  + [(split d] [j).1 - (split d] [i).1] [flucVanish_sbSupport d] [(2 * d + 1)] [d]
  Sblk_diag_pos: - [{L] [] [Sblk2] []  ==>  + [{d L] [(g : ℝ)] [svar d] [g]
  Sblk2_diag_eq: - [{L] [] [Sblk2] [] [1 / (5 * (W] [2)]  ==>  + [{d L] [(g : ℝ)] [svar d] [g] [((W] [d)⁻¹ * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹]
### b.6 The d = 2 tokens of the two sources (ST1-COMMON item 2): code lines (not docstrings) before the private `Checks` section, and their replacement
$ python3 tokens.py   # tokens: W^2, W², W⁻², L², Z2, zdist2, 1/5, 5*W, sq, d = 2 
RBM2D FlucAvg (code, before section Checks at line 411):
  357: theorem card_blockAvg_support (d : Sizes) (n : ℕ) (a : Z2 (d.L n)) :
  369: = 5 * d.W n ^ 2 :=
  376: rw [Sizes.size, sq]
  377: simp [Idx, Z2, Fintype.card_prod, ZMod.card]
  381: Fintype.card (Z2 (d.L n)) ≤ d.size n := by
  384: rw [Sizes.size, sq]
  385: simp only [Z2, Fintype.card_prod, ZMod.card]
RBM2D LDE (code, before section Checks at line 722):
  568: have hm : (0 : Z2 L) ∈ sbSupport L := by
  570: have h0 : sbKre2 L (i.1 - i.1) = 1 / 5 := by
  577: Sblk2 L W i i = 1 / (5 * (W : ℝ) ^ 2) := by
  578: have hm : (0 : Z2 L) ∈ sbSupport L := by
  580: have h0 : sbKre2 L (i.1 - i.1) = 1 / 5 := by
replacements in RBM3D/Green/LDE.lean (grep -n):
423:      = (2 * d + 1) * sz.W n ^ d :=
430:  Sizes.card_Idx sz n
435:    Fintype.card (Zd d (sz.L n)) ≤ sz.size n := by
437:  have h : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by
440:  exact Nat.pow_le_pow_left hLW d
1009:  simp [svar, SBR, sbKernelR]
1092:  rw [card_BlockIndex, Real.rpow_one, Sizes.size, mul_comm (sz.W n)]
(`1/5` and `5` of `sbKre2`/`sbSupport` -> `sbKernelR d L g 0 = (1+2dg²)⁻¹`, `flucVanish_sbSupport` (2d+1 points); `Z2 L` -> `Zd d L`; `sq` -> `Nat.pow_le_pow_left`/`Sizes.card_Idx`; the `‖·‖ ^ 2` of the sources are absolute squares, dimension-free.)
### b.7 Name-clash grep of the new public names
$ declaration lines `theorem|lemma|def|structure|abbrev|inductive|instance NAME` for the 45 public names of namespace RBM.Green, in RBM3D/ of the worktree (main at e84e0f7) and in every branch `git branch --no-merged main | grep t/` except t/T2078
$ clash.sh   # (grep -E of the declaration lines above)
worktree (main e84e0f7 + this branch) hits: 0 ; other unmerged t/* branches: 76 searched, 0 hits
### b.8 Registry pre-check (ST1-COMMON item 8): `import RBM3D`, `import RBM3D.Green.LDE`, `#assert_rbm_axioms`
$ lake env lean precheck.lean > precheck.out; echo $?  /  same file without the LDE import (precheck_base.lean) -> diff of the two outputs
exit 0 ; axiom audit: 2607 theorems, 1076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
99:premises found by scanning: 83 (borrowed 2, owed 67, structural 14).
1c1
< axiom audit: 2540 theorems, 1073 definitions, 0 axioms in `RBM` 
---
> axiom audit: 2607 theorems, 1076 definitions, 0 axioms in `RBM` 
=> no new premise in the scan, no unclassified premise; no line appended to RBM3D/Test/Axioms.lean (not touched by this commit).
### b.9 Port provenance
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf ; ... log -1 --format=%h (HEAD)
c9a24cf ; HEAD 9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/FlucAvg.lean RBM2D/Green/LDE.lean | tail -3
 RBM2D/Green/FlucAvg.lean | 187 +++++------------------------------------------
 RBM2D/Green/LDE.lean     | 145 +++---------------------------------
 2 files changed, 32 insertions(+), 300 deletions(-)
$ git -C ../RBM2D --no-optional-locks diff c9a24cf HEAD -- RBM2D/Green/FlucAvg.lean RBM2D/Green/LDE.lean | grep -E "^[-+](theorem|lemma|def|structure|noncomputable def|abbrev) [A-Za-z_]" | cut -c1-60   # public declarations removed (-) or added (+) at HEAD
-theorem Sblk2_diag_eq {L W : ℕ} [NeZero L] [NeZero W] (i : 
$ git -C ../RBM2D --no-optional-locks diff c9a24cf HEAD -- RBM2D/Green/FlucAvg.lean RBM2D/Green/LDE.lean | grep -cE "^-private (theorem|def)"   # private declarations removed at HEAD (the Checks sections)
17
(RBM2D HEAD deleted `Sblk2_diag_eq` as dead code (T2274); it is ported here because the ticket pins c9a24cf and lists it; the sources read are `git -C ../RBM2D show c9a24cf:RBM2D/Green/{FlucAvg,LDE}.lean`; RBM1D was not read.)


### b.10 Narrative (facts as in b.1-b.9 and the file)

* `RBM3D/Green/LDE.lean` (1404 lines, commit `df28c0e` on `t/T2078`, only file in the diff) ports all 44 public declarations of RBM2D `Green/FlucAvg` and `Green/LDE` at `c9a24cf` (b.5): 40 have the RBM2D signature after R1-R4, `Sblk2 -> svar`, `spectralZ/M -> zt/mE`; 4 change (`card_blockAvg_support`, `card_Sblk_support`, `Sblk_diag_pos`, `Sblk2_diag_eq`); none is dropped; one corollary is added (`LDE_norm_flucAvg_le_of_boundedWeight`).
* The conclusions of `stochDom_ldeRow`, `stochDom_ldeCol`, `stochDom_normSq_Hflow_diag` are, after whitespace normalisation, the text of the hypotheses `hLrow`, `hLcol`, `hLdiag` of `diag_bound_stochDom` (b.3, `pincmp.py`); the first two also feed `entry_bound_stochDom` in the `example` of b.4.
* Reused from the merged files, not copied: `condRow`, `rowSplit`, `flucDiag*`, `greenMinorMat`, `BoundedWeight`, `flucVanish_card_*` (FlucVanish); `zt_im_ne_zero`, `OffPair`, `PrecPT` pins (EntryDom); `stochDom_rowSum_generalTime`, `minorCol`, `minorRowConj`, `eventually_card_LdeIdx_le` (RowIndep); `norm_Gsig_le_inv_eta`, `norm_matrix_entry_le_opNorm`, `isUnit_sub_smul_of_isHermitian`. Copied as private helpers: the Gaussian even-moment lemmas (RowIndep:89-160) and the matrix-inverse measurability (both private in RowIndep), `Gres H z true = green H z` (public as `cont_Gres_true_eq_green` in `Induction/ContinuityNet`, not imported), and `LDE_greenBlk_true` (EntryDom's `entryDom_greenBlk_true_eq` is private).
* Uniform weights: neither source takes `UniformWeight` in any declaration (docstrings only, section (a)); no step needs `t = c`. The bounded-weight reading is the corollary `LDE_norm_flucAvg_le_of_boundedWeight` (only `∑ t ≤ 1`), applied to the row `j ↦ S_{0j}` at `sz0` in `norm_flucAvg_le_boundedWeight_sz0`.
* `d`-dimensional constants: counts `W^d`, `(2d+1) W^d`, `#Idx = (W L)^d = size n`, `#Zd d L = L^d ≤ size n`; the diagonal profile `W^{-d}(1+2dg²)⁻¹ > 0` for every real `g`; the moment constant of `stochDom_normSq_Hflow_diag` is `RowIndep_dfac (2p) + 1 = (4p-1)!! + 1`, with no `d`, `W`, `L`, `g` in it; the index-set exponents are `Ccard = 1` (`#Vtx = N`, `eventually_card_Idx_le`) and `2` (`#LdeIdx ≤ N²`). No `#A` dependence enters these targets.
* DECISIONS §29 for `eventually_le_W`: it is `∀ᶠ n`, from `SizeTendsto` and `Bandwidth c`, `0 < c`; no constant depends on `W`, `L`, `lam`; no hypothesis relates `lam` to `L`; `L^d ≤ W^K` is not used; time sequences are `0 ≤ t n < 1` as stated.
* Instances (b.4): every deterministic hypothesis is discharged at `sz0` (`d = 3`), `E ≡ 0`, `κ = 1`, `t ≡ 1/2`; `SizeTendsto` and `Bandwidth (1/6)` are the merged `sz0_tendsto`, `sz0_bandwidth`; the `GiiOmegaSeq` example keeps `hLquad` (S1-12..S1-19) as its only hypothesis. `integral_norm_Hflow_diag_pow_szT` reproduces the preflight sample (`d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `u = 1/2`): `S_xx = 1/20`, `E|H_xx|^4 = 3/1600`.
* Registry: no new premise appears in the scan (b.8) and `RBM3D/Test/Axioms.lean` is not modified. Axioms: only `propext`, `Classical.choice`, `Quot.sound` (b.2); no `sorry`, `admit`, `native_decide`, declared `axiom` (b.1).

## (c) Verified Mathlib names used (each by `#check @name` in `lake env lean`, exit 0; `lake env lean mathlibcheck.lean`)

* `Matrix.inv_def`
* `Ring.inverse_eq_inv'`
* `Continuous.matrix_det`
* `Continuous.matrix_adjugate`
* `Matrix.measurable_iff`
* `MeasureTheory.StronglyMeasurable.integral_prod_right'`
* `Finset.measurable_sum`
* `Filter.tendsto_atTop_mono'`
* `tendsto_rpow_atTop`
* `tendsto_natCast_atTop_iff`
* `Nat.pow_le_pow_left`
* `Nat.le_mul_of_pos_left`
* `Matrix.inv_submatrix_equiv`
* `Matrix.nonsing_inv_eq_ringInverse`
* `dotProduct_single_one`
* `dotProduct_star_self_nonneg`
* `Matrix.dotProduct_star_self_pos_iff`
* `Matrix.IsHermitian.im_star_dotProduct_mulVec_self`
* `ProbabilityTheory.memLp_id_gaussianReal'`
* `ProbabilityTheory.gaussianReal_of_var_ne_zero`
* `MeasureTheory.integrable_withDensity_iff_integrable_smul'`
* `ProbabilityTheory.measurable_gaussianPDF`
* `ProbabilityTheory.gaussianPDF_lt_top`
* `ProbabilityTheory.gaussianPDF_def`
* `ProbabilityTheory.gaussianPDFReal_nonneg`
* `ProbabilityTheory.gaussianReal_zero_var`
* `MeasureTheory.integral_dirac`
* `hasDerivAt_pow`
* `MeasureTheory.integral_map`
* `MeasureTheory.integrable_map_measure`
* `measurable_pi_apply`
* `pow_le_one₀`
* `Real.one_le_rpow`
* `le_mul_of_one_le_left`
* `Real.sq_sqrt`
* `Real.sqrt_sq_eq_abs`
* `Real.sqrt_pos`
* `Real.mul_self_sqrt`
* `inv_mul_le_iff₀`
* `Real.rpow_add`
* `Complex.norm_conj`
* `Complex.norm_real`
* `Matrix.mulVec_mulVec`
* `Finset.sum_subtype`
* `Finset.sum_equiv`
* `ite_true`
* `if_true`: **deprecated** at this Mathlib ("Use `ite_true` instead"); `ite_true` used.

## (d) Open issues and paper-delta candidates

* `T2078a` (card_Sblk_support): the row support is `{j : blk j - blk i ∈ flucVanish_sbSupport d L}` (orientation of `boundedWeight_svarF`; RBM2D: `blk i - blk j ∈ sbSupport`, the same set since `sbSupport` is symmetric) and its size is `(2d+1) W^d` (RBM2D: `5 W²`).
* `T2078b` (`Sblk2_diag_eq`, `Sblk_diag_pos`): `svar d L W g i i = W^{-d} (1 + 2 d g²)⁻¹`, positive for every real `g` (RBM2D: `1/(5 W²)`, no coupling).
* `T2078c` (addition, no RBM2D counterpart): `LDE_norm_flucAvg_le_of_boundedWeight`, the `BoundedWeight` form of `norm_flucAvg_le` (uses T2061a).
* Names kept from RBM2D although dimension-specific in spelling: `Sblk_diag_pos`, `Sblk2_diag_eq`, `flucAvg_card_Z2_le_size` (RBM2D consumer at `c9a24cf`: `Universality/GUEPhase/PathBounds.lean:128`); the dispatcher may rename them later. RBM2D HEAD deleted `Sblk2_diag_eq` (99d6fe0, T2274); at `c9a24cf` neither `Sblk2_diag_eq` nor `Sblk_diag_pos` has a consumer outside `LDE.lean` (`git grep` at `c9a24cf`), so `Sblk2_diag_eq` may be dropped by a later cleanup.
* `hLquad` (the quadratic-form large deviation input, `ldeQuad`) is not in this ticket; it is the only hypothesis of the `GiiOmegaSeq` example. The statements `isUnit_det_Hflow_sub`, `green_Hflow_diag_ne_zero` have the `z` of the section variable first, as RBM2D.
* No stop condition of the ticket was met: no step needed `t = c`, and every statement of the two sources has a `d`-dimensional form (the four that change are listed in b.5).
