Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 05:47:41 UTC 2026

Source: RBM2D `RBM2D/Green/IBPRem.lean` at `c9a24cf` (`git show`, lines 1-530 kept; the file has 886 lines with the private `Checks` section). Mathematics (all `d`-free): `ibpRem(i,k) = E_i[(G_ii-m)(G_kk-m)] + m(E_i(G_kk-m) - (G_kk-m))` (`ibpRem_eq_add`, merged `Green/IBP.lean:1344`, hypotheses `|E|<2`, `t<1`, no `0 ≤ t`, no `GaussIBP`); first summand `≺ Ψ²` (product of two entries of `G-m`, then `E_i` under an envelope); second `≺ Ψ²` for `k ≠ i` (minor replacement `|G_kk - G^{(i)}_kk| = |G_ki G_ik/G_ii| ≤ 2|G_ki||G_ik|` on `max|G-m| ≤ δ ≤ 1/2`, `G^{(i)}_kk` is `E_i`-invariant); on `k = i` only `≺ 1`.

### (i) Exponent table

| # | Quantity | Value / form at `d ≥ 3` | Constraint | Slack |
|---|---|---|---|---|
| 1 | scale `size n` (R3) | `sz.size n = (W_n L_n)^d`; every `size^τ`, `size^{-D}`, `size^{Kenv}`, `size^{-B}` of the file is the same power as in RBM2D | `PerTimeDomAt (seqP sz) sz.size` is the merged vocabulary (`CondDom.lean:381`) | none: no exponent of the file contains `d` |
| 2 | `d = 2` tokens of the source (portmap row 47: `d=2:1`, `Z2/zdist2:1`) | only docstrings: line 53 `Z2 (W L)`, lines 54 and 100 `size n = (W L)²`; the code has no `W²`, `L²`, `N²`, `1/5`, scale or `zdist` token (grep below) | replace `Z2 (W L)` by `Idx d (sz.L n) (sz.W n)`, `(W L)²` by `(W L)^d = sz.size n` | n/a |
| 3 | floor `hΨlow : size^{-B} ≤ Ψ²` | `B = 1` | from the pin floor `W^{-d/2} ≤ Ψ`, `Ψ ≥ 0`: `Ψ² ≥ W^{-d}`; `size = (W L)^d ≥ W^d` (`L ≥ 3`) so `size^{-1} = W^{-d} L^{-d} ≤ Ψ²` | factor `L^d ≥ 3^d = 27` at `d = 3` (instance: ratio 27, below); `B` free in the statements (`0 ≤ B`) |
| 4 | envelope `hEnv : (η_t⁻¹+1)² ≤ size^{Kenv}` | `Kenv = 3` at the consumer: `η_t = (zt E t).im ≥ size^{-1}` eventually (`eta_lower_of_rangeCond`, `LocalLaw.lean:917`, from `RangeCond δ t`) gives `(η⁻¹+1)² ≤ (size+1)² ≤ size^3` for `size ≥ 3` | `Kenv ≥ 0` | `d`-free; instance uses `Kenv = 1` (`η_t = 1/2`, env `= 9 ≤ size`) |
| 5 | `hΨ1 : Ψ² ≤ 1` (eventually) | from `Ψ ≤ size^{-a}`, `a > 0` (pin premise) | needed only by `ibpRem_diag`, `ibpRem` | `size^{-2a}` |
| 6 | `hδ1 : δ n ≤ 1/2` (eventually) | instance `δ = 1/4` | `|G_ii| ≥ 1 - δ ≥ 1/2` (`‖m‖ = 1`) gives the factor `2` of (4.9) | factor 2 |
| 7 | constants of (4.9) and `IBPRem_add` | `2` (minor: `1/|G_ii| ≤ 2`; sum: `ζ+ζ ≤ 2ζ`) | `d`-free | absorbed in `size^τ`, `τ > 0` |
| 8 | `hsize : size → ∞` | `Admissible` field `SizeTendsto`; needed by `perTimeCalc_*`, `perTimeDomAt_condRow_*` | all statements except `green_diag_sub`, `green_offdiag`, `greenDiagCentered_one` | `size_n = (3(n+2))^3` |
| 9 | `hd : 1 ≤ d` (`D200`) | enters only via merged `perTimeDomAt_of_le_left_on` (`CondDom.lean:401`, needs `3 ≤ size`) | propagate to `greenDiagCentered_sub_minor`, `condRow_greenDiagCentered_sub_self`, `ibpRem_offdiag`, `ibpRem` (4 theorems); NOT to `condRow_prod_green_diag`, `condExpDiag_one`, `ibpRem_diag`, `greenDiagCentered_one`, `green_*` | `d ≥ 3` at every consumer |
| 10 | `D201` `hd : 3 ≤ d` (`giiOmegaSeq`, `giiSeq_of_asGMc`) | not used by any statement here (`hll` is a hypothesis) | — | — |

Statements to port (RBM2D line at `c9a24cf`): `IBPRemOffPair` (98, `Idx d L W` pairs; the merged `OffPair` is over `Vtx`, `EntryDom.lean:678`), `perTimeDomAt_green_diag_sub` (142), `_green_offdiag` (155), `_prod_green_diag_sub` (169), `_condRow_prod_green_diag` (199), `_greenDiagCentered_sub_minor` (247), `_condRow_greenDiagCentered_sub_self` (280), `_ibpRem_offdiag` (351), `_greenDiagCentered_one` (386), `_condExpDiag_one` (408), `_ibpRem_diag` (455), `_ibpRem` (503). Private there (stay private, `IBPRem_` prefix): `one_le_size` (merged `sz.one_le_size`, no `hd`), `precomp`, `add`, `goodEvent`. Nothing dropped; the `Checks` section is replaced by the instances. Renames: R1 `d : Sizes` → `sz : Sizes d`; `spectralZ`/`spectralM` → `zt`/`mE`; `Sizes.seqHflow d n` → `Sizes.seqHflow sz n`; `ibpRem_eq_add` called without `gaussIBP`; `etaT`, `llErrMat`, `green` as merged.

**Floor check (ticket).** No statement takes the floor on `Ψ` as a hypothesis: they take `hΨ0 : 0 ≤ Ψ`, `hll : LocalLawDetSeq sz E t Ψ` (any `Ψ`) and `hΨlow` with free `B ≥ 0`. At `W^{-d/2} ≤ Ψ` the premise `hΨlow` holds with `B = 1` (row 3), so every statement holds as ported at the new floor and the consumer `IBPDetThm d` (S1-30, premise `∀ᶠ n, W^{-d/2} ≤ Ψ ∧ Ψ ≤ size^{-a}`, `LocalLaw.lean:186-195`) obtains `hΨlow`, `hΨ1`, `hΨ0` from its own premises. No statement needs the old floor `W^{-1} ≤ Ψ`: PASS.

**DECISIONS §29 items.** (1) time: `t n < 1` for all `n` (premise `∀ n, t n < 1` of `IBPDetThm`); `0 ≤ t` is not used by any statement (`ibpRem_eq_add` has `ht : t < 1` only); `s` does not exist (single time). (2) case (ii) boundary `1 - ilambda²/L²`: not used (the file has no `ilambda` or `L` condition; `lam` appears only inside the model). (3) `L`/`W` polynomial relation `L^d ≤ W^K`: used nowhere; the only `L`-dependence is `size = (W L)^d` through `size ≥ W^d` (row 3), valid for any `L ≥ 1`. (4) `∀ n` vs `∀ᶠ n`: `hE`, `ht1`, `hΨ0` are `∀ n` (same as the pin premises `∀ n, |E n| < 2 - κ`, `∀ n, t n < 1`, `∀ n, 0 ≤ Ψ n`); `hEnv`, `hΨlow`, `hΨ1`, `hδ1` are `∀ᶠ n`; `hsize` is `Tendsto`. No `∀ n` condition is imposed at finitely many `n` beyond what the pin gives.

Grep of `d = 2` tokens in the source code region (evidence for row 2):
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/IBPRem.lean | sed -n 1,530p | grep -nE "Z2|²|W \* L|zdist|1/5|ellT|Meta" | grep -vE "Ψ²|η_t⁻¹|\(G_ii - m\)²"
53:* The index is the fine lattice `Idx (d.L n) (d.W n) = Z2 (W L)`, on which `condRow`, `Hflow` and
54:  `greenMinorMat` live; `size n = (W L)²`.
100:/-- `1 ≤ size n` for every `Sizes` (`size n = (W L)² ≥ 1`). -/
```

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `L_n = 3`, `W_n = n+2` (`n = 0`: `L = 3`, `W = 2`, `size = 216`), `g = 1/2` (`lam n`), `E_n = 0` (`m = i`), `t_n = 1/2` (`η_t = (1-t) Im m = 1/2`), `Ψ_n = W_n^{-3/2}` (the floor itself), `δ_n = 1/4`, `Kenv = 1`, `B = 1`. Every deterministic hypothesis holds at every `n`; `hll`, `hΩ` stay hypotheses (other gates' pins, DECISIONS §70).
```
$ python3 scratchpad/T2114/instance_check.py   (exact Fractions; first lines of output)
n=    0 W=    2 size=216  env=9<=size  size^-1=4.630e-03 <= Psi^2=1.250e-01 (ratio 27)  ALL TRUE
n=    1 W=    3 size=729  env=9<=size  size^-1=1.372e-03 <= Psi^2=3.704e-02 (ratio 27)  ALL TRUE
n=    7 W=    9 size=19683  env=9<=size  size^-1=5.081e-05 <= Psi^2=1.372e-03 (ratio 27)  ALL TRUE
n=  100 W=  102 size=28652616  env=9<=size  size^-1=3.490e-08 <= Psi^2=9.423e-07 (ratio 27)  ALL TRUE
n=10000 W=10002 size=27016203240216  env=9<=size  size^-1=3.701e-14 <= Psi^2=9.994e-13 (ratio 27)  ALL TRUE
size_n -> infinity (hsize): size_n = (3(n+2))^3, monotone, size_{10^4} = 27016203240216
all deterministic hypotheses hold: True
floor check: (WL)^-d <= W^-d for d in 1..5 and sample (W,L): OK
(size+1)^2 <= size^3 for size>=3: True
```
(checked per `n`: `hE`, `ht1`, `hKenv`, `hB`, `hEnv`, `hΨlow`, `hΨ1`, `hδ1`, `hd`, `1 ≤ size`; at `n = 0` the window is `W = 2`, `L = 3`, 216 sites, no `N = 0`, nothing astronomically large.)

**External hypotheses, limit computation (TEAM §8 l.14).** `hll : LocalLawDetSeq sz E t Ψ` at `Ψ = W^{-3/2}` and `hΩ` at `δ = 1/4`. Model of `Gauss/FineModel.lean` (complex Hermitian `X`, `E|X_xy|² = S_xy = W^{-d} SB_ab`, `SB = a` same block, `g² a` at `ℓ¹` block distance 1, `a = (1+2dg²)⁻¹`; `H_t = √t X`), `d = 3`, `L = 3`, `g = 1/2`, `E = 0`, `t = 1/2`, `G = (H - z_t)⁻¹`, `z_t = i/2`:
```
$ python3 scratchpad/T2114/limit_check.py
W=1 N=  27  rms|G_ii-m|=0.5206  rms*W^{d/2}=0.5206  max|G-m|=0.8423  max/Psi=0.842  (Psi=W^-3/2=1.0000)
W=2 N= 216  rms|G_ii-m|=0.1888  rms*W^{d/2}=0.5340  max|G-m|=0.5008  max/Psi=1.416  (Psi=W^-3/2=0.3536)
W=3 N= 729  rms|G_ii-m|=0.1026  rms*W^{d/2}=0.5333  max|G-m|=0.3159  max/Psi=1.642  (Psi=W^-3/2=0.1925)
W=4 N=1728  rms|G_ii-m|=0.0664  rms*W^{d/2}=0.5314  max|G-m|=0.2380  max/Psi=1.904  (Psi=W^-3/2=0.1250)
```
`rms |G_ii - m| · W^{d/2}` is stable at ≈ 0.53 (so `|G_ii - m| ~ W^{-3/2}`, consistent with `Ψ ≥ W^{-d/2}`), `max|G-m|` is `≤ 1.9 Ψ` and its ratio to `Ψ` grows slowly (the maximum over `N²` entries: a `size^τ` factor), and `max|G-m| → 0` (0.84, 0.50, 0.32, 0.24), and its sample mean is `0.238 < 1/4` at `W = 4`; at `W = 2` the event `max|G-m| ≤ 1/2` holds in only 54.9 % of the samples of item (iii) below, so it is not yet typical there. This is a finite-size sanity check, not a proof of the pins (they are other gates').

### (iii) Numeric check of `ibpRem` (ticket item), `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `t = 1/2`
`ibpRem(i,k) = E_i[G_ii(G_kk - m)] - m(G_kk - m)`; `E_i` = mean over `M = 40` independent resamplings of row and column `i` (including the diagonal entry); 1000 outer samples; per sample one random `i` and one `k` in the support of `S_i·` (`k ≠ i`, "near", `S_ik > 0`), one `k` outside it ("far", `S_ik = 0`), and the diagonal `(i,i)`. `Ψ² = W^{-d} = 0.125`. The `E_i` is a 40-sample Monte Carlo mean (error `~ 0.15/√40`), so "max" below carries that noise.
```
$ python3 scratchpad/T2114/ibprem_check.py 1000 40
N = 216  row sums of S: min/max 1.0 1.0  S_ii = 0.05 = W^-d/(1+2dg^2) = 0.05
nonzero entries per row: 56 = (2d+1) W^d = 56
minor identity |G^(i)_kk - (G_kk - G_ki G_ik/G_ii)| = 1.3877787807814457e-17
samples 1000 inner 40  Psi = W^{-d/2} = 0.3535533905932738  Psi^2 = 0.12500000000000003  eta_t = 0.5
max_ij|G-m| per sample: mean 0.5012 max 0.6441  frac<=1/2: 0.549  frac<=Psi: 0.000
|ibpRem| near: mean 0.01195  max 0.10999  bound 0.1250  max/bound 0.8799  #exceed 0
|ibpRem| far : mean 0.00471  max 0.02793  bound 0.1250  max/bound 0.2235  #exceed 0
|ibpRem| diag: mean 0.16772  max 0.58997  bound 1.0000  max/bound 0.5900  #exceed 0
max |direct - decomposition| (ibpRem_eq_add, same inner samples): 1.2480669349684855e-16
max |direct - Schur form| (E_i G_kk = G^(i)_kk + E_i[G_ki G_ik/G_ii], same inner samples, exact identity): 2.270022877680131e-15
minor replacement on good event (max|G-m|<=1/2): n=1098, max |G_ki G_ik/G_ii| / (2|G_ki||G_ik|) = 0.6758 (<=1 required)
```
Reading: off the diagonal `|ibpRem| ≤ 0.110 < Ψ² = 0.125` (near) and `≤ 0.028` (far), on the diagonal `≤ 0.59 ≤ 1`; no sample exceeds its bound (the claim is `≺`, i.e. up to `size^τ`; at `size = 216` the check is a sanity check of the shape `Ψ²` vs `1`, not an asymptotic one). The identity `ibpRem_eq_add` and the minor replacement `≤ 2|G_ki||G_ik|` hold numerically. At `W = 2` the empirical `max|G-m|` (mean 0.50) is above `Ψ = 0.354`: the pin `hll` at `Ψ = W^{-3/2}` is an asymptotic statement (table above), not claimed at `W = 2`; this does not affect the deterministic reduction proved here.

### Verdicts
- All twelve declarations (`IBPRemOffPair` and the eleven `perTimeDomAt_*` of the ticket's list, including the endpoint `perTimeDomAt_ibpRem`, IBPRem:503): **PASS**. No statement is false at `d ≥ 3`; no exponent of the file depends on `d` beyond `size = (W L)^d`; the floor `W^{-d/2} ≤ Ψ` suffices (`hΨlow` with `B = 1`, slack `L^d`); the only `d`-dependence of hypotheses is `hd : 1 ≤ d` on four theorems (row 9, D200).
- Residual statement differences to list in the stage-1b report: `hd : 1 ≤ d` on `greenDiagCentered_sub_minor`, `condRow_greenDiagCentered_sub_self`, `ibpRem_offdiag`, `ibpRem` (D200, no new delta needed); `IBPRemOffPair` over `Idx d L W` (merged `OffPair` is over `Vtx`).

## (b) Script output

```
$ date -u
Sun Oct  4 06:03:45 UTC 2026
$ git log -1 --format="%h %s"; git status --short; wc -l RBM3D/Green/IBPRem.lean
0d5259a T2114: IBPRem header: cite the kept RBM2D line range
     815 RBM3D/Green/IBPRem.lean
$ git diff --stat main...t/T2114
 RBM3D/Green/IBPRem.lean | 815 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 815 insertions(+)
$ lake build RBM3D.Green.IBPRem 2>&1 | tail -1
Build completed successfully (3338 jobs).
$ lake env lean RBM3D/Green/IBPRem.lean; echo "exit=$?"    (fresh elaboration, no output)
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Green/IBPRem.lean; echo "grep exit=$?"
grep exit=1
$ lake build    (whole library incl. root #assert_rbm_axioms; run after the commit)
Build completed successfully (3857 jobs).
exit: 0
info: RBM3D.lean:156:0: axiom audit: 3371 theorems, 1222 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).

$ lake env lean scratchpad/T2114/registry_precheck.lean   (import RBM3D; import RBM3D.Green.IBPRem; #assert_rbm_axioms)
exit=0
axiom audit: 3383 theorems, 1223 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 83 (borrowed 2, owed 65, structural 16).
registry: 5 borrowed + 104 owed + 39 structural; 65 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,

$ #print axioms of every public target, of the floor lemma and of every instance (scratch copy of the file with the lines appended); grouped by axiom set
[Classical.choice,Quot.sound,propext]: 27 declarations
    (private) IBPRem_inst_green_diag_sub, (private) IBPRem_inst_green_offdiag, (private) IBPRem_inst_prod_green_diag_sub, (private) IBPRem_inst_condRow_prod_green_diag,
    (private) IBPRem_inst_greenDiagCentered_sub_minor, (private) IBPRem_inst_condRow_greenDiagCentered_sub_self, (private) IBPRem_inst_ibpRem_offdiag, (private)
    IBPRem_inst_greenDiagCentered_one, (private) IBPRem_inst_condExpDiag_one, (private) IBPRem_inst_ibpRem_diag, (private) IBPRem_inst_ibpRem, (private) IBPRemCk_hΩ,
    (private) IBPRemCk_hll, (private) IBPRemCk_offPair_nonempty, (private) IBPRemCk_hΨlow, IBPRem_hΨlow_of_floor, perTimeDomAt_green_diag_sub, perTimeDomAt_green_offdiag,
    perTimeDomAt_prod_green_diag_sub, perTimeDomAt_condRow_prod_green_diag, perTimeDomAt_greenDiagCentered_sub_minor, perTimeDomAt_condRow_greenDiagCentered_sub_self,
    perTimeDomAt_ibpRem_offdiag, perTimeDomAt_greenDiagCentered_one, perTimeDomAt_condExpDiag_one, perTimeDomAt_ibpRem_diag, perTimeDomAt_ibpRem

$ python3 scratchpad/T2114/stmt_diff.py
# RBM2D c9a24cf statement (renamed by R1-R3) vs RBM3D statement, whitespace-normalised, up to `:=`
IDENTICAL  IBPRemOffPair
IDENTICAL  perTimeDomAt_green_diag_sub
IDENTICAL  perTimeDomAt_green_offdiag
IDENTICAL  perTimeDomAt_prod_green_diag_sub
IDENTICAL  perTimeDomAt_condRow_prod_green_diag
DIFFERS    perTimeDomAt_greenDiagCentered_sub_minor
     insert old: -  | new: (hd : 1 ≤ d)  | at old tokens 2
DIFFERS    perTimeDomAt_condRow_greenDiagCentered_sub_self
     insert old: -  | new: (hd : 1 ≤ d)  | at old tokens 2
DIFFERS    perTimeDomAt_ibpRem_offdiag
     insert old: -  | new: (hd : 1 ≤ d)  | at old tokens 2
IDENTICAL  perTimeDomAt_greenDiagCentered_one
IDENTICAL  perTimeDomAt_condExpDiag_one
IDENTICAL  perTimeDomAt_ibpRem_diag
DIFFERS    perTimeDomAt_ibpRem
     insert old: -  | new: (hd : 1 ≤ d)  | at old tokens 2
$ python3 scratchpad/T2114/lines_map.py
# RBM2D c9a24cf line -> RBM3D line (declaration heads), and the private helpers
IBPRemOffPair 98->84 ; perTimeDomAt_green_diag_sub 142->153 ; perTimeDomAt_green_offdiag 155->166 ; perTimeDomAt_prod_green_diag_sub 169->180 ; perTimeDomAt_condRow_prod_green_diag 199->210 ; perTimeDomAt_greenDiagCentered_sub_minor 247->258 ; perTimeDomAt_condRow_greenDiagCentered_sub_self 280->291 ; perTimeDomAt_ibpRem_offdiag 351->362 ; perTimeDomAt_greenDiagCentered_one 386->397 ; perTimeDomAt_condExpDiag_one 408->419 ; perTimeDomAt_ibpRem_diag 455->466 ; perTimeDomAt_ibpRem 503->514
private: IBPRem_precomp 108->87 ; IBPRem_add 118->97 ; IBPRem_goodEvent 129->113 ; IBPRem_Gres_true new at 106 ; IBPRem_one_le_size 101 -> merged Sizes.one_le_size
```

Target statements, extracted from `RBM3D/Green/IBPRem.lean` by `python3 scratchpad/T2114/extract_stmts.py` (line: statement up to `:=`; `section` variables `{d : ℕ} {sz : Sizes d} {E t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}`):

```
84: abbrev IBPRemOffPair (d L W : ℕ) : Type := {p : Idx d L W × Idx d L W // p.1 ≠ p.2}
126: theorem IBPRem_hΨlow_of_floor {d : ℕ} (sz : Sizes d) (n : ℕ) {Ψ : ℝ} (hfloor : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ Ψ * Ψ
153: theorem perTimeDomAt_green_diag_sub (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n)) (fun n i ω => ‖green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) i i - mE (E n)‖) (fun n _ _ => Ψ n)
166: theorem perTimeDomAt_green_offdiag (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n)) (fun n v ω => ‖green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) v.1.1 v.1.2‖) (fun n _ _ => Ψ n)
180: theorem perTimeDomAt_prod_green_diag_sub (hsize : Tendsto sz.size atTop atTop) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q ω => ‖(green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) q.1 q.1 - mE (E n)) * (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) q.2 q.2 - mE (E n))‖) (fun n _ _ => Ψ n * Ψ n)
210: theorem perTimeDomAt_condRow_prod_green_diag (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B) (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv) (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q ω => ‖condRow sz n q.1 (fun η => (green (Sizes.seqHflow sz n (t n) η) (zt (E n) (t n)) q.1 q.1 - mE (E n)) * (green (Sizes.seqHflow sz n (t n) η) (zt (E n) (t n)) q.2 q.2 - mE (E n))) ω‖) (fun n _ _ => Ψ n * Ψ n)
258: theorem perTimeDomAt_greenDiagCentered_sub_minor (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n)) (fun n v ω => ‖greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2 ω - greenMinorDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖) (fun n _ _ => Ψ n * Ψ n)
291: theorem perTimeDomAt_condRow_greenDiagCentered_sub_self (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B) (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv) (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n) (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n)) (fun n v ω => ‖condRow sz n v.1.1 (greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2) ω - greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2 ω‖) (fun n _ _ => Ψ n * Ψ n)
362: theorem perTimeDomAt_ibpRem_offdiag (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B) (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv) (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n) (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n)) (fun n v ω => ‖ibpRem sz n (E n) (t n) (v.1.1, v.1.2) ω‖) (fun n _ _ => Ψ n * Ψ n)
397: theorem perTimeDomAt_greenDiagCentered_one {V : ℕ → Type*} (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) (kk : ∀ n, V n → Idx d (sz.L n) (sz.W n)) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := V) (fun n a ω => ‖greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) (kk n a) ω‖) (fun _ _ _ => (1 : ℝ))
419: theorem perTimeDomAt_condExpDiag_one (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B) (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv) (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n)) (fun n i ω => ‖condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω‖) (fun _ _ _ => (1 : ℝ))
466: theorem perTimeDomAt_ibpRem_diag (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B) (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv) (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n) (hΨ1 : ∀ᶠ n : ℕ in atTop, Ψ n * Ψ n ≤ 1) (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n)) (fun n i ω => ‖ibpRem sz n (E n) (t n) (i, i) ω‖) (fun _ _ _ => (1 : ℝ))
514: theorem perTimeDomAt_ibpRem (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B) (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv) (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n) (hΨ1 : ∀ᶠ n : ℕ in atTop, Ψ n * Ψ n ≤ 1) (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2) (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) (hll : LocalLawDetSeq sz E t Ψ) : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q ω => ‖ibpRem sz n (E n) (t n) q ω‖) (fun n q _ => if q.1 = q.2 then (1 : ℝ) else Ψ n * Ψ n)
```

The compiled nonempty instance of the endpoint (`d = 3`, `sz0`, `E = 0`, `t = 1/2`, `Ψ = W^{-3/2}`, `δ = 1/4`, `Kenv = B = 1`; every deterministic hypothesis discharged; the only hypothesis is `(asGMc)` at `c = 3/2`).  The other ten targets have the same-shaped instances `IBPRem_inst_*` (list below), `IBPRemOffPair` has `IBPRemCk_offPair_nonempty`, the floor lemma is applied in `IBPRemCk_hΨlow`:

```
802: private theorem IBPRem_inst_ibpRem
803:     (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
804:     PerTimeDomAt (Sizes.seqP sz0) sz0.size
805:       (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
806:       (fun n q ω => ‖ibpRem sz0 n (IBPRemCkE n) (IBPRemCkT n) q ω‖)
807:       (fun n q _ => if q.1 = q.2 then (1 : ℝ) else IBPRemCkPsi n * IBPRemCkPsi n) :=
808:   perTimeDomAt_ibpRem (δ := IBPRemCkDelta) (Kenv := 1) (B := 1) (by norm_num) tendsto_sz0_size IBPRemCk_hE
809:     IBPRemCk_ht1 IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hΨlow IBPRemCk_hΨ1
810:     IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)
$ grep -oE "^private theorem (IBPRem_inst_|IBPRemCk_(hΩ|hll|offPair_nonempty|hΨlow|hEnv))[A-Za-z_Ωψ]*" RBM3D/Green/IBPRem.lean | sed "s/private theorem //" | tr "
" " "
IBPRemCk_hΨlow IBPRemCk_hEnv IBPRemCk_offPair_nonempty IBPRemCk_hll IBPRemCk_hΩ IBPRem_inst_green_diag_sub IBPRem_inst_green_offdiag IBPRem_inst_prod_green_diag_sub IBPRem_inst_condRow_prod_green_diag IBPRem_inst_greenDiagCentered_sub_minor IBPRem_inst_condRow_greenDiagCentered_sub_self IBPRem_inst_ibpRem_offdiag IBPRem_inst_greenDiagCentered_one IBPRem_inst_condExpDiag_one IBPRem_inst_ibpRem_diag IBPRem_inst_ibpRem 
```

```
$ name-clash grep of every new public/private name against main (git grep on commit, and the main worktree files)
main = 778bdf7
git grep exit=1 (1 = no match)
grep exit=1 (1 = no match)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf ; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/IBPRem.lean
c9a24cf
 RBM2D/Green/IBPRem.lean | 476 ++++++------------------------------------------
 1 file changed, 52 insertions(+), 424 deletions(-)
(RBM2D HEAD is ahead of the pinned port source c9a24cf for this file; the port is from c9a24cf as the ticket says.)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h HEAD
9e0f275
```

### Narrative

* **Result.** `RBM3D/Green/IBPRem.lean` (815 lines, branch `t/T2114`, commits `d3f1055` and `0d5259a`) ports RBM2D `Green/IBPRem.lean` at `c9a24cf`, lines 1-528 (up to `end Whole`); the `Checks` part (531-886) is replaced by the instances at the end of the file. All twelve declarations of the ticket list are ported, none dropped: `IBPRemOffPair` and the eleven `perTimeDomAt_*`, endpoint `perTimeDomAt_ibpRem` (RBM2D `IBPRem:503`, here 514).
* **Statements.** The diff above: eight are identical to RBM2D's after R1-R3; four carry one inserted hypothesis `(hd : 1 ≤ d)`. This is D200: the merged `perTimeDomAt_of_le_left_on` (`CondDom.lean:401`) needs `3 ≤ size`; `perTimeDomAt_greenDiagCentered_sub_minor` calls it, and `_condRow_greenDiagCentered_sub_self`, `_ibpRem_offdiag`, `_ibpRem` use that one (exactly the four of (a), row 9). `d ≥ 3` (D201) is not needed anywhere. The other seven statements have no `hd`.
* **`d = 3` exponents (ST1-COMMON item 2).** No exponent of any statement contains `d`: each power of `N` is a power of `sz.size n = (W L)^d` (R3); `Kenv`, `B`, `τ` are free reals. The portmap tokens `d=2:1` and `Z2/zdist2:1` are the two docstring phrases at RBM2D lines 51 and 53 (grep in (a)); the header of this file replaces them. No `W^2`, `L^2`, `N^2`, `1/5`, `ellT`, `scal` token occurs in the file.
* **Floor check (ticket).** No statement takes a floor on `Ψ`; the floor enters only as `hΨlow : size^{-B} ≤ Ψ²` with `B ≥ 0` free. New public `IBPRem_hΨlow_of_floor` proves, for every `d` and `n`, that `W^{-d/2} ≤ Ψ` gives `size^{-1} ≤ Ψ²` (`size = (W L)^d ≥ W^d`). So every statement holds at the floor of T2108 (D213); the old floor `W⁻¹ ≤ Ψ` is not used. No stop condition of the ticket occurred.
* **Other differences.** `ibpRem_eq_add` is called without `gaussIBP`. `IBPRem_one_le_size` is the merged `Sizes.one_le_size`. New private `IBPRem_Gres_true` (`Gres H z true = green H z`): `llErrMat` is stated through the merged `Gres`, the entries of this file through `green`. `IBPRemOffPair d L W` is over the fine index `Idx d L W` (merged `OffPair` is over `Vtx`). `IBPRem_precomp`, `IBPRem_add`, `IBPRem_goodEvent` stay private.
* **Instances.** Every target has a compiled nonempty instance at `d = 3` (private `IBPRem_inst_*`; `IBPRemCk_offPair_nonempty` for `IBPRemOffPair`; the floor lemma is applied in `IBPRemCk_hΨlow`). The data are at `sz0` of `Defs/Sizes.lean` (`L = 4(n+1)`, `W = (2(n+1))^5`, `size 0 = 2097152`; ST1-COMMON item 7), not at the (a)(ii) sequence `L = 3`, `W = n+2`; the other data are those of (a): `E = 0`, `t = 1/2`, `δ = 1/4`, `Kenv = B = 1`, `Ψ = W^{-3/2}` (the floor). The rows 3-6 of (a)(i) (floor, envelope `9 ≤ size`, `Ψ² ≤ 1`, `δ ≤ 1/2`) are proved in Lean at `sz0` for every `n`. Every deterministic hypothesis (`hd`, `hsize`, `hE`, `ht1`, `hΨ0`, `hKenv`, `hB`, `hEnv`, `hΨlow`, `hΨ1`, `hδ1`) is discharged; the single hypothesis of each instance is `AsGMcSeq sz0 E t (3/2)` (`(asGMc)`, another gate's pin). `hll` is its `asGMcSeq_iff` form; `hΩ` is derived from it by the merged `entryDom_goodSet_highProb_of_asGMc` (`W^{-3/4} ≤ 1/4` as `W ≥ 16`). The limit computation of this pin, at the data of (a)(ii), is in (a)(ii).
* **Gates.** The whole `lake build` is green but does not see the module (the root import is the hub's); the registry pre-check (`import RBM3D`, `import RBM3D.Green.IBPRem`, `#assert_rbm_axioms`) exits 0 with no unclassified premise, so `RBM3D/Test/Axioms.lean` is unchanged. Paper `3_5:33` (`(GavLGEX)`), `3_5:37`, `1_2:359` (`Main_DEL_COND`) are cited in the header.

## (c) Verified Mathlib names (`#check` in `scratchpad/T2114/mathlib_check.lean`, exit 0; names verified absent: none searched)

```
Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Matrix.nonsing_inv_eq_ringInverse : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing 
inv_le_one_of_one_le₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a 
one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀
inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [Mu
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
Real.rpow_le_rpow_of_nonpos : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Nat.pow_le_pow_left : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
Nat.le_mul_of_pos_right : ∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
exists_pair_ne : ∀ (α : Type u_1) [Nontrivial α], ∃ x y, x ≠ y
pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] 
Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
norm_mul : ∀ {α : Type u_1} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖
norm_add_le : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a + b‖ ≤ ‖a‖ + ‖b‖
norm_sub_le : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a - b‖ ≤ ‖a‖ + ‖b‖
```

## (d) Open issues and paper-delta candidates

* **Paper-delta candidates:** none new. `hd : 1 ≤ d` is D200 (named in the ticket). `hsize` is as in RBM2D (its header cites T2156a). The floor `W^{-d/2}` is D213 / T2108a.
* **Instance hypothesis.** The instances rest on `(asGMc)` at `c = 3/2` for `sz0` (`AsGMcSeq`, another gate's pin). By (a)(iii) the finite-size check at `W = 2` has `max|G-m|` above `Ψ = W^{-3/2}`: the pin is asymptotic, as (a) says; it does not affect the deterministic reduction proved here.
* **For S1-30 (`IBPDetThm d`).** This file takes `hΨ0`, `hΨlow`, `hΨ1`, `hEnv`, `hδ1`, `hΩ`, `hll` as hypotheses. The pin's premises give `hll`, `hΨ0`, the floor and `Ψ ≤ size^{-a}`; `hΨlow` then follows from `IBPRem_hΨlow_of_floor` (proved here). `hEnv` (cited in (a) row 4 from `eta_lower_of_rangeCond`), `hΨ1`, `hδ1` and the good event `hΩ` (from `‖G-m‖_max ≺ Ψ ≤ size^{-a}`) must be supplied by S1-30; they are not derived here (unverified leads, not claims).
