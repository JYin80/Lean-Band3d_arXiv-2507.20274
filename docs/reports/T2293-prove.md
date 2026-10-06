Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 12:07:26 UTC 2026 (`date -u` at start; scripts below run later the same session)

Scripts live in `<scratchpad>/T2293/` (`classify.py`, `inst.py`, `inst2.py`, `mc.py`; scratchpad = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`). Covers T2293 (UN-41) and T2293b (UN-42), as the ticket's preflight block says.

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| lattice exponent `d` | `d = 3` instance; `d` a parameter | `3 ≤ d` only via `mix_det (hd)`; law, tails, `Smix` need no `d ≥ 3` | none needed |
| `N = size n` | `(W L)^d` (`Defs/Sizes.lean:157`); `gueVar` diag `1/N`, `Smix` flat part `b/N` | `Σ_j Smix_ij = a+b` needs `N·(b/N) = b` | exact (script rows) |
| error scale in the pin | `W^{-d}` (RBM2D `W^{-2}`); `svarF` diag `W^{-d}(1+2dg²)⁻¹` | `W^{-d}` term is not needed: `T·maxLoopPM < llErr² ≤ mixCdet Φ² maxLoopPM ≤ T maxLoopPM` is already contradictory | `W^{-d} ≥ 0` is pure slack (T2293b) |
| coupling `g = sz.lam n`, `Λ = 𝔡⁻¹` | `sz0`: `lam n = (2(n+1))^{-6}` | `0 < g ≤ Λ` (only `mixEntry_det`, `mixEntry_union`), from `WO 𝔡`: `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` | `W^{-d/2+𝔡} > 0`; at `sz0`: `(2(n+1))^{-7} ≤ lam ≤ 1/64 ≤ 10 = 𝔡⁻¹` |
| `κ`, `E` | `κ = 1`, `E = 0` | `0 < κ`, `|E| ≤ 2-κ` (⇒ `κ ≤ 2`) | `|E| = 0 ≤ 1` |
| `mixC κ` | `√(2κ)/2 = 0.7071` at `κ=1` | `≤ Im mE E = √(4-E²)/2` (`EntryDet.lean`, `EntryDet_mixC_le_mE_im`) | `1 - 0.7071` at `E=0` |
| `mixDelta d Λ κ` | `min(1/2, 1/(2 mixK), mixC/2)`, `mixK = Kstab3·(1+1/gapK κ)` (`EntryDet.lean:619-626`); `Kstab3` is built from `Classical.choose` constants (`Stability.lean:212`) | `0 < mixDelta ≤ 1/2` (`mixDelta_pos`), `(d,Λ,κ)`-only, `u`-free and `L`-free | no numeric value exists; used only through `0 <` and `≤ 1/2` |
| `mixCdet d Λ κ` | `(2160 mixK²+162)(1+3/mixC)`; `≥ 12173.41` at `κ=1` (`mixK ≥ 1`) | `n`-free; `mixCdet Φ² ≤ T = N^τ` | `≤ N^{τ/2}` eventually (`eventually_le_rpow`) |
| `u = a+b` | `1/2` (all three mixtures); `3/4` in the `mix_det` instance | `0 < u < 1`, `a,b ≥ 0` | `min(u, 1-u) = 1/4` |
| `c₀`, `δ n` | `c₀ = 1/4`, `δ_n = N^{-1/4}` | `δ_n ≤ N^{-c₀}`; `N^{-c₀} ≤ mixDelta` eventually | equality for the first; second is the eventual threshold |
| `τ`, `D`, `n0` | `1/10`, `2`, `1` (`K n = 2 ≤ N^1`) | `K n ≤ N^{n0}` | `2 ≤ 2097152` at `n = 0` |
| `τ'` | `min(τ/4, c₀) = 1/40` | `τ' ≤ c₀` (for `36Φδ² ≤ 1`), `τ' ≤ τ/4` (`Φ² ≤ N^{τ/2}`) | `1/4 - 1/40`, `0` |
| `Φ = N^{τ'}` | `N^{1/40}` | `Φ ≥ 2` (`mixBad_tail`, `mixEntry_union`: eventually); `36Φδ² ≤ 36 N^{τ'-2c₀} ≤ 36 N^{-c₀} ≤ 1` needs `N^{c₀} ≥ 36` (`N ≥ 1679616`) | `N^{τ'-c₀}` factor; `Φ ≥ 2` needs `N ≥ 2^{40}` (fails at `n=0`, eventual) |
| `q` | `q = 239` | `D+n0+3 ≤ τ'(q+1)`: `6 ≤ 6` | equality at `q=239`; `q=240` has `6.025` |
| `Cq = mixCq q`; union bound | `(K+1)·4N²·Cq/Φ^{q+1} ≤ 2N^{n0}·4N²·Cq/N^{D+n0+3} = 8Cq/N^{D+1} ≤ N^{-D}` | `8 mixCq q ≤ N` | `log10(8 mixCq 239) = 1504.2` ⇒ `(n+1) ≥ 10^{83.2}` at `sz0` (eventual threshold only; no hypothesis is large) |
| tail Chebyshev constants | `hwConst q = ((2q+1)(4q+2))^{q+1}` (`IBPPoly.lean:721`): `hwConst 1 = 324`, `mixCq 1 = 5200` | quad: `lam > 0`; row/col: `Λ > 1`; diag: `Λ > 0`; `mixBad_tail`: `Λ ≥ 2`; `z.im ≠ 0` | at `Λ=lam=2, q=1` quad `81`, row/col `324` (trivial, ≥ 1), diag `0.736`; at `Λ=50`: `0.1296`, `5.6e-5`, `2.8e-11` |
| sizes `sz0` | `𝔠 = 1/6`, `𝔡 = 1/10`, `d = 3` | `Bandwidth 𝔠`: `N^{1/6} ≤ W` ⇔ `N ≤ W^6`; `WO 𝔡` exponent `-d/2+𝔡 = -7/5` | `N = 2^{21}(n+1)^{18} ≤ W^6 = 2^{30}(n+1)^{30}` |

**d-token count** (`:1-1525` of RBM2D `EntryTail.lean` at `c9a24cf`; `python3 classify.py` on the regex of the ticket):
```
CARRIER/vocab (import map) 79 | Kstab2/log 13 (all in :1237-1469, dropped) | LAT W^-2 10 [106,123,1123,1130,1141,1177,1181,1195,1203,1512]
LAT (WL)^2 6 [312,323,1011,1199,1216,1224] + :1020 (`Nn := (W*L)^2`, listed under "other") | scalar norm^2 21 | scalar Φ/δ/Λ ^2 17 | other ^2 44
```
`:1249` `(d.W n * d.L n)^2` is in the dropped `mixEntry_W_le_size`. The "other" class was inspected line by line (grep output above): `llErrMat … ^ 2`, `‖·‖ ^ 2`, `δ ^ 2`, `Φ ^ 2`, `mixK ^ 2`, outer `^ 2` of `4 * (…)^2` (pair count `N²`, kept), no further lattice exponent. The lattice hits are exactly the ticket's list (7 `(WL)^2` hits incl. `:1020`, 10 `W^{-2}` hits incl. docstrings `:106`, `:1123`).

### (ii) One concrete nondegenerate instance

**(ii-1) fixed-size data, `d=3, L=3, W=2` (`N=216`), `g=1`, `(a,b)=(1/4,1/4)`; profile, `MixProfOK`, tail constants, `mix_det` witness.** Command: `python3 inst.py`
```
N = 216  W^d = 8  svarF diag = 1/56 = W^-d(1+2dg^2)^-1 = 1/56
row sums svarF all =1: True
row sums Smix all = a+b = 1/2 : True
MixProfOK symm: True
MixProfOK off (sigRow=2*mixVar = Smix, x!=y): True
MixProfOK diag (mixVar(x,x)=Smix xx): True  Smix_ii = 17/3024 >0
hwConst 1 = 324  mixCq 1 = 5200
Lam=lam=2: quad bound hw/lam^(q+1)=81; row/col bound hw/((Lam-1)^2)^(q+1)=324; diag 2exp(-Lam/2)=0.7358
Lam=lam=50: quad bound hw/lam^(q+1)=0.1296; row/col bound hw/((Lam-1)^2)^(q+1)=5.62e-05; diag 2exp(-Lam/2)=2.778e-11
zeta= 0  rho=(u-S_ii)^2/sum_{k!=i}S_ik^2 (u^0) = 55.0
zeta= 1/2  rho=(u-S_ii)^2/sum_{k!=i}S_ik^2 (u^0) = 125.17642117054046
zeta= 1  rho=(u-S_ii)^2/sum_{k!=i}S_ik^2 (u^0) = 215.0
Phi= 2000 >= max rho: True ; 36*Phi*delta^2<=1 iff delta <= 0.003726779962499649
mixC(1)= 0.7071067811865476  gapK(1)= 1  mixCdet >= (2160+162)(1+3/mixC)= 12173.41167549098
u=1/100: llErr_diag=u/(1-u)=0.010101 (<= 0.0037268: False)
u=1/1000: llErr_diag=u/(1-u)=0.001001 (<= 0.0037268: True)
```
The script's lattice is `(block a ∈ Z_3^3, inner r ∈ Z_2^3)` with `svarF_ij = W^{-d}·sbKernelR(a_i - a_j)` (`Block.lean:74-76`: `(1+2dg²)⁻¹` at `0`, `g²(1+2dg²)⁻¹` at periodic `L¹` distance 1), `gvarF = svarF` (diag) or `svarF/2`, `gueVar = 1/N` (diag) or `1/(2N)` (`Pins.lean:61`), `sigRow v i k = 2 v(i,k,true)` (`AuxCarrier.lean:768`). Law identity (`mixSample_law`): coordinate variance of `√a ω₁ + √b ω₂` is `a gvarF + b gueVar = mixVar` (`AuxCarrier.lean:282`), also for `a=0` or `b=0` (`mixVar_zero_*`).

**`mix_det` witness (all hypotheses at once, deterministic part).** `d=3, L=3, W=2`, `E=0`, `κ=g=Λ=1`, `M = 0` (Hermitian), `u = a+b`: then `z = (1-u)i`, `G = i/(1-u)·I`, `m = i`, `llErrMat` diag `= u/(1-u)`, off-diag `0`; row/col LDE LHS `= 0`; `‖M_ii‖² = 0`; quad LHS `= ((u-S_ii)/(1-u))²`, quad RHS `= Σ_{k≠i}S_ik²/(1-u)²`, so the quad hypothesis is `(u-S_ii)² ≤ Φ Σ_{k≠i}S_ik²`, i.e. `Φ ≥ ρ(ζ)` with `ρ = 55, 125.2, 215` at `ζ = b/u = 0, 1/2, 1` (script). Choose `Φ = 256 ≥ 215`, `ζ` arbitrary, `δ = u/(1-u)`; remaining hypotheses: `36Φδ² ≤ 1 ⇔ δ ≤ 1/96`, and `δ ≤ mixDelta 3 1 1` (a positive constant, independent of `u`). **Limit computation:** `lim_{u→0+} u/(1-u) = 0 < min(1/96, mixDelta 3 1 1)`, so every `u ∈ (0, min(1/97, c*/(1+c*)))`, `c* = mixDelta 3 1 1`, is a witness (e.g. `u=1/200`: `δ = 0.005025 ≤ 1/96 = 0.010417`; `c*` has no numeric value, see table). Observation (not a statement defect): the ticket's `inst_mixEntry_det` takes `Φ = 1`, `δ = mixDelta/3`, `M` and the LDE inputs as variables; `M = 0` does **not** satisfy the quad input at `Φ = 1` (`ρ ≥ 55`), so the witness above needs `Φ ≥ 215`; with `M` a variable the example does not depend on this.

**(ii-2) sequence data for `gueEntryMix` (T2293b `inst_entryMix`) and the coupling window (iii).** Command: `python3 inst2.py`
```
n=0: L,W,size,lam = 4 32 2097152 1/64
Bandwidth(1/6) N<=W^6, n<3000: True ; WO(1/10): (2(n+1))^-7 <= lam n <= 10, n<3000: True ; exponent -d/2+dd = -1.4 =-7/5; W^(-7/5)=(2(n+1))^(5*(-7/5))
lam n <= 1/64 <= 10 all n; lam>0 all n; max lam = 0.015625
tau'=min(tau/4,c0)= 1/40 <= c0: True <= tau/4: True
least q with tau'(q+1) >= D+n0+3 = 239 : tau'(q+1)= 6 >= 6 True
K n =2 <= N^n0 (N=size 0 = 2097152 ) True
mixture 1/2 0 0<=a,b, u= 1/2 in (0,1): True
mixture 1/4 1/4 0<=a,b, u= 1/2 in (0,1): True
mixture 0 1/2 0<=a,b, u= 1/2 in (0,1): True
|E|<=2-kappa: True
N^{c0}>=36 at n=0 (N>=36^4=1679616): True ; N^{tau'}>=2 needs N>=2^40=1099511627776: n=0 fails (False)
log10(8 mixCq q) = 1504.2057333040489 ; size n = 2^21 (n+1)^18 =>  need (n+1) >= 10^83.2
```
Reading: every hypothesis of `gueEntryMix` (`sz0.Admissible (1/6) (1/10)` = `Defs/Sizes.lean:331`, `κ=1`, `E ≡ 0`, `n0=1`, `K ≡ 2`, three mixtures, `c₀=1/4`, `δ_n=N^{-1/4}≥0`, `τ=1/10`, `D=2`) holds numerically at the stated data; only the conclusion `∀ᶠ n` has an astronomically large threshold (`n+1 ≥ 10^{83.2}`, from `8 mixCq 239 ≤ N`), as in RBM2D. The coupling window (iii) holds for every `n`: `0 < lam n ≤ 1/64 ≤ 𝔡⁻¹ = 10`. (iv): `mixDelta d 𝔡⁻¹ κ`, `mixCdet d 𝔡⁻¹ κ` are `n`-free (`EntryDet.lean:619-629`; `Kstab3` has no `L`), so `N^{-c₀} ≤ mixDelta` and `mixCdet ≤ N^{τ/2}` are `eventually_le_rpow` (`Domination.lean:68`: `∀ᶠ N, C ≤ N^τ`) applied at `C = (mixDelta)⁻¹` resp. `C = mixCdet` with exponents `c₀`, `τ/2`.

**(ii-3) numeric check of the pinned event at `d = 3` (ticket item (ii)).** The dispatcher's script `t2293_mc.py` is not on disk (`find / -name t2293_mc.py` returned nothing), so `mc.py` was written here: `Z_{WL}^3`, `(L,W) ∈ {(3,2),(4,2),(3,3)}`, `H = √a X_band(g) + √b X_GUE` (entry variance `a svarF + b/N`), `g ∈ {0.5,1}`, `E ∈ {0,1}`, `u ∈ {0.3,0.6,0.9,0.97}`, `ζ ∈ {0,1/2,1}`, 8 samples (seed 2293), `G = (H - z)⁻¹`, `z = E + (1-u)m(E)`, `maxLoopPM = max_{a,b} W^{-2d} Σ_{x∈a,y∈b}|G_xy|²` (`Eblk = diag(W^{-d} 1_{[a]})`, `GLoop.lean:55`; `G(-) = G(+)*`). Command: `python3 mc.py 8`
```
cases total 1152 on a priori event 632 max ratio 2.763770256115404
(3, 2) N= 216 n_event 174 max 0.8353131627236922
(4, 2) N= 512 n_event 199 max 0.8724129951688687
(3, 3) N= 729 n_event 259 max 2.763770256115404
worst (3, 3, 0.5, 0.9, 1, 1.0, 2.76)   [L,W,g,u,zeta,E,ratio]
```
Ratio = `max_ij |G-mδ|²_ij/(maxLoopPM + W^{-3})` on the a priori event `‖G-m‖_max ≤ 1/2` (the event failed in the other 520 samples; `u` of the failures ∈ {0.3,…,0.97}). Worst `2.76 ≪ mixCdet·Φ² ≥ 12173` (`Φ ≥ 1`), consistent with the `O(1)` claim of the ticket (`≤ 2.75` there; `2.76` here, other sample set); no counterexample to the pinned event.

**Ticket items (vii)-(ix), one line each.** (vii) §29 items (1)-(7): as the ticket's lines (rows above give the numbers; `∀ᶠ` only in `gueEntryMix`). (viii) Consumers: UN-43 `gueEntryMix hd 𝔠 𝔡 sz hA κ …` and `(ouP (UNModel.band sz) n).map (mixMat sz n t₁ (u_k - t₁))` read off the check file's `T2293_ouP_mixSample_preimage`/`GUEEntryMixV`; UN-48 `mixEntry_greenBlk_eq` is `T2293_mixEntry_greenBlk_eq` (`greenBlk … true = (green M (zt E u)).submatrix …`, definitional in `Gres`/`blockMat`, `Gres` with `σ = true` uses `z`). (ix) Registry: no line expected per the ticket (`GUEEntryMix`, `MixProfOK` Prop-valued, not assumed unproved); not re-derived here.

### Verdicts

- **T2293 (UN-41): PASS.** No hypothesis set is empty: (ii-1) gives profile, `MixProfOK`, law identity and tail constants at `N = 216`; the `mix_det` hypotheses are jointly satisfiable (witness `M = 0`, `Φ ≥ 215`, `u` small; only unknown number is `mixDelta 3 1 1 > 0`, `u`-independent); every exponent in the table closes (`τ' ≤ c₀`, `τ' ≤ τ/4`, `6 ≤ 6`, `2τ' ≤ τ/2`). No statement is false at `d ≥ 3`; `ouMat_eq_mixMat` uses `√(exp(-t)) = exp(-t/2)` (true).
- **T2293b (UN-42): PASS** (same data): `sz0` admissible at `(1/6, 1/10)`, window `0 < lam ≤ 1/64 ≤ 10`, `q = 239`, all scalar hypotheses of `gueEntryMix` hold; the `∀ᶠ` threshold is eventual only.
- Observations for stage 1b (not blockers): (1) `inst_mixEntry_det` at `Φ = 1` leaves LDE inputs as variables; a discharged witness needs `Φ ≥ 215` (above). (2) Tails at `Λ = lam = 2, q = 1` have conclusion bounds `≥ 1` for quad/row/col (trivial); `Λ = 50` gives informative numbers. (3) `mixDelta`, `mixCdet`, `Kstab3` have no numeric value (`Classical.choose`), so numeric claims about them are only the bounds listed in the table.

## (b) Script output (scripts in `<scratchpad>/T2293/`; each block starts with its `date -u`; branch `t/T2293`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2293`, head `408c53a`)

### (b.1) commit, build, registry pre-check
```
$ date -u
Tue Oct  6 12:40:31 UTC 2026
$ git log --oneline -1 && git diff --stat main...t/T2293 && git status --short | wc -l   # (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2293)
408c53a T2293: instances of the index-generic helpers of EntryTail
 RBM3D/Universality/GUEPhase/EntryTail.lean | 1419 ++++++++++++++++++++++++++++
 1 file changed, 1419 insertions(+)
       0
$ wc -l RBM3D/Universality/GUEPhase/EntryTail.lean; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/EntryTail.lean
    1419 RBM3D/Universality/GUEPhase/EntryTail.lean
0
$ lake build RBM3D.Universality.GUEPhase.EntryTail 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3360 jobs).
$ lake env lean RBM3D/Universality/GUEPhase/EntryTail.lean ; echo exit=$?   # no warning lines from this file
exit=0
$ lake build 2>&1 | tail -1   # whole library as of main + this branch (root import added by the hub at merge)
Build completed successfully (4099 jobs).
$ cat registry.lean   # temporary, uncommitted
import RBM3D
import RBM3D.Universality.GUEPhase.EntryTail

#assert_rbm_axioms
$ lake env lean registry.lean > registry.out; echo exit=$?
exit=0
axiom audit: 8476 theorems, 2791 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ same file without the EntryTail import (baseline):
axiom audit: 8377 theorems, 2784 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ diff <(registry.out minus line 1) <(registry_base.out minus line 1) | wc -l   # premise ledger unchanged
       0
$ grep -c "GUEEntryMix\|MixProfOK\|EntryTail" registry.out
0
```

### (b.2) pin examples (scratch file importing the check file's definitions), axioms of the 102 public declarations
```
$ date -u
Tue Oct  6 12:41:22 UTC 2026
$ lake env lean pins.lean ; echo exit=$?   # pins.lean = import RBM3D + EntryTail, check file lines 145-328 copied verbatim (sed -n 145,328p), then the examples
exit=0
$ diff -B <(sed -n 145,328p docs/tickets/checks/T2293-check.lean) <(pins.lean from "## 2. Vocabulary" to before "### Examples") | wc -l   # definitions copied verbatim
       0
$ grep -c "^example" pins.lean; pin examples (names):
26
mixMat_isHermitian ouMat_eq_mixMat mixMat_zero_right mixMat_zero_left mixMat_eq_Xmat_mixSample measurable_mixSample measurable_mixMat mixSample_law ouP_mixSample_preimage mixEntry_mixVar_coe mixEntry_sigRow_gvarF mixEntry_sigRow_mixVar mixEntry_mixVar_diag mixEntry_Smix_diag_pos mixProfOK mixEntry_quad_tail mixEntry_row_tail mixEntry_col_tail mixEntry_diag_tail mixEntry_greenBlk_eq mixEntry_det 
$ vocabulary examples (rfl / Iff):
232:    RBM.Univ.MixProfOK v S ↔ MixProfOKV d L W v S :=
258:    RBM.Univ.mixMat sz n a b ω = mixMatV sz n a b ω := rfl
261:    RBM.Univ.mixSample sz n a b ω = mixSampleV sz n a b ω := rfl
262:example (d : ℕ) : RBM.Univ.GUEEntryMix d = GUEEntryMixV d := rfl
263:example (d : ℕ) : RBM.Univ.GUEEntryMix d ↔ GUEEntryMixV d := Iff.rfl
$ #print axioms of the 102 public declarations of EntryTail.lean (axioms.lean; names from the file by script)
exit=0
 101 [propext, Classical.choice, Quot.sound]
   1 [propext, Quot.sound]
'RBM.Univ.EntryTailCheck.inst_x1_ne' depends on axioms: [propext, Quot.sound]
targets:
mixMat: [propext, Classical.choice, Quot.sound];mixMat_isHermitian: [propext, Classical.choice, Quot.sound];ouMat_eq_mixMat: [propext, Classical.choice, Quot.sound];GUEEntryMix: [propext, Classical.choice, Quot.sound];mixSample_law: [propext, Classical.choice, Quot.sound];mixProfOK: [propext, Classical.choice, Quot.sound];mixEntry_quad_tail: [propext, Classical.choice, Quot.sound];mixEntry_row_tail: [propext, Classical.choice, Quot.sound];mixEntry_col_tail: [propext, Classical.choice, Quot.sound];mixEntry_diag_tail: [propext, Classical.choice, Quot.sound];mixEntry_greenBlk_eq: [propext, Classical.choice, Quot.sound];mixEntry_det: [propext, Classical.choice, Quot.sound];
```

### (b.3) target statements, extracted from `EntryTail.lean` by `extract.py` (namespace `RBM.Univ`; section variables `{d L W} [NeZero L] [NeZero W]` / `{d} (sz : Sizes d)`)
```
def mixMat (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := Real.sqrt a • Sizes.seqXmat sz n ω.1 + Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2
theorem mixMat_isHermitian (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : (mixMat sz n a b ω).IsHermitian
theorem ouMat_eq_mixMat (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMat (UNModel.band sz) n t ω = mixMat sz n (Real.exp (-t)) (1 - Real.exp (-t)) ω
theorem mixMat_zero_right (sz : Sizes d) (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : mixMat sz n a 0 ω = Real.sqrt a • Sizes.seqXmat sz n ω.1
theorem mixMat_zero_left (sz : Sizes d) (n : ℕ) (b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : mixMat sz n 0 b ω = Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2
def mixSample (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : Ω d (sz.L n) (sz.W n) := fun c => Real.sqrt a * Sizes.slice sz n ω.1 c + Real.sqrt b * ω.2 c
theorem measurable_mixSample (sz : Sizes d) (n : ℕ) (a b : ℝ) : Measurable (mixSample sz n a b)
theorem mixMat_eq_Xmat_mixSample (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : mixMat sz n a b ω = Xmat d (sz.L n) (sz.W n) (mixSample sz n a b ω)
theorem measurable_mixMat (sz : Sizes d) (n : ℕ) (a b : ℝ) : Measurable (mixMat sz n a b)
theorem mixSample_law (sz : Sizes d) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (ouP (UNModel.band sz) n).map (mixSample sz n a b) = gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (sz.lam n) a b)
theorem ouP_mixSample_preimage (sz : Sizes d) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {A : Set (Ω d (sz.L n) (sz.W n))} (hA : MeasurableSet A) : ouP (UNModel.band sz) n (mixSample sz n a b ⁻¹' A) = gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (sz.lam n) a b) A
theorem mixEntry_mixVar_coe (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : CoordF d L W) : (mixVar d L W g a b c : ℝ) = a * (gvarF d L W g c : ℝ) + b * (gueVar d L W c : ℝ)
theorem mixEntry_sigRow_gvarF (g : ℝ) {i k : Idx d L W} (hik : k ≠ i) : sigRow d L W (gvarF d L W g) i k = svarF d L W g i k
theorem mixEntry_sigRow_mixVar (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {i k : Idx d L W} (hik : k ≠ i) : sigRow d L W (mixVar d L W g a b) i k = Smix d L W g a b i k
theorem mixEntry_mixVar_diag (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Idx d L W) : (mixVar d L W g a b (i, i, true) : ℝ) = Smix d L W g a b i i
theorem mixEntry_Smix_diag_pos (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (i : Idx d L W) : 0 < Smix d L W g a b i i
structure MixProfOK (v : CoordF d L W → ℝ≥0) (S : Idx d L W → Idx d L W → ℝ) : Prop where symm : ∀ x y, S x y = S y x off : ∀ x y, x ≠ y → sigRow d L W v x y = S x y diag : ∀ x, (v (x, x, true) : ℝ) = S x x
theorem mixProfOK (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : MixProfOK (mixVar d L W g a b) (Smix d L W g a b)
theorem mixEntry_minor_eq {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : ν) (k l : {a : ν // a ≠ i}) : green (H.submatrix Subtype.val Subtype.val) z k l = greenMinor (green H z) i k.1 l.1
theorem mixEntry_quad_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ} (hv : TagFree d L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) : gaussLaw d L W v {s | lam * ldeQuadRHS S (green (Xmat d L W s) z) i < ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) S 1 i} ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1))
theorem mixEntry_row_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ} (hv : TagFree d L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) {i j : Idx d L W} (hij : i ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) : gaussLaw d L W v {s | Λ * ldeRowRHS S (green (Xmat d L W s) z) i j < ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) i j} ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1))
theorem mixEntry_col_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ} (hv : TagFree d L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) {k j : Idx d L W} (hkj : k ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) : gaussLaw d L W v {s | Λ * ldeColRHS S (green (Xmat d L W s) z) k j < ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) k j} ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1))
theorem mixEntry_diag_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ} (hS : MixProfOK v S) (i : Idx d L W) (hpos : 0 < S i i) {Λ : ℝ} (hΛ : 0 < Λ) : gaussLaw d L W v {s | Λ * S i i < ‖Xmat d L W s i i‖ ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-Λ / 2))
theorem mixEntry_greenBlk_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : greenBlk d L W E u M true = (green M (zt E u)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm
theorem mixEntry_det (hd : 3 ≤ d) (hL : 3 ≤ L) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1) {δ Φ : ℝ} (hllErr : ∀ x y, llErrMat d L W E (a + b) M x y ≤ δ) (hδ : δ ≤ mixDelta d Λ κ) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hrow : ∀ i j, i ≠ j → ldeRowLHS M (green M (zt E (a + b))) i j ≤ Φ * ldeRowRHS (Smix d L W g a b) (green M (zt E (a + b))) i j) (hcol : ∀ k j, k ≠ j → ldeColLHS M (green M (zt E (a + b))) k j ≤ Φ * ldeColRHS (Smix d L W g a b) (green M (zt E (a + b))) k j) (hquad : ∀ i, ldeQuadLHS M (green M (zt E (a + b))) (Smix d L W g a b) 1 i ≤ Φ * ldeQuadRHS (Smix d L W g a b) (green M (zt E (a + b))) i) (hdiag : ∀ i, ‖M i i‖ ^ 2 ≤ Φ * Smix d L W g a b i i) (i j : Idx d L W) : llErrMat d L W E (a + b) M i j ^ 2 ≤ mixCdet d Λ κ * Φ ^ 2 * maxLoopPM d L W E (a + b) M
def GUEEntryMix (d : ℕ) : Prop := ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ n0 : ℕ, ∀ K : ℕ → ℕ, (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ, (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) → ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) → (∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) → ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop, ouP (UNModel.band sz) n {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)), ((sz.size n : ℕ) : ℝ) ^ τ * (maxLoopPM d (sz.L n) (sz.W n) (E n) (a n k + b n k) (mixMat sz n (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) < (if ∀ x y, llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k) (mixMat sz n (a n k) (b n k) ω) x y ≤ δ n then llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k) (mixMat sz n (a n k) (b n k) ω) i j ^ 2 else 0)} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
```

### (b.4) compiled nonempty instances (namespace `RBM.Univ.EntryTailCheck`, `d = 3`, `L = 3`, `W = 2`, `g = 1`, `(a, b) = (1/4, 1/4)`; carrier ones at `sz0`, `n = 0`)
Names (all 60 are in the module build of (b.1)): `inst_zt_im inst_zt_im_ne inst_x1_ne inst_mixMat_isHermitian inst_ouMat_eq_mixMat inst_mixMat_zero_right inst_mixMat_zero_left inst_mixMat_eq_Xmat_mixSample inst_measurable_mixMat inst_mixSample_law inst_ouP_mixSample_preimage inst_mixEntry_mixVar_coe inst_mixEntry_sigRow_gvarF inst_mixEntry_sigRow_mixVar inst_mixEntry_mixVar_diag inst_mixEntry_Smix_diag_pos inst_mixProfOK inst_mixEntry_quad_tail inst_mixEntry_row_tail inst_mixEntry_col_tail inst_mixEntry_diag_tail inst_mixEntry_quad_tail_sharp inst_mixEntry_row_tail_sharp inst_mixEntry_col_tail_sharp inst_mixEntry_greenBlk_eq inst_mixEntry_det inst_measurable_mixSample inst_mixEntry_minor_eq inst_mixEntry_meas_Xmat inst_mixEntry_meas_green inst_mixEntry_meas_greenMinor inst_mixEntry_meas_ldeRowLHS inst_mixEntry_meas_ldeRowRHS inst_mixEntry_meas_ldeColLHS inst_mixEntry_meas_ldeColRHS inst_mixEntry_meas_ldeQuadLHS inst_mixEntry_meas_ldeQuadRHS inst_mixEntry_meas_diag inst_mixEntry_relabel_ldeRowLHS inst_mixEntry_relabel_ldeRowRHS inst_mixEntry_relabel_ldeColLHS inst_mixEntry_relabel_ldeColRHS inst_mixEntry_relabel_ldeQuadLHS inst_mixEntry_relabel_ldeQuadRHS inst_green_zero inst_greenMinor_zero inst_ldeRowLHS_zero inst_ldeColLHS_zero inst_ldeQuadLHS_zero inst_ldeQuadRHS_zero inst_quad_zero inst_mE_zero inst_zt_zero inst_zt_zero_ne inst_llErr_zero inst_det_zero instDelta instDelta_pos instU inst_mixEntry_det_full`.
Statements of the endpoint instances, extracted by script:
```
theorem inst_mixSample_law : (ouP (UNModel.band sz0) 0).map (mixSample sz0 0 (1 / 4) (1 / 4)) = gaussLaw 3 (sz0.L 0) (sz0.W 0) (mixVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 4) (1 / 4))
theorem inst_mixEntry_quad_tail : gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4)) {s | 2 * ldeQuadRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (0 : Idx 3 3 2) < ldeQuadLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (Smix 3 3 2 1 (1 / 4) (1 / 4)) 1 0} ≤ ENNReal.ofReal (hwConst 1 / 2 ^ (1 + 1))
theorem inst_mixEntry_row_tail : gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4)) {s | 2 * ldeRowRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) < ldeRowLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) 0 (![1, 0, 0] : Idx 3 3 2)} ≤ ENNReal.ofReal (hwConst 1 / ((2 - 1) ^ 2) ^ (1 + 1))
theorem inst_mixEntry_col_tail : gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4)) {s | 2 * ldeColRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (![1, 0, 0] : Idx 3 3 2) (0 : Idx 3 3 2) < ldeColLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (![1, 0, 0] : Idx 3 3 2) 0} ≤ ENNReal.ofReal (hwConst 1 / ((2 - 1) ^ 2) ^ (1 + 1))
theorem inst_mixEntry_diag_tail : gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4)) {s | 2 * Smix 3 3 2 1 (1 / 4) (1 / 4) (0 : Idx 3 3 2) 0 < ‖Xmat 3 3 2 s 0 0‖ ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-2 / 2))
theorem inst_mixEntry_greenBlk_eq : greenBlk 3 3 2 0 (1 / 2) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true = (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (1 / 2))).submatrix (splitEquiv 3 3 2).symm (splitEquiv 3 3 2).symm
theorem inst_mixEntry_det {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian) (hllErr : ∀ x y, llErrMat 3 3 2 0 (1 / 2 + 1 / 4) M x y ≤ mixDelta 3 1 1 / 3) (hrow : ∀ i j, i ≠ j → ldeRowLHS M (green M (zt 0 (1 / 2 + 1 / 4))) i j ≤ 1 * ldeRowRHS (Smix 3 3 2 1 (1 / 2) (1 / 4)) (green M (zt 0 (1 / 2 + 1 / 4))) i j) (hcol : ∀ k j, k ≠ j → ldeColLHS M (green M (zt 0 (1 / 2 + 1 / 4))) k j ≤ 1 * ldeColRHS (Smix 3 3 2 1 (1 / 2) (1 / 4)) (green M (zt 0 (1 / 2 + 1 / 4))) k j) (hquad : ∀ i, ldeQuadLHS M (green M (zt 0 (1 / 2 + 1 / 4))) (Smix 3 3 2 1 (1 / 2) (1 / 4)) 1 i ≤ 1 * ldeQuadRHS (Smix 3 3 2 1 (1 / 2) (1 / 4)) (green M (zt 0 (1 / 2 + 1 / 4))) i) (hdiag : ∀ i, ‖M i i‖ ^ 2 ≤ 1 * Smix 3 3 2 1 (1 / 2) (1 / 4) i i) (i j : Idx 3 3 2) : llErrMat 3 3 2 0 (1 / 2 + 1 / 4) M i j ^ 2 ≤ mixCdet 3 1 1 * 1 ^ 2 * maxLoopPM 3 3 2 0 (1 / 2 + 1 / 4) M
theorem inst_mixEntry_det_full (i j : Idx 3 3 2) : llErrMat 3 3 2 0 (instU / 2 + instU / 2) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) i j ^ 2 ≤ mixCdet 3 1 1 * 256 ^ 2 * maxLoopPM 3 3 2 0 (instU / 2 + instU / 2) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
```

### (b.5) name-clash grep, port citation, comparison with the source
```
$ date -u
Tue Oct  6 12:41:29 UTC 2026
$ clash.sh   # for each of the public names of EntryTail.lean: grep -rnw --include=*.lean NAME RBM3D | grep -v EntryTail.lean
public names checked: 102; names with a hit in RBM3D/ outside EntryTail.lean: 0; 'EntryTailCheck' hits outside: 0
names with a hit in docs/tickets/*.md (prose of tickets naming this ticket's targets, not code): mixMat mixMat_isHermitian ouMat_eq_mixMat mixMat_zero_right mixMat_zero_left GUEEntryMix mixSample measurable_mixSample mixMat_eq_Xmat_mixSample measurable_mixMat mixSample_law ouP_mixSample_preimage mixEntry_mixVar_coe mixEntry_sigRow_gvarF mixEntry_sigRow_mixVar mixEntry_mixVar_diag mixEntry_Smix_diag_pos MixProfOK mixProfOK mixEntry_minor_eq mixEntry_quad_tail mixEntry_row_tail mixEntry_col_tail mixEntry_diag_tail mixEntry_greenBlk_eq mixEntry_det inst_mixMat_isHermitian inst_ouMat_eq_mixMat inst_mixMat_zero_right inst_mixMat_zero_left inst_mixSample_law inst_mixEntry_sigRow_mixVar inst_mixEntry_Smix_diag_pos inst_mixProfOK inst_mixEntry_greenBlk_eq inst_mixEntry_det 
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   # RBM2D HEAD
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/EntryTail.lean
 RBM2D/Universality/GUEPhase/EntryTail.lean | 359 +++++++----------------------
 1 file changed, 85 insertions(+), 274 deletions(-)
$ python3 portcmp.py   # per-declaration comparison of source :1-874 (c9a24cf) with the port, tokens d/L/W/g dropped, renamings applied, comments stripped
identical (22): mixEntry_pair_map MixProfOK mixEntry_meas_Xmat mixEntry_meas_greenMinor mixEntry_meas_ldeRowLHS mixEntry_meas_ldeRowRHS mixEntry_meas_ldeColLHS mixEntry_meas_ldeColRHS mixEntry_meas_ldeQuadLHS mixEntry_meas_ldeQuadRHS mixEntry_meas_diag mixEntry_gaussianReal_ge_le mixEntry_gaussianReal_le_le mixEntry_gaussianReal_tail mixEntry_diag_tail mixEntry_erase_iff mixEntry_relabel_ldeRowLHS mixEntry_relabel_ldeRowRHS mixEntry_relabel_ldeColLHS mixEntry_relabel_ldeColRHS mixEntry_relabel_ldeQuadLHS mixEntry_relabel_ldeQuadRHS
differs (tokens differing/total; carrier, mix_det interface and A=0 edits): mixMat:28/31 mixMat_isHermitian:20/26 ouMat_eq_mixMat:19/55 mixMat_zero_right:18/26 mixMat_zero_left:19/26 GUEEntryMix:70/330 mixSample:20/29 measurable_mixSample:28/58 mixMat_eq_Xmat_mixSample:26/54 measurable_mixMat:29/59 mixSample_law:20/463 ouP_mixSample_preimage:30/50 mixEntry_mixVar_coe:3/51 mixEntry_sigRow_gvar:46/50 mixEntry_sigRow_mixVar:3/85 mixEntry_mixVar_diag:27/79 mixEntry_Smix_diag_pos:26/111 mixProfOK:3/40 mixEntry_minor_eq:1/136 mixEntry_meas_green:13/37 mixEntry_quad_tail:19/323 mixEntry_row_tail:91/632 mixEntry_col_tail:119/754 mixEntry_greenBlk_eq:50/124 mixEntry_det:27/512
new helpers: mixSamplePair measurable_mixSamplePair EntryTail_Gres_true mixEntry_auxMinorRes_zero
not ported: mixEntry_mixVar_tagFree
```

### (b.6) narrative
- One new file, `RBM3D/Universality/GUEPhase/EntryTail.lean` (1419 lines, commits `34b30b1` and `408c53a`; the second adds the instances of the helpers), imports only `RBM3D.Universality.GUEPhase.EntryDet` (it brings `AuxCarrier`, `OU`, `Pins`, `Green.EntryDom`; the build in (b.1) shows no other import is needed). `git diff --stat main...t/T2293` lists only this file; `RBM3D/Test/Axioms.lean` is untouched (no registry line: the ledger of the pre-check is identical with and without the module, only the theorem and definition counts grow).
- Port of RBM2D `Universality/GUEPhase/EntryTail.lean` at `c9a24cf` `:1-874` (RBM2D HEAD `9e0f275` differs from `c9a24cf` by 85 insertions and 274 deletions, (b.5); ported from `c9a24cf` as the ticket says). 22 declarations are identical to the source after the normalisation of (b.5) (the `mixEntry_meas_*` but `_green`, the Chernoff/Gaussian tails, `mixEntry_diag_tail`, `mixEntry_relabel_*`, `mixEntry_erase_iff`, `mixEntry_pair_map`, `MixProfOK`); the others differ by the carrier, the `d`/`g` arguments or the `A = 0` edits.
- Carrier: `mixMat`, `mixSample` on `SeqΩ sz × Ω d (sz.L n) (sz.W n)` with `Sizes.slice`; `GUEEntryMix d` has `sz.Admissible 𝔠 𝔡` and `(W^d)⁻¹`; the library definitions equal the check file's `mixMatV`, `mixSampleV`, `GUEEntryMixV` (`rfl` examples, (b.2)).
- `mixSample_law`: the body of RBM2D `:202-262` is the private pair-space lemma `mixSamplePair_law` at `PF d L W g ⊗ gueP` (20 of 463 tokens differ from the source, (b.5)); the theorem transports it by `Prod.map (slice sz n) id` and `seqP_map_slice`, as `ouSample_law` (`OU.lean:208-222`) does.
- Tails: `mixEntry_quad_tail` uses `gaussLaw_quad_tail … (A := 0)` and `zero_add` (13 of 323 tokens differ); row and column use `auxLinChaos`/`aux_lin_tail` with `auxMinorRes … 0 …`, rewritten to `greenMinor (green (auxHG …))` by the new private `mixEntry_auxMinorRes_zero`. The merged `continuous_green_of_isHermitian` returns `Gres … true`; the new private `EntryTail_Gres_true` converts it to `green` (same proof as the private `auxCarrier_Gres_true` of `AuxCarrier.lean`). `RowChaos.sum_erase_eq` (merged, `Green/LDEQuadMom.lean:728`) is used as is.
- `mixEntry_det` calls `mix_det hd hL hM hg hgΛ …` and `entryDom_goodEvent_of_llErr d L W …`; `3 ≤ d`, `0 < g`, `g ≤ Λ` appear only there (§29 (6)); the pin `GUEEntryMix d` has no `3 ≤ d`.
- Instances: the ticket's data (`Λ = lam = 2`, `q = 1`) give tail bounds `≥ 1` for quad/row/col (`hwConst q = ((2q+1)(4q+2))^(q+1)`, `Green/IBPPoly.lean:721`, so `hwConst 1 = 324`, `hwConst 0 = 2`); the `_sharp` variants (`λ = Λ = 4`, `q = 0`) have bounds `hwConst 0 / 4 = 1/2` and `hwConst 0 / 9 = 2/9`; the diagonal bound is `2 exp(-1)`. `inst_mixEntry_det` is the ticket's form (`M` Hermitian and the four LDE inputs as hypotheses). `inst_mixEntry_det_full` discharges everything at `M = 0`, `E = 0`, `g = Λ = κ = 1`, `Φ = 256`, `δ = min (mixDelta 3 1 1) (1/100)`, `u = δ/(1+δ)`, `(a, b) = (u/2, u/2)`: `llErrMat` is `u/(1-u) = δ` on the diagonal and `0` off it (proved), rows/columns are `0 ≤ Φ·(nonneg)`, the quadratic input is Cauchy-Schwarz with `#(univ.erase i) = 215 ≤ 256`, the diagonal input is `0 ≤ Φ Smix_ii`. This is the witness of preflight (ii-1) (`M = 0`, `Φ ≥ 215`, `u` small).
- Preflight (a): nothing found wrong, so no (a′). Its observation (1) (`Φ = 1` is not a witness at `M = 0`) is consistent with `Φ = 256` here.
- Not in this ticket: `mixBad`, `mixBad_tail`, the union, the size scale and `gueEntryMix` (T2293b, `EntryTailMain.lean`); `GUEEntryMix d` is stated here and proved there.
- The whole-library `lake build` in the worktree does not contain the module (the hub adds the root import at merge); the registry pre-check (`import RBM3D` + the module + `#assert_rbm_axioms`) is the check that the module passes the library-wide axiom audit.

## (c) Verified Mathlib and merged names used (`#check`, names.lean: 32 names, exit 0, 0 error lines, 12:37 UTC)
`Real.sqrt_eq_iff_mul_self_eq`, `gaussianReal_map_const_mul`, `gaussianReal_conv_gaussianReal`, `MeasureTheory.Measure.map_prod_map`, `MeasureTheory.IsProjectiveLimit.unique`, `MeasureTheory.Measure.isProjectiveLimit_infinitePi`, `MeasureTheory.Measure.infinitePi_map_restrict`, `MeasureTheory.Measure.infinitePi_map_eval`, `MeasureTheory.measurePreserving_arrowProdEquivProdArrow`, `MeasureTheory.Measure.pi_map_pi`, `ProbabilityTheory.measure_ge_le_exp_mul_mgf`, `ProbabilityTheory.measure_le_le_exp_mul_mgf`, `ProbabilityTheory.integrable_exp_mul_gaussianReal`, `ProbabilityTheory.mgf_id_gaussianReal`, `MeasureTheory.ofReal_measureReal`, `Finset.sum_subtype`, `Finset.sum_equiv`, `Finset.card_erase_of_mem`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.inv_eq_right_inv`, `Matrix.isHermitian_zero`, `sq_sum_le_card_mul_sum_sq` (root namespace), `smul_mul_smul_comm`, `Complex.norm_conj`, `Complex.I_ne_zero`.
Merged RBM3D names, all present: `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`, `RBM.Ind.Gres_eq_green_zSig`, `RBM.Gauss.continuous_green_of_isHermitian` (conclusion is `Gres … true`), `RBM.Green.green_diag_ne_zero`, `RBM.Green.inv_minor_resolvent`, `RBM.Green.RowChaos.sum_erase_eq`.
Deprecated names met while writing (compiler warnings): `if_pos`, `if_neg`, `if_true`; none remains in the file (grep).

## (d) Open issues and paper-delta candidates
- `T2293a` (Lean structure, not a paper delta): the `d ≥ 3` carrier is `ouP (UNModel.band sz) n` with coupling `sz.lam n` (RBM2D `ouP L W` had none); `GUEEntryMix d` quantifies `sz.Admissible 𝔠 𝔡` (with `WO 𝔡`) instead of `Admissible 𝔠 d`; `3 ≤ d` is not inside the pin.
- `T2293b` (bookkeeping): the pin's error term is `(W^d)⁻¹` (RBM2D `W^{-2}`), as the ticket pins it; this ticket only states it, the slack argument belongs to T2293b (`mixEntry_event_subset`).
- `T2293c` (Lean structure): class T split as T2173 says: the band instance is here, the BA instance (`lamV = 0`, matrix `m`) is BA-C3; the four tails are stated for any tag-free `v` and any `S` with `MixProfOK` and serve both.
- Rename (ticket): RBM2D `mixEntry_sigRow_gvar` is `mixEntry_sigRow_gvarF`; `mixEntry_mixVar_tagFree` is not ported (merged as `mixVar_tagFree`).
- `inst_mixEntry_det` follows the ticket (`M` and the LDE inputs are hypotheses); the fully discharged instance is `inst_mixEntry_det_full`. The tail instances at the ticket's data have conclusions `≥ 1`; the `_sharp` ones do not.
- Preflight (ii-3) Monte-Carlo (a) was not re-run here (no new claim depends on it).
