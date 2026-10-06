Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 11:07:51 UTC 2026

External hypotheses: none (every input is merged: BASelf, BAimInv_diag, BAcard_Zd); no concrete-limit check applies. Statements below are as in `docs/tickets/checks/T2283-check.lean` sections 2-3 and the merged pins `MFixedPoint.lean:558, 566, 583` (read, unchanged).

### (i) Exponent table (no exponents; constants/thresholds the targets use)

| row | value | constraint | slack |
|---|---|---|---|
| `Im w`, `w = z+m` (`BAMB_ward_row`) | `Im z + Im m` | `> 0` for `BAimInv_diag`; `Im m > 0` from `BASelf`, `Im z ≥ 0` | `≥ Im m > 0` |
| Ward row: `(Im m+Im z)·Σ_b‖M_ab‖² = Im m` | factor `Im m/(Im m+Im z)` | `= 1` iff `Im z = 0`; `≤ 1` for `Im z ≥ 0` (gives `‖m‖² = ‖M_aa‖² ≤ Σ_b‖M_ab‖² ≤ 1`) | none needed |
| `BAPropM12` constants | none | conclusion determined by the datum `(L,g,z/E,m)` | n/a |
| `κ ≤ 1` (scalar lemma) | `κ ≤ Im m ≤ ‖m‖ ≤ 1` | needed for `κ/2 ≥ κ²/4` and `x = κ² ≤ 1` | `κ ≤ 1` from hypotheses |
| `ε` of `BAoffDiag` | `κ²/4` (before `L,g,E,m`; depends on `κ` only, §18) | (A) `ε ≤ ‖1-tm²‖ ∀t∈[0,1]`; (B) `(1-ε)‖1-tm²‖ ≥ 1-‖m‖²`; `0<ε<1` | `ε ≤ 1/4`; see below |
| (A) with `s=‖m‖², y=Im m` | `‖1-tm²‖² = (1-ts)²+4ty²` (identity, ring) `≥ (1-t)²+4tκ²` since `1-ts ≥ 1-t ≥ 0` | `t≤1/2`: `≥1/4`, so `‖·‖ ≥ 1/2`; `t≥1/2`: `≥2κ²`, so `‖·‖ ≥ √2κ`; both `≥ κ²/4` | `min(1/2,√2κ) ≥ κ²/4` for `κ≤1` (at `κ=1`: `1/2` vs `1/4`) |
| (B) step 1 | `‖1-tm²‖²-(1-s)² = s(1-t)(2-s-ts)+4ty² ≥ κ²(1-s)` | `2-s-ts ≥ 1-s`, `s ≥ y² ≥ κ²`, `4ty² ≥ tκ²(1-s)` | `κ²(1-s) ≥ κ²(1-s)²` since `0≤1-s≤1` |
| (B) step 2 | `‖1-tm²‖ ≥ √(1+κ²)(1-s)` | need `(1-ε)√(1+κ²) ≥ 1`, i.e. `(1-x/4)²(1+x) = 1 + x(8-7x+x²)/16 ≥ 1`, `x=κ²∈(0,1]` | `8-7x+x² ≥ 2` on `[0,1]` (min at `x=1`), so excess `≥ x/8` |
| `ε=κ²/2` | not used | (ii) of ticket does not give it | n/a |

Hypotheses used by proofs: `BAWard`/`BAPropM12`: `BASelf`, `0 ≤ Im z` (resp. real `E`); `BAoffDiag`: `κ ≤ Im m` (from `BAReal`), `t∈[0,1]`. Not used: `3 ≤ L`, `0 < g`, `3 ≤ d`, `0 < Λ`, `g ≤ Λ` (`L ≥ 1` only through `NeZero L`). `BAoffDiag`'s `3 ≤ d → 0<Λ → 0<κ →` are premises of the pin; `0<κ` is used.

### (ii) Pin vs paper (PASS/FAIL)

- `BAWard` vs `7_8:1853` (translation invariance, `M_aa ≡ m`), `:1864-1869` (`(eq:WardM)`), `:1902-1904`: PASS. At `Im z = 0` the row identity is `Σ_b|M_ab|²=1` (`Im m>0` cancels); for `Im z>0` the factor `Im m+Im z` is as in `BAward_avg` (`MFixedPoint.lean:389`, its row-sum). `M` symmetric by `1_2:634` ("complex symmetric") and `Ψ^{(B)}_{ab}=1(a∼b)` (`1_2:616`, `PsiB` entries `if Adj d L a b`, `Adj = (zdistD (x-y) = 1)`), translation invariant as `Adj (a+r)(b+r) ↔ Adj a b`.
- `BAPropM12` vs `lem:propM` (1)(2): PASS. It is the first four conjuncts of `BAPropM` (`:566-575`) verbatim under `BASelf` at real `E`; `Im m ≳ 1` is excluded (bulk premise `κ ≤ Im m` of `BAReal`). It needs no `κ`, `Λ`, `3 ≤ L`.
- `BAoffDiag` vs `A:32-34`: PASS. `A:33` states `‖M'‖_{∞→∞} = Σ_{a≠0}|M'_{0a}| = 1-|m|² ≤ (1-ε)|1-tm²|`, `|1-tm²| ≥ ε`, `t∈[0,1]`; Lean sums `‖BAMss … true true 0 a‖ = ‖M_a0 M_0a‖` over `a≠0`, `= Σ|M_0a|²` by symmetry `= 1-|M_00|² = 1-|m|²` (Ward row 0 minus the diagonal term). `BAMss` is `(eq:Msig)` (`1_2:1070-1071`).

### (iii) §29 (1)-(7)
(1) no flow time; `t∈[0,1]` endpoints included (checked at `t=0,1` below). (2) no gate. (3) no `L`-`W` relation; `3 ≤ L` premise unused. (4) fixed `(L,g)`, no `n`. (5) no law: `grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/MFixedPoint.lean` = 0 (new file not yet existing: `ls RBM3D/BA/Ward.lean` → No such file; the count on it is the prover's). (6) `0<g,0<Λ,0<κ` premises, `ε` before `L,g,E,m`, depends on `κ` only. (7) consumers apply at their own `(g,E,m)`.
### (iv) Two data, one model
`BAWard`, `BAPropM12`: no constant; PASS. `BAoffDiag`: `ε=κ²/4` observes only `κ`; the proof (A),(B) uses only `κ ≤ Im m`, `‖m‖ ≤ 1`, so any two data with the same `κ` and any `(L, g≤Λ, E)` get the same valid `ε`: PASS.

### (iii') Name-clash grep and registry
`cd /Users/junyin/Lean_proof/RBM3D && grep -rlw "BAMB_shift\|BAMB_transpose\|BAMB_symm\|BAMB_diag_eq\|BAMB_ward_row\|baWard_holds\|BAMB_row_sq_real\|BAm_norm_le_one\|BAPropM12\|baPropM12_holds\|BAnorm_one_sub_tm2_sq\|BAoffDiag_scalar\|BAMss_pp_apply\|BAoffDiag_row_sum\|BAoffDiag_of_real\|baOffDiag_holds\|WardInst" RBM3D` → no output (0 hits at `main` f3e7c74). Registry: no line (conclusions unconditional; `BASelf` is a merged data condition).

### (v) Numeric check at d = 3 (command `python3 chk.py`; `Ψ^{(B)}` from `Adj` on `Z_L^3`, `m` by continuation `η↓0` then Newton, `M` by dense inversion; `q = |1-tm²|`, `ε=κ²/4`, `κ=Im m`, `t` on a 2001-point grid of `[0,1]`)
```
L 4 g1.5 edge scan (E,Im m): [(6.7, 0.1364), (6.75, 0.0586), (8.9, 0.0439), (8.95, 0.0858)]
L 6 g1.5 edge scan (E,Im m): [(6.55, 0.1336), (6.6, 0.0788), (7.35, 0.0333), (7.4, 0.0968)]
L=4 g=0.3  E=0     m=(-0+0.82816j)          self=4.3e-17 shift=6.7e-16 sym=2.8e-16 diag=4.5e-16 ward=6.7e-16 offd=0.0e+00 min(q-eps)=0.829 min((1-eps)q-(1-|m|^2))=0.5144 max(1-|m|^2)/q=0.314
L=4 g=0.3  E=2     m=(-0.64317+0.44127j)    self=2.2e-16 shift=1.7e-15 sym=5.1e-16 diag=1.2e-15 ward=1.8e-15 offd=1.1e-16 min(q-eps)=0.884 min((1-eps)q-(1-|m|^2))=0.4960 max(1-|m|^2)/q=0.420
L=4 g=1.5  E=0.5   m=(-0.23533+0.51132j)    self=4.8e-16 shift=1.0e-15 sym=9.6e-16 diag=8.9e-16 ward=2.0e-15 offd=6.7e-16 min(q-eps)=0.935 min((1-eps)q-(1-|m|^2))=0.2515 max(1-|m|^2)/q=0.683
L=4 g=1.5  E=6     m=(-0.08287+0.30156j)    self=3.1e-16 shift=9.7e-16 sym=5.0e-16 diag=8.7e-16 ward=1.9e-15 offd=0.0e+00 min(q-eps)=0.977 min((1-eps)q-(1-|m|^2))=0.0751 max(1-|m|^2)/q=0.902
L=6 g=0.5  E=1     m=(-0.23689+0.62737j)    self=1.2e-16 shift=1.6e-15 sym=8.7e-16 diag=1.3e-15 ward=1.8e-15 offd=1.1e-16 min(q-eps)=0.902 min((1-eps)q-(1-|m|^2))=0.3513 max(1-|m|^2)/q=0.550
L=6 g=1.5  E=6     m=(-0.09102+0.22758j)    self=2.2e-16 shift=1.2e-15 sym=9.7e-16 diag=8.9e-16 ward=3.8e-15 offd=3.3e-16 min(q-eps)=0.987 min((1-eps)q-(1-|m|^2))=0.0471 max(1-|m|^2)/q=0.940
L=6 g=3    E=3     m=(-0.01466+0.41541j)    self=7.2e-16 shift=3.2e-15 sym=3.0e-15 diag=2.7e-15 ward=1.2e-14 offd=1.2e-15 min(q-eps)=0.957 min((1-eps)q-(1-|m|^2))=0.1296 max(1-|m|^2)/q=0.827
L=4 g=10   E=0     m=(-0+0.55938j)          self=2.4e-15 shift=4.6e-15 sym=3.9e-15 diag=2.4e-15 ward=1.3e-15 offd=0.0e+00 min(q-eps)=0.922 min((1-eps)q-(1-|m|^2))=0.2347 max(1-|m|^2)/q=0.687
L,g,E= (6, 0.2, 2.3) outside support (Im m = 0.0 )
L=4 g=1.5  E=6.7   m=(-0.41969+0.13636j)    self=8.6e-16 shift=1.2e-15 sym=1.0e-15 diag=1.5e-15 ward=7.5e-15 offd=4.8e-15 min(q-eps)=0.846 min((1-eps)q-(1-|m|^2))=0.0410 max(1-|m|^2)/q=0.947
L=4 g=1.5  E=9.1   m=(-0.11617+0.12543j)    self=3.0e-16 shift=3.4e-16 sym=1.5e-16 diag=4.9e-16 ward=3.2e-15 offd=7.8e-16 min(q-eps)=0.996 min((1-eps)q-(1-|m|^2))=0.0253 max(1-|m|^2)/q=0.971
L=6 g=1.5  E=6.55  m=(-0.34581+0.13364j)    self=5.0e-16 shift=1.7e-15 sym=1.8e-15 diag=1.7e-15 ward=1.0e-14 offd=2.2e-16 min(q-eps)=0.899 min((1-eps)q-(1-|m|^2))=0.0364 max(1-|m|^2)/q=0.955
L=6 g=1.5  E=7.9   m=(-0.27811+0.11945j)    self=4.2e-16 shift=1.3e-15 sym=5.9e-16 diag=1.2e-15 ward=9.3e-15 offd=4.0e-15 min(q-eps)=0.936 min((1-eps)q-(1-|m|^2))=0.0275 max(1-|m|^2)/q=0.967
scalar scan min slack (random 1e5, kappa<=Im m,|m|<=1,t in[0,1]): 0.0017813243668426404  identity 2a max err 1e4: 6.821210263296962e-13
min (1-x/4)^2(1+x)-1 on [0,1]: 0.0
```
Columns: self = |tr M/L³ − m|; shift = max over 3 translations of |M_{a+r,b+r} − M_ab|; sym = |M − Mᵀ|; diag = max|M_aa − m|; ward = max_a |Σ_b|M_ab|² − 1|; offd = |Σ_{a≠0}|M_a0 M_0a| − (1−|m|²)|. All residuals ≤ 1.2e-14; the two edge points per L have `Im m` in 0.119-0.136 (`< 0.15`); `(6,.2,2.3)` is outside the support (not a `BAReal` datum, as the ticket says). Last two lines: random scan of the scalar claim and the polynomial `(1-x/4)²(1+x)-1 ≥ 0` (min 0 at x=0).

### (ii-inst) One concrete nondegenerate instance (command `python3 inst.py`)
Data: `d=3, L=4` (`|Z_4^3|=64`), `g=1.5 ≤ Λ=2`, `E=0.5`, `m = −0.2353+0.5113i`, `κ=1/2 ≤ Im m`, `‖m‖ ≈ 0.563 ≤ 1`, `t ∈ [0,1]` (grid incl. endpoints); instance B (complex point, as the Lean instance `(zS 4 10, mS 4 10)`): `g=10`, `w=6i/5`, `m = mean 1/(gλ − w)`, `z = w − m`, `Im z>0`; scalar instance `κ=1/2, m=0.6i, t∈{0,1}`.
```
instance A: d=3 L=4 g=1.5<=Lam=2 E=0.5 m= (-0.23532913652347218+0.5113218986933616j)  kappa=0.5<=Im m: True  |m|<=1: True
 (self_m) res 4.847302891456678e-16  Ward rows max err 1.9984014443252818e-15  card Zd= 64
 2a identity max err 8.881784197001252e-16
 (i) q>=sqrt((1-t)^2+4t kap^2): True  q>=kap^2/4: min slack 0.9375
 (ii) q^2>=(1+kap^2)(1-s)^2: min slack 0.41659824516258726  (y-form with kappa=Im m: 0.41125424584476133 )
 row0 sum_{a!=0}|M_a0 M_0a| = 0.6831701134197332  1-|m|^2 = 0.6831701134197325
 final: (1-kap^2/4)q-(1-s) min over t: 0.25432988658026745
instance B: z= (3.0747973611688906e-16+0.9380312166207381j)  m= (-3.0747973611688906e-16+0.26196878337926194j)  Im z>0: True  self res 3.124504377233793e-16
 Ward factor rows: max |(Im m+Im z) sum|M_ab|^2 - Im m| = 3.3306690738754696e-16  Im m + Im z = 1.2
 |m|<=1: 0.26196878337926194  sum|M_ab|^2 row = 0.21830731948271823  = Im m/(Im m+Im z)= 0.21830731948271828
 scalar kappa=.5 m=.6i t= 0  |1-tm^2|= 1.0  >=1/16: True  1-|m|^2= 0.64  <= (15/16)q: True
 scalar kappa=.5 m=.6i t= 1  |1-tm^2|= 1.3599999999999999  >=1/16: True  1-|m|^2= 0.64  <= (15/16)q: True
scan 1e6: min[q^2-((1-t)^2+4t kap^2)]= 2.3027899172158722e-08  min[q^2-(1+kap^2)(1-s)^2]= 0.00010938742482291541  min[(1-x/4)^2(1+x)-1]= 5.017789008743279e-07
```
All hypotheses of `BAWard`, `BAPropM12`, `BAoffDiag` (real datum A) and of `BAMB_ward_row` (complex datum B, factor `Im m+Im z = 1.2`) hold simultaneously; rows are nonempty (64 points), `Im m > 0`, no collapsed window.

### Verdicts
- Ward half (`BAMB_shift`, `_transpose`, `_symm`, `_diag_eq`, `_ward_row`, `baWard_holds`, `_row_sq_real`, `BAm_norm_le_one`, `baPropM12_holds`): **PASS**.
- Off-diagonal half (`BAnorm_one_sub_tm2_sq`, `BAoffDiag_scalar`, `BAMss_pp_apply`, `BAoffDiag_row_sum`, `BAoffDiag_of_real`, `baOffDiag_holds`): **PASS** (`ε=κ²/4` closes with the slacks in (i); the ticket's route (ii)+(i) is correct as stated).
- Instances list of the ticket: hypotheses match the signatures (`zS_im_pos.le`, `P.real.1`, `P.g0_le`); no FAIL/BLOCKED found. Stale "Owed: BA-D3" docstrings: `MFixedPoint.lean:557, 566, 582` (for the hub; not edited).
- Overall: **PASS**. Paper-delta candidates: none.

## (b) Script output — Tue Oct  6 11:14:56 UTC 2026

```
$ lake build RBM3D.BA.Ward   (worktree RBM3D-wt/T2283, branch t/T2283, commit 2056e33)
⚠ [3332/3332] Built RBM3D.BA.Ward (14s)
warning: RBM3D/BA/Ward.lean:16:100: This line exceeds the 100 character limit, please shorten it!

Build completed successfully (3332 jobs).
exit 0
$ lake env lean <scratch: T2283-check.lean + import RBM3D.BA.Ward + 16 `example : T2283Check.BAPropM12 = BAPropM12 := rfl` / `example : T2283Check.Y_pin := @RBM.BA.Y`>
exit 0, error lines: 0  (16 examples: BAPropM12 rfl + 15 theorems)
$ registry pre-check: temp file `import RBM3D` + `import RBM3D.BA.Ward` + `#assert_rbm_axioms`, lake env lean
axiom audit: 8228 theorems, 2669 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit 0; lines matching Ward|PropM12|offDiag|BAMB: only STExpWardIConcl, STExpWardIIConcl, STExpWardIConcl' (Sizes names, not this file)
$ lake build   (full library; RBM3D.lean has no import of RBM3D.BA.Ward before the hub merge)
Build completed successfully (4092 jobs).
exit 0
$ lake env lean ax.lean  (#print axioms of 15 theorems, BAPropM12, 2 instance theorems)
'RBM.BA.BAMB_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_diag_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_ward_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWard_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_row_sq_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropM12_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAnorm_one_sub_tm2_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAoffDiag_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMss_pp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAoffDiag_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAoffDiag_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baOffDiag_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.WardInst.ward_scalar_inst_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.WardInst.ward_scalar_inst_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAPropM12' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2283
 RBM3D/BA/Ward.lean | 427 +++++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 427 insertions(+)
$ grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/Ward.lean
0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/Ward.lean | wc -l
       0
$ grep -rlw <the 16 new public names and WardInst> RBM3D   (main worktree, before this branch is merged)
0 files
$ grep -rlw <same> RBM3D   (T2283 worktree)
RBM3D/BA/Ward.lean
```

### Target statements (extracted by script from RBM3D/BA/Ward.lean, namespace RBM.BA, section vars: (d L : ℕ) [NeZero L])
```lean
theorem BAMB_shift (g : ℝ) (z m : ℂ) (a b r : Zd d L) :
    BAMB d L g z m (a + r) (b + r) = BAMB d L g z m a b
theorem BAMB_transpose (g : ℝ) (z m : ℂ) :
    Matrix.transpose (BAMB d L g z m) = BAMB d L g z m
theorem BAMB_symm (g : ℝ) (z m : ℂ) (a b : Zd d L) :
    BAMB d L g z m a b = BAMB d L g z m b a
theorem BAMB_diag_eq (g : ℝ) (z m : ℂ) (h : BASelf d L g z m) (a : Zd d L) :
    BAMB d L g z m a a = m
theorem BAMB_ward_row (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) (h : BASelf d L g z m) (a : Zd d L) :
    (m.im + z.im) * ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im
theorem baWard_holds (d : ℕ) : BAWard d
theorem BAMB_row_sq_real (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
    ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1
theorem BAm_norm_le_one (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) (h : BASelf d L g z m) : ‖m‖ ≤ 1
theorem baPropM12_holds (d : ℕ) : BAPropM12 d
theorem BAnorm_one_sub_tm2_sq (t : ℝ) (m : ℂ) :
    ‖1 - (t : ℂ) * m ^ 2‖ ^ 2 = (1 - t * ‖m‖ ^ 2) ^ 2 + 4 * t * m.im ^ 2
theorem BAoffDiag_scalar (κ t : ℝ) (m : ℂ) (hκ : 0 < κ) (hκm : κ ≤ m.im) (hm : ‖m‖ ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
      1 - ‖m‖ ^ 2 ≤ (1 - κ ^ 2 / 4) * ‖1 - (t : ℂ) * m ^ 2‖
theorem BAMss_pp_apply (d L : ℕ) [NeZero L] (M : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    BAMss d L M true true a b = M b a * M a b
theorem BAoffDiag_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) :
    ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
      = 1 - ‖m‖ ^ 2
theorem BAoffDiag_of_real (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
        ≤ (1 - κ ^ 2 / 4) * ‖1 - (t : ℂ) * m ^ 2‖
theorem baOffDiag_holds (d : ℕ) (Λ κ : ℝ) : BAoffDiag d Λ κ
def BAPropM12 : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    BASelf d L g (E : ℂ) m →
      (∀ a b r : Zd d L, BAMB d L g (E : ℂ) m (a + r) (b + r) = BAMB d L g (E : ℂ) m a b) ∧
      (∀ a : Zd d L, BAMB d L g (E : ℂ) m a a = m) ∧
      (∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1) ∧ ‖m‖ ≤ 1

end PropM12
```

### Compiled nonempty instances (RBM.BA.WardInst, lines 314-423 of the file; d = 3, L = 4, card (Zd 3 4) = 64; no hypothesis left open)
```lean
example :
    (∀ a b r : Zd 3 4, BAMB 3 4 10 (zS 4 10) (mS 4 10) (a + r) (b + r) = BAMB 3 4 10 (zS 4 10) (mS 4 10) a b) ∧
    (∀ a : Zd 3 4, BAMB 3 4 10 (zS 4 10) (mS 4 10) a a = mS 4 10) ∧
    ∀ a : Zd 3 4, ((mS 4 10).im + (zS 4 10).im) * ∑ b, ‖BAMB 3 4 10 (zS 4 10) (mS 4 10) a b‖ ^ 2
      = (mS 4 10).im :=
  baWard_holds 3 4 (by norm_num) 10 (by norm_num) (zS 4 10) (mS 4 10) (zS_im_pos 4 10).le (selfS 4 10)

/-- `baWard_holds` at the real-axis flow point `P`. -/
example :
    (∀ a b r : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b) ∧
    (∀ a : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a a = P.m0) ∧
    ∀ a : Zd 3 4, (P.m0.im + ((P.E : ℂ)).im) * ∑ b, ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ^ 2 = P.m0.im :=
  baWard_holds 3 4 (by norm_num) P.g0 P.g0_pos (P.E : ℂ) P.m0 (by simp) P.real.1

/-- `baPropM12_holds` at the flow point `P`. -/
example :
    (∀ a b r : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b) ∧
    (∀ a : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a a = P.m0) ∧
    (∀ a : Zd 3 4, ∑ b, ‖BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b‖ ^ 2 = 1) ∧ ‖P.m0‖ ≤ 1 :=
  baPropM12_holds 3 4 (by norm_num) P.g0 P.g0_pos P.E P.m0 P.real.1

/-- The row-wise pieces at `P`: symmetry, transpose, `M_aa = m`, Ward row, `|m| ≤ 1`. -/
example (a b : Zd 3 4) : BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 b a :=
  BAMB_symm 3 4 P.g0 (P.E : ℂ) P.m0 a b
-- ...
example :
    P.m0.im ^ 2 / 4 ≤ ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd 3 4), ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true 0 a‖
        ≤ (1 - P.m0.im ^ 2 / 4) * ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ :=
  BAoffDiag_of_real 3 4 P.g0 P.m0.im P.E P.m0 P.real.1.1 P.real (1 / 2) (by norm_num) (by norm_num)

/-- `baOffDiag_holds` at `d = 3`, `Λ = 10`, `κ = Im m₀`, applied at `L = 4`, `g = P.g0 ≤ 10`, `P.E`, `P.m0`,
`t = 1/2`: the `ε` is explicit, quantified before the data. -/
example : ∃ ε : ℝ, 0 < ε ∧
    (ε ≤ ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd 3 4), ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true 0 a‖
        ≤ (1 - ε) * ‖1 - (((1 / 2 : ℝ)) : ℂ) * P.m0 ^ 2‖) := by
  obtain ⟨ε, hε, h⟩ := baOffDiag_holds 3 10 P.m0.im (le_refl 3) (by norm_num) P.real.1.1
  exact ⟨ε, hε, h 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num)⟩

/-- `BAnorm_one_sub_tm2_sq` at `m = (3/5) i`, `t = 1/2`. -/
```
Further examples in the same namespace (the rest of lines 314-423): BAMB_symm, BAMB_transpose, BAMB_shift, BAMB_diag_eq, BAMB_row_sq_real, BAm_norm_le_one at P; BAMB_ward_row at (zS 4 10, mS 4 10) with Im z > 0; BAoffDiag_row_sum, BAoffDiag_of_real, BAMss_pp_apply at P; BAnorm_one_sub_tm2_sq and BAoffDiag_scalar at kappa = 1/2, m = (3/5) i, t in {0, 1} (two named theorems ward_scalar_inst_norm, ward_scalar_inst_im discharge the scalar hypotheses).

### Narrative
- One new file, RBM3D/BA/Ward.lean (427 lines incl. instances); imports exactly RBM3D.BA.MFixedPoint; no Mathlib module added. No merged file touched; MFixedPoint.lean docstrings are not edited.
- Every statement equals the check file's section 2/3 body: the 16 rfl / @-examples compile (exit 0, 0 error lines).
- Route as in the ticket: BAMB_shift from Matrix.inv_submatrix_equiv at Equiv.addRight r; BAMB_transpose from Matrix.transpose_nonsing_inv and zdistD_neg; BAMB_diag_eq from shift + BAcard_Zd; BAMB_ward_row from BAimInv_diag at w = z + m; offdiag scalar part by nlinarith with the ticket's products (A: case split t <= 1/2; B: q^2 >= (1+kappa^2)(1-s)^2, then (1-x/4)^2(1+x) >= 1).
- Hypotheses of the pins not used by the proofs: 3 <= L (replaced by NeZero L), 0 < g (all three), 3 <= d, 0 < Lambda, g <= Lambda (BAoffDiag). The pins are unchanged (no primed successor); epsilon = kappa^2/4 depends on kappa only (DECISIONS §18).
- BAPropM is not proved here (conjunct (3) is BA-D4); BAPropM12 = its first four conjuncts under BASelf at real E.
- Registry: no line needed (pre-check exit 0; no BA/Ward name in the ledgers). Test/Axioms.lean untouched.
- For the hub at merge: the docstrings 'Owed: BA-D3' at MFixedPoint.lean (lines of BAWard, BAPropM, BAoffDiag; preflight lists :557, :566, :582) are stale for BAWard and BAoffDiag; BAPropM stays owed to BA-D4. Root import to add: import RBM3D.BA.Ward.
- Two public instance theorems in WardInst (ward_scalar_inst_norm, ward_scalar_inst_im) are not pinned names; they are in the instance namespace and clash with nothing (grep above).
- Ports: none (no RBM1D/RBM2D text used), so no diff-stat.

## (c) Verified Mathlib names (all compiled in this file)
Matrix.inv_submatrix_equiv; Matrix.transpose_nonsing_inv; Matrix.nonsing_inv_eq_ringInverse; Equiv.addRight (Equiv.coe_addRight); add_left_inj; add_sub_add_right_eq_sub; Matrix.submatrix_apply; Matrix.transpose_sub; Matrix.transpose_smul; Matrix.transpose_one; Finset.add_sum_erase; Finset.single_le_sum; Finset.sum_const; Finset.card_univ; Complex.sq_norm; Complex.normSq_apply; inv_mul_cancel₀; pow_pos; not_le; mul_le_mul.
Verified absent: Nat.pos_pow_of_pos (unknown constant); push_neg is deprecated in this Mathlib (push Not), avoided.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. (Off the real axis, (eq:WardM) holds with factor Im m/(Im m + Im z): already in BAward_avg's docstring and BAMB_ward_row; not re-proposed.)
- Linter: one over-100-character line remains in the module docstring (line 16); the file sets linter.style.longLine false after the docstring; build warning only.
