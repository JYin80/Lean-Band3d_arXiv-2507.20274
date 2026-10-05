Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 14:53:59 UTC 2026

### (i) Exponent table (no exponents; constants and identities the targets use)

Notation: `A = gΨ^{(B)}` (real symmetric, Hermitian: `PsiB_isHermitian`), `n = L^d = card (Zd d L)` (`BAcard_Zd`), `w_j = z + m_j`, `M_j = (A - w_j)⁻¹`, `X_j = n⁻¹ Σ_{a,b}|M_j(b,a)|²`.

| Quantity | Value | Constraint it must satisfy | Slack / note |
|---|---|---|---|
| `t` in [32] (2.5) | `1` (`BASelf` has `m = n⁻¹ tr(A - z - 1·m)⁻¹`) | `0 ≤ t` (`freeConv_existsUnique`) | slack 1; `t = 0` is not used |
| `card (Zd d L)` | `L^d`; `L^d ≥ 1` since `NeZero L` | nonempty `Fintype` for `freeConv_existsUnique` (`Nonempty (Zd d L)`: the zero vector) | no `3 ≤ L`, no `3 ≤ d`: holds for `d = 0`, `L = 1,2` (numerics below) |
| `v_i = BAspec d L g i` | `g·λ_i(Ψ^{(B)})` | real; spectral theorem for the Hermitian `Ψ^{(B)}`: `gΨ = U diag(gλ) U*` for every real `g` (any sign) | `g` may be `≤ 0` for 4a-4d |
| Invertibility in 4a | `(z+m).im ≠ 0` | `gλ_i - w ≠ 0` for every `i` since `Im(gλ_i - w) = -Im w ≠ 0` | exact |
| `Im w_j` (4b, 4d) | `Im m_j + Im z` | `> 0` when `0 ≤ Im z`, `0 < Im m_j` (so `A - w_j` invertible, `isUnit_sub_smul_of_isHermitian`, and 4a applies) | slack `Im m_j > 0` |
| `X_j` (Ward, `BAward_avg`) | `Im m_j / (Im m_j + Im z)` | from `Im M_aa = Im w Σ_b|M_ab|²` summed over `a`, `Im(n⁻¹ tr M) = Im m`: `X_j ≤ 1` | `< 1` for `Im z > 0`; `= 1` exactly on the real axis |
| Resolvent identity (4d) | `M₁ - M₂ = (w₁-w₂) M₁M₂`, `w₁-w₂ = m₁-m₂` | if `m₁ ≠ m₂`: `n⁻¹ tr(M₁M₂) = 1` | uses only `m_j = n⁻¹ tr M_j` |
| Hilbert–Schmidt identity (4d) | `0 ≤ n⁻¹‖M₁ - M₂*‖²_HS = X₁ + X₂ - 2 Re n⁻¹tr(M₁M₂) = X₁ + X₂ - 2` | `≤ 0` by `X_j ≤ 1`; hence `X₁ = X₂ = 1` | `Im z > 0`: `X_j < 1`, contradiction at once; `Im z = 0`: `M₁ = M₂* = (A - conj w₂)⁻¹`, so `w₁ = conj w₂`, `Im m₁ = -Im m₂`, contradicting `Im m_j > 0` |
| Subordination `BASelf_subord` (`Im w > 1`) | `Im m_w ∈ [Im w/(‖w‖² + g² L^d), (Im w)⁻¹]`, `Im(w - m_w) > 0` | row bound `Σ_k|(A-w)_{ik}|² ≤ ‖w‖² + g²L^d` (diagonal of `Ψ^{(B)}` is `0`, entries `≤ 1`); column bound `Σ_k|G_{ki}|² ≤ (Im w)⁻²`; `(Im w)⁻¹ < 1 ⇔ Im w > 1` | at `w = 6i/5`, `L = 4`, `g = 10`: lower `1.875e-4`, value `0.26197`, upper `0.8333`; `Im(w-m_w) = 0.938 > 0` |
| `t₀ = Im m/(Im m + Im z)` (`BAt0`) | `∈ (0,1)` | `Im m > 0`, `Im z > 0` | `t₀ = 0.2183` at `w = 6i/5`; `t₀ = 0.1862` at `w = 1/2+6i/5` |
| `√t₀ z.im = (1-t₀) m.im / √t₀` (`BAt0_mul`, clause 4 of `BAzztE_data`) | `E = (t₀ Re z - (1-t₀) Re m)/√t₀`, `m₀ = m/√t₀`, `g₀ = √t₀ g` | `E + m₀ = √t₀ (z+m)`; `√t₀ M(g₀,E,m₀) = M(g,z,m)`; `g₀ ≤ g`, `Im m₀ ≥ Im m` | `g₀ = 4.672 ≤ 10`; `Im m₀ = 0.5607 ≥ 0.2620` |
| `κ` for `BAbulk_iff_exists` | `κ = Im m₀/π = 0.17846` | `0 < κ`; `π κ ≤ Im m` | equality at the flow point, slack 0 (allowed: `≤`) |
| Pin hypotheses `3 ≤ L`, `0 < g` | not used by 4a-4f (proofs above use only: `A` Hermitian, `n ≥ 1`, `Im m_j > 0`, `0 ≤ Im z`) | pins `BAmExists`/`BAmUniqReal` quantify over a subset of the proved range | the weaker pins follow; report it, do not change pins |
| Existence | only for `Im z > 0` (`freeConv_existsUnique`) | on the real axis a gap energy has no root | `BAm = 0` there; uniqueness (4d) is vacuous in a gap |

Paper cross-check: `(self_m)` `1_2:626-629`, `(def_G0)` `1_2:631`, `m(E) = m(E+i0)` `1_2:715` (`paper/tex/1_2_Intro_model_result.tex`), `zztE_BA` with `t₀, E, g₀` `7_8:1796-1808` (`paper/tex/7_8_light_weight.tex`), `(eq:WardM)` `7_8:1869`.  The check-file statements 4a-4f were read against these: 4b's right side `((v i:ℂ) - z - ((1:ℝ):ℂ)*m)` is `v_i - (z+m)`, the form of `freeConv_existsUnique` at `t = 1` (`RBM3D/Universality/FreeConv.lean:639-641`); 4a, 4b agree with `BAMB = Mres (g•PsiB) z m = Ring.inverse (g•PsiB - (z+m)•1)` (`RBM3D/Loop/GLoopFlow.lean:81-82`).  `Adj` is `zdistD (x-y) = 1` (`Defs/Lattice.lean:108`), the `ℓ¹` nearest-neighbour adjacency (6 neighbours for `L ≥ 3`).

### (ii) Concrete nondegenerate instance (`d = 3`, `L = 4`, `g = 10`, `z = i`; `n = 64`)

All hypotheses of 4a-4f: `NeZero 4`, `Nonempty (Zd 3 4)`, `0 ≤ Im z` (`Im z = 1`, `Im z = 0.938`, and `Im z = 0` at `E`), `0 < Im m`, `(z+m).im ≠ 0`, `κ = 0.178 > 0`; `Im w = 6/5 > 1`.  No external hypothesis (the targets assume none of the five owed pins), so no external limit computation is needed.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2189/inst.py` (numpy 2.0.2, scipy 1.13.1; builds `Ψ^{(B)}` from the definition `Σ_i min(u_i, L-u_i) = 1`, then `v = 10 λ(Ψ)`; fixed point by `ω ← z + n⁻¹Σ(v-ω)⁻¹`; roots of `m - n⁻¹Σ(v-E-m)⁻¹` by damped complex Newton from 65 random starts with `Im m > 0`; the matrix residual uses `numpy.linalg.inv` of the 64 x 64 matrix):

```
card Zd 3 4 = 64 ; Hermitian: True ; row sums: {np.float64(6.0)}
max |v - 20 sum cos(pi k/2)| = 3.70847999811969e-14 ; v range -60.00000000000003 59.999999999999986
== (1) m(i,10) ==
m = (3.5063098258181213e-16+0.25134862782262446j) ; matrix residual |m - L^-3 tr M| = 5.361572761180937e-16
X = L^-3 sum|M|^2 = 0.2008621915860303 ; Im m/(Im m+Im z) = 0.20086219158603058
roots with Im m>0 from 65 starts: [0.25134863j]
trace identity: tr M - sum (v-(z+m))^-1 = 2.7866589113603718e-14
== (2) flow points ==
w = 1.2j
  z = 0.9380312166207381j  m_w = 0.2619687833792619j  0<Im z: True  Im w>1: True
  t0 = 0.21830731948271825  g0 = 4.672336883003175  E = 0.0  m0 = 0.5606804259603809j
  real-axis residual = 1.1102230246251565e-16  L^-3 sum|M0|^2 = 1.0
  |z_t0 - sqrt(t0) z| = 1.1102230246251565e-16  max|sqrt(t0)M0 - M| = 1.4311468676808659e-15
  real-axis roots (Im m>0) from 65 starts: [0.56068043j]
  subord bounds:  0.00018745782199005225 <= 0.2619687833792619 <= 0.8333333333333334
w = (0.5+1.2j)
  z = (0.591812840512842+0.976551716261576j)  m_w = (-0.09181284051284196+0.22344828373842396j)  0<Im z: True  Im w>1: True
  t0 = 0.18620690311535332  g0 = 4.315169789421423  E = 0.4285261092711537  m0 = (-0.2127676198000825+0.5178203747305707j)
  real-axis residual = 1.1443916996305594e-16  L^-3 sum|M0|^2 = 1.0
  |z_t0 - sqrt(t0) z| = 0.0  max|sqrt(t0)M0 - M| = 1.156020675135664e-15
  real-axis roots (Im m>0) from 65 starts: [(-0.21276762+0.51782037j)]
  subord bounds:  0.00018745050135198676 <= 0.22344828373842396 <= 0.8333333333333334
== (3) real-axis uniqueness scans ==
g=1e-3 : number of distinct roots with Im m>0 over 241 energies E ->count histogram {0: 50, 1: 191}
gap L=4 g=10 : number of distinct roots with Im m>0 over 241 energies E ->count histogram {0: 220, 1: 21}
```

Algebraic identities of 4d and the pin-hypothesis check: `python3 .../T2189/ident.py` (last 8 lines):

```
max |v - 20 sum cos(pi k/2)| = 3.70847999811969e-14 ; v range -60.00000000000003 59.999999999999986
resolvent identity |M1-M2-(m1-m2)M1M2| = 8.341509011073279e-16
HS identity:  0.6550391947926906 = 0.6550391947926908
z = (0.3+0.7j)  (Im m+Im z)*L^-3 sum|M|^2 = 0.29834688169824336  Im m = 0.2983468816982444  t0 = 0.29884090106110167  0<t0<1: True
z = (2+0.05j)  (Im m+Im z)*L^-3 sum|M|^2 = 0.005209431043335327  Im m = 0.00520943104333535  t0 = 0.09435762957322144  0<t0<1: True
d=3 L=2 g=-3.0: card=8, fixed pt m=0.017118+0.046401j, residual=3.5e-16, real-axis roots at E=0.3: 0
d=3 L=1 g=0.5: card=1, fixed pt m=-0.075638+0.776203j, residual=9.0e-16, real-axis roots at E=0.3: 1
d=0 L=5 g=2.0: card=1, fixed pt m=-0.075638+0.776203j, residual=9.0e-16, real-axis roots at E=0.3: 1
```

Reading of the output (script values only):
- `m(i,10) = 0.25135 i` (`Re m = 3.5e-16`), residual of `(self_m)` through the explicit `64 x 64` inverse `5.4e-16`, `|tr M - Σ(v-(z+m))⁻¹| = 2.8e-14` (4a), `X = 0.20086 = Im m/(Im m + Im z)` (Ward), exactly one root with `Im m > 0` (4c, 4d at `Im z > 0`); the 64 eigenvalues equal `20 Σ_j cos(π k_j/2)` to `3.7e-14`.
- Flow point of `w = 6i/5`: `z = 0.93803 i`, `m_w = 0.26197 i`, `t₀ = 0.218307`, `g₀ = 4.67234`, `E = 0`, `m₀ = 0.56068 i`, real-axis residual `1.1e-16`, `X₀ = 1.0` (`Im z = 0`: Ward with `X = 1`), `|z_{t₀} - √t₀ z| = 1.1e-16`, `max|√t₀ M₀ - M| = 1.4e-15` (clause 4 of `BAzztE_data`), one real-axis root (4d at `Im z = 0`).  Flow point of `w = 1/2 + 6i/5`: `E = 0.42853 ≠ 0`, `m₀ = -0.21277 + 0.51782 i`, residual `1.1e-16`, one root.
- Real-axis scans (`241` energies each over `[min v - 2.5, max v + 2.5]`, 65 starts per energy): `g = 10^{-3}` and the gap case `L = 4`, `g = 10` never give two roots (`0` roots at `50` and `220` energies: outside the support or in a gap, where `BAm = 0`; `1` root at the others).  This is a numerical search, not a proof; the proof is the Hilbert–Schmidt argument above.
- Pin hypotheses not needed: `(d,L,g) = (3,2,-3)`, `(3,1,1/2)`, `(0,5,2)` have a fixed point with residual `≤ 9e-16`, and at most one root on the real axis.

### Verdicts

- Target 1 (vocabulary, `BAspec`): PASS (definitions only; `BAspec` is real-valued, no hypothesis).
- Target 2 (seven pins, stated only): PASS (no theorem assumes them; `BAmExists`, `BAmUniqReal` are proved by 4e).
- Target 3 (17 copied probe theorems): PASS mathematically (their hypotheses are the instance above: `Im w = 6/5 > 1`, `0 < Im z`, `0 < Im m`, `0 < κ ≤ Im m`; their compilation on `main` is stage 1b's task).
- Target 4a `BAMB_trace_eq_sum`: PASS (spectral theorem; `gλ_i - w ≠ 0`).
- Target 4b `BASelf_iff_freeConv`: PASS (`Im(z+m) > 0` from 4a's hypothesis; `n = L^d`).
- Target 4c `BASelf_exists`: PASS (`freeConv_existsUnique` at `t = 1` and 4b).
- Target 4d `BASelf_unique`: PASS (resolvent identity + averaged Ward + Hilbert–Schmidt; no spectral input; every `Im z ≥ 0`).
- Target 4e `baMExists_holds`, `baMUniqReal_holds`: PASS (4c, 4d; pins' `3 ≤ L`, `0 < g` unused).
- Target 4f `BAm_self`, `BAm_eq_freeConvST`, `BAm_real_eq_of_self`, `BAbulk_iff_exists`: PASS (`BAm_spec` + 4c/4d; `isFreeConv51_freeConvST` and the uniqueness half of `freeConv_existsUnique`; `BAbulk_iff` with `huniq` from 4d at `Im z = 0`).
- Instances (ticket list): PASS (the data `(L,g,z) = (4,10,i)`, `zS`, `P.g0`, `P.E` above satisfy every hypothesis).

### (a′) Preflight corrections

None: nothing in section (a) was found wrong while proving (the route of 4d is the one of its table; see the narrative for the one difference in the last step).

## (b) Script output (Mon Oct  5 15:07:58 UTC 2026)

Library file: `/Users/junyin/Lean_proof/RBM3D-wt/T2189/RBM3D/BA/MFixedPoint.lean`, branch `t/T2189`, commit `d397b09`.  Scripts and scratch files: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2189/` (`verify2.py`, `verify3.py`, `axioms.lean`, `precheck.lean`, `mathlib_names.lean`).

### b.1 Build

```
$ lake build RBM3D.BA.MFixedPoint 2>&1 | grep -v "^warning: RBM3D/Defs\|^$\|^Note\|^trace"
⚠ [3305/3331] Replayed RBM3D.Defs.Tail
Build completed successfully (3331 jobs).
$ lake build 2>&1 | tail -1   (full library; the root import of the new module is added by the hub at merge)
Build completed successfully (3992 jobs).
```

### b.2 Axioms (`#print axioms`; the 59 names are the 49 new public names of the ticket and the 10 names of `RBM.BA.MFixedPointInst`)

```
$ lake env lean axioms.lean   (#print axioms of the 49 new public RBM.BA names and the 10 names of RBM.BA.MFixedPointInst)
declarations printed: 59; depending on exactly [propext, Classical.choice, Quot.sound]: 59; others: none
'RBM.BA.BAMB_trace_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BASelf_iff_freeConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BASelf_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BASelf_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMExists_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMUniqReal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_eq_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_real_eq_of_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAbulk_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Statements of the targets against the check file, the probe and the ticket

`python3 verify2.py` (reads the library file, `docs/tickets/checks/T2189-check.lean`, and `git show t/T2161:RBM3D/Probe/T2161Pins.lean`):

```
(A) 21 definitions/pins + BAspec, whitespace-normalised md5, library vs check file: equal 22/22, differing: none
(B) targets 4a-4d, 4f: library statement body vs check `_stmt` body: equal 8/8, differing: none
    4e baMExists_holds: `theorem baMExists_holds (d : ℕ) : BAmExists d` (concludes exactly `BAmExists d`: True)
    4e baMUniqReal_holds: `theorem baMUniqReal_holds (d : ℕ) : BAmUniqReal d` (concludes exactly `BAmUniqReal d`: True)
(C) 17 copied statements, library vs probe t/T2161:RBM3D/Probe/T2161Pins.lean at 82e72b3: equal 17/17, differing: none

Target statements extracted from the library file (binders `(d L : ℕ) [NeZero L]`, 4e `(d : ℕ)`):
theorem BAMB_trace_eq_sum (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    (BAMB d L g z m).trace = ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹
theorem BASelf_iff_freeConv (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m : ℂ), 0 ≤ z.im →
    (BASelf d L g z m ↔ 0 < m.im ∧
      m = ((Fintype.card (Zd d L) : ℕ) : ℂ)⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - z - ((1 : ℝ) : ℂ) * m)⁻¹)
theorem BASelf_exists (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z : ℂ), 0 < z.im →
    ∃ m : ℂ, BASelf d L g z m
theorem BASelf_unique (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m m' : ℂ), 0 ≤ z.im →
    BASelf d L g z m → BASelf d L g z m' → m = m'
theorem BAm_self (d L : ℕ) [NeZero L] :
    ∀ (g : ℝ) (z : ℂ), 0 < z.im → BASelf d L g z (BAm d L g z)
theorem BAm_eq_freeConvST (d L : ℕ) [NeZero L] :
    ∀ (g : ℝ) (z : ℂ), 0 < z.im → BAm d L g z = RBM.Univ.freeConvST (BAspec d L g) 1 z
theorem BAm_real_eq_of_self (d L : ℕ) [NeZero L] :
    ∀ (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → BAm d L g (E : ℂ) = m
theorem BAbulk_iff_exists (d L : ℕ) [NeZero L] :
    ∀ (g κ E : ℝ), 0 < κ →
      (BAbulk d L g κ E ↔ ∃ m : ℂ, BASelf d L g (E : ℂ) m ∧ Real.pi * κ ≤ m.im)
theorem baMExists_holds (d : ℕ) : BAmExists d
theorem baMUniqReal_holds (d : ℕ) : BAmUniqReal d
```

`python3 verify3.py`:

```
17 copied theorems, statement and proof text (whitespace-normalised md5), library vs probe: equal 17/17, differing: none
```

### b.4 Compiled nonempty instances (`d = 3`, `L = 4`, `card (Zd 3 4) = 64`; `g = 10`, `z = i`; `P` the flow point of `(4, 10)`)

```
$ python3 inst_cov.py   (examples in `namespace RBM.BA.MFixedPointInst`: 28; each applies a target theorem; no `sorry`, no hypothesis left open)
target theorems applied by an example: 27 / 27; missing: none
example line numbers per theorem (file lines): BAMB_trace_eq_sum:915; BASelf_iff_freeConv:923; BASelf_exists:907; BASelf_unique:929,934,984; baMExists_holds:898; baMUniqReal_holds:902; BAm_self:909,915,923,929; BAm_eq_freeConvST:911; BAm_real_eq_of_self:937; BAbulk_iff_exists:940; BAimInv_diag:946; BAcolSq_le:950; BAcolSq_ge:954; BAcard_Zd:958; BArow_le:960; BAPsi_isHermitian:946,950,954,964; BAmSubord_im:966; BASelf_subord:970; BAt0_pos:972; BAt0_lt_one:974; BAt0_mul:976; BAzztE_data:978; BAward_avg:980; BAm_spec:902,934,982,989; BAbulk_iff:984; BAdom_real:989; BAg0_le:992

examples of the 10 new theorems (extracted by script from the file):
example : ∃! m : ℂ, BASelf 3 4 10 Complex.I m :=
  baMExists_holds 3 4 (by norm_num) 10 (by norm_num) Complex.I (by simp)
example : BAm 3 4 P.g0 (P.E : ℂ) = P.m0 :=
  baMUniqReal_holds 3 4 (by norm_num) P.g0 P.g0_pos P.E _ _ (BAm_spec ⟨P.m0, P.real.1⟩) P.real.1
example : ∃ m : ℂ, BASelf 3 4 10 Complex.I m := BASelf_exists 3 4 10 Complex.I (by simp)
example : BASelf 3 4 10 Complex.I (BAm 3 4 10 Complex.I) := BAm_self 3 4 10 Complex.I (by simp)
example : BAm 3 4 10 Complex.I = RBM.Univ.freeConvST (BAspec 3 4 10) 1 Complex.I :=
  BAm_eq_freeConvST 3 4 10 Complex.I (by simp)
example : (BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I)).trace
    = ∑ i, ((BAspec 3 4 10 i : ℂ) - (Complex.I + BAm 3 4 10 Complex.I))⁻¹ := by
  refine BAMB_trace_eq_sum 3 4 10 Complex.I _ ?_
  have h := (BAm_self 3 4 10 Complex.I (by simp)).1
  rw [Complex.add_im]
  simp only [Complex.I_im]
  linarith
example : 0 < (BAm 3 4 10 Complex.I).im ∧ BAm 3 4 10 Complex.I
    = ((Fintype.card (Zd 3 4) : ℕ) : ℂ)⁻¹ * ∑ i, ((BAspec 3 4 10 i : ℂ) - Complex.I
      - ((1 : ℝ) : ℂ) * BAm 3 4 10 Complex.I)⁻¹ :=
  (BASelf_iff_freeConv 3 4 10 Complex.I _ (by simp)).mp (BAm_self 3 4 10 Complex.I (by simp))
example : mS 4 10 = BAm 3 4 10 (zS 4 10) :=
  BASelf_unique 3 4 10 (zS 4 10) _ _ (zS_im_pos 4 10).le (selfS 4 10)
    (BAm_self 3 4 10 _ (zS_im_pos 4 10))
example : P.m0 = BAm 3 4 P.g0 (P.E : ℂ) :=
  BASelf_unique 3 4 P.g0 (P.E : ℂ) _ _ (by simp) P.real.1 (BAm_spec ⟨P.m0, P.real.1⟩)
example : BAm 3 4 P.g0 (P.E : ℂ) = P.m0 := BAm_real_eq_of_self 3 4 P.g0 P.E P.m0 P.real.1
example : BAbulk 3 4 P.g0 (P.m0.im / Real.pi) P.E :=
  (BAbulk_iff_exists 3 4 P.g0 (P.m0.im / Real.pi) P.E (div_pos P.real.1.1 Real.pi_pos)).mpr
    ⟨P.m0, P.real.1, le_of_eq (by field_simp)⟩
```

The remaining 17 examples apply the copied theorems at `wI = 6i/5`, `(zS 4 10, mS 4 10)` and `P` (lines 946-992 of the file).

### b.5 Registry pre-check, scope, name clashes, ports

```
$ lake env lean precheck.lean   (uncommitted temp file: `import RBM3D`, `import RBM3D.BA.MFixedPoint`, `#assert_rbm_axioms`; DECISIONS §20 (2))
exit code 0
axiom audit: 5498 theorems, 1984 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines of the output mentioning RBM.BA (ledger rows): 0
$ git diff --stat main...t/T2189
 RBM3D/BA/MFixedPoint.lean | 996 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 996 insertions(+)
$ git diff --stat main...t/T2189 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l   (registry and root untouched)
0
$ grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/MFixedPoint.lean
0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/MFixedPoint.lean
0
$ name-clash: for each of the 49 new public names, git grep -nw NAME main -- RBM3D RBM3D.lean   (main = 2a42f07)
names with hits: 0 of 49
$ git grep -n "namespace RBM.BA\|RBM.BA.MFixedPointInst" main -- RBM3D RBM3D.lean | wc -l
0
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Delocalization.lean   (HEAD = 9e0f275)
 RBM2D/Delocalization.lean | 56 +++++------------------------------------------
 1 file changed, 6 insertions(+), 50 deletions(-)
$ git diff --stat 275e275 HEAD -- <the six imported RBM3D files> lean-toolchain lake-manifest.json | wc -l   (probe base unchanged)
0
```

### b.6 Narrative

- Scope: one new file, `RBM3D/BA/MFixedPoint.lean` (996 lines), one commit; `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are untouched (b.5).  `lake build RBM3D.BA.MFixedPoint` and the full `lake build` report `Build completed successfully` (b.1); the hub adds the root import.
- Ported base (probe `t/T2161:RBM3D/Probe/T2161Pins.lean` at 82e72b3): the file is assembled from the probe lines `:45-176` (section 0), `:177-366` (section 1), `:374-418` (`BAm`, `BArho`, `BAward_avg`), `:437-440` and `:450-550` (bulk set, `BAm_spec` ... `BATheta0`), `:558-653` (the seven pins).  Not copied: `:441-449` (`BAedgeBulk`, `BAsuppSet`, `BAdistBulk`, DECISIONS §51) and everything after `:655`.  The docstrings of 19 definitions (17 of them the check file's text; `BAmExists`, `BAmUniqReal` reworded to "Proved by ...") replace the probe's.  The 17 copied theorems have the same statement and proof text as the probe (b.3) and compiled without repair.
- Instance data `wI` ... `exists_flowPt` is copied from probe `:1897-1946` into `RBM.BA.MFixedPointInst`; `P` is `(exists_flowPt 4 (g := 10) _).some`.  `wI_im` is private under the name `MFixedPoint_wI_im`; `fp`, `fp_kappa_pos`, `mS_im_lower`, `mS_im_upper`, `zS_add_mS_im` are not copied.
- New proofs.  4a: private `MFixedPoint_inv_spectral` (`(gΨ - w)⁻¹ = U diag((gλ - w)⁻¹) U*`, via `Matrix.inv_eq_right_inv`), then trace cyclic and `trace_diagonal`; the model is the private `RBM.Univ.InjSum_green_eq_spectral` (`RBM3D/Universality/InjSum.lean:43`; RBM2D `Delocalization.lean:47` at `c9a24cf`), whose proof is adapted to the scaled eigenvalues.  4b: `and_congr_right`, 4a, `BAcard_Zd`.  4c: `freeConv_existsUnique (BAspec d L g) (t := 1)` and 4b.  4d: for `m ≠ m'` the resolvent identity gives `tr (M M') = L^d`; `BAward_avg` gives `Σ|M_{ba}|² ≤ L^d` for both; the private `MFixedPoint_HS` (expansion of `Σ|M_{ab} - conj M'_{ba}|²`) gives `Σ|M_{ab} - conj M'_{ba}|² ≤ 0`, so `M_{ab} = conj M'_{ba}` for all `a, b`; the trace then gives `m = conj m'`, contradicting `Im m, Im m' > 0`.  This ends through the trace and not through `w₁ = conj w₂` as in the ticket's route; it has no case split on `Im z`.  4e: from 4c, 4d.  4f: as in the ticket (`BAm_spec`, `isFreeConv51_freeConvST`, `BAbulk_iff` with `huniq` from 4d).
- Hypotheses actually used: 4a-4d and 4f hold for every `L` with `NeZero L`, every real `g` (any sign) and every `d` (no `3 ≤ d`).  In `baMExists_holds`, `baMUniqReal_holds` the pin's `3 ≤ L` is used only to build `NeZero L` and `0 < g` is not used; the pins are unchanged.
- No theorem of the file assumes a pin; `BAmBoundary`, `BAWard`, `BAPropM`, `BAoffDiag`, `BAImmLower` are stated only (owed rows BA-D6, BA-D3, BA-D4, BA-D7 of the ticket).
- Section (a) of this report was written at 14:53:59 UTC and this stage started at 14:55:06 UTC (`date -u`); the numbers of (a) (`t₀ = 0.2183`, `g₀ = 4.672`, `κ = 0.178` at `P`) are not used by any proof: the instances use the Lean-defined `P`.

## (c) Verified Mathlib names (`#check` in `mathlib_names.lean`, exit 0, 27 of 27 resolve; all are used by the new proofs)

- Spectral bridge: `Matrix.IsHermitian.spectral_theorem`, `Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.eigenvectorUnitary`, `Unitary.coe_star_mul_self`, `Unitary.coe_mul_star_self`.
- Inverses: `Matrix.inv_eq_right_inv`, `Matrix.nonsing_inv_eq_ringInverse`, `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`.
- Matrices and traces: `Matrix.trace_mul_comm`, `Matrix.trace_diagonal`, `Matrix.diagonal_mul_diagonal`, `Matrix.diagonal_one`, `Matrix.trace_sub`, `Matrix.trace_smul`.
- Sums and inequalities: `Finset.sum_eq_zero_iff_of_nonneg`, `Finset.sum_comm`, `inv_mul_le_iff₀`, `le_of_mul_le_mul_left`, `pow_eq_zero_iff`, `sub_sub_sub_cancel_left`.
- Complex numbers: `Complex.sq_norm`, `Complex.normSq_apply`, `Complex.re_sum`, `Complex.natCast_re`, `Complex.conj_natCast`, `Complex.conj_im`.
- Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates

- No open issue on the targets.  BA-D1b (probe sections 4-7, re-pinned over the BA law, §57 (3)) is not in this file, as the ticket says.
- `T2189a` (paper `1_2:626-629`, `1_2:715`): the paper states uniqueness of `m(z)` in `C_+` and uses `m(E) = m(E + i0)` without stating real-axis uniqueness.  The file proves `BASelf_unique` for every `Im z ≥ 0` (the real axis included), every `L ≥ 1`, every real `g`; `BAm` at a real `E` is that unique real-axis solution (`0` if none, a gap: `BAm_real_eq_of_self`); the identification with the boundary value `m(E + i0)` is the owed pin `BAmBoundary`.
- `T2189b` (paper `1_2:626-629`, `1_2:615`, `1_2:631`): `(self_m)` of the paper is `N⁻¹ tr` over the fine `N x N` matrix; `BASelf` states it on the block lattice as `L^{-d} tr M^{(B)}` (`Ψ = Ψ^{(B)} ⊗ I_{W^d}`); the equality of the two normalised traces is not proved in this file.
- The pins `BAmExists`, `BAmUniqReal` assume `3 ≤ L` and `0 < g` which `baMExists_holds`, `baMUniqReal_holds` do not need (reported, not changed, as the ticket instructs).

