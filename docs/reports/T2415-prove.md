Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 09:17 UTC 2026

No new mathematics: T8-BA is the transport of the band instances `bandStep2Mat`/`bandStep2Data` (`Chain/Step2Gen.lean:128-145`)
to the carrier `baFM`/`baFMz` (`BA/FlowPins.lean:321-330, 393`). Paper refs of the objects: (Eq:defGLoop) `1_2:824`, (self_Gt) `1_2:725`,
(def_G0) `1_2:631`, (MBM) `1_2:686`, (eq:t0E0_BA) `7_8:1798`.

### (i) Exponent table and field table

Constants of the targets (`d = 3` only; `3 ≤ d` is a hypothesis of the generic Step 2, not of the carrier):

| quantity | value at the instance | constraint | slack (n = 0 / all n) |
|---|---|---|---|
| `κ` | 1/2 | `0 < κ` (`flowOK_T`); `κ ≤ Im m(z_n, g_n)` (`BAdom`, `BA/MFixedPoint.lean:435`) | `Im m = 0.8325` (n=0); Lean: `4/5 ≤ Im m` all n (`mS_im_half`, `FlowPins:1147`, used in `flow_sz0` `:1214`) |
| `ε` | 1/10 | `N^{-1+ε} ≤ Im z_n ≤ 1` | `N^{-0.9} = 2.0e-6 ≤ 0.3675`; Lean: `Im z_n ∈ [11/30, 7/10]` (`zSeq_im_ge/le`) |
| `𝔠` | 1/6 | `N^𝔠 ≤ W` (`Bandwidth`, `Defs/Sizes.lean:168`) | `N^{1/6} = 11.31 ≤ 32` (n=0) |
| `𝔡` | 1/10 | `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` (`WO`, `Sizes.lean:164`) | `W^{-1.4} = 7.8e-3 ≤ g = 1.56e-2 ≤ 10` |
| `t₀_n` | 0.6937 (n=0) | `0 < t₀ < 1` (`BAt0_pos/_lt_one`, `MFixedPoint:282-285`, needs `Im z > 0`, `Im m > 0`) | Lean: `2/3 ≤ t₀_n < 1` (`t0_sz0`, `FlowPins:1227`) |
| `g₀_n = √t₀ g` | 1.30e-2 (n=0) | `lam0 = BAflowLam0 sz z` (`FlowPins:386`) | `0 < g₀ ≤ g ≤ 𝔡⁻¹` since `0 < t₀ < 1` |
| `E_n` | 1.8e-18 (n=0) | `E = BAflowEs sz z` (`:383`), no range constraint | none needed |
| `0 ≤ s ≤ t ≤ T0` | not part of the carrier | belongs to the generic Step 2 (T1/T7) | n/a |

Field table of `Step2Mat sz` / `Step2Data sz` (BA definition; every type checked against `Step2Gen:77-110`, by reading the signatures). Notation:
`z_u := ztOf (BAmF sz lam0 E n) (E n) u` (`ztOf m E t = E + (1-t) m`, `Loop/GLoopFlow.lean:55`), `H : Matrix (Idx d (sz.L n) (sz.W n))²  ℂ`.

| field | BA value | source file:line | type check |
|---|---|---|---|
| `toFlowFM` | `baFM sz lam0 E` | `FlowPins:322` | `FlowFM sz` |
| `LM n u {k} H σ a` | `loopFine d (sz.L n) (sz.W n) H z_u σ a` | `BALloop` `FlowPins:264` with `seqHflowBA lam0 n t ω` replaced by `H` | `ℂ`; `BALloop sz lam0 E n t σ a ω` is this at `H = sz.seqHflowBA lam0 n t ω` (`rfl`) |
| `GMM n u H x y` | `Gres H z_u true x y - BAMfine sz lam0 E n x y` | `BAGt` `:259`, `BAMfine` `:255`, `BAGM` `:305` | `ℂ`; `BAGM = BAGt - BAMfine` at `H = seqHflowBA` |
| `LIM n u H I` | `loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) z_u I` | mirrors `STLIM` `Induction/Step2Defs.lean:713`, with `z_u` for `zt E τ`; `loopL` `GLoopFlow:123`, `blockMat` `:105` | `LoopIdx (Zd d (sz.L n)) → ℂ` |
| `KI n u I` | `BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n))) (PropSpin (BAmF sz lam0 E n)) u I` | `BAKsol` `:283`; `BAKloop` `:298-301` is this at `I = KLloopOf d (sz.L n) σ a` (`rfl`) | `ℂ` |
| `Pp` | `pathP (sz.withLam 0)` (BAT-C1) | `Path/Walk.lean:58` | needs `Measure (PathΩ sz)`; `PathΩ` is an `abbrev` of `ℕ → SeqΩ`, and `(sz.withLam 0).L = sz.L`, `.W = sz.W` by unfolding `withLam` (`Defs/Sizes.lean:182`); same unification as the merged `BAStep2` (`FlowPins:432`, `Sizes.seqP (sz.withLam 0)` against `Measure sz.SeqΩ`). Fallback in 1b: `show`/`@pathP`. |
| `Hpath s t K n k ω` | `((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + pathH (sz.withLam 0) s t K n k ω` (BAT-C1) | `seqHflowBA` `Gauss/BlockAnderson.lean:81-84` (`(lam0 n : ℂ) • PsiI + …`); `pathH` `Path/Walk.lean:75` | `Matrix (Idx d (sz.L n) (sz.W n))² ℂ`; `ω : PathΩ sz` passed to `pathH (sz.withLam 0)` (same defeq as `Pp`) |
| `T0` | `BAflowT0 sz z` | `FlowPins:380` | `ℕ → ℝ` |
| `flowOK κ ε 𝔠 𝔡` | `BAFlow sz κ ε 𝔠 𝔡 z` | `FlowPins:389` | `ℝ → ℝ → ℝ → ℝ → Prop` |

`baStep2Data sz z`: `toStep2Mat := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`, so `toFlowFM = baFM sz (BAflowLam0 sz z) (BAflowEs sz z) = baFMz sz z` is `rfl` (`baFMz` is that definition, `FlowPins:393`).

### (ii) Concrete nondegenerate instance and proof plan of the three facts

Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), `z = zSeq`
(`z_n = w - m_S`, `w = 6i/5`, `FlowPins:1181`, `MFixedPoint:849-868`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`. The merged `FlowPinsInst.flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
(`FlowPins:1214`) already proves every hypothesis of `flowOK`. Numeric check (independent of Lean; `Ψ^{(B)}` spectrum on `Z_L^3` is `Σ_i 2cos(2πk_i/L)`, `Adj` = `ℓ¹`-distance 1, `Lattice.lean:108`):

```
$ python3 -I .../scratchpad/T2415/inst.py
n=0 L=4 W=32 N=2097152 g=1.562e-02 Im m=0.8325 Im z=0.3675 Re m=-1e-18 res=0e+00 T0=0.6937 (<1:True) lam0=1.301e-02 E=1.79e-18 N^-0.9=2.0e-06 Adm(W>=N^c,WO)=(True, True) BAdom=(True, True)
n=1 L=8 W=1024 N=549755813888 g=2.441e-04 Im m=0.8333 Im z=0.3667 Re m=-6e-20 res=0e+00 T0=0.6944 (<1:True) lam0=2.035e-04 E=6.63e-20 N^-0.9=2.7e-11 Adm(W>=N^c,WO)=(True, True) BAdom=(True, True)
n=2 L=12 W=7776 N=812479653347328 g=2.143e-05 Im m=0.8333 Im z=0.3667 Re m=3e-21 res=0e+00 T0=0.6944 (<1:True) lam0=1.786e-05 E=-3.55e-21 N^-0.9=3.8e-14 Adm(W>=N^c,WO)=(True, True) BAdom=(True, True)
n=5 L=24 W=248832 N=212986666247081951232 g=3.349e-07 Im m=0.8333 Im z=0.3667 Re m=1e-22 res=0e+00 T0=0.6944 (<1:True) lam0=2.791e-07 E=-1.16e-22 N^-0.9=5.1e-19 Adm(W>=N^c,WO)=(True, True) BAdom=(True, True)
```
(`res` is the residual of `(self_m)` at `(z_S, m_S)`; it is 0 because `z_S + m_S = w` makes the two sides the same expression, the identity behind `selfS`, `MFixedPoint:870`. `BAm sz0 zSeq = mS` is `BAm_zSeq`, `FlowPins:1189`.) `W ≥ N^{1/6}` and `WO` hold for all n in Lean (`sz0_admissible`, `Defs/Sizes.lean:331`, used in `flow_sz0`).
The instance is nondegenerate: `n = 0` has `L = 4`, `W = 32`, `N = 2097152`, `g = 1/64 ≠ 0`, `0 < t₀ < 1`. No external hypothesis occurs (`BAm`, `BAStep2` content is not assumed), so no limit computation is needed.

Planned compiled instances (target 6): `example : (baStep2Data sz0 zSeq).flowOK (1/2) (1/10) (1/6) (1/10) := flow_sz0`;
`example (n) : (baStep2Data sz0 zSeq).T0 n < 1 := (baStep2Data sz0 zSeq).flowOK_T (by norm_num) flow_sz0 n` (with `T0 n = BAflowT0 sz0 zSeq n` by `rfl`).

Proof plan of the three facts:
1. `flowOK_adm := fun h => h.1` (first conjunct of `BAFlow`, `FlowPins:389-390`).
2. `flowOK_T := fun hκ h n => BAt0_lt_one hz hm`, `BAflowT0 sz z n = BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))` by unfolding (`FlowPins:380`). `hm : 0 < (BAm …).im` from `lt_of_lt_of_le hκ (h.2 n).1` (`BAdom` first conjunct, `κ ≤ Im m`). `hz : 0 < (z n).im` from `(h.2 n).2.1 : (sz.size n)^{-1+ε} ≤ (z n).im` and `Real.rpow_pos_of_pos` with `0 < sz.size n` (`sz.one_le_size n`), exactly as `Step2Gen_flow_im_pos` (`Step2Gen:122-125`). `BAm_im_lower` (`ImmLower:391`) is not needed, since `κ ≤ Im m` is already in `BAdom`.
3. `L_swap`: the left side `(baFM …).L n t ![true,false] ![a,b] ω` unfolds to `loopFine d (sz.L n) (sz.W n) (seqHflowBA …) z_t ![true,false] ![a,b]`, whose swap is the model-free trace cyclicity of `Step2Gen_loopFine_swap` (`Step2Gen:114`, any `H`, `z`). Reuse by `open private Step2Gen_loopFine_swap from RBM3D.Chain.Step2Gen` (the form already used at `Chain/NewKLKGen.lean:38-40`); no re-proof.

Bridges (target 3), all by unfolding: `(baStep2Data sz z).toFlowFM = baFMz sz z` and `(baStep2Data sz z).T0 = BAflowT0 sz z` are `rfl`. `BAStep2 d ↔ STStep2G d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => (baStep2Data sz z).flowOK κ ε 𝔠 𝔡) (fun sz z => (baStep2Data sz z).toFlowFM) (fun sz z => (baStep2Data sz z).T0)`
should be `Iff.rfl`: `BAStep2 d` unfolds to `STStep2G d … BAFlow baFMz BAflowT0` (`FlowPins:432`, `rfl` example at `:1430`), and the three projections of the explicit structure `baStep2Data sz z` reduce to `BAFlow sz κ ε 𝔠 𝔡 z`, `baFMz sz z`, `BAflowT0 sz z`.

### (iv) Target 4: the energy family

The pins `STNewKLKgL`/`STNewKLKgL'` (`Step2Gen:903`, `NewKLKGen:69`) and `STK2decaygL` (`Step2Gen:907`) take `mk : ∀ sz, (ℕ → ℝ) → Step2Mat sz` and use `mk sz (fun _ => E)`, for every `sz` with `0 < sz.lam n ≤ 𝔡⁻¹`. At BA the flow coupling `g₀_n = √t₀ g_n` depends on `z`, but the pins quantify over all `sz`, so the coupling can be carried by `sz`:

proposed one-line `def`: `baStep2Fam (sz : Sizes d) (E : ℕ → ℝ) : Step2Mat sz := baStep2Mat sz sz.lam E`.

Use at the flow `z`: apply the pin at `sz' := sz.withLam (BAflowLam0 sz z)`; then `(baStep2Fam sz' E).K = (baFM sz (BAflowLam0 sz z) E).K` by `rfl` (`sz'.lam = BAflowLam0 sz z` by `withLam`, `sz'.L = sz.L`, `sz'.W = sz.W`, and `sz'.withLam 0 = sz.withLam 0` by structure eta). The pin hypotheses at `sz'`: `0 < sz'.lam n` and `sz'.lam n ≤ 𝔡⁻¹` follow from `0 < t₀ < 1` (table) and `WO` for `sz`. `(baStep2Fam sz E').m n = BAm d (sz.L n) (sz.lam n) E` at the constant sequence, which is the datum `κ ≤ Im m` of the primed pins (`NewKLKGen:55`).
Rejected: `lam0 := BAflowLam0 sz (E + iη)` (needs a second parameter `η`, not in `mk`'s type).
Record for T3-BA (BAT-F1/F2): `STK2decaygL` has the band domain `|E| ≤ 2 - κ`; at BA the primed form with `κ ≤ Im m` is needed (supervisor 0853, BAT-F2, not re-verified here). I propose to define `baStep2Fam` in `Step2BA.lean` (it is a one-line `def`).

### Verdicts

- Target 1 (`baStep2Mat`, with BAT-C1): PASS. All eight fields have a BA definition with the checked type. Only open point: the `Pp`/`Hpath` `PathΩ (sz.withLam 0)` vs `PathΩ sz` unification (defeq by unfolding, same as the merged `BAStep2`); fallback `show`.
- Target 2 (`baStep2Data` and the three facts): PASS (proof plan above; every input is a merged lemma).
- Target 3 (bridges): PASS.
- Target 4 (`baStep2Fam`): PASS (one-line def).
- Target 6 (instances): PASS (`flow_sz0` is merged; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`).

### (a′) Preflight corrections — Sun Oct 11 09:25:08 UTC 2026
Neither changes a verdict (targets 1-4 are delivered). Evidence: the first builds of 1b (tool log).
1. (iv) `(baStep2Fam sz' E).toFlowFM = baFM sz (BAflowLam0 sz z) E` "by `rfl`" at `sz' = sz.withLam lam0` is not a typed statement:
   `error: RBM3D/BA/Step2BA.lean:154:48: Type mismatch  baFM sz lam0 E  has type  FlowFM sz  but is expected to have type  FlowFM (sz.withLam lam0)`.
   Field-wise it compiles: `baStep2Fam_K`, `baStep2Fam_m` (below).
2. (iv) "`0 < sz'.lam n`, `sz'.lam n ≤ 𝔡⁻¹` follow from `WO`": `WO` (`Sizes.lean:164`) is eventual in `n`, so they hold at the `n` with
   `0 < g_n ≤ 𝔡⁻¹`. Compiled: `baStep2Fam_lam_pos_le` (`0 < g_n → 0 < g₀_n ≤ g_n`, from `BAt0_pos`, `BAg0_le`).
3. (i) `Hpath`: the ascription `(pathH (sz.withLam 0) … : Matrix …)` fails (`failed to synthesize HAdd (Matrix (Idx d (sz.L n) …) ℂ) (Matrix (Idx d ((sz.withLam 0).L n) …) ℂ)`);
   `show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from pathH (sz.withLam 0) …` works (the fallback of (a)). `Pp` needed none.

## (b) Script output — Sun Oct 11 09:25:08 UTC 2026

```
$ wc -l RBM3D/BA/Step2BA.lean   (stop line 900)
     209 RBM3D/BA/Step2BA.lean
$ lake build RBM3D.BA.Step2BA | tail -1
Build completed successfully (3737 jobs).
$ lake build (full, worktree, with import RBM3D.BA.Step2BA in RBM3D.lean; saved log)
Build completed successfully (4225 jobs).
$ lake env lean docs/tickets/checks/T2415-check.lean; echo $?
0
$ #print axioms of the 16 public declarations: standard three / other
16
0
$ grep -c "sorry\|admit\|native_decide\|^axiom" Step2BA.lean
0
$ grep -rln "baStep2\|BAStep2_iff_STStep2G\|Step2BAInst\|Step2BA_" RBM3D RBM3D.lean   (name clash)
RBM3D/BA/Step2BA.lean
$ git diff --stat main...t/T2415
 RBM3D.lean            |   1 +
 RBM3D/BA/Step2BA.lean | 209 ++++++++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 210 insertions(+)
--- field table as written: baStep2Mat (comments dropped), baStep2Data ---
54:def baStep2Mat {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : Step2Mat sz where
55:  toFlowFM := baFM sz lam0 E
57:  LM := fun n u {_k} H σ a => loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz lam0 E n) (E n) u) σ a
59:  GMM := fun n u H x y => Gres H (ztOf (BAmF sz lam0 E n) (E n) u) true x y - BAMfine sz lam0 E n x y
61:  LIM := fun n u H I =>
62:    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) I
64:  KI := fun n u I =>
65:    BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
66:      (PropSpin (BAmF sz lam0 E n)) u I
68:  Pp := pathP (sz.withLam 0)
70:  Hpath := fun s t K n k ω =>
71:    ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) +
72:      (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from pathH (sz.withLam 0) s t K n k ω)
def baStep2Data {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Step2Data sz where
  toStep2Mat := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)
  T0 := BAflowT0 sz z
  flowOK := fun κ ε 𝔠 𝔡 => BAFlow sz κ ε 𝔠 𝔡 z
  flowOK_adm := fun h => h.1
  flowOK_T := fun hκ h n => Step2BA_T0_lt_one hκ h n
  L_swap := fun n t a b ω => Step2Gen_loopFine_swap _ _ a b
--- bridge (Iff.rfl), energy family, rfl bridges named in the file ---
144:theorem BAStep2_iff_STStep2G (d : ℕ) :
145-    BAStep2 d ↔ STStep2G d (fun sz => Sizes.seqP (sz.withLam 0))
146-      (fun sz κ ε 𝔠 𝔡 z => (baStep2Data sz z).flowOK κ ε 𝔠 𝔡) (fun sz z => (baStep2Data sz z).toFlowFM)
147-      (fun sz z => (baStep2Data sz z).T0) := Iff.rfl
148-
157:def baStep2Fam {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : Step2Mat sz := baStep2Mat sz sz.lam E
160:theorem baStep2Fam_K {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) :
161-    (baStep2Fam (sz.withLam lam0) E).K = (baFM sz lam0 E).K := rfl
164:theorem baStep2Fam_m {d : ℕ} (sz : Sizes d) (E : ℝ) (n : ℕ) :
165-    (baStep2Fam sz (fun _ => E)).m n = BAm d (sz.L n) (sz.lam n) (E : ℂ) := rfl
--- compiled nonempty instances (d = 3, sz0, zSeq), doc lines dropped ---
184:example : (baStep2Data sz0 zSeq).flowOK (1 / 2) (1 / 10) (1 / 6) (1 / 10) := flow_sz0
187:example (n : ℕ) : (baStep2Data sz0 zSeq).T0 n < 1 :=
188-  (baStep2Data sz0 zSeq).flowOK_T (by norm_num) flow_sz0 n
191:example : 2 / 3 ≤ (baStep2Data sz0 zSeq).T0 0 ∧ (baStep2Data sz0 zSeq).T0 0 < 1 :=
192-  ⟨t0_sz0 0, (baStep2Data sz0 zSeq).flowOK_T (by norm_num) flow_sz0 0⟩
195:example : sz0.Admissible (1 / 6) (1 / 10) := (baStep2Data sz0 zSeq).flowOK_adm flow_sz0
198:example (a b : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) (t : ℝ) :
199-    (baStep2Data sz0 zSeq).L 0 t ![true, false] ![a, b] ω = (baStep2Data sz0 zSeq).L 0 t ![false, true] ![b, a] ω :=
200-  (baStep2Data sz0 zSeq).L_swap 0 t a b ω
203:example (n : ℕ) : 0 < (sz0.withLam (BAflowLam0 sz0 zSeq)).lam n ∧
204-    (sz0.withLam (BAflowLam0 sz0 zSeq)).lam n ≤ sz0.lam n :=
205-  baStep2Fam_lam_pos_le (by norm_num) flow_sz0 n (sz0_lam_pos n)
```

**Narrative** (Sun Oct 11 09:25:50 UTC 2026)
- Delivered: `baStep2Mat` (field table above; BAT-C1 `Pp`, `Hpath`), `baStep2Data` (three facts), the `rfl` bridges
  (`baStep2Mat_toFlowFM/_LM/_GMM/_KI/_Hpath/_Pp`, `baStep2Data_toFlowFM/_T0/_flowOK`), `BAStep2_iff_STStep2G` (`Iff.rfl`, no fallback needed),
  `baStep2Fam` (one-line def) with `baStep2Fam_K/_m/_lam_pos_le`. Imports: `RBM3D.BA.FlowPins`, `RBM3D.Chain.Step2Gen`; no drift kernel (T2414).
- `L_swap`: `open private Step2Gen_loopFine_swap from RBM3D.Chain.Step2Gen` (reused, not re-proved). `flowOK_T`: two private helpers
  (`Step2BA_flow_im_pos`: `0 < Im z_n` from `N^{-1+ε} ≤ Im z_n`; `Step2BA_T0_lt_one`: `BAt0_lt_one` with `0 < Im m` from `κ ≤ Im m` in `BAdom`);
  `BAm_im_lower` was not needed. `flowOK_adm` is `h.1`.
- Root import: one line `import RBM3D.BA.Step2BA` after the last import of `RBM3D.lean` (the ticket lists `RBM3D.lean` as sole writable); `#assert_rbm_axioms`
  is still last; the full `lake build` above passes with it. No module under `RBM3D/` imports `Step2BA` (only the root `RBM3D.lean` does).
- Instances: six `example`s at `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`), `zSeq`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`; the merged `flow_sz0`
  discharges `BAFlow`, so every deterministic hypothesis is discharged; no external pin occurs. They cover `flowOK`, `flowOK_T` (all `n`, and `2/3 ≤ T0 0 < 1`),
  `flowOK_adm`, `L_swap` (at `n = 0`), and `baStep2Fam_lam_pos_le`.
- Target 4 (record for T3-BA, BAT-F1): `mk := fun sz E => baStep2Fam sz E`, `baStep2Fam sz E = baStep2Mat sz sz.lam E`; at the flow `z` apply the pin at
  `sz' := sz.withLam (BAflowLam0 sz z)`: then `(baStep2Fam sz' E).K = (baFM sz (BAflowLam0 sz z) E).K` (`baStep2Fam_K`, `rfl`), `.m n = BAm d (sz'.L n) (sz'.lam n) E`
  (`baStep2Fam_m`), and `0 < sz'.lam n ≤ sz.lam n` (`baStep2Fam_lam_pos_le`; the pin range `sz'.lam n ≤ 𝔡⁻¹` follows from `sz.lam n ≤ 𝔡⁻¹`, which `WO` gives eventually).
- Report length: 191 lines (`wc -l`): over the ticket's 150 because section (a) alone is 85 lines; within CLAUDE.md §6's 300.

## (c) Verified names (`#check`, tool log)
`Real.rpow_pos_of_pos`, `Real.sqrt_pos`, `mul_pos`, `lt_of_lt_of_le` (Mathlib); `RBM.BA.BAt0_pos`, `BAt0_lt_one`, `BAg0_le`, `RBM.Gauss.Sizes.one_le_size`,
`RBM.BA.FlowPinsInst.sz0_lam_pos` (`FlowPins:1184`), `flow_sz0`, `t0_sz0` (`FlowPins:1214, 1227`). Verified absent: none checked.

## (d) Open issues and paper-delta candidates
- For T3-BA: `STK2decaygL` (`Step2Gen:907-911`) has the band domain `|E| ≤ 2 - κ`; supervisor 0853 BAT-F2 (`:168`, O6 `:220`) asks for a primed
  `STK2decaygL'` with premise `κ ≤ Im m`; the analogous primed `STNewKLKAtgL'` is `NewKLKGen:53-55`. `WO` is eventual, so the pins at `sz'` apply for the `n` with `0 < g_n ≤ 𝔡⁻¹`.
- Not here, as the ticket says: the eleven open Step 2 obligations (hypotheses of T1-BA/T7-BA), the pin `BAStep2 d` itself, the drift kernel (T8b).
- Sibling scan: this branch is based on main `260732c`, where `Step2Mat` has the eight fields of (i) (`Step2Gen:77-93`); if T2414 changes `Step2Mat`, rebase.
- Paper-delta candidates: none (the carrier changes no paper statement; `Hpath`/`Pp` follow `seqHflowBA`, `BlockAnderson:83-86`).
