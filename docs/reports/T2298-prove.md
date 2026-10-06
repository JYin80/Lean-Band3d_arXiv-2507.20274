Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 13:31:37 UTC 2026

Targets (UN-42, ticket T2293b read as T2298): `mixCq_pos`, `mixBad_tail`, `mixEntry_event_subset`, `mixEntry_union`, `gueEntryMix`
(pins: `docs/tickets/checks/T2298-check.lean` §2 "T2293b"). Source facts below were read from RBM3D `Defs/Sizes.lean`,
`Universality/GUEPhase/EntryDet.lean`, `Universality/GUEPhase/EntryTail.lean`, `Green/Stability.lean`, `Green/IBPPoly.lean`,
and RBM2D `EntryTail.lean` (c9a24cf :884, :1008, :1470 for `mixCq`, `mixBad_tail`, `gueEntryMix`).

### (i) Exponent table

Notation: `N = sz.size n = (W L)^d`, `Λ = 𝔡⁻¹`, `τ' = min(τ/4, c₀)`, `Φ = N^{τ'}`, `T = N^τ`, `Cq = mixCq q`.
`Ks := Kstab3 d Λ κ` is a `Classical.choose` constant of `prop5Short_holds` (`Green/Stability.lean:194-214`): it has no
numeric value and enters only through `mixDelta` and `mixCdet`; `mixK = Ks (1 + 1/gapK κ)`, `mixDelta = min(1/2, 1/(2 mixK), mixC/2)`,
`mixCdet = (2160 mixK² + 162)(1 + 3/mixC)`, `mixC κ = √(2κ)/2`, `gapK κ = min(1, √(κ(4-κ)/2))`. Every row is `L`-free.

| quantity | value / choice | constraint | slack |
|---|---|---|---|
| `τ'` | `min(τ/4, c₀)` | `0 < τ' ≤ c₀`, `τ' ≤ τ/4` | `c₀ - τ' ≥ 0`, `τ/4 - τ' ≥ 0`, one of the two is 0 |
| `Φ ≥ 2` (union needs `2 ≤ Φ`; subset needs `1 ≤ Φ`) | `N^{τ'}` | `N ≥ 2^{1/τ'}` | eventually, from `SizeTendsto` |
| `36 Φ δ² ≤ 1` | `δ ≤ N^{-c₀}`, `τ' ≤ c₀` | `36 N^{τ'-2c₀} ≤ 36 N^{-c₀} ≤ 1`, needs `N ≥ 36^{1/c₀}` | exponent slack `c₀ - τ' ≥ 0` (extra), then `N^{c₀} ≥ 36` |
| `δ ≤ mixDelta d Λ κ` | `δ ≤ N^{-c₀}` | `N ≥ mixDelta⁻¹^{1/c₀}`; `mixDelta > 0` (`mixDelta_pos`, needs `κ ≤ 2`) | eventually, constant fixed before `n` |
| `κ ≤ 2` | from `|E 0| ≤ 2-κ` | `κ ≤ 2 - |E 0|` | `2 - κ ≥ 0` |
| `Φ² ≤ N^{τ/2}` | `N^{2τ'}` | `2τ' ≤ τ/2` | `τ/2 - 2τ' ≥ 0` (= 0 iff `τ' = τ/4`) |
| `mixCdet ≤ N^{τ/2}` | constant | `N ≥ mixCdet^{2/τ}` | eventually |
| `T ≥ mixCdet Φ²` | `T = N^{τ/2}·N^{τ/2} = N^τ` | `mixCdet Φ² ≤ N^{τ/2}·N^{τ/2}` | 0 by design |
| `q` | least `q` with `τ'(q+1) ≥ D + n0 + 3` | `q = ⌈(D+n0+3)/τ'⌉ - 1` | `τ'(q+1) - (D+n0+3) ∈ [0, τ')` |
| `K+1 ≤ 2N^{n0}` | `K ≤ N^{n0}`, `N ≥ 1` | | `N^{n0} ≥ 1` |
| union arithmetic | `(K+1)·4N²·Cq/N^{τ'(q+1)} ≤ 2N^{n0}·4N²·Cq/N^{D+n0+3} = 8Cq/N^{D+1}` | `≤ N^{-D}` iff `N ≥ 8Cq` | exponent 0; the `N` in `D+1` pays the `8 Cq` |
| `mixBad_tail` count | `rows N² + cols N² + quad N + diag N ≤ 4N²` | `N ≥ 1` | `N² - N ≥ 0` |
| `mixCq` common bound (`Λ ≥ 2`) | `4^{q+1}hwConst q + 2^{q+2}(q+1)!` | `Λ/4 ≤ (Λ-1)²`; `2e^{-Λ/2} ≤ 2^{q+2}(q+1)!/Λ^{q+1}` (`exp(Λ/2) ≥ (Λ/2)^{q+1}/(q+1)!`) | `Λ = 2`: `(Λ-1)² = 1 ≥ 1/2 = Λ/4`; slack factor `4^{q+1}` |
| `z = zt E (a+b)`, `Im z ≠ 0` | `Im z = (1-(a+b))·√(4-E²)/2` (`zt_im`, `mE_im`) | `a+b < 1`, `4 - E² ≥ κ(4-κ) > 0` | `1 - (a+b) > 0` |
| coupling window | `0 < sz.lam n ≤ 𝔡⁻¹` | from `WO 𝔡`: `lam ≥ W^{-d/2+𝔡} > 0` since `W ≥ 1`; `lam ≤ 𝔡⁻¹` | eventually in `n` |
| eventual `n` | max of the thresholds above (all `∀ᶠ` via `SizeTendsto`, `eventually_le_rpow`) | `N ≥ max(8Cq, 36^{1/c₀}, 2^{1/τ'}, mixDelta⁻¹^{1/c₀}, mixCdet^{2/τ})` | the threshold is data of the conclusion `∀ᶠ n`, as in the paper's "N large" |
| `W^{-d}` | `(W^d)⁻¹` | enters only as `T·(maxLoopPM + W^{-d})`, `T·W^{-d} ≥ 0` | not used in the proof of the tails |

Event-subset logic (math): `T ≥ 0` (as `mixCdet ≥ 0`, `mixCdet_nonneg`), so `T(maxLoopPM + W^{-d}) ≥ 0`, hence membership forces the `if` to
be the `llErr² ` branch; off `mixBad`, the four LDE bounds hold with `≤`, `mix_det`/`mixEntry_det` gives `llErr² ≤ mixCdet Φ² maxLoopPM ≤ T maxLoopPM`,
contradiction. Needs `0 < sz.lam n ≤ Λ`, `3 ≤ d`, `3 ≤ L` (`sz.three_le_L n`), `a+b ∈ (0,1)`. No statement is false at `d ≥ 3`.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz = sz0` (`L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6}`, so `size n = 2097152 (n+1)^18`),
`(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1`, `E n = 0`, `n0 = 1`, `K n = 2` (three mixtures `(a,b) = (1/2,0), (1/4,1/4), (0,1/2)`, `a+b = 1/2`),
`c₀ = 1/4`, `δ n = N^{-1/4}`, `τ = 1/10`, `D = 2` (the ticket's `inst_entryMix`); single-size pins at `n = 0` (`L=4, W=32, lam=1/64, N=2097152`),
`Λ = 10`, `a = b = 1/4`, `Φ = 2`, `δ := min(mixDelta 3 10 1, 1/12)`, `T := mixCdet 3 10 1 · Φ²` (so `36Φδ² ≤ 1/2`, `mixCdet Φ² ≤ T`, no value of `Ks` needed),
`mixBad_tail` at `Idx 3 3 2`, `g = 1`, `(1/4,1/4)`, `z = zt 0 (1/2)`, `Λ = 2`, `q = 1`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2298/inst.py`

```
n=0 L=4 W=32 N=2097152 lam=1/64 WO ok, N<=W^6 ok
n=1 L=8 W=1024 N=549755813888 lam=1/4096 WO ok, N<=W^6 ok
n=5 L=24 W=248832 N=212986666247081951232 lam=1/2985984 WO ok, N<=W^6 ok
mixBad_tail: Nn=216  a+b=1/2 in (0,1); Im z=(1-1/2)*Im m(0)=1/2*sqrt(4)/2=1/2; Lam=2>=2
  hwConst 1=324 mixCq 1=5200  RHS=4*Nn^2*mixCq/2^2=242611200
ticket instance: c0=1/4 tau=1/10 D=2 n0=1 | tau'=1/40 q=239 tau'(q+1)=6>=D+n0+3=6
   tau'<=c0:True tau'<=tau/4:True 2tau'<=tau/2: True (slack 0)  tau'-2c0=-19/40<=-c0=-1/4
   log10 Cq=1503.3
   Kstab3=1: mixDelta=0.25 mixCdet=4.615e+04 thresholds log10N: delta 2.4, cdet 93.3
   Kstab3=10: mixDelta=0.025 mixCdet=4.53e+06 thresholds log10N: delta 6.4, cdet 133.1
   Kstab3=1000: mixDelta=0.00025 mixCdet=4.53e+10 thresholds log10N: delta 14.4, cdet 213.1
   thresholds log10 N (Kstab3-free):  {'8Cq': 1504.2, '36^(1/c0)': 6.2, "2^(1/tau')": 12.0}
   => N >= 10^1504.2  <=> (n+1) >= 10^83.22 along sz0
   final arith: 8Cq/N^(D+1) <= N^(-D) iff N>=8Cq : equality at N=8Cq: True
light variant: c0=1/4 tau=1 D=1 n0=1 | tau'=1/4 q=19 tau'(q+1)=5>=D+n0+3=5
   tau'<=c0:True tau'<=tau/4:True 2tau'<=tau/2: True (slack 0)  tau'-2c0=-1/4<=-c0=-1/4
   log10 Cq=81.7
   Kstab3=1: mixDelta=0.25 mixCdet=4.615e+04 thresholds log10N: delta 2.4, cdet 9.3
   Kstab3=10: mixDelta=0.025 mixCdet=4.53e+06 thresholds log10N: delta 6.4, cdet 13.3
   Kstab3=1000: mixDelta=0.00025 mixCdet=4.53e+10 thresholds log10N: delta 14.4, cdet 21.3
   thresholds log10 N (Kstab3-free):  {'8Cq': 82.6, '36^(1/c0)': 6.2, "2^(1/tau')": 1.2}
   => N >= 10^82.6  <=> (n+1) >= 10^4.24 along sz0
   final arith: 8Cq/N^(D+1) <= N^(-D) iff N>=8Cq : equality at N=8Cq: True
event_subset/union: 0<lam=1/64<=Lam=10; |E|=0<=2-kappa=1; a+b=1/2; 1<=Phi=2 (union needs 2<=Phi); delta:=min(mixDelta 3 10 1,1/12): 36*2*(1/12)^2=1/2<=1; T:=mixCdet 3 10 1*Phi^2
   size 0 = 2097152 = ((32*4)^3); union RHS (K+1=3): 3*4*N^2*mixCq1/2^2 = 68609525573222400
   Kstab3 = Classical.choose constant: value not computable; all rows symbolic in it (mixDelta>0 by mixDelta_pos, mixCdet finite)
```

Reading of the output (script lines above; `mixK = 2 Ks`, `gapK 1 = 1`, `mixC 1 = √2/2` were used in the script):
* Every deterministic hypothesis of every target holds at the data: `sz0` is admissible at `(1/6, 1/10)` (`WO`: `W^{-7/5} = (2(n+1))^{-7} ≤ lam ≤ 10`;
  `W^6 ≥ N`; `N → ∞`), `0 < lam n ≤ 10` for all `n`, `|E| = 0 ≤ 1`, `a n k + b n k = 1/2 ∈ (0,1)`, `K n = 2 ≤ N^1`, `δ n = N^{-1/4} ≥ 0`, `τ, D > 0`.
* The unproved-constant rows (`mixDelta`, `mixCdet`) hold for every `Ks ≥ 1` (`one_le_Kstab3`), shown at `Ks ∈ {1, 10, 1000}`; they do not affect the dominant threshold.
* The conclusion of `gueEntryMix` is `∀ᶠ n`. At the ticket's `(τ, D) = (1/10, 2)` the exponent chain forces `q = 239` and the eventual size `N ≥ 8 mixCq 239 ≈ 10^{1504}`
  (i.e. `n + 1 ≳ 10^{83}` along `sz0`). This is the paper's "N large", not a hypothesis: the instance applies `gueEntryMix` and obtains an `Eventually` statement.
  Optional lighter data with the same structure: `(τ, D) = (1, 1)`, `q = 19`, `N ≥ 10^{82.6}`.
* The numeric bounds `ofReal (4 N² Cq/Λ^{q+1})` at the `mixBad_tail` and `mixEntry_union` instances exceed 1 (`242611200`, `6.86e16`), so these two instances are true but weak; the
  nondegeneracy is in the data (`Idx 3 3 2`, `Idx 3 4 32` nonempty, `Im z = 1/2 ≠ 0`, `Λ ≥ 2`).
* External hypothesis: none. `gueEntryMix` takes no external input (`mixEntry_det` ← `mix_det` ← `Kstab3`, which is built from the proved theorem `Prop5Short.lean:400 prop5Short_holds`,
  checked present by `grep -rn "theorem prop5Short_holds"`). The limit computation needed for the `∀ᶠ` steps is `N^{-c₀} → 0`, `N^{τ/2} → ∞` for `c₀, τ > 0` (`eventually_le_rpow`, `Defs/Domination.lean:68`) applied to the fixed constants `mixDelta⁻¹`, `mixCdet`, `8 mixCq q`, `2^{1/τ'}`, `36^{1/c₀}`.

### Verdicts

* `mixCq_pos` (and `mixEntry_tail_{row,quad,diag}_le`): PASS (`hwConst_pos`; `mixCq q ≥ 4^{q+1} hwConst q + 2^{q+2}(q+1)! > 0`; arithmetic in the table).
* `mixBad_tail`: PASS (union over `N²` pairs ×2 plus `N` quad plus `N` diag, each `≤ Cq/Λ^{q+1}`, total `≤ 4N² Cq/Λ^{q+1}` with `Λ ≥ 2`, `N = (WL)^d ≥ 1`).
* `mixEntry_event_subset`: PASS (hypothesis set consistent at the instance; logic above).
* `mixEntry_union`: PASS (`(K+1)` events, each preimage of `mixBad` under `mixSample`, measure `≤ 4N² Cq/Φ^{q+1}`, needs `2 ≤ Φ`; `Im z ≠ 0` from `a+b < 1`, `|E| ≤ 2-κ`).
* `gueEntryMix (hd : 3 ≤ d)`: PASS (all exponents close with slack 0 at the stated spots: `τ'(q+1) = D+n0+3`, `2τ' ≤ τ/2`, `N ≥ 8Cq`; no exponent depends on `L` or `d` beyond `N = (WL)^d` and `W^{-d/2+𝔡}` in `WO`).

## (b) Script output — Tue Oct  6 13:45:37 UTC 2026
```
$ lake build RBM3D.Universality.GUEPhase.EntryTailMain 2>&1 | grep -E "EntryTailMain|Build completed|error"
Build completed successfully (3361 jobs).
$ lake env lean RBM3D/Universality/GUEPhase/EntryTailMain.lean; echo exit=$?     (prints nothing else: no warning in this file)
exit=0
$ git log --oneline -1; git diff --stat main...t/T2298
58708cd T2298: UN-42 Universality/GUEPhase/EntryTailMain (mixBad union, gueEntryMix at d >= 3)
 RBM3D/Universality/GUEPhase/EntryTailMain.lean | 777 +++++++++++++++++++++++++
 1 file changed, 777 insertions(+)
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/EntryTailMain.lean; grep -n "^import" RBM3D/Universality/GUEPhase/EntryTailMain.lean
0
6:import RBM3D.Universality.GUEPhase.EntryTail
$ lake env lean ax.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"   # ax.lean: #print axioms of 18 declarations
18
$ lake env lean ax.lean | grep -vc "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
0
# ax.lean prints: mixCq_pos mixEntry_tail_row_le mixEntry_tail_quad_le mixEntry_tail_diag_le mixEntry_measurableSet_mixBad mixBad_tail mixEntry_event_subset mixEntry_union gueEntryMix EntryTailMainCheck.inst_mixCq_pos EntryTailMainCheck.inst_mixBad_tail EntryTailMainCheck.inst_mixBad_tail_small EntryTailMainCheck.inst_lam_window EntryTailMainCheck.inst_mixEntry_event_subset EntryTailMainCheck.inst_mixEntry_union EntryTailMainCheck.inst_entryMix EntryTailMainCheck.inst_entryMix_quarter EntryTailMainCheck.mix_params_values 
$ lake env lean pins.lean; echo exit=$?   # = check-file section 2 verbatim (lines 145-376) + the examples below
exit=0  (output lines:        0)
$ grep -n "^example" pins.lean   # last 8 lines; each example has the shown 1-3 line proof by the target
236:example : T2293b_mixCq_pos := fun q => RBM.Univ.mixCq_pos q
238:example : T2293b_mixBad_tail := by
242:example : T2293b_mixEntry_event_subset := by
246:example : T2293b_mixEntry_union := by
250:example : T2293b_gueEntryMix := fun _d hd => RBM.Univ.gueEntryMix hd
253:example (q : ℕ) : RBM.Univ.mixCq q = mixCqV q := rfl
254:example (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) (z : ℂ) (Λ : ℝ) :
256:example (d : ℕ) : RBM.Univ.GUEEntryMix d = GUEEntryMixV d := rfl
```

### Target statements (script `extract.py`: from the declaration line to the first `:=`)
```
def mixCq (q : ℕ) : ℝ := 4 ^ (q + 1) * hwConst q + 2 ^ (q + 2) * ((q + 1).factorial : ℝ)
theorem mixCq_pos (q : ℕ) : 0 < mixCq q := by
def mixBad (g a b : ℝ) (z : ℂ) (Λ : ℝ) : Set (Ω d L W) :=
theorem mixEntry_measurableSet_mixBad (g a b : ℝ) {z : ℂ} (hz : z.im ≠ 0) (Λ : ℝ) :
    MeasurableSet (mixBad d L W g a b z Λ) := by
theorem mixBad_tail (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) {z : ℂ}
    (hz : z.im ≠ 0) {Λ : ℝ} (hΛ : 2 ≤ Λ) (q : ℕ) :
    gaussLaw d L W (mixVar d L W g a b) (mixBad d L W g a b z Λ)
      ≤ ENNReal.ofReal (4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (mixCq q / Λ ^ (q + 1))) := by
theorem mixEntry_event_subset (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {Λ κ E a b δ Φ T : ℝ}
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1) (hδ : δ ≤ mixDelta d Λ κ) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hT : mixCdet d Λ κ * Φ ^ 2 ≤ T) :
    {ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) | ∃ i j : Idx d (sz.L n) (sz.W n),
      T * (maxLoopPM d (sz.L n) (sz.W n) E (a + b) (mixMat sz n a b ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a + b) (mixMat sz n a b ω) x y ≤ δ
          then llErrMat d (sz.L n) (sz.W n) E (a + b) (mixMat sz n a b ω) i j ^ 2 else 0)}
      ⊆ mixSample sz n a b ⁻¹' mixBad d (sz.L n) (sz.W n) (sz.lam n) a b (zt E (a + b)) Φ := by
theorem mixEntry_union (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {Λ κ E δ Φ T : ℝ}
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {K : ℕ}
    {a b : Fin (K + 1) → ℝ} (hab : ∀ k, 0 ≤ a k ∧ 0 ≤ b k ∧ 0 < a k + b k ∧ a k + b k < 1)
    (hδ : δ ≤ mixDelta d Λ κ) (hΦ2 : 2 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hT : mixCdet d Λ κ * Φ ^ 2 ≤ T) (q : ℕ) :
    ouP (UNModel.band sz) n {ω | ∃ (k : Fin (K + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      T * (maxLoopPM d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) x y ≤ δ
          then llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMat sz n (a k) (b k) ω) i j ^ 2
          else 0)}
      ≤ ENNReal.ofReal (((K : ℝ) + 1) *
          (4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)))) := by
theorem gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d := by
```

### Compiled nonempty instances (namespace `RBM.Univ.EntryTailMainCheck`, `d = 3`; compiled by the module build above)
```
$ sed -n '629,635p;698,704p;718,723p;738,752p' RBM3D/Universality/GUEPhase/EntryTailMain.lean
theorem inst_mixBad_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
        (mixBad 3 3 2 1 (1 / 4) (1 / 4) (zt 0 (1 / 2)) 2) ≤
      ENNReal.ofReal (4 * (((2 * 3) ^ 3 : ℕ) : ℝ) ^ 2 * (mixCq 1 / 2 ^ (1 + 1))) :=
  mixBad_tail 3 3 2 1 (by norm_num) (by norm_num) (by norm_num) EntryTailCheck.inst_zt_im_ne
    (by norm_num) 1

          else 0)} ⊆
      mixSample sz0 0 (1 / 4) (1 / 4) ⁻¹'
        mixBad 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 4) (1 / 4) (zt 0 (1 / 4 + 1 / 4)) 2 :=
  mixEntry_event_subset (d := 3) (by norm_num) sz0 0 (Λ := 10) (κ := 1) (E := 0) (a := 1 / 4)
    (b := 1 / 4) (δ := delta0) (Φ := 2) (T := mixCdet 3 10 1 * 2 ^ 2) (inst_lam_window 0).1
    (inst_lam_window 0).2 one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (min_le_left _ _) (by norm_num) delta0_36 le_rfl
      ENNReal.ofReal ((((2 : ℕ) : ℝ) + 1) *
        (4 * ((sz0.size 0 : ℕ) : ℝ) ^ 2 * (mixCq 1 / 2 ^ (1 + 1)))) :=
  mixEntry_union (d := 3) (by norm_num) sz0 0 (Λ := 10) (κ := 1) (E := 0) (δ := delta0) (Φ := 2)
    (T := mixCdet 3 10 1 * 2 ^ 2) (inst_lam_window 0).1 (inst_lam_window 0).2 one_pos
    (by norm_num) (K := 2) (a := aMix 0) (b := bMix 0) (mix_params_ok 0) (min_le_left _ _)
    le_rfl delta0_36 le_rfl 1
theorem inst_entryMix :
    ∀ᶠ n in atTop, ouP (UNModel.band sz0) n
      {ω | ∃ (k : Fin (2 + 1)) (i j : Idx 3 (sz0.L n) (sz0.W n)),
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
            (maxLoopPM 3 (sz0.L n) (sz0.W n) 0 (aMix n k + bMix n k)
                (mixMat sz0 n (aMix n k) (bMix n k) ω) + (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) <
          (if ∀ x y, llErrMat 3 (sz0.L n) (sz0.W n) 0 (aMix n k + bMix n k)
                (mixMat sz0 n (aMix n k) (bMix n k) ω) x y ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
            then llErrMat 3 (sz0.L n) (sz0.W n) 0 (aMix n k + bMix n k)
                (mixMat sz0 n (aMix n k) (bMix n k) ω) i j ^ 2
            else 0)} ≤ ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
  gueEntryMix (by norm_num : 3 ≤ 3) (1 / 6) (1 / 10) sz0 sz0_admissible 1 one_pos (fun _ => 0)
    (fun n => by norm_num) 1 (fun _ => 2) sz0_size_ge_two aMix bMix mix_params_ok (1 / 4)
    (fun n => ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) (by norm_num) (fun n => by positivity)
    (Eventually.of_forall fun n => le_rfl) (1 / 10) 2 (by norm_num) (by norm_num)
$ grep -n "^theorem inst_" RBM3D/Universality/GUEPhase/EntryTailMain.lean | cut -d" " -f1-2
622:theorem inst_mixCq_pos 629:theorem inst_mixBad_tail 637:theorem inst_mixBad_tail_small 647:theorem inst_lam_window 689:theorem inst_mixEntry_event_subset 708:theorem inst_mixEntry_union 738:theorem inst_entryMix 756:theorem inst_entryMix_quarter 
```

### Name clash, port comparison, registry
```
$ grep -rnE "^\s*(private )?(theorem|def|lemma|abbrev|structure|instance|noncomputable def) (mixCq|mixCq_pos|mixEntry_tail_row_le|mixEntry_tail_quad_le|mixEntry_tail_diag_le|mixBad|mixEntry_measurableSet_mixBad|mixBad_tail|mixEntry_event_subset|mixEntry_union|gueEntryMix|mixCq_one|delta0|delta0_nonneg|delta0_le|delta0_36|zeta3|aMix|bMix|mix_params_ok|mix_params_values|sz0_size_ge_two|inst_mixCq_pos|inst_mixBad_tail|inst_mixBad_tail_small|inst_lam_window|inst_mixEntry_event_subset|inst_mixEntry_union|inst_entryMix|inst_entryMix_quarter)(\s|$)" RBM3D --include="*.lean" | grep -v EntryTailMain.lean | wc -l   # all 30 new public names
       0
$ grep -rnw "gueEntryMix\|mixBad\|mixCq\|mixBad_tail\|mixEntry_union\|mixEntry_event_subset" RBM3D --include="*.lean" | grep -v EntryTailMain.lean | cut -c1-110
RBM3D/Universality/GUEPhase/EntryTail.lean:13:(`:876-1525`: the union of the failure events, the size scale an
$ grep -rn EntryTailMainCheck RBM3D --include="*.lean" | grep -v EntryTailMain.lean | wc -l
       0
$ python3 compare.py   # RBM2D c9a24cf :876-1525 (git show) against this file, by declaration
text-IDENTICAL to source (9): mixCq, mixCq_pos, mixEntry_tail_row_le, mixEntry_tail_quad_le, mixEntry_tail_diag_le, mixEntry_measurableSet_and, mixEntry_measure_and_le, mixEntry_final_arith, mixEntry_scalar_36
adapted (d>=3 tokens, carrier, hypotheses):
   mixBad (10->10 lines, 20 diff-lines)
   mixEntry_measurableSet_mixBad (19->19 lines, 12 diff-lines)
   mixBad_tail (101->103 lines, 76 diff-lines)
   mixEntry_event_subset (59->72 lines, 73 diff-lines)
   mixEntry_union (43->46 lines, 51 diff-lines)
   gueEntryMix (54->55 lines, 57 diff-lines)
lattice "^ 2" (W L)^2 / W^2 hits in source :876-1525: [1011, 1020, 1130, 1141, 1177, 1181, 1195, 1199, 1203, 1216, 1224] (+ :1512, the `d.W n` form)
same patterns in EntryTailMain.lean: []
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/EntryTail.lean
9e0f275
 RBM2D/Universality/GUEPhase/EntryTail.lean | 359 +++++++----------------------
 1 file changed, 85 insertions(+), 274 deletions(-)
# hunks of that diff with old line >= 876 (git diff -U0 | grep "^@@"):
-1005,2 -1112 -1120,2 -1124 -1185,2 -1237,2 -1253 -1283 -1336 -1427 -1463,4 -1468 -1527,146 
$ lake env lean reg.lean > reg.out; echo exit=$?   # reg.lean: import RBM3D; import RBM3D.Universality.GUEPhase.EntryTailMain; #assert_rbm_axioms
exit=0  lines=     273
axiom audit: 8548 theorems, 2802 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c "GUEEntryMix\|MixProfOK\|mixCq\|mixBad\|EntryTail\|gueEntryMix" reg.out   # no registry line needed
0
```

### Narrative
* New file `RBM3D/Universality/GUEPhase/EntryTailMain.lean` (777 lines, commit 58708cd on `t/T2298`, the only file in `git diff --stat main...t/T2298`). Port of RBM2D `EntryTail.lean` at `c9a24cf` `:876-1525` to `d ≥ 3`; imports only `RBM3D.Universality.GUEPhase.EntryTail`. Section (a) needed no correction (no (a′)).
* Ported text-identically (compare.py): `mixCq`, `mixCq_pos`, `mixEntry_tail_{row,quad,diag}_le`, `mixEntry_final_arith`, `mixEntry_scalar_36`, and the private `mixEntry_measurableSet_and`, `mixEntry_measure_and_le`. Adapted: `mixBad`, `mixEntry_measurableSet_mixBad`, `mixBad_tail`, `mixEntry_event_subset`, `mixEntry_union`, `gueEntryMix`.
* Adaptations: `mixBad d L W g a b z Λ` has profile `Smix d L W g a b` on `Ω d L W`; `(W L)^2 → (W L)^d` (pair-count `^ 2` kept) and `W^2 → W^d` at every source line listed above; carrier `ouP (UNModel.band sz) n`, `mixMat sz n`, `mixSample sz n`, `mixSample_law` with coupling `sz.lam n`; `mixEntry_event_subset`/`mixEntry_union` carry `hd : 3 ≤ d`, `hg : 0 < sz.lam n`, `hgΛ : sz.lam n ≤ Λ` (passed to `mixEntry_det`), `mixDelta d Λ κ`, `mixCdet d Λ κ`, `sz.three_le_L n`.
* `gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d`: `Λ := 𝔡⁻¹`; the filter is the source's plus the coupling window `0 < sz.lam n ≤ 𝔡⁻¹` (private `EntryTail_eventually_lam`, from `WO 𝔡` and `W ≥ 1`); `SizeTendsto` (real-valued) is turned into the `ℕ`-valued `Tendsto sz.size` by `tendsto_natCast_atTop_iff.mp` (source: the other direction).
* The size scale of RBM2D `:1240-1384` (`Kstab2 ≲ log L`) is not ported: `mixDelta d Λ κ` and `mixCdet d Λ κ` do not depend on `n`, so `EntryTail_eventually_delta` (`mixDelta_pos`, `eventually_le_rpow`) and `EntryTail_eventually_mixCdet` (`eventually_le_rpow`) replace it (both private).
* No statement was false, no hypothesis was added beyond the list above, no pinned or merged signature was changed. All merged names the file calls resolve at the T2293-ticket names (the build is the check).
* Instances (all in the module): every deterministic hypothesis discharged by `norm_num`/`positivity`/merged facts (`sz0_admissible`, `inst_lam_window`, `mix_params_ok`, `delta0_36`); the sample `ω` is a variable of the carrier; the conclusion of `inst_entryMix`/`inst_entryMix_quarter` is `∀ᶠ n` (no `n` is exhibited: the threshold is data of `gueEntryMix`, see (a) rows "eventual n"). `inst_mixBad_tail` (bound `> 1`, weak but true) and `inst_mixBad_tail_small` (`Λ = 10^6`, bound `≤ 1/1000`).
* `GUEEntryMix` is concluded by `gueEntryMix`; the registry pre-check shows `0 axioms in RBM`, exit 0, and no line mentions the new names: no `Axioms.lean` registry line is needed (file not touched).

## (c) Verified Mathlib names (scratch `names.lean`: `#check @name` for each; `lake env lean names.lean` printed 0 errors)
`measure_iUnion_fintype_le`, `measure_union_le`, `measure_mono`, `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_add`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`, `Fintype.card_prod`, `Fintype.card_fin`, `Nat.one_le_pow`, `Real.pow_div_factorial_le_exp`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_natCast`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`, `pow_le_pow_left₀`, `inv_anti₀`, `one_le_pow₀`, `mul_inv_le_iff₀`, `inv_le_one_of_one_le₀`, `tendsto_natCast_atTop_iff`, `Filter.Tendsto.eventually_gt_atTop`, `Filter.Tendsto.eventually_ge_atTop`, `Nat.le_ceil`, `Nat.le_self_pow`, `Nat.le_mul_of_pos_left`, `measurableSet_lt`; project names `RBM.eventually_le_rpow`, `RBM.Green.zt_im_ne_zero`, `RBM.Gauss.card_Idx`. Names verified absent: none needed.

## (d) Open issues and paper-delta candidates
* No open issue; no external input; `GUEEntryMix d` is proved for every `3 ≤ d` (pin `T2293b_gueEntryMix`).
* `T2298a` (Lean structure, not a paper delta): the coupling window `0 < sz.lam n ≤ 𝔡⁻¹` (from `WO 𝔡`) supplies `g = sz.lam n`, `Λ = 𝔡⁻¹` inside `gueEntryMix`; `mixDelta d 𝔡⁻¹ κ`, `mixCdet d 𝔡⁻¹ κ` are `n`-free, so the RBM2D `log L` size-scale lemmas have no counterpart (T2278a).
* `T2298b` (bookkeeping): the error term in the pinned event is `W^{-d}` (RBM2D `W^{-2}`), and the pair count `(W L)^d` squared uses `N = (W L)^d` (as T2293b).
* `T2298c` (Lean structure): two private helpers beyond the ticket's `EntryTail_eventually_lam`: `EntryTail_eventually_delta`, `EntryTail_eventually_mixCdet` (prefix per §3 (E)); `mixBad`, `mixBad_tail`, `mixEntry_measurableSet_mixBad` take `d L W` (and `g`) explicitly, `mixEntry_event_subset`/`mixEntry_union` take `{d}` implicit with `hd sz n` explicit (as the pins' binder order).
