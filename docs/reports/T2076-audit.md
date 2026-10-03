Auditor model: claude-opus-5-5

# T2076 audit (round 1): S1-32 `Induction/ConArg` (`ConArgPin`, `conArg`, `stConArg_holds`)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2076-audit1`, detached at `t/T2076` = `a1c8df1`. Written Sat Oct  3 20:21:55 UTC 2026.

## 0. Scope
```
$ git diff --stat main...t/T2076; git diff --name-only main...HEAD
 RBM3D/Induction/ConArg.lean | 876 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 876 insertions(+)
RBM3D/Induction/ConArg.lean
```
Only a sole writable file is touched (new file). `RBM3D/Test/Axioms.lean` is untouched, and so are the frozen signatures (`Induction/Defs.lean` is unchanged).
Imports: `RBM3D.Induction.ConArgDet`, `.PerTimeCalc`, `.ScaleFacts`, `.Defs` (no `import RBM3D`).

## 1. Statements

### 1.1 `stConArg_holds` against the merged pin `STConArg` (`Induction/Defs.lean:334`)
```
$ lake env lean ax.lean
  (example : ∀ d : ℕ, RBM.Gauss.Sizes.STConArg d := RBM.Gauss.Sizes.stConArg_holds ; #check)
RBM.Gauss.Sizes.stConArg_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STConArg d
exit 0
```
The type is exactly the merged pin, fully qualified. No local `STConArg` is declared in the file (declaration outline: `grep -n "^def\|^theorem"` gives only `ConArgPin`:655, `conArg`:673, `stConArg_holds`:806). The pin is unchanged on the branch, so its hypotheses, quantifier order (`κ ε 𝔡 ε₁ C₀`, then `𝔠 sz z`, `STFlow`, `s t`, `∀ n` ranges `ε₁ ≤ s ≤ t < 1`, `STLmax` at `s`, `∀ k ≥ 2`), the right side `(Bctl_s · η_s/η_t)^{k-1}`, and `Ω_t = STomegaC … C₀` all carry over as the dispatcher pinned them. **PASS.**

### 1.2 `ConArgPin` / `conArg` against RBM2D `c9a24cf` `ConArg:61`
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/ConArg.lean | sed -n 61,74p
def ConArgPin (κ c : ℝ) (E : ℕ → ℝ) (t₁ t₂ : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → (∀ n, c < t₁ n) → (∀ n, t₁ n ≤ t₂ n) →
    (∀ n, t₂ n < 1) → SizeTendsto d →
    (∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt (Sizes.seqP d) d.size ... loopAbs ... (t₁ n) ...
      (fun n _ _ => (scaleM (d.L n) (d.W n) (E n) (t₁ n))⁻¹ ^ (k - 1))) →
    ∀ k : ℕ, 1 ≤ k → Path.PerTimeDomAt ...
      (fun n p ω => (if gMax (E n) (t₂ n) (...) ≤ 2 then 1 else 0) * loopAbs ...)
      (fun n _ _ => (ellT (d.L n) (t₂ n) / ellT (d.L n) (t₁ n)) ^ (2 * (k - 1)) *
        (scaleM (d.L n) (d.W n) (E n) (t₂ n))⁻¹ ^ (k - 1))
$ sed -n 655,668p RBM3D/Induction/ConArg.lean
def ConArgPin {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 ≤ C₀ → (∀ n, c ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto →
    (∀ k : ℕ, 1 ≤ k →
      sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖Sizes.Lloop sz n (E n) (s n) p.1 p.2 ω‖)
        (fun n _ _ => (sz.Bctl n (s n)) ^ (k - 1))) →
    ∀ k : ℕ, 1 ≤ k →
      sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => Sizes.STomegaC sz n (E n) (t n) C₀ ω *
          ‖Sizes.Lloop sz n (E n) (t n) p.1 p.2 ω‖)
        (fun n _ _ => (sz.Bctl n (s n) *
          (Gauss.etaT (E n) (s n) / Gauss.etaT (E n) (t n))) ^ (k - 1))
$ grep -n "def PrecPT" RBM3D/Defs/StochDomAt.lean
125:def PrecPT (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := Path.PerTimeDomAt (seqP sz) sz.size ξ ζ
```
Differences, each one checked:
- The `d = 2` scale `(ℓ₂/ℓ₁)^{2(k-1)}M_{t₂}^{-(k-1)}` becomes `(Bctl_s η_s/η_t)^{k-1}`, which is the form the ticket requires (T2015 b, row `STConArg`). The hypothesis (55) at `s`, `M_{t₁}^{-1} → Bctl_s`, matches `STLmax`'s right side `(Bctl τ)^{k-1}`.
- The threshold `2` becomes a general `C₀ ≥ 0`, and `c < t₁` is relaxed to `c ≤ s`. Both make the theorem stronger.
- `PerTimeDomAt` keeps the same form (`PrecPT` is a definitional abbreviation); the index drops RBM2D's `Unit ×` factor; `Z2 → Zd d`.

`conArg : ConArgPin sz κ c C₀ E s t` is proved with no further hypotheses. **PASS.**

## 2. Vacuity, hidden hypotheses, cycles
- No new `structure`/`class` is declared, and no hypothesis sits in a field: the outline has only `private theorem`s, 1 `def`, 2 `theorem`s and 2 `example`s.
- `ConArgPin`'s premises can all be satisfied together (the instance in §3 discharges them). `C₀ = 0` is allowed, but `C₀ = 2` is used.
- In `stConArg_holds` (lines 806–818), `STLmax` is turned into the per-time (55) by `Path.perTimeOfStochDomAt`. The bulk condition comes from `lemma28_quant` (merged), `SizeTendsto` comes from `hflow.1.2.2.1`, and the conclusion is lifted by `stochDomAt_of_perTimeDomAt` with `#U ≤ size^{2k}` (`conArg_card_le`, eventually `2 ≤ size`). No pin is assumed in order to prove itself. The dependencies `ConArgDet`, `PerTimeCalc`, `ScaleFacts`, `Defs` and `GLoopFlow` are all merged on `main`.
- External hypotheses: none are introduced. `STLmax` is part of the pin itself (the ST-6 chain).

## 3. Compiled nonempty instances (file lines 837–872)
- **`conArg`.** `example (h55 : …)` at `d = 3`, `sz0` (`n = 0`: `L = 4, W = 32, λ = 1/64, N = 2097152`), `E = STflowE z0`, `κ = 1/10`, `c = 1/16`, `C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`. Every deterministic premise is discharged: `0<κ`, `0<c`, `0≤C₀` and the time ranges by `norm_num`; the bulk condition by `bulk_z0` (`lemma28_quant` at `z0`); `SizeTendsto` by `sz0_tendsto`. Only (55) at `s` remains as a hypothesis; it is the per-time form of the pin `STLmax`.
- **`stConArg_holds`.** `example (hL : STLmax sz0 (STflowE z0) (fun _ => 1/16))` at the same data plus `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `ε₁ = 1/16`. `STFlow` is discharged by the merged `flow_z0` (`Induction/Defs.lean:435`), and the positivity and ranges by `norm_num`. The only remaining hypothesis is the ST-6 pin `STLmax`, which the rules allow.

The data are nondegenerate: `N ≥ 2097152`, the index set is nonempty, `s < t` is a strict window, no premise is `False`, and no witness is astronomically large. Both examples compile in the build of §4. **PASS.**

## 4. Build, hygiene, axioms
```
$ lake build RBM3D.Induction.ConArg 2>&1 | grep -i "error\|warning\|sorry"; tail -1
(no lines)
Build completed successfully (3323 jobs).
exit 0
$ grep -nE "sorry|admit|^axiom|native_decide" RBM3D/Induction/ConArg.lean; echo "grep exit $?"
grep exit 1
$ lake env lean ax.lean
'RBM.Ind.ConArgPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.conArg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stConArg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git grep -nE "ConArgPin|stConArg_holds|theorem conArg\b" main -- RBM3D; echo "git grep exit $?"
git grep exit 1
```
Helpers are `private`, as §3 (E) requires. The public names do not clash with anything on `main`. **PASS.**

## 5. Paper deltas
```
$ grep -n "T2015b\|T2015h\|^## D26\|^## D32" docs/paper-deltas.md
259:## D26 · `lem_ConArg` 只陈述 `t < 1`（2026-10-03，T2015b；钉文 `STConArg` …）
283:## D32 · `STConArg` 只留 `(res_lo_bo_eta)` 的第一个界（2026-10-03，T2015h）
```
- The endpoint `stConArg_holds` equals the merged pin. The pin's differences from the paper are already recorded: `t < 1` is D26, and the omitted second bound is D32. The `W^{-d}B_{s,0}` scale is part of the pin's T2015 design (row `STConArg`).
- The differences in `ConArgPin` from the paper are proposed as candidates: `k ≥ 1` and `C₀ ≥ 0` (T2076a), and `c ≤ s` (T2076b). Coverage is complete. **PASS.**

## 6. Observations (no verdict effect)
- O1. `ConArgPin` is stated per time (`PrecPT`, union outside `P`) at a general energy `E`. The paper's `≺` takes the max inside, as `Prec` does. This is RBM2D's form, unchanged, and the two are equivalent because `#U ≤ size^{2k}` (`stConArg_holds` does exactly this lift). Not a statement difference for the endpoint. The dispatcher may still want a one-line note under T2076a.
- O2. Report (a) row 5 says a new lemma is needed; this is corrected in (a′).1 (`lemma28_quant` is merged and used). No effect.
- O3. Registry: `STConArg` can leave `owedProps` after this merge (report b.4 / narrative). That removal belongs to the cleanup ticket.

## Verdict
| target | verdict |
|---|---|
| `stConArg_holds (d : ℕ) : STConArg d` | PASS |
| `ConArgPin` / `conArg` (ported, `d`-general) | PASS |

Ticket T2076: **PASS**. No dispatcher sign-off is needed.
