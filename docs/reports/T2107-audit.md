Auditor model: claude-opus-5-5
# T2107 audit, round 1 (LW-05: `Graph/LWWeightExp`, pin `LWweightExp`, Amend 1) — Sun Oct  4 06:21:55 UTC 2026
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2107-audit1`, detached at `t/T2107` = 273e270; merge base 6187713; main = 37ac2ae.

## 1. Diff scope and the Amend 1 edit of `Graph/LWPins.lean`
```
$ git diff --name-only main...t/T2107
RBM3D/Graph/LWPins.lean
RBM3D/Graph/LWWeightExp.lean
RBM3D/Test/Axioms.lean
$ git diff -U0 main...t/T2107 -- RBM3D/Graph/LWPins.lean | grep -cE "^-[^-]" ; ... | grep -cE "^\+[^+]"
6
6
$ diff <(git show main:RBM3D/Graph/LWPins.lean) \
       <(git show t/T2107:RBM3D/Graph/LWPins.lean | sed 's/LWPins_lwSp d L W g E t/LWPins_lwSp d L W E g t/g') && echo IDENTICAL
IDENTICAL
$ git grep -n "LWPins_lwSp d L W E g t" main t/T2107 -- RBM3D | cut -c1-40
main:RBM3D/Graph/LWPins.lean:112:   main:...:115:   main:...:169:   main:...:172:   main:...:176:   main:...:180:   (none on t/T2107)
$ git grep -c LWPins_lwSp main -- RBM3D
main:RBM3D/Graph/LWPins.lean:8          # no user of the swapped order outside LWPins.lean
$ git diff -U0 main...t/T2107 -- RBM3D/Test/Axioms.lean | grep -E "^[-+@]"
@@ -152 +151,0 @@ def owedProps : List Name :=
-   `RBM.Graph.LWweightExp, -- `(Owx)` (`7_8:294-306`): LW-05
```
The six edits are exactly lines 112, 115, 169, 172, 176, 180 and nothing else (Amend 1). `Test/Axioms.lean`: one registry line removed. Only sole writable files are touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.LWPins RBM3D.Graph.LWWeightExp RBM3D.Test.Axioms
Build completed successfully (3362 jobs).   EXIT 0
$ grep -E "^(warning|error)" build.log | sed -E 's/:[0-9]+:[0-9]+:.*//' | sort | uniq -c
   1 warning: RBM3D/Green/FlucVanish.lean
  14 warning: RBM3D/Green/IBPPoly.lean
  18 warning: RBM3D/Green/LDEQuad.lean
  20 warning: RBM3D/Green/LDEQuadMom.lean        # merged files, lint only; 0 messages from the 3 ticket files
$ lake env lean scratch/ax.lean     (#print axioms)
'RBM.Graph.lwWeightExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwWx_integral' / 'lwWx_lwPoly' / 'lwWx_dh' / 'lwWx_lwdf' / 'lwWx_lwSp' / 'lwWx_hSp'
  : each [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owxT{1,2,3,4}_counters', 'RBM.Graph.owxT{1,2,3,4}_ord' : each [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^\s*axiom" RBM3D/Graph/LWWeightExp.lean RBM3D/Graph/LWPins.lean
(no output)
$ name-clash grep of the 86 public names of LWWeightExp.lean against main 37ac2ae (all RBM3D/*.lean)
clashes on main: 0
```
Full `lake build` not rerun here (hub runs it at merge; the four merges since the base add new files and imports only).

## 3. Target 2: `lwWeightExp_holds : LWweightExp d` — PASS
Statement: `theorem lwWeightExp_holds (d : ℕ) : LWweightExp d` — the merged pin itself (by name, so verbatim);
auditor check `example : ∀ d, LWweightExp d := lwWeightExp_holds` compiles. The amended pin (`LWPins.lean:106-116`):
```
∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ P x,
  ∫ Ǧ_xx·f ∂PF = ∫ (m Σ_α S_xα Ǧ_xx Ǧ_αα f + m³ Σ_{α,β} LWPins_lwSp d L W g E t x α · S_αβ Ǧ_αα Ǧ_ββ f
                    − m Σ_α S_xα G_αx ∂_{αx} f − m³ Σ_{α,β} LWPins_lwSp d L W g E t x α · S_αβ G_βα ∂_{βα} f) ∂PF
def LWPins_lwSp … (g E t : ℝ) := of (LWPins_lwS g t) * Ring.inverse (1 - mE E ^ 2 • of (LWPins_lwS g t))
```
Against `7_8:294-306` (`\eqref{Owx}`, read from TeX): same four terms, signs, powers `m, m³`, index sums, `S_t = tS`,
`S⁺ = S(1−m²S)⁻¹` (D82, D94), `f` a resolvent polynomial (D64), `∂_{h}` = `LWPins_dH` (D65), fixed-size `PF` (D103).
After Amend 1 the `S⁺` argument order matches the definition `(g E t)`. No sign condition on `g`, every `d`, `0 ≤ t < 1`.
Dependencies, all merged, no cycle: `owx_integral` (`LWStein.lean:1239`, hypotheses `GaussIBP sz`, `0<z.im`, `0<u`,
`m≠0`, `z+u m=−m⁻¹`, `hSp`), `gaussIBP (sz : Sizes d) : GaussIBP sz` (`IBPPoly.lean:305`, unconditional),
`seqP_map_slice` (`FineModel.lean:184`). `PF` is a probability measure (`FineModel.lean:100`), so the pin is not vacuous.
Every `owx_integral` hypothesis is discharged inside the proof (`lwWx_im_pos`, `lwWx_mE_ne`, `lwWx_flow`, `lwWx_hSp`);
`t = 0` closed separately (`lwWx_gc_zero`, `lwWx_lwS_zero`, `lwWx_lwSp_zero`). No hypothesis in a structure field
(`lwWxSizes` fills `Sizes`' five fields from `hL`, `NeZero W`).
Instance (`LWWeightExp.lean:1440`, compiled): `lwWeightExp_holds 3 3 1 (le_refl 3) (1/2) 0 (1/2) lwWx_inst_hE (by norm_num)
(by norm_num) (X (true, 0, 0)) 0` — `d=3, L=3, W=1 (N=27), g=1/2, E=0, t=1/2, P = X(true,x,x)` as the ticket asks;
also `:1446` discharges the merged `LWInstFixed.inst_ssl` (`W=2, N=216, g=1`) with `lwWeightExp_holds 3`.

## 4. Target 1: the bridge (a)–(d) — PASS
Statements (extracted from the file, `LWWeightExp.lean`):
```
(a) lwWx_integral {F : SeqΩ (lwWxSizes d L W g hL) → ℂ} {G : Ω d L W → ℂ} (hF : Continuous F)
      (h : ∀ ω', G (slice … 0 ω') = F ω') : ∫ G ∂PF d L W g = ∫ F ∂seqP (lwWxSizes …)
(b) lwWx_lwG : lwG sz 0 (zt E t) t x y ω = LWPins_lwG d L W E t (slice sz 0 ω) x y := rfl
    lwWx_lwS : lwS sz 0 t = Matrix.of (LWPins_lwS d L W g t)
    lwWx_lwSp : lwSplus sz 0 t (mE E) = LWPins_lwSp d L W g E t
    lwWx_im_pos (|E|<2) (t<1) : 0 < (zt E t).im ; lwWx_mE_ne : mE E ≠ 0 ; lwWx_flow : zt E t + t·mE E = −(mE E)⁻¹
    lwWx_hSp (|E|<2) (0≤t) (t<1) : Sp_ij − m² Σ_w Sp_iw lwS_wj = lwS_ij   for Sp = LWPins_lwSp d L W g E t
(c) lwWxVar v := if v.1 then (v.2.1, v.2.2, true) else (v.2.2, v.2.1, false) ; lwWxRename := MvPolynomial.rename lwWxVar
    lwWx_lwPoly : lwPoly sz 0 (zt E t) t (lwWxRename P) ω = LWPins_lwf d L W E t P (slice sz 0 ω)
(d) lwWx_dh (0<z.im) (0<u) : dhSample sz 0 u α w (lwPoly sz 0 z u (lwWxRename P)) ω
                              = LWPins_dH (LWPins_resPoly z P) (Hflow u (slice ω)) α w
    lwWx_lwdf (0<(zt E t).im) (0<t) : LWPins_lwdf … P (slice ω) α w = dhSample sz 0 t α w (lwPoly …) ω
```
(c) uses the swap `(false,a,b) ↦ (b,a,false)` required by the ticket (proved via `lwWx_Gres_false` at Hermitian `H`,
not assumed); `(a)` needs `F` continuous — a weaker variant than an arbitrary integrand, recorded as candidate T2107d;
all integrands of the pins are continuous (`Tame.cont`), and the general measure identity is the merged `seqP_map_slice`.
(d) needs `0 < t`, the reason `t = 0` is handled separately (ticket). Instances compiled at `d=3,L=3,W=1,g=1/2,E=0,t=1/2`:
`:1393` (b, all flow data and `hSp`), `:1403` (a, `F = G_00`), `:1411` (c, variable map), `:1422` (c, on
`X(false,0,e₀)·X(true,0,0)` with `0 ≠ e₀` proved at `:1415`), `:1430` (d, same polynomial, all `α w`).

## 5. Target 3: `(Owx)` as a graph operation — PASS
```
owx_graph_E (hG : GaussIBP sz) (0<z.im) (0<u) (m≠0) (z+u m=−m⁻¹) (Sp M) (hSp) (hM : ∀ a, M a a = m)
  (Γ : LGraph E I) (p) (hp : p ∈ lwSplit Γ.solid) (x : I) (hx : p.1 = ⟨true,true,inr x,inr x⟩) (ℓe) :
  ∫ Γ.val D ℓe = ∫ (owxT1 m Γ x).val + ∫ (owxT2 m Γ p x).val
               + Σ_{q ∈ lwSplit p.2} ∫ (owxT3 m Γ x q).val + Σ_{q ∈ lwSplit p.2} ∫ (owxT4 m Γ x q).val
     (D = lwSampleData sz n z u M (lwS sz n u) Sp ω, integrals over seqP sz)
owxT1_counters : Δ(nS,nW,nV,nM) = (+1,+1,+1,0) ; owxT2_counters (hp) : (+1,+2,+2,0)
owxT3_counters (hp)(hq : q ∈ lwSplit p.2) : (+1,+1,+1,0) ; owxT4_counters (hp)(hq) : (+1,+2,+2,0)
owxT{1..4}_ord : ord (owxT_i …).counters = ord Γ.counters + 1
```
Matches the ticket (four terms, `α` summed as new internal vertices, `w = x` resp. `(β,α)`, counters and `ord` per
term) and the preflight table (a)(i). The value identity is proved, so the edge encodings of `owxDE` (signs of the
derivative, red swap) are checked by Lean, not by docstring. All hypotheses explicit; `hSp`, `hM` deterministic.
No definition outside `LWVocab` is needed. Instances compiled: `:1468` on the merged `owxG2 (mE 0)` and `:1484` on
`Ǧ_xx G_ax` (both with `gaussIBP` and every deterministic hypothesis discharged, `u = 1/2`, `Sp = lwSplus`, `M = mI`,
`N = 27`); `:1492` the four terms' counters by `decide` (`Γ = (2,0,1,1)`, T1 `(3,1,2,1)`, T2 `(3,2,3,1)`, T3 `(3,1,2,1)`,
T4 `(3,2,3,1)`). Auditor's check (scratch file, not in the branch), exit 0:
```
have hp : p ∈ lwSplit Γ.solid := by simp [p, Γ, lwSplit, lwWxInstGraph]
have hq : q ∈ lwSplit p.2 := by simp [p, q, lwSplit]
have := owxT3_counters 1 Γ p hp 0 q hq ; have := owxT4_ord 1 Γ p hp 0 q hq ; have := owxT2_counters 1 Γ p hp 0
```

## 6. Paper-delta coverage
Pin vs paper: `f` polynomial D64; `∂_h` D65; `S⁺` D82/D94; derivative graphs D81; `PF` vs `seqP`, `t = 0` D103.
New, proposed in the prove report (d): T2107a (pin argument order, fixed by Amend 1), T2107b (graph operation only for
the blue weight, `0<u`, `M_aa = m`), T2107c (derivative terms via `owxDE`, not `LGraph.dTerm`), T2107d (bridge at the
constant size sequence, `n = 0`, continuous `F`). Every Lean/paper difference found above is covered.

## 7. Observations (no RETURN)
- O1. The counter and `ord` theorems are not themselves applied by an `example` in the file; the file checks their
  conclusions at concrete data by `decide` (`:1492`) and discharges `hp` for the same graph (`:1484`). The auditor's
  scratch application above compiles. Suggest adding it in a later touch of the file.
- O2. CLAUDE.md §3(E): unpinned public helpers (`lwWx_*`, `owxEmb`, `owxDE`, `owxT*`, …) are not prefixed with the file
  stem `LWWeightExp`; names are distinct on main (0 clashes) and LW-06/07/08 reuse them by design.
- O3. T2107a is a Lean-internal pin correction rather than a paper difference; the dispatcher may file it under rework.

## Verdict
Target 1 (bridge) PASS; target 2 (`lwWeightExp_holds : LWweightExp d`) PASS; target 3 (`(Owx)` graph operation) PASS.
Ticket T2107: **PASS**. No dispatcher sign-off needed (the `LWPins.lean` edit is the one authorized by Amend 1).
