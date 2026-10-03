Auditor model: claude-opus-5-5

# T2030 audit (round 1) — S1-01 `RBM3D/Gauss/FlowCalculus.lean`

Written Sat Oct  3 05:52:22 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2030-audit1`, detached at `t/T2030` = 9894147.

## 1. Scope and build
```
$ git diff --stat main...t/T2030
 RBM3D/Gauss/FlowCalculus.lean | 962 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 962 insertions(+)
$ git diff --name-only 976030d main -- RBM3D        # main moved since the branch base 976030d
RBM3D/Loop/KLUnique.lean
RBM3D/Propagator/Prop6Hold.lean
RBM3D/Test/Axioms.lean                               # none is imported by FlowCalculus (imports: Loop.GLoopFlow + 3 Mathlib)
$ lake build RBM3D.Gauss.FlowCalculus 2>&1 | grep -E "error|warning|sorry|Build completed"
Build completed successfully (3296 jobs).
$ ls -la .lake/build/lib/lean/RBM3D/Gauss/FlowCalculus.olean   # rebuilt in this worktree (22:50 local = 05:50 UTC)
-rw-r--r--@ 1 junyin  staff  1250320 Oct  2 22:50 .lake/build/lib/lean/RBM3D/Gauss/FlowCalculus.olean
$ lake env lean RBM3D/Gauss/FlowCalculus.lean ; echo exit=$?       # no output lines (no warning/error)
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Gauss/FlowCalculus.lean   # (no output)
```
Only the sole writable file is touched; it is a new file, so no frozen signature changes.

## 2. Axioms and registry pre-check (Amend 1)
```
$ lake env lean ax.lean     # import RBM3D.Gauss.FlowCalculus; #print axioms for all 56 public theorem/def names (grep of the file)
     56 [propext, Classical.choice, Quot.sound]
$ lake env lean reg.lean    # import RBM3D; import RBM3D.Gauss.FlowCalculus; #assert_rbm_axioms
axiom audit: 1121 theorems, 404 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
...
premises found by scanning: 7 (borrowed 2, owed 0, structural 5).
registry precheck exit=0
```
The file defines 4 defs (`HflowBlock`, `spectralMSign`, `gsigFlowDeriv`, `loopWordDeriv`), none `Prop`-valued; no theorem takes an
unproved `Prop` predicate as a hypothesis, so no registry line is owed (Amend 1 satisfied with `Test/Axioms.lean` untouched).

## 3. Statements against the pin (RBM2D `c9a24cf`, ten files), by script
Script `sd.py` (scratchpad): extracts every `theorem`/`def` header up to `:=` from the ten RBM2D files and the new file,
renames on the RBM2D side (`spectralM→mE`, `spectralZ→zt`, `Z2 L→Zd d L`, `LoopIdx→Loop.LoopIdx`, `gloop→loopL`, `Gsig→Gres`,
`BlockIndex L W→Vtx d L W`, `P L W→PF d L W g`, `X L W→X d L W`, `(W:ℝ)⁻¹^2→((W:ℝ)^d)⁻¹`, `(L*W)^2→(L*W)^d`,
`(Xmat ω).submatrix splitEquiv…→blockMat d L W (Xmat d L W ω)`), compares whitespace-normalised text.
```
NOT PORTED SpectralWindow spectralM
NOT PORTED SpectralWindow spectralZ
NOT PORTED FlowTimeCont continuous_Hflow_nonzero_index_example
NOT PORTED GreenTimeCont continuous_green_Hflow_nonzero_index_example
NOT PORTED LoopTimeCont continuous_gloop_Hflow_one_edge_example
NOT PORTED LoopSampleCont measurable_gloop_HflowBlock_one_edge_example
rbm2d 61 same 42 diff 13 new-only ['spectralMSign_eq_mSigma']
```
The 13 DIFF lines, read individually (verbatim excerpts):
```
continuousOn_integral_norm_gloop_pow_spectralZ   3D adds (g : ℝ) — the coupling of the merged law PF d L W g; rest identical
continuous_seqHflow_entry_time                   2D: (i j : Idx (sz.L n) (sz.W n))   3D: (i j : Idx d (sz.L n) (sz.W n))
continuous_green_of_isHermitian(_moving), continuous_green_Hflow_time, continuous_green_Hflow_moving_time,
continuous_green_HflowBlock_time, continuous_green_HflowBlock_sample, hasDerivAt_green_moving
                                                 2D: green (f v) z   3D: Gres (f v) z true   (D22: Ring.inverse = ⁻¹ on matrices)
norm_Gsig_le_inv_eta                             2D: H : Matrix (BlockIndex L W) …   3D: H : Matrix n n ℂ (generalisation, contains 2D)
norm_foldr_Gsig_Eblk_le, norm_gloop_le_crude, norm_gloop_HflowBlock_le_crude_on_Icc
                                                 3D adds local [NeZero W] (2D: global variable); bound (η⁻¹ * ((W:ℝ)^d)⁻¹)^n, (L*W)^d
```
Key targets (ticket list) at `c9a24cf`, line contents checked:
```
GreenTimeCont:88  theorem continuous_green_Hflow_nonzero_index_example (ω : Ω 3 1) :
LoopTimeCont:96   theorem continuous_gloop_Hflow_one_edge_example (ω : Ω 3 1) :
LoopSampleCont:77 theorem measurable_gloop_HflowBlock_one_edge_example (u : ℝ) :
FlowTimeCont:53   theorem continuous_seqHflow_entry_time (n : ℕ) (ω : SeqΩ d)
SpectralWindow:64 theorem continuousOn_integral_norm_gloop_pow_spectralZ
LoopEnvelope:120  theorem norm_gloop_HflowBlock_le_crude_on_Icc {s t η : ℝ} (hη : 0 < η)
```
Bridge definitions checked against the merged files (signatures/bodies):
```
GLoopFlow:74   def Gres (H) (z) (σ) := Ring.inverse (H - (if σ then z else conj z) • 1)
GLoopFlow:105  def blockMat M := M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm
GLoopFlow:123  def loopL H z I := trace ((I.σ.zip I.a).foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1)
GLoop:55       def Eblk a := diagonal fun x => if x.1 = a then ((W:ℂ)^d)⁻¹ else 0
FineModel:437  def Hflow u ω := (Real.sqrt u : ℂ) • Xmat d L W ω
Semicircle:38  def mE E := (-E + Real.sqrt (4 - E^2) * I) / 2 ;  Semicircle:179  def zt E t := E + (1 - t) * mE E
FlowCalculus:222 def HflowBlock u ω := blockMat d L W (Hflow d L W u ω)
```
`gsigFlowDeriv`/`loopWordDeriv` (FlowCalculus:465, :509) match RBM2D LoopDerivative:29, :63 term by term (`G * (X/(2√u) + m_σ) * G`,
negated; Leibniz recursion). Mathematics: `dH_u/du = X/(2√u)`, `dz_u/du = -m`, `dG = -G(dH - dz)G`: sign and drift correct; the
`σ = false` branch uses `conj m`. Envelope: `‖tr M‖ ≤ N‖M‖`, `‖G‖ ≤ η⁻¹`, `‖E_a‖ = W^{-d}`, `N = card Vtx = (LW)^d`: the
`d = 2 → d` exponent change (portmap P.1 rows 9, 10) is in place in every envelope statement; no residual `W^2`, `(LW)^2`, `Z2`
in any statement (prove report b.7 grep; my diff above shows none).

Verdict on statements: all ten key statements and the other 46 public ports match the RBM2D pin after the dimension change;
differences are binder placement, the extra `g` of the merged law, `Gres … true` for `green`, and one generalisation.
The three RBM2D `*_example` key items (GreenTimeCont:88, LoopTimeCont:96, LoopSampleCont:77; d = 2, `W = 1`) are
replaced by `d = 3, L = 3, W = 2` examples of the general theorems (section 4) — the ticket allows a stated drop (b.6/b.9).

## 4. Hidden hypotheses, vacuity, cycles
- Hypotheses are all explicit in signatures (`|E| < 2` or `|E| ≤ 2-κ`, `0 < u < 1`, `s ≤ t < 1`, `Im z ≠ 0`, `0 < η ≤ |Im z|`,
  `I.WF`, `IsHermitian`). The only structure argument is `sz : Sizes d` (data fields `three_le_L`, `W_pos`), instanced by `sz0`.
- No external hypothesis; no `Prop` predicate hypothesis. Imports: `RBM3D.Loop.GLoopFlow` (merged) + Mathlib only: no cycle.

## 5. Compiled nonempty instances (file lines 857–962; compiled in §1)
Data: `d = 3, L = 3, W = 2` (`N = 216`), `E = 1/2`, `κ = 1`, window `[1/5, 3/5]`, `u = 1/2`, `g = 1`, `q = 2`,
loop `⟨[true,false,true], [![1,0,2], ![0,1,0], ![2,2,1]]⟩` (WF by `rfl`, length 3), `Im z = 1` or `u + I`;
`sz0` (`Defs/Sizes.lean:260`: `L 0 = 4`, `W 0 = 32`, `d = 3`) for the sequence statement.
| key target | instance | discharged at concrete data |
|---|---|---|
| `norm_spectralM`, `hasDerivAt_spectralZ_im` | example 1 | `|1/2| < 2` by `norm_num` |
| `spectralZ_window_gap_of_bulk` | example 2 | `κ = 1`, `|1/2| ≤ 1`, `3/5 < 1` |
| `continuous_seqHflow_entry_time` | example 3 | `sz0`, `n = 0`, entry `(0,0)` |
| `continuous_green_Hflow_(moving_)time`, `continuous_gloop_Hflow_time` | example 4 | `Im I ≠ 0`, `Im(u+I) ≠ 0` by `simp` |
| `continuous_/measurable_gloop_HflowBlock_sample` | example 5 | `u = 1/2`, `Im I ≠ 0`, WF |
| `hasDerivAt_green_/gloop_HflowBlock_spectralZ` | example 6 | `|1/2|<2`, `0 < 1/2 < 1`, WF |
| `norm_gloop_HflowBlock_le_crude_on_Icc` | example 7 | `η = (2/5) Im m(1/2) > 0` from the gap lemma, WF |
| `continuousOn_integral_norm_gloop_pow_spectralZ` | example 8 | `κ=1`, `|1/2| ≤ 1`, `1/5 ≤ 3/5 < 1`, WF, `q = 2`, `g = 1` |
| `card_BlockIndex`, `norm_Eblk_le_inv_W_sq` | example 9 | `card Vtx 3 3 2 = 216 = card Idx 3 3 2` |
No `N = 0`, empty index, collapsed window or `False` premise; `sz0` size (`2097152`) is a fixed concrete value, not used to
make any hypothesis hold (the statement is pure continuity).

## 6. Paper deltas
- Single-time flow `H_u = √u X` instead of `(MBM)`: signed D21. `G = Ring.inverse(H - z)`: signed D22.
- Crude envelope, window continuity and Green/loop derivatives are Lean-side auxiliary facts of the port (no paper statement
  differs). The prover's "T2030a: none" is consistent with this; no uncovered Lean/paper difference found.

## 7. Observations (no RETURN)
- O1: Report (d) proposes no delta but does not cite D21/D22 by number (ST1-COMMON item 9 asks signed entries be cited).
- O2: `norm_Eblk_le_inv_W_sq` keeps RBM2D's name though it states `W^{-d}`; disclosed in (d); statement correct.
- O3: `continuous_seqHflow_entry_time` instance uses `sz0` (N = 2097152); harmless for a continuity statement.
- O4: The theorems allow `s < 0` (then `√u = 0`); still true, matches RBM2D.

## 8. Verdict
Per target (all ten key statements and the remaining public ports): PASS. Build PASS, axioms PASS, instances PASS,
paper-delta coverage PASS. No dispatcher sign-off needed.

**T2030: PASS.**
