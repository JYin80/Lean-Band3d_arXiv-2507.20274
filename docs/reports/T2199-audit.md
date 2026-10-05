Auditor model: claude-opus-5-5
# T2199 audit (round 1): S3-12b `Induction/NQEndLin`, `nqGridEndLinN`. Mon Oct  5 18:59:45 UTC 2026
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2199-audit1`, detached at `t/T2199` = `cfafa98`.
Scratch scripts are in the session scratchpad `T2199/` (`sdiff.py`, `aud_stmt.lean`, `aud_ax.lean`, `aud_reg.lean`).

## 1. Statement against the pin (check file §2)
```
$ python3 sdiff.py   # def body of T2199_nqGridEndLinN vs `theorem nqGridEndLinN :` .. `:= by`, whitespace-normalised
pin tokens 518 thm tokens 518 IDENTICAL(whitespace-normalised)
$ lake env lean aud_stmt.lean   # check-file §2 verbatim + `example : RBM.Ind.T2199Check.T2199_nqGridEndLinN := @RBM.Ind.nqGridEndLinN`
'RBM.Ind.nqGridEndLinN' depends on axioms: [propext, Classical.choice, Quot.sound]
...
exit: 0
```
The pinned statement (read): its hypotheses are `3 ≤ d`, `κ 𝔠 τ 𝔡 > 0`, `SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡`, `|E| ≤ 2-κ`,
`0 ≤ s ≤ t < 1`, `STCaseI s t`, `RangeCond τ t`, and `W⁻¹ ≤ (1-t)/(1-s)` eventually. The quantifiers are
`∀ k ≥ 2, ∀ Λ Φ₁ Φ₂ Φ₃ (≥ 0, Λ ≥ 1 eventually), ∀ v ∈ [s,t], ∀ ε₀ > 0, ∀ D₁ > 0, ∃ ε₁ τ' D' C_K, ∀ Φc K`, then the grid
`N^{C_K} ≤ K ≤ ⌈N^{C_K}⌉` and `∀ᶠ n`, `∃ G`, `P(Gᶜ) ≤ N^{-D₁}`. The right side is `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃)B_v^k`, with no `Φc`,
no square of a level and no `STKbound` premise. This matches ticket target 3 and the design paragraph.
Verdict on the statement: **matches the pin exactly**.

## 2. Hidden hypotheses, vacuity, cycles
```
$ sed -n 1-9p RBM3D/Induction/NQEndLin.lean | grep import
import RBM3D.Induction.NQLin
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Loop.KLFinal
$ git grep -nE "nqGridEndLinN|nqEndLin_|NQEndLinInst|NQEndArith|nqEnd_" main -- RBM3D | wc -l
       0
```
- All imports are merged modules. The file does not import `RBM3D` or `Step34PinsP`, so there is no cycle.
- `Sizes` is the only structure argument and is structural. `STCaseI` and `RangeCond` are merged predicates, discharged at the
  data by `sz0_caseI` and `rangeCond_mono … rangeCond_half`.
- The private Prop structure `NQEndArith` (`:662`) is proved by `nqEnd_arith` inside the proof (`:1131`). It is not a premise
  of the target.
- `STKbound` is produced internally (`:1117`):
  `have hKb : sz.STKbound E := stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam`, with `Λg = 𝔡⁻¹` and `hlam`
  taken from `WO`.
- External/eventual premise `W⁻¹ ≤ (1-t)/(1-s)`. Limit check at the data: `W ≥ 32` (`W_ge_32`) gives `W⁻¹ ≤ 1/32 ≤ 15/16`
  (`WtInst`, `:1334`), so the premise holds for every `n`.
- The good-walk hypothesis stays in the conclusion as an implication. Its non-vacuity is assigned to S3-12c by the ticket
  (merged witnesses `nqLinGood_instance_nonempty`, `gridGood_instance_nonempty`). This follows the ticket's design and is not
  a defect here.

## 3. Compiled nonempty instances (namespace `RBM.Ind.NQEndLinInst`)
Data (merged definitions, checked by grep):
```
RBM3D/Defs/Sizes.lean:260 sz0 : Sizes 3; L = 4(n+1), W = (2(n+1))^5, lam = (2(n+1))^{-6}
RBM3D/Induction/Defs.lean:439-440 sInst ≡ 0, tInst ≡ 1/16;  GridGoodN.lean:1123 vg ≡ 1/32
RBM3D/Induction/AzumaProxyN.lean:1125 Einst ≡ 1/2; :1128 sig3 = ![true,false,true]; :1182 Λ3 ≡ 3; :1183 Φ1 ≡ 1
```
(4) `nqEndLin_instance` (`:1552`) applies `nqGridEndLinN` at the following data, with every premise given by a closed term:
- sizes and constants: `sz0`, `κ = 1`, `𝔠 = 1/6`, `τ = 1/2`, `𝔡 = 1/10`;
- times: `E = Einst`, `s = sInst`, `t = tInst`;
- structural premises: `sz0_tendsto`, `sz0_bandwidth`, `sz0_WO`, `sz0_caseI`, `rangeCond_tInst`, `WtInst`;
- levels: `Λ3`, `Φ1`, `12`, `Φ1`; end time `vg`; `ε₀ = 1/10`; `D₁ = 1`;
- the conclusion at `Φc = Φ1`, `K = KC C_K = max 1 ⌈N^{C_K}⌉` with `KC_ne_zero`, `KC_low`, `KC_up`, extracted at one `n`.

No hypothesis is left. The window is not collapsed: `window_nondegenerate`, `s_n = 0 < 1/32 = v_n`, `Δ > 0`.
`example`s at `k = 2, 3, 4` (`:1580-1586`).
(3) `assembly_instance` (`:1500`) applies the private `nqEndLin_assembly` with every premise discharged, including
`stKbound_holds`, `nqEnd_ev_hδ` and `hYm`, at `0 < Δ`. Its conclusion is `P(Gᶜ) ≤ N^{-2}` and the terminal
`‖A_K‖ ≤ assembledRHSLinN`.
(1) `asymp_instance` and (2) `ha1_instance … hΔη_instance`, `hwL_i`, `hWt_vg`, `hW1_i`, `hWε_i`, `hdW_i` are all present.
(5) The statement script is in §1, exit 0.
The instances are nondegenerate: `d = 3`, `L ≥ 4`, `W ≥ 32`, the window has positive length, `k ≥ 2` with a non-alternating `σ`,
and the levels are positive. The index `n` comes from `Filter.Eventually.exists` on the theorem's own `∀ᶠ`, which is the
pattern the ticket prescribes.
Verdict on the instances: **present and nondegenerate**.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Induction.NQEndLin 2>&1 | grep -E "error|warning: declaration uses|sorry|Build completed|^✖"
Build completed successfully (3842 jobs).
$ lake env lean aud_ax.lean   # `#print axioms` of all 40 public declarations of the file (awk over theorem/def/abbrev)
exit: 0
39   # lines with exactly [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.hσ3_i' depends on axioms: [propext, Quot.sound]
$ lake env lean aud_stmt.lean   (tail)
'RBM.Ind.nqGridEndLinN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.nqEndLin_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.assembly_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.asymp_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.hδ_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndLinInst.he2_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/NQEndLin.lean | wc -l
       0
$ git diff --stat main...t/T2199
 RBM3D/Induction/NQEndLin.lean | 1592 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1592 insertions(+)
$ printf 'import RBM3D\nimport RBM3D.Induction.NQEndLin\n#assert_rbm_axioms\n' > aud_reg.lean; lake env lean aud_reg.lean
exit: 0
axiom audit: 5938 theorems, 2086 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 109 (borrowed 1, owed 85, structural 23).
$ grep -nE "error|NQEndLin|nqEnd" reg.out
1:axiom audit: …   135:premises found by scanning: …   (no error line, no NQEndLin premise)
```
- All axioms are within the three standard ones. `hσ3_i` uses a subset of them, which is allowed.
- The only file touched is the sole writable file, which is new, so no frozen signature is touched.
- No `set_option maxHeartbeats`.

Verdict on build, axioms and diff: **pass**.

## 5. Paper deltas
The paper statement `lem:STOeq_NQ` (`3_5:1136-1150`, `(am;asoiuw)`) is a `sup_u` bound in terms of `Ξ̂`, `Ξ` at a single time
`t`. The Lean statement differs from it in five ways, each covered by a proposed candidate in prove report (d):
- **T2199a**: the grid form for one end time `v`; `GoodSetN` at a free crude level `Φc`; `GoodLinN` at the deterministic
  levels; the linear right side (route (R)).
- **T2199b**: explicit exponents and the eventual thresholds.
- **T2199c**: the collapsed window `v = s`.
- **T2199d**: the premises `W⁻¹ ≤ (1-t)/(1-s)` eventually and `STCaseI`.
- **T2199e**: `STKbound` is internal; `C_P*` is fixed before the grid; the union over sign vectors costs `D₁+1`.

The replacement of `Ξ̂` by deterministic levels is already D473/D474 (T2186a/b) in `docs/paper-deltas.md:1432-1433`. No
uncovered difference was found.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The registry pre-check above was run with the build cache copied from the main worktree. The count is 5938 theorems,
  against 5882 in the prove report, because main has since merged `LemDecCalELip` and `QProxy`. No error, exit 0. The hub's
  full build at merge is decisive.
- O2. The prove report says the largest eventual thresholds are around `log₁₀ N ≈ 274` (from `4 ≤ W^ε`). This is
  `∀ᶠ n` content of the pinned statement, not a witness of a hypothesis.
- O3. `nqEndLin_assembly` is private because its binder mentions the unclassified `YMomentBoundsN`. The report shows the
  registry reply. This is allowed by the ticket.

## Verdict
`nqGridEndLinN`: **PASS**. The statement is identical to the pin; the endpoint instance has every premise discharged at
nondegenerate data (`k = 2, 3, 4`); the module builds; the axioms are standard; the only file touched is the sole writable
file; every paper delta is covered by a proposed candidate.
Ticket T2199: **PASS**.
