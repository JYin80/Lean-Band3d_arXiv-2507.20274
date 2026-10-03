Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 22:09:01 UTC 2026

Sources: ticket T2080; probe `git show 0362cbc:RBM3D/Probe/T2039Pins.lean` (lines 2128-2242 and 2526-3571, 1161 lines moved, 44 declarations);
merged `Induction/Step2Defs.lean` (`STLWB` :406, `STLWT` :421, `STEGtM` :99, `STPsiClass` :335, `STLWassm` :342, `STLWassmExp` :349, `sz0` instance data :905-1067),
`Graph/LWPins.lean` (`LWE` :218, `LWAssm` :234, `LWterm` :240, `LWAssmExp`, `LWtermExp`), `Graph/LWPsi.lean` (`LWWindow` :47, `LWClass` :52, `LWPsiRel` :59),
`Defs/StochDomAt.lean` (`StochDomAt` :61, union over `u` inside `P`), `Defs/Sizes.lean` (`Sizes` :138 has no `3 ≤ d` field). Scratch scripts: `$S` = scratchpad `T2080/`.

### (i) Exponent / constant table (the targets are exponent-free moves plus two bridges; these are all the constants that matter)

| item | value | constraint | slack |
|---|---|---|---|
| `d` | 3 (`sz0`) | LW pins `LWterm`/`LWtermExp` start `3 ≤ d →`; `STLWB`/`STLWT` do not; `Sizes d` has no `3 ≤ d` | bridge needs `3 ≤ d` as a hypothesis (see (iii), D1) |
| `ε₀` | 1/20 | `0 < ε₀`; and `ε₀ ≤ d/2` is forced by `STPsiClass`(3) + `W → ∞` (`W^{-d/2} ≤ c⁻¹Ψ(0) ≤ c⁻¹W^{-ε₀}`) | 3/2 - 1/20 = 1.45 |
| `Ψ(n,r)` | `W_n^{-1}` (`Ψ0`) | window `W^{-3/2} ≤ Ψ ≤ W^{-1/20}` | n=0: 5.5e-3 ≤ 3.1e-2 ≤ 0.84 |
| `c` (`STPsiClass`(3), `C=0`) | 1 | `W^{-d/2} ≤ c⁻¹Ψ(0)` only up to `c`; `LWWindow` is strict (no constant) | c ≤ 1 automatic (`cΨ(0) ≤ Ψ(0)`) |
| `Ψ'` handed to `LWAssm` | `max(Ψ(n,0), W^{-d/2})` | `W^{-d/2} ≤ Ψ' ≤ W^{-ε₀}` eventually (needs `ε₀ ≤ d/2`); `Ψ² ≤ Ψ'²` for `LWInit` (monotone `≺`) | equals `W^{-1}` at the instance |
| `Φ(n,r)` | `Ψ(n,⌊r⌋₊)` | `LWClass`: `≤ W^{-ε₀}`, `C₃ = c₀⁻¹` from `STPsiClass`(3) at `C = 0` | `C₃ = 1` |
| `Cc(C)` | `c_{⌈C⌉}⁻¹` (`STPsiClass`(3) at `⌈C⌉`) | `Φ(0) ≤ Cc(C)Φ(ℓ)` for `ℓ ≤ C`, `⌊ℓ⌋₊ ≤ ⌈C⌉` | `Cc ≡ 1` at the instance |
| `C₁', C₂'` (`LWPsiRel`) | `C₁·2^{C₂}`, `C₂` | `r₂/r₁ ≤ 2ℓ₂/ℓ₁` (`⌊ℓ₁⌋ ≥ ℓ₁/2` for `ℓ₁ ≥ 1`, `⌊ℓ₂⌋ ≤ ℓ₂`), so `Ψ(r₁)/Ψ(r₂) ≤ C₁(r₂/r₁)^{C₂} ≤ C₁2^{C₂}(ℓ₂/ℓ₁)^{C₂}` | `2·2² = 8 > 1`, `C₂ = 2 > 1` |
| `ℓ_n` (`STLWT`) | `0` (merged `ℓ0_range`); finite-n test: 1e12 for `n<2`, 1 for `n ≥ 2` | `0 ≤ ℓ ≤ (log W)^{10}·ellT` (`∀ᶠ` in ST, `∀ n` in `LWAssmExp`); `ℓ'_n = 0` for `n < N₀` stays in range since `(log W)^{10} ≥ 0` (even power) and `ellT ≥ 0` (merged `ellT_nonneg`) | n=0 bound 2.5e5 vs 1e12 (violated), n≥2 holds |
| `t`, `E`, `z` | `t ≡ 1/16 ≤ lemT`, `E = 1/2`, `z_n = 1/2 + i N^{-4/5}` | `0 ≤ t_n ≤ lemT(z_n)`; identical in `STLWB`, `LWterm`, `STLWT`, `LWtermExp` | merged `sixteenth_le_lemT` |
| `κ, ε, 𝔡, 𝔠` | 1/10, 1/10, 1/10, 1/6 | `STFlow` (Admissible: `SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡`) identical in both sides; gives `W → ∞` (`ST_W_tendsto`, in the moved range) | merged `flow_z0` |
| `D` | any `D > 0` | `∀ D > 0` on both sides | — |

DECISIONS §29 items for each bridge (`STLWB_of_LWterm`, `STLWT_of_LWtermExp`): (1) time domain: both sides use `∀ n, 0 ≤ t n` and `∀ n, t n ≤ lemT (z n)`, textually identical; (2) the case-(ii) boundary `1 - ilambda²/L²`: not used, the bounds `η⁻¹Ψ(0)Ψ²`, `η⁻¹Bctl^{1/2}·STprof` are the same expressions on both sides (`STprof` unfolds to `(W^d)⁻¹ tailW … (zdistInf …)`); (3) `L`/`W` polynomial relation: not used, `STFlow` is the same hypothesis on both sides; (4) `∀` vs `∀ᶠ`: three places, all handled below (D3, D4, and the window of `Ψ`, which is `∀ᶠ` on both sides).

### (ii) Instance and bridge mathematics

**Bridge 1, `STEGt = LWE` (difference (1)).** With `loopM σ a = tr(∏_i G(σ_i)E_{a_i})`, `A = G(σ₀)E_{a₀}`, `B = G(σ₁)E_y`, `C = G(σ₁)E_{a₁}`:
`loop ![σ₀,σ₁,σ₁] ![a₀,y,a₁] = tr(A·B·C)` (STEGtM second term) and `loop ![σ₁,σ₁,σ₀] ![y,a₁,a₀] = tr(B·C·A)` (LWcut(σ₁,σ₀,a₁,a₀)); equal by `Matrix.trace_mul_comm A (B*C)`. The first STEGtM term is `LWcut(σ₀,σ₁,a₀,a₁)` verbatim (`STavgM σ x = STLM ![σ] ![x] - STmsig`, `STmsig = mSigma` pointwise, `STLM_seqHflow` is `rfl`), and `LWE σ a = LWcut(σ₁,σ₀,a₁,a₀) + LWcut(σ₀,σ₁,a₀,a₁)`; the product order `avg·SB·L` vs `SB·avg·L` is commutativity; `Finset.sum_add_distrib` plus `add_comm` finishes. Same `SB x y` order of arguments, same prefactor `(W:ℂ)^d`.

**Bridge 1, difference (2).** `STInitialGT2 sz E t ε₀ (fun n => Ψ n 0)` has the same text as `LWInit sz E t ε₀ Ψ'`. `LWAssm` takes `Ψ'` and `Φ` unrelated (only `Φ` enters the conclusion), so `Ψ' := max(Ψ n 0, W^{-d/2})`, `Φ n r := Ψ n ⌊r⌋₊`; `Φ n 0 = Ψ n 0` makes the conclusion `η⁻¹Φ(0)Φ(|a-b|)²` equal to the `STLWB` bound (`⌊(k:ℝ)⌋₊ = k`).
`LWLoop2 Φ` (index `Bool × Zd × Zd`, charge `![b, !b]`) follows from `STLWassm` (index `{σ // σ 0 ≠ σ 1} × (Fin 2 → Zd)`) by the injection `(b,a₁,a₂) ↦ (⟨![b,!b],_⟩, ![a₁,a₂])`: `StochDomAt` has the union over `u` inside `P`, so the bad set of the sub-family is contained in that of the family.

**Bridge 1, difference (3)/(5) of F15 and two further differences found.** `STPsiClass`(1)(2) are `∀ n`, `LWClass`/`LWPsiRel` use `∀ᶠ n` / `AntitoneOn (Ici 0)`: derivable. The `r ∈ ℕ` versus `ℓ ∈ ℝ` extension and the constants are in the table (`Cc`, `C₁'`). Beyond F15: **D1** the `3 ≤ d →` premise and **D2** the strict window (below).

**Bridge 2, `STLWT_of_LWtermExp` (difference (4)).** Let `N₀` be given by `∀ᶠ n, 0 ≤ ℓ n ≤ (log W)^{10} ellT`. Put `ℓ' n = if n < N₀ then 0 else ℓ n`. `LWAssmExp` for `ℓ'`: `0 ≤ ℓ' ≤ (log W)^{10} ellT` for all `n` (zero is in range); `LWWindow`, `LWInit` are `∀ᶠ`/`StochDomAt` (insensitive to finitely many `n`); `LWLoopExp ℓ'` follows from `STLWassmExp ℓ` for every `D` because the two bounds differ only at `n < N₀` and `StochDomAt` is `∀ᶠ l`. `LWtermExp` then gives the bound with `ℓ'`; it transfers back to `ℓ` for the same reason (same lemma as the probe's `ST_scaleAdm_congr`, lines 5907-5930). `STLWassmExp` has index `{σ // σ 0 ≠ σ 1} × (Fin 2 → Zd)`, `LWLoopExp` has `Bool × Zd × Zd`: injection as above. Conclusions are identical after `STprof` is unfolded and `STEGt = LWE`.

**Concrete instance (d = 3, merged `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`).** Command and output:
```
$ python3 $S/inst.py        # (A) rotation identity numerically on a toy lattice, (B) window/class/Psi-rel at sz0, (C) finite-n lemma
(1) max |STEGtM-LWE| over 4 charge pairs x 9 label pairs: 3.581228955807223e-15
n=0 W=32 L=4 lam=1.562e-02 Psi=W^-1=3.125e-02 W^{-3/2}=5.524e-03 W^{-1/20}=8.409e-01 ellT(t=1/16)=1.000
n=1 W=1024 L=8 lam=2.441e-04 Psi=W^-1=9.766e-04 W^{-3/2}=3.052e-05 W^{-1/20}=7.071e-01 ellT(t=1/16)=1.000
n=5 W=248832 L=24 lam=3.349e-07 Psi=W^-1=4.019e-06 W^{-3/2}=8.056e-09 W^{-1/20}=5.373e-01 ellT(t=1/16)=1.000
n=1000 W=32160320320160032 L=4004 lam=1.553e-20 Psi=W^-1=3.109e-17 W^{-3/2}=1.734e-25 W^{-1/20}=1.495e-01 ellT(t=1/16)=1.000
(2) window/class/Psi-rel checks all true: True ; eps0=1/20 <= d/2=1.5: True
(4) range at n=0..5 for ell: [False, False, True, True, True, True]  (log W_0)^10*ellT=2.500e+05
(4) range for ell' (ell zeroed below N0=2), n=0..50 all: True
```
(Rows n=2, 50 omitted here; the script prints them.) At this instance every hypothesis of every target holds with nonempty data: `STFlow sz0 (1/10) (1/10) 1/6 (1/10) z0` is the merged `flow_z0`; `Ψ0` is in `STPsiClass sz0 (1/20)` (merged `Ψ0_class`, `c = 1`); `Ψ' = W^{-1}`; `ℓ ≡ 0` (merged `ℓ0_range`) and the finite-n variant above; `t ≡ 1/16`. The moved events/probability theorems are instantiated by the grid data of the merged `sz0`, `sInst = 0`, `tInst = 1/16`, `K_n = ⌈N^{C_K}⌉ ≥ 1` (as in the merged `STGridMart` example); the external hypotheses `LWterm 3`, `LWtermExp 3` (not proved: LW gate) and `STNewKLKAt`, `STGoodAt` stay hypotheses of the examples (CLAUDE.md §4 step 2).

### (iii) Declarations moved, roles, and script lists

| block (probe lines) | declarations | role |
|---|---|---|
| §9 `GridWhp` (2128-2242) | `ST_prec_mono_eventually`, `ST_prec_of_le_ev`, `ST_prec_sup`, `ST_grid_whp_of_sections`, `ST_grid_whp_zero` | per-time `≺` at sections to w.h.p. for the grid walk; feeds (E1)-(E4) |
| §11 `STBdata`, `LWsec`, `LWsec2` | `STBdata` (def), `ST_Wpow_le_size`, `ST_W_tendsto`, `ST_size_rpow_neg_le`, `ST_rpow_neg_half`, `ST_prof_le_Bctl` | size data `cB W^{-d} ≤ W^{-d}B_{u,0} ≤ N^{-c}`; `W → ∞` |
| `LWsec3` | `ST_flow_im_pos`, `ST_rpow_sq`, `ST_quarter_le`, `ST_LW_sections` | premises of `STLWT`, `STEMn2Exp` at a time section; returns their conclusions |
| `Infra` | `ST_size_pow_small/big`, `ST_card_idx_prod(_le)`, `ST_card_fin2_lab_le`, `ST_hcard`, `ST_mE_im_ge`, `ST_model_le_path` | polynomial label counts, `Im m(E) ≥ √κ/2` |
| `Events` | `ST_gridTime_zero`, `ST_flow_eta_pos`, `ST_event_weak` (E1), `ST_event_init` (E2), `ST_event_lw` (E3), `ST_JhatM_nonneg`, `ST_event_mg` (E4) | the four w.h.p. events |
| `GoodProb` | `ST_union_prob`, `ST_good_prob` | with the martingale event (E5) and a.e. identities: `P(¬STGoodAt) ≤ N^{-D'}`; reclassification of `STGoodAt` (registry pre-check) is the prover's |
| `Arith`, `More` | `ST_log_le`, `ST_hsmall_aux`, `ST_final_cmp`, `ST_prof_lower(_N)`, `ST_bP_lower`, `ST_gridTime_mono`, `ST_gridStep_nonneg`, `ST_sqrt_gridStep_le`, `ST_floor_sq`, `ST_cstar_le`, `ST_init_cmp` | closure arithmetic for ST2-04 |

```
$ cd /Users/junyin/Lean_proof/RBM3D; (sed -n 2128,2242p probe; sed -n 2526,3571p probe) > moved.txt   # probe = git show 0362cbc:RBM3D/Probe/T2039Pins.lean
$ bash $S/dep.sh $S | grep 'inlib=0'      # probe declarations used in moved.txt, defined outside it and not in the library
ST2_Bctl_pos probe-line=1738 inlib=0        # = merged STBctl_pos (ticket); ST2_Bctl_mono = merged STBctl_mono
STScaleInv probe-line=2260 inlib=0          # probe §10 (ST2-04 range) : def, used at moved lines 281, 571, 644
ST_STprof_pos probe-line=2309 inlib=0       # probe §10 : theorem, used at moved lines 608, 629
ST_card_lab_le probe-line=2315 inlib=0      # probe §10 : theorem, used at moved line 431
ST_Bdata_holds probe-line=4397 inlib=0      # occurs only in two docstrings (moved lines 119, 129): no dependency
$ python3 $S/ext.py $S/probe.txt | awk '{print $2}' | sort | uniq -c    # 31 probe copies of merged names (STEGt, STLWT, STInitialGT2, STGoodAt, ST_whp_grid, ...)
  31 IDENT
```
Name clash (`grep -rlw` of the 44 moved names over `RBM3D/` outside `Probe/`): only `ST_good_prob` occurs, in the `Test/Axioms.lean` comment of the `STGoodAt` registry line (`:175`); no declaration clash. `ST_prec_*`, `ST_grid_whp_*` do not clash with merged `ST_whp_grid`, `ST_PT_of_sections`.

### Verdicts

* **D1 (blocks the bridges as pinned).** `LWterm d` and `LWtermExp d` begin `3 ≤ d →`; `STLWB d` and `STLWT d` do not, and `Sizes d` carries no `d ≥ 3` field. For `d ∈ {1,2}` (`STFlow` is satisfiable there: `N = (WL)^d → ∞`) the premise `LWterm d` is vacuous and `STLWB d` is a substantive statement, so `LWterm d → STLWB d` cannot be derived (`d = 0` is vacuous: `Admissible` fails). Needed: bridges with an extra hypothesis `(hd : 3 ≤ d)` (all consumers, e.g. `STStep2`, are under `3 ≤ d →`). This is not a change of any ST/LW pin, but it changes the ticket's bridge signature.
* **D2 (provable, not a blocker).** `STPsiClass`(3) gives `W^{-d/2} ≤ c⁻¹Ψ(0)` only up to a constant, `LWWindow` demands `W^{-d/2} ≤ Ψ`. Example `Ψ = W^{-3/2}/2` at `W = 32`: `0.002762 < 0.005524 = W^{-3/2}` while `STPsiClass`(3) holds with `c = 1/2`. Closed by `Ψ' = max(Ψ(0), W^{-d/2})` (table), using `W → ∞` from `STFlow`; no change of statement.
* **D3 (scope of the move).** The range contains uses of `STScaleInv` (def, probe 2260-2263), `ST_STprof_pos` (2309-2313), `ST_card_lab_le` (2315-2335), which lie in probe §10 (ST2-04) and are in neither merged file (`grep` above). The file does not compile without them. Needed: these three move into `Step2Events.lean` (≈30 lines) and ST2-04 imports them instead of copying (otherwise a name clash at ST2-04).
* **D4.** The moved text is otherwise self-contained: the 31 probe copies of already merged names are textually identical to the merged ones (`IDENT`, comments and whitespace stripped); `STBdata`'s proof `ST_Bdata_holds` stays in ST2-04 (ticket); `STGoodAt` registry class decided after `ST_good_prob` compiles.

* `Step2Events` move (44 declarations): **PASS**, with D3 added to the range.
* `STLWB_of_LWterm`: **FAIL as pinned** (D1: not derivable for `d ∈ {1,2}`); true and closed for `3 ≤ d` (rotation, `Ψ` binding with D2).
* `STLWT_of_LWtermExp`: **FAIL as pinned** (D1); true and closed for `3 ≤ d` (finite-n lemma).
* Overall verdict: **FAIL** (ticket amendment: `(hd : 3 ≤ d)` on both bridges; D3 declarations added to the moved range).

### (a′) Preflight corrections — Sat Oct  3 22:54:44 UTC 2026

Restart under Amend 1 (D1-D3 of (a) adopted).  Two details of (a) differ from the files:
1. (a)(iii) D3 gives `ST_card_lab_le` at probe lines 2315-2335; the declaration with its docstring is probe lines 2314-2330 (the ticket's 2315-2335 is the same range extended; `ST_zdistInf_le` (theorem at probe line 2333) is not moved).
2. The ticket's renaming list names `ST2_Bctl_pos` and `ST2_Bctl_mono`; only `ST2_Bctl_pos` occurs in the moved range (3 uses); `ST2_Bctl_mono` does not.
No verdict of (a) changes.

## (b) Script output (generated Sat Oct  3 22:54:44 UTC 2026)

Build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2080`, branch `t/T2080`, HEAD per `git log`):
```
$ lake build RBM3D.Induction.Step2Events 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3747 jobs).
$ git log --format='%h %s' -1; git diff main...t/T2080 --stat | tail -3
342d4a0 T2080: ST2-03 Step2Events (grid events, LW premises at a time section, ST-2/LW bridges)
 RBM3D/Induction/Step2Events.lean | 2049 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean           |    8 +-
 2 files changed, 2054 insertions(+), 3 deletions(-)
$ wc -l RBM3D/Induction/Step2Events.lean; grep -c 'sorry\|admit\|native_decide\|^axiom' <it>
2049 RBM3D/Induction/Step2Events.lean   (forbidden-token count: 0)
```
Full library with `import RBM3D.Induction.Step2Events` added temporarily to `RBM3D.lean` (not committed; the hub adds it at merge), run after the rebase onto main `a91ac93`:
```
$ lake build > full.txt; grep -n 'axiom audit\|Build completed' full.txt; grep 'STStep1Weak\|STScaleInv' full.txt
388:info: RBM3D.lean:123:0: axiom audit: 2702 theorems, 1096 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
542:Build completed successfully (3824 jobs).
  RBM.Gauss.Sizes.STStep1Weak: 9 [no certificate]
  RBM.Gauss.Sizes.STScaleInv: 3 [no certificate]
```
Registry pre-check: before the two registry lines were added, the same full build failed with
`error: RBM3D.lean:119:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of borrowedProps, owedProps, structuralProps: [RBM.Gauss.Sizes.STScaleInv, RBM.Gauss.Sizes.STStep1Weak]`
(tool log of this session).  Both are now in `owedProps` (class proposed: owed; `STGoodAt` stays `owed`: `ST_good_prob` bounds `P(¬ STGoodAt)`, it does not prove `STGoodAt`).

`#print axioms` of all 49 public declarations of the file (47 theorems, 2 defs), script `axioms.lean`:
```
49 of 49 lines read: depends on axioms: [propext, Classical.choice, Quot.sound]; other lines: none
'RBM.Gauss.Sizes.STLWB_of_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STLWT_of_LWtermExp' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Target statements (extracted by script from the file):
```lean
theorem STLWB_of_LWterm {d : ℕ} (hd : 3 ≤ d) : LWterm d → STLWB d
theorem STLWT_of_LWtermExp {d : ℕ} (hd : 3 ≤ d) : LWtermExp d → STLWT d
```
Compiled nonempty instances: one `example` per public theorem, section `13. Compiled nonempty instances` (`d = 3`, `sz0`, `z0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16`); every public theorem name occurs in that section (script: 47 theorems, 0 without an instance).  The two bridges (end of the file):
```lean
example (ω : sz0.SeqΩ) : STEGt sz0 0 (1 / 2) 0 ![true, false] ![0, 0] ω =
    LWE sz0 0 (1 / 2) 0 ![true, false] ![0, 0] ω :=
  STB_EGt_eq_LWE sz0 0 (1 / 2) 0 ![true, false] ![0, 0] ω

example (h : LWterm 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :=
  inst_LWB (STLWB_of_LWterm (by norm_num) h) hI hA

example (h : LWtermExp 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D → STLWassmExp sz0 (STflowE z0) tInst D (fun _ => 0)) (D : ℝ) (hD : 0 < D) :=
  inst_LWT (STLWT_of_LWtermExp (by norm_num) h) hI hA D hD
```
`LWterm 3`, `LWtermExp 3` are pins of the LW gate and stay hypotheses; `3 ≤ 3` is discharged; `inst_LWB`/`inst_LWT` are the merged applications of `STLWB 3`/`STLWT 3` at `Ψ_n = W_n^{-1}`, `ε₀ = 1/20`, `t ≡ 1/16` (`Step2Defs.lean`).
Other pins that stay hypotheses of the examples: `STLWT 3`, `STEMn2Exp 3`, `STStep1Weak`, `STDecay`, `STScaleInv` (at `Kf ≡ 0`), `STGridMart 3` (for `ST_LW_sections`, `ST_event_*`, `ST_good_prob`).
Name-clash grep (`grep -rnw <name> RBM3D --exclude-dir=Probe`, 54 names incl. private; outside `Step2Events.lean` only):
```
STScaleInv -> 'RBM3D/Test/Axioms.lean:179:   `RBM.Gauss.Sizes.STScaleInv, -- `(eq:LW_assm_exp)` at the scale family at every
ST_LW_sections -> 'RBM3D/Test/Axioms.lean:179:   `RBM.Gauss.Sizes.STScaleInv, -- `(eq:LW_assm_exp)` at the scale family at every
ST_event_lw -> 'RBM3D/Test/Axioms.lean:179:   `RBM.Gauss.Sizes.STScaleInv, -- `(eq:LW_assm_exp)` at the scale family at every
ST_event_mg -> 'RBM3D/Test/Axioms.lean:179:   `RBM.Gauss.Sizes.STScaleInv, -- `(eq:LW_assm_exp)` at the scale family at every
ST_good_prob -> "RBM3D/Test/Axioms.lean:177:   `RBM.Gauss.Sizes.STGoodAt, -- the pathwise good event (E1)-(E5) of one self-imp
STLWB_of_LWterm -> 'RBM3D/Test/Axioms.lean:145:   `RBM.Gauss.Sizes.STLWB, -- `lem:LWterm` (`3_5:385-404`): LW gate; `STLWB_of_LWt
STLWT_of_LWtermExp -> 'RBM3D/Test/Axioms.lean:145:   `RBM.Gauss.Sizes.STLWB, -- `lem:LWterm` (`3_5:385-404`): LW gate; `STLWB_of_LWt
```
(only comments of `Test/Axioms.lean`; no declaration clash.)
Diff against the probe (`git --no-optional-locks show 0362cbc:RBM3D/Probe/T2039Pins.lean`, lines 2128-2242, 2258-2263, 2308-2330, 2526-3571, vs the moved body of the file; `<` probe, `>` file; 59 changed lines, all listed by kind):
```
  10 > namespace RBM.Gauss.Sizes
  10 > 
   9 > end RBM.Gauss.Sizes
   9 < namespace RBM.Probe.T2039
   9 < end RBM.Probe.T2039
   2 > open RBM RBM.Loop RBM.Path
   2 >   have hb := (STBctl_pos sz n hlt).le
   2 <   have hb := (ST2_Bctl_pos sz n hlt).le
   1 > variable {d : ℕ} (sz : Sizes d)
   1 > section ScaleMoved
   1 > end ScaleMoved
   1 >     (STBctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (lt_of_le_of_lt (htT n)
   1 < open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
   1 <     (ST2_Bctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (lt_of_le_of_lt (htT n)
```
The kinds: namespace `RBM.Probe.T2039` becomes `RBM.Gauss.Sizes` (9 pairs), the `open` entry `RBM.Probe.T2039` dropped, `ST2_Bctl_pos` becomes `STBctl_pos` (3 lines), and the inserted `section ScaleMoved` holding the three §10 declarations.  No port from `../RBM1D`/`../RBM2D` (RBM1D/RBM2D diff-stat: not applicable).

### Narrative
- Moved: probe §9 `GridWhp` (5 theorems), §10 `STScaleInv`, `ST_STprof_pos`, `ST_card_lab_le` (D3), §11 `STBdata` ... `More` (the rest), 47 theorems + 2 defs in all, text verbatim except the listed renamings.
- Bridges (D1: `(hd : 3 ≤ d)`), proved from `LWterm`/`LWtermExp`; no pin changed.  Common tool `STB_prec_dom` (private): `≺` transfers along a pointwise domination of the families, eventually in `n`.
- `STB_EGt_eq_LWE` (private): `STEGt = LWE` pointwise.  The rotation is `STB_trace_six` (`tr(P(Q(R(S(TU))))) = tr(T(U(P(Q(RS)))))`, `Matrix.trace_mul_comm`) applied to the six factors `G E` of the loop; the factor order is `ring`.
- Bridge 1: `Φ_t(r) = Ψ_t(⌊r⌋₊)`, `Ψ' = max (Ψ_t(0), W^{-d/2})` (D2); `ε₀ ≤ d/2` (`STB_eps_le`) from `STPsiClass` (3) at `C = 0` and `W → ∞` (`ST_W_tendsto`, `STFlow`); constants `C₁' = C₁ 2^{C₂}`, `C₂' = C₂`, `C₃ = (c 0)⁻¹`, `Cc C = (c ⌈C⌉₊)⁻¹`; `LWLoop2` from `STLWassm` by the injection `(b, a₁, a₂) ↦ (⟨![b, !b], _⟩, ![a₁, a₂])`.
- Bridge 2: `ℓ' = 0` for `n < N₀` (`N₀` from the eventual range), range proved with `Even.pow_nonneg`, `ellT_nonneg`; `≺` for `ℓ` and `ℓ'` agree for `n ≥ N₀` (`STB_prec_dom`).
- Instances: the real/size facts use `sz0` (`W = (2(n+1))^5`, `L = 4(n+1)`): `N ≤ W^6` (`size_le_W6`), `Bctl ≥ W^{-3}/2` and `Bctl ≤ 3 W^{-3}` on `[0, 1/16]`, so `cB = 1/2`, `c = 1/4`, `N^{1/8} Bctl^{1/4} ≤ 3` (`small_sz0`, `δ₀ = 3`, `ε₁ = 1/8`); `ST_good_prob` at `D = 1`, `D' = 1`, `Dm = 6`, `K_n = ⌈N^{C_K}⌉`, `Mart`, `Rem` from `STGridMart 3`, `ρ₁ ≡ 1`, `r₀ = N^{C₀ - C_K/2 + 2}`, `a₀ = 2 N^{1/8} Bctl^{1/5}`, the four events are `ST_event_weak/init/lw/mg` at the same data.
- The `Prec`-level examples of §9 use constant families (`F ≡ 1/2`, `Z ≡ 1`); the event examples take their premises from the pins above, not from constant families.
- Special case: the bridges are conditional adapters (`LWterm d → STLWB d` for `3 ≤ d`); they prove neither pin.

## (c) Verified Mathlib names (`#check` in `names.lean` over `import RBM3D.Induction.Step2Events`, all resolved; the script output is `names.out`)
- Nat.floor_le_floor
- Nat.floor_le_ceil
- Nat.lt_floor_add_one
- Nat.le_floor
- Nat.floor_le
- Nat.floor_natCast
- tendsto_rpow_neg_atTop
- Real.rpow_le_rpow_of_exponent_le
- Real.rpow_le_rpow_of_exponent_ge
- Real.rpow_le_rpow_of_nonpos
- Real.rpow_add_one
- Real.rpow_natCast
- Real.mul_rpow
- Real.inv_rpow
- Real.rpow_neg
- Real.rpow_neg_one
- Real.rpow_mul
- Real.one_le_rpow_of_pos_of_le_one_of_nonpos
- Real.rpow_lt_one
- Real.volume_Icc
- Matrix.trace_mul_comm
- le_inv_mul_iff₀
- div_le_div₀
- pow_le_pow_left₀
- Even.pow_nonneg
- Filter.eventually_atTop
- Filter.Tendsto.eventually_ge_atTop
Names verified absent: none searched.  Deprecated in this toolchain: `push_neg` (use `push Not`), `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`; occurs in the moved text only).

## (d) Open issues and paper-delta candidates
- T2080a: the bridges `STLWB_of_LWterm`, `STLWT_of_LWtermExp` carry `(hd : 3 ≤ d)`: the Step 2 pins `STLWB d`, `STLWT d` have no `3 ≤ d` premise, `LWterm d`, `LWtermExp d` have (D1; the paper's `lem:LWterm`, `lem: EWGn2_N` are for `d ≥ 3`).
- T2080b: `STLWB` binds the control of `(initialGT2)` to `Ψ_t(0)`, `LWAssm` takes `Ψ'` separately; the bridge uses `Ψ' = max (Ψ_t(0), W^{-d/2})` because `LWWindow` has no constant while `STPsiClass` (3) has one (D2).
- T2080c: `Φ_t(r) = Ψ_t(⌊r⌋₊)` for real `r` (`LWPsiRel` is stated for `ℓ ∈ ℝ`, `STPsiClass` for `r ∈ ℕ`), constants `C₁' = C₁ 2^{C₂}`.
- T2080d: bridge 2 changes `ℓ_n` at finitely many `n` (`∀ᶠ n` in `STLWT`, `∀ n` in `LWAssmExp`).
- T2080e: continuation of T2071a/T2071b: namespace `RBM.Gauss.Sizes`, `ST2_Bctl_pos` is `STBctl_pos`; `STScaleInv`, `ST_STprof_pos`, `ST_card_lab_le` (probe §10) now live in `Step2Events.lean`: ST2-04 imports them.
- T2080f: registry: `STStep1Weak`, `STScaleInv` added to `owedProps` (class proposed: owed); comments of `STLWB`, `STLWT`, `STGoodAt` updated.
- Hub note: `RBM3D/Test/Axioms.lean` changed on `main` after the branch point (T2077); the branch is rebased onto `a91ac93` and the diff to `main` is 8 lines there.
- Not proved here: `LWterm`, `LWtermExp` (LW gate); `STBdata` is a definition (`ST_Bdata_holds` is ST2-04).
- The instances of `ST_event_*`, `ST_good_prob` take `STLWT 3`, `STEMn2Exp 3`, `STStep1Weak`, `STDecay`, `STScaleInv`, `STGridMart 3` as hypotheses; they are pins of other gates (CLAUDE.md §4 step 2).
