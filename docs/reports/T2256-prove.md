Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 05:07:14 UTC 2026

### (i) Exponent table

Notation: `s₁ = max(s, 1−c₁)`, `x = 1−t`, `Bctl_t = W^{-d}[(g²+x)⁻¹ + (L^d x)⁻¹]` (`Bparam d L g t 0`, `Params.lean:36`; `g = sz.lam n`),
`η_u = (1−u) Im m(E, g₀')`, `g₀' = BAflowLam0 sz z'`. Slack numbers are from the script in (ii).

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `c₁` | `(0, 1/2]`; instance 1/3 | `s₁ ≥ 1/2 > 0`; `1−u ≥ c₁` for `u < 1−c₁` | `s₁ = 2/3` |
| 2 | `κ` | instance 1/2 | `Im m(E,g₀') ≥ κ` (`BAFamZ_im_m_ge`, via `BAFamZ_mono` to `Fam(0)`, needs `0 ≤ t`: from `0 ≤ s ≤ t`, resp. `0 ≤ u ≤ t`) | `Im m = 0.99949` (n=0), `1.00000` (n≥1) |
| 3 | `κ', ε'` | existential in `BAFlowMember` (`κ' ≤ κ`, `ε' ≤ ε`, `> 0`) | pins `BAGbEXPii/ij` are applied at `(κ',ε',𝔡)` (hypotheses `0<κ'`, `0<ε'`, `0<𝔡` hold) | none needed: no value of `κ',ε'` enters any bound |
| 4 | `𝔡`, `lam ≤ 𝔡⁻¹` | 1/10, `lam ≤ 10` (`Admissible`, `WO`) | holds eventually in `n` | `lam_0 = 1/64` |
| 5 | times | `0 ≤ s ≤ u ≤ t ≤ t₀(z) < 1` | `t₀ = Im m/(Im m + Im z)` (`BAflow_T0_bounds`) | `t₀ = 0.69374` (n=0), `25/36 = 0.69444` (n≥1) vs `t = 2/3`: `≥ 0.0270` |
| 6 | member horizon | `n ≥ n₀`: `u ≤ t ≤ t₀(z) → u ≤ t₀(z')` | `BAFamZ_horizon`; `n < n₀`: `z'' = z` | 0 (equality case `u = t₀(z)` allowed) |
| 7 | (a) `η_{s₁}` | `η_{s₁} = (1−s₁) Im m(E,g_{s₁}) ≤ 1−s₁` | `\|m\| ≤ 1` (`BAself_norm_le_one`; if no solution `Im m = 0`) | `\|m(g_s)\| = 0.9995`, bound `1/3` |
| 8 | (a) ratio | `η_{s₁}/η_u ≤ (1−s₁)/((1−u)κ)` | constant `κ^{-(k−1)} = 2^{k−1}` absorbed | — |
| 9 | (a) monotonicity | `(1−s₁)Bctl_{s₁} ≤ (1−s)Bctl_s` | `x ↦ x/(g²+x) + L^{-d}` increasing, `1−s₁ ≤ 1−s` | **zero slack in the limit** (ratio of the two sides `0.99976` at n=0, `→1`): the bound must be used without any lost constant |
| 10 | (b) `η_u` | `η_u ≥ c₁κ = 1/6` | `u < s₁ ⇒ u < 1−c₁` (since `u ≥ s`, `s₁ = max(s,1−c₁)`), so `1−u > c₁` | `η_u = 0.937`; slack `0.77` |
| 11 | (b) constant | `C_k = (c₁κ)^{-k}(𝔡⁻²+1)^{k−1} = 6^k 101^{k−1}` | `η^{-k}(W^{-d})^{k−1} ≤ C_k (((1−s)/(1−u))Bctl_s)^{k−1}` using `W^{-d} ≤ (g²+1)Bctl_s` (`s1_Wd_le_Bctl`), `(1−s)/(1−u) ≥ 1` | k=1,2,3 at n=0: `1.07 ≤ 6`, `3.5e-5 ≤ 0.12`, `1.1e-9 ≤ 2.4e-3` |
| 12 | `k = 1` | RHS `= 1` | `omegaC·\|𝓛^{(1)}\| ≤ C₀` surely (`𝓛^{(1)}_a = W^{-d}Σ_{x∈[a]}G_{xx}`, `Eblk` = `W^{-d}`-normalised) | 0 |
| 13 | `baM_entry_le` | `‖M_xy‖ ≤ ‖M‖_op ≤ (Im m)⁻¹` | `M = (g₀Ψ − (E+m))⁻¹` (`Mres`, `GLoopFlow.lean:81`), `gΨ` Hermitian (`g` real), `Im(E+m) = Im m > 0` | operator norm bound is **sharp**: `‖M‖ = 1.000508 = 1/Im m`; `max\|M_xy\| = 0.99949` |
| 14 | `baOmegaC_eq_one` | threshold `C = 1 + (Im m)⁻¹` | `‖G−M‖_max ≤ 1 ⇒ ‖G_xy‖ ≤ 1 + (Im m)⁻¹` | `C = 2.0005`. S2b2 will need the constant `C₀ = 1+κ⁻¹ = 3 ≥ C` (`Im m ≥ κ`): the stated 4b is at the `n`-dependent threshold only; an indicator-monotonicity step is needed there (not a target here) |
| 15 | pins' `ε₀` | any `ε₀ > 0` (instance 1) | `BAGiiGEX`/`BAGijGEX` at `u` with `0 ≤ u ≤ t₀(z'')` | — |
| 16 | **ConArg premise time range** (target 5, `BABootstrap'`) | `{u : ∀n, s₁ n ≤ u n ∧ u n ≤ t n}` | nonempty iff `s₁ n ≤ t n` for **all** `n` | **FAILS** for `t n < 1−c₁` at one `n` (see findings) |
| 17 | corrected premise range | `s₁ ≤ u ≤ max(t, 1−c₁)` | `u' = max(u,s₁) ≤ max(t,1−c₁) < 1`; `g_s = √(s₁/u')g₀'` in the window `[√(1−c₁)g₀, g₀]` (`u' ≤ t ≤ t₀'` if `t ≥ 1−c₁`; `u' = s₁ = 1−c₁` and `g_s = g₀'` if `t < 1−c₁`) | — |

**Findings.**
- **P1 (confirmed).** Target 3: `BAFamZ_mono` (`Fam(t) ⊆ Fam(0)`, `0 ≤ t`) → `BAFlowMember` gives `n₀` and `BAFlow sz κ' ε' 𝔠 𝔡 z''`, `z'' = if n<n₀ then z else z'`; `0 ≤ u ≤ t₀(z'')` (row 6); pin at `z''`; `PrecL_congr` back to `z'`: `baFMz sz z''` and `baFMz sz z'` agree for `n ≥ n₀` since `BAflowEs n`, `BAflowLam0 n` depend on `z n` only (`FlowPins.lean:540-546`, `BAflowT0 = BAt0 (z n) (BAm … (z n))`). `step1TargetV3_holds` uses only `hii`, `hij` (`Step1.lean:526-534`; `STGbEXPav` unused, `Step1Setup.lean:79`), so S2b2 has signature `BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d` (after the premise correction of row 17).
- **P2.** `7_8:1916-1946` (b) is for `(G_t−M)_{xy}`, `M = M^{(B)}⊗I`; no `|M_xy|` term is needed. The band weak-law core `s1_wl_det` (`Step1Setup.lean:1064`) takes the diagonal bound on `STGM = G−m` and the off-diagonal on `G_{xy}`, `x≠y`; with `M_xy` in place of `m` the diagonal is `G_xx − M_xx = G_xx − m` (`7_8:1857`, `M_aa ≡ m`) and the off-diagonal bound for `‖(G−M)_{xy}‖²` enters the same way, so the weak law closes with `G−M` (core also uses `‖G‖_max ≤ C₀` from row 14). **But** the pinned right side (`gexRHS`: nearest-neighbour sums of random 2-loops `+ W^{-d}1_{|a−b|≤1}`, squared, with an indicator) is the band text `3_5:24`, not the printed BA text: `(GijGEX_BA)` `7_8:1940-1944` is linear, with deterministic `Φ_t`, weights `e^{-c(|a'−a|+|b'−b|)}`, `Ψ_t e^{-c|a−b|}`, `W^{-D}`. The pin is stronger than the printed lemma in this respect. For `g ≍ 1` (allowed, `g ≤ 𝔡⁻¹`) `M_ab` decays only like `(Cg)^{|a−b|}` (`7_8:1891`, `Mbound_AO`), and no file here proves the nearest-neighbour form; its source `[RBSO1D, L6.1]` is not in the repository. Recorded for `T2256a`; the pins are hypotheses of this ticket, so no target of this ticket depends on their truth.
- **P3.** `Im m ≥ κ` on the family (row 2) gives `‖G‖_max ≤ 1 + κ⁻¹ = 3` on `{‖G−M‖_max ≤ 1}` (band: `C₀ = 2`); `ConArg''` holds for every `C₀ > 0`, so `C₀ = 3` is admissible. Rows 13-14 verified numerically below.
- **P4.** Right-side arithmetic of target 5: case (a) rows 7-9, case (b) rows 10-11, `k = 1` row 12, all at `sz0`, `zSeq`, `c₁ = 1/3`; script in (ii).
- **P5.** Source ranges that need a BA re-proof for S2b2 (script in (ii)): `Step1.lean:86-540` (455), `Continuity.lean:57-735` (679, band objects `Ω d L W`, `zt`), Bridge `Step1Setup.lean:905-1119` (215), `S1Std` region `Step1Setup.lean:135-260` (126): 1475 raw lines before the BA-specific `S1Std.hE` analogue and the time-Lipschitz bound of `BAGt`. This is above the 1500 line threshold of the ticket: propose splitting S2b2 now into S2b2a (BA `gopbound` and `step1NetLift`, the Lipschitz bound; consumes only `BAGt`, `BAflowEs`) and S2b2b (Bridge, `S1Std` analogue, `Step1.lean` §1-§4, `baBootstrap'_holds`).

### (ii) One concrete nondegenerate instance

Data: `d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`), `zSeq = zS` (`w = 6i/5`, `z+m = w`), `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `c₁=1/3`, `ε₀=1`.
Two time data: (b) the ticket's `s≡t≡u≡1/16` (`1/16 < 1−c₁ = 2/3`: the ConArg premise range is **empty**, so the premise is vacuous and only case (b) is exercised);
(a) `s≡1/2`, `t≡u≡2/3` (`s₁ = 2/3 = u`, premise range `{u ≡ 2/3}` nonempty, `t ≤ t₀` by `t0_sz0`), members `z' = zSeq` (`t₀' = t₀`) and `t₀' = 2/3 = min(t₀, max(t,1−c₁))`.
Numerics: `Ψ_B` = adjacency of `Z_L^3` (`Adj`: `zdistD = 1`), `m` solved from `(self_m)` at `(g₀', E)`, `E = BAflowE z m` (`MFixedPoint.lean:280`).

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2256/inst.py
s1 = 2/3 ; premise set {u: s1<=u<=t n for all n} nonempty?  t=1/16: False ; t=2/3: True ; t_n alternating 2/3,1/16: False
n=0 L=4 W=32 g=1.56e-02 t0=0.69374 E=3.1e-18  min Im m(E,g') on window=0.99949 (>=kappa=.5)
   (a) t0'=0.6937: |m(g_s)|=0.9995 eta_s<=1-s1=0.3333; Im m(E,g0')=0.9995>=1/2; lhs=9.292e-05<=rhs=1.859e-04; (1-s1)B_s1=3.097208e-05<=(1-s)B_s=3.097952e-05
   (a) t0'=0.6667: |m(g_s)|=0.9995 eta_s<=1-s1=0.3333; Im m(E,g0')=0.9995>=1/2; lhs=9.292e-05<=rhs=1.859e-04; (1-s1)B_s1=3.097208e-05<=(1-s)B_s=3.097952e-05
   (b) u=s=1/16: eta>=c1*kappa=1/6; k=1 1.07e+00<=6.00e+00; k=2 3.48e-05<=1.20e-01; k=3 1.13e-09<=2.41e-03
n=1 L=8 W=1024 g=2.44e-04 t0=0.69444 E=2.4e-20  min Im m(E,g') on window=1.00000 (>=kappa=.5)
   (a) t0'=0.6944: |m(g_s)|=1.0000 eta_s<=1-s1=0.3333; Im m(E,g0')=1.0000>=1/2; lhs=2.799e-09<=rhs=5.599e-09; (1-s1)B_s1=9.331414e-10<=(1-s)B_s=9.331415e-10
   (a) t0'=0.6667: |m(g_s)|=1.0000 eta_s<=1-s1=0.3333; Im m(E,g0')=1.0000>=1/2; lhs=2.799e-09<=rhs=5.599e-09; (1-s1)B_s1=9.331414e-10<=(1-s)B_s=9.331415e-10
   (b) u=s=1/16: eta>=c1*kappa=1/6; k=1 1.07e+00<=6.00e+00; k=2 1.06e-09<=3.62e-06; k=3 1.05e-18<=2.18e-12
n=5 L=24 W=248832 g=3.35e-07 t0=0.69444 E=1.2e-22  min Im m(E,g') on window=1.00000 (>=kappa=.5)
   (a) t0'=0.6944: |m(g_s)|=1.0000 eta_s<=1-s1=0.3333; Im m(E,g0')=1.0000>=1/2; lhs=1.947e-16<=rhs=3.895e-16; (1-s1)B_s1=6.491017e-17<=(1-s)B_s=6.491017e-17
   (a) t0'=0.6667: |m(g_s)|=1.0000 eta_s<=1-s1=0.3333; Im m(E,g0')=1.0000>=1/2; lhs=1.947e-16<=rhs=3.895e-16; (1-s1)B_s1=6.491017e-17<=(1-s)B_s=6.491017e-17
   (b) u=s=1/16: eta>=c1*kappa=1/6; k=1 1.07e+00<=6.00e+00; k=2 7.38e-17<=2.52e-13; k=3 5.11e-33<=1.06e-26
baM_entry_le n=0: max|M_xy|=0.999493 <= ||M||=1.000508 <= 1/Im m=1.000508 ; omegaC threshold 1+1/Im m=2.000508 <= 1+1/kappa=3
baM_entry_le n=1: max|M_xy|=1.000000 <= ||M||=1.000000 <= 1/Im m=1.000000 ; omegaC threshold 1+1/Im m=2.000000 <= 1+1/kappa=3
```
The script asserts `t₀ ≥ 2/3`, `Im z ≥ 11/30` (merged `t0_sz0`, `zSeq_im_ge`) and `m(E,g₀) = m_S/√t₀` (merged `BAmF_sz0_eq`) at each printed `n`.

```
$ for each of Step1.lean:86-540, Continuity.lean:57-735, Step1Setup.lean:905-1119, Step1Setup.lean:135-260: awk 'NR>=a&&NR<=b' | wc -l
RBM3D/Induction/Step1.lean:86-540 455
RBM3D/Induction/Continuity.lean:57-735 679
RBM3D/Induction/Step1Setup.lean:905-1119 215
RBM3D/Induction/Step1Setup.lean:135-260 126
```

External hypotheses of the instance and their limits:
- `hwin : BAWinBulk sz0 zSeq (1/3) (1/2)`: window `[√(2/3) g₀, g₀]`, min `Im m(E,g') = 0.99949` (n=0), `1.00000` (n≥1) `≥ 1/2` (printed above); limit: `g → 0`, `E → 0` (`E_n ≤ 3.1e-18` at n=0, `Re m_S = 0` by the symmetric spectrum of `Ψ_B`), `m → i` from `m = (−E−m)⁻¹`, `Im m → 1`.
- `hmem : BAFlowMember 3` is used only at `z' = zSeq = z`, `n₀ = 0`, where its conclusion is `BAFlow sz0 κ ε 𝔠 𝔡 zSeq` = merged `flow_sz0` (`Im m ≥ 4/5`, `Im z ∈ [11/30, 7/10]`); no further limit.
- `hii : BAGbEXPii 3`: owed pin (BA-G6), a hypothesis of the example; the instance evaluates it at `u ≡ 1/16` or `2/3 ≤ t₀`, `ε₀ = 1`, `0 ≤ u ≤ t₀`.
- ConArg premise of `baBoot_LI` at (a): `{u ≡ 2/3}`; `baConArg''_holds 3` applies with `ε₁ = 1/2`, `s₁ ≡ u ≡ 2/3 < 1`, `κ ≤ Im m(E,g_s)` (`g_s = g₀'`, `0.99949 ≥ 1/2`), and its `STLmaxgL` premise at time `2/3 = 1−c₁` is `BATrivialLmax_holds` (merged), so this premise is derivable at the instance.

### Verdict per target
- Target 1 pins `BAGiiGEX`, `BAGijGEX`, `BAGavLGEX`, `BAGbEXP*`, `BAFlowMember`, vocabulary: **PASS** (P2 risk on the `BAGijGEX` right side recorded above for `T2256a`; not blocking).
- Target 1 `BABootstrap'`: **FAIL** as pinned. Its ConArg-premise hypothesis `∀ u, (∀ n, s₁ n ≤ u n) → (∀ n, u n ≤ t n) → …` has no `u` as soon as `1−c₁ > t n` for one `n` (row 16; ticket instance `t ≡ 1/16`), so the premise carries no information, while the conclusion at those `n'` with `t n' ≥ s₁ n'` still needs the loop bound at times in `[s₁, t]`. Corrected text: replace `(∀ n, u n ≤ t n)` by `(∀ n, u n ≤ max (t n) (1 - c₁))` (row 17; checked: `u' = max(u, s₁)` is admissible and `BAConArg''` hypotheses hold at `u'`).
- Target 2 (`BAFamZ_mono`, `BAFamZ_horizon`, `PrecL_congr`): **PASS**.
- Target 3 (`baGii_member`, `baGij_member`): **PASS** (P1).
- Target 4 (`baM_entry_le`, `baOmegaC_eq_one`): **PASS** (rows 13-14, numerics above; sharp constant).
- Target 5 (`baBoot_LI`): **FAIL** as stated, same premise defect; with the premise range of row 17 in `baBoot_LI_stmt` the arithmetic closes in both cases and `k = 1` (rows 7-12, script). Needed edit: the same replacement `u n ≤ max (t n) (1 - c₁)` in `baBoot_LI_stmt`; the glue per `n` then uses `u' = max(u, s₁)`.
- P5: S2b2 above 1500 lines, split proposed (see P5).
- Overall: **FAIL** (premise of `BABootstrap'` and `baBoot_LI_stmt`).

### (a′) Preflight corrections — Tue Oct  6 05:47:02 UTC 2026
- Stage 1a returned FAIL on targets 1 (`BABootstrap'`) and 5 (`baBoot_LI`) only (rows 16-17 above). Amend 1 (`docs/tickets/T2256-amend-1.md`) replaces `(∀ n, u n ≤ t n)` by `(∀ n, u n ≤ max (t n) (1 - c₁))` in both; the compiled pins and `baBoot_LI` below are the amended texts (`rfl`/`example` against the recompiled check file, section (b)). The verdict FAIL of (a) for these two targets is superseded by row 17 of (a); targets 2-4 stand as in (a).
- No other correction to (a). Row 14's remark stands: `baOmegaC_eq_one` is at the `n`-dependent threshold `1 + (Im m)⁻¹`, as pinned. The compiled instances use the (a) data of case (a) (`s ≡ 1/2`, `t ≡ u ≡ 2/3`) and `u ≡ 1/2 < s₁ = 2/3` for case (b), not the vacuous-premise data `s ≡ t ≡ u ≡ 1/16`.

## (b) Script output — Tue Oct  6 05:47:02 UTC 2026
```
$ git log -1 --format="%h %s" && git status --short
092370e T2256: BA event forms of lem_GbEXP_BA, BABootstrap', member transfer, baBoot_LI (BA-S2b1)
$ lake build RBM3D.BA.Step1Boot 2>&1 | grep -c "Step1Boot.lean.*warning\|error"   (warnings/errors in the new file)
exit=0
0
$ lake build RBM3D.BA.Step1Boot 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3753 jobs).
$ lake build   (full library, before the hub adds the root import; includes #assert_rbm_axioms)
exit=0
Build completed successfully (4061 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/Step1Boot.lean
0
$ wc -l RBM3D/BA/Step1Boot.lean
     834 RBM3D/BA/Step1Boot.lean
$ git diff --stat main...t/T2256
 RBM3D/BA/Step1Boot.lean | 834 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   5 +
 2 files changed, 839 insertions(+)
```

```
$ lake env lean scratchpad/T2256/axioms.lean   (#print axioms of the 20 public declarations of the file; "std3" = [propext, Classical.choice, Quot.sound])
std3 count: 20 of 20; other lines: 0
'PrecL_congr': std3
'baGii_member': std3
'baGij_member': std3
'baM_entry_le': std3
'baOmegaC_eq_one': std3
'baBoot_LI': std3
'Step1BootInst.inst_baGii_member': std3
'Step1BootInst.inst_baGij_member': std3
'Step1BootInst.inst_baM_entry_le': std3
'Step1BootInst.inst_baOmegaC_eq_one': std3
'Step1BootInst.inst_baBoot_LI_a': std3
'Step1BootInst.inst_PrecL_congr': std3

$ lake env lean scratchpad/T2256/stmt_check.lean   (= docs/tickets/checks/T2256-check.lean + import RBM3D.BA.Step1Boot + 13 acceptance examples)
exit=0  lines with error/sorry: 0  examples: 17 (4 in the check file, 13 added)
example : @RBM.BA.BAGbEXPii = @RBM.BA.T2256Check.BAGbEXPii := rfl
example : @RBM.BA.BABootstrap' = @RBM.BA.T2256Check.BABootstrap' := rfl
example (d : ℕ) : T2256Check.baGii_member_stmt d := RBM.BA.baGii_member d
example (d : ℕ) : T2256Check.baBoot_LI_stmt d := RBM.BA.baBoot_LI d
$ grep -c "RBM1D\|RBM2D" RBM3D/BA/Step1Boot.lean   (no text of RBM1D/RBM2D is ported or cited in the file)
0

$ instances: awk from each "theorem inst_*" to its ":=" (signature only)
theorem inst_baGii_member (hii : BAGbEXPii 3) (hmem : BAFlowMember 3)
    (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) : BAGiiGEX sz0 zSeq (fun _ => 1 / 2) 1 :=
theorem inst_baM_entry_le (n : ℕ) (x y : Idx 3 (sz0.L n) (sz0.W n)) :
    ‖(baFM sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).M n x y‖ ≤
      ((BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n).im)⁻¹ :=
theorem inst_baOmegaC_eq_one (ω : sz0.SeqΩ) :
    (baFMz sz0 zSeq).omegaC 0 0 (1 + ((BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im)⁻¹) ω = 1 :=
theorem inst_hcon (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    ∀ u : ℕ → ℝ, (∀ n, max ((fun _ => (1 / 2 : ℝ)) n) (1 - 1 / 3) ≤ u n) →
      (∀ n, u n ≤ max ((fun _ => (2 / 3 : ℝ)) n) (1 - 1 / 3)) →
      ∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
        BAConArgLoop'' sz0 zSeq (fun n => max ((fun _ => (1 / 2 : ℝ)) n) (1 - 1 / 3)) u k C₀ := by
theorem inst_baBoot_LI_a (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) (C₀ : ℝ) (hC₀ : 0 < C₀) (k : ℕ) (hk : 1 ≤ k) :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
      (fun n p ω => (baFMz sz0 zSeq).omegaC n ((fun _ => (2 / 3 : ℝ)) n) C₀ ω *
        ‖(baFMz sz0 zSeq).L n ((fun _ => (2 / 3 : ℝ)) n) p.1 p.2 ω‖)
      (fun n _ _ => ((1 - (fun _ => (1 / 2 : ℝ)) n) / (1 - (fun _ => (2 / 3 : ℝ)) n)) ^ (k - 1) *
        (sz0.Bctl n ((fun _ => (1 / 2 : ℝ)) n)) ^ (k - 1)) :=
theorem inst_BAFamZ_mono : BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 2) zSeq :=
theorem inst_BAFamZ_horizon (n : ℕ) : (2 / 3 : ℝ) ≤ BAflowT0 sz0 zSeq n :=
theorem inst_PrecL_congr :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun _ => Unit)
        (fun n _ ω => ‖(baFMz sz0 zSeq).L n (1 / 2) (fun _ : Fin 1 => true) (fun _ => 0) ω‖) (fun _ _ _ => 1) ↔
      PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun _ => Unit)
        (fun n _ ω => ‖(baFMz sz0 (fun n => if n < 5 then 0 else zSeq n)).L n (1 / 2)
          (fun _ : Fin 1 => true) (fun _ => 0) ω‖) (fun _ _ _ => 1) := by
(also inst_baGij_member, inst_baBoot_LI_b: same shape; lines 719, 800 of the file)
```

```
$ extract the target statements: awk from the "theorem <name>" line to the first line ending in ":= by"
theorem baGii_member (d : ℕ) :
    BAGbEXPii d → BAFlowMember d →
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
            ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀ := by
theorem baGij_member (d : ℕ) :
    BAGbEXPij d → BAFlowMember d →
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
            ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀ := by
theorem baM_entry_le (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
      ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFM sz lam0 E).M n x y‖ ≤ ((BAmF sz lam0 E n).im)⁻¹ := by
theorem baOmegaC_eq_one (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 < (BAmF sz lam0 E n).im →
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFM sz lam0 E).GM n u ω x y‖ ≤ 1) →
      (baFM sz lam0 E).omegaC n u (1 + ((BAmF sz lam0 E n).im)⁻¹) ω = 1 := by
theorem baBoot_LI (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
              (∀ u : ℕ → ℝ, (∀ n, max (s n) (1 - c₁) ≤ u n) → (∀ n, u n ≤ max (t n) (1 - c₁)) →
                ∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k →
                  BAConArgLoop'' sz z' (fun n => max (s n) (1 - c₁)) u k C₀) →
              ∀ C₀ : ℝ, 0 < C₀ → ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
                PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
                  (fun n p ω => (baFMz sz z').omegaC n (u n) C₀ ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
                  (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) := by
```

```
$ name-clash grep (scratchpad/T2256/clash.sh): for each new public name N, count of  (def|theorem|lemma|abbrev|structure|namespace) N  in RBM3D/ outside Step1Boot.lean and Probe/
FlowFM.indMax=0;FlowFM.gexRHS=0;bandFM_indMax=0;bandFM_gexRHS=0;BAGiiGEX=0;BAGijGEX=0;BAGavLGEX=0;BAGbEXPii=0;BAGbEXPij=0;BAGbEXPav=0;BAFlowMember=0;BABootstrap'=0;BAFamZ_mono=0;BAFamZ_horizon=0;PrecL_congr=0;baGii_member=0;baGij_member=0;baM_entry_le=0;baOmegaC_eq_one=0;baBoot_LI=0;Step1BootInst=0
$ same names on the other t/T22[45]* branches (git grep outside Probe/):
       0

$ registry pre-check (DECISIONS §20 (2)): scratchpad/T2256/precheck.lean = import RBM3D, import RBM3D.BA.Step1Boot, #assert_rbm_axioms
  before the 5 registry lines:
precheck.lean:3:0: error: axiom audit: 3 premise(s) that no theorem of this development proves are in none of `borrowedPr
  [RBM.BA.BAFlowMember, RBM.BA.BAGbEXPij, RBM.BA.BAGbEXPii]
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed).
  after (exit=0):
axiom audit: 7615 theorems, 2557 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
153:  RBM.BA.BAGbEXPii: 2 [no certificate]
154:  RBM.BA.BAGbEXPij: 2 [no certificate]
155:  RBM.BA.BAGbEXPav: 0 [no certificate]
156:  RBM.BA.BAFlowMember: 4 [no certificate]
157:  RBM.BA.BABootstrap': 0 [no certificate]
$ git diff main...t/T2256 -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.BA.BAGbEXPii, -- `lem_GbEXP_BA` `(GiiGEX)` event form `1(Ω(t, ε₀)) ‖G_t - M‖²_max ≺ max 𝓛^{(2)}` over the BA ca
+   `RBM.BA.BAGbEXPij, -- `lem_GbEXP_BA` `(GijGEX)` event form on `(G_t - M)_{xy}`, `x ≠ y`, over the BA carrier, `7_8:1
+   `RBM.BA.BAGbEXPav, -- `lem_GbEXP_BA` `(GavLGEX)` over the BA carrier under `(initialGT2)`, `7_8:1916-1946`; T2256 (s
+   `RBM.BA.BAFlowMember, -- finite modification of a member of `Fam(0)` is a `BAFlow` sequence (route (A), probe `T2205
+   `RBM.BA.BABootstrap', -- BA Step 1 bootstrap for one member of `Fam(t)`, event form, `7_8:1987-1990` (T2256, DECISIO
```

Narrative (what the proofs do; every other statement above is script output).
- Section 0 copies the pins of the check file (`FlowFM.indMax`, `FlowFM.gexRHS`, `BAGiiGEX/BAGijGEX/BAGavLGEX`, `BAGbEXPii/ij/av`, `BAFlowMember`, `BABootstrap'`); `rfl` against `T2256Check` above. `bandFM_indMax`, `bandFM_gexRHS` are `rfl` bridges to the band `STindMax`, `STgexRHS`.
- Section 1: `BAFamZ_mono`, `BAFamZ_horizon`, `PrecL_congr` moved from the probe `t/T2205:RBM3D/Probe/T2205Pins.lean` (commit 96e4087) lines 1299, 1304, 1508 (the probe's section variables `{d} {sz}` are written out in the signature of `PrecL_congr`; statements and proofs unchanged).
- Targets 3: `Boot_member` (`BAFamZ_mono`, `BAFlowMember`, `BAFamZ_horizon`) gives `κ', ε'`, `z'' = if n < n₀ then z else z'`, `BAFlow sz κ' ε' 𝔠 𝔡 z''`, `u ≤ t₀(z'')`, `z'' n = z' n` eventually; the pin at `z''`; `PrecL_congr` back to `z'` with `Boot_baFMz_eqAt` (the `L`, `G`, `M` fields of `baFMz` at `n` depend on `z n` only; port of the probe `baFM_eqAt`, `:1598`, restricted to these fields).
- Target 4a: `RBM.norm_inverse_entry_le` (`Analysis/Resolvent.lean:153`) at `g₀ Ψ` Hermitian and `w = E + m`, `Im w = Im m > 0`; 4b: `‖G‖ ≤ ‖G - M‖ + ‖M‖ ≤ 1 + (Im m)⁻¹` by 4a.
- Target 5 (port of band `s1_LI`, `Induction/Step1Setup.lean:774-860` at 4f186cf, with `ConArg` output as input): `k = 1`: `Ω_u |𝓛^{(1)}| ≤ C₀` surely (`Boot_L_one_le`, `Boot_omegaC_L_one_le`; copies of private `ConArg_norm_trace_mul_Eblk_le_of_diag` `:998`, `ConArg_Gres_false` `:1012`, `ConArg_gres_blockMat_true` `:1044` of `BA/ConArg.lean`, and of `Step1Trivial_seqHflowBA_herm`, `BA/Step1Trivial.lean`). `k ≥ 2`: the premise at `u' = max(u, s₁)`; per large `n` either (a) `s₁ n ≤ u n`: `u' n = u n`, `η_{s₁}/η_u ≤ (1 - s₁)/((1 - u)κ)` (`BAself_norm_le_one` via `Boot_BAm_im_bounds`; `BAFamZ_im_m_ge`), `(1 - s₁) B_{s₁} ≤ (1 - s) B_s` (`STBctl_xmono`, no lost constant: preflight row 9), constant `κ^{-(k-1)}`; or (b) `u n < s₁ n`, hence `u n < 1 - c₁`: `η_u ≥ c₁κ`, `baFM_loop_det`, `s1_Wd_le_Bctl`, `(1 - s)/(1 - u) ≥ 1`, constant `(c₁κ)^{-k} (𝔡⁻² + 1)^{k-1}`. `Boot_prec_cases` glues the two index sets per `n` (the shape of `s1_pt_of_ev_or`).
- The instance `inst_hcon` derives the ConArg premise from `baConArg''_holds 3` and `BATrivialLmax_holds` (`g_s = g₀` since `s₁ = u' = 2/3`: `lamS_two_thirds`); only `hwin` remains a hypothesis (as T2238's instance), plus the owed pins `hii/hij/hmem` where those are the targets. `inst_baOmegaC_eq_one` is at `u = 0`, where `G_0 = M` (`Boot_GM_zero`), every `ω`.
- Nothing is ported from RBM1D/RBM2D (grep count 0 above; RBM1D/RBM2D `git diff --stat` not applicable). Ported text is RBM3D's own: probe `T2205Pins.lean` (96e4087), band `Step1Setup.lean` (4f186cf), `BA/ConArg.lean` private lemmas.
- Not done here (not targets): `baBootstrap'_holds` (S2b2), proofs of `BAGbEXP*` (BA-G6) and `BAFlowMember` (BA-S3).

## (c) Verified Mathlib names (each `#check`ed by `lake env lean scratchpad/T2256/mathlib.lean`, exit 0, 0 errors/deprecations; also used in the compiled file)
`Complex.im_le_norm`, `Complex.ofReal_im`, `Complex.add_im`, `Complex.conj_ofReal`, `Complex.norm_real`, `Real.norm_of_nonneg`, `Real.rpow_nonneg`, `abs_of_pos`, `norm_le_norm_sub_add`, `norm_sum_le`, `norm_star`
`le_mul_of_one_le_left`, `one_le_pow₀`, `pow_le_pow_left₀`, `mul_le_of_le_one_left`, `lt_max_iff`, `max_eq_left`, `max_le_max`, `div_le_iff₀`, `one_le_div`, `div_mul_eq_mul_div`, `Finset.mul_sum`
`Filter.eventually_atTop`, `Filter.eventually_ge_atTop`, `Filter.eventually_congr` (not `eventually_congr`: unknown at the root namespace), `List.ofFn_succ`
`Matrix.conjTranspose_nonsing_inv`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.conjTranspose_apply`, `Matrix.IsHermitian.add`, `Matrix.IsHermitian.submatrix`
Seen deprecated during development (the compiler printed "`if_pos` has been deprecated: Use `ite_eq_left` instead", same for `if_neg`): not used in the final file.

## (d) Open issues and paper-delta candidates
- **T2256a**: `lem_GbEXP_BA` is used in the event form `1(Ω(t, ε₀)) …` of `(GiiGEX)`, `(GijGEX)`, `(GavLGEX)` of `3_5:21-33` over the BA carrier, `(GijGEX)` on `(G_t - M)_{xy}`; the printed global form `7_8:1916-1946` ((a) local laws `‖G_t - M‖_max ≺ Ψ_t`, (b) entrywise decay with `Φ_t`, `e^{-c(|a'-a|+|b'-b|)}`, `W^{-D}`) is a corollary (D539, §72 (5)).
- **T2256b**: the pinned right side `gexRHS` of `BAGijGEX` is the band's `3_5:24` form (nearest-neighbour sums of random `𝓛^{(2)}` plus `W^{-d} 1_{|a-b|≤1}`, squared estimate), not the printed BA form `7_8:1940-1944` (linear in deterministic `Φ_t`, `Ψ_t`, weights `e^{-c_λ(|a'-a|+|b'-b|)}`, `W^{-D}`). `M_{ab}` is not diagonal and `C^{-1}λ 1(a∼b) ≤ |M_{ab}| ≤ (Cλ)^{|a-b|}` only for `λ < (2C)^{-1}` (`Mbound_AO`, `7_8:1891`); that the BA proof (`[RBSO1D, Lemma 6.1]`, not in the repository) gives the nearest-neighbour form was not checked here (preflight P2). `BAGbEXPij` is an owed hypothesis; no target here depends on its truth.
- **T2256c**: (Amend 1) the ConArg-output premise of `BABootstrap'`/`baBoot_LI` is on `[s₁, max(t, 1 - c₁)]`; below `1 - c₁` the loop bound is deterministic (`baFM_loop_det`). Lean-only formulation of "same as [RBSO1D, §7.1]" (`7_8:1987-1990`).
- **T2256d**: `baOmegaC_eq_one` gives `Ω` at the `n`-dependent threshold `1 + (Im m)⁻¹ ≤ 1 + κ⁻¹`, the band's `s1_omegaC_eq_one` has the fixed `C₀ = 2` (`|m| = 1`). S2b2 needs `Ω_C ⊆ Ω_{C₀}` for `C₀ ≥ C` (indicator monotonicity, not a target here).
- `BAGbEXPav` and `BABootstrap'` are registered (ticket) though the §20 scan does not list them (no theorem assumes them yet); `BAGiiGEX/BAGijGEX/BAGavLGEX` have no registry line (not listed by the pre-check).
- The positive-time instances of `baOmegaC_eq_one` need the BA-G6 pins; the compiled one is at `u = 0` (`G_0 = M`).
- Preflight P5 (in (a)): S2b2 above 1500 lines, split S2b2a/S2b2b proposed; for the dispatcher.
