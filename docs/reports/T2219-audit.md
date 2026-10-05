Auditor model: claude-opus-5-5

# T2219 audit (MA-02 `RBM3D/Main/ZTransfer.lean`), round 1 — Mon Oct  5 22:11:34 UTC 2026

Branch `t/T2219` at `b07371e`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2219-audit1` (detached).
Scratch: `$S = <scratchpad>/T2219` (probe extract, Lean scratch files, logs).

## 1. Diff scope
```
$ git diff --stat main...t/T2219
 RBM3D/Main/ZTransfer.lean | 577 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 577 insertions(+)
```
Only the sole writable file; `RBM3D/Test/Axioms.lean`, `RBM3D/Endpoints.lean` untouched (no frozen signature changed).

## 2. Verbatim move (Targets 1)
```
$ git show 97d958e:RBM3D/Probe/T2192Pins.lean > $S/probe.lean; python3 $S/vb.py $S/probe.lean ZTransfer.lean
B0 215-223 lines 9 in file: True in order: True count: 1
B1 472-663 lines 192 in file: True in order: True count: 1
B2 776-1059 lines 284 in file: True in order: True count: 1
B3 2236-2272 lines 37 in file: True in order: True count: 1
$ sed -n '1,5p;36,44p;46p;215,223p;472,663p;774p;776,1059p;2112,2114p;2236,2272p' $S/probe.lean > $S/concat.lean
$ diff $S/concat.lean ZTransfer.lean | grep -E '^[<>]' | grep -vE '^[<>] *$'
> -/
> import RBM3D.Endpoints
> /-!
> # MA-02: the `zztE` transfer and `(eq:BtBt)` (Theorems 2.1-2.5, assembly)
  ... (13 further module-docstring lines, as listed in the prove report)
< namespace RBM.Probe.T2192
> namespace RBM.Endpoints
> end Scalars
> /-! ## The `zztE` transfer and `(eq:BtBt)` -/
> end Inst
> end RBM.Endpoints
```
(`> -/` is the copyright's closing line, displaced by the diff alignment.) Every added line is of a kind Targets 1 allows; the only removed line is the namespace rename. Import is exactly `RBM3D.Endpoints`. `size_cast` (probe `:225`) not copied.

## 3. Statements against the pins (check-file equality, compiled)
Scratch `Eq.lean` = `import RBM3D.Endpoints` + `import RBM3D.Main.ZTransfer` + `docs/tickets/checks/T2219-check.lean:26-254` + 20 examples:
`example : RBM.Endpoints.T2219Check.X_pin = RBM.Endpoints.X := rfl` (X = the 7 pins);
`example : RBM.Endpoints.T2219Check.Y_pin := @RBM.Endpoints.Y` (Y = im_identity, im_msc_ge, STWB_compare, sum_vtx, trace_four, trace_two), `Gres_blockMat_pin := @Gres_blockMat'`;
`example : RBM.Endpoints.Inst.T2219Check.inst_Z_pin := @RBM.Endpoints.Inst.inst_Z` (6 instances).
```
$ grep -c '^example' Eq.lean
20
$ lake env lean Eq.lean 2>&1 | grep -ciE 'error'; lake env lean Eq.lean >/dev/null 2>&1; echo "exit $?"
0
exit 0
```
Endpoint theorems conclude the pins with no extra hypothesis (signature lines, `grep -nE '^theorem (zRange|zGreen|zLocal|btBt|zAve|zTrace|zProfile)'`):
```
79:theorem zRange : MAZRange := by
105:theorem zGreen : MAZGreen := fun sz n _ hz ω => Sizes.Gt_lemT sz n hz ω
114:theorem zLocal : MAZLocal := by
214:theorem btBt : MABtBt := by
368:theorem zAve : MAZAve := by
394:theorem zTrace : MAZTrace := by
473:theorem zProfile : MAZProfile := by
```
Against the paper (`paper/tex/1_2_Intro_model_result.tex`), from the merged definitions read (`Endpoints.lean:58-92`, `Induction/Defs.lean:64-80`, `Loop/GLoopFlow.lean:92-165`):
- `MAZRange`: `1 - lemT z = Im z/(Im m + Im z)` is `(eq:t0E0)` `1_2:789` rearranged; `|E| ≤ 2-κ`, `1/16 ≤ t₀ < 1`, `Im z/2 ≤ 1-t₀` are extra true conclusions (bulk range of `zztE` `1_2:786`). PASS.
- `MAZGreen`: `√t₀ G_{t₀}(E) = G(z)` pointwise in `ω` (paper `=ᵈ`, `1_2:792`); the single-time carrier `Gt` is the merged definition. PASS.
- `MAZLocal`: `M = m I` (`Mband`), `|G-M|² = t₀ |G_{t₀}-m(E)|²`, i.e. `(G_bound)` from `(Gt_bound)` (`1_2:1228`). PASS.
- `MABtBt`: `STWB sz n t₀ k = W^{-d}B_{t₀,k}` (`eq_B_param` `1_2:1107`), `calB(η, Wk) = 𝓑_{η,Wk}`; two-sided bound with constants `2`, `√(κ(4-κ))/8`, `3 ≤ d`, domain hypotheses `0<Im z≤1`, `|Re z|≤2-κ`; `K = Wk` matches `B_{t,(K/W)}` of `(eq:BtBt)` `1_2:1111`. PASS (see observation O1).
- `MAZAve`: `W^{-d} Σ_{x∈[a]} G_xx = √t₀ 𝓛^{(1)}_{t₀,+,a}` (`loopM` = `tr ∏ Gres(σᵢ) E_{aᵢ}`, `Eblk = W^{-d}1_{[a]}`), `(G_bound_ave)` via `ML:GLoop` n=1. PASS.
- `MAZTrace`: `avg2 F a b = W^{-2d} Σ_{x∈[a]} Σ_{y∈[b]} F x y`; `tr(G E_b G^σ E_a) = W^{-2d} Σ_{x∈[a],y∈[b]} G_xy G^σ_yx`: loop indices `![b, a]` consistent; `(eq:diffu1,2)` `1_2:490-498`; D506. PASS.
- `MAZProfile`: `profPM = |m|²Θ^{(+,-)}_{ab}/W^d`, `profPP = m²Θ^{(+,+)}_{ab}/W^d` (`1_2:494,498`) against `t₀·𝒦^{(2)}` at `(b,a)` (`Kn2sol` `1_2:1175`); `(b,a)` vs `(a,b)` by Θ symmetry, D506. PASS.
Quantifiers: every pin quantifies only the model `sz`, `n`, `z`, `κ`, `ω`, indices; no `∀ᶠ`, no probability, no lower bound on `lam`; all hypotheses are order relations / `3 ≤ d`.

## 4. Hidden hypotheses, vacuity, cycles
- No structure carries a hypothesis besides merged `Sizes` (`L`, `W`, `lam`, `three_le_L`, `W_pos`); the seven pins are `def … : Prop` concluded by unconditional theorems and are a hypothesis of nothing here.
- Dependencies: only merged modules (closure of `RBM3D.Endpoints`); no external hypothesis, so no limit check owed.
- Name clash grep (31 names, `grep -rnE "^(private )?(theorem|lemma|def|abbrev) <n>( |$)" RBM3D --include=*.lean`, excluding ZTransfer):
```
RBM3D/Endpoints.lean:220:private theorem W_pos_real : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
RBM3D/Endpoints.lean:222:private theorem L_pos_real : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
grep done (31 names)
```
Only the intended private re-declarations; they coexist in the environment (ZTransfer imports Endpoints and builds; the registry pre-check imports both with `RBM3D`).

## 5. Compiled nonempty instances
File lines 538-573: `inst_zRange`, `inst_btBt`, `inst_zLocal`, `inst_zAve`, `inst_zTrace`, `inst_zProfile` at `d = 3`, `sz0`, `n = 0`, `κ = 1/10`, `z = zI`. Hypotheses discharged by `zI_im_pos`, `zI_im_le`, `zI_re_le`, `le_rfl` (`3 ≤ 3`), `by norm_num` (`0 < 1/10`); none left open. Data (merged):
```
RBM3D/Defs/Sizes.lean:267: theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64
RBM3D/Endpoints.lean:550: def zI : ℂ := ⟨1 / 2, ((sz0.size 0 : ℕ) : ℝ) ^ (-(4 / 5) : ℝ)⟩
RBM3D/Endpoints.lean:552: theorem zI_dom : sz0.locDomain (1 / 10) (1 / 10) 0 zI := sz0_locDomain
```
Nondegenerate (no `N = 0`, nonempty lattice, `0 < Im zI ≤ 1`); statements equal the check-file instance pins (§3). PASS.

## 6. Build and axioms
```
$ lake build RBM3D.Main.ZTransfer   (audit worktree)
✔ [3330/3330] Built RBM3D.Main.ZTransfer (5.5s)
Build completed successfully (3330 jobs).
exit 0
$ grep -cE '^error' build.log
0
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Main/ZTransfer.lean   (no output)
$ lake env lean Ax.lean     (import RBM3D.Main.ZTransfer; #print axioms of the 20 public theorems)
'RBM.Endpoints.im_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.zRange' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.zGreen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.zLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.im_msc_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.STWB_compare' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.btBt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Gres_blockMat'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.sum_vtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.trace_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.trace_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.zAve' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.zTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.zProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_zRange' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_btBt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_zLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_zAve' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_zTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_zProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ lake env lean Pre.lean    (import RBM3D; import RBM3D.Main.ZTransfer; #assert_rbm_axioms)
exit 0
axiom audit: 6457 theorems, 2229 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
$ grep -cE 'ZTransfer|MAZ|MABtBt' pre.log
0
```
No registry line needed (Targets 3). The full `lake build` is left to the hub at merge.

## 7. Paper deltas
Differences: loop indices `(b,a)` / profile symmetry (D506, cited); `L^∞` block distance `Wk` in `calB` (D501, cited); `=ᵈ` vs pointwise (merged carrier, no statement change for consumers); `≍` replaced by explicit constants (CLAUDE.md §7). No uncovered statement difference that changes a consumer.

## Observations (no RETURN)
- O1. `MABtBt` is `(eq:BtBt)` only at `t = t₀ = lemT z` and with `𝓑_{η,·}` at the endpoint `η = Im z` (paper: `𝓑_{η_t,K}`, `η_{t₀} = (1-t₀) Im m(E) = √t₀ Im z`, `1_2:721`); this is exactly the composite the paper uses at `1_2:1228` ("with (eq:zztE), (eq:BtBt)"), and the ticket pins it. The dispatcher may wish to note this reading next to D501/D506; not a defect.
- O2. The prove report's verbatim diff listing omits nothing material; its axiom block abbreviates the output as `std3` (verbatim output reproduced in §6 here).

## Verdict
| Target | Verdict |
|---|---|
| 1 Verbatim move B0-B3, 7 pins + 24 theorems (`zRange`, `zGreen`, `zLocal`, `btBt`, `zAve`, `zTrace`, `zProfile`, helpers, 6 instances) | PASS |
| 2 Imports (`RBM3D.Endpoints` only) | PASS |
| 3 Registry (no line; pre-check exit 0) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
