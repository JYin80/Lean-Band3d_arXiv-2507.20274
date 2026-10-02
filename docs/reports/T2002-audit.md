Auditor model: claude-opus-5-5

# T2002 audit (round 1) — MD-D1 vocabulary design (report only), Fri Oct  2 23:09:48 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2002-audit1`, detached at `t/T2002` = `5d2a4a8`; `main` = `709c5c7`.
Inputs: ticket `docs/tickets/T2002.md`, check file `docs/tickets/checks/T2002-check.lean` (`#check` lines only, no pinned statement text),
prove report `docs/reports/T2002-prove.md` (297 lines), port map `docs/reports/T2002-portmap.md`, probe `RBM3D/Probe/T2002Vocab.lean`.

## 1. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Probe.T2002Vocab 2>&1 | grep -v "depends on axioms" | grep -E "error|warning|sorry|Build|^✖"
Build completed successfully (3294 jobs).
$ lake env lean RBM3D/Probe/T2002Vocab.lean > ax.txt 2>&1; echo exit=$?; wc -l <ax.txt; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.txt
exit=0
      60
60
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|unsafe|implemented_by|extern" RBM3D/Probe/T2002Vocab.lean; echo grep=$?
grep=1
$ git diff --name-only main...HEAD
RBM3D/Probe/T2002Vocab.lean
```
Exhaustive axiom check over every constant of the module (the probe prints 60 of them; scratch file `AxAll.lean`, `import RBM3D.Probe.T2002Vocab`,
iterates `env.constants`, keeps those with module `RBM3D.Probe.T2002Vocab`, runs `Lean.collectAxioms`):
```
$ lake env lean AxAll.lean 2>&1 | grep -v "^'" | tail -1
constants in module: 263; with non-standard axioms: 0 []
```
Clash / merge check (scratch `AuditInst.lean` imports `RBM3D` and `RBM3D.Probe.T2002Vocab` together; compiled with no output, see §3):
```
$ git show 709c5c7:RBM3D/Defs/SemicircleIntegral.lean | <names> | <grep each in probe>; git merge-tree --write-tree main t/T2002
clash-scan done
merge-tree clean
```
Sole writable files: the branch touches only `RBM3D/Probe/T2002Vocab.lean` (new; stays on the branch); the two reports are in the main worktree. No frozen signature touched (no merged file in the diff).

## 2. Statement-centred check: the pins against the ticket's hard constraints (item 2) and the paper

Paper lines read: `1_2:220-235` (`stoch_domination`, w.h.p.), `1_2:250-275` (lattice, blocks, `L^∞`), `1_2:290-345` (`bandcw0`, `eq:variancematrix`,
`def_Green`, `eq:defmzsc`, `eq:defMzsc`), `1_2:355-395` (`Main_DEL_COND`, `eq:WO`, `eq:spectral_domain`, `G_bound`), `1_2:600-634` (`bandcwV`,
`eq:H_blocka`, `eq:Psi3D`, `self_m`, `def_G0`), `1_2:680-724` (`MBM`, `eq:zt`, `eta`), `1_2:1105-1123,1216-1224`, `7_8:1796-1801`.

| pin (probe line) | paper | check | verdict |
|---|---|---|---|
| `Sizes d {L W lam three_le_L W_pos}` (141) | `1_2:262`, `def:ilambda` | `d` is the structure parameter; `lam : ℕ → ℝ` a sequence; no field constrains `lam` | PASS |
| `Sizes.size n = (W n * L n)^d` (160), `card_Idx` (163) | `N=(W·L)^d` (1_2:263) | `#Idx = size` proved | PASS |
| `card_Iblk : (Iblk d L W a).card = W^d` (98) | `eq:blockIa` | block size `W^d`, zero-based blocks (T2002d) | PASS |
| `Sizes.WO 𝔡` (167) | `eq:WO` 1_2:363 `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡^{-1}` | literal, eventual in `n` (T2002e) | PASS |
| `Sizes.Bandwidth 𝔠` (171), `SizeTendsto`, `Admissible` (180) | `Main_DEL_COND` 1_2:359 | `N^𝔠 ≤ W`; `𝔠,𝔡>0`; `N→∞` explicit | PASS |
| `locDomain κ ε n z` (189) | `eq:spectral_domain` 1_2:380 | `|Re z| ≤ 2-κ`, `N^{-1+ε} ≤ Im z ≤ 1` | PASS |
| `svarF` (261), `gvarF` (303), `PF` (311), `Xmat` (327) | `bandcw0`, `eq:variancematrix` | `S_xy = W^{-d} SBR(g)_{ab}`; merged `sbKernelR` = `(1+2dg²)^{-1}(1_{x=0} + g² 1_{|x|_1=1})`; real diag, two real coords of variance `S/2` off-diag; Hermitian proved; `a∼b` = `Adj` (ℓ¹ distance 1, consistent with the `2d` normalisation) | PASS |
| `seqP` (383), `seqP_map_slice` (398) | one probability space for `≺` | each size slice has law `PF` (proved) | PASS |
| `seqHflow n u = √u • seqXmat` (439) | `MBM` 1_2:686 single time, `H_0=0` | law of `H_u` only (route T2002g, DECISIONS §7) | PASS |
| `PathΩ, pathP, filt, gridTime, pathH` (948-972), `TransferLaw`, `IndepIncr` (977, 984) | `MBM` grid walk | `pathH = √s X_0 + √Δ Σ_{i≤k} X_i` has variance `u_k S`; the two pins are stated (MD-4 targets), not assumed in any definition | PASS |
| `ztOf m E t`, `etaOf` (510, 513); `zt_eq_ztOf` rfl | `eq:zt`, `eta` 1_2:717-721 | `z_t = E+(1-t)m`, `η_t = (1-t)Im m` | PASS |
| `Gres H z σ` (529), `Sizes.Gt` (607), `Gn` (620) | `def_Green`, `Def:G_loop` | `σ=false` uses `z̄`; total inverse (T2002h) | PASS |
| `Mres H0 z m` (536) | `def_G0` 1_2:632 | `(H0 - z - m)^{-1}`; band `M = m I` proved (`Mres_zero_msc`) | PASS |
| `loopM` (547), `loopFine` (565), `Sizes.Lloop` (613), `loopL` (578) | `Eq:defGLoop` 1_2:824 | `tr ∏ G(σ_i) E_{a_i}` with merged `Eblk = W^{-d} 1_{[a]}`; `Lloop_zero_one` checks `𝓛^{(1)}_{0}=m(σ)` | PASS |
| `StochDomAt P size` (813), `Prec`, `PrecPT`, `PrecGrid`, `Whp` (873-880, 1017) | `stoch_domination` 1_2:229, w.h.p. 1_2:223 | `∀τ>0 ∀D>0 ∀ᶠ n, P(∪_u{ξ > N^τ ζ}) ≤ N^{-D}`; quantifier order as paper; **one scale** `sz.size` everywhere; merged `StochDom`/`HighProb` = case `id` (`Iff.rfl`) | PASS |
| `LocalLawPT (E t : ℕ → ℝ) ζ` (886) | `Gt_bound` 1_2:1221 shape | energies and times are sequences (TEAM §8 lesson 23); general `ζ`, so the paper's squared form is an instance | PASS |
| `PsiB, PsiV, PsiI` (458-466), `seqHBA` (658), `seqHflowBA` (496) | `eq:Psi3D`, `eq:H_blocka`, `bandcwV`, `MBM` with `H_0 = ilambda Ψ` | `V` = model of `sz.withLam 0` (`S^{(B)}(0)=I`); same vocabulary; `m(z,g)`, `M^{(B)}` left to the MA layer (O4) | PASS |
| `Bctl n t = W^{-d} Bparam d L lam t 0` (217) | `eq_B_param` 1_2:1107 | merged `Bparam` = `(g²+|1-t|)^{-1}(K+1)^{-(d-2)} + (L^d|1-t|)^{-1}` | PASS |
| `W_rpow_le`, `size_rpow_le_W_rpow` (223, 240) | conversion `W^τ ↔ N^τ'` | `W^τ ≤ N^{τ/d}` (`0<d`), `N^τ ≤ W^{τ/𝔠}` under `W ≥ N^𝔠` | PASS |

Hard constraints of item 2: `d` a parameter (`3 ≤ d` appears nowhere; `0 < d` only in `W_rpow_le`); `N=(WL)^d`; block `W^d`; `lam` a sequence, never
fixed (`sz0_lam_tendsto`: `lam → 0`); energies sequences (`LocalLawPT`); one scale `N = sz.size n` (paper's own `≺` uses `N^τ`, `N^{-D}`); renaming
rule R1 `d : Sizes → sz : Sizes d`; block Anderson in the same vocabulary. All met.

## 3. Hidden hypotheses, vacuity, cycles; compiled nonempty instances

- Structure fields: `Sizes` has `three_le_L` (T2002c, already signed T2001a) and `W_pos` (`W ≥ 1`, implicit in the paper). No other `Prop` field in any pin.
- No pin definition assumes `TransferLaw`/`IndepIncr`; they stay hypotheses only of `transfer_at`, `indep_at` (MD-4 targets). Dependencies are merged RBM3D files only (imports lines 6-15). No cycle.
- Instances (namespace `RBM.Gauss.T2002Inst`, `d=3`, `n=0`: `L=4`, `W=32`, `lam=1/64`, `N=2097152`; `lam_n=(2(n+1))^{-6} → 0`): `sz0_admissible`
  (`𝔠=1/6`, `𝔡=1/10`, all five clauses proved), `z0_mem` (`z0 = 1/2 + i N^{-4/5} ∈ 𝐃_{1/10,1/10}`), `z0_zztE`, `z0_Gt`, `card_Idx_sz0`, `card_Iblk_sz0`,
  `seqP_sz0_slice`, `Gt_prec`/`Gt_whp`/`localLaw_sz0`/`Gt_timeIcc_prec` (along non-constant `Eseq n = 1/(n+2)`), `gridRes_prec` (grid time `1/4`,
  `gridTime_sz0`), `Lloop_sz0`, `loop_envelope`, `Mres_sz0`, `transfer_at`, `W_le_size_sz0`, `size_le_W_sz0`. None uses `N=0`, an empty index,
  a collapsed window or a `False` premise; all compile (§1).
- `Gt_BA_sz0` keeps `hlam0 : lam0 0 = √t0·lam 0` and `hzt : ztOf m0 E t0 = √t0·z0` (the two clauses of `eq:t0E0_BA`/`eq:zztE_BA`, MA layer). Auditor
  non-vacuity check: both discharged at concrete data (scratch `AuditInst.lean`, compiled with no output, exit 0):
```
example (ω : Sizes.SeqΩ sz0) :
    (Real.sqrt (1/4) : ℂ) • Gres (sz0.seqHflowBA (fun n => Real.sqrt (1/4) * sz0.lam n) 0 (1/4) ω)
      (ztOf ((Real.sqrt (1/4) * z0 - (0:ℝ)) / (1 - (1/4:ℝ))) 0 (1/4)) true = Gres (sz0.seqHBA 0 ω) z0 true := by
  refine Gt_BA_sz0 _ _ 0 (1/4) (by norm_num) rfl ?_ ω
  have h : (1 - ((1/4 : ℝ) : ℂ)) ≠ 0 := by norm_num
  simp only [ztOf]; push_cast; field_simp; ring
$ lake env lean AuditInst.lean 2>&1 | head -20   # (no output)
```
- External hypotheses: none (no pin carries the DECISIONS §5 input).

## 4. Items 1 and 4 (inventory, port map) re-checked by script

```
$ python3 <parse portmap part C; for each row: git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/<dir>/<file> | count lines>
rows 326
mismatches 0
Counter({'Induction': 60, 'Universality': 56, 'Gauss': 47, 'Hierarchy': 47, 'Path': 42, 'Green': 34, 'Evolution': 24, 'Main': 9, 'Defs': 7})
Counter({'b': 200, 'a': 56, 'd': 45, 'c': 25})
lean files in nine dirs at c9a24cf: 326
$ python3 <RBM3D inventory at 3c11d7b: files / lines per group>
Defs 11 files 2615 lines 37 defs (incl. private)
Gauss 5 files 1088 lines 12 defs (incl. private)
Loop 1 files 293 lines 5 defs (incl. private)
Analysis 1 files 180 lines 0 defs (incl. private)
```
Every port row cites the RBM2D file and its line count at `c9a24cf` (0 mismatches); file and line totals of item 1 (i) match the report (b.4);
the class totals match b.5 (56/200/25/45). Split table (b.6, portmap E.2) and the first ST design tickets are present.

## 5. Paper-delta coverage

Every Lean/paper difference found in §2 is proposed: `lam` = `\ilambda` naming (T2002a); `L^∞` vs merged `ℓ¹` (T2002b); `three_le_L` (T2002c);
zero-based blocks (T2002d); "N sufficiently large" → `∀ᶠ n` (T2002e); merged `Gsig` built on the time-one `Hmat` (T2002f); single-time law + grid walk
carrier, per-time `≺` (T2002g); `Ring.inverse` resolvent (T2002h); `W^τ` vs `N^τ` scale (T2002i). No uncovered difference found.

## 6. Observations (no RETURN)

1. The probe prints axioms for 60 of 263 constants; the auditor's exhaustive check (§1) covers all 263.
2. `Gt_BA_sz0` leaves two deterministic clauses as hypotheses; they are the content of the cited `zztE_BA` (MA gate). The auditor's compiled example
   (§3) shows they are jointly satisfiable at `sz0`; a downstream MA/MD-3 ticket should state the instance with `m0 = m(E, λ0)`.
3. `Gt_prec`, `localLaw_sz0`, `gridRes_prec`, `Gt_timeIcc_prec` instantiate `≺` through the deterministic Ward bound (`prec_of_le`); this exhibits
   the pins at nondegenerate data, not a probabilistic estimate (none is claimed).
4. My raw-regex count of RBM3D `Defs` definitions is 37 vs the report's 39 (elaborated environment, portmap A.1); file and line totals agree.
5. Open issues O1 (RBM2D port commit `c9a24cf` vs trimmed `0c1330a`/`79985ee`) and O2 (paper-form endpoint needs the lifts RBM2D deleted) are
   dispatcher items for the downstream MD/ST tickets; they do not affect this ticket's statements.

## Verdict

| target | verdict |
|---|---|
| 1 inventory | PASS |
| 2 decisions + hard constraints | PASS |
| 3 pins (probe) | PASS |
| 4 port map | PASS |
| 5 split table | PASS |
| 6 instances | PASS |

**T2002: PASS.** Report-only ticket; the probe stays on `t/T2002`; the hub merges the reports (rule (A), report-only path).
