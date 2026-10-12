Auditor model: claude-opus-5-5
# T2434 1a-audit (design gate, under Amend 1 / H229) — Mon Oct 12 06:09:45 UTC 2026 (`date -u`)

Inputs: ticket `docs/tickets/T2434.md`, `T2434-amend-1.md` (binding), check file `docs/tickets/checks/T2434-check.lean`,
`docs/reports/T2434-prove.md` (a) and (a″), branch `t/T2434` = `024dc54` (base `e3f59c2`; main now `483a67f`).
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2434-1a-audit` (detached at `024dc54`). Scratch: scratchpad `T2434/audit1a/`.

## 1. Probe recompile (Amend 1: "recompile RBM3D/Probe/T2434Pins.lean on t/T2434 in your own detached worktree")
```
$ lake build RBM3D.Graph.BAExp14aB RBM3D.BA.TwistPins | tail -1
Build completed successfully (4005 jobs).
$ lake env lean RBM3D/Probe/T2434Pins.lean > audit_probe.txt; echo EXIT=$?      # 06:01:27 .. 06:01:33 UTC
EXIT=0
$ grep -ci 'error\|warning' audit_probe.txt
0
$ grep axioms audit_probe.txt
'RBM.BA.BAExp14bS2Fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14bS3Fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14bS2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14bS3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14bExpand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14bCutConj' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-status main...t/T2434 ; git grep -c -E 'sorry|admit|native_decide|^axiom ' t/T2434 -- RBM3D/Probe/T2434Pins.lean | wc -l
A	RBM3D/Probe/T2434Pins.lean                     # 267 lines (≤ 400), sole writable, never merged
0
$ git grep -n -i BAExp14b main -- RBM3D RBM3D.lean | wc -l ; (all refs/heads/t/*: files containing BAExp14b)
0
t/T2434:RBM3D/Probe/T2434Pins.lean
```

## 2. Pins bound to the dispatcher's templates (my own file `audit1a/bind.lean` = probe lines 1-185 + check-file section 2 verbatim)
```lean
example (d : ℕ) : BAExp14bExpand d = T2434_ExpandShape d (Fin 8) (Fin 4) BAExp14bS2Fam BAExp14bS3Fam := rfl
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : BAExp14bCutConj sz z = T2434_CutConj sz z := rfl
example (d : ℕ) : BAExp14bS2 d ↔ T2434_FamShape d (Fin 8) BAExp14bS2Fam T2434_Prem7 := by ...   -- (un)currying, 7 premises
example (d : ℕ) : BAExp14bS3 d ↔ T2434_FamShape d (Fin 4) BAExp14bS3Fam (fun sz z t => STLocalEntrygL .. ∧ LWAvgLawgL .. ∧
    STLmaxgL .. ∧ STLKgL .. ∧ STDecaygL ..) := by ...                                            -- the five of LWCutExpG
#print RBM.BA.BAExp14aS1Fam    -- σc convention reference
```
```
$ lake env lean audit1a/bind.lean ; echo EXIT=$?
def RBM.BA.BAExp14aS1Fam ... := fun {d} sz z n t ω k σc σo ac ao =>
  if σc = true then BAExp14a_F sz z n t ω k σo ao ac else star (BAExp14a_F sz z n t ω k (!σo) ac ao)
EXIT=0
```
`BAExp14bS2Fam`/`S3Fam` use the identical `if σc then F j σo ao ac else star (F j (!σo) ac ao)` (probe :169-175). Premises: S2 = the
seven of `T2434_Prem7` (incl. `BATwistAvgLaw`, `BATwistLoopLaw`, imported from `BA/TwistPins.lean`, not redefined); S3 = five, no `BATwist*`.
This is Amend 1 item 1 exactly.

## 3. The 18-family partition, checked by hand against the merged right sides
Cut (σc=+, `LWcutg` `Chain/LWGen.lean:39`, `C.S = 1`): `W^{-2d}Σ_{x∈[ao],y∈[ac]}G(σo)_{yx}Σ_α X_{[α]}G_{xα}G_{αy}`, `G = Ǧ + M`.
- `ǦǦ`: `BAGGGammaR` (`Graph/BAGGExp.lean:67`) at `(x,y,y') := (α,y,x)`, `f = X_{[α]}·tail`. Its sums give, term by term: `(W-1)_{αβ}M_{βy}M_{xβ}` = `FT1`;
  `(W-1)_{αβ}(Ǧ_{βy}M_{xβ} + M_{βy}Ǧ_{xβ})` = `FT2a + FT2b`; `W_{αw}M_{wγ}S_{γδ}[Ǧ_{δδ}G_{γy}Ǧ_{xw} + Ǧ_{γw}G_{δy}G_{xδ} − G_{δy}Ǧ_{xw}∂_{δγ}f]`
  with `W = W^{(0)} + W^{(1)}` = `FT3A_k` (`Σ_δ S_{γδ}Ǧ_{δδ} = tX_{[γ]}`) + `FT3B_k` + `FT3CG_k`/`FT3CX_k` (∂ on tail / on `X`). Matches probe :86-113, :134-138.
- `MǦ`: `M_{xα}·BAlanlwR` (`Graph/BAExpand.lean:106`) at `(α,y)` = `FC1` + `D1` (`−M_{xα}M_{αα'}S_{α'β}G_{βy}∂_{βα'}f`) = `FC1 + FD1t + FD1X`.
- `ǦM`: `BAlanlwR` at `(x,α)`, times `M_{αy}` = `FC2 + FD2t + FD2X`. `MM` = `FMM`. Union = S1(6) ∪ S2(8) ∪ S3(4), disjoint.
- Derivatives: `BAExpand_dh_of_partial` gives `∂_{h_{αw}}G_{ij} = −G_{iα}G_{wj}`, `_star_` gives `−star(G_{iw}G_{αj})`: so `BAExp14b_dtail σ x y δ γ`
  (`−G_{yδ}G_{γx}` / `−star(G_{xγ}G_{δy})`) and `BAExp14b_dX α δ γ = −W^{-d}Σ_{v∈[α]}G_{vδ}G_{γv}` are `∂_{h_{δγ}}` of tail and `X`. Correct.
- Conjugation: `conj Tr(G^*E_{a1}G^*E_{ac}G(σo)E_{ao}) = Tr(G E_{a1} G E_{ao} G(!σo) E_{ac})`, `conj(Tr(G^*E_{a1}) − m̄) = Tr(GE_{a1}) − m`, so
  `LWcutg false σo ac ao = star(LWcutg true (!σo) ao ac)`: the pin `BAExp14bCutConj` is the right identity, consistent with the `σc=false` branch of `S*Fam`.
- Forms used are merged and fully quantified (`BAGGGamma`, `BAlanlw`: `∀ x y [y']`); no transposed `lanlw` needed. Stop rule "form not merged": not hit.

## 4. Numerics rerun (prover's scripts in scratchpad `T2434/`, outputs in `T2434/audit1a/`)
```
$ python3 inst.py                                   # 06:02:59 UTC
d,L,W,N = 3 4 32 2097152 | lam = 1/64 | W^d = 32768 | L^d blocks = 64
3<=d: True | kappa,eps,dd>0: True True True | t=1/2 <= t0 lower bound 2/3 : True
kappa <= Im m (4/5): True | N^(-1+eps)= 2.0442456484533175e-06 <= 1/4: True
U_n nonempty: lam^2/L^d = 3.814697265625e-06 <= 1-t = 0.5 : True
Bparam = 2.0302739141044412 | Bctl = W^-d B = 6.195904278883183e-05 | bound (1-t)^-1 Bctl^(5/2) = 6.043544786717419e-11
$ python3 tl_base.py
TL2 at t=0 (L~ = K~ exactly, G=M): max |twL2'-twK| over all sigma,(a,c1,c2) = 1.1102230246251565e-16
TL1 at t=0 (G-circ = 0): max |twTr| = 0.0
$ python3 s3root.py
baG5Graph (BAExpandId.lean:75-83): BAGraph (Fin 2) (Fin 3) | mdot := []: True
T3C-tr_0 : internal 4 ['w', 'g', 'v', 'd'], M-dotted 1  -> is a baG5Graph (3 internal, 0 M-dotted)? False
T3C-tr_1 : internal 6 ['w', 'g', 'v', 'd', 'a', 'b'], M-dotted 3  -> is a baG5Graph (3 internal, 0 M-dotted)? False
D1X      : internal 4 ['a', 'p', 'v', 's'], M-dotted 2  -> is a baG5Graph (3 internal, 0 M-dotted)? False
D2X      : internal 4 ['p', 'v', 's', 'a'], M-dotted 2  -> is a baG5Graph (3 internal, 0 M-dotted)? False
$ python3 lean_vs_cut.py 3 40 0.7 0.0 0.2 | tail -1          # W^d = 1, Gauss-Hermite
L=3 (g0,E,t)=(0.7,0.0,0.2) nodes/var=40 total nodes=64000  max |E[cut] - sum of 18 families| = 6.022e-07   largest single family |E F| = 0.067
$ python3 lean_vs_cut_qmc.py 3 2 14 0.7 0.3 0.1 1 | tail -1  # W^d = 2, GUE blocks
L=3 Wd=2 (g0,E,t)=(0.7,0.3,0.1) Sobol 2^14=16384 seed=1  max |E[cut] - sum of 18 families| = 4.170e-05   largest single family |E F| = 0.003
$ python3 lean_vs_cut_qmc.py 3 2 18 0.7 0.3 0.1 2 | tail -1
L=3 Wd=2 (g0,E,t)=(0.7,0.3,0.1) Sobol 2^18=262144 seed=2  max |E[cut] - sum of 18 families| = 6.457e-06   largest single family |E F| = 0.003
```
All match (a)/(a″) verbatim. `baG5Graph` read directly: `BAGraph (Fin 2) (Fin 3)`, `mdot := []` (`Graph/BAExpandId.lean:75-83`) — confirmed.
**Sensitivity (mine):** each S2/S3 family doubled in turn (`qmc_pert.py`, `quad_pert.py` = the scripts with `out[PERT] *= 2`):
```
W^d=2 QMC 2^14 (baseline 4.170e-05): PERT=6 5.615e-04  7 5.869e-04  8 1.870e-04  9 1.871e-04  10 2.413e-04  11 4.194e-05
                                      12 2.668e-04  13 4.952e-05  14 3.007e-03  15 2.963e-03  16 6.826e-04  17 6.211e-05
W^d=1 quad 40 (baseline 6.022e-07):  PERT=11 9.696e-04   PERT=13 1.441e-03   PERT=17 1.783e-03
```
The checks resolve every S2/S3 family. The three `W − 1` families (11 `T3B_1`, 13 `T3C-Ḡ_1`, 17 `T3C-tr_1`) are below resolution at `W^d = 2`, `t = 0.1`.
They are resolved by the `W^d = 1` quadrature (×1600 over baseline). Their `W^{-d}` structure is that of the `k = 0` twins (same code, `Wk[k]` only),
and those are resolved at `W^d = 2`.

## 5. Design-gate deliverables (ticket "Stage 1a, design gate") and stop lines
| item | where in (a)/(a″) | finding |
|---|---|---|
| (i) family table, partition flag, routes, unused | (a) :25-36 | 18 families, owner, premises, route per S2 family; partition = DECISIONS §244 Q3 (C1, C2 in S1; `∂Ḡ` → S2; `∂tr` → S3); unused fable rows MG̊/G̊M listed. Union checked in §3. **met** |
| (ii) pins S2, S3, `σc` convention, premise subsets | (a) :50-51, probe :169-184 | bound to templates (§2). **met** (see O2 on "block form") |
| (iii) S3 vs L4d's root | (a) :38-47 | not `baG5Graph` (confirmed §4); answered by Amend 1 item 3 (owed to L4d2). Not a stop for this row. |
| (iv) probe compiles | (a″), §1 | EXIT 0, no warnings, standard axioms, 267 ≤ 400 lines. **met** |
| (v) consumers | (a) :55-56 | L4b2 / L4g-L4c1 / L4a2 named with what they read. **met** (terse; O2) |
| (vi) band ↦ BA table, untwinned §§ | (a) :58-59 | §§1-8, 11-12 mapped to file A/B; §§9-10, 13-16 not twinned with reasons. **met** |
| (vii) exponent table, instance | (a) :8-23, :64-81 | rerun §4; instance nondegenerate (`n=0`, `L=4`, `W=32`, `t=1/2`, `ac=0 ≠ ao=e₀`, compiled probe :257). **met** (O1) |
| (viii) lines per file, §§11-12 priced | (a) :61-62 | A 1,300-1,700; B 1,300-1,800 incl. §§11-12 650-850; both < 2,000. **met** |
| Instances (probe) | probe :214-262 | S2, S3, identity, conjugation applied at `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`; only other gates' pins left as hypotheses; index sets nonempty ∀ n. |

Binding stop lines: **none hit.** File stop line 2,000: predicted below for both files. Identity closes (§3 symbolic, §4 numeric, both charges).
Every S2 family has a route from the seven premises (see O1 for P3). The S3-root stop is answered by Amend 1. Every `GGGamma`/`lanlw` form needed is merged.

## 6. Observations (no statement, instance, build, axiom or paper-delta change; no RETURN)
- **O1 (P3 exponent row; for the L4b2 ticket).** (a) :14 states P3 as `|𝔼X_c| ≺ 𝔟^{3/2}` and cites L4a. The merged bound carries a `(1−t)⁻¹`:
  `theorem BAExp14a_e_bound ... : ‖BAExp14a_e sz z n t c‖ ≤ CM * ε₂ / (1 - t)` (`Graph/BAExp14aB.lean:978-979`), with `ε₂` from the private
  `BAExp14a_q_prec` (`𝔼[X_cǦ_{yw}] ≺ 𝔟^{3/2}`, from P1 and P2 only, `:1377-1382`). So P3 is derivable from the seven premises, as
  `|𝔼X_c| ≺ (1−t)⁻¹𝔟^{3/2}`. The routes that use it (`𝔼X·K` with `K ≲ 𝔟`, twK_bound (i), no `η`) stay at `(1−t)⁻¹𝔟^{5/2}`, so the target holds and no route breaks.
  The `(1−t)⁻¹` budget is spent, though: L4b2 must not pair P3 with `η⁻¹` or with twK_bound (ii) (`Σ_a‖K̃‖ ≤ C(W^dη)⁻¹`). Recommend that the dispatcher put this in L4b2's ticket.
- **O2 (block form).** Ticket (ii) says "S2 is in the block form L4b2 transcribes", but the pinned `BAExp14bS2Fam` is in fine-sum form, with the block
  forms deferred to target 3 ((a″) note 3: "not pinned by the probe"). Amend 1 item 1 fixes the pins as written, so this is accepted. The 1b must name and prove the
  block-form lemmas listed in (v) (twTie, `W−1` block, 8 block forms); the final audit checks them.
- **O3.** (a) :96 still reads "Overall: BLOCKED". Amend 1 supersedes that line. (a) has no (a′), which is correct (the probe did not edit (a)).
- **O4.** The probe was compiled against base `e3f59c2`. Main has since moved to `483a67f`. `git diff --name-status e3f59c2 483a67f -- RBM3D` lists only new
  files (`BA/TwistGrid*Tail*`, `Graph/BALvl1A`) and `Test/Axioms.lean`, so the closure of the probe's imports is unchanged.
- Paper deltas: none at this stage. The decomposition (D402 `W−1 = M⁺S⁺`, `lanlw` children split by product rule) is already covered (D402; T2418).

## Verdict
**PASS** — T2434 stage 1a (design gate + probe) under Amend 1: every design-gate deliverable is met, no binding stop line is hit, and the probe recompiles (EXIT 0, standard axioms).
1b (`prover-max`) may start. No dispatcher sign-off needed; O1 is a recommendation for the L4b2 ticket.
