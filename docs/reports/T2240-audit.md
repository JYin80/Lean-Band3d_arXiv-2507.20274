Auditor model: claude-opus-5-5

# T2240 audit (MA-05a, `RBM3D/Main/QUECore.lean`): round 1, Tue Oct  6 02:30:33 UTC 2026

Branch `t/T2240` at 61862e8 (merge-base e2ec919; `main` now 25362ad). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2240-audit1` (detached at 61862e8). Scratch files in `scratchpad/T2240/`.

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2240
 RBM3D/Main/QUECore.lean | 1235 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    3 +-
```
Axioms.lean change: `RBM.Endpoints.qd2Bad]` -> `RBM.Endpoints.qd2Bad,` plus one appended structural line
`RBM.Univ.queWindow]`. No line deleted (no owed line touched). Ticket allows a registry line if the
pre-check flags a name (Targets 6); the prove report (b) says the pre-check flagged `queWindow` (hypothesis
`hwin`). `queWindow` is a condition on the eigenvalue `x` (Pins.lean:380): structural fits §20.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Main.QUECore
✔ [3715/3715] Built RBM3D.Main.QUECore (6.1s)
Build completed successfully (3715 jobs).      # no warning/error lines from QUECore
$ lake build RBM3D
Build completed successfully (4043 jobs).
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Main.QUECore; #assert_rbm_axioms
axiom audit: 6973 theorems, 2358 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; ...
exit=0
$ grep -cE "^\s*(structure|class|axiom)\b|sorry|admit|native_decide" RBM3D/Main/QUECore.lean
0
```
`#print axioms` (from the equality file of section 3):
```
'RBM.Endpoints.thetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.normSq_le_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queMarkov' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queX_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queBad_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.que2Bad_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_thetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_queBad_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Imports (file :6-10): exactly the five of the check file; none added.

## 3. Statements against the pins (compiled)
Verbatim blocks (probe 97d958e, python `block in text`, raw and with namespace substituted):
```
665 772 True True
2439 2446 True True
```
Check-file equality: scratch file = check-file imports + `import RBM3D.Main.QUECore` + the check file body +
the 13 acceptance examples (4 `rfl` vocabulary, `MAThetaDiff_pin = MAThetaDiff := rfl`, 6 target
`example : Y_pin := @RBM.Endpoints.Y`, 2 instance examples) + the 8 `#print axioms` above:
```
$ grep -c '^example' eqcheck.lean
13
$ lake env lean eqcheck.lean | grep -v longLine     # (#check echo lines of section 1 omitted)
exit=0
```
So every target's type is definitionally the dispatcher's pin; the vocabulary bodies are the check file's.

Public declarations of the file (no public name outside the ticket's list; all helpers `private`, `queCore_*`):
```
76 def MAThetaDiff | 105 thetaDiff | 176 queImG | 181 queBlk | 186 queObs | 191 queX
422 normSq_le_trace | 805 queX_core | 966 queBad_sub | 1013 que2Bad_sub | 1087 queMarkov
1112 inst_thetaDiff | 1146 inst_queBad_sub
```
Clash grep on `main` (`git grep -nE "(theorem|def|lemma|abbrev) <name>\b" main -- RBM3D ':!RBM3D/Probe/*'`):
0 hits for each of the 13 names.

Mathematics against `1_2:520-537` (read by the auditor):
- `normSq_le_trace`: `|ψ_k^*Bψ_k'|² ≤ 4η² Re tr(ImG B ImG B)` for `|μ_k−E|,|μ_k'−E| ≤ η`, Hermitian `B`:
  the `(ssfa2)` step (`w_k = η/((μ_k−E)²+η²) ≥ 1/(2η)`); explicit constant 4 for `≲`.
- `queX_core`: hypothesis = the expectation conjuncts of merged `QDiff` (Endpoints.lean:205-208, same
  integrands `avg2 …‖Gn‖²`, `avg2 … Gn Gn`) with error `ε`, plus row variation `K` of `profPM`/`profPP`;
  conclusion integrable, `X_c ≥ 0` pointwise, `E X_c ≤ 4(K+ε)`. With `c = δ_a`, `B_c = E_a − L^{-d}W^{-d}I
  = E_a − N^{-1}` (paper's observable). This is `(ssfa2)`-`(ssfa2_deter)` at one `(sz,n,z)`, no `∀ᶠ`.
- `queBad_sub`/`que2Bad_sub`: `W^{-d}·W^{d−c}/N = W^{-c}/N` and `(W^d|A|)^{-1}·W^{d−c}|A|/N = W^{-c}/N`,
  squared and fed to `normSq_le_trace`: threshold `W^{-2c} ≤ 4N²η²X` is exact. Window hypothesis
  `∀x, queWindow … x → |x−E| ≤ η` is the paper's `η =` window radius (`1_2:523`) as an inclusion.
- `MAThetaDiff`: `‖Θ_ab − Θ_ab'‖ ≤ C g^{-2}` for both `Θ(|m|²)` and `Θ(m²)`, `C = C(d,𝔡,κ)` uniform in
  `L ≥ 3`, `g ≤ 𝔡⁻¹`, `z` in the bulk domain: deterministic, stronger than the paper's `≺ ilambda^{-2}`
  (`1_2:536-537`); proved (`thetaDiff`), so no hidden assumption.
- `queMarkov`: standard Markov with `S ⊆ {s ≤ f}`.
No special-case/adapter substitution: each target is the general pinned statement.

## 4. Hidden hypotheses, vacuity, cycles
- No `structure`/`class` declared; every hypothesis is in the signatures above.
- Dependencies are merged declarations (`prop5to8_holds`, `Theta_apply_add_right`, `norm_SB`,
  `cont_Gres_true_eq_green`, `seqXmat_isHermitian`, …; section 1 `#check`s of the check file compile).
  `queX_core`'s `ε`/`K` hypotheses are not owed pins of this ticket; MA-05b discharges them from `QDiff`
  and `thetaDiff` (consumer route shown compiled in the `queX_core` example, §5). No cycle: the file
  imports only merged modules and no module imports it yet.
- No external hypothesis introduced (no limit check required).

## 5. Compiled nonempty instances (file :1107-1230, all compile in the module build)
| target | instance | data | open hypotheses |
|---|---|---|---|
| `thetaDiff` | `inst_thetaDiff` (verbatim probe) | `d=3, 𝔡=κ=1/10, L=4, g=1/64, z=zI, a=0` | none |
| `queBad_sub` | `inst_queBad_sub` | `sz0, n=0` (`L=4,W=32,lam=1/64,N=2097152`), `ε₀=1/30, c=1/60, E=0, η=1` | none (window via private `queCore_inst_window`, rpow bounds: `32^{-1/30}(1/64)32^{3/2}/2097152 ≤ 1`) |
| `que2Bad_sub` | `example` :1157 | same data, `A = {0}` | none |
| `normSq_le_trace` | `example` :1161 | `Fin 2`, `H = diag(1/2,−1/2)`, `B = σ_x`, `E=0, η=1, k=0, k'=1` | none (eigenbasis, Hermitian, window by tactics) |
| `queMarkov` | `example` :1182 | `Fin 2`, `P = ½ count`, `f i = i`, `s=1`, `T=½`, `S={1}` | none |
| `queX_core` | `example` :1196 | `sz0, n=0, z=zI, c=δ_0`, `K = C·lam⁻²/W³` from `thetaDiff` | `hQ` (expectation half of `QDiff` at `zI`: another gate's pin, allowed) |
None is degenerate (no `N = 0`, empty index, collapsed window or `False` premise; `η = 1` vs window
half-width ≈ 1.2e-6 is a mild, not astronomical, margin).

## 6. Paper deltas
Prove report (d): no `T2240a`; cites D500, D503, D504 (`docs/paper-deltas.md:1459-1463`, present).
Statement differences found: explicit constants `4`, `4(K+ε)` for `≲` and the deterministic `C g^{-2}`
for `≺ ilambda^{-2}` — both strengthenings of inline (unnumbered) steps of the proof outline, proved
here; the ticket scopes `T2240a` to statements at odds with `1_2:524-537` (none found). Covered.

## 7. Observations (no verdict impact)
- O1. `merge-tree main t/T2240` reports a textual conflict in `RBM3D/Test/Axioms.lean` at the closing
  line of `structuralProps` (main 25362ad appended `RBM.BA.BAWinBulk]` there): the hub unions the two
  lines at merge (§20 (3)); after union exactly one `]` must remain.
- O2. The registry line `RBM.Univ.queWindow` was not expected in the ticket header; the ticket
  authorizes it if flagged (Targets 6). Dispatcher may note it; no sign-off required.
- O3. D504 (endpoint explicit forms) is cited for the core's explicit constant `4`; this is a loose
  citation (the constant is in an intermediate lemma), not a statement difference.

## Verdict
| target | statement | vacuity/hidden | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `MAThetaDiff`/`thetaDiff` | = pin (rfl, verbatim) | ok | `inst_thetaDiff` | ok | ok | PASS |
| `queImG`,`queBlk`,`queObs`,`queX` | = check file (rfl) | — | used in instances | ok | — | PASS |
| `normSq_le_trace` | = pin | ok | example :1161 | ok | ok | PASS |
| `queX_core` | = pin | ok | example :1196 | ok | ok | PASS |
| `queBad_sub` | = pin | ok | `inst_queBad_sub` | ok | ok | PASS |
| `que2Bad_sub` | = pin | ok | example :1157 | ok | ok | PASS |
| `queMarkov` | = pin | ok | example :1182 | ok | ok | PASS |

**T2240: PASS.** No dispatcher sign-off needed.
