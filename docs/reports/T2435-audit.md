Auditor model: claude-opus-5-5

# T2435 audit (round 1): BA-L L3c3a `Graph/BAAuxGraph2`, `Graph/BAAuxGraph2B`

Time: Mon Oct 12 06:32:15 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2435-audit1`, detached at `e1cdda3` (`t/T2435`).
Scratch (CONTROL H28): `<scratchpad>/T2435/{build.out,ax.lean,sdiff.py}`. `sdiff.py A nameA B nameB subst…` extracts a declaration's
statement (up to the blank line / `:= by`), applies the listed text substitutions band→BA to A, and prints a token diff.

**Overall: PASS (all targets). No dispatcher sign-off needed.**

## 1. Diff, build, axioms, forbidden tokens

```
$ git diff --name-status main...t/T2435
A	RBM3D/Graph/BAAuxGraph2.lean
A	RBM3D/Graph/BAAuxGraph2B.lean
A	RBM3D/Probe/T2435Pins.lean            # probe, sole writable, never merged
$ git diff main...t/T2435 -- RBM3D/Graph/BAAtom2.lean RBM3D/Graph/AuxGraph2.lean RBM3D/Chain RBM3D/BA | wc -l
       0
$ git diff --name-status $(git merge-base main t/T2435) main -- RBM3D RBM3D.lean lakefile.toml lake-manifest.json
M RBM3D.lean / A BA/TwistGridWTail.lean / A BA/TwistGridWTail2.lean / A Graph/BALvl1A.lean / M Test/Axioms.lean   (no imported module modified)
$ lake build RBM3D.Graph.BAAuxGraph2 RBM3D.Graph.BAAuxGraph2B   (audit worktree)
✔ [4001/4002] Built RBM3D.Graph.BAAuxGraph2 (6.5s)
✔ [4002/4002] Built RBM3D.Graph.BAAuxGraph2B (10s)
Build completed successfully (4002 jobs).        # error lines: none; warning lines in the two new files: none
$ grep -n -E "\bsorry\b|\badmit\b|^axiom|native_decide" RBM3D/Graph/BAAuxGraph2.lean RBM3D/Graph/BAAuxGraph2B.lean; echo $?
1
$ lake env lean ax.lean
'RBM.Graph.baZetaVar_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baZetaVar_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baZeta_ward_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baZetaSq_ge_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWXigL_bandFM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baZetaClaim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baGbyZeta_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baGbyZeta_hxi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEntryPsi_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAAnpAuxG' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2435-check.lean >/dev/null; echo "check file exit $?"   (on the branch)
check file exit 0
$ wc -l BAAuxGraph2.lean BAAuxGraph2B.lean       # stop line 2,000 per file
    1113 / 1064
$ git grep -w -c <17 new public names> main -- RBM3D | wc -l   (each name)
0 for every name;  grep "^(theorem|def|abbrev) BAXi" in both files: exit 1 (no BAXi* name)
```

## 2. Statements against the pin / the band twin (script diffs)

```
== LWXigL vs check file T2435_LWXigL        (target 2)
token diffs: 0
== baZetaSq vs lwXiSq  (Lloop sz n (E n) → (baFMz sz z).L n; E → z, D₁)     (target 1, ζ)
insert: band[] -> BA[+ ( ( sz.W n : ℕ ) : ℝ ) ^ ( -D₁ )]
== baZeta_ward_sum vs lwXi_ward_sum         (target 1, Ward)
insert {κ ε 𝔠 𝔡}; |E n|<2 → 0<κ; t n<1 → hflow : BAFlow sz κ ε 𝔠 𝔡 z, 0 ≤ t n, t n ≤ BAflowT0 sz z n;
insert: RHS + ( ( sz.L n : ℕ ) : ℝ ) ^ d * ( ( sz.W n : ℕ ) : ℝ ) ^ ( -D₁ )
== BAZetaClaim vs LWXiClaim  (STFlow→BAFlow, lemT→BAflowT0, LWLoop2→LWLoop2gL (baFMz) (seqP (sz.withLam 0)),
                              Prec→PrecL (seqP (sz.withLam 0)), STGM→(baFMz sz z).GM, LWXi→LWXigL, lwXiVar→baZetaVar)   (target 3)
insert: band[] -> BA[∀ D₁ : ℝ, max ( ( d : ℝ ) + 2 * C₂ / ( 𝔠 * d ) + 1 ) ( 1 / 𝔠 ) ≤ D₁ →]
token diffs: 1
== BAGbyZeta vs LWGbyXi  (same substitutions)   (target 4)
replace: band[2 * R n + 1 ≤ ρ n] -> BA[∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ( ( sz.W n : ℕ ) : ℝ ) ≤ ρ n - 2 * R n]
replace: band[U := {q // q.1.1 ≠ q.1.2 ∧ R-balls}] -> BA[U := BAGbyZetaU sz R]   (BAGbyZetaU = the R-balls, no x ≠ y)
replace: band[‖Gt sz n (STflowE z n) (t n) true ω …‖] -> BA[‖(baFMz sz z).GM n (t n) ω …‖]
(+ `(D₁ : ℝ)` in the binder; token diffs: 10, all listed above)
== BAEntryPsi vs LWEntryPsi  (same substitutions)   (target 5)
token diffs: 0
== BAAnpAuxG vs BAAnpAux (BAAtom2:677) (STFlow→BAFlow, lemT→BAflowT0, Prec→PrecL μ, LWXi→LWXigL (baFMz), etaT→(baFMz).eta)  (target 6)
token diffs: 0
```

- **`baGbyZeta_hxi` vs G3's `hξ0`/`hξ`** (`BAAtom2.lean:403-406`, the same text in `baGtoAG_E` `:616-618`): its conclusion is
  `(∀ a b, 0 ≤ ξ a b) ∧ (∀ x y a b, zdistD([x]−a) ≤ R n → zdistD([y]−b) ≤ R n → ‖D.G x y − D.M x y‖ ≤ ξ a b)` at
  `ξ = c·baZetaVar …`, `L = sz.L n`, `W = sz.W n`; the example `BAAuxGraph2B.lean:1019` passes `.1`, `.2` to `baGtoAG_holds` and compiles
  (no cast): verbatim. All pairs `x, y` (diagonal included) and `G − M` (not `G`): the ticket's (i)(a) / G3's `hξ`.
- **Carrier/law:** every BA statement uses `baFMz sz z`, `Sizes.seqP (sz.withLam 0)` (the `μ0` of `LWPinsBA.lean`), `BAFlow`,
  `0 ≤ t n ≤ BAflowT0 sz z n`; parameter order `κ ε 𝔡` → `𝔠 sz z` → `t` → class → `ε₁` → windows, as in the band pins.
- **Verdicts per target:**

| # | target | statement | verdict |
|---|---|---|---|
| 1 | `baZetaSq`/`baZetaVar`, `baZetaVar_nonneg`, `_symm`, `baZeta_ward_sum` | band twin + floor `W^{-D₁}`; Ward with BA flow hypotheses, extra floor term `L^d W^{-D₁}` | PASS |
| 2 | `LWXigL`, `LWXigL_bandFM` | = `T2435_LWXigL` (0 diffs); bridge `↔ LWXi` at `bandFM`, `seqP sz` | PASS |
| 3 | `BAZetaClaim`/`baZetaClaim_holds` | twin of `LWXiClaim` + lower bound on `D₁` (a "large D" condition; T2435b) | PASS |
| 4 | `BAGbyZeta`/`baGbyZeta_holds`, `baGbyZeta_hxi` | stronger in conclusion (all pairs, `G − M`); separation `ρ − 2R ≥ K log W ∀K` eventually replaces `2R+1 ≤ ρ` (T2435c); no `LWPsiAll`/`LWLoop2gL`/unprimed `BAGbEXPij` | PASS |
| 5 | `BAEntryPsi`/`baEntryPsi_holds` | twin of `LWEntryPsi` (0 diffs) | PASS |
| 6 | `BAAnpAuxG` (pin, owner L3d1) | = `BAAnpAux` on the BA carrier (0 diffs); not proved, as the ticket allows | PASS (pin) |
| 7 | instances | §4 below | PASS |
| 8 | registry | none; `Test/Axioms.lean` untouched | PASS |

## 3. Hidden hypotheses, vacuity, cycles

- No structure carries a hypothesis: the only new type is `abbrev BAGbyZetaU` (a subtype by the two `R`-ball inequalities); the
  diagonal `(x, x)` is in it (example `B:979`, conjunct 2, `⟨((x,x),([x],[x])), …⟩` with `R ≥ 0`).
- `BAAnpAuxG` is a `def … : Prop` and is used only as a hypothesis `h6` of the example `B:979`; nothing proved here depends on it.
- No cycle: imports of the new files are merged modules (`Chain.Carrier`, `Graph.LWPins`, `BA.FlowPins`, `BA.GreenLDE`, `BA.Ward`,
  `Induction.*`, `Graph.AuxGraph2`, `Graph.BAAtom2`, `BA.LWPinsBA`, `BA.GreenOff`, `BA.GreenLocal`, `BA.Step1Boot`, `BA.Prop5Short`);
  B imports A. Axioms above are the standard three.
- External hypotheses kept: `LWLoop2gL` (stage-L pin) and `‖G − M‖ ≺ W^{-ε₁}` (entry law), both "other gates' pins" per the ticket
  (target 7). Their limit check is in the prove report (a)(ii) (`inst.py`: Ward ceiling vs `Φ0²` ratio 205 / 5.3e12 / 2.1e25 at
  n = 0/10/199; `W^{-1/20}` vs floor `W^{-3/2}`).
- `D₁` and the separation hypothesis are jointly satisfiable with `ρ + 1 ≤ N^τ ∀τ` at one `(ρ, R, D₁)`: `ρ = 2R + (log W)^{3/2}`,
  `R = (log W)^{21/20}`, `D₁ = 12 = max(12, 6)` — discharged in Lean (`BAAuxGraph2B_ρ0_rad`, `BAAuxGraph2B_sep`, `by norm_num`).

## 4. Compiled nonempty instances (all compile: build above)

Data: `d = 3`, `sz0` (n = 0: `L = 4`, `W = 32`), `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0`
(`half_lt_t0`), `Φ0 ≡ W^{-1/2}` with `LWPsiAll sz0 (1/10) 2 2 1 (fun _ => 1) Φ0` proved (`BAAuxGraph2B_psiAll`), `ε₁ = 1/20`, `D₁ = 12`.

| line | applies | deterministic hypotheses discharged | left as hypotheses |
|---|---|---|---|
| A:1073 | `baZetaSq_ge_W`: `W^{-3}+W^{-12} ≤ ζ²(a,a)`, `ζ(a,a) > 0` | `ρ0 = log W ≥ 0` | — |
| A:1086 | `baZetaVar_nonneg`, `baZetaVar_symm` | all | — |
| A:1093 | `baZeta_ward_sum` | `0<κ`, `flow_sz0`, `0 ≤ 1/2 ≤ T0`, `ρ0 ≥ 0`, `hA` with `A = Σ‖GM‖` | — |
| A:1104 | `LWXigL_bandFM` at `bandFM sz0 0`, `Φ = W^{-1/2}`, `ξ ≡ 1` | all | — |
| B:965 | `baZetaClaim_holds 3` | flow, `t`, `LWPsiAll`, `ρ0 ≥ 0`, `ρ0 + 1 ≤ N^τ`, `D₁ = 12` | `LWLoop2gL`, entry law |
| B:979 | `baGbyZeta_holds 3`, `baEntryPsi_holds 3`, `BAAnpAuxG 3` fed with ζ from target 3 | flow, `t`, `R0 ≥ 0`, separation, `p = 2`, `baPQ`, `nM ≤ 2`, `LocReg345`, mol ≠ (by `decide`) | `LWLoop2gL`, entry law, `h6 : BAAnpAuxG 3` (L3d1 pin) |
| B:1019 / B:1046 | `baGbyZeta_hxi` into `baGtoAG_holds`; data `D` with `D.G = C.G`, `D.M = C.M` exists | `hcξ`, `R = R0 0` | the sample event `h` and G3's own premises (see O3) |

No `N = 0`, no empty index, no collapsed window (`ζ(a,a) > 0` proved at n = 0), no `False` premise; `D₁ = 12`, `ρ`, `R` polylog.

## 5. Paper deltas (prove report (d)); coverage of every Lean/paper difference

| difference (Lean vs `B:424-431`) | candidate |
|---|---|
| ζ is the block loop-window variable of `(eq:xia1a2)` on `baFMz`, not the atom-centre entry sum `(Gyiyjatom)` | T2435a |
| floor `W^{-D}` is an explicit `D₁ ≥ max(d + 2C₂/(𝔠d) + 1, 1/𝔠)` in `BAZetaClaim` | T2435b |
| `‖G−M‖ ≺ ζ` proved sample-wise from `GreenOff_carrier_decay`, not from `(GijGEX_BA)`; separation `ρ − 2R ≥ K log W ∀K` | T2435c |
| Ward sum in block form `Σ_{a₂} ζ² ≺ (W^d η)⁻¹` (paper: fine-lattice `≺ η⁻¹`) | T2435d |
| two-charge sum, radius `ρ` a parameter, balls by `zdistInf` (inherited from the band twin) | already D464, D465 (T2185a/b) |

All statement differences found in §2 are covered.

## 6. Observations (no statement, instance, build, axiom or delta effect)

- O1. The prove report has 290 lines; the ticket's report limit is 250 (CLAUDE.md §6's 300 holds). The report says so in (d).
- O2. `baZetaSq_ge_W` (`BAAuxGraph2.lean:192`) is public, unpinned and not prefixed with the file stem (CLAUDE.md §3 (E)); no clash on
  `main` (grep 0). The dispatcher may ask for a rename or `private` in a later touch; it does not change any pinned statement.
- O3. The `baGbyZeta_hxi` instance keeps the sample hypothesis `h` (as the merged band instance `AuxGraph2.lean:1450` keeps it for
  `lwGbyXi_hxi`); `h` is satisfiable at every `ω` because `ζ ≥ W^{-6} > 0` (floor) — e.g. `cξ = W^6 Σ‖G−M‖`. Not degenerate.
- O4. Design-gate item (ii) (both terms of `GreenCore_decayRHS`, classes `(eq:Psi)` and `𝖳`) is a written argument with script checks
  (prove report (a), E7–E9); it is not on the proved path (no `BAGbEXPij'`, no `BAGbEXPij` used), so it bears on no Lean statement here.
- O5. The `baGtoAG_E` match is by text (`diff -w BAAtom2:405-406 vs :617-618`, exit 0, prove report (a″)) plus the existence
  example `B:1046`; `baGtoAG_holds` itself is applied at `B:1019`.

## Verdict

T2435: **PASS** (targets 1–8). Build of both modules passes in the audit worktree; axioms standard; diff only in sole writable files
(the probe `RBM3D/Probe/T2435Pins.lean` is not to be merged); root imports `RBM3D.Graph.BAAuxGraph2`, `RBM3D.Graph.BAAuxGraph2B`
to be added by the hub after the last `import` line.
