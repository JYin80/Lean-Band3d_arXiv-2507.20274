Auditor model: claude-opus-5-5
# T2472 1a-audit (design gate G5, BA-L L3d4 `BAProv`) — Mon Oct 12 21:38:53 UTC 2026
Inputs: ticket `docs/tickets/T2472.md`; check `docs/tickets/checks/T2472-check.lean`; prove report `docs/reports/T2472-prove.md` (a), (a″) (157 lines);
branch `t/T2472` cf137d01; audit worktree `RBM3D-wt/T2472-1a-audit` (detached at cf137d01, own `.lake/build` clone). Scratch: scratchpad `T2472/audit1a/`.

## 1. Branch, probe compile, hygiene (script output)
```
$ git diff --stat main...t/T2472            # main = 97341078
 RBM3D/Probe/T2472Pins.lean | 399 +++++++++++++++++++++++++++++++++++++++++++++
$ git diff --stat c986735f main -- RBM3D | tail -1   # main drift since the branch base: new files + Test/Axioms only
 7 files changed, 5648 insertions(+)
$ (date -u; time lake env lean RBM3D/Probe/T2472Pins.lean; echo exit=$?; date -u)   # in the audit worktree
Mon Oct 12 21:34:00 UTC 2026
baEngineProv_imp_localregularX : BAEngineProv → T2472_LocRegXClosed
'RBM.Graph.BAProv_start2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAProv_within_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAProv_locStep_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEngineProv_imp_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEngineProv_imp_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean RBM3D/Probe/T2472Pins.lean  136.84s user 7.60s system 99% cpu 2:25.03 total
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^inductive|^structure" RBM3D/Probe/T2472Pins.lean
45:structure BAProvOut (P : BAPGraph (Fin 2)) where          # the ticket's target 2 (twin of `structure ProvOut`, LWProv:66)
$ grep -cE "sz\.lam|withLam|Sizes|gK" RBM3D/Probe/T2472Pins.lean ; grep -rln "Probe.T2472Pins" RBM3D.lean RBM3D | wc -l
0
0
$ grep -n "open private" RBM3D/Probe/T2472Pins.lean
20:open private BAVocab_merge_adj BAVocab_vmap_surjective from RBM3D.Graph.BAVocab
```
Probe 399 ≤ 400 lines, exit 0, standard axioms, no importer: the ticket's 1a acceptance line holds.
## 2. Binding pins against the probe texts (script diff)
```
$ diff <(check:299-337 without docstrings) <(probe:102-132)
18d17
< packing `baPG`): at the BA data `BAlwData` (real `S`), pointwise in the sample, ...   # a docstring line the filter missed; code identical
$ diff <(probe:358-365, def → example) <(check:345-352)  → engine shape: identical to check:345-352
```
Compiled equivalences (probe:144-148): `T2472_FxyDUniv ↔ ∀…, fxyValD D univ x y = fxyVal D x y`, `T2472_FxyDUnion ↔ … fxyValD (D₁ ∪ D₂) = … + …`,
`T2472_Bridge ↔ BAProv_Bridge` — all `Iff.rfl`; `baEngineProv_imp_localregularX : BAEngineProv → T2472_LocRegXClosed` proved (probe:134).
`baEngineProv_imp_shape : BAEngineProv → T2472_EngineShape` (probe:367) gives the check's non-binding engine shape from the probe text.

## 3. Statements fixed at this 1a-audit (probe texts; 1b diffs against them)
| target | text | probe line | check against ticket / band |
|---|---|---|---|
| 1 | `BAGraph.valW Γ D Wt ℓe := Σ ℓi, (Wt (Sum.elim ℓe ℓi) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)`; `BAPGraph.valW` (packing literal of `BAPGraph.val`, BAVocab:187-192); `valW_one` | 30, 34, 41 | = ticket formula; twin of `valW`/`pvalW`/`valW_one` LWProv:45-58 |
| 2 | `BAProvOut P := {Q, π}`, `ExtOK`, `Molecular` (both conjuncts on `.g.shadow`), `comp`, `Molecular.comp`, `BACoverBy` (over `LGraph.AuxIMol P.g.shadow`), `BACoverBy.comp` | 45-69 | twin of LWProv:66-80, 94-142, molecules on the shadow (§275 (5)); no tags |
| 3 | `BAWExp d P outs`: `∀ L W [NeZero L] [NeZero W], 3 ≤ L → ∀ g0 Em t m, BASelf d L g0 Em m → 0 ≤ t → t < 1 → ∀ Wt ℓe, ∫ P.valW (BAlwData…) Wt ℓe ∂PF d L W 0 = Σ_o ∫ o.Q.valW (BAlwData…) (Wt ∘ (· ∘ o.π)) ℓe`; `.refl` | 71-77 | C1 exactly (same binder as `BAframeStepIdentity` BALvl1A:85-88 and `BALocRegConcl` (d) BAEngine:228-231); every real `Wt` (band WExp:82-92) |
| 6 | `BAProvStepPos d := ∀ P L, BALocStep P L → P.g.Normal → ∃ ps, ps.map (·.Q) = L ∧ (∀ o ∈ ps, ExtOK ∧ Molecular) ∧ BAWExp d P ps` | 79-81 | = ticket target 6 |
| 8 (a) | `BAEngineProv`: `∀ p c, 0<c → ∀ K0 d D, ∃ outs errs : List (BAProvOut (baPG (ofLGraph (fxyPowGraph p))))`, (ExtOK ∧ `BACoverBy (o.π ∘ inr ∘ localReg_fxyBeta)`) ∧ `BALocRegConcl` ∧ `p ≤ n_{W,black}` ∧ `BAWExp d` on `outs ++ errs` | 83-88 | check shape follows (probe:367); `d` is the dimension in both `BALocRegConcl` (BAEngine:223, 228) and `BAWExp` — consistent |
| 9 (a) | `fxyValD D Dm x y` (data level, `(split β).1 ∈ Dm`) | 90-91 | `Iff.rfl` with the pins (§2) |
`.comp`, `.prod`, `baProv_exists` are not G5-b items: their texts are the band twins (`WExp.comp` LWProv:111, `WExp.prod` :119, `lwProv_exists` :1560) with `BAWExp`/`BAProvOut` substituted; the final audit diffs them against those.

## 4. Numerics rerun (scratch copies of the 1a scripts; prov.py seeded)
```
$ python3 prov.py > prov.out    # 2:04.56 total
$ diff <(cut -c1-400 prov.out) <(cut -c1-400 ../prov.out) && echo "prov.out identical to 1a's"
prov.out identical to 1a's
$ head -3 prov.out | cut -c1-200
start terms p=2: 16 | ExtOK (ext ids fixed): True | internal molecules = {alpha_i,beta_i}, covered by beta^(k): True | x~y start terms: 7 of 16
p=1: start terms 4, covered True, x~y 1
p=3: start terms 64, covered True, x~y 37
$ sed -n 4,6p prov.out | cut -c1-230
strategy S' from the 16 start terms, K = ord+2: nodes 10832, output-vs-parent checks 10900, violations 0, truncated False
  steps by kind {'weight': 108, 'gg': 32, 'within': 20} | outputs by x~y {'x!~y': 6894, 'x~y': 4006} | max #M-dots on a node 17 | max M-dots on a shortest ext0-ext1 path 5
every BAFrameStep at all 4 twists of random normal parents: steps by kind {'weight': 52522, 'within': 26534, 'edge': 9751, 'gg': 334, 'ggSplit': 40} | outputs checked 4648438 | violations 0 | terms with an unjoined new vertex 0
$ python3 cut.py | tail -6 ; python3 mdecay.py | sed -n 3,8p ; python3 lines.py | head -4
   (2, 0, 0, 40, 2) -> 1 | K-ord = 38   (2, 1, 1, 60, 2) -> 2 | K-ord = 58   (2, 2, 2, 80, 2) -> 1 | K-ord = 78
   (3, 0, 0, 40, 2) -> 4 | K-ord = 37   (3, 1, 1, 60, 2) -> 4 | K-ord = 57   (4, 0, 0, 40, 2) -> 4 | K-ord = 36
 0.01562   1.00   0.617784    1.0e-15 3.088920e-01   3.2374e+00   1.049235e+03
 0.01562   0.10   0.950589    1.0e-15 4.752943e-01   2.1040e+00   4.434075e+02
 1.00000   1.00   0.354845    1.0e-15 2.914163e-02   3.4315e+01   1.177566e+05
 1.00000   0.10   0.554668    2.2e-16 4.518593e-02   2.2131e+01   4.898024e+04
10.00000   1.00   0.251349    8.9e-16 2.092381e-03   4.7792e+02   2.284117e+07
10.00000   0.10   0.511681    3.3e-16 4.254940e-03   2.3502e+02   5.523489e+06
file A (BAProv): band lines 797, header 40, central 847
file B (BAProvB): band lines 882, header 0, central 1295
central total 2142 | prior (T2387 TW, LWProv 1-1820 x 0.85) 1547 | split line 1950: exceeded | stop line per file 2000 | 2.6 x central (TLC-4) = 5569
```
(cut.py rows joined two per line here; values verbatim.) All numbers of (a)(i)-(iii), (vii), (xii) reproduce.

## 5. Per-labelling census (row (iv)): signatures read on main
```
BAWeightOp:418  private theorem BAWeightOp_core … (ℓe : Ex → Idx d L W) (ℓi : Ix → Idx d L W) : Integrable … ∧ ∫ Γ.term (…) (Sum.elim ℓe ℓi) = ∫ BAWeightOp_R Γ p … ℓe ℓi
BAGGOp:521      private theorem BAGGOp_core … (ℓe) (ℓi) : … ∫ Γ.term (…) (Sum.elim ℓe ℓi) = ∫ BAGGOp_R Γ p q … ℓe ℓi
BAExpandW:638   theorem BAExpandW_term_integral … (ℓe) (ℓi) : ∫ Γ.term (…) (Sum.elim ℓe ℓi) = Σ α β ∫ (lanlwT1 Γ p).term … + …
BASymm1:245     theorem BAGraph.BASymm1_term_twist … (ℓ : E ⊕ I → ι) : (Γ.twist c t).term D ℓ = lwSymmCj c (Γ.term (BASymm1_dataTr D t) ℓ)
BASymm2:104     theorem baTwistIntegral_gen … (F : BALData (Idx d L W) → ℂ) : ∫ lwSymmCj c (F (dataTr …)) = lwSymmCj c (∫ F …)
BAVocab:618     private theorem BAVocab_split_val … (ℓ : V → ι) (es) : Σ over baSplitSolid es … = (es.map (SEdge.val D.toLData ℓ)).prod
BAWeightOp:689-697  baExpFrame_lw, t = 0: `rcases ht0.eq_or_lt with rfl | ht` — both sides vanish pointwise (Ǧ = 0, S = 0)
BALvl1A:334     private theorem BALvl1A_macroA_graph … (ℓ' : E → Idx d L W) : ∫ Γ.val … ℓ' = …   # ext-level; composition of lanlw + lw per labelling → weighted twin (priced, 1.1 ×)
```
Every step identity has a per-labelling core or is a composition of such cores; none exists only after the sum over the old labels.

## 6. H250 (4) fill-in table (ticket rows (i)-(xiv))
| # | filled at | audit check |
|---|---|---|
| (i) | (a) G5-a ¶1-¶6 | root reading of `7_8:1631-1650` checked against the TeX (`D_{>ℓ}`, `D_{≤ℓ}` on internal aux vertices); roots = images of `β^{(k)}`, `[root] ∈ Dm` exact, matches `BAAtom_solid_prod_conf` `root`/`hroot` (BAAtom:535-536) — met |
| (ii) | (a) row (ii) | joining table per constructor; machine-checked by prov.py (0 unjoined, 4,648,438 outputs) and probe (238 outputs, `BAProv_chk`; negative control l.388) — met |
| (iii) | (a) row (iii) | rerun identical, 0 violations — met |
| (iv) | (a) row (iv) | §5 — met |
| (v) | (a) row (v); probe `BAProv_start2` l.184 | 16 terms, `ExtOK`, `BACoverBy`; control l.195 (β₀ alone fails) — met |
| (vi) | (a″) row (vi) | §2-§3 — met |
| (vii) | (a) row (vii) | M-decay branch; numbers at g = 1/64, 1, 10 reproduce (§4); not a stop (§275 (6)) — met |
| (viii) | (a) row (viii) | §7 below — met (observation O1) |
| (ix) | (a) row (ix) | probe 0 hits — met, UBA-C1 not triggered |
| (x) | (a) row (x) | C1 = `BASelf`, `0 ≤ t < 1`, `3 ≤ L`; `Normal` for step/recursion — met |
| (xi) | (a) row (xi) + (a″) P4 | registry none; `open private` list complete with P4 — met |
| (xii) | (a) row (xii) | §4 — met |
| (xiii) | (a) row (xiii) | §8 — met |
| (xiv) | (a) row (xiv) | rerun below — met |
```
$ git grep -c -E "$PAT" main -- RBM3D RBM3D.lean | wc -l ; (75 branches t/T24* except t/T2472) | wc -l    # PAT as in (a) row (xiv); main 97341078
0
0
```

## 7. Interface table of 1a (viii) (basis of the L3d2b ticket, §274 (6))
| band consumer (line) | what it reads | BA name read by L3d2b | owner |
|---|---|---|---|
| `LWMomentExp:32-74` `LWf_split`, `dom_*` | `LWfD`, `LWfD_union` | `fxyValD`, `fxyValD_union` (9 a, b); carrier `LWfgD` | 9: L3d4a; `LWfgD`: L3d2b (needs T2470 `LWfg`) |
| `:256-287` `lwMomentExp_(p)valW_smul`, `_pvalW_evX` | homogeneity of `pvalW` | own weighted lemma (twin of private `BAExp14d_term_scale` BAExp14d:93; `val_scale` :111 needs `BAReal`); `_evX` has no BA twin (no tags) | L3d2b |
| `:289-367` `lwMomentExp_valW_norm_le` … | `valW` | `BAGraph.valW` (1) | L3d2b |
| `:379-382` `lwMomentExp_wt`, `_wt_abs` | `ProvOutX.π` | own def over `BAProvOut.π` (2) | L3d2b |
| `:390-460` `lwMomentExp_expand` | `WExp.prod` :404, `lwProv_bridge` :412 | `BAWExp.prod` (3), `baProv_bridge` (9 c), `baStart_nWS` (merged BAEngine:208) | L3d4a (1, 3, 9) |
| `:1000-1016` `lwMomentExp_rep` | `Cover` | the `BACoverBy` conjunct of `BAEngineProv` → `rep` (probe `BACoverBy.rep` l.346) | L3d4a (2), L3d4b (8) |
| `:1164` `lwGtoAGRooted_holds` call | rooted G3, `rep`, `wt` | BA rooted G3 (twin of `AuxGraphRooted 1-569`, from `BAAtom_solid_prod_conf`, `BAGtoAGT` BAExp14d:269) | L3d2b (§275 (2)) |
| `:1302-1345` `lwMomentExp_pin_gen` (engine :1325) | `lw_localregularXP` | `ba_localregularXP : BAEngineProv` (8 a): lists, `BALocRegConcl` (a)(b)(c)(d), `p ≤ n_{W,black}`, `BAWExp` | L3d4b |
| `AuxGraphRooted:225-243, 362` | `valW` only | `BAGraph.valW` (1) | L3d4a |
| `LWTermHolds:1524` (L5) | `lwMomentExp_holds` only | nothing from `BAProv*` | — |
Not in this row: the `x ~ y` outputs (4,006 of 10,900 in the model) stay in the lists (`2p ≤ ord`); L3d2b owns the M-chain bound (`BAMfine_decay` GreenSchur:124 needs `BAReal`, `0 < g ≤ Λ`).

## 8. Pre-signed decisions
- **Split L3d4a (`BAProv`) / L3d4b (`BAProvB`): confirmed.** Central 2,142 > 1,950. Rows: 847 and 1,295, each ≤ 1,950 and < 2,000 → **no third row** (no REQ). The cut is the ticket's (band §1-§4 | §5-§9). The 1a's alternative cut (1,467 / 675) is not pre-signed and is not adopted.
  Condition (CLAUDE.md §4 step 2): L3d4a is audited alone, so `BAProv.lean` must carry its own compiled instances (target 9 (c) at `Dm = univ` and `{0}`, `BACoverBy` at the 16 start terms, `BAWExp.prod` at the flow point); lines.py puts all instances (120) in B. Moving ≈ 60 lines gives A ≈ 907: decision unchanged.
- **Switch to `prover-max`: not triggered.** (a) no new shadow molecule, no dropped joining edge (§4: 0 violations, 0 unjoined; probe 238 outputs); (b) every identity has a per-labelling form (§5). Role stays `prover-hard`.
- No dispatcher sign-off requested.

## 9. Stop lines (ticket :34-39)
file > 2,000: no (847 / 1,295). G5 fails: no. Comparison text / `Sizes` read / new `inductive` / merged-file edit / `private` deletion: none (`open private` only). Public result with an unproved `Prop` premise: none in the texts (`BAProv_locStep_exists`'s `H` is a probe helper; the binder is discharged per 8 (a)). T2470/L3d2b content needed: no.

## 10. Observations (no RETURN)
- O1 (viii) cites no line for `LWMomentExp:1164` and `:289-367`; both read only `valW` / the rooted G3, rows added in §7.
- O2 The strategy run stops at `K = ord + 2` (engine `K` 40-80, cut.py). The molecular property is per step; the random-parent table covers all five kinds (ggSplit: 40 steps, 1,008 outputs).
- O3 TLC-4 upper reference per file 2,202 / 3,367 (> 2,000): not a 1a stop (central decides), but L3d4b has 705 lines headroom at central.
- O4 (vii) for L3d2b: the M-decay threshold is only asymptotic (`ln W0` = 4.4e2 / 4.9e4 / 5.5e6 at g = 1/64, 1, 10, η = 0.1). The L3d2b ticket must state it as an eventual (`∀ᶠ W`) bound with `BAReal` and give a limit check.
- O5 No `T2472a…` paper-delta candidates yet. Due in the 1b reports (shadow molecules; the weight on the start graph for "internal vertices in `D`"; statements at `BAlwData`).

## Verdict
T2472 stage 1a (design gate G5 + probe): **PASS.** Every row of the fill-in table is met, the probe compiles (exit 0, standard axioms, 399 lines), the numerics reproduce, and no binding stop line is hit.
Split L3d4a / L3d4b confirmed with the instance condition of §8. No `prover-max` switch. No sign-off needed.
