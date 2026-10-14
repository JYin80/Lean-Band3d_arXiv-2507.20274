Verdict: PASS, no stop rule fired. (a) D1: `T2503_BAMainIndFamTL` is pinned unchanged (probe :33-47 equals the check's Part 2 text by `Iff.rfl`, section 0). (b) D2: K2 (`T2503_k2Member`), the family Step-1 call (`T2503_famStep1Call`) and the wrapper `S1 → Fam` (`T2503_famOfS1`) are compiled from merged names; D2 (c) yes, 16 lines. (c) D3: PASS with the (κ', ε') reading: a member of `Fam(t)` is a `BAFlow` only at `(κ', ε') = (c_κ(κ) κ, ε/2)` after a finite modification below `n₀` (not at `(κ, ε)`), with horizon `≥ t` at every `n`; the per-member base and the TL2 congruence are compiled; class `t_n = 0`: mix at the main flow only. (d) D4: the whole family twin of `baChainTL_holds` compiles (`T2503_baChainFamTL` with tail passage and shift transport, 110 probe lines; the single-flow chain section it twins, `TwistChain:144-264`, has 121); rows V2a 1 (273 / 440 / 950 lines), V2b 1 (540 / 700 / 1,100), V3 1 (240 / 395 / 766); V forecast ≈ 12 (11-14) unchanged, below 15, no REQ.

# T2503 design: the family step of the BA main induction (V2a design gate; V-C1 steps 1-4)
Written Wed Oct 14 05:13:39 UTC 2026 (`date -u`) by the stage-1b prover (claude-sonnet-5-5) on branch `t/T2503` (base `main` 6b359e50). Probe `RBM3D/Probe/T2503Pins.lean`, 391 lines (cap 400), never merged. Section (a) of `docs/reports/T2503-prove.md` (preflight PASS) is not edited; one correction is in its (a′). `X:N` = `RBM3D/X.lean:N` at the checkout; `:N` alone = a probe line; `T2205:N` = `t/T2205:RBM3D/Probe/T2205Pins.lean:N` (commit 96e4087c). Scripts (scratchpad `T2503/`) and their verbatim outputs are in section 0; every `file:line` citation of a merged file below was checked by `cite_lines.py` (summary in section 0; the script prints the cited line of each citation).

## 0. Script output
```
$ zsh probe_check.sh                                                     # cwd = /Users/junyin/Lean_proof/RBM3D-wt/T2503
lines:           391
lake env lean RBM3D/Probe/T2503Pins.lean: exit=0, output lines=       0
lake build RBM3D.Probe.T2503Pins: exit=0, last line: Build completed successfully (4230 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs: 18, theorems: 15, examples: 16
T2503_tl2Congr [propext, Classical.choice, Quot.sound]
T2503_k2Member [propext, Classical.choice, Quot.sound]
T2503_famStep1Call [propext, Classical.choice, Quot.sound]
T2503_memberFlow [propext, Classical.choice, Quot.sound]
T2503_famOfS1 [propext, Classical.choice, Quot.sound]
T2503_memberBase [propext, Classical.choice, Quot.sound]
T2503_tailPassage [propext, Classical.choice, Quot.sound]
T2503_precL_shift [propext, Classical.choice, Quot.sound]
T2503_conclShift [propext, Classical.choice, Quot.sound]
T2503_baChainFamTL [propext, Classical.choice, Quot.sound]
$ python3 -I mk_iffrfl.py; lake env lean iffrfl.lean     # the check's Part 2 text, then `example (d) (R) : T2503_X d R ↔ RBM.BA.T2503_X d R := Iff.rfl`
iffrfl exit=0 lines=0     # 9 examples: BAMainIndFamTL, BAMainIndS1TL, FamOfS1, BAChainFamTL, FamStep1Call, K2Member, MemberFlow, TL2Congr, RegShape
S1 (probe :48-58) against BAMainIndTL (BA/TwistPins.lean:169-175), token diff:
  insert old: - | new: STStep1LoopgL C μ s t → STStep1WeakgL C μ s t →
D1 pin (probe :33-47) minus its 2 `BATwistLoopLaw` conjuncts and the premise `R sz s t` against T2205's BAMainInd (T2205:1715-1735), `let`s expanded: token diff has 2 hunks
  delete old: ( | new: -
  delete old: ) | new: -
  all hunks are single parentheses (the parentheses around the five-conjunct hypothesis of T2205): True
$ grep -rn 'T2503\|BAMainIndFamTL\|BAMainIndS1TL\|BAChainFamTL\|BATwistLoopLaw_congr' RBM3D/ | grep -v Probe/T2503Pins.lean
RBM3D/BA/TwistPins.lean:168 and :184   # the two doc comments edited under answer (4); no declaration; git grep over t/T2[45]*: `T2503_` only in t/T2503
$ python3 -I recheck_v1.py        # `T2503v1_*` against docs/tickets/checks/T2502-check.lean (commit 6b359e50, sha1 84baca8d1cc7)
T2502_Exp2UgL: check line 182 ; T2503v1_Exp2UgL: probe line 264 ; identical after prefix map: True
T2502_Step2CoregL: check line 189 ; T2503v1_Step2CoregL: probe line 269 ; identical after prefix map: True
T2502_IngR6gL: check line 194 ; T2503v1_IngR6gL: probe line 271 ; identical after prefix map: True
T2502_Step6RgL: check line 210 ; T2503v1_Step6RgL: probe line 284 ; identical after prefix map: True
$ python3 -I comment_check.py RBM3D/BA/TwistPins.lean RBM3D/BA/LWPinsBA.lean RBM3D/BA/Step2CloseBA.lean RBM3D/Graph/BAGGExp.lean
BA/TwistPins.lean: replace old[168-168] new[168-168] old-lines-all-comment=True new-lines-all-comment=True
BA/TwistPins.lean: replace old[184-184] new[184-184] old-lines-all-comment=True new-lines-all-comment=True
BA/LWPinsBA.lean: replace old[20-20] new[20-20] old-lines-all-comment=True new-lines-all-comment=True
BA/LWPinsBA.lean: replace old[44-44] new[44-44] old-lines-all-comment=True new-lines-all-comment=True
BA/LWPinsBA.lean: replace old[46-46] new[46-46] old-lines-all-comment=True new-lines-all-comment=True
BA/LWPinsBA.lean: replace old[48-48] new[48-48] old-lines-all-comment=True new-lines-all-comment=True
BA/Step2CloseBA.lean: replace old[201-201] new[201-201] old-lines-all-comment=True new-lines-all-comment=True
Graph/BAGGExp.lean: replace old[78-78] new[78-78] old-lines-all-comment=True new-lines-all-comment=True
files: 4 hunks outside comments: 0
$ python3 -I cite_lines.py design.md     # every `file:line` citation of a merged file in this report
citations checked: 58, problems: 0   # (script output on this report; scratchpad cite_lines.out prints the cited line of each)
$ lake build     # worktree, full library, after the comment edits, 04:53:35-05:00:51 UTC (log: scratchpad lakebuild_full.log)
Build completed successfully (4382 jobs).  exit=0   # 95 modules rebuilt (the four edited files and their cones), `Graph/LWExpCert*` rebuilt: 0, error lines: 0
$ git diff --stat main...t/T2503
 RBM3D/BA/LWPinsBA.lean       |   8 +-
 RBM3D/BA/Step2CloseBA.lean   |   2 +-
 RBM3D/BA/TwistPins.lean      |   4 +-
 RBM3D/Graph/BAGGExp.lean     |   2 +-
 RBM3D/Probe/T2503Pins.lean   | 391 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2503-design.md | 179 ++++++++++++++++++++
 6 files changed, 578 insertions(+), 8 deletions(-)
$ wc -l docs/reports/T2503-design.md RBM3D/Probe/T2503Pins.lean
     179 docs/reports/T2503-design.md
     391 RBM3D/Probe/T2503Pins.lean
     570 total
```

## D1 = V-C1 step 1 (the family step)
**D1 (a), binding text: pinned, unchanged.** Probe :33-47 (extracted by script):
```
def T2503_BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
        (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t →
        (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
          let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0)
          STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧
            STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
          let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0)
          STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧
            STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t
```
Change table (old, new, why): none; all nine pins of the check, `T2503_RegShape` included, are the probe's text up to `Iff.rfl` (section 0). The private `T2503_Step5BA` (:300) only abbreviates the Step-5 reading of the four exact-type examples (:305-308). Binder order is that of T2205's `BAMainInd` (T2205:1715) with `BATwistLoopLaw` as the sixth hypothesis conjunct and the seventh conclusion conjunct.
**D1 (b), proposed: single flow plus wrapper, accepted.** `T2503_BAMainIndS1TL` (:48-58) is `BAMainIndTL` (`BA/TwistPins.lean:169`) with `STStep1LoopgL`, `STStep1WeakgL` on `[s,t]` as the last two hypotheses. `T2503_famOfS1 : S1 → Fam` (:124-139, 16 lines, generic in `R`) needs nothing beyond D2/D3: `T2503_memberFlow` (D3 a), `T2503_famStep1Call` (D2 b), `T2503_tl2Congr` (D3 b) and the nine merged congruences `STLKgL`, `STDecaygL`, `STDecayStronggL`, `STLocalMaxgL`, `STExp2gL`, `STStep1LoopgL`, `STStep1WeakgL`, `STLmaxgL`, `STLocalEntrygL` `_congr` (`BA/Step1Fam:205-260`). The four regime proofs stay single flow and band-shaped; the family enters once. The regime glue (V2b) must stay in family form: the second stage of `BA_mainInd_compose` (T2205:2462) needs the hypotheses at the cut time for every member of `Fam(m)`, which are the first stage's conclusions.
**D1 (c), comment texts (taken, answer (4); script check and full `lake build` in section 0):** `BA/TwistPins.lean:168`, doc comment of `BAMainIndTL`, appended: "Not on the route; superseded by the family form `BAMainIndFamTL` (V2a; design T2503; supervisor 2026-10-14-0342 V-F1); do not read." `:184`, doc comment of `BAChainTL`, appended: "Reads the single-flow step `BAMainIndTL`; the route's chain is the family twin (V3; design T2503)." LC-1: `BA/LWPinsBA.lean:20` (readings `BALWterm`, `BALWtermExp` now "proved: `baLWterm_holds`, `baLWtermExp_holds`" with file:line; `BALWtermEXP` "superseded by `BALWtermEXPTw` (T2490/T2494); no producer; do not read"), `:44` (proved: `baLWterm_holds`, `Graph/BATermHolds.lean:706`), `:46` (proved: `baLWtermExp_holds`, `Graph/BATermHoldsB.lean:865`), `:48` (superseded by `BALWtermEXPTw`, no producer, do not read); `BA/Step2CloseBA.lean:201` ("(BA-L6)" now "proved: `baLWterm_holds`, `baLWtermExp_holds`; kept as hypotheses here"); `Graph/BAGGExp.lean:78` ("owed: BA-L2c" now "proved: `baGGGamma_holds`, `Graph/BAGGExp.lean:358`"). Line counts unchanged, so every cited line number of these four files is unchanged.

## D2 = V-C1 step 2 (the family hypothesis suffices; probe from merged names)
Statements (first lines extracted by script from the probe; the pins are the check's):
```
:95  theorem T2503_tl2Congr : T2503_TL2Congr
:103  theorem T2503_k2Member (d : ℕ) : T2503_K2Member d
:110  theorem T2503_famStep1Call (d : ℕ) : T2503_FamStep1Call d
:115  theorem T2503_memberFlow (d : ℕ) : T2503_MemberFlow d
:124  theorem T2503_famOfS1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : T2503_FamOfS1 d R
:142  theorem T2503_memberBase (d : ℕ) (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
:155  theorem T2503_tailPassage (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
:177  theorem T2503_conclShift {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (n₀ : ℕ) :
:235  theorem T2503_baChainFamTL (d : ℕ) : T2503_BAChainFamTL d
```
- **D2 (a) `T2503_k2Member`** (:103-109): `BAFamZ_mono` (`BA/Step1Boot:173`) to `Fam(0)`, `BAFlowMember_holds` (`Step1Fam:624`), `baKbound_holds` (`BA/KBound:245`) at the modified flow, `baFMz_eqAt` (`:273`) with `STKboundgL_congr` (`:247`). 7 lines.
- **D2 (b) `T2503_famStep1Call`** (:110-114): `baStep1_holds' d _` (`Step1Prime:892`, needs `2 ≤ d`, given by `omega` from `3 ≤ d`) applied at exact type to `fun z' hz' => ⟨K2, (H z' hz').1, (H z' hz').2.2.2.1⟩`; `BAStep1` is not restated. 5 lines. Of the six family conjuncts of a member only `STLKgL` and `STLocalMaxgL` are read here (the third premise of `BAStep1`, `STKboundgL`, is K2); the other four are read at `z''` in the wrapper.
- **D2 (c) yes: `T2503_famOfS1`** (:124-139, 16 lines, cap 180): per member `z' ∈ Fam(t) ⊆ Fam(s)` the modified flow `z''` at `(κ', ε')` (D3 a), the six hypotheses and the Step-1 pair carried to `z''` by the congruences, `S1` at `z''` with `𝔠d` of `S1` at `(κ', ε', 𝔡)` (so `BAStep1`'s `∀ 𝔠d` absorbs it), the seven conclusions carried back. V2a's 1b ports it.
- **Compiled `d = 3` instances** (probe :310-391; each target theorem applied with every deterministic hypothesis discharged): D2 (a) :326, D2 (b) :330 and :338 (`c₁` of `BAWinBulk_of_dom_holds`, as `Step1Fam:975-977`), D2 (c) :356, D3 (a) :347, D3 (b) :353, D3 (c) :364, D4 (b) :370, D4 (a) :379 (`t ≡ 1/2` and `t ≡ 0`). Data: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_0 = 2^21`), `zSeq`, `flow_sz0` weakened to `κ = 1/4` (`BAdom` is monotone in `κ`), `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3` (`sz0_win_third` weakened), `s ≡ 1/10 < t ≡ 1/2 ≤ T0` (`half_lt_t0`), `STConStInd` from `s1Setup_conStInd_const`; the non-main member is `BAzSrc sz0 zSeq (2/3) (17/25)` of `Fam(1/10) = Fam(1/2)` (`inst_BAFamZ_closed`, `BAFamZ_mono_max`), horizon ratio `(2/3)/(17/25) = 50/51 < 1` (`BAtauS`, `Step1Fam:60`). Left as hypotheses (other gates' pins): the six family conjuncts per member (stochastic), `hS1` (V2a's 1b target), `STBaseG`, `STG0M`, `STHorizonG` (V3), the family step (V2b), the seven shifted conclusions.

## D3 = V-C1 step 3 (members)
- **D3 (a) `T2503_memberFlow`** (:115-123). `t ≤ BAflowT0 sz z'` is the merged `BAFamZ_horizon` (`Step1Boot:179`). V-C1 step 3's "same `(κ, ε, 𝔠, 𝔡)`" is false as written on `main`: a member is a `BAFlow` for the same `(𝔠, 𝔡)` but at `(κ', ε') = (c_κ(κ) κ, ε/2)`, `c_κ(κ) = √min(κ/(κ+1), 1/2)` (`Step1Fam:488`, `:624-626`), after the finite modification `z'' n = if n < n₀ then z n else z' n` (`BAFlowMember`, `Step1Boot:133`); `(κ', ε')` is fixed by `(κ, ε, 𝔡)` before `(𝔠, sz, z)`. At the instance (κ, ε) = (1/4, 1/10): `κ' = 0.1118`, `ε' = 1/20`, `n₀ = 5` ((a) rows 4-6). The horizon of `z''` is `≥ t` at every `n` (`BAflowT0_congr`, `Step1Fam:74`, below `n₀`; `BAFamZ_horizon` from `n₀`), and `z''` is `FlowFM.EvEq` to the member. Not a stop (ticket answer (3)); for DECISIONS §314 (dispatcher).
- **D3 (b) `T2503_tl2Congr`** (:95-102, 8 lines; public in V2a's 1b as `BATwistLoopLaw_congr`): `twL2'` reads `C.G n` and `twK` reads `C.M n` (`BA/TwistPins:70, 76`), the `PrecL` index type depends on `sz.L n` only, so `PrecL_congr` (`Step1Boot:185`) applies with `EqAt.G`, `EqAt.M`.
- **D3 (c) `T2503_memberBase`** (:142-154): `STBaseG` (`Induction/MainIndBase:58`), `baTwistLoopBase_holds` (`TwistChain:110`) and `STG0M` (`:54`) at `z''` give `STConclgL` and TL2 at the zero sequence for the member, then back by the congruences. `t = 0 ≤ T0(z)` is `BAflow_T0_bounds` (`Step1Trivial:47`), and D3 (a) then gives `0 ≤ T0(z'')`; all facts are tail-local. V3's base statements are uniform over `BAflow` at every `(κ, ε)` with `0 < ε`, `0 < 𝔡` (`STBaseG` quantifies both; K3 variant of `stBaseG_of_init`, `MainIndBase:110`), so they cover the members: the theorem takes exactly V3's `STBaseG` and `STG0M` as hypotheses.
- **D3 (d), class `t_n = 0`: mix at the main flow only.** The chain runs to `t'_n = T0_n/2` on the class and the last `exact` of `T2503_baChainFamTL` (:235-261) mixes the base at the zero sequence with the chain at `t'` for the main flow `z` (`BAFamZ_main`, `Step1Trivial:56`), as `baChainTL_holds` does. `Fam(0) = Fam(T0/2)` is also true ((a) row 12: `BAFamZ_mono_max`, `Step1Fam:172`, `T0 < 1`, `c₁ ≤ 1/2`) but unused and not compiled. Correction to (a): its sentence "so no mixing at the main flow is needed" is wrong, the mix is needed (see (a′)); no verdict changes.

## D4 = V-C1 step 4 (price)
Compiled pieces (probe lines, `spans.py`): family step 28 pins + 45 proofs (`tl2Congr` 8, `k2Member` 7, `famStep1Call` 5, `memberFlow` 9, `famOfS1` 16); chain twin 110 = `memberBase` 13, `tailPassage` 12, `shift_mono` + `precL_shift` + `conclShift` 28, `posConclFam` 30, `baChainFamTL` 27. Basis (`d4_price.py`, output below): compiled lines ×1.0 = lo, ×1.5 = central (docstrings, imports, instances, public names), ×2.6 = hi (TL's realized/central, DECISIONS §268 (1) TLC-4); uncompiled pieces are my line estimates, named in the table.
```
$ python3 -I d4_price.py
compiled: family-step pins 28 proofs 45 chain twin (memberBase+tail+shift+posConclFam+chain) 110
V2a lo/central/hi (273, 440, 950)  REQ 2,200 / 2 rows
V2b lo/central/hi (540, 700, 1100)  REQ 1,400 / 1 row
V3  lo/central/hi (240, 395, 766)  REQ 1,400 / 1 row (<= 700 likely, T2379-design:86)
sum (1053, 1535, 2816)  REQ 5,000
V rows lo/point/hi (V1s1 3, V1s2 1-2, V1s3 1-2, V1-BA 2, V2a 1-2, V2b 1, V3 1, gate 1): 11 12.0 14
```
- **(a) the family twin of `baChainTL_holds`: compiled, `T2503_baChainFamTL` (:235-261) and `T2503_posConclFam` (:203-232).** Family induction with motive "every member of `Fam(p_k)`" over `stChainTime` (`MainIndChain:51, 80`), base `T2503_memberBase`, step `T2503_BAMainIndFamTL d STAny`, the six hypotheses from `STConclgL ∧ TL2` and `STLocalMaxgL_of_STLocalEntrygL` (`MainIndChain:126`); the five `TwistChain_*_mix` plus the TL2 mix by `open private` (:202), no copy. The single-flow model (`TwistChain:144-264`, 121 lines, 47 of them the mixing section `:186-232`, reused here by `open private`) is twinned by 57 lines (`posConclFam` 30, `baChainFamTL` 27); with the member base, tail passage and shift the family route is 110 lines.
- **(b) tail passage, route (α) chosen, compiled.** `T2503_tailPassage` (:155-166): from `WO` (`hflow.1.2.2.2.2`) an `n₀` with `0 < lam ≤ 𝔡⁻¹` on the tail, `BAFlow` at `κ/2` by `comp_admissible` (`SizesComp:93`) and pointwise `BAdom`, window by `BAWinBulk_of_dom_holds` (`CouplingWindow:836`) at `κ/2` (T2205 audit O5). `T2503_precL_shift` + `T2503_conclShift` (:169-195, 27 lines) carry the seven conclusions back along the shift with the merged `stochDomAt_iff_comp_cover` (`SizesComp:536`), `seqP_withLam_reindex_preimage` (`:239`) and `integral_reindex` (`:253`); the carrier objects `L`, `K`, `G`, `M` that the seven predicates read commute with `reindex` by `rfl` (the `fun _ _ _ => rfl` arguments), so no V2b transport is needed and V3 can run beside V2a's 1b (Q2, answer (9)). Route (β) is not cheaper: `BAdom` (`MFixedPoint:435`) reads `BAm d (L n) (lam n) (z n)`, so changing `lam` below `n₀` needs a fresh flow point for each such `n`, and a grep of `BA/` and `Graph/` (`∃ z … BAdom`, `BAdom_exists`, `flow_exists`, `BAFlow_exists`) finds no existence lemma for such points.
- **(c) the wrapper** is priced inside V2a (16 compiled lines).

| row | file | statements (= probe pins) | lo / central / hi (lines) | role | dependencies | order |
|---|---|---|---|---|---|---|
| V2a (REQ 2,200, 2 rows) | `BA/MainIndFamTL` (new; TL untouched) | `BAMainIndFamTL`, `BAMainIndS1TL` (:33-58), public `BATwistLoopLaw_congr` (:95), K2, family Step-1 call, `BAFlowMember` reading, wrapper (:103-139); uncompiled: generic `BA_mainIndS1_of_steps` (120 / 180 / 300) after `ST_mainIndR_of_steps` (`MainIndRegimes:165`), four regime theorems (20 / 30 / 60), `d = 3` instances with private data for (i), (ii), (iv) (60 / 120 / 400) | 273 / 440 / 950 (1 row) | prover-hard (T2379: prover-max; no new mathematics is left in V2a) | U3-BA (a)/(b), V1-BA (waiting); T2501 b merged | 1 |
| V2b (REQ 1,400, 1) | `BA/MainIndGlue` | `BA_mainInd_of_regimes` in family form (T2205:2462-2489, 2521-2615, 2789-3309 minus the superseded `BAExactLaw` block, ≈ 97 lines, and with the ≈ 100 lines of `*_fwd`/`*_cov` replaced by 12 one-line transports through `stochDomAt_iff_comp_cover`, TL2 included) | 540 / 700 / 1,100 (1 row) | prover (port) | V2a statements; T2206 merged | 2 |
| V3 (REQ 1,400, 1; "likely ≤ 700", `T2379-design:86`) | `BA/MainIndOutBA` | `BAChainFamTL` = `T2503_baChainFamTL`, member base, tail passage and shift (:142-261, compiled); V3-owned `STG0M` (15 / 25 / 50), `STLK0` at `baFMz` (30 / 60 / 150), `STBaseG` K3 variant (20 / 30 / 60), `STHorizonG` (20 / 35 / 80), `UNMLOutBA` wrapper (5 / 10 / 20), instances (40 / 70 / 120) | 240 / 395 / 766 (1 row) | prover-hard | the family step as a hypothesis (beside V2a's 1b); `BAMLOutTL 3` from it | beside V2a |
**V forecast.** Rows: V1s1 3 (T2502), V1s2′ 1-2, V1s3′ 1-2, V1-BA 2, V2a 1 (bottom-up; the REQ reading is 2), V2b 1, V3 1, this gate 1 (the Q5 (a) "+1"): 11 / 12 / 14 (the script's last line). **≈ 12 (11-14), unchanged; below 15: no REQ (Q1).** The family step shortens V2a (the family enters once, through a 16-line wrapper) and the chain twin is 110 lines, so the family route adds no row.

## 1b targets and inputs (V2a: per regime `T2503_RegShape d R Rc S6`, then `BAMainIndFamTL d R` by the wrapper)
| regime | Steps 3-4 | Step 5 | Step 6 | status |
|---|---|---|---|---|
| (iii) `STReg5III` | `STStep3RgL/4RgL d STCaseI` at the BA tuple (`Step34Gen:347, 359`) | hypothesis `STStep5IIIgL d` at `baPin` (`Step5Gen:228`, `LWPinsBA:39`; Q4); `d = 3`: merged `baStep5III_holds` (`Step5IIITargets:57`), exact type compiled :308 | `T2503_Step6BA d STReg5III` | Steps 3-4: waiting (U3-BA (b): `T2498.state`: U3s3a merged ec57490f, a′ on `t/T2498a2`; U3s4 not released and U3-BA not drafted: ticket, DECISIONS §314 (8)); Step 6: waiting (V1-BA: `T2502.state` row a proving) |
| (i) `STReg5I` | case (i) | merged `baStep5I_holds` (`Step5CasesBA:248`, T2501 b bbb1fd30), exact type :305 | `T2503_Step6BA d STReg5I` | as (iii) |
| (ii) `STReg5II` | case (ii) | merged `baStep5II_holds` (`:254`), :306 | `T2503_Step6BA d STReg5II` | as (iii) |
| (iv) `STReg5IV` | case (ii), `3 ≤ d` (`st_caseII_of_reg5IV`, `MainIndRegimes:145`) | merged `baStep5IV_holds` (`:260`), :307 | `T2503_Step6BA d STReg5IV` | as (iii) |
Corrections to the ticket's table: none to a row; two additions. (1) **Step 6** (:288-294): T2502's generic text has no TL premises, but `BALWtermEXPTw` (`Graph/BAExp14a2:92`, producer `baLWtermEXPTw_holds`, `Graph/BALWOut:54`) reads TL1 and TL2 at each time `u`; so V1-BA's `BAStep6R` is T2502's `Step6RgL` at the BA tuple with `∀ u ∈ [s,t], BATwistAvgLaw u ∧ BATwistLoopLaw u` on the `Concl` slot (`T2503_Step6BA`), which V2a supplies by `TwistStep2_tl1` (`TwistStep2:1137`) and `baTwistLoopStep_caseI/II` (`TwistLoop:705, 709`); a proposal for V1-BA's ticket, compiled in all four regime readings (:303-304); single flow, no family form needed for Step 6. (2) **Common inputs, all merged and read by name:** Step 1 `baStep1_holds'` through the wrapper; Step 2 `baStep2_closed` (`Graph/BATermHoldsB:879`), `baStep2Decay_holds` (`DecayLoopBA:114`; its binders are exactly the five Step-1 premises that `S1` carries), `baSTLWB_of`, `baSTLWT_of` (`:135, 140`) fed by `baLWterm_holds` (`Graph/BATermHolds:706`), `baLWtermExp_holds` (`BATermHoldsB:865`); K12 `baKbound_holds`, `baKward_holds` (`BA/KBound:245, 302`); T7-BA `baDecayLoopU_of` (`DecayLoopBA:60`); `twSteps` conjuncts 1-4 by `Iff.rfl`; regime to case `st_caseI_of_reg5III/I`, `st_caseII_of_reg5II/IV` (`MainIndRegimes:125, 137, 141, 145`). **U6-BA does not gate V2a's 1b** (answer (7)): V2a states Step 5 as the merged `STStep5RgL` at the BA tuple (`T2503_Step5BA`, :300) and reads T2501 b by name; U6-BA's abbreviation `BAStep5R` is not read. V2a's 1b starts after U3-BA (a)/(b) and V1-BA merge. Regimes (i), (ii), (iv) are empty at `sz0` for constant `(s, t)` ((a) row 15), so their `d = 3` instances need private data or hypothesised intervals (T2501 Amend 1 precedent).

## `T2503v1_` re-check, paper deltas, findings, stop rules
- **Re-check table** (section 0): the four copies `T2503v1_Exp2UgL`, `Step2CoregL`, `IngR6gL`, `Step6RgL` (:264-287) equal T2502's check pins (`T2502-check.lean:182, 189, 194, 210`) after the prefix map; T2502 is not merged (`T2502.state`: proving, row a), so re-check at its merge with `python3 -I recheck_v1.py` against `Chain/Step6Gen`.
- **Paper deltas:** none beyond D536 (family form, finite modification `(κ', ε')`) and D538 (`∀ n, 0 < sz.lam n`, the tail `Sizes.comp (· + n₀)` and the window at `κ/2`), `docs/paper-deltas.md:1495, 1497`. No `T2503a` candidate.
- **Findings.** F1: `LWPinsBA.lean:50, 52` (`BASTLWB`, `BASTLWT`, "owed: T1-BA / T7-BA, through L5") are stale in the same way (`baSTLWB_of`, `baSTLWT_of` bridge them from the proved `BALWterm`, `BALWtermExp`); outside this ticket's four lines, for the next LC-1 touch. F2: `BAChainTL`/`baChainTL_holds` stay valid and unused; the comments say so. F3: the case-(iii) general-`d` hypothesis is unchanged (Q4, owner text "Jun scope decision (D712 (d); supervisor 2026-10-14-0342 V-F2)").
- **Stop rules (ticket):** family Step-1 call typechecks at exact type (:110): not fired. Per-member base obtainable (:142) with `t ≤ T0` at every `n` (:115): not fired. No merged statement changed (`BAStep1`, `BAFamZ`, `BAFlowMember`, TL pins, `STBaseG` untouched; the TL files change two doc comments only): not fired. Unmerged check texts changed: none. D4 forecast 12, not ≥ 15: not fired. Probe 391 ≤ 400 and this report ≤ 250 lines (`wc -l` in section 0): not fired.

## Fill-in table (stage-1a deliverables of T2503; line = line of this report)
| item | where |
|---|---|
| First line: (a) D1 pinned/changed, (b) D2 compiled and D2 (c), (c) D3 verdict with the (κ', ε') reading, (d) D4 central, rows, V forecast | line 1 |
| Forecast ≥ 15 in the first line | n/a, because the forecast is 12 (11-14), below 15 (line 1, V forecast 132) |
| D1 (a) binding text pinned or changed; change table (old, new, why) | 66-84; `Iff.rfl` 25 |
| D1 (b) `S1` and the wrapper; whether the wrapper needs more than D2/D3 | 85 (no: only D2, D3 and the nine congruences) |
| D1 (c) doc-comment texts (`BAMainIndTL`, `BAChainTL`) and LC-1 texts; answer (4) taken | 86; script check 39-48; full build 51 |
| D2 (a) K2 per member, `baKbound_holds` at the modified flow | 101; probe :103 |
| D2 (b) `baStep1_holds'` at exact type, no restatement of `BAStep1` | 102; probe :110 |
| D2 (c) `T2503_famOfS1` (≤ 180 lines: yes) | 103; probe :124-139 |
| D3 (a) members: flow at `(κ', ε')`, horizon, `EvEq`; the `(κ', ε')` reading | 107; probe :115 |
| D3 (b) TL2 congruence | 108; probe :95 |
| D3 (c) per-member base; V3's uniform base statements cover the members | 109; probe :142 |
| D3 (d) class `t_n = 0`: which | 110 (mix at the main flow only) |
| D4 (a) family twin of `baChainTL_holds`, lo / central / hi | 123; table 129; `d4_price.out` 115 |
| D4 (b) tail passage: route (α) or (β), probe typechecks the passage | 124; probe :155-196 |
| D4 (c) wrapper priced | 125 |
| V row table: files, statements = probe pins, lo / central / hi, role, dependencies, order | 129-131 |
| Whether V's forecast moves | 132 (no) |
| 1b targets and inputs (merged / running / waiting / hypothesis); corrections | 134-141 |
| `T2503v1_` re-check table | 144; section 0 34-38 |
| Paper-delta note (expected none beyond D536/D538) | 145 |
| Acceptance, probe: `lake env lean` exit 0, standard axioms, no sorry/admit/axiom/native_decide/inductive, ≤ 400 lines, `d = 3` instances | section 0 8-23; instances 104 |
| Acceptance, check: probe `T2503_BAMainIndFamTL` equals the check's by `Iff.rfl` | 25 |
| Acceptance, diff: `git diff --stat main...t/T2503`, comment-only lines, `lake build` | 53; 39; 51 |
| Sibling scan / name clash of the new public names | 32 |
| Stop rules (binding): the five rules | 147 |
| Findings | 146 |
