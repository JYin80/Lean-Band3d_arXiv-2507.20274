Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 05:46:40 UTC 2026

Worktree `RBM3D-wt/T2490` HEAD `e6c26ca4` = `main` `e6c26ca4` (ticket text says 4270f377; the merged inputs below are read at `e6c26ca4`). T2489 state: `proving` (not merged), so target 5 is not in scope at this start state.

### (i) Exponent table

| # | quantity | value / where | constraint | slack |
|---|---|---|---|---|
| E1 | `ζ_n = (1-t_n)⁻¹ B^{5/2}`, `B = sz.Bctl n (t n)` | the bound text is identical in `LWtermEXPG` (`Chain/LWGen:119`), S1 (`BAExp14aB:129`), S2 (`BAExp14b:176`), S3 (`:187`), check `T2490_LWCutExpG`/`BALWCutExpTw`/`BALWtermEXPTw` (`T2490-check:136,147,158`) | same `ζ` in all five, so targets 2, 3 carry it unchanged | exact (no loss) |
| E2 | exponent of each input bound | `N^{τ/2}ζ`, from `StochDomAt` at `τ/2` for each `τ > 0` (`BAExp14a_det_iff`, `BAExp14a:58`) | `τ/2 > 0` | exact |
| E3 | reduction (target 2): two cuts | `‖𝔼 LWE‖ ≤ 2 N^{τ/2} ζ ≤ N^{τ/2}·N^{τ/2} ζ = N^τ ζ` | `2 ≤ N^{τ/2}` eventually (`size → ∞`, `Sizes.tendsto_size` of `hflow.1.2.2.1`) | at the instance below: `N^{1/2}/2 = 724.1` (τ=1, n=0) |
| E4 | assembly (target 3): families | `6 (S1) + 8 (S2) + 4 (S3) = 18` terms, `‖𝔼 LWcutg‖ ≤ 18 N^{τ/2} ζ ≤ N^τ ζ` | `18 ≤ N^{τ/2}` eventually; `ζ ≥ 0` (`t n < 1` by `BAExp14a_t_lt_one`, `STBctl_pos`) | τ=1, n=0: `80.45`; τ=1/2: `2.11`; τ=1/10 from `n = 11`: `1.08` |
| E5 | exponent `5/2` of `B` | in the conclusion of every pin | no constraint (not changed) | n/a |
| E6 | dimension `d` | only inside the pins (`3 ≤ d →` first premise of each); no exponent of the reduction or assembly depends on `d` | `3 ≤ d` carried | n/a |
| E7 | index set `U_n` | `sz.lam n ^ 2 / L^d ≤ 1 - t n`, carried verbatim as the subtype of every pin | the same predicate in S1, S2, S3, cut, LWE (see (ii)) | `λ²/L³ = 3.8e-6 ≤ 1/2` at n=0, → 0 |

No `τ`-independent constant is introduced; the only constants are `2` and `18` (counts of terms).

### (ii) Index map, premises, integrability, instance

**Index map** (against the merged texts). Cut index `p = ((σc,σo),(ac,ao))`, subtype of `(Bool×Bool)×(Zd×Zd)` (`T2490-check:146`). S1/S2/S3 index `(k, (σc,σo), (ac,ao))` with `k : Fin 6 / Fin 8 / Fin 4` (`BAExp14aB:128`, `BAExp14b:175`, `BAExp14b:186`). Hence the pointwise input at cut index `p` is the pin at `⟨(k, p.1), p.2⟩`: no swap, no `σc` case split in target 3 (the red charge sits inside `BAExp14aS1Fam`, `BAExp14bS2Fam`, `BAExp14bS3Fam` and the identity `BAExp14bExpand`, `BAExp14b:192`, which is stated at the same `(σc,σo,ac,ao)`). LWE index `(Fin 2 → Bool) × (Fin 2 → Zd)` with the same predicate (`Chain/LWGen:116`; `T2490-check:157`); `LWEg = LWcutg(σ 1,σ 0,a 1,a 0) + LWcutg(σ 0,σ 1,a 0,a 1)` (`LWGen:44`, `rfl`); both cut indices use the same `hg`.

**Premise table** (which of the seven premises of `BALWCutExpTw` each input reads):

| input | premises read | source |
|---|---|---|
| S1 `baExp14a_S1_holds` | 1-2 (`STLocalEntrygL`, `LWAvgLawgL`) | `BAExp14aB:124-129` |
| S2 `BAExp14bS2 d` (antecedent) | 1-7 (all, incl. TL1 `BATwistAvgLaw`, TL2 `BATwistLoopLaw`) | `BAExp14b:170-176` |
| S3 `baExp14bS3_holds` | 1-5 | `BAExp14b:181-187` |
| identity `baExp14b_expand_holds`, conjugation `baExp14b_cut_conj` | none beyond `BAFlow`, `0 ≤ t`, `t ≤ BAflowT0` | `BAExp14b:192-203`, `BAExp14bB:210` |
| reduction (target 2) | none of its own; consumes `BALWCutExpTw` as a whole | |

All seven are available at every cut index of target 3, so S2 is applicable. The three pins end in `PrecL … μ` with `μ = seqP (sz.withLam 0)`, so one uses `StochDomAt` at the same `μ` and the same `sz.size`.

**Integrability of `LWcutg` (target 2 only; the assembly needs none: the identity is an equation of integrals).** Route, public names only: `BAExp14b_cut_true` (`BAExp14bB:146`, `LWcutg true = W^{-2d} Σ_{x,y,α} tail·X·G·G`; its `hSelf` is `(BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1`) turns the `σc = true` cut into a finite sum of products of `BAExp14a_tail`, `BAExp14a_X`, `G`; each `G_{xy}` is continuous (`BAExp14a_cont_G`, `BAExp14aB:791`) and bounded by `η⁻¹` (`BAExp14a_G_le`, `BAExp14a:1273`), `M` is `ω`-independent; `BAExp14a_integrable` (`BAExp14aB:838`) closes. `σc = false` is `star` of the `true` cut at `(!σo, ao, ac)` (`baExp14b_cut_conj`). `BAExp14b_BM*` is `private` (`BAExp14bB:394, 436`), so the bounded-continuous closure lemmas (about 47 lines at `BAExp14bB:389-435`) are re-derived in the new file with stem `BAExp14a2_`. Facts needed from the flow: `t n < 1` and `size → ∞` only (matches the stop rule: no property of `baFMz` beyond continuity, `‖G‖ ≤ η⁻¹`, `t < 1`, `size → ∞`).

**Instance** (all hypotheses of targets 1-4, 6 at once, `d = 3`): `sz0` (`L n = 4(n+1)`, `W n = (2(n+1))^5`, `λ n = (2(n+1))^{-6}`, `Defs/Sizes:260-263`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`FlowPins:1214`), `t ≡ 1/2` with `1/2 < BAflowT0 sz0 zSeq n` (`half_lt_t0`, `FlowPins:1254`; `t0_sz0 : 2/3 ≤ T0`, `:1227`). Check (limit computation for `size → ∞` and the eventual constants, exact rationals):

```
$ python3 -I .../scratchpad/T2490/inst.py
n=0: L,W,N,lam = 4 32 2097152 1/64 N==2097152: True
hyp: 3<=d True kappa,eps,dd>0 True True True
lam^2/L^3 at n=0,1,10,1000: [3.814697265625e-06, 1.1641532182693481e-10, 9.132081961409137e-22, 3.757931987947123e-51]
U_n nonempty (lam^2/L^3<=1-t) for n<2000: True
cut indices at n=0 (Bool^2 x (Zd x Zd)): 16384 families 6+8+4 = 18 terms 294912
tau=1 assembly 18: need N>=c^(2/tau)=3.240e+02; first n0=0; N(n0)=2.097e+06; slack N^(tau/2)/c at n0 = 80.453
tau=1 reduction 2: need N>=c^(2/tau)=4.000e+00; first n0=0; N(n0)=2.097e+06; slack N^(tau/2)/c at n0 = 724.077
tau=1/2 assembly 18: need N>=c^(2/tau)=1.050e+05; first n0=0; N(n0)=2.097e+06; slack N^(tau/2)/c at n0 = 2.114
tau=1/2 reduction 2: need N>=c^(2/tau)=1.600e+01; first n0=0; N(n0)=2.097e+06; slack N^(tau/2)/c at n0 = 19.027
tau=1/10 assembly 18: need N>=c^(2/tau)=1.275e+25; first n0=11; N(n0)=5.583e+25; slack N^(tau/2)/c at n0 = 1.077
tau=1/10 reduction 2: need N>=c^(2/tau)=1.049e+06; first n0=0; N(n0)=2.097e+06; slack N^(tau/2)/c at n0 = 1.035
tau=1,n=0: N^(1/2) = 1448.1546878700494 ; slack vs 18: 80.45303821500275
closed form N(n)=2^21 (n+1)^18 (strictly increasing, -> inf): True
```

`N(n) = (W L)^3 = 2^21 (n+1)^18` is increasing, so "first `n0`" holds for all `n ≥ n0`. The instance is nondegenerate: `N_0 = 2097152`, 16384 cut indices, `U_n` is the full index set (`λ²/L³ ≤ 4e-6 < 1/2`). The deterministic hypotheses are discharged; the external ones (five Step 1/2 pins, TL1, TL2, S2) are other gates' pins and stay hypotheses of the examples. TL1 is dischargeable by name for instance 6 (c): `baTwistAvgProd_holds 3` (`TwistAvgB:451`) reads `LWAvgLawgL`, `STLmaxgL` (`TwistPins:154-158`), matching the ticket; TL2 has no producer at a fixed `t` (`Test/Axioms.lean:193`).

### Registry (`Test/Axioms.lean`)

`scanPremises` (`:471-492`) looks at theorems whose name has prefix `RBM` and is not internal; `private` names carry the prefix `_private`, so private helpers are not scanned (consistent with the T2482 block of §290 (3)). It collects the Prop defs occurring in the binders of such theorems.
- Planned public theorems: `LWCutExp_iff`, `band_LWCutExpG`, `baLWtermEXPTw_of_cut`, `baLWCutExpTw_of_S2`, `baLWtermEXPTw_of_S2` (and closures under the start decision). Their types are `∀ d : ℕ, <Of-def> d`, `<iff>` or `bandPin … 3`; the only binder is `d : ℕ`, so no Prop def is assumed. They conclude `BALWtermEXPTwOfCut`, `BALWCutExpTwOfS2`, `BALWtermEXPTwOfS2` (target 5: `BALWCutExpTw`, `BALWtermEXPTw`), which no one assumes.
- `BAExp14bS2` (antecedent) occurs only inside the body of the new Of-defs, not in a theorem binder; it is not in `Test/Axioms.lean` today (grep: no hit) and no merged theorem takes it (grep over `RBM3D`: only `BAExp14b.lean`).
- The five Step 1/2 pins and TL1, TL2 occur only inside the new Prop defs: registered at `Axioms.lean:133` (`STLmaxgL`), `:135` (`STLKgL`), `:144` (`STLocalEntrygL`), `:217` (`STDecaygL`), `:192` (`BATwistAvgLaw`), `:193` (`BATwistLoopLaw`); `LWAvgLawgL` has no line (not needed).
- **Lines needed: none.** `Test/Axioms.lean` stays unchanged. A public helper with a `BAExp14bS2`, `BATwist*` or `BALWCutExpTw` binder would be unregistered: all helpers stay `private` (§3 (E)).

### (vi) Line estimate (re-priced by census) against 2,000 / 1,950 / 1,800

```
$ sed -n counts: band twin LWExpTerm 47-64: 18; 204-328: 125; 1212-1231: 20; LWExpTerm2 1953-2023: 71 (= 234); probe 411-440: 30, 458-471: 14 (= 44); total 278
$ BA private BM scaffold BAExp14bB 389-435: 47; atoms 436-462: 27; cut_true 146-203: 58
bottom-up lines: 485   (header 50, pins 70, BM scaffold 50, atoms+cut BM 75, reduction 65, assembly 110, composition 10, instances 55, closures 0)
central (x1.15 docstring/blank overhead): 558; ticket drafting 420/600/1100
```

Central about 560 lines; high end 1,100 (ticket's upper reference, 1.61 × twin lines plus the new parts). **Neither rule applies:** 560 is below 1,800 (reserve `BAExp14a2B` not needed) and below 1,950 (pre-signed split 1 | 2 not taken); even the 1,100 upper value is below 1,800. One file `RBM3D/Graph/BAExp14a2.lean`, stop line 2,000 not near. Consequently L stays 45 / 50 and the L40-C3 projection 47 (no split); L40-C4: no fold (dispatcher answer (2)); nothing found here reopens it.

### Notes for the 1b (not process narrative)

- `BAExp14a_inst_prob` is stated for `BAExp14a_μ sz : Measure sz.SeqΩ`; the pins are stated with `let μ := Sizes.seqP (sz.withLam 0)` (docstring `BAExp14aB:647`: equal but not reducibly): convert with `change`/`show` at `BAExp14a_μ sz` before `BAExp14a_det_iff`.
- UBA-C1: not triggered; `sz.lam` occurs only in the carried index-set predicate and `withLam 0` only in the law `μ`; no comparison with `gK`.
- Paper delta candidate (already filed by the ticket, T2398d): BA `B:118` "analogous … omit"; the BA cut pin carries TL1, TL2 (R1).

### Verdicts

- Target 1 (pins, band bridge, statement defs): PASS (shapes fixed by `T2490-check`, which the hub compiled with exit 0, CONTROL H274 (2)).
- Target 2 (reduction): PASS (E3; integrability by public names + local BM closure).
- Target 3 (assembly): PASS (E4; index map without swap; premises 1-7 available; no integrability needed).
- Target 4 (composition): PASS.
- Target 5 (closures): not in scope at this state (T2489 `proving`); the 1b decides at its start; exponent-wise nothing blocks it.
- Target 6 (instances): PASS (instance above; (c) TL1 by name).
- Target 7 (C1, registry): PASS (no registry line, no crossing).
- Overall: **PASS**.

## (a′) Preflight corrections — Tue Oct 13 06:04:46 UTC 2026

- E4 (line 14 of this report) cites `BAExp14a_t_lt_one` for `t n < 1`. That lemma is stated for `Sizes (k + 2)` (`RBM3D/Graph/BAExp14aB.lean:1267`) and does not apply at a general `d`. The file uses `(ba_G_data hκ sz hflow n (ht0 n) (htT n)).1` (`RBM3D/BA/GreenLDE.lean:55`, any `d`). No verdict changes.

## (b) Script output

**Start decision.** At 05:47:46 UTC (first `date -u` of the 1b, tool log) `docs/queue/T2489.state` read `state: proving` (`updated: Tue Oct 13 05:00:43 UTC 2026`) and `git log main` had no `T2489: merge` commit; re-read below, unchanged. **T2489 is not merged, so target 5 (closures) is not delivered; it goes to the last terminal ticket (L40-C1).** Targets 1-4 and 6 are delivered in one row, no split.
```
$ date -u; head -4 docs/queue/T2489.state; git log main -1 --format="main %h %s" | cut -c1-80; git log main --oneline | grep -c "T2489: merge"
Tue Oct 13 06:00:07 UTC 2026
state: proving
reason: started (H273, H12) in the slot freed by T2488: workflow wf_c6388f4b-e6e, stage 1a preflight (split at
updated: Tue Oct 13 05:00:43 UTC 2026
reports: docs/reports/T2489-prove.md, docs/reports/T2489-audit.md
main 7be99aae T2486: merge U2-BA (a) BA/KDecayBA, SEforLnBA (split; (b) B45BA fo
0
```
**Filled 1a table** (lines of this report): (i) exponent table 7-19; (ii) index map 23; (iii) premise table 25-35; (iv) integrability route 37; (v) UBA-C1 82, registry 60-66, tables below; (vi) predicted lines 68-77, actual below.

**Lines, branch, build, axioms.** Stop line 2,000: the file has 406 lines (predicted central 558, line 77); the 1,950 split and the reserve file `BAExp14a2B` are not used; L40-C4: no fold (dispatcher answer (2)); nothing found here reopens it.
```
$ git log -1 --format="%h %an" t/T2490; wc -l RBM3D/Graph/BAExp14a2.lean; git diff --stat main...t/T2490; grep -rln BAExp14a2 RBM3D RBM3D.lean | grep -v Graph/BAExp14a2.lean
b10f2c9f Jun Yin
     406 RBM3D/Graph/BAExp14a2.lean
 RBM3D.lean                 |   1 +
 RBM3D/Graph/BAExp14a2.lean | 406 +++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 407 insertions(+)
RBM3D.lean
$ lake build RBM3D.Graph.BAExp14a2 | grep -E "BAExp14a2|Build completed|error"   (no warning of the file)
Build completed successfully (4050 jobs).
$ lake build | grep -E "axiom audit|premises found|Build completed|error"   (RBM3D.lean with the import line)
info: RBM3D.lean:583:0: axiom audit: 14600 theorems, 4558 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 61, structural 46, refuted 6, superseded 14).
Build completed successfully (4351 jobs).
$ lake env lean ax.lean   (import RBM3D.Graph.BAExp14a2; #print axioms of the five public results)
LWCutExp_iff : [propext, Classical.choice, Quot.sound]
band_LWCutExpG : [propext, Classical.choice, Quot.sound]
baLWtermEXPTw_of_cut : [propext, Classical.choice, Quot.sound]
baLWCutExpTw_of_S2 : [propext, Classical.choice, Quot.sound]
baLWtermEXPTw_of_S2 : [propext, Classical.choice, Quot.sound]
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Graph/BAExp14a2.lean: 0;  git diff --stat main...t/T2490 -- RBM3D/Test/Axioms.lean | wc -l:        0
```
**Statement diff against `T2490_*`** (check file `docs/tickets/checks/T2490-check.lean`): targets 1-4 equal the check up to the name; `T2490_CutClosed`, `T2490_TermClosed` (target 5) are not delivered.
```
$ python3 -I stmtdiff.py | grep -E "IDENTICAL|ALL"      (check file vs RBM3D/Graph/BAExp14a2.lean, `T2490_` removed, whitespace normalised)
IDENTICAL LWCutExpG 836
IDENTICAL BALWCutExpTw 730
IDENTICAL BALWtermEXPTw 702
IDENTICAL BALWtermEXPTwOfCut 73
IDENTICAL BALWCutExpTwOfS2 68
IDENTICAL BALWtermEXPTwOfS2 70
ALL DEFS IDENTICAL: True
$ lake env lean cmp.lean; echo exit=$?     (cmp.lean = the check file + `import RBM3D.Graph.BAExp14a2` + the examples below)
exit=0   (grep -ciE "error|sorry" of the output: 0)
example : T2490_BandCut := band_LWCutExpG
example : T2490_Reduction := baLWtermEXPTw_of_cut
example : T2490_Assembly := baLWCutExpTw_of_S2
example : T2490_TermOfS2 := baLWtermEXPTw_of_S2
example : ∀ d : ℕ, LWCutExp d ↔ bandPin T2490_LWCutExpG d := LWCutExp_iff
(+ six `example (d : ℕ) : <def> d = T2490_<def> d := rfl` for LWCutExpG, BALWCutExpTw, BALWtermEXPTw, BALWtermEXPTwOfCut, BALWCutExpTwOfS2, BALWtermEXPTwOfS2)
```

**Target statements extracted from the file.**
```
$ sed -n "73p;77p;102p;105p;108p;218p;272p;326p" RBM3D/Graph/BAExp14a2.lean
theorem LWCutExp_iff (d : ℕ) : LWCutExp d ↔ bandPin LWCutExpG d := Iff.rfl
theorem band_LWCutExpG : bandPin LWCutExpG 3 := (LWCutExp_iff 3).1 (lwCutExp_holds 3)
def BALWtermEXPTwOfCut (d : ℕ) : Prop := BALWCutExpTw d → BALWtermEXPTw d
def BALWCutExpTwOfS2 (d : ℕ) : Prop := BAExp14bS2 d → BALWCutExpTw d
def BALWtermEXPTwOfS2 (d : ℕ) : Prop := BAExp14bS2 d → BALWtermEXPTw d
theorem baLWtermEXPTw_of_cut : ∀ d : ℕ, BALWtermEXPTwOfCut d := by
theorem baLWCutExpTw_of_S2 : ∀ d : ℕ, BALWCutExpTwOfS2 d := by
theorem baLWtermEXPTw_of_S2 : ∀ d : ℕ, BALWtermEXPTwOfS2 d :=
```
The pins `LWCutExpG` (`def` at l.59), `BALWCutExpTw` (l.82), `BALWtermEXPTw` (l.92) are the check's texts (IDENTICAL above).

**Compiled nonempty instances** (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`; the docstring above each example names its target).
```
$ grep -n "^example" RBM3D/Graph/BAExp14a2.lean | cut -c1-72
342:example (hS2 : BAExp14bS2 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ
350:example (hcut : BALWCutExpTw 3) (hE : STLocalEntrygL (baFMz sz0 zSeq
358:example (hS2 : BAExp14bS2 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ
367:example (hS2 : BAExp14bS2 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ
377:example (hcut : BALWCutExpTw 3) (hE : STLocalEntrygL (baFMz sz0 zSeq
393:example (h1 : STLocalEntrygL (bandFM sz0 (STflowE z0)) (Sizes.seqP s
400:example : LWCutExp 3 := (LWCutExp_iff 3).2 band_LWCutExpG
$ sed -n "376,384p" RBM3D/Graph/BAExp14a2.lean | cut -c1-165     (instance 6 (c), the shape of the check)
/-- Instance 6 (c), shape of the check `T2490-check.lean`: the R1 cut pin `BALWCutExpTw 3` at the same data with TL1 produced from `hA`, `hM`. -/
example (hcut : BALWCutExpTw 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  hcut le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
    (baTwistAvgProd_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
      (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM) hT2
```
Discharged: `3 ≤ 3`, `0 < 1/2`, `0 < 1/10` (twice), `flow_sz0`, `0 ≤ t`, `t ≤ BAflowT0` (`half_lt_t0`), TL1 by name in 6 (c). Hypotheses: the five Step 1/2 pins, TL2, TL1 in 6 (a)/(b), `BAExp14bS2 3` (T2489), `BALWCutExpTw 3` in the examples of target 2 and 6 (c). Nondegenerate data: `N_0 = 2097152`, 16384 cut indices at `n = 0` (section (a) lines 39-58).

**Name-clash grep** (final names; `main` and sibling branches). Docstring mentions only on `main` (`BAExp14aB:18, 122`, `BAExp14b:15, 168, 179, 961`, `BAExp14e:346`).
```
$ for r in main t/T2473c t/T2484b t/T2486 t/T2487 t/T2488 t/T2489 t/T2482b: git grep -nE "(def|theorem|abbrev|lemma|structure|inductive|instance) +[A-Za-z_.]*(N)" $r -- RBM3D | grep -vc BAExp14a2.lean; git ls-tree -r --name-only $r | grep -c BAExp14a2
  N = LWCutExpG|LWCutExp_iff|band_LWCutExpG|BALWCutExpTw|BALWtermEXPTw|…OfCut|…OfS2|baLWtermEXPTw_of_cut|baLWCutExpTw_of_S2|baLWtermEXPTw_of_S2|baLWCutExpTw_holds|baLWtermEXPTw_holds|BAExp14a2_|BALWCutExp
main: defs=0 files=0 (7be99aae)   t/T2473c: defs=0 files=0 (61732d61)
t/T2484b: defs=0 files=0 (c61ae3b4)   t/T2486: defs=0 files=0 (19c7f4c7)
t/T2487: defs=0 files=0 (3b9c210d)   t/T2488: defs=0 files=0 (63baa94a)
t/T2489: defs=0 files=0 (5a1e7dae)   t/T2482b: defs=0 files=0 (49b2de45)
```
**Census** (name level; new-file lines in the last column).

| item | source file:line | kind | lines |
|---|---|---|---|
| pins `LWCutExpG`, `BALWCutExpTw`; `BALWtermEXPTw` | probe `t/T2398:RBM3D/Probe/T2398Pins.lean:413-440` (verbatim); `Chain/LWGen.lean:108`, `BA/LWPinsBA.lean:49` | new defs | 57-100 |
| `LWCutExp_iff`, `band_LWCutExpG` | probe `:427`; `Graph/LWExpTerm6.lean:617`; pattern `LWPinsBA.lean:59` | new | 72-77 |
| BM scaffold + atoms | private `BAExp14b_BM*` `BAExp14bB.lean:389-462` | stem copy `BAExp14a2_BM*` | 110-208 |
| reduction; assembly | twins `LWExpTerm.lean:286-328`; `LWExpTerm2.lean:1956-2023` | adapted | 212-259; 261-321 |
| public imports | `baExp14a_S1_holds` `BAExp14aB:1692`; `baExp14b_expand_holds` `BAExp14bB:1035`; `baExp14b_cut_conj` `:210`; `BAExp14b_cut_true` `:146`; `baExp14bS3_holds` `BAExp14e:347`; `BAExp14a_det_iff` `BAExp14a:58`; `BAExp14a_integrable` `BAExp14aB:838`; `BAExp14a_cont_G` `:791`; `BAExp14a_G_le` `BAExp14a:1273`; `ba_G_data` `BA/GreenLDE:55`; `BAflow_real` `BA/GreenSchur:59`; `baTwistAvgProd_holds` `BA/TwistAvgB:451`; `Sizes.tendsto_size` `Defs/StochDomAt:735`; `STBctl_pos` `Induction/ScaleFacts:64` | merged | used |

No port from `../RBM1D` or `../RBM2D` (the twins are RBM3D band files); no RBM1D/RBM2D diff-stat.

**UBA-C1 and hypothesis tables.**
```
$ grep -nE "sz\.lam|withLam|gK" RBM3D/Graph/BAExp14a2.lean | cut -d: -f1 | paste -sd" " -; grep -c gK RBM3D/Graph/BAExp14a2.lean
68 80 84 87 94 97 215 299 301 303 312 339
0
$ python3 -I binders.py   (pin names in the statement of every theorem of the file)
public   LWCutExp_iff               pin names in statement: none
public   band_LWCutExpG             pin names in statement: none
public   baLWtermEXPTw_of_cut       pin names in statement: none
public   baLWCutExpTw_of_S2         pin names in statement: none
public   baLWtermEXPTw_of_S2        pin names in statement: none
private helpers: 13  with pin names in the statement: 0
```
Hits: l.68, 87, 97 are the carried index-set predicate `sz.lam n ^ 2 / L^d ≤ 1 - t n` of the pins (verbatim from `LWtermEXPG` and the probe); l.80, 84, 94, 215, 299-312 write the law `seqP (sz.withLam 0)` (statement text, docstring, integrand law restated for `rw [hid]`); l.339 is the instance notation. No `gK`, no comparison of `sz.lam` with a coupling: UBA-C1 not triggered, no crossing; `BAflowLam0` and `inductive`/`structure` do not occur in the file (grep count 0). The five public results have no binder after `d` and conclude `LWCutExp d ↔ …`, `bandPin LWCutExpG 3`, `BALWtermEXPTwOfCut d`, `BALWCutExpTwOfS2 d`, `BALWtermEXPTwOfS2 d`.

**Registry.** `Test/Axioms.lean` unchanged (the diff stat above lists two files); the full `lake build` with `import RBM3D.Graph.BAExp14a2` after the last import line of `RBM3D.lean` passes the registry scan. The import line is committed with the file; the hub resolves `RBM3D.lean` at merge.

**Narrative.**
- Delivered: targets 1, 2, 3, 4 and 6 in `RBM3D/Graph/BAExp14a2.lean` (406 lines), commit `b10f2c9f` on `t/T2490` (the file and the import line of `RBM3D.lean`). Target 5: not delivered (start decision).
- `baLWCutExpTw_of_S2` and `baLWtermEXPTw_of_S2` are conditional on `BAExp14bS2 d` (antecedent in the statement def); `baLWtermEXPTw_of_cut` is conditional on `BALWCutExpTw d`. None is the unconditional pin; the unconditional closures are target 5.
- Assembly: at the cut index `⟨((σc,σo),(ac,ao)),hg⟩` the pins S1, S2, S3 are applied at `⟨(k,(σc,σo),(ac,ao)),hg⟩` (same subtype, no swap); `baExp14b_expand_holds` already covers both charges, so `baExp14b_cut_conj` is used only for the integrability of the red cut in the reduction. S2 enters only as the antecedent applied to the seven premises.
- Reduction: `LWEg` unfolds to two `LWcutg`; `LWcutg` is bounded continuous (`BAExp14a2_BM_cutg`: `σc = +` through `BAExp14b_cut_true` and the BM closure, `σc = -` through `baExp14b_cut_conj`), hence `integral_add`. `StochDomAt.precomp_param` is not needed: `BAExp14a_det_iff` is taken at the same law and index subtype.
- The pins are stated with the integrand on `(sz.withLam 0).SeqΩ`; `rw [hid]` needs the syntactic `Sizes.seqP (sz.withLam 0)`, not the abbreviation `BAExp14a_μ sz` (used only as the argument `P` of `BAExp14a_det_iff`).

## (c) Verified Mathlib names (all compiled in `lake build RBM3D.Graph.BAExp14a2`)

`norm_sum_le`, `norm_add_le`, `norm_neg`, `norm_star`, `Finset.sum_le_sum`, `MeasureTheory.integral_add`, `continuous_finsetSum`, `Continuous.star`, `Continuous.mul`, `Real.rpow_add`, `Real.rpow_nonneg`, `tendsto_rpow_atTop`, `tendsto_natCast_atTop_iff`, `eventually_ge_atTop`, `half_pos`, `Nat.cast_pos`, `Fintype.card_fin`, `mul_le_mul_of_nonneg_right`. Absent on `main` and the sibling branches: the new public names (grep above).

## (d) Open issues and paper-delta candidates

- Target 5 (`baLWCutExpTw_holds`, `baLWtermEXPTw_holds`, one line each from the producer of `BAExp14bS2`): owed to the last terminal ticket (L40-C1), after T2489 merges. The `Test/Axioms.lean` lines of TL1/TL2 (`:192-193`, "owner: TL stage, closed ... + BA-V") stay registered.
- The merged docstrings `BAExp14aB.lean:18, 122` and `BAExp14b.lean:15, 168` name `BALWCutExpTw`; they resolve to `RBM.BA.BALWCutExpTw` of this file.
- **T2490a**: the Lean successor pin `BALWtermEXPTw` has seven premises (adds `BATwistAvgLaw`, `BATwistLoopLaw` to the five Step 1/2 pins) where `lem:LWterm_EXP` (`6_Step6_two_loop.tex:83-88`) names the Step 1/2 hypotheses only; the paper's BA proof is "analogous ... omit" (`B_graphical_lemmas.tex:118`). Route R1, the same difference as T2398d for the cut pin.
- **T2490b**: the Lean proof of `lem:LWterm_EXP` at BA is decomposed as `LWE → LWcut` (`(eq:ELW_term)`, `B:10-15`) and `𝔼 LWcut = S1 + S2 + S3` (6 + 8 + 4 families); the paper states one bound for `LWE`. The assembly takes S2 as exact-type antecedent (UBA-C3), so the Lean result is conditional until T2489 and target 5.
