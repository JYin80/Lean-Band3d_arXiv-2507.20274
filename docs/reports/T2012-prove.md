Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 01:24:29 UTC 2026

### (i) Exponent table

Scale: every `≺` here is `StochDomAt` at `N := size l` (`sz.size n = (sz.W n * sz.L n)^d`, merged `Defs/Sizes.lean:157`).
`badSetAt size ξ ζ τ l = {ω | ∃ u, (size l)^τ ζ(l,u) < ξ(l,u)}`; `StochDomAt`: ∀ τ,D>0, ∀ᶠ l, P(badSetAt) ≤ ofReal((size l)^{-D}).
Probe (`5d2a4a8:RBM3D/Probe/T2002Vocab.lean` lines 795–935) is Lean-checked; only mathematics is audited here.

| item | value / form | constraint | slack |
|---|---|---|---|
| scale `N` | `(W L)^d`, `d ≥ 3` (`d` is a parameter of `Sizes d`) | `N ≥ 1` (always: `W>0`, `L ≥ 3`) for `prec_of_le`, `precPT_of_le` | `N ≥ 3^d ≥ 27` for every `n` |
| `N → ∞` (`Tendsto size atTop atTop`, `= Sizes.SizeTendsto` after `tendsto_natCast_atTop_iff`) | hypothesis, not a consequence of `Sizes` | needed for every lemma that uses `2 N^{-(D+1)} ≤ N^{-D}` (needs `N ≥ 2`), `N^C ≥ 1`, or `C ≤ N^{e}`: the At-versions of trans, add, mul, of_forall_le, HighProbAt.inter/biInter, absorb, `stochDomAt_of_momentDomAt`, `stochDomAt_Icc_of_holder_on_good` | at `sz0`: `n ≤ N_n` (script), so `N_n ≥ 2` from `n=0` on |
| `prec_of_le`, `precPT_of_le`, `Prec.whp`, `stochDom_iff_at_id`, `highProb_iff_at_id`, `perTimeOfStochDomAt`, `perTimeDomAt_iff_forall_section` | no `N → ∞` | `1 ≤ N^τ` for `τ>0` (from `1 ≤ N`); the other four need no size hypothesis | none |
| transitivity split | `τ ↦ τ/2`, `(N^{τ/2})^2 = N^τ` (`rpow_add'`, `τ/2+τ/2 ≠ 0`, `N ≥ 0`) | `N^{τ/2} ≥ 0` only | exact |
| union of two bad sets (trans, add, mul) | `P ≤ 2 N^{-(D+1)}` | `2 N^{-(D+1)} ≤ N^{-D}` iff `N ≥ 2` | `N ≥ 2`; at `sz0` `N_0 = 2097152` |
| grid union bound (`stochDomAt_of_perTimeDomAt`, `highProbAt_iInter`) | `#U(l) ≤ N^C`, `C ≥ 0`; per-time bound at `D' = D + C` | `N^C · N^{-(D+C)} = N^{-D}` (`rpow_add'`, `D ≠ 0`, `N ≥ 0`): no `N ≥ 1` needed | exact equality |
| Markov (`meas_gt_le_of_moment`) | `P(Y > t) ≤ M / t^{2p}`, `t = N^τ Φ` | `t>0`, `E|Y|^{2p} ≤ M`, integrable | exact |
| moment ⇒ `≺` (`MomentDomAt`: `E|Y|^{2p} ≤ C N^{εp} Φ^{2p}`, `ε` outside `p`) | `ε := τ`, `p := ⌈(D + C_card + 1)/τ⌉`, bound `C N^{-τp}` | `C N^{-τp} ≤ N^{-(D+C_card)}` iff `C ≤ N^{τp-D-C_card}` | `τp − D − C_card ≥ 1`, so `N ≥ C` suffices |
| Hölder time net on `[0,T]` | `A = (K+B+1)/γ`, `m = ⌈N^A⌉+1`, points `m+1`, `#U = ⌈N^A⌉+2` | `K,B ≥ 0`, `γ>0`, `T>0`, `N^{-B} ≤ Φ`; `#U ≤ N^{A+1}` needs `N ≥ 4`, `A ≥ 0` | `⌈N^A⌉+2 ≤ N^A+3 ≤ N^A·N` for `N ≥ 4` |
| net error | `N^K (T/m)^γ ≤ N^K T^γ N^{-Aγ} = T^γ N^{-B-1}` | `≤ N^{τ/2} Φ`: `T^γ N^{-1} ≤ 1` (`N ≥ T^γ`) and `N^{-B} ≤ Φ` | factor `N^{-1}`; `2 N^{τ/2} ≤ N^τ` needs `N^{τ/2} ≥ 2` |
| net Markov exponent | `C_card = A+1` | `p = ⌈(D+A+2)/τ⌉`, `τp − (D+A+1) ≥ 1` | 1 |
| `highProbAt` from `Prec.whp` | event `{∀u, ξ ≤ N^τ ζ}` | complement `= badSetAt` (set equality) | exact |

**Finding F1 (source of the "StochDomAt calculus").** In `RBM2D` at `c9a24cf`, `Defs/StochDom.lean` has `StochDomAt` only in the def (line 103) and `StochDomAt.of_unifDetDom_L_scale` (line 334; scale `W^2 l^2`, d=2-specific, not the `size` scale). The calculus `refl, trans, add, mul, const_mul_*, of_forall_le, of_subset*, NormStochDom, Absorb` exists there only for the index scale `StochDom` (merged in `RBM3D/Defs/StochDom.lean`). Command and output below. So the `StochDomAt` calculus of target 2 has no RBM2D source: it is the index-scale proof with `N := size l`, plus the hypothesis `Tendsto size atTop atTop` (row above). The mathematics is the same proof; statements are true with that hypothesis. Without it the step `2 N^{-(D+1)} ≤ N^{-D}` fails for `N = 1` (`2 > 1`), so the proof does not go through for bounded `size`; `prec_of_le` etc. do not need it.
**Finding F2.** `stochDomAt_of_momentDomAt`, `stochDomAt_Icc_of_holder_on_good` (RBM2D `Gauss/Domination.lean:171, :474`) carry `hsize : Tendsto size atTop atTop`; `sz.SizeTendsto` supplies it. `momentDomAt_of_stochDomAt` is at `MomentBridge.lean:170`.
**Finding F3.** `HighProbAt` is pinned in `StochDomAt.lean` (probe line 834); `highProbAt_univ`, `stochDomAt_Icc_of_holder_on_good` (RBM2D `Gauss/Domination.lean:463–467, :474`) must be ported against that pinned def, not a second copy.

### (ii) One concrete nondegenerate instance

Sizes: probe `T2002Inst.sz0` (`d=3`, `L n = 4(n+1)`, `W n = (2(n+1))^5`, `N_n = ((2(n+1))^5 · 4(n+1))^3`; `N_0 = 2097152`; not `N=0`, not empty index). Parameters: `D=1`, `C_card=2`, grid net `K=1,B=1,γ=1/2,T=1` (`A=6`), moment constant `C0=5` (the constant of `MomentDom`, a hypothesis), `Φ=N^{-B}`.
Hypotheses of the targets checked at once: `1 ≤ N`, `N ≥ 2` and `N_n ≥ n` (so `SizeTendsto`); grid `#U ≤ N^C`; Markov + union with `p=⌈(D+C_card+1)/τ⌉` at `N ∈ {10^3, 10^6, N_0}`, `τ ∈ {0.01, 0.1}`; net cardinality and net error.
For the compiled instances: `prec_of_le` at `sz0` with `ξ = ζ = 1` (needs `ζ ≥ 0`, `ξ ≤ ζ`, `1 ≤ N_n`); `StochDomAt` trans at `size = sz0.size`, `ξ = ζ = χ = 1`, `Ω = Unit`, `P = dirac ()`, hypotheses `Tendsto sz0.size atTop atTop` (from `sz0_tendsto`, probe line 1089), `StochDomAt P size 1 1` (empty bad set since `1 ≤ N^τ·1`).
External hypothesis: none (the moment constant `C0` and `Ccard` are hypotheses of `MomentDomAt` / `hcard`, supplied by the caller; no authorized external input is used). Concrete limit: `N_n → ∞` as `n ≤ N_n` (script line 1), and `C0 N^{-τp} N^{C_card} ≤ N^{-D}` for `N ≥ C0^{1/1} = 5` (script, last lines).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2012_pre.py`
```
sz0 N_0 = 2097152  N_1 = 549755813888  n<=N_n for n<200: True  min_n N_n >= 2: True
N=10^3.000 tau=0.01 p=400 tau*p=4.00 log10(Markov)=-11.30 <= -9.00: True; after union -5.30 <= -3.00: True; net err True; 2N^-(D+1)<=N^-D True; card<=N^(A+1) True/True (A=6.0, card=1e+18)
N=10^3.000 tau=0.1 p=40 tau*p=4.00 log10(Markov)=-11.30 <= -9.00: True; after union -5.30 <= -3.00: True; net err True; 2N^-(D+1)<=N^-D True; card<=N^(A+1) True/True (A=6.0, card=1e+18)
N=10^6.000 tau=0.01 p=400 tau*p=4.00 log10(Markov)=-23.30 <= -18.00: True; after union -11.30 <= -6.00: True; net err True; 2N^-(D+1)<=N^-D True; card<=N^(A+1) True/True (A=6.0, card=1e+36)
N=10^6.000 tau=0.1 p=40 tau*p=4.00 log10(Markov)=-23.30 <= -18.00: True; after union -11.30 <= -6.00: True; net err True; 2N^-(D+1)<=N^-D True; card<=N^(A+1) True/True (A=6.0, card=1e+36)
N=10^6.322 tau=0.01 p=400 tau*p=4.00 log10(Markov)=-24.59 <= -18.96: True; after union -11.94 <= -6.32: True; net err True; 2N^-(D+1)<=N^-D True; card<=N^(A+1) True/True (A=6.0, card=8.51e+37)
N=10^6.322 tau=0.1 p=40 tau*p=4.00 log10(Markov)=-24.59 <= -18.96: True; after union -11.94 <= -6.32: True; net err True; 2N^-(D+1)<=N^-D True; card<=N^(A+1) True/True (A=6.0, card=8.51e+37)
ALL OK: True
tau=0.01: tau*p-(D+Ccard)=1.000 (>=1 required), threshold N0 >= C0^(1/slack)=5.000
tau=0.1: tau*p-(D+Ccard)=1.000 (>=1 required), threshold N0 >= C0^(1/slack)=5.000
net: N=10^3 tau=0.01 p=900 slack=1.000; N^(A+1)*C0*N^(-tau p)=10^-5.30 <= N^-D=10^-3.00: True
net: N=10^3 tau=0.1 p=90 slack=1.000; N^(A+1)*C0*N^(-tau p)=10^-5.30 <= N^-D=10^-3.00: True
net: N=10^6 tau=0.01 p=900 slack=1.000; N^(A+1)*C0*N^(-tau p)=10^-11.30 <= N^-D=10^-6.00: True
net: N=10^6 tau=0.1 p=90 slack=1.000; N^(A+1)*C0*N^(-tau p)=10^-11.30 <= N^-D=10^-6.00: True
```
Finding F1 evidence: `git -C ../RBM2D --no-optional-locks grep -n "StochDomAt" c9a24cf -- RBM2D/Defs/StochDom.lean`
```
RBM2D/Defs/StochDom.lean:26:`StochDomAt.of_unifDetDom_L_scale` uses the admissible sizes `N(L) = W(L)² L²`.
RBM2D/Defs/StochDom.lean:103:def StochDomAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop :=
RBM2D/Defs/StochDom.lean:327:namespace StochDomAt
RBM2D/Defs/StochDom.lean:337:    StochDomAt P (fun l => W l ^ 2 * l ^ 2)
RBM2D/Defs/StochDom.lean:359:end StochDomAt
RBM2D/Defs/StochDom.lean:602:    StochDomAt P (U := fun _ => Unit) (fun l => 2 ^ 2 * l ^ 2)
RBM2D/Defs/StochDom.lean:604:  apply StochDomAt.of_unifDetDom_L_scale (W := fun _ => 2)
```
**Verdicts.**
- Target 1 (pinned probe text, items of section 7 without `LocalLawPT`): PASS (every statement has its exponent/arith closed above; `N ≥ 1` from `Sizes`).
- Target 2, `Defs/StochDomAt.lean` (`PerTime` port; `StochDomAt` calculus): PASS, with F1 (the calculus is new work from the index-scale proof, needs `Tendsto size atTop atTop`; statements must carry it).
- Target 2, `Gauss/DominationAt.lean` (`*At` Domination, MomentBridge, Envelope, SteinMatrix): PASS, with F2, F3.
Overall: PASS.

## (b) Script output — Sat Oct  3 02:00:37 UTC 2026
```
$ date -u
Sat Oct  3 01:59:09 UTC 2026
$ git log --oneline -1; git rev-list --count main..t/T2012
7d75f54 T2012: module doc of DominationAt (Envelope note)
9
$ lake build RBM3D.Defs.StochDomAt RBM3D.Gauss.DominationAt 2>&1 | grep -v "^trace" | tail -3
Build completed successfully (3248 jobs).
$ grep -nE "axiom audit:|premises found|Build completed" /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/fullbuild.txt
8:info: RBM3D.lean:55:0: axiom audit: 829 theorems, 305 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
27:premises found by scanning: 14 (borrowed 5, owed 1, structural 8).
41:Build completed successfully (3693 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Defs/StochDomAt.lean RBM3D/Gauss/DominationAt.lean
RBM3D/Defs/StochDomAt.lean:0
RBM3D/Gauss/DominationAt.lean:0
$ git diff main...t/T2012 --stat
 RBM3D/Defs/StochDomAt.lean    | 997 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Gauss/DominationAt.lean | 849 +++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   2 +
 3 files changed, 1848 insertions(+)
$ git diff main -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.NormStochDomAt,       -- notation of `(stoch_domination)` at scale `N`
+   `RBM.Path.PerTimeDomAt,    -- notation of `(stoch_domination)` at scale `N`

## axioms of every public declaration of the two modules (117 theorems and defs)
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/axioms_t2012.lean > /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/decls_axioms.txt; python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/axgroups.py
axioms [propext, Classical.choice, Quot.sound]: 116 declarations
axioms [propext, Quot.sound]: 1 declarations: G.Sizes.one_le_size
TOTAL 117 declarations; with an axiom outside [propext, Classical.choice, Quot.sound]: 0; axioms used overall: [Quot.sound, Classical.choice, propext]

## item 1: the pinned block against the probe
$ /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/pinned_diff.sh
file lines 43-174 (132 lines); probe lines 795-881 + 891-935 (132 lines)
diff exit code: 0
occurrences of `def LocalLawPT` in the file: 0

## pinned statements, extracted from RBM3D/Defs/StochDomAt.lean
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/stmts.py S badSetAt StochDomAt stochDom_iff_at_id HighProbAt highProb_iff_at_id TimeIcc PerTimeDomAt Prec PrecPT Whp one_le_size prec_of_le precPT_of_le Prec.whp
def badSetAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) (τ : ℝ) (l : ℕ) : Set Ω := {ω | ∃ u, (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω}
def StochDomAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop := ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, P (badSetAt size ξ ζ τ l) ≤ ENNRe...
theorem stochDom_iff_at_id (ξ ζ : ∀ N, U N → Ω → ℝ) : StochDom P ξ ζ ↔ StochDomAt P id ξ ζ
def HighProbAt (P : Measure Ω) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω) : Prop := ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, P (Ξ l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^...
theorem highProb_iff_at_id (P : Measure Ω) (Ξ : ℕ → Set Ω) : HighProb P Ξ ↔ HighProbAt P id Ξ
abbrev TimeIcc (s t : ℕ → ℝ) (n : ℕ) : Type := ↥(Set.Icc (s n) (t n))
def PerTimeDomAt (P : Measure Ω) (size : ℕ → ℕ) {U : ℕ → Type*} (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop := ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop,...
def Prec (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := StochDomAt (seqP sz) sz.size ξ ζ
def PrecPT (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := Path.PerTimeDomAt (seqP sz) sz.size ξ ζ
def Whp (Ξ : ℕ → Set (SeqΩ sz)) : Prop := HighProbAt (seqP sz) sz.size Ξ
theorem one_le_size (n : ℕ) : 1 ≤ sz.size n
theorem prec_of_le {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : sz.Prec ξ ζ
theorem precPT_of_le {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : sz.PrecPT ξ ζ
theorem Prec.whp {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (h : sz.Prec ξ ζ) {τ : ℝ} (hτ : 0 < τ) : sz.Whp (fun n => {ω | ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ)...

## item 2: ported declarations, name->RBM3D line (RBM2D line at c9a24cf is the number after the colon in the name)
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/portdiff.py
RBM2D/Path/PerTime.lean -> Defs/StochDomAt.lean, whole text: 6/6 SAME
  PerTimeOfStochDomAt:55->189 perTimeOfStochDomAt:60->195 rpow_mul_rpow_neg_add_of_nonneg:68->204
  perTimeDomAt_iff_forall_section:77->213 stochDomAt_of_perTimeDomAt:112->249 highProbAt_iInter:141->279
RBM2D/Gauss/Domination.lean -> Gauss/DominationAt.lean, whole text: 5/5 SAME
  MomentDomAt:162->66 stochDomAt_of_momentDomAt:171->75 highProbAt_univ:467->160
  stochDomAt_Icc_of_holder_on_good:474->167 momentDomAt_constant_one_example:649->295
RBM2D/Gauss/MomentBridge.lean -> Gauss/DominationAt.lean, whole text: 2/2 SAME
  integrable_abs_evenPow_of_envelope:29->314 momentDomAt_of_stochDomAt:170->328
RBM2D/Gauss/SteinMatrix.lean -> Gauss/DominationAt.lean, whole text, after the update->upd renames: 5/5 SAME
  law_pi:83->509 map_update:91->517 stein:134->559 law:32->500 Sample:29->497
RBM2D/Defs/StochDom.lean:460-554 -> Defs/StochDomAt.lean, whole text: 2/2 SAME
  two_mul_le_mul_self:478->643 le_rpow_mul_of_le_add_rpow_neg:486->651
RBM2D/Defs/StochDom.lean StochDom.* (index scale) -> StochDomAt.*, statement, N:=size l, +hsize: 13/14 SAME
  of_subset:132->325 precomp_param:141->335 of_le_left:152->347 of_subset_union:159->355 of_eventually_empty:176->376
  refl:192->400 trans:202->411 add:215->427 mul:225->439 const_mul_left:243->462 const_mul_right:259->483
  of_forall_le:279->507 highProb:318->534 of_unifDetDom:183->387
  NOT SAME: of_unifDetDom:183 DIFF: +(hl +: +∀ᶠ +l +: +ℕ +in +atTop, +l +≤ +size +l) +(hg +: +∀ +l +u, +0 +≤ +g +l +u)
RBM2D/Defs/StochDom.lean HighProb.*, Absorb (index scale) -> HighProbAt.*, StochDomAt.*, statement: 7/7 SAME
  mono:366->564 inter:373->571 biInter:388->589 nonempty:411->613 HighProb.of_eventually_univ:467->599
  StochDom.of_add_le:504->669 StochDom.of_highProb_add_rpow_neg:535->697
SAME: 40 DIFF: 1 NOT FOUND: 0

## instances (nonempty, at sz0 on seqP sz0): coverage and the required three, extracted from the files
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/cover.py
public theorems outside the instance namespaces: 46 ; each referenced by a theorem/example of the instance sections: 46 ; not referenced: []
instance declarations in the two files: theorems 52 examples 10 ; targets -> instances:
   Gauss.Sizes.prec_of_le -> prec_Xi_Ze, prec_Ze_Ch, stochDomAt_of_add_le
   StochDomAt.trans -> stochDomAt_Xi_Ch
   stochDom_iff_at_id -> stochDomAt_id_Ze, stochDom_Ze
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/stmts.py S obs Xi Ze Ch stochDomAt_id_Ze prec_Xi_Ze stochDomAt_Xi_Ch obs_nonconst
def obs (n : ℕ) (ω : SeqΩ sz0) : ℝ := |Real.sin (ω ⟨n, ((0 : Idx 3 (sz0.L n) (sz0.W n)), (0 : Idx 3 (sz0.L n) (sz0.W n)), true)⟩)|
def Xi (n : ℕ) (_ : Unit) (ω : SeqΩ sz0) : ℝ := obs n ω
def Ze (n : ℕ) (_ : Unit) (ω : SeqΩ sz0) : ℝ := 1 + obs n ω
def Ch (n : ℕ) (_ : Unit) (ω : SeqΩ sz0) : ℝ := 2 + obs n ω
theorem stochDomAt_id_Ze : StochDomAt (seqP sz0) id Ze Ze
theorem prec_Xi_Ze : sz0.Prec Xi Ze
theorem stochDomAt_Xi_Ch : StochDomAt (seqP sz0) sz0.size Xi Ch
theorem obs_nonconst (n : ℕ) : ∃ ω ω' : SeqΩ sz0, obs n ω ≠ obs n ω'
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/stmts.py D stochDomAt_obs_of_moment momentDomAt_obs_of_dom stochDomAt_Icc_Yt stein_sin_seqP gvar_c0_pos
theorem stochDomAt_obs_of_moment : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) (fun n _ ω => obs n ω) (fun _ _ _ => (1 : ℝ))
theorem momentDomAt_obs_of_dom : MomentDomAt (seqP sz0) sz0.size (U := fun _ => Unit) (fun n _ ω => obs n ω) (fun _ _ => (1 : ℝ))
theorem stochDomAt_Icc_Yt : StochDomAt (seqP sz0) sz0.size (U := fun _ => ↥(Set.Icc (0 : ℝ) 1)) (fun n u ω => Yt n (u : ℝ) ω) (fun _ _ _ => (1 : ℝ))
theorem stein_sin_seqP : ∫ ω, ω c0 • (↑(Real.sin (ω c0)) : ℂ) ∂(seqP sz0) = (seqGvar sz0 c0 : ℝ) • ∫ ω, (↑(Real.cos (ω c0)) : ℂ) ∂(seqP sz0)
theorem gvar_c0_pos : 0 < (seqGvar sz0 c0 : ℝ)
$ grep -n "theorem sz0_values" -A1 RBM3D/Defs/Sizes.lean
267:theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64 := by
268-  refine ⟨rfl, rfl, ?_, ?_⟩

## name clash
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/clash.lean
checked 117 new public names against `import RBM3D` (main at the branch point); clashes: []
$ git grep -lE "StochDomAt|HighProbAt|PerTimeDomAt|MomentDomAt|badSetAt|NormStochDomAt" c950f27 -- RBM3D RBM3D.lean; echo "exit=$?"
exit=1

## RBM2D movement of the ported files since c9a24cf (read-only)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format='RBM2D HEAD %h'; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Defs/StochDom.lean RBM2D/Path/PerTime.lean RBM2D/Gauss/Domination.lean RBM2D/Gauss/MomentBridge.lean RBM2D/Gauss/Envelope.lean RBM2D/Gauss/SteinMatrix.lean | tail -1
RBM2D HEAD 9e0f275
 6 files changed, 81 insertions(+), 1455 deletions(-)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Gauss/Envelope.lean | grep -cE 'size|StochDom|HighProb|MomentDom'; echo '(0 = no size-indexed or StochDom statement in RBM2D/Gauss/Envelope.lean at c9a24cf)'
0
(0 = no size-indexed or StochDom statement in RBM2D/Gauss/Envelope.lean at c9a24cf)

## Mathlib names (present / absent), file mathlib_names.lean
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/mathlib_names.lean
present 49; absent: [Measurable.measurable_abs, Measurable.abs]
```

### Narrative (script output above; facts only)
1. Delivered on `t/T2012` (HEAD 7d75f54, 9 commits over the merge-base c950f27; `git rev-parse --short main` is 13dbbc0 at the time of writing: T2011 added `RBM3D/Propagator/HeatBounds1D.lean`, namespace `RBM.Heat`, and one root import, so no name clash and no overlap with my files): `RBM3D/Defs/StochDomAt.lean` (997 lines), `RBM3D/Gauss/DominationAt.lean` (849 lines), two lines in `RBM3D/Test/Axioms.lean`. `git diff main...t/T2012 --stat` lists only these three files.
2. Full build: the worktree's `RBM3D.lean` got `import RBM3D.Defs.StochDomAt` and `import RBM3D.Gauss.DominationAt` after `import RBM3D.Loop.KLTree` (copy saved, file restored afterwards, never committed; `git status --short` clean), then `lake build` (started 01:57:30 UTC by `date -u`), exit 0, `#assert_rbm_axioms` passed (829 theorems, 0 axioms). The hub adds the two imports at merge.
3. Item 1: lines 43-174 of `StochDomAt.lean` equal probe lines 795-881 and 891-935 at `5d2a4a8` (diff exit code 0); `LocalLawPT` (882-890) is absent as ticketed. No proof needed a change on current `main`.
4. Item 2, verbatim ports (script: whole text SAME): 6 declarations of `Path/PerTime.lean`, 5 of `Gauss/Domination.lean`, 2 of `Gauss/MomentBridge.lean`, 5 of `Gauss/SteinMatrix.lean` (merged `upd`, `upd_self`, `upd_of_ne`, `measurable_upd`, `integral_mul_gaussianReal_complex'` stand in for RBM2D's `update*`, `integral_mul_gaussianReal_complex_all`; the rename is applied before the comparison), 2 arithmetic lemmas of the `Absorb` section.
5. Finding F1 of section (a) holds: `RBM2D/Defs/StochDom.lean` has no `size`-indexed calculus (the grep in (a) shows only the definition `StochDomAt` at `:103` and `of_unifDetDom_L_scale` at `:334`, scale `W² l²`). The 21 calculus statements are RBM2D's index-scale statements with `N := size l` and `StochDom P := StochDomAt P size`; 20 of 21 are identical after that substitution (script); the proofs are the index-scale proofs with `N := size l`.
6. The one non-identical statement is `StochDomAt.of_unifDetDom`: it takes `UnifDetDom` at the index scale `l`, `0 ≤ g`, and `∀ᶠ l, l ≤ size l` (the scale-change hypothesis; the `d = 2` analogue is `of_unifDetDom_L_scale`).
7. `hsize : Tendsto size atTop atTop` is carried by `of_subset_union`, `refl`, `trans`, `add`, `mul`, `const_mul_left`, `const_mul_right`, `of_forall_le`, `HighProbAt.inter`, `HighProbAt.nonempty`, `of_add_le`, `of_highProbAt_add_rpow_neg`, and by `stochDomAt_of_momentDomAt`, `stochDomAt_Icc_of_holder_on_good`, `momentDomAt_of_stochDomAt` (as in RBM2D, F2) and the two new `momentDomAt_of_..` variants. For `sz : Sizes d` it is `Sizes.tendsto_size sz h` from `SizeTendsto` (signed D20). `of_subset`, `precomp_param`, `of_le_left`, `of_eventually_empty`, `highProb`, `HighProbAt.mono`, `biInter`, `of_eventually_univ` and every pinned theorem need none.
8. New names with no RBM2D source: `NormStochDomAt`, `normStochDom_iff_at_id`, `HighProbAt.biInter` (alias of `Path.highProbAt_iInter`), `momentDomAt_of_stochDomAt_of_nonneg`, `momentDomAt_of_normStochDomAt` (scale versions of the merged index-scale bridges), `Sizes.tendsto_size`, `Sizes.seqP_eq_law` (`rfl`: `seqP sz` is `GaussianProduct.law (seqGvar sz)`), and the instance namespaces `StochDomAtInst`, `DominationAtInst`.
9. Not ported: `RBM2D/Gauss/Envelope.lean` has no `size`-indexed or `StochDom` statement at `c9a24cf` (grep count 0 above), so "the sequence-level part of Envelope.lean" is empty and the at-scale reverse bridge is `MomentBridge.lean:170`; `momentDom_green_of_stochDom` (`MomentBridge.lean:325`) needs `green` and `norm_green_le`, which `main` does not have; index-scale items already on `main` were not re-declared.
10. Instances (section 10 of `StochDomAt.lean`, last section of `DominationAt.lean`): all at `sz0` (`d = 3`, `N_0 = 2097152`), on `seqP sz0`, with the nonconstant observable `obs` (`obs_nonconst`) and a positive-variance coordinate (`gvar_c0_pos`); the three required instances are `stochDomAt_id_Ze` and `stochDom_Ze` (`stochDom_iff_at_id`), `prec_Xi_Ze` (`prec_of_le`), `stochDomAt_Xi_Ch` (`StochDomAt.trans`). The coverage script finds each of the 46 public non-instance theorems used by an instance theorem or `example` (52 theorems, 10 examples). Inputs: `sz0_tendsto`, `sz0_self_le_size`, the bound `0 ≤ obs ≤ 1`; no unproved pin, no external input.
11. Axiom registry (DECISIONS §16): the audit scan reported `RBM.NormStochDomAt` and `RBM.Path.PerTimeDomAt` as unclassified premises; exactly those two lines are in `structuralProps`. The instances that conclude these two predicates are `example`s, because a named theorem concluding a predicate counts as its proof in the scan.
12. Section (a) needed no correction (no (a′)): F1 is the grep in (a); F2 and F3 are the lines in the port table (`:171`, `:474`, `:170`; `HighProbAt` is the pinned definition, never re-declared).

## (c) Verified Mathlib names (present in this environment, each used in the two files)
`tendsto_natCast_atTop_iff` (root namespace) · `Real.abs_sin_le_one` · `Real.abs_cos_le_one` · `Real.continuous_sin` · `Real.continuous_cos`
`continuous_abs` · `Measurable.const_mul` · `Measurable.pow_const` · `measurable_pi_apply` · `MeasureTheory.integral_mono_of_nonneg`
`MeasureTheory.integrable_const` · `MeasureTheory.Integrable.mono'` · `MeasureTheory.ae_of_all` · `pow_le_one₀` · `mul_le_of_le_one_right`
`Complex.continuous_ofReal` · `Real.hasDerivAt_sin` · `HasDerivAt.ofReal_comp` · `Complex.norm_real` · `Complex.real_smul`
`Real.rpow_lt_one_of_one_lt_of_neg` · `Real.rpow_add'` · `Real.one_le_rpow` · `Real.rpow_le_rpow_of_exponent_le` · `Real.div_rpow` · `Real.rpow_natCast` · `Real.rpow_neg`
`inv_lt_one_iff₀` · `Fintype.card_eq_zero_iff` · `Set.nonempty_iff_ne_empty` · `ENNReal.ofReal_lt_one` · `ENNReal.ofReal_mul` · `ENNReal.ofReal_add`
`MeasureTheory.measure_iUnion_fintype_le` · `MeasureTheory.Measure.eq_infinitePi` · `MeasureTheory.Measure.infinitePi_pi` · `MeasureTheory.Measure.infinitePi` · `MeasureTheory.Measure.map_apply`
`MeasureTheory.integral_mono` · `MeasureTheory.integral_indicator_const` · `MeasureTheory.integral_prod` · `MeasureTheory.integral_map`
Verified absent (script above): `Measurable.abs`, `Measurable.measurable_abs` (use `continuous_abs.measurable.comp`); `Filter.tendsto_natCast_atTop_iff` (the name is the root-level one).

## (d) Open issues and paper-delta candidates
* Paper-delta candidate **T2012a**: `StochDomAt`, `HighProbAt`, `PerTimeDomAt`, `MomentDomAt` are stated for an arbitrary measure `P` and real-valued families, with no sign condition in the definition; the paper's `≺` (`1_2:227-231`) is for non-negative variables on a probability space. Sign and finiteness enter only where used (`refl`, `mul`, `const_mul_*` need `0 ≤ ζ`; the moment bridges need `IsFiniteMeasure P`). Same convention as the merged `StochDom`.
* Paper-delta candidate **T2012b**: `StochDomAt.of_unifDetDom` converts a deterministic `UnifDetDom` at the index scale `l` into the scale `size l` under `l ≤ size l` eventually; the paper's (ii) ⇒ (i) is at one `N`. API only, no paper counterpart.
* Already signed, cited and not re-proposed: D20 (`N → ∞`, here `hsize`), D21 (per-time `≺`, union outside `P`), D23 (`W^τ` written `N^τ`).
* Portmap observation: the row `Gauss/Envelope` (E.2 and part C) names a "sequence-level part" that does not exist at `c9a24cf` (item 9); the deterministic resolvent envelope (`norm_green_le`, derivative bounds) of that file is not on `main` and is not needed by this ticket's targets.
* Not ported, available to MD-4 or later: at-scale deterministic-modulus time net (`stochDomAt_Icc_of_holder`, `_of_lipschitz`; no RBM2D at-scale source), `HighProbInAt`, `momentDom_green_of_stochDom`.
* Root imports for the hub: `import RBM3D.Defs.StochDomAt`, `import RBM3D.Gauss.DominationAt` after the last `import` line of `RBM3D.lean`.
