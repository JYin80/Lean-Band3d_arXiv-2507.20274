Auditor model: claude-opus-5-5
# T2192 audit (round 1): MA-D1 endpoint freeze (design, report only)
Audit time: Mon Oct  5 18:15:41 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2192-audit1`, detached at `t/T2192` = `97d958e`, base `76b840e`.

## 1. Scope and build
```
$ git diff --name-only main...t/T2192
RBM3D/Probe/T2192Pins.lean
$ lake build RBM3D.Probe.T2192Pins
✔ [3996/3996] Built RBM3D.Probe.T2192Pins (9.5s)
Build completed successfully (3996 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^ *axiom |_root_" RBM3D/Probe/T2192Pins.lean
(no output)
$ grep -nE "^namespace|^end RBM|^end Inst" RBM3D/Probe/T2192Pins.lean
46:namespace RBM.Probe.T2192
2112:namespace Inst
2490:end Inst
2492:end RBM.Probe.T2192
```
Only the sole writable probe file is touched (the prove report and the optional `docs/reports/T2192-portmap.md` live in the main worktree, the portmap untracked). No frozen signature, no `RBM3D.lean`. Every declaration sits in `RBM.Probe.T2192`.

Axioms (auditor's own file `Ax.lean`, `import RBM3D.Probe.T2192Pins`, 51 `#print axioms`: the 4 pins, `BUniv`, every proved chain theorem, both bridges, `band_endpoints_of_pins`, `final_shape`, and 21 instance/extreme-input theorems):
```
$ lake env lean Ax.lean > ax.out; echo exit=$?
exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
51
$ grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
(no output)
```

## 2. Statements against the paper (`1_2:357-511`), `T2001_*`, the UN consumers
Paper metric `1_2:274-275`: `|x-y| ≡ ‖[x-y]_{WL}‖_∞`, `|a-b| ≡ ‖[a-b]_L‖_∞` (both L^∞).

| pin | paper | Lean (probe line) | check |
|---|---|---|---|
| `decol` | Thm 2.1: `d≥3`, `W≥N^𝔠`, `(eq:WO)`; ∀κ,τ small, D large; P(max_{|λ_k|≤2-κ}‖ψ_k‖²_∞ ≤ N^{-1+τ}) ≥ 1-N^{-D}, N large | `:164`: `(d,3≤d)(𝔠,𝔡)(sz, Admissible)(κ,τ,D>0) ∀ᶠ n`, P(decolBad) ≤ N^{-D}; `decolBad` = some orthonormal eigenbasis fails (T2001h) | match (T2001a sequence form, T2001h) |
| `locSC` | Thm 2.2: (G_bound), (G_bound_ave), ∩_z inside, `|G-M|² ≤ W^τ 𝓑_{η,|x-y|}`, `|W^{-d}Σ_{[a]}G_xx - m| ≤ W^τ 𝓑_{η,0}` | `:171`, events `locBad1/2` `:135-140`; `𝓑 = calB` `:57` (body = `(eq:calBetaK)`); `|x-y|` read as `distB = W·|[x]-[y]|_∞` `:66`; `M = msc·I` `:70` | match, block reading (T2001e, metric changed ℓ¹→L^∞, candidate `T2192b`) |
| `QUE` | Thm 2.3: `ε₀∈(0,𝔡/2)`, `0<c<ε₀∧𝔡/5`, ∀τ; sup_E max_a P(...≥W^{d-c}/N) ≤ W^{-(2ε₀)∧(2𝔡/5)+2c+τ}; (Meq:QUE2) ∀A | `:181`: same constants and order; merged `queWindow`/`queBadMat`/`queBound` (`Universality/Pins.lean:380-392`); `que2BadMat` `:153` (`≥ W^{d-c}|A|/N`); `A.Nonempty` | match (T2001f) |
| `QDiff` | Thm 2.5: (eq:diffu1,2) with ∩_z, bound `W^τ[(𝓑_{η,0})^{1/5}𝓑_{η,W|a-b|} ∧ 𝓑²_{η,0}]`; (Meq:QdS1,2) "for each z ∈ 𝐃, N large" | `:196`: `qdBound` `:95`, `qdBoundExp` `:100` term by term as paper; profiles `|m|²Θ^{(+,-)}/W^d`, `m²Θ^{(+,+)}/W^d` `:87-92`; `a,b` inside P; expectation half `∀ᶠ n ∀ z ∈ 𝐃` | match; stronger readings documented (`T2192a` uniform N₀, `T2192d` a,b inside) |
| `BUniv` | Thm 2.4 | `abbrev BUniv := UNBUniv` `:208` | not re-pinned (as ticket) |
| Thm 2.7 | BA | referenced by BA names (portmap P.7 rows 42-48), `Thm27 : Prop` hypothesis of `final_shape` | as ticket target 4 |

Script diff against the T2001 copy (only vocabulary changes; quantifier order and every exponent unchanged):
```
$ diff -w <(T2001_QUE body, bd95cc9:…T2001Endpoints.lean:195-206) <(QUE body, :181-190)
2,3c2,3
<   ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, 0 < 𝔠 → 0 < 𝔡 → ∀ s : SizeSeq, Admissible d 𝔠 𝔡 s →
<     ∀ κ : ℝ, 0 < κ → ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
---
>   ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
>     ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
5,12c5,10   (Pn/QueBad/Que2Bad/Hmat/s.g → Sizes.seqP/queBadMat/que2BadMat/seqXmat/sz.lam; bounds identical)
```
(`0<𝔠, 0<𝔡` moved into the merged `Sizes.Admissible`, `Defs/Sizes.lean:177`: `0<𝔠 ∧ 0<𝔡 ∧ SizeTendsto ∧ Bandwidth ∧ WO`.) `T2001_decol/locSC/QDiff` (`:128,158,297`) have the same binder sequence `(d)(𝔠 𝔡)(sz)(κ ε τ D) ∀ᶠ n`.

UN consumers, by compiled bridges (the statement-level diff is the type check):
```
locSC_to_UNLocAvgBand : locSC → UNLocAvgBand   (:2055; rewrite calB … 0 = Bctl n (1-η) under the binder, calB_zero_eq_Bctl :230)
QUE_to_UNQueBand      : QUE → UNQueBand        (:2066; projection `.1`)
```
Both on the three standard axioms (above). `UNLocAvgBand` (`Universality/Pins.lean:416`) has threshold `W^τ·Bctl n (1-Im z)`, `∩_z` inside, `N^{-D}`: identical to `locSC`'s second conjunct after `calB_zero_eq_Bctl`.

## 3. Hidden hypotheses, vacuity, cycles
- Pins are plain `def … : Prop` over merged vocabulary; no structure fields carry hypotheses. Chain pins are implications (`MANetLoc := locSCFixed → locSC`, `MANetQD := QDiffFixed → QDiff`, `MAQUE := QDiff → QUE`, `MADecol := locSC → decol`, `MAFixed := (∀ d, UNMLOut d) → locSCFixed ∧ QDiffFixed`); `MADecol`, `MAFixed` and `thetaDiff` are **proved** (`decol_of_locSC` `:1845`, `fixed_of_ML` `:1594`, `thetaDiff` `:706`).
- `band_endpoints_of_pins (hML : ∀ d, UNMLOut d) (hNL : MANetLoc) (hNQ : MANetQD) (hQ : MAQUE)`; `final_shape` adds the nine UN rows, `UNGUELocal`, `UNGreenCorrAll`, `Thm27`/`hBA`, and `UNL32` as premise. No cycle: no premise mentions a conclusion; `UNMLOut` (owed, ST-6) and `UNL32` (borrowed, limit check `un_L32_arith`, merged with instance, T2162) are merged pins.
- Extreme inputs (lesson 25), compiled: `domain_extreme` (`κ=2, ε=1` nonempty; `κ=3`, `ε=2` empty), `locBad1_empty_kappa`, `im_mE_edge`, `queDomain_edge` (`E=±19/10`), `que2BadMat_univ` (A = univ: event empty), `que2BadMat_empty_zero` (A = ∅ fires at the zero matrix: why `A ≠ ∅`), `(eq:WO)` edges `szLo` (`ilambda = W^{-3/2+1/5}`), `szUp` (`ilambda = 5 = 𝔡⁻¹`) with `szLo_admissible`, `szUp_admissible`, `inst_locSC_lo/up`, `inst_QUE_up`.

## 4. Compiled nonempty instances (d = 3, `sz0`: n=0 gives L=4, W=32, N=2097152, ilambda=1/64; `sz0_admissible (1/6) (1/10)`)
| endpoint / theorem | instance | data |
|---|---|---|
| `decol` | `Inst.inst_decol (h : decol)` `:2128` | κ=τ=1/10, D=1 |
| `locSC` | `inst_locSC (h : locSC)` `:2134` | κ=1/10, ε=1/20, τ=1/10, D=2 |
| `QUE` | `inst_QUE (h : QUE)` `:2142` | κ=1/10, ε₀=1/30<1/20, c=1/60<min(1/30,1/50), τ=1/10 |
| `QDiff` | `inst_QDiff (h : QDiff)` `:2154` | as locSC |
| `BUniv` | `inst_BUniv (h : BUniv)` `:2167` | merged `bump`, `bump_testFun` |
| bridges | `inst_bridge_loc`, `inst_bridge_que` `:2175,2185` | as above |
| `decol_of_locSC` | `inst_decol_of_locSC (h : locSC)` `:2207` | proved deduction applied |
| `fixed_of_ML` | `inst_locSCFixed`, `inst_QDiffFixed (hML : ∀ d, UNMLOut d)` `:2215,2224` | proved from UNMLOut |
| transfer, (eq:BtBt) | `inst_zRange`, `inst_btBt`, `inst_zLocal`, `inst_zAve`, `inst_zTrace`, `inst_zProfile` | `zI = 1/2 + i N^{-4/5}` ∈ 𝐃_{1/10,1/10} (`sz0_locDomain`) |
| `thetaDiff` | `inst_thetaDiff` | L=4, g=1/64, z=zI |
| `final_shape` | `inst_final_shape` `:2194` | all premises hypotheses (other gates' pins) |
Every deterministic hypothesis (`3 ≤ d`, `Admissible`, positivity, `ε₀,c` ranges, domain membership) is discharged by `norm_num`/merged lemmas; the remaining hypotheses are the endpoint pins themselves or `UNMLOut`/UN rows/`UNL32`, which are other gates' pins. No `N=0`, empty index, collapsed window or `False` premise.

## 5. Coverage (target 6), independent re-run
```
$ sed -n 250,669p paper/tex/1_2_Intro_model_result.tex | sed 's/%.*//' | grep -o '\\label{[^}]*}' | sort -u | wc -l
43
$ for l in labels: grep -qF "$l" <portmap P.7> || echo MISSING $l
(no output)
```
Thm 2.7 bullets mapped to `BAThm27`, `BAEnd_locSC`, `BAEnd_QUE`/`BAEnd_QUEL`, `BAEnd_BUniv`/`BAEnd_BUnivL`, `BAEnd_QDiff` (branch text `t/T2161`, `t/T2173`; not on `main`: `grep -rn "BAThm27\|BAEnd_QUEL" RBM3D` empty, as the ticket states).

## 6. Split count and paper deltas
Split at the top of the prove report: 6 tickets (MA-01…MA-06), total central 4940 lines, below every threshold of §9 O2 (25/40/50). Paper-delta candidates proposed (prove report (d)): `T2192a` (QdS N₀ uniform over 𝐃), `T2192b` (L^∞ block distance), `T2192c` (`(eq:ukx)` with `η = N^{-1+min(τ/2,1/2)}`), `T2192d` (a,b inside P), `T2192e` (form decision, `Prec` ≡ explicit: `explicit_of_stochDomAt`, `prec_of_explicit` compiled), `T2192f` (empty domain only for κ>2 or ε>1), `T2192g` (loop indices `(b,a)` in `zTrace`). Every Lean/paper difference found in §2 above (sequence form, ∩_z inside, A ≠ ∅, any eigenbasis: signed T2001a/b/f/h; L^∞ block reading; uniform N₀; a,b inside) is covered.

## 7. Verdicts
| target | verdict |
|---|---|
| 1 endpoint pins + form decision | PASS |
| 2 assembly chain (a)-(e) | PASS (MA-04 nets and MA-05 `MAQUE` are pins by design, priced in the split) |
| 3 interfaces (bridges, consumer table) | PASS |
| 4 exponent table, skeleton, instances, extreme inputs | PASS |
| 5 split and count | PASS |
| 6 coverage | PASS |

## 8. Observations (no RETURN)
1. `T2192b` changes the T2001e reading (DECISIONS §10: block ℓ¹) to block L^∞. This follows the paper's metric (`1_2:274-275`) and the merged `STLocalEntry`; the two are equivalent up to `d^{d-2}` (`calB_distB_compare`, compiled) absorbed by `W^τ`. The dispatcher should record it as an amendment to T2001e when numbering the delta.
2. The comparison with the literal fine distance `|x-y|` (`K + W ≤ 2(Wk + W)`, factor `2^{d-2}`) is not compiled (prove report (d) open item 3). The comparison is elementary, so MA-01 can take it.
3. `MAThetaDiff` states `∃ C` (CLAUDE.md §7 asks for hard-coded constants). It is a chain lemma, not an endpoint; the constant comes from merged `prop5to8_holds`.
4. The net constants (preflight row 6) are numeric only, as the report says; MA-04 (`prover-max`) owns them.
