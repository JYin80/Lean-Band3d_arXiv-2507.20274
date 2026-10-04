Auditor model: claude-opus-5-5

# T2141 audit (round 1) — Sun Oct  4 17:33:18 UTC 2026

Ticket `docs/tickets/T2141.md` (V1 + Amend 1). Branch `t/T2141` at f13a06b; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2141-audit1` (detached). Targets (Amend 1): pin `STFarEntryAtLog`, theorem `stFarEntryAtLog`, section lemma `prec_timeIcc_section`.

## 1. Diff scope
```
$ git diff --name-status main...t/T2141
A	RBM3D/Evolution/FarEntry.lean
$ git log --oneline main..t/T2141
f13a06b T2141: Evolution/FarEntry (STFarEntryAtLog, stFarEntryAtLog, prec_timeIcc_section; instance on Step5Inst.szCL)
```
Only the sole writable file `RBM3D/Evolution/FarEntry.lean` (new); `Test/Axioms.lean` untouched (no registry line expected). No merged file changed, so no frozen signature touched. Imports: `Induction/{Step5Pins,Step34Pins,KDecay}`, `Green/{Pins,GbEXP}`, `Path/KellStar` (not `RBM3D`; `Step5Pins` is needed for `szCL`).

## 2. Statement: pin vs Amend 1 (script diff)
Script: extract the `U`, the integrand and the bound from Amend 1's pin text and from the body of `def STFarEntryAtLog`; normalise whitespace; compare.
```
0 MATCH
1 MATCH
2 MATCH
$ sed -n 673,680p RBM3D/Evolution/FarEntry.lean
def STFarEntryAtLog (sz : Sizes d) (E τ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' →
    sz.Prec (U := fun n => Bool × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖Gt sz n (E n) (τ n) p.1 ω p.2.1 p.2.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2) : ℕ) : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

```
Quantifiers `∀ c > 0, ∀ D' > 0` before `Prec` as in Amend 1; both charges (`Bool` in `U`); all fine-lattice pairs; block distance `zdistInf` of `STblk`; threshold `c (log W)^3 ℓ_τ`; bound `W^{-D'}`. **PASS.**

## 3. Statement: theorem and section lemma
```
$ sed -n 835,840p; sed -n 63,66p  RBM3D/Evolution/FarEntry.lean
theorem stFarEntryAtLog (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) {Cd : ℝ}
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd) :
    STFarEntryAtLog sz (STflowE z) τ := by
theorem prec_timeIcc_section {d : ℕ} (sz : Sizes d) {s t τ : ℕ → ℝ} (hsτ : ∀ n, s n ≤ τ n)
    (hτt : ∀ n, τ n ≤ t n) {V : ℕ → Type*} {ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) :
    sz.Prec (U := V) (fun n v ω => ξ n (⟨τ n, hsτ n, hτt n⟩, v) ω)
```
- `stFarEntryAtLog` vs ticket target 2: `3 ≤ d`, `STFlow sz κ ε 𝔠 𝔡 z`, `0 < κ`, `0 ≤ s`, `t ≤ lemT z`, `s ≤ τ ≤ t`, `STStep2Concl sz (STflowE z) s t Cd` (any `Cd`); conclusion `STFarEntryAtLog sz (STflowE z) τ` — as pinned. Differences: (+) `hε : 0 < ε`, required by the merged quantifier of `STGbEXPij` (`Induction/Defs.lean:315`: `∀ κ ε 𝔡, 0 < κ → 0 < ε → 0 < 𝔡 → …`), the paper's `ε > 0`; (−) `s < t` dropped (weaker hypothesis, stronger theorem). Both covered by candidate `T2141b`. Ticket explicitly allows "take only what the proof uses". **PASS.**
- `prec_timeIcc_section` vs target 3: a `Prec` over `TimeIcc s t n × V n` gives the `Prec` at `τ` with `s ≤ τ ≤ t`; public with docstring (S5-20 may use it). Name not on `main` (grep §6). **PASS.**

## 4. Hidden hypotheses, vacuity, cycles
```
$ grep -n "def STStep2Concl\|def STFlow " RBM3D/Induction/{Step34Pins,Defs}.lean
RBM3D/Induction/Defs.lean:286:def STFlow {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
RBM3D/Induction/Step34Pins.lean:221:def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  sz.Admissible 𝔠 𝔡 ∧ ∀ n, sz.locDomain κ ε n (z n)

def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STLocalEntryU sz E s t ∧ STAvgU sz E s t ∧ STGdecayW sz E s t Cd
```
- No new structure; hypotheses are the merged `STFlow` (admissibility + domain) and the Step 2 pin bundle `STStep2Concl` (another gate's pin, allowed as a hypothesis by the ticket). The proof uses only `hStep2.1` (`STLocalEntryU`) and `hStep2.2.2` (`STGdecayW`), via `prec_timeIcc_section` (lines 701–702).
- `(GijGEX)` is the proved `RBM.Green.stGbEXPij_of_v3 (RBM.Green.gbEXPV3 hd)` (line 699), `𝒦` decay is the merged `RBM.Path.kellStarEv` (line 714); both are merged theorems, not hypotheses. No dependency on T2141 itself or on any downstream S5-20 module (imports above). No external hypothesis added.
- Consumer: probe `7b2b789:RBM3D/Probe/T2134Pins.lean:427` `STCltIsoConcl` isolates at `10 (log W)^3 ℓ_s` with `zdistInf` on blocks; the pin with arbitrary `c > 0` at `τ = s` serves it.

## 5. Compiled nonempty instance
```
$ sed -n 904,905p; sed -n 924,936p RBM3D/Evolution/FarEntry.lean
theorem farEntry_szCL_far_nonempty (n : ℕ) : farEntry_FarNonempty szCL sCL 1 n := by
  refine farEntry_farNonempty_of szCL sCL 1 n (xCL n) 0 ?_
theorem farEntry_szCL_stFarEntryAtLog (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    STFarEntryAtLog szCL (STflowE zCL) sCL ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
  ⟨stFarEntryAtLog (by norm_num) szCL (κ := 1 / 10) (ε := 1 / 10) (by norm_num) (by norm_num)
    flow_zCL (fun _ => le_rfl) lemT_zCL (fun _ => le_rfl) (fun n => (szCL_hst n).le) hStep2,
   farEntry_szCL_far_nonempty⟩

/-- The section lemma `prec_timeIcc_section` applied on `szCL`: `STLocalEntryU` and `STGdecayW` of
`STStep2Concl` on `[s, t] = [0, 1 - L_n^{-2}]` restrict to the time sequence `τ = s ≡ 0`. -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) : True := by
  have _h1 := prec_timeIcc_section szCL (fun _ => le_rfl) (fun n => (szCL_hst n).le) hStep2.1
  have _h3 := prec_timeIcc_section szCL (fun _ => le_rfl) (fun n => (szCL_hst n).le)
    (hStep2.2.2 2 (by norm_num))
  trivial
$ #print sCL / tCL / #check szCL (lake env lean, audit worktree)
RBM.Gauss.Step5Inst.szCL : RBM.Gauss.Sizes 3
def RBM.Gauss.Step5Inst.sCL : ℕ → ℝ :=
fun x => 0
def RBM.Gauss.Step5Inst.tCL : ℕ → ℝ :=
fun n => 1 - (↑(RBM.Gauss.Step5Inst.szCL.L n) ^ 2)⁻¹
```
- `stFarEntryAtLog`: applied at `d = 3` on the merged `Step5Inst.szCL` (`L_n = 2(n+24)^5`, `W_n = 2^{n+24}`), `κ = ε = 1/10`, `flow_zCL`, `s = τ ≡ 0`, `t = tCL = 1 - L_n^{-2}` (`lemT_zCL`, `szCL_hst`), `Cd = 1`. Every deterministic hypothesis discharged; only `STStep2Concl` stays (allowed). Far set nonempty at every `n` with `c = 1` (`farEntry_szCL_far_nonempty`: blocks `(xCL n, 0)`, `|xCL n|_∞ = (n+24)^5 ≥ (log W_n)^3`, `ℓ_s = 1`), so the indicator is not identically 0. Not degenerate. **PASS.**
- `prec_timeIcc_section`: `example` at lines 932–936 on `szCL` with `τ = s`, `hsτ`, `hτt` discharged, applied to `STLocalEntryU` and `STGdecayW` of the hypothesis. **PASS.**

## 6. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Evolution.FarEntry
✔ [3804/3804] Built RBM3D.Evolution.FarEntry (10s)
Build completed successfully (3804 jobs).
exit 0
$ grep -c "FarEntry.lean" build.log    # warnings/errors in the new file
0
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stFarEntryAtLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.prec_timeIcc_section' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.farEntry_szCL_stFarEntryAtLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.farEntry_szCL_far_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|^axiom|native_decide" RBM3D/Evolution/FarEntry.lean | wc -l
       0
$ for n in <public names>; do git grep -n "$n" main -- RBM3D | wc -l; done
prec_timeIcc_section:        0
STFarEntryAtLog:        0
stFarEntryAtLog:        0
farEntry_FarNonempty:        0
farEntry_farNonempty_of:        0
farEntry_szCL_far_nonempty:        0
farEntry_szCL_stFarEntryAtLog:        0
```
Build exit 0 (the other warnings in the log are in merged files). Axioms: only the three standard ones. Public names new on `main`; unpinned public helpers carry the `farEntry_` stem (§3 (E)).

## 7. Paper deltas
```
## (d) Open issues and paper-delta candidates
1. **T2141a** (log-scale threshold, `3_5:2245`): the far set is `{c (log W)³ ℓ_τ ≤ |[x]-[y]|_∞}` for every `c > 0` (consumer `STCltIsoConcl`: isolation `10 (log W)³ ℓ_s`), not RBM2D's `W^{τ'} ℓ_u`; the drafted pin follows by `W^{τ'} ≥ c (log W)³` eventually.  The paper omits the proof of `(eq:bound_isolated)` and cites [DYYY25, (7.39)] (`3_5:2245`).
2. **T2141b** (hypotheses): the theorem needs `0 < ε` (quantifier of `STGbEXPij`; the paper's `𝐃_{κ,ε}`, `ε > 0` small); `s < t` of the ticket is not needed.  The statement is for both charges and all pairs `(x,y)` of fine lattice points (RBM2D: `σ = +` only, the consumer transposes).
```
Lean/paper differences: log-scale threshold for every `c` (T2141a, as Amend 1 requests); `0 < ε` added, `s < t` dropped, both charges / all fine pairs (T2141b). All differences covered.

## 8. Observations (no verdict effect)
- The instance takes `Cd = 1` in `STStep2Concl`; `stFarEntryAtLog` is uniform in `Cd`, so any Step 2 constant fits; the instance's choice only fixes which Step 2 hypothesis it is conditional on.
- Prove report (a) row 9 and the `sz0` instance of (a)(ii) are superseded by Amend 1 (the file uses `szCL`, as Amend 1 requires).

## Verdict
- `STFarEntryAtLog` (pin): **PASS**. `stFarEntryAtLog`: **PASS**. `prec_timeIcc_section`: **PASS**.
- Ticket T2141: **PASS**. No dispatcher sign-off needed.
