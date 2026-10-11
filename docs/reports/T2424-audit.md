Auditor model: claude-opus-5-5

# T2424 audit (round 1) — BA-T T3-BA: `NewKLKGenHyp` at `baStep2Fam`, `STNewKLKgL'` and `STK2decaygL'` at BA

Written Sun Oct 11 12:56:30 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2424-audit1`, detached at `t/T2424` = `31a2210`; merge base with `main` = `631b8f4` (= `main`).

## 1. Diff, hygiene, name clash

```
$ git diff --name-only main...t/T2424
RBM3D/BA/NewKLKBA.lean
$ grep -nE "sorry|admit|native_decide|^axiom|mSigma|M = m I|maxHeartbeats" RBM3D/BA/NewKLKBA.lean; echo "grep exit=$?"
grep exit=1
$ grep -nE "^(theorem|lemma|def|abbrev|structure|instance)" RBM3D/BA/NewKLKBA.lean     (public declarations; line 734 is docstring text)
446:theorem baNewKLKGenHyp (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
560:theorem stNewKLKgL'_ba (d : ℕ) : STNewKLKgL' d (fun sz E => baStep2Fam sz E) :=
567:theorem stK2decaygL'_ba (d : ℕ) : STK2decaygL' d (fun sz E => baStep2Fam sz E) := by
$ grep -rnE "baNewKLKGenHyp|stNewKLKgL'_ba|stK2decaygL'_ba|NewKLKBA" RBM3D | grep -v "^RBM3D/BA/NewKLKBA.lean"
RBM3D/Chain/NewKLKGen.lean:30:  `stK2decaygL'_band` proves the primed `K^{(2)}` decay at the band (BAT-F2, T2414).
RBM3D/Chain/NewKLKGen.lean:749:theorem stK2decaygL'_band (d : ℕ) : STK2decaygL' d (fun sz E => bandStep2Mat sz E) := by
RBM3D/Chain/NewKLKGen.lean:802:  (bandStep2_STK2decay d).mpr (stK2decaygL_of_primed (stK2decaygL'_band d)
```
Only the sole writable file is touched (`RBM3D.lean` import left to the hub at merge, §3 (A) 4). No clash (the hits are `stK2decaygL'_band`, a different name). All helpers are `private` with stem `NewKLKBA_`, or private in `namespace NewKLKBAInst` (§3 (E)). No frozen signature edited (new file only).

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.NewKLKBA 2>&1 | grep -E "error|warning|Build completed|sorry" | grep -v longLine | tail
warning: RBM3D/BA/NewKLKBA.lean:20:100: This line exceeds the 100 character limit, please shorten it!
  ... (same style warning at lines 21, 27, 30-34, 36 of the module docstring; others are in pre-existing files)
Build completed successfully (3839 jobs).
[exited with code 0]
$ lake env lean <scratch>/T2424/ax.lean     (import RBM3D.BA.NewKLKBA; #print axioms; #check)
'RBM.BA.baNewKLKGenHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKgL'_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stK2decaygL'_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
@baNewKLKGenHyp : ∀ {d : ℕ}, 3 ≤ d → ∀ (κ 𝔡 : ℝ), 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 fun sz E => baStep2Fam sz E
stNewKLKgL'_ba : ∀ (d : ℕ), STNewKLKgL' d fun sz E => baStep2Fam sz E
stK2decaygL'_ba : ∀ (d : ℕ), STK2decaygL' d fun sz E => baStep2Fam sz E
exit=0
$ lake env lean docs/tickets/checks/T2424-check.lean >/dev/null 2>&1; echo "check exit=$?"
check exit=0
```
Only error/warning lines read: no errors. Axioms: the standard three.

## 3. Statements against the pins

The check file pins no statement text; it `#check`s the merged pin definitions. The ticket's targets are exactly those definitions at
`mk := fun sz E => baStep2Fam sz E`. Type-ascription check (same scratch file, compiled, exit 0 above):
```
example : (∀ d, 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 (fun sz E => baStep2Fam sz E)) :=
  fun d hd κ 𝔡 hκ h𝔡 => baNewKLKGenHyp hd κ 𝔡 hκ h𝔡
example : ∀ d, STNewKLKgL' d (fun sz E => baStep2Fam sz E) := stNewKLKgL'_ba
example : ∀ d, STK2decaygL' d (fun sz E => baStep2Fam sz E) := stK2decaygL'_ba
```
Pins read (merged, `main`): `NewKLKGenHyp` `Chain/NewKLKGen.lean:383-411` (F5 support/row/symmetry of `S`; F6 `‖m‖ ≤ 1`;
F7 `Σ_b ‖Step2Gen_thetaKer … s s' u a b‖ · tailW(ℓ',W,D')(|b-a'|) ≤ K_c/(1-u) · tailW(…)(|a-a'|)` for all `s s'`, all `ℓ', D' ≥ 0`;
F8 both marginals `≤ C_K W^{-d}(1-u)⁻¹`; F9 `∃ ζ, Im ζ = (1-u) Im m`, `LM = loopFine … ζ`, `GMM x x = Gres H ζ true x x - m`), with
`∃ K_c C_K ≥ 0` in front of all five clauses (constants uniform in `sz, n, E, u`, depending on `(d, κ, 𝔡)` only);
`STNewKLKgL'` `:72` (`3 ≤ d → ∀ κ 𝔡 > 0, ∃ C δ₀ > 0, STNewKLKAtgL'`); `STK2decaygL'` `Chain/Step2Gen.lean:1118` (`∃ C > 0` before
`∀ sz n E u D`, domain `0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m`, `0 ≤ u < 1`, `0 ≤ D`).
- Target 1: hypotheses `3 ≤ d`, `0 < κ`, `0 < 𝔡` exactly as the ticket lists; conclusion is the pin, unmodified. Witnesses
  (`baNewKLKGenHyp`, line 455): `K_c = Q₀ * CT + Cs`, `C_K = 1`; `Q₀` from `NewKLKBA_tail d hd 𝔡⁻¹ κ` (depends on `(d, 𝔡⁻¹, κ)`),
  `CT` from `ekPropTInf_holds d`, `Cs = 2^(d-2) e`. So `K_c` depends on `(d, κ, 𝔡)` only and is not `1` (ticket item 1, C1).
- Target 2: `stNewKLKgL'_of _ (fun hd κ 𝔡 hκ h𝔡 => baNewKLKGenHyp hd κ 𝔡 hκ h𝔡)`; constant as the generic theorem gives it (ticket item 2).
- Target 3: `∃ C` chosen as `Q₀` before `∀ sz n E u D` (quantifier order of the pin); premise `κ ≤ Im m` (primed domain); no
  `|E| ≤ 2-κ`, no smallness of `g` beyond `0 < lam ≤ 𝔡⁻¹` (ticket items 3, 6).
- F7 is the real BA Θ-convolution (BAT-F1): the clause is the pin's, over `Step2Gen_thetaKer` of the BA carrier; the proof identifies it
  with `Θ_BA M^{(ss')}` (`Step2Kern_thetaKer_BA`) and bounds it through `NewKLKBA_tail` (below). Not a special case: all `s, s'`,
  all `ℓ', D' ≥ 0`, all `u ∈ [0,1)`.
Statement verdict: all three targets are the general pins, no special case, no adapter.

## 4. Hidden hypotheses, vacuity, cycles

Signatures of the load-bearing private helpers (read from the file):
```
269: private theorem NewKLKBA_tail (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
       ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), …
       BAReal d L g κ E m → ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
         ‖(BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤ Q₀ * tailT d L g u (…)
401: private theorem NewKLKBA_real … (hIm : κ ≤ ((baStep2Fam sz (fun _ => E)).m n).im) : BAReal d (sz.L n) (sz.lam n) κ E (BAm …)
417: private theorem NewKLKBA_K_two … (hlam : 0 < sz.lam n) (hlamΛ : sz.lam n ≤ Λ) (hIm : κ ≤ …) (u) (hu0 : 0 ≤ u) (hu1 : u < 1) … :
       (baStep2Fam sz (fun _ => E)).K n u σ a = (W^d)⁻¹ * (BATheta … u (σ 0) (σ 1) * BAMss … (σ 0) (σ 1)) (a 0) (a 1)
623: private theorem NewKLKBA_GMM_small … (hIm : κ ≤ …) {u} (hu0 : 0 ≤ u) (hu1 : u < 1) (x y) :
       ‖(baStep2Fam sz (fun _ => E)).GMM n u ((sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)) x y‖ ≤ u / ((1 - u) * κ)
```
- No `structure`/`class` introduced; section `variable`s are `{d : ℕ}` only; no hypothesis is carried by a field.
- Every input is a merged theorem (`baProp5_holds`, `baComp_holds`, `ekPropTInf_holds`, `baKsolve`, `baK_unique`, `BAm_self_of_im_pos`,
  `BAMB_diag_eq`, …; imports are merged modules of `main` `631b8f4`). No external hypothesis, so no limit check is needed. No cycle:
  the file imports only upstream modules and nothing imports it.
- `BAReal` is derived from the premise `κ ≤ Im m` (`NewKLKBA_real`), not assumed.
- Non-vacuity of the domain: `κ ≤ Im m` holds at the BA datum (`hrI : BAReal 3 (sz0.L 0) gI (1/2) EI mI`, `BA/EKPins.lean:668`,
  `:= BAflow_real … flow_sz0 0`, a merged theorem), `0 < gI ≤ 1/64` (`gI_pos`, `gI_le`, `:652, :656`).

## 5. Compiled nonempty instances (file §6, lines 737-822; compiled in the build of §2)

Datum: `d = 3`, `szI = sz0.withLam (BAflowLam0 sz0 zSeq)`, `n = 0` (`L = 4` via `sz0_values.1`, `W = 32`), `E = EI`, `κ = 1/2`, `𝔡 = 1`.
- Target 1 (line 761): `baNewKLKGenHyp (d := 3) … (1/2) 1` and each of F5–F9 applied at `(szI, 0, EI)`, `u = 1/32`, `ℓ' = 2`, `D' = 1`;
  every hypothesis discharged by `szI_lam_pos` (`gI_pos`), `szI_lam_le` (`gI_le`), `szI_im` (`hrI.2`), `norm_num`. Nondegenerate.
- Target 2 (lines 795, 797-810): `example : STNewKLKgL' 3 … := stNewKLKgL'_ba 3`, and a pointwise application at `u = 1/32`, `D = 1`,
  `ℓ = 2 ≤ L = 4`, `H = g₀Ψ` (Hermitian by `NewKLKBA_hermitian`), `‖G_u − M‖_max ≤ 2/31 ≤ 1/4 = δ₀` by `NewKLKBA_GMM_small`.
  The pointwise application goes through `stNewKLKAtgL'_of` + `baNewKLKGenHyp` (the term `stNewKLKgL'_ba` is built from), not through
  `stNewKLKgL'_ba` itself (whose `δ₀` is existential). Auditor check that the endpoint itself applies at the same datum
  (scratch file, not a source edit; `u = 0`, where `NewKLKBA_GMM_small` gives `‖G − M‖ ≤ 0 ≤ δ₀` for the unknown `δ₀ > 0`):
```
$ cat <scratch>/T2424/inst2.lean | sed -n 9,20p
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (szA.L 0)),
    ‖STthetaOpg cmA 0 0 σ (STLKMg cmA 0 0 HA σ) a‖ ≤
      C / (1 - 0) * STJhatMg cmA 0 1 2 0 HA * STprof szA 0 0 1 2 (a 0) (a 1) := by
  obtain ⟨C, δ₀, hC, hδ, h⟩ := stNewKLKgL'_ba 3 (by norm_num) (1 / 2) 1 (by norm_num) (by norm_num)
  refine ⟨C, hC, fun σ a => ?_⟩
  have hL : (2 : ℝ) ≤ ((szA.L 0 : ℕ) : ℝ) := by
    have : szA.L 0 = 4 := sz0_values.1
    rw [this]; norm_num
  exact (h szA 0 EI 0 1 2 gI_pos (gI_le.trans (by norm_num)) szA_im le_rfl (by norm_num) zero_le_one
    (by norm_num) hL HA (NewKLKBA_hermitian szA 0)
    (fun x y => (NewKLKBA_GMM_small (κ := 1 / 2) (by norm_num) szA 0 EI szA_im le_rfl (by norm_num) x y).trans
      (by simpa using hδ.le)) σ a).1
$ lake env lean <scratch>/T2424/inst2.lean; echo "exit=${pipestatus[1]}"
exit=0
```
  (`szA`, `cmA`, `HA` = the file's `szI`, `cmI`, `HI`; `szA_im := hrI.2`.) So both the endpoint and its constituent theorem apply at
  concrete nondegenerate data.
- Target 3 (lines 814, 816-820): `stK2decaygL'_ba 3 … (1/2) 1` applied at `(szI, 0, EI, u = 1/32, D = 1)`, all `σ, a`; all
  hypotheses discharged. Nondegenerate.
No `N = 0`, no empty index, no collapsed window, no `False` premise, no astronomically large witness (`g₀ ≤ 1/64`, `L = 4`, `W = 32`).

## 6. Paper deltas

The three statements are the merged pins verbatim (§3), so this ticket introduces no new Lean/paper statement difference; the pins'
own differences (deterministic form D83, sharp form D315/D348, primed domain `κ ≤ Im m` and F7 over the block kernel from T2414) are
outside this ticket's diff. The prove report's "no `T2424a`" is consistent with that.

## 7. Observations (no RETURN)

- O1. The target-2 pointwise instance applies `stNewKLKAtgL'_of` + `baNewKLKGenHyp` rather than `stNewKLKgL'_ba`; the auditor's
  scratch check in §5 shows `stNewKLKgL'_ba` itself applies at the same datum. No statement or instance gap.
- O2. The ticket asks for a prove report ≤ 150 lines; the prove report has 208 lines (within CLAUDE.md §6's 300). Report-only.
- O3. Prove report (b) records that the Lean constants (`ℓ_* = 2Λ+1`, `C_P` formula) differ from the (a) table values; the forms of
  `Q₀`, `K_c` are unchanged; no statement depends on these values.

## 8. Verdict

| target | statement | hidden hyp / vacuity / cycle | instance | build, axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `baNewKLKGenHyp` | = pin `NewKLKGenHyp` at BA, `K_c = Q₀C_T + C_s`, `C_K = 1` | none | line 761, d = 3, u = 1/32 | ok, standard 3 | none new | PASS |
| 2 `stNewKLKgL'_ba` | = pin `STNewKLKgL'` at BA | none | lines 795-810 (+ auditor check) | ok, standard 3 | none new | PASS |
| 3 `stK2decaygL'_ba` | = pin `STK2decaygL'` at BA, `C = Q₀` | none | lines 814-820 | ok, standard 3 | none new | PASS |

Overall: **PASS**. No dispatcher sign-off needed. Hub: add `import RBM3D.BA.NewKLKBA` after the last import of `RBM3D.lean` and run the full build at merge.
