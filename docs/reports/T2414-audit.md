Auditor model: claude-opus-5-5
# T2414 audit (round 1) — Sun Oct 11 10:44:03 UTC 2026

Inputs: `docs/tickets/T2414.md`, `docs/tickets/checks/T2414-check.lean`, `docs/reports/T2414-prove.md`, branch `t/T2414` at `0684439`.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2414-audit1` (detached at `0684439`); merge-test worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2414-audit1-merge` (detached `main`@`913f555` plus the three branch files plus one root import line; scratch, may be removed).
`S` = scratchpad `.../scratchpad/T2414`.

## 1. Diff, stop line, build, axioms

```
$ git diff --name-only main...t/T2414
RBM3D/Chain/NewKLKGen.lean
RBM3D/Chain/Step2Gen.lean
RBM3D/Chain/Step2Kern.lean
RBM3D/Probe/T2414Pins.lean            # 1a probe, sole-writable, never merged
$ git diff --numstat main...t/T2414 -- RBM3D/Chain | awk '{i+=$1;d+=$2} END{print "inserted",i,"deleted",d,"net",i-d}'
inserted 619 deleted 102 net 517      # stop line 1,400 (probe's 769 included: 1,286, still under)
$ git diff --stat c33ef56 main -- RBM3D/Chain/ | tail -1          # base of t/T2414 = c33ef56
(empty: Chain/ unchanged on main since the base)
$ cd T2414-audit1 && lake build RBM3D.Chain.Step2Gen RBM3D.Chain.NewKLKGen RBM3D.Chain.Step2Kern; echo EXIT $?
Build completed successfully (3769 jobs).   EXIT 0      (grep -c "^error" : 0)
$ cd T2414-audit1-merge && lake build     # main@913f555 + branch files + `import RBM3D.Chain.Step2Kern` after the last import
Sun Oct 11 10:39:17 UTC 2026 ... Build completed successfully (4229 jobs).  EXIT 0  Sun Oct 11 10:43:36 UTC 2026
(#assert_rbm_axioms is the last line of RBM3D.lean: passes; main's newer BA/Step2BA, GreenCond*, BASizeClaim*, Test/Axioms build with it)
$ lake env lean $S/Ax.lean    # #print axioms of the 29 new/re-proved public theorems
names: Step2Kern_Mss_of_kron _Mss_band _thetaKer_band _uKer_band _ThetaN_band _UN_band; bandStep2_STthetaOp _STgDrift
 _STGridMartAt _STGridMart _STgDriftN _STeeUM _STGridRepNAt _STGridRepN _STNewKLKAt _STNewKLK; Step2Kern_Theta_comm _Mss_BA
 _thetaKer_BA _BAKsolve_form _uKer_BA _UN_BA; stNewKLKAtgL'_of stNewKLKAtgL'_holds stNewKLKgL'_of newKLKGenHyp_band
 stNewKLKgL_of_primed stK2decaygL_of_primed stK2decaygL'_band
  29 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Chain/{Step2Gen,NewKLKGen,Step2Kern}.lean; echo grep-exit=$?
grep-exit=1
$ lake env lean docs/tickets/checks/T2414-check.lean; echo $?     # in the audit worktree (G1 examples STNewKLK d, STK2decay d)
0   (error lines: 0)
$ git grep -cw <18 new public names> main -- 'RBM3D/*.lean'      # name clash
all 0
$ cat lakefile.toml | grep -A1 lean_lib       # default target = root RBM3D only; the probe is not built by `lake build`
[[lean_lib]]
name = "RBM3D"
```

## 2. Statements against the pins (script)

The 1a-audited probe (`6111b33`, `RBM3D/Probe/T2414Pins.lean`) carries the ticket's statements; I diffed the final definitions against it
and compiled every theorem pin against the final theorems.

```
$ python3 -I $S/defdiff.py    # docstrings/comments stripped, whitespace-normalised, `RBM.BA.` qualifier dropped
Step2Kern_Msig Step2Kern_Bsig Step2Kern_Mss Step2Gen_thetaKer Step2Gen_uKer Step2Gen_ThetaN Step2Gen_UN STthetaOpg STgDriftg
STgDriftNg STeeUMg STGridMartAtgL STGridMartgL STGridRepNAtgL STGridRepNgL STNewKLKAtgL STNewKLKgL STNewKLKAtgL' STNewKLKgL'
NewKLKGenHyp STK2decaygL'                                  -> 21/21 IDENTICAL
$ lake env lean $S/PinChk.lean; echo exit=$?   # probe §3-§6 pins, vocabulary §1-§2 deleted so names resolve to the final RBM.BA
                                                # declarations; one `example : X_pin := fun .. => RBM.BA.X ..` per pin
exit=0   (29 examples, 0 error lines)
$ git diff main...t/T2414 -- RBM3D/Chain/{Step2Gen,NewKLKGen}.lean | grep -E "^[-+](def|theorem) "   # changed headers
- Step2Gen_thetaKer (μ) / _uKer (μ) / _ThetaN (m : Fin n → ℂ) / _UN (m)   + same names over (C : FlowFM sz) (n) (σ σ' | σ : Fin k → Bool)
+ Step2Kern_Msig/_Bsig/_Mss, 6 band lemmas, STK2decaygL', stK2decaygL_of_primed, stK2decaygL'_band; Step2Gen_Theta moved (text equal)
  bandStep2_* : statement lines unchanged, proofs only (Iff.rfl/rfl -> proved)
```

Mathematics (checked by reading, against the paper):
- `Step2Kern_Mss C n σ σ' a b = W^{-d} Σ_{x∈[a],y∈[b]} M(σ)_{yx} M(σ')_{xy}`, `M(−)_{xy} = conj M_{yx}`. With `(E_a)_{xy} = W^{-d}1(x=y∈[a])`
  (`1_2:81, 530, 824`), `eq:Msig` (`1_2:1070`) `W^d tr(M(σ₁)E_a M(σ₂)E_b) = W^{-d} Σ_{x∈[a],y∈[b]} M(σ₁)_{yx}M(σ₂)_{xy}`: identical.
  BA reading `M^{(B)}_{ba}(σ₁)M^{(B)}_{ab}(σ₂)` (`1_2:1071`) = `BAMss` (`MFixedPoint:511`): proved, `Step2Kern_Mss_BA`.
- `thetaKer = X(1 − tX)⁻¹`, `uKer = (1 − sX)(1 − tX)⁻¹`, `X = M^{(σσ')}S`; slot `i` with `(σ_i, σ_{i+1})` (`finRotate`): `def:op_thn`,
  `def_Ustz` (`3_5:111-118`), cyclic convention `σ_{n+1}=σ_1`. Matches.
- (b): `Step2Kern_Mss_band` = `m_σ m_σ' I` (paper footnote `1_2:664`); the ten bridges keep their merged statements (headers unchanged).
- (c): `thetaKer = BATheta * BAMss` and `W^{-d}·thetaKer` = RHS of `BAKsolve` (`KSolve:63-66`), all `σ : Bool × Bool`; `UN = BAUN`
  (E-C1, `EKPins:53`), no obstacle. Hypothesis `(E n + m).im ≠ 0` only (that of `BAMres_fine_kron`).
- (e): F7 is `Σ_b ‖thetaKer C n s s' u a b‖ 𝒯̃(|b−a'|) ≤ K_c/(1−u) 𝒯̃(|a−a'|)` for all `s s'`; at BA (`S = 1`) `thetaKer = Θ_BA M^{(ss')}`,
  i.e. BAT-F1's real Θ-convolution. `stNewKLKAtgL'_of`/`_holds`/`stNewKLKgL'_of` keep their headers (δ₀ = κ/2).
- BAT-F2: `STK2decaygL'` is `STK2decaygL` with `|E| ≤ 2−κ` replaced by `κ ≤ ((mk sz (fun _ => E)).m n).im` (same shape as `STNewKLKgL'`);
  `stK2decaygL_of_primed` has the shape of `stNewKLKgL_of_primed`.
- Choice of (a) (block kernel, not the cut), in place, `Chain/Carrier.lean` untouched: as the ticket prefers.

## 3. Hidden hypotheses, vacuity, cycles

- No new structure or field; `FlowFM` unchanged (`Carrier.lean` not in the diff). `NewKLKGenHyp` is a `Prop` conjunction in the
  signature (F5-F9), visible; the only text change is F7. F6 (`‖m‖ ≤ 1`) stays and is no longer read by the proof (observation O2).
- No cycle: `Step2Kern.lean` imports `Step2Gen`, `BA.FlowPins/KSolve/EKPins/KTreeRep` (all merged); nothing imports it.
  Dependencies used (`BAMres_fine_kron`, `BAMfine_sz0_kron`, `BAmF_sz0_im_pos`, `baKsolve`, `stK2decay_holds`) are merged on `main`.
- No external hypothesis is added. `STK2decaygL'` at BA and F7 at BA are owed by later tickets (T3-BA, BA K⁽²⁾ decay), as the ticket says;
  `STK2decaygL'` is non-vacuous at the band: `stK2decaygL'_band` (proved from the merged `stK2decay_holds`).

## 4. Compiled nonempty instances (all compile in the module builds of §1)

| Endpoint | Instance (file:line) | Data |
|---|---|---|
| (b) kernel identities, `Mss_of_kron` | `Step2Gen.lean:1242`, `:1275` | `d=3`, `sz0` (L=4, W=32), `E≡0` (`m=i`), all four charge pairs, `k=3`; `kron` hyp. proved via `split_injective` |
| 10 bridges (b) | `Step2Gen.lean:1165, 1210, 1217, 1232` | `bandStep2Mat sz0 (STflowE z0)`, grid 8 steps on `[0,1/16]`, loop length 3 |
| (c) BA identities, `UN = BAUN` | `Step2Kern.lean:151` | `baFMz sz0 zSeq`, `n=0`, all four pairs, `k=3`; `Im m > 0` from `BAmF_sz0_im_pos`; no numeric stand-in |
| (c) cut form via merged `baKsolve` | `Step2Kern.lean:190` | same datum, `K` of `baKsolve 3` equals `W^{-d}·thetaKer` |
| `stNewKLKAtgL'_of`/`_holds`, `newKLKGenHyp_band` | `NewKLKGen.lean:772, 776, 785, 815` | band, `κ=𝔡=1/10`, `δ₀=1/20`; pointwise `n=0,E=0,u=1/32,D=1,ℓ=2,H=0` |
| `stNewKLKgL'_of`, G1 `STNewKLK d` | `NewKLKGen.lean:794` | via `stNewKLKgL_of_primed`, `bandStep2_STNewKLK` |
| BAT-F2 `stK2decaygL_of_primed`, G1 `STK2decay d` | `NewKLKGen.lean:801` | band, domain fact `Ind.half_le_mE_im` discharged |

No `N = 0`, empty index, collapsed window or `False` premise. Every deterministic hypothesis discharged at the data.

## 5. Paper deltas

Proposed in the prove report (d): `T2414a` (`eq:Msig` vs `def:Theta_BA` reading), `T2414b` (extends `T2405a`: block-kernel drift
forms, F7 over all four `(s,s')`, `STK2decaygL'` premise `κ ≤ Im m`). Every Lean/paper difference I found is covered (see O1 on wording).

## 6. Verdicts

| Target | Verdict |
|---|---|
| 1 (a) block kernel from the carrier, convention in docstring | PASS |
| 2 drift operator and n-loop kernels over (a) (in place; `STeeUMg` added, forced) | PASS |
| 3 (b) band bridges (10, proved) | PASS |
| 4 (c) BA identity, `BAKsolve` form, `BAUN` identity | PASS |
| 5 (e) `NewKLKGen` F7 restated, theorems re-proved, band instance | PASS |
| 6 BAT-F2 `STK2decaygL'`, `stK2decaygL_of_primed` | PASS |
| 7 G1 (check file, band statements unchanged, full build of main+branch) | PASS |
| 8 nonempty instances `d = 3` | PASS |
| 9 registry: none; `#assert_rbm_axioms` passes in the merge-test build | PASS |

**Overall: PASS.** No dispatcher sign-off needed.

## 7. Observations (no RETURN)

- O1 (T2414a wording). With `(E_a)_{xy} = W^{-d}1(x=y∈[a])`, `eq:Msig`'s `W^d tr(…)` *equals* the Lean `W^{-d}Σ…` form: there is no
  normalisation difference. The actual paper-internal point: `def:Theta_BA` (`1_2:663`) writes `M^{(+,-)}_{ab} = W^{-d}Σ_{x∈[a],y∈[b]}|M_{xy}|²`,
  the transpose of `eq:Msig` at `(+,−)` (`Σ|M_{yx}|²`) for non-symmetric `M`; the two agree at the band and at BA (`M^{(B)}` complex
  symmetric). Lean follows `eq:Msig`, the definition `def:op_thn` recalls. Suggest the dispatcher reword T2414a accordingly.
- O2. F6 of `NewKLKGenHyp` is kept but unused by `stNewKLKAtgL'_of`; T3-BA must still discharge it at BA (or a later ticket drops it).
- O3. `RBM3D/Probe/T2414Pins.lean` no longer compiles on the branch (`lake env lean`: 4 errors, lines 578-581, Application type mismatch; the merged generic
  kernels it references were redefined). It is not merged, not root-imported, and not a default build target.
- O4. `stK2decaygL'_band` is public without the file stem (§3 (E)); it is a result (band proof of the primed pin, needed by the axiom
  audit scan), not a helper; no statement, build or axiom effect.
- O5. Prove report is 288 lines (ticket asks ≤ 200; CLAUDE.md §6 limit 300).
- O6. Hub: add `import RBM3D.Chain.Step2Kern` after the last import line of `RBM3D.lean` (done in the merge-test worktree; built).
