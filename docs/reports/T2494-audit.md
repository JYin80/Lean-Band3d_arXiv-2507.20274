Auditor model: claude-opus-5-5

# T2494 audit, round 1: row a (L5a, file A `RBM3D/Graph/BATermHolds.lean`: targets 1-3, 8 (a))

Written Tue Oct 13 08:11:13 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2494-audit1`, detached at `t/T2494` = `e50823fe`.
Scope: the pre-signed switch to `prover-max` (1a verdict lines 76-78) and the pre-signed split A | B + C apply; row b (targets 4-7, 8 (b)-(d), 9) is not in this round.
Scratch: `<scratchpad>/T2494/` (`full.log`, `audit_check.lean`, `pin.txt`, `tgt3.txt`, `nreg.py`; not committed).

**Verdict: PASS** (targets 1, 2, 3, 8 (a)). Observations O1-O4 below; no repair.

## 1. Diff scope, hygiene
```
$ git diff --name-only main...t/T2494
RBM3D.lean
RBM3D/Graph/BATermHolds.lean
$ git diff main...t/T2494 -- RBM3D.lean   (one line, after the last import, before #assert_rbm_axioms)
+import RBM3D.Graph.BATermHolds
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/BATermHolds.lean ; echo "grep exit $?"
grep exit 1
$ grep -nE "^\s*(@\[[^]]*\]\s*)?(noncomputable |protected )?(theorem|lemma|def|abbrev|structure|inductive|instance)\b" F | grep -v private
706:theorem baLWterm_holds : ∀ d : ℕ, BALWterm d := by
715:def BALWtermExpN (d : ℕ) : Prop :=
758:theorem baLWtermExpN_holds : ∀ d : ℕ, BALWtermExpN d := by
$ grep -cE "^(private|@\[.*\] private)" F
20
$ git grep -n -E "\b(baLWterm_holds|BALWtermExpN|baLWtermExpN_holds)\b" main -- RBM3D   (main = 6ccc6be2)
(no output)
$ wc -l F
     914 RBM3D/Graph/BATermHolds.lean        (stop line 2,000)
```
Both files are sole writable files; no merged file edited; no frozen signature touched; no new `inductive`/`structure`.

## 2. Statements against the pin (script)
Target 2. Pin: `def T2494_TermClosed : Prop := ∀ d : ℕ, BALWterm d` (check file :191). Lean: `theorem baLWterm_holds : ∀ d : ℕ, BALWterm d` (F:706): identical up to the name. `BALWterm = baPin LWtermG` (`BA/LWPinsBA.lean:45`, unchanged; not in the diff).
```
$ lake env lean <scratch>/audit_check.lean   (check file verbatim + `import RBM3D.Graph.BATermHolds` + the lines below; exit printed)
example : T2494_TermClosed := baLWterm_holds
example : ∀ d : ℕ, BALWterm d := baLWterm_holds
example : ∀ d : ℕ, BALWtermExpN d := baLWtermExpN_holds
example : ∀ d, BALWterm d ↔ baPin LWtermG d := fun _ => Iff.rfl
#print axioms RBM.BA.baLWterm_holds / baLWtermExpN_holds / BALWtermExpN
...
'RBM.BA.baLWterm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermExpN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BALWtermExpN' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Target 3 (ticket: "a statement def for the regime (name at the 1b)", regime `1 - t ≤ λ²/L²`, no pinned text). Diff of the body of `LWtermExpG` (`Chain/LWGen.lean:96-105`) instantiated by `baPin` (`law ↦ Sizes.seqP (sz.withLam 0)`, `mk ↦ baFMz`, `Flow ↦ BAFlow`, `T0 ↦ BAflowT0`) against `BALWtermExpN` (F:716-726):
```
$ diff pin.txt tgt3.txt
6,7c6,8
< PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
< (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1 p.2 ω‖)
---
> PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
> 1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
> (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
10c11
< ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)))
---
> ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))
```
The only difference is the index subtype of the regime (and the projections `.1` it forces): hypotheses, quantifier order (`d, κ, ε, 𝔡` before `𝔠, sz, z`, then `t`, then `ε₀ Ψ ℓ`, `LWAssmExpgL`, then `∀ D > 0`), the loss `η⁻¹ Bctl^{1/2} · W^{-d} tailW`, the window `ℓ ≤ (log W)^{10} ℓ_t` (inside `LWAssmExpgL`) and the dimension/law are the merged pin's. The regime is `7_8:20` ("when `1 - t ≤ λ²/L²` … immediate consequence of `lem:LWterm`"), as in the ticket. Target 3 is the regime half of target 5 (consumer: row b), not a general-statement substitute; the union is row b.

Target 1 (inputs): all private (20 `private` declarations; §1); no public statement to compare.

## 3. Vacuity, hidden hypotheses, cycles
- No new structure, no `Prop` field. The pin hypotheses (`LWAssmgL`, `LWAssmExpgL`) are the paper's lemma hypotheses inside the merged pin / the regime def, not binders of a public theorem (public binder: `d : ℕ` only, F:706, :758).
- C1 / UBA-C1 / U5S-C3 greps:
```
$ grep -nE "sz\.lam|withLam|gK" F | awk -F: '$1>=704 && $1<=727'    (public statement text)
719: … LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) …        (merged law)
721: … PrecL sz (Sizes.seqP (sz.withLam 0)) …                          (merged law)
722:  1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2                 (the regime, ticket target 3)
725: … tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) …                        (pin vocabulary)
$ grep -cwE "mE|STGM|STKloop|etaT|STflowE|lwS|STGridRepNgL|BAAnpAuxG|BAShapePath" F
0
```
  No `gK`, no comparison other than the pin vocabulary, no `∀ sz z` family premise.
- Dependencies are merged results (`baLWMoment_closed`, `baGbyZeta_holds`, `baZetaClaim_holds`, `BAMomentGen_avg_whp`, `BAExp14b_cut_true`, `BAExp14d_Bctl_small`, `lwN_*`; signatures printed by the check file in `audit_check.lean`); axioms are the standard three (§2); no cycle (Lean-checked, no hypothesis on `BALWterm`).
- Target 3 non-vacuity (its index set is empty at the merged instance data, see O1). Limit check, `d = 3` at the `sz0` sizes, `t = t₀ = Im m/(Im m + Im z)`, `Im z = N^{-1+ε}`, `ε = 1/10`, `Im m ≥ κ = 1/2`:
```
$ python3 -I nreg.py      (m = n + 1;  1 - t₀ ≤ Im z/(κ + Im z)  vs  λ²/L²)
1 1-t0<=4.088e-06 lam^2/L^2=1.526e-05 True
2 1-t0<=5.431e-11 lam^2/L^2=9.313e-10 True
10 1-t0<=2.580e-22 lam^2/L^2=1.526e-19 True
100 1-t0<=1.628e-38 lam^2/L^2=1.526e-33 True
1000 1-t0<=1.027e-54 lam^2/L^2=1.526e-47 True
```
  So the regime is nonempty at admissible `t ≤ t₀` once `Im z_n` is near the lower edge `N^{-1+ε}` of `BAdom`; it is empty only at the merged `zSeq` (`Im z_n` of order 1, `zSeq_im_le`).

## 4. Compiled nonempty instance (8 (a))
```
$ sed -n 883,892p F   (lines 886-888 elided)
883: example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
884:     (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAMomentExpGen_Φ0) :
885:     PrecL sz0 μ0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
  …
889:   baLWterm_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
890:     (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1)
891:     BAMomentExpGen_Ψ0 BAMomentExpGen_Φ0
892:     ⟨by norm_num, BAMomentExpGen_Ψ0_window, hI, BAMomentExpGen_psiAll0.2.1, BAMomentExpGen_psiAll0.2.2, hL⟩
```
`d = 3`; `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`, `sz0_values`); `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `flow_sz0`; `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`); `ε₀ = 1/10`; `Ψ = Φ ≡ W^{-1/2}` (window, class, `(eq:Psi)` discharged by the merged `BAMomentExpGen_Ψ0_window`, `_psiAll0`). Index set `(Fin 2 → Bool) × (Fin 2 → Zd 3 L_n)` nonempty. Only `STInitialGT2gL` (registered pin, other gate) and `LWLoop2gL` (the stochastic `(LW_assm)` component of `LWAssmgL`) stay hypotheses: stronger than the check's shape (whole `LWAssmgL` as hypothesis). Compiled in the module build (§5). Not degenerate.

## 5. Builds and axioms
```
$ lake build RBM3D.Graph.BATermHolds 2>&1 | grep -E "error|Build completed"
Build completed successfully (4071 jobs).
$ lake build > full.log 2>&1 ; tail -2 full.log ; grep -c "error:" full.log     (branch root import, registry check)
Build completed successfully (4357 jobs).
exit 0
0
$ grep -n "axiom audit" full.log
6250:info: RBM3D.lean:589:0: axiom audit: 14709 theorems, 4576 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep "BATermHolds.lean" full.log | grep warning | sed 's/.*warning: //' | cut -c1-40 | sort | uniq -c
  (16 lines) This line exceeds the 100 character limit   (header docstring lines 19-41 only)
$ grep -o "RBM.BA.BALWterm[A-Za-z]*" full.log | sort | uniq -c       (registry: still owed; removal is target 9, row b)
   2 RBM.BA.BALWterm
   1 RBM.BA.BALWtermExp
```

## 6. Paper deltas
| Lean/paper difference | coverage |
|---|---|
| target 2: none beyond the merged pin `LWtermG` (its own deltas, e.g. D641 (b)-(d), already in `docs/paper-deltas.md:1605`) | covered |
| target 3: regime split of `lem: EWGn2_N` at `1 - t ≤ λ²/L²` (`7_8:20`) | `docs/paper-deltas.md:415` (D99, T2040k) for the band; BA reading identical; prove (d) also cites T2342a |
| `B:286-288` "analogously": the `M_{yx}` part of the closing edge at BA (offset support, weight `W^{-d}`) | candidate `T2494a` (prove (d)); proof-level, statement unchanged |
| `claim:xi` at BA used at `ρ = (log W)^{3/2}`, `R = 0`, not the ticket's `ρ = 1` | candidate `T2494b` (prove (d)); proof-level; ticket-text correction for the dispatcher |

## 7. Per-target verdicts
| target | verdict | basis |
|---|---|---|
| 1 inputs (private) | PASS | §1, §3, build |
| 2 `baLWterm_holds : ∀ d, BALWterm d` | PASS | = `T2494_TermClosed` (§2), instance §4, axioms §2 |
| 3 `BALWtermExpN`, `baLWtermExpN_holds` | PASS | pin restricted to the regime (§2 diff), non-vacuity limit check §3; instance owed by 8 (b) in row b (O1) |
| 8 (a) instance | PASS | §4 |
| 4-7, 8 (b)-(d), 9 | not in this row | split A | B + C (row b, `t/T2494b`) |

## 8. Observations (no statement, instance, build, axiom or delta-coverage effect)
- O1. Target 3 has no nonempty compiled instance in this row: at the merged `sz0`/`zSeq` data the regime is empty for every `t ≤ BAflowT0` (`Im z_n` of order 1), and the file proves emptiness at `t ≡ 1/2` (F:894-911). The ticket assigns the regime instances to 8 (b) (target 5, "both regimes nonempty … or n/a with the reason"), which is row b; §3's limit check shows the regime is nonempty for `Im z_n ≈ N^{-1+ε}`. Row b's auditor should check 8 (b)'s reason against this (a nonempty N-regime point needs a flow sequence with small `Im z`, not in merged data).
- O2. `git merge-tree --write-tree main t/T2494` reports a content conflict in `RBM3D.lean` only (main `6ccc6be2` added six imports at the same place). Rule (A) step 4 has the hub add the import itself; no code conflict.
- O3. Header docstring lines over 100 characters (style lint warnings, 16 lines); the lint option is set after the docstring.
- O4. The registry still lists `BALWterm`, `BALWtermExp` as owed although `baLWterm_holds` now proves the first: by design, target 9 is row b.
