Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 22:06:50 UTC 2026

Citations: `B:N`, `7_8:N` are lines of `paper/tex/B_graphical_lemmas.tex`, `7_8_light_weight.tex`; `probe N` is a line of `t/T2387:RBM3D/Probe/T2387Pins.lean`; other `path:N` are relative to `RBM3D/` (worktree HEAD 699d51b). Scripts: `ordtab.py`, `inst.py` (with a copy of `docs/reports/T2390/stab.py`) in the scratchpad `T2395/`; no Lean was written.
Counters are `(nS, nW, nA, nM)` = solid edges (light-weights included), waved edges, internal atoms, internal molecules; `ord = nS + 2(nW - nA)` (`B:353`; band: `nV` for `nA`, `7_8:239`).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `ord` / `size` of the atomic image | `size = (L^d)^{nM} Ψ^{nS} W^{-d(nW-nA)}` (`B:349-350`); band `W^{-d(nW-nV)}` (`7_8:239`) | the map atom -> vertex keeps `(nS,nW,nA,nM)`, hence `ord`, `size`, cutoff | equal (0) |
| 2 | `Δord` of the BA `GGGamma` terms (D402 and printed form; `f` has no edge at `x,w,α,β`; derivative term not computed): `T1` `S⁺_{xβ}M_{βy}M_{y'β}` | `0` (counters `(0,1,1,0)` from `(2,0,1,1)`; `baGGT1_ord`, `baGGLhs_ord`, probe 313) | `Lvl1Good` (`LWLvl1.lean:989-992`): `ord Γ ≤ ord Q`, and strict or (equal and `(loops, nS, pairs)` falls lexicographically) | `T1`: `nS` 2 -> 0, so the equal-order branch holds; `ord` slack 0 |
| 3 | `Δord` of the other listed terms (`T2a,b`; `T3a,b` for `W = 1` and `W = M⁺S⁺`, all `G = Ǧ + M` splits) | `>= +1` (script lines `T2a` .. `T3b`) | `>= 0` for `Lvl1Good` | `+1` |
| 4 | other `Lvl1Good` parts at `T1` | `nM`: `0 <= 1`; `nA - nW`: `0 <= 1` | `Q.nM <= Γ.nM`, `Q.nV - Q.nW <= Γ.nV - Γ.nW` | 1 and 1 |
| 5 | band `R2` `m³S⁺_{xy}G_{y'y}f` at `y' = y` (the atomic image of `y ~ y'`) | `ord` +1 as counted by `oe2xR2_ord` (`LWGGExp.lean:1113`: `G_{y'y}` one solid edge); its `G_{yy} = Ǧ_{yy} + m` part `m` has `Δord = 0`, counters `(0,1,1,0)` = BA `T1` | the band shows the same order-keeping term | the BA first sum is the band's `m`-part of `R2` |
| 6 | within-atom solid edge (`T3b`: `Ǧ_{αw}`, `α ~ w`) | `within = 1` in the script | `B:308-313` discards "edges between vertices within the same atom", but `nS` counts them | image must keep it as a loop; else `ord` drops by 1 |
| 7 | `lvl1Cutoff` (`LWLvl1.lean:3981`): `c = 1/4`, `D = 10`, `d = 3`, `K0 = 2` | `K = 4(10 + 2nM + 3(nA-nW)^+)`: `baLWT1` 60, `baGGLhs` 60, `baGGT1` 40 | `L^d <= W^{K0}`: `64 <= 32^2`; `K0 = 1` fails (`64 > 32`) | 16x |
| 8 | `Ψ` window (`W^{-d/2} <= Ψ <= W^{-c}`), `Ψ = W^{-1}` | `2^{-7.5} <= 2^{-5} <= 2^{-1.25}` | `lvl1_size_le` (`LWLvl1.lean:3989`) | `2^{2.5}` left, `2^{3.75}` right |
| 9 | size of `Q = (62,5,6,1)` (`ord 60`) | `log2 size = -289` (`Ψ = W^{-1}`), `-56.5` at `Ψ = W^{-1/4}`, `-444` at `W^{-3/2}` | `<= W^{-D} = 2^{-50}` | `2^{239}`, `2^{6.5}`, `2^{394}` |
| 10 | `Admissible` (`T2390-prove.md`): `W >= N^{1/6}`; `W^{-d/2+𝔡} <= g <= 𝔡⁻¹` (`𝔡 = 1/10`, `Λ = 10`) | `32` vs `11.31`; `2^{-7}` vs `g` | as stated | `2.83x`; `g/2^{-7}` = 2x / 128x / 1280x |
| 11 | `κ` from `Im m` (`BAReal`), `g = 1/64 / 1 / 10` | `κ = 0.5 / 0.25 / 0.04`; `Im m` (L = 64) `0.8325 / 0.3435 / 0.0439`; (L = 4) `0.8325 / 0.3777 / 0.2620` | `κ <= Im m` uniformly in `L` (T2390c: `κ(g=10) = 0.044`, not 0.262) | `1.67x / 1.37x / 1.10x` |
| 12 | `c = BAct_rate(3,10,κ)` (`BA/CombesThomas.lean:45`) | `4.158e-3 / 2.081e-3 / 3.333e-4` | `‖M_xy‖ <= c⁻¹e^{-c|b|}` with exact offset support (`BAMfine_decay`, `BA/GreenSchur.lean:124-132`) | observed `max‖M‖/(c⁻¹e^{-c|b|}) = 5.4e-5 / 3.8e-4 / 2.8e-5` |
| 13 | `ρ` per `M`-dotted edge: `Σ_b‖M_ab‖` (`BAMB_row_l1`, `GreenSchur.lean:139`) | observed `1.083 / 15.91 / 245` (L = 64); Lean `c⁻¹expC(1,c) = 4.9e15 / 1.6e17 / 1.5e21` | enters value bounds only; the counters transport has no `ρ` | constants independent of `W` |
| 14 | atom truncation `B:317-319`, `ε₁ = 1/10`, `D = 10` | `e^{-c(log W)^{1+ε₁}} <= W^{-D}` needs `log10(log W) >= 33.8 / 36.8 / 44.8` | astronomically large `W` | not usable (C1/L5): use exact offset support + row `ℓ¹` (rows 12-13) |
| 15 | `Lvl1Ident` hypotheses (`LWLvl1.lean:3828-3836`): `M a a = m`, `M a b = 0` for `a ≠ b` | fail at BA `g ≠ 0`, `Im m > 0` (`ba_scalarM_hyp_fails`, probe 253) | band identity half is not applicable at BA data | transport covers the counters half; the identity half needs `BAGGGamma` / `lanlw` / `lweight` |
| 16 | D402 coefficient `W - 1 = M⁺S⁺` (`ba_W_sub_one`, probe 287) | rows 2-3 are the same for the printed `S⁺_{xβ}` and for `M⁺S⁺` | | |

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 4`, `W = 32` (`N = 2097152`), `g = 1/64, 1, 10`, `κ` of row 11, `𝔡 = 1/10`, `ε = 1/10`, `K0 = 2`, `c = 1/4`, `D = 10`, `Ψ = W^{-1}`, `t0 = Im m/(Im m + Im z) < 1`; parent `baGGLhs` `(2,0,1,1)`, child `baGGT1` `(0,1,1,0)`, `G = baLWT1` `(2,1,2,1)`, `Q = (62,5,6,1)`. Band side for the external hypothesis (T2390's model, `L -> infinity` = L = 64): `Im m`, rate, `ρ` computed by `inst.py` (row 11-13, Ward `Σ_b|M_0b|² = 1`).
Commands: `cd <scratchpad>/T2395; python3 -I ordtab.py; python3 -I inst.py` (outputs verbatim below).

```
parent Gc_{y'x}Gc_{xy}: {'nS': 2, 'nW': 0, 'nA': 1, 'nM': 1, 'ord': 0, 'AmW': 1, 'loops': 0, 'within': 0}
T1  S+_{xb} M_{by} M_{y'b}         printed  splits= 1 min dord=+0 (mask (): {'nS': 0, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 0, 'AmW': 0, 'loops': 0, 'within': 0})  all Lvl1Good: True
T2a S+_{xb} Gc_{by} M_{y'b}        printed  splits= 1 min dord=+1 (mask (): {'nS': 1, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 1, 'AmW': 0, 'loops': 0, 'within': 0})  all Lvl1Good: True
T2b S+_{xb} M_{by} Gc_{y'b}        printed  splits= 1 min dord=+1 (mask (): {'nS': 1, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 1, 'AmW': 0, 'loops': 0, 'within': 0})  all Lvl1Good: True
T1  S+_{xb} M_{by} M_{y'b}         D402     splits= 1 min dord=+0 (mask (): {'nS': 0, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 0, 'AmW': 0, 'loops': 0, 'within': 0})  all Lvl1Good: True
T2a S+_{xb} Gc_{by} M_{y'b}        D402     splits= 1 min dord=+1 (mask (): {'nS': 1, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 1, 'AmW': 0, 'loops': 0, 'within': 0})  all Lvl1Good: True
T2b S+_{xb} M_{by} Gc_{y'b}        D402     splits= 1 min dord=+1 (mask (): {'nS': 1, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 1, 'AmW': 0, 'loops': 0, 'within': 0})  all Lvl1Good: True
T3a Gc_bb G_{ay} Gc_{y'w}          W=delta  splits= 2 min dord=+1 (mask (0,): {'nS': 3, 'nW': 1, 'nA': 2, 'nM': 1, 'ord': 1, 'AmW': 1, 'loops': 1, 'within': 0})  all Lvl1Good: True
T3b Gc_{aw} G_{by} G_{y'b}         W=delta  splits= 4 min dord=+1 (mask (0, 0): {'nS': 3, 'nW': 1, 'nA': 2, 'nM': 1, 'ord': 1, 'AmW': 1, 'loops': 0, 'within': 1})  all Lvl1Good: True
T3a Gc_bb G_{ay} Gc_{y'w}          W=M+S+   splits= 2 min dord=+1 (mask (0,): {'nS': 3, 'nW': 2, 'nA': 3, 'nM': 1, 'ord': 1, 'AmW': 1, 'loops': 1, 'within': 0})  all Lvl1Good: True
T3b Gc_{aw} G_{by} G_{y'b}         W=M+S+   splits= 4 min dord=+1 (mask (0, 0): {'nS': 3, 'nW': 2, 'nA': 3, 'nM': 1, 'ord': 1, 'AmW': 1, 'loops': 0, 'within': 1})  all Lvl1Good: True

band, y' = y: parent G_{xy}G_{yx}, ext {y}; R2 as counted in oe2xR2_ord (G_{yy} one solid edge), then G_{yy} = Gc_{yy} + m
parent: {'nS': 2, 'nW': 0, 'nA': 1, 'nM': 1, 'ord': 0, 'AmW': 1, 'loops': 0, 'within': 0}
R2 uncircled / Gc_yy part: {'nS': 1, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 1, 'AmW': 0, 'loops': 1, 'within': 0} dord = 1
R2 m part: {'nS': 0, 'nW': 1, 'nA': 1, 'nM': 0, 'ord': 0, 'AmW': 0, 'loops': 0, 'within': 0} dord = 0
BA T1 counters equal band R2 m-part counters (nS,nW,nA,nM): True
```

```
N=2097152  N^(1/6)=11.314 <= W=32: True;  L^d=64
cutoff baGGLhs counters(nS,nW,nA,nM)=(2, 0, 1, 1): K = 60
cutoff baGGT1 counters(nS,nW,nA,nM)=(0, 1, 1, 0): K = 40
cutoff baLWT1 counters(nS,nW,nA,nM)=(2, 1, 2, 1): K = 60
  Q=(62, 5, 6, 1) ord=60 Psi=W^-1: log2 size = -289.00 <= log2 W^-D = -50: True; slack 2^239.00
  Q=(62, 5, 6, 1) ord=60 Psi=W^-3/2 (left end): log2 size = -444.00 <= log2 W^-D = -50: True; slack 2^394.00
  Q=(62, 5, 6, 1) ord=60 Psi=W^-1/4 (right end): log2 size = -56.50 <= log2 W^-D = -50: True; slack 2^6.50
  window W^-d/2 <= Psi <= W^-c: 2^-7.5 <= 2^-5 <= 2^-1.25: True;  Admissible W^(-d/2+dd)=2^-7.0

(C) g, kappa, Im m(z) [L=64], c = BAct_rate(3,10,kappa), rho_obs = sum_b|M_0b|, rho_Lean = c^-1 expC(1,c), Ward, decay ratio, atom-truncation threshold
g=0.015625  Im m=0.8325>=kappa=0.5: True; g0=0.0130<=Lam: True; Im m0=0.9995, |m0|=0.9995<=1; c=4.158e-03; rho_obs=1.083; rho_Lean=4.943e+15; Ward err=1.1e-16; max|M|/(c^-1 e^-c|b|)=5.4e-05<=1: True; truncation needs log10(log W) >= 33.8
g=1         Im m=0.3435>=kappa=0.25: True; g0=0.5350<=Lam: True; Im m0=0.6420, |m0|=0.6420<=1; c=2.081e-03; rho_obs=15.91; rho_Lean=1.574e+17; Ward err=1.3e-15; max|M|/(c^-1 e^-c|b|)=3.8e-04<=1: True; truncation needs log10(log W) >= 36.8
g=10        Im m=0.0439>=kappa=0.04: True; g0=1.9121<=Lam: True; Im m0=0.2294, |m0|=0.2294<=1; c=3.333e-04; rho_obs=245; rho_Lean=1.494e+21; Ward err=1.8e-14; max|M|/(c^-1 e^-c|b|)=2.8e-05<=1: True; truncation needs log10(log W) >= 44.8

(D) the same data at the instance size L = 4 (BAReal, BAdom, window N^(-1+eps) <= Im z <= 1, self-consistency residual, Admissible W^(-d/2+dd) <= g <= 1/dd)
g=0.015625  Im m=0.8325>=0.5: True; self-consistency residual=6.8e-19; Im z=0.368 in [N^(-1+eps)=2.04e-06, 1]: True; W^(-d/2+dd)=7.81e-03 <= g <= 10: True; g0=0.0130; t0=0.6937<1; rho_obs=1.083; Ward err=0.0e+00
g=1         Im m=0.3777>=0.25: True; self-consistency residual=5.0e-16; Im z=0.822 in [N^(-1+eps)=2.04e-06, 1]: True; W^(-d/2+dd)=7.81e-03 <= g <= 10: True; g0=0.5610; t0=0.3148<1; rho_obs=5.915; Ward err=1.3e-15
g=10        Im m=0.2620>=0.04: True; self-consistency residual=4.4e-16; Im z=0.938 in [N^(-1+eps)=2.04e-06, 1]: True; W^(-d/2+dd)=7.81e-03 <= g <= 10: True; g0=4.6723; t0=0.2183<1; rho_obs=4.847; Ward err=2.2e-15
```

### Verdicts

- **S1 (atomic correspondence, tested): PASS.** Rows 1-6: the `GGGamma` list (D402 and printed) has `Δord >= 0` with exactly one order-keeping term, `T1`, which is the band's `m`-part of `R2` at `y' = y` and is a `Lvl1Good` step (`nS` 2 -> 0). Needed correction: keep within-atom solid edges as loops in the atomic image (row 6, `B:312`). Not computed here: the derivative term, `lanlw`/`lem_lweight` lists, the 17 `LocStep` outputs.
- **S2 (decision), G1: PASS (hypotheses and exponents close; decision is stage 1b's).** The counters half of `lvl1_lemma` (outs, errs, `ord`, `nM`, `nV - nW`) transports under the counter-preserving map; the identity half does not (row 15) and must come from the BA expansions.
- **Pins, C1/L5: PASS.** Rows 7-14 hold at `g = 1/64, 1, 10`; the atom truncation of `B:317-319` is excluded (row 14).
- **Overall verdict: PASS.**

## (b) Script output — Sun Oct 11 00:08:00 UTC 2026

Run in `/Users/junyin/Lean_proof/RBM3D-wt/T2395`. No port from RBM1D/RBM2D (nothing copied; no port diff-stat). The design (answers S1, S2, G1, pins, C1, rows) is `docs/reports/T2395-design.md`; this section holds the build, axioms, statements, instances.

```
$ git log -9 --format='%h %s'
f0b651f T2395: design report: line count of 6a-6c, wording of the image pin
ec74d9a T2395: design report: header, REQ note (never merged probe stays on the branch)
5548217 T2395: probe: image drops the original x-dots, LocStd iff for normal graphs; report self-tests (never merged)
3fd0e51 T2395: probe: quantify the vertex type inside the identity pin (never merged)
e352eef T2395: design report (G1 + S test: decision S' with corrections K1-K4), probe evidence statements (never merge
89edb0a T2395: probe: frame identity pin, instances of every pin, compact instance graphs (never merged)
6fe5bc0 T2395: probe: docstring width, wording (never merged)
d6400e9 T2395: probe of the BA lvl1 pins (L3a1-L3a5), the atomic image and the S test evidence (never merged)
699d51b H189: T2394, T2395 tickets and checks, DECISIONS §208, CONTROL
$ git status --short | wc -l        (worktree clean)
       0
$ git diff --stat main...t/T2395
 RBM3D/Probe/T2395Pins.lean   | 398 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2395-design.md | 165 ++++++++++++++++++
 2 files changed, 563 insertions(+)
$ wc -l RBM3D/Probe/T2395Pins.lean docs/reports/T2395-design.md      (limits 400 and 300)
     398 RBM3D/Probe/T2395Pins.lean
     165 docs/reports/T2395-design.md
     563 total
$ diff docs/reports/T2395-design.md (main worktree) docs/reports/T2395-design.md (branch)
design report: main worktree copy == branch copy
$ lake build RBM3D.Probe.T2395Pins 2>&1 | grep -E 'T2395Pins|Build completed|error'
Build completed successfully (3793 jobs).
$ lake env lean RBM3D/Probe/T2395Pins.lean; echo exit $?       (no output of its own: no warning, no error)
exit 0
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/Probe/T2395Pins.lean
0
$ lake env lean ax.lean     (import RBM3D.Probe.T2395Pins; #print axioms of the nine proved declarations)
'RBM.Graph.BAGraph.twist_atomAdj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_twist_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_good_of_lit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ba_gg2_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ba_lw2_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ba_failStep2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ba_failWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ba_withinMacro' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ggStep' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statements, extracted by `extract.py` from the file (the eight pins; `ba_twist_counters` and `ba_good_of_lit` are proved; the decide-proved evidence theorems `ba_gg2_first`, `ba_lw2_first`, `ba_failStep2`, `ba_failWithin`, `ba_withinMacro` and `ggStep` are at probe 342-376 and quoted in design §1.4, §2):

```
def BAimg : Prop := ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I),
  Γ.img.g.counters = Γ.counters ∧ Γ.img.g.lvl1NLoops = Γ.nLoops ∧ Γ.img.g.lvl1NPairs = Γ.nPairs ∧ Fintype.card Γ.img.E' = Γ.nExt ∧
    (Γ.Normal → Γ.img.g.Normal) ∧ (Γ.Normal → (Γ.LocStd ↔ Γ.img.g.LocStd))

def BAtwistIntegral (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (c t' : Bool) (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      ∫ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        (if c then (star : ℂ → ℂ) else id) (∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

def BAexpFrameE (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      (∀ p ∈ lwSplit Γ.solid, p.1.σ = true → p.1.circ = true → p.1.src = p.1.dst → ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (Γ.lw2 p) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.lw4 p) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) ∧
      (∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = true → p.1.circ = true → q.1.σ = true → q.1.circ = true → p.1.src = q.1.dst →
        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, baSum (Γ.gg2 p q) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.gg4 p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

def BAlvl1StepIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val outs (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

def BAlvl1StepGood : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal →
  ∀ Q ∈ outs, Q.g.Normal ∧ BALvl1Good P.g Q.g

def BAsim (m : ℂ) : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal →
  ∀ Q ∈ outs, (∃ outsπ : List (PGraph E), LocStep m P.img outsπ ∧ ∃ Q0 ∈ outsπ, Q.g.scalingOrder = ord Q0.g.counters ∧ Q.g.nM = Q0.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW = (Q0.g.nV : ℤ) - Q0.g.nW ∧ Q.g.nLoops = Q0.g.lvl1NLoops ∧ Q.g.nS = Q0.g.nS ∧ Q.g.nPairs = Q0.g.lvl1NPairs ∧
      Q.g.nExt = Fintype.card Q0.E') ∨ P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt

def BAlvl1ExistsStep : Prop := ∀ {E : Type} (P : BAPGraph E), P.g.Normal → ¬ P.g.LocStd → ∃ outs, BALocStep P outs

def BAlvl1Lemma (d : ℕ) : Prop :=
  ∀ {E : Type} (K : ℤ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧ (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ outs ++ errs, BAReach K P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

theorem ba_twist_counters (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).counters = Γ.counters := by ...

theorem ba_good_of_lit {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁] [Fintype E₂] [DecidableEq E₂] [Fintype I₂]
    [DecidableEq I₂] {Γ : BAGraph E₁ I₁} {Q : BAGraph E₂ I₂} (h : BALvl1GoodLit Γ Q) (hx : Q.nExt ≤ Γ.nExt) : BALvl1Good Γ Q := by ...
```

Compiled nonempty instances (probe 379-381, 388-396 of `f0b651f`, verbatim; correction at the Repair below: `BAsim` had no instance in `f0b651f`, so "each pin" was false for it): each listed pin is applied at concrete data with every deterministic hypothesis discharged (`BASelf` by `BAflow_real` at `sz0`: `d = 3`, `L = 4`, `W = 32`, `g₀ = 1/64`; normality, step constructor and memberships by `decide`/`rfl`); pins that are other rows' statements stay hypotheses `h`:

```
example (h : BAlvl1StepGood) := h (baPG baGGLhs) _ ggStep (by decide)
example (h : BAlvl1ExistsStep) : ∃ outs, BALocStep (baPG baGGLhs) outs := h (baPG baGGLhs) (by decide) (by decide)
example (h : BAlvl1Lemma 3) := h 10 (baPG baGGLhs) (by decide)
example (h : BAlvl1StepIdentity 3) :=
  h (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0)
    (BAflow_real _ _ _ _ sz0 zSeq flow_sz0 0).1 (by norm_num) (by norm_num) (baPG BAVocabInst.baGGLhs) _ T2395Inst.ggStep (by decide) ℓe
example (h : BAtwistIntegral 3) := h (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2)
  (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0) (BAflow_real _ _ _ _ sz0 zSeq flow_sz0 0).1 (by norm_num) (by norm_num) true false BAVocabInst.baGGLhs ℓe
example (h : BAexpFrameE 3) := (h (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2)
  (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0) (BAflow_real _ _ _ _ sz0 zSeq flow_sz0 0).1 (by norm_num) (by norm_num) baGcxx (fun _ => default)).1
  (⟨true, true, .inr 0, .inr 0⟩, []) List.mem_cons_self rfl rfl rfl
example (h : BAimg) : BAVocabInst.baGGLhs.img.g.Normal := (h BAVocabInst.baGGLhs).2.2.2.2.1 (by decide)
```

Name-clash grep (`clash.py`, new public names against every other `RBM3D/**/*.lean`):
```
57 declared names; files scanned: 433 ; clashes: []
```

Narrative (facts only; every number is in the output above or in the design report).
- Result: decision S′ (S with corrections K1-K4), G1 written, 8 pins and 9 proved declarations in the probe; the S1 tables, the proof of G1, the pins, C1 and the row table are in `docs/reports/T2395-design.md` (165 lines).
- (a) was not edited and no (a′) is needed: its rows 2-3 (`Δord` of the `GGGamma` terms: `S1` 0, the others `≥ +1`) are the table of design §3 (b); its row 5 (the band's `R2` `m`-part at `y' = y`) is design §1.5; its row 6 (a within-atom solid edge must stay a loop) is K1.
- The S1 test is a Python model (`basim.py`) of the expansions as stated in Lean. It was cross-checked against `#eval` of the Lean definitions (`xcheck`: all partition members of 26 + 15 + 2 terms agree) and its band side against the proved `Lvl1Good` (`bandcheck`: 3,037,466 outputs, 0 violations). The budget table is verified exhaustively over all coincidence patterns of the atoms (`table.py`).
- `lw2 lw4 gg2 gg4` are provisional copies of `B:376-405` with the D402 coefficient (rows L2c1, L2c2 own them); `BAimg`, `BAsim` are pins without proof; the five evidence theorems are proved by `decide` (the last by `decide +kernel`).
- The report is written to `docs/reports/` of the main worktree and also committed on the branch, because the ticket's acceptance asks `git diff --stat main...t/T2395` to be the probe and the report; the T2387 precedent kept the report on `main` only.
- Ticket text against `main`: the ticket names its sibling gates T2396 (G2) and T2397 (LW-14); on `main` the G2 gate is T2397 and the LW-14 gate T2398 (T2396 is BA/KStep). The ticket and supervisor 2149 call L3a1-L3b6 "12 rows"; T2387 §6 lists 11 rows with central sum 16,257.
- No external input; [yang2024Del] was not needed; no question to Jun. Stop rule checked with `wc -l`: probe 398 (limit 400), design report 165 (limit 300).

## (c) Verified names (checked by `#check` in the probe's context)

- `decide_eq_decide : decide p = decide q ↔ (p ↔ q)` (core).
- `List.any_map : (List.map f l).any p = l.any (p ∘ f)`.
- `Function.comp_def : f ∘ g = fun x => f (g x)`.
- `Function.surjective_id : Function.Surjective id`.
- `Function.Surjective.comp : Surjective g → Surjective f → Surjective (g ∘ f)`.
- `List.mem_cons_self : a ∈ a :: l`; `List.mem_cons_of_mem : a ∈ l → a ∈ y :: l`.
- `List.countP : (α → Bool) → List α → ℕ`; `List.eraseIdx : List α → ℕ → List α`.
- `Finset.image : (α → β) → Finset α → Finset β` (`[DecidableEq β]`).
- Merged RBM3D names used (all exist): `lwSymmTwistG`, `lwSymmTwistG_dotted`, `lwSymmTwistG_adj`, `lwSymmTwistG_counters`, `owxDE`, `owxEmb`, `LGraph.owxExt`, `lwSplit`, `PGraph.lvl1Comp`, `LGraph.mergeP`, `LGraph.lvl1NLoops`, `LGraph.lvl1NPairs`, `LocStep`, `BAGraph.partition`, `BAGraph.lanlwD`, `BAGraph.lanlwT1`, `BAGraph.lanlwTerms`, `BAlwData`, `BAComb.val`, `BAPGraph.val`, `RBM.BA.BASelf`, `RBM.BA.BAflow_real`, `RBM.BA.FlowPinsInst.flow_sz0`, `RBM.BA.FlowPinsInst.zSeq`, `BAVocabInst.baGGLhs`, `baGcxx`, `lanlw_val`, `lanlw_scalingOrderG`, `BAGraph.val_eq_partition`.
- Names verified absent: none claimed.

## (d) Open issues and paper-delta candidates

Open issues.
1. `BAimg` (R0) and `BAsim` (R1) are unproved pins; the matching of §1.4 is at the level of invariants, `PathInv` and the cost apparatus need graph-level matching (design §6, row R1).
2. The graph-operation identities of `lw2 lw4` and `gg2 gg4` and their `ord ≥` bounds (the table of design §3 (b) is the plan) belong to L2c1, L2c2; `BAGGGamma` (`t/T2387` probe 344) is owed by L2c2.
3. Lemma E and the budget table are exhaustive over coincidence patterns for `D_q`, `T1/3a`, `3b`, `S1`; for the `(M⁺S⁺)` parts and `GGGamma` sum 3 the identification with these rows is by structure and by the random test (design §7 Limits).
4. Property (6) at BA is claimed to transport through `PGraph.LocCostGe` (all setoids); the G2 gate (T2397) must confirm it and name the `ScostLL` lemmas for the BA-only shapes.
5. The row table is a census estimate (`rowtab.py`), not a port.

Paper-delta candidates (tags `T2395a`-`e`; the dispatcher numbers them).
- `T2395a` `B:312`: the atomic graph must keep within-atom solid and waved edges as loops; otherwise `n_S`, `n_W` of `(eq:ordG_BA)` are not those of the atomic graph.
- `T2395b` `B:322`, `B:416` ("carry over verbatim"): true for the invariants of the outputs of the expansions (design §1.4), false for the step relation: it needs the macro steps (K2) and `nExt` in the termination measure (K3).
- `T2395c` `B:407` ("as explained in [yang2024Del, Appendix B]"): the argument is design §3 (strategy at atoms, two macro steps, `nExt`, Lemma E); that paper was not needed.
- `T2395d` `B:98-100`, `(eq:GGraisesord)`: the first sum of `GGGamma` keeps the order of its parent; it is the band's `R2` `m`-part at `y' ~ y` (`7:361`); extends `T2387b`.
- `T2395e` the band's `Lvl1Ident` hypotheses (`M a a = m`, `M a b = 0`) fail at BA data (`T2387e`); the identity half of the `lvl1` lemma is BA-specific.

## Repair (audit round 1) — Sun Oct 11 00:28:55 UTC 2026

Defects D1, D2 and required items 1-5 of `docs/reports/T2395-audit.md`; commit `4c1de4c` on `t/T2395`. The design report (§0, §2, §3 Step 3, §4, §6, §7, and its own `## Repair`) carries the mathematics; probe line numbers below are those of `4c1de4c`; those in (b) above are of `f0b651f`.

```
$ wc -l RBM3D/Probe/T2395Pins.lean docs/reports/T2395-design.md      (limits 400 / 300)
     396 RBM3D/Probe/T2395Pins.lean
     173 docs/reports/T2395-design.md
$ git diff --stat main...HEAD
 RBM3D/Probe/T2395Pins.lean   | 396 +++++++++++++++++++++++++++++++++++++++++++
 docs/reports/T2395-design.md | 173 +++++++++++++++++++
 2 files changed, 569 insertions(+)
$ lake build RBM3D.Probe.T2395Pins 2>&1 | grep -A2 T2395Pins; ... | tail -1
✔ [3793/3793] Built RBM3D.Probe.T2395Pins (81s)
Build completed successfully (3793 jobs).
$ lake env lean RBM3D/Probe/T2395Pins.lean; echo exit $?
exit 0
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2395Pins.lean
0
$ lake env lean ax2.lean      (scratchpad T2395/; #print axioms)
'RBM.Graph.ba_lvl1StepGood_of_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2395Inst.ggFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
(the nine other proved declarations, as in (b): [propext, Classical.choice, Quot.sound], same output)
$ git grep -nE '(def|theorem|abbrev|inductive|lemma) +([A-Za-z0-9_.]*\.)?<name>( |$)' main -- 'RBM3D/*.lean' | wc -l
BAstepMono 0; BAtwistInv 0; ba_lvl1StepGood_of_sim 0; ggFrame 0; good_congr 0; lit_of_band 0   (the last two are private)
```

New statements (`sed -n '269,274p;323p' RBM3D/Probe/T2395Pins.lean`):
```
def BAstepMono : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal ∧
  P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧ ((Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧ Q.g.nExt ≤ P.g.nExt
/-- **L3a1, twist invariance**: the twist keeps normality, the external atoms, the atom-level loops and pairs (counters: `ba_twist_counters`). -/
def BAtwistInv : Prop := ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : BAGraph E I),
  (Γ.Normal → (Γ.twist c t).Normal) ∧ (Γ.twist c t).nExt = Γ.nExt ∧ (Γ.twist c t).nLoops = Γ.nLoops ∧ (Γ.twist c t).nPairs = Γ.nPairs
/-- L3a5: a non-locally-standard normal graph has a step (`lvl1_exists_step`, `LWLvl1.lean:3655`). -/
theorem ba_lvl1StepGood_of_sim {m : ℂ} (hi : BAimg) (hs : BAsim m) (hm : BAstepMono) (ht : BAtwistInv) : BAlvl1StepGood := by
```
Compiled instances added (`sed -n '369,379p'`; probe 372-374 are the earlier ones):
```
theorem ggFrame : BAFrameStep (baPG baGGLhs) ggF := BAFrameStep.gg (baPG baGGLhs) ggP (List.mem_cons_of_mem _ List.mem_cons_self) ggQ
  List.mem_cons_self ⟨rfl, rfl, rfl, rfl⟩ (0 : Fin 1) ⟨rfl, rfl⟩ (by decide) (by decide) (by decide)
theorem ggStep : BALocStep (baPG baGGLhs) (ggF.map (BAPGraph.twist false false)) := ⟨false, false, ggF, ggFrame, rfl⟩
example (h : BAlvl1StepGood) := h (baPG baGGLhs) _ ggStep (by decide)
example (h : BAlvl1ExistsStep) : ∃ outs, BALocStep (baPG baGGLhs) outs := h (baPG baGGLhs) (by decide) (by decide)
example (h : BAlvl1Lemma 3) := h 10 (baPG baGGLhs) (by decide)
example (h : BAsim Complex.I) := h (baPG baGGLhs) ggF ggFrame (by decide)
example (h : BAstepMono) := h (baPG baGGLhs) ggF ggFrame (by decide)
example (h : BAtwistInv) := h true true baGGLhs
example (hi : BAimg) (hs : BAsim Complex.I) (hm : BAstepMono) (ht : BAtwistInv) :=
  ba_lvl1StepGood_of_sim hi hs hm ht (baPG baGGLhs) _ ggStep (by decide)
```
Narrative.
- D1: the counter half of Lemma S is the pin `BAstepMono` (row L3a4); the twist invariance of `Normal`, `nExt`, loops, pairs is the pin `BAtwistInv` (row L3a1; the counters were already `ba_twist_counters`). `BAsim` is unchanged. The reduction `ba_lvl1StepGood_of_sim` is proved from `BAimg`, `BAsim m`, `BAstepMono`, `BAtwistInv`, the merged `lvl1_step_good` (`LWLvl1.lean:3290`) and two private helpers (`good_congr`, `lit_of_band`, probe 301, 311).
- D2: `BAsim Complex.I` and `BAstepMono` are applied at the frame step `ggFrame` (probe 369, the `gg` step at `baGGLhs` used by `ggStep`), `BAtwistInv` at `baGGLhs` with twist `(true, true)`, the reduction at `ggStep`; the normality hypotheses are discharged by `decide`.
- Rows (design §6): L3a1 +60 / +80 / +150 for `BAtwistInv`; L3a4 +40 for the copied reduction and deps R0, R1, L3a1; S′ total 5,900 / 7,230 / 12,530.
- Paper-delta candidate added: `T2395f` (`B:407-416`): the paper states no bound on the number of external atoms of the outputs and no twist invariance of the atom structure; `BAstepMono` and `BAtwistInv` are BA-specific (they serve K3, `T2395b`).
- Verified names used in the repair: `List.mem_map`, `.lt_or_eq` on `≤` in `ℤ`, `Counters.mk.injEq` (structure injectivity lemma), `lvl1_step_good`; all elaborate in the compiled probe.
