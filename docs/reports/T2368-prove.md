Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 03:16:59 UTC 2026

Citations: `1_2:N` = `paper/tex/1_2_Intro_model_result.tex`; `KB:N` = `RBM3D/BA/KBase.lean`; `TR:N` = `RBM3D/Loop/TreeRep.lean`; `KLT:N` = `RBM3D/Loop/KLTree.lean`; `MF:N` = `RBM3D/BA/MFixedPoint.lean`. Scripts (not in the repository): scratchpad `T2368/` (`n3.py`, `inst.py`, `ext.py`; `kode.py` copied from `T2360/`).

### (i) Exponent table

Mathematics. With `Θ^{ij} = Θ_t^{(σ_i,σ_j)} = (1 - t M^{ij})⁻¹`, `M^{ij}_{ab} = M(σ_i)_{ba} M(σ_j)_{ab}` (`MF:511`), `BAMLoop_n = W^{-(n-1)d} ∏_i M(σ_i)_{a_{i-1}a_i}` (`KB:54`, K00). `treeEqRhsS` at `S = 1` (`KLT:809`) is `W^d Σ_{k<l} Σ_a K(cutGlueL k l a) K(cutGlueR k l a)` (the `S=1` kernel collapses `Σ_{a,b}` to `a = b`).
Cut `(k,l)` of an `n`-loop (`TR:75-82`): `cutGlueL` has charges `σ[:k] ++ σ[l-1:]`, labels `a[:k-1], x, a[l-1:]`, length `k+n-l+1`; `cutGlueR` has charges `σ[k-1:l]`, labels `a[k-1:l-1], x`, length `l-k+1`.
* `n = 2`: only `(1,2)`: `∂_t K = W^d K K`. With `K = W^{-d} Θ M` (matrix in `a₁,a₂`): `∂_t(ΘM) = ΘMΘM` (`BATheta_hasDerivAt`, `KB:341`), and `W^d (W^{-d})² = W^{-d}`. At `t=0`: `Θ=1`, `W^{-d} M^{12}(a₁,a₂) = W^{-d} M(σ₁)_{a₂a₁} M(σ₂)_{a₁a₂} = BAMLoop_2`.
* `n = 3`: `(1,2)`: `W^d Σ_b K₂^{σ₁σ₂}(a₁,b) K₃(b,a₂,a₃) = Σ_b (Θ^{12}M^{12})(a₁,b) K₃(b,a₂,a₃)` (leaf 1: `Θ→ΘMΘ`); `(2,3)`: same on leaf 2 with `K₂^{σ₂σ₃}`; `(1,3)`: `W^d Σ_b K₂^{σ₁σ₃}(b,a₃) K₃(a₁,a₂,b)` (leaf 3; charge pair is `(σ₁,σ₃)`, not `(σ₃,σ₁)`: use `Θ^{13} = Θ^{31}` (`BATheta_swap`, `KB:350`), `M^{13} = M^{31}` (the `e` inside the proof of `BATheta_swap`, not a stand-alone lemma), `Θ`, `M` symmetric (`BATheta_isSymm`, `KB:371`) and `ΘM = MΘ` (resolvent, `KB:330`), so `(ΘM)(b,a₃) = (ΘM)(a₃,b)`). The three terms equal the three leaf derivatives of the triple sum, `∂Θ = ΘMΘ` on each leaf, the `BAMLoop_3` factor being `t`-independent. At `t=0`, `Θ = 1` (`PropThetaQ Q 0 = Ring.inverse 1`), so `(Kn3sol)` is `BAMLoop_3`. `W` power: `W^d·W^{-d}·W^{-2d} = W^{-2d}`, an identity in `ℂ` also at `W^d = 0` (`0⁻¹ = 0`).
* No 1-loop occurs in any cut of a loop of length `≥ 2` (`two_le_length_cutGlueL/R`, `Loop/Unique.lean:68-72`; table below), so the clause-3 (`PropSpin m`) of `IsKLoopSLe` is only the third conjunct, and the ticket's sentence "cuts of a 3-loop are 2-loops and 1-loops" is: **cuts are of lengths 2 and 3 only**. System `n ≤ 3` is closed.

| row | value | constraint | slack |
|---|---|---|---|
| `t` range | `t ∈ [0,1)` | `|t| < 1` for `1 - tQ` unit, `‖Q‖_{∞→∞} ≤ 1` (`KB:151,159`) | `1-t ≥ 0.1` at `t = 0.9`; binding at `t = 1`: `‖M^{+-}‖ = 1`, row sums of `Θ^{+-}` `= (1-t)⁻¹` (`KB:381`). `HasDerivAt` at `t = 0` is two-sided: needs `|s| < 1` near 0: slack 1 |
| `‖M^{ij}‖_{∞→∞}` | `≤ 1` | `|M^{ij}_{ab}| = BAK_ab`, Ward row sums (`KB:312`); uses `BAReal.1 = BASelf` only | 0 for `(+,-)`; `κ ≤ Im m` not used here |
| `W` | any `W : ℕ` | none: `W^d·(W^d)⁻¹·(W^d)⁻¹ = (W^d)⁻¹` (`n=2`) and `W^d·(W^d)⁻¹·((W^d)⁻¹)² = ((W^d)⁻¹)²` (`n=3`) hold in `ℂ` also at `W^d = 0` | no hypothesis `1 ≤ W` needed |
| `3 ≤ L` | pin's `haveI : NeZero L` | appears only to supply `NeZero L`; no `BATheta_*` lemma takes `hL` (`KB:324-381`) | any `L ≥ 3` (instance `L = 5`) |
| `0 < g ≤ Λ`, `0 < κ ≤ Im m` | instance `g = 0.5`, `Λ = 1`, `κ = 0.5`, `Im m = 0.807` | pin hypotheses; `g` enters only through `BAMB` | `Λ - g = 0.5`, `Im m - κ = 0.307` |
| leaf charge pair | leaf `v` carries `Θ^{(σ_v,σ_{v+1})}` (K00) | negative control: `Θ^{(σ_v,σ_v)}` gives error `1.96e-01` (below) | the pinned form passes at `7.5e-9`; the wrong form fails at `2e-1` |
| `n=3` equation | linear in `K₃`, coefficients `K₂` | levels: lengths `{2,3}` only (script `ext.py` below) | no level-4 term in the `n ≤ 3` system |
| hypotheses beyond `BAReal`, `3 ≤ L`, `0 ≤ t < 1` for `baKsolveLe3_holds` | none | | none needed; no pin repair (amend) needed |
| N3 stop line | `n=3` error `7.5e-9` (RK4, 800 steps) | `≤ 1e-8` target, `1e-6` stop | `2.5e-9` to target, `1.0e-6` to stop; exact-ODE defect `5.1e-13` |

K01 instances (S = 1). `kernel_one_rot_transl` (`Loop/KLUnique.lean:866`) gives symmetry, `‖1_{ab}‖ ≤ 1`, translation invariance: no hypothesis on `d, L`. `RotS` needs `M⟨s::σ,b::a⟩ = M⟨σ++[s],a++[b]⟩` for `σ.length = a.length`: for `BAMLoop` the factors `M(σ_i)_{a_{i-1}a_i}` of the rotated loop are the same multiset (`BAMLoop_rot`; commutative product; checked at `n = 4,5`, below). `TranslS` needs `M⟨σ, a.map(·+c)⟩ = M⟨σ,a⟩`: follows from `Ms σ (x+c)(y+c) = Ms σ x y`, which for `Ms = BAMsigma (BAMB ..)` is `BAMB_shift` (`BA/Ward.lean:53`) and, for `σ = false`, `(Mᴴ)(x+c)(y+c) = conj M(y+c)(x+c) = conj M y x`. `BAKsol_isKLoopS`: `BAKsolve d` provides `∃ K, IsKLoopS .. (BAMLoop d L W (BAMsigma d L (BAMB ..))) ..` and `BAKsol` (`BA/FlowPins.lean:281`) is the `dite` on the same existential (same `S = 1`, `m = PropSpin m`, `M`), so `choose_spec` applies.
`BAKsolve d` is a pin (K05b), not an external input; it is used only as the antecedent of `BAKsol_*`. Plausibility of its conclusion (all levels): level `n`'s equation is linear in `K^{(n)}` (cuts of length `n` pair with a 2-loop: `l = k+1`), with coefficients from lower levels continuous on `[0,1)`; numerics: the `n ≤ 5` system integrates to `t = 0.9` with finite values (`ext.py` below).

### (ii) Concrete nondegenerate instance and N3

Instance: `d = 1`, `L = 5`, `W = 2`, `g = 0.5`, `Λ = 1`, `κ = 0.5`, `E = 0.3`, `m` the root of `(self_m)` with `Im m > 0` (circulant `Ψ` = cycle adjacency on `Z_5`), `t ∈ {0, 0.5, 0.9}`. Lean instance data (prover's choice, not part of this check): `inst_flow_real 0` (`BA/GreenSchur.lean:602`, `d = 3`, `κ = 9/10`, `BAReal` at `n = 0` of `GreenSchur_szF`), `0 < g` for that datum is still to be shown (`g = √t₀ · lam`; `BAt0_pos`, `MF:282`).
Command: `cd T2368 && PYTHONPATH=. python3 inst.py` (and `ext.py`); output:
```
d=1 L=5 W=2 g=0.5 E=0.3 Lambda=1 kappa=0.5
hyp: 3<=L True | 0<Lambda,0<kappa True | 0<g<=Lambda True | W=2 (W^d=2)
BAReal: BASelf: Im m = 0.8071590763828076 >0: True ; |m - L^-d tr M| = 2.7755575615628914e-16 ; kappa<=Im m: True
m = (-0.0688890070224153+0.8071590763828076j)
t = 0.0 in [0,1): True
t = 0.5 in [0,1): True
t = 0.9 in [0,1): True
t=0 length-2 value W^-d M^(++)(0,1) = (0.04672996876536969+0.04354678749301095j) ; BAMLoop_2 = W^-1 M(+)_{10} M(+)_{01} = (0.04672996876536969+0.04354678749301095j)
nonzero for some sigma: True
rotation defect: n=3 5.6e-17  n=2 3.0e-17 | translation defect (shift all labels by 1): 2.8e-16
M(sigma) translation invariance (circulant): 2.2247786310271853e-16
negative control (leaf Theta^(sigma_v sigma_v) instead of Theta^(sigma_v sigma_{v+1})): max err 1.96e-01
n=4 BAMLoop cyclic invariance at t=0 (max over sigma, a): 6.938893903907228e-18
n=5 BAMLoop cyclic invariance at t=0 (max over sigma, a): 3.576224061345498e-18
N=5 system RK4 to t=0.9 finite: True  max|K4|=3.702 max|K5|=5.724
n = 2 cuts (k,l)->(len L, len R): {(1, 2): (2, 2)}
n = 3 cuts (k,l)->(len L, len R): {(1, 2): (3, 2), (1, 3): (2, 3), (2, 3): (3, 2)}
n = 4 cuts (k,l)->(len L, len R): {(1, 2): (4, 2), (1, 3): (3, 3), (1, 4): (2, 4), (2, 3): (4, 2), (2, 4): (3, 3), (3, 4): (4, 2)}
```
N3 command: `PYTHONPATH=. python3 n3.py > n3.out` (RK4, `treeEqRhsS`, `S = 1`, initial data the K00 `BAMLoop`, vs `(Kn2sol)`, `(Kn3sol)` as pinned, every `σ`, every `a`; also the exact defect `|rhs(closed) - d/dt closed|` with `∂Θ = ΘMΘ`). Summary (script over `n3.out`) and the 8 worst rows (`t = 0.9`):
```
24 rows (q in {4,5}, g in {0.2,0.5}, W in {1,2}, t in {0,0.5,0.9}), E=0.3, 800 RK4 steps
max|closed-RK4|: n=2 6.1e-10  n=3 7.5e-09 ; max exact-ODE defect: n=2 1.4e-14  n=3 5.1e-13
q=4 g=0.2 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 6.1e-10 n=3 7.5e-09 | ODE defect(exact) n=2 7.1e-15 n=3 4.6e-13
q=4 g=0.2 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 3.0e-10 n=3 1.9e-09 | ODE defect(exact) n=2 3.6e-15 n=3 1.1e-13
q=4 g=0.5 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 5.6e-10 n=3 4.8e-09 | ODE defect(exact) n=2 7.1e-15 n=3 6.4e-14
q=4 g=0.5 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 2.8e-10 n=3 1.2e-09 | ODE defect(exact) n=2 3.6e-15 n=3 1.6e-14
q=5 g=0.2 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 5.4e-10 n=3 6.6e-09 | ODE defect(exact) n=2 1.4e-14 n=3 5.1e-13
q=5 g=0.2 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 2.7e-10 n=3 1.6e-09 | ODE defect(exact) n=2 7.1e-15 n=3 1.3e-13
q=5 g=0.5 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 4.4e-10 n=3 3.3e-09 | ODE defect(exact) n=2 7.1e-15 n=3 5.7e-14
q=5 g=0.5 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 2.2e-10 n=3 8.3e-10 | ODE defect(exact) n=2 3.6e-15 n=3 1.4e-14
```
At `t = 0` the closed forms equal the RK4 initial state exactly (`0.0e+00`, all 8 `t=0` rows of `n3.out`).

External hypotheses: none beyond `BAReal` (a merged `def`, discharged at the data above: `|m - L⁻ᵈ tr M| = 2.8e-16`, `Im m = 0.807 ≥ κ`) and the pin `BAKsolve d` (antecedent of the `BAKsol_*` lemmas only).

### Verdict
* `baKsolveLe3_holds` (and the pins `IsKLoopSLe`, `BAKsolveLe3`, `BAKsolve`): **PASS** (`n=3` N3 error `7.5e-9 ≤ 1e-8`; hypotheses are exactly `BAReal`, `3 ≤ L`, `0 ≤ t < 1`).
* `baK_unique`, `baK_rotate`, `baK_translate`, `BAMLoop_rot`, `BAMLoop_translate`, `BAMsigma_shift`, `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate`: **PASS** (all hypotheses of `uniqS_holds`, `rotS_holds`, `translS_holds` hold at `S = 1`, `BAMLoop`).
* (iii) the line-estimate plan is not part of this section (stage-1a rules).

## (b) Script output (stage 1b, Sat Oct 10 03:36:15 UTC 2026)

Scripts and scratch files: scratchpad `T2368/` (`gen.sh`, `pindiff.py`, `stmts.py`, `summ.py`, `pins.lean`, `ax.lean`, `names.lean`); not in the repository. The prove branch is `t/T2368`; the only file in `git diff main...t/T2368` is `RBM3D/BA/KSolve.lean`.

```
$ date -u
Sat Oct 10 03:34:37 UTC 2026
$ git log --oneline -4 ; wc -l RBM3D/BA/KSolve.lean ; git diff --stat main...t/T2368
057f0f4 T2368: BA/KSolve wrap header doc (no content change)
a82cad1 T2368: BA/KSolve compiled instances (section 3)
329fd3b T2368: BA instances of K01 (baK_unique/rotate/translate, BAMLoop_rot/translate, BAKsol_*) (section 2)
3f232b0 T2368: BA/KSolve pins and baKsolveLe3_holds (section 1)
     767 RBM3D/BA/KSolve.lean
 RBM3D/BA/KSolve.lean | 767 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 767 insertions(+)
$ lake build RBM3D.BA.KSolve 2>&1 | grep -E "KSolve|Build completed|error"
Build completed successfully (3740 jobs).
$ lake env lean docs/tickets/checks/T2368-check.lean >/dev/null; echo exit $?   (check file, imports the merged K01 pins)
exit 0
$ python3 pindiff.py   (pin docstring+def text in KSolve.lean vs the check file, Part 1)
IsKLoopSLe identical text (docstring+def): True | lines 8
BAKsolve identical text (docstring+def): True | lines 12
BAKsolveLe3 identical text (docstring+def): True | lines 18
$ lake env lean pins.lean ; echo exit $?   (check file Part 1 + KSolve + `example : @RBM.BA.X = @RBM.BA.T2368Check.X := rfl` for X in IsKLoopSLe, BAKsolve, BAKsolveLe3, and `RBM.BA.baKsolveLe3_holds : ∀ d, T2368Check.BAKsolveLe3 d`)
exit 0
$ lake env lean ax.lean   (#print axioms of every target and instance)
baKsolveLe3_holds : [propext, Classical.choice, Quot.sound]
baK_unique : [propext, Classical.choice, Quot.sound]
baK_rotate : [propext, Classical.choice, Quot.sound]
baK_translate : [propext, Classical.choice, Quot.sound]
BAMLoop_rot : [propext, Classical.choice, Quot.sound]
BAMLoop_translate : [propext, Classical.choice, Quot.sound]
BAMsigma_shift : [propext, Classical.choice, Quot.sound]
BAKsol_isKLoopS : [propext, Classical.choice, Quot.sound]
BAKsol_rotate : [propext, Classical.choice, Quot.sound]
BAKsol_translate : [propext, Classical.choice, Quot.sound]
KSolveInst.le3_nondeg : [propext, Classical.choice, Quot.sound]
KSolveInst.rot_witness : [propext, Classical.choice, Quot.sound]
KSolveInst.translate_BAMLoop : [propext, Classical.choice, Quot.sound]
KSolveInst.unique_inst : [propext, Classical.choice, Quot.sound]
KSolveInst.rotate_inst : [propext, Classical.choice, Quot.sound]
KSolveInst.translate_inst : [propext, Classical.choice, Quot.sound]
$ grep -n "sorry|admit|native_decide|^axiom" RBM3D/BA/KSolve.lean | wc -l
       0
$ name-clash: for each new public name, grep -rnw NAME RBM3D RBM3D.lean --include=*.lean (excluding RBM3D/BA/KSolve.lean), hit counts
IsKLoopSLe=       0 BAKsolve=       0 BAKsolveLe3=       0 baKsolveLe3_holds=       0 baK_unique=       0 baK_rotate=       0 baK_translate=       0 BAMLoop_rot=       0 BAMLoop_translate=       0 BAMsigma_shift=       0 BAKsol_isKLoopS=       0 BAKsol_rotate=       0 BAKsol_translate=       0 KSolveInst=       0 
```

Target statements, extracted by `python3 stmts.py targets` (declaration text up to `:=`; pins are the three `def`s whose text equals the check file, see `pindiff.py` above):
```
-- KSolve.lean:478-496
theorem baKsolveLe3_holds : ∀ d, BAKsolveLe3 d :=
-- KSolve.lean:521-542
theorem BAMLoop_rot (d L W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) (hσa : σ.length = a.length) :
    BAMLoop d L W M ⟨s :: σ, b :: a⟩ = BAMLoop d L W M ⟨σ ++ [s], a ++ [b]⟩ :=
-- KSolve.lean:546-555
theorem BAMLoop_translate (d L W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (c : Zd d L) (I : LoopIdx (Zd d L)) :
    BAMLoop d L W M ⟨I.σ, I.a.map (· + c)⟩ = BAMLoop d L W M I :=
-- KSolve.lean:558-562
theorem BAMsigma_shift (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (x + c) (y + c) = BAMsigma d L (BAMB d L g z m) σ x y :=
-- KSolve.lean:568-578
theorem baK_unique {K K' : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K)
    (hK' : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K') :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I :=
-- KSolve.lean:582-587
theorem baK_rotate {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length → K t ⟨s :: σ, b :: a⟩ = K t ⟨σ ++ [s], a ++ [b]⟩ :=
-- KSolve.lean:591-597
theorem baK_translate (hMs : ∀ (σ : Bool) (x y c : Zd d L), Ms σ (x + c) (y + c) = Ms σ x y)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      K t ⟨I.σ, I.a.map (· + c)⟩ = K t I :=
-- KSolve.lean:606-615
theorem BAKsol_isKLoopS {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1)
      (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m)) :=
-- KSolve.lean:619-625
theorem BAKsol_rotate {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length →
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: σ, b :: a⟩ =
        BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨σ ++ [s], a ++ [b]⟩ :=
-- KSolve.lean:629-634
theorem BAKsol_translate {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨I.σ, I.a.map (· + c)⟩ =
        BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t I :=
```

Compiled nonempty instances, extracted by `python3 stmts.py inst` (first lines of each statement, full text at the cited lines; `P` = merged flow point `(d,L)=(3,4)`, `BA/MFixedPoint.lean:893`, `W = 2`, `Λ = 10`, `κ = Im m₀`):
```
-- KSolve.lean:655-668
example : ∃ K : ℝ → LoopIdx (Zd 3 4) → ℂ,
    IsKLoopSLe 3 4 2 3 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
  ...  (statement continues)
  (proof term, line 668:)
  baKsolveLe3_holds 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real
-- KSolve.lean:672-686
theorem le3_nondeg : ∃ K : ℝ → LoopIdx (Zd 3 4) → ℂ,
    IsKLoopSLe 3 4 2 3 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
      (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) K ∧
    K 0 ⟨[true, false], [0, 0]⟩ = (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (P.m0 * starRingEnd ℂ P.m0) ∧
    (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (P.m0 * starRingEnd ℂ P.m0) ≠ 0 :=
-- KSolve.lean:690-695
theorem rot_witness :
    BAMLoop 1 3 1 BAMLoop_witM ⟨true :: [true, false], (![0] : Zd 1 3) :: [![1], ![2]]⟩ =
  ...
-- KSolve.lean:698-700
example (σ : Bool) : BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ (![0, 1, 2] + ![1, 0, 0]) (![1, 0, 3] + ![1, 0, 0]) =
    BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ ![0, 1, 2] ![1, 0, 3] :=
-- KSolve.lean:704-718
theorem translate_BAMLoop :
    BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
  ...
-- KSolve.lean:722-731
theorem unique_inst (h : BAKsolve 3) :
    ∃ K : ℝ → LoopIdx (Zd 3 4) → ℂ,
  ...
-- KSolve.lean:735-747
theorem rotate_inst (h : BAKsolve 3) :
    BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
  ...
-- KSolve.lean:751-763
theorem translate_inst (h : BAKsolve 3) :
    BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
  ...
```

N3 table (again, as the ticket requires; same script as section (a), output identical to the 1a `n3.out`):
```
$ cd T2368 && PYTHONPATH=. python3 n3.py > n3b.out; diff n3.out n3b.out && echo identical-to-1a-n3.out; python3 summ.py   (RK4 of treeEqRhsS, S=1, K00 BAMLoop data, vs (Kn2sol),(Kn3sol) as pinned; every sigma, every a)
identical-to-1a-n3.out
24 rows (q in {4,5}, g in {0.2,0.5}, W in {1,2}, t in {0,0.5,0.9}), E=0.3, 800 RK4 steps
max|closed-RK4|: n=2 6.1e-10  n=3 7.5e-09 ; max exact-ODE defect: n=2 1.4e-14  n=3 5.1e-13
t=0 rows: max|closed-RK4| = 0.0
q=4 g=0.2 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 6.1e-10 n=3 7.5e-09 | ODE defect(exact) n=2 7.1e-15 n=3 4.6e-13
q=4 g=0.2 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 3.0e-10 n=3 1.9e-09 | ODE defect(exact) n=2 3.6e-15 n=3 1.1e-13
q=4 g=0.5 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 5.6e-10 n=3 4.8e-09 | ODE defect(exact) n=2 7.1e-15 n=3 6.4e-14
q=4 g=0.5 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 2.8e-10 n=3 1.2e-09 | ODE defect(exact) n=2 3.6e-15 n=3 1.6e-14
q=5 g=0.2 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 5.4e-10 n=3 6.6e-09 | ODE defect(exact) n=2 1.4e-14 n=3 5.1e-13
q=5 g=0.2 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 2.7e-10 n=3 1.6e-09 | ODE defect(exact) n=2 7.1e-15 n=3 1.3e-13
q=5 g=0.5 W=1 E=0.3 t=0.9: max|closed-RK4| n=2 4.4e-10 n=3 3.3e-09 | ODE defect(exact) n=2 7.1e-15 n=3 5.7e-14
q=5 g=0.5 W=2 E=0.3 t=0.9: max|closed-RK4| n=2 2.2e-10 n=3 8.3e-10 | ODE defect(exact) n=2 3.6e-15 n=3 1.4e-14
```

Narrative (stage 1b; every number above is script output):
* Result: the three pins and all nine proved targets are in `RBM3D/BA/KSolve.lean`; `lake build RBM3D.BA.KSolve` succeeds; every axiom list is `[propext, Classical.choice, Quot.sound]`; the file has 767 lines against the stop line 1400 (`wc -l` at the section commits: 495, 635, 764; 767 after the header rewrap). No hypothesis was added, no pin changed, no amend needed: the pins are text-identical to the check file (`pindiff.py`) and `rfl`-equal (`pins.lean`).
* `baKsolveLe3_holds`: the family is the private `BAKSolve_K` (pattern match on `⟨σ, a⟩`: `PropSpin m` at length 1, `(Kn2sol)` at length 2, `(Kn3sol)` at length 3, `0` otherwise). Length 2: the only cut is `(1,2)` (`BAKSolve_rhs_two`); the derivative is `BATheta_hasDerivAt` through `Matrix.mul_apply` (`BAKSolve_mulRight_hasDerivAt`); the weight identity is `W^d (W^d)⁻¹ (W^d)⁻¹ = (W^d)⁻¹` (`BAKSolve_wc_pow`), true in ℂ also at `W^d = 0`.
* Length 3: `BAKSolve_tau ℬ A B C` is the triple sum with weight `ℬ = BAMLoop`; `BAKSolve_tau_hasDerivAt` is the product rule on the three leaves; `BAKSolve_rhs_three` lists the cuts `(1,2)`, `(1,3)`, `(2,3)`; `BAKSolve_tau_leg1/2/3` turn `Σ_a X(a_v, a) τ(… a …)` into `τ(… X·A …)` on leaf `v`. The cut `(1,3)` carries the charge pair `(σ₁,σ₃)`, so it is converted to `(σ₃,σ₁)` by `BATheta_swap`, `BAKSolve_Mss_swap` (the `e` inside `BATheta_swap` is not a lemma, so it is reproved) and the symmetry of `ΘM` (`BAKSolve_ThQ_symm`, from `BATheta_isSymm` and the commutation `BAKSolve_comm`, itself from `BATheta_resolvent`). `W^d (W^d)⁻¹` is absorbed by the weight (`BAKSolve_wc_BAMLoop`, `BAMLoop` has length `≥ 2`).
* Initial data: `BAKSolve_Theta_zero` (`Θ_0 = 1`), `BAKSolve_tau_one`, and `simp` on `BAMLoop`, `BAMss` at length 2 (`BAKSolve_zero`).
* Hypotheses of `baKsolveLe3_holds`: only `BAReal` and `0 ≤ t < 1` are used; `3 ≤ L` only supplies `NeZero L`; `0 < Λ, 0 < κ, 0 < g, g ≤ Λ` of the pin are not used; `W : ℕ` is arbitrary.
* K01 instances: `BAMLoop_rot` by `BAMLoop_apply` and a cyclic reindexing of the product over `range (n+1)` (`BAKSolve_getD_snoc`, `BAKSolve_prod_rot`); `BAMLoop_translate` by `List.map_rotate`, `List.zip_map`; `BAMsigma_shift` from `BAMB_shift`; `baK_unique` takes the `2`-loop bounds of both families from `retireS_holds` (`R = max R R'`) and applies `uniqS_holds`; `baK_rotate`, `baK_translate` apply `rotS_holds`, `translS_holds` with `kernel_one_rot_transl`. `BAKsol_*` follow with `BAKsol_isKLoopS` and `BAMsigma_shift`.
* Instances: data `P` (`BA/MFixedPoint.lean:893`), `W = 2`, `Λ = 10`, `κ = Im m₀`. `le3_nondeg`: the `2`-loop at `t = 0`, `σ = (+,-)`, `a = (0,0)` is `8⁻¹ m₀ conj m₀ ≠ 0`. `unique_inst`, `rotate_inst`, `translate_inst` need a family at all lengths, which only `BAKsolve 3` (K05b's pin, not proved here) provides: it stays a hypothesis of those three (CLAUDE.md §4 step 2). `rot_witness` (K00 witness, value `15`) and `translate_BAMLoop` carry no pin hypothesis.
* The 1a instance (`d = 1, L = 5`) is numerical; the Lean instance uses the merged `P` instead of `inst_flow_real 0`, for which 1a noted `0 < g` is still to be shown. Section (a) is not edited and needs no (a′).

## (c) Verified names (all compile in `KSolve.lean`; `names.lean` printed `present: 40/41; absent: [List.getD_singleton_default_eq]`)
* `HasDerivAt.fun_sum`, `.mul`, `.mul_const`, `.const_mul`, `.congr_deriv` (Mathlib `Analysis/Calculus/Deriv/{Add,Mul}.lean`).
* `Finset.sum_comm`, `.mul_sum`, `.sum_mul`, `.sum_congr`, `.sum_insert`, `.sum_singleton`, `.sum_empty`, `.sum_add_distrib`, `.prod_congr`, `.prod_range_succ`, `.prod_range_succ'`.
* `List.getD_append`, `.getD_append_right`, `.getD_cons_succ`, `.map_rotate`, `.zip_map`, `.zip_map_right`, `.map_map`, `.map_congr_left`, `.length_eq_three`; `Nat.mod_add_mod`, `.mod_self`, `.mod_eq_of_lt`, `.lt_succ_iff_lt_or_eq`.
* `smul_right_injective`, `mul_inv_cancel₀`, `inv_ne_zero`, `Complex.star_def`, `Matrix.mul_assoc`, `.mul_apply`, `.transpose_mul`, `.one_apply`, `.one_mul`.
* Verified absent: `List.getD_singleton_default_eq` (`unknown constant`, tool log of the first name probe).
* Merged project names used: `BATheta_hasDerivAt`, `BATheta_resolvent`, `BATheta_swap`, `BATheta_isSymm` (`BA/KBase.lean`), `BAMLoop_apply`, `BAMLoop_witM`, `BAMLoop_witness`, `BAMB_shift`, `BAMB_symm`, `BAMB_diag_eq` (`BA/Ward.lean`), `retireS_holds`, `uniqS_holds`, `exists_eq_of_length_two` (`Loop/Unique.lean`), `rotS_holds`, `translS_holds`, `kernel_one_rot_transl` (`Loop/KLUnique.lean`), `P` (`BA/MFixedPoint.lean`).

## (d) Open issues and paper-delta candidates
* **T2368a** (`BAKsolve`, `BAKsolveLe3` carry no `1 ≤ W`): the pins quantify `W : ℕ`; the paper has `W ≥ 1`. The Lean statement is stronger and is proved: at `W^d = 0`, `(W^d)⁻¹ = 0` in ℂ and both sides vanish. Candidate: record as a harmless strengthening.
* **T2368b** (`(Kn3sol)`, `1_2:1176`): proved as pinned, i.e. with the K00 convention (D632: `σ_i` on `(a_{i-1}, a_i)`) and as one tree (D634); leaf `v` carries `Θ^{(σ_v,σ_{v+1})}`. No new difference; the negative control of (a) (`Θ^{(σ_v,σ_v)}`: error `1.96e-01`) shows the convention is binding.
* **T2368c** (ticket text): `T2368.md` line 15 says the cuts of a 3-loop are "2-loops, and 1-loops"; the cuts have lengths 2 and 3 only (`BAKSolve_rhs_three`, `two_le_length_cutGlueL/R`); the length-1 clause of `IsKLoopSLe` enters no cut at `n ≤ 3`. Candidate: wording fix.
* Open: `unique_inst`, `rotate_inst`, `translate_inst` are conditional on `BAKsolve 3` (K05b). `baK_unique/rotate/translate` are the `S = 1` instances of the generic pins, not new general statements (CLAUDE.md §5.6). `BAKSolve_Msigma_symm` copies the private `BAKBase_Msigma_symm` (`BA/KBase.lean:304`), which cannot be imported.

## Repair (Amend 1, repairer claude-opus-5-5, Sat Oct 10 04:06:15 UTC 2026)
Scope: `docs/tickets/T2368-amend-1.md`: register `RBM.BA.BAKsolve` in `owedProps` of `RBM3D/Test/Axioms.lean`; `RBM3D/BA/KSolve.lean` unchanged.
```
$ git log --oneline -1; git diff --stat 057f0f4..HEAD
f3004f5 T2368: register owed premise RBM.BA.BAKsolve in owedProps (Amend 1)
 RBM3D/Test/Axioms.lean | 1 +
 1 file changed, 1 insertion(+)
$ git diff 057f0f4..HEAD | grep "^[+-][^+-]" | cut -c1-110
+   `RBM.BA.BAKsolve, -- existence of the BA `𝒦` on `[0,1)` with `(Kn2sol)` (`1_2:1175`), hypothesis of `BAKso
$ cat RegCheck.lean   # temporary, uncommitted, in the scratchpad
import RBM3D
import RBM3D.BA.KSolve

#assert_rbm_axioms
$ lake env lean RegCheck.lean; echo "exit $?"   (output excerpt: head -3, grep BAKsolve/registry/error)
exit 0
axiom audit: 10762 theorems, 3156 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
47:  RBM.BA.BAKsolve: 6 [no certificate]
registry: 2 borrowed + 126 owed + 109 structural + 7 refuted + 14 superseded; 124 register
$ lake build 2>&1 | tail -1   (full library, worktree, run before the commit on the same working tree)
Build completed successfully (4177 jobs).
```
