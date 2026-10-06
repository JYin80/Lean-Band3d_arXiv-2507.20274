Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 10:26 UTC 2026

Scripts (Python, no Lean) in `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2281/`: `lib.py`, `table.py`, `far2.py`, `far.py`, `farfft.py`, `near2.py`. `T = sfT`, `d = 3`, `ξ = T` or random symmetric `ξ ≤ T`, `θ` = max row sum of `ξ²`, `C` omitted.

### (i) Exponent table

| quantity | value / constraint | slack |
|---|---|---|
| far `C` (`AnpDetFarAt`) | depends on `Γ,d`; uniform in `L,W,g,t,θ,ℓ≥0,ξ,a,b` | **none at `q=0`**: ratio `T(0)/T(ℓ)` unbounded in `ℓ` (below) |
| far `θ^q`, `T(0)^{ord-p}`, `T(ℓ)^p` | `figAux`: `q=2`, `ord=6-4=2`, `ord-p=0`; `anpKey_oneEdge` (`AnpKey.lean:843`): `q=0`, `ord=1`, `ord-p=0` | `figAux` ratios `≤ 0.55` (far2, far.py); `oneEdge` unbounded |
| far domain `𝐃_{>ℓ}` | restricts internal labels only (check file `farD`); a path with no internal vertex is unconstrained | `q=0`: `D^0` = one point, `a,b` arbitrary |
| near `Λ^{2q}(W^d(1-t))^{-q}` | `figAux`: `q=2`; `Λ = ℓ/ℓ_t` minimal, `1 ≤ ℓ ≤ Λ ℓ_t` | `ℓ=1,2,3`, `ℓ_t=1`: `Λ²/(W^d(1-t)) = 0.25, 1, 2.25` at `t=.5` |
| near `Ψ^{ord-p}` | `= Π_j Ψ^{k_j-2} · Ψ^{#dropped edges}`; `figAux`: `k=(2,2)`, `ord-p=0`; `loopG` below: `ord-p=2` | `T(0) ≤ Ψ`: `0.40825 ≤ 0.40855` (slack `3.1e-4`) |
| `EKTTk` premises | `3≤d`, `2≤k`, `0<W`, `0≤g`, `t<1`, `g² ≤ L²(1-t)`, `1≤ℓ≤Λ ℓ_t`, `D ⊆ {α: |a-α|_1 ≤ ℓ}` (`nearD` gives it) | `0.25 ≤ 50` at `L=10,g=.5,t=.5` |
| `ℓ_t=ellT` | `(g,t)=(.5,0),(.5,.5)`: 1; `(3,0)`: 3; `(3,.5)`, `L≥6`: 4.243 | `ℓ_t ≥ 1` always |
| `C_near` | depends on `Γ,d` only: product of `EKTTk` constants for `k ≤ |es|` | max ratio over tests `2.6` (below) |
| norms | far, `farD`: `zdistInf`; near, `nearD`, `EKTTk`: `zdistD`; `zdistInf ≤ zdistD`, so `T(zdistD) ≤ T(zdistInf)` | edge premise `ξ ≤ T(zdistInf)` does not give `ξ ≤ T(zdistD)` (S2, iii-2) |

### (ii) Concrete instance and tests

```
$ cd $S && python3 table.py
instance L=10 W=2 g=0.5 t=0.5 d=3 : g^2=0.25 <= L^2(1-t)=50.0 ; ellT=1 ; 1-t=0.50
T(0)=0.40825 Psi=0.40855 (T(0)<=Psi, slack 3.06e-04) ; T(1,2,3)=0.17509 0.11622 0.08586
theta=max_a sum_b T(zdistInf)^2=6.44028 ; (W^d(1-t))^-1=0.25000
 ell=1 Lam=ell/ellT=1  Lam^2/(W^d(1-t))=0.25000  1<=ell<=Lam*ellT ok=True
 ell=2 Lam=ell/ellT=2  Lam^2/(W^d(1-t))=1.00000  1<=ell<=Lam*ellT ok=True
 ell=3 Lam=ell/ellT=3  Lam^2/(W^d(1-t))=2.25000  1<=ell<=Lam*ellT ok=True
figAux nonempty: far ell=2 |D>ell|=925 of 1000 (a_i=a, b_i=b, |a-b|_inf=2) ; near ell=3 |D<=ell|=25
```
At this data every hypothesis of `AnpDetFarAt 3 figAux` (`ξ=T`, `θ=6.44`, `ℓ=2`) and `AnpDetNearAt 3 figAux` (`ℓ=3`, `Λ=3`) holds with `D` nonempty (no external hypothesis in either pin).

**(1) `AnpDetFarAt` first.** `Γ = anpKey_oneEdge` (`p=1,q=0`, one solid edge `a_0 — b_0`; merged `IsNested`, `AnpKey.lean:847`; `NoGhost`: its only edge has `ghost = false`, `:844`). `valOnD` over `Fin 0 → D` is one term, so `valOnD = ξ(a_0,b_0)`; `farD` is not used. Take `a_0=b_0`, `ξ = sfT(zdistInf)` (symmetric, `≥0`, `≤ sfT`; `θ` any value `≥ max_α Σ_β ξ²`): LHS `= sfT(0)`, RHS `= C θ^0 sfT(0)^{1-1} sfT(ℓ) = C sfT(ℓ)`.
```
$ cd $S && python3 - <<'EOF'   # lib.sfT, L=10 W=2 g=.5 t=.5
q0 far, oneEdge, a_0=b_0, xi=sfT, L=10 W=2 g=.5 t=.5 : ratio LHS/RHS(C=1)=sfT(0)/sfT(ell):
  ell=1  2.33164
  ell=3  4.75489
  ell=10  16.1204
  ell=100  1491.53
  ell=10000  5.18496e+23
```
`sfT(0)/sfT(ℓ) = (ℓ+1)^{1/2} e^{½√(ℓ/ℓ_t)}` (`d=3`) `→ ∞`, with `ℓ ≥ 0` free in the pin; no uniform `C`. Same ratio in every `(L,W,g,t)` with `ℓ_t = 1`; `L=3,W=1,g=1,t=0` gives identical values. Random nested graphs with `q=0` (generator: own, seed 2281, since `find` located no `graphs.py` of T2264 (only `blueprint/cowork/graphs.py`, an SVG file)):
```
$ cd $S && python3 far.py 7 0
L,W,g,t= 7 2.0 0.5 0.0 ellT= 1.0 theta(xi=T)= 2.337 graphs: 60 {'q0': 20, 'q>=1, every path meets an internal vertex': 31, 'q>=1, some path external-only': 9}
q0  max LHS/(theta^q T(0)^(ord-p) T(ell)^p) by ell: {0.5: 5.31, 1: 12.7, 1.5: 24.8, 2: 43.3, 2.5: 70.2, 3: 108.0}
q>=1, every path meets an internal vertex  max ...: {0.5: 0.188, 1: 0.333, 1.5: 0.511, 2: 0.489, 2.5: 0.671, 3: 0.0}
q>=1, some path external-only  max ...: {0.5: 0.357, 1: 0.486, 1.5: 1.3, 2: 0.41, 2.5: 0.732, 3: 0.0}
```
(`ℓ=3` row `0.0`: `D` empty at `L=7`.) So `AnpDetFarAt` fails for `q=0` and grows with `ℓ`; for `q ≥ 1` no violation is seen at this scale.

**(S1) configuration** (`p=1` is not nested for `q ≥ 1`: property (2) needs two paths through each internal vertex, so the configuration is embedded in `figAux`, `a_0=a_1=a`, `b_0=b_1=b`, `|a-b| = 2.5ℓ`):
```
$ cd $S && python3 far2.py
== figAux far (p=q=2, ord-p=0): ratio = LHS/(theta^2 T(ell)^2), theta=max row sum of xi^2, C omitted ==
L=6 W=2 g=0.5 t=0  max ratio ell=1,2,3 (40 random a_0,a_1,b_0,b_1 x {xi=T, rand}): [0.424, 0.219, 0.0]
L=6 W=2 g=0.5 t=0.5  max ratio ell=1,2,3 (...): [0.388, 0.175, 0.0]
L=10 W=2 g=0.5 t=0  max ratio ell=1,2,3 (...): [0.184, 0.397, 0.543]
L=10 W=2 g=0.5 t=0.5  max ratio ell=1,2,3 (...): [0.185, 0.404, 0.463]
S1 config L=10 |a-b|_inf=5=2.5*ell, ell=2: ratio=0.4791 ; share of LHS from labelings with every edge <= ell: 0.0317
```
Growth in `ℓ/ℓ_t` (`a_0=a_1=a`, `b_0=b_1=b`, `|a-b|=1.5ℓ`, `L=128`, FFT, `farfft.py`, `ℓ` list edited to 4,8,..,28):
```
$ cd $S && python3 -W ignore farfft.py 128      (column |a-b|/ell = 1.5)
ell= 4: 0.0576   ell= 8: 0.1347   ell=12: 0.2122   ell=16: 0.2822   ell=20: 0.3427   ell=24: 0.3956   ell=28: 0.4476
```
Increments fall (`.077,.078,.070,.060,.053,.052`); not conclusive: the true large-`ℓ/ℓ_t` behaviour of `q ≥ 1` is **not settled** by these runs (sub-exponential "one big jump" heuristic suggests a bounded ratio at `|a-b|/ℓ > 1`, unproved).

**(2) `AnpDetNearAt`.** Ratio `LHS / [(Λ²/(W^d(1-t)))^q Ψ^{ord-p} T(|a-b|_1∧ℓ)^p]`, `Λ = ℓ/ℓ_t`, `L=6`, 12 random `(a,b)` × `{ξ=T, random ξ≤T}`; `loopG` = `p=2,q=1`, path 0 `a_0→a_1→α→a_1→b_0`, path 1 `a_1→α→b_1` (edges 0–5; satisfies `IsNested` (1)–(6) by inspection: no loop, `α` on both paths, Hall for `{α}`):
```
$ cd $S && python3 near2.py
ordN(figAux)= 2 p=2 q=2 -> Psi power ord-p = 0 ; ordN(loopG)= 4 -> ord-p = 2
figAux          L=6 W=2 g=0.5 t=0   max ratio ell=1,2,3: [0.0, 0.242, 0.159]
figAux          L=6 W=2 g=0.5 t=0.5 max ratio ell=1,2,3: [1.35, 0.185, 0.0841]
figAux          L=6 W=2 g=3   t=0   max ratio ell=1,2,3: [2.49, 0.695, 0.383]
loopG (x=y)     L=6 W=2 g=0.5 t=0   max ratio ell=1,2,3: [0.942, 0.299, 0.161]
loopG (x=y)     L=6 W=2 g=0.5 t=0.5 max ratio ell=1,2,3: [0.104, 0.249, 0.039]
loopG (x=y)     L=6 W=2 g=3   t=0   max ratio ell=1,2,3: [0.0, 0.0975, 0.29]
40 random loop-free nested, q<=2  g=0.5 t=0:   [2.03, 1.0, 1.0]   t=0.5: [1.0, 1.0, 1.0]   g=3 t=0: [2.6, 1.0, 1.0]
```
Bounded (`≤ 2.6`) everywhere; no violation.

**(3) Negative controls.** (a) Dropping `T(ℓ)^p` in far: the `q=0` rows above are the violation (`108` at `ℓ=3` and growing). (b) `k=1` (`n=1` instead of `2`): `near2.py` prints max ratio `1.73` for `k=1` vs `0.69` for `k=2` at `L=6..18`, `W=2,g=.5,t=0,ℓ=3`: no failure at this scale, so the paper's "fails when `k=1`" (`7_8:1700`) is not reproduced numerically; it only affects the exponent `Ψ^{k-2}` and `EKTTk` assumes `2 ≤ n`.

### (iii) Inspection

1. **Path-preserving graph.** Summing internal `α` visited by `k ≥ 2` passages `x_i→α→y_i` (`IsNested` (2)) via `ekTTk_holds d k` (`D = nearD ⊆ {|a-α|_1≤ℓ}`) and replacing each by an edge `x_i y_i` keeps (2), (3), walks, edge-disjointness and `Nodup` (`Visits` of the other vertices unchanged), `NoGhost`, `q-1`, `ordN' = ordN - k + 2` (`solid' = solid - k`). **Two defects of the ticket's step statement:** (A) if some passage has `x_i = y_i` (path `…→x→α→x→…`, two parallel edges `xα`; present in `loopG`), the new edge is a self-loop and `IsNested` (1) (`LWVocab.lean:338`, `e.u ≠ e.v`) fails; such a loop is bounded by `T(0) ≤ Ψ` (`sfT_zero_le_PsiT`) and may be deleted with `ordN' = ordN-k+2-1`, `Ψ` gaining one power; the induction invariant must be "nested without (1), loops deleted". (B) Edges at `α` on no path are bounded by `T(0) ≤ Ψ` and deleted, same bookkeeping, `Ψ^{ord-p}` total unchanged. The sum must be run on `ξ' = sfT(min(zdistD,ℓ))` (monotone, `ξ ≥ 0`), because the new edges are `T`-edges. At `q=0` each path carries one edge with labels `(a,b)` (a path from label `a` to label `b` has an `a→b` step; paths are edge-disjoint), `≥ p` factors `T(|a-b|∧ℓ)`, the rest `≤ T(0) ≤ Ψ`.
2. **Norms (S2).** `ξ ≤ T(zdistInf)` (`LWLoopExp` is stated with `zdistInf`, `LWPins.lean:274-279`) does not imply `ξ ≤ T(zdistD ∧ ℓ)`: `T(zdistD) ≤ T(zdistInf)`, ratio up to `e^{½(√(d r)-√r)/√ℓ_t}`. LW-13b cannot feed `AnpDetNearAt` from `LWLoopExp` without an `ℓ¹` edge bound or a `zdistInf` variant of `EKTTk`.
3. **Far, structure.** The merged `anpKey_long_edge` gives length `≥ ℓ/len` only (S1); the `q=0` failure above is independent of S1 and of the union bound.

### Verdicts

- `lwMomExp_far : ∀ d, AnpDetFar d` — **FAIL.** `AnpDetFarAt 3 anpKey_oneEdge` is false (script above): `D` constrains only internal labels, so for a path with no internal vertex the claimed factor `T(ℓ)` is false for any `ℓ > |a_0-b_0|`. Not repaired here (ticket: stop after 1a). `q ≥ 1` with every path meeting an internal vertex is not refuted and not proved (S1 open); the dispatcher must choose the corrected pin (e.g. add "every path visits an internal vertex", or constrain external labels in `farD`).
- `lwMomExp_near : ∀ d, AnpDetNear d` — **PASS** (no violation in the tests; route via `ekTTk_holds` closes the exponent count), on condition of the corrected invariant in (iii)-1.
- `lwMomExp_near_step` — **PASS only in the corrected form** of (iii)-1 (loop deletion, extra-edge deletion); as described in the ticket ("new graph again `IsNested`") it is false for `loopG`.
- `lwMomExp_inst_far` (`AnpDetFarAt 3 figAux`): hypotheses hold nondegenerately (above); instance true numerically but cannot be obtained from `lwMomExp_far`.

Paper-delta candidates: `T2281a` `7_8:1636-1640` (`𝐃_{>ℓ}` restricts internal vertices only; "each path contains a long ending edge" fails for paths with no internal vertex and, per S1, edges `≈0.83ℓ`); `T2281b` `7_8:1602`; `T2281c` norms `claim:TTk` (`ℓ¹`) vs `(eq:LW_moment_exp)` (`zdistInf`).

## (b) Script output (stage 1b, Tue Oct  6 11:14:56 UTC 2026)
Scripts and scratch files are in `S` (the scratchpad `T2281/`, as in (a)); every output below is verbatim.

```
$ cd RBM3D-wt/T2281 && git log -1 --format="%h %an <%ae> %s"
350ef0c Jun Yin <321276894+JYin80@users.noreply.github.com> T2281: LW-13a near part: lwMomExp_near, corrected step lwMomExp_near_step', instances
$ git diff main...t/T2281 --stat
 RBM3D/Graph/LWMomExp.lean | 1086 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1086 insertions(+)
$ wc -l RBM3D/Graph/LWMomExp.lean
    1086 RBM3D/Graph/LWMomExp.lean
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWMomExp.lean; echo "grep exit $?"
grep exit 1
$ grep -c "farD\|AnpDetFar\|NearStepShape" RBM3D/Graph/LWMomExp.lean
0
$ lake build RBM3D.Graph.LWMomExp 2>&1 | grep -E "LWMomExp|Build completed|error"
Build completed successfully (3352 jobs).
(exit 0)
$ lake env lean axioms.lean   # import RBM3D.Graph.LWMomExp; #print axioms of the 6 public declarations
'RBM.Graph.lwMomExp_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_near_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_near_step'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_inst_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_inst_near_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExp_inst_step' depends on axioms: [propext, Classical.choice, Quot.sound]
(exit 0)
$ lake env lean pincheck.lean ; echo "(exit $?)"   # pincheck.lean = check-file section 2 (near part, namespace RBM.Graph.T2281Check) + the examples below
39:example : T2281Check.AnpDetNear 3 := lwMomExp_near 3
41:example : T2281Check.AnpDetNearAt 3 figAux := lwMomExp_inst_near
43:example : ∀ d, T2281Check.AnpDetNear d := lwMomExp_near
(exit 0)
$ python3 pindiff.py   # whitespace-normalised text of the pin blocks, check file vs LWMomExp.lean (prefix rename valOnD -> lwMomExp_valOnD, nearD -> lwMomExp_nearD)
AnpDetNearAt  (check file) vs AnpDetNearAt       (LWMomExp.lean): IDENTICAL after the prefix rename
AnpDetNear    (check file) vs AnpDetNear         (LWMomExp.lean): IDENTICAL after the prefix rename
valOnD        (check file) vs lwMomExp_valOnD    (LWMomExp.lean): IDENTICAL after the prefix rename
nearD         (check file) vs lwMomExp_nearD     (LWMomExp.lean): IDENTICAL after the prefix rename
```

Target statements (extracted from the file by `extract.py` / `extract2.py`; the pin text is the check file text, no added hypothesis):
```
-- RBM3D/Graph/LWMomExp.lean:900
def AnpDetNearAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistD d L (α - β) : ℕ) : ℝ) ℓ)) →
        ∀ a b : Zd d L,
          lwMomExp_valOnD Γ ξ (fun _ => a) (fun _ => b) (lwMomExp_nearD d L a b ℓ) ≤
            C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
              sfT d L W g t (min ((zdistD d L (a - b) : ℕ) : ℝ) ℓ) ^ p

-- RBM3D/Graph/LWMomExp.lean:911
def AnpDetNear (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → AnpDetNearAt d Γ

-- RBM3D/Graph/LWMomExp.lean:1023
theorem lwMomExp_near : ∀ d, AnpDetNear d

-- RBM3D/Graph/LWMomExp.lean:662
theorem lwMomExp_near_step' (d N : ℕ) (hd : 3 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ a b : Zd d L,
      ∀ {p q : ℕ} (m : Fin p → List (NV p (q + 1))),
        ∑ i, ((m i).length + 1) ≤ N → (∃ i i', i ≠ i' ∧ Sum.inr 0 ∈ m i ∧ Sum.inr 0 ∈ m i') →
        lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b m ≤
          K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) * PsiT d L W g t ^ ((lwMomExp_occ m : ℤ) - 2) *
            lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b
              (lwMomExp_del m)

-- RBM3D/Graph/LWMomExp.lean:1036
theorem lwMomExp_inst_near : AnpDetNearAt 3 figAux

-- RBM3D/Graph/LWMomExp.lean:1053
theorem lwMomExp_inst_near_pt : ∃ C : ℝ, 0 < C ∧
    (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2).Nonempty ∧
    lwMomExp_valOnD figAux (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2) (fun _ => (0 : Zd 3 6))
        (fun _ => (Pi.single 0 1 : Zd 3 6)) (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2) ≤
      C * ((2 : ℝ) ^ 2 * (((2 : ℝ) ^ 3)⁻¹ / (1 - 1 / 2))) ^ 2 *
        PsiT 3 6 2 (1 / 2) (1 / 2) ^ (figAux.ordN - ((2 : ℕ) : ℤ)) *
        sfT 3 6 2 (1 / 2) (1 / 2) (min ((zdistD 3 6 ((0 : Zd 3 6) - Pi.single 0 1) : ℕ) : ℝ) 2) ^ 2

-- RBM3D/Graph/LWMomExp.lean:1072
theorem lwMomExp_inst_step : ∃ K : ℝ, 0 < K ∧
    lwMomExp_sysVal (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2)
        (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2) 0 (Pi.single 0 1) (lwMomExp_sysOf figAux) ≤
      K * ((2 : ℝ) ^ 2 * (((2 : ℝ) ^ 3)⁻¹ / (1 - 1 / 2))) *
        PsiT 3 6 2 (1 / 2) (1 / 2) ^ ((lwMomExp_occ (lwMomExp_sysOf figAux) : ℤ) - 2) *
        lwMomExp_sysVal (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2)
          (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2) 0 (Pi.single 0 1)
          (lwMomExp_del (lwMomExp_sysOf figAux))

-- RBM3D/Graph/LWMomExp.lean:147
def lwMomExp_sysVal {ι : Type*} (w : ι → ι → ℝ) (D : Finset ι) (a b : ι) {p q : ℕ}
    (m : Fin p → List (NV p q)) : ℝ
241:def lwMomExp_del {p q : ℕ} (m : Fin p → List (NV p (q + 1))) : Fin p → List (NV p q) :=
245:def lwMomExp_occ {p q : ℕ} (m : Fin p → List (NV p (q + 1))) : ℕ :=
521:noncomputable def lwMomExp_tau (d L : ℕ) (W g t ℓ : ℝ) (u v : Zd d L) : ℝ :=
833:def lwMomExp_sysOf : Fin p → List (NV p q) := fun i => ((Γ.path i).map Prod.snd).dropLast
```

Registry pre-check (`registry.lean` = `import RBM3D`, `import RBM3D.Graph.LWMomExp`, `import RBM3D.Test.Axioms`, `#assert_rbm_axioms`), with and without the new module, and the whole library:
```
exit with module: 0
exit baseline (no LWMomExp): 0
$ diff registry.out registry0.out   # with vs without the new module
1c1
< axiom audit: 8182 theorems, 2662 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 8174 theorems, 2650 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake build 2>&1 | tail -2   # in the worktree; exit 0
non-vacuity certificates: 0 of 148 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4088 jobs).
```

Name-clash and port checks (new public names: `lwMomExp_*`, `AnpDetNearAt`, `AnpDetNear`; every other helper is `private`):
```
$ grep -rnE "lwMomExp_|AnpDetNear" RBM3D --include="*.lean" | grep -v RBM3D/Graph/LWMomExp.lean | wc -l   # worktree
       0
$ same over /Users/junyin/Lean_proof/RBM3D/RBM3D (main worktree) | wc -l
       0
$ same over T2279.md T2280.md checks/T2279-check.lean checks/T2280-check.lean (drafts) | wc -l
0
$ git ls-tree -r main --name-only | grep -c RBM3D/Graph/LWMomExp.lean
0
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; git grep -cE "lwMomExp_|AnpDetNear" (RBM2D, RBM1D)
9e0f275
       0
de0de42
       0
```

Narrative.
1. Scope (amendment 1, `docs/tickets/T2281-amend-1.md`): the near part only.  The file declares no far vocabulary (`grep -c` above is 0).  Delivered: `lwMomExp_near : ∀ d, AnpDetNear d` (line 1023; per-graph form `lwMomExp_near_graph`), the corrected step `lwMomExp_near_step'` (line 662) and the instances `lwMomExp_inst_near`, `lwMomExp_inst_near_pt`, `lwMomExp_inst_step`.  One file is touched (`git diff --stat`), no registry line (the ledger diff shows only the declaration counts).  No (a′): I found no mistake in (a) that changes a verdict; the near verdicts of stage 1a stand.
2. Route, with the lemma names of the file.
   - `ξ ≥ 0` and `ξ ≤ τ = lwMomExp_tau` pointwise, so the value is at most the same product with `τ`.
   - Edges on no path: `τ ≤ sfT 0 ≤ PsiT` (`lwMomExp_tau_le`, `sfT_zero_le_PsiT`); `lwMomExp_prod_split` splits `∏_k` into the path edges times the others (from `IsNested`: Nodup and edge-disjoint paths).
   - A path (`WalkOK`) is the vertex sequence `lwMomExp_sysOf Γ i` (`lwMomExp_walk_chain`, `lwMomExp_walk_last`, `lwMomExp_walk_visit`); the value is `lwMomExp_sysVal`.
   - The step: `lwMomExp_marks` (a sequence with the summed vertex marked factors as `R · Π_passages τ(x,c) τ(c,y) · τ(c,c)^r`; the sequence with it deleted is `R · Π τ(x,y)`), then `lwMomExp_step_aux` applies the merged `ekTTk_holds` (one `K` for all `2 ≤ k ≤ N`: `lwMomExp_exists_K`); the power of `Ψ` is `A - 2`, `A` the number of occurrences of the vertex (`lwMomExp_occ`).
   - Induction `lwMomExp_sys_bound`: `q+1 → q` by `lwMomExp_del` (delete the first internal vertex, renumber); at `q = 0` `lwMomExp_base` (all labels in `{a, b}`: one step `τ(a,b)`, the others `≤ sfT 0`).
3. Differences from the ticket text.  (i) The step is the corrected one of amendment 1, stated for path systems (vertex sequences between `a_i` and `b_i`), not for `NGraph`: a passage `x → α → y` with `x = y`, or a step `α α`, stays a step of weight `sfT 0 ≤ PsiT`; no loop is created or deleted, so the first conjunct of `IsNested` (`e.u ≠ e.v`) plays no role, and the exponent is `A - 2` with `A = k +` (number of steps `α α`).  Edges on no path are bounded once, in `lwMomExp_near_graph` (amendment (B)).  `NearStepShape` is not used.  (ii) `lwMomExp_near_graph` uses of `IsNested` only the projections `.2.1` (walks), `.2.2.1` (Nodup), `.2.2.2.1` (edge-disjoint), `.2.2.2.2.1` (two distinct paths through each internal vertex): `grep -on "hN\(\.[12]\)\+"` gives exactly these four; the no-loop and Hall conjuncts are not used.  (iii) The symmetry part of the hypothesis on `ξ` is not used (kept as pinned).  (iv) `C = K^q`, `K` depends on `d` and `N = Σ_i |path i|` only; `L, W, g, t, ℓ, Λ, ξ, a, b` come after `C`, as pinned.
4. Not here: the far bound (amendment 1); `LWMomentExp`, `LWMoment` (registry lines untouched).
5. Size: the file has 1086 lines (`wc -l` above); the amendment target `≤ 1000` is not met (86 lines over).

## (c) Verified Mathlib and repository names (each used in a compiled proof of the file; build log above)
- `Finset.sum_nbij'`, `Finset.sum_product'`, `Finset.sum_comm`, `Fintype.mem_piFinset`, `Fin.forall_fin_succ`, `Fin.cons`, `Fin.tail`, `Fin.cases`: `lwMomExp_sum_succ`, `lwMomExp_phi`.
- `Finset.prod_biUnion`, `Finset.card_biUnion`, `List.prod_toFinset`, `List.toFinset_card_of_nodup`, `Finset.prod_mul_prod_compl`, `Finset.card_add_card_compl`, `Fintype.card_fin`: `lwMomExp_prod_split`, `lwMomExp_pathEdges_card`.
- `Finset.prod_le_prod₀` (ordered-semiring form `(∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ g i)`), `Finset.sum_le_card_nsmul`, `Fintype.card_piFinset`, `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Finset.sum_pair`, `Finset.sum_le_sum_of_subset`.
- `List.length_filterMap_eq_countP`, `List.length_eq_countP_add_countP (p) {l}`, `List.countP_le_length` (no explicit argument), `List.countP_eq_length_filter`, `List.countP_congr`, `List.filter_map`, `List.filterMap_map`, `List.map_filterMap`, `List.mem_filterMap`.
- `List.prod_flatten`, `List.map_flatten`, `List.length_flatten`, `List.map_ofFn`, `List.ofFn_comp'`, `List.prod_ofFn`, `List.sum_ofFn`, `List.ofFn_getElem_eq_map`, `List.dropLast_cons_of_ne_nil`, `List.dropLast_singleton`, `Option.isNone_map`.
- `Real.sqrt_le_one` (an iff `√x ≤ 1 ↔ x ≤ 1`), `Real.sqrt_pos`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `zpow_add₀`, `zpow_natCast`, `abs_pos`.
- Repository: `sfT_le_zero_mul`, `sfT_zero_le_PsiT`, `sfT_nonneg`, `one_le_ellT`, `zdistD_neg`, `ekTTk_holds`, `anpKey6_w_nonneg`, `figAux_nested`.
- Verified absent or different (error text in the tool log): `List.ofFn_get_eq_map` (unknown constant); `Fin.mem_piFinset_iff_zero_tail` (unknown constant in this import closure: it is in `Mathlib/Data/Fin/Tuple/Finset.lean`, not imported); `Finset.prod_le_prod` is the ordered-monoid form `[MulLeftMono]`, not usable on `ℝ`.

## (d) Open issues and paper-delta candidates
- Far bound `(adsuu33)`: not here (amendment 1); `AnpDetFarAt 3 anpKey_oneEdge` is false as pinned (script in (a)(ii)(1)), `q ≥ 1` open: back to the dispatcher.
- LW-13b must supply `ξ ≤ 𝖳_t(|·-·|_1 ∧ ℓ)` (`zdistD`); `LWXi`/`LWLoopExp` use `zdistInf` ((a)(iii)-2; candidate `T2281c`).  Not addressed here.
- `T2281a`, `T2281b`, `T2281c` stand as in the last line of (a): `7_8:1636-1640`; `7_8:1602`; `claim:TTk` (`zdistD`) against `(eq:LW_moment_exp)` (`zdistInf`).
- `T2281d` `7_8:1779-1784`: the paper takes `k_1 = Σ r_i` passages, says `𝒢^{(1)}` again satisfies (1)-(3) of `lem:Anp_key` and that `𝒢^{(q)}` "consists solely of `p` solid edges between `[a]` and `[b]`"; a passage `x → α → y` with `x = y` gives a self-loop, which `IsNested` (first conjunct) excludes.  Lean keeps such steps with weight `sfT 0 ≤ PsiT`; the power is `A - 2` per vertex, total `ord - p`, as in `(adsuu_exp2)`.
- `T2281e` `7_8:1662`: `claim:TTk` is stated for `0 ≤ ℓ ≤ (log W)^{10} ℓ_t`; the merged `EKTTk`, hence the pin `AnpDetNearAt` (check file), has `1 ≤ ℓ`.
