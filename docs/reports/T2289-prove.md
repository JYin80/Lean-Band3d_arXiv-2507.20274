Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 11:39:46 UTC 2026

`S` = scratchpad `T2289/` (Python only, no Lean); `T = sfT`, `d = 3`, `ξ = T(min(zdistInf,ℓ))` or `T(·)·U`, `U` random symmetric in `(0,1)`, `θ` = max row sum of `ξ²`; `C` omitted (= 1). Graph checks (`g.py`) re-implement `WalkOK`, `IsNested` (1)-(6), `NoGhost`, `ownExt`, `GhostOK`, `nngh`, `ordN` of `LWVocab.lean:320-365`.

### (i) Exponent table

| quantity | value / constraint | slack |
|---|---|---|
| `C` of both pins | `C := C(Γ^gh)` of `anpDetGh_holds` (`AnpKey6.lean:857`, `C = Π_j max 1 |𝔓_j|`); depends on `Γ`, `d` only; `Γ^gh` has `GhostOK`, `IsNested` | `figAux`: `C = 9`, max ratio `0.992`, so `C = 1` already suffices in all tests below |
| `ψ r := T(min(r,ℓ))` | antitone on `[0,∞)` (`sfT_antitone`, `0 ≤ min r ℓ` as `ℓ ≥ 0`); `ψ r > 0` (`W>0`, `t<1` gives `g²+|1−t|>0`); `ψ 0 = T 0` (`ℓ ≥ 0`); edge premise of `AnpDetGhAt` is literally `ξ ≤ ψ(zdistInf)` | none needed |
| head factor | `ξ(a_i,head) ≤ T(min(|a_i−b_i|,ℓ))`: head `= b_i`: equality of premise; head `= inr α` with `ℓ < |a_i−lab α|`: `ξ ≤ T(ℓ) ≤ T(min(|a_i−b_i|,ℓ))` (`T` antitone, `min(·,ℓ) ≤ ℓ`) | `0` at `|a_i−b_i| ≥ ℓ` (equality `ratio = 1`, `oneEdge` rows) |
| `T(0)` exponent | `ordN(Γ^gh) − nngh(Γ^gh) = (ordN − p) − 0` (`anpKey_ghostify_ord` `p` times, `anpKey_nngh_of_noGhost`) | exact; `figAux`: `2−2 = 0`; `oneEdge`: `1−1 = 0`; `auxQ`: `2−2 = 0` |
| `θ` exponent | `q` (same `q`; `Γ^gh` has the same internal vertices) | exact |
| `nngh(Γ^gh)` | `0` (every path non-empty: `WalkOK` with `a_i ≠ b_i` as vertices; head solid by `NoGhost`; heads distinct edges by `IsNested` (3),(4)); product over paths of `AnpDetGhAt` `= 1`, `c` unused | exact |
| `ℓ` | `0 ≤ ℓ` only (for `ψ 0`); no `ℓ_t`, `Λ`, `log W` | no lower bound; `ℓ = 0` row `ratio ≤ 1` |
| `W, t, g, d, L` | `0 < W`, `t < 1`, `θ > 0`; `g` free; no `3 ≤ d`; no `1−t > ĝ²/L²`; no `L^d ≤ W^K`; no `∀ᶠ n` (§29 (1)-(4), (6)) | none |
| uniformity (§29 (5), (7)) | `C` quantified before `L, W, g, t, θ, ℓ, ξ, a, b, S`; bound exact (no `≺`) | n/a |

### (ii) Concrete instance and tests

**Instance** (`AnpFarAndAt 3 figAux` and `AnpFarHeadAt 3 figAux`; no external hypothesis, `anpDetGh_holds` is merged: no limit computation owed): `L=10, W=2, g=1/2, t=1/2, ℓ=2`, `a_0=a_1=(0,0,0)`, `b_0=b_1=(4,0,0)`, `ξ = T(min(zdistInf,2))`.
```
$ cd $S && python3 -W ignore inst.py
hyp: 0<W=2, t=0.5<1, theta=14.1055>0, ell=2>=0, xi symmetric=True >=0=True edge<=T(min(zdistInf,ell))=True rowsum<=theta=True ; |a-b|_inf=4
graph figAux: IsNested=True NoGhost=True ownExt=True
farDAnd size=775 of 1000 ; piFinset size=600625
AnpFarAndAt: LHS=1.5588  RHS(C=1)=2.68734  ratio=0.5801  (ordN-p=0)
AnpFarHeadAt: heads=[('c', 0), ('c', 0)] HeadFar(all of S)=True |S|=875000  LHS=2.35171 RHS=2.68734 ratio=0.8751
sum_S val(G)=2.35171 <= prod_i T(|a_i-b_i|^ell) * sum_S val(G^gh)=2.35171 ; G^gh: ordN=0 (=2-2), nngh=0, GhostOK=True IsNested=True
```
(`S` of the head line `= {lab : |a_0−lab 0|_∞ > ℓ}`, only the head vertex constrained: a set larger than `farDAnd²`, `HeadFar` holds by construction.)

**Table: the three required graphs** (`figAux`: `p=q=2`; `oneEdge` = `anpKey_oneEdge`: `p=1,q=0`; `auxQ` = the nested output of `lwAuxNested_holds` at `localReg2_inst_Q`: `p=2,q=1`, walks `a_i→c→b_i`), `D = farDAnd^q`, `L ∈ {6,10}`, `t ∈ {0,½}`, `ξ ∈ {T, random}`, `ℓ = 0..3`:
```
$ cd $S && python3 -W ignore tabsum.py | tail -3
 figAux   p=2 q=2 ordN=2 ordN(gh)=0 nngh(gh)=0 GhostOK(gh)=True IsNested(gh)=True heads->['c0', 'c0'] | max ratio ell=0..3: [0.992, 0.836, 0.459, 0.053]
 oneEdge  p=1 q=0 ordN=1 ordN(gh)=0 nngh(gh)=0 GhostOK(gh)=True IsNested(gh)=True heads->['b0'] | max ratio ell=0..3: [1.0, 1.0, 1.0, 1.0]
 auxQ     p=2 q=1 ordN=2 ordN(gh)=0 nngh(gh)=0 GhostOK(gh)=True IsNested(gh)=True heads->['c0', 'c0'] | max ratio ell=0..3: [0.996, 0.892, 0.608, 0.25]
```
**(1) The T2281 1a counterexample passes** (`oneEdge`, `a_0=b_0`, `ξ=T(min(zdistInf,ℓ))`; LHS `= ξ(a,a)`, new RHS `= T(0)^0·T(min(0,ℓ))`, equal):
```
$ cd $S && python3 -W ignore cx1.py | tail -6      # L=10 W=2 g=.5 t=.5
  ell=    1  new ratio=1   old-pin ratio T(0)/T(ell)=2.33164
  ell=  100  new ratio=1   old-pin ratio T(0)/T(ell)=1491.53
  ell=10000  new ratio=1   old-pin ratio T(0)/T(ell)=5.18496e+23
    neg. control (a), oneEdge |a-b|=r<ell, RHS T(ell)^p instead of T(min(r,ell))^p:
  r=1 ell=   10  T(r)/T(ell)=6.91375 ; with correct RHS T(min(r,ell)): 1
  r=5 ell=10000  T(r)/T(ell)=6.92013e+22 ; with correct RHS T(min(r,ell)): 1
```
**(2) Supervisor 1102 family** (`figAux`, `a_0=a_1=a`, `b_0=b_1=b`, `|a−b|=17m`, `ℓ=10m`, `ρ=6m`, `ξ=T(ρ)1[|α−β|≤ρ]`; admissible: `ρ<ℓ`, `T` antitone, script-checked). FFT (`m=1,4`, `L=40,140`), then exact count (balls of `|·|_∞` factorise over coordinates; `L=10⁹`, `ℓ_t=1`):
```
$ cd $S && python3 -W ignore cx2.py
m=1 L= 40 |a-b|=17 ell=10 rho= 6  ell_t=1  xi admissible(truncated premise)=True  theta=2.71
   ball(a,rho)&D_and size=0 (D_and = |c-a|>ell and |c-b|>ell)  LHS_and=0  ratio_and=0 | old farD ('or'): LHS_or=9.079e-05  ratio_or=LHS/(theta^2 T(ell)^2)=0.03213  [T(6m)/T(10m)]^2=3.205
m=4 L=140 |a-b|=68 ell=40 rho=24  ell_t=1  xi admissible(truncated premise)=True  theta=3.508
   ball(a,rho)&D_and size=0 (D_and = |c-a|>ell and |c-b|>ell)  LHS_and=0  ratio_and=0 | old farD ('or'): LHS_or=1.376e-06  ratio_or=LHS/(theta^2 T(ell)^2)=0.02558  [T(6m)/T(10m)]^2=6.823
$ cd $S && python3 -W ignore cx2b.py | sed -n 2,6p   # old farD ("or"); with "and": LHS = 0 for every m (ball(a,6m) ∩ D_and = ∅)
  m=    1  ratio_or=0.032131   [T(6m)/T(10m)]^2=3.2052   N/(12m+1)^6=0.010025
  m=    4  ratio_or=0.023983   [T(6m)/T(10m)]^2=6.8228   N/(12m+1)^6=0.0035151
  m=   10  ratio_or=0.039996   [T(6m)/T(10m)]^2=15.773   N/(12m+1)^6=0.0025358
  m=  100  ratio_or=4.1695   [T(6m)/T(10m)]^2=2075.7   N/(12m+1)^6=0.0020088
  m= 1000  ratio_or=2.0087e+07   [T(6m)/T(10m)]^2=1.0256e+10   N/(12m+1)^6=0.0019587
```
(`m=2,4` FFT values differ from the exact count by torus wrap, `3ρ` = the other way round. The old-domain growth is real but starts only at `m ≳ 30`.)

**(3) Random graphs with `ownExt`** (own generator `rnd.py`, seed 2289; `python3 -W ignore rnd.py`; rejection-filtered by `IsNested`, `NoGhost`, `ownExt`; walks may return to `a_i`/`b_i` mid-path; extra edges between arbitrary vertices):
```
$ cd $S && python3 -W ignore rnd.py
graphs: 65 nested&NoGhost&ownExt, (p,q) counts {(1, 0): 5, (2, 0): 5, (3, 0): 5, (2, 1): 15, (2, 2): 15, (3, 1): 10, (3, 2): 10}; first step to b_i in 33, a_i/b_i revisit mid-path in 53 graphs
violations of [ordN(gh)=ordN-p, nngh(gh)=0, GhostOK(gh), IsNested(gh), head in {b_i,internal}]: 0
L=6 g=0.5 t=0.0 ell_t=1: max ratio by ell {0: 1.0, 1: 1.0, 2: 0.081}
L=6 g=0.5 t=0.5 ell_t=1: max ratio by ell {0: 1.0, 1: 0.6033, 2: 0.1839}
L=10 g=0.5 t=0.0 ell_t=1: max ratio by ell {0: 1.0, 1: 0.894, 2: 0.5257, 3: 0.1071, 4: 0.081}
```
Larger `ℓ/ℓ_t` (`figAux`, `a_0=a_1`, `b_0=b_1`, FFT `L=64`; `L=128`, `|a−b|=2.5ℓ`):
```
$ cd $S && python3 -W ignore cx3.py | tail -6      # cols: |a-b|, ell : ratio_and, ratio_or (old farD, RHS T(ell)^2)
   10     6 : 0.9623      1.0035
   10    14 : 0.2632      0.7914
   10    22 : 0.0179      0.2997
   30     6 : 0.9585      1.0087
   30    14 : 0.5597      1.2072
   30    22 : 0.1438      1.1860
$ cd $S && python3 -W ignore cx4.py | tail -3
  ell= 4 |a-b|=10  ratio_and=0.9984  ratio_or(old farD)=1.0002
  ell=12 |a-b|=30  ratio_and=0.9565  ratio_or(old farD)=1.0147
  ell=24 |a-b|=60  ratio_and=0.6484  ratio_or(old farD)=1.2260
```
`ratio_and ≤ 1` and falls with `ℓ/ℓ_t` in every run. The S1-type "or" control rises slowly (`1.0002 → 1.226`, not conclusive at this scale); the decisive negative controls are (1) neg. (a) and (2) (`ratio_or` `2·10⁷` at `m=1000`).

**By inspection** (mathematics, files):
1. *Ghosting the head* (`GhostOK`, `IsNested`): for `ownExt` and `IsNested` the head of path `i` is the first fold step of `WalkOK` (`LWVocab.lean:320-324`), an edge `{a_i, st.2}` with `st.2 ∈ {a_i, b_i, inr α}` by `ownExt`; `st.2 = a_i` is a self-loop, excluded by `IsNested` (1); so `st.2 ∈ {b_i, inr α}`. `anpKey_ghostify_ghostOK` needs `noGhostPath i₀ = true` and `hend = head?` (`AnpKey.lean:477-480`); `anpKey_ghostify_nested` needs only `IsNested` (`:434`); after one ghostification the other paths keep their heads (`anpKey_gf_path` `:414`) and stay ghost-free (`anpKey_gf_noGhostPath_iff` `:589`); the `p` heads are distinct edges (`IsNested` (3),(4)), so `ordN − nngh` is unchanged at each step and the product of edge factors splits as `Π_i ξ(head_i) · val(Γ^gh)` (`anpKey2_ep_ghostify` `AnpKey2.lean:493`). Script: `GhostOK(gh)`, `IsNested(gh)`, `nngh(gh)=0` in 68 graphs.
2. *External–external steps in `lwAuxNested_holds` outputs*: every step of path `i` ends in `auxGraph_nodeV Dt i c` (`AuxGraph.lean:1219-1222`), whose four branches (`:1172-1175`) give `a_i`, `b_i`, `inr _`, `a_i`; so `ownExt` holds. The only external–external step is `a_i b_i` (`𝓜_x 𝓜_y`), possibly mid-path, never a self-loop; the head is `b_i` or internal; `rest` edges are attached to `a_0, b_0` and are not steps.
3. *Domain through `a_1` (S1): positive, with one precision.* `f^{>ℓ}` restricts the block variable `a_1^{(k)}` of `β^{(k)}` in each copy (`7_8:1607-1608`). The initial graph of `|f|^p` has the external molecules `𝓜_x, 𝓜_y` and `p` internal molecules `{α^{(k)}, β^{(k)}}` (waved edge `S_{αβ}`, `7_8:31`, `:850`). The local expansions create no molecule: every new vertex is joined to an existing one by waved/dotted edges (`7_8:351`); an internal molecule in the end is one of these `p` or a merger of them, or merges into `𝓜_x` and disappears (`7_8:851`, case (iii); that needs a vertex of the molecule radius `O(W(log W)^{3/2})` around `x` (`7_8:258`) next to a vertex of block `a_1^{(k)}` with `|a_1^{(k)}−a| > ℓ`, excluded up to the small error of `(eq:scalemole)`). So every surviving internal molecule contains a `β^{(k)}` with `|a_1^{(k)}−a|, |a_1^{(k)}−b| > ℓ`. The centre `α_i` is a free choice (`7_8:859`; `:876-879`, `:916-920` use only `|β−α_i| ≤ W(log W)^{1+ε₁}`); choosing `α_i := β^{(k)}` puts `[α_i] ∈ D^∧_{>ℓ}` exactly. For an arbitrary centre the restricted distance is only `> ℓ` minus a shift of order `(log W)^{1+ε₁}` blocks; not needed with this choice (delta `T2289d`). The p=2 instance: `figAux`/`auxQ` have both heads at the internal molecule that contains `β^{(k)}`. Not a stop condition.
4. *Statement truth*: `AnpFarHeadAt` is proved pointwise: for `lab ∈ S`, `val_lab(Γ) = Π_i ξ(head_i)·val_lab(Γ^gh) ≤ Π_i T(min(|a_i−b_i|,ℓ))·val_lab(Γ^gh)` (all factors `≥ 0`), sum over `S`, enlarge `S` to `univ`, `AnpDetGhAt Γ^gh` with `ψ` above. `AnpFarAndAt` is the case `S = piFinset(farDAnd)`: `farDAnd` gives `ℓ < |a_i − c|` for every `i`, `HeadFar` at every head. `LWAuxNestedOwn`: same witness `auxGraph_ngraph Dt` as `lwAuxNested_holds` plus item 2.

### Verdicts
- `lwMomExpFar_head` (`AnpFarHeadAt`): **PASS** (no counterexample in any run above; all hypotheses hold at the instance).
- `lwMomExpFar_and` (`AnpFarAndAt`): **PASS** (instance ratio `0.5801`; the T2281 1a counterexample and the supervisor family both pass).
- `lwMomExpFar_auxOwn` (`LWAuxNestedOwn`): **PASS** (by item 2).
- Paper-delta candidates: `T2289a` `7_8:1607-1611` "and" split; `T2289b` `7_8:1636-1640` long edge = first step or `a_ib_i`; `T2289c` `7_8:1622-1625` `T_t(|a−b|∧ℓ)^p`; `T2289d` `7_8:1636` domain holds for centre `α_i := β^{(k)}` (item 3).

## (b) Script output (stage 1b, written Tue Oct  6 11:56:17 UTC 2026; branch `t/T2289`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2289`)

```
$ date -u
Tue Oct  6 11:55:28 UTC 2026
$ git log --oneline -1; git diff --stat main...t/T2289; grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWMomExpFar.lean | wc -l
dee5e6e T2289: LW-13c far part of lem:LW_moment_exp, "and" domain (Graph/LWMomExpFar)
 RBM3D/Graph/LWMomExpFar.lean | 476 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 476 insertions(+)
       0
$ lake build RBM3D.Graph.LWMomExpFar 2>&1 | grep -E "error|LWMomExpFar.lean|Build completed" | sed -E "s/^warning: .*(exceeds the 100).*/<line-length warning>/" | sort | uniq -c
  31 <line-length lint warning>
   1 Build completed successfully (3393 jobs).
$ lake build 2>&1 | tail -1      # whole library, root RBM3D.lean unchanged (hub adds the import at merge)
Build completed successfully (4095 jobs).
$ lake env lean pins.lean   # check-file section 2 copied into namespace T2289Check + rfl/example checks + #print axioms
'RBM.Graph.lwMomExpFar_head' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_and' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_auxOwn' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_figAux' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_oneEdge' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_head' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMomExpFar_inst_aux' axioms: [propext, Classical.choice, Quot.sound]
$ python3 pindiff.py   # check-file definitions, vocabulary renamed, against the file (text, whitespace-normalised)
lwMomExpFar_farDAnd: check-file body (renamed) == file body (whitespace-normalised): True
lwMomExpFar_ownExt: check-file body (renamed) == file body (whitespace-normalised): True
lwMomExpFar_HeadFar: check-file body (renamed) == file body (whitespace-normalised): True
AnpFarHeadAt: check-file body (renamed) == file body (whitespace-normalised): True
AnpFarHead: check-file body (renamed) == file body (whitespace-normalised): True
AnpFarAndAt: check-file body (renamed) == file body (whitespace-normalised): True
AnpFarAnd: check-file body (renamed) == file body (whitespace-normalised): True
LWAuxNestedOwn: check-file body (renamed) == file body (whitespace-normalised): True
$ python3 ext.py <names>   # target and pin statements extracted from the file (line: text)
42: def lwMomExpFar_farDAnd (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
     Finset.univ.filter fun c => ∀ i : Fin p,
       ℓ < ((zdistInf d L (a i - c) : ℕ) : ℝ) ∧ ℓ < ((zdistInf d L (b i - c) : ℕ) : ℝ)
48: def lwMomExpFar_ownExt {p q : ℕ} (Γ : NGraph p q) : Prop :=
     ∀ i : Fin p, ∀ st ∈ Γ.path i,
       st.2 = Sum.inl (Sum.inl i) ∨ st.2 = Sum.inl (Sum.inr i) ∨ ∃ α : Fin q, st.2 = Sum.inr α
57: def lwMomExpFar_HeadFar (d L : ℕ) [NeZero L] {p q : ℕ} (Γ : NGraph p q) (a : Fin p → Zd d L) (ℓ : ℝ)
       (S : Finset (Fin q → Zd d L)) : Prop :=
     ∀ lab ∈ S, ∀ (i : Fin p) (st : Fin Γ.es.length × NV p q) (α : Fin q),
       (Γ.path i).head? = some st → st.2 = Sum.inr α → ℓ < ((zdistInf d L (a i - lab α) : ℕ) : ℝ)
65: def AnpFarHeadAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
     ∃ C : ℝ, 0 < C ∧
       ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
         ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
           (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
           (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
           ∀ (a b : Fin p → Zd d L) (S : Finset (Fin q → Zd d L)), lwMomExpFar_HeadFar d L Γ a ℓ S →
             Γ.valOn ξ a b S ≤
               C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
                 ∏ i, sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ)
76: def AnpFarHead (d : ℕ) : Prop :=
     ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → AnpFarHeadAt d Γ
80: def AnpFarAndAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
     ∃ C : ℝ, 0 < C ∧
       ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
         ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
           (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
           (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
           ∀ a b : Fin p → Zd d L,
             Γ.valOn ξ a b (Fintype.piFinset fun _ : Fin q => lwMomExpFar_farDAnd d L a b ℓ) ≤
               C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
                 ∏ i, sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ)
91: def AnpFarAnd (d : ℕ) : Prop :=
     ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → AnpFarAndAt d Γ
96: def LWAuxNestedOwn : Prop :=
     ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
       Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
       ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧
         Γa.ordN = LGraph.auxOrd Q.g ∧
         ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
           Γa.val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be
275: theorem lwMomExpFar_head : ∀ d : ℕ, AnpFarHead d := by
338: theorem lwMomExpFar_and : ∀ d : ℕ, AnpFarAnd d := by
374: theorem lwMomExpFar_auxOwn : LWAuxNestedOwn := by
$ sed -n "415,450p" RBM3D/Graph/LWMomExpFar.lean | awk "/\/--/{c=1} !c{print} /-\//{c=0}"   # instances (1)-(4), statement of (5), docstrings dropped

theorem lwMomExpFar_inst_figAux : AnpFarAndAt 3 figAux :=
  lwMomExpFar_and 3 2 2 figAux figAux_nested.2 figAux_nested.1 (by decide +kernel)

theorem lwMomExpFar_inst_oneEdge : AnpFarAndAt 3 anpKey_oneEdge :=
  lwMomExpFar_and 3 1 0 anpKey_oneEdge (by unfold NGraph.NoGhost; decide +kernel) anpKey_oneEdge_nested
    (by unfold lwMomExpFar_ownExt; decide +kernel)

theorem lwMomExpFar_inst_head : AnpFarHeadAt 3 figAux :=
  lwMomExpFar_head 3 2 2 figAux figAux_nested.2 figAux_nested.1 (by decide +kernel)

theorem lwMomExpFar_inst_aux :
    ∃ Γa : NGraph 2 localReg2_inst_Q.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧
      AnpFarAndAt 3 Γa := by
  obtain ⟨Γa, h1, h2, h3, -⟩ := lwMomExpFar_auxOwn 2 localReg2_inst_Q.pack (by norm_num)
    localReg2_inst_Q_locReg345 auxGraph_inst_Q_hxy
  exact ⟨Γa, h1, h2, h3, lwMomExpFar_and 3 _ _ Γa h1 h2 h3⟩

example : ∃ (ξ : Zd 3 4 → Zd 3 4 → ℝ) (θ : ℝ) (a b : Fin 2 → Zd 3 4),
    0 < θ ∧ (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) ∧
    (∀ α β, ξ α β ≤ sfT 3 4 2 (1 / 2) (1 / 2) (min ((zdistInf 3 4 (α - β) : ℕ) : ℝ) 1)) ∧
    (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) ∧ (lwMomExpFar_farDAnd 3 4 a b 1).Nonempty ∧
    ∃ C : ℝ, 0 < C ∧
      figAux.valOn ξ a b (Fintype.piFinset fun _ : Fin 2 => lwMomExpFar_farDAnd 3 4 a b 1) ≤
        C * θ ^ 2 * sfT 3 4 2 (1 / 2) (1 / 2) 0 ^ (figAux.ordN - ((2 : ℕ) : ℤ)) *
          ∏ i, sfT 3 4 2 (1 / 2) (1 / 2) (min ((zdistInf 3 4 (a i - b i) : ℕ) : ℝ) 1) := by
  obtain ⟨C, hC, H⟩ := lwMomExpFar_inst_figAux
  set ξ : Zd 3 4 → Zd 3 4 → ℝ :=
$ bash clash.sh
new public names:       28
total hits outside the new file (RBM3D/*.lean + T2288.md draft): 0
T2288.md exists: /Users/junyin/Lean_proof/RBM3D/docs/tickets/T2288.md
private helpers:
110:private theorem lwMomExpFar_foldl_none {α β : Type*} (f : Option α → β → Option α)
199:private theorem lwMomExpFar_ghost_false {Γ : NGraph p q} {i : Fin p} (hn : Γ.noGhostPa
264:private theorem lwMomExpFar_sfT_pos {d L : ℕ} [NeZero L] {W g t : ℝ} (hW : 0 < W) (ht 
$ lake env lean registry.lean   # import RBM3D; import RBM3D.Graph.LWMomExpFar; import RBM3D.Test.Axioms; #assert_rbm_axioms  (run 11:50:42 UTC, 43 s)
exit=0 (recorded at the run); line 1 of the output:
axiom audit: 8293 theorems, 2702 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ same file without the LWMomExpFar import (registry0.lean), then diff of the two outputs after line 1
axiom audit: 8276 theorems, 2691 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
owed/paper ledgers identical (diff empty); new names in registry.out: 0; LWMomentExp lines: 1
$ name existence check (Lean env.contains), names.lean
Finset.prod_le_prod₀+ Finset.prod_nonneg+ Finset.sum_le_sum_of_subset_of_nonneg+ Finset.single_le_sum+ Finset.sum_pos+ Finset.mul_sum+ Finset.prod_insert+ Finset.induction_on+ Fins
et.prod_eq_one+ Finset.sum_nonneg+ Finset.sum_le_sum+ Finset.mem_filter+ Fintype.mem_piFinset+ List.head?_eq_some_iff+ List.exists_cons_of_ne_nil+ List.map_congr_left+ List.map_map
+ List.foldl_cons+ List.mem_cons_self+ List.mem_map+ Nat.one_lt_cast+ abs_pos+ min_eq_left+ min_eq_right+ min_le_min_right+ Option.bind_some+ Finset.prod_le_prod+ Finset.prod_le_pr
od_of_nonneg -ABSENT 
```

Narrative (facts from the file and the log above):
- Section (a) was not edited, no `(a′)` section; stage 1b started 11:41 UTC (first `date -u` of the stage `Tue Oct  6 11:41:34 UTC 2026`).
- One new file `RBM3D/Graph/LWMomExpFar.lean` (476 lines), imports `RBM3D.Graph.AnpKey6`, `RBM3D.Graph.AuxGraph`; commit `dee5e6e` on `t/T2289`;
  `git diff --stat main...t/T2289` touches only that file; no registry line (the pins are conclusions of the three targets); no `sorry`/`admit`/`native_decide`/`axiom` (grep count 0).
- No port: RBM1D and RBM2D were not read or touched for this ticket (no diff-stat owed).
- The pins `AnpFarHeadAt`, `AnpFarHead`, `AnpFarAndAt`, `AnpFarAnd`, `LWAuxNestedOwn` and the vocabulary equal the check-file definitions (text diff above; `rfl` and
  `example : T2289Check.AnpFarHead 3 := lwMomExpFar_head 3` (likewise `AnpFarAnd`, `LWAuxNestedOwn`, and `∀ d`) compile in `pins.lean`); no hypothesis added, no signature changed.
- Route as in the ticket.  `lwMomExpFar_ghost_heads` (line 208) ghostifies the first edge of the paths of a `Finset T` one by one (`Finset.induction_on`); the invariant `lwMomExpFar_walk`
  (the steps `((u, v), next)`) is unchanged by `NGraph.ghostify` (`lwMomExpFar_walk_ghostify`); each step uses `anpKey_ghostify_nested`, `anpKey_ghostify_ghostOK` (`hend` = head), `anpKey_gf_noGhostPath_iff`,
  `anpKey_ghostify_ord`, `anpKey2_ep_ghostify`.  `lwMomExpFar_ghost_all` takes `T = univ`: `nngh = 0`, `ord - n_ngh = ord - p`.
- `lwMomExpFar_head` (line 275): `C` of `anpDetGh_holds d p q Γ'` for the ghostified graph, `ψ r = sfT (min r ℓ)` (antitone by `sfT_antitone`, positive by the private `lwMomExpFar_sfT_pos`, `ψ 0 = sfT 0` as `0 ≤ ℓ`),
  head factor `≤ sfT (min |a_i - b_i| ℓ)` (head `b_i`: the edge premise; head internal: `HeadFar` gives `ℓ < |a_i - lab α|`, so `ξ ≤ sfT ℓ ≤ sfT (min ..)`), product, sum over `S`, enlarged to `univ`.
- `lwMomExpFar_and` (line 338) takes only the first conjunct (`.1`, line 346) of `farDAnd`: the proof of `lwMomExpFar_head` never reads the `b_i`-side (suspicion S2 of the ticket; a one-sided domain would suffice for the head form).
- `lwMomExpFar_auxOwn` (line 374) is the body of `lwAuxNested_holds` (`AuxGraph.lean:1606-1640`) with the same witness `auxGraph_ngraph Dt`, plus `lwMomExpFar_nodeV_cases` (the four branches of `auxGraph_nodeV`) for `ownExt`.
- Instances: (1)-(4) as in the ticket (names `lwMomExpFar_inst_figAux`, `_oneEdge`, `_head`, `_aux`, all `theorem`s, no premise); one extra `example` (5) applies instance (1) at `L = 4`, `W = 2`, `g = t = 1/2`, `ℓ = 1`,
  `ξ = sfT (min |α - β| ℓ)`, `θ` = total mass of `ξ²`, with every premise discharged and `farDAnd` nonempty (witness `Pi.single 1 2`, `decide +kernel`).
- Lint: 31 line-length warnings in the new file (long docstring/signature lines), no other warning in it; the full `lake build` (root `RBM3D.lean` unchanged) passes.

## (c) Verified Mathlib/core names used

All names in the last block of (b) were checked with `Environment.contains`: 27 of the 28 names exist (`Finset.prod_le_prod₀`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.single_le_sum`, `Finset.sum_pos`, `List.head?_eq_some_iff`,
`List.exists_cons_of_ne_nil`, `List.map_congr_left`, `Fintype.mem_piFinset`, `Nat.one_lt_cast`, `Option.bind_some`, ...).  `Finset.prod_le_prod` exists but is the ordered-monoid version (needs `MulLeftMono`; my first attempt with it
failed to elaborate for `ℝ`); the nonnegative-factor version is `Finset.prod_le_prod₀` (`#check`: `(∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ g i) → ∏ f ≤ ∏ g`).  Absent: `Finset.prod_le_prod_of_nonneg`.

## (d) Open issues and paper-delta candidates

- `T2289a` `7_8:1607-1611`: `f^{>ℓ}` is split by `|a_1 - a| ∧ |a_1 - b| > ℓ` ("and"); `f^{≤ℓ}` is over the union of the two balls (supervisor 1102 §2.2).  Lean: `lwMomExpFar_farDAnd`.
- `T2289b` `7_8:1636-1640`: `𝐃_{>ℓ}` with "and"; the long ending edge is the first step of each path (external-internal) or the direct edge `a_ib_i`; Lean ghostifies exactly the first step (`lwMomExpFar_ghost_heads`).
- `T2289c` `7_8:1622-1625` `(eq:LW_moment_exp_far)`: `Π_i 𝖳_t(|a_i - b_i| ∧ ℓ)` in place of `𝖳_t(ℓ)^p` (Lean: `AnpFarHeadAt`/`AnpFarAndAt` conclusions).
- `T2289d` `7_8:1636` (from section (a) item 3, mathematics, not Lean-checked here): every surviving internal molecule contains a `β^{(k)}` with `|a_1^{(k)} - a|, |a_1^{(k)} - b| > ℓ`, so the domain claim holds for the centre `α_i := β^{(k)}`.
- `T2289e` (Lean/paper difference): the pins carry the premise `ownExt` (not in the paper; `lwMomExpFar_auxOwn` shows the outputs of `lwAuxNested_holds`' construction have it), `AnpFarHeadAt` takes an arbitrary labelling set `S` with `HeadFar`
  (more general than the paper's domain), and `C` depends on `Γ` and `d` only.
- Open for LW-13b: to supply `HeadFar` / membership in `farDAnd` for the labellings of the expansion of `|f^{>ℓ}|^p` (S1 of the ticket; section (a) item 3 argues it, no Lean statement yet), and the near part / union domain (T2281).
