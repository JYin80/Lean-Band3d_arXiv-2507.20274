Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 20:07:54 UTC 2026

Notation: `E_J = Theta_{xi_J} - I` (edge `J`, `xi_J = t m(s)^2`, equal charges `s`), `d_s = Theta_{xi_s}(0,0) - 1`, `O_s = E_s` off the diagonal,
`A_s = sum_{a != 0} |Theta_{xi_s}(0,a)|`, `P = (prod m) * sum_F prod_{J in F} d_{s_J}`, `T(n) = |TSP n|` (`TSP 3 = {empty}`: `Partition.lean:108`).
Scripts (python3 + numpy, not Lean) in `scratchpad/T2070/`: `chk.py` (model: `SB` circulant `Defs/Block.lean:38-44`, `Theta=(1-xi S)^-1` by FFT, trees/`KLleafPar`/`KLnodePar` of `KLTree.lean:59-82`, `Sigma^(empty)` of `KLTree.lean:366`), `run2.py` (targets 2), `run1.py` (target 1), `short.py`, `consts.py`, `inst.py`.

### (i) Exponent table
| item | value | constraint | slack |
|---|---|---|---|
| `KLShort` constants `C_k, c_k` | from merged `prop5Short_holds d gmax kappa''` (`Propagator/Prop5Short.lean:400`), `kappa'' = sqrt(kappa(4-kappa))/2`: `(d,gmax,kappa)=(3,1,1)`: `kappa''=0.8660`, `c_k=0.0846`, `C_k=140.89` (docstring formulas `Prop5Short.lean:395-399`, `consts.py`) | `kappa'' <= Im m(E)=sqrt(4-E^2)/2` for `|E|<=2-kappa` (`4-E^2 >= kappa(4-kappa)`); `kappa>2`: no `E`, vacuous | `E=0`: 1.0000 vs 0.8660; `E=1`: 0.8660 = 0.8660 (tight). `KLShort d kappa gmax` is **provable** for `3<=d, 0<kappa, 0<gmax` (`mSigma E s = PropSpin (mE E) s`, `‖mE E‖=1` `Semicircle.lean:87`): `KLShort_holds`. Numeric: `max_a |Theta|/(C_k(1_{a=0}+g^2 e^{-c_k|a|}))=0.0054` over `L in{5,9,15}, E in{0,1}, g in{.05,.5,1}, t in{.5,.9,.99,.9999}, s in{+,-}` (`short.py`) |
| edge entry bound `B` | `B = C_k(1+gmax^2)+1 = 282.8` (`3,1,1`) | `\|E_s(x,y)\| <= B e^{-c_k\|x-y\|}`: `x=y`: `\|Theta(0,0)-1\| <= C_k(1+g^2)+1`; `x!=y`: `<= C_k g^2 e^{..}`; `B>=1` | no `g,L,t` |
| tree rate / lattice sum | rate `c = c_k/2` (`0.0423`); per-node weight `lam = c_k/(2 n^2)`: `n=3,4,6`: `0.00470, 0.00264, 0.00117`; `sum_{b in Z_L^d} e^{-lam\|a-b\|} <= expC(d-2,lam)` (`Defs/RadialSum.lean:271-276`, `L`-uniform, `d=k+2>=3`): `1.3e13, 1.3e14, 3.2e15` | `lam * (#nodes<=n^2) <= c_k/2` (distance of every node `<=` leaf path + edge path, `dist_bounds` RBM2D `PureLoop.lean:267`) | exact (`lam n^2 = c_k/2`) |
| target 1 constant `C1` | `C1 = T(n) B^{n+n^2} expC(d-2,lam)^{n^2}`: `log10 C1 = 147, 275, 663` for `n=3,4,6`; `T=1,3,45` | none (existence only, never evaluated) | depends on `d,n,kappa,gmax`; no `L,W,g,t,E` |
| target 2(a) | `C_a = 2^{n^2} n gapK(kappa)^{-n} (2/sqrt(kappa(4-kappa)))` (`n=4,kappa=1`: `2^16*4*1*1.1547=302698`) times `eta_t <= (1-t) Im m <= 1-t` | merged `KLSigmaPi_alt_sumZero_le` (`KLSumZeroWard.lean:1160`): no `d>=3`, no `W`, `g` free | actual `signed/(1-t)<=1.000` (grid below), bound 3e5: slack 3e5 |
| target 2(b) | `D=B`, `A_s <= A0 g^2`, `A0 = C_k expC(d-2,c_k) = 1.7e10`; `R_b = sum_F [prod(\|d\|+A) - prod\|d\|] <= T(n) n A0 g^2 (B+A0 gmax^2)^n`; `C_b = max(C_a, 2 T(n) n A0 (B+A0 gmax^2)^n)` | `abs <= \|P\|+R_b`, `\|P\| <= signed + R_b` | numeric fit `C_abs=6.77 (n=4), 40.3 (n=6)` (grid) |
| boundaries (§29) | `t in[0,1)`: `t=0` (`Sigma=1`), `t=0.9999`; `g=0.01..1=gmax`; `n=3` (target 1 only; star `Sigma=prod m 1[delta all equal]`, `maxDist=0`), `n=5` (odd, target 1), `n=4,6` even | `C,c` free of `L,W,g,t`; `n>=4` even only for target 2 | `abs/g^2` stays ~6 as `t->1` (`g=0.2`): the `g^2` in 2(b) is sharp, not removable |

**Target 1 (`KLmolecule_holds`), port table** RBM2D `Loop/PureLoop.lean` at `c9a24cf` (RBM2D HEAD `9e0f275`; read-only): `SigmaPi_empty_shortRange_prec` `:747` and its private chain `SigmaPi_bound :688`, `tree_bound :312`, `dist_bounds :267`, `path_aux/path_le :209-266`, `IsTSPf/nodes_laminar/nodePar_spec :67-170`. Changes: `Z2 L -> Zd d L`, `zdist2 -> zdistD` (`l^1` torus norm: `zdistD_add_le`, `zdistD_neg` merged); `SigmaPi -> KLSigmaPi d L g`, `mSig -> mSigma`, `thetaEdge L -> thetaEdge d L g`, `treeValW/selfW -> KLtreeValW/KLselfW` (`KLtreeValW_eq_sum_selfW` merged), `nodes/leafPar/nodePar -> KLnodes/KLleafPar/KLnodePar` (re-prove laminarity against `KL*`); `(1+2/lam)^2 -> expC(d-2,lam)` via merged `sum_radial_exp_decay_le`/`sum_exp_decay_centre` (`d=k+2`, `k>=1`); `Prop5Hyp kappa c` + `UnifDetDom` (loss `N^tau`) -> the deterministic constants `(C_k,c_k)` of `KLShort` (the 2D gap `c sqrt(c_kappa)` rate is replaced by `c_k` directly, the `gap_le_norm` section `:430-540` is not needed); `‖prod m‖=1` by `norm_mSigma` (needs only `|E|<=2`). Proof: only equal-charge diagonals (`KLFlong F sigma = empty`), so every `E_J` is a `KLShort` edge: `\|Sigma\| <= T(n) B^{n+n^2} expC^{n^2} e^{-(c_k/2) maxDist}`, summing the `<= n^2` free node labels against `e^{-lam\|a_i-b\|}`, `lam n^2 = c_k/2`. No `L`: only `expC`.
**Target 2(b), argument at `d>=3`.** Write `E_J = d_{s_J} I + O_{s_J}` (diagonal / off-diagonal in `x-y`). `Finset.prod_add` over the edges of `F` gives subsets `S` of off-diagonal edges. `S=empty`: all node labels equal the root, so `delta` is all-equal (`delta=(x,..,x)` once `delta_0=x`) with value `prod_{J}d_J`; summed over `F` and times `prod m` this is `P` (and `prod m = 1`). `S!=empty`: a non-all-equal pattern forces an off-diagonal edge `J in S`, `a=b_J-b_par != 0`, with equal charges, so `KLShort` gives `\|O(a)\| <= C_k g^2 e^{-c_k\|a\|}` **without** the `1_{a=0}` term (property 5'). Summing `\|T_{F,S}(delta)\|` over `delta` (`delta_0=x`) is `<=` the sum over all node labels with `b_{leafPar 0}=x`; contracting the `d`-edges gives a tree on `\|S\|+1` classes; peel every class `!= leafPar 0` against exactly one `O`-edge: each costs `sum_a \|O(a)\| <= A_s <= A0 g^2` (`expC`, `L`-uniform; the `L^d` fibre count never appears, each free label is summed against a decay). So `sum_delta \|Sigma\| <= \|P\| + R_b` and signed `= P + R` with `\|R\|<=R_b`, hence `\|P\| <= \|signed\| + R_b`, `abs <= \|signed\| + 2R_b <= C_a(1-t) + 2R_b <= C_b(g^2+1-t)`. Requires `n` even only through (a) (`sigma_alt`, `prod m=1`). Lean-side warning: the class-peeling is rooted at `KLleafPar 0`, which is **not** always the root `(0,n-1)` (e.g. `(0,2)`), so peel by induction on non-fixed nodes (any leaf of the node tree `!= leafPar 0`).
**`KLShort` and the registry.** Outside `KLTree.lean` no merged Lean file mentions `KLShort` (grep count 0); inside it, it is the definition (`:278`) and the field `short` of `KLPT`; `Test/Axioms.lean` registers only `KLPT` (line 79). The theorems of this ticket take `KLShort d kappa gmax` as hypothesis (as pinned), so a scan of `Test/Axioms.lean` would find it as an unproved premise unless a theorem concludes it: `KLShort_holds (hd : 3<=d) (hkappa : 0<kappa) (hgmax : 0<gmax) : KLShort d kappa gmax` (from `prop5Short_holds d gmax kappa''`, split `kappa<=2` / `kappa>2` vacuous) removes the premise: no registry line needed, and the pins then hold unconditionally.

### (ii) One concrete nondegenerate instance
Data: `d=3, kappa=1, gmax=1`, `KLPar` point `L=5, W=1, g=1/2, E=0, t=9/10`; `n=4` (both pins; `n=3` = star for target 1), `sigma = sigma_alt` for target 2, `x=0`. Every hypothesis holds simultaneously (Lean: `KLShort` from `KLShort_holds`, no hypothesis left).
```
$ python3 inst.py
hypotheses: {'3<=d': True, '3<=n': True, '4<=n': True, 'Even n': True, '0<kappa': True, '0<gmax': True, '3<=L': True, '1<=W': True, '0<g': True, 'g<=gmax': True, '|E|<=2-kappa': True, '0<=t': True, 't<1': True} ALL
KLShort_holds route: kappa''=sqrt(kappa(4-kappa))/2=0.8660 <= Im m(E)=1.0000: True; |m(E)|=1.0; |Theta(0,0)|,|Theta(0,a)|<=C_k(1_(a=0)+g^2 e^(-c_k|a|)) checked in short.py
n=4,L=5,g=0.5,E=0.0,t=0.9: |#delta supports|=249  signed=0.052632  (1/19=0.052632)  merged bound RHS (a)=30269.8 >= signed: True;  abs=1.419475  |P|=0.512008 R_bound=0.9075  abs<=|P|+R_b: True  |P|<=signed+R_b: True
   fitted: signed/(1-t)=0.5263  abs/(g^2+1-t)=4.0556  (both > 0: nondegenerate; abs>signed)
   molecule at sigma_alt: #supports with maxDist=0: 1, maxDist>0: 248; max|Sigma|e^(0.5 maxDist)=0.5120; max_(maxDist=r)|Sigma| r=1..4: ['5.216e-02', '7.187e-03', '1.462e-03', '1.790e-04']
```
(`inst.py` RHS (a) uses `eta_t=(1-t)Im m`, `n=4`: `2^16*4*1*(2/sqrt3)*0.1=30269.8`; the line in (i) `302698` is without `eta_t`.) `signed=1/19=2/(1+t)-1` is the exact `E=0,n=4` closed form (`Q(t)=1+2((1+t)^-1-1)`, T2056); `t=1/2` gives `1/3` (T2056 instance).
`KLShort` is not external here (it is proved by `KLShort_holds`), so the TEAM §8 lesson 14 limit check is the constants check: `short.py` max ratio 0.0054 <= 1 over the grid including `t=0.9999`:
```
$ python3 short.py | head -1
KLShort check at (d,kappa,gmax)=(3,1,1), constants of prop5Short_holds: max_a |Theta_xi(0,a)| / (C_k(1_(a=0)+g^2 e^(-c_k|a|))) = 0.0054 (must be <=1) at (L,E,g,t,s)=(5, 1.0, 0.05, 0.5, 0)
```
Grid for target 2 (`d=3`, `L in{5,9}` for `n=4,6`; `E in{0,1}`, `g in{.05,.5,1}`, `t in{0,.5,.9,.99}`; 48 cases per `(n)`), `python3 run2.py 4 5,9; python3 run2.py 6 5,9`; and 20 boundary cases (`(g,t) in {(.01,.9999),(.05,.9999),(.2,.9999),(1,.9999),(.01,.99)}`, `E in{0,1}`, `(n,L) in{(4,9),(6,5)}`); "expansion-ok" = `abs<=|P|+R_b` and `|P|<=signed+R_b`:
```
FIT n=4 Ls=[5, 9]: C_signed=max signed/(1-t)=1.0000  C_abs=max abs/(g^2+1-t)=6.7652  expansion inequalities all ok: True
FIT n=6 Ls=[5, 9]: C_signed=max signed/(1-t)=1.0000  C_abs=max abs/(g^2+1-t)=40.3077  expansion inequalities all ok: True
(grep -c "expansion-ok=False" grid.txt) 0
boundary n=4 L=9 E=1 g=0.2 t=0.9999: signed/(1-t)=0.6667 abs/(g^2+1-t)=7.9945 ok=True   (all 20 boundary rows: ok=True, abs/(g^2+1-t) <= 30.95)
```
Grid for target 1 (`python3 run1.py`; `sup_delta |Sigma| e^{c maxDist}`, all `delta` with `delta_0=0`; same `E,g,t` grid; fitted slope = worst `log max_{maxDist=r}|Sigma|` slope, `r>=1`):
```
n=4 L=[5,9] sigmas=all 16: sup e^(0.5 md)=1.0000 sup e^(1.0 md)=1.0000 worst slope=-1.060 (L=9,E=0,g=1,t=.99,sigma=0000)
n=5 L=[5] sigmas=all 32 (E in 0,1; g in .05,1; t in 0,.9,.99): sup e^(0.5 md)=1.0000 sup e^(1.0 md)=1.0000 worst slope=-1.249
n=6 L=[5] sigmas=alt,++--++,+--++-: sup=1.0000 (c=.5, 1.0) worst slope=-1.222
n=6 L=[9] sigmas=alt: sup=1.0000 worst slope=-1.051
n=6 L=[5] sigmas=all-plus (t in .5,.9,.99): sup e^(0.5 md)=0.8270 worst slope=-1.256
n=3: Sigma=prod m * 1[delta_0=delta_1=delta_2], |.|=1, maxDist=0: C=1, any c
```
Fitted `C = 1.0` at `c = 0.5, 1.0` (attained at `t=0`/all-equal `delta`); true decay rate `~1.05..1.26` vs the provable `c_k/2 = 0.0423` (slack 25x; constants pessimistic, fine for `exists C c`). Not covered: `n=6, L=9` only for `sigma_alt` (all-plus at `L=9` needs `729^5` entries), `sigma` all `2^6` at `L=5` only for 3 patterns plus all-plus; `n>=7`.

### Verdicts
- `KLmolecule_holds` (`KLmoleculePin` body, `3<=d`, `3<=n`, `0<kappa`, `0<gmax`, `KLShort` hyp.): **PASS**. Chain closes with explicit `C1, c=c_k/2` depending on `d,n,kappa,gmax` only; instance numbers above.
- `KLsumZero_holds` (`KLsumZeroPin` body, `4<=n` even): **PASS**. (a) merged `KLSigmaPi_alt_sumZero_le` with `eta_t<=1-t`; (b) new argument above (`abs <= |signed| + 2 R_b`, `R_b = O(g^2)` from `KLShort`); numerically verified (`C_abs` 6.77, 40.3; all expansion inequalities hold).
- `KLShort_holds` (extra theorem): **PASS**, derivable from merged `prop5Short_holds`; the pins then hold unconditionally and the registry needs no `KLShort` line.
- Paper-delta candidates: `T2070a` (absolute estimate `Sum_delta|Sigma^(empty)(sigma_alt)| <= C(g^2+(1-t))` proved internally from `(prop:ThfadC_short)` and the signed estimate, instead of citing [RBSO1D] Claim 4.30; `C = max(C_a, 2T(n) n A0 (B+A0 gmax^2)^n)`), `T2070b` (rate `c_k/2` and the explicit constants route via `prop5Short_holds` with `kappa''`).

## (b) Script output (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2070, branch t/T2070; scripts and logs in the scratchpad `T2070/`; run times from `date -u`)

### Build, hygiene, axioms, name clash
```
$ date -u
Sat Oct  3 20:43:20 UTC 2026
$ git log -1 --format=%h t/T2070
ffa1a9e
$ lake build RBM3D.Loop.KLMolecule   (tool log of the build that compiled the final source; the commit amend afterwards changed no source)
✔ [3253/3253] Built RBM3D.Loop.KLMolecule (8.6s)
Build completed successfully (3253 jobs).
$ lake build RBM3D.Loop.KLMolecule 2>&1 | tail -2
Build completed successfully (3253 jobs).
$ lake build 2>&1 | tail -1     (full library; the root RBM3D.lean does not import the new module until the hub merges)
Build completed successfully (3787 jobs).
```
```
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Loop/KLMolecule.lean   -> exit status 1 (1 = no match)
$ git diff --stat main...t/T2070
 RBM3D/Loop/KLMolecule.lean | 1029 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1029 insertions(+)
$ git log -1 --format="%h %an <%ae> %s" t/T2070
ffa1a9e Jun Yin <321276894+JYin80@users.noreply.github.com> T2070: KL8+9 molecule decay and sum-zero estimates (Loop/KLMolecule)
$ grep -n "^theorem [A-Za-z]\|^def \|^noncomputable def\|^structure\|^abbrev\|^instance" RBM3D/Loop/KLMolecule.lean   (public declarations; all others are private)
44:def KLmoleculeAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
53:def KLsumZeroAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
341:theorem KLShort_holds (d : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) :
610:theorem KLmolecule_holds :
776:theorem KLsumZero_holds :
917:theorem KLMolecule_inst_molecule_norm :
930:theorem KLMolecule_inst_molecule :
944:theorem KLMolecule_inst_signed_val :
959:theorem KLMolecule_inst_sumZero :
$ lake env lean axioms.lean | python3 group.py   (import RBM3D.Loop.KLMolecule; #print axioms of the 9 new public declarations: 2 defs, 3 theorems, 4 instance theorems)
9 declarations: KLmoleculeAt, KLsumZeroAt, KLShort_holds, KLmolecule_holds, KLsumZero_holds, KLMolecule_inst_molecule_norm, KLMolecule_inst_molecule, KLMolecule_inst_signed_val, KLMolecule_inst_sumZero
   axioms: [propext, Classical.choice, Quot.sound]
$ name-clash: for each new public name, grep -rnw NAME RBM3D RBM3D.lean --include="*.lean" | grep -v RBM3D/Loop/KLMolecule.lean | wc -l
 KLmoleculeAt=0 KLsumZeroAt=0 KLShort_holds=0 KLmolecule_holds=0 KLsumZero_holds=0 KLMolecule_inst_molecule_norm=0 KLMolecule_inst_molecule=0 KLMolecule_inst_signed_val=0 KLMolecule_inst_sumZero=0
$ git --no-optional-locks log -1 --format="%h %s" main; for n in <the 9 names>; do git --no-optional-locks grep -nw "$n" main -- RBM3D RBM3D.lean | wc -l; done   (main worktree, read-only; counts)
a262beb T2073: merge ST2-22 Path/StepDecomp
 KLmoleculeAt=0 KLsumZeroAt=0 KLShort_holds=0 KLmolecule_holds=0 KLsumZero_holds=0 KLMolecule_inst_molecule_norm=0 KLMolecule_inst_molecule=0 KLMolecule_inst_signed_val=0 KLMolecule_inst_sumZero=0
$ grep -rn "KLMolecule" RBM3D RBM3D.lean --include="*.lean" | grep -v RBM3D/Loop/KLMolecule.lean | wc -l
0
(public declarations of the new file: 2 defs + 3 theorems + 4 instance theorems = 9, listed above; private declarations: 31; examples: 5)
```
### Target statements extracted from the file by script; script diff against the ticket pins
```
$ python3 extract.py 'block|^def KLmoleculeAt' 'block|^def KLsumZeroAt' 'stmt|^theorem KLShort_holds' 'stmt|^theorem KLmolecule_holds' 'stmt|^theorem KLsumZero_holds'   (file line: text)
44: def KLmoleculeAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
45:   ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
46:     (δ : Fin n → Zd d p.L),
47:     ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d p.L δ : ℝ)))
53: def KLsumZeroAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
54:   ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (x : Zd d p.L),
55:     ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
56:         KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (1 - p.t) ∧
57:     ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x),
58:         ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (p.g ^ 2 + (1 - p.t))
341: theorem KLShort_holds (d : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) :
342:     KLShort d κ gmax := by
610: theorem KLmolecule_holds :
611:     ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLShort d κ gmax →
612:       KLmoleculeAt d n κ gmax := by
776: theorem KLsumZero_holds :
777:     ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 4 ≤ n → Even n → 0 < κ → 0 < gmax →
778:       KLShort d κ gmax → KLsumZeroAt d n κ gmax := by
$ python3 diffpins.py   (new file vs docs/tickets/checks/T2070-check.lean, whitespace-normalised)
def KLmoleculeAt: IDENTICAL (whitespace-normalised, check file vs new file)
def KLsumZeroAt: IDENTICAL (whitespace-normalised, check file vs new file)
theorem KLmolecule_holds statement vs body of KLmoleculePin: IDENTICAL
theorem KLsumZero_holds statement vs body of KLsumZeroPin: IDENTICAL
$ lake env lean pincheck.lean   (check file T2070-check.lean + import of the new module + the two examples below)
35:example : KLmoleculePin := KLmolecule_holds
36:example : KLsumZeroPin := KLsumZero_holds
38:example (d n : ℕ) [NeZero n] (κ gmax : ℝ) : KLmoleculeAt d n κ gmax ↔ RBM.Loop.KLmoleculeAt d n κ gmax := Iff.rfl
39:example (d n : ℕ) [NeZero n] (κ gmax : ℝ) : KLsumZeroAt d n κ gmax ↔ RBM.Loop.KLsumZeroAt d n κ gmax := Iff.rfl
exit: 0
```
### Compiled nonempty instances (extracted by script; `KLinstPar`, `KLinstσ`, `KLinsta` are merged data of `KLTree.lean`: `L = 5, g = 1/2, E = 0, t = 9/10`; `KLinsta = ![0,1,2]`)
```
$ python3 extract.py 'block|^theorem KLMolecule_inst_molecule :' 'block|^theorem KLMolecule_inst_sumZero :' 'stmt|^theorem KLMolecule_inst_molecule_norm' 'stmt|^theorem KLMolecule_inst_signed_val'
930: theorem KLMolecule_inst_molecule :
931:     ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
932:       ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ KLinsta‖
933:         ≤ C * Real.exp (-(c * (KLmaxDist 3 5 KLinsta : ℝ))) ∧
934:       ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun _ => 0)‖ = 1 ∧
935:       ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun _ => 0)‖
936:         ≤ C * Real.exp (-(c * (KLmaxDist 3 5 (fun _ : Fin 3 => (0 : Zd 3 5)) : ℝ))) := by
937:   obtain ⟨C, hC, c, hc, h⟩ := KLmolecule_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos
938:     one_pos (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)
939:   exact ⟨C, hC, c, hc, h KLinstPar KLinstσ KLinsta, KLMolecule_inst_molecule_norm,
940:     h KLinstPar KLinstσ (fun _ => 0)⟩
959: theorem KLMolecule_inst_sumZero :
960:     ∃ C : ℝ, 0 < C ∧
961:       ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
962:           KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ = 1 / 19 ∧
963:       ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
964:           KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 9 / 10) ∧
965:       ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
966:           ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖
967:         ≤ C * ((1 / 2) ^ 2 + (1 - 9 / 10)) := by
968:   obtain ⟨C, hC, h⟩ := KLsumZero_holds 3 4 1 1 (by norm_num) (by norm_num) ⟨2, by norm_num⟩
969:     one_pos one_pos (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)
970:   have h0 := h KLinstPar 0
971:   refine ⟨C, hC, ?_, h0⟩
972:   rw [KLMolecule_inst_signed_val]
973:   simp
917: theorem KLMolecule_inst_molecule_norm :
918:     ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun _ => 0)‖ = 1 := by
944: theorem KLMolecule_inst_signed_val :
945:     ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0),
946:       KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ = 1 / 19 := by
$ grep -c "^example" RBM3D/Loop/KLMolecule.lean  -> 5 further `example`s (boundary point g = gmax = 1, |E| = 2-κ = 1, t = 99/100, n = 6; KLShort 3 (1/2) 2; KLmoleculeAt 3 4 1 1, 3 5 (1/2) 2; KLsumZeroAt 3 8 (1/2) 2)
```
### Registry pre-check (DECISIONS §16, §20), counterfactual, and ports
```
$ grep -n "KLPT\|KLShort" RBM3D/Test/Axioms.lean | cut -c1-120;  grep -rn "KLShort" RBM3D --include="*.lean" | grep -v RBM3D/Loop/KLMolecule.lean | cut -c1-80
79:  [`RBM.ThetaDiffOne, `RBM.ThetaDiffTwo, `RBM.PropTH, `RBM.Loop.KTreeRep, `RBM.Loop.KLPT]
RBM3D/Loop/KLTree.lean:278:def KLShort (d : ℕ) (κ gmax : ℝ) : Prop :=
RBM3D/Loop/KLTree.lean:323:  short : KLShort d κ gmax
$ cat precheck.lean   (not committed; DECISIONS §20 registry pre-check)
import RBM3D
import RBM3D.Loop.KLMolecule

#assert_rbm_axioms
$ lake env lean precheck.lean > out; echo $?
exit: 0
1:axiom audit: 2291 theorems, 998 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
96:premises found by scanning: 79 (borrowed 2, owed 65, structural 12).
97:registry: 5 borrowed + 84 owed + 34 structural; 44 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ same with only `import RBM3D` (no new module):
exit: 0
1:axiom audit: 2284 theorems, 996 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
96:premises found by scanning: 79 (borrowed 2, owed 65, structural 12).
$ counterfactual: `import RBM3D` + a theorem `T2070scratch_uses (h : KLShort 3 1 1) : True` + #assert_rbm_axioms
exit: 1
error: axiom audit: 1 premise(s) that no theorem of this development proves
8:  [RBM.Loop.KLShort]
$ emulated hub merge steps 4-5 in a scratch clone (rsync of the worktree without .git; a python3 edit inserted `import RBM3D.Loop.KLMolecule` after the last import line of the clone RBM3D.lean); diff worktree RBM3D.lean vs clone RBM3D.lean:
105a106
> import RBM3D.Loop.KLMolecule
$ lake build 2>&1 | tail -2   (the hub merge step 5, full library incl. #assert_rbm_axioms at the end of RBM3D.lean)
non-vacuity certificates: 4 of 89 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3788 jobs).
$ lake env lean RBM3D.lean | grep "axiom audit:\|premises found by scanning"   (the root file with the new import)
axiom audit: 2291 theorems, 998 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 79 (borrowed 2, owed 65, structural 12).
exit of lake env lean RBM3D.lean: 0
$ git -C ../RBM2D --no-optional-locks log -1 --format="%h %s" c9a24cf; ... log -1 --format="%h %s"  (HEAD)
c9a24cf T2273: merge dead-code closure tool and report
9e0f275 Final clean-up: renames of private and section names, records, publication drafts
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/PureLoop.lean
 RBM2D/Loop/PureLoop.lean | 239 +++++------------------------------------------
 1 file changed, 22 insertions(+), 217 deletions(-)
(hunk summary by python script over `git diff -U0 c9a24cf HEAD`: 16 hunks = 11 comment/doc/section-name hunks + 5 hunks deleting declarations: wholeP_not_mem, norm_mSig', sum_TSPlong', Kcal_pure_bound, Kcal_pure_prec; the declarations listed below are unchanged)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Loop/PureLoop.lean | grep -n "theorem zdist2_symm\|theorem zdist2_tri\|def pathSet\|theorem anc_step\|theorem path_aux\|theorem path_le\|theorem dist_bounds\|theorem tree_bound\|theorem exists_pair\|theorem SigmaPi_bound\|theorem SigmaPi_empty_shortRange_prec" | cut -c1-60
48:private theorem zdist2_symm (x y : Z2 L) : zdist2 L (x - 
51:private theorem zdist2_tri (x y z : Z2 L) :
182:private def pathSet (F : Finset (Fin n × Fin n)) (x y : 
186:private theorem anc_step {F : Finset (Fin n × Fin n)} (h
209:private theorem path_aux {F : Finset (Fin n × Fin n)} (h
259:private theorem path_le {F : Finset (Fin n × Fin n)} (hF
267:private theorem dist_bounds {F : Finset (Fin n × Fin n)}
312:private theorem tree_bound {F : Finset (Fin n × Fin n)} 
574:private theorem exists_pair {L : ℕ} [NeZero L] {n : ℕ} [
688:private theorem SigmaPi_bound {E t : ℝ} (hn : 3 ≤ n) (σ 
747:theorem SigmaPi_empty_shortRange_prec :
$ grep -n "^private theorem\|^private def" RBM3D/Loop/KLMolecule.lean | sed -E "s/^([0-9]+):private (theorem|def) (KLMolecule_[A-Za-z_0-9]+).*/\1:\3/" | tr "\n" " "
72:KLMolecule_zdistD_symm 76:KLMolecule_zdistD_tri 82:KLMolecule_pathSet 86:KLMolecule_anc_step 110:KLMolecule_path_aux 161:KLMolecule_path_le 170:KLMolecule_const_of_edges 187:KLMolecule_exists_offdiag 209:KLMolecule_tree_bound 367:KLMolecule_edge 439:KLMolecule_prod_const_exp 450:KLMolecule_card_le 456:KLMolecule_prod_le 478:KLMolecule_prod_off 526:KLMolecule_selfW_eq 532:KLMolecule_selfW_bound 546:KLMolecule_selfW_bound_nc 566:KLMolecule_SigmaPi_of_tree 584:KLMolecule_exists_pair 592:KLMolecule_same_charge 663:KLMolecule_etaT_le 673:KLMolecule_signed 688:KLMolecule_sum_slice 722:KLMolecule_sum_exp_maxDist 885:KLMolecule_mE_zero 891:KLMolecule_mSigma_sq 895:KLMolecule_TSPlong_four 900:KLMolecule_Qlayer_four 912:KLMolecule_TSPlong_three 
```
### Numerics for the route of the proof (python3 + numpy, not Lean; model of `chk.py` of section (a): `Σ^{(∅)}` from the tree sum, `S = {δ_0 = 0}`, `c₀ = (0,…,0)`, `nc = ∑_{δ∈S, δ≠c₀}|Σ(δ)|`)
```
$ python3 routeB.py 4 5,9; python3 routeB.py 6 5,9; python3 routeB.py 4 5,9 boundary; python3 routeB.py 6 5 boundary
routeB grid n=4 Ls=[5, 9] #cases=48: max nc/g^2=4.8113  max_(delta nonconst)|Sigma|e^(0.5 maxDist)/g^2=0.5495  max abs/(g^2+1-t)=6.7652  identities (abs=|S(c0)|+nc, |S(c0)|<=|signed|+nc) all ok: True
   argmax nc/g^2 at (L,E,g,t)=(9, 1.0, 0.5, 0.99): signed=6.7001e-03 abs=1.7590e+00 |Sigma(c0)|=5.5613e-01 nc=1.2028e+00
routeB grid n=6 Ls=[5, 9] #cases=48: max nc/g^2=39.8345  max_(delta nonconst)|Sigma|e^(0.5 maxDist)/g^2=0.1911  max abs/(g^2+1-t)=40.3077  identities (abs=|S(c0)|+nc, |S(c0)|<=|signed|+nc) all ok: True
   argmax nc/g^2 at (L,E,g,t)=(9, 0.0, 1.0, 0.99): signed=3.7309e-03 abs=4.0711e+01 |Sigma(c0)|=8.7631e-01 nc=3.9834e+01
routeB boundary n=4 Ls=[5, 9] #cases=20: max nc/g^2=4.9387  max_(delta nonconst)|Sigma|e^(0.5 maxDist)/g^2=0.5496  max abs/(g^2+1-t)=7.9945  identities (abs=|S(c0)|+nc, |S(c0)|<=|signed|+nc) all ok: True
   argmax nc/g^2 at (L,E,g,t)=(9, 0.0, 1.0, 0.9999): signed=5.0003e-05 abs=5.9117e+00 |Sigma(c0)|=9.7300e-01 nc=4.9387e+00
routeB boundary n=6 Ls=[5] #cases=10: max nc/g^2=30.0751  max_(delta nonconst)|Sigma|e^(0.5 maxDist)/g^2=0.1923  max abs/(g^2+1-t)=30.9504  identities (abs=|S(c0)|+nc, |S(c0)|<=|signed|+nc) all ok: True
   argmax nc/g^2 at (L,E,g,t)=(5, 0.0, 1.0, 0.9999): signed=3.7498e-05 abs=3.0953e+01 |Sigma(c0)|=8.7838e-01 nc=3.0075e+01
```
### Notes (narrative; every number above is from the script output)
1. Delivered: `RBM3D/Loop/KLMolecule.lean` (1029 lines), commit `ffa1a9e` on `t/T2070`; `git diff --stat main...t/T2070` shows this file only. `Test/Axioms.lean` is untouched (see 4).
2. Proved, all with the three standard axioms: target 1 `KLmolecule_holds`; target 2 `KLsumZero_holds` (signed and absolute estimate); extra `KLShort_holds`. `KLmoleculeAt`, `KLsumZeroAt` are the pins' defs and the two
   theorems state the pin bodies, character-identical after whitespace (script diff); `example : KLmoleculePin := KLmolecule_holds` (check file namespace, new module imported) compiles, exit 0.
3. `KLShort` is proved, so the pins hold unconditionally: `KLShort_holds` applies the merged `prop5Short_holds d gmax κ''` with `κ'' = √(κ(4-κ))/2 ≤ Im m(E)` for `|E| ≤ 2-κ` (`4-E² ≥ κ(4-κ)`),
   and `mSigma E s = PropSpin (mE E) s` is definitional; for `κ > 2` the bulk is empty (vacuous). The theorems keep `KLShort d κ gmax` as hypothesis, as pinned.
4. Registry (DECISIONS §16, §20): `Test/Axioms.lean:79` (`borrowedProps`) registers `KLPT`; `KLShort` occurs in that file nowhere, and outside the new file only in `KLTree.lean:278, 323` (greps above); it is not registered. Since `KLShort_holds` concludes it, the scan finds the same 79 premises with and without the new module (exit 0);
   without it, a theorem assuming `KLShort` makes the scan fail with `[RBM.Loop.KLShort]` (counterfactual above). `KLmoleculeAt`, `KLsumZeroAt` are concluded by their theorems and assumed by none: no registry line.
5. Target 1 (port of RBM2D `tree_bound`, `SigmaPi_bound`, `SigmaPi_empty_shortRange_prec`, `c9a24cf`): `KLselfW` is `KLtreeValW` with identity leaf matrices; in the layer `π = ∅` all internal edges have equal charges,
   and by translation invariance and `KLShort` every entry of `Θ - I` is `≤ B e^{-c_κ|x-y|}`, `B = C_κ(1+gmax²)+1` (`KLMolecule_edge`). `KLMolecule_tree_bound` sums the free node labels with the laminar path bound
   and `sum_exp_decay_centre` (`expC`, uniform in `L`): `C = |TSP n| B^{n²} expC(d-2, c_κ/(2n²))^{n²}`, `c = c_κ/2`, depending on `d, n, κ, gmax` only (no `L, W, g, t, E, σ`).
6. Changes against the RBM2D source: `Z2 L → Zd d L`, `zdist2 → zdistD`; `Prop5Hyp`, `UnifDetDom`, `absorb` and the gap section → the explicit constants of `KLShort`; `(1+2/λ)² → expC`; laminar API of `KLTree.lean`;
   no leaf factor `B^n` (identity leaves cost nothing for a labelling consistent with `δ`); `dist_bounds` is inlined. RBM2D HEAD differs from `c9a24cf` here only in comments and deleted declarations (block above).
7. Target 2(a): the merged `KLSigmaPi_alt_sumZero_le` with `η_t = (1-t) Im m ≤ 1-t`; `C_a = 2^{n²} n gapK(κ)^{-n} (2/√(κ(4-κ)))`.
8. Target 2(b) (new). The route differs from (a)'s expansion (`d_s I + O_s`, `P`, `R_b`, class peeling), none of which occurs in Lean. For `δ` in the slice `S = {δ_0 = x}`, `δ ≠ c₀ = (x,…,x)`:
   every labelling consistent with `δ` has an internal edge with different labels (`KLMolecule_const_of_edges`: equal labels on all edges force a constant labelling), that edge is bounded by `C_κ g² e^{-c_κ|x-y|}`
   (no `1_{a=0}`), so `|Σ(δ)| ≤ g² G₁ e^{-(c/2) max|δ_i-δ_j|}`. `∑_{δ∈S} e^{-(c/2) maxDist} ≤ expC(d-2, c/(2n))^{n-1}` (a product of one-point lattice sums, `KLMolecule_sum_slice`), so `∑_{S∖c₀}|Σ| ≤ g² R`.
   As `c₀ ∈ S`: `|Σ(c₀)| ≤ |signed| + g² R`, hence `∑_S |Σ| ≤ |signed| + 2 g² R ≤ C (g² + 1-t)`, `C = C_a + 2R + 1`, `R = G₁ expC(d-2, c/(2n))^{n-1}`, `G₁ = |TSP n| (C_κ/B) B^{n²} expC(d-2, c_κ/(2n²))^{n²}`.
9. Section (a) is unedited and has no error that changes a verdict (no (a′)). Lean's constants are not (a)'s table values (`C1`, `C_b`, `A0`); the pins are `∃ C c`, the constants are never evaluated.
10. Numerics for the route of the proof (`routeB.py`: `d=3`, `L ∈ {5,9}`, `E ∈ {0,1}`, `g ∈ {.05,.5,1}`, `t ∈ {0,.5,.9,.99}`, `n=4,6`, `σ^{alt}`, plus boundary points `g ∈ {.01,.05,.2,1}`, `t` up to `.9999`, `L=5` only for `n=6`): the identities
    `abs = |Σ(c₀)| + nc` and `|Σ(c₀)| ≤ |signed| + nc` hold in all 126 cases; fitted `nc/g² ≤ 4.94` (n=4), `≤ 39.84` (n=6); `sup_{δ≠c₀}|Σ| e^{0.5 maxDist}/g² ≤ 0.55` (n=4), `≤ 0.20` (n=6); the argmax of `nc/g²` has `t ≥ .99` in all four runs.
11. DECISIONS §29: (1) `0 ≤ t < 1` is `KLPar.ht0/ht1`, used for `‖t m m'‖ < 1`; `t = 0` and `t = .9999` are in the grids; (2) no `ilambda` window occurs; (3) no `L`–`W` relation is used, `W` does not enter `C, c`;
    (4) the pins quantify over the loop length `n`, not `N`; `n = 3` (star), `4`, `5` (odd), `6`, `8` are covered by instances; `g → 0`: `C` is `g`-free and 2(b) carries `g²`; `g = gmax`: `B` uses `gmax` (boundary instance `g = gmax = 1`, `|E| = 2-κ = 1`, `t = 99/100`, `n = 6`).
12. Instances (file §7): probe data `d=3, L=5, g=1/2, E=0, t=9/10, κ=gmax=1`. `n=3`: molecule at `δ=(0,1,2)` and at `(0,0,0)`, where `‖Σ‖ = 1` exactly (so `C ≥ 1`). `n=4`: the signed sum is exactly `1/19`
    (merged `SumZero_sum_slice_alt` with `Q(σ^{alt},∅)(t) = 1 + 2((1+t)⁻¹ - 1)`), so the absolute sum is `≥ 1/19`. Further `example`s: the boundary point and `n = 4, 5, 8`, `(κ, gmax) = (1/2, 2)`.

## (c) Verified Mathlib names used (script `names2.lean`: every name below occurs in the file and resolves with `import RBM3D.Loop.KLMolecule`, exit 0; the types of the non-obvious ones from `#check`, script `chk_names.lean`)
- `Finset.prod_univ_sum : ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ Fintype.piFinset t, ∏ i, f i (x i)`; `Fintype.mem_piFinset : f ∈ piFinset t ↔ ∀ a, f a ∈ t a`; `Fintype.piFinset_univ`
- `Finset.mul_prod_erase (s) (f) (h : a ∈ s) : f a * ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x`; `Finset.add_sum_erase` (same with `+`, `∑`); `Finset.card_erase_of_mem : #(s.erase a) = #s - 1`
- `Finset.exists_mem_eq_sup (s) (hne : s.Nonempty) (f) : ∃ i ∈ s, s.sup f = f i`; `Finset.le_sup`; `Finset.univ_nonempty`; `Finset.sum_coe_sort (s) (f) : ∑ i : ↥s, f ↑i = ∑ i ∈ s, f i`
- `Finset.prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ f ≤ ∏ g`; `Finset.single_le_sum (h : ∀ i ∈ s, 0 ≤ f i) (ha : a ∈ s) : f a ≤ ∑ x ∈ s, f x`; `Finset.prod_nonneg`, `Finset.sum_nonneg`
- `Finset.sum_le_sum_of_subset_of_nonneg (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 0 ≤ f i)`; `pow_le_pow_right₀ (1 ≤ a) (m ≤ n) : a ^ m ≤ a ^ n`; `pow_le_pow_left₀ (0 ≤ a) (a ≤ b) (n) : a ^ n ≤ b ^ n`
- `Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2`; `Matrix.one_apply_ne (h : i ≠ j) : 1 i j = 0`; `Matrix.one_apply`, `Matrix.one_apply_eq`, `Matrix.sub_apply`; `Nat.strong_induction_on`
- Also resolved: `Finset.card_le_card card_le_univ card_pos card_univ erase_subset filter_subset mem_erase mem_filter mem_insert mem_univ mul_sum ne_of_mem_erase prod_congr prod_const prod_empty prod_eq_one prod_eq_zero prod_mul_distrib prod_singleton sum_const sum_insert sum_le_sum sum_neg_distrib sum_singleton`;
  `Fintype.card_coe card_fin piFinset`; `Nat.cast_sum Nat.mul_pos NeZero.pos Ne.symm`; `Real.exp_add exp_le_exp exp_pos exp_sum sqrt_le_sqrt sqrt_nonneg sqrt_pos sqrt_sq`; `abs_nonneg add_le_add div_le_one div_nonneg iff_comm le_min le_of_eq mul_le_mul`
  `mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_nonneg mul_one mul_self_le_mul_self neg_mul neg_sub norm_mul norm_nonneg norm_prod norm_sub_le norm_sum_le norm_zero not_le nsmul_eq_mul one_mul sq_abs sq_nonneg sub_add_sub_cancel sub_eq_zero sub_self sub_zero true_and zero_add zero_le_one`.
- Absent: `expC_pos` (no such RBM3D lemma; positivity of `expC` is proved inline by `unfold expC; positivity`). Deprecated in this Mathlib (warnings of the first compile of this file): `if_pos`, `if_neg`, `if_true`; the final file uses `simp` instead and compiles without warnings.
- Merged project names used (all checked by the build): `KLnodePar_spec`, `KLleafPar_mem`, `KLnodePar_mem`, `KLmem_nodes_of_mem`, `KLisTSP_of_mem_TSP`, `KLArcLe.trans/antisymm`, `KLtreeValW_empty`, `KLSigmaPi_alt_sumZero_le`, `SumZero_sum_slice_alt`, `sum_exp_decay_centre`, `expC`, `prop5Short_holds` (`Propagator/Prop5Short.lean:400`), `Theta_apply_add_right_of_three_le`, `norm_mSigma`, `norm_mul_mSigma_lt_one`, `mE_im`, `norm_mE`, `zdistD_neg`, `zdistD_add_le`.

## (d) Open issues and paper-delta candidates
- `T2070a` (`(eq:Sigma-empty-sum-zero)`, `paper/tex/A_deterministic_estimates.tex:731`, second estimate): the paper writes `OO(ilambda² + |1-t|)` and cites [RBSO1D] Claim 4.30 ("dimension-independent"). Lean proves it for `d ≥ 3` from `(prop:ThfadC_short)` and the signed estimate:
  `∑_{δ_0=x}|Σ^{(∅)}(σ^{alt},δ)| ≤ C(g² + (1-t))`, `C = C(d,n,κ,gmax)`, every `0 < g ≤ gmax`, `|E| ≤ 2-κ`, `t ∈ [0,1)`, `L ≥ 3`, `W ≥ 1`, `n ≥ 4` even. [RBSO1D] Claim 4.30 is therefore not an external input.
- `T2070b` (`(eq:molecule-decay)`, `:691`, and the signed estimate of `(eq:Sigma-empty-sum-zero)`): the paper's "for some constants `c, C`" and `OO(|1-t|)` are explicit and depend on `(d, n, κ, gmax)` (bulk `|E| ≤ 2-κ`, `g ≤ gmax`); the molecule rate is `c = c_κ/2`. The statements are otherwise as in the paper.
- For the dispatcher: `KLShort_holds` proves `KLShort` for every `d ≥ 3`; KL10, KL12, KL14 can discharge the `KLShort` hypothesis of these pins and `KLPT.short` with it (the other four fields of `KLPT` are unchanged).
  The hub adds `import RBM3D.Loop.KLMolecule` after the last `import` of `RBM3D.lean` and runs the full build; the registry pre-check and the emulated full build (scratch clone) above both pass (exit 0, 3788 jobs).
- Open: `KLmolecule_holds` is the layer `π = ∅` only, as pinned (the cut at an innermost long edge, KL10-KL11, is untouched); `n ≥ 4` even enters `KLsumZero_holds` only through the merged signed bound and `∏ m = 1`.
  Exact instance values are computed for the `n = 3` star and the `n = 4` signed sum (`1/19`); the other instances apply the theorems without evaluating `Σ^{(∅)}`.
Report finished: Sat Oct  3 20:48:22 UTC 2026
