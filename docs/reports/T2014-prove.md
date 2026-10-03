Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 01:24:20 UTC 2026

Conventions (merged `Loop/KLTree.lean`, `Loop/Partition.lean`): vertices `0..n-1`; `KLwholeP n = (0, n-1)`; `KLInArc (i,j) v ⇔ i ≤ v < j`;
`KLArcLe d J ⇔ J.1 ≤ d.1 ∧ d.2 ≤ J.2`; `T_SP(n) = TSP n` = crossing-free sets of `IsDiag` pairs; `|T_SP(3)| = 1` (`TSP_three`), `|T_SP(4)| = 3`, `|T_SP(5)| = 11`.
Cut data (RBM2D `TreeRep.lean` at `c9a24cf`, git log -1 of RBM2D HEAD now `9e0f275`): `J = (i,j)`, `w := wIn J = j - i`, `IsDiag n i j ⇒ i + 2 ≤ j` (`width_of_isDiag`, :1382).

### (i) Exponent table (index and weight bookkeeping; no analytic exponents enter this ticket)

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| inside polygon vertices | `w + 1 = j - i + 1` | `3 ≤ w+1`, `w + 1 < n` (`isDiag_split_lt`) | `w ∈ [2, n-2]` for a diagonal |
| outside polygon vertices | `n - w + 1` | `3 ≤ n-w+1 < n` | `n - w + 1 ≥ 3` since `w ≤ n-2` |
| `\|F\|` | `\|F_in\| + \|F_out\| + 1` | edges of `F` = `{J}` ⊔ inside (`ArcLe d J, d ≠ J`) ⊔ outside (`¬ArcLe d J`) (`edgeEquiv`, :628) | exact; checked below |
| `inV J v` (`v ∈ [i,j)`) | `v - i ∈ [0, w-1]` | injective, image = `{0..w-1}`; inside leaf count `w` | the extra root leaf is the vertex `w = Fin.last`, label `u`, weight `Pᵀ` |
| `outV J v` (`v ∉ [i,j)`) | `col J v = v` if `v ≤ i`, `v - (w-1)` if `v ≥ j` | image = `{0..n-w}` minus `glueV J` | outside leaf count `n - w`; `n - w + 1` with the glue leaf |
| `glueV J` | `min i (n-w) = i` (as `i + w = j ≤ n-1 ⇒ i ≤ n-w-1`) | between `outV(i-1)` and `outV(j)`; label `w`(matrix index), weight `Q` | strict: `i < n - w` |
| `shiftIn J d` | `(d.1 - i, d.2 - i)` (truncating, `min _ w`) | `shiftIn J J = (0, w) = KLwholeP (w+1)` (`shiftIn_self`, :758) | exact |
| `shiftOut J d` | `(col d.1, col d.2)` (`min _ (n-w)`) | `shiftOut J (wholeP n) = wholeP (n-w+1)` (:1075); defined on edges with `OutEnds J` | exact |
| `glueF J G H` | `{J} ∪ unColP(G) ∪ unShift(H)` | inverse of `F ↦ (FOut, FIn)` | `FIn(glueF)=H`, `FOut(glueF)=G`, `glueF(FOut,FIn)=F` |
| cut bijection | `#{F ∈ T_SP(n) : J ∈ F} = \|T_SP(n-w+1)\| · \|T_SP(w+1)\|` | needs `2 ≤ n`, `IsDiag n J.1 J.2` (`hJd`) | exact; `KLsum_cut` has `∑_F f(F_out,F_in) = ∑_G ∑_H f G H` |
| weight on cut edge | `E J := P S Q` | tree value = `∑_{u,w} V_in(root leaf (u, Pᵀ)) · S_{uw} · V_out(glue leaf (w, Q))` | `P_{b_J,u} = (Pᵀ)_{u,b_J}`, `Q_{w,b_par}` used as stated; other edges/leaf weights unchanged |
| new root leaves | in: `a'(last) = u`, `M'(last) = Pᵀ`; out: `a'(glueV) = w`, `M'(glueV) = Q` | `gval_in_eq` (:818), `gval_out_eq` (:1102) | exact |
| index set | `Zd d L` replaces `Z2 L` | the statements and proofs use only `Fintype`, matrix product, sums; no dimension-specific fact | `d = 3, L = 3`: 27 points; nothing depends on `d` |
| diagonal existence | `T_SP(n)` contains a nonempty `F` iff `n ≥ 4` | `J ∈ F` with `IsDiag n J.1 J.2` forces `n ≥ 4` | **`n = 3` has no diagonal, so `KLtreeValW_cut` has no instance at `n = 3`** (see (ii)) |

Ticket-vs-source mismatches found (precise):
1. The ticket's renaming "`gval → KLtreeValG`" is wrong. RBM2D `gval` (TreeRep.lean:422, in section `Generic` 415–509; generic tree value over node/leaf/edge types) is in the public statement of `treeValW_cut` (:648). `KLtreeValG` (KLTree.lean:123) is a different object (`m t σ a F`, with `thetaEdge`). No `gval`, `gval_congr`, `gval_split`, `treeValW_eq_gval` (TreeRep.lean:422, 431, 480, 515) exists in `RBM3D/` (grep below, empty). They lie outside the ticket's line range 545–1674 (T2008 ported 185–413 only). The port needs them (lines 415–522) as public `KL`-prefixed defs/lemmas (a name for `gval` must be fixed, e.g. `KLgval`).
2. The ticket's instance "`KLtreeValW_cut` at `n = 3` with one concrete `F`" cannot exist (hypothesis `J ∈ F`, `F` ∈ `T_SP(3) = {∅}`).

### (ii) One concrete nondegenerate instance

Instance A (`KLsum_cut`): `n = 5`, `J = (1,3)`, `f = fun _ _ => 1`: `IsDiag 5 1 3`, `w = 2`, inside 3-gon, outside 4-gon; both sides `= 3`.
Instance B (`KLtreeValW_cut`, replacing the impossible `n = 3`): `n = 4`, `F = {(0,2)}`, `J = (0,2)`, `d = 3`, `L = 3` (inside 3-gon, outside 3-gon, `F_in = F_out = ∅`); richer: `n = 5`, `F = {(0,2),(0,3)}`, `J = (0,3)` (`F_in = {(0,2)}` in a 4-gon, `F_out = ∅`) and `J = (0,2)` (`F_out = {(0,2)}`).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/inst.py`
```
n=3: diagonals=[]  |TSP|=1  #F containing a diagonal=0
n=4: diagonals=[(0, 2), (1, 3)]  |TSP|=3  #F containing a diagonal=2
n=5: diagonals=[(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]  |TSP|=11  #F containing a diagonal=10
IsDiag 5 1 3 = True ; wIn = 2 ; out-polygon n-wIn+1 = 4 ; in-polygon wIn+1 = 3
KLsum_cut, f=1: LHS = 3  RHS = |TSP 4|*|TSP 3| = 3 * 1 = 3
F in TSP 5 with (1,3): [[(1, 3)], [(0, 3), (1, 3)], [(1, 3), (1, 4)]]
```
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/cutcheck.py` (Python transcription of the Lean definitions `IsDiag`, `Crossing`, `FIn`, `shiftIn`, `col`, `FOut`, `shiftOut`, `glueF`, `inV`, `outV`, `glueV`, `KLleafPar`, `KLnodePar`; for every diagonal `J`, `n = 4..7`, it checks: count identity, `FOut,FIn ∈ T_SP`, `glueF(FOut,FIn) = F`, `FOut(glueF G H) = G`, `FIn(glueF G H) = H`, `glueF(G,H) ∈ T_SP(n) ∋ J`, injectivity of `F ↦ (FOut,FIn)`, `|F| = |F_in|+|F_out|+1`, `inV`/`outV`/`glueV` bijections, `shiftIn J J = (0,w)`). Last 12 lines of output:
```
   n=7 J=(4, 6) w=2 in-polygon 3-gon out-polygon 6-gon  #{F:J in F}=45  |T(6)|*|T(3)|=45
n=7: |T_SP|=197, 14 diagonals, all checks: True
TSP(3) = {frozenset()}
n=5 d=3 L=3 F=[(0, 2), (0, 3)] J=(0, 2): F_in=[] (3-gon) F_out=[(0, 2)] (4-gon)  |lhs-rhs|=1.94e-17  |lhs|=2.391e-02
n=5 d=3 L=3 F=[(0, 2), (0, 3)] J=(0, 3): F_in=[(0, 2)] (4-gon) F_out=[] (3-gon)  |lhs-rhs|=1.07e-16  |lhs|=2.684e-02
n=5 d=3 L=3 F=[(1, 3), (1, 4)] J=(1, 3): F_in=[] (3-gon) F_out=[(1, 3)] (4-gon)  |lhs-rhs|=6.55e-17  |lhs|=5.296e-02
n=5 d=3 L=3 F=[(1, 3), (1, 4)] J=(1, 4): F_in=[(0, 2)] (4-gon) F_out=[] (3-gon)  |lhs-rhs|=8.04e-17  |lhs|=1.489e-02
n=4 d=3 L=3 F=[(0, 2)] J=(0, 2): F_in=[] (3-gon) F_out=[] (3-gon)  |lhs-rhs|=1.57e-16  |lhs|=6.434e-02
```
and the per-`n` lines `n=4: |T_SP|=3, 2 diagonals, all checks: True`, `n=5: |T_SP|=11, 5 diagonals, all checks: True`, `n=6: |T_SP|=45, 9 diagonals, all checks: True`, `n=7: |T_SP|=197, 14 diagonals, all checks: True`; every diagonal printed for `n = 4, 5` (e.g. `n=5 J=(1, 3): #{F:J in F}=3 = |T(4)|*|T(3)|=3`). The numerical cut identity: random complex 27×27 matrices (`M_v, E_e, P, S, Q`), random labels `a`, tree value computed by the full sum over node labelings (`27^{|nodes|}` terms) on both sides.
External hypotheses: none (no `Prop` hypothesis, no limit computation needed).
Gap grep: `grep -rn "gval\|treeValW_eq" /Users/junyin/Lean_proof/RBM3D/RBM3D | grep -v KLtreeValW_eq_sum_selfW` returns no line other than `KLtreeValW_eq_sum_selfW` uses.

### Verdicts
- `KLsum_cut`, `KLFIn`, `KLFOut`, `KLglueF`, `KLFIn_mem_TSP`, `KLFOut_mem_TSP`, `KLglueF_mem_TSP`, `KLglueF_cut`, `KLFIn_glueF`, `KLFOut_glueF`: PASS (statements true; instance A).
- `KLtreeValW_cut`: statement true (instance B, `n ≥ 4`); the ticket's stated instance `n = 3` is FAIL (no `F ∋ J` exists in `T_SP(3)`); replace by `n = 4`, `F = {(0,2)}`.
- Ticket mapping `gval → KLtreeValG`: FAIL as written (different object); the generic value (TreeRep.lean:415–522) must be added as a public `KL`-prefixed def with its transport lemmas (dispatcher to confirm the name and that this lies in the sole writable file).
Overall verdict: FAIL (ticket text: instance at `n = 3` impossible; `gval` mapping wrong). The mathematics of every target holds.

### (a″) Confirmation of Amend 1 (CONTROL H13) — Sat Oct  3 01:56:57 UTC 2026

Point 1 (generic value, `gval → KLgval`). Source read at `c9a24cf` (`TreeRep.lean` 415–543: `gval` :422, `gval_congr` :431, `sum_perm4`/`sum_perm4'` private, `gval_split` :480, `treeValW_eq_gval` :515). `gval` is `∑ b : Nd → Z2 L, (∏ ℓ, M ℓ (a ℓ) (b (p ℓ))) * ∏ e, E e (b (c e)) (b (q e))`; the merged `KLtreeValW` (KLTree.lean:114–119) is the same sum with `Nd = ↥(KLnodes F)`, `Lf = Fin n`, `Ed = ↥F`, `Z2 L → Zd d L`; so `KLtreeValW_eq_gval` is `rfl` as in RBM2D. The statements use only `Fintype`, `DecidableEq Nd`, matrix product and sums: no dimension-specific fact; only `[NeZero L]` is needed (as in KLTree.lean:109). `gval_split` is an algebraic identity (`Fintype.prod_sum_type`, `Matrix.mul_apply`, reorder of a fourfold sum): true for every `d, L`. `KLtreeValW_empty` is merged (KLTree.lean:161): not duplicated. The grep `gval` in `RBM3D/` is empty (clash-free). Verdict: PASS.

Point 2 (instance `n = 4`, `F = {(0,2)}`, `J = (0,2)`). Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/amend1.py`
```
IsDiag 4 0 2 = True ; F in TSP(4): True ; w = 2 ; in-polygon 3 ; out-polygon 3
#F in TSP(4) with J = 1 ; |TSP(3)|*|TSP(3)| = 1
nodes(F) = 2 = nodes(F_out)+nodes(F_in) = 2 ; edges |F| = 1 = 0+0+1 ; leaves n = 4 = (3-1 glue)+(3-1 root)
```
All hypotheses of `KLtreeValW_cut` hold (`IsDiag 4 0 2`, `F ∈ T_SP(4)`, `J ∈ F`, `2 ≤ n`, `NeZero 4`); `F_in = F_out = ∅` (two 3-gons); numerical cut identity at `n = 4, d = 3, L = 3`, same `F`, `J`: `|lhs-rhs| = 1.57e-16`, `|lhs| = 6.434e-02` (cutcheck.py output above, line `n=4 d=3 L=3 ...`). No external hypothesis. The `KLsum_cut` instance (`n = 5`, `J = (1,3)`, `f = 1`, both sides `3`) is unchanged and stands (Instance A).

Verdict on the ticket as amended: **PASS** for every target (`KLgval`, `KLgval_congr`, `KLgval_split`, `KLtreeValW_eq_gval`, `KLtreeValW_cut`, `KLsum_cut` and the listed objects/membership lemmas).

## (b) Script output — Sat Oct  3 03:16:16 UTC 2026

Scripts are in `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad` (outside the repository); `WT=/Users/junyin/Lean_proof/RBM3D-wt/T2014`, `MAIN=/Users/junyin/Lean_proof/RBM3D`, `R2=/Users/junyin/Lean_proof/RBM2D`. Each block is a command and its output; a filter is part of the command.

### b1 Branch, scope, hygiene
```
$ git -C $WT log --format='%h %an <%ae> %s' main..t/T2014; git -C $WT diff --stat main...t/T2014; git -C $WT status --short
b470e51 Jun Yin <321276894+JYin80@users.noreply.github.com> T2014: KL2 cut of a tree at an internal edge and the cut bijection
 RBM3D/Loop/KLCut.lean | 1648 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1648 insertions(+)
$ grep -cE 'sorry|admit|native_decide|^axiom|^ *axiom ' RBM3D/Loop/KLCut.lean
0
$ grep -nE '3 ≤ d|d ≥ 3|hd3' RBM3D/Loop/KLCut.lean
10:# The cut of a tree at an internal edge and the cut bijection (KL2), `d ≥ 3`
```
### b2 Builds (copied from the tool log of the runs)
```
$ rm $WT/.lake/build/lib/lean/RBM3D/Loop/KLCut.{olean,olean.hash,ilean,ilean.hash,trace}; date -u; (time lake build RBM3D.Loop.KLCut); date -u
Sat Oct  3 02:57:57 UTC 2026
Sat Oct  3 02:58:17 UTC 2026
✔ [3237/3237] Built RBM3D.Loop.KLCut (16s)
Build completed successfully (3237 jobs).
lake build RBM3D.Loop.KLCut  19.85s user 6.18s system 133% cpu 19.539 total
$ [$WT/RBM3D.lean: `import RBM3D.Loop.KLCut` added after `import RBM3D.Loop.KLTree`, uncommitted, removed again (b1 status empty)]; date -u; lake build; date -u
$ grep -nE 'warning|Built RBM3D |axiom audit|Build completed' $SP/build_full.txt     [run 02:58:31 - 02:58:41 UTC; the audit line is followed by 'All within [propext, Classical.choice, Quot.sound]']
4:warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
7:ℹ [3691/3692] Built RBM3D (6.3s)
8:info: RBM3D.lean:54:0: axiom audit: 795 theorems, 322 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
42:Build completed successfully (3692 jobs).
```
### b3 Axioms and privacy (`axioms_check.lean`: `#print axioms` of the 14 theorem targets and the 2 pinned instances, then a meta-command over the module; `privcheck.lean`)
```
$ lake env lean $SP/axioms_check.lean | grep 'depends on axioms' | sed/sort/awk (group by axiom set)
16 theorems with axioms [propext, Classical.choice, Quot.sound]: KLCutInst_sum_cut KLCutInst_treeValW_cut KLFIn_glueF KLFIn_mem_TSP KLFOut_glueF KLFOut_mem_TSP KLglueF_cut KLglueF_mem_TSP KLgval_congr KLgval_in_eq KLgval_out_eq KLgval_split KLhasDerivAt_treeValW KLsum_cut KLtreeValW_cut KLtreeValW_eq_gval
$ lake env lean $SP/axioms_check.lean | grep -A2 '^module RBM3D' | tr '\n' ' '
module RBM3D.Loop.KLCut: 100 non-internal constants (64 theorems, 36 definitions); union of axioms over all of them: [Quot.sound,  Classical.choice,  propext]; sorry-free: true 
$ lake env lean $SP/privcheck.lean
public constants: 100; private constants (all kinds): 101; public statements/definition bodies mentioning a private constant: 0 []
```
### b4 Name clashes (whole-word `git grep` of every declared name of KLCut.lean in `main:RBM3D` and `main:RBM3D.lean`; `$SP/clash.sh public|private`)
```
$ git -C $MAIN log -1 --format='main = %h' main; $SP/clash.sh public | awk '{n++; if ($2>0) {print; bad++}} END{print n " public names checked, " bad+0 " with a hit on main"}'    # likewise private
main = 33049c0
92 public names checked, 0 with a hit on main
29 private names checked, 0 with a hit on main
```
### b5 Statements of the targets and of the objects they mention (`python3 $SP/stmt.py RBM3D/Loop/KLCut.lean <names>`: theorems up to the first `:=`, defs whole; whitespace collapsed; leading number = line in KLCut.lean)
```
58: noncomputable def KLgval {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf] [Fintype Ed] (a : Lf → Zd d L) (M : Lf → Matrix (Zd d L) (Zd d L) ℂ) (p : Lf → Nd) (E : Ed → Matrix (Zd d L)
      (Zd d L) ℂ) (c q : Ed → Nd) : ℂ := ∑ b : Nd → Zd d L, (∏ ℓ, M ℓ (a ℓ) (b (p ℓ))) * ∏ e, E e (b (c e)) (b (q e))
67: theorem KLgval_congr {Nd Lf Ed Nd' Lf' Ed' : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf] [Fintype Ed] [Fintype Nd'] [DecidableEq Nd'] [Fintype Lf'] [Fintype Ed'] (eN : Nd ≃ Nd') (eL : Lf ≃
      Lf') (eE : Ed ≃ Ed') {a : Lf → Zd d L} {M : Lf → Matrix (Zd d L) (Zd d L) ℂ} {p : Lf → Nd} {E : Ed → Matrix (Zd d L) (Zd d L) ℂ} {c q : Ed → Nd} {a' : Lf' → Zd d L} {M' : Lf' → Matrix (Zd d L)
      (Zd d L) ℂ} {p' : Lf' → Nd'} {E' : Ed' → Matrix (Zd d L) (Zd d L) ℂ} {c' q' : Ed' → Nd'} (ha : ∀ ℓ, a' (eL ℓ) = a ℓ) (hM : ∀ ℓ, M' (eL ℓ) = M ℓ) (hp : ∀ ℓ, p' (eL ℓ) = eN (p ℓ)) (hE : ∀ e, E'
      (eE e) = E e) (hc : ∀ e, c' (eE e) = eN (c e)) (hq : ∀ e, q' (eE e) = eN (q e)) : KLgval d L a M p E c q = KLgval d L a' M' p' E' c' q' := ...
116: theorem KLgval_split {N₁ N₂ Lf₁ Lf₂ Ed₁ Ed₂ : Type*} [Fintype N₁] [DecidableEq N₁] [Fintype N₂] [DecidableEq N₂] [Fintype Lf₁] [Fintype Lf₂] [Fintype Ed₁] [Fintype Ed₂] (a₁ : Lf₁ → Zd d L) (M₁ :
      Lf₁ → Matrix (Zd d L) (Zd d L) ℂ) (p₁ : Lf₁ → N₁) (E₁ : Ed₁ → Matrix (Zd d L) (Zd d L) ℂ) (c₁ q₁ : Ed₁ → N₁) (a₂ : Lf₂ → Zd d L) (M₂ : Lf₂ → Matrix (Zd d L) (Zd d L) ℂ) (p₂ : Lf₂ → N₂) (E₂ : Ed₂
      → Matrix (Zd d L) (Zd d L) ℂ) (c₂ q₂ : Ed₂ → N₂) (P S Q : Matrix (Zd d L) (Zd d L) ℂ) (c₀ : N₂) (q₀ : N₁) : KLgval d L (Sum.elim a₁ a₂) (Sum.elim M₁ M₂) (Sum.elim (Sum.inl ∘ p₁) (Sum.inr ∘ p₂))
      (fun o : Option (Ed₁ ⊕ Ed₂) => o.elim (P * S * Q) (Sum.elim E₁ E₂)) (fun o => o.elim (Sum.inr c₀) (Sum.elim (Sum.inl ∘ c₁) (Sum.inr ∘ c₂))) (fun o => o.elim (Sum.inl q₀) (Sum.elim (Sum.inl ∘ q₁)
      (Sum.inr ∘ q₂))) = ∑ u : Zd d L, ∑ w : Zd d L, KLgval d L (fun o : Option Lf₂ => o.elim u a₂) (fun o => o.elim P.transpose M₂) (fun o => o.elim c₀ p₂) E₂ c₂ q₂ * S u w * KLgval d L (fun o :
      Option Lf₁ => o.elim w a₁) (fun o => o.elim Q M₁) (fun o => o.elim q₀ p₁) E₁ c₁ q₁ := ...
153: theorem KLtreeValW_eq_gval (F : Finset (Fin n × Fin n)) (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) : KLtreeValW d L F a M E = KLgval d L a
      M (fun v => (⟨KLleafPar F v, KLleafPar_mem F v⟩ : ↥(KLnodes F))) E (fun d => (⟨d.1, KLmem_nodes_of_mem d.2⟩ : ↥(KLnodes F))) (fun d => (⟨KLnodePar F d, KLnodePar_mem F d⟩ : ↥(KLnodes F))) := ...
282: theorem KLtreeValW_cut (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (P S Q : Matrix (Zd d L) (Zd d L) ℂ) : KLtreeValW d L F a M
      (Function.update E ⟨J, hJ⟩ (P * S * Q)) = ∑ u : Zd d L, ∑ w : Zd d L, KLgval d L (fun o : Option (KLLIn J) => o.elim u (fun v => a v.1)) (fun o => o.elim P.transpose (fun v => M v.1)) (fun o =>
      o.elim (KLcutIn hJ) (KLinLeafPar hF hJ)) (fun d : KLEIn F J => E d.1) KLinChild (KLinPar hF hn hJ) * S u w * KLgval d L (fun o : Option (KLLOut J) => o.elim w (fun v => a v.1)) (fun o => o.elim
      Q (fun v => M v.1)) (fun o => o.elim (KLcutOut hF hn hJ) (KLoutLeafPar hF hJ)) (fun d : KLEOut F J => E d.1) KLoutChild (KLoutPar hF hn) := ...
1297: theorem KLsum_cut (hn : 2 ≤ n) (f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) → Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ) : ∑ F ∈ (TSP n).filter (fun F => J ∈ F), f
      (KLFOut F J) (KLFIn F J) = ∑ G ∈ TSP (n - KLwIn J + 1), ∑ H ∈ TSP (KLwIn J + 1), f G H := ...
361: def KLwIn (J : Fin n × Fin n) : ℕ := J.2.val - J.1.val
368: def KLFIn (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) := (F.filter fun d => KLArcLe d J ∧ d ≠ J).image (KLshiftIn J)
589: def KLFOut (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) := (F.filter fun d => ¬KLArcLe d J).image (KLshiftOut J)
373: def KLinV (J : Fin n × Fin n) (v : Fin n) : Fin (KLwIn J + 1) := ⟨min (v.val - J.1.val) (KLwIn J), by omega⟩
594: def KLoutV (J : Fin n × Fin n) (v : Fin n) : Fin (n - KLwIn J + 1) := ⟨min (KLcol J v.val) (n - KLwIn J), by omega⟩
598: def KLglueV (J : Fin n × Fin n) : Fin (n - KLwIn J + 1) := ⟨min J.1.val (n - KLwIn J), by omega⟩
1019: def KLglueF (J : Fin n × Fin n) (G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))) (H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))) : Finset (Fin n × Fin n) := insert J (G.image
      (KLunColP J) ∪ H.image (KLunShift J))
1038: theorem KLFIn_mem_TSP {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) : KLFIn F J ∈ TSP (KLwIn J + 1) := ...
1070: theorem KLFOut_mem_TSP {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) : KLFOut F J ∈ TSP (n - KLwIn J + 1) := ...
1140: theorem KLglueF_mem_TSP {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))} {H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} (hG : G ∈ TSP (n - KLwIn J + 1)) (hH : H ∈ TSP (KLwIn J
      + 1)) : KLglueF J G H ∈ TSP n := ...
1266: theorem KLglueF_cut {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) : KLglueF J (KLFOut F J) (KLFIn F J) = F := ...
1221: theorem KLFIn_glueF {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))} {H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} (hG : G ∈ TSP (n - KLwIn J + 1)) (hH : H ∈ TSP (KLwIn J +
      1)) : KLFIn (KLglueF J G H) J = H := ...
1243: theorem KLFOut_glueF {G : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1))} {H : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1))} (hG : G ∈ TSP (n - KLwIn J + 1)) : KLFOut (KLglueF J G H) J
      = G := ...
$ lake env lean $SP/hyps.lean | sed -E 's/\[inst\._@[^ ]* : /[/g; s/RBM\.Loop\.//g'     # instance binders and Prop-typed binders of each theorem; 'of k' = number of binders
KLtreeValW_cut: [NeZero L] [NeZero n] (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)  (of 16 binders)
KLsum_cut: [NeZero n] (hJd : IsDiag n J.1 J.2) (hn : 2 ≤ n)  (of 6 binders)
KLFIn_mem_TSP: (hF : KLIsTSP F)  (of 4 binders)
KLFOut_mem_TSP: [NeZero n] (hJd : IsDiag n J.1 J.2) (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)  (of 8 binders)
KLglueF_mem_TSP: [NeZero n] (hJd : IsDiag n J.1 J.2) (hG : G ∈ TSP (n - KLwIn J + 1)) (hH : H ∈ TSP (KLwIn J + 1))  (of 8 binders)
KLglueF_cut: [NeZero n] (hJd : IsDiag n J.1 J.2) (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)  (of 8 binders)
KLFIn_glueF: [NeZero n] (hJd : IsDiag n J.1 J.2) (hG : G ∈ TSP (n - KLwIn J + 1)) (hH : H ∈ TSP (KLwIn J + 1))  (of 8 binders)
KLFOut_glueF: [NeZero n] (hJd : IsDiag n J.1 J.2) (hG : G ∈ TSP (n - KLwIn J + 1))  (of 7 binders)
```
### b6 Port against RBM2D `TreeRep.lean` 415-1667 at `c9a24cf` (`portdiff.py`: per declaration, comments and modifiers dropped, whitespace collapsed; the RBM2D text renamed by the ticket's map: `Z2 L`->`Zd d L`, each RBM2D declared name x with a declared `KLx` in KLTree.lean/KLCut.lean -> `KLx`, `(L : ℕ)`->`(d L : ℕ)`; compared as strings, statement and proof)
```
$ python3 $SP/portdiff.py summary; python3 $SP/portdiff.py rows | grep -v 'identical after renaming'; python3 $SP/portdiff.py tokdiff hasDerivAt_treeValW; python3 $SP/ctxdiff.py; python3 $SP/extras.py
88 identical after renaming
1 MISSING in RBM3D
1 STATEMENT DIFFERS
RBM3D-only (non-instance) declarations: []
---
treeValW_empty | KLtreeValW_empty | MISSING in RBM3D | 
hasDerivAt_treeValW | KLhasDerivAt_treeValW | STATEMENT DIFFERS | public
---
replace: RBM2D(renamed) `d`  ->  RBM3D `e`
replace: RBM2D(renamed) `d`  ->  RBM3D `e`
replace: RBM2D(renamed) `d)))`  ->  RBM3D `e)))`
---
context lines (variable/include/omit/section/end/namespace/open/set_option): RBM2D 60, RBM3D 63
--- RBM2D(renamed) 415-1667
+++ RBM3D KLCut.lean
@@ -0,0 +1,3 @@
+set_option linter.style.longLine false
+namespace RBM.Loop
+open Finset
@@ -3 +6 @@
-variable {L}
+variable {d L}
---
extra public names (not in the ticket list, Amend 1 list or the statement/definition closure): 22
T = TreeRep.lean:1668-2587, K = KBoundCut.lean:1522-2138, S = SumZeroWard.lean:937-2085 (all at c9a24cf): RBM2D files whose downstream code mentions the RBM2D name
KLprod_update_eq (prod_update_eq) TK; KLhasDerivAt_treeValW (hasDerivAt_treeValW) T; KLshiftIn_val (shiftIn_val) TKS; KLinV_val (inV_val) TK; KLshiftIn_injOn (shiftIn_injOn) S; KLgval_in_eq
(gval_in_eq) TK; KLOutEnds (OutEnds) KS; KLcol_of_le (col_of_le) TK; KLcol_of_gt (col_of_gt) TK; KLshiftOut_val (shiftOut_val) TKS; KLoutV_val (outV_val) TK; KLshiftOut_injOn
(shiftOut_injOn) KS; KLdiag_width (diag_width) KS; KLoutEnds_of (outEnds_of) TKS; KLgval_out_eq (gval_out_eq) TK; KLunShift_val (unShift_val) TK; KLunColP_val (unColP_val) TK; KLunCol_of_le
(unCol_of_le) TKS; KLunCol_of_gt (unCol_of_gt) TKS; KLunCol_col (unCol_col) TKS; KLmem_diagonals_iff (mem_diagonals_iff) T; KLwidth_of_isDiag (width_of_isDiag) TKS
```
### b7 Compiled instances at d = 3, L = 3 (`python3 $SP/full.py RBM3D/Loop/KLCut.lean <names>`: whole declaration), in `section Instances` (KLCut.lean:1332-1646)
```
1337: theorem KLCutInst_sum_cut : ∑ F ∈ (TSP 5).filter (fun F => ((1 : Fin 5), (3 : Fin 5)) ∈ F), (fun _ _ => (1 : ℂ)) (KLFOut F ((1 : Fin 5), (3 : Fin 5))) (KLFIn F ((1 : Fin 5), (3 : Fin 5))) = ∑ G
      ∈ TSP (5 - KLwIn ((1 : Fin 5), (3 : Fin 5)) + 1), ∑ H ∈ TSP (KLwIn ((1 : Fin 5), (3 : Fin 5)) + 1), (fun _ _ => (1 : ℂ)) G H := KLsum_cut (n := 5) (J := ((1 : Fin 5), (3 : Fin 5))) (by decide)
      (by norm_num) (fun _ _ => 1)
1345: theorem KLCutInst_sum_cut_count : ((TSP 5).filter (fun F => ((1 : Fin 5), (3 : Fin 5)) ∈ F)).card = 3 ∧ (TSP 4).card * (TSP 3).card = 3 := ⟨by decide, by decide⟩
1434: def KLCutInst_F4 : Finset (Fin 4 × Fin 4) := {(0, 2)}
1441: def KLCutInst_σ4 : Fin 4 → Bool := ![true, false, true, false]
1444: def KLCutInst_a4 : Fin 4 → Zd 3 3 := ![0, 1, 2, 0]
1447: noncomputable def KLCutInst_M4 : Fin 4 → Matrix (Zd 3 3) (Zd 3 3) ℂ := fun v => thetaEdge 3 3 (1 / 2) (mSigma 0) (9 / 10) (KLCutInst_σ4 v) (KLCutInst_σ4 (v + 1))
1451: noncomputable def KLCutInst_E4 : ↥KLCutInst_F4 → Matrix (Zd 3 3) (Zd 3 3) ℂ := fun e => thetaEdge 3 3 (1 / 2) (mSigma 0) (9 / 10) (KLCutInst_σ4 e.1.1) (KLCutInst_σ4 e.1.2) - 1
1455: noncomputable def KLCutInst_P4 : Matrix (Zd 3 3) (Zd 3 3) ℂ := thetaEdge 3 3 (1 / 2) (mSigma 0) (9 / 10) (KLCutInst_σ4 0) (KLCutInst_σ4 2)
1436: theorem KLCutInst_F4_mem : KLCutInst_F4 ∈ TSP 4 := by decide
1438: theorem KLCutInst_J4_mem : ((0 : Fin 4), (2 : Fin 4)) ∈ KLCutInst_F4 := by decide
1461: theorem KLCutInst_treeValW_cut : KLtreeValW 3 3 KLCutInst_F4 KLCutInst_a4 KLCutInst_M4 (Function.update KLCutInst_E4 ⟨((0 : Fin 4), (2 : Fin 4)), KLCutInst_J4_mem⟩ (KLCutInst_P4 * SB 3 3 (1 / 2)
      * KLCutInst_P4)) = ∑ u : Zd 3 3, ∑ w : Zd 3 3, KLgval 3 3 (fun o : Option (KLLIn ((0 : Fin 4), (2 : Fin 4))) => o.elim u (fun v => KLCutInst_a4 v.1)) (fun o => o.elim KLCutInst_P4.transpose (fun
      v => KLCutInst_M4 v.1)) (fun o => o.elim (KLcutIn KLCutInst_J4_mem) (KLinLeafPar (KLisTSP_of_mem_TSP KLCutInst_F4_mem) KLCutInst_J4_mem)) (fun e : KLEIn KLCutInst_F4 ((0 : Fin 4), (2 : Fin 4))
      => KLCutInst_E4 e.1) KLinChild (KLinPar (KLisTSP_of_mem_TSP KLCutInst_F4_mem) (by norm_num) KLCutInst_J4_mem) * SB 3 3 (1 / 2) u w * KLgval 3 3 (fun o : Option (KLLOut ((0 : Fin 4), (2 : Fin
      4))) => o.elim w (fun v => KLCutInst_a4 v.1)) (fun o => o.elim KLCutInst_P4 (fun v => KLCutInst_M4 v.1)) (fun o => o.elim (KLcutOut (KLisTSP_of_mem_TSP KLCutInst_F4_mem) (by norm_num)
      KLCutInst_J4_mem) (KLoutLeafPar (KLisTSP_of_mem_TSP KLCutInst_F4_mem) KLCutInst_J4_mem)) (fun e : KLEOut KLCutInst_F4 ((0 : Fin 4), (2 : Fin 4)) => KLCutInst_E4 e.1) KLoutChild (KLoutPar
      (KLisTSP_of_mem_TSP KLCutInst_F4_mem) (by norm_num)) := KLtreeValW_cut 3 3 (KLisTSP_of_mem_TSP KLCutInst_F4_mem) (by norm_num) KLCutInst_J4_mem KLCutInst_a4 KLCutInst_M4 KLCutInst_E4
      KLCutInst_P4 (SB 3 3 (1 / 2)) KLCutInst_P4
applications inside `section Instances` (whole-word count, comments stripped): KLgval_congr:1 KLgval_split:1 KLtreeValW_eq_gval:1 KLtreeValW_cut:1 KLsum_cut:1 KLFIn_mem_TSP:1 KLFOut_mem_TSP:1 KLglueF_mem_TSP:1 KLglueF_cut:1 KLFIn_glueF:1 KLFOut_glueF:1 KLgval_in_eq:1 KLgval_out_eq:1 KLhasDerivAt_treeValW:1
```
### b8 Ports (source project, file:line, commit)
```
$ git -C $R2 --no-optional-locks log -1 --format=%h c9a24cf; git -C $R2 --no-optional-locks log -1 --format=%h; git -C $R2 --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/TreeRep.lean
c9a24cf
9e0f275
 RBM2D/Loop/TreeRep.lean | 58 ++++++++++++++++++-------------------------------
 1 file changed, 21 insertions(+), 37 deletions(-)
$ git -C $R2 --no-optional-locks diff -U0 c9a24cf HEAD -- RBM2D/Loop/TreeRep.lean | grep '^@@' | sed 's/ @@.*/ @@/' | tr '\n' ' '
@@ -11,15 +11,13 @@ @@ -36 +34 @@ @@ -179 +177 @@ @@ -251,6 +248,0 @@ @@ -2020 +2012 @@ @@ -2553 +2545 @@ @@ -2555 +2547 @@ @@ -2560,2 +2552,2 @@ @@ -2577,9 +2569 @@ 
```
Ported: RBM2D `RBM2D/Loop/TreeRep.lean` lines 415-1667 at `c9a24cf` (sections Generic 415, Value 511, Cut 583, CutIn 722, CutOut 938, CutBij 1265-1667, section Assembly starts at 1669; `treeValW_cut` :648, `sum_cut` :1643). RBM1D: nothing ported.

### Narrative (restart run of stage 1b)
1. At restart `t/T2014` already carried `b470e51` (one commit, `RBM3D/Loop/KLCut.lean`, 1648 lines, from the interrupted run) and the worktree was clean (b1). I did not edit or recommit the Lean file; I re-verified it (b1-b8) and wrote (b)-(d), which this report lacked.
2. The file ports RBM2D `TreeRep.lean` 415-1667 at `c9a24cf` (Amend 1's `Generic`/`Value` sections and the ticket's 545-1674) with `Z2 L` to `Zd d L` and the merged KL1 names. The only hypotheses on `d`, `L` are `(d L : ℕ) [NeZero L]`; the grep for `3 ≤ d` / `d ≥ 3` finds only the module-doc title (b1).
3. Fidelity (b6): of the 90 RBM2D declarations in the range, 88 equal the file's after the renaming (statement and proof; whitespace and comments ignored). `treeValW_empty` is the merged `KLtreeValW_empty` (KLTree.lean:161), not duplicated (Amend 1). `hasDerivAt_treeValW` differs only in a bound variable (`d` to `e`; `d` is the dimension here). The `variable/include/omit/section` lines differ only by `variable {L}` to `variable {d L}` and three file-header lines. So every public statement is RBM2D's after the renaming: no hypothesis added, no signature changed, nothing weakened.
4. Targets (b5, b7): everything the ticket and Amend 1 name is present and public; the objects their statements mention are public `KL` defs (`KLNIn KLNOut KLLIn KLLOut KLEIn KLEOut KLinLeafPar KLoutLeafPar KLinChild KLinPar KLoutChild KLoutPar KLcutIn KLcutOut KLshiftIn KLshiftOut KLcol KLunShift KLunCol KLunColP`). `edgeEquiv`, `sum_perm4`, `sum_perm4'` and 26 other helpers are private (29 private declarations). `KLtreeValW_eq_gval` is `rfl` against the merged `KLtreeValW`.
5. Instances (b7), at d = 3, L = 3: each of the 14 theorem targets is applied once in `section Instances` (named theorems `KLCutInst_*`; CLAUDE.md §4 step 2 allows a named check). Pinned: `KLCutInst_sum_cut` (n = 5, J = (1,3), f = fun _ _ => 1) with `KLCutInst_sum_cut_count` (#{F in T_SP(5) : J in F} = 3 and |T_SP(4)|·|T_SP(3)| = 3), and `KLCutInst_treeValW_cut` (Amend 1 point 2: n = 4, F = {(0,2)}, J = (0,2); leaf and edge weights are those of `KLtreeValG` at g = 1/2, E = 0, t = 9/10, charges (+,-,+,-); the cut edge carries Θ S^(B) Θ). Every hypothesis is discharged (`decide`, `norm_num`, `KLisTSP_of_mem_TSP`); no other gate's pin occurs.
6. Deviation D1 from ticket item 2: 22 public names go beyond the ticket's list, Amend 1's list and the objects mentioned by their statements (last block of b6; `KLprod_update_eq`, `KLhasDerivAt_treeValW`, `KLgval_in_eq`, `KLgval_out_eq`, `KLOutEnds` and 17 helper lemmas). Reason: RBM2D's code after the cut machinery in `TreeRep.lean`, `KBoundCut.lean`, `SumZeroWard.lean` mentions each of them (codes T/K/S in b6), and the design report T2004 row KL2 says "private copies: KBoundCut.lean:78-1521, SumZeroWard.lean:44-936" and "public once". They are `KL`-prefixed, clash-free (b4) and carry RBM2D's statements (b6). Visibility only: to follow item 2 literally add `private` to these 22; KL3/KL7/KL11 would then re-port them privately.
7. Hygiene (b1, b3): all 100 non-internal constants (the 92 declared public names plus 8 compiler-generated `*.congr_simp` lemmas; 64 theorems, 36 definitions) depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`admit`/`axiom`/`native_decide`; no public statement or definition body mentions a private constant.
8. Builds (b2): the module builds without a warning after its cache files were removed (16 s). With `import RBM3D.Loop.KLCut` added to `RBM3D.lean` temporarily (the root does not import it on the branch; the hub adds it at merge), the full `lake build` with the root `#assert_rbm_axioms` passes (795 theorems, 322 definitions, 0 axioms). The only warning of that build is in `RBM3D/Propagator/LaplaceGauss.lean:36`.
9. RBM2D `HEAD` is `9e0f275`; its diff to `c9a24cf` has no hunk inside lines 415-1667 of the old file (b8).
10. Sections (a) and (a″) were not edited.

## (c) Verified Mathlib names used (each resolved in Lean by `$SP/resolve.lean`, `$SP/fieldnames.lean`; names verified absent: none)
Equiv: arrowCongr_apply ofBijective ofBijective_apply refl sumArrowEquivProdArrow sumArrowEquivProdArrow_symm_apply_inl sumArrowEquivProdArrow_symm_apply_inr sumComm sumCompl
    sumCompl_symm_apply_of_neg sumCompl_symm_apply_of_pos swap
Finset: card filter image mem_filter mem_image mem_image_of_mem mem_insert mem_insert_of_mem mem_insert_self mem_product mem_singleton mem_union mem_union_left mem_union_right mem_univ
    mul_prod_erase mul_sum ne_of_mem_erase prod_congr sum_add_distrib sum_comm sum_congr sum_const sum_mul sum_nbij' sum_product'
Fintype: prod_congr prod_option prod_sum_type sum_congr sum_prod_type
Function: update update_of_ne update_self
HasDerivAt: fun_finsetProd fun_sum
Matrix: mul_apply transpose_apply
NeZero: pos
_root_: le_of_lt le_refl lt_of_lt_of_le mul_one not_le not_lt nsmul_eq_mul smul_eq_mul
Field-notation uses, all OK in `fieldnames.lean`: Equiv.sum_comp Equiv.prod_comp Equiv.arrowCongr Equiv.trans Equiv.symm HasDerivAt.congr_deriv HasDerivAt.mul HasDerivAt.mul_const Complex.ofRealCLM ContinuousLinearMap.hasDerivAt Finset.erase Finset.univ Matrix.transpose.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2014a` unused). The file restates no statement of the paper: it is a port of tree/laminar combinatorics and one algebraic splitting identity, with RBM2D's statements after the renaming (b6).
- D1 (dispatcher/auditor decision, narrative 6): 22 extra public helpers beyond ticket item 2; affects visibility only.
- For KL3: `KLhasDerivAt_treeValW` (RBM2D `TreeRep.lean:555`, "one term per edge") lies in this ticket's source range and is ported here, public, with `KLprod_update_eq`; a KL3 ticket should not port it again. `sum_perm4'` is private here (Amend 1) but RBM2D uses it at `TreeRep.lean:1981` (`git show c9a24cf:RBM2D/Loop/TreeRep.lean | awk 'NR>1667 && /sum_perm4/'` prints only that line): KL3 re-ports it privately.
- Ticket text: it places `sum_cut` (`TreeRep.lean:1643`) in "the cut part of `Assembly`"; at `c9a24cf` it lies in `section CutBij` (1265-1667) and `section Assembly` starts at 1669. The range 415-1667 contains everything the ticket and Amend 1 name.
