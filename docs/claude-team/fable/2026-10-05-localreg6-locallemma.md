Fable model: claude-fable-5-1

# lem:localregular property (6): the local lemma is PROVED after changing the cost (2026-10-05)

Follow-up to `docs/claude-team/fable/2026-10-04-localreg6.md` (cited "R1 §n").  Companions in this directory:
`2026-10-05-locallemma-enum.py` (abstract enumeration, 17 terms), `2026-10-05-locallemma-prims.py` (primitive moves,
decomposition, case tables), `2026-10-05-locallemma-check.py` (concrete checks on the LocStep model
`2026-10-04-localreg6-model.py`), `2026-10-05-localreg6-locallemma-output.txt` (every run, verbatim),
`2026-10-05-localreg6-locallemma-tables.txt` (the 992 case rows).  Nothing on the device was changed.

## 0. Verdict

* **Proved (hand proof, finite, every case checkable; §2-§5).**  Replace the chain cost of R1 by the *local* cost
  `c(G) := ord(G) + #elem(G)`, `#elem` = number of internal vertices whose half-edge multiset is `{c-in, c-out}` for one
  colour `c` (a lone light-weight or an SC vertex; no chains, no cycle/closure bonuses).  With
  `Φ(Q) := min over partitions π of V(Q) of c(M_π Q)` (`M_π`: merge the classes, keep circled loops, drop the other
  in-class edges; `Φ^far`: `x, y` in different classes), **the step lemma `Φ(Q') ≥ Φ(Q)` holds for every `LocStep`
  output `Q'`**, `Φ^far(Γ_p) = 3p`, `Φ^all(Γ_p) = 2p`, and `Φ ≤ ord` at a locally standard graph.  Hence
  `ord ≥ 2p` for **every** locally standard output and `ord ≥ 3p` for those with `M_x ≠ M_y` (hence the paper's (6)
  without the `(scalemole)` error term of DECISIONS §47; remark `B:280-283` is confirmed).
* **Why it closes.**  R1's `rescost` (chains, `−2` per cycle, `−1` per closure) was an attempt to predict what the
  min over merges does; with `c` purely local, the closures are *exactly* the merges (an SC chain closing on `e` is
  "merge its vertices into `e`"), so they are absorbed by the min and nothing has to be predicted.  The price is that
  the restriction `π|V(Q)` is not always the right partition of `Q`: in **exactly one shape**, the *2-cycle
  collapse* (the step removes the two edges `U → Z → U` of one colour, adds nothing but one waved edge; e.g. `R2` with
  `y = y'`, `P4` with `s = v`, and the merged images of these shapes inside `D`, `R7`), the right partition merges `U` and `Z`
  (§4.4).  No other repair is ever needed; a 3-cycle collapse (`R8`) is two of them.
* **Structure of the proof (§3).**  The 17 terms are compositions of **7 primitive moves** (`Loop`, `AddLoop`,
  `MoveLoop`, `MoveSC`, `MoveOut`, `Dmove`, `Contract`), each with ≤ 4 named vertices and ≤ 1 new vertex; the local
  lemma composes, so it is proved for the 7 primitives only.  For a primitive with a new vertex `α`, the *placement
  lemma* (§4.3) reduces every partition in which `α` shares a class to the one with `α` alone, except when both
  neighbours of `α` are in its class (`k = 2`); so each primitive needs one table for `α` alone and one for `k = 2`
  (§4.5): 15 + 15 rows for `Dmove`, ≤ 5 for the others.  Each row is a one-line computation of
  `Δord` and of the half-edge patterns of ≤ 4 classes.
* **Numerics (§6).**  Abstract enumeration: all 229,164 configurations of the 17 terms (24,835 with all classes
  internal; 52 resp. 13 with `Δc < 0`) and all 985 of the 7 primitives (3 with `Δc < 0`): every negative one is a
  `k`-cycle collapse, and the repair is verified over all residual patterns.  Concrete: 3.6 M `(Q, π₀, T, placement)` instances on reachable
  graphs (`p = 2, 3, 4`), 0 failures; `Φ` brute-forced over all partitions on 1,240 reachable states and 7,077
  children: 0 decreases; `Φ` is non-decreasing on R1's path where `Ψ` dropped.
* **Recommendation.**  LW-10c states (6) as `LocReg6 : 2p ≤ ord` for every output and adds the far corollary
  `3p ≤ ord`; invariant = the universal form of `Φ` (§7); 4 tickets, ~5,000 lines, no research risk left (the risk
  is the list/`Setoid` bookkeeping of §7 R1).

## 1. Definitions

Graph `G`: vertices `V` with external set `X ⊆ V` (`x`, `y`; after a merge of `x` with `y` one external vertex),
solid edges `(colour, circled, src, dst)`, waved edges (loops allowed; `n_W` counts them all).  All loops are
circled (`Normal` (iii); true for every graph below) and every circled edge is a loop (true for `Γ_p` and preserved:
new circled edges are loops, `lvl1Split.circ` circles loops only).

* **Half-edge pattern** `H(v) ∈ ℕ⁴ = (bi, bo, ri, ro)`: for a non-loop edge of colour `c` one `c-out` at `src`,
  one `c-in` at `dst`; a loop of colour `c` at `v` gives `c-in` and `c-out` at `v`.  **(E5)** In this encoding a loop
  of colour `c` and a pair `{c-in, c-out}` of non-loop edges are the same; this is why "`L → SC`" costs nothing.
* `elem(H) :⇔ H ∈ {(1,1,0,0), (0,0,1,1)}`; `#elem(G) := #{v ∈ V∖X : elem(H(v))}`.
* `c(G) := ord(G) + #elem(G) = n_S + 2(n_W − n_V) + #elem`, `n_V = |V∖X|`.
* For a partition `π` (equivalently a setoid `s`) of `V`: `M_π G` has the classes as vertices (a class is external
  iff it contains an external vertex), the solid edges `e` that are *kept* (`e.circ ∨ ¬ s(src, dst)`), all waved
  edges.  **Setoid cost** `c_s(G) := c(M_π G) = #kept + 2 n_W − 2·#(internal classes) + #(internal classes `K` with
  `elem(H_s(K))`)`, `H_s(K) = Σ` of the half-edges of kept edges at members of `K`.  (For Lean this formula needs no
  merged `LGraph`, §7.)
* `Φ^all(Q) := min_s c_s(Q)`; `Φ^far(Q) := min_{s : ¬ s(x,y)} c_s(Q)`.  `Φ ≤ c(Q)` (trivial partition).  Relation to
  R1: `c = Ψ + #cyc1 + 2#cyc ≥ Ψ`, so `Φ ≥ Ψ_min`; the R1 numbers `Ψ_min^far(Γ_p) = 3p`, `Ψ_min^all(Γ_p) = 2p` are
  lower bounds for `Φ(Γ_p)`, attained (§5).

## 2. Reduction of the step lemma to the local lemma [proved]

**Lemma A (adding a circled loop at a class never lowers `c_s`).**  `Δc_s = +1 + Δelem(K) ≥ 0` since `Δelem ≥ −1`
(`0` for an external class).  Equivalently dropping a loop never raises `c_s`.

**Lemma B (pullback).**  Let `Q' ∈ outs` of a `LocStep` at `Q`, `T` the unmerged term and `vm : V(T) → V(Q')` the
vertex map of `lvl1_part_struct` (`LWLvl1:248`): `Q'.solid` = the images of the kept edges of `T` under `vm`
(`lvl1Split.keep`), plus some in-class uncircled edges of `T` turned into circled loops (`lvl1Split.circ`); the others
dropped; `Q'.waved = vm(T.waved)`; externals go to externals.  For a setoid `s` on `V(Q')` let `s' := s ∘ vm` on
`V(T)`.  Then an edge of `T` is kept under `s'` iff its image is an edge of `Q'` kept under `s` (a circled loop stays a
circled loop; a non-loop with `vm src ≠ vm dst` is kept iff `¬ s`; an in-class uncircled edge is dropped under `s'`
and is either absent in `Q'` or one of the extra circled loops), the internal classes of `s` and `s'` correspond
(`vm` onto, externals to externals), `n_W` agrees, and the patterns agree up to the extra loops.  Hence by Lemma A
`c_s(Q') ≥ c_{s'}(T)`, and `¬ s(x', y') ⇒ ¬ s'(x, y)`.

**Local lemma (LL) for a term `T` of `Q`.**  For every setoid `s'` on `V(T)` there is a setoid `s₀` on `V(Q)`, equal
to the restriction `s'|V(Q)` (`s'.comap emb`) or to a coarsening of it by merges of two classes of which at most one
is external (one merge for a primitive, at most two for a composite term), such that `c_{s₀}(Q) ≤ c_{s'}(T)` and
`¬ s'(x, y) ⇒ ¬ s₀(x, y)`.

**Step lemma.**  `LL` + Lemma B give `Φ(Q') ≥ Φ(Q)` for both versions: for the far version, a far `s` on `Q'` pulls
back to a far `s'` and `LL` returns a far `s₀`; no hypothesis "`Q` far" is used (if `x = y` in `Q'` the far
statement for `Q'` is vacuous).  Twists `(c, t)` (global colour flip, global transpose) and the frame leave `c_s`
invariant (`elem` is symmetric in `b ↔ r` and `in ↔ out`), so `LL` may be proved in the frame.

## 3. The 7 primitive moves and the decomposition of the 17 terms [verified symbolically]

A move takes a graph `G` and vertex arguments in `V(G)` (the Lean constructors already take arbitrary arguments; in
the proof `G` is arbitrary — it is `M_{π₀} Q` — so *every coincidence* of the arguments is allowed, the removed
edges are present or not according to the coincidence, see §4.1).  Blue = colour of the expanded loop/edge in the frame.

| move | removed | added | waved / new |
|---|---|---|---|
| `Loop(z)` | — | light-weight at fresh `α` | `z–α`, `α` |
| `AddLoop(z, col)` | — | light-weight at `z` | — |
| `MoveLoop(z)` | the blue light-weight of `z` | blue light-weight at fresh `α` | `z–α`, `α` |
| `MoveSC(z; u, v)` | `u → z`, `z → v` (blue) | `u → α`, `α → v` | `z–α`, `α` |
| `MoveOut(z; v, d)` | `z → v` (blue), `z → d` (red) | `α → v` (blue), `α → d` (red) | `z–α`, `α` |
| `Dmove(z; p, q)` | `p = (z → v, blue)` or the blue light-weight of `z` (then `v := z`), and `q = (a → b, col)` (an edge or a light-weight, `a = b`) | `DE(α, z, q)` and `α → v` (blue); blue `q`: `a → α, z → b`; red `q`: `a → z, α → b` | `z–α`, `α` |
| `Contract(z; u, v)` | `u → z`, `z → v` (blue) | `u → v` | `z–v`, none |

Decomposition (`prims.py check_decompositions`, equality of the final edge multisets, waved count and new vertices,
after cancelling an edge removed and re-added — `R7` drops and re-adds `G_{y'x}`; the end of a waved edge is
irrelevant for `c`):
`T1 = Loop(w)`; `T2 = MoveLoop(w) ∘ Loop(α)`; `T3 = Dmove(w; lw_w, q)`; `T4 = MoveLoop(w) ∘ Dmove(α; lw_α, q)`;
`Oe1xOwx = Loop(x)`; `D = Dmove(x; x→v, q)`; `P3 = MoveOut(x; v, d)`; `P5 = MoveOut ∘ AddLoop(x, red)`;
`P4 = MoveSC(x; s, v)`; `P6 = MoveSC ∘ AddLoop(x, blue)`; `R2 = Contract(x; y', y)`; `R3 = Loop(x)`;
`R4 = MoveSC(x; y', y) ∘ Loop(α)`; `R5 = MoveSC ∘ AddLoop(x, blue)`; `R6 = Loop(x) ∘ MoveSC(x; y', y)`;
`R7 = Dmove(x; x→y, q')`; `R8 = MoveSC(x; y', y) ∘ Dmove(α; α→y, q')`.

**Composition lemma.**  If `LL` holds for `τ₁ : Q → T₁` and for `τ₂ : T₁ → T` then it holds for `T`: given `s` on
`V(T)` take `s₁` for `τ₂`, then `s₀` for `τ₁`; "restriction or one merge" composes to "restriction coarsened by ≤ 2
merges" (the far clause composes).  The intermediate graphs `T₁` (outputs of `MoveLoop`, `MoveSC`, `Loop`) have only
circled loops, so the hypotheses of §1 hold for the second move.  So `LL` for the 17 terms follows from `LL` for the
7 primitives on an arbitrary graph.  (In `Dmove` the added edge `z → b` resp. `a → z` may be an uncircled loop of
`T` when `b = z` resp. `a = z` in `Q` — the weight `G_{ww}` of `T3`; it is in-class under every `s'`, hence dropped
in `c_{s'}(T)`, which is the worst case by Lemma A.)

## 4. The local lemma for a primitive [proved]

### 4.1 The surgery identity
Let the primitive remove the list `R` and add the list `A` of edges, add `n_w` waved edges and the fresh vertex `α`
(none for `Contract`, `AddLoop`).  For `s'` on `V(T)` and `s₀ := s'|V(Q)`, with "kept" meaning circled-loop or
ends in different classes (an uncircled loop is never kept):
```
c_{s'}(T) − c_{s₀}(Q) = Δord + Σ_K Δelem(K),
Δord = #kept(A) − #kept(R) + 2 n_w − 2·[α is alone in its class],
Δelem(K) = [K internal]·( elem(H₀(K) − R_K + A_K) − elem(H₀(K)) ),
```
summed over the classes `K` of `s'` meeting the arguments or `α`; `R_K`, `A_K` are the half-edges at members of `K`
of the kept removed/added edges; `H₀(K)` the pattern in `M_{s₀} Q` (for a fresh class `H₀ = 0`, `R = 0`).  All other
classes are unchanged.  (Proof: both sides are `List.countP` sums over `T.solid = (Q.solid − R) ++ A`.)

### 4.2 Pattern facts (`H ∈ ℕ⁴`, `R ⊆ H`, `A` multisets of half-edges)
(E0) `Δ := elem(H − R + A) − elem(H) ∈ {−1, 0, 1}`; `Δ = −1 ⇒ elem(H)`.  (E1) `R = ∅`: `Δ = [elem(H + A)] − [elem H]`,
and `elem(H + A) ⇒ |H| = 2 − |A|`; for `|A| = 2`: `Δ = [H = 0]·[elem A] − [elem H]`.  (E2) `A = ∅`: `Δ = [elem(H − R)]
− [elem H]`.  (E3) `R = A` (as multisets): `Δ = 0`.  (E4) `H ⊇ {b-out, r-out}` or `⊇ {b-in, r-in}` or `⊇ {b-·, r-·}`
with two colours present: `¬ elem H`.  (E5) a loop of colour `c` = the pair `{c-in, c-out}`.  (E6) if `A` has two half-edges
of different colours, or of the same direction, `elem(H + A) = 0`.  "Residual" `X := H₀(K) − R_K` (anything in `ℕ⁴`);
the minimum of `Δelem(K)` over `X` depends only on `(R_K, A_K)` and is `≤ 0`, so an **external class (`Δelem = 0`)
is never worse than an internal one**; the tables below are for internal classes.

### 4.3 Placement lemma (reduces "α in a class" to "α alone")
Let `s'` put `α` into a class `C` with old vertices, and `s''` be `s'` with `α` split off.  In `M_{s''} T` the
vertex `α` is internal with exactly one circled loop (`Loop`, `MoveLoop`) or exactly two non-loop edges to
`f₁, f₂` (`MoveSC`: `u, v`; `MoveOut`: `v, d`; `Dmove` blue: `a, v`; red: `b, v`), pattern `A_α`, `|A_α| = 2`.
Let `k := #{i : [f_i] = C}` (0 for a loop).  Merging `α` into `C` drops the `k` edges `α–C`, loses one internal
vertex, so
```
c_{s'}(T) − c_{s''}(T) = 2 − k − elem(A_α) + [C internal]·( elem(H_C − h̄ + A_α − h) − elem(H_C) ),
```
where `h, h̄` are the half-edges of the dropped edges at `α` resp. at `C`.  **If `k ≤ 1` this is `≥ 0`**:
`k = 0`: `≥ 2 − 1 − 1`; `k = 1` and `A_α` an SC pair: the class pattern is unchanged (`h̄ = ` the other half of
`A_α`, E5), value `1 − 1 + 0 = 0`; `k = 1` and `A_α` not an SC pair (`{b-out, r-out}`, `{r-out, b-out}`, `{r-in,
b-out}` …): `≥ 1 − 0 − 1 = 0`; `C` external: `≥ 2 − k − 1 ≥ 0`.  So for `k ≤ 1`, `LL` for `s'` follows from `LL`
for `s''` (same restriction `s₀`).  **`k = 2`** is treated directly (§4.5); it means both edges of `α` are dropped.
(Checked on 51,769 concrete `k ≤ 1` instances, 0 violations.)

### 4.4 Repair lemma (2-cycle collapse)
Suppose the net effect on `M_{s₀} Q` is: remove two kept edges `U → Z`, `Z → U` of one colour (`U ≠ Z`), add no
solid edge, add one waved edge.  Write `X_U, X_Z` for the residual patterns.  Then `Δc = [elem X_U] − [X_U = 0] +
[elem X_Z] − [X_Z = 0]` (internal classes only; `Δord = 0`).  If `Δc < 0` some internal class, say `Z`, has `X_Z = 0`
(it was an SC vertex of the 2-cycle), hence no other edge at `Z`; let `s₀' := s₀ ⊔ (U ~ Z)`.  Merging drops the two
cycle edges and the vertex `Z`: `c_{s₀'}(Q) − c_{s₀}(Q) = −2 + 2 − 1 − [U internal]·([elem(X_U + cyc)] −
[elem X_U]) = −1 − [X_U = 0] + [elem X_U] = Δc`, so `c_{s₀'}(Q) = c_{s'}(T)`.  If `U, Z` are both external, `Δc = 0`
and no repair is needed; so the repair never merges two externals (far clause).  (A 3-cycle collapse, `R8` with
`[y] = [a]`, `[y'] = [b]`, `α → [y']`, `β → [y]`, is `MoveSC` followed by a 2-cycle collapse of `Dmove`; the
composition lemma handles it with two merges, verified directly as well, §6.)

### 4.5 The case tables (`α` alone, then `k = 2`; `[e]` = "`e` kept"; exhaustive, each row ≤ 2 lines)
Notation: a removed edge of `Q` between arguments in the same class is absent in `M_{s₀} Q` ("dropped"); a light-weight
argument (`p = lw_z`, `q = lw_a`) is a kept loop whatever the classes.  `X` = residual pattern of the named class.

**Loop(z).** `α` alone: `Δord = +1`, `α` elementary: `Δc = +2`.  `α` in `C` (§4.3 covers it; directly: `Δord = +3`,
`Δelem(C) ≥ −1`): `Δc ≥ +2`.
**AddLoop(z).** `Δord = +1`, `Δelem(z) ≥ −1`: `Δc ≥ 0` (tight: `z` elementary).
**MoveLoop(z).** `α` alone: `Δord = 0`; `Δelem(z) = elem(X) − [X = 0]`; `α` elementary `+1`: `Δc ≥ 0` (tight: `z` a
lone light-weight).  `α ∈ [z]`: edge set unchanged, `Δc = +2`.
**Contract(z; u, v)** (no new vertex; `Δord = [u→v] − [u→z] − [z→v] + 2`):
(a) `[u], [v], [z]` distinct: `Δord = 1`; `z` loses `{b-in, b-out}`: `Δelem(z) = elem(X) − [X = 0] ≥ −1`; `u, v`
unchanged (E3): `Δc ≥ 0`.  (b) `[u] = [v] ≠ [z]`: `Δord = 0`, `z` and `U` each lose the pair: **collapse**, §4.4.
(c) `[u] = [z] ≠ [v]` or `[v] = [z] ≠ [u]`: one removed edge absent, the added edge equals the other removed one:
`Δc = +2`.  (d) all equal: `Δc = +2`.
**MoveSC(z; u, v)**, `α` alone (`[u→α]`, `[α→v]` kept): (a) `[u] ≠ [z] ≠ [v]`: `Δord = 0`, `z`: `elem(X) − [X=0]`,
`u, v` unchanged (E3), `α`: `+1`: `Δc ≥ 0` (tight: `z` SC).  (b) `[u] = [z] ≠ [v]` (or symmetric): `Δord = +1`;
`z` loses `b-out`, gains `b-out` (from `u → α`): unchanged; `α`: `+1`: `Δc = +2`.  (c) `[u] = [v] = [z]`: `Δord = +2`,
`z` gains a pair (`≥ −1`), `α +1`: `Δc ≥ +2`.  `k = 2` (`[u] = [v] =: U`, `α ∈ U`): `U ≠ [z]`: both added edges dropped,
`Δord = 0`, `z` and `U` lose a pair: **collapse**; `U = [z]`: nothing changes, `Δc = +2`.
**MoveOut(z; v, d)**, `α` alone: (a) `[v], [d] ≠ [z]`: `Δord = 0`; `z` loses `{b-out, r-out}`: never elementary before
(E4), so `Δelem(z) ≥ 0`; `α = {b-out, r-out}`: `0`; `v, d` unchanged: `Δc ≥ 0` (tight: generic `P3`).  (b) `[v] = [z] ≠
[d]`: `Δord = +1`; `z`: `−r-out + b-in`: `≥ −1`: `Δc ≥ 0` (symmetric for `[d] = [z]`).  (c) `[v] = [d] = [z]`: `Δord =
+2`, `z` gains `{b-in, r-in}`: `≥ −1`: `Δc ≥ +1`.  `k = 2` (`[v] = [d] = U ∋ α`): `U ≠ [z]`: `Δord = 0`, `z` loses
`{b-out, r-out}` (`≥ 0`), `U` loses `{b-in, r-in}` (`≥ 0`, E4): `Δc ≥ 0` — *no collapse* (two colours); `U = [z]`:
`Δc = +2`.
**Dmove(z; p, q), blue `q`**, `α` alone (`e₁ = a→α`, `e₃ = α→v` kept; `e₂ = z→b` kept iff `[z] ≠ [b]`;
`Δord = 2 + [e₂] − [p] − [q]`; `α` is an SC vertex, `+1`; pairs: `z: (p, e₂)`, `v: (p, e₃)`, `a: (q, e₁)`, `b:
(q, e₂)` — each named vertex loses a half-edge by its removed edge and regains the same type by its added edge, so a
class is changed only through dropped/absent edges).  The 15 partitions of `{z, v, a, b}` (`[p]`, `[q]` are `1`
unless `v ~ z` resp. `a ~ b`, where they are `1` for a light-weight and `0` for an edge; `Δc_min` = the table value):
```
 {z}{v}{a}{b}: Δord 1, no class changes                              → +2
 {z,v}{a}{b}:  Δord 2−[p]; [z]: (−loop)+{b-out,b-in}: Δelem = 0 (lw, E5) or ≥ −1 (edge) → +2
 {z,a}{v}{b}:  Δord 1; [z]: −b-out−b-out+b-out+b-out                 → +2
 {z,b}{v}{a}:  e₂ dropped, Δord 0; [z] loses {b-out,b-in}: elem(X)−[X=0]  → ≥ 0 (tight)
 {v,a}{z}{b}:  Δord 1; [v]: −b-in−b-out+b-out+b-in                   → +2
 {v,b}{z}{a}:  Δord 1; [v]: −b-in−b-in+b-in+b-in                     → +2
 {a,b}{z}{v}:  Δord 2−[q]; [a]: (−loop)+{b-out,b-in}                 → +2
 {z,v}{a,b}:   Δord 3−[p]−[q]; [z], [a] each (−loop)+pair            → ≥ 2
 {z,a}{v,b}:   Δord 1; [z], [v] unchanged                            → +2
 {z,b}{v,a}:   e₂ dropped, Δord 0; [z] loses the pair; [v] unchanged → ≥ 0 (tight)
 {z,v,a}{b}:   Δord 2−[p]; [z]: (−loop)−b-out+b-out+b-out+b-in       → +2
 {z,v,b}{a}:   e₂ dropped, Δord 1−[p]; [z]: (−loop)−b-in+b-in        → ≥ 0 (lw tight), +2 (edge)
 {z,a,b}{v}:   e₂ dropped, Δord 1−[q]; [z]: −b-out(−loop)+b-out      → ≥ 0 (lw tight), +2 (edge)
 {v,a,b}{z}:   Δord 2−[q]; [v]: −b-in(−loop)+b-out+b-in+b-in         → +2
 {z,v,a,b}:    e₂ dropped, Δord 2−[p]−[q]; [z]: (−loops)+pair        → ≥ 1 (two lw), +2
```
`k = 2` (`[a] = [v] =: U ∋ α`; `e₁, e₃` dropped; net: remove `p` (`Z → U`), `q` (`U → B`), add `e₂` (`Z → B`), `Z :=
[z]`, `B := [b]`): `Z, U, B` distinct: `Δord 1`, `Z`, `B` unchanged, `U` loses a pair: `≥ 0`.  `Z = B ≠ U`: `e₂`
dropped, `Δord 0`, `Z` and `U` lose a pair: **collapse** (the one of `D`/`T3`/`R7`).  `Z = U ≠ B`: `Δord = 2 − [p] ≥
1`, `U`: `(−loop) − b-out + b-out ≥ −1`: `≥ 0`.  `B = U ≠ Z`: `Δord = 2 − [q] ≥ 1`, `U`: `−b-in (−loop) + b-in ≥
−1`: `≥ 0`.  `Z = U = B`: `Δord = 2 − [p] − [q]`, `U` loses `[p] + [q]` loops: `≥ 0`.
**Dmove, red `q`** (`e₁ = a→z` kept iff `[a] ≠ [z]`; `e₂ = α→b`, `e₃ = α→v` kept when `α` alone; `α = {r-out,
b-out}`: `0`; `Δord = 2 + [e₁] − [p] − [q]`; pairs `v: (p, e₃)`, `a: (q, e₁)`, `b: (q, e₂)` preserve types, but
`z` changes type: `−b-out (p) + r-in (e₁)`):
```
 {z}{v}{a}{b}: Δord 1; z: −b-out+r-in ≥ −1                           → ≥ 0 (tight: z blue SC)
 {z,v}:        Δord 2−[p]; [z]: (−loop)+{r-in,b-in}: −[X=0] (lw) / ≥ −1 → ≥ 0 / ≥ 1
 {z,a}:        e₁ dropped, Δord 0; [z]: −b-out−r-out: never elem before (E4) → ≥ 0
 {z,b}:        Δord 1; [z]: −b-out−r-in+r-in+r-in ≥ −1               → ≥ 0
 {v,a}, {v,b}: Δord 1; [v] unchanged; z ≥ −1                         → ≥ 0
 {a,b}:        Δord 2−[q]; [a]: (−loop_r)+{r-out,r-in}: 0 (lw) / ≥ −1; z ≥ −1 → ≥ 0
 {z,v}{a,b}:   Δord 3−[p]−[q]; [z]: (−loop)+{r-in,b-in}; [a]: (−loop_r)+{r-in,r-out} → ≥ 1−[p] ≥ 0
 {z,a}{v,b}:   e₁ dropped, Δord 0; [z]: −b-out−r-out ≥ 0; [v] unchanged → ≥ 0
 {z,b}{v,a}:   Δord 1; [z]: −b-out+r-in ≥ −1; [v] unchanged          → ≥ 0
 {z,v,a}{b}:   e₁ dropped, Δord 1−[p]; [z]: (−loop)−r-out+b-in: ≥ 0 (lw) / ≥ −1 (edge) → ≥ 0
 {z,v,b}{a}:   Δord 2−[p]; [z]: (−loop)+{r-in,b-in}                  → ≥ 0
 {z,a,b}{v}:   e₁ dropped, Δord 1−[q]; [z]: −b-out(−loop_r)+r-in: ≥ 0 (lw) / ≥ −1 → ≥ 0
 {v,a,b}{z}:   Δord 2−[q]; [v]: (−loop_r)+{r-in,r-out}: 0 / ≥ −1; z ≥ −1 → ≥ 0
 {z,v,a,b}:    e₁ dropped, Δord 2−[p]−[q]; [z]: (−loops)+{r-in,b-in}: ≥ 0 (two lw, E4) / ≥ −1 → ≥ 0
```
`k = 2` (`[b] = [v] =: U ∋ α`; net: remove `p` (`Z → U`, blue), `q` (`A → U`, red), add `e₁` (`A → Z`, red)):
`A, Z, U` distinct: `Δord 1`; `Z: −b-out + r-in ≥ −1`; `A` unchanged; `U` loses `{b-in, r-in}`: `≥ 0` (E4): `≥ 0`.
`A = Z ≠ U`: `e₁` dropped, `Δord 0`; `Z` loses `{b-out, r-out}` and `U` loses `{b-in, r-in}`: both `≥ 0` (E4), **no
collapse** (two colours).  `Z = U ≠ A`: `Δord = 2 − [p] ≥ 1`; `U: (−loop) − r-in + r-in ≥ −1`: `≥ 0`.  `A = U ≠ Z`:
`Δord = 2 − [q] ≥ 1`; `U: −b-in (−loop_r) + r-out`: `≥ 0` if lw (before ≥ 3 half-edges), `≥ −1` if edge (then
`Δord = 2`); `Z ≥ −1`: `≥ 0`.  All equal: `Δord = 2 − [p] − [q]`, `U` loses `[p] + [q]` loops: `≥ 0`.

Every row above is reproduced by `prims.py --tables` (the companion `-tables.txt`, 992 rows including the `α ∈ C`
rows that §4.3 makes redundant): every hand bound is attained or exceeded by the table minimum, and the only negative
rows are the three collapses.

**Conclusion of §4.**  For each primitive and each `s'`: if `α` shares a class with `k ≤ 1`, §4.3; otherwise the row of
the table gives `Δc ≥ 0` (`s₀ = s'|V(Q)`) or a 2-cycle collapse, where §4.4 gives `s₀ = s'|V(Q) ⊔ (U ~ Z)`.  With
§3, `LL` holds for the 17 terms. ∎

## 5. Initial values and the final step [proved]

**`Γ_p` (`fxyPowGraph p`).**  Vertices `x, y, α_i, β_i`; edges `x → α_i`, `α_i → y` (colour `c_i`), light-weight at
`β_i`; waved `α_i – β_i`.  For a setoid `s`: let `A_ext`, `B_ext` be the numbers of `α_i`, `β_i` in external classes,
`m` the number of internal classes, `σ` the number of singleton internal classes, `d` the number of dropped edges.
`n_S = 3p − d`, `n_W = p`, so `c_s = 5p − d − 2m + #elem`.  A singleton `{α_i}` (both edges kept: its ends are in
external classes) is an SC vertex and a singleton `{β_i}` a lone light-weight: `#elem ≥ σ`.  The other internal
classes have ≥ 2 members, so `2(m − σ) ≤ 2p − A_ext − B_ext − σ`.  Hence `c_s ≥ 3p − d + A_ext + B_ext`.  If
`¬ s(x, y)`: `d ≤ A_ext` (each `α_i` loses at most one edge), so `c_s ≥ 3p`.  In general `d ≤ 2 A_ext ≤ A_ext + p`,
so `c_s ≥ 2p`.  Both are attained (trivial partition; `{x, y, all α_i}`), brute force `p ≤ 3` (§6).

**Final step.**  `Q` locally standard: no loops, every internal vertex standard neutral (one blue, one red edge: not
elementary by E4) or isolated: `c(Q) = ord(Q)`.  With the trivial setoid, `Φ^all(Q) ≤ ord(Q)`; if `x ≠ y` as
vertices (in particular if `M_x ≠ M_y`), also `Φ^far(Q) ≤ ord(Q)`.

**Theorem.**  Along `Lvl1Reach` from `Γ_p`: `Φ^all ≥ 2p` and, for every setoid separating `x, y`, `c_s ≥ 3p` (the
latter is vacuous once `x = y` as vertices, and needs no "parent far" lemma).  Hence `ord ≥ 2p` at every locally
standard output and `ord ≥ 3p` when `M_x ≠ M_y`. ∎  (Hypotheses on the states: normal and "circled ⇒ loop", both
invariant; `hbad`, `hnb`, the cutoff and `¬ LocStd` are not used.)

## 6. Numerical cross-checks (`2026-10-05-localreg6-locallemma-output.txt`, verbatim excerpts)
```
[gg/R7] configs 22752 ... naive failures: 39; failing shapes: {('2-cycle', -2): 5, ('2-cycle', -1): 34}
[gg/R8] configs 194556 ... naive failures: 4; failing shapes: {('3-cycle', -2): 1, ('3-cycle', -1): 3}
GRAND: {'configs': 229164, 'naive_fail': 52, 'other': 0}            (17 terms, every ext/int assignment)
GRAND: {'configs': 24835, 'naive_fail': 13, 'other': 0}             (17 terms, all classes internal)
2-cycle collapse repair: tested 26244 residual patterns (x ext flags); failing cases 319; >= 2 external classes among them: 0; repair fails: 0
3-cycle collapse repair: tested 4251528 ...; failing cases 478; >= 2 external classes among them: 0; repair fails: 0
all decompositions verified: True                                   (17 terms = compositions of the 7 primitives)
GRAND (primitives): {'configs': 985, 'fail': 3, 'other': 0}         (MoveSC, Dmove, Contract: one 2-cycle collapse each)
Gamma_1: ... Phi^far=3 (3p=3) Phi^all=2 (2p=2);  Gamma_2: Phi^far=6 Phi^all=4;  Gamma_3: Phi^far=9 Phi^all=6
lemma A for c: 609 loop removals on reachable states (p=2), c increased in 0
DONE premerge(c) p=2 seed=11 far: {('realizable','collapse2'): 238, ('realizable','collapse3'): 86, ('realizable','naive_fail'): 324, ('realizable','repaired'): 324, ('realizable','tests'): 220157, ('unrealizable','tests'): 1268851}
DONE premerge(c) p=2 seed=12 xy:  {... 'collapse2': 332, 'collapse3': 104, 'naive_fail': 436, 'repaired': 436, 'tests': 203827 / 1037353}
DONE premerge(c) p=3 far: {'collapse2': 26, 'collapse3': 4, 'naive_fail': 30, 'repaired': 30, 'tests': 52932 / 462592}
DONE premerge(c) p=4 xy:  {'collapse2': 20, 'collapse3': 8, 'naive_fail': 28, 'repaired': 28, 'tests': 30154 / 368286}
placement lemma: {('k', 0): 37309, ('k', 1): 14460, ('k', 2): 5610}   (no 'VIOLATION' key: 0 violations for k <= 1)
DONE phi p=2 ORDMAX=3: states 67, children checked {'far': 391, 'all': 670}, violations {}, min Phi {'far': 6, 'all': 4}
DONE phi p=2 ORDMAX=4: states 1173, children checked {'far': 1476, 'all': 4540}, violations {}, min Phi {'far': 6, 'all': 4}, min ord of loc. std. children {'all': 4, 'far': 6}
cexpath (R1 §2.3, Psi 65 -> 64): state 17: ord=62 Psi=65 c=65 Phi^far=63 Phi^all=61 ; child: ord=64 Psi=64 c=67 Phi^far=64 Phi^all=62  (non-decreasing)
```
The "premerge" rows test `LL` on real `(Q, π₀, T, placement)`: every naive failure is a collapse and is repaired by
merging the collapsed classes (`FAIL_NOT_COLLAPSE`, `FAIL_REPAIR` never occur).  The "phi" rows brute-force `Φ` over
all set partitions (`|V| ≤ 8`).  Soundness of the abstract enumeration: the configuration space is (set partition of
the named vertices) × (placement of each new vertex: alone, shared fresh class, a named class, an unnamed class) ×
(edge/light-weight variants) × (ext/int flags), and the per-class minimum over residual patterns truncated at 2
(`elem` only sees whether a count is 0, 1 or ≥ 2); each class's residual is independent (realised by edges to
far-away vertices), and residual edges *between* named classes matter only for the repair, where a failing
configuration forces a class with empty residual (§4.4), so they are absent.

## 7. Recommended pin shape for LW-10c and tickets

Statement forms (namespace `RBM.Graph`; `E = Fin 2`, `x = ext 0`, `y = ext 1`):
```lean
def LGraph.halfPat (Γ : LGraph E I) (v : E ⊕ I) : ℕ × ℕ × ℕ × ℕ      -- (b-in, b-out, r-in, r-out), loops count twice
def lwElem (h : ℕ × ℕ × ℕ × ℕ) : Bool := decide (h = (1,1,0,0) ∨ h = (0,0,1,1))
/-- cost of `Γ` merged along `s`: kept edges, waved edges, internal classes, elementary internal classes (§1) -/
def LGraph.scost (Γ : LGraph E I) (s : Setoid (E ⊕ I)) [DecidableRel s.r] : ℤ
theorem LGraph.scost_bot (hN : Γ.Normal) : Γ.scost ⊥ = ord Γ.counters + Γ.nElem
/-- the invariant: every merge separating `x, y` (if `far`) costs at least `k` -/
def PGraph.LocCostGe (far : Bool) (k : ℤ) (P : PGraph E) : Prop :=
  ∀ (s : Setoid (P.E' ⊕ P.I')) [DecidableRel s.r], (far = true → ¬ s.r (inl (P.ext 0)) (inl (P.ext 1))) → k ≤ P.g.scost s
theorem fxyPowGraph_locCostGe (p) : LocCostGe false (2p) ⟨fxyPowGraph p⟩ ∧ LocCostGe true (3p) ⟨fxyPowGraph p⟩
theorem locCostGe_locStep (hst : LocStep m P outs) (hQ : Q ∈ outs) (hN : P.g.Normal) (hc : ∀ e ∈ P.g.solid, e.circ → e.src = e.dst)
    (h : P.LocCostGe far k) : Q.LocCostGe far k
theorem locReg6_of_locCostGe (hQ : Q.LocStd) (h : Q.LocCostGe false k) : k ≤ ord Q.g.counters
theorem locReg6far_of_locCostGe (hQ : Q.LocStd) (hxy : Q.ext 0 ≠ Q.ext 1) (h : Q.LocCostGe true k) : k ≤ ord Q.g.counters
```
The local lemma, per primitive, in the form the step lemma consumes (here `Dmove`; `T` is the Lean term graph):
```lean
theorem scost_dmove (Γ : LGraph E I) (hN : loops circled, circled ⇒ loop) (z : E ⊕ I) (p q : SEdge _) (hp : p ∈ Γ.solid ...) (hq ...)
    (s : Setoid (E ⊕ (I ⊕ Fin 1))) [DecidableRel s.r] :
    ∃ s₀ : Setoid (E ⊕ I), (s₀ = s.comap (owxEmb 1) ∨ ∃ u v, (¬ ext u ∨ ¬ ext v) ∧ s₀ = s.comap (owxEmb 1) ⊔ eqv u v) ∧
      (¬ s.r (inl x) (inl y) → ¬ s₀.r (inl x) (inl y)) ∧ Γ.scost s₀ ≤ (dmoveGraph Γ z p q).scost s
```
Tickets (prover-max; each ≤ 1,500 lines):

| # | content | lines | risk |
|---|---|---|---|
| LW-10c-1 | `halfPat`, `lwElem`, `scost`, `LocCostGe`; `scost_bot`; Lemma A (`scost_cons_loop_ge`); Lemma B via `lvl1_part_struct` (`scost_partition_ge : Q.g.scost s ≥ T.scost (s.comap vm)`); `fxyPowGraph_locCostGe` (§5 counting over an arbitrary setoid); the two final lemmas | 1300 | medium: the §5 counting with `Quotient` classes |
| LW-10c-2 | the surgery identity §4.1 (`scost` of `(Γ.solid − R) ++ A` under `s` vs `s.comap`), the pattern facts §4.2 (`omega`/`decide` on `ℕ⁴`), placement lemma §4.3, repair lemma §4.4, composition lemma; primitives `Loop`, `AddLoop`, `MoveLoop`, `Contract` | 1400 | medium-high: the surgery identity is the technical core (`List.countP` over `Quotient`-valued keys) |
| LW-10c-3 | `MoveSC`, `MoveOut`, `Dmove` (tables §4.5: `by_cases` on the ≤ 6 class equalities, then `omega` with the pattern facts; the tables file is the spec) | 1300 | medium: size only |
| LW-10c-4 | the 17 decomposition lemmas (`List.Perm` of `solid`, equal `waved.length`, twists: `scost_twist`), `locCostGe_locStep` (mirror `pathInv2_locStep`), induction along `Lvl1Reach`, `LocReg6` (`2p ≤ ord`, all outputs) + far corollary, assembly `lw_localregular` with `lw_localregular_upto5` | 1200 | low-medium: plumbing |

Risks and notes.  (R1) `Setoid`/`Quotient` bookkeeping; alternative: `s` as a surjection `σ : V → Fin n` with an
explicit external predicate — same proofs.  (R2) `Dmove` has 15 + 15 rows (`α` alone) and 5 + 5 cases (`k = 2`), each with the `[p]`, `[q]` flags; keep
them as separate lemmas with the row name in the docstring.  (R3) the far corollary needs `M_x ≠ M_y → ext 0 ≠ ext 1`
only.  (R4) nothing of R1's chain machinery (`rescost`, `Ψ_min`, `Ψ₃`) is needed; R1 §7's targets 1 and 5 are
replaced by the above.  (R5) if the dispatcher wants a single statement for (6): `LocReg6 : 2p ≤ ord` for every
`Q ∈ outs` (the form `PGraph.LocReg6` already has), from `LocCostGe false (2p)`.

## 8. Differences from the paper / the previous report
The paper's `ord + n_dv + n_lw` (`B:200-278`) corresponds to the trivial-partition value `c(Q)` of this report (`n_dv +
n_lw` ↔ `#elem`); it is not monotone (R1 §2.3 and the collapses above), the minimum over merges is.  The paper's `3p −
n_dv/2 > 2p` is replaced by `Φ^far ≥ 3p`, `Φ^all ≥ 2p`.  R1 §4.3's lemma (for `Ψ_min`) is not proved and not needed;
R1 §4.1-4.2, §4.4 carry over with `c` in place of `Ψ` (Lemma A is simpler).  Model-vs-Lean caveats are those of
R1 §8; the analysis of §4 is for arbitrary graphs and arbitrary vertex arguments, so the Lean hypotheses of
`LocStep` (`hbad`, `hnb`, `hv`, `hy`) are not needed, only `Normal` and "circled ⇒ loop".
