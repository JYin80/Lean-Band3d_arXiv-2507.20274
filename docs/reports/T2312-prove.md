Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct  7 10:53:04 UTC 2026

Target: `lwMomExp_valOnD_eq_valOn` (RBM.Graph): for `Γ : NGraph p q`, `ξ : ι → ι → ℝ`, `a b : Fin p → ι`, `D : Finset ι`,
`lwMomExp_valOnD Γ ξ a b D = Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D))`.
Definitions read from the worktree (`/Users/junyin/Lean_proof/RBM3D-wt/T2312`, HEAD a88cf75):
- `lwMomExp_valOnD` (LWMomExp.lean:526) `= ∑ ℓ ∈ piFinset (fun _ => D), ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k`.
- `anpKey6_w` (AnpKey6.lean:664) `= if (Γ.es.get k).ghost then 1 else ξ (Sum.elim (Sum.elim a b) ℓ (Γ.es.get k).u) (… .v)`.
- `NGraph.valOn` (AnpKey2.lean:54) `= ∑ ℓ ∈ S, (Γ.es.map fun e => if e.ghost then 1 else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (… e.v)).prod`.
Mathematically the two sides agree termwise: both are `Σ_{ℓ ∈ D^q} Π_{edges e} (1 if ghost else ξ(lab ℓ e.u, lab ℓ e.v))`; the only difference is `List.prod` of a mapped list versus `Finset.prod` over `Fin es.length`, the same identity as in `anpKey6_val_eq` (AnpKey6.lean:669-674).

### (i) Exponent table

The target is an exact algebraic identity. It contains no exponent, threshold, window, `N`, `L`, `W`, `ℓ` or analytic constant.

| quantity | value | constraint | slack |
|---|---|---|---|
| analytic exponents / thresholds / constants | none | none | n/a |
| dimension `d`, `3 ≤ d` | does not occur (`ι` is an arbitrary type, `Type*`) | none | n/a |
| `p, q : ℕ` | arbitrary | none (`q = 0` is allowed by the statement; both sides then have the single term `ℓ = Fin.elim0`) | n/a |
| hypotheses on `Γ` (`IsNested`, `WalkOK`, path properties) | none | none; the statement uses only `Γ.es` (`ghost`, `u`, `v`); `Γ.path` is unused | n/a |
| hypotheses on `ξ` (nonnegativity, decay) | none | none | n/a |
| `D : Finset ι` | arbitrary | none (`D = ∅`, `q ≥ 1` gives `0 = 0`) | n/a |
| instances on `ι` | none (no `Fintype ι`, no `DecidableEq ι`) | `piFinset` needs only the instances on `Fin q`; both sides use the same `piFinset` term | n/a |
| external hypotheses | none | none, so no limit computation is needed (TEAM §8 lesson 14) | n/a |

### (ii) Concrete nondegenerate instance

Data: `p = q = 2`, `ι = {0,1,2}`, `D = {0,1}` (a proper subset, `|D^q| = 4 < 9 = |ι^q|`), `a = (0,2)`, `b = (1,2)`,
`ξ(x,y) = (1 + 3x + y²)/7` (asymmetric), 5 edges: `a0–l0`, `l0–b0`, `a1–l1`, `l1–b1` (ghost), `l0–l1`.
There are solid and ghost edges, a repeated internal vertex and a non-trivial restriction `D ≠ univ`. The script models the definitions above in exact rational arithmetic (it is a Python model of the formulas, not Lean).
`valOnD` is evaluated as a sum over `D^q` of the product over `k` of `anpKey6_w`.
`valOn` is evaluated as a sum over `piFinset D` of the list product of the mapped edge factors.

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2312/inst.py`
```
p,q,|iota|,D = 2 2 3 [0, 1] ; #edges = 5 (ghost: 1 )
|piFinset D| = 4 ; |univ^q| = 9
valOnD = 726/2401 ; valOn(piFinset D) = 726/2401 ; equal: True
val over full iota^q = 11076/2401 ; differs from D-restricted: True
```
Every hypothesis of the target holds at this data (the target has none beyond the typed arguments), and the identity holds with a nonzero common value, so it is not a vacuous `0 = 0`.

### Verdict
- `lwMomExp_valOnD_eq_valOn`: **PASS** (a true identity, no hypothesis set to satisfy, no exponent; only the elementary `List.prod` versus `Fin`-product step).

## (b) Script output

### Build and axioms (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2312, commit de44f57 on t/T2312, Wed Oct  7 10:54:29 UTC 2026)
```
$ lake build RBM3D.Graph.LWMomExpD 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3353 jobs).
$ lake env lean ax.lean   # import RBM3D.Graph.LWMomExpD; #print axioms RBM.Graph.lwMomExp_valOnD_eq_valOn
'RBM.Graph.lwMomExp_valOnD_eq_valOn' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat a88cf75 HEAD
 RBM3D/Graph/LWMomExpD.lean | 42 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 42 insertions(+)
$ grep -rn "lwMomExp_valOnD_eq_valOn" RBM3D | grep -v Graph/LWMomExpD.lean   # name clash; exit code follows
exit 1
$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Graph/LWMomExpD.lean; exit code follows
exit 1
```

### Target statement and compiled nonempty instance (sed -n 14,45p RBM3D/Graph/LWMomExpD.lean)
```lean
/-- **LW-13b-1 identity twin** (`7_8:1636`, DECISIONS §123): the domain-restricted value
`lwMomExp_valOnD Γ ξ a b D` equals `NGraph.valOn` restricted to `D^q = piFinset D`.
Bridges `AnpDetNearAt` (near, `lwMomExp_valOnD`) and `AnpFarAndAt` (far, `NGraph.valOn`)
in the domain decomposition of `lem:LW_moment_exp`. -/
theorem lwMomExp_valOnD_eq_valOn {p q : ℕ} {ι : Type*}
    (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (D : Finset ι) :
    lwMomExp_valOnD Γ ξ a b D =
      Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D)) := by
  unfold lwMomExp_valOnD NGraph.valOn
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- Compiled nonempty instance: `p = 1`, `q = 2`, `ι = Fin 3`, proper subdomain `D = {0, 1}`,
a solid edge `a₀–α₀`, a solid edge `α₀–α₁`, a ghost edge `α₁–b₀`, an asymmetric weight `ξ`. -/
example :
    lwMomExp_valOnD
      (⟨[⟨false, Sum.inl (Sum.inl 0), Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inr 1⟩,
          ⟨true, Sum.inr 1, Sum.inl (Sum.inr 0)⟩], fun _ => []⟩ : NGraph 1 2)
      (fun x y : Fin 3 => ((x : ℕ) + 2 * (y : ℕ) + 1 : ℝ)) (fun _ => 0) (fun _ => 2)
      ({0, 1} : Finset (Fin 3)) =
    NGraph.valOn
      (⟨[⟨false, Sum.inl (Sum.inl 0), Sum.inr 0⟩, ⟨false, Sum.inr 0, Sum.inr 1⟩,
          ⟨true, Sum.inr 1, Sum.inl (Sum.inr 0)⟩], fun _ => []⟩ : NGraph 1 2)
      (fun x y : Fin 3 => ((x : ℕ) + 2 * (y : ℕ) + 1 : ℝ)) (fun _ => 0) (fun _ => 2)
      (Fintype.piFinset (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3)))) :=
  lwMomExp_valOnD_eq_valOn _ _ _ _ _

end RBM.Graph
```
### Statement against the ticket pin (script diff of the theorem header)
```
identical to ticket pin
```

Narrative: the proof is the ticket sketch verbatim (unfold both sides, Finset.sum_congr, List.ofFn_getElem_eq_map, List.prod_ofFn, rfl). No hypothesis added, signature as pinned. The example instantiates p=1, q=2, ι=Fin 3, proper domain D={0,1}, three edges (two solid, one ghost), asymmetric xi; it has no hypotheses beyond the typed arguments. No ports from RBM1D/RBM2D.

## (c) Verified names
- `List.ofFn_getElem_eq_map`, `List.prod_ofFn`, `Finset.sum_congr`: used by `anpKey6_val_eq` (AnpKey6.lean:669) and compiled here.
- `Fintype.piFinset`, `RBM.Graph.lwMomExp_valOnD`, `RBM.Graph.NGraph.valOn`, `RBM.Graph.anpKey6_w`: compiled here.

## (d) Open issues
- No open issues. No paper-delta candidates (internal algebraic identity; ticket states no delta).
