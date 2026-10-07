Auditor model: claude-opus-5-5

# T2312 audit (round 1), Wed Oct  7 10:55:58 UTC 2026

Branch `t/T2312` at `de44f57`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2312-audit1` (detached).
Target: `RBM.Graph.lwMomExp_valOnD_eq_valOn` in `RBM3D/Graph/LWMomExpD.lean`.

## 1. Statement against the ticket pin (script diff)
```
$ awk '/^```lean/{f=1;next} /^```/{if(f){exit}} f' docs/tickets/T2312.md | <strip docstring> > pin.txt
$ sed -n '/^theorem lwMomExp_valOnD_eq_valOn/,/:= by/p' RBM3D/Graph/LWMomExpD.lean | sed 's/ := by$//' > lean.txt
$ diff pin.txt lean.txt && echo "DIFF: identical"
DIFF: identical
$ cat lean.txt
theorem lwMomExp_valOnD_eq_valOn {p q : ℕ} {ι : Type*}
    (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (D : Finset ι) :
    lwMomExp_valOnD Γ ξ a b D =
      Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D))
```
The definitions it relates (signatures read on `main`):
```
LWMomExp.lean:526  noncomputable def lwMomExp_valOnD {p q : ℕ} {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ)
    (a b : Fin p → ι) (D : Finset ι) : ℝ :=
  ∑ ℓ ∈ Fintype.piFinset (fun _ : Fin q => D), ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k
AnpKey2.lean:54    def valOn (Γ : NGraph p q) {ι : Type*} (ξ : ι → ι → ℝ) (a b : Fin p → ι)
    (S : Finset (Fin q → ι)) : ℝ :=
  ∑ ℓ ∈ S, (Γ.es.map fun e => if e.ghost then (1 : ℝ) else ξ (…ℓ e.u) (…ℓ e.v)).prod
AnpKey6.lean:664   def anpKey6_w … := if (Γ.es.get k).ghost then 1 else ξ (…ℓ (Γ.es.get k).u) (…ℓ (Γ.es.get k).v)
```
Both sides are `Σ_{ℓ∈D^q} Π_{edges} (1 if ghost else ξ(lab u, lab v))`; the statement is the general
identity for arbitrary `p q ι Γ ξ a b D` with no hypotheses, as the ticket's mathematics requires.
Not a special case.

## 2. Vacuity, hidden hypotheses, cycles
- No hypotheses at all; no structure carries a hypothesis. `NGraph` (LWVocab.lean:311) has only data fields:
```
structure NGraph (p q : ℕ) where
  es : List (NEdge p q)
  path : Fin p → List (Fin es.length × NV p q)
```
- Dependencies: only `RBM3D.Graph.LWMomExp` (merged), whose defs are used; the new file is not imported anywhere
  else, so no cycle. No external hypothesis, so no limit check is needed.

## 3. Compiled nonempty instance
The file's `example` (lines ~29-43) applies the theorem at `p = 1`, `q = 2`, `ι = Fin 3`, `D = {0,1}` (proper,
`|D^q| = 4 < 9`), three edges (two solid, one ghost), asymmetric `ξ x y = x + 2y + 1`, `a = 0`, `b = 2`.
It compiles as part of the module build (§4). The theorem has no hypotheses to discharge.
Nondegeneracy check by the auditor (scratch file, not in the branch): the common value is 22, not 0.
```
$ cat val.lean  (tail)
  unfold NGraph.valOn
  have h : (Fintype.piFinset (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3)))) = {![0,0], ![0,1], ![1,0], ![1,1]} := by decide
  rw [h]
  simp [Finset.sum_insert] ; norm_num
$ lake env lean val.lean   # goal: NGraph.valOn <same data as the example> = 22
exit 0
```

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Graph.LWMomExpD 2>&1 | grep -E "error|warning|Build completed" | grep -v linter | tail -5
warning: RBM3D/Graph/AnpKey.lean:905:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Graph/AnpKey.lean:906:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Graph/AnpKey.lean:915:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Graph/AnpKey.lean:916:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3353 jobs).
$ lake build RBM3D.Graph.LWMomExpD 2>&1 | grep -E "LWMomExpD" | grep -E "error|warning" | wc -l
       0
$ lake env lean ax.lean   # import RBM3D.Graph.LWMomExpD; #print axioms RBM.Graph.lwMomExp_valOnD_eq_valOn
'RBM.Graph.lwMomExp_valOnD_eq_valOn' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|set_option" RBM3D/Graph/LWMomExpD.lean; echo "hygiene grep exit $?"
hygiene grep exit 1
$ git diff --stat main...HEAD
 RBM3D/Graph/LWMomExpD.lean | 42 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 42 insertions(+)
$ grep -rn "lwMomExp_valOnD_eq_valOn" RBM3D | grep -v LWMomExpD.lean; echo "clash grep exit $?"
clash grep exit 1
```
(The warnings are in the pre-existing merged `AnpKey.lean`, not in the ticket's file.)
The diff touches only the sole writable file `RBM3D/Graph/LWMomExpD.lean`; no frozen signature is touched.

## 5. Paper deltas
The Lean statement is an internal algebraic identity between two Lean value forms of the same paper sum
(`7_8:1636`); it introduces no Lean/paper statement difference. The ticket states no delta; none needed.

## Observations (no effect on verdict)
- The prove report's section (a) labels the prover as the author of the preflight; the ticket waived stage 1a.
  Process only.

## Verdict
- `lwMomExp_valOnD_eq_valOn`: **PASS**.
Ticket T2312: **PASS**. No dispatcher sign-off needed.
