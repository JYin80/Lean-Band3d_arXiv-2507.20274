Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 06:22:29 UTC 2026

Source: `git -C ../RBM2D show c9a24cf:RBM2D/Green/LDEQuad.lean` (1105 lines; 924 = portmap "kept" = lines before the `Checks` section / `#print axioms`; `sum_coord_mul_deriv` is at line 889, as in the ticket).

### (i) Exponent table

The file is abstract Gaussian calculus on independent centred coordinates (its own header, lines 21-22: involves neither `Z_L²` nor the profile `S`). It contains no exponent of `W`, `L`, `N`; the only dimension-dependent content is the private `Checks` section (lines 924-1021). Every public statement is written against `Sizes.SeqΩ`, `Sizes.SeqCoord`, `Sizes.seqP`, `Sizes.seqGvar` (RBM3D: `RBM.Gauss.Sizes d`, `FineModel.lean:156-169`), where `d` becomes the parameter of `Sizes d` (rule R1).

| Statement (c9a24cf line) | What it says | Role of dimension / exponent | Change from RBM2D |
|---|---|---|---|
| `FinDep` 96, `polyW` 105, `polyW_*` 107-123, `young_pow` 134 | finite dependence; weight `1+∑_{c∈I}|ω_c|`; `(q+1)ab^q ≤ a^{q+1}+q b^{q+1}` (`a,b ≥ 0`) | none (real inequalities; `q` is the moment order) | only `d : Sizes` → `sz : Sizes d` |
| `Tame` 181 and closure lemmas 193-298 | continuous, finitely dependent, polynomially bounded; closed under +,·,conj,pow,sum | none | none (renaming only) |
| `GaussIBP` 318 | Stein: `E[ω_c g]=v_c E[∂_c g]` with `v_c=seqGvar c`; all polynomial moments of `seqP` finite | `v_c` is `gvarF`, `= (W^d)⁻¹ S^{(B)}_{ab}(g)`/2 off-diag in RBM3D (RBM2D: fixed five-point profile) but only through the abstract `seqGvar` | none in statement |
| `Tame.integrable` 328 | `GaussIBP sz → Tame f → Integrable f seqP` | none | none |
| `RowChaos` 354, `w,sg,h,U,V,cen,chaos,dA,dB,Tq,Rq` 388-426 | row chaos `Q=∑h_k B_kl \bar h_l − ∑σ_k B_kk`, `σ_k=2r²w_k` | `κ` abstract index type; `B` bounded by `Bbd`; no `W^d`, `L^d` | none |
| `norm_Rq_le` 431 | `‖R‖ ≤ T/2` | none | none |
| `hasDerivAt_*` 520-850, `tame*` 468-494 | `∂_{a_k}Q=dA_k`, `∂_{b_k}Q=dB_k` and derivative formulas | none | none |
| `sum_coord_mul_deriv` 889 | Euler: `∑_k(ω_{k,tt} dA_k+ω_{k,ff} dB_k)=2(Q+cen)` | none (degree-2 homogeneity) | none |
| `Checks` 924-1021 (private) | two-index chaos on `W_n=L_n=n+3`, `chk_gvar=1/90`, `chk_sg=1/45`, `chk_cen=1/9`, `chk_euler` | **`svar=1/(5W²)`** | see below |

Constants/tokens (portmap row 49: `Z2/zdist2:1`; ST1-COMMON item 2):

| Token | Location | Replacement / status | Slack |
|---|---|---|---|
| `Z2` | line 919 (docstring of `Checks`: `Idx 3 3 = Z2 9`) | `Idx 3 3 2 = Zd 3 6`; card `(WL)^d=216` (below) | exact |
| `1/(5·3²)=1/45`, `chk_gvar 1/90`, `chk_sg 1/45`, `chk_cen 1/9` (lines 978-979, 994-1005; "1/5" is not a portmap token for this file but is a d=2 number) | RBM2D five-point profile; RBM3D `svarF=(W^d)⁻¹·sbKernelR(blk x−blk y)`, kernel `(1+2dg²)⁻¹` at block difference 0 and `g²(1+2dg²)⁻¹` at `|·|_L=1` (`Defs/Block.lean:74`) | at `d=3,W=2,L=3,lam=1`: `svarF=1/56`, `chk_gvar=1/112`, `chk_sg=1/56`, `chk_cen=5/56` | exact rationals, see (ii) |
| `two-dimensional`, `Z_L²` | lines 19, 21 (header prose) | rewrite to `Z_L^d` | prose |
| `gvar_offDiag`, `svar`, `sbSupport`, `blk` in `chk_gvar` 983-988 | RBM2D-specific | `gvarF` off-diag lemma (private copy of `FineModel` `fineModel_gvarF_offDiag`), `svarF`, `sbKernelR`, `zdistD`; `card_nbhd` needs `3 ≤ L` (`Defs/Neighbours.lean:158`): `L=3` ok | `L=3` is the boundary value |

Public declarations: 75 at `c9a24cf` (portmap `pub`=75; my grep of non-private `theorem|def|structure|abbrev` lines gives 75); portmap row 49 "used by ST-2..6 = 0" counts ST-2..ST-6 only, and S1-13, S1-14, S1-17, S1-19 (ST-1) consume them (RBM2D `LDEQuadMom` 97, `LDEQuadT` 127, `IBPPoly` 48, `CondRow` 20 hits of `Tame|polyW|young_pow|FinDep|GaussIBP|RowChaos`). **Drop: none.**

Name clashes: `grep -rnw "FinDep|polyW|Tame|GaussIBP|RowChaos|young_pow" RBM3D` prints no match (empty output). Namespace `RBM.Green` exists (`EntryCore.lean:39`).

Registry (DECISIONS §20 / ticket Amend 1): `GaussIBP` is a `Prop` structure taken as hypothesis by `Tame.integrable` and proved by no theorem of this ticket (RBM2D `IBPPoly:299 gaussIBP`, S1-19). Not a data condition: it is a theorem about `seqP` that the paper's setting implies (standard Stein identity; I am not sure it is a result "the paper proves"), so by the §20 rule "unsure → owed": append `RBM.Green.GaussIBP` to `owedProps` (`RBM3D/Test/Axioms.lean`, `def owedProps`). `Tame` is concluded by `Tame.const` etc., so the scan counts it proved; `RowChaos` is data, not `Prop`.

### (ii) Concrete instance, `d=3, W=2, L=3, lam=g=1`

Sizes: `L_n=3, W_n=2, lam_n=1` (`three_le_L`, `W_pos` hold; `N=(WL)^d=216`). Row `x=(0,0,0)`, columns `yF=(1,0,0)`, `yT=(2,0,0)` in `Z_6^3`, `κ=Bool`, `eps=1`, `r=1`, `B=[[2,1],[0,3]]` constant, `Ifree=∅`, `Bbd=3`. Hypotheses of `sum_coord_mul_deriv` (all are `RowChaos` fields): `co_inj`, `gvar_tag`, `eps_sq`, `B_cont`, `B_bdd`, `Ifree_free`, `B_free`; no other hypothesis. Hypothesis `GaussIBP` of `Tame.integrable` is a later gate's pin (S1-19): stays a hypothesis of its example; its two fields are checked below on the model's actual variance `v=1/112` (Stein with `g=ω³`, finiteness of Gaussian moments is classical).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2031_check.py`
```
N = (WL)^d = 216 =  216
sum_x kern over Z_L^d = 1 (card of |x|=1 : 6 = 2d = 6 )
row sum_j S_{x0 j} = 1
blk x0, yF, yT = (0, 0, 0) (0, 0, 0) (1, 0, 0) ; svarF(x0,yF), svarF(x0,yT) = 1/56 1/56
w = gvarF = 1/112  sg = 2 r^2 w (r=1) = 1/56  [d=2, W=3 RBM2D chk: w=1/90, sg=1/45]
Euler: lhs = (3299/72+19/2i)  rhs = (3299/72+19/2i)  equal: True
dA_k = r(U_k+V_k), dB_k = r eps_k i (U_k-V_k): True True
cen = sum_k sg_k B_kk = (5/56+0i)  [d=2 RBM2D chk: 1/9]
|Rq| = 1.0372216031905304 <= Tq/2 = 1.0381324404761905 : True
co_inj (4 distinct coords): True  eps^2=1: True  Bbd=3 >= max|B_kl|: True  gvar_tag: True
Stein check g=omega^3: E[w x^4]=3v^2 = 3/12544  v*E[3x^2] = 3/12544
```
Reading: the variance profile is row-stochastic on all 216 points (`∑_j S_{x0 j}=1`) and `S_{x0,yF}=S_{x0,yT}=1/56` (same block, resp. block at `|·|_L=1`, both `(W^d)⁻¹(1+2dg²)⁻¹=1/(8·7)` at `g=1`), so `gvarF=1/112`, `σ_k=1/56`, `cen=5/56` replace the d=2 values `1/90, 1/45, 1/9`. Euler's identity holds exactly with the exponents/constants of the statement unchanged (`2(Q+cen)`, factor 2 = degree of the chaos).

### Verdicts
- Targets `FinDep`…`Tame.integrable`, `RowChaos` and derivative lemmas, `sum_coord_mul_deriv`: **PASS** (dimension-free; hypotheses satisfiable at the instance above; no exponent closes against anything).
- `Checks` section numeric constants must be recomputed as above (`1/112, 1/56, 5/56` at `lam=1`): **PASS** (values verified by script).
- Verdict: **PASS**.

## (b) Script output — stage 1b, Sat Oct  3 06:28:19 UTC 2026

Branch `t/T2031`, commit `2c7ebcc`; files: `RBM3D/Green/LDEQuad.lean` (new, 1049 lines), `RBM3D/Test/Axioms.lean` (registry lines).

### Build
```
$ lake build RBM3D.Green.LDEQuad   # tail (18 style-linter warnings, no error)
Build completed successfully (3244 jobs).
$ lake build   # full library, root #assert_rbm_axioms; exit 0
Build completed successfully (3736 jobs).
```

### Registry pre-check (DECISIONS §20; scratch file outside the repository)
```
$ cat precheck.lean
import RBM3D
import RBM3D.Green.LDEQuad
#assert_rbm_axioms
$ lake env lean precheck.lean   # exit 0
axiom audit: 1278 theorems, 452 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
```
Registered (RBM3D/Test/Axioms.lean): `RBM.Green.GaussIBP` in `owedProps` (a Stein identity about `seqP`, proved by S1-19, not a data condition; unsure, so owed); `RBM.Green.FinDep` in `structuralProps` (property of a function, hypothesis of `Tame.ofBdd`). `Tame` is concluded by `Tame.const`, `RowChaos` is data: not scanned.

### Axioms of the 75 public declarations (`#print axioms`, script `ax.lean`)
```
$ lake env lean ax.lean | sed "s/.*depends on axioms: //" | sort | uniq -c
  75 [propext, Classical.choice, Quot.sound]
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Green/LDEQuad.lean
0
```
Public count (declarations of the RBM2D file before `Checks`): 75 = RBM2D portmap `pub` 75. Dropped: none.

### Target statements (extracted by script from the file)
```lean
theorem sum_coord_mul_deriv (ω : Sizes.SeqΩ sz) :
    ∑ k, ((ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k)
      = 2 * (C.chaos ω + C.cen ω) := by
theorem hasDerivAt_chaos_true (k : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k true) s))
      (C.dA ω k) (ω (C.co k true)) := by
theorem hasDerivAt_chaos_false (k : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k false) s))
      (C.dB ω k) (ω (C.co k false)) := by
theorem Tame.integrable (hG : GaussIBP sz) {f : Sizes.SeqΩ sz → ℂ} (hf : Tame sz f) :
    Integrable f (Sizes.seqP sz) := by
structure GaussIBP (sz : Sizes d) : Prop where
structure Tame (sz : Sizes d) (f : Sizes.SeqΩ sz → ℂ) : Prop where
structure RowChaos (sz : Sizes d) (κ : Type*) [Fintype κ] [DecidableEq κ] where
theorem young_pow (q : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((q : ℝ) + 1) * (a * b ^ q) ≤ a ^ (q + 1) + (q : ℝ) * b ^ (q + 1) := by
theorem norm_Rq_le (ω : Sizes.SeqΩ sz) : ‖C.Rq ω‖ ≤ C.Tq ω / 2 := by
```

### Statement diff against RBM2D (c9a24cf:RBM2D/Green/LDEQuad.lean lines 81-915, after renaming R1)
```
$ git -C ../RBM2D show c9a24cf:RBM2D/Green/LDEQuad.lean | sed -n 81,915p | perl -pe 's/Sizes\.(SeqΩ|SeqCoord|seqGvar|seqP) d/Sizes.$1 sz/g; s/(Tame|FinDep|RowChaos|GaussIBP) d/$1 sz/g; s/\(d := d\)/(sz := sz)/g; (+ the four binder lines `(d : Sizes)` -> `(sz : Sizes d)`, `variable {d : Sizes}` -> `variable {sz : Sizes d}`)' | diff - <(sed -n '/^namespace RBM.Green/,/^end RowChaos/p' RBM3D/Green/LDEQuad.lean)
5a6,7
> variable {d : ℕ}
> 
16c18
< def FinDep {d : ℕ} (sz : Sizes d) {V : Type*} (g : Sizes.SeqΩ sz → V) : Prop :=
---
> def FinDep (sz : Sizes d) {V : Type*} (g : Sizes.SeqΩ sz → V) : Prop :=
25c27,28
< noncomputable def polyW (I : Finset (Sizes.SeqCoord sz)) (ω : Sizes.SeqΩ sz) : ℝ := 1 + ∑ c ∈ I, |ω c|
---
> noncomputable def polyW (I : Finset (Sizes.SeqCoord sz)) (ω : Sizes.SeqΩ sz) : ℝ :=
>   1 + ∑ c ∈ I, |ω c|
```
Residuals: `variable {d : ℕ}` added (the parameter of `Sizes d`); `FinDep` takes `(sz : Sizes d)` with `d` from the variable; one line break in `polyW` (line length). Every statement and proof is otherwise RBM2D's verbatim.

### Compiled nonempty instance (d = 3, `sz0` n = 0: L = 4, W = 32, lam = 1/64, N = 2097152; same file, section `Checks`)
```lean
section Checks
open SizesInst
private noncomputable def chkX : Idx 3 (sz0.L 0) (sz0.W 0) := 0
private noncomputable def chkY : Bool → Idx 3 (sz0.L 0) (sz0.W 0)
  | false => ![1, 0, 0]
  | true => ![32, 0, 0]
private noncomputable def chkCo (k b : Bool) : Sizes.SeqCoord sz0 := ⟨0, (chkX, chkY k, b)⟩
private noncomputable def chkMat : Bool → Bool → ℂ
  | false, false => 2
  | false, true => 1
  | true, false => 0
  | true, true => 3
private theorem chkY_injective : Function.Injective chkY := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)
private theorem chkCo_injective : Function.Injective fun p : Bool × Bool => chkCo p.1 p.2 := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  simp only [chkCo, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨hy, hb⟩ := h
  rw [chkY_injective hy, hb]
private noncomputable def chkChaos : RowChaos sz0 Bool where
  co := chkCo
  co_inj := chkCo_injective
  gvar_tag _ := rfl
  eps _ := 1
  eps_sq _ := by norm_num
  r := 1
  B _ := chkMat
  B_cont _ _ := continuous_const
  Bbd := 3
  B_bdd _ k l := by
    cases k <;> cases l <;> norm_num [chkMat]
  Ifree := ∅
  Ifree_free _ _ := Finset.notMem_empty _
  B_free _ _ _ := rfl
private theorem chk_gvarF_offDiag (i j : Idx 3 (sz0.L 0) (sz0.W 0)) (b : Bool) (hij : i ≠ j) :
    (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (i, j, b) : ℝ) =
      svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j / 2 := by …
private theorem chk_svarF_false :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) chkX (chkY false) =
      ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹ := by …
private theorem chk_svarF_true :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) chkX (chkY true) =
      ((32 : ℝ) ^ 3)⁻¹ * ((1 / 64 : ℝ) ^ 2 * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹) := by …
private theorem chk_w (k : Bool) : 0 < chkChaos.w k := by …
private theorem chk_sg (k : Bool) : 0 < chkChaos.sg k := by …
private theorem chk_tame_coord :
    Tame sz0 (fun ω : Sizes.SeqΩ sz0 => (ω (chkChaos.co false true) : ℂ)) :=
  Tame.coord _
private theorem chk_euler (ω : Sizes.SeqΩ sz0) :
    ∑ k, ((ω (chkChaos.co k true) : ℂ) * chkChaos.dA ω k
      + (ω (chkChaos.co k false) : ℂ) * chkChaos.dB ω k)
      = 2 * (chkChaos.chaos ω + chkChaos.cen ω) :=
  chkChaos.sum_coord_mul_deriv ω
example (hG : GaussIBP sz0) : Integrable chkChaos.chaos (Sizes.seqP sz0) :=
  Tame.integrable hG chkChaos.tamechaos
example (ω : Sizes.SeqΩ sz0) (k : Bool) :
    HasDerivAt (fun s : ℝ => chkChaos.chaos (Function.update ω (chkChaos.co k true) s))
      (chkChaos.dA ω k) (ω (chkChaos.co k true)) ∧
    HasDerivAt (fun s : ℝ => chkChaos.chaos (Function.update ω (chkChaos.co k false) s))
      (chkChaos.dB ω k) (ω (chkChaos.co k false)) ∧
    ‖chkChaos.Rq ω‖ ≤ chkChaos.Tq ω / 2 :=
  ⟨chkChaos.hasDerivAt_chaos_true k ω, chkChaos.hasDerivAt_chaos_false k ω,
    chkChaos.norm_Rq_le ω⟩
example (ω : Sizes.SeqΩ sz0) :
    ((2 : ℕ) + 1 : ℝ) * (1 * 2 ^ 2) ≤ 1 ^ (2 + 1) + (2 : ℕ) * 2 ^ (2 + 1) ∧
    1 ≤ polyW ({chkChaos.co false true} : Finset (Sizes.SeqCoord sz0)) ω ∧
    polyW ({chkChaos.co false true} : Finset (Sizes.SeqCoord sz0)) ω ^ 1 ≤
      polyW {chkChaos.co false true, chkChaos.co true true} ω ^ 2 :=
  ⟨by simpa using young_pow 2 (a := 1) (b := 2) (by norm_num) (by norm_num),
    one_le_polyW _ ω, polyW_pow_le (by simp) (by norm_num) ω⟩
end Checks
```

### Name clash and ports
```
$ grep -rnwE "FinDep|polyW|Tame|GaussIBP|RowChaos|young_pow|one_le_polyW|polyW_pos|polyW_nonneg|polyW_mono|polyW_pow_le" RBM3D RBM3D.lean --include="*.lean" | grep -v "Green/LDEQuad.lean"
RBM3D/Test/Axioms.lean:90:   `RBM.Green.GaussIBP]  -- Stein identity and finite polynomial
RBM3D/Test/Axioms.lean:115:   `RBM.Green.FinDep,         -- `g` reads finitely many Gaussi
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/LDEQuad.lean
 RBM2D/Green/LDEQuad.lean | 222 ++++-------------------------------------------
 1 file changed, 15 insertions(+), 207 deletions(-)
$ git diff --stat main...t/T2031
 RBM3D/Green/LDEQuad.lean | 1049 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    4 +-
 2 files changed, 1052 insertions(+), 1 deletion(-)
$ grep -nE "d = 2|Z2|1/5|zdist2|W2|L2" RBM3D/Green/LDEQuad.lean   # empty (exit 1)
exit=1
```

### Narrative (report-level facts only)
- Port of RBM2D `Green/LDEQuad.lean` lines 81-915 at `c9a24cf` (all 75 public declarations, none dropped; the portmap marks none unused: S1-13, S1-14, S1-17, S1-19 consume them). Statements and proofs are RBM2D's after rule R1 (script diff above: three residual hunks, none changes a statement).
- Imports: `RBM3D.Gauss.FineModel` replaces `RBM2D.Gauss.Model`; Mathlib imports are RBM2D's. No ST-2..ST-6 file, no `RBM3D` root.
- Dimension: the ported part has no `W`, `L`, `N`, `d` content (preflight table (i)); `d` occurs only as the parameter of `Sizes d`. The RBM2D `Checks` section was rewritten (not ported) at `d = 3` on `SizesInst.sz0` (ticket instance rule); its `Z2`, `svar`, `sbSupport`, `blk`, `gvar_offDiag`, `1/90`, `1/45`, `1/9` tokens are replaced by `Zd 3`, `svarF`, `SBR`/`sbKernelR`/`split`, a private copy of the off-diagonal variance lemma, and the exact values `S = (32^3)^{-1}(1+6g^2)^{-1}` (same block) and `(32^3)^{-1} g^2 (1+6g^2)^{-1}` (neighbouring block), `g = 1/64`. Zero `d = 2` tokens remain (grep above).
- Instance: `chkChaos : RowChaos sz0 Bool` has `co_inj`, `gvar_tag`, `eps_sq`, `B_cont`, `B_bdd`, `Ifree_free`, `B_free` all discharged; `chk_euler` applies `sum_coord_mul_deriv`; the `example` for `Tame.integrable` keeps `GaussIBP sz0` as a hypothesis (S1-19 pin, owed registry). Both columns have positive variance (`chk_w`, `chk_sg`).
- The preflight section (a) used `W = 2, L = 3, lam = 1` for its numeric check; the Lean instance uses `sz0` (`W = 32, L = 4, lam = 1/64`) as ST1-COMMON item 7 prescribes; no statement depends on the choice.
- The exact `GaussIBP` classification (owed vs structural) is for the dispatcher to confirm (I was unsure whether the paper proves Stein's identity, so owed per DECISIONS §20).

## (c) Verified Mathlib names (all used in the file; it builds)
`geom_sum₂_mul`, `Finset.sum_nonneg`, `Finset.sum_le_sum_of_subset_of_nonneg`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `Integrable.mono`, `Integrable.const_mul`, `HasDerivAt.fun_mul`, `HasDerivAt.fun_sum`, `HasDerivAt.const_mul`, `HasDerivAt.ofReal_comp`, `Complex.conjCLE`, `Function.update_eq_self`, `Function.update_of_ne`, `Finset.notMem_empty`, `Complex.continuous_conj`, `Complex.norm_real`. (Names as written by RBM2D at `c9a24cf`; the build above is the verification. No name verified absent.)

## (d) Open issues and paper-delta candidates
- No paper-delta candidate: the file states no paper statement (abstract Gaussian calculus; none of the paper's labels is involved).
- Registry: `RBM.Green.GaussIBP` owed, `RBM.Green.FinDep` structural (above). The hub merge step 5 should find the registry clean (pre-check exit 0); if merging conflicts on `Test/Axioms.lean` only in the lists, take the union (DECISIONS §20).
- S1-19 must prove `GaussIBP sz` for `Sizes.seqP sz` with `seqGvar` (RBM3D `seqP_map_restrict` at `FineModel.lean:521` is the reduction to a finite product).
