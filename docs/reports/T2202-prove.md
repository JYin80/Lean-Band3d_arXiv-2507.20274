Prover model: claude-sonnet-5-5

## (a) Math preflight — 2026-10-05 19:06 UTC (`date -u`: Mon Oct  5 19:06:01 UTC 2026)

Notation: `N = (W L)^d`, `n` = loop length bound, `B,B'\ge 0`. All statements below hold for every `d` (no `3 ≤ d` is used); instance at `d = 3` (and `d = 4` in the power count).

### (i) Exponent table

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `SBgue` entry (T1) | `L^{-d}`; `∑_a S_{ab} = L^d · L^{-d} = 1` needs `L^d ≠ 0` (`NeZero L`, `card_Zd`, merged `Defs/Lattice.lean:67`) | equality; `d = 0` also fine (`L^0 = 1`) |
| 2 | double sum (T4) | `∑_{a,b} |S_{ab}| = L^{2d} L^{-d} = L^d`, so `W^d · L^d = (W L)^d = N` | equality (script: 27, 64, 81) |
| 3 | cut/glue lengths (T4) | for `1 ≤ k < l ≤ m`: `|cutL| = k+m-l+1`, `|cutR| = l-k+1`, sum `m+2`, each in `[2, m]` (so the `K,K'` bounds apply, `WF` kept) | 0 violations on 763308 cases |
| 4 | pair count / sum shape (T4) | `j := |cutR| ∈ [2,m]`, `|cutL| = m-j+2`; pairs with a given `j`: `m-j+1 ≤ m`; total `m(m-1)/2 ≤ m²` | bound `m² N ∑_j B(m-j+2)B'(j)` is loose by factor ≥ 2 (instance: 648 vs 3888) |
| 5 | `ellT_eq_L` (T3) | `0 ≤ g`, `t < 1`, `L²(1-t) ≤ g²` ⟹ `g/√(1-t) ≥ L` ⟹ `max(g/√(1-t),1) ≥ L` ⟹ `ellT = L` (exponent 2: `ℓ` is a length, `d`-free); true for all `L : ℕ` | equality at `L=4, g=1/2, t=63/64` (`16/64 = 1/4`); `g<0` and `t ≥ 1` need the hypotheses (cex below) |
| 6 | `K_bootstrap` (T5) | `B := 2Aλ(u)^{-(len-1)}`: product exponent `(len-j+1)+(j-1) = len` for every `j`; derivative bound `≤ 4CnA²N λ^{-len}`; `λ` decreasing gives `∫ ≤ 4CnA²·N(t-t₁)·λ(t)^{-len}`; with `N(t-t₁) ≤ ελ`, `4CnAε<1`: `‖k‖ ≤ Aλ(t₁)^{-(len-1)} + 4CnA²ελ^{-(len-1)} < 2Aλ(t)^{-(len-1)}`. `ε ≥ 0` is forced at `t = t₁` | `0 < A` makes the last step strict |
| 7 | `eq736` constants (T7) | apply T5 with `C = n²`, `N = (WL)^d` (T4: `len(I)² ≤ n²`, sum has only `B ≥ 0` terms): needs `4 n³ A ε < 1` | instance `0.32`, slack `0.68`; saturating case `0.98743` (script) |
| 8 | (7.30) at `N=216` | `N(t-t₁) ≤ ε λ_t`: `216 ≤ 400` (`λ ≡ 40000, ε = 1/100`) | slack `184` (ticket's `λ ≡ 4000` of RBM2D would give `40 < 216`: too small, as the ticket says) |
| 9 | `eventually_small` (T5) | `τ' < τU ⟹ N^{τ'-τU} → 0`, `4n³ N^{τ'-τU} < 1` iff `N > (4n³)^{1/(τU-τ')}` | instance `n=2, τ'=1/4, τU=1/2`: `N > 32^4 = 2^20` (a `∀ᶠ` statement, no explicit `N` needed) |
| 10 | `eventually_rpow_le_of_neg` (T7) | `a<0, ρ>0`: `N^a ≤ ρ` iff `N ≥ ρ^{1/a}` (`N ≥ 1`) | no hypothesis beyond `a<0, 0<ρ` |
| 11 | `finite_loopIdx` (T5) | `Zd d L = Fin d → ZMod L` finite for `NeZero L`; loops of length `≤ n`: `≤ ∑_{m≤n} 2^m L^{dm}` | finite for every `d,n` |
| 12 | `rhs745G/746G` (T6) | `N` abstract; martingale line `√(t-t₁)·√(N⁻¹η⁻²)` has no `d` | RBM2D `PathBounds.lean:230-400` at `c9a24cf`: `W ^ 2`: 0, `L ^ 2`: 0, `Z2`: 4 (types of `Kt`/`hK` only), `d.size`: 15 (script below) |
| 13 | window for consumers (iv) | `Nη_{t₁} = N(1-t₁) Im m ≤ (WL)^d g²/L² Im m = g² W^d L^{d-2} Im m` (largest admissible `1-t₁ = g²/L²`); `d=2`: `g² W²` | table below: `log_N ∈ [0.6975, 0.8272]` |
| 14 | `hscale` on window | `t-t₁ ≤ N^{-τU}η_t` gives `1-t ≥ (1-t₁)/(1+N^{-τU}Im m)`, so `Nη_t ≥ Nη_{t₁}/2` (`Im m=1`); need `log_N(Nη_{t₁}/2) ≥ τU` | min margin `0.552` (`τU = 1/10`), `0.602` (`1/20`), `0.652` (T2173 values) |

Flags for the dispatcher (no target fails): (F1) the ticket's `τU ∈ {1/20, 1/10}` are the `𝔡` values of `T2173-prove.md:32-33`; the `τ_U` of that table is `≤ 1/79200`, `1/264000` (`T2173-prove.md:32-33`, rows `c=1/6,d=1/10` and `c=1/10,d=1/20`). All four values were checked (rows 14, script). (F2) `1-t₁ ≤ g²/L²` is only an upper bound: `hscale` also needs the lower bound `1-t₁ ≥ 2N^{τU-1}/Im m`; the two are compatible since the table has `Nη_{t₁}^{max}/2 ≥ N^{τU}`. This is a constraint for UN-31/48 (not for T2202). (F3) `4 n³ N^{τ'-τU} < 1` holds only for `log2 N > 100` (`n=2, τ'=τU/2, τU=1/10`) and `> 2.6·10^6` (`τU = 1/264000`, `n=2`): an asymptotic statement, as in RBM2D; no limit hypothesis is external (class G, no external input; the only limits are `N^{τ'-τU}→0`, `N^a→0`, both elementary).

### (ii) Concrete instance and scripts

Instance: `d=3, L=3, W=2` (`N=216`), loop `⟨[+,-,+],[0,1,2]⟩` (`|I|=3`) for T4 (`K=K'≡1`: `648 ≤ 3888`); `eq736`: `n=2, K≡0, t₁=0, t₀=1, A=1, ε=1/100, λ≡40000` (all hypotheses: `λ>0`, antitone, continuous, `‖K t₁‖ = 0 ≤ Aλ^{-1}`, `216·t ≤ 400`, `0.32<1`; derivative `0 = primRhsGUE(0)`); nonzero tight solution at `n=2`: `K ≡ K₀/(1-NK₀t)`, `K₀=1/7000` solves `K' = primRhsGUE K = N K²` (for `|I|=2` the only pair is `(k,l)=(1,2)`, `cutL = [x,a₂]`, `cutR = [a₁,y]`, sum `= L^{-d}(∑_x K)(∑_y K) · W^d` with `K` constant in the labels), `ε = 216/7000`, `4n³Aε = 0.98743`, `K(1)λ = 1.03184 < 2`. `ellT_eq_L`: `L=4, g=1/2, t=63/64`. `eventually_small`: `n=2, τ'=1/4, τU=1/2`. `finite_loopIdx`: `d=3, L=3, n=4`.

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2202/pre.py
SBgue d=3 L=3: |Z|=27=L^d=27, col sum=1, sum|S|=27=L^d:True
SBgue d=3 L=4: |Z|=64=L^d=64, col sum=1, sum|S|=64=L^d:True
SBgue d=4 L=3: |Z|=81=L^d=81, col sum=1, sum|S|=81=L^d:True
n=2: #(k,l)=1=n(n-1)/2:True <= n^2:True
n=3: #(k,l)=3=n(n-1)/2:True <= n^2:True
n=4: #(k,l)=6=n(n-1)/2:True <= n^2:True
cut/glue checks: 763308 violations: 0 (n<=3 full over Z_3^3 x Bool^n; n=4 all sigma, 3000 random label tuples)
K=K'=1, |I|=3, d=3,L=3,W=2: |primBil| = 648 = 8*3*27: True ; bound 3^2*216*2 = 3888 ; ok: True
random K,K' (40 loops n<=4, d=3 L=3 W=2): max LHS/RHS = 0.0165 <= 1: True
ellT_eq_L grid: hypotheses satisfied at 480 points, failures 0
L=4,g=1/2,t=63/64: 4.0 hyp 16/64<=1/4: True
cex g=-1,L=5,t=99/100: hyp 0.2500000000000002 <=1 ; ellT = 1.0
cex t=2,g=1,L=5: hyp -25 <=1 ; ellT = 1.0
eq736 inst: N= 216 N*(t-t1)<= 216 <= eps*lam = 400 ; 4n^3 A eps = 8/25 <1
tight n=2: lam=7000, eps=N/lam=0.03086, 4n^3 A eps=0.98743<1: True; K(1)*lam=1.03184 < 2: True
table: g,(d,L,W),N, N*eta_t1=g^2 W^d L^(d-2) (Im m=1), log_N; d=2 form g^2W^2
g=0.5 (d,L,W)=(3,4,32) N=2^21.00 Neta=3.277e+04 logN=0.7143 d=2-form g^2W^2=256.0
g=0.5 (d,L,W)=(3,5,32) N=2^21.97 Neta=4.096e+04 logN=0.6975 d=2-form g^2W^2=256.0
g=0.5 (d,L,W)=(4,3,8) N=2^18.34 Neta=9216 logN=0.7181 d=2-form g^2W^2=16.0
g=1.0 (d,L,W)=(3,4,32) N=2^21.00 Neta=1.311e+05 logN=0.8095 d=2-form g^2W^2=1024.0
g=1.0 (d,L,W)=(3,5,32) N=2^21.97 Neta=1.638e+05 logN=0.7886 d=2-form g^2W^2=1024.0
g=1.0 (d,L,W)=(4,3,8) N=2^18.34 Neta=3.686e+04 logN=0.8272 d=2-form g^2W^2=64.0
tauU=0.05: hscale N eta_t>=N^tauU holds at all 6 rows with margin min log_N(Neta_t1/2)-tauU = 0.602
   n0=2, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 200
   n0=8, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 440
tauU=0.1: hscale N eta_t>=N^tauU holds at all 6 rows with margin min log_N(Neta_t1/2)-tauU = 0.552
   n0=2, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 100
   n0=8, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 220
tauU=1.26e-05: hscale N eta_t>=N^tauU holds at all 6 rows with margin min log_N(Neta_t1/2)-tauU = 0.652
   n0=2, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 7.92e+05
   n0=8, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 1.742e+06
tauU=3.79e-06: hscale N eta_t>=N^tauU holds at all 6 rows with margin min log_N(Neta_t1/2)-tauU = 0.652
   n0=2, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 2.64e+06
   n0=8, tau'=tauU/2: 4n^3 N^(tau'-tauU)<1 iff log2 N > 5.808e+06
```

```
$ cd /Users/junyin/Lean_proof/RBM2D; for p in 'W \^ 2' 'L \^ 2' 'Z2' 'd\.size'; do echo "$p: $(git --no-optional-locks show c9a24cf:RBM2D/Universality/GUEPhase/PathBounds.lean | sed -n 230,400p | grep -c -E "$p")"; done
W \^ 2: 0
L \^ 2: 0
Z2: 4
d\.size: 15
```

Script note: `pre.py` is Python (no Lean), kept in the scratchpad; "random K" rows use random phases (max ratio 0.0165 is a smoke test, the proof is rows 2-4). Reachable set of RBM2D `Bootstrap.lean` at HEAD `9e0f275` (`git show HEAD:... | grep '^theorem|def|abbrev'`): the 27 declarations of the ticket (`SBgue`, `SBgue_apply`, `continuity_argument`, `ellT_eq_L`, `primBilGUE`, `primRhsGUE`, `_add_left/right`, `primRhsGUE_sub`, `norm_primBilGUE_le`, `norm_primRhsGUE_le`, `sum_pow_mul_pow`, `K_bootstrap`, `finite_loopIdx`, `eq736`, `LoopSet`, `eventually_small`, `supOn`, `supOn_le`, `rhs745G`, `rhs746G`, `supOn_line1_le`, `mul_le_of_eq730`, `sqrt_mul_sqrt_le`, `supOn_nonneg`, `inv_mul_pow`, `eventually_rpow_le_of_neg`), none of `eq736_detDom`, `stochDom_of_forall_highProb`.

Counterexamples (script above): `g=-1, L=5, t=99/100` and `t=2, g=1, L=5` satisfy `L²(1-t) ≤ g²` but `ellT = 1 ≠ 5`, so `0 ≤ g` and `t < 1` are needed in T3.

### Verdicts
- T1 `SBgue`, `sum_SBgue_col/row`: PASS (rows 1-2; script `col sum=1`).
- T2 `continuity_argument`: PASS (dimension-free, verbatim port).
- T3 `ellT_eq_L`: PASS (row 5; 480 grid points, 0 failures; hypotheses necessary).
- T4 `primBilGUE` family, `norm_primBilGUE_le`, `norm_primRhsGUE_le`: PASS (rows 2-4; instance `648 ≤ 3888`).
- T5 `sum_pow_mul_pow`, `K_bootstrap`, `finite_loopIdx`, `eq736`, `eventually_small`: PASS (rows 6-9, 11; instance and saturating example).
- T6 `supOn` vocabulary: PASS (row 12; no `d` enters; the scalar lemmas are real-variable, verbatim).
- T7 `eventually_rpow_le_of_neg`: PASS (row 10).
- Overall: PASS. Flags F1-F3 are for the consumers' tickets / dispatcher; no input is missing.

## (b) Script output and narrative — Mon Oct  5 19:22:13 UTC 2026

Branch `t/T2202` at `d9f3538`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2202`, sole file `RBM3D/Universality/GUEPhase/Bootstrap.lean` (new). Scratch files: scratchpad `T2202/` (`report_b.sh`, `pincheck.lean`, `declcmp.py`, `extract.py`). No (a′): section (a) is unchanged.

```
$ grep -n "^import" RBM3D/Universality/GUEPhase/Bootstrap.lean; grep -nE "hd : 3|3 ≤ d" (same file)
6:import Mathlib.Analysis.Calculus.Deriv.Inv
7:import Mathlib.Analysis.Calculus.MeanValue
8:import Mathlib.Analysis.Complex.RealDeriv
9:import Mathlib.Data.Set.Finite.List
10:import RBM3D.Defs.Lattice
11:import RBM3D.Defs.Params
12:import RBM3D.Defs.Domination
13:import RBM3D.Loop.TreeRep
32:All statements hold for every `d` (no `3 ≤ d`); the only `d`-dependence is `SBgue` (`L^{-d}`), the
$ lake build   (whole library in the worktree; the root RBM3D.lean does not yet import the new module, the hub adds it at merge)
Build completed successfully (4005 jobs).
$ lake build RBM3D.Universality.GUEPhase.Bootstrap 2>&1 | grep -v "^trace" | tail -3
Build completed successfully (2509 jobs).
commit: d9f3538 T2202: UN-26a GUEPhase/Bootstrap (abstract bootstrap; branch t/T2202
$ git diff --stat main...t/T2202
 RBM3D/Universality/GUEPhase/Bootstrap.lean | 863 +++++++++++++++++++++++++++++
 1 file changed, 863 insertions(+)
$ wc -l  RBM3D/Universality/GUEPhase/Bootstrap.lean ; hygiene grep
     863
sorry/admit/native_decide/axiom hits: 0

$ lake env lean ax_all.lean  (#print axioms of the public declarations and of the BootstrapCheck declarations), aggregated
60 declarations printed
56 depends on axioms: [propext, Classical.choice, Quot.sound]
1 does not depend on any axioms
3 depends on axioms: [propext, Quot.sound]

$ lake env lean pincheck.lean   (check-file section 2 copied verbatim + one example per pin and per vocabulary def)
exit 0; examples in file: 18
pins instantiated: T2202_sum_SBgue_col T2202_continuity_argument T2202_ellT_eq_L T2202_norm_primBilGUE_le T2202_norm_primRhsGUE_le T2202_K_bootstrap T2202_finite_loopIdx T2202_eq736 T2202_eventually_small T2202_eventually_rpow_le_of_neg T2202_inst_bounds 
vocabulary rfl examples (SBgueV, primBilGUEV, primRhsGUEV, supOnV, rhs745GV, rhs746GV): 6

$ registry pre-check: import RBM3D + import RBM3D.Universality.GUEPhase.Bootstrap + #assert_rbm_axioms
exit 0
axiom audit: 6012 theorems, 2103 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
new names in registry output: 0

$ python3 declcmp.py  (source c9a24cf:Bootstrap.lean:47-645 with the import-map renamings by sed vs the port; changed lines per declaration)
in source only: ['eq736_detDom', 'stochDom_of_forall_highProb'] | in port only: ['sum_SBgue_col', 'sum_SBgue_row']
== ellT_eq_L 15
== primBilGUE 2
== GUEPhaseBootstrap_length_cutGlueL_le 5
== GUEPhaseBootstrap_length_cutGlueR_le 5
== norm_primBilGUE_le 36
== norm_primRhsGUE_le 5
== K_bootstrap 8
== eq736 10
== LoopSet 2
total changed lines 88
declarations identical after renaming: SBgue SBgue_apply continuity_argument primRhsGUE primBilGUE_add_left primBilGUE_add_right primRhsGUE_sub GUEPhaseBootstrap_two_le_length_cutGlueL GUEPhaseBootstrap_two_le_length_cutGlueR sum_pow_mul_pow finite_loopIdx eventually_small supOn supOn_le rhs745G rhs746G supOn_line1_le mul_le_of_eq730 sqrt_mul_sqrt_le supOn_nonneg inv_mul_pow eventually_rpow_le_of_neg

$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; diff --stat c9a24cf HEAD -- Bootstrap.lean
9e0f275
 RBM2D/Universality/GUEPhase/Bootstrap.lean | 901 +----------------------------
 1 file changed, 8 insertions(+), 893 deletions(-)

$ name-clash: git grep -nw <name> main -- RBM3D docs/tickets (excluding T2202 ticket/check), new public names
SBgue:0 SBgue_apply:0 sum_SBgue_col:0 sum_SBgue_row:0 continuity_argument:0 ellT_eq_L:0 primBilGUE:0 primRhsGUE:0 primBilGUE_add_left:0 primBilGUE_add_right:0 primRhsGUE_sub:0 norm_primBilGUE_le:0 norm_primRhsGUE_le:0 sum_pow_mul_pow:0 K_bootstrap:0 finite_loopIdx:0 eq736:0 LoopSet:0 eventually_small:0 supOn:0 supOn_le:0 rhs745G:0 rhs746G:0 supOn_line1_le:0 mul_le_of_eq730:0 sqrt_mul_sqrt_le:0 supOn_nonneg:0 inv_mul_pow:0 eventually_rpow_le_of_neg:0 BootstrapCheck:0 
$ git grep -nw sum_SBgue_col main -- RBM3D | head
```

Target statements (heads extracted from the file by `extract.py`; defs with bodies; one line each):
```
def SBgue : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun _ _ => ((L : ℂ) ^ d)⁻¹
@[simp] theorem SBgue_apply (a b : Zd d L) : SBgue d L a b = ((L : ℂ) ^ d)⁻¹
theorem sum_SBgue_col (b : Zd d L) : ∑ a : Zd d L, SBgue d L a b = 1
theorem sum_SBgue_row (a : Zd d L) : ∑ b : Zd d L, SBgue d L a b = 1
theorem continuity_argument {ι : Type*} {S : Set ι} (hS : S.Finite) {f g : ι → ℝ → ℝ} {t1 t0 : ℝ} (hf : ∀ i ∈ S, ContinuousOn (f i) (Icc t1 t0)) (hg : ∀ i ∈ S, ContinuousOn (g i) (Icc t1 t0)) (h0 : ∀ i ∈ S, f i t1 < g i t1) (hstep : ∀ t ∈ Icc t1 t0, (∀ u ∈ Icc t1 t, ∀ i ∈ S, f i u ≤ g i u) → ∀ i ∈ S, f i t < g i t) : ∀ t ∈ Icc t1 t0, ∀ i ∈ S, f i t < g i t
theorem ellT_eq_L {L : ℕ} {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ g ^ 2) : RBM.ellT L g t = L
def primBilGUE (W : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ := (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L, K (I.cutGlueL k l a) * SBgue d L a b * K' (I.cutGlueR k l b)
def primRhsGUE (W : ℕ) (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ := primBilGUE d L W K K I
theorem primBilGUE_add_left (W : ℕ) (K₁ K₂ K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : primBilGUE d L W (K₁ + K₂) K' I = primBilGUE d L W K₁ K' I + primBilGUE d L W K₂ K' I
theorem primBilGUE_add_right (W : ℕ) (K K₁ K₂ : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : primBilGUE d L W K (K₁ + K₂) I = primBilGUE d L W K K₁ I + primBilGUE d L W K K₂ I
theorem primRhsGUE_sub (W : ℕ) (Lf K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : primRhsGUE d L W Lf I - primRhsGUE d L W K I = primBilGUE d L W K (Lf - K) I + primBilGUE d L W (Lf - K) K I + primBilGUE d L W (Lf - K) (Lf - K) I
theorem norm_primBilGUE_le (W : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (B B' : ℕ → ℝ) (I : LoopIdx (Zd d L)) (hI : I.WF) (hB : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ B J.length) (hB' : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K' J‖ ≤ B' J.length) (hB0 : ∀ j, 0 ≤ B j) (hB0' : ∀ j, 0 ≤ B' j) : ‖primBilGUE d L W K K' I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) * ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B' j
theorem norm_primRhsGUE_le (W : ℕ) (K : LoopIdx (Zd d L) → ℂ) (B : ℕ → ℝ) (I : LoopIdx (Zd d L)) (hI : I.WF) (hB : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ B J.length) (hB0 : ∀ j, 0 ≤ B j) : ‖primRhsGUE d L W K I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) * ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B j
theorem sum_pow_mul_pow (c x : ℝ) (m : ℕ) : ∑ j ∈ Finset.Icc 2 m, (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1)) = ((m - 1 : ℕ) : ℝ) * c ^ 2 * x ^ m
theorem K_bootstrap {ι : Type*} {S : Set ι} (hS : S.Finite) (len : ι → ℕ) {n : ℕ} (hlen : ∀ i ∈ S, 2 ≤ len i ∧ len i ≤ n) (k dk : ℝ → ι → ℂ) {t1 t0 C N A ε : ℝ} (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t) (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u) (hlamc : ContinuousOn lam (Icc t1 t0)) (hderiv : ∀ t ∈ Icc t1 t0, ∀ i ∈ S, HasDerivWithinAt (fun s => k s i) (dk t i) (Icc t1 t0) t) (hd : ∀ t ∈ Icc t1 t0, ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → (∀ j ∈ S, ‖k t j‖ ≤ B (len j)) → ∀ i ∈ S, ‖dk t i‖ ≤ C * N * ∑ j ∈ Finset.Icc 2 (len i), B (len i - j + 2) * B j) (hC : 0 ≤ C) (hN : 0 ≤ N) (hA : 0 < A) (hinit : ∀ i ∈ S, ‖k t1 i‖ ≤ A * (lam t1)⁻¹ ^ (len i - 1)) (hsmall : ∀ t ∈ Icc t1 t0, N * (t - t1) ≤ ε * lam t) (hε : 4 * C * n * A * ε < 1) : ∀ t ∈ Icc t1 t0, ∀ i ∈ S, ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1)
theorem finite_loopIdx (d L : ℕ) [NeZero L] (n : ℕ) : {I : LoopIdx (Zd d L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}.Finite
theorem eq736 (d L W : ℕ) [NeZero L] (Kt : ℝ → LoopIdx (Zd d L) → ℂ) {n : ℕ} {t1 t0 A ε : ℝ} (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t) (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u) (hlamc : ContinuousOn lam (Icc t1 t0)) (hK : ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n → HasDerivWithinAt (fun s => Kt s I) (primRhsGUE d L W (Kt t) I) (Icc t1 t0) t) (hA : 0 < A) (hinit : ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n → ‖Kt t1 I‖ ≤ A * (lam t1)⁻¹ ^ (I.length - 1)) (hsmall : ∀ t ∈ Icc t1 t0, (((W * L) ^ d : ℕ) : ℝ) * (t - t1) ≤ ε * lam t) (hε : 4 * ((n : ℝ) ^ 2) * n * A * ε < 1) : ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n → ‖Kt t I‖ < 2 * A * (lam t)⁻¹ ^ (I.length - 1)
abbrev LoopSet (d L : ℕ) (n : ℕ) : Type := {I : LoopIdx (Zd d L) // I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}
theorem eventually_small {n : ℕ} {τ' τU : ℝ} (h : τ' < τU) : ∀ᶠ N : ℕ in atTop, 4 * ((n : ℝ) ^ 2) * n * (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) < 1
def supOn (g : ℝ → ℝ) (a b : ℝ) : ℝ := ⨆ u : Icc a b, g u
theorem supOn_le {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (h : ∀ u ∈ Icc a b, g u ≤ c) : supOn g a b ≤ c
def rhs745G (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n, ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t + (N * η t)⁻¹ ^ n + N * (t - t1) * supOn (fun u => Lm 2 u * Lm n u) t1 t + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t
def rhs746G (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n, ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t + (N * η t)⁻¹ ^ n + N * (t - t1) * supOn (fun u => Dm 1 u * Lm (n + 1) u) t1 t + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * n) u)) t1 t
theorem supOn_line1_le {Dm : ℕ → ℝ → ℝ} {n : ℕ} {t c x : ℝ} (e : ℕ) (he : e ≤ 1) (ht1t : t1 ≤ t) (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x) (hD : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n → 0 ≤ Dm j u ∧ Dm j u ≤ c * x ^ (j - 1 + e)) : supOn (fun u => ∑ k ∈ Finset.Icc 2 n, ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t ≤ n * ((1 + c) * c * x ^ (n + e))
theorem mul_le_of_eq730 {t ε y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) (hsm : t - t1 ≤ ε * η t) : N * (t - t1) * y ≤ ε * ((N * η t)⁻¹)⁻¹ * y
theorem sqrt_mul_sqrt_le {t ε : ℝ} (hN : 0 < N) (hηt : 0 < η t) (ht1t : t1 ≤ t) (hsm : t - t1 ≤ ε * η t) : Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) ≤ Real.sqrt (ε * (N * η t)⁻¹)
theorem supOn_nonneg {g : ℝ → ℝ} {a b : ℝ} (h : ∀ u ∈ Icc a b, 0 ≤ g u) : 0 ≤ supOn g a b
theorem inv_mul_pow {x : ℝ} (hx : x ≠ 0) {n : ℕ} (hn : 1 ≤ n) : x⁻¹ * x ^ n = x ^ (n - 1)
theorem eventually_rpow_le_of_neg {a ρ : ℝ} (ha : a < 0) (hρ : 0 < ρ) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ ρ
```

Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.BootstrapCheck`; `d = 3`, `L = 3`, `W = 2`, `N = 216`; statements extracted by script; each theorem is proved by applying the target at the concrete data, no deterministic hypothesis left open; built by the `lake build` above):
```
def loopThree : LoopIdx (Zd 3 3) := ⟨[true, false, true], [fun _ => 0, fun _ => 1, fun _ => 2]⟩
theorem loopThree_WF : loopThree.WF
theorem loopThree_length : loopThree.length = 3
theorem primBilGUE_zero_left (d L W : ℕ) [NeZero L] (K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : primBilGUE d L W (fun _ => 0) K' I = 0
theorem primRhsGUE_zero (d L W : ℕ) [NeZero L] (I : LoopIdx (Zd d L)) : primRhsGUE d L W (fun _ => 0) I = 0
theorem inst_sum_SBgue_col : ∑ a : Zd 3 3, SBgue 3 3 a 0 = 1
theorem inst_sum_SBgue_row : ∑ b : Zd 3 3, SBgue 3 3 0 b = 1
theorem inst_continuity_argument : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ ({1, 2} : Set ℕ), (fun (i : ℕ) (_ : ℝ) => (i : ℝ)) i t < (fun (i : ℕ) (_ : ℝ) => (i : ℝ) + 1) i t
theorem inst_K_bootstrap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ ({0} : Set ℕ), ‖(fun (_ : ℝ) (_ : ℕ) => (1 / 100 : ℂ)) t i‖ < 2 * (1 : ℝ) * ((fun _ : ℝ => (16 : ℝ)) t)⁻¹ ^ ((fun _ : ℕ => 2) i - 1)
theorem inst_norm_primBilGUE_le_zero : ‖primBilGUE 3 3 2 (fun _ => 0) (fun _ => 0) loopThree‖ ≤ (loopThree.length : ℝ) ^ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) * ∑ j ∈ Icc 2 loopThree.length, (fun _ : ℕ => (1 : ℝ)) (loopThree.length - j + 2) * (fun _ : ℕ => (1 : ℝ)) j
theorem inst_norm_primBilGUE_le_one : ‖primBilGUE 3 3 2 (fun _ => 1) (fun _ => 1) loopThree‖ ≤ (loopThree.length : ℝ) ^ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) * ∑ j ∈ Icc 2 loopThree.length, (fun _ : ℕ => (1 : ℝ)) (loopThree.length - j + 2) * (fun _ : ℕ => (1 : ℝ)) j
theorem inst_norm_primRhsGUE_le : ‖primRhsGUE 3 3 2 (fun _ => 1) loopThree‖ ≤ (loopThree.length : ℝ) ^ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) * ∑ j ∈ Icc 2 loopThree.length, (fun _ : ℕ => (1 : ℝ)) (loopThree.length - j + 2) * (fun _ : ℕ => (1 : ℝ)) j
theorem inst_eq736 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ I : LoopIdx (Zd 3 3), I.WF → 2 ≤ I.length → I.length ≤ 2 → ‖(fun (_ : ℝ) (_ : LoopIdx (Zd 3 3)) => (0 : ℂ)) t I‖ < 2 * (1 : ℝ) * ((fun _ : ℝ => (40000 : ℝ)) t)⁻¹ ^ (I.length - 1)
theorem inst_ellT_eq_L : RBM.ellT 4 (1 / 2) (63 / 64) = 4
theorem inst_finite_loopIdx : {I : LoopIdx (Zd 3 3) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ 4}.Finite ∧ loopThree ∈ {I : LoopIdx (Zd 3 3) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ 4}
theorem inst_eventually_small : ∀ᶠ N : ℕ in atTop, 4 * (((2 : ℕ) : ℝ) ^ 2) * ((2 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) < 1
theorem inst_eventually_rpow_le_of_neg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 : ℝ) ≤ 1 / 2
theorem inst_sum_pow_mul_pow : ∑ j ∈ Finset.Icc 2 4, ((3 : ℝ) * 2 ^ (4 - j + 2 - 1)) * (3 * 2 ^ (j - 1)) = ((4 - 1 : ℕ) : ℝ) * 3 ^ 2 * 2 ^ 4
theorem inst_supOn_le : supOn (fun u => u) 0 1 ≤ 1
theorem inst_supOn_nonneg : 0 ≤ supOn (fun u => u) 0 1
theorem inst_inv_mul_pow : (2 : ℝ)⁻¹ * 2 ^ 3 = 2 ^ (3 - 1)
theorem inst_mul_le_of_eq730 : (216 : ℝ) * (1 / 2 - 0) * 1 ≤ 1 * ((216 * (fun _ : ℝ => (1 : ℝ)) (1 / 2))⁻¹)⁻¹ * 1
theorem inst_sqrt_mul_sqrt_le : Real.sqrt (1 / 2 - 0) * Real.sqrt ((216 : ℝ)⁻¹ * ((fun _ : ℝ => (1 : ℝ)) (1 / 2))⁻¹ ^ 2) ≤ Real.sqrt (1 * (216 * (fun _ : ℝ => (1 : ℝ)) (1 / 2))⁻¹)
theorem inst_supOn_line1_le : supOn (fun u => ∑ k ∈ Finset.Icc 2 3, (((216 : ℝ) * (fun _ : ℝ => (1 : ℝ)) u)⁻¹ ^ (k - 1) + (fun (j : ℕ) (_ : ℝ) => ((1 / 216 : ℝ)) ^ (j - 1 + 1)) k u) * (fun (j : ℕ) (_ : ℝ) => ((1 / 216 : ℝ)) ^ (j - 1 + 1)) (3 - k + 2) u) 0 1 ≤ ((3 : ℕ) : ℝ) * ((1 + 1) * 1 * (1 / 216 : ℝ) ^ (3 + 1))
theorem inst_bounds : (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 - 0) ≤ 1 / 100 * 40000 ∧ 4 * ((2 : ℝ) ^ 2) * 2 * 1 * (1 / 100) < 1 ∧ (4 : ℝ) ^ 2 * (1 - 63 / 64) ≤ (1 / 2) ^ 2
def kTight (t : ℝ) : ℝ := (1 / 7000) / (1 - 216 / 7000 * t)
theorem kTight_hasDerivAt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt kTight (216 * kTight t ^ 2) t
theorem primRhsGUE_const_len_two (c : ℂ) (I : LoopIdx (Zd 3 3)) (hI : I.length = 2) : primRhsGUE 3 3 2 (fun _ => c) I = 216 * c ^ 2
theorem kTight_zero : kTight 0 = 1 / 7000
theorem kTight_one : kTight 1 = 1 / 6784
theorem inst_eq736_tight : ∀ t ∈ Icc (0 : ℝ) 1, ∀ I : LoopIdx (Zd 3 3), I.WF → 2 ≤ I.length → I.length ≤ 2 → ‖(fun (t : ℝ) (_ : LoopIdx (Zd 3 3)) => (kTight t : ℂ)) t I‖ < 2 * (1 : ℝ) * ((fun _ : ℝ => (7000 : ℝ)) t)⁻¹ ^ (I.length - 1)
```

Narrative (facts from the outputs above):
- All targets 1-7 of the ticket are proved in the one new file (863 lines): 29 public declarations = the 27 live declarations of RBM2D `Bootstrap.lean` at `c9a24cf` plus `sum_SBgue_col`, `sum_SBgue_row`. Not ported: `eq736_detDom`, `stochDom_of_forall_highProb` (`declcmp.py`: "in source only").
- `declcmp.py` compares the source `:47-645` after the import-map renamings (`Z2 L ↦ Zd d L`, `L ↦ d L`, `W^2 ↦ W^d`, `wf_cutGlue*` argument order, `Path.ellT ↦ RBM.ellT`) with the port, per declaration: 22 of 31 declarations identical, 9 changed (88 lines). The changes are: `ellT_eq_L` (coupling `g`, `0 ≤ g`, `L²(1−t) ≤ g²`, floor `1`: new proof), `primBilGUE` (`W^d`), `norm_primBilGUE_le`/`norm_primRhsGUE_le`/`eq736` (`(W L)^d`, `L^d` for the double sum, `card_Zd` instead of `Fintype.card_prod`/`ZMod.card`), the two private `_le` length helpers (now one-line uses of the merged `LoopIdx.length_cutGlueL_le/R_le`), `K_bootstrap` (drift renamed `dk`, as in the check file), `LoopSet` (`d L`).
- The `d`-dependence is only `SBgue` (`L^{-d}`), `W^d` in `primBilGUE` and `N = (W L)^d`; no `3 ≤ d` is used (grep above: only a docstring line). The scalar lemmas and the continuity argument are verbatim.
- The 11 pins and 6 vocabulary `rfl` equalities of the check file compile against the library (`pincheck.lean`, exit 0); `continuity_argument` and `K_bootstrap` are instanced as `@name.{0}` (check file has `ι : Type`).
- Instances: 31 declarations in `BootstrapCheck`, 21 of them `inst_*` theorems (all targets of the ticket's instance list, plus `sum_SBgue_row`, `norm_primRhsGUE_le`, `sum_pow_mul_pow`, `supOn_le`, `supOn_nonneg`, `supOn_line1_le`, `mul_le_of_eq730`, `sqrt_mul_sqrt_le`, `inv_mul_pow`, `eventually_rpow_le_of_neg`). Beyond the ticket: `inst_eq736_tight`, `eq736` at the nonzero solution `K(t) = K₀/(1 − N K₀ t)`, `K₀ = 1/7000`, `λ ≡ 7000`, `ε = 216/7000` (`4 n³ A ε = 0.987`, `kTight_one : K(1) = 1/6784`), next to `inst_eq736` at `K ≡ 0`. No instance for `SBgue_apply`, `primBilGUE_add_left/right`, `primRhsGUE_sub` (not in the ticket's list).
- Imports: the ticket's four `RBM3D` modules and `Mathlib.Data.Set.Finite.List`, plus Mathlib `Analysis.Calculus.MeanValue` (home of `norm_image_sub_le_of_norm_deriv_le_segment'`, used by `K_bootstrap`) and, for `inst_eq736_tight` only, `Analysis.Calculus.Deriv.Inv`, `Analysis.Complex.RealDeriv`. No `RBM3D` root import.
- `RBM3D/Test/Axioms.lean` is not edited: the registry pre-check exits 0 and lists no new name (count 0 above); `git diff --stat main...t/T2202` lists only the writable file. Interface rule: every stem as pinned, no `gueBootstrap_` rename, no name clash (grep above: 0 hits for 29 names and `BootstrapCheck`).
- Special case (CLAUDE.md §5.6): `primBilGUE`/`primRhsGUE` are the GUE-profile equation (7.33) only, not the band-profile `treeEqRhs`; no bridge lemma (not a target). `rhs745G`/`rhs746G` take an abstract `N`.
- The `d ≥ 3` limit bookkeeping of the ticket's preflight (iv) is section (a) rows 13-14 and flags F1-F3 (not repeated); this file has no limit hypothesis besides `∀ᶠ N` in `eventually_small` and `eventually_rpow_le_of_neg`.

## (c) Verified Mathlib names (`#check` in scratch `mathlib_names.lean`: 30 names, no error)
- `norm_image_sub_le_of_norm_deriv_le_segment'` (`Analysis/Calculus/MeanValue.lean:326`); `List.finite_length_le`; `Set.Finite.isClosed_biUnion`; `IsClosed.isClosed_le`; `IsClosed.csInf_mem`; `ContinuousWithinAt.closure_le`; `closure_Ico`.
- `ciSup_le`; `Real.iSup_nonneg`; `Real.sqrt_pos`; `Real.sq_sqrt`; `Real.sqrt_mul`; `Real.sqrt_le_sqrt`; `pow_le_pow_iff_left₀`; `abs_of_pos`; `le_div_iff₀`; `inv_anti₀`; `pow_le_pow_left₀`; `pow_le_pow_of_le_one`; `ContinuousOn.inv₀`; `Finset.single_le_sum`; `Nat.card_Icc`; `Nat.card_Ioc`; `tendsto_rpow_atTop`; `hasDerivWithinAt_const`; `HasDerivAt.hasDerivWithinAt`.
- `HasDerivAt.inv` (`Analysis/Calculus/Deriv/Inv.lean:111`), `HasDerivAt.ofReal_comp` (`Analysis/Complex/RealDeriv.lean:102`), `HasDerivAt.const_mul`, `HasDerivAt.const_sub`. Not in scope without their imports: `HasDerivAt.inv` fails to resolve until `Mathlib.Analysis.Calculus.Deriv.Inv` is imported (error in scratch `tight.lean`).
- Verified absent at root: Mathlib has no `inv_mul_pow`, `sqrt_mul_sqrt_le`, `sum_pow_mul_pow`, `supOn` (`grep -rnw` over `.lake/packages/mathlib/Mathlib`, 0 hits).

## (d) Open issues and paper-delta candidates
- No open issue blocks the audit. Flags F1-F3 of (a) (consumer windows, `τ_U` values, size of `N` for `eventually_small`) are for the dispatcher and the consumers UN-31/48/49/50.
- `T2202a` (paper delta, same as the ticket's): (7.30) ⟹ `ℓ_{t₁} = L` for the merged `ellT` with coupling and floor: `ellT_eq_L : 0 ≤ g → t < 1 → L²(1 − t) ≤ g² → ellT L g t = L` (RBM2D/[YY_25]: `L²(1 − t) ≤ 1`, no coupling, no floor); `0 ≤ g` and `t < 1` needed (counterexamples in (a)).
- `T2202b` (paper delta): the `d ≥ 3` form of (7.33)-(7.36) of the GUE phase, not spelled out in the paper (`1_2_Intro_model_result.tex:566-570` refers to [YY_25] for `d = 1` and [DYYY25] for `d = 2`): `S^{(B)}_{GUE} = L^{-d}`, prefactor `W^d`, power counting `n² N`, `N = (W L)^d`.
- `T2202c` (bookkeeping, not a statement difference): `N η_{t₁} ≤ g² W^d L^{d-2} Im m` at the largest admissible `1 − t₁ = g²/L²` (`d = 2`: `g² W²`); table in (a), `log_N ∈ [0.6975, 0.8272]`.
- `T2202d` (Lean structure, not a paper delta): `eq736_detDom`, `eq728G`, `eq727GE` not ported (dead in RBM2D after T2274; UN-26b gives the size-scale forms); UN-26 split a/b by imports; `eq736` carries explicit `(d L W)`; `K_bootstrap`'s drift is `dk`.
- `T2202e` (Lean structure, not a paper delta): three Mathlib imports beyond the ticket's list (see narrative); the sole-file scope is unchanged.
