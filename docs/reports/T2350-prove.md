Prover model: claude-sonnet-5-5
## (a) Math preflight — Thu Oct  8 23:08:57 UTC 2026

Target mathematics (UN-44): the 2-loop algebra `W^d Σ_{a,b∈Z_L^d} K(a,·) SBgue_{ab} K'(·,b)` with `SBgue_{ab} = L^{-d}`; one grid step of `K̃` on 2-loops (`‖K̃_u+Δ ∂_tK̃_u−K̃_{u+Δ}‖ ≤ 3N²Δ²`); Duhamel in expectation; one step of `‖e_{k+1}‖ ≤ (1+2NρΛΔ)‖e_k‖_max + eq729c`, `N=(WL)^d`. Source: RBM2D `Universality/GUEPhase/Eq729A.lean` (1043 lines, RBM2D HEAD 9e0f275).

### (i) Exponent table

Token census of the source (command and output). The file has 82 `^ 2` tokens: 42 are d-dependent (W:11, L:17, (WL):12, W⁻¹:1 listed + 1 at source line 342 written `((d.W n : ℝ))⁻¹ ^ 2`, not matched by that regex), 40 are d-free (Λ²:23, N²:11, M²:2, Δ²:3, and the outer `^ 2` of `3·N^2·Δ^2` at line 552, unmatched); plus one `pow_pos … 2` (line 738, d-dependent, not a `^` token). The ticket's "109" is not what this count gives.
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2350/tok.py
lines: 1043  '^ 2' tokens: 82
 11  (W:C/R)^2  -> (W)^d
 17  (L:R)^2 [=|Z2 L|]-> (L)^d
 12  ((W*L)^2:N) -> ((W*L)^d:N)
  1  (W:R)^-1 ^2 -> ((W)^d)^-1
  1  pow_pos (W*L>0) 2 -> d
 23  (rho*Lambda^2) etc: Lambda^2 [d-free]
 11  N^2 [loop length 2, d-free]
  2  M^2 [=N^2, d-free]
  3  Delta^2 [d-free]
N^3: 8 N^4: 3 (3-loop bound; envConst literal N^4: both d-free)  Z2: 79  d.size n: 7
```

| quantity | d = 2 source | d-form (this ticket) | constraint / reason | slack at the instance (d=3, L=4, W=32) |
|---|---|---|---|---|
| prefactor in primBilGUE, egtNGUE (11 tokens) | `W^2` | `W^d` | `Vtx = Zd d L × Fin (W^d)`; primBilGUE/egtNGUE carry `(W:ℂ)^d` | `W^d = 32768` |
| `SBgue_{ab}` (17 tokens, norm `(L^2)⁻¹`) | `1/L^2` | `1/L^d` (`SBgue_apply`: `((L:ℂ)^d)⁻¹`) | `\|Z_L^d\| = L^d` | `L^d = 64` |
| 2-loop double sum | `W²·L⁴·L⁻² = (WL)²` | `W^d·(L^d)²·L^{-d} = (WL)^d = N` | exact identity (script A: brute force at d=3, L=3, W=2, c=1/7) | equality, 0 loss |
| `N` (12 tokens `((W*L)^2:ℕ)`, `d.size n`) | `(WL)²` | `(WL)^d = sz.size n` | `N ≥ 1` (`W>0`, `L≥3`) | `N = 2097152`, `N−1` |
| norm of primBil on a 2-loop | `≤ Nαβ` | `≤ Nαβ` (same) | needs `‖K‖≤α`, `‖K'‖≤β` entrywise on the two sections | tight for constant family (script B last line) |
| crude loop bound (1+1 tokens) | `(LW)²(η⁻¹(W⁻¹)²)^ℓ`, `(W⁻¹)²≤1` | `(LW)^d(η⁻¹(W^d)⁻¹)^ℓ`, `(W^d)⁻¹≤1` | integrability only; `W^d ≥ 1` | `(W^d)⁻¹ = 3.05e-5 ≤ 1` |
| loop-length powers `N^1,N^2,N^3` (11 `N^2`, 2 `M^2`, 8 `N^3`) | `N^ℓ` | same, d-free | `‖𝓛_I‖ ≤ (η⁻¹)^ℓ ≤ N^ℓ`, from `η_s⁻¹ ≤ N` on `[t₁,t₀]` | `η(t₀)⁻¹ = 10 ≤ N`: slack `N−10` |
| `η_s⁻¹ ≤ N` on `[t₁,t₀]` | `Λ=(Nη(t₀))⁻¹≤1` | same | `η_s ≥ η(t₀)`, `s ≤ t₀`; `Nη(t₀) ≥ 1` | `Nη(t₀) = 209715.2` |
| `ρΛ ≤ 1`, `ρΛ² ≤ 1` | – | same | `ρ ≤ Nη(t₀)` | `ρ = 1`, max `209715.2` |
| Kdisc remainder `3N²Δ²` (3 terms `N·(NΔ)`) | `3N²Δ²`, `N=(WL)²` | `3N²Δ²`, `N=(WL)^d` | `NΔ ≤ 1` (`hMΔ`), `b2 ≤ 1` | `NΔ = 0.920514`; min `K = 92052` |
| envelope `16(k+3)^4 N^4(1+η⁻¹)^{k+4}` at `k=2` | `10000 N⁴(1+η⁻¹)⁶` | same literal, `N=(WL)^d` | `η⁻¹ ≤ N ⇒ ≤ 10000 N⁴(1+N)⁶` | `16·5⁴ = 10000` exact |
| Δ-exponent of Duhamel | `Δ^{3/2}` | `Δ^{3/2}` | d-free | – |
| `eq729c(N,ρ,Λ,p,Δ)` | 3 groups: `Δ·N(…)`, `10000N⁴(1+N)⁶Δ^{3/2}`, `3N²Δ²` | same formula, `N=(WL)^d` | bounds `‖F−K‖≤2N²` (2-loop), `≤2N³` (3-loop), `‖F_{1-loop}−m‖≤2N`; use `N^ℓ≥1`, `ρΛ≤1` | pieces finite at the instance (script C) |
| cut structure on a 2-loop | one cut `(k,l)=(1,2)`; two `𝓔^{(G̃)}` edges `k∈{1,2}` | same (list-level, d-free) | `cutGlueL 1 2 a ⟨[s₁,s₂],[a₁,a₂]⟩ = ⟨[s₁,s₂],[a,a₂]⟩`, `cutGlueR 1 2 b = ⟨[s₁,s₂],[a₁,b]⟩`, `cutGlue 1 b = ⟨[s₁,s₁,s₂],[b,a₁,a₂]⟩`, `cutGlue 2 b = ⟨[s₁,s₂,s₂],[a₁,b,a₂]⟩` (script A') | – |
| `1`-loop `primRhsGUE` | `0` (`Ioc 1 1 = ∅`) | `0` | d-free | – |
| time domain | `0≤t₁≤t₀<1` | same | `η_u>0` for `u<1`; `u_k ∈ [t₁,t₀]` for `k≤K` | `1−t₀ = 0.1` |

§29 fixed rows (one line each): (1) time domain `0 ≤ t₁ ≤ t₀ < 1` is an explicit hypothesis of `eq729_duhamel`/`eq729_one_step`; `eq729_Kdisc` only uses membership in `[t₁,t₀]`. (2) not applicable: GUE phase has no coupling `ilambda` (`SBgue = L^{-d}`). (3) no relation `L^d ≤ W^K` is used: only `N=(WL)^d`, `3 ≤ L` (for `NeZero L` and the pin `loopGenGUE`'s `hL`), `W>0`. (4) all statements are at one fixed `n` (no `∀ᶠ`); `Nη(t₀) ≥ 1` (`hΛ1`) and `NΔ ≤ 1` are hypotheses, not derived; the constants `3`, `10000`, `2` contain no `W`, `L`, `ilambda`.

### (ii) One concrete nondegenerate instance

Data: `d=3`, `sz0` of Grid.lean (`L=4`, `W=32`, `N=2097152`, Grid.lean:830), `n=0`, `E=0`, `t₁ = 0.9·e^{-1/20}`, `t₀ = 0.9` (the GridCheck times), `k=0`, grid size `K=100000` (the GridCheck `K=4` violates `NΔ ≤ 1`; `K` is a free argument; minimum `92052`). `ρ=1`, `Λ=(Nη(t₀))⁻¹`, `η(t₀) = (1−t₀)·Im m^{(0)} = 0.1` (`Im m^{(E)} = √(4−E²)/2 = 1`). Primitive family: `Kt s ⟨[s₁,s₂],[x,y]⟩ = c(s) = c₀/(1−N c₀(s−t₁))`, `c₀ = 10⁻⁶`, and `Kt s = 0` on 3-loops (and on other lengths). Then `primRhsGUE(Kt s)⟨[s₁,s₂],[x,y]⟩ = N c(s)²` (script A) `= c'(s)`, so `hKd` holds, and `hK2b` (`c ≤ ρΛ`), `hK3b` (`0 ≤ ρΛ²`) hold. Targets covered: `eq729_primBil2`/`eq729_norm_primBil2_le`/`eq729_norm_primRhs2_le` (data above, `α=β=c`), `eq729_Kdisc` (`u=t₁`, `Δ=(t₀−t₁)/K`, `b2=ρΛ`), `eq729_one_step` deterministic hypotheses (`hE, ht1, ht10, ht0, hΛ, hΛ1, hρ0, hρΛ, hp0, hMΔ, hK2b, hK3b, hKd, hk`; `hBk` with `Bk = N²+1`, which holds since `‖F_{2-loop}‖ ≤ N²`, `‖Kt‖ ≤ ρΛ ≤ 1`). `hX, hg1–hg3` are the stochastic inputs of the second half (`gueGrid_expect_oneLoop`, `GUEPathBounds.lk`); they stay hypotheses of the example (CLAUDE.md §4 step 2), with `B = univ`, `p = 1` (`Pgue B ≤ 1`) making `hg1–hg3` vacuous. `eq729_duhamel`'s hypothesis `hdrift` (integrability of `genMatGUE` along `gueH`) is a theorem of the same boundedness argument, not data.
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2350/inst.py
A: |Z_L^d| = 27  W^d*sum = 4.4081632653061224489795918367346938775510204081632653061224489795918367346938607  (WL)^d c^2 = 4.4081632653061224489795918367346938775510204081632653061224489795918367346938773  equal: True
A': cutGlue1 = (['s1', 's1', 's2'], ['b', 'a1', 'a2'])  cutGlue2 = (['s1', 's2', 's2'], ['a1', 'b', 'a2'])
A': cutGlueL(1,2) = (['s1', 's2'], ['a', 'a2'])  cutGlueR(1,2) = (['s1', 's2'], ['a1', 'b'])
B: Nη(t0) = 209715.2  max rho (rho*Lambda<=1) = 209715.2  Bk := N^2+1 = 4398046511105
B: N = 2097152  t1 = 0.856106482051  t0 = 0.9  K = 100000  Delta = 4.389352e-7
B: 0<=t1<=t0<1: True  k=0<K: True  |E|=0<2
B: Lambda = (N eta(t0))^-1 = 4.768372e-6  Lambda<=1: True  rho*Lambda<=1: True
B: N*Delta = 0.920514  <=1: True  minimal K = ceil(N (t0-t1)) = 92052
B: N*c0*(t0-t1) = 0.092051 (<1: no blow-up)
B: c(t1) = 1.000e-6  c(t0) = 1.101e-6  rho*Lambda = 4.768e-6  c<=rho*Lambda on [t1,t0]: True
B: ODE at s = 0.856106  c'(s) = 2.097152e-6  N c^2 = 2.097152e-6  rel.err = 4.4e-24
B: ODE at s = 0.900000  c'(s) = 2.543943e-6  N c^2 = 2.543943e-6  rel.err = 5.3e-24
B: Kdisc  |K_u + Delta*primRhs - K_{u+Delta}| = 8.473e-19  <= 3 N^2 Delta^2 = 2.542e+0 : True
B: u, u+Delta in [t1,t0]: True  b2 = rho*Lambda <= 1: True
B: primBil2 norm = N c(u)^2 = 2.097e-6  <= N*alpha*beta with alpha=beta=c(u): tight
C: 16*(2+3)^4 = 10000   eta(t0)^-1 = 1E+1  <= N: True
C: eq729c(N,rho,Lambda,p=1,Delta) = 4.785e+57  (finite; dominated by 10000 N^4 (1+N)^6 Delta^{3/2} = 4.785e+57 )
C: remainder term <= 1 needs Delta <=  1.546e-45  i.e. K >=  2.840e+43 (paper grid K=(N+1)^(32 n0+64); not a hypothesis of any target)
```
Reading of the output: every deterministic hypothesis holds with slack (`NΔ = 0.9205`, `Λ = 4.8e-6`, `c(t₀) = 1.10e-6 ≤ ρΛ = 4.77e-6`, no blow-up `Nc₀(t₀−t₁) = 0.092`); Kdisc's residual `8.5e-19` is far below `3N²Δ² = 2.5`. The conclusion of `eq729_one_step` at this `K` is a true but vacuous bound (`eq729c ≈ 4.8e57`, dominated by `10000N⁴(1+N)⁶Δ^{3/2}`); it needs `Δ ≲ 1.5e-45` to be `≤ 1`, i.e. the paper's grid `K=(N+1)^{32n₀+64}`, which is a proof device, not a hypothesis of any target. No `N=0`, empty index set, collapsed window (`t₀−t₁ = 0.0439`) or `False` premise occurs.
External-hypothesis limit check (TEAM §8 lesson 14): none of the targets has an external (cited-work) hypothesis; `hX`/`hg*` are in-paper stochastic inputs. 
### Verdicts
- All 17 targets (`eq729_primBil2, eq729_eG2, eq729_norm_primBil2_le, eq729_primRhs_one, eq729F, eq729_step_nonneg, eq729_KΔ, eq729_time_mem, eq729_eta_pos, eq729_eta_le, eq729_zt_im, eq729_duhamel, eq729_norm_primRhs2_le, eq729_Kdisc, eq729e, eq729c, eq729_one_step`): **PASS**. Every `d`-line closes with `N=(WL)^d`; the only changes are `W^2→W^d`, `L^2→L^d`, `(WL)^2→(WL)^d`, `(W⁻¹)²→(W^d)⁻¹`; `N^ℓ` and `3N²Δ²`, `10000N⁴(1+N)⁶Δ^{3/2}`, `eq729c` keep their form.
- Recommended instances for 1b (two targets, as the ticket asks): `eq729_Kdisc` and `eq729_norm_primBil2_le` (fully deterministic data above, `sz0`).
- The ticket's preflight items (ii) twin-name table and (iii) merged-signature table are name/signature checks, outside stage 1a's two-part scope; not done here.

### (a′) Preflight corrections — Thu Oct  8 23:34:39 UTC 2026
No mistake in (a) that changes a verdict was found; PASS stands.  Stage 1b used another concrete instance of the same constraints of (i): `t₁ = 17/20` (not `0.9 e^{-1/20}`), `t₀ = 9/10`, `K = 131072 = 2^17` (not 100000), `Bk = 50` (not `N²+1`; at `k = 0`, `η(t₁) = 3/20`).  Re-check by script (`N`, `η(t₀)`, `Λ` agree with (a)):
```
$ python3 -I scratchpad/T2350/inst2.py
N = 2097152  Delta = 1/2621440  N*Delta = 0.8  (<=1: True )
min K = ceil(N(t0-t1)) = 104858  K = 131072
eta(t0) = 0.1  Lambda = (N eta)^-1 = 4.76837158203125e-06  = 10/2097152: True
c(t1) = 1e-06  c(t0) = 1.1171406918050133e-06  2e-6 bound: True  c<=Lambda: True
den min = 1 - N c0 (t0-t1) = 0.8951424  >= 1/2: True
Kdisc: |K_u + D*primRhs - K_{u+D}| = 6.400005120004096e-19  <= 3 N^2 D^2 = 1.92 : True
ODE c' = N c^2 at t1: c'(t1) = c0*N*c0/den^2 = 2.097152e-06  N c(t1)^2 = 2.097152e-06
hBk: eta(t1) = 0.15  (1/eta(t1))^2 = 44.44444444444444  +1 = 45.44444444444444  <= 50: True
envelope literal 16*(2+3)^4 = 10000
rho*Lambda<=1: True  Lambda<=1: True
eq729c(N,1,Lam,p=1,Delta) = 3.877e+57  (Delta-term 1.857e+26, 10000 N^4(1+N)^6 Delta^1.5 = 3.877e+57, 3N^2Delta^2 = 1.920e+00)
```

## (b) Script output
```
$ for h in $(git log --reverse --format=%h main..t/T2350); do git show $h:RBM3D/Universality/GUEPhase/Eq729A.lean | wc -l; done | tr '\n' ' '   # stop size 1600
697 1062 1326 1417 1417   (commits 4a846fd 558976d 3c0fc5a d2ff84c 8b1f52a )
$ lake build RBM3D.Universality.GUEPhase.Eq729A   # Thu Oct  8 23:27:44 UTC 2026
Build completed successfully (3774 jobs).   [exit=0; warnings from the new file: 0]
$ lake build   # full library, Thu Oct  8 23:28:30 UTC 2026  (the module is not yet imported by RBM3D.lean; the hub adds it at merge)
Build completed successfully (4161 jobs).   [exit=0]
$ printf 'import RBM3D\nimport RBM3D.Universality.GUEPhase.Eq729A\n\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean   # Thu Oct  8 23:27:46 UTC 2026
axiom audit: 10454 theorems, 3069 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
[exit=0]
$ lake env lean ax.lean   # #print axioms of every public declaration below (Thu Oct  8 23:26:44 UTC 2026); the lines below summarize its output by script
  26  [propext, Classical.choice, Quot.sound]   (26 lines of 26; none other)
  targets: eq729_primBil2, eq729_eG2, eq729_norm_primBil2_le, eq729_primRhs_one, eq729F, eq729_step_nonneg, eq729_KΔ, eq729_time_mem, eq729_eta_pos, eq729_eta_le, eq729_zt_im, eq729_duhamel, eq729_norm_primRhs2_le, eq729_Kdisc, eq729e, eq729c, eq729_one_step
  instances: Eq729AInst.eq729_Kdisc_check, Eq729AInst.eq729_norm_primBil2_le_check, Eq729AInst.eq729_one_step_check, Eq729AInst.eq729_duhamel_check, Eq729AInst.eq729_primBil2_check, Eq729AInst.eq729_primRhs_one_check, Eq729AInst.eq729_norm_primRhs2_le_check, Eq729AInst.eq729_eG2_check, Eq729AInst.eq729_grid_facts_check
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/GUEPhase/Eq729A.lean  ->  0      $ git diff --stat main...t/T2350 | tail -2
 RBM3D/Universality/GUEPhase/Eq729A.lean | 1417 +++++++++++++++++++++++++++++++
 1 file changed, 1417 insertions(+)
```
**Targets**, extracted from the file by `stmts.py` (`line: statement up to :=`, whitespace collapsed):
```
52: theorem eq729_primBil2 (d L W : ℕ) [NeZero L] (K K' : LoopIdx (Zd d L) → ℂ) (s1 s2 : Bool) (a1 a2 : Zd d L) : primBilGUE d L W K K' ⟨[s1, s2], [a1, a2]⟩ = (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L, K ⟨[s1, s2], [a, a2]⟩ * SBgue d L a b * K' ⟨[s1, s2], [a1, b]⟩
80: theorem eq729_eG2 (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (s1 s2 : Bool) (a1 a2 : Zd d L) : egtNGUE d L W E u M ⟨[s1, s2], [a1, a2]⟩ = (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L, ((loopL d L W (blockMat d L W M) (zt E u) ⟨[s1], [a]⟩ - mSigma E s1) * SBgue d L a b * loopL d L W (blockMat d L W M) (zt E u) ⟨[s1, s1, s2], [b, a1, a2]⟩ + (loopL d L W (blockMat d L W M) (zt E u) ⟨[s2], [a]⟩ - mSigma E s2) * SBgue d L a b * loopL d L W (blockMat d L W M) (zt E u) ⟨[s1, s2, s2], [a1, b, a2]⟩)
132: theorem eq729_norm_primBil2_le (d L W : ℕ) [NeZero L] (K K' : LoopIdx (Zd d L) → ℂ) (s1 s2 : Bool) (a1 a2 : Zd d L) {α β : ℝ} (hA : ∀ x, ‖K ⟨[s1, s2], [x, a2]⟩‖ ≤ α) (hB : ∀ y, ‖K' ⟨[s1, s2], [a1, y]⟩‖ ≤ β) : ‖primBilGUE d L W K K' ⟨[s1, s2], [a1, a2]⟩‖ ≤ (((W * L) ^ d : ℕ) : ℝ) * α * β
141: theorem eq729_primRhs_one (d L W : ℕ) [NeZero L] (K : LoopIdx (Zd d L) → ℂ) (s : Bool) (a : Zd d L) : primRhsGUE d L W K ⟨[s], [a]⟩ = 0
275: def eq729F (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (n k : ℕ) (ω : PathΩ sz) (I : LoopIdx (Zd d (sz.L n))) : ℂ
283: theorem eq729_step_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (ht10 : t1 n ≤ t0 n) : 0 ≤ gridStep t1 t0 K n
293: theorem eq729_KΔ {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hK : K n ≠ 0) : (K n : ℝ) * gridStep t1 t0 K n = t0 n - t1 n
300: theorem eq729_time_mem {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} (ht10 : t1 n ≤ t0 n) (hK : K n ≠ 0) (hk : k ≤ K n) : gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n)
313: theorem eq729_eta_pos {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) : 0 < etaT E u
317: theorem eq729_eta_le {E : ℝ} (hE : |E| < 2) {u t : ℝ} (hut : u ≤ t) : etaT E t ≤ etaT E u
322: theorem eq729_zt_im (E u : ℝ) : (zt E u).im = etaT E u
378: theorem eq729_duhamel {d : ℕ} (sz : Sizes d) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n : ℕ} (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) {k : ℕ} (hk : k < K n) {J : LoopIdx (Zd d (sz.L n))} (hwf : J.WF) (hdrift : Integrable (fun ω => genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n k) (gueH sz t1 t0 K n k ω) J) (Pgue sz)) : ‖(∫ ω, eq729F sz t1 t0 K E n (k + 1) ω J ∂(Pgue sz)) - (∫ ω, eq729F sz t1 t0 K E n k ω J ∂(Pgue sz)) - (gridStep t1 t0 K n : ℂ) * ∫ ω, genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n k) (gueH sz t1 t0 K n k ω) J ∂(Pgue sz)‖ ≤ envConst d (sz.L n) (sz.W n) (E n) J.length (gridTime t1 t0 K n (k + 1)) * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)
555: theorem eq729_norm_primRhs2_le (K : LoopIdx (Zd d L) → ℂ) {b : ℝ} (hb : ∀ s1 s2 x y, ‖K ⟨[s1, s2], [x, y]⟩‖ ≤ b) (s1 s2 : Bool) (a1 a2 : Zd d L) : ‖primRhsGUE d L W K ⟨[s1, s2], [a1, a2]⟩‖ ≤ (((W * L) ^ d : ℕ) : ℝ) * b * b
562: theorem eq729_Kdisc (Kf : ℝ → LoopIdx (Zd d L) → ℂ) {t1 t0 u Δ b2 : ℝ} (hu : u ∈ Set.Icc t1 t0) (hu' : u + Δ ∈ Set.Icc t1 t0) (hΔ : 0 ≤ Δ) (hb2 : b2 ≤ 1) (hMΔ : (((W * L) ^ d : ℕ) : ℝ) * Δ ≤ 1) (hKb : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, ‖Kf s ⟨[s1, s2], [x, y]⟩‖ ≤ b2) (hKd : ∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kf s ⟨[s1, s2], [x, y]⟩) (primRhsGUE d L W (Kf s) ⟨[s1, s2], [x, y]⟩) (Set.Icc t1 t0) s) (s1 s2 : Bool) (a1 a2 : Zd d L) : ‖Kf u ⟨[s1, s2], [a1, a2]⟩ + (Δ : ℂ) * primRhsGUE d L W (Kf u) ⟨[s1, s2], [a1, a2]⟩ - Kf (u + Δ) ⟨[s1, s2], [a1, a2]⟩‖ ≤ 3 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2
717: def eq729e {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n k : ℕ) (I : LoopIdx (Zd d (sz.L n))) : ℂ
723: def eq729c (N ρ Λ p Δ : ℝ) : ℝ
731: theorem eq729_one_step {d : ℕ} (sz : Sizes d) {t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) {E : ℕ → ℝ} {n : ℕ} (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) {Λ ρ p Bk : ℝ} (hΛ : Λ = (((sz.size n : ℕ) : ℝ) * etaT (E n) (t0 n))⁻¹) (hΛ1 : Λ ≤ 1) (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p) (hMΔ : ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1) (hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ) (hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w, ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2) (hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩) (Set.Icc (t1 n) (t0 n)) s) {k : ℕ} (hk : k < K n) (hX : ∀ a, ‖(∫ ω, eq729F sz t1 t0 K E n k ω ⟨[true], [a]⟩ ∂(Pgue sz)) - mE (E n)‖ ≤ ρ * Λ ^ 2) {B : Set (PathΩ sz)} (hB : Pgue sz B ≤ ENNReal.ofReal p) (hg1 : ∀ ω ∉ B, ∀ σ a, ‖eq729F sz t1 t0 K E n k ω ⟨[σ], [a]⟩ - mSigma (E n) σ‖ ≤ ρ * Λ) (hg2 : ∀ ω ∉ B, ∀ s1 s2 x y, ‖eq729F sz t1 t0 K E n k ω ⟨[s1, s2], [x, y]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2) (hg3 : ∀ ω ∉ B, ∀ s1 s2 s3 x y w, ‖eq729F sz t1 t0 K E n k ω ⟨[s1, s2, s3], [x, y, w]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3) (hBk : ∀ s1 s2 x y, ‖eq729e sz t1 t0 K E Kt n k ⟨[s1, s2], [x, y]⟩‖ ≤ Bk) (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)) : ‖eq729e sz t1 t0 K E Kt n (k + 1) ⟨[s1, s2], [a1, a2]⟩‖ ≤ (1 + gridStep t1 t0 K n * (2 * ((sz.size n : ℕ) : ℝ) * (ρ * Λ))) * Bk + eq729c ((sz.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n)
```
**Instances** (namespace `RBM.Univ.GUEPhase.Eq729AInst`, same file, compiled in the build above; statements cut at 300 characters):
```
1201: theorem eq729_Kdisc_check (s1 s2 : Bool) (a1 a2 : Zd 3 (sz0.L 0)) : ‖Eq729AInst_Kt (sz0.L 0) (17 / 20) ⟨[s1, s2], [a1, a2]⟩ + ((1 / 2621440 : ℝ) : ℂ) * primRhsGUE 3 (sz0.L 0) (sz0.W 0) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) ⟨[s1, s2], [a1, a2]⟩ - Eq729AInst_Kt (sz0.L 0) (17 / 20 + 1 / 2621440) ⟨[
1218: theorem eq729_norm_primBil2_le_check : ‖primBilGUE 3 (sz0.L 0) (sz0.W 0) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) ⟨[true, false], [0, 1]⟩‖ ≤ (((sz0.W 0 * sz0.L 0) ^ 3 : ℕ) : ℝ) * (1 / 1000000) * (1 / 1000000)
1283: theorem eq729_one_step_check {p : ℝ} (hp0 : 0 ≤ p) {B : Set (PathΩ sz0)} (hX : ∀ a, ‖(∫ ω, eq729F sz0 Eq729AInst_t1 Eq729AInst_t0 Eq729AInst_K Eq729AInst_E 0 0 ω ⟨[true], [a]⟩ ∂(Pgue sz0)) - mE (Eq729AInst_E 0)‖ ≤ 1 * (10 / 2097152) ^ 2) (hB : Pgue sz0 B ≤ ENNReal.ofReal p) (hg1 : ∀ ω ∉ B, ∀ σ
1371: theorem eq729_duhamel_check (s1 s2 : Bool) (a1 a2 : Zd 3 (sz0.L 0)) : ‖(∫ ω, eq729F sz0 Eq729AInst_t1 Eq729AInst_t0 Eq729AInst_K Eq729AInst_E 0 (0 + 1) ω ⟨[s1, s2], [a1, a2]⟩ ∂(Pgue sz0)) - (∫ ω, eq729F sz0 Eq729AInst_t1 Eq729AInst_t0 Eq729AInst_K Eq729AInst_E 0 0 ω ⟨[s1, s2], [a1, a2]⟩ ∂(Pgue
1330: theorem eq729_primBil2_check : primBilGUE 3 (sz0.L 0) (sz0.W 0) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) ⟨[true, false], [0, 1]⟩ = (sz0.W 0 : ℂ) ^ 3 * ∑ a : Zd 3 (sz0.L 0), ∑ b : Zd 3 (sz0.L 0), Eq729AInst_Kt (sz0.L 0) (17 / 20) ⟨[true, false], [a, 1]⟩ * SBgue 3 
1338: theorem eq729_primRhs_one_check : primRhsGUE 3 (sz0.L 0) (sz0.W 0) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) ⟨[true], [0]⟩ = 0
1343: theorem eq729_norm_primRhs2_le_check : ‖primRhsGUE 3 (sz0.L 0) (sz0.W 0) (Eq729AInst_Kt (sz0.L 0) (17 / 20)) ⟨[true, false], [0, 1]⟩‖ ≤ (((sz0.W 0 * sz0.L 0) ^ 3 : ℕ) : ℝ) * (1 / 1000000) * (1 / 1000000)
1351: theorem eq729_eG2_check : egtNGUE 3 (sz0.L 0) (sz0.W 0) 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 (sz0.L 0) (sz0.W 0) => (2 : ℂ)) ⟨[true, false], [0, 1]⟩ = (sz0.W 0 : ℂ) ^ 3 * ∑ a : Zd 3 (sz0.L 0), ∑ b : Zd 3 (sz0.L 0), ((loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (Matrix.diago
1393: theorem eq729_grid_facts_check : 0 ≤ gridStep Eq729AInst_t1 Eq729AInst_t0 Eq729AInst_K 0 ∧ ((Eq729AInst_K 0 : ℕ) : ℝ) * gridStep Eq729AInst_t1 Eq729AInst_t0 Eq729AInst_K 0 = Eq729AInst_t0 0 - Eq729AInst_t1 0 ∧ gridTime Eq729AInst_t1 Eq729AInst_t0 Eq729AInst_K 0 1000 ∈ Set.Icc (Eq729AInst_t1 0)
# proofs (terms) of the two required instances: sed -n 1207,1211p; sed -n 1222,1223p; and of eq729_one_step_check: sed -n 1304,1312p
  eq729_Kdisc (W := sz0.W 0) (Eq729AInst_Kt (sz0.L 0)) (t1 := 17 / 20) (t0 := 9 / 10)
    (u := 17 / 20) (Δ := 1 / 2621440) (b2 := 1 / 100000) ⟨le_rfl, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)
    (by rw [Eq729AInst_N]; norm_num) (Eq729AInst_hKb (by norm_num)) Eq729AInst_hKd s1 s2 a1 a2

  exact eq729_norm_primBil2_le 3 (sz0.L 0) (sz0.W 0) _ _ true false 0 1
    (fun x => Eq729AInst_hK0 true false x 1) (fun y => Eq729AInst_hK0 true false 0 y)
  eq729_one_step sz0 Eq729AInst_K (fun n => Eq729AInst_Kt (sz0.L n)) (E := Eq729AInst_E)
    (n := 0) (Λ := 10 / 2097152) (ρ := 1) (p := p) (Bk := 50) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Eq729AInst_hΛ (by norm_num) zero_le_one (by norm_num) hp0
    (by rw [(sz0_values).2.2.1]; unfold gridStep; norm_num)
    (Eq729AInst_hKb (by norm_num))
    (fun s _ s1 s2 s3 x y w => by
      rw [Eq729AInst_Kt_three, norm_zero]; positivity)
    Eq729AInst_hKd (k := 0) (by norm_num) hX hB hg1 hg2 hg3 Eq729AInst_hBk s1 s2 a1 a2
```
**Name-clash grep** and **port** (RBM2D read-only, source `RBM2D/Universality/GUEPhase/Eq729A.lean` 1043 lines, commit 9e0f275):
```
$ grep -rnE '\b(eq729_[A-Za-z0-9_]*|eq729F|eq729e|eq729c|Eq729AInst|Eq729A_[A-Za-z0-9_]*)\b' RBM3D RBM3D.lean --include='*.lean' | grep -v '^RBM3D/Probe/' | grep -v 'RBM3D/Universality/GUEPhase/Eq729A.lean' | wc -l
0
$ git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/Eq729A.lean | wc -l
0   (source unchanged since the cited commit)
$ grep -nE 'Z2|\(W : [ℝℂ]\) \^ 2|\(L : ℝ\) \^ 2|\(W \* L\) \^ 2|BlockIndex|spectralZ|KLoop' RBM3D/Universality/GUEPhase/Eq729A.lean | cut -d: -f1
20 21 22   (docstring lines of the renaming paragraph only)
$ binder names (h…) of eq729_one_step, RBM2D vs RBM3D (stmts.py | grep -oE '\(h[^ :]*')   ->  identical lists: True (20 names)
```
**Translation table** (source line in RBM2D; line in this file for the first name; the ticket's port map applied):
```
eq729_primBil2                               src :61          file :52   `(L W)`→`(d L W)`; `Z2 L`→`Zd d L`; `primBilGUE L W`→`primBilGUE d L W`; `(W:ℂ)^2`→`^d`; `SBgue L a b`→`SBgue d L a b`
eq729_eG2                                    src :88          file :80   as above; `gloop L W (blockMat M) (spectralZ E u) I`→`loopL d L W (blockMat d L W M) (zt E u) I`; `KLoop.mSig`→`mSigma`; `egtNGUE L W`→`egtNGUE d L W`
eq729_norm_primBil2_le                       src :139         file :132  `(L W)`→`(d L W)`; `((W*L)^2:ℕ)`→`((W*L)^d:ℕ)`; hypotheses `hA hB` and the bound `N α β` unchanged
eq729_primRhs_one                            src :148         file :141  `(L W)`→`(d L W)`; `Z2 L`→`Zd d L`
eq729F                                       src :264         file :275  `(d : Sizes)`→`{d : ℕ} (sz : Sizes d)`; body `loopL d (sz.L n) (sz.W n) (blockMat d …) (zt (E n) (gridTime …)) I`
eq729_step_nonneg / eq729_KΔ / eq729_time_mem src :272/282/289 file :283  none (no `d`); same statements and proofs
eq729_eta_pos / eq729_eta_le / eq729_zt_im   src :302/306/311 file :313  none; `eq729_zt_im` proof `etaT_eq_zt_im.symm` (source `spectralZ_im`); statement `(zt E u).im = etaT E u`
eq729_duhamel                                src :362         file :378  `(d : Sizes)`→`{d} (sz : Sizes d)`; `genMatGUE (d.L n) (d.W n)`→`genMatGUE d (sz.L n) (sz.W n)`; `envConst`→`envConst d …`; `spectralZ`→`zt`; `Pgue d`→`Pgue sz`; hypotheses and bound unchanged
eq729_norm_primRhs2_le                       src :537         file :555  `{L W}`→`{d L W}`; `(W*L)^2`→`(W*L)^d`
eq729_Kdisc                                  src :544         file :562  `{L W}`→`{d L W}`; `N=(W*L)^d` in `hMΔ` and in `3 N² Δ²`; `hb2 hKb hKd` unchanged
eq729e                                       src :681         file :717  `(d : Sizes)`→`{d} (sz : Sizes d)`; `Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ`
eq729c                                       src :687         file :723  verbatim (a function of five reals)
eq729_one_step                               src :695         file :731  `sz`; `d.size n`→`sz.size n` (`=(W L)^d`); `KLoop.mSig`→`mSigma`; `spectralM`→`mE`; `Z2 (d.L n)`→`Zd d (sz.L n)`; all hypotheses, order and conclusion unchanged
```
**Twin table** (RBM2D name → RBM3D; resolved by `lake env lean pn.lean`, module shown):
```
GoodEvent_measurable_gloop → walk_measurable_loopL, walk_measurable_blockMat (Path.Walk:780,788), gueH_measurable (Universality.GUEPhase.Grid:205)
norm_gloop_le_crude → Gauss.norm_gloop_le_crude (Gauss.FlowCalculus:708);  Ind.norm_gloop_le_of_le_abs_im → same name (Induction.Split:757)
Gsig_conjTranspose, gloopProd_cons/nil, Eblk_conjTranspose → re-derived: Eq729A_Gres_conjTranspose (copy of private Split.lean:250), Eblk_isHermitian (Loop.GLoop:66), `simp [loopL]`
trace_Eblk_eq_one → trace_Eblk (Loop.GLoopFlow:231);  KLoop.mSig, spectralM, spectralZ_im → mSigma (Defs.Semicircle:85), mE, etaT_eq_zt_im (Loop.GLoop:79)
RBM.Ind.LLf L W E u M → loopL d L W (blockMat d L W M) (zt E u), through loopGenGUE (Universality.GUEPhase.Generator:1229); condExp_loop_drift_gue (Universality.GUEPhase.Drift:1318)
absent from the Eq729A import closure (same script): trace_Eblk_eq_one, etaT_le_of_le, Green.etaT_le_of_le, gloopProd_cons, Eblk_conjTranspose, Gsig_conjTranspose, size_eq, GoodEvent_measurable_gloop, Gres_conjTranspose
```
**Narrative.**
- All 17 declarations of the ticket are in the file with the statements of the source under the port map; every `W^2`, `L^2`, `(W L)^2` of a `d`-line is `^d` (table; grep above); `N^ℓ`, `3 N² Δ²`, `10000 N⁴ (1+N)⁶ Δ^{3/2}`, `eq729c` keep their form, as predicted in (a).  28 private helpers `Eq729A_*`.
- Proof changes beyond renaming: `Eq729A_avgErr_eq` uses the merged `trace_Eblk` and `simp [loopL]`; `Eq729A_loopL_one_false` re-derives the conjugation of a 1-loop (`Eq729A_Gres_conjTranspose`, `Eblk_isHermitian`); `Eq729A_loop_bound` bounds `((W:ℝ)^d)⁻¹ ≤ 1` by `inv_le_one_of_one_le₀ (one_le_pow₀ …)`; `Eq729A_genMat_two` is the merged `loopGenGUE` at `k = 2` with `LLf` replaced by `loopL … (zt E u)`; the card of `Zd d L` is `simp only [Zd, Fintype.card_fun, Fintype.card_fin, ZMod.card]` (and one `ring` after `field_simp`); `eq729_one_step`'s proof is the source's with these renames.
- New: private `Eq729A_hdrift_int` (the drift of a 2-loop is integrable: source lines 780-784 and 792-799, inside `eq729_one_step`, as a lemma), used only by the `eq729_duhamel` instance; and the namespace `Eq729AInst` (9 `_check` theorems, 2 examples).
- Instances at `d = 3`, `sz0` (`L = 4`, `W = 32`, `N = 2097152`), `n = 0`, `E = 0`, window `t₀ - t₁ = 1/20`, `K = 131072` (`N Δ = 4/5`), family `c(s)` with `c' = N c²`, `primRhsGUE K̃_s = N c(s)² ≠ 0` (`Eq729AInst_primRhs`).  The two required instances (`eq729_Kdisc`, `eq729_norm_primBil2_le`) and every other target have one.  `eq729_duhamel_check`: all hypotheses discharged.  `eq729_one_step_check`: every deterministic hypothesis discharged (`hK2b`, `hK3b`, `hKd`, `hBk`, `hMΔ`, …); the stochastic inputs `hX`, `hB`, `hg1`-`hg3` stay hypotheses (CLAUDE.md §4 step 2), and the `example` after it takes `B = univ`, `p = 1`, leaving only `hX`.
- The conclusion of `eq729_one_step_check` is true but its right side is `≈ 3.9e57` (last line of (a′)), dominated by the envelope term: it needs `Δ` of the order `1e-45`, the paper's grid `K = (N+1)^{32 n₀+64}`, which is a proof device, not a hypothesis of any target (as in (a)).
- Not done: no `∀ᶠ n` statement (all targets are at a fixed `n`); `3 ≤ d` is not used; the full `lake build` above does not contain the module (root import is the hub's), the registry pre-check does.

## (c) Verified Mathlib names (module of the first resolution; `lake env lean mn.lean`)
MeasureTheory.norm_integral_le_of_norm_le_const: MeasureTheory.Integral.Bochner.Basic
MeasureTheory.integral_condExp: MeasureTheory.Function.ConditionalExpectation.Basic
MeasureTheory.integrable_condExp: MeasureTheory.Function.ConditionalExpectation.Basic
MeasureTheory.integral_finsetSum: MeasureTheory.Integral.Bochner.Basic
MeasureTheory.integral_indicator_const: MeasureTheory.Integral.Bochner.Set
MeasureTheory.measure_toMeasurable: MeasureTheory.Measure.MeasureSpaceDef
MeasureTheory.Integrable.of_bound: MeasureTheory.Integral.IntegrableOn
norm_add₃_le: Analysis.Normed.Group.Basic
Convex.norm_image_sub_le_of_norm_hasDerivWithin_le: Analysis.Calculus.MeanValue
HasDerivAt.ofReal_comp: Analysis.Complex.RealDeriv
ENNReal.toReal_le_of_le_ofReal: Basic.ENNReal.Real
integral_conj: MeasureTheory.Integral.Bochner.ContinuousLinearMap
pow_le_one₀: Algebra.Order.GroupWithZero.Basic
inv_le_one_of_one_le₀: Algebra.Order.GroupWithZero.Basic
inv_le_iff_one_le_mul₀: Algebra.Order.GroupWithZero.Basic
one_le_pow₀: Algebra.Order.GroupWithZero.Basic
HasDerivAt.div: Analysis.Calculus.Deriv.Inv
MeasureTheory.probReal_univ: MeasureTheory.Measure.Typeclasses.Probability
pow_le_pow_left₀: Algebra.Order.GroupWithZero.Basic
div_le_iff₀: Algebra.Order.GroupWithZero.Basic
Matrix.trace_conjTranspose: LinearAlgebra.Matrix.Trace
Matrix.conjTranspose_nonsing_inv: LinearAlgebra.Matrix.NonsingularInverse
(not listed: 11 further names of the same files, all resolved in the same run: `integral_add/sub/const_mul/mono`, `norm_integral_le_integral_norm`, `norm_sum_le`, `trace_smul`, `trace_mul_comm`, `ZMod.card`, `Fintype.card_fun`, `hasDerivAt_const`.)  No Mathlib name was found absent; the names not found are project-local (twin table).

## (d) Open issues and paper-delta candidates
- `eq729_one_step_check` keeps `hX` (1-loop input of the second half, `gueGrid_expect_oneLoop`, UN-47) as a hypothesis; with `B = univ`, `p = 1` the rest is discharged (vacuous `∀ ω ∉ univ`, as (a) planned).
- The ticket's "109 `^ 2` tokens" is 82 in the source (section (a)); no effect on the port.
- `$ grep -c '7\.29\|eq:729' paper/tex/*.tex paper/README.md` sums to 0: the d ≥ 3 TeX has no (7.29); "(7.29)" is the ticket's and RBM2D's numbering.
- Paper-delta candidate `T2350a`: UN-44 (GUE-phase grid, first half of (7.29)) has no statement in `paper/tex/`; the 17 targets are audited against RBM2D `Eq729A.lean` at 9e0f275 and this report's table, not against the d ≥ 3 paper.
- Paper-delta candidate `T2350b`: `eq729c` and `eq729_Kdisc` give explicit constants (`3 N² Δ²`, `10000 N⁴ (1+N)⁶ Δ^{3/2}`, from the band `envConst`), where the paper writes `≺`; `d` enters only through `N = (W L)^d`.
