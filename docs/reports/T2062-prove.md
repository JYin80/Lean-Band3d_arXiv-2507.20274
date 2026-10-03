Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 18:58:24 UTC 2026

Notation: `N = sz.size n = (W L)^d`, `Q = η_t⁻¹`, `c₁ = √(2κ)/2`, `x = |u-u'|`, `ζ_u = ((1-s)/(1-u))^{k-1} Bctl(s)^{k-1}`, `Bctl = W^{-d}·Bparam(…,K=0)`. Sources read: `Defs.lean:377` (`STNetLift`), `Defs.lean:234` (`STStep1Loop`), `Sizes.lean:138-214`, `docs/reports/T2047-prove.md` (b.4, b.7), RBM2D `Continuity.lean:1125-1462` at `c9a24cf`.

Targets in mathematics. `gopbound`: `GopboundPin sz κ E` (T2047 pin, `C' = 2C+14`). `stNetLift_holds : STNetLift d`: if for every time sequence `u ∈ [s,t]` and every `k ≥ 1` one has `max_{σ,a}|𝓛^{(k)}_{u_n,σ,a}| ≺ ζ_{u_n}` (the pin `Prec` has the union over `(σ,a)` inside `P`, `u` fixed along `n`), then `max_{u∈[s,t],σ,a}|𝓛^{(k)}_{u,σ,a}|/ζ_u ≺ 1` (`STStep1Loop`, `u` inside `P`).

### (i) Exponent table (d-free unless stated; `N` is the only scale)

| Item (RBM2D line) | Value | Constraint | Slack |
|---|---|---|---|
| `GopboundPin` C' (:1272) | `C' = 2C+14` | `3N^6·N^{-C'/2} ≤ N^{-C}`, i.e. `3N⁻¹ ≤ 1` | `N/3`; needs `N ≥ 3` |
| `Q=η_t⁻¹ ≤ N²` (`cont_eta_inv_le` :1044) | `η_t=(1-t)Im m(E)` | `(1-t)⁻¹ ≤ N`, `1/c₁ ≤ N` | `1/c₁=4.47` at `κ=1/10` |
| `\|E\| ≤ 2-κ` for `E = lemE z_n` | (RBM2D: hypothesis `hE`) | `\|lemE z\| ≤ \|Re z\| ≤ 2-κ` (`abs_lemE_le`, `STFlow`/`locDomain`) | exact |
| `(1-t)⁻¹ ≤ N` (RBM2D hyp. `RangeCond`; **new derivation**) | `t ≤ lemT z_n`, `(1-t₀)Im m(E)=√t₀·Im z` (`zt_im_lemma28`,`zt_im`), `Im m(E) ≤ 1`, `t₀ ≥ 1/16` (`lemma28_quant`) | `1-t ≥ Im z/4 ≥ N^{-1+ε}/4`, so `(1-t)⁻¹ ≤ 4N^{1-ε} ≤ N` iff `N^ε ≥ 4` | `N^ε` = 4.287 vs 4 at `sz0`, `n=0` (tight); eventual since `N→∞` |
| `t<1` | `t ≤ lemT z <1` (`lemT_lt_one`) | `s ≥ 0` | `1-t ≥ N^{-1+ε}/4 > 0` |
| entry modulus (`cont_entry_diff` :776) | `‖G_u-G_{u'}‖_max ≤ Q²(Xb+1)√x`, `Xb=2N²` | `Q²(Xb+1) ≤ 3N^6`, `x ≤ 1` | `N^4 ≤ N^6` |
| `card Idx = card Vtx = (WL)^d = N` | exact (`Sizes.card_Idx`) | `d` enters only here | exact |
| loop net: `A, Cv, ε` (:1387) | `A=6k+16`, `Cv=k+1`, `ε=N^{-k}`; `#V=2^k(L^d)^k` | `#V ≤ 2^kN^k ≤ N^{k+1}` (`L^d ≤ N`, `2^k ≤ N`); `6k ≤ N` | factor `N/2^k`; 2D `L²` → `L^d` |
| `cont_core` index count | `netSize(A+1,N)·#V ≤ N^{A+2+Cv}`; spacing `≤ N^{-A-1}` | union cost absorbed by `D → D+A+2+Cv` | T2047 table |
| gA, gC (:1153) | gA `N·N^{-A} ≤ N⁻¹`; gC `N·k·N^{2k}·3N^6·N^{-A/2} ≤ N^{-k}` | exponent `1+2k+6-(3k+8) = -k-1` | lhs/rhs `= 3k/N` |
| gB (:1153) | `N·N^{-A/2} ≤ N⁻¹` | (not needed in 3D: `ζ` has no `ℓ_u` factor) | dropped |
| `ζ_{u'} ≤ 2ζ_u` (replaces `cont_LP_zeta_ratio`) | `(1-u)/(1-u') ≤ 1+x/(1-t) ≤ 1+Nx` (u,u' ≤ t); `Bctl(s)` does not depend on `u` | `(1+Nx)^{k-1} ≤ 1/(1-(k-1)Nx) ≤ 2` if `(k-1)Nx ≤ 1/2`; `Nx ≤ N^{-6k-15}` | needs `k-1 ≤ N`; 2D needed `3(k-1) ≤ N/2` |
| `ε ≤ ζ` (replaces `cont_LP_low` :1130) | `ζ ≥ Bctl(s)^{k-1} ≥ N^{-(k-1)} ≥ N^{-k}` | `0 ≤ s ≤ u < 1`; `Bctl(s) ≥ N⁻¹` (`cont_inv_size_le_Bctl`) | factor `N` |
| diagonal step (new; `Prec` for all `u`-sequences ⇒ `PerTimeDomAt`) | for fixed `τ,D`: if `∀ᶠ n ∀ u∈[s_n,t_n] ∀ v: P(N^τζ<ξ) ≤ N^{-D}` failed, pick bad `(u_n)` on a frequent set, `u_n:=s_n` elsewhere: contradicts `Prec` at that sequence; single `(u,v)` event ⊆ union event | none (pure logic, no exponent) | — |
| weak law `A,Cv,ε` (:1445; **not in `STNetLift`**) | `A=40`, `Cv=2`, `ε=N^{-1/4}`, `ζ=Bctl(u)^{1/4}` | `3N^6N^{-20} ≤ N^{-1/4}`; `Bctl(u) ≥ N⁻¹`; ratio `(1+Nx)^{1/4} ≤ 2` (`cont_Bctl_ratio`) | `log2` lhs `-292.4` vs `-5.25` |

Where the 2D `d=2` exponents sit: `(WL)²→(WL)^d` (all `=N`), `L²→L^d`, `W²→W^d` (only in `scaleM`, replaced by `Bctl`), `card Z2 m = m²→m^d` (`card_Idx`), `scaleM`/`ℓ` → `Bctl`. No exponent in the table depends on `d` except through `N = (WL)^d`; none changes sign at `d ≥ 3`. No statement is false at `d ≥ 3` as ported.

How `step1NetLift` gives `STNetLift`: intro `κ ε 𝔡 𝔠 sz z hflow s t hs0 hst ht hu`. From `STFlow`: `SizeTendsto` (so `Tendsto size`), `|Re z_n| ≤ 2-κ`, `N^{-1+ε} ≤ Im z_n ≤ 1`. Then `E = STflowE z`: `|E_n| ≤ 2-κ` (row 3), `(1-t_n)⁻¹ ≤ N` eventually (row 4). `PerTimeDomAt` for `ξ=‖Lloop‖`, `ζ` over `TimeIcc s t n × V n` by the diagonal step from `hu`; then `cont_core` with `A=6k+16`, `Cv=k+1`, `ε=N^{-k}`, `Ξ = contGood` (`cont_highProbAt_good`), `hlow` (row `ε ≤ ζ`), `hclose` (gC, `ζ`-ratio, deterministic loop modulus `cont_loopAbs_diff` ported to `Lloop = loopFine …`). Conclusion `StochDomAt` over `TimeIcc × V` is `STStep1Loop` for each `k ≥ 1`. `Bandwidth`, `WO` (in `Admissible`) and `CondStInd` are unused; there is no `3 ≤ d` hypothesis in `STNetLift` and none is needed (`SizeTendsto` already forces `N → ∞`). No propagator (PT) pin occurs in the cut part. The weak-law half of RBM2D `Step1NetLift` has no 3D pin: `STNetLift` states the loop family only, and `STStep1Weak/STStep1WeakPT` occur outside `Induction/Defs.lean` only in comments of `ContinuityNet.lean` (lines 27, 658, 724; `grep -rn` below shows files); porting it (rows weak law) is optional and consumer-free.

### (ii) Concrete instance: `sz0`, `n=0`, `d=3`, `L=4`, `W=32`, `lam=1/64`, `N=2^21`; `κ=ε=1/10`, `z_0 = 1/2 + i N^{-4/5}`, `s=0`, `t=t₀=lemT z_0`, `u ∈ {0,1/32,1/16,t₀}`, `k ∈ {1,2,3}`
All hypotheses of `stNetLift_holds` at once: `STFlow` (`SizeTendsto`, `locDomain`), `0≤s≤t≤lemT z`, `t<1`; the `Prec` hypothesis `hu` is the stochastic input (stays a hypothesis of the instance, as in `inst_netLift`, `Defs.lean:607`). `gopbound`: `0<κ`, `|E|=1/2 ≤ 1.9`, `SizeTendsto sz0` (limit: `N_n=((2(n+1))^5·4(n+1))^3 → ∞`, last line). Command and output (`out.txt` columns cut to 230):
```
$ python3 scratchpad/T2062/check.py   # exact Fractions for Bctl, ζ; floats only for msc(z_0)
d=3 L=4 W=32 lam=1/64 N=(WL)^d=2097152=2^21; kappa=eps=0.1
STFlow: |Re z|=0.5<=2-kappa=1.9: True; N^(-1+eps)=2.044e-06 <= Im z=8.764e-06 <= 1: True
msc root check |m^2+zm+1|=2.2e-16, Im m>0: True
lemE=0.500000 |lemE|<=|Re z|=0.5: True; lemT=0.999990948752; 1-lemT=9.0512e-06; formula eta/(Im m+eta)=9.0512e-06
1-t0 >= Im z/4 (via (1-t0)Im m(E)=sqrt(t0)Im z, Im m(E)<=1, t0>=1/16): True; (1-t0)^-1=1.105e+05 <= 4/Im z=4.564e+05 <= N=2097152: True; N^eps=4.2871>=4: True
c1=sqrt(2kappa)/2=0.2236; 1/c1=4.472<=N: True
--- k=1: A=6k+16=22, mesh x=N^-A=2^-462, netSize ~ N^(A+1)=2^483; #V=2^k L^(dk)=128 <= N^(k+1): True
  loop modulus log2: N k N^2k 3N^6 N^(-A/2) = -40.42  vs log2 N^-k = -21.00; ratio=3k/N: 1.431e-06 vs 1.431e-06; ok=True
  u=0: eta_u^-1=1.033e+00 <= N^2=4.40e+12: True; zeta(u)=1.0000e+00 >= eps=N^-k=4.768e-07: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=1/32: eta_u^-1=1.066e+00 <= N^2=4.40e+12: True; zeta(u)=1.0000e+00 >= eps=N^-k=4.768e-07: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=1/16: eta_u^-1=1.102e+00 <= N^2=4.40e+12: True; zeta(u)=1.0000e+00 >= eps=N^-k=4.768e-07: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=4503558864172939/4503599627370496: eta_u^-1=1.141e+05 <= N^2=4.40e+12: True; zeta(u)=1.0000e+00 >= eps=N^-k=4.768e-07: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
--- k=2: A=6k+16=28, mesh x=N^-A=2^-588, netSize ~ N^(A+1)=2^609; #V=2^k L^(dk)=16384 <= N^(k+1): True
  loop modulus log2: N k N^2k 3N^6 N^(-A/2) = -60.42  vs log2 N^-k = -42.00; ratio=3k/N: 2.861e-06 vs 2.861e-06; ok=True
  u=0: eta_u^-1=1.033e+00 <= N^2=4.40e+12: True; zeta(u)=3.0987e-05 >= eps=N^-k=2.274e-13: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=1/32: eta_u^-1=1.066e+00 <= N^2=4.40e+12: True; zeta(u)=3.1987e-05 >= eps=N^-k=2.274e-13: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=1/16: eta_u^-1=1.102e+00 <= N^2=4.40e+12: True; zeta(u)=3.3053e-05 >= eps=N^-k=2.274e-13: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=4503558864172939/4503599627370496: eta_u^-1=1.141e+05 <= N^2=4.40e+12: True; zeta(u)=3.4235e+00 >= eps=N^-k=2.274e-13: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
--- k=3: A=6k+16=34, mesh x=N^-A=2^-714, netSize ~ N^(A+1)=2^735; #V=2^k L^(dk)=2097152 <= N^(k+1): True
  loop modulus log2: N k N^2k 3N^6 N^(-A/2) = -80.83  vs log2 N^-k = -63.00; ratio=3k/N: 4.292e-06 vs 4.292e-06; ok=True
  u=0: eta_u^-1=1.033e+00 <= N^2=4.40e+12: True; zeta(u)=9.6019e-10 >= eps=N^-k=1.084e-19: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=1/32: eta_u^-1=1.066e+00 <= N^2=4.40e+12: True; zeta(u)=1.0231e-09 >= eps=N^-k=1.084e-19: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=1/16: eta_u^-1=1.102e+00 <= N^2=4.40e+12: True; zeta(u)=1.0925e-09 >= eps=N^-k=1.084e-19: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
  u=4503558864172939/4503599627370496: eta_u^-1=1.141e+05 <= N^2=4.40e+12: True; zeta(u)=1.1720e+01 >= eps=N^-k=1.084e-19: True; zeta(u+x)/zeta(u)=1.000000000000<=2: True
Bctl(0)=3.0987e-05 >= 1/N=4.7684e-07: True; Bctl(1/16)=3.3052e-05 (independent of u in the pin's zeta: zeta uses Bctl(s) only)
gopbound C=1 C'=16: 3N^6 sqrt(N^-C')/N^-C = 1.431e-06 = 3/N=1.431e-06 <=1: True
gopbound C=2 C'=18: 3N^6 sqrt(N^-C')/N^-C = 1.431e-06 = 3/N=1.431e-06 <=1: True
gopbound C=3 C'=20: 3N^6 sqrt(N^-C')/N^-C = 1.431e-06 = 3/N=1.431e-06 <=1: True
SizeTendsto sz0: N_n=((2(n+1))^5*4(n+1))^3 for n=0,1,10: [2097152, 549755813888, 11659991713824860234842112]
```
```
$ grep -rln "STStep1Weak" /Users/junyin/Lean_proof/RBM3D/RBM3D | sort
/Users/junyin/Lean_proof/RBM3D/RBM3D/Induction/ContinuityNet.lean
/Users/junyin/Lean_proof/RBM3D/RBM3D/Induction/Defs.lean
```

### Verdicts
- `gopbound` (`GopboundPin`, `C' = 2C+14`): **PASS**. Slack `N/3`; hypotheses hold together at `sz0`, `N=2^21`, `C∈{1,2,3}`.
- `stNetLift_holds` (`STNetLift d`, exact type): **PASS**. Every exponent closes (`A=6k+16`, gC slack `3k/N`, `(k-1)Nx ≤ N^{-6k-15}·k`); two points for the prover: (1) `RangeCond` is derived, not assumed: `(1-t)⁻¹ ≤ N` needs `N^ε ≥ 4` (eventual; 4.287 at `sz0`), via `zt_im_lemma28`, `zt_im`, `Im m(E) ≤ 1`, `lemma28_quant`; (2) the per-time input of `cont_core` comes from the diagonal step above (new, no RBM2D counterpart).
- `Step1NetLift` / `step1NetLift` (RBM2D defs, loop and weak half): **PASS** for the loop half; the weak half is a statement with no 3D consumer. Dropping its weak half needs no dispatcher decision per the grep above (no Lean use of `STStep1Weak` outside `Defs.lean`); the ticket lists `Step1NetLift`, so the prover should either port both halves (`cont_WL_low`, `cont_WL_close`, rows weak law) or say it dropped the weak half.
- Proposed paper-delta candidate for the prover: none at preflight.

## (b) Script output (written Sat Oct  3 19:18:45 UTC 2026, `date -u`)

Branch `t/T2062`, one file `RBM3D/Induction/Continuity.lean`, commit `030c138`. Scratch files: `scratchpad/T2062/`, not committed. All outputs below are verbatim (long lines cut by `cut -c1-170`).

### b.1 Build, hygiene, scope of the diff
$ lake build RBM3D.Induction.Continuity (tail)   # exit=0
Build completed successfully (3323 jobs).
exit=0
$ lake env lean RBM3D/Induction/Continuity.lean | wc -l   (0 lines = no error, no warning)   # exit=0
       0
$ lake build   (whole library; the root import of the new module is added by the hub at merge) (tail)   # exit=0
non-vacuity certificates: 4 of 48 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3782 jobs).
$ grep -c 'sorry|admit|native_decide|^axiom' RBM3D/Induction/Continuity.lean   # exit=1
0
$ git diff main...t/T2062 --stat   # exit=0
 RBM3D/Induction/Continuity.lean | 857 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 857 insertions(+)
$ git log --oneline -1   # exit=0
030c138 T2062: S1-34 Induction/Continuity second part (gopbound, step1NetLift, stNetLift_holds)
first build of the module after its last edit (tool log): ✔ [3323/3323] Built RBM3D.Induction.Continuity (5.8s)

### b.2 #print axioms of the public declarations (gopbound, Step1NetLift, step1NetLift, stNetLift_holds)
$ lake env lean ax.lean   # import RBM3D.Induction.Continuity; #print axioms of the four public names   # exit=0
'RBM.Ind.gopbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.Step1NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.step1NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stNetLift_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stNetLift_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STNetLift d

### b.3 Registry pre-check (DECISIONS §20, ST1-COMMON item 8)
$ cat precheck.lean; lake env lean precheck.lean | grep "axiom audit|premises found|STNetLift"
import RBM3D
import RBM3D.Induction.Continuity
#assert_rbm_axioms
1:axiom audit: 2158 theorems, 884 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
26:  RBM.Gauss.Sizes.STNetLift: 2 [no certificate]
55:premises found by scanning: 45 (borrowed 2, owed 31, structural 12).
66: RBM.Gauss.Sizes.STNetLift,
exit=0
base library (`lake build` of the worktree, root without the new module):
info: RBM3D.lean:103:0: axiom audit: 2155 theorems, 883 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 46 (borrowed 2, owed 32, structural 12).

### b.4 Target statements, extracted from the file by script (proofs elided as `…`)
$ python3 extract.py gopbound Step1NetLift step1NetLift stNetLift_holds
L527: theorem gopbound (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : GopboundPin sz κ E := …
L594: def Step1NetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    (STStep1LoopPT sz E s t → STStep1Loop sz E s t) ∧
      (STStep1WeakPT sz E s t → STStep1Weak sz E s t)
L605: theorem step1NetLift (sz : Sizes d) : ∀ E κ τ s t, Step1NetLift sz E κ τ s t := …
L777: theorem stNetLift_holds (d : ℕ) : STNetLift d := …
merged pin (RBM3D/Induction/Defs.lean): `def STNetLift (d : ℕ) : Prop` at line 377; `stNetLift_holds : ∀ (d : ℕ), STNetLift d` (b.2 `#check`)

### b.5 Compiled nonempty instances (section 5 of the file: `sz0`, `d = 3`, `n = 0`, `N = 2097152`, `κ = ε = 1/10`; docstrings omitted)
$ sed -n 803,854p RBM3D/Induction/Continuity.lean   (comments removed)
section Instances
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
example (C : ℝ) (hC : 0 < C) :=
  gopbound sz0 (1 / 10) (fun _ => (1 / 2 : ℝ)) (by norm_num) (fun _ => by norm_num) sz0_tendsto C hC
example : Step1NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst :=
  step1NetLift sz0 _ _ _ _ _
example :
    (STStep1LoopPT sz0 (STflowE z0) sInst tInst → STStep1Loop sz0 (STflowE z0) sInst tInst) ∧
      (STStep1WeakPT sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst) :=
  step1NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst (by norm_num)
    (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto RBM.Green.Instance.premises.2.2.2.2
example
    (hu : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      ∀ k : ℕ, 1 ≤ k →
        Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (u n) p.1 p.2 ω‖)
          (fun n _ _ => ((1 - sInst n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1))) :
    STStep1Loop sz0 (STflowE z0) sInst tInst :=
  inst_netLift (stNetLift_holds 3) hu
example
    (hu : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      ∀ k : ℕ, 1 ≤ k →
        Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (u n) p.1 p.2 ω‖)
          (fun n _ _ => ((1 - sInst n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1))) :
    STStep1Loop sz0 (STflowE z0) sInst tInst :=
  stNetLift_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hu

Hypotheses that stay in an instance: `hu` (the loop bound `≺` at every time sequence in `[0,1/16]`, the stochastic input of `STNetLift`) and `STStep1LoopPT`/`STStep1WeakPT` (the per-time inputs of the two implications). Discharged: `0 < κ`, `|E n| ≤ 2 - κ`, `SizeTendsto sz0` (`sz0_tendsto`), `0 ≤ s ≤ t < 1`, `RangeCond`, `STFlow`, `t ≤ lemT z`.

### b.6 Statement diff against RBM2D `c9a24cf` lines 765-1464 after renaming R1-R4 (`python3 stmtdiff.py`; `Cont2D.lean` is `git -C ../RBM2D show c9a24cf:RBM2D/Induction/Continuity.lean`)
RBM2D lines 765-1464: 20 declarations; ported with identical signature after renaming: 8; ported with a changed signature: 9; not ported: 3
IDENTICAL: cont_entry_diff contWord contWord_cons cont_word_norm cont_word_diff cont_one_add_pow_le cont_eta_inv_le gopbound
NOT PORTED: cont_llErr_diff(:798) cont_scaleM_ratio(:933) cont_one_le_size(:1038)
--- CHANGED cont_loopAbs_diff (Continuity:877)
   insert: '' -> '‖'
   replace: 'Abs' -> 'Fine d'
--- CHANGED cont_LP_zeta_ratio (Continuity:973)
   delete: 'd L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) {E ' -> ''
   insert: '' -> ' B'
--- CHANGED cont_WL_low (Continuity:1057)
   delete: 'L W ' -> ''
   replace: 'hL' -> 'sz'
--- CHANGED cont_WL_close (Continuity:1065)
   delete: 'L W ' -> ''
   delete: '[NeZero L] [NeZero W] ' -> ''
--- CHANGED cont_LP_low (Continuity:1130)
   delete: 'L W ' -> ''
   replace: 'hL' -> 'sz'
--- CHANGED cont_LP_eventually (Continuity:1153)
   delete: 'N ^ (-(6 * (k : ℝ) + 16) / 2) ≤ N⁻¹ ∧ N * ' -> ''
--- CHANGED cont_LP_close (Continuity:1188)
   delete: ' {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)' -> ''
   insert: '' -> ' B'
--- CHANGED Step1NetLift (Continuity:1261)
   delete: ' c' -> ''
   delete: ' → 0 < c' -> ''
   delete: ' → Bandwidth d c → CondStInd d E s t' -> ''
--- CHANGED step1NetLift (Continuity:1331)
   delete: 'c ' -> ''
   delete: 'c ' -> ''
NEW (no RBM2D counterpart): cont_loopFine_eq cont_STGM_eq perTime_of_sections stNetLift_holds

### b.7 Dimension tokens of the part (`python3 tokens.py`, comments stripped; ST1-COMMON item 2)
token (code only)                  RBM2D 765-1464  new file §1-4
W^2  `W ^ 2`                                  0              0
L^2  `L ^ 2`                                 22              0
N^2  `(W * L) ^ 2`                           22              0
(d.L n : ℝ)^2                                 3              0
Z2/zdist2                                    13              0
scaleM/ellT                                  96              0
W^-2 type (`⁻²`)                              0              0
`d : Sizes` / `d.size|L|W`                   93              0
`(W : ℝ)⁻¹` (`W^{-2}` bound)                  0              0
cont_card_Z2                                  4              0
3D replacement `^ d`                          -              6
L^2  `L ^ 2` RBM2D lines: [935, 936, 939, 941, 942, 950, 976, 977, 1059, 1066, 1078, 1109, 1132, 1134, 1135, 1137, 1143, 1145, 1147, 1189]
(d.L n : ℝ)^2 RBM2D lines: [1370, 1380, 1383]
Z2/zdist2 RBM2D lines: [810, 815, 819, 839, 880, 1086, 1198, 1297, 1361, 1369, 1387, 1441]
N^2,N^6,Q^2 (N, Q symbols)                   48             47
Bctl                                          0             24

### b.8 Name clash of the new public names against the worktree (`main` at the branch point)
$ grep -rnw <name> RBM3D | grep -v Induction/Continuity.lean   (4 names)
gopbound: no declaration; hits are docstring mentions: RBM3D/Induction/ContinuityNet.lean:19; RBM3D/Induction/ContinuityNet.lean:817; RBM3D/Induction/ContinuityNet.lean:837
Step1NetLift: no declaration; hits are docstring mentions: RBM3D/Induction/Defs.lean:373; RBM3D/Induction/ContinuityNet.lean:20
step1NetLift: no declaration; hits are docstring mentions: RBM3D/Induction/ContinuityNet.lean:20
stNetLift_holds: no hit

### b.9 Port source drift
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Continuity.lean
 RBM2D/Induction/Continuity.lean | 270 ++++++----------------------------------
 1 file changed, 36 insertions(+), 234 deletions(-)
bcc2c11 T2275: merge comment clean-up (Induction)
99d6fe0 T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)
hunks of that diff inside lines 765-1464 (c9a24cf numbering): 773 834 875 931 1037 1247 1255 1257 1267 

### b.10 Narrative
* File. `RBM3D/Induction/Continuity.lean` (857 lines) ports RBM2D `Continuity:765-1464` on top of `ContinuityNet` (T2047, imported, nothing copied), `Induction.Defs` and `Green.Pins` (both S1-07 = T2028; for `Sizes.RangeCond` and `v3_premises_of_stFlow`). Public: `gopbound`, `Step1NetLift`, `step1NetLift` (`RBM.Ind`) and `stNetLift_holds` (`RBM.Gauss.Sizes`, next to its pin); the other 17 declarations are `private`. Per b.6: 8 signatures identical after renaming, 9 changed, 3 not ported, all three `private` in RBM2D: `cont_llErr_diff` (its content is `cont_STGM_eq` plus `abs_norm_sub_norm_le`), `cont_scaleM_ratio` (replaced by T2047 `cont_Bctl_ratio`, `cont_inv_add_one_sub_ratio`), `cont_one_le_size` (merged `Sizes.one_le_size`; dead lemma at RBM2D HEAD, b.9). No PT/propagator pin occurs in this part.
* `stNetLift_holds : STNetLift d` has the pin's type exactly (b.2), for every `d`, no `3 ≤ d`. Proof: (i) the diagonal step `perTime_of_sections` (new, no RBM2D counterpart, no exponent): `≺` along every time section with the union over `(sigma, a)` inside `P` gives `PerTimeDomAt` over `TimeIcc s t n x (sigma, a)`, via `perTimeDomAt_iff_forall_section` and `StochDomAt.precomp_param`; (ii) `Green.v3_premises_of_stFlow` turns `STFlow` and `t <= lemT z` into the premises of `step1NetLift` at `(kappa/2, eps/2)`: `|E_n| < 2 - kappa/2`, `t_n < 1`, `RangeCond (eps/2) t`, `SizeTendsto`. This replaces the derivation planned in (a)(i) row 16 (`N^eps >= 4`, tight at `sz0`); I found no wrong statement in (a), so there is no (a').
* `step1NetLift` applies `cont_core` on `TimeIcc s t n x V n` with `contGood`. Loops: `V = (sigma, a)`, `A = 6k+16`, `Cv = k+1`, `eps = N^{-k}`, `#V = 2^k (L^d)^k <= N^{k+1}` (`hcardZ`: `card (Zd d L) = L^d`; `L^d <= (W L)^d`); weak law: `V = Idx x Idx`, `A = 40`, `Cv = 2`, `eps = N^{-1/4}`. Closing: `cont_LP_close` (gC of (a)(i) row 22; `(k-1) N^-1 <= 1/6`), `cont_WL_close` (`g3`; `(11/10)^{1/4} <= 2` through `cont_Bctl_ratio`). RBM2D's `gB` (`N N^{-A/2} <= N^-1`) served only the `ell` factor of the `d = 2` control and is not in `cont_LP_eventually`.
* Dimension (b.7): `(W L)^2` (22 tokens) became `(W L)^d = sz.size n`; `(d.L n)^2` (3) became `L^d` (`card (Zd d L) = L^d`); `cont_card_Z2` (4) became `Sizes.card_Idx`, `card_BlockIndex`; `scaleM`/`ellT` (96) became `Bctl`; `d : Sizes` (93) became `sz : Sizes d`; `Z2` (13) became `Zd d L`. The exponents in `N`, `k` (`N^2`, `N^6`, `Q^2`, `6k+16`, `40`, `1/4`, `C' = 2C+14`) are unchanged: the exponent table of (a)(i) holds for every `d`. The two docstring mentions `d = 2` (`Continuity:835, 876`) read `d >= 3`.
* `Step1NetLift` ports both halves; `stNetLift_holds` needs the loop half only. Dropped as unused by the proof: the argument `c`, `Bandwidth d c`, `CondStInd d E s t` (RBM2D `T2070b` says the same); `RangeCond` is the merged `Sizes.RangeCond` (T2062a, (d)).
* Registry (b.3): the scan finds no unregistered premise. `stNetLift_holds` has conclusion head `STNetLift`, so the found-premise count goes 46 to 45 and `STNetLift` appears under "carry nothing yet": its owed registry line can go once this merges (cleanup ticket). `RBM3D/Test/Axioms.lean` is unchanged.

## (c) Verified Mathlib names used (`#check @name` in `scratchpad/T2062/names_used.lean`, 46 of 46 resolve, 0 errors; names verified absent: none)
abs_norm_sub_norm_le; Matrix.trace_sub; sub_sub_sub_cancel_right; tendsto_natCast_atTop_iff; Fintype.card_prod; Fintype.card_fun; Fintype.card_bool; Fintype.card_fin; ZMod.card; Real.rpow_le_rpow; Real.mul_rpow; Real.rpow_one; Real.inv_rpow; Real.rpow_neg; half_pos; pow_le_pow_of_le_one; one_le_pow₀; inv_le_one_of_one_le₀; Real.rpow_le_rpow_of_exponent_le; pow_le_pow_left₀; pow_le_pow_right₀; one_le_div; inv_anti₀; div_le_div_iff₀; Real.rpow_natCast; Real.rpow_add; Real.rpow_pos_of_pos; Real.rpow_two; Real.rpow_zero; Real.rpow_nonneg; Real.sqrt_nonneg; Real.sqrt_pos; Filter.Tendsto.eventually_ge_atTop; Filter.eventually_ge_atTop; MeasureTheory.measure_mono; abs_sub_comm; abs_le; sub_sub_cancel; inv_inv; div_le_one; Nat.sub_le; Nat.cast_nonneg; le_mul_of_one_le_left; mul_pow; List.length_cons; Matrix.IsHermitian.submatrix

## (d) Open issues and paper-delta candidates
* `T2062a`: `Step1NetLift` (`Continuity:1261`) differs from RBM2D's by dropping the arguments `c`, `Bandwidth d c`, `CondStInd d E s t` (unused by the proof, RBM2D `T2070b`) and by reading `Step1LoopPT/Unif`, `Step1WeakLawPT/Unif`, `RangeCond` as the merged `STStep1LoopPT/Loop`, `STStep1WeakPT/Weak`, `Sizes.RangeCond`. No hypothesis is added; the statement is stronger.
* The hypothesis of `STNetLift` (`≺` at every time sequence, union over `(sigma, a)` inside `P`) implies `STStep1LoopPT` (the diagonal step): both are `≺` statements at the one scale `N`. No paper delta: the pin is the merged T2028 text, unchanged.
* For the cleanup ticket: remove `RBM.Gauss.Sizes.STNetLift` from `owedProps` once this merges. Nothing else is open; no file outside the sole writable file was touched (b.1).
