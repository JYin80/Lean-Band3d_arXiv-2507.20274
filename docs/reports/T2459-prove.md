Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 15:16:44 UTC 2026
Targets (math only): U5's BA targets `STPfStep5gL`, `STStep5IIIgL` (T2458-check:361, 338) at the BA tuple `(Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)` (check:457-459), regime `STReg5III: sz.lam n^2 <= 1 - t n` (`Step5Pins:58`). Scripts (not in the repo): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2459` (`prefl.py` sha1 prefix 9e14116ebfb4 + `out_*.txt`; `stab.py` of T2390 imported). Notation: `g = sz.lam`, `g0 = BAflowLam0 = sqrt(t0) g` (`FlowPins:386`), `m0 = m/sqrt(t0)`, `K = |M^(B)|^2` (`BAK`), kernel `uKer_(s,t) = (s/t) I + (1-s/t) Theta_t` (`EKPins:79`).

### (i) Exponent table
`d=3`, `Lam = 1/dd = 10`, flow data `(kappa, eps, c, dd) = (1/2, 1/10, 1/6, 1/10)` (`flow_sz0`, `FlowPins:1214`), `sz0` of `Defs/Sizes:260`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^-6`; `t = 1/2`, `s = 1/10`.
| quantity | value | constraint | slack |
|---|---|---|---|
| Admissible `W^(-d/2+dd) <= lam <= 1` (`sz0_admissible` `Sizes:331`) | `lam/W^(-d/2+dd)` = 2.0 / 4.0 / 22.0 (n=0/1/10) | `>= 1` | 2x / 4x / 22x |
| Bandwidth `N^(1/6) <= W` | `N^(1/6)/W` = 0.354 / 0.088 / 0.0029 | `<= 1` | 2.8x / 11x / 340x |
| regime `lam^2 <= 1-t`, `t=1/2` | `lam^2` = 2.4e-4 / 6e-8 / 8e-17 | `<= 0.5` | >= 2000x |
| window `0 <= s < t <= BAflowT0` (`t0_sz0` `FlowPins:1227`, `half_lt_t0` `:1254`) | `t0(n=0)` = 0.6937 (n=1,10: 0.6944) | `t0 >= 2/3 > 1/2` | 0.19 (>= 1/6 proved) |
| `kappa <= Im m` (`BAdom`) | `Im m` = 0.8325 (n=0) | `>= 1/2` | 1.67x |
| `g0 <= lam <= Lam` | `g0` = 0.0130 (n=0) | `g0 <= lam = 0.0156` | 1.2x (`sqrt(t0)` = 0.833) |
| Ward / `|m0|` | `ward` <= 2e-14 all rows; `|m0|` = 0.999493 (n=0) | `sum_b |M_0b|^2 = 1` (`BAMB_ward_row` `Ward:108`), `|m0| <= 1` | `1-|m0|^2 = 1.0e-3 = 5.99 g0^2` |
| `eps1 = min(dd/8, 1/4)` (`PfStep5:34`) | 1/80 = 0.0125 | stop exponent `eps0 < eps1` (`PfStep5:2325`: `eps0 = min(eps1, tau)/2`) | sample `eps0 = 0.01`: 1.25x |
| closure `eps0 < dd/4` (`PfStep5Alg:143-150`) | `dd/4` = 0.025; `2 eps0 - dd/2` = -0.03 | `< eps0` | 0.025 vs 0.01 |
| closure input `lam^2 W^d >= W^(2 dd)` | sz0: `lam^2 W^d = W^0.6` | `>= W^0.2` | exponent 3x; `(lam^2 W^d)^(-1/4) = W^-0.15 <= W^-0.05` |
| closure `N^tau C (1+log W+...) < W^eps0` (conclusion-internal, eventual) | sample `tau = eps0/24`: first `log10 W` = 381.9 (C=1), 868.3 (C=6000) | `eventually` | not a hypothesis of the targets (see (ii)) |
| `D0 = 2/c + 12 d`, `D* = max(D,D0)+2d+1` (`PfStep5:34`) | 48; `D*` = 55 at `D=1` | `D* tau' <= 1/2`, `6 tau' <= tau/4` | by choice `tau' = min(tau/24, 1/(2D*))` |
| rate `c = BAct_rate(3,10,kappa)` (`CombesThomas:45`) | 4.158e-3 / 2.081e-3 / 3.33e-4 (kappa 1/2, 1/4, 0.04) | `> 0`, only `(d, Lam, kappa)` | C1 ok |
| `r = t(1-|m0|^2)/(1-t|m0|^2)` (step ratio of `Theta_t` off the diagonal; `1-t >= g0^2` from the regime) | 2.3e-3 (g=1/64), 0.191 (g=1), 0.042 (g=10, record) | `< 1` uniformly | `1 - r >= 0.76` in the data |
| kernel const `C_U = max sum_b |uKer(a,b)| e^(sqrt|a-b|_inf) / rho`, `rho=(1-s)/(1-t)`, 4 charge pairs, `s in {0,t/4,t/2,t}` | 1.0039 (g=1/64, L=4..64) / 1.5163 (g=1, L>=16; 1.48 at L=4) / 1.63..4.01 (g=10, L=4..256, record) | bounded in `L` | g=1/64 flat (L=4..64), g=1 flat to 3 digits (L>=16); g=10 (regime empty): 3.69 (L=128) -> 4.01 (L=256) |
| `min |1 - t sigma(p)|` at `t_b` | 0.306 / 0.714 / 0.956 | `> 0` as `t -> t0` | no degeneration |
| far field `(1-t)|Theta(+-)(0,x)|`, `|x|_inf >= 8` (`(1/8)(log W)^(3/2) >= 8` iff `W >= e^16`) | 6e-17 / 1.7e-7 / 5.3e-6 | small | — |
| regime reading `g` (`STReg5III`), `g = 1/64 / 1 / 10` | `tmax = min(t0, 1-g^2)` = 0.6937 / 0 / empty | `s<t` needs `tmax > 0` | g=1, 10: **empty** (vacuity confirmed) |
| regime reading `g0` | `tmax = min(t0, 1-g0^2)` = 0.6937 / 0.2862 / empty (`g0^2 = 4.39 > 1`) | — | changing the reading changes a size-level name: stop rule 4 |
| `ell = g0/sqrt(1-t)` at `baFMz`, regime `g^2 <= 1-t` | `<= sqrt(t0) < 1` (analytic: `g0 = sqrt(t0) g`); 0.024 at g=1/64, `t_b` | `ell_t = 1` (`1_2:1118`, case (iii)) | R* = 1.0010 (script C) |
| shape `forall lam0, T2458_STTailtoTailgL' 3 (baFM . lam0)` (check:462), free `lam0` | lattice `R*(ell)`: 1.08 (ell 0.76) -> plateau 3.1-3.2 (ell >= 17, torus-limited L=64) | would need `R* <= Cc(kappa)` | **not confirmed false** on the lattice; continuum lower bound (heuristic) grows like `e^(ell/4)`; U5 does not read it (`baFMz`) |

**H249 (3): can BA case (iii) use TL's one-slot clause (iv) instead of clause 4 of `STGridRepNAtgL d 2`?** Answer: **no as a drop-in; T2460 target 4 should stay until U5's design decides.**
- Types: (iv) (`BATwistGridMartAt`, `BA/TwistGrid2:218`; `BATwistGridWTail` `:255`; `twU` `BA/TwistGrid:105`) is `sum_j twU_(j,k) *v dMart(b, c1, c2)` in one slot, twist frozen at `(c1, c2) = (a 1, a 1)` (T2460 target 1, H1). Clause 4 (`Chain/Step2Gen:994`, `:1025`) is `Step2Gen_UN` over both slots; band `PfStep5:2170` takes conjunct 4 of `stGridRepN_holds d hd 2`.
- Slot 2 in the twisted hierarchy appears only as the source `B1~ = twB1M` (`TwistGrid:90`), with kernel `Theta_u K` (opposite charges: row sum exactly `1/(1-u)`, `K` doubly stochastic). Closing it by a sup-ratio Gronwall (`J = sup |Z|/T`, `T_u ~ (1-u)^-2`, one-slot `rho = (1-u)/(1-t)`) gives the loss `J_t <= J_s ((1-s)/(1-t))^(C_ell - 1)`, `C_ell = (1-u) sum_x Theta_u(0,x) e^(sqrt|x|)` (for `Theta_u K`: `(C_ell-(1-u))/u`, the same to 3 digits below). Script D (proxy: `M` of the flow `g=1/64`, `Theta_u` at `u = 1-g^2`; an estimate of the loss, not a proof of impossibility): `C_ell = 3.136`, loss 5.2e7 at `s=0`, against 1.0017 at `1-u = 1/2`. So naive reuse of (iv) loses a power of `lam^-2` at the edge of case (iii); the two-slot kernel is what makes the constant `C_d^2` (no exponentiation).
- Outline only, not claimed: `uKer_(v,w)` is affine in `v` (`BAuKer_convex`; script D: error 3e-16), so `sum_j U_j(a1,b1) X_j = Theta_k sum_j X_j + (I-Theta_k) sum_j (u_j/u_k) X_j`; with summation by parts, `BAuKerSemigroup_holds` (`TwistGrid:199`) and (iv) at every endpoint `j <= k`, the two-slot tail might follow from (iv); the QV scale (`(E x E)` cross terms between different `b1`) is unchecked. That is U5-design work, not a 1a fact.

### (ii) One concrete nondegenerate instance
`d=3, n=0`: `L=4, W=32, N=2097152`, `g=lam=1/64`, `g0=0.0130`, `Im m=0.8325 >= 1/2`, `t0=0.6937`, `s=1/10 < t=1/2 <= t0`, `1-t = 0.5 >= g^2 = 2.4e-4`, `D=1`, `D*=55`, `eps0=0.01`. Hypotheses of the targets: `3<=d`, `BAFlow` (proved, `flow_sz0`), `s<t<=BAflowT0`, `STReg5III`; the other-gate pins of `STIngR5` (`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`, `STConStInd`, `STStep1Loop`, `STStep2Concl`, `LmaxU`, `LKU`) stay hypotheses (proved on `main` or other gates). Inputs without producer in this ticket: P1 clause 4 (T2460 target 4), P5 `BAKellStarEv` (`t/T2452` probe), U6 statements (T2458, unmerged).
Commands (`cd $S`) and verbatim output:
```
$ python3 prefl.py A | grep -E '^(eps1|n=   0 L=4 W|n=  10 L=44 W|closure|c=BAct|n= 0 L=  4 g=)' | cut -c1-260
eps1=min(dd/8,1/4)=0.0125; eps0=0.01<eps1:True; closure needs eps<dd/4=0.025; 2eps0-dd/2=-0.030 (<eps0: True); D0=2/c+12d=48
n=   0 L=4 W=32 lam=1.562e-02 lam/W^(-d/2+dd)=2.0 N^(1/6)/W=3.54e-01 lam^2<=1-t:True lam^2W^d=W^0.600(need>=0.2) Adm:True
n=  10 L=44 W=5.154e+06 lam=8.820e-09 lam/W^(-d/2+dd)=22.0 N^(1/6)/W=2.92e-03 lam^2<=1-t:True lam^2W^d=W^0.600(need>=0.2) Adm:True
closure C=1 tau=4.17e-04 eps=0.01 (LHS bounded by 2*max of the two terms): first n with LHS<W^eps has log10 W=381.9; stays true for n=10*hi: True
closure C=6000 tau=4.17e-04 eps=0.01 (LHS bounded by 2*max of the two terms): first n with LHS<W^eps has log10 W=868.3; stays true for n=10*hi: True
c=BAct_rate(3,10,kappa)=min(log(1+kappa/(4 d Lam)),kappa/2): kappa=0.5: 4.1580e-03, kappa=0.25: 2.0812e-03, kappa=0.04: 3.3328e-04
n= 0 L=  4 g=1.562e-02 Imz=0.3675 Imm=0.8325 t0=0.6937 (>=2/3:True) 1/2<t0:True g0=1.301e-02 Imm0=0.9995 |m0|=0.999493 1-|m0|^2=1.015e-03 g0^2=1.694e-04
$ python3 prefl.py B big | grep -E '^(g=0.01562 L=  4|g=0.01562 L= 64|g=1 L=  4|g=1 L= 64|g=10 L=  4|g=10 L=256|--)' | sed 's/ ward=[^ ]*//' | cut -c1-300
g=0.01562 L=  4 t0=0.6937 g0=0.0130 Imm0=0.9995 (1-|m0|^2)/g0^2=5.990 tmax[lam]=0.6937 tmax[g0]=0.6937 | t_b=0.6937 C_U=1.0039 min|1-t sig|=0.306 r=2.293e-03 Kwt-|m0|^2=1.019e-03
g=0.01562 L= 64 t0=0.6937 g0=0.0130 Imm0=0.9995 (1-|m0|^2)/g0^2=5.991 tmax[lam]=0.6937 tmax[g0]=0.6937 | t_b=0.6937 C_U=1.0039 min|1-t sig|=0.306 r=2.293e-03 Kwt-|m0|^2=1.019e-03
-- g=1: sz.lam=g reading is empty (1-t>=1 forces t<=0); g0 reading: window (0, 0.2862]
g=1 L=  4 t0=0.3148 g0=0.5610 Imm0=0.6732 (1-|m0|^2)/g0^2=1.737 tmax[lam]=0.0000 tmax[g0]=0.3148 | t_b=0.3148 C_U=1.4795 min|1-t sig|=0.685 r=2.007e-01 Kwt-|m0|^2=5.500e-01
g=1 L= 64 t0=0.2862 g0=0.5350 Imm0=0.6420 (1-|m0|^2)/g0^2=2.054 tmax[lam]=0.0000 tmax[g0]=0.2862 | t_b=0.2862 C_U=1.5163 min|1-t sig|=0.714 r=1.908e-01 Kwt-|m0|^2=5.913e-01
-- g=10: both readings empty (g0^2>1); kernel constants at the t0 boundary 'for the record'
g=10 L=  4 t0=0.3138 g0=5.6017 Imm0=0.5602 (1-|m0|^2)/g0^2=0.022 tmax[lam]=0.0000 tmax[g0]=0.0000 | t_b=0.3138 C_U=1.6318 min|1-t sig|=0.686 r=2.388e-01 Kwt-|m0|^2=6.872e-01
g=10 L=256 t0=0.0439 g0=2.0953 Imm0=0.2095 (1-|m0|^2)/g0^2=0.218 tmax[lam]=0.0000 tmax[g0]=0.0000 | t_b=0.0439 C_U=4.0068 min|1-t sig|=0.956 r=4.206e-02 Kwt-|m0|^2=9.633e-01
$ python3 prefl.py D | grep -E '^(  1-u=5.000e-01|  1-u=1.000e-02|  1-u=2.441e-04|  max)'
  1-u=5.000e-01: (1-u)*rowsum=1.000000  C_ell=1.001742  (1/om)^(C_ell-1) at s=0: 1.0012
  1-u=1.000e-02: (1-u)*rowsum=1.000000  C_ell=1.156905  (1/om)^(C_ell-1) at s=0: 2.0597
  1-u=2.441e-04: (1-u)*rowsum=1.000000  C_ell=3.135762  (1/om)^(C_ell-1) at s=0: 51896918.6173
  max|U(0.4)-(U(0.1)+U(0.7))/2| = 3.3306690738754696e-16 ; max|U(v,w)-((v/w)I+(1-v/w)Theta_w)| = 1.7763568394002505e-15
$ python3 prefl.py C | sed -n '2,8p;23,24p'
lam0=g0=0.5350 (Im m=0.343>=kappa), L=64; sz.lam^2=1-t (regime equality), mean-free spread ell=g0/sqrt(1-t):
  t=0.500000 sz.lam=7.07e-01 ell=   0.76 R*=    1.080 at R=32
  t=0.900000 sz.lam=3.16e-01 ell=   1.69 R*=    1.395 at R=32
  t=0.990000 sz.lam=1.00e-01 ell=   5.35 R*=    2.898 at R=32
  t=0.999000 sz.lam=3.16e-02 ell=  16.92 R*=    3.158 at R=32
  t=0.999900 sz.lam=1.00e-02 ell=  53.50 R*=    3.135 at R=32
  t=0.999999 sz.lam=1.00e-03 ell= 534.99 R*=    3.134 at R=32
baFMz-consistent (sz.lam=g, g0=sqrt(t0) g, t<=min(t0,1-g^2)): R*
  g=0.01562 t_b=0.6937 ell=g0/sqrt(1-tb)=0.024 (<=sqrt(t0)=0.833) R*=1.0010
$ python3 prefl.py E | sed -n '2,7p'
  ell=   8 R=      16 L>=32 F=    438.8 lower bound on ratio=4.458e-02
  ell=  20 R=     100 L>=200 F=   1742.4 lower bound on ratio=2.276e-01
  ell=  40 R=     400 L>=800 F=   3522.9 lower bound on ratio=8.535e+00
  ell=  80 R=    1600 L>=3200 F=   5088.1 lower bound on ratio=3.394e+04
  ell= 160 R=    6400 L>=12800 F=   5687.6 lower bound on ratio=2.301e+12
  ell= 320 R=   25600 L>=51200 F=   5762.2 lower bound on ratio=6.859e+28
```
External hypotheses, concrete limit: the closure arithmetic `N^tau C (1+log W+W^(2 eps0)(lam^2 W^d)^(-1/4)) < W^eps0` holds from `log10 W >= 381.9` (`C=1`, `tau=eps0/24`) and stays true for `10x` larger `n` (line `closure`); it is a conclusion-internal eventual step (as in `pfStep5Alg_inst_closure`, `PfStep5Alg:774`), not a witness required by the hypotheses. The probabilistic pins (P1 clause 4, P5, U6) have no finite-size check here.
Not decided by this 1a (1b of the design ticket): U5-2 (the `E` bounds with non-scalar `M`), U5-3 (QV/flow bounds, closure at BA), the far-field route (`BAKellStarEv` vs `baEMn2ExpHK`).

### Verdicts
- `STPfStep5gL` at the BA tuple: **PASS** (regime nonempty at `sz0`, `t=1/2`; every exponent row closes; kernel constants bounded in `L` where the regime is nonempty: g=1/64, g=1 under the `g0` reading). Notes: (1) g=1 under `sz.lam` and g=10 under both readings are empty (as the ticket expects); g=10 record `C_U` still rises 8.6% from L=128 to 256. (2) The closure threshold `log10 W >= 382` is eventual. (3) H249 (3): no, see above.
- `STStep5IIIgL` at the BA tuple: **PASS** (same data; same hypotheses; conclusions `STStep5ConclgL` (check:196) vs `STPfConclgL` (check:254); in the band `ST_step5_caseIII_of_pf` (`Step5Cases:311`) derives III from Pf and its body (`:311-330`) reads `hflow.1` (Admissible) and `hPfc`; BA reading unchecked here).

## (a′) Preflight corrections — Mon Oct 12 17:33:36 UTC 2026
Section (a)(ii) lists "U6 statements (T2458, unmerged)" among the inputs without producer. U6 was already merged when (a) was written (a: Mon Oct 12 15:16:44 UTC 2026):
```
$ git -C /Users/junyin/Lean_proof/RBM3D log -1 --format='%h %cd %s' 1debc23
1debc23 Mon Oct 12 08:05:25 2026 -0700 T2458: merge U U6 Chain/Step5Gen
$ git merge-base --is-ancestor 1debc23 t/T2459 && echo '1debc23 is an ancestor of t/T2459'
1debc23 is an ancestor of t/T2459
```
(1debc23 = 15:05:25 UTC.) No verdict of (a) changes: the probe uses U6's statements by name. (a)(ii) also lists P5 `BAKellStarEv` as an input; the design does not need it (design report U5-2, `T2459_Theta_far`).

## (b) Script output (report-only design ticket: the deliverable is `docs/reports/T2459-design.md` plus the probe)
All commands at the worktree root `/Users/junyin/Lean_proof/RBM3D-wt/T2459`, branch `t/T2459`. Build, axioms, name clash (`bash docs/reports/T2459/probe_check.sh`, verbatim from `docs/reports/T2459/out/probe_check.out`):
```
$ bash docs/reports/T2459/probe_check.sh
lines:      394
lake env lean RBM3D/Probe/T2459Pins.lean: exit=0, output lines=       0
lake build RBM3D.Probe.T2459Pins: exit=0, last line: Build completed successfully (4065 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs/abbrevs: 26, theorems: 11, examples: 9
T2459_flowFacts_BA: [propext, Classical.choice, Quot.sound]
T2459_lam0_le_lam: [propext, Classical.choice, Quot.sound]
T2459_kernel_at_flow: [propext, Classical.choice, Quot.sound]
T2459_sz0_lam_le: [propext, Classical.choice, Quot.sound]
T2459_scalar_sz0: [propext, Classical.choice, Quot.sound]
T2459_main_of_parts: [propext, Classical.choice, Quot.sound]
T2459_Theta_far: [propext, Classical.choice, Quot.sound]
T2459_trace_mul_le: [propext, Classical.choice, Quot.sound]
T2459_trace_mul3_le: [propext, Classical.choice, Quot.sound]
T2459_reg_sz0: [propext, Classical.choice, Quot.sound]
T2459_inst_IngR5: [propext, Classical.choice, Quot.sound]
--- name clash: declarations named T2459_* / T2459u4_* / T2459u6_* on main and on the sibling branches that exist (absent = no such branch)
main:0 t/T2450:0 t/T2452:0 t/T2454:0 t/T2455:0 t/T2456:0 t/T2457:0 t/T2458:0 t/T2460:0 t/T2461:0 t/T2462:0 t/T2463:absent 
references to T2459Pins or BA/Step5III on main: 0
$ lake build RBM3D.Probe.T2459Pins 2>&1 | tail -1
Build completed successfully (4065 jobs).
```
Statements (`bash docs/reports/T2459/statements.sh`, the two BA targets and five central pins, from the def line to the next blank line or declaration):
```
--- statements (def blocks of RBM3D/Probe/T2459Pins.lean, from the def line to the next blank line or declaration)
def T2459_STPfStep5BA : Prop := STPfStep5gL 3 (T2459_law 3) (T2459_Flow 3) baFMz BAflowT0
def T2459_STStep5IIIBA : Prop := STStep5IIIgL 3 (T2459_law 3) (T2459_Flow 3) baFMz BAflowT0
def T2459_BAKernel (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D s t : ℝ),
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
    0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFM sz lam0 E) n Cc D s t
def T2459_BAEdet (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    T2459_BAscalar sz n u D Λ K₀ J → T2459_BAmatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
        lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a) ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
        lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)) ∧
    (∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2))
def T2459_BAgoodThm : Prop :=
  ∀ (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
    (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t → STKboundgL (baFMz sz z) (T2459_law 3 sz) → STAvgUgL (baFMz sz z) (T2459_law 3 sz) s t →
    T2459_LmaxU (baFMz sz z) (T2459_law 3 sz) s t → T2459_LKU (baFMz sz z) (T2459_law 3 sz) s t →
    STGdecayWgL (baFMz sz z) (T2459_law 3 sz) s t Cd → ∀ D : ℝ, 0 < D → T2459_BAgood sz z s t D Cd
def T2459_BAfromWalk : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
    (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
    T2459_BAWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t → STPfConclgL (baFMz sz z) (T2459_law 3 sz) s t
def T2459_P1 : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAtgL 3 2 C₀ (T2459_Flow 3) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0
```
Compiled instances (the same script; line numbers in the probe; each applies a pin at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/10 < t ≡ 1/2 < t0`, the deterministic hypotheses discharged, other gates' stochastic pins as hypotheses):
```
--- instances (examples and instance theorems; first line and the line number in RBM3D/Probe/T2459Pins.lean)
52:theorem T2459_flowFacts_BA : T2459u4_FlowFacts 3 (T2459_Flow 3) baFMz BAflowT0 := fun κ hκ =>
84:theorem T2459_kernel_at_flow (hK : T2459_BAKernel 3) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
154:theorem T2459_scalar_sz0 : T2459_BAscalar SizesInst.sz0 1 (1 / 2) 40 1 1 1 := by
234:example (hcl : T2459_BAclosure) (hP1 : T2459_P1) (hK : T2459_BAKernel 3) (hE : T2459_BAEdet 3) (hg : T2459_BAgoodThm)
242:theorem T2459_Theta_far {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ}
315:theorem T2459_reg_sz0 : STReg5III SizesInst.sz0 T2459_s0 T2459_t0 := fun n => by
328:theorem T2459_inst_IngR5 {Concl : ∀ (sz : Sizes 3) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop}
338:example (h : T2459_STPfStep5BA) (hp : T2459_prem) : STPfConclgL T2459_C0 T2459_μ0 T2459_s0 T2459_t0 :=
342:example (hs : T2459_caseIII_succ 3 (T2459_law 3) (T2459_Flow 3) baFMz BAflowT0) (hpf : T2459_STPfStep5BA) : T2459_STStep5IIIBA :=
346:example (hw : T2459_BAweighted 3) : ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t < 1 → SizesInst.sz0.lam n ^ 2 ≤ 1 - t →
357:example (hK : T2459_BAKernel 3) : ∃ Cc : ℝ, 0 < Cc ∧ ∀ᶠ n in atTop, ∀ D : ℝ, STTailtoTailConclgL T2459_C0 n Cc D (1 / 10) (1 / 2) := by
364:example (hE : T2459_BAEdet 3) (H : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ)
373:example (hg : T2459_BAgoodThm) (hp : T2459_prem) : T2459_BAgood SizesInst.sz0 FlowPinsInst.zSeq T2459_s0 T2459_t0 1 1 := by
379:example (h : T2459_BAWalk) (hf : T2459_BAfromWalk) (hp : T2459_prem) : STPfConclgL T2459_C0 T2459_μ0 T2459_s0 T2459_t0 :=
384:example : ∀ᶠ n in atTop, ∀ (x x' : Zd 3 (SizesInst.sz0.L n)) (s : Bool), x ≠ x' →
```
Ports and scope:
```
$ grep -c 'RBM1D\|RBM2D' RBM3D/Probe/T2459Pins.lean
0
$ git diff --name-only main...t/T2459 | grep -v '^docs/reports/T2459/'; (count of files under docs/reports/T2459/)
RBM3D/Probe/T2459Pins.lean
docs/reports/T2459-design.md
docs/reports/T2459/: 28 files
$ git log --oneline main..t/T2459 | cut -c1-110
2a6ad6e T2459: design report header wording
83cd61a T2459: design report, verification level and wording
4d36b3d T2459: design report regenerated from the final outputs
8a792bc T2459: design report refresh (J-free input wording, T2459f, citations)
914f017 T2459: statements and Mathlib-name scripts and outputs, design report refresh
ed53f66 T2459: design report docs/reports/T2459-design.md, probe with the J-free long-leg input and instances,
aff844c T2459: probe RBM3D/Probe/T2459Pins.lean (382 lines) and scripts under docs/reports/T2459/ (design gate
$ wc -l docs/reports/T2459-design.md RBM3D/Probe/T2459Pins.lean
     321 docs/reports/T2459-design.md
     394 RBM3D/Probe/T2459Pins.lean
     715 total
```
No port from RBM1D or RBM2D (count 0, no diff-stat needed). The probe is never merged (ticket); `lake build` of the full library is the hub's merge step and is not needed for a report-only merge.

Narrative (facts; the numbers are in the blocks above and in the design report):
- Deliverables on `t/T2459`: `docs/reports/T2459-design.md` (first line = verdict, regime reading, 1b rows and central), `RBM3D/Probe/T2459Pins.lean`, scripts and verbatim outputs in `docs/reports/T2459/` (`run_all.sh` regenerates them; `cite.sh`, `cite_lines.py` print the file:line evidence).
- Verdict: BA case (iii) of Step 5 closes at paper level with named inputs: P1 = T2460 target 4 (kept: H249 (3) answered no), U4s1's `T2462_caseIII` (its premise `T2462_FlowFacts` is proved at BA by merged names, `T2459_flowFacts_BA`), and the Steps 1-4 premises of `STIngR5gL`. No stop rule fired.
- Verification level: U5-1 and U5-2 are derived by hand from the cited merged statements; compiled are the pins, the instances, `T2459_Theta_far`, `T2459_flowFacts_BA` and the Hilbert-Schmidt trace bound.
- H250 (3) (UBA-C4): the kernel is read at `g0 <= g` (`T2459_lam0_le_lam`), the regime at `g = sz.lam`, and the constant `A = (kappa+1)/kappa` does not enter (C1 table, design report U5-5).
- H250 (4): the fill-in table is the end of the design report (section (f)); every row has a line reference or "n/a, because".
- The pin `T2459_BAmatrix` carries a J-free long-leg decay (vi) from `STLKU` (k = 2) and `STGdecayWgL`; without it the near configuration of `dif` carries `J^2` on the indicator term and the closure fails (design report U5-2). The pin `T2459_BAEdet` has the extra factor `W^(2 theta d (Cd+1)) Sum_y e^(-(theta/2) sqrt|y|)` in `dif`.
- Judgement calls the dispatcher may overrule: (1) at g = 10 the record constants `CU` grow with L (1.63 to 4.01, L = 4..256) but the regime is empty under both readings, so ticket stop rule 3 is not applied (design report (f)); (2) P5 `BAKellStarEv` is dropped for the K-level `baEMn2ExpHK`, which moves the `lem_dec_calE` cut-offs to `2 l*`, `6 l*` (T2459b); (3) the free-`lam0` shape of T2458-check:462 is judged false by a continuum argument only (lattice numerics cannot reach it).
- Probe content: 26 defs/abbrevs, 11 theorems with the three standard axioms, 9 examples. Instances exist for every pin except `T2459_P1` (an unmerged row's pin: hypothesis of exact type) and the matrix part of `T2459_BAmatrix` (a hypothesis of the ℰ-bounds instance: `BAKloop` is choice-valued, `FlowPins:298`, `KSolve:606`, no evaluation at concrete data is merged).
- U6 re-check: Part 2 of `docs/tickets/checks/T2458-check.lean` against merged `Chain/Step5Gen.lean`: 11 `Iff.rfl`, exit 0 (`out/u6_recheck.out`).
- U5's 1b: 5 rows, 4,650 / 6,900 / 10,600 lines (lo / central / hi); inputs without producer: none (design report (d)).

## (c) Verified Mathlib names used (resolved by Lean: module and line of the declaration; `lake env lean docs/reports/T2459/names.lean`)
```
Matrix.frobenius_norm_def: Mathlib.Analysis.Matrix.Normed:561
Matrix.frobenius_norm_mul: Mathlib.Analysis.Matrix.Normed:657
Matrix.diag_apply: Mathlib.Data.Matrix.Diagonal:292
Matrix.mul_apply: Mathlib.Data.Matrix.Mul:298
Matrix.mul_assoc: Mathlib.Data.Matrix.Mul:482
Matrix.one_apply_ne: Mathlib.Data.Matrix.Diagonal:241
Matrix.add_apply: Mathlib.LinearAlgebra.Matrix.Defs:297
Matrix.smul_apply: Mathlib.LinearAlgebra.Matrix.Defs:301
Finset.sum_mul_sq_le_sq_mul_sq: Mathlib.Algebra.Order.BigOperators.Ring.Finset:170
Finset.sum_comm: Mathlib.Algebra.BigOperators.Group.Finset.Sigma:120
Finset.sum_le_sum: Mathlib.Algebra.Order.BigOperators.Group.Finset:110
Finset.sum_nonneg: Mathlib.Algebra.Order.BigOperators.Group.Finset:151
norm_sum_le: Mathlib.Analysis.Normed.Group.Basic:808
Fintype.sum_prod_type: Mathlib.Data.Fintype.BigOperators:272
Real.sqrt_eq_rpow: Mathlib.Analysis.SpecialFunctions.Pow.Real:986
Real.sqrt_mul: Mathlib.Analysis.Real.Sqrt:365
Real.le_sqrt_of_sq_le: Mathlib.Analysis.Real.Sqrt:258
Real.rpow_natCast: Mathlib.Analysis.SpecialFunctions.Pow.Real:61
Real.one_le_rpow: Mathlib.Analysis.SpecialFunctions.Pow.Real:678
Real.rpow_le_rpow_of_exponent_le: Mathlib.Analysis.SpecialFunctions.Pow.Real:616
Real.log_two_gt_d9: Mathlib.Analysis.Complex.ExponentialBounds:83
Real.log_pow: Mathlib.Analysis.SpecialFunctions.Log.Basic:287
Real.norm_of_nonneg: Mathlib.Analysis.Normed.Group.Real:62
Complex.norm_real: Mathlib.Analysis.Complex.Norm:104
Complex.norm_natCast: Mathlib.Analysis.Complex.Norm:114
pow_le_pow_iff_left₀: Mathlib.Algebra.Order.GroupWithZero.Basic:682
pow_le_pow_left₀: Mathlib.Algebra.Order.GroupWithZero.Basic:513
inv_anti₀: Mathlib.Algebra.Order.GroupWithZero.Basic:1220
mul_nonpos_of_nonneg_of_nonpos: Mathlib.Algebra.Order.GroupWithZero.Basic:69
mul_le_mul_of_nonneg_left: Mathlib.Algebra.Order.GroupWithZero.Defs:225
mul_le_mul_of_nonneg_right: Mathlib.Algebra.Order.GroupWithZero.Defs:229
Matrix.trace_mul_le_frobenius_norm: ABSENT
Matrix.abs_trace_mul_le: ABSENT
Matrix.norm_trace_mul_le: ABSENT
Matrix.trace_mul_le_norm_mul_norm: ABSENT
```
The four `ABSENT` names are Hilbert-Schmidt trace Cauchy-Schwarz lemmas that were searched and do not exist; `T2459_trace_mul_le` is proved from `Finset.sum_mul_sq_le_sq_mul_sq`.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates (ready-to-paste text in the design report (e)): `T2459a` (the omitted BA argument of `sec:Step5_larget`, `7_8:2101`), `T2459b` (cut-offs `2 l*`, `6 l*`), `T2459c` (loop-level Hilbert-Schmidt route, no `lem_GbEXP_BA` in case (iii)), `T2459d` (free-`lam0` shape expected false), `T2459e` (Theta-level far field from the K-level one), `T2459f` (extra `W^(2 theta d (Cd+1))` factor in `dif`).
- Open: (1) no witness for the matrix part of `T2459_BAmatrix`, no instance of `T2459_P1`; (2) the derivation of (vi) by interpolation and the lattice sum `S_theta` (rate `theta/2`) are stated in the design report, not compiled (no merged lemma at that rate); (3) `lossE2wG` is the loss budget by a design-level count, a primed loss is the fallback; (4) H249 (3) "no" and the free-`lam0` shape are argument sketches with numerics as proxies; (5) the g = 10 judgement above; (6) the ticket's drafting count 23 for `|E| < 2` is not reproduced (17 literal, 59 with `<` or `≤`).
