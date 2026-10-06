Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 10:11:50 UTC 2026

### (i) Exponent table

Notation: `N = 2^21`, `W = 32 = N^{5/21}` (`log_N 2 = 1/21 = 0.0476`), `k = m+2 = 3`, `C₄ = qProxy4C 3 3 10 (1/2) 1`,
`C_n = qProxyCn 3 2 10 1 1 (1/2)`, `C_Q = qProxyCQ = 2C_n+2` (`QProxy.lean:440`), both constants `> 0` (`qProxy4C_pos`,
`qProxyCn_pos` at `d=3, 2≤k, Λg=10, κ'=1/2, KL=1, C=1, c=1/2`), `ε₀ = C₄ + C_n + 12`. `log_N 6 = 0.123`, `log_N 12 = 0.171`.
`Ls = Im m(1/2)⁻¹ log N = 15.03` (`Im m(1/2) = √15/4`; the merged `Ls_bounds` gives `14 ≤ Ls ≤ 16`).

| quantity | value | constraint | slack |
|---|---|---|---|
| `n, L, W, N, g=lam n` | `0, 4, 32, 2^21, 1/64` (`sz0_values`) | `W = N^{5/21}` | — |
| `E, s, v, K, Δ` | `1/2, 0, 1/32, 4, 1/128` | `\|E\|<2`, `0≤s≤v<1`, `K≠0`, `KΔ = v−s = 0.0313` | `1−v = 0.969` |
| `η_v⁻¹` | `1.0661` | `≤ N` | `N/η_v⁻¹ ≈ 2·10^6` |
| `Δ η_v⁻¹` | `0.00833` | `≤ 1` | `0.992` |
| `ε` (kernel), `ε₁`, `Γ`, `Λ` | `4/5`, `2/21`, `N^{2/21} = 4`, `3` | `Γ = N^{ε₁}`, `1 ≤ Λ`, `0 ≤ ε₁` | `Λ−1 = 2` |
| `εq, D_Y, D_t, τ_K` | `1, 1, −5, 1/21` | `hR`: `Σ ≤ N^{−D_t} = N^5` (merged `NQBudgetInst.hR_instance`, stated at `k=3`, `τ_K = 1/21`, `N^{−(−5)}`, `NQBudget.lean:1241-1247`) | docstring there: `~2^100` vs `2^105` |
| `hlog` | `Σ_{j<4}Δ/η_{u_j} = 0.0327` | `≤ Ls = 15.03` (merged `hlog_instance`, `NQBudget.lean:1271`) | `15.0` |
| `Σ_jΔ/η_{u_{j+1}}` (QV step) | `0.0329` | `≤ hlog + 1` (`nqBudget_sum_succ_le`, needs `Δ/η_v ≤ 1`) | `0.97` |
| `δ0 = δD`, `D'` | `4W^{−6}`, `6` | `≥ 0` | — |
| `D''` | `5` | only an exponent in target 10 (no `hD` there); see the note below: S3-18a's `hD` needs `D'' > m+3+C_Q = 6+2C_n` | `D'' = 7+2C_n` gives `W^{−D''+C_Q} = W^{−5}`, `he2` slack `5.39` (vs `5.15`) |
| drift level data `(Γ,Φ₁,Φ₂,Φ₃,C_n',ε',D',τ_N,X)` | `(4,1,12,1,C_n,1/5,6,1,1)` | target 8 premises `\|E\|<2`, `u<1`, `Φ_i, X ≥ 0` | — |
| `Pa` (target 8) | `W^{C_n/5}·Γ²·k + N^{τ_N} = 48W^{C_n/5} + N` | `≥ 0` | — |
| `Φd` | `Φ₁+Φ₂+Φ₃+X = 15` | `≥ 0` | — |
| `b` | `W^{−D'+C_n} = W^{−6+C_n}` | `≥ 0` | — |
| `X0` | `4 B_s^3 = N^{ε₁} B_s^3` | `hX0: X0 ≤ N^{ε₁}B_s^k` | equality (0) |
| `altBudget_kapFar` | `W^{0.8C₄}((1+g²)N)^3`, `(1+g²)^3 = 1.0007` | `κ ≤ kapFar` for `0≤u_i≤u_m<1`, `(1−u_m)⁻¹ ≤ N` | `r ≤ (1+g²)(1−u_m)⁻¹ ≤ (1+g²)N` |

Absorption rows (target 10; `log_N` of the left side, `+log_N q` for the `/q`, against `ε₀ = C₄+C_n+12`). Formulas are the
pinned hypotheses of the check file, evaluated by `inst.py` (below) with the exact `Pa`, `kapFar`, `qvFar`, `Ls`:

| row | pinned left side at the data | `log_N(LHS·q)` bound | slack at `C₄=C_n=0` | slope of slack in `C₄`, `C_n` |
|---|---|---|---|---|
| `ha1` (`q=6`) | `W^{0.8C₄}N^{2/21}` | `0.095 + 0.190C₄ + 0.123` | `11.78` | `0.81, 1.00` |
| `ha2` (`q=12`) | `W^{0.8C₄}·Pa·Ls`, `Pa = 48W^{C_n/5}+N` | `≤ 1.186 + 0.190C₄ + 0.047C_n + 0.171` (the `N` branch dominates) | `10.64` | `0.81, 0.95` |
| `ha3` (`q=12`) | `N·W^{0.8C₄}W^{0.8C_n}N^{2/21}√(3(Ls+1))` | `1.228 + 0.190C₄ + 0.190C_n + 0.171` | `10.60` | `0.81, 0.81` |
| `he0` (`q=12`) | `N^3 W^{C₄}·4W^{−6}` | `1.667 + 0.238C₄ + 0.171` | `10.16` | `0.76, 1.00` |
| `he1` (`q=12`) | `N^3(kapFar·W^{−6+C_n} + W^{C₄}·4W^{−6})` | `4.571 + 0.235C₄ + 0.238C_n + 0.171` | `7.26` | `0.76, 0.76` |
| `he2` (`q=12`) | `N·N^3·√(3·qvFar·W^{−5+C_Q})`, `qvFar ≈ N^{0.428C₄+6}` | `6.681 + 0.213C₄ + 0.238C_n + 0.171` | `5.15` | `0.79, 0.76` |
| `he3` (`q=6`) | `N^3·N^{−1}` | `2 + 0.123` | `9.88` | `1, 1` |
| `he4` (`q=6`) | `N^3·N^{5}` | `8 + 0.123` | `3.88` (smallest) | `1, 1` |

Every slack slope is `> 0`: each left side is a log-sum-exp of affine functions of `(C₄,C_n)` whose slopes (in `N`-exponent units) are at most `0.238 < 1`, so
the slack is nondecreasing in `C₄, C_n ≥ 0`, and the minimum over `C₄, C_n ≥ 0` is at `(0,0)`: `3.88 (he4)`. Hence all eight absorption
inequalities hold for every positive `C₄, C_n` (the abstract `Classical.choose` constants), with no size assumption on them.

Identities used by targets 4-9 (checked in (ii) by script): target 4 `qvBdAltQN = nqBudget_qvShape` with `κ = W^{C₄ε}r^k`, `Ce = W^{C₄}`,
`Cc = W^{C₄}W^k`, `G = W^{2C_nε}(Γ(ΓΛ))`, `Wd = W^{−D''+C_Q}` is a ring identity (associativity of products, `B^{2(m+2)}` same on both sides).
`altBudget_qvFar = kapFar(kapFar + W^{C₄}) + W^{C₄}W^k` is `Cfar(Cfar+Ce)+Cc` of `tbQvN` by definition. Target 8: `(k−2)Φ₁+Φ₂+Φ₃ ≤ k(Φ₁+Φ₂+Φ₃+X)`
and `N^{τ_N}η⁻¹B^kX ≤ N^{τ_N}(Φ₁+Φ₂+Φ₃+X)B^k/η` (needs `η>0`: `|E|<2`, `u<1`). Target 9: `(k−1)+kΓΦ ≤ k(1+ΓΦ)` and the same `X` step.
Kernel: `r B_{u_i} ≤ B_{u_m}` is `nqGood2_ratio_mul_Bctl_le` (every real `g`), `(rB)^k ≤ B'^k` for `0 ≤ rB`; far bound `r ≤ (1+g²)(1−u_m)⁻¹`.
Bookkeeping of target 10: `t₁ ≤ P₀X/6` (`ha1`), `t₂ ≤ P₀X/12` (`he0`, `ε_{0,K} = W^{C₄}`), `t₃ ≤ P₀ΦdX/12 + P₀X/12` (`ha2`, `he1`), `t₄ ≤ P₀Λ^{1/2}X/12 + P₀X/12`
(`ha3`, `he2`, `√(x+y) ≤ √x+√y`), `t₅,t₆ ≤ P₀X/6` (`he3`,`he4`); total coefficient `≤ 1` after `X ≤ Λ^{1/2}X` (`1 ≤ Λ`); `N^{−k} ≤ B_v^k`
as in `budgetNonAltLinN` (`ContinuityNet.cont_inv_size_le_Bctl`, `NQLin.lean:1026-1029`).

### (ii) One concrete nondegenerate instance

Data: `d=3`, `sz0`, `n=0`, label `aFar : Fin (1+1+1) → Zd 3 (sz0.L 0)` (nonempty), `m=1` (`k=3`), `E=1/2`, grid `(sInst, vg, Kg)`: `u_j = j/128`, `K=4`,
`Λg=10, κ'=1/2, KL=1, C=1, c=1/2, ε=4/5`, `Γ=4, Λ=3`, `Φ₁=Φ₃=1, Φ₂=12, X=1`, `C_n' = C_n`, `ε'=1/5`, `D'=6`, `D''=5`, `D_Y=1`, `D_t=−5`, `τ_K=1/21`, `εq=1`, `τ_N=1`, `ε₁=2/21`,
`ε₀ = C₄+C_n+12`, `X0 = 4B_0^3`, `δ0 = δD = 4W^{−6}`, `dd j = dDriftAltLinQN(u_j)` (so `dd j ≤ Pa·15·B_{u_j}^3/η_{u_j} + W^{−6+C_n}` by target 8).
All hypotheses of target 10 hold: positivity/range rows `0≤ε₁`, `|E|<2`, `0≤s≤v<1`, `K≠0`, `η_v⁻¹≤N`, `Δη_v⁻¹≤1`, `Γ=N^{ε₁}`, `1≤Λ`, `Pa,Φd,b,δ0,δD ≥ 0`, `hdd`, `hlog`,
`hX0` (equality), `hR` and `ha1…he4` for every `C₄,C_n>0`. No `N=0`, no empty window (`K=4`, `KΔ = 1/32`), no `False` premise.
Targets 1-3 at `u = gridTime sInst vg Kg 0`, `(i,m) = (0,4)`, `k=3`: `0 ≤ u_0 ≤ u_4 = 1/32 < 1`, `(1−u_4)⁻¹ = 1.03 ≤ N`. Targets 5-7 at the same data.
Targets 8, 9 at `u=0`, `E=1/2`, `m=1`: `|E|<2`, `u<1`, `Φ_i, X, Γ ≥ 0`. External hypotheses: none of the targets takes an unproved pin; `hlog` and `hR` are discharged by the
merged theorems `NQBudgetInst.hlog_instance`, `hR_instance` (both at this very data, `k=3`, `τ_K=1/21`, `D_t=−5`; statement of `hR_instance` at `NQBudget.lean:1241-1247`).

Command and output (scratch scripts in the scratchpad `T2279/`; exact log-space evaluation of the pinned left sides; Lean's `Ls ≤ 16` bound is weaker than the `15.03` used here):

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2279/inst.py
Im m(1/2)=0.968246  Ls=15.0335  log_N 2=0.047619
eta_v^-1=1.0661 <= N: True ; Delta*eta_v^-1=0.00833 <=1: True
hlog sum_j<4 D/eta_uj=0.03266 <= Ls: True ; sum D/eta_u(j+1)=0.03292 <= hlog+1: True
K*Delta=0.03125 = v-s ; Gamma=N^(2/21)=4.000000 ; Lambda=3>=1
slack in N-exponent units (=(rhs-lhs)/21) at (C4,Cn); lhs/rhs are log2:
(0, 0) {'ha1': 11.782, 'ha2': 10.643, 'ha3': 10.601, 'he0': 10.163, 'he1': 7.258, 'he2': 5.149, 'he3': 9.877, 'he4': 3.877} min>0: True
(1, 1) {'ha1': 13.591, 'ha2': 12.453, 'ha3': 12.22, 'he0': 11.925, 'he1': 8.829, 'he2': 6.72, 'he3': 11.877, 'he4': 5.877} min>0: True
(5, 0) {'ha1': 15.829, 'ha2': 14.691, 'ha3': 14.649, 'he0': 13.972, 'he1': 11.305, 'he2': 9.196, 'he3': 14.877, 'he4': 8.877} min>0: True
(0, 5) {'ha1': 16.782, 'ha2': 15.643, 'ha3': 14.649, 'he0': 15.163, 'he1': 11.067, 'he2': 8.958, 'he3': 14.877, 'he4': 8.877} min>0: True
(1000, 1000) {'ha1': 1821.305, 'ha2': 1773.282, 'ha3': 1629.649, 'he0': 1772.067, 'he1': 1578.686, 'he2': 1554.268, 'he3': 2009.877, 'he4': 2003.877} min>0: True
slack slope per unit C4 / Cn in N-exponent (>=0 means closes for all C4,Cn>=0):
ha1 0.8095 1.0
ha2 0.8095 0.9531
ha3 0.8095 0.8095
he0 0.7619 1.0
he1 0.7648 0.7619
he2 0.7872 0.7619
he3 1.0 1.0
he4 1.0 1.0
grid minimum slack (N-exponent): (3.8769065475847064, 'he4', 0, 0)
variant D''=7+2Cn: W^(-D''+C_Q)=W^-5; he2 slack (N-exponent):
[(0, 0, 5.387), (1, 1, 7.196), (10, 10, 23.482)]
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2279/algebra.py
target4 m=0 (k=2): qvBdAltQN == nqBudget_qvShape at 1000 exact rational points: True
target4 m=1 (k=3): qvBdAltQN == nqBudget_qvShape at 1000 exact rational points: True
target 8: min(rhs-lhs) over 2e5 samples = 0.0345 (>=0)
target 9: min(rhs-lhs) over 2e5 samples = 0.00549 (>=0)
```

### Note for stage 1b (mathematics; not a correction to (a))
With the ticket's `D'' = 5`, target 10 holds, but S3-18a later needs `hD : (m+1)+2+C_Q < D''` of `qvFormQN_le_of_goodSetN` at `m ↦ m+1`, i.e. `D'' > 6+2C_n`.
`D'' = 7+2C_n` (so `−D''+C_Q = −5`) satisfies it and makes `he2` strictly easier (slack `5.39`); stage 1b may use it for the compiled instance.

### Verdicts
- Targets 0 (vocabulary), 1, 2, 3, 4, 5, 6, 7, 8, 9, 10: PASS. Each statement is true as pinned: kernel and QV from the merged `r B_u ≤ B_t`, `tbDriftN`, `tbQvN`;
  `kappaAltQN` is `W^{C₄ε}r^k` and `epsAltQN = W^{C₄}` (`QDriftA.lean:100-105`); `qProxyCQ = 2C_n+2`; target 10's eight absorption hypotheses are simultaneously satisfiable
  (smallest slack `3.88`, row `he4`) for all positive `C₄, C_n`. The drift level `dd j` enters generically, so target 10 does not need `Φ²`.
- Overall: PASS.

## (a′) Preflight corrections

None. Every value of (a) used here was reproduced in Lean (the eight absorption inequalities hold for all `C₄, C_n > 0`, private
lemmas `ha1_inst`-`he4_inst`, `QBudgetA.lean:1020-1173`). The one deviation from the ticket's data is not a correction of (a): see narrative 5.

## (b) Script output (report finalised Tue Oct  6 10:38:13 UTC 2026; commit time from git below)

```
$ lake build RBM3D.Induction.QBudgetA 2>&1 | tail -3
info: RBM3D/Induction/QBudgetA.lean:1338:0: 'RBM.Ind.budgetAltQN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QBudgetA.lean:1339:0: 'RBM.Ind.QBudgetAInst.budgetAltQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3861 jobs).
$ lake build RBM3D.Induction.QBudgetA 2>&1 | grep "QBudgetA.lean" | grep -c "warning\|error"
0
$ lake env lean RBM3D/Induction/QBudgetA.lean 2>&1 | grep -v "depends on axioms" | wc -l   # fresh elaboration of the file
       0
$ grep -c "sorry\|admit\|native_decide\|^axiom\|maxHeartbeats" RBM3D/Induction/QBudgetA.lean
0
$ wc -l RBM3D/Induction/QBudgetA.lean
    1339 RBM3D/Induction/QBudgetA.lean
```

```
$ lake env lean RBM3D/Induction/QBudgetA.lean 2>&1 | grep "depends on axioms" | sed "s/.*axioms: //" | sort | uniq -c
  17 [propext, Classical.choice, Quot.sound]
$ grep -c "#print axioms" RBM3D/Induction/QBudgetA.lean
17
```

Target statements (`theorem NAME :` at lines 137, 154, 171, 235, 251, 273, 341, 419, 469, 575 for targets 1-10; vocabulary `def`s at lines 57, 63, 70, 86, 94, 104).
The statements are not reprinted: each is byte-identical to the `Prop` body of `docs/tickets/checks/T2279-check.lean:173-325`, and §2 is copied verbatim (script):

```
$ python3 stmtdiff.py   # check-file §2 verbatim, §3 Prop bodies vs theorem statements (exact text)
vocabulary (check lines 107-171, 6 defs) verbatim in QBudgetA.lean: True
kappaAltQN_mul_Bctl_pow_le: True
kappaAltQN_succ_mul_Bctl_pow_le: True
kappaAltQN_le_kapFar: True
qvBdAltQN_eq_qvShape: True
tbInitAltQN: True
tbDriftAltQN: True
tbQvAltQN: True
dDriftAltLinQN_le_shape: True
dDriftAltQN_le_shape: True
budgetAltQN: True
ALL IDENTICAL: True
$ lake env lean StmtCheck.lean > out 2>&1; echo exit=$?; grep -v "longLine\|exceeds\|^$\|^Note" out | wc -l   # check file §3 + `theorem chk_X : T2279_X := @X` (ten targets), importing QBudgetA
exit=0
       0
```

Commit, instance statement (target 10; the abstract constants `C4₀ = qProxy4C 3 3 10 (1/2) 1`, `Cn₀ = qProxyCn 3 2 10 1 1 (1/2)`, both proved `> 0`
by `qProxy4C_pos`, `qProxyCn_pos`), and the list of instances:

```
$ git diff --stat main...t/T2279 | cat; git log -1 --format="%h %cd" --date=format-local:"%Y-%m-%d %H:%M:%S UTC"   # TZ=UTC
 RBM3D/Induction/QBudgetA.lean | 1339 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1339 insertions(+)
284e06f 2026-10-06 10:31:49 UTC
$ grep -n "local notation" RBM3D/Induction/QBudgetA.lean; sed -n "1290,1297p" RBM3D/Induction/QBudgetA.lean   # target 10 instance statement
1177:local notation "C4₀" => qProxy4C 3 (1 + 1 + 1) 10 (1 / 2) 1
1178:local notation "Cn₀" => qProxyCn 3 (1 + 1) 10 1 1 (1 / 2)
theorem budgetAltQN_instance :
    assembledRHSAltQN sz0 Einst sInst vg Kg 0 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5) Γ4 Λ3
        (fun j => dDriftAltLinQN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn₀
          (1 / 5) 6 1 1)
        (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (7 + 2 * Cn₀) 1 (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4₀ + Cn₀ + 12) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + (1 + 12 + 1 + 1)) * (sz0.Bctl 0 (vg 0)) ^ (1 + 1 + 1) := by
$ grep -n "^example\|^theorem budgetAltQN_instance" RBM3D/Induction/QBudgetA.lean | cut -c1-72   # nonempty instances: targets 1-3, 4, 5, 6, 7, 8, 9, 10
1230:example : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) ((sz0.W 0 : ℕ) : 
1237:example : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) ((sz0.W 0 : ℕ) : 
1244:example : kappaAltQN 3 3 10 (1 / 2) 1 (sz0.lam 0) ((sz0.W 0 : ℕ) : 
1250:example : qvBdAltQN sz0 0 (1 / 2) 1 10 (1 / 2) 1 1 (1 / 2) (4 / 5) 
1262:example := tbInitAltQN sz0 (s := sInst) (v := vg) (K := Kg) 0 3 10 
1267:example := tbDriftAltQN sz0 (E := Einst) (s := sInst) (v := vg) (K 
1275:example := tbQvAltQN sz0 (E := Einst) (s := sInst) (v := vg) (K := 
1279:example := dDriftAltLinQN_le_shape sz0 0 (1 / 2) 0 1 4 1 12 1 Cn₀ (
1283:example := dDriftAltQN_le_shape sz0 0 (1 / 2) 0 1 4 1 Cn₀ (1 / 5) 6
1290:theorem budgetAltQN_instance :
```

```
$ name-clash grep (-F over RBM3D/ RBM3D.lean, main worktree and t/T2279 minus QBudgetA.lean)
19 names (16 public decls, QBudgetAInst, budgetAltQN_instance, prefix QBudgetA_): total hits outside QBudgetA.lean = 0
$ printf "import RBM3D
import RBM3D.Induction.QBudgetA

#assert_rbm_axioms
" > Registry.lean; lake env lean Registry.lean | head -3; echo exit=${pipestatus[1]}
axiom audit: 8060 theorems, 2642 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit=0
$ lake build 2>&1 | tail -1   # whole library (RBM3D.lean does not import QBudgetA before the hub merge)
Build completed successfully (4085 jobs).
$ lake env lean Consumer.lean; echo exit=$?   # three consumer checks (iii-a, iii-b, iii-c), scratch file
exit=0
$ lake env lean MathlibChk.lean; echo exit=$?   # #check of the 34 Mathlib names of (c)
exit=0
```

Ports: no text of RBM1D/RBM2D was copied or opened by stage 1b (no `git -C ../RBM*` command was run); the proofs are adaptations of merged RBM3D lemmas
(hashes `git log --oneline -1 -- <file>` in the worktree: `NQBudget.lean` 5b887a6, `NQLin.lean` d783ee3, `NQGood2.lean` cc96b69):
target 1-2 `kappaNonAltN_mul_Bctl_pow_le`, `_succ_` (`NQGood2.lean:188-217`) with exponent `k`; 3 `nqBudget_kappa_le_kapFar` (`NQBudget.lean:163`);
5 `tbInitNonAltN` (`:368`); 6 `tbDriftLinN` (`NQLin.lean:876`); 7 `tbQvNonAltN` (`NQBudget.lean:458`); 10 `budgetNonAltLinN` (`NQLin.lean:966-1235`), `nqLin_final`,
`nqLin_absorb`; instance helpers re-derived from the private lemmas of `NQLinInst` (`NQLin.lean:1256-1722`). RBM1D/RBM2D diff-stat: not applicable.

### Narrative
1. New file `RBM3D/Induction/QBudgetA.lean` only (1339 lines, one commit on `t/T2279`, hash above). Imports `QLevelsB`, `QProxy`, `NQLin` as pinned.
2. Targets 0-10: vocabulary verbatim; targets 1-10 proved with exactly the pinned statements (script diff and the compiled `chk_X : T2279_X := @X`). No new hypothesis,
   no weakened target, no changed pin. No `set_option maxHeartbeats` anywhere in the file (target 10 elaborates within the default limit).
3. Target 10 differs from `budgetNonAltLinN` as the ticket says: generic drift level (`hdd`, `Pa`, `Φd`, `b` as hypotheses), separate `δ0`, `δD`, the extra `he0` (`t₂`),
   the `b`-part of `he1`, and `W^{2C_nε} = (W^{C_nε})²` (`QBudgetA_rpow_two_mul`) so that `ha3` carries `W^{C₄ε} W^{C_nε}`. `QBudgetA_final` has one `Φd`.
4. `k = m + 1 + 1` is used in all statements; in targets 8-9 the term `η⁻¹ B^{m+2} X` of `dDriftAltLinQN`/`dDriftAltQN` is rewritten by `ring` (it identifies the
   exponents `m + 2` and `m + 1 + 1`, defeq in any case).
5. Instance data are those of (a)(ii) except `D'' = 7 + 2 C_n` (not `5`), as the "Note for stage 1b" in (a) allows: then `-D'' + C_Q = -5` (`hexp`, by `unfold qProxyCQ; ring`),
   and `D''` satisfies the premise `(m+1)+2+C_Q < D''` of `qvFormQN_le_of_goodSetN` at `m ↦ m+1` (`6 + 2C_n < 7 + 2C_n` at `m = 1`); (a) gives the `he2` slack `5.39` instead of `5.15`.
   `δ0 = δD = 4 W^{-6}` at the instance (merged `alt_hA0clsQN` gives `δ₀ = 2 W^{-D'}`, `QDriftA.lean:488-489`; `alt_hDclsQN` gives `δD = 4 W^{-D'}`, `QDriftB.lean:399-400`;
   the target takes both as free reals).
6. Instances: every deterministic hypothesis of targets 1-10 is discharged at `d = 3`, `sz0`, `n = 0`, `m = 1`, `K = 4` (`KΔ = 1/32`), `aFar` (nonempty label), `N = 2^21`;
   `hlog`, `hR` are the merged `NQBudgetInst.hlog_instance`, `hR_instance`; `hdd` is target 8 at each grid time (`hdd_inst`). No hypothesis is left open in the instances.
7. Consumer checks (preflight (iii) of the ticket; scratch file, not committed, compiled with exit 0 above): (iii-a) the right side of `AssembledN`'s conclusion
   (`GridAssemblyN.lean:249-255`, copied by script) at `κ = kappaAltQN`, `εK = epsAltQN`, `dDrift j _ = dd j`, `δD j _ = δD`, `c = cQVAltQN … (K n)`, `stepErr = stepErrN …`
   equals `assembledRHSAltQN` (`subst; simp only; rfl`); (iii-b) `qvBdAltQN … m` is the right side of `qvFormQN_le_of_goodSetN` at `m ↦ m+1` (`QProxy.lean:1186-1196`) by `rfl`;
   (iii-c) `azumaSubGQ_gridExitN` at `m ↦ m+1` accepts `Q = cQVAltQN` from `qvFormQN ≤ qvBdAltQN` (`Real.le_coe_toNNReal`).
8. Not done (outside the Lean deliverable): the list of eventual forms of `ha1`-`he4` for S3-17b (preflight (iii), not part of (a)); the ticket's Open issues 1-3 are untouched
   (the per-matrix linear level `dFlowQN_levelLin`, the cut S3-17a/b, `hY` of S3-18a stay with the dispatcher).

## (c) Verified Mathlib names (`#check @name`, scratchpad `MathlibSig.lean`, `ElemChk.lean`, exit 0; conclusion shown); verified absent: none searched

```
abs_of_pos :: |a| = a
div_le_iff₀ :: b / c ≤ a ↔ b ≤ a * c
inv_eq_one_div :: x⁻¹ = 1 / x
inv_pow :: a⁻¹ ^ n = (a ^ n)⁻¹
le_div_iff₀ :: a ≤ b / c ↔ a * c ≤ b
le_mul_of_one_le_left :: b ≤ a * b
mul_div_cancel₀ :: b * (a / b) = a
mul_pow :: (a * b) ^ n = a ^ n * b ^ n
mul_self_nonneg :: 0 ≤ a * a
Nat.cast_ne_zero :: ↑n ≠ 0 ↔ n ≠ 0
Nat.one_le_pow :: 1 ≤ m ^ n
one_le_inv₀ :: 1 ≤ a⁻¹ ↔ a ≤ 1
pow_le_pow_left₀ :: a ^ n ≤ b ^ n
pow_le_pow_right₀ :: a ^ m ≤ a ^ n
Real.coe_toNNReal :: ↑r.toNNReal = r
Real.le_sqrt' :: x ≤ √y ↔ x ^ 2 ≤ y
Real.log_nonneg :: 0 ≤ Real.log x
Real.log_pow :: Real.log (x ^ n) = ↑n * Real.log x
Real.log_two_gt_d9 :: 0.6931471803 < Real.log 2
Real.log_two_lt_d9 :: Real.log 2 < 0.6931471808
Real.one_le_rpow :: 1 ≤ x ^ z
Real.rpow_add :: x ^ (y + z) = x ^ y * x ^ z
Real.rpow_mul :: x ^ (y * z) = (x ^ y) ^ z
Real.rpow_natCast :: x ^ ↑n = x ^ n
Real.rpow_neg :: x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one :: x ^ (-1) = x⁻¹
Real.rpow_nonneg :: 0 ≤ x ^ y
Real.rpow_one :: x ^ 1 = x
Real.sqrt_eq_rpow :: √x = x ^ (1 / 2)
Real.sqrt_le_iff :: √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
Real.sqrt_le_sqrt :: √x ≤ √y
Real.sqrt_mul :: √(x * y) = √x * √y
Real.sqrt_sq :: √(x ^ 2) = x
Real.le_coe_toNNReal :: r ≤ ↑r.toNNReal
```

Elementary names used and `#check`ed in the same way (exit 0): `add_le_add add_nonneg div_nonneg mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_nonneg pow_nonneg pow_pos sq_nonneg inv_nonneg Nat.cast_nonneg Nat.mul_pos Nat.zero_le Finset.mem_range Finset.sum_congr`.

## (d) Open issues and paper-delta candidates
- `T2279a`: at `d ≥ 3` the alternating budget has one kernel `W^{C₄ε} r^k` (exponent `k`, `kappaAltQN`) and one drift term (no `ℚ/𝔼` split, DECISIONS §83), and is
  proved with the inequality `r B_u ≤ B_t` (`nqGood2_ratio_mul_Bctl_le`, paper `3_5:1158`) in place of the `d = 2` identity `R_{s,t}^k M_s^{-k} = M_t^{-k}`.
- `T2279b`: hypotheses of `budgetAltQN` beyond those of `budgetNonAltLinN`: `hdd` with `0 ≤ Pa`, `0 ≤ Φd`, `0 ≤ b` (the generic drift level), separate `0 ≤ δ0`, `0 ≤ δD`,
  `he0`, and `he1` with the `b`-part and `W^{C₄} δD`; `D'`, `hk : 2 ≤ k`, `Φ₁ Φ₂ Φ₃` do not occur (`k = m + 2`, `Φd` replaces `Φ₁+Φ₂+Φ₃`). The contents of `ha2` (`Pa` in place of
  `k W^{Cε} (N^{ε₁})²`), `ha3` (extra factor `W^{C_nε}`), `he1`, `he2` (`altBudget_kapFar`, `altBudget_qvFar`, exponent `k`, `C₄ = qProxy4C`) differ by the pins; no other difference found.
- `T2279c` (statement shape): the instance shows `Φd` as `1 + 12 + 1 + 1` (`Φ₁+Φ₂+Φ₃+X` of target 8), not `15`.
- Open for the dispatcher: the ticket's Open issues 1-3 (not decided here).
