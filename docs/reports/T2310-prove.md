Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct  7 09:28:54 UTC 2026

Restart under CONTROL H106 (DECISIONS §119-§120): pin `STXiRoundPT'` (ticket §1), target `stOeqQtRoundPT'_holds : ∀ d, STOeqQtRoundPT' d`.
Notation: `k = n_`, `m = n_-2` (`altGridEndQN`: loop length `m+1+1`, `QEndGrid.lean:1326`), `ε₀ = τ/2`, `e₂ = min(ε₀,1)/2`, `ε₁ = e₂/40` (`QEndGrid.lean:1307-1313`; `ε₁,τ',D',C_K` are `∃`, only `>0` known to the caller), `N = sz.size n`.

### (i) Exponent table
| # | quantity | value / choice | constraint (source) | slack / verdict |
|---|---|---|---|---|
| 1 | `n_` vs `m` | `m = n_-2` | `altGridEndQN` premise `1 ≤ m` ⇒ `n_ ≥ 3` = pin's `3 ≤ n_` | closes; `n_=2` would give `m=0` (script) |
| 2 | sign split | all `σ`: `σ(last)=!σ 0` (alt endpoint) ∪ `σ(last)=σ 0` (non-alt) | `STXiLK = 1 + max_{σ,a}‖(𝓛-𝒦)^{(n_)}‖/B^{n_}` (`Step34Pins.lean:68`) is over **all** `σ`; `altGridEndQN` covers only `σ(last)=!σ 0`; `finRotate n_ (last)=0` so `σ(last)=σ 0` lies in `STNQConclPT''`'s set `∃k, σ k = σ(finRotate k)` (`NQEndFlow.lean:107`); paper `3_5:1679`: "`lem:STOeq_NQ` already gives a good enough bound for non-alternating" | **closes only with the non-alt half; ticket §2 does not list it.** Source: `nqFlow_core` (`NQEndFlow.lean:642`, **private**; must be copied; `stOeqNQPT''_holds` :921 is diagonal-index, cannot be used as a black box for pairs `(v,u)`) |
| 3 | pair index | section `(v_n,u_n)`, `s≤v≤u≤t`; window `[s,ṽ]`, `ṽ=v` where `s<v`, else `t`; constants `XL m n u'_n`, `u'_n=u` resp. `t` | restriction of `Prec` over `STPair` to pairs `(w,u'_n)`, `w ≤ ṽ ≤ u'_n`; `B_v^{1/6} ≤ B_u^{1/6}` by `STBctl_mono` (`ScaleFacts.lean:74`, `u<1`) | closes (script: `Bctl` monotone); collapsed `v_n=s_n`: `STLK s` at length `n_` and `1 ≤ RHS` |
| 4 | level constants | `ε₀=τ/2=0.05`, `e₂=0.025`, `ε₁=6.25e-4` (at `τ=0.1`) | final level `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃+X)B_v^{n_}` ≤ `N^{τ}·RHS B_v^{n_}` | closes with factor 2 (row 5) |
| 5 | `X` double count | `X := XLK(n_-1)` (`altYGridN` at `l=n_-1`, `QEndA.lean:194`), `Φ₁ = Σ_{2..n_-1}XLK` (`NQLin.lean:79`) | `Λ^{1/2}+Φ₁+Φ₂+Φ₃ ≤ B_v^{1/6}XLK n_ + STbootRHS 2 …` (`nqFlow_level_le`, `NQEndFlow.lean:402`); `X ≤ STbootRHS 2` (`n_-1 ≥ 2`), so sum ≤ 2·RHS | `N^{τ/2} ≥ 2` iff `log₁₀N ≥ 6.02` (eventual); `STbootRHS 2 ≤ STbootRHS 1` (extra term `XLK 1 ≥ 1`) |
| 6 | current length | `Φcur = XLK n_` in `Φ₂` (`NQLin.lean:84`) | `NQLinConcl` (`NQLin.lean:102`) needs `Ξ̂^{LK}_m ≺ XLK m`, `m ≤ k` **including `m=k`** | closes: pin hypothesis `m ≤ n_` (ticket §1) |
| 7 | crude `Φc` of `GoodSetN` | `Φc = Σ_{m=1}^{n_+1}(XL m+XLK m)` (`nqFlowPhiC`, `NQEndFlow.lean:172`) | `GridGoodNConcl` (`GridGoodN.lean:505`) needs `Ξ̂^L_m ≺ Φc` (`m≤k+1`), `Ξ̂^{LK}_m ≺ Φc` (`m≤k`), `STlenL` (`Step34Pins.lean:391`): `m ≤ n_+1` is in `STlenL` | closes from pin hypotheses (no crude `N^{C}` bound needed) |
| 8 | initial-loop split (`startLevelQN`, `QLevelsA.lean:421`) | `ν=N^{ε₁/8}`, `ε'=ε₁/8` (`STLK s` at lengths `m+1`, `m+2`), `τN=ε₁/2` | `hMΛ`: `c₀ν² ≤ N^{τN}`, `c₀=(2m+5)·3·4^{dm}·(2/√κ)·C`, mollifier `C=(1+40d(m+1))6^{d(m+1)}` (`QopAlgebra.lean:511`, `QEndGrid.lean:767`); output `‖𝒬_s(𝓛-𝒦)‖ ≤ Y + N^{τN}B^{m+2}X` is a **sum** | **ticket §2a (`τN=ε₁/8`, `ν=N^{ε₁/8}`) fails `hMΛ` for every `N`** (`c₀N^{ε₁/4} > N^{ε₁/8}`; script). Corrected: (a) `c₀ ≤ N^{ε₁/4}` iff `log₁₀N ≥ 67074`; (b) `N^{ε₁/8}+N^{ε₁/2} ≤ N^{ε₁}` if `log₁₀N ≥ 963.3`. Both eventual in `n`, as in `altGridEndQN`'s own `hMΛ` (`QEndGrid.lean:874`, `ν=N^{ε₁}`, `τN=5ε₁`: `log₁₀N ≥ 5590`) |
| 9 | far decay `hF`,`hFv` | `ω_f=W^{τ''}`, `τ''=ε₁/(8dm)`; decay `D_F=(2m+6)/𝔠` | `hωd: ω_f^{dm} ≤ ν`; `hFv: Fv ≤ ν N^{-(2m+4)}`; source `stDecayLoopU_of_step2` (`DecayLoopB.lean:1637`) with `hD := (STStep2Concl).2.2` (`STGdecayW`, `Step34Pins.lean:221`) at `u=s_n` (`STIngR` supplies `STStep2Concl`); `Prec` slack `N^{1}`, `W ≥ N^𝔠` | closes: `N·W^{-D_F} ≤ N^{-(2m+5)} ≤ ν N^{-(2m+4)}`. `STKbound` has no distance decay (not a source) |
| 10 | union over `(σ,a)` (non-alt half) | `nqFlow_core` is per `(σ_n,a_n)` | `2^{n_}L^{dn_} ≤ 2^{n_}N^{n_}` (`L^d ≤ N`); run core at `D+n_+1` | `8N^{3}N^{-(D+4)}=8N^{-D-1} ≤ N^{-D}` iff `N ≥ 8`. Alt half: `G` of `altGridEndQN` covers all `σ,a` at once |
| 11 | constants / hypotheses from `STIngR` | `𝔠d := min(𝔠G,𝔠L)` from `gridGoodN_holds`, `nqLinGood_holds` (as `stOeqNZPT''_holds`, `QtNonzeroFlow.lean:837-862`); `κ'=κ/2` via `v3_premises_of_stFlow` | `STConStInd 𝔠d` restricted to `[s,v]` (`st_conStInd_sub`) | closes (pattern verbatim from T2292) |

### (ii) One concrete nondegenerate instance
Data: `d=3`, `L=4x`, `W=(2x)^5`, `λ=(2x)^{-6}`, `x=n+1`, `N=(WL)^3`; `z_n=0.1i` (`E=lemE z`); `κ=1`, `𝔠=1/6`, `𝔡=1/10`, `ε=1/10`; `s≡0`, `t≡1/2`; `n_=3`, `p=1` (`m=1`); `XL≡XLK≡1`; `τ=1/10`.
Deterministic hypotheses (STFlow, case I, `RangeCond`, `W^{-1} ≤ (1-t)/(1-s)`, `|E|≤2-κ/2`) are checked for every `n<3000`. The probabilistic hypotheses (`STKbound`, `STKward`, `STLK s`, `STStep2Concl`, the `Prec` hypotheses `Ξ̂ ≺ 1`) stay hypotheses of `STIngR`/the pin and are not evaluated. External hypothesis `STConStInd 𝔠d` (eventual): limit computation below (`𝔠d=1/100`, the largest allowed). The `log₁₀N` thresholds of rows 5, 8 enter only the conclusion's `∀ᶠ n`, not the hypotheses.
Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2310 && python3 -I pre2.py`
```
instance d=3 L=4x W=(2x)^5 lam=(2x)^-6 x=n+1 N=(WL)^d z=0.1i kappa=1.0 c=0.1667 dd=0.1 eps=0.1 s=0 t=1/2 lemT=0.9049 lemE=-0.0
STFlow locDomain/Bandwidth/WO, |E|<=2-kappa/2, RangeCond(eps/2), STCaseI, W^-1<=(1-t)/(1-s), every n<3000: True  0<=s<t<=lemT: True
STConStInd (external, limit): Bctl(t)^cd<=(1-t)/(1-s)=1/2 with cd=1/100 holds for all 3000>n>=53; B(n=53)=6.305e-31, B(n=2999)=4.254e-57 -> 0
n_=3: m=n_-2=1, altGridEndQN needs 1<=m: True; alt loop length m+2=3=n_; altYSetN length m+1=2=n_-1; X=XLK(n_-1)>=1 and n_-1 in [1,n_-1] of STbootRHS sum: True
n_=4: m=n_-2=2, altGridEndQN needs 1<=m: True; alt loop length m+2=4=n_; altYSetN length m+1=3=n_-1; X=XLK(n_-1)>=1 and n_-1 in [1,n_-1] of STbootRHS sum: True
n_=5: m=n_-2=3, altGridEndQN needs 1<=m: True; alt loop length m+2=5=n_; altYSetN length m+1=4=n_-1; X=XLK(n_-1)>=1 and n_-1 in [1,n_-1] of STbootRHS sum: True
n_=2: m=0, 1<=m: False
eps0=tau/2=0.05; e2=0.025; eps1=e2/40=0.000625; mollifier C=(1+40d(m+1))6^(d(m+1))=11244096; c0=(2m+5)3*4^(dm)*Gamma*C=3.0224e+10
ticket 2a split: nu=N^(e1/8), tauN=e1/8: c0*N^(e1/4)<=N^(e1/8) at N=1..1e300 ever true: False
corrected: nu=N^(e1/8), tauN=e1/2, eps'=e1/8: (a) c0*N^(e1/4)<=N^(e1/2) iff log10N>=67074; (b) N^(e1/8)+N^(e1/2)<=N^e1 if log10N>=963.3
internal pattern of altGridEndQN (QEndGrid.lean:874): nu=N^e1, tauN=e2/8=0.003125=5*e1: c0*N^(2e1)<=N^(5e1) iff log10N>=5590
hF: omega_f=W^tau'' with tau''=e1/(8dm)=2.604e-05; hwd: omega_f^(dm)=W^(e1/8)<=nu=N^(e1/8) at n=4: True
hF decay: D_F=(2m+6)/c=48, Prec slack N^1: N*W^-D_F=8.00e-222 <= nu*N^-(2m+4)>=3.81e-114 at n=4: True; via W>=N^c: N^(1-(2m+6))=N^-7 <= N^-(2m+4): True
final level: N^eps0*(Lam^(1/2)+F1+F2+F3+X)<= N^eps0*2*RHS2 (X=XLK(n_-1) counted twice) <= N^tau*RHS iff N^(tau/2)>=2: log10N>=6.02 ; n=4 log10N=18.90: True
union over (sigma,a) in NQ half: 2^n_*L^(d n_)<=2^n_*N^n_ ; run nqFlow_core at D+n_+1: 2^3*N^3*N^-(D+4)=8*N^-(D+1)<=N^-D iff N>=8: n=4 N=8.00e+18 True
Bctl monotone in u at n=4 on [0.0, 0.1, 0.25, 0.4, 0.5] : True
```

### Verdict
- **Target `stOeqQtRoundPT'_holds` (pin `STXiRoundPT'`): PASS** — every hypothesis set holds (instance), every exponent closes with the choices of rows 5, 8, 9, 10 (eventual in `n`).
- Required of stage 1b (ticket gaps, not obstructions): (1) row 2: the non-alternating half is not in ticket §2; it needs a private copy of `nqFlow_core` (`NQEndFlow.lean:642`, plus its helpers) with pair-constant controls (row 3) and the union bound (row 10); (2) row 8: use `τN=ε₁/2` (or `5ε₁` with `ν=N^{ε₁}`), not ticket §2a's `ε₁/8`; the combined bound is a sum, not a product; (3) row 5: constant 2 absorbed by `N^{τ/2}`; (4) row 9: `hF` from `stDecayLoopU_of_step2` with `D_F=(2m+6)/𝔠`.
- Paper-delta candidate `T2310a`: `STXiRoundPT'` is the paper's `(eq:alternatecase1)` (`3_5:1687`) with the sup over `v` of the parameters replaced by constants `XLK m n u` and `(W^{-d}B_{u,0})^{1/6}`; the pin states `Prec` over pairs `(v,u)` with parameters at `u` and takes `B_v^{1/6} ≤ B_u^{1/6}`.

## (a′) Preflight corrections — Wed Oct  7 10:08:19 UTC 2026
Section (a) was not edited; the verdict PASS is unchanged. Three statements of (a) differ from what stage 1b did:
- Row 2 / "Required of stage 1b (1)" ("`stOeqNQPT''_holds` … cannot be used as a black box for pairs `(v,u)`"): it can, through a window change. `STNQConclPT''` on the window `[s, uu]` with the controls frozen at `uu_n` (pair hypotheses restricted along `(w, x) ↦ (w, uu_n)`) is `PrecPT` over `TimeIcc s uu × signs × labels`; at the time `w_n ≤ uu_n` it is a `PerTimeDomAt` over `(σ, a)`. No copy of `nqFlow_core` is needed (`altQFlow_nq_half`, `QEndB1.lean`).
- Row 10: the union over `(σ, a)` of the non-alternating half is `Path.stochDomAt_of_perTimeDomAt` with `#(σ,a) ≤ 2^{n_} (L^d)^{n_} ≤ N^{2n_}` (`N ≥ 2`), not "run core at `D+n_+1`". The alternating half needs no union (`G` of `altGridEndQN` covers every `σ, a`), as (a) says.
- Row 8: `ε₁` from `altGridEndQN` is only `> 0` for the caller, so `ν = N^{ε₁/8} ≤ N` can fail; the proof uses `e = min ε₁ 1` (`ν = N^{e/8}`, `τ_N = e/2`, `ωf = W^{e/(8dm)}`). Row 9 used `D_F = (2m+5)/𝔠` (`N·W^{-D_F} ≤ N^{-(2m+4)} ≤ ν N^{-(2m+4)}`; (a)'s `(2m+6)/𝔠` also closes).

## (b) Script output (stage 1b, written Wed Oct  7 10:13:05 UTC 2026 per `date -u`; commit on `t/T2310` as printed below)
```
$ git log -1 --format="%h %cI" ; git diff --name-only main...t/T2310 ; wc -l RBM3D/Induction/QEndB1.lean
a6e597e 2026-10-07T03:11:55-07:00
RBM3D/Induction/QEndB1.lean
    1326 RBM3D/Induction/QEndB1.lean
$ lake build RBM3D.Induction.QEndB1 2>&1 | grep -E "QEndB1.lean|Build completed|error|sorry"
info: RBM3D/Induction/QEndB1.lean:1323:0: 'RBM.Gauss.Sizes.STXiRoundPT'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QEndB1.lean:1324:0: 'RBM.Gauss.Sizes.STOeqQtRoundPT'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QEndB1.lean:1325:0: 'RBM.Ind.stOeqQtRoundPT'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QEndB1.lean:1326:0: 'RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT'' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3870 jobs).
$ grep -c "sorry\|admit\|native_decide\|axiom \|maxHeartbeats" RBM3D/Induction/QEndB1.lean
0
$ target statements (extracted by sed from the file)
def STXiRoundPT' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 3 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2)
          (sz.Bctl n (s n)) n_ p)

def STOeqQtRoundPT' (d : ℕ) : Prop :=
  STIngR d STCaseI (fun sz E s t => STXiRoundPT' sz E s t)

1187:theorem stOeqQtRoundPT'_holds : ∀ d : ℕ, STOeqQtRoundPT' d := by
$ python3 -I stmt_diff.py   (pins vs docs/tickets/checks/T2310-check.lean)
STXiRoundPT' statement lines: check 13 file 13 ; unified-diff lines: 0
STOeqQtRoundPT' statement lines: check 2 file 2 ; unified-diff lines: 0
$ lake env lean pin_check.lean ; echo $?   (check file + `import RBM3D.Induction.QEndB1` + identity examples below)
exit: 0
example : @RBM.Gauss.Sizes.T2310Check.STXiRoundPT' = @RBM.Gauss.Sizes.STXiRoundPT' := rfl
example : @RBM.Gauss.Sizes.T2310Check.STOeqQtRoundPT' = @RBM.Gauss.Sizes.STOeqQtRoundPT' := rfl
example : RBM.Gauss.Sizes.T2310Check.stOeqQtRoundPT'_holds_pin := RBM.Ind.stOeqQtRoundPT'_holds
example : ∀ d : ℕ, RBM.Gauss.Sizes.STOeqQtRoundPT' d := @RBM.Ind.stOeqQtRoundPT'_holds
$ instance (extracted): sed -n "/^theorem inst_OeqQtRoundPT/,/sz0_hs0 sz0_hst/p"
theorem inst_OeqQtRoundPT' :
    InstIngConcl (fun sz E s t => STXiRoundPT' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STXiRoundPT' sz E s t) (stOeqQtRoundPT'_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos
$ example (1), applied at n_ = 3, p = 1, XL = XLK = 1 (hypotheses left: STLK s, STStep2Concl, pair hypotheses)
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    PrecPT sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 3 ω)
      (fun n q _ => sz0.Bctl n q.1.2 ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqQtRoundPT'
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 3 1 le_rfl le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp
$ grep -n "^example\|^theorem inst_\|^namespace QEndB1Inst" RBM3D/Induction/QEndB1.lean | sed -n "/QEndB1Inst/,\$p"
1243:namespace QEndB1Inst
1251:theorem inst_OeqQtRoundPT' :
1261:example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
1278:example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
1295:example (n : ℕ) : ∃ q : STPair sInst tInst n, q.1.1 < q.1.2 :=
1298:example (n : ℕ) : ∃ q : STPair sInst tInst n, q.1.1 = q.1.2 :=
1303:example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2) 3 1 ≤
1307:example : (fun _ : ℕ => (1 : ℝ)) (3 - 1) ≤ STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2) 3 1 :=
1310:example : 2 * (4 : ℝ) ^ (-(1 + (1 : ℝ))) ≤ (4 : ℝ) ^ (-(1 : ℝ)) :=
1315:example : ∀ d : ℕ, STOeqQtRoundPT' d := @stOeqQtRoundPT'_holds
$ name-clash grep in the main worktree (HEAD dab3fad): grep -rn -F <name> RBM3D RBM3D.lean | grep -v QEndB1.lean | wc -l
STXiRoundPT'               0
STOeqQtRoundPT'            0
stOeqQtRoundPT'_holds      0
QEndB1Inst                 0
inst_OeqQtRoundPT'         0
altQFlow_                  0
QEndB1                     0
$ lines per section (awk over "/-! ## " headers)
   39  /-! ## Pins -/
  305  /-! ## §0 helpers (private copies of `NQEndFlow.lean`) -/
   58  /-! ## §1 small facts: `STbootRHS`, the sizes, the failure-probability arithmetic -
  220  /-! ## §2 the projected initial loops `altQFlow_initQ` -/
  199  /-! ## §3 the alternating endpoint at one non-collapsed section -/
   74  /-! ## §4 the non-alternating half (the merged per-time pin `stOeqNQPT''_holds`) an
  209  /-! ## §5 the endpoint at an arbitrary pair `(w_n, u_n)` -/
   59  /-! ## §6 the per-time round `stOeqQtRoundPT'_holds` -/
   93  /-! ## §7 Compiled nonempty instances at `d = 3`
$ sources of the copies: git log -1 --format=%h -- <file> (RBM3D files); RBM1D/RBM2D references in the file
RBM3D/Induction/NQEndFlow.lean       0f60da2
RBM3D/Induction/QLevelsB.lean        54b8610
RBM3D/Green/EntryDom.lean            a68a954
mentions of RBM1D/RBM2D in RBM3D/Induction/QEndB1.lean (grep -c): 0; no RBM1D/RBM2D code ported
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ registry pre-check: lake env lean reg_before.lean / reg_after.lean (import RBM3D [+ import RBM3D.Induction.QEndB1] + #assert_rbm_axioms)
before: exit 0; axiom audit: 8959 theorems, 2911 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after : exit 0; axiom audit: 8961 theorems, 2913 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff of lines 2..268 (owed/borrowed premise listing): none
```

Narrative (facts from the files and the tool log above):
1. Deliverable: `RBM3D/Induction/QEndB1.lean` (1326 lines, one file, commit `a6e597e` on `t/T2310`). `lake build RBM3D.Induction.QEndB1`: `Build completed successfully (3870 jobs)`; the four public declarations depend on `propext, Classical.choice, Quot.sound` only; the count of `sorry|admit|native_decide|axiom |maxHeartbeats` is 0; `git diff --name-only main...t/T2310` lists only the sole file.
2. Statements: the pins `STXiRoundPT'`, `STOeqQtRoundPT'` are the ticket's text (script diff 0 lines); `pin_check.lean` (check file + `import RBM3D.Induction.QEndB1`) has exit 0: `rfl` identities of both pins, and the check file's `stOeqQtRoundPT'_holds_pin` is proved by `stOeqQtRoundPT'_holds`. No hypothesis added, no pinned signature changed.
3. Top level (`stOeqQtRoundPT'_holds`, §6): `𝔠_d = min (𝔠_d^G, 𝔠_d^L, 𝔠_d^{NQ}, 1/(2d))` from `gridGoodN_holds`, `nqLinGood_holds`, `stOeqNQPT''_holds`; premises from the flow (`v3_premises_of_stFlow`, `st_window`), `STDecayLoopU` from `stDecayLoopU_of_step2`; the three merged pins are re-instantiated on sub-windows; then `perTimeDomAt_iff_forall_section` and `altQFlow_section` (§5) at a pair `q n = ((w_n, u_n), _)`.
4. `altQFlow_section`: where `s_n < w_n`, the window is `[s, v]`, `v_n = w_n`, the controls are frozen at `uu_n = u_n` (pair hypotheses restricted along `w ↦ (w, uu_n)`); where `w_n = s_n` the sequences `v_n = uu_n = t_n` are dummies and only `altQFlow_collapsed` (`STLK s`) is used. `Ξ̂^{(𝓛-𝒦)}_{w,n_} = 1 + max_{σ,a} …`; every sign is alternating (`σ_last = ¬σ_0`) or has `σ_last = σ_0 = σ_{finRotate last}` (`finRotate_last`); alternating part `altQFlow_core` (§3), non-alternating part `altQFlow_nq_half` (§4); `1 + N^{τ/2} ζ_A ≤ 2N^{τ/2} ζ_A ≤ N^τ ζ_A ≤ N^τ ζ` (`ζ_A ≤ ζ`: `STBctl_mono`, `STbootRHS 2 ≤ STbootRHS 1`).
5. `altQFlow_core`: `altGridEndQN` at `ε₀ = τ/2`, `D₁ = D+2`; the walk events are `GoodSetN` (`gridGoodN_holds`, crude level `Φc`, level `Λ_s`), `GoodLinN` (`nqLinGood_holds`, `Φ₂` with `Y (m+2)`, the current length), `altYSetN` (`altYGridN` at the length `m+1`, level `Y (m+1)`) and the projected initial bound (`altQFlow_initQ`), joined by `HighProbAt.inter` at `D+2` and transferred by `map_pathH_eq` at the indices `0` and `K_n`. The additive level `X = Y (m+1)` is `≤ STbootRHS 2` (`m+1 ≥ 2`), so the bracket is `≤ 2ζ` and `N^{τ/2}·2ζ ≤ N^τ ζ`.
6. `altQFlow_initQ` (§2): `startLevelQN` per matrix at `u = s_n`, `X ≡ 1`, `ν = N^{e/8}`, `τ_N = e/2`, `e = min ε 1`; `hY`, `hYtop` from `STLK s` at the lengths `m+1`, `m+2`; `hF` from `STDecayLoopU` at `u = s_n` (window `W^{e/(8dm)}`, `Fv = N W^{-D_F}`, `D_F = (2m+5)/𝔠`, `W ≥ N^𝔠`); the mollifier bound is the copied `hexp` block of `QLevelsB.lean`.
7. Where ticket §2 did not hold or was incomplete (all internal): (i) §2 has no non-alternating half although `STXiLK` is the maximum over all signs and `altGridEndQN` covers only `σ_last = ¬σ_0` (see (a′), row 2); (ii) §2a's `τ_N = ε₁/8`, `ν = N^{ε₁/8}` fails `hMΛ` (a), row 8; the proof uses `τ_N = e/2`; (iii) `hF` comes from `stDecayLoopU_of_step2`, not `STKbound` (as (a), row 9).
8. Ports: none from RBM1D/RBM2D (the file mentions neither; script output above). §0 (305 lines) copies private helpers of `NQEndFlow.lean` (`0f60da2`) under the prefix `altQFlow_`; one `hexp` block from `QLevelsB.lean` (`54b8610`); `card_Zd` from `Green/EntryDom.lean` (`a68a954`).
9. Size: 1326 lines against the ticket's 850 / 1000 / 1250 (lo / central / hi); the stop rule (1400) was not reached. `RBM3D.lean` and `Test/Axioms.lean` are unchanged; the registry pre-check above: +2 theorems, +2 definitions, 0 axioms, remaining listing identical.
10. Limits: the conclusion is `∀ᶠ n`, so the instances apply the theorem and keep `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` as hypotheses of the example (other gates' pins, as in `NQEndFlowInst`); they evaluate no `n`. `n_ = 2` is outside the pin (`3 ≤ n_`; `altGridEndQN` needs `m = n_ - 2 ≥ 1`).

## (c) Verified Mathlib / core names used (all `#check`ed by `<scratch>/names_check.lean` after `import RBM3D.Induction.QEndB1`: 52 names, exit 0)
`Finset.sum_le_sum_of_subset_of_nonneg` (`s ⊆ t → (∀ i ∈ t, i ∉ s → 0 ≤ f i) → ∑ s f ≤ ∑ t f`)
`Finset.Icc_subset_Icc` (`a₂ ≤ a₁ → b₁ ≤ b₂ → Icc a₁ b₁ ⊆ Icc a₂ b₂`)
`Finset.single_le_sum` (`(∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ s f`)
`Finset.sup'_le` (`(H : s.Nonempty) (f) → (∀ b ∈ s, f b ≤ a) → s.sup' H f ≤ a`)
`Nat.le_mul_of_pos_right` (`(n) → 0 < m → n ≤ n * m`); `Nat.le_mul_of_pos_left` (`(m) → 0 < n → m ≤ n * m`)
`Nat.le_self_pow` (`n ≠ 0 → (a) → a ≤ a ^ n`); `Nat.pow_le_pow_left` (`n ≤ m → (i) → n ^ i ≤ m ^ i`)
`ZMod.card` (`(n) [Fintype (ZMod n)] → Fintype.card (ZMod n) = n`)
`Real.rpow_add` (`0 < x → x ^ (y + z) = x ^ y * x ^ z`); `Real.rpow_mul` (`0 ≤ x → x ^ (y * z) = (x ^ y) ^ z`)
`Real.rpow_natCast` (`x ^ (n : ℝ) = x ^ n`); `Real.rpow_neg` (`0 ≤ x → x ^ (-y) = (x ^ y)⁻¹`); `Real.rpow_neg_one` (`x ^ (-1) = x⁻¹`)
`Real.rpow_le_rpow` (`0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z`)
`Real.rpow_le_rpow_of_exponent_le` (`1 ≤ x → y ≤ z → x ^ y ≤ x ^ z`)
`Real.one_le_rpow` (`1 ≤ x → 0 ≤ z → 1 ≤ x ^ z`); `Real.rpow_nonneg` (`0 ≤ x → 0 ≤ x ^ y`)
`Real.exp_le_one_iff` (`exp x ≤ 1 ↔ x ≤ 0`)
`inv_anti₀` (`0 < b → b ≤ a → a⁻¹ ≤ b⁻¹`); `one_div_le_one_div_of_le` (`0 < a → a ≤ b → 1 / b ≤ 1 / a`)
`le_mul_of_one_le_left` (`0 ≤ b → 1 ≤ a → b ≤ a * b`)
`div_le_iff₀` (`0 < c → (b / c ≤ a ↔ b ≤ a * c)`); `lt_div_iff₀` (`0 < c → (a < b / c ↔ a * c < b)`)
`div_nonpos_of_nonpos_of_nonneg` (`a ≤ 0 → 0 ≤ b → a / b ≤ 0`)
`Fintype.card_subtype_le` (`card {x // p x} ≤ card α`); `Fintype.card_fun` (`card (α → β) = card β ^ card α`)
`Fintype.card_prod` (`card (α × β) = card α * card β`); `Fintype.card_fin` (`card (Fin n) = n`)
`finRotate_last` (`finRotate (n + 1) (Fin.last n) = 0`)
`Measurable.norm` (`Measurable f → Measurable fun a => ‖f a‖`); `Measurable.sub` (`Measurable f → Measurable g → Measurable (f - g)`)
`Measurable.mul_const` (`Measurable f → ∀ c, Measurable fun x => f x * c`)
`Finset.measurable_sum` (`(s) → (∀ i ∈ s, Measurable (f i)) → Measurable fun a => ∑ i ∈ s, f i a`)
`MeasurableSet.iInter` / `MeasurableSet.iUnion` (`[Countable ι] → (∀ b, MeasurableSet (f b)) → MeasurableSet (⋂ / ⋃ b, f b)`)
`measurableSet_le` / `measurableSet_lt` (`Measurable f → Measurable g → MeasurableSet {a | f a ≤ g a}` / `{a | f a < g a}`)
`Set.preimage_compl` (`f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ`); `Set.mem_ofPred_eq` (`(x ∈ {y | p y}) = p x`)
`tendsto_rpow_atTop` (`0 < y → Tendsto (fun x => x ^ y) atTop atTop`); `Filter.Tendsto.eventually_ge_atTop` (`Tendsto f l atTop → (c) → ∀ᶠ x in l, c ≤ f x`)
`MeasureTheory.measure_union_le` (`μ (s ∪ t) ≤ μ s + μ t`); `MeasureTheory.measure_mono` (`s ⊆ t → μ s ≤ μ t`); `MeasureTheory.measure_ne_top` (`(μ) [IsFiniteMeasure μ] (s) → μ s ≠ ⊤`)
`ENNReal.ofReal_add` (`0 ≤ p → 0 ≤ q → ofReal (p + q) = ofReal p + ofReal q`); `ENNReal.ofReal_le_ofReal` (`p ≤ q → ofReal p ≤ ofReal q`)
`MeasureTheory.ofReal_measureReal` (`μ s ≠ ⊤ → ofReal (μ.real s) = μ s`)
Changed / absent in this toolchain (compile log): `add_le_add_left` is `b ≤ c → ∀ a, b + a ≤ c + a` (the `a + b ≤ a + c` form of older Mathlib is not this name); `push_neg` is deprecated (use `push Not`); `Set.compl_setOf` is deprecated (`Set.compl_ofPred : {a | p a}ᶜ = {a | ¬p a}`); `Set.setOf_true` is deprecated (`Set.ofPred_true`); `if_pos` is deprecated (warning text: use `ite_eq_left`; the proof uses `simp only [h, ↓reduceIte]`).

## (d) Open issues and paper-delta candidates
- `T2310a` (from (a)): `STXiRoundPT'` is the pair-indexed per-time form of `(eq:alternatecase1)` (`3_5:1687`) with the parameters `XL, XLK` constant in `v` (the paper has `sup_{v ∈ [s,u]}` of parameters on the right) and `B_v^{1/6} ≤ B_u^{1/6}` (`STBctl_mono`, used in `altQFlow_section`); `3 ≤ n_` against the paper's `n ≥ 2`.
- `T2310b`: the projected initial loops (`3_5:1676-1690`, the start term of the alternating case) are bounded by `N^{ε} B_s^{n_}` with `ν = N^{e/8}`, `τ_N = e/2`, `e = min ε 1`; the far decay comes from `stDecayLoopU_of_step2` (`DecayLoopB.lean:1637`); eventual in `n` only (`c₀ ≤ N^{e/4}`, `N^{e/2} ≥ 2`).
- `T2310c`: the non-alternating signs (`3_5:1679`: "`lem:STOeq_NQ` already gives a good enough bound") are the merged per-time pin `stOeqNQPT''_holds` used on the window `[s, uu_n]` with the controls frozen at `uu_n` (the merged pin is diagonal: control and quantity at the same time), plus a union over `(σ, a)`, `#(σ,a) ≤ N^{2n_}`.
- `T2310d`: collapsed pairs `w_n = s_n` are bounded by `STLK s` at length `n_` (the `Prec`/`StochDomAt` union over `(σ, a)` is inside `STLK`); the dummy window `[s, t]` of the core is not used at those `n` (cf. D597, T2292d).
- `T2310e`: the additive lower-length level `X = Y (m+1)` of `altGridEndQN` (`T2302a`), the factor `1` of `Ξ̂ = 1 + max …` and the factor `2` are absorbed by `N^{τ/2} ≥ 2` (eventual in `n`).
- Open (1): `n_ = 2` is not covered (`3 ≤ n_`; `altGridEndQN` needs `m = n_ - 2 ≥ 1`); the merged `STXiRound'` and `STXiBoot'` have `2 ≤ n_`, so S3-18b2 needs a separate source for `n_ = 2`.
- Open (2): size 1326 lines against the ticket's hi 1250 (stop rule 1400 not reached); §0 copies are 305 lines.
- Open (3): ticket text: §2 omits the non-alternating half; §2a's `τ_N = ε₁/8` fails `hMΛ`; the ticket names `gridGoodN_holds`, `nqLinGood_holds`, `STQop` without namespaces: they, and `QopAlgebra_mollifier_props`, are in `RBM.Gauss.Sizes` (not `RBM.Ind`), while `stOeqNQPT''_holds` and `altGridEndQN` are in `RBM.Ind` (`#check` output in the tool log).
- Open (4): the examples of §7 keep `STLK s`, `STStep2Concl` and `Ξ̂ ≺ 1` as hypotheses (other gates' pins); no new owed premise is created by this file.
