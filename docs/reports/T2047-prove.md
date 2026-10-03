Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 14:27:08 UTC 2026

Source: RBM2D `Induction/Continuity.lean` at `c9a24cf` (1644 lines; `git show`); targets: `GopboundPin` (:65) and the cut part (declarations before `gopbound` :1269 / `Step1NetLift` :1261 / `step1NetLift` :1331). Notation: `N = sz.size n = (W L)^d`, `Q = η_t⁻¹`, `c₁ = √(2κ)/2`, `x = |u-u'|`.

### (i) Exponent table

| Item (RBM2D line) | Value (d ≥ 1, in terms of N) | Constraint | Slack |
|---|---|---|---|
| `GopboundPin` C' (:65, :1272) | `C' = 2C+14` | `3N^6 · N^{-C'/2} ≤ N^{-C}`, i.e. `3N^{-(C+1)} ≤ N^{-C}` | factor `N/3` (needs `N ≥ 3`); any `C' ≥ 2C+12+2log_N 3` also works |
| entry modulus `cont_entry_diff` (:776) | `‖G_u-G_u'‖_max ≤ Q²(Xb+1)√x`, `Xb = 2N²`, `Q = N²` | `u,u' ≤ t = 1-1/N`, `x ≤ 1`, `Q ≥ η_t⁻¹` | `Q²(Xb+1) ≤ 3N^6` (`N ≥ 1`) |
| `Q = η_t⁻¹ ≤ N²` (`cont_eta_inv_le` :1044) | `η_t = (1-t) Im m`, `Im m ≥ c₁` | `(1-t)⁻¹ ≤ N`, `1/c₁ ≤ N` | `N/ (1/c₁)`; `κ=1/10`: `1/c₁ = 4.47` |
| bulk `cont_bulk` (:727) | `Im m ≥ √(2κ)/2`, `|E| < 2` | `|E| ≤ 2-κ` (so `κ ≤ 2`), `4-E² ≥ 4κ-κ² ≥ 2κ` | slack `κ(2-κ) ≥ 0`; d-free |
| `‖X‖ ≤ Xb` (`cont_norm_Xmat_le` :512) | `Xb = card(Idx)·2·N = 2N²` | all coordinates `≤ N`; `card Idx = (WL)^d = N` | d enters only through `card Idx = N` (2D: `(WL)²`) |
| good event Ξ (`contGood` :230) | `|ω_c| ≤ N` for all `c ∈ CoordF`, `card CoordF = 2N²` | `P(Ξᶜ) ≤ 2N²·2e^{-N²/2} ≤ N^{-D}` for every `D`, eventually | `log10 P ≈ -9.5e11` at `N=2^21` (script) |
| variance `cont_seqGvar_le_one` (:233) | `seqGvar ≤ svarF = W^{-d}·SBR ≤ 1` | `sbKernelR ≥ 0`, `Σ sbKernelR = 1` (`L ≥ 3`), `W ≥ 1`; any real `lam` | no hypothesis on `lam`; replaces 2D five-point profile |
| `Eblk` (`cont_norm_Eblk_le_one` :596) | `‖Eblk‖ ≤ W^{-d} ≤ 1` | `W ≥ 1` | `W^{-d} = 3.05e-5` at `sz0` (2D: `W^{-2}`) |
| `card Vtx` (`cont_LP_close` :1188, `card_BlockIndex`) | `(L W)^d = N` | closing trace `≤ card·‖·‖` | exact |
| `cont_core` net (:147) | `netSize(A+1,N) ≥ N^{A+1}`, spacing `≤ N^{-A-1} ≤ N^{-A}`; `#net ≤ N^{A+2}` | `N ≥ 4`; `hcard: #V ≤ N^{Cv}`; `N^{τ/2} ≥ 3` (so `N^τ-2N^{τ/2}-1 ≥ 0`); `2N^{-(D+1)} ≤ N^{-D}` (`N ≥ 2`) | total index `N^{A+2+Cv}`; union cost absorbed by `D → D+A+2+Cv` |
| loop family: A, Cv, ε (:1387) | `A_k = 6k+16`, `Cv = k+1`, `ε = N^{-k}` | `#V = 2^k (L^d)^k ≤ 2^k N^k ≤ N^{k+1}` (`L^d ≤ (WL)^d`, `2^k ≤ N`) | 2D `L²` becomes `L^d`; slack `N/2^k` |
| loop closeness gA, gB, gC (:1153) | gA `N·N^{-A} ≤ N⁻¹`; gB `N·N^{-A/2} ≤ N⁻¹`; gC `N·k·N^{2k}·3N^6·N^{-A/2} ≤ N^{-k}` | `6k ≤ N` | gC lhs/rhs `= 3k/N`; exponent count `1+2k+6-(3k+8) = -k-1`; d-free |
| loop control ζ (3D probe `STStep1Loop`) | `ζ_u = ((1-s)/(1-u))^{k-1}·Bctl(s)^{k-1}` (2D: `(ℓ_u/ℓ_s)^{2(k-1)} M_u^{-(k-1)}`) | `ζ_{u'} ≤ 2ζ_u`: `(1-u)/(1-u') ≤ 1+N x`, `(1+N x)^{k-1} ≤ 1+2(k-1)Nx ≤ 2` | needs `(k-1)·N^{-1} ≤ 1/2` (weaker than 2D `3(k-1)N⁻¹ ≤ 1/2`); gB (the `ℓ` term `(1-t)⁻¹√x ≤ N⁻¹`) is no longer needed |
| lower bound `ε ≤ ζ` (`cont_LP_low` :1130) | `Bctl(s) ≥ N⁻¹` for `0 ≤ s < 1`; `(1-s)/(1-u) ≥ 1`; so `ζ ≥ N^{-(k-1)} ≥ N^{-k}` | `0 ≤ s ≤ u < 1` | factor `N`; 2D used `M_u ≤ N`; 3D: `W^{-d}(L^d(1-u))⁻¹ = (N(1-u))⁻¹ ≥ N⁻¹`, no `Im m`, no `|E|<2` |
| `Bctl` ratio (replaces `cont_scaleM_ratio` :933) | `Bctl(u') ≤ (1+x/(1-t))·Bctl(u)`, `Bparam(K=0) = (g²+1-u)⁻¹ + (L^d(1-u))⁻¹` | `u,u' ≤ t < 1`; each term's ratio `≤ 1+x/(1-t)` (`g² ≥ 0`); `(1-t)⁻¹ ≤ N` | gives `1+N x`; new derivation, not a rename (2D `Im m·min(W²,N(1-u))`) |
| weak law: A, Cv, ε (:1445) | `A = 40`, `Cv = 2` (`#Idx² = N²`), `ε = N^{-1/4}`, `ζ = Bctl(u)^{1/4}` | g2 `N·N^{-40} ≤ 1/10`; g3 `3N^6 N^{-20} ≤ N^{-1/4}` (`N^{13.75} ≥ 3`); `(11/10)^{1/4} ≤ 2` | `log2` lhs of g3 `= -292.4` vs `-5.25`; any `A > 12.5` works |
| `hRange` → `(1-t)⁻¹ ≤ N` | `RangeCond δ t`: `N^{-1+δ} ≤ 1-t` | `δ ≥ 0`, `N ≥ 1`: `(1-t)⁻¹ ≤ N^{1-δ} ≤ N` | factor `N^δ` |
| `‖z_u - z_{u'}‖` (`cont_norm_spectralZ_sub` :582) | `= x` | `zt E u = E + (1-u) mE E`, `‖mE E‖ = 1` for `|E| ≤ 2` | exact |

Dimension tokens in RBM2D lines 1–1464 (regex counts over `c9a24cf`, comments included; each is replaced by a `d`-version or removed): `W²`: 8 (all in `scaleM` lemmas :618–658, removed with `scaleM`); `L²`: 1 (+3 in Main, S1-34); `(WL)²`: 11 in §3–4 (`scaleM`), 8 in §5, 15 in §6 (all `= N`, become `sz.size n`/`(W*L)^d`); `Z2`: 5 (§2), 1, 6 (§4 Flow), 3 (§6) → `Zd d (W*L)`, `Zd d L`; `cont_card_Z2` (m²) → `m^d` (`card_Idx`). `scaleM` (62 occurrences, lines 1–222 once, §3–§6) and `ellT` (51 occurrences, §3, §5, §6) → `Bctl`/`Bparam` (the probe's `ellT L g t` is not needed by the 3D controls). Cut facts: by my count of non-blank non-comment lines (1365 for the file; the portmap lists 1462; the ticket's cut is 679) the section ends `Assembly` (:763), `Flow` (:925), `Close` (:1245) are at 598, 737, 1022. `gopbound` uses `cont_eta_inv_le` (:1044, §6), `cont_card_Z2`, `cont_norm_Xmat_le`, `cont_entry_diff` (Flow), `cont_bulk`, `cont_good_compl`, `cont_eventually_tail`; `step1NetLift` uses `cont_core`, `cont_highProbAt_good`, `cont_gap`, the §5/§6 lemmas. No propagator (PT) pin occurs in the cut part; `cont_core` takes `PerTimeDomAt` as its abstract hypothesis.

### (ii) Concrete instance (`sz0`, `n = 0`: `d=3, L=4, W=32, lam=1/64, N=2^21`; `κ=1/10`, `E ≡ 1/2`)
Hypotheses of `GopboundPin`: `0 < κ`; `|E n| = 1/2 ≤ 2-κ = 1.9`; `SizeTendsto sz0` (limit: `N_n = ((2(n+1))^5·4(n+1))^3 ≥ n → ∞`, last output line; merged as `sz0_tendsto`). Command and output:
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2047/check.py
N=2097152=2^21; card Idx=2097152; card Vtx=(LW)^d=2097152; card Coord=2N^2=8796093022208; L^d=64<=N: True
kappa=0.1 E=0.5: |E|<=2-kappa: True; Im m=0.9682 >= c1=0.2236: True; 1/c1=4.472 <= N
t=1-1/N: eta_t^-1=2.166e+06 <= N^2=4.398e+12: True; Eblk bound W^-d=3.052e-05<=1
GopboundPin (C'=2C+14, Q=N^2, Xb=2N^2): modulus bound Q^2(Xb+1)*sqrt(delta) vs N^-C
 C=1 C'=16 delta=N^-16=2^-336 bound/N^-C=9.537e-07 (3/N=1.431e-06) ok=True
 C=2 C'=18 delta=N^-18=2^-378 bound/N^-C=9.537e-07 (3/N=1.431e-06) ok=True
 C=3 C'=20 delta=N^-20=2^-420 bound/N^-C=9.537e-07 (3/N=1.431e-06) ok=True
tail: P(bad)<=2N^2*2*exp(-N^2/2): log10 = -9.55e+11  vs N^-D: D=10 -> -63.2, D=1000 -> -6322
net (cont_core): netSize(A+1,N)=ceil(N^(A+1))+1 ; spacing 1/netSize <= N^-A ; #index <= N^(A+2+Cv)
 loop k=1: A=22 netSize=2^483+1, (netSize+2)*cardV <= N^26: True, cardV=128<=N^2: True, spacing ok: True
 loop k=2: A=28 netSize=2^609+1, (netSize+2)*cardV <= N^33: True, cardV=16384<=N^3: True, spacing ok: True
 loop k=3: A=34 netSize=2^735+1, (netSize+2)*cardV <= N^40: True, cardV=2097152<=N^4: True, spacing ok: True
 weak law: A=40 netSize=2^861+1, (netSize+2)*cardV <= N^44: True, cardV=4398046511104<=N^2: True, spacing ok: True
loop closeness conditions gA,gB,gC,g2 at A=6k+16:
 k=1 A=22: gA=True gB=True gC=True (lhs/rhs=1.431e-06=3k/N) 6k<=N=True zeta>=N^-(k-1)>=eps=N^-k: True
 k=2 A=28: gA=True gB=True gC=True (lhs/rhs=2.861e-06=3k/N) 6k<=N=True zeta>=N^-(k-1)>=eps=N^-k: True
 k=3 A=34: gA=True gB=True gC=True (lhs/rhs=4.292e-06=3k/N) 6k<=N=True zeta>=N^-(k-1)>=eps=N^-k: True
weak law A=40: g2 N*N^-40<=1/10: True  g3 log2(3N^6N^-20)= -292.42 <= log2(N^-1/4)=-5.25:  True
Bctl = W^-d*Bparam(d,L,lam,t,0) = W^-d[(lam^2+1-t)^-1+(L^d(1-t))^-1]  (exact Fractions)
 u=0.500000 u'=0.500000000: Bctl>=1/N: True; Bctl(u')/Bctl(u)=1.000000000, Bctl(u)/Bctl(u')=1.000000000 <= 1+N|u-u'|=1.000000000: True; (1-t)^-1<=N: True
 u=0.999999 u'=0.999999523: Bctl>=1/N: True; Bctl(u')/Bctl(u)=1.801011702, Bctl(u)/Bctl(u')=0.555243477 <= 1+N|u-u'|=2.000000000: True; (1-t)^-1<=N: True
 u=0.000000 u'=0.000000000: Bctl>=1/N: True; Bctl(u')/Bctl(u)=1.000000000, Bctl(u)/Bctl(u')=1.000000000 <= 1+N|u-u'|=1.000000000: True; (1-t)^-1<=N: True
loop-control ratio ((1-u)/(1-u'))^(k-1), k=3, u=1/2,u'=1/2+N^-28: 1.0  <= 2: True
SizeTendsto (N_n=((2(n+1))^5*4(n+1))^3 >= n): [(0, 2097152), (1, 549755813888), (10, 11659991713824860234842112)] True
```

### Verdicts
- `GopboundPin` (statement and the exponent chain `C' = 2C+14`): **PASS**. Hypotheses hold together at `sz0` (nonempty, `N = 2^21`, `C ∈ {1,2,3}`); slack `N/3`; no external hypothesis beyond `SizeTendsto`.
- Cut part (`cont_core`, good event, deterministic resolvent and flow estimates, loop and weak-law closeness): **PASS** with one mathematical change to record for the prover: the 2D controls `scaleM`, `ℓ` do not exist in the 3D vocabulary (`STStep1Loop`, `STStep1Weak`); the lemmas `cont_scaleM_*`, `cont_LP_zeta_ratio`, `cont_ellT_diff`, `cont_one_div_sqrt_diff`, `cont_WL_low`, `cont_LP_low` are re-derived for `((1-s)/(1-u))^{k-1} Bctl(s)^{k-1}` and `Bctl(u)^{1/4}` with the table's constants (checked above at `sz0`), not renamed. No paper-delta candidate is proposed at preflight.

## (b) Script output (written Sat Oct  3 14:51:53 UTC 2026, `date -u`)

Branch `t/T2047`, commit `f486e99` (T2047: S1-33 Induction/ContinuityNet (first part of Continuity)), one file. Scratch files: `scratchpad/T2047/`, not committed.

### b.1 Build, hygiene, scope of the diff
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2047 && lake build RBM3D.Induction.ContinuityNet; echo exit=$?
✔ [3306/3306] Built RBM3D.Induction.ContinuityNet (5.9s)
Build completed successfully (3306 jobs).
exit=0
$ lake build; echo exit=$?      # whole library; the root import of the new module is added by the hub at merge
Build completed successfully (3770 jobs).
exit=0
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/Induction/ContinuityNet.lean; grep -c warning <module build log>
0 0
$ git diff main...t/T2047 --stat
 RBM3D/Induction/ContinuityNet.lean | 1010 ++++++++++++++++++++++++++++++++++++
 1 file changed, 1010 insertions(+)
```

### b.2 `#print axioms` of the 34 public declarations (2 defs `GopboundPin`, `contGood`; 32 theorems)
```
$ lake env lean axioms.lean   # import RBM3D.Induction.ContinuityNet; one #print axioms per public name (pubnames.txt)
lines reading `depends on axioms: [propext, Classical.choice, Quot.sound]`: 34 of 34
'GopboundPin' axioms: [propext, Classical.choice, Quot.sound]
'ContinuityNet.cont_core' axioms: [propext, Classical.choice, Quot.sound]
'ContinuityNet.cont_good_compl' axioms: [propext, Classical.choice, Quot.sound]
'ContinuityNet.cont_highProbAt_good' axioms: [propext, Classical.choice, Quot.sound]
'ContinuityNet.cont_green_flow_diff' axioms: [propext, Classical.choice, Quot.sound]
'ContinuityNet.cont_inv_size_le_Bctl' axioms: [propext, Classical.choice, Quot.sound]
'ContinuityNet.cont_Bctl_ratio' axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Registry pre-check (DECISIONS §20, ST1-COMMON item 8)
```
$ cat precheck.lean   # import RBM3D / import RBM3D.Induction.ContinuityNet / #assert_rbm_axioms
$ lake env lean precheck.lean; echo exit=$?
axiom audit: 1799 theorems, 812 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 51 (borrowed 2, owed 35, structural 14).
exit=0
base library (`lake build` at 6ef5d49, above): axiom audit: 1767 theorems, 810 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
base library: premises found by scanning: 51 (borrowed 2, owed 35, structural 14).
```
Same 51 premises found, none unregistered: `GopboundPin` is assumed by no theorem of this file, so no registry line is needed; `RBM3D/Test/Axioms.lean` is unchanged.

### b.4 Target statements, extracted by script (`python3 extract.py <names>` over the committed file; proofs elided as `…`)
```
L55: def GopboundPin {d : ℕ} (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → sz.SizeTendsto →
  ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    sz.seqP {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
        u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ i j : Idx d (sz.L n) (sz.W n),
          ((sz.size n : ℕ) : ℝ) ^ (-C) <
            ‖(sz.seqHflow n u ω - zt (E n) u • 1)⁻¹ i j -
              (sz.seqHflow n u' ω - zt (E n) u' • 1)⁻¹ i j‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
L142: theorem cont_core {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop)
    {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1)
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    {ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ} {A Cv : ℝ} (hA : 0 ≤ A) (hCv : 0 ≤ Cv)
    (hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ Cv)
    (hpt : PerTimeDomAt P size ξ ζ) {Ξ : ℕ → Set Ω} (hΞ : HighProbAt P size Ξ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hlow : ∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × V n) (ω : Ω), ε n ≤ ζ n p ω)
    (hclose : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ (size n : ℝ) ^ (-A) → ∀ v : V n,
        ξ n (u, v) ω ≤ ξ n (u', v) ω + ε n ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    StochDomAt P size ξ ζ := …
L369: theorem cont_highProbAt_good {d : ℕ} (sz : Sizes d) (hsize : Tendsto sz.size atTop atTop) :
    HighProbAt sz.seqP sz.size (contGood sz) := …
L313: theorem cont_good_compl {d : ℕ} (sz : Sizes d) (n : ℕ) :
    sz.seqP (contGood sz n)ᶜ ≤
      ENNReal.ofReal (2 * ((sz.size n : ℕ) : ℝ) ^ 2 *
        (2 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ 2 / 2))) := …
L582: theorem cont_green_flow_diff {H H' X : Matrix n n ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X) {Xb Δ : ℝ} (hX : ‖X‖ ≤ Xb)
    (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) {z z' : ℂ} {η Q : ℝ} (hη : 0 < η)
    (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ) :
    ‖green H z - green H' z'‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := …
L701: theorem cont_inv_size_le_Bctl {d : ℕ} (sz : Sizes d) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n s := …
L725: theorem cont_Bctl_ratio {d : ℕ} (sz : Sizes d) (n : ℕ) {t u u' : ℝ} (ht : t < 1) (hut : u ≤ t)
    (hu't : u' ≤ t) :
    sz.Bctl n u ≤ (1 + (1 - t)⁻¹ * |u - u'|) * sz.Bctl n u' := …
L676: theorem cont_inv_add_one_sub_ratio {γ t u u' : ℝ} (hγ : 0 ≤ γ) (ht : t < 1) (hut : u ≤ t)
    (hu't : u' ≤ t) :
    (γ + (1 - u))⁻¹ ≤ (1 + (1 - t)⁻¹ * |u - u'|) * (γ + (1 - u'))⁻¹ := …
```

### b.5 Compiled nonempty instances (section 5 of the file: `sz0`, `d = 3`, `n = 0`, `N = 2097152`, `κ = 1/10`, `E ≡ 1/2`, sample `ω₁ ≡ 1`)
```
$ sed -n 838,839p RBM3D/Induction/ContinuityNet.lean
example (h : GopboundPin sz0 (1 / 10) (fun _ => (1 / 2 : ℝ))) :=
  h (by norm_num) (fun _ => by norm_num) sz0_tendsto
$ sed -n 846,852p RBM3D/Induction/ContinuityNet.lean     # cont_core: window [0,1/16], V = Idx×Idx, A = 4, Cv = 2, ε = 2N⁻¹
example (hpt : PerTimeDomAt sz0.seqP sz0.size
      (U := fun n => TimeIcc (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => 1 / 16) n ×
        (Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)))
      (fun n p ω => ‖sz0.seqHflow n (p.1 : ℝ) ω p.2.1 p.2.2‖) (fun _ _ _ => (1 : ℝ))) :
    StochDomAt sz0.seqP sz0.size
      (U := fun n => TimeIcc (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => 1 / 16) n ×
        (Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)))
$ python3 (scan of the file)     # every public theorem is applied in some `example`
examples: 33 | public theorems: 32 | not applied in any example: none
```
Hypotheses that stay in an instance: `GopboundPin sz0 (1/10) (fun _ => 1/2)` (the pin S1-34 proves as `gopbound`), and `PerTimeDomAt` for the `cont_core` instance (another gate's pin). All deterministic hypotheses are discharged: `0 < κ`, `|E n| ≤ 19/10`, `SizeTendsto sz0` (`sz0_tendsto`), the window, `#V ≤ N²`, closeness on `contGood`, `ε ≤ ζ`.

### b.6 Statement diff against RBM2D `c9a24cf` after renaming (`python3 stmtdiff.py`; renames R1–R4 of ST1-COMMON item 2 as regexes)
```
RBM2D lines 1-764: 42 declarations; identical after renaming: 34; differ: 1; not in new file (removed/replaced): 7
IDENTICAL: cont_stochDomAt_of_subset contTime contTime_mem cont_exists_close cont_core contGood cont_seqGvar_le_one cont_coord_tail cont_card_coord cont_good_compl
  cont_eventually_tail cont_highProbAt_good cont_opNorm_sq_le_frob cont_norm_le_card_mul cont_norm_one_le cont_green_diff cont_abs_sqrt_sub_sqrt_le cont_norm_Xentry_le
  cont_norm_Xmat_le cont_norm_blockMat_Xmat_le cont_blockMat_sub cont_blockMat_smul cont_green_flow_diff cont_im_m_le_one cont_eta_le_abs_im cont_norm_spectralZ_sub
  cont_norm_Eblk_le_one cont_spectralM_im_nonneg cont_inv_le_const_mul_inv cont_sqrt_rpow cont_sqrt_abs_le cont_bulk cont_gap cont_pow_mul_rpow
REMOVED/REPLACED: cont_card_Z2(:289) cont_abs_min_sub_min_le(:609) cont_scaleM_diff(:618) cont_im_le_scaleM(:631) cont_scaleM_le(:640) cont_one_div_sqrt_diff(:662) cont_ellT_diff(:687)
--- DIFF GopboundPin (Continuity:65)
   insert: 'def GopboundPin (κ : ℝ) (' -> 'def GopboundPin {d : ℕ} (sz : Sizes d) (κ : ℝ) ('
NEW (no RBM2D counterpart): cont_Gres_true_eq_green cont_Gres_false_eq_green cont_norm_green_le cont_inv_add_one_sub_ratio cont_Bctl_eq cont_inv_size_le_Bctl cont_Bctl_ratio
PRIVATE in new file (non-instance): cont_stochDomAt_of_subset contTime contTime_mem cont_exists_close cont_seqGvar_le_one cont_coord_tail cont_card_coord
  cont_opNorm_sq_le_frob
```
Residual difference: the pin's `variable (d : Sizes)` (RBM2D :58) is the explicit argument `{d : ℕ} (sz : Sizes d)`; 8 declarations are `private` in both files, the 26 others are `private` in RBM2D and public here (namespace `RBM.Ind.ContinuityNet`; `GopboundPin` in `RBM.Ind`).

### b.7 The cut (RBM2D `Continuity.lean` at `c9a24cf`; portmap `CONT1 = 764/1644`, T2015-portmap.md:1460)
```
this file: lines 1-764 = header, `GopboundPin` :65, Core :81-222, Good :226-366, Resolvent :370-456, Modulus :458-531, GreenFlow :533-565,
  Spectral :567-588, EblkNorm :589-602, Scalars :606-658, Scalars2 :660-694, Ratio :696-705, Analytic :707-722, Bulk :724-740, Assembly :742-763
S1-34 (next ticket): lines 765-1464: 20 declarations: cont_entry_diff:776 cont_llErr_diff:798 contWord:809 contWord_cons:814 cont_word_norm:818 cont_word_diff:836 cont_loopAbs_diff:877 cont_scaleM_ratio:933 cont_one_add_pow_le:956 cont_LP_zeta_ratio:973 cont_one_le_size:1038 cont_eta_inv_le:1044 cont_WL_low:1057 cont_WL_close:1065 cont_LP_low:1130 cont_LP_eventually:1153 cont_LP_close:1188 Step1NetLift:1261 gopbound:1269 step1NetLift:1331
  + the Checks section :1466-1637 (test data of RBM2D, replaced by `sz0` instances)
code lines (comments stripped): RBM2D 1-764: 598; new file sections 0-4: 594; section 5 (instances): 125; file total 1010 lines
$ python3 refcheck.py   # which part-1 declarations the S1-34 side references
part-1 declarations used by RBM2D lines 765-1464: 26; public in the new file: 21; not carried over: cont_card_Z2(:289) cont_scaleM_diff(:618) cont_im_le_scaleM(:631) cont_scaleM_le(:640) cont_ellT_diff(:687)
PT/propagator pins (`PropTH`, `Prop5`, `Prop6`, `ThetaDecay`, `ThetaZero`, `KLPT`) in RBM2D 1-764 / in the new file: 0 / 0
```

### b.8 Dimension tokens of the cut part (`python3 tokens2.py`, comments stripped; ST1-COMMON item 2)
```
token (code only)                  RBM2D 1-764 new file §0-4
W^2  `W ^ 2`                                8          0
L^2  `L ^ 2`                               12          0
N^2  `(W * L) ^ 2`                         11          0
Z2/zdist2                                   4          0
scaleM/ellT                                15          0
W^-2 type (`⁻²`, `_inv_W_sq`)               1          1
`d : Sizes` / `d.size|L|W`                 95          0
`(W : ℝ)⁻¹` (`W^{-2}` bound)                2          0
3D replacement `^ d`                        -         20
W^2  `W ^ 2` RBM2D lines: [634, 635, 645, 646, 652, 654, 655]
L^2  `L ^ 2` RBM2D lines: [621, 626, 627, 632, 635, 641, 645, 646, 650, 652, 654]
N^2  `(W * L) ^ 2` RBM2D lines: [621, 626, 627, 632, 635, 641, 645, 646, 652, 654]
Z2/zdist2 RBM2D lines: [289, 290, 300, 596]
scaleM/ellT RBM2D lines: [618, 620, 622, 631, 632, 633, 640, 641, 642, 687, 688, 689]
```
Disposition: `W^2`, `L^2`, `(WL)^2`, `scaleM`, `ellT` (RBM2D :609-694, 6 declarations `cont_abs_min_sub_min_le`, `cont_scaleM_diff`, `cont_im_le_scaleM`, `cont_scaleM_le`, `cont_one_div_sqrt_diff`, `cont_ellT_diff`) are removed: the `d = 3` controls are `Bctl` (section 4, new lemmas, `W^d`, `L^d` explicit); `Z2` (:289, :290, :300, :596) became `card_Idx`/`Zd d L`; `d : Sizes` became `sz : Sizes d`; the one `⁻²` is the merged lemma name `norm_Eblk_le_inv_W_sq` (statement `(W^d)⁻¹`). All other lemmas of the cut are dimension-free.

### b.9 Name clash of the 34 new public names against `main` (a68a954)
```
$ for each name: grep -rnw --include='*.lean' <short name> /Users/junyin/Lean_proof/RBM3D/RBM3D | grep -v ContinuityNet.lean
names checked=34, names with a hit outside the new file=1
GopboundPin: RBM3D/Induction/Defs.lean:360 (a docstring mention, no declaration)
```

### b.10 Port source drift
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Continuity.lean
 RBM2D/Induction/Continuity.lean | 270 ++++++----------------------------------
 1 file changed, 36 insertions(+), 234 deletions(-)
$ git -C ../RBM2D --no-optional-locks log --oneline c9a24cf..HEAD -- RBM2D/Induction/Continuity.lean
bcc2c11 T2275: merge comment clean-up (Induction)
99d6fe0 T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)
```
The 23 hunks (`git diff -U0 ... | grep ^@@`) are doc-comment edits, the dead lemma `cont_one_le_size` (:1037-1042), the deleted Checks section and the trailing `#print axioms` lines (:1640-1644); the port is from `c9a24cf` as the ticket pins. RBM1D was not read (the RBM1D citations in docstrings are RBM2D's own, `86573b9`).

### b.11 Does the cut serve S1-34? Uncommitted scratch re-port of S1-34 pieces against `import RBM3D.Induction.ContinuityNet` only
```
$ lake env lean scratchpad/T2047/gop_scratch.lean; echo exit=$?   # cont_entry_diff (:776), cont_eta_inv_le (:1044), proof of gopbound (:1269), for every d
'RBM.Ind.gopbound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean scratchpad/T2047/scal_scratch.lean; echo exit=$?  # weak-law lower bound `WL_low`, weak-law control ratio `WL_zeta`, loop-control ratio `loop_ratio` ((1-s)/(1-u))
'RBM.Ind.WL_low' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.WL_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.loop_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### b.12 Narrative
* Cut. This file is RBM2D `Continuity.lean` lines 1-764 (through `end Assembly`), the portmap's CONT1 (764/1644 × 1462 = 679, the ticket's "679 kept lines"). S1-34 takes `Flow`, `Ratio2`, `Close`, `Main` (:765-1464) and imports this file only (b.7, b.11).
* API for S1-34. Of the 26 part-1 declarations that RBM2D lines 765-1464 use (b.7), 21 are public in `RBM.Ind.ContinuityNet` under RBM2D's name; the other 5 have 3D replacements (`cont_card_Z2` is the merged `card_Zd`/`Sizes.card_Idx`; `cont_scaleM_diff`, `cont_im_le_scaleM`, `cont_scaleM_le`, `cont_ellT_diff` are the section 4 lemmas for `Bctl`). The 21 are (`GopboundPin`, `cont_spectralM_im_nonneg`, `cont_core`, `contGood`, `cont_good_compl`, `cont_eventually_tail`, `cont_highProbAt_good`, `cont_norm_Xmat_le`, `cont_norm_blockMat_Xmat_le`, `cont_blockMat_sub`, `cont_blockMat_smul`, `cont_green_flow_diff`, `cont_eta_le_abs_im`, `cont_norm_spectralZ_sub`, `cont_norm_Eblk_le_one`, `cont_abs_sqrt_sub_sqrt_le`, `cont_sqrt_abs_le`, `cont_bulk`, `cont_gap`, `cont_pow_mul_rpow`, `cont_inv_le_const_mul_inv`); the helpers only used inside the file are `private` (b.6).
* Vocabulary (R1-R4). `d : Sizes` is `sz : Sizes d`; `Z2 L` is `Zd d L`; `Coord`, `Xmat`, `Hflow`, `blockMat`, `BlockIndex` are `CoordF`, `Xmat d`, `Hflow d`, `blockMat d`, `Vtx`; `spectralM`, `spectralZ` are `mE`, `zt`; `green` is the merged `RBM.green` (EntryCore). RBM2D's `norm_green_le` and `isUnit_sub_smul_one_of_im_ne_zero` are not merged: `cont_norm_green_le` is the merged `norm_Gsig_le_inv_eta` read through the new bridge `cont_Gres_true_eq_green` (with `cont_Gres_false_eq_green` for the `σ = -` loops of S1-34), and `isUnit_sub_smul_of_isHermitian` is used.
* Dimension-dependent proofs. `cont_seqGvar_le_one`: the variance of every coordinate is `≤ 1` from the row sum `sum_sbKernelR` (stochastic kernel, `L ≥ 3`) and `W ≥ 1`, for any coupling `sz.lam n`; RBM2D unfolded the five-point `svar` (`split_ifs`). `cont_card_coord`: `2N²` from `Sizes.card_Idx` (`N = (WL)^d`), `cont_card_Z2` dropped. `cont_norm_Eblk_le_one`: `‖E_a‖ ≤ W^{-d} ≤ 1`. `cont_norm_blockMat_Xmat_le`: `#Vtx`. The statements of the net lift, the Gaussian tail of the good event, the resolvent and flow moduli, the bulk constant and the gap lemma do not mention `d`.
* Scales. The 2D controls `scaleM`, `ℓ` have no 3D analogue (`STStep1Loop`, `STStep1Weak` use `((1-s)/(1-u))^{k-1} Bctl(s)^{k-1}` and `Bctl(u)^{1/4}`). Section 4 re-derives, for `Bctl`, what the net lift needs: `N⁻¹ ≤ Bctl n s` (`0 ≤ s < 1`; replaces `M_u ≤ N`) and `Bctl n u ≤ (1 + (1-t)⁻¹|u-u'|) Bctl n u'` for `u, u' ≤ t < 1`, with the underlying `(γ + 1 - u)⁻¹` ratio (also the `(1-s)/(1-u)` ratio of the loop control). With `(1-t)⁻¹ ≤ N` this is `1 + N|u-u'|`, the constant of preflight rows 23-25. These are new text, not renamings; the exponents `C' = 2C + 14`, `A = 6k + 16`, `A = 40` of the preflight table belong to S1-34 and were not re-checked here beyond the scratch `gopbound` (`C' = 2C + 14`, b.11).
* Good event. `contGood` (every coordinate `≤ N`) has `P(contGoodᶜ) ≤ 4N² e^{-N²/2}` (`cont_good_compl`), eventually `≤ N^{-D}` for every `D` (`cont_highProbAt_good`); on it `‖X‖ ≤ 2N²`.
* Registry. No new premise: `GopboundPin` is the statement S1-34 proves, no theorem here assumes it (b.3).
* Preflight (a) stands; no correction (a′) is needed. Its row 17 (variance bound without a hypothesis on `lam`) and rows 23-25 (`Bctl` ratio, lower bound `N⁻¹`) are exactly what the proofs use.

## (c) Verified Mathlib names used (new relative to the RBM2D text; `#check` in `scratchpad/T2047/names.lean`, 23 of 23 resolve)
ProbabilityTheory.HasSubgaussianMGF.id_map_iff; ProbabilityTheory.HasSubgaussianMGF.measure_ge_le; ProbabilityTheory.integrable_exp_mul_gaussianReal; ProbabilityTheory.mgf_id_gaussianReal; MeasureTheory.ofReal_measureReal; MeasureTheory.measure_iUnion_fintype_le; Matrix.cstar_norm_def; Matrix.ofLp_toEuclideanCLM; Matrix.l2_opNorm_diagonal; Finset.sum_mul_sq_le_sq_mul_sq; pow_le_pow_iff_left₀; tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero; Matrix.nonsing_inv_eq_ringInverse; Matrix.nonsing_inv_mul; Matrix.mul_nonsing_inv; inv_anti₀; div_le_div_iff₀; Set.mem_ofPred_eq; norm_le_insert'; Nat.one_le_cast; Real.rpow_neg_one; Real.sqrt_eq_rpow.
Verified deprecated: `Set.mem_setOf_eq` (warning at this Mathlib; used `Set.mem_ofPred_eq`). Merged RBM3D names used: `Sizes.card_Idx`, `Sizes.seqP_map_eval`, `sum_sbKernelR`, `sbKernelR_nonneg`, `norm_Gsig_le_inv_eta`, `norm_Eblk_le_inv_W_sq`, `isUnit_sub_smul_of_isHermitian`, `Hflow_sub`, `Hflow_sub_apply`, `stochDomAt_of_perTimeDomAt`, `card_net_le`, `netPt`, `netSize`, `Sizes.tendsto_size`, `sz0_tendsto`.

## (d) Open issues and paper-delta candidates
* `T2047a` (pin readings, all inherited from RBM2D `Continuity:60-64` and unchanged): `GopboundPin` has the premise `0 < κ →` (RBM2D `T2070a`: the paper's bulk hypothesis `κ > 0`), the range `u ≥ N^{-1}` of `Gopboundu` is read as `1 - u ≥ N^{-1}`, and "exponentially small" as `≤ N^{-D}` for every `D` (RBM2D `T2006i`). The `d ≥ 3` paper has no statement of `Gopboundu` (signed `T2015e`); the pin is stated for every `d` (no `3 ≤ d`), since its proof (b.11) uses none.
* Open for S1-34: the loop and weak-law closeness (`Close`) and the ratio lemmas `cont_one_add_pow_le`, `cont_LP_zeta_ratio` are to be rewritten for `Bctl` on top of section 4; `Gres`-based `contWord` replaces `Gsig`; `cont_card_Z2` is `card_Zd`/`Sizes.card_Idx`, `cont_one_le_size` is `Sizes.one_le_size`.
* The `cont_core` instance leaves the per-time domination as a hypothesis; the discharge of `PerTimeDomAt` for the families of Step 1 is `STStep1LoopPT`/`STStep1WeakPT` (S1-34).
* No statement of the cut part differs from the paper beyond `T2047a`; no hypothesis was added, no pinned signature changed, no file outside the sole writable files touched (`Test/Axioms.lean` untouched).
