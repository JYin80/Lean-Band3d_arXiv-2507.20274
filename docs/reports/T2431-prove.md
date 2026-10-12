Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 00:31:04 UTC 2026

Targets (mathematics only): (T1) `BATwistLoopBase d` (`TwistPins.lean:164`): from `G_0 = M` at the carrier, `‖L̃_0 − K̃_0‖ ≺ B^{3/2}` at the zero sequence. (T2) `BAChainTL d` (`:185`): `BAMainIndTL d STAny`, `STHorizonG`, `STBaseG`, T1, `STG0M` at every flow give `BAMLOutTL d`. Both pins are read as stated in `TwistPins.lean:164-188`; no quantifier or premise defect found (see verdicts).

### (i) Exponent table

Instance constants `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)` (order of the binders `∀ κ ε 𝔡 𝔠` in the pins; `BAFlow sz κ ε 𝔠 𝔡 z` has `𝔠 𝔡` swapped), `sz0` (`Defs/Sizes.lean:260`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = (LW)^3`).

| quantity | value | constraint | slack |
|---|---|---|---|
| TL2 exponent `3/2` (`BATwistLoopLaw`, `TwistPins.lean:95`) | `3/2` | base case: `ξ = ‖L̃_0 − K̃_0‖ = 0` for every `n, u, ω` (exact identity, T1 proof shape), `ζ = Bctl^{3/2} ≥ 0` (`mainIndBase_bctl_nonneg`, `MainIndBase.lean:69`) | any exponent works at `t = 0`; no loss (script: max error 5.6e-17 = float rounding) |
| `τ = ε/2` | `1/20` | `stChainSteps` needs `0 < τ` and `N^{-1+τ} ≤ 1 − T0` eventually (`STHorizonG`) | `N_0^{-0.95} = 9.9e-7` vs `1 − T0 ≥ 11/36 = 0.3056` (script) |
| `μ = min(2𝔠𝔡, τ)` | `min(1/30, 1/20) = 1/30` | `> 0` | `1/30` vs `1/20` |
| `𝔠_d` | `1/100` (the pin gives some `0 < 𝔠_d ≤ 1/100`; any smaller value only enlarges `K`) | `0 < 𝔠_d ≤ 1/100` | — |
| chain length `K` | `K ≥ 2/(𝔠_d μ) = 6000` | `2 ≤ K 𝔠_d μ` (`stChainSteps` hypothesis, `MainIndChain.lean:80-82`; used as `hK` at `:156-157`) | `K = 6000` gives `K 𝔠_d μ = 2` (equality; any `K ≥ 6000` works) |
| `2^{𝔠_d} ≤ N^{𝔠_d μ/2}` (`stChainSteps` proof `:88`) | `N ≥ 2^{2/μ} = 2^{60}` | eventually in `n` | `N_n ≥ 2^{60}` first at `n = 4` (script; `N_3 < 2^{60}`); eventual, not at `n = 0` |
| `W^{-d}B_{u,0} ≤ 2N^{-μ}` (`scaleFacts_R1`, `Induction/ScaleFacts.lean:193`, proved) | `u ≤ T0`, `\|1−u\| ≥ 11/36` | eventually | ratio LHS/RHS ≤ 8.2e-5 for `n = 0..300` (script) |
| `(1−t)^{1/K} ≥ N^{-1/K}` chain: `2^{𝔠_d} N^{-μ𝔠_d} ≤ N^{-1/K} ≤ (N^{-1+τ})^{1/K} ≤ (1−t)^{1/K}` | at `n = 10`, `t = 1/2`: `0.98777 ≤ 0.99043 ≤ 0.99090 ≤ 0.99988` | needs `K 𝔠_d μ ≥ 2` and `1 − t ≥ N^{-1+τ}` | all four steps strict (script) |
| chain times `p_k = 1 − (1−t)^{k/K}` | `p_0 = 0`, `p_K = t`, `p_k < p_{k+1} ≤ t` | strict because `t_n > 0` (`stChainTime_facts`, `:62`) | `t = 1/2`, `K = 6000`: min step `5.8e-5 > 0` (script) |
| horizon `T0 = BAt0 = Im m/(Im m + Im z)` (`MFixedPoint.lean:279`) | `Im m + Im z = 6/5` (`t0_sz0` proof, `FlowPins.lean:1227-1240`); `2/3 ≤ T0 < 1`; `1 − T0 = Im z/(6/5) ≥ (11/30)/(6/5) = 11/36` (`zSeq_im_ge`, `:1205`) | `0 < T0 < 1` (`STHorizonG`) | `1/3 ≥ 1 − T0 ≥ 11/36` |
| `Im m_F > 0` at every `n` (T1 needs it for `BAMfine_eq`, `GreenSchur.lean:93`) | `BAflow_real … n` (`FlowPins.lean:322-330`) gives `BAReal`, `.1.1 : 0 < Im m_F`; at `sz0`: `BAmF_sz0_im_pos` (`:1270`) | every `n` (not eventual) | `Im m(z_n) ≥ 4/5` (`mS_im_half`, `FlowPins.lean:1147`) |
| `Θ_0` (`PropThetaQ Q 0 = Ring.inverse (1 − (0:ℂ)•Q)`, `Propagator/Pins.lean:214`) | `Ring.inverse 1 = 1`, entries `δ_{aa'}` | — | exact |

### (ii) One concrete nondegenerate instance

T1 at `d = 3`, `sz0`, `n = 0`: `L = 4` (`4^3 = 64` blocks `a, c₁, c₂`), `W = 32`; four charges `σ ∈ {±}²`, `c₁ ≠ c₂` and `c₁ = c₂`; generic complex `M^{(B)}`. Identity checked: with `M_{xy} = 1[o_x = o_y] M^{(B)}_{[x][y]}` (`BAMfine_eq`), `L̃_0 = twLoopX (twChg M σ₀) (twChg M σ₁) = W^{-d} M^{(B)}(σ₀)_{c₂a} M^{(B)}(σ₁)_{ac₁} = K̃_0` (`Θ_0 = 1`). The script uses 8 offsets instead of `W^d = 32768` (the offset count enters only as the factor `W^d` and cancels: `Σ_{x∈[a],w∈[c₁]} δ_{o_x o_w} = W^d`). T2 at `t ≡ 0` and `t ≡ 1/2`: `K = 6000`, `𝔠_d = 1/100` (rows above); `1/2 ≤ T0` by `half_lt_t0` (`FlowPins.lean:1254`).

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2431/inst2.py
base case G_0=M, d=3, L=4 (64 blocks), 8 offsets: checked 24 tuples (4 charges; c1!=c2 and c1=c2): max |L~_0-K~_0| = 5.594315114139762e-17 ; |K~_{(-,+),(0;1,2)}| = 0.10481202019287322
tau = eps/2 = 1/20 ; mu = min(2 c dd, tau) = 1/30 ; K >= 2/(cd*mu) = 6000 ; K = 6000 gives K*cd*mu = 2
N_0 = 2097152 = 2^21: True
1-T0 >= 11/36 = 0.3055555555555556 ; N^(-1+eps/2) at n=0: 9.873055685437949e-07  (<= 11/36: True )
2^cd <= N^(cd*mu/2) iff N >= 2^60; first n with N_n >= 2^60: 4 ; N_3>=: False
chain p_k: p_0=0, p_K=1/2, strictly increasing for K=6000; min step = 5.776560165438038e-05
Bctl(u) <= 2 N^-mu for n=0..300 (|1-u|=11/36): True ; max ratio = 8.23270849071266e-05
n=10: 2^cd N^(-mu cd) = 0.9877675026855512  <= N^(-1/K) = 0.9904264203632711  <= (N^(-1+tau))^(1/K) = 0.9909029152464031  <= (1-t)^(1/K) = 0.9998844821426083 ; chain: True
```

External hypotheses (stay hypotheses of the Lean instances; limit computations):
- `STHorizonG` at `sz0`: `Admissible (1/6) (1/10)` is `sz0_admissible` (`Defs/Sizes.lean:331`); `0 < T0 < 1` and `1 − T0 ≥ 11/36` above; `N_n^{-19/20} ≤ N_n^{-0.9} ≤ 1/4` is `size_rpow_le` (`FlowPins.lean:1168`, proved, all `n`), and `N_n ≥ 2^{21}` (`size_ge`, `:1153`) gives `N_n^{-19/20} ≤ 2^{-19.95} < 11/36` (script row `n = 0`): the eventual clause holds from `n = 0`.
- `STG0M (baFMz sz z)`: at the carrier `G_0 = Gres(seqHflowBA lam0 n 0 ω, ztOf m E 0, true) = Ring.inverse(λ₀Ψ − (E + (1−0)m)•1)` (`ztOf m E t = E + (1−t) m`, `Loop/GLoopFlow.lean:55`; `seqHflowBA … 0 = λ₀ • PsiI`, example `Gauss/BlockAnderson.lean:214-224`) and `M = Mres(λ₀Ψ, E, m) = Ring.inverse(λ₀Ψ − (E+m)•1)` (`GLoopFlow.lean:81`; `Gres` `:74`): identical matrices, so the premise is exactly satisfiable (BA-V `GLoopAtT0` owner; not proved here).
- `BAMainIndTL d STAny`, `STBaseG`: BA-V / merged-base pins, kept as hypotheses. Their deterministic premises are discharged by the rows above (`STConStInd` by `stChainSteps` with `K = 6000`; `STAny` is `True`, `Step34Pins.lean:272`); T2's TL2 base is T1.

### (iii) Twin table (band chain lemma ↦ BA twin in `RBM3D/BA/TwistChain.lean`, new)

| band/merged source (file:line) | BA twin (namespace `RBM.BA`) | change |
|---|---|---|
| `stPosConclG_of_mainIndG` `MainIndChain.lean:148-172` | `TwistChain_posConcl` (private or stem-prefixed) | hypotheses `BAMainIndTL d STAny` (`TwistPins.lean:169`), `STHorizonG`, `STBaseG`, `BATwistLoopBase d`, `STG0M`; invariant `STConclgL ∧ BATwistLoopLaw`; `H` gets `trivial` for `R = STAny` after the four order hypotheses |
| `stMLOutG_of_mainIndG` `MainIndOut.lean:99-123` | `baChainTL_holds` | `STMLOutG`-shape plus 6th conjunct; `h0` from T1 + `hbase`, `h1` from `TwistChain_posConcl` |
| `STLKgL_mix` `:66`, `STLmaxgL_mix` `:71`, `STDecaygL_mix` `:76`, `STExp2gL_mix` `:81`, `STLocalEntrygL_mix` `:86` (all `MainIndOut.lean`) | `TwistChain_{LK,Lmax,Decay,Exp2,LocalEntry}_mix` | verbatim copies |
| (none) | `TwistChain_TL2_mix` | 6th mix: the proof of `STExp2gL_mix` (`:81-85`) with `BATwistLoopLaw`; valid because `U n = (Fin 2 → Bool) × Zd³` does not depend on `t` and the bad set is rewritten by `simpa [h] using hu` |
| `precL_of_zero` `MainIndBase.lean:71-78` (private) | `TwistChain_precL_of_zero` | verbatim copy |
| public, reused: `stChainTime_zero :55`, `_top :58`, `_facts :62`, `stChainSteps :80`, `STLocalMaxgL_of_STLocalEntrygL :126` (`MainIndChain.lean`), `mainIndBase_bctl_nonneg` (`MainIndBase.lean:69`), `twCirc_holds` (`TwistPins.lean:467`) | — | — |

### (iv) The seventh conjunct (TL2)
- Base: `k = 0`, `stChainTime t K 0 = fun _ => 0` (`stChainTime_zero`); `STConclgL` from `STBaseG`, `BATwistLoopLaw` from `BATwistLoopBase d … hG` with `hG := (STG0M premise) at baFMz sz z` (binder order `κ ε 𝔡 𝔠`).
- Step: `BAMainIndTL` at `(s, t) = (p_k, p_{k+1})`: hypotheses `(LK, Decay, DecayStrong, LocalMax = of LocalEntry, Exp2, TL2)` from the invariant (`ih'.1, ih'.2.2.1, ih'.2.2.2.2.2, …, TL2`); output `(LK, Lmax, Decay, Exp2, LocalEntry, DecayStrong, TL2)` is `STConclgL ∧ BATwistLoopLaw`; regime `trivial`; `STConStInd` by `stChainSteps` with `hK`.
- Mix: `t' = if t n = 0 then T0/2 else t n`; `BATwistLoopLaw` at `t` from `h0` (zero sequence) and `h1` (`t'`) by `TwistChain_TL2_mix`.

### (v) Base case: `STG0M` at `baFMz` and `0 < Im m_F`
`C.G n 0 ω = C.M n` entrywise by `STG0M` (`MainIndBase.lean:54`) ⇒ `twChg (C.G n 0 ω) σ = twChg (C.M n) σ`. `0 < Im m_F` at every `n` from `BAflow_real` (`.1.1`) ⇒ `BAMfine_eq` (`GreenSchur.lean:93`): `M` has offset form with `MB = BAMB …`; `twChg` of the offset form is the offset form with `BAMsigma σ MB`. `twCirc_holds` (public, `TwistPins.lean:467`) at `X₂ = M`: `twLoopX X₁ (M − M) = 0`, hence `twLoopX X₁ M a c₁ c₂ = W^{-d} MB_{ac₁} twTrP X₁ a c₂` (this avoids the private `TwistPins_circ_term`); `twTrP` of the offset form `= MB'_{c₂a}` by `card_Iblk` (`Defs/Sizes.lean:95`); `twMB_ba` (`:80`) gives `twMB = BAMB`; `Θ_0 = 1`; so `twL2' = twK` exactly, closed by `TwistChain_precL_of_zero` with `ζ = Bctl^{3/2} ≥ 0`.

### (vi) Copied private lemmas
| source (file:line) | new name |
|---|---|
| `MainIndOut.lean:66, 71, 76, 81, 86` (five `_mix`) | `TwistChain_{LK,Lmax,Decay,Exp2,LocalEntry}_mix` |
| (new, shape of `:81`) | `TwistChain_TL2_mix` |
| `MainIndBase.lean:71-78` `precL_of_zero` | `TwistChain_precL_of_zero` |
| `TwistPins.lean:293` `TwistPins_split_shift`, `:297` `TwistPins_mem_blk`, `:301` `TwistPins_shift_of_mem` (all private; needed for the offset-form `twTrP`) | `TwistChain_split_shift`, `TwistChain_mem_blk`, `TwistChain_shift_of_mem` |
| `TwistPins.lean:828` `TwistPins_trP_diag` (private; scalar case, `card_Iblk` pattern) | adapted to the offset form: `TwistChain_trP_offset` |

### (vii) Predicted size against the stop line (prediction, not a measurement)
Base theorem with 4 helpers ≈ 130; chain assembly ≈ 70; 6 mix lemmas ≈ 40; `baChainTL_holds` ≈ 45; instances (T1; T2 at `t ≡ 0`, `t ≡ 1/2`) ≈ 60; header ≈ 20; total ≈ 370, under the ticket's 450 expected and the 1,000 stop line.

### Verdicts
- Target 1 `baTwistLoopBase_holds`: PASS. The pin is true as stated (`STG0M` exact at the carrier; `L̃_0 = K̃_0` exact; `ξ ≡ 0`).
- Target 2 `baChainTL_holds`: PASS. The pin is true as stated given its hypotheses: all six premises of `BAMainIndTL` are in the invariant, the regime argument is `trivial`, `K` is a fixed natural number.

## (a′) Preflight corrections — Mon Oct 12 00:38:25 UTC 2026
- (vi) listed `TwistPins_shift_of_mem` (`TwistPins.lean:301`) as needed for the offset-form `twTrP`: it is not (the proof uses only `split_shift`, `mem_blk`, `card_Iblk`); (v) is as proved (`twCirc_holds` at `X₂ = M`, no copy of `TwistPins_circ_term`). No verdict changes.

## (b) Script output

### b.1 Size against the stop line (CONTROL H134: stop size 1,000)
```
$ wc -l RBM3D/BA/TwistChain.lean
     297 RBM3D/BA/TwistChain.lean
$ git log --oneline -1
198fa66 T2431: TwistChain base case baTwistLoopBase_holds, chain baChainTL_holds, instances
```

### b.2 Twin table as finally proved (band/merged chain lemma ↦ BA twin; `RBM3D/BA/TwistChain.lean` lines)
| source (file:line) | BA twin (line) | change |
|---|---|---|
| `stPosConclG_of_mainIndG` `MainIndChain.lean:148-172` | `TwistChain_posConcl` (`:152`, private) | invariant `STConclgL ∧ BATwistLoopLaw`; hypotheses `BAMainIndTL d STAny`, `STHorizonG`, `STBaseG`, `BATwistLoopBase d`, `STG0M` at every flow; `k = 0`: `STBaseG` and `BATwistLoopBase` with `STG0M`; step: `H … trivial ⟨LK, Decay, DecayStrong, LocalMax-of-LocalEntry, Exp2, TL2⟩ (stChainSteps …)`, output split 6 + 1 |
| `stMLOutG_of_mainIndG` `MainIndOut.lean:99-123` | `baChainTL_holds` (`:240`) | `t' = if t n = 0 then BAflowT0/2 else t n`; `h1 = TwistChain_posConcl`, `h0 = STBaseG` and `BATwistLoopBase` with `STG0M`; six mixes (five copies and `TwistChain_TL2_mix`) |
| (new) | `baTwistLoopBase_holds` (`:110`) | `STG0M` ⇒ `G_0 = M`; `BAMfine_eq` (`Im m_F > 0` from `BAflow_real … n`, `.1.1`); `twChg` offset form; `twL2' = W^{-d} MB(σ₁)_{ac₁} MB(σ₀)_{c₂a}`; `twK_ba` and `Θ_0 = 1`; `ξ = 0` |
| public, reused unchanged | — | `stChainTime_zero :55`, `_top :58`, `_facts :62`, `stChainSteps :80`, `STLocalMaxgL_of_STLocalEntrygL :126` (`MainIndChain.lean`), `mainIndBase_bctl_nonneg` (`MainIndBase.lean:69`), `twCirc_holds` (`TwistPins.lean:467`), `twK_ba` (`:279`), `BAMfine_eq` (`GreenSchur.lean:93`), `BAflow_real` (`:59`), `card_Iblk` |

### b.3 Copied and new private lemmas (source file:line ↦ new name, `TwistChain.lean` line)
| source | new name | kind |
|---|---|---|
| `MainIndOut.lean:66, 71, 76, 81, 86` (`STLKgL_mix`, `STLmaxgL_mix`, `STDecaygL_mix`, `STExp2gL_mix`, `STLocalEntrygL_mix`) | `TwistChain_LK_mix :194`, `_Lmax_mix :200`, `_Decay_mix :206`, `_Exp2_mix :212`, `_LocalEntry_mix :218` | verbatim copies |
| shape of `MainIndOut.lean:81-85` | `TwistChain_TL2_mix :226` | new: `BATwistLoopLaw` (index set `(Fin 2 → Bool) × Zd³` independent of `t`) |
| `MainIndBase.lean:71-78` `precL_of_zero` | `TwistChain_precL_of_zero :43` | verbatim, `μ` made explicit |
| `TwistPins.lean:293` `TwistPins_split_shift`, `:297` `TwistPins_mem_blk` | `TwistChain_split_shift :53`, `TwistChain_mem_blk :58` | verbatim copies |
| `TwistPins.lean:828` `TwistPins_trP_diag` (scalar case) | `TwistChain_trP_offset :82` | adapted to the offset form (`twTrP n X a c = MB c a`) |
| `TwistPins.lean:440` `TwistPins_circ_term` (not copied) | `TwistChain_loop_offset :98` | `twCirc_holds` (`:467`, public) at `X₂ = M` instead |
| (new) | `TwistChain_Off :63` (def), `TwistChain_chg_off :69` | `twChg` of an offset-form matrix |

### b.4 Build
```
$ lake build RBM3D.BA.TwistChain 2>&1 | grep -n "TwistChain\|error\|Build"
2695:Build completed successfully (3998 jobs).
(the build of the final file state, before the module was cached, printed: `2695:✔ [3998/3998] Built RBM3D.BA.TwistChain (3.0s)`, no warning of `TwistChain.lean`)
$ (full `lake build` with the temporary line `import RBM3D.BA.TwistChain` after line 474 of RBM3D.lean, since reverted; not committed: the hub adds it at merge, CLAUDE.md §3 (A) 4) tail of log
Build completed successfully (4246 jobs).
lake build  37.93s user 5.37s system 100% cpu 43.066 total
$ grep -c "error" fullbuild.log ; grep -n "TwistChain" fullbuild.log
0
$ lake env lean docs/tickets/checks/T2431-check.lean > /dev/null 2>&1 ; echo exit=$?
exit=0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/TwistChain.lean ; echo grep-exit=$?
grep-exit=1
```

### b.5 Axioms and the targets' statements (the theorem types are the pins, checked by `example`)
```
$ lake env lean scratch/ax.lean   (import RBM3D.BA.TwistChain; #print axioms; #check; example (d) : BATwistLoopBase d := baTwistLoopBase_holds d; likewise BAChainTL)
'RBM.BA.baTwistLoopBase_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baChainTL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.BA.baTwistLoopBase_holds : ∀ (d : ℕ), RBM.BA.BATwistLoopBase d
RBM.BA.baChainTL_holds : ∀ (d : ℕ), RBM.BA.BAChainTL d
(the two `example` lines of the scratch file elaborate without error: no further output)
$ sed -n 164,166p RBM3D/BA/TwistPins.lean ; sed -n 185,188p RBM3D/BA/TwistPins.lean   (the pins)
def BATwistLoopBase (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    STG0M (baFMz sz z) → BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) (fun _ => 0)
def BAChainTL (d : ℕ) : Prop :=
  BAMainIndTL d STAny → STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z) →
    STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz → BATwistLoopBase d →
      (∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) → BAMLOutTL d
$ grep -n "^theorem baTwistLoopBase_holds\|^theorem baChainTL_holds" RBM3D/BA/TwistChain.lean
110:theorem baTwistLoopBase_holds (d : ℕ) : BATwistLoopBase d := by
240:theorem baChainTL_holds (d : ℕ) : BAChainTL d := by
```

### b.6 The compiled nonempty instances (`TwistChain.lean:266-295`; `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`)
```
$ sed -n 269,295p RBM3D/BA/TwistChain.lean
section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.MFixedPointInst
local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Target 1 at the datum: TL2 at the zero sequence; `G_0 = M` at the carrier is the one hypothesis. -/
example (hG : STG0M (baFMz sz0 zSeq)) : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 0) :=
  baTwistLoopBase_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq flow_sz0 hG

/-- Target 2 at `t ≡ 0` (the class mixed with the chain to `t' = T0/2`): the TL2 conjunct; the base premise `BATwistLoopBase 3` is
`baTwistLoopBase_holds 3`. -/
example (hm : BAMainIndTL 3 STAny) (hh : STHorizonG 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z))
    (hb : STBaseG 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
    (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) :
    BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 0) :=
  (baChainTL_holds 3 hm hh hb (baTwistLoopBase_holds 3) hG le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
    (by norm_num) sz0 zSeq flow_sz0 (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])).2.2.2.2.2

/-- Target 2 at `t ≡ 1/2` (`1/2 ≤ T0` by `half_lt_t0`): the six conclusions, the TL2 conjunct extracted. -/
example (hm : BAMainIndTL 3 STAny) (hh : STHorizonG 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z))
    (hb : STBaseG 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz)
    (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) :
    let C := baFMz sz0 zSeq; STLKgL C μ0 (fun _ => 1 / 2) ∧ STLmaxgL C μ0 (fun _ => 1 / 2) ∧ STDecaygL C μ0 (fun _ => 1 / 2) ∧
      STExp2gL C μ0 (fun _ => 1 / 2) ∧ STLocalEntrygL C μ0 (fun _ => 1 / 2) ∧ BATwistLoopLaw C μ0 (fun _ => 1 / 2) :=
  baChainTL_holds 3 hm hh hb (baTwistLoopBase_holds 3) hG le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
    (by norm_num) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)

end Inst
```

### b.7 Name clash, diff, ports
```
$ grep -rn "baTwistLoopBase_holds\|baChainTL_holds\|TwistChain_" RBM3D RBM3D.lean | grep -v "RBM3D/BA/TwistChain.lean" | wc -l
       0
$ git grep -l "baTwistLoopBase_holds\|baChainTL_holds\|TwistChain_" $(git for-each-ref --format="%(refname)" refs/heads) -- RBM3D RBM3D.lean | grep -v "t/T2431:RBM3D/BA/TwistChain.lean" | wc -l
       0
$ git diff --stat main...t/T2431
 RBM3D/BA/TwistChain.lean | 297 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 297 insertions(+)
$ git status --short
```
Ports from RBM1D/RBM2D: none (no file of `../RBM1D` or `../RBM2D` was read or copied; every copy above is from RBM3D files of the worktree base `aa2b87e`, which is `main` at this time), so no RBM1D/RBM2D diff-stat applies.

### Narrative (facts from the files and the tool log above)
- Verdict: both targets proved in the one new file, `RBM3D/BA/TwistChain.lean`, 297 lines against the stop line 1,000 (preflight predicted ≈ 370). The two theorem types are the TL0 pins (`TwistPins.lean:164-166, 185-188`) verbatim, by `example` (b.5); no hypothesis added, nothing weakened.
- Axioms of both targets: `propext`, `Classical.choice`, `Quot.sound` (b.5). No `sorry`/`admit`/`native_decide`/`axiom` (b.4).
- `baTwistLoopBase_holds`: `STG0M` rewrites `C.G n 0 ω` to `C.M n`; `BAMfine_eq` gives `M` the offset form with `MB = BAMB` (`0 < Im m_F` at every `n` is `(BAflow_real … n).1.1`, not eventual); `TwistChain_chg_off` carries `twChg M σ` to the offset form with `BAMsigma σ MB`; `TwistChain_loop_offset` evaluates `twLoopX` (`twCirc_holds` at `X₂ = M`, the difference `X₂ − M` is `0`) and `TwistChain_trP_offset` evaluates `twTrP` (`card_Iblk`); on the other side `twK_ba` and `Θ_0 = Ring.inverse 1 = 1` (`simp?`: `Ring.inverse_one`) give the same product. So `‖L̃_0 − K̃_0‖ = 0` for every `n, σ, a, c₁, c₂, ω` and `TwistChain_precL_of_zero` closes with `ζ = Bctl^{3/2} ≥ 0` (`mainIndBase_bctl_nonneg`). The exponent `3/2` is not used.
- `baChainTL_holds`: `TwistChain_posConcl` is the twin of `stPosConclG_of_mainIndG` with the invariant `STConclgL ∧ BATwistLoopLaw`; the step feeds `BAMainIndTL d STAny` the invariant (LocalMax from LocalEntry by `STLocalMaxgL_of_STLocalEntrygL`) with regime `trivial`, and `STConStInd` by `stChainSteps` with `K ≥ 2/(𝔠_d min(2𝔠𝔡, ε/2))` as in the merged proof. `baChainTL_holds` runs the chain to `t'` and mixes the zero sequence and `t'` on the class `t_n = 0` with five copied mixes and `TwistChain_TL2_mix`.
- Instances (b.6): target 1 at `sz0` with `STG0M` as hypothesis; target 2 at `t ≡ 0` (mixed class; TL2 conjunct extracted, `BATwistLoopBase 3` discharged by `baTwistLoopBase_holds 3`) and at `t ≡ 1/2` (`half_lt_t0`, six conclusions); `BAMainIndTL 3 STAny`, `STHorizonG`, `STBaseG`, `STG0M` at the carrier stay hypotheses (BA-V's owed pins); `d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, no collapsed window.
- `RBM3D.lean` is not changed on the branch: `git show --stat` of the T2430 commits `3f8e049` and `66632ff` lists only `RBM3D/BA/TwistQV.lean`, and of the merge commit `aa2b87e` lists `RBM3D.lean | 1 +`. The full `lake build` of b.4 was run with a temporary import line (reverted; `git status --short` is empty). The hub adds `import RBM3D.BA.TwistChain` after the last `import` line (`RBM3D.lean:474` at this time).

## (c) Verified Mathlib names (`#check` in the scratch file `ax.lean`, output above in the tool log; used here)
- `Ring.inverse_one` (`Ring.inverse 1 = 1`), `Finset.sum_ite_eq`, `Finset.sum_const`, `nsmul_eq_mul`, `Finset.sum_congr`, `Real.rpow_nonneg`, `exists_nat_ge`, `div_le_iff₀`, `Nat.pos_of_ne_zero`, `tendsto_natCast_atTop_iff`, `Matrix.one_apply`, `ite_mul`, `Matrix.conjTranspose_apply`, `Complex.star_def`, `sub_eq_zero`, `Set.mem_ofPred_eq`: all exist with the used signatures.
- `simp?` on `BATheta … 0 σ₁ σ₂ = 1`: `simp only [BATheta, PropThetaQ, Complex.ofReal_zero, zero_smul, sub_zero, Ring.inverse_one]`.
- Names verified absent: none searched (the clash grep of b.7 covers the new RBM3D names only).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2431a` not needed): both statements are the TL0 pins verbatim; the proofs add no Lean/paper statement difference.
- Remaining premises, owed by BA-V and unchanged: `BAMainIndTL d STAny` (V2a/V2b: the step), `STG0M` at the carrier (`GLoopAtT0`), `STHorizonG` and `STBaseG` at the BA data. Registry: none; the owed line is still listed in the full-build log: `  RBM.BA.BATwistLoopLaw: 0 [no certificate]` (log line 5267), as the ticket says.
- Observation: `STBaseG` is a separate premise of the pin `BAChainTL` although `stBaseG_of_init` (`MainIndBase.lean:110`) derives it from `STLK0`, `STG0M`, `STKboundgL`; not changed (frozen pin).
- Observation: `STG0M` is used twice in `baChainTL_holds`: at `k = 0` of the chain (inside `TwistChain_posConcl`) and for the zero sequence of the mix.
