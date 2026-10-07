Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct  7 05:54:13 UTC 2026

### (i) Exponent table

Notation: `N = sz.size n = (W L)^d` (`Defs/Sizes.lean:157`; `card (Idx d L W) = (W L)^d`, `:160`, equals the `((W*L)^d : ℕ)` of `L1t`/`L2t`, `Pins.lean:617-630`), `ε` the slack of `UNJakk`/`UNUywk`/`UNEMCTE2k`, `t* = N^{-1+τ}`, `#(b₁,b₂) = 4`.

| quantity | value | constraint | slack |
|---|---|---|---|
| `c'` (`UNClaimRowk`/`UNClaimRow`, `Pins.lean:815`, `PinsK.lean:442`) | `𝔠𝔡/30` | `> 0`: `hA.1 : 0<𝔠`, `hA.2.1 : 0<𝔡` (`Admissible`, `Sizes.lean:177`) | at `(1/6, 1/10)`: `1/1800` |
| slack `ε` used in `UNJakk`,`UNUywk`,`UNEMCTE2k` (target 1) | `τ/4` | `> 0` (needs `0<τU`) | — |
| `L₁` bound: `∫ w·L1t ≤ 4·N⁻¹·N·N^{ε}N^{1-c'+Cτ}` | `B = 4 N^{τ/4+1-c'+Cτ}` | per `y`: `UNJakk` at `s=univ.erase u`, `i=u`, `a↦x, b↦y` (`Σ_{b₁b₂}`, `Finset.sum_comm`, triangle) | equals `B` exactly |
| `L₂` bound: `∫ w·L2t ≤ 4·N⁻²·N·N^{ε}N^{2-c'+Cτ}` | `= B` | per `y`: `UNUywk` at `s=(univ.erase u).erase v`, `i=u`, `j=v`, `i≠j` | equals `B` exactly |
| `B ≥ 0` (needed by `UNEMCTE2k`) | `B>0` | `N>0` from `W_pos`, `three_le_L` | — |
| `(EMCTE2)` output | `N^{τ/4}N^{-1+Cnτ}·B = 4N^{-c'+(Cn+C+1/2)τ}` | exponent identity `(ε-1+Cnτ)+(ε+1-c'+Cτ) = -c'+(Cn+C+1/2)τ` | exact |
| target 1 conclusion constant `Cn' = Cn+C+1` | `Cn+C+1` | `4N^{-c'+(Cn+C+1/2)τ} ≤ N^{-c'+(Cn+C+1)τ}` iff `N^{τ/2} ≥ 4` | eventual: `N ≥ 4^{2/τ} = 2^{4/τ}`; `τ=1/4`: `N≥2^16` (have `2^21`, ratio `N^{1/8}=6.17 ≥ 4`); `τ=1/100`: `N ≥ 2^400`, `sz0` index `n ≥ 2179484` (eventual only) |
| single threshold of target 1 | `n ≥ n₀(UNEMCTE2k, UNJakk, UNUywk at (C₀,τ/4)) ∧ N^{τ/2} ≥ 4` | `filter_upwards`; uniform in `z,t,s,y` | `SizeTendsto` gives the second |
| `τ'` of `unGreenCorr` (`GreenCorr.lean:864-870`) | `c'/(2(Cmax+1))`, `Cmax = max 0 (sup'_{nf≤k} Cn nf)` (`:810`) | depends on `E,k,c',Cn` only, not `O,r,a,b` | `Cmax·τ' ≤ c'/2`; at `Cmax=3`: `τ'=6.94e-5`, `Cmax·τ' = 2.08e-4 ≤ 2.78e-4` |
| `τ₀` of target 6 | `min τ' (inf'_{nf≤k} τ₀(nf))` | `>0`; order `∃τ₀, ∀τU, ∀O` of `UNUnivMainRow` (`Pins.lean:745`) is met (no dependence on `O`) | at the instance `6.94e-5` |
| `ρ` range (target 4) | `a=c/π`, `b=C/π`, `0<a` | `UNDens` (`Pins.lean:462`) at `x=E` (`|E-E|=0 ≤ δ`), `0<η≤10`: `c ≤ Im m ≤ C`; `Im m(E+iη)/π → ρ n` along `𝓝[>] 0` (`ge_of_tendsto`, `le_of_tendsto`) | msc, `E=0`: `c=9/100`, `C=1`; `ρ=1/π = b` (upper bound attained with `≤`) |
| `UNGreenCorr` hypotheses at `ρ` | `∀ᶠ n, a ≤ ρ n ≤ b`, `0<a` | `UNGreenCorr` (`Pins.lean:535`) | as above |
| `size → ∞` for `UNGreenCorrAll` (`Pins.lean:546`) | from `hA.2.2.1 : SizeTendsto` | `ℝ`-cast form vs `ℕ`-form: `tendsto_natCast_atTop_iff` | — |
| `3 ≤ d` | passed on only | argument of `unApriori_of_trLocal` (`Apriori.lean:149`) and of `UNClaimRowk` | `d=3` |
| transfer (target 5) | no measurability, any `O` | `apriori_ouMat_zero_integral` (`Apriori.lean:89`) with `g A := if h : A.IsHermitian then kPoint k O E h.eigenvalues else 0`; `ouMat M n 0 ω = M.H n ω.1` | none (equality) |

Consistency of the sums in `L1t`/`L2t` (`Pins.lean:617-630`) with the pins (`Pins.lean:694-722`, `PinsK.lean:365-390`): `L1t` has `(G²)_aa S°_ab G_bb`, `UNJak` has `Σ_x (G²)_xx S°_xy G_yy` (`a↦x`, `b↦y`); `L2t` has `(G₁²)_ab S°_ab (G₂²)_ba`, `UNUyw` has `Σ_x (G₁²)_xy S°_xy (G₂²)_yx` (`a↦x`, `b↦y`); both sum over `y` outside (`N` terms), prefactors `N⁻¹`, `N⁻²`. The `lamV`/`lam` argument of `scirc` is `K.lamV sz n` in both the pins and `L1t`/`L2t` (`PinsK.lean:345-390`).

### (ii) One concrete nondegenerate instance

Data: `d=3`, `sz0` (`Defs/Sizes.lean:260`: `L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`), `𝔠=1/6`, `𝔡=1/10`, `c'=1/1800`, `E=0`, `K=UNKind.band 3`; target 1 at `nf=2`, `τU=1/4`, `Cn=C=1` (so `Cn'=3`); target 6 at `m=msc`, `δ=1/2`, `ρ_n≡rhoSC 0`, `k=1`, `Cn nf=3` for `nf≤1`, `τ₀(nf)=1/4`. Hypotheses that remain pins of other tickets (owed): `UNEMCTE2k`, `UNJakk`, `UNUywk` (target 1), `UNTrLocal`, `UNClaimAll` (target 6).

Command and output (script `inst.py` in the scratchpad `T2309/`, pure Python arithmetic, no Lean):

```
$ python3 -I inst.py
sz0 admissible(1/6,1/10) for n=0..30: True
n=0: L=4 W=32 N=(WL)^3=2097152 = 2^21.0  W/N^c=2.828  lam=1/64  W^(-d/2+dd)=0.00781
c' = cc*dd/30 = 1/1800 = 0.0005555555555555556
tau=0.25 Cn=1 C=1: lnL1=lnL2=lnB: True; ln(out)=10.4758 <= ln N^(-c'+Cn' tau)=10.9090: True; N^(tau/2)=6.1688>=4: True; exponent identity: True
hypotheses of target 1 at (b): SizeTendsto (N_n=2^21 (n+1)^18 ->inf), tau>0, three pins; Cn'=Cn+C+1 = 3
tau=1/4: need log2 N >= 16, first sz0 index n0=0
tau=1/100: need log2 N >= 400, first sz0 index n0=2179484
Im msc(i eta), eta in (0,10]: min=0.09902 (>= c=0.09: True), max=0.99501 (<= C=1: True)
limit: Im msc(i eta)/pi at eta=1e-1,1e-3,1e-6,1e-9: [0.302792031, 0.318150771, 0.318309727, 0.318309886] -> rhoSC(0)=sqrt(4)/(2pi)= 0.3183098861837907
a=c/pi=0.028648 <= rho=0.318310 <= b=C/pi=0.318310: True
Cmax=3: tau'=c'/(2(Cmax+1))=6.9444e-05 >0; Cmax*tau'=2.0833e-04 <= c'/2=2.7778e-04: True; -c'+Cmax*tau'=-3.4722e-04<0
Cmax=6: tau'=c'/(2(Cmax+1))=3.9683e-05 >0; Cmax*tau'=2.3810e-04 <= c'/2=2.7778e-04: True; -c'+Cmax*tau'=-3.1746e-04<0
Cmax=10: tau'=c'/(2(Cmax+1))=2.5253e-05 >0; Cmax*tau'=2.5253e-04 <= c'/2=2.7778e-04: True; -c'+Cmax*tau'=-3.0303e-04<0
tau0 = min(tau',tau0(0),tau0(1)) = 6.944444444444444e-05
tU=tau0: ouTStar=N^(-1+tU)=4.77319e-07 at N=2^21 (>0); N^tU=1.0010
window nonempty: True
card Idx = N: (W*L)^d = 2097152 = size: 2097152
```

Reading: (1) `sz0` is admissible at `(1/6,1/10)` for `n = 0..30` (`W ≥ N^{1/6}`, `W^{-1.4} ≤ lam ≤ 10`), `N_0 = (32·4)^3 = 2^21 = card (Idx 3 4 32)`, no `N=0`, nonempty index. (2) Target 1 at `τ=1/4`: `L₁`, `L₂` bounds equal `B`, the exponent identity holds, and `N^{τ/2} = 6.17 ≥ 4` already at `n=0`; for smaller `τ` the last step is the eventual threshold `N ≥ 2^{4/τ}` (stated in `filter_upwards`, not a hypothesis). (3) Target 4 (external-style limit, TEAM §8 lesson 14): `Im msc(iη) = (√(η²+4) − η)/2`, strictly decreasing in `η`, equal to `0.0990` at `η=10` and `→ 1` as `η ↓ 0`; `Im msc(iη)/π → 1/π = rhoSC 0` (numerics above: `0.3183098861` at `η=1e-9`); `c=9/100 ≤ Im msc ≤ 1 = C` on `0<η≤10`, so `a = 0.09/π ≤ ρ = 1/π ≤ b = 1/π`. (The `max` in the grid output is the grid's maximum, `η ≥ 0.01`; the supremum `1` is not attained.) (4) Target 6: `τ' = c'/(2(Cmax+1)) > 0` at `Cmax = 3`, `-c' + Cmax τ' < 0`; `ouTStar > 0`, window `N^{-1-τ} ≤ N^{-1+τ}` nonempty at `τU = τ₀`. The window `InWindow` forces `z.im ≥ N^{-1-τ} > 0`, so the entry bound `‖G_xy‖ ≤ 1/Im z` is finite (bounded measurable integrands).

Pins that stay hypotheses of the instances, and why they are satisfiable: `UNTrLocal sz0 band msc 0 (1/2)` is the band tracial local law (`UNTrLocalBandRow`, `Pins.lean:842`, shape `δ ≤ κ/2`, `|E| ≤ 2-κ`, here `κ=1`); `UNClaimAll sz0 band 0` is the Claim `(417)` at `c'=𝔠𝔡/30`; the three pins of target 1 are the owed `(EMCTE2)`, `(jaklsdufowe)`, `(uywy7723r3rf)`. Their rows (`UNClaimRow`, target 3) take exactly these as premises; no premise is added.

### Verdicts

- Target 1 `unClaim417C_of_rows` (check 2.1): PASS. Hypotheses `SizeTendsto`, `0<τU`, three pins consistent at the instance; exponent closes (`N^{τ/2} ≥ 4` eventual, from `SizeTendsto`, slack `τ/4`); `Cn' = Cn+C+1`.
- Target 2 `unClaimRowk` (check 2.2): PASS. Follows from target 1 with `0 < 𝔠𝔡/30` and `hA.2.2.1`.
- Target 3 `unClaimRow` (check 2.3): PASS. `UNClaimRowk_band.1 (unClaimRowk _)` (`PinsK.lean:573`, an `↔`; `.1` has type `UNClaimRowk (fun d => UNKind.band d) → UNClaimRow`).
- Target 4 `unDens_rho_bounds` (check 2.4): PASS. `a = c/π > 0`, `b = C/π`; at msc `E=0` verified above.
- Target 5 `univMain_transfer` (check 2.5): PASS (mathematically an equality of integrals by `ouMat M n 0 ω = M.H n ω.1` and first marginal of `ouP`; no numeric constants).
- Target 6 `univMainRow` (check 2.6): PASS. `τ₀ = min τ' (inf' τ₀(nf))` depends on `E,k,c',Cn` only, the order `∃τ₀ ∀τU ∀O` is met; `UNGreenCorr` used with `r := ρ`, `a,b` from target 4; `UNApriori` from `unApriori_of_trLocal`.
- Target 7 `unCore'_holds` (check 2.7): PASS (`un_core'_of_univMainRow univMainRow`, `GUETranslation.lean:791`; consumes the unprimed `UNUnivMainRow`).
- Instances (a)–(d): PASS at the data above; each keeps only the owed pins named in the ticket.

Overall: PASS. No exponent fails to close, no hypothesis set is empty, no missing input.

## (a′) Preflight corrections

None.

## (b) Script output — Wed Oct  7 06:10:48 UTC 2026

Branch `t/T2309`, one commit on top of `3c11598` touching exactly `RBM3D/Universality/UnivMain.lean` (new) and
`RBM3D/Test/Axioms.lean` (3 deletions).  Sections below: build, axioms, target and instance statements; scratch check
against the check file; name clash and port; registry pre-check and full build.

```
$ date -u; git log --oneline -1; git status --short | wc -l   # worktree RBM3D-wt/T2309, branch t/T2309
Wed Oct  7 06:08:57 UTC 2026
34f43ca T2309: UN-24 Universality/UnivMain (UNUnivMainRow, UNClaimRow, UNClaimRowk, UNCore')
       0
$ lake build RBM3D.Universality.UnivMain > out 2>&1; echo exit=$?; tail -1 out; grep -c "UnivMain.lean.*\(warning\|error\)" out
exit=0
Build completed successfully (3410 jobs).
0
$ grep "UnivMain.lean.*depends on axioms" out | sed "s/^info: RBM3D.Universality.//"   # #print axioms of every public declaration
UnivMain.lean:674:0: 'RBM.Univ.unClaim417C_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:675:0: 'RBM.Univ.unClaimRowk' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:676:0: 'RBM.Univ.unClaimRow' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:677:0: 'RBM.Univ.unDens_rho_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:678:0: 'RBM.Univ.univMain_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:679:0: 'RBM.Univ.univMainRow' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:680:0: 'RBM.Univ.unCore'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:681:0: 'RBM.Univ.UnivMainInst.inst_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:682:0: 'RBM.Univ.UnivMainInst.inst_univMain_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:683:0: 'RBM.Univ.UnivMainInst.inst_claim417_core' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:684:0: 'RBM.Univ.UnivMainInst.inst_claimAll_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:685:0: 'RBM.Univ.UnivMainInst.inst_rho_bounds_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:686:0: 'RBM.Univ.UnivMainInst.inst_transfer_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:687:0: 'RBM.Univ.UnivMainInst.inst_unClaimRowk_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
UnivMain.lean:688:0: 'RBM.Univ.UnivMainInst.inst_core'_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/UnivMain.lean; echo grep-exit=$?
grep-exit=1
$ python3 -I extract.py <targets 1-7>   # statements extracted from the file (signature up to `:=`)
-- RBM3D/Universality/UnivMain.lean:393
theorem unClaim417C_of_rows {d : ℕ} (K : UNKind d) (sz : Sizes d) (hsize : sz.SizeTendsto)
    (E : ℝ) (nf : ℕ) (τU c' Cn C : ℝ) (hτ : 0 < τU)
    (hEM : UNEMCTE2k K sz E nf τU Cn) (hJ : UNJakk K sz E nf τU C c')
    (hU : UNUywk K sz E nf τU C c') :
    UNClaim417C sz (K.M sz) E nf τU c' (Cn + C + 1) := by
-- RBM3D/Universality/UnivMain.lean:466
theorem unClaimRowk : ∀ K : ∀ d, UNKind d, UNClaimRowk K := by
-- RBM3D/Universality/UnivMain.lean:476
theorem unClaimRow : UNClaimRow := UNClaimRowk_band.1 (unClaimRowk _)
-- RBM3D/Universality/UnivMain.lean:486
theorem unDens_rho_bounds (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : UNDens m E ρ δ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n in atTop, a ≤ ρ n ∧ ρ n ≤ b := by
-- RBM3D/Universality/UnivMain.lean:509
theorem univMain_transfer {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) :
    ∫ ω, kPoint k O E (M.herm n ω).eigenvalues ∂M.μ =
      ∫ ω, kPoint k O E (ouMat_isHermitian M n 0 ω).eigenvalues ∂(ouP M n) := by
-- RBM3D/Universality/UnivMain.lean:533
theorem univMainRow : UNUnivMainRow := by
-- RBM3D/Universality/UnivMain.lean:557
theorem unCore'_holds : UNCore' := un_core'_of_univMainRow univMainRow
$ python3 -I extract.py <instances>   # the compiled nonempty instances (namespace RBM.Univ.UnivMainInst)
-- RBM3D/Universality/UnivMain.lean:587
theorem inst_univMain_band_zero :
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
      UNClaimAll sz0 (UNModel.band sz0) 0 →
        ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
          UNUnivMain sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 1
            (UNInst.bump : (Fin 1 → ℝ) → ℝ) τU := by
-- RBM3D/Universality/UnivMain.lean:601
theorem inst_claim417_core :
    UNEMCTE2k (UNKind.band 3) sz0 0 2 (1 / 4) 1 →
      UNJakk (UNKind.band 3) sz0 0 2 (1 / 4) 1 (1 / 1800) →
        UNUywk (UNKind.band 3) sz0 0 2 (1 / 4) 1 (1 / 1800) →
          UNClaim417C sz0 ((UNKind.band 3).M sz0) 0 2 (1 / 4) (1 / 1800) 3 := by
-- RBM3D/Universality/UnivMain.lean:615
theorem inst_claimAll_band_zero :
    UNLocAvgBand → UNOUClaims → UNClaimAll sz0 (UNModel.band sz0) 0 := by
-- RBM3D/Universality/UnivMain.lean:628
theorem inst_rho_bounds_zero :
    ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n in atTop, a ≤ (fun _ : ℕ => rhoSC 0) n ∧ (fun _ : ℕ => rhoSC 0) n ≤ b :=
-- RBM3D/Universality/UnivMain.lean:633
theorem inst_transfer_band_zero :
    ∫ ω, kPoint 1 (UNInst.bump : (Fin 1 → ℝ) → ℝ) 0 ((UNModel.band sz0).herm 0 ω).eigenvalues
        ∂(UNModel.band sz0).μ =
      ∫ ω, kPoint 1 (UNInst.bump : (Fin 1 → ℝ) → ℝ) 0
        (ouMat_isHermitian (UNModel.band sz0) 0 0 ω).eigenvalues ∂(ouP (UNModel.band sz0) 0) :=
-- RBM3D/Universality/UnivMain.lean:643
theorem inst_unClaimRowk_band_zero :
    UNLocAvgBand → UNOUClaims → UNClaimAllC sz0 ((UNKind.band 3).M sz0) 0 := by
-- RBM3D/Universality/UnivMain.lean:661
theorem inst_core'_band_zero :
    UNL32 → UNGUELocal → UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
      (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
        UNClaimAll sz0 (UNModel.band sz0) 0 →
          UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1
            (UNInst.bump : (Fin 1 → ℝ) → ℝ) :=
-- RBM3D/Universality/UnivMain.lean:578
theorem inst_nondegenerate :
    (UNInst.bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ (UNInst.bump : (Fin 1 → ℝ) → ℝ) (fun _ => 3) = 0 ∧
      sz0.size 0 = 2097152 ∧ 0 < rhoSC 0 :=
```
```
$ lake env lean T2309-check-scratch.lean; echo exit=$?   # check file + `import RBM3D.Universality.UnivMain` + examples:
exit=0
lines containing 'error': 0
example : T2309_unClaim417C_of_rows := @RBM.Univ.unClaim417C_of_rows
example : T2309_unClaimRowk := RBM.Univ.unClaimRowk
example : T2309_unClaimRow := RBM.Univ.unClaimRow
example : T2309_unDens_rho_bounds := RBM.Univ.unDens_rho_bounds
example : T2309_univMain_transfer := @RBM.Univ.univMain_transfer
example : T2309_univMainRow := RBM.Univ.univMainRow
example : T2309_unCore'_holds := RBM.Univ.unCore'_holds
example : T2309_inst_univMain_band_zero := RBM.Univ.UnivMainInst.inst_univMain_band_zero
example : T2309_inst_claim417_core := RBM.Univ.UnivMainInst.inst_claim417_core
example : T2309_inst_claimAll_band_zero := RBM.Univ.UnivMainInst.inst_claimAll_band_zero
example : T2309_inst_rho_bounds_zero := RBM.Univ.UnivMainInst.inst_rho_bounds_zero
$ name-clash: for n in <public names>: git grep -nw -e $n main -- RBM3D RBM3D.lean | wc -l   (main = 1d19466)
unClaim417C_of_rows=0 unClaimRowk=0 unClaimRow=0 unDens_rho_bounds=0 univMain_transfer=0 univMainRow=1 unCore'_holds=0 UnivMainInst=0 inst_nondegenerate=0 inst_univMain_band_zero=0 inst_claim417_core=0 inst_claimAll_band_zero=0 inst_rho_bounds_zero=0 inst_transfer_band_zero=0 inst_unClaimRowk_band_zero=0 inst_core'_band_zero=0 
$ git grep -nw -e univMainRow main -- RBM3D RBM3D.lean | cut -c1-110   # the one non-zero count (a docstring of Pins.lean)
main:RBM3D/Universality/Pins.lean:562:`ρ_n`.  RBM2D `Pins.lean:386` (`UnivMain`). Consumer (RBM2D `c9a24cf`): 
$ declaration-level: git grep -nE "(theorem|def|lemma|abbrev|instance) (RBM\.Univ\.)?(univMainRow|unClaimRow|unClaimRowk)( |$)" main -- RBM3D RBM3D.lean | wc -l
       0
$ ls RBM3D/Universality/UnivMain.lean on main: 0 (count)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; ... diff --stat c9a24cf HEAD -- RBM2D/Universality/UnivMain.lean
9e0f275
 RBM2D/Universality/UnivMain.lean | 105 ++++-----------------------------------
 1 file changed, 11 insertions(+), 94 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/UnivMain.lean | wc -l
     552
$ git diff --stat main...t/T2309; git diff HEAD~1 HEAD -- RBM3D/Test/Axioms.lean | grep "^[-+]"
 RBM3D/Test/Axioms.lean           |   3 -
 RBM3D/Universality/UnivMain.lean | 690 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 690 insertions(+), 3 deletions(-)
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNUnivMainRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNClaimRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNClaimRowk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
```
```
$ cat precheck.lean  (scratch, uncommitted, outside the worktree)
import RBM3D
import RBM3D.Universality.UnivMain

#assert_rbm_axioms
$ lake build RBM3D.Test.Axioms; lake env lean precheck.lean > out 2>&1; echo exit=$?
Build completed successfully (2 jobs).
exit=0
$ grep -n "axiom audit:\|^registry:\|premises found\|unregistered\|error" out | cut -c1-170
1:axiom audit: 8725 theorems, 2867 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
150:premises found by scanning: 149 (borrowed 1, owed 90, structural 41, refuted 6, superseded 11).
151:registry: 2 borrowed + 141 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ owed count, base (git show HEAD~1) vs branch (python over `def owedProps`)
owedProps entries: base 144 branch 141 difference 3 | removed: ['RBM.Univ.UNClaimRow', 'RBM.Univ.UNClaimRowk', 'RBM.Univ.UNUnivMainRow'] | added: []
$ full `lake build` of the worktree, run earlier in this session (tool log); RBM3D.lean got a temporary uncommitted
  `import RBM3D.Universality.UnivMain` (after `import RBM3D.Graph.LWExpTerm5`), restored afterwards from a copy:
  06:03:21 UTC, root WITHOUT the import: exit=1; "error: RBM3D.lean:349:0: axiom audit: 3 premise(s) that no theorem of this
    development proves are in none of ...: [RBM.Univ.UNUnivMainRow, RBM.Univ.UNClaimRow, RBM.Univ.UNClaimRowk]"
  06:03:40-06:04:30 UTC, root WITH the import: exit=0 ; grep of its output:
3721:info: RBM3D.lean:350:0: axiom audit: 8725 theorems, 2867 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
3871:registry: 2 borrowed + 141 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
3990:Build completed successfully (4116 jobs).
$ git status --short RBM3D.lean | wc -l   # root file restored
       0
```

### Narrative

* `UnivMain.lean` has 690 lines: 25 `private` helpers (prefix `UnivMain_`), the 7 target theorems, 8 instance theorems in
  `RBM.Univ.UnivMainInst` (`inst_nondegenerate` and (a)-(g)).  Targets 1-7 and instances (a)-(d) have exactly the types of
  the check file 2.1-2.7, 3.1-3.4 (the 11 `example`s above compile); (e)-(g) are extra instances of targets 5, 2, 7.
* Port of RBM2D `UnivMain.lean` at `c9a24cf` (552 lines; the file at RBM2D HEAD `9e0f275` differs, diff stat above).
  Adaptations: `gSel` becomes `Gres` (no `conjTranspose` case split); `norm_green_le` is replaced by a private copy of
  `norm_Gres_entry_le` (`Loop/GLoopFlow.lean:519`); `Idx d L W`, `(W L)^d`, extra argument `lam`; the generic `K`
  costs one fact, `Measurable (ouMatC M n t)` (`ouMatC_eq_ouMat_add`, `measurable_ouMat`, `Measurable.add_const`);
  `UNGreenCorr` is applied with the dilation `r := ρ` and `a, b` from target 4.
* Target 1: one eventual threshold (`UNEMCTE2k`, `UNJakk`, `UNUywk` at `(C₀, τU/4)` and `N^{τU/2} ≥ 4` from
  `tendsto_rpow_atTop` and `SizeTendsto`), `B = 4 N^{τU/4} N^{1-c'+Cτ}` for both `L₁` (`Jak`, `s = univ.erase u`) and `L₂`
  (`Uyw`, `s = (univ.erase u).erase v`), `C_n' = C_n + C + 1`; `3 ≤ d` and any `L`-`W` relation are not used.
* Target 4 uses `UNDens` only at `x = E` (`c ≤ Im m ≤ C`, and the limit to `ρ_n`); the Lipschitz part is unused.
* Target 5: `apriori_ouMat_zero_integral` with the test function `A ↦ if h : A.IsHermitian then kPoint … h.eigenvalues
  else 0`; no measurability, every `O`.
* Target 6: `τ₀ = min τ' (inf'_{nf ≤ k} τ₀(nf))` depends on `E, k, c', Cn` only (order `∃ τ₀, ∀ τU, ∀ O` as pinned);
  `UNApriori` is `unApriori_of_trLocal`; `3 ≤ d` is only passed on (`UNGreenCorrAll`, `unApriori_of_trLocal`).
* Instances at `d = 3`, `sz0` (`n = 0`: `N = 2097152`, `inst_nondegenerate`), band model, `E = 0`, `k = 1`, `bump`.
  Hypotheses left: (a) `UNTrLocal`, `UNClaimAll`; (b) `UNEMCTE2k`, `UNJakk`, `UNUywk`; (c), (f) `UNLocAvgBand`,
  `UNOUClaims`; (g) `UNL32`, `UNGUELocal`, `UNTrLocal`, `UNNormBound`, `UNClaimAll`.  Discharged: `Admissible`
  (`UNInst.sz0_adm`), `greenCorrAll`, `UNDens` (`un_dens_msc_zero`), `UNDens'` (`un_dens'_msc_zero`), `IsTestFun bump`,
  `|0| ≤ 2 - 1/2`, `size → ∞`.  (c) and (f) use the merged `unEMCTE2Row`/`unEMCTE2Rowk_band` and `jakUywRow`.
* Not targets: `UNClaimRowBA` (`BA/UNPins.lean:136` is `UNClaimRowk (fun d => UNKind.ba d)`; this file does not import
  `BA/*`; follow-up `unClaimRowk (fun d => UNKind.ba d)` on the BA side); `UNTrLocal`, `UNClaim417`, `UNClaimAll`,
  `UNLocAvgBand`, `UNOUClaims` (owed, hypotheses); `UNBUniv`; `UNInfty1Row`, `UNCoreC`, `UNCoreC'` do not occur in the file (grep).
  `unClaimRow` is the band case of the general `unClaimRowk`; no special case is claimed as the general statement.
* Hub merge note: add `import RBM3D.Universality.UnivMain` to `RBM3D.lean` in the same commit (build output above: the root
  audit fails without it, passes with it); `Axioms.lean` conflicts only in registry lists: union minus the 3 deleted lines.
* No obstruction: no hypothesis added, no target weakened, no merged signature changed.

## (c) Verified Mathlib names (`#check` in this session, scratch `names.lean`; all used in `UnivMain.lean`)

`MeasureTheory.integral_finsetSum`; `MeasureTheory.integrable_finsetSum`; `MeasureTheory.integral_const_mul`;
`MeasureTheory.integral_mono_of_nonneg`; `MeasureTheory.Integrable.of_bound`; `Finset.inf'_le`; `Finset.lt_inf'_iff`;
`tendsto_rpow_atTop`; `ge_of_tendsto`; `le_of_tendsto`; `Ioo_mem_nhdsGT`; `tendsto_natCast_atTop_iff`;
`Measurable.add_const`; `measurable_pi_iff`; `Complex.re_add_im`; `Real.rpow_add`; `Filter.Tendsto.eventually_ge_atTop`;
`div_le_div_of_nonneg_right`; `dite_eq_left` (core).  Deprecated in this toolchain (warning on `#check`, not used):
`MeasureTheory.integral_finset_sum`, `MeasureTheory.integrable_finset_sum`, `dif_pos` (use the names above).

## (d) Open issues and paper-delta candidates

* **T2309a** (design, no paper statement): (1) `UNClaimRow` is proved model-generically (`unClaimRowk`), so the BA row
  `UNClaimRowBA` is one line (hub/BA follow-up); (2) `UNUnivMainRow` uses `UNDens` only through `c/π ≤ ρ_n ≤ C/π`
  (target 4), so the weakness of `UNDens` (DECISIONS §65) is harmless for this row (for the supervisor's T2190a file);
  (3) `UNCore'` is now a theorem (`unCore'_holds`); its own hypotheses `UNL32`, `UNGUELocal`, `UNGreenCorrAll` stay inside it.
* No `T2309c`: no difference between the Lean statements and the check file or the paper was found.
* For `docs/mathlib-api.md`: the check file section 1 `#check`s the deprecated alias `integral_finset_sum`; current name
  `integral_finsetSum`.
