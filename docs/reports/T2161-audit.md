Auditor model: claude-opus-5-5

# T2161 (BA-D1, report-only design) — audit round 1, Sun Oct  4 23:29:22 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2161-audit1` (detached at `t/T2161` = 82e72b3). Scratch scripts: `$A` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161/audit`.
**Verdict: PASS. Needs dispatcher sign-off**: (i) the decided bulk form `ρ_N(E) ≥ κ` changes the energy set that Thm 2.7 covers (report top notice 1); (ii) 57 BA tickets, over DECISIONS §9 O2's limit of 50 (top notice 2). Both are flagged at the top of the prove report, as the ticket requires; Jun decides.

## 1. Build, axioms, hygiene, scope
    $ git diff --name-only main...t/T2161
    RBM3D/Probe/T2161Pins.lean
    $ lake build RBM3D.Probe.T2161Pins > $A/build.out 2>&1; tail -2 $A/build.out
    Build completed successfully (3749 jobs).
    exit=0
    $ grep -c error $A/build.out; grep -c 'warning: RBM3D/Probe/T2161Pins' $A/build.out
    0
    0
    $ (axiom lines in $A/build.out)  std-axiom lines: 125; other 'depends on axioms' lines: 0; #print axioms in file: 125
    $ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom ' RBM3D/Probe/T2161Pins.lean
    0
The branch changes only the sole writable probe; no frozen signature is touched. Probe-only ticket (stays on the branch), so hub steps 3–5 are skipped. The check file `docs/tickets/checks/T2161-check.lean` has only `#check`s of merged names and no pinned text. So each statement is compared with the paper below.

## 2. Statements against the paper (per pin family)
| pin (probe line) | paper | result |
|---|---|---|
| `BASelf` :191, `BAMB` :187 | `(self_m)` 1_2:626, `(def_G0)` 1_2:631 (`N⁻¹tr` = `L^{-d}tr` on blocks) | match |
| `BAmExists`/`BAmUniqReal`/`BAmBoundary` :571-591 | "unique solution, Im m>0" 1_2:626; `m(E)=m(E+i0)` 1_2:715 | match; real-axis uniqueness is Schwarz–Pick (F is a non-Möbius self-map of ℂ₊) |
| `BAWard` :597, `BAPropM` :612 | `lem:propM` (1)(2)(3) 7_8:1847-1906 | match except: `Im m ≳ 1` is a hypothesis (`BAReal`, κ ≤ Im m), T2161b; constants `(d,Λ,κ)` vs the paper's `(d,κ)` (§9 O1/§18; see O2) |
| `BAoffDiag` :631 | `(eq:off_diagM)` A:32-34 (`M'_{0a}=M^{(+,+)}_{0a}`, a≠0) | match |
| `BAImmLower` :645 | [LSY15 L3.5] use at 7_8:1906, now internal | true by Biane's uniform Hölder-1/3 bound on the density + Poisson; bridge only |
| `BAProp5..8` :676-726 | `lem_propTH` 5-8, A:1-70, with `Θ=(1−tM^{(σ,σ')})⁻¹`, `S^{(B)}=I` | shape = merged `Prop5Decay..Prop8ZeroMode`; constants before `L,g,E,m`; `|r| ≤ c|a|`, `0<c<1`; both charge pairs |
| `BAzztE_data` :296 (proved), `BAzztE_Mres` :1704 (proved) | `zztE_BA` 7_8:1796-1808 | stronger: drops `|Re z| ≤ 2−κ` (T2001g) and `Im z ≤ 1` |
| `BAMainInd` :1071 = `STMainIndG` | `lem:main_ind_BA` 7_8:1825 | same quantifier order as merged `STMainInd` (`STMainInd_iff` is `Iff.rfl`); domain `BAdom` (Im m(z) ≥ κ), bridged by `BAendDom_to_dom` |
| `BAGbEXP`, `BAConArg`, `BAStep1`, `BAStep2`, `BAEMn2Exp` :1115-1280 | 7_8:1916-2092 | constants first (`κ,ε,𝔡` → `c`/`𝔠_d`/`C_d`), then the sizes; `≺` at scale N; deterministic `𝒥` in `BAEMn2Exp` as in `(eq:MG_conclusion3_BA)` |
| `BAKsolve` :1295 | `(Kn2sol)` 1_2:1175: `𝒦^{(2)} = W^{-d}(Θ_t M^{(σ1,σ2)})_{a1a2}` | match (`S=1`, 1-loops = m) |
| `BAlanlw`, `BAlweight`, `BAGGGamma` :1429-1450 | B:359-405 | first two match as printed; `GGGamma` has corrected coefficient `(M⁺S⁺)_{xβ}` (T2161a; independently confirmed in §4) |
| `BAEnd_decol/locSC/QUE/BUniv/QDiff`, `BAThm27` :1543-1660 | Thm 2.7 1_2:644-669, `(eq:psikLinfty)`, `(G_bound)`, `(G_bound_ave)`, `(Meq:QUE)`, `(Meq:QUE2)`, `(eq:diffu1)`-`(Meq:QdS2)` with `ΘM` | match, with `|E| ≤ e_λ−κ` replaced by `BAbulk` (ρ_N ≥ κ); universality in the form of DECISIONS §11 (`ρ_N(E)^{-k}` vs `ρ_sc(E')^{-k}`, `|E'|<2`); `∩_z` inside the probability (T2001b); QUE window `W^{-ε0} g W^{d/2}/N`, exponent `−(2ε0∧2𝔡/5)+2c+τ`; QdS `𝓑²((g²W^d)^{-1/5}+𝓑)` |

Bulk condition (ticket's open question): the prover rejects both options and proposes a third form, with evidence. Auditor's independent recomputation (`python3 $A/aud_ba.py`, `$A/aud_cls.py`):
    L=4 g=0.5: support edges -3.6200 3.6200  #sign changes of 1(rho>1e-6) on grid=6 (2 = one interval)
    L=5 g=0.2: support edges -2.2450 2.2550  #sign changes of 1(rho>1e-6) on grid=2 (2 = one interval)
    L=4 g=0.3: support edges -2.6350 2.6350  #sign changes of 1(rho>1e-6) on grid=2 (2 = one interval)
    cusp L=4 g=0.354226 E=2.507922 eta=0.001: rho=1.663e-02 rho/eta^(1/3)=0.1663
    cusp L=4 g=0.354226 E=2.507922 eta=1e-05: rho=3.622e-03 rho/eta^(1/3)=0.1681
    L=4 g0=4.6723: edges -28.3200 28.3200; interior gaps on grid=6; rho(E*=0.0)=0.17847
    L=5 g0=0.1562: edges -2.1500 2.1500; interior gaps on grid=0; rho(E*=-0.00015)=0.29835
    L=4 g0=0.2223: edges -2.3350 2.3350; interior gaps on grid=0; rho(E*=0.0)=0.28308
This confirms the report's three claims. At `L=4`, `g=1/2` there are interior gaps, so "λ ≤ 1" does not give an interval. At odd `L` the support is asymmetric. Near `g_c(4)` there is a `ρ ∝ η^{1/3}` cusp inside `|E| ≤ e−0.1`. The class values `ρ_N(E_*)` agree with b.5 to 5 digits. The ρ-form is the only form among those compared that is defined in every class and gives `Im m ≳ 1`. It changes the stated energy set: it is defined for odd `L` and gaps, and it drops the cusp points. That is a dispatcher/Jun decision (T2161b).

## 3. Vacuity, hidden hypotheses, cycles
- Structure fields: `FlowFM` (:829) has only data fields (`L K G M S eta m`). `FlowPt` (:1933) is instance data with `BAReal` proved by `exists_flowPt` from `BAzztE_data`. `BAProp5to8` bundles pins. No hypothesis is hidden in a field.
- Endpoints: `BAThm27` contains no `BAmExists`/`BAData` premise. `m = BAm` is a definition (choice; `0` when no solution), so `BArho = 0` in a gap and the bulk condition fails there.
- No cycle: glue pins go `BAMainInd → locSC → {decol, QUE, BUniv, QDiff}` and chain pins `→ BAMainInd` (`BAThm27_skeleton(_chain)` :1851, :1868). Every import is a merged module (build above).
- External hypothesis, limit check: LSY Thm 2.2 enters only through `BAGlueUniv` (BA-N1/N2). For fixed `(L,g₀)`, `ρ_N(E_*)` does not depend on `n` (class sequences), so the §11 normalisation is a fixed positive number (0.178/0.298/0.283 above). The full LSY check is deferred to UN-D1/T2162 (report b.9 row 11). Accepted for a design ticket.

## 4. Extreme inputs (ticket acceptance: "tried at one extreme input")
    $ python3 $A/aud_ba.py | tail -2     # BAoffDiag / BAPropM(2) at g = Λ = 10, L = 6, worst E with Im m ≥ 0.05
    BAoffDiag extreme g=10 L=6, Im m>=0.05: max r=(1-|m|^2)/min_t|1-t m^2| = 0.9964 at E=-59.950, m=-0.0142+0.0579j
      Ward sum_b|M_0b|^2=1.000000008  M_00-m=1.0e-09  offdiag sum |M_0a|^2=0.9964 vs 1-|m|^2=0.9964
`r < 1`, so `ε ≈ |m|² ≳ κ²`: consistent with `ε = ε(d,Λ,κ)`, and `ε → 0` as `κ → 0` (as the report says). Ward and `M_aa = m` hold exactly.
    $ python3 $A/aud_gg.py        # GGGamma, f = 1, d=1 L=3 W=2 (N=6), g0=.5 E=.3 t=.5, x=0 y=y'=2, 4e5 GUE samples
    real-axis m=-0.219728+0.735456j  M_xx-m max=5.2e-13
    LHS=-0.033146+0.003011j (se 3.1e-04)
    RHS printed  (S^+)    =0.036112-0.018021j  |LHS-RHS|=7.24e-02
    RHS corrected(M^+S^+) =-0.033099+0.002804j  |LHS-RHS|=2.12e-04
Independent confirmation of T2161a: the printed B:398 coefficient fails by 230 s.e. The corrected one (used in `BAGGGamma`) agrees within 1 s.e. `S⁺ = S(1−M⁺S)⁻¹` matches `(eq:def-Spm)` 7_8:110 (`S^{(B)}=I`, `S_t=tS`).
For the PT pins, the report's b.6 (P5 = 98, P8 = 104 at g=10) shows that the constant depends on `Λ` (`C ≳ g²` at t=0, as in §9 O1). This is allowed by §18 and is not a counterexample to a pin with `C(d,Λ,κ)`.

## 5. Compiled nonempty instances (all in the probe, all built above)
- Deterministic pins (13.2-13.3, :1988-2087): applied at `L=4`, raw `g=10`, `Λ=10`, flow point `(g₀,E,m₀)` with `g₀ ≤ 10`, `κ = Im m₀ > 0` proved. PT displacements are `a=(2,0,0)`, `r=(1,0,0)` (`|r| ≤ |a|/2`, proved by `decide`), `t=1/2`. The real-axis datum is constructed (subordination `w = 6i/5`, `BASelf_subord`), not assumed.
- Chain pins (13.5) at `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `g_n=(2(n+1))^{-6}`, `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`): `flow_sz0` proves `BAFlow` from the pin `BAmExists`. The window `t₀_n ≥ 1/16` is proved, so the window is not collapsed.
- Endpoints: `inst_cls_Thm27` (:2554) / `inst_cls_Thm27_chain` (:2574) at the class sequences `clsSz L g₀` (constant `L ≥ 3`, `W_n=(2(n+1))^5`, `0<g₀≤10`). `Admissible (1/6) (1/10)` is proved (`clsSz_admissible`). Bulk membership of `E_*` is proved (`cls_bulk`) and `𝐃^{BA}` is nonempty at every `n` (`cls_domain`). Applied at gaps (`L=4`, g=10), odd (`L=5`, g=1/5), interval (`L=4`, g=3/10): `inst_cls_gaps/odd/interval`. The remaining hypotheses are pins: `BAThm27 3`, `BAmUniqReal 3`, and for the chain version the other pins and glue pins.
- Nondegenerate: `N → ∞`, nonempty index sets, `κ > 0`, no `False` premise, and no witness that works only because a quantity is astronomically large.

## 6. Paper-delta coverage
| Lean/paper difference | candidate |
|---|---|
| bulk `ρ_N ≥ κ` instead of `|E| ≤ e_λ−κ`; `Im m ≳ 1` as hypothesis | T2161b (needs Jun) |
| `GGGamma` coefficient `(M⁺S⁺)_{xβ}` | T2161a (confirmed §4) |
| `B_{t,K}`, `ℓ_t` use model `g_n`, not `g₀=√t₀ g` | T2161c |
| `zztE_BA` without `|Re z| ≤ 2−κ` | T2001g (signed, §10) |
| universality density-normalised | DECISIONS §11 (Jun) |
| `lem:propM`/PT constants depend on `Λ` (paper: `C(d,κ)`) | no T2161 entry; covered by §9 O1 ("BA 一侧同理") / T2003a; see O2 |

## 7. Observations (no RETURN)
- O1. `BAlocSCConcl`/`BAqdConcl` measure `|x−y|` with `zdistD` (ℓ¹), but §12 T2002b assigns `zdistInf` to endpoint statements. Since `𝓑_{η,K}` decreases in `K` and `K_∞ ≤ K_1 ≤ dK_∞`, the two differ by at most a constant factor depending only on `d`, absorbed by `W^τ`. Align at the MA freeze.
- O2. The `Λ`-dependence of the constants of `BAPropM`, `BAoffDiag` and `BAProp5..8` (the paper says `(d,κ)`) is stated in narrative item 8 but not as a `T2161x` candidate. The dispatcher may want it recorded explicitly (it is authorised by §9 O1/§18).
- O3. The sequence-level classification (which class each instance belongs to) is numerical, not compiled (narrative item 7). The auditor reproduced it (§2). The cusp class has only `FlowPt`/`BASelf` instances. That is consistent, because the ρ-form excludes cusp points.
- O4. `inst_BAThm27` at `sz0` keeps `hbulk` as an undischarged deterministic premise. The class-sequence instances discharge it, so endpoint coverage is complete.
- O5. `BAmUniqReal` (deterministic, owed to BA-D2) is a hypothesis of the endpoint instances. It is a pin of another ticket, so this is allowed.

## Verdict per target
| target | verdict |
|---|---|
| 1 inventory (b.8, portmap) | PASS |
| 2 pins (deterministic, PT-BA, chain, K, graph layer, endpoints) | PASS (bulk form: dispatcher sign-off / Jun) |
| 3 external citations (b.9, 12 rows with routes and lines) | PASS |
| 4 constant table (b.4, b.6) | PASS |
| 5 compiled skeleton `BAThm27_skeleton_chain` | PASS |
| 6 split table, count 57 > 50 (top notice) | PASS (needs Jun via the dispatcher before any BA proof ticket) |
| 7 instances (§5) | PASS |
Overall: **PASS — needs dispatcher sign-off** (bulk-form change to Thm 2.7; BA count over 50).
