Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 04:44 UTC 2026

**Verdict.** Target 1 (S2, S3), 2 (`baExp14b_expand_holds`), 3, 4, 5, 6: the identity closes (MC below) and S2 has a route per family; **BLOCKED on one missing input: the root of S3** ((i) S3 rows, (iii)). Targets 2-4 do not use that root; the dispatcher may release with it recorded as owed to L4c1/L4e-C/L4g.
Notation: `𝔟 = Bctl = W^{-d}B_{t,0}`; `X_c = tr(ǦE_c)`; `f = X_{[α]}·tail`, `tail = G(σo)_{yx}`; `x∈[ao]`, `y∈[ac]` (`BAExp14a_outer`, `BAExp14aB.lean:70`); target per family `(1-t)⁻¹𝔟^{5/2}`.
`∂_{δγ}X_{[α]} = -W^{-d}Σ_{v∈[α]}G_{vδ}G_{γv}`; `∂_{δγ}tail = -G_{yδ}G_{γx}` (σo=+), `-conj(G_{xγ}G_{δy})` (σo=-) (`BAExpand_dh_of_partial`, `_star_of_partial`, `BAExpand.lean:193, 217`).

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| target | `(1-t)⁻¹𝔟^{5/2}`, `n≥n₀` | `η⁻¹ ≤ κ⁻¹(1-t)⁻¹` (`BAExp14a_eta_inv_le :1271`), constant `κ⁻¹` | none |
| P1 `STLocalEntrygL` | `|Ǧ_{xy}| ≺ 𝔟^{1/2}` | crude `|T̃| ≤ max|Ǧ|` | `T̃` needs 1/2 in D1t/D2t: 0 |
| P2 `LWAvgLawgL` | `|X_c| ≺ 𝔟` | | |
| P3 (not in the seven) | `|𝔼X_c| ≺ 𝔟^{3/2}` | needed by D1t, D2t, T2a/b (`𝔼X·K` with `K ≲ 𝔟`); in L4a only via private `BAExp14a_q_prec :1377` (+ public `_e_bound :978`, `_EGxx :881`) | 0; L4b2 re-derives it |
| P4 `STLmaxgL`, `STLKgL` | `|L^{(2)}| ≺ 𝔟`, `|L^{(2)}-K^{(2)}| ≺ 𝔟²` | D1t: `X·L^{(2)}·T̃` = 1+1+1/2 | 0 |
| TL1 `BATwistAvgLaw` | `|T̃| ≺ 𝔟` | T3B (`X·T̃·η⁻¹𝔟^{1/2}` = 1+1+1/2), T3C-Ḡ | 0 (fable §4: "no slack") |
| TL2 `BATwistLoopLaw` | `|L̃-K̃| ≺ 𝔟^{3/2}` | D2t, T2a/b: `X·(L̃-K̃)` = 1+3/2 | 0 (proofs give `2-δ`) |
| `twK_bound` (`TwistPins.lean:122`) | `|K̃| ≤ C𝔟`, `Σ_a|K̃| ≤ C(W^dη)⁻¹`, eventual | D2t, T2, T3C-Ḡ | |
| `M^{(B)}` `ℓ¹`, `𝒦̃` | row/column sums `≤ C` (`BAMB_row_l1`) | all block forms | |
| `W^{-d}` vs `𝔟` | `W^{-d} ≤ (g²+1)𝔟` (design §3.2, `ba_xy_count`) | `twCirc` correction in T2 | C1: constants in `(d,κ,𝔡)` |
| `W-1` | `= M⁺SW` (D402; `BAExp14a_W_sub_one`, `BAExp14a.lean:1116`) | MC asserts it | |
| `t` | `0 ≤ t ≤ BAflowT0 < 1` (`BAExp14a_t_lt_one :1267`) | GGGamma/lanlw need `0≤t<1`; `t=0` all families vanish | |
| stop line | 2,000 per file | see (viii) | |

**Family table** (cut at `σc=+`; 18 families; `σc=-` by conjugation, (iv)). `W^{(0)}=1`, `W^{(1)}=W-1`, `Σ_{α∈[a₁]}W^{(1)}_{αw}=𝒦̃_{a₁[w]}`.
| id | expression (outer frame `W^{-2d}Σ_{x,y}Σ_α`) | S | owner | premises, route |
|---|---|---|---|---|
| MM, T1, T3A_{0,1}, C1, C2 | `M_{xα}M_{αy}f`, `Σ_β(W-1)_{αβ}M_{xβ}M_{βy}f`, `ΣW^{(k)}_{αw}M_{wγ}tX_{[γ]}G_{γy}Ǧ_{xw}f`, `lanlw` children `Σ_βS_{α'β}Ǧ_{ββ}` on MǦ (C1), ǦM (C2) | S1 | merged `baExp14a_S1_holds :1692` | P1, P2 |
| D1t | `-M_{xα}M_{αα'}S_{α'β}G_{βy}X_{[α]}∂_{βα'}tail` (lanlw on MǦ) | S2 | L4b2 | block form `tΣ_{a₁,c}M^B_{aa₁}M^B_{a₁c}X_{a₁}L^{(2)}_{(c,b)}·\bar{Tr(GP_{ca})}`; P1-P4; 5/2 |
| D2t | `-M_{xα'}S_{α'β}G_{βα}M_{αy}X_{[α]}∂_{βα'}tail` (lanlw on ǦM) | S2 | L4b2 | `tΣM^B_{ac}M^B_{a₁b}X_{a₁}\bar{T̃(G)}·L̃_{(c;a₁,b)}`; P3, TL2, `twK_bound`; 5/2 |
| T2a, T2b | `Σ_β(W-1)_{αβ}Ǧ_{βy}M_{xβ}f`, `…M_{βy}Ǧ_{xβ}f` | S2 | L4b2 | `Σ𝒦̃_{a₁c}M^B_{ac}X_{a₁}L̃^∘`; TL2 (+TL1 for `twCirc`), P3; 5/2 |
| T3B_k | `ΣW^{(k)}_{αw}M_{wγ}S_{γδ}Ǧ_{γw}G_{δy}G_{xδ}f` | S2 | L4b2 | `tΣκ_kM^B X_{a₁}T̃·[W^{-2d}Σ_{x,y,δ∈c₂}tail·G_{δy}G_{xδ}]`; TL1+Ward; `η⁻¹𝔟^{5/2}` (fable §4) |
| T3C-Ḡ_k | `-ΣW^{(k)}_{αw}M_{wγ}S_{γδ}G_{δy}Ǧ_{xw}X_{[α]}∂_{δγ}tail` | S2 | L4b2 | TL1+TL2+Ward (fable §3.1-3.3, σo=-); `η⁻¹𝔟^{5/2}` |
| D1X, D2X | `-M_{xα}M_{αα'}S_{α'β}G_{βy}(∂_{βα'}X_{[α]})tail`; `-M_{xα'}S_{α'β}G_{βα}M_{αy}(∂_{βα'}X_{[α]})tail` | S3 | L4g/L4c1 | graph, root missing (iii) |
| T3C-tr_k | `-ΣW^{(k)}_{αw}M_{wγ}S_{γδ}G_{δy}Ǧ_{xw}(∂_{δγ}X_{[α]})tail` | S3 | L4g/L4c1 | graph, root missing (iii) |
**Partition (flag).** S1 keeps C1, C2 (forced: they are two of the merged six). So MǦ, ǦM are not S2 families: `MǦ = C1 + D1t + D1X`, `ǦM = C2 + D2t + D2X` (`BAlanlwR`, `BAExpand.lean:106`), and `ǦǦ = T1+T2+ΣT3A+ΣT3B+ΣT3C` (`BAGGGammaR`, `BAGGExp.lean:67`, at `(x,y,y')=(α,y,x)`, `P` for `f`). Unused: fable §4 rows MG̊, G̊M (TL2 on the parents); replaced by D1t, D2t (block forms derived here by hand; the identity is checked by MC below). D1t needs no TL; D2t, T2 need TL2; T3B, T3C-Ḡ need TL1 (T3C-Ḡ also TL2). T2/T3B/T3C-Ḡ routes are taken from fable §3-§4, not re-derived; σo=+ for T3B, T3C-Ḡ is not verified (paper B:7 "analogous").

### (iii) S3 against L4d's root: it is **not** a combination of `(baG5Graph k s).val`
`$ python3 scratch/T2434/s3root.py` (the S3 vertex data are my hand derivation of (i); only the first line is read from the file)
```
baG5Graph (BAExpandId.lean:75-83): BAGraph (Fin 2) (Fin 3) | mdot := []: True
T3C-tr_0 : internal 4 ['w','g','v','d'], M-dotted 1  -> is a baG5Graph (3 internal, 0 M-dotted)? False
T3C-tr_1 : internal 6 [...,'a','b'], M-dotted 3  -> ... False   (W-1 = M⁺S⁺ adds a, b)
D1X      : internal 4 ['a','p','v','s'], M-dotted 2           -> ... False
D2X      : internal 4 ['p','v','s','a'], M-dotted 2           -> ... False
```
Reason: `α` of the band `𝒢` splits into `(w,γ)` joined by `M_{wγ}` (`Ǧ_{xw}` at `w`, `S_{γδ}` and `∂X` at `γ`); the `v∈[α]` tie is `W^{(k)}` (k=0: `t`-free block identity `= S_{vw}/t`, not `BAlwS`; k=1: `(W-1)=M⁺S⁺`). Missing: roots `baT3CtrGraph k`, `baD1XGraph`, `baD2XGraph` (`BAGraph (Fin 2) (Fin 4/6)`, `mdot ≠ []`) with their identity (L4d), closure `ord ≥ 5-2·1[x~y]` (L4e-C; the M edges change the counters) and leaf bound (L4c1). Generic `baExpFrame_gg` (`BAGGOp.lean:788`) and `BAGraph` with `mdot` exist.

### (iv) Statements (mathematics; compiled by the probe step)
- `BAExp14bS2Fam sz z n t ω (j : Fin 8) σc σo ac ao := if σc then F₂ j σo ao ac else star (F₂ j (!σo) ac ao)` with `F₂` the outer frame of the 8 S2 rows (`D1t,D2t,T2a,T2b,T3B_0,T3B_1,T3C-Ḡ_0,T3C-Ḡ_1`); `BAExp14bS3Fam` likewise over `Fin 4` (`D1X,D2X,T3C-tr_0,T3C-tr_1`), tail derivative as in the notation line.
- `BAExp14bS2 d := T2434_FamShape d (Fin 8) BAExp14bS2Fam (STLocalEntrygL ∧ LWAvgLawgL ∧ STLmaxgL ∧ STLKgL ∧ STDecaygL ∧ BATwistAvgLaw ∧ BATwistLoopLaw)` (all seven; `BATwist*` imported from `TwistPins.lean:91, 95`). `BAExp14bS3 d := T2434_FamShape d (Fin 4) BAExp14bS3Fam (the five of `LWCutExpG`: STLocalEntrygL, LWAvgLawgL, STLmaxgL, STLKgL, STDecaygL)`.
- `BAExp14bExpand d := T2434_ExpandShape d (Fin 8) (Fin 4) BAExp14bS2Fam BAExp14bS3Fam`; conjugation `T2434_CutConj` (`LWcutg false σo ac ao = star (LWcutg true (!σo) ao ac)`: from `Gres false = G^*`, `Eblk` real, `C.S = 1`, `star (m)` for `σc=false`; checked by hand on `Tr(G^*E_aG^*E_{ac}G(σo)E_{ao})`).
- Proof plan of the identity: `LWcutg(true) = W^{-2d}Σ_{x,y}tail Σ_αX_{[α]}(Ǧ+M)_{xα}(Ǧ+M)_{αy}` (`BAExp14a_L1_eq :172`, `_X_eq :188`, `Eblk` of `trace_Eblk :148`); `ǦǦ` by `baGGGamma_holds`, `MǦ`, `ǦM` by `baLanlw_holds` (both on `PF d L W 0`, transported by `BAExp14a_int_slice :702`); integrability by continuity + bound (`BAExp14a_integrable :838`); `Leibniz` for `∂f`.

### (v) Consumers
L4b2: S2 + block forms of file A (`twTie`, `W-1` block, the 8 block forms); L4g/L4c1: S3 (graph form, fine sums); L4a2: `baExp14b_expand_holds`, S1-S3, `BAExp14a_prec_fin :217` (finite union of `PrecL`).

### (vi) Band → BA (`LWExpTerm2`)
§1 `:67-147` pins → S2/S3 + `Fam` (A; no `K`, `ω` inside, `S^{(B)}=I`) | §2 `:149-574` block algebra → `twTie` (probe 226), block forms, ties by `BAMfine_eq` (A) | §3-§5 `:576-714` traces, `Lloop` bridge → merged `BAExp14a_trace_Eblk :148`, `_L1_eq :172`; new: 3-loop only (A, ~60); `L2/L4/L5` not twinned (S3 is a graph) | §6 `:716-921` `(Oe2x)`, tameness → `BAGGGamma`/`lanlw` at the carrier with `f=X·tail` (B) | §7 `:923-1017`, §8 `:1020-1086` integrals, assembly algebra → (B)/(A) | §11-§12 `:1220-1637` → `baExp14b_cut_expand`, `_cut_conj` (B). Not twinned: §9 BM integrability (continuity+bound), §10 `K⁺` split (`W-1=M⁺SW`), §13 kernel facts (L4a re-proved `ω`), §14 `t=0` bound, §15 assembly (L4a2), §16 instances (own).

### (viii) Size (estimate; ratio 1.5-2.1 on the band basis, not a count)
File A ≈ 1,300-1,700 (pins/Fam ≈ 250, ties ≈ 120, 8 block forms ≈ 700-900); file B ≈ 1,300-1,800, of which §§11-12 (418 band lines) ≈ 650-850 (18 families vs 5). Both below 2,000; B is the one at risk.

### (ii) Concrete instance (`d=3`, `sz0` n=0, `zSeq`, `flow_sz0`, `t=1/2`; data `Defs/Sizes.lean:260`, `BA/FlowPins.lean:1214-1254`)
`$ python3 scratch/T2434/inst.py`
```
d,L,W,N = 3 4 32 2097152 | lam = 1/64 | W^d = 32768 | L^d blocks = 64
3<=d: True | kappa,eps,dd>0: True True True | t=1/2 <= t0 lower bound 2/3 : True
kappa <= Im m (4/5): True | N^(-1+eps)= 2.0442456484533175e-06 <= 1/4: True
U_n nonempty: lam^2/L^d = 3.814697265625e-06 <= 1-t = 0.5 : True
Bparam = 2.0302739141044412 | Bctl = W^-d B = 6.195904278883183e-05 | bound (1-t)^-1 Bctl^(5/2) = 6.043544786717419e-11
families: S1 6 + S2 8 + S3 4 = 18; index sets: |Fin 8| x 4 charges x 64 x 64 labels = 131072 (S2), 65536 (S3)
 n=1: lam^2/L^d=1.16e-10 <=1/2: True ; Bctl=1.866e-09 ; (1-t)^-1 Bctl^(5/2)=3.009e-22
 n=5: lam^2/L^d=8.11e-18 <=1/2: True ; Bctl=1.298e-16 ; (1-t)^-1 Bctl^(5/2)=3.840e-40
```
Deterministic hypotheses hold at these numbers; `STLocalEntrygL, LWAvgLawgL, STLmaxgL, STLKgL, STDecaygL, BATwistAvgLaw, BATwistLoopLaw` stay hypotheses of the example (other gates' pins).
**External hypotheses TL1, TL2, limit check** at the base time `t=0` (`G=M`, `Ǧ=0`; generic `M^{(B)}`, `L=3`, `W^d=4`, all `σ`, `(a,c₁,c₂)`; `twL2'`, `twK`, `twTr` as `TwistPins.lean:55-82`): `$ python3 scratch/T2434/tl_base.py`
```
TL2 at t=0 (L~ = K~ exactly, G=M): max |twL2'-twK| over all sigma,(a,c1,c2) = 1.1102230246251565e-16
TL1 at t=0 (G-circ = 0): max |twTr| = 0.0
```
**Identity closes (Monte Carlo of the 18-family decomposition, independent of Lean).** `d=1, L=3, W^d=2`, GUE blocks (`E|V_ij|²=1/W^d`), `g₀=0.7, E=0.3, t=0.6`, `m` solved from `m = N⁻¹Tr M` (asserted, with `W-1 = M⁺SW`); 2.4·10⁶ samples (4 seeds × 30 × 20,000); `∂` as in the notation line; `f=X·tail`.
`$ python3 scratch/T2434/mc_cut.py <seed 11-14> 30; python3 scratch/T2434/agg.py`
```
sigma_o=+ ao=0 ac=0: E[cut]=0.0303-0.0151j  sum of 18 families=0.0309-0.0148j  |diff|=6.7e-04  s.e.=1.9e-03
sigma_o=+ ao=0 ac=1: E[cut]=0.0207-0.0202j  sum of 18 families=0.0214-0.0185j  |diff|=1.9e-03  s.e.=1.0e-03
sigma_o=- ao=0 ac=0: E[cut]=-0.1879+0.0307j  sum of 18 families=-0.1884+0.0284j  |diff|=2.4e-03  s.e.=1.2e-03
sigma_o=- ao=0 ac=1: E[cut]=-0.1170+0.0213j  sum of 18 families=-0.1166+0.0215j  |diff|=4.3e-04  s.e.=6.5e-04
```
(Individual families reach `0.19` in absolute value; `s.e.` is that of the per-sample difference `E[cut] - Σ families`.)

### Verdicts
- Target 1 (S2, S3 pins): **S2 PASS** (8 families, routes above; P3 is a missing premise of the seven, L4b2 re-derives it); **S3 BLOCKED** (root, (iii)).
- Target 2 (`baExp14b_expand_holds`): **PASS** (the 18-family identity closes both charges; conjugation as in (iv)).
- Targets 3, 4, 5, 6: **PASS** (instances above; no smallness of `g` or `M-m₀I`; no registry line).
- Overall: **BLOCKED** (S3's root: REQ for L4c1/L4e-C/L4g, or a dispatcher decision to release 1b without it).

## (a′) Preflight corrections — Mon Oct 12 09:22 UTC 2026 (`date -u`)
One correction to (a)(i), no verdict changes: the row `T2a, T2b` gives one kernel `M^B_{ac}` for both. Proved below: `T2a` has `M^{(B)}_{ac}` with the loop `Tr(Ǧ E_b G^σ P_{ac})` (circled leg in slot 1 of `twLoopX`); `T2b` has `M^{(B)}_{cb}` with `Tr(G^σ E_a Ǧ P_{cb})` (slot 2, the slot of `twCirc`; likewise `T3C-Ḡ`).

## (a″) Probe compile — Mon Oct 12 06:00:03 UTC 2026 (`date -u`)

Role `prover-max` (claude-sonnet-5-5), probe step under Amend 1 item 1 (`docs/tickets/T2434-amend-1.md`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2434`, branch `t/T2434`; one new file `RBM3D/Probe/T2434Pins.lean` (267 lines, never merged, no root import); commits `7a6515a` (the probe) and `024dc54` (`#check` lines in signature form, output only), the only commits beyond the base `e3f59c2`. Section (a) is not edited; there is no (a′). Scratch (not in the repository): scratchpad `T2434/` (`lean_vs_cut*.py`, `equiv2.lean`, `names.sh`, `final_block2.sh`).
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2434 && lake env lean RBM3D/Probe/T2434Pins.lean     # 05:58:12 .. 05:58:19 UTC, HEAD 024dc54, tracked changes 0
RBM.BA.BAExp14b_dtail {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool)
  (x y δ γ : Idx d (sz.L n) (sz.W n)) : ℂ
RBM.BA.BAExp14b_dX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (α δ γ : Idx d (sz.L n) (sz.W n)) :
  ℂ
RBM.BA.BAExp14b_outerDt {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n))
  (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ
RBM.BA.BAExp14b_outerDX {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool)
  (a b : Zd d (sz.L n)) (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ
RBM.BA.BAExp14b_FS2 {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (j : Fin 8) (σ : Bool)
  (a b : Zd d (sz.L n)) : ℂ
RBM.BA.BAExp14b_FS3 {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (j : Fin 4) (σ : Bool)
  (a b : Zd d (sz.L n)) : ℂ
RBM.BA.BAExp14bS2Fam {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (j : Fin 8) (σc σo : Bool)
  (ac ao : Zd d (sz.L n)) : ℂ
RBM.BA.BAExp14bS3Fam {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (j : Fin 4) (σc σo : Bool)
  (ac ao : Zd d (sz.L n)) : ℂ
RBM.BA.BAExp14bS2 (d : ℕ) : Prop
RBM.BA.BAExp14bS3 (d : ℕ) : Prop
RBM.BA.BAExp14bExpand (d : ℕ) : Prop
RBM.BA.BAExp14bCutConj {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Prop
6 of 6 lines of #print axioms (BAExp14bS2Fam, S3Fam, S2, S3, Expand, CutConj): [propext, Classical.choice, Quot.sound]
EXIT=0     # 26 output lines, of which with 'error' or 'warning': 0
$ cd /Users/junyin/Lean_proof/RBM3D && lake env lean /Users/junyin/Lean_proof/RBM3D-wt/T2434/RBM3D/Probe/T2434Pins.lean     # main = d11da04, 05:58:19 .. 05:58:24 UTC
EXIT=0     # 26 output lines, diff against the run above: empty
$ git diff --name-status e3f59c2 main -- RBM3D RBM3D.lean     # base of t/T2434 against main; no other file of RBM3D/ differs
M RBM3D.lean;A RBM3D/BA/TwistGridTail.lean;A RBM3D/BA/TwistGridTail2.lean;A RBM3D/BA/TwistGridWTail.lean;A RBM3D/BA/TwistGridWTail2.lean;A RBM3D/Graph/BALvl1A.lean;M RBM3D/Test/Axioms.lean;
$ wc -l RBM3D/Probe/T2434Pins.lean; grep -c -i 'sorry\|admit\|native_decide'; grep -c '^axiom '; git diff --stat main...t/T2434
267 lines; hits sorry|admit|native_decide: 0; hits '^axiom ': 0; 1 file changed, 267 insertions(+)
```
Name clash (`names.sh`, stem `BAExp14b` case-insensitive; 23 names = the 21 public declarations of the probe + `baExp14b_expand_holds`, `baExp14b_cut_conj`): main `d11da04`: 0 hits in `RBM3D/*.lean` + `RBM3D.lean` (the 23 names with `-w`: 0); 442 ref tips (heads+remotes): 0 hits outside `Probe/`; inside `Probe/`: only `refs/heads/t/T2434:RBM3D/Probe/T2434Pins.lean`; `.lake/packages`: 0.
Examples (all compile): `:214` S2 at `d = 3`, `sz0` (`n = 0`), `zSeq`, `flow_sz0`, `t ≡ 1/2`, the seven premises as hypotheses; `:222` S3 (five premises); `:229` the identity at the same data, `n = 0`, `t = 1/2`, `ac = 0`, `ao = e₀`, `σc σo` free, no premise; `:234` the conjugation; `:239` both index sets nonempty at every `n` (`λ_n²/L_n³ ≤ 1/2`); `:257` `0 ≠ e₀` in `Zd 3 (sz0.L 0)`.
Binding to the check file (scratch `equiv2.lean` = probe lines 1-206 + section 2 of `T2434-check.lean` verbatim + 4 examples; `lake env lean` EXIT 0): `BAExp14bExpand d = T2434_ExpandShape d (Fin 8) (Fin 4) BAExp14bS2Fam BAExp14bS3Fam` and `BAExp14bCutConj sz z = T2434_CutConj sz z` by `rfl`; `BAExp14bS2 d ↔ T2434_FamShape d (Fin 8) BAExp14bS2Fam T2434_Prem7` and `BAExp14bS3 d ↔ T2434_FamShape d (Fin 4) BAExp14bS3Fam (the five premises)` by (un)currying.
Evidence that the 18 families as typed are the cut. `lean_vs_cut*.py` transcribes S1 from `Graph/BAExp14aB.lean:57-114` and S2, S3 from the probe (not from the preflight's einsum) and computes the cut from its definition (`LWcutg` `Chain/LWGen.lean:39`, `loopM = Tr(Π_i G(σ_i)E_{a_i})` `Loop/GLoopFlow.lean:92`, `Eblk` `Loop/GLoop.lean:55`, `C.S = 1`), so `x ∈ [ao]`, `y ∈ [ac]`, closing edge `G(σo)_{yx}`; the red charge is the cut with `G^*` against the red families (conjugate, swapped blocks, flipped tail). Model: `H = g₀Ψ + √t V` (`BAlwH`), `Ψ` the cycle on `L` blocks, `m = N⁻¹ Tr M` with `M_{ββ} = m` asserted, `z_t = E + (1-t)m` (`ztOf`, `Loop/GLoopFlow.lean:55`). Last line of each run (`W^d = 1`: all four charge pairs and all `(ac, ao)`; `W^d = 2`: six labellings):
```
$ python3 lean_vs_cut.py 3 40 0.7 0.0 0.2           L=3 (g0,E,t)=(0.7,0.0,0.2) nodes/var=40 total nodes=64000  max |E[cut] - sum of 18 families| = 6.022e-07   largest single family |E F| = 0.067
$ python3 lean_vs_cut_b.py 3 56 0.7 0.0 0.2         L=3 (g0,E,t)=(0.7,0.0,0.2) nodes/var=56 total nodes=175616  max |E[cut] - sum of 18 families| = 1.500e-08   largest single family |E F| = 0.067
$ python3 lean_vs_cut_b.py 4 16 0.7 0.3 0.1         L=4 (g0,E,t)=(0.7,0.3,0.1) nodes/var=16 total nodes=65536  max |E[cut] - sum of 18 families| = 5.478e-08   largest single family |E F| = 0.037
$ python3 lean_vs_cut_qmc.py 3 2 14 0.7 0.3 0.1 1   L=3 Wd=2 (g0,E,t)=(0.7,0.3,0.1) Sobol 2^14=16384 seed=1    max |E[cut] - sum of 18 families| = 4.170e-05   largest single family |E F| = 0.003
$ python3 lean_vs_cut_qmc.py 3 2 18 0.7 0.3 0.1 1   L=3 Wd=2 (g0,E,t)=(0.7,0.3,0.1) Sobol 2^18=262144 seed=1   max |E[cut] - sum of 18 families| = 7.282e-06   largest single family |E F| = 0.003
$ python3 lean_vs_cut_qmc.py 3 2 18 0.7 0.3 0.1 2   (same, seed=2)                                              max |E[cut] - sum of 18 families| = 6.457e-06   largest single family |E F| = 0.003
```
The `W^d = 1` runs are Gauss-Hermite quadratures (the error falls from 6.0e-07 at 40 nodes to 1.5e-08 at 56) but blind to the factors `W^{-d}`; the `W^d = 2` runs (GUE blocks, `E|V_{ij}|² = 1/W^d`) have `|diff|/|E cut| ≤ 6.1e-3` at `2^14` and `≤ 1.1e-3` at `2^18` (both seeds) over the six labellings.

Notes.
1. **Result.** The probe compiles, EXIT 0, against the worktree build (base `e3f59c2`) and against main's environment (`d11da04`). The files of `RBM3D/` that differ from the base are new files, `RBM3D.lean` and `Test/Axioms.lean`, and no module outside `Test/` imports `RBM3D` or `RBM3D.Test.*` (grep: 0), so the closure of the probe's imports is the base's. No stop-rule trigger: the identity closes in expectation at the printed accuracy, both charges; both `lanlw` children are the merged standard form (`BAlanlwR` at `(α, y)` for `MǦ`, at `(x, α)` for `ǦM`; `baLanlw_holds` is for all `x y`, no transposed form); `GGGamma` is `BAGGGammaR` at `(x, y, y') := (α, y, x)`.
2. **Not proved here.** S2, S3, the identity and the conjugation are `Prop`-valued pins; the examples apply them as hypotheses `h` at the data; the premises of S2, S3 (other gates' pins) stay hypotheses. S3 is the four families as fine sums (Amend 1 item 1) and does not use the roots of (iii).
3. **Fixed by the probe** (lines 39-184, to be copied verbatim into `Graph/BAExp14b.lean`; helpers carry the stem `BAExp14b_`): `BAExp14b_dtail σ x y δ γ` (`∂_{h_{δγ}}` of the closing edge) and `BAExp14b_dX α δ γ` (`∂_{h_{δγ}}X_{[α]}`); the frames `BAExp14b_outerDt` (tail differentiated: `W^{-2d}Σ_{x,y}Σ_α X_{[α]}T`) and `BAExp14b_outerDX` (`X` differentiated: `W^{-2d}Σ_{x,y}G(σ)_{yx}Σ_α T`); the merged `BAExp14a_outer`, `BAExp14a_X`, `BAExp14a_Wk` serve `T2a`, `T2b`, `T3B`; families `BAExp14b_FD1t, FD2t, FT2a, FT2b, FT3B k, FT3CG k` dispatched by `BAExp14b_FS2 : Fin 8` in the order `D1t, D2t, T2a, T2b, T3B_0, T3B_1, T3C-Ḡ_0, T3C-Ḡ_1`, and `FD1X, FD2X, FT3CX k` by `BAExp14b_FS3 : Fin 4` in the order `D1X, D2X, T3C-tr_0, T3C-tr_1`; the integrands `BAExp14bS2Fam`, `BAExp14bS3Fam` in the `σc` convention of `BAExp14aS1Fam`; the pins `BAExp14bS2` (seven premises, curried as `BALWCutExpTw`), `BAExp14bS3` (five), `BAExp14bExpand`, `BAExp14bCutConj`. The block-form lemmas of target 3 are not pinned by the probe.
4. **Paper-delta candidates:** none new at this step.


## (b) Script output — Mon Oct 12 09:22 UTC 2026 (`date -u`)
Role `prover-max` (claude-sonnet-5-5), stage 1b rerun under Amend 1 (H229). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2434`, branch `t/T2434`. At 08:11:36 UTC (`date -u`) HEAD was `203b485` with one uncommitted change in `Graph/BAExp14b.lean` (27 lines, `loop2`). Commits of this run: `1ac6995`, `2a26066`, `6cccbdd` (HEAD). Sole files: `BAExp14b.lean`, `BAExp14bB.lean` (the probe is unchanged since `024dc54`). Scratch: scratchpad `T2434/` (`blkA.lean`, `blockcheck.py`, `final_verify.sh`, `extract_final.py`, `s3roots2.py`, `names2.sh`).
```
$ wc -l RBM3D/Graph/BAExp14b.lean RBM3D/Graph/BAExp14bB.lean           # stop line 2,000 per file; (a)(viii) priced 1,300-1,700 / 1,300-1,800
   998 BAExp14b.lean   1076 BAExp14bB.lean   (2074 total; both below the stop line)
$ python3 extract_final.py <names>     # statements extracted from the files; line numbers first
BAExp14b.lean:170  def BAExp14bS2 (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0) STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t → STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t → PrecL sz μ (U := fun n => {_p : Fin 8 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n}) (fun n p _ => ‖∫ ω, BAExp14bS2Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
BAExp14b.lean:181  def BAExp14bS3 (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0) STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t → STDecaygL (baFMz sz z) μ t → PrecL sz μ (U := fun n => {_p : Fin 4 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n}) (fun n p _ => ‖∫ ω, BAExp14bS3Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
BAExp14b.lean:192  def BAExp14bExpand (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (σc σo : Bool) (ac ao : Zd d (sz.L n)), ∫ ω, LWcutg (baFMz sz z) n t σc σo ac ao ω ∂(Sizes.seqP (sz.withLam 0)) = (∑ k : Fin 6, ∫ ω, BAExp14aS1Fam sz z n t ω k σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))) + (∑ j : Fin 8, ∫ ω, BAExp14bS2Fam sz z n t ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))) + (∑ j : Fin 4, ∫ ω, BAExp14bS3Fam sz z n t ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0)))
BAExp14b.lean:202  def BAExp14bCutConj {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Prop := ∀ (n : ℕ) (t : ℝ) (σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ), LWcutg (baFMz sz z) n t false σo ac ao ω = star (LWcutg (baFMz sz z) n t true (!σo) ao ac ω)
BAExp14bB.lean:1035  theorem baExp14b_expand_holds (d : ℕ) : BAExp14bExpand d
BAExp14bB.lean:210  theorem baExp14b_cut_conj (sz : Sizes d) (z : ℕ → ℂ) : BAExp14bCutConj sz z
(`hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n)` is abbreviated `hr : BAReal ..` in the eight lines that follow: the six block forms, the dispatcher on `j : Fin 8`, `Wk_blk`)
BAExp14b.lean:673  theorem BAExp14b_FD1t_block (hr : BAReal ..) (σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FD1t sz z n t ω σ a b = (t : ℂ) * ∑ a₁, ∑ c, BAExp14b_MB sz z n a a₁ * BAExp14b_MB sz z n a₁ c * BAExp14a_X sz z n t ω a₁ * twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c * (baFMz sz z).L n t ![true, σ] ![b, c] ω
BAExp14b.lean:695  theorem BAExp14b_FD2t_block (hr : BAReal ..) (σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FD2t sz z n t ω σ a b = (t : ℂ) * ∑ a₁, ∑ c, BAExp14b_MB sz z n a c * BAExp14b_MB sz z n a₁ b * BAExp14a_X sz z n t ω a₁ * twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c * twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) c a₁ b
BAExp14b.lean:717  theorem BAExp14b_FT2a_block (hr : BAReal ..) (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FT2a sz z n t ω σ a b = ∑ a₁, ∑ c, (BAExp14b_om sz z n t - 1) a₁ c * BAExp14b_MB sz z n a c * BAExp14a_X sz z n t ω a₁ * twLoopX n ((baFMz sz z).GM n t ω) (twChg ((baFMz sz z).G n t ω) σ) b a c
BAExp14b.lean:739  theorem BAExp14b_FT2b_block (hr : BAReal ..) (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FT2b sz z n t ω σ a b = ∑ a₁, ∑ c, (BAExp14b_om sz z n t - 1) a₁ c * BAExp14b_MB sz z n c b * BAExp14a_X sz z n t ω a₁ * twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c b
BAExp14b.lean:762  theorem BAExp14b_FT3B_block (hr : BAReal ..) (ht0 : 0 ≤ t) (ht1 : t < 1) (k σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FT3B sz z n t ω k σ a b = (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t k a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14a_X sz z n t ω a₁ * twTrP n ((baFMz sz z).GM n t ω) c₁ c₂ * (baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω
BAExp14b.lean:807  theorem BAExp14b_FT3CG_block (hr : BAReal ..) (ht0 : 0 ≤ t) (ht1 : t < 1) (k σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FT3CG sz z n t ω k σ a b = (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t k a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14a_X sz z n t ω a₁ * (baFMz sz z).L n t ![true, σ] ![b, c₂] ω * twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c₁ c₂
BAExp14b.lean:879  theorem BAExp14b_FS2_block (hr : BAReal ..) (ht0 : 0 ≤ t) (ht1 : t < 1) (j : Fin 8) (σ : Bool) (a b : Zd d (sz.L n)) : BAExp14b_FS2 sz z n t ω j σ a b = BAExp14b_BS2 sz z n t ω j σ a b
BAExp14b.lean:598  theorem BAExp14b_Wk_blk (hr : BAReal ..) (ht0 : 0 ≤ t) (ht1 : t < 1) (k : Bool) (a₁ : Zd d (sz.L n)) (w : Idx d (sz.L n) (sz.W n)) : ∑ α ∈ Iblk d (sz.L n) (sz.W n) a₁, BAExp14a_Wk sz z n t k α w = BAExp14b_kap sz z n t k a₁ (split d (sz.L n) (sz.W n) w).1
```
```
$ lake build RBM3D.Graph.BAExp14b RBM3D.Graph.BAExp14bB     # 09:11:54 .. 09:12:46 UTC, files as committed in 6cccbdd
✔ [4007/4008] Built RBM3D.Graph.BAExp14b (31s)
✔ [4008/4008] Built RBM3D.Graph.BAExp14bB (17s)
Build completed successfully (4008 jobs).    # EXIT=0, no warning in the two files; rerun 09:15:19 at HEAD 6cccbdd: same result
$ grep -c -i 'sorry|admit|native_decide'; grep -c '^axiom '            -> 0 and 0 in both files
$ lake env lean axioms_all.lean    # 69 `#print axioms`: every public declaration of the two files (list: scratchpad pubnames.txt)
EXIT=0  #print axioms lines: 69, of which [propext, Classical.choice, Quot.sound]: 69, other lines: 0
'RBM.BA.BAExp14b_FS2_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14bS2Fam_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExp14b_expand_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean precheck.lean      # import RBM3D + both modules + #assert_rbm_axioms (root imports are the hub's: not edited here)
EXIT=0  axiom audit: 12808 theorems, 4042 definitions, 0 axioms in `RBM` ... All within [propext, Classical.choice, Quot.sound]
$ diff <(probe lines 39-185) <(BAExp14b.lean lines 59-205)     # the pins and integrands are the probe's, verbatim
identical
$ lake env lean bind_final.lean    # = T2434-check.lean section 2 + `BAExp14bExpand d = T2434_ExpandShape d (Fin 8) (Fin 4) BAExp14bS2Fam BAExp14bS3Fam := rfl`,
EXIT=0, 0 errors   # `BAExp14bCutConj sz z = T2434_CutConj sz z := rfl`, S2 and S3 `↔ T2434_FamShape ..` (7 and 5 premises)
$ lake env lean docs/tickets/checks/T2434-check.lean        # on the branch
EXIT=0, 0 errors
```
Instances (compiled `example`s; `d = 3`, `sz0` = `n = 0`: `L = 4`, `W = 32`, `λ = 1/64`, `zSeq`, `flow_sz0`, `t = 1/2`, blocks `0 ≠ e₀`; `BAReal` by `BAflow_real`; `ω` arbitrary): `BAExp14bB.lean:1065` `baExp14b_expand_holds 3 le_rfl (1/2) (1/10) (1/10) .. sz0 zSeq flow_sz0 0 (1/2) .. σc σo 0 (Pi.single 0 1)` (every hypothesis discharged, no premise on the law); `:1070` `baExp14b_cut_conj`; `BAExp14b.lean:926` `FS2_block` (all `j`, `σ`), `:931-939` the six block-form lemmas (`k`, `σ` free), `:943` `S2Fam_block`, `:947` `Wk_blk`, `:950` `twTie_ba`; `:954` S2 (`h : BAExp14bS2 3` and the seven premises as hypotheses, other gates' pins), `:962` S3 (five), `:970` both index sets nonempty for every `n`, `:988` `0 ≠ e₀` in `Zd 3 (sz0.L 0)`.
```
$ sed -n 1065,1067p BAExp14bB.lean     # the instance of target 2
example (σc σo : Bool) :=
  baExp14b_expand_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 0 (1 / 2)
    (by norm_num) (half_lt_t0 0).le σc σo 0 (Pi.single 0 1)
$ sed -n 926,929p BAExp14b.lean      # the instance of the block forms (target 3)
example (ω : sz0.SeqΩ) (j : Fin 8) (σ : Bool) :
    BAExp14b_FS2 sz0 zSeq 0 (1 / 2) ω j σ 0 (Pi.single 0 1) = BAExp14b_BS2 sz0 zSeq 0 (1 / 2) ω j σ 0 (Pi.single 0 1) :=
  BAExp14b_FS2_block BAExp14b_hr0 (by norm_num) (by norm_num) j σ 0 (Pi.single 0 1)

```
```
$ names2.sh   # 69 public names, all with the stem BAExp14b/baExp14b
main ff2c7a5: hits of the stem in RBM3D/*.lean + RBM3D.lean: 0; hits of the 69 names (-w): 0
ref tips other than t/T2434: 443; hits of the stem outside RBM3D/Probe/T2434Pins.lean: 0;  .lake/packages: 0 files;  ../RBM1D, ../RBM2D (read-only grep): 0 files
$ diff <(t/T2398 6429bb5 RBM3D/Probe/T2398Pins.lean:226-252 | sed s/twTie/BAExp14b_twTie/) <(BAExp14b.lean:554-580)
identical      # the only port (twTie); no text from RBM1D/RBM2D (not read in this run)
$ python3 s3roots2.py   # the S3 roots of Amend 1 item 3, counted in the three S3 definitions
baD1XGraph     BAExp14b_FD1X:132   body binders [α', β] + frame [α] + dX [v] = 4 internal; M-factors 2; S-factors 1 (+ the weight W^{-d}1[v∈[α]] of dX)
baD2XGraph     BAExp14b_FD2X:138   same data: 4 internal; M-factors 2 (M_{xα'}, M_{αy}); S 1 (+ the dX weight)
baT3CtrGraph k BAExp14b_FT3CX:144  body binders [w, γ, δ] + [α] + [v], Wk-factor 1: k = 0 (Wk = 1, α = w) 4 internal, M 1; k = 1 (W - 1 = M⁺ S W: BAExp14a.lean:1132, M⁺_{xy} = M_{xy}M_{yx}: BAExpand.lean:78) 6 internal, M 3
BAExpandId.lean:83:  mdot := []     # `baG5Graph : BAGraph (Fin 2) (Fin 3)` (:75-83): no M-dotted edge, 3 internal vertices
```
Merge check (main `9eaf866` against the base `e3f59c2`): `git diff --name-status e3f59c2 main -- RBM3D RBM3D.lean` lists 10 `A` (new modules: `BA/TwistGrid*Tail*`, `Graph/BAAuxGraph2*`, `Graph/BALvl1*`, `Graph/BAStepS`) and 2 `M` (`RBM3D.lean`, `RBM3D/Test/Axioms.lean`); `grep -rln '^import RBM3D$\|^import RBM3D\.Test' RBM3D | grep -v '^RBM3D/Test/'` gives 0 files, so the import closure of the two files is the same on main as on the base.
Narrative.
1. At the start `baExp14b_expand_holds` was committed (`e36e274`) but `lake build RBM3D.Graph.BAExp14b` failed on the uncommitted change (08:12:17..08:12:25: `error: BAExp14b.lean:306:11: typeclass instance problem is stuck`). Rewritten (`1ac6995`), both files built (08:16:33-08:16:54, 4008 jobs); `#print axioms baExp14b_expand_holds` and `baExp14b_cut_conj`: standard three.
2. New in part A (§3-§8): the coordinates `(block, offset)` of a fine vertex (`BAExp14b_pt`, `_sum_idx`, `_sum_blk`) and the entries `M`, `S`, `W^{(0)} = 1`, `W^{(1)} = lift(ω - 1)` in them (`_M_pt`, `_S_pt`, `_Wk_pt_*`; `BAExp14a_W_sub_one`); `𝓛^{(2)}, 𝓛^{(3)}` of the carrier, `twTrP`, `twLoopX` as sums over offsets; `twTie` (port); `Wk_blk` (`Σ_{α∈[a₁]} W^{(k)}_{αw} = κ_k(a₁, [w])`); the block forms; the instances.
3. Proof of each block form: unfold the family, coordinates, the ties as Kronecker deltas eliminated by `simp` (`bf_elim`), a permutation of the nested sums (private `BAExp14b_rot4, _rev3, _mf3, _mf4`), `field_simp` for the `W^d` of the free offset sums. `FT3B_block`, `FT3CG_block` need more than 400000 heartbeats (bisect: `maxHeartbeats` 400000 fails, 800000 and 1600000 pass); the limit is 1600000, with the comment the linter asks for.
4. Independent check before the Lean proofs: `blockcheck.py` computes the fine sums of the eight families from their definitions (random complex `G`, `MB`, `κ`; `L = 3`, `W^d = 2`) and the block forms: `max err 1.1234667099445444e-14` over both charges and all `(a, b)` (rerun 09:21 UTC).
5. Not proved here: S2 (L4b2), S3 (L4g, L4c1, successor L4d2). `S2`, `S3`, `BAExp14bExpand`, `BAExp14bCutConj` are `Prop`-valued pins; the examples apply them as hypotheses; `STLocalEntrygL`, .., `BATwistAvgLaw`, `BATwistLoopLaw` stay hypotheses (other gates' pins). `baExp14b_expand_holds` has none of them. C1: the identity and the block forms are exact (no smallness of `g` or `M - m₀I`, no constants).
6. Consumers (v): L4b2 reads `BAExp14b_FS2_block`, `BAExp14bS2Fam_block`, `BAExp14b_BS2`, `_Wk_blk`, `_twTie(_ba)`, `_twLoopX_twL2'`, `_MB`, `_om`, `_kap`; L4g / L4c1 / L4d2 read `BAExp14bS3` and `BAExp14b_FS3`; the L4a2 assembly reads `baExp14b_expand_holds`, `BAExp14aS1`, S2, S3 and `BAExp14a_prec_fin`.
7. (vi): `LWExpTerm2` §§1-8 and §§11-12 are twinned (part A §1, §3-§8; part B §§1-8); §§9-10, 13-16 are not, for the reasons of (a)(vi).
8. Targets of Amend 1 item 2: 1 the pins (in the file, verbatim from the probe); 2 `baExp14b_expand_holds` (proved, both charges); 3 the block-form lemmas (six lemmas, `BAExp14b_FS2_block`, `_Wk_blk`, `_twTie`); 4 the instances (listed above); 5 C1 (exact identities, no constants); 6 registry: none (`#assert_rbm_axioms` pre-check above); item 3: the three S3 roots (above).

## (c) Verified Mathlib names (module, line from `findDeclarationRanges?` through `lake env lean`; all used and compiled; no absent-name check was needed)
`neg_ite` (Algebra.Notation.Defs:139); `Finset.sum_ite_irrel` (Algebra.BigOperators.Group.Finset.Defs:573); `Finset.sum_ite_eq`, `Finset.sum_ite_eq'` (..Group.Finset.Piecewise:140, 149)
`Finset.sum_const`, `Finset.sum_eq_single`, `Finset.sum_filter` (..Group.Finset.Basic:636, 354, 332); `Finset.sum_comm` (..Group.Finset.Sigma:120); `Equiv.sum_comp` (..Group.Finset.Defs:749)
`Finset.mul_sum`, `Finset.sum_mul` (Algebra.BigOperators.Ring.Finset:59, 56); `Fintype.sum_prod_type` (Data.Fintype.BigOperators:272); `Finset.card_univ`, `Fintype.card_fin` (Data.Fintype.Card:103, 496)
`nsmul_eq_mul` (Algebra.Ring.Defs:187); `star_mul'` (Algebra.Star.Basic:165); `Complex.star_def` (Basic.Complex.Basic:499); `Equiv.apply_symm_apply` (Logic.Equiv.Defs:249)

## (d) Open issues and paper-delta candidates
1. Paper deltas: none new (`T2434a`: none); the decomposition (D402 `W - 1 = M⁺S⁺`, `lanlw` children by the product rule) is the one the 1a-audit found already covered (D402; T2418).
2. For L4b2: `T2a` has the circle in slot 1 of `twLoopX`; the merged `twCirc_holds` is the slot-2 relation, so L4b2 needs the slot-1 analogue or `twL2'` with an explicit `M` correction. `D1t`, `D2t` carry `Tr(G^σ P_{ac})` of the uncircled `G`, not of `Ǧ` (`twTr_eq`: `twTr` is the `Ǧ` one). P3 (`|𝔼X_c|`, not among the seven) is re-derived in L4b2 (Amend 1 item 4); nothing here uses it.
3. S3's three roots (above) are outside `baG5Graph` (`mdot := []`); identity, closure `ord ≥ 5 - 2·1[x~y]`, leaf bound are owed to the successor (provisionally L4d2), Amend 1 item 3.
