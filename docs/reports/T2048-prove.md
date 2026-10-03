Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 10:27:00 UTC 2026

Target (KL7b): `KLK_sumAll_le`: for κ>0, L≥3, W≥1, |E|≤2−κ, t∈[0,1), n≥2, σ₁=+, σₙ=−, a₁ fixed:
`|∑_{a₂..aₙ} 𝒦_{t,σ,a}| ≤ 2^{n²} c_κ^{-2n} (W^d η_t)^{-(n−1)}`, `c_κ = gapK κ`, `η_t = (1−t) Im m(E)`.
Notation: `u = (W^d η_t)^{-1}`, `B_n = 2^{n²} c^{-2n} u^{n−1}`, `T_n(σ) = ∑_{a∈(Z_L^d)^n} 𝒦_{t,σ,a}`.
Claim proved by induction: `|T_n(σ)| ≤ L^d B_n` for ALL σ∈{±}ⁿ; then `T_n = L^d · (fibre sum at a₁)` (translation) and divide by L^d.

**(i) Exponent table.**
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | d | free in the statement (no `3≤d` used: Θ row/column sums need only `3≤L`, `‖ξ‖<1`); instance d=3 | none needed |
| 2 | g | free real (`KLK_ward`, `KLK_translate`, `KLK_rotate` take `(g E : ℝ)` with no hypothesis on g; `sum_Theta_row_of_three_le` needs only `3≤L`, `‖ξ‖<1`); instance g=1/2 | none |
| 3 | L, W | `3≤L` (Θ symmetric, row sums), `1≤W` (so `W^d>0`); instance L=3, W=2 | 0 for L; W^d=8 |
| 4 | κ, E | κ>0, \|E\|≤2−κ ⇒ κ≤2, \|E\|≤2; instance κ=1, E∈{0,1} | 2−κ−\|E\| = 1, 0 |
| 5 | t, η_t | t∈[0,1): `η_t>0` needs t<1, \|E\|<2; `η_t≤1` needs t≥0 (Im m≤1). Script: η=0.5, 0.1 (E=0, t=.5,.9), 0.4330, 0.0866 (E=1) | η_t ≤ 1 ⇒ `W^{-d} ≤ u` (slack `η_t^{-1}` = 2, 10, 2.31, 11.5) |
| 6 | gap `c=gapK κ=min(1,√(κ(4−κ)/2))` | `0<c≤1`; `c ≤ \|1−t m(s)²\|` (merged `gapK_le_norm`, same-sign only: `m(+)m(−)=1` has no gap, `\|1−t\|→0`, hence η_t) | κ=1: c=1; min\|1−t m²\| = 1.5 (E=0), 1.3229 (E=1) (script) |
| 7 | pure n=1 | `\|T_1\| = L^d\|m\| = L^d` ≤ `L^d B_1 = L^d·2c^{-2}` | factor 2c^{-2} ≥ 2 |
| 8 | pure n=2 | `T_2 = L^d W^{-d} m²/(1−t m²)`; `\|T_2\| ≤ L^d W^{-d} c^{-1}` ≤ `L^d·16c^{-4}u` | `16c^{-3}η_t^{-1}` ≥ 16 (=32 at c=1, η=.5) |
| 9 | pure n≥3 (`sum_Kpi_closed`, only π=∅ survives) | `T_n = (W^d)^{-(n−1)} L^d Alayer(∅)`; `\|Alayer\| ≤ \|∏m\|·c^{-n}·\|Q\|`, `\|Q\| ≤ #TSP·c^{-(n−2)}` (edge `\|(1−ξ)^{-1}−1\| = t/\|1−ξ\| ≤ c^{-1}`, `\|F\|≤n−2`), `#TSP ≤ 2^{n²}`. Total `2^{n²}c^{-(2n−2)} W^{-d(n−1)}` vs `B_n` | `c^{-2}η_t^{-(n−1)}` ≥ 1 (script: all pure inequalities hold, n=1..8) |
| 10 | Ward step (σ₁=+, σₙ=−, `KLK_ward`) | `T_n(σ)=(2iW^dη_t)^{-1}(T_{n−1}(+,μ)−T_{n−1}(−,μ))`, `\|·\|≤ (u/2)·2·L^d B_{n−1}` | `B_n/(u B_{n−1}) = 2^{2n−1}c^{-2}` = 8, 32, 128 (n=2,3,4; c=1); 32,128,512 (c=½) |
| 11 | constant `2^{n²}c^{-2n}` | `n²` from `#TSP ≤ 2^{#diagonals} ≤ 2^{n²}`; `c^{-2n}` from `c^{-(2n−2)}` (row 9) and from the induction `c^{-2(n−1)} ≤ c^{-2n}` (row 10); `2^{(n−1)²} ≤ 2^{n²}` | script: #TSP(n)=1,3,11,45,197 (n=3..7), max\|F\|=n−3 ≤ n−2 |
| 12 | §23 factor `∏m(σ_i)` | `Alayer`, `KLKpi` carry it; RBM2D has `∏mSig` outside `L²·Alayer`. Enters only in row 9 (`T_n = (W^d)^{-(n−1)}·(L^d·Alayer ∅)`, no separate `∏m`); `\|∏m\|=1` ⇒ norm bound unchanged. Nowhere else (n=1,2, Ward, rotation, translation: statements without it) | script: σ=(+,+,−) T=1.125j = closed form WITH ∏m (=1j), 1.125 without; σ=(+,+,+,−): −0.15625 vs +0.15625 |
| 13 | translation, fibre | `T_n = L^d ·∑_{a: a₁=y}`, `card Zd d L = L^d` (RBM2D :361 has L²); fibre independent of y by `KLK_translate` | script: rel. diff. in a₁∈{0,5,13} ≤ 5.0e-16 |
| 14 | rotation, induction | `KLK_rotate`: `T_n(σ)=T_n(σ∘(·+1))`; non-pure σ has i₀ with σ(i₀)=−, σ(i₀+1)=+, rotate to σ₁=+, σₙ=− | script: rotation rel. err ≤ 7.7e-16 |

**(ii) One nondegenerate instance.** d=3, L=3 (N=L^d=27), W=2, g=1/2, E∈{0,1} (κ=1, c=1, \|E\|≤1=2−κ), t∈{1/2, 9/10}, n∈{2,3,4}, all σ∈{±}ⁿ (σ₁=+, σₙ=− for the bound; all σ for rotation/induction). 𝒦 is the tree sum `(eq_Ktree)` (n=3,4: 1 resp. 3 trees), Θ=(1−ξS^(B))⁻¹ with S^(B): diagonal 0.4, six neighbours 0.1, by exact Fourier sum (the T2004 construction, whose ODE/Ward checks were passed there). No hypothesis of the target is external, so the lesson-14 limit computation has nothing to check; the Ward identity (merged `KLK_ward`) is verified numerically on totals below.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2048/T2048_pre.py` (scripts `T2048_table.py`, `T2048_inst.py` in the same directory).
```
d=3 L=3 W=2 g=0.5 N=27
E=0 t=0.5 eta=0.50000 u=(W^d eta)^-1=0.2500 | max|fibre|/B (s1=+,sn=-), max|T|/(L^d B) all sigma: {2: ('6.25e-02', '6.25e-02', 'bare 1.000'), 3: ('1.30e-03', '1.30e-03', 'bare 0.667'), 4: ('1.02e-05', '1.02e-05', 'bare 0.667')}
   rel err: fibre const in a1 5.0e-16 | Ward on totals 2.2e-15 | rotation 5.3e-16 | closed form (Alayer incl. prod m; n=2 row sum) 3.2e-15
E=0 t=0.9 eta=0.10000 u=(W^d eta)^-1=1.2500 | ... {2: ('6.25e-02', '6.25e-02', 'bare 1.000'), 3: ('1.03e-03', '1.03e-03', 'bare 0.526'), 4: ('8.03e-06', '8.03e-06', 'bare 0.526')}
   rel err: fibre const in a1 4.3e-16 | Ward on totals 8.4e-15 | rotation 5.1e-16 | closed form (Alayer incl. prod m; n=2 row sum) 8.6e-15
E=1 t=0.5 eta=0.43301 u=(W^d eta)^-1=0.2887 | ... {2: ('5.41e-02', '5.41e-02', 'bare 0.866'), 3: ('1.11e-03', '1.11e-03', 'bare 0.567'), 4: ('8.50e-06', '8.50e-06', 'bare 0.557')}
   rel err: fibre const in a1 3.9e-16 | Ward on totals 9.2e-16 | rotation 4.5e-16 | closed form (Alayer incl. prod m; n=2 row sum) 1.2e-15
E=1 t=0.9 eta=0.08660 u=(W^d eta)^-1=1.4434 | ... {2: ('5.41e-02', '5.41e-02', 'bare 0.866'), 3: ('8.90e-04', '8.90e-04', 'bare 0.456'), 4: ('6.95e-06', '6.95e-06', 'bare 0.455')}
   rel err: fibre const in a1 3.2e-16 | Ward on totals 3.7e-15 | rotation 7.7e-16 | closed form (Alayer incl. prod m; n=2 row sum) 4.4e-15
Alayer w/ prod m vs without, E=0 sigma=(+,+,-): |prod m|=1.000, prod m=1j (differs from 1 => factor needed)
  sigma=(1, 1, -1) T=1.125j  closed(with prod m)=1.125j  closed(without)=(1.125+0j)
  sigma=(1, -1, 1, -1) T=(0.28125+0j)  closed(with prod m)=(0.28125+0j)  closed(without)=(0.28125+0j)
  sigma=(1, 1, 1, -1) T=(-0.15625-0j)  closed(with prod m)=(-0.15625+0j)  closed(without)=(0.15625-0j)
E=0 max over s,t of |edgeR(s,s)| = 0.4737 <= 1/gapK(1)=1.0000; min|1-t m(s)^2|=1.5000 >= gapK(1)=1.0000
E=1 max over s,t of |edgeR(s,s)| = 0.5467 <= 1/gapK(1)=1.0000; min|1-t m(s)^2|=1.3229 >= gapK(1)=1.0000
```
(Columns: max over σ₁=+,σₙ=− of |fibre|/B_n; max over all σ of |T_n|/(L^d B_n); "bare" = max |fibre|/u^{n−1}, i.e. the bound with constant 1. "..." = same header as the first line. "closed form" is `T_n = (W^d)^{-(n−1)} L^d ∏m ∏_v(1−ξ_v)^{-1} ∑_{F∈TSP(n)}∏_{e∈F}((1−ξ_e)^{-1}−1)`, n≥3, and the row-sum formula at n=2.)
Command: `python3 .../T2048_table.py` and `python3 .../T2048_inst.py`:
```
c=1.0 E=0 t=0.5 eta=0.5000 u=0.250: all inequalities hold: True; slack B_n/(u B_{n-1}) at n=2,3,4: ['8', '32', '128'] = 2^(2n-1)c^-2: [8.0, 32.0, 128.0]
c=1.0 E=1 t=0.9 eta=0.0866 u=1.443: all inequalities hold: True; slack B_n/(u B_{n-1}) at n=2,3,4: ['8', '32', '128'] = 2^(2n-1)c^-2: [8.0, 32.0, 128.0]
c=0.5 E=0 t=0.5 eta=0.5000 u=0.250: all inequalities hold: True; slack B_n/(u B_{n-1}) at n=2,3,4: ['32', '128', '512'] = 2^(2n-1)c^-2: [32.0, 128.0, 512.0]
c=0.5 E=1 t=0.9 eta=0.0866 u=1.443: all inequalities hold: True; slack B_n/(u B_{n-1}) at n=2,3,4: ['32', '128', '512'] = 2^(2n-1)c^-2: [32.0, 128.0, 512.0]
n=3 |diagonals|=0  #TSP(n)=1 (<= 2^(n^2)=512)  max|F|=0 (= n-2=1)
n=4 |diagonals|=2  #TSP(n)=3 (<= 2^(n^2)=65536)  max|F|=1 (= n-2=2)
n=5 |diagonals|=5  #TSP(n)=11 (<= 2^(n^2)=33554432)  max|F|=2 (= n-2=3)
n=6 |diagonals|=9  #TSP(n)=45 (<= 2^(n^2)=68719476736)  max|F|=3 (= n-2=4)
n=7 |diagonals|=14  #TSP(n)=197 (<= 2^(n^2)=562949953421312)  max|F|=4 (= n-2=5)
E=0 t=1/2 kappa=1 sigma=(1, -1): fibre(a1=0)=(0.25+0j)  bound B=4.0000  ratio=6.250e-02  (n=2 exact W^-d/(1-t)=0.2500)
E=0 t=1/2 kappa=1 sigma=(1, -1, 1, -1): fibre(a1=0)=(0.01041667-0j)  bound B=1024.0000  ratio=1.017e-05  (n=2 exact W^-d/(1-t)=0.2500)
```
(The "all inequalities" lines check, for n up to 8: row 7, 8, 9 (pure) and row 10 (induction step) with W=2, d=3. The last two lines are the two instances of the ticket at κ=1, E=0, t=1/2.)

**Verdict.** `KLK_sumAll_le` (n≥2, σ₁=+, σₙ=−, all a₁): PASS. Hypotheses hold at the instance; every inequality closes with slack ≥ 8 (row 10) and ≥ 1 (row 9); the ticket's two compiled instances (n=4 σ=(+,−,+,−), n=2) have ratios 1.0e-5 and 6.3e-2; the only change against RBM2D beyond renaming, `W²→W^d`, `L²→L^d` is the §23 factor in row 12 (cancels in norm; script shows the phase matters for the closed form itself).

## (b) Script output (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2048, branch t/T2048; scripts and raw outputs in
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2048/: `report_b.sh` -> `report_b.out` (pasted below), `portdiff.py`, `portdiff_full.out` (all body hunks), `extract.py`, `clash.sh`)

$ date -u   # first command of the final collection
Sat Oct  3 10:53:36 UTC 2026
$ git log --oneline -1; git diff --stat main...t/T2048; git diff --name-only main...t/T2048
1f823ca T2048: KL7b, port RBM2D Loop/SumAll.lean to RBM3D/Loop/KLSumAll.lean
 RBM3D/Loop/KLSumAll.lean | 842 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 842 insertions(+)
RBM3D/Loop/KLSumAll.lean
$ lake build RBM3D.Loop.KLSumAll 2>&1 | tail -2
Build completed successfully (3248 jobs).
$ lake build 2>&1 | grep -E "axiom audit|error|Build completed|sorry"   # whole library as on the branch (RBM3D.lean does not import the module yet)
info: RBM3D.lean:84:0: axiom audit: 1484 theorems, 543 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3744 jobs).
$ # the hub adds `import RBM3D.Loop.KLSumAll` after the last import of RBM3D.lean at merge; the same line added here temporarily:
$ git diff --stat; lake build 2>&1 | grep -E "axiom audit|All within|error|Build completed|sorry"
 RBM3D.lean | 1 +
 1 file changed, 1 insertion(+)
info: RBM3D.lean:85:0: axiom audit: 1490 theorems, 543 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
Build completed successfully (3745 jobs).
$ cmp RBM3D.lean RBM3D.lean.orig && echo identical; git status --short   # the line removed again, root module rebuilt
identical
$ lake env lean precheck.lean 2>&1 | head -3; echo exit   # registry pre-check (DECISIONS §20): scratch file `import RBM3D` / `import RBM3D.Loop.KLSumAll` / `#assert_rbm_axioms`, not committed
axiom audit: 1490 theorems, 543 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit: 0
$ lake env lean precheck_ctrl.lean 2>&1 | head -1   # control: `import RBM3D` only
axiom audit: 1484 theorems, 543 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean ax.lean   # #print axioms of the target and of the instances
'RBM.Loop.KLK_sumAll_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_four_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_two_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_three' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axgroups.lean 2>&1 | head -3   # collectAxioms of every declaration of the module (public and private, non-internal)
declarations of RBM3D.Loop.KLSumAll (non-internal): 39
3 declarations depend exactly on axioms #[Quot.sound, propext]
36 declarations depend exactly on axioms #[Classical.choice, Quot.sound, propext]
$ grep -nE "sorry|admit|native_decide|^\s*axiom|^\s*opaque|implemented_by|extern" RBM3D/Loop/KLSumAll.lean; echo exit $?
exit: 1
$ grep -nE ": Prop|structure|class |^import" RBM3D/Loop/KLSumAll.lean
6:import RBM3D.Loop.KLSumZero
7:import RBM3D.Loop.KLWard
8:import RBM3D.Loop.KLUnique
111:    (v : Fin n) : Prop :=
$ python3 extract.py RBM3D/Loop/KLSumAll.lean KLK_sumAll_le   # text from the keyword to :=; the section variable is `variable (d : ℕ) (g : ℝ)` (line 724)
[KLSumAll.lean:729] theorem KLK_sumAll_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) (hn : 2 ≤ n) (σ : Fin n → Bool),
      σ ⟨0, by omega⟩ = true → σ ⟨n - 1, by omega⟩ = false → ∀ a₁ : Zd d L,
        ‖∑ a ∈ Finset.univ.filter (fun a : Fin n → Zd d L => a ⟨0, by omega⟩ = a₁),
            KLK d L g W E t (KLloopOf d L σ a)‖
          ≤ 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (((W : ℝ) ^ d * Gauss.etaT E t)⁻¹) ^ (n - 1)
$ lake env lean chk_target.lean 2>&1 | tr -s "[:space:]" " "   # `#check @RBM.Loop.KLK_sumAll_le`, elaborated (whitespace squeezed to one line)
RBM.Loop.KLK_sumAll_le : ∀ (d : ℕ) (g κ : ℝ), 0 < κ → ∀ (L W : ℕ) [inst : NeZero L], 3 ≤ L → 1 ≤ W → ∀ (E : ℝ), |E| ≤ 2 - κ → ∀ t ∈ Set.Ico 0 1, ∀ (n : ℕ) (hn : 2 ≤ n) (σ : Fin n → Bool), σ ⟨0, ⋯⟩ = true → σ ⟨n - 1, ⋯⟩ = false → ∀ (a₁ : RBM.Zd d L), ‖∑ a with a ⟨0, ⋯⟩ = a₁, RBM.Loop.KLK d L g W E t (RBM.Loop.KLloopOf d L σ a)‖ ≤ 2 ^ n ^ 2 * (RBM.Loop.gapK κ)⁻¹ ^ (2 * n) * (↑W ^ d * RBM.Gauss.etaT E t)⁻¹ ^ (n - 1) 
$ python3 extract.py RBM3D/Loop/KLSumAll.lean <5 instances>   # compiled instances, d = 3, L = 3, W = 2, g = 1/2, E = 0, t = 1/2, kappa = 1; no hypothesis left
[KLSumAll.lean:771] theorem KLSumAll_inst_four (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 4 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false, true, false] a)‖
      ≤ 2 ^ (4 ^ 2) * (gapK 1)⁻¹ ^ (2 * 4) *
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (4 - 1)
[KLSumAll.lean:780] theorem KLSumAll_inst_four_val (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 4 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false, true, false] a)‖ ≤ 1024
[KLSumAll.lean:789] theorem KLSumAll_inst_two (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false] a)‖
      ≤ 2 ^ (2 ^ 2) * (gapK 1)⁻¹ ^ (2 * 2) *
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (2 - 1)
[KLSumAll.lean:814] theorem KLSumAll_inst_two_val (a₁ : Zd 3 3) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, false] a) = 1 / 4
[KLSumAll.lean:798] theorem KLSumAll_inst_three (a₁ : Zd 3 3) :
    ‖∑ a ∈ Finset.univ.filter (fun a : Fin 3 → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
        KLK 3 3 (1 / 2) 2 0 (1 / 2) (KLloopOf 3 3 ![true, true, false] a)‖
      ≤ 2 ^ (3 ^ 2) * (gapK 1)⁻¹ ^ (2 * 3) *
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (3 - 1)
$ awk ... RBM3D/Loop/KLSumAll.lean   # the proof term of KLSumAll_inst_four (last 3 lines of the declaration)
          ((((2 : ℕ) : ℝ) ^ 3 * Gauss.etaT 0 (1 / 2))⁻¹) ^ (4 - 1) :=
  KLK_sumAll_le 3 (1 / 2) 1 one_pos 3 2 (by norm_num) (by norm_num) 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 (by norm_num) ![true, false, true, false] rfl rfl a₁
$ python3 portdiff.py SumAll_c9a24cf.lean RBM3D/Loop/KLSumAll.lean SumAll_pure_ge3   # SumAll_c9a24cf.lean = git -C ../RBM2D show c9a24cf:RBM2D/Loop/SumAll.lean
RBM2D declarations in SumAll.lean (c9a24cf): 39; RBM3D declarations in KLSumAll.lean (private, public, instances): 38
signature (text up to ':=') SAME after renaming R1-R4: 30
   SumAll_isDiag_of_mem_TSP SumAll_crossingFree_of_mem_TSP SumAll_gapK_pos SumAll_gapK_le_one SumAll_norm_edge_le SumAll_goodPt SumAll_exists_goodPt SumAll_goodPt_inj SumAll_card_le_of_mem_TSP SumAll_card_TSPlong_le SumAll_etaT_le_one SumAll_T SumAll_sum_snoc SumAll_ofFn_rot SumAll_T_rot SumAll_T_rot_iter SumAll_exists_false_true SumAll_fiber_const SumAll_T_eq_fiber SumAll_loopOf_snoc SumAll_loopOf_cons SumAll_T_ward SumAll_norm_inv_one_sub_le SumAll_pure_one SumAll_pure_two SumAll_pure_ge3 SumAll_B SumAll_pure_bound SumAll_main Kcal_sumAll_le
replaced by merged API / not needed / instances: 9
   SumAll_norm_mSig'  ->  norm_mSigma (merged, Defs/Semicircle.lean:87)
   SumAll_norm_xi'  ->  norm_mul_mSigma_lt_one (merged, Defs/Semicircle.lean:91; only ‖ξ‖ < 1 is used)
   SumAll_gapK_sq_le  ->  inside merged gapK_le_norm (KLSumZero.lean:456, public)
   SumAll_norm_one_sub_sq  ->  inside merged gapK_le_norm (KLSumZero.lean:456, public)
   SumAll_gapK_le_norm  ->  gapK_le_norm (merged, KLSumZero.lean:456, public)
   SumAll_etaT_eq  ->  rfl: Gauss.etaT E t = (1 - t) * (mE E).im (GLoop.lean:75)
   SumAll_etaT_pos  ->  Gauss.etaT_pos (merged, GLoop.lean)
   SumAll_card_Z2  ->  card_Zd (merged, Defs/Lattice.lean:67)
   SumAll_check_instance  ->  section 7: KLSumAll_inst_*
RBM2D declarations with no RBM3D counterpart (must be empty): []
signature DIFFERS after renaming: 0
proof body: lines of the RBM2D proof (renamed) / of the RBM3D proof / lines that differ after renaming (rows with >= 5 differing lines; the others are one-line API renames):
   SumAll_T_ward                        23   26    6
   SumAll_pure_two                      34   35   12
   SumAll_pure_ge3                      74   76   22
   SumAll_main                          73   75    7
   (26 further declarations, 23 differing lines in total)
   total (all 30 ported)               498  505   70
--- body diff of SumAll_pure_ge3: hunks that involve the factor ∏ m / Alayer / hT (- RBM2D renamed, + RBM3D); other hunks as one line each (first - line ==> first + line)
  ~ have hct := KLSumAll_gapK_le_norm hκ hE ht.1 s  ==>  have hct := gapK_le_norm hκ hE ht.1 s
  ~ have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSigma E s * mSigma E s  ==>  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSigma E s * mSigma E s
  - have hT : KLSumAll_T d L g W E t σ = ((W : ℂ) ^ d)⁻¹ ^ (k + 3 - 1) * (∏ i, mSigma E (σ i)) *
  + have hT : KLSumAll_T d L g W E t σ = ((W : ℂ) ^ d)⁻¹ ^ (k + 3 - 1) *
  ~ rw [Finset.sum_congr rfl (fun a _ => Kcal_eq_sum_Kpi L W E t  ==>  rw [Finset.sum_congr rfl
  ~ rw [Finset.sum_congr rfl (fun π _ => sum_Kpi_closed (mSigma   ==>  rw [Finset.sum_congr rfl (fun π _ => sum_Kpi_closed d L g (m
  ~ rw [norm_mul, KLSumAll_norm_mSig' hE2]; norm_num  ==>  rw [norm_mul, norm_mSigma hE2]; norm_num
  - have hA : ‖Alayer (mSigma E) t σ ∅‖ ≤
  - (gapK κ)⁻¹ ^ (k + 3) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1)) := by
  - unfold Alayer
  - rw [norm_mul, norm_prod]
  - have hP : ∏ v : Fin (k + 3), ‖(1 - (t : ℂ) * (mSigma E (σ v) * mSigma E (σ (v + 1))))⁻¹‖
  + have hprodm : ‖∏ i, mSigma E (σ i)‖ = 1 := by
  + rw [norm_prod]; simp [hσ, norm_mSigma hE2]
  + have hP : ‖∏ v : Fin (k + 3), (1 - (t : ℂ) * (mSigma E (σ v) * mSigma E (σ (v + 1))))⁻¹‖
  + rw [norm_prod]
  + have hA : ‖Alayer (mSigma E) t σ ∅‖ ≤
  + (gapK κ)⁻¹ ^ (k + 3) * (2 ^ ((k + 3) ^ 2) * (gapK κ)⁻¹ ^ (k + 1)) := by
  + unfold Alayer
  + rw [norm_mul, norm_mul, hprodm, one_mul]
  - rw [hT, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  + rw [hT, norm_mul, norm_mul, norm_pow, norm_pow]
  - have h2 : ‖∏ i, mSigma E (σ i)‖ = 1 := by
  - rw [norm_prod]; simp [hσ, KLSumAll_norm_mSig' hE2]
  - rw [h1, h2, h3, mul_one]
  + rw [h1, h3]
RBM3D declarations with no RBM2D counterpart (8): KLSumAll_etaT_half KLSumAll_gapK_one KLSumAll_inst_four KLSumAll_inst_four_val KLSumAll_inst_three KLSumAll_inst_two KLSumAll_inst_two_val KLSumAll_mSigma_zero
$ clash.sh   # each new public name, grep -w, on main and on every other t/* branch (git grep) and in the worktree outside the new file
refs checked: main + 44 t/* branches (all except t/T2048); and the worktree outside RBM3D/Loop/KLSumAll.lean
  KLK_sumAll_le: hits on refs = 0, in worktree outside the file = 0
  KLSumAll_inst_four: hits on refs = 0, in worktree outside the file = 0
  KLSumAll_inst_four_val: hits on refs = 0, in worktree outside the file = 0
  KLSumAll_inst_two: hits on refs = 0, in worktree outside the file = 0
  KLSumAll_inst_two_val: hits on refs = 0, in worktree outside the file = 0
  KLSumAll_inst_three: hits on refs = 0, in worktree outside the file = 0
  file-stem prefix: git grep -c 'KLSumAll_' main -- RBM3D RBM3D.lean -> 0 hits
$ cd ~/Lean_proof/RBM3D   # main worktree, read-only commands; date -u:
Sat Oct  3 10:54:36 UTC 2026
$ git -C ../RBM2D --no-optional-locks log -1 --format="RBM2D HEAD %h"; ... merge-base --is-ancestor c9a24cf HEAD; echo exit $?
RBM2D HEAD 9e0f275
exit: 0
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/SumAll.lean
 RBM2D/Loop/SumAll.lean | 47 +++++++++++++----------------------------------
 1 file changed, 13 insertions(+), 34 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Loop/SumAll.lean | wc -l; grep -n "sumAinK\|sumallAinK\|sumAll" paper/tex/*.tex; echo exit $?
     788
exit: 1
$ git -C ../RBM2D --no-optional-locks grep -n "SumAll_\|sumAll" c9a24cf -- RBM2D/Loop/SumZeroWard.lean | cut -c1-110   # what KL7c takes from SumAll
c9a24cf:RBM2D/Loop/SumZeroWard.lean:29:  `Kcal_sumAll_le` (T2028) at `L = 3`, `W = 1` with `Kcal_eq_sum_Kpi` (
c9a24cf:RBM2D/Loop/SumZeroWard.lean:31:* `Kcal_sumAll_le` is stated only for `σ₀ = +`, `σ_{n-1} = -`.  The ind
c9a24cf:RBM2D/Loop/SumZeroWard.lean:1397:/-! ## 8. The base bound (3.49) from the RBM2D Ward bound `Kcal_sumAl
c9a24cf:RBM2D/Loop/SumZeroWard.lean:1406:η_t^{-(n-1)}`.  From `Kcal_sumAll_le` (T2028) at `L = 3`, `W = 1`, wi
c9a24cf:RBM2D/Loop/SumZeroWard.lean:1446:    have h := Kcal_sumAll_le κ hκ 3 1 (by norm_num) le_rfl E hE t ht 
$ python3 (exact arithmetic) B_n = 2^(n^2) c^(-2n) ((W^d eta_t)^-1)^(n-1) at c = gapK 1 = 1, W = 2, d = 3, eta_t = 1/2
u = 1/4  B_n: {2: '4', 3: '32', 4: '1024'}
$ python3 T2048_inst.py   # preflight script: fibre sum from the tree sum (eq_Ktree), E = 0, t = 1/2, kappa = 1
E=0 t=1/2 kappa=1 sigma=(1, -1): fibre(a1=0)=(0.25+0j)  bound B=4.0000  ratio=6.250e-02  (n=2 exact W^-d/(1-t)=0.2500)
E=0 t=1/2 kappa=1 sigma=(1, -1, 1, -1): fibre(a1=0)=(0.01041667-0j)  bound B=1024.0000  ratio=1.017e-05  (n=2 exact W^-d/(1-t)=0.2500)

Narrative (each fact is in the output above, the files or the tool log):
1. Source: `RBM2D/Loop/SumAll.lean` at `c9a24cf` (788 lines, read-only; its only public declaration is `Kcal_sumAll_le`). RBM2D HEAD is `9e0f275` and `c9a24cf` is its ancestor; the later diff of this file (read in full) is docstrings and the removal of the checks section, no proof change. RBM1D: not read, nothing copied.
2. Coverage (`portdiff.py`): 39 RBM2D declarations; 30 ported, every signature identical after the renaming (`Z2 L ↦ Zd d L`, `Kcal L W E t (loopOf L σ a) ↦ KLK d L g W E t (KLloopOf d L σ a)`, `mSig ↦ mSigma`, `etaT ↦ Gauss.etaT`, `TSPlong/Flong/ArcLe ↦ KLTSPlong/KLFlong/KLArcLe`, `Theta L ↦ Theta d L g`, `W², L² ↦ W^d, L^d`, the binders `(d L : ℕ) [NeZero L] (g : ℝ)` and `{g : ℝ}`); 9 replaced by merged API or by section 7 (list above); none missing.
3. Reused, not copied: `KLK_ward`, `KLK_rotate`, `KLK_translate`, `KLK_eq_sum_Kpi`, `KLK_two`, `sum_Kpi_closed`, `Alayer`, `Qlayer`, `edgeR`, `gapK`, `gapK_le_norm`, `norm_mSigma`, `norm_mul_mSigma_lt_one`, `Gauss.etaT_pos`, `card_Zd`, `sum_Theta_row_of_three_le`, `KLisTSP_of_mem_TSP`. Copied and kept private (they are private in `KLSumZero.lean`): `gapK_pos`, `gapK_le_one`, `norm_edge_le`, the `goodPt` chain, `card_le_of_mem_TSP`, `card_TSPlong_le`; also `etaT_le_one` (private in RBM2D).
4. DECISIONS §23 (the factor `∏ m(σ_i)`): it enters only in `KLSumAll_pure_ge3` (body diff above). The merged `KLK_eq_sum_Kpi` has no separate `∏ m` and `Alayer` contains it, so `hT` loses RBM2D's factor `∏ m(σ_i)` and `hA` uses `hprodm : ‖∏ m(σ_i)‖ = 1`. The statement, `n = 1, 2`, the Ward step, rotation and translation are unchanged. Brute force: section (a) row 12 and its script lines (σ = (+,+,+,−): closed form −0.15625 with the factor, +0.15625 without).
5. All other body differences were read (`portdiff_full.out`: 30 declarations, 70 differing lines in all): names and argument order of the merged lemmas, the named arguments `(d := d) (g := g)`, `rw [Gauss.etaT]`, `Bool.not_true` for the `[!true]` of `KLK_ward`, line wrapping, and `KLisTSP_of_mem_TSP` for the two laminar helpers.
6. Statement: `KLK_sumAll_le` has the signature of `Kcal_sumAll_le` after the renaming; `(d : ℕ) (g : ℝ)` stand first (section variables, as in KL7a's `SigmaPi_alt_sumZero_le_of_Qlayer_one`). No hypothesis is added: `3 ≤ d` is not used, nothing is assumed on `g`, no unproved `Prop` enters (the only `Prop`-valued definition is the private `goodPt`, as in KL7a). `RBM3D/Test/Axioms.lean` is not touched; the pre-check exits 0 and counts 6 more theorems with the module (1490 against 1484).
7. Instances at d = 3, L = 3, W = 2, g = 1/2, E = 0, t = 1/2, κ = 1: n = 4, σ = (+,−,+,−) (fibre of 27³ terms; the bound is 1024, the `B` of the preflight script); n = 2 (the sum is 1/4 ≠ 0, against the bound 4); n = 3, σ = (+,+,−) (RBM2D's check at :775, which has n = 3; the ticket says n = 2 there, both are compiled). Every deterministic hypothesis is discharged; the theorem has no external hypothesis, so none is left.
8. KL7c: RBM2D `SumZeroWard.lean` takes only `Kcal_sumAll_le` from `SumAll.lean` (grep above, use at :1446 with `L = 3`, `W = 1`), so no helper is made public.
9. The whole library builds with the root import line added (3745 jobs); the line is removed again (`cmp` identical, `git status` empty); the root file is not in the diff.

## (c) Verified Mathlib names
Names newly used relative to RBM2D's `SumAll.lean` (the others occur there and compile here); `#check` output of `mathlibchk.lean`. No name was invented; none was searched for and found absent.
Bool.not_true : (!true) = false
Complex.mul_conj : ∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑(Complex.normSq z)
Complex.normSq_eq_norm_sq : ∀ (z : ℂ), Complex.normSq z = ‖z‖ ^ 2
@Finset.mem_univ : ∀ {α : Type u_1} [inst : Fintype α] (x : α), x ∈ Finset.univ
@Finset.sum_eq_single : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {s : Finset ι} {f : ι → M} (a : ι),
  (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s → f a = 0) → ∑ x ∈ s, f x = f a
@Finset.sum_filter : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [inst : AddCommMonoid M] (p : ι → Prop)
  [inst_1 : DecidablePred p] (f : ι → M), ∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0
@Real.one_le_sqrt : ∀ {x : ℝ}, 1 ≤ √x ↔ 1 ≤ x
@ite_true : ∀ {α : Sort u_1} {x : Decidable True} (a b : α), (if True then a else b) = a
@min_eq_left : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → min a b = a
@one_mul : ∀ {M : Type u_1} [inst : MulOneClass M] (a : M), 1 * a = a

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. This paper has no counterpart statement (grep above, exit 1); the explicit constant `2^{n²} c_κ^{-2n}` and the bulk restriction `|E| ≤ 2 - κ` are RBM2D's paper-delta T2004a-11, cited and not re-proposed (ticket).
- Section (a) is not edited and there is no (a′): its rows 7-12 match the file (pure `n = 1, 2, ≥ 3` in `KLSumAll_pure_one/two/ge3`, the Ward step `u/2 · 2 · L^d B_{n-1}` in `KLSumAll_main`, `∏ m` only in the pure `n ≥ 3` identity).
- No obstruction: nothing stopped, no target weakened, no hypothesis added. `KLK_sumAll_le` is the general statement (all `n ≥ 2`, `σ₁ = +`, `σ_n = −`, all `a₁`), not a conditional adapter.
- For KL7c: use `KLK_sumAll_le` as RBM2D's `SumZeroWard.lean:1446` does; the factor `∏ m(σ_i)` inside `Alayer` (T2043 audit O3) is KL7c's to adapt.

Report finished: Sat Oct  3 10:56:15 UTC 2026
