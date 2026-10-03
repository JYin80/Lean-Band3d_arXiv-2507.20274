Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 04:22:22 UTC 2026

Notation: `e = 1-t`, `γ = lgGam d g t = t g²/(1+2dg²)`, `ε = e/γ`, `n = zdistD d L a ≤ dL/2`, `μ = PropSpin m σ₁ · PropSpin m σ₂`
(`σ₁≠σ₂ ⇒ μ = m m̄ = 1`; `σ₁=σ₂ ⇒ μ = m²` or `m̄²`). `U1`, `U2s` (`i=j`), `U2m` (`i≠j`): the pinned differences times `(g²+e)(n+1)^{d-1}` resp. `(g²+e)(n+1)^d`.
`D1 = Θ(a+e_j)-Θ(a)`, `D2 =` unit second difference. Upstream (all merged theorems, none is a hypothesis of a target; read from the sources):
`kProd_diff1_le`/`kProd_diff2_le` (`τ ≤ L²`; `C=A^d, c=c_f/d`, HeatProduct.lean:469, :527): `|D K_τ| ≤ C min(1,τ^{-(d+1)/2}) e^{-c min(n²/τ,n)}`, resp. exponent `(d+2)/2`;
`kProd_gap` (`τ ≥ L²`; `C_G = d(1+C_g)^d, c_G = c_g`, :640): `|D1 K_τ| ≤ C_G L^{-(d+1)}e^{-c_Gτ/L²}`, `|D2 K_τ| ≤ C_G L^{-(d+2)}e^{-c_Gτ/L²}`;
`lg_bulk` (`m = d+1, d+2 ≥ 4 ≥ 3`, `c = c_K`, `c' = min(c/2,1)`; LaplaceGauss.lean:692, c' at :705): `n≥1`: `ε≤1`: `≤ C_B n^{-(m-2)} e^{-c' n√ε}`; `ε≥1`: `≤ (2/ε)e^{-c'n}`;
`lg_zero` (:541): `n=0`: `≤ 1+2/(m-2) ≤ 2` and `≤ 1/ε`; `lg_tail` (:295, κ>0 / ε>0 forms): `∫_{L²}^∞ e^{-ετ-κτ/L²} ≤ e^{-εL²} min(1/ε, L²/κ)`;
`lg_convA` (:206): `C_A = 3+4dΛ²+2Λ²`: `ε≥1 ⇒ 1/e ≤ C_A/(g²+e)`, `ε<1 ⇒ 1/γ ≤ C_A/(g²+e)` (both `0<t<1`, `0<g≤Λ`);
`prop5Short_holds` (Prop5Short.lean:400): `|Θ_{tμ}(0,a')| ≤ C_s(1_{a'=0} + g² e^{-c_s|a'|})` for `σ₁=σ₂`, `κ ≤ Im m`, `t ∈ [0,1)`.
Auxiliary closed form (checked below): `M_k(b) = sup_{x≥0}(1+x)^k e^{-bx} = max(1,(k/(be))^k e^b)`; `P_k = (d/2+1)^k` (`n+1 ≤ (d/2+1)L`).

### (i) Exponent / constant table

| step (regime) | statement used | constant | constraint / slack |
|---|---|---|---|
| `t = 0`, `σ₁≠σ₂` and `σ₁=σ₂` | `Θ = 1_{a=0}` (`ξ=0`, no `τ=γs`): `D1 ≠ 0` only if `n ≤ 1` (`|D1| ≤ 1`), `D2 ≠ 0` only if `n ≤ 2` (`|D2| ≤ 2`, `L ≥ 3`) | `C ≥ 2^{d-1}(Λ²+1)`, `C ≥ 2·3^d(Λ²+1)` | `(g²+1)⁻¹ ≥ (Λ²+1)⁻¹`; `(n+1)^{-(d-1)} ≥ 2^{-(d-1)}`, `(n+1)^{-d} ≥ 3^{-d}`; grid max at `t=0`: U1 = 8.000, U2 = 54.000 (= `1·2·27` at `g=1`, `n=2`, `|D2|=1`, output 1) |
| `t>0`, `σ₁≠σ₂`: reduction | `Θ_t(0,a) = γ⁻¹∫_0^∞ e^{-ετ}K_τ(a)dτ` (`Theta_eq_laplace_prod`, `0<t<1`), differences under the integral | exact | head+tail = Θ to `1e-7` (assert in pf2); `ε>0` since `t<1` |
| head `(0,L²]`, `ε ≥ 1`, `n ≥ 1` | `lg_bulk` 2nd: `γ⁻¹(2/ε)e^{-c'n} = 2e⁻¹e^{-c'n}`; `1/e ≤ C_A/(g²+e)`; `e^{-c'n} ≤ M_{d-1}(c')(n+1)^{-(d-1)}` (resp. `M_d(c')`) | `2C_K C_A M_{d-1}(c')` (resp. `M_d`) | no zero mode needed: the pins carry no exponential. `M_2(0.1)=59.8274`, `M_3(0.1)=1485.6269` (`b=c'=0.1`; closed form = brute force, output 2) |
| head, `ε < 1`, `n ≥ 1` | `lg_bulk` 1st (`ε ≤ 1`): `γ⁻¹C_B n^{-(d-1)}` (resp. `n^{-d}`), `e^{-c'n√ε} ≤ 1`; `γ⁻¹ ≤ C_A/(g²+e)`; `n^{-k} ≤ 2^k(n+1)^{-k}` | `C_K C_B(m) C_A 2^{d-1}` (resp. `2^d`) | `ε<1` covers both `L⁻² ≤ ε<1` and `ε<L⁻²`: the head needs no `ℓ_t`, no `L` (regimes B, C of PT-F1 coincide here) |
| head, `n = 0` | `lg_zero`: `ε<1`: `γ⁻¹(1+2/(m-2)) ≤ 2C_A/(g²+e)`; `ε≥1`: `γ⁻¹/ε = 1/e ≤ C_A/(g²+e)` | `2 C_K C_A` | `(n+1)^{-k} = 1` |
| tail `(L²,∞)`, all `ε>0` | `kProd_gap`: `γ⁻¹C_G L^{-(d+1)}∫_{L²}^∞ e^{-ετ-c_Gτ/L²}dτ ≤ C_G L^{-(d+1)} min(1/e, L²/(c_Gγ))` (`lg_tail`, `e^{-εL²} ≤ 1`) | as left | `ε≥1`: use `1/e ≤ C_A/(g²+e)`; `ε<1`: `L²/γ ≤ C_A L²/(g²+e)`; then `L^{-(d+1)}L² = L^{-(d-1)} ≤ P_{d-1}(n+1)^{-(d-1)}` (resp. `L^{-d} ≤ P_d (n+1)^{-d}`) by `n ≤ dL/2` |
| **U1 final, `σ₁≠σ₂`** | `C_1 = max(t=0 row, head rows `ε≥1`, `ε<1`, `n=0`, tail row `C_G max(1,1/c_G)C_A P_{d-1}`)`; max not sum (head, tail bound the two summands separately: sum of two) | explicit in `(d,Λ)` | Λ only through `C_A`, `Λ²+1`; grid max, all `t>0`: U1 = 6.167, U2s = 38.262, U2m = 38.533 (output 1; T2003 N5: ≤ 5.5, 9.6 at `L=193`) |
| `σ₁=σ₂`, `t ≥ 0`, `κ ≤ Im m` | triangle inequality (2 resp. 4 terms) + `prop5Short_holds`; `|a'| ≥ n-2` (`a' = a+e_i+e_j`, `zdistD` is an `ℓ¹` norm); `1_{a'=0} ⇒ n ≤ 2`, so `1 ≤ 3^d(n+1)^{-d}`; `1 ≤ (Λ²+1)/(g²+e)`; `g² ≤ Λ²(Λ²+1)/(g²+e)`; `e^{-c_s(n-2)} ≤ e^{2c_s}M_k(c_s)(n+1)^{-k}` | U1: `C_s[2(Λ²+1)2^{d-1} + 2Λ²(Λ²+1)e^{2c_s}M_{d-1}(c_s)]`; U2: `C_s[4(Λ²+1)3^d + 4Λ²(Λ²+1)e^{2c_s}M_d(c_s)]` | at `Λ=1, c_s=0.3, d=3`: chain constants 75.18 and 1195.65 (× `C_s`); direct max of the chain sums over `L∈{3,5,9}, g, e, a` = 38.066 and 742.196 (below, output 3). No use of `κ` beyond `prop5Short_holds` |
| final | `C = max(U1/U2 `σ≠` constants, `σ=` constants, `t=0` rows)`, after `(d,Λ,κ)`, before `L,g,t,m,σ,a,i,j` | explicit | matches pin order of `PropUnit1/2`; `d ≥ 3` used only via `lg_bulk/lg_zero` (`m ≥ 4`), `Γ`, `1+2/(m-2) ≤ 2` |

Dimension: `d-1`, `d` in `(n+1)^{d-1}` are ℕ-subtractions, harmless for `d ≥ 3`; `-(m-2)` real exponent at `m=d+1` equals `-(d-1)`.
Slack: no exponent is tight (pins have no exponential, only polynomial `(n+1)^{-(d-1)}`, `(n+1)^{-d}`); the exponent `d-1`, `d` is exactly `m-2` at `m = d+1, d+2` (the Gamma-integral of `lg_bulk`), 0 slack by design, none needed.
Tail check: the tail differences are at rounding level (`≤ 2.7e-15 … 1.3e-12` of the shape) because the realised gap rate is `27 … 39 ≫` any `c_G` used; the tail row is therefore not numerically tight.

### (ii) Concrete instance

Data: `d=3, Λ=1, κ=1/2, L=5, g=1/2, t=9/10, m=I, σ₁=true, σ₂=false, a=0, i=j=0` (`μ = I·conj(I) = 1`; `ε = 10/9 ≥ 1`; `n = 0`: head row `n=0`, tail row `ε≥1`).
Hypotheses: `3≤d`, `0<Λ`, `0<κ`, `3≤L`, `0<g≤Λ`, `0≤t<1`, `‖m‖=1`, `κ ≤ Im m = 1`. External hypotheses: none (every ingredient is a merged theorem, so no limit computation is needed).
Scripts (numpy; exact Fourier `Θ(0,·) = ifftn 1/(1-ξλ_k)`, `λ_k = (1+2g²Σcos k_j)/(1+2dg²)`; shifts by `np.roll`; checked against the Lean `Theta` convention through `1-tλ_k = e + γΣ(2-2cos k_j)`) in
`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2024/` (`common.py`, `pf1.py` … `pf4.py`).

Command 1 (output 1): `cd <dir> && python3 pf1.py` — ticket grid `d=3, L∈{3,5,9,17}, g∈{.05,.5,1}, t∈{0,.5,1-g²,1-g²/L²,1-g²/L³}`, all `a,i,j`, `μ=1`, and `μ ∈ {m²,m̄²}` at `sin φ ∈ {1,.5}` (`κ=1/2`):
```
rows (L,g,t,mu): 280  regimes (t,g,L rows): {'eps>=1': 20, 'Linv2<=eps<1': 14, 'eps<Linv2': 10, 't=0': 12}
('mu=1 (s1!=s2)', 't=0')                             max U1=8.000 U2s=54.000 U2m=54.000
('mu=1 (s1!=s2)', 't>0')                             max U1=6.167 U2s=38.262 U2m=38.533
('mu=m^2/mbar^2 (s1==s2, sin phi in {1,.5})', 't=0') max U1=8.000 U2s=54.000 U2m=54.000
('mu=m^2/mbar^2 (s1==s2, sin phi in {1,.5})', 't>0') max U1=6.161 U2s=44.485 U2m=44.669
```
Command 2 (output 2): `python3 pf2.py` — exact head/tail split at `τ=L²` (`head = L^{-d}Σe^{ika}(1-e^{-(ε+μ_k)L²})/(e+γμ_k)`) of the `σ₁≠σ₂` differences, regimes A/B/C = `ε ≥ 1`, `L⁻² ≤ ε < 1`, `ε < L⁻²`; `M_k` closed form vs brute force:
```
A eps>=1         U1 rows=20 head ratio |D head|(g^2+e)(n+1)^p max=6.167 ; tail ratio |D tail|/(L^-(d+q) min(1/e,L^2/gam)) max=4.52e-16
A eps>=1         U2 rows=20 head ratio |D head|(g^2+e)(n+1)^p max=38.533 ; tail ratio |D tail|/(L^-(d+q) min(1/e,L^2/gam)) max=2.71e-15
B Linv2<=eps<1   U1 rows=14 head ratio |D head|(g^2+e)(n+1)^p max=4.841 ; tail ratio |D tail|/(L^-(d+q) min(1/e,L^2/gam)) max=2.22e-13
B Linv2<=eps<1   U2 rows=14 head ratio |D head|(g^2+e)(n+1)^p max=27.404 ; tail ratio |D tail|/(L^-(d+q) min(1/e,L^2/gam)) max=1.33e-12
C eps<Linv2      U1 rows=10 head ratio |D head|(g^2+e)(n+1)^p max=4.666 ; tail ratio |D tail|/(L^-(d+q) min(1/e,L^2/gam)) max=4.41e-13
C eps<Linv2      U2 rows=10 head ratio |D head|(g^2+e)(n+1)^p max=25.695 ; tail ratio |D tail|/(L^-(d+q) min(1/e,L^2/gam)) max=2.65e-12
L=3  L^2(2-2cos(2pi/L))=27.000 (realised gap rate c_G, constants use any smaller c)
L=5  L^2(2-2cos(2pi/L))=34.549 (realised gap rate c_G, constants use any smaller c)
L=9  L^2(2-2cos(2pi/L))=37.901 (realised gap rate c_G, constants use any smaller c)
L=17  L^2(2-2cos(2pi/L))=39.031 (realised gap rate c_G, constants use any smaller c)
b=0.05 k=2  sup_x (1+x)^k e^{-bx}: brute 227.6385 closed form 227.6385
b=0.05 k=3  sup_x (1+x)^k e^{-bx}: brute 11305.3765 closed form 11305.3765
b=0.10 k=2  sup_x (1+x)^k e^{-bx}: brute 59.8274 closed form 59.8274
b=0.10 k=3  sup_x (1+x)^k e^{-bx}: brute 1485.6269 closed form 1485.6269
b=0.50 k=2  sup_x (1+x)^k e^{-bx}: brute 3.5701 closed form 3.5701
b=0.50 k=3  sup_x (1+x)^k e^{-bx}: brute 17.7304 closed form 17.7304
```
Command 3 (output 3): `python3 pf3.py` — chain for `σ₁=σ₂` with the Prop5Short shape `S(a)=1_{a=0}+g²e^{-0.3|a|}` on `L∈{3,5,9}`, `e ∈ {1,.5,g²,g²/L²,1e-6}`:
```
max over L,g,e,a,i,j of [S(a+e_j)+S(a)](g^2+e)(n+1)^(d-1) = 38.066 ; [4-point sum S](g^2+e)(n+1)^d = 742.196
analytic chain constants (Lam=1,c=.3,d=3), times C_s of prop5Short: U1 75.18, U2 1195.65
```
Command 4 (output 4): `python3 pf4.py` — the ticket instance, all `a ∈ Z_5³`, all `i,j`:
```
e=0.1000 gamma=0.0900 eps=1.1111 (>=1: regime A) L^-2=0.040 mu=PropSpin m true*PropSpin m false=(1+0j)
imag part max |Im Theta|=5.79e-17 (mu=1 so Theta real)
all a, i, j (L=5): U1=2.1110 U2s=11.8226 U2m=12.2115 ; max n=6 <= dL/2=7.5
target a=0, i=j=0:  |Theta(e_0)-Theta(0)|=1.507866 ; (g^2+e)^-1 (0+1)^-(d-1)=2.857143 ; ratio=0.5278
target a=0, i=j=0:  |2nd diff|=1.251070 ; (g^2+e)^-1 (0+1)^-d=2.857143 ; ratio=0.4379
(info) s1==s2 at same data, mu=m^2=(-1+0j): U1,U2s,U2m = 1.1314 8.1622 8.1979 ; |1-t mu|=1.900
lg_convA 1st part at instance: 1/e=10.000 <= C_A/(g^2+e)=48.571 (C_A=17)
```
Not covered by the compiled instance (it has `μ = 1`): the `σ₁=σ₂` branch; output 1 (`μ=m²,m̄²`) and output 4 (info line) cover it numerically.

### Verdicts
- `propUnit1_holds` (`PropUnit1 d Λ κ`): PASS. Hypotheses satisfiable at the instance (nonempty: `n=0`, `ε=10/9`, ratio 0.5278); regimes `t=0`, `ε≥1`, `ε<1`, `n=0`, tail, and `σ₁=σ₂` all close with constants depending on `(d,Λ,κ)` only and exact exponents `d-1`; no unproved input.
- `propUnit2_holds` (`PropUnit2 d Λ κ`): PASS. Same, exponents `d` (mixed and same-direction share the proof; instance ratio 0.4379 at `i=j=0`); `kProd_diff2_le`, `kProd_gap` 3rd conjunct supply the kernel bounds.
- Notes for 1b (no pin change): `t=0` is outside `Theta_eq_laplace_prod`'s `τ=γs` use (`γ=0`), separate case; `D1`/`D2` of the integral needs integrability of each `e^{-ετ}K_τ` on `(0,∞)` (from `lg_bulk` integrability on the head and `lg_tail` on the tail); `κ > 1` is vacuous (`Im m ≤ 1`).

## (b) Script output (stage 1b, `prover-max`; commit `d926433` on branch `t/T2024`; section (a) not edited, no (a′) needed)

```
$ git diff main...t/T2024 --stat; git log --format="%h %s" main..t/T2024
 RBM3D/Propagator/PropUnit.lean | 1008 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1008 insertions(+)
d926433 T2024: PropUnit1/PropUnit2 hold (route H unit first and second differences of Theta)
$ lake build RBM3D.Propagator.PropUnit > build_module.txt 2>&1; echo exit=$?   # run Sat Oct  3 04:44:23 UTC 2026 (`date -u`); exit=0
$ grep -v -e '^$' -e '^Note: This linter' build_module.txt | tail -4
⚠ [3408/3408] Built RBM3D.Propagator.PropUnit (13s)
warning: RBM3D/Propagator/PropUnit.lean:37:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/PropUnit.lean:59:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3408 jobs).
$ lake build > fullbuild.txt 2>&1; echo exit=$?   # Sat Oct  3 04:44:46 → 04:44:56 UTC; exit=0; `import RBM3D.Propagator.PropUnit` TEMPORARILY added after the last import of RBM3D.lean (the hub adds it at merge), removed again: `git status --short` empty, never committed
$ grep -n 'axiom audit\|All within\|Build completed' fullbuild.txt
88:info: RBM3D.lean:66:0: axiom audit: 1019 theorems, 387 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
89:All within [propext,
123:Build completed successfully (3723 jobs).
$ lake env lean axioms.lean   # run Sat Oct  3 04:45:09 UTC 2026: import RBM3D.Propagator.PropUnit; #print axioms ×4; #check @propUnit1_holds, @propUnit2_holds
'RBM.PropUnit1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.PropUnit2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.propUnit1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.propUnit2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.propUnit1_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.PropUnit1 d Λ κ
RBM.propUnit2_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.PropUnit2 d Λ κ
$ grep -nE 'sorry|admit|native_decide|^axiom|^[ ]*axiom ' RBM3D/Propagator/PropUnit.lean ; echo exit=$?
exit=1 (1 = no match)
$ grep -rn --include='*.lean' -E 'PropUnit|propUnit|pu_' RBM3D | grep -vc '^RBM3D/Propagator/PropUnit.lean'   # name-clash grep: new public names and the private prefix
0
```
Pinned statements: diff of the docstring+def blocks (check file lines 29-56; PropUnit.lean lines 37-64), run Sat Oct  3 04:53:23 UTC 2026:
```
$ diff <check-file defs> <PropUnit.lean defs>; echo diff-exit=$?; shasum -a 256 < each
diff-exit=0
e336b7b4eb4bc25fdfb77eb5de16959fd0fd898377aeb40458182aed334e3d6b
e336b7b4eb4bc25fdfb77eb5de16959fd0fd898377aeb40458182aed334e3d6b
```
Target statements, extracted from the file (`sed -n '37,63p' RBM3D/Propagator/PropUnit.lean | grep -v '^$'` for the defs, `grep -nE '^theorem' RBM3D/Propagator/PropUnit.lean` for the theorems):
```
/-- **Unit pin 1**: `|Θ_t(0, a + e_j) − Θ_t(0, a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-(d−1)}`; constants `(d, Λ, κ)`;
bulk `κ ≤ Im m` (idle for `σ₁ ≠ σ₂`, as in the merged P6–P8 pins). -/
def PropUnit1 (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
          ∀ (a : Zd d L) (j : Fin d),
            haveI : NeZero L := ⟨by omega⟩
            ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single j 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
              ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹
/-- **Unit pin 2**: the unit second differences, mixed (`i ≠ j`) and same-direction (`i = j`):
`|Θ(a+e_i+e_j) − Θ(a+e_i) − Θ(a+e_j) + Θ(a)| ≤ C (g² + |1−t|)⁻¹ (|a| + 1)^{-d}`. -/
def PropUnit2 (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool,
          ∀ (a : Zd d L) (i j : Fin d),
            haveI : NeZero L := ⟨by omega⟩
            ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single i 1 + Pi.single j 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single i 1)
                - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + Pi.single j 1)
                + Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
              ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹
747:theorem propUnit1_holds (d : ℕ) (Λ κ : ℝ) : PropUnit1 d Λ κ := by
826:theorem propUnit2_holds (d : ℕ) (Λ κ : ℝ) : PropUnit2 d Λ κ := by
```

Compiled nonempty instances: 5 `example`s in the built module (lines 928,941,961,975,989); the first two are the ticket's (`d=3, Λ=1, κ=1/2, L=5, g=1/2, t=9/10, m=I, σ₁=true, σ₂=false, a=0, i=j=0`):
```
$ sed -n '928,958p' RBM3D/Propagator/PropUnit.lean
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (0 : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
        * (((zdistD 3 5 (0 : Zd 3 5) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit1_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0 0⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1 + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1)
        - Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 ((0 : Zd 3 5) + Pi.single 0 1)
        + Theta 3 5 (1 / 2)
          (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
          0 (0 : Zd 3 5)‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
        * (((zdistD 3 5 (0 : Zd 3 5) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := propUnit2_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0 0 0⟩
```

Ports: none from `../RBM1D` / `../RBM2D` (no file there was read, nothing copied; the RBM1D/RBM2D `git diff --stat` is not applicable).

Narrative (every statement is checkable in the file or in the output above).
- Result: `propUnit1_holds` (U1) and `propUnit2_holds` (U2: mixed and same direction) are proved for every `d Λ κ` in the new file `RBM3D/Propagator/PropUnit.lean`: 4 public declarations (the two pinned `def`s, verbatim from the check file, and the two theorems), 28 private helpers `pu_*`, 5 `example`s. No hypothesis added, no pin or upstream signature changed; the only hypotheses are the pins' own `3 ≤ d`, `0 < Λ`, `0 < κ`.
- `C` is chosen after `(d, Λ, κ)` and before `L, g, t, m, σ₁, σ₂, a, (i,) j`: `max CM (max (4(Λ²+1)3^d) (2 Cs KS))` (U1, file line 755), `... (4 Cs KS)` (U2, line 834), `KS = pu_KS Λ cs q`, `q = d-1` resp. `d`. It depends only on the merged constants `CK, cK` (`kProd_diff1_le` / `kProd_diff2_le`, `d`), `CG, cG` (`kProd_gap`, `d`), `C_A` (`lg_convA`, `(d, Λ)`), `Cs, cs` (`prop5Short_holds`, `(d, Λ, κ)`).
- Branch `σ₁ = σ₂` (every `t ∈ [0,1)`; `κ ≤ Im m` is used only here, through `prop5Short_holds`): triangle inequality, then per point `pu_S_bound`: `1_{x=0} ≤ 3^q(Λ²+1)(g²+e)⁻¹(n+1)^{-q}` (`x = 0 ⇒ n ≤ 2`), `g² ≤ Λ²(Λ²+1)(g²+e)⁻¹`, `e^{-c|x|} ≤ e^{2c}e^{-cn}` (`|a| ≤ |x| + 2`, `pu_shift`), `(n+1)^q e^{-cn} ≤ q!(2/c)^q e^{c/2}` (`pu_pow_exp_le`).
- Branch `σ₁ ≠ σ₂`, `t = 0`: `Θ_0 = 1` (`pu_Theta_zero`); the difference is `0` unless a shifted point is `0`, which forces `n ≤ 2` (`pu_ne_zero`); `pu_t0_bound`.
- Branch `σ₁ ≠ σ₂`, `0 < t < 1`: `PropSpin m σ₁ * PropSpin m σ₂ = 1` (`pu_spin_ne`); `Theta_eq_laplace_prod` and `integral_comp_mul_left_Ioi` give `Θ_t(0,x) = γ⁻¹ ∫₀^∞ e^{-ετ} K_τ(x) dτ`, `ε = (1-t)/γ` (`pu_Theta_eq`), so the unit differences are `γ⁻¹ |∫ e^{-ετ} ΔK_τ|` (`pu_diff1_eq`, `pu_diff2_eq`). `pu_int_bound` splits at `L²`: head `e^{-ετ}|ΔK_τ| ≤ CK · lgIntegrand m cK n ε τ` (`m = d+1` resp. `d+2`; `kProd_diff1_le` / `kProd_diff2_le`), tail `e^{-ετ}|ΔK_τ| ≤ CG L^{-m} e^{-ετ-cGτ/L²}` (`kProd_gap`, conjunct 2 resp. 3). `pu_head`: `n = 0` by `lg_zero`, `n ≥ 1` by `lg_bulk`, each for `ε < 1` and `ε ≥ 1`, with `lg_convA`. `pu_tail`: `lg_tail`, `n ≤ dL/2` (`pu_zdistD_two_le`). `pu_master` glues them with `m = p + 2`. `3 ≤ d` enters as `3 ≤ m`, `2 ≤ p` (`omega`) and as the hypothesis of `prop5Short_holds`.
- Integrability of each `e^{-ετ}K_τ(x)` on `(0,∞)` follows from continuity (`pu_kProd_cont`: `fun_prop` on the finite Fourier sum `hkT`) and `0 ≤ K_τ ≤ 1` (`hkT_mass`); integrability of the difference is the first conclusion of `pu_int_bound`.
- Private copies re-proved because the upstream versions are `private` (grep and `#check` in (c)): continuity, `0 ≤ K ≤ 1` and integrability of `kProd` (`HeatProduct.lean:943, 946, 1064`), a variant of `lg_pow_exp_le` (`LaplaceGauss.lean:574`), nonnegativity of `lgIntegrand` (`LaplaceGauss.lean:496`). Nothing is shared with T2023's file.
- Instances: besides the ticket's two (`a = 0`, `σ₁ ≠ σ₂`, `ε = 10/9 ≥ 1`), three more cover `σ₁ = σ₂ = true` (`μ = I² = -1`) at `a = (1,0,0) ≠ 0`, the branch `t = 0` at `a = (-1,0,0)`, and the mixed direction `(i,j) = (0,2)`; every deterministic hypothesis is discharged by `norm_num` / `Complex.norm_I`.
- Lints: the only warnings of the new file are the 100-character limit on file lines 37 and 59, the pinned text kept verbatim.

## (c) Verified Mathlib names used
Each name was resolved by a script (`#where`: `realizeGlobalConstWithInfos` + `env.getModuleIdxFor?` on the built module, run Sat Oct  3 04:53:23 UTC 2026); one line per defining module; every name is used in `PropUnit.lean`, which compiles (b):
`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`: `MeasureTheory.integral_comp_mul_left_Ioi`
`Mathlib/MeasureTheory/Integral/ExpDecay.lean`: `exp_neg_integrableOn_Ioi`
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`: `MeasureTheory.integral_sub`, `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul`, `MeasureTheory.norm_integral_le_of_norm_le`
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`: `MeasureTheory.setIntegral_union`, `MeasureTheory.setIntegral_mono_set`, `MeasureTheory.setIntegral_congr_fun`
`Mathlib/Order/Interval/Set/LinearOrder.lean`: `Set.Ioc_union_Ioi_eq_Ioi`
`Mathlib/Order/Interval/Set/Disjoint.lean`: `Set.Ioc_disjoint_Ioi_same`
`Mathlib/Order/Interval/Set/Basic.lean`: `Set.Ioc_subset_Ioi_self`
`Mathlib/MeasureTheory/Integral/IntegrableOn.lean`: `MeasureTheory.IntegrableOn.union`, `MeasureTheory.IntegrableOn.mono_set`
`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`: `MeasureTheory.Integrable.sub`, `MeasureTheory.Integrable.mono'`, `MeasureTheory.Integrable.const_mul`
`Mathlib/MeasureTheory/Measure/Restrict.lean`: `MeasureTheory.ae_restrict_iff'`, `MeasureTheory.ae_restrict_mem`
`Mathlib/Analysis/Complex/Exponential.lean`: `Real.pow_div_factorial_le_exp`, `Real.exp_le_one_iff`, `Real.exp_le_exp`
`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`: `Real.rpow_neg`, `Real.rpow_natCast`
`Mathlib/Analysis/Normed/Group/Real.lean`: `Real.norm_of_nonneg`
`Mathlib/Analysis/Complex/Basic.lean`: `Complex.mul_conj'`
`Mathlib/Analysis/Complex/Norm.lean`: `Complex.norm_real`
`Mathlib/Basic/Complex/Basic.lean`: `Complex.ofReal_sub`
`Mathlib/Data/Matrix/Diagonal.lean`: `Matrix.one_apply`
`Mathlib/Data/ZMod/Basic.lean`: `ZMod.val_one_eq_one_mod`
`Mathlib/Algebra/Order/GroupWithZero/Basic.lean`: `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `div_le_div_iff₀`, `div_le_div_iff_of_pos_right`, `le_div_iff₀`, `div_le_iff₀`
`Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`: `Finset.prod_le_one₀`
`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`: `Finset.single_le_sum`
`Init.Data.Nat.Basic`: `Nat.eq_zero_or_pos`
`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`: `Finset.sum_eq_single`
`Mathlib/Algebra/Notation/Pi/Basic.lean`: `Pi.single_eq_of_ne`
`Mathlib/Algebra/Group/Defs.lean`: `add_neg_cancel_right`
Names verified absent as accessible declarations (upstream `private`, re-proved here as private copies); `lake env lean absent.lean`, run Sat Oct  3 04:53:27 UTC 2026:
```
$ grep -n '^private lemma \(kProd_continuous\|kProd_nonneg_le_one\|phi_integrable\|lg_pow_exp_le\|lg_integrand_nonneg\)' RBM3D/Propagator/{HeatProduct,LaplaceGauss}.lean | cut -c1-72
RBM3D/Propagator/HeatProduct.lean:943:private lemma kProd_continuous (a 
RBM3D/Propagator/HeatProduct.lean:946:private lemma kProd_nonneg_le_one 
RBM3D/Propagator/HeatProduct.lean:1064:private lemma phi_integrable {γ e
RBM3D/Propagator/LaplaceGauss.lean:496:private lemma lg_integrand_nonneg
RBM3D/Propagator/LaplaceGauss.lean:574:private lemma lg_pow_exp_le {c : 
$ #check @RBM.Heat.<each of the five names>
absent.lean:2:8: error(lean.unknownIdentifier): Unknown identifier `RBM.Heat.kProd_continuous`
absent.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `RBM.Heat.kProd_nonneg_le_one`
absent.lean:4:8: error(lean.unknownIdentifier): Unknown identifier `RBM.Heat.phi_integrable`
absent.lean:5:8: error(lean.unknownIdentifier): Unknown identifier `RBM.Heat.lg_pow_exp_le`
absent.lean:6:8: error(lean.unknownIdentifier): Unknown identifier `RBM.Heat.lg_integrand_nonneg`
```

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2024a`, … not needed): the unit pins are internal to route H; no statement was changed or weakened.
- Hub, at merge: add `import RBM3D.Propagator.PropUnit` after the last `import` line of `RBM3D.lean` (not in this commit, which holds only the sole writable file; (b) shows the full `lake build` passing `#assert_rbm_axioms` with that line). `RBM3D/Test/Axioms.lean` was not touched.
- For PT-G: both theorems are `∀ d Λ κ`, constants before `L g t m σ₁ σ₂ a (i) j`; the bulk condition `κ ≤ Im m` is used only for `σ₁ = σ₂` and idle for `σ₁ ≠ σ₂`, as pinned; `d - 1` is ℕ-subtraction, harmless for `d ≥ 3`.
- The constants are explicit and not optimised (`q!`-type factors from `pu_pow_exp_le`, `C_A = 3 + 4dΛ² + 2Λ²` from `lg_convA`).
- If T2023's file needs the same helpers (`pu_kProd_cont`, `pu_int_K`, `pu_pow_exp_le`, …), it keeps its own private copy (ticket line 9); consolidation is for the later G ticket.
