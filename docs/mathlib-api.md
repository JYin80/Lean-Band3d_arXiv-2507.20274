# 已核实的 Mathlib API

Mathlib `v4.34.0`，rev `5ed2965256430c3649e86755f9576b54eca72435`。
源码在 `../RBM1D/.lake/packages/mathlib/Mathlib/`。

**规矩**（`CLAUDE.md` 规则 3）：用到一个没在这张表上的 Mathlib 名字，
先 grep 或 `#check @foo` 核实签名，然后**把它记到这里**。版本漂移是这类项目最大的时间黑洞，
这张表就是用来把「查过一次」变成「所有人都不用再查」。

记的时候写清楚：**完整名字、签名要点、实例要求、用在哪**。

## 矩阵

| 名字 | 要点 |
|---|---|
| `Matrix.circulant` | `[Sub n] (v : n → α) : Matrix n n α`，`circulant v i j = v (i - j)`。`Fin d → ZMod L` 经 `Pi` 实例满足 `Sub`。 |
| `Matrix.circulant_isSymm_iff` | 要 `[SubtractionMonoid n]`；`(circulant v).IsSymm ↔ ∀ i, v (-i) = v i`。 |
| `Matrix.submatrix_mul_equiv` | 平移不变性用它把 `submatrix e e` 穿过乘法。 |
| `Matrix.submatrix_one_equiv` | `(1 : Matrix _ _ _).submatrix e e = 1`。 |
| `Matrix.linfty_opNNNorm_def` | `ℓ^∞` 算子范数 = 行和的 `sup`。`norm_SB` 走这条。 |

## 环与逆

| 名字 | 要点 |
|---|---|
| `Ring.inverse` | **传播子用它，不要用 `Matrix.inv`**——后者会拖进行列式与可逆性实例。 |
| `Ring.inverse_mul_cancel` / `Ring.mul_inverse_cancel` | 要 `IsUnit`。 |
| `Units.oneSub` / `Units.val_oneSub` | `‖x‖ < 1` ⇒ `IsUnit (1 - x)`，赋范环里。 |
| `NormedRing.inverse_one_sub` | Neumann 级数 `(1-x)⁻¹ = ∑ xᵏ`，要 `‖x‖ < 1`。 |

## ZMod

| 名字 | 要点 |
|---|---|
| `ZMod.val_lt` | 要 `[NeZero n]`。 |
| `ZMod.val_add` | `(a+b).val = (a.val+b.val) % n`，要 `[NeZero n]`。 |
| `ZMod.neg_val` | `(-a).val = if a = 0 then 0 else n - a.val`，要 `[NeZero n]`。 |
| `ZMod.val_eq_zero` | `a.val = 0 ↔ a = 0`。**不叫** `val_eq_zero_iff_eq_zero`（我一开始写错过）。 |
| `CharP.cast_eq_zero_iff` | 证 `(1 : ZMod L) ≠ 0`、`(2 : ZMod L) ≠ 0` 用它，配 `3 ≤ L`。 |

## Finset 求和

| 名字 | 要点 |
|---|---|
| `Finset.single_le_sum` | 非负项里单项 ≤ 总和。隐参数顺序见 `Analysis/CStarAlgebra/Module/Constructions.lean:278` 的用法。 |
| `Finset.sum_add_distrib` | 存在（Finset 版），但 grep `theorem sum_add_distrib` 找不到声明行，只能看调用处。 |
| `Fintype.sum_equiv (Equiv.subLeft a)` | 把 `∑_b f (a - b)` 换成 `∑_u f u`，行和引理靠它。 |
| `Finset.prod_le_prod` | ⚠️ 有两个同名重载；要非负实数版的话是 **`prod_le_prod₀`**（RBM1D 踩过）。 |

## 求导（Q23，`Propagator/Deriv.lean` 全部核实过）

| 名字 | 要点 |
|---|---|
| `NormedRing.inverse_continuousAt` | `Ring.inverse` 在单位处连续，参数是 `u : Mˣ`。 |
| `hasDerivAt_iff_tendsto_slope` | 把 `HasDerivAt` 换成差商沿 `𝓝[≠] x` 的极限。 |
| `slope_def_field` | `slope f a b = (f b - f a)/(b - a)`。 |
| `eventually_nhdsWithin_of_eventually_nhds` | 把 `∀ᶠ in 𝓝` 降成 `∀ᶠ in 𝓝[≠]`。 |
| `self_mem_nhdsWithin` | `{x}ᶜ ∈ 𝓝[≠] x`，配 `sub_ne_zero_of_ne` 得 `ζ - ξ ≠ 0`。 |
| `HasDerivAt.mul_const` | 在 `Mathlib.Analysis.Calculus.Deriv.Mul`，**Deriv.Basic 里没有**。 |
| `HasDerivAt.comp` | 在 `Mathlib.Analysis.Calculus.Deriv.Comp`，`x` 是显式参数。 |
| `HasDerivAt.comp_ofReal` | 在 `Mathlib.Analysis.Complex.RealDeriv`：`HasDerivAt e e' ↑z → HasDerivAt (fun y : ℝ => e ↑y) e' z`。ℝ→ℂ 的复合走它最省事。 |
| `ContinuousLinearMap.hasDerivAt` | 在 `Deriv.Linear`；没 import 那个文件时 `f.hasDerivAt` 会报「environment does not contain」。 |

**踩到的坑（重要）**：`HasDerivAt` 是 `def`（会展开成 `HasFDerivAtFilter`），
所以点记号 `h.mul_const`、`h.scomp` 在**该引理所在文件没被 import** 时，
报的不是「unknown constant」而是
「Invalid field `mul_const`: The environment does not contain `HasFDerivAtFilter.mul_const`」——
**这条信息会把人引到错误的方向**（去找 `HasFDerivAtFilter` 的引理），
实际要做的是补 import。写成显式的 `HasDerivAt.mul_const h c` 才会报出真正的
「Unknown constant」。

## 已知的坑

* `if_neg` 在这版 Mathlib 里**已 deprecated**，提示用 `ite_eq_right`。只是 warning，不是 error。
* `simp only [foo]` 对一个 `def` 能否展开，取决于是否生成了 equation lemma；不行就用 `unfold foo` 或 `show`。
* `show` 若改变了目标会触发 style linter，要用 `change`（Q1 里 `Propagator/Basic.lean` 就改了两处）。
