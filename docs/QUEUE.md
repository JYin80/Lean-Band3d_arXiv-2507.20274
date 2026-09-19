# 工单队列 · RBM3D

> **这是 Claude Code 的工作入口。** 每次开工：从上往下找第一条 `OPEN` 的工单，
> 把它改成 `CLAIMED`（单独提交这一行），做完改 `DONE` 并在 `docs/STATUS.md` 记一笔。
> 规则见 `CLAUDE.md`：不留 `sorry`，不发明 Mathlib 名字，每次回报前必须有一次 `exit=0`。
>
> 队列由 Cowork 侧维护，约每 10 分钟刷新一次。已被认领的工单不会被改写。

最后刷新：2026-09-19 · beat 0

| # | 工单 | 文件 | 状态 |
|---|---|---|---|
| Q1 | 让现有草稿编译通过 | 全部 | **DONE** (CC；`./check.sh` 待 T0) |
| Q2 | 邻居计数 `#{x : \|x\| = 1} = 2d` | `Defs/Block.lean` | BLOCKED by Q1 |
| Q3 | `‖S^(B)(g)‖ = 1` | `Defs/Block.lean` | BLOCKED by Q2 |
| Q4 | `S^(B) 1 = 1` | `Defs/Block.lean` | BLOCKED by Q2 |
| Q5 | 性质 4 的 `(∞→∞)` 范数界 | `Propagator/Props4.lean` | BLOCKED by Q3,Q4 |
| Q6 | 图模型 · case 分析穷尽性 ⭐ | `Graph/Model.lean` | **CLAIMED** (CC) |
| Q7 | 核对 `[yang2024Del]` B.10 的一个记号 | — | OPEN（需要查文献，非 Lean） |

---

## Q1 · 让现有草稿编译通过 — **DONE**（CC，2026-09-19）

> **完成记录**：按 import 顺序逐文件编译，9 个文件 + `RBM3D.lean` 全部 exit=0，
> **零 error、零 warning、零 sorry**。`#assert_rbm_axioms` 通过：136 条声明，
> 只有 `interfaceAxioms` 那 5 条，各被依赖 1 次。
> 重写后的 `Propagator/Basic.lean`（RBM1D 移植）一次编过；唯一改动是两处 `show` → `change`
> （lint：`show` 改变了目标）。之前 T1 的 import 修正已在 `3c07bc8` 里。
> **编译方式**：`.lake` 还不存在（T0），所以没用 `lake`，而是直调 v4.34.0 的 `lean`，
> `LEAN_PATH` 只读借用 `../RBM1D/.lake/packages/*/.lake/build/lib/lean`。
> **验收里的 `./check.sh` 那一步要等 T0**，届时应直接绿。

**文件**：`RBM3D/` 下全部 `.lean`。
**背景**：这批文件是 Cowork 在没有编译器的情况下写的，**一行都没编译过**。
所有 Mathlib 名字都 grep 过 `../RBM1D/.lake/packages/mathlib/` 确认存在，但签名没验。

**做法**：按 import 顺序逐文件 `lake env lean RBM3D/Xxx.lean`：

```
Defs/Lattice → Defs/Params → Defs/Block → Defs/Domination
  → Propagator/Basic → Propagator/Interface → Graph/ScalingOrder → Test/Axioms
```

每修好一个就单独提交。**不要攒一大坨再一起编译。**

**已知高风险点，按可疑程度排序**：

1. **`Propagator/Interface.lean` 的 `haveI : NeZero L := ⟨by omega⟩`**
   写在 axiom 陈述的 binder 之后、Prop 主体之前，`by omega` 要用上下文里的 `hL : 3 ≤ L`。
   若 elaboration 不认，改成把 `NeZero L` 提成 instance binder。
2. **`Graph/ScalingOrder.lean` 的 `simp only [ord]`** —— `ord` 是 `def`，能否展开取决于
   equation lemma。不行就换 `unfold ord` 或 `show`。
3. **`Defs/Lattice.lean` 的 `Finset.single_le_sum`** —— 用法照抄自 Mathlib 内部调用
   （`Analysis/CStarAlgebra/Module/Constructions.lean:278`），隐参数顺序没验。
4. **`Defs/Lattice.lean` 的 `if_neg`** —— 这版 Mathlib 里已 deprecated（提示用
   `ite_eq_right`）。只是 warning，可顺手换掉。
5. **`Defs/Block.lean` 的 `circulant_isSymm_iff`** —— 要求 `[SubtractionMonoid n]`，
   `Fin d → ZMod L` 经 `Pi` 实例应当满足，没验过。
6. **`Propagator/Basic.lean` 的 `noncomm_ring` 那几步** —— 整段是从
   `RBM1D/Propagator/Basic.lean` 逐行移植的（那边已编译通过），只把 `SB L` 换成
   `SB d L g`、`ZMod L` 换成 `Zd d L`、`norm_SB L hL` 换成假设 `hS`。
   **所以这个文件的可疑度其实最低**，出错多半在 `Zd d L` 的实例推断上。
7. **`Test/Axioms.lean`** —— `collectAxioms` 与 `MessageData.joinSep` 照抄 RBM1D（已验），
   `env.find?` 的 match 分支是新写的。

**验收**：`./check.sh` → `errors: 0`、`exit=0`，且 `#assert_rbm_axioms` 只报出
`interfaceAxioms` 里那 5 条。

---

## Q2 · 邻居计数 `#{x : Zd d L | zdistD d L x = 1} = 2 * d` — BLOCKED by Q1

**文件**：`RBM3D/Defs/Block.lean`（或新开 `Defs/Neighbours.lean`）。

**这是整层的地基**：`Propagator/Basic.lean` 里每条结构引理都带着假设
`hS : ‖SB d L g‖ = 1`，而那条界最终归结到这个计数。Q3、Q4、Q5 全压在它上面。
**做完这一条，传播子那一层立刻全部解除假设。**

**陈述**（建议）：

```lean
theorem card_nbhd (d L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1).card = 2 * d
```

**证法**：与 `Fin d × Bool` 之间建双射——`(i, b) ↦ Pi.single i (if b then 1 else -1)`。
需要的三件事：

* `zdistD d L (Pi.single i u) = zdist L u`（单点支撑，其余坐标为 0）；
* `zdist L 1 = 1` 与 `zdist L (-1) = 1`，都需要 `3 ≤ L`
  （`RBM1D/Defs/Dist.lean` 的 `zdist_one_le` / `zdist_neg_one_le` 是同一件事，去抄）；
* 单射性：`1 ≠ -1` in `ZMod L` 需要 `3 ≤ L`——这正是 `L ≤ 2` 时定理失效的原因
  （`L = 2` 时 `1 = -1`，邻居塌成 `d` 个）。`RBM1D/Defs/Block.lean` 的
  `one_ne_zero_zmod` / `two_ne_zero_zmod` 可直接搬。

反过来还要证：`zdistD d L x = 1` 蕴含 `x` 形如 `Pi.single i u` 且 `zdist L u = 1`
（和为 1 的自然数族恰有一项为 1）。

---

## Q3 · `‖S^(B)(g)‖ = 1` — BLOCKED by Q2

**文件**：`RBM3D/Defs/Block.lean`。

**直接移植 `RBM1D/Propagator/Basic.lean` 的 `section Norm`**（五条，已编译通过）：

```
nnnorm_sbKernel → sum_nnnorm_sbKernel → sum_nnnorm_SB_row → nnnorm_SB → norm_SB
```

只有两处不同：

* 核的取值不是常数 `1/3`，而是 `(1+2dg²)⁻¹` 与 `g²(1+2dg²)⁻¹` 两档，
  所以 `nnnorm_sbKernel` 要分三种情形。两个值都 `≥ 0`（`g > 0`），`positivity` 能下。
* 求和用 Q2 的计数：`(1+2dg²)⁻¹ + 2d · g²(1+2dg²)⁻¹ = 1`，`field_simp` + `ring` 收尾。

**产出**：`theorem norm_SB (d L : ℕ) [NeZero L] (g : ℝ) (hg : 0 < g) (hL : 3 ≤ L) :
‖SB d L g‖ = 1`，它就是 `Propagator/Basic.lean` 里那个 `hS`。

---

## Q4 · `S^(B) 1 = 1` — BLOCKED by Q2

**文件**：`RBM3D/Defs/Block.lean`。
移植 `RBM1D/Defs/Block.lean` 的 `sum_SB_row` / `SB_mulVec_one`，同样用 Q2 的计数。
行和那一步用 `Fintype.sum_equiv (Equiv.subLeft a)` 把 `Σ_b SB a b` 换成 `Σ_u sbKernel u`。

**产出**：`Propagator/Basic.lean` 里 `Theta_mulVec_one` / `sum_Theta_row` 的假设 `hone`。

---

## Q5 · 性质 4 的 `(∞→∞)` 范数界 — BLOCKED by Q3,Q4

**文件**：新开 `RBM3D/Propagator/Props4.lean`。

论文 A.1 的两步，**两步都已经有料**：

1. `|Θ_{t,ab}^{(σ₁,σ₂)}| ≤ Θ_{t,ab}^{(+,-)}`：逐项比较 Neumann 级数
   `Theta_eq_tsum`（已在 `Propagator/Basic.lean` 里证好）。
2. `‖Θ_t‖_{∞→∞} ≤ (1-t)⁻¹`：由 1 与 `sum_Theta_row`（ξ = t，`|m|=1`）。

注意随机带矩阵模型下 `M^(σ₁,σ₂) = m(σ₁)m(σ₂) I` 且 `|m(σ)| = 1`，所以
`ξ = t·m(σ₁)m(σ₂)` 满足 `‖ξ‖ = t < 1`，而 `Θ^{(+,-)}` 对应 `ξ = t·|m|² = t` 是实的。

---

## Q6 · 图模型与 case 分析穷尽性 ⭐ — **OPEN，与 Q1 无关，可并行**

**文件**：新开 `RBM3D/Graph/Model.lean`。
**这是本项目机器检查收益最高的一块**，而且**不依赖传播子那一层，现在就能动**。

**背景**：第三轮人工校对在附录 B 的 `lem_scalingorder` 发现漏掉一种情形 case (vi)。
但它的算术与 case (iv) 完全相同——`ord_case_vi` 在 Lean 里就是 `ord_case_iv` 的推论
（见 `Graph/ScalingOrder.lean`）。**只检查算术的形式化抓不到它**，漏的是情形枚举。

**要建的最小结构**：足以表达那个 case 分析的构型。权展开作用在
`G_{β₁α}`、`G_{wβ₂}`、`G_{αw}` 三条边上，分类依据是

* 这三条边各自「对角 / 非对角」；
* `β₁ = β₂` 与否。

把它做成一个归纳类型（或 `structure` + 判定），让 `cases` 的穷尽性由编译器保证，
每个构造子调用 `Graph/ScalingOrder.lean` 里已证好的算术引理
（`ord_case_ii`…`ord_case_vi`）。

**验收标准**：删掉 `ord_case_vi` 的那一个分支，编译器应当报 non-exhaustive。
能做到这一点，这个项目就在数学上有了第三轮人工校对没有的保证。

---

## Q7 · 核对 `[yang2024Del]` Lemma B.10 的一个记号 — **OPEN（查文献，非 Lean）**

附录 B 的三条 expansion 引理要写成 axiom，**陈述错了编译器查不出来**，
所以必须在 `Graph/Expansions.lean` 落地之前核清楚。要确认的就一个符号：

* 本文 `eq:BE`（Lemma B.9）第一项写的是 `Ǧ_ββ G_αy`（`ββ` 带 check，`αy` 不带）；
* 本文 `eq:LW`（Lemma B.10）括号内对应的第一项写的是 `Ǧ_αy Ǧ_ββ`（**两个都带 check**）。

若 `eq:LW` 的内层括号本应是 `eq:BE` 右端把 `x` 换成 `y`，则 `Ǧ_αy` 处多了一个 check。
**要查**：`[yang2024Del]` Lemma B.10 那一项到底是 `G_αy` 还是 `Ǧ_αy`。
（作者已答复说「合作者查过，完全一样」，但没说是哪一个版本，所以落地前仍需确认。）
