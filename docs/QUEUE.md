# 工单队列 · RBM3D

> **这是 Claude Code 的工作入口。** 每次开工：从上往下找第一条 `OPEN` 的工单，
> 把它改成 `CLAIMED`（单独提交这一行），做完改 `DONE` 并在 `docs/STATUS.md` 记一笔。
> 规则见 `CLAUDE.md`：不留 `sorry`，不发明 Mathlib 名字，每次回报前必须有一次 `exit=0`。
>
> 队列由 Cowork 侧维护，约每 10 分钟刷新一次。已被认领的工单不会被改写。
>
> **工单编号不许两边各编各的。** beat 11 撞过一次：Cowork 侧在 beat 10 开了 Q23–Q27，
> CC 在同一时间把 Q17b 的后续也叫成 Q26，表里于是出现两条 Q26，下一个领单的人会领错。
> **从此分号段：CC 自己开的工单从 Q28 往上顺排，Cowork 侧开的工单从 Q40 起。**
> 号段分开，两边都不必先同步就能开单。
>
> **两份蓝图的分工**：`blueprint/src/content.tex`（leanblueprint，CC 维护）是**机器可核的进度**——
> `\lean{}` 指向真实声明、`\leanok` 与提交同步、`\uses` 组成依赖图。
> `blueprint/cowork/`（Cowork 维护，发布成给作者看的网页）是**叙事与队列快照**。
> **两边都别去改对方那一份**；不一致时以 `content.tex` 为准，Cowork 负责把差异反映到网页上。

最后刷新：2026-09-20 · beat 14（**Q22a 完成 —— `KTwoFormula` 从假设变成定理**；Q22b 认领中，是最后一个大件）

| # | 工单 | 文件 | 状态 |
|---|---|---|---|
| Q1 | 让现有草稿编译通过 | 全部 | **DONE** (CC；`./check.sh` 待 T0) |
| Q2 | 邻居计数 `#{x : \|x\| = 1} = 2d` | `Defs/Neighbours.lean` | **DONE** (CC) |
| Q3 | `‖S^(B)(g)‖ = 1` | `Defs/Block.lean` | **DONE** (CC) |
| Q4 | `S^(B) 1 = 1` | `Defs/Block.lean` | **DONE** (CC) |
| Q5 | 性质 4 的 `(∞→∞)` 范数界 | `Propagator/Props4.lean` | **DONE** (CC) |
| Q6 | 图模型 · case 分析穷尽性 ⭐ | `Graph/Model.lean` | **DONE** (CC) |
| Q7 | 核对 `[yang2024Del]` B.10 的一个记号 | — | 降级（不在关键路径） |
| Q8 | `(Owx)` / `(Oe2x)` 的确定性内核 | `Graph/Expansions.lean` | **DONE**（选 B：不写 axiom） |
| Q9 | 演化核 `U^(n)` 与 `lem:sum_Ndecay` | `Kernel/Evolution.lean` | **DONE** (CC) |
| Q10 | 尾函数 `𝒯_t` / `wT^ℓ_{t,D}` | `Defs/Tail.lean` | **DONE** (CC) |
| Q11 | `lem:propT` 卷积界 `TTT2` | `Kernel/PropT.lean` | **DONE** (CC) |
| Q12 | `claim:TTk`（`eq:TtTt` / `eq:KtKt`） | `Kernel/PropT.lean` | **DONE** (CC)；求和版另开 Q20 |
| Q13 | `lem:sum_decay_nonzero`（`Q^(A)` · `I_diff(σ)`） | `Kernel/Evolution.lean` | **DONE** (CC) |
| Q14 | 典范树划分 `TSP(P_a)` 与边值 | `Loop/Partition.lean` | **DONE** (CC) |
| Q15 | 树表示 `eq_Ktree`（`[YY_25]` Lem 3.4） | `Loop/TreeRep.lean` | **DONE** (CC)：陈述层落地，`eq_Ktree` 按假设；移植 → Q22 |
| Q16 | `lem_pureloop` 同号 `K`-loop 的指数衰减 | `Loop/PureLoop.lean` | **PARTIAL** (CC)：`n = 2` + 工具；一般 `n` → Q25 |
| Q17a | `eq:latticesum_d3`（第三轮新加的那条） | `Kernel/SumDecay.lean` | **DONE** (CC)：不依赖任何接口假设 |
| Q17b | `lem:sum_decay` 本体（`sum_res_1` / `sum_res_2`） | `Kernel/SumDecay.lean` | **PARTIAL** (CC)：两块零件已证；三条结论 → **Q28** |
| Q18 | 让审计直接报定理数与公理承重情况 | `Test/Axioms.lean` | **DONE** (CC)：283 定理 / 132 定义 / 0 公理 |
| Q19 | **把 5 条接口 axiom 改成 `structure` 字段** ⭐ | `Propagator/Interface.lean` | **DONE** (CC)：全项目零公理 |
| Q20 | `(eq:key_T_reudce)` 求和版（带 `≺`） | `Kernel/PropT.lean` | **PARTIAL** (CC)：确定性不等式已证；`Ψ²ℓ² ≺ (W^dη)⁻¹` 的吸收 → Q29 |
| Q23 | **传播子对 `t` 的求导层** ⭐ —— **主线第一步** | `Propagator/Deriv.lean` | **DONE** (CC)：4 条 + `t`-形式；Q27 解锁 |
| Q27 | **证出 `KTwoFormula`（`(Kn2sol)`）** ⭐ —— 主线第二步 | `Loop/Primitive.lean` | **DONE** (CC)：存在性 (Q27) + 唯一性 (Q22a) ⇒ `KTwoFormula` 是定理 |
| Q22a | **Grönwall 唯一性**（250 行）—— 主线第三步 | `Loop/Unique.lean` | **DONE** (CC)：唯一性 + **`KTwoFormula` 已消** |
| Q22b | 树公式 = 存在性（真正的大件）—— 主线第四步 | `Loop/TreeRep*.lean` | **PARTIAL** (CC)：`n = 3` 已证（`Loop/TreeThree.lean`）；`n = 4` → Q30，一般 `n` → Q31 |
| Q24 | `ML:Kbound` —— 论文说「需额外修改以处理 `d ≥ 3`」 ⭐ | `Loop/KBound.lean` | **OPEN**（R1 转正） |
| Q25 | `lem_pureloop` 的一般 `n` | `Loop/PureLoop.lean` | **OPEN**（CC 于 Q16 开出） |
| Q26 | **审计自动发现借用谓词 + 分两本账** ⭐ | `Test/Axioms.lean` | **OPEN**（范围已扩：见下方 beat 14 补充） |
| Q29 | `(eq:key_T_reudce)` 的 `≺` 吸收步 | `Kernel/PropT.lean` | **OPEN**（CC 于 Q20 开出） |
| Q28 | `lem:sum_decay` 的三条结论（`sum_res_1` / `(I)` / `(II)`） | `Kernel/SumDecay.lean` | **OPEN**（CC 于 Q17b 开出；原叫 Q26，撞号已改） |
| Q30 | `(eq_Ktree)` 的 `n = 4`（第一次出现内部边） | `Loop/TreeFour.lean` | **OPEN**（CC 于 Q22b 开出） |
| Q31 | `(eq_Ktree)` 的一般 `n`（`polyVal` 递归上做归纳） | `Loop/TreeRepGeneral.lean` | **OPEN**（CC 于 Q22b 开出；需 Q30） |
| Q40 | **依赖图：分开「借来的」与「暂时假设的」，并修一条错边** ⭐ | `blueprint/src/content.tex` | **OPEN**（Cowork 提；不动 Lean 代码） |
| Q41 | **每条假设的「非空洞」证书**（固定 `L` 版） ⭐ | `Test/InterfaceShape.lean` | **OPEN**（Cowork 提；beat 6 那类缺陷的正面检查） |
| Q21 | **逐字核对剩下四条接口陈述** ⭐ | `Propagator/Interface.lean` | **DONE** (CC)：1 条修正 + 1 条反例 |

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

## Q2 · 邻居计数 `#{x : Zd d L | zdistD d L x = 1} = 2 * d` — **DONE**（CC，2026-09-19）

> **完成记录**：新文件 `RBM3D/Defs/Neighbours.lean`（只 import `Defs/Lattice`；**`Block.lean` 没动**，
> Q3/Q4 用时在 `Block.lean` 里加 `import RBM3D.Defs.Neighbours`）。零 error / 零 warning / 零 sorry，审计干净。
>
> 给 Q3/Q4 用的签名（已编译验证）：
>
> ```lean
> theorem card_nbhd (d L : ℕ) [NeZero L] (hL : 3 ≤ L) :
>     (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1).card = 2 * d
> theorem card_adj (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (a : Zd d L) :
>     (Finset.univ.filter fun b : Zd d L => Adj d L a b).card = 2 * d
> ```
>
> 顺带落地、Q3 可能用到的：`zdist_eq_one_iff : zdist L u = 1 ↔ u = 1 ∨ u = -1`、
> `one_ne_neg_one_of_three_le`、`zdist_one`、`zdist_neg_one`、`zdistD_single`
> （`zdistD (Pi.single i u) = zdist u`）、`unitVec`（`(i, b) ↦ ±eᵢ`）及其单射性、
> `filter_zdistD_eq_one`（单位球 = `unitVec` 的像）。另加了 `Decidable (Adj d L x y)` 实例。
> 证法按工单：与 `Fin d × Bool` 的单射；反方向用 `Finset.add_sum_erase` + `Finset.sum_eq_zero_iff`
> 得「和为 1 的自然数族恰有一项为 1」。没用 RBM1D 的引理（一维部分直接从 `ZMod.val` 算）。


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

## Q3 · `‖S^(B)(g)‖ = 1` — **DONE**（CC，2026-09-19）

> **完成记录**（Q3、Q4 一起做，同一文件 `Defs/Block.lean` 末尾的 `section Stochastic`）：
>
> ```lean
> theorem norm_SB (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) : ‖SB d L g‖ = 1
> theorem SB_mulVec_one (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) :
>     SB d L g *ᵥ (1 : Zd d L → ℂ) = 1
> ```
>
> **与工单签名的唯一差别：`norm_SB` 没有 `hg : 0 < g`。** 两档核值 `(1+2dg²)⁻¹`、`g²(1+2dg²)⁻¹`
> 对任意实数 `g` 都非负，用不上这个假设，所以陈述更强。调用处写 `norm_SB d L g hL`。
>
> **已实测**：`Theta_mul d L g (norm_SB d L g hL) hξ` 与
> `sum_Theta_row d L g (norm_SB d L g hL) (SB_mulVec_one d L g hL) hξ a` 都能编过——
> 即 `Propagator/Basic.lean` 的 `hS`、`hone` 可以在任何调用处直接消掉（范数是同一个
> `Matrix.Norms.Operator` 的 `ℓ^∞` 算子范数）。`Propagator/Basic.lean` 本身**没改**，
> 那些假设仍在陈述里；要不要把它们从陈述中拿掉由 Cowork 定。
>
> 做法：没照搬 RBM1D 的 `nnnorm_sbKernel` 三情形，而是把核写成实值非负函数
> `sbKernelR = a·1_{x=0} + b·1_{|x|=1}`（`sbKernel_eq_ofReal`、`sbKernelR_nonneg`），
> 总质量 `sum_sbKernelR : a + 2d·b = 1` 由 `card_nbhd` + `field_simp` 得到；
> 于是 `sum_sbKernel`（Q4）和 `sum_norm_sbKernel`（Q3）是同一个计算的两个推论。
> 之后按 RBM1D 的链：`sum_SB_row` / `sum_norm_SB_row`（`Equiv.subLeft`）→ `sum_nnnorm_SB_row`
> → `nnnorm_SB`（`linfty_opNNNorm_def`）→ `norm_SB`。
> 全库 294 条声明，零 error / 零 warning / 零 sorry，审计干净。


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

## Q4 · `S^(B) 1 = 1` — **DONE**（CC，2026-09-19；见 Q3 的完成记录）

**文件**：`RBM3D/Defs/Block.lean`。
移植 `RBM1D/Defs/Block.lean` 的 `sum_SB_row` / `SB_mulVec_one`，同样用 Q2 的计数。
行和那一步用 `Fintype.sum_equiv (Equiv.subLeft a)` 把 `Σ_b SB a b` 换成 `Σ_u sbKernel u`。

**产出**：`Propagator/Basic.lean` 里 `Theta_mulVec_one` / `sum_Theta_row` 的假设 `hone`。

---

## Q5 · 性质 4 的 `(∞→∞)` 范数界 — **DONE**（CC，2026-09-19）

> **完成记录**：新文件 `RBM3D/Propagator/Props4.lean`（已加进 `RBM3D.lean`），零 error / 零 warning /
> 零 sorry，全库 320 条声明，审计干净。约定：`Θ_t^(σ₁,σ₂) = Theta d L g (t·m)`，`‖m‖ = 1`；
> `Θ_t^(+,-) = Theta d L g t`。
>
> ```lean
> theorem norm_Theta_apply_le (hL : 3 ≤ L) (ht0 : 0 ≤ t) (ht1 : t < 1) (hm : ‖m‖ = 1) (a b) :
>     ‖Theta d L g ((t : ℂ) * m) a b‖ ≤ (Theta d L g t a b).re      -- |Θ^(σ₁,σ₂)_ab| ≤ Θ^(+,-)_ab
> theorem Theta_real_eq / Theta_real_nonneg                         -- Θ^(+,-) 是实的、非负
> theorem sum_Theta_real_row : ∑ b, (Theta d L g t a b).re = (1 - t)⁻¹
> theorem norm_Theta_le (hL) (ht0) (ht1) (hm) :
>     ‖Theta d L g ((t : ℂ) * m)‖ ≤ (1 - t)⁻¹                       -- (eq:THETAinftinf)，ℓ^∞ 算子范数
> ```
>
> 证法按论文 A.1：`S^(B)` 是非负实矩阵 `SBR` 的复化（`SB_eq_map_SBR`、`SB_pow_eq_map`、
> `SBR_pow_nonneg`），所以 Taylor 级数第 `k` 项的 `(a,b)` 元是 `ξ^k (SBR^k)_ab`（`Theta_apply_eq_tsum`）；
> 逐项取范数（`norm_tsum_le_tsum_norm`）得第一条，加上行和得第二条。
>
> **顺手消掉 `hS` / `hone`**（工单要求）：同文件 `section Unconditional` 给出无假设版本，全部只要 `hL : 3 ≤ L`——
> `Theta_mul_of_three_le`、`mul_Theta_of_three_le`、`Theta_transpose_of_three_le`（性质 1）、
> `Theta_apply_add_right_of_three_le`（性质 2）、`Theta_commute_SB_of_three_le`、`Theta_commute_of_three_le`（性质 3）、
> `sum_Theta_row_of_three_le`、`Theta_eq_tsum_of_three_le`。`Propagator/Basic.lean` 本身未改。
> 至此 `lem_propTH` 性质 1–4 全部是定理（Phase 1 完成标准第 3 条的前半）。


> Q3、Q4 都已落地，所以 `Propagator/Basic.lean` 里那两个假设 `hS` 与 `hone` 现在都能
> 直接由 `norm_SB` / `SB_mulVec_one` 供上。**顺手把那一层的假设消掉**：整个文件的结构
> 引理都是带着 `hS` 证的，现在可以给出无假设的推论版本。

**文件**：新开 `RBM3D/Propagator/Props4.lean`。

论文 A.1 的两步，**两步都已经有料**：

1. `|Θ_{t,ab}^{(σ₁,σ₂)}| ≤ Θ_{t,ab}^{(+,-)}`：逐项比较 Neumann 级数
   `Theta_eq_tsum`（已在 `Propagator/Basic.lean` 里证好）。
2. `‖Θ_t‖_{∞→∞} ≤ (1-t)⁻¹`：由 1 与 `sum_Theta_row`（ξ = t，`|m|=1`）。

注意随机带矩阵模型下 `M^(σ₁,σ₂) = m(σ₁)m(σ₂) I` 且 `|m(σ)| = 1`，所以
`ξ = t·m(σ₁)m(σ₂)` 满足 `‖ξ‖ = t < 1`，而 `Θ^{(+,-)}` 对应 `ξ = t·|m|² = t` 是实的。

---

## Q6 · 图模型与 case 分析穷尽性 ⭐ — **DONE**（CC，2026-09-19）

> **完成记录**：`RBM3D/Graph/Model.lean`，编译通过（零 error / 零 warning / 零 sorry），审计干净。
>
> * **模型**：一个构型 = `β₁ — α — w — β₂ — β₁` 这个 4-环上的等号模式
>   （`e₁ = G_{β₁α}`、`e₂ = G_{wβ₂}`、`e₃ = G_{αw}` 各自是否对角，加 `β₁ = β₂` 与否），`Pattern`，共 16 种。
> * `Pattern.of_realizable`：等号可传递，4-环上不可能恰好三处相等 → 只有 12 种可实现
>   （`card_realizable`，`decide` 验证）。
> * `Pattern.classify`：**一个 `match`** 把 12 种分到论文的 (i)–(vi)，4 种不可实现的用可实现性排除。
> * `classify_eq_{i..vi}_iff`：每个 case 恰好刻画为论文描述它时用的顶点（不）等式——
>   比如 `classify α w β₁ β₂ = .vi ↔ α = w ∧ β₁ ≠ α ∧ w ≠ β₂`。所以这些 case 就是论文的 case，不是重新编号。
> * `ord_weight_step`：任一构型下 `ord` 至少升 `Case.gain ≥ 1`，经 `Case.ord_ge` 调用 `ord_case_ii..vi`。
>
> **验收（已实测）**：删掉 `=> .vi` 那一行，Lean 报
> `Missing cases: (mk false false true false), (mk false false true true)`——正好是 case (vi) 的两种模式。
> 把 (vi) 冒充成「不可实现」（`absurd h (by decide)`）同样编不过。`classify_vi_occurs` 给出具体见证
> （`Fin 3` 上 `α = w = 0, β₁ = 1, β₂ = 2`）。
>
> **范围说明**：`Case.Rel` 里各 case 的计数关系（`n_W, n_V, n_S`）照抄论文，**本身未被推导**——
> 那需要完整的图（分子、light-weight、dotted-edge 划分），不在最小模型里。case (i) 论文只给了结论
> `ord(𝒢₁) ≥ ord(𝒢₀)+1`，`Rel .i` 就原样记这个。`n_lw / n_dv` 的记账（`eq:relateG1G0`）也未建模。
> 所以 Lean 保证的是：**情形枚举完整** + **每个 case 的算术**；不保证每个 case 的计数关系本身正确。
> 陈述没有偏离论文，未记 `paper-deltas.md`。


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

## Q7 · 核对 `[yang2024Del]` Lemma B.10 的一个记号 — 降级，不再阻塞

beat 1 的查证，三条：

**一、它不在关键路径上。** `eq:LW`（`lem_lweight`）是**块 Anderson 模型**那一套的权展开，
写在附录 B 的 BA 工具箱里。全文**没有任何 `\eqref{eq:LW}` 或 `\Cref{lem_lweight}`**——
它一次都没被引用过。随机带矩阵那条线上真正用的权展开是 `(Owx)`，GG 展开是 `(Oe2x)`；
`Graph/Model.lean` 的 case 分析就建在 `(Owx)` 的第三项上。而按 `docs/paper-deltas.md` D6，
本项目目前只覆盖随机带矩阵模型。**所以 `Graph/Expansions.lean` 先要写的是 `(Owx)` 和
`(Oe2x)`，不是 B.9 / B.10** —— 见 Q8。

**二、文献没查到。** `yang2024Del` = arXiv:2501.08608（Yang–Yin，*Delocalization of a
general class of random block Schrödinger operators*）。arXiv 的 HTML 版与 ar5iv 都只返回
摘要和导航，取不到附录 B；PDF 也不在这台机器上（`3D_Band` 与 `Lean_proof` 下都没有）。

**三、数学上 `Ǧ_αy` 很可能本来就是对的，不是笔误。** `\Gc = \mathring G = G − M` 是中心化的
G，而 B.10 的前因子 `(1 + M⁺S⁺)`（`M⁺_{xy} = M_{xy}M_{yx}`）正是把 B.9 递归求和起来的那个
几何级数——**权展开的意义就在于这次重求和把 `G_{αy}` 的确定性部分 `M_{αy}` 吸收掉，剩下
`Ǧ_{αy}`**。若真如此，B.9 写 `G_αy` 而 B.10 写 `Ǧ_αy` 恰恰是对的，合作者说「完全一样」
也就说得通了。

**这是待确认的假说，不是结论。** 谁手上有 2501.08608 的 PDF，翻到 Lemma B.10，只需回答
一个字：括号内第一项那个 `(α,y)` 因子，是 `G` 还是 `Ǧ`。

## Q8 · `(Owx)` 与 `(Oe2x)` 的确定性内核 — **DONE**（选 B）

> ### 拍板（Cowork，beat 2）：**选 B，不写这两条 axiom。工单就此关闭。**
>
> 三条理由，第三条是关键：
>
> 1. **(1)(2)(4) 正是规则 6 划出去的随机层。** 为了陈述两条引理去建概率空间、预解式和
>    Wirtinger 导数，等于把 Phase 1 明确排除的东西建起来，只为写两句自己无法验证的话。
> 2. **PLAN 的风险表里已经点名了这一条**：「接口公理写错，编译器查不出来」。而这两条恰好是
>    风险最高的样本——`S^±` 相对 `[yang2021delocalization]` 有一个**有意的** `m²` 归一化差
>    （`paper-deltas.md` D9.3），外加 `S` vs `S_t = tS` 的替换。写错了没有任何机制会报警。
> 3. **这里「假设」严格优于「公理」。** 证明真正用到的不是那两个 `=_𝔼` 恒等式本身，而是它们
>    产生的构型与计数关系——而这些 `Graph/Model.lean` 已经用 `Case.Rel` 作为**显式假设**带着了。
>    假设出现在每条定理的类型里，调用处一眼可见；公理躲在 `#print axioms` 里。
>    所以 B 不是「做不到只好放弃」，是**在这个位置假设本来就是更诚实的形式**。
>    将来 `ScalingOrder` 需要 `eq:GGraisesord` 时，按同样的原则处理：作为假设，不作为公理。
>
> `interfaceAxioms` 保持 5 条不变。蓝图里 `(Owx)`/`(Oe2x)` 作为灰色「仅在蓝图」节点，
> 依赖边指向 `Expansions.lean` 的导数引理与 `Model.lean`。
>
> **CC 的出处更正已采纳**：两条出自 `[yang2021delocalization]` Lemma 3.5 / 3.14，
> 不是我工单里写的 `[yang2024Del]`。已记入 `paper-deltas.md` D10。



> **结论：按工单「前置比预期深就别硬撑」，两条 axiom 没有写。** 落地的是它们的确定性内核。
>
> **一、先更正出处。** 论文把两条都归给 **`[yang2021delocalization]`**：`(Owx)` 是其 Lemma 3.5，
> `(Oe2x)` 是其 Lemma 3.14（`7_8_light_weight.tex` L293、L334），不是 `[yang2024Del]`。
> 它们在 §7 开头，前面还有一句：原文是对 `G = (H−z)⁻¹` 陈述的，这里把 `G, S` 换成 `G_t, S_t = tS` 使用。
>
> **二、卡在哪。** 两条都是 `=_𝔼`（期望相等）的恒等式，对「`G` 的任意可微函数 `f`」成立。
> 要逐字陈述，至少需要：
> (1) `N × N` 随机带矩阵 `H` 及其分布（概率空间、方差矩阵 `S`、Hermitian 约束）；
> (2) 预解式 `G(z)`、`m(z)`、`Ǧ = G − M`；
> (3) `S^±`，按**本文**归一化（与原文差 `m²`，见 `paper-deltas.md` D9.3）；
> (4) `∂_{h_{αx}}`：Hermitian 矩阵元上的 Wirtinger 导数；
> (5) `f` 的取值范围和可积性（「可微函数」在 Lean 里要给出一个具体类，比如 `G` 的矩阵元多项式）。
> 仓库里这些**一样都没有**；(1)(2)(4) 正是 CLAUDE.md 规则 6 说 Phase 1 不碰的随机层。
> 没有它们，写出来的 axiom 要么是空话（量词范围不对），要么写错了归一化还查不出来——
> 这正是 PLAN 风险表里「接口公理写错，编译器查不出来」那一条。
>
> **三、落地了什么**（`RBM3D/Graph/Expansions.lean`，**无 axiom**，零 error / 零 warning / 零 sorry，全库 323 条，审计不变）：
>
> ```lean
> theorem hasDerivAt_inverse_apply (hA : IsUnit A) (α w i j : n) :
>     HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w 1) i j)
>       (-(Ring.inverse A i α * Ring.inverse A w j)) 0     -- ∂_{h_{αw}} G_{ij} = −G_{iα} G_{wj}
> theorem hasDerivAt_inverse_sub_apply ...                  -- 对 light-weight Ǧ = G − M 同样成立
> ```
>
> 这就是 `(Owx)` 第三项里 `∂_{h_{αw}}` 打到 `G_{β₁β₂}`（或 `Ǧ_{β₁β₂}`）时产生 `G_{β₁α} G_{wβ₂}` 的那一步，
> 加上前因子 `G_{αw}`，正好是 `Graph/Model.lean` 分类的三条新边 `e₁, e₂, e₃`。所以现在
> 「展开产生哪三条边」（本文件）和「这三条边有哪些对角构型、各升多少阶」（`Model.lean`）都有编译器检查；
> 中间只剩「期望恒等式本身」没进 Lean。
> 注：这里的导数是沿矩阵单位 `E_{αw}` 的方向导数，也就是把 `h_{αw}`、`h_{wα}` 当作独立变量的
> Wirtinger 导数——文献里的 `∂_{h_{αw}}` 正是这个约定。
>
> **四、三个选项（请 Jun / Cowork 拍板）**：
> * **A. 建最小随机层，再写两条 axiom。** 按上面 (1)–(5) 建模，`f` 取 `G` 矩阵元的多项式。
>   工作量大，而且要突破规则 6；归一化（`S` vs `S_t`、`S^±` 的 `m²`）是主要写错风险。
> * **B.（推荐，Phase 1）不写 axiom**，蓝图里这两条作为灰色「仅在蓝图」节点，
>   依赖边指向 `Expansions.lean` 的导数引理和 `Model.lean`。借用边界照样诚实可见，
>   只是不进 `interfaceAxioms`。
> * **C. 在图模型层面写一条抽象 axiom**（比如「第三项产生的图恰好是这些构型」）。
>   **不推荐**：那已经是由论文引理推出来的推论，不是逐字的论文陈述，违反规则 4。
>
> `interfaceAxioms` 与 `paper-deltas.md` 本次**都没改**（没有新增 axiom）。


**文件**：新开 `RBM3D/Graph/Expansions.lean`。这是 Q7 的真正替代品。

`Graph/Model.lean` 现在是自足的：它只谈构型与计数，没有陈述展开式本身。要把它接到论文上，
得把随机带矩阵线上实际用到的两条展开写成接口公理：

* **`(Owx)`** 权展开 —— `Graph/Model.lean` 的 case 分析建在它第三项上；
* **`(Oe2x)`** GG 展开 —— `Graph/ScalingOrder.lean` 的 `eq:GGraisesord` 引用它。

两条都引自 `[yang2024Del]`，所以都是 `axiom`，**落地时必须同时加进
`Test/Axioms.lean` 的 `interfaceAxioms` 并在 `docs/paper-deltas.md` 记一条**。

**开工前先定建模深度。** 这两条是关于 `f(G)` 的恒等式，要陈述就得有「可微的 G 的函数」
和 `∂_{h_{βα}}` 这些对象。照 `Model.lean` 的先例：**先只建到能被编译器检查的那一层**，
不要一上来就建完整的图代数。如果发现陈述它们需要的前置比预期深，就在 STATUS.md 里写清楚
卡在哪，别硬撑。


---

# 第二批：附录 A（确定性估计）

论文里这一章是**本文自足**的推导——以 `lem_propTH` 为输入，往上盖。Q9 现在就能开工，
它只用到刚证好的性质 4。**Q9 与 Q10 文件不相交，可以两个人同时做。**

## Q9 · 演化核 `U^(n)` 与 `lem:sum_Ndecay` — **DONE**（CC，2026-09-19）

> **完成记录**：新文件 `RBM3D/Kernel/Evolution.lean`（已加进 `RBM3D.lean`），**不依赖任何接口公理**，
> 零 error / 零 warning / 零 sorry；全库 338 条声明，审计干净。
>
> **定义**（签名入参 `m : Fin n → ℂ`，`m i = m(σ_i)`，`‖m i‖ = 1`；张量 `A : (Fin n → Zd d L) → ℂ`）：
> `cycProd m i = m i * m (finRotate n i)`（即 `μ_i = m(σ_i)m(σ_{i+1})`，循环约定）；
> `thetaKer μ t = (μ • SB) * Θ_{tμ}`；`uKer μ s t = (1 − (sμ) • SB) * Θ_{tμ}`；
> `ThetaN`（`def:op_thn`，用 `Function.update a i b` 表示 `a^(i)(b_i)`）；`UN`（`def_Ustz`）。
> 按工单复用 `Theta`，没有另起炉灶。
>
> **定理**：
>
> ```lean
> theorem uKer_eq_one_add (hL) (hξ : ‖(t:ℂ) * μ‖ < 1) :                     -- (eq:decompUalt)
>     uKer d L g μ s t = 1 + (((t:ℂ) - s) * μ) • (SB d L g * Theta d L g ((t:ℂ) * μ))
> theorem norm_Xi_le (hL) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (hμ : ‖μ‖ = 1) :  -- (Xi_infint)
>     ‖(((t:ℂ) - s) * μ) • (SB d L g * Theta d L g ((t:ℂ) * μ))‖ ≤ (t - s) / (1 - t)
> theorem norm_uKer_le ... : ‖uKer d L g μ s t‖ ≤ (1 - s) / (1 - t)
> theorem norm_UN_le (hL) (hm : ∀ i, ‖m i‖ = 1) (hs) (hst) (ht) (A) :           -- (sum_res_Ndecay)
>     ‖UN d L g m s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖
> ```
>
> `‖A‖` 就是 Mathlib 在函数类型上的 sup 范数 `max_a |A_a|`；`‖·‖_{∞→∞}` 是 `ℓ^∞` 算子范数。
> `(Xi_infint)` 的第二个不等号用的正是 Q5 的 `norm_Theta_le`。
> **积的那一步没有对 `n` 归纳**：`∏_i Σ_c |K_i(a_i,c)| = Σ_b ∏_i |K_i(a_i,b_i)|` 就是
> `Finset.prod_univ_sum`，一行。论文要求 `n ≥ 2`，这里对所有 `n` 成立（陈述更强，不算偏离）。
> 另有辅助引理 `sum_norm_row_le`（行和 ≤ `ℓ^∞` 算子范数），Q13 大概用得上。


**文件**：新开 `RBM3D/Kernel/Evolution.lean`。**只依赖 Q5（性质 4），不需要任何接口公理。**

要定义的（`\Cref{DefTHUST}`）：张量 `A : (Zd d L)^n → ℂ`、它的 `‖A‖_∞ = max_a |A_a|`，以及

* `(def:op_thn)` `(Θ^(n)_{t,σ} ∘ A)_a = Σ_i Σ_{b_i} (M^(σ_i,σ_{i+1}) S^(B) / (1 − t M^(σ_i,σ_{i+1}) S^(B)))_{a_i b_i} · A_{a^(i)(b_i)}`，
  其中 `a^(i)(b_i) := (a_1,…,a_{i-1}, b_i, a_{i+1},…,a_n)`，并约定 `σ_{n+1} = σ_1`；
* `(def_Ustz)` `(U^(n)_{s,t,σ} ∘ A)_a = Σ_b ∏_{i=1}^n ((1 − s M^(σ_i,σ_{i+1}) S^(B)) / (1 − t M^(σ_i,σ_{i+1}) S^(B)))_{a_i b_i} · A_b`。

**随机带矩阵模型下 `M^(σ_i,σ_{i+1}) = m(σ_i)m(σ_{i+1}) I`，所以那个分式就是
`(1 − s ξ_i S^(B))·Θ_{t,ξ_i}`，其中 `ξ_i = t·m(σ_i)m(σ_{i+1})`** —— 直接复用
`Propagator/Basic.lean` 的 `Theta`，不要另起炉灶。

要证的三条，按顺序：

1. **`(eq:decompUalt)`**：`(1 − s M S)/(1 − t M S) = 1 + Ξ^(i)`，其中 `Ξ^(i) := (t−s)·M S·Θ_t`。
   纯代数恒等式，用 `Theta_mul` / `mul_Theta` 展开即可。
2. **`(Xi_infint)`**：`‖Ξ^(i)‖_{∞→∞} = max_a Σ_b |Ξ^(i)_{ab}| ≤ (t−s)·‖Θ_t‖_{∞→∞} ≤ (t−s)/(1−t)`。
   **第二个不等号就是 Q5 刚证好的 `norm_Theta_le`。**
3. **`(sum_res_Ndecay)` = `lem:sum_Ndecay`**：`‖U^(n)_{s,t,σ} ∘ A‖_∞ ≤ ((1−s)/(1−t))^n ‖A‖_∞`。
   由 1、2 得单个因子的 `(∞→∞)` 范数 `≤ 1 + (t−s)/(1−t) = (1−s)/(1−t)`，再对 `n` 个因子取积。

**提示**：`n` 个指标上的张量用 `(Fin n → Zd d L) → ℂ`；`U^(n)` 是 `n` 个同一算子在不同指标上的
张量积，所以「积的范数 ≤ 范数的积」那一步建议先对 `n` 归纳，别一上来就找 Mathlib 的张量积 API。

## Q10 · 尾函数 `𝒯_t` 与 `wT^ℓ_{t,D}` — **DONE**（CC，2026-09-19）

> **完成记录**：新文件 `RBM3D/Defs/Tail.lean`（只依赖 `Defs/Params.lean`），零 error / 零 warning / 零 sorry；
> 全库 361 条声明，审计干净。
>
> **定义**：`BparamR d L g t (r : ℝ)`——`B_{t,r}` 取实数自变量（`𝒯_t` 要在 `r ∧ ℓ` 处取值，`ℓ` 是实数），
> `BparamR_natCast` 证明它在自然数处等于 `Bparam`；`tailT d L g t r = BparamR r * exp(−√(r/ℓ_t))`（`defTUL`）；
> `tailW d L g t ℓ W D r = max (tailT (min r ℓ)) (W ^ (−D))`（`defWTTlD`，`W^{-D}` 用 `Real.rpow`）。
> 平方根沿用 `Params.lean` 的 `Real.sqrt` 约定。
>
> **性质**：`tailT_nonneg`、`tailT_zero : 𝒯_t(0) = B_{t,0}`、`tailT_antitone`（`[0,∞)` 上单调不增，
> 两个因子分别单调：`BparamR_antitone`、指数因子）；`rpow_neg_le_tailW`、`tailW_pos : 0 < W → 0 < wT`、
> `tailW_antitone`（要 `0 ≤ ℓ`）。
>
> **L325 那句话，拆成两条带显式常数的引理**：
>
> ```lean
> theorem zeroMode_le_of_ge (hd : 2 ≤ d) (hL : 1 ≤ L) (ht : t < 1) (hr0 : 0 ≤ r) (hrL : r ≤ L)
>     (hgt : g²/L² ≤ 1 - t) :
>     (L^d |1-t|)⁻¹ ≤ 2^(d-1) * ((g² + |1-t|)⁻¹ * ((r+1)^(d-2))⁻¹)      -- 零模项被衰减项压住
> theorem ellT_eq_of_le (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ L) (h : 1 - t ≤ g²/L²) : ℓ_t = L
> theorem exp_tail_ge ... (hrL : r ≤ L) : exp(-1) ≤ exp(-√(r/ℓ_t))    -- 指数因子是常数阶
> ```
>
> 论文只说「压住」「常数阶」，常数 `2^{d-1}`、`e⁻¹` 是论证实际给出的。`exp_tail_ge` 不需要 `0 ≤ r`（比论文强）。
> `ellT_eq_of_le` 需要 `g ≥ 0`，论文里 `g > 0` 是默认的。


**文件**：新开 `RBM3D/Defs/Tail.lean`。只依赖 `Defs/Params.lean` 的 `Bparam` / `ellT`。

`\Cref{def: TTfunc}`：

* `(defTUL)` `𝒯_t(r) := B_{t,r} · exp(−(r/ℓ_t)^{1/2})`，`r ≥ 0`；
* `(defWTTlD)` `wT^ℓ_{t,D}(r) := max(𝒯_t(r ∧ ℓ), W^{-D})`，`0 ≤ ℓ ≤ L`。

要证的基本性质（论文正文里当作显然，形式化必须写出来）：

* `𝒯_t` 关于 `r` 单调不增 —— 注意 `B_{t,r}` 的第一项 `(g²+|1−t|)⁻¹/(r+1)^{d-2}` 单调减、
  第二项 `(L^d|1−t|)⁻¹` 是常数，指数因子也单调减；
* 非负性、`𝒯_t(0) = B_{t,0}`；
* `wT` 单调不增、`≥ W^{-D} > 0`（后面所有除以 `wT` 的地方都要它非零）；
* 论文 L325 那句话：`0 ≤ r ≤ L` 时，`1−t ≥ g²/L²` 则 `B_{t,r}` 的第二项被第一项压住，
  反之则反过来 —— **这条在第三轮我补 `eq:MG_conclusion2` 的理由时用到了，值得单独成引理。**

## Q11 · `lem:propT` 的卷积界 — **DONE**（CC，2026-09-19）

> **完成记录**：`(TTT2)` 完整证明，**两个区制都做了，常数全部显式，没有 `≲`**。零 error / 零 warning / 零 sorry，
> 不依赖接口公理；全库 434 条声明，审计干净。
>
> ```lean
> theorem propT (k : ℕ) :                                 -- d = k + 2
>     ∃ C > 0, ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
>       (g²/L² ≤ 1 - t ∨ 1 - u ≤ g²/L²) →                    -- 区制 (i) ∨ 区制 (ii)
>       ∀ a b, Σ_c 𝒯_u(|a−c|) 𝒯_t(|c−b|) ≤ C/(1−u) · 𝒯_t(|a−b|)
> ```
>
> `C = constI k + constII k` 只依赖 `d`。分区制的版本是 `propT_i`、`propT_ii`（`Kernel/PropT.lean`）。
> 证明链上的文件：`Defs/Shells.lean`（K0）→ `Defs/RadialSum.lean`（K2）→ `Defs/Convolution.lean`（K3）→ `Kernel/PropT.lean`（K4/K5）。
>
> **与论文证明的两处差别**（都不改陈述）：
> 1. 论文 A.3 第二步引的是一条 `ℝ^d` 上的「基本微积分事实」，没有证明；这里换成它的格点版 `sum_conv_le`，
>    完整证明，靠 `√` 的次可加性 `sqrt_add_sqrt_sub_ge`。
> 2. L325 那句「`0 ≤ r ≤ L` 时零模项被压住」，在 ℓ¹ 环面距离下不够用：`|x|` 最大到 `dL/2`，不止 `L`。
>    所以用推广版 `zeroMode_le_of_ge_mul`（`r ≤ mL`，常数 `2(2m)^{d-2}`）；区制 (ii) 的下界同理，
>    用 `E_L(r) ≥ e^{−√d}`（`r ≤ dL`）。常数吸收了这些，陈述不变。
>
> **附带**：证明从头到尾没用 `d ≥ 3`，结论对 `d ≥ 2` 都成立。陈述里多了 `0 < g`——论文的默认假设。
>
> 原拆解计划（保留作记录）：


> **CC 的拆解计划**（论文 A.3 两步都是 `≲`，第二步还用了一条只在 `ℝ^d` 上陈述的「基本微积分事实」，
> 下面是离散化之后、能直接在 `Z_L^d` 上证的路线；`|x| = zdistD`，即 ℓ¹ 环面距离）：
>
> * **K0 球壳计数** ✅ `Defs/Shells.lean`：`card_sphere_le : #{x ∈ Z_L^{d+1} : |x| = r} ≤ 2^{d+1}(r+1)^d`
>   （一维：距离 `= r` 的点至多 2 个、`≤ r` 的至多 `2r+1` 个；再按 `Fin.consEquiv` 对 `d` 归纳）。
> * **K2 径向和** ✅ `Defs/RadialSum.lean`：`sum_radial_exp_le : Σ_{x ∈ Z_L^{k+2}} (|x|+1)^{-k} e^{-κ√(|x|/ℓ)} ≤ 2^{k+2}·C(κ)·ℓ²`，
>   `C(κ) = 32(1+720/κ⁶)`（`ℓ ≥ 1`，`κ > 0`）。逐项用 `e^y ≥ y⁶/6!` 把 `(r+1)e^{-κ√(r/ℓ)}` 压到 `C ℓ³/((ℓ+r)(ℓ+r+1))`，再用望远镜和，**不需要积分比较**。
>   原计划：`Σ_x (|x|+1)^{-(d-2)} e^{-κ√(|x|/ℓ)} ≤ C_d ℓ²`（`ℓ ≥ 1`，`d ≥ 3`）。按球壳求和后，
>   化成一维的 `Σ_r (r+1) e^{-κ√(r/ℓ)} ≲ ℓ²`。取 `ℓ = L` 时指数因子 `≥ e^{-κ√d}`，也就给出区制 (ii) 要的 `Σ_x (|x|+1)^{-(d-2)} ≲ L²`。
> * **K3 卷积拆分** ✅ `Defs/Convolution.lean`：`sum_conv_le : Σ_c P(a−c)E_{ℓ₁}(a−c)·P(c−b)E_{ℓ₂}(c−b) ≤ C·ℓ₁²·P(a−b)E_{ℓ₂}(a−b)`，
>   对任意 `1 ≤ ℓ₁ ≤ ℓ₂` 成立（`P(x) = (|x|+1)^{-(d-2)}`，`E_ℓ(x) = e^{-√(|x|/ℓ)}`，`C = 2^{2d-1}·C(2−√2)`）。
>   两个区制都直接用它：(i) 取 `ℓ₁ = ℓ_u`、`ℓ₂ = ℓ_t`；(ii) 取 `ℓ₁ = ℓ₂ = L`。关键引理 `sqrt_add_sqrt_sub_ge`：
>   `r ≤ p+q ⟹ √(p/ℓ₁) + √(q/ℓ₂) − √(r/ℓ₂) ≥ (2−√2)√(min(p,q)/ℓ₁)`。
>   原计划：K3 卷积拆分（那条「微积分事实」的离散版）：设 `X = √|a−c|`、`Y = √|c−b|`、`Z = √|a−b|`。
>   由三角不等式 `Z ≤ √(X²+Y²)` 得 `X + ε(Y − Z) ≥ (2−√2)·min(X, Y)`，对所有 `ε ∈ [0,1]` 成立。
>   再按 `|a−c| ≤ |c−b|` 与否拆成两块：每块里 `(|a−b|+1)/(|c−b|+1) ≤ 2`（或对称的那一个），于是归结到 K2。
> * **K4 区制 (ii)** `1−t ≤ 1−u ≤ g²/L²`：`ℓ_u = ℓ_t = L`，指数因子在 `[e⁻¹, 1]` 之间（Q10 的 `exp_tail_ge`）；
>   把「衰减项 + 零模项」两两相乘，得四个交叉项，逐项用 `L² ≤ g²/(1−u)` 估计。
> * **K5 区制 (i)** `1−u ≥ 1−t ≥ g²/L²`：零模项被衰减项压住（Q10 的 `zeroMode_le_of_ge`），`ℓ_u ≤ ℓ_t`，
>   用 K3（取 `ε = √(ℓ_u/ℓ_t)`），最后 `ℓ_u²/(g²+1−u) ≤ 1/(1−u)`。
>
> 常数 `C_d` 最终是显式的（形如 `2^{O(d)}`）。


**文件**：新开 `RBM3D/Kernel/PropT.lean`。陈述（`TTT2`）：存在只依赖 `d` 的 `C_d > 0`，使得对
任意 `0 ≤ u ≤ t < 1` 满足 (i) `1−u ≥ 1−t ≥ g²/L²` 或 (ii) `1−t ≤ 1−u ≤ g²/L²`，

```
Σ_{c ∈ Z_L^d} 𝒯_u(|a−c|) · 𝒯_t(|c−b|) ≤ C_d/(1−u) · 𝒯_t(|a−b|),   ∀ a,b
```

证明在附录 A.3（`sec:pfpropT`）。**注意两个区制要分开做**，这是 `d ≥ 3` 与低维不同的地方之一。

## Q12 · `claim:TTk`（`eq:TtTt` / `eq:KtKt`） — **DONE**（CC，2026-09-19）

> **完成记录**：`Kernel/PropT.lean` 的 `section TTk`。**这次是真的 `lake build`**（`./check.sh` → `errors: 0`，`exit=0`，
> 451 条声明，审计干净）——磁盘腾出来了，`.lake` 已建好，T0 的阻塞没了。
>
> **两处对工单的订正**（都已按论文原文落地）：
> 1. A.4 用的是 `𝖳_t`（论文宏 `\sT`，`7_8_light_weight.tex` L23），**不是 `𝒯_t`**：
>    `𝖳_t(r) = (g²+|1−t|)^{-1/2} W^{-d/2} (r+1)^{-(d-2)/2} e^{-½√(r/ℓ_t)}`，即 `W^{-d}·(𝒯_t 衰减部分)` 的平方根，不含零模。
>    Lean 里是 `sfT`，半次幂用 `Real.sqrt` 写；`Ψ_t = (W^{-d}B_{t,0})^{1/2}` 是 `PsiT`。
> 2. **`(eq:TtTt)` 带前提 `|x−α| ∨ |y−α| ≤ ℓ`**（原文 "for 1 ≤ i ≤ r" 的适用范围）。没有它结论是假的：
>    `x = y` 且两距离都远大于 `ℓ` 时，右端的 `(|x−α|∧|y−α|+1)^{-(d-2)/2}` 远小于左端。
>
> 落地的声明：`sfT_zero_le_PsiT`（`𝖳_t(0) ≤ Ψ_t`）、`sfT_le_PsiT_mul`（`𝖳_t(r) ≤ Ψ_t (r+1)^{-(d-2)/2}`）、
> `sfT_TtTt`（`(eq:TtTt)`，常数 `2^{(d-2)/2}`，带上面那个前提）、`sfT_KtKt`（`(eq:KtKt)`，常数 1）、
> `sfT_pair_cases`（情形覆盖）、`min_le_add_min`（截断三角不等式）、`sqrt_add_le_add_sqrt`。
>
> **`sfT_pair_cases` 就是工单点名要核的那件事**：每个指标要么落进 `(eq:TtTt)`，要么（必要时交换 `x`、`y`）落进 `(eq:KtKt)`。
> 所以第三轮把 case 2 改成 `2 ≤ i ≤ k`、case 3 改成 `1 ≤ i ≤ k` 是对的——`(eq:TtTt)` 没覆盖的指标必有一个距离超过 `ℓ`，
> 正好是 `(eq:KtKt)` 的前提；原稿的 `3 ≤ i ≤ k` 会漏掉 `i = 2`。
>
> **未做**：求和版 `(eq:key_T_reudce)`（带 `≺`、`ℓ ≤ (log W)^{10} ℓ_t` 与三情形求和）→ **Q20**。


**文件**：同 `Kernel/PropT.lean`。附录 A.4。**这一条要特别小心**：第三轮校对就是在这里发现
原稿漏了截断——两式都必须带 `∧ ℓ`：

```
𝒯_t(|x_i−α| ∧ ℓ) · 𝒯_t(|y_i−α| ∧ ℓ) ≲ 𝒯_t(|x_i−y_i| ∧ ℓ)                      (eq:TtTt)
|y_i−α| > ℓ 时： ≲ 𝒯_t(ℓ) · (W^{-d}B_{t,0})^{1/2} · (|x_i−α| ∧ ℓ + 1)^{-(d-2)/2}   (eq:KtKt)
```

两条都由 `𝒯_t` 的定义、单调性，加上两条初等事实推出：
`𝒯_t(0) ≤ (W^{-d}B_{t,0})^{1/2}` 与 `𝒯_t(r ∧ ℓ) ≤ 𝒯_t(0)·(r ∧ ℓ + 1)^{-(d-2)/2}`。
另外第三轮把 case 2 的适用范围从 `3 ≤ i ≤ k` 改成 `2 ≤ i ≤ k`、case 3 改成 `1 ≤ i ≤ k`
（原稿漏了下标）——**形式化时把这两处当作重点核对对象**。

## Q13 · `lem:sum_decay_nonzero` — **DONE**（CC，2026-09-19）

> **完成记录**：`Kernel/Evolution.lean`。`./check.sh` → `errors: 0`、`exit=0`。主定理：
>
> ```lean
> theorem norm_zeroModeSet_UN_le (hd : 3 ≤ k + 2) (hg : 0 < g) (hm : ∀ i, ‖m i‖ = 1)
>     (hmi : ∀ i, 0 < (m i).im) (hshort : ∀ i, ThetaDecayShort (k+2) g (m i))
>     (hzero : ∀ i, ThetaZeroMode (k+2) g (cycProd m i))
>     (hA : SameSignOutside m A) (hτ : 0 < τ) :
>     ∃ C > 0, ∀ L ≥ 3, ∀ s t, 0 ≤ s → s ≤ t → t < 1 → 1 - s ≤ g²/L² → ∀ 𝒜,
>       ‖Q^(A) ∘ U^(n)_{s,t,σ} ∘ 𝒜‖_∞ ≤ C · L^(n·τ) · ‖𝒜‖_∞
> ```
>
> `≺` 按 `Defs/Interface` 的惯例写成展开式 `∀ τ > 0, ∃ C > 0, … ≤ C L^{nτ}`。
> `SameSignOutside m A`（`∀ i ∉ A, m i = m (i+1)`）就是 `A ⊇ I_diff(σ)`。
>
> **结构部分**（无需接口）：`tensorKer`（任意单指标核族的张量积，`U^(n)` 是其实例）、
> `avgOp`（`P^(i)`）、`zeroModeOp`（`Q^(i)`）、`zeroModeSet`（`Q^(A)`）、
> `projMat`（`Proj_{e^⊥} = I − L^{-d}J`，幂等）；
> `zeroModeOp_tensorKer` / `zeroModeSet_tensorKer`：`Q^(A)` 穿过张量核 = 把 `A` 中那些指标的核左乘 `projMat`；
> `norm_tensorKer_le`：`‖K∘𝒜‖ ≤ (∏‖K_i‖)‖𝒜‖`。
>
> **分析部分**（用接口假设）：`norm_le_sum_row_zero`（平移不变矩阵的范数由一行控制）、
> `projMat_mul_SB_comm`（论文那句「`Proj` 与平移不变的 `M S^(B)` 交换」）、
> **`projMat_mul_Theta : Proj·Θ_ξ = Θ̊_ξ`**（投影就是 `(def_Thxi0)` 的去零模）；
> `exists_norm_uKer_same_le`（`(eq:samecolor)`，用 `(prop:ThfadC_short)` + `sum_radial_exp_decay_le`）、
> `exists_norm_projMat_mul_uKer_le`（`(eq:diffcolor)`，用 `(prop:ThfadC0)` + `sum_radial_pow_le`，
> 并在这里用掉 `1−s ≤ g²/L²`）。最后把 `n` 个单指标界乘起来。
>
> **副产品：接口的一处修正**。接上分析部分时发现 `(prop:ThfadC_short)` 原先对任意单位谱参数陈述，
> 而那在 `σ₁ ≠ σ₂`（谱参数 `1`）时**是假的**——已按论文限定到 `σ₁ = σ₂`（谱参数 `m(σ)²`，`0 < m.im`），
> 并在 `RBM3D/Test/InterfaceShape.lean` 里**机器证明了原写法为假**。见 `docs/paper-deltas.md` D11。


**文件**：`RBM3D/Kernel/Evolution.lean`。附录 A.2 末尾，`sum_res_Ndecay_nonzero`。
第三轮补写的那段推导现在是显式的，照着做即可：由 `(def_Ustz)`，`U^(n)` 在 `n` 个指标上分别作用；
由 `\Cref{def;zero_mode_remove}`，`Q^(A) = ∏_{i∈A} Q^(i)` 把 `i ∈ A` 的因子换成带
`Proj_{e^⊥}` 的形式。第一类因子用那个 `(∞→∞)` 界；第二类因子由假设 `A ⊃ I_diff(σ)` 强制
`σ_i = σ_{i+1}`，从而落在 `(eq:decompUalt)` 的适用范围内。
**需要 `(prop:ThfadC)`（接口公理）作输入。**


---

# 第三批：附录 A.5（`Sec:CalK`，`K`-loop 的树表示）

**先读这一段再动手。** Q8 的教训是：陈述一条引理所需的建模深度，要在开工前判断，不要写到一半
发现前置太深。这一批的三条深度**差别很大**：

* Q14 是纯组合＋已有的 `Theta`，**不碰随机层**；
* Q15 是本文**逐字陈述**的一条引理（归给 `[YY_25]` Lemma 3.4），而且**完全是确定性的**
  （只涉及 `Θ` 传播子与树，没有 `=_𝔼`，没有概率空间）——**所以它和 `(Owx)` 不同，是合格的
  接口公理候选**。更妙的是 RBM1D 已经把它证出来了（见下），所以也可以选择移植而非公理化。
* Q16 是本文**自足证明**的推论。

## Q14 · 典范树划分与边值 — **DONE**（CC，2026-09-19）

> **完成记录**：新文件 `RBM3D/Loop/Partition.lean`，`./check.sh` → `errors: 0`、`exit=0`，不依赖任何接口假设。
>
> **数据结构按工单要求与 RBM1D 一致**（`RBM1D/Loop/Crossing.lean` + `Loop/Tree.lean`）：树用它的**对角线集合**表示，
> `TSP n` 定义为「不交叉的对角线集合」。`def:canpnical_part` 的平面几何**不形式化**——这一点 RBM1D 已经记过，
> 这里沿用同样的建模（见文件的 Modelling 段）。只有索引类型从 `ZMod L` 换成 `Zd d L`，传播子多带一个耦合 `g`。
>
> 落地的内容：
> * 组合层：`IsDiag`、`diagonals`、`Crossing`、`CrossingFree`、`TSP`，以及 `noncrossing_split`（不交叉 ⇒ 可分离）、
>   `isDiag_split_lt`（两块都更小，这是递归终止的理由）；
> * 边值：`thetaEdge`（`(f-external)` 的 `Θ^(σ_k,σ_{k+1})_t`）；内部边 `(Θ − I)` 出现在 `polyVal` 的分裂步里
>   （左块新顶点带 `(Θ − I)ᵀ`、右块带 `I`，合起来正是 `(f-internal)`）；
> * 值：`polyVal`（按对角线递归，终止性已证）、`bdList`、`treeVal`、`treeSum`，
>   以及 **`GammaN`**（`(M-graph-value-unsummed)`，含 `∏_i m(σ_i)` 前因子）与 `GammaSum`（对 `TSP` 求和）。
>
> **自检**：`TSP_three = {∅}`（三角形没有对角线）、`TSP_four = {∅, {(0,2)}, {(1,3)}}`（两条对角线相交，不能共存）、
> `card_TSP_five = 11`（小 Schröder 数 `1, 3, 11, 45`）；
> **验收** `treeVal_four_nil`：`n = 4` 无对角线时树值 = 星图 `Σ_b ∏_i Θ^(σ_i,σ_{i+1})(a_i,b)`。
>
> **Q15 现在可以开工**：`GammaSum` 就是 `eq_Ktree` 右端（差一个 `W^{-d(n-1)}`），
> 而且数据结构与 RBM1D 的 `TreeRep.lean` / `TreeRepGeneral.lean` 对齐，可以考虑移植而不是公理化。


**文件**：新开 `RBM3D/Loop/Partition.lean`。不依赖任何接口公理。

`\Cref{def:canpnical_part}`：`n ≥ 3`，定向多边形 `P_a` 顶点 `a = (a_1,…,a_n)` 按逆时针循环排列
（约定 `a_i = a_j ⟺ i ≡ j mod n`）。典范划分把它分成若干多边形子区域，满足：

* 边与子区域一一对应：每条边 `(a_{k-1}, a_k)` 恰属于一个子区域 `R_k`，每个子区域恰含一条多边形边；
* 每个顶点 `a_k` 恰属于两个区域 `R_k` 与 `R_{k+1}`（约定 `R_{n+1} = R_1`）。

**去掉多边形的 `n` 条边后，剩下的内部边构成一棵树，叶子是多边形的顶点。** 这棵树就是
`Γ ∈ TSP(P_a)`，论文明确说**把它当抽象树结构而非等价类**——形式化时照此办理。
恰含一个外顶点 `a_k` 的边叫**外部边**，连接两个内顶点的叫**内部边**。
给定 `σ ∈ {+,-}^n`，区域 `R_k` 带电荷 `σ_k`（即边 `(a_{k-1},a_k)` 的电荷）。

边值（`f-external` 起）：外部边 `e = (a_k, b)` 夹在 `R_k` 与 `R_{k+1}` 之间时
`f_{t,σ}(e) := Θ^(σ_k,σ_{k+1})_t(a_k, b)`。内部边的取值见论文同一处，一并抄下来。
再由边值定义 `Γ^(n)_{t,σ,a}`。

**开工前先看 RBM1D**：`Loop/Tree.lean`、`Loop/TreeRep.lean`（729 行）、
`Loop/TreeRepGeneral.lean`（2546 行）都已编译通过，索引类型是它的 `LoopIdx`。
**树的表示方式直接沿用那边的**，别自己重新设计——Q15 要移植的话，数据结构一致才移植得动。

## Q15 · 树表示 `eq_Ktree` — **DONE**（CC，2026-09-19）：陈述层落地，`eq_Ktree` 按假设

> **完成记录**：新文件 `RBM3D/Loop/TreeRep.lean`，`./check.sh` → `errors: 0`、`exit=0`，零 sorry，公理审计仍为空。
>
> **先说评估结论（工单要求的那一步）**：走移植**超过一拍**，所以按工单的备选方案办——
> 陈述层做实，`eq_Ktree` 本身按**假设**（不是 axiom）写，移植另开 **Q22**。理由有两条，第二条是关键：
> 1. RBM1D 那边是 `TreeRep.lean`（729 行，`n ≤ 4`）+ `TreeRepGeneral.lean`（2546 行）；
> 2. **那条路线依赖 RBM3D 还没有的东西**——ODE 唯一性论证要先能对 `t` 求导 `Θ_t`，
>    即 RBM1D 的 `Propagator/Deriv.lean`；本项目的传播子层目前只有代数与范数，没有求导。
>
> **但陈述层不是空壳**：`eq_Ktree` 里的 `K^(n)` 不是随便一个函数，而是被 `\Cref{Def_Ktza}` 唯一确定的对象，
> 所以这次把定义它的东西都做出来了：
> * `LoopIdx`（索引数据，与 RBM1D 同构，标签类型泛化）、`cutGlueL` / `cutGlueR`（`(calGonIND)` 的 cut-and-glue），
>   以及长度与 `WF` 的保持性；特别是 `length_cutGlueL_add_length_cutGlueR`：两段链长之和为 `n + 2`——
>   **这正是 `(pro_dyncalK)` 是二次方程的原因**；
> * `treeEqRhs`：卷积树方程 `(pro_dyncalK)` 的右端（`W^d`，`d` 维权重）；
> * `MLoop`：初值 `(eq:initial_K)`，用论文给出的随机带矩阵简化形式（只形式化 RBM 模型，D6）；
> * `IsKLoop`：`\Cref{Def_Ktza}` 逐条写成谓词（ODE + 初值 + 长度 1 的情形）；
> * `KTreeRep`：`(eq_Ktree)` 作为假设，形状与 `PropTH` 一致，**Q22 落地时可以原地替换、下游签名一字不改**。
>
> **自检** `treeEqRhs_two`：`n = 2` 时由 `cutGlueL/cutGlueR` 生成的右端确实是两回路方程
> `W^d Σ_{a,b} K_{σ,(a₁,a)} S_{ab} K_{σ,(b,a₂)}`——两边的哑指标顺序相反，靠 `S^(B)` 的对称性对上。
> 这是索引层与论文之间的第一道核对。

> **beat 8 更新：移植的路已经铺好了，优先走移植，不要默认公理化。**
> Q14 落地时刻意把 `TSP`（不交叉对角线集合）的表示**与 RBM1D 对齐**，所以
> `RBM1D/Loop/TreeRep.lean`（729 行，已编译）和 `TreeRepGeneral.lean`（2546 行）
> 的证明可以直接借过来，而不是重新推。
>
> 那边的路线再强调一次，因为它是省力的关键：**不做组合双射**，而是证明
> 「树和满足同一个 ODE 且初值相同」，再由解的唯一性收尾
> （`hasDerivAt_kFour` + `kFour_zero` ⇒ `kFour_eq_treeSum`）。
> `TreeRep.lean` 先在 `n ≤ 4` 上把组合讲透（`n = 4` 是第一个出现内部边的情形，
> 「树的边 ↔ `(k,l)` 对」的双射在那里看得最清楚），`TreeRepGeneral.lean` 做一般 `n`。
>
> 现有可复用的（**不要重做，import 即可**）：`Loop/Partition.lean` 的 `TSP`、`thetaEdge`、
> `polyVal` / `treeVal` / `treeSum`、`GammaN`、`GammaSum`，以及自检
> `TSP_three` / `TSP_four` / `card_TSP_five` 和验收 `treeVal_four_nil`。
>
> **若评估下来移植超过一拍的量**，就先按接口假设写（不是 axiom——见 `CLAUDE.md`「接口的形式」），
> 把移植另开一条工单，并在 STATUS 里写清楚理由与卡点。

**文件**：新开 `RBM3D/Loop/TreeRep.lean`。陈述（`\Cref{tree-representation}`，`n ≥ 4`）：

```
K^(n)_{t,σ,a} = W^{-d(n-1)} · Σ_{Γ ∈ TSP(P_a)} Γ^(n)_{t,σ,a}
```

**两条路，开工前先选：**

* **公理化。** 它是本文逐字陈述、归给 `[YY_25]` Lemma 3.4 的引理，且纯确定性——
  符合 D10 的标准，是合格的接口公理。若选这条，**必须同时加进 `Test/Axioms.lean` 的
  `interfaceAxioms` 并在 `paper-deltas.md` 记一条**。
* **移植 RBM1D 的证明（推荐先评估）。** 那边是**真证出来的**，而且路线很省力：
  **不做组合双射，而是证明「树和满足同一个 ODE 且初值相同」，再由解的唯一性收尾**
  （`hasDerivAt_kFour` + `kFour_zero` ⇒ `kFour_eq_treeSum`）。
  `TreeRep.lean` 先在 `n ≤ 4` 上把组合讲透（n=4 是第一个出现内部边的情形，
  「树的边 ↔ `(k,l)` 对」的双射在那里看得最清楚：4 条边界边 + 2 条对角线 对 6 个 `k<l` 对），
  `TreeRepGeneral.lean` 做一般 `n`。
  **先花 15 分钟读那两个文件的 module docstring，再判断移植成本。** 若评估下来超过一拍的量，
  就先公理化、把移植另开一条工单——但要在 STATUS 里写清楚理由。

## Q16 · `lem_pureloop` — **PARTIAL**（CC，2026-09-19）：`n = 2` 与工具已证，一般 `n` → Q25

> **完成记录**：新文件 `RBM3D/Loop/PureLoop.lean`，`./check.sh` → `errors: 0`、`exit=0`、零 sorry。
>
> **证出来的**：
> * `norm_Theta_same_le_exp`：把 `(prop:ThfadC_short)` 化成实际要用的形状 `|Θ^(σ,σ)_t(0,a)| ≤ C e^{-c|a|}`。
>   指示函数 `1_{a=0}` 被吸收进常数——因为 `a = 0` 时 `e^{-c|a|} = 1`，`a ≠ 0` 时它本来就是 0。
> * `sum_exp_decay_conv`：`Σ_y e^{-c|x-y|}e^{-c|y-z|} ≤ C(c,d) e^{-(c/2)|x-z|}`，对 `L` 一致。
>   **一半衰减付给三角不等式，另一半付给对 `y` 求和**——这是一般 `n` 归纳里每次分裂都要用的那一步。
> * `pureLoop_two`：`res_pureKes` 在 `n = 2` 的情形，由 `(Kn2sol)` 加上面两条推出。
>   `(Kn2sol)` 本身是论文从 `[YY_25]`/`[RBSO1D]` 取来的公式，按惯例写成假设 `KTwoFormula`。
>
> **没做的：一般 `n`**。论文的证明走的是 `(eq:tree_rep2)`——带 `M`-边的**精细**树表示，
> 而 Q15 落地的是 `eq_Ktree`（`Γ^(n)`，边是 `Θ` 与 `Θ − I`）。两者都能用：纯回路时所有电荷相同，
> 每条边要么是 `Θ^(σ,σ)`、要么是 `Θ^(σ,σ) − I = tμS Θ`，都指数衰减。
> 但要把这件事贯穿 `polyVal` 的递归，需要对那个递归做归纳，每次分裂对内部顶点求和、常数 `c` 递减一次——
> **工具（`sum_exp_decay_conv`）已经备好，剩下的是归纳本身**，另开 **Q25**。
>
> 审计里 `ThetaDecayShort` 的承重从 2 条升到 **4 条**。


**文件**：新开 `RBM3D/Loop/PureLoop.lean`。陈述（`res_pureKes`）：`σ_1 = σ_2 = … = σ_n` 时，
存在 `c_n, C_n > 0` 使得

```
|K^(n)_{t,σ,a}| ≤ C_n · W^{-d(n-1)} · exp(−c_n · max_{i,j}|a_i − a_j|)
```

**这条是本文自足证的**：用树表示 `eq:tree_rep2`（每项只含 `M`-边与短的无标号边），
加上 `(prop:ThfadC_short)` 的指数衰减——注意 `(prop:ThfadC_short)` 是接口公理
`theta_decay_short`，所以这条会依赖它，审计里会体现出来，这是对的。


---

## Q17 · `lem:sum_decay` 与 `eq:latticesum_d3` — **Q17a DONE**（CC，2026-09-19），Q17b 待做

> **Q17a 完成记录**：新文件 `RBM3D/Kernel/SumDecay.lean`，`./check.sh` → `errors: 0`、`exit=0`，
> **不依赖任何接口假设**。
>
> ```lean
> theorem latticesum_d3 (k : ℕ) (hc : 0 < c) (hℓ : 0 < ℓ) (hR : 1 ≤ R) (hL : 3 ≤ L) (a₁ a₂) :
>     ∑ b ∈ {b | R < |a₁−b| ∧ R < |a₂−b|},
>         exp (−(c·|a₁−b|/ℓ)) / (|a₁−b|^(k+1) · |a₂−b|^(k+2))
>       ≤ latC k * Real.log L / (R : ℝ) ^ k          -- d = k+3，即 R^{d−3}
> ```
>
> **`d = 3` 与 `d ≥ 4` 不用分开处理**（比工单预计的省事）。对每个 `b`，记 `u = |a₁−b|`、`v = |a₂−b|`：
> `v ≥ u/2` 时被求和项 `≤ 2^{d−1}u^{−(2d−3)}`；`v < u/2` 时 `u > 2v`，项 `≤ v^{−(2d−3)}`。
> 于是**与情形无关地** `f(b) ≤ 2^{d−1}(u^{−(2d−3)} + v^{−(2d−3)})`，两项都是径向函数，
> 按球壳求和（`card_sphere_le`）后剩 `Σ_{r>R} r^{2−d}`，再用 `r^{2−d} = r^{−1}·r^{3−d} ≤ r^{−1}R^{3−d}`（`r > R`，`d ≥ 3`）
> 归结到调和和 `Σ_{r≤M} 1/r ≤ 1 + log M`（`sum_inv_Icc_le`，由 `log x ≤ x−1` 望远镜得到）。
> **`log` 对每个 `d` 都出现，但只在 `d = 3` 时是必需的**——正如论文所说。
>
> 指数因子按论文写在陈述里，但证明中只用到 `≤ 1`：**这个界来自环面直径，不是来自 `ℓ_t` 截断**。
> 常数 `latC k = 2^{3k+9}(2 + log(k+3))` 显式。辅助引理 `sum_radial_tail_le`、`one_le_log_of_three_le`（`e < 3`）。
>
> **Q17b 仍待做**：`lem:sum_decay` 本体（`sum_res_1`、`sum_res_2`），需要接口假设 `ThetaDecay`（`(prop:ThfadC)`）。



**文件**：`RBM3D/Kernel/Evolution.lean`（或新开 `Kernel/SumDecay.lean`，与 Q13 同文件时注意串行）。

**为什么补开**：附录 A.2 开头写着「we present the proofs of
`lem:sum_Ndecay`, `lem:sum_decay`, `lem:sum_decay_nonzero`」——三条。
我第一批只开了第一条（Q9）和第三条（Q13），**中间这条漏了**。

**而且漏掉的恰好是最值得形式化的一条。** `eq:latticesum_d3` 是**第三轮校对时新加进论文的**：
原稿在 `eq:bddfA` 的第三步直接得到 `W^{(n+4)ε}`，但那一步的格点求和在 `d = 3` 是临界情形，
会多出一个 `log`。补进去的是

```
Σ_{b : |a₁−b| ∧ |a₂−b| > R}  exp(−c|a₁−b|/ℓ_t) / (|a₁−b|^{d−2} · |a₂−b|^{d−1})  ≲  log L / R^{d−3},
                                                                        ∀ 1 ≤ R ≤ L
```

对每个 `d ≥ 3` 成立；**`log` 只在临界情形 `d = 3` 需要**——那里被求和项恰好像 `|b|^{-d}` 那样衰减，
`R ≤ |b| ≲ ℓ_t` 上的和是 `log(ℓ_t/R)` 量级。指数因此从 `W^{(n+4)ε}` 改成 `W^{(n+5)ε}`。

**这是整篇论文附录里唯一一处「新数学」**（其余都是补写隐含步骤或修记号），所以它是
形式化收益最高的单条引理之一：如果论文那一步其实站不住，Lean 会在这里卡住。

**现在做它比一小时前便宜得多**：Q11 的 K0、K2 已经落地了需要的基础设施——
`Defs/Shells.lean` 的 `card_sphere_le`（球壳计数 `#{|x| = r} ≤ 2^d (r+1)^{d-1}`）
和 `Defs/RadialSum.lean` 的 `sum_radial` / `sum_radial_exp_le`（按球壳求和、
带 stretched-exponential 截断的径向和）。**先读这两个文件再动手，别重复造。**

**建议拆成两步**：

* **Q17a**：把 `eq:latticesum_d3` 作为独立引理证出来（纯格点求和，只用 Shells + RadialSum，
  不需要任何接口公理）。**注意 `d = 3` 与 `d ≥ 4` 要分开处理**——这正是
  `docs/PLAN.md` 里说的「`d = 3` 的临界性只集中在两处」的第一处。
* **Q17b**：`lem:sum_decay` 本体（`sum_res_1`、`sum_res_2`）。走 `(eq:decompUalt)` 把
  `U^(n)∘A` 按 `A ⊂ [n]` 拆开（Q9 已经有这个分解），再分别证 `sum_res_1_red0`（`|A| = k ≥ 1`）
  与 `sum_res_1_red`（`A = ∅`）。需要 `(eq:decayXi)`，它来自接口公理 `theta_decay`
  （`(prop:ThfadC)`），所以这条会依赖接口公理，审计里会体现——这是对的。

做完 Q17a 就在 STATUS 里单独记一笔：**那一条是第三轮新加的，Lean 通过等于给它独立背书。**


---

## Q18 · 让审计直接报定理数与公理承重情况 — **DONE**（CC，2026-09-19）

> **完成记录**：`Test/Axioms.lean`。`./check.sh` 现在报的是：
>
> ```
> axiom audit: 283 theorems, 132 definitions, 0 axioms in `RBM`
>   (compiler-generated declarations excluded).
> All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper
>   cites rather than proves is carried as hypotheses, not asserted.
> theorems resting on each borrowed result:
>   RBM.ThetaDecay: 0        RBM.ThetaDecayShort: 2
>   RBM.ThetaDiffOne: 0      RBM.ThetaDiffTwo: 0
>   RBM.ThetaZeroMode: 2     RBM.PropTH: 0        RBM.Loop.KTreeRep: 0
> ```
>
> **过滤用的是现成判定**（按工单要求没有自己拼字符串）：`Name.isInternalDetail`、
> `Lean.isAuxRecursor`、`Lean.isNoConfusion`，外加排除 `.recInfo`。分类用 `ConstantInfo`：
> `thmInfo` / `axiomInfo` / `defnInfo`+`inductInfo`+`ctorInfo`+`opaqueInfo`。
> 下限检查从「≥ 20 条声明」改成「≥ 20 条**定理**」。
>
> **第二件事按 Q19 之后的实际情况调整了口径**（工单写于 Q19 前后）：接口现在是**假设**不是公理，
> 所以「借用承重多少」不再是「哪些声明依赖某条公理」，而是**哪些定理的类型里带着接口假设**。
> 审计现在数的正是这个，并且**排除接口自身的投影**（`PropTH.decay` 之类提到它但并不依赖它——
> 第一版没排除时 `PropTH` 显示 4，全是投影，那是误导）。
>
> **那个数字已经不是 0 了**：`ThetaDecayShort` 和 `ThetaZeroMode` 各承重 2 条——正是 Q13 的定理。
> 工单说「从 0 变正的时刻值得单独记一笔」，这一笔记在 STATUS 里。


**文件**：`RBM3D/Test/Axioms.lean`。**动手前确认没人正在改这个文件。**

**起因**：`#assert_rbm_axioms` 现在报的是「N 条声明」，数的是 `env.constants` 里所有 `RBM`
前缀的常量——里面混着 `def`、`structure`、`instance`，以及编译器自动生成的递归子、
equation lemma、`.proof_N`、实例投影。实测：总数 389，其中**手写只有 222 条，167 条是自动生成的**；
手写的 222 条里**定理 174、定义 37、结构 6、公理 5**。

拿「389 条声明」当进度报是误导的（Cowork 侧已经这么报了好几拍，是我的错）。

**要改成**：报告里分开列出

* `theorem` 的条数（`ConstantInfo.thmInfo`）；
* 定义类的条数（`defnInfo` / `inductInfo` / `ctorInfo` / `opaqueInfo`）；
* 公理数；
* 过滤掉编译器生成的（名字里含 `.proof_`、`.eq_`、`._`、以 `.rec`/`.recOn`/`.casesOn`/`.below`/
  `.brecOn`/`.noConfusion`/`.ofNat`/`.sizeOf` 结尾等——用 `Name.isInternal` 或
  `isAuxRecursor` / `isNoConfusion` 之类的现成判定，**别自己拼字符串匹配**，先去
  `../RBM1D/.lake/packages/mathlib/` 或 Lean 核心里 grep 有没有现成的）。

**另外一件更要紧的**：现在每条接口公理的依赖计数都是 **1，也就是只有它自己**——
`collectAxioms` 对公理本身会返回它自己。换句话说**目前 174 条定理没有一条依赖接口公理**，
借来的结果还没有承重。这是个好消息，但报告里看不出来。请把计数改成
**「除它自己以外有多少条声明依赖它」**（即当前值减一），并在都为 0 时明确写一句
「no declaration yet depends on the borrowed results」。

第一批会让它非零的是 Q13、Q16、Q17b。**那个数字从 0 变正的时刻，就是「借用开始承重」**，
值得在 STATUS 里单独记一笔。


---

## Q19 · 把 5 条接口 axiom 改成 `structure` 字段 — **DONE**（CC，2026-09-19）⭐

> **完成记录**：`./check.sh` → `errors: 0`、`exit=0`、464 条声明。
> **审计报的是：「No interface axioms」——全项目现在只用 `propext` / `Classical.choice` / `Quot.sound`，
> 零项目公理**，与 RBM1D、RBM2D 同一标准。
>
> `Propagator/Interface.lean`：5 条 `axiom` → 5 个 `Prop` 定义 `ThetaDecay`、`ThetaDecayShort`、
> `ThetaDiffOne`、`ThetaDiffTwo`、`ThetaZeroMode`，外加 `structure PropTH (d g m)` 打包（字段名
> `decay` / `decayShort` / `diffOne` / `diffTwo` / `zeroMode`）。**陈述一字未动**；原来写在 binder 里的
> 默认假设 `3 ≤ d`、`0 < g`、`‖m‖ = 1`（以及两条差分的 `τ > 0`）改成各自 `Prop` 的前件，
> 于是每条都能**单独陈述、单独假设、单独消解**——将来证出某一条就是
> `theorem thetaDecay_of (hd : 3 ≤ d) … : ThetaDecay d g m`，下游签名一个字不用改。
>
> `Test/Axioms.lean`：`interfaceAxioms := []`，审计在清单为空时改报「No interface axioms」一行。
> **反向测试已跑**：临时加一条 `sorry` 定理和一条 `axiom`，审计照样失败（`RBM.bogus depends on [sorryAx]`）。
>
> 连带改的文档：`docs/paper-deltas.md` 的 D5 重写（并在 D10 里注明清单已清空）、`README.md` 状态表、
> `RBM3D/Basic.lean` 的模块说明。下游目前没有任何定理引用这 5 条，所以**这次改动零返工**（Q13、Q16、Q17 将是第一批使用者）。


**文件**：`RBM3D/Propagator/Interface.lean`（改写）、`RBM3D/Test/Axioms.lean`（收尾）。

**为什么改**：见 `CLAUDE.md` 的「接口的形式」。一句话——`axiom` 污染公理审计，而且
**将来真把它证出来时，下游要返工**；写成字段/参数就能做到「原地把字段换成定理，签名一个字不改」。

本项目已经自发走对过两次：`Graph/Model.lean` 的 `Case.Rel` 是显式假设；
`Propagator/Basic.lean` 早期的 `hS` / `hone` 也是假设，被 Q3/Q4 消掉时**签名没变、下游零返工**。
Q19 就是把这个形式贯彻到剩下 5 条。

**建议形状**（两层，兼顾「单条可消」与「调用方便」）：

```lean
/-- `(prop:ThfadC)`，`lem_propTH` 性质 5。 -/
def ThetaDecay (d : ℕ) (g : ℝ) (m : ℂ) : Prop :=
  ∃ Cd > (0:ℝ), ∃ cd > (0:ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L, …

def ThetaDecayShort  (d : ℕ) (g : ℝ) (m : ℂ) : Prop := …   -- (prop:ThfadC_short)
def ThetaDiffOne     (d : ℕ) (g : ℝ) (m : ℂ) : Prop := …   -- (prop:BD1)
def ThetaDiffTwo     (d : ℕ) (g : ℝ) (m : ℂ) : Prop := …   -- (prop:BD2)
def ThetaZeroMode    (d : ℕ) (g : ℝ) (m : ℂ) : Prop := …   -- (prop:ThfadC0)

/-- `lem_propTH` 性质 5–8：本文引用而未证的那几条，打包。 -/
structure PropTH (d : ℕ) (g : ℝ) (m : ℂ) : Prop where
  decay       : ThetaDecay d g m
  decayShort  : ThetaDecayShort d g m
  diffOne     : ThetaDiffOne d g m
  diffTwo     : ThetaDiffTwo d g m
  zeroMode    : ThetaZeroMode d g m
```

**陈述内容原样搬过来**，一个字不改——现在那 5 条 axiom 的 body 就是要的东西。

**下游怎么用**：需要它的定理多带一个参数 `(hP : PropTH d g m)`，用 `hP.decay` 取。
目前没有任何定理依赖这 5 条（审计报的依赖数都是 1，即只有它自己），**所以这次改动零返工**，
这也正是现在做而不是以后做的理由。第一批会用到的是 Q13、Q16、Q17b。

**单条分开写的理由**：`(prop:BD1)` 论文自己说在所引文献里**根本没有显式证明**，
而其余几条有出处。将来能一条条消掉，所以要能一条条引用。

**收尾**：`Test/Axioms.lean` 的 `interfaceAxioms` 清空，审计回到 RBM1D 那种最严形式——
**只允许 `propext` / `Classical.choice` / `Quot.sound`**。这是验收标准：
`#assert_rbm_axioms` 通过且接口名单为空。同时在 `docs/paper-deltas.md` 把 D5 改写
（那条现在写的是「接口公理写成展开式」，要改成「写成 `Prop` 定义 + 结构字段」）。

## Q20 · `(eq:key_T_reudce)` 求和版 — **PARTIAL**（CC，2026-09-19）

**文件**：`RBM3D/Kernel/PropT.lean`。Q12 的 STATUS 里明确建议单开这条：
`claim:TTk` 的逐点版做完之后，带 `≺` 和 `ℓ ≤ (log W)^{10} ℓ_t` 的求和版是另一件事。

---

# 储备工单（队列见底时按顺序自取，见 `CLAUDE.md` 的「永不停工」）

**R1 · `ML:Kbound`：`K`-loop 的关键界**（附录 A.5 末尾）。论文说「证明类似 `[YY_25]`
Lemma 3.11，但**需要额外修改以处理 `d ≥ 3`**」——**那句「额外修改」正是要在 Lean 里看清楚的地方**，
也是这一章里最可能藏东西的一条。先读 `../RBM1D/RBM1D/Loop/KBound.lean`（1657 行，已编译）。

**R2 · `m-loop-tsp`：块 Anderson 的 `M`-loop 版典范划分**（`\Cref{m-loop-tsp}`）。
依赖 Q14。注意 `paper-deltas.md` D6：本项目目前只覆盖随机带矩阵模型，这条是往块 Anderson 扩的第一步。

**R3 · 维护：消假设。** 把带着假设的引理找出来（`grep -n 'Case.Rel\|hP :\|(h[A-Z]'`），
凡是前提已经落地的就给出无假设版本，签名不变。Q3/Q4 消掉 `hS`/`hone` 就是范例。

**R4 · 维护：补 `docs/mathlib-api.md`。** 把各文件里实际用到的 Mathlib 名字核一遍记进去。

**R5 · 审计：逐字对一节。** 挑论文的一节（建议从 §2.5 传播子开始），
把 Lean 陈述与论文**逐字**对一遍，偏离记进 `paper-deltas.md`，
并写明**论文第几页、改哪一段、大约几行**。

> RBM1D 的经验里，两个最大的收益都不是写代码换来的，是坐下来把论文读一遍换来的——
> 其中一次**否定性核查**（确认某条捷径走不通）省下了 150–300 条定理的白工。
> **R5 这类活不是填空，是正经工作。**

### CC 的完成记录（2026-09-19）

**做了什么**（`Defs/RadialSum.lean` + `Kernel/PropT.lean`，`./check.sh` 绿，0 warning）：

* `sum_shift`：格点和按 `α ↦ a - α` 重标。
* `sum_ball_min_pow_le`：**Appendix A.4 的那条格点和**
  `Σ_{α ∈ D} (|x-α| ∧ ℓ + 1)^{-(d-2)} ≤ C_d ℓ²`，`D` 任意含于 `a` 的 `ℓ`-球（即论文的 `D_{≤ℓ}`）。
* `sfT_antitone`、`wfac`（`(r+1)^{-(d-2)/2}` 因子）及其 `nonneg / le_one / antitone / sq`、
  `wfac_min_sq_le`（`(p∧q+1)^{-(d-2)} ≤ (p+1)^{-(d-2)} + (q+1)^{-(d-2)}`）。
* `sfT_pair_le`：**论文的三种情形在逐点层面合并成一条**。
* `prod_sfT_pair_le`（`k` 对相乘）、`prod_wfac_le_two`（`k ≥ 2` 时只留两个多项式因子）。
* `keyC`、**`key_T_reduce`**：`Σ_{α∈D} Π_i 𝖳(|x_i-α|∧ℓ)𝖳(|y_i-α|∧ℓ)
  ≤ C(d,n)·(Ψ_t²ℓ²)·Ψ_t^{n-2}·Π_i 𝖳(|x_i-y_i|∧ℓ)`，`n ≥ 2`，`ℓ ≥ 1`。

**两点比论文更省的地方**（都不是偏离，是证明路线不同，已记 paper-deltas D14/D15）：

1. **三种情形逐点合并**。把多项式因子取成 `|x_i-α| ∧ |y_i-α| ∧ ℓ`（截断后的 min），
   情形 1 的 `(eq:TtTt)` 因子与情形 2/3 的 `(eq:KtKt)` 因子就都是它。
   于是 `2^{2k}` 个 `D_{≤ℓ,𝛔}` 分块和三种情形的讨论**在 Lean 里都不需要**：
   情形之分只决定「保留几个多项式因子」，而这由 `prod_wfac_le_two` 一条处理。
2. **不数 `D_{≤ℓ}` 的体积**。论文在 `|x-α| > ℓ` 的区域用 `|D_{≤ℓ}| ≲ ℓ^d` 乘常数
   `(ℓ+1)^{-(d-2)}`。这里改成：`α ∈ D` 保证 `|a-α| ≤ ℓ`，于是**以 `a` 为心的第二份 K2**
   本身就 `≥ e^{-1}(ℓ+1)^{-(d-2)}`，体积因子由 `sum_radial_exp_le` 免费给出。
   两个区域都由 K2 付账，`ℓ²` 是同一个 `ℓ²`。

**没做的（→ Q29）**：从 `Ψ_t²ℓ²` 到 `(W^dη_t)^{-1}` 的吸收，即
`ℓ ≤ (log W)^{10}ℓ_t` 与 `ℓ_t²B_{t,0} ≲ |1-t|^{-1}`（`1-t ≥ ĝ²/L²`）那一步；
论文正是在这里出现对数因子、结论只能写 `≺` 而不是 `≲`。`DetDom` 的外衣也留在 Q29。

**边界条件**：`ℓ ≥ 1`（K2 的前提 `sum_radial_exp_le` 要 `ℓ ≥ 1`；论文写 `0 ≤ ℓ`，
`ℓ < 1` 时球内只有 `α = a` 一点，是平凡情形）。

### CC 的实现要点（Q12 完成后补，2026-09-19）

Q12 已把两条点态界和情形覆盖做完，剩下的就是求和：

* 按 `𝛔 ∈ {0,1}^{2k}` 把 `α` 的求和区域分块（论文 `D_{≤ℓ,𝛔}`），逐块证 `eq:key_T_reudce_pf`；
* 三种情形分别调用 `sfT_TtTt` / `sfT_KtKt`，**覆盖性已由 `sfT_pair_cases` 保证**，不必再手工讨论；
* 剩下的格点和 `Σ_α (|x_1−α| ∧ |y_1−α| + 1)^{-(d-2)} ≲ ℓ²` **可以复用 K2**
  （`Defs/RadialSum.lean` 的 `sum_radial_exp_le`）：`|x| ≤ ℓ` 时 `e^{-√(|x|/ℓ)} ≥ e^{-1}`，
  所以硬截断的和至多是带指数截断那个和的 `e` 倍；
* `≺` 用 `Defs/Domination.lean` 的 `DetDom`；`ℓ ≤ (log W)^{10} ℓ_t` 与 `ℓ_t² B_{t,0} ≲ |1−t|^{-1}` 是吸收对数因子的地方。


---

## Q21 · 逐字核对剩下四条接口陈述 — **DONE**（CC，2026-09-19）⭐

> **逐条结论**（对照 `1_2_Intro_model_result.tex` L1140–L1180 的 `lem_propTH` 性质 5–8）：
>
> | 性质 | 论文标签 | 结论 |
> |---|---|---|
> | 5 | `(prop:ThfadC)` | **与论文一致**。前件齐（`∀ a`、`t ∈ [0,1)`、`3 ≤ L`），量词序为 `∃C ∀L` ✅ |
> | 5' | `(prop:ThfadC_short)` | **已修**（beat 6，D11）：论文限定 `σ₁ = σ₂`，原 Lean 漏了 |
> | 6 | `(prop:BD1)` | **已修，D12**：论文是 `|r| ≲ |a|`，原 Lean 写成 `|r| ≤ |a|`（只取了隐含常数 = 1） |
> | 7 | `(prop:BD2)` | **已修，D12**：同上 |
> | 8 | `(prop:ThfadC0)` | **与论文一致**，且**零模去除是本质的**——见下面的反例 |
>
> **D12 的修法**：`≲` 按论文的用法读作「对**每个**常数 `c > 0`，在 `|r| ≤ c|a|` 上成立，`≺` 的常数可依赖 `c`」。
> 所以 `ThetaDiffOne` / `ThetaDiffTwo` 现在多一个 `∀ c > 0` 前件，条件写成 `(|r| : ℝ) ≤ c * |a|`。
> 原写法（`c = 1`）假设的比论文claim的**弱**，下游若需要 `c = 2` 就接不上。
>
> **新增反例（可执行的核对，Q21 点名要的那种）**：
> `RBM3D/Test/InterfaceShape.lean` 的 `not_zeroMode_without_removal`——
> 把性质 8 里的 `Θ̊` 换成 `Θ`，在谱参数 `1`（即 `σ₁ ≠ σ₂`）处**可证伪**：
> `Σ_b Θ_{t,0b} = (1−t)⁻¹` 随 `t → 1` 发散，而右端对 `t` 一致有界。
> 这机器确认了：`(prop:ThfadC0)` 的内容**就在**零模去除上，不是可有可无的修饰。
>
> **量词与归一化的核对**：四条的 `≺` 展开都是 `∀ τ > 0, ∃ C > 0, ∀ L …`，`C` 依赖 `τ, d, g, m` 而不依赖 `L, t, a, r` ✅；
> `B_{t,|a|}`、`ℓ_t`、`g²` 与 `Defs/Params.lean` 的定义逐项对上 ✅。
> 一处**有意的弱化**（D13）：论文说常数「depending on d」，而这里的 `∃ C` 位于以 `(d, g, m)` 为参数的 `Prop` 内，
> 所以常数也可以依赖 `g` 和 `m`——作为**假设**这样更弱、更安全；将来证出来时给出的常数只会更强。


**文件**：`RBM3D/Propagator/Interface.lean`、`RBM3D/Test/InterfaceShape.lean`。

**起因**：beat 6 发现 `(prop:ThfadC_short)` 的 Lean 陈述**是错的**。论文写的是
「Furthermore, **when `σ₁ = σ₂`**, we have a much stronger exponential decay」
（`1_2_Intro_model_result.tex` L1147），而 Cowork 在 beat 0 写那条 axiom 时**把这个限定漏了**，
改成对任意 `‖m‖ = 1` 陈述。于是 `σ₁ ≠ σ₂`（谱参数 `1`）时它为假：
`Σ_b Θ_{t,0b} = (1−t)⁻¹` 发散，而右端与 `t` 无关且可求和。

**论文没有错，错的是形式化。** 已修，并有机器证明 `not_decayShort_at_one` 证明旧写法在
谱参数 `1` 处不成立（`docs/paper-deltas.md` D11）。

**为什么要立刻核其余四条**：性质 5、6、7、8 是同一次坐下来写的，同一个人、同一种疏忽模式。
漏掉一个前件不会被任何自动机制发现——**审计查不出陈述错误，只查公理来源**。
而 Q13、Q16、Q17 正要开始用它们，越晚发现返工越大。

**做法**：把 `Interface.lean` 里四条 `Prop` 定义与论文 `lem_propTH` 的性质 5、6、7、8
（`1_2_Intro_model_result.tex` L1140–L1180）**逐字**对照，每条确认：

1. **前件齐不齐**——论文的每个「when …」「for …」「satisfying …」都到位了吗？
   性质 6、7 都有 `|r| ≲ |a|`；性质 5 有 `∀ a ∈ Z_L^d`；注意 `t ∈ [0,1)` 与 `3 ≤ L`。
2. **量词顺序对不对**——`∃ C ∀ L` 还是 `∀ L ∃ C`？论文的常数不依赖 `L`、`a`、`t`。
3. **`≺` 展开对不对**——`∀ τ > 0, ∃ C > 0` 里 `C` 可以依赖 `τ` 但不能依赖 `L`、`a`、`t`。
4. **两边的量纲/归一化**——`B_{t,|a|}`、`ℓ_t`、`g²` 是否与 `Defs/Params.lean` 里的定义一致。

**能加负面测试就加**：像 `not_decayShort_at_one` 那样，找一个参数点让「可疑的强写法」可被证伪。
这比读十遍管用——**它是可执行的核对**。若某条找不到反例也无妨，把核对结论写进 STATUS。

**验收**：四条逐条给出结论（「与论文一致」或「已修正，见 D…」），
每条修正都在 `paper-deltas.md` 记一条，并写明论文第几页/哪一段。

## Q22 · 移植 RBM1D 的 `eq_Ktree` 证明 — **OPEN**（CC 于 Q15 开出）

**目标**：把 `Loop/TreeRep.lean` 的假设 `KTreeRep` 换成定理，从而彻底不依赖 `[YY_25]` Lemma 3.4。

**路线（RBM1D 已走通，不要重新设计）**：不做组合双射，而是证明「树和与 `K`-loop 满足同一个卷积树方程、
且 `t = 0` 初值相同」，再由解的唯一性收尾。

**前置（这是 Q15 评估时卡住的地方）**：
* **传播子对 `t` 的导数层**——RBM1D 的 `Propagator/Deriv.lean`，RBM3D 目前没有。
  需要 `∂_t Θ_t = Θ_t · (M S^(B)) · Θ_t` 这类恒等式（`Ring.inverse` 的求导，`Defs`/`Props4` 已有的代数够用）。
* 然后照 `RBM1D/Loop/TreeRep.lean`（`n ≤ 4`，把组合讲透）→ `TreeRepGeneral.lean`（一般 `n`）移植。

**建议拆**：Q22a 传播子求导层；Q22b `n ≤ 4`；Q22c 一般 `n`。
每一步都能独立编译、独立提交，Q22a 本身对别的工单也有用。

---

## Q17b · `lem:sum_decay` 本体 — **PARTIAL**（CC，2026-09-19）：两块零件已证，三条结论 → Q28

> **完成记录**：`Kernel/SumDecay.lean` 续写，`./check.sh` → `errors: 0`、`exit=0`、零 sorry。
>
> **证出来的两块**（都是 A.2 证明反复用的零件）：
> * **`(eq:decomp_U2)`** `UN_apply_eq_sum_powerset`：按 `(eq:decompUalt)` 把每个单指标因子写成 `1 + Ξ^(i)`，
>   再把 `n` 个因子的积按子集展开——`Σ_{A ⊆ [n]} ∏_{i∈A} δ ∏_{i∉A} Ξ`。用的是 Mathlib 的 `Finset.prod_add`，
>   没有重造 Q9 的分解（`uKer_eq_one_add`）。新增定义 `XiKer` 给 `Ξ^(i)` 一个名字。
> * **`(eq:decayXi)`** `norm_XiKer_apply_le`：`|Ξ^(i)_{ab}| ≤ C(1−s)(g²+|1−t|)⁻¹(|a−b|+1)^{−(d−2)} e^{−c|a−b|/ℓ_t}`，
>   由 `(prop:ThfadC)`（接口假设 `ThetaDecay`，签名里写着）推出。三个技术点：
>   零模项由 `zeroMode_le_of_ge_mul` 吸收（用到 `lem:sum_decay` 假设的 `t ≤ 1 − g²/L²`）；
>   **`S^(B)` 只连最近邻**（新引理 `SB_apply_eq_zero_of_one_lt`），所以衰减廓线从 `|c−b|` 搬到 `|a−b|` 只差常数；
>   行和为 1 把对 `c` 的求和吃掉。
>
> **没做的：三条结论本身**（`sum_res_1`、`(I)` 非交替、`(II)` 和零性质）→ **Q28**。
> 它们要把上面两块接起来，再加上 `𝒜` 的快衰减假设 `(deccA0)`、`W^ε` 截断、
> 以及 `(1−s)ℓ_s² ≍ g²+|1−s|`（`eq:1-sells2`）这套记账——是独立的一拍。
>
> 审计里 `ThetaDecay` 的承重从 0 变成 **1**。


**文件**：`RBM3D/Kernel/SumDecay.lean`（Q17a 已建好，续写即可）。

**做法**见上面 Q17 条目末尾的「建议拆成两步」：走 `(eq:decompUalt)` 把 `U^(n)∘𝒜` 按 `A ⊂ [n]` 拆开
（**Q9 已经有这个分解，别重造**），分别证 `sum_res_1_red0`（`|A| = k ≥ 1`）与 `sum_res_1_red`（`A = ∅`）。
`(eq:decayXi)` 来自 `(prop:ThfadC)`，所以签名里要带 `ThetaDecay`（或整包 `PropTH`）——
**照 Q13 的写法**：把接口假设写进参数表，借了什么一眼可见。

**现成可用**：Q17a 留下的 `latticesum_d3`、`sum_inv_Icc_le`（调和和）、`sum_radial_tail_le`（径向尾和）。

---

## Q23 · 传播子对 `t` 的求导层 ⭐ — **DONE**（CC，2026-09-20）

**文件**：新开 `RBM3D/Propagator/Deriv.lean`。

**为什么这拍提**：Q15 的评估结论是「移植 `eq_Ktree` 卡点不在行数，而在前置：RBM1D 的
ODE 唯一性路线要先能对 `t` 求导 `Θ_t`」。这拍实测了那个前置有多大——
**`RBM1D/RBM1D/Propagator/Deriv.lean` 一共 92 行，4 条定理**，而它用到的东西
RBM3D 的 `Propagator/Basic.lean` **已经全都有**。也就是说这不是大件，是一拍能完的活，
做完 Q22 就只剩组合部分了。

**逐条对应**（左边是 RBM1D 的名字，右边是这里要写的）：

| RBM1D | 内容 | RBM3D 需要的前置 | 有没有 |
|---|---|---|---|
| `continuousAt_Theta` | `ζ ↦ Θ_ζ` 在 `‖ξ‖ < 1` 处连续 | `isUnit_one_sub_smul_SB` | ✅ `Basic.lean:78` |
| `Theta_sub_Theta` | 预解式恒等式 `Θ_ζ − Θ_ξ = (ζ−ξ)·Θ_ζ S^(B) Θ_ξ` | `Theta_mul` / `mul_Theta` | ✅ `Basic.lean:82,86` |
| `continuous_matrix_entry` | 取矩阵元连续 | — | 纯 Mathlib |
| `hasDerivAt_Theta_apply` | **(2.51)** `∂_ξ (Θ_ξ)_{ab} = (Θ_ξ S^(B) Θ_ξ)_{ab}` | 上面三条 | — |

**两处必须照抄、不要自己设计**：

1. **走预解式恒等式 + 连续性，不要逐项求导 Neumann 级数。**
   RBM1D 的路线是：先证 `Θ_ζ − Θ_ξ = (ζ−ξ)•(Θ_ζ S^(B) Θ_ξ)`（`noncomm_ring` 两步就下来了），
   再用 `hasDerivAt_iff_tendsto_slope`，把差商换成 `Θ_ζ S^(B) Θ_ξ` 后对 `ζ → ξ` 取极限。
2. **陈述写成逐元（entrywise）的。** RBM1D 的注释给了理由：一是第 3 节用到的全是对块指标逐元求和，
   二是**绕开 `Matrix` 的 Pi 拓扑与 `ℓ^∞` 算子范数之间的 instance 钻石**。
   写成整体矩阵的 `HasDerivAt` 会撞上这个钻石——**别试**。

**RBM3D 这边的唯一差异**：`Basic.lean` 里每条 `Theta` 引理都多带一个前件 `hS : ‖SB d L g‖ = 1`。
**继续带着它，别在这一层擅自改风格**（要消的话是 `norm_SB d L g hL`，`Defs/Block.lean:133`，Q3 已证）。

**可以直接信的 Mathlib 名字**（RBM1D 已编译过，顺手补进 `docs/mathlib-api.md`）：
`NormedRing.inverse_continuousAt`、`hasDerivAt_iff_tendsto_slope`、`slope_def_field`、
`eventually_nhdsWithin_of_eventually_nhds`、`self_mem_nhdsWithin`、`sub_ne_zero_of_ne`。
import 需要 `Mathlib.Analysis.Calculus.Deriv.Basic`、`Mathlib.Analysis.Calculus.Deriv.Slope`、
`Mathlib.Topology.Instances.Matrix`。

**验收**：`./check.sh` → `errors: 0`、`exit=0`，零 `sorry`，审计仍为空；
STATUS 里记一笔「**Q22 的前置已拆掉**」，并说明 `d` 作为参数有没有带来额外麻烦（预计没有，`Θ` 的定义同构）。

### CC 的完成记录（2026-09-20）

**照单全收地移植了**，`RBM3D/Propagator/Deriv.lean`（134 行，`./check.sh` 绿、0 warning）：
`continuousAt_Theta`、`Theta_sub_Theta`（预解式恒等式）、`continuous_matrix_entry`、
`hasDerivAt_Theta_apply`（逐元）。工单点名的两条纪律都守住了：走预解式 + 连续性、陈述逐元。

**多做了一条**：`hasDerivAt_Theta_mul_apply` —— 沿 `ξ = t μ` 对**实参数 `t`** 求导，
`∂_t (Θ_{tμ})_{ab} = μ (Θ S^(B) Θ)_{ab}`。理由：Q27 要的是 `∂_t K^(2)`，
拿到的却是 `∂_ξ`，差一次链式法则；与其让 Q27 每次自己接，不如在这一层接好。
（`μ = m(σ₁)m(σ₂)` 时它就是 `Θ_t^{(σ₁,σ₂)}` 本身对 `t` 的导数。）

**`d` 作为参数有没有带来麻烦：没有，一处都没有。** 整个论证里 `d` 只出现在类型
`Zd d L` 中，从不参与推理——`Θ` 的定义、预解式恒等式、`Ring.inverse` 的连续性都与维数无关。
与 RBM1D 的唯一差别是每条引理多带一个前件 `hS : ‖S^(B)‖ = 1`（按工单要求保留，
要消时用 `norm_SB d L g hL`）。

**踩到一个值得记的坑**（已写进 `docs/mathlib-api.md`）：`HasDerivAt` 是 `def`，
点记号 `h.mul_const` 在**该引理所在文件没 import** 时，报的不是 unknown constant，
而是「The environment does not contain `HasFDerivAtFilter.mul_const`」——
这条信息会把人引去找 `HasFDerivAtFilter` 的引理，实际只是缺 import
（`Deriv.Mul`、`Deriv.Comp`、`Complex.RealDeriv`）。写成显式应用才会报出真正的错因。

**下一步**：Q27（`(Kn2sol)`）现在没有前置了。

---

## Q22a · Grönwall 唯一性 — **DONE**（CC，2026-09-20）⭐

**文件**：`RBM3D/Loop/Unique.lean`（新，约 290 行）。`./check.sh` 绿、0 warning。

**移植的部分**（对应 `RBM1D/Loop/Unique.lean`，250 行，**一次编译通过**）：
`length_cutGlueR_eq_two` / `length_cutGlueL_eq_two`（结构引理：一条链满长 ⇒ 另一条是 2-loop）、
`two_le_length_cutGlueL/R`、`LoopVec`（长度 `n` 的回路作为有限类型）、`norm_SB_apply_le`、
`norm_mul_mul_sub_le`、`eq_on_level`（一次 Grönwall）、`isKLoop_unique`。

`d` **全程不参与推理**：它只在标签类型 `Zd d L` 和 `(pro_dyncalK)` 的前因子 `W^d` 里出现
（RBM1D 那边是 `W`，这里是 `W^d`，只影响一处 `norm_pow`）。

**比 RBM1D 多做的一层——这才是这拍的重点**：

* `norm_kTwo_le`（放在 `Loop/Primitive.lean`）：显式解的逐元界 `‖K^(2)‖ ≤ W^{-d}(1-t)^{-1}`，
  由 `norm_Theta_apply_le` + `Theta_real_nonneg` + `sum_Theta_real_row` 得到；
* `exists_eq_of_length_two`：长度 2 的良构回路就是 `⟨[σ₁,σ₂],[a₁,a₂]⟩`；
* **`kTwoFormula_of_isKLoop`**：只要 `K` 是 `[0,1)` 上的一族 `K`-loop、且它的 2-loop
  在每个 `[0,T₀]`（`T₀ < 1`）上有界，**`KTwoFormula` 就成立**。
  证法：只在 `n = 2` 这一层用 `eq_on_level`（此时「更短回路已一致」的前提是空的），
  `K` 与 `kTwoLoop` 解同一条 Riccati、在 `t = 0` 同取 `M`-loop 值。
* `pureLoop_two_of_isKLoop`：Q16 的估计，`KTwoFormula` 彻底消失，只剩 `ThetaDecayShort`。

**账目变化**：`KTwoFormula` 从「假设」变成「定理」。它本来就属于 Q26 说的
「欠下的」而不是「借来的」——现在这笔欠账还上了。代价只剩一条**先验界**
（2-loop 在每个 `[0,T₀]` 上有界），那是论文自己沿途证出来的东西，不是向外借的。

**`KTreeRep` 的状态也变了**：唯一性不再是假设，它现在**只欠存在性**（Q22b）。

**给 Q22b 的交接**：`isKLoop_unique` 的签名就是 Q22b 要对接的接口——
证明「树和满足 `(pro_dyncalK)` 且初值为 `M`-loop」之后，配上 2-loop 的先验界，
`eq_Ktree` 立刻落地，不需要再碰唯一性。

---

## Q22b · 树公式 = 存在性 — **PARTIAL**（CC，2026-09-20）：`n = 3` 已证

**这一拍做了什么**：新开 `RBM3D/Loop/TreeThree.lean`，把 `(eq_Ktree)` 在 **`n = 3`** 处证完。
`./check.sh` 绿、0 warning。

三角形没有对角线，所以 `TSP 3 = {∅}`（Q14 已证），树和就是单个星形
`Σ_b Θ^(σ₀σ₁)(a₀,b) Θ^(σ₁σ₂)(a₁,b) Θ^(σ₂σ₀)(a₂,b)`。真正的内容是**星形的三条边与
`(pro_dyncalK)` 的三个 `(k,l)` 项一一对应**：

* `(1,2)` 切下 2-链 `(σ₀,σ₁)`，换掉标签 `a₀`；
* `(2,3)` 切下 `(σ₁,σ₂)`，换掉 `a₁`；
* `(1,3)` 切下 `(σ₀,σ₂)`，换掉 `a₂`——**这一项的 2-链在 `S^(B)` 的左边**，
  所以要两条求和引理 `sum_SB_starLeft` / `sum_SB_starRight`，不是一条。

落地的声明：`treeEqRhs_three`、`treeVal_three_nil`、`treeSum_three`、
`sum_SB_starLeft/Right`、`hasDerivAt_starThree`、`kThree`、`hasDerivAt_kThree`、
`kThree_zero`、`kLoop3`、`exists_eq_of_length_three`、**`kThree_eq_of_isKLoop`**。

**最后一条是这拍的收获**：它说的是「**任意**一族 `K`-loop（2-loop 在 `[0,T₀]` 上有界）
的 3-loop 就是树值」——不带任何关于解的形状的假设。证法是 Q22a 的 `eq_on_level` 用在 `n = 3`，
长度 2 那一层由上一拍的 `kTwoFormula_of_isKLoop` 供给。**注意它只要 2-loop 的先验界，
不要 3-loop 的**：因为 `n ≥ 3` 的方程对 `n`-loop 是线性的，系数正是 2-loop。

**踩到的两个点**（写下来给 Q30/Q31）：

1. `HasDerivAt.sum` 的函数形状是 `∑ i ∈ s, A i`（Pi 上的和），要的是 **`HasDerivAt.fun_sum`**
   （`fun y => ∑ i, A i y`）；用错了报的是 type mismatch，不好认。
2. 三重积求导后目标里会留下**未 β 归约的** `((fun s => …) * fun s => …) t`，`ring` 看不穿，
   要先 `simp only [Pi.mul_apply]`。同理，`ring` 把 `thetaEdge …` 与 `Theta d L g (…)`
   当成两个不同的原子——**先做结合律的 `show`，再 `simp only [thetaEdge]` 展开，最后 `ring`**，
   顺序反了 `rw` 的模式就对不上。

**剩下的拆成两张**：

* **Q30 · `n = 4`**：第一次出现**内部边**（对角线 `(0,2)` 与 `(1,3)`），
  `TSP 4 = {∅, {(0,2)}, {(1,3)}}` 也已证。RBM1D 对应 `Loop/TreeRep.lean` 的 729 行，
  其中大半是 `star4/spl02/spl13` 的「按某一行线性」引理（`*_slot0..3`）。
  这里的 `polyVal` 是递归定义的，`treeVal_four_nil` 已经把星形那一支算出来了，
  两条对角线那一支要先算 `polyVal` 在 `F = [(0,2)]` 处的值。
* **Q31 · 一般 `n`**：对 `polyVal` 的递归做归纳，RBM1D 那边 2546 行。
  **先做 Q30**：`n = 4` 是唯一能看清「边 ↔ `(k,l)` 双射」在有内部边时长什么样的地方。

---

## Q24 · `ML:Kbound` —— 论文说「需额外修改以处理 `d ≥ 3`」 ⭐ — **OPEN**（R1 转正，本拍新提）

**文件**：新开 `RBM3D/Loop/KBound.lean`。

**起因**：论文说这条的证明「类似 `[YY_25]` Lemma 3.11，但**需要额外修改以处理 `d ≥ 3`**」。
**那句「额外修改」正是 Lean 该去看清楚的地方**——和 Q17 是一个道理：
凡是论文用一句话带过、而维数在其中起作用的地方，形式化的边际收益最高。

**先说别做什么**：`RBM1D/RBM1D/Loop/KBound.lean` **有 2515 行**，且依赖
`Loop/SumZero` 与 `Propagator/LongDiff`（16k 行量级的一条链），RBM3D 这两层都还没有。
**不要整体移植**，这一拍也移植不完。

**这一拍只做两件事**：

1. **陈述层**：把 `ML:Kbound` 在 `Loop/KBound.lean` 里**逐字**写下来——参数、量词顺序、
   常数依赖谁不依赖谁（对照 Q21 的四条核对清单来写），先不证。
   形状对齐 `PropTH` / `KTreeRep`：证不出来就当假设，**但必须是假设，不是 `axiom`**。
2. **把「额外修改」定位到具体一步**：读 RBM1D 那条链的骨架
   （`selfW_eq_treeValW_one` → `norm_selfEdge_le` → `norm_SigmaPi_empty_le`），
   找出**哪一步的常数或求和依赖维数**，在 STATUS 里写清「`d = 1` 那里用的是什么、`d ≥ 3` 得换成什么」。
   多半落在两处之一：球壳计数（`d−1` 次幂，`Defs/Shells.lean` 已有 `card_sphere_le`）
   与径向和的收敛性（`Σ r^{2−d}` 在 `d = 3` 是临界的，正是 Q17a 撞见的那个 `log`）。

**验收**：陈述层编译通过（`exit=0`、零 `sorry`），STATUS 里一段话说清那处「额外修改」是什么。
**若发现论文那句话其实掩盖了一个实质困难，立刻点出来**，别当成普通证明困难往下走——
Q17 和 beat 6 的接口缺陷都是这么找出来的。

## Q25 · `lem_pureloop` 的一般 `n` — **OPEN**（CC 于 Q16 开出）

**文件**：`RBM3D/Loop/PureLoop.lean`（接在 `pureLoop_two` 之后）。

**目标**：`res_pureKes` 对一般 `n`：`|K^(n)_{t,σ,a}| ≤ C_n W^{-d(n-1)} exp(−c_n max_{i,j}|a_i−a_j|)`，
纯回路（所有 `σ_i` 相同）。

**路线**：由 `KTreeRep`（Q15 的假设）把 `K^(n)` 换成 `W^{-d(n-1)} Σ_{Γ∈TSP} Γ^(n)`，
再对 `Loop/Partition.lean` 的 `polyVal` 递归做归纳，证「纯回路的树值指数衰减」：
* 外部边是 `Θ^(σ,σ)`，由 `norm_Theta_same_le_exp` 指数衰减；
* 内部边是 `Θ^(σ,σ) − I = tμ S^(B) Θ^(σ,σ)`，`S^(B)` 只连最近邻，所以也指数衰减（需要一条小引理）；
* 每次分裂对新顶点 `y` 求和，用 `sum_exp_decay_conv`，代价是 `c` 减半——
  `n` 固定时累计代价是 `c_n = c/2^{n}` 量级，常数 `C_n` 随 `|TSP n|`（小 Schröder 数）增长，这与论文的 `c_n, C_n` 形状一致。

**提示**：归纳假设要对「多边形的标签集合的最大两两距离」陈述，而不是对单个距离，
否则分裂后两块拼不回来。

**注意**（合并自本拍重复开出的同号工单）：`pureLoop_two` 现在带着假设 `KTwoFormula`。
**Q27 若先落地，这条假设会消失**，一般 `n` 的写法应当同样通过 `IsKLoop` 走，而不是再添新假设。

---

## Q26 · 审计要自动发现「借来的谓词」，不能靠硬编码名单 ⭐ — **OPEN**（beat 10 提，beat 14 扩范围）

> **beat 14 补充：只扫具名 `Prop` 是不够的。** Q22a 落地时带进来一条新的前提——
> `kTwoFormula_of_isKLoop` 的 `hbdd`（2-loop 在每个 `[0,T₀]` 上有界）。
> 它**直接写在签名里**，所以符合本项目「借了什么一眼可见」的原则；
> 但它不是一个具名 `Prop`，于是**任何汇总都数不到它**——包括这张工单原本设计的自动发现。
>
> 两件事一起做：
> 1. **CLAUDE.md 新增规则 15**：本项目没证出来的数学前提必须具名（`hbdd` 改成 `TwoLoopBounded` 之类）。
>    规则立住之后，「扫具名 `Prop`」才等于「扫全部前提」。
> 2. 审计里加一条**兜底检查**：若某条定理的签名里出现了不来自具名 `Prop` 的数学前提，报出来。
>    做不到全自动就退一步——**至少让已知的那几条具名化之后，名单与实际前件对不上时构建失败**。
>
> **为什么较真**：`hbdd` 这条其实是良性的（论文自己沿途证，`norm_kTwo_le` 也为显式解兑现了它）。
> 较真的不是这一条，是**「数不着」这件事本身**——对一份把「零公理」写在抬头的开发，
> 数不着和藏起来差别不大。

**文件**：`RBM3D/Test/Axioms.lean`。

**起因（这就是它值得单开一条的理由）**：Q18 刚把审计改成报「有多少条定理的类型里带着接口假设」，
名单是手写的六条（五条 `PropTH` 分量 + `KTreeRep`）。**紧接着的 Q16 就引入了第七条 `KTwoFormula`，
而它不在名单里，审计一声不吭。** 报告看上去仍然完整——这正是最坏的一种失败：
一份声称「全部记账」的报告，实际漏了记。

这和 beat 6 的教训是同一类：**审计只能查它被告知去查的东西**。
公理审计查不出陈述错误；承重审计查不出没登记的假设。**修法是让它自己去发现，而不是等人来登记。**

**做法建议**：扫 `RBM` 命名空间里所有 `Prop` 值的 `def` / `structure`，凡满足
「本身不是由本项目证明的定理、且出现在某条定理的类型里作为前件」的，都列进报告。
`PropTH` 的投影要排除（Q18 已经处理过这一层）。若做不到全自动，退一步也要做到：
**名单与实际前件对不上时构建失败**，而不是静默漏报。

**顺带要分的两本账**（这一条比计数更重要）：

* **借来的**：论文引用文献而未证的——`PropTH` 五条、`KTreeRep`（`[YY_25]` Lem 3.4）、
  `KTwoFormula`（`(Kn2sol)`，论文写作「As shown in `[YY_25,RBSO1D]`」）。这类是长期假设。
* **欠下的**：本可以在本项目里证出来、只是为了往前走而先假设的。
  **Q27 已经查明 `KTwoFormula` 属于这一本**（见下）。

两本账混在一起，「零公理」这个标题就会比实情好看。**报告要把它们分开列。**

**验收**：审计输出分两段；把一条新假设加进任意文件而不登记，构建应当失败（留一个反向测试）。

### CC 的完成记录（2026-09-20）

`RBM3D/Loop/Primitive.lean`（新文件，`./check.sh` 绿、0 warning）：`kTwo`、`Theta_zero`、
`norm_mul_lt_one`、`hasDerivAt_kTwo`、`kTwo_zero`、`kTwoLoop`、`hasDerivAt_kTwoLoop`、
`kTwoLoop_zero`、`kTwoFormula_kTwoLoop`、`pureLoop_two_kTwoLoop`。

**工单的算盘打对了**：`(Kn2sol)` 确实满足同一个 ODE 与同一个初值，
求导那一步直接用 Q23 多写的 `hasDerivAt_Theta_mul_apply`（沿 `ξ = tμ` 对 `t` 求导），
右端用 Q15 的 `treeEqRhs_two`，两边 `field_simp` 就合上了。

**但有一点要说清楚，工单标题写得比实际能做到的强**：
`KTwoFormula m K` 说的是「**任意**一族 `K`-loop 的 2-loop 等于那个公式」。
本文件证的是 `kTwo` **是一个**解（存在性）；要把任意 `K` 改写成它，需要
「同一 ODE + 同一初值 ⇒ 同一解」，也就是 **Q22a 的 Grönwall 唯一性**。
所以这条标 **PARTIAL**：存在性这一半已落地，`KTwoFormula` 还没真的消掉。

**两件仍然有用的产出**：

1. `kTwoFormula_kTwoLoop`：**`KTwoFormula` 是可满足的**。这条值得单独留着——
   一个不可满足的假设会让所有带着它的定理变成空洞的真，而审计只数「有多少定理压在它上面」，
   数不出空洞。现在这条假设有了显式见证。
2. `pureLoop_two_kTwoLoop`：把 Q16 的估计用到显式解上，**`KTwoFormula` 当场消失**，
   只剩 `ThetaDecayShort`——那条是论文真的向外借的。
   审计里 `ThetaDecayShort` 的承重从 4 涨到 5，涨的正是这条。

**给 Q22a 的交接**：唯一性的陈述应当写成「若 `K₁ K₂` 都 `IsKLoop m T`，则在 `T` 上逐点相等」，
`n = 2` 的 Riccati 情形现在有现成的显式解可以拿来对照测试。

---

## Q27 · 证出 `KTwoFormula`（`(Kn2sol)`） ⭐ — **PARTIAL**（CC，2026-09-20）：存在性已证，消假设待 Q22a

**文件**：新开 `RBM3D/Loop/Primitive.lean`（对应 `RBM1D/RBM1D/Loop/Primitive.lean`，**168 行**）。

**结论先说：这条不必借，能证。** 本拍算了一遍：`IsKLoop`（`Loop/TreeRep.lean`）已经是
「满足树方程这个 ODE + `t = 0` 初值 `MLoop`」的刻画，而 `(Kn2sol)` 的显式解

```
F(t) = W^{-d} · m(σ₁)m(σ₂) · Θ_{t·m(σ₁)m(σ₂)}(a₁, a₂)
```

**恰好满足同一个 ODE 与同一个初值**：

* 求导：`∂_t F = W^{-d}(m₁m₂)² · (Θ S^(B) Θ)(a₁,a₂)`，用的是 `∂_ξ Θ = Θ S^(B) Θ` 与链式法则 —— **这就是 Q23**；
* 方程右端：`treeEqRhs` 在 `n = 2` 处由 **Q15 已证的 `treeEqRhs_two`** 化为
  `W^d · Σ_{a,b} F(a₁,a) S(a,b) F(b,a₂) = W^d · W^{-2d}(m₁m₂)² (Θ S Θ)(a₁,a₂)`，两边一致 ✅；
* 初值：`MLoop` 在 `n = 2` 是 `W^{-d} m₁m₂ · 1[a₁=a₂]`，而 `Θ_0 = 1` ✅。

**所以这条属于「欠下的」而不是「借来的」**（Q26 的两本账）。论文把它放在 `\begin{example}` 里
写「As shown in `[YY_25,RBSO1D]`」，但那是一次例行计算，不是外部输入。

**路线**：照 `RBM1D/RBM1D/Loop/Primitive.lean` 移植 —— 它有现成的
`kTwo`、`hasDerivAt_kTwo`、`kTwo_zero`、`hasDerivAt_kTwoLoop`，结构与这里一一对应。
**先做 Q23**（它 import `RBM1D.Propagator.Deriv`）。

**做完的收益有两层**：`pureLoop_two`（Q16）的假设当场消失；
更要紧的是**它是 Q22 那条唯一性路线的小号预演**——同样的 ODE + 初值 + 唯一性三件套，
只是 `n = 2`。这一条走通，Q22 就不再是「没走过的大件」。

---

## Q22 重新拆分（本拍据实测修订）

本拍量了 RBM1D 那一侧的实际行数，Q22 应当拆成**便宜的一半**和**贵的一半**，别当一个大件：

| 步 | 内容 | RBM1D 对应 | 行数 | 依赖 |
|---|---|---|---|---|
| Q23 | 传播子求导层 | `Propagator/Deriv.lean` | 92 | — |
| Q27 | 2-loop 显式解，消掉 `KTwoFormula` | `Loop/Primitive.lean` | 168 | Q23 |
| **Q22a** | **Grönwall 唯一性 `isPrimitive_unique`** | `Loop/Unique.lean` | **250** | Q27 |
| Q22b | 树公式（存在性） | `Loop/TreeRep.lean` + `TreeRepGeneral.lean` | 729 + 2546 | Q22a |

**关键观察**：`Loop/Unique.lean` 的证法是**一次 Grönwall**，不做组合。它的注释把结构讲清楚了——
`n ≥ 3` 时方程对长度 `n` 的未知量是**线性**的（另一支必为 2-loop），`n = 2` 时是 Riccati，
两种情形同一个估计覆盖，再对 `n` 强归纳。Mathlib 侧用的是
`Mathlib.Analysis.ODE.Gronwall`（`norm_le_gronwallBound_of_norm_deriv_right_le` 等，
`ODE_solution_unique*` 在 `Mathlib/Analysis/ODE/ExistUnique.lean`，均已核实存在）。

**因此 Q22a 一旦落地，`KTreeRep` 就从「表示定理」退成「只欠存在性」**——
唯一性不再是假设。这比整体移植先便宜得多，也先有用得多。

## Q28 · `lem:sum_decay` 的三条结论 — **OPEN**（CC 于 Q17b 开出）

> **改号说明**：CC 开这条时叫它 Q26，而 Cowork 侧在同一拍把 Q26 给了审计工单，表里撞了号。
> 内容一字未动，只改编号。以后 CC 从 Q28 往上顺排、Cowork 从 Q40 起（见本文件开头）。

**文件**：`RBM3D/Kernel/SumDecay.lean`（接在 `norm_XiKer_apply_le` 之后）。

**要证**：`sum_res_1`（主界）、`(I)` `sum_res_2_NAL`（`σ` 非交替）、`(II)` `sum_res_2`（`𝒜` 满足和零性质）。

**手上已有**：`UN_apply_eq_sum_powerset`（`(eq:decomp_U2)`）、`norm_XiKer_apply_le`（`(eq:decayXi)`）、
`latticesum_d3`（Q17a）、`sum_radial_*`、`sum_inv_Icc_le`。

**关键记账**（论文 A.2 的走法，按这个顺序做）：
1. `sum_res_1_red0`（`|A| = k ≥ 1`）：`|𝒜_b| ≤ ‖𝒜‖`，对 `i ∉ A` 各自求和。
   **注意**：直接用 `‖Ξ‖_{∞→∞} ≤ (t−s)/(1−t)` 给出的形状是 `((t−s)/(1−t))^{n−k}`，
   **比论文claim的 `((g²+|1−s|)/(g²+|1−t|))^{n−k}` 弱**——必须走 `(deccA0)` 把求和限制在
   `|a_i − b_i| ≲ W^ε ℓ_s` 的球内，再用 `(eq:decayXi)` 和球内求和 `Σ_{|x|≤R}(|x|+1)^{−(d−2)} ≲ R²`，
   配合 `(1−s)ℓ_s² ≲ g²+|1−s|` 才凑出论文的形状。**这一步是整条引理的关键，别走捷径。**
2. `sum_res_1_red`（`A = ∅`）：多出 `ℓ_t²/ℓ_s²` 因子。
3. `(I)`：非交替时某个 `Ξ^(k)` 是同号的，用 `(prop:ThfadC_short)` 换掉一个因子。
4. `(II)`：和零性质让 `A = ∅` 的主项消失（论文 `eq:decompXii` 那一步），剩下的用 `(prop:BD1)` 与 `latticesum_d3`。

**前两步要先补**：球内求和引理 `Σ_{|x| ≤ R} (|x|+1)^{−(d−2)} ≤ C_d (R+1)²`（仿 `sum_radial_tail_le` 写，几行），
以及 `(1−s) * ellT L g s ^ 2 ≤ g² + |1−s|`（从 `ellT` 定义直接算）。

---

## Q29 · `(eq:key_T_reudce)` 的 `≺` 吸收步 — **OPEN**（CC 于 Q20 开出）

**文件**：`RBM3D/Kernel/PropT.lean`（接在 `key_T_reduce` 之后）。

Q20 证到了确定性不等式，右边留着 `Ψ_t² ℓ²`。剩下的就是论文那一行末尾：

* `ℓ ≤ (log W)^{10} ℓ_t`（`claim:TTk` 的前提）；
* `ℓ_t² B_{t,0} ≲ |1-t|^{-1} ≲ η_t^{-1}`，在 `1 - t ≥ ĝ²/L²` 时成立；
* 于是 `Ψ_t² ℓ² = W^{-d} B_{t,0} ℓ² ≲ (log W)^{20} (W^d η_t)^{-1}`，对数因子**吃进 `≺`**。

**要点**：这是全项目第一处真正用到 `Defs/Domination.lean` 的 `DetDom` 的地方——
`≺` 的定义是「∀ τ > 0，N 充分大时 ≤ N^τ ·」，`(log W)^{20}` 正好被任意小的 `N^τ` 吞掉。
需要一条通用引理：**多项式对数因子 `≺ 1`**（`(log N)^m ≺ 1`），放 `Defs/Domination.lean`。
那条引理本身是纯 Mathlib 练习（`Real.isLittleO_log_rpow_atTop` 一类），但它会被后面
所有带 `≺` 的陈述反复用到，值得单独证干净。

**注意**：`η_t`、`B_{t,0}`、`ℓ_t` 之间的关系要逐字核对论文 `(def:etat)` 与 `lem:Bt0`，
不要凭印象写；`1 - t ≥ ĝ²/L²` 这个前提在 `claim:TTk` 里是显式写着的。

---

## Q40 · 依赖图把「借来的」和「暂时假设的」混成一类，而且有一条边是错的 ⭐ — **OPEN**（Cowork 于 beat 12 提）

**文件**：`blueprint/src/content.tex`（只动蓝图，不动 Lean 代码）。

CC 在 Q20 那一拍把 `content.tex` 整理得很好——`\lean{}` 都 `#check` 过、`\uses` 都能解析、
房规「`\leanok` 与它命名的声明同一次提交」也立住了。**下面两处是在那个基础上继续挑的，不是返工。**

### 一、`ax:` 这一类现在装了两种东西

第三章的抬头写得很清楚：「这些是本文**引用**而非证明的估计」。但 `ax:` 前缀现在挂着七个节点：

* **真·借来的**（五条）：`ax:ThfadC`、`ax:ThfadCshort`、`ax:BD1`、`ax:BD2`、`ax:ThfadC0`。
  本项目**不打算**证它们，它们会长期是假设。
* **只是暂时假设的**（两条）：`ax:KTreeRep`、`ax:KTwoFormula`。
  两条**都有工单要把它们证出来**（Q22a/Q22b 与 Q27），`content.tex` 自己就写着。

在生成的依赖图里这七个是同一种颜色、同一种说法，于是图在说「这七条都是外部输入」——
**而其中两条其实是本项目的欠债**。这正是 Q26 在审计那一侧要分的两本账，
蓝图这一侧也得分：**建议把后两条换个前缀（如 `hyp:`）并在章节里单独成段**，
说明「陈述在 Lean 里，证明本项目会补，工单是 Qxx」。

### 二、`ax:KTwoFormula` 的 `\uses{ax:KTreeRep}` 是错的

这条边说：2-loop 的闭式解依赖一般 `n` 的树表示。**它不依赖。** beat 10 算过：
`(Kn2sol)` 的证明（Q27）只用三样东西——

1. `IsKLoop`（「树方程 ODE + `t=0` 初值」的刻画），
2. `treeEqRhs_two`（Q15 **已证**的 `n = 2` 右端），
3. `∂_ξ Θ = Θ S^(B) Θ`（Q23）。

一条都不是 `KTreeRep`。**画成依赖 `KTreeRep`，图就在说 Q27 得等那个大件，而事实相反**——
Q27 恰恰是绕开大件、先拿到的那一块。

**根子在节点划分**：`ax:KTreeRep` 的 `\lean{}` 里塞了五个名字
（`LoopIdx`、`treeEqRhs`、`MLoop`、`IsKLoop`、`KTreeRep`），前四个是**已经落地的定义**，
只有第五个是假设。因为混在一起，整个节点拿不到 `\leanok`，**已完成的那四个也跟着显示为未完成**。

**建议拆成两个节点**：

* `def:kloop` —— `LoopIdx`、cut-and-glue、`treeEqRhs`、`treeEqRhs_two`、`MLoop`、`IsKLoop`，
  **带 `\leanok`**（这些都证/定义好了）；
* `hyp:KTreeRep` —— 只有 `KTreeRep` 这一条假设，`\uses{def:kloop}`。

然后 `ax:KTwoFormula` 改成 `\uses{def:kloop, def:Theta}`（Q23 落地后再加求导那个节点）。
**改完之后图才会显示出这条项目最关心的事实：主线可以从 Q23 → Q27 走，不必先啃 Q22b。**

**验收**：`leanblueprint` 能构建、`\uses` 全部解析；第三章分成「借来的五条」与「暂时假设的两条」两段；
`ax:KTwoFormula` 不再指向 `KTreeRep`；已落地的 `K`-loop 定义拿到 `\leanok`。
**与 Q26 对齐**：审计的两本账和蓝图的两段说的应当是同一件事。

---

## Q41 · 每条假设都要有「非空洞」证书 ⭐ — **OPEN**（Cowork 于 beat 13 提）

**文件**：`RBM3D/Test/InterfaceShape.lean`（已有反面测试，正面的加在这里）与 `RBM3D/Test/Axioms.lean`（报告）。

**起因**：Q27 这一拍 CC 顺手做了一件比工单要求更要紧的事——`kTwoFormula_kTwoLoop`，
给 `KTwoFormula` 一个**显式见证**。它记录的是：这条假设**可满足**，所以带着它的定理不是空洞真。
STATUS 里那句「这一点审计数不出来，只能靠这样一条定理记录」说到了点子上。

**为什么这不是锦上添花**：审计报「有 5 条定理依赖 `ThetaDecayShort`」，
但**若 `ThetaDecayShort` 本身是假的，这 5 条全是空洞真，而审计照样报 0 公理、一切正常**。
这不是假想——**beat 6 就是这么回事**：`(prop:ThfadC_short)` 当初漏了 `σ₁ = σ₂` 的限定，
在谱参数 `1` 处为假，那段时间整个项目是不一致的，公理审计查不出来，
最后是 Q13 第一次去用它才撞出来。`not_decayShort_at_one` 是那次的反面记录；
**这张工单要的是正面的那一半**。

**现在的账**：`KTwoFormula` 有见证（Q27）；`KTreeRep` 与五条 `PropTH` 分量**一条都没有**。

**可做的是什么**（五条 `PropTH` 没法整条证出来——那就是论文引用它们的原因——所以要挑一个能证的弱化）：

> **固定 `L` 版**：把 `∃ C, ∀ L, …` 换成 `∀ L, ∃ C, …`。
> 固定 `L` 时格点有限、`t` 在紧区间上，界的存在性是可证的；
> 假设的全部内容是**关于 `L` 的一致性**。

**这个弱化恰好覆盖 beat 6 那类缺陷**：当初的假写法在**固定 `L`** 下就已经不成立
（`Σ_b Θ_{t,0b} = (1−t)⁻¹` 随 `t → 1` 发散，与 `L` 无关），所以固定 `L` 版当时就会证不出来。
**换句话说，这条检查若早在 beat 0 就位，beat 6 的缺陷不会存在。**

**验收**：

1. 五条 `PropTH` 分量各有一条固定 `L` 版定理（或：明确记录为什么这一条连固定 `L` 版都证不出来，
   那本身就是必须立刻上报的发现）。
2. `KTreeRep` 照 `kTwoFormula_kTwoLoop` 的样子给见证——**Q22a 落地后它是顺带的**，
   所以这条可以排在 Q22a 之后，别阻塞主线。
3. 审计增报一列：每条假设**有没有非空洞证书**。与 Q26 合起来，三件事齐了——
   假设被自动发现、被分成借来的/欠下的、而且已知可满足。

**不要做的**：别为了凑证书把陈述削弱。若某条的固定 `L` 版也证不出来，**那是发现，不是障碍**，
按 CLAUDE.md 规则 13 留一个机器可核的反例，并当场上报。

---

## Q30 · `(eq_Ktree)` 的 `n = 4` — **OPEN**（CC 于 Q22b 开出）

**文件**：新开 `RBM3D/Loop/TreeFour.lean`。参照 `RBM1D/RBM1D/Loop/TreeRep.lean`（729 行）。

**为什么单开**：`n = 4` 是**第一次出现内部边**的长度。边与 `(k,l)` 的双射在这里第一次完整：
4 条边界边 + 2 条对角线 = 6 个 `k < l` 对。`n = 3` 只验证了「边界边 ↔ 带 2-链的项」这一半。

**已有的**：`TSP_four`（Q14）、`treeVal_four_nil`（星形那一支，Q14 已算）、
`sum_SB_starLeft/Right`、`hasDerivAt_Theta_mul_apply`、`eq_on_level`。

**要做的**：① `polyVal` 在 `F = [(0,2)]` 与 `[(1,3)]` 处的值（对角线那两支）；
② `treeEqRhs_four`（六项的索引核对）；③ 内部边 `Θ^(σ₀,σ₂) − I` 的导数
（`(prop:...)`：`∂_t(Θ−I) = μ Θ S Θ`，与边界边同一条公式，因为 `I` 不含 `t`）；
④ 拼起来 + `eq_on_level` 在 `n = 4`（低层由 Q22b 的 `n ≤ 3` 供给）。

**提醒**：内部边那两项的右端是**两条 3-链**相乘（不是 2-链 × 4-链），
所以低层供给要用到 `kThree_eq_of_isKLoop`，这正是这一拍先做 `n = 3` 的原因。

---

## Q31 · `(eq_Ktree)` 的一般 `n` — **OPEN**（CC 于 Q22b 开出；需 Q30）

**文件**：`RBM3D/Loop/TreeRepGeneral.lean`（新）。RBM1D 对应 2546 行——**本项目最大的一件**。

**路线**：对 `Loop/Partition.lean` 的 `polyVal` 递归做归纳。归纳的骨架应当是
「边 ↔ `(k,l)` 的双射」：每个 `Γ ∈ TSP(n)` 的每条边，求导后给出一个 `(k,l)` 项；
反过来每个 `(k,l)` 项由「把两块的树分别求和」得到。`noncrossing_split`、
`leftPairs`/`rightPairs`、`isDiag_split_lt`（都在 Q14 里）是这条路的零件。

**先做 Q30**，再回来定归纳假设的形状——不要跳过 `n = 4` 直接写一般 `n`。
