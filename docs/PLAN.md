# 形式化路线图（RBM3D）

## 项目形状（为什么是这个形状）

1. **Mathlib 没有随机分析**：没有 Itô 公式、矩阵布朗运动、SDE、Dyson Brownian motion。
   论文 §3–§7 的随机流（loop hierarchy、Steps 1–6、light-weight 项）**目前在 Lean 里
   无法证明**，只能作为接口挂起来，而且现在还不到时候。
2. **可完全形式化的是确定性内核**：§2.5 的传播子层 + 附录 A + 附录 B。
3. **但这篇论文的传播子衰减估计自己不证**（见 `CLAUDE.md`）。所以本项目的形状与
   RBM2D 不同：那边 §8 是主战场，这边 `lem_propTH` 性质 5–8 是**接口边界**，
   主战场在它**之上**——附录 A.2–A.5 和附录 B，那些是论文真正自足的推导。

一句话：**`lem_propTH` 是这个项目的地基线。地基以下打桩（axiom），地基以上盖楼（定理）。**

## 阶段表

| 阶段 | 内容 | 依赖 | 状态 |
|---|---|---|---|
| 0 | 脚手架、`Zd d L` 与周期距离、`ℓ_t`、`B_{t,K}`、`S^(B)(g)`、`Θ_t`、`≺`、公理审计 | — | **草稿已写，未编译**（T1） |
| 1 | 接口层：`lem_propTH` 性质 5–8 作为 axiom，逐字对齐论文 | 0 | **草稿已写，未编译**（T1） |
| 2 | 性质 1–4：论文完整证明的四条（对称、平移不变、交换、$\infty\to\infty$ 范数） | 0 | 未开始（T2–T3） |
| 3 | 附录 B 的 scaling order 算术记账 | — | **部分已写**（T4 收尾） |
| 4 | 图模型：molecule / atom / solid-waved-dotted-ghost edge / IPC，case 分析穷尽性 | 3 | 未开始（T5），**本项目最有价值的一块** |
| 5 | 附录 A.2：evolution kernel `U^(n)`、`Q^(A)`、`I_diff(σ)` 的分解 | 1, 2 | 未开始（T6） |
| 6 | 附录 A.3–A.4：`lem:propT`、`claim:TTk` | 5 | 未开始（T7） |
| 7 | 附录 A.5：canonical partition、tree representation、`K`-loop | 5 | 未开始（T8） |
| 8 | 降级公理：把 `(prop:BD1)(prop:BD2)(prop:ThfadC0)` 从 axiom 变成定理 | 1 | 未开始（T9–T11），**最硬** |
| — | 随机层 | — | **不形式化** |

### 为什么把阶段 4（图模型）排得这么靠前

第三轮校对在附录 B 的 `lem_scalingorder` 里发现漏掉了一种情形（case (vi)）。
**但它的算术与 case (iv) 完全相同**——`ord_case_vi` 在 Lean 里就是 `ord_case_iv` 的推论。
也就是说，只检查算术的形式化**抓不到**这个漏洞；漏的是**情形枚举**，不是不等式。

这件事直接决定了阶段 3 和阶段 4 的分工：阶段 3（算术）一天就能完，价值有限；
真正的价值在阶段 4——把图的构型枚举成一个 Lean 的归纳类型，让 `cases` 的穷尽性
由编译器保证。**这是整个项目里机器检查收益最高的一块**，也是唯一一处
Lean 能发现人眼漏掉的东西的地方。

### 为什么阶段 8 排在最后

把 `(prop:BD1)` 等降级成定理，要走 `[RBSO1D]` 附录 B 的 summation-by-parts 论证
（论文自己说它"extends directly to dimensions $d\ge 3$"），而 RBM2D 正在为 d=2 做同一件事。
合理的顺序是等 RBM2D 的 §8 落地，再把它推广到一般 d，而不是在这里从零重做。
`(prop:BD1)` 是个例外：论文说它在 `[yang2024Del]` 里**根本没有显式陈述**，
所以那一条无论如何都得自己证。

## Phase 1（= 阶段 0–3）完成标准

1. `./check.sh` → 零 error、零 sorry、exit=0
2. `#assert_rbm_axioms` 通过，且报出的接口依赖计数与 `interfaceAxioms` 列表一致
3. `lem_propTH` 性质 1–4 全部是定理；性质 5–8 是登记在册的 axiom
4. 附录 B 的算术记账全部是定理
5. `leanblueprint checkdecls && leanblueprint web` 通过
6. 人工复核：接口公理的每一条，逐字对着 `paper/tex/1_2_Intro_model_result.tex`
   的 `lem_propTH` 核一遍——**这一步不能省，公理写错了编译器不会告诉你**

## 风险与对策

| 风险 | 对策 |
|---|---|
| Cowork 写的第一批文件编不过 | T1 就是干这个的。这批文件**一次都没编译过**，错会集中在 Mathlib 引理名、`haveI : NeZero L` 在 axiom 陈述里的 elaboration、以及 `simp only [ord]` 能否展开 `def` |
| 接口陈述写错（与论文不符） | **已兑现一次**：`(prop:ThfadC_short)` 漏了论文的 `σ₁ = σ₂` 限定，当 axiom 的那段时间项目是不一致的。发现它的不是审计，是 Q13 第一次去用它。对策升级为三条：① 接口一律写成假设而非 axiom（Q19，把不一致降级为「下游空洞成立」）；② 每条接口尽量配一个**负面测试**，机器证明错误写法为假（`Test/InterfaceShape.lean`）；③ 逐字核对（Q21） |
| 磁盘满 | 见 T0。三份 Mathlib 放不下 |
| `Fin d → ZMod L` 上的 `Finset` 记账比 `ZMod L × ZMod L` 笨重 | 集中在 `Defs/Lattice.lean` 与 `Defs/Block.lean` 两处，改一处即可 |
| 图模型设计过度 | 先只建 `lem_scalingorder` 的 case 分析需要的最小结构，不要一上来就建完整的 IPC 图 |
| 范围蔓延 | 蓝图依赖图是唯一进度真相；Phase 1 不碰随机层任何东西 |

## 蓝图

`blueprint/src/content.tex` 写**整篇论文**的骨架（章节 + 每条定理的壳子和 `\uses{}`），
但只给已形式化的节点填 `\lean{}` 和 `\leanok`。依赖图配色：
绿 = 已形式化，蓝 = 已陈述未证，灰 = 仅在蓝图里（随机层与接口公理）。
**接口公理在图上单独用一种颜色**，让「哪些结论踩在借来的结果上」一眼可见。
