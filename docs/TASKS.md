# 工单队列（RBM3D）

**开工前先在这张表里认领（填 owner），并单独提交这一行。** 分工按文件切，不按难度切。

owner 取值：`CC`（Claude Code，本机）/ `CW`（Cowork，云端）/ `Jun`

| # | 工单 | 文件 | owner | 状态 |
|---|---|---|---|---|
| T0 | 磁盘与 Mathlib 依赖 | `lakefile.toml` | Jun | 待办 |
| T1 | 让第一批草稿编译通过 | 全部 `.lean` | CC | **完成**（逐文件编译；`./check.sh` 待 T0） |
| T2 | `lem_propTH` 性质 1–2 | `Propagator/Props14.lean` | — | 待办 |
| T3 | `lem_propTH` 性质 3–4 | `Propagator/Props14.lean` | — | 待办 |
| T4 | `S^(B)(g)` 双随机性 | `Defs/Block.lean` | — | 待办 |
| T5 | 图模型与 case 穷尽性 | `Graph/Model.lean` | — | 待办 |
| T6 | evolution kernel 分解 | `Kernel/Evolution.lean` | — | 待办 |
| T7 | `lem:propT` 与 `claim:TTk` | `Kernel/PropT.lean` | — | 待办 |
| T8 | canonical partition / tree representation | `Loop/Tree.lean` | — | 待办 |
| T9 | 降级 `(prop:ThfadC0)` | `Propagator/ZeroMode.lean` | — | 待办 |
| T10 | 降级 `(prop:BD2)` | `Propagator/Diff.lean` | — | 待办 |
| T11 | 降级 `(prop:BD1)` | `Propagator/Diff.lean` | — | 待办 |
| T12 | 蓝图 + GitHub Pages 上线 | `blueprint/`, 仓库设置 | Jun | 待办 |
| T13 | 把仓库加进 Cowork 会话的 sources | 仓库设置 | Jun | 待办 |

---

## T0 — 磁盘与 Mathlib 依赖

`~/Lean_proof` 所在卷 97% 满，剩约 15G。RBM1D 的 Mathlib build 约 6.6 GB，RBM2D 还没建。
三个项目各一份放不下。三选一：

1. 清磁盘，然后老实 `lake exe cache get`（最稳）
2. `RBM3D/.lake/packages` 符号链接到 `../RBM1D/.lake/packages`。toolchain 与 rev
   三者完全一致（都是 `v4.34.0`），理论上可行，**但要先确认 `lake` 不会写坏 RBM1D 那棵树**
3. 换一块盘

**在 T0 做完之前 `lake build` / `./check.sh` 跑不了**；但 T1 已绕过它完成，见 T1 的完成记录。

## T1 — 让第一批草稿编译通过 ⚠️ 最优先

`RBM3D/` 下的全部 `.lean` 是 Cowork 在**没有编译器**的情况下写的，一次都没编译过。
所有 Mathlib 名字都 grep 过 `../RBM1D/.lake/packages/mathlib/`，但签名没验过。

已知的高风险点，按可疑程度排序：

1. **`Propagator/Interface.lean` 的 `haveI : NeZero L := ⟨by omega⟩`**
   写在 axiom 陈述的 binder 之后、Prop 主体之前。`by omega` 要用上下文里的
   `hL : 3 ≤ L` 证 `L ≠ 0`。如果 elaboration 不认，改成显式
   `∀ (L : ℕ) (hL : 3 ≤ L), ∀ _ : NeZero L, ...` 或者把 `NeZero L` 提成 instance binder。
2. **`Graph/ScalingOrder.lean` 的 `simp only [ord]`** —— `ord` 是 `def`，
   `simp only` 能不能展开取决于是否生成了 equation lemma。不行就换 `unfold ord` 或
   `show (_ : ℤ) + _ ≤ _`。
3. **`Defs/Lattice.lean` 的 `Finset.single_le_sum`** —— 用法照抄自 Mathlib 内部调用
   （`Mathlib/Analysis/CStarAlgebra/Module/Constructions.lean:278`），但隐参数顺序没验。
4. **`Defs/Lattice.lean` 的 `if_neg`** —— RBM1D 的 build.log 显示它在这版 Mathlib 里
   已 deprecated（提示用 `ite_eq_right`）。只是 warning，不是 error，但可以顺手换掉。
5. **`Defs/Block.lean` 的 `circulant_isSymm_iff`** —— 要求 `[SubtractionMonoid n]`，
   `Fin d → ZMod L` 经 `Pi` 实例应当满足，但没验过。
6. **`Propagator/Basic.lean` 的 `ThetaRBM_eq_Theta`** —— 那句 `simp only [...]` 是猜的。
   证不出来就把这条引理删掉，它不是承重的。
7. **`Test/Axioms.lean`** —— 用了 `env.find?`、`.axiomInfo`、`collectAxioms`、
   `MessageData.joinSep`。`collectAxioms` 与 `joinSep` 照抄 RBM1D（已验），
   `env.find?` 的 match 分支是新写的。

**做法**：一个文件一个文件 `lake env lean RBM3D/Xxx.lean`，按 import 顺序来
（`Defs/Lattice` → `Defs/Params` → `Defs/Block` → `Defs/Domination` →
`Propagator/Basic` → `Propagator/Interface` → `Graph/ScalingOrder` → `Test/Axioms`）。
每修好一个就提交一次，并在 `docs/STATUS.md` 记一笔。

### T1 完成记录（2026-09-19 · CC）

没有动 T0：`RBM3D/.lake` 仍不存在，RBM1D 的树**只读**使用。做法是直接调 v4.34.0 的 `lean`，
`LEAN_PATH` = RBM1D 各 package 的 `.lake/build/lib/lean`（只读）+ 一个临时目录放 RBM3D 自己的 olean，
按 import 顺序逐文件 `lean -o`，`-D` 选项照抄 `lakefile.toml` 的 `leanOptions`。

结果：8 个文件 + 根文件 `RBM3D.lean` 全部 exit=0，**零 error、零 warning、零 sorry**。
`#assert_rbm_axioms` 通过：`RBM` 下 124 条声明，只用 `propext / Classical.choice / Quot.sound`
加 5 条接口公理，每条接口公理依赖计数 = 1（只有它自己）。
反向测试：临时文件里加一条 `sorry` 定理和一条未登记 `axiom`，审计正确报错。

改动（全是小修，没有改任何陈述）：

| 文件 | 问题 | 修法 |
|---|---|---|
| `Defs/Block.lean` | 没 import ℝ/ℂ，连锁报错 | 加 `import Mathlib.Basic.Complex.Basic`（`Mathlib.Data.Complex.Basic` 在这版已 deprecated） |
| `Defs/Block.lean` | `SB_apply_add_right` 未用 `[NeZero L]` 的 linter 警告 | `omit [NeZero L] in` |
| `Graph/ScalingOrder.lean` | `Mathlib.Tactic.Omega`、`Mathlib.Data.Int.Defs` 两个模块在这版不存在 | 换成 `Mathlib.Data.Int.Basic` + `Mathlib.Order.Basic`（后者提供 `Eq.le`）；`omega` 在核心里 |
| `Defs/Lattice.lean` | `if_neg` deprecated（风险点 4） | `simp [ZMod.neg_val, h]` |
| `Propagator/Interface.lean` | docstring 表格两行超 100 字符 | 缩短出处列措辞 |

七个风险点里 1、2、3、5、6、7 **原样通过**（`haveI : NeZero L := ⟨by omega⟩`、`simp only [ord]`、
`Finset.single_le_sum`、`circulant_isSymm_iff`、`ThetaRBM_eq_Theta`、`env.find?` 都没问题）。

**尚未验证**：`lake build` / `./check.sh` 本身（要 T0），以及 `checkdecls` 这个依赖能否解析。
T0 落地后跑一次 `./check.sh`，应当直接绿。

## T2 — `lem_propTH` 性质 1–2

对称性与平移不变性。`Defs/Block.lean` 里 `S^(B)` 那一层的对应命题（`SB_isSymm`、
`SB_apply_add_right`）已经写了；要抬到 `Θ_t`，走 `(eq;Taylor)` 的 Neumann 级数：
`Θ_t = Σ_k t^k (M S)^k`，级数每一项都对称 / 平移不变，取极限。
Mathlib 里找 `Matrix.inv_eq_of_...` 或直接用 `(1 - A)⁻¹ = ∑ Aᵏ` 的现成引理
（RBM1D 的 `Theta_eq_tsum` 就是这个，**先去抄那条**）。

## T3 — `lem_propTH` 性质 3–4

性质 3（交换性）：`Θ` 是 `S^(B)` 的有理函数，RBM 模型下 `M` 是数量矩阵，所以平凡。
性质 4（$\infty\to\infty$ 范数）：论文 A.1 有完整证明——Taylor 展开逐项比较
`|M^(σ₁,σ₂)_{ab}| ≤ M^(+,-)_{ab}`，再用 `M^(+,-)S^(B)` 双随机得 `Σ_b Θ^(+,-)_{ab} = (1-t)^{-1}`。
**依赖 T4。**

## T4 — `S^(B)(g)` 的双随机性

`Σ_b S^(B)_{ab} = 1`。要点是 `3 ≤ L` 时每点恰有 `2d` 个邻居，即
`#{x : Zd d L | zdistD d L x = 1} = 2 * d`。
证法：该集合与 `Fin d × Bool` 之间的双射（第 i 个坐标取 `±1`，其余取 0）。
`L ≤ 2` 时不成立（`L = 2` 时 `1 = -1`，邻居塌成 `d` 个），这就是 `3 ≤ L` 的来源。
参照 RBM1D 的 `card_sbSupport` / `sum_SB_row`，那边是 d=1 的同一件事。

## T5 — 图模型与 case 穷尽性 ⭐ 本项目最有价值的一块

见 `docs/PLAN.md`「为什么把阶段 4 排得这么靠前」。

要建的最小结构：足以表达 `lem_scalingorder` 证明里那个 case 分析的构型——
`G_{β₁α}`、`G_{wβ₂}`、`G_{αw}` 各自对角 / 非对角，以及 `β₁ = β₂` 与否。
把它做成一个 Lean 归纳类型，让 `cases` 的穷尽性由编译器保证，然后对每个构造子
调用 `Graph/ScalingOrder.lean` 里已经证好的算术引理。

**验收标准**：删掉 `ord_case_vi` 的调用，编译器应当报 non-exhaustive。
能做到这一点，这个项目就在数学上有了第三轮人工校对没有的保证。

## T6 — evolution kernel 分解

附录 A.2。第三轮补写的那段（`U^(n)_{s,t,σ}` 按指标分解、`Q^(A)` 的作用、
`A ⊃ I_diff(σ)` 强制 `σ_i = σ_{i+1}`）现在是显式的，可以直接照着形式化。
**依赖 T1、T2、T3。**

## T7 — `lem:propT` 与 `claim:TTk`

附录 A.3–A.4。第三轮给 `eq:TtTt` / `eq:KtKt` 补了 `∧ ℓ` 截断并修了 case 2/3 的
下标范围（`3 ≤ i ≤ k` → `2 ≤ i ≤ k` / `1 ≤ i ≤ k`）——**形式化时特别注意这两处**，
它们正是原稿出错的地方。**依赖 T6。**

## T8 — canonical partition / tree representation

附录 A.5。`def:canpnical_part`、`m-loop-tsp`、`tree-representation`。
注意 `tree-representation` 本身是 `[YY_25]` Lemma 3.4，**又是一条接口公理**，
落地时要加进 `interfaceAxioms`。RBM1D 有 `Loop/TreeRep.lean` 和
`Loop/TreeRepGeneral.lean`（共 ~2000 行，已编译），**先去看那边**。

## T-B10 — 核对 `eq:LW` 与 `[yang2024Del]` Lemma B.10 ⚠️ 落地接口公理前必做

见 `docs/paper-deltas.md` D9 第 2 条。要确认的就一个符号：Lemma B.10 里对应项是
`G_αy` 还是 `Ǧ_αy`。附录 B 的三条 expansion 引理要写成 axiom，陈述错了编译器查不出来，
所以**这一条必须在 `Graph/Expansions.lean` 落地之前核清楚**。

## T9 / T10 / T11 — 降级接口公理

见 `docs/PLAN.md`「为什么阶段 8 排在最后」。T11（`prop:BD1`）是唯一一条
在任何文献里都没有显式证明的，必须自己做。

## T12 — 蓝图上线

`pip install leanblueprint`；`leanblueprint web` 产出推 GitHub Pages。
Pages 要先在仓库 Settings 里开。`blueprint.yml` 只在 push 时发布，手动 Run workflow
会「成功」但什么都不发布。

## T13 — 把仓库加进 Cowork 会话的 sources

现在云端会话 push 不了这个仓库（git 代理 403：不在授权仓库集里），
所以 RBM2D 那套「写 → push → 读 CI 日志 → 改」的回路用不了。
加进去之后 Cowork 就能用 CI 当编译器，一轮约 10 分钟。
