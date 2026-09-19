# STATUS（RBM3D）

> 两边（Claude Code / Cowork）**唯一**的共享状态。开工前读它，收工前更新它。

## 2026-09-19 · Cowork · 项目建立

从空目录建起。范围、接口策略、索引类型三项由 Jun 拍板：
显式 axiom 接口 / Phase 1 三条线并行（附录 B 组合层、传播子定义+性质 1–4、附录 A.2–A.5）/
`Fin d → ZMod L` 且 `d` 保持参数。

### 落地的东西

脚手架完整：`lakefile.toml`、`lean-toolchain`(v4.34.0)、`.gitignore`、CI 两个 workflow、
`check.sh`/`watch.sh`、`home_page/`、`blueprint/` 的 macros 与样式、`paper/`（tex + PDF，已 gitignore）。
文档：`CLAUDE.md`、`docs/PLAN.md`、`docs/TASKS.md`、`docs/paper-deltas.md`、本文件。

Lean（**全部未编译**，见下）：

| 文件 | 内容 |
|---|---|
| `RBM3D/Basic.lean` | 文档枢纽 |
| `RBM3D/Defs/Lattice.lean` | `zdist`、`Zd d L`、`zdistD`、`Adj`；零点刻画、三角不等式、取负不变 |
| `RBM3D/Defs/Params.lean` | `ellT` `(eq:ellt)`、`Bparam` `(eq_B_param)` |
| `RBM3D/Defs/Block.lean` | `sbKernel`、`SB` `(eq:variancematrix)`；对称性与平移不变性 |
| `RBM3D/Defs/Domination.lean` | `UnifDetDom` / `DetDom`，**从 RBM1D 原样搬来**（那边已编译通过） |
| `RBM3D/Propagator/Basic.lean` | `Theta`、`ThetaRBM` `(def_Thxi)`、`ThetaRBM0` `(def_Thxi0)` |
| `RBM3D/Propagator/Interface.lean` | 5 条接口公理，逐字对应 `lem_propTH` 性质 5–8 |
| `RBM3D/Graph/ScalingOrder.lean` | `Counters`、`ord` `(eq:ordG)`、case (ii)–(vi) 的算术 |
| `RBM3D/Test/Axioms.lean` | `#assert_rbm_axioms`，带接口公理白名单与依赖计数 |

### 状态：**一行 Lean 都没有编译过**

云端容器和本机 VM 都拿不到 Mathlib（出口策略挡 `reservoir.lean-lang.org` 与
GitHub releases），而且这个仓库不在云端会话的授权仓库集里，**push 也做不了**，
所以 RBM2D 那条「用 CI 当编译器」的退路在这里暂时不通（T13）。

所有 Mathlib 名字都 grep 过 `../RBM1D/.lake/packages/mathlib/` 确认存在，
但**签名没有验证过**。`docs/TASKS.md` 的 T1 列了 7 个按可疑程度排序的风险点。

### 下一步

1. **T0**：磁盘。`~/Lean_proof` 所在卷 97% 满，只剩 15G，一份 Mathlib 要 6.6G。
2. **T1**：本机逐文件编译，按 import 顺序。
3. 然后按 `docs/PLAN.md` 的阶段表走，**T5（图模型）是价值最高的一块**。

### 一条值得记住的发现

第三轮人工校对在附录 B 发现漏掉的 case (vi)，其算术与 case (iv) 完全相同
（`ord_case_vi` 在 Lean 里就是 `ord_case_iv` 的推论）。
**只检查算术的形式化抓不到它**——漏的是情形枚举，不是不等式。
这直接决定了 T5 的验收标准：删掉 case (vi) 应当让编译器报 non-exhaustive。

## 2026-09-19 · Claude Code · T1 完成

**第一批草稿全部编译通过**：8 个文件 + `RBM3D.lean`，零 error / 零 warning / 零 sorry，
`#assert_rbm_axioms` 通过（124 条声明，5 条接口公理各被依赖 1 次）。
详见 `docs/TASKS.md` 的「T1 完成记录」。

没碰 T0：借 RBM1D 已编好的 Mathlib olean（只读，`LEAN_PATH` 直调 `lean`），
RBM3D 的 olean 写在临时目录。所以 **`./check.sh` 仍没跑过**，等 T0。

改动只有 import 修正和 lint 清理，**没有改任何陈述**，不需要记 `paper-deltas.md`。

**没有提交**：`.git/index.lock` 从首次 `git add` 起一直存在（>10 分钟），
initial commit 没落地，像是 Cowork 那边中断留下的死锁。Jun 确认没有 git 进程在跑后
`rm .git/index.lock`，再做首次提交（T1 的改动可以并进去，或单独一个 commit）。

下一步候选（都不依赖 T0，可以用同样的方式编译）：**T4**（`S^(B)` 双随机性，T3 的前置）、
**T5**（图模型，价值最高）。

## 2026-09-19 · Claude Code · Q1 完成

`docs/QUEUE.md` 的 Q1：重写后的传播子层（`959b4bd`）与其余文件全部编译通过，
零 error / 零 warning / 零 sorry；审计 136 条声明，5 条接口公理各依赖 1 次。
唯一改动：`Propagator/Basic.lean` 两处 `show` → `change`。
编译仍是借 RBM1D 的 Mathlib olean（只读），`./check.sh` 待 T0。
下一条：Q2（邻居计数）已解除阻塞；Q6（图模型）一直可并行。

## 2026-09-19 · Claude Code · Q6 完成（图模型 · case 穷尽性）

新文件 `RBM3D/Graph/Model.lean`（已加进 `RBM3D.lean`）。`lem_scalingorder` 权展开那一步的 case 分析，
做成 4-环 `β₁—α—w—β₂` 上等号模式的一个 `match`：16 种模式，12 种可实现，全部分到 (i)–(vi)；
**删掉 case (vi) 那一行，编译器报 `Missing cases`**（已实测）。每个 case 都证明了与论文描述等价的顶点刻画，
`ord_weight_step` 给出每步 `ord` 至少升 1。
全库：249 条声明，审计干净，5 条接口公理各依赖 1 次。
未覆盖：各 case 的计数关系是照抄论文的假设（`Case.Rel`），不是推导出来的；`n_lw/n_dv` 未建模。详见 QUEUE 的 Q6 完成记录。

## 2026-09-19 · Claude Code · Q2 完成（邻居计数）

新文件 `RBM3D/Defs/Neighbours.lean`：`card_nbhd d L hL : #{x | |x| = 1} = 2 * d`，以及平移版 `card_adj`。
`Block.lean` 未改动。全库 278 条声明，审计干净。Q3、Q4 现在可以解锁。签名见 QUEUE 的 Q2 完成记录。

## 2026-09-19 · Claude Code · Q3 + Q4 完成（`S^(B)` 双随机）

`Defs/Block.lean` 新增 `section Stochastic`：`norm_SB d L g hL : ‖SB d L g‖ = 1`、
`SB_mulVec_one d L g hL : SB *ᵥ 1 = 1`、`sum_SB_row` 等。`norm_SB` **不需要 `0 < g`**（比工单签名强）。
实测可直接消掉 `Propagator/Basic.lean` 的 `hS` / `hone`；该文件本身未改。Q5 可以解锁。
全库 294 条声明，审计干净。

## 2026-09-19 · Claude Code · Q5 完成（`lem_propTH` 性质 4）

新文件 `RBM3D/Propagator/Props4.lean`：`norm_Theta_apply_le`（`|Θ^(σ₁,σ₂)_ab| ≤ Θ^(+,-)_ab`）、
`sum_Theta_real_row`（行和 `(1-t)⁻¹`）、`norm_Theta_le`（`‖Θ_t^(σ₁,σ₂)‖_{∞→∞} ≤ (1-t)⁻¹`）。
另有性质 1–3 与行和、Neumann 级数的无 `hS/hone` 版本（`*_of_three_le`）。
**`lem_propTH` 性质 1–4 现在全部是定理**，5–8 仍是登记在册的接口公理。全库 320 条声明，审计干净。

## 2026-09-19 · Claude Code · Q8 部分完成 —— **卡住，需要拍板**

**卡在**：`(Owx)`/`(Oe2x)` 是 `=_𝔼` 恒等式，对 `G` 的任意可微函数成立。要逐字陈述，需要随机带矩阵模型本身
（分布、`G(z)`、`m`、`S^±` 的本文归一化、`∂_{h}` 的 Wirtinger 约定、`f` 的函数类）。这些都不在仓库里，
而且大半属于规则 6 不碰的随机层。**试过**：梳理这两条公理的最小前置（见 QUEUE 的 Q8 记录 (1)–(5)），
没有哪种不建随机层、又能逐字对应论文的写法。**所以没写 axiom。**

**落地了**：`RBM3D/Graph/Expansions.lean`（无 axiom）——`∂_{h_{αw}} G_{ij} = −G_{iα} G_{wj}`，
也就是 `(Owx)` 第三项产生 `Model.lean` 那三条新边的确定性一步。全库 323 条声明，审计不变。

**另外**：两条展开的出处是 `[yang2021delocalization]` Lemma 3.5 / 3.14，不是工单写的 `[yang2024Del]`。

**需要决定**：A（建最小随机层再写 axiom）/ B（推荐：Phase 1 不写 axiom，蓝图灰节点）/ C（不推荐）。详见 QUEUE。

## 2026-09-19 · Claude Code · Q9 完成（演化核与 `lem:sum_Ndecay`）

新文件 `RBM3D/Kernel/Evolution.lean`：定义 `ThetaN`（`def:op_thn`）和 `UN`（`def_Ustz`），都建在 `Theta` 上；
证明了 `(eq:decompUalt)`、`(Xi_infint)` 和 `lem:sum_Ndecay`（`norm_UN_le : ‖U^(n)∘A‖_∞ ≤ ((1-s)/(1-t))^n ‖A‖_∞`）。
不依赖接口公理。全库 338 条声明，审计干净。Q13 现在可以解锁。

## 2026-09-19 · Claude Code · Q10 完成（尾函数）

新文件 `RBM3D/Defs/Tail.lean`：`tailT`（`𝒯_t`）、`tailW`（`wT^ℓ_{t,D}`）和实数版 `BparamR`；
证明了非负、`𝒯_t(0) = B_{t,0}`、单调性、`wT ≥ W^{-D} > 0`；L325 那句话拆成两条引理
（`zeroMode_le_of_ge`，常数 `2^{d-1}`；`ellT_eq_of_le` + `exp_tail_ge`，常数 `e⁻¹`）。全库 361 条声明，审计干净。
Q11、Q12 现在可以解锁。
