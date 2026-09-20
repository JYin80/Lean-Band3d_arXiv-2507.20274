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

## 2026-09-19 · Claude Code · Q11 进行中（K0 落地）

Q11（`lem:propT`）是附录 A 里分析量最大的一条，要好几轮心跳，拆解计划 K0–K5 见 QUEUE 的 Q11 条目。
本轮落地 **K0**：新文件 `RBM3D/Defs/Shells.lean`，`card_sphere_le : #{x ∈ Z_L^{d+1} : |x| = r} ≤ 2^{d+1}(r+1)^d`。
全库 389 条声明，审计干净。**Q11 保持 CLAIMED**，下一步 K2（径向和）。

## 2026-09-19 · Claude Code · Q11 进行中（K2 落地）

新文件 `RBM3D/Defs/RadialSum.lean`：`sum_radial`（按球壳求和）和 `sum_radial_exp_le`（K2：`Σ_x (|x|+1)^{-(d-2)} e^{-κ√(|x|/ℓ)} ≤ 2^d·32(1+720/κ⁶)·ℓ²`）。
逐项用 `e^y ≥ y⁶/6!` 加望远镜和，没有积分比较。Q11 仍 CLAIMED，下一步 K3（卷积拆分）。

## 2026-09-19 · Claude Code · Q11 进行中（K3 落地）

新文件 `RBM3D/Defs/Convolution.lean`：`sum_conv_le`，即 A.3 那条只在 `ℝ^d` 上陈述、没有证明的「基本微积分事实」的格点版：
`Σ_c P(a−c)E_{ℓ₁}(a−c)·P(c−b)E_{ℓ₂}(c−b) ≤ C ℓ₁² P(a−b)E_{ℓ₂}(a−b)`，对所有 `1 ≤ ℓ₁ ≤ ℓ₂`。
Q11 剩下的是 K4/K5：把 `𝒯_u`、`𝒯_t` 拆成「衰减项 + 零模项」，分两个区制拼装。Q11 仍 CLAIMED。

## 2026-09-19 · Claude Code · Q11 完成（`lem:propT`）

`Kernel/PropT.lean`：`propT`（`(TTT2)`，两个区制，常数显式，`d ≥ 2`），以及 `propT_i`、`propT_ii`。
证明链是 K0 球壳计数 → K2 径向和 → K3 格点卷积（论文那条 `ℝ^d` 微积分事实的离散版，完整证明）→ K4/K5 拼装。
不依赖接口公理。全库 434 条声明，审计干净。
**Q12（`claim:TTk`，同文件）现在可以开工。**

## 2026-09-19 · Claude Code · Q12 暂停（Jun 叫停心跳）——已认领，还没写 Lean

读完 A.4 后的两点订正，**开工前请先看**：

1. **A.4 里的函数是 `𝖳_t`（`\sT`，`main.tex` L209 定义为 `\mathsf T`），不是 `𝒯_t`。** 定义在 `7_8_light_weight.tex` L23：
   `𝖳_t(r) = (g²+|1−t|)^{-1/2} W^{-d/2} (r+1)^{-(d-2)/2} e^{-½√(r/ℓ_t)}`，
   即 `W^{-d}·(𝒯_t 的衰减部分)` 的平方根，**不含零模项**。QUEUE 里 Q12 的公式写成了 `𝒯_t(…)`，需要改。
2. **`(eq:TtTt)` 带前提**：只在 `|x_i−α| ∨ |y_i−α| ≤ ℓ` 时成立（原文 "For 1 ≤ i ≤ r"）。去掉前提会失效：
   例如 `x = y`、两个距离都 `≫ ℓ`，右边 `(|x−α|∧|y−α|+1)^{-(d-2)/2}` 远小于左边。

打算的 Lean 做法（还没写）：定义 `sfT`（`𝖳_t`，用 `Real.sqrt` 写半次幂）和 `Ψ_t = √(W^{-d}B_{t,0})`；证明两条初等事实
`𝖳_t(0) ≤ Ψ_t`、`𝖳_t(s) ≤ 𝖳_t(0)(s+1)^{-(d-2)/2}`；`(eq:TtTt)`（常数 `2^{(d-2)/2}`，靠 `√` 次可加和
`|x−y| ≤ 2 max`）与 `(eq:KtKt)`（常数 1）；再加一条**情形覆盖**引理：每对 `(x_i,y_i)` 要么两距离都 `≤ ℓ`（用 TtTt），
要么交换后 `|y_i−α| > ℓ`（用 KtKt）——这正好核对第三轮改的下标范围（case 2：`2 ≤ i ≤ k`；case 3：`1 ≤ i ≤ k`），
读下来这两处修正是对的。求和版 `(eq:key_T_reudce)`（带 `≺` 和 `ℓ ≤ (log W)^{10} ℓ_t`）不在这一步里，建议单开工单。

## 2026-09-19 · Claude Code · Q12 完成 + **T0 解除，`lake build` 已通**

**磁盘腾出来了**（`~/Lean_proof` 所在卷现在 112G 可用），`lake exe cache get` + `lake build` 一次成功，
`RBM3D/.lake` 已建好。**从此按 CLAUDE.md 的正规回路验证：`./check.sh` → `build.log`。**
本轮 `./check.sh`：`errors: 0`、`exit=0`、451 条声明、审计干净。

**Q12 完成**（`Kernel/PropT.lean` 的 `section TTk`）：`sfT`（`𝖳_t`）、`PsiT`（`Ψ_t`）、两条初等事实、
`(eq:TtTt)`（常数 `2^{(d-2)/2}`，带前提 `|x−α| ∨ |y−α| ≤ ℓ`）、`(eq:KtKt)`（常数 1），
以及 `sfT_pair_cases`（情形覆盖，核实第三轮改的下标范围是对的）。求和版另开 **Q20**。

## 2026-09-19 · Claude Code · Q19 完成 —— **全项目零公理**

`Propagator/Interface.lean` 的 5 条 `axiom` 改成 `Prop` 定义 + `structure PropTH`（陈述一字未动，
默认假设变成前件）；`Test/Axioms.lean` 的 `interfaceAxioms` 清空。审计现在报「No interface axioms」，
只允许 `propext` / `Classical.choice` / `Quot.sound`，与 RBM1D / RBM2D 同标准。反向测试通过（`sorry` 与野生 axiom 仍被拦下）。
`./check.sh`：`errors: 0`、`exit=0`、464 条声明。文档连带更新：`paper-deltas.md` D5/D10、`README.md`、`Basic.lean`。
**用到这 5 条的定理今后写成 `(hP : PropTH d g m)` 参数**，取 `hP.decay` 等；Q13、Q16、Q17 是第一批使用者。

## 2026-09-19 · Claude Code · 接口修正：`(prop:ThfadC_short)` 限定 `σ₁ = σ₂`

做 Q13 接分析部分时发现的**真缺陷**（原 axiom 就有，Q19 只是逐字搬过来）：性质 5' 原先对任意 `‖m‖ = 1` 陈述，
而 `σ₁ ≠ σ₂` 对应谱参数 `1`，那时 `Σ_b Θ_{t,0b} = (1−t)⁻¹` 发散、右端却与 `t` 无关且求和有界——**该陈述为假**。
它当 axiom 的那段时间，项目其实是不一致的（公理审计查不出这种错）。

**已修**：`ThetaDecayShort d g m` 现在讲 `t·(m*m)`（即 `m(σ)²`）并要求 `0 < m.im`；
`PropTH` 只打包性质 5/6/7/8；新文件 `RBM3D/Test/InterfaceShape.lean` 的 `not_decayShort_at_one`
**机器证明了原写法在谱参数 `1` 处不成立**。记在 `docs/paper-deltas.md` 的 D11。
`./check.sh`：`errors: 0`、`exit=0`。

## 2026-09-19 · Claude Code · Q13 完成（`lem:sum_decay_nonzero`）

`Kernel/Evolution.lean`：`norm_zeroModeSet_UN_le`——`‖Q^(A) ∘ U^(n) ∘ 𝒜‖ ≺ ‖𝒜‖`（`1−s ≤ g²/L²`，`A ⊇ I_diff(σ)`）。
结构部分是 `tensorKer` + `Q^(A)` 穿过张量核；分析部分用两条接口假设（性质 5' 与性质 8），
关键代数事实是 `projMat_mul_Theta : Proj·Θ = Θ̊`。`./check.sh` 全绿。
**第一批真正使用接口假设的定理**——签名里直接写着 `ThetaDecayShort` / `ThetaZeroMode`，借用了什么一眼可见。

## 2026-09-19 · Claude Code · Q21 完成（逐字核对四条接口陈述）

结论：性质 5 与论文一致；性质 6、7 的 `|r| ≲ |a|` 原先写成 `|r| ≤ |a|`，**已改成忠实的 `∀ c > 0`** 形式（D12）；
性质 8 与论文一致，并新增反例 `not_zeroMode_without_removal`——把 `Θ̊` 换成 `Θ` 在谱参数 `1` 处可证伪，
说明零模去除是这条估计的全部内容。常数允许依赖 `g`、`m` 记为 D13（有意的弱化）。
`./check.sh` 全绿。**目前接口相关的两个负面测试都在 `RBM3D/Test/InterfaceShape.lean`，随全量构建跑。**

## 2026-09-19 · Claude Code · Q14 完成（典范树划分与边值）

新文件 `RBM3D/Loop/Partition.lean`：`TSP`（不交叉对角线集合，沿用 RBM1D 的表示）、`thetaEdge`、
`polyVal`/`treeVal`/`treeSum`、`GammaN`（含 `∏ m(σ_i)`）、`GammaSum`。自检 `TSP_three`/`TSP_four`/`card_TSP_five`，
验收 `treeVal_four_nil`（`n = 4` 星图）。不依赖接口假设，`./check.sh` 全绿。
**Q15 解锁**，且因为数据结构与 RBM1D 对齐，`eq_Ktree` 可以考虑移植 `RBM1D/Loop/TreeRep.lean` 而不是当公理。

## 2026-09-19 · Claude Code · Q17a 完成 —— **论文第三轮新加的那条估计，Lean 给了独立背书**

`RBM3D/Kernel/SumDecay.lean` 的 `latticesum_d3`：`(eq:latticesum_d3)` 完整证明，常数显式，不依赖接口假设。
**这是整篇论文附录里唯一一处「新数学」**（第三轮才补进去的），现在它在 Lean 里站住了。
证明没有按 `d = 3` / `d ≥ 4` 分情形：逐点拆成两个径向函数之和，按球壳求和后归结到调和和 `Σ 1/r ≤ 1 + log M`，
`log` 自然只在 `d = 3` 时是必需的。附带的可复用件：`sum_inv_Icc_le`（调和和）、`sum_radial_tail_le`（径向尾和）。
Q17b（`lem:sum_decay` 本体，要用 `ThetaDecay`）仍待做。

## 2026-09-19 · Claude Code · Q15 完成（陈述层）+ 开出 Q22（移植）

**评估结论**：`eq_Ktree` 走移植超过一拍，按工单备选方案执行——陈述层做实，`eq_Ktree` 按假设写，移植另开 Q22。
**卡点不在行数，而在前置**：RBM1D 的 ODE 唯一性路线要先能对 `t` 求导 `Θ_t`（它的 `Propagator/Deriv.lean`），
RBM3D 的传播子层目前只有代数与范数，没有求导层。Q22a 就是补这一层。

**本轮落地**（`RBM3D/Loop/TreeRep.lean`，零 sorry，审计仍为空）：`LoopIdx` 与 cut-and-glue 算子（与 RBM1D 同构）、
`treeEqRhs`（`(pro_dyncalK)` 右端）、`MLoop`（初值）、`IsKLoop`（`Def_Ktza` 逐条谓词）、`KTreeRep`（`eq_Ktree` 作为假设）。
自检 `treeEqRhs_two`：`n = 2` 的右端与论文的两回路方程一致（靠 `S^(B)` 对称性对上哑指标顺序）。
**`KTreeRep` 的形状与 `PropTH` 一致，Q22 落地时可原地替换、下游零返工。**

## 2026-09-19 · Claude Code · Q18 完成 —— **借用开始承重了**

审计报告改成分类计数：**283 定理 / 132 定义 / 0 公理**（过滤编译器生成的，用 `isInternalDetail`、
`isAuxRecursor`、`isNoConfusion` 等现成判定）。原来那个「389 条声明」把递归子、equation lemma 都算进去了，是虚高。

**更要紧的一行**：审计现在报「有多少条定理的类型里带着接口假设」，并排除接口自身的投影。
结果 **`ThetaDecayShort: 2`、`ThetaZeroMode: 2`，其余为 0**——这两条正是 Q13 证的
（`exists_norm_uKer_same_le`、`exists_norm_projMat_mul_uKer_le`、`norm_zeroModeSet_UN_le`）。

**这就是工单说的那个时刻：借来的结果第一次真正承重。** 在此之前（Q13 之前）全项目没有任何结论依赖论文引用的估计；
现在有了，而且**在定理的签名里写着**，不需要读证明也看得见。往后这几个数只会增长，
减少的唯一方式是把对应的接口假设证出来（`docs/PLAN.md` 阶段 8 与 Q22）。

## 2026-09-19 · Claude Code · Q16 部分完成（`n = 2` 与工具），一般 `n` → Q25

`RBM3D/Loop/PureLoop.lean`：`norm_Theta_same_le_exp`（`(prop:ThfadC_short)` 的可用形状）、
`sum_exp_decay_conv`（指数卷积，一半衰减付给三角不等式、一半付给求和）、`pureLoop_two`（`res_pureKes` 的 `n = 2`）。
`(Kn2sol)` 按惯例写成假设 `KTwoFormula`。

一般 `n` 需要对 `polyVal` 递归做归纳（每次分裂用一次 `sum_exp_decay_conv`、`c` 减半），工具已备好，另开 Q25。
审计：286 定理，`ThetaDecayShort` 承重 2 → **4** 条。

## 2026-09-19 · Claude Code · Q17b 部分完成（两块零件），三条结论 → Q26

`Kernel/SumDecay.lean`：`(eq:decomp_U2)`（`UN_apply_eq_sum_powerset`，靠 `Finset.prod_add` 按子集展开）
与 `(eq:decayXi)`（`norm_XiKer_apply_le`，由接口假设 `ThetaDecay` 推出）。后者的三个技术点：
零模项用 `zeroMode_le_of_ge_mul` 吸收、`S^(B)` 的最近邻支集（新引理 `SB_apply_eq_zero_of_one_lt`）
把廓线从 `|c−b|` 搬到 `|a−b|`、行和为 1 吃掉对 `c` 的求和。

三条结论（`sum_res_1` / 非交替 / 和零）留给 Q26，并在那里写明**一个容易踩的坑**：
直接用 `‖Ξ‖_{∞→∞}` 得到的形状比论文claim的弱，必须走 `(deccA0)` 的球内截断加 `(1−s)ℓ_s² ≲ g²+|1−s|` 才凑得出来。

审计：291 定理，`ThetaDecay` 承重 0 → **1**，`ThetaDecayShort` 4，`ThetaZeroMode` 2。

## 2026-09-19 · Claude Code · Q20 部分完成（`(eq:key_T_reudce)` 的确定性版）+ 蓝图整体更新

`Defs/RadialSum.lean`：`sum_shift`、`sum_ball_min_pow_le`（Appendix A.4 的格点和
`Σ_{α∈D}(|x−α|∧ℓ+1)^{−(d−2)} ≤ C_d ℓ²`，`D` 任意含于 `a` 的 `ℓ`-球）。
`Kernel/PropT.lean`：`sfT_antitone`、`wfac` 一族、`sfT_pair_le`、`prod_sfT_pair_le`、
`prod_wfac_le_two`、`key_T_reduce`。

**两处比论文省的地方**（D14、D15）：三种情形在逐点层面合并成一条，`2^{2k}` 个 `D_{≤ℓ,𝛔}`
分块不需要；`|D_{≤ℓ}| ≲ ℓ^d` 的体积计数也不需要——以 `a` 为心的第二份 K2 自己带着体积因子。
留给 Q29 的是 `Ψ_t²ℓ² ≺ (W^dη_t)^{-1}` 的吸收，那也是全项目第一处真要用 `DetDom` 的地方。

顺手：修掉 `Loop/PureLoop.lean` 的 `if_false` 弃用告警（现在 0 warning）；
合并了重复开出的两条 Q25；我的 `lem:sum_decay` 工单与 Cowork 的审计工单撞号，已按
QUEUE 顶部的分号约定改为 Q28（我的新工单从 Q29 起）。

**蓝图**（`blueprint/src/content.tex`，自 Q11 以来第一次动）：抬头那段「目前没有任何节点带
`\lean{}`，因为 RBM3D 还一行都没编译过」已经严重过期，改写；给所有已证节点打上
`\lean{} + \leanok`，给七条接口 `Prop` 只打 `\lean{}` 不打 `\leanok`（陈述在、证明不在）；
五条传播子节点不再自称 axiom（Q19 之后全项目零公理）；新增 A.4 与 A.5 两组节点
（`def:sfT`、`lem:TTk-pointwise`、`lem:ballsum`、`lem:TTk-sum`、`lem:latticesum`、
`lem:sumdecay-parts`、`def:tsp`、`ax:KTreeRep`、`ax:KTwoFormula`、`lem:pureloop`），
每条都写明「还差什么、是哪张工单」。所有 `\lean{}` 名字都拿编译好的环境 `#check` 过，
所有 `\uses` 都能解析。

审计：**304 定理 / 137 定义 / 0 公理**，`ThetaDecay` 1、`ThetaDecayShort` 4、`ThetaZeroMode` 2。

## 2026-09-20 · Claude Code · Q23 完成：**Q22 的前置已拆掉**

`RBM3D/Propagator/Deriv.lean`（新文件）：`continuousAt_Theta`、`Theta_sub_Theta`（预解式恒等式）、
`continuous_matrix_entry`、`hasDerivAt_Theta_apply`（逐元 `∂_ξ Θ = Θ S^(B) Θ`），
外加一条 `hasDerivAt_Theta_mul_apply`：沿 `ξ = tμ` 对实参数 `t` 求导。
多写这一条是因为 Q27 要的是 `∂_t K^(2)`，与 `∂_ξ` 差一次链式法则，放这一层接好比让下游各接一次强。

**`d` 作为参数没有带来任何额外麻烦**：`d` 只出现在类型 `Zd d L` 里，从不参与推理；
`Θ` 的定义、预解式恒等式、`Ring.inverse` 的连续性都与维数无关。与 RBM1D 的唯一差别是
每条引理多带前件 `hS : ‖S^(B)‖ = 1`（按工单要求保留风格）。

**主线现在的状态**：Q23 ✅ → **Q27（`(Kn2sol)`）已解锁，无前置** → Q22a（Grönwall 唯一性）
→ Q22b（树公式存在性）。也就是说 `KTreeRep` 与 `KTwoFormula` 这两条「借来的谓词」
第一次有了可执行的消解路径。

顺手：`docs/mathlib-api.md` 补了一节「求导」（9 个核实过的名字）和一个坑——
`HasDerivAt` 是 `def`，缺 import 时点记号报的是 `HasFDerivAtFilter.xxx 不存在`，会把人引向错误方向；
蓝图补了 `lem:Theta-deriv` 节点（`\lean{} + \leanok`），并写明它是 `ax:KTreeRep` / `ax:KTwoFormula` 的前置。

审计：**309 定理 / 137 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q27 部分完成：`(Kn2sol)` 的存在性这一半

`RBM3D/Loop/Primitive.lean`（新文件）：`kTwo` 及其满足性——`hasDerivAt_kTwo` 证明它解
`n = 2` 的卷积树方程（求导用 Q23 的 `hasDerivAt_Theta_mul_apply`，右端用 Q15 的 `treeEqRhs_two`），
`kTwo_zero` 证明它在 `t = 0` 取 `M`-loop 值。

**PARTIAL 而不是 DONE 的理由**：`KTwoFormula m K` 讲的是**任意**一族 `K`-loop，
本文件证的是「`kTwo` 是一个解」。要把任意 `K` 改写成它，需要「同一 ODE + 同一初值 ⇒ 同一解」，
即 Q22a 的 Grönwall 唯一性。工单标题（「消掉这条假设」）比这一拍实际能做到的强一档。

两件仍然有用的产出：`kTwoFormula_kTwoLoop` 给出 `KTwoFormula` 的**显式见证**
（假设可满足 ⇒ 带着它的定理不是空洞真——这一点审计数不出来，只能靠这样一条定理记录）；
`pureLoop_two_kTwoLoop` 把 Q16 的估计用在显式解上，`KTwoFormula` 当场消失，
只剩真正借来的 `ThetaDecayShort`（它的承重因此从 4 涨到 5）。

**主线**：Q23 ✅ → Q27 存在性 ✅ → **Q22a（Grönwall 唯一性）已解锁，是现在的瓶颈**：
它一落地，`KTwoFormula` 真消掉，且 `KTreeRep` 退成「只欠存在性」。

审计：**317 定理 / 139 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q22a 完成 ⭐ —— **`KTwoFormula` 从假设变成定理**

`RBM3D/Loop/Unique.lean`（新）：结构引理（一条链满长 ⇒ 另一条是 2-loop）、`LoopVec`、
`eq_on_level`（一次 Grönwall）、`isKLoop_unique`。RBM1D 那 250 行**一次编译通过**，
`d` 全程不参与推理，只在标签类型与前因子 `W^d` 里出现。

**这一拍真正的收获在移植之外**：把唯一性用在 `n = 2` 这一层（那里「更短回路已一致」的前提是空的），
与 Q27 的显式解对照，得到

* `kTwoFormula_of_isKLoop`：只要 `K` 是 `[0,1)` 上的一族 `K`-loop、其 2-loop 在每个 `[0,T₀]` 上有界，
  **`KTwoFormula` 成立**——它不再是假设，是定理；
* `pureLoop_two_of_isKLoop`：Q16 的纯回路估计，`KTwoFormula` 消失，只剩 `ThetaDecayShort`。

配套的 `norm_kTwo_le`（显式解的逐元界 `W^{-d}(1-t)^{-1}`）放在 `Loop/Primitive.lean`。

**账目**：项目里「欠下的」少了一条。剩下的代价是一条**先验界**（2-loop 在 `[0,T₀]` 上有界），
那是论文自己沿途证的，不是向外借的。`KTreeRep` 也从「表示定理」退成**只欠存在性**（Q22b）。

审计：**332 定理 / 141 定义 / 0 公理**；`ThetaDecayShort` 承重 5 → 6（新增的那条纯回路推论）。

**主线**：Q23 ✅ → Q27 ✅ → Q22a ✅ → **Q22b（树公式存在性，RBM1D 那边 729 + 2546 行）是唯一剩下的大件**。

## 2026-09-20 · Claude Code · Q22b 第一片：`(eq_Ktree)` 在 `n = 3` 证完

新开 `RBM3D/Loop/TreeThree.lean`。三角形没有对角线（`TSP_three`，Q14），树和就是单个星形；
真正的内容是**星形三条边与 `(pro_dyncalK)` 三个 `(k,l)` 项的一一对应**。
其中 `(1,3)` 那一项的 2-链落在 `S^(B)` 的**左边**，所以求和引理要两条
（`sum_SB_starLeft` / `sum_SB_starRight`），不是一条——这一点在 `n = 3` 上才看得出来。

**`kThree_eq_of_isKLoop`**：任意一族 `K`-loop（只要 2-loop 在每个 `[0,T₀]` 上有界）
的 3-loop 就是树值，不带任何关于解的形状的假设。证法是 Q22a 的 `eq_on_level` 用在 `n = 3`，
长度 2 那一层由 `kTwoFormula_of_isKLoop` 供给。**只要 2-loop 的先验界、不要 3-loop 的**，
因为 `n ≥ 3` 的方程对 `n`-loop 线性、系数正是 2-loop。

两个踩过的坑已写进 QUEUE 的完成记录（给 Q30/Q31）：`HasDerivAt.fun_sum` 与 `HasDerivAt.sum`
的函数形状之别；三重积求导后残留的未 β 归约 `(f * g) t`（要 `Pi.mul_apply`），
以及 `ring` 把 `thetaEdge` 和展开后的 `Theta` 当作两个原子——**先结合律、再展开、最后 ring**。

**Q22b 拆成两张新工单**：**Q30**（`n = 4`，第一次出现内部边，6 个 `(k,l)` 对 4 边 + 2 对角线）、
**Q31**（一般 `n`，对 `polyVal` 递归归纳，RBM1D 那边 2546 行，本项目最大的一件）。

审计：**344 定理 / 143 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q24 完成 ⭐：论文那句「需额外修改以处理 `d ≥ 3`」是什么

`RBM3D/Loop/KBound.lean`（新）：`KLoopBound`（`ML:Kbound` 的逐字陈述，当假设，已登记进审计）、
**`inv_pow_pair_le`**（那处「额外修改」本身，已证）、`not_inv_pow_pair_le_single`（负面测试）。

**结论：那句话指的是 `(eq:ind-step-bound)` 情形 (ii) 第 4 条里的一步**——
两个外部边被长边分解的反对称部分 `f₁` 打到，各带 `(|a−b|^{d−1}+1)^{-1}`，对 `b` 求和时要先拆成

`(x^{d−1}+1)^{-1}(y^{d−1}+1)^{-1} ≤ 2[(x^d+1)^{-1}(y^{d−2}+1)^{-1} + (x^{d−2}+1)^{-1}(y^d+1)^{-1}]`。

**为什么必须不对称地拆（论文没写，这是本拍的审计发现）**：直觉上会把一个 `(d−1)` 因子放大成 1，
但 `Σ_b (|a−b|^{d−1}+1)^{-1}` 在格点上直接发散，连 `Σ_b (|a−b|^d+1)^{-1} ≈ log L` 也发散。
让和收敛的是另一因子剩下的 `d−2` 次幂，而它有用当且仅当 **`d ≥ 3`**——
`d = 2` 时退化成常数、对数回来，`d = 1` 时 `|·|^{d−1} = 1` 根本不带衰减。
**这正是 `[YY_25]` 的一维论证必须改写的地方。**

**没有发现论文掩盖实质困难**：这句话是老实的，改写方向在 `d ≥ 3` 下确实走得通。

**开出 Q32**：拆分之后的格点和 `Σ_b (|a−b|^d+1)^{-1}(|c−b|^{d−2}+1)^{-1} ≲ 1`
（手算量级是 `C/(|a−c|+1)`，三块分割的路线已写进工单；零件在 Shells/RadialSum 里都有）。

顺手把 `KLoopBound` 加进 `Test/Axioms.lean` 的 `interfaceProps`——在 Q26 把审计改成自动发现之前，
硬编码名单至少要跟上新增的假设，否则报告会漏报（这正是 Q26 要解决的毛病，又多了一个实例）。

审计：**346 定理 / 144 定义 / 0 公理**。

## 2026-09-20 · Claude Code · 维护：规则 15 —— `hbdd` 具名为 `TwoLoopBounded`

CLAUDE.md 规则 15 点名的就是我上两拍写下的那条匿名前提（2-loop 在每个 `[0,T₀]` 上有界），
到本拍已扩散到三处签名。现已具名为 `RBM.Loop.TwoLoopBounded`（与 `IsKLoop` 同处
`Loop/TreeRep.lean`），三处一起改，并登记进 `Test/Axioms.lean` 的 `interfaceProps`。

**效果立刻可见**：审计新增一行 `RBM.Loop.TwoLoopBounded: 3`。
改之前它在三个签名里看得见、却在任何汇总里数不到——这正是规则 15 要防的事。
不占工单（硬规则、我自己的代码），Q26 剩下的仍是本体：自动发现 + 分两本账。

审计：**346 定理 / 145 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q25 部分完成：星形树（任意 `n`）与 `res_pureKes` 的 `n = 3`

**先记一条事实**：`RBM1D` 里**没有**纯回路引理（grep 一条都没有）。这块是原创，不是移植。

`Loop/PureLoop.lean`：`sum_exp_decay_centre`，以及 **`norm_sum_prod_le`**——
若 `‖E x y‖ ≤ C e^{-c|x−y|}`，则 `‖Σ_b ∏_{i<n} E(a_i,b)‖ ≤ C^n C(c/2,d) e^{-(c/2)|a_p−a_q|}`
对**任意一对**下标 `(p,q)` 成立，对 `L` 一致。拆法与 `sum_exp_decay_conv` 相同：
总衰减 `Σ_i|a_i−b|` 一半付给三角不等式、一半付给对中心求和。**这覆盖任意 `n` 的星形树**。

`Loop/TreeThree.lean`：**`pureLoop_three`**，`res_pureKes` 在 `n = 3`，
对 3-loop 的形状不带任何假设（`kThree_eq_of_isKLoop` 供给），只剩 `ThetaDecayShort` 与 `TwoLoopBounded`。

**对「最大两两距离」的处理**：不引入 `Finset.max`，而是对**每一对** `(p,q)` 各给一条界——
等价，但下游取哪一对都行，用起来更顺。

**开出 Q33**（带对角线的树，`n ≥ 4`）：它要先证「内部边 `Θ−I = ξS^(B)Θ` 也指数衰减」，
再对 `polyVal` 递归归纳；**并且要等 `KTreeRep` 在 `n ≥ 4` 落地（Q30/Q31）**，
否则只能重新引入假设，与 Q16 的原则冲突。

审计：**349 定理 / 145 定义 / 0 公理**；`ThetaDecayShort` 6 → 7、`TwoLoopBounded` 3 → 4。

## 2026-09-20 · Claude Code · Q26 完成 ⭐：审计自己找前件，报告分两本账

`Test/Axioms.lean` 不再信任手写名单。`scanPremises` 扫环境里 `RBM` 的 `Prop` 值定义，
挑出「某条定理当前件用、而本项目无任何定理证出」的那些；凡落在
`borrowedProps` / `owedProps` / `structuralProps` 三份名单之外的，**构建失败**。

两个判定坑都踩过并处理了：**结构体投影不算证明**（`PropTH.decay` 只是拆包），
用 `isStructure` + `getStructureFields` 精确排除——先试的「名字前缀」粗筛会把
`DetDom.refl` 这种真定理一起排掉、反而把 `DetDom` 误判成未证。

**两本账**：借来的 8 条（论文引用而未证）、欠下的 1 条（`TwoLoopBounded`，承重 4）、
另列 5 条结构性谓词（定义对象本身，不进账但必须显式登记）。
`KTwoFormula` 因 Q22a 已证，**自动**从账上消失——名单时代要手工删。

**反向测试** `Test/AuditNegative.lean`：审计跳过的 `RBM.Audit.Fixture` 里放一条没人证的
`FakePremise`，断言扫描必须报出它；另手工验证删掉 `TwoLoopBounded` 会让构建失败。

顺带：审计自己的辅助定义以前被算进「本项目定义」，现已排除，定义数 145 → **140**。

**已知边界**（写下来备查）：判定靠「没有定理以它为结论」，所以
`theorem foo (h : P) : P := h` 这种同义反复能骗过它。

审计：**349 定理 / 140 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q29 完成：`(eq:key_T_reudce)` 的吸收步，`≺` 第一次真正用上

三块：

* `Defs/Domination.lean` · **`detDom_log_pow`**：`(log N)^m ≺ 1`。这条把「把对数吃进 `≺`」
  从一句话变成一条定理，后面每条带 `≺` 的估计都要用。
  （Mathlib 的 `isLittleO_log_rpow_rpow_atTop` **在根命名空间**，不是 `Real.`。）
* `Defs/Params.lean` · **`Bparam_mul_ellT_sq_le`**：`B_{t,0} ℓ_t² ≤ 3|1−t|^{-1}`，
  前提是 `claim:TTk` 显式写着的 `1−t ≥ ĝ²/L²`，**常数显式**。
  第一项正好给 `|1−t|^{-1}`，零模项给 `2L^{2−d}|1−t|^{-1}`——`d ≥ 2` 用在这里。
* `Kernel/PropT.lean` · **`key_T_reduce_absorbed`**：Q20 的 `Ψ_t²ℓ²` 换成论文右端
  `3Λ²(W^d|1−t|)^{-1}`，`Λ=(log W)^{10}`；`η_t ≍ 1−t` 由 `(eta)` 给出。

**没有把 `η_t` 单独定义进 Lean**：本条里它只以 `1−t` 的形式出现，定义它反而多一层要核对的东西；
将来随机层若需要，再连 `(eq:zt)`、`(eq:BtBt)` 一起对。

审计：**349 定理 / 140 定义 / 0 公理**（新增的都是定理，账目无变化）。

## 2026-09-20 · Claude Code · Q28 部分完成：两块前置 + `lem:sum_decay` 的关键记账

工单点名「前两步要先补」，补了，并顺手把它说「别走捷径」的那一步也证了。

* `Defs/RadialSum.lean` · `sum_ball_pow_le`：球内求和 `Σ(|a−α|+1)^{−(d−2)} ≤ C_d R²`。
  几行——Q20 的 `sum_ball_min_pow_le` 在「被加项与球同心」时那个 `∧R` 截断什么也不做。
* `Defs/Params.lean` · `one_sub_mul_ellT_sq_le`：`|1−s|ℓ_s² ≤ ĝ²+|1−s|`。
* `Kernel/SumDecay.lean` · **`sum_ball_norm_XiKer_le`**：一个 `Ξ` 因子在球上求和，
  代价正好是 `Λ²(ĝ²+|1−s|)/(ĝ²+|1−t|)`——**论文每个因子的记账**。
  三件零件咬合得很干净：`(eq:decayXi)` 给逐元界、球内求和给 `R²`、`(1−s)ℓ_s² ≤ ĝ²+|1−s|` 收尾。

**一次规则 4 的教训**：写前置 ② 时我又写了一遍 `ellT_sq_le`，而 `Kernel/PropT.lean` 里早就有。
编译报重复声明才发现。既然它只是 `(eq:ellt)` 的事实，已把原来那条**下沉到 `Defs/Params.lean`**
（陈述一字未改），PropT 从那里用。**造轮子前先 grep。**

**维护**：QUEUE 里有三处完成记录被我之前的脚本插到了错误的小节（Q27 的落在 Q26 段里、
Q28 的落在 Q27 段里），已归位；同时把 Q23/Q24/Q26/Q29 的小节标题从 OPEN 更新为 DONE。

**开出 Q34**：四步装配本身（`sum_res_1` 的两个归约 + (I) + (II)），路线与注意事项已写进工单。

审计：**357 定理 / 140 定义 / 0 公理**。

## 2026-09-20 · Claude Code · 规则 10 的一次取舍，以及 Q30 的一半

**先记取舍**：Cowork 把随机层工单（Q42 确定性包络、Q43 Stein 三层）提到了队首，
但 CLAUDE.md **规则 10 写着「不碰随机层」**。Q42 的工单正文自己写明目的是
「给出『`≺` ⟹ 矩』的反向桥……Q45 的前提」，Q43 是 Stein——两条都在随机层里。
**本侧不认领**，理由写进了队列的 Q42 小节，并指出可拆出来的那一半
（`‖(H−z)⁻¹‖ ≤ (Im z)⁻¹` 是纯线性代数，与随机矩阵无关）以及一个坑：
那里的 `‖·‖` 是**谱范数**，而本项目全程是 `Matrix.Norms.Operator` 的 **ℓ^∞ 算子范数**，
RBM1D 为此单开了 `Gauss/OpNorm.lean`。**若要开做随机层，应先改 CLAUDE.md 规则 10。**

**然后做了 Q30 的一半**（`Loop/TreeFour.lean`）：
`treeEqRhs_four`（六项索引，链都算出）、`treeVal_four_diag02/13`（两条对角线的树值）、
`treeSum_four`。**边与项的对应在 `n = 4` 第一次完整**：4 条边界边 ↔ 带 2-链的四项，
2 条对角线 ↔ **两条 3-链**相乘的两项——工单的提醒说中了，先做 `n = 3` 是对的。

两处技术记录（给 Q31/Q35）：`cutGlue` 里带数字减法的下标 `simp only` 不算、要 `norm_num`，
之后补 `ring` 处理结合律；`diagList {(0,2)}` 用 `decide` 会卡住（`Finset.sort` 的实例展不开），
`simp [diagList]` 就过。

**开出 Q35**：求导匹配（内部边导数 + 四顶点求和引理 + 配对 + `eq_on_level` 在 `n = 4`）。
证到那里就拿到 `(eq_Ktree)` 的 `n = 4`——**`KTreeRep` 的第一个真正实例**。

审计：**361 定理 / 140 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q43a 完成，以及一次判断错误的纠正

**纠正**：上一拍我以 CLAUDE.md 规则 10「不碰随机层」为由跳过 Q42/Q43。
**那是旧版**——规则 10 在 beat 15 整条重写过，现行文本是「随机层按『没有 Itô』那条路走，
不要去碰 Itô 本身」，Q42–Q46 都不在禁区里。我引的是**会话开始时载入的 CLAUDE.md 快照**。
**教训：认领工单前重读 `CLAUDE.md` 原文。会话里的那份是快照，仓库里的是活的。**
Cowork 已在规则 10 里加了指针（「若你记得的是『不碰随机层』，那是旧版」）。

**Q43a**：`RBM3D/Gauss/Stein.lean`，从 RBM1D 整包搬来，**一次编译通过**。
Cowork 的实测准确：该文件只 import Mathlib，零项目依赖，移植就是「文件 + 换模块文档」。
内容：`p' = −(x/v)p`（**整条路线唯一的概率内容**）、Stein 恒等式的密度形式与测度形式、
有界 `C¹` 形式、复值形式，外加四条可积性辅助。**`d` 一次都没出现**——它是实轴上的一维分析。

审计：**372 定理 / 140 定义 / 0 公理**（两本账不变：新增的全是定理）。

**下一步建议**：Q43b（Stein 矩阵版）要走**重采样**而非 Fubini，但它依赖本项目还没有的
高斯带矩阵模型与生成元层；建议先开模型那条。

## 2026-09-20 · Claude Code · Q43b 部分完成：随机层的卡点是缺一个模型

**实测结论**：Q43b 不是「整包可搬」。`RBM1D/Gauss/SteinMatrix.lean` 第一行就 import
`Gauss.Generator`，后者依赖 `Gauss/Model.lean`（489 行）。**本项目没有模型，而且它不能照搬**——
RBM1D 的指标集是一维的，这里矩阵元由 `Zd d L` 指标、方差廓线是 `SB`。

**这一拍落地了不需要模型的那一半**（`Gauss/SteinMatrix.lean`）：
`integral_mul_gaussianReal_complex'`（**去掉方差非零前提**的一维复值 Stein——
`v = 0` 时高斯退化成 `δ₀`，两边同时为零，正是工单说重采样优于 Fubini 的理由之一），
以及坐标更新工具 `upd` / `measurable_upd` / `continuous_update_coord`，
**按任意指标类型**陈述（RBM1D 那边绑在它自己的指标上；这些其实只是 `Function.update` 的事实）。

**开出 Q48（高斯带矩阵模型）**：随机层真正的前置。工单里写清了最小需求
（Hermite 对称的坐标集、取自 `SB` 的方差廓线、无穷乘积测度、矩阵化），
并提醒 `upd` 那套已按任意指标类型证好、不要重写。

审计：**378 定理 / 141 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q48 完成：高斯模型 + 重采样不变性（Q43b 的卡点解除）

`Gauss/Model.lean`（新，**不是移植**，按本篇论文的模型重写）：
`Vtx = Zd d L × Fin (W^d)`（块标号 + 块内位置）、`svar = W^{-d} S^(B)_{ab}`（逐字 `(eq:variancematrix)`）、
独立坐标 `Coord`/`Omega`/`gvar`/`P`、矩阵 `Hmat` 与 `Hmat_isHermitian`（`(bandcw0)`）。
对角线一个实高斯、非对角两个各半方差，两种情形都满足 `E|H_xy|² = S_xy`。

**`P_map_update`**：`(P ⊗ γ_c).map (upd c) = P`——**随机层唯一用到独立性的地方**，
也正是 Q43b 缺的那条。在可测长方体上用 `Measure.pi_eq` 比较；`upd c` 下长方体的原像还是长方体。

**一处有意的设计差异**：RBM1D 为整个 `N` 序列建一个空间（`Dims`）；
这里按本项目风格**对固定 `d, L, W, g` 建模**，坐标集有限，用 `Measure.pi`。
将来渐近陈述若需要单一空间，再加一层包装，不影响这里的陈述。

审计：**387 定理 / 149 定义 / 0 公理**。

**下一步**：Q43b 只剩「把 Stein 两边推过 `upd c`，Fubini 分离坐标 `t`，内层用一维复值恒等式」。

## 2026-09-20 · Claude Code · Q42a 完成：确定性包络的线性代数核心

`RBM3D/Analysis/Resolvent.lean`。**内容只有一条估计**：对称算子满足 `|Im z|‖v‖ ≤ ‖Tv − zv‖`。
证法：`⟪v,Tv⟫` 对对称算子是实的 ⇒ `Im⟪v, Tv − zv⟫ = −(Im z)‖v‖²`，再 Cauchy–Schwarz。
推论：`T − z` 在 `Im z ≠ 0` 时单射；`Tu − zu = w ⟹ ‖u‖ ≤ |Im z|⁻¹‖w‖`（包络形式）。

**写成算子而不是矩阵是有意的**：本项目 `Matrix` 全程带 ℓ^∞ 算子范数，而预解式界是**谱范数**的陈述，
同一类型上两个不同 instance（我在 beat 19 提醒过的坑）。核心估计里不出现矩阵范数；
另给 Hermite 矩阵在 `EuclideanSpace ℂ n` 上的特化，那里范数无歧义。

**这条界在全空间成立**（只用 Hermite 性，逐点事实），不是「在好事件上成立」——
所以 Stein 要的全局有界天然满足，不需要磨光截断。Q42b 因此解锁。

审计：**393 定理 / 149 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q42b 部分完成：矩与 `≺` 之间的两座桥

三个文件（都是移植 + 文档重新指向本篇论文）：

* **`Defs/StochDom.lean`**：`(stoch_domination)` 与 `w.h.p.` 约定。**逐字核对过**——
  对 `u` 的并集在概率**里面**；论文同段的确定性约定就是已有的 `DetDom`，两者由
  `StochDom.of_unifDetDom` 接上。本项目此前只有确定性那一半。
* **`Gauss/Domination.lean`**：正向桥（矩 ⟹ `≺`，Markov + 并集界）+ 网格论证。
* **`Gauss/Envelope.lean`**：**反向桥**（工单点名的那条）。`≺` 本身推不出矩；
  补一个多项式增长的确定性包络即可，而 Q42a 提供的正是它。

**只搬了通用的一半**：`G`-loop 自身的包络需要 §5 的回路层（`gloop`、`loopMax`）——
本项目还没有，**已开 Q49**（其中还要先定义 `m^{(E)}`，逐字对 `(eq:defmzsc)`）。

**审计当场发挥作用**：移植带进来未登记的前件 `NormStochDom`，构建**直接失败**并点名它，
登记后才过——这正是 Q26 要的效果（名单与实际不符就失败，而不是静默漏报）。

审计：**424 定理 / 157 定义 / 0 公理**；前件扫描 11 条（8 借 / 1 欠 / 6 结构）。

## 2026-09-20 · Claude Code · Q49 部分完成：半圆律层 + `G`-loop 定义层

* **`Defs/Semicircle.lean`**（移植）：`(eq:defmzsc)` 的 `m_sc`、`m^{(E)}`、流 `(eq:zt)`。
  **顺带的收获**：`norm_mE`/`mE_im_pos` 正是接口 `Prop` 带的 `‖m‖ = 1`、`0 < m.im`——
  本项目现在有了这两条前提的**具体见证**，对 Q41（非空洞证书）直接有用。
* **`Loop/GLoop.lean`**：`Eblk`（`E_a`）、`etaT`（`η_t > 0` 当 `|E|<2`、`t<1`）、
  `Gsig`（`G_t(σ)`）、`gloop`（**有序**乘积的迹——矩阵不交换，用 `List.ofFn |>.prod`）、`loopMax`。

**没做也没硬凑**：`(5.2)` 的包络 `|L^(n)| ≤ (η_t^{-1})^n`。分析输入齐了（Q42a），
但「算子范数界 ⟹ 乘积的迹的界」需要 `|tr X| ≤ rank·‖X‖₂` 一类不等式，
**Mathlib 的 `Matrix.trace` 在 ℓ² 算子范数下没有这套 API**。已开 **Q50**，
里面写了两条候选路线（自证 `|tr X| ≤ card·‖X‖₂`，或绕开迹走逐元界）并提醒先算量纲。

审计：**456 定理 / 171 定义 / 0 公理**。

## 2026-09-20 · Claude Code · Q50 完成：`G`-loop 的确定性包络 `(5.2)`

`|L^(n)_{t,σ,a}| ≤ (η_t^{-1})^n`，**逐点、全空间**。

**工单要求先算量纲，算完否定了我上一拍写的第一条候选路线**：
用算子范数 + `|tr X| ≤ card·‖X‖₂` 得到的是 `L^d W^{d(1−n)}η^{-n}`，`n ≥ 2` 时不是 `η^{-n}`——
**矩阵的体积压过了 `E_a` 的小**。正确的路是保留逐元并利用块结构：每个因子只支撑在一个块
（`W^d` 个格点）上且带 `W^{-d}`，所以对内部顶点求和是**平均**。不变量：

`|(∏_{i<k} G_i E_{a_i})_{xz}| ≤ W^{-d}η^{-k}·1(z ∈ [a_k])`，

对因子列表归纳；取迹时花掉最后那个指示函数，正好得 `η^{-n}`。

新增：`Analysis/Resolvent.lean` 的 `isUnit_sub_smul_of_isHermitian` 与 **`norm_inverse_entry_le`**
（逆的逐元界，取一列再用 `PiLp.norm_apply_le`）；`Loop/GLoop.lean` 的 `norm_prod_entry_le`、
**`norm_gloop_le`**。

**修正一句上一拍的判断**：我说「卡在 Mathlib 没有迹范数不等式」——准确的说法是
**那条不等式即使有也不够用**，绕开它才对。

审计：**463 定理 / 171 定义 / 0 公理**。
