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
