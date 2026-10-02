# RBM3D 决定记录（总调度维护；先原话，后落实）

## §1 团队与工作方式（Jun，2026-10-02：「在 RBM3D 文件夹里把这些流程安排的方法写在他们的相关文件里，然后再写一个 prompt 给总调度」）

- 2026-10-02 16:48 UTC，RBM2D 的总调度 V2 把 RBM2D 的三方团队框架写进本仓库，覆盖旧工作模式：`CLAUDE.md`、`.claude/agents/*.md`、`.claude/settings.json`、`docs/claude-team/`（TEAM、STARTUP、hb.sh、tools、DISPATCHER-PROMPT.txt）、`docs/queue/CONTROL.md`、`docs/tickets/README.md`、`docs/reports/README.md`、`docs/supervisor/`、本文件、`docs/HANDOFF.md`、`docs/ROUTES.md`、`docs/rework-ledger.md`。旧的 `CLAUDE.md`、`docs/TASKS.md`、`docs/QUEUE.md` 移进 `docs/archive/2026-10-02-old-workmode/`。
- RBM2D 定下、在本仓库直接生效的常规见 TEAM §9（模型档位与自动升级、Fable 子代理、流程自动、并行 4、接口规则、检查文件名字核对、尺度统一、心跳、简单任务、外部输入版本、收尾发布、CONTROL 归档）。
- 旧工作模式留下的 `docs/PLAN.md`、`docs/STATUS.md`、`docs/paper-deltas.md`、`docs/stochastic-audit.md`、`docs/mathlib-api.md`、蓝图与 Lean 文档串里的说法，一律按未核实处理（CLAUDE.md §5.10）。

## §2 目标与口径（待 Jun 确认，按顺序一次问一件）

1. **范围与验收终点**（**已定，见 §3**）：做整篇论文（含随机层 §3–§8，照 RBM2D 的路线）还是只做旧计划的确定性内核？做整篇的话，终点是论文 §2 的哪几条主定理（逐条列出，钉文写在 `RBM3D/Endpoints.lean`，冻结前由覆盖摸底单核对）。
   - （调度 V1 补，2026-10-02 17:02 UTC，按 PDF 编号）论文 §2 的主结果共六条：Thm 2.1 Delocalization（`MR:decol`）、Thm 2.2 Local semicircle law（`MR:locSC`：`(G_bound)`、`(G_bound_ave)`）、Thm 2.3 QUE（`MR:QUE`：`(Meq:QUE)`、`(Meq:QUE2)`）、Thm 2.4 Bulk universality（`Thm: B_Univ`）、Thm 2.5 Quantum diffusion（`MR:QuDiff`：`(eq:diffu1)`、`(eq:diffu2)`、`(Meq:QdS1)`、`(Meq:QdS2)`）、Thm 2.7 block Anderson 模型（`MR:decol_BA`，四项）。前五条都带耦合参数 `W^{-d/2+𝔡} ≤ λ ≤ 𝔡^{-1}`（`(eq:WO)`）。
   - Thm 2.7 由 §8（`sec:ext-to-BA`）与 App. B.3 证明，额外引用 [RBSO1D] Lemma 3.3、3.9、§7.1、§7.3，[LeeSchSteYau2015] Lemma 3.5，[Aizenman_book] Thm 10.5；还需要自由卷积 `m(z,λ)`、`M^{(B)}`、谱边 `e_λ` 的确定性理论。这些在 RBM1D/RBM2D 里都没有。
   - 选项：A 六条全做；B 只做随机带状矩阵的五条（2.1–2.5），2.7 以后另定；C 只做旧计划的确定性内核（§2.5、App. A、App. B，随机层不做）。
2. **论文忠实度**（**已定，见 §4**）：照 RBM2D §5 的口径（以论文为唯一来源；笔误、必要条件、等价表述可小改并记 paper-deltas；实质改动由 Jun 定）？
3. **被引结果的处理**（**已定，见 §5**）：论文引用别处的结果（例如 `lem_propTH` 性质 5–8、附录 B 引的三条展开引理）——作为授权的外部输入（Lean 里写成显式假设，不用 `axiom`），还是内部证明？旧模式在 `Test/Axioms.lean` 里留了「接口公理」白名单，新规则只许三条标准公理，需要 Jun 定是否改写成假设。
   - （调度 V1 核对，2026-10-02 17:02 UTC）`RBM3D/Test/Axioms.lean` 的 `interfaceAxioms` 是空表，全库 grep 没有 `axiom` 声明；被引结果已写成假设 `Prop`（`borrowedProps`：`ThetaDecay`、`ThetaDecayShort`、`ThetaDiffOne`、`ThetaDiffTwo`、`ThetaZeroMode`、`PropTH`、`Loop.KTreeRep`）。所以与 CLAUDE.md §5.3 不冲突；本项只剩「哪些被引结果授权为外部输入」。
   - （调度 V1 清点，2026-10-02 17:08 UTC；grep 全部 TeX 的 `\cite`，只列证明链上承重的）按来源分五组：
     1. [YY_25]（= RBM1D 的论文，arXiv:2501.01718）与 [DYYY25]（= RBM2D 的论文，arXiv:2503.07606）：Lemma 2.8（`zztE`）、2.11、3.4（`tree-representation`）、3.6、3.10、3.11、4.1、5.1、5.3（`Sol_CalL`）、5.5（`lem:DIfREP`）、5.7、5.15，§5.1、§5.3、§5.6，(5.109)、(5.118)；[DYYY25] Thm 2.4、2.6 的证明、Lemma 2.14、§7（CLT 相消）、(7.39)、§8。两个姐妹项目里都有 Lean 证明，可移植后按 d ≥ 3 重做。
     2. 传播子 `lem_propTH` 性质 5–8：[yang2024Del] Lemma 3.1、(E.19)（(BD1) 原文未写，「analogous」）；[RBSO1D] Lemma 3.10 与 App. B；[DYYY25] Lemma 2.14、§8；[Lawler_book] §2 的 local CLT；[bourgade2019random] Lemma 4.2。
     3. 图展开（§7 light-weight 项、App. B）：[yang2021delocalization] Lemma 3.5、3.10、3.14、3.22 与 §3；[yang2021random] 的 nested property；[yang2024Del] Lemma B.9–B.11 与 App. B（BA 版）。两个姐妹项目里都没有。
     4. block Anderson（Thm 2.7）：[RBSO1D] Lemma 3.3（`zztE_BA`）、3.17、4.16（`tree-representation_BA`）、4.29、Claim 4.30、Lemma 6.1、7.1、§4、§7.1、§7.3、App. A.10、(A.112)、Thm 2.2；[LeeSchSteYau2015] Lemma 3.5；[Aizenman_book] Thm 10.5（Combes–Thomas）；[Biane]（自由卷积密度）。姐妹项目里都没有（RBM2D 有 `Universality/FreeConv.lean`，对象不同，可参考）。
     5. Bulk universality：照 [DYYY25] Thm 2.6 的证明，用 [Xu:2024aa] 的 Green 函数比较；那条证明里唯一的外部输入是 [LANDON20191137]（Landon–Sosoe–Yau）Thm 2.2，即 RBM2D DECISIONS §6 授权的那一条（本文正文不直接引它）。

4. **并行上限**（**已定，见 §6**）：默认 4；RBM2D 的中枢同时在跑时是否先用 3。
5. **从 RBM2D 移植**（**已定，见 §7**）：允许并鼓励（CLAUDE.md §5.2 已写）；是否有不想照搬的部分。

## §3 验收终点：六条主结果全做（Jun，2026-10-02 17:05 UTC：「A」——回答 §2 第 1 项，选项 A = 六条全做，含 block Anderson 模型）

- **终点**：论文 §2 的六条主结果，按原文陈述（偏差按 §2 第 2 项的口径处理），`d` 为参数、`3 ≤ d`：
  1. Thm 2.1 Delocalization（`MR:decol`，`(eq:psikLinfty)`）；
  2. Thm 2.2 Local semicircle law（`MR:locSC`：entrywise `(G_bound)` 与 block-averaged `(G_bound_ave)`）；
  3. Thm 2.3 QUE（`MR:QUE`：`(Meq:QUE)` 与 `(Meq:QUE2)`）；
  4. Thm 2.4 Bulk universality（`Thm: B_Univ`，`(eq:universality)`）；
  5. Thm 2.5 Quantum diffusion（`MR:QuDiff`：`(eq:diffu1)`、`(eq:diffu2)`、`(Meq:QdS1)`、`(Meq:QdS2)`）；
  6. Thm 2.7 block Anderson 模型（`MR:decol_BA`）：上面 1–5 在 BA 模型下的对应陈述（`2-κ` 换成 `e_λ-κ`；`m`、`M` 取 `(self_m)`、`(def_G0)`；量子扩散用 `(def:Theta_BA)` 的 `Θ^{(±)}M^{(±)}`）。
  前五条带耦合参数 `W^{-d/2+𝔡} ≤ λ ≤ 𝔡^{-1}`（`(eq:WO)`）与 `W ≥ N^𝔠`（`(Main_DEL_COND)`）。另加它们实际依赖的内部结果。
- **完成合同**（沿用 RBM1D、RBM2D）：带未证假设的条件定理、特例、有限例子都不算论文结论；终点声明只能依赖 §2 第 3 项授权的外部输入，其余一律内部证明。
- **落实**：
  - 终点钉文写在 `RBM3D/Endpoints.lean`，冻结前由覆盖摸底单核对（TEAM §3）；写法参照 RBM2D 的 `RBM2D/Endpoints.lean` 与 `RBM2D/Main/`（只读，按 CLAUDE.md §5.2 移植并逐条对照本文）。
  - Thm 2.7 额外引用的结果（[RBSO1D] Lemma 3.3、3.9、§7.1、§7.3，[LeeSchSteYau2015] Lemma 3.5，[Aizenman_book] Thm 10.5，以及正文 `lem_propTH` 下「in the setting of the block Anderson model」一句、A.5 引 [RBSO1D, §4] 的 `M` 替换规则）是否授权为外部输入，并入 §2 第 3 项一起问。
  - 旧 paper-delta D6（「只形式化随机带状矩阵模型的传播子」）按本节作废，由总调度在 paper-deltas 里标注。
  - 随机层（§3–§8）照 RBM2D 的做法开 gate；具体路线（真路径/单时刻律的分工）在设计单里定，路线级选择报 Jun（TEAM §4）。
  - 覆盖摸底单以这六条为终点清单；何时写票，等 §2 其余各项定下来，或 Jun 同意提前摸底。

## §4 论文忠实度（Jun，2026-10-02 17:06 UTC：「b」——回答 §2 第 2 项）

- **口径 (b)**（同 RBM1D、RBM2D §5）：以 `paper/2507.20274-inventiones-submission.pdf` 为唯一来源。三类微小改动（明显笔误、必要的附加条件、等价表述）由总调度逐条签字并记入 `docs/paper-deltas.md`，不逐条问 Jun；改动论文假设或结论的实质性修改，由 Jun 决定。证法不同、陈述更强、纯 Lean 写法差异，照常记录，不算实质改动。
- **旧条目 D1–D16**（旧工作模式写，未核实，CLAUDE.md §5.10）：不自动生效。哪张票用到哪一条，总调度先对照论文原文与 Lean 签名核一遍，再按本节归类（D6 已按 §3 作废）。新条目由票的报告以 `T####a` 提出，总调度续编号。

## §5 授权的外部输入（Jun，2026-10-02 17:13 UTC：「先A吧后期可以改动」——回答 §2 第 3 项，选项 A = 只授权 Landon–Sosoe–Yau Thm 2.2，同 RBM2D §6）

- **唯一授权的外部输入**：[LANDON20191137]（Landon–Sosoe–Yau 2019，Fixed energy universality of Dyson Brownian motion）Theorem 2.2，取复 Hermitian（GUE）版本，只用于 Thm 2.4（`Thm: B_Univ`）证明中照 [DYYY25] Thm 2.6 做的那一步（`H_{t*}` 与 GUE 的比较）。
  - 按单位密度读（RBM1D paper-deltas T1654a：[32] 的 (2.9) 漏了 `ρ^{-k}`，Jun 在 RBM1D 确认为笔误）；复 Hermitian 版本在原文未明写——两点都记 paper-deltas。写票时预审与审核在 d ≥ 3 的具体参数下重做两边的极限核算（TEAM §8 教训 14），逐条核对前提；按 TEAM §9.12 核对作者最新 arXiv 版本，版本号写进钉文文档串。
  - Lean 写法可照 RBM2D 的 `RBM.Univ.L32`（`RBM2D/Main/BUnivHolds.lean`），移植时按 CLAUDE.md §5.2 注明出处并重核。
- **其余一律内部证明**：DECISIONS §2 第 3 项清点的第 1–4 组全部在内——[YY_25]/[DYYY25] 的结果（从 RBM1D/RBM2D 移植后按 d ≥ 3 重做）、`lem_propTH` 性质 5–8、§7 与 App. B 的图展开引理、block Anderson 用到的 [RBSO1D]、[LeeSchSteYau2015] Lemma 3.5、Combes–Thomas、[Biane]，以及 [Xu:2024aa] 的 Green 函数比较。
- **可改**：Jun 说「后期可以改动」。某条内部证明代价明显过大时，总调度单独问 Jun 是否授权那一条，附工作量估计与该条在终点中的位置；未获授权前照内部证明做。
- 旧 paper-deltas D5、D10（接口写成 `Prop`、`(Owx)`/`(Oe2x)` 不作公理）中「被引结果当假设」的部分，作为中间写法仍可用，但终点不得依赖除本节以外的未证假设（§3 完成合同）。

## §6 并行上限（Jun，2026-10-02 17:15 UTC：「4」——回答 §2 第 4 项，总调度建议的是 4）

- CONTROL 保持 `parallel: 4`（同时最多 4 条工单 Workflow）。RBM2D 的中枢仍在跑发布清理（17:13 UTC 时 1 张在做）。
- 以后要提到 5–6，由总调度问 Jun（资源级）。

## §7 移植 RBM1D/RBM2D 与随机层默认路线（Jun，2026-10-02 17:18 UTC：「A」——回答 §2 第 5 项，选项 A = 全部照搬）

- **移植**：照 CLAUDE.md §5.2：RBM1D、RBM2D 只读；可把其 Lean 陈述、证明、辅助引理复制进本单唯一可写文件再改；注明出处（项目、文件:行、提交号）；逐条对照本文按 d ≥ 3 重核（索引 `Zd d L`、`W^d`、`N = (WL)^d`、`ℓ_t`、`B_{t,K}`、λ 的出现处与全部指数）；公开名查重。
- **随机层默认路线 = RBM2D 的路线**（RBM2D DECISIONS §10，源自 RBM1D）：在间距 `N^{-C}` 的网格时刻上用独立高斯增量构造真路径（每个网格时刻与单时刻模型同分布，且是马尔可夫过程）；论文用停时的地方（本文 `Sol_CalL` 的 `τ`、`lem:DIfREP`、Step 2 的 `(eq:def2_stopping)`）在这条路径上做；BDG 改用网格上的 Azuma–Hoeffding 加 Doob；其余各步只用单时刻律。
- **照本文另做**（d ≥ 3 特有）：Step 2 的 `J_{u,D}`/Gronwall 论证与 `(Eq:Gdecay_w)`；§7 light-weight 项与图展开；Steps 3–5 中 `λ^2/L^d ≤ 1-t ≤ λ^2/L^2` 等新区间；`lem_propTH` 的 d 维证明；block Anderson（§8、App. B.3）。
- **改路线**：设计单发现 RBM2D 的路线在某处不适用时，路线级改动报 Jun（TEAM §4），不自行换。

