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

## §8 第一批放行（Jun，2026-10-02 17:41 UTC：「run」——回答「是否放行 T2001–T2004 并把 CONTROL 改成 RUN」）

- 四个检查文件经 H2 编译全部退出码 0（17:32 UTC）；H3 已把调度文件提交推送（3c11d7b）。
- 放行 T2001（SV-1 覆盖摸底）、T2002（MD-D1 词汇与移植表）、T2003（PT-D1 传播子）、T2004（KL-D1 K-loop），CONTROL 改 `mode: RUN`。
- 开工次序（CLAUDE.md §3 (G)，parallel 4，四张同时）：T2002、T2003、T2004（接口设计）、T2001。

## §9 监督 1745（每日兜底，PASS）两条观察的落实（总调度，2026-10-02 17:59 UTC）

- **O1**（`(prop:ThfadC)` 的常数必须依赖 `𝔡`：`t = 0` 时 `Θ = I`、`B_{0,0} = (1+λ²)^{-1} + L^{-d}`，故 `C ≳ λ²`，在 `λ ≤ 𝔡^{-1}` 下即 `C = C(d, 𝔡)`）：T2003 已要求 `λ ∈ (0, 𝔡^{-1}]` 并把 `𝔡` 依赖记为候选 `T2003a`，覆盖。T2004 已开工（17:53 UTC），票面只写「constants independent of `λ` and `L`」，未写 `λ` 的上界；不中途发 amend（不改目标，只是范围），改为：T2004 报告合并后、写 KL 证明票之前，总调度逐条核对 T2004 的局部 PT 假设限定 `λ ∈ (0, 𝔡^{-1}]`、常数取 `C(d, 𝔡)`（短程取 `C(d, κ, 𝔡)`），并在 `λ = 𝔡^{-1}` 处试一次；不满足的，KL 证明票的钉文照 T2003 的钉文改正（记 paper-delta），不算 T2004 返工。BA 一侧同理。
- **O2**（预算风险提前登记）：LW-D1、BA-D1、PT-D1 的拆单表出来后，先按估计票数对照 25/40/50 预判；某一 gate 的预估票数单独超过 50，开工前单独问 Jun（ROUTES「单独问 Jun」）。

## §10 T2001（覆盖摸底）合并后的签字与落实（总调度按 §4 签字，2026-10-02 19:22 UTC；依据 T2001 审核 RETURN → 修复一次 → PASS，a62eeef）

- **签字接受**（§4 的微小改动；合并成 Lean 文件时逐条记入 paper-deltas，编号届时给）：
  - T2001a（等价/必要条件）：「∃N₀」写成沿尺寸序列的陈述，`size n → ∞` 列入可容许条件，`3 ≤ L` 显式（同 RBM2D T2001a,b）；
  - T2001e（等价）：`𝓑_{η,|x-y|}` 里细格点距离读作 `W·|[x]-[y]|`（块的 l¹ 距离），常数并入 `W^τ`；
  - T2001f（必要条件）：`(Meq:QUE2)` 要求 `A ≠ ∅`；
  - T2001g（笔误）：`zztE_BA`（7_8:1797）的 `|Re z| ≤ 2-κ` 应为 `e_λ-κ`；
  - T2001h（读法，同 RBM2D T2001d,g,h）：`m` 取积分定义（等式由 T2005 证明）、关联函数用特征值求和形式、任意正交特征基。
- **T2001b 定为论文原形**：`(G_bound)`、`(G_bound_ave)`、`(eq:diffu1)`、`(eq:diffu2)` 的 `∩_z` 放在概率之内（1_2:388–399、490–499 字面）。比 RBM2D 的逐点钉文强；网格 + 对 `z` 的 Lipschitz 性（1_2:1228 的 net 论证）是 MA 的证明义务。
- **T2001c 交 Jun**（实质改动）：block Anderson 的 bulk universality（1_2:655）字面上与同一能量 `E` 的 GUE 比较，当 `ρ_N(E) ≠ ρ_sc(E)` 时不成立（摸底报告的数值：`λ = 1`、`E = 0` 时比值 0.4106）。
- **T2001d、T2001l 暂不签**：BA 的支撑 `supp μ_N = [-e_λ, e_λ]`（1_2:624）只在 `L` 为偶数时对称，`L` 固定、`λ` 大时（如 `d = 3, L = 4, λ = 10`）还可以不是区间，这时 `e_λ` 无定义、BA 钉文空真。两种写法（体内条件改成「`E` 到支撑补集的距离 ≥ κ」，或在可容许条件里限 `L_n → ∞` 且为偶数或 `λ ≤ 1`）由 BA 设计单 BA-D1 比较可证性后提出；若要给 Thm 2.7 加假设，交 Jun。
- **T2001i–k（发现）**：旧 `Interface.lean` 五个 Prop 的常数依赖 `(λ, m)`，不能用于 `λ_n → 0`（由 T2003 重钉）；`Gsig`/`gloop` 是时刻 1 的矩阵、`StochDom` 要单一概率空间而 `Gauss.P` 每个尺寸一个（由 T2002 处理）；`norm_zeroModeSet_UN_le`、`pureLoop_*` 排除了负电荷（`0 < Im m`），EK、KL 设计时补上。
- **ROUTES 补行**（摸底报告的 flag 行）：Ward 恒等式（`eq_Ward0`、`eq_Ward`、`lem_WI_K`、`lem_wardineq_K`）归 KL；`[net]`（1_2:1228）、`eq:ukx` 归 MA；`def_G0t`、`eq:opS` 归 MD。
- **第一张证明票**：T2005（F0-1，`msc` = 积分定义，移植 RBM2D `Defs/SemicircleIntegral.lean`，`prover`），立即可开工。其余摸底报告提出的票等 T2002–T2004 的设计。

## §11 block Anderson 的 bulk universality 按密度归一化陈述（Jun，2026-10-02 19:24 UTC：「A」——回答 T2001c，DECISIONS §10）

- **陈述**（Thm 2.7 第 3 项中的 `(eq:universality)`）：对 `|E| ≤ e_λ − κ`（体内条件的写法待 T2001d/l，由 BA-D1 定）、固定 `n`、`O ∈ C_c^∞(ℝ^n)`、任意 `|E'| < 2`，
  `lim_{N→∞} ∫ O(α) [ ρ_N(E)^{-n} p_H^{(n)}(E + α/(Nρ_N(E))) − ρ_sc(E')^{-n} p_GUE^{(n)}(E' + α/(Nρ_sc(E'))) ] dα = 0`，
  其中 `ρ_N` 是 `(self_m)` 的 `m(z,λ)` 给出的密度（`π^{-1} Im m(E + i0)`）。随机带状矩阵模型 `ρ_N = ρ_sc`，取 `E' = E` 即原文 `(eq:universality)`。
- 属实质改动（改 Thm 2.7 的结论形式），由 Jun 定；记 paper-delta（合并成 Lean 文件时编号）。证明路线不变：Landon–Sosoe–Yau Thm 2.2（DECISIONS §5）本身给出按局部密度归一化的形式。
- **落实**：终点冻结票（SV-2）照此钉 `BA_BUniv`；T2001 探针里的 `T2001_BA_BUniv`（匹配 `ρ_sc(E'_n) = ρ_N(E)`）与 `T2001_BA_BUniv_literal`（原文）都不用；UN-D1、BA-D1 的极限核算按此形式做（含 `ρ_N(E)` 的下界与 `E ↦ ρ_N(E)` 的正则性）。

## §12 T2002（MD-D1 词汇与移植表）合并后的签字与落实（总调度按 §4 签字，2026-10-02 23:17 UTC；依据 T2002 审核 PASS，06f2064）

- **词汇决定照 T2002 报告 (b.9) 接受**：细格点 `Idx d L W = Zd d (W*L)` 承载模型与终点陈述，块乘积 `Vtx` 承载 `E_a`、`S`、loop，二者经 `splitEquiv` 桥接；尺寸数据 `Sizes d`（字段 `L W lam`，`lam : ℕ → ℝ` 只受 `WO` 约束）；一个可数乘积概率空间 `seqP`；单时刻流 `seqHflow = √u • seqXmat`，停时处用网格游走 `pathH`（§7）；所有 `≺` 的尺度是 `N = sz.size n = (W n L n)^d`（`StochDomAt … size`；论文 `(stoch_domination)` 本身用 `N^τ`）；能量取序列；BA 用同一词汇（`withLam 0`、`H_0 = λ₀Ψ`、`m, M` 为数据），确定性的 `m(z,λ)`、`M^{(B)}`、`e_λ` 另成一层（BA gate）。
- **移植源提交固定为 RBM2D `c9a24cf`**（T2002 O1）：它含全部文件（包括后来被 RBM2D 死代码清理删掉、但本项目因 §10 T2001b 需要的 `Path/NetLift.lean`、`Main/RegionUnif.lean`）；RBM2D 之后的提交（`99d6fe0` 死代码、`81fca44` 注释清理）不改保留文件的陈述。票面一律写 `c9a24cf`。
- **签字接受的 paper-delta 候选**（§4 微小改动，合并成 Lean 时编号）：T2002a（命名：`lam` = 论文 `\ilambda`，印作 `g`）、T2002b（距离：随机层与终点陈述用论文的 `L^∞`（`zdistInf`），传播子层用已合并的 `l¹`（`zdistD`），二者差常数 `d`）、T2002c、T2002e（已含于 §10 T2001a）、T2002d（坐标约定，平移等价）、T2002f（旧 `Loop/GLoop.lean` 文档串说 `G_t` 而 `Gsig` 用时刻 1 的矩阵：文档串勘误，随 MD-3 改）、T2002g（流的 Lean 写法，§7）、T2002h（`Ring.inverse`）、T2002i（`W^τ` 与 `N^τ` 等价）。
- **拆单**：MD-1…MD-5（报告 (b.6)、portmap E.2）。第一张 MD-1 = T2006（`prover-max`，立即）；MD-2、MD-3 等 MD-1 合并；MD-4 等 MD-1、MD-2；MD-5 等 MD-4。
- **ST 子 gate**（portmap E）：ST-1 Step 1（86 文件 / 29.9k 行保留）、ST-2 Step 2（46 / 31.8k，含 d ≥ 3 新论证，与 LW 设计同步）、ST-3 Steps 3–4（40 / 39.0k）、ST-4 Step 5（17 / 15.1k）、ST-5 Step 6（7 / 6.8k）、ST-6 装配（9 / 3.2k）；UN 58 / 51.6k。设计单 ST-D1、ST-D2、ST-D3 在 MD-1 合并后写；ST-D4…D6 等 ST-D2 的钉文。各子 gate 按 25/40/50 分别计数。

## §13 T2003（PT-D1 传播子）审核 PASS 要求总调度签字：签字与落实（总调度，2026-10-02 23:17 UTC；依据 `docs/reports/T2003-audit.md` §7，d6e6054）

- **签字**：审核对五个钉文、骨架与实例全部 PASS，要签字的只是路线（见下），不是陈述缺陷。报告可以合并（H6，只并报告与 state；探针留在分支）。不算返工。
- **钉文接受**（`Prop5Decay`、`Prop5Short`、`Prop6Diff1`、`Prop7Diff2`、`Prop8ZeroMode`、`Prop5to8`）：常数在 `L, g, t, m, σ, a` 之前，只依赖 `(d, Λ)`（5s 另加 `κ`，6/7 另加 `c`），`g ∈ (0, Λ]`，`Λ = 𝔡^{-1}`。
- **签字接受的 paper-delta 候选**：T2003a（必要条件：常数依赖 `Λ = 𝔡^{-1}`，`Prop5_needs_Lambda` 已编译证明必要；论文写「depending on d」）、T2003b（必要条件：`|r| ≲ |a|` 读作 `|r| ≤ c|a|`、`0 < c < 1`；`c = 1` 时为假，`Prop6Old_false`）、T2003c（更强：6–8 无损失）、T2003d（等价：体内条件写作 `κ ≤ Im m`；5s 用显式谱隙，不引 [bourgade2019random]）、T2003e（更强：性质 5 对一切单位 `m`）、T2003f（`|a|` 取周期 `l¹` 距离，旧 D2）。旧 D11 保留，D12、D13 作废（D12 照字面为假）。
- **旧接口**：`ThetaDiffOne`、`ThetaDiffTwo`、`PropTH` 照字面为假（无合并定理以之为假设）；`ThetaDecay`、`ThetaDecayShort`、`ThetaZeroMode` 可由新钉文导出（桥接定理），已合并的消费者不必改。
- **路线**：设计选了路线 H（把论文性质 5 的随机游走论证做严：Poisson 化 + 张量化，一维热核界，Laplace–Gauss 积分；6–8 由热核差分得到，不走论文所引的 Fourier 分部求和），估 8 张票约 7.4k 行；备选 F（把 RBM2D 的 Fourier/围道路线推到 d 维）约 15k 行、14–17 张。H 在论文和 RBM2D 里都没有，按 TEAM §4 属路线级，**交 Jun**（建议 H，先做 B1+B2 试点，试点失败改 F）。路线定前：与路线无关的 PT-A（T2007：钉文入库、桥接、旧接口反例、性质 5s 的谱隙证明）可开工；B1…G 不写。
- **T2004 核对义务**（§9 O1）照旧：T2004 合并后核对其局部 PT 假设与上述钉文一致。

## §14 传播子路线：H，先请 Fable 5.1 复核（Jun，2026-10-02 23:24 UTC：「我选H 但use a fable 5.1 High subagent to check it first, if it agrees, then H, otherwise let me know again」——回答 §13 的路线问题）

- **决定**：选路线 H，条件是一个 Fable 5.1（high）子代理独立复核后同意；复核不同意，就把结论带回给 Jun 再定。
- **落实**：总调度起 1 个 Fable 子代理，只读材料（T2003 prove/audit 报告、论文 §2.5 与 App. A.1、已合并的 `Propagator/{Basic,Props4}`、`Defs/{Params,Block}`），交回完整可核查的论证或精确缺口；结论记入本节；同意则写 PT-B1（试点）与后续票，不同意则问 Jun。
- **Fable 复核结论（2026-10-02 23:44 UTC）：AGREE**（全文 `docs/claude-team/fable/2026-10-02-routeH.md`）。路线 H 每一步都是初等的（不需要局部 CLT、Bessel 函数、围道积分，也不引任何外部结果），给出的正是 T2003 钉的形状，常数对 `(d, Λ, κ, c)` 一致，无对数或 `L^τ` 损失。按 Jun 的条件，**定为路线 H**。
- **票面必须带上的更正**（Fable §2、§5）：
  - F2（B1/B2）：一维热核用级数定义 `h_τ(n) = e^{-2τ} Σ_j τ^j N_j(n)/j!`，母函数 `Σ_n h_τ(n) z^n = exp(τ(z+1/z) − 2τ)`，倾斜反演 `e^{νn} h_τ(n) = (2π)^{-1} ∫_{-π}^{π} e^{-ikn} exp(2τ(cosh(ν+ik)−1)) dk`；不用围道平移，不用 `poissonMeasure`；界 (a) `0 ≤ h ≤ min(1, (√π/4)τ^{-1/2}) exp(−c₀ min(n²/τ, |n|))`，`c₀ = 0.18`（用 `Real.cosh_le_exp_half_sq` 时 0.14），(b)、(c) 一阶、二阶差分带 `min(1, τ^{-1})`、`min(1, τ^{-3/2})`、指数 `c₀/2`。
  - F4（D）：乘积核的指数是 `c/d`；朴素不等式 `Σ_j min(a_j²/τ, |a_j|) ≥ min(|a|²/τ, |a|)` 为假（`a = (1,50,0)`、`τ = 10`），正确的是带 `1/d` 的版本。
  - F5（E/F）：按 `ε = e/γ` 分区（`ε ≥ 1`、`L^{-2} ≤ ε < 1`、`ε < L^{-2}`）；`e < γ ⇒ t > ½`；`L^{-d}` 项也要用 `e^{-ετ}`；零模项的指数因子由 `εL² ≥ (2/d)|a|/ℓ_t` 得到；`min(1/e, 1/γ) ≤ C_{d,Λ}/(λ²+e)` 是 `Λ` 进入常数的唯一地方。
  - F7（G）：二阶差分按 `n²` 项分解（混合方向与同方向都要）。
  - 记号：拉普拉斯变量与 `s₀ = S_00` 分开命名。
- **落实**：写 PT-B1（试点：一维热核的定义、母函数、倾斜反演）与 PT-E（与 Θ 无关的 Laplace–Gauss 积分引理，和试点并行）；PT-B2 等 B1 合并（试点的另一半：ℤ 上的界）。B1+B2 不通就回到 F 并告诉 Jun。
- **试点结果（2026-10-03 02:05 UTC）**：B1 = T2009（73cf5c1）、B2 = T2011（13dbbc0）都一次审核通过并合并：一维热核的级数定义、母函数、倾斜反演、周期化，以及 ℤ 上的衰减与一、二阶差分界均已在 Lean 里证出，0 公理。路线 H 的去留条件满足，不回 F；接着写 PT-C（T2017）、D、F、G。
- **PT-E 的范围（总调度，2026-10-03 00:05 UTC，流程决定）**：T2010 = Fable §2 S5 的 (L1)–(L3) 原样（Key 引理、`n ≥ 1` 与 `n = 0` 的界、尾/头积分、F5 (a)–(c) 换算），钉在 `docs/tickets/checks/T2010-check.lean`。一处修正：Fable 的 (L1) 第一式对大 `ε` 不成立（`n = 1` 时积分 `≥ e^{-c}(1−e^{-ε})/ε`），钉文按 `ε ≤ 1` / `ε ≥ 1` 分两式；F5 的 (ii) 区只用第二式，(iii)(iv) 区 `ε < 1`，不影响路线。设计行 E 的 `laplace_gauss_5/6/7/8`（按性质组装成 `B_{t,|a|} e^{-c|a|/ℓ_t}`）挪到 F，等 C、D 定下核界的形状再钉。

## §15 T2004（KL-D1 K-loop 层设计）合并后的签字与落实（总调度按 §4 签字，2026-10-02 23:47 UTC；依据 T2004 审核 PASS，0b91f7a）

- **定义选择**：`𝒦` 取树表示定义（选项 B，同 RBM2D P6），ODE `(pro_dyncalK)` 与唯一性为定理（KL3、KL4）。旧的 `KTreeRep`（借来的假设）由定义取代，`TwoLoopBounded`、`KLoopBound`（欠下的假设）由已编译的退役引理取代，KL14 删除。
- **§9 O1 核对通过**：T2004 的局部传播子形状 `KLDecay`、`KLShort`、`KLDiffOne/Two`、`KLZero` 全带 `0 < g ≤ gmax`，常数依赖 `(d, gmax)`（短程另加 `κ`），在 `g = gmax` 处试过。与 T2003 的钉文相容：T2003 的 `Prop5to8` 更强（无损失），桥接 `KLPT_of_Prop5to8` 放在 KL14（届时 PT 证明已合并）；`|a|` 两边都用 `zdistD`（`l¹`），与 §12 T2002b 的约定一致（传播子与 K-loop 层用 `l¹`，随机层与终点用 `L^∞`）。
- **签字接受的 paper-delta 候选**：T2004a（证明需要的条件：`ML:Kbound` 在 `n = 3` 时还要用 `(prop:ThfadC_short)`，论文 A:673 只引了 `(prop:ThfadC)`；陈述不变）、T2004b（必要条件：`g ≤ gmax`，同 T2003a）、T2004c（必要范围：`|r| ≤ c|a|`、`c < 1`，同 T2003b）、T2004d（笔误：`Def_Ktza` 与 `Θ_t` 定义里的 `t ∈ [0,1]` 应为 `[0,1)`）、T2004e（更强：`≺` 读作对每个 `τ > 0` 的 `L^τ` 损失，`KLBoundAt_prec` 换到 `N^τ`）。
- **拆单**：KL1…KL14（报告 b 的 ROW 行；KL4+5、KL8+9 合票，KL7 三张，KL10 两张，KL13 可选）。KL1 = T2008（`prover`，立即）；KL10（`(eq:ind-step-bound)`，d ≥ 3 新估计）是高风险行。审核观察 O2（KL10 的叶子只取 `Θ`，即 RBM2D 的 `innerId` 路线）由 KL10/KL11 的设计确认。
- 预计票数约 15（< 25），KL gate 不触发预判（§9 O2）。


## §16 公理审计登记：T2007、T2008 合并被拦（总调度，2026-10-03 00:34 UTC，流程决定）
- **事由**：T2007（PT-A）、T2008（KL1）审核都 PASS，合并第 5 步全量 `lake build` 在根文件 `#assert_rbm_axioms` 失败：扫描出「作为假设、本库没有定理证明」的 `Prop` 未登记在 `RBM3D/Test/Axioms.lean` 三张表（borrowed / owed / structural）里——T2007：`RBM.Prop5to8`、`RBM.Prop5Decay`、`RBM.Prop8ZeroMode`；T2008：`RBM.Loop.KLPT`。没有提交，main 已复原。
- **归类**：四个都记 **borrowed**（论文对 `lem_propTH` 5–8 是引用不是证明；它们取代旧的 `ThetaDecay` … `PropTH`，后者本来就在 borrowed；`KLPT` 是同一批性质的 KL 局部形）。账本记的是论文的状态；按 §5 它们不是授权外部输入，路线 H（§14）要把它们证掉。T2006 在跑的标准假设 `RBM.Gauss.Sizes.{WO, Bandwidth, SizeTendsto, Admissible, locDomain}` 预先记 **structural**（参数区间与谱域，是对象的定义，不是借来的结果），免得 T2006 合并时同样被拦；登记了暂时没人用只出提示，不报错。
- **落实**：T2007 Amend 1（`repairer` 只改 `Axioms.lean` 两张表和一句文档串 → 第 2 轮审核只看 amend → 合并）；T2007 合并后 T2008 从合并第 5 步续做（分支不动）；H9。
- **以后的票**：凡票里新出现「当假设用、本票不证」的 `Prop`，总调度在票面写明归类并把 `RBM3D/Test/Axioms.lean` 列进唯一可写文件；验收条件写「全量 `lake build`（含根文件 `#assert_rbm_axioms`）」，prover 交审核前自己跑一遍。

## §17 放行改为「编译通过即开工」（总调度，2026-10-03 01:19 UTC，流程决定）
- **事由**：检查文件由中枢在它的循环里编译，总调度要等下一次心跳才看到 exit 0 再放行，每张票平白多等 10–15 分钟（T2011–T2014 01:02 编完、01:18 才放行）。
- **做法**：新票写好后直接列进 CONTROL 的 Released，开工条件写「Pre-release 里本票检查文件的 done 行为 exit 0」；检查文件同时列在 Pre-release。中枢编译后若 exit 0、又有空位，同一循环里开工；exit 1 则不开工，等总调度改检查文件。放行仍是总调度的决定（CLAUDE.md §4 第 0 步不变），只是把条件写在票面上。

## §18 T2016（EK-D1 演化核设计）合并后的签字与落实（总调度按 §4 签字，2026-10-03 04:07 UTC；依据 T2016 审核 PASS，c154f29；探针 `RBM3D/Probe/T2016Pins.lean` 在 `t/T2016` 的 c961e62）
- **钉文照报告 b2 接受**：词汇 `EKsgn`、`EKFastDecay`（= `(deccA0)`）、`EKSumZero`（= `(sumAzero)`）；钉文 `EKSumNdecay`、`EKSumDecay1`（`(sum_res_1)`）、`EKSumDecayNAL`（`(sum_res_2_NAL)`）、`EKSumDecay2`（`(sum_res_2)`）、`EKSumDecayNonzero`、`EKPropT`、`EKTTk`。常数在 `(d, n, Λ, κ)` 之后、`L, g, W, ε, D, s, t, m, σ, A` 之前，`g ∈ (0, Λ]`，两种电荷都含，无 `L^τ` 损失；PT 钉文 `Prop5Decay`、`Prop5Short`、`Prop6Diff1`（`c = 1/2`）、`Prop8ZeroMode` 作前提（路线 H 证掉）。
- **已合并的 `RBM3D/Kernel/*` 不够用**（报告 N2）：六条用旧假设的陈述常数排在 `g` 之后，两条带 `L^τ`，`norm_zeroModeSet_UN_le` 排除了负电荷；EK-2、EK-3、EK-5 取代它们（`Kernel/` 以外只有 `Loop/PureLoop.lean` 导入，没有文件引用其声明），旧文件不改，退役放到最后的死代码清理。三条钉文已由合并定理证出（`norm_UN_le`、`propT`、`key_T_reduce_absorbed` 加桥接），`(eq:latticesum_d3)` 已合并。
- **拆单**（报告 b9）：EK-1 钉文与桥接（prover，300 行）→ EK-2 `Ξ` 界（prover-hard，500）→ EK-3 `(sum_res_1)`、`(sum_res_2_NAL)` 全部 `n`（prover-hard，800）→ EK-4 `ΔΞ` 与 `(sumAzero) ⟹ (sum_res_2)`（prover-max，1450，**唯一高风险**：d ≥ 3 新论证）；EK-5 `lem:sum_decay_nonzero` 无损版（prover，450，在 EK-1、EK-2 后）；EK-6 钉文 ⟹ 尺度 `N` 的 `≺`（prover，500，等 ST-D3 定下消费者形式）。6 张约 4.0k 行，宽口径 12–15，低于 25（§9 O2）。
- **paper-delta 候选签字**（合并成 Lean 时编号）：T2016a（`(sum_res_2)` 带 `log L ≤ W^ε`，论文 A.2 自己说用它吸收）、T2016b（`4 ≤ W^ε`：`≲` 的常数只在 `W^ε` 有下界时才能吸进 `W^{C_nε}`）、T2016c（`lem:propT` 只含区间 (i)(ii)，中间区间无下游使用）、T2016d（`claim:TTk` 的 `D` 为任意 `ℓ`-球内集合、`ℓ ≥ 1`、`Λ²` 显式、`η_t ≍ 1−t`）、T2016e（`lem:sum_decay_nonzero` 无损、两种电荷，强于论文）、T2016f（常数对 `g ∈ (0, Λ]` 一致；`(deccA0)`、`(sumAzero)` 用 `ℓ¹` 距离，见 D18）。
- **公理登记（§16）**：`Prop6Diff1` 记 borrowed，由第一张把它当假设的 EK-4 写进 `Axioms.lean`；`EKSumDecay1`、`EKSumDecayNAL`、`EKSumDecay2`、`EKSumDecayNonzero` 若在 EK-3..5 合并前被 ST 票当假设，由那张票记 owed。

## §19 T2015（ST-D1：Step 1 与 `lem:main_ind` 设计）合并后的签字与落实（总调度按 §4 签字，2026-10-03 05:10 UTC；依据审核第 2 轮 PASS（一次修复），5e7de62；探针 `RBM3D/Probe/T2015Pins.lean` 在 `t/T2015` 的 752e027）
- **钉文照报告 b.3 接受**（探针第 1、1b、2 节，161–501 行，命名空间 `RBM.Gauss.Sizes`，前缀 `ST`）：`STflowE`、`STFlow`、`STMainInd`（`lem:main_ind` 序列级，`≺` 一律尺度 `N`）、`STGbEXPii/ij/av`、`STGbEXP`、`STConArg`、`STStep1`，以及 `STBootstrap`、`STNetLift`、`STKbound`、估计层定义。b.2 已证明它们直接绑定到已合并的 MD-2/MD-3 名字（第 0 节的复制品在入库时删掉）。
- **拆单照 portmap P.7 接受**：ST-1 = 36 张（S1-01…S1-36），约 3.7 万行，在 25–40 之间（§9 O2，不问 Jun）；把 `Induction/{ScaleFacts, PerTimeCalc, Split}`（原 ST-3）和 `Induction/Defs`（原 ST-6）挪进 ST-1（S1-07…S1-09）照准。关键路径 12 张（S1-10 → S1-15 → … → S1-30）；第一波 S1-01、S1-03、S1-07、S1-09、S1-10、S1-12。
- **公理登记（§16）**：`STKbound` 记 owed（KL7 证），`STLK`、`STLmax`、`STDecay`、`STDecayStrong`、`STLocalMax`、`STExp2` 记 owed（ST-6 的链式归纳证），`STConStInd`、`STFlow` 记 structural；由 S1-07 写进 `Axioms.lean`。**修正报告 b.8 的一处**：`STGbEXP_BA`、`STConArg_BA`（论文说「逐字照 [RBSO1D] Lemma 6.1」）报告提议记 borrowed，但 §5 只授权 LSY 一条外部结果，所以记 **owed**：BA gate 要在内部证（照 RBSO1D 的论证）。BA-D1 若认定内部证不可行，再问 Jun。
- **paper-delta 候选签字**（合并成 Lean 时编号）：T2015b（`lem_ConArg` 限 `t < 1`）、T2015c（`lem:main_ind` 的时间限 `t ≤ t₀`）、T2015d（「小 `ε₀`」读作任意 `ε₀ > 0`）、T2015e（Step 1 对任意起点 `s ≥ 0`，`u < 1/2` 用尖锐包络，时间连续性 `Gopboundu` 在 d ≥ 3 论文里无陈述）、T2015f（`(Eq:Gdecay+IND_s<g)` 只在 `g² ≤ 1−τ` 的尺寸上）、T2015g（`STStep1` 对每个 `𝔠_d ∈ (0, 10^{-2}]`，只用 (a)、(c)、`ML:Kbound`，强于论文）、T2015h（`STConArg` 只留 `(res_lo_bo_eta)` 第一个界，第二个是确定性的 `STBctl_mono`）。T2015a 作废。
- **未决小项**：(i) `𝔠_d` 排在 `𝔠` 之前——接受（Step 1 对 `𝔠_d ≤ 1/4` 都成立，Steps 2–5 的约束等 ST-D2/D3 再核）；(ii)(iii) 的一般证明归 S1-08、S1-36。

## §20 公理登记的盲区与 T2029 合并被拦（总调度，2026-10-03 05:42 UTC，流程决定；接 §16）
- **事**：T2029（S1-10 `Green/EntryCore`）审核 PASS，合并第 5 步全量 `lake build` 在根 `#assert_rbm_axioms` 处失败：票自己定义、又被确定性引理当假设的五个 `Prop` 谓词 `RBM.Green.{GoodEvent, LDERow, LDECol, LDEQuad, Stable}` 没登记。prover 和审核员没发现，是因为新文件要等合并时中枢才加根导入，交付前的全量构建扫不到它（§16 的盲区）；ST1-COMMON 第 8 条「只有 S1-07 写 `Axioms.lean`」也挡住了自登记。票面缺陷，记在总调度账上。
- **归类口径**：一个 `Prop` 值定义，若描述的是样本、矩阵或参数满足的条件（事件 Ω、LDE 事件、稳定性条件、`(deccA0)`/`(sumAzero)` 这类数据条件），由确定性引理当假设，它本身不是要证的结论 → **structural**；它以高概率成立、或对具体对象成立，由别的票证明（在注释里写明，知道的话）。论文证过而我们还没证的结论 → **owed**；外部文献 → **borrowed**（只允许 LSY，§5）。拿不准就记 owed 并在报告里提出。
- **今后所有证明票**（不止 ST-1）：(1) `RBM3D/Test/Axioms.lean` 对每张证明票都可写，但只能在三张表里追加登记行（每行一个名字，带一行注释），不改别的；(2) prover 交付前在主工作树外跑一次「登记预检」：一个不提交的临时文件 `import RBM3D` + `import <本票新模块>…` + `#assert_rbm_axioms`，`lake env lean` 退出 0；报告里贴输出；(3) 中枢合并时 `Axioms.lean` 若只在登记表里冲突，取两边并集，再跑全量构建。
- **T2029**：`docs/tickets/T2029.md` Amend 1——在 `t/T2029` 上跑一次 `repairer`，把上面五个名字记进 `structuralProps`，跑预检和全量构建；再一轮审核（只看 `Axioms.lean` 的差异与预检输出）；然后从第 5 步续合并。
- 已放行未合并的票（T2027、T2028、T2030–T2035）各加 Amend 1，照上面三条；正在跑的若已错过，合并被拦时照 T2029 的办法补一次 repairer，不算返工。

## §21 EK-4 预检否掉钉文 `EKSumDecay2`：补 `L^d ≤ W^K`（总调度，2026-10-03 08:13 UTC，按 §4 签字的小改动；依据 `docs/reports/T2042-prove.md` (a)）
- **事**：T2042（EK-4）预检判 FAIL：照 §18 签的 `EKSumDecay2` 在 `d = 3, n = 2` 不成立。钉文里 `L` 与 `W` 只有 `log L ≤ W^ε` 一条关系，而 `EKSumZero` 对全部 `b'` 求和、`EKFastDecay` 只给逐点 `W^{-D}`：把补偿质量以密度 `≤ W^{-D}` 摊到 `L^d` 个远点上，`A` 在窗口内就不再和为零，`‖UN A‖` 带回 `ℓ_t/ℓ_s`（预检 (ii) 第 3、4 块：`L = 129` 的合法数据上比值从 3.1 涨到 106.7；固定 `C` 取 `L ≈ W^{D/3}` 即反例）。我核过机制：论文 `A_deterministic_estimates.tex:186–190` 把远处余项记成 `W^{-D+n}`，没数 `L`；`Σ_{b_i} |ΔΞ_{a_i;b_1 b_i}|` 里 `Ξ_{a_i b_1}` 那一项对 `b_i` 求和给出 `L^d`，所以余项实为 `W^{-D} L^{d(n−1)}`。
- **改法（照预检的候选 1，最贴论文）**：钉文加一个常数 `K > 0`（量词放在 `∃ C` 之前，`C` 可依赖 `K`）和前提 `(L : ℝ)^d ≤ W^K`。论文的常设假设 `(Main_DEL_COND)` `W ≥ N^𝔠`（`N = (WL)^d`）给出 `L^d ≤ W^{1/𝔠}`，所以消费者（EK-6、ST-3）取 `K = 1/𝔠` 即可，论文的 `W^{-D+n}` 正是默认了它。候选 2（窗口内和为零）、3（`ℓ¹` 远处衰减）改的是 `(sumAzero)`/`(deccA0)` 本身，不取。
- **paper-delta 候选 T2042a**（签字，合并成 Lean 时编号）：`(sum_res_2)` / `(eq:bddfA)` 的余项 `W^{-D+n}` 需要 `L` 关于 `W` 多项式（`L^d ≤ W^K`，由 `(Main_DEL_COND)` 保证），常数依赖 `K`。
- **落实**：`docs/tickets/T2042.md` Amend 1——`RBM3D/Evolution/Pins.lean` 对这张票可写，只改 `EKSumDecay2` 的定义体（照检查文件逐字）、它的文档串加一句 T2042a，以及私有实例 `ekInstDecay2`（取 `K = 2`：`5^3 = 125 ≤ 25^2`）；T2042 在原分支从预检重开。不算返工（钉文缺陷，记在总调度 §18 签字账上）。`EKSumDecay1`、`EKSumDecayNAL`（已证）、`EKSumDecayNonzero` 不受影响（无和为零前提）。

## §22 T2028（S1-07，ST-1 钉文入库）合并后的签字（总调度按 §4 签字，2026-10-03 08:16 UTC；依据审核第 2 轮 PASS（一次修复），64bdfd3）
- **T2028a 照准**：`GbEXPHypV3` 等取 `Admissible 𝔠 𝔡`（含 `(eq:WO)`）代替 RBM2D 的 `SizeTendsto → Bandwidth 𝔠`，`𝔡` 排在 `𝔠` 之后——论文 `lem_GbEXP` 的设定就是随机带状矩阵模型（含 `(eq:WO)`），不算越过 ST1-COMMON 第 6 条。记 D39。
- **T2028b–f** 记为 D40–D44（形式上的加强或 RBM2D 读法，照移植保留）；T2028b 由 S1-16 定：d ≥ 3 只能证对称右端时，把 `gexRHS` 换成 `STgexRHS`，由 S1-16 报告、我改票。
- **登记归类确认**（T2028 按 §20 自登记、§19 未签的七个）：`STMainInd`（ST-6 链终点）、`STConArg`（S1-32）、`STStep1`、`STBootstrap`、`STForbidden`（S1-36；`forbidden_region` 由 S1-08 移植）、`STNetLift`（S1-34）、`GbEXPV3Theorem`（S1-30）、`GijOmegaSeq`（S1-24）、`AsGMcPT`（Step 1 的 `(Gtmwc)`）——都由后续票证出，**owed** 正确。
- **paper-deltas 编号补齐**：§18 的 T2016a–f（钉文已随 T2022 入库）记 D33–D38；§19 的 T2015b–h（随 T2028 入库）记 D26–D32；T2042a（§21）等 EK-4 合并时编号。

## §23 T2043（KL7a）审核要求签字：照准 R1/R2（总调度，2026-10-03 08:57 UTC；依据 `docs/reports/T2043-audit.md` §7）
- **事**：移植 RBM2D `Loop/SumZero.lean` 时，`Alayer` 的定义体（R1）和 `sum_SigmaPi`、`SumZero_sum_slice` 的右端（R2）多了因子 `∏_i m(σ_i)`，超出了票面"只改名字和指数"。原因是已合并、冻结的 `KLKpi`/`KLSigmaPi`（`RBM3D/Loop/KLTree.lean:353, 368`）照论文（`A_deterministic_estimates.tex:357, 611`）带这个因子，RBM2D 的没有；RBM2D 原式对合并的定义为假（编译的反例 `KLSumZero_neg_Kpi_closed_2Dform`）。`SumZero_sum_slice_alt` 与条件界因 `∏ m(σ^alt_i) = 1`（`n` 偶、`‖m‖ = 1`）保持 RBM2D 原式。
- **签字**：R1、R2 照准——是被合并定义逼出来的，且与论文一致，不是 paper-delta。prover 没停下来报告就继续做了，这次结果正确，不追究；票面那句"stop and report"的本意是防止偏离论文，这里没有偏离。
- **给 KL7b/KL7c 的话**（写进票）：`Alayer` 现含 `∏ m(σ_i)`；RBM2D `Alayer_cut`（`SumZeroWard`）的前因子在 KL7c 要相应调整（审核 O3）。票面的"`W²η_t → W^dη_t`"对 `SigmaPi_alt_sumZero_le_of_Qlayer_one` 不适用（RBM2D :802 与论文 A:731 都不含 `W`；审核 O1），是我写票的笔误。

## §24 T2040（LW-D1 光权重层设计）合并后的签字（总调度按 §4 签字，2026-10-03 10:30 UTC；依据审核第 2 轮 PASS（一次修复），45e2630；探针 `RBM3D/Probe/T2040Graphs.lean` 在 `t/T2040` 的 eeda441）
- **体量**：gate LW 27 张（21–39，每张约 1000 行），加 BA 33 张（27–48）；都不过 50（§9 O2），中值在 25–40 之间，不问 Jun。LW-12（`lem:Anp` 及其钥匙引理，估 4.9k/7.3k/12.2k 行）写票时再拆成 5–8 张，总数仍按 27 计。
- **表示法照报告 b.3 选 A**：记录型 `LGraph`（边多重集、计数器、分子、`ord` 都在记录上）；B（`GTerm` 绑定项）只可作打印语法，不作陈述。
- **钉文照 b.4 接受**：`LWterm`、`LWtermB`、`LWtermExp`（含 `LWtermExpS`/`N` 两段）、`LWtermEXP`、`LWMoment`、`LWMomentExp`、`LWAnpKey`、`LWAnpKeyGh`、`LWAnp`、`LWReduceB/T`；三条展开式 `LWweightExp`、`LWedgeExp`、`LWggExp` 钉成期望的恒等式，余项是显式的 Stein 缺陷（"=_E"，合并的 MD-2 Stein）。常数先于序列，`≺` 一律尺度 `N`，距离 `zdistInf`。`lem:LWterm`、`lem: EWGn2_N` 的文本等 ST-D2（T2039）签字时与它的消费者形式对齐，以此处为准、差异在那时记。
- **缩减路线 R1**（把 [yang2021] 引理 3.5、3.10、3.14、3.22 当外部输入，省约 6 张）**不取**：§5 只允许 LSY Thm 2.2；照全内部证明走（这不是需要 Jun 决定的事，除非他想改 §5）。R2（只做 Step 6）不成路线。
- **paper-delta 候选 T2040a–o 签字**（合并成 Lean 时编号）：T2040a（`Ψ_t` 加窗口 `W^{-d/2} ≤ Ψ_t` 与常数 `C₃`）、c（奇数 `L`）、d（`f` 取预解式多项式）、e（流版本展开 `S_t = tS`）、f（`lem: EWGn2_N` 的 `t ≤ lemT z`）、g、h（"不妨设 `Ψ_t` 递减" 作前提）、i（`∂_{h_{αx}}` 的定义）、j、k（`1 − t ≤ g²/L²` 一段单列 `LWtermExpN`）、l、m（`claim:size`、`claim:xi` 论文无证明，LW-09、LW-11 补）、n（`lem:LWterm_EXP` 的前提读法）、o（约化步骤不是论文编号陈述）。T2040b 已在预检里关闭。
- **登记**：照报告 b.11——钉文的随机前提（`LWInit`、`LWLoop2`、`LWLoopExp`、`LWXi`、局部律）由 ST 链给出，记 owed；数据条件记 structural；照 §20 由首次当前提的票登记。
- **首批票**：LW-03（词汇，MD-1…3 与已合并 `Graph/{Model,ScalingOrder}`）、LW-15（`(eq:Psi)` 与 `Ψ_t` 窗口，已合并 `Defs/Tail`）、LW-04（Stein 桥，`GaussIBP` 作前提——owed，S1-19 证）。钉文入库（`LWterm` 等）放在 ST-D2 签字之后的一张票里。

## §25 T2041（ST-D3：Steps 3–4 设计）合并后的签字（总调度按 §4 签字，2026-10-03 10:30 UTC；依据审核第 2 轮 PASS（一次修复），3747ff7；探针 `RBM3D/Probe/T2041Pins.lean` 在 `t/T2041` 的 3c58211）
- **钉文照 P.2 接受**：`STStep3R`、`STStep4R`（按区间谓词 `STAny`/`STCaseI`/`STCaseII`），配料 `STContract`、`STSEforLn`、`STXiBoot`、`STOeqNQ`、`STOeqQt`、`STOeqQtNZ`、`STNewPQ`、`STIterations`/`STIterationsII`、`STMollifierProps`、`STQopNorm`；对 `u ∈ [s,t]` 一致的 `STLmaxU`、`STLKU`（端点即 ST-1 的 `STLmax`/`STLK`）。
- **Step 2 的接口**：Step 3 要的是 `STStep2Concl`（`STLocalEntryU`、`STAvgU`、`STGdecayW`，对 `u ∈ [s,t]` 一致，后者带 `((1−s)/(1−u))^{C_d}`）；T2039（ST-D2）签字时核对它的结论蕴含这三条。
- **EK-6 消费形式照 P.3**：`STEKSumNdecay`、`STEKSumRes2NAL`、`STEKSumRes2`、`STEKNonzero`（以及票面要求的 `STEKSumRes1`），尺度 `N`；`lem:propT`、`claim:TTk`、`(eq:latticesum_d3)` Steps 3–4 不用。EK-6 = 由合并的 `EK*` 钉文推出这些 `STEK*`（`STEKSumRes2` 用 §21 的 `L^d ≤ W^K`，`K` 取自 `Admissible` 的 `𝔠`）。
- **拆单照 P.7**：34 张（S3-01…S3-27，含 a/b），约 3.8 万行，25–40 之间（§9 O2），不问 Jun；9 张高风险，无 RBM2D 源的 7 张（S3-02、03、20–23、27）。RBM2D 10 个文件不移植（`PP*` (+,+) 基、`LocalForm*`、`AltSymm`：d ≥ 3 走 EK-4），照准（F-A）。
- **顺序**：S3-01（钉文入库）、S3-06（K 环衰减、`STKward` 桥）要先于 ST-2 的网格证明（F-D）；`HierAlgebra`、`HierarchyN` 归 ST-2（T2039）。S3-10…22 要等 ST-D2 的网格钉文与 EK-6。
- **paper-delta 候选 T2041a–i 签字**（合并成 Lean 时编号）；T2041c（`lem_+Q` 带 `4 ≤ W^ε`、`L^d ≤ W^K`）与 §21 同源；T2041i（Steps 3–4 只用 (a) 加 `STKbound`、`STKward`，前提比论文少）照准。
- **登记**照 (d)：`STKward`、`STStep2Concl` 及其三部分、`STLmaxU`、`STXiBoot`、`STIterHyp`、各配料、`STEK*` 记 owed；`STMollifierProps`、区间谓词、`STEKDecay`/`Low`/`Win`、`STAlternating` 记 structural。
- **风险**：`STIterationsII`（情形 (ii) 的迭代，论文 3_5:1594 "we omit the details"）无印刷证明；`lem:iterations` 用了 [YY_25] (5.118)（RBM2D 有 `loopXi_le`，S1-09）。`STContract` 只有数值核对。这些票（S3-02、S3-22、S3-24b）照 prover-max 写，卡住先起 Fable。
