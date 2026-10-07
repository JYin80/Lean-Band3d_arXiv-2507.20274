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

## §26 T2045（S1-08）审核要求签字：照准未移植的三条（总调度，2026-10-03 13:05 UTC；依据 `docs/reports/T2045-audit.md` §5，`t/T2045` 的 60dac4a）
- **事**：RBM2D `Induction/ScaleFacts.lean` 的 `ChainStepCond`、`chainStepCond`、`scaleFacts_inv_sq_le_tailT` 没有移植，portmap 也没标"不用"。票面说"portmap 不标不用就移植"，审核据此要求签字。
- **签字**：照准，不算返工。三条的消费者都不在 ST-1（`Chain`、`MainInd` 归 ST-6，`Step45` 的 Step 5 部分归 ST-6；T2041 portmap 已记 `chainStepCond→6`、`step5→6`），而且它们的 3D 形式不只是改名（RBM2D 的 `CondStInd` 网格指数 30；`tailT`、`ellStar`、`scaleM` 是 2D Step 5 的对象），ST1-COMMON 第 6 条本来就要求停下报告。本文 `1_2:1308-1312` 的时间归纳分两段，不固定网格 `s_k`；链式归纳的一步就是 `scaleFacts_R1` + `scaleFacts_R2` 在所选网格上。**推迟到 ST-6 的链式归纳票**（写那张票时按本文重写，不照搬 RBM2D）。
- **paper-delta**：T2045a（`scaleFacts_R1` 在 `W^{-d}B_{t,0}` 上、前提加 `(eq:WO)`；比率事实去掉 `0 ≤ s`）、T2045b（三条不移植）照准，编 D46、D47。
- **给 S1-35 的话**（写进票）：probe `752e027:RBM3D/Probe/T2015Pins.lean` 4.0 节的 `StochDomAt.of_subset_whp`、`StochDomAt.of_subset_compl` 还没入库（T2045 证明报告 (d).2），Step 1 的组合要用；合并的 MD-2 若没有同义引理，由 S1-35 移入。

## §27 EK-6 预检否掉钉文 `STEKNonzero`：补 `0 ≤ s`（总调度，2026-10-03 18:43 UTC，按 §4 签字的小改动；依据 `docs/reports/T2053-prove.md` (a) 第 16 行与反例）
- **事**：T2053（EK-6）预检判 FAIL：随 T2049 入库的 `STEKNonzero`（`RBM3D/Induction/Step34Pins.lean:665`）只要 `1 − ilambda²/L² ≤ s`，没有 `0 ≤ s`；`ilambda > L` 时窗口伸到负时间，`U_{v,t}` 在 `t_n < 0` 近奇异，反例 `L = 4, g = 50, s = −3/2` 让左边超过任何 `N^τ`。已证的 `EKSumDecayNonzero`（T2035）与 Props 5s、8 都要 `0 ≤ s`（`0 ≤ t < 1`）。论文 case (ii) 本来就在 `[0, 1)` 里（`lem:main_ind` 的时间），是我在 §25 签钉文时漏看。
- **改法**：`STEKNonzero` 在 `(∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) →` 之后加 `(∀ n, 0 ≤ s n) →`，别的不动。消费者 S3-21（`STOeqQtNZ`）的设定里 `0 ≤ s` 本来就有（`STIngR`），不受影响。不记 paper-delta（论文的时间本就非负），不算返工（钉文缺陷，记在总调度 §25 签字账上）。
- **实例数据**：票面"每条在 `(sz0, sInst, tInst)` 与 `(szB, 15/16, 31/32)`"不对——`STEKSumRes1/NAL/Res2` 要情形 (i) 的窗口 `STEKWin`，用 `(sz0, 0, 1/16)` 与 `(szB, 7/8, 15/16)`；`STEKNonzero` 要情形 (ii)，只用 `(szB, 15/16, 31/32)`；`STEKSumNdecay` 两处都行。照预检 (ii) 的选择。
- **落实**：`docs/tickets/T2053.md` Amend 1；T2053 在原分支从预检重开。

## §28 T2039（ST-D2：Step 2 与路径层设计）合并后的签字（总调度按 §4 签字，2026-10-03 18:47 UTC；依据审核第 2 轮 PASS（一次修复），6ef5d49；探针 `RBM3D/Probe/T2039Pins.lean` 在 `t/T2039` 的 0362cbc）
- **钉文照 P.9 接受**：`STStep2`（结论 `STStep2Local`、`STStep2Avg`、`STStep2Decay`，`∃ C_d ∃ 𝔠_d ≤ 10⁻²`，常数在序列之前），配料 `STNewKLK`、`STContractPt`、`STLWB`、`STLWT`、`STEMn2Poly`、`STEMn2Exp`、`STGridRepN`（每个圈长；`STGridMart` 是 `m = 2`）、`STK2decay`、`STNetLift2`、`STScaleExists`（审核后重述的 `STScaleOk`/`STScaleAdm`，"对大 `n`"）、`STOptL2`、`STLocalAvgOfL2`。骨架 `ST_step2_of_pins`/`ST_step2_of_pinsN` 与实例已编译。
- **§25 的接口对上了**：`ST_step2_concl` 编译证明 Step 2 的结论蕴含 `STStep2Concl`（`STAvgU` 经 `𝓛^{(1)}_- = conj 𝓛^{(1)}_+`）。常数 `C_d = 3C + 1`、`𝔠_d = min(1/100, 1/(60 C_d), 𝔠₀)`，满足预检的 `𝔠_d(C_0 + 1/6) < 1/30`。给 ST-6 链的话：Steps 3–4 的 `∃ 𝔠_d`（`STIngR`/`STIterR`）与 Step 2 的 `𝔠_d` 取较小者；`STConStInd` 在 `Bctl ≤ 1` 时对 `𝔠_d` 单调（小的更强），链式票里要写出这一步。
- **LW 钉文对齐（F15）**：结论相同（`STLWB` = `LWterm`，`STLWT` = `LWtermExp`，界与指数一致）；五处形式差别。照 §24 **以 LW 设计为准**：LW 钉文入库（`LWterm` 等，下面 LW-P 票）；ST-2 保留消费形式 `STLWB`/`STLWT`，桥 `STLWB_of_LWterm`、`STLWT_of_LWtermExp`（含差别 (1)：`STEGtM` 与 `LWE` 差一个圈的循环旋转与两项次序，要证）放进 ST2-03。
- **拆单照 P.5**：41 张，4.13 万行；`lem_dec_calE` 四张（ST2-36…39）是 Step 5 用的（`3_5:2317`），**移到 ST-4**，ST-2 记 37 张，在 25–40 之间（§9 O2），不问 Jun。`StoppedEndDefs` 不移植（T2049 已钉 `STOeqNQ`/`STOeqQt`/`STOeqQtNZ`，F16）照准；`HierAlgebra`、`HierarchyN` 是 ST2-28a；ST2-32（`GridGoodN`）不用 class-c 的 `GoodSet/Bootstrap` 重写（prover-hard）；ST2-06b（`(TTT2)` 的 `|·|_∞` 版）先于 ST2-07。
- **`lem:newKLK` 钉成确定性的**（对每个 Hermitian `H`、`‖G−M‖_max ≤ δ₀`）照准；ST2-07 若证明要更多，停下报告。
- **登记**照 (d).7：owed——`STNewKLK`、`STContractPt`、`STEMn2Poly`、`STEMn2Exp`、`STGridRepN`、`STK2decay`、`STNetLift2`、`STScaleExists`、`STOptL2`、`STLocalAvgOfL2`、`STStep2`、`STLWB`、`STLWT`、`STInitialGT2`、`STLWassm`、`STLWassmExp`；structural——`STPsiClass`；`Prop5Decay` borrowed（ST2-06、07 内）。由 ST2-01 一次登记。
- **paper-delta 候选 T2039a–j 签字**（随 ST2-01 入库时编号）。
- **风险**：高——ST2-09…11（`lem: EMn2_N`）；中高——ST2-12/13（`STGridRepN`）；`STScaleExists` 的真伪 Lean 未验证（第一版被审核反驳，修后不再被同一反例驳倒）。这些票照 prover-max / prover-hard 写，卡住先起 Fable 子代理。
- **顺序**：ST2-01（钉文与词汇入库，探针 §0 的 24 条 ST-1 钉文副本换成已合并的名字）先行；同时开 LW-P（LW 钉文入库，§24）、ST2-05、ST2-06b、ST2-20、ST2-22（只依赖已合并的东西）。

## §29 钉文边界核对成为固定项（总调度，2026-10-03 18:51 UTC；依据监督结论 `docs/supervisor/2026-10-03-1849.md` O2、O3）
- **事**：24 小时内三条签过或入库的钉文按原样为假：`EKSumDecay2`（缺 `L^d ≤ W^K`，§21）、`STScaleExists`（`∀ n` 在小 `n` 强迫 `Bctl ≤ 1`，T2039 审核第 1 轮）、`STEKNonzero`（缺 `0 ≤ s`，§27）。都在被证明消费之前拦下，但属同一类：窗口边界。
- **固定核对项（四条）**：今后①我签设计单的钉文时，②钉文入库票与 EK/ST 消费形式票的预检，都对每条钉文逐条核：(1) 时间域 `0 ≤ s`、`t < 1`（及 `t ≤ lemT z`）；(2) 情形 (ii) 的边界 `1 − ilambda²/L²`，特别是 `ilambda > L` 时它伸到负时间；(3) `L` 与 `W` 的多项式关系（`L^d ≤ W^K`，由 `(Main_DEL_COND)` 保证）是否被用到而没写进前提；(4) `∀ n` 与 `∀ᶠ n`（有限个 `n` 处的条件不应被强加）。每条给编译实例或纸面论证，否则给反例并停下报告。常数不得暗含 `W`、`L`、`ilambda`（T2039 审核 O4）。
- **当前落实**：T2066（ST2-01，ST-2 钉文入库）与 T2067（LW-P）的预检已加这四条（开工前改票，不算 Amend）。已入库、尚未被证的 Steps 3–4 钉文（T2049）中已核过 `0 ≤ s` 的不再重做；S3 票的预检照此执行。
- **O3 的三座桥**（ST-2 ↔ LW，F15 的 (1)(2)(4)）都放在 **ST2-03**：(1) `STEGtM` 与 `LWE` 差一个圈的循环旋转与两项次序（迹的循环不变性）；(2) `STLWB` 把 `(initialGT2)` 的控制 `Ψ` 绑到 `Ψ_t(0)`；(4) `STLWT` 的 `ℓ` 范围是 `∀ᶠ n`，`LWAssmExp` 是 `∀ n`，要一条"有限个 `n` 处改动不影响"的引理（同 `ST_scaleAdm_congr`）。写 ST2-03 时逐条写进票。
- **O1** 已由 §28 处理（ST2-36…39 移 ST-4，ST-2 计 37）。**O4**：ROUTES 的票数分成"已用（宽口径，含返工）"与"计划"两列，下面改。

## §30 S1-17 预检：RBM2D 的均匀权 `uniformWeight_svar` 在 d ≥ 3 不成立——改成有界权（总调度，2026-10-03 19:06 UTC，按 §4 的小改动；依据 `docs/reports/T2061-prove.md` (a)）
- **事**：RBM2D 的方差剖面 `svar` 是固定的五点均匀剖面（无 `g`），所以行 `j ↦ svar i j` 是 `UniformWeight`（支撑上取同一值 `c`）。本文的 `svarF d L W g`（`(eq:variancematrix)`）带 `g`：同块取 `W^{-d}/(1+2dg²)`，邻块取 `g² W^{-d}/(1+2dg²)`，只有 `g² = 1` 时均匀；`lam` 是可以趋于 0 的序列。所以 `uniformWeight_svar` 照搬为假（预检数值：0.05 与 0.0125 对 0.017857）。三条关键目标不受影响（预检 PASS）。
- **决定（候选 A 的变体）**：保留 `UniformWeight`（块平均 `uniformWeight_blockAvg2` 在任何 `d` 都均匀），另立**有界权** `BoundedWeight t c A`：`0 ≤ t k ≤ c` 在 `A` 上、`A` 外为 `0`（需要时加 `Σ t = 1`），证 `UniformWeight → BoundedWeight`，并把 `uniformWeight_svar` 换成 `boundedWeight_svarF`：`c = W^{-d}`（`1/(1+2dg²) ≤ 1`、`g²/(1+2dg²) ≤ 1`），`A = {j : a_j − a_i ∈ {0} ∪ 邻块}`，`#A = (2d+1) W^d`。RBM2D 后续证明（`FlucIter.lean:980-995` 取 `|t(v i)| = c`）只用到 `≤ c`；S1-18、S1-20、S1-30 的票照此把前提 `UniformWeight` 换成 `BoundedWeight`（前提更弱，结论更强），各票预检逐处核对"`= c` 只当 `≤ c` 用"，有例外就停下报告。
- **paper-delta 候选 T2061a**：论文的波动平均对一般的有界、和为一的权成立，Lean 以 `BoundedWeight` 陈述；RBM2D 的均匀权是 `d = 2` 模型（无 `g`）的特例。不算返工（照搬类的偏差，ST1-COMMON 第 6 条要求停下报告，做得对）。
- **落实**：`docs/tickets/T2061.md` Amend 1；T2061 在原分支从预检重开。

## §31 T2077、T2080 的票面修正（总调度，2026-10-03 22:24 UTC，流程事项与小改动；依据 `docs/reports/T2077-prove.md` (b.9)(d.1)、`docs/reports/T2080-prove.md` (a) Verdicts D1–D3）
- **T2077（S1-06）**：票里点名的两条关键陈述 `sum_norm_integral_pairCutIntegrand_le`（BlockSumBound:78）、`expected_gloop_hierarchy_integral_unconditional`（Continuity:307）及其周边，依赖 RBM2D 上游已删的死代码链（`ContractionSecondLoopExpectedCuts`、`LoopHierarchyGenerator`、`LoopHierarchyCutNormBounds`、`LoopHierarchyIntegral` 等，约 1000 行；portmap 记为 class d，RBM2D T2274 删除，9e0f275 上已不存在），portmap 后续无消费者。**决定：删去这两条目标，不移植死代码链**。是票面错误（我从 portmap P.7 注记照抄了已删的名字），不算返工。`sum_norm_SB_row` 不另立别名：消费者用合并的 `RBM.sum_norm_SB_row d L g hL a`（`Defs/Block.lean:118`）。T2077 在原分支 586e57c 直接进审核。
- **T2080（ST2-03）**：LW 钉文 `LWterm d`、`LWtermExp d` 以 `3 ≤ d →` 开头，ST-2 消费形式 `STLWB d`、`STLWT d` 没有，`Sizes d` 也不带 `d ≥ 3`；`d ∈ {1,2}` 时前提空真而结论实在，桥按原签名推不出。**决定：两座桥加前提 `(hd : 3 ≤ d)`**（不改任何钉文；`STStep2` 等消费者都在 `3 ≤ d →` 之下，主定理只要 `d ≥ 3`）。另：探针 §10 的 `STScaleInv`（2260–2263）、`ST_STprof_pos`（2309–2313）、`ST_card_lab_le`（2315–2335）被 ST2-03 的搬移范围用到，**移入 `Step2Events.lean`**，ST2-04 导入、不再复制。D2（`Ψ' = max(Ψ(0), W^{-d/2})`）照预检做法，无须改陈述。票面疏漏，不算返工。T2080 在原分支从 1b 重开（预检报告 (a) 已覆盖修正后的票）。

## §32 T2095（ST2-28a）预检 BLOCKED：`hierarchyN` 取条件形式（总调度，2026-10-04 01:41 UTC，流程事项；依据 `docs/reports/T2095-prove.md` (a) Verdicts）
- **事**：无条件的 `hierarchyN : HierarchyN d` 的 RBM2D 证明（`HN:31-34`）是 `rw [loopGenN …]` 再用 `loopDrift_sub_K_deriv_n`；一般 `n` 的 `LoopGenN`（`genMat 𝓛 = llPairN + egtN`）属 ST2-28（536 行，未合并），不是 T2095 的依赖（portmap P.5 漏写）。`HierAlgebra` 各目标与 `HierarchyN` 的 `Prop`、`n = 2` 约化：预检 PASS。
- **决定**：照预检提议，`hierarchyN` 取条件形式 `hierarchyN_of_loopGenN : STLoopGenNForm d → HierarchyN d`，`STLoopGenNForm` 是一般 `n` 的圈生成元恒等式，按合并的 `LoopGenN2` 的形状（`∀ sz n`、`g = sz.lam n`、合并的 `ST*` 词汇）在本票文件里定义，登记为 owed（ST2-28）。ST2-28 的票须证出 `STLoopGenNForm d` 本身（类型一字不改），合并后再组合出无条件的 `hierarchyN`（ST2-28 票里写）。不算返工（票面依赖漏写）。
- **落实**：`docs/tickets/T2095.md` Amend 1；T2095 在原分支从 1b 重开，预检报告 (a) 沿用。

## §33 T2097（ST2-25）预检 FAIL：`tailtoTail` 照搬在 d ≥ 3 不成立——本票删去，留给 ST-D4（总调度，2026-10-04 01:57 UTC，流程事项；依据 `docs/reports/T2097-prove.md` (a) "Verdict per target" 与 part C）
- **事**：RBM2D `tailtoTail`（`Path/UTransport:422`，论文 `TailtoTail`/`(neiwuj)`，`3_5:2345–2362`，Step 5）照搬为假：`d = 2` 的恒等式 `r²M_s⁻² = ρ_ℓ⁴M_t⁻²` 靠振幅 `∝ η⁻²`；`d ≥ 3` 的振幅 `B_{t,r} ∝ (g² + 1 − t)⁻¹`，留下因子 `ρ_η = (1−s)/(1−t)`。数值（part C，精确的 `U`）：`g = 0.01`、`1 − t = 0.01`、`1 − s = 0.5`（论文的区间 `1 − s ≥ 1 − t ≥ g²` 之内）比值约 `53.6`，与 `ρ_η = 50` 同阶；`g = 1` 时还随 `L` 增长。其余五组目标预检 PASS。
- **决定**：`tailtoTail` 从 ST2-25 删去（P.1 的 ST-2 消费者 `Path/StepBound` 属 c 类、不移植；论文的用处是 Step 5 的 `lem:pf_step5`，属 ST-4）。`(neiwuj)` 在 `d ≥ 3` 的正确形式（带 `ρ_η`，或换论证）交给 ST-4 的设计票 ST-D4 先查清，再决定 `lem:pf_step5` 怎么走；**这可能是论文 Step 5 的一处真缺口**，paper-delta 候选 T2097a 暂记为"待核"。不算返工。
- **落实**：`docs/tickets/T2097.md` Amend 1；T2097 在原分支从 1b 重开，预检报告 (a) 沿用。
- **更正（总调度，2026-10-04 02:40 UTC；依据 Fable 复核 `docs/claude-team/fable/2026-10-04-tailtotail.md`，Jun 指派）**：`(neiwuj)` **成立**，上面"可能是论文缺口"的判断撤回。T2097 预检把尾函数认错了：`TailtoTail`（`3_5:2344–2362`）用的是 Step 5 自己的 `T_{u,D}(r) = (W^d|1−u|)^{-2} e^{−√r} + W^{-D}`（`def_WTuD`，`3_5:2296`，振幅 `η_u^{-2}`，与一、二维相同），不是 `def: TTfunc` 的 `𝒯_t`/`𝒯̃^ℓ_{t,D}`（`3_5:311–322`，Lean 的 `tailT`/`tailW`，振幅 `(g²+1−t)^{-1}`）。用正确的 `T`：`sum_res_Ndecay` 的因子 `((1−s)/(1−t))²` 恰好把 `(W^d(1−s))^{-2}` 变成 `(W^d(1−t))^{-2}`；`1−t ≥ g²` 时 `ℓ_t = 1`，核按 `(2d/(2d+1))^{|x|₁}` 衰减，`e^{−√r}` 由 `√` 的三角不等式保住；常数只依赖 `d`。数值（`d = 3`，精确的 `U`，`L = 16, 32, 64`，`ρ_η` 到 `5·10⁵`）：比值都在 `[0.66, 1.36]`；用 `𝒯` 则重现预检的 `53.6`。`lem:pf_step5` 照论文的停时论证闭合，无缺口（Fable 置信约 95% / 85%）。T2097a 撤销，不编 paper-delta。
- **后续**：`tailtoTail` 仍不放回 T2097（已按 Amend 1 在 1b）；Step 5（ST-4）移植时新增 `tailTD`（= `def_WTuD`）到 `Defs/Tail.lean`，按 Fable 给的陈述移植 `tailtoTail`：`0 ≤ s ≤ t < 1`、`g² ≤ 1−t`、`‖A b‖ ≤ T_{s,D}(|b₁−b₂|)` ⟹ `‖U∘A (a)‖ ≤ C_d² T_{t,D}(|a₁−a₂|) + ((1−s)/(1−t))² W^{-D}`（证明用 `ukerNonneg`、`ukerRowSum`、`√` 三角不等式、Neumann 界）。写进 ST-D4 的设计要求。

## §34 T2107（LW-05）BLOCKED：钉文 `LWweightExp`、`LWggExp` 把 `LWPins_lwSp` 的实参 `E`、`g` 写反了——改钉文（总调度，2026-10-04 05:50 UTC，按 §4 签字的小改动，同 §27；依据 `docs/reports/T2107-prove.md` (d) 第 1 项与 `docs/queue/T2107.state`）
- **事**：`LWPins_lwSp` 的显式实参顺序是 `d L W g E t`（`Graph/LWPins.lean:84`，节变量 `(g E t : ℝ)`），而 `LWweightExp`（`:112`、`:115`）与 `LWggExp`（`:169`、`:172`、`:176`、`:180`）写成 `LWPins_lwSp d L W E g t`，即以能量当耦合、以耦合当能量。照字面钉文为假：`LWweightExp 0` 已编译出反例（`LWweightExp_zero_false`），`d = 3` 的蒙特卡罗偏 16.8 个标准差。文档串与设计（T2040，§24）写的都是 `S⁺ = S(1 − m²S)⁻¹`，本意无歧义。
- **决定**：六处一律改成 `LWPins_lwSp d L W g E t`，其余一字不改。改后的 `LWweightExp` 就是 T2107 已证的 `LWweightExpFix`（`lwWeightExpFix_holds`，对一切 `d`），所以不另立新名：删去 `LWweightExpFix` 与反例 `LWweightExp_zero_false`，定理改名 `lwWeightExp_holds : LWweightExp d`。`LWggExp` 同修，LW-07 照修后的钉文证。
- **落实**：`docs/tickets/T2107.md` Amend 1（`RBM3D/Graph/LWPins.lean` 只许改这六处实参）；T2107 在原分支从 1b 续做（预检 (a)、(a′) 沿用），再审核。钉文笔误不算返工（同 §27、§32）。
- **教训**：钉文入库票（T2067）的预检核了边界四项（§29），没核实参顺序；同名实数参数多的定义（`g E t`）调用时易错位。今后钉文入库票的预检加一项：每个调用对照定义的显式实参顺序。

## §35 T2118（ST2-11）预检 FAIL：`S̃₃` 的论文路线要"大 D"，钉文 `STEMn2Exp` 是 ∀ D > 0——钉文不动，换路线（总调度，2026-10-04 07:49 UTC，流程事项；依据 `docs/reports/T2118-prove.md` (a) Verdicts 与 Fable 复核 `docs/claude-team/fable/2026-10-04-emn2exp-D.md`）
- **事**：T2118 预检按论文 `3_5:871–888` 的路线（六条腿都用 `(Ĵ + W^{-D}) W^{-d}𝒯̃` 界）估 `S̃₃`，第 7 行"底对底"项 `u|Reg|W^{-D}` 要 `D ≥ log_W(g²ℓ_t^{d−2})`；论文写"任意大常数 D"（`3_5:437`），合并的钉文 `STEMn2Exp`（`Step2Defs.lean:456`）与 `emn2Exp_of_far3` 的 `h3` 是 `∀ D > 0`。预检没有说钉文为假。
- **Fable 复核结论**：钉文按 `∀ D > 0` **不假**，不需要 `D` 的下界。第 7 行是论文链的副产物（`3_5:881–886` 的 `W^{-2D}Σ_c 1`）。按 `(b,c')` 腿上剖面的大小把 `S̃₃` 分开即对每个 `D > 0` 闭合：`A^f = {c' : P_D(|c'−b|) ≤ P_D(|a−b|)}`（含该腿的整个底区）用收缩不等式（同 `S̃₁` 的 `emn2Exp_part1`，`M = y²P_D(|a−b|)`、`K = 1`）给出 `(W^{-d}B_{t,0})^{1/2}` 项，不求和、不用 `Ĵ`、不要 `D` 的条件；`A^n` 上该腿是真尾巴，六腿 Hölder 只遇到 `Σ_c 𝒯𝒯`（`(TTT2)`）与 `W^{-D}Σ_c 𝒯 ≤ C₁W^{-D}/(1−t)`，"底对底"项不出现。配料都已合并或已在预检计划里；脚本见 Fable 报告第 2 节（手算与脚本核对，非 Lean）。另：`STLWT` 无此问题（右边对 `D` 反单调，前提不含 `D`）。若改钉文成"∀ 大 D"约需一天，修改 `ST_LW_sections`、`ST_event_mg`、`ST_selfImprove_section`、`ST_selfImprove`、`ST_step2_of_pins*` 等，无数学风险但不必要。
- **决定**：钉文 `STEMn2Exp` 与 `emn2Exp_of_far3` 不改；`docs/tickets/T2118.md` Amend 1 换成分区路线，从 1a 重开（预检只补分区部分的 (a′)：`A^f` 的收缩不等式与 `A^n` 的 Hölder，其余行沿用 (a)），再 1b、审核。paper-delta 候选 T2118a：`3_5:881–886` 需 `D ≥ (d−2)log_W ℓ_t`；形式化在 `𝒯̃(|c'−b|) ≤ 𝒯̃(|a−b|)` 处分开 `S̃₃`，底区用收缩不等式，故 `(eq:MG_conclusion3)` 对每个 `D > 0` 成立。不算返工（预检按规则停下报告）。

## §36 T2118（ST2-11）审核 RETURN：证明多带 `(hd : 3 ≤ d)`——签字接受，并定为常设（总调度，2026-10-04 10:31 UTC，流程事项；依据 `docs/reports/T2118-audit.md` §1、§6，`docs/reports/T2118-prove.md` (d) 1）
- **事**：T2118 在 e9983a2 证出 `emn2Exp_far3 (d) (hd : 3 ≤ d)` 与 `stEMn2Exp_holds (d) (hd : 3 ≤ d) : STEMn2Exp d`；钉文要的是对一切 `d`。多出的 `hd` 来自已合并的输入 `EKPropTInf`（`Evolution/PropTInf.lean:523`）、`KellStarEv`（`Path/KellStar.lean:55`），二者只对 `d ≥ 3` 陈述；论文本身也只在 `d ≥ 3`。消费者 `ST_step2_of_pins'` 等都在 `STStep2 d := 3 ≤ d → …` 之下用它，文件末的例子已编译这条链。审核其余全部 PASS。
- **决定（签字）**：接受 `(hd : 3 ≤ d)`，钉文 `STEMn2Exp`、`emn2Exp_of_far3` 不改。**常设**（推广 §31）：证明钉文的定理可以多带 `(hd : 3 ≤ d)`，条件是 (i) 用到的已合并输入只对 `d ≥ 3` 陈述，(ii) 每个消费者都在 `3 ≤ d` 之下用到它（主定理只要 `d ≥ 3`），(iii) 报告里列出消费者并编译一条到 `3 ≤ d` 端点的例子。满足这三条不再要签字，审核按 PASS 处理。
- **登记表**：这样证出的钉文，登记预检通过就可以删其 owed 行；`3 ≤ d` 这一条件记在 paper-delta（如 T2118b）里，证明定理的文档串最好也写上（缺了只记观察，不退回）。带别的条件的条件形式（如 T2125 的 `STKbound`）仍按审核逐个核对消费者。
- **落实**：`docs/tickets/T2118.md` Amend 2；H64：t/T2118 在 e9983a2 直接跑第 2 轮 `auditor`（按 Amend 2 核对），PASS 即合并。不算返工（钉文写成对一切 `d` 是票面疏漏）。

## §37 T2129（S3-06）预检 FAIL：新钉文 `STKcalDecay` 对一切 `g ∈ (0, gmax]` 为假——加 `Q` 与 `W^{-Q} ≤ g`（总调度，2026-10-04 11:01 UTC，流程事项（票面钉文由我起草）；依据 `docs/reports/T2129-prove.md` (a) row 5、Finding 1、Verdicts）
- **事**：我在票里起草的 `STKcalDecay`（RBM2D `KcalDecay` 的 `d` 维形式）对每个 `g ∈ (0, gmax]` 量化。预检数值：`d = 3`、`L = 9`、`W = 2`、`1 − u = g²` 时异号传播子 `≈ g⁻²`，`|𝒦^{(3)}| ≈ c W^{-6} g⁻⁴`，`g = 0.01` 时 `1.6·10³ > W^{-D}`；对每个大 `N` 取 `L = W = N^{1/6}` 前提全成立而结论不成立，所以照字面为假。RBM2D 的 `KcalDecay` 没有 `g`（常数与 `g` 无关），是我移植时漏的。目标 2、3 预检 PASS。
- **决定**：钉文改为：在 `∀ᶠ N` 之前加 `∀ Q > 0`，并加前提 `(W : ℝ)^(-Q) ≤ g`；其余不变。消费者（`lem_decayLoop`、`lem_BcalE`、`GridGoodEvent`）由 `(eq:WO)`（`lam ≥ W^{-d/2+𝔡}`）以 `Q = d/2` 供给，`g ≤ gmax` 由 `lam ≤ 𝔡⁻¹`。paper-delta 候选 T2129a（论文由 `(eq:WO)` 隐含此下界）。不算返工（票面钉文错）。
- **落实**：`docs/tickets/T2129.md` Amend 1；H65：T2129 在原分支从 1b（`prover-hard`）续，预检报告 (a) 沿用。

## §38 T2128（LW-08）预检 BLOCKED：合并的三个展开只覆盖蓝色、出边、内部顶点——另开 LW-08a 补对称性（总调度，2026-10-04 11:18 UTC，流程事项；依据 `docs/reports/T2128-prove.md` (a) rows C1–C4、Verdicts）
- **事**：预检数学上 PASS：终止度量 `μ = ((K − ord)^+, w, Φ, n_S)` 字典序，290335 个一步输出无一违反；`ord ≥ K` 截断（选 (a)），`size ≤ W^{-D}` 的推论成立（`n_M`、`n_V − n_W` 不增）。但目标 2（`LocStep` 的期望恒等式）缺输入：合并的 `owx_graph_E`、`oe1x_graph_E`、`oe2x_graph_E` 只对蓝色权（内部顶点）、蓝色出边、蓝色 `G_{xy}G_{y'x}` 成立；`strat_local` 会遇到红色、入边、外部顶点上的权（`G_{xv}G_{yv}` 无蓝色出边；2648 个需走第 2 步的随机图里 1206 个无蓝色出边坏顶点；`p2Graph` 第一步 736 个输出里 352 个外部顶点带轻权）。缺：(S1) 图的共轭，(S2) 虚部翻转下 `seqP` 不变、`G ↦ Gᵀ` 的转置不变性，(S3) 外部顶点的 `(Owx)`；(C4) 带圈非自环边要数据 `M a b = 0`（`a ≠ b`）。
- **决定**：S1–S3 另开一张票 **LW-08a = T2131**（`Graph/LWSymm`，`prover-hard`），T2128 不扩范围；C4 作为 T2128 的数据假设（`M = m·1`，同 `lwClaimSize`）。T2131 合并后 T2128 在原分支从 1b（`prover-max`）续，预检 (a) 沿用。LW gate 总数 29 → 30。不算返工（设计拆单漏了对称性输入）。
- **落实**：`docs/tickets/T2131.md`（新，Released 100）；`docs/tickets/T2128.md` Amend 1。

## §39 T2135（S3-07b）预检 FAIL：目标 2 的前提是按时刻的 `STDecayLoopPT`，`STEKDecay` 要关于时间一致——本票加一个一致形式（总调度，2026-10-04 13:07 UTC，流程事项（票面前提由我起草）；依据 `docs/reports/T2135-prove.md` (a) row 12、Verdicts）
- **事**：目标 1（割的引理、窗口和、`glueTerm`、`eeLoop`）预检 PASS。目标 2（`ℰ` 项的标号衰减，`STEKDecay` 形式）照票面 FAIL：`STEKDecay` 是 `Whp{∀ v ∈ [s_n,t_n], …}`（时间并在概率之内），票面给的前提 `STDecayLoopPT` 是按时刻的 `PrecPT`（并在概率之外）；按时刻推不出一致（连续时间，`stochDomAt_of_perTimeDomAt` 要有限指标集）。用一致形式的前提，第 1–11 行全部闭合（`τ' = ε/2`、`D'' = D + (m+2)/𝔠 + 1`）。
- **决定**：本票加目标 3：`STDecayLoopU`（`STDecayLoopPT` 把 `PrecPT` 换成 `Prec`，即关于 `u ∈ [s,t]` 一致）与 `stDecayLoopU_of_step2`：由合并的一致形式 Step-2 衰减 `STGdecayW`（`Prec`，`Step34Pins.lean:208`）在一致事件上逐点套用 S3-07a 的确定性切割论证得到（S3-07a 的 `stDecayLoopAt_holds` 本是逐点蕴含）；目标 2 改以 `STDecayLoopU` 为前提。paper-delta 候选 T2135b（论文 `1_2:1371` 的"关于 `u` 一致"）。不算返工（票面前提错）。
- **落实**：`docs/tickets/T2135.md` Amend 1；H66：T2135 在原分支从 1b 续，预检 (a) 沿用；目标 3 的预检只补一行 (a′)（一致事件上的逐点蕴含）。

## §40 ST-D4（T2134）合并后的签字与落实（总调度按 §4 签字，2026-10-04 15:59 UTC；依据 T2134 审核第 2 轮 PASS，3668596；报告 `docs/reports/T2134-prove.md`、`T2134-portmap.md` P.1–P.10）
- **钉文接受**：探针 `RBM3D/Probe/T2134Pins.lean`（`t/T2134` 7b2b789）的 18 个钉文与形状 `STIngR5`（同 `STIngR`）、`STStep5Concl = STGdecayW … 0 ∧ STDecayStrongU`、组装 `ST_step5_assembly`（得 `t` 时的 `STDecay ∧ STDecayStrong`）、情形 (iv) 由 Step 4 证出（`stStep5IV_holds`）。
- **签字接受的 paper-delta 候选**：T2134a–j（入库为 D315–D324）。路线照论文（情形 (i) CLT、(ii) 零模、(iii) 停时 + `tailtoTail`），不是路线级改动；`lem:newKLK` 的锐形式（F-C）、情形 (ii) 的闭合（F-F）是把论文"从略"之处写实。
- **登记类别（改动一处）**：报告提议 `STLemDecCalE`、`STPfStep5`、`STCltIso` 记 borrowed；**不接受**：§5 只授权 LSY 为借用，这三条由 S5-05…S5-11、S5-17…S5-21 内部证明，**记 owed**（同 §19 对 `STGbEXP_BA` 的处理）。其余照报告：`STStep5I/II/III`、`STStep5`、`STEtermsMid`、`STDuhamelI/II`、`STIniTermI/II`、`STWardII`、`STNewKLKL`、`STCltFar`、`STExpInv`、`STTailtoTail` owed；`STReg5*` structural。
- **`tailTD`**：放进 `RBM3D/Defs/Tail.lean`（S5-01 对该文件只准追加 `tailTD` 及其基本引理），与 `tailT`、`tailW` 同处。
- **拆单**：29 张（S5-01…S5-29，其中 S5-05…S5-08 即 T2039 的 ST2-36…39，§28），约 2.6 万行，在 25–40 区间，不问 Jun（§9 O2）。ST-4 计数改为 1 / 30（设计 + 29）。依赖链：S5-01 先行；S5-17（CltSwapPath）、S5-19（FarEntry）只依赖合并文件，可与 S5-01 并行。高风险：S5-10/11（`lem:pf_step5`）、S5-15、S5-23…25（CLT 矩与组装）。
- 不算返工（设计票审核退回一次已记在返工账）。


## §41 T2134 拆单表 S5-17 的依赖更正：CltPath 依赖 CltResolvent（总调度，2026-10-04 16:06 UTC，流程事项；依据 RBM2D `c9a24cf` 的 `Evolution/CltPath.lean:6` `import RBM2D.Evolution.CltResolvent`）
- portmap P.5 行 S5-17（`Evolution/CltSwapPath` = CltSwap + CltPath，"只依赖 Gauss/Model、Gauss/Envelope"）有误：`CltPath` 用 `CltResolvent` 的 `cltPert_max_le`、`cltPert_sub_le`、`cltDeriv_eval_le`、`cltFarGeomNear` 与 `Case3Defs` 的 `LocalForm`。
- 改为：**S5-17 = `Evolution/CltSwap`**（只移植 CltSwap，329 行，prover，低风险，可立即开工）；**CltPath 并入 S5-18**（`Evolution/CltResolvent` 之后同票，或 S5-18 的第二个文件），S5-18 估计约 1170 行，仍 prover、中风险。张数不变，ST-4 仍记 30。
- 不算返工。

## §42 LW-10（lem:localregular）拆两张（总调度，2026-10-04 16:32 UTC，流程事项；依据 T2040 拆单表行 LW-10（2525 行，prover-max，高风险）、论文 `B:172-278`）
- **LW-10a**：起点图 `|f_xy|^p`（一般偶数 `p`；合并的只有 `p2Graph`）及其值恒等式与计数器、性质 (1)–(6) 的谓词（全部钉出）、`lvl1_lemma_size` 作用于起点图得到 `(eq:local_Gs)`，并证 (1)、(2)（含 `(eq:MolVW)`）、(3)、(5)：分子图上 `p` 条两两边不交的路径跨每一步 `LocStep` 保持（`B:178-199` 三种情形），用 `lvl1_lemma_induction`。
- **LW-10b**：(4)（每个内部分子至少两条路径经过，`B:184-199`）与 (6)（`ord ≥ 2p`，`B:200-278`：特殊轻权与特殊顶点的记账，权重阶段 `ord + n_dv + n_lw` 不减、边与 GG 阶段每去掉一个特殊顶点 `ord` 至少加 1/2；论文对边与 GG 展开"从略"），并组装 `lem:localregular` 全文。等 LW-10a。
- 理由：两部分的不变量互相独立（分子与路径 / 阶与记号），合在一张约 2500 行且论文有"从略"处；拆开各自可审。LW 总张数 30 → 31（LW-10a、LW-10b），计数口径不变。
- 不算返工。

## §43 T2141（S5-19）预检 BLOCKED：票面钉文的远距尺度 `W^{τ'}ℓ` 不够 CLT 用——改用对数尺度（总调度，2026-10-04 16:45 UTC，流程事项（票面钉文由我起草）；依据 `docs/reports/T2141-prove.md` (a) Consumer check、rows 9–10、Verdicts）
- 消费者 `STCltIsoConcl`（`Step5Pins`，`3_5:2245`）的隔离尺度是 `10 (log W)^3 ℓ_s`，而 `(log W)^3 < W^{τ'}`：`W^{τ'}ℓ` 形式的远距衰减用不上。
- 采纳预检的变体 **`STFarEntryAtLog`**：对一切 `c > 0`、`D' > 0`，`‖G_τ(σ)_{xy}‖ · 1[c (log W)^3 ℓ_τ ≤ |[x]−[y]|_∞] ≺ W^{−D'}`，两种荷。它蕴含原票面形式（指示函数单调），原形式无消费者，不再证。
- 路线：(a) rows 1–8、10–13；`𝒦` 部分用 `RBM.Path.kellStarEv`（阈值 `(log W)^{3/2}ℓ`），`B45_far_main` 只到 `W^{τ}ℓ`，不够。邻居数是 `3^{2d}`（`STgexRHS` 用 `zdistInf ≤ 1` 的立方体），票面写的 `(2d+1)²` 是我的笔误，只差常数。
- 实例改在 `Step5Inst.szCL`（`L_n = 2(n+24)^5`，`W_n = 2^{n+24}`）上：`sz0` 的远集在 `n ≈ 3·10^5` 之前是空的。
- T2141 Amend 1，从 1b（`prover-hard`）续，以现有 (a) 为预检；H67。不算返工（票面钉文是我起草的）。

## §44 S5-22 拆两张（总调度，2026-10-04 18:49 UTC，流程事项；依据 T2134 portmap P.5 行 S5-22、RBM2D `Evolution/MLExpInv.lean`）
- **S5-22a**：钉文 `STExpInv`（`𝔼𝓛^{(2)}` 的平移、反射不变性，`3_5:2196`）——移植 RBM2D `expInvariant` 的路线（块格自同构、细格提升、坐标重标保持高斯律、圈的等变性），`Z2 ↦ Zd d`；确定性 + 律的不变性，约 800 行，prover。
- **S5-22b**：`f^{far}` 的均值部分 `(eq:boundEfar)`（`3_5:2184-2212`：一阶差变二阶差，`(prop:BD2)`）——新陈述，由预检定，S5-25 用；等 S5-22a。
- 理由：S5-22 原估 1200 行，两部分无共同证明工具；前者是端点钉文，可立即开工。ST-4 总数 30 → 31。不算返工。

## §45 监督 2026-10-04 19:48 PASS 的五条观察：照办（总调度，2026-10-04 19:50 UTC，流程事项；依据 `docs/supervisor/2026-10-04-1948.md` O1–O5）
- **O1 计数**：ROUTES「宽口径」一列照页首规则改正（动了 Lean 的返工计入、只改报告的不计、总调度票面/钉文缺陷的 Amend 不计）：ST-1 **40**（已闭合）、ST-2 **34**、ST-4 **16 / 32**、LW **15 / 33**；以后每次放行同步。监督请求照 TEAM §6 写：**ST-3 到 25**、**ST-2 到 40** 时各写一份 `REQ-…`（放行该票的同一轮）。
- **O2 钉文起草**：总调度在证明票里起草新钉文时，票面写出**消费者陈述（file:line）**，预检的「消费者核对」为必填一行。§29 的固定核对项加三条：(5) 按时刻（`PrecPT`，并集在概率外）还是关于时间一致（`Prec`，并集在概率内）；(6) 由 `(eq:WO)`、`SizeTendsto` 提供的参数下界（`g ≥ W^{-Q}`、`N → ∞`、`0 < lam` 最终成立）是否写进前提；(7) 尺度是否对上消费者（`(log W)^k ℓ` 还是 `W^{τ}ℓ`）。
- **O3 接口**（写进下列票的目标）：(1) ST2-34/35 以 RBM2D `YMomentsUnifN`（`AzumaProxyN:2042`）为目标（`C_P` 在 `C_K`、`K` 之前），并核对它在 portmap 给 ST2-34/35 的范围内；(2) `u = 0` 时 `0 ∈ GoodSetN` 写成 Lean 引理，放进 ST2-34（或 S3-10）的目标；(3) S3-10 票面写明 `ellT_mono` 的逐点 `0 ≤ lam n` 的处理（最终形式 + 有限项改动引理，或 `g < 0` 时 `ellT = min 1 L` 的直接论证）。
- **O4 设计单**：BA-D1、UN-D1（只出报告的设计单）在有槽位时尽早放行；ST-D5、ST-D6、MA 冻结单随后。若设计单预判某块超过 50 张，在开工前问 Jun（§9 O2）。ROUTES 的 MA、EK 行过时文字顺手改。
- **O5 孤儿 owed 项**（`STBootstrap`、`STForbidden`）：并入最后的清理票，不单开。

## §46 停掉 blueprint 的发布（Jun，2026-10-04 20:16 UTC：「不要再push blue print 总出错搞不定算了」）
- `.github/workflows/blueprint.yml`（"Compile blueprint"，doc-gen4 + Pages）不再随 push 触发：去掉 `on: push`，只留 `workflow_dispatch`（手动）。快速编译检查 `lean_action_ci.yml` 不动。
- 从此不写 blueprint-sync 票，`blueprint/` 目录不动；CLAUDE.md「Blueprint and CI」一节加一行说明。由中枢执行 H68。

## §47 LW-10b 的性质 (6) 预检受阻：拆出 LW-10c，起 Fable 查证明（总调度，2026-10-04 21:58 UTC，流程事项；依据 `docs/reports/T2151-prove.md` (a) Verdicts、`docs/queue/T2151.state` BLOCKED）
- **事**：T2151（LW-10b）预检：性质 (4) PASS（需一个带颜色的新不变量族）；性质 (6) `ord ≥ 2p` 受阻——票面照论文 `B:275-277` 写的步进断言 (E)（「去掉一个 distinguished vertex 使 `ord` 至少升 1/2，故 `2·ord + n_dv` 不降」）**不成立**（`M_x = M_y` 时 9 → ≤ 8；`M_x ≠ M_y` 的 bubble 例中也不单调，候选 A3 亦不单调）；但 (6) 本身未被数值反驳（`p = 2` 最小 4、`p = 4` 最小 8，都 `= 2p`）。论文对边与 `GG` 情形写「we omit the details」。
- **定**：(1) **T2151 Amend 1**：目标 2（性质 (6)）移出；目标 3 改成 (1)–(5) 的组装 `lw_localregular_upto5`（`(eq:local_Gs)` 与每个 `Q ∈ outs` 的 `LocReg1 ∧ LocReg2 p ∧ LocReg345 p`，一族共同路径）；从 1b 续跑，现有 (a) 作预检。(2) **新 LW-10c**：性质 (6) 与带 (6) 的完整组装 `lw_localregular`；(6) 照论文在 `(eq:far_ab)`（`M_x ≠ M_y`，`7_8:792`）下陈述，`M_x = M_y` 的输出照 `(scalemole)` 归入误差项（做法由 LW-10c 预检定）。LW-10c 等 Fable 报告再写。(3) **起 Fable 5.1 子代理一个**：找 (6) 的正确归纳不变量（对 `LocStep` 每一情形单调）或反例，报告写到 `docs/claude-team/fable/2026-10-04-localreg6.md`。
- **理由**：(4) 与 (1)–(5) 的组装已可证，LW-11（AuxGraph，用 (2) `(eq:MolVW)`）不必等 (6)；(6) 是论文略去的证明，先查清再开票。若 Fable 发现 (6) 在 `M_x ≠ M_y` 下不成立，再按路线级问题问 Jun。LW 总数 33 → 34。不算返工（票面照论文略去的论证写错）。

## §48 UN-D1（T2162）签字：核心接口照报告；52 张交 Jun（总调度，2026-10-04 23:20 UTC；依据 `docs/reports/T2162-prove.md`、`docs/reports/T2162-audit.md`（PASS，要签字两项））
- **(i) 2(b) 接口签字**：核心 `UNCore`（探针 `:759`）对抽象模型 `UNModel` 与抽象密度陈述，输入为 `UNL32`（借用，§5）、`UNGUELocal`、`UNGreenCorrAll`、`UNDens`、`UNTrLocal`、`UNNormBound` 与 **`UNClaimAll`（Claim (417)）**；delocalization 与 `(Meq:QUE)` 只进带状模型的行（`UNOURow`、`UNJakUywRow`），由它们产出带状模型的 `UNClaimAll`。理由照报告 b.8 第 2 项：`(EMCTE2)` 的 OU 生成元恒等式对均值非零的 BA 模型带一阶漂移项，核心不能直接吃 BA 的 QUE。**落实**：BA 的 Claim (417)（OU 下的 QUE、带漂移的 `EMCTE2`、Jak/Uyw）归 BA 块，由 BA-D1（T2161）或其后续拆单负责；T2161 不改票（在跑），其报告到时由总调度核对是否已计入，未计入则补一张 BA 设计补充单。
- **(ii) 设计报告合并**：T2162 照常合并（只合并报告与 portmap；探针留在分支 `t/T2162`），由中枢执行 H70。
- **(iii) 张数 52 > 50**（§9 O2）：交 Jun 决定；回复前任何 UN 证明票不开工。UN 的拆单、registry 分类（报告 (d) 4）照报告。
- paper-delta 候选 T2162a–g 在合并簿记时编号。

## §49 S3-10 拆两张（总调度，2026-10-04 23:30 UTC，流程事项；依据 T2041 portmap 行 S3-10、RBM2D `Induction/NonAltGood.lean` 在 `c9a24cf` 已有 2308 行）
- **S3-10a**（`Induction/NQGood1`）：漂移张量及其与 `GoodSetN` 的三条复合、`qvFormN` 的上界、`hker_of_case1`（EK-6），以及好集的时间平移 `u_j → u_{j+1}`（RBM2D §1–§2，连同 `StoppedEndDefs` 里这些要用的定义：`driftTensor`、`qvFormN_eq_re_UgenPair`；那个文件没有分给任何 ST-2 票）。
- **S3-10b**（`Induction/NQGood2`）：常数与类、`GridAssemblyHypN` 各字段、二次变差常数、`subGaussStop_nonAlt`、实例（RBM2D §4–§6）；等 S3-10a。RBM2D §3（`zero_mem_goodSetN`）已由 T2159 合并（D366），不再移植。
- 理由：portmap 估 950 行时 RBM2D 文件约 830 行，现已 2308 行；两半各约 1200 行。ST-3 总数 38 → 39。不算返工。

## §50 UN 批 52 张（Jun，2026-10-05 02:56 UTC 记录：「A」——回答总调度 02:25 UTC 的提问：Thm 2.4 的 UN-D1 拆单 52 张 > 50，A = 批 52 张，B = 把 H_t 的 QUE 与对角 local law 列为第二条授权外部输入、减到 24 张，C = UN 推后）
- UN 按 T2162 的拆单做 52 张（UN-01…UN-52，含 GUE 相 28 张，从 RBM2D 移植并按 d ≥ 3 重做）；外部输入仍只有 LSY Thm 2.2（§5）。
- UN gate 的预算上限按 52 张计；监督的 50 张自动 HOLD 规则对 UN 改为 60 张（52 + 返工余量），25、40 两个请求点照旧。
- §48 (iii) 的「回复前任何 UN 证明票不开工」解除：UN 证明票照 T2162 portmap P.3 的顺序随槽位写票、放行（UN-01 钉文入库先行）。

## §51 BA 的体内条件改成 ρ_N(E) ≥ κ（Jun，2026-10-05 02:58 UTC 记录：「第二个问题A」——回答总调度 02:57 UTC 的提问：Thm 2.7 的体内能量条件，A = 改成 `ρ_N(E) ≥ κ`，B = 保留 `|E| ≤ e_λ − κ` 另加假设，C = BA 推后）
- 依据：T2161（BA-D1）报告 top notice 1、(a)、b.3、b.5 与审核 §2：论文的 `|E| ≤ e_λ − κ`（`1_2:649`、`7_8:1817-1819`）预设 `supp μ_N = [−e_λ, e_λ]`；在可容许参数下 L 为奇数时不对称、L = 4 且 λ ≥ 1/2 时有内部 gap、gap 刚打开处有 cusp（`L = 4`、`λ ≈ 0.354`、`E* ≈ 2.508`，`ρ_N(E*) = 0`），`lem:propM`(2) 的 `Im m ≳ 1` 在那里不成立。
- **定**：Thm 2.7 各项的能量集取 `B_κ = {E : ρ_N(E) ≥ κ}`，`ρ_N(E) = π⁻¹ Im m(E + i0, λ)`（探针的 `BAbulk`）；链上的定义域 `Im m(z, λ) ≥ κ`，桥接钉文 `BAImmLower`；universality 照 §11 的密度归一化。这就是 T2001d、T2001l 的结论（§10 当时暂不签的两项）。paper-delta：T2161b（编号在 T2161 合并簿记时给）。
- T2161 的签字项 (1) 由此了结；签字项 (2)（57 张 > 50）另问 Jun。

## §52 BA 批准，预算上限 70 张（Jun，2026-10-05 02:59 UTC 记录：「A」——回答总调度 02:59 UTC 的提问：Thm 2.7 的 BA 拆单 57 张 > 50；A = 批准、上限 70 张、BA 设计补充单出来后若超过 70 再问，B = 批 57 张但 universality 项暂缓，C = BA 推后）
- BA 照 T2161 的拆单做（57 张：D 6、P 8、K 5、E 3、G 6、S 3、T 8、U 6、V 3、L 4、M 3、N 2），体内条件照 §51。BA gate 预算上限 70 张；监督的 50 张自动 HOLD 规则对 BA 改为 70 张，25、40 两个请求点照旧。
- **BA 设计补充单（BA-D2）**：照 §48 (i)，BA 的 Claim (417)（OU 流下的 QUE、带一阶漂移的 `EMCTE2`、Jak/Uyw 的 BA 形式）未计入 T2161，另派一张只出报告的设计单补上；补充后总数若超过 70，开工前再问 Jun。
- T2161 的两个签字项至此了结（§51、§52）：照常合并报告（只合并报告与 portmap，探针留在 `t/T2161`），由中枢执行 H71。

## §53 拆单：ST2-13、LW-11、S5-06/07（总调度，2026-10-05 03:35 UTC，流程事项；依据 T2168、T2170、T2171 票面）
- **ST2-12/13**：`STGridRepN` 全部约 4000 行，T2168 只做 ST2-12（分解、余项界、由两条尾界组装）；ST2-13 拆 **ST2-13a**（普通尾，之后 `STGridMart` 由 `stGridMart_of_tail` 得出）与 **ST2-13b**（`𝒰` 加权尾，对 `k ≤ K` 一致），都等 T2168。ST-2 39 → 40；放行 13a/13b 那一轮照 §45 O1 写 REQ（ST-2 到 40）。
- **LW-11**：T2170 = **LW-11a**（辅助图、`GtoAG`、scalemole、nested 形式，不用性质 (6)）；`claim:xi` 移到 **LW-11b**。LW 34 → 35。
- **S5-06/07**：整份移植约 2100 行，T2171 = S5-06（`Path/LemDecCalEdif`）；S5-07 另开文件 `Path/LemDecCalEdif2`，等 T2171。T2172（S5-08）约 1700 行，照收。
- T2171/T2172 的新前提（`E2Hyp` 补回 3/4/6-loop 界，下限加强为 `(L^dW^{6d})² ≤ W^D`）由预检核实；T2164 的 M1 因此更紧，S5-09 写票前定。
- （03:53 UTC 补）§52 所说的 BA 设计补充单写为 T2173，标签改称 **BA-DS**（T2173 Amend 1）：T2161 拆单表 P.9 里 BA-D1…BA-D6 是确定性层的行名，避免混淆。

## §54 UN 拆单按导入关系重切（总调度，2026-10-05 05:50 UTC，流程事项；依据 RBM2D `c9a24cf` 各源文件的 `import` 行）
- T2162 portmap P.3 的 UN-02（`OU` + `Step1Cond`）、UN-03（`EigenInterlacing` + `InjSum`）、UN-05（`GreenCorr` + `EigenMeasurable`）各含一个依赖未合并文件的源：`Step1Cond` 导入 `GUEInvariance`、`EigenMeasurable`；`EigenInterlacing` 导入 `RBM2D.Delocalization`；`GreenCorr` 导入 `PoissonSmoothing`、`EigenMeasurable`。按导入重切：**UN-02a** = `OU` + `EigenMeasurable`（T2177）、**UN-03a** = `InjSum` + `PoissonSmoothing`（T2178）、UN-06 = `FreeConv` + `FreeConvStability`（T2176）、UN-08 = `GUEInvariance`（T2175）；之后 `Step1Cond`（等 T2175、T2177）、`GreenCorr`（等 T2177、T2178）、`EigenInterlacing`（先查 `RBM2D.Delocalization` 在 RBM3D 的对应）。总张数大致不变（52 ± 2，在 §50 的 60 张上限内）。

## §55 LW-10c：Fable 证出局部引理，性质 (6) 按 `2p ≤ ord` 对所有输出陈述（总调度，2026-10-05 05:50 UTC，流程事项；依据 `docs/claude-team/fable/2026-10-05-localreg6-locallemma.md`）
- Fable（claude-fable-5-1）把代价改成局部代价 `c = ord + #elem`（elementary = 孤立 light-weight 或 SC 顶点，不再记链），`Φ(Q) = min_π c(M_π Q)`；对每个 `LocStep` 输出证明步进引理 `Φ(Q') ≥ Φ(Q)`（17 个项分解为 7 个原语，逐原语有手证与表；唯一 `Δc < 0` 的形状是 2-圈塌缩，由合并修复，不合并两个外部顶点）；`Φ^all(Γ_p) = 2p`、`Φ^far(Γ_p) = 3p`。数值：229164 个抽象构型、3.6 M 具体实例、1240 个可达状态上暴力求 `Φ`，0 反例。**无数学缺口。**
- **定**：LW-10c 照报告 §(4) 的钉文形状（`LGraph.scost`、`PGraph.LocCostGe far k`、`locCostGe_locStep`、`fxyPowGraph_locCostGe`、`locReg6_of_locCostGe`），(6) 陈述为对每个输出 `2p ≤ ord`，`M_x ≠ M_y` 下 `3p ≤ ord` 作推论；§47 里「`M_x = M_y` 的输出照 `(scalemole)` 归入误差项」不再需要。拆 4 张（LW-10c1…c4，约 1300/1400/1300/1200 行），LW 35 → 38。paper-delta：T2151a–c 在 LW-10c 合并时编号。

## §56 T2176、T2178 的合并签字（总调度，2026-10-05 06:14 UTC，流程事项；依据 `docs/reports/T2176-audit.md` §3、`docs/queue/T2178.state`）
- **T2176（UN-06）**：`freeConv_stable_local` 的实例保留确定性前提 `hyp`（`mV v` 在窗口上接近伸缩半圆），其余前提全部卸掉；照审核的方案 (A) 签字。理由：满足 `hyp` 的 `v` 至少约 `2.3·10^5` 个点（审核 §3 脚本），Lean 见证不可行；`hyp` 由下游 local law 提供（同 RBM2D `FreeConvStabilityCheck`）；非空真由报告 (a)(ii-c) 的 `N = 10^6` 分位测度数值核对支持。票面建议的 `v ≡ 0`（`Fin 3`）被证明违反 `hyp`，是票面错，不算返工。T2176 Amend 1，H74 合并。
- **T2178（UN-03a）**：未登记的前提 `RBM.Univ.InjSum_IsTestFun`（测试函数光滑且紧支）按 §20 归 **structural**；T2178 Amend 1（repairer 只加一行登记、预检、第 2 轮只审 `Axioms.lean` 差异），H75。不算返工（§20 同 T2029）。
- **今后的移植票**：票面「唯一可写文件」一律加上 `RBM3D/Test/Axioms.lean`（只追加登记行），并写明登记预检（§20 (1)(2)）。

## §57 BA-DS（T2173）签字：中心化 OU 流按「加主撇后继」实现，UN-25…52 写成模型通用（总调度，2026-10-05 06:58 UTC，流程事项；依据 `docs/reports/T2173-prove.md`、`docs/reports/T2173-audit.md` §6）
- **事**：BA 的 Claim (417) 要走中心化 OU 流 `λΨ + e^{-t/2}V + √(1−e^{-t})H'`（T2162 的 `ouMat` 带均值 `e^{-t/2}λΨ`，生成元恒等式的漂移项不衰减，报告 b.5）。报告方案 A1 改动已合并的 `UNModel`（加 `mean`）与 `ouMat`（T2174 `Universality/Pins.lean:104,150`）及 `OU.lean` 三行；另给不改动的方案（(d)2：流与初值放进 `UNKind`，主撇的 pin 副本）。BA 总数 62（61…66）≤ 70 的前提是 UN-25…52 写成模型通用；只写带状则 75 > 70。
- **定**：(1) **不改已合并的签名**（CLAUDE.md §5.3）：UN-01b 在新文件里加 `UNKind`、中心化流与初值、模型通用的主撇 pin 与行（报告的 `UN*k`、`un_claimAll_of_rowsk`），以及「`mean = 0` 时与 `ouMat` 一致」的桥接引理；`Universality/Pins.lean`、`OU.lean`、`EigenMeasurable.lean` 与在跑的 T2183（`Step1Cond`）都不动。(2) **UN-25…52 一律写成模型通用**（对 `UNKind`），BA 不另做 28 张双胞胎；BA 总数按 62 计（上限 70，不问 Jun）；UN 53 张（加 UN-01b，上限 60）。(3) **T2173a**：T2161 的 BA 钉文用的是 `sz.seqP`（高斯部分是带状剖面），BA 的律应为 `(sz.withLam 0).seqP`（编译见证 `seqGvar_ne_withLam_zero`）；BA 第一批票（BA-C1 起）照报告带律参数（`PrecL`、`BAEnd_QUEL`）重钉，T2161 探针里的旧形式不照抄。(4) T2173 照常合并报告（探针留在 `t/T2173`），H77。

## §58 S3-12 暂停：预算里的 `Φ²` 吸收不进 `STNQConcl` 的线性右端；BA-D1 拆 a/b；UN-01b 的结构（总调度，2026-10-05 07:19 UTC，流程事项；依据 S3-12 票面草稿（未发）、`docs/reports/T2179-prove.md` (d) T2179a、`docs/reports/T2146-prove.md` 表行 4）
- **事**：起草 S3-12（`STNQConcl` 端点）时查出：合并的 `GoodSetN`（T2146）只有一个水平 `Φ`，(D2) 条款给漂移 `Γk(ΓΦ)²`，于是 S3-11 的预算是 `(Λ^{1/2} + Φ + Φ²)B_v^k`（D449）；`Φ` 要覆盖 `XLK m`（`2 ≤ m ≤ k−1`）等控制量，取 `XL ≡ 1`、`XLK ≡ N^δ` 时钉文右端是 `O(N^δ + …)`，而这条路线至少给 `N^{-2ε₁}N^{2δ}`，故不能证出钉文。钉文本身（论文 `(sahwNQ)` 对乘积线性）没问题；RBM2D 有单独的乘积条款 (G3)、预算线性，T2146 以「无消费者、`k = 2` 太强」删掉了 (G3)（D345）。另一缺口：`STNQConcl` 对当前长度无前提，`GridGoodNConcl` 要 `Ξ̂^{(𝓛−𝒦)}_k` 的界，需按随机水平切片，也要 (D2) 线性才闭合。
- **定**：(1) S3-12 **暂不写票**。候选修法 A：在新文件里加一条线性的 (D2′) 条款与单独的水平 `Φ₂`（`GoodSetN′`，不改已合并签名），重做线性预算（「S3-11b」约 900 行），再写 S3-12a（端点在网格上）、S3-12b（`STNQConcl` 的论文形式）。(2) 修法 A 先请监督复核路线（REQ-2026-10-05-0719）；必要时起 Fable。改钉文（修法 B）是口径级，不采用，除非 A 不通再问 Jun。(3) **BA-D1 拆 a/b**：T2189 = BA-D1a（无律的确定性词汇与钉文，探针 §§0–3）+ BA-D2；BA-D1b（PT 钉文、流、载体、链钉文，探针 §§4–7）照 §57 (3) 用律 `(sz.withLam 0).seqP` 重钉，随 BA-C1；BA 总数仍 62。(4) **UN-01b（T2187）**：均值放进模型（`UNModelC extends UNModel` 加 `mean`），流 `ouMatC` 由均值定义（`UNCoreC` 对所有模型量化，任意流会使它为假）；照准。

## §59 监督 2026-10-05 06:53 PASS 的五条观察：照办（总调度，2026-10-05 07:21 UTC，流程事项；依据 `docs/supervisor/2026-10-05-0653.md` O1–O5）
- **O1 计数**：宽口径只在**放行时**（或动了 Lean 的返工时）加一，合并时不再加；ROUTES 改正为 ST-2 38、ST-3 23、ST-4 25、LW 18、UN 9、BA 3（含 06:13 后放行的票）。ST-4 已到 25，补写 REQ-2026-10-05-0721；ST-3 到 25 时照写。
- **O2**：T2180 Amend 2（只开放接口：粗界与 peeling 引理改公开、各带实例；目标陈述不变；作用于 1b），H78；不算返工（不改陈述）。
- **O3**：ST2-13b 票面写明：核心对 `zeroModeSet Q ∘ UN`、对一切 `Q` 证，`GridRepWTailNAt` 为 `Q = ∅` 的情形（S5-26 的 `STDuhamelConcl` 要 `Q`）；路线照监督答 1 (a)–(d)：一个向量鞅 `V_k = Σ P_j ΔMart_j`、与 `K` 无关的粗**时间**网格、`v_p → u_k` 的转移、二阶部分用 Doob。
- **O4**：Step 2 收尾组合（`3 ≤ d → LWterm d → LWtermExp d → STStep2 d`，经 `ST_step2_of_pins'`、`stGridMart_holds`、`stOptL2_of_pins` 与两条桥）及登记删除（`STStep2`、`STOptL2`、`STLWB`、`STLWT`、陈旧的 `STOptL2` 注释）写进 LW-01 票（或最先证出 `LWterm`、`LWtermExp` 的票）的目标。
- **O5**：T2173 的签字已由 §57 定（不改已合并签名，加主撇后继 `UNModelC`/`ouMatC`，见 T2187），消费者核对由 T2187 的桥接引理承担。

## §60 监督 07:55 建议 HOLD（只限 ST-3 非交错端点）：照办，钉文形式交 Jun（总调度，2026-10-05 08:16 UTC；依据 `docs/supervisor/2026-10-05-0755.md`）
- **事**：(1) `Φ²` 障碍成立；(2) 修法 A 也到不了 `STNQConcl`：钉文右端的随机跨时刻自项 `B_u^{1/6}·sup_{w∈[s,u]} Ξ̂^{(𝓛−𝒦)}_w`（`STsupXiLK`）定义在单时刻耦合 `seqHflow = √u X` 上，§7 的网格游走路线只能传递单时刻事件，确定性水平的命题推不出随机形式（两点反例）；(3) 唯一可行是把钉文改成 RBM2D `STOeqPT` 的形式（当前长度有确定性控制 `XLK n_`，结论用 `B_u^{1/6}·XLK n_`），自吸收挪到 `STXiBoot`（S3-18b）作有限步确定性自举；路线 (R) 用合并的 `GoodSetN`（粗水平）交一个新的线性集合 `G_lin`，约 3 张票，不复制 `GridGoodN`。交错链（S3-14…18）同样要用确定性水平钉。
- **定**：(1) 照办 HOLD 的范围：不写 S3-11b、S3-12a/b，也不写消费 `STNQConcl` 的票（S3-18b、S3-24b、S3-26），交错链 S3-14…18 在钉文形式定之前也不开工；不改 CONTROL 的 mode（无在跑的 ST-3 票），其他 gate 照常。(2) 钉文改形式是口径级（论文 `lem:STOeq_NQ` 的陈述），已问 Jun（2026-10-05 08:16 UTC，A = 照 RBM2D 确定性形式、自吸收挪到 bootstrap；B = 保留论文形式，需真正的矩阵布朗运动，等于换路线；C = 其他）。

## §61 监督 08:03 PASS（ST-4 到 25）：M1、M3 并入一次钉文修改，由 S5-09 执行（总调度，2026-10-05 08:16 UTC，按 §4 签字的小改动，同 §27、§37；依据 `docs/supervisor/2026-10-05-0803.md`）
- **定**：`STLemDecCalEConcl`（`RBM3D/Induction/Step5Pins.lean:161-163`）的下限前提 `∀ᶠ n, size n ≤ W^D` 改为 `∀ᶠ n, (L^d W^{6d})² ≤ W^D`（T2171/T2172 的下限，D429、D434、D437），并加前提 `∀ n u D, Jst n u D ≤ W_n`（M3：`E2Hyp` 仍带 `J ≤ W` 合取项）。这是削弱（限定 `D` 的范围）；唯一的证明消费者是 `lem:pf_step5`（S5-10/11，未写），其 `STPfConcl` 对 `D` 单调，S5-10 的预检写明下降 `D′ = max(D, D₀)`。合并的消费者只有 `inst_lemDecCalE` 与登记行。S5-09 的票让 `Step5Pins.lean` 对这一处修改可写（同 §34 的做法）。M2 不改钉文（由 `stGbEXP_holds` 经去指示函数、网格提升得到，S5-09 预检）。paper-delta 在 S5-09 合并时编号（续 D374、D429）。
- ST-4 计划改为 33 张（O4）。

## §62 S3-12 钉文改用 RBM2D 确定性形式（Jun，2026-10-05 14:30 UTC：「A」——回答 §60 的问题）；监督 0755 的范围 HOLD 解除；路线 (R) 三张
- **定（Jun）**：A。`STNQConcl`/`STOeqNQ`（`Induction/Step34Pins.lean:428-445`）照 RBM2D `STOeqPT`（`Induction/Defs.lean:247`）的形式重钉：前提 `Ξ̂^{(𝓛−𝒦)}_m ≺ XLK m` 对 `1 ≤ m ≤ n_`（含当前长度）；结论里 `B_u^{1/6}·STsupXiLK … (s n) u n_` 换成 `B_u^{1/6}·XLK n_ u`。原钉文蕴含新钉文（新钉文更弱）。自吸收挪到 `STXiBoot`（S3-18b）的证明里，作有限步确定性自举：起点 `STXiLKM_crudeN` 的 `Ξ̂_n ≤ N^{C₀}`（`𝒦` 用 `STKbound`），每轮用非交错与交错端点（`XLK n_ :=` 当前控制），`B_u^{1/6} ≤ N^{-c}`（`(eq:WO)` 下，S3-18b 预检核对），`⌈C₀/c⌉ + 1` 轮得 `STXiBoot` 的确定性右端。
- **执行（总调度，照监督 0755 答 3）**：
  (1) **钉文用主撇后继**（§57、CLAUDE.md §5.3）：新文件里写 `STNQConcl′`、`STOeqNQ′`，已合并的 `STNQConcl`/`STOeqNQ`/`inst_OeqNQ` 不动；登记表 owed 行从 `STOeqNQ` 改记 `STOeqNQ′`（S3-12a 的票让 `Test/Axioms.lean` 对这一行可写，§20/§56）。paper-delta 在 S3-12a 合并时编号：「`(am;asoiuw)` 的随机跨时刻自项换成当前长度的确定性控制，同 RBM2D `STOeqPT`（§7 所需）」。
  (2) **路线 (R)，三张**：**S3-12a** = 钉文′ + 新集合 `G_lin`（(D1′)、(D2′)、(D3′) 各用自己的确定性水平：(D1′) 取长度 `≤ k−1` 的控制，(D3′) 取 `𝓛` 长度 `n−1…n+1` 的控制，(D2′) 取 `Φ₂ = Σ_{n'} XLK(k+2−n')(XL(n₁')XL(n₂'))^{1/2} + B_u^{1/6}·XLK k`）+ `G_lin` 的可测性（照 `GridGoodN.lean` 的私有 `gridGood_meas_*` 复制）+ 高概率（`stSEforLn_holds` 合取 3、`StochDomAt.mul`、`map_pathH_eq`、至多 `N^C` 个网格时刻取并，同 `gridGoodN_holds` 对 (D2) 的推法）+ 线性预算（`tbInitNonAltN`、`tbQvNonAltN`、`tbDriftN` 取线性水平）+ 主撇 `subGaussStop` 包装，约 1000–1300 行；**S3-12b** = 网格端点（约 1200 行）；**S3-12c** = 流端点（`TimeIcc` 上一致，`Prec`，连续性网；约 800–1000 行）。合并的 `GoodSetN` 取粗水平 `Φ = N^{C₀}`（`hX`、`hY` 确定性成立，`hQ` 保留真 `Λ`），只用它的无水平条款（Herm、Dec、Va、Vb）与 (D4)；不复制 `GridGoodN`；**`GoodSetN` 的水平不得要求控制当前长度**（否则线性预算仍带 `N^{ε₀}·XLK k`）。不能用的已合并件：`dDriftNonAltN`/`nonAlt_hdriftN`（`Φ²` 水平）与 `budgetNonAltN`。
  (3) **S3-11b 取消**（并入 S3-12a 的线性预算）；§58 的「S3-11b + S3-12a/b」换成「S3-12a/b/c」，ST-3 计划仍 41（监督 0755 O1：现实总数 44–46，过 40 那次放行写请求）。
  (4) **交错链 S3-14…18 从一开始就用确定性的当前长度水平钉**（监督 0755 O2；其漂移里的 `ℰ^{(𝓛−𝒦)×(𝓛−𝒦)}` 有同样的自项）；S3-18b 的票写上面的自举；S3-24b、S3-26 消费 `STOeqNQ′`。
  (5) 监督 0755 的范围 HOLD 只到「钉文形式定之前」，条件已满足，解除：S3-12a 现在可写；S3-14…18、S3-18b、S3-24b、S3-26 照依赖写。

## §63 §61 的 M3 前提改为 `Jst ≤ W^{1/2}`；S5-09 的 M2 走 `GijGEXPTSwap` + 网格提升（总调度，2026-10-05 14:58 UTC，按 §4 签字的小改动，同 §61；依据 S5-09 票面起草（T2193）的核对）
- **事**：(1) M3：S5-09 把 `≺` 前提 `Prec STLK2 ≤ Jst·T` 换成确定性 `E2Hyp` 条款时要取 `J := N^{τ'}·Jst`（`≺` 的余量），`E2Hyp`（`Path/LemDecCalE.lean:84`）要 `J ≤ W`；§61 加的前提 `Jst ≤ W` 推不出 `N^{τ'}·Jst ≤ W`。(2) M2：`stGbEXP_holds` 的 `STGijGEX` 右端 `STgexRHS`（`Induction/Defs.lean:92`，两个定向）大于 `E2Hyp` 要的单定向 `gexRHS … [q] [p]`，`Green/Pins.lean:792-793` 的文档串写明反向推不出；监督 0803 说的「由 `stGbEXP_holds` 得」不成立。
- **定**：(1) `STLemDecCalEConcl` 新加的前提写成 `∀ n u D, Jst n u D ≤ W_n^{1/2}`（不是 §61 的 `≤ W_n`）：新下限给 `N ≤ L^dW^{6d} ≤ W^{D/2}`，故 `τ' ≤ 1/D` 时 `N^{τ'} ≤ W^{1/2}`，`J ≤ W` 成立；消费者 `lem:pf_step5` 的停时给 `J* < W^ε`（`ε < 1/2`），照样满足。仍是削弱（多一个前提），已合并消费者不变。S5-10 的票写明供 `Jst ≤ W^{1/2}`。(2) M2 走 `gbEXPV3` → `gijGEXPTSwap_giiGEXPT_of_V3`（每个时刻、无指示函数，需 `AsGMcPT`，由 `STLocalEntryU` 得），再做网格提升到对 `u` 一致（照抄 `Path/NetLift2` 的私有 Lipschitz 辅助引理）；这是 S5-09 的目标 2。预检必须写出网格误差的吸收论证；若要右端带 `W^{-D}` 下限才能吸收，或目标 2 超过 800 行，1a 后停，总调度把它拆成 S5-09a（ST-4 计划 33 → 34）。
- paper-delta 在 S5-09 合并时编号（T2193a 下限、T2193b `J* ≤ W^{1/2}`、T2193c 单定向 `(GijGEX)` 一致形式）。

## §64 监督 15:50 PASS：S5-09 走「实现控制量」路线 (d)，拆出 S5-09a；ST-3 25 复核通过（总调度，2026-10-05 16:05 UTC，流程事项，同 §61/§63；依据 `docs/supervisor/2026-10-05-1550.md`）
- **事**：T2193（S5-09）1a 停于 M2：每个时刻的 (P-e7/8) 不能用网格提升成对 `u` 一致（`gexRHS` 在 `|a−b| > 1` 无多项式下限），T2193 (a) 行 (3) 正确；监督撤回 0803 答 2 的 M2 说法。
- **定**：(1) 照监督答 2.1 的路线 (d)：确定性引理**逐时刻**在实现控制量 `J♯(n,u,ω) := max(1, max_{σ,a} STLK2/STtailTD)` 上用（`E2Hyp` 只在每个时刻、每个矩阵上要），再用合并的 `cont_core`（`ContinuityNet.lean:142-154`，`ζ` 可随机）对**结论**做网格提升（右端 `J♯^{m_i}R_i` 有下限、对 `u` 相对连续）；最后在假设事件上 `J♯ ≤ N^{τ''}Jst` 对一切 `u` 同时成立。不改钉文、不加 `E2Hyp′`、不做衰减自举；无须 Jun。(2) **拆**：**S5-09a**（新票 T2198）= (L1) `STLK2`、`‖STELKLK‖`、`‖STEGt‖`、`‖STee‖` 在 `{‖X‖ ≤ N^C}` 上对 `u` Hölder-1/2（多项式常数；照抄 `Path/NetLift2` 的私有 `nl2_entry_diff`、`nl2_word_diff`/`nl2_loop_sub`、`nl2_eta_inv_le`，或公开的 `Theta_sub_Theta`、`gdn_K_lip`），**公开**（S5-13 也要，监督 O1）+ (L2) 确定性因子 `R_i` 的相对连续 + 通用引理「`PrecPT(ξ ≤ J♯^m R)` + Lipschitz + 下限 ⇒ `Prec`」；**S5-09**（T2193，Amend 1）= 目标 1（钉文改动，1a 已 PASS）+ (P) 逐时刻 + (N)(C) 组装，等 T2198 合并后从 1b 续（1a 的目标 1、3 的结论与合取项表照用）。ST-4 计划 33 → 34。T2193 重启不计返工（未动 Lean，§45）。(3) paper-delta：T2193c 作废，改 T2193c′「`lem_dec_calE` 对 `u` 一致：每个时刻在实现控制量上用确定性引理，结论做网格提升（§7）」；T2193a、T2193b 不变。(4) **网格提升规则**（监督 O1，写进以后的票）：只提升右端确定、或随机但连续且有多项式下限的界；右端随机且无下限的逐时刻条款（`GijGEX`/`GiiGEX` 型）一律不提升，改为逐时刻用确定性引理再提升其结论。(5) ST-3 25 复核 PASS（计划 41，S3-14 拆则 42；现实 44–47；过 40、45 时写请求）；交错链：S3-15/16 取确定性 `X ≥ 1`、`Ξ̂ ≺ X`（同 `STWardTypeP`/`STB45`），**S3-18a 的票必须在全为确定性水平的交错好集族上实例化 T2194 的 7b**（无须控制当前长度的 `Φ`），写进其预检脚本核对 (iii)。(6) ROUTES：ST-5 记 1（T2191）、MA 记 1（T2192）（设计票放行即计，§59 O1）。

## §65 T2190a：合并的 `UNDens` 偏弱（已编译见证），`UNStep1Good`/`UNCore` 疑似与带状行矛盾；UN-01c 主撇后继待写，先请监督复核（总调度，2026-10-05 16:28 UTC，流程事项；依据 `docs/reports/T2190-prove.md` (d) d.2、`docs/tickets/T2190.md` 的 Finding T2190a）
- **事**：T2190（UN-07，d1a0316）目标 6 编译了 `unDens_not_eta_determined`：一列在 `Im z ≥ h_n`（任意 `h_n > 0`）上等于 `msc` 的数据满足 `UNDens`，但 `ρ_n = ρ_sc(0) + 1/(2π)`；故 `UNDens` 的 `ρ_n` 不由高度 `≥ h_n` 上的 `m_n` 决定，而 `UNTrLocal` 只看 `Im z ≥ N^{-1+ε}`。票面论证（未编译）：`vOU` 及其自由卷积与 `m` 无关，`UNStep1Good` 用于带状模型的 `(msc, ρ_sc)` 与上面那列数据会给出两个不相容的结论，故 `UNStep1Good`（owed，UN-12）与 `UNTrLocalBandRow`、`UNNormBandRow` 矛盾；`UNCore` 经两个伸缩下的 `UNUnivDilAt` 同理。T2190 目标 3、5：BA 数据（`m_{u ⊞ sc_1}` 类）同时满足合并的 `UNDens` 与更强的复 Lipschitz 条件（盒 `|Re z − E| ≤ δ`、`0 < Im z ≤ 1` 上对 `n` 一致）。
- **定**：(1) 照 CLAUDE.md §5.3、§57 (1)：不改已合并签名；修法是新文件里的主撇后继 `UNDens′`（参照对 `z` 作为复函数在盒上 Lipschitz、对 `n` 一致，即 T2190 目标 4 的前提）、`UNStep1Good′`、`UNCore′`，消费者改接主撇版（UN-12 证 `UNStep1Good′`；BA-C2 的 `UNDensBARow` 给 `UNDens′`）。(2) 先写 REQ 给监督（REQ-2026-10-05-1628）：确认矛盾论证、主撇钉文的形状与消费者链；监督答复前不写 UN-12 与 UN-01c，其他 UN 票（UN-25 = T2196 在跑、UN-09/10 等不碰这三条钉文的）照常。(3) UN 计划因 UN-01c 加 1（53 → 54，上限 60）；在监督答复后定。

## §66 监督 16:51 PASS（T2190a）：UN-01c 一张票，主撇后继含 `UNInfty1Row′`；四条假钉文移出 owed；BA 钉文先过「两组数据、一个模型」检验（总调度，2026-10-05 17:07 UTC，流程事项；依据 `docs/supervisor/2026-10-05-1651.md`）
- **定**：(1) 照监督 3.1 的表写 **UN-01c**（新票 T2201，`prover-hard`，500–800 行，新文件 + 登记行）：`UNDens′`（合并的 `UNDens` 加 T2190 目标 4 的盒假设：`Im` 下界、范数界、作为复函数 Lipschitz，常数对 `n` 一致；结构性）+ `UNDens′.toUNDens`；`UNStep1Good′`（owed，UN-12）；`UNInfty1Row′`（owed，UN-14；请求漏列，监督补）；`UNCore′` + `un_core_of_rows′`；定理 `UNDensBandRow → UNDensBandRow′`；`un_bUniv_of_rows′`；`UNStep1GoodC′`、`UNCoreC′`（owed）；主撇实例（`UNDens′` 在 `msc`、`E = 0`、`δ = 1/2` 上由 `stable_lip_msc` 的常数给）；加编译的反驳 `unDens_shift` 与 `not_UNStep1Good`（只用合并事实）。(2) 登记：加 `UNDens′`（结构性）与四条主撇 owed；**把四条假钉文 `UNStep1Good`、`UNInfty1Row`、`UNStep1GoodC`、`UNCoreC` 移出 owed**，另记「被取代、已反驳」一类（定义保留，CLAUDE.md §5.3），否则「owed 为空」到不了。(3) 后续票改接主撇：UN-12 证 `UNStep1Good′`（及 `UNStep1GoodC′`）；UN-13 若陈述含 `UNDens` 写票时查；UN-14 证 `UNInfty1Row′`；BA-C1b 用 `UNDensBARow′`、`baBUniv_of_rows` 走 `UNCoreC′`（T2197 第 28 行的拆分说明已改）。(4) UN 计划 53 → 54（上限 60）。(5) 监督 O1：BA 的钉文（T2161 探针、T2197 `BA/FlowPins`）在写 BA-C1b 前先请监督做「两组数据、一个模型」检验（REQ-2026-10-05-1708）；以后新路线的钉文签字前都写请求（TEAM §6）。

## §67 T2191（ST-D5 = Step 6 设计）签字：报告合并，Step 6 计划 14 张；一般 `STStep6` 的拼接（S6-13）与 S5-29 的路线 (A)/(B) 先请监督（总调度，2026-10-05 17:45 UTC，同 §57 签设计票的做法；依据 `docs/reports/T2191-audit.md` §2「Target 5(a)」、`docs/reports/T2191-prove.md` (d)）
- **事**：审核除一项外全部 PASS；BLOCKED 项：由四个区域钉文拼出一般 `STStep6` 只在特殊情形编译（`STGenericPos`：每个 `[s_n,t_n]` 含三个边界；或固定阶段顺序）。一般 `(s,t)` 下非空阶段的集合随 `n` 变，空阶段喂不进区域钉文（`STIngR6` 要 `s_n < t_n`）。审核与证明者给两条路：(A) 把 `ℕ` 按非空阶段模式分成有限类，做「钉文到尺寸子列」的转移（`seqP` 是 `Measure.infinitePi`，库里尚无子列/`StrictMono` 转移）；(B) 把区域条件放进指标集重钉区域钉文（同 `LWtermEXP`；偏离票面的 `STStep6R d R` 形状）。合并的 `STStep5`（S5-29，未写）有同一缺口；另：合并的 `STStep3R/4R/5R` 带 `STStep2Concl … C_d`，其损失 `((1-s)/(1-u))^{C_d}` 不随起点 `s' > s` 限制，S5-29 是否满足未查。
- **定**：(1) T2191 作只出报告的设计票合并（报告与状态文件；探针 `Probe/T2191Pins.lean` 留在分支，S6-01 照它建 `Induction/Step6Pins.lean`）；H84。(2) Step 6 计划 = 1 设计 + 13 证明票（S6-01…S6-13），ROUTES 记在 ST-5 行（14 张，远低于 25）。(3) 路线 (A)/(B) 是路线级，写 REQ-2026-10-05-1746 请监督定（同时管 S6-13 与 S5-29，及 `C_d` 损失的限制问题）；答复前不写 S6-13、S5-29，其余 S6 票（先 S6-01 钉文文件）照依赖写。(4) paper-delta T2191a–e 在本次合并编号。

## §68 监督 18:06：BA Step-1/归纳钉文范围 HOLD（`BAConArg` 为假；BA Step 1 按单条流闭不上）；ST 拼接改在主归纳层、走 (A) 子列转移，S3-27、S5-29、S6-13 不要了（总调度，2026-10-05 18:18 UTC，照办；依据 `docs/supervisor/2026-10-05-1806.md`）
- **BA（REQ-1708）**：(1) **范围 HOLD 照办**：T2197 撤出 Released（未开工），等它的 Amend 1 与 BA Step-1 设计单（**BA-D3**，新票）都经监督复核后再放；BA-S1、BA-S3、BA-V2 不写。其余（确定性层 `MFixedPoint`、PT 钉文、D472、载体、BA-DS、BA-C1b 拆分说明）PASS。(2) **F1**：`BAConArg`（探针 `:1160`，T2197 目标 5）按钉文为假：`g_s = √(s/t)g₀` 处 `E` 可在支撑外，`η_s = 0`（监督给了 `d = 3` 的数值实例；只有块对角高斯势的高概率算子范数界未编译）。主撇 `BAConArg′` 加假设 `∀ n, κ ≤ Im BAmF … (BAlamS …) …`（`E` 在耦合 `g_s` 的 κ-体内）。(3) **F2**：`BAStep1`、`BAMainInd` 为真，但论文路线按单条流闭不上（BA 中 `g₀Ψ` 不随 `√(t/s)` 缩放，ConArg 换流）；修法（交 BA-D3 核）：在耦合窗 `g' ∈ [g₀√(1−c₁), g₀]` 上对流族陈述 Step 1 与归纳；确定性钉文「`m(E,·)` 在 κ-体上对耦合 Lipschitz」；ConArg 链从 `s₀ = 1 − c₁` 起。§51 的体集合保留，不问 Jun。(4) **T2197 Amend 1**（照监督 1.6）：目标 5 中 `BAConArg` 换成 `BAConArg′`（替换 L5）；`BAStep1`、`BAMainInd`、`inst_BAStep1`、`inst_BAMainInd` 推迟到 BA-D3；登记 `BAConArg′` owed（BA-S1），不登 `BAConArg`；加 `baSelf_none_of_gt`、`not_BAConArg_of_norm`（范数界作显式前提）；目标 1–4 不变。(5) BA 计划 62 → 63（BA-D3）。(6) 监督 O1：T2001g 把 `zztE_BA` 的 `|Re z| ≤ 2 − κ` 当笔误要重议（在论文 ConArg 路线下它正是让耦合路径留在体内的条件）；paper-delta 随 BA-D3 写。
- **ST 拼接（REQ-1746）**：(7) 在**主归纳层**拼（不是拼 Step 5/6 的结论）：`ST_mainIndR_of_steps R`（R ∈ {(iii),(i),(ii),(iv)}，用 `STStep1`、`STStep2`、对齐的 `STStep3/4`、`STStep5R_R`、`STStep6R_R`，证明照 T2191 目标 5(b)）+ `ST_mainInd_of_regimes`（按非空阶段模式类（10 种）用 (A) 组合）。每个阶段起点的输入都由上一阶段给（`STLK_of_STLKU_at`、`STLocalMax`、`STDecay_of_STGdecayW_at`、`STDecayStrong`、`STExp2_of_STExp2U`、`st_conStInd_sub`）。原因：合并的 `STIngR5` 有两个锚在 `s` 的前提（`STGdecayW s t C_d` 的 `((1−s)/(1−s'))^{C_d}`、`STStep1Loop` 的 `(L^d/4)^{k−1}`），限制到后起点吸收不了。(8) **(A) 一张通用票**：`Sizes.comp φ`（`StrictMono φ`）、`SeqΩ` 的重标号映射（对 `seqP` 保测）、逐 `n` 对象与之交换（预期 `rfl`）、`Prec_comp_iff`、有限分划覆盖引理；对任意律（`PrecL` 形式）陈述，BA 也要用。(9) 一般的 `STStep3`、`STStep4`（S3-27）、`STStep5`（S5-29）、`STStep6`（S6-13）不再被消费：三张票取消，登记移出 owed 进「被取代、不需要」类（定义保留，同 §66 (2)）。(10) 计数：ST-3 计划 41 → 40（去 S3-27），ST-4 34 → 33（去 S5-29），ST-5 仍 14（S6-13 换成主层区域组装），(A) 票 +1，记在 ST-5（15）。MA-D1 不受影响（`STMainInd` 接口不变）；若其拆分表列了 S3-27/S5-29/S6-13，换成 (A) 票与区域组装。

## §69 监督 19:55（REQ-1928）：A 部分 R2*（自举右端首项改 `B_s`）待 Jun；B 部分 C 形式重钉（`UNTrLocalInit′`、`UNMeanBound`、`UNStep1GoodC″`、`UNCoreC″`），UN-12b 加 1（总调度，2026-10-05 20:03 UTC；依据 `docs/supervisor/2026-10-05-1955.md`）
- **A（S3-12c，草稿 `docs/tickets/drafts/T2207-draft.md`）**：G1 成立：合并 `GoodSetN` 的 (D4) 单水平 `Λ`，`hQ` 要求在窗内每个时刻成立，最小可取水平在 `B_s`，终点多 `(B_v/B_s)^{1/(4p)}`，在区域 (iii) 可达 `N` 的一个幂。R1（S3-12b′ 加 (D4′)）只修非交错端点；**交错情形 (i)**（`sum_res_2`，每份幂 `n`）无论单水平还是 (D4′) 都只到 `B_s^{-1/(4p)}`（paper-delta 候选 T2207d：`3_5:1676-1690` 的 `B_{u,0}` 不随所引核界得出）。所有下游只用这一项里 `B` 的时间一致下界（合并的 `iterationsA_step` 只用 `(cv·A)⁻¹ ≤ B_u` 在 `w = s`；Step 4 论文 (saww02) 本就在 `B_{s,0}`）。**监督建议 R2***：主撇后继 `STNQConcl″`、`STOeqNQ″`、`STXiBoot′`、`STOeqQt′`、`STOeqQtNZ′`、`STIterR′`（→ `STIterations′`、`STIterationsII′`），`STbootRHS … (sz.Bctl n (s n))` 代替 `(sz.Bctl n u)`，只动首项，`B_u^{1/6}·XLK` 不变；桥 `STNQConcl′ → STNQConcl″`、`STXiBoot → STXiBoot′` 平凡；旧 owed 移入「被取代、不需要」；合并的 S3-12b、S3-14 照用，不要 S3-12b′。这改的是 §62（Jun「A」）签的钉文内容 → **问 Jun**（2026-10-05 20:03 UTC）。答前：T2207 不放；S3-15…18、S3-21/22 不按最终钉文形式写；在跑的不受影响。G2 成立，单调包络 `X♯(u) := inf_{u′∈[u,t]} X(u′)` 的路线可靠，不改钉文（监督承认 1550 的界面核对漏了 `hclose`）。G3（`𝒦^{(k)}` 时间模，`KLK_isKLoop` + 中值定理，约 200 行）、G4、`RangeCond`（`v3_premises_of_stFlow`）、窗口条件（`st_window`，要 `d·𝔠_d < 1`）都有已合并来源。S3-12c 拆 c1（逐时刻端点在 `B_s`，约 800 行）/c2（包络、单侧 core、`𝒦` 模、提升，600–700 行）：ST-3 计划 40 → 41（R2* 钉文若单独一票则 42）。
- **B（UN-12，T2208 照跑）**：T2208a（`UNStep1GoodC′` 为假：均值无界）、T2208b（`UNTrLocalInit` 对带状模型为假：`ouInit` 谱移 `≈ 0.17·t*` 超出容差）都对（论证）。修法照办：`UNTrLocalInit′`（容差加 `W^τ·ouTStar`，owed，BA 行）、`UNMeanBound sz M CV₀`（结构性）、`UNStep1GoodC″`、`UNCoreC″`（owed）；`UNTrLocalInit`、`UNStep1GoodC′`、`UNCoreC′` 移入 refuted/superseded；推荐编译条件反驳 `not_UNStep1GoodC′_of_diag`。新票 **UN-12b**（重钉 + 反驳 + C 形式 Step 1，600–900 行），UN 计划 55 → 56（上限 60）。T2205（BA-D3）不改（监督复核其报告时：BA-D8 若仍开放，复盒形式更合 BA-C1b）；**BA-C1b 拆分说明改指 `UNCoreC″`**（T2197 第 29 行）。
- 监督 O3（TEAM §8 候选）：实例保留某前提时，预检要用数字说明带状与 BA 模型满足它（「两组数据、一个模型」抓不到「预期模型不满足前提」）。

## §70 T2209（S5-10）1a 的 F2：一个 `D` 闭不上 S5-11 的停时环；改用随时间变的水平 `D_u`；目标 7 拆成 S5-10a（总调度，2026-10-05 20:42 UTC，流程事项；依据 `docs/reports/T2209-prove.md` (a)）
- **事**：LK×LK 漂移的下限项 `N^τJ²W^{-d}(1−t′)^{-2}W^{-D′}`，停时比要 `≤ W^εW^{-D′}`；在 WO 边界 `1 − t′ = lam² = W^{−d+2𝔡}` 多出 `W^{ε+d−4𝔡}`，只在 `𝔡 ≥ (d+ε)/4` 时闭。§63 与 T2193 Amend 1 给 S5-10 的「`D′ = max(D, D₀)`」说明不够（T2209 起草时的 F1 已改用 S5-09 的逐时刻件）。
- **定**：(1) 照预检的修法：`D_u := D* + 2 log_W(1−u)`，`D* := max(D, D₀) + 2d + 1`；`W^{−D_u} = (1−u)^{−2}W^{−D*}`，`ρ_j²W^{−D_{u_j}} = (1−u_k)^{−2}W^{−D*}`；在 `(u, D_u)` 上对 `J♯` 停；最后由目标 1 降到 `D`（`D_u ≥ D`）。不改钉文（`STPfConcl` 对 `D` 单调）。(2) T2209 Amend 1：目标 2 换成 2′（水平为序列 `D : ℕ → ℝ`，原 2 为推论），采用 4′；目标 7 拆出为 **S5-10a**（新票，`Induction/TailtoTailSq`，近/远对、远程指数 `D₂` 单列）；T2209 从 1b 续（H86）。(3) ST-4 计划 33 → 34。(4) S5-11 的票照报告 (a)「(3) Consumer chain」写。


## §71 S5-11 拆 a/b；S6-11 的 `c ≤ 0` 缺口交预检定（总调度，2026-10-05 22:20 UTC，流程事项）
- **S5-11**：起草估计全票 1900–2400 行（> 1500，§9），拆成 **S5-11a = T2221**（`Induction/PfStep5Grid`：水平 `D_u`、矩阵 `J♯`、(eq:def_TTT) 的网格停时下标、网格分解的确定性 Duhamel 形式；不登记、不提升）与 **S5-11b**（`Induction/PfStep5`：概率、停时、`PrecPT → Prec` 提升（只提升 `STLK2 ≤ N^τ T_{u,D}`，右端确定且有 `W^{-D}` 下限，合 §64 (4)）、`STIngR5` 组装、删 `STPfStep5` 的登记行；等 T2221）。远段指数取 `D₂ = 2D* + C_Y + 2d/𝔠 + 3d + 1`（`4YL^dρ³W^{-D₂} ≤ W^{-2D*}`）。ST-4 计划 34 → 35。
- **S6-11（T2223，T2223a）**：合并的 `STExpIniIConcl`（`Step6Pins.lean:463`）第二部分对任意磨光常数 `c`（含 `c ≤ 0`）量化，论文工具（lem_+Q、sum_res_2）只在 `c > 0` 时可用。票给两条路：A（主撇后继 `STExpIniI'` 加 `0 < C → 0 < c`、新文件里主撇消费者 `ST_step6_caseI_of_pins'`；消费者只造正常数）；B（证合并的 `STExpIniI`、删登记行）。1a 预检定路线；走 A 时总调度写 REQ 请监督核。**`STExpIntQConcl`（S6-09）、`STExpWardIConcl`（S6-10）有同样的量词**：写这两张票前先看 T2223 预检结论。
- **S6-06（T2222）**：格点和已由 `RBM.Loop.KDecay_sum_tailT_le`（`Induction/KDecay.lean:1241`）给出，期望一步走 RBM2D 的一阶矩引理（不需可测性或下限）；`momentDomAt_of_stochDomAt` 路线作备选。估计降到约 900 行。

## §72 BA 范围 HOLD 解除；T2197 Amend 2；BA 事件形式重钉（总调度，2026-10-05 22:54 UTC，流程事项；依据监督 `2026-10-05-2252.md`，PASS）
- (1) 监督 1806 §1.4–§1.6 的范围 HOLD 全部解除。Amend 1 的 `BAConArg'` 与 BA-D3 编译用的钉文逐字一致；`s ≥ 1 − c₁` 是消费者（`BAStep1_of_parts`）的条件，不是钉文的。
- (2) **T2197 Amend 2**（`docs/tickets/T2197-amend-2.md`）：实例 `inst_BAConArg'` 取 `s ≡ t`（一般引理 `BAConArg'_premise_diag`）；额外目标 (b) 改为条件形式 `not_BAConArg_of_data`（> 150 行就删）；推迟 `BAGbEXP*`（不登记）。T2197 随 Amend 1、2 重新放行。`s < t` 的 ConArg 实例（`sz0_conArg_bulk`）进 BA-S3 的移植单；BA-S3 另加 `BALmaxFromLK_holds` 的具体实例（审核 O1）。
- (3) BA-D8、BA-S1、BA-S2a、BA-S3 可写；BA-S1 的依赖去掉 BA-G6、BA-K4（预检确认）；BA-V2a/b 只等依赖，票里写出 `κ/2` 一步（`BAWinBulk_of_dom`，审核 O5）。
- (4) **T2205e 不是 HOLD**：全局 `BAGbEXP` 不假（事件形式的推论），但带状镜像路线上无消费者。写 BA-G3…G6、S2b、T2、U5 中第一张之前，在那张票（或 BA-G6）里钉 BA 事件形式 `BAGbEXPii/ij/av`（`STGbEXP*` 加载体上的 `STindMax`、律 `Sizes.seqP (sz.withLam 0)`）；BA 计数不变（66）。
- (5) D539 照监督 O2 补一句：论文的全局形式是对的，事件形式是连续性论证在形式化里的要求。

## §73 S6-12 拆 a/b；Step 6 区域 (i) 磨光常数照监督 2347 定（总调度，2026-10-05 23:57 UTC，流程事项；依据 `docs/supervisor/2026-10-05-2347.md`，PASS）
- (1) **S6-12** 估计 1550 行（> 1500），拆成 **S6-12a = T2229**（`Induction/ExpWardII`，证 `STExpWardII`；合并的 `stWardII_identity` `WardII.lean:143` 可用）与 **S6-12b**（`Induction/ExpIntII`，证 `STExpIntII`，prover-max，约 850 行，可与 a 并行）。ST-5 计划 15 → 16。
- (2) **S6-10** 证主撇后继 `STExpWardI'`（`STExpWardIConcl'` = 原文在 `∀ (C c : ℝ)` 后加 `0 < C → 0 < c →`）；可选变体：先证无符号 `STExpWardI`、一行推出 `STExpWardI'`——只在 1a 预检确认尺寸引理（`‖ϑ_u‖_∞ ≤ C(e^{|c|d/2} + 2/d) ℓ_u^{-d}`）≤ 100 行、其余证明不用 `c` 时取。
- (3) **S6-09** 证 `STExpIntI'`（前提用 **`STExpWardIConcl'`**，结论第二部分 `STExpIntQConcl'`），并写消费者 `ST_step6_caseI_of_pins''`（只改 `hward`、`hint.2` 两处应用）与 `inst_skeleton6I''`；S6-09 等 S6-10、S6-07。两张都并行时，后合并的那张放消费者。检查文件里放主撇定义；S6-09 的检查加消费者比对（监督 O2）。主撇实例给正常数族（`∃ C c > 0, ϑ`）。
- (4) `ST_step6_caseI_of_pins''` 合并后，无符号 `STExpIniI`、`STExpIntI`、`STExpWardI` 移到「被取代、不需要」（§68 (9)），不进 refuted；`STExpIntQConcl'`、`STExpWardIConcl'` 登记 structural（同 `STExpIniIConcl'`）。在此之前 `STExpIniI` 仍 owed。
- (5) S6-07（T2228）、S6-12 不受影响（无磨光量词）。

## §74 LW-12（`lem:Anp`）拆 6 张（总调度，2026-10-06 00:18 UTC，流程事项；照 §24「写票时再拆成 5–8 张，总数仍按原计划计」）
- **LW-12a = T2234**（`Graph/AnpKey`：`(adsuu22)` 的确定性钉文 `AnpDetGh`、`q = 0` 基例、归纳组装、`≺` 提升 `AnpDetGh → LWAnpKeyGh`、化归 `LWAnpKeyGh → LWAnpKey → LWAnp`；新 owed 行 `AnpDetGhStep`、`AnpDetGh`）；**LW-12b**（`AnpKey2`：区域、末边类型 A1/A2/B1/B2、定点）；**LW-12c/d/e**（`AnpKey3/4/5`：情形 (I)+(II)、(III)、(IV) 前半；b 之后可并行）；**LW-12f**（`AnpKey6`：(IV) 后半、归纳步、删 `LWAnp*` 的登记行）。每张 1000–1500 行，共约 7.5k。LW 计划 38 不变（§24 已按 5–8 张计）。
- 确定性钉文由起草者写成，只假设 ψ 正且不增；若情形 (I)–(IV) 还要 `(eq:Psi)`，LW-12a 预检加成主撇后继，再写 LW-12b。
- LW-14 不要 `lem:Anp`（`B:84-89` 用 Cauchy–Schwarz），依赖已齐，可与 LW-12 并行。

## §75 LW-14 拆 a/b/c（总调度，2026-10-06 00:44 UTC，流程事项）
- LW-14 照 T2040 的中值约 2524 行，拆三张：**LW-14a = T2236**（`Graph/LWExpTerm`：化归 `LWE → LWcut`、圈层项 I₁、I₄₁；新 owed 行 `LWCutExp`、`LWExpG5`）；**LW-14b**（`LWExpTerm2`：GG 展开、∂ 分拆 I₄ = I₄₁ + I₄₂、I₂、I₃、J₁–J₄、组装 `LWExpG5 → LWCutExp`；预检定 `η_t^{-1} ≤ C(1−t)^{-1}` 的归一与 J₄ 是否要主撇 `LWExpG5'`）；**LW-14c**（`LWExpTerm3`：图展开证 I₄₂、删 `LWtermEXP` 登记行）。T2040 计 2.5 张，现 3 张：LW 计划 38 → 39。
- T2236a（候选）：I₁、I₄₁ 用 `(res_ELK_n=1)`，合并钉文与引理陈述都没列；单时刻可由 `LWAvgLaw` 经 `stImproveExpAver_holds` 得，钉文仍可证。

## §76 S6-09 拆 a/b；「被取代」登记暂缓（总调度，2026-10-06 01:22 UTC，流程事项）
- (1) **S6-09** 估计 1700–1900 行，拆成 **S6-09a = T2239**（`Induction/ExpIntI`：定义 `STExpIntQConcl'`、`STExpIntI'`；σ₁=σ₂ 一半、区域 (i) 核界、积分组装；消费者 `ST_step6_caseI_of_pins''`（`hInt : STExpIntI' d` 作前提）、`ST_step6I_of_LW_Int`、`inst_skeleton6I''`）与 **S6-09b**（`Induction/ExpIntIQ`：𝒬 一半、`stExpIntI'_holds`、`inst_expIntI'`、`stStep6I_of_LW`）。ST-5 计划 16 → 17。
- (2) **T2239a**（起草者疑点，列为 T2239 预检必查项）：`(sum_res_2)` 要整个 𝒬 源（含 `(𝒫f)∂ϑ`）快速衰减，而 `STMollifierProps` 的导数条款只给 `∂ϑ` 的大小、不给衰减，`STExpIntQConcl'` 对一切这样的 ϑ 量化。预检确认则 S6-09b 写之前先发 REQ 给监督。
- (3) `Test/Axioms.lean` 没有「被取代、不需要」的列表（§68 (9) 的类），`STStep3/4/5/6` 等仍在 `owedProps`。在建该列表之前（要一张改 `Test/Axioms.lean` 结构的小票，与区域组装或最后清理一起），被取代的钉文保留在 `owedProps`、只改注释；§73 (4) 的移动到那时一起做。

## §77 MA-05 拆 a/b；T2237（BA-S1）1a BLOCKED → REQ（总调度，2026-10-06 01:50 UTC，流程事项）
- (1) **MA-05** 估计约 1580 行，拆成 **MA-05a = T2240**（`Main/QUECore`：RBM2D `QUEFromQDiff.lean:38-812` 的 d≥3 移植（去掉 d=2 的剖面差 `:451-501`）、探针 ThetaDiff `:665-772` 原样、`MAThetaDiff`）与 **MA-05b**（`Main/QUEFromQDiff`：探针 QUE 段 `:1864-2020`、d=3 链、`QUE_of_QDiff`、实例，约 600 行；要重声明 MA-01 的私有 `W_pos_real`、`L_pos_real`、`size_cast`）。MA 计划 7 → 8。
- (2) **T2237（BA-S1）** 1a 判 BLOCKED（P1）：`BAConArgLoop` 对随机因子 `Φ_t = max_a tr(Im G_t E_a)` 线性，带状递归给不出；缺 `Φ_s` 的下界与基界 `|tr G_t E_a| ≲ Φ_t`（数值上一般不成立，`Y_1/Φ_t = 347`）；钉文未证假。后继候选 S-A（加 `STLocalMaxgL`，不够）、S-B（带状的 `Ω_t` 事件形）；都要改 `BABootstrap`（BA-S2b）与骨架 `BAStep1_of_parts`（BA-S3）。**钉文级问题，交监督（REQ-2026-10-06-0149）**；答复前 T2237 扣着（CONTROL 注明）、BA-S2b、BA-S3 不写；BA-S2a（T2238）、BA-C1b（T2241）不受影响。

## §78 LW-14 再拆出 LW-14d（总调度，2026-10-06 02:08 UTC，流程事项）
- LW-14b 起草估计 1900–2300 行，再拆：**LW-14b = T2243**（`Graph/LWExpTerm2`：GG 展开（`oe2x_integral`）、∂ 分拆、σc 共轭、十项与钉文配对、组装 `lwCutExp_of_terms`）；**LW-14d**（`LWExpTerm4`，1100–1400 行：项界 `LWExpI1K`、`LWExpI23K`、`LWExpI41K`）；**LW-14c** 改证主撇 `LWExpG5'`（S 边换成 S⁺；J₄ 要它，§75 (ii) 结论），`LwExpG5OfG5'` 在 b。LW 计划 39 → 40。
- §75 (i)：`η_t^{-1} ≤ √(2/κ)(1−t)^{-1}` 由 `st6_mE_im_ge`（`Step6Kit:544`）给。候选 T2243b：论文「σ = + 同理」（`B:14`）合并钉文未覆盖，`LWExpI41K`、`LWExpG5'` 都写成含 σo = + 的情形，预检查其成立。

## §79 T2239a 确认 → REQ；S6-09b 暂不写；区域组装票（总调度，2026-10-06 02:27 UTC，流程事项）
- (1) T2239 预检确认 T2239a（`STMollifierProps` 第 4 条只给 `∂_tϑ` 的大小、不给衰减；`(sum_res_2)` 要 `(𝒫f)∂ϑ` 衰减；`STExpIntQConcl'` 未证假）。照 §76 (2) 发 REQ-2026-10-06-0226（选项：分部积分 / 加导数衰减条款的后继 `STExpIntQConcl''` 由 `QopAlgebra_mollifier` 满足 / 单独证 `Θ^{(2)}` 像的衰减）。答复前 S6-09b 不写；`STStep6I` 是 Step 6 唯一卡在这里的区域。
- (2) 主归纳区域组装 = **T2245**（`Induction/MainIndRegimes`，§68 (7)）：四个区域的 `ST_mainIndR_of_steps`、十种阶段模式的 `ST_mainInd_of_regimes`、`ST_mainInd_of_pins`（以尚欠的步钉文为前提）；对 R2* 中立（`STStep3I/II`、`STStep4I/II` 作前提）；同票在 `Test/Axioms.lean` 加 `supersededProps` 列表（照 §76 (3)），把 `STStep3/4/5/6`、`STExpIniI`、`STExpIntI` 移进去（§73 (4)：消费者 `ST_step6_caseI_of_pins''` 已随 T2239 合并）。计入 ST-6（计划待 ST-D6）。注：`ST_mainInd_of_steps`、`ST_step6_compose` 等不在 `Step6Kit`（留在 `t/T2191` 探针，`Step6Kit.lean:32-35`），票指向探针 `:351-404`。

## §80 Jun 答 R2*：A（总调度记，2026-10-06 02:46 UTC；Jun 原话「A」，02:4x UTC）
- (1) 照监督 1955 A1 的 R2*：自举钉文右端首项的 `B_u` 换成窗口起点 `B_s`（`STbootRHS … (sz.Bctl n (s n))`），其余项（`B_u^{1/6}·XLK`）不变。主撇后继：`STNQConcl″`、`STOeqNQ″`、`STXiBoot′`、`STOeqQt′`、`STOeqQtNZ′`、`STIterR′`（前提 `STXiBoot′`，推出 `STIterations′`、`STIterationsII′`）。平凡桥 `STNQConcl′ → STNQConcl″`、`STXiBoot → STXiBoot′`。旧 owed（`STOeqNQ′`、`STOeqQt`、`STOeqQtNZ`、`STIterations`、`STIterationsII`）移「被取代、不需要」（`supersededProps` 由 T2245 建；它未合并前照 §76 (3) 留 owed 改注释）。合并的 S3-12b、S3-14 照用；不要 S3-12b′。改的是 §62（Jun「A」）签的钉文内容，Jun 已签。
- (2) 票的安排（监督 1955 A4，总调度定）：钉文定义与桥放进 **S3-12c1**（逐时刻端点，`B_s`，约 800 行）；**S3-12c2**（包络 `X♯`、单侧核、`𝒦` 模、提升，约 600–700 行）等 c1；`STIterR′` 的证明（`iterationsA_step` 在 `w = s` 取 `hlow`，约 50 行）放 **S3-24b**。ST-3 计划 40 → 41（c1/c2 拆；钉文不单开票）。T2207 草稿作废，c1 另编票号重写。
- (3) 解冻：S3-12c1 现在写；S3-15…18、S3-21/22 按主撇最终形式写（依赖到时查）；T2207d（`3_5:1676-1690` 的 `B_{u,0}` 不随所引核界得出）合并 c1 时编号。

## §81 监督 0255：BA-S1 走 S-B（`BAConArg''`，事件形）；S6-09b 走转移 (d)，拆出 S6-09c（总调度，2026-10-06 03:06 UTC，照办；依据 `docs/supervisor/2026-10-06-0255.md`）
- (1) **REQ-0149 PASS，S-B**：`BAConArg''` = `BAConArg'` 的前提照抄，结论换成带状 `STConArg` 的事件形（`Ω_t = {‖G_t‖_max ≤ C₀}`，右端 `((η_s/η_t)Bctl_s)^{k-1}`，无 `Φ_t`）。T2237 照自身目标 1 的停报路径续做：`docs/tickets/T2237-amend-1.md`，从 1a 重启。`BAConArg'` 不进 refuted，进「被取代」。BA-S2b 用 `BABootstrap'`、BA-S3 用 `BAStep1_of_parts'`（从起草起就用）。BA 计数不变 9/66。paper-delta T2237a 合并时编号。不问 Jun。
- (2) **REQ-0226 PASS，路线 (d)**：`STExpIntQConcl'` 照合并形式可证——结论只经 `ϑ_s`、`ϑ_u` 依赖 ϑ，两个容许磨光函数之差 `(𝒫f)(ϑ − ϑ*)` 由前提 `STExpWardIConcl'` 界到 `B³`，故由显式 `ϑ* = QopAlgebra_mollifier`（`C* = (1+40d)6^d`、`c* = 1/4`）转移到整个类。不要新钉文、不要 `''` 后继与消费者孪生。(b) 只在 S6-09b 的 1a 否定转移时作后备；(a) 否决；(c)（`Θ^{(n)}` 像的衰减传递）任何路线都要。
- (3) **S6-09c**（新，确定性，`Induction/QopDecay.lean`，对 `m` 一般、公开，供 ST-3 交错链 O3 用）：`QopAlgebra_mollifier_derivDecay`（约 60 行，`qa_core` 里把 `uSe^{-uS} ≤ 1` 换成 `≤ (2/e)e^{-uS/2}`、用 `qaU_lb`）+ `Θ^{(n)}` 衰减传递（150–300 行，预检确认合并的性质 5 的衰减形式）。S6-09b（转移，100–150 行 + 组装）等 S6-09c。ST-5 计划 17 → 18。paper-delta T2239a（`(eq:derv_Theta)` 应同时给 `∂_tϑ` 衰减；`6:132`、`(eq:alternatecase2)` `3_5:1711-1714` 与 `ℬ₄` 用到的 `Θ^{(n)}` 像衰减未写）现编号 D556。
- (4) 监督 O3：写 S3-15…18（交错链）时把 S6-09c 的引理列为输入（或移植 RBM2D 等价物）。O4：计数过 25/40/50 那轮要写 REQ（LW 过 25 时漏写，监督已补查 PASS）；下次门槛 LW 40、ST-3 40、ST-4 35（计划）。

## §82 `STStep5R` 登记类；返工计数（总调度，2026-10-06 03:20 UTC，流程事项）
- T2245 把 `STStep5R`（`ST_mainIndR_of_steps` 的前提，原不在任何登记表）登记为 structural（同 `STStep6R`）：照准。`STStep3R`/`STStep4R` 仍 owed（不一致，留最后清理）。`supersededProps` 已由 T2245 建（05e5052），之后的被取代钉文都移进去（§76 (3)、§80 (1)、§81 (1)）。
- T2244 审核 RETURN 一次（只改实例段）后 PASS：返工 18/239。

## §83 ST-3 交错链 S3-15 按 d≥3 重排（总调度，2026-10-06 03:40 UTC，流程事项）
- S3-15a = T2250 起草发现：合并的 EK-4 `(sum_res_2)` 只要和为零加衰减，对一切 σ 成立，漂移 `𝒬_u(ℬ₁+ℬ₂+ℬ₃)+ℬ₄+ℬ₅` 逐路径和为零，所以 RBM2D 的 Q/E 分拆（Case 3/4、局部形、`AltExpSymm`、`AltQPartGrid`、T 版）不移植（候选 T2250a）。S3-15a 改为：漂移恒等式、ℬ₄/ℬ₅ 与漂移的和为零、初值项的和为零与核类、经 `𝒬_t` 的衰减、由 EK-4 得 `hker`、可测性；全为确定性，不用 R2* 主撇钉文（不等 T2246），不用磨光导数衰减（不等 T2249）。
- **S3-15b** 换新范围：漂移的衰减类 `hDcls`（ℬ₄、ℬ₅ 的衰减），要 T2249（S6-09c）的磨光导数衰减与 `Θ^{(n)}` 衰减传递（监督 0255 O3）；等 T2250、T2249。ST-3 计划 41 不变（S3-15 仍 a/b 两张）；S3-16…18 写票前照此新口径细查（RBM2D 源可能也有不用移植的部分）。
- T2242 把 `NGraph.EndAt`、`IsA1`、`IsA2`、`IsB1`、`NoA2` 登记 structural：照准（组合谓词）。

## §84 LW-14c 拆出 LW-14e；BA-S2b 拆 S2b1/S2b2（总调度，2026-10-06 04:38 UTC，流程事项）
- (1) **LW-14c = T2255**（`Graph/LWExpTerm3`）：5-圈到细图 `𝒢_xy` 的桥、至多一个内分子的图的 `≺` 界、`lwExpG5'_of_expand : LWG5Expand → LWExpG5'`、以 LW-14d 三项与 `LWG5Expand` 为前提的 `LWCutExp`、`LWtermEXP`；新 owed `LWG5Expand`。**LW-14e**（`Graph/LWExpTerm5`：图展开组合，情形 (1)–(4)、`oe2x_graph_E`、阶计数）证 `LWG5Expand`。规则：LW-14d 与 LW-14e 后合并的那张补无条件一行式，删 `LWtermEXP`、`LWCutExp`、`LWExpG5'`、`LWG5Expand` 的登记行。LW 计划 40 → 41。
- (2) **BA-S2b** 估计 1500–2600 行，拆：**S2b1 = T2256**（`BA/Step1Boot`：BA 事件形式 G 钉文 `BAGbEXPii/ij/av`（owed，BA-G6；监督 2252 Q2 要求在第一张 G 相关票里钉）、`BAFlowMember`（owed，BA-S3）、`BABootstrap'`（owed，S2b2）、事件桥接引理）；**S2b2**（证 `baBootstrap'_holds : BAFlowMember → BAGbEXPii → BAGbEXPij → BABootstrap'`，移植 `step1TargetV3_holds` 与 `Step1Setup` 的相应部分）。BA 计划 66 → 67。T2256 预检 P2 判定 `BAGijGEX` 是否须写在 `(G − M)_xy` 上（BA 的 `M` 未必对角）。
- (3) T2249 审核 RETURN 一次（实例窗口塌缩）后 PASS：返工 19/247。

## §85 S3-24b 不等 S3-18b/S3-22（总调度，2026-10-06 04:57 UTC，流程事项）
- S3-24b = T2259 起草发现：`STIterR`（`Step34Pins.lean:486`）与 `STIterR'`（`NQEndFlow.lean:142`）都把自举界作为自己的前提，所以 S3-24b 原定「等 S3-18b、S3-22」不成立（那两张只对 S3-25 要紧）；情形 (ii) 与步的管线已在 S3-24a 合并。S3-24b 照此只证 `iterationsB_step`（`STXiBoot'` 前提、`hlow` 在 `w = s`）与 `stIterations'_holds`、`stIterationsII'_holds`；私有辅助（`IterationsA.lean:876-1046, 1072-1276`）照旧复制（前缀 `iterationsB_`），不另开公开化小票。`STIterR'` 只在两个区域证出、仍 owed（注释写明）；`STIterR`/`STIterR'` 是否改 structural 留最后清理。ST-3 计划 41 不变。

## §86 T2256（BA-S2b1）1a FAIL：ConArg 前提的时间范围（总调度，2026-10-06 05:15 UTC，流程事项）
- 预检：`BABootstrap'` 与 `baBoot_LI_stmt` 的 ConArg 前提对 `u` 要求 `max(s n, 1−c₁) ≤ u n ≤ t n`（对一切 n），只要某个 n 有 `t n < 1 − c₁`（实例 `t ≡ 1/16`）这个集合就空，前提不携带信息。照预检的修法：上界改 `u n ≤ max (t n) (1 − c₁)`，逐 n 用 `u' = max(u, s₁)` 粘合。`docs/tickets/T2256-amend-1.md`、检查文件两行、H92（从 1b 续）。不算钉文级问题（新钉文，未合并），不发 REQ。

## §87 BA-S2b2 拆 a/b；LW-12e 走求和证书路线（总调度，2026-10-06 06:29 UTC，流程事项）
- (1) **BA-S2b2** 拆：**S2b2a = T2262**（`BA/Step1Setup`：复用带状 `S1Std`（能量取占位 `E ≡ 0`，预检 P1 确认）、非标量 `M` 的桥、时间连续与 `BAGt` 时间 Lipschitz、网格提升、`Ω_C ⊆ Ω_{C₀}`）；**S2b2b**（移植 `Step1.lean` §1–§4 加 `baBootstrap'_holds`，删 `BABootstrap'` 登记行）。BA 计划 67 → 68。
- (2) **LW-12e = T2264** 把 (IV) 前半重定义为一个组合定理 `anpKey5_cert`（每条路径去掉一条边后，余下实边有求和证书 `AnpSumCert`）；LW-12f 欠 `AnpKey6SumPin`（沿证书求和）与 `AnpKey6DirectPin := ∀ d, AnpDetGh d`，由此得 `AnpDetGhCaseIV`、`anpDetGhStep_holds` 与登记删除。起草者称论文 (IV) 的鸽巢（`7_8:1388-1393`）对合并的 `NGraph` 不成立（`figIVext`：q = 1 < p = 2、末边在外顶点），重根步 (iii) 在 α₁–α₂ 边为桥时失效（候选）；`AnpKey5GraphPin`/`AnpKey5CertPin` 只有手证，**预检必须先跑脚本反例搜索，找到反例就在 1a 停**。若 f 的直接路线成立，情形 (I)–(III)（已合并的 LW-12c、在跑的 T2260）对 `LWAnpKeyGh` 不再必需：**T2260 不扣**（已在 1a，代价小，且是 f 失败时的后备），到时把不用的钉文归「被取代」。LW 计划 41 不变（e 仍一张）。

## §88 LW-14e 改证主撇 `LWG5Expand'`、拆出 LW-14f；UN-18 拆出 UN-18b（总调度，2026-10-06 06:48 UTC，流程事项）
- (1) **LW-14e = T2265** 起草判合并的 `LWG5Expand`（T2255 起草者自定的建模钉文，`LWExpTerm3.lean:1781`）照写不可证：F1 系数——红自环拆分产生 `m̄ = m^{-1}`，不能写成 E 之前固定列表上的 `m^j`；F2 外分子——分拆项 α=x、β=y 非零且 x、y 在同一分子，`lwGraphPrec1`/`LWScalemole` 不覆盖（T2255 审核观察 1 已提示）。照主撇规则：新文件钉 `LWG5Expand'`（系数 `m^j·m̄^{j'}`，每图外分子互异或 `LWJoined`）并证；`LWG5Expand` 移 `supersededProps`。预检先确认 F1/F2，否证则回原钉文。**LW-14f**（`Graph/LWExpTerm6`，700–1000 行）：连接图的界、`lwExpG5'_of_expand'`、无条件 `lwExpG5'_holds`、`lwCutExp_holds`、`lwTermEXP_holds`，删 `LWtermEXP`、`LWCutExp`、`LWExpG5'` 登记行；§84 (1) 的「后合并者补一行式」规则移给 LW-14f。LW 计划 41 → 42。
- (2) **UN-18 = T2266** 只做 `EMCTE2` 一半（证带状 `UNEMCTE2`、`UNEMCTE2Row`，删两条 owed）；`Apriori` 一半（`UNApriori`，要 UN-04）为 **UN-18b**。UN 计划 56 → 57（上限 60）。T2266a (2)：BA 行 `UNEMCTE2RowBA` 无漂移（`ouMatC` 固定均值），要平移 `Φ ↦ Φ(λΨ + ·)` 与 `UNModel.ba` 的载体转移（约 150–250 行），留 BA 侧。
- (3) 两件都请监督核（REQ）：LW-14e 的主撇是否必要、`LWG5Expand'` 形状；LW-12e = T2264 称论文 (IV) 鸽巢（`7_8:1388-1393`）对合并 `NGraph` 不成立（§87 (2)）。都不扣票（预检先查）。

## §89 监督 0752：LW-14e 主撇与 LW-12e 证书路线都 PASS；门槛 REQ 规程（总调度，2026-10-06 08:12 UTC，照办）
- (1) A：F1、F2 成立；`LWG5Expand'` 形状对；LW-14f 需要（连接图的界是辅助图为空的 GtoAG）；若 T2265 的 1a 发现外顶点合并的 3 阶叶，后备为 `ext 0 = ext 1` 时阈值取 3。B：论文 (IV) 鸽巢与重根 (iii) 有缺口（写作缺口，引理成立）；证书路线可靠（T2264 已合并）；LW-12f = T2270 走直接路线；LW-12c/d（已合并）对 `LWAnpKeyGh` 非必需、作后备（不移被取代：它们的钉文 `AnpDetGhCaseI/III` 由 T2270 一并证出并删登记行）。
- (2) **门槛规程（监督 O2/O4）**：每次放行后对每个 gate 比较计数与 25/40/50，过线的那一轮写 `REQ-…`（第 1 行 `status: open`）。已漏两次（LW 25、UN 25，监督已补查 PASS）。下一门槛：LW 40、ST-3 40、UN 40、ST-4 35（计划）。写进 HEARTBEAT 每轮做法。

## §90 条件证明与 owed 行（总调度，2026-10-06 08:25 UTC，流程事项）
- 一张票以另一条 owed 钉文为前提证出某钉文 X（`P → X`，P 已登记 owed 或本票登记为 owed）时，可以删 X 的 owed 行：未证的内容由 P 的 owed 行承载，owed 总数不减（先例 T2266 的 `UNEMCTE2`）。T2273（UN-21）照此：新登记 `UNOUClaims` owed（`Pins.lean:659`，此前不在任何列表），删 `UNJak` owed 行。前提若不在任何登记表，必须同票登记。

## §91 UN GUE 段按导入重排、拆出 UN-51a；S3-22 拆 a/b/c；T2269c 照准（总调度，2026-10-06 08:54 UTC，流程事项）
- (1) **UN GUE 段**：T2162 拆分表 UN-27…UN-52 的依赖列是顺序不是导入（17:28 UTC 已注意到 UN-27 要 `ZeroModeProfile`）。照 §54 按 RBM2D `import` 行重排：`ZeroModeProfile ← Pins, OU, OUHessian`（都已合并）先做，拆成 **UN-51a = T2276**（UN-51 留 `RandomLayerA/B`）；UN 计划 57 → 58（上限 60）。现在可写：`GUEPhase/Generator`（UN-28，← `Bootstrap`；但 `HierVocab`、`ContractionSecondLoopAllCuts`、`OperationsPairWord` 三个导入在 RBM3D 无对应文件，起草前先找名字）、`GUEPhase/EntryDet`（UN-30，← `AuxCarrier`；`Green/EntryBlock` 无 RBM3D 文件，`Sblk2` 辅助私有复制）。T2276 合并后：`QUEFlow`、`KPrim`（`Kcal` 改名）、`Grid`（UN-27，要 `Main/ZRescale` 的子移植，8 个名字 RBM3D 都没有）；`Markov`、`OneLoop`、`LLTransfer` ← `Grid`；`Proc` ← `Grid, Bootstrap, Generator, KPrim, EntryDet`；`EntryTail` ← `AuxCarrier, EntryDet`。UN-24（`UnivMain`）按导入只要 `Apriori, GreenCorr, EigenMeasurable`，写票前再核行级依赖。**UN-18b = T2275**（`Apriori`，`UNApriori` 由 owed 的 `UNTrLocal` 条件证出，§90）。
- (2) **S3-22 拆 a/b/c**（S3-21 = T2274 起草）：照情形 (i) 已合并链（S3-12a/b/c1/c2 共约 5600 行）比较，S3-21 后剩约 3000 行：**S3-22a**（网格端点 `nzGridEndN`）、**S3-22b**（逐时刻流 + 提升）、**S3-22c**（`newPQ` 组合 + 自举 → `stOeqQtNZ'_holds`，删 owed 行）。预算项挪进 S3-21（同 S3-12a）。ST-3 计划 41 → 43。§83 的情形 (ii) 类比成立且更强：EK-5 无衰减、无和为零前提，不要衰减类、远部分、比权与近/远 QV 拆分。写 S3-18b 时让自举在区域上写成通用形，S3-22c 照用。
- (3) **T2269c**（审核 O1）：T2269 为实例登记 `STKboundgL`、`STLKgL`、`STLocalMaxgL` 为 owed（净 owed +2），照 §90 照准；证明票：BA 链 BA-K4/BA-V2/BA-S3（登记注释已写）。T2269b（`BABootstrap'` 有未用前提）记 D581，留 BA-S3 起草时参考；不另开瘦身主撇。
- (4) T2276 新钉的 d≥3 OU 接口行（`UNOULL`、`UNOUEq747`、`UNG1Row`、`UNG2bRow`；删 `UNOURow`、`UNOUDiag` 的 owed 行）与 `ouTauMax` 的设计值（T2276a/b）、S3-22 三拆，一并请监督核（REQ-2026-10-06-0854）；不扣票（预检先查）。

## §92 BA 可写清单；§91 (1) 更正；监督 0956；S3-17a 线性水平；T2265 形状；LW-13 拆分（总调度，2026-10-06 10:00 UTC，流程事项）
- (1) **BA 盘点**（T2161/T2205/T2173 计划表对合并文件）：现可写 **BA-D3（Ward）**（`BA/Ward` + `BA/OffDiag`：`BAWard`、`BAoffDiag`、`BAPropM` (1)(2)，钉文在 `MFixedPoint.lean:557-591`，T2161-portmap:998、1056；为免与 BA-D3 设计单同名，票里称「P.9 row BA-D3 (Ward)」）、**BA-D6**（`BA/Boundary`：`BAmBoundary`，`:1000`、`:1058`；RBM2D 源 `FreeConvStability` 已移植，或低于估计）、**BA-L1**（`Graph/BAVocab`，`:1044`、`:1102`）。下一层：D4 ← D3；D7 ← D6；G1 ← D4、D7；L2 ← L1（套 D402 的 GGGamma 系数修正）；C2 ← D2、D3、D4、D6、D7；L3 还要 LW-12f（已合并），L4 要 LW-14e/f。计划表过时处：BA-S3 文件名（现 `BA/Step1Fam`）、BA-S1 依赖 G6/K4 已去（§72 (3)）、G6 现欠三条事件形钉文、`BAWard` 等确定性钉文无登记行（第一个用到的票补）。BA-S3 = T2277、UN-30 = T2278 已放行（09:43）。
- (2) **§91 (1) 更正**：`EntryDet` 不需要 `Sblk2` 私有复制：RBM2D `Green/EntryBlock` 已移植为 `RBM3D/Green/EntryDom.lean`（T2057）。`EntryDet` 只带状（类 T）；BA 形属 BA-C3（`BA/GUEEntry`）。
- (3) **监督 0956（REQ-0854）A、B 都 PASS**，照办：**O1** 写 UN-51 或 UN-52 的 QUEFlow 一半之前，先钉模型通用接口 `UNOULLk`、`UNOUEq747k`、`UNG1Rowk`、`UNG2bRowk` → `UNOURowk`（剖面作显式参数或新结构，不加 `UNKind` 字段，§57 (1)；T2276 的钉文作带状实例，照 `UNOUQUEk_band`）：新票 **UN-51g**（UN 计划 58 → 59）；否则 BA 要 P 类孪生 +2。**O2** UN-51 预检列 RandomLayerA 在 d≥3 的 `τ_U` 约束表；需更小值则 `ouTauMax'` + `UNG1Row'`；`UNG2bRow` 不用 `τ_U ≤ ouTauMax` 证。**O3** UN-47/50/51 的产出钉文取 `η_Q` 处 `qdBoundExp` 形（带 `Θ̃`）与 `η_LL` 处矩形，不抄 d=2 的 `Meta⁻³` 形。**O4** S3-22a 取 `D'' ≥ 2(k+2)/𝔠` 加余量（不是 `2k+4d+10`）。**O5** S3-22b 预定后备切法：逐时刻端点 / 一致提升（同 c1/c2），用到则 ST-3 43 → 44。**O6** `UNOUClaims` 登记注释改由 T2280 顺带。**O7** UN 计划 52 → 59，外推约 63 > 上限 60（Jun §50）：UN 到 40 的 REQ 写外推；超 60 是问 Jun 的事。**O8** 见 (5)。
- (4) **S3-17a = T2279** 起草发现：合并的 S3-16b 漂移水平 `dDriftAltQN`/`alt_hdriftQN` 对 `Φ` 是二次的（来自 `GoodSetN` 的 (D2)，`STelklkM` 在 (2, k) 处含当前长度），高概率水平要控制 `Ξ̂_{n_}`，预算带 `N^{ε₀}·XLK(n_)²`，正是 §62 (2)/(4) 排除的，照原样闭不了 `STXiBoot'`。T2279 写成通用预算（`budgetAltQN`，同 `budgetNonAltLinN` 形）并钉线性水平 `dDriftAltLinQN`（经 `GoodLinN`，σ 通用）；**S3-17b** 改为线性漂移水平（`dFlowQN_levelLin`、`alt_hdriftLinQN`，约 200 行）+ 8 条假设的最终形式（RBM2D 13 条缩为 8 条），约 900 行；ST-3 计划不变（43）。S3-18a 要从它的好集族取 `n_−1` 长度处的 `hY`。请监督核（REQ）。
- (5) **T2265（LW-14e）形状**（监督 0956 O8）：参考列表 30,609 / 31,159 片叶（票估约 400）；`LocStep.gg` 要 `hwf`，不适用带权图。决定：列表由展开过程本身定义（递归 `def`），目标 2 沿过程归纳、由逐步事实证，不枚举、不 `decide`；实例 (2) 去掉；带权的步事实直接证（私有），不走 `LocStep`；1b 预计超 1500 行则 RETURN 带切法（T2265a/b，LW 43 → 44）。`docs/tickets/T2265-amend-1.md`、H96。
- (6) **LW-13 拆分**（T2281 起草）：设计行估 2511 行（高 3766）；论文短距区直接取自 `lem:LW_moment`（`7_8:1602`）。**LW-13a = T2281**（`Graph/LWMomExp`：远 `(adsuu33)`、近 `(adsuu_exp2)` 的确定性图核心）；顺序改为 LW-13a → LW-02 → **LW-13b**（`LWMomentExp`）→ LW-01（写 LW-02 前核 T2216:40 说它要 LW-13 的那一处）。LW 计划 42 → 43。疑点 S1：`𝐃_{>ℓ}` 用「或」定义（`7_8:1636`），路径不必有长于 `ℓ` 的边，远钉文可能不成立——预检先测，假则停报；S2：`EKTTk` 用 `zdistD`、`LWMomentExp` 用 `zdistInf`，LW-13b 要从 `LWLoopExp` 取 `zdistD` 边界或给 `EKTTk` 加 `zdistInf` 版。请监督核（REQ）。
- (7) **UN-23 = T2280**：合并的 `UNUyw` 在 d≥3 以 `c' = 𝔠𝔡/30` 成立，无主撇；删 `UNUyw`、`UNJakUywRow` 两条 owed；角色降为 prover。
- (8) 本轮 H95：T2265 工作流活着（09:41 仍有动作），未重启。

## §93 UN-51g 与 BA-D3（Ward）放行；S3-21 合并（总调度，2026-10-06 10:15 UTC，流程事项）
- (1) **UN-51g = T2282**（`Universality/OUInterfaceK`）照监督 0956 O1：新结构 `UNOUProfile K`（字段 `pm`、`pp`，`UNKind` 不加字段）、通用钉文 `UNOULLk`、`UNOUEq747k`（`qdBoundExp` 形，O3）、`UNG1Rowk`、`UNG2bRowk`（不要 `τ_U ≤ ouTauMax`，O2）、`UNOUProfRowk`；`ouRowk_of_pins`、`ouDiagk_of_ouLLk`、带状桥。登记：加 `UNOULLk`、`UNG1Rowk`、`UNG2bRowk`、`UNOUProfRowk`，删 `UNOURowk`、`UNOUDiagk`、`UNOULL`、`UNG1Row`、`UNG2bRow`（净 −1，§90）；`UNOURowBA` 留到 BA-C3。设计改动：bulk 条件放进 `∀ᶠ n`（BA 的 bulk 在个别 `n` 可为空，否则 `ouDiagk_of_ouLLk` 假），带状桥用补齐论证而非 `rfl`；`UNOUProfRowk` 用带状行差形 `C lam⁻² W^{-d}`，BA 剖面是否满足由 BA-C3 核。并入 REQ-1000 D 请监督核。UN 计划 58 → 59（§92 (3)），本票计入：UN 34/59。
- (2) **P.9 row BA-D3（Ward）= T2283**（`BA/Ward`）：`BAWard`、`BAoffDiag` 无条件证，`BAPropM` 的 (1)(2) 作新钉 `BAPropM12`（`BAPropM` 本身随 (3) 归 BA-D4 登记）；无登记改动；`ε = κ²/4`（常数只依赖 `κ`，T2161 b.4 说依赖 `Λ` 不确）；未用的钉文前提照留并在报告列出。BA 14/68。
- (3) S3-21 = T2274 合并（95d8b2a）：S3-22a 可写（`D'' ≥ 2(k+2)/𝔠`，O4）。

## §94 T2281（LW-13a）远钉文不成立 → 只做近区；S3-22a、BA-D6 放行；BA-S3 合并（总调度，2026-10-06 10:34 UTC，流程事项）
- (1) **T2281 1a FAIL（远目标）**：`AnpDetFarAt 3 anpKey_oneEdge` 照钉文假——`farD` 只限制内部标号，没有内部顶点的路径（`q = 0`）对 `ℓ > |a₀ − b₀|` 得不到因子 `T(ℓ)`（脚本反例，违背随 `ℓ` 增长）；`q ≥ 1` 且每条路径过内部顶点的情形（S1）未证未否。近区 `AnpDetNear` PASS；步引理照钉文（「新图仍 `IsNested`」）对 `loopG` 假，改正形：自环与不在路径上的边各以 `T(0) ≤ Ψ` 界掉、不变式「去掉 (1) 的 nested、删自环」。决定：**Amend 1** 只做近区（`lwMomExp_near`、实例、改正步 `lwMomExp_near_step'`），远区退回总调度，并入 REQ-1000 B4 请监督定改正钉文（候选：加「每条路径过内部顶点」或在 `farD` 限制外部标号；S1 的长边因子）。远区之后另票（LW-13c，LW 43 → 44，等答复）。S2（`zdistD` 对 `zdistInf`）确认，归 LW-13b。H97。
- (2) **S3-22a = T2284**（`Induction/QtNonzeroEnd`，prover-max，1150/1400/1650，预定切法 T2284a/b）：`D'' := 2(k+2)/𝔠 + 1`（O4，d=3 表在票里）；初值假设取 `Q^{(A)}` 投影后的环（`budgetNZN` 对 `Γ`、`X0` 用同一 `ε₁`），S3-22b 由 `STLK s` 在 `ε₁/2` 推出（约 30 行）。ST-3 36/43。
- (3) **BA-D6 = T2285**（`BA/Boundary`）：无条件证 `BAmBoundary`（各 `d`）；§92 (1) 说可复用 `FreeConvStability` 不对（那里只对小 `t`、谱近半圆；BA 是 `t = 1`），不导入；计划行的「`ρ_N` 连续」「bulk 开集」不在钉文里，归 BA-C2、BA-D7。BA 15/68。
- (4) BA-S3 = T2277 合并（596a83a）：`BAFlowMember`、`BAStep1` 证出（`baStep1_holds` 以 `BAGbEXPii/ij` 为前提，§90）；`FlowFM.EvEq` 登记 structural。

## §95 监督 1102；T2265 扣住、先做设计探针 LW-14e-D；LW-13c（「且」远域）；ST-3 水平规则（总调度，2026-10-06 11:28 UTC，流程事项）
- (1) **T2265（LW-14e）扣住**：1b 在 Amend 1 上限处 RETURN（10:45）：不是大小问题，是**进展**——「每片叶 `ord ≥ tg`」要「`ord < tg` 的结点总有候选顶点」，Amend 1 的不变式推不出（`stuckG` 满足全部不变式、`ord = 3 < 5`、无候选；有界搜索 2/3 个内部顶点各 442/10,655 个卡住图）；论文 `B:97-108` 说 `(Oe2x)` 严格升 `ord`，Lean 只有「不降」（`Lvl1Good`）。监督 1102 C/O7：再放行前先做设计/探针步，按 (B) 证书路线（可计算模型 + 到 `LGraph.partition` 的正确性桥 + 内核检查具体树的进展与 `ord ≥ tg`）、(A) 限时脚本搜不变式、(C) 逐根项叶界的顺序选。决定：**LW-14e-D = T2288**（设计/探针，仅报告，prover-max，下一个空槽优先；探针里对具体树放开 `decide`/`rfl`，永不 `native_decide`）；T2265 在 CONTROL 里注明扣住，等 T2288 的切法再写 Amend 2 或新票。LW-14e 至少再两张。临界路径：`LWtermEXP` → Step 6 全部区域 → ST-6、MA-06。
- (2) **LW-13（监督 1102 B）**：顺序 13a → 02 → 13b → 01 对（LW-02 = `LWMoment` 不要 LW-13；`Axioms.lean:163` 注释日后改「LW-13b」）。远钉文 (a)(b) 都修不好（`figAux` 反例，比值按 `e^{(√10−√6)√(m/ℓ_t)}` 增长）；改用「且」域 `𝐃^∧_{>ℓ}`，由合并的 `anpDetGh_holds` 得，S1 不再相关；近区覆盖两球之并（`2^q` 常数）。**LW-13c = T2289**（`Graph/LWMomExpFar`）；起草加前提 `ownExt`（每条路径只碰自己的 `a_i`、`b_i`，`lwAuxNested_holds` 的输出满足），并证 `LWAuxNestedOwn`；预检 (iii) 若确认 `f^{>ℓ}` 只限制 `a_1` 则 1a 后停。S2：要 `EKTTk` 的 `zdistInf` 版（O6），放进 LW-13b 或单开一票（+0/+1）。T2281 = LW-13a 近区已合并（e7d495b，`zdistD`/交集形）；O5（一般化近区步）来不及，LW-13b 需要时加孪生（加行不加票）。LW 计划 43 → 44；外推 45–48（O11）：LW 到 40 的 REQ 写外推；到 50 未闭合照 TEAM §6 建议 HOLD——在那之前安排 LW-14 的数学复核。
- (3) **ST-3 水平规则（监督 1102 O3，照办）**：每张钉漂移水平或好集水平的 ST-3 票，票头引 §62 (2)/(4)，预检用一行核「没有水平要求控制当前长度的 `Ξ̂`」。T2272 的二次水平 `dFlowQN_levelM`、`alt_hdriftQN` 已合并但无消费者；下一张碰 `QLevelsB` 的票加一行文档串「不可用于 `STXiBoot'`（§62 (2)）」。**S3-18a** 要写出 `n_−1` 长度处 `hY` 的高概率事件（确定性水平 `Ξ̂_{n_−1} ≤ N^ε XLK(n_−1)`，`Prec` → 网格，同 `gridGoodN_holds` 的 (G2)）（O1）。
- (4) **UN（监督 1102 D）**：bulk 放进 `∀ᶠ n` 对；`UNOUProfRowk` 的无损行差形对 BA 依赖两条未核事实（无损 `BAProp8`；由 `ρ_N ≥ κ` 得 `Im m` 下界）——T2282 已合并，记为 **BA-C3 的无损义务**（O9）。**UN-51 设计**（O8）：要钉模型通用的 ML 输入（`UNMLOut` 与 `UNMLOutBA` 为其实例），`g1Rowk` 加「`P` 是 `K` 的方差与 `m` 的 `Θ̃` 剖面」前提；否则 BA 仍要 RandomLayerB 孪生。O10：UN-51 用于 BA 时核 `BAFlow` 的 `∀ n, BAdom` 是否要在更小 `κ''` 处补齐。

## §96 BA-D4、BA-D7 放行；S3-22a 合并（总调度，2026-10-06 11:43 UTC，流程事项）
- (1) **BA-D4 = T2290**（`BA/CombesThomas`）：`BAPropM` 在 d≥3 照钉文成立，无条件；(3) 用加权 ℓ² Combes–Thomas（`BAMB_ct_core`，基于 `RBM.norm_sub_smul_ge_of_isHermitian`），常数 `C = 16d²/κ³`、`c = min(log(1 + κ/(4dΛ)), κ/2)`；不导入 RBM2D 的 CombesThomas（那是小耦合 Neumann 级数）；未用前提 `(2C)⁻¹ ≤ g`、`3 ≤ d` 列报告。`MFixedPoint.lean` 的「Owed: BA-D3/D4/D6/D7」文档串过时，留待清理（不改合并文件，§57 (1)）。
- (2) **BA-D7 = T2291**（`BA/ImmLower`）：`BAImmLower` 照钉文成立，`c = κ⁵/64`，代数路线（两点估计 + 实点 Ward 界）代替计划的 Hölder-1/3 + Poisson 平滑；BA-D7 实际不依赖 BA-D6（只要 D2 与 T2283 的 `BAm_norm_le_one`）。监督 1102 O9 (b)（由 `ρ_N ≥ κ` 得 `Im m` 下界）由 `BAm_im_lower_of_bulk` 覆盖；O9 (a)（无损 `BAProp8`）仍归 BA-C3。角色降为 prover-hard。BA 18/68。
- (3) S3-22a = T2284 合并（9664e13，`nzGridEndN`）：S3-22b 可写（后备切法：逐时刻端点 / 一致提升，监督 0956 O5；初值假设由 `STLK s` 在 `ε₁/2` 推出，§94 (2)）。

## §97 S3-22b 拆 b/b2；UN-41/42 切法；S3-17b、BA-L1、LW-13c 合并（总调度，2026-10-06 12:01 UTC，流程事项）
- (1) **S3-22b = T2292**（`Induction/QtNonzeroFlow`，逐时刻端点 `stOeqNZPT''_holds`，新钉 `STNZConclPT''`、`STOeqNZPT''`）；起草估全部约 1800 行，照监督 0956 O5 的预定后备切法拆出 **S3-22b2**（一致提升，`QtNonzeroFlowLift`：`STNZConcl''`、`STOeqNZ''`、`stOeqNZ''_holds`；票文在 `docs/tickets/T2292.md` 的 "Split" 节，T2292 合并后另编号放行，prover-hard）。ST-3 计划 43 → 44；本票计入：ST-3 38/44。`𝔠d := min 𝔠G 𝔠L`（情形 (ii) 不用 `st_window`，去掉情形 (i) 的 `1/(2d)`）。
- (2) **UN-41 = T2293**（`GUEPhase/EntryTail` `:1-874`），**UN-42**（`EntryTailMain` `:876-1525`，约 680 行）T2293 合并后另编号放行（票文在 `docs/tickets/T2293.md` 的 "T2293b" 节；CONTROL 只放行 T2293 节）。类 T，只带状，不要 ML 输入；RBM2D 的 `Kstab2`/log 渐近在 d≥3 消失。UN 计划不变；本票计入：UN 35/59。
- (3) 合并：S3-17b = T2286（acb4f83，线性漂移水平；S3-18a 可写，带 `n_−1` 处 `hY` 事件，§95 (3)）、BA-L1 = T2287（c230ce5，BA 图词汇；BA-L2 可写，套 D402 GGGamma 修正，`BAlanlw`/`BAlweight`/`BAGGGamma` 由 BA-L2 自加）、LW-13c = T2289（fbec579，「且」远域）。

## §98 S3-18a 拆 a1/a2；BA-L2 拆 a/b/c（BA 到上限 70）；BA-D7 合并（总调度，2026-10-06 12:15 UTC，流程事项）
- (1) **S3-18a1 = T2294**（`Induction/QEndA`）：词汇 `altYSetN`、`altExitTauN`；`n_−1` 长度处的 `hY` 事件 `altYGridN`（监督 1102 O1；`Prec` → 网格，复用 `gridGoodN_holds` 的 (G2)）；组合 C1–C5。全部约 2050 行，拆出 **S3-18a2**（`Induction/QEndGrid`，网格端点 `altGridEndQN`，prover-max，约 1250 行，T2294 合并后另编号）。ST-3 计划 44 → 45；本票计入 39/45。起草发现第三处 ST-3 形状失误：合并的 `assembledRHSAltQN`/`budgetAltQN` 的 `hR` 用非交错的 `stepErrN`，而 𝒬 过程余项 `rGridQN` 只由 `qErrQN` 界（`QGridA.lean:2114`）；T2294 加桥 C1b `assembledRHSAltQN_qErr_le`（约 50 行，右端加 `N^{−D_t}`，S3-18a2 以 `ε₀/2` 吸收），不改钉文。ST-3 过 40 那轮的 REQ 一并报。
- (2) **BA-L2 拆 a/b/c**：全部约 3600 行（计划 2400）；**BA-L2a = T2295**（`Graph/BAExpand`：BA 流 `g₀Ψ + √t V` 的 Stein 层，钉 `BAlanlw` 并证，`lanlw` 作 `BAGraph` 运算，`scalingOrderG` 记阶）；**BA-L2b**（`Graph/BAExpandW`，`BAlweight`）、**BA-L2c**（`Graph/BAExpandGG`，`BAGGGamma` 带 D402 修正）后续。BA 计划 68 → **70 = 上限**（§57）。**此后 BA 再加票即超上限，是要问 Jun 的事**；新的拆分优先在既有票内消化。本票计入 BA 19/70。
- (3) BA-D7 = T2291 合并（30f7ef8，479 行，低于估计）：BA-G1（等 T2290）、BA-C2（等 T2290）可写。

## §99 BA-G1、LW-02 放行（总调度，2026-10-06 12:30 UTC，流程事项）
- (1) **BA-G1 = T2296**（`BA/GreenSchur`）：计划行未给 G1 钉文；定为后续 G 票要的确定性层（11 个目标：流处实轴 bulk 数据、耦合窗、D3/D4 的细格 `M` 事实、预解恒等式 `BAGt_sub_BAMfine`（新 def `BAflowPert`）、Schur 结构）；`(eq_resolventunderpoly)` 的格和一步留给 BA-T2（`(eq:Psi)` 未入库）；`V` 的块外零只几乎处处成立（`Xentry` 无方差因子），两个 Schur 目标以块支撑为前提，证明归 BA-G2。不证钉文、不改登记。预设切法在同一分支内（不加票）；超 1500 行则 RETURN，因 BA 已到上限，要问 Jun。BA 20/70。
- (2) **LW-02 = T2297**（`Graph/LWMoment`）：照钉文证 `LWMoment`，删其 owed 行，`LWMomentExp` 注释改「LW-13b」（监督 1102 §2.1）。疑点 S1：`LWf` 用 `S = svarF`，展开用方差 `t·svarF`，直接走会损 `t^{-p}`；修法为齐次性 + 新不变式（每个展开输出保留至少 `p` 条黑色波浪边，沿 `LocStep` 传）——预检确认无 `LocStep` 规则删掉它，否则 1a 后停，由总调度定主撇 `LWMoment'`。预设切法：超 1500 行则 §1–§2 移 LW-02′（`Graph/LWMomentA`），LW 44 → 45。LW 36/44。

## §100 UN-42 = T2298（总调度，2026-10-06 12:51 UTC，流程事项）
- UN-41 = T2293 合并（e5c3253）后，UN-42 放行为 **T2298**：票文即 `docs/tickets/T2293.md` 的 "Ticket: T2293b" 节（改号，免得中枢工具处理带字母的票号），检查文件照抄 T2293 的（12:04 已编译 exit 0）；合并名与 T2293 票文不同处以合并为准。UN 计划不变；本票计入 UN 36/59。以后拆出的后半票一律另编号放行（S3-22b2、S3-18a2、BA-L2b/c 同此）。

## §101 S3-22b2 = T2299；ST-3 过 40 写 REQ（总调度，2026-10-06 13:06 UTC，流程事项）
- (1) S3-22b = T2292 合并（59a0ab5，`stOeqNZPT''_holds`）后，S3-22b2（一致提升）放行为 **T2299**（票文即 T2292.md 的 "Split" 段，改号，§100；检查文件照抄 T2292 的）。ST-3 40/45。
- (2) **门槛（§89）**：ST-3 宽口径计数到 40，本轮写 `REQ-2026-10-06-1307`：外推、三处形状失误（§62 (2)/§92 (4) 二次水平、§98 (1) 余项界）、剩余链。

## §102 T2295（BA-L2a）只合并 L2a1；L2a2 并入 BA-L2b（总调度，2026-10-06 13:23 UTC，流程事项）
- T2295 的 1b 在票内 1500 行切点停下，交了 BA-L2a1（d57aa36，904 行：词汇、钉文 `BAlanlw`、`baLanlw_holds`、实例 I1–I2，构建通过）。因 BA 已到上限 70（§98 (2)），不另开 L2a2：**Amend 1** 把 T2295 的目标缩为已交部分，审核后合并（H99）；目标 3（`lanlw` 作 `BAGraph` 运算、值恒等式、`scalingOrderG` 断言）与实例 I3–I4 并入 **BA-L2b**（`Graph/BAExpandW`，`BAlweight`），写 L2b 时一并起草，必要时 L2b 内部分节、超限则 RETURN 问 Jun。BA 仍 20/70。

## §103 T2297（LW-02）扣住：缺与 m 无关的展开列表（与 LW-14e 同类）（总调度，2026-10-06 13:38 UTC，流程事项）
- T2297 1a BLOCKED：`lwMoment_val_smul`、`lwMoment_fxy_bridge` PASS，S1（时间尺度）闭合；但 `lwMoment_holds` 缺一个输入——对每个偶数 `p`，一张**与 `m` 无关的有限展开列表**（系数 `mE E ^ j`）及其期望恒等式（即 `LWG5Expand` 那一类钉文）：合并的 `lw_localregular`（`LocalRegular6d.lean:1107`）在 `∃ outs errs` 前固定 `m`，而钉文的 `∃ c` 在 `z` 之前、`m = mE(STflowE z n)` 随 `n` 变。另有路线修正 F2：近对（块距 `≤ (2+n_V)(log W)²`）要用最大界 `|f| ≺ η⁻¹Ψ²`（`7_8:62-66, 95`），不能用尺寸界（`𝓜_x = 𝓜_y` 输出带 `(L^d)^{n_M}`）。
- 这与 LW-14e（T2265，§95 (1)）同根：都要一个按过程定义、系数跟踪、与 `m` 无关的展开列表及「叶的性质」。决定：T2297 扣住；等 **T2288（LW-14e-D 设计探针）** 的结论，再为两者设计共用的展开引擎（可能是一张新的 LW 引擎票，LW 计划 +1，到时写 REQ）。F2 记入 LW-02 改写时的范围。并入 REQ-1307 Q4 请监督看。LW 计数不变（T2297 已计入 36）。

## §104 BA-C2、UN-29 放行；BA-L2a1、UN-42 合并（总调度，2026-10-06 13:56 UTC，流程事项）
- (1) **BA-C2 = T2300**（`BA/MReg`）：无额外前提证 `UNDensBARow'`（模由 D7 的 `BASelf_sub_le`，`κ → κ/2` 窗由子列极限 + D6 的 `BASelf_of_tendsto`；常数只依赖 `κ`），删其 owed 行；计划行说要 D4，实不需要；耦合平移 `|m(z, λe^{t/2}) − m(z, λ)| ≤ Ct` 属 BA-N1（登记与 `UNTrLocalInitBARow'` 文档串已如此），不在本票。BA 21/70（计划内行，不超上限）。
- (2) **UN-29 = T2301**（`GUEPhase/KPrim`）：类 T、只带状（BA 形归 BA-C3），d≥3 只改 `W⁻²→W^{-d}`、`L²→L^d`；KPrim 不读 `UNOUProfile`，而是给带状剖面（桥到 `profPMTilde`/`profPPTilde`）；源 909 行（表记 799）。UN 37/59。
- (3) 合并：BA-L2a1 = T2295（ad9bb6d，Amend 1 目标；中枢注：H99 的仅审核运行误重跑了 1a（中枢脚本缺陷，已修），改写了 prove 报告 (a) 节）、UN-42 = T2298（90ce008，`gueEntryMix`）。

## §105 监督 1356（REQ-1307）：ST-3 剩余计划、S3-18b 预拆、LW 展开引擎、LW 复核、BA 上限（总调度，2026-10-06 13:57 UTC，照办）
- (1) **ST-3**（Q1–Q3 PASS）：外推 46–48（<50）。C1b 桥可靠，`budgetAltQN` 不要主撇（O5；`QBudgetA` 加一行文档串，留下次碰该文件的票）。**自举的区域通用形放进 S3-22c**（不放 S3-18b）：S3-22c 预检写出 `B_u^{1/6} ≤ N^{−c}` 的收缩指数 `c` 及来源，两区域对 `n` 一致（T2292 表有 `log_N B_s` 小 `n` 处到 `−0.004`），即 §62 (1) 核（O2）。**S3-18b 预拆 b1（逐时刻）/b2（提升 + 情形 (i) 实例）**，b1 带 `m = n_` 的粗界注（O3）：ST-3 计划 45 → 46。S3-25/26 的目标是 `STStep3I/II`、`STStep4I/II`；四个证出后参数形 `STStep3R`/`STStep4R` 出 `owedProps`（O4）。**新规（O1）**：每张钉预算或组装右端的 ST-3 票带「前提 ↔ 产出」表（同 T2294 的 G3）：后续票要卸的每个前提，写其合并产出 file:line 或「新」（抓第 (3) 类失误）。
- (2) **LW 展开引擎**（Q4 PASS，范围放宽，O6）：一个与 `m` 无关的 `lw_localregular` 引擎钉文，供 LW-02 与 LW-13b 共用；路线为沿 `Lvl1Reach m` 运输（每个 `LocStep` 在 `m` 处的输出是某个与 `m` 无关输出在 `m` 处的取值；T2288 探针的 `lwSplitLoopsX_spec`、`partitionX` 正是分拆的这一步）；建在 LW-14e-2 载体上，T2265a 对抽象步写归纳。顺序 **LW-14e-2 → 引擎 → LW-02 / LW-13b**；LW-13b 票须写明引擎钉文为其展开输入；`zdistInf` 版 `EKTTk` 并入 LW-13b，LW-02 的剩余（F2：近对用 `STGbEXPav` 的最大界）并入 T2297 改写。没有更便宜的紧性路线。
- (3) **LW 预算**（O7）：算上 T2288 的拆分（+3，portmap 13:37）、引擎（+1）、`EKTTk`（0/+1）、LW-02′（0/+1），LW 外推 48–50（未计返工）；TEAM §6 在 50 未闭合时建议 HOLD。**现在安排 LW 数学复核**（§95 (2)）：由总调度起一个 Fable 5.1 子代理做（只读，报告写 `docs/claude-team/fable/2026-10-06-lw-review.md`），范围：LW-14e 进展缺口与 T2288 路线、LW 引擎、LW-13 远/近、LW-01 收尾的剩余张数与风险。LW 到 40 的 REQ 须重述外推。
- (4) **T2288 拆分**（O8）：证书模块由中枢单独构建；第 4 张票经 `Rel` 证 `k = true` 的转移，否则要第二份证书（写票时照此）。
- (5) **BA 上限**（O9）：BA-L2b 背着 T2295 移来的目标 3（其合并孪生 `(Owx)` 935 行）与 I3–I4，加 `BAlweight`，可能超 1500 行——这将是第一个 BA 上限问题，起草 BA-L2b 定尺寸后，如超则**作为一件事问 Jun**（TEAM §4）。

## §106 S3-18a2 放行；BA-L2b 超上限 → 问 Jun（总调度，2026-10-06 14:13 UTC）
- (1) **S3-18a2 = T2302**（`Induction/QEndGrid`，prover-max，1200/1400/1650，预设切法 T2302a/b，用则 ST-3 46 → 47）：照 T2294 钉文形状证 `altGridEndQN`；T2294d（`yMomentsQUnifN` 要 `∀ n, 0 < sz.lam n`，`STFlow` 只给最终成立）在票内用 `lam ≤ 0` 处的 δ 磨光函数解决（`ellT = 1`），不加钉文前提；投影初值是唯一无合并产出的前提，归 S3-18b1（约 40 行）。ST-3 41/46。
- (2) **BA-L2b 起草（T2303，草稿 `docs/tickets/drafts/T2303-draft.md`）**：尺寸 1630/2050/2750（`BAlweight` 380/500/750 + T2295 移来的目标 3 与 I3–I4 1250/1550/2000；后者的 LW 孪生 935 行，另加原子、`scalingOrderG`、BA 版 `lwStein_term_eq`）；要拆 T2303a/b → BA 71，超上限 70（§98 (2)）；把 3(c) 挪进 BA-L2c 会让 L2c 到约 2000 行，挪进 BA-L3 不行（其孪生 4462 行）。另：`lem_lweight` 的图运算现在不在任何票里，BA-L3 要它，可能再 +1（BA 72）。**这是第一个 BA 上限问题，问 Jun（一件事）**；答前 T2303 不放（CONTROL「Pending approval」注明），BA 其他计划内票照常。
- (3) S3-22b2 = T2299 合并（2cf288c）：S3-22c 可写（区域通用自举，§105 (1) O2）。

## §107 LW-14e 按 T2288 拆四张；T2265 撤回；BA-C2、UN-29 合并（总调度，2026-10-06 14:40 UTC，流程事项）
- (1) **T2288（LW-14e-D）合并**（4686e08，仅报告；探针留 t/T2288 5f3d37f）：选路线 (B) 内核证书（R-all：每个低于目标结点的每个候选都检查，不固定选择规则；B-full 叶性质），载体为真 `PGraph (Fin 2)` + `LGraph.partition`（追指数的副本），过程对 `sel` 与燃料通用；在 `(Oe2x)` 新建顶点处展开也可（证书覆盖全部候选）；`R1` 在恒等式层由 `oe2xR1_val` 去掉；钉文 `LWG5Expand'` 不变。拆四张：**LW-14e-1 Cert = T2306**（模型 + 证书，三模块，prover，**中枢单独逐个构建**，最重块 7.1 GB）、**LW-14e-2 恒等式 = T2307**（过程 + `lwExpandIdentity_holds`；另钉抽象 `expandG`/`ExpandGSum` 供 LW 引擎）、LW-14e-3 Sim（等 1、2，prover-max）、LW-14e-4 Sound（等 3，prover-max：`lwG5Expand'_holds`、`LWG5Expand` 移 superseded；经 `Rel` 证 `k = true` 的转移，否则要第二份证书）。1 ∥ 2 → 3 → 4 → LW-14f。
- (2) **T2265 撤回**（被 T2306–T2309 取代；状态记为 superseded，分支不合并）。LW 计划 44 → 47（T2288 portmap §6）；T2306、T2307 计入：LW 38/47。外推 48–50（监督 1356 O7）；LW 数学复核待安排。
- (3) 论文差异（T2288a–e）：`(eq:GGraisesord)`（`B:98-100`）在深度 ≥ 1 的带点再分拆后不成立（36/40 个子结点阶不升）；情形 (4) 的「两次展开共升 ≥ 2」树深 3、叶界余量 0；进展对展开顶点的任何选法都成立（树内），树外有卡住图；`GtoAG` 要的分子事实在每片叶上由枚举成立；Lean 以有限内核证书证叶界，论文说「检查可见」。
- (4) 合并：BA-C2 = T2300（3deaafe，`UNDensBARow'` 证出，owed 147 → 146）、UN-29 = T2301（241ebfd，`KPrim`）。

## §108 T2306 构建规则放宽；BA-P1 放行；LW 数学复核（Fable）结论（总调度，2026-10-06 14:59 UTC，流程事项）
- (1) **T2306（LW-14e-1 Cert）**：中枢问「单独构建」是否要停其他槽。决定（H101）：三个证书模块永远逐个构建；其他工作流照跑；证书模块构建期间不开新工作流、不跑别的全量构建；空闲内存 < 12 GB 时等；被杀或严重换页则在无其他构建时重试。避免空槽一小时以上。
- (2) **BA-P1 = T2308**（`BA/Prop5Short`）：无额外前提证 owed 的 `BAProp5s`（`FlowPins.lean:182`），加权 ℓ^∞ Combes–Thomas 路线代替论文的截断 Taylor（`M'` 稠密，合并的卷积界每用一次衰减率减半；候选 T2308a：`A:41` 的卷积界要损衰减率）；删其 owed 行。BA 22/70（计划内）。
- (3) **LW 数学复核**（Fable 5.1，`docs/claude-team/fable/2026-10-06-lw-review.md`）：剩余已命名 7 行（14e-3、14e-4、14f、引擎、13b、01、LW-16），不拆则 45；现实 48–50，尾部 51–53；超支在 **LW-13b**。风险：(a) **LW-13b 隐藏缺口**——`f = f^{>ℓ} + f^{≤ℓ}` 限制的是内部顶点 `β` 的块（`7_8:1607-1611`），而 `LGraph.val` 与 `lw_localregular` 对内部标号全求和，无合并机制把域带过展开（`T2289-prove.md:264`）；选项 (i) 带域的孪生恒等式、(ii) 不限制展开再在 `NGraph` 层按叶拆近/远（出现混合模式，要新钉）、(iii) 让 `β` 外部化；写 LW-13b 前须定（REQ）。`zdistInf` 版 `EKTTk` 要重证（换范数损 `e^{Θ((log W)^5)}`），300–600 行，并入 13b 的拆分。(b) 引擎自然性对三条 `LocStep` 规则都可信（`m` 只作系数、无系数为零的分支）；但 X 载体要逐构造子追 `(j, j')`、共轭交换，且递归要照 `lvl1_exists_aux` 的良基/截断形（不是 T2307 的燃料 `expandG`）；900–1700 行。(c) LW-14e-4 的 `k = true` 靠 `Rel` 不看波浪边颜色；若 L6/L7 某性质读颜色要第二份证书。(d) LW-02 F2 的输入 `STGbEXPav` 已合并且形对；用 `Ψ' := max(Φ n 0)(W^{-d/2})`，不要用 `LWInit` 的 `Ψ`。建议：照 14e-2 → 引擎 → LW-02 ∥ 14e-3 → 14e-4 → 14f 推进，13b 待域机制定；不并引擎入 14e-4，不并 13b 入 02。写票前先钉：引擎 X 载体/递归形、LW-02 的 `Ψ'` 路线；**REQ 给监督问 LW-13b 的域机制**（REQ-1459）；14e-4 列 L6/L7 性质核颜色；LW-16 核 `tailW` 类的 `LWPsiRel` 是否确定性。若 13b 定为 ≥ 2 行，LW 到 40 的 REQ 把外推改为 49–51，HOLD 复核那时就排。

## §109 UN-24 放行（总调度，2026-10-06 15:26 UTC，流程事项）
- **UN-24 = T2309**（`Universality/UnivMain`）：`UNUnivMainRow`、`UNClaimRow` 在 d≥3 照钉文成立（`un_core_of_rows'` 用的是不带撇的 `UNUnivMainRow`；该行只要 `c/π ≤ ρ_n ≤ C/π`，§65 的 `UNDens` 弱点无碍）；另证模型通用 `UNClaimRowk`（同算术 + `ouMatC` 可测），带状由 `UNClaimRowk_band` 得；附 `unCore'_holds : UNCore'`（一行，自合并的 `un_core'_of_univMainRow`）。删 owed：`UNUnivMainRow`、`UNClaimRow`、`UNClaimRowk`；`UNClaimRowBA` 留 BA 侧一行跟进。起草者称合并后 `UNCore'` 不再依赖任何开放行——合并时核实，若属实记入 ROUTES（UN 核心闭合）。UN 39/59。

## §110 UN 过 40 → REQ-0623；T2308+T2309 合并簿记（总调度，2026-10-07 06:23 UTC，流程事项）
- (1) **T2308（BA-P1）合并**（1d19466，06:02 UTC Oct 7）：`BA/Prop5Short`，`baProp5s_holds`，owed 146 → 145。BA 23/70（计划内）。
- (2) **T2309（UN-24）合并**（3eca2db，06:17 UTC Oct 7）：`Universality/UnivMain`，删 owed `UNUnivMainRow`/`UNClaimRow`/`UNClaimRowk`，owed 145 → 142。UN 40/59。中枢核实：合并后 `UNCore'` 不再依赖任何开放行（§109 条件满足）——已记。
- (3) **UN 过 40 → REQ-2026-10-07-0623 已写**（`docs/supervisor/requests/REQ-2026-10-07-0623.md`）：外推约 63 > 上限 60（0956 O7）；Q1 问外推是否合理、Q2 问是否需提上限及提到多少、Q3 问可否合并减张；BA 上限问题已挂 Jun，UN 先过监督。监督 trig_01LMeV5aP8ieHGcixDbpLYEx 下次 06:41 UTC 读取。
- (4) **当前状态**：只跑 T2306（LW-14e-1 Cert，prover-max）；三槽空闲；下一批准备：S3-18b1、LW 引擎票、LW-14e-3 Sim、BA-P2、BA-L2c（依 Jun 答复）。

## §111 T2310 写就（总调度，2026-10-07 07:05 UTC，流程事项）
- **T2310（S3-18b1 / QEndB1）已写**：`docs/tickets/T2310.md`；新文件 `Induction/QEndB1.lean`；新 pin `STXiBootPT'`（`STXiBoot'` 的逐时刻版，`Prec` → `PrecPT`）+ `STOeqQtPT'`（= `STIngR d STCaseI STXiBootPT'`）；公开定理 `stOeqQtPT'_holds : ∀ d, STOeqQtPT' d`。
- **证明结构**：`altQFlow_initQ`（~40 行，新；STLK s at ε₁/2 + startLevelQN at u=s,X=1）→ `altQFlow_core`（private；调 `altGridEndQN`，放 G3 表 9 行，O3 注：m=n_ crude bound 用 `STXiLKM_crudeN`，非 pair 假设）→ `altQFlow_section`（private；collapsed window）→ `stOeqQtPT'_holds`（perTimeDomAt_iff_forall_section）。
- **计数**：ST-3 45/46；欠账 142（无变化，T2310 合并后 +1 owed STOeqQtPT'，-0 released）；下一票 T2311。

## §112 T2306 审计 PASS（总调度，2026-10-07 06:39 UTC，流程事项）
- **T2306（LW-14e-1 / LW Cert）审计 PASS**（claude-opus-5-5 round 1，533adf0；`cert_all`、`cert_FF`、`cert_FT`、`goodB_succ_of`、`inner_node_one`、`root_F?_shape`、`lwCert_root0_nonleaf`、`lwCert_roots_below` 全部 PASS）。构建时间 8.4s/3.73GB + 563.9s/6.99GB + 621.2s/7.01GB，均在 ≤30min ≤8GB 限内；公理：仅 [propext, Classical.choice, Quot.sound]；`git diff --name-only main...t/T2306` 仅 3 新文件；D612（T2288e）已覆盖论文差异。state=audit-pass，hub 正在合并（rule (A) + H101）。
- **合并后**：LW 40/47（现实 48–50）→ **写 LW-40 REQ**（下一步，等 merge commit 确认后写；外推 48–50，~8–10 张尾部；LW-13b 仍待域机制，REQ-1459 已开放）。同时解锁：LW-14e-3 Sim 票可写（T2306+T2307 均已合并 ✓）。
- **当前 main**：3eca2db；T2306 merge 后将移动；LW 39→40（合并确认后更新计数）。

## §113 T2306 合并 + LW 过 40 → REQ-0650（总调度，2026-10-07 06:50 UTC，流程事项）
- **T2306（LW-14e-1 Cert）合并**（8096694，06:49 UTC Oct 7）：`Graph/LWExpCert`/`LWExpCertS0`/`LWExpCertS1`，`cert_all`（有限核证书，`decide +kernel`）；full lake build 4120 jobs PASS。LW **40/47**（现实 48–50）。
- **LW 过 40 → REQ-2026-10-07-0650 已写**（`docs/supervisor/requests/REQ-2026-10-07-0650.md`）：Q1 外推合理性，Q2 LW-13b 域机制（REQ-1459 已开放，优先决定），Q3 合并/删减；监督下次 :41 UTC 读取。
- **T2306+T2307 均已合并** → LW-14e-3 Sim（T2311 候选）解锁；LW 引擎票亦解锁（T2307 合并 ✓）。
- **当前开放 REQ**：REQ-1459（LW-13b 域机制）、REQ-0623（UN 上限）、REQ-0650（LW 上限/13b）。仍扣住：T2297（LW-02，等引擎）、T2303（BA-L2b，等 Jun）。

## §114 — T2311 写出（2026-10-07 07:14 UTC）

**决策**：T2306（LW-14e-1 Cert，8096694）+ T2307（LW-14e-2，3c11598）均已合并，解锁 LW-14e-3 Sim → 写 T2311。

**内容**：T2311（LW-14e-3 Sim）= `RBM3D/Graph/LWExpSim.lean`；模型桥接票。证明：
- `PartitionSim`（Bridge 1）：模型分拆 `cPartitionX` ↔ 真实分拆 `partitionX` via `List.Forall₂ (Rel …)`。
- `ChildrenSim`（Bridge 2）：模型子节点 `childrenX` ↔ 真实子节点 `RCand.kids` via `List.Forall₂ (Rel …)`。
模拟关系 `Rel`：顶点类型的等价 `eE : Fin (N.a+1) ≃ P.E'`、`eI : Fin N.b ≃ P.I'`。
证明层次：L1 `labsOf_spec`、L2 `cMerge_rel`（等价类 `Equiv.ofBijective`）、L3 `partitionSim`、L4 分拆在 `relabel` 下的自然性、L5 八个 family 在 `relabel`/`renum` 下的对应 → `childrenSim`。
角色：prover-max，估计 650/800/1100 行，上限 1500（超则 RETURN 提出 3a/3b 拆分）。
pin 定义逐字来自 `t/T2288:RBM3D/Probe/T2288Cert.lean`（probe 457-610，已经审计）。
票号 T2311，检查文件 `docs/tickets/checks/T2311-check.lean`，门槛 LW → 41/47（合并后）。

## §115 — 数学监督重建（2026-10-07 07:40 UTC）

Jun 的旧监督账号不可用（trig_01LMeV5aP8ieHGcixDbpLYEx 自 Oct 6 13:56 UTC 停报）。
新监督在 misslose 账号建立：

- 触发器：trig_01R1NVdwWjDU2P5KMhtTLr43
- 名称：RBM3D 数学监督（每小时看请求队列）
- Cron：`41 * * * *`
- 设备：mac-lan（a8df38d8-bcfe-42ee-8376-b92f5dad7fe5），连接 /Users/junyin/Lean_proof/RBM3D
- 权限：auto（自动批准），push 通知开
- 首次运行：2026-10-07T07:41:00Z，预期处理 REQ-1459、REQ-0623、REQ-0650
- 提示词来源：STARTUP.md §3（原样）

## §116 — T2310、T2311 放行，H103 写就（2026-10-07 07:42 UTC）

Hub 报告无票可做（所有已放行票均已合并）。总调度：

- 写 `docs/tickets/checks/T2310-check.lean`（逐字照 T2310 §7）
- CONTROL.md 放行 T2310（278）和 T2311（279），加入 Pre-release checks
- CONTROL.md 写 H103（commit 指令：自 H94 b2529ba 起的调度文件，§92–§115，提交 + push）
- 数学监督 trig_01R1NVdwWjDU2P5KMhtTLr43 将在 07:41 UTC 处理三个 open REQ（REQ-1459、REQ-0623、REQ-0650）

## §117 — T2310-check / T2311-check 重写（2026-10-07 08:xx UTC）

H103 执行后 Hub 报告两个 check 文件均编译失败：

- **T2310-check.lean**：exit 1，"object file '.../QEndB1.olean' does not exist"。
  原因：check 文件直接 import 了待创建的新模块 `RBM3D.Induction.QEndB1`（照抄 T2310 §7 格式，格式不符合
  预发布 check 规范）。修复：去掉新模块 import，改为 import 真实依赖（QEndGrid、QEndA、NQEndFlow、
  QLevelsA、NQLin、GridGoodN、NQBudget、KLFinal），Section 1 `#check` 已合并符号，Section 2 在临时
  namespace `RBM.Gauss.Sizes.T2310Check` 内定义 `STXiBootPT'`、`STOeqQtPT'`，Section 3 声明 pin Prop。

- **T2311-check.lean**：exit 1，17 个 unknown identifier 错误（`MNode`、`cMerge` 等）。
  Hub 注记："the merged cert names are in namespace `RBM.Graph.LWCert` (`RBM3D/Graph/LWExpCert.lean:35`);
  the check opens only `RBM.Gauss.Sizes`"。修复：去掉 `open RBM.Gauss.Sizes` 对 cert 符号的依赖，
  Section 1 改用 `#check @RBM.Graph.LWCert.MNode` 等全限定名；Section 2 从 `#check` 不存在符号改为
  在临时 namespace `RBM.Graph.T2311Check` 内定义新符号（逐字照探针文本），`Cand.toR` 因需 proof term
  `cands_spec` 而以 `axiom` 声明（仅用于类型检查，此文件永不被 import）。

正确格式参照：`docs/tickets/checks/T2308-check.lean`（§92）。写 H104（commit 两个修复后的 check 文件）。

## §118 — T2310-check / T2311-check 第二轮修复（2026-10-07 08:38 UTC）

H104 执行后 Hub 编译两个 check 文件，再次失败：

- **T2310-check.lean**（exit 1）：`RBM.Gauss.Sizes.perTimeDomAt_iff_forall_section` 不存在。
  Hub 注：the merged lemma is `RBM.Path.perTimeDomAt_iff_forall_section`，定义在
  `RBM3D/Defs/StochDomAt.lean:213`（namespace `RBM.Path`，开于 line 183）。
  修复：将 `#check` 行改为 `@RBM.Path.perTimeDomAt_iff_forall_section`；import 不变（NQEndFlow 已
  间接引入 StochDomAt）。

- **T2311-check.lean**（exit 1）：`RBM.Graph.LWCert.MNode.toP` 不存在（line 79 & 111）。
  原因：在 namespace `RBM.Graph.T2311Check` 内写 `def MNode.toP`，全限定名为
  `RBM.Graph.T2311Check.MNode.toP`；但使用处 `N.toP h`（dot 语法）令 Lean 查找
  `RBM.Graph.LWCert.MNode.toP`（`N : MNode` 的类型命名空间），后者不存在。
  修复：将两处 `N.toP h` 替换为显式调用 `MNode.toP N h`（Lean 在当前 namespace 下先找
  `RBM.Graph.T2311Check.MNode.toP`，正确解析）。

写 H105（commit 两个第二轮修复后的 check 文件 + DECISIONS §118）。

## §119 — 数学监督 2026-10-07-0838 判决：PASS，O1–O5（总调度，2026-10-07 09:10 UTC）

监督报告：`docs/supervisor/2026-10-07-0838.md`（07:41 UTC 触发，处理三个 open REQ）。

**处理结果（open REQ 归零）：**
- REQ-1459（LW-13b 域机制）→ 接受；方向：`lwMomExp_valOnD` identity twin 作 LW-13b-1 pin。
- REQ-0623（UN 上限）→ 搁置；等 Jun 决定（见 O4）。
- REQ-0650（LW 上限/13b）→ 接受；LW 上限 ≤ 50，13b 设计在 LW=41 后继续。

**标志 O1–O5：**
- O1：LW-13b 域机制确定（`lwMomExp_valOnD` identity twin）→ 在 LW=41 后起草 LW-13b-1 之前先设计 pin。
- O2：LW-14e-4 waved colour 检查 → 在 LW-14e-4 票草稿前阅读对应纸张节（waved colour 部分）。
- O3：`(eq:Psi)` tailW 覆盖确认 → 在放行 LW-16 之前确认 `(eq:Psi)` 涵盖 tailW 情形。
- O4：**UN 上限询问（Jun 单问）**：UN 当前 40/59，预计 ~63，上限 60；是否提升至 65？（TEAM §4：每次只问一件；已在本节写就后提出）
- O5：下一个 REQ 在 LW=43。

## §120 — T2310 pin 重设计：`STXiBootPT'` → `STXiRoundPT'`（总调度，2026-10-07 09:10 UTC）

**背景：** T2310（S3-18b1）于 08:50 UTC 预检失败（状态 `preflight-fail`，报告 `docs/reports/T2310-prove.md`）。
原 pin `STXiBootPT'`（最终拼接形状）逐行验证失败：

| 行 | 失败原因 |
|---|---|
| 行 2 | `2 ≤ n_` 不足：`m = n_ − 2 ≥ 1` 要求 `n_ ≥ 3` |
| 行 7 | 缺少 `m = n_` 假设（当前长度控制） |
| 行 8–10 | 最终拼接形状；各轮由 `stXiBootR_of_round` 完成，需使用轮形状 |
| 行 9 | 非交替 σ 无来源（旧 `m+1≤n_` 不含 `m=n_`） |
| 行 5 | ν = N^{ε₁/2} 分解失败；正确：ν = N^{ε₁/8} |
| 行 6 | hF 来源 `STKbound` 错误；应为 `stDecayLoopU_of_step2`（DecayLoopB.lean:1637） |

**新 pin `STXiRoundPT'`（对齐 `STXiRound'` at QtNonzeroBoot.lean:92–106）：**
```lean
def STXiRoundPT' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 3 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →                        -- KEY: m ≤ n_ covers m = n_
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2)
          (sz.Bctl n (s n)) n_ p)
```

**论文 delta T2310a：** §3.5 per-time 轮引理直接给出 `PrecPT` 结论；从轮到 boot 的提升在 S3-18b2 完成
（对应 §3.5:1676–1714 alternating case 最后组合）。

**文件更新（本节写就时同步）：** `docs/tickets/T2310.md`、`docs/tickets/checks/T2310-check.lean`；
H106（CONTROL.md）commit 本节 + 重启 T2310 证明器。

## §121 — T2311 合并：LW-14e-3 Sim `Graph/LWExpSim`（总调度，2026-10-07 09:44 UTC）

**Ticket:** T2311 (LW-14e-3 Sim, `Graph/LWExpSim`)  
**合并哈希：** 7e7b3be  
**Gate：** LW 40 → 41/47  
**审计：** PASS（claude-opus-5-5，round 1）；full lake build 4121 jobs；无 registry 变更  
**交付物：** `partitionSim : PartitionSim`、`childrenSim : ChildrenSim`、`rel_self`；1211 行，67 个 private 辅助定理，std 3 公理；kernel-checked 实例（163 partition terms，550 children）  
**合并方式：** Hub rule (A) 自动合并（审计 PASS 后无需总调度 H 指令）

**下游：**
- S3-18b2 设计待开展：使用 `stXiBootR_of_round`（QtNonzeroBoot.lean:581）将 `STXiRoundPT'` 提升为 `STXiBoot'`/`STOeqQt'`；在 T2310 合并后启动；合并后 ST-3 关闭于 46/46
- LW-13b 设计：`lwMomExp_valOnD` identity twin（监督 O1）；在 LW=41 后、草稿 LW-13b-1 之前设计 pin（当前 LW=41/47，满足条件）

## §122 — T2310 预检 PASS + §2a τN 修正（总调度，2026-10-07 09:44 UTC）

**工作流：** wf_3f89a0e7-de8，stage 1a 预检报告 09:28:54 UTC  
**Pin：** `STXiRoundPT'` — **PASS**（逐行 verdict：行 1–11 全部 closes）  
**Stage 1b：** 工作流继续运行中（预检 PASS 后自动推进）

**行 8 修正（原 ticket §2a 错误）：**  
`startLevelQN` 的 `hMΛ` 条件要求 `c₀ν² ≤ N^{τN}`；原 ticket §2a 取 `τN = ε₁/8`，则需 `c₀ N^{ε₁/4} ≤ N^{ε₁/8}`，对一切 N 均失败（c₀ 约 3×10¹⁰）。  
**修正：`τN = ε₁/2`**；则 `c₀ N^{ε₁/4} ≤ N^{ε₁/2}` iff log₁₀N ≥ 67074，eventual。  
综合输出：`N^{ε₁/8} + N^{ε₁/2} ≤ N^{ε₁}`（log₁₀N ≥ 963.3，eventual）✓  
ticket §2a steps 2–3 已更新（本节写就时同步）。

**Stage 1b 必要事项（来自预检）：**
1. 行 2：非交替 σ 半部分需 `nqFlow_core`（NQEndFlow.lean:642，private）的副本，含 pair-constant 控制（行 3）与 union bound（2^{n_} N^{n_} at D+n_+1）（行 10）
2. 行 8：τN = ε₁/2（非 ε₁/8）；联合界为和 N^{ε₁/8} + N^{ε₁/2} ≤ N^{ε₁}
3. 行 5：常数因子 2 被 N^{τ/2} 吸收（eventual）
4. 行 9：hF 由 `stDecayLoopU_of_step2`（DecayLoopB.lean:1637）提供，D_F = (2m+6)/𝔠

**论文 delta T2310a（新增候选，已在 §120 中预告）：** `STXiRoundPT'` 对应论文 §3.5:1687 `(eq:alternatecase1)`；参数上确界被常数 `XLK m n u` 与 `B_v^{1/6} ≤ B_u^{1/6}` 替换；pin 在 `STPair` 上用 `Prec` 陈述（pair (v,u)，参数取 u 处）。

**文件更新（本节写就时同步）：** `docs/tickets/T2310.md` §2a；H107（CONTROL.md）commit 本节。

## §123 — LW-13b-1 pin 设计：`lwMomExp_valOnD_eq_valOn` identity twin（总调度，2026-10-07 10:07 UTC）
**监督 O1 满足：** LW=41（T2311 合并，DECISIONS §121）  
**域机制（REQ-1459，Fable §108 选项 (i)）：** `anpKey6_w`（AnpKey6.lean:664，`namespace RBM.Graph`）与 `NGraph.valOn` 的每条边因子完全一致——均为 `if ghost then 1 else ξ(Sum.elim (Sum.elim a b) ℓ e.u)(Sum.elim (Sum.elim a b) ℓ e.v)`。  
`lwMomExp_valOnD Γ ξ a b D`（LWMomExp.lean:526）= `Σ_{ℓ ∈ piFinset D} Π_k anpKey6_w ℓ k` = `Γ.valOn ξ a b (piFinset D)`（AnpKey2.lean:54），与 `anpKey6_val_eq`（AnpKey6.lean:669）同一 unfold + `List.prod_ofFn` + `rfl` 证明，仅域从 `Fintype.univ` 收缩为 `piFinset D`。  

**Pin（T2312, LW-13b-1，文件 `RBM3D/Graph/LWMomExpD.lean`）：**
```lean
theorem lwMomExp_valOnD_eq_valOn {p q : ℕ} {ι : Type*}
    (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (D : Finset ι) :
    lwMomExp_valOnD Γ ξ a b D =
      Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D)) := by
  unfold lwMomExp_valOnD NGraph.valOn
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl
```
**作用：** 桥接 `AnpDetNearAt`（近区用 `lwMomExp_valOnD`，LWMomExp.lean:900）与 `AnpFarAndAt`（远区用 `Γ.valOn`，LWMomExpFar.lean:80），使两者在域分解中统一为 `NGraph.valOn`。  
**依赖：** T2281（`RBM3D.Graph.LWMomExp`），T2289（`RBM3D.Graph.LWMomExpFar`）均已合并；无需 T2297（LW-02）。  
**大小：** ≈15 行（namespace `RBM.Graph`；开放 Hub 放行）。  
**下游（LW-13b-2，待后续设计）：** 组装 `∀ d, LWMomentExp d`（LWPins.lean:341，`RBM.Gauss.Sizes`）；依赖 T2312 + T2297（HELD）+ T2281（`lwMomExp_near`）+ T2289（`lwMomExpFar_and`）。

## §124 — Jun 批准 UN 上限 → 65（总调度，2026-10-07 10:10 UTC）
**Jun 回复：** "UN OK"  
**决定：** UN 上限从 60 提升至 **65**（当前 UN=40/59，预计约 63，新上限内）。  
**依据询问：** DECISIONS §119 O4（UN 当前 40/59，预计 ~63，上限 60，是否提升至 65？）  
**REQ-0623 Q2 已答：** 提升至 65，批准。Q1（外推是否合理）与 Q3（可否合并减张）由监督另行判决。  
**Gate 更新：** UN 40/65（原 40/59 上限 60 → 新上限 65）。  
**TEAM §4 单问解除：** 下一个 Jun 问题已发出（见下）。  
**下一个 Jun 问题（BA 上限）：** BA-L2b (T2303) 拆 a/b = BA 71；加 `lem_lweight` 图运算单独票 = BA 72，超上限 70（§57）。是否提升 BA 上限至 72？（答前 T2303 不放行）

## §125 — T2310 合并（S3-18b1，`stOeqQtRoundPT'_holds`）（总调度，2026-10-07 10:28 UTC）
**合并提交：** 319bf17（`Induction/QEndB1`，`stOeqQtRoundPT'_holds : ∀ d, STOeqQtRoundPT' d`；lake 全量编译 4122 任务 PASS）  
**审计：** PASS 第 1 轮（claude-opus-5-5；pin `STXiRoundPT'`、`STOeqQtRoundPT'` 与 check 文件完全一致）  
**监督报告 2026-10-07-1008.md：** 无新操作项；UN cap 65 已在 §124 记录，本次仅确认。  
**Gate 更新：** ST-3 42 → **43/46**  
**下游：** S3-18b2 设计开放（目标：`stXiBootR_of_round` 提升 `STXiRoundPT'` → `STXiBoot'`/`STOeqQt'`）。  
**H109：** commit 本节 + ROUTES 更新。

## §126 — T2312 合并：LW-13b-1 `lwMomExp_valOnD_eq_valOn`（总调度，2026-10-07 11:13 UTC）
**合并提交：** d71c955（`Graph/LWMomExpD.lean`，`lwMomExp_valOnD_eq_valOn`；full lake build 4123 tasks PASS）  
**审计：** PASS 第 1 轮（claude-opus-5-5，t/T2312 at de44f57；pin 完全一致；`unfold lwMomExp_valOnD NGraph.valOn`，≈7 行）  
**Gate 更新：** LW 41 → **42**/47  
**下游：** LW-13b-2（组装 `∀ d, LWMomentExp d`，LWPins.lean:341）待 T2297（LW-02，HELD，等引擎）+ T2281（`lwMomExp_near`）+ T2289（`lwMomExpFar_and`），后两者已合并  
**ROUTES 补记（§108 以来四次 LW 合并均未写 ROUTES）：**  
- T2307（LW-14e-2，3c11598，05:32 UTC Oct 7）：LW 38→39  
- T2306（LW-14e-1 Cert，8096694，06:49 UTC Oct 7）：LW 39→40（过 40 → REQ-0650）  
- T2311（LW-14e-3 Sim，7e7b3be，09:43 UTC Oct 7）：LW 40→41（过 41 → 监督 O1 满足）  
- T2312（LW-13b-1，d71c955，10:57 UTC Oct 7）：LW 41→42（本节）  
**H113：** commit 本节 + ROUTES LW 更新（38→42，四条合并记录）。

## §127 — S3-18b2 设计：PrecPT→Prec 提升 + n_=2 缺口；拆为 T2313（S3-18b2a）+ T2314（S3-18b2b）（总调度，2026-10-07 14:37 UTC）

**来源：** Fable 5.1 子代理调查（aee8f35731ec80f34，71 工具调用，292157 token；14:12–14:27 UTC）

### STXiRound' vs STXiRoundPT' 差异

两者**仅两处不同**：（a）阈值 `2 ≤ n_` vs `3 ≤ n_`；（b）结论中 `Prec` vs `PrecPT`（index set 均为 `STPair s t`）。假设（四条 `Prec` 前提）、控制参数和 RHS（`B_u^{1/6} XLK n_ + STbootRHS 1`）完全相同。

签名（`variable (sz : Sizes d)`，namespace `RBM.Gauss.Sizes`）：
- `STXiRound'`（QtNonzeroBoot.lean:92）：`∀ n_ p, 2 ≤ n_ → … → Prec sz (U := STPair s t) (STXiLK n_) (ζ)`
- `STXiRoundPT'`（QEndB1.lean:84）：同上但 `3 ≤ n_`，结论为 `PrecPT`

`STIngR`（Step34Pins.lean:445）：`3 ≤ d` → ∃ 𝔠d > 0 → …（流条件）→ `R sz s t` → `Concl sz (STflowE z) s t`。

### PrecPT→Prec 桥接模式

无通用桥（`stochDomAt_of_perTimeDomAt` 需 `Fintype (U l)`，`STPair` 为无界不可数集）。已有模式（T2258 NQEndFlowLift.lean、T2299 QtNonzeroFlowLift.lean，均为 `private`）：

1. **包络**：`nqFlowSharp t XL/XLK`（公开，非降，`1 ≤ X♯ ≤ X`）；转移 pair 假设
2. **ζ♯ 引理**（lo=1）：`1 ≤ ζ♯`，`ζ♯` 对 u 单调，`ζ♯ ≤ ζ`（可从 lo=2 版本直接复制）
3. **对角约束**：LHS 仅依赖 `q.1.1`，ζ♯ 对 `q.1.2` 单调 → 在 `TimeIcc s t n × Unit` 上 PT 约束对角化
4. **单侧网提升**（~150 行 private copy）：`(w ↦ ξ(w,n_) ≺ ζ♯(w))` PrecPT → Prec
5. **对角→pair 传播**（~30 行）：`StochDomAt.of_subset` + `prec_of_le_right ζ♯ ≤ ζ`
6. **组装**：`stXiBootR_of_round d STCaseI H` 得 `STOeqQt' d`

第三份 private copy 不可避免（T2299 已接受 verbatim copy 先例）。

### n_=2 缺口（实质性）

T2310 的 `3 ≤ n_` 来源：`altGridEndQN`（QEndGrid.lean:1326，`1 ≤ m`）→ `altGrid_arith`（:1225，`τ' = min(ε/4, e₂/(40·d·m))`，`m=0` 分母为零）。底层层（QProxy、altYGridN、startLevelQN）无下界，`m=0` 有效。

解决方案：Primed successor `altGridEndQN'`（`τ' := min(ε/4, e₂/(40·d·(m+1)))`）+ `STXiRoundPT''`（`2 ≤ n_`，PrecPT）→ `stOeqQtRoundPT''_holds : ∀ d, STOeqQtRoundPT'' d`。改动限于 QEndGrid/QEndA/QEndB1 中的 primed successor（原签名冻结，TEAM §5.3），≈250-350 行。

`altQFlow_core`（QEndB1.lean:721）at `m=0`：`XLK 1 ≤ STbootRHS 1 … 2 p` 因 `Icc 1 1` 平凡成立；数值行 `altGrid_arith` 以 `m+1` 替换 `m` 后 `τ'·d·m = τ'·d·(m+1)-τ'·d` 边界仍满足（需重检，放入 T2313 工单）。

### 设计决定：拆两票

**T2313 = S3-18b2a**（前置）：
- 目标 pin：`stOeqQtRoundPT''_holds : ∀ d, STOeqQtRoundPT'' d`（`STXiRoundPT''`，`2 ≤ n_`，PrecPT 结论）
- 改动：QEndGrid（`altGridEndQN'`，~120 行）+ QEndA（`gridDriftQN_envelope'`，~15 行）+ QEndB1（`STXiRoundPT''` 定义 + `stOeqQtRoundPT''_holds`，~150 行）
- 依赖：T2302（S3-18a2，QEndGrid，ec3f678）+ T2294（S3-18a1，QEndA，8a0c4cd）+ T2310（S3-18b1，QEndB1，319bf17）；均已合并；无 HELD 依赖 → **可立即开工**
- 估计：250–350 行；角色：`prover-hard`

**T2314 = S3-18b2b**（主，依赖 T2310 + T2313）：
- 目标 pin：`stOeqQt'_holds : ∀ d, STOeqQt' d`（`STIngR d STCaseI STXiBoot'`，`STOeqQt'` NQEndFlow.lean:127）
- 新文件：`RBM3D/Induction/QtXiRoundLift.lean`；包络 + ζ♯(lo=1) + 对角 + 单侧网 + 对角→pair + 组装
- 依赖：T2310（319bf17）+ T2313（待合并）+ T2304（S3-22c，7812b3c，`stXiBootR_of_round`）
- 估计：700–750 行；角色：`prover-hard`

### ST-3 下游
T2313 → T2314 → `stOeqQt'_holds` → S3-24b（`STIterR'`，NQEndFlow.lean:134）→ ST-3 46/46。

**H114：** commit 本节（§127）+ T2313.md。

## §128 — BA gate 上限：Jun 批准 72（总调度，2026-10-07 16:20 UTC）

**Jun 决定（消息 "72"，2026-10-07 16:20 洛杉矶时间）：** BA gate 上限 = **72**（原 §52 批准上限 70，现扩至 72）。

**效果：** T2303（BA-L2b）HOLD 解除，可立即开工（不再受上限阻挡）。ROUTES BA 更新：22 / **72**；"上限 70" → "上限 72（§52/§57→§128）"；T2303 blocker 注释替换为可开工提示。

**H115：** commit 本节（§128）+ ROUTES BA 更新。
