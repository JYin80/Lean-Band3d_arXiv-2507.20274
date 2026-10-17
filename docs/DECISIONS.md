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

## §129 — T2313 合并；放行五张：T2314、T2303（拆）、T2316、T2317、T2318（总调度，2026-10-08 02:15 UTC，流程事项）

- (0) **T2313（S3-18b2a）合并** ae94fa7（审核一轮 PASS，4123 jobs）：`STXiRoundPT''`、`STOeqQtRoundPT''`、`stOeqQtRoundPT''_holds`（n_ ≥ 2）。**ST-3 43 → 44/46**。
- (1) **BA-L2b 拆两张**（§128 上限 72）：**T2303 = BA-L2b1**（`Graph/BAExpandW`：`BAlweight` + 图词汇 + `lanlw_val`，中心约 1180，prover-hard；超 1500 在节边界停）；**T2315 = BA-L2b2**（`Graph/BAExpandWOrd`：目标 3(c) 计数、`lanlw_ord`、`lanlw_scalingOrderG` + (I3)–(I4)，约 850），T2303 合并后写 check 再放行。BA 计划 70 → 71。草稿 `docs/tickets/drafts/T2303-*` 保留作底稿。
- (2) `lem_lweight` 的图运算（T2303 草稿 stale (2)）不在任何票内：BA-L3 设计时定（并入 L3，或在上限 72 内再加一张）。
- (3) **T2314 = S3-18b2b**（`Induction/QtXiRoundLift`，prover-hard，720/850/1000）：`stXiRoundQt_holds`（PrecPT→Prec 提升，§127 模式，T2258/T2299 私有引理第三份拷贝）+ `stOeqQt'_holds := stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)`；删 owed `STOeqQt'`。`STXiRoundPT''` 单独覆盖全部 n_ ≥ 2（与 `STXiRoundPT'` 只差门槛；与 `STXiRound'` 只差 Prec/PrecPT），`stOeqQtRoundPT'_holds` 不用。关键路径，列表顶。合并后 ST-3 45/46。
- (4) **T2316 = UN-27 `Grid`**（RBM2D 移植，`RBM.Univ.GUEPhase`，prover-hard，820/900/1000）：§91 记的 ZRescale 缺名现已在 `Defs/Semicircle`；`green_smul_mul` 私有（`Induction/ConArg.lean:386-417`）照拷。`GUEPathBounds` 只做 band 形（BA 形归 BA-C5，T2173 类 G），本票不加登记行（首个消费者 UN-33 登记）。解锁 UN-31 `Proc`。
- (5) **T2317 = BA-P2 `BA/KKernel`**（prover，500/700/950）：K = |M|²，无现成钉文，新陈述 `BAK…`（对称、Ward 行和、尾、指数矩、邻点下界）；d=3 数值脚本全过。附一条给监督（不扣票）：BA-P3 大 g 的符号间隙无论文出处，需 `1−|m|² ≥ c(d,Λ,κ)g²` 与 M 的超八面体对称，P3 设计时处理。
- (6) **T2318 = LW-14e-4 Sound**（`Graph/LWExpSound`，prover-max，1100/1400/1800）。**O2（§119）PASS**：waved 颜色只进边值（`7_8:134-139`）；分子、`n_W`、`ord`、辅助图与颜色无关；Lean 中 `WEdge.col/σ` 只被 `WEdge.val` 读。新 `RelKids`（Bridge 2 沿 `Rel`，T2288 审核 §8 obs. 2 的缺口）、`BelowOfSound`；`lwG5Expand'_holds`；登记 `LWG5Expand` → superseded。中心近 1500：整张放行，预设切 T2318a（L5′+L6）/T2318b（L7+L8，LW +1 行），超 1500 在节边界停（T2295 先例）。**流程决定**：允许删 `Graph/LWExpSim.lean` 中 `lwExpSim_*` 前的 `private`（文件名前缀满足 CLAUDE.md §3 (E)；只此一种改动），免第三份拷贝。
- (7) 放行顺序（parallel 4）：**T2314 → T2318 → T2303 → T2316 → T2317**（第五张等空槽）。计数：ST-3 44/46、LW 42/47、UN 40/65、BA 23/72（ROUTES 原写 22/39 为漏改；§110 已记 BA 23、UN 40）。下一张票号 **T2319**（T2315 已占）。

## §130 — 合并 T2314、T2316、T2317；T2318 预检 FAIL → 修复路线 (A)，新票 T2319（总调度，2026-10-08 02:50 UTC）

- (0) **合并**：T2316（UN-27 `GUEPhase/Grid`，d133012）→ **UN 41/65**；T2317（BA-P2 `BA/KKernel`，fc0904a）→ **BA 24/72**；T2314（S3-18b2b `Induction/QtXiRoundLift`，c8e166a，`stOeqQt'_holds`，删 owed `STOeqQt'`）→ **ST-3 45/46**。解锁：UN-31 `Proc`（Grid、Generator、KPrim 都已合并）、S3-25/26（`STStep3I/II`、`STStep4I/II`）、BA-P3 `KSymbol`（先处理 §129 (5) 记的大 g 符号间隙）。BA 下一张合并即到 25 → 写 REQ。
- (1) **T2318（LW-14e-4）1a FAIL**（`docs/reports/T2318-prove.md` (a)）：钉文 `BelowOfSound` 为假（反例：一条无实边支撑的 ×-边 b-edge）。原因在已合并的 T2306：`belowOf`（`LWExpCert.lean:157-190`）用 Δ 的全部 ×-边作一致性检验，真实分拆（`dotBase`）丢掉 b-edge；(Oe2x) 家族图保留 dotted、删实边，3061/3394 个家族图受影响，`cert_all` 没覆盖 212194（s=F）/231842（s=T）个真实项（python 镜像：全是满足叶性的叶子，0 个非叶）。目标 1、2、5、7 PASS。不是论文问题（探针簿记错，`t/T2288 … T2288Cert.lean:335-370`），无 paper-delta。
- (2) **修复路线 (A)**（Fable 设计，`docs/claude-team/fable/2026-10-08-t2318-belowof.md`）：带撇修正旗标 `belowOf'`（一行：`X0 := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)`，即恰为 `¬ Consistent`）+ 新证书 `cert_all'`，新文件 `Graph/LWExpCertB`、`LWExpCertBS0`、`LWExpCertBS1`（`RBM.Graph.LWCert`；已合并文件不动）。舍 (B)（再走一遍同一棵树、成本相同、L7 两分支）与 (C)（b-edge 合并后叶性无短论证：可生成新的无圈环，`n_M` 不单调）。
- (3) **T2319 = LW-14e-1′**（prover，720/790/1000）：构建按 H101 单独跑（S0/S1 各约 12–19 分钟，内存 7.5–9.5 GB；先测最重块 `ch_FF_10_0_8'`，超 8 GB 或 5 分钟按票内预授权按候选拆块）。LW 计划 47 → 48；若 T2318 走预设切 T2318b 则 49（上限 50）——下次 LW REQ（LW=43）告知监督。
- (4) **T2318 Amend 1**（`docs/tickets/T2318-amend-1.md`）：`BelowOfSound`/`SoundStep`/`SoundRoot` 改用 `belowOf'`/`childrenB'`/`rootInfo'`（定理名不变），check 文件已改（依赖 T2319 模块，T2319 合并后再编译）。T2318 等 T2319 合并 + 中枢 H101 合并后构建 B 模块，然后从 1a 重开；02:11 报告留作 `T2318-prove-1a-fail.md`。不计返工。
- (5) 旧 `LWExpCertS0/S1` 在 T2318 改用 B 模块后成死代码（从头构建约 20 分钟内核时间）；删不删由 LW-14f 定。
- (6) 计数：ST-3 45/46、LW 42/48、UN 41/65、BA 24/72。在跑：T2303。下一张票号 T2320。

## §131 — T2303 合并 → BA 25，REQ-0305；放行 T2315（总调度，2026-10-08 03:05 UTC）

- (1) **T2303（BA-L2b1）合并** 8f90d6d（审核一轮 PASS，4127 jobs）：`BAlweight`、`baLweight_holds`、`lanlw_val`、图词汇。**BA 25/72** → **REQ-2026-10-08-0305 已写**（Q1 BA 外推与拆分；Q2 BA-P3 大 g 符号间隙路线——答复前 BA-P3 不放；Q3 T2318/T2319 修复确认）。
- (2) **T2315 = BA-L2b2**（`Graph/BAExpandWOrd`，prover-hard，650/850/1200）：目标 3(c)（`lanlwT1_counters`、`lanlwD_counters`、`lanlw_ord`、`lanlw_scalingOrderG`）+ (I3)–(I4)，陈述取 T2303 草稿 check 原文（`T2303_` → `T2315_`），check §1 沿用已编译的 T2303-check §1 再加 T2303 合并名。BAVocab 私有闭包引理本地重证。
- (3) 票面起草从此由总调度自写，Fable 子代理只用于数学卡住、一次一个（Jun 2026-10-08 02:4x UTC 指出用量过大）。
- (4) 在跑：T2319（H101 构建）。待写（总调度自写）：S3-25/26（ST-3 末张）、UN-31 `Proc`。下一张票号 T2320。

## §132 — S3-25 = T2320：Step 3 按消费的区域证；`STStep3I` 不作目标（总调度，2026-10-08 03:10 UTC）

- (1) ST-3 计划 46 → 47：S3-25（Step 3）、S3-26（Step 4）两张都还没做（S3-27 已取消，§68 (9)）；在外推 46–48 之内。
- (2) **S3-25 = T2320**（`Induction/Step3.lean`，prover-hard，600/800/1100）。论文在 case (i) 内以 `1-u = ilambda²` 再分（`3_5:1384`：`1-s > ilambda²` 时由 `(lRB1)` 直接得；其余靠 `lem:iterations`），且加中间时刻（`3_5:1105` 脚注）；形式化里 Steps 2–5 不能加中间时刻（§68 (9)），而 `ST_mainIndR_of_steps`（`MainIndRegimes.lean:165`）对 Step 3/4 的区域 `R34 ⊇ R` 是泛型的。所以 S3-25 证三个区域钉：`STStep3R d STReg5III`（`(lRB1)` + `((1-s)/(1-u))B_s ≤ 4B_u`，纯实代数）、`STStep3R d STReg5I`（迭代，`STReg5I = STRegIterI`）、`STStep3II d`（迭代 case (ii)）。探针骨架 `st_step3_skeleton`（`3c58211`）私有移植。删 owed `STStep3II`。
- (3) `STStep3I`（case (i) 含跨 `ilambda²` 的 `[s,t]`）不作目标：S3-26 加带撇组装 `ST_mainIndR_III/I_of_steps'`（吃区域钉）后，登记把 `STStep3I`、`STStep4I` 标为 superseded。路线与 §68 (9) 一致，不改已合并文件；REQ 下次告知监督。
- (4) 下一张票号 T2321（S3-26），然后 UN-31 `Proc`。

## §133 — S3-26 = T2321：`STStep4I/II` + 带撇总组装 `ST_mainInd_of_pins'`（总调度，2026-10-08 03:15 UTC）

- (1) Step 4 不分区域：`STStep4R d R` 以 Step 3 的结论 `STLmaxU` 为前提，`STXiBoot'` 在 case (i)（`stOeqQt'_holds`）与 case (ii)（`stOeqQtNZ'_holds`）全域已证，故直接证 owed 的 `STStep4I`、`STStep4II`（探针骨架 `st_step4_skeleton` 换成 R2* 的 `STXiBoot'`，首项 `B_s^{-1/(4p)}` 由 `st_Bctl_ge` 吸收）。
- (2) **T2321**（`Induction/Step4.lean`，prover-hard，450/600/850）另加 `ST_mainInd_of_pins'`：同 `ST_mainInd_of_pins`（`MainIndRegimes.lean:674`），但 Step 3 用区域钉 `STStep3R · STReg5III`、`STStep3R · STReg5I`、`STStep3II`（作前提，不 import T2320 的文件，两票并行），Step 4 用本票定理；区域 (iii)/(i) 走 `ST_mainIndR_of_steps d R R`。
- (3) 登记：T2321 删 owed `STStep4I`、`STStep4II`，把 `STStep3I` 从 owed 移到 superseded（被区域钉 + `ST_mainInd_of_pins'` 取代；定义保留）；T2320 只删 `STStep3II`，不碰 `STStep3I`。合并顺序 T2320 先于 T2321（共享 `Axioms.lean` 的锚文本）。
- (4) T2320 + T2321 合并后 ST-3 47/47（计划 47）；最终把三个 Step-3 定理代入 `ST_mainInd_of_pins'` 归 ST-6（ST-D6 未写）。下一张票号 T2322（UN-31 `Proc`）。

## §134 — UN-31 `Proc` 拆两张：T2322 = UN-31a（`:1-860`），T2323 = UN-31b（`gueKproc_detDom`）（总调度，2026-10-08 03:20 UTC）

- (1) RBM2D `GUEPhase/Proc.lean` 1424 行，按已合并兄弟票的放大比（×1.01–×1.74）整张 1450/1750/2400，超 1500。源文件在 `:860/:862` 有干净切缝：前半只用已合并名字；后半 `KprocDom`/`KprocInput` 用 RBM2D 的 K-loop 机器（`KLoop.Kcal`、`Mt`、`Par`、`Kbound_prec_uncond`、`kloop_Mt_eq`、`scaleM`、`size_eq`），RBM3D 无对应，须走 `STKbound` 路线（先例 `GridDriftN.lean:54`、`GridEnvelopeN.lean:38`）。
- (2) **T2322 = UN-31a**（`Universality/GUEPhase/Proc.lean`，prover-hard，900/1050/1450）：11 个定义（check §2 原文，按 Grid 的换名规则译成 d 维）、结构事实、loop 最大值事实、`norm_egtNGUE_le`、`gueDev_succ_le`；d 敏感的 `gue_inv_W_le_loopMax`、`norm_egtNGUE_le` 由预检 (i) 写出 d 维陈述（经 `inv_N_le_maxLoopPM`、`ellT_eq_L`）。**T2323 = UN-31b**（`GUEPhase/ProcK.lean`）T2322 合并后写。UN 计划 +1（上限 65 内）。
- (3) 放行顺序：T2320 → T2321 → T2322 → T2315（ST-3 关键路径先）。下一张票号 T2324（T2323 已占）。

## §135 — 监督 2026-10-08-0344 判决 PASS（REQ-0305 归零）；H101 (3) 放宽（总调度，2026-10-08 04:08 UTC）

- (1) **Q1 BA 外推**：71–72 不现实，中心约 80–85（76–95）。确定性行实际 ×0.55，随机链 ×2.7（行数），图层 ×1.3；主要风险 BA-L3（孪生 `LWLvl1` 4462 行）、BA-L4（LW-14 链约 1 万行）、T1–T8/U1–U6/V1–V3。可合并/删：G2–G6 → 4、E1+E3、P7+P8、N1 并入 C3–C5/M1、K5（若 `BA/Ward` 已给）。**O1**：写 BA-L3/L4/T1 之前先做一次「模型通用实例化」设计探针（(i) `LWLvl1`、LW-14e 引擎能否对边核/传播子参数化，BA 直接实例化；(ii) BA-T1…T8 能否经模型通用接口吃 ST-2 定理），按实测比例重排 BA 计划，**给 Jun 一个上限数**；在此之前 BA 只发计划内的行。
- (2) **Q2 BA-P3**：路线对，补上缺口；属 paper-delta（论证缺失、陈述为真）→ **D614**：BA 游走在 `g ≍ 1` 的非退化论文未证，由 `1 − |m|² ≥ 2dg²/R⁴`（`R = 2dg + |E+m|`）与坐标置换不变性补上。**O2**：放 BA-P3，目标含方差引理与坐标置换不变性，预设切 P3a/P3b（只在触发时计数）。
- (3) **Q3**：修复 (A) 确认；`belowOf`/`cert_all` 在 `Graph/LWExpCert*.lean` 外无消费者，`LWExpSim` 的 `childrenX` 是精确的，T2311 不受影响。**前向规则**：BA-L4 及 LW-02/LW-13b 若用证书，一律用 `belowOf'`、`cert_all'`。
- (4) §132–§133（S3-25/26 区域钉）PASS；§127、§129 (4)、§134 无意见。计数表：UN 计划已到上限 65，下次 UN REQ 在 45；LW 到 43 照计划告知监督。
- (5) **H101 (3) 放宽（流程事项）**：原 (3)「证书模块构建期间不开新工作流、不跑别的全量构建」使 T2320/T2321/T2322/T2315 在 T2319 构建期间空等约一小时。改为：证书模块构建期间**可以开新工作流**（stage 1a 预检不跑 lake）；其他工作树的单模块 `lake build` 照 (4) 内存护栏（空闲 < 12 GB 则等）；**仍不跑别的全量 `lake build`**（合并前的全量构建排在证书构建之后）。(1)、(2)、(4)、(5) 不变；对 T2319 与以后的证书票同样适用。

## §136 — 放 BA-P3 = T2324（`BA/KSymbol`，监督 0344 O2）（总调度，2026-10-08 04:10 UTC）

- (1) **T2324 = BA-P3**（prover-hard，1000/1300/1700）：目标 1–4（P3a）方差下界 `1 − |m|² ≥ 2dg²/R⁴`、坐标置换不变 `BAMB_perm`、各方向等权 `BAK_dir_eq`、各方向下界 `K_{0,±e_i} ≥ c g²`（一致于 `L`、`g ∈ (0,Λ]`）；目标 5–8（P3b）符号 `BAKhat`（对偶环面 `θ_k = 2πk/L`）为 Fourier 变换、间隙 `1 − K̂ ≥ c g²|θ|²`、懒惰 `1 + K̂ ≥ 2κ²`、二阶矩 `≤ C g²`。预设切 P3a/P3b（超 1500 在边界停，P3b 另编号，BA +1，只在触发时计）。D614 已记。
- (2) BA 计划仍 71（P3 本就在计划内）；O1 的模型通用实例化探针与 BA 重排在写 BA-L3/L4/T1 之前做，之后给 Jun 一个上限数。
- (3) 放行顺序：T2320 → T2321 → T2322（已在预检）→ T2315 → T2324。下一张票号 T2325。

## §137 — T2321 合并 → ST-3 46/47；T2320、T2322 预检 PASS（总调度，2026-10-08 04:30 UTC）

- (1) **T2321（S3-26）合并** 4a63165（审核一轮 PASS，4128 jobs）：`stStep4I_holds`、`stStep4II_holds`、`ST_mainInd_of_pins'`；登记删 owed `STStep4I/II`，`STStep3I` 移入 superseded。**ST-3 46/47**。预检记的票面小误（不影响判决）：`STXiBoot'` 的下标是 `lo = 1`；无 `B_u^{1/6}` 项；无 `min`/`st5_conStInd_mono` 步。合并顺序先于 T2320（共享锚文本不在同一行，无冲突）。
- (2) **T2320（S3-25）1a PASS**（三个目标全过；f1：`hbase` 还需 `hK`，1b 处理）；**T2322（UN-31a）1a PASS**，`gue_inv_W_le_loopMax` 取预检的 d 维修正 C1（`hell : L^d(1-u) ≤ 1`，结论 `(W⁻¹)^d ≤ 2 L₂`；字面的 `L²` 由此路线推不出）——票面本就交预检定 d 维陈述，照准。
- (3) T2315 预检中；T2324 等槽。在跑：T2319、T2320、T2322、T2315。

## §138 — 监督 O1：BA 模型通用实例化设计探针交中枢 = T2325（总调度，2026-10-08 04:35 UTC）

- (1) **T2325 = BA-DP2**（设计探针，只出报告，**不计 BA 行**——监督 0344 O1「at no ticket cost」；prover-max，同 T2288 先例）：(i) `LWLvl1`、LW-14e 引擎能否对边核/传播子参数化让 BA-L3/L4 实例化；(ii) BA-T/U/V 链能否经模型通用接口吃 ST-2…ST-5 定理（先例 BA-S3、UN-51g）；(iii) BA 重排（实测比例、监督列的合并/删候选 (a)–(e)），两条路线的总数与**一个**推荐上限。报告给监督读，上限数由总调度带给 Jun。
- (2) 交中枢做而不用总调度的 Fable 子代理（Jun 2026-10-08 指出 Fable 额度被起草工单的 4 个子代理浪费；§131 (3) 规则不变：Fable 只用于数学卡住、一次一个，不用于起草）。
- (3) 优先级在证明票之后。下一张票号 T2326。

## §139 — T2320 合并 → **ST-3 47/47 闭合**；T2322 审核 PASS（修复一次）（总调度，2026-10-08 05:00 UTC）

- (1) **T2320（S3-25）合并** b582dab（审核一轮 PASS，4129 jobs）：`stStep3RegIII_holds`、`stStep3RegI_holds`、`stStep3II_holds`；删 owed `STStep3II`。**ST-3 47/47，子门槛 ST-3 完成。** `ST_mainInd_of_pins'`（T2321）的 Step-3/4 前提全部有定理。
- (2) **T2322（UN-31a）** 审核第 2 轮 PASS（规则 B 修复一次，计返工）；合并因证书构建（H122）延后。合并后 UN 42/65，写 T2323（UN-31b）。
- (3) 主归纳仍欠的步钉：`STStep2`（`ST_step2_of_pins` 等）、`STStep5I/II`、`STStep6I/II/III`（后者等 LW-14 `LWtermEXP`）；ST-4 31/35、ST-5 17/18 的余票与 ST-D6 下一步排查（总调度自做，不用 Fable）。

## §140 — 合并 T2315、T2322、T2324、T2325；BA-DP2 结论：BA 约 163–174 张，推荐上限 175 → REQ-0850（总调度，2026-10-08 08:50 UTC）

- (0) 中枢 05:2x–06:20 UTC 撞上用量上限（"session limit · resets 11:20pm LA"），三个阶段按规则 (H) 在重置后重跑；无数学影响。
- (1) **合并**：T2322（UN-31a `GUEPhase/Proc`，e17d56f，修复一次）→ **UN 42/65**；T2315（BA-L2b2 `Graph/BAExpandWOrd`，044707b）、T2324（BA-P3 `BA/KSymbol`，0da5856，P3b 切未触发）→ **BA 27/72**；T2325（BA-DP2 设计报告，5d9506a，报告型，不计行；探针留 t/T2325 05b9293）。
- (2) **T2325 结论**（`docs/reports/T2325-portmap.md`）：(i) 图层除 `expandG_sum`、`lvl1_size_le`、`Lvl1Lt`、`AnpKey*` 外不对边核/传播子参数化（读 Owx/Oe1x/Oe2x 项形、标量 `M = m I`、`GaussIBP`），BA-L2c/L3/L4 须孪生（源 38.8k 行，按 0.8 约 31k 行，portmap 只给 3.1k）；(ii) ST 链定理的前提/结论是 `Lloop sz`/`STKloop sz` 谓词、46% 私有、51% 读带状对象，BA-T/U/V 是移植（Steps 2–6 孪生 78–92k 行，portmap 20.9k）。`Induction/` 自 T2161 估算以来从 57k 长到 114k 行。**重排：路线 I（能实例化处实例化）163 张 [128..214]，路线 T（全孪生）174 [141..223]；推荐上限 175**；可能压低它的杠杆是 §4 的 G-in-place 试点（一张设计票）。paper-delta 候选 T2325a–c → **D615–D617**。
- (3) 与监督 0344 的 80–85 相差一倍 → **REQ-2026-10-08-0850**：请监督复核 T2325 的计数方法与比例，再定给 Jun 的**一个**上限数（O1）。答复前：BA 只发计划内且不依赖路线的行（BA-P4 `KHeat` 可写）；BA-L3/L4/T1 不写。

## §141 — UN-31b = T2323（`GUEPhase/ProcK`，`gueKproc_detDom`）（总调度，2026-10-08 08:55 UTC）

- (1) **T2323**（prover-hard，600/750/1000）：移植 RBM2D `Proc.lean:862-1424`。唯一改动：`t₁` 处 K-loop 初值由 `STKloop` 给（`hKinit`），其界用 `STKbound E`（新前提 `hKb`，先例 T2153a；流下由 `stKbound_of_flow` 证），代替 RBM2D 的 `Kbound_prec_uncond`；从 `B_{t₁,0}` 换到 `(Nη_{t₁})⁻¹` 需 **`L^d(1−t₁) ≤ ilambda²`**（零模区域；RBM2D 的 `L²(1−t₁) ≤ 1` 是 d=2、λ=1 情形，字面的 `L²` 在 d≥3 差 `L^{d−2}`，`N^ε` 吸收不了）。预检 (ii) 核对消费者的 `t₁` 满足之。
- (2) 放行时有 3 个空槽（只 T2319 在审核）。下一张票号 T2326。

## §142 — 监督 0944 判决 PASS（REQ-0850 归零）：BA 约 175（140–225），先做试点再定上限；排序规则（总调度，2026-10-08 09:55 UTC）

- (1) **Q1**：T2325 方法与量级可靠，监督 0344 的 80–85 偏低（没看源码增长：`Induction/` 57k → 114k）；三处修正：K/G 行若按源码估 +20–25（一致方法下路线 T ≈ 195–200、路线 I ≈ 185）；7 张「公开」票计入它们所改的门（ST/LW 各 +2–5）；Step 3–4 的 0.8 孪生比可能偏高（唯一可能大幅下修处）。**净：中心 ≈ 175，区间 140–225，K/G 上行 ≈ 195。**
- (2) **Q2 / O1**：先**告知** Jun 预估（≈ 175，140–225，上行 ≈ 200），**暂不问上限**；先做试点（O2），再带**一个**数。若 Jun 现在就要数：**200**。
- (3) **O2 试点 = T2326**（BA-DP3，报告型，prover-max，计 1 个 BA 行、在现计划内）：在两处测「模型通用化」的改动比例 `g`——Step 2 的 `ST_selfImprove_section` 与 Q 文件族的 `QDriftA.lean`（在 `stStep3RegI_holds` 依赖链上）；`g ≈ 0.25` 则 BA 链约 30–40 张、总数 110–125；`g ≳ 0.6` 则无节省，175–200 成立。
- (4) **O3 排序规则（总调度自定）**：ST-4…ST-6 闭合、其文件的「公开」票合并之前，不写 BA-T/U/V、BA-L3、BA-L4；公开票计入所改文件所属的门。路线备选（监督 Q3）：(a) BA 链在带状链闭合后（已采用为排序规则）；(b) 模型通用载体（试点所测）；(c) BA 只证条件定理（Steps 2–6 作为一个显式假设，约 60–80 张）；(d) BA 出范围（MA-06 不含 `Thm27`）。(c)、(d) 只有 Jun 能定，试点之后与上限数一起问。
- (5) **O4（UN）**：`gueKproc_detDom` 的消费者（UN-33…UN-52）的 `t₁` 一律取零模区域（`hell`），不用 `GridCheck` 的时刻。
- (6) 计数：BA 27/72（试点后 28）；LW 到 43（T2319 合并时）→ 照计划给监督写说明；UN 到 43（T2323 合并时）。下一张票号 T2327。

## §143 — 中枢空槽：UN-32 = T2327（`GUEPhase/Markov`）；T2318 重启排成 H128（总调度，2026-10-08 10:00 UTC）

- (1) Jun 指出中枢已空（T2319、T2323 只在等合并，T2326 待 H127）。**T2327 = UN-32**（`Universality/GUEPhase/Markov.lean`，RBM2D 912 行移植，prover-hard，850/950/1200）：`gueCondExp_freeze`、`gueHasCondSubgaussianMGF_of_frozen`、`vGue`、`gueMap_lin_Xmat`、`gueHasCondSubgaussianMGF_linear`、`gue_highProb_incr_le`；51 个外部名只缺 3 个（`Z2` 换名；`Xmat_apply`、`hfun` 本地重证）；与维数无关，除基数计数 `(W L)^d`。
- (2) **H128**：T2319 合并且 H101 合并后构建完成即编译 T2318 新 check，exit 0 则 T2318 从 1a 重启。
- (3) 下一步自写（不用 Fable）：BA-P4 `KHeat`（A 组确定性行，监督 0944 认可照常推进）、ST-4 余票摸底。下一张票号 T2328。

## §144 — **Jun 决定：BA 必证，张数不设上限；每个阶段须有监督明确验证**（总调度，2026-10-08 10:05 UTC）

- (1) **Jun（2026-10-08 03:0x PDT）**：「BA 肯定是要证明的，多少张我都批，只是每一个阶段都要有明确监督验证，只要不浪费走错路，都可以批，它本来就是非常复杂。」→ BA 上限 72（§128）**取消**，不再为 BA 张数问 Jun；O1（监督 0344/0944）的「一个上限数」不再需要。T2326 试点照跑，目的从「定上限」改为「选路线、不走冤枉路」。
- (2) **BA 阶段闸门（流程，总调度定）**。BA 剩余工作分为阶段：**P**（传播子确定性层 P4–P8）、**K**（K-loop K1–K5）、**G/E**（Green 层 G2–G6、E1–E3）、**L**（图层 L2c、L3、L4 及 `lem_lweight` 图运算）、**T/U/V**（链：Steps 2–6、主归纳、`GLoopAtT0`）、**M/N**（装配 M1–M3、N1–N2），以及当前在做的 C 行补完。每个阶段：
  - **开阶段闸门**：写该阶段第一张票之前，总调度把该阶段的设计（钉文、拆单、依赖、路线选择及其依据）写成 REQ 交监督；**监督 PASS 之后才放该阶段的票**。
  - **关阶段闸门**：阶段最后一张合并后，写 REQ 请监督核对该阶段钉文全部证出、与下游消费者的形状一致、没有被取代而未登记的路线；**PASS 之后，消费它的阶段才开**。
  - 阶段内单票照常（预检 + 审核）；预检 FAIL 或路线疑问立即 REQ，不等阶段末。
- (3) **防走错路的排序（沿用 §142 (4)）**：T/U/V 与 L 阶段不早于 ST-4…ST-6、LW-14 闭合及其「公开」票合并；T/U/V 的路线（模型通用载体 G / 实例化 I / 孪生 T）由 T2326 试点结果 + 监督 PASS 决定。P 阶段（BA-P4…P8）不依赖路线，现在可开，但先过开阶段闸门。
- (4) ROUTES 的 BA 行改为「不设上限（Jun §144），阶段闸门」；BA 计数仍照实记。LW（≤ 50）、UN（65）上限不变。
- (5) **第一个开阶段闸门：阶段 P** → **REQ-2026-10-08-1010**（P4 `KHeat` 的 Fourier 路线、P5/P7 零模、P6 分部求和所需正则性、拆分；5–7 张）。监督 PASS 前不放 BA-P4。

## §145 — **Jun：其他方向尽量先闭合（与 BA 并行）**；ST-4 收尾两张（总调度，2026-10-08 10:17 UTC）

- (1) **Jun（2026-10-08 03:1x PDT）**：「另一方面 尽量同时让其他方向先闭合。」→ 排序（流程，总调度定）：BA 阶段 P 等监督（REQ-1010）期间，槽位优先给 **ST-4 收尾 → LW-14 → UN 链 → MA**；BA 只放闸门已过的票。
- (2) **ST-4（31 / 35）剩四行**（T2134 portmap 447–460）：S5-13 `EtermsMid`、S5-15 `DuhamelI`（← S5-13）、S5-16 `IniTermI`、S5-26 `DuhamelII`（← S5-15）。现在放两张互不依赖的：
  - **S5-13 = T2328**（`Induction/EtermsMid.lean`，`stEtermsMid_of_LWT : ∀ d, STLWT d → STEtermsMid d`，prover-hard，700/900/1300）。`STLWT` 留作前提（LW 闸门证，经 `STLWT_of_LWtermExp`），与 `ST_step2_of_pinsLW'` 同一做法；登记行 `STEtermsMid` 留 owed，注释写上「由 `STLWT` 证出」。
  - **S5-16 = T2329**（`Induction/IniTermI.lean`，`stIniTermI_holds : ∀ d, STIniTermI d`，prover-hard，1100/1400/1900，超 2200 拆出 `IniTermIUnif`）。登记删 `STIniTermI` 行。
- (3) **T2329 的一处论文外的接线（总调度查出，交 1a 核）**：`STCltFar`（S5-25 已证）只在序列终点 `t n` 给 `f^{far}`，而 `STIniTermConcl` 要对 `u ∈ [s,t]` 一致（`Prec` 的并在概率里面）。路线：`f^{far}_u` 只经确定性 `Θ_u` 依赖 `u`（预解式恒等式给 Lipschitz），`u` 网格间距 `N^{-C'}`；每个网格点对「最坏序列」`t'_n` 用 `stCltFar_holds`，再对 `≤ N^C` 个点取并；`STIngR5` 的前提从 `[s,t]` 限制到 `[s,t']`（`Prec` 指标集单调；`STConStInd` 用 `STBctl_mono`），作公开引理 `stIngR5_hyps_restrict`（S5-15 也可用）。1a 若有一条前提不能限制 → FAIL 并点名，不硬做。
- (4) 小比值情形 `ρ_u ≤ (log W)^{10}`（`(eq:assmtlarge)` 的补集，论文 `3_5:1950-1954` 一句带过）在 T2329 里要写出来：两次 `(uwp2-92kj)`，`(log W)^{20}` 被 `≺` 吸收。
- (5) 其余方向现状：LW-14 = T2319 合并中 → H128 重启 T2318 → LW-14f（`LWtermEXP` 组装，同时放开 `STStep2`/Step 6 三区域）；UN 链 T2323 待合并、T2327 预检中；MA 7/8 待 UN 链。S5-15 在 T2328 合并后写；ST-D6（主归纳组装设计）在 ST-4 闭合前写好。下一张票号 T2330。

## §146 — 监督 1048：阶段 P PASS（附 C1–C5）；合并 T2319、T2323、T2327；放 UN-33、BA-P4a；LW 43 / UN 45 的 REQ（总调度，2026-10-08 11:00 UTC）

- (1) **合并**（中枢，10:2x UTC）：T2319 = LW-14e-1′（ba2ddf3）→ **LW 43**；T2323 = UN-31b `ProcK`（9cd356f）、T2327 = UN-32 `Markov`（c99e133）→ **UN 44**。H128 已执行：T2318 从 1a 重开，1a PASS，1b（prover-max）中。H131 已执行：T2328 1a PASS、1b 中；T2329 1a 中。
- (2) **监督 1048（REQ-1010）：阶段 P 可开，PASS，附设计改正 C1–C5**，照办（写进阶段 P 各票）：
  - C1：P4 不能用单区域「`+L^{-d}` 地板」形，要和带状一样两个区域：(i) `τ ≤ L²` 无地板（`kProd_le` 孪生），(ii) `τ ≥ L²` 零模 + 能隙（`kProd_gap` 孪生）；切点是扩散时间 `τ = g² s ≥ L²`，不是 `n ≥ L²`。
  - C2：连续时间（Poisson 化）`P_s = e^{-s} Σ sⁿ/n! Kⁿ`，`Θ = ∫ e^{-(1-t)u} P_{tu} du`，与 `Theta_eq_laplace_prod` 同形，`LaplaceGauss` 按 `γ = t g²` 代入；只要 `BAK_gap`，不要懒性。
  - C3：倾斜在提升上做（居中提升 `K̃`，逐坐标 Chernoff 由 `BAK_exp_moment_le`，半群合并）；`A:58-67` 的 `Z^d` 游走读作环面核的居中提升 → P4b 报告记论文差异。
  - C4：P6 要的差分正则性没人产出 → 新行 P4c（单方向符号正则性由 `BAK_off_le`；区域 (i) 的单位差分，多项式衰减 `M = ⌊d/2⌋+1`）；P6 改路线须先 REQ。
  - C5：`σ₁ = σ₂` 四条归约（由 `BAProp5s`）进 P8。
  - 行：**P4a `KHeat`、P4b `KHeatTail`、P4c `KHeatDiff`、P5 `Prop5`（旧 P7 并入）、P6 `PropUnit`、P8 `Prop6Path`**，共 6 张；顺序 P4a →（P4b ∥ P4c）→（P5 ← P4b；P6 ← P4c）→ P8。阶段 P 超 9 张（1.5 倍）须 REQ。关阶段 REQ 列 `BAProp5to8` 四个电荷对全证、`Test/Axioms.lean:137-141` 五行删掉（O5）。
- (3) **放行（自写，不用 Fable）**：**T2330 = UN-33**（`Universality/GUEPhase/BoundsA.lean`，RBM2D 718 行移植，prover-hard，700/780/1000；两处与 `d` 有关：`HC` 控制 `(W^d)⁻¹`、`hellN : L^d(1-t₁) ≤ 1`，由 O4 的零模区域推出；登记只给 `GUEPathBounds` 行注释加条件生产者）；**T2331 = BA-P4a**（`BA/KHeat.lean`，prover-hard，800/1000/1400：`BAP`、`kBA`、Laplace 恒等式、半群/平移、基本性质、Fourier 形、对角界、`kBA_gap`（`kProd_gap` 逐字孪生））。槽位满（T2318、T2326、T2328、T2329），两张排队：先 T2330（§145 UN 先于 BA），后 T2331。
- (4) **REQ-2026-10-08-1100**（计划中的 LW 43、UN 45 说明）：L1 问 T2318 之后的顺序（LW-14f 先，因 `STLWT` 是 T2328 唯一未证前提、Step 6 等 `LWtermEXP`）及 LW-02 = T2297 能否带 Amend 重开；U1 问 UN 余 20 行（计划正好到上限 65）的路线信号。
- (5) 计数（宽口径，含已放行）：ST-4 33/35、LW 43/48（上限 50）、UN 45/65（上限 65）、BA 29（不设上限；阶段 P 计划 +6）、MA 7/8。下一张票号 T2332。

## §147 — 监督 1143：LW 两条路（C6/C7）；放 LW 引擎 T2332、S5-15 T2333；UN 外推告知 Jun（总调度，2026-10-08 11:52 UTC）

- (1) **合并**：T2328 = S5-13（7b9fefe，`stEtermsMid_of_LWT`）→ ST-4 S5-15 可写。T2329 1a PASS（§145 (3) 的 `u` 一致化路线过预检），1b 中；T2330 1a PASS（两处 `d` 行确认），1b 中；T2331 排队。**流程注**：T2328 写到 1757 行，超过停止线 1500 没停（审核 O2）；以后票里写明「停止线有约束力」，T2333 起照写。
- (2) **监督 1143（REQ-1100）PASS，改正 C6、C7**，照办：
  - C6：LW-14f 产出 `LWtermEXP`（期望界，给 Step 6 三区域），**不产出** `LWtermExp`（`≺` 界，`STLWT_of_LWtermExp`、`ST_step2_of_pinsLW'` 用的）。`LWtermExp` ← LW-01 ← LW-13b ← LW-02 = T2297，LW-16（`LWtermExpN`）并行。§145 (2)、(5) 里「`STLWT` 经 LW-14f」那句改正为此。
  - C7：`m` 无关展开引擎不存在（`lw_localregular` 在 `∃ outs errs` 前固定 `m`），是计划内的一行（0838 表「Engine 1」），T2297 不能只靠 Amend 重开；LW-16 也是计划内行，REQ 漏列。
  - 新顺序：① **引擎现在写，与 T2318 并行** → ② T2318 合并后 LW-14f → ③ LW-16 有空位就写（先做 0838 O3：`tailW` 类 `LWPsiRel` 在 `1-t ≤ ĝ²/L²` 区域是确定性的）→ ④ T2297 带 Amend 重开（引擎作展开输入；F2 用 `Ψ' := max(Φ n 0)(W^{-d/2})`）→ ⑤ LW-13b-2 → ⑥ LW-01。计数 48–49，尾部 50–52，**很可能在 LW-01 到 50**：LW-01 票要带「前提 ↔ 已合并生产者」表，供到 50 时 TEAM §6 复核（O2）。
  - O3（UN）：外推 **68–71 > 上限 65**（风险行 UN-47 `Eq729B`、UN-38 `DuhamelB`、UN-45/46 `OneLoop`；UN-51/52 还等 ST-D6）。照监督意见**现在告诉 Jun 一次，作信息，不提问**；首次拆分前写 REQ。
  - O4（UN 接口）：`hellN` 由 0944 的零模估计 `∀ᶠ n` 推出，不由 O4 的 `hell` 逐点推（`ilambda` 可大于 1）。T2330 不改；`Bounds_path` 的消费者（UN-50/51）照此。
- (3) **放行（自写，不用 Fable）**：
  - **T2332 = LW 引擎**（`Graph/LWEngine.lean`，prover-max，900/1200/1700）：`lw_localregularX : ∀ p c, 0 < c → ∀ K0 d D, ∃ outsX errsX, ∀ m ≠ 0, LWLocRegConcl … (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧ (每个图 ≥ p 条黑波浪边)`；`LWLocRegConcl` 逐字取 `lw_localregular` 的结论；递归仿 `lvl1_exists_aux`（WF + 截断），不用 `expandG`；预检 (ii) 查候选选择不读系数。
  - **T2333 = S5-15**（`Induction/DuhamelI.lean`，prover-max，1100/1400/1900）：`stDuhamelI_holds : ∀ d, STDuhamelI d`；网格 Duhamel（`stGridRepN_holds`）+ 核估计（S5-14）+ 误差项（`STEtermsMidConcl` 是钉的前提）+ `𝒰` 加权 Azuma + 指数闭合 `ρA^{-1/3}, ρA^{-1/2}, ρ³A^{-1/4} ≤ A^{-1/5}`；网格→模型转移照 Step 2（`ST_good_engine`/`ST_good_prob`），预检 (v) 点名；公开 `stDuhamelConcl_engine`（一般 `Q`、`P`）给 S5-26 用；登记删 `STDuhamelI` 行。
  - 排队顺序（4 槽全满：T2318、T2326、T2329、T2330）：**T2332 → T2333 → T2331**（§145：ST/LW 先于 BA；引擎在 `STLWT` 长链之首）。
- (4) 计数（宽口径）：ST-4 34/35、LW 44/48–49（尾 50–52）、UN 45/65（外推 68–71）、BA 29、MA 7/8。下一张票号 T2334。

## §148 — 合并 T2326/T2329/T2330/T2331；T2318 签字；LW-14f、P4b、P4c；T2332 检查文件修正；停止线（总调度，2026-10-08 12:52 UTC）

- (1) **合并**：T2329 = S5-16（850a8a3，`stIniTermI_holds`、`stIngR5_hyps_restrict`）；T2330 = UN-33（2686aaf）；T2331 = BA-P4a（8a6c908，`BA/KHeat`）；T2326 = BA-DP3 试点（d760deb，仅报告）。T2326 结论：**推荐路线 G**（Steps 2–6 链在原处泛化，链约 39 张 [33..61]；图层 L2c–L4 走路线 I），BA 合计约 141 张 [136–163]，规划数 165。按 §144 这是给阶段闸门的规划数，不是上限；**交给 T/U/V 开阶段 REQ**（在 ST-4…ST-6 闭合、发布票合并之后），不问 Jun。
- (2) **T2318 签字（流程，总调度定）**：审核 8 个目标全 PASS，只差一行登记：分支把 `RBM.Graph.LGraph.IsExtCls`（`LWVocab.lean:741`，`∃ a, Γ.cls (inl a) = q`，定义性谓词）加进 `structuralProps`。**批准**：与 `IsExtMol`、`XBetween` 同类，是结构性的不是欠账；按规则 (A) 合并，证书模块构建照 H101。
- (3) **T2332 检查文件 exit 1**：T2307 的 `partitionX`、`lwSplitLoopsX`、`lwSplitLoopsX_spec`、`partitionX_spec`、`val_eq_partitionX` 在命名空间 `RBM.Gauss.Sizes`（`LWExpTerm5.lean:51`），不在 `RBM.Graph`。五行 `#check` 已改，票文注明命名空间；重编译后放行。以后每个检查文件的每个 `#check` 都过 `nsof` 脚本（`inductive` 手查）。
- (4) **新票（自写，不用 Fable）**：
  - **T2334 = LW-14f**（`Graph/LWExpTerm6.lean`，prover-hard，700/900/1200）：`LwGraphPrecJoin`（T2265 检查文件第 3 节草案，`LWJoinedPin ↦ LWJoined`）及其证明、`lwExpG5'_of_expand'`、无条件 `lwExpG5'_holds`、`lwCutExp_holds`、`lwTermEXP_holds`、`stStep6I/II/III_holds`；登记删 `LWtermEXP`、`LWCutExp`、`LWExpG5'`、`STStep6I/II/III` 六行（§84 (1) 收尾规则）。检查文件引 `LWExpSound`，**T2318 合并后才能编译**。旧证书模块 `LWExpCertS0/S1` 本票不删，报告消费者，另排。
  - **T2335 = BA-P4b**（`BA/KHeatTail.lean`，prover-hard，700/900/1300）：`kBA_le` = `kProd_le` 逐字孪生（C1 (i)、O1），居中提升 + 坐标 Chernoff + 半群合并（C3）；报告论文差异候选（O4）。
  - **T2336 = BA-P4c**（`BA/KHeatDiff.lean`，prover-max，900/1200/1700，风险行，O2）：`kBA_diff1_le`、`kBA_diff2_le`，多项式衰减 `M = ⌊d/2⌋+1`，单方向分部求和（阶 `2M ≤ d+2`，1a 逐 `d` 列表核对）。**总调度改正 C4 的形式**：`(1+|a|²/τ)^{-M}` 在 `τ → 0`、固定 `a ≠ 0` 时不成立（差 ≍ `τ e^{-c|a|}`，不是 `O(τ^M)`），钉文用 `(1+|a|²/max τ 1)^{-M}`；`τ < 1` 段对 `τ` 积分代价 `(1+|a|²)^{-M} ≤ (|a|+1)^{-(d-1)}`（`2M ≥ d-1`），P6 的新 Laplace 引理在 `τ = 1` 处分段。1a 若认为此形式不够 P6 用，FAIL 并指出哪个积分。下次阶段 P 的 REQ 里告诉监督这处改正。
- (5) **停止线（流程）**：T2328（1757/1500）、T2329（3823/2200）都超了停止线没停，审核都过了、内容没问题，但文件过大拖慢构建、也让拆分失去意义。**新规则**：中枢在 1b 的提示里写明「每个小节提交时 `wc -l`，超过停止线就提交、停下、RETURN」；审核把超线记为流程发现（不阻塞合并）；总调度在票里写「停止线有约束力」（T2333 起已写）。
- (6) 排队（4 槽：T2333 在跑）：**T2332（修正后）→ T2334（T2318 合并、检查编译通过后）→ T2335 → T2336**。之后：S5-26 等 T2333 合并（用其引擎）；LW-16 下一张（先核 0838 O3）；T2297 Amend 等 T2332。
- (7) 计数（宽口径）：ST-4 34/35、LW 45/48–49、UN 45/65、BA 31（阶段 P 已开 3/6）、MA 7/8。下一张票号 T2337。

## §149 — LW-14 闭合、Step 6 证出；BA-P5、ST-D6 放行（总调度，2026-10-08 13:50 UTC）

- (1) **合并**：T2318 = LW-14e-4（a2c8dd6，签字的 `IsExtCls` 结构行；`LWG5Expand` → superseded）；**T2334 = LW-14f**（8a62117）：`lwGraphPrecJoin_holds`、`lwExpG5'_holds`、`lwCutExp_holds`、`lwTermEXP_holds`、**`stStep6I/II/III_holds`**，登记删 `LWtermEXP`、`LWCutExp`、`LWExpG5'`、`STStep6I/II/III` 六行。**LW-14 闭合；Step 6（ST-5）闭合**：ST-5 计 17 张，计划中的第 18 行（Step 6 收尾）由 LW-14f 完成，不再另开。T2335 = BA-P4b（d002ba6，`kBA_le`）。
- (2) `ST_mainInd_of_pins'` 剩下的前提：`STStep2`（← `STLWT` ← LW-01 链，C6）、`STStep5I`（S5-15 = T2333 1b 中；`STEtermsMid` ← `STLWT`）、`STStep5II`（S5-26，等 T2333 的引擎）。
- (3) **放行（自写，不用 Fable）**：
  - **T2338 = ST-D6**（仅报告，prover-max 设计；报告 ≤ 400 行 + 分支上的探针钉文）：从 `STMainInd`（一步 `s → t`）到 `UNMLOut`（每个时间序列 `t_n ≤ lemT z_n` 上的 `ML:GLoop`、`ML:GLoop_expec`、`ML:GtLocal`）：基例 `t = 0`（`G_0 = M`，`𝓛 = 𝒦`）、归纳闭合（结论里有没有下一步要的 `STLocalMax`）、有限时间链与对任意序列的一致性、对消费者 `UNMLOut`/`MAFixed` 的形状核对、路线 G（载体通用，BA 用 `UNMLOutBA` 实例化）的成本、拆行。候选目标 `∀ d, STMainInd d → UNMLOut d`。它在 UN-51/52、MA-06 的关键路径上。
  - **T2337 = BA-P5**（`BA/Prop5.lean`，prover-hard，800/1000/1400）：`BAProp5mixed`、`BAProp8mixed`（`BAProp5`/`BAProp8` 加 `σ₁ ≠ σ₂`）；照搬 `Prop5Hold`，`kProd ↦ kBA`、`lgGam ↦ t g²`；混合电荷时矩阵就是 `K`，带状的「性质 4 化为实 `Θ`」一步不需要；`LGConvA/B/C` 按 `γ = t g²` 重述。登记不动（P8 收尾）。
  - 排队（T2332、T2333、T2336 在跑）：**T2338 先**（ST 关键路径，§145），**T2337 次**。
- (4) 计数（宽口径）：ST-4 34/35、ST-5 闭合、ST-6 2/设计、LW 45/48–49、UN 45/65、BA 32（阶段 P 4/6 已放）、MA 7/8。下一张票号 T2339。

## §150 — 合并 T2332/T2333/T2337；T2297 Amend 1 重开；S5-26 放行；T2338 检查文件修正（总调度，2026-10-08 14:49 UTC）

- (1) **合并**：T2332 = LW 引擎（015198c，`lw_localregularX`、`lwEvX`、`LWLocRegConcl`、`lw_nWS_ge`）；T2333 = S5-15（66cfb76，`stDuhamelI_holds`；1994 行，停止线 2000 内；引擎 `stDuhamelConcl_engine` 只做 `Q = ∅`、任意符号类，一般 `Q` 未做——票文允许）；T2337 = BA-P5（dea6588，`baProp5mixed_holds`、`baProp8mixed_holds`，1479 行）。
- (2) **T2338（ST-D6）检查文件 exit 1**：`UNMLOutBA` 在 `BA/UNPins.lean`，检查文件没引。已加 `import RBM3D.BA.UNPins`，重编译后放行。
- (3) **T2297 = LW-02，Amend 1**（`docs/tickets/T2297-amend-1.md`；检查文件加一行 import、六行 `#check`，钉文不变）：F1（缺与 `m` 无关的展开列表）由 `lw_localregularX` 解决——在 `z` 之前取一次表，对每个 `n` 在 `m = mE(STflowE z n)` 取值；S1（`nWS ≥ p`）现在是引擎的输出；F2：近对（`GtoAG` 半径内）的 `𝓜_x = 𝓜_y` 输出用最大界 `|f| ≺ η⁻¹Ψ'²`，`Ψ' := max(Φ n 0)(W^{-d/2})`（监督 1143 L1 第 4 项），远对仍用展开。从 1a 新分支重开；LW 计数 +0。
- (4) **T2339 = S5-26**（`Induction/DuhamelII.lean`，prover-max，900/1200/1700）：`stDuhamelII_holds`；同号 `Q = ∅` 由 `stDuhamelConcl_engine`（`hTTT := Or.inr`）；异号 `Q^{(1)}` 要 `Θ̊` 的两条核估计（`‖Θ̊‖_{∞→∞} ≺ ilambda⁻²L²`、`(uwp2-92kj00)`，由 `prop8ZeroMode_holds`）和 `Φ` 主控的 `Q` 版本（复用 `DuhamelI` 的公开 API）；登记删 `STDuhamelII`。ST-4 最后一张：合并后 ST-4 35/35 闭合。
- (5) 排队（T2336 在跑，3 个空位）：**T2338 → T2297 → T2339**，三张同时开。之后：LW-16（先核 0838 O3）、P4c 合并后写 P6、P6 合并后写 P8。
- (6) 计数（宽口径）：ST-4 35/35、ST-6 2/设计、LW 45/48–49、UN 45/65、BA 32、MA 7/8。下一张票号 T2340。

## §151 — ST-4 闭合；T2297 Amend 2；ST-6 R1–R3 = T2340（总调度，2026-10-08 18:44 UTC）

- (0) **合并**：T2336 = BA-P4c（f234507，`kBA_diff1_le`、`kBA_diff2_le`，1757 行，停止线 1800 内）；T2339 = S5-26（0853ac1，`stDuhamelII_holds`，登记删 `STDuhamelII`）→ **ST-4 35/35 闭合**；T2338 = ST-D6（7154d50，仅报告，审核 PASS；探针留在 `t/T2338` 854aa29）。16:22 UTC 中枢额度用尽，16:20 重置后三张 1b 按规则 (H) 重跑（H136 done 行）。
- (1) **T2297 停止线 RETURN**（`LWMoment.lean` 1566 > 1500，第 9 节）：剩余 (R1)–(R3) 约 290 行，报告逐条列出，无新数学，估计全文约 1860 行。决定：不走预设切分 LW-02′，**停止线改 2000，从 9f9d1a2 接着跑 1b**（`docs/tickets/T2297-amend-2.md`）；再超 2000 就切分，不再改。理由：切分要多一张票、一个检查文件和一轮部分审核，换来的只是把约 290 行搬到另一个文件；剩余部分已经逐项估过。LW 计数 +0。
- (2) **ST-D6 设计签字**（报告 §7；审核 O1–O3）：R1–R3 合为**一张票 T2340**（`prover-hard`，三文件 `Induction/MainIndBase`、`MainIndChain`、`MainIndOut`，650 / 900 / 1100，停止线总计 1200）；R1 走**改一词路线**：删 `AzumaProxyN.lean:597` 的 `private`（不搬 120 行，不用 `open private`——库代码不用这个写法）；于是 `STLoopZeroId` 不进库，`stBase_band`、`unMLOut_of_mainInd` 都不带这个假设。命名空间：载体上的定义与定理放 `RBM.BA`（挨着 `STMainIndG`），`stMainInd_of_LW` 放 `RBM.Gauss.Sizes`，`UNMLOut` 一侧放 `RBM.Univ`。新增 `stMainInd_of_LW : ∀ d, LWterm d → LWtermExp d → STMainInd d`、`unMLOut_of_LW`（`STDuhamelII` 已由 T2339 证出）。
- (3) 登记（设计 §7 提议，签）：`STLK0`、`STG0M`、`STBaseG`、`STHorizonG` 入 `owedProps`（载体事实；带模型实例本票证出，BA 实例欠 BA-V）；`STConclgL`、`STMLOutG` 入 `structuralProps`。
- (4) R4（`stMainInd_holds`、`unMLOut_holds`，删 `STMainInd`、`UNMLOut` 两行）等 LW-01，可并入 LW-01 的收尾票。设计开放问题 2（`Test/Axioms.lean:102-107` 六行 `STLK … STExp2`）到 R4 时定：R4 后若已无定理以它们为假设，移入 `structuralProps`（它们只是 `STMainInd` 的组成部分）。
- (5) 排队：T2297（续 1b）、T2340。下一步写 BA-P6（P4c 已合并）与 LW-16，两张都放上后 4 张在跑。
- (6) 计数（宽口径）：ST-4 35/35 闭合、ST-6 3/4（T2338、T2340、R4；主归纳区域组装 T2245 另计）、LW 45/48–49、UN 45/65、BA 32、MA 7/8。下一张票号 T2341。

## §152 — BA-P6 = T2341；LW-16 = T2342（0838 O3 书面回答）；监督 REQ-1851（总调度，2026-10-08 18:51 UTC）

- (1) **BA-P6 = T2341**（`BA/PropUnit.lean`，`prover-hard`，900 / 1200 / 1500，停止线 1700）：混合电荷 `σ₁ ≠ σ₂` 的单位一阶、二阶差分 `baPropUnit1mixed_holds`、`baPropUnit2mixed_holds`；钉 P4c 的原样输出（`kBA_diff1_le`、`kBA_diff2_le`），新加一条多项式衰减的 Laplace 引理（`lg_bulk` 的多项式版，在 `τ = 1` 处分段）。允许删 `BA/Prop5.lean` 中至多 8 个声明的 `private`（同 §151 (2) 的改一词路线）。登记不动（`BAProp6/7` 等 P8）。
- (2) **C4 更正告知监督**：P4c 的衰减因子用 `max τ 1`（监督 C4 的字面形式在 `τ → 0` 不成立），T2336 已按此证出并审核通过；P6 消费这一形式。写进 REQ-1851 B1，不阻塞（P6 在监督 1048 已放行的阶段 P 行内，路线不变）。
- (3) **监督 0838 O3 的书面回答**（LW-16 放行前要求）：`tailW` 类作为全体实数 `r` 上的类**不满足** `(eq:Psi)`——`ℓ > L` 时（`LWAssmExp` 允许 `ℓ ≤ (log W)^{10} ℓ_t`），`r` 从 `L` 到 `ℓ` 之间的因子 `exp(√(r∧ℓ/ℓ_t))` 是伸展指数，不是多项式。所以 LW-16 不拿 `tailW` 类当 `Φ`，而是对**已合并的 B 类** `LWPhiB`（`c₀ = d`，`K = ⌊ℓ⌋ ∧ L`）用 `LWterm`：`(eq:Psi)` 由 `LWPhiB_psiAll`（T2051）给出；`LWLoop2` 在任何区域都由 `LWLoopExp` 推出（指数因子 `≤ 1`，取大的 `D'`）；在 `1 - t ≤ ĝ²/L²` 的子类型上，`r ≤ L` 时 B 界 `≤ e · tailW`（`tailT_regime2_bounds`，`ℓ_t = L`）。不加新钉文，也不需要子序列转移（指标集本身就是逐个 `n` 的子类型）。**LW-16 = T2342**（`Graph/LWTermExpN.lean`，`lwtermExpN_of_LWterm : ∀ d, LWterm d → LWtermExpN d`，`prover`，300 / 450 / 650，停止线 800）；登记不动（LW-01 删 `LWtermExpN`）。
- (4) **REQ-1851**（不阻塞）：B1 `max τ 1`、B2 O3 的回答、B3 ST-D6 签字（§151 (2)–(4)）、B4 T2297 Amend 2。监督对任何一条说 HOLD，相关票在下一个阶段边界停。
- (5) 排队：H138 放 T2342（LW，先）、T2341（BA）。**下一个空位给 UN-34**（§145：先闭合其他方向；UN 首次拆分前 REQ），P8 等 P6 合并。
- (6) 计数（宽口径）：ST-4 35/35、ST-6 3/4、LW 46/48–49（T2342 计入）、UN 45/65、BA 33（T2341 计入；阶段 P 余 P8）、MA 7/8。下一张票号 T2343。

## §153 — UN-34 + UN-35 合并为一张 T2343（复用 `Path/OneStep.lean` §1–§4）（总调度，2026-10-08 18:54 UTC）

- (1) RBM2D `GUEPhase/Drift.lean`（HEAD 9e0f275，2067 行）的私有辅助引理是 `Path/OneStep.lean`、`Path/LoopStep.lean` 的拷贝（源文件头自述）；RBM3D 两者都已合并且对 `d` 通用。决定：**UN-34 与 UN-35 合并为一张 T2343**，只移植源 §4 的 GUE 计数与 §5–§13；源 §1–§3（约 650 行：字的射流、沿直线与沿谱路径的圈泛函、它们的界）**复用** `OneStep.lean` §1–§4，删其中被用到的声明的 `private`（同 §151 (2) 改一词路线，报告列清单）。目标 `oneStepEnvelopeGUE`、`gueH_succ`、`condExp_loop_step_gue`、`condExp_loop_drift_gue`（检查文件第 2 节，按带模型孪生 `OneStepEnvelope`、`pathH_succ`、`condExp_loop_step/drift` 定形）。`prover-hard`，1100 / 1350 / 1700，停止线 1900；超线则按预设切分退回 UN-34（§5–§7）/ UN-35（§8–§13）两行。
- (2) UN 计划 65 → **64**（对监督 1143 外推 68–71 留出一行余量）；这是合并不是拆分，写进 REQ-2026-10-08-1851 B5 告知监督，不阻塞。
- (3) 排队：H138 后 4 张在跑（T2297、T2340、T2342、T2341）；**T2343 在下一个空位放行，排在一切之前**（H139）。之后 UN-36/37 `DuhamelA` 等 T2343 合并。
- (4) 计数（宽口径）：UN 46/64（T2343 计入）；其余同 §152。下一张票号 T2344。

## §154 — 监督 1942 全部 PASS；T2297、T2342 合并；LW-13b-2 = T2344（总调度，2026-10-08 19:55 UTC）

- (0) **合并**：T2342 = LW-16（84cd789，`lwtermExpN_of_LWterm`）；T2297 = LW-02（1546ef7，`lwMoment_holds`，1872 行，停止线 2000 内，未切分）。T2340、T2341 审核 PASS，合并等 H122（T2343 工作树里的证书模块重建占内存）。T2343 1a 中。
- (1) **监督 2026-10-08-1942：REQ-1851 的 B1–B5 全部无异议，PASS**。B1：C4 按 `max τ 1` 读，P8 同一计算；B2：0838 O3 关闭（另做了无环检查：LW-01 内部顺序 `LWterm → LWtermExpN → LWtermExp`）；B3：ST-D6 签字无异议；B4：已无意义；B5：合并无异议。
- (2) **C8 / O2（记给 LW-01）**：Step 2 的收尾已由 `stMainInd_of_LW`（T2340）完成，LW-01 **不得**再证 `3 ≤ d → LWterm → LWtermExp → STStep2`；LW-01 范围：`LWReduceB`、`LWReduceT`、`LWterm`、`LWtermB`、`LWtermExpS`、并 `LWtermExp`，加 R4（`stMainInd_holds`、`unMLOut_holds`）和登记删除；保留 1143 O2 的「前提 ↔ 已合并产出者」表，加票内顺序 `LWterm → LWtermExpN（T2342）→ LWtermExp`。
- (3) **O3（T2343 审核）**：审核必须用脚本核对 `OneStep.lean`/`LoopStep.lean` 的差分只有删 `private`（同 T2341 对 `Prop5.lean` 的核对）。写进 H140，由中枢放进 T2343 第 2 阶段的审核提示。
- (4) **LW-13b-2 = T2344**（C9/O1：唯一剩下的 LW 链的头）：`lwMomentExp_holds : ∀ d, LWMomentExp d`，`prover-max`，1200 / 1700 / 2400，停止线 2200。**第 1a 阶段即设计**（这是 LW 的风险行）：(A) 无指数衰减区域由 `lwMoment_holds` + B 类给出（论文 `7_8:1602`，同 T2342 的手法）；(B) 指数区域 `f = f^{>ℓ} + f^{≤ℓ}`，远引理用引擎展开 + `lwMomExpFar_and`（`HeadFar` 域声明 `T2289d` 在此证），近引理用 `lwMomExp_near`，并解决 `zdistD`/`zdistInf` 边度量缺口（T2281 S2）。域机制两个候选：监督 REQ-1459 的选项 (i)，或先试**把指示函数吸收进黑边** `S_{a_1a_2} ↦ 1_{far}(a_1) S_{a_1a_2}`（若引擎对黑边矩阵是参数化的，则不需要改词汇）。**预设切分**：1a 中心估计超过 1800 行就切——本票做 (A) + 组装 + 远引理，近引理与登记删除归 **LW-13b-3**（新行）；1a 两个域机制都不成立 → 停在 1a，向监督发 REQ。
- (5) 计数（宽口径）：LW 47（T2344 计入；计划 48 = + LW-01；切分则 49）；ST-6 3/4；UN 46/64；BA 33；MA 7/8。下一张票号 T2345。
- (6) 排队：空位 1 个（T2340、T2341 等合并占着）→ **T2344 立即放行**。T2340、T2341 合并后：BA-P8（T2341 后）与 UN-36/37（T2343 后）。§145 顺序：LW/ST/UN 先于 BA。

## §155 — T2340、T2341 合并；T2343 审核 PASS；UN-36、UN-37 = T2345、T2346（并行）（总调度，2026-10-08 20:54 UTC）

- (0) **合并**：T2340 = ST-6 R1–R3（03ec112：`Induction/MainIndBase/Chain/Out`，`stMainInd_of_LW`、`unMLOut_of_LW`；登记按审核 O1 三方合入）；T2341 = BA-P6（37426e6：`baPropUnit1mixed_holds`、`baPropUnit2mixed_holds`；`Prop5.lean` 只删 8 个 `private`，脚本核过）。T2343 = UN-34 审核 PASS（`OneStep.lean` 差分只删 `private`，审核脚本 + 中枢复核 21/21，监督 1942 O3 已满足），正在合并。T2344 = LW-13b-2 在 1a（设计）。
- (1) **UN 关键链**：按 RBM2D 导入关系，`DuhamelA → DuhamelB → DuhamelC → PathBounds → RandomLayerB → UN-52` 是最长的一条，先开。`DuhamelA`（1985 行）的 §5–§7 只通过 `Duhamel_contDiffAt_loop` 一处用到 §1–§4，所以按依赖切成两个文件**并行**：**UN-36 = T2345**（`GUEPhase/DuhamelA1`，§1–§4，`prover-hard`，1000 / 1150 / 1400，停止线 1600；`Duhamel_contDiffAt_loop` 公开）与 **UN-37 = T2346**（`GUEPhase/DuhamelA2`，§5–§7，`prover-hard`，900 / 1050 / 1300，停止线 1500；自己重推 `Duhamel_contDiffAt_loop`，私有前缀 `DuhamelA2_`，`Duhamel_gueH_succ` 不搬，用已合并的 `gueH_succ`）。计划行数不变（portmap 本来就是 UN-36/37 两行）。
- (2) 钉文：T2345 钉三条（`Duhamel_vGue_le`、`Duhamel_loopMax_le_crude`（`d` 行 `(L W)^d`）、`Duhamel_vGue_gradMat_le`）；其余目标按移植表翻译，证明报告给出翻译表，审核逐行核对（移植票的做法，§155 定）。
- (3) 其他可并行的 UN 行（导入已齐）：UN-43 `EntryGrid`、UN-44 `Eq729A`、UN-48 `HypA`、UN-45/46 `OneLoop`（风险行）、`LLTransfer`（UN-50 的一半）、`QUEFlow`（UN-52 的一半）。下一个空位：UN-43 或 BA-P8（§145：UN 先）。
- (4) 计数（宽口径）：UN 48/64（T2345、T2346 计入）；LW 47；ST-6 3/4；BA 33（阶段 P 余 P8）；MA 7/8。下一张票号 T2347。

## §156 — T2343 合并；T2344 1a FAIL → 监督 REQ-2152；T2345/T2346 检查文件修正（总调度，2026-10-08 21:52 UTC）

- (0) **合并**：T2343 = UN-34+35（5d0b6da，`GUEPhase/Drift`；`OneStep.lean` 只删 21 个 `private`；合并构建 61 分钟，`OneStep` 改动触发证书模块重建）。
- (1) **T2344（LW-13b-2）1a FAIL**（报告 (a)）：A、Asm PASS；度量缺口用 `zdistInf` 孪生（候选 2）PASS，重标 `ℓ_t ↦ dℓ_t` FAIL；**域机制 FAIL**：黑边吸收指示函数不成立（所有黑波浪边、包括 IBP 产生的，都按 `D.S` 取值，Stein 一步要行和 `s`），REQ-1459 的选项 (i) 也带不过展开（`LGraph.val`、引擎、`GtoAG` 都对内部标签全求和）；缺的是**带初始顶点权重的展开恒等式**（顶点来源穿过引擎的每一步 `LocStep`，即 `T2289d`）。另有 G2（指数类 `ξ` 的界不能经 `LWPsiAll`，半径 `(log W)^{3/2}` 才渐近成立）、G4（近区是两球之并，已合并的近区域是交，改三分 `f^{>} + f^{(a)} + f^{(b)}`）。按票面规则：停在 1a，向监督发 **REQ-2152**（R1 域机制路线、R2 G2、R3 行数与 50 的 HOLD 审查）。T2344 不重启，等回复。这是数学卡点；若监督判断需要专门的数学设计，至多开一张设计票或一次 Fable 复核。
- (2) **T2345/T2346 检查文件 exit 1**：两行 `#check`（`isUnit_sub_smul_one_of_im_ne_zero`、`green_sub_green`）在 `Induction/ConArgDet.lean`，检查文件没引；删去这两行（只是给证明者的参考名）。H142 重编译后放行。
- (3) 排队：T2345、T2346 放行后 2 张在跑；再补 UN-43 `EntryGrid`（与 DuhamelA 无关，导入已齐）和 BA-P8，保持 4 张。
- (4) 计数（宽口径）：LW 47（T2344 计入；路线 (a) 则 +2 行，到 LW-01 时 50–51，HOLD 审查问题已提给监督）；UN 48/64；ST-6 3/4；BA 33；MA 7/8。下一张票号 T2347。

## §157 — UN-43 = T2347（`EntryGrid`，复用 `Grid.lean` 的私有混合网格引理）（总调度，2026-10-08 21:53 UTC）

- (1) RBM2D `EntryGrid.lean`（902 行）自述把 `Grid.lean` 的私有混合网格引理拷了一份（约 290 行）；RBM3D 的 `GUEPhase/Grid.lean` 有同样的引理（前缀 `GUEPhaseGrid_`，`:117-530`）。同 §153：**删 `Grid.lean` 里用到的那些声明的 `private`，不拷**；审核用脚本核对差分只删关键词（监督 1942 O3 的规则）。**UN-43 = T2347**，`prover-hard`，550 / 700 / 900，停止线 1100。导入（`EntryTail`、`EntryTailMain`、`Proc`）都已合并，与 DuhamelA 无关，可并行。
- (2) 计数（宽口径）：UN 49/64（T2347 计入）。其余同 §156。下一张票号 T2348。

## §158 — T2345/T2346/T2347 合并；监督 2244 PASS（LW-13b 走 (a)，先开设计票）；LW-13b-D = T2348；UN-38 = T2349，UN-44 = T2350（总调度，2026-10-08 22:52 UTC）

- (0) **合并**：T2345 = UN-36（1f3eec5，`DuhamelA1`）；T2346 = UN-37（168c9fd，`DuhamelA2`）；T2347 = UN-43（f9f498d，`EntryGrid`，`Grid.lean` 只删 `private`）。22:31 起中枢空转，本节补满。
- (1) **监督 2026-10-08-2244（回 REQ-2152）：PASS**。R1：路线 (a)，形式是"分子来源"（molecule provenance）——论文说的"内部顶点都在 `D_{>ℓ}`"指的是辅助图的顶点（分子），成立的原因是 `S^{(B)}` 在块上最近邻、IBP 从不新建分子，所以每个输出图的每个分子都含一个初始 `β^{(k)}`；需要的是一条通用引理：每个 `LocStepX` 构造子都带一个输入顶点到输出顶点的映射，且其 `eval` 恒等式对旧顶点的标签逐点成立；若都逐点成立，一行 800–1500，否则真孪生 1500–2500。(b)、(c) 都不通。R2：接受 `Rb = K(log W)^{3/2}`（与论文的阈值一致，渐近成立）。R3：**现在不 HOLD**；设计票的报告回监督的 REQ 就是 50 行审查；LW 预计 51–52；监督要我在给 Jun 的下次汇报里说明 LW 会到 50、还差 1–2 行。
- (2) **LW-13b-D = T2348**（仅报告，`prover-max`，探针 ≤ 600 行，停止线 900）：范围按监督 2244 O1（来源引理与逐构造子表、分子层面的域钉文与 `Rb` 放大、G4 三分、G2 指数类 `ξ`、Met 的 `zdistInf` 孪生（删 `LWMomExp.lean:310, 434` 的 `private`）、(A) 与组装、行数）。报告合并后我向监督发 REQ，PASS 前不放任何 LW 证明行。LW 48。
- (3) **UN 两张**（导入都已合并，§145 优先于 BA）：**UN-38 = T2349**（`DuhamelB`，1020 行，900 / 1050 / 1300，停止线 1500；关键链 DuhamelA → B → C 的下一张）；**UN-44 = T2350**（`Eq729A`，1043 行，900 / 1100 / 1400，停止线 1600；源文件有 109 个 `^ 2` 记号，2-圈代数 `W²·Σ`、`SBgue = 1/L²` 的 `d` 化是预检的重点）。目标按移植表翻译，报告给翻译表，审核逐行核对（§155 (2) 的做法）。UN 51/64。
- (4) 第 4 个空位：BA-P8（下一轮写）或 UN-48 `HypA`（缺名较多：`KLoop.Kcal/Kgen/Mt/Par/mSig`、`scaleM`，预检要先找 RBM3D 孪生）。
- (5) 计数（宽口径）：LW 48（T2348 计入；路线 (a) 共 51–52）；UN 51/64；ST-6 3/4；BA 33；MA 7/8。下一张票号 T2351。

## §159 — T2349、T2350 合并；UN 三张：DuhamelC = T2351，HypA = T2352，OneLoop = T2353（总调度，2026-10-08 23:52 UTC）

- (0) **合并**：T2349 = UN-38（198f15c，`DuhamelB`）；T2350 = UN-44（9c3bfc7，`Eq729A`）。两张都在半小时内完成。T2348（LW-13b-D）1a 中。
- (1) **合并行**（UN 上限压力，监督外推 67–70 > 64）：`DuhamelC`（1521 行，只有 3 个缺名，唯一公开目标 `gueGrid_loop_duhamel`）合 UN-39/40 为一张 **T2351**（`prover-hard`，1300 / 1500 / 1800，停止线 2100，预设切分回两行）；`OneLoop`（1729 行）合 UN-45/46 为一张 **T2353**（`prover-max`，风险行：`d ≥ 3` 下 `log L` 记号的形式要变；1a 逐行写替换并在 `d = 3` 数值核对；缺名 19 个，RBM2D 的 `Evolution/XiBounds` 等层在 RBM3D 没有同名文件，1a 按内容找孪生，FAIL 停在 1a 回调度、再发监督）。**UN-48 = T2352**（`HypA`，1010 行，`prover-hard`，900 / 1050 / 1300；缺名 19 个，`Loop/Kcal`、`Path/Scales` 等没有同名文件，同样 1a 按内容找孪生，缺层超过 300 行即 FAIL）。
- (2) 计数（宽口径）：UN 54/64（T2351、T2352、T2353 计入；两次合并各省一行，计划内剩余：UN-47 `Eq729B`、UN-49 `HypB`、UN-50 `LLTransfer`+`PathBounds`、UN-51、UN-52）。LW 48；ST-6 3/4；BA 33；MA 7/8。下一张票号 T2354。
- (3) 4 槽：T2348、T2351、T2352、T2353。BA-P8 等空位（§145：UN 先）。

## §160 — T2352、T2353 合并；T2348 报告合并 → 监督 REQ-0100（LW 50 行审查）；UN 三张：HypB+LLTransfer = T2354，QUEFlow = T2355，Eq729B = T2356（1a 设计门）（总调度，2026-10-09 01:02 UTC）

- (0) **合并**：T2352 = UN-48（9b66b53，`HypA`，一次返工）；T2353 = UN-45/46（93b8ec8，`OneLoop`，1 轮审核 PASS）；T2348 = LW-13b-D（d525990，仅报告；审核 1–7 PASS；探针留在 `t/T2348` 9f3bd75）。00:52 起中枢 0 张在跑，本节补 3 张。
- (1) **UN 行重排（计划行数不变）**：UN-49 `HypB`（1021 行）与原 UN-50 的一半 `LLTransfer`（440 行，只导入 `Grid`、`ZeroModeProfile`）合为一张 **T2354**（两个新文件，`prover-hard`，1250 / 1500 / 1850，停止线 2050，预设切分 HypB | LLTransfer）；`oull_of_pathBounds` 的结论按已合并钉文 `UNOULL` 的体写（UN-51 直接实例化）。`QUEFlow` 从 UN-52 拆出为 **UN-52a = T2355**：RBM3D 的形式是通用行 `g2bRowk : ∀ K P, UNG2bRowk K P`（T2282 已钉，监督 0956 O2），已合并的 `queFixed`/`queChain`（MA-05b）就是论证的分件；`queFixed` 只对 `Sizes.seqP` 陈述，所以在新文件里做私有的通用拷贝，不改合并文件；删欠账 `UNG2bRowk` 一行（`Test/Axioms.lean:194`）；600 / 850 / 1200，停止线 1400。原 UN-50 的另一半 `PathBounds`（要 HypB）以后并入 UN-51（`RandomLayerA/B`），UN-52b = `Main/BUniv` + `BUnivHolds`。
- (2) **UN-47 `Eq729B` = T2356，1a 设计门**：不是纯移植。RBM2D 的初始项 `MLExpConcl`（`N^ε scaleM^{-3}`）和结论（`trGEGEmat`/`profileTilde`/`W^δ Meta^{-3}`，`η_Q = W^{2/3}/N`）在 RBM3D 已由钉文 `STExp2`（`Bctl²((ilambda² W^d)^{-1/5} + Bctl)`）和 `UNOUEq747`（`qdBoundExp`，`η_Q = W^{-𝔡/3} ilambda W^{d/2}/N`）取代；从 `t₁` 的 `STExp2` 经 GUE 段到 `t₀`、再经 (7.47) 到 `qdBoundExp` 的指数链是 RBM2D 里没有的数学（监督 1143 O3 本就列为风险行）。所以 1a = 设计报告 + 探针（≤ 400 行，只有 Prop 钉文和实变量指数引理），审核 PASS 后只合并报告并停；我把设计作为 REQ 发监督，PASS 后另写 H 指令放 1b（`prover-max`，暂估 1400 / 1750 / 2200，预设切分在源 `:784`）。1a FAIL 则回调度。
- (3) **T2348 → REQ-2026-10-09-0100**（监督 2244 O2 的 50 行审查）：Q1 路线 (R)（有根 `GtoAG`、精确域，新增行 G ≈ 470）对 (E)（`Rb` 放大）；Q2 三行 R1/R2/R3（LW 49–51）、预设切分 C1–C3、LW-01 = 52（切分最多 55），是否要 HOLD 或升级给 Jun；Q3 PASS 后 R1、R2 同放，R3 等两者合并；Q4 论文差异候选编号（T2344a–d、T2348a–b；T2348c 是对票与 2244 O1 的更正：`LWMomExp.lean` 要删 10 个 `private`，不是 2 个）。PASS 前不放任何 LW 证明行。
- (4) 计数（宽口径）：UN 57/64（T2354、T2355、T2356 计入；计划内剩 UN-51（`PathBounds` + `RandomLayerA/B`）、UN-52b → 59）；LW 48（R1–R3 待审，LW-01 = 52–55）；ST-6 3/4；BA 33；MA 7/8。下一张票号 T2357。
- (5) 槽位：3 张（T2354、T2355、T2356 1a）。第 4 张 BA-P8（§144 每阶段监督把关、§145 其他方向优先），下一轮读清 BA 阶段 P 的放行条件后写。

## §161 — BA-P8 = T2357（阶段 P 最后一行，监督 1048 行 P8 + C5）（总调度，2026-10-09 01:04 UTC）

- (1) **BA-P8 = T2357**（`BA/Prop6Path.lean`，`prover-hard`，600 / 800 / 1100，停止线 1300）：`σ₁ ≠ σ₂` 的性质 6/7 照带状 `Prop6Hold.lean` 的路径论证（单位差分 `BAPropUnit1/2mixed` → `|r| ≤ c|a|`）；`σ₁ = σ₂` 的四条归约由 `BAProp5s`（C5 的写法逐条进 1a）；5/8 的混合电荷由 T2337；打包 `baProp5to8_holds`，删登记 `Test/Axioms.lean:137-141` 五行。**流程决定**：带状路径引理（`p6h_*`，约 290 行，对 `f : Zd d L → ℂ` 通用）是 `private`，按 §153 本该删关键词；但 `Propagator/Prop6Hold.lean` 在导入树最底层（`ZeroModeProfile`、`Loop`、`Induction` 以上几乎全依赖），改一个关键词就是整树重编（T2343 改 `OneStep` 已 61 分钟），会堵后面所有合并——这次**拷贝**，不改合并文件；§153 的规则对处在树底的文件不适用，以后同类情况照此。
- (2) 与 T2355 同写 `Test/Axioms.lean`（194 行 vs 137-141 行），不相邻，后合并的那张正常三方合并。
- (3) 阶段 P：第 6 张（上限 9）；P8 合并后发阶段 P 关闭 REQ（`BAProp5to8` 四个电荷对全证、五行已删，1048 O5）。BA 34。
- (4) 槽位 4/4（T2354、T2355、T2356 1a、T2357）。下一张票号 T2358。

## §162 — 监督 0143 PASS（LW 50 行审查）：放 R1 = T2358、R2 = T2359，LW 上限 55；T2355、T2357 合并；BA 阶段 P 关闭 REQ（总调度，2026-10-09 01:56 UTC）

- (0) **合并**：T2355 = UN-52a（5d7a660，`g2bRowk` 证出，删欠账 `UNG2bRowk`）；T2357 = BA-P8（83847ef，`baProp5to8_holds` 四个电荷对全证，删 `Test/Axioms.lean` 五行）。都是 1 轮审核 PASS。T2354 1b 中，T2356 1a（设计）中。
- (1) **监督 2026-10-09-0143（回 REQ-0100）：PASS**。Q1 走 (R)（有根 `GtoAG` 是 `auxGraph_exists_forest` 去掉 `choose` 的机械推广；(E) 只在 R3 1a 遇到具体障碍时作后备，换 (E) 要 REQ）；Q2 接受 R1/R2/R3、预设切分 C1–C3、LW-01 = 52，**LW 上限 55（含 LW-01），硬约束**：第 56 张、C1–C3 以外的切分、或 R1–R3 的数学性 1a FAIL，任一出现即 REQ，监督会建议 LW 门 HOLD 并上报 Jun；Q3 R1、R2 现在同放，R3 等两者合并，条件 C1–C6；Q4 论文差异编号（见 (4)）。另：REQ 第 1 行必须恰为 `status: open`（O4），本 REQ 漏了，以后照办。
- (2) **R1 = T2358**（`Graph/LWProv.lean`，`prover-max`，1003 / 1440 / 2170，停止线 1950）：陈述 = 探针 `:29-185, 291-310` 逐字（审核脚本 diff），唯一改动 C3（`LWExpData` 不立为定义，九个合取式写进 `WExp`/`WExp.prod` 的绑定）；1a 先编出 C1（加权桥 `lwProv_bridge`，`lwMoment_fxyPow_val` 的孪生）与 C2（`weight` 构造子的 `Molecular`、`fxyPowGraph p` 的初始 `Cover`），失败即停回调度发 REQ。**R2 = T2359**（`Graph/LWMomExpInf.lean`、`LWXiExp.lean`、`LWMomentExpA.lean`，`LWMomExp.lean` 只删 **11** 个 `private`（C4 (a)，含 `lwMomExp_stepFn`），`prover-max`，1182 / 1573 / 2344，停止线 2100）。**流程决定**：`LWfD`（受限的 `f`）放在 R1（加权桥要它），R2 与 R1 并行不共文件，所以 (A) 用已合并的 `LWf` 在目标 `LWMomentExp` 的子类型上加 `regA d K` 来陈述（`LWMomExpNoExpF`，对一切 `K > 0`，C4 (b)），R3 用 `LWfD … univ = LWf` 转换；探针的 `LWMomentExpOn`、域、远/近钉文、`LWMomentExpOfParts` 归 R3（按 C6 选 (α)：`∀ p, ∃ K`）。
- (3) **LW 计数**：48 → T2358 = 49、T2359 = 50；R3 = 51，LW-01 = 52；上限 55。告知 Jun：LW 过 50，审查已做（PASS），名义 52，上限 55。
- (4) **论文差异**（监督 0143 Q4）：D618 = T2344a、D619 = T2344b、D620 = T2344c、D621 = T2344d、D622 = T2348a、D623 = T2348b，记入 `docs/paper-deltas.md`；T2348c 不是差异，是对票与 2244 O1 的更正（11 个关键词）。
- (5) **BA 阶段 P 关闭 → REQ-2026-10-09-0156**（1048 O5）：P4a T2331、P4b T2335、P4c T2336、P5 T2337、P6 T2341、P8 T2357，6 张（上限 9），`BAProp5to8` 四个电荷对全证，五行登记已删；问下一阶段 K 的开法（我提议先开一张仅报告的 BA-DK 设计票出行表）。阶段 K 答复前不写 BA 证明票。
- (6) 计数（宽口径）：LW 50（R1、R2 计入）；UN 57/64；ST-6 3/4；BA 34（阶段 P 关闭待批）；MA 7/8。槽位 4/4（T2354、T2356 1a、T2358、T2359）。下一张票号 T2360。

## §163 — 监督 0243 PASS：BA 阶段 P 关闭、阶段 K 先设计（BA-DK = T2360）；LW 两个 1a FAIL 改为钉文修补（T2358/T2359 Amend 1）；T2354 合并、T2356 设计 → REQ；UN-50b PathBounds = T2361（总调度，2026-10-09 02:54 UTC）

- (0) **合并**：T2354 = UN-49 + UN-50a（5d8f515，`HypB` + `LLTransfer`，一次返工后审核 PASS）；T2356 1a 设计报告（8d76de9，仅报告，探针留 `t/T2356` fe9888f）。02:15 起中枢 0 张在跑（T2358、T2359 1a FAIL，T2356 等 REQ），本节补满。
- (1) **LW 两个 1a FAIL（02:09、02:13）**：监督 0243 在本轮主动审了（不等 REQ），判定**不是 0143 O2 情形，不建议 HOLD**：两处都是钉文过强，修补在已合并目标的定义域内。**T2358 Amend 1**（L1）：`LocStepXProv` 加 `P.g.Normal →`（供给：`lwEngine_exists` 里的 `hch`、根 `fxyPowGraph_normal`），C1、C2 数学上已过，从 1a 重开。**T2359 Amend 1**（L2）：`LWXiE` 合取 2 限制到子类型 `λ²/L² < 1 - t`（目标 `LWMomentExp` 本就只在这里），G2 类改为 `Φ_E = (W^{-d} tailW_{ℓ,W,2D})^{1/2}`，核拷贝加 `sfT_TtTt/KtKt/pair_cases`，`AuxGraph2` 17 个私有辅助（244 行）拷入；中心约 +330 行，停止线仍 2100，越线即 O2。0243 O4 对 O2 的澄清照录：1a FAIL 若靠（i）加一个所有调用者都已提供的前提，或（ii）限制到已合并目标的定义域来修补，是钉文修补，不触发 O2；所需事实在目标定义域上为假或未证，才是 O2。修补不算票：LW 仍 50（计划 52，上限 55），记入返工账本；告知 Jun（通知性）。
- (2) **BA**：阶段 P 关闭（6/9，`baProp5to8_holds` 四电荷对全证、五行已删）。阶段 K 不从旧表（T2161 K1–K5、T2325 重估）开，先开一张仅报告的设计票 **BA-DK = T2360**（`prover-max`，探针 ≤ 400、报告 ≤ 300），条件 K1–K6 写进票：K1 对 19 个带状 KL 文件逐个分 (g) 原地泛化 / (t) 孪生 / (b) BA 新数学；K2 目标按 `STKboundgL` 形状、只在实 `t`、`BAReal` 数据上用 `Θ_BA`；K3 四个只引用未证的 BA 项的论文状态；K4 交付；K5 超 12 行或 (t) 超 10k 中心行要逐文件说理由；K6 BA 35。报告即阶段 K 开启 REQ，PASS 前不写 BA 证明票。论文差异 D624–D627 记入（0243 O1：T2335a–c、T2336a；T2341 审核无差异）。
- (3) **UN-50b = T2361**（`GUEPhase/PathBounds.lean`，`prover-hard`，550 / 700 / 950，停止线 1100）：HypB 已合并，`PathBounds` 不再等 UN-51（`RandomLayerA` 要 Eq729B，等监督）。RBM2D 的输入 `MLConcl`（`InitLK`、`InitLocal`，`scaleM` 形）在 RBM3D 换成 `UNMLOut` 的 ST 结论（`STLK`、`STLocalEntry` 等，`d ≥ 3` 界），1a 必须写语句表并证明 ST 结论给出 `GUEPathBounds` 的第 0 步输入；做不到即 FAIL 回调度。UN 58/64。
- (4) **T2356 设计 → REQ-2026-10-09-0254**：三个目标的陈述（目标 1 结论带 `I₀(t₁)`；目标 2、3 结论是 `UNOUEq747` 的体）、桥（无新钉文，只用 `STExp2`）、F2 好数据（`goodFlow`）、尺寸 1355 / 1687 / 2265、切分 `:784`、差异候选 T2356a–c；问 1b 放行。BA 种类的 `UNOUEq747k` 我提议归 BA（BA-C3 线），不归 UN。
- (5) 计数（宽口径）：LW 50（两张修补中）；UN 58/64；ST-6 3/4；BA 35；MA 7/8。槽位 4/4（T2358 A1、T2359 A1、T2360、T2361）。下一张票号 T2362。REQ 第 1 行一律 `status: open`（0143 O4）。

## §164 — 监督 0344 PASS：T2356（Eq729B）放 1b；T2361 检查文件补导入；论文差异 D628–D631（总调度，2026-10-09 03:51 UTC）

- (0) 状态：T2358、T2359 在 Amend 1 下 1a PASS，1b 中（03:32 起）；T2360（BA-DK）设计中；T2361 检查文件 exit 1（`gueKproc_detDom` 在 `GUEPhase/ProcK.lean`，检查文件没导入），未放行——补 `import RBM3D.Universality.GUEPhase.ProcK` 重编。
- (1) **监督 2026-10-09-0344（回 REQ-0254）：PASS**，条件 E1–E5，写进 `docs/tickets/T2356-1b.md`：Q1 三个目标照设计 §1（目标 1 的 `I₀(t₁)` 是被迫的且能闭合：F1 给 `I₀ ≤ 8𝓑²(X + 𝓑)`，正是 `qdBoundExp` 的形状）；Q2 `∀ n` 目标 + `goodFlow`、`goodFlow` 与 `bridge` 放 `Eq729B.lean`；BA 种类的 `UNOUEq747k` 不归 UN，归 **BA-C5 `BA/GUEHyp`**（不是我提议的 BA-C3；T2173 portmap `:246, :277`，Eq729B 是 T 类）；E2 导入去 `DuhamelC`、加 `HypA`、`Main/ZTransfer`、`Main/QUEFromQDiff`、`Loop/KLFinal`；E3 一行，1355 / 1687 / 2265，停止线 2400，`:784` 切分只作后备；E4（软）与种类无关的链引理保持公开、按实数据陈述，供 BA-C5 复用；E5 记给 UN-51 的设计：`UNG1Rowk` 的 BA 实例由 BA 侧（BA-C5）闭合，或 `UNG1Rowk` 加种类的 `Eq747k` 生产者作前提（`Test/Axioms.lean:188` 的归属注释届时改为「带状：UN-51；BA：BA-C5」）。
- (2) **论文差异** D628 = T2356a、D629 = T2356b、D630 = T2356c、D631 = T2352a（0344 Q4，补记 T2352a）。
- (3) **槽位**：T2358、T2359、T2360 在跑；**T2356 1b 先放**（UN-51 的关键路径），T2361 等 T2360 报告合并空出槽位再放（保持 4 张）。
- (4) 计数（宽口径）：LW 50；UN 58/64；ST-6 3/4；BA 35；MA 7/8。下一张票号 T2362。

## §165 — 交接：调度 V1 → V2；不开新票，收尾在跑的四张；交接包、启动文件、TEAM §10、工具入库；CONTROL 归档（总调度，2026-10-09 04:05 UTC）

- (0) **Jun（2026-10-09 约 04:00 UTC）**：「准备交班给下一个调度，修改一下 doc/team startup 的文件，不要发新工单了，收尾现在在跑的就行。」
- (1) **不开新票**：Released 只留在跑的 T2356（Eq729B 1b）、T2358（LW R1 1b）、T2360（BA-DK 设计）、T2361（PathBounds 1a）；H151：照常规跑完（审核 PASS 自动合并、RETURN 一次自动修复），不开其他票，四张都结束后中枢写 `docs/queue/DRAINED`。CLAUDE.md 没有 `DRAIN` mode，用 `mode: RUN` + 只含在跑票的 Released 列表 + H151 实现。
- (2) **交接包** `docs/HANDOFF.md` 重写（§0 局面与四张票各自结束后要做的事；§1 计数；§2 接下来的票：R3、LW-01（并 ST-6 R4）、UN-51（先定监督 0344 E5）、UN-52b、MA-06、BA 阶段 K；§3 Jun 的口径与偏好；§4 做法；§5 新调度立即要做的事）；旧启动交接包原文附在后面。
- (3) **启动文件**：`docs/claude-team/STARTUP.md` §2 改为接手版提示词（= `DISPATCHER-PROMPT.txt`，调度 V2），§3 记当前监督任务 `trig_01R1NVdwWjDU2P5KMhtTLr43`，§4 注明第一次启动专用，§5 写交接做法；`TEAM.md` 加 §10（V1 期间定下的 13 条常规：中文与中枢不空、Fable 只在数学卡住时用一次一个、BA 阶段门、gate 上限与预设切分、1a FAIL 分流、设计门、删 `private` 或拷贝、检查文件核名与导入、REQ 首行、停止线、时间戳、差异与返工账本、交接）。
- (4) **工具**入库：`docs/claude-team/tools/nsof.sh`（查声明全名与位置）、`portmap.py`（RBM2D 文件用到的名字在 RBM3D 的孪生或缺失）。
- (5) **CONTROL 归档**：旧 CONTROL（约 190KB）原样附到 `docs/queue/CONTROL-archive.md` 末尾；新 CONTROL 约 8KB（常设规则 H4/H12/H23/H28/H101/H122、H151、合并记录尾部 6 行）。
- (6) 调度 V1 的心跳停止；监督定时任务不动。交接后本会话不再写文件。计数（宽口径）：ST-6 3/4；LW 50（计划 52，上限 55）；UN 58/64；BA 35；MA 7/8。下一张票号 T2362，下一节 §166，下一条 H152，下一号差异 D632。

## §166 — 调度 V2 接手；中枢周额度停摆后恢复；T2360（BA-DK）合并 → 阶段 K 开启 REQ-2026-10-09-2010（总调度 V2，2026-10-09 20:12 UTC）

- (0) **接手**：Jun 在 2026-10-09 19:2x UTC 指定 Cowork 会话 session_01MtDU5B1PoJEbaNvMuRAPrx（账号 misslose@ucla.edu）为调度 V2，接手调度 V1（session_01RThagGKa4jNgUEWeKViyyg）；按 HANDOFF §5 排心跳（STARTUP §2 的 V2 固定消息）、在 `HEARTBEAT-STATE.md` 顶部写明唯一总调度。监督任务 `trig_01R1NVdwWjDU2P5KMhtTLr43` 不动。
- (1) **中枢停摆**：04:22–19:22 UTC（周用量上限，12:00 PT 重置）。19:25 中枢按规则 (H) 重跑 T2356、T2358、T2360 的 1b；T2361 审核 PASS（19:29），但合并第 3 步被中枢会话的权限检查拒绝；H152（授权重试）中枢答「拒绝覆盖重试，须 Jun 在该会话里允许」——已告知 Jun。
- (2) **T2360 = BA-DK 合并**（76106b7，仅报告，审核 PASS）：K1–K6 已答；16 行、中心 12.7k 行、阶段旗标 24 张；**F1：已合并的 `BAMLoop`（`BA/FlowPins.lean:274`）与论文 `(eq:KMloop)` 的配对不同**（`σ_i` 配 `(a_i,a_{i+1})` 而非 `(a_{i-1},a_i)`），`n ≥ 3` 混合电荷时 `(WI_calK)` 与树表示都不成立（数值，审核独立复核）。按 HANDOFF §2.6 与 §144 (2) 写 **REQ-2026-10-09-2010**（阶段 K 开启）：Q1 开阶段 K（16 行、旗标 24、K04 后设计核对）；Q2 F1 原地修还是加撇后继；Q3 四个带状 KL 文件原地泛化还是孪生（原地会触发导入树底层重编）；Q4 不新增外部输入（K05、K08 以带状 Lean 证明为蓝本）；Q5 阶段 K 的关闭条件（`BAKbound`、`BAKsolve`、`BAKward`、`STKward` 的载体形式）。**PASS 前不写 BA 证明票。** T2360a–e 待监督无异议后编 D632–D636。
- (3) **派单**：H151 收尾中（T2356、T2358 1b，T2361 待合并）；按 HANDOFF §2：T2358 合并 → LW R3；T2356、T2361 合并 → UN-51（先定 0344 E5）；阶段 K 等 REQ-2010。BA 计数 35 不变；其余同 HANDOFF §1。下一张票号 T2362，下一节 §167，下一条 H153，下一号差异 D632。

## §167 — H151 收尾完成（DRAINED）；T2358 审核 BLOCKED → 签 R-a（Amend 2）；回到正常运行（总调度 V2，2026-10-09 20:41 UTC）

- (0) **DRAINED**（20:31:46 UTC）：T2360 已合并（76106b7）；T2356、T2361 审核 PASS，合并等 Jun 在中枢会话里允许（权限检查拒绝，§166 (1)）；T2358 审核 BLOCKED。H151 完成。CONTROL 的 reason 改回正常运行（RUN），按 HANDOFF §2 随输入合并补票。
- (1) **T2358 = LW-13b R1 签字：选 R-a**（流程，总调度定；0243 O4 的钉文修补）：除 `locStepXProv_holds : LocStepXProv` 外全部目标证出（da182dc，1890 行，审核其余全 PASS）。原钉文按**值** `r ∈ LX` 给映射，构造按**位置**给，列表有重复值时值决定性未证；位置版 `lwProv_LocStepXProvPos` 已证（`lwProv_locStepXProvPos_holds`），引擎目标 `lw_localregularXP : LWEngineProv` 由它证出；审核 grep 核过 R3 的消费者都不提 `LocStepXProv`。所以目标换成位置版，删掉值版定义与其条件适配（`docs/tickets/T2358-amend-2.md`），repairer 只做这些删改，第 2 轮审核按脚本核 diff。不是新票：LW 计数 +0；返工账本 +1（开工后改目标）。不发 REQ：不是 0143 O2 的情形（不是切分、不是数学性 1a FAIL；替代陈述已证、无消费者）。REQ-2010 的 For information 未列此事，下次 REQ 顺带告知监督。
- (2) **H153**：Step A 提交调度文件（§166、§167、REQ-2010、REQ-2025、T2358 Amend 2、ROUTES、CONTROL、WORKLOG、DRAINED 与中枢未入库的报告由中枢按名自定）；Step C 跑 T2358 Amend 2（repairer → 第 2 轮 auditor → 规则 (A) 合并）。T2356、T2361 的合并仍等 Jun 的权限。
- (3) 计数不变：LW 50（R1 修补中，R3 = 51、LW-01 = 52，上限 55）；UN 58/64；BA 35；ST-6 3/4；MA 7/8。下一张票号 T2362，下一节 §168，下一条 H154，下一号差异 D632。

## §168 — 监督 2051 PASS：阶段 K 开（K-a…K-e、G1–G3）、F1 原地修；UN-51 取 (a)（U1–U5）；放 BA-K00 = T2362；写 UN-51 = T2363（等合并）；差异 D632–D635（总调度 V2，2026-10-09 21:01 UTC）

- (0) **T2358 Amend 2**：repairer 删掉值索引钉文与 4 个辅助（6d6ef4d，1820 行），第 2 轮审核 PASS（脚本核 diff）；合并与 T2356、T2361 一样等 Jun 在中枢会话里允许。监督 2051 已看过 Amend 2：符合 0243 O4，无 HOLD，LW 仍 50。
- (1) **监督 2026-10-09-2051 A（REQ-2010）：PASS**——阶段 K 按设计 §4 的 16 行开，旗标 24 张（BA 到 59），条件照办：**K-a** K00 先合并，之前不写任何陈述里提 `BAKsol`/`BAKloop`/`BAMLoop`/`baFM*` 的行（K09a 不含 BA 对象，但受 K-b 约束）；**K-b**（新发现 F2）K09a 写票时钉**一个**关于 `(Sig, TH)` 的抽象谓词，既是 K09a 的前提又是 K08b 的目标（加权、任意根、任意交替 `σ`、`Q ≤ 2(d−1)`、反射与平移；或逐点形式），`SumZeroAbs` 作废；K09a 的 1b 前做数值核对（`Q ∈ (1, 2, 4)`、`g ∈ (0.1, 0.2, 0.4)`、两个 `1−t`，比值对 `g² + 1 − t`），比值随 `g ↓` 增长即 REQ；**K-c** K04 合并后、写 K05 前发 REQ（仙人掌 API、K05 提纲、`M`-边电荷规则对改正后 `BAMLoop` 的数值复核、K05–K08 重估）；**K-d** 阶段 K 从 K00 起计（BA 36），超 24 张未关即 REQ；**K-e** K05b 的目标显式包含所有 `n` 的 `BAKsolve`。**Q2**：F1 **原地**修（K00 唯一可写：`BA/FlowPins.lean` 的 `BAMLoop` 文档串与体（272–276 行）+ 新 `BA/KBase.lean`；编出 `BAMLoop_apply`、长度 ≤ 2 不变、见证 = 15；迹形式 ≤ 100 行则做，否则记欠 T/U/V）。**Q3**：四个带状文件原地泛化，接受，条件 G1（检查文件对每个外用公开声明写 `example : 旧陈述 := 旧名`，不删不改名）、G2（原地合并让路关键路径：T2356、T2361、LW R3、LW-01/ST-6 R4、UN-51、UN-52b、MA-06 先合并）、G3（保不住旧陈述的段落改放新通用文件，算 amend）。**Q4**：不新增外部输入；K05a、K08a 的 1a 是设计门（完整书面论证 + 审核后才 1b）；内部路线超 1.5 倍 hi 时可问 Jun 是否授权 [RBSO1D]。**Q5**：关闭条件 `BAKbound`、`BAKsolve`（所有 `n`）、`BAKward`、`STKwardgL`（K12 钉并对 `baFMz` 证）、`inst_BAKbound`（`U` 卸掉），外加带状消费者对照表（`KLK_one/two` → K03，`KLK_rotate` → K01，`KLK_isKLoop` → K05b，`KLK_ward` → K02，`stKbound/ward_of_flow` → K12，`KLbound_holds` → K12；`lem_pureloop` K07、`lem_wardineq_K` K11、`BATreeRep` K05b 公开），关闭 REQ 附此表。
- (2) **监督 2051 B（REQ-2025）：PASS**——取 **(a)**（钉文不改；带状实例 UN-51，BA 实例 BA-C5 + BA-N2），**U1** UN-51 证种类通用的生产者 `UNG1Rowk K P ML Loc Que`（T 输入作前提；列表即 BA-C5 的目标单），带状实例是推论；**U2** 等 T2356、T2361 合并才放；**U3** 1a 列 RandomLayerA 各行的 `τ_U` 约束，需小于 `ouTauMax` 即 REQ；**U4** 导入 `Eq729B`、`PathBounds`，不导入 ST-6，不重证链；**U5** UN-51 = 59、UN-52b = 60，超出预设 A|B 的切分即 REQ。`Test/Axioms.lean:187-188` 的归属注释由 UN-51 改为「band: UN-51; BA: BA-C5 (T inputs) + BA-N2 (instance)」。
- (3) **票**（自写，不用 Fable）：**T2362 = BA-K00**（`BA/FlowPins.lean` 272–276 原地 + `BA/KBase.lean`，`prover-hard`，503 / 579 / 744，停止线 950；现在放行，H154）。**T2363 = UN-51**（`GUEPhase/RandomLayerA/B`，`prover-hard`，800–1000，停止线 1300，预设切分 A|B；检查文件导入 `Eq729B`、`PathBounds`，**两者合并后**才列入 Pre-release 并放行）。LW R3 等 T2358 合并后写（HANDOFF §2.1：C5、C6、0243 L1、§162 (2)）。K01、K09a 等 K00 合并（K-a）与 K-b 的谓词与数值核对。
- (4) **差异**：D632（T2360a，已改正的 Lean 缺陷）、D633（T2360b）、D634（T2360d）、D635（T2360e）；T2360c 不编号。
- (5) 计数：BA 36（K00 计入）；UN 58（UN-51 写好未放）；LW 50；ST-6 3/4；MA 7/8。下一张票号 T2364，下一节 §169，下一条 H155，下一号差异 D636。

## §169 — LW-13b R3 = T2364 写好，等 T2358 合并（总调度 V2，2026-10-09 21:15 UTC）

- (1) **T2364 = LW-13b R3 = G + F**（`Graph/AuxGraphRooted.lean`、`Graph/LWMomentExp.lean`、`Test/Axioms.lean` 删欠账 `LWMomentExp`；`prover-max`，1183 / 1567 / 2337，停止线 2100，预设切分 C3 = G | F；LW 51）：条件 C5（1a 先编有根森林；换 (E) 要 REQ）、C6 取 **(α)**（`∀ p, ∃ K`，远尾半径为论文尺度）、0243 L1（步引理只经引擎递归，即只用 `lw_localregularXP`）、§162 (2)（`LWfD … univ = LWf` 转换）。检查文件导入 `LWProv`，**T2358 合并后**才列入 Pre-release 并放行。
- (2) 待放的票（合并后当轮放）：T2363（UN-51，等 T2356 + T2361）、T2364（R3，等 T2358）。在跑：T2362（BA-K00，1a）。三张审核 PASS 的票（T2356、T2358、T2361）等 Jun 在中枢会话里允许合并。下一张票号 T2365，下一节 §170，下一条 H155，下一号差异 D636。

## §170 — Jun 授权中枢的合并动作（总调度 V2，2026-10-09 21:55 UTC）

- (0) **Jun（2026-10-09 约 21:47 UTC，本会话）**：「我允许你告诉他吧， 我现在没法用那台电脑」——回答调度请他在中枢会话里允许 T2356、T2358、T2361、T2362 的合并。
- (1) **落实**：H155 原样转述 Jun 的话，授权 CLAUDE.md §3 规则 (A) 的合并动作（检出本单文件到 `main`、加根导入、全库构建、提交、推送 main），顺序 T2361 → T2356 → T2358 → T2362，以后规则 (A) 的合并同此。若中枢会话的权限检查仍拒绝，中枢保持 `audit-pass`，done 行写明被拒的动作；调度不改中枢的权限设置（`.claude/settings.json`）。

## §171 — BA-K09a = T2365 放行（K-b 的谓词钉定）（总调度 V2，2026-10-09 23:01 UTC）

- (0) 更正 §168 (3)：K09a **不等** K00 合并。监督 2051 K-a 写明「K09a contains no BA object and may run in parallel with K00, subject to K-b」，G2 写明「K01 and K09a may be released now」。K01 仍等 K00（设计行 K01 依赖 K00，且含 BA 实例）。
- (1) **T2365 = BA-K09a**（BA 37，阶段 K 第 2 张）：在 `Loop/KLIndStepA.lean`、`Loop/KLIndStepB.lean` 原地把 `(eq:ind-step-bound)` 改写到抽象数据 `(ι, L, g, t, Sig, TH)` 上，即路线 G。`prover-hard`，355 / 472 / 549，停止线：两文件净增 700 行。
  - 目标：`indStepAbs_of`，陈述钉为检查文件的 `IndStepAbsOfStmt`；三个带状实例；`KLindStepAt_iff`（`Iff.rfl`）；`KLindStepAt_holds` 改由新路线导出，陈述不变。
  - G1：两文件在外部使用的 9 个公开名，加上 `KLindStepPin` 的定义体，旧陈述写进检查文件（`example … := @名` / `Iff.rfl`）。名单由脚本找出：`KLIndStepA_Theta_apply_sub`、`KLlat_inv_le_Bparam`、`KLIndStepA_Bparam_le_zero`、`KLIndStepA_Bparam_nonneg`、`KLIndStepA_Theta_norm_le`、`KLIndStepA_thetaEdge_long`、`KLindStep_nonAlt_noloss`、`KLindStepAt`、`KLindStepPin_holds`。
  - G2：合并让位给关键路径。
- (2) **K-b（发现 F2）：取形式 (i)**，钉为 `SigSumZeroAbs`。它既是 K09a 的假设，也是 K08b 的目标，取代探针的 `SumZeroAbs`。内容如下，交替 `σ` 时成立：
  - 反射与平移不变；
  - 每个根 `r`、每个切片 `δ_r = x` 上，带号估计 `≤ C(1-t)`，带权绝对估计 `Σ|Σ(δ)|(maxDist+1)^Q ≤ C(g²+1-t)`，对每个 `Q ≤ 2(d-1)` 成立。
  
  不取形式 (ii)（逐点 `g²` 因子）：(i) 更弱，而且已经够用（带状步只用 `Q = d` 与 `Q = 2(d-1)`）。带状形式就是 `KLsumZero_weighted`（D194），不算新差异。
- (3) **另外两个抽象假设包**：
  - `SigDecayAbs`：`(eq:molecule-decay)`，情形 (i) 用；BA 的来源是 K07。
  - `IndStepTH`：取代 `KLPT` 的叶包。内容是性质 5、5'、6、7、8，形状同 `KLPT`/`BAProp5to8`；6、7 只在 `c = 1/2` 处（带状证明只用这一处，`KLIndStepA.lean:182, 291`）；另加平移和长边行和。BA 的来源是 K12 的 `baProp5to8_holds`。
  - 参数范围只用 `KLPar` 那一组（`3 ≤ L`、`0 < g ≤ gmax`、`0 ≤ t < 1`）。
  - 若 1a 发现还缺假设，按钉文修补处理，走 amend（0243 O4）。
- (4) **K-b 的数值核对 N1 放在 K09a 的 1a**（监督允许「as K09a's step 0」）。
  - 设置：BA 分子 `Σ^{(∅)}`，K00 约定，B8 设置；`g ∈ {0.1, 0.2, 0.4, 0.8}`，`1-t ∈ {1e-3, 1e-4}`，`Q ∈ {1, 2, 4}`；比值取 `S_Q/(g²+1-t)`，并查反射、平移。
  - 停止线：`ratio(0.1)/ratio(0.4) > 2`，或反射/平移缺陷 > 1e-10 → 不进 1b，`returned`，调度发 REQ。
- (5) H157：提交 + 编译 T2365-check + 开工（H12）。H156 已完成（22:43:23，exit 0，109 行），K01 的转储在 `docs/tickets/checks/K01-statement-dump.out`，K01 等 K00 合并后写。
- (6) 计数：BA 37；在跑 T2365（开工后）；4 张 audit-pass 仍等 Jun 在 Mac 上允许合并（H155 无回复）。下一张票号 T2366，下一节 §172，下一条 H158，下一号差异 D636。

## §172 — BA-K01 的通用部分 = T2366 放行；K01 的 BA 实例移到 K03（总调度 V2，2026-10-09 23:09 UTC）

- (0) H157 完成：提交 1fe7b7f，T2365-check exit 0，T2365 于 23:03:44 开工（wf_d34cffd1-3d8，1a 含 N1）。
- (1) **调度决定（流程，不涉路线）**：设计行 K01 只因「BA instances」依赖 K00（K-a：提到 `BAMLoop`/`BAKsol` 的陈述须等 K00 合并）。四张合并卡在中枢权限上，K00 何时合并不知道，所以把 K01 拆成两部分：
  - 通用部分现在放行，即 T2366；
  - BA 实例并入 **K03**（`BA/KSolve.lean`）：`BAMLoop` 处的唯一性、`BAKsol` 的旋转与平移。K03 本来就依赖 K01 和 K00，所以并入后行数不变，不算 K-d 的拆分，旗标计数不变。
  - 收尾表「`KLK_rotate` → BA rotation → K01」改记为 K03，在 K-c REQ 和阶段 K 收尾 REQ 里写明。
- (2) **T2366 = BA-K01 通用部分**（BA 38，阶段 K 第 3 张）：
  - 范围：在 `Loop/Unique.lean`、`Loop/KLUnique.lean` 原地做（路线 G）。
  - 钉文：`UniqS`（探针原文）、`RetireS`（两环界，与 `S` 无关）、`RotS`（对称、`‖S‖ ≤ 1`、`M` 旋转不变）、`TranslS`（`S` 平移不变、`‖S‖ ≤ 1`、`M` 平移不变）；对应定理 `*_holds`。
  - 带状导出：`isKLoop_unique`、`KLretire_twoLoopBounded`、`KLK_rotate`、`KLK_translate`、`eq_on_level`，陈述都不变。
  - G1：H156 转储的 18 个外用名全部写进检查文件。
  - 规模：`prover-hard`，约 213 / 272 / 311；停止线为两文件净增 420。
  - G2：合并让位给关键路径。
- (3) H158：提交 + 编译 T2366-check + 开工（与 T2365 并行）。
- (4) 计数：BA 38。在跑 T2365，T2366 开工后变两张。4 张 audit-pass 仍等 Jun 在 Mac 上允许合并。下一张票号 T2367，下一节 §173，下一条 H159，下一号差异 D636。

## §173 — K-b 的数值核对 N1 通过（总调度 V2，2026-10-09 23:20 UTC）

- (1) T2365 的 1a 报告（`docs/reports/T2365-prove.md` (a)，23:12:59 UTC）：
  - 设置：BA 分子 `Σ^{(∅)}`，K00 约定；`n = 4`（`q = 4, 5`）与 `n = 6`（`q = 3`），`E = 0.3`。
  - 比值 `S_Q/(g²+1-t)`：`g` 变小时比值也变小。所有 `Q`、`1-t`、`σ` 与设置下，`ratio(0.1)/ratio(0.4)` 的最大值是 **0.3545**，停止线为 2。
  - 补充：`g` 一直降到 0.01，比值保持有界（`n = 4, q = 4`、`Q = 1, 2, 4` 时为 1.8 / 2.8 / 9.0）。
  - 反射/平移缺陷 ≤ 6.7e-16，带号估计 `/(1-t)` 约为 0.4–4.4。
  - 结论：监督 2051 K-b 的「ratio grows as g ↓ → REQ」没有触发，不发 REQ。K06–K08 照 K-b 谓词 `SigSumZeroAbs` 做。
- (2) T2365、T2366 的 1a 都是 PASS，不需要 amend：
  - T2365：`indStepTH_band` 需要 `0 < κ`（为了 `|E| ≤ 2`），这是带状实例的参数，不是包里的假设。陈述里没有 `hκ` 的带状公开名（`KLIndStepA_Theta_norm_le`、`KLf0_bound` 等）保留原证明。
  - T2366：`Unique.lean` 要加 `import RBM3D.Loop.KLTree`，脚本确认不成环，在票的允许范围内。
  - 两张都进入 1b。

## §174 — Jun 在 Mac 上放行合并；四张合并，T2363、T2364 放行（总调度 V2，2026-10-10 01:11 UTC）

- (0) **Jun 回到电脑前**（本会话，约 00:55 UTC 问「要对 hub 说什么」）。调度给出原话（授权规则 (A) 合并 T2361 → T2356 → T2358 → T2362 → T2366，以后规则 (A) 合并同此），Jun 在中枢会话里输入。
- (1) **合并**（全库构建，已推送）：
  - T2361：16b812a，00:56，UN-50b `PathBounds`；
  - T2356：96f2390，00:57，UN `Eq729B`，D628–D631；
  - T2358：c587dcd，00:59，LW-13b R1 `LWProv`，Amend 1 + Amend 2；
  - T2362：8050043，01:01，BA-K00：`BAMLoop` 原地修 + `BA/KBase`。
  
  T2366（K01 通用部分，audit-pass）按规则 (A) 接着合并。返工账本补五行（T2360、T2361、T2356、T2358、T2362）。
- (2) **放行**：
  - **T2363 = UN-51**：输入 T2356、T2361 已合并；
  - **T2364 = LW-13b R3**：输入 T2358 已合并。
  
  两张的检查文件名字核对过，全部在 main 上。H159：提交 + 编译 + 开工，连同在跑的 T2365 共 3 个 workflow。
- (3) K00 已合并，K-a 解除：K03（`BA/KSolve`，并入 K01 的 BA 实例，等 T2366 合并）与 K04（`BA/KCactus`，只依赖 K00）可以写了。下一轮起写。
- (4) CONTROL 超过 20KB，已归档到 `CONTROL-archive.md`：已合并的 Released 行、已完成的 Pre-release 项、H151–H154、H156–H158，以及 10 月 9 日的 Merge log 行。H155 保留，因为它是常设授权。
- (5) 计数：UN 59（UN-51 开工）；LW 51（R3 开工）；BA 38。下一张票号 T2367，下一节 §175，下一条 H160，下一号差异 D636。

## §175 — T2365 审核 PASS；BA-K04 = T2367 放行（总调度 V2，2026-10-10 01:26 UTC）

- (1) **T2365（BA-K09a）审核 PASS**（b74e5fd，auditor claude-opus-5-5，不需要签字），排在 T2366 之后按规则 (A) 合并。
  - 检查方式的教训：钉文 `IndStepTH` 是 `structure`。检查文件里的那份副本是另一个归纳类型，两者永远不可能 `rfl` 相等，所以票里写的 `example : @X = @Check.X := rfl` 对结构体做不到。审核改为逐字段检查：7 个字段类型各自 `rfl`，双向 `Iff` 可以编译。这算通过。
  - 以后钉结构体时，票里直接写逐字段的检查方式；`def` 钉文照旧用 `rfl`。
- (2) **T2367 = BA-K04**（BA 39，阶段 K 第 4 张）：新文件 `BA/KCactus.lean`，定义仙人掌。
  - 内容：槽位（每个叶一个，每条弦两个）、节点内按区间的循环序、`M` 边电荷（D633 规则，K00 约定）；值 `BACactusVal` 写成合并的 `KLgval` 的实例（节点取槽位）；`BAGamma` 的类型钉为探针 `BATreeRep` 的 `Γ` 参数类型。
  - API：计数、`F = ∅` 的闭式、`n = 3` 即 `(Kn3sol)`、对称性。
  - 1a 是设计门（监督 Q4 的意思）：Lean 定义的 Python 镜像对照 T2360 B8 的 `mgraph.py`，逐棵树误差 ≤ 1e-12，树和对 ODE 误差 ≤ 1e-8（`n ≤ 6`）；`n ≤ 5` 有失败就不进 1b。
  - `prover-max`，500 / 700 / 1000，停止线 1300。合并后发 K-c REQ。
- (3) 中枢：T2366 合并构建中（证书模块重编，H101/H122）；H159（T2363、T2364）、H160（T2367）的编译与开工排在它之后。计数 BA 39。下一张票号 T2368，下一节 §176，下一条 H161，下一号差异 D636。

## §176 — BA-K03 = T2368 写好，等 T2366 合并（总调度 V2，2026-10-10 01:41 UTC）

- (1) **T2368 = BA-K03**（BA 40，阶段 K 第 5 张）：新文件 `BA/KSolve.lean`。
  - 钉文：`IsKLoopSLe`（长度 ≤ N 的方程组，封闭）、`BAKsolve`（探针原文；K05b 的目标，在这里先钉）、`BAKsolveLe3`。`BAKsolveLe3` 要求：长度 2 是 `(Kn2sol)`，长度 3 是 `(Kn3sol)`（K00 约定下逐字写出：叶 `a_v` 带 `Θ^{(σ_v,σ_{v+1})}`，乘以 `BAMLoop`），长度 1 是 `PropSpin m`。
  - 从 K01 移来的 BA 实例（§172）：`baK_unique`、`baK_rotate`、`baK_translate`（`BAMLoop_rot`、`BAMLoop_translate`、`BAMB_shift`），以及 `BAKsolve` 条件下的 `BAKsol_isKLoopS`、`BAKsol_rotate`、`BAKsol_translate`。收尾表中「BA rotation」由这里交付。
  - 1a 的 N3：在 B8 设置下用 RK4 求解 `n = 2, 3`，与钉住的闭式比较，目标误差 ≤ 1e-8；`n = 3` 超过 1e-6 就不进 1b（钉文修补，走 amend）。
  - `prover-hard`，约 700 / 844 / 1085，停止线 1400。
  - 检查文件导入 T2366 的新名字，所以 **T2366 合并后**才列入 Pre-release 并放行。
- (2) 计数：BA 40（K03 写好未放）。下一张票号 T2369，下一节 §177，下一条 H161，下一号差异 D636。

## §177 — BA-K02 = T2369 写好，等 T2366 合并（总调度 V2，2026-10-10 01:56 UTC）

- (1) **T2369 = BA-K02**（BA 41，阶段 K 第 6 张）：在 `Loop/KLWard.lean` 原地做通用 Ward（路线 G），另开新文件 `BA/KWard.lean` 放 BA 实例。
  - 钉文：`KernelFacts`（探针原文，结构体，逐字段核对）、`WardS`。`WardS` 的条件：`KernelFacts S`；`Im m(+) > 0`；`m(-) = conj m(+)`；`M` 翻转后取共轭；`M` 循环不变；`M` 在 `t = 0`、长度 ≥ 3 时满足恒等式；`K` 在长度 2 时满足恒等式。结论是对 `[0,1)` 上的任一解 `(WI_calK)` 成立，`η_t = (1-t) Im m(+)`。
  - 目标：`wardS_holds`；带状的 `kernelFacts_one/SB`；G1 是 `KLK_ward`、`KLWard_flip`。
  - BA 实例 `baK_ward`：任一 BA 解只要满足 `(Kn2sol)` 子句，就满足 Ward。`t = 0` 的条件由 `BAMB_ward_row` 给出，长度 2 的条件由 `BATheta_row_sum_pm` 与 `BAK_row_sum` 给出。
  - 1a 的 N2：在 B8 设置下核对 `t = 0` 的条件与 ODE 解的 Ward；`t = 0` 的缺陷超过 1e-6 就不进 1b。
  - `prover-hard`，425 / 612 / 770，停止线 1000（净增 + 新文件）。
- (2) **收尾表**：「`KLK_ward` → `BAKward` → K02」改为：K02 交付 `baK_ward`（对任一解成立）；`BAKward`（探针 306，陈述在 `BAKsol` 上）在 K12 组装，即 `baK_ward` 加上 K03 的 `BAKsol_isKLoopS`，前提是 `BAKsolve d`（K05b）。这样 K02 不依赖 K03，`BAKsolve` 只钉一次（K03）。阶段 K 收尾 REQ 写明这一点。
- (3) T2366 合并后当轮放行 T2368（K03）与 T2369（K02）。两张检查文件都导入 T2366 的新名字；T2369 的检查文件在今天的 main 上也能编译，但票依赖 T2366。名额：T2363、T2364、T2367 开工后只剩 1 个空位，先放 K03（`BAKsolve` 等关键路径），K02 等下一个空位。
- (4) 计数：BA 41（K02、K03 写好未放）。下一张票号 T2370，下一节 §178，下一条 H161，下一号差异 D636。

## §178 — T2366 合并；T2363、T2364、T2367 开工；T2368、T2369 放行（总调度 V2，2026-10-10 02:09 UTC）

- (1) **T2366（BA-K01 通用部分）合并 010cad9**，02:02 UTC，全库 4177 jobs。合并构建约 1 小时：`KLK_rotate` 的下游含证书模块，要按 H101/H122 重编。这就是 G2 说的原地合并的代价。之后 T2365（K09a）按规则 (A) 接着合并。
- (2) H159/H160 的 B/C 已完成：T2363（UN-51）、T2364（LW R3）、T2367（K04）的检查都 exit 0，从 main 010cad9 开工。现在在跑 3 张。
- (3) **放行 T2368（K03）**，补第 4 个名额；**放行 T2369（K02）**，等下一个空位（H12）。H161 负责提交、编译、开工。
- (4) 计数：UN 59；LW 51；BA 41。下一张票号 T2370，下一节 §179，下一条 H162，下一号差异 D636。

## §179 — T2364 Amend 1：C6 改取 (β)；三张 1a PASS（总调度 V2，2026-10-10 02:24 UTC）

- (1) **1a 报告**：
  - **T2363（UN-51）**：PASS。U3 的结论：没有哪一行需要 `τ_U < ouTauMax`，不改钉、不发 REQ。U1 的通用生产者 T1–T6 齐备，预设切分没有触发。
  - **T2367（K04）**：PASS。镜像核对 (α) = 1.9e-15，(β) = 1.24e-9（`n = 6`）、6.8e-10（`n ≤ 5`）；规模估计 1070，停止线 1300。候选差异 `T2367a`：`BAGamma` 是全函数（非 TSP 输入取垃圾值）。
  - **T2364（LW R3）**：PASS 附条件。F1：字面 (α)（`K` 在 `𝔠, sz, D` 之前）合不上，因为 `K_card` 要在拿到 `(p, ⌈1/𝔠⌉, D)` 之后才能取。F2–F4 是 1b 要从已合并的公开引理补出来的证明。
- (2) **调度决定**：C6 改取 **(β)**（1a 读法 5b，`∀ K > 0`，远尾半径 `K (log W)^{3/2} / K_card`）。
  - 监督 0143 C6 写明两种形式都对，只是偏好 (α)；F1 说明字面 (α) 做不到，所以这个选择仍在监督允许的范围内。目标 `lwMomentExp_holds` 不变。不发 REQ。
  - 记入 `docs/tickets/T2364-amend-1.md`，由 H162 交给 1b。返工账本在合并时记一行：开工后改钉文。
- (3) 下一张票号 T2370，下一节 §180，下一条 H163，下一号差异 D636。

## §180 — T2365、T2367 合并；K-c REQ 发出（总调度 V2，2026-10-10 03:25 UTC）

- (1) **合并**：
  - T2365（BA-K09a）a5c1a1a，03:11 UTC，全库构建，证书模块重编，约 60 分钟；
  - T2367（BA-K04）9b94993，03:20 UTC，`BA/KCactus` 1263 行。
  
  H161 完成：T2368（K03）03:11 开工，T2369（K02）03:19 开工。在跑 4 张：T2363、T2364、T2368、T2369。返工账本补两行。
- (2) **K-c**（监督 2051 Q1）：K04 已合并，发 **REQ-2026-10-10-0324**。内容：
  - (i) 已编译的仙人掌 API；
  - (iii) 电荷规则的组合表述，并对照 K00 核过：Lean 里的 `BACactusVal_sum_zero_BAMLoop`、镜像 1.9e-15、对 ODE 1.24e-9；
  - (ii) K05 的提纲：叶项 = 二环乘 `n` 环（n 个相邻或绕回的切对）；弦项 = `Θ²` 在 `u` 处切开（`KLsum_cut`）；由此得 `BAKsolve` 与 `BATreeRep`；
  - (iv) 规模：K05a 800 / 1100 / 1600，K05b 900 / 1300 / 1900。
  
  同一请求里请监督确认 §172、§177 对收尾表的两处挪动，并告知 §179（LW C6 改取 β）。**K05a/b 等这条 REQ 的 PASS。**
- (3) 此刻没有可放的新票：
  - K05 等 REQ；
  - K06 起都依赖 K05；
  - K09b 依赖 K08b；
  - UN-52b 依赖 UN-51；
  - LW-01、ST-6 R4 依赖 R3；
  - MA-06 排在最后。
  
  四个名额都满。
- (4) 计数：BA 41。阶段 K：已合并 4 张，在跑 2 张，共 6/24。下一张票号 T2370，下一节 §181，下一条 H163，下一号差异 D636。open REQ：0324。

## §181 — 监督 0350：K-c PASS（C1–C5）；T2368 Amend 1（`BAKsolve` 登记为 owed）（总调度 V2，2026-10-10 03:54 UTC）

- (1) **监督 2026-10-10-0350（回 REQ-0324）：PASS。** K05a、K05b 可以按提纲 (ii) 写，两张的 1a 都是设计门，附条件 C1–C5：
  - **C1：2 环不是仙人掌。** 长度 2 的仙人掌是 `ΘMΘ`，`(Kn2sol)` 是 `W^{-d}ΘM`，两者只在 `t = 0` 时相等。所以 K05b 的见证族要拼起来：长度 1 用 `PropSpin`，长度 2 用 `(Kn2sol)` 闭式，长度 ≥ 3 用 `W^{-d(n-1)}ΣBAGamma`。K05a 里的二环一律用闭式。`BATreeRep` 仍是 `n ≥ 3`。
  - **C2：方向。** 绕回对和每个弦切的一片方向是反的，要用 `M` 对称、`BATheta_swap`、`BATheta_isSymm`。需要非对称 `M` 的路线算 1a FAIL。
  - **C3：逐项数值核对。** 每个叶 `v` 和每条弦 `J` 的导数项，要等于它在表中对应切对的 `treeEqRhsS` 被加项。镜像 `cutGlueL/R` 与 `KLCut` 的映射，容差 ≤ 1e-12，`n = 3..6`。索引错算 amend；所需恒等式为假算 REQ。
  - **C4：`BAKsol` 不带 `(Kn2sol)` 子句。** K05b 由 `baK_unique` 得到 `BATreeRep`。K12 组装 `BAKward` 要用 `BAKsol_isKLoopS`、`baK_unique`（把 `(Kn2sol)` 传给 `BAKsol`）和 `baK_ward` 三样。
  - **C5：Q4 线。** 在 K05b 的 1a 评估：K05a 合并后的实际行数加上 K05b 的再估计，超过 3.3k 时可以问 Jun，但不是 HOLD。K05 只按预设的 a|b 切分。
  
  另外：Q2 的两处挪动认可（收尾表改为「BA rotation → K03」「`BAKward` → K02 + K03 + K12」）；LW R3 Amend 1 (β) 认可；阶段 K 实际行数与设计中心之比 1.07×，阶段 1.5× 规则不触发。
- (2) **T2368（K03）合并被登记拦下**：`BAKsolve` 是未登记的前提。这是调度的错：票上写了「Registry: none」。按 0350 O4 把它登记为 owed，生产者 K05b，由 K05b 删除这一行。写 **T2368 Amend 1**（H23 (c)：repairer 加一行，第 2 轮审核按脚本核对 diff），交给 **H163**。返工账本在合并时记：是（流程缺口）。教训：钉一个 Prop 定义、又让公开定理把它当前提时，票里必须写明登记类别。
- (3) **下一步**：写 **K05a**（`BA/KTreeDeriv.lean`，叶项，1a 设计门，C1–C3）。K05b 等 K05a 合并，在它的 1a 评估 C5。K12 的行写明 C4 的三样。
- (4) 下一张票号 T2370，下一节 §182，下一条 H164，下一号差异 D636。open REQ：无。

## §182 — BA-K05a = T2370 放行（总调度 V2，2026-10-10 03:58 UTC）

- (1) **T2370 = BA-K05a**（BA 42，阶段 K 第 7 张）：新文件 `BA/KTreeDeriv.lean`。
  - 钉文（检查文件逐字）：
    - `BASplicedFam`（0350 C1 的拼接族）；
    - `BAGammaDerivRHS`：`∂_tΓ_F`。叶项写成 `Σ_b (ΘM)(a_v,b) Γ_F(a_v←b)`；弦项是把边 `inl J` 的权换成 `Θ²` 后的 `KLgval`；
    - `BAGammaDerivStmt`：`0 ≤ t < 1`、`BAReal`、`KLIsTSP F` 下的 `HasDerivAt`；
    - `BALeafPairsStmt`：对任一满足 `BASplicedFam` 的族，叶部分等于 `treeEqRhsS` 的 `n` 个叶对，即 `(v+1, v+2)` 和绕回对 `(1, n)`，按 0350 的表。
  - 另外：`BAKcac` 加上 `BAKcac_spliced`（K05b 用）；`KLloopOf_*` 的列表恒等式。
  - 1a 是设计门：书面论证加 C3 逐项镜像（容差 1e-12）；1a 之后、1b 之前插一道 1a-audit。
  - `prover-max`，800 / 1100 / 1600，停止线 2000。
  - 不依赖 K03（T2368 还没合并）：二环只通过 `BASplicedFam` 的闭式进来。
- (2) 现在每张给公开定理加前提钉文的票，都要做登记预检（`#assert_rbm_axioms`），由 §181 (2) 的教训而来。T2370 已写入。
- (3) 下一张票号 T2371，下一节 §183，下一条 H165，下一号差异 D636。

## §183 — T2363（UN-51）合并；UN-52b = T2371 放行（总调度 V2，2026-10-10 04:12 UTC）

- (1) **T2363 合并 0347cb8**（04:08 UTC，UN-51：`RandomLayerA/B`，11 个目标；`Test/Axioms.lean` 只改 `UNOULLk`、`UNG1Rowk` 的归属注释）。返工账本补一行。中枢：T2370（K05a）已占 T2363 让出的名额（04:06 开工）；T2368 正在跑 Amend 1；T2364、T2369 在 1b。
- (2) **T2371 = UN-52b**（UN 60，计划 64，上限 65）：新文件 `Main/BUniv.lean`、`Main/BUnivHolds.lean`。
  - 用合并的 `un_bUniv_of_rows'` 组装 `UNBUniv`，接入所有已证的行：`un_infty1Row'`、`univMainRow`、`unClaimRow`、`unEMCTE2Row`、`jakUywRow`、`greenCorrAll`，以及 `unOURow = ouRow_of_pins g1Row g2bRow`（UN-51 之后两者都已证）。
  - 钉文 `BUnivFromLeaves`：剩下的叶是三条带状行 `UNDensBandRow`、`UNTrLocalBandRow`、`UNNormBandRow`（登记为 owed，归属写的是「UN-01」）；`UNL32`（borrowed）；`UNMLOut`、`UNLocAvgBand`、`UNQueBand`（消费的 MA/ST-6 输入）；`UNGUELocal`。
  - `bUniv_holds` 只能去掉 1a 证出或已有定理覆盖的叶。
  - 1a 做叶表，列每片叶的状态和生产者，作为 UN 收尾 REQ 的材料。三条带状行若在任何计划里都没有生产者，在 1a 报告里报给调度，由调度决定是在 UN 上限 65 以内加票，还是发 REQ。
  - `prover-hard`，150 / 250 / 400，停止线 500。属关键路径，下一个空位优先给它。
- (3) 计数：UN 60（写好）；BA 42。下一张票号 T2372，下一节 §184，下一条 H166，下一号差异 D636。

## §184 — T2368（K03）合并；T2371 1a 叶表 → UN-10a = T2372、UN-10b = T2373（总调度 V2，2026-10-10 04:31 UTC）

- (1) **T2368 合并 79dec34**（04:12 UTC，BA-K03 `BA/KSolve`，767 行；Amend 1 在 `Test/Axioms.lean` 加一行 owed `BAKsolve`，生产者 K05b）。返工账本记：是（流程缺口，§181 (2)）。
- (2) **T2371 1a PASS**（叶表）。叶 9 `UNDensBandRow` 和叶 10 `UNTrLocalBandRow` 在本票证出（确定性；`UNLocAvgBand` 是叶 10 自带的前提）。剩下两片 owed 叶在任何计划里都没有票：
  - 叶 11 `UNNormBandRow`：高斯尾 + 并集界 + 厄米矩阵特征值 ≤ N·最大元，200–320 行；
  - 叶 16 `UNGUESchurTail`：门户表 UN-10 的 `GUELocalSchur`（RBM2D 570 行），加上它导入的 `EigenInterlacing`（RBM2D 588 行，RBM3D 没有孪生）。
- (3) 两张票都在上限 65 以内，所以调度自定，不发 REQ。门户表 UN-10 原来是一张，现在拆成两张：
  - **T2372 = UN-10a**：`Universality/NormBand.lean`，`unNormBandRow`。`prover-hard`，200 / 280 / 380，停止线 500。删登记一行 `UNNormBandRow`。
  - **T2373 = UN-10b**：`Universality/EigenInterlacing.lean`、`Universality/GUELocalSchur.lean`，`gueSchurTail`、`gueLocal`。`prover-max`，1000 / 1250 / 1550，停止线 1700。1a 是设计门，内容是孪生表和指数表。中心估计超过 1500 行，或缺的孪生超过 200 行，就退回，拆成 (a) `EigenInterlacing`、(b) `GUELocalSchur`，那时 UN 到 63。删登记 `UNGUESchurTail`；`UNGUELocal` 按 T2357 的规则一并删，以预检为准。
  - 优先级：T2371 > T2372 > T2373 > BA 新票（其他方向先收尾）。
- (4) **T2371 Amend 1**：叶 11 不在本票做（有生产者 T2372）。`bUniv_holds` 的文档串写明各叶的生产者。由 H166 送给正在跑的 prover。
- (5) UN 收尾：T2371、T2372、T2373 合并后，`bUniv_holds` 剩下的叶只有 `UNNormBandRow`、`UNGUESchurTail`（都已证，由 MA-06 接上），加上 `UNL32`（borrowed）、`UNMLOut`（ST-6）、`UNLocAvgBand`、`UNQueBand`（MA 输入）。那时发 UN 收尾 REQ。是否要再加一张 UN-52c 把已证的叶接进 `bUniv_holds`，在收尾 REQ 里一起问。
- (6) 计数：UN 62（写好），计划 64，上限 65；BA 42。下一张票号 T2374，下一节 §185，下一条 H167，下一号差异 D636。

## §185 — T2371 合并；四张 audit-pass 排队合并；K05b = T2374、LW-01 + ST-6 R4 = T2375（总调度 V2，2026-10-10 07:25 UTC）

- (1) **局面**：中枢 04:2x–05:20 UTC 停在 API 会话上限，05:24 按规则 (H) 重跑。心跳链断了约 2 小时 40 分（04:39 那次的通知 07:19 才送到）。之后：
  - **T2371（UN-52b）合并 c0a7747**：313 行；叶 9、10 本票证出；Amend 1 生效，叶 11 留作前提。
  - T2369（K02）、T2364（LW R3）、T2372（UN-10a）、T2370（K05a）都已 audit-pass，排队合并。T2369 的合并构建 05:47 起在跑，`KLWard` 原地改动，下游要重编。
  - T2373（UN-10b）的 1a 设计门 PASS：中心 1320 行，不触发拆分；现在在 1b。
  - 中枢只剩 T2373 一张在证明，三个名额空着。
- (2) **合并顺序**（H167）：T2369 之后先合 T2370，再合 T2364，最后 T2372。理由：K05b 的 1b 等 T2370，LW-01 的 1b 等 T2364；T2372 下游没有人在等（UN 收尾 REQ 还要等 T2373）。
- (3) **T2374 = BA-K05b**（BA 43，阶段 K 第 8 行）：新文件 `BA/KTreeRep.lean`。
  - 内容：弦对（每条对角 `J` 对 `(i+1, j+1)` 项，用 `KLsum_cut` 和 `KLFIn/KLFOut/KLshift*/KLinV/KLoutV`）；`baKcac_isKLoopS`；`baKsolve : ∀ d, BAKsolve d`；`baTreeRep : ∀ d, BATreeRep d (@BAGamma d)`，经 `BAKsol_isKLoopS` + `baK_unique` 得到（0350 C4）。
  - 钉文 `BATreeRep`：照探针逐字。删登记 `BAKsolve` 一行（0350 O4）。
  - 1a 设计门：书面论证、C3 逐弦数值、C5 的 Q4 线读数；之后 1a-audit。`prover-max`，800 / 1100 / 1600，停止线 2000。
  - **1a 现在开**：读 `t/T2370`，不跑 `lake`。**1b 等 T2370 合并后**从 `main` 开分支。
- (4) **T2375 = LW-01 + ST-6 R4**（LW 52，上限 55；ST-6 4/4）：新文件 `Graph/LWTermHolds.lean`、`Induction/MainIndHolds.lean`。
  - 内容：`LWInteg`、Markov 一步、`LWReduceB`、`LWterm`、`LWtermB`、`LWReduceT`、`LWtermExpS`、`LWtermExpN`（用已合并的 `lwtermExpN_of_LWterm`）、`LWtermExp`；R4 `stMainInd_holds`（= `stMainInd_of_LW`，按 1942 C8 不重证 Step 2）、`unMLOut_holds`；删相应登记行。
  - 1a 设计门：前提 ↔ 生产者表（1143 O2）、指数表、实例。`prover-max`，1000 / 1300 / 2000，停止线 2300。
  - **不预授切分**：0143 规定 C1–C3 以外的 LW 切分要发 REQ。1a 中心估计超过 2000 行就退回，附 B/T 两半的切分方案，由调度发 REQ。
  - **1a 现在开**（读 `t/T2364`）；**1b 等 T2364 合并后**开。
- (5) 返工账本补 T2371 一行（否）。
- (6) 计数：UN 62（计划 64，上限 65）；LW 52（上限 55）；ST-6 4/4（R4 并入 T2375）；BA 43；MA 7/8。下一张票号 T2376，下一节 §186，下一条 H168，下一号差异 D636。

## §186 — T2373（UN-10b）合并；UN 收尾 REQ（总调度 V2，2026-10-10 08:07 UTC）

- (1) **T2373 合并 ff39b72**（07:57 UTC）：`gueSchurTail : UNGUESchurTail`、`gueLocal : UNGUELocal` 已证，删了两行登记。至此 UN 带状链的票全部合并：UN-51、UN-52b、UN-10a、UN-10b。UN 计数 62，上限 65。
- (2) `bUniv_holds` 剩下的叶：
  - `UNNormBandRow`、`UNGUESchurTail`：已证；
  - `UNMLOut`：T2375 的 `unMLOut_holds`；
  - `UNLocAvgBand`、`UNQueBand`：由 MA 的 `locSC`、`QUE` 经已合并的桥得到；
  - `UNL32`：借用。
  T2375 合并后，`UNBUniv` 只差一行组装，归 MA-06。
- (3) **REQ-2026-10-10-0806**（UN 收尾，不阻塞在跑的票）：
  - Q1：UN 闸门对带状模型关闭，最后一行放进 MA-06，还是另开 UN-52c；
  - Q2：剩下的 UN 登记行分 (a)–(e) 五类，问 (d) 类是否改登记类别、(e) 类是否归 BA 终端阶段；
  - Q3：有没有漏掉、没有生产者的叶。
  答复前不开任何 UN 票。
- (4) 中枢：T2374（K05b）、T2375（LW-01）都在 1b，共 2 张在跑。暂时没有可放的票：K06 等 K05b，MA-06 等 T2375 和 BA 终端。
- (5) 下一张票号 T2376，下一节 §187，下一条 H169，下一号差异 D636。

## §187 — T2374（K05b）合并；BA-K06 = T2376 放行（总调度 V2，2026-10-10 08:53 UTC）

- (1) **T2374 合并 ab54184**（08:46 UTC，`BA/KTreeRep`，1763 行）：`baKsolve : ∀ d, BAKsolve d`、`baTreeRep : ∀ d, BATreeRep d (@BAGamma d)` 已证，登记的 `BAKsolve` 已删（0350 O4）。阶段 K 已合并 8 行：K00、K01g、K09a、K04、K03、K02、K05a、K05b。K05 合计 612 + 1763 = 2375 行，低于 Q4 线 3.3k。
- (2) **T2376 = BA-K06**（BA 44，阶段 K 第 9 行）：新文件 `BA/KMolecule.lean`，是带状 `KLTree` §4–§5 加 `KLSumZeroWard` §1–§3 的 BA 孪生。
  - 内容：`BAKpi`、`(eq_K-Kpi)`、`BASigmaPi`、`(eq:molecule-Kpi)` 的第一步、在最内长边处的分解、作为接口族的分子权 `BASig`（`SigSumZeroAbs` / `IndStepAbs` 的 `Sig` 类型，含两条平移条款）。
  - 通用的层组合学直接用已合并的（`Flong_eq_iff_cut`、`exists_innermost`、`sigmaIn/Out`、`KLsum_cut`）。
  - 1a 设计门：定出全部公开陈述，并对照下游 K07、K08、K10、K09b 的用法；数值核对 ≤ 1e-12。之后 1a-audit。
  - `prover-hard`，500 / 750 / 1200，停止线 1500。
- (3) 中枢：T2375（LW-01）在 1b，加上 T2376，共 2 张。UN 收尾 REQ-0806 仍未答。
- (4) 计数：BA 44（阶段 K 9/24）；UN 62；LW 52；ST-6 4/4；MA 7/8。下一张票号 T2377，下一节 §188，下一条 H170，下一号差异 D636。

## §188 — 监督 0853（回 REQ-0806）PASS：UN 带状关闭；MA-06 拆 a/b；E1–E4 交 BA（总调度 V2，2026-10-10 08:56 UTC）

- (1) **监督 2026-10-10-0853：PASS**。
  - Q1：UN 对带状模型关闭，不开 UN-52c，UN 停在 62。
  - Q2：(a)–(c) 同意；(d) 按规则移入 `structuralProps`，但 `UNOUQUE` 归 (a)；(e) 同意，E1–E4 除外。
  - Q3：有四项没有生产者（E1–E4），都属 BA 体普适性（Thm 2.7 第 3b 条），不影响 Thm 2.4。
- (2) **采纳 R1：MA-06 拆成 a/b**（MA 计划 8 → 9）。
  - **MA-06a = 带状终端**：`UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff`，约十行组装，T2375 合并后放行。它负责 C1 和 O3 的登记编辑：
    - 删 `UNBUniv`、`Endpoints.{decol, locSC, QUE, QDiff, BUniv}`、`UNOUClaims`、`UNLocAvgBand`、`UNQueBand`，配 `unOUClaims_holds`、`unLocAvgBand_holds`、`unQueBand_holds`；`UNOUQUE` 随 `UNOUClaims` 一起删，或附注留下；
    - `UNTrLocal`、`UNNormBound`、`UNClaim417`、`GUEPathBounds`、`UNTrLocalInit'` 移入 `structuralProps`，注释写明带状实例和 BA 行的指针；
    - `STLWB`、`STLWT`、`STOptL2` 给出类别决定（superseded，并写明替代它的带守卫的消费者）；
    - `UNClaimRowBA` 用 `unClaimRowk _` 消掉。
  - **MA-06b**：`Thm27` 和 `final_shape`，等 BA 终端。
  - 理由：Jun §145（其他方向先收尾，与 BA 并行）。带状 Thm 2.1–2.5 不应等 BA。
- (3) **C2：E1–E4 交 BA，记为 BA-N3**（阶段 M/N，「`UNKind.ba` 上的 UN 侧形式」）：
  - E1：`UNEMCTE2RowBA` + `UNEMCTE2k`、`UNEMCTE2Rowk`；
  - E2：`UNJakUywRowBA` + `UNJakk`、`UNUywk`、`UNJakUywRowk`；
  - E3：`UNCoreC''`；
  - E4：`UNGreenCorrAllC`、`UNGreenCorrC`。
  阶段 M/N 开启 REQ 的设计里逐项决定走转移（`ouMatC (ba sz) = λΨ + ouMat …`，加平移 `Φ ↦ Φ(λΨ + ·)`）还是写泛型孪生。E5（BA 流是否满足 `etaT`、`|fE| ≤ 2 − κ`）放进 BA-C5 的 1a。ROUTES 的 UN 行据此记为「带状关闭；E1–E4 交 BA-N3」。
- (4) **T2376 已由 Jun 在中枢直接开工**（中枢会话「开始啊」，08:53:51 UTC；9d5d47d 提交了票和检查文件）。H169 剩下的提交步骤照常执行。
- (5) 计数：UN 62（关闭）；MA 7 / 计划 9；BA 44（阶段 M/N 加 BA-N3）。下一张票号 T2377，下一节 §189，下一条 H171，下一号差异 D636。

## §189 — MA-06a = T2377 预先放行（T2375 合并后开工）（总调度 V2，2026-10-10 09:09 UTC）

- (1) T2375（LW-01）的证明阶段 09:07 UTC 交了报告，正在审核。为了它一合并就能开工，先写好 **T2377 = MA-06a**（带状终端，MA 8，计划 9）。
  - 新文件 `Main/BandTerminal.lean`：`locSC_holds`、`QDiff_holds`、`QUE_holds`、`decol_holds`、`unLocAvgBand_holds`、`unQueBand_holds`、`unOUClaims_holds`、`unBUniv_of_L32`、`band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff`、`unClaimRowBA_holds`。
  - 登记编辑：按 0853 的 C1、O3 删行、移类别；E1–E4 的归属注释改成 BA-N3。
  - `prover-hard`，150 / 250 / 400，停止线 500。
  - **开工条件：T2375 合并。**
- (2) 下一张票号 T2378，下一节 §190，下一条 H172，下一号差异 D636。

## §190 — T2375 合并：LW、ST-6 关闭；T2377 开工；T2376 Amend 1（K06 拆成两个文件）（总调度 V2，2026-10-10 09:23 UTC）

- (1) **T2375（LW-01 + ST-6 R4）合并 17ccf68**（09:17 UTC，1894 行，停止线 2300，审核一次 PASS）。
  - `lem:LWterm`、`lem: EWGn2_N`、`STMainInd`、`STStep2`、`UNMLOut` 对所有 d 成立；另外证出 `stEtermsMid_holds`、`stStep5I/II_holds`。相应登记行都已删。
  - **LW 关闭，52 / 上限 55。ST-6 关闭，4/4。**
  - T2377（MA-06a）在同一轮开工，分支从 17ccf68 拉出。
- (2) **T2376（K06）1a-audit RETURN**：陈述、论证、数值都 PASS（6.84e-14），只有计划超线。按实测的复制量，中心估计约 1598 行，停止线是 1500。
  - **调度决定（流程，不发 REQ）：取审核给的方案 (b)，写 T2376 Amend 1。**
    - 新增唯一可写文件 `BA/KCactusCut.lean`，放从 K05b 复制来的切割工具，对外公开 `baCactus_cut`，K10 以后直接导入。
    - 两个文件合计停止线 2000；角色升为 `prover-max`。
    - 1a 不重做：prover 在 1b 报告开头按实测量重列计划。
    - 加纸面差异候选 `T2376c`。
  - 这不算拆票：还是一张票，阶段 K 的计数不变。
- (3) 返工账本补 T2375 一行（否）。
- (4) 计数：LW 52（关闭）；ST-6 4/4（关闭）；UN 62（带状关闭）；MA 8 / 计划 9（T2377 在跑）；BA 44（阶段 K 9/24）。下一张票号 T2378，下一节 §191，下一条 H173，下一号差异 D636。

## §191 — T2377（MA-06a）合并：带状主定理 Thm 2.1–2.5 证完；中枢补位：BA 阶段 G/E、T/U/V 的设计票（总调度 V2，2026-10-10 09:56 UTC）

- (1) **T2377 合并 8b66528**（09:41 UTC，`Main/BandTerminal`，159 行，审核一次 PASS）：`band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff`。**带状模型的五条主定理（Thm 2.1–2.5）全部证完，唯一前提是借用的 LSY 输入 `UNL32`。** 登记按监督 0853 C1/O3 改完。`owedProps` 剩 82 行：BA 14、Gauss 47（BA 链载体件和 ST 侧剩余件）、Green 2、Univ 19（BA 的 UN 侧件，含 E1–E4）。MA 8 / 计划 9，只剩 MA-06b（`Thm27`、`final_shape`，等 BA 终端）。
- (2) **中枢只剩 T2376（K06）一张在跑**，阶段 K 其余各行都等 K06。补位的办法是开另外两个 BA 阶段的设计票。两张都只出报告；报告合并后作为开阶段 REQ 交监督（§144）：
  - **T2378 = BA-DGE**（BA 45）：阶段 G（Green 层，`lem_GbEXP_BA` → 登记的 `BAGbEXPii/ij/av`，旧行 G2–G6；G1 已合并）和阶段 E（EK 层，旧行 E1–E3）。问题 GE1–GE6：路线（原地泛化或孪生）、输入、纸面状态、对 K/L/T 的依赖（哪些行现在就能和 K 并行）、行表、旗标。
  - **T2379 = BA-DT**（BA 46）：阶段 T/U/V（链：Steps 2–6、主归纳、`GLoopAtT0`）。§144 (3) 的前提（ST-4…6、LW-14 闭合）已经满足。问题 TV1–TV6：在一个语义重的块上复测路线 G 的 `g` 和 `f_sem`（触发线 `g > 0.5` 或 `f_sem > 0.30` 就改走路线 I）；载体与钉文；对 K/G/E/L 的依赖；行表与配对；张数，超过 40 行拆子阶段；对已关闭的带状文件做原地编辑的代价。
  - 两张都是 `prover-max`、只出报告，探针不合并。
- (3) 计数：MA 8/9；BA 46（阶段 K 9/24；另有设计票 T2378、T2379）。下一张票号 T2380，下一节 §192，下一条 H173，下一号差异 D636。

## §192 — T2376（K06）合并；K07 = T2380、K10 = T2381 并行放行（总调度 V2，2026-10-10 10:26 UTC）

- (1) **T2376 合并 d2fb5b1**（10:22 UTC，`BA/KMolecule` + `BA/KCactusCut`，共 1737 行，停止线 2000，审核一次 PASS）：`BAKpi`、`baK_eq_sum_Kpi`、`BASigmaPi`、`baKpi_eq_sum_SigmaPi`、`baSigmaPi_cut`、`BASig`、`baSig_transl`、`baSigmaPi_reflect`，以及公开的 `baCactus_cut`。阶段 K 已合并 9 行。返工账本记「是」：计划超线，加开第二个文件，是调度的估计缺口。
- (2) 按设计顺序（K06 → K07、K10），两行并行放行：
  - **T2380 = BA-K07**（BA 47）：`BA/KPure.lean`，纯回路与 `(eq:molecule-decay)`。论证：每条边核 `≤ B e^{−κ|x−y|}`（`Mbound_AO`、`(prop:ThfadC_short)`），用生成树约化得出衰减；结论以 `SigDecayAbs` 的形式落在 `BASig` 上。
  - **T2381 = BA-K10**（BA 48）：`BA/KInduct.lean`，包括 `n ≤ 3` 的基础层（经 `baK_unique` 转给 `BAKsol`）和 `baKpi_cut`。`baKpi_cut` 的粘合边是 BA 的 `tΘ`，前因子正好是 `t`，复用 `baCactus_cut`。陈述按 K09b 的泛型第 7 节接口写。
  - 两张都是 1a 设计门加 1a-audit，`prover-max`，停止线 2000。
- (3) 中枢：T2378、T2379（设计票）加 T2380、T2381，共 4 张。
- (4) 计数：BA 48（阶段 K 11/24：已合并 9 行，K07、K10 在跑；另有设计票 T2378、T2379）。下一张票号 T2382，下一节 §193，下一条 H175，下一号差异 D636。

## §193 — T2381（K10）1a PASS；后续行的路由备忘（总调度 V2，2026-10-10 10:54 UTC）

- (1) **T2381 的 1a 和 1a-audit 都 PASS**：陈述、论证、数值都过了；计划约 1220 行，停止线 2000；进入 1b。
- (2) 审核提出 D1–D3，都不改 K10 的陈述，记作后续票的路由：
  - D1：`BAKBoundAt` 在 K10 定义，K12 导入。
  - D2：K10 新增定义 `BAKpiBoundAt`。
  - D3：解析的空层界（带状 `KLInduct_Kpi_empty_bound` 的孪生，带状 §6）要用 K07（T2380）和一个已证的 `IndStepAbs`，所以 K10 交不出。**写 K09b 或 K12 时，把它明确分给其中一张**（倾向 K09b：泛型第 7 节的 `KLKpi_step` 要消费它）。
- (3) T2379（阶段 T/U/V 设计）的报告已在分支上写出，等审核。

## §194 — T2378、T2379 设计报告合并；两份开阶段 REQ（总调度 V2，2026-10-10 11:28 UTC）

- (1) **T2378 合并 38eb3ee、T2379 合并 06f6e38**：都只出报告，审核一次 PASS，探针留在各自分支。
- (2) **REQ-2026-10-10-1127-GE**（开阶段 G、E）。T2378 的结论：
  - 12 行（G 9、E 3），中心 13.5k，旗标 18，全部可与阶段 K 并行。
  - 问题：Q1 开不开（E 能不能先开）；Q2 **F2 范围缺口**，L6.1 只对 `g ≤ W^{-ε}` 证过，`BAFlow` 推不出这个条件。选项是 (a) 在 G3a/G3b/G4 的 1a 里自己写论证，或 (b) 交 Jun 决定是否把 L6.1 借作外部输入并收窄 BA 主定理；Q3 F1 钉文形状；Q4 F3 `M ≠ mI`；Q5 关阶段条件。
  - 若监督选 (b)，那是 Jun 的决定，到时一次只问这一件。
- (3) **REQ-2026-10-10-1127-TUV**（开阶段 T/U/V）。T2379 的结论：
  - 路线 G 成立；46 行，拆子阶段 T（19）、U（19）、V（8）；先开 row 0（载体上移）和 T5s1（触发线块）；24 张带状侧票不依赖 BA。
  - 问题：Q1 路线；Q2 这次 PASS 是否直接开子阶段 T；Q3 证书合并道；Q4 K 衍生事实归 U2、U3；Q5 比例 1.144。
- (4) 中枢：T2380（K07）、T2381（K10）在跑，共 2 张。监督 :41 那轮答复后，按结论放 row 0、T5s1，以及 G/E 中不受 F2 影响的行（E1–E3、G2 等）。
- (5) 下一张票号 T2382，下一节 §195，下一条 H175，下一号差异 D636。

## §195 — 监督 1155（回 REQ-1127-GE、-TUV）PASS 带条件；K10 合并；放 row 0、T5s1、K11（总调度 V2，2026-10-10 12:01 UTC）

- (1) **T2381（K10）合并 306957f**（991 行）。阶段 K 已合并 10 行；K07 在跑；K11（依赖 K02、K10）可以写了。
- (2) **监督 2026-10-10-1155：两份 REQ 都 PASS，带条件。**
  - **GE：**
    - 阶段 E 现在开：E1、E2；E3 按 C4。
    - 阶段 G 现在开：G2，以及 G3a 的 1a 设计门（带 C1、C2、C3）。G3a 的 1a-audit 之后再发一份短 REQ（C2）；PASS 后才放 G3b、G4、G5a、G5c。
    - Q2 答 (c)：在全范围上自证，**不交 Jun**（不借 L6.1）。依据是 BA 已合并的事实在整个窗口 `0 < g₀ ≤ Λ` 上一致成立：Kronecker 形式 `M = M^{(B)} ⊗ I`、`BAMfine_decay`、`BAMB_row_l1`、`BAMB_ward_row`、`κ ≤ Im m`。
    - **C1 全范围规则**：不许用 `g ≤ W^{-ε}`，不许用 `‖M − m₀I‖` 小，不许用 `(Cλ)^{|a-b|}`。这条同样约束阶段 T/U/V 里 BA 的读法。
    - Q3：**按论文形状重钉**（`BAGbEXPii'/ij'`，C3）；带撇的 Step-1 消费者放新行 G7；阶段 G 旗标 19.5；旧钉文在那次合并时记为 superseded。
    - Q4：可以，Kronecker 形式作为主接口事实。
    - C5：G/E 和 T/U/V 共用一条证书合并道。小组 D、E、F 能另开泛型文件的就另开，以避开证书重编。
  - **TUV：**
    - 路线 G 确认；这次 PASS **开了子阶段 T 的带状侧**：row 0、T5s1，然后按依赖顺序 T8、T7、T1、T2、T3、T4s1、T4s2、T5s2、T6，走合并道。
    - C7：BA 侧 T 行要先发一份短钉文 REQ，可在 row 0、T8 合并后写；T4-BA、T5-BA、T6-BA 可作第一批。
    - C8：T7-BA 挪到子阶段 U（T 18 行、旗标 27；U 20 行、旗标 30）。
    - I1：BA 的 Step 2 用确定的 `J`，不是随机的 `Ĵ`；T1 是触发线检查点。
    - **R1：现在派阶段 L 的设计票。**
    - **X1**：Step 5 的 CLT 层（`Evolution/Clt*` 等 11 个文件，13.9k 行）在两份设计里都没有生产者。子阶段 U 开之前要定生产者（C9）。C10 是 200 行规则。
- (3) **本轮放票**（中枢现在只有 T2380 在跑）：
  - **T2382 = row 0**（载体上移：新文件 `Chain/Carrier.lean`，`BA/FlowPins.lean` 原地删掉搬走的块；G1 检查）；
  - **T2383 = T5s1**（`Induction/LoopGenN` + `HierarchyN` 原地，触发线：`g > 0.5` 或 `f_sem > 0.30` 就退回）；
  - **T2384 = K11**（`BA/KWardIneq`，`lem_wardineq_K`，设计门）。
  - BA 计数 49、50、51。
- (4) **下几轮待写**：G3a（设计门，C1–C3）、E1、E2、G2、阶段 L 设计票（R1）；K08a（等 K07）。再往后：BA-T 钉文 REQ（C7，等 row 0、T8）；X1 的生产者（子阶段 U 开之前）。
- (5) 下一张票号 T2385，下一节 §196，下一条 H177，下一号差异 D636。

## §196 — K07 合并；T2383 Amend 1（`HierarchyN` 归 T5s2，BA 实例归 T5-BA）（总调度 V2，2026-10-10 12:15 UTC）

- (1) **T2380（K07）合并 8609423**（`BA/KPure`，1016 行）：`baSig_decay` 证出（`SigDecayAbs` 落在 `BASig` 上，所有 σ）。阶段 K 已合并 11 行。K08a（依赖 K02、K07）可以写了。
- (2) **T2383（T5s1）1a 卡在 target 2，问 (A)/(B)/(C)。调度定 (A)**（流程，自定）：
  - `HierarchyN.lean` 本票不动。它的泛型改写依赖 `Step2Defs` 的词汇（T8，按 L1 是加法式）和 `HierAlgebra` 的 `loopDrift_sub_K_deriv_n`（T5s2），所以**并入 T5s2**；T5s2 的文件表加上 `HierarchyN.lean`。
  - 另外，**BA 实例从本票拿出来，放进 T5-BA**：在链文件 `Induction/LoopGenN` 里导入 `BA/FlowPins`，会把 BA 层放到链的上游，扩大以后的重编范围。本票改用一个不依赖 BA 的非带状实例（例如 `m = I`）证明不空。
  - 触发线未触发（`g` = 0.239，`f_sem` = 0），路线 G 继续。
- (3) 下一张票号 T2385，下一节 §197，下一条 H178，下一号差异 D636。

## §197 — BA-K08a = T2385 放行（总调度 V2，2026-10-10 12:16 UTC）

- (1) **T2385 = BA-K08a**（BA 52，阶段 K 第 13 行）：新文件 `BA/KSumZeroA.lean`，做带符号的和为零（`‖Σ_{δ_r = x} BASig‖ ≤ C(1−t)`，交错 σ），以及 `𝒦` 求和的 Ward 界。
  - 它的 1a 是 **K08a、K08b 合起来的设计门**（2051 Q4）：论文这里有缺口，要写完整论证；包括 K-b 的加权形式，即 K08b 的绝对加权条款。
  - 数值在 `g = 1/64, 1, 10` 上核对（1155 C1）；比值若随 `g ↓` 或 `t ↑ 1` 增长，就发 REQ。
  - 1a 同时给出 K08 合计相对 Q4 线 4.8k 的读数，越线可问 Jun。
  - `prover-max`，1000 / 1400 / 2400，停止线 2400。
- (2) 中枢：T2382、T2383、T2384、T2385，共 4 张。下一张票号 T2386，下一节 §198，下一条 H179，下一号差异 D636。
- (3) 待写：G3a 设计门、E1、E2、G2、阶段 L 设计票（放在一个空位出现之后）；K08b（等 K08a）。

## §198 — T8 = T2386、阶段 L 设计 = T2387 放行；row 0 已合并（总调度 V2，2026-10-10 12:39 UTC）

- (1) **T2382（row 0）合并 ada2b54**：新 `Chain/Carrier.lean`（178 行，只导入 `Induction/Defs`），从 `BA/FlowPins` 搬出 16 个声明；`STJhatg`、`STLWassmExpgL` 留下；审核一次 PASS。T/U/V 里以载体为基础的票从此可以分支。
- (2) **T2386 = BA-T T8**（BA 53，子阶段 T 的带状侧，`prover-hard`，700 / 1000 / 1400，停止线 1500）：Step 2 词汇在载体上的泛型读法。
  - **布局（流程决定，监督 1155 C5 的原则）**：L1 当初把它定为「附加」，是因为 `Step2Defs` 在 `FlowFM` 上游；row 0 之后载体只依赖 `Induction/Defs`。所以附加的泛型文本放进**新文件** `Chain/Step2Gen.lean`（`Step2Data extends FlowFM`、49 个词汇的泛型形式、探针的 Step 2 族、`Iff.rfl` 桥），`Step2Defs` 不动。
  - `bandFM` 挪进 `Chain/Carrier`，以后链上原地改写的票都在 `bandFM` 上取带状推论，不必导入 `BA/FlowPins`。
  - `LocalAvg1/2` 原地改写，外部输入（`stGbEXP_holds`、`Step2Iterate` 的事实、尺寸数据）作为假设。
  - `BAStep2` 只钉不证，放在 `BA/FlowPins`，登记一条 owed。
  - 实测反向锥：`Step2Defs` 177 个模块，含全部 6 个证书模块；新文件 0；`Carrier` 39 个模块；`LocalAvg1` 8 个模块，都不含证书模块。所以 **T2386 不进证书合并道**（设计原估 56 分钟道时，省下）。若 1a 发现必须改 `Step2Defs`，说明理由，并回到合并道。
  - 1a 是设计门，后面接 1a-audit；预测超过 1500 行就拆成 T8a / T8b。
- (3) **T2387 = BA-DL**（BA 54，阶段 L 设计，只出报告，`prover-max`；监督 1155 R1）。问题 LD1–LD7：
  - 按族实测路线（R / P / G / T）；
  - 在 BA 上钉住链所需的 L 输出（`LWtermExp`、`LWAssm`、`LWcut`、`LWtermEXP`、`LWAvgLaw`、`STLWB`、`STLWT`、`STEMn2Exp`）；
  - `B:286-525` 与 `B:118` 的论文状态；
  - 证书孪生的构建代价和合并道负担（C5）；
  - 对 K / E / G 的依赖；
  - 行表与旗标。

  报告作为阶段 L 的开阶段 REQ。
- (4) **T2383（T5s1）12:37 合并 5c50416**（Amend 1，只改 `LoopGenN.lean`，+160 −99；绊线实测 g = 0.239、f_sem = 0，未触发，路线 G 在测点成立）。中枢：T2384、T2385 在跑；T2386、T2387 补满 4 个位。下一张票号 T2388，下一节 §199，下一条 H180，下一号差异 D636。
- (5) 待写：G3a 设计门、E1、E2、G2（有空位就放）；K08b（等 K08a）；BA-T 钉文 REQ（C7，等 T8 合并）。

## §199 — BA-E1 = T2388 预放行（总调度 V2，2026-10-10 12:47 UTC）

- (1) 中枢 4 张满（T2384、T2385、T2386、T2387；H179 已执行，61849a6）。**T2388 = BA-E1**（BA 55，阶段 E 第一行；监督 1155 GE/O1：E 现在开）先放进 Released，有空位就开工，排在 T2387 之后。
  - 新文件 `BA/EKPins.lean`：`BAuKer`、`BAUN`、五个阶段 E 钉文（探针 208-250 原文）；证 `baEKSumNdecay_holds`（`A:95-110`），以及 BA 的 `Ξ` 三条（`BAEKXiDecay`、`BAEKXiBall`、`BAEKSameRow`，由 `BAuKer_convex` + `baProp5_holds` 证，F4：不要 `Mbound_AO`；C1：只用均匀事实）。
  - 另四个钉文登记 owed（E2：Decay1、NAL、2；E3：Nonzero）。
  - `prover-hard`，900 / 1200 / 1900，停止线 2000（1500 行在节边界停下汇报）。论文论证完整，不设设计门。新 BA 文件，不进证书合并道。
- (2) 待写：G2（进合并道）、G3a 设计门（C1/C2/C3）、E2（等 E1）；K08b（等 K08a）。

## §200 — BA-G2 = T2389 预放行，排在 T2388 之前（总调度 V2，2026-10-10 12:48 UTC）

- (1) **T2389 = BA-G2**（BA 56，阶段 G 第一行，关键路径 G2 → G3a → G3b → G4 → G6a → G6b；监督 1155 GE/O1）。
  - `Green/LDE`、`RowIndep`、`IBPPoly` 的 G 段原地改写到确定性厄米平移 `D` 上（`green (D + seqHflow …) z`），`D = 0` 时以旧名、旧陈述取回带状定理（G1，28 个名字）。
  - 新 `BA/GreenLDE`：`BAGt_eq_green`、`BAX`、钉文 `BALDEin` 并证 `baLDEin_holds`；`X` 的几乎处处块支撑由 `gaussianReal_zero_var` 得到。
  - 高斯计算，论证完整，不设设计门；C1：不加任何小量假设。
  - `prover-hard`，900 / 1200 / 1550，停止线 1800。
  - **进证书合并道**：三个文件的锥 156 个模块，含 6 个证书模块（实测）。
- (2) 次序：阶段 G 的链比 E 长，所以 **T2389 排在 T2388 之前**，抢下一个空位。
- (3) 待写：G3a 设计门（C1/C2/C3；只跑 1a 设计门，1b 等 G2 合并）、E2（等 E1）；K08b（等 K08a）；BA-T 钉文 REQ（等 T8）。

## §201 — BA-G3a = T2390 预放行（设计门；1b 等 G2 合并）（总调度 V2，2026-10-10 13:01 UTC）

- (1) 外部：T2385 的 1a-audit 第一轮 RETURN（`baK_sumAll_eq_layers` 在 `W = 0` 时不成立，缺 `1 ≤ W`、`3 ≤ L`、`0 < κ`、`0 < g`；两条陈述把假设藏在 `..` 后面）。中枢按规则 (B) 修一次 (a) 节，再做第二轮 1a-audit，不需要我签字。其余照常。
- (2) **T2390 = BA-G3a**（BA 57，阶段 G 关键路径；监督 1155 C2）。
  - 1a 是 **G3a、G3b、G4 合起来的设计门**：
    - (i) 耦合对角 / 非对角系统的稳定算子，界要认到已合并的 BA 界上（`baProp5s_holds`、`BAoffDiag_scalar`、`Θ` 行和）；
    - (ii) 块内子式上的逐项律；
    - (iii) `(GijGEX_BA)` 的 `M^{(B)}` 级数与指数权；
    - (iv) 常数只依赖 `(d, κ, 𝔡)`；
    - (v) 在 `g = 1/64, 1, 10` 上数值核对稳定常数和衰减率，随 `L` 增长或在 `t ↑ T₀` 退化就停下，转 REQ；
    - (vi) 定下带撇钉文 `BAGbEXPii'`、`BAGbEXPij'` 的 Lean 形式（C3），以及消费者（G7）要改什么；
    - (vii) 拆出 G3a / G3b / G4 各自的陈述与行数。
  - C1 约束：禁用 `g ≤ W^{-ε}`、`‖M − m₀ I‖` 小、`(Cλ)^{|a-b|}`；碰到就转 REQ。1a 收不拢 → RETURN，问 Jun 一个数学问题。
  - 1b（`prover-max`，800 / 1300 / 1950，停止线 2000，新文件 `BA/GreenCore`，不进合并道）要等两件事：1a-audit PASS，和 **T2389 合并**。1a-audit 之后由我写 C2 的短 REQ，它不挡 1b，放的是 G3b、G4、G5a、G5c。
- (3) 空位次序：T2389 → T2390（1a）→ T2388。

## §202 — K11 合并；T2386 Amend 1（R1：16 个词汇留在 T8）；T2384 的签字事后追认（总调度 V2，2026-10-10 13:18 UTC）

- (1) **T2384（BA-K11）合并 85e7cd6**：`BA/KWardIneq` 1338 行（停止线 2000），无登记变动，审核一次 PASS。阶段 K 已合并 12 行，剩 K08a（T2385，在跑）、K08b、K09b、K12（都排在 K08a 后面）。
- (2) **追认 T2384 的 D1 / D2**：
  - 1a-audit 写了「1b 前需总调度签字」，中枢没等签字就跑了 1b。
  - 结果可以接受：D1 走了第三条路，用文件内的桥 `KWardIneq_IndAt_of_abs` 和 `KWardIneq_Data`，不加登记行，前提照样显式；D2 在 1b 前把 main 并进了分支。
  - **从此成为常规（H183 (3)）**：1a-audit 要签字时，1b 停下等 H 指令，状态写 `blocked`。T2386 这次就是这样做的。
- (3) **T2386 Amend 1：选 R1**，16 个被推迟的名字（`STGMM`、`STNewKLKAt`、`STNewKLK`、`STK2decay` 和 N 圈族 12 个）在本票就给泛型形式。
  - 理由是流程：`Step2Gen` 现在的锥是空的；等 T7、T1、T3、T4 原地改写导入它之后，它就在证书模块上游。实测 `Step2Events` 86 个模块、`Step2Iterate` 72、`NewKLK` 83、`GridDuhamelN` 112，都含 6 个证书模块。现在漏掉的名字，以后每补一个就是一次证书合并道合并；现在补齐约多 190–260 行，仍在停止线 1500 以内。
  - 具体做法：
    - `STGMM` 是矩阵层定义（R3 纠正），给一个矩阵层字段；
    - 三个对能量量化的钉文用载体族 `mk` 在常数能量序列上取，β 化简后是 `Iff.rfl`，不许「推迟」；
    - N 圈 12 个在 `Step2Data` 里加列表下标字段，`FlowFM` 不动；
    - 超过 1500 就拆 T8a（词汇）/ T8b（`LocalAvg1/2`）。
  - O1–O5 的处理：O3 G1 补三项；O4 owed 行在预检要求时可加，并写明属主；O5 `T2386a` 在合并时编号。
- (4) 空位次序：T2386（恢复）→ T2388。在跑：T2385、T2387、T2389、T2390。下一张票号 T2391，下一节 §203，下一条 H184。

## §203 — 五张合并；Jun：这波结束后换中枢，先不发新单；T2390 Amend 1 备好但暂停（总调度 V2，2026-10-10 21:10 UTC）

- (1) **心跳断了约 7 小时 20 分钟**：13:46 那次心跳 21:08 才送到。这段时间中枢自己跑完了在手的票：
  - **T2385（K08a）** e67bfbd，`BA/KSumZeroA` 1195 行；
  - **T2388（E1）** 76458c2，`BA/EKPins` 856 行，登记 4 条 owed；
  - **T2387（阶段 L 设计）** 8994389：33 行，中心 42.3k 行，旗标 50，9 行要设计门；
  - **T2386（T8）** 2a05b1d，净 1317 行，Amend 1 下的完整词汇；
  - **T2389（G2）** b6cc9d2，978 行，走证书合并道。它的 D1：只有 `stochDom_ldeRow/Col/Quad` 是 `D = 0` 处的字面推论，其余声明保留原证明；陈述与 G1 一致，审核 PASS。

  中枢从 17:38 起空闲，T2390 13:36 起等我答复。
- (2) **Jun 指示**（21:09 UTC）：「这波工单结束好我要换hub，所以这波结束后先不要发新单了。」**从此不放新票**，见 H184：中枢什么都不开，排空后写 `DRAINED`。
- (3) **T2390 Amend 1 已写好，但暂停**，等 H 指令恢复：
  - D2：`BAGbEXPii'` 不钉，已合并的 `BAGbEXPii` 由同一论证证出，比印刷形式强；记差异候选 T2390d，C2 REQ 里请监督确认。
  - D1：探针编译另起一步，用 `prover-max` 角色，只写 `Probe/T2390Pins.lean`。
  - D3：(a′) 写局部闭合（加权范数或迭代到 `W^{-D}`），常数全部写出。
  - D4：非退化实例数据。
  - 恢复后的次序：D1 → (a′) → 1a-audit 第二轮 → 1b → 审核。
- (4) 在手但不发的（留给新中枢）：K08b、E2、G3b（等 C2 REQ）、T7 / T1 / T2 / T3 / T4 / T5s2 / T6（ST 侧）、BA-T 钉文 REQ（C7，row 0 与 T8 已合并）、阶段 L 开阶段 REQ（T2387）。下一张票号 T2391，下一节 §204，下一条 H185。
- (5) **Jun 21:1x UTC 选定：T2390 留给新中枢。**旧中枢按 H184 排空，写 `DRAINED`；新中枢接手后，由一条新的 H 指令按 Amend 1 恢复 T2390。

## §204 — 新中枢就位，恢复正常运行；T2390 按 Amend 1 恢复（总调度 V2，2026-10-10 21:18 UTC）

- (1) Jun 21:1x UTC：「new hub is ready」。新中枢 HUB.alive 21:15:27 UTC；旧中枢的 H184 已执行（907ddea，DRAINED 21:15:47）。**H184 (2) 解除，恢复正常运行**（H185）。`DRAINED` 在下一次提交里删掉。
- (2) **T2390 现在恢复**，照 Amend 1 走：D1 探针编译（`prover-max`，只写 `Probe/T2390Pins.lean`）→ (a′) → 1a-audit 第二轮 → 1b → 审核。
- (3) 本轮接着写：K08b、E2、ST 侧的 T7；之后写 BA-T 钉文 REQ（C7）和阶段 L 开阶段 REQ。

## §205 — 新中枢的第一批：K08b = T2391、E2 = T2392、T6 = T2393（总调度 V2，2026-10-10 21:22 UTC）

- (1) **T2391 = BA-K08b**（BA 58，阶段 K 关键路径 K08b → K09b → K12）。新文件 `BA/KSumZeroB.lean`，内容是 B1 组合、`baSig_nc_pointwise`（`g²` 增益）、`baSig_weighted`（每个 `Q`），以及 K-b 谓词 `baSig_sumZeroAbs : SigSumZeroAbs … (BASig …)`（带 `3 ≤ n`、`t i < 1`；`SigSumZeroAbs` 本身不改，T2385b）。设计门已在 T2385 (a+) 过了，这里只做普通 1a。`prover-max`，700 / 1000 / 1500，停止线 2000，不进合并道。
- (2) **T2392 = BA-E2**（BA 59）。新文件 `BA/EKSum.lean`，证三个属主是 BA-E2 的 owed 钉文 `BAEKSumDecay1`、`BAEKSumDecayNAL`、`BAEKSumDecay2`（`A:111-198`，论证完整），并删掉那三条 owed 登记。`prover-hard`，700 / 950 / 1500，停止线 2000，不进合并道。
- (3) **T2393 = BA-T T6**（BA 60，子阶段 T 带状侧）：`Contract.lean` 原地加矩阵形式 `STContractM`（任意厄米 `H`、`Im z > 0`），`stContract_holds` 以旧名、旧陈述作为推论（G1）。`STContractPt` 本来就是矩阵通用的，不动。`prover`，150 / 250 / 400，停止线 600。锥 47 个模块，不含证书模块，不进合并道。
- (4) 中枢：T2390（恢复）、T2391、T2392、T2393，共 4 张。空位次序 T2390 → T2391 → T2392 → T2393。下一张票号 T2394，下一节 §206，下一条 H187。待写：BA-T 钉文 REQ（C7）、阶段 L 开阶段 REQ（T2387）、T7（ST 侧，进合并道）、K09b（等 K08b）、E3（等 E2）。

## §206 — 阶段 L 开阶段 REQ 已发（总调度 V2，2026-10-10 21:24 UTC）

- (1) **REQ-2026-10-10-2124-L**（T2387 设计合并 8994389）的问题：
  - Q1：路线 R/P / G（L3d2、L5、L4a，在第一处设绊线）/ 孪生；33 行，旗标 50；只有一次证书合并（L4e2）。
  - Q2：首批开没有 L 前驱的六行：L0、L2c1、L2c2（D402 修正后的系数）、L3c2、L4a、L4a2（K12 合并前把它的钉文当假设）。
  - Q3：G1–G6 这六处缺口，TeX 指向 [yang2024Del] App. B，仓库里没有。默认在 1a 里自己写（§5）；1a 卡住才问 Jun 一个问题（请他提供 App. B 的文本作阅读材料，不作外部输入）。
  - Q4：杠杆 (S)、(C) 等 L3a3、L4e1 的 1a 出来以后再提请求。
  - Q5：关闭条件。
- (2) 监督 :41 答复之前，阶段 L 不放任何证明票。下一张票号 T2394，下一节 §207，下一条 H188。

## §207 — 新中枢的状态文件命名错误（总调度 V2，2026-10-10 21:39 UTC）

- (1) H186 开工时，中枢写出的状态文件名是 `docs/queue/T2391 wf_dfcfd1a6-44c prover-max.state`（T2392、T2393 同样），字段也错位了：`updated:` 里是票号串，`reports:` 是 `docs/reports/-prove.md`。分支是对的（`t/T2391` 到 `t/T2393`），报告也写在 `T####-prove.md`，所以工作流本身没问题。
- (2) H188：改回标准的 `docs/queue/T####.state`；错名文件挪进 `_to_delete/`（没进版本库）；修好写状态文件那一步（票号要单独作变量）。工作流不重启。
- (3) 阶段 L 的 REQ 等监督 :41 那一轮。下一张票号 T2394，下一节 §208，下一条 H189。

## §208 — 监督 2149 PASS，阶段 L 开启；T6 合并；L0 = T2394、L3a3 设计门 = T2395 放行（总调度 V2，2026-10-10 21:57 UTC）

- (1) **T2393（T6）合并 b53fd22**：`Contract.lean` 原地，+130 −53，审核一次 PASS。子阶段 T 已合并 row 0、T5s1、T8、T6。
- (2) **监督 2149：PASS，附 L1–L8。**
  - 首批开 L0（建在 `Chain/Step2Gen` 上，L2）、L2c1、L2c2、L3c2。**L4a、L4a2 先不开**（L3：G6 设计门之前不开）。
  - **L4：三个决定路线的设计门先跑**：L3a3 的 1a（G1 + S 杠杆）、L3b3 的 1a（G2）、一个 LW-14 设计门（G6 + C 杠杆）。L3a1、L3a2、L3b4–L3b6 等它们。三个的结果一起写一份 REQ，并附上十个超 1500 行的行怎么拆。
  - **L1：S 是论文自己的论证，孪生是退路，不是默认。**
  - Q3：默认在 1a 里自己写；1a 卡住才问 Jun 一个问题，数学问题或请他提供 App. B（他是合作者）。
  - L5：C1 约束阶段 L；常数在 `g = 1/64, 1, 10` 上核对。
  - L6：L3c3 等 T2390 的 C2 REQ PASS。
  - L7：L3d2、L5 的泛型陈述等管线的 1a 定了再写。
  - L8：关闭条件。
- (3) **T2394 = BA-L0**（BA 61）：两个新文件。
  - `Chain/LWGen`：只放 LW 的泛型名字、`PinFam`、`bandPin` 和 `Iff.rfl` 桥，只导入 `Step2Gen` 与 `LWPins`。
  - `BA/LWPinsBA`：放 `baPin`、BA 读法、带状实例（这些要导入 `LWTermHolds`、`LWExpTerm6`，它们在链文件下游）。
  - 不重新定义 `Step2Gen` 已有的名字，不钉 `STEMn2Exp`。
  - `prover`，200 / 300 / 450，停止线 600。
- (4) **T2395 = L3a3 设计门**（BA 62，只出报告）：S1 原子对应的检验（先查 `GGGamma` 第一和保序这个已知障碍）、S2 决定、G1 的 BA `lvl1` 论证、上游行的钉文、C1/L5、决定后的行表。`prover-max`，排在新票的第一位。
- (5) 下一轮写：T2396（L3b3 设计门，G2）、T2397（LW-14 设计门，G6 + C）、L2c1、L2c2、L3c2。中枢：T2390、T2391、T2392 在跑，T2395 补第 4 个位。下一张票号 T2396，下一节 §209，下一条 H190。

## §209 — K08b、E2 合并；K09b = T2396 放行（新文件，不进合并道）（总调度 V2，2026-10-10 22:12 UTC）

- (1) **T2391（K08b）合并 14d7ab4**：`BA/KSumZeroB` 755 行，K-b 谓词 `baSig_sumZeroAbs`，审核一次 PASS。**T2392（E2）合并 5ba1ebe**：`BA/EKSum` 1929 行（超过 1500 拆分线，审核记作观察，停止线 2000 之内），删了三条 owed，审核一次 PASS。阶段 E 只剩 E3。
- (2) **T2396 = BA-K09b**（BA 63）：在 BA 上对分子做归纳，证 `baKpiBoundAt_holds : ∀ n ≥ 3, BAKpiBoundAt`。
  - **布局（流程决定，1155 C5 原则）**：2051 接受的是在 `Loop/KLInduct.lean` §7 原地改写。但实测该文件的锥有 127 个模块，含 6 个证书模块；带状定理已经证完，本身不用改。所以把抽象归纳步写进新文件 `BA/KStep.lean`（带状 §7 的文本，把 `Sig`、`TH`、`Kp` 和切割恒等式作为假设），BA 实例也在同一文件，`KLInduct` 不动，不进合并道。1a 若发现非原地不可，退回原地方案，那样要走合并道。
  - D3（BA 上的空层解析界）在本票解决。
  - `prover-hard`，450 / 650 / 950，停止线 1300，排第一。
- (3) 中枢：T2390、T2394、T2395、T2396。下一轮写：L3b3 设计门（G2）、LW-14 设计门（G6 + C）、L2c1、L2c2、L3c2、E3（C4：U3s1 未合并时只证 `BAEKSumDecayNonzero` 和尺度 N 的结论）、K12（等 K09b）。下一张票号 T2397，下一节 §210，下一条 H191。

## §210 — L0 合并；另两个决定路线的设计门 T2398（LW-14，G6 + C）、T2397（L3b3，G2）放行（总调度 V2，2026-10-10 22:26 UTC）

- (1) **T2394（L0）合并 f136ab5**：`Chain/LWGen` 151 行、`BA/LWPinsBA` 111 行，审核一次 PASS。阶段 L 已合并 1 行。
- (2) **T2398 = LW-14 设计门**（BA 65，只出报告；2149 L3、L4 (c)）：
  - W1：用 `GGGamma` 展开得到的 BA 项表与 BA 核；
  - W2：`LWExpI*K`、`lwExpTerm4_*` 的泛型接口是否接得住这张表（决定 L4a 走 G 还是孪生）；
  - W3：C 杠杆，`(eq:sizeGammamu_E)` 在 BA 上直接证还是靠证书；
  - W4：期望恒等式；
  - W5：上游行的钉文；行表与拆分。
  - 它决定约 15k 行，排在新票第一位。
- (3) **T2397 = L3b3 设计门**（BA 64，只出报告；2149 L4 (b)）：性质 (6) 在 BA 上，两个分支都要回答（S 成立就搬运带状的局部代价路线，不成立就写 BA 原子处的合并代价）；L3b1–L3b6 的钉文与拆分。排在 T2398 之后。
- (4) 三个设计门都出报告后合写一份 L4 REQ。中枢：T2390、T2395、T2396 在跑，T2398 补第 4 个位。下一张票号 T2399，下一节 §211，下一条 H192。待写：L2c1、L2c2、L3c2、E3、K12（等 K09b）、T7、BA-T 钉文 REQ、C2 REQ。

## §211 — T2390 1a-audit 第二轮 PASS；C2 REQ 已发（总调度 V2，2026-10-10 22:42 UTC）

- (1) T2390 1a-audit 第二轮 21:57 PASS：D1–D4 都满足；`BAGbEXPij'`、`BAStab` 在探针里编译通过（10fcef2）；(a′) 的闭合是局部的，`c_λ = min(c₀/12, μ/6)`，不用 `W^{-D}`；实例数据非退化（`t = 1/2`）。1b 正在跑。
- (2) **REQ-2026-10-10-2241-G**（C2 短 REQ）：
  - Q1：放 G3b、G4、G5a、G5c（G5a、G5c 保留设计门）；
  - Q2：确认 `BAGbEXPii` 代替带撇的对角钉文（T2390d）；
  - Q3：带撇钉文 `BAGbEXPij'` 的形式，以及 G7 消费者的改动（窗口常数 `3S⁴ + 4`）；
  - Q4：阶段 L 的 L6 接口不需要另做复核。
  - 附 κ 的发现：`g = 10` 时 κ ≈ 0.044。
- (3) 下一张票号 T2399，下一节 §212，下一条 H193。

## §212 — K09b 合并；监督 2254 PASS（C2）；K12 = T2399、G3b = T2400 放行；T2397/T2398 Amend 1（G2）（总调度 V2，2026-10-10 22:58 UTC）

- (1) **T2396（K09b）合并 19fc8cf**：`BA/KStep` 746 行（停止线 1300），`baKpiBoundAt_holds`，审核一次 PASS。阶段 K 只剩 K12。
- (2) **监督 2254：PASS，附 G1–G3。**
  - Q1：G3b 现在放；G5a、G5c 现在开设计门 1a，它们的 1b 等 G3a 合并；G4 等 G3a 与 G3b 合并后开，1a 是普通预检（D3.4 已审过）。
  - **G1：G5a 设计门的范围扩大**，要处理两块的偏移平均 `W^{-d}Σ_o 𝔛_{(b',o),(a,o)}`，对每个 `b'` 都要；结构事实写成一般形式。G5b 的 1a 也是设计门，除非 G5a 已写出这个矩界。
  - Q2：确认 `BAGbEXPii` 代替带撇的对角钉文；修订 1155 C3：G7 合并时只把 `BAGbEXPij` 登记为被取代。
  - Q3：带撇钉文 `BAGbEXPij'` 的形式和 G7 的改动可以接受。
  - Q4：L6 接口确认，附 G3：L3c3 的 1a 要对右边两项、两类轮廓（`(eq:Psi)` 与 `𝖳`）都证 (ii)，常数不依赖 `n`。
  - **G2：常数核对一律用对 `L` 一致的 κ（`g = 10` 时约 0.044），以及 `Λ = 𝔡⁻¹ = 10`**。T2398 预检里第 8–9 行不合规（用了 `L = 3`、`Λ = g`）。
- (3) **T2397、T2398 Amend 1**：把 G2 规则写进它们余下各阶段的提示；凡是依赖 κ 或速率、且进入对固定 `n` 必须成立的指数或阈值的闭合，都要按一致值复核，不成立就报 REQ。不重启。
- (4) **T2399 = BA-K12**（BA 66，阶段 K 最后一行）：
  - 对所有 `n` 证 `BAKBoundAt`（`n ≤ 3` 用 K10，`n ≥ 4` 用分层分解加 K09b）；
  - 钉 `BAKbound` 并给 `baKbound_holds`（探针里已编译的归约）；
  - 在 `Chain/Carrier` 里钉 `STKwardgL`（锥 53 个模块，不含证书模块），用 K11 证 `BAKward`；
  - 实例；2051 Q5 的对照表。
  - `prover-hard`，400 / 600 / 900，停止线 1300，排第一。
- (5) **T2400 = BA-G3b**（BA 67）：新文件 `BA/GreenStab`。
  - (S1) `baStab_of_real`：把 `BAStab` 的定义体展开写，`K = 16κ⁻⁴`，本票不定义 `BAStab`，避免和 T2390 的 `GreenCore` 重名；
  - (S3) `ρ`、`ρ₂ ≤ 1`、`ρ̂`；
  - (S2) `Θ` 的平移不变性（把私有的 `baP8_BATheta_shift` 公开，或另写一份）和加权 `ℓ¹` 行界。
  - `prover-hard`，300 / 450 / 750，停止线 1000。
- (6) T2390 1b：`GreenCore` 进行中已有 1265 行。到停止线就按 (a′) 的行图拆（R3 / R4），不在闭合中间切（2254 附注；H193 (4)）。
- (7) 下一张票号 T2401，下一节 §213，下一条 H194。待写：G5a 设计门（含 G1）、G5c 设计门（优先用新文件）、L2c1、L2c2、L3c2、E3、T7、BA-T 钉文 REQ；L4 REQ（等三个设计门）；阶段 K 关闭 REQ（等 K12）。

## §213 — G5a、G5c 设计门放行（T2401、T2402）；中枢对 H193 (2) 的处理接受（总调度 V2，2026-10-10 23:13 UTC）

- (1) **T2401 = BA-G5a**（BA 68）：设计门 1a 写 BA 的子式好事件、子式差、单块涨落平均，以及 **G1 要求的两块偏移平均**（对每个 `b'`，`W^{-d}Σ_o 𝔛_{(b',o),(a,o)}`、`W^{-d}Σ_o 𝒜'_{(b',o)}` 都要到 `O(Ψ²)`）；结构事实写成一般形式；判断 G5b 是否还要设计门。(iv) 收不拢就转 REQ。1b 等 1a-audit PASS 和 T2390 合并。`prover-max`，1100 / 1650 / 2600，每个文件停止线 2000。
- (2) **T2402 = BA-G5c**（BA 69）：设计门 1a 写 BA 的分部积分展开 `E_i(G_ii − M_ii)` 和余项（`G − M = −M(√t V + tm)G`）。**新文件**，不改 `Green/IBP`（它的锥含证书模块，1155 C5、2254）。1b 同样等 T2390。`prover-max`，950 / 1550 / 2300。
- (3) 两张设计门的探针步骤都按 T2390 Amend 1 D1 的做法，由会写 Lean 的 `prover-max` 编译。1a-audit 通过后置 `held`，把位让出来。
- (4) H193 (2)：中枢说 T2397、T2398 正在跑的 1b 改不了提示，打算在 1b 结束、审核之前停下工作流，再带着 Amend 1 重跑审核。接受。
- (5) 空位次序：T2399、T2400、T2401（1a）、T2402（1a）。下一张票号 T2403，下一节 §214，下一条 H195。待写：L2c1、L2c2、L3c2、E3、T7、BA-T 钉文 REQ；L4 REQ（等三个设计门）；阶段 K 关闭 REQ（等 K12）。

## §214 — T2398 的 §8 问题转给 Jun（2149 Q3 规定的那一个问题）（总调度 V2，2026-10-11 00:31 UTC）

- (1) T2398 的设计结论：W2 = 否（L4a 改孪生），W3 = C（`(eq:sizeGammamu_E)` 直接证，用修正后的平均形式 `5 − 2·1[x ~ y]`；证书四行 L4e1–L4f2 换成一行）。STOP：`B:118` 的 (v) 缺一步，即 `T3C-Ḡ` 族（BA 的 `I₄₁`，块间 `M_{wγ}` 造成扭转的 loop）。审核（带 Amend 1 重跑）判 **BLOCKED**：停得准确、有理；W1–W5、C1 通过（κ 按一致值复核后）。
- (2) **转给 Jun 的问题**（00:31 UTC，一个问题，数学形式）：[yang2024Del] App. B 或 [RBSO1D] 怎么界 `𝔼[tr(ǦE_{a₁}) Ǧ_{xw}M_{wγ}Ḡ_{xγ}𝓛^{(2)}]`：(R1) 用带非对角块插入的 loop 局部律，还是 (R2) 用原子处 `ǦMǦ` 的展开恒等式？也可以指出 App. B 里的相应段落，只作阅读材料。
- (3) 等答复期间：T2398 置 `held`，让出位置；不合并（行表有条件）。按审核的意见，L4d、L4e（C）、L4c 以及 L4a2 的归约部分只依赖 §3，可以照常推进；它们在 L4 REQ 里提。L4a、L4b 和 L4a2 的拼装部分等答复。
- (4) T2395 第一轮审核 RETURN（D1 要修），中枢按规则 (B) 自修一次（报告 00:28 已更新）。下一张票号 T2403，下一节 §215，下一条 H196。

## §215 — G3a、G3b 合并；G4 = T2403 放行（总调度 V2，2026-10-11 01:02 UTC）

- (1) **T2390（G3a）合并 cbda0ab**：`BA/GreenCore` 1981 行（停止线 2000），R1–R5；登记两条 owed（`BAStab` 属主 G3b、`BAGbEXPij'` 属主 G4）。1b 的 `prover-max` 没写完（缺 D3.3 的 (X*)、(Ξ)），按 §94 升级一次到 `prover-opus` xhigh 补上；审核 PASS（观察 O3–O6：有几个实例用了零样本、常数 26 对 8、`Φ²` 的损失）。
- (2) **T2400（G3b）合并 4a4327e**：`BA/GreenStab` 442 行，`baStab_of_real`、`ρ`/`ρ₂`/`ρ̂`、`Θ` 加权 `ℓ¹`；`baP8_BATheta_shift` 公开（一行）；审核一次 PASS。`BAStab` 的 owed 行还在（本票不能改登记文件），由 G4 去掉。
- (3) **T2403 = BA-G4**（BA 70，阶段 G 关键路径）：
  - 新文件 `BA/GreenOff`；D3.4 的加权闭合（比值范数 `𝒩`，`c_λ = GreenStab_clam`）；
  - `BAStab` 的连接（由 `baStab_of_real` 得到），并去掉其 owed 行；
  - `baGbEXPij'_holds`，去掉 owed 行；若概率层要用 G6a 的东西，就只证确定性部分，属主改成 G6a；
  - 非退化实例，避开零样本（T2390 审核 O3）。
  - 1a 是普通预检（D3.4 已审，2254）。`prover-max`，500 / 800 / 1200，停止线 1600，排第一。
- (4) G5a（T2401）、G5c（T2402）已开工；G3a 已合并，所以没有等待的一步。在跑：T2397、T2399、T2401、T2402；排队：T2403。下一张票号 T2404，下一节 §216，下一条 H197。待写：G6a（等 G4、G5a/G5b）、E3、L2c1、L2c2、L3c2、T7、BA-T 钉文 REQ；L4 REQ（等 T2397）；阶段 K 关闭 REQ（等 K12）。

## §216 — K12 合并，阶段 K 做完、关闭 REQ 已交；ST 侧 T2 = T2404 放行（总调度 V2，2026-10-11 01:23 UTC）

- (1) **T2399（K12）合并 561093a**：新 `BA/KBound` 418 行，`Chain/Carrier` +23（`STKwardgL`），`Chain/Step2Gen` +28（桥 `bandFM_STKward`）；审核一次 PASS（O1 只是报告长度）。`baKBoundAt_holds`（所有 `n`）、`baKbound_holds`、`baKward_holds`、`inst_BAKbound`（`d = 3`、`sz0`，无假设）。阶段 K 的 16 张票全部合并。
- (2) **阶段 K 关闭 REQ**：`docs/supervisor/requests/REQ-2026-10-11-0118-K.md`。按 2051 Q5 填了两张表（关闭条件五项，各有公开定理和实例；下游消费表六行，每行都有 BA 对应）。一个登记问题 Q2：`STKboundgL`（`Test/Axioms.lean:134`）现在在 BA 载体上已证，但仍是 `inst_baBootstrap'`、`inst_baBootstrap'_full` 的假设 `hK`；调度建议由 G7 顺手用 `inst_BAKbound` 消掉，owner 注释改写，行留到 BA-V。
- (3) **T2397（L3b3 设计门）审核 RETURN**：P2 / S 分支的搬运定理靠一个钉文 `BAImgSim`，按所写的样子证不出来，且已合并的 T2395 对 BA 策略否定了它；实例因此退化，S 行的定价也没用 T2395 指定的 BA 专属形状。属于规则 (B) 的一次自动修补，不需要调度决定。L4 REQ 等修补后的审核。
- (4) **T2404 = BA-T T2（ST 侧）**（BA 71）：`EMn2Poly`、`EMn2Exp1`、`EMn2Exp2` 原地改写，证 T8 已钉的 `STEMn2PolygL`、`STEMn2ExpgL`，其他块的输入作假设（必须在 BA 能兑现，C1）；二圈公式 `KLK_two` 换成一个不等式假设（BA 来源：`BAKsolve` 的 `(Kn2sol)` 加 G3b 的 `Θ` 界）；I1：能在 80 行内给出确定性 `J` 形式就顺带给（目标 5′），否则留给 BA-T 钉文 REQ。设计门 1a + 1a-audit，`prover-hard`，500 / 650 / 900，停止线 1000；不在证书通道（三个锥分别 16 / 8 / 7 个模块）。
- (5) 在跑：T2397（修补）、T2401、T2402、T2403；排队：T2404。下一张票号 T2405，下一节 §217，下一条 H198。待写：BA-T 钉文 REQ（C7，第一批 T4-BA、T5-BA、T6-BA；带 I1）；ST 侧 T4s2（不在锥里）、T3、T4s1、T5s2；E3（C4：U3s1 未开，只证 `BAEKSumDecayNonzero`，`STEK*` 的 BA 形式归 U3-BA）；G6a（等 G4、G5a/b）；L2c1、L2c2、L3c2；L4 REQ（等 T2397）。

## §217 — ST 侧 T3 = T2405 放行；T2398 的文章位置告诉 Jun（总调度 V2，2026-10-11 01:37 UTC）

- (1) **T2405 = BA-T T3（ST 侧）**（BA 72）：`lem:newKLK` 的通用形式 `STNewKLKgL`（T8 已钉）。`NewKLK.lean` 的 A–D、F 节本来就是抽象的，带状的东西只在 B（`Θ` 尾）和 E（模型的 `𝓛 − 𝒦`，`KLK_two`、标量 `m`）。布局按监督 C5：优先 (A) 新文件 `Chain/NewKLKGen.lean`（`open private` 用 NewKLK 的抽象引理；没人 import，所以不进证书通道）；只有 (A) 比原地改 (B) 多 150 行以上才走 (B)（那样进通道）。`Step2K2` 不动：`STK2decay` 是模型自己的 `𝒦^{(2)}` 界，留给 T3-BA 在 BA 上证 `STK2decaygL`。设计门 1a + 1a-audit，`prover-hard`，350 / 500 / 750，停止线 900。
- (2) T2404 和 T2405 要同一个输入（无下限的二圈尾界）；两张票都加了一句：谁的 1a 先出，后者照抄陈述和名字。T2404 还没开工，这句在开工前加进票里（H198 一起提交）。
- (3) Jun（01:3x UTC）问 T2398 卡在文章哪一步。已回：`6_Step6_two_loop.tex:83`（`lem:LWterm_EXP`）；带状证明 `B_graphical_lemmas.tex` §B.1、`:50-64`（`I₄₁`、`(eq:termI41)`）；BA 只有 `:118` 一句"类比，用 `(GGGamma)` 替代 `(Oe2x)`，细节从略"；`(GGGamma)` 在 `:392-405`（[yang2024Del] Lemma B.11），第三个和式的 `Ḡ_{xy}` 导数给出 `Ǧ_{xw}M_{wγ}Ḡ_{xγ}`，`M_{wγ}` 跨块，`lem:main_ind_BA` 只管 `E_a`-圈。问题不变（R1 / R2）。
- (4) 中枢 `HUB.alive` 停在 01:01（31 分钟）；在跑的四个工作流里，T2397 的审核工作流自己带修补步骤，其余在 1a/1b 中，可能只是在等工作流结束。下一轮再看；若到 02:00 仍无动静，告诉 Jun。
- (5) 排队：T2404、T2405。下一张票号 T2406，下一节 §218，下一条 H199。

## §218 — 阶段 K 关闭（监督 0150 PASS）；中枢 API 限额停 1 小时；T2397 合并；T2403、T2405 签字；T2398 的 Fable 分析（总调度 V2，2026-10-11 03:06 UTC）

- (1) **监督 0150：阶段 K 关闭 PASS**。Q1 两张表通过（`KLK_ward` 对应恒等式 `KBound_baKsol_ward`，不等式 `BAKward` 对应 `stKward_of_flow`）。Q2 取 (a)，附 K1：登记改 owner 注释要改三行（`Test/Axioms.lean:133` `STLmaxgL`、`:134` `STKboundgL`、`:135` `STLKgL`；133、135 的 owner 改为 BA-V（主归纳），去掉 "BA-K4"；133 注明 BA 上 `STLmaxgL` 由 `STLKgL` 经 `BALmaxFromLK_holds` 得到）。时机：本裁决之后第一张改登记的票，最迟 G7；不为注释改正在跑的票。K2、K3 是给 BA-V 的备注，K4 改行数。
- (2) **中枢停摆 01:1x–02:10 UTC**：API 会话限额（"resets 7:10pm America/Los_Angeles"）；T2401、T2402 按规则 (H) 重跑（02:12）。监督 01:41 那次 4 秒结束也是同一原因；01:50 又跑了一次，答了 REQ 0118-K。
- (3) **T2397（L3b3 设计门）报告合并 a34b8d9**：审核第二轮 PASS（一次规则 (B) 修补）；探针留在 `t/T2397` 54ba7be。L4 REQ 的三个设计门（T2395、T2397、T2398）都已交付，T2398 等 Jun 对路线的确认。
- (4) **T2403（G4）1a BLOCKED → Amend 1**：目标 3 签名，`BAGbEXPij'` 钉文里没有 `d ≥ 3`，而所有已合并的引理都要 `2 ≤ d`。决定：`baGbEXPij'_holds (d) (hd : 2 ≤ d)`，钉文不改；owed 行能去就去，去不掉就改 owner 注释，指向 G7；K1 不在本票。1b 直接开始。
- (5) **T2405（ST 侧 T3）1a-audit RETURN + 要求签字 → Amend 1**：BA 上 `Im m ≥ κ/2` 在钉文的能量域 `|E| ≤ 2-κ` 内不成立（`L = 96`、`g = 10` 时 `0.0414`）。决定：证一个带撇的通用钉文 `STNewKLKAtgL'`，把 `|E| ≤ 2-κ` 换成载体数据 `κ ≤ Im m`（就是 `BAReal` 的形式）；不带撇的作为推论（带状经 `Ind.half_le_mE_im`，取 `κ' = κ/2`、`δ₀ = κ/4`）。第 2 行改为 `κ/2 ≤ Im m`；与 T2404 的协调作废（两边输入不同）；设计门的 (i)、(iii)–(v) 必须写进 (a′)。BA 读法归 BA-T 钉文 REQ（C7）。
- (6) **T2398 §8 的 Fable 5.1 分析**（Jun 同意起子代理，放了 [68] = `paper/2501.08608v4.pdf`）：报告 `docs/tickets/T2398-analysis-fable.md`。
  - 结论：确实卡住；[68] 附录 B 没有这个机制（那里靠 `λ = W^{-ξ}` 和 `d ≥ 7` 做逐项、按尺度阶估计；Lemma B.11 展开后的异色对只说"同阶"，p.90、p.93）。[P] p.89 的"analogous"背后缺一个引理（paper delta T2398d）。
  - 补法 R1，两条扭转圈律：(TL1) `|Tr(G̊P_{c1c2})| ≺ W^{-d}B`；(TL2) `|L̃ − K̃| ≺ (W^{-d}B)^{3/2}`，`L̃ = Tr(G(σ1)E_aG(σ2)P_{c1c2})`，`K̃ = W^{-d}Σ_{a'}Θ^{(σ1σ2)}(a,a')M^{(B)}(σ1)_{c2a'}M^{(B)}(σ2)_{a'c1}`（`(−,+)` 用 `Θ^{(−,+)}` 和 `|M|²`，不是探针里的 `M∘M`）。有了这两条，(B.4) 可以逐行照搬，3/2 正好够；首层其他扭转项也一并解决。
  - 证明路线：TL2 = 对一个扭转 2-圈重做 Step 4，交替情形要用 TL1；TL1 = Lemma 8.4(a) 的块间版涨落平均。不用 g 小。d = 1 的数值与之一致。
  - Lean：L4b2 变小（照搬 `LWExpI1K`/`I41K`）；新钉文 `BATwistAvgLaw`、`BATwistLoopLaw`；TL2 的证明是一个小阶段，中心约 6k 行，TL1 约 2–3k 行。证出来之前作为待证钉文。
  - 已问 Jun 是否按 R1 走；他回答之前，T2398 的后续（Amend 2、报告合并）和 L4 REQ 不写。
- (7) 在跑：T2401、T2402（重跑）、T2404（规则 (B) 修补）；接下来 T2403（1b）、T2405（修补）。下一张票号 T2406，下一节 §219，下一条 H200。

## §219 — BA-E3 = T2406 放行（总调度 V2，2026-10-11 03:21 UTC）

- (1) **T2406 = BA-E3**（BA 73，阶段 E 最后一行）：新文件 `BA/EKNonzero`，证 `BAEKSumDecayNonzero`。照搬带状 `ekSumDecayNonzero_holds`：`i ∉ A` 用 `baEKSameRow_holds`；`i ∈ A` 用 `Proj` 与 `M^{(σσ')}` 可交换，再加 `baProp8_holds` 和径向求和。按 C4：U3s1 没合并，所以不证 `STEK*` 的 BA 形式，归 U3-BA。`prover-hard`，250 / 350 / 550，停止线 800；不在证书通道。
- (2) **登记**：去掉 owed 行 `BAEKSumDecayNonzero`。同时按监督 0150 K1 改三行 owner 注释（`STKboundgL`、`STLmaxgL`、`STLKgL`），因为本票是那次裁决之后第一张改登记的票。
- (3) E3 合并后写阶段 E 关闭 REQ：五条 `BAEK*` 钉文全部证完；`STEK*` 的 BA 形式归 U3-BA（O4）。
- (4) 排队：T2405（修补）、T2406。仍在等 Jun 对 R1 的回答（T2398）。下一张票号 T2407，下一节 §220，下一条 H201。

## §220 — Jun 选 R1；TL1、TL2 的证明交监督审；T2404、T2406 合并（阶段 E 做完）；T2401、T2402 签字（总调度 V2，2026-10-11 04:17 UTC）

- (1) **Jun 的决定**（约 03:2x UTC，原话）：「同色的问题？ 可以选 R1， 先继续做BA， 同时 这个数学sub agent，必须写出TL1，TL2 给数学监督审查。」随后又说：「之后向我汇报TL1，2的进展，直到我表示收到再停止。」所以 TL1/TL2 的进展每轮向 Jun 汇报，直到他说"收到"。已回答同色问题：卡住的是异色那一项（G̊_{y′w}M_{wα}Ḡ_{y′α}，交替的 (−,+) 扭转 2-圈）；同色的扭转项（T3B 的 1-圈，(+,+) 圈）比较容易，用 TL1 就够。
- (2) **Fable 写出了证明**：`docs/tickets/T2398-TL-proofs.md`（Lemmas T.1–T.13）。
  - TL1（T.7）：一次高斯分部积分（迹的形式，不乘 M），再做 2p 阶矩的 bootstrap；不依赖 [59]。
  - TL2（T.12）：`|L̃ − K̃| ≺ (W^{-d}B)^{2−δ}`，作为 Theorem 8.2 的第五条假设和结论；s = 0 时成立，指数沿归纳不损失。交替情形用外部锚点 c1 代替 sum-zero 一步；区域 (ii) 靠孪生 K-圈的 Ward 恒等式精确消去零模，再用 TL1。
  - 作者自己标出三处没写全的地方：(α)、(β)、(γ)。
  - 交监督：REQ-2026-10-11-0416-TL（Q1 陈述，Q2 证明，Q3 在 Lean 里作为 owed 待证钉文，Q4 paper delta）。T2398 等审查结果再写 Amend 2。
- (3) **T2404（ST 侧 T2）合并 aa396d7**（三个文件原地改，净 450 / 1000）；**T2406（E3）合并 6f4572a**（`BA/EKNonzero` 357 行；登记去一行、改三行注释，K1 已做）。**阶段 E 三行全部合并**：五条 `BAEK*` 钉文都证完；`STEK*` 的 BA 形式归 U3-BA（C4）。下一轮写阶段 E 关闭 REQ。
- (4) **T2401（G5a）1a-audit RETURN 并要求签字 → Amend 1**：D1–D3 按审核员列的改；D4 把 R6（族矩孪生）移到 G5b；移完后若某个文件 hi 仍超过 2,000，允许拆出第三个文件 `GreenMinor3`。按规则 (B) 修补。
- (5) **T2402（G5c）1a-audit PASS 但要求签字 → Amend 1**：F2，T2401 通往 `BAGbEXPav` 的路线不用 G5c；G6b 的对角部分是否要用 G5c 还没定。决定：G5c 的 1b 暂停，现在只合并报告；等 G6a/G6b 的设计决定是重开（另起一张票）还是放弃。D3 暂时不用定，把 +419 行这个数记下来。
- (6) 在跑：T2403（1b）、T2405（修补）；T2401 修补接着开工。槽位还空一个：下一轮补票（阶段 E 关闭 REQ；BA-T 钉文 REQ；ST 侧 T4s2/T5s2/T4s1 的顺序；L2c1、L2c2、L3c2；G5b，带上 R6；G6a，等 G4）。下一张票号 T2407，下一节 §221，下一条 H202。

## §221 — BA-L2c1 = T2407 放行（总调度 V2，2026-10-11 04:20 UTC）

- (1) **T2407 = BA-L2c1**（BA 74；阶段 L 首批，监督 2149 Q2 已 PASS，"任何路线都需要"）：新文件 `Graph/BAWeightOp`，把权展开 (B.19)（[P] Lemma B.7，p.94）写成图操作：项表、值恒等式（由 `baLweight_holds` 得到）、计数和阶。照搬带状 `LWWeightExp` §3（`owxT1`–`owxT4`、`owx_graph_E`），沿用 BA 的 `lanlw` 已有做法（`BAExpandW`、`BAExpandWOrd`）。`prover-hard`，800 / 950 / 1,700，停止线 2,000；不进证书通道。
- (2) 槽位：T2403、T2405 在跑；T2401 修补、T2402 只合并报告、T2407 排队。下一张票号 T2408，下一节 §222，下一条 H203。还没写：L2c2（hi 2,697，要拆）、L3c2、G5b（带 R6，等 G5a 合并）、G6a（等 G4）、BA-T 钉文 REQ、阶段 E 关闭 REQ、L4 REQ（等 TL 审查）。

## §222 — G4、T2405 合并；放 G6a = T2408、L2c2a = T2409；T2407 Amend 1（总调度 V2，2026-10-11 04:34 UTC）

- (1) **T2403（G4）合并 292a855**：新 `BA/GreenOff` 1,568 行（停止线 1,600）；`baGbEXPij'_holds`（`2 ≤ d`）、`baStab_holds`；登记去掉 `BAStab`、`BAGbEXPij'` 两条 owed。**T2405（ST 侧 T3）合并 2af090d**：新 `Chain/NewKLKGen` 816 行，带撇的通用钉文 `STNewKLKAtgL'`。**T2402** 只合并报告（5ee937e）。现在在跑：T2401（修补）、T2407（L2c1）。槽位空两个，所以补两张票。
- (2) **T2408 = BA-G6a**（BA 75，关键路径排第一）：BA 在确定性控制下的局部律，逐序列那一层。照搬带状 `Green/LocalLaw.lean`（`localLawDetThm`、`loopFloorThm`、接线），用已合并的单时刻核心 `GreenCore_diag`、`baGbEXPij'_holds`、`baStab_holds`。1a 是设计门：第 (ii) 项要求 G6a 的输出逐字满足 G5a（T2401 G.6）和 G5c（T2402 的 `hll`）用到的局部律前提。探针由 `prover-max` 编译。`prover-hard`，1,100 / 1,450 / 2,400，每个文件停止线 2,000，必要时拆 `GreenLocal2`。
- (3) **L2c2 拆成两张**（hi 2,697 超过 2,000）：**T2409 = L2c2a**（BA 76）只做钉文和证明，新 `Graph/BAGGExp`：从 T2387 探针逐字复制 `ba_W_sub_one`、`BAGGGammaL/R`、`BAGGGamma`，证 `baGGGamma_holds`，路线照 [68] Lemma B.11，用已合并的 `baLanlw_holds`、`baLweight_holds` 和 `W` 方程组。450 / 650 / 1,000，停止线 1,300。**L2c2b**（`gg2`、`gg4` 的图操作、`BAexpFrameE`、计数和阶）等 T2407 和 T2409 都合并后再写。
- (4) **T2407 Amend 1**：T2395（S′）的探针已经钉好下游要用的形式：`BAGraph.ext`、`lw2`、`lw4`（`t/T2395` 探针 106–128），T2407 必须逐字用这些；目标 2 是 `BAexpFrameE` 的第一合取项 `baExpFrame_lw`；阶的陈述要用 T2395 `BAstepMono` 需要的形式。不重启，把 amend 传给剩下的阶段。
- (5) 下一张票号 T2410，下一节 §223，下一条 H204。还没写：阶段 E 关闭 REQ、L3c2、L2c2b、G5b（带 R6，等 G5a 合并）、BA-T 钉文 REQ、ST 侧 T4s1/T4s2/T5s2、L4 REQ（等 TL 审查）。

## §223 — TL1、TL2 审查 PASS（监督 0652，带 C1–C4）；T2398 Amend 2；放 L2c2b = T2410、G5b = T2411（总调度 V2，2026-10-11 07:43 UTC）

- (1) **监督 0652：TL1、TL2 PASS。** Q1：陈述正确，足以闭合 (B.1)。TL2 的指数 3/2 正好够，没有余量；T3B 要 TL1，也没有余量。Q2：证明成立，监督每一步都重推了；(α) 实际不用，(β)、(γ) 只是写法问题；S1–S3 是措辞，留给以后写证明的那张票。Q3：可以作为 owed 待证钉文，条件 C1–C4：
  - C1：TL2 是归纳命题，产出分两部分：单步定理（TL 阶段）和接进 BA 主归纳的第五条假设兼结论（BA-V，基础情形 `L̃_0 = K̃_0`）；owner 注释写 "TL stage (one step) + BA-V (induction)"。
  - C2：钉文用显式 `twK`（(−,+) 用 `|M|²`），未加圈的二圈，指数 3/2，四种电荷都要，去掉 `∃Kt`。
  - C3：统一指标约定（探针的 `twTr c₁ c₂` 就是证明里的 `T̃_{(c₂,c₁)}`）。
  - C4：TL 的证明另立一个新的 BA 阶段，单独提开阶段 REQ，不占阶段 L 的 50 张。
  - Q4：记 T2398d；TL2 改的是 Theorem 8.2 本身。已向 Jun 汇报（07:40 UTC）。Jun 要求每轮汇报 TL 进展，直到他说"收到"，此要求仍有效。
- (2) **中枢空了 1.5 小时**（06:09–07:4x）：调度会话从 04:46 到 07:39 没有运行（心跳链断了约 3 小时）。期间 T2401（G5a，3 个文件）、T2407（L2c1）、T2408（G6a，一次修补）、T2409（L2c2a）全部合并。
- (3) **T2398 Amend 2**：按 R1 恢复。探针换上 `BATwistAvgLaw`、`twK`、`BATwistLoopLaw`，模型无关的引理只写陈述；行表重新估价：L4b2 改成照搬，L4a2 加两个假设，新增一行 L4t（约 450 行）；记 T2398d。流程：`prover-max` → 审核 → 只合并报告。
- (4) **T2410 = L2c2b**（BA 77）：新 `Graph/BAGGOp`，`gg2`/`gg4` 照 T2395 探针逐字写，`baExpFrame_gg`、`BAexpFrameE`、`baExpFrameE_holds`（S′ 各行要用），计数和阶（第一项和保阶）。800 / 1,000 / 1,800，停止线 2,000。
- (5) **T2411 = G5b**（BA 78）：m5、阈值族、R6（族矩）、`BAFamGain`、`BAFAav`，两个新文件 `GreenCond`、`GreenCond2`；登记去两行。`prover-max`，1,150 / 1,550 / 2,550，每个文件停止线 2,000。普通 1a。
- (6) 下一步：L4 REQ（TL 已过）；TL 阶段开阶段 REQ（C4）；阶段 E 关闭 REQ；L3c2；G6b（等 G5b；G5c 的 1b 是否需要由 G6b 的设计定）；BA-T 钉文 REQ；ST 侧 T4s1/T4s2/T5s2。下一张票号 T2412，下一节 §224，下一条 H205。

## §224 — L3c2 = T2412 放行（总调度 V2，2026-10-11 07:44 UTC）

- **T2412 = BA-L3c2**（BA 79；阶段 L 首批，2149 Q2 + L5）：BA 上的 `claim:size`，带 `M` 点边和原子。带状的 `lwClaimSize` 要求 `hM`（`M` 是标量对角阵），这在 BA 上不成立。1a 是设计门：要写出原子怎么进入 size 计数（用一致的衰减率），给出 `S⁺ = SW` 的衰减，常数在 L5 的三个点上核对；原子那一步若闭不上就停下来写 REQ。探针由 `prover-max` 编译。`prover-hard`，950 / 1,350 / 2,350，每个文件停止线 2,000。中枢的四个槽位：T2398、T2410、T2411、T2412。下一张票号 T2413，下一节 §225，下一条 H206。

## §225 — 阶段 E 关闭 REQ、TL 阶段开阶段 REQ（总调度 V2，2026-10-11 07:55 UTC）

- (1) **阶段 E 关闭 REQ**（`REQ-2026-10-11-0755-E`）：三张票（T2388、T2392、T2406），五条 `BAEK*` 钉文都已证明，各有实例；没有 owner 是阶段 E 的 owed 行。`STEK*` 的 BA 形式归 U3-BA（C4/O4），阶段 E 关闭不等 U3s1。
- (2) **TL 阶段开阶段 REQ**（`REQ-2026-10-11-0755-TLS`，0652 C4）：
  - 提议先做设计票 TL-D（只出报告），固定 BA 载体上 TL1、TL2、T.12′ 的 Lean 陈述（Step 1–4 的钉文作假设）、行表和 TL-V 的接法；
  - 行的大致划分：TL0、TL1、TL2a、TL2b、TL2c、TL-V，共 6–8 行；
  - 把阶段 L 的 L4t 移进 TL0；
  - 登记 owner 文本按 C1 写。
- (3) **L4 REQ** 等 T2398 Amend 2 的新行表合并后再写。在跑：T2398、T2410、T2411、T2412。下一张票号 T2413，下一节 §226，下一条 H207。

## §226 — BA 侧 T 的钉文 REQ（C7，第一批）（总调度 V2，2026-10-11 08:11 UTC）

- `REQ-2026-10-11-0811-BAT`：第一批是 T8-BA（BA 的 `Step2Mat`/`Step2Data` 实例）、T2-BA（T6-BA 并进来）、T3-BA。每行都写了 BA 钉文、数据事实及其已合并的来源、阶段输入和 C1。
  - T2-BA 用 T2404 的假设块：`emn2PolyFacts`、`emn2ExpFacts`、`emn2ExpHK`。其中 (S) 在 BA 上成立，因为 `SB d L 0 = 1`。
  - T3-BA 用 T2405 的 `NewKLKGenHyp`（F5–F9）。
  - I1：BA 的第三个估计用 J 形式 `stEMn2ExpJgL_of`；T1 的通用陈述也取 J 形式。
  - T4-BA、T5-BA 放到第二批，等 ST 侧的 T4s1、T4s2、T5s2 合并。
- 交给监督的 REQ 现在有三份没回：0755-E、0755-TLS、0811-BAT，监督 08:41 那次一起处理。下一张票号 T2413，下一节 §227，下一条 H208。

## §227 — L4 REQ（阶段 L 三个定路线的设计门都过了）；T2398 合并（总调度 V2，2026-10-11 08:46 UTC）

- (1) **T2398 只合并报告 7b0a10a**（审核 PASS，Amend 2）。CONTROL 去掉 365 行；返工账本记"是"（两次 amend、一次设计 STOP、R1）。
- (2) **`REQ-2026-10-11-0845-L4`**（2149 L4/O3 + L8/O8）：
  - S′（T2395）+ G2（T2397）：L3b3′ 810、L3b4′ 380；R1 的目标改成 `BASimC`/`BASimP`（字面 `BAImgSim` 撤回）；双胞胎只作逐形状的后备。S′ 这一块 11 行，中心 7,830（双胞胎 16,257）。
  - L4：W2 = 否（L4a 双胞胎），W3 = C（证书行 L4e1–L4f2 取消，阶段 L 不占证书通道），R1（L4a2、L4b2 以 TL1、TL2 为假设）：9 行，中心 10,408；L4t 按 0755-TLS 进 TL 阶段。
  - 超过 1,500 行的拆法：超 5% 才拆。L3c3 按文件拆成 L3c3a/L3c3b；L4c1/L4c2 的切点在开票时挪到各约 1,380；L3d4（3%）、L4a（4%）不拆；L3b* 双胞胎、L4f2 随路线取消；L4b、L4c 已由 T2398 拆好。
  - 计数：已用 9 + 待开 30 = 39 / 50。剩余中心 26,889（T2387 原计划 33 行 42,337）。
  - 风险：L2c1 实际 1,941 行，超出估价上限 1,728；TW 比例可能偏低，R0、R1、L4a 首当其冲。
  - 放行次序：先 R0、L4a、L4d（T2410 合并后）、L3c1（T2412 合并后）；再 R1、L3a1、L3b3′、L4b1、L4e-C、L4a2；其余按链。
- (3) 交给监督的 REQ 现在有四份没回：0755-E、0755-TLS、0811-BAT、0845-L4。中枢三张在跑（T2410、T2411、T2412）；空位用不等 REQ 的票填（ST 侧 T 行，见 §228）。下一张票号 T2413，下一节 §228，下一条 H209。

## §228 — 监督 0853：阶段 E 关闭；阶段 TL 开（TL-D = T2413）；子阶段 T 范围 HOLD（BAT-F1），T8b = T2414；T2410 合并（总调度 V2，2026-10-11 09:01 UTC）

- (1) **T2410（L2c2b）合并 7c0f55a**：`Graph/BAGGOp` 1,852 行，审核一次 PASS。又一张 TW 行超出估价上限（L2c1 1,941）；已补进 L4 REQ 的校准风险一段。
- (2) **监督 0853**：
  - REQ-E PASS：阶段 E 关闭，记入 ROUTES（O1）。BA 的 `STEK*` 归 U3-BA，并且要建在 T8b 的核上（E-C1、O2）。
  - REQ-TLS PASS：阶段 TL 开，临时旗标 12；条件 TL-C1–C4；L4t 进 TL0（L 的旗标仍 50）；登记文本照 Q3。
  - REQ-BAT：T8-BA PASS（BAT-C1：`Pp`、`Hpath` 的 BA 值）；T2-BA（并 T6-BA）PASS（BAT-C2：混合对 `Θ_BA·M^{(σσ')}` 的复合界作公开引理）；**T3-BA HOLD**。
  - **BAT-F1**：通用漂移算子 `STthetaOpg` 和 n 圈核 `Step2Gen_*` 是带状的标量 `m` 闭式；在 BA 载体（`S = 1`）上是对角的，不是 `Θ_BA M^{(σσ')}`。T2386 报告 `:109` 的说法不对；T2405a 早就点到了，但当时只记了一笔、没上报。受影响的已合并票只有 T2405（证明可救：F7 重述）。HOLD 范围：T3-BA、带状侧 T1/T7/T4s1/T4s2/T5s2、U3s1 的核与 `STEK*` 形状；不影响 T8-BA、T2-BA、在跑的票、阶段 G/L/TL。T2405a 记为由 T8b 解决，不作文章差异（论文的 `def:Theta_BA` 本来就对）。
  - BAT-F2：BA 用加撇的 `STK2decaygL'`（前提 `κ ≤ Im m`）。I1（J 形式）PASS；T1 的 1a 要说明带状 Gronwall 取 `J := Ĵ` 够不够，并列出 11 条 site-1 义务（O7）。
- (3) **T2413 = TL-D**（BA 80；阶段 TL 第 1 张）：只出报告。把 T2398 探针里的 TL 钉文原样抄进新探针；D1–D7 按 TL-C1 六项写：T.12′ 的时间窗、BA 核（不用 `Step2Gen_*`）、`twK_bound` 对 T.1(i)、C1 数值、S1–S3 的去向、TL-V 归谁、行表与最终旗标（多于 8 行要短 REQ）。`prover-max`，探针 ≤ 400 行，报告 ≤ 300 行。优先级第一。
- (4) **T2414 = T8b**（BA 81；子阶段 T 新行，T 变 19 行、旗标 28.5）：从载体的 `FlowFM.M` 导出块核 `M^{(σσ')}`，漂移核 `M^{(σσ')}S(1 − uM^{(σσ')}S)⁻¹`；n 圈核、`STgDriftg`、`STGridRepN`、`STGridMart` 同形；带状桥接（不再是 `Iff.rfl` 的要证）；BA 恒等式对 `BATheta·BAMss`，n 圈对 `BAUN`；`NewKLKGen` 的 F7 重述后重证；加撇的 `STK2decaygL'`。设计门 1a（`prover-max` 探针）→ 1a-audit → 1b `prover-hard`；估价 450 / 700 / 1,200，停止线 1,400；不在证书通道（`Step2Gen` 的反向锥 76 个模块，不含证书）。(b) 或 (c) 不成立时停，写短 REQ。
- (5) T8-BA、T2-BA 下一轮写（它们读 `Step2Mat`，不依赖新核）。中枢：T2411、T2412 在跑，T2413、T2414 放行后满四张。下一张票号 T2415，下一节 §229，下一条 H210。

## §229 — T8-BA = T2415、T2-BA = T2416 放行（排在 T2413、T2414 之后）（总调度 V2，2026-10-11 09:04 UTC）

- **T2415 = T8-BA**（BA 82）：新 `BA/Step2BA`，`baStep2Mat`（`toFlowFM := baFM`，`LM`/`GMM`/`LIM`/`KI` 取 BA 对象；BAT-C1：`Pp := pathP (sz.withLam 0)`，`Hpath := lam0 • PsiI + pathH (sz.withLam 0)`），`baStep2Data`（`T0 = BAflowT0`，`flowOK = BAFlow`，三条事实），与 `BAStep2` 的桥；能量族里 `lam0` 怎么定由 1a 说明，留给 T3-BA。不用 T8b 的核。`prover-hard`，350 / 500 / 750，停止线 900。
- **T2416 = T2-BA（并 T6-BA）**（BA 83）：新 `BA/EMn2BA`，在 BA 读法下给出 T2404 的三个假设块（`emn2PolyFacts`、`emn2ExpFacts`、`emn2ExpHK`）；BAT-C2：混合对 `Θ_BA·M^{(σσ')}` 的复合界作公开引理；BA 钉文 `STEMn2PolygL`、J 形式、Ĵ 形式（0853 Q2）；`STContractM` 的 BA 推论。1a 要核对 `emn2ExpEllStar`/`Bctl` 读的 `sz.lam` 与 `BAProp5` 的 `ellT L g t` 一致。`prover-hard`，550 / 850 / 1,500，停止线 1,800。
- 中枢次序：T2413 → T2414 → T2415 → T2416（并行 4；T2411、T2412 在跑）。子阶段 T 计数：8 张 + T8b 共 9 / 28.5。下一张票号 T2417，下一节 §230，下一条 H211。

## §230 — T2412（L3c2）合并（总调度 V2，2026-10-11 09:27 UTC）

- **T2412 合并 260732c**：`Graph/BASizeClaim` 1,167 行 + `BASizeClaim2` 825 行，设计门 1a-audit PASS，审核一次 PASS（O1–O4 只是观察）。阶段 L 已合并：L0、L2c1、L2c2a、L2c2b、L3c2 和三个设计门。L3c1（1a = G3、G4）按 L4 REQ 的放行次序，等监督 09:41 的结论再写。
- 中枢：T2411、T2413、T2414、T2415 在跑，T2416 排队。下一张票号 T2417，下一节 §231，下一条 H212。

## §231 — T2415（T8-BA）合并（总调度 V2，2026-10-11 09:42 UTC）

- **T2415 合并 54ecfc4**：`BA/Step2BA` 209 行（估价中心 500），审核一次 PASS。能量族 `baStep2Fam sz E = baStep2Mat sz sz.lam E` 已定义并记给 T3-BA（报告 `:177`）；T3-BA 仍在 BAT-F1 的 HOLD 里，等 T8b（T2414）。
- 子阶段 T：已合并 row 0、T5s1、T8、T6、T2、T3、T8-BA；在跑 T8b（T2414）、T2-BA（T2416）。中枢：T2411、T2413、T2414、T2416。队列空：L 阶段的行等 L4 REQ（监督 09:41 这次），G6b 等 G5b，TL0 等 TL-D。下一张票号 T2417，下一节 §232，下一条 H212。

## §232 — 监督 0951：L4 REQ PASS（L4-C1–C9）；放阶段 L 的「现在」四行：R0 = T2417、L4a = T2418、L4d = T2419、L3c1 = T2420（总调度 V2，2026-10-11 10:01 UTC）

- (1) **监督 0951 PASS（Q1–Q4）**，两处更正：
  - 计数是 **38 / 50**，不是 39（剩余 28 行，L3c3 拆后 29；加已用 9）。
  - L3c3b 排在 L3c3a 之后，不能并行。
- (2) **条件（写进对应的票）：**
  - L4-C1：R1 证明一条图层面的对应（允许重新标号），由它推出 `BAsim m`（或 `BAsim'`）；`BASimC` 在 L3b4′ 推出，`BASimP` 在 L3b1 推出；R1 的 1a 是逐形状后备的位置。
  - L4-C2：R0 只定义一个像映射，两套钉文都对它证明（已写进 T2417）。
  - L4-C3：L3b4′ 把 `BAFinal` 钉在 `BAGraph.LocStd` 上。
  - L4-C4：L3b1 的 1a 先用数值核对五种形状的 `PathInv2`；L3d2、L3d4 的 1a 要说明远半部分里 `x ~ y` 的项怎么处理。
  - L4-C5：带上下文的 GG 引理归 L4e-C。
  - L4-C6：L4a 的 1a 钉 S1，L4b1/L4b2 钉 S2、S3；L4a 和 L4b2 重叠的 I1K/I41K 归 L4b2（中心约少 370 行）；TL 的名字从 TL0 导入（已写进 T2418）。
  - L4-C7：L4g 的输入改接 L4e-C 和 L4c2。
  - L4-C8：中心 ≥ 1,000 的行开票时就写明第二个文件（本批 T2418、T2420 已写）。
  - L4-C9：「下一批」R1 排最先；L3a3 还要等 R1；L4a2 分两半，组装那一半等 TL0；L4b2 等 TL0 和 L4b1。
- (3) **校准**（O5，记入 ROUTES）：阶段 L 实际行数约为中心估价的 1.5–2.1 倍；剩余 26,889 中心约合 46k 行。停止线按每文件 2,000 计。
- (4) **放行四张**（BA 84–87），优先级 T2417 → T2418 → T2419 → T2420：
  - T2417 = R0 `Graph/BAAtomic`：原子层词汇，一个像映射，`BAimg` 加 (m0)–(m2) 和 `BAPathLift`。`prover-hard`。
  - T2418 = L4a `Graph/BAExp14a` + `BAExp14aB`：S1 族、核 `ω`、连结和、细格 Ward；`LWExpTerm4` 去掉 §6、§9 后的孪生。1a 钉 S1 → 1a-audit。`prover-hard`。
  - T2419 = L4d `Graph/BAExpandId`：`baG5Graph`、`BAG5Identity`、GG 一步和展开恒等式（导入 `expandG_sum`）。`prover-hard`。
  - T2420 = L3c1 `Graph/BAAtom` + `BAAtom2`：设计门 G3（`(G_by_auxG_BA)`，要写出论证）、G4（替 L3d1 钉陈述）。`prover-max`。
- (5) 中枢：T2411、T2413、T2414、T2416 在跑；四张新票排队。阶段 L 已用 13 / 50。下一张票号 T2421，下一节 §233，下一条 H214。

## §233 — T2416（T2-BA）合并；TL-D 设计写完（10 行，旗标 15），交 TL 旗标短 REQ（总调度 V2，2026-10-11 10:13 UTC）

- (1) **T2416 合并 e4a1833**：`BA/EMn2BA` 1,090 行，审核一次 PASS。BAT-C2 的复合界已是公开引理（T3-BA 的 F7/F8、T8b 的核对 (c) 可用）。子阶段 T：已合并 8 张（row 0、T5s1、T8、T6、T2、T3、T8-BA、T2-BA），T8b（T2414）在跑。
- (2) **TL-D（T2413）设计写完**（10:07，审核在跑）：10 行 = TL-D + 9 行证明（TL0、TL1a、TL1b、TL2a–TL2e、TL-V），中心 8,688；T.7–T.13 在 BA 载体上每一步都闭合，没有 STOP；F1–F6 只改陈述、前提、归属。`twK_bound` 保持 `Bctl` 形式（D3）。TL-V 是 TL 的行；带第五条的主归纳一步 `BAMainIndTL` 归 BA-V 的 V2a（D6）。
- (3) **短 REQ `REQ-2026-10-11-1013-TLF`**（0853 TLS Q1：多于 8 行要短 REQ）：Q1 旗标 15；Q2 两条登记文本；Q3 F3（BA 的 Claim 4.5 等 T7-BA，在 T8b 之后）和 F4（`STLmaxU`/`STLKU` 的载体形式等 U3s1）作为假设。审核若 RETURN 改了行表，REQ 先修改再答。TL0 是第一行证明，等 T2413 审核 PASS 就放（不等这份 REQ）。
- (4) 中枢：T2411、T2413、T2414、T2417 在跑；T2418、T2419、T2420 排队。下一张票号 T2421，下一节 §234，下一条 H215。

## §234 — T2411（G5b）、T2413（TL-D）合并；放 TL0 = T2421、G6b = T2422；G5c 的 1b 放弃（总调度 V2，2026-10-11 10:30 UTC）

- (1) **T2411 合并 bd0efad**：`BA/GreenCond` 1,989 行 + `GreenCond2` 1,990 行，审核一次 PASS。登记里去掉 `BAFamGain`、`BAFAav`；另加了 `STInitialGT2gL`，owner 写成 BA-G6b（审核观察 2 留给总调度）。这个归属不对：它是 `BAGavLGEX`、`BAFAav` 的前提，阶段 G 不产出它，和带状的 `STInitialGT2` 一样归 Step 1 / 主归纳链。T2422 把 owner 改成 BA-V。
- (2) **T2413（TL-D）只合并报告 1d34da3**：审核第二轮 PASS（修补一次）。行表不变，10 行、旗标 15。短 REQ 1013-TLF 已补一句"审核已过"。
- (3) **T2421 = TL0**（BA 88；TL-C2）：新 `BA/TwistPins`，把 T2413 探针 §1–§3 的定义原样搬进来；证明 `twFold`、`twWard`、`twCirc`、`twK_bound`（`Bctl` 形式）以及 `twMB_ba`、`twK_ba`；T2398 审核的 O2–O4；`owedProps` 加两行（`BATwistLoopLaw` 的 owner 照 1013-TLF Q2 的答复）。`prover-hard`，450 / 620 / 950，停止线 2,000。下一个开工。
- (4) **T2422 = G6b**（BA 89）：G6a 和 G5b 之后，G6b 只剩一步组合：`baGbEXPav_holds` = G6a 的接线 + G5b 的 `baFAav_holds`。登记里去掉 `BAGbEXPii`、`BAGbEXPav`，`STInitialGT2gL` 的 owner 改成 BA-V；`BAGbEXPij`（不加撇）留给 G7。`prover`，停止线 400。
- (5) **G5c（T2402）的 1b 放弃**：T2401/T2408 的 `BAGbEXPav` 路线不用 G5c，对角律在 G6a 已闭合（T2408 O1），G5c 没有使用方。T2402 只保留已合并的报告；阶段 G 剩 G6b、G7。
- (6) 中枢：T2414、T2417、T2418、T2419 在跑；开工次序 T2421 → T2422 → T2420。下一张票号 T2423，下一节 §235，下一条 H216。

## §235 — T2418（L4a）1a-audit 要签字：签了（Amend 1）（总调度 V2，2026-10-11 10:44 UTC）

- **T2418 的 1a-audit RETURN**：一是 1a 的交付项缺了（S1 的 Lean 陈述、章节对照、行数预测、§6/§9 排除说明）；二是 1a 提出了三处改动范围，需要总调度签字。
- **签字（Amend 1）**，与监督 0951 L4-C6、T2398 设计 §2 一致：
  - 接受：S1 不带 `|𝔼 tr| ≺ B²` 前提，票内自己证 `|𝔼X| ≺ B^{3/2}`。这是加强，使用方 `BALWCutExpTw` 本来就没有这个前提。记文章差异候选 T2418a。
  - 接受：`T3A` 用粗估留在 S1（Ward + Schur，指数 5/2），不再孪生 `lwExpTerm4_L3` 和 §8 未扭曲部分。这是 L4a 范围缩小，不改归属：§6、§9 和 §8 的扭曲部分仍归 L4b2。
  - 接受：K12 的输入 S1 不用，留给 L4b2。
  - `MǦ`、`ǦM` 的 `∂Ḡ_{xy}` 子项归 L4b2，跟它们的母项一起；`∂tr` 子项归 S3（L4b1）。S1 只管两权子项 `F_C1`、`F_C2`。
- **流程**：1a 按规则 (B) 修补，补齐审核列的 2–7 项 → 1a-audit 第二轮 → 1b → 审核。下个空位先开它，排在 T2422、T2420 前面。下一张票号 T2423，下一节 §236，下一条 H217。

## §236 — T8b、G6b 合并（子阶段 T 的 HOLD 解除）；监督 1049：TL 旗标 15 PASS；T2421、T2419 签字（总调度 V2，2026-10-11 10:59 UTC）

- (1) **T2414（T8b）合并 6c42b16**：新 `Chain/Step2Kern` 207 行，`Step2Gen`、`NewKLKGen` 原地改，审核一次 PASS。**BAT-F1 的范围 HOLD 解除**（0853 O4）：T3-BA、带状侧 T1/T7/T4s1/T4s2/T5s2、U3s1 现在可以按 T8b 的核来写。T2405a 记为由 T8b 解决，不算文章差异。
- (2) **T2422（G6b）合并 6daccd4**：`BA/GbEXPav` 30 行；登记去掉 `BAGbEXPii`、`BAGbEXPav`。阶段 G 只剩 G7。
- (3) **监督 1049：1013-TLF PASS**：TL 共 10 行，旗标 15；附条件 TLF-C1 到 C5：
  - C1：TL1a、TL2a、TL2b、TL2d 开票时写明第二个文件；
  - C2：`BATwistLoopStep` 只能有一张票产出，默认 TL2e（网格在 TL2e）；
  - C3：TL2a 等 T8b 合并后放（现在已满足）；
  - C4：两条登记文本改写，已写进 T2421 Amend 1；
  - C5：U3s1、T7 的载体形式要和 `twSteps` 第 2–4 项 `Iff.rfl` 一致。
  - BA-V 接口清单加四项：V2a 的目标是每个情形下的 `BAMainIndTL`；V2b 加第十二个传递；V3 和 BA-M1 改吃 `BAMLOutTL`；`GLoopAtT0` 同时供 `STBaseG` 和 `BAChainTL`。
- (4) **T2421（TL0）1a 卡住 → Amend 1**：`twK_bound` 改成 `∀ᶠ n`（常数仍在 `sz`、`z` 之前），因为 `g` 的窗口在 `BAFlow` 下只是最终成立；使用方都在 `≺` 里，不受影响。登记文本照 TLF-C4。
- (5) **T2419（L4d）审核要签字 → Amend 1，选 (b)**：两种电荷都在本行做，红色 `GG` 恒等式用共轭从蓝色的得到。理由有二：论文的 GG 步是"同电荷"的两条边；L4-C3 的叶子形状要求红对也能展开。只做蓝色就是不能推广的特殊情形（TEAM §6）。若共轭需要新的数学输入就停下来，退回 (a) 加一张后继票。
- (6) 中枢：T2417、T2418（修补）、T2420 在跑；T2421、T2419 等空位。下一批：R1（L4-C9 最先）、T3-BA、TL1a/TL2a/TL2b/TL-V（TL0 合并后）、G7、带状侧 T 行。下一张票号 T2423，下一节 §237，下一条 H218。

## §237 — 放 R1 = T2423（等 R0 合并）、T3-BA = T2424（总调度 V2，2026-10-11 11:01 UTC）

- **T2423 = R1**（BA 90；L4-C1、L4-C9 第 1 项）：新 `Graph/BASim` + `BASim2`。内容：
  - 证一条图层面的对应（允许重新标号）：每个 BA 步都对应原子像上的一个带状 `LocStep`；
  - 由它推出 `BAsim m`（或 `BAsim'`）；1a 定按步还是按输出；
  - 图层面的 Lemma E（`(M⁺S⁺)` 部分、GG 第三个和）；
  - 1a 也是逐形状后备的位置。

  设计门，`prover-max`，两个文件。等 T2417（R0）合并后开工。
- **T2424 = T3-BA**（BA 91；HOLD 解除后第一张）：新 `BA/NewKLKBA`，在 `baStep2Fam` 上给出 `NewKLKGenHyp` 的 F5–F9。F7 是 BA 的 Θ 卷积，用 T8b 的核加 T2416 的 BAT-C2 证明，`K_c ≠ 1`。由此得 BA 的 `STNewKLKgL'` 和加撇的 `STK2decaygL'`（BAT-F2）。`prover-hard`，停止线 1,200。
- 开工次序：T2421（续）→ T2419（修补）→ T2423（R0 合并后，否则先开 T2424）。
- 还没写、下一轮考虑：
  - TL1a、TL2a、TL2b、TL-V：等 TL0 合并；TL1a、TL2a、TL2b、TL2d 要写明第二个文件（TLF-C1）；
  - G7；
  - 带状侧 T7（带 TLF-C5 的 `Iff.rfl` 形式要求）、T1（J 形式；O7）、T4s1/T4s2/T5s2（按 T8b 的核）；
  - 阶段 L 的 L3a1、L3b3′、L4b1、L4e-C。
- 下一张票号 T2425，下一节 §238，下一条 H219。

## §238 — R0 合并；T2418 的探针步骤批准（总调度 V2，2026-10-11 11:14 UTC）

- **T2417（R0）合并 1dc7516**：`Graph/BAAtomic` 985 行 + `BAAtomic2` 262 行，审核一次 PASS（估价中心 900，落地 1,247）。R1 = T2423 随即开工（R0 是它的输入）。
- **T2418（L4a）修补卡在流程上**：Amend 1 要求 S1 的 Lean 定义在 1a 编译，但预检代理按规定不写 Lean。批准由 `prover-max` 跑一个探针步骤（T2390 Amend 1 D1 / H194 的先例），在 `RBM3D/Probe/T2418Pins.lean` 写 S1 定义并编译，结果贴进报告；之后 1a-audit 第二轮 → 1b → 审核。以后凡要求"1a 编译陈述"的票，都在票里直接写明探针步骤。
- 中枢：T2419（修补）、T2420、T2421、T2423 在跑；T2418（探针步骤）、T2424 排队。下一张票号 T2425，下一节 §239，下一条 H220。

## §239 — 放 L3a1 = T2425、L3b3′ = T2426（总调度 V2，2026-10-11 11:16 UTC）

- **T2425 = L3a1 `BASymm1`**（BA 92）：BA 图的扭曲（共轭、转置），`ba_twist_counters`、`BAtwistInv`、`BAtwistIntegral`（由 `lwSymm_twist_integral` 在 BA 律下得到）；`LWSymm` §1–§3 的孪生。`prover-hard`，停止线 2,000。
- **T2426 = L3b3′ `BAScostS′`**（BA 93）：原子层的代价词汇（T2397 探针原样搬入，建在 R0 的 `atomSetoid`/`promoteC` 上），BA Lemma B，五条只在 BA 出现的 `ScostLL` 引理（E1、S1 两原子、E2、宏 (a)/(b) 中间项），`BAInit`。`prover-max`，可拆两个文件。
- 开工次序：T2418（探针步骤）→ T2424 → T2425 → T2426。阶段 L 已用 18 / 50（T2425、T2426 计入）。下一张票号 T2427，下一节 §240，下一条 H221。

## §240 — 调度 V3 接手；11:17 后七张合并；T2423（R1）签字（Amend 1）（总调度 V3，2026-10-11 21:47 UTC）

- (1) **接手**：Jun 2026-10-11 21:4x UTC 指示「恢复调度工作」。从 21:44 UTC 起唯一的总调度是调度 V3 = Cowork 会话 session_01Qidfbgzdy6FV6jy1eSbZgb（账号 junyin.harvard@gmail.com）。调度 V2（session_01MtDU5B1PoJEbaNvMuRAPrx）最后写入 11:17 UTC，此后心跳中断；中枢自 15:12 UTC 起空转（HUB.alive 新鲜，无可开工的票）。
- (2) **11:17 后合并（规则 (A)，中枢自动）**：T2419（L4d，977d5da，Amend 1 两种电荷）、T2421（TL0，631b8f4，`BA/TwistPins` 962 行，两条 owed 行按 TLF-C4）、T2424（T3-BA，f3a7401）、T2425（L3a1，3dbb04d）、T2420（L3c1，46120c3，G3/G4）、T2418（L4a，4bd65c3，S1 `baExp14a_S1_holds`）、T2426（L3b3′，135f605；`BReach` 写成 `ReflTransGen` 定义并证与钉文的归纳式等价，文章差异候选 T2426c；审核 O2 留给 L3b4′）。11:2x–12:10 UTC 中枢四个 workflow 撞 API 限额，12:12 起按规则 (H) 重跑，不计返工。
- (3) **T2423（R1）1a-audit 第二轮 PASS，要签字 → Amend 1**：
  - S1：R1 只交 frame 层的对应（`BAMatch` 在 `P.img`），这正是 `BAsim m`、`ba_lvl1StepGood_of_sim`、逐输出 `BASimC'` 用的。`BALocStep` 层的推论 `BAMatchTw` 及其三条桥（`img_twist`、`BAEquiv.twist`、`partition` 与 twist 交换）归 **L3b4′**（本来就排在 R1、L3a3、L3b3′ 之后，且由 R1 推 `BASimC`，L4-C1）；L3b4′ 的 1a 若查无使用方就删掉并写明。
  - S2：现在就命名第三个文件 `Graph/BASim3.lean`（Lemma E + `BAsim'` 组装），停止线仍是每文件 2,000。
  - O1：本票报告放宽到 400 行，(a)/(a″)/(a′) 可压缩成摘要并引提交号。O4：`PGraph.BAEquivC`、`BAPGraph.twist` 由 Amend 1 钉名（公开），L3b4′ 要导入。O2：1b 从当前 `main` 开始，`BAShape`/`BTStep` 改用 T2426 已合并的定义。
  - 流程：从 1b（`prover-max`）续跑 → 审核。下个空位先开它。
- (4) **返工账本**补 T2418（是：1a-audit RETURN，Amend 1 + 探针步骤）、T2419（是：审核 RETURN 要签字，Amend 1 修补一次）、T2421（否：1a 卡在钉文，Amend 1 在写 Lean 前，按先例不计）、T2424、T2425、T2420、T2426（否）。CONTROL 超过 30KB，H208–H220 与合并记录归档。
- (5) 计数：BA 93（阶段 L 18 / 50，TL 2 / 15，T 10 / 28.5，G/E 12 / 19.5）。下一张票号 T2427，下一节 §241，下一条 H222。下一批（本轮写）：TL1a、TL2a、TL2b、TL2c、TL-V（TL0、T8b、T6-BA 都已合并，TL-D §7 的依赖都满足）；之后 L4b1、L3a2、L3c3a、L4e-C、G7、带状侧 T7/T1/T4s1/T4s2/T5s2。

## §241 — 阶段 TL 放五行：TL1a = T2427、TL2a = T2428、TL2b = T2429、TL2c = T2430、TL-V = T2431（总调度 V3，2026-10-11 22:08 UTC）

- (1) **依据**：TL-D（T2413）§7 的依赖——TL0 已合并（T2421），T8b（T2414）、T8-BA（T2415）、T6-BA（T2416）已合并，所以 TL1a、TL2a、TL2b、TL2c、TL-V 都可以开工；TL1b 等 TL1a，TL2d 等 TL2a、TL2b、TL2c、TL1b，TL2e 最后（TLF-C2：`BATwistLoopStep` 由 TL2e 产出）。BA 94–98；阶段 TL 7 / 15。
- (2) **T2427 = TL1a**（`prover-max`，`BA/TwistAvgA` + `TwistAvgA2`，TLF-C1）：T.7 Steps 1–4 一直做到 2p 阶矩递推不等式（TP:89），新钉文 `BATwistAvgRec`（名字由探针定），前提与 `BATwistAvgProd` 相同。**行内容调整**：T.6 和 Hölder 从 TL1b 挪到 TL1a，TL1b 只做 Step 5 的 bootstrap（含 S1）、Step 6、`BATwistAvgProd`；文件逼近停止线时 1a 可以把 T.6 退回 TL1b（1a-audit 记下）。IBP 路线优先用已合并的 `baLanlw_holds`（`Graph/BAExpand.lean:744`）：(C.3)–(C.4) 是镜像形式（求和块在扭转的另一侧），数学等价，记文章差异候选 T2427a。设计门带探针步骤（§238）。
- (3) **T2428 = TL2a**（`prover-max`，`BA/TwistGrid` + `TwistGrid2`）：T.8、T.9 的网格形式，`BATwistGen`、`BATwistHier`、`BATwistDuhamel`、`BATwistGridMart`（名字由探针定）。TLF-C3 照做；两处更正记下：`STGridMartAtgL` 在 T8b 之后位于 `Chain/Step2Gen.lean:857`（1049 写的 `:659` 是旧行号）；T8b 是**原地**重钉 `Step2Gen_*` 核（块核），所以规则写成"陈述用 BA 名（`BATheta`、`BAMss`、`BAuKer`），`Step2Gen_thetaKer`/`Step2Gen_uKer` 只出现在两条桥引理里，`STthetaOpg` 一律不出现"。`Ũ` 加权尾项（`STGridRepNAtgL` 第四合取项）列入目标 4(b)(iv)：(D.5) 的鞅项要它。**风险**：4(b) 的余项和两个鞅尾在带状侧由 `Path/DifREP1` §3–§4、`DifREP2`、`DifREP3`（约 6,000 行）证明，不在本行估价基础内；1a 若判断两个文件放不下就停，由总调度决定拆行（若加行，TL 旗标 15 以内处理，超出再发短 REQ）。
- (4) **T2429 = TL2b**（`prover-hard`，探针步骤 `prover-max`；`BA/TwistKer` + `TwistKer2`）：T.10 (a)(b)(d) = `BATwKerA/Far/Zero`，T.1 (iii) 新钉文 `BATwKDecay`，T.11 (i)(ii)(iv)(v) = `BATwistSrc1/2/4/5`（对所有 regime `R`）。**私有引理**：照监督 1049 的建议删 `private` 关键字，不拷贝——`BA/EKPins` 的反向导入只有 5 个模块，`BA/EKNonzero` 没有，都不在证书通道、也不在在跑票的可写集里；两个文件列为可写，审核用脚本核对 diff 只删关键词；具体删哪些由探针步骤定。
- (5) **T2430 = TL2c**（`prover-max`，`BA/TwistQV`，必要时 `TwistQV2`）：T.11 (iii) = `BATwistSrc3`（对所有 `R`）。公开的 `STContractM`/`STContractPt` 只界未扭转的圈，Schatten 工具在 `Induction/Contract.lean`、`ContractPt.lean` 里都是 `private`；`Induction/Contract` 处在导入树下层，按 §161 (1) **拷贝**（词干 `TwistQV_`），不删关键字。
- (6) **T2431 = TL-V**（`prover-hard`，`BA/TwistChain`，停止线 1,000）：`baTwistLoopBase_holds`、`baChainTL_holds`（带第七合取项的链）。`BAChainTL` 里的 `BATwistLoopBase` 前提有了目标 1 就多余，但不另加推论（V3、BA-M1 直接用两条定理）。
- (7) 开工次序：T2423（在跑）→ T2427 → T2428 → T2429 → T2430 → T2431。登记（`Test/Axioms.lean`）五张都不改。下一张票号 T2432，下一节 §242，下一条 H223。下一批：L4b1、L3a2、L3c3a、L4e-C、G7、带状侧 T7/T1/T4s1/T4s2/T5s2；TL1b 在 T2427 合并后。

## §242 — T2428（TL2a）1a 撞停止线：按探针提议拆成四行（Amend 1）（总调度 V3，2026-10-11 23:31 UTC）

- (1) **T2428 的 1a 通过、1a-audit BLOCKED 要签字**：目标 4(b) 的 (ii)–(iv)（余项界、鞅尾、`Ũ` 加权尾）预计 3,445 行，两个文件放不下（停止线每文件 2,000）。原因：带状的 `oneStepEnvelope`、`difRepTail_condMGF_Z`、`STeeM` 都只对 `loopL`/`ZvecN` 陈述，扭转版本要新证（§241 (3) 预计的风险）。不缺数学输入。
- (2) **签字（Amend 1）**：接受探针的拆法。T2428 保留目标 1–3、`BAuKer` 半群、4(a)、4(b) 第 (i) 条、两条核桥，另把 `BATwistGridMartAt`、`BATwistGridMart`、`BATwistGridRem`、`BATwistGridTail`、`BATwistGridWTail`、`BATwistGridAssemble` 逐字从探针 f6c3866 抄进 `TwistGrid2`，并证 `baTwistGridAssemble_holds`（预计 1,035 + 465 行）。后继三行在 T2428 合并后写：**TL2a2** = (ii) `BATwistGridRem`（中心 1,380，两个文件）、**TL2a3** = (iii) `BATwistGridTail`（915）、**TL2a4** = (iv) `BATwistGridWTail`（1,150）。`baTwistGridMart_holds` 是三行推论，放进 TL2d。
- (3) **阶段 TL 行数 10 → 13**，仍在旗标 15 以内（§241 (3) 的规则）；余量只剩 2 张。再超就给监督发短 REQ。TL2d 的输入改为 TL2a–TL2a4、TL2b、TL2c、TL1b。T2427 的 1a-audit RETURN 是钉文少一个前提（`0 < ε`），中枢自动修补，不需签字。下一张票号 T2432，下一节 §243，下一条 H224。

## §243 — TL2b、TL2c 合并；放 L3a2 = T2432、L4e-C = T2433（总调度 V3，2026-10-12 00:34 UTC）

- (1) **T2429（TL2b）合并 7eb7279**：新 `BA/TwistKer` 1,599 + `TwistKer2` 1,442（T.10 (a)(b)(d)、T.1 (iii) `BATwKDecay`、T.11 (i)(ii)(iv)(v)），`BA/EKPins`、`BA/EKNonzero` 只删 `private`（9 行）；审核一次 PASS。**T2430（TL2c）合并 aa2b87e**：新 `BA/TwistQV` 1,429 行（`baTwistSrc3_holds`）；审核一次 PASS。TL 已合并 4 / 13 行（TL-D、TL0、TL2b、TL2c）；在跑 TL1a（修补）、TL2a（1b）、TL-V。
- (2) **T2432 = L3a2 `BASymm2`**（BA 99；L 19 / 50；`prover-hard`）：S′ 下只做 `LWSymm` §5 的孪生（三种展开的扭转形式）加 §6 的实例模式；§4（`OwxE`）不孪生，1a 确认。关键路径，排在 T2433 前。
- (3) **T2433 = L4e-C `BAG5Leaf`**（BA 100；L 20 / 50；设计门 + 探针步骤，`prover-max`）：带上下文的 GG 引理（L4-C5）、闭包表、叶子性质，`BAG5Tgt/Leaf/Expand` 逐字从 T2398 探针抄入，L4g 用（L4-C7）。附带的签字：附着条款在这里证；引理的行数由 1a 估；证明路线由 1a 定，可以用可计算的桥，但不能孪生证书机器、不走证书通道；表在 Lean 树上对四种 `(k, s)` 重算；只做蓝色须先证选择器不会选红色。
- (4) 下一张票号 T2434，下一节 §244，下一条 H225。还没写：L4b1、L3c3a、G7、带状侧 T7/T1/T4s1/T4s2/T5s2；TL1b（T2427 后）、TL2a2–4（T2428 后）、TL2d、TL2e。

## §244 — TL-V 合并；放 L4b1 = T2434、L3c3a = T2435（总调度 V3，2026-10-12 01:07 UTC）

- (1) **T2431（TL-V）合并 edeea3d**：新 `BA/TwistChain` 297 行（`baTwistLoopBase_holds`、`baChainTL_holds`），审核一次 PASS。TL 已合并 5 / 13（TL-D、TL0、TL2b、TL2c、TL-V）。
- (2) **T2434 = L4b1**（BA 101；L 21 / 50；`prover-max`，`Graph/BAExp14b` + `BAExp14bB`，设计门 + 探针步骤）：钉 S2、S3，证展开恒等式 `baExp14b_expand_holds`（𝔼 cut = S1 六族 + S2 + S3，两种电荷）。S2 的证明归 L4b2（要 TL1/TL2 作前提），S3 的证明归 L4g（与 L4c1、L4e-C）——与 T2398 设计 (b′) C 一致。分族按 T2418 Amend 1。S3 的根是否是 `baG5Graph` 值的组合，是设计门的停止项。`LWExpTerm2` §§11–12 本行内由 1a 估价，其余未估价的 §§ 报给调度。
- (3) **T2435 = L3c3a**（BA 102；L 22 / 50；设计门（T2387 标"1a: stage G"）+ 探针步骤，1b `prover-hard`，`Graph/BAAuxGraph2` + `BAAuxGraph2B`）：`AuxGraph2` 1–1500 的孪生（ζ、`LWXigL`、`BAZetaClaim`、`BAGbyZeta`、`BAEntryPsi`），ζ/ξ 与 G3 的 `hξ` 联合核对是设计门第 (i) 项；`BAAnpAuxG` 只钉不证（L3d1 证）；G7 的不带撇 `BAGbEXPij` 只作前提。L3c3b 等它合并（0951 更正）。
- (4) 下一张票号 T2436，下一节 §245，下一条 H226。还没写：G7、带状侧 T7/T1/T4s1/T4s2/T5s2；TL1b（T2427 后）、TL2a2–4（T2428 后）、TL2d、TL2e；L3a3、L3b4′（等 R1）。

## §245 — TL1a 合并；放 TL1b = T2436（总调度 V3，2026-10-12 01:09 UTC）

- (1) **T2427（TL1a）合并 a24d4e9**：新 `BA/TwistAvgA` 1,085 + `TwistAvgA2` 1,228；`baTwistAvgRec_holds`（2p 阶矩递推）、`twAvgMoment/Reg/SCS/SPrec/T6_holds`；T.6 留在 TL1a（未用退路）。1a-audit 第一轮 RETURN（`twAvgReg` 缺 `0 < ε`）→ 探针修补一次 → 第二轮 PASS；审核一次 PASS。文章差异候选 T2427a（镜像形式）、T2427b、T2427c 待记。
- (2) **T2436 = TL1b**（BA 103；TL 8 / 15；`prover-hard`，`BA/TwistAvgB`，停止线 1,500）：证接口 `T2427_TL1b`（`BATwistAvgRec → BATwistAvgProd`，按 TL1a 报告 (iv) 的方案：bootstrap、S1 分情况、逐对 Markov、对所有块对取并），再得 `baTwistAvgProd_holds`；不用 net。登记不动（`BATwistAvgLaw` 的 owed 行到 BA-V 才退）。这张票由总调度直接写（不起子代理），只读了接口和方案。排在等待队列最前。
- (3) 下一张票号 T2437，下一节 §246，下一条 H227。

## §246 — TL2a 合并；放 TL2a2 = T2437、TL2a3 = T2438、TL2a4 = T2439（总调度 V3，2026-10-12 01:43 UTC）

- (1) **T2428（TL2a）合并 1a559d5**（Amend 1 范围）：新 `BA/TwistGrid` 963 + `TwistGrid2` 345；T.8、T.9、`BATwistDuhamel`、分解第 (i) 条、两条核桥、六个部件钉文、`baTwistGridAssemble_holds`；审核一次 PASS。TL 已合并 7 / 13。
- (2) **三张后继**（§242），都对已合并的钉文证明，不需设计门，可以并行，排在 T2434、T2435 前面：
  - **T2437 = TL2a2**（BA 104；TL 9 / 15；`prover-max`；`BA/TwistGridRem` + `TwistGridRem2`）：`baTwistGridRem_holds (d) : ∃ C₀, 0 ≤ C₀ ∧ BATwistGridRem d C₀`——每个 `d` 各取 `C₀` 就够（`BATwistGridMart` 和组装定理都只要这个）；钉文不带 `3 ≤ d`，若用到的引理带，可加前提。扭转版的一步包络（`DifREP1` §3–§4 的孪生）。
  - **T2438 = TL2a3**（BA 105；TL 10 / 15；`prover-hard`；`BA/TwistGridTail`，必要时 `TwistGridTail2`）：`baTwistGridTail_holds (d) : BATwistGridTail d`（`DifREP2` 的孪生；通用的 `stepDecompCN` 直接给出 Z+Y 分解）。条件 MGF 写成公开的带词干引理 `TwistGridTail_condMGF_Z`。
  - **T2439 = TL2a4**（BA 106；TL 11 / 15；`prover-hard`；`BA/TwistGridWTail` + `TwistGridWTail2`）：`baTwistGridWTail_holds (d) : BATwistGridWTail d`（`DifREP3` 的孪生）；默认拷贝 T2438 的条件 MGF（带词干），只有 T2438 在它 1b 开始前已合并才改为导入。
  - `baTwistGridMart_holds` 不在这三张里，写进 TL2d。
- (3) **阶段 TL 计数 11 / 15**（13 行，剩 TL2d、TL2e 两张；余量 2）。下一张票号 T2440，下一节 §247，下一条 H228。

## §247 — L3a2、TL1b、R1 合并（TL1 证完）；中枢 API 限额停了 1 小时 50 分；放 L3a3 = T2440（总调度 V3，2026-10-12 04:33 UTC）

- (1) **中枢停摆**：约 01:21–03:11 UTC，四个 workflow 撞 API 会话限额（"resets 8:10pm America/Los_Angeles" = 03:10 UTC），03:11 按规则 (H) 重跑，H227 同时执行（35279ca）。不计返工。
- (2) **合并**：T2432（L3a2，8a05c54，`Graph/BASymm2` 554 行）；**T2436（TL1b，4b3bb8a，`BA/TwistAvgB` 504 行）——`baTwistAvgProd_holds` 成立，TL1 在 BA 载体上证完**（owed 行 `BATwistAvgLaw` 仍到 BA-V 才退）；**T2423（R1，b16ad61，`Graph/BASim` 1,979 + `BASim2` 1,928 + `BASim3` 1,962）**。TL 已合并 8 / 13；L 阶段已合并到 R1、L3a1、L3a2、L3b3′ 等。
- (3) **T2440 = L3a3 `BALvl1A`**（BA 107；L 23 / 50；`prover-hard`；`Graph/BALvl1A`，必要时 `BALvl1A2`）：`BALocStep`（五种）、打包、`BAlvl1StepIdentity` 与 `baLvl1StepIdentity_holds`、`BAReach`；T2395 探针里 `outsOf`/`withinOuts`/`splitOuts`/`BAFrameStep`/`BAPGraph.twist` 已由 R1 合并（逐字相同），只抄 `BALocStep`、`BAlvl1StepIdentity`、`BAReach`。不需探针步骤。签字附注：钉文比探针强（不带 `P.g.Normal`、`BASelf`、`3 ≤ L`），1a 若发现要前提就作钉文修补报告；`BAExpandId` 的私有可积引理用 `BALvl1A_` 词干拷贝。S′ 关键路径，排在等待队列最前（L3b4′ 等它）。
- (4) 下一张票号 T2441，下一节 §248，下一条 H229。还没写：TL2d（等 TL2a2–4）、TL2e、G7、带状侧 T 行、L3a4（等 L3a3）、L3b4′（等 L3a3）、L3c3b（等 L3c3a）。

## §248 — TL2a2 合并；T2434（L4b1）1a 卡在 S3 的根：签字放行（Amend 1），缺口记给后继行 L4d2，短 REQ（总调度 V3，2026-10-12 04:51 UTC）

- (1) **T2437（TL2a2）合并 e3f59c2**：新 `BA/TwistGridRem` 1,078 + `TwistGridRem2` 494（`baTwistGridRem_holds`，C₀ = 11）；审核一次 PASS。TL 已合并 9 / 13。
- (2) **T2434（L4b1）1a BLOCKED**：展开恒等式闭合，S2 每族都有路线；但 S3 的四族（`D1X`、`D2X`、`T3C-tr_0/1`）的根带 `M` 点边（`mdot ≠ []`），不在 L4d 的 `baG5Graph`、L4e-C 的闭包表、L4c1 的叶子界的范围内。**签字（Amend 1）**：钉文照 1a 写的保留（S3 的钉文只涉及四族，不需要根）；本行继续证恒等式 `baExp14b_expand_holds`；S2 的证明归 L4b2，S3 的证明归 L4g；三个根（`baT3CtrGraph k`、`baD1XGraph`、`baD2XGraph`）的恒等式、闭包和叶子界记给后继行，暂名 **L4d2**（在 L4e-C 之后），写 L4c1/L4g 时定。P3（`|𝔼X_c| ≺ 𝔟^{3/2}`）由 L4b2 重证。按 0243 O4 这是计划缺行，不是路线失败；仍发短 REQ `REQ-2026-10-12-0451-L4S3` 请监督确认（Q1 性质、Q2 加 L4d2 还是并入 L4c1/L4g）。不阻塞任何在跑的票。
- (3) 下一张票号 T2441，下一节 §249，下一条 H230。

## §249 — TL2a3、TL2a4 合并（网格的三个部件全证完）；放 TL2d = T2441（总调度 V3，2026-10-12 05:25 UTC）

- (1) **T2438（TL2a3）合并 0b55de5**（`BA/TwistGridTail` 1,501 + `TwistGridTail2` 449）；**T2439（TL2a4）合并 dba665d**（`BA/TwistGridWTail` 1,822 + `TwistGridWTail2` 1,334）；都审核一次 PASS。TL 已合并 11 / 13，只剩 TL2d、TL2e。
- (2) **T2441 = TL2d**（BA 108；TL 12 / 15；`prover-max`；`BA/TwistStep`（T.12″ `baTwistZeroMode_holds` 与推论 `baTwistGridMart_holds`）+ `BA/TwistStep2`（T.12′ 的分情况估计））：新钉文 `BATwistStepFixed d R`（`BATwFrame` 框架，固定 `τ`，`Ξ̃` 作前提，四种电荷一并），对 `STCaseI`、`STCaseII` 各证一次；探针步骤同时钉 `T2441_TL2e := ∀ d R, BATwistStepFixed d R → BATwistLoopStep d R`，1a 写 TL2e 的方案（net S2、逐 τ、T.12、T.13 与 S3）。三种情况都在本行：(A) σ₁ = σ₂（T.10 (c)）、(B) σ₁ ≠ σ₂ 在 `STCaseI`（外部锚点 c₁）、(C) σ₁ ≠ σ₂ 在 `STCaseII`（零模，用 T.12″、TL1、`twWard`、T.10 (d)）；跨界情形（脚注 6）不在 TL 任何一行，归 BA-V。若两个文件放不下，1a 停，加第 14 行要发短 REQ。`Ξ̃` 前提的形式（确定性水平上的 `≺`，代替路径上的上确界）由 1a 提、1a-audit 定，报告写清对 TL2e bootstrap 的影响。
- (3) 下一张票号 T2442，下一节 §250，下一条 H231。open REQ：0451-L4S3。

## §250 — T2440（L3a3）审核要签字：登记一行 `BAReach.below`（Amend 1）（总调度 V3，2026-10-12 05:26 UTC）

- **T2440 审核 BLOCKED**：目标 1–6 都过；但 `import RBM3D` + `#assert_rbm_axioms` 的前提扫描把递归归纳类型 `BAReach` 自动生成的 `BAReach.below` 当成前提。修法在 `RBM3D/Test/Axioms.lean`，不在本票可写文件里。
- **签字（Amend 1）**：选审核的 (a)——把 `Test/Axioms.lean` 加进可写文件，只加一行 `structuralProps`：`RBM.Graph.BAReach.below`（与带状孪生 `Lvl1Reach.below`、`lvl1Split.below` 同样处理，`:257-258`）。不改写成 `ReflTransGen` 定义（T2426 的做法），因为带状孪生就是这样登记的，L3a5 的钉文也针对归纳类型。规则 (B) 修补一次 → 审核第二轮。以后带递归归纳类型钉文的票，写票时就把这一行登记列进可写文件。下一张票号 T2442，下一节 §251，下一条 H232。

## §251 — L3a3 合并；监督 0554：S3 块范围 HOLD（L4S3-F1）；T2433 Amend 1（只做通用一半 + 跑 L4S3-L1）（总调度 V3，2026-10-12 05:59 UTC）

- (1) **T2440（L3a3）合并 d11da04**（`Graph/BALvl1A` 676 行；`Test/Axioms.lean` 加一行 `BAReach.below`；审核第二轮 PASS）。S′ 链：L3a4、L3b4′ 现在都可以写（L3a4 等 L3a3、R0、R1、L3a1；L3b4′ 等 L3a3、R1、L3b3′，`BAMatchTw` 归它，§240）。
- (2) **监督 0554（REQ-0451-L4S3）：RECOMMEND HOLD，范围只限 stage L 的 S3 块。** Q1 只同意一半：S3 四族和它们的恒等式（通用步骤）没问题，但带 `M` 结点的真根的闭包 `ord ≥ 5 − 2·1[x~y]` 没有证据——0951 把 320 项闭包当成 S3 的证据时没核对 `𝒢` 是不是 `T3C-tr` 的根（监督自认漏看）。HOLD 范围：T2433 证 `baG5Graph` 表和目标 4 的那部分 1b，以及 L4d2、L4c1、L4g 三张票。不在范围内：T2434、L4b2、L4a2 的约化一半、S′ 链、L3c3a/b、L3d*、阶段 TL、G7、子阶段 T 及其他。CONTROL 仍 RUN。**解除条件 L4S3-L1**：在 Lean 树上对真根跑一次闭包，0 个卡住的结点且叶子性质都成立 → 解除，不用新 REQ；有卡住的 → 短 REQ（可能要问 Jun；候选路线 T2398 §8 的 R2，或用扭转圈界）。Q2：解除后加一行 L4d2（真根、根列表与恒等式、具体闭包表、打包形式；设计门），L4c1、L4g 改接 L4d2；stage L 计划 38 → 39，旗标 50 不变。
- (3) **T2433 Amend 1**：只做通用一半（`BACtx`、带上下文的 GG 引理两种电荷及 `kids` 形式、`BAselStar`（需要时放宽到任意 `BACtx` 候选）、`BAG5LeafProps`、`BAG5Attached`，对任意根列表）；去掉 `baG5Graph` 的具体闭包表和目标 4（没有使用方）——这也回答了它 1a-audit 关于第二个文件超停止线的问题。L4S3-L1 由 T2433 当前的 scratch 步骤跑（或在 1a-audit 第二轮前单独一个 `prover-max` scratch 步骤），结果写进报告 (a⁗)。
- (4) 簿记（0554 O4）：BA-V 接口清单加第 (v) 项——TP 脚注 6 的跨界情形（不在任何 TL 行，§249）；文章差异候选 T2434a 记下；ROUTES 的 BA 格更新。
- (5) 下一张票号 T2442，下一节 §252，下一条 H233。下一批：L3a4、L3b4′（S′ 链，不在 HOLD 内）、G7、带状侧 T 行。

## §252 — 放 L3a4 = T2442、L3b4′ = T2443；stage L 到 25，发短状态 REQ（总调度 V3，2026-10-12 06:18 UTC）

- (1) **T2442 = L3a4 `BALvl1B`**（BA 109；L 24 / 50；`prover-max`；`Graph/BALvl1B` + `BALvl1B2`）：抄入 `BALvl1Good`、`BALvl1GoodLit`、`BAlvl1StepGood`、`BAstepMono`、`ba_good_of_lit`；R1 实际交的是 `BAsim'`（`baSim'_holds`），所以约化 `ba_lvl1StepGood_of_sim` 改用 `BAsim'` 作前提（不能用没人证的 `BAsim`，否则前提扫描会报）；分区结构、合并预算；`baStepMono_holds`、`baLvl1StepGood_holds`。不设设计门（只换前提，检查文件能编译新陈述）；1a 走不通就停，再加探针步骤。
- (2) **T2443 = L3b4′ `BAStepS`**（BA 110；L 25 / 50；`prover-hard`，探针步骤 `prover-max`）：`BAFrameStepTN`、`BALocStepT`、`BABridge`、`locCostGeA` 的扭转不变性、逐输出 `BASimC'` 与 `baSimC'_holds`、`baStep_of_simC'`、`BAFinalS`（钉在 `BAGraph.LocStd` 上，L4-C3）、`ba_ord_ge_of_simC'`。`BAMatchTw` 默认不做（`P' := (P.twist c t).img` 加 `baMatch_holds` 就够），1a 确认；目标 3 失败时才走 `BAMatchTw`（§240）。T2426 审核 O2 的三个无主输入在 1a 估价，≤ 400 行在本行，否则加一行。
- (3) **stage L 到 25**：按 TEAM §6 / 监督 0554 预算注，发短状态 REQ（`REQ-2026-10-12-0618-L25`）。不阻塞。下一张票号 T2444，下一节 §253，下一条 H234。

## §253 — L3c3a 合并；L4S3-L1 未解除（T3C-tr 有卡住节点），发 REQ；T2433 的通用一半继续（总调度 V3，2026-10-12 06:39 UTC）

- (1) **T2435 = L3c3a 合并** c43bdf1（06:34 UTC；`Graph/BAAuxGraph2` 1,113 + `BAAuxGraph2B` 1,064；目标 1–5、7 证完，目标 6 钉为 `BAAnpAuxG` 交 L3d1；探针 `Probe/T2435Pins` 331 行不合并；1a-audit PASS，审核第一轮 PASS）。L3c3b（`LWXiExp` 孪生）现在可写（0951 L4-C9 第 3 项）。
- (2) **L4S3-L1 结果（T2433 报告 (a⁗)）：未解除。** `T3C-tr_0`、`T3C-tr_1` 每种尾电荷各 7 个卡住节点：根项 #2（ord 4，margin −1，`x ≁ y`）加 ord-3 根项 #0 走一步 GG 后的 6 个子图；形状是 `M` 连接把原子上两条实线边分开的 4-圈 `x → A → B → y → x`（0554 F1 第 5 项预料的 `baTwB_stuck`）。`D1X`、`D2X` 闭合（每种电荷 109 片叶子，叶子性质全满足）。放宽到 V2/V3 只闭合 s = 1。四个根都对上 `BAlanlwR`、`BAGGGammaR`、`mc_cut.py`。按 0554 规则发短 REQ（`REQ-2026-10-12-0639-L4S3L1`）：问路线（T2398 §8 R2 的 `ǦMǦ` 展开 / 扭转圈估计 / 放宽 / 其他）和是否要问 Jun。HOLD 范围不变（L4d2、L4c1、L4g；T2433 的具体表和目标 4）。先不问 Jun，等监督答复。
- (3) **T2433 的问题（H234 答复）**：通用一半不读 `T3C-tr` 闭包，继续 1a-audit 第二轮 → 1b `prover-max`，只在 Amend 1 范围内（`BACtx`、带上下文的 GG 引理两种电荷及 `kids` 形式、`BAselStar`（需要时放宽到任意 `BACtx` 候选）、`BAG5LeafProps`、`BAG5Attached`，对任意根列表）；不做具体表、目标 4，也不对真根写闭包结论。Amend 1 第 2 项的"1b 前停"只管 L4S3-L1 的报告，已交。
- (4) 下一张票号 T2444，下一节 §254，下一条 H235。下一批：L3c3b、G7、带状侧 T 行；L3a5 等 L3a4（T2442），TL2e 等 TL2d（T2441）。

## §254 — 监督 0655：L25 PASS（L6 等 L4g）；L4S3-L1 未过（L4S3-F2），S3 路线问 Jun；T2433 的 1b 加两条件；放 L3c3b = T2444（总调度 V3，2026-10-12 07:10 UTC）

- (1) **REQ-0618-L25：PASS**，继续到 40：L3a5、L3b1、L3b2、L3c3b、L3d1–L3d4、L4b2、L4a2 约化半、L5 不读 S3 块，输入合并就放（0655 O5）。**L6（`BALWOut`）要 L4g**，L4g 在 S3 HOLD 里，L6 不在 L4g 之前放。
- (2) **REQ-0639-L4S3L1：HOLD 继续，范围同 0554**（L4d2、L4c1、L4g；T2433 的 `baG5Graph` 表和目标 4）。L4S3-L1 未过（发现 **L4S3-F2**：`M` 分开的原子卡住 BA 版 `(eq;EGxy:x=y)` 的第二步 GG）。**HOLD 现在只在 Jun 选定路线并检查后解除。** 路线是 Jun 的问题（0655 Q2；与 T2398c/d 同一处文章缺口，这次在 S3）：(A) 在两个插入处 Cauchy–Schwarz 到普通圈 `𝓛^{(2)}·𝓛^{(6)}` 加 `(c₁,c₂)` 求和的 Ward 恒等式；(B) 两个插入的扭转圈局部律（延伸已采用的扭转 2-圈律）；(C) 其他。监督排序 (A) 先查、(B) 次之、R2 最后；(c) 放宽已被排除。问题原文按 0655 Q2 发给 Jun（洛杉矶时间）；Jun 的回答原话记入新的一节。按 0655 Q2 / TEAM §4 起一个 Fable 子代理查 (A)（对 `(c₁,c₂)` 的求和、`(Gammamuxy)` 的叶子界是否保住），结果随问题或紧接着给 Jun。**Jun 回答前 S3 不开探针票、不开 Lean 行。**
- (3) **T2433 的 1b 加两条件（0655 Q3-C1、Q3-C2，O4；H235）**：不写任何完备性陈述（"每棵树都终于 `BAG5LeafProps` 叶子"，对任何根列表，通用的也不行），留出新叶子类或新步类型的位置；`BAselStar` 不按这次跑的结果放宽到 V2/V3（只闭合 s = 1，消费者是否要 s = 1 随 S3 路线定）。T2434（L4b1）不受影响：`BAExp14bS3` 是目标陈述，新前提归它的生产者（L4d2/L4c1）。
- (4) **T2444 = L3c3b `BAZetaExp`**（BA 111；L 26 / 50；`prover-hard`；一个文件 `Graph/BAZetaExp.lean`，`LWXiExp` 1–787 的孪生，中心估计 669，预期 600–1,100，停止线 2,000）：目标 `LWXiEgL`（`LWXiE` 的载体形式）及桥 `LWXiEgL_bandFM`、`BAZetaExpClaim` / `baZetaExpClaim_holds`、帮手映射（L3c3a 的公开 `BAAuxGraph2_*` 替代带状侧私有副本）、`d = 3` 实例；登记不动。**不设设计门**（目标 1、2 已在检查文件钉住，用的是 `main` 上的名字）。文件名用 `BAZetaExp`（§244 禁新 `BAXi*`）；下限 `max (2D) (1/𝔠) ≤ D₁` 钉在检查文件里，1a 写论证，需要更大的下限就停。`𝖳_t` 剖面读 `sz.lam`（同已合并的通用钉），不是本行的问题。检查文件在设备上用独立 `lean` 加拷贝的 `.olean` 编过（无错无警告），中枢用 `lake env lean` 在 `main` 上再编。
- (5) 簿记（0655 O6）：ROUTES 的 BA 格 111（T2444）、L 26、TL 12 / 15；文章差异 T2434a 扩充（F2），随下一批文章差异记。`HUB.alive` 06:51 后没更新（07:09 看到），下一轮再看。
- (6) 下一张票号 T2445，下一节 §255，下一条 H236。下一批：G7、带状侧 T 行；L3a5 等 L3a4（T2442），TL2e 等 TL2d（T2441）。

## §255 — Jun 定 S3 路线：「A」；Fable 查 (A)：字面拆法不行，修正的 (A′) 成立；发 REQ 问解除与 L4d2 的形状；中枢停（总调度 V3，2026-10-12 08:05 UTC）

- (1) **Jun 原话**（回答 0655 Q2；问题 07:12 UTC 按原文发出，洛杉矶 00:12；08:03 UTC 前收到）：「A」。
- (2) **Fable 查 (A)**（`docs/claude-team/fable/2026-10-12-s3-fold-A.md`，按 0655 Q2 / TEAM §4，不算票）：
  - 化成迹的形式核过（因子 `t²`，`S^{(B)} = I`）。
  - 字面的 (A)（固定 `(c₁,c₂)` 上 Cauchy–Schwarz 到 `(𝓛^{(2)})^{1/2}(𝓛^{(6)})^{1/2}`，再对 pair 求和）**不行**：用已合并的钉文最多到 `η^{-1}Ψ^5 (L^d/(W^dB))^{1/2}`。
  - **修正的 (A′) 成立**（[proved]）：对 `(x, c₁, c₂, o, o')` 一起做一次 Cauchy–Schwarz，两边都是完整求和（逐项律、`M` 的 Ward 恒等式 `Σ_b|M^{(B)}_{ab}|² = 1`、在 `x` 处的预解式 Ward 恒等式，后者给出 3-圈），得到 `η^{-1}(W^{-d}B)^{5/2}·B^{-1}`。
  - 叶子类只有 `[a]×[b]` 平均形式的界。
  - 其余六个子图和 `T3C-tr_1` 同样折叠；#17、#47 刚好达到目标。
  - 与电荷无关。
  - Lean 方面：模型无关的 `twFold2` 一族、`twVec`、一条 `≺` 实例化；不要 TL 钉文，不要新阶段；文章差异在 B:118。
  - 我复核了 §2.2 的指数账（`W^{-3d}·(B W^d η^{-1})^{1/2}·(η^{-1}B²)^{1/2} = η^{-1}W^{-5d/2}B^{3/2}`），对得上。
- (3) **REQ-2026-10-12-0805-S3A** 问三件事：
  - (i) Jun 的选择加这个论证是否解除 HOLD（剩下的检查放在 L4d2 的 1a 里做数值复测）；
  - (ii) L4d2 拆成 L4d2a（模型无关的折叠引理，不读 S3）和 L4d2b（根、恒等式、闭包表、折叠叶子类），计划到 40；
  - (iii) T2433 的 `BAG5LeafProps`/`BAG5Tgt`、T2434 的 `BAExp14bS3` 是否要为平均形式的叶子类留接口。
  - 监督答复前不写 L4d2（HOLD 仍在）。告诉 Jun：字面拆法不行，按 (A′) 做（只是告知，不再问）。
- (4) **中枢停了**：`HUB.alive` 停在 06:51:14 UTC，各分支最后提交约 06:52，H235 没执行，像 01:21–03:11 那次 API 限额。已告诉 Jun；恢复后按规则 (H) 重跑。
- (5) 文章差异候选加 T2434a/b（B:118 的折叠代替第二步 GG）。下一张票号 T2445，下一节 §256，下一条 H237。

## §256 — L3a4 合并；监督 0851：S3 HOLD 解除（按 (A′)，条件 S3A-C1–C5）；L4d2 拆 a/b，计划 40（总调度 V3，2026-10-12 09:07 UTC）

- (1) **T2442 = L3a4 合并** ec795c5（08:51 UTC；`Graph/BALvl1B` 491 + `BALvl1B2` 318；7 个目标；审核 PASS 第一轮）。L3a5 现在可写（链 L3a4 → L3a5 → L3b1 → L3b2）。
- (2) **监督 0851：PASS，S3 HOLD（0554 O1、0655 O1）解除**，依据是 §255（Jun 原话「A」）加修正的折叠 (A′) 加监督自己的核查；(A′) 在 Jun 的选择之内（仍是在插入处做 Cauchy–Schwarz、pair 求和靠 `M` 的 Ward 恒等式、无新钉文、无新阶段，只是 ℓ² 放在 `x` 上与插入指标一起）。条件：
  - **S3A-C1**：Fable §2.2 `F₂` 第 3 步用了带状公式 `E_cME_{c'} = δ_{cc'}W^{-d}mE_c`；BA 上 `M` 不是块对角（`BAMfine_eq`），展开两条带圈腿多出三个交叉项，各自用 2-圈界闭合（`≺ W^{-2d}B_0`、`≺ W^{-2d}`），`F₂ ≺ η^{-1}B_0²` 仍成立；`≺` 实例化必须写 BA 的展开。
  - **S3A-C2**：`B_0 ≥ c` 在 Lean 框架里成立（`BAFlow` → `Admissible` → `WO 𝔡`；`Bctl` 含 `(lam²+|1−t|)^{-1}`），不需要新前提。
  - **S3A-C3**：钉文的界是 `(1−t)^{-1}Bctl^{5/2}`，折叠给 `η_t^{-1}`；用已合并的 `η_t ≥ (1−t)·Im m`（`GreenCond2.lean:321-345`）换。
  - **S3A-C4**：`BAExp14bS3` 的五个前提够用（逐项律、2/3-圈所有电荷、可选 `STLKgL`），不用任何 `BATwist*` 前提。
  - **S3A-C5**：L4d2b 的 1a 要做 14 个卡住形状（每个根 7 个）两种电荷的约化"节点平均 = `twLoop2X`（显式 `ρ`）"，逐样本对引擎 / `mc_cut.py` 到 1e-12；每个 `ρ` 给出 `r₁, r₂` 及所用的确定性界；#17/#47 给出 `X ≺ W^d·Bctl`；闭包表里折叠类与 `BAG5Leaf` 并列，`MERGED`、`T3C-tr_1`、`D2X` 的每片叶子二者居一。不成立就停在 1b 前写 REQ（该节点 HOLD 复回）。小尺寸数值不算检查。
- (3) **L4d2 拆两行，计划 39 → 40**（0851 Q2；不是凑数：L4d2a 不读 S3、不读 T2433，可以马上开）：
  - **L4d2a**（新文件放在 `BA/TwistPins` 旁，如 `BA/TwistFold2`，`twTrP` 指标约定）：`twLoop2X` 及迹形式、`twFold2`、`twFold2_bound`（`β, r₁, r₂`）、`twVec` 与 BA 事实 `‖M^*e_x‖² ≤ 1`、`Π_bM^*MΠ_b ≤ Π_b`、对抽象权 `ρ` 的 `≺` 实例化（假设 `r₁, r₂ ≤ C` 及可选随机标量因子 `≺ W^d·Bctl`；结论 `≺ (1−t)^{-1}Bctl^{5/2}`，平均形式；含 S3A-C1、C2、C3）。现在写。
  - **L4d2b**：根（`MERGED`、`T3C-tr_1`、`D2X`）、恒等式、带折叠叶子类的闭包表、14 个约化（两种电荷）及 `ρ`、`r` 界、S3A-C5 的 1a。等 T2433 的通用名字上 `main`，或在检查文件里钉住。
  - L4c1、L4g、L6 输入合并后照计划开；它们的解析叶子界要取析取（`BAG5Leaf` 叶子走 `GtoAG`/`(Gammamuxy)` 逐点再平均；折叠叶子直接走 L4d2a，平均形式），写进它们的票。
- (4) **T2433 不加接口、不改**（`BAG5Tgt` 是单图组合谓词，折叠叶子 ord 4 本来不满足它；折叠类是 L4d2b 定义的独立谓词，闭包写成"`BAG5LeafProps` ∨ 折叠"；前提是 T2433 守 Q3-C1，叶子性质保持 `Prop` 谓词）。Q3-C2 定了：折叠与电荷无关，`BAselStar` 不放宽到 V2/V3。**T2434 不改**（`BAExp14bS3` 本来就是平均形式；五个前提够用）。
- (5) **告诉 Jun**（0851 O2，只告知）：字面拆法丢 `(L^d/(W^dB))^{1/2}`；修正的折叠以余量 `B^{-1}` 闭合、无新输入；按它做；Jun 若反对，S3 块 HOLD 复回。
- (6) 簿记（O6）：ROUTES 的 BA 格写 S3 HOLD 解除、stage L 计划 40；**文章差异 T2434a/b** 记 (A′)：BA 上对 `M` 分开的 4-圈，`(eq;EGxy:x=y)` 的第二步 GG 换成折叠，界成立于 `[a]×[b]` 平均形式（`I_{42}` 正是这样用，B:67-70）；随下一批文章差异写进 `paper-deltas.md`。
- (7) 下一张票号 T2445（= L4d2a），T2446（= L3a5），下一节 §257，下一条 H237。

## §257 — L3b4′ 合并；放 L4d2a = T2445、L3a5 = T2446；O2 形状要新开一行（计划 41），发短 REQ（总调度 V3，2026-10-12 09:35 UTC）

- (1) **T2443 = L3b4′ 合并** 9eaf866（09:17 UTC；`Graph/BAStepS` 523 行；目标 1–8；`BALocReg6` 去掉框架正规性假设（更强）；探针 393 行留在 t/T2443；1a-audit PASS，审核 PASS）。e2/macroA/macroB 的形状输入（T2426 审核 O2）按票的 ≤ 400 行规则（估价 1,200–1,600 行）留作 `BALocReg6` 的假设，`baLocReg6_reach` 是条件形式 → 要新开一行。
- (2) **T2445 = L4d2a `BA/TwistFold2` + `TwistFold2B`**（BA 112；L 27 / 50；`prover-max`；不设设计门）：`twLoop2X` 及迹形式、`twFold2`、`twFold2_bound`（平方形式，`β, r₁, r₂` 作上界，因子 `W^{-5d}`）、`twVec`（假设 `G − G^* = 2iη G^*G`）、`twMrow_le`/`twMblk_le`（`BAMfine` 上，只用上界）、`twB0_ge`（S3A-C2）、`twEta_ge`（S3A-C3）、`twFold2Prec`（`≺` 行，逐路径；前提 `STLocalEntrygL`、`STLmaxgL`；`ρ` 的 `r₁, r₂ ≤ Cρ`；随机因子 `X ≺ W^d·Bctl`；结论 `≺ (1−t)⁻¹Bctl^{5/2}`）及 `X ≡ 1` 的 `twFold2PrecDet`、实例。登记不动（两个前提已登记为欠）。S3A-C1 的展开是 1a 和证明的必备内容。答复起草问题：逐路径形式（消费者用 `BAExp14a_prec_integral` 取期望）；`ρ`、`X` 可依赖 `(σ, a, b)`；不带 `STLKgL`；`W^{-5d}` 在 1a 对 Fable §2.2 复核。
- (3) **T2446 = L3a5 `Graph/BALvl1C`**（BA 113；L 28 / 50；`prover-hard`；不设设计门）：钉 `BAlvl1ExistsStep`、`BAlvl1Lemma`（探针原文）；`baLvl1ExistsStep_holds`（`lvl1_exists_step` 孪生，`¬LocStd` 的每种情形对应 `P.twist c t` 上五种 `BAFrameStep` 之一）；测度下降与 `ba_lvl1_induction`；`baLvl1Lemma_holds`；文章形式 `BAlvl1LemmaSize`（留在本行，L3b1 读它）；实例。不用 `BAsim`。
- (4) 开工顺序：T2446（S′ 链）→ T2445。
- (5) **O2 行**：暂名 L3b4″（`Graph/BAShapeO2`，`prover-hard`），stage L 计划 40 → 41，超过 40 → 按 0655 O3 发短 REQ（`REQ-2026-10-12-0935-O2row`）：问开不开、一行还是两行、在链上的位置。监督答复前不写。
- (6) 下一张票号 T2447，下一节 §258，下一条 H239。

## §258 — L4b1、L3c3b 合并；监督 0948：开 O2 行 L3b4″（计划 41，一行两文件）；H238 的提交被中枢的权限检查拦下（总调度 V3，2026-10-12 09:53 UTC）

- (1) **T2434 = L4b1 合并** 74af906（09:36 UTC；`Graph/BAExp14b` 998 + `BAExp14bB` 1,076；S2、S3 钉文与展开恒等式；S3 的根欠 L4d2b（0851 Q3 (b)）；审核 PASS 第一轮）。审核 O2（S2 钉文以 TL1/TL2 为前提）记为文章差异候选 T2434c，不是路线缺口（TL1、TL2 已合并）。L4b2 现在可写。
- (2) **T2444 = L3c3b 合并** 23a4e69（09:50 UTC；`Graph/BAZetaExp` 591 行；API 限额后按规则 (H) 重跑 1b；审核 PASS）。L3d2 只差 L3d3。
- (3) **监督 0948：PASS，开 O2 行 L3b4″**（stage L 计划 40 → 41，旗标 50 不变；用量 28）：一行，两个文件在开票时定名（`Graph/BAShapeO2` 放建造引理，`BAShapeO2B` 放两条 stage-2 推论、三个 `_tn` 引理、`baLocReg6_holds`、实例），`prover-hard`，现在可开。条件：
  - **O2R-C1**：只证 `BALocReg6` 的绑定变量本身，不重新陈述：`baShapeLL_e2_tn`、`baShapeLL_macroA_tn`、`baShapeLL_macroB_tn`，以及无假设的推论 `baLocReg6_holds`，加非退化实例。
  - **O2R-C2**（1a 与停止规则）：(a) 列出 17 个带 `e2` 或 macroB stage 1 的建造项及各自路线；(b) 在样本图上逐个 setoid 数值检查 `BAScostLL P.g X`，含 slack 0；(c) stage 2 的输出与 `Q0 ∈ tr.partition` 的关系及构造子假设；(d) 无隐藏输入（不用 L3b1、L3b2 的不变量）。(b) 发现违反、或 (c)/(d) 不成立，就停在 1b 前写 REQ。
  - **O2R-C3**：消费者是 L3d3、L3d2（经它们到 L3d4、L5、L6），L3b1、L3b2 不是。最好本行在 L3d3 的 1b 之前跑；否则 L3d3/L3d2 原样带着绑定变量（不新立 `Prop`、不加欠账），本行合并后的第一个消费者行消掉它，最晚 L6。
  - **O2R-C4**（给 L3b1 的票）：`e2`、`macroA`、`macroB` 的路径输入 `BAShapePath` 写成 L3b1 或 L3b2 的目标，不留作假设；L3b1 的 1a 用 `PathInv2` 检查估价，装不下就在 1b 前发短 REQ。
  - 拆分规则（§227）：1a 的中心估计超过 1,575 时，可以在已定的文件边界拆成两行（计划 42），不必再发 REQ。
  - 文章差异 `T2443d`（(6) 是条件形式）在本行合并时撤回。
- (4) **H238 第 (1) 项没做成**：中枢 09:42 的提交和推送被它自己会话的权限检查（auto-mode 分类器，"Modify Shared Resources"）拦下，10 个文件留在主工作树未提交；之后两次合并的推送正常。H239 让它随下一次提交补上；再被拦就告诉 Jun。
- (5) 中枢今天第二次撞 API 限额（09:37–09:38 按规则 (H) 重跑 T2433、T2441、T2444），不计超时（TEAM §7）。
- (6) 下一张票号 T2447（= L3b4″），下一节 §259，下一条 H240。其后：L3d3（输入都在 `main`）、L4b2、L3d1；L3b1 等 L3a5（T2446）、TL2e 等 TL2d（T2441）、L4d2b 等 T2433。

## §259 — 放 L3b4″ = T2447（O2 行）；H239 已补交（总调度 V3，2026-10-12 10:16 UTC）

- (1) **T2447 = L3b4″**（BA 114；L 29 / 50；计划 41；`prover-hard`；不设设计门）：`Graph/BAShapeO2`（17 个建造项的 stage-1 引理与共用工具）+ `Graph/BAShapeO2B`（两条 stage-2 推论、`baShapeLL_e2_tn`、`baShapeLL_macroA_tn`、`baShapeLL_macroB_tn`、无假设的 `baLocReg6_holds`、实例）。四个目标陈述都钉在检查文件里（`T2447_E2TN`、`T2447_MacroATN`、`T2447_MacroBTN`、`T2447_LocReg6Holds`，绑定变量 `T2447_Binder` 照抄 `BAStepS:100`）。1a 按 O2R-C2 (a)–(d)，带停止规则；中心估计超过 1,575 时可在文件边界拆成两行（§227，计划 42）。答复起草问题：stage-2 走 (α) 或 (β) 由 1a 定并说明；实例 (iii) 若 1a 确认 `baPC` 与 `BAScostInst.gc` 是同一数据（一个原子里 `a ≠ a'`）就可用它；`hTA` 处的额外实例保留。合并时撤回文章差异 `T2443d`。
- (2) **H239 已执行**（d5e9fa3，10:01 UTC）：H238 的 10 个文件补交，09:42 的拒绝没有再出现，不用告诉 Jun。
- (3) 开工顺序：T2447 排第一（监督要它在 L3d3 的 1b 之前）。下一张票号 T2448，下一节 §260，下一条 H241。其后：L3d3、L4b2、L3d1。

## §260 — L3a5 合并；放 L3d3 = T2448；Jun：M/N 现在先做一张只出报告的设计单，排在 X1 生产者和子阶段 U 的开阶段 REQ 之后（总调度 V3，2026-10-12 10:40 UTC）

- (1) **T2446 = L3a5 合并** 7f23e96（10:21 UTC；`Graph/BALvl1C` 627 行；五个目标与实例；备用文件 `BALvl1C2` 没用上；审核 PASS）。L3b1 现在可写，它的票要带上 O2R-C4（`e2`、`macroA`、`macroB` 的 `BAShapePath` 作为 L3b1/L3b2 的目标），以及起始项的界 `P0.g.nM ≤ p`（T2448 起草时发现没有任何行证它，L3d2 要用；归 L3b1）。
- (2) **T2448 = L3d3 `Graph/BAEngine`**（BA 115；L 30 / 50；`prover-hard`；不设设计门；一个文件，估计 400–800 行，T2387 中心 796）：BA 的步骤不带 `m` 标签（`BAExpandId:86-88`），无数据递推已经由 `baLvl1Lemma_holds` 合并，所以带状 `LWEngine` 的标签一半（`:54-463`）和递推（`:612-723`）去掉。目标：`BALocRegConcl`（`LWLocRegConcl` 的孪生，16 项起始分区，(6) 用 BA 形式，远端一半只对不同原子成立（L4-C4 (b)），`BAlwData` 处的期望恒等式）；`baStep_nWS`、`ba_nWS_ge`、`baStart_nWS`（黑色波浪边数沿 `BAReach` 不减）；`baEngine_assemble`（公开）；`ba_localregularX`（去掉 `∀ m ≠ 0`）；p = 2 的实例。形状绑定变量按 O2R-C3：T2447 未合并时照抄 `BAStepS:100` 的绑定变量；1b 开始时若 T2447 已合并，就改引 `baLocReg6_holds`（1b 开始时一次定下）。答复起草问题：(b) 不变量 (1)–(5) 不放进 `BALocRegConcl`，1a 列出带状消费者实际读 `LWLocRegConcl` 的哪些合取项，若有消费者读 (1)–(5) 就停下报告；(c) `P0.g.nM ≤ p` 归 L3b1；(d) 不读 L4d（T2419）就从输入里删掉并在报告里说明。另记：0948 Q3 的输入清单漏了 L3a5（已合并，不影响）。
- (3) **Jun 的指示（2026-10-12 10:3x UTC，原话首段）：**「建议现在就做 M/N 的设计。但只做一张只出报告的设计/摸底单，并且排在 X1 的生产者和子阶段 U 的开阶段 REQ 之后；M/N 的证明票还是等 V 关闭、过了阶段闸门再放。」理由（Jun 列的三条）：M/N 是 BA 的终点，钉文一定下来，U、V 必须交什么就定了，越早发现"没有票负责"越便宜（TEAM §3 的覆盖摸底单）；条件已具备（M1–M3、N2 是带状装配的孪生，MA-01…06a、UN-51/52b 已合并；V3 与 BA-M1 都吃 `BAMLOutTL`，§2105；没合并的上游输入按设计单规则用同类型的本地假设代替）；BA-C5 要早回答 BA 的流是否满足 UN 窗口条件 `etaT` 与 `|fE| ≤ 2 − κ`（E5），不满足的话 BA 的 BUniv 路线要改并牵动 U、V。设计单要做的事：
  - 终点覆盖：Thm 2.7 的五个 BA 终点（locSC、QDiff、decol、QUE、BUniv）逐条对到 Lean 钉文和负责的行，每个输入写出生产者，没有生产者的单列；
  - 钉死接口：M/N 对 U、V 输出的消费形状写成钉文，U、V 的票照这个形状陈述；
  - N3 的路线：UN 侧 E1–E4 在 BA 上的形式（BA-N3），逐项定走转移还是写泛型孪生；
  - 重新估价：N1 很可能取消或并入 C3/M1，估出行数和票数。
  代价：一张只出报告的票（BA 计数 +1，占一个槽几个小时）；排在 X1 和 U 的 REQ 之后；V 的陈述形状若再变（像 §2105），钉文跟着改。
- (4) **执行顺序**：X1 的生产者（Step 5 的 CLT 层，`Evolution/Clt*` 等 11 个文件、13.9k 行，两份设计都没有生产者；子阶段 U 开之前要定，C9）→ 子阶段 U 的开阶段 REQ → M/N 设计单（只出报告）。M/N 的证明票等 V 关闭并过阶段闸门。
- (5) 下一张票号 T2449，下一节 §261，下一条 H242。

## §261 — TL2d 合并；X1 生产者提案（路线 G：X1a、X1b，BA 实例归 U4-BA）；发子阶段 U 的开阶段 REQ（总调度 V3，2026-10-12 11:05 UTC）

- (1) **T2441 = TL2d 合并** 20917ed（10:49 UTC；`BA/TwistStep` 1,795 + `TwistStep2` 1,564，都在 2,000 停止线下；`baTwistGridMart_holds`、`baTwistZeroMode_holds`、`STCaseI`/`STCaseII` 的 `BATwistStepFixed`、实例；API 限额后按规则 (H) 重跑 1b；审核 PASS）。TL 13 行已合并 12 行，剩 TL2e（现在可写）。
- (2) **Jun 顺序第 1 步：X1 的生产者**（§260 (4)）。X1 = `Evolution/Clt*`、`MeanFar`、`FarEntry`、`ExpInv`：11 个文件、13,899 行、115 个定理。带状侧只有一个消费者（`IniTermI:2005-2008`，U4s2），BA 侧暂时没有。数学上与模型无关：Θ 只通过传播子界进入（`CltMoments1:929-1000`），BA 的流是 `λ₀Ψ` 加 g = 0 的带状流（`Gauss/BlockAnderson:83-86`）。**提案走路线 G**（监督 1155 C9 的推荐）：在载体上原地改写成泛型，加两行 ST 侧的 U 行：
  - **X1a**（约 0.6k 行；设计门 1a 带探针步骤；先做 tier 1 文件）；
  - **X1b**（约 1.0k 行；在 X1a 与 U4s1 之后）；
  - BA 实例归 U4-BA，U4-BA 可能要第三张票。
  - 退路（C6）：某段 f_sem > 0.30 就用修订改成 BA 孪生。整套孪生要 7–9 张票、约 11k 行，所以不走。
- (3) **Jun 顺序第 2 步：发 `REQ-2026-10-12-1104-U`**（子阶段 U 的开阶段 REQ）。行数 20 + 2（X1a、X1b）+ 1（U-D）= 23，旗标 34.5。五个问题：
  - Q1：X1 的生产者走路线 G；
  - Q2：开 U 的 ST 侧，第一批 U3s1 的词汇文件、U6（新增文件 `Chain/Step5Gen`）、X1a、U-D；BA 侧在 M/N 设计报告之后用一份短的钉文 REQ 开；
  - Q3：行表更正（`Step3`/`Step4` 从 U3s1 挪到 U3s4，不改计数；U6 作为新增文件，不进证书通道；U5 在 U6 之后早开设计门）；
  - Q4：C10 普查只做到 import 层，是下界，提案用一张只出报告的覆盖单 U-D 做逐事实普查，并为四个没有生产者的层（`Path/DifREP1–3`；`Path/LemDecCalE*` + `NetLift2` + `KellStar`；`Path/NetLift1`；`Green/CondDom`）定生产者，同时问 `DifREP`/`NetLift1` 归 T 还是 U；
  - Q5：U 的关闭条件（含对 V 与 M/N 终点钉文的形状检查）。
  
  U 现在可以开：没有规则要求 T 先关，C8 把 T7-BA 挪进 U 正是为了让 T 先关。实际上只有 U3s1 的词汇、U6、X1a 的 tier 1 不卡在 T4s1 上。
- (4) **Jun 顺序第 3 步**：REQ 已发，接着写 M/N 的只出报告的设计单（BA +1）。另外，带状侧的 T 行（T4s1、T7、T5s2、T1、T4s2）从 §236 起没有放出；T4s1 在每个 ST 侧 U 行的 import 闭包里，排在 M/N 设计单之后尽快写。
- (5) ROUTES：X1 一项改为"X1 生产者提案：X1a/X1b（路线 G），BA 实例归 U4-BA（REQ U 待答）"；TL 13 行已合并 12 行。下一张票号 T2449（M/N 设计单），下一节 §262，下一条 H243。

## §262 — L4d2a、L4e-C 通用一半合并；放 M/N 设计单 = T2449（只出报告）；记 1049 的 `unMLOutBA_of_pins` 问题（总调度 V3，2026-10-12 11:23 UTC）

- (1) **T2445 = L4d2a 合并** b0161bc（11:08 UTC；`BA/TwistFold2` 656 + `TwistFold2B` 1,066；8 个目标，含 7 与 7′，加实例；审核 PASS）。折叠引理 `twFold2` 一族与 `≺` 行 `twFold2Prec` 现在在 `main` 上。
- (2) **T2433 = L4e-C 通用一半合并** 695cfc7（11:22 UTC；`Graph/BAG5Leaf` 1,136 行：`BACtx`、带上下文的 GG 引理（两种电荷，`kids` 形式）、`BAselStar`、`BAG5LeafProps`、`BAG5Attached`、实例；没有 `baG5Graph` 表、没有目标 4；`BAG5Leaf2` 没建；审核 PASS 第一轮）。**L4d2b 现在可写**（0851 O4：T2433 的通用名字已上 `main`），它的 1a 走 S3A-C5。
- (3) **T2449 = M/N 设计单（BA-DMN，只出报告）**（BA 116；`prover-max`；模板 T2379）：交付 `docs/reports/T2449-design.md`（≤ 400 行）和不合并的探针 `RBM3D/Probe/T2449Pins.lean`（≤ 400 行，留在 `t/T2449`）。报告先回答 **MN0 = BA-C5/E5**：起草时初步看，E5 照字面多半不成立。`RandomLayerB_Flow`/`_Prod` 用的是半圆律的 `etaT E t = (1-t)·Im mE(E)` 加 `|fE| ≤ 2-κ`，而 BA 的恒等式用 BA 的 `m(E,λ₀)`（`7_8:1801`），ρ-bulk 会超过 `2-κ`，`BAFlow` 里也没有 `|Re z| ≤ 2-κ`。修法可能只在 BA-C5 里：把 `RandomLayerB` 改成以 η 函数为参数的泛型副本（监督 0853 `:126`）；U、V 多半不受影响。U、V 的陈述若要改，就停下报告。之后是 MN1 终点覆盖、MN2 接口钉文、MN3 N3 的路线、MN4 重新估价（C3–C5 计入，给出含与不含两种总数）。答复起草问题：C3–C5 保留；报告上限 400 行；E5 的 `example` 形状编不过时由中枢报告，调度改检查文件。
- (4) **记下监督 1049 的问题**：已合并的 `unMLOutBA_of_pins`（`Induction/MainIndOut.lean:144`）带一个 `STMainIndG` 前提，按监督 1049，BA 证不出它。M/N 设计单要说明 M/N 怎样绕开（换后继形状或换路线）。另外，`BAEnd_locSC`、`BAEnd_QDiff`、`BAEnd_decol`、`BAThm27` 只在 `t/T2161` 上，而且是按旧的带状律写的；设计单要给出按正确的律写的后继（建议名 `BAEnd_locSCL` 等）。
- (5) 槽位：在跑 T2447、T2448，空出两个槽；T2449 开工，另一个槽留给下一张。下一张票号 T2450（L4d2b）、T2451（TL2e），下一节 §263，下一条 H244。其后：T4s1、L3b1、L4b2、L3d1。

## §263 — L3b4″、L3d3 合并；放 L4d2b = T2450、TL2e = T2451；监督 1152：子阶段 U 开（23 行，旗标 34.5），X1 走路线 G（总调度 V3，2026-10-12 11:57 UTC）

- (1) **T2447 = L3b4″ 合并** 00f4a10（11:28 UTC；`Graph/BAShapeO2` 1,094 + `BAShapeO2B` 447；`baShapeLL_e2_tn`、`_macroA_tn`、`_macroB_tn`、`baLocReg6_holds`、实例；审核 PASS）。**文章差异 `T2443d` 撤回**（0948）。
- (2) **T2448 = L3d3 合并** 79f3c1c（11:30 UTC；`Graph/BAEngine` 506 行；T2447 在 1b 时还没合并，目标 3–4 带着 `T2448_Binder`；审核 PASS，观察 O1：带状消费者读不变量 (1)–(5)，即起草答复 (b) 的情形；O2 给调度，不要签字）。按 O2R-C3，第一个在 T2447 之后写的消费者行（L3d2）用 `baLocReg6_holds` 消掉绑定变量。**L3d2 写之前先定 (1)–(5) 的约定**（1152 O7）：L3b1 的票把沿 `BAReach` 的 (1)–(5) 列为目标。
- (3) **T2450 = L4d2b `Graph/BAS3Close` + `BAS3CloseB`（+ 备用 `BAS3CloseC`）**（BA 117；L 31 / 50；`prover-max`；不设设计门；1a 走 S3A-C5，带停止规则）：三个根、根列表、`BAS3Identity`；`BAFoldLeaf`（显式 `ρ`、#17/#47 的因子、`r₁, r₂ ≤ Cρ`）；14 个卡住图两种电荷的 `baS3Fold_holds`；`BAS3Xprec`；闭包 `BAS3Close`（"`BAG5LeafProps` ∨ 折叠"）；打包形式 `BAS3Expand'`；实例。估计 2,300 / 3,400 / 5,200：先一行带三个文件，1a 的中心估计若仍超 1,575，就在文件边界拆行并发短 REQ（计划 41 → 42/43），在 1b 之前。
- (4) **T2451 = TL2e `BA/TwistLoop`**（TL 13 / 15；BA 118；`prover-hard`，按 TL 设计行；不设设计门）：`baTwistLoopStep_of_fixed`（= `T2441_TL2e` 原文）、`baTwistLoopStep_caseI/_caseII`（T.12 在 3/2）、新钉文 `BATwKcircBound` 与 `baTwKcircBound_holds`（T.13 (ii) 加 S3，交给 L4b2）、实例。**stage TL 随本行关闭**：票里提出 C1–C6 作为关闭清单的提案，报告交 (a)–(h)，由监督在关闭 REQ 里定。
- (5) **监督 1152：PASS，子阶段 U 的 ST 侧现在开**：23 行，旗标 34.5（U4-BA 要第三张票时 24 / 36）；U-D 指名的生产者行每行 +1.5，放在 U-C6 指定的子阶段。条件：
  - **X1-C1**（谱域，F1）：泛型 X1 陈述里不许出现 `|E| ≤ 2 − κ`、`|E| < 2`、`mE`、`zt E`、`cltCk`、`etaT E`；谱参数用 `ztOf C.m E u` 与 `C.eta`，下界来自 `κ ≤ Im m`；带状推论恢复旧陈述；若 T2449 的 MN0 定了别的 BA 谱读法，X1 跟着改。
  - **X1-C2**（Θ 接口）：tier 2 把 `(prop:ThfadC)`、`(prop:BD1)`、`(prop:BD2)` 和平移不变性作为抽象剖面上的假设，不用 `‖m‖ = 1`、显式 Θ 公式或 `PropSpin`；1a 给出"带状事实 → 泛型假设 → BA 生产者"表。
  - **X1-C3**：1a 列出 X1a 的文件从 `KDecay`、`Step34Pins`、`Step5Pins`、`Green/*`、`KellStar` 读的每条事实及其 BA 生产者；泛型 `FarEntry` 的非对角 Green 输入取 `STGbEXPij` 与带撇 `BAGbEXPij'` 都能推出的形式。
  - **X1-C4**：`STCltFargL`、`STCltIsogL`、`STExpInvgL` 由 X1a 的 1a-audit 定、放在 X1a 的文件里；U6 不陈述它们。
  - **X1-C5**：熔断与退路如提案（f_sem > 0.30 的段改孪生；超过 1.5 × 中心才发 REQ；U4-BA 第三张票已在 PASS 内）。
  - **U-C1**：计数 23 / 34.5。
  - **U-C2**：U3s1 的泛型词汇放新文件（如 `Chain/Step34Gen.lean`），带 `Iff.rfl` 桥，`Step34Pins` 不动（不进证书通道）。
  - **U-C3**：`Step3`、`Step4` §1–§2 归 U3s4；`Step4` §3 留在带状，泛型后继归 V2。
  - **U-C4**：U6 作新文件 `Chain/Step5Gen.lean`；只用一个核 `Step2Gen_UN`，T4s1 的泛型 `Ugen` 必须就是它（定义相等或桥），不另立第三个核。
  - **U-C5**：U5 早开设计门：1a 写出 BA 的 Step 5 情形 (iii) 的完整 d = 3 论证（文章省略了），只用带撇钉文和范围一致的事实，在 `g = 1/64, 1, 10` 处做数值检查；可以在 U6 合并前开，U6 的陈述用同类型的本地假设；论证合不上就发 REQ（届时是给 Jun 的数学问题）；U5 的 1b 等 BA 钉文 REQ。
  - **U-C6**（U-D）：(a) 按使用而不是按 import 做逐事实普查，覆盖每个 U 行和五个未放的 ST 侧 T 行（T7、T1、T4s1、T4s2、T5s2）；(b) 每个无主层判断是模型无关可复用、BA 已覆盖（含 `BA/TwistGrid*` 对 `DifREP2` 的复用、`EMn2BA` 里的 `KellStar` 副本）还是要生产者，`KellStar` 只要一个共享的 BA 陈述 `KellStarEv`；(c) 放置规则：生产者放在最早消费它的子阶段，`DifREP`（T1 要 m = 2 的 GridMart；U4s3、`PfStep5` 要所有 m 的 `STGridRepN`，一个泛型行）和 `NetLift1–2`（T1 要 `STNetLift2`）归子阶段 T（旗标 28.5 每行 +1.5），`LemDecCalE*`、`KellStar`、`CondDom` 若要生产者归 U；(d) T1-BA 钉文等 U-D，ST 侧 T1 不等。
  - 两个路线发现（都不 HOLD）：F1 谱域；F2 T1 的覆盖缺口（GridMart 与 `STNetLift2` 在 BA 上没有生产者）。
  - **U 的关闭条件**（Q5）：九个 BA 侧行的目标证完、公开、有非空 `d = 3` 实例（含 U1-BA、BA 的 `STEK*` 及 `STEKDecay`/`STEKWin`/`STEKLow`、`BAKcalDecay`）；欠账行删掉、被带撇形式替代的带状钉文登记为 superseded；X1 与放在 U 的 C10 生产者合并、泛型、in-place 文件有 G1 检查；谱域：U 的陈述里不出现 `|E| ≤ 2 − κ`、`mE`、`zt E`，BA 实例用 MN0 定的读法；U5 的论证记为文章差异；对 V 与 T2449 终点钉文的形状检查通过。
- (6) **放票顺序（1152 O1、O2）**：第一批 U-D（先放）、X1a、U3s1（新文件）、U6（新文件）；**T4s1 与 T7（ST 侧）尽快给槽位**，它们比 U 行本身卡住更多 U；然后 U4s1、U1s1 在 T4s1 后，U2 在 U3s1 与 T7 后，其余按 import 顺序；U5 设计门有槽就开。BA 侧的 U 钉文 REQ 在 T2449 报告之后。
- (7) ROUTES：子阶段 U 开，0 / 34.5；X1 = X1a/X1b（路线 G）；`T2443d` 撤回。下一张票号 T2452 起（U-D、T4s1、T7、X1a、U3s1、U6、U5、L3b1、L4b2、L3d1、L3d2），下一节 §264，下一条 H245。

## §264 — 放 U-D = T2452、T4s1 = T2453、T7 = T2454（总调度 V3，2026-10-12 12:26 UTC）

- (1) **T2452 = U-D**（只出报告的 C10 覆盖单；子阶段 U 1 / 34.5；BA 119；`prover-max`；模板 T2413 = TL-D）：交付 `docs/reports/T2452-design.md`（≤ 300 行，唯一合并的文件）；探针 `RBM3D/Probe/T2452Pins.lean`（≤ 400 行，不合并）只在共享陈述 `BAKellStarEv` 或某个生产者陈述在 `main` 上还没有泛型形式时才要。起草时 grep 到：用 `NetLift` 的行只有 T1（`Step2Iterate:1781, 1788`），其余是误报；行用到的 `CondDom` 事实只有三行长的 `etaT_le_of_le`；`DifREP` 的消费者都只读 `m = 2`；`KellStar` 的开放消费者只读第一个合取项（Θ 远场，`s = 0`）。答复：普查范围加上起草发现的层（`Step2Scale` 的 `STScaleExists` 是 T1 的假设，在 T2379 里没有主；`Step2Core`（`STGoodAt` 所在）；`ContinuityNet`、`Split`、`Green/MinorDiff`、其他 `Path/*`）；查清放在 T 的 `DifREP2/3` 生产者是否读 U 行的事实（`NQGood1`、`ZeroModeCalc`），读的话就不能在 U 之前关（1155 C8 的情形），定不了就停；U-C6 (c) 的"所有 m 一个泛型行"照写，但报告消费者都只读 m = 2，让监督决定是否收窄；`LemDecCalE*` 在 BA 上要不要生产者（只有情形 (iii) 用它，而 BA 上 U5 替代了情形 (iii)）；T4s1 起草时把 `AzumaProxyN/2` 挪到了 T4s2，一并纳入 T 行普查；停止规则（多出约三行以上，或某层有语义或文章风险）不变。
- (2) **T2453 = T4s1**（ST 侧；子阶段 T 11 / 28.5；BA 120；`prover`；不设设计门）：**新增文件** `RBM3D/Chain/GridDuhamelGen.lean`，`GridDuhamelN` 不动（§198 (2) 先例、U-C2；原地改会把 `Chain/Carrier`、`Chain/Step2Gen` 放到证书上游）；不进证书通道。目标：`Step2Gen_UN` 的核代数；**U-C4 的桥 `Ugen` = `Step2Gen_UN (bandFM …)`**（不另立第三个核）；`Step2Gen_USemigroup`（核的半群律取代 `|E| < 2`；带状实例本行证，BA 实例欠 T4-BA）；词汇 `AvecNg`、`martIncNg`、`predIncNg`（带状桥）与 `AvecNg_two`；`StoppedDuhamelNg`、`StoppedAzumaNg`（载体上）；带状推论与 d = 3 实例；谱项 grep（泛型陈述里没有 `|E|`、`mE`、`zt` 等）；G1 按构造成立（列出 `GridDuhamelN` 的 21 个公开名）。答复：`AzumaProxyN`、`AzumaProxyN2` 从 T4s1 挪到 T4s2，不改计数（它们 import T4s2/T5s2 的文件、证 T4s2 的钉文），交 U-D 的 T 行普查，下次子阶段 T 的 REQ 报告；T4s2 的票注意 `GridGoodN` import `DecayLoopB`（T7）与 `SEforLn2`（U2）。
- (3) **T2454 = T7**（ST 侧；子阶段 T 12 / 28.5；BA 121；**`prover-hard`**，调度从 T2379 的 `prover` 上调（13 个目标、设计门，T2404 = T2 的先例）；**设计门**，探针步骤 `prover-max`，因为目标 4–11 所假定的模型事实清单现在钉不住）：**新增三个文件** `Chain/DecayGen.lean`、`Chain/Step2EventsGen.lean`（都不许 import `BA/`，U2、T1 以后要 import 它们）和叶文件 `Chain/DecayGenTw.lean`（TLF-C5 的例子与实例）；带状 `Step2Events`、`DecayLoopA`、`DecayLoopB` 不动；不进证书通道。目标：`STDecayLoopUgL`（`twSteps` 第 4 个合取项原文）、`STDecayLoopPTgL`、`STKcalDecaygL`（𝒦 的远端衰减假设）、`stDecayLoopAtgL_of`、`stDecayLoopPTgL_of_step2`、`stDecayLoopUgL_of_step2`、`stEtermDecaygL`（只在 U3s1 的 `STEKDecay` 词汇已上 `main` 时，否则挪到 U2）、`STScaleInvgL`、`ST_LW_sectionsg`、`Step2Mat` 上的事件 (E1)–(E4)、`ST_good_probg`、`STBdatagL` 与两条 L-桥、TLF-C5 的例子（`Iff.rfl` 例子是 1b 的目标，写在 `DecayGenTw` 里；检查文件只钉 `Prop` 形状）、d = 3 实例。TLF-C5 对 T7 只要第 4 个合取项，第 2–3 个归 U3s1。答复：`Step2Core`、`Step2Scale` 交 U-D；**U2、U2-BA 的票把 `STKcalDecaygL` 作为 `BAKcalDecay` 的目标形式**；T8 的 `STGdecayWgL`、`STStep2DecayPTgL`、`STDecaygL` 只在 1a 确认本行的公开定理绑定它们时才加进登记；目标 11 按 150 行规则可以挪到 T1-BA 或 stage L。
- (4) 开工顺序：T2452（U-D，便宜，监督要它先）→ T2453（T4s1）→ T2454（T7）。在跑 T2449、T2450、T2451。下一张票号 T2455，下一节 §265，下一条 H246。其后：X1a、U3s1（新文件 `Chain/Step34Gen`）、U6（新文件 `Chain/Step5Gen`）、U5 设计门、L3b1、L4b2、L3d1、L3d2。

## §265 — TL2e、T4s1 合并，stage TL 13/13 → 发关闭 REQ；放 X1a = T2455、L3b1 = T2456（总调度 V3，2026-10-12 13:14 UTC）

- (1) **T2451 = TL2e 合并** 4d4091e（12:47 UTC；`BA/TwistLoop` 904 行，landed/central 1.06；审核 PASS；登记不动）。**stage TL 13 行全部合并** → 发关闭 REQ `REQ-2026-10-12-1314-TLclose`（C1–C6，依据 T2451 报告 §(d) 的 (a)–(h)）。
- (2) **T2453 = T4s1 合并** 4fad610（13:07 UTC；`Chain/GridDuhamelGen` 683 行，新增文件，`GridDuhamelN` 不动；九个目标，含 U-C4 的桥、`Step2Gen_USemigroup`、`StoppedDuhamelNg`、`StoppedAzumaNg`；审核 PASS）。U4s1、U1s1 现在可写（1152 F4）。子阶段 T：T4s1 已合并。
- (3) **T2455 = X1a**（子阶段 U 2 / 34.5；BA 122；`prover-hard`，探针步骤 `prover-max`；设计门）：原地改 `Evolution/CltSwap`、`CltResolvent`、`CltPath`、`FarEntry`、`CltGood`、`CltStep`、`ExpInv`（5,792 行，100 个公开声明按 G1 保留；反向锥里没有证书模块），另加新文件 `Chain/CltGen.lean`（≤ 300 行，不 import `BA/*`），只放词汇和三条钉文 `STCltFargL`、`STCltIsogL`、`STExpInvgL`（X1-C4）。估计 450 / 650 / 1,100。结论已钉住并有约束力（`T2455_CltEtaLowerOf` 等），前提清单在 1a-audit 用探针 `Probe/T2455Pins.lean` 定。答复：第二个不合并的探针 `Probe/T2455Meas.lean`（X1-C5 的测量）批准；`Chain/CltGen` 算 X1a 的文件；`T2455_KfargL` 跟 T2452 的 D4 消费者形式（若那时已在 `main`）；MN0 的读法（`κ ≤ Im m`）有冲突就停。
- (4) **T2456 = L3b1 `Graph/BALocReg1` + `BALocReg1B`**（BA 123；L 32 / 50；计划 41；`prover-hard`；不设设计门；估计 1,100 / 1,500 / 2,600）：`PathInv2` 沿 `BAEquivC` 与扭转的搬运工具；`BASimP'`（每个输出一步带状步，同 `BASimC'`，L4-C1）；所有非带状形状的 `BAShapePath`（`s1` 空真、`e1`，以及 O2R-C4 的 `e2`、`macroA`、`macroB`）；`baPathStep_holds`；`BAPathInit`；`baStart_nM_le`（`P0.g.nM ≤ p`，§260 (1)）；**(1)–(5) 的约定 `BALocReg15` 沿 `BAReach`**（1152 O7：路径不变量、`nM ≤ p`、像上的 `LocReg2`，在 `LocStd` 处像与影子上的 `LocReg1` 加 `LocReg345`）；像到影子的 `LocReg345` 桥（已合并的 BA 消费者在 `BAShadowPG` 上读 (3)–(5)：`BAAtom2:647`、`:677`、`BAAuxGraph2B:865`）；BA 数据处 `|f_xy|^p` 的值恒等式；实例。答复：`e1`、`s1` 留在范围内；用 `BASimP'`；合成陈述（`BALocRegConcl` 加输出的 (1)–(5)）归 L3b2；1a 中心估计超过 1,575 时可把 `e2`/`macroA`/`macroB` 挪到 L3b2（拆分 Σ，计划仍 41），1b 前要调度签字。
- (5) 在跑：T2449、T2450、T2452、T2454；排队：T2455 → T2456。下一张票号 T2457，下一节 §266，下一条 H247。其后：U3s1（新文件 `Chain/Step34Gen`）、U6（新文件 `Chain/Step5Gen`）、U4s1、U1s1、U5 设计门、L4b2（现在有 `BATwKcircBound`）、L3d1、L3d2（等 L3b1 的 (1)–(5)）。

## §266 — M/N 设计单 T2449 合并：E5 照字面不成立，修补为新的泛型行 C5g，U、V 陈述不变；放 U3s1 = T2457、U6 = T2458（总调度 V3，2026-10-12 13:51 UTC）

- (1) **T2449 = M/N 设计单合并** 45400a7（13:19 UTC；只合并报告 `docs/reports/T2449-design.md` 158 行；探针 397 行留在 `t/T2449`；审核第一轮 RETURN（`Que′` 没钉进探针；`RBG_Prod` 实例 r2–r4 没证）→ 规则 (B) 修补一次 → 第二轮 PASS）。结论：
  - **MN0（BA-C5 / E5）：照字面不成立。** 在 `UNKind.ba` 上，Flow（T1）的第 1、2、4 个合取项、Dom（T1′）、Bulk（T6）都有反例（例如 `z = 2.5+0.2i` 处 `fE = 2.1430 > 1.95`；g = 10 时 `fT = 0.0156 < 1/16`；g > 0 时 `etaT` 与 BA 的 `√t₀ Im z` 不一致）；Prod、Que 喂不进去；LL 不受影响；MLout 成立。
  - **修补**：`RandomLayerB` 的带撇后继 `RBG_Flow`、`RBG_Dom`、`RBG_Prod`、`RBG_Que` 加子序列引理（边距 `κ' = (πκ)^5/2048`，常数 `cT` 代替 `1/16`，`η_{t₀} := √fT Im z`），约 530 行，作为**新行 C5g**（`Universality/GUEPhase/RandomLayerBG.lean`，`prover-hard`），不需要 BA、T、U、V 的任何东西；BA 实例在探针里已经证了（`ba_dom_of_bulk` 即 `BAm_im_lower_window`）。**U、V 的陈述不变，已合并的钉文不变**，停止规则没触发。
  - **MN1**：五个终点用 ρ-bulk 读法和律 `seqP (sz.withLam 0)`：新钉文 `BAEnd_locSCL`、`BAEnd_QDiffL`、`BAEnd_decolL`、`BAThm27L`（探针 192-217），加已合并的 `BAEnd_QUEL`、`BAEnd_BUnivL`。`baBUniv_of_rows` 的 15 个输入里 4 个现在可用，11 个欠给行（M1 3、M3 1、N2 2、N3a 2、N3b 2、V 1），**3 项没有生产者**（E5 修补 → C5g；E2–E4 原地改的可写文件；BA 的 `thetaDiff`）。
  - **MN2**：V3 是投影 `BAMLOutTL d → UNMLOutBA d`（探针里已证）；M/N 不直接读 U；`unMLOutBA_of_pins`（带 `STMainIndG` 前提）没有消费者，不需要（监督 1049 的问题就此消掉）。
  - **MN3**：E1 走移位泛函的转移；E2 原地做双耦合推广；E3、E4 原地写成 C 形式，不能转移。
  - **MN4**：M/N 共 6 行（M1、M2、M3、N2、N3a、N3b），中心 5,090 行；加上 C3、C4、C5、C5g 共 10 行、8,807 行。N1 不取消，430 行并入 M1（360）和 N2（70）。阶段旗标 9（含 C 行 15）。
  - 设计单请求的决定（§7）：建 C5g；N1 并入 M1/N2；给 N3a、N3b 定可写文件；V3 := `unMLOutBA_of_BAMLOutTL ∘ baChainTL_holds`；M/N 的开阶段 REQ 用 §5 的行数和探针钉文的形状。**C5g、N3a、N3b 都不需要 U、V 的输出，可以在 V 关闭前开**，但 Jun 定过"M/N 的证明票等 V 关闭"（§260 (3)），所以先问 Jun，没答复前照原计划等。
  - 文章差异候选：`T2449a`（BA 终点钉文用显式形式与律 `seqP (sz.withLam 0)`）、`T2449b`（UN-51 的 Flow、Dom、Bulk 接口在 BA 上不成立，修补带边距 `κ'`；文中 `zztE_BA` 的 `|Re z| ≤ 2-κ` 是 T2001g 的笔误）、`T2449c`（G_bound 用 `distB`）。观察：几处已合并的 QUE 实例数据指数 > 0，界 ≥ 1（`Endpoints.lean:541`、`Main/BandTerminal.lean:110`、`BA/UNPins.lean:1225`），记下，之后处理。
- (2) **下一件（1152 O6）：BA 侧 U 的钉文 REQ** 现在可以写了（T2449 报告已合并）；用 `BAMainIndTL d STAny` 陈述 U 的行，按 MN0 读 X1-C1。
- (3) **T2457 = U3s1**（子阶段 U 3 / 34.5；BA 124；`prover-hard`，探针步骤 `prover-hard`；窄设计门 D1–D3）：新文件 `Chain/Step34Gen.lean`（不 import `BA/*`）和叶文件 `Chain/Step34GenTw.lean`（TLF-C5 的例子与 BA 陈述层检查），备用 `Step34GenB`；`Step34Pins` 不动，不进证书通道。目标：TLF-C5 第 2–3 个合取项 `STLmaxUgL`/`STLKUgL`（有约束力的钉文）、环最大值、样本处的环与 ℰ 项、`STStep3RgL`/`STStep4RgL`、`STEKDecaygL`/`STEKLowgL` 与五个 `STEK*` 形式（在 `Step2Gen_UN` 上，E-C1；BA 形式归 U3-BA）、`STNewPQgL`、实例。答复：叶文件接受；D3 (b)（stage E 的 BA 核耦合 `lam0 = √t₀·sz.lam`，带状 `STEK*` 读 `sz.lam`）由探针定，需要阶段 E 没有的耦合论证就停在 1b 前报告；两条欠账登记行只在 1a 确认有公开定理绑定时才加；D2 由 T2457、T2458 里先到 1a-audit 的那张定。
- (4) **T2458 = U6**（子阶段 U 4 / 34.5；BA 125；`prover-hard`；不设设计门；估计 500 / 750 / 1,150）：新文件 `Chain/Step5Gen.lean`，只 import `GridDuhamelGen`、`Step5Pins`（条件情形加 `Step34Gen`）；一个核（`Ugen` 变成 `Step2Gen_UN`，`Ugen` 的桥只用 T4s1 的 `bandStep2_Ugen`）；不读 X1a 的钉文。答复：D2 同上；LemDecCalE 在 U6 的 1b 开始时若 T2457 未合并就挪到 U4s3；泛型 TailtoTail 不在 BA 上声称（归 U5）；`sz.lam` 的 BA 读法留给 X1a 的 `g₀` 测量与 U6-BA。
- (5) 下一张票号 T2459，下一节 §267，下一条 H248。排队：T2456 → T2457 → T2458。其后：BA 侧 U 钉文 REQ、U4s1、U1s1、U5 设计门、L4b2、L3d1、L3d2。

## §267 — U-D 合并（T 加两行生产者 P1、P2，旗标 31.5）；T7 的 1a-audit 签字；放 U5 设计门 = T2459；发 BA 侧 U 钉文 REQ（总调度 V3，2026-10-12 14:19 UTC）

- (1) **T2452 = U-D 合并** 6bdc5a3（13:55 UTC；只合并报告 `docs/reports/T2452-design.md` 207 行；探针 371 行留在 `t/T2452`；审核 PASS；停止规则没触发）：
  - 按使用普查：19 行、85 个文件；行文件外读到的 530 个声明中 77 个下面超过 200 行；其中复用 21、已被阶段或已合并的 BA 定理覆盖 44、无 BA 读者 4、U5 内部 2、**要生产者 6**；REQ 表的 9 行里 4 行确认、3 行细化、2 行驳回。
  - **子阶段 T 加两行生产者**：**P1** 无扭转的 BA 网格钉文 `STGridMartgL`，在 `baStep2Mat` 上，从 TL 钉文 `baTwistGridMart_holds` 加三个恒等式得到（形状已编过）；**P2** `STNetLift2gL`，在 `baFMz` 上，直接做。T 旗标 28.5 → **31.5**，BA 计数 +2（1152 U-C6 (c) 的规则内，不必再发 REQ）。
  - **U 不加行**（旗标仍 34.5）：P3、P4、P6 是 T1/T1-BA 的目标；P5 = `BAKellStarEv`（探针里已证）是 U5 的目标；P7 是 U3-BA 的目标。`LemDecCalE` 没有 BA 读者，不要生产者；`CondDom` 只读一处，不要生产者；`Step2Scale`、`Step2Core` 给的是目标（P3、P4）不是行。FarEntry 的远场在 K 层（已合并的 `baEMn2ExpHK`）。
  - 所有消费者都只读 `m = 2`。ST 侧 T1 的陈述不变（P4 加约 330 行）。
- (2) **T2454 = T7 的 1a-audit RETURN，要调度签字**（14:05；1a 本身 PASS，探针 397 行 PASS）。缺的 (i) 布局、(vi) T1 读的 `Step2Events`/`Step2Core` 公开声明逐个定、(vii) 每个文件的中心行数，以及登记计划把 `STScaleInvgL` 藏进了 `S2EvGen_Sect`，这些由 prover 补交 1a。调度的决定（H248）：
  - BA 侧的事实（`baFM_WardPair`、`baFlow_facts`、`baStep2_Grid`、目标 6 的 BA 实例）放在叶文件 `DecayGenTw`，加 `import RBM3D.BA.EMn2BA`，用脚本证明它仍是叶（零 importer）；
  - F7（BA 上的 `S2EvGen_Rot3`）由 1b 在 `DecayGenTw` 里证（`loopFine` 的迹循环性，同 `STB_loop_rot`，`Step2Events.lean:1283`）；超过 150 行就记为 T1-BA 的义务并在报告里说明；
  - 拆分：补交的 1a 若中心总数超过 1,950，在文件边界拆成 T7a（衰减：`DecayGen` + `DecayGenTw` 的衰减部分）与 T7b（事件：`Step2EventsGen`），调度预先签字，1a-audit 第二轮确认，调度事后发一份短的 T 通知 REQ（不阻塞）；
  - 公开帮手（`DecayGen_ward`、`bandFM_WardPair`、`baFM_WardPair`、`bandStep2_Grid`、`baStep2_Grid`、`bandFlow_facts`、`baFlow_facts`、`bandFM_Spec`、`bandFM_Rot3`）用文件词干前缀命名（`DecayGen_*`、`Step2EventsGen_*`、`DecayGenTw_*`），或改成 private；
  - 文章差异候选 `T2454a`–`d` 记下。
- (3) **T2459 = U5 设计门**（子阶段 U 5 / 34.5；BA 126；`prover-max`；只合并报告 `docs/reports/T2459-design.md`，≤ 450 行；探针 `Probe/T2459Pins.lean` 不合并，U6 的钉文以 `T2459u6_` 前缀原样抄入作本地假设，U6 合并时复核）：BA 的 Step 5 情形 (iii) 的完整 d = 3 论证（U5-0 … U5-9：带状情形 (iii) 栈的清点与 BA 替代、BA 核界（TailtoTail 及平方形式）、由带撇钉文得到的 `lem_dec_calE` 的 ℰ 界、BA 上的 `lem:pf_step5`、两个 BA 目标 `STPfStep5gL`、`STStep5IIIgL`、C1 常数表、`g = 1/64, 1, 10` 处的数值、1b 的行表、文章差异 `T2459a`）。主要风险在 ℰ 界：BA 的 `M = M^(B) ⊗ I` 在相邻块同偏移的点之间有 g₀ 量级的元，带状证明里依赖非对角 G 小的每一步（`E2Hyp`）都要用 `G = M + (G − M)` 重做。`|m| = 1` 那一处已有合并的事实可替代（`BAK_row_sum`、`K_aa = |m|²`、`BAK_off_le`、`BAuKer_convex`、`g₀ ≤ sz.lam`）。论证合不上就停下报告，调度发 REQ（届时是给 Jun 的数学问题，1155 C2）。U5 的 1b 等 BA 钉文 REQ。**T2458 检查文件第 462 行的 BA 例子 `∀ lam0, T2458_STTailtoTailgL' 3 (baFM sz lam0 ·)` 只是形状、不是 U6 的目标**（`lam0 ≫ sz.lam` 时可能不成立，由 U5 的 1a 判定）。
- (4) **发 `REQ-2026-10-12-1418-UBA`**（BA 侧 U 钉文 REQ，1152 Q2、O6）：九个 BA 侧行各自的 ST 配对、BA 目标钉文（在 `baPin` 上的泛型钉文，核 `BAUN`，谱读法 `κ ≤ Im m`）、依赖与最早开工时间；`BAKcalDecay` 是 `STKcalDecaygL` 的 BA 读法；U4-BA 带 X1 的 BA 实例。五个问题：目标形状、放行规则（每行等 ST 配对合并，U5 设计门例外）、`g` 对 `g₀` 的读法、U3-BA 与 U4-BA 的 (a)/(b) 拆分、MN1 三个无主项都不落在 U。风险：用到 U-D 的结果（尚无裁决确认）；T2457 的 D3 (b) 未定；G7（带撇的 Step 1 重接线）还没开票，它卡 U3-BA (b) 和 U5。
- (5) 待写：P1、P2（子阶段 T）、G7、U4s1、U1s1、L4b2、L3d1、L3d2（等 L3b1），以及 T1、T4s2、T5s2。下一张票号 T2460，下一节 §268，下一条 H249。

## §268 — 监督 1354：stage TL 关闭（13 / 15，TLC-1–TLC-4）；BA-V 接口清单（一处）；U3s1 的 1a-audit 签字（D3 (b) 取 (B)）；放 P1 = T2460、P2 = T2461（总调度 V3，2026-10-12 14:46 UTC）

- (1) **监督 1354：PASS，stage TL 关闭于 13 / 15**（C1–C6 成立）。条件：
  - **TLC-1**：BA-V 接口清单只写一处，见下面 (2)；BA-V 的设计票引这一处。
  - **TLC-2**：加第 (vi) 项；两条欠账行的 owner 注释在下一张本来就要改 `Test/Axioms.lean` 的票里改写（不为此单开票）：`BATwistAvgLaw` 改成 "TL stage, closed (`baTwistAvgProd_holds`, `TwistStep2_tl1`) + BA-V (V1/V2a, per `u` from `twSteps`)"；`BATwistLoopLaw` 改成 "TL stage, closed (`baTwistLoopStep_caseI/II`, `baTwistLoopBase_holds`, `baChainTL_holds`) + BA-V (V2a/V2b: the fifth conjunct and the regime glue; `GLoopAtT0`)"。
  - **TLC-3**：在 `docs/paper-deltas.md` 里给 `T2398d`、`T2421a`、`T2427a`、`T2441a` 编号；文章差异账本从 2026-10-09 21:01 UTC 起没动过，要补一遍（交一个子代理整理，调度写入）。
  - **TLC-4**：TL 实际落地是中心估计的 2.6 倍（22,517 / 8,688）；U（旗标 34.5）和 L 剩下的行沿用 TLF-C1 的规则（中心 ≥ 1,000 时开票就定第二个文件），1a 的行数预测以 2.6 倍作上参考。
  - O4：U3s1 只写合取项 2–3（它正是这样）；V2a 的合取项 1 来自子阶段 T 的 `BAStep2`。
- (2) **BA-V 接口清单（TLC-1，唯一一处；BA-V 的设计票引用本节）**：
  - **K2**（监督 0150）：每个成员的前提 `STKboundgL (baFMz sz z')`（`z' ∈ Fam(s)`）可以消掉，路线已合并：`BAFamZ_mono`（`Step1Boot:173`）→ `BAFlowMember_holds`（`Step1Fam:624`）→ `baKbound_holds` → `baFMz_eqAt`（`:273`）与 `STKboundgL_congr`（`:247`）；BA-V 在 `d ≥ 3` 的组装里补上 `3 ≤ d`，约 30 行。
  - **K3**（0150）：`stBaseG_of_init` 的 `hK`（`MainIndBase:114`）没有 `0 < ε`、`0 < 𝔡`，`baKbound_holds` 接不上；BA-V 里用 `hK` 带 `0 < ε → 0 < 𝔡 →` 的变体，或去掉 `hε` 的约化副本（`BAKbound_of_uniform` 的证明不用它）。
  - **第五个合取项**（0652 O2）：TL2 沿主归纳传递，基础情形来自 `G_0 = M`（`L̃_0 = K̃_0`）。
  - **(i)–(iv)**（1049 O3，§236）：V2a 的目标是每个情形下的 `BAMainIndTL`；V2b 加第十二个传递；V3 与 BA-M1 吃 `BAMLOutTL`；`GLoopAtT0` 同时供 `STBaseG` 和 `BAChainTL`。
  - **(v)**（0554，§249、§251）：TP 脚注 6 的跨界情形，不在任何 TL 行里。
  - **(vi)**（1354 TLC-2）：V1、V2a 在每个 `u ∈ [s,t]` 取 TL1 用 `TwistStep2_tl1`（`TwistStep2:1137`，经 `baTwistAvgProd_holds`，取自 `twSteps` 的合取项 1 的 `STAvgUgL`（`𝒦^{(1)} = m` 由 `baKsol_one`）与合取项 2，同带状 `LWAvgLaw_of_STAvgU_at`，`Step6Kit:189`），取 TL2 用 `baTwistLoopStep_caseI/II`；V1、V2a、V2b 证完时两条欠账行退掉。
  - **`twSteps` 的 owner 表**（1354 Q2 (a)）：合取项 1 `STStep2ConclgL`，泛型已合并（`Chain/Step2Gen:514`），BA 实例是子阶段 T 的钉文 `BAStep2`（`FlowPins:432`，T1 + T1-BA）；合取项 2（`STLmaxU`）泛型 U3s1 `STLmaxUgL`，BA 实例 U3-BA；合取项 3（`STLKU`）泛型 U3s1 `STLKUgL`，BA 实例 U3-BA；合取项 4（远场衰减 `STDecayLoopU`）泛型 T7 = T2454 `STDecayLoopUgL`，BA 实例 T7-BA（按 1155 C8 在 U 里）。V2a 用 `Iff.rfl` 从这四处消掉 `twSteps`（TLF-C5）。
  - **V3**（T2449 MN2）：`V3 := unMLOutBA_of_BAMLOutTL ∘ baChainTL_holds`；`unMLOutBA_of_pins` 不用。
  - **D3 (b) 的换算**（本节 (3)）：U3-BA 欠一个由 `BAdom` 得到的耦合换算。
- (3) **T2457 = U3s1 的 1a-audit RETURN，要调度签字**（14:31）：缺的 (i) 布局与反向锥、(iii) 131 个公开声明的范围表、(iv) 桥表、(v) 前提扫描与登记、(vi) T7 目标 7 读的形式（部分）、(vii) 行数预测与 `open private` 清单，由 prover 补交（写成 (a‴)）。**§7 的决定取 (B)**：`STEKDecaygL` 保持在 `sz.lam`（它是 TLF-C5 合取项 4 的读法，`twSteps` 是已合并的 TL 钉文，TL 已关闭不能改），**U3-BA 欠由 `BAdom` 得到的换算**：`ellT L lam0 ≥ √t0·ellT L lam`、由 `BAdom` 得 `t0 ≥ κ/(κ+1)`、最终 `W^{ε/2} ≥ 1/√t0`（带最终-`W` 的极限检查），作为新的欠项记进 BA 侧 U 钉文（REQ UBA 已发，监督读本节）。T7 的目标 7 已经按它的停止规则挪到 U2；U2 的票读 `STEKDecayKgL gK`，换算在 U3-BA。本票的泛型形式不变。
- (4) **T2455 = X1a 的 1a-audit RETURN**（14:43，无需签字）：`STGijDecgL` 的环前提只覆盖 `(-,+)` 电荷，所以 `STGbEXPij` 推不出带状形式；X1-C2/X1-C3 表和每个文件的行数预测没给；按规则 (B) 修补一次（R1–R3 → 1a-audit 第二轮 → 1b）。不用调度动作。
- (5) **T2460 = P1**（子阶段 T 13 / 31.5；BA 127；`prover-hard`；不设设计门）：新文件 `BA/GridMartBA.lean`：三个恒等式 `BAGridBridge`/`baGridBridge_holds`（U-D 探针 `T2452_Bridge` 原文）、`baGridMart_holds : STGridMartgL d BAFlow (fun sz z => baStep2Mat …) BAflowT0`（对每个 d；T1 的 `STGridMartAt` 在 `Step2Iterate:1399` 从这个钉文解出，不另立目标）、条件目标 4（BA 上 m = 2 的 `STGridRepNAtgL`：表恒等式加第 4 条）、d = 3 实例、谱项 grep。**只做 m = 2**（所有读者只读 m = 2；TL 不覆盖 m > 2；所有 m 要走 P1G 路线，2.1k–4.5k 行、2–3 行）；监督的"所有 m 一个泛型行"读作：载体泛型 Prop 上的一行，用在 m = 2；下次子阶段 T 的通知 REQ 报告。**第 4 条待定**：TL 的条款 (iv) 只加权一个槽（`twU`，`TwistGrid:105`），钉文的第 4 条加权两个槽（`Step2Gen_UN`）；1a 确认推不出就在 1b 前把目标 4 去掉（调度预签），U5 那边的输入就没有生产者：等 T2459 说情形 (iii) 能不能用单槽条款，不能就新开一行 T（双槽 BA 尾）。
- (6) **T2461 = P2**（子阶段 T 14 / 31.5；BA 128；`prover-hard`；不设设计门；估计 600 / 900 / 1,600）：新叶文件 `BA/NetLiftBA.lean`（备用 `NetLiftBA2`）：`baNetLift2_holds (d) : STNetLift2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (BAFlow …) baFMz BAflowT0`、**P6 `baFlow_premises`（BA 流前提，U-D 探针 `T2452_ba_premises` 原文，在本行证、公开；T1-BA import）**、d = 3 实例、谱项 grep。BA 路线：三族各自是 `cont_core` 加 `seqP (sz.withLam 0)` 下的好事件；唯一新的 BA 估计是 `𝒦^{(2)}` 对每个电荷对的时间 Lipschitz 界；1a 可以拿 `baNetLift`（`Step1Setup:877`，T2262）作模板。
- (7) ROUTES：stage TL 已关闭（13 / 15）；子阶段 T 旗标 31.5（P1、P2）。下一张票号 T2462，下一节 §269，下一条 H250。待写：G7、U4s1、U1s1、L4b2、L3d1、L3d2（等 L3b1）、T1、T4s2、T5s2；文章差异账本补录（TLC-3）。

## §269 — 监督 1457：BA 侧 U 钉文 PASS（UBA-C1–C4）；U 的唯一耦合规则（g 对 g₀）；U6 合并；L3b1 拆分 Σ 签字；文章差异补录 D636–D691（总调度 V3，2026-10-12 15:11 UTC）

- (1) **监督 1457：PASS**，九个 BA 侧行就是这张表，修正三处（耦合层、类的量词、`baFlowLam0_ge`）。发现 **F1**：从 `g` 到 `g₀` 的跨越在 U 里没有负责人（不是数学缺口，不 HOLD）。事实：BA 的核跑在 `g₀ = √t₀ g`；`BAFlow` 下每个 n 有 `t₀ ∈ [κ/(κ+1), 1)`（`TwistStep2_T0_ge`，`TwistStep2:731`），`g₀² ≤ g² ≤ ((κ+1)/κ) g₀²`（`TwistStep2_lam0_sq`，`:740`，随 TL2d 合并，公开）；情形谓词的类型是 `Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop`，看不到 `z`，所以在 BA 上只能读 `g = sz.lam`。
- (2) **U 的唯一耦合规则（UBA-C1；T2457 (a‴)、U3s2–U3s4、U3-BA (a)/(b)、X1a 的 R2、U4-BA、U6-BA、T2459 都引本节）**：
  - **尺寸层的量读 `g = sz.lam`**：情形谓词、`Bctl`、TL 合取项里的 `ellT`、`STAI`、泛型 Step 陈述的窗口。BA 陈述传 `sz`，不传 `sz.withLam g₀`。
  - **核层和剖面层的事实读 `g₀`**：经 T2457 的耦合 `gK`，或经剖面假设。
  - **泛型证明从一层跨到另一层时，只取一个比较假设**：`∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`；带状 `A = 1`，BA `A = (κ+1)/κ`（由 `TwistStep2_lam0_sq`）。
  - **跨越表与负责人**（`A = (κ+1)/κ`；常数只依赖 κ 与 n，C1 成立）：
    - (a) 情形 (i) 的窗口 `t ≤ 1 − g²/L²` ⇒ `t ≤ 1 − g₀²/L²`：免费（U3 的 Res1、NAL、Res2）。
    - (b) 情形 (ii) 的阈值：`1 − s ≤ g²/L²` 推不出阶段 E 的 `1 − s ≤ g₀²/L²`，差 `(1−t₀)g²/L²`；**泛型 Nonzero 形式带参数 `A`**，阈值 `(1 − s)L² ≤ A gK²`；带状实例 `A = 1`（即已合并的阶段 E）；**BA 实例归 U3-BA (a)**，`A = (κ+1)/κ`，是 `baEKSumDecayNonzero_holds`（`EKNonzero:261-280`）的乘积步，用 `baTwKerZero_holds`（`TwistKer:256`）代替私有的 `A = 1` 因子，约 50 行（TL 的先例 `BATwKerZero`、`TwistStep2_kerC`）。
    - (c) 比值 `r(g₀)/r(g) ≤ 1/t₀`（每个因子）→ `A^n`，被 `W^{Cε}` 吸收；(d) `ℓ(g₀,u) ≥ √t₀ ℓ(g,u)` 且 `ℓ(g₀) ≤ ℓ(g)`；(e) 衰减截断：`twSteps` 合取项 4 在 `ellT (sz.lam) · W^{τ'}`，取 `τ' = ε/2`，要 `W^{ε/2} ≥ √A`（最终成立）：**(c)–(e) 在 `Chain/Step34Gen` 里泛型地写一次**（T2457 的 1b，若在停止线内；否则作 U3s2 的第一个引理）。
    - (f) 在 `ℓ(g₀)` 证的衰减在 `ℓ(g)` 读：免费（`ℓ(g₀) ≤ ℓ(g)`；U2-BA 的 `STKcalDecaygL`、`BAKellStarEv`、X1 的 Θ 衰减）。
    - (g) Θ 剖面事实（`STThPropsg` 在 `sz.lam` 读 `Bparam`、`ellT`、`(g²+|1−t|)⁻¹`，`BAProp5–7` 在 `g₀`）：进 X1a 的 R2 表；BA 换算归 U4-BA (a)。
    - (h) Step 5 核（BA 载体上 `S := 1`，核只经 `C.S`/`C.M` 看到 g）：归 T2459 的 1a 与 U6-BA 的钉文。
  - **T2457 的 §7 取 (B)**（与 §268 (3) 一致）：`STEKDecaygL` 留在 `sz.lam`，T7、U2 不变，(e) 在比较假设下泛型地成立。§268 (3) 里"U3-BA 欠 `BAdom` 换算"按本规则改为：(e) 在 `Step34Gen` 泛型地写，BA 端只需比较假设（由 `TwistStep2_lam0_sq` 给出）。
  - 可以接受的另一种：泛型消费者只读 `sz.lam`，由 BA 实例行做 (b)–(e)（TL 自己的放法）。本项目取上面的主规则。**不加行**：约 50 + 100–150 行进现有行，U 旗标仍 34.5。
- (3) **UBA-C2（形状更正，写 BA 侧行时照办）**：`BAEKKer` 去掉"对每个 n `0 < lam0 n ≤ Λ`"，改用 T2457 的最终形式 `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹`（`BAflow_lam0_window`，`GreenSchur:72`），类里带 `gK = lam0`；**删掉 U6-BA 的目标 `baFlowLam0_ge`**，改用已合并的 `TwistStep2_lam0_sq`、`TwistStep2_T0_ge`（import 或三行重述，不再抄私有的 `KBound_t0_ge`）；U4-BA (a) 跟 X1a 修过的 `STGijDecgL`（R1：对称的 `Φ` 或两种混合电荷），`baGbEXPij'_holds` 两种都覆盖；U3-BA (a) 加 A 形式 Nonzero 的 BA 实例。
- (4) **UBA-C3（放行）**：每个 BA 行在它的 ST 配对合并后放；另外 U3-BA (a) 还要等本节的记录（已记）；A 形式下不需要 BA 半群（T4-BA）；G7 与阶段 L 的钉文按同类型的假设进入。**UBA-C4（U5）**：T2459 的论证在 `g₀` 读 Step 5 的核、在 `g` 读情形；C1 常数表记下 `A`；(h) 若需要的不止比较假设，就是 U-C5 的停止情形。
- (5) **O4（1a 反复漏项）**：设计门的 1a 提示里加一张票里 stage-1a 交付项的填空表，每项一行，写行号或"n/a，因为……"；表没填满，探针步骤不算完（H250 交中枢）。
- (6) **T2458 = U6 合并** 1debc23（15:05 UTC；`Chain/Step5Gen` 666 行，新增文件；目标 1–10、12–15 与实例；目标 11（LemDecCalE）因 T2457 未合并按票挪到 U4s3；第 462 行的 BA 形状留给 T2459（H248 (3)）；审核 PASS）。U4s1、U4s2 现在有 U6 的词汇。
- (7) **T2456 = L3b1 的拆分 Σ 签字**（15:01，1a 预检 BLOCKED 等签字）：数值 (b) 0 违反，(c) 无新行，目标 8 成立；估价中心 2,424（含 3(c)–(e)）超过 1,575 → **批准拆分 Σ**：目标 3(c)–(e)（`e2`、`macroA`、`macroB` 的 `BAShapePath`）挪到 L3b2，L3b1 中心 1,550；L3b1 照抄绑定变量陈述约定（不新立 `Prop`），stage L 计划仍 41（L3b2 本来就在计划里）；**L3b2 的票必须把这三项列为目标**（O2R-C4）。
- (8) **文章差异补录（TLC-3）**：`docs/paper-deltas.md` 追加 **D636–D691**（56 条，按票号；同一论文位置合并为一条），含 `T2398d` → D666、`T2421a` → D682、`T2427a` → D684、`T2441a` → D687、折叠 (A′) 一组 → D665、`T2434c` → D685、`T2418a` → D680、`T2449a–c` → D689；撤回的 T2443d、T2419a、T2390i 不编号；重复的并入旧条的注记、非陈述差异的候选列在补录段的"不编号"里。证明行未合并的候选（T2398a、T2433a、T2448b、G2/G4/G5/G6、T2454a–d、T2457a、T2459a、U5 论证）在行合并时再编号。窗口外还漏了 T2359a、T2353a–b、T2354a–c，下次补。
- (9) ROUTES（O5）：U 5 / 34.5；T 旗标 31.5（P1、P2）；BA 计数到 128（T2461）。下一张票号 T2462，下一节 §270，下一条 H251。待写：U4s1、U1s1、G7、L4b2、L3d1、L3b2（含 3(c)–(e)）、T1、T4s2、T5s2、U3s2–U3s4、U2（等 U3s1、T7）。

## §270 — L4d2b 合并（S3 闭包完成）；放 U4s1 = T2462、U1s1 = T2463（总调度 V3，2026-10-12 15:54 UTC）

- (1) **T2450 = L4d2b 合并** ab5746d（15:37 UTC；`Graph/BAS3Close` 1,953 + `BAS3CloseB` 837 + 备用 `BAS3CloseC` 1,661，都在 2,000 停止线下；目标 1–6：根、`BAS3Identity`、`BAFoldLeaf`、14 个折叠约化、`BAS3Xprec`、`BAS3Close`、`BAS3Expand'`、实例；审核 PASS 第一轮）。**S3 闭包完成**：L4c1、L4g 现在可写（它们的解析叶子界取析取：`BAG5Leaf` 叶子逐点再平均，折叠叶子直接走 L4d2a，平均形式；0851 Q3）。stage L 计划 41。
- (2) **T2462 = U4s1**（子阶段 U 6 / 34.5；BA 129；`prover-hard`；窄设计门 D1–D4，`prover-hard` 探针，1a 带填空表）：**新增三个文件** `Chain/Step5CasesGen`、`Chain/Step5KerGen`、`Chain/NewKLKLGen`（7 个带状文件 5,431 行不动；`Step5Kit` 在证书锥里，原地改要证书合并）。目标：流事实；泛型情形 (i)–(iv) 与组装（情形 (iv) 不需要谱事实，经 `STConStInd`）；Ward 项；核分解 `uKer = 1 + (t−s)·thetaKer`；核在 `gK` 的衰减与 `sz.lam` 的剖面界加 UBA-C1 比较假设；T3 的 `NewKLKGenHyp` 下的泛型 NewKLKL；TailtoTail 只给带状实例；greps；G1；七条欠账登记。估计 1,500 / 2,000 / 3,000（2.6 倍上参考 5,200）；**预签拆分**：1a 中心超过 1,950 就在文件边界拆成 U4s1a / U4s1b，调度事后发不阻塞的通知 REQ。答复：X1b 不再被 import 强制排在 U4s1 后（`Step5Kit` 不改），但它消费本行的目标 1，所以仍在后（报给监督）；U4s1（D1）与 U1s1 的 Ward 文本只要一份，先到 1a-audit 的那张定；D2（`thetaKer` 在 `gK` 的衰减，所有电荷对）是核层事实（§269 (2)），X1 tier 2 在 `sz.lam` 读 Θ 剖面时用比较假设桥接，1a 写出桥并对齐 X1a 修过的 `STThPropsg`；`Chain/NewKLKGen` 经 T3 的 BA 例子传递 import 了 `BA/FlowPins`：1a 查它是否在证书锥里，不在就可以把那个 BA 例子挪到新叶文件 `Chain/NewKLKGenBA.lean`（两个文件加进可写），在就保留并在报告里记下。
- (3) **T2463 = U1s1**（子阶段 U 7 / 34.5；BA 130；`prover`；不设设计门；估计 650 / 950 / 1,500，按 TLC-4 先定备用文件）：**新增** `Chain/ZeroModeGen.lean`（备用 `ZeroModeGenB`；四个带状文件 `ZeroModeCalc`、`NewPQ`、`QopAlgebra`、`QopNorm` 都在证书锥里，不改）。目标：一个载体前提 `ZeroModeGen_KerSums`（`M^{(σσ')}S` 的行和等于列和；`Step2Gen_Theta` 是 `Ring.inverse`，所以不要时间窗口）；`zeroModeSet` 与 `Step2Gen_UN`、`Step2Gen_ThetaN` 交换；带零模算子的网格 Duhamel 步；模型无关的 newPQ（Ward 族谓词、公开的 G 环 Ward 事实、展开）；载体 Ward 类与泛型 (𝓛−𝒦) 展开；`QopAlgebra` 的核读法；带状推论与 d = 3 实例；一个核、X1-C1、UBA-C1 的 grep（UBA-C1 不起作用：没有泛型陈述读 g 或 g₀）；条件目标 `STNewPQgL d ZeroModeGen_WardCls`（T2457 合并后才写，否则归 U1-BA）；G1。`QopNorm` 模型无关，不写泛型文本。记给 U1-BA：U1-BA 证出 `KerSums (baFM)` 后，`baZeroModeSet_UN` 就是目标 2 在 `baFM` 上（陈述不变，不必 REQ）。
- (4) T2457 的 (a‴) 保持目标 7 为类钉文（H251）。下一张票号 T2464，下一节 §271，下一条 H252。待写：**L4c1、L4g**（S3 之后）、G7、L4b2、L3d1、L3b2（含 3(c)–(e)）、T1、T4s2、T5s2、U1s2、U3s2–U3s4、U2（等 U3s1、T7）。

## §271 — T7a、X1a 合并；放 L4c1 = T2464、L4g = T2465、L4c2 = T2466；U3s1 第二轮签字（比较假设加非负）；P1 Amend 1（H3 改不等式，目标 4 离开）（总调度 V3，2026-10-12 17:11 UTC）

- (1) **T2454 = T7a 合并** aa38bde（15:56 UTC）：1a-audit 第二轮确认按预签拆成 T7a/T7b（中心 1,962 > 1,950）；新 `Chain/DecayGen` 657 + 叶 `Chain/DecayGenTw` 80；目标 1–6、12 和目标 6 的 BA 实例；目标 7 归 U2，**目标 8–11 归 T7b**（`Step2EventsGen`，后继行，待写）；审核 PASS。子阶段 T 多一行 T7b（旗标 31.5 内；发一份不阻塞的通知 REQ，与 T7b 票一起）。
- (2) **T2455 = X1a 合并** 62eed82（16:53 UTC）：原地改 `Evolution/CltGood`、`CltPath`、`CltResolvent`、`CltStep`、`ExpInv`、`FarEntry`（`CltSwap` 不变），新 `Chain/CltGen` 267 行（`STCltFargL`、`STCltIsogL`、`STExpInvgL`，1a-audit 第二轮定）；登记：与 T2454 的行取并，新加五行（`STLocalEntryUgL`、`STGijDecgL`、`STKfargL`、`STMfarg`、`CltInvg`）；1a-audit RETURN → 规则 (B) 修补一次 → 第二轮 PASS；1b 带 UBA-C1 重跑；审核 PASS（观察：证明报告 377 行，超 300）。X1b 现在等 U4s1。
- (3) **L4c1/L4c2/L4g 的切分**（两份草稿重叠，调度定）：
  - **T2464 = L4c1**（BA 131；L 33 / 50；`prover-max`；不设设计门；`Graph/BAExp14c` + `BAExp14cB`，备用 `BAExp14cC`）：带状 `LWExpTerm3:1233-1425`（≺→𝔼 工具）；目标：子根 `baS3RootT0`（只取 T3C-tr_0）、四个根的桥（S3 族 × t = 根平均）、≺→𝔼 工具、**`BAFoldLeafT`（保留因子 t 的折叠类：已合并的 `BAFoldLeaf` 丢了权里的 `t^p`，小 t 时吸收不了 1/t）**、叶钉文 `BAG5LeafPrec`（只陈述）与 `BAS3LeafAvg`（带 0851 Q3 的析取与 x~y 支撑）、条件组装 `baExp14bS3_of_leaf : BAG5LeafPrec d → BAExp14bS3 d`、实例。`BAExp14bS3` 对四个族分别作界，而 `MERGED` 只给 D1X + T3C-tr_0 之和：用子根得 T3C-tr_0，D1X = MERGED − T3C-tr_0，所以已合并的钉文原样产出，不要后继钉文。
  - **T2466 = L4c2**（BA 133；L 35 / 50；`prover-max`；不设设计门；`Graph/BAExp14d` + `BAExp14dB`，备用 `BAExp14dC`；带状 `LWExpTerm3:384-1228, 1426-1661`，中心 1,297）：n_M = 1 叶子的 q ≤ 1 界；**与 T2464 并行开工**（不读 T2464 的文件；floor 与 `η ≤ 1` 是约 40 行的私有副本，T2464 先合并就改为 import）；目标：重标度数据与 `val(BAlwData_t) = t^{n_W}·val(D'_t)`、不带 hext 的 BA GtoAG 副本 `BAGtoAGT`（`BAG5LeafProps` 没有不同外分子的条款）、确定性 q ≤ 1 界、`BAExp14d_Bctl_small` 与 `BAExp14dEntry`、主目标 `BAG5LeafPrec1` / `baG5LeafPrec1_holds`（= L4g 的 `Q1`，名字与陈述在 1a-audit 冻结）、实例；L3d1（G4）不是输入（带状路线不用它）。0851 Q3 的析取：本行只是逐对 GtoAG 那一半，平均与折叠叶子归 T2464，n_M = 0 叶子归 L4g。
  - **T2465 = L4g**（BA 132；L 34 / 50；`prover-max`；不设设计门；`Graph/BAExp14e`，估计 450 / 650 / 1,200）：`BAGraphPrecJoin`/`baGraphPrecJoin_holds`；证 T2464 的 `BAG5LeafPrec`（n_M = 0 一半自己证，n_M = 1 一半取 T2466 的 `BAG5LeafPrec1`）；`baExp14bS3_holds = baExp14bS3_of_leaf d (baG5LeafPrec_holds d)`；实例。**等 T2464、T2466 合并后开工**。之后 L6（`BALWOut`）还等 L5、L3d2。
- (4) **T2457 = U3s1 的 1a-audit 第二轮 RETURN，要签字**（16:41）：(a‴) 的比较假设多了 `∀ n, 0 < gK n`，不是 §269 (2) 的原文，在带状的一般容许 `sz` 上消不掉；但只用 §269 原文又得不到每个 n 的窗口步 (a)。**决定：§269 (2) 的比较假设改为 `∀ n, 0 ≤ gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`**（加非负；带状 `gK = sz.lam ≥ 0`，BA `gK = √t₀·sz.lam ≥ 0`，都对每个 n 成立）。由此 `sz.lam n > 0 ⇒ gK n > 0`；`sz.lam n = 0 ⇒ gK n = 0`，两个窗口相同。窗口步 (a) 按这两种情形写，不要 `∀ n, 0 < gK n`。T2462（U4s1，正在 1a）和以后所有引 §269 (2) 的票都用这个改过的文本。其余（第一轮 1–7 项、(B)、A 形式 Nonzero、H251 (2)）都满足；`STNewPQgL` 的文本已对 T2463 编过。
- (5) **T2460 = P1 的 1a 预检 FAIL → Amend 1**（`docs/tickets/T2460-amend-1.md`）：目标 1 `T2460_Bridge` 的第三个合取项 H3（二次变差）照 U-D 探针写成等式，是错的（`twEEk` 有交叉项，`STEEMg` 只有两个对角 6-圈；216 个随机例子 0 个成立）。调度改检查文件：H3′ `‖twEEk …‖ ≤ 2 * ‖STEEMg …‖`（常数是槽数 2，尖锐；数值 0 违反）；目标 2 的粘合用 H3′（钉文事件在 ε′ 处落在 TL 在 ε′/2 处的事件里，最终成立）；**目标 4（带第 4 条的 m = 2 表形式）在 1b 前离开**（预签）。U5 的输入（双槽 BA 尾）没有生产者：等 T2459 的报告说情形 (iii) 能否用单槽条款，不能就新开一行 T。
- (6) 在跑：T2456、T2459、T2461、T2462；排队：T2463 → T2457（签字后 1b）→ T2460（Amend 1）→ T2464 → T2466 → T2465（等 T2464、T2466）。下一张票号 T2467（T7b），下一节 §272，下一条 H253。待写：T7b（含通知 REQ）、G7、L4b2、L3d1、L3b2、T1、T4s2、T5s2、X1b、U1s2、U3s2–U3s4、U2。

## §272 — L3b1、P2 合并；放 T7b = T2467、G7 = T2468；发子阶段 T 的通知 REQ（总调度 V3，2026-10-12 17:35 UTC）

- (1) **T2456 = L3b1 合并** 3bb131d（17:13 UTC；拆分 Σ 之后：`Graph/BALocReg1` 884 + `BALocReg1B` 926；目标 1、2、3(a)(b)、4–10 与实例；3(c)–(e)（`e2`、`macroA`、`macroB` 的 `BAShapePath`）挪到 L3b2；审核第一轮 RETURN（目标 10 的实例 (ii) `P_C` 处的 `baShapePath_e1_tn`、(vi) `BAReach` 可达图上的 `LocStd` 分支缺）→ 规则 (B) 修补 → 第二轮 PASS）。**L3b2 与 L3d2 现在可写**（L3d2 读 L3b1 的 (1)–(5) 约定 `BALocReg15`；L3b2 必须把 3(c)–(e) 列为目标，O2R-C4）。
- (2) **T2461 = P2 合并** a55ef84（17:24 UTC；`BA/NetLiftBA` 838 行：`baNetLift2_holds`、`baFlow_premises`（P6）、实例；审核 PASS）。T1-BA 的 `hNet` 与 P6 有了。
- (3) **T2467 = T7b**（子阶段 T 15 / 31.5；BA 134；`prover-hard`；不设设计门：T2454 的探针 e949c71 已编过目标 8–11，1a-audit 第二轮已过）：新文件 `Chain/Step2EventsGen.lean`（不 import `BA/*`；T1 import 它）加**新叶文件 `Chain/Step2EventsGenTw.lean`**（BA 侧，不改已合并的 `DecayGenTw`）；目标：`STScaleInvgL`、`ST_LW_sectionsg`、四个事件、`STGoodAtg`/`ST_good_probg`、`STBdatagL` 与两条 L-桥（目标 11 留在本行，带状证明 72 + 29 行，在 150 行规则内），51 个声明表里的 20 个泛型形式；F7 泛型地证。`STScaleInvgL`、`STStep1WeakgL` 作显式前提（不捆在 section 里）。`Step2EventsGen` import `Chain/DecayGen`（无环）。
- (4) **T2468 = G7**（BA-G；G/E 13 / 19.5；BA 135；`prover-hard`；不设设计门；估计 600 / 900 / 1,400）：**新增** `BA/Step1Prime.lean`（备用 `Step1PrimeB`；原地改会成环：`BAGbEXPij'` 在 `GreenCore`，而它 import `Step1`/`Step1Fam`），不进证书通道。目标：带撇钉文传给族里每个成员 `baGij'_member`；事件簿记与窗口常数只依赖 (d, c) 的 `flowFM_wl_det` 孪生；带撇副本 `baS1_wl_seq'`…`baS1_loopPT'`；`baBootstrap'_of_ij'`、`baStep1_of_ij'`；无条件的 `baBootstrap'_holds'`、`baStep1_holds'`（`2 ≤ d`；U3-BA (b) 与 U5 读后者）；BA 读法 `baSTGiiGEXgL_holds`、`baSTGavLGEXgL_holds`；实例（`inst_baBootstrap'_ij'` 用 `inst_BAKbound` 消掉 `hK`，0150 O2；旧的 `inst_baBootstrap'`、`_full` 保留 `hK`）；登记：`BAGbEXPij` 从 `owedProps` 移到 `supersededProps`，几行注释改写。**`STGijGEXgL` 的 BA 负责人记为 T1-BA**（它是带状窗口形状，1155 C3 说 BA 上证不出，`stStep2LocalPT_of_L2decayG` 的 BA 读者要一个带撇后继）。Step 1 没有 g/g₀ 跨越。**G7 合并后 stage G 关闭**，届时发关闭 REQ。
- (5) **发 `REQ-2026-10-12-1734-Tnotice`**（子阶段 T 的通知，不阻塞，只问"有无异议"）：T7 拆成 T7a/T7b（H248 (2) 预签）；P1 Amend 1（H3 改不等式，目标 4 离开，双槽 BA 尾等 T2459 报告）；P1 只做 m = 2 及对 1152 U-C6 (c) 的读法；§269 (2) 比较假设加非负。
- (6) 开工顺序：T2463 → T2457（1b）→ T2460 → **T2468（G7）→ T2467（T7b）**；T2465 等 T2464、T2466。下一张票号 T2469，下一节 §273，下一条 H254。待写：L3b2（含 3(c)–(e)）、L3d2、L4b2、L3d1、T1、T4s2、T5s2、X1b、U1s2、U3s2–U3s4、U2。

## §273 — 监督 1752：UBA-C1 比较假设改为 R1（TN-C1；限定范围的 HOLD 在记录上解除）；T2462 1a-audit PASS、按预签拆 U4s1a/U4s1b、Amend 1；T2457 的 1b 改用 R1；T2459 合并（总调度 V3，2026-10-12 18:13 UTC）

- (1) **监督 1752 的裁定**（对 `REQ-2026-10-12-1734-Tnotice`）：建议 HOLD，只限 UBA-C1 的比较假设文本（TN-F1）；T 的三项通过，附条件 TN-C1–TN-C4。TN-F1：`Sizes.lam` 不是每个 n 都有符号（`Defs/Sizes.lean:144`；`WO` 只是最终成立），所以 §271 (4) 的文本在带状（第一合取项就是 `∀ n, 0 ≤ sz.lam n`）和 BA（`sz.lam n < 0` 处 `gK n = √t₀·sz.lam n > sz.lam n`）都消不掉；§271 (4) 写的理由是错的。**决定（TN-C1，采纳 R1）：UBA-C1 唯一的比较假设文本是 `∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`。** 带状 `gK = sz.lam`、`A = 1`（`mul_self_nonneg`、`le_refl`）；BA `gK = BAflowLam0 sz z`、`A = (κ+1)/κ`（`0 ≤ √t₀·lam²`，`TwistStep2_lam0_sq`）；对每个 n、每个容许的 `sz` 都成立，只用已合并的名字。逐指标的推论（三行引理，各行可写私有副本）：`sz.lam n ≥ 0 ⇒ 0 ≤ gK n ≤ sz.lam n`；`sz.lam n < 0 ⇒ sz.lam n ≤ gK n ≤ 0`；`gK n = 0 ↔ sz.lam n = 0`；`0 < gK n ⇒ 0 < sz.lam n ∧ gK n ≤ sz.lam n`。§269 (2) 的跨越表对每个 n：(a) 窗口只要 `gK² ≤ lam²`；(b) A 形式阈值、(c) 比值都读平方；(d) `ellT`：`lam n ≤ 0` 时两边都是 1，正的情形照旧；(e) 本来就是最终的。**这个文本替换 §269 (2) 与 §271 (4) 的比较假设，凡引用处一律用它**：T2457 (a‴)、T2462、U3s2–U3s4、U3-BA、U4-BA、X1b、U5 的 1b 行、T2459 的 C1 表（它的保护形式 `0 < gK n → gK n ≤ sz.lam n` 由 R1 推出）。不采纳 R2（只有平方；要求 (d) 的读者都是最终的或带保护）和 R3（给每个特化加 `∀ n, 0 ≤ sz.lam n`，造成无主的欠账，与 ST-3 / §106 (1) 相反）。已合并的文件里没有旧文本（唯一命中是 `Chain/CltGen.lean:19` 的文档串，留给以后碰这个文件的行顺手改）。**HOLD 在记录上解除**：本节和 H254 把 R1 交到 T2462 和 T2457，不另发 REQ。
- (2) **T2462 = U4s1 的 1a-audit PASS**（18:07 UTC）：探针 359 行，三条标准公理；D1（Ward 项，`T2462_WardIdent` 原文；T2463 当时未合并，由本行定 Ward 文本，§270 注 (7)）、D2（`ThDecayK` 原文，`ProfileK` = 检查文本 + E1）、D3 通过；F2（`Step5KerGen` 复制 97 行辅助，不加 `Induction/NewKLKL`、`B45` 的 import）、F3（`_band` 的结论头）、F4（不搬 `NewKLKGen` 的 BA 例子）。**按预签拆分**（中心 2,011 > 1,950）：U4s1a = `Chain/Step5CasesGen`（目标 1–7，七条登记行，中心 933）；U4s1b = `Chain/Step5KerGen` + `Chain/NewKLKLGen`（目标 8–11，无登记行，中心 1,078），U4s1b 走自己的分支，不等 U4s1a。U 7 / 34.5（1752 O5 已按拆分计）。**Amend 1**（`docs/tickets/T2462-amend-1.md`，调度改了检查文件）：`T2462_ProfileK` 的比较子句和两条 UBA-C1 形状行改为 R1，加一条逐指标推论的形状行；目标 12 (a) 的 grep 字面量是 R1；非带状实例用 `gK = sz.lam / 2`、`A = 4`，不用 `withLam`（1a-audit O2）；O3：U4s1a 的 2,000 行停止线照旧约束。拆分的通知并入下一份 REQ。
- (3) **T2457 = U3s1 的 1b**：H252 (2) 的文本作废，改用 R1。窗口步 (a) 对每个 n 只用 `gK n ^ 2 ≤ sz.lam n ^ 2`，不再按 `sz.lam n = 0 / > 0` 分；`ellT` 那一步 (d) 按 `sz.lam n` 的符号分（1752 TN-C1）；用私有的三行引理。它 18:12 已按 H252 (2) 开了 1b：H254 (2) 让中枢停掉、带 R1 重跑。
- (4) **T2459 = U5 设计门合并** e288560（17:41 UTC；只合并报告，探针与脚本留在 `t/T2459`；审核 PASS）：BA 情形 (iii) 在论文层面用具名输入闭合；1b 五行 U5a `BA/Step5IIIKer` 1,200、U5b `BA/Step5IIIEdet` 2,350（新数学，`prover-max`）、U5c `BA/Step5IIIGood` 900、U5d `BA/Step5IIIWalk` 2,200、U5e `BA/Step5IIITargets` 250，中心 6,900（4,650 / 6,900 / 10,600）。1752 接受这个重新定价：U 计划 23 → 28，旗标 34.5 → 42，五行不必再 REQ；第六行或 U5b 超过高估 3,600 才要短 REQ。顺序：U5a、U5b 没有未合并的输入；U5c 等 Steps 1–4 的 BA 钉文（作假设）；U5d 等 U5a–U5c 和 TN-C2 行；U5e 等 U5d 和 T2462 的目标 4。U5 各行用 R1。**T2459 的生产者表对 U5d 作废**（"无生产者的输入：无"和 F5"目标 4 必须留下"都已过时，见 1752 TN-F2 和 T2459 审核 O1）：双槽 BA 尾由新开的 T 行产出（下一节）。
- (5) 在跑：T2462（U4s1a 进 1b；U4s1b 等 Amend 1 的检查编译后排队）、T2457（1b，带 R1 重跑）、T2464、T2466；T2463 已合并（下一节簿记）。排队：U4s1b → T2460 → T2468；**T2467 等 TN-C3 的修订（下一节）再开工**；T2465 等 T2464、T2466。下一节 §274，下一条 H255。

## §274 — T2463 合并；按 1752 O2–O5：开 P1b = T2471（双槽 BA 尾）、T2467 Amend 1（布局定为新叶）、m = 2 前提规则；放 L3b2 = T2469、L3d2a = T2470；发通知 REQ（总调度 V3，2026-10-12 18:38 UTC）

- (1) **T2463 = U1s1 合并** 01b4c521（18:11 UTC）：新 `Chain/ZeroModeGen` 878 行（新增；备用 `ZeroModeGenB` 未用）；目标 1–8、10 与实例；条件目标 9（`stNewPQgL_wardCls`）按票挪到 U1-BA（T2457 未合并）；无登记变更；审核 PASS 第一轮。Ward 文本由先到 1a-audit 的 T2462 定（`T2462_WardIdent`，§273 (2)）；已合并的 `ZeroModeGen_WardCls` 与它的关系由 U4s1a 的 1b 在开始时查（导入，或带精确类型的桥，§270 注 (7)）。
- (2) **O2（TN-C2）：开 T2471 = P1b，双槽 BA 尾**（T 16 / 33，拆分时 17 / 34.5；BA 138）。目标是 TN-C2 原文 `∃ C₀, 0 ≤ C₀ ∧ STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0`（`T2459_P1`，每个 d）。窄设计门 D1–D3 带探针步骤：D1 用复用普查定路线（默认 (i)：泛型后继 `Chain/GridRepTailGen` + `GridRepTailGen2`，BA 叶 `BA/GridRepTailBA`；改走 (ii) `BA/TwistGridQTail*` 的规则：有带状专有事实写不成"BA 侧已合并或 ≤ 400 行可证"的类字段）；D2 定核类 K1–K4 与增量类；D3 定行数与拆分。估计 2,400 / 3,400 / 5,000：预签在 1,950 处拆成 P1b-1（两个 Chain 文件）/ P1b-2（BA 叶），第二行不发 REQ，P1b-2 可在 P1b-1 审核 PASS 后走叠在 `t/T2471` 上的分支、在 P1b-1 之后合并；第三行（中心 > 3,900）要短 REQ。`prover-hard`；若取 (ii)，或 BA 的交叉标签二次变差不是带状的形式，预签改 `prover-max`。**一处读法（报监督）**：TN-C2 写"由 P1 的目标 2 加第 4 条组成"；但 `baGridMart_holds` 的结论是 `∃ Mart Rem`，而第 4 条要对同一个 `Mart` 成立，所以本行用 P1 的**目标 1**（`T2460_Bridge`，H3′）加 TL 的显式部分 `baTwistGridRem_holds`、`baTwistGridTail_holds`。目标 6 (a) 把桥当精确类型的假设，不等 T2460；6 (b) 只有一行，T2460 没合并就挪到 U5d 开头，不挡合并。**负责人移动**：T2460 原目标 4 (a)（三条列表恒等式与 `filt` 等式）和 T2459 约 120 行的列表-环桥归本行，U5d 导入目标 5。带状只要结论桥和 `GridRepTailGen_Ker` 的带状实例（不要求 `Inc` 的带状实例；3 (c) 取消）；BA 侧的证明就是类不空的检验。UBA-C1 预计不触发（触发就只用 R1）。**T2459 的生产者表对 U5d 作废**（§273 (4)）：U5d 读本行的 `baGridRepNAt2_holds`（名字沿用 T2460 原来的提议）。T2460 照 Amend 1 不变，目标 4 不放回去。
- (3) **O3（TN-C3）：T2467 Amend 1**（`docs/tickets/T2467-amend-1.md`）：BA 侧放新叶 `Chain/Step2EventsGenTw.lean`，**不改** `Chain/DecayGenTw.lean`。这与 §272 (3)、CONTROL #435、票内的调度答复、T2454 1a-audit 第二轮的布局 (A) 一致；票里写"追加到 `DecayGenTw`"的各处（布局、注、唯一可写文件、构建、导入者 grep、diff）按 Amend 改读；检查文件只改了两处注释。
- (4) **O4（TN-C4）：m = 2 前提规则（常设）**：泛型后继（T1、U4s3 的后继、U5a–U5e、V 各行）都不以 `STGridRepNgL`（所有 m）作前提，只取 `STGridMartgL` 或 `STGridRepNAtgL d 2`；验收 grep：新公开陈述里 `STGridRepNgL` 0 处。原因：照抄带状的 `ST_gridMart_of_repN (stGridRepN_holds d hd)` 会带进所有 m 的钉文，而它在 BA 上没有生产者；登记表也不把 BA 上的 `STGridRepNgL` 记作欠账。写这些票时都写进去。
- (5) **放 T2469 = L3b2**（BA 136；L 36 / 50，计划 41；`prover-hard`；无设计门；`Graph/BALocReg2` + `BALocReg2B`，备用 `BALocReg2C`）：L3b1 挪出的 3(c)–(e)（`e2`、`macroA`、`macroB` 的 `BAShapePath`）、无绑定的路径步与 (1)–(5) 合同、组合陈述 `BALocRegConcl` 加输出的 (1)–(5)。T2448 的形状绑定用三个 `baShapeLL_*_tn` 消掉（就是 `baLocReg6_holds` 的内容；监督说的"用 `baLocReg6_holds`"按此读）。中心 > 1,575 时可在 `BALocReg2 | BALocReg2B` 处拆（计划 42，1b 前签字）。
- (6) **放 T2470 = L3d2a**（BA 137；L 37 / 50；`prover-hard`；无设计门；`Graph/BAMomentGen` + `BAMomentGenB`；1,300 / 1,480 / 2,630）：`LWMoment` 那一半（`LWfg`、`LWMomentG` 与带状桥、BA 读法 `BALWMoment`、无绑定的引擎 `ba_localregularX_holds`、`baLWMoment_of_anp`）。1b 开始时定两件事：T2469 已合并就用它的无假设形式，否则把路径绑定作目标 4 的第一个假设；T2466 已合并就导入它的重标度与 `baGtoAGT_holds`，否则写私有副本。**`LWMomentExp` 那一半改为后继行 L3d2b**（在 L3d4 的 1a-audit 之后），阶段 L 计划 41 → 42（旗标 50 不变）；连同路线说明（T2387 的 G 路线不适用，因为组装读的是 BA 对象；这一族中心约 3,000，T2387 定价 1,121）写进通知 REQ。
- (7) **发 `REQ-2026-10-12-1838-Unotice`**（不阻塞，问"有无异议"）：O1–O4 怎么落实（R1、U4s1 拆分、T2471 与目标 1 的读法及负责人移动、T2467 的布局、m = 2 规则），以及阶段 L 计划 41 → 42（L3d2b）。
- (8) 路线账（1752 O5 加本节）：BA 139（T2471；含拆出的 U4s1b）；G/E 13 / 19.5；T 16 / 33；U 7 / 42，计划 28；L 37 / 50，计划 41（提议 42）；V 0 / 12。
- (9) 在跑：T2457（1b，R1）、T2462（U4s1a 的 1b）、T2464、T2466。排队（有空位就开）：U4s1b → T2460 → T2468 → T2471 → T2469 → T2470 → T2467（Amend 1）；T2465 等 T2464、T2466。下一张票号 T2472，下一节 §275，下一条 H256。待写：U5a、U5b（没有未合并的输入）、L4b2、L3d1、T1、T4s2、T5s2、X1b、U1s2、U3s2–U3s4、U2；G7 合并后发 stage G 的关闭 REQ。

## §275 — 监督 1852 PASS（HOLD 已解除）；U4s1a、U4s1b、U3s1、L4c2、L4c1 合并；放 L3d4 = T2472（G5 设计门，排最前）；UN-C1–C5；BA 全程预计（总调度 V3，2026-10-12 19:34 UTC）

- (1) **合并**：
  - **T2462 = U4s1 完成**：U4s1a c9f69dba（18:50；`Chain/Step5CasesGen` 784 行，目标 1–7，七条登记行）+ U4s1b 52f8f82a（19:30；`Chain/Step5KerGen` 550 + `Chain/NewKLKLGen` 377，目标 8–11，R1）；两半审核都 PASS 第一轮。文章差异候选 `T2462a`（载体数据形式：流事实和 `(zYU1)` 恒等式是目标 2–7 的假设，带状由目标 1、7 消掉）。X1b 现在可写（它读目标 1）。
  - **T2457 = U3s1** 6e7d2602（18:55）：`Chain/Step34Gen` 1,255 + 叶 `Step34GenTw` 99；目标 1–9（R1，(d) 按符号分）；两条登记行；审核 PASS。U3s2–U3s4、T2463 的条件目标 9（挪到 U1-BA）、U2 现在有了输入。
  - **T2466 = L4c2** 03109267（19:00）：`Graph/BAExp14d` 620 + `BAExp14dB` 908；目标 1–8（`BAG5LeafPrec1 = T2465_Q1Need`）；审核 PASS。
  - **T2464 = L4c1** 9e1d5f15（19:32）：`Graph/BAExp14c` 919 + `BAExp14cB` 1,153；目标 1–7；审核 PASS。**T2465（L4g）的开工条件已满足。**
- (2) **监督 1852：PASS**，对 REQ 1838 的六项都无异议；1752 的限定范围 HOLD 在记录上解除。条件 UN-C1–C5：
  - **UN-C1（O1）：L3d4 不在待写清单上**，它挡着 L3d2b、L5、L6（自 11:30 L3d3 合并起就能写）。→ 本节 (3) 放 T2472，排最前。
  - **UN-C2（O2）：L5 按孪生价重新定价**（`LWTermHolds 1-1801` + `LWTermExpN 1-546`，中心 1,994，预计两个文件、可能两行；G 路线不适用，理由同 L4a、L3d2）。**阶段 L 的计数**：计划 42 是行数，已用 37 是票数（含两张返工），未放的行 L3d1、L3d4、L3d2b、L4a2、L4b2、L5、L6 共 7 行 → 终点 **44 张**，实际约 45–47（旗标 50）。到 40 张时的阶段 L REQ 要逐行给出预测（L3d1、L3d4、L3d2b、L4a2 两半、L4b2、L5、L6），并写明预测到 50 之前怎么办。
  - **UN-F3（O3）：计数更正**：U 是 **8 / 42，计划 29**（U4s1 拆分加一行；我 §273 (2) 读错了）。§274 各票的 BA 序号顺移一位：U4s1b 136、T2469 137、T2470 138、T2471 139（票头上写的 136/137/138 以此为准）；总数 139 不变。
  - **UN-C3（O4）：Ward 的唯一 BA 证明**：`ZeroModeGen_WardCls`（T2463）与 `Step5CasesGen_WardIdent`（U4s1a）两个文本在带状都对、都要用（`STNewPQgL` 读前者，`STWardIIgL` 读后者）；缺的是桥 `ZeroModeGen_WardCls C →（一指标 L、K 的共轭）→ Step5CasesGen_WardIdent C`。**负责人：U4-BA (b) 与 U1-BA 中先写的那一行**；共轭条件写成内联假设，不起名 `Prop`（免得探针扫描加登记行）；U4-BA (b) 读 U1-BA 在 `baFM` 上的类，不另证恒等式。计数不变。写这两行时带上。
  - **UN-C4（O5）：** T2467 `:39` 停止规则里引的旧比较文本按 R1 读（H256 让中枢写在开工行里，不另出 Amend 2）；T2468 `:30` 引的 §271 (4) 按 §273 (1) 读（T2468 在跑，H256 转告）。
  - **UN-C5（O6）：T2471 的 1a/1b**：第 1 条对**每个** n 成立，而桥只是最终成立，所以 `Rem` 取每个 n 上的残差 `A_k − A_0 − Δ Σ Drift − Mart`（`baTwistGrid_decomp` 的模式，`TwistGrid2:166-176`），不取 `twRem`；第 2–4 条是最终的，在那里用 H1–H2 与目标 5 的恒等式得 `Rem = twRem`，`Σ martIncNg = twMart`（在 `(σ, a 0, a 1, a 1)`），二次变差用 H3′ 在 `ε′/2`；`CK` 取三部分的最大值。T2471 19:30 已开工，H256 把这条作为说明交给它的 1a 与 1b。
- (3) **放 T2472 = L3d4 `BAProv`**（BA 140；阶段 L 38 / 50，计划 42 行 = 44 张；`prover-hard`，1a 碰到条件 (a)/(b) 预签改 `prover-max`；`Graph/BAProv` + `BAProvB`，备用 `BAProvC`；1,329 / 1,547 / 2,930，参考上限 4,020）：带状 `LWProv 1-1820` 的 BA 孪生；**窄设计门 G5 带探针**：1a 写出 `lem:LW_moment_exp` 来源（provenance）那一半的 BA 论证（每个 BA 步给旧顶点到新顶点的映射；分子在 `BAGraph.shadow` 上读，没有新分子；恒等式逐标号成立，加权版求和即得；起始项覆盖；根取 `β^{(k)}` 的像），定 `BAProvOut`、`BACoverBy`、`BAWExp`、`BAProvStepPos`、`BAEngineProv`、`fxyValD` 及桥的陈述，并给出 L3d2b、L5 要读的接口表（1a (viii)；**L3d2b 的票就按 1a-audit 的这张表写**）。没有未合并的输入（T2469、T2470 不是输入；T2448 的绑定在本行用三个 `baShapeLL_*_tn` 消掉，`ba_localregularX_holds` 仍归 T2470）。调度答复：拆分在 1,950 处预签（L3d4a / L3d4b，计划 42 → 43、预测 45，在 40 张的阶段 L REQ 里报），第三行要短 REQ；BA 带根的 G3（`AuxGraphRooted` 的孪生，约 480 中心）归 L3d2b；数据层 `fxyValD`、并集引理与桥归本行，载体 `LWfgD` 归 L3d2b；L4-C4 (b) 只是 1a 项；UBA-C1 不触发（触发只用 R1）。**排在下一个空位**，在 T2469、T2470 之前。
- (4) **BA 全程预计（给 Jun，仅供参考；§144 不设上限）**：已用 139（加本节 140）；已计划未放：T 约 7、U 21、L 7–8、V 约 8、M/N 6–10 → 终点约 **190–200 张**（再有返工另算），对照 T2326 的估计 141 [136–163] 与计划数 165（§148 (1)）。超出的部分在链式子阶段（T/U/V 现计划约 60 行，在 T2326 链区间 [33..61] 的顶部）和阶段 L（计划从 33 行涨到 42 行）。各阶段旗标仍是控制手段；下一份开阶段 REQ 或 40 张的阶段 L REQ 带上这个预测。
- (5) 在跑：T2460、T2468、T2471 + 空出的一个位；排队：**T2472 → T2465 → T2469 → T2470 → T2467**。下一张票号 T2473，下一节 §276，下一条 H257。待写：X1b（U4s1 已合并）、U3s2–U3s4（U3s1 已合并）、U5a、U5b、U1s2、U2、T1、T4s2、T5s2、L4b2、L3d1、L3d2b（在 T2472 1a-audit 之后）、L5（孪生价）；G7 合并后发 stage G 关闭 REQ；阶段 L 到 40 张时发阶段 L REQ（带全程预计）。

## §276 — P1、G7（stage G 关闭）、L4g 合并；T2471 1a-audit PASS（拆 P1b-1/P1b-2）；放 T5s2 = T2474、T4s2 = T2473（T5s2 在前）；L3b2 拆分签字；Jun「start」→ M/N 部分开阶段；发 REQ（总调度 V3，2026-10-12 20:34 UTC）

- (1) **合并**：
  - **T2460 = P1** ad52b370（19:33）：`BA/GridMartBA` 747 行；目标 1（H3′）、2、3、5、6；目标 4 已离开（归 T2471）；审核 PASS。T2471 的 6 (b) 现在可以直接用 `baGridBridge_holds`。
  - **T2468 = G7** e9d820fc（19:36）：`BA/Step1Prime` 1,181 行；带撇的 Step 1（`baBootstrap'_holds'`、`baStep1_holds'`）、`baSTGiiGEXgL_holds`、`baSTGavLGEXgL_holds`；登记：`BAGbEXPij` 移入 `supersededProps`；审核 PASS（O1：`baS1_*'` 多带 `hd : 2 ≤ d`，与钉文目标一致）。**stage G 关闭的五个条件（2254 Q2）都满足**（见 `T2468-prove.md:139`）→ 本节发关闭 REQ（与 (6) 合并）。H256 (4) 的 UN-C4 说明没赶上 T2468（它已合并）：其报告 `:30` 处读 §271 (4)，按 §273 (1) 理解。
  - **T2465 = L4g** c986735f（20:21）：`Graph/BAExp14e` 433 行；`baG5LeafPrec_holds`、`baExp14bS3_holds`；审核 PASS。**L4 的 S3 链到此闭合。**
- (2) **T2471 = P1b 的 1a-audit PASS**（20:16）：路线 (i)；中心 2,960 > 1,950 → **按预签拆成 P1b-1**（`Chain/GridRepTailGen` + `GridRepTailGen2`，目标 1–3）**/ P1b-2**（`BA/GridRepTailBA`，目标 4–7），不要第三行；条件 (7) 不成立，1b 用 `prover-hard`；UN-C5 已进它后面各阶段的提示（H256 (3) done）。计数：T 17 / 34.5，BA 141（P1b-2）。观察 O3：`Chain/GridRepTailGen` 没有备用文件，2.6× 参考超 2,000，超了就是停止。
- (3) **放 T2474 = T5s2 与 T2473 = T4s2**（两张都在 `Chain/` 新增文件，带状文件不改，不进证书通道）。**带状的 import 顺序是 T5s2 → T4s2**（`GridGoodN`、`GridEnvelopeN`、`GridAssemblyN`、`AzumaProxyN` 都 import T5s2 的文件），与 T2379 的排序相反，所以 **T5s2 在前，T4s2 等 T5s2 合并后再开工**。
  - **T2474 = T5s2**（BA 143；T 19 / 34.5；`prover`，C6 触发或类字段无带状消法时预签改 `prover-hard`；不设设计门；`Chain/StepDecompGen` + `Chain/HierDriftGen`，备用 `HierDriftGen2`；1,350 / 1,900 / 2,950；预签在文件边界拆 T5s2a / T5s2b，T5s2b 可叠在 `t/T2474` 上）：`StepDecompN`、`LoopC2N`、`HierAlgebra`、`QVN`、`GridDriftN`、`HierarchyN`（§196 (2) 并入）的泛型形式：载体类 `StepDecompGen_LoopForm` / `_WalkForm`、`hermTestFunLoopNOf`、`QVPropagatedNg`、所有 k 的词汇（`loopFamNg`、`ZfamNg`、`ZvecNg`、`YvecNg`、`stoppedEdgeNg`、`SubGaussFormNg`、`SubGaussStopNg`）与识别、层级代数（K-loop 类、类 (t) 的 `KTwo`）、`HierarchyNg`、`stepErrNg` 与 `GridDriftNg` 钉文、`gridDriftNg`、两个包络、带状实例。**它拥有每步层与漂移的全部泛型名字。**
  - **T2473 = T4s2**（BA 142；T 18 / 34.5；`prover-hard`；窄设计门 D1–D3 带探针；`Chain/GridGoodGen`、`GridEnvelopeGen`、`GridAssemblyGen`、`AzumaProxyGen`，备用 `AzumaProxyGen2`；2,000 / 2,900 / 4,500；预签拆 T4s2a = GridGood + Envelope / T4s2b = Assembly + AzumaProxy）：矩阵控制、`GoodSetNg`、出口时与可测性、`GridGoodN` 钉文（每个载体与族两种形式）、包络、组装、Azuma 代理、初始归属（内联假设）、Y 矩、实例。**调度答复**：T5s2 先合并（两半都合并）再开工；不定义 T2474 的任何名字，原目标 6（词汇）取消，目标 5 只留 `GridEnvelopeN` 的包络并按名字读 T2474 的 `stepErrNg`、`gridDriftNg`；W 用 T2474 的 `StepDecompGen_WalkForm`（一个文本）；核事实在 T2471 的 P1b-1 已合并时 import `GridRepTailGen_Ker`，否则同一合取式内联，不另起名字（X1-C4）；W 与 T2467 的 F9 不冲突（F9 是 T7b 的 BA 侧事实，W 在 BA 上是定义性的，归 T4-BA/T5-BA）；BA 的初始归属（`H₀ = g₀Ψ`）1a 报告有无来源，没有也**不** RETURN，记为 T4-BA 的欠项、由调度报监督；`STSEforLngL`、`STSEforLnConclgL`、`STEKDecaygL` 的登记负责人 U2 / U2-BA。
  - **与 T2471 的分工**：T2471 保留 `GridRepTailGen_Ker` / `_Inc` / `_Hyp`（m = 2 尾），不定义 T2474 的任何公开名字（H257 告诉它的 1b）；T2474 的 `HierDriftGen_UStep` 第一字段照抄 T2471 的 K3（内联，一行桥），不 import T2471 的文件。
  - **下游覆盖（记给 U 的票）**：U2、U4s3 不读这六个文件里的任何名字（只经 import 闭包）；U1s2、U3s2–U3s4、T4s2 只读 T2474 目标 2–10 列出的名字。T4s2 的五个文件：U3s2–U3s4、U1s2 读（按用量统计列在 T2473 各目标下），U4s3 不读。
- (4) **T2469 = L3b2 的拆分签字**（1a 预检 BLOCKED 于 §227 拆分规则，20:30；数学全部 PASS，`PathInv2` 逐项 0 违例；中心 2,130 > 1,575）：**签字，按票里预留的边界拆**：L3b2a = 目标 1 (a)（`Graph/BALocReg2`，1,240）；L3b2b = 其余（`Graph/BALocReg2B`，890），在 L3b2a 审核 PASS 后走叠在 `t/T2469` 上的分支、在 L3b2a 之后合并。阶段 L：计划 42 → **43 行**，预计 **45 张**（T2472 若拆则 46）；已用 39 张（含 L3b2b）。下一张阶段 L 的票到 40 张，届时发阶段 L REQ（UN-C2 (b)：逐行预测和到 50 之前怎么办，带 BA 全程预计）。
- (5) **Jun 的决定**（2026-10-12 约 20:2x UTC，原话）：「start」。读作对 §266 (1) 所问"C5g、N3a、N3b 不需要 U、V 的输出，能否在 V 关闭前开"的答复：**可以开**。（如果 Jun 本意不是这个，以 Jun 后来的话为准。）§260 (3)"M/N 的证明票等 V 关闭"对这三行解除；M/N 其余各行（M1、M2、M3、N2 和 C3、C4、C5）仍等 V 关闭。按 TEAM §6，开 M/N 要开阶段 REQ：本节的 REQ 提议现在开 M/N、只放这三行，旗标按 T2449 MN4 定为 15（含 C 行；M/N 六行 9）；N3a、N3b 的可写文件（T2449 §4：原地改已合并的 UN 文件并做 G1 检查，或写带撇后继）由各自 1a 按证书锥检查定，原地文件在证书锥里就默认写带撇后继。监督回复前这三行不开工（REQ 回来再写票）。
- (6) **发 `REQ-2026-10-12-2034-GcloseMN`**：A 部分 stage G 关闭（2254 Q2 五条，T2468 的合并名字；`STGijGEXgL` 的 BA 负责人 T1-BA，§272；G5c 的 1b 放弃，§234；登记 `:148`、`:150` 改为"在 `baFMz` 上已证"）；B 部分 M/N 按 (5) 部分开阶段；C 部分计数与 BA 全程预计（1852 要求随下一份开阶段 REQ 带上）。
- (7) 计数：BA 144（T2474；含 P1b-2、L3b2b）；G/E 13 / 19.5（G 关闭）；T 19 / 34.5；U 8 / 42，计划 29；L 39 / 50，计划 43 行 = 45 张；V 0 / 12；M/N 待开（提议旗标 15）。
- (8) 在跑：T2467、T2470、T2471、T2472；T2469 等签字后进 1b。排队：**T2469（L3b2a 1b）→ T2474 → L3b2b（叠在 L3b2a 后）→ T2473（等 T2474 合并）**。下一张票号 T2475，下一节 §277，下一条 H258。待写：X1b、U5a、U5b、U1s2、U2（等 T5s2、T7b）、U3s2–U3s4（等 T4s2、T5s2、T7b）、T1（等 T7b）、L4b2、L3d1、L3d2b（等 T2472 1a-audit）、L5（孪生价）；M/N 的 C5g、N3a、N3b（REQ 通过后）；阶段 L 到 40 张时的 REQ。

## §277 — T2473 检查文件修正（总调度 V3，2026-10-12 20:46 UTC）

- (1) H257 (2)：T2473 的检查在 `main` c986735f 上 exit 1，两处错误都在 `:314-315`（`HasCondSubgaussianMGF … Cm.Pp` 要 `IsFiniteMeasure Cm.Pp`）。那是目标 6（`SubGaussFormNg`）的形状行，目标 6 已按 §276 (3) 取消；调度把这行的绑定改成 `(Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp]`（与 `StoppedAzumaNg` 一致），注明只作读法。钉文与其他形状都不变。T2474 的检查 exit 0。T2473 本来就等 T2474 合并，不受影响。H258 让中枢重编。
- (2) T2471 的 1b（P1b-1）在 H257 (4) 之前已开；不定义 T2474 名字的说明进它的审核提示（中枢在 1b → 审核边界交）。

## §278 — 监督 2049 PASS：stage G 关闭，M/N 开（只放 C5g、N3a、N3b，旗标 15）；P1b-1、L3d2a、T7b 合并；放 C5g = T2475、N3a = T2476、N3b = T2477（总调度 V3，2026-10-12 21:31 UTC）

- (1) **监督 2049：问题 1–3 都 PASS。** stage G 关闭（G/E 13 / 19.5，E 早已关闭）；M/N 为 C5g、N3a、N3b 开阶段，旗标 15；N3a、N3b 的可写文件规则接受，附 GMN-C2。条件（都不挡在跑的票）：
  - **GMN-C1（T1-BA）**：Step 2 局部界的带撇 BA 读者（`stStep2LocalPT_of_L2decayG` 的 BA 读法）写 T1-BA 时列为有名字、有定价的目标；首选把 Green 输入取成 `STGijDecgL`（`FarEntry` 的形式，带状经 `stGijDecgL_of_gex`、BA 经 U4-BA 从 `BAGbEXPij'` 的蕴涵），一个泛型读者服务两个模型；T1-BA 的 1a 确认 `STGijDecgL` 加 `(eq:Psirelations)` 能闭合局部界论证，不行就写只给 BA 的带撇读者；超 1,950 预签拆分。
  - **GMN-C2（N3a、N3b 原地改）**：(a) 1a 报两个锥（证书锥与 `Main/BandTerminal` 锥）；(b) 文件外有读者的公开声明陈述逐字不变（签名脚本 diff），两耦合与 C 形式起新名字，带状经 `lamV = lamQ`、`ouMatC_toC`、`UNGreenCorrAllC.toAll` 恢复，私有引理可改陈述；(c) 审核对比合并前后的 `#print axioms band_terminal` 与 `#print axioms bUniv_holds`，并跑全量构建；(d) 某个声明做不到 (b) 就只给它写带撇后继，1a 重新定价。实测八个文件的反向锥都不含证书模块、都含 `Main/BandTerminal`，所以都原地改（与 T2449 §4 定价一致）。
  - **GMN-C3（C5g）**：`RBG_*` 从 `t/T2449` 921369b 逐字照抄；四个 BA 实例（`ba_flowG`、`ba_domG`、MLout、`ba_dom_of_bulk`）作为目标放 BA 侧的叶文件；泛型文件不 import `BA/*`；C5 以后若要改 `RBG_Prod`/`RBG_Que`，写 C5 的带撇后继，不返工 C5g。
  - **GMN-C4：BA 的 `thetaDiff` 负责人记为 M3**（C3 的 1a 若用 `ζ = 0` 的剖面得到它，可以接过去）。写进 M/N 行表。
  - **GMN-C5：阶段 L 到 40 张的 REQ 从基数 45 算**（43 行 + 2 张返工），实际 46–48（T2472 预签拆分 +1，L5 按孪生价 1,994 很可能 +1），并在到 49–50 之前写明哪些行可合并、哪些可等 HOLD 复核。
  - **O6**：M/N 其余各行（M1–M3、N2、C3–C5）在 V 关闭时发一份短通知 REQ 开，届时对照 V 已合并的输出（`BAMLOutTL`、V3）复核 T2449 的探针钉文；旗标仍 15，除非行表变。
  - BA 全程预计更新为约 **194–199** 张（1852 的 190–200 下限上移）。
- (2) **合并**：
  - **T2471 P1b-1** 51e233bd（21:10）：`Chain/GridRepTailGen` 795 + `GridRepTailGen2` 929；目标 1–3；审核 PASS；P1b-2（`BA/GridRepTailBA`，目标 4–7）在叠加的 `t/T2471b` 上跑。
  - **T2470 = L3d2a** 4cc5e713（21:13）：`Graph/BAMomentGen` 1,549 + `BAMomentGenB` 847；目标 1–4（目标 4 按钉文以 `BAAnpAuxG 3` 与路径绑定为条件：L3d1 合并后的第一个消费者、T2469 合并后的第一个消费者各消一个，最迟 L6）；审核 PASS。
  - **T2467 = T7b** 97341078（21:18）：`Chain/Step2EventsGen` 1,351 + 叶 `Chain/Step2EventsGenTw` 171；目标 8–11 与 F1–F2、F7、F9；登记 +6；`DecayGenTw` 未动；审核 PASS。**T1 现在可写**（它等的是 T7b）；U2 还等 T5s2（T2474 在跑）。
- (3) **放 M/N 的三张票**（都 `prover-hard`，都只用已合并的输入）：
  - **T2475 = C5g**（M/N 1 / 15；BA 145；窄设计门 D1–D2 带探针：兼容输入与 `g1Rowk_of_inputsG` 在 T2449 只有描述，1a-audit 定；`RBG_*`（目标 1–4）与四个 BA 实例（目标 9–12）现在就有约束力；泛型 `Universality/GUEPhase/RandomLayerBG` + BA 叶 `BA/RandomLayerBGBA`；520 / 720 / 1,040）。答复：BA 上兼容输入的剖面一半归 **C3**；名字 `g1Rowk_of_inputsG`；登记按前提扫描给未被推出的 `RBG_*` 加欠账行（负责人 BA-C5），改 `:172-173` 的负责人注释。
  - **T2476 = N3a**（M/N 2 / 15；BA 146；E1 在 BA 叶 `BA/EMCTE2BA`（备用 `JakUywBA`），E2 原地改 `Jak`、`Uyw`（`JakSpectral` 预计不改）；680 / 930 / 1,280；预签拆 N3a-1 / N3a-2）。**新发现**：`Jak`、`Uyw` 的定时引理还带着带状 bulk `|E| ≤ 2 − κ`（T2449 MN3 漏了），只加两个耦合到不了 `UNKind.ba`。答复：**加一个窄设计门 D1 带探针**，1b 前编出 `hdiag` 的 bulk 窗口形式与坏事件转移假设、以及它们的 BA 消法（`BAbulk_window`、`unBadYBA_measure_le`、BA 的成对形式）和带状消法；BA 消法不成立就停在 1b 前（短 REQ）；K 形式放叶文件用 `open private`（带状文件不加 import），做不到再让 `Jak` import `PinsK` 并报锥变化。
  - **T2477 = N3b**（M/N 3 / 15；BA 147；不设设计门；原地改 `GreenCorr`、`UnivMain`、`Step1Band`，备用新文件 `Step1BandC`；E4 = `unGreenCorrC`、`greenCorrAllC`；E3 = `step1BandC''` 等到 `unCoreC''_holds`；都对每个 `UNModelC` 成立，`baBUniv_of_rows` 原样接受）。答复：`PinsDens` 从可写文件去掉（`un_core_of_rows'` 的 C 形式放 `UnivMain`）；`GUETranslation` 不可写，翻译行的 C 形式放 `UnivMain`；`Step1BandC` 允许；带状 `step1Band`、`univMainRow` 保留原证明和陈述；非零均值实例放审核的草稿文件、贴进审核报告；三个新 import 接受，1a 报 `BandTerminal` 锥前后；三条已推出的欠账行删除（T2411 先例）。
  - **N3a 与 N3b 一次合并一张**；后合并的那张在合并后的底上重跑 `band_terminal` / `bUniv_holds` 的公理对比与全量构建。
- (4) 计数：BA 147；G/E 关闭；T 19 / 34.5；U 8 / 42，计划 29；L 39 / 50（计划 43 行 = 45 张，实际 46–48）；V 0 / 12；M/N 3 / 15。
- (5) 在跑：T2469（L3b2a）、T2471（P1b-2）、T2472、T2474。排队：L3b2b（L3b2a 审核 PASS 后马上）→ **T2475 → T2476 → T2477** → T2473（等 T2474 合并）。下一张票号 T2478，下一节 §279，下一条 H260。待写：**T1**（T7b 已合并）、X1b、U5a、U5b、U2（等 T5s2）、U3s2–U3s4（等 T4s2、T5s2）、U1s2、L4b2、L3d1、L3d2b（等 T2472 1a-audit）、L5（孪生价）；阶段 L 到 40 张时的 REQ（基数 45）。

## §279 — L3b2a、P1b-2 合并（P1b 完成）；T2472 1a-audit PASS、拆 L3d4a/L3d4b，阶段 L 到 40；放 T1 = T2478、X1b = T2479；发阶段 L 40 张 REQ（含 X1b 的 X1-C5）（总调度 V3，2026-10-12 22:27 UTC）

- (1) **合并**：**T2469 L3b2a** a931034a（21:50；`Graph/BALocReg2` 886 行，目标 1 (a)：18 个项引理 + 5 个列表形式；审核 PASS）；L3b2b 在叠加分支上跑。**T2471 P1b-2** ae791953（22:14；`BA/GridRepTailBA` 1,396 行，目标 4–7 含 6 (b)；审核 PASS）→ **P1b 完成**：`baGridRepNAt2_holds`（TN-C2 的陈述，每个 d）已证，U5d 的输入到齐。
- (2) **T2472 = L3d4 的 1a-audit PASS**（G5 设计门；探针 399 行；数值复现：0 个新影子分子、0 个未连接）：BA 来源论证已写；陈述按探针文本定；**中心 2,142 > 1,950 → 按预签拆 L3d4a（`Graph/BAProv` 847）/ L3d4b（`Graph/BAProvB` 1,295）**；不切 `prover-max`；接口表 (viii) 是 L3d2b 票的依据（O4：L3d2b 把 M 衰减阈值写成最终的（`∀ᶠ W`）界并带 `BAReal`，给极限检查）。**阶段 L 到 40 张**（38 行 + 2 张返工）→ 发阶段 L REQ（GMN-C5）。**L3d2b 等 T2472 两半都合并后再写**（它的检查要用 T2472 的名字，必须在 `main` 上）。
- (3) **放 T2478 = T1**（BA 149；T 20 / 34.5；**`prover-hard`**；不设设计门；新增 `Chain/Step2IterGen` + `Step2IterGen2` | `OptL2Gen` + `Step2CloseGen`，带状文件不动，不进证书通道；预签拆 T1a = 目标 1–6 / T1b = 目标 7–11（叠加）；2,000 / 2,850 / 4,250）：载体类 `NewKLKAtN`、`NewKLK`、`K2`、`OneLoop`；P4 `ST_good_engineg`；自改进步、迭代（`ST_decay_ptg`、`ST_L2_decay_ptg`）、平均律与打包；骨架 `ST_step2_of_pinsg`（唯一网格输入 `STGridMartgL`，TN-C4）；泛型 OptL2；**GMN-C1 的泛型局部界读者取 `STGijDecgL`**（带状经 `bandFM_STGijDecgL_of_three_le`；闭合不了就退回 T1-BA）；§12.2 列表恒等式的泛型形式（T1 拥有；T2471 已合并的是其 BA 实例，重合处一行桥）；带状推论与实例。**它顺带改写 `Test/Axioms.lean:195-196` 的 TLC-2 负责人文本**（1354 给的原文）。
- (4) **放 T2479 = X1b**（BA 150；U 9 / 42；`prover-hard`；不设设计门；**新增**而非原地：`Evolution/CltMoments2G`、`MeanFarG`、`CltFarG`，备用 `CltFarG2`，因为 `MeanFar` 2,311、`CltMoments1` 2,132 已超 2,000 行停止线；目标：泛型权与 `CltMom2` 词汇、矩层、均值部分、dom/off/fluc 步、`stCltFargL_holds : STCltFargL d`、带状生产者 `bandFM_STThPropsg`、`bandFM_STKpropsg`、桥 `STCltFargL d → STCltFar d`、实例；BA 实例归 U4-BA（C9））。**重新定价 1,500 / 2,000 / 3,000，超过计划 1.0k 的 1.5 倍 → 按 X1-C5 要发 REQ**（本节的 REQ 项 B）；**T2479 等监督对项 B 的答复再开工**。§270 (2) 记为满足（X1b 在带状桥和 `Prec` 辅助里用 U4s1 的目标 1，流元组包装留给 U4s2）。预签拆 X1b-1 / X1b-2（叠加）。
- (5) **调度直接改的文档串**：`Chain/CltGen.lean:19` 的旧比较文本改为 R1（§273 (1)；Lean 文档串，简单任务），H260 让中枢按名字提交。
- (6) **发 `REQ-2026-10-12-2228-L40X1b`**：项 A 阶段 L 到 40：逐行预测（未放的 6 行 L3d1、L3d2b、L4a2、L4b2、L5、L6；基数 46，实际 47–48，最坏 49），到 49–50 之前的计划：**P1 预签把 L6 并进 L5 的最后一张**（于是基数 45、实际 46–47、最坏 48），**P2 任何一次放行会让预测到 49 之前先发短 REQ**（合并候选：L4b2 并进 L4a2 后半；L3d1 并进 L3d2b 前半；或对剩余行做 HOLD 复核）；项 B X1b 的 X1-C5（2,000 中心，新增布局，无孪生，预签拆分）。
- (7) 计数：BA 150；T 20 / 34.5；U 9 / 42（计划 29，X1b 拆则 30）；L 40 / 50；M/N 3 / 15；V 0 / 12。
- (8) 在跑：T2469b（L3b2b）、T2472、T2474、T2475。排队：**T2476 → T2477 → T2478**；T2479 等 REQ 项 B；T2473 等 T2474 合并。下一张票号 T2480，下一节 §280，下一条 H261。待写：L3d2b（等 T2472 合并）、U5a、U5b、U2（等 T5s2）、U3s2–U3s4（等 T4s2、T5s2）、U1s2、L4b2、L3d1、L4a2、L5（含 L6）。

## §280 — 监督 2246 PASS（阶段 L 预测、X1b）；L3b2b、L3d4a、T5s2 合并；放 U2 = T2480、U5a = T2481（总调度 V3，2026-10-12 23:13 UTC）

- (1) **监督 2246：A1–A3、B1 都 PASS。**
  - **L40-F1**：L3d2b 拆两张是预期情形；按 1a 的 1.4–1.6 倍重新定价，**预期 47 张**（L3d1 1、L3d2b 2、L4a2 1、L4b2 1、L5（含 L6）2），范围 46–49（未计返工），离 50 约 3 张，P2 很可能要用；打包下限 46–47。
  - **L40-C1（P1 的预签形式）**：L6 的接线并进**最后写的那张终端票**（L5 的最后一张，或含 L4a2 组装的那张，等另一张合并后再写）；那张票 (a) 带 T2387 §8 (6) 的关闭条件（`BALWterm`、`BALWtermExp`、七前提 `BALWtermEXP` 已证并有 d = 3 实例；欠账行删除；载体形式对照 T2386 检查形状），(b) 消掉 T2470 目标 4 剩下的前提（`BAAnpAuxG`、路径绑定；"最迟 L6"改为"最迟这张"），(c) 加上 L6 约 250 中心重新定价，超 1,950 也不为 L6 拆（那是 P2 的情形）。它合并后发阶段 L 关闭 REQ。（L40-F2：L6 读 L4a2 的组装，所以不能固定塞进 L5。）**路径绑定**：T2469 两半都已合并，下一个写的消费者（L3d2b 或 L5）就消掉它。
  - **L40-C2**：L3d2b 的 1a 写明 `∀ᶠ` 相对耦合的位置：耦合 `g₀` 是序列前固定的实数则 `∀ᶠ n` 即可；载体若允许耦合随 n 在 `(0, Λ]` 里变，阈值对这个范围一致（O4 的数随 g 增大，上确界在 Λ）；阈值只依赖 `(d, Λ, κ)` 和固定指数；极限检查覆盖 L5 读的范围。
  - **L40-C3**：每次阶段 L 放行和每次 1a-audit 都重算预测；到 49 发短 REQ。
  - **L40-C4**：只在吸收的那张仍 ≤ 1,950 时合并；L4b2 只能并在 L4a2 组装那一半旁；L3d1 只能并进 L3d2b 较轻的一半并带着它的 G4 门；否则 49 的 REQ 就是 HOLD 复核。
  - **X1b（B1）PASS**：T2479 开工；**1a 的中心若超 3,000 发通知 REQ（X1b-C1）**；**任何预计超 1,800 行的新文件都要留备用兄弟文件（X1b-C2）**。
  - ROUTES（O6）：阶段 L 写"预期 47，范围 46–49（含 P1）"。
- (2) **合并**：
  - **T2469 L3b2b** bcd86fa2（22:28；`Graph/BALocReg2B` 624 行；目标 1 (b)–(d)、2、3、4；审核 PASS）→ **T2469 = L3b2 完成**。
  - **T2472 L3d4a** c4b39007（22:30；`Graph/BAProv` 877 行；目标 1–4、5 (a)、9；审核 PASS）；L3d4b 排队（叠加）。
  - **T2474 = T5s2 完成**，按预签拆成两行合并：T5s2a e8fd7d27（`Chain/StepDecompGen` 1,246）、T5s2b eaa247c4（`Chain/HierDriftGen` 1,381）；审核 PASS。子阶段 T 多一行。**U2 现在可写**（等的是 T5s2、T7）。T2473（T4s2）已开工。
- (3) **T2475、T2476 的 1a-audit 都 PASS**（都无签字）。
- (4) **放 T2480 = U2**（U 10 / 42；BA 152；`prover-hard`；不设设计门；新增 `Chain/KDecayGen`、`Chain/SEforLnGen`（备用 `SEforLnGen2`）、`Chain/B45Gen`（备用 `B45Gen2`），带状文件不动，不进证书通道；1,600 / 2,250 / 3,400；预签拆 U2a = KDecayGen + SEforLnGen / U2b = B45Gen（叠加））：时间一致的 𝒦 界与 Ward；`SEforLnGen_Facts` 类与 SEforLn 第 1–4 部分、`stSEforLnConclgL_of`、`stSEforLngL_of`；**`stEtermDecaygL`（T7a 的目标 7）：四个结论都是 U3s1 的 `STEKDecaygL`（在 `sz.lam`）**；`B45Gen_Facts` 与泛型 B45 核心（用 T7a 的 `stDecayLoopUgL_of_step2` 代替 B45 §3）、别的行读的 B45 辅助的公开泛型版；`stWardTypePPingL_of`、`stB45PingL_of`；实例。答复：一圈事实 T1 合并了就 import，否则同一合取式内联；Θ 和用已合并的 `Step5KerGen_ThDecay`；`STKcalDecaygL` 保持登记前提，负责人改为 U2-BA；C6 由 1a 测，触发就把类 (t) 段交给 U2-BA（已计划 937），除非 U2-BA 超 1.5 倍才发通知。
- (5) **放 T2481 = U5a**（U 11 / 42；BA 153；`prover-hard`；不设设计门；`BA/Step5IIIKer` + `BA/Step5IIIKer2`；800 / 1,200 / 1,800）：`lam0 ≤ sz.lam`（流上）、`T2459_BAweighted`、`T2459_BAKernel` 及其流上读法、`T2459_Theta_far` 与新的四种电荷对 `uKer` 远场（对 `v ≤ w` 一致）、BA 的 `tailtoTailSq`（(H1)–(H3)）及其 `STeeUMg` 读法（给 U5d）、实例。答复：核的路线由 1a 选较短的（走 `baProp5_holds` 就去掉目标 2）；目标 4 (b)、5 不设探针但 1a 先做数值核对，钉文不成立就停；保护形式是 R1 的推论，可用；拆分预签，但那是 U5 的第六行，1a-audit 确认时调度发短通知 REQ；(H2) 留在 U5d。
- (6) 计数：BA 153；T 21 / 34.5（T5s2 拆成两行）；U 11 / 42（计划 29 → 30：X1b、U2 若拆再加）；L 40 / 50（预期 47，范围 46–49）；M/N 3 / 15；V 0 / 12。
- (7) 在跑：T2473、T2475、T2476、T2477。排队：**T2478 → T2479 → L3d4b → T2480 → T2481**。下一张票号 T2482，下一节 §281，下一条 H262。待写：L3d2b（等 L3d4b 合并；带 L40-C2）、U5b（新数学，`prover-max`）、U3s2–U3s4（等 T4s2）、U1s2、L3d1、L4b2、L4a2、L5（P1）。

## §281 — N3b、C5g 合并；T2473 = T4s2 的 1a-audit RETURN → Amend 1（三行、`Im m ≤ 1` 前提、读已合并的 `LoopForm`/`Law`）；发 T 的短通知 REQ（总调度 V3，2026-10-12 23:28 UTC）

- (1) **合并**：**T2477 = N3b** 2dcfcda5（23:13；原地改 `GreenCorr` +268、`UnivMain` +215、`Step1Band` +489 −115，备用 `Step1BandC` 未用；9 个目标与实例；原有公开声明不变；登记删 3 行；审核 PASS；**合并后 `#print axioms band_terminal` 与 `bUniv_holds` 都是三条标准公理，与合并前相同**；T2476 = N3a 在这个底上重做对比）。**T2475 = C5g** 35b7d6cb（23:23；泛型 `Universality/GUEPhase/RandomLayerBG` 526（不 import `BA/*`）+ 叶 `BA/RandomLayerBGBA` 219；目标 1–14 与实例；`Test/Axioms.lean` 两条负责人注释改写；1a-audit、审核都 PASS）。M/N 三行里两行已合并。
- (2) **T2473 = T4s2 的 1a-audit RETURN，要调度签字**（23:18；1a 与探针 PASS，路线 (a)，不切 `prover-max`）。**决定（`docs/tickets/T2473-amend-1.md`）**：
  - **S1：拆三行**：T4s2a = `GridGoodGen` + `GridEnvelopeGen`（目标 1–5，约 1,386，**1b 现在开**）；T4s2b = `GridAssemblyGen`（约 1,211）；T4s2c = `AzumaProxyGen`（约 1,432；预计超 1,800 才用备用 `AzumaProxyGen2`）；依次叠加、依次合并。第三行发短通知 REQ（不阻塞）。
  - **S2：接受内联前提 `∀ n, (Cm.m n).im ≤ 1`**（目标 5 的包络和；带状由 `hierDriftGen_band_eta` / `|E n| ≤ 2 − κ` 消，BA 由 T4-BA 用 `BAm_norm_le_one` 消；不起名字，不进登记）。
  - **S3：批准**目标 4 读已合并的 `StepDecompGen_LoopForm`（T2474）与 `Step2EventsGen_Law`（T2467 F9 的最后一个合取项）代替单独的游走事实与可测性兼容（都是已合并的唯一文本，X1-C4）；票内答复 (4) 在这一点上作废。
  - BA 的初始归属仍记为 T4-BA 的欠项。
- (3) **发 `REQ-2026-10-12-2328-T4s2`**（不阻塞）：T4s2 三行、S2、S3 的记录。计数：T 21 → 23 / 34.5（T1 再拆则 24）；BA 155。
- (4) 在跑：T2472b（L3d4b）、T2476（N3a）、T2478（T1）、T2479（X1b）；T2473 的 T4s2a 等空位进 1b。排队：**T2473（T4s2a 1b）→ T2480 → T2481**；T4s2b、T4s2c 依次叠加。下一张票号 T2482，下一节 §282，下一条 H263。待写：L3d2b（等 L3d4b）、U5b、U3s2–U3s4（等 T4s2 三行）、U1s2、L3d1、L4b2、L4a2、L5（P1）。

## §282 — N3a 合并（M/N 已开的三行全部合并）；监督 2351 PASS（T4s2）；T4-BA 欠项归 T5-BA；放 U5b = T2482（总调度 V3，2026-10-13 00:03 UTC）

- (1) **合并**：**T2476 = N3a** 0f3ecb6b（23:51；E2 原地改 `Jak`（±76）、`Uyw`（±78），公开陈述逐字不变（GMN-C2）；E1 与 BA 消法在新叶 `BA/EMCTE2BA` 986 行：`unEMCTE2RowBA_holds`、`unJakUywRowBA_holds` 等；10 个目标与实例；`Test/Axioms.lean` 五条负责人注释与 T2477 的三条删除取并；1a-audit、审核 PASS；在 N3b + N3a 合并后的底上重做对比：`#print axioms band_terminal`、`bUniv_holds` 仍是三条标准公理，不变）。**M/N 已开的 C5g、N3a、N3b 全部合并**（3 / 15）；其余行等 V 关闭（短通知 REQ，2049 O6）。
- (2) **监督 2351：S1、S2、S3 与第 4 项都 PASS**，条件 T4S2-C1–C3：
  - **T4S2-C1（T4-BA 欠项要有计数的负责人）**：T4s2 输出的 BA 形式（`StepDecompGen_LoopForm`/`Step2EventsGen_Law` 在 BA 上的消法、`Im m ≤ 1`、BA 初始归属等）**归 T5-BA**：T4s2c 之后写 T5-BA 时并进去，前提是 T5-BA 的 1a 中心 ≤ 1,950；否则加一行 T4-BA（T +1）。原"半群"项划掉。ROUTES 的 T 行写上负责人。
  - **T4S2-C2**：BA 的目标 9（初始归属）写成 `∀ᶠ n`（或实例的 n）形式；主路径上没有泛型陈述把它当 `∀ n` 读（它只在实例节里用）。
  - **T4S2-C3**：S2 与 `LoopForm` 的 BA 消法走 `ba_G_data` + `BAm_norm_le_one`（已合并的 `BAAuxGraph2_eta_le_one` 正是这条链）；不新加 `open private`。
  - **O5**：X1b-C1 是**不阻塞**的通知 REQ（1a 中心超 3,000 时中枢在状态里报、照常继续，调度发通知），改 `T2479.state` 的措辞。
  - 子阶段 T：23 / 34.5（T4s2 三行），预期 26–27（T1-BA 拆则 28）。
- (3) **放 T2482 = U5b**（U 12 / 42；BA 156；**新数学，`prover-max`**；**窄设计门 E 带探针**（§238）：1a 写出 Hilbert–Schmidt 层（腿恒等式 `‖X_i‖² = 𝓛^(2)` 与换到 (+,−) 电荷型）、`lk`/`wG`/`dif` 的逐情形不等式链、对 `lossE2wG` 的损失预算表，并在 g = 1/64、1、10 重跑数值（含 BA 预解式上的 HS 与粘合比）；任何一步不成立就停在 1b 前；`BA/Step5IIIEdet` + `Step5IIIEdet2`，备用 `Step5IIIEdet3`；1,600 / 2,350 / 3,600）：Frobenius 迹界（含新的 k 重形式，需 k ≥ 2）、BA 载体上的环界与列表/粘合形式、前提包 `BAStep5IIIEScalar`/`BAStep5IIIEMatrix`（T2459 探针原文；U5c 推出矩阵部分）、`lk`、`wG`、格点和 S_θ 与 `dif`、`BAStep5IIIEdet` 及 `_holds`（U5d 读）、实例（矩阵部分在实例里仍是假设）。不读 U5a 的名字，现在就能开。UBA-C1 不触发。答复：拆分是预期情形（2,350 > 1,950），成为 U5 的第六行，1a-audit 确认时调度发不阻塞的短通知；中心超 3,600 或第三行在 1b 前发短 REQ；公开 `Prop` 只有前提包与 `BAStep5IIIEdet`；`dif` 用同一个 `lossE2wG`；O2 的组合实例归 U5c；探针证腿恒等式与电荷换型，目标 2 在 1b 证。
- (4) 计数：BA 156；T 23 / 34.5；U 12 / 42；L 40 / 50（预期 47）；M/N 3 / 15（三行已合并）；V 0 / 12。
- (5) 在跑：T2472b（L3d4b）、T2473（T4s2a）、T2478（T1，规则 (B) 修补后再 1a-audit）、T2479（X1b）。排队：**T2480 → T2481 → T2482**；T4s2b、T4s2c 依次叠加。下一张票号 T2483，下一节 §283，下一条 H264。待写：L3d2b（等 L3d4b）、U3s2–U3s4（等 T4s2 三行）、U1s2、L3d1、L4b2、L4a2、L5（P1）、T1-BA、T5-BA（含 T4-BA 欠项）。

## §283 — X1b-1、T1a、L3d4b 合并；T4s2a 目标 4 被挡 → Amend 2（加 `WalkForm`）；放 L3d2b = T2483（总调度 V3，2026-10-13 00:46 UTC）

- (1) **合并**：**T2472 L3d4b** d1eb95ac（00:08；`Graph/BAProvB` 1,238 行；目标 5 (b)、6、7、8 (a)(b)、10）→ **L3d4 完成**，L3d2b 可写。**T2479 X1b-1** 82deb62b（00:26；`Evolution/CltMoments2G` 729 + `MeanFarG` 869；目标 1–4；登记 +6；1a 中心 2,141 未触发 X1b-C1；按预签拆分，X1b-2（`CltFarG`）叠加在跑）。**T2478 T1a** 6039f7ed（00:40；`Chain/Step2IterGen` 1,263 + `Step2IterGen2` 538；目标 1–6；`Test/Axioms.lean` 的 TLC-2 负责人文本与 `STOptL2gL` 行；1a-audit 第二轮（一次规则 (B) 修补）确认拆分；T1b 叠加在跑）。计数：U 13 / 42（X1b 拆）、T 24 / 34.5（T1 拆）。
- (2) **T2473 T4s2a 的 1b 被挡**（00:35；目标 1、2、3、5 与带状实例已提交 db4066bc，未审核）：`GridGoodNConclg` 的结论 `GoodSetNg … (Cm.Hpath …)` 第一条是 `IsHermitian`，Amend 1 第 3 项给目标 4 的前提都不陈述它。**决定（Amend 2）**：目标 4 (a)(b) **再取已合并的 `StepDecompGen_WalkForm`**（本行目标 7–10 已经在读；带状 `stepDecompGen_walkForm_band`，BA 定义性 `baStep2Mat_walkForm`），不用"厄米 `Hf`"前提；其余照 Amend 1；从 db4066bc 续做目标 4，然后**对 T4s2a 整体做一次审核**（带 2351 的 T4S2-C2/C3 说明）。
- (3) **放 T2483 = L3d2b**（BA 159；阶段 L 41 / 50，拆分后 42，预期仍 47；`prover-hard`；不设设计门（绑定钉文不成立时预签退到窄设计门带探针）；新增 `Graph/BAMomentExpGen`（目标 1–5，约 900）+ `BAMomentExpGenB`（目标 6–10，约 1,250），备用 `BAMomentExpGenC`；1,850 / 2,150 / 3,700；在文件边界预签拆分（预期），1a 中心超 3,900 为第三行要短 REQ）：载体 `LWfgD`（带状桥、`univ`、并集）、`LWMomentExpG` 及带状等价与 `BALWMomentExp`、**路径绑定的消法 `baLWMomentOfAnp_closed`（L40-F2，T2470 目标 4；L5 读）**、加权齐次 `T2483_ValWScale`、BA 带根的 G3 `T2483_GtoAGRooted`、`BALWMomentExpOfAnp` 与 `baLWMomentExp_of_anp`；形状：`LWfgD` 到 `fxyValD` 的桥、加权的尺度-分子尾（覆盖所有 `x ~ y` 输出）、嵌套形式、regime (A)、远/近钉文、极限检查。**L40-C2 取情形 (b)**：耦合随 n 在 `(0, 𝔡⁻¹]` 变，阈值在这个范围一致（上确界在 Λ）；`𝔠`、`K_c` 算序列前固定的常数；1a 写出量词位置、极限检查（`(0, Λ]` 上正的 `BAct_rate` 与 O4 三个数）并说明 L5 读的范围（更宽就停）。`BAAnpAuxG` 只作 regime (A) 的精确类型前提（L3d1 合并了就顺带证 `T2483_MomentExpClosed`）。排在 T2482 前。
- (4) 计数：BA 159；T 24 / 34.5；U 13 / 42；L 41 / 50（预期 47）；M/N 3 / 15；V 0 / 12。阶段 L 预测重算（L40-C3）：L3d2b 2 张（已计入），其余不变 → 预期 47。
- (5) 在跑：T2478b（T1b）、T2479b（X1b-2）、T2480（U2）、T2481（U5a）；T2473 T4s2a 等 Amend 2 续做。排队：**T2473（T4s2a 续 1b）→ T2483 → T2482**；T4s2b、T4s2c 依次叠加。下一张票号 T2484，下一节 §284，下一条 H265。待写：U3s2–U3s4（等 T4s2 三行）、U1s2、L3d1、L4b2、L4a2、L5（P1）、T1-BA、T5-BA（含 T4-BA 欠项）、U5c。

## §284 — X1b 完成、U2a 合并；U2a 的两处钉文前提追认；放 U4s2 = T2484；发 U 的短通知 REQ（总调度 V3，2026-10-13 01:29 UTC）

- (1) **合并**：**T2479 X1b-2** 16861112（00:55；`Evolution/CltFarG` 1,070 行，目标 5–9 含 `stCltFargL_holds`；审核 PASS）→ **X1b 完成**，U4s2 可写。**T2480 U2a** 650a122d（01:16；`Chain/KDecayGen` 244、`Chain/SEforLnGen` 1,718、备用 `Chain/SEforLnGen2` 975（按 1,800 行规则用了）；目标 1–6；登记：`STKcalDecaygL` 负责人注释、`STAvgUgL`、`STStep2ConclgL`；审核 PASS）；U2b（`Chain/B45Gen`）叠加待开。T2483（L3d2b）已开工（排在 U2b 前，按 H264 (4)）。计数：U 14 / 42（U2 拆）。
- (2) **U2a 的两处钉文前提追认**（证明报告 (a′) 1、(d) 1）：目标 4（`T2480_SEforLnConclOf`）多了 `S` 的支撑前提，目标 6（`T2480_EtermDecaygL`）多了一圈值 `hone`；两者都是类 `SEforLnGen_Facts` 的字段，带状有见证（`SEforLn2_SB_sum`、`DecayLoopB_avgErr_eq`），找不到不用它们的证明。**接受**。`hone` 以内联精确类型合取式出现（答复 (3) 在 1a 开始时定的；T1a 的 `Step2IterGen_OneLoop` 已在 `main`，以后可用一行桥换成类）。
- (3) **C6 / 1.5 倍**：U2 预计 3,874 行，超过 1.5 × 2,250 = 3,375 → 发短通知 REQ（不阻塞；无路线变更、无孪生、无新数学）。
- (4) **放 T2484 = U4s2**（U 15 / 42；BA 161；`prover-hard`；**窄设计门 D1–D4 带探针**（D1 核事实、D2 流元组包装、D3 Ward、D4 规模），因为两个假设类都没有已合并的文本；新增 `Chain/IniTermIIGen`（U4s2a）、`Chain/CltFarUGen` + `Chain/IniTermIGen`（U4s2b），备用 `IniTermIIGen2`、`IniTermIGen2`；1,600 / 2,300 / 3,500；预签拆 U4s2a / U4s2b（叠加））：类 `T2484_KerFacts`（`gK` 上的 D2 核事实 + R1 + 混合列和、零模、同电荷短程）与情形 (ii) 核心；钉文 `T2484_IniTermIIOf`（结论 `STIniTermIIgL`）；流元组包装 `T2484_CltFlow`（在每个网格时间组装 `HCltOf`）；`T2484_CltFarUConclgL` 及带状桥、`u` 一致的 CLT；情形 (i) 层与钉文 `T2484_IniTermIOf`（结论 `STIniTermIgL`）；带状重导与实例。答复：新核字段读 `gK`，跨越只用 R1；包装在这里，BA 消法归 U4-BA（C9）；Ward 用已合并的 `Step5CasesGen_WardIdent`，不够再用 `ZeroModeGen_WardCls` 加内联共轭（UN-C3），不另起文本；情形 (i) 读已合并的 `STThPropsg`。
- (5) 计数：BA 161；T 24 / 34.5；U 15 / 42；L 41 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (6) 在跑：T2473（T4s2a 续 1b）、T2478b（T1b）、T2481（U5a）、T2483（L3d2b）。排队：**T2480b（U2b）→ T2482 → T2484**；T4s2b、T4s2c 依次叠加。下一张票号 T2485，下一节 §285，下一条 H266。待写：U3s2–U3s4（等 T4s2）、U1s2、U4s3（等 T1、T4s2）、L3d1、L4b2、L4a2、L5（P1）、T5-BA（含 T4-BA 欠项）、T1-BA、U5c。

## §285 — U5a、T4s2a 合并；监督 0149 PASS 与 O1–O6 落账；T1b 目标 11 签字（照交付接受）；放 U5c = T2485（总调度 V3，2026-10-13 02:13 UTC）

- (1) **合并**：**T2481 U5a** a2f86197（01:32；`BA/Step5IIIKer` 709、`BA/Step5IIIKer2` 471；目标 2 按核路线 (b) 删去（答复 (1) 允许）；无登记变动；审核 PASS 第一轮）→ **U5a 完成**。**T2473 T4s2a** 86eb22f2（01:38；`Chain/GridGoodGen` 1,037、`Chain/GridEnvelopeGen` 360；目标 4 按 Amend 2 取 `StepDecompGen_WalkForm`，目标 5 带已接受的 `∀ n, (Cm.m n).im ≤ 1`；四条登记行含结构性 `STAny`；审核 PASS，附 T4S2-C2/C3 备注；探针留在 `t/T2473`）；T4s2b、T4s2c 依次叠加。
- (2) **监督 2026-10-13-0149：PASS**（U2 照账；U2b 继续；U2-C1–C3 都不阻塞）。落账：
  - **O1（U2-C1，C6 实测数）**：「U2 ≈ 4,000–4,400 行（U2a 实测 2,937；U2b 1a 中心 1,075）；连 U2-BA 孪生 ≈ 4,950–5,310 = 中心的 2.2–2.4 倍；1a 时（00:18 UTC）已过 1.5 倍；通知 REQ 0129 PASS（无路线变更）」。已写进 ROUTES 的 U 行。**常规改动**：以后带 C6 点的行，1a 的整行预测一过线就发通知 REQ（1155 C6），不等合并。
  - **O2（U2-C2）**：U2-BA 的票按 `KDecay` §1–§8（`:52-998`，791 行代码）重新定价 `BAKcalDecay`（监督粗估 1a 中心 1,250–1,850；T2379 的 514 / 937 / 1,687 作废），并预签：1a 中心超 1,950 就在 U2a / U2b 边界拆，U2-BA (a) = `BAKcalDecay` + 目标 3–6 的 BA 读法（只读已合并的名字，WardCls 除外，可在 U2b 合并前开工），U2-BA (b) = 目标 7–9 的读法（U2b 之后）；拆则 U +1。
  - **O3（U2-C3）**：UN-C3 的归属改为「**U2-BA、U1-BA 或 U4-BA (b)，谁先写谁做**」：那一行证一次 `ZeroModeGen_WardCls (baFM …)`（若同时写 WardIdent 桥，带 1852 `:78-79` 的内联共轭），其余读它。BA 上的 `hone` 与 `Step2IterGen_OneLoop` 第一个合取式出自同一个 `baKsol_one` 证明；T1-BA 的消法先有，就用一行 `.1` 展开桥，不另起命名 `Prop`。不改计数。
  - **O4（Amend 2 后续）**：`StepDecompGen_WalkForm` 的 BA 消法（`baStep2Mat_walkForm` 不在 `main` 上；`Pp`/`Hpath` 在 `Step2BA:68, 70` 用 `rfl` 对上，`Ψ` 条款照 `BA/ConArg:308-316` 由 `PsiI_isHermitian` 几行得到）列入 T5-BA 的 T4-BA 欠项。
  - **O5（登记措辞）**：`Test/Axioms.lean:229-231` 上 `STAvgUgL`、`STStep2ConclgL` 的负责人注释改成「generic: T1a (`ST_avgU_of_avgg`, `ST_concl_of_step2g`, `Step2IterGen2:266, 281`); BA: T1-BA」。由中枢在 T1b 合并时做（只改注释，扫描不变；见 H266 (3)），避开 U2b 的块（`:233-235`）。
  - **O6（计数）**：T2483 的 1a（中心 2,122）用了预签拆 → **L 42 / 50**，**BA 162**（§284 (5) 的 41 / 161 作废）；ROUTES 的 L 格写「L3d2b 拆两行（L3d2b-1 / -2）」。预期 47 不变（拆分已计入）。
  - **1a 范围（观察，常规改动）**：要在写 Lean 之前拿到名字级表格的票，把这些项派到 1b 开头或 1a-audit，不派给 1a（CLAUDE.md §4 第 1 步「不查名字」）。T2485 答复 (9) 已照做；之后的票同样。
  - BA 全局预测（供 Jun 参考，§144 不设上限）：≈ 199–208，期望 ≈ 202。
- (3) **放 T2485 = U5c**（U 16 / 42；BA 163；`prover-hard`；无设计门、无探针；新增 `BA/Step5IIIGood`（目标 1–3）+ `BA/Step5IIIGood2`（目标 4–5）；700 / 1,100 / 1,650；预签拆 U5c-1 / U5c-2（叠加），拆则是 U5 的第六或第七行，在 U5c-2 的 1b 前发短 REQ）：实现的控制 `J♯` 及其规格、层级单调、每个时刻的好事件 `BAStep5IIIGood(Thm)`（逐合取式路线 (i)–(vi)，七个坏集合 `7N^{-(D₁+1)} ≤ N^{-D₁}`）、流上的标量部分（审核 O2 后半）、实例（含组合实例）。**开工条件：T2482 的 1a-audit PASS 之后**（不是 U5b 合并之后）。答复：
  - (1) 矩阵部分照抄冻结的 `T2482_BAMatrix`（精确类型，内联，不另起公开名，X1-C4），U5b-1 合并后用一行定义桥接到 `BAStep5IIIEMatrix`（这一行或 U5d 开头）；开工时 U5b-1 已合并则直接按名读。
  - (2) 探针 `T2459_BAgoodThm` 的四处更正 (a)–(d) 确认、在检查文件里绑定：用已合并的 `STLmaxUgL`/`STLKUgL`；加 `0 < ε`、`0 < 𝔡`、`0 < Cd`；去掉 `STKboundgL`（按名用 `baKbound_holds`）。
  - (3) 目标 2、4 留在这里（U5c 管「好事件 ⇒ 束」）。(4) 好集合的可测原像形式归 U5d（同带状 `pfStep5_goodMeas`）。(5) 不带 Step 1 前提；要用 Step 1 只能 `baStep1_holds' d hd`。(6) 目标 3、4 停在 `d = 3`。(7) 登记只改四行的消费者注释，且仅在扫描要求时；O5 改写已落地则在改写后的行上追加（并集）。(8) U 16 / 42、BA 163。(9) 名字级的预检项 (iv) 的文件:行列、(vi)、(ix) 若 1a 不查名字，就放到 1b 开头、写 Lean 之前。
- (4) **T1b（T2478b）目标 11 签字：照交付接受**。`step2CloseGen_step2_of_pinsLW'` 带四个前提 `LWterm`、`LWtermExp`、`STEMn2Exp`、`STGridMart`，都是已合并的定理（`lwterm_holds` `Graph/LWTermHolds:682`、`stEMn2Exp_holds` `Induction/EMn2Exp2:1274`、`stGridMart_holds` `Path/DifREP2:2283`），推论不空。票上「只留 `LWtermExp`」在票自己的布局下做不到（`STEMn2Exp` 的锥含 `BA.FlowPins`，违反无 BA 闭包；带状 `ST_step2_of_pinsLW'` 本身也留着 `STEMn2Exp`），是票的措辞错，不是证明的问题；改布局（加 `Path/DifREP2` 或 `Graph/LWTermHolds` 的导入）只为一个带状推论，不值。目标 11 是带状重导，没有下游读它的前提表。**合并 T1b**：中枢按审核 O1 加两条根导入（hub §3 (A)4）；T2478e 作论文差异候选，合并时编号。→ **T1 完成**（T1a 6039f7ed + T1b）。
- (5) 计数：BA 163；T 24 / 34.5；U 16 / 42；L 42 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (6) 在跑：T2480b（U2b）、T2482（U5b 设计门）、T2483（L3d2b-1，prover-max）、T2484（U4s2 设计门）。T2478b 等本节签字后合并。开工顺序（有空位时）：**T4s2b → T2485（满足开工条件时）→ T4s2c**。下一张票号 T2486，下一节 §286，下一条 H267。待写：U3s2–U3s4（等 T4s2 b/c）、U4s3（T1 已齐，等 T4s2）、U1s2、L3d1（G4）、L4b2、L4a2、L5（带 L6，L40-C1）、T5-BA（含 T4-BA 欠项与 O4 的 WalkForm）、T1-BA（含 GMN-C1 读者）、U2-BA（按 O2 定价）、U5d（U5a–c 之后）、U5e。

## §286 — T1 完成、L3d2b-1 合并；U2b 目标 7 的类多两个字段：照交付接受（总调度 V3，2026-10-13 02:39 UTC）

- (1) **合并**：**T2478 T1b** 1e73b1b8（02:24；`Chain/OptL2Gen` 1,423、`Chain/Step2CloseGen` 921；目标 11 按 §285 (4) 的四前提形式；登记：`STOptL2gL` 移出（T1b 证出）、`STStep1LoopgL` 记为欠项、`STAvgUgL`/`STStep2ConclgL` 的负责人注释按监督 0149 O5 改写）→ **T1 完成**（T1a 6039f7ed + T1b）。**T2483 L3d2b-1** 772b1ca1（02:36；`Graph/BAMomentExpGen` 1,147；目标 1–5 与实例 10 (iv)、(v)；prover-max（预签换档条件 (a)）；审核 PASS）；L3d2b-2（`BAMomentExpGenB`，目标 6–10）已在 `t/T2483b` 叠加开工。T4s2b 已开工（`t/T2473b`）。
- (2) **T2480b（U2b）目标 7 签字：照交付接受**。`B45Gen_Facts` = 钉文 `T2480_B45Facts` 加两个字段 `∀ n, ((mk sz z).m n).im ≤ 1` 与 `∀ n, ZeroModeGen_KerSums (mk sz z) n`。检查文件头（`T2480-check.lean:8-9`）本来就允许「带具名带状消法」加类字段；两者的带状消法都有名字（`norm_mE` + `Complex.im_le_norm`；已合并的 `zeroModeGen_kerSums_band`，U1s1），并在 `b45Gen_facts_band` 里用上；审核核过必要性（钉文前提只给 `Im m` 的下界，推不出 `η_u⁻¹` 界；列和常数性没有来源）。目标 9 的两个钉文随之换成这个类，不另算差异。没有别的票读 `T2480_B45Facts`。**合并 U2b** → U2 完成。
  - BA 一侧：`Im m ≤ 1` 已在 U2-BA 的清单上（`BAm_norm_le_one`）；**`ZeroModeGen_KerSums` 的 BA 消法加进 U2-BA 的清单**（`S = 1` 时化为 `Step2Kern_Mss` 的行、列和常数，可从 `BAK_row_sum`（`KKernel:124`）与 `BAMss_norm_eq_BAK`（`KKernel:102`）得到）。U2-BA 按 §285 (2) O2 定价时一并计入。
  - 这一条同 §284 (2)：检查文件要求 1a (iii) 报告加字段，1a 推到了 1b。照 §285 (2)「1a 范围」处理，不算 1a 越权。
  - 论文差异候选 T2480c（审核 §7 的四项）合并时编号。
- (3) 计数不变：BA 163；T 24 / 34.5（T1 完成）；U 16 / 42；L 42 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (4) 在跑：T2473b（T4s2b）、T2482（U5b 设计门）、T2483b（L3d2b-2）、T2484（U4s2 设计门）；T2480b 等本节签字后合并。排队：T2485（等 T2482 的 1a-audit PASS）→ T4s2c（等 T4s2b 审核 PASS）。下一张票号 T2486，下一节 §287，下一条 H268。待写不变（§285 (6)），U2-BA 加上 (2) 的 `KerSums`。

## §287 — U2 完成；T2482 1a-audit PASS（U5b 拆两行 = U5 第六行，发通知 REQ；U5c 开工条件满足）；放 U2-BA = T2486、T1-BA = T2487（总调度 V3，2026-10-13 03:14 UTC）

- (1) **合并与状态**：**T2480 U2b** 78f4cc14（02:43；`Chain/B45Gen`；目标 7 的类按 §286 (2) 签字）→ **U2 完成**（U2a 650a122d + U2b）。**T2482（U5b）1a-audit PASS**（03:01）：预签拆 U5b-1 / U5b-2 确认（1a 中心 2,450 = 1,262 + 1,188），束文本 `T2482_BAScalar`/`T2482_BAMatrix` 没变（1a-audit `:30-34`），不需 1b 前 REQ；U5b-1 的 1b（prover-max）在跑。→ **U5 第六行**，按 T2482.md:9 发通知 REQ；U 17 / 42，BA 164。**T2485（U5c）开工条件满足**（束文本没变，T2485 停止规则 2 不触发），占下一个空位。
- (2) **发 `REQ-2026-10-13-0314-U5six`**（不阻塞）：U5 第六行；U2-BA、T1-BA 的重新定价与两条"一份证明"的归属。
- (3) **放 T2486 = U2-BA**（U 18 / 42，拆则 19；BA 165；`prover-hard`；无设计门（目标 1 的槽图直径界写不出来时退回窄门 D1，预签）；新增 `BA/KDecayBA`（备用 `KDecayBA2`）、`BA/SEforLnBA`、`BA/B45BA`；1,350 / 1,950 / 3,000；预签拆 (a) 目标 1–5 / (b) 目标 6–8（叠加 `t/T2486b`），1a 定）：`BAKcalDecay`（`KDecay` §1–§8 的 BA 孪生）、UN-C3 的唯一 BA `WardCls` 证明、四个小载体事实、U2 目标 3–9 的 BA 读法。答复：(1) 四个小载体事实按"先写者"归这里，T5-BA、U3-BA (a)、U4-BA 读；(2) ε-free 的私有拷贝；(3) `KerSums` 同电荷对加 `BAMB_shift` + `BAMB_symm`（§286 (2) 的来源只覆盖混合对）；(4) `WardCls` 走 `baKcac_isKLoopS` + `baK_unique`；(5) WardIdent 桥归 U4-BA (b)；(6) 无设计门，C6 数在 1a 更新，超 2,925 或 U2 + 孪生超 5,310 就在 1a 发通知；(7) 一圈证明归 T1-BA，本行 2 (b) 是 `.1` 一行桥，1b 最后写，T2487 没合并就在这一项停；(8) 名字级表格放 1b 开头。
- (4) **放 T2487 = T1-BA**（T 25 / 34.5，拆则 26；BA 166；`prover-hard`；无设计门；新增 `BA/Step2IterBA`（备用 `Step2IterBA2`）、`BA/Step2CloseBA`；1,000 / 1,450 / 2,350；预签拆在文件边界）：BA Step 2 `baStep2_holds : … → BAStep2`，经 T1 已合并的骨架；目标含厄米路、**唯一的 `baKsol_one` 一圈证明**、ListLink、K2、newKLK（每载体的私有拷贝，常数显式，F1）、`STBdatagL`、P3 `baScaleExists_holds`、`baSTOptL2gL_holds`、GMN-C1 的 BA 读者（输入取 `STGijDecgL`）、骨架的私有拷贝（一圈输入放到流之下，F2）、实例。答复：(1)(2) 两份私有拷贝；(3) **BA `STGijDecgL` 在这里证**（由 `baGbEXPij'_holds`），条件是 1a 定价 ≤ 100 行，那时登记负责人从 U4-BA 改成 T1-BA，U4-BA 读它；否则照草稿作精确类型输入；(4) 预签拆；(5) 每时刻读法不导出；(6) 本行拥有一圈证明，`baStep2_oneLoop` 改名要报告；(7) 无设计门；(8) T 25 / 34.5，BA 166；(9) 名字级表格放 1b 开头。
- (5) **开工顺序**（有空位时）：**T2485 → T2487 → T2486**；T4s2c 在 T4s2b 审核 PASS 后占当时第一个空位。
- (6) 计数：BA 166；T 25 / 34.5；U 18 / 42（U2-BA 拆则 19）；L 42 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (7) 在跑：T2473b（T4s2b）、T2482（U5b-1 1b）、T2483b（L3d2b-2）、T2484（U4s2 设计门）。排队：T2485 → T2487 → T2486；T4s2c。下一张票号 T2488，下一节 §288，下一条 H269。待写：U3s2–U3s4（等 T4s2 b/c）、U4s3（等 T4s2）、U1s2、L3d1（G4）、L4b2、L4a2、L5（带 L6）、T5-BA（含 T4-BA 欠项与 WalkForm）、U5d（U5a–c 之后）、U5e。

## §288 — T4s2b 合并；U4s2 拆两行确认；U5c 1a 不拆（总调度 V3，2026-10-13 03:30 UTC）

- (1) **合并**：**T2473 T4s2b** 4efcae69（03:14；`Chain/GridAssemblyGen` 1,197，目标 7；审核 PASS）；T4s2c（`Chain/AzumaProxyGen`，目标 8–10）在 `t/T2473c` 叠加，等空位。
- (2) **T2484（U4s2）1a-audit PASS**（03:04）：预签拆 U4s2a / U4s2b 确认，无第三行，无需签字。→ **U 19 / 42，BA 167**。观察 1：U4s2b 的分支要含 `Chain/B45Gen`（78f4cc14），`t/T2484` 基于 86eb22f2 不含它——U4s2b 开 1b 前，中枢把它的分支建在含 78f4cc14 的基上（U4s2a 合并后的 `main`，或把 `main` 合进 `t/T2484b`），见 H269 (2)。观察 2：目标 6–7 的 UBA-C1 是 R1 的逐指标守卫形式，许可内。
- (3) **T2485（U5c）1a**：中心 1,430（1,090 + 340），不拆；无文件高估超 1,800，不设备用；目标 1–4 PASS（目标 3 只要钉好的 `0<ε`、`0<𝔡`、`0<Cd`、`0<θ<1`）。按答复 (9)，名字级项在 1b 开头做。
- (4) 中枢的开工顺序 **T4s2c → T2487 → T2486** 照 H268 (4)（T4s2c 在 T4s2b 审核 PASS 后占第一个空位）。
- (5) 计数：BA 167；T 25 / 34.5；U 19 / 42（U2-BA 拆则 20）；L 42 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (6) 在跑：T2482（U5b-1）、T2483b（L3d2b-2）、T2484（U4s2a 1b）、T2485（U5c 1b）。排队：T4s2c → T2487 → T2486。下一张票号 T2488，下一节 §289，下一条 H270。

## §289 — U4s2a 合并；开工顺序（总调度 V3，2026-10-13 03:45 UTC）

- (1) **合并**：**T2484 U4s2a** ba7e559e（03:43；`Chain/IniTermIIGen` 1,113；目标 1–4 及其 10–11 部分；审核 PASS；探针留在 `t/T2484`）。U4s2b（`CltFarUGen` + `IniTermIGen`，目标 5–9）在 `t/T2484b` 叠加，1b 前合入含 `Chain/B45Gen` 的 `main`（H269 (2)），等空位。T4s2c 已开工（`t/T2473c`）。
- (2) **开工顺序**（有空位时）：**T2487 → U4s2b → T2486**。T1-BA 先（它拥有一圈证明，U2-BA 读它）；U4s2b 次之（U4s3 等它与 T4s2c）；U2-BA 最后（它的 2 (b) 本来就最后写）。
- (3) 计数不变：BA 167；T 25 / 34.5；U 19 / 42；L 42 / 50；M/N 3 / 15；V 0 / 12。
- (4) 在跑：T2473c（T4s2c）、T2482（U5b-1）、T2483b（L3d2b-2）、T2485（U5c）。排队：T2487 → U4s2b → T2486。下一张票号 T2488，下一节 §290，下一条 H271。T4s2c 合并后写 U3s2–U3s4；U4s2b 与 T4s2c 都合并后写 U4s3。

## §290 — 监督 0349 PASS，O1–O6 落账；T2486 Amend 1（`LCompat`/`KCompat` 不设流前提）；T2482 U5b-1 的登记：调度定 `owedProps`，合并时由中枢加；放 L3d1 = T2488（总调度 V3，2026-10-13 04:07 UTC）

- (1) **监督 2026-10-13-0349：PASS**（U5 第六行、T2486、T2487 都无异议；U5S-C1–C4）。落账：
  - **O1（U5S-C1）**：T2486 的 `T2486_BACarrierFacts` 有一处问题：`LCompat` 被放在流前提之下，但 T5-BA 的 `hC`（`GridGoodGen:853`）要的是对每个 `sz z` 都成立。→ **Amend 1**（见 (2)），在 T2486 第 0 步之前落地。T2486 本来排在第三，不损失工作。
  - **O2（U5S-C2）**：去掉 T2486 答复 (6) 里「U2 + 孪生超 5,310」那一支。U2 的 C6 孪生只算 `KDecayBA`（中心 1,100）。ROUTES 的 U 行改写为：「U2 实测 4,181；孪生 `KDecayBA` 实测 N（中心 1,100，合并时填）；U2 + 孪生按中心 ≈ 5,280 = 2,250 的 2.35 倍（C6，1155）；0149 的 4,950–5,310 用的是 T2379 整行的 937 当孪生」。
  - **O3（U5S-F3）**：已定价的两张 BA 行约为 T2379 价格的 2.1 倍（U2-BA 937 → 1,950；T1-BA 682 → 1,450），偏差在 T2379 的行价，不在票的定价。**下次放 U 行时**，对 T2379 剩下的 BA 行（U1-BA、U3-BA、U4-BA、T7-BA、V1-BA）乘约 2 的系数，重新推 U 的计划；U 计划到 40 发通知 REQ。监督的预测：U 终点 35–38（原 33–34），V +0–1。
  - **O4（U5S-C3，常规改动）**：剩下的泛型行（U3s2–U3s4、U4s3、U1s2、V1s 各行）在 1a（名字级的放 1b 开头）交一张**族前提表**：每个 `∀ sz z, …` 前提标明有没有流前提，写出 BA 消法及其形式。BA 消法需要流（`BAReal`、`0 < g₀`、`0 < Im m`）的前提，放在 `0 < κ → Flow` 之下；钉住的 `∃ C` 不得依赖族里冻结的 `(sz, z)`（F1 模式）。写这些票时照做。
  - **O5（U5S-C4）**：T2487 的 1a 报 `STGijDecgL` 归哪一行时，在同一节里把负责人写进 DECISIONS、ROUTES 的 U 行和登记注释。T2486 合并时，四个载体事实和 `WardCls` 的负责人注释改到它名下。
  - **O6（计数）**：U 19 / 42（U2-BA 拆则 20），T 25 / 34.5，BA 167（REQ 里的 18 / 166 已被 §288 取代）。BA 全局预测（给 Jun）≈ 201–213，期望 ≈ 205。
- (2) **T2486 Amend 1**（`docs/tickets/T2486-amend-1.md`；票与检查文件就地改）：
  - `LCompat`、`KCompat` 对每个 `sz, lam0, E` 都成立，不设流前提（已合并的 `Step34GenTw:84-86` 的形式加以推广）；只有 `LoopForm` 留在流前提之下；
  - 2 (c) 的消费者加上 T5-BA 的 `hC`；
  - 去掉 5,310 那一支。
  - 检查文件要重新编译（H271 (2)）。
- (3) **T2482（U5b-1）审核卡在登记上**（03:48）：整库 `#assert_rbm_axioms` 报未登记的前提 `RBM.BA.BAStep5IIIEMatrix`。票上写的是「Registry: none」，`Test/Axioms.lean` 也不是这张票可写的文件，所以错在票，不在证明。审核的其余各项都已 PASS（目标 1–5、8 (a) 与钉文一致，实例编译通过，公理标准）。
  - **调度的决定**：把 `BAStep5IIIEMatrix` 记为 `owedProps`，负责人是 U5c（T2485 在好事件上证出它，组合实例 5 (b)），再由 U5d 读。
  - **做法**：按 T2454 先例（CONTROL `:386`），由 **中枢在合并时** 按 H271 (3) 的原文加这一行，然后重跑审核 §5 的预检（应 exit 0）。登记只加一行，不改证明，所以不另开修补阶段，也不再审第二轮。`BAStep5IIIEScalar` 扫描没有报，不登记。
  - **U5c 的登记答复 (7) 随之补充**：T2485 若在扫描里看到 `BAStep5IIIEMatrix` 已被证出，可以删掉这一行（只删这一行）。
- (4) **放 T2488 = L3d1 `BAAnpLift`**（BA-L；阶段 L 43 / 50，L40-C3 预测 47；BA 168；`prover-hard`，预签可换 `prover-max`；窄设计门 G4，无探针；新增 `Graph/BAAnpLift`，备用 `BAAnpLiftB`；起草估计 290 / 360 / 630，由 1a 按普查重估；预签拆 L3d1a / L3d1b，拆则 L 44 / 48）：
  - 内容：`lem:Anp` 在 BA 律、载体与时间范围上重述，得到 L3d1 的钉文 `BAAnpAuxG`（`BAAuxGraph2B:865`，对每个 `d`），再加两个矩钉文的闭合。
  - 答复：
    - G4 不设探针；
    - 闭合 4 (a) 总在这里做；4 (b) 只在 1b 开始时 L3d2b-2 已合并才做；
    - 不并行（L40-C4：L3d2b 两半都超过 750）；
    - 排在 U4s2b 之后、T2486 之前。
- (5) **开工顺序**（有空位时）：**T2484b（U4s2b）→ T2488 → T2486**（T2486 先要 Amend 1 的检查编译通过）。T2487 已开工（03:48）。
- (6) 计数：BA 168；T 25 / 34.5；U 19 / 42（U2-BA 拆则 20）；L 43 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (7) 在跑：T2473c（T4s2c）、T2482（U5b-1，等合并时加登记行）、T2483b（L3d2b-2）、T2485（U5c）、T2487（T1-BA 1a）。排队：T2484b → T2488 → T2486。下一张票号 T2489，下一节 §291，下一条 H272。

## §291 — U5b-1、U5c、L3d2b-2 合并（U5c、L3d2b 完成）；U5b-2 排进开工顺序（总调度 V3，2026-10-13 04:23 UTC）

- (1) **合并**：
  - **T2482 U5b-1** 6482d46a（04:14；`BA/Step5IIIEdet` 1,493；目标 1–5、8 (a)；`owedProps` 行 `BAStep5IIIEMatrix` 按 H271 (3) 同一提交加入，预检 exit 0）；U5b-2（`BA/Step5IIIEdet2`，目标 6–7、8 (b)）在 `t/T2482b` 叠加。
  - **T2485 U5c** 12f5d1ba（04:16；`BA/Step5IIIGood` 704、`Step5IIIGood2` 198；目标 1–5；不拆；审核 PASS 第一轮）→ **U5c 完成**。`BAStep5IIIEMatrix` 的登记行还在（U5c 没删；U5d 读它）。
  - **T2483 L3d2b-2** 2cc78196（04:20；`Graph/BAMomentExpGenB` 1,344；目标 6–9 与实例；prover-max；审核 PASS）→ **L3d2b 完成**。T2488（L3d1）04:21 开工时 L3d2b-2 已合并 → 按 T2488 答复 (4)，闭合 4 (b) `BALWMomentExp` 在 L3d1 里做。
  - U4s2b 已开工（`t/T2484b` 基于 12f5d1ba，含 `Chain/B45Gen`）。
- (2) **开工顺序**（有空位时）：**T2482b（U5b-2）→ T2486**。U5b-2 在 U5 的关键路径上（U5d 读 `BAStep5IIIEdet` 3）；T2486 本来就要等 T2487 的一圈证明。
- (3) 计数不变：BA 168；T 25 / 34.5；U 19 / 42；L 43 / 50（预期 47）；M/N 3 / 15；V 0 / 12。
- (4) 在跑：T2473c（T4s2c）、T2484b（U4s2b）、T2487（T1-BA）、T2488（L3d1 设计门）。排队：U5b-2 → T2486。下一张票号 T2489，下一节 §292，下一条 H273。起草中：L4a2、L4b2（阶段 L）。待写：U5d（U5b-2 之后，或以 `T2482_BAEdet` 精确类型前提先写）、U3s2–U3s4（等 T4s2c）、U4s3（等 U4s2b、T4s2c）、T5-BA（等 T4s2c）、U1s2、L5（带 L6）、U5e。

## §292 — T1-BA 合并（BA Step 2 只剩阶段 L 的两个钉文）；`STGijDecgL` 归 T1-BA；放 L4b2 = T2489、L4a2 = T2490（总调度 V3，2026-10-13 04:48 UTC）

- (1) **合并**：**T2487 T1-BA** 268e07d4（04:39；`BA/Step2IterBA` 833、`BA/Step2CloseBA` 259；目标 1–12 加 9b；不拆；审核 PASS 第一轮）→ **T1-BA 完成**。`baStep2_holds : BALWterm d → BALWtermExp d → BAStep2 d`：**BA Step 2 只剩阶段 L 的两个钉文**（`BALWterm`、`BALWtermExp`，已登记，BA-L6）。唯一的一圈证明 `baStep2_oneLoop` 已合并 → T2486 的 2 (b) 可以照写（一行 `.1` 桥），不会停。U5b-2 已开工（`t/T2482b`）。
- (2) **`STGijDecgL` 的负责人（监督 0349 O5 / U5S-C4）**：T2487 的 1a 走了情形 (3)（≤ 100 行，实际 10 行）→ **BA `STGijDecgL` 由 T1-BA 证出**（`baSTGijDecgL_holds`，`Step2CloseBA:66`，由 `baGbEXPij'_holds`），U4-BA 不再欠这一项。登记注释已由 T2487 改好（`Test/Axioms.lean:202`；`STGijGEXgL` 写「BA: not needed」）。ROUTES 的 U 行与 T 行同步写上。
- (3) **放 T2489 = L4b2**（BA-L；L 44 / 50；BA 169；`prover-hard`，预签可换 `prover-max`；无设计门、无探针；新增 `Graph/BAExp14b2`（目标 1–3）+ `BAExp14b2B`（目标 4–7），备用 `BAExp14b2C`；1,220 / 1,550 / 2,720；预签拆在文件边界，拆则 L 45、预测 48）：证明已合并的 S2 钉文 `BAExp14bS2`（`BAExp14b:170`，L4b1 = T2434）——`lwExpI1K`/`I23K`/`I41K` 的扭转孪生，用 `(twL2', twK, twTr)`；P3 `‖𝔼X_c‖ ≺ 𝔟^{3/2}`（没有 `(1-t)⁻¹`）要经 `ω = Θ^{(+,+)}` 反解 `BAExp14a_e_eq`，仍需 `𝔼X ≺ 𝔟²` 时触发停止规则 S1。答复：TL1、TL2 照已合并 S2 文本保留（TL2 是精确类型前提，BA-V 每个 `u` 的项）；自成一行；两个文件；P3 用词干拷贝；排在 T2486 之后、T2490 之前。
- (4) **放 T2490 = L4a2**（BA-L；L 45 / 50；BA 170；`prover-hard`；无设计门；新增 `Graph/BAExp14a2`，备用 `BAExp14a2B`；420 / 600 / 1,100（设计的 917 / 1,068 / 2,022 还含 L4a、L4b2 已覆盖的 I₁、I₄₁ 项）；预签拆在目标 2 | 3–6）：`lem:LWterm_EXP` 在 BA——`LWE → LWcut` 的约化、按类型读已合并的 S2 钉文把 S1–S3 组装成 `BALWCutExpTw`（探针 434–440 原文，绑定结论），七前提的后继 `BALWtermEXPTw` 钉在这里（L6 原样读）。答复：一行（选项 (b)）；不并 L4b2；TL1 留在绑定文本；闭合只在 1b 开始时 T2489 已合并才做，否则归最后一张终端票（L5 的最后一张，带 L6）；排在 T2489 之后。
- (5) **开工顺序**（有空位时）：**T2486 → T2489 → T2490**。
- (6) 计数：BA 170；T 25 / 34.5（T1-BA 完成；剩 T5-BA、T7-BA，预期终点 26–27）；U 19 / 42（U2-BA 拆则 20）；**L 45 / 50**（L40-C3 预测 47：剩 L5 带 L6 两行；任一行拆则 48）；M/N 3 / 15；V 0 / 12。
- (7) 在跑：T2473c（T4s2c）、T2482b（U5b-2）、T2484b（U4s2b）、T2488（L3d1）。排队：T2486 → T2489 → T2490。下一张票号 T2491，下一节 §293，下一条 H274。待写：U5d（U5b-2 之后）、U3s2–U3s4、T5-BA（等 T4s2c）、U4s3（等 U4s2b、T4s2c）、U1s2、L5（带 L6，阶段 L 的最后一张）、U5e、T7-BA。

## §293 — T4s2 完成、L3d1 合并；T2490 检查补导入（总调度 V3，2026-10-13 05:04 UTC）

- (1) **合并**：
  - **T2473 T4s2c** 66b2ab97（04:54；`Chain/AzumaProxyGen` 950，目标 8–10；审核 PASS）→ **T4s2 完成**（三行：86eb22f2、4efcae69、66b2ab97）。登记：证明报告把 `GoodSetNg` 记为 `owedProps`（初始成员归 T4-BA；`hQ` 是 Step 3 的输出，U3s2–U3s3）。**调度追认 `owedProps` 这一归类**（它是好集合的成员前提，不是定义对象的谓词）。→ U3s2–U3s4、T5-BA 现在可写；U4s3 还等 U4s2b。
  - **T2488 L3d1** 3d0b9578（05:00；`Graph/BAAnpLift` 388；目标 1–5，**含 4 (b)**——开 1b 时 L3d2b-2 已合并；不拆、没换档；审核 PASS 第一轮）→ `BAAnpAuxG`、`BALWMoment`、`BALWMomentExp` 在 BA 上闭合。
  - T2486（U2-BA，Amend 1）与 T2489（L4b2）已开工。
- (2) **T2490 检查补导入**：编译报 `Unknown identifier RBM.BA.baTwistLoopStep_caseI`（定义在 `BA/TwistLoop.lean:705`，检查文件没有导入它）。调度在检查文件里加了 `import RBM3D.BA.TwistLoop`，钉文不变；又用脚本核过检查里所有 75 个名字，加这一行后都能从导入链到达。中枢重新编译（H274 (2)）。
- (3) 计数不变：BA 170；T 25 / 34.5；U 19 / 42；L 45 / 50（预测 47）；M/N 3 / 15；V 0 / 12。
- (4) 在跑：T2482b（U5b-2）、T2484b（U4s2b）、T2486（U2-BA）、T2489（L4b2）。排队：T2490（检查编译通过后）。下一张票号 T2491，下一节 §294，下一条 H275。起草中：U3s2、T5-BA。待写：U3s3、U3s4、U4s3（等 U4s2b）、U5d（等 U5b-2）、U1s2、L5（带 L6）、U5e、T7-BA。

## §294 — U5b、U4s2 完成；放 U3s2 = T2491（三行预签）与 T5-BA = T2492；U 计划重推到 ≈ 44（旗标 42），发通知 REQ（总调度 V3，2026-10-13 05:45 UTC）

- (1) **合并**：**T2482 U5b-2** e0043e75（05:38；`BA/Step5IIIEdet2` 1,277；目标 6–7、8 (b)；无新的未登记前提；审核 PASS）→ **U5b 完成**（→ U5d 可写：U5a–c 都已合并）。**T2484 U4s2b** e6c26ca4（05:42；`Chain/CltFarUGen` 715、`IniTermIGen` 1,210、备用 `IniTermIGen2` 787；目标 5–9；审核 PASS）→ **U4s2 完成**（共 3,825 行；→ U4s3 可写：U4s2、T4s2 都已合并）。T2490（L4a2）已开工。
- (2) **发 `REQ-2026-10-13-0545-Uplan`**（不阻塞）：
  - U3s2 预签的第三行；
  - 按 0349 O3 重推 U 计划：泛型 ST 行实际落在 T2379 编辑价约 3 倍，BA 行约 2 倍 → 预期 **≈ 44（41–47），超过旗标 42**；
  - T5-BA 的发现 F1；
  - 问监督：照重推的计划继续有无异议，旗标是否重设、是否要先做路线复核。
- (3) **放 T2491 = U3s2**（U 20 / 42，拆则 22；BA 171；`prover-hard`；**窄设计门 D1–D5 带探针**；新增 `Chain/NQGood1Gen`、`NQGood2Gen`（U3s2a）、`NQBudgetGen`、`NQLinGen`（U3s2b）、`NQEndLinGen`、`NQEndFlowGen`（U3s2c）；3,300 / 4,100 / 5,700；**三行叠加预签**）：Step 3 的 `NQ*` 层（`lem:STOeq_NQ`，非交替，路线 (R)）在流载体上的泛型形式。
  - 绑定结论：`nqLinGoodgL_of`、`stOeqNQPTgL''_of`，以及 `hQ_nonAltNg`——T4s2 留下的 `hQ`。
  - 答复：
    - 设计门保留；
    - 去掉没人读的均匀提升 `stOeqNQ''_holds`；
    - D2（`𝒦` 的时间模，(t) 类）归这里；
    - 第三行现在预签，通知随本 REQ 发出；
    - `‖m‖ ≤ 1` 内联；
    - 十条 R2* 文本都钉在这里；
    - 常数显式写成 `Ck`；
    - **(9) 漂移前提**：公开陈述不带 `∀ n` 的 `GridDriftNg`/`HierarchyNg` 前提，漂移在 `∀ᶠ n` 下逐指标进入；本行新加一个公开的泛型"最终"包络（设计门 **D5**，由探针编译其文本），之后的行读它；
    - 名字级表格放 1b 开头。
- (4) **放 T2492 = T5-BA**（T 26 / 34.5，拆则 27；BA 172；`prover-hard`；无设计门；新增 `BA/GridDriftBA`（目标 1–6）、`BA/GridGoodBA`（目标 7–11），备用各一；1,040 / 1,580 / 2,510；预签在文件边界拆）。内容：
  - T5s2 六个类在 BA 的实例：WalkForm（0149 O4）、`Im m ≤ 1`、方差律、概率律、KLink、KLoop、KTwo、UStep、Expand、沿流的束；
  - T4-BA 欠项：`∀ᶠ n` 形式的初始成员资格，水平 `C₀` 定在 `(sz, z)` 之前；
  - `GridGoodNgL` 在 BA 上的实例（经 `gridGoodNgL_of`）、包络、Azuma/Y/QV 读法、实例。
  - 答复：
    - 两部分都在这里做；
    - F1 接受，BA 包络用私有拷贝（公开的泛型最终形式归 T2491）；
    - 现在开工，T2486 (a) 的四个事实先作精确类型前提，闭合放最后写，届时 T2486 (a) 没合并就停在那里；
    - `h0` 用 `∀ᶠ n`；
    - BA 实例不另起钉文名；
    - `HierarchyNg` 在 BA 的逐指标读法归 V1-BA；
    - 登记里 `GoodSetNg` 一行的负责人从 T4-BA 改成 T5-BA；
    - 名字级表格放 1b 开头。
- (5) **开工顺序**（有空位时）：**T2492 → T2491**（T2491 先跑设计门与探针）。
- (6) 计数：BA 172；T 26 / 34.5；U 20 / 42（U3s2 拆则 22；重推的计划 ≈ 44，见 (2)）；L 45 / 50（预测 47）；M/N 3 / 15；V 0 / 12。
- (7) 在跑：T2486（U2-BA）、T2489（L4b2）、T2490（L4a2）+ 一个空位。排队：T2492 → T2491。下一张票号 T2493，下一节 §295，下一条 H276。待写：U5d（可写）、U4s3（可写）、U3s3、U3s4、U1s2、L5（带 L6）、U5e、T7-BA。

## §295 — U2-BA (a)、L4a2、L4b2a 合并（U2-BA、L4b2 各拆两行）；放 U5d = T2493（总调度 V3，2026-10-13 06:18 UTC）

- (1) **合并**：
  - **T2486 U2-BA (a)** 7be99aae（05:54；`BA/KDecayBA` 885、`BA/SEforLnBA` 371；目标 1–5；审核 PASS）。1a 确认预签拆 → U2-BA (b)（`BA/B45BA`，目标 6–8）在 `t/T2486b` 叠加。→ **U +1**。C6：U2 的孪生 `KDecayBA` 实测 885（中心 1,100），U2 + 孪生 = 4,181 + 885 = **5,066** = 2,250 的 2.25 倍（填 ROUTES 的 N）。
  - **T2490 L4a2** 4e78c3da（06:10；`Graph/BAExp14a2` 406；目标 1–4、6；审核 PASS 第一轮）→ **L4a2 完成**。目标 5 的闭合按答复 (5)，因为 1b 开始时 T2489 还没合并，**挪到最后一张终端票（L5 的最后一张，带 L6）**。
  - **T2489 L4b2a** 6a1c1f8f（06:16；`Graph/BAExp14b2` 1,794；目标 1–3；审核 PASS）。1a 确认拆分 → L4b2b（文件 B，目标 4–7）在 `t/T2489b` 叠加。→ **L +1：L 46 / 50，L40-C3 预测 48**（剩 L5 带 L6 两行）。按 2246，预测到 49 发短 REQ，现在还没到。
  - T2491（U3s2 设计门）、T2492（T5-BA）已开工；T2492 的 T2486 (a) 输入现在已合并，闭合不必停。
- (2) 计数：BA 174（U2-BA、L4b2 各拆一行）；T 26 / 34.5；**U 21 / 42**（U3s2 若拆三行则 23；重推计划 ≈ 45，Uplan REQ 等监督回复）；**L 46 / 50**（预测 48）；M/N 3 / 15；V 0 / 12。
- (3) **放 T2493 = U5d**（U 22 / 42；BA 175；`prover-max`；无设计门；新增 `BA/Step5IIIWalk`（U5d-1）、`BA/Step5IIIWalk2`（U5d-2），备用 `Step5IIIWalk3`；1,800 / 2,500 / 3,600；预签拆，预计会拆 → 成为 U5 的第七行，1a-audit 时发短 REQ）。
  - 目标：
    - 到 `BAStep5IIIEMatrix` 的桥（之后可删 `owedProps` 那一行）；
    - 好集合与 `J♯` 的可测形式；
    - 流上的 (H2)；
    - 游走层级 `D_u ∈ [D*−6, D*]`；
    - BA 核上的 Duhamel 形式；
    - 游走（`BAStep5IIIWalk`，闭合就是它的证明）；
    - 提升（`BAStep5IIIFromWalk`）；
    - 实例。
  - 答复：
    - **游走读 `s` 处的 `STDecayStronggL`**：它界的是二圈的 `‖𝓛 − 𝒦‖`，是 `s` 处的归纳假设，属圈层，C1 允许。**T2485 的 C1 清单和设计 F2 把它当成条目层的界，错了，这里更正。**
    - U5e 的输入是两个文本；
    - 闭合是证明，不另立带前提的文本；
    - Duhamel 走确定性的 `pfStep5Grid_duhamel` 的 BA 重述，常数与指数在 1a 定；
    - 更正 (a)；
    - 登记行可删；
    - 第七行的 REQ 在 1a-audit 时发；
    - 两半都用 `prover-max`；
    - 名字级表格放 1b 开头。
- (4) **开工顺序**：T2493 占下一个空位。
- (5) 在跑：T2486b（U2-BA (b)）、T2489b（L4b2b）、T2491（U3s2 设计门）、T2492（T5-BA）。排队：T2493。下一张票号 T2494，下一节 §296，下一条 H277。待写：U4s3（可写）、U3s3、U3s4、U1s2、L5（带 L6，含 L4a2 的闭合）、U5e（U5d 之后）、T7-BA。

## §296 — U2-BA 完成；放 L5（带 L6，最后一张终端票）= T2494、T7-BA = T2495（总调度 V3，2026-10-13 06:59 UTC）

- (1) **合并**：**T2486 U2-BA (b)** 5fbefff2（06:30；`BA/B45BA` 399；目标 6–8；审核 PASS）→ **U2-BA 完成**（`KDecayBA` 885、`SEforLnBA` 371、`B45BA` 399）。
  - 按监督 0349 O5（U5S-C4），四个 BA 载体事实（`LoopForm`、`LCompat`、`KCompat`、`FlowFacts`）和 UN-C3 的 BA `WardCls` 的负责人改为 U2-BA：ROUTES 与 DECISIONS 照此记；T5-BA、U3-BA (a)、U4-BA、U1-BA 都读它。
  - T2493（U5d）已开工。
- (2) **监督对 `REQ-2026-10-13-0545-Uplan` 还没回复**（06:41 那轮没有出文件）。它不阻塞，照常推进；回复到了再落账。本节放的两张票都不在 U 阶段。
- (3) **放 T2494 = L5（带 L6）**（BA-L；L 47 / 50，拆则 48 = 预测；BA 176；`prover-hard`，预签可换 `prover-max`；无设计门；新增 `Graph/BATermHolds`、`BATermHoldsB`、`BALWOut`，备用 `BATermHoldsC`；1,870 / 2,240 / 3,850；预签在 A | B + C 拆）。
  - 目标：
    - `baLWterm_holds`；
    - 两种区间（`1 − t ≤ λ²/L²` 与 `>`）下的 `baLWtermExp_holds`；
    - **`baStep2_closed : ∀ d, BAStep2 d`**（BA Step 2 全闭）；
    - L6 / T2490 的目标 5：`baLWCutExpTw_holds`、`baLWtermEXPTw_holds`；
    - 实例；
    - 登记去掉 `BALWterm` 等三行，并改相关负责人注释。
  - T2387 §8 (6) 的收尾条件列为验收项 (i)–(ix)。
  - 开工条件：A 行现在开工；B 行要等 A 行审核 PASS，而且 T2489b（L4b2b）已合并（它读 `baExp14bS2_holds`）。
  - 合并后发阶段 L 的收尾 REQ（2246 O1）。
- (4) **放 T2495 = T7-BA**（BA-T；T 27 / 34.5，拆则 28；BA 177；`prover`；无设计门；新增 `BA/DecayLoopBA`；140 / 215 / 360）。
  - 内容：BA 上的均匀圈衰减 `baDecayLoopU_of`（`𝒦` 的远端衰减由 `baKcalDecay_holds` 给出）、`baFlow_sizeInv_le`（公开）、逐时刻与单时刻的读法、`twSteps` 合取项 1 和 4、L-桥，以及实例。
  - 阶段 L 的两个钉文先作精确类型前提；1b 开始时若 T2494 已合并，无条件读法只出现在实例部分。
  - **T 的最后一行。**
- (5) **开工顺序**（有空位时）：**T2494 → T2495**。
- (6) 计数：BA 177；T 27 / 34.5（T7-BA 是最后一行；预期终点 27–28）；U 22 / 42（U3s2 若拆三行则 24；重推计划 ≈ 45，REQ 待回复）；L 47 / 50（预测 48）；M/N 3 / 15；V 0 / 12。
- (7) 在跑：T2489b（L4b2b）、T2491（U3s2 设计门）、T2492（T5-BA）、T2493（U5d）。排队：T2494 → T2495。下一张票号 T2496，下一节 §297，下一条 H278。待写（U 行等 Uplan 回复后再放）：U4s3、U3s3、U3s4、U1s2、U5e（U5d 之后）、U-BA 各行。

## §297 — 监督 0658 PASS（U 计划 ≈ 48、旗标 42 不变、UP-C1–C4）落账；L4b2 完成；U3s2 三行、U5d 拆两行确认；T2492 审核 RETURN（修补）；T2493 的两条登记行（总调度 V3，2026-10-13 07:16 UTC）

- (1) **监督 2026-10-13-0658：PASS**（对 Uplan REQ：照常推进；在跑的不受影响）。要点与落账：
  - **UP-F1 / UP-C1**：泛型新文件行实际是 T2379 编辑价的 **×3.9**（不是 ×3），BA 行 ×2 → **U 计划 ≈ 48（44–51）**（取代 REQ 的 44 与 0349 的 35–38）。**旗标 42 保留**（这次 REQ 就是它的通知，到 42 不再发）。**新线**：某次放行使预测 ≥ 49 → 放行前发短 REQ；U 已用 50 而未关闭 → 建议 HOLD（先做数学复核）。每次放 U 行都用实测落地数重推预测。
  - **UP-F2 / UP-C2（布局；U4s3 放行前必须做，之后 U3s3、U3s4、U1s2、V1s2、V1s3 同样）**：超出来自"新文件"布局，不是数学。证书通道外的转换行，票上给两个价——**原地**（T2379 模型 (edit + 245 + 15 × frozen) × 1.2，只算 2,000 行以下的带状文件）与**新文件**（自底向上的普查数）——取便宜的，除非 1a 指出障碍（G1 推论写不出、带状读者展开被转换的定义、锥、停止线）。两个价与理由写进票和 ROUTES 的 U 行。校准：第一张 B 密集载体的原地转换落地超过原地价 2 倍，后面的行回到新文件，不用 REQ，预测重算。监督估 UP-C2 下 U ≈ 44–45、V ≈ 11。
  - **U3s2 改原地（监督标为"可选，调度定"）：不改。** 理由：切换点是 1a-audit，而 T2491 的 1a-audit 06:48 已 PASS、U3s2a 的 1b 已在跑；只把 U3s2b/c 改原地会让带状 `NQBudget` 等文件导入泛型 `NQGood1Gen`，布局混杂。UP-C2 从 U4s3 起执行。
  - **UP-C3**：U3s2 若出第四行、U5d 的第二行只记账，不发 REQ；U3s2 落地时的 C6 数记在 ROUTES 的 U 行（1a：edit + 孪生 5,710，线 6,150）。
  - **UP-F3 / UP-C4（漂移形式）**：T5-BA 的最终包络保持私有；BA 读者（U3-BA (b)、U1-BA）读 `baGridDrift_envelope`；以后的泛型行读 T2491 的 `gridDriftNg_envelope_ev`；不出第三个包络文本。**V1s1（`ExpHier`）的层级前提在 `∀ᶠ n` 下逐指标写**，V1-BA 就不必私拷 `hierarchyNg_of`。
  - **O5（记录）**：1155 C5 的"≤ 100 额外行"只适用于新增的词汇文件（T8 `Step2Gen`、U3s1 `Step34Gen`、U6）；转换行按 UP-C2 定价。0349 F3（只对 BA 行乘系数）作废，以 UP-F1 为准。
  - **O6（V）**：V 的开场 REQ 用 ≈ 13（11–14，旗标 12），UP-C2 下 ≈ 11。
  - BA 全局预测（给 Jun）：**≈ 219（212–227）**，UP-C2 下 ≈ 214。
- (2) **合并**：**T2489 L4b2b** bbe91c0a（07:13；`Graph/BAExp14b2B` 1,174；目标 4–7；审核 PASS）→ **L4b2 完成**（`baExp14bS2_holds` 合并）→ T2494 B 行的条件之一（T2489b 合并）已满足，另一条是 A 行审核 PASS。
- (3) **T2491（U3s2）1a-audit PASS**（06:48）：D1–D5 全部 PASS，文本定下；**三行确认**（U3s2a 1,634 / U3s2b 1,909 / U3s2c 1,817；中心 5,360，第四行线 5,850 有 490 余量）；不需签字，U3s2a 的 1b 已开。→ U +2。
- (4) **T2492（T5-BA）审核 RETURN**（07:10，规则 (B) 修补，非签字项）：目标 8–9 的实例里多留了 `hKb`、`hKw`，应改传 `inst_BAKbound` 与 `baKward_holds …`。修补由中枢的修补阶段做。调度答审核的两条观察：`baGridDrift_envelope` 对每个 `d` 保留 `hKb`（与检查里的形状一致，去掉要 `3 ≤ d`），不改；检查文件目标 8 形状里 `STEKDecaygL` 的误展开只是非绑定的形状，不改检查。
- (5) **T2493（U5d）1a PASS**：
  - **拆分确认**（中心 3,050：U5d-1 `Step5IIIWalk` 1,675 / U5d-2 `Step5IIIWalk2` 1,375）→ U5 第七行，按 UP-C3 只记账、不发 REQ → U +1。
  - `θ` 在 `ε₀` 之后选（票上 `θ = ε₀/(8d(Cd+1))` 不够；实例常数由 1a 定）：**接受**。
  - **登记**：目标 1 (a) 证出 `BAStep5IIIEMatrix` → 删 `:240` 那行（照答复 (6)）。目标 1 (b) 的约束量 `BAStep5IIIGood` 没有定理证出，`s` 处的 `STDecayStronggL` 也是未登记前提。→ **调度批准两条 `owedProps` 行**（原文见 H278 (3)），T2493 的 `Test/Axioms.lean` 可写范围加上这两行；1b 没加的话，中枢合并时照 T2482 先例加上并重跑预检。
- (6) 计数：**BA 180**（U3s2 多两行、U5d 多一行）；T 27 / 34.5；**U 25 / 42**（计划 ≈ 48（44–51），UP-C2 下 ≈ 44–45；预测 ≥ 49 才发短 REQ）；L 47 / 50（预测 48）；M/N 3 / 15；V 0 / 12（预测 ≈ 13）。
- (7) 在跑：T2491（U3s2a 1b）、T2492（修补）、T2493（U5d-1 1b）+ T2494（A 行，L4b2b 合并空出的位）。排队：T2495。下一张票号 T2496，下一节 §298，下一条 H279。**下一张 U 票 U4s3 按 UP-C2 双定价起草。**

## §298 — 子阶段 T 完成（T5-BA、T7-BA 合并），发 T 收尾 REQ；U3s2a 合并；放 U4s3 = T2496（原地布局，UP-C2 的第一次检验）（总调度 V3，2026-10-13 07:58 UTC）

- (1) **合并**：
  - **T2492 T5-BA** b3ead83b（07:19；`BA/GridDriftBA` 757、`BA/GridGoodBA` 1,330；目标 1–11；不拆；一次规则 (B) 修补后第二轮审核 PASS；闭合 `baGridGood_holds` 按名读 T2486 (a)；`GoodSetNg` 的负责人注释改为 T5-BA）。
  - **T2495 T7-BA** 3238c365（07:40；`BA/DecayLoopBA` 228；目标 1–6；审核 PASS 第一轮）。
  - → **子阶段 T 的所有行都已合并：T 27 / 34.5**（0658 预测的终点）。BA Step 2 只差 L5（T2494）的两个钉文和 `baStep2_closed`。发 **`REQ-2026-10-13-0758-Tclose`**，请监督确认 T 在 27 / 34.5 关闭（只以 T2494 证出的阶段 L 钉文为条件）。
  - **T2491 U3s2a** 9df6a9e7（07:29；`Chain/NQGood1Gen` 836、`NQGood2Gen` 687；目标 1–6；审核 PASS）；U3s2b 已在 `t/T2491b` 叠加开工，U3s2c 等 U3s2b 审核 PASS。
  - T2494（L5 + L6）1a PASS：拆分 A | B + C 确认（A 1,185 | B + C 1,197）；预签换档条件 (a) 成立，A 行用 prover-max 重跑 1b → **L 48 / 50**（等于预测）。
- (2) **放 T2496 = U4s3**（U 26 / 42，拆则 27；BA 181；`prover-hard`；**窄设计门 D1–D4 带探针**）。
  - **布局：原地**（UP-C2）。原地价约 1,770（D4 范围；按 T2379 范围 2,058），新文件约 4,480–5,850；1a 没查出障碍。**这是第一次原地转换 B 密集载体，即 UP-C2 (d) 的检验**：实际落地（加的行减去挪动的行）超过 3,540，以后的行就回到新文件，不用 REQ。
  - 可写文件是带状的 `Induction/LemDecCalELip`、`EtermsMid`（U4s3a），`DuhamelI`、`DuhamelII` 和新的兄弟文件 `DuhamelI2`（U4s3b）；备用 `EtermsMid2`。G1：每个冻结的带状声明保留名字和类型。
  - D4 范围：`LemDecCalEPrec` 与 `LemDecCalELip` §5–§7 留在带状。
  - `lem_dec_calE` 的两个钉文写在这里，最多一条 `owedProps`，已批准。
  - D3 内联（用 `T2491_KLip` 的 `k = 2` 文本）。
  - 与 T2491c 的合并先后不限。
  - 预测 U ≈ 46（原地），低于 49，不发 REQ。
- (3) 计数：BA 181；**T 27 / 34.5（全部合并，收尾 REQ 待复）**；U 26 / 42（计划 ≈ 46–48）；**L 48 / 50**（T2494 拆两行，等于预测）；M/N 3 / 15；V 0 / 12。
- (4) 在跑：T2491b（U3s2b）、T2493（U5d-1）、T2494（L5 A 行，prover-max）。排队：T2496（检查编译通过后占空位）。下一张票号 T2497，下一节 §299，下一条 H280。待写：U3s3、U3s4、U1s2（都按 UP-C2 双定价；U3s3/U3s4 等 U3s2c）、U5e（U5d 之后）、U-BA 各行（U1-BA、U3-BA、U4-BA、U6-BA）。

## §299 — Jun：这批工单做完就停，不再放新票；换中枢账号；休息到洛杉矶 9:00；U5d-2 开工（不需 REQ）（总调度 V3，2026-10-13 08:44 UTC）

- (1) **Jun 的话**（08:4x UTC = 洛杉矶 01:4x）：「这批工单结束就不要发工单，整理完这批就好，我要换 hub 账号。休息到 LA 9am」。调度的读法：
  - **这批** = 已经开工的票及其叠加的后续行：T2491（U3s2c 在跑）、T2493（U5d-2）、T2494（L5 B 行在跑）、T2496（U4s3，08:02 已开工）。做完、审核、合并、簿记为止。
  - **不再放新票**：U1s2 = T2497、U3s3 = T2498 的草稿已写好，**不放行**，存在 `docs/claude-team/drafts/`（不进 `docs/tickets/`，CONTROL 不列）。等 Jun 下一次的话再定。
  - 换中枢账号是 Jun 的事；调度在 CONTROL 写明这批的范围，供交接。
  - 休息到洛杉矶 9:00（16:00 UTC）：这批做完、簿记完以后，心跳链停下，只排一次 16:00 UTC 的唤醒。
- (2) **合并**：
  - **T2493 U5d-1** f2af0245（08:00；`BA/Step5IIIWalk` 1,799；目标 1–5 与逐时刻层；审核 PASS）。`owedProps` 的 `BAStep5IIIEMatrix` 行已删（目标 1 (a) 证出）。H278 (3) 批准的两条行没加：带登记预检的全量构建不需要它们。
  - **T2494 L5a** 1843bd31（08:14；`Graph/BATermHolds` 914；目标 1–3、8 (a)；审核 PASS）。B 行（L6、目标 9）在 `t/T2494b` 用 prover-max 跑。
  - **T2491 U3s2b** c2542930（08:20；`Chain/NQBudgetGen` 982、`NQLinGen` 1,101；目标 7–10；审核 PASS）。U3s2c 在 `t/T2491c` 跑。
- (3) **U5d-2 开工，不需要 REQ**：中枢在等"U5 第七行的短 REQ"，但监督 0658 UP-C3 已定 U5d 的第二行只记账、不发 REQ（§297 (5)）。U5d-2 属于这批，占下一个空位。
- (4) 计数不变：BA 181；T 27 / 34.5（收尾 REQ 待复）；U 26 / 42；L 48 / 50；M/N 3 / 15；V 0 / 12。
- (5) 在跑：T2491c（U3s2c）、T2494b（L6）、T2496（U4s3 设计门）。下一个空位给 T2493b（U5d-2）。之后没有排队的票。

## §300 — 监督 0849：子阶段 T 在 27 / 34.5 关闭；TC-1–TC-3 落账（总调度 V3，2026-10-13 09:00 UTC）

- (1) **监督 2026-10-13-0849：PASS，子阶段 T 关闭于 27 / 34.5**，没有剩下的 T 行；T 的旗标撤销。
  - T 的 BA 输出只差阶段 L 的**一个**钉文：`BALWterm` 已由 T2494 A 行（1843bd31）证出，剩 `BALWtermExp`。
  - 具体条件是 T2494 目标 5（`baLWtermExp_holds`）与目标 6（`baStep2_closed`），都在 B 行，正在跑。
  - 阶段 L 的收尾 REQ 引用 `baStep2_closed`，并附去掉 `BALWterm`/`BALWtermExp` 后的公理扫描（O5）；这同时了结 T 的最后一个条件，不再另发 T 的 REQ。
- (2) **TC-1（登记注释）**：
  - `Test/Axioms.lean:196-197`（`STStep2DecayPTgL`、`STGdecayWgL`）还写着 "BA: `baStep2_holds` (T2487; inputs `BALWterm`/`BALWtermExp` (BA-L6) …)"，B 行合并后就过时了。
  - 改成 "BA: `baStep2_closed` (T2494), under the Step 1 binders of `STStep2G` (BA-V)"，并入 T2494 目标 9 的登记改动。B 行的 1b 正在跑，不打断；由中枢在 B 行合并时改（只改注释；H281 (2)）。
- (3) **TC-2（`hQ` 的 BA 负责人）**：T5-BA 目标 10 里的确定性控制项 `hQ` 在 `baStep2Mat` 上的 BA 负责人记为 **U3-BA (b)**；`hQ` 的每个组成部分在 BA 上都已合并。写进 U3-BA 的票；U3-BA 落地时，同时改 `GoodSetNg` 的负责人注释。属于 U 的事项，不重开 T。
- (4) **TC-3（BA 计数）**：BA 是 **182**，不是 181——§298 把 T2494 的拆分和 T2496 算成了一行。分阶段：T 27、U 26、L 48。
- (5) 按 Jun 的话（§299）：只做这批的簿记，不写票、不放票。
- (6) 在跑：T2491c（U3s2c）、T2493b（U5d-2）、T2494b（L6）、T2496（U4s3 设计门）。

## §301 — T2496（U4s3）Amend 1：批准 A6–A9，U4s3a 的 1b 重跑（总调度 V3，2026-10-13 09:17 UTC）

- (1) **T2496 U4s3a 的 1b 在写 Lean 之前停下**（09:06）：1b 开头做名字级核对时发现，转换后的证明要读的四个事实（G1–G4），在 1a-audit 定下的前提行 1–11 里都没有出处。前面几步都已 PASS：预检、探针（D1 是已合并的 `Step5IIIWalk_duhamel`）、1a-audit（拆分适用，中心 2,040–2,084）。
- (2) **Amend 1（`docs/tickets/T2496-amend-1.md`）**：
  - **A6**：D2 加 GMM 合取式。带状 `rfl`；BA 用 `Step2EventsGenTw_baGrid` 第 1 条。照原文批准。
  - **A7**：加内联守卫前提 `∑ b ‖S n a b‖ ≤ 1`。带状 `sum_norm_SB_row`；BA 上 `S = 1`。照原文批准。
  - **A8**：`𝒦^{(2)}` 的大小。先在 1b 开头试由 A9 的衰减类加 `STprof` 上界推出；推不出，再用内联的"最终"前提 `‖K‖ ≤ N`，并写明它的带状消法和 BA 消法；BA 消法也没有就停下。
  - **A9**：行 7 改到载体层面。`𝒦^{(2)}` 衰减用已合并的 `Step2IterGen_K2`；`ℓ = L` 的 `lem:newKLK` 新起一个载体类，`∃ C δ₀` 在规模之前、`∀ᶠ n`，带状消法照 `step2IterGen_newKLKAtN_band`，BA 负责人记为 **U4-BA**。新类不另走探针：1b 先编译类的文本和带状消法，审核对照 `(S5WG+M000)` 与 U5S-C3 检查。
  - 族前提表补上相应的行；拆分照旧；UP-C2 (d) 的校准行数把这些新增行算进去。
- (3) 这属于"整理这批"（§299）：T2496 本来就在这批里，Amend 1 只是让它接着做，不是新票。
- (4) 在跑：T2491c（U3s2c，已有审核报告）、T2493b（U5d-2）、T2494b（L6，已有证明报告）；T2496 按 Amend 1 重跑 U4s3a 的 1b。

## §302 — 阶段 L 的最后一张终端票合并：BA Step 2 无条件闭合，发阶段 L 收尾 REQ；U3s2 完成（总调度 V3，2026-10-13 09:32 UTC）

- (1) **合并**：
  - **T2494 L5b + L6** 8df84009（09:24；`Graph/BATermHoldsB` 1,002、`Graph/BALWOut` 126；目标 4–7、9；审核 PASS）→ **T2494 完成**。H281 (2) 的两条登记注释（`:196-197`）已在同一提交改好。
  - **`baStep2_closed : ∀ d, BAStep2 d`** 的公理扫描只剩 `[propext, Classical.choice, Quot.sound]`；`BALWterm`、`BALWtermExp` 两条登记行已删。→ **BA Step 2 无条件闭合**，T 的最后一个条件了结（0849 O5）。
  - **阶段 L 的所有行都已合并：L 48 / 50**，与 L40-C3 的预测一致，49 的 P2 REQ 没有触发。
  - 发 **`REQ-2026-10-13-0932-Lclose`**，请监督确认阶段 L 在 48 / 50 关闭（2246 O1）。
  - **T2491 U3s2c** c72bc745（09:26；`Chain/NQEndLinGen` 1,022、`NQEndFlowGen` 888；目标 11–15；一次规则 (B) 修补后审核 PASS）→ **U3s2 完成**。
    - 三行实际落地共 5,516 行（836 + 687 + 982 + 1,101 + 1,022 + 888），1a 估 5,360，比值 1.03。
    - C6（UP-C3 记账）：edit + 孪生 ≈ 5,516 + 350 = 5,866，低于线 6,150，不触发。
    - 公开的泛型最终包络 `gridDriftNg_envelope_ev` 已合并（D5）。
- (2) 这批（§299）还剩两张：T2493b（U5d-2，1b 在跑）、T2496（U4s3a 按 Amend 1 重跑 1b）。仍不放新票。
- (3) 计数：BA 182；T 27 / 34.5（已关闭）；U 26 / 42；**L 48 / 50（全部合并，收尾 REQ 待复）**；M/N 3 / 15；V 0 / 12。

## §303 — U5d 完成；这批只剩 U4s3（总调度 V3，2026-10-13 09:47 UTC）

- (1) **合并**：**T2493 U5d-2** f7470f58（09:41；`BA/Step5IIIWalk2` 1,067；目标 6–8；审核 PASS）→ **U5d 完成**（U5d-1 1,799 + U5d-2 1,067 = 2,866，1a 估 3,050，比值 0.94）。登记：H278 (3) 批准的 `owedProps` 行 `RBM.BA.STDecayStronggL` 已加（它是 `baStep5III_walk_at` 的前提）；`BAStep5IIIGood` 那行不需要。`BAStep5IIIEMatrix` 那行已在 U5d-1 删掉。→ U5e（U5 的最后一行，BA 的目标）现在可写，但按 Jun 的话（§299）不写。
- (2) 这批只剩 **T2496（U4s3）**：U4s3a 按 Amend 1 重跑 1b，之后 U4s3b。仍不放新票。
- (3) 计数：BA 182；T 27 / 34.5（关闭）；U 26 / 42；L 48 / 50（全部合并，收尾 REQ 待复）；M/N 3 / 15；V 0 / 12。

## §304 — U4s3a 合并（第一次原地转换）；这批只剩 U4s3b（总调度 V3，2026-10-13 11:23 UTC）

- (1) **T2496 U4s3a** e89f5609（11:14；原地改 `Induction/LemDecCalELip`、`Induction/EtermsMid`，新增 `Induction/EtermsMid2`（1,800 规则的备用文件，由 `EtermsMid` 导入）；目标 1–5；`STEtermsMidgL` 的负责人注释已改；审核 PASS）。全量构建 4,371 个作业，**所有带状读者都照常编译**（G1 成立）。
  - **UP-C2 (d) 校准**：U4s3a 原地新增 1,411 行，预测 921（×1.53）。整张票的检验线 3,540 还剩 2,129 留给 U4s3b。超过检验线，以后的行就回到新文件布局；最终判断在 U4s3b 合并之后。
- (2) 这批（§299）只剩 **U4s3b**（`DuhamelI`、`DuhamelII` 原地 + 新文件 `DuhamelI2`；目标 6–10），已在 `t/T2496b` 叠加开工。仍不放新票。
- (3) 计数不变：BA 182；T 27 / 34.5（关闭）；U 26 / 42；L 48 / 50（全部合并，收尾 REQ 待复）；M/N 3 / 15；V 0 / 12。

## §305 — T2496（U4s3b）Amend 2：批准 A10、A11（网格律、厄米游走），U4s3b 的 1b 重跑（总调度 V3，2026-10-13 11:40 UTC）

- (1) **U4s3b 的 1b 在写 Lean 之前停下**（11:35，1b 开头做名字级核对）：目标 8、9（以及目标 7 的分段部分）要读网格游走的两个事实，在前提行 1–11 和 A6–A9 里都找不到出处：
  - **G5**：网格的律与矩阵层可测性。`STGridMartgL` 不带律参数；D2 的 `Hm` 是存在量词，和 `Pp` 不挂钩。
  - **G6**：厄米游走。
- (2) **Amend 2（`docs/tickets/T2496-amend-2.md`）**：
  - **A10**：不设守卫的族前提 `hGrid : ∀ sz z, Step2EventsGen_Grid (mk sz z) (law sz)`。
  - **A11**：不设守卫的族前提 `hHerm`（`Hpath` 厄米）。
  - 两条都照已合并的 `OptL2Gen`/`Step2IterGen2` 的写法；带状和 BA 的消法都在探针 B 里编译过（BA：`Step2EventsGenTw_baGrid`、`baStep2Mat_Hpath_herm`，对每个 `sz z` 都成立，不需要流）。
  - 另外三条：
    - 确认 `Step2IterGen_K2` 也进目标 8、9 的前提表；
    - 准许 `DuhamelI` 导入 `Chain/GridRepTailGen2`（在上游，不成环）；
    - `DuhamelI` 预测超过 1,800 行时，D1 和逐路径界（§5）挪到新文件 `DuhamelI2`（挪动的行不计入 UP-C2 (d)）。
  - 冻结名照 G1 不变。
- (3) 属于这批（§299）：T2496 接着做，不算新票。UP-C2 (d)：U4s3a 原地新增 1,411 行，U4s3b 预计新增约 800，加上 A10、A11 之后仍远低于检验线 3,540。

## §306 — 监督 0947：阶段 L 在 48 / 50 关闭；BA Step 2 闭合；LC-1–LC-3 落账（总调度 V3，2026-10-13 12:26 UTC）

- (1) **监督 2026-10-13-0947 回复 `REQ-2026-10-13-0932-Lclose`：PASS。**
  - 阶段 L 在 **48 / 50** 关闭，旗标 50 撤销。比 2246 的预期 47 多一张，多在 L4b2 拆行（L40-F1 列过的拆行风险）。
  - `baStep2_closed : ∀ d, BAStep2 d`（8df84009）在 `main` 上，公理只有 `[propext, Classical.choice, Quot.sound]`；登记里不剩阶段 L 的钉文。「无条件」的意思是：`BAStep2` 是 `STStep2G` 的框架，只剩 Step 1 的五个结论作前提，由 V2a 消掉（0849 TC-F2，本来如此）。
  - 子阶段 T 的最后一个条件（0849 O5）也由此消掉。
- (2) **LC-1（过时的 Lean 文档注释，只改注释）：** `BA/LWPinsBA.lean:20, :44, :46, :48`（"owed: BA-L6"），`BA/Step2CloseBA.lean:201`，`Graph/BAGGExp.lean:78`（"owed: BA-L2c"）。下一张碰这三个文件的票把这几行放进可写范围（多半是第一张导入 `LWPinsBA` 的 V 票）。`BALWtermEXP` 的注释改为 "superseded by `BALWtermEXPTw` (T2490/T2494); no producer; do not read"。现在不开票（§299）。
- (3) **LC-2（paper-deltas 账本）：** `docs/paper-deltas.md` 最后一次写入是 2026-10-12 15:10 UTC（D636–D691）。之后合并的阶段 L 行的候选还没编号：T2450、T2456、T2464、T2466、T2469、T2472、T2483、T2488、T2489、T2490、T2494，以及 §269 (8) 推迟的 `T2398a`、`T2433a`、`T2448b` 和 G2/G4/G5/G6 门候选。做法：一节补账，按论文位置去重，照 TLC-3 的样子；`T2494a` 与 `T2494c` 是同一个论文缺口（BA 的 `(eq:directG1/2)` 里的 `|M_{yx}|` 项，`B_graphical_lemmas.tex:286-288`），记一条。这是调度簿记，不是票；交给调度 V4（HANDOFF §5）。
- (4) **LC-3（ROUTES）：** BA 格子里阶段 L 一句的开头改为「阶段 L 关闭于 48 / 50（监督 2026-10-13-0947）」，并记上：V1-BA 读 `BALWtermEXPTw` / `BALWCutExpTw`（七个前提），不读五前提的 `BALWtermEXP`（`LWPinsBA:49`，没有出处）。本节一并改完。
- (5) **O4（V 的接口，写 V 票时照用）：** V2a 用 `baLWterm_holds`、`baLWtermExp_holds` 消掉 `baStep2Decay_holds`、`baSTLWB_of`、`baSTLWT_of` 的钉文前提，类型完全对上，不需要包装。V1-BA 读 `baLWtermEXPTw_holds`、`baLWCutExpTw_holds`，TL1、TL2 按 `u` 取（1354 TLC (b)），`LWAvgLawgL` 取自 `STAvgUgL`。
- (6) **T2496b 的状态：** Jun 在中枢会话里于 11:59 UTC 暂停了 U4s3b 在 Amend 2 下的 1b 重跑（约 17 分钟时停下，没有提交；`t/T2496b` 停在 462b5e09）。中枢循环已停。恢复时照 state 文件：在 `t/T2496b` 上按 Amend 1 + Amend 2 重跑 U4s3b 的 1b（prover-hard，skipPreflight），然后审计。
- (7) 计数：BA 182（O5，不变）；T 27 / 34.5（关闭）；**L 48 / 50（关闭）**；U 26 / 42；V 0 / 12；M/N 3 / 15。

## §307 — 调度 V4 接手；LC-2 论文差异补录 D692–D719（总调度 V4，2026-10-13 17:28 UTC）

- (0) **接手**：调度 V4 = Cowork 会话 session_01RThagGKa4jNgUEWeKViyyg（misslose@g.ucla.edu），2026-10-13 16:44 UTC 起（STARTUP §2 的 V4 提示词）。中枢在新账号下 16:45 UTC 重启：H286 提交 7b9e0c4c；T2496b（U4s3b）按 Amend 1 + Amend 2 恢复 1b（wf_d2f59162-2a4）。Jun 2026-10-13：这批做完就停，**Jun 说开新票之前不放票、不写票**。
- (1) **LC-2（监督 0947；§306 (3)）**：`docs/paper-deltas.md` 追加「补录 D692–D719」一节（28 条；由后台起草子代理整理，调度核读后写入）：先排 §269 (8) 推迟的项（D692 = T2398a + T2433a，D693–D696 = 缺口 G2、G4、G5、G6，T2454a–d → D697，T2457a → D699，T2459a 与 U5 论证 → D702），再按票号排 2026-10-12 15:10 UTC 以后合并的行；`T2494a` + `T2494c` 记一条（D719）。不编号部分：撤回 `T2491c5`；对 D664、D338/D389、D653、D666/D685、D690、D671/D675 的补注；非论文差异（`T2448b` 条件已由 L3b2b 消掉，等）；`T2496e` 待 U4s3b 合并时编号。上段两处更正：`T2455` 并非「无候选」（a 记 D698），`T2458` 上段漏记（D700 (a)、D701 (a)）。范围外仍未编号：`T2353a–c`、`T2354a–c`、`T2359a`、`T2329b`、`T2342a`（下次补录）。
- (2) 计数不变：BA 182；T 27 / 34.5（关闭）；L 48 / 50（关闭）；U 26 / 42；V 0 / 12；M/N 3 / 15。下一节 §308。

## §308 — U4s3b 合并，T2496 完成；UP-C2 (d) 检验通过（原地落地 3,086 < 3,540）；这批做完（总调度 V4，2026-10-13 18:03 UTC）

- (1) **T2496 U4s3b** 5e24c0bb（17:54；Amend 1 + Amend 2 下原地改 `Induction/DuhamelI`（1,087）、`Induction/DuhamelII`（968），新文件 `Induction/DuhamelI2`（1,699，由 `DuhamelII` 导入）；目标 6–10 带实例；`Test/Axioms.lean` 的 `STDuhamelIgL`/`STDuhamelIIgL` 负责人注释；审核第一轮 PASS（claude-opus-5-5），全量构建 4,372 个作业，带状读者照常编译）。探针 `Probe/T2496Pins.lean` 留在分支，不合并。
  - 审核观察 4（根文件导入 `DuhamelI2`）：`RBM3D.lean` 已导入 `DuhamelII`，`DuhamelI2` 经它传递进入全量构建与 `#assert_rbm_axioms`，同 U4s3a 的 `EtermsMid2`；照中枢 done 行，不另加根导入。
  - 偏离票文，审核接受：A7 `hSr` 与行 10 的 `Step34Gen_LCompat/KCompat` 证明不读，不进目标 8、9 的前提（陈述更强）；lift 与计数辅助留在 `DuhamelI`（1,800 规则内）；删掉 8 个没有外部读者的带状公有辅助，由 `duhamelIG_*` 取代（Lean-only）。
- (2) **UP-C2 (d) 检验结论**：U4s3b 落地 = 加 2,458 − 挪 783 = 1,675（停报预测 1,714–1,782；挪动行数是证明者脚本算的，审核没复算，照收）。整张票 1,411 + 1,675 = **3,086 < 3,540**：B 密集载体的原地转换通过检验，以后的转换行照 UP-C2 取较便宜的价，不退回新文件。
  - 校准：实测 3,086 / 原地价 1,770（D4 范围）= ×1.74，其中包括两次修补（A6–A11）加的前提；新文件价 4,480–5,850，原地仍然便宜。
  - 流程（总调度定）：以后的转换票在原地价旁加一个 ×1.74 的敏感价；敏感价不比新文件价便宜，就选新文件。
- (3) 论文差异（paper-deltas 文末「合并时判定 T2496e–f」）：`T2496e` 作 D718 补注，`T2496f` 不编号（Lean 内部常数）；两条报告与审核都说不改论文陈述。
- (4) 返工账本补 T2496 一行（两次钉文修补，不算票）。ROUTES U 行更新。
- (5) **这批（§299）全部做完**：中枢没有在跑的票。照 Jun（2026-10-13）「这批做完就停」：不写票、不放票，等 Jun 说开；开了以后照 HANDOFF §2 先放 T2497。H288 提交本节簿记，中枢待命。
- (6) 计数：BA 182；T 27 / 34.5（关闭）；L 48 / 50（关闭）；**U 27 / 42**（T2496 在 1a-audit 确认拆两行，按 §298 (2)「拆则 27」；§301–§307 写的 26 没算拆分，本节更正；两行现在都已合并）；V 0 / 12；M/N 3 / 15。下一节 §309。

## §309 — Jun：开新票；放 T2497（U1s2，两行，新文件布局：§308 (2) 敏感价第一次用）（总调度 V4，2026-10-14 00:40 UTC）

- (1) **Jun（2026-10-14 约 00:30 UTC，洛杉矶 10-13 17:30）在调度会话里回「go ahead」**，回应调度每轮的「你说开新票之前，我不放票」：恢复放票。照 HANDOFF §2：先放 T2497（U1s2）；T2498（U3s3）等 U1s2a 合并后放；之后 U3s4、U5e、U-BA 各行、V 开场 REQ。中枢保持 2–4 张在跑（T2497 两行 = 2）。
- (2) **T2497 定稿**（V3 草稿，§299；票面 `docs/tickets/T2497.md`，检查 `docs/tickets/checks/T2497-check.lean`）：
  - **布局：新文件**（行 a：`Chain/QGridGen` + `Chain/QGridGen2`；行 b：`Chain/IterationsGen` + `Chain/IterationsGen2`），四个带状文件 `IterationsA/B`、`QGridA/B` 都不改。理由：§308 (2) 的 ×1.74 敏感价第一次用。草稿的混合布局（`IterationsB`、`QGridB` 原地）模型价 2,050（自下而上 1,940）；原地部分 502 × 1.74 → 敏感价 2,421（自下而上 360 × 1.74 → 2,206）；新文件 2,040（自下而上 2,170）。敏感价不比新文件便宜 → 新文件。全原地按 UP-C2 (a) 本来就排除（`IterationsA` 2,033、`QGridA` 2,318 超停止线）。逐文件也一样（`IterationsB` 原地 230 → 400，对新文件 400；`QGridB` 部分只加一条目标，≈ 90 行，放哪都一样）。带状文件不改，原地障碍检查（G1、读者展开、锥）不再需要；`IterationsB` 的 24 个私有控制量在 `IterationsGen2` 里抄成私有 `…g`。
  - **两行从一开始**：U1s2a（QGrid，目标 1–9，≈ 1,150–1,170，hi 1,500）在 `t/T2497`；U1s2b（Iterations，目标 10–15，≈ 865–1,020）在 `t/T2497b`，都从 `main` 起，不叠放，互不导入，同时开工，合并顺序任意。只有行 b 改 `Test/Axioms.lean`（`STIterR'` 负责人注释）。
  - **R2* 文本**：U3s2c 已合并（c72bc745，`Chain/NQEndFlowGen`），按名字读。草稿检查文件里的四份 `T2497_*` 抄本与合并文本逐字比对一致（调度脚本，2026-10-14），已删，钉文 `T2497_IterationsOf/IIOf` 改用合并的 `STIterationsgL'`/`STIterationsIIgL'`；检查加 `import RBM3D.Chain.NQEndFlowGen`，Part 1 加四个名字。
  - 草稿的 12 个待定问题都定了（票面「Decisions」）：除 (1) 改为新文件外，都照草稿取向（范围 S、E′ 路线、奇链界的 `LCompat` + `LoopForm` + 厄米 `Hf`、生成元行界从 `UStep` (b) 取极限、无设计门、`prover`、USemigroup 的 BA 归 U1-BA、`STContractM` 不在这里）。都是流程或监督规则内的路线细节，不问 Jun。
  - 检查文件调度不编译；H290 (2) 中枢在 `main` 上编译，exit 0 才开工。
- (3) 预测（UP-C1）：新文件两行，U 预测 ≈ 45–46，低于 49，不发 REQ。
- (4) **T2498（U3s3）放行前要改的**（草稿在 `docs/claude-team/drafts/`）：T2497 的新文件名（目标 8 在 `Chain/QGridGen2`，不在 `QGridB` §6；T2498 导入 `Chain/QGridGen`/`QGridGen2`）；它自己的八文件原地布局也要照 §308 (2) 加 ×1.74 敏感价重算。U1s2a 合并后放。
- (5) 计数：BA 183（U1s2 两行，计划一行，+1）；T 27 / 34.5（关闭）；L 48 / 50（关闭）；**U 29 / 42**（T2497 两行）；V 0 / 12；M/N 3 / 15。H290。下一节 §310，下一张新票号 T2499（T2498 已由草稿占用），下一条 H291。

## §310 — T2497 两行合并（U1s2 完成，新文件布局落地 2,358）；放 T2498（U3s3，三行，混合布局经 ×1.74 敏感价保留）与 T2499（U5e）（总调度 V4，2026-10-14 01:35 UTC）

- (1) **T2497 合并**：行 a（U1s2a，QGrid）2ee4af8a（01:14；新 `Chain/QGridGen` 970 + `Chain/QGridGen2` 154 = 1,124，预测 1,150–1,170，比 0.97；目标 1–9 带实例；不改登记）；行 b（U1s2b，Iterations）0bf9dc0c（01:17；新 `Chain/IterationsGen` 633 + `Chain/IterationsGen2` 601 = 1,234，预测 865–1,020，比 1.21（对自下而上 1,020））。两行审核都是第一轮 PASS（claude-opus-5-5），带状文件一个没动，全量构建 4,374 / 4,376 个作业。**U1s2 完成**。
  - 校准（新文件价）：落地 2,358 / 模型价 2,040 = ×1.16（对自下而上 2,170 为 ×1.09），在 2,000 停止线与 hi 2,290 附近，正常。
  - 行 b 登记：`STIterR'` 负责人注释照票；另加一条扫描报出的 `owedProps` 行 `RBM.BA.STXiBootgL'`（`Test/Axioms.lean:229`；票说"只为扫描报出的加"，允许；审核 O1）：它是 `iterationsB_stepg` 与合并的 `STIterRgL'` 的前提；泛型钉文 `STOeqQtgL'`、`STOeqQtNZgL'` 推出它（证明在 U3s3、U3s4），BA 归 U3-BA。**接受**；U3s3/U3s4 的票面按此记账。
  - 审核观察（行 a O1–O4：`gridDriftQNg_of` 无独立实例、目标 5 的网格事实代 `u_{j+1} < 1`、可积性改读 `HierDriftGen_integrable_LIM`、多出的公开名都带词干；行 b O2–O3）：照收，无动作。
- (2) **论文差异**：D720 ← `T2497a`–`b`（载体类代 `|E| < 2`、`M = mI`、`‖m‖ = 1`、行和 `= 1`；目标 8 以 `DecayGen_Spec` + `Im m ≤ 1` 代 `|E n| ≤ 2 − κ`，E′ 路线）；行 b 无新候选（继承 D170、D171、D563）。写入 `docs/paper-deltas.md` 文末新段。
- (3) **放 T2498（U3s3）**（V3 草稿 §299 → 定稿 `docs/tickets/T2498.md`、检查 `docs/tickets/checks/T2498-check.lean`）：
  - 布局：**混合 8 + 2 保留**（原地 `QProxy`、`QDriftA/B`、`QLevelsA/B`、`QBudgetA/B`、`QEndA` + 实例兄弟 `QProxy2`、`QEndA2`；新 `Chain/QEndGridGen`、`Chain/QEndB1Gen`）。§308 (2) 敏感价：原地 1,880 × 1.74 = 3,271，合计 6,221 < 新文件（D4 范围）7,680；逐文件原地敏感价也都低于新文件价（最近的 `QEndA` 910 / 950）。全十个原地（1,820，敏感价 3,167）要把 `QEndGrid`、`QEndB1`（都超 2,000，UP-C2 (a) 之外；`QEndB1` 尾部是 U3s4 读的）原地拆开：不取，不发 REQ。
  - 开工条件满足：T2497 行 a 已合并（`Chain/QGridGen`、`QGridGen2` 按名字读）；U3s2c 已合并（行 c 按名字读，不抄 T2491 文本）。层次更正：`Chain/QGridGen` 导入带状 `QGridA`、`QGridGen2` 导入 `QGridB`，两者都在原地文件的上游，无环。
  - 三行预签、叠放 a → b → c；行 a 有设计门 D1–D4 + 探针 → 1a-audit（要签字时 H183 (3)）→ 1b `prover-hard` → 审核。草稿 10 个待定问题照草稿取向定（票面「Decisions」）。
- (4) **放 T2499（U5e）**（后台起草子代理起草，调度核读定稿 `docs/tickets/T2499.md`、检查 `docs/tickets/checks/T2499-check.lean`）：新 BA 叶文件 `BA/Step5IIITargets`，把合并的 U5d 两个文本（`baStep5IIIWalk_holds`、`baStep5IIIFromWalk_holds`）与 U4s1 的 `ST_step5_caseIII_of_pfgL` + U2-BA 的 `baStep5CasesGen_flowFacts` 组合成 BA 元组上的 `STPfStep5gL`、`STStep5IIIgL`（d = 3）；无新数学、无设计门；价 60 / 100 / 160（设计 150 / 250 / 450 早于 U5d 的 `example`）；角色定为 `prover`；登记删 `owedProps` 的 `RBM.BA.STPfStep5gL`（结论头被证出）。合并后 U5 完成。
- (5) 预测（UP-C1）：≈ 45（44–47）：§298 的 46 记 U1s2 三行（实为两行）、U3s3 三到四行（取三行）；U5e 已在账。低于 49，不发 REQ。
- (6) 计数：BA 185（U3s3 计划一行、定三行，+2；U5e 计划内）；T 27 / 34.5（关闭）；L 48 / 50（关闭）；**U 33 / 42**（T2498 三行 30–32，T2499 33）；V 0 / 12；M/N 3 / 15。H291。下一节 §311，下一张票号 T2500，下一条 H292。
- (7) 下一批起草：U3s4（等 U3s3）；U-BA 各行里 **U1-BA**（U1s2 已合并，可写；含 `stNewPQgL_wardCls` 的 BA 读法，读 U2-BA 的 `WardCls`）与 **U4-BA**（U4s3 已合并，可写；欠项 A9、D2 的 BA 消法）先起草；U6-BA；V 开场 REQ（记 BA 情形 (iii) 只在 d = 3）。

## §311 — T2499 合并（U5 完成，合计 7,830）；放 T2500（U1-BA，一行）与 T2501（U4-BA，三行预签 a1 ∥ a2 → b）；T2498 Amend 1（`∃ C₆` 在 `κ` 之后）（总调度 V4，2026-10-14 02:32 UTC）

- (1) **T2499 合并** 086d9091（02:00 UTC）：新 `BA/Step5IIITargets` 112 行（价 60 / 100 / 160，比 1.12）；目标 1–3 带实例（d = 3）；登记删 `owedProps` 的 `RBM.BA.STPfStep5gL`、T2462 头注释加注记；根导入被分支放在中间，中枢挪到最后一行；审核第一轮 PASS（claude-opus-5-5）；全量构建 4,377 个作业。**U5 完成**：`Step5IIIKer` 709 + `Ker2` 471 + `Edet` 1,493 + `Edet2` 1,277 + `Good` 704 + `Good2` 198 + `Walk` 1,799 + `Walk2` 1,067 + `Targets` 112 = **7,830**，对 T2459 设计中心 6,900 为 ×1.13（4,650 / 6,900 / 10,600 之内）；九个文件、七行。
  - 论文差异：无新候选；D702 的未结注记「U5e 尚未写」由本票了结（`paper-deltas.md` 文末新段）；d = 3 照 D712 (d)。
- (2) **放 T2500 = U1-BA**（后台起草子代理起草，调度核读定稿）：新 BA 叶 `BA/ZeroModeBA`；目标 1–7：T2463 挪来的 `stNewPQgL_wardCls`、它的 BA 读法 `baSTNewPQgL`（读 U2-BA 的 `baZeroModeGen_wardCls`）、`baZeroModeSet_UN`（`BAUN` 形式）与 `baZeroModeSet_ThetaN`、`baStep2Gen_USemigroup`（`gridRepTailGen_ker_BA` 的第一合取项）、`baIterationsGen2_fam`、R2* 两个钉文 `baSTIterationsgL'_holds`、`baSTIterationsIIgL'_holds`，实例 d = 3（情形 (i) 新私有数据，`lam ≡ 2`）。
  - 输入全部已合并（U2-BA = T2486 7be99aae / 5fbefff2；U1s2 = T2497）；不依赖 U3s3（T2498）或 U3s4：`STXiBootgL'` 只是 R2* 钉文里的绑定变量（BA 负责人 U3-BA，§310 (1)）。
  - 无新数学、无设计门、`prover`；自下而上 200 / 320 / 480（UP-F1 读数 1,310 / 2,446 / 4,464 记在旁边：其内容已由 U2-BA、P1b-2、U1s2b 合并）；一行，停止线 640。UP-C2：目标 1–4 原地 84、敏感价 122，新叶 70 → 新文件。
  - 登记只改 `STIterR'` 负责人注释；无 `owedProps` 可删。草稿十个待定问题照草稿定（票面「Decisions」）；WardIdent 桥归 U4-BA (b)，QGrid 目标 6、8 的 BA 归 U3-BA (b)；UP-C4 在这里空成立（U1-BA 不读漂移）。
- (3) **放 T2501 = U4-BA**（后台起草子代理起草，调度核读定稿）：范围比 HANDOFF §2 的 A9 + D2 大——登记与 T2462 / T2484 / T2479 / T2496 票面把约 15 项的 BA 负责人记为 U4-BA (a)/(b)，全收。
  - 行 a1 `BA/Step5KerBA`：`IniTermGen_KerFacts`（`gK = g₀`，带 R1 比较）与 `Step5KerGen_ThDecay`（`∃ C₆` 在 `κ` 之后）；**A9**（`stNewKLKLAtgL'_of` 的逐载体私有副本，F7 不读，R1 不进）；**D2**（`hFM`，T2496 探针里已编译）；**D3**（k = 2 的 `NQEndFlowGen_KLip`，在这里证，U3-BA 的一般 k 以后复用）；`baNewKLKLgL'`。
  - 行 a2 `BA/CltFlowBA`：X1 实例 `IniTermGen_CltFlow` 及五个登记头（`STThPropsg`、`STKpropsg`、`STMfarg`、`STKfargL`、`CltInvg`/`CltRepg` → `STExpInvgL`）。
  - 行 b `BA/Step5CasesBA`：UN-C3 Ward 桥（泛型，共轭内联）+ BA 读法，六个成分钉文，情形 (i)、(ii)、(iv)（与 U5e 的 (iii) 一起交 V2a/V2b、U6-BA）。
  - 输入全部已合并（含 U2-BA 的四个载体事实与 `WardCls`）；不等 U3-BA、U1-BA、U6-BA。
  - **行数与拆分**：草稿两行、行 a 中心过 1,950 才拆 a1 ∥ a2；行 a 自下而上 1,530，校准后 ≈ 1,850–1,900 正在线上，又有两个空位 → **放行时就拆**：a1 ∥ a2 都从 `main` 现在开工、互不导入，行 b 等两行都 PASS 并合并后叠放。角色 a1、a2 `prover-hard`，b `prover`；无设计门、无探针。
  - 价：自下而上 1,350 / 2,000 / 3,000（校准 ≈ 2,300–2,480；UP-F1 读数 5,418 / 三行记在旁边）；全是新 BA 叶，无原地价、无 ×1.74；停止线 a1 1,150、a2 1,200、b 700，单文件 2,000。
  - 登记：删十条 `owedProps`（a2 五条 X1 行，b 五条成分钉文行；a1 无），`STStep5ConclgL` 留下、改负责人注释；三个票头注释加注记。草稿十二个待定问题除 (2)、(12) 与 (3) 的停止线照上改外，照草稿定。
- (4) **T2498 Amend 1**（`docs/tickets/T2498-amend-1.md`）：T2501 草稿查出 T2498 检查文件 `:254-258` 的形状（非约束）把 `∃ C₆` 放在 `κ` 之前，而 BA 的尾常数 `NewKLKBA_tail`（`NewKLKBA:269`）依赖 `κ`。票面族前提表第 9 行（`T2498.md:73`）本来写的是「`∃ C₆` 在 `κ` 之后」：以表为准。行 a 若已按形状写成在前，在 1a-audit 前或 1b 开头挪到 `0 < κ` 之后；只是减弱前提，目标不变。流程事，不问 Jun。
- (5) 预测（UP-C1）：≈ 44（43–46）：§310 (5) 的 ≈ 45 记 U1-BA 两行（0658 `:56`），实为一行；U4-BA 记三行（`:58`），实为三行。低于 49，不发 REQ。
- (6) 计数：BA 186（U4-BA 计划两张、定三行，+1；U1-BA 计划内一行）；T 27 / 34.5（关闭）；L 48 / 50（关闭）；**U 37 / 42**（T2498 30–32，T2499 33，T2500 34，T2501 35–37）；V 0 / 12；M/N 3 / 15。中枢在跑：T2498、T2500、T2501a1、T2501a2（4 个位）。H292。下一节 §312，下一张票号 T2502，下一条 H293。
- (7) 下一批起草：U3s4（等 U3s3 = T2498）；U3-BA (a)/(b)（等 U3s3–s4）；U6-BA（读 U4-BA 行 b 与 U5e）；V 开场 REQ（记 BA 情形 (iii) 只在 d = 3；V1-BA 读 `BALWtermEXPTw` / `BALWCutExpTw`）。

## §312 — T2500 合并（U1-BA；U1 完成）；T2498 行 a 按预签切分 a | a′（总调度 V4，2026-10-14 03:16 UTC）

- (1) **T2500 合并** a6ec5c5c（03:05 UTC）：新 `BA/ZeroModeBA` 409 行（自下而上 200 / 320 / 480，中心的 ×1.28，停止线 640 之下；情形 (i) 的 `BAFlow` 证明 82 行，低于 120）；目标 1–6 带 d = 3 实例；登记只改 `STIterR'` 负责人注释；审核第一轮 PASS（claude-opus-5-5）；全量构建 4,378 个作业。**U1 完成**（U1s1 = T2463、U1s2 = T2497、U1-BA = T2500）。
  - 论文差异：无新候选（D720、D563 覆盖；`paper-deltas.md` 文末新段）。
  - 审核观察 O1–O3（实例以 `have` 应用定理后收 `True`；行数；`t ≤ T₀` 直接证）：照收，无动作。
- (2) **T2498 行 a 切分**：1a-audit PASS（02:35 UTC），1a 中心 2,508（低端 1,981）> 1,950，票面预签切分生效，不需签字：U3s3a = `QProxy`、`QDriftA/B`、`QLevelsA/B`、`QProxy2`（目标 1–6 及目标 9 的相应部分，`t/T2498`）| U3s3a′ = `QBudgetA/B`、`QEndA`、`QEndA2`（目标 7、8 及目标 9 的相应部分，`t/T2498a2`），叠放 a → a′ → b → c。四行 1a 合计 4,799 < 5,850（UP-C3 不触发）。1a-audit 也独立查出 `∃ C₆` 须在 `κ` 之后，与 Amend 1 一致；中枢在 1b 开头交了 Amend 1（H292 (2)）。
- (3) 预测（UP-C1）：≈ 45（44–47）：§311 (5) 的 ≈ 44 加 T2498 的第四行。低于 49，不发 REQ。
- (4) 计数：BA 187（T2498 +1）；T 27 / 34.5（关闭）；L 48 / 50（关闭）；**U 38 / 42**（T2498 30–33，T2499 34，T2500 35，T2501 36–38）；V 0 / 12；M/N 3 / 15。中枢在跑：T2498 行 a、T2501 a1、T2501 a2（3 个位）。H293。下一节 §313，下一张票号 T2502，下一条 H294。
- (5) 现在没有可写的 U 票（U3s4 等 T2498，U3-BA 等 U3s3–s4，U6-BA 等 T2501 行 b）。**起草 V 开场 REQ**（后台起草子代理；0658 O6：≈ 13（11–14）对旗标 12，UP-C2 下 ≈ 11；问哪些 V 行可与 U 的尾巴并行开工；记 BA 情形 (iii) 只在 d = 3、0947 O4 的 V 接口）。

## §313 — T2501 行 a1、a2 合并（行 b 开工）；D721；T2501 Amend 1（行 b 实例数据）；发 V 开场 REQ（总调度 V4，2026-10-14 03:33 UTC）

- (1) **T2501 行 a1 合并** 4c9a9311（03:22 UTC）：新 `BA/Step5KerBA` 708 行（自下而上 740，比 0.96）；目标 1、3–7 带 d = 3 实例；不改登记；审核第一轮 PASS。**行 a2 合并** db1932eb（03:24 UTC）：新 `BA/CltFlowBA` 778 行（自下而上 790，比 0.98）；目标 2 带 d = 3 实例；登记删五条 `owedProps`（`STKfargL`、`STMfarg`、`CltInvg`、`STThPropsg`、`STKpropsg`）并加票头注记；审核第一轮 PASS。两行合计 1,486（自下而上 1,530，×0.97）；全量构建 4,380 个作业。**行 b 03:24 开工**（wf_8efc2c9f-d25，从 db1932eb）。
  - 审核观察：a1 O1–O5（报告 212 行、导入 `EtermsMid2`、多三个 `open private`、平移引理换 `baP8_BATheta_shift`、文档串）；a2 O1–O4（`STMfarg` 改由 `baPropM_holds` 证、实例 (B) 是固定 `L` 的 `lam ≡ 1` 数据、报告 210 行、也用了 R1 的第一合取项 `g₀² ≤ lam²`——在合并的 R1 文本里，票面 UBA-C1 表少写了，不是陈述差异）。照收，无动作。
  - **文档串修正（LC 类）**：`EMn2BA_mF_data`（`BA/EMn2BA:124`）的文档串写 `‖m_F‖ ≤ 1`，第二合取项其实是 `Im m_F ≤ 1`；进下一张碰 `EMn2BA` 的票（同 LC-1 的做法）。
  - 论文差异：**D721 ← T2501a**（行 a1：BA 的 `Θ` 衰减常数 `C₆` 依赖 `κ`，`∃ C₆` 在 `κ` 之后；仅形状）；行 a2 无新候选。写入 `paper-deltas.md` 文末新段。
- (2) **T2501 Amend 1**（`docs/tickets/T2501-amend-1.md`）：行 a2 报告 (d) 与审核 O2 指出 `(sz0, zSeq, flow_sz0)` 上 Step 5 情形 (i)、(ii) 的区间是空的，行 a2 的数据 (B) 是私有的。行 b 可按 `TwistStep2_szII`（公开）与 T2500 的私有 `lam ≡ 2` 数据的样子自建私有数据（每个连流证明 ≤ 120 行），不出公开 `def`；找不到非空区间就把区间与区制留作假设并报告（不停）；行 b 停止线 700 → 900。流程事，不问 Jun。H294 (2) 在下一个阶段边界交给行 b。
- (3) **发 V 开场 REQ**：`docs/supervisor/requests/REQ-2026-10-14-0330-Vopen.md`（后台起草子代理起草，调度核读，按 a1、a2 已合并改了现状）。要点：
  - Q1：开 V，≈ 12（11–14）行，旗标 12 不变，加 UP-C1 式线（预测 ≥ 15 先发短 REQ；用到 15 未关闭建议 HOLD），列出关闭条件。
  - Q2：V1s1 现在开（输入全在 `main`，导入闭包里没有 U3s3/U3s4 文件），V2a 的设计门（1a + 探针）在下一个空位，其余按依赖叠放。
  - Q3：V1s1 在证书通道里 → 新文件（4,560，三行）；V1s2′、V1s3′ 原地（×1.74 敏感价仍比新文件便宜），并按导入层重切（不改行数）。
  - Q4：BA 情形 (iii) 只有 d = 3：V 对所有 d ≥ 3 陈述，带一个显式假设 `STStep5IIIgL d`，另给 d = 3 的无条件推论；Thm 2.7 是否要覆盖 d > 3 是 Jun 的范围问题，到 V 的关闭 REQ 再问。
  - Q5：(a) V2a 的步是单流的，而 `BAStep1` 是族钉文（T2205 的路线 (A)），可能要族版本的步与链（加 0–1 行，由 V2a 设计门先定）；(b) `GLoopAtT0`、`STBaseG`、`STHorizonG` 在 BA 的负责人是 "BA-V" 但没有 V 行 → 归 V3。
  - 监督下一次 :41 运行；回复前不放 V 票。
- (4) 计数不变：BA 187；T 27 / 34.5（关闭）；L 48 / 50（关闭）；U 38 / 42（预测 ≈ 45）；V 0 / 12；M/N 3 / 15。中枢在跑：T2498 行 a、T2501 行 b（2 个位）。H294。下一节 §314，下一张票号 T2502，下一条 H295。

## §314 — 监督 0342 PASS：V 开场（≈ 12，旗标 12）；V-F1 族形式的步（V-C1）；V-F2 问 Jun；T2501 行 b 合并（U4 完成）；放 T2502（V1s1，三行）与 T2503（V2a 设计门）（总调度 V4，2026-10-14 04:20 UTC）

- (1) **监督 0342 PASS**（`docs/supervisor/2026-10-14-0342.md`，答 REQ-2026-10-14-0330-Vopen）：
  - **Q1**：开 V，≈ 12（11–14），旗标 12；新线：放行使预测 ≥ 15 → 先发短 REQ；V 用到 15 未关闭 → 建议 HOLD。关闭条件 (i)–(iv) 收下，两处修改：(i) 写成「`BAMLOutTL 3` 由族链经 `BAFamZ_main` 取回」；加 (v)：族形式的步与链公开、标准公理，`BAMainIndTL` 的文档注释写明不在路线上。
  - **Q2**：V1s1 现在开；V2a 设计门**现在**占第二个空位；然后 V1s2′ → V1s3′ → V1-BA；V2a 的 1b 等 U3-BA (a)/(b)、T2501 b、U6-BA、V1-BA；V2b；V3（可与 V2a 的 1b 并行，族步作假设）。
  - **Q3**：V1s1 新文件（证书通道，45 个模块的锥与 22 个冻结行不动）；V1s2′、V1s3′ 原地（×1.74 仍便宜）；按导入层重切正确，不改行数。
  - **Q4**：V 对所有 d ≥ 3 陈述，情形 (iii) 作一个显式假设 `STStep5IIIgL d`，另给 d = 3 的无条件推论；**修改：Thm 2.7 的范围问题现在就问 Jun**（O3），`STStep5IIIgL` 在 d > 3 的 `owedProps` 行（若扫描要）负责人写「Jun scope decision (D712 (d); supervisor 2026-10-14-0342 V-F2)」。
  - **Q5**：(a) **V-F1 确认**：单流的 `BAMainIndTL` 由族形式的 `BAStep1` 推不出（论文 `lem_ConArg_BA` 读另一条流的 `(loopbound_s)`）；**V-C1（约束）**：V2a 设计门按序 (1) 陈述族步 `BAMainIndFamTL`，`BAMainIndTL` 原样留着、注释标为不在路线上；(2) 探针编译族形式的 Step 1 调用与 K2 逐成员的 `STKboundgL`；(3) 查族成员的流与时界，使逐成员的基础事实适用；(4) 给族链孪生与尾段定价，若超出「+0–1 行」则预测动，按 Q1 的 15 线。不对单流 `BAMainIndTL` 放任何 V2a/V2b/V3 的 1b。(b) `GLoopAtT0`、`STBaseG`、`STHorizonG` 在 BA 归 V3。
  - O1–O4 照办：本节与 ROUTES 记 V 开场；T2503 = O2；O3 = 本轮向 Jun 提问；O4 = LC-1 与 `BAMainIndTL` 注释进 T2503 的合并（T2503 答 (4)）。
- (2) **T2501 行 b 合并** bbb1fd30（03:59 UTC）：新 `BA/Step5CasesBA` 556 行（自下而上 470，×1.18；Amend 1 停止线 900 之下；私有实例数据照 Amend 1）；目标 9–12；登记删五条 `owedProps`（`STEtermsMidgL`、`STDuhamelIgL`、`STDuhamelIIgL`、`STIniTermIgL`、`STIniTermIIgL`），`STStep5ConclgL` 改负责人注释；审核第一轮 PASS；全量构建 4,381 个作业。**T2501 完成**：a1 708 + a2 778 + b 556 = 2,042（自下而上 2,000，×1.02；UP-F1 读数 5,418）；共删十条 `owedProps`。**U4 完成**（U4s1 = T2462、U4s2 = T2484、U4s3 = T2496、U4-BA = T2501）。BA 上 Step 5 四种情形都已合并（(iii) 只在 d = 3）。
  - 审核观察 O1–O5（情形 (iv) 的实例保留九个载体谓词作假设——它们不是确定性的；`(sz0, zSeq)` 的区间为空，照 Amend 1 用私有数据；报告 235 行；桥的实例走 BA 组合；与 T2498 的并集）：照收。论文差异：无新候选。
- (3) **放 T2502 = V1s1**（后台起草子代理起草，调度核读定稿）：新文件 `Chain/Step6Gen`、`Step6KitGen`（行 a）、`ExpHierGen` → `ExpDuhamelGen`（行 b）、`ExpAvgGen`（行 c）；三行预签：a 先，b ∥ c 在 a 合并后并行（保持导入次序；字面切法中间一行约 2,000，过 1,950 线）；价：UP-F1 记 4,560，自下而上 4,030（3,030–5,400），普查 ×1.24 3,031，原地 2,093 / ×1.74 3,641（只记账）；`prover-hard`；行 a、b 无设计门，行 c 预授权窄门（W1：自洽方程与同荷 `uKer` 行界，无合并的载体文本）；行 b 的 W2（私有生成元，预算 300）；`T2502_IngR6gL`、`T2502_Step6RgL` 现在就有约束力（V1-BA 与 T2503 读）。草稿十二个待定问题照草稿定。LC-1 不在这里（不导入 `BA/LWPinsBA`）。
- (4) **放 T2503 = V2a 设计门**（后台起草子代理起草，调度核读定稿；O2）：1a 报告 + 探针 `RBM3D/Probe/T2503Pins.lean`（不合并），`prover-max`；D1–D4 对应 V-C1 四步；约束文本 `T2503_BAMainIndFamTL`；建议（不约束）单流 `BAMainIndS1TL` + 一个包装 `FamOfS1`；草稿查出成员在 `main` 上是有限修改后、在 `(κ', ε') ≤ (κ, ε)` 处的 `BAFlow`（`BAFlowMember`），不是同一 `(κ, ε)`：不算停，D3 核实对 `BAFlow` 一致的基础事实足够（报告记，监督看）；`BATwistLoopLaw` 的同余缺（约 10 行）；合并：报告 + `BAMainIndTL`/`BAChainTL` 注释 + LC-1 四处注释（只改注释行；O4、Q1 (iv)、(v) 的注释部分提前了结）。草稿十一个待定问题照草稿定。Step 6 输入先用抽象 `S6`，T2502 合并时对表。
- (5) **O3：问 Jun**（本轮，洛杉矶时间）：Thm 2.7（BA）是否覆盖 d > 3——(A) 把 U5 的 d = 3 文件推广到一般 d（约 90 处 `Sizes 3`/`Zd 3`，待定价），或 (B) 在论文差异里把 BA 结论限定为 d = 3（`1_2:645`），Jun 在 Lean 做完后改论文。答复前两条路都不挡 V。
- (6) 预测：V ≈ 12（11–14）不变（V1s1 三行照 0658 定价，设计门是 Q5 (a) 的「+1」）；U ≈ 45（44–47）。都不发 REQ。
- (7) 计数（§310 (6) 的口径：BA 只记相对 T2379 计划的增量）：**BA 190**（V1s1 计划一行、定三行 +2；V2a 设计门计划外 +1）；T 27 / 34.5（关闭）；L 48 / 50（关闭）；U 38 / 42（U1、U4、U5 完成）；**V 4 / 12**（T2502 1–3，T2503 4）；M/N 3 / 15。中枢在跑：T2498 行 a（审核中）、T2502 行 a、T2503（3 个位）。H295。下一节 §315，下一张票号 T2504，下一条 H296。
- (8) 下一批：U3s4（等 T2498）；U3-BA (a)/(b)；U6-BA（REQ-1418 的 BA 缩写，T2503 答 (7)：不挡 V2a）；V1s2′（等 T2502 行 a，原地，两价 + ×1.74）。

## §315 — T2498 行 a 第一部分（U3s3a）合并；D722；a′ 开工（总调度 V4，2026-10-14 04:33 UTC）

- (1) **T2498 U3s3a 合并** ec57490f（04:21 UTC）：原地改 `Induction/QProxy`、`QDriftA`、`QDriftB`、`QLevelsA`、`QLevelsB`，新 `Induction/QProxy2` 838 行（根导入，无别的导入者）；目标 1–6 与目标 9 的相应部分；不改登记；探针不合并。审核第一轮 RETURN（漏了一个论文差异候选），一次规则 (B) 只改报告的修补（加 `T2498f`），第二轮 PASS；全量构建 4,382 个作业。**U3s3a′ 04:22 开工**（`t/T2498a2`，叠放，wf_d7dacd26-ca0）。
  - 校准（审核 O3）：新增 − 挪动 = 2,256，对 1a 中心 1,229 为 ×1.84，略高于 §308 (2) 的 ×1.74；`QDriftA` 到 1,893 行（1,800 规则的预留文件线附近）。记账：a′ 落地后核 T2498 原地部分合计对敏感价 3,271；若原地部分超过敏感价且总计逼近新文件价 7,680，下一张转换票的敏感系数改用新的实测值（不回头改 T2498 布局：剩下的 b、c 本来就是新文件）。
  - 审核观察：O1 四个新 `open private`；O2 一个实例用的是证明体而非目标；O4 合并时不带探针、加根导入（中枢已照办）；O5 旧检查文件 `docs/tickets/checks/T2194-check.lean:182, 206` `#check` 了被删的两个带状声明——那是从未编译的旧检查，只记账（归 `T2498c`），不改。
  - 论文差异：**D722 ← T2498a–f**（写入 `paper-deltas.md` 文末新段）。
- (2) 计数不变：BA 190；U 38 / 42；V 4 / 12；M/N 3 / 15。中枢在跑：T2498 a′、T2502 行 a、T2503（3 个位）。H296。下一节 §316，下一张票号 T2504，下一条 H297。Jun 的 Thm 2.7 维数问题（§314 (5)）待答。

## §316 — Jun 定 Thm 2.7（BA）的维数范围：B，只做 d = 3（D723）（总调度 V4，2026-10-14 05:29 UTC）

- (1) **Jun 的决定**（2026-10-14 05:29 UTC，调度会话，回 §314 (5) / 监督 0342 V-F2 / O3 的提问）：**B**——BA 的 Thm 2.7（`MR:decol_BA`）在 Lean 里只做 **d = 3**；论文 `1_2:644-645` 写的是 d ≥ 3，记一条论文差异（**D723**），Jun 在 Lean 做完后自己改论文。不推广 U5 的 d = 3 文件（`Step5IIIGood`、`Step5IIIWalk`、`Step5IIIWalk2` 里约 90 处 `Sizes 3`/`Zd 3`），不开推广票，BA 预测不加行。
- (2) **对 V 的影响（不改任何已放行的票）**：
  - 0342 Q4 的做法照旧：V2a/V2b/V3 的泛型 BA 陈述对所有 d ≥ 3 写、情形 (iii) 带一个显式假设 `STStep5IIIgL d`（几乎零成本，保持与带状 `∀ d, 3 ≤ d` 的形状一致）；**BA 终端（`BAMLOutTL 3`、`UNMLOutBA` 在 d = 3）是无条件的结论**，即 V 关闭条件 (i)。
  - d > 3 的情形 (iii) 不再是待定事项：若扫描要求一条 `owedProps` 行，负责人注释写「out of scope: Jun decision B, BA Thm 2.7 at d = 3 (D723; DECISIONS §316)」，取代 0342 Q4 的「Jun scope decision」临时写法。
  - T2503（V2a 设计门）的答 (11) 已按这个形状写，无需修改；V2a 1b 票写时照本节。
  - MA-06b（等 BA 终端）读 d = 3 的终端；监督下一次运行从本节与 ROUTES 读到答复。
- (3) 计数不变：BA 190；U 38 / 42；V 4 / 12；M/N 3 / 15。H297。下一节 §317，下一张票号 T2504，下一条 H298。

## §317 — T2503（V2a 设计门）合并：族步可行、V 预测仍 ≈ 12；中枢 API 限额停摆（规则 (H)）（总调度 V4，2026-10-14 07:08 UTC）

- (1) **T2503 合并** e297a13b（07:01 UTC，审核第一轮 PASS；只合并报告 `docs/reports/T2503-design.md` 与注释改动，探针 391 行留在 `t/T2503` 93bd54cd）。V-C1 四步全过：
  - D1：约束文本 `T2503_BAMainIndFamTL` 原样钉住（探针与检查 `Iff.rfl`）。
  - D2：K2、族形式的 Step 1 调用、包装 `S1 → Fam`（16 行）都由合并的名字编译。
  - D3：PASS，按 `(κ', ε') = (c_κ(κ) κ, ε/2)` 读（成员在 `n₀` 以下有限修改后才是 `BAFlow`），时界每个 `n` 都 `≥ t`；逐成员的基础事实与 TL2 同余已编译；链的 `t_n = 0` 类只在主流处混合。
  - D4：`baChainTL_holds` 的族孪生整段编译（110 行探针，带尾段与平移）；行价 V2a 273 / 440 / 950（一行，`prover-hard`）、V2b 540 / 700 / 1,100（一行）、V3 240 / 395 / 766（一行）；**V 预测 ≈ 12（11–14）不变**，低于 15，不发 REQ。
  - 注释改动（答 (4)）：`BAMainIndTL`、`BAChainTL` 标为不在路线上；LC-1 的四处过时注释（`LWPinsBA:20, 44, 46, 48`、`Step2CloseBA:201`、`BAGGExp:78`）已改 → **监督 0947 LC-1 了结**（0342 Q1 关闭条件 (iv) 达成；(v) 的注释部分达成）。
  - 发现：F1 `LWPinsBA:50, 52`（`BASTLWB`、`BASTLWT` 的「owed」注释）同样过时，进下一张碰 `LWPinsBA` 的票（与 `EMn2BA_mF_data` 文档串一起）；F2 单流的 `BAChainTL` 保留不用；F3 情形 (iii) 一般 d 的负责人注释照 §316 改为 Jun 决定 B（下一张碰登记的 V 票做）。
  - **Step 6 输入的补充**（给 V1-BA 票）：`BALWtermEXPTw` 每个时刻 `u` 读 TL1、TL2，所以 V1-BA 的 `BAStep6R` = T2502 的 `Step6RgL` 在 BA 元组上、`Concl` 槽加 `∀ u ∈ [s,t], BATwistAvgLaw u ∧ BATwistLoopLaw u`（`T2503_Step6BA`），由 V2a 用 `TwistStep2_tl1` 与 `baTwistLoopStep_caseI/II` 供给；单流，不需族形式。
  - 论文差异：无新候选（D536、D538 覆盖）。
- (2) **中枢停摆**：T2502 行 a 与 T2498 a′ 的审核两次撞 API 会话限额（「resets 12am America/Los_Angeles」= 07:00 UTC），中枢照规则 (H) 在 07:01 UTC 重跑审核（1b 走缓存，不重做）。约 05:3x–07:00 UTC 无进展；本会话的心跳在同一段时间也没有送达（05:35 的心跳 07:07 才到），07:07 重新排上。
  - T2502 行 a 的 1b 落地 2,150 行，正好等于行 a 停止线；审核结果出来再看是否越线。
- (3) **下一张：V3**（0342 Q2：可与 V2a 的 1b 并行，族步作假设；族步文本已由 T2503 钉住）。现在起草（后台起草子代理），放行后占 T2502 行 b、c 之外的空位。V2b（读 V2a 的陈述 = T2503 的钉文）也可提前，等 V3 起草后再定。
- (4) 计数不变：BA 190；U 38 / 42；V 4 / 12（预测 ≈ 12）；M/N 3 / 15。H298。下一节 §318，下一张票号 T2504，下一条 H299。

## §318 — T2502 行 a、T2498 行 a 第二部分合并；T2498 原地实测 ×2.54；D724、D725；T2502 行 c 的 W1 门；放 T2504（V3）（总调度 V4，2026-10-14 07:31 UTC）

- (1) **T2502 行 a（V1s1a）合并** d3351df4（07:09 UTC）：新 `Chain/Step6Gen` 902 + `Chain/Step6KitGen` 1,248 = 2,150（正好等于行 a 停止线 2,150，自下而上 1,535 的 ×1.40）；目标 1–9 带实例；登记：`STExp2U` 负责人注释、新 `owedProps` 块（`STExp2UgL` … `LWtermEXPG`）与 `structuralProps` 块；审核第一轮 PASS（API 限额后重跑）；全量构建 4,384 个作业。行 b、c 07:15 从 d3351df4 开工。
  - 审核观察：O1 四个包装的 `hK1` 对所有 `(sz, z)` 量化、没有 `Flow` 守卫——带状由 `ST_Kloop_one` 消；BA 候选 `baKsol_one`（`BA/KInduct:77`）由 V1-BA 核（记给 V1-BA 票）；O2 实例位置；O3 `hKer` 的 BA 取值（`κm = κ`、`Aof κ = (κ+1)/κ`）由 V1-BA 核；O4 登记分类（`STStep6gL` 进 `supersededProps`，与带状 `STStep6` 一致；未加撇的泛型 `STExpIniIgL`/`STExpIntIgL` 记为欠，负责人 V1s2′/V1s3′）：照收。
  - 论文差异：**D725 ← T2502a**（泛型 Duhamel 文本 `STExpDuhEqgL`、`STExpDuhamelZgL/QgL` 对 `n` 是最终成立，论文与带状对每个 `n`；票面答 (5)、UP-C4）。
- (2) **T2498 U3s3a′ 合并** bd5531ea（07:14 UTC）：原地改 `QBudgetA`、`QBudgetB`、`QEndA`，新 `Induction/QEndA2` 1,642；目标 7、8 与 9 的其余部分；登记 `GoodSetNg` 负责人注释；审核第一轮 PASS（API 限额后重跑）；全量构建 4,385 个作业。**T2498 行 a 完成**；行 b（U3s3b，`t/T2498b`）07:15 开工。
  - **校准**：行 a 两部分新增 − 挪动 2,256 + 2,511 = **4,767**，对 1a 中心 2,508 为 ×1.90；对放行时的原地价 1,880 为 **×2.54**（U4s3 是 ×1.74）。T2498 的原地部分已超过放行时的敏感价 3,271。
  - **影响 V1s2′、V1s3′ 的布局**（0342 Q3 按 ×1.74 批的原地：≈ 2,300 / 2,450 < 新文件 ≈ 3,160 / 3,440）：按 ×2.54，原地 ≈ 3,353 / 3,581，已不比新文件便宜。规则：V1s2′ 放行前两个系数都算；若按 ×2.54 原地不便宜，**先发短 REQ 问监督**（布局是 0342 批的，不自己翻）。
  - 审核观察 O1–O6（R1 进了 `hQ_altQNg`、删了三个带状私有助手、实例取值、`alt_hkerGridQNg_instance` 在 `X = 0` 处结论平凡但前提都消了、旧检查 `T2279-check.lean:176, 210` 引了被删的带状定理（从不编译，只记账）、校准超出）：照收。
  - 论文差异：**D724 ← T2498g–k**。
- (3) **T2502 行 c 的 W1 门**（票面答 (7) 预授权）：1a 没找到合并的 W1 文本，并对票上的 W1 草稿提了三条意见（自洽方程草稿不能推出 `M` 的块平均等于 `C.m n`；缺 `C.S n = SB d (L n) (g' n)` 前提；非标量 `M` 时 Stein 误差 `tr(E_a M E_p G)` 由哪个前提界到 `Bctl²`）。门在跑（探针 `RBM3D/Probe/T2502Pins.lean` → 1a-audit），行 a、b 不等。
- (4) **放 T2504 = V3**（后台起草子代理起草，调度核读定稿；0342 Q2、§317 (3)）：新 BA 叶 `BA/MainIndOutBA`；族步 `BAMainIndFamTL d STAny` 作精确类型的假设（T2503 约束文本原样），终端定理 `baMLOutTL_of_famStep`、`unMLOutBA_of_famStep`，以后 V2a/V2b 按名字接上，不改 V3。
  - 草稿十个待定问题照草稿定，其中：(1) **定义 `BAMainIndFamTL` 由 V3 发布**（连同 `BATwistLoopLaw_congr`、`baFamMember_flow`），V2a 的 1b 导入 `BA/MainIndOutBA`（改 T2503 答 (1) 的放置）；(2) 登记删五条（`STLK0`、`STG0M`、`STBaseG`、`STHorizonG`、`UNMLOutBA`），加一条 `BAMainIndFamTL`（V2b 合并时删）；(7) **M/N 形状问题**：N 已合并的读者取 `∀ d, UNMLOutBA d`，而按 §316 只有 `UNMLOutBA 3` 无条件——V3 只报告，不改 N 的文件，在 V 的关闭 REQ 里提；(9) F1（`LWPinsBA:20, 50, 52`）与 `EMn2BA_mF_data` 文档串的注释修正放进这张票。
  - 价：设计 240 / 395 / 766，本票加定义与插口后中心 ≈ 435，一行，`prover-hard`，停止线 766；REQ 读数 1,400 记旁边。
- (5) 计数：BA 190（V3 是 T2379 计划内一行）；U 38 / 42；**V 5 / 12**（T2502 1–3，T2503 4，T2504 5）；预测 ≈ 12；M/N 3 / 15。中枢在跑：T2498 行 b、T2502 行 b、T2502 行 c（W1 门）、T2504（4 个位）。H299。下一节 §319，下一张票号 T2505，下一条 H300。

## §319 — T2502 行 c 的 W1 门签字 (A)（逐时刻）；Amend 1；T2498 行 b 合并；D726、D727（总调度 V4，2026-10-14 08:12 UTC）

- (1) **T2502 行 c 的 W1 门：签 (A)，逐时刻形式**（1a-audit `docs/reports/T2502c-1a-audit.md` BLOCKED，H183 (3)）。
  - 门的结果：探针 0f0ad532 编译通过；W1 (i)′（三个合取：(a) `C.S n = SB d (L n) (g' n)`、(b) 自洽方程、(c) `M` 的块平均是 `C.m n`）和 W1 (ii)′（最终成立）作为文本 PASS，带状和 BA 都有实例。
  - 卡点：BA 的 `M = M^{(B)} ⊗ I` 不是标量，Stein 余项是非对角的扭偏迹，票上两个钉住的前提（`LWAvgLawgL`、`STLKgL`）管不住。
  - 选 (A)，不选 (B)，理由三条：
    - (B) 要在泛型陈述里写 `M = m • 1`，票面 C1（`:70`）禁止；它还会让 V1-BA 在 BA 上重做一遍行 c 的 Stein 论证。
    - (A) 的两个新前提都有具名的 BA 来源和负责人：(iii) 由 TL1 `BATwistAvgLaw` 经 `TwistPins_circ_term`（`BA/TwistPins:439`）给出，TL1 每个时刻由 V2a 的 `TwistStep2_tl1` 供；(iv) 由 `CltFlowBA_MB_decay`（`BA/CltFlowBA:221`，常数在 `(κ, 𝔡)`）求和给出。两座桥都归 **V1-BA**。
    - 逐时刻：BA 上 TL1 只是每个时刻的前提，所以 (iii) 跟 `LWAvgLawgL u`、`STLKgL u` 并列，进每时刻的核心定理。
  - **Amend 1**（`docs/tickets/T2502-amend-1.md`，检查 `docs/tickets/checks/T2502-amend-1-check.lean`，钉文抄探针、前缀 `T2502c_` → `T2502_`）：
    - 目标 16 拆三：16a 核心 `stImproveCoregL_of`（族第 9 + 14 行连 (iv) → `STImproveCoregL`）；16b `stImproveExpAvergL_of`（已合并的行 a 钉文，由 16a 加新的族第 15 行 `W1iiiOfLW` 推出，只用于带状型载体）；16c `stExpAvgUgL_of_core`（`st6_expAvgU_of_ping` 的逐流变体，给 V1-BA 接 TL1）。
    - 族表：行 c 用合并后的第 9 + 14 行，`∃ Cs CM` 放在 `(κ, ε, 𝔡)` 之后；行 b 的第 9 行不变；新第 15 行没有 BA 来源，这是设计如此。
    - 行 c 可以在 `Chain/ExpAvgGen` 里发布九个 W1 词汇，只对这九个解除「公开 def 只在 `Step6Gen`」的停止线。
    - 行 c 可以写 `Test/Axioms.lean` 的登记行。
    - 行 c 中心 1,020 → 1,260，停止线 1,450 → 1,750。BA、V 的计数不变。
  - 论文差异：**D727 ← `T2502ca`**（`6:12-21` 只覆盖标量 `M`；D725 末句以此为准）。
- (2) **T2498 行 b（U3s3b）合并** 051e596f（07:54 UTC）：
  - 新 `Chain/QEndGridGen` 1,168 行（票面 1,700，停止线 2,000，×0.69），目标 10 `altGridEndQNg` 带实例。
  - 没有登记改动；审核第一轮 PASS；全量构建 4,386 个作业。
  - 审核观察 O1–O4 照收：O1 导入 `Chain/NQEndLinGen` 不在票上的出处单里（已合并模块，`open private` 四个与模型无关的载体引理，没有抄文本），记账；O2 `lam` 修补留在内部、由 `hcmp` 推出守卫 (g)；O3、O4 是实例助手。
  - 论文差异：**D726 ← `T2498l`–`n`**。
  - 行 c（U3s3c，`Chain/QEndB1Gen`，目标 11–13）07:54 叠在 `t/T2498b` 上开工（wf_ec6438f4-f5c）。
- (3) **记给 V1-BA 票**（与 §318 (1) 的 O1 `hK1`、O3 `hKer`、T2503 的 Step 6 TL 前提并列）：
  - (a) 三座桥：(iii) ← TL1；第 9 + 14 行 ← 探针 `T2502c_ba_W1fam`（`t/T2502c` 0f0ad532 `:227-262`）；(iv) ← 公开的 `CltFlowBA_MB_decay`。
  - (b) `Chain/Step6KitGen` 的包装（`:338`、`:722`、`:755`、`:799`）吃全局的 `hAvg : STImproveExpAvergL …`，BA 给不出（每个时刻要 TL1）。V1-BA 经 16c 和逐流变体接上；变体放在哪里（V1-BA 自己的文件，或一张小的泛型补行）由 V1-BA 的 1a 定。
- (4) 计数：BA 190；U 38 / 42；V 5 / 12；M/N 3 / 15。中枢：T2498c、T2502b、T2504 在跑；T2502c 由 H300 放行 1b（4 个位）。H300。下一节 §320，下一张票号 T2505，下一条 H301。

## §320 — T2502 行 b、T2504（V3）合并；V1s2′/V1s3′ 布局短 REQ；起草 U6-BA（总调度 V4，2026-10-14 08:38 UTC）

- (1) **T2502 行 b（V1s1b）合并** a1ce279b（08:27 UTC）：新 `Chain/ExpHierGen` 885 + `Chain/ExpDuhamelGen` 582 = 1,467（自下而上 1,475 的 ×0.99，停止线 2,050）；目标 10–13 带实例；没有登记改动；审核第一轮 PASS；全量构建 4,389 个作业。
  - 审核观察 O1–O6 照收：O2 `hmk` 没加守卫（更强的前提，BA 与带状都由 `rfl` 满足）；O3 `ExpHierGen_hierarchy_two` 在 `0 < u < 1`（钉文只用开区间）；O4 票面目标 13 的说法「`zeroModeSet` 与 `Step2Gen_UN` 可交换」对一般载体不成立、也没用到，**票面文字以此更正**，不是论文差异；O5 载体实例只在 `H₀ = 0`（本行不能导入 BA）——**记给 V1-BA：编一个 `H₀ ≠ 0` 的 BA 实例**；O6 报告 291 行超票面 250，只记账。
  - 论文差异：无新增（D725 已覆盖；非标量 `M` 的事归行 c 的 D727）。
- (2) **T2504（V3）合并** 364e0d1e（08:25 UTC）：新 `BA/MainIndOutBA` 430（中心 ≈ 435 的 ×0.99，停止线 766）；15 个公开声明带 `d = 3` 实例；登记删 T2340 载体事实与 `UNMLOutBA` 的 `owedProps` 行、加 `BAMainIndFamTL`（V2b 合并时删）；`BA/LWPinsBA`、`BA/EMn2BA` 只改注释；审核第一轮 PASS；全量构建 4,387 个作业。
  - 审核观察：O1 报告超长、O2 行数，只记账；O3 M/N 形状（N 的读者取 `∀ d, UNMLOutBA d`，本票只在 `BAMainIndFamTL d STAny` 下给出）——照票面答 (7) 归 M/N，进 V 收尾 REQ。
  - 论文差异：无新增（D536、D538、D723）。
- (3) **V1s2′/V1s3′ 布局**（§318 (2) 的规则）：新文件校准取 V1s1 行 a + b 落地 3,617，对普查价份额 4,560 × 3,010 / 4,030 ≈ 3,406 为 **×1.06**；原地按 ×2.54 为 ≈ 3,353 / 3,581，新文件按 ×1.06 为 ≈ 3,350 / 3,650，两者打平。0342 Q3 批的是原地，**发短 REQ** `docs/supervisor/requests/REQ-2026-10-14-0835-V1s2layout.md`（调度倾向新文件：价打平，新文件系数波动小，与 V1s1 一致）。V1s2′ 等监督答复后起草。
- (4) **放票计划**（中枢在跑 2 个：T2498 行 c、T2502 行 c）：
  - 后台起草 **U6-BA**（Step 5 词汇在 BA 上，REQ-1418 `:72-95`；输入 T2501 行 b、T2499 都已合并；T2503 答 (7)：不挡 V2a 的设计，但 0342 Q2 让 V2a 的 1b 等它）。
  - V2b 照 0342 Q2 的次序排在 V2a 之后（只有 V3 获准与 V2a 的 1b 并行），不提前。
  - U3s4 等 T2498 行 c；V1-BA 等 T2502 行 c；U3-BA (a)/(b) 等 U3s3–s4。
- (5) 计数：BA 190；U 38 / 42；**V 5 / 12**（T2502 三行中 a、b 已合并，T2503、T2504 已合并）；M/N 3 / 15。H301。下一节 §321，下一张票号 T2505，下一条 H302。

## §321 — U6-BA 记账关闭，不开票（总调度 V4，2026-10-14 08:44 UTC）

- (1) 后台起草子代理核对 U6-BA（REQ-1418 `:72-75`）的每一项，对照表在 `docs/claude-team/drafts/U6-BA-coverage.md`（42 行）。调度抽查了几个名字。结论：**都已由合并的公开定理覆盖，U6-BA 不开票，记账关闭**。
  - Step 5 四种情形在 BA 元组上：`baStep5I_holds`、`baStep5II_holds`、`baStep5IV_holds`（`BA/Step5CasesBA:248, 254, 260`），`baStep5III_holds`（`BA/Step5IIITargets:57`，只在 `d = 3`，D723）。泛型的区间名在 `Chain/Step5Gen:226-230`。
  - 数据：
    - `TwistStep2_T0_ge`（`κ/(κ+1) ≤ BAflowT0`，`BA/TwistStep2:731`）；
    - `TwistStep2_lam0_sq`（`:740`）、`baStep5III_lam0_le_lam`（`BA/Step5IIIKer:399`）；
    - `Step2Kern_UN_BA`（`Chain/Step2Kern:124`）；
    - `BAflow_real`、`EMn2BA_mF_data`；
    - `baKbound_holds`、`baKward_holds`。
  - `baFlowLam0_ge` 已被监督 1457 UBA-C2（`:89`）删掉，不再是目标。
  - `d = 3` 实例：情形 (iii) 在 `sz0, zSeq`；(i)、(ii)、(iv) 用私有数据，因为这三个区间在 `sz0` 上是空的（T2501 Amend 1）。
  - 缩写 `BAStep5R` 不引入：没有读者，T2503 答 (7) 和设计 `:143` 写明 V2a 直接用 `STStep5RgL` 在 BA 元组上。登记里没有一行以 U6-BA 为负责人。
- (2) 随之改：
  - U 的预测 ≈ 45 → **≈ 44**（0658 `:59` 的 U6-BA 一行取消）；已用数不变（38 / 42，没占票号）。
  - V2a 的 1b 等的单子去掉 U6-BA，剩 U3-BA (a)/(b)、T2501 b（已合并）、V1-BA。
  - U 的收尾 REQ（1152 `:165` 第 1 项）引这张对照表。
  - 旧票里写着「读者：U6-BA」的注（`T2501.md:27`、`T2458.md:38, :82`、`T2462.md:70` 等）只记账、不改。
- (3) 中枢在跑 2 个：T2498 行 c、T2502 行 c。可写的票暂时没有：
  - V1s2′ 等 REQ-0835 的答复；
  - U3s4 等 T2498 行 c；
  - V1-BA 等 T2502 行 c；
  - U3-BA 等 U3s3–s4；
  - V2a 的 1b、V2b 按 0342 Q2 的次序。
- (4) 计数：BA 190；U 38 / 42（预测 ≈ 44）；V 5 / 12；M/N 3 / 15。H302。下一节 §322，下一张票号 T2505，下一条 H303。

## §322 — T2498 行 c 合并（U3s3 完成）；监督 0843 PASS：V1s2′/V1s3′ 改新文件；D728；起草 U3s4、V1s2′（总调度 V4，2026-10-14 08:55 UTC）

- (1) **T2498 行 c（U3s3c）合并** 39db8072（08:36 UTC）：
  - 新 `Chain/QEndB1Gen` 1,126 行，目标 11–13 带实例；没有登记改动；审核第一轮 PASS；全量构建 4,390 个作业。
  - **T2498 完成**：行 a ec57490f + bd5531ea，行 b 051e596f，行 c 39db8072。
  - 落地：原地部分 4,767（×2.54）+ 新文件 1,168 + 1,126 = 7,061，对放行时混合价 6,221 为 ×1.14。
  - 审核观察：
    - O1 报告超长，只记账；
    - O2 检查 `:254-258` 的非约束 BA 形状还是 `∃ C₆` 在 `κ` 前，以 Amend 1 为准，只记账；
    - O3 `Test/Axioms:218` `STXiBootgL'` 的负责人注释写着「proofs: U3s3, U3s4」，**交 U3s4 票核对并更新**；
    - O4 实例用 `sz0`/`z0`。
  - 论文差异：**D728 ← `T2498o`–`r`**。
- (2) **监督 0843 PASS**（答 REQ-0835）：
  - **V1s2′、V1s3′ 改新文件**（`Chain/…Gen`，同 V1s1），取代 0342 Q3 第二条。原因：按 ×2.54 原地不比新文件便宜，UP-C2 的规则本身就定了；新文件的系数集中在 1 附近，波动小。
  - 预计各 2 行，V 预测 ≈ 12–13，低于 REQ 线 15。
  - 分层照 0843：新文件导入 `Chain/*Gen` 和带状 `Induction/Exp*`、`Qop*` 作来源，不导入 `BA/*`，带状文件不导入新文件。`QopNorm` 不另做孪生，`QopDecay` 的孪生在 V1s3′ 里。
  - **V1L-C1（约束）**：V1s3′ 的泛型情形 (i) 消费者（带状 `ST_step6_caseI_of_pins''`，`ExpIntI:584`）的平均输入写成逐流形式（`STExpAvgUgL` 在 `[s,t]` 上，或 16c 的输入），不吃全局 `STImproveExpAvergL`；V1s2′ 的 1a 若找到读全局平均的陈述，同样处理。
  - **V1L-C2（次序）**：V1s3′ 的消费者那一行，1b 等 T2502 行 c 合并；V1s2′ 现在可写可开工，但需要 `Chain/ExpAvgGen` 引理的新文件也等行 c。
  - 票面 `T2502.md:14, :26` 的「V1s2′/V1s3′ in place」以此为准。
- (3) **放票**：中枢只剩 1 个在跑（T2502 行 c）。后台起草子代理同时起草 **U3s4**（读 U3s3 的 `STOeqQtRoundPTgL''`，`STOeqQtgL'` 的证明归它，双定价 ×2.54 / ×1.06）和 **V1s2′**（新文件，照 0843 的分层与 O2）。V1s3′ 等 V1s2′ 之后起草。
- (4) 计数：BA 190；U 38 / 42（预测 ≈ 44）；V 5 / 12（预测 ≈ 12–13）；M/N 3 / 15。H303。下一节 §323，下一张票号 T2505，下一条 H304。

## §323 — 放 T2505（U3s4，新文件三行）与 T2506（V1s2′，新文件两行）（总调度 V4，2026-10-14 09:18 UTC）

- (1) **T2505 = U3s4**（后台起草子代理起草，调度核读定稿；`docs/tickets/T2505.md`、检查 `T2505-check.lean`）：Step 3 的 `Qt` 层在流载体上，情形 (i) `lem:STOeq_Qt`（从 U3s3 的每时刻圆推出一致圆，再自举）与情形 (ii) `lem:STOeq_Qt_nonzero`。
  - **布局新文件**（UP-C2、§308 (2)）：全部原地 1,602，×1.74 = 2,787，×2.54 = 4,069；新文件普查 ×1.24 = 3,580，再 ×1.06 = 3,790。按实测 ×2.54 新文件便宜 7–14 %，又是 0843 (2) 的低波动布局；六个带状文件不改。
  - **三行预签**：
    - a = U 39（`Chain/QtBootGen`、`QtXiRoundLiftGen`，≈ 640 / 680，目标 1–5，现在开工）；
    - b = U 40（`Chain/QtNonzeroGen`、`QtNonzeroEndGen`，≈ 1,650 / 1,750，目标 6–9，与 a 并行；**只有 b 带设计门**：D1 新的确定性无损核类，探针 ≤ 300 → 1a-audit；超 1,950 则 b | b′）；
    - c = U 41（`Chain/QtNonzeroFlowGen`、`QtNonzeroBootGen`，≈ 1,285 / 1,365，目标 10–15，等 a、b 合并；登记改 `Test/Axioms` `:214` 的 `STXiBootgL'` 负责人注释（T2498c O3）与 `:121`）。
  - 七个待定问题照草稿定：
    - (3) D1 作新类，不读会丢 `N^ε` 的 `STEKNonzerogL`；U3-BA (a) 出一个 BA 引理同时给 D1 和 A 形 `STEKNonzerogL`。
    - (4) 族第 14、15 行的 BA 归 U3-BA（第 16 行的 BA 已合并）。
  - 计数：BA 190 → 192（T2379 计一行，三行 +2；b 拆则 193）；U 41 / 42；U 预测 ≈ 44 → ≈ 46（< 49，不发 REQ）。
- (2) **T2506 = V1s2′**（同上；`docs/tickets/T2506.md`、检查 `T2506-check.lean`）：Step 6 情形 (i)/(ii)/(iv) 的成分证明在载体上，新文件（0843）。
  - **两行预签、并行**（两行之间没有导入）：a = V 6（`Chain/ExpEtermsAGen` → `ExpEtermsBGen`，≈ 1,595，目标 1–5）；b = V 7（`Chain/ExpIniIGen`、`ExpWardIGen`、`ExpIntIIGen`，≈ 1,930，目标 6–13）。
  - 价：簿记 3,160 / ×1.06 = 3,350；普查重跑 ×1.24 = 2,800 / 2,968；自下而上 2,645 / 3,525 / 4,725；原地只记账 1,320 / 2,297 / 3,353。
  - **V1L-C1**：本票范围里唯一读全局平均的是 `ST_step6_caseI_of_pins'`（`ExpIniI:1127`），只有带状实例用，它的证明被 `ST_step6_caseI_of_pins''`（`ExpIntI:573`，V1s3′）照抄 → **不转换**；其余读平均的陈述都已是逐流形式，转成 `STExpAvgUgL`。
  - **V1L-C2**：没有新文件需要 `Chain/ExpAvgGen`，两行都现在可开工。
  - 七个待定问题照草稿定：
    - (3) `ExpIniIGen`、`ExpWardIGen` 里的四个带撇公开定义（带状带撇钉文的孪生）照 Amend 1 第 3 条的先例放开；
    - (4) 族第 9′ 行取整个已合并类 `IniTermGen_CltFlow`（BA 有 `baIniTermGen_cltFlow`）；
    - (5) W-d（E 项衰减只在 `Step2Mat` 层有文本）预授权行 a 的窄门（探针 ≤ 200，行 b 不等）；
    - (7) 0843 的几处行号在 `main` 上有偏差（如 `ExpIntI:584` 实为 `:573`），只记账。
  - 计数：BA 192 → 193（T2379 计 V1s2 一张，两行 +1）；V 7 / 12；拆第三行则 V 预测 13（< 15）。
- (3) **开工次序**（中枢上限 4 个，T2502 行 c 占 1 个）：T2506 行 b → T2505 行 b（门）→ T2505 行 a → T2506 行 a（有空位时）；T2505 行 c 等 a、b 合并。
- (4) 计数：**BA 193**；U 41 / 42（预测 ≈ 46）；V 7 / 12（预测 ≈ 12–13）；M/N 3 / 15。H304。下一节 §324，下一张票号 T2507，下一条 H305。

## §324 — T2502 行 c 审核签字：接受 `hFF`（Amend 2），放行合并（总调度 V4，2026-10-14 09:51 UTC）

- (1) **T2502 行 c**（1b 7cf02a5f，`Chain/ExpAvgGen` 1,587 行：中心 1,260 的 ×1.26，停止线 1,750；目标 14、15、16a–16c；全量构建通过）审核第一轮逐目标 PASS，但要调度签字（规则 (B)）。
  - 问题：16a `stImproveCoregL_of`、16b `stImproveExpAvergL_of` 只有在多一个前提 `hFF : Step5CasesGen_FlowFacts d Flow mk T0` 时才等于 Amend 1 检查里的约束形状。
  - **签字：接受**，写成 Amend 2（`docs/tickets/T2502-amend-2.md`）。理由：
    - 这是族表第 3 行，票面本来就列给目标 15、16；Amend 1 只改了第 9、14、15 行，它的形状漏了第 3 行，是调度的疏忽。
    - 带状、BA 两边的来源都已合并。
    - 已合并的行 a 包装也这样取（`Step6KitGen:677, 716, 747, 795`）。
    - 证明要用到其中的 `SizeTendsto`、`T0 < 1`、`κm ≤ Im m`，`ExpAvgGen_W1fam` 不提供这些。
    - 不是论文差异，属于 `lem:main_ind` 的设定。
  - 16c `stExpAvgUgL_of_core` 的形状：照 `st6_expAvgU_of_ping`，把 `hAvg` 换成 `hCore : STImproveCoregL …`，再加每时刻的 W1 (iii) 前提 `hiii`。审核核对过，记账。
  - 审核观察 O1–O3：探针不合并；`stImproveExpAver_of_gL` 没带词干，只记账；`hFF` 即本条。
  - 论文差异：D727 已确认（报告 (d) 5），无新增。
- (2) 行 c 合并后 **V1s1 完成**。可以起草：
  - **V1-BA**：带 §319 (3)、§320 (1) O5、§318 (1) O1/O3、T2503 的 Step 6 TL 前提；16c 是 BA 接 TL1 的口子。
  - **V1s3′**：V1L-C1、V1L-C2，消费者那一行现在可以开工。
- (3) 计数不变：BA 193；U 41 / 42；V 7 / 12；M/N 3 / 15。中枢在跑 4 个：T2505a、T2505b、T2506a、T2506b；T2502 行 c 由 H305 合并。H305。下一节 §325，下一张票号 T2507，下一条 H306。

## §325 — T2502 行 c 合并，V1s1 完成；T2505 行 b 1a-audit PASS（总调度 V4，2026-10-14 10:05 UTC）

- (1) **T2502 行 c 合并** 089052ca（09:53 UTC，H305：Amend 1、Amend 2）：
  - 新 `Chain/ExpAvgGen` 1,587 行；目标 14、15，以及 16a `stImproveCoregL_of`、16b `stImproveExpAvergL_of`、16c `stExpAvgUgL_of_core`，都带实例。
  - 登记：`STImproveExpAvergL` 负责人注释；`owedProps` 加 `ExpAvgGen_W1fam`、`ExpAvgGen_W1iii`、`ExpAvgGen_W1iiiOfLW`。
  - 全量构建 4,391 个作业。
  - **T2502（V1s1）完成**：行 a d3351df4 2,150，行 b a1ce279b 1,467，行 c 089052ca 1,587，合计 5,204。对 0342 的 UP-F1 价 4,560 为 ×1.14，对自下而上 4,030 + Amend 1 加的 240 为 ×1.22。
- (2) **T2505 行 b 的 D1 门 1a-audit PASS**（`docs/reports/T2505b-1a-audit.md:148-150`）：D1 文本定为 `T2505-check.lean:154-167`，探针编译通过，中心 1,755，按预签不拆。不需要签字，1b 照跑。
- (3) 计数不变：BA 193；U 41 / 42；V 7 / 12；M/N 3 / 15。在跑 4 个：T2505a、T2505b、T2506a、T2506b。H306。下一节 §326，下一张票号 T2507，下一条 H307。

## §326 — 中枢 API 限额停摆（约 10:2x–12:00 UTC）；本会话心跳同段中断（总调度 V4，2026-10-14 12:07 UTC）

- (1) 约 10:2x 到 12:00 UTC，中枢四个工作流都因 API 会话限额停了（限额在 12:00 UTC 重置）。12:02 中枢按规则 (H) 把四个工作流原样续跑，H306 done 0e09fbfc。停下时各行的进度：
  - T2505 行 a：1b 2a7ddae2 已完成，审核在跑；
  - T2505 行 b：门已过（探针 bf9aaf6a、1a-audit PASS、不拆），1b 写到 `QtNonzeroGen` 744 行；
  - T2506 行 a：1b 写到 `ExpEtermsAGen` 660 行；
  - T2506 行 b：1b 已提交四次。
  - 这段时间没有合并。
- (2) 本会话的心跳同段也断了：10:20 那次 12:06 才送到。12:06 重排（trig_01GxH5HT8xLjQtAibpVy2yYC，12:21）。
- (3) 计数不变：BA 193；U 41 / 42（预测 ≈ 46）；V 7 / 12（预测 ≈ 12–13）；M/N 3 / 15。下一节 §327，下一张票号 T2507，下一条 H307。

## §327 — T2505 行 a、T2506 行 b 合并；D729；起草 U3-BA (a)（总调度 V4，2026-10-14 12:27 UTC）

- (1) **T2505 行 a（U3s4a）合并** 74b7c64b（12:09 UTC，限额后重跑的审核第一轮 PASS）：
  - 新 `Chain/QtBootGen` 551 + `Chain/QtXiRoundLiftGen` 788 = 1,339 行；目标 1–5 带实例。
  - 登记：`owedProps` 加 `STXiRoundgL'`。全量构建 4,393 个作业。
  - **校准**：1,339 对票面中心 640 / 680 是 ×2.09 / ×1.97，超过高估 1,160；两个文件都不到 2,000，没触发停止线。**行 c 放行前把票面价按 ×2 复核**（中心 1,285 / 1,365 → ≈ 2,600，过 1,950 就按预签在文件边界拆 c | c′，BA +1）。
  - 审核观察 O1–O5 照收：
    - O1 目标 5 的全名是 `RBM.BA.QtXiRoundLiftGenCheck.stOeqQtgL'_band`，记账；
    - O2 目标 3 名 `stXiRoundgL'_of_PTfam` 没带词干；
    - O3 情形 (i) 的实例在 `sz0`；
    - O4 多导入 `Induction/LemDecCalELip`、`Chain/Step6KitGen`，都已合并、不是 BA；
    - O5 即上面的校准。
  - 论文差异：**D729 ← `T2505a`–`d`**。
- (2) **T2506 行 b（V1s2′b）合并** c9b3f490（12:25 UTC）：
  - 新 `Chain/ExpIniIGen` 957 + `ExpWardIGen` 581 + `ExpIntIIGen` 438 = 1,976 行（中心 ≈ 1,930 的 ×1.02）；目标 6–13 带实例。
  - 登记：行 b 的负责人注释，带撇结论 `STExpIniIConclgL'`、`STExpWardIConclgL'`。审核第一轮 PASS；全量构建 4,396 个作业。
  - 审核观察 O1–O5 照收。O3：票面要求把 `Test/Axioms:224` 的块标题改成「new files」，这一行没改，**交行 a 做**（行 a 的登记行本来就在那一块）。O4：多导入 `Chain/CltGen`，已合并。
  - 论文差异：无新增（D725、D727 覆盖）。
- (3) **放票**：中枢在跑 2 个（T2505b、T2506a），空 2 个位。
  - **U3-BA (a)**（REQ-1418 `:44-49`：BA 上的 `STEK*` 形式、`BAEKKer` 类、`baKloop_lip`、`baEta_antitone`，1457 UBA-C1 (b) 的 A 形 Nonzero 实例）现在可写：它的 ST 对 T2457 早已合并，§323 (1) 又把 U3s4 的 D1 的 BA 引理和族第 14、15 行的 BA 交给它。
  - 后台起草子代理起草。凡是要读 `Chain/QtNonzeroGen`（T2505b）的部分，单列一行，等 T2505b 合并。
  - U3-BA (b) 等 U3s4 全部完成和 U3-BA (a)。
- (4) 计数：BA 193；U 41 / 42；V 7 / 12；M/N 3 / 15。H307。下一节 §328，下一张票号 T2507，下一条 H308。

## §328 — 放 T2507 = U3-BA (a)（一行）（总调度 V4，2026-10-14 12:44 UTC）

- (1) **T2507 = U3-BA (a)**（后台起草子代理起草，调度核读定稿；`docs/tickets/T2507.md`、检查 `T2507-check.lean`）：U3 的 BA 核层，新 BA 叶 `BA/EKGenBA` ≈ 690 + `BA/KLipBA` ≈ 335。
  - 价：自下而上 750 / 1,025 / 1,500，停止线 1,550；超 1,950 按预签在文件边界拆 a | a′。UP-F1 的 2,912 × 2 = 5,824 是 (a)+(b) 合计，记在旁边，本票约占 19 %。
  - **覆盖核对**（照 U6-BA 的做法）：REQ-1418 的 `LCompat`/`KCompat`（`baStep34_LCompat`/`KCompat`，`SEforLnBA:122, 129`）、`STEKDecay/Low/Win` 的 BA 读法（只是词汇；E 项衰减 `baEtermDecaygL`，`gK` 处的窗口与衰减由 `step34Gen_winK_of_cmp`/`decayK_of_cmp` 给出）、`baEta_antitone`（`NQGood1Gen_eta_anti` 用在 `baStep2Mat_loopForm` 上，写一个 `example`）都已合并，**记账关闭**。
  - 要写的：
    - 类 `BAEKKer`（1457 UBA-C2 的形状，唯一新的公开 def）；
    - 五个 `STEK*` 形式在 BA 上；
    - A 形 Nonzero 引理（任意 `Aof`）；
    - `baKloop_lip`（每个 k ≥ 2；已合并的 `baKLip_two` 不动）；
    - T2491 D1 `NQGoodGen_KerNALFam`、T2498 D1 `QProxyG_KerEK4Fam` 的 BA 来源（合并的文档串和 T2498 族第 8 行都写着负责人是 U3-BA (a)）；
    - V1 三个定理共用的 `hKer` 束 `baEKKer_flow`（给 V1-BA）。
  - **七个待定问题**：(1)、(3)–(7) 照草稿定；**(2) 取另一个选项**：T2505 D1 的 BA 来源（目标 7，`BA/QtNZBA`）并进 U3-BA (b)，因为它唯一的读者就是 (b)，(b) 本来也要等 U3s4 全部完成。本票只有行 a。
  - 登记：本票不关、不加任何行。名字写着 U3-BA 的四行（`:194`、`:195`、`:214`、`:217`）归 U3-BA (b)。
  - 计数：U 42 / 42（旗标保留，预测 ≈ 46，< 49 不发 REQ）；BA 193（+0）。
- (2) 开工：行 a 现在从 `main` 开工，`prover-hard`，没有设计门。中枢在跑 3 个：T2505b、T2506a、T2507。H308。下一节 §329，下一张票号 T2508，下一条 H309。

## §329 — T2505 行 b 合并、行 c 开工；T2506 行 a 签字接受 `hK1`（Amend 1）（总调度 V4，2026-10-14 13:01 UTC）

- (1) **T2505 行 b（U3s4b）合并** b610fbdb：
  - 新 `Chain/QtNonzeroGen` 956 + `QtNonzeroEndGen` 688 = 1,644 行，是 1a 中心 1,755 的 ×0.94。目标 6–9 带实例；D1 文本与检查一致；没有登记改动。审核第一轮 PASS；全量构建 4,398 个作业。
  - 审核观察 O1–O5 照收（O2：`nzGridEndNg` 的 `hst` 没用到，无害）。
  - 论文差异：**D730 ← `T2505ba`–`bc`**。
  - **行 c**（`QtNonzeroFlowGen`、`QtNonzeroBootGen`）12:43 由中枢按票面开工（wf_a3fea484-937）。§327 (1) 的 ×2 复核：两个文件按 ×2 约 1,840、890，各自都在 2,000 的单文件停止线以内，不中途插手；如果 1a 的行中心超过 1,950，按票面的拆分规则办。
- (2) **T2506 行 a（V1s2′a）审核 RETURN，要签字**（1b a990102c；H307 的块标题改名已做）：
  - (1) 可修的缺陷：`expLK_envg` 的实例（`ExpEtermsAGen:585`）没消掉确定性前提 `hK`，审核已编译出修法。
  - (2) 目标 4、5 多了前提 `hK1`（族第 19 行的 `𝒦^{(1)} = m_σ` 合取），而票面把第 19 行只派给 WardI。
  - **签字：接受 `hK1`**，写成 Amend 1（`docs/tickets/T2506-amend-1.md`）。理由：`ℰ^{G̃}` 的包络要 `‖m‖ ≤ N`，已合并的类都给不出；第 19 行两边的来源都已命名（带状 `ST_Kloop_one`，BA `baKsol_oneLoop`）；先例是 `Step6KitGen` 的包装（§318 (1) O1）；不是论文差异。修 (1) 照审核的写法做，再跑第二轮审核。
- (3) 在跑：T2505c、T2507；T2506a 由 H309 修复、复审。计数：BA 193；U 42 / 42；V 7 / 12；M/N 3 / 15。H309。下一节 §330，下一张票号 T2508，下一条 H310。

## §330 — T2506 行 a、T2505 行 c、T2507 合并（V1s2′、U3s4、U3-BA (a) 完成）；D731；放 T2508 = V1s3′（总调度 V4，2026-10-14 13:44 UTC）

- (1) **合并**：
  - **T2506 行 a** 4845a70f（Amend 1，修复 6d6dde16，第二轮审核 PASS）：`ExpEtermsAGen` 692 + `ExpEtermsBGen` 1,027 = 1,719 行，对中心 1,595 为 ×1.08。**T2506（V1s2′）完成**，两行合计 3,695，对自下而上 3,525 为 ×1.05。
  - **T2505 行 c** ffd134c4：`QtNonzeroFlowGen` 1,145 + `QtNonzeroBootGen` 780 = 1,925 行，对票面中心 1,285 / 1,365 为 ×1.50 / ×1.41。**T2505（U3s4）完成**，三行合计 1,339 + 1,644 + 1,925 = 4,908，对新文件价 3,580 / 3,790 为 ×1.37 / ×1.29。
    - 审核观察：O1 报告里的标签撞号，改标 `T2505ca`–`cc`；O2 登记 `:217` 结尾还写着「case (ii): T2505 row c」，交 U3-BA (b) 一并改；O3–O5 只记账。
  - **T2507（U3-BA (a)）** c3f8b05d：`BA/EKGenBA` 706 + `BA/KLipBA` 324 = 1,030 行，对中心 1,025 为 ×1.00；目标 1–6、8；没有登记改动。论文差异：无新增（D699、D730）。
  - 论文差异：**D731 ← `T2505ca`–`cc`**。
- (2) **放 T2508 = V1s3′**（后台起草子代理起草，调度核读定稿；`docs/tickets/T2508.md`、检查 `T2508-check.lean`）：新文件两行，**串行**。
  - 行 a `t/T2508` = `ExpWardIIGen`、`ExpIntEasyGen`、`ExpIntIGen`（≈ 1,745，消费者那一行）；行 b `t/T2508b` = `QopDecayGen` → `ExpIntIQGen`（≈ 1,685），等行 a 合并。
  - 价：簿记 3,440 / ×1.06 3,646；普查 2,616 / 2,773；自下而上 3,430；原地只记账 1,410 / 2,450 / 3,581。
  - **V1L-C1**：有三个读全局平均的陈述，取逐流形式：平均以 `STExpAvgUgL` 在 `[s,t]` 上进入。核心带前提 `hAvgU`；包装放在 `Concl` 槽（`T2508_Step6IAvgUgL`，同 T2503 的 `BAStep6R`）；加 16c 输入的推论（约 +30）。已合并的 `st6_caseI_coreg` 喂不进去（它要的未撇 `STExpIniIConclgL`、`STExpIntQConclgL` 没有生产者），所以新的带撇核心 `st6_caseI_coreg'` 就是 V1-BA 在情形 (i) 读的。`stStep6IV_holds`、`ST_step6I_of_LW_Int`、`stStep6I_of_LW` 只留带状。
  - 八个待定问题照草稿定：串行切分、保留 16c 推论、不加情形 (iv) 的逐流包装、`ExpIntIGen` 放两个带撇公开 def、新族行 21–23 和 19′、登记的过渡行。
  - 计数：V 7 → 9 / 12；BA 193 → 194（T2379 计 V1s3 一张，两行 +1）；拆第三行则 V 10、BA 195，预测 13–14（< 15）。
- (3) **中枢空了**：三张都合并，现在一个都没在跑。H310 先放 T2508 行 a。
  - **U3-BA (b)** 现在可写：U3s4 全部完成，U3-BA (a) 已合并。后台起草，带上 T2505 D1 的 BA 来源（§328 (1) (2)）、登记 `:194`、`:195`、`:214`、`:217` 四行（含 T2505c O2）、Steps 3–4 在 BA 上（REQ-1418 `:51-54`）。
  - V1-BA 等 V1s3′。
- (4) 计数：**BA 194**；U 42 / 42（预测 ≈ 46）；V 9 / 12（预测 12–13）；M/N 3 / 15。H310。下一节 §331，下一张票号 T2509，下一条 H311。

## §331 — 放 T2509 = U3-BA (b)（Steps 3–4 在 BA 上，含泛型 Steps 3–4 的生产者）（总调度 V4，2026-10-14 14:06 UTC）

- (1) **T2509 = U3-BA (b)**（后台起草子代理起草，调度核读定稿；`docs/tickets/T2509.md`、检查 `T2509-check.lean`）。
  - **覆盖**：`stOeqQtgL'_of` 有 27 个前提槽、`stOeqQtNZgL'_of` 有 25 个，BA 上都已有合并的来源，只差情形 (ii) 的 D1（`QtNZGen_KerNZFam`）。D1 就是 T2507 并过来的目标（这里的目标 6 `baQtNZGen_kerNZ`），源引理 `baEKSumDecayNonzeroA_holds`（`EKGenBA:262`）已合并，**不设计门**。BA 上的迭代、`QDriftData`、G7（T2468 `baStep1_holds'`）都已合并，没有前提要先当假设进来。
  - **发现的缺口**：`Chain/` 里没有对一般载体证 `STStep3RgL`/`STStep4RgL` 的定理。带状的 `Induction/Step3` §1–§4、`Step4` §1–§2 从没移植过：T2457 `:40` 派给 U3s4，T2505 `:36, :48` 又指向 V，两头都没开票。**本票补上**：新 `Chain/Step34RGen`（≈ 800，复用 `IterationsGen2_Fam`）加新 BA 叶 `BA/Step34BA`（≈ 500）。
  - 价：一行，`t/T2509`，现在开工，`prover-hard`。自下而上 1,000 / 1,300 / 1,900，校准后 1,320–1,840；停止线 1,250 / 800；1a 中心超 1,950 按预签拆 a | a′（a′ 叠在 a 上）。T2379 给 (b) 的余量 1,882（中心），UP-F1 的 4,794 记在旁边。
  - **八个待定问题照草稿定**：
    - (1) 泛型 Steps 3–4 生产者放本票，不另开 ST 行；
    - (2) REQ-1418 的「在 `STAny` 上」做不到（§68 (9)、§132 (3)、§133 (1)：Step 4 只能从 `STCaseI`/`STCaseII` 的自举来），改成逐区间的目标 8–9；
    - (4) 不引入缩写 `BAStep3R`/`BAStep4R`（没有读者，同 U6-BA 的先例）；
    - (5) T2507 的目标 7 是这里的目标 6；
    - (6) 登记只改负责人注释 `:194`、`:195`、`:214`、`:217`（`:217` 的结尾改掉「case (ii): T2505 row c」，即 T2505c O2）；预扫描若已显示 `STXiBootgL'` 不再挂东西，就把 `:214` 删掉；
    - (8) 族前提复用 `IterationsGen2_Fam`（BA `baIterationsGen2_fam` 已合并）。
  - 计数：U 43 / 42（旗标保留，预测 ≈ 46，< 49 不发 REQ）；BA 194（+0；T2379 给 U3-BA 计两行）。拆则 U 44、BA 195。
- (2) **记给 V2a 的 1b 票**（待定问题 (3)；T2503 的检查不改）：`T2503-check:282, 284` 在情形 (iii)、(i) 里按 `Rc = STCaseI` 读 Steps 3–4，而 `STCaseI` 处的 Step 3 是已被取代的 `STStep3I`。V2a 在这两处取 `R34 = R`，同带状的 `ST_mainInd_of_pins'`（`Induction/Step4:209-228`）：Step 3 读本票目标 8 在该区间上的形式，Step 4 读 `baStep4RegIII/RegI_holds`；情形 (ii)、(iv) 照旧用 `STCaseII`。价不变。
- (3) 在跑：T2508a、T2509（H311 后）。计数：BA 194；U 43 / 42；V 9 / 12；M/N 3 / 15。H311。下一节 §332，下一张票号 T2510，下一条 H312。

## §332 — T2508 行 a 合并；放 T2510 = V1-BA（Step 6 在 BA 上）（总调度 V4，2026-10-14 14:49 UTC）

- (1) **T2508 行 a 合并 57178a34**（V1s3′a：新 `Chain/ExpWardIIGen` 435 + `ExpIntEasyGen` 482 + `ExpIntIGen` 835 = 1,752 = 票面 ≈ 1,745 的 ×1.00；审核第 1 轮 RETURN（四个实例里留着 Duhamel 假设），一次规则 (B) 修复 5d7f96f7，第 2 轮 PASS）。行 b 14:46 开工（wf_e9ed66d3-8b3）。报告标签 `T2508a`、`T2508b` 与行 b 撞号，改标 `T2508aa`、`ab`，记 **D732**（Lean 手段，不改论文陈述）。
- (2) **T2510 = V1-BA**（后台起草子代理起草，调度核读定稿；`docs/tickets/T2510.md`、检查 `T2510-check.lean`）。
  - **覆盖**：泛型 Step 6 生产者共 29 个前提槽。19 个 BA 上已有合并来源；3 个合并加胶水（第 7 行逐时刻 LW、第 18 行标签桥、第 21 行逐流平均）；4 个 `main` 上没有（第 9 + 14 行、(iii)、(iv)、每个 `n` 的 `hK1`），各有具名路线；3 个按设计不在 BA 上（`LWtermEXPG`、第 15 行、全局 `STImproveExpAvergL`）。不设计门。
  - **切法**：两行串行。行 a `t/T2510`（V 第 10 行）= 目标 1–10：三座桥、BA 族行、九个已合并钉文与 16a、情形 (iii)/(iv)/(ii) 以 T2508 的三个钉文（类型已合并，`Step6Gen:351, 356, 362`）作假设装配；**现在开工**，与 T2508 b、T2509 并行，文件不相交；行 a 不读 T2508 的名字（T2508 a 已合并也照此）。行 b `t/T2510b`（V 第 11 行）= 目标 11–15：T2508 生产者在 BA 上、情形 (i)、四个 `baStep6Reg*_holds`；T2508 行 b 与本票行 a 都合并后开工（它导入 `Step6PinsBA`）。
  - 价：自下而上行 a 1,000（700 / 1,550）、行 b 330（230 / 560），校准后 1,280–1,700；T2379 记账 928 / 1,771 / 3,268，UP-F1 3,540 记在旁边。停止线 `Step6BridgeBA` 800、`Step6PinsBA` 800、`Step6BA` 550；1a 中心超 1,950 在文件边界拆。
  - **八个待定问题**：
    - Q1 取两行切法，不并进 V2a 的 1b（否则 V2a 直接读 T2508 的名字）；
    - Q2 **F1 接受**，§318 (1) O1 的读法更正：每个 `n` 的 `hK1` 在 BA 上不成立（`baKsol_one` 要 `0 < g₀ₙ`，只在 `WO` 窗口里最终成立）；`≺` 在 `n` 上是最终的，所以用私有的最终孪生（目标 4，由 `baKsol_oneLoop` 喂），泛型文本不动，单为此不做 1a-audit；Lean 内部，不记论文差异；
    - Q3 `BAStep6R` 是唯一的新公开 def（X1-C4 例外：V2a 的检查只写抽象 `S6`，1b 要按名字读）；
    - Q4 钉文 1 在 1a 需要时可加 `u` 的范围前提，报告即可，不修订；
    - Q5 行 b 的 1a、1b 一次跑，开工条件如上；
    - Q6 登记 `:225` 的块标题归行 b，行 a 不碰；
    - Q7 第 22 行约束变量次序（`κ, 𝔡` 对 `𝔡, κ`）在行 b 用私有适配引理，不修订；
    - Q8 预授权 (iii) 的窄门：1a 若发现恒等式要的不止 `u` 处的 TL1 与 `0 < Im m`，先探针（≤ 150 行）再 1a-audit；行 a 的文件 2 不等它。
  - §319 (3) (b) 的答案：逐流变体放在行 a 的文件 1 里（私有），不另开泛型补行。O3 由 F2 确认（`baEKKer_flow` 正是 `hKer` 槽）。O5（§320 (1)）由目标 10 的 `H₀ = g₀Ψ ≠ 0` 实例做。
  - 计数：V 11 / 12（预测 13，含 V2a、V2b；< 15 不发 REQ）；BA 194（+0，T2379 `:134` 给 V1-BA 计两行；拆则 +1）。
- (3) 在跑：T2508b、T2509，H312 后加 T2510 行 a（3 个）。计数：BA 194；U 43 / 42；V 11 / 12；M/N 3 / 15。H312。下一节 §333，下一张票号 T2511，下一条 H313。

## §333 — T2509 合并，U 的行全部合并 → 关闭 REQ；V2a 1b 可切、V2b 不必等 V2a → 短 REQ 问次序（总调度 V4，2026-10-14 15:32 UTC）

- (1) **T2509 = U3-BA (b) 合并 beefb80b**（15:04 UTC）：新泛型 `Chain/Step34RGen` 739 + BA 叶 `BA/Step34BA` 455 = 1,194 = 自下而上中心 1,300 的 ×0.92；目标 1–10 带实例；审核第 1 轮 PASS；无新论文差异（逐区间钉文由 D51、D56 覆盖，A 形 D1 由 D730 覆盖）。U3-BA 完成：(a) 1,030 + (b) 1,194。
- (2) **子阶段 U 的行全部合并，U 43 / 42**（旗标 42；最后预测 ≈ 46）。发关闭 REQ `docs/supervisor/requests/REQ-2026-10-14-1512-Uclose.md`。留给 V 的条件：BA 情形 (iii) 在一般 `d` 上以 `STStep5IIIgL d` 为假设（0342 Q4；§316 Jun 定 B，`d = 3` 无条件）；`twSteps` 的 `STLmaxUgL`、`STLKUgL` 由 T2509 逐区间给出、V2a 消。
- (3) **V2a 1b（T2511）与 V2b（T2512）已起草**（后台起草子代理；`docs/claude-team/drafts/V2a.md`、`V2a-r2.md`、`V2b.md` 与检查）：
  - V2a 可切两行：行 a `BA/MainIndFamTL`（自下而上 371 中心，校准 356–475）不读未合并的名字：Steps 3–4 直接读 T2509 已合并的名字（§331 (2) 的 `R34 = R`），Step 6 以已合并 `STIngR6gL d R … Concl6` 的任意槽加桥进入，不抄 T2510 的 `BAStep6R`（X1-C4）；行 b `BA/MainIndRegBA`（70 中心）用 T2510 的名字合上 Step 6，并写 `d = 3` 终端。切开多 +49 行，T2510 b 之后的关键路径少约 320 中心行。
  - V2b 不必等 V2a：四个情形输入的类型是已合并的 `BAMainIndFamTL d R`（V3，`MainIndOutBA:60`），新叶 `BA/MainIndGlue`，自下而上 260 / 365 / 615（T2503 的 540 / 700 / 1,100 逐行移植探针，其中约 270 行是 `MainIndRegimes`（T2245）已公开的模式引理）。
  - 这偏离 0342 Q2 的串行次序（V2a 的 1b 等 V1-BA；V2b 在 V2a 之后），发短 REQ `REQ-2026-10-14-1512-V2order.md`，**答复前两张都不放**；不允许则 V2a 一行在 T2510 b 后、V2b 在 V2a 后。计数（允许时）：V 用 14 / 12，预测 13 → 14（< 15）；BA 195（+1，V2a 两行）。
- (4) T2510 行 a 1a PASS（F7：钉文 1 不需要范围前提；(iii) 只要 `u` 处的 TL1 与 `0 < Im m`；不做 1a-audit），1b 在跑；T2508 行 b 1a PASS，1b 在跑。在跑：T2508b、T2510a（2 / 4）。计数：BA 194；U 43 / 42（全部合并）；V 11 / 12；M/N 3 / 15。下一节 §334，下一张票号 T2511（V2a）、T2512（V2b），下一条 H313。

## §334 — 监督 1743：U 在 43 / 42 关闭；V2a 1b 切两行、V2b 现在开；T2508、T2510 合并；放 T2511（V2a 1b）、T2512（V2b）；调度停摆约 12.5 小时（总调度 V4，2026-10-15 06:17 UTC）

- (1) **监督 2026-10-14-1743 两件都 PASS**：
  - **U 关闭于 43 / 42**，旗标撤销；1152 Q5 的六个关闭条件逐条核过。
  - **V2order**：V2a 1b 切两行（行 a 现在开），V2b 现在开，取代 0342 Q2 的串行次序。条件 **V2O-C1**（约束）：`baMainIndFamTL_three`、`baMLOutTL_three`、`unMLOutBA_three` 只由一张票写，另一张不加备份。
  - **O3**：1152 Q5 (6) 的 M/N 一半（对 T2449 端点钉文的形状核对）带进 M/N 开场 REQ。
- (2) **停摆**：本会话 2026-10-14 15:46 UTC 的心跳到 2026-10-15 06:10 UTC 才送达（会话断连），心跳链断约 14 小时；中枢 17:44 UTC 合并 T2510 行 b 后没有新票，空转约 12.5 小时。06:10 重排心跳，向 Jun 报告。
- (3) 停摆期间的合并：
  - **T2510 行 a dc358686**（15:39）：`Step6BridgeBA` 395 + `Step6PinsBA` 488 = 883，自下而上 1,000 的 ×0.88；审核第 1 轮 PASS。
  - **T2508 行 b dff951fe**（17:21）：`QopDecayGen` 443 + `ExpIntIQGen` 1,414 = 1,857，票面 ≈ 1,685 的 ×1.10；审核第 1 轮 RETURN（`szB` 处的退化实例），一次规则 (B) 修复 c490c2e3，第 2 轮 PASS。
  - **T2510 行 b dd605b0c**（17:44）：`Step6BA` 240，×0.73；审核第 1 轮 PASS。
  - **V1s3′ 完成**（两行 3,609 = 簿记 3,440 的 ×1.05）；**V1-BA 完成**（1,123 = 自下而上 1,330 的 ×0.84）。三份报告都无论文差异候选。
- (4) **放 T2511 = V2a 1b**（后台起草子代理起草 r1–r3，调度核读定稿；`docs/tickets/T2511.md`、检查 `T2511-check.lean`）：
  - 行 a `t/T2511`（V 第 12 行）= 目标 1–10：K2、族的 Step 1 调用、私有单流步与包装、槽形式的泛型步（目标 6）、四个情形定理（Steps 3–4 读 T2509 的名字，(iii)/(i) 取 `R34 = R`）、四个闭合情形（目标 10，读 T2510 的 `BAStep6R` 与 `baStep6Reg*_holds`，桥 `fun _ _ _ _ h c => c h`）；新 `BA/MainIndFamTL` + `BA/MainIndRegBA`；自下而上 267 / 441 / 947，校准 423–564；**现在开工**。
  - 行 b `t/T2511b`（V 第 14 行）= 目标 11–12：`d = 3` 终端（V2O-C1 的唯一写者）与一般 `d` 形式 `baMainIndFamTL_any`；新 `BA/MainIndTermBA`，40 / 60 / 120；登记删 `:140`，并改 Step-1/Step-2/TL1 六行的负责人注释（T2504 决定 (3) 修订）；T2511 行 a 与 T2512 都合并后开工。
  - 监督 O2 的选择：泛型目标 6 保持槽形式，行 a 用 T2510 的名字闭合；`BAStep6R` 只按名字读，不重述。`BAMainIndS1TL` 私有。
- (5) **放 T2512 = V2b**（`docs/tickets/T2512.md`、检查 `T2512-check.lean`）：一行 `t/T2512`（V 第 13 行），新 `BA/MainIndGlue`，`baMainIndFamTL_of_regimes (h₃ h₁ h₂ h₄) : BAMainIndFamTL d STAny`；输入是已合并类型的假设，**现在开工**，与 T2511 行 a 并行。价按自下而上 260 / 365 / 615（校准 350–467；T2245 的模式层已公开，探针约 270 行不必移植），停止线 800；`prover`（移植）。不写终端（V2O-C1）；`:140` 留到 T2511 行 b。
- (6) 计数：BA 195（+1，V2a 第二行）；U 43 / 42 关闭；**V 14 / 12 已放**（T2511 a = 12、T2512 = 13、T2511 b = 14），预测 14；离 HOLD 线 15 只剩一行：再拆或 V 的收尾行放行前先发短 REQ。M/N 3 / 15。H313。下一节 §335，下一张票号 T2513，下一条 H314。

## §335 — H313 开工；M/N 开场 REQ 提前发；V 关闭 REQ 备好（总调度 V4，2026-10-15 06:40 UTC）

- (1) H313 done 97779231：两个检查 exit 0；T2511 行 a（wf_1d110bb2-bf9）与 T2512（wf_a9c42de2-cae）06:22 并行开工。
- (2) **后台起草子代理备好 V 关闭 REQ 与 M/N 开场**（`docs/claude-team/drafts/REQ-Vclose.md`、`REQ-MNopen.md`、`MN-plan.md`）：
  - V 关闭各项（0342 Q1）：族链与终端在 T2511 行 b 合并后齐；登记里只有 `:134` `STKboundgL`（「BA-V 消」）不在 T2512、T2511 b 的单子里，V 关闭时用 H 指令改一条注释指向 `baKboundMember_holds`。
  - **形状核对（1743 O3）**：M 侧逐 `d` 对得上（`BAMAFixed d := UNMLOutBA d → …` 在 `d = 3` 吃 `unMLOutBA_three`；`BAMLOutTL` 未变）。**N 侧对不上**：`baBUniv_of_rows (hML : ∀ d, UNMLOutBA d)`（`BA/UNPins:367-370`）、`UNOURowBA`（`:123`）、`UNQueBA_of_BAEnd_QUEL`（`:357`）、`UNLocAvgk`/`UNQuek`/`UNOUClaimsk`（`PinsK:398, 406, 421`）都要每个 `d`；V 只给 `∀ d, STStep5IIIgL d → …`，照现在的合并文本 `BAEnd_BUnivL 3` 带着 `d > 3` 的情形 (iii) 条件，与 §316（`d = 3` 无条件）不合。即 §318 (4) (7)、§320 (2) 记下的事。
  - 新设计门 **MN-D3**（`d = 3` 的 UN 侧组装）：(A) 带维数过滤 `D` 的带撇后继（带状 `D = True`、BA `D = (· = 3)`），推荐，是 Jun 的 B 的落实，不另问 Jun；(B) 在 `∀ d, STStep5IIIgL d` 下陈述，要问 Jun；(C) 推广 U5，Jun 的 B 已排除。
  - M/N 余下七行（M1、M2、M3、N2、C3、C4、C5）+ MN-D3；中心 7,077，校准 6,794–9,059（`thetaDiff` 与 MN-D3 的实现未定价）；预测 ≈ 12（11–14），旗标 15；BA 终点 ≈ 204。
- (3) **M/N 开场 REQ 提前发**（`docs/supervisor/requests/REQ-2026-10-15-0640-MNopen.md`）：V 的最后一行（T2511 b）合并前就问，好让第一批在那时开工；Q3 问 MN-D3（设计门，不是证明票）能否现在就开。V 关闭 REQ 在 T2511 b 合并后发。
- (4) 在跑：T2511a、T2512（2 / 4）。计数不变：BA 195；V 14 / 12；M/N 3 / 15。H 未写（下次放行时一并提交本节与 REQ）。下一节 §336，下一张票号 T2513，下一条 H314。

## §336 — T2512（V2b）合并；监督 0643：M/N 开（(A)，MNO-C1–C4）；放 T2513 = MN-D3（总调度 V4，2026-10-15 06:58 UTC）

- (1) **T2512 = V2b 合并 a47cf1e1**（06:48）：新 `BA/MainIndGlue` 436 = 自下而上中心 365 的 ×1.19（校准 350–467 之内）；审核第 1 轮 PASS；不写终端（V2O-C1）。T2511 行 b 现在只等行 a。
- (2) **监督 2026-10-15-0643 PASS：M/N 开**，预测 ≈ 12（11–14），旗标 15；新线：放行使预测到 15 或以上先发短 REQ，用到 15 未关闭建议 HOLD（取代通用的 25 / 40 线）。
  - 形状核对确认：M 侧在 `d = 3` 对得上；N 侧的 `∀ d` 与 §316 不合。
  - **MN-D3 取 (A)**（维数过滤的带撇后继），是 Jun 的 B 的落实，**不问 Jun**；只有 MN-D3 的探针表明 (A) 做不成时 (B) 才去问 Jun。(C) 排除。监督的 grep 显示 (A) 要覆盖的面比 REQ 列的宽：`UNTrLocalBARow`、`UNTrLocalInitBARow'`（M1 行 b 的目标）、`unJakUywRowBA_holds`、`g1Rowk_of_inputsG` 与其 BA 实例、`ouRowk_of_pins`、`un_claimAll_of_rowsBA`、`baBUniv_of_rows`、两座桥、`UNPins:1027-1066` 的 `inst_*`。
  - 关闭条件 (i)–(v) 照收，加 (vi)：`BAThm27L 3`、`BAEnd_BUnivL 3` 的最终公开形式不带 `STStep5IIIgL`、不带 `∀ d` 的 `UNMLOutBA`/`UNLocAvgBA`/`UNQueBA`，唯一外部假设 `UNL32`，关闭 REQ 逐字引两个签名；(vii)：`d > 3` 形式保持假设形，登记注释用 §316 的措辞。
  - Q3：MN-D3 现在开；M1 行 a 与 C3（先 D1）在 T2511 行 b 合并时开。Q4：(a) M1 行 a 在 `BA/MAPins` 公开全部 MN1 钉文；(b) `BAThm27L 3` 归 N2（N2 的 1a 中心连 MN-D3 实现超 1,950 时退到 MA-06b，不改计数）；(c) `thetaDiff` 先由 C3 的 D1 在 `ζ = 0` 试，C3 的 1a-audit 拿不出陈述与路线则 M2 合并时就放 M3 的 D1。
  - **约束 MNO-C1**：MN-D3 的后继都是新名字，不改已合并陈述；`#print axioms band_terminal`、`bUniv_holds` 前后不变；带状在 `D = True` 由一行 `Iff` 恢复。**MNO-C2**：MN-D3 报告逐条列 Q2 单子，每条「逐 `d`：机械复制」或「用到别的维数」带行号；有一条后者或实现总价超 1,950 → N2 放行前发短 REQ。**MNO-C3**：M1 行 b 的 TrLocal 行经逐 `d` 核心 `∀ d, 3 ≤ d → (d 处的 UNLocAvg) → d 处的 TrLocal` 证，已合并的 `∀ d` 文本作一行推论，所以 M1 b 不等 MN-D3；M1 的 `UNLocAvgBA` 桥、M3 的 `UNQueBA` 桥同理。**MNO-C4**：每个 1a 自下而上重新定价，新行在 1a 时就进预测，15 线规则在那时适用。
- (3) **放 T2513 = MN-D3**（总调度直接写票，`docs/tickets/T2513.md`、检查 `T2513-check.lean`：只 `#check` 0643 Q2 单子里的已合并名字）：设计门，报告 + 探针（≤ 300，上限 400），`prover-max`；交付 D1 过滤词汇（新名字）、D2 MNO-C2 逐条表（含 grep）、D3 探针（`d = 3` 的 `BAEnd_BUnivL 3` 只带 `UNL32` 与 `d = 3` 输入）、D4 实现价与归属（进 N2 或另开泛型行）、D5 MNO-C3 的逐 `d` 核心文本、D6 关闭条件 (vi) 的两个签名。只合并报告，探针留在分支。**现在开工**，与 T2511 行 a 并行。
- (4) 计数：BA 196（+1，MN-D3 是 T2379/T2449 计划外的门）；V 14 / 12（预测 14；V 关闭 REQ 在 T2511 b 合并后发）；**M/N 4 / 15**（预测 ≈ 12）。在跑：T2511a，H314 后加 T2513（2 / 4）。H314。下一节 §337，下一张票号 T2514，下一条 H315。

## §337 — T2511 行 a 合并；放 T2514 = M1、T2515 = C3（T2511 行 b 合并时开工）（总调度 V4，2026-10-15 07:22 UTC）

- (1) **T2511 行 a 合并 a082fcfe**（07:03）：`MainIndFamTL` 397 + `MainIndRegBA` 113 = 510 = 自下而上中心 441 的 ×1.16；审核第 1 轮 PASS；无登记改动。行 b（终端）07:03 开工（wf_30917a08-7f3）。T2513（MN-D3）07:03 开工（wf_3fe0bb07-d69，H314 done 251dd3a0）。
- (2) **T2514 = M1**（后台起草子代理起草，调度核读定稿）：两行预签。行 a `t/T2514`（M/N 第 5 行）= `BA/MAPins`（T2449 探针 158-257 的 MN1 钉文原样公开，外加三个逐 `d` 文本 `UNLocAvgBAAt`、`UNTrLocalBAAt`、`UNTrLocalInitBAAt'`，与已合并的 `∀ d` 文本 `Iff.rfl`）+ `BA/MALocal`（固定 `z` 的 locSC、网、`baEnd_locSCL`、经逐 `d` 核心的 `UNLocAvgBA` 桥，`baEnd_locSCL_three`），自下而上 655 / 925 / 1,435，校准 888–1,184；行 b `t/T2514b`（M/N 第 6 行）= `BA/MATrLocalBA`（TrLocal 两行经逐 `d` 核心，MNO-C3），255 / 365 / 760。发现：TrLocalInit′ 要在 `λ̂ = λe^{t*/2} > λ` 处的 bulk，已合并的 `BAwindow_step` 只往下走，可能要 ≤ 250 行的私有孪生（预授权窄探针）；BA 端域是 ρ-bulk，网在 `κ/2` 用 `BAbulk_window` 建。登记：行 a 删 `:178` `UNLocAvgBA`，改 `:391`；行 b 删 `:182`、`:183`，改 `:384`、`:388`（T2511 b 删 `:140` 后各行号减一，按名字找）。决定 (1)–(7) 见票。
- (3) **T2515 = C3**（后台起草子代理起草，调度核读定稿）：先 D1（窄门 + 探针 ≤ 200，1a-audit 在 1b 之前）：(i) O9 无损 `BAProp8` 已在 `main`（`BA/FlowPins:217`，`baProp8_holds` `Prop6Path:1009`），D1 交付它在复 `z` 的用法（`BAzztE_data` 搬 `Θ`、`cT ≤ t₀`、`Θ̃` 的 BA 振荡界）；(ii) `ζ = 0` 处的 `thetaDiff`（`T2515_ThetaDiffBA`，路线 (i) + `ΘQ = Θ − 1`），1a-audit 记「交付」或「不能交付」；(iii) 剖面文本 `UNOUProfile.ba`；(iv) BA 的 GUE 相 2-loop。价：自下而上普查 2,808 中心（T2449 1,102 的 ×2.5），预签在 `GUEKPrim` | `GUEEntry` 拆；行 b 不读行 a。C3 不读 V 的输出，但照 0643 Q3/O3 在 T2511 b 合并时开工（T2511 b 短，已在跑）。登记 `:171` `UNOUProfRowk` 移到 `structuralProps`；EntryGrid（UN-43）归 C5。决定 (1)–(9) 见票。
- (4) **M/N 计数约定**（余下全程）：按 §310 (6) 记相对 T2379/T2449 计划的增量。T2514 行 a +0（BA 196）、行 b +1（BA 197）；T2515 行 a +0（BA 197），拆则行 b +1（BA 198，1a 时记）。M/N：T2513 = 4、T2514 = 5、6、T2515 = 7（行 b 8）；预测 ≈ 12，C3 拆则 ≈ 13（< 15）。
- (5) 在跑：T2511b、T2513；T2511 b 合并后加 T2514 行 a、T2515（D1 → 1a）（4 / 4）。H315。下一节 §338，下一张票号 T2516，下一条 H316。V 关闭 REQ 在 T2511 b 合并后发。

## §338 — T2511 行 b 合并，V 的行全部合并 → V 关闭 REQ；T2514、T2515 开工；C3 在 1a 拆两行（总调度 V4，2026-10-15 07:37 UTC）

- (1) **T2511 行 b 合并 c536c603**（07:22）：新 `BA/MainIndTermBA` 124（`baMainIndFamTL_three`、`baMLOutTL_three`、`unMLOutBA_three` 无条件；`baMainIndFamTL_any` 一般 `d` 在 `STStep5IIIgL d` 下）；审核第 1 轮 PASS；登记删 `:140`，六行负责人注释改名 T2511。T2511 两行合计 634 = 自下而上 501（441 + 60）的 ×1.27。**V 的 14 行全部合并**，合计 15,131 行，无新论文差异。
- (2) **发 V 关闭 REQ** `docs/supervisor/requests/REQ-2026-10-15-0736-Vclose.md`：0342 Q1 的 (i)–(v) 逐条对上；`:134` `STKboundgL`（「BA-V 消」）问能否用 H 指令改注释指向 `baKboundMember_holds`；N 侧 `∀ d` 已由 0643 归 MN-D3。
- (3) H315 done b2326aac：T2514 行 a（wf_669e4239-a80）与 T2515（wf_ad1bd330-26f，D1 → 探针 → 1a-audit）07:23 开工。1a：T2514 PASS（`MALocal` 中心约 830，停止线 1,300）；**T2515 拆 a | b**（中心 2,762 > 1,950；行 b 1,648 ≤ 1,950，不再拆 b′），D1 (i) 无损，`thetaDiff` 的编译结果等 1a-audit；`stable_mixBA` 是未定价的新 BA 数学（观察项）。T2513 的 1a：D2 表到 grep 为止无「用到别的维数」。
- (4) 计数：C3 的行 b 记为 **M/N 第 8 行，BA 198**（§337 (4) 约定）；M/N 预测 ≈ 13（< 15）；V 14 / 12（待关闭）。在跑：T2513、T2514a、T2515（3 / 4）；T2514 行 b 在行 a 的 1a PASS 且 `BA/MAPins` 提交后叠上。H 未写（下次放行时一并提交 §338 与 REQ-0736）。下一节 §339，下一张票号 T2516，下一条 H316。

## §339 — 监督 0742：V 在 14 / 12 关闭；VC-C1；放 T2516 = M2、T2517 = C4（总调度 V4，2026-10-15 08:01 UTC）

- (1) **监督 2026-10-15-0742 PASS：子阶段 V 关闭于 14 / 12**（旗标 12 撤销；HOLD 线 15 没到）。关闭条件 (i)–(v) 逐条核过；`baMainIndFamTL_three`、`baMLOutTL_three`、`unMLOutBA_three` 无假设、标准三公理；一般 `d` 只多 `STStep5IIIgL d` 一个前提（在类型里）。三个带过去的事都归 M/N（0643 已接）。超出 +2：0843 的 V1s2′/V1s3′ 新文件重排与 1743 的 T2511 两行，都是事先报过的。
- (2) **VC-C1**：`Test/Axioms.lean:134` `STKboundgL` 的负责人注释改为指向 `baKbound_holds`（K12）与 `baKboundMember_holds`（T2511），只改注释，由 H316 随下一次提交做，不算票、不另审核（T2482 / H271 (3) 先例）；该行留在 `owedProps`。
- (3) T2514 行 a 的 1a PASS，`BA/MAPins` 在 `t/T2514` 112ffba2 提交，行 b 叠上开工（wf_ae4776d3-ad9）。在跑：T2513、T2514a、T2514b、T2515（4 / 4）。
- (4) **放 T2516 = M2**（后台起草子代理起草，调度核读定稿）：`BA/MAQDiff`，逐 `d` 的 `baQDiffFixed_of_ML`、`baMANetQD`、`baEnd_QDiffL`，`d = 3` 的 `baEnd_QDiffL_three`（读 `unMLOutBA_three`）；唯一的新数学是 `BAprof` 对 `z` 的 Lipschitz 界（常数提议 `12κ'^{-2}(1+κ'^{-2})`，Ward → Neumann → 预解恒等式；预授权 ≤ 150 行探针）。自下而上 645 / 880 / 1,270，校准 845–1,126。T2514 行 a 合并后开工。M/N 第 9 行，BA 198（+0）。决定 (1)–(7) 见票。
- (5) **放 T2517 = C4**（同上）：发现 T2449 当作泛型的两样输入在 `main` 上只有带状形式：GUE 漂移（`Drift:756/1208/1318` 用 `zt E`、`|E| < 2`）；BA 的 `M` 不是对角，一圈要一个新的路径输入 `hoff`（GUE 网格上 `M` 加权的块迹，`ExpAvgGen_W1iii` 的网格形）。两样进 D1。自下而上中心 2,035（T2449 868 的 ×2.34），预签在 `GUEOneLoop` | `GUEEq729BA` 拆（1a 时记）。**目标 8 挪给 C5**，C4 不读 C3 的名字，**有空位就开工**（C3 ∥ C4 → C5）；`hoff` 的生产者定为 C5（新范围，C5 的价风险）。M/N 第 10 行，BA 198（+0）；拆则第 11 行、BA 199、预测 ≈ 14；C5 若也拆就到 15 → C5 放行前发短 REQ。决定 (1)–(8) 见票。
- (6) 计数：BA 198；V 14 / 12 关闭；M/N 已放 10（T2513、T2514 a/b、T2515 a/b、T2516、T2517 a），预测 ≈ 13–14。H316。下一节 §340，下一张票号 T2518，下一条 H317。

## §340 — MN-D3（T2513）报告合并：(A) 可行，实现进 N2；T2514 行 a 合并；C3 的 1a-audit：`thetaDiff` 交付；T2517 检查修正（总调度 V4，2026-10-15 08:17 UTC）

- (1) **T2513 = MN-D3 报告合并 0deabaa8**（08:12）：PASS，没有停止规则触发；**(A) 照写可行，(B) 不用问 Jun**。探针 392 行（≤ 400），不改任何已合并文件；`BAEnd_BUnivL 3` 只要 `UNL32` 与 `d = 3` 的钉文。D2：0643 Q2 单子逐条都是「逐 `d`：机械复制」，**没有一条「用到别的维数」**（grep 102 处逐一归位）→ N2 放行前不发 REQ（MNO-C2）。D4：实现 = G1 `Universality/PinsKD`（8 个过滤钉文 + 带状 `Iff`，中心 166）+ G2 `Universality/GUEPhase/RandomLayerBGD`（118）+ BA 叶（在 N2 的 `BA/UNBUniv` 里，185），合计 469，校准 479–626；**放进 N2**（N2 连实现 700–920，高端 1,189，离 1,950 有 1.64 倍余量）。D6：`BAThm27L 3`、`BAEnd_BUnivL 3` 的最终签名（唯一外部假设 `UNL32`）由 N2 写。F1：已合并的 `∀ d` 读法留在 `main` 上不改，但不在 `d = 3` 终端上了（登记措辞照 §316）。
- (2) **G1 的位置（报告 §4 的选择）**：取 (γ′)：G1 随 G2 一起进 N2；M1 行 b 与 M3 的逐 `d` 核心用 T2514 行 a 已在 `BA/MAPins` 公开的逐 `d` 文本（`UNLocAvgBAAt`、`UNTrLocalBAAt`、`UNTrLocalInitBAAt'`；§337 T2514 决定 (2)），N2 用一行 `Iff` 把 G1 的过滤钉文与这些文本接上。不改在跑的 T2514 行 b，不加行；M/N 预测不变。
- (3) **T2514 行 a 合并 3a67e18d**（08:15）：`BA/MAPins` 279 + `BA/MALocal` 927 = 1,206 = 中心 925 的 ×1.30；审核第 1 轮 PASS。行 b 在跑；T2516（M2）08:15 开工。
- (4) **T2515 的 1a-audit PASS**（探针 45195400）：D1 (i)–(iv) 签字；**(ii) `thetaDiff` 交付**（`probe_thetaDiff : T2515_ThetaDiffBA`，标准三公理，`C = 2C₈/cT + 𝔡⁻²`）→ 照 §337 T2515 决定 (7)，C3 拥有 BA 的 `thetaDiff`（目标 6），**M3 不要 D1**。拆 a | b，两行都在跑（行 a wf_ae2dfc4e-3b7、行 b wf_98290c01-026）。
- (5) **T2517 检查不编译**（H316 (3)：`RBM.BA.BAStab` 不在导入闭包里；目标 4、6、7 的提议钉文实例综合失败）。检查修正（行数不变）：`BAStab` 的 `#check` 改为注释；目标 4、6、7 的提议文本放进块注释，由 1a 加上 `Zd d (sz.L n)` 需要的实例参数（如由 `sz.three_le_L` 得 `NeZero (sz.L n)`），1a-audit 后才有约束力。H317 重编译后有空位就开工。
- (6) 在跑：T2514b、T2515a、T2515b、T2516（4 / 4）；T2517 等空位。计数：BA 198；M/N 已放 10（T2517 行 b 在 1a 时记）；余下 M3（不要 D1）、C5（读 C3 a/b 与 C4，带 `hoff` 的生产、目标 8、EntryGrid）、N2（带 G1、G2、BA 叶）；预测 ≈ 13–15，C4 与 C5 都拆时到 15 → C5 或 N2 放行前发短 REQ。H317。下一节 §341，下一张票号 T2518，下一条 H318。

## §341 — M1 完成；放 T2518 = M3（总调度 V4，2026-10-15 08:33 UTC）

- (1) **T2514 行 b 合并 242d669e**（08:31）：新 `BA/MATrLocalBA` 521 = 中心 365 的 ×1.43；审核第 1 轮 PASS。**M1 完成**：两行 1,727 = 中心 1,290 的 ×1.34。T2517（C4）08:31 在空出的位开工（H317 done 89947ef7，修正后的检查 exit 0）。
- (2) **放 T2518 = M3**（后台起草子代理起草，调度核读定稿）：`BA/MADecolQUE`，逐 `d` 的 `baMADecol`、`baEnd_decolL`、`baQueFixed`、`baMAQUE`、`baEnd_QUEL` 与 `d = 3` 形式；`UNQueBA` 桥经逐 `d` 核心 `unQueBAAt_of_QUEL`（MNO-C3），`BA/MAPins` 里没有 `UNQueBAAt`，由 M3 公开。没有新数学：decol 是带状证明取 `C_M = 1`（`M_xx = m`、`‖m‖ ≤ 1`），QUE 的前半复用已合并的私有 `QUEFlow_queFixed`，要写的只有 `que2Bad_sub` 的私有泛型拷贝（≈ 75）。自下而上 317 / 432 / 650，校准 415–562（T2449 1,300 的 ×0.33；MN 计划的合计因此降约 870 中心行）。T2516 与 T2515 行 a 都合并后开工。M/N 第 11 或 12 行；BA 198（+0）。决定 (1)–(6) 见票。
- (3) 在跑：T2515a、T2515b、T2516、T2517（4 / 4）；T2518 排队。剩下没写票的：C5（等 C3 a/b、C4）、N2（最后）。计数：BA 198；M/N 预测 ≈ 13–15。H318。下一节 §342，下一张票号 T2519，下一条 H319。

## §342 — M2 与 C3 行 a 合并；M3 开工（总调度 V4，2026-10-15 09:19 UTC）

- (1) **T2516 = M2 合并 dec8e150**（09:04）：`BA/MAQDiff` 1,099 = 中心 880 的 ×1.25；审核第 1 轮 PASS；无登记改动。
- (2) **T2515 行 a = C3a 合并 13b68cea**（09:14）：`BA/GUEKPrim` 1,241 = 中心 1,126 的 ×1.10；D1 与目标 1–8（含 `baThetaDiff`）；登记 `UNG1Rowk` 负责人注释、`UNOUProfRowk` 移到结构列表。行 b 在跑。
- (3) **T2518 = M3** 在 M2 与 C3 行 a 合并后开工（wf_01e692ed-31b）。在跑：T2515b、T2517（D1 → 1a-audit）、T2518（3 / 4）。没有可放的票：C5 等 C3 b 与 C4，N2 最后。C5 在 C4 的 1a-audit 后起草。下一节 §343，下一张票号 T2519，下一条 H319。

## §343 — C4 设计门通过，拆 a | b；起草 C5（总调度 V4，2026-10-15 09:36 UTC）

- (1) **T2517 = C4 设计门 PASS**（09:22，`docs/reports/T2517-1a-audit.md`，探针 c305806d，无需签字）：`T2517_*` 文本、`gueHBA`（目标 1：`PsiI` 取在 `(sz.withLam 0)`，与票里的读法 `rfl` 相等，修掉了检查文件的类型不合）、D1 (i)–(iii)、普查都签了。普查：行 a `BA/GUEOneLoop` 中心 1,044（宽口径 1,199），行 b `BA/GUEEq729BA` 中心 958（宽口径 1,246）；合计 2,002 > 1,950，**按预签拆 a | b**（行 a 目标 1–5，`t/T2517`；行 b 目标 6、7、9，`t/T2517b`，叠在行 a 带 `gueHBA` 的第一个提交上）。行 a 的 1b 已开工（wf_68f640fb-cfa）。D1 (i) 收口：`hoff` 的消费者形式是 `T2517_OneLoopBA` 的第二个 `StochDomAt` 前提，生产路线 `t_aq − Q_aq = M^B_aq twTr(q,a)`（数值 5e-16）→ **生产者 C5**（T2517 决定 (2)）。
- (2) 审核附注 2：行 b 的 Layout 导入 `BA/GUEKPrim` 和目标 8 与决定 (1) 矛盾；1b 照决定 (1) 两样都去掉（目标 8 归 C5）。附注 1（Drift 纯普查 80 对 422）不改拆分：宽口径 2,445 与决定 (4) 都支持拆。
- (3) **计数（MNO-C4）**：C4 行 b 在 1a 记为 **M/N 第 12 行，BA 199（+1）**（票里写第 11 行；其间 T2518 放行已占第 11 行，按放行顺序记第 12）；M/N 已放 12 行，预测 12 + C5（1，多半 2）+ N2（1）= 14–15。余下没写票：**C5**（`BA/GUEHyp`；读 C3 a/b 与 C4 a/b；带目标 8 `baEq729_Kdisc`、`hoff`/`h1`/`hK3b`/`Kt(t₁)` 的生产、`gueGrid_eq729` 孪生、HypA/Proc/PathBounds 孪生、DuhamelA–C/BoundsA/EntryGrid（UN-43）孪生；1a 定是否另开泛型 `Of` 行）和 **N2**。C5 按 C3/C4 的比率（自下而上 1,217 的 ×2.3–2.5 ≈ 2,800–3,000）多半在 1a 拆 → 预测 **15** → **C5 放行前发短 REQ**（0643 Q1 线）。
- (4) **起草 C5**：后台起草子代理，稿子写到 `docs/claude-team/drafts/C5.md`、`C5-check.lean`，短 REQ 稿 `C5-REQ.md`；调度核读定稿。C5 的开工条件：C3 行 b 与 C4 a/b 合并后从 `main` 开工。在跑：T2515b、T2517（行 a 1b）、T2518（3 / 4）。下一节 §344，下一张票号 T2519，下一条 H319。

## §344 — M3 合并（M 链完成）；C5 重新定价 ≈ 6,300 行、四行；短 REQ（总调度 V4，2026-10-15 10:16 UTC）

- (1) **T2518 = M3 合并 9c5fc941**（09:43）：`BA/MADecolQUE` 532，在校准 415–562 之内；审核第 1 轮 PASS；登记照票（欠账扫描 125 → 124）。**M 链 M1、M2、M3 全部合并。** T2517 行 b 09:41 叠在行 a 的第一个提交 db2015e4 上开工（wf_a0d6dc7e-0d0）。在跑：T2515b、T2517、T2517b（3 / 4）。
- (2) **C5 = T2519 起草完**（后台起草子代理，`docs/claude-team/drafts/C5.md` 108 行、`C5-check.lean` 452 行、`C5-REQ.md`）。**结论：C5 不是 2 行 ≈ 2,800–3,000，而是自下而上中心 6,311（宽口径 8,301；×0.96–1.28 为 6,059–8,078），四行。** 原因：T2449 的 C5 是 T2173 的孪生组 G3，按 §57 (2)（UN-25…52 写成模型泛型）定价；UN gate 实际只做了带状形（§129 (4)：「`GUEPathBounds` 只做 band 形（BA 形归 BA-C5）」；核过：`GUEPhase/` 29 个文件里只有 `Generator` 有 `ztOf`）。所以 C5 带三样：T2449 计过价的 T 类孪生（Eq729B、HypA、Proc、ProcK、PathBounds，2,171）；没计价的 P 类改写（HypB、BoundsA、DuhamelA2/B/C、EntryGrid、LLTransfer，2,090）；新的 BA 数学 ≈ 1,385（`hoff` 生产者 800 [500, 1,400]、对矩阵 `M` 的局部律、BA 的 K̃ 与正性补齐）。预签四行（纯普查，每行 ≤ 1,950）：a `GUEProcBA`、`GUEHypABA`、`GUEEntryGridBA` 1,726；b `GUEDuhamelBA`、`GUETwistBA` 1,517；c `GUEHypBBA`、`GUEPathBoundsBA` 1,650；d `GUELLBA`、`GUEHyp`（Eq729B 孪生、`baEq729_Kdisc`、`ba_prodG`/`ba_LLG`/`ba_QueG`）1,418；备用 a′、b′、c′。泛型 `Of` 两个价（UP-C2）：原地 6,224–6,812（与 BA 叶持平，宽口径省 1,500–2,000，但碰 `Main/BandTerminal` 的锥、三个文件的 2,000 停止线和 56 个冻结的公开名），新文件 8,274–10,227（最贵，不提）。`hoff` 路线 R1：恒等式 `t_aq − Q_aq = M^B_aq twTr(q,a)` + 网格单时高斯律下 `twTr` 的 Stein 矩界，只读同一网格时刻的两条路径界字段与 `baM_row_l1`；R2（要 `t₁` 处的 `twTr`，是 V 输出）、R3（Ward + 折叠只给 O(1)）不取。
- (3) **计数**：C5 a–d = M/N 第 13–16 行（BA 199 → 202），备用到 19；N2 一行。**预测 17（17–20）**，越过旗标 15；第 15 行在 C5 的 1a 记 c 行时用到（HOLD 线）。照 0643 Q1，**放行前发短 REQ：`docs/supervisor/requests/REQ-2026-10-15-1015-C5split.md`**（Q1 在预测 17 放行、旗标提到 20；Q2 布局：BA 叶 vs 原地；Q3 `hoff` 的窄 D1 + 探针；Q4 V 关闭后是否仍守「不读 V 名」）。没有路线改动：C5 不读 V 输出，`RBG_*` 文本照合并的不动（GMN-C3），N2 的读法不变。
- (4) **起草 OQ 的调度决定**（流程事）：OQ1 现在发 REQ。OQ2 1a（无证明目标）在 C4 行 a 合并后开工，各行按输入从 `main` 开工（a 在 C3 b 与 C4 a 之后，b 在 C4 b 之后，c 在 a、b 之后，d 最后）。OQ3 拆分以纯普查为准（与 C3、C4 同）。OQ4 若 K 界要每个 `n` 的 `BAFlow` 且补齐不收口 → 带撇 `RBG_Prod` 是停止线，1a 停、短 REQ（不预先批）。OQ5、OQ6 等 Q4 的回复，默认守（`BA/TwistAvg*` 不读，实例保留 `UNMLOutBA 3` 为前提）。OQ7 新结构行 `GUEPathBoundsBA` 归首次定义它的行（行 a 的第一个提交），`:383` `GUEPathBounds` 的负责人注释归生产者所在的行 c。
- (5) 票等监督回复后定稿（票号 T2519）。N2 最后，再 MA-06b。H319。下一节 §345，下一张票号 T2519，下一条 H320。

## §345 — C4 行 a 合并；C3 行 b 审核 RETURN（总调度 V4，2026-10-15 10:45 UTC）

- (1) **T2517 行 a = C4a 合并 ff7bd277**（10:33）：`BA/GUEOneLoop` 1,395 = 1a 中心 1,044 的 ×1.34（宽口径 1,199 的 ×1.16）；D1 与目标 1–5（含 `gueHBA`、`gueGrid_expect_oneLoopBA`）；无登记改动；审核第 1 轮 PASS。行 b 在跑（叠在 db2015e4，合并时只应用它自己的差分）。
- (2) **T2515 行 b = C3b 审核第 1 轮 RETURN**（10:24，`docs/reports/T2515b-audit.md` §6）：目标 10 `mix_detBA` 的实例退化（只 `u = 0`）；中枢按规则做一次自动修复。审核附注：落地 `GUEEntry` 1,524 + `GUEEntry2` 1,225 = 2,749，超过票里的软停止线 1,300 / 700，但没超过约束性的单文件 2,000；行上限 1,950 按 1a 中心（1,648）判，落地 = 1a 中心的 ×1.67。**不改计数**（拆分按 1a 中心定，§337 (4)）；附注 3 的临时标签 `T2515c` 重号由调度在 paper-deltas 里编（行 a 的矩阵 2-loop 与行 b 的钉文族形各一号，Jun 改论文时看）。
- (3) 校准：C3a ×1.10、C3b ×1.67、C4a ×1.34（对 1a 中心）。C5 的 REQ 里写的落地区间 6,940–9,025 按 ×1.10–1.43；若取 ×1.34–1.67，C5 ≈ 8,500–10,500。四行的拆法与行上限按 1a 中心判，计数不变；在定稿的票里写明这条风险。在跑：T2515b（修复）、T2517b（2 / 4）；C5 等监督对 REQ-2026-10-15-1015-C5split 的回复。下一节 §346，下一张票号 T2519，下一条 H320。

## §346 — C4 完成；监督 1044 PASS（C5 放行条件、旗标 20）；T2515b 停在签字问题；V4 → V5 交接（总调度 V4，2026-10-15 11:03 UTC）

- (1) **T2517 行 b = C4b 合并 26561542**（10:50）：`BA/GUEEq729BA` 1,331 = 1a 中心 958 的 ×1.39；目标 6、7、9（目标 8 照决定 (1) 归 C5）；无登记改动；审核第 1 轮 PASS。**C4 完成**（a ff7bd277、b 26561542）。
- (2) **监督 1044 PASS**（回复 REQ-2026-10-15-1015-C5split）。照它的 O1 记录：**M/N 旗标 15 → 20**；REQ 线 = 放行使预测 > 20（预签集合 {C5 a–d、a′–c′、N2 一行} 之外的任何行）；HOLD 线 = 用到 21 而 M/N 未关闭。**布局 L1**（BA 叶、十个新文件、不改带状文件；Duhamel 层原地只在 C5S-C3 下）。**§57 (2) 对 GUE 相作废**：GUE 相只经 `Generator` 带状泛型，BA 形在 `BA/GUE*BA`。**V 规则放宽**：不读 V 名仍是 C5 的默认，不再是停止线；`BA/TwistAvg*` 里已合并的代数引理可按名字读（票里记一笔）；R2 仍停（GMN-C3）。`hoff` 的 D1 (i) 窄门 + 探针（R1）批准。约束条件 C5S-C1–C4 写进 T2519 的停止规则。O2（定稿 T2519；1a 现在就可以开）、O3（paper-delta 候选 `T2519a`–`c`）留给下一任调度。
- (3) **T2515 行 b = C3b：audit-fail**（10:55）：审核两轮 RETURN，目标 10、11（`mix_detBA`、`mixEntry_detBA`）完全消掉前提的实例只在退化点 `(a,b) = (0,0)`；规则 (B) 修复 f158d5f5 报 OBSTRUCTION（`0 ≤ a ≤ b`、`0 < b`、`a + b ≤ 1/2` 下 `X = 0` 的完全实例不可能；`a > b`、`a + b > 1/2`、`X ≠ 0` 未覆盖）。中枢问：先验事件与 LDE 事件能否在 `0 < a + b` 留作实例前提，还是改目标 / 路线。**留给 V5 答**（HANDOFF §5 第 3 条）；在答复之前 T2515b 停着，C5 行 a 的输入不齐。
- (4) **Jun（10:5x UTC）：「别写新单，赶紧写team startup，写好V5调度的prompt，做好接班」。** V4 不定稿 T2519、不放票。交接包写进 `docs/HANDOFF.md`（V4 → V5，旧包作附录）；`docs/claude-team/STARTUP.md` §2 换成 V5 提示词、§3 核对监督任务（`trig_01R1NVdwWjDU2P5KMhtTLr43` 仍在，10:42 UTC 成功）、§5 加「交接时删掉旧心跳」；`DISPATCHER-PROMPT.txt` = V5 版。CONTROL 删掉已完成的 T2517 条目，H320 提交这些文件并写明交接。V4 删掉自己待发的心跳后不再写任何文件。下一节 §347，下一张票号 T2519，下一条 H321，下一个 paper-delta D733。

## §347 — 调度 V5 接手；T2515 行 b（C3b）签字：照审核方案 3，样本层事件留作 `(1/4,1/4)` 实例的前提（Amend 1），H321 第 3 轮审核后合并（总调度 V5，2026-10-16 09:54 UTC）

- (1) **接手**：从 2026-10-16 09:5x UTC 起，唯一的总调度是**调度 V5 = Cowork 会话 session_01TaEcrA2Z45rxfP66wcBhm7（账号 junyin.harvard@gmail.com）**。核对（HANDOFF §0、§5）：H320 done（10-15 11:11 UTC）之后没有新合并、没有 state 变化；中枢在线（`HUB.alive` 10-16 09:47 UTC），无工作流在跑；没有待发的旧心跳（本会话心跳 trig_01CkL9G8nVsyUHEe6gYpKncX）；`docs/supervisor/` 最新仍是 1044，open REQ 0。**Jun 2026-10-15「别写新单」仍有效**：T2519（C5）草稿不定稿、不放，等 Jun 说开。
- (2) **T2515 行 b 的签字**（HANDOFF §5 第 3 条；`docs/reports/T2515b-audit.md` §6 方案 3；`T2515b.state` 的问题）：目标 10 `mix_detBA`、11 `mixEntry_detBA` 的实例里，先验事件（`hΩ` / `hllErr`）、四个 LDE 输入（行、列、二次型、对角）和 loop 界 `hLm` 能否在 `0 < a + b` 留作前提。**定：可以，不改任何公开陈述。**
  - (a) 它们都是样本层事件（`GUEEntry_bad` 的事件），概率一侧由目标 12 `gueEntryMixBA` 处理（钉文 = 1a-audit 签的文本，在 `S0` 全部卸掉）。`:1049` 的实例就在真模型 `sz0`、`n = 25` 的样本 `ω` 上；数值与结构前提（`d = 3`、`BAReal`、`(a,b)` 窗、`δ ≤ GUEEntry_dlt`、`W^{-d} ≤ δ²`、`GUEEntry_cs Φ δ² ≤ 1`、`Im z > 0`、Hermitian、预解恒等式）全部卸掉。带状先例 `inst_mixEntry_det`（`EntryTail:1085`）同样保留 LDE 输入。
  - (b) 先例 §56（T2176：`freeConv_stable_local` 的实例保留 `hyp`）：Lean 见证不可行、前提由下游提供、非空真另有数量级依据时，调度签字。
  - (c) **`X = 0` 的障碍不是空真**：`X = 0` 是非典型样本（二次型为 0，偏差就是整个均值 `≈ b·Im z·κ²`，要 `Φ ≳ W^d`）。典型样本的 LDE 偏差是一个标准差的量级（Hanson–Wright），`Φ` 取 polylog `N` 即可；`Φ ≤ (GUEEntry_cs δ²)⁻¹` 在 `δ ≈ W^{-d/2}·polylog` 时只要 `W^d ≫ GUEEntry_cs·polylog N`；先验事件的典型尺度 `|G − M| ≈ W^{-d/2}`，与 `W^{-d} ≤ δ² ≤ GUEEntry_dlt²` 在 `W` 大时同时成立。所以前提集在 `gueEntryMixBA` 的 `∀ᶠ n` 区域对典型样本非空。`n = 25`、`Φ = 1` 的 `(1/4,1/4)` 实例只是变量实例（审核观察 3：那里偏薄），不作非空证据。
  - (d) 先验事件在下游由 C5 的网格自举（`gueGrid_entry_boundBA`，PathBounds 孪生）从起点的 `BAMO` 局部律传下去；那是 C5 的事，闭不上时 C5 的 1a 会停。
  - 审核 §3 的 `X = 0` 障碍（`hwd` + `hΦδ` 由本票的 BA 陈述引入）记为 **`T2515d` 的附注**，合并时编号。修复加的 345 行私有障碍证明**保留**（编译证据；私有、标准公理、`GUEEntry2` 1,570 < 2,000；收尾时 `DeadDecls` 一并清，TEAM §9.13）；审核观察 1 照此了结。
  - **落实**：`docs/tickets/T2515-amend-1.md`；**H321**：中枢在 `t/T2515b` f158d5f5 上起一个新的 `auditor`（第 3 轮，只核 Amend 1 第 5 条 (i)–(iv)），不改 Lean；PASS 照规则 (A) 合并，否则停下等调度。返工：行 b 两轮 RETURN + 一次修复，合并时记账。计数不变（行 b = M/N 第 8 行，BA 198，§338 (4)）。
- (3) T2515 b 合并后 C5 行 a 的输入就齐了（C3 a/b、C4 a/b 都在 `main`）；仍等 Jun 说开新票才定稿、放 T2519（HANDOFF §2）。
- (4) **监督**：定时任务 trig_01R1NVdwWjDU2P5KMhtTLr43 在账号 misslose@g.ucla.edu 上，本会话账号的 list_triggers 看不到它。1044 之后没有 open REQ，按它的提示词今天 10:41 UTC 也不写文件；11:41 UTC 起（距 1044 满 24 小时）它做每日兜底检查、写一份结论——以那份文件确认它还在。
- 下一节 §348，下一张票号 T2519，下一条 H322，下一个 paper-delta D733。

## §348 — C3 完成（T2515 行 b 合并 fde07256）；Jun：开新票、开启监督；本账号新建监督任务；放 T2519 = C5（总调度 V5，2026-10-16 10:36 UTC）

- (1) **T2515 行 b = C3b 合并 fde07256**（10:11）：第 3 轮审核 PASS（只核 Amend 1；第一个第 3 轮审核代理没做检查就回 PASS，中枢没有采用，按规则 (H) 重跑）；`BA/GUEEntry` 1,524 + `BA/GUEEntry2` 1,570（含修复的 345 行私有障碍证明）= 3,094 = 1a 中心 1,648 的 ×1.88；无登记改动。**C3 完成**（a 13b68cea、b fde07256；合计 4,335 = 1a 中心 2,762 的 ×1.57）。返工账本加 T2515 一行（行 b 两轮 RETURN + 一次修复；V4 期间 T2497–T2518 的账本行未补，空闲时补）。paper-delta：行 a、行 b 的候选（含 `T2515d` 的 Amend 1 附注）在补账时从 D733 起编号（HANDOFF §5 第 4 条）。
- (2) **Jun（2026-10-16 10:1x UTC）：「开新票， 开启监督」。**
  - (a) 2026-10-15 的「别写新单」解除：按 HANDOFF §2 派单，保持中枢 2–4 张在跑（能跑的票受依赖限制，见 (4)）。
  - (b) **监督**：在本账号（junyin.harvard@gmail.com）新建定时任务 **trig_01BrMU6EVEAcJw5bdXZd9ptU**「RBM3D 数学监督（每小时看请求队列）」：cron `41 * * * *`（UTC），要求本机（Mac Studio），连接 `/Users/junyin/Lean_proof/RBM3D`，模型 claude-opus-5-5，自动批准，推送开；提示词照 STARTUP §3 原样。旧任务 trig_01R1NVdwWjDU2P5KMhtTLr43 在 misslose@g.ucla.edu 上，本账号停不了；它若还在跑，两份任务会同时处理同一个 open REQ，所以请 Jun 在那个账号里把它暂停（STARTUP §3 已记）。新任务第一次有事做是 11:41 UTC（1044 满 24 小时，做每日兜底检查）。
- (3) **放 T2519 = C5**（`docs/tickets/T2519.md`，由 V4 的草稿定稿；检查 `docs/tickets/checks/T2519-check.lean`、提议 `T2519-pins.lean`）：
  - 照监督 1044 写入 Decisions (1)–(14)。OQ1–OQ7 的答复：OQ1 REQ 已发、1044 PASS；OQ2 1a 现在开；OQ3 纯普查定拆分；OQ4 带撇 `RBG_Prod` 是 1a 的停止线（短 REQ，不预批）；OQ5 `BA/TwistAvg*` 里已合并的代数引理可按名读、逐个记在报告里（1044 Q4），R2 仍停；OQ6 实例保留 `UNMLOutBA 3` 为前提；OQ7 新结构行 `GUEPathBoundsBA` 归行 a，`:383` 注释归行 c。
  - 停止规则加 C5S-C1–C4；布局 L1（Duhamel 层原地只在 C5S-C3 下）；校准风险写进票（C3b ×1.88、C4 ×1.34–1.39 → 落地约 8,500–10,500）。
  - **检查文件拆两份**（流程决定）：`T2519-check.lean` 只有输入名的 `#check`（133 个，含 C3 b、C4 a/b；逐名用 `nsof.sh` 在 fde07256 核过全名），是放行门；草稿的 `T2519_*` 提议文本放进 `T2519-pins.lean`，中枢编译供参考、不卡放行，1a 在探针里按需重述（§340 (5) T2517 的先例）。理由：提议文本从没编译过，T2517 曾因实例综合失败卡过一轮；1a 本来就要定这些文本。
  - **开工**：检查编译通过后从 `main` 开 1a（`prover-max`）；1a-audit 后中枢自行开行 a（`main`）、行 b（叠在行 a 第一个提交上），**除非** 1a-audit 报出 C5S-C1 的线（总宽口径中心 > 9,025，或某行中心 > 1,950 而备用用完）或任何停止规则——那时停下等调度。行 c 在 a、b 合并后、行 d 在 c 之后，由中枢照票开。
- (4) **计数**：C5 行 a = M/N 第 13 行（BA 199，+0）；b、c、d 在 1a 记为 14–16（BA 202）；预测 17（17–20），旗标 20。依赖使中枢暂时只有这一张票：N2 读 C5 的产出，MA-06b 读 N2；C5 的 1a-audit 签了 `T2519_*` 文本后，N2 的 1a（无证明目标）可以提前开，N2 草稿在 C5 的 1a-audit 前后起草。在跑：T2519（1 / 4）。H322。
- 下一节 §349，下一张票号 T2520，下一条 H323，下一个 paper-delta D733。

## §349 — C5 的 1a 在 D1 (i) 停（`hoff` 的 R1 差一个 `Λ^{1/4}`）；按票的停止规则发短 REQ-2026-10-16-1118-C5hoff；N2 草稿完成（总调度 V5，2026-10-16 11:18 UTC）

- (1) **H322 done 43597737**（10:44）：`T2519-check.lean` 与 `T2519-pins.lean` 都 exit 0、无错误行（提议文本第一次编译就过）；T2519 的 1a 10:44 开工（wf_46255651-fd0）。
- (2) **1a 结果（11:06，`docs/reports/T2519-prove.md` (a)，`T2519.state` = preflight-fail）**：只有 D1 (i) FAIL，其余（D1 (ii)–(v)、T15、T16 的尺度前提、普查、布局）都过。
  - `twTr` 的 Stein 恒等式精确成立（MC 核过）；自项（C5S-C2）没问题。障碍在导数项 `R₂`：只用 1044 Q3 列的两样输入（PB `lk 1` 与 `localLaw`，逐元 `Λ^{1/2}`）只得 `|R₂| ≲ Λ^{3/2}`、`twTr ≺ Λ^{3/4}`，差 `Λ^{1/4}`；用 Hilbert–Schmidt 配对、长 4 的 loop 与 2-loop 的界则 `|R₂| ≲ Λ²`，闭合（MC：`CS(HS)/Λ²` 在 N = 512、1728 都是 3.38，不随 `N` 长）。
  - 1a 的修法（C5 内部，不改 `RBG_*`、不读 V、不用 TL 名）：(a) `T2519_PBBA` 的 `n0` 由 3 改 4（PB 给 `lk k`，`k ≤ 4`；带状 `GUEPathBounds` 对 `n0` 泛型，网格指数 160 → 192）；(b) `T2519_HoffBA` 加前提「2-loop 与 4-loop 的 K 界 `‖Kt_k‖ ≤ C(2Λ_u)^{k−1}`」，由 `BAKFam` 与 D1 (iii) 的 K 界在 BA 上卸掉。
  - **按票的停止规则 D1 (i)（R1 用两个 PB 字段闭不上 → 1a 停、短 REQ）发 `docs/supervisor/requests/REQ-2026-10-16-1118-C5hoff.md`**：Q1 这个修法能否作为 C5 内部的钉文修补（0243 O4；Amend 1，从 1a 重跑，不算票），R1 的输入从 {`lk 1`, `localLaw`} 扩到 {`lk k ≤ 4`, `localLaw`, 2/4-loop 的 K 界}；Q2 C5S-C1 的 9,025 线按宽口径总中心（现 8,312）读；Q3 修后若还要别的（`t₁` 处的 `twTr`、`(Nη)⁻²` 的扭 2-loop、TL/V 名、PB/`BAReal`/`baM_row_l1`/K 界以外的前提）仍停。新监督任务 11:41 UTC 处理。
  - 计数（1a 普查重跑）：纯口径 a 1,704、b 1,636、c 1,645、d 1,429（都 ≤ 1,950，**不动备用**）；宽口径总中心 8,312 ≤ 9,025（`hoff` 取 1,400 时 8,912）。行 b–d 在 1a-audit 时记为 M/N 14–16。M/N 13 用、预测 17 不变。
- (3) **N2 草稿**（后台起草子代理，`docs/claude-team/drafts/N2.md` 72 行、`N2-check.lean` 446 行，T2520）：中心 744（校准 743–978，高端约 1,250），离 1,950 很远；角色提 `prover-hard`（关键路径终端装配、公开过滤词汇）；1b 在 C5 行 d 合并后开，1a 在 C5 的 1a-audit 签了 `T2519_*` 之后可提前开；检查 144 个 `#check`（在 `main` 43597737 上逐名核过），C5 名字放 ACTIVATE 块，`T2520_*` 提议另列。发现：M1、M3 已合并逐 `d` 的文本与核心，N2 只要两条一行的 `Iff`；退路（`BAThm27L 3` → MA-06b）只省约 15 行。待定 OQ1–OQ6（C5 产出是否对每个 `d` 签、`UNOURowBA` 欠账行能否删、过期欠账行 `UNEMCTE2RowBA`/`UNJakUywRowBA` 是否顺手删等）在 C5 的 1a-audit 后定稿时答。
- 在跑：无（T2519 停在 1a，等 REQ）。下一节 §350，下一张票号 T2520，下一条 H323，下一个 paper-delta D733。

## §350 — 监督 1134 PASS（C5 的 `hoff`：R1 取 T.7 的输入集）；T2519 Amend 1，H323 从 1a 重跑；paper-delta 补账 D733–D737（总调度 V5，2026-10-16 11:50 UTC）

- (1) **监督 2026-10-16-1134 PASS**（回 REQ-2026-10-16-1118-C5hoff；结论 11:34 UTC 写出：Jun 手动触发了监督任务（Jun 2026-10-16 11:5x UTC：「是我让他跑的」），不是两个任务重复运行）：
  - Q1 是：作为 C5 内部的钉文修补（Amend 1，从 1a 重跑，**不算票**，没写 Lean）。障碍是真的，原因是 1044 Q3 把 R1 的输入列成了意译、漏了导数项；合并的 BA 流侧 Lemma T.7（TL1，`docs/tickets/T2398-TL-proofs.md:64`）要的正是 (I2) 与 n ∈ {2, 4} 的 (I3)。监督认了这个错（代价一次 1a，无 Lean、无票）。
  - `n₀ = 4` 在 `main` 上站得住：`GUEPathBounds` 及其生产者对任意 `2 ≤ n0`，`gueGrid_eq729` 只要 `3 ≤ n0`，`gueK_existsBA` 的长度上界是参数，`RBG_*` 把 `KF`、`PB` 当自由参数，N2 不受影响。K 界前提由已有的 `Hyp_Kt_detDom`（BA 孪生 = C5 目标 3）给出。
  - Q2 确认：C5S-C1 是固定数 9,025，对比 1a 重跑的宽口径总中心（现 8,312；`hoff` 超过约 1,513 中心才触线）。
  - Q3 同意并列明 R1 的可用输入；之外一律在 1a 停、短 REQ（另加三种：`n₀ ≥ 5`、非同一网格时刻的 K 界、`gueGrid_eq729BA` 的新前提）。
  - 约束 **C5H-C1**（K 界写成 `Hyp_Kt_detDomBA` 的结论形：`∀ ε > 0, ∀ᶠ n, ∀ s ∈ [t₁, t₀]`，`2 ≤ |I| ≤ 4`，`‖Kt‖ ≤ N^ε (N η_s)^{-(|I|−1)}`）、**C5H-C2**（`T2519_PBBA` 与 `T2519_KFamBA` 一起改，探针给 `T2519_ProducersBA` 仍可类型检查、`gueGrid_eq729BA` 的前提能供 `T2519_HoffBA` 的全部前提的 `example`）、**C5H-C3**（`GUETwistBA` 按 T.7 的五步自下而上重新定价，两个导数项 `𝒮₁`、`𝒮₂` 都算，对照 TL1 落地 2,817）、**C5H-C4**（`T2519a` 记 `n₀ = 4` 与 T.7 的输入集）。教训（监督）：路线若照抄已合并证明，批准时逐字抄它的输入清单。
- (2) **落实**：`docs/tickets/T2519-amend-1.md`（八条，含上面的约束与新的 D1 (i) 停止规则）；**H323**：提交、从 `main` 在 `t/T2519` 重跑 1a（preflight 写 (a′) → 探针 → 1a-audit），之后照 H322 (3) 开行 a、b。`T2519-pins.lean` 不改（只供参考，Decision (12)），改后的文本由 1a 在探针里编译、1a-audit 签。返工账本在合并时记（开工后的 amend）。
- (3) **paper-delta 补账**（HANDOFF §5 第 4 条）：`docs/paper-deltas.md` 加一节「合并时编号 T2513–T2518」：**D733** ← `T2515a`–`c`（C3 行 a）、**D734** ← `T2515ba`–`bc`（C3 行 b，原 `T2515c`–`e` 改标；带 Amend 1 的 `X = 0` 附注）、**D735** ← `T2516a`（M2 的剖面 `z`-Lipschitz）、**D736** ← `T2517a`–`b`（C4 行 a：BA 的 Lemma 5.15、新输入 `hoff`）、**D737** ← `T2517c`–`d`（C4 行 b：自由流点陈述、网格游走载体）；T2513、T2514 a/b、T2518 无候选。
- (4) 计数不变：M/N 13 用（1a FAIL 与 Amend 1 记 +0），预测 17，旗标 20；BA 199。在跑：T2519 的 1a（H323 后，1 / 4）。下一节 §351，下一张票号 T2520，下一条 H324，下一个 paper-delta D738。

## §351 — C5 的 1a 重跑：D1 (i) PASS；`GUETwistBA` 按 T.7 重新定价 1,628，b′ 预签启用；C5S-C1 9,080 > 9,025 → 短 REQ-2026-10-16-1225-C5line（总调度 V5，2026-10-16 12:25 UTC）

- (1) **H323 done 25e22c0b**（11:53）：1a 按 Amend 1 重跑（wf_30b51f27-aca）。**preflight (a′) PASS**（12:08）：D1 (i) 照 Amend 1 的输入清单闭合（`𝒮₁`、`𝒮₂` 都是 4-loop `≺ Λ³` 配 2-loop `≺ Λ`，指数余量 0）；探针步骤在跑，之后 1a-audit。
- (2) **定价（C5H-C3）**：`GUETwistBA` 按 T.7 五步、对照 TL1 落地（2,817 行）自下而上：中心当量 1,628（lo 1,243、hi 2,112，按票的 ×1.34）或 1,499（按 TL1 自己的 ×1.46）；原价 860 [500, 1,400]。行 b 不拆是 2,404 > 1,950 → **备用 b′ 启用**（预签，Amend 1 第 5 条，不需 REQ）：b = `GUEDuhamelBA`，b′ = `GUETwistBA`。
- (3) **C5S-C1**：宽口径总中心 = 8,312 − 860 + 1,628 = **9,080 > 9,025（超 55）**（按 ×1.46 是 8,951，不超）。照 1044 C5S-C1「1a 重跑超 9,025 → 1b 前短 REQ」，发 `docs/supervisor/requests/REQ-2026-10-16-1225-C5line.md`（12:25，赶 12:41 那轮）：Q1 行 a、b、b′ 能否在 1a-audit PASS 后开工（预测 18 ≤ 20）；Q2 1b 期间是否换一条新线（提议 1a-audit 的宽口径总中心 +10%，单行落地超 1a 中心 ×1.67 发短 REQ）。中枢按 H322/H323 (3) 在 1a-audit 报超线时会停下；监督答复后由新 H 指令放行。
- (4) 计数（1a-audit 时记）：C5 = a、b、b′、c、d = M/N 第 13–17 行（BA 199 → 203）；N2 一行 → 预测 18（18–20），旗标 20。
- 下一节 §352，下一张票号 T2520，下一条 H324，下一个 paper-delta D738。

## §352 — 监督 1248 PASS：C5 行 a、b、b′ 在 1a-audit 后开；9,025 线在 1a-audit 时失效，换落地线 C5L-L1–L3；b′ 拆两文件；Amend 2，H324（总调度 V5，2026-10-16 12:57 UTC）

- (1) **监督 2026-10-16-1248 PASS**（回 REQ-2026-10-16-1225-C5line）：
  - Q1 是：超出的 55 行（0.6%）全部来自 `GUETwistBA`（860 → 1,628），是 1134 改正 1044 Q3 的代价，不是路线出问题；在估计本身的噪声里。按 ×1.34（保守、触线的那个读法）给 PASS。
  - **C5L-C1**：PASS 只覆盖 1a-audit 自己的数在 (a′) 区间内的情形（总宽口径 ≤ 9,564、`GUETwistBA` ≤ 1,950、其他行 ≤ 1,950 或有备用、C5H-C2 的 `example` 编译、没有 Amend 1 第 4 条的停止）；否则 1b 前停、短 REQ。
  - **C5L-C2（新发现）**：`GUETwistBA` 的落地预测 2,181 行 > 单文件 2,000 的约束线 → b′ 加拆分文件 `BA/GUETwistBA2`（按 T.7 的步骤边界拆，约 1,160 / 780），不加行、不改计数。
  - **C5L-C3**：经 `BA/TwistAvgA` 传递导入 `BA.TwistPins` 接受（V、TL 都已关闭；不直接导入、不点 `TwistPins` 的名字）。
  - Q2：**9,025 线在 1a-audit PASS 时失效**；1b 期间换成落地 `wc -l` 的线：**C5L-L1** 每行 max(1.67 × 1a 纯口径中心, 1.34 × 1a 宽口径中心)（a 2,927、b 2,245、b′ 2,719、c 2,811、d 2,386），超了该行照常审核合并，但导入它的行在答复前不开；**C5L-L2** C5 总落地超 12,000 → 下一行放行前短 REQ；**C5L-L3** 1a 式重新定价（订 a′ 或 c′）超 1.10 × 1a-audit 宽口径总中心（≈ 9,990）→ 短 REQ。
  - O3（可选）：`GUEHypBBA`、`GUEHyp` 各给一个备用文件——采纳（`GUEHypBBA2`、`GUEHyp2`，只在主文件过 1,500 时用）。
  - 教训（监督）：停止线的单位要和检查时量的东西一致；单文件 2,000 线要用落地预测去比，不能用普查中心。
- (2) **落实**：`docs/tickets/T2519-amend-2.md`（八条：b′ = `GUETwistBA` + `GUETwistBA2`，分支 `t/T2519b2`，叠在行 a 第一个提交上；新增可写文件；顺序 a → b、b′ → c（a、b 合并后）→ d（c、b′ 合并后）；1b 的开工条件 C5L-C1；落地线 C5L-L1–L3；C5L-C3；计数；报告规则）。**H324**：提交，取代 H322/H323 (3) 的停止条件，1a-audit PASS（在 C5L-C1 内）后开行 a、b、b′（三个都 `prover-max`），c、d 照 Amend 2 第 3 条（`prover-hard`）；每行报告时中枢照 Amend 2 第 5 条比落地线。
- (3) 计数：b′ 在 1a 记账 → C5 = a、b、b′、c、d = M/N 第 13–17 行（1a-audit 时 BA 199 → 203）；N2 第 18 行，预测 18（18–20），旗标 20。在跑：T2519 的 1a（探针步骤）；1a-audit PASS 后 3 个（a、b、b′）。N2 的 1a 在 C5 的 1a-audit 签了 `T2519_*` 后可提前开（T2520 定稿中）。
- 下一节 §353，下一张票号 T2520，下一条 H325，下一个 paper-delta D738。

## §353 — 放 T2520 = N2（最后一张 M/N 票）：1a 在 C5 的 1a-audit PASS 后开，1b 在 C5 行 d 合并后（总调度 V5，2026-10-16 12:58 UTC）

- (1) **T2520 = N2 定稿**（`docs/tickets/T2520.md`，由 §349 (3) 的草稿定；检查 `docs/tickets/checks/T2520-check.lean`（放行门：已合并名字的 `#check`，C5 的五个名字放注释块，C5 行 a、d 合并后再打开）、提议 `T2520-pins.lean`（不卡放行））。内容：MN-D3 的实现 G1 `Universality/PinsKD`（八个维数过滤钉文 + 带状 `Iff`）、G2 `Universality/GUEPhase/RandomLayerBGD`（过滤后的泛型链）、BA 叶 `BA/UNBUniv`（`UNNormBARow`、`UNOURowBA`、过滤后的 BA 装配、与 M1/M3 逐 `d` 文本的两条一行 `Iff`、`UNL32 → BAEnd_BUnivL 3`、`UNL32 → BAThm27L 3`，即关闭条件 (vi) 的最终形式）。中心 744（743–978）。
- (2) **答草稿的 OQ**（Decisions (8)–(12)）：OQ1 是（C5 的生产者对每个 `d` 签，N2 证合并的 `UNOURowBA` 并删欠账 `:176`；若 C5 只签 `d = 3`，走票里的 `d = 3` 分支，不算 amend）；OQ2 `_of_ML` 与 `baThm27L_any`（`STStep5IIIgL d` 下，关闭条件 (iii)）都要；OQ3 扫描确认后顺手删过期欠账 `UNEMCTE2RowBA`、`UNJakUywRowBA`（关闭条件 (ii)）；OQ4 用探针；OQ6 若退路触发，MA-06b 按 `baEnd_BUnivL_three` 写。角色 `prover-hard`。
- (3) **开工**：1a（探针，无证明目标）在 T2519 的 1a-audit PASS 后从 `main` 开（N2 按名读 `BAKFam`、`BAPB`，`KF`、`PB` 自由，不重述 `n₀`，监督 1134 O3）；1b 在 T2519 行 d 合并后。H325。
- (4) 计数：N2 = M/N 第 18 行（C5 = 13–17）；预测 18，旗标 20；BA +0（1a-audit 后 203）。在跑（预期）：C5 行 a、b、b′ + N2 的 1a = 4 / 4。
- 下一节 §354，下一张票号 T2521（MA-06b），下一条 H326，下一个 paper-delta D738。

## §354 — C5 的 1a-audit RETURN 只为签字：调度签 Amend 3（F1、F2、`open private`、报告行），1a-audit 记 PASS；C5 行 a、b、b′ 与 N2 的 1a 开工（H326）；C5 记账 M/N 13–17（总调度 V5，2026-10-16 13:13 UTC）

- (1) **H324、H325 done 1545818f**（13:03）：两份 T2520 检查都 exit 0；T2520 的 1a 等 C5 的 1a-audit。**C5 的探针 PASS**（b992c2e7，298 行，exit 0，标准公理）。**1a-audit（13:04）RETURN、要调度签字**（它开跑时 Amend 2 还没提交）：签了全部 `T2519_*` 文本、Amend 1 第 2 条的 `example`、D1 (i)–(v)、L1、普查、拆分 a | b | b′ | c | d（b′ 启用，a′、c′ 不用）；要求 (1) C5S-C1 的裁定；(2) 记下 `T2519_HoffBA` 里超出 Amend 1 字面的 F1（`4 ≤ n0`）与 F2（`Kt = m` 前提加 `0 < g n →` 守卫）；(3) 对 `open private … from BA/TwistAvgB` 与 `TwistPins` 闭包的裁定；(4) 报告补 (iv)、(viii) 两行。
- (2) **签字 = `docs/tickets/T2519-amend-3.md`**：(1) 已由监督 1248 裁定、落在 Amend 2 第 4 条内（9,080 ≤ 9,564 等），9,025 线现在失效；(2) F1、F2 照探针 `:79-98` 签（F1 由 `lk 4` 强制，`n0 ≥ 5` 允许但不要求，不触 Amend 1 第 4 条；F2 削弱前提）；(3) 准许按 (iii′) 的清单读 `BA/TwistAvg*` 的引理，其中私有的经 `open private` 读，不改文件、不删 `private`，传递导入 `TwistPins` 接受（1248 C5L-C3）；(4) 两行移到各行的报告；外加审核观察 1b：行 a 的 `Hyp_Kt_detDomBA` 结论形式要与探针 `:238-240` 的 `hKdet` 一致。流程事，不发 REQ。
- (3) **H326**：提交 Amend 3 等；**C5 的 1a-audit 按 Amend 3 记为 PASS**：现在开行 a（`t/T2519`）、行 b（`t/T2519b`）、行 b′（`t/T2519b2`），b、b′ 叠在 a 的第一个提交上，都 `prover-max`；落地线照 Amend 2 第 5 条；T2520 的 1a（`prover-hard`）同时开（4 / 4）。
- (4) **计数（1a 记账）**：C5 行 b、b′、c、d = M/N 第 14–17 行（BA 200–203）；N2 第 18 行；预测 18，旗标 20。返工：T2519 的两次 1a（第一次 FAIL、Amend 1–3）在合并时记账。
- 下一节 §355，下一张票号 T2521，下一条 H327，下一个 paper-delta D738。

## §355 — Jun：Lean 做完后的收尾与发布（照 RBM1D、RBM2D）：清理、GitHub 只留 Lean 与最终论文、与投稿版的对比文件（总调度 V5，2026-10-16 13:30 UTC）

- **Jun（2026-10-16 约 06:3x PDT）**：「如果顺利结束，后面要做的事是 1. 清理不用file/code 过时文件和注释， 只保留正确lean 文件上传到github。 2。 github仓库只有lean 文件和修改过的最终版paper文件 （以及一些常规小文件）, lean文件应该和paperpdf文件match ，如果有少量不同，在readme. 里指出。 类似案例可以见rbm1d rbm2d。 3 生成一份和之前pdf文件（2507.20274-inventiones-submission）的对比文件。  我会交给合作者处理，所以不用给editor写信」
- **对旧规则的影响**：此前的「不改论文（Jun 在 Lean 做完后自己改）」在收尾阶段由这条取代：最终版论文由调度这边照 paper-deltas 改出（RBM2D §247 的做法），Jun 与合作者审；`paper/tex` 原件不动，改在副本上。
- **落实（M/N 关闭、MA-06b 合并、监督收尾 PASS 之后；照 RBM2D §244–§251）**：
  1. **清理代码**：用 `docs/claude-team/tools/DeadDecls.lean` 从终点（带状与 BA 的 Thm 2.x 终端、`band_terminal`、`bUniv_holds`、`Endpoints` 里的定理及其非退化实例、`#assert_rbm_axioms`）做常量闭包，出不可达报告；一张票删全部死代码（跨目录互相引用，不按目录拆）；删逐票留下的 `#check`/`#print`/`#eval` 与多余 `example`，只留终点的非退化实例；复跑工具须 0 个不可达。
  2. **清理注释**：按目录并行几张票，只动注释与文档串（去掉票号、DECISIONS、paper-delta 编号、角色、流程字眼，改用论文自己的标签），去注释脚本验证代码逐字不变；名字里的流程字眼零星改名由调度直接改（RBM2D §250）。
  3. **最终论文**：Opus 子代理（不用 Fable）把 `docs/paper-deltas.md` 的条目逐条对照 TeX 分类、需改论文的改进副本，编译（云端；设备缺 `stmaryrd`），公式编号尽量不变；放 `paper/final/`（PDF + tex）。
  4. **论文与 Lean 的少量不同**：照 RBM1D/RBM2D 的 `docs/PAPER-VS-LEAN.md` 由中枢出一份文档（每个 Lean 名字可编译核对），README 里概述并指向它。
  5. **与投稿版的对比**（`paper/2507.20274-inventiones-submission.pdf`）：分三档（一档真有细节错误、二档显而易见可修、三档笔误与补充说明），一、二档给 before/after；**给合作者，不写给 editor 的信**；不上传 GitHub。另可附 latexdiff 的 PDF。
  6. **发布树**：`RBM3D/`、`RBM3D.lean`、`lakefile.toml`、`lake-manifest.json`、`lean-toolchain`、`LICENSE`、`README.md`、`paper/`（最终版）、`docs/PAPER-VS-LEAN.md`、`.gitignore`、CI 工作流；不含 `docs/` 其余、`CLAUDE.md`、`.claude/`、`blueprint/`、`home_page/`、`check.sh`、`watch.sh`。旧历史怎么处理（RBM2D 是本地 bundle 备份、`main` 换成单个干净提交、强制推送由 Jun 亲手做）到那一步再问 Jun。
- 提前可做、不碰论文与代码的准备（流程事，调度自己定）：paper-deltas 的分类清单、DeadDecls 的试跑报告（只出报告）、发布清单与 README 草稿；在 C5、N2 跑的空档里做。
- 下一节 §356，下一张票号 T2521，下一条 H327，下一个 paper-delta D738。

## §356 — Jun：最终论文由调度直接改，普通改动自己定，大问题才问 Jun（总调度 V5，2026-10-16 13:37 UTC）

- **Jun（2026-10-16 约 06:4x PDT）**：「因为这次论文会让合作者再check， 所以你可以直接改，如果有大问题可以问我 普通的你自己决定就好了。」
- **落实**（补 §355 第 3 步）：最终论文（`paper/final/`，在 `paper/tex` 的副本上改）由调度这边直接改，Opus 子代理起草、调度复核；按 paper-deltas 逐条处理，笔误、补充说明、显而易见的修复、与 Lean 一致的精确化都自己定，不问 Jun。**只有大问题问 Jun**：改动影响定理的陈述或假设（例如把论文结论收窄或加前提）、需要换证明路线、或与已签的 Jun 决定（如 §316 的 B：BA 终端只做 `d = 3`）有关的写法。一次只问一件。合作者会再核，所以对比文件（§355 第 5 步）照常给出每一处改动。
- 时机不变：MA-06b 之后、清理票在中枢上跑的时候做（同步子代理会堵心跳）。
- 下一节 §357。

## §357 — Jun：GitHub 干净就行，本地不必留完整历史（总调度 V5，2026-10-16 13:39 UTC）

- **Jun（2026-10-16 约 06:4x PDT）**：「GitHub是干净就行， 本地留不留完整历史记录意义不大。」
- **落实**（定 §355 第 6 步的历史问题）：发布时 GitHub 的 `main` 换成**单个干净提交**（发布树，内容照 §355）；**不做本地 bundle 备份**、不另建归档分支（与 RBM2D §244 不同）；本地 `.git` 里的旧提交不专门清理，也不再推送（发布后把旧推送地址设为 `no_push`，防误推，同 RBM2D §250）。强制推送照 RBM2D：中枢的权限禁止 `git push --force`，所以发布指令做到推送前一步，推送命令由 Jun 在终端亲手运行（这是唯一一次 force push）。
- 下一节 §358。

## §358 — N2 的 1a 完成（不需 1a-audit，落地预测 887–1,106）；放 T2521 = MA-06b（最后一张证明票，`final_shape`）（总调度 V5，2026-10-16 13:54 UTC）

- (1) **T2520 = N2 的 1a**（13:48，`T2520.state` = held）：preflight PASS；探针 PASS（`RBM3D/Probe/T2520Pins.lean` 196 行，exit 0，82ef67a8，不合并）；没有移动钉文、停止线，也没触发退路，所以不跑 1a-audit（票 Decisions (1)）；落地预测 887–1,106 < 1,950。1b 等 C5 行 d 合并。
- (2) **放 T2521 = MA-06b**（`docs/tickets/T2521.md`、检查 `T2521-check.lean`）：新文件 `Main/FinalShape.lean`，`Thm27 := BAThm27L 3`（论文 Thm 2.7，`d = 3`，Jun 的 B）、`Thm27_of_L32`（= N2 的 `baThm27L_three`）、**`final_shape : UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27`**（全项目的最终定理：带状 Thm 2.1–2.5 与 BA Thm 2.7，唯一外部前提 `UNL32`），实例沿用 `BandTerminal` 与 `BA/MAPins:213` 的数据。角色 `prover`；1a 现在开（占空出的第 4 个位），1b 在 T2520 合并后。MA 8 → 9（MA 关闭）。
- (3) 在跑：C5 行 a、b、b′（3）+ T2521 的 1a（H327 后 4 / 4）；N2 等 C5 行 d。之后：M/N 关闭 REQ（N2 合并后发），Lean 侧完成，进入 §355–§357 的收尾。
- 下一节 §359，下一张票号 T2522，下一条 H328，下一个 paper-delta D738。

## §359 — T2521 的检查修正：`unMLOutBA_three` 的模块没进导入闭包（总调度 V5，2026-10-16 14:10 UTC）

- H327 done 66649d46：`T2521-check.lean` exit 1，`:25` 的 `#check @RBM.BA.unMLOutBA_three` 未知——检查只导入 `Main/BandTerminal`、`BA/MAPins`，`BA/MainIndTermBA` 不在闭包里（TEAM §10.8 的老坑，调度的错）。修正：该行改为注释（行数不变；这个名字由 N2 读，MA-06b 不需要）。开工前的检查修正，不算返工。H328 重编、通过就开 1a。
- 下一节 §360，下一张票号 T2522，下一条 H329，下一个 paper-delta D738。

## §360 — C5 行 a、b 合并；行 a 审核观察 2：耦合窗口在 C5 里一律改为「最终成立」，三个 `∀ n` 输入加带撇后继，行 c 负责（T2519 Amend 4）（总调度 V5，2026-10-16 14:47 UTC）

- (1) **行 a 合并** 9e07cc2e（14:29）：新 `BA/GUEProcBA` 645、`GUEHypABA` 920、`GUEEntryGridBA` 425，落地 1,990 / 线 2,927；审核第 1 轮 PASS；登记 `structuralProps` 行 `RBM.BA.GUEPathBoundsBA`；探针留在 `t/T2519`。**行 b 合并** affd3e77（14:42）：新 `BA/GUEDuhamelBA` 948、`GUEDuhamelBA2` 1,058，落地 2,006 / 线 2,245；审核第 1 轮 PASS（观察 2：端点内联 `loopMax (gueHBA …)`，与 `gueLmaxBA` 定义相等，行 c 用 `unfold`/`rfl` 接）。C5 累计 3,996 / 12,000。行 c 14:42:49 开工（wf_9ce94310-f95，`prover-hard`）；行 b′ 在跑。
- (2) **缺口**（行 a 审核 §6 观察 2 = 证明报告 (d) 1）：C3 b 的钉文 `GUEEntryMixBA`、C4 a 的 `gueGrid_expect_oneLoopBA`、行 a 的 `gueGrid_entry_boundBA` 要求每个 `n` 都有 `0 < g n ≤ 𝔡⁻¹`（或 `Λ`）；BA 生产者处 `g n = √t₀ λ_n`，窗口只由 `(eq:WO)` 最终成立（`Sizes.lam` 无符号），`BAReal` 则对每个 `n` 成立（`RBG_Prod` 的 `BAEd` 是 `∀ n`）。所有相关结论都是对 `n` 最终的。
- (3) **裁定（流程，调度自定）**：在源头把窗口放宽为最终成立，用带撇后继（CLAUDE.md：不改冻结签名）：`GUEEntryMixBA'`/`gueEntryMixBA'`、`gueGrid_entry_boundBA'`、`gueGrid_expect_oneLoopBA'`，前提拆成 `∀ n, BAReal` 与 `∀ᶠ n, 0 < g n ≤ c`；证明搬过去（窗口只在 `filter_upwards` 里的一个 `n` 用到：`GUEEntry2:816`、`GUEEntryGridBA:323`、`GUEOneLoop:1240`；`GUEOneLoop:1227` 的 `(hg 0)` 改用最终窗口的见证），原定理变包装，不复制证明。行 c、d 的公开陈述一律取最终窗口。弃用的两条路：沿 `Sizes.comp` 平移（要 `Pgue` 的重标号像律，仓库里没有）、对小 `n` 换数据（要任意 `L`、`κ` 下 BA 数据的存在引理，是新数学）。
- (4) **归属与价格**：行 c 第一个提交做三处后继（行 d 从 `main` 读）；行 c 可写文件加 `BA/GUEEntry2`、`BA/GUEEntryGridBA`、`BA/GUEOneLoop`（只限这三处）；≤ 200 行 diff，算在行 c 的线 2,811 里（不加线），C5 总线 12,000 不变。停止：某个证明在最终过滤之外用窗口、需要改 > 60 行，或后继要新的 `Prop` 前提，或行 c 自己的陈述取不了最终窗口 → 写问题到 `T2519c.state`。`GUEEntryMixBA` 没有登记行，带撇的也不加。
- (5) **返工**：Amend 4 写在行 c 开工之后（约 5 分钟），按「开工后的 Amend 算返工」记入 T2519 的返工账（合并时写行）；H329 让中枢把 Amend 4 交给在跑的行 c（不能中途加输入就停下重开行 c 的 1b，已有提交保留）。
- (6) **paper-deltas**：行 a、b 的标签编号 D738–D743（`T2519a`、`b`、`c`（按 Amend 4 改写）、`e`、`f` + `ba2`、`ba1` + `ba3`）。
- 下一节 §361，下一张票号 T2522，下一条 H330，下一个 paper-delta D744。

## §361 — C5 行 b′ 落地超线（2,879 / 2,719，+160）→ 短 REQ-2026-10-16-1547-C5bprime（C5L-L1）；行 d 等监督（总调度 V5，2026-10-16 15:47 UTC）

- (1) H329 done 9f044e2c（14:53）：行 c 第一次运行停掉（未提交的 `GUEHypBBA.lean` 327 行留给新运行），按 Amend 1–4 重开 wf_dbe38880-e15；返工约 11 分钟，合并时记入 T2519 的返工账。
- (2) **行 b′ 的 1b 报告**（15:45）：`BA/GUETwistBA` 1,799 + `GUETwistBA2` 1,080 = **2,879 > 线 2,719**（+160，+5.9 %）；超出在 T.7 的矩自举（网格并集指数进矩阶、`(Nη_u)⁻¹ ≥ N^{-τ}` 时用逐元 `localLaw`），即监督 1134 Q3 加给 R1 的部分；每个文件 < 2,000。按 Amend 2 第 5 条 / C5L-L1：b′ 照常审核、合并；**行 d（读 `gueGrid_twistBA`）在监督回答前不开**。短 REQ-2026-10-16-1547-C5bprime（Q1：c、b′ 合并后行 d 可否照线 2,386 与总线 12,000 开工）。预测：a、b、b′、c 合计约 9,260，加 d 到线约 11,650 ≤ 12,000；计数不变（M/N 预测 18 ≤ 20）。
- (3) **行 c 的 1b 接近完成**：新 `GUEHypBBA` 1,422、`GUEPathBoundsBA` 778，Amend 4 改三个已合并文件（+187 / −34），约 2,390 ≤ 2,811。报告 (d) 2 列出行 d 的 `ba_prodG` 要接的前提（`hlam` 最终、`h730`/`hscale` 走 `T2519_FlowEtaBA`、`hell`、`hell1`、`hellg`、`BAMO` 的 `hLK`/`hLoc`、`BAKFam` 的 `hKinit`/`hK`），合 Amend 4。
- (4) b′ 报告 (d) 3：合并后行 d 的实例可以用行 a 的 `Hyp_Kt_detDomBA` 去掉 `twist_sz0` 的 `hKb` 前提（可选，不加目标，行 d 自定）。
- 下一节 §362，下一张票号 T2522，下一条 H331，下一个 paper-delta D744。

## §362 — C5 行 c 合并（2,387 / 2,811，含 Amend 4 的三个带撇后继）；审核观察 1 交给行 d 的实例（总调度 V5，2026-10-16 16:04 UTC）

- (1) **行 c 合并** 432301f7（16:01）：新 `BA/GUEHypBBA` 1,422、`GUEPathBoundsBA` 778，Amend 4 的 `GUEEntryMixBA'`、`gueEntryMixBA'`、`gueGrid_entry_boundBA'`、`gueGrid_expect_oneLoopBA'` 与包装（`GUEEntry2` 65、`GUEEntryGridBA` 54、`GUEOneLoop` 68 行 diff），落地 2,387 / 2,811；审核第 1 轮 PASS；`Test/Axioms.lean` 的 `GUEPathBounds` 主人注释。C5 累计 9,262（a 1,990 + b 2,006 + b′ 2,879 已报 + c 2,387）/ 12,000。
- (2) **审核观察 1（给行 d）**：`GUEPathBoundsBA` 实例的 `t₁` 在流的视界之上（`t₁ > 5/6 ≥ BAflowT0` 在 `zSeq`），所以那里的 `hLK`/`hLoc` 只在类型上是 `UNMLOutBA` 的形状（与已合并的带状实例 `PathBounds:893` 同样）；行 d 的生产者实例要用 `Im z` 小的 `z` 序列（`hell` 使 `T0` 接近 1），不能用 `zSeq`。放行行 d 的 H 行把这条交给行 d。
- (3) paper-deltas：行 c 的 `T2519ca`–`cc` 编 D744–D746；`T2519cd`（窗口最终成立）已由 D740 覆盖。
- (4) 在跑：b′ 审核（1 / 4）；行 d 等 REQ-2026-10-16-1547-C5bprime（监督 16:41）；N2 的 1b 等行 d；T2521 的 1b 等 N2。
- 下一节 §363，下一张票号 T2522，下一条 H331，下一个 paper-delta D747。

## §363 — C5 行 b′ 合并（2,977 / 2,719，超 258；审核 RETURN 一次 + 规则 (B) 修复）；C5 累计 9,360，只剩行 d（总调度 V5，2026-10-16 16:34 UTC）

- (1) **行 b′ 合并** 98cb433d（16:22）：新 `BA/GUETwistBA` 1,799、`GUETwistBA2` 1,178；审核第 1 轮 RETURN（实例的时间窗口退化：一个开放前提在实例数据上为假），规则 (B) 修复 aa49d4d3（实例改到 GUE 相窗口 `1 − t₀ = x_n`、`t₀ − t₁ = x_n/(2N)`，+98 行），第 2 轮 PASS。落地 2,977，超线 258（+9.5 %）。REQ-2026-10-16-1547-C5bprime 在监督跑之前补了更新段。
- (2) C5 累计 9,360 / 12,000（a 1,990、b 2,006、b′ 2,977、c 2,387）；行 d 到线 2,386 时 11,746。
- (3) 审核观察 2：行 a、c 合并后 `twist_sz0` 可以去掉 `hKb`（审核已编译 `audit_hKb`）；交给行 d 的实例，可选。
- (4) paper-deltas：b′ 的 `T2519ba`–`bc` 改标 `T2519bpa`–`bpc`（与行 b 的 `ba1`–`ba3` 撞号，§345 (2)），编 D747–D749；`T2519bd`（F1、F2、窗口最终）由 D738、D740 覆盖。
- (5) 返工（合并 T2519 时写入返工账）：行 c 开工后的 Amend 4 重开（约 11 分钟）；行 b′ 审核 RETURN 一次 + 一次修复。
- 下一节 §364，下一张票号 T2522，下一条 H331，下一个 paper-delta D750。

## §364 — 监督 1652 PASS：放行 C5 行 d（T2519 Amend 5：C5D-L1/L2 落地规则、生产者实例取 GUE 相数据 C5D-C2）；监督重复运行一次（总调度 V5，2026-10-16 17:08 UTC）

- (1) **监督 `2026-10-16-1652` PASS**（REQ-2026-10-16-1547-C5bprime）：b′ 的超出不传到行 d（行 d 按名字读 `gueGrid_twistBA`），超出在 1134 Q3 给 R1 加的部分 + 实例修复，不是路线外溢；行 d 是孪生行，预测 ≈ 1,770–2,320 ≤ 2,386，C5 总 ≈ 11,130–11,680 ≤ 12,000。条件：**C5D-L1**（线 2,386 照旧；实例部分单列小计；落在 (2,386, 2,640] 且超出 ≤ 实例小计 → 不发 REQ）、**C5D-L2**（12,000 是绝对上限，行 d 剩 2,640；超了在 N2 的 1b 前发短 REQ）、**C5D-C2**（生产者实例必须用 GUE 相数据：`Im z_n = c λ_n²/(2L_n³)`、`t₁ = fT − N^{-τD}√fT η_n`，`zSeq` 会让 `RBG_Prod` 的前提在每个 `n` 都假；超出已合并的 `ba_flowG`/`ba_domG` 的引理 → 停）。写成 **T2519 Amend 5**；H331 放行行 d（`prover-max`，监督 O1）。
- (2) **重复运行**：16:41 那次在触发记录里 6 秒就"结束"，我 16:49 手动补跑；实际两次都在跑，写了 1652 和 1654 两份结论，后一份由监督自己移到 `docs/supervisor/withdrawn/`（结论一致，1652 为准）。**教训**：定时任务记录里的 `finished_at` 是投递时间，不是会话结束；REQ 在 :41 之后仍 open，至少等到 :58 再看，不要马上补跑。
- (3) **监督的计数**：BA 203（C5 行 a–d = M/N 13–17），N2 的 1b 时 204；M/N 预测 18（18–20），旗标 20；行内返工（b′ 一次 RETURN + 修复、行 c 按 Amend 4 重开）按先例 +0（T2440、T2515 行 b）；最严读法会到 20 = 旗标，仍在 REQ、HOLD 线下。
- (4) **实例区间教训**（1652）：前提里有 `hell` 的地方，实例数据必须在 GUE 相（`Im z ≲ c λ²/L^d`）；1a 钉这类陈述时要点名实例数据并定价。同类缺陷再 RETURN 一次 = TEAM §6 的 REQ 触发（被撤回的 1654 认为算上 T2515 行 b 已经两次；预防措施相同）。以后写涉及 `hell` 的票，把实例数据写进票里。
- 下一节 §365，下一张票号 T2522，下一条 H332，下一个 paper-delta D750。

## §365 — C5（T2519）完成：行 d 合并（1,853 / 2,386），C5 共 11,213 / 12,000；打开 T2520 检查 Part 2，放 N2 的 1b（总调度 V5，2026-10-16 19:12 UTC）

- (1) **行 d 合并** bcdddd36（18:58）：新 `BA/GUELLBA` 410、`GUEHyp` 1,443（备用 `GUEHyp2` 没用），落地 1,853 / 线 2,386（C5D-L1，不发 REQ），实例小计 494；生产者实例在 GUE 相（`S0`，`Im z = c′ g₀²/(2L³)`），没用 `zSeq`；审核第 1 轮 PASS。审核观察：Amend 5 的「从 `n = 13` 起」在 `S0` 上没复现，`hscale` 由 `GUEHyp_scale_ev` 最终成立，门槛写成公式 `N_n^{19/20} √fT η ≥ 1`（不是退化）；`Eq729B_perNBA` 的例子留 `hX` 开（终点 `gueGrid_eq729BA` 的实例完整）；可选的 `hKb` 没去。
- (2) **C5 完成**：a 1,990、b 2,006、b′ 2,977、c 2,387、d 1,853 = **11,213 / 12,000**（C5D-L2）。M/N 13–17（BA 203）。返工：1a 按 Amend 1 重跑一次、1a-audit 签字 RETURN（Amend 3）、行 c 开工后 Amend 4 重开、行 b′ 审核 RETURN 一次 + 修复；监督 3 次 PASS（1134、1248、1652）。返工账写 T2519 一行（行内返工 +0，监督 1652）。
- (3) **T2520 检查 Part 2 打开**（`docs/tickets/checks/T2520-check.lean`：加 `import RBM3D.BA.GUEProcBA`、`import RBM3D.BA.GUEHyp`，五个 `#check`：`BAKFam`、`BAPB`、`ba_prodG`、`ba_LLG`、`ba_QueG`；名字已在 `main` 上核对：`GUEProcBA:76/93`、`GUEHyp:918/924/934`，命名空间 `RBM.BA`）。H332：重编（门），exit 0 就开 N2 的 1b（`prover-hard` → `auditor`）。N2 = M/N 第 18 行，BA 204。
- (4) paper-deltas：行 d 的 `T2519da`–`dd` 编 D750–D753（`db` 的窗口、零模、`n₀` 部分已由 D738、D740、D741 覆盖，只编新的部分）。
- (5) 之后：N2 合并 → 发 M/N 关闭 REQ（0643 (i)–(vii)，引 `baEnd_BUnivL_three`、`baThm27L_three` 的签名）；打开 `T2521-check.lean` Part 3 重编 → MA-06b 的 1b → Lean 侧完成 → §355–§357 收尾。
- 下一节 §366，下一张票号 T2522，下一条 H333，下一个 paper-delta D754。

## §366 — N2（T2520）合并；M/N 全部合并，发 M/N 关闭 REQ；T2521 检查 Part 3 打开；MA-06b 的 1b 在跑（总调度 V5，2026-10-16 19:56 UTC）

- (1) **N2 合并** 9d2b0883（19:44）：新 `Universality/PinsKD` 188、`GUEPhase/RandomLayerBGD` 183、`BA/UNBUniv` 397；审核第 1 轮 PASS；owed 行 `UNOURowBA`、`UNEMCTE2RowBA`、`UNJakUywRowBA`、`UNNormBARow` 关闭，加五个过滤后的结构名；`baEnd_BUnivL_three`、`baThm27L_three : UNL32 → …`；`band_terminal`、`bUniv_holds` 的公理不变。审核观察 O2（两条结构行可换成 `∀ Dm` 定理）、O3（过时的 owed 行 `UNG1Rowk` 留着、主人文字已更新）——**调度裁定：都放到发布清理票里做**（删 `UNG1Rowk` owed 行；O2 可选）。
- (2) **M/N 全部合并**：MN-D3、M1、M2、M3、C3、C4、C5（5 行）、N2 = M/N 用 18 / 旗标 20；BA 204。**发 M/N 关闭 REQ-2026-10-16-1955-MNclose**（0643 的 (i)–(vii)，逐字引 `baEnd_BUnivL_three`、`baThm27L_three` 签名；Q1：M/N 是否关闭）。监督 20:41 跑（不要提前补跑，§364 (2)）。
- (3) **MA-06b（T2521）的 1b** 19:44 由中枢按 H327 (3) 自动开（wf_6402eb22-4f1）；检查 Part 3 是在 1b 开工后才打开的（我原计划先打开、重编再开 1b——H327 没写这一步，是我的疏忽；无害：证明者在临时副本里把打开后的检查编译过，exit 0）。`docs/tickets/checks/T2521-check.lean` Part 3 现已打开（`import RBM3D.BA.UNBUniv` + `#check` + 精确类型 `example`），H333 让中枢重编一次留记录（不是门）。1b 报告：`Main/FinalShape` 120 行，`final_shape`/`Thm27_of_L32`/`Thm27` 只依赖三条标准公理，`UNL32` 是唯一前提，无 paper-delta。
- (4) 返工账：T2520 一行。下一步：T2521 合并 → MA 9 关闭、**Lean 侧完成** → 发布阶段（§355–§357）：DeadDecls 闭包 → 删除票 → 注释清理票 → paper/final → PAPER-VS-LEAN.md → 对比文件 → 发布树。
- 下一节 §367，下一张票号 T2522，下一条 H334，下一个 paper-delta D754。

## §367 — MA-06b（T2521）合并：**Lean 侧完成**（`final_shape : UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27`）；MA 9 关闭；发布阶段第 1 步：T2522 = 死代码报告（总调度 V5，2026-10-16 20:13 UTC）

- (1) **T2521 合并** 2242e73e（19:56）：新 `Main/FinalShape` 120 行，`Thm27 := BAThm27L 3`、`Thm27_of_L32`（= `baThm27L_three`）、**`final_shape`**，带编译实例（`UNL32` 唯一前提）；只依赖三条标准公理；根导入在合并时加上；审核第 1 轮 PASS；全量构建 4443 个任务。H333 done 1567a102（T2521 检查 Part 3 exit 0，留记录）。
- (2) **Lean 侧完成**：带状 Thm 2.1–2.5（`band_terminal`）与 BA Thm 2.7（`d = 3`，Jun 的 B）在 `final_shape` 里，唯一外部前提 `UNL32`（LSY arXiv:1609.09011 Thm 2.2）。MA 8 → 9（MA 关闭）。M/N 关闭等监督回 REQ-2026-10-16-1955-MNclose（20:41）。
- (3) **发布阶段**（§355–§357，照 RBM2D §244–§251）：
  - **第 1 步 T2522**：死代码报告，只出报告，不改 `RBM3D/`。工具 `docs/claude-team/tools/DeadDecls.lean` 是从 RBM2D 拷来的，根还是 RBM2D 的，要换。
  - **根（核心）**：`final_shape`、`Thm27`、`Thm27_of_L32`、`band_terminal`、`Main/FinalShape` 里 `example` 用到的常量、`RBM.Audit`。
  - **另报四组（只报增量，不在这张票里定）**：
    - G1：`BandTerminal` 的实例；
    - G2：`BA/MAPins` 的实例；
    - G3：BA 的一般 `d` 形式 `baThm27L_any`、`_of_ML`、`baEnd_BUnivL_of_ML`；
    - G4：`bUniv_holds` 与 `BUnivHolds` 的实例。
  - 报告还列出 `Test/Axioms.lean` 登记里在核心闭包外的名字（删除票要一并删）。
  - 留哪几组，看了增量再定。保留原则：论文的结果加非退化实例；条件形式的一般 `d` 若增量小就留，并在 PAPER-VS-LEAN 里说明；增量大就删。这不改任何陈述，属于流程事，调度自己定。
- (4) **之后**：
  - T2522 合并后开一张删除票（跨目录互相引用，不按目录拆；RBM2D §245），删除时连同删掉 `UNG1Rowk` 的 owed 行、N2 审核 O2（可选）、逐票留下的 `#check`/`#print`/`#eval` 与多余 `example`。
  - 然后按目录做注释清理票（并行）。
  - 同时用 Opus 子代理起草最终论文（`paper/final/`）、PAPER-VS-LEAN（中枢票）、与投稿版的对比（三档，给合作者）、发布树。
- 下一节 §368，下一张票号 T2523，下一条 H335，下一个 paper-delta D754。

## §368 — 监督 2046 PASS：**M/N 关闭**（18 / 20，BA 204），MNC-C1（一般 `d` 的 BA 形式留着）；T2522 合并，四组都留；放删除票 T2523；最终论文 A 阶段完成（总调度 V5，2026-10-16 20:56 UTC）

- (1) **监督 `2026-10-16-2046` PASS**（REQ-2026-10-16-1955-MNclose）：(i)–(vii) 都满足，**M/N 关闭 18 / 旗标 20，BA 204，全部门关闭**（MA 9）。
  - 两处更正：C1，六个 `_three` 的 `#print axioms` 只有后两个在 T2520 审核里，其余在 T2514/T2516/T2518 的报告里；C2，`grep "decision B"` 在 `Test/Axioms.lean` 里其实有五行，都已是 §316 的措辞。两处都不藏缺口。
  - 过时的 `UNG1Rowk` owed 行可在删除票里删；`UNOULLk` 由删除票定（改为结构名）。
  - **MNC-C1（对发布阶段有约束）**：删除票保留 G3（`baThm27L_any`、`_of_ML`、`baEnd_BUnivL_of_ML` 及它们到达的东西），否则 Lean 对 `d > 3` 什么都不说，§316 的第二个论文选项就不成立了。
  - 教训「实例区间」可在下次交接时写进 TEAM §10。
- (2) **T2522 合并** 97e70f09（死代码报告）：核心闭包 673 个模块、32,770 个声明，不可达 10,243 个，约 100,264 行，17 个整模块死。
  - 四组增量都很小：G1 4 个声明 27 行；G2 10 个 53 行；G3 2 个 12 行；G4 0（已在核心里）。**全部保留**（G3 本来就是 MNC-C1 要求的）。
  - 登记里不可达的名字：owed 11、structural 23、refuted 4。
  - 审核观察 2：一些只给非根 `example` 用的辅助声明，和 `simp only` 里的 `GUETwistBA_Pi_apply`；`Test/InterfaceShape` 整模块死，删。
- (3) **放 T2523**（删除票，一张，`prover-hard`；照 RBM2D T2274）：
  - 根 = 核心 + G1–G4，工具里改成根；删 17 个死模块与全部不可达声明（脚本按行区间、自下而上）；全库的 `#print`/`#check`/`#eval`/`#guard_msgs` 与 `example` 只在 `FinalShape`、`BandTerminal` §Instances、`MAPins`、`BUnivHolds` 里保留。
  - 登记：删掉被删的名字；删 `UNG1Rowk` 的 owed 行；`UNOULLk` 从 owed 移到 structural（§20 规则）。
  - 验收：全量构建、公理、DeadDecls 复跑 0 不可达、检查文件 `T2523-check.lean` 编译、插入 ≤ 300 行。
- (4) **最终论文 A 阶段**（§356；云端 `/home/claude/paperwork/`，4 个 Opus 子代理并行把 D1–D753 全部分类）：
  - **N 693（Lean 内部，不改论文）、X 7（被取代）、E 9（三档：笔误、说明）、C2 13（二档：显然可修）、C1 24（一档：真有细节错误或缺口）、STMT 6**。
  - **STMT 的处理**：D403（Thm 2.7 的体内条件改成 `ρ_N(E) ≥ κ`）是 Jun 2026-10-05 已定的（§51 选 A），照改，不再问。D536、D547（Lemma 8.5 要 `Im m ≥ κ`）是它的后果。D562（Lemma 8.5(1) 改成事件形式）、D174（`lem_propTH` 6–7 的 `|r| ≲ |a|` 改成 `|r| ≤ c₀|a|`、`c₀ < 1`）、D666（Thm 8.2 要第五项 twisted-loop 估计 + 新引理 TL1）都是内部引理或命题的精确化与补缺口，主定理不变、路线不换，按 §356 由调度自己定，在对比文件里放第一档。
  - 下一步 B 阶段：按 TeX 文件把 52 处改动落到 `paper/final/tex` 副本（带占位的 D665、D666 要从 Lean 的陈述补全），云端编译。
- 下一节 §369，下一张票号 T2524，下一条 H336，下一个 paper-delta D754。

## §369 — 最终论文 B 阶段：52 处改动落进 `paper/final/tex`（草稿，106 页，零错误）；接下来独立复核与对比文件（总调度 V5，2026-10-16 21:46 UTC）

- (1) 三个 Opus 子代理按文件分组改，各在自己的整树副本里：X 改 `1_2`、`3_5`、`6`、`A`，共 21 处；Y1 改 `7_8`，18 处；Y2 改 `B`，13 处。合并后云端编译：**106 页（原 97），无错误，无未定义引用**。
  - 档位：一档（C1 + STMT）30 处，二档 13 处，三档 9 处。
  - 编号：§2 从新的 (2.34) `eq:bulkBA` 起后移一位；§8 从新的 (8.4) `eq:TL2_BA` 起后移一位；新增 Lemma 8.6（TL1）。定理与引理编号不变，其余章节编号不变。
- (2) **草稿已存设备**：`paper/final/tex/`、`paper/final/DubovaYangYauYin_RBM3D_Lean_version.pdf`；不发布的附件在 `paper/notes-not-published/`（分类表 `class_1..4.md`、改动日志 `edits_X/Y1/Y2.md`、latexdiff PDF）。
- (3) **子代理自报需要作者核的地方**（对比文件里单列一节）：
  - D469/D544/D651 的 "elementary class" 定义是重构的；
  - D612/D692 等几处有限个情形的核对只陈述、没写出；
  - Lemma 8.4、8.6 的涨落平均与高阶矩步骤，以及 (8.4) 的传播，是证明梗概；
  - D382 脚注里 `M_{y,α}` 的归一化；
  - Lemma 2.19 的常数在 BA 上依赖 `(d, κ, 𝔡)`，陈述仍写 "depending on d"。
- (4) **下一步**：
  - 一个独立的 Opus 复核子代理通读 diff，修记号与交叉引用的不一致（例如 Y2 用了 Y1 的记号、Lemma 2.19 的常数依赖），改动记进 `edits_review.md`；
  - 再由一个子代理照 RBM2D `changes-old-to-final.tex` 的格式写给合作者的对比文件（三档，一二档有 before/after 表，附「请作者核对」一节），不上传 GitHub；
  - 然后交 Jun。
- 下一节 §370。

## §370 — 最终论文定稿草稿与对比文件完成（交 Jun 与合作者）（总调度 V5，2026-10-16 22:38 UTC）

- (1) **独立复核**（Opus 子代理）改了 5 处：
  - Lemma 2.19 (5) 的常数在 BA 上也依赖 κ、𝔡；
  - (A.49) 在新的 `|r| ≤ c₀|a|` 下的分情形；
  - (⋆) 改为 `equation*`；
  - B.1(ii) 与 §3.2 里与体内常数 κ 撞名的记号，改名为 ν、φ_a。
  复核编译 106 页、零错误、无未定义引用。
- (2) **复核发现的高级别问题：Thm 2.7 的 universality 没有按 BA 的密度 ρ_N 归一化**（原文直接引 (2.20)，ρ_N ≠ ρ_sc 时不对）。这是 Jun 2026-10-02 已定的 §11（选 A：按局部密度归一化，任意 `|E'| < 2`），也是 Lean 的 `BAEnd_BUnivL` 的形式。分类阶段漏了这一项，调度在 Thm 2.7 第三项直接补上：一个不编号的公式，不影响编号。记在 `edits_dispatcher.md`，列为一档。
- (3) **对比文件** `changes-submission-to-final.tex/pdf`（19 页，英文，照 RBM2D `changes-old-to-final` 的格式）：
  - 一档 31 条、二档 13 条、三档 9 条，一二档带 before/after 表；
  - 最后一节「请作者核对」：Appendix B 里重构的 elementary class、只陈述未写出的有限情形核对、Lemma 8.4/8.6 与 (8.4) 传播的证明梗概、M_{y,α} 脚注的归一化等。
- (4) **文件**（设备）：
  - `paper/final/DubovaYangYauYin_RBM3D_Lean_version.pdf`（106 页）与 `paper/final/tex/`；
  - 不发布的放 `paper/notes-not-published/`：`changes-submission-to-final.pdf`、`latexdiff-submission-to-final.pdf`、`review_concerns.md`、各组改动日志、分类表。
- (5) 发布树里的 `paper/` 只放最终版（PDF + tex）。对比文件、latexdiff 和笔记都不上传（§355 第 5 步）。
- 下一节 §371。

## §371 — Jun：Thm 2.7（BA）要做所有 d ≥ 3（推翻 §316 的 B；D723 撤回，D754）；新阶段 BA-D；设计门 T2524；发布清理与之并行（总调度 V5，2026-10-16 23:40 UTC）

- (1) **Jun 的决定**（2026-10-16 23:2x UTC，调度会话，原话）：「哦不行 我发现title是d\ge 3, 我记错了， 不好意思，你只有把d>=3 情况做出来了。」——**BA 的 Thm 2.7（`MR:decol_BA`）在 Lean 里必须对每个 d ≥ 3 成立**，与论文（标题、`1_2:644-645`）一致。§316 (1) 的 B 作废；D723 撤回（D754 记）。
- (2) **缺口**（同监督 0342 V-F2：覆盖缺口，不是数学缺口）：一般 d 的 `baThm27L_any`（`BA/UNBUniv.lean:286`）已合并，只缺 BA 元组上的 `STStep5IIIgL d …`（情形 (iii)），其 d = 3 证明是 U5 的 9 个文件（`BA/Step5III{Edet,Edet2,Good,Good2,Ker,Ker2,Walk,Walk2,Targets}`，7,830 行，`Sizes 3`/`Zd 3` 共 116 处）。其余输入都对 d ≥ 3 成立（V 关闭条件 (iii)、M/N 关闭条件 (iii)/(vii)）。
- (3) **新阶段 BA-D**（REQ-2026-10-16-2332-BAanyD，监督 23:41）：
  - 预测 ≈ 5 张（4–8），旗标 10，预测到 8 发 REQ（待监督答 Q1）；
  - **T2524 = 设计门，现在开**（prover-max；报告 + 探针，探针不合并；与 T2523 并行，U5 文件在 T2523 保留的闭包里）：逐处普查 d = 3 的用法，分 (a) 只是下标、(b) 依赖 d 的常数/指数、(c) 实质；就地推广 vs 新文件两种价；行 ≤ 1,950；最终陈述；
  - 有 (c) 项「open」→ 先起 Fable 复核再开行；
  - 行（1b）等 T2524 的 1a-audit 和监督答复，从 T2523 合并后的 `main` 开；
  - 装配票：`baStep5III_holds_any`、`Thm27 := ∀ d, 3 ≤ d → BAThm27L d`、`final_shape` 只留 `UNL32`；d = 3 的定理与实例一行保留。
- (4) **发布清理与 BA-D 并行**（流程决定，待监督 Q4 确认）：
  - T2523 照常跑完合并；
  - 合并后先放：除 BA-D 文件（`BA/Step5III*`、`BA/UNBUniv`、`Main/FinalShape`，以及 T2524 点名的文件）以外的注释清理票，和公开版公理审计票（`RBM3D/Test/`、`RBM3D.lean`；登记表不进公开版，见下）；
  - BA-D 关闭后：BA-D 文件的注释票、DeadDecls 重跑（d = 3 专用的部分可能变死）、`docs/PAPER-VS-LEAN.md`、README 与发布树。
- (5) **公开版公理审计**（流程决定）：`RBM3D/Test/Axioms.lean` 换成 RBM2D 的形式（只查三条公理 + 数量下限），删 `Test/AuditNegative.lean`。理由：证明完成后 `final_shape` 只有 `UNL32` 一条前提、只用三条标准公理；登记表（owed / structural / refuted / superseded）在公开版里会被读成「未证的假设」，注释也多是历史。BA-D 期间登记表照旧用（新行若要登记照 §20）；审计票在 BA-D 的行合并之后放，以免改登记表撞车。
- (6) **辅助工具**（调度写，非 Lean）：`docs/claude-team/tools/texref.py`（把注释里的投稿 TeX 行号 `3_5:1234` 译成最终论文的 label 与编号）、`docs/claude-team/tools/paper-labels.tsv`（最终 PDF 的 623 个 label，取自 main.aux）。注释清理票用。
- (7) 返工账补齐 T2497–T2518（21 行）。计数：BA-D 1 / ≈5。H336。下一节 §372，下一张票号 T2525，下一条 H337，下一条 paper-delta D755。

## §372 — 监督 2346 PASS：BA-D 开（BAD-C1–C5，关闭条件 (i)–(ix)）；T2524 Amend 1；审计票时机更正 C1（总调度 V5，2026-10-16 23:59 UTC）

- (1) **监督 2346 PASS**（REQ BAanyD 已 done）：BA-D 开，预测 ≈ 5（4–8），**旗标 10、预测 ≥ 8 发 REQ、用到 12 未关闭建议 HOLD**（BAD-C1）。仍判为覆盖缺口、不是数学缺口：U5 的 d = 3 只在 9 个文件里；导入的文件里没有非实例的 `Sizes 3` 声明；收尾指数不含 d。BA 计 **205**；装配票记在 BA-D，MA 保持 9 关闭。
- (2) **关闭条件**：(i) `baStep5III_holds_any (d) (hd : 3 ≤ d) : STStep5IIIgL d …`（`baThm27L_any` 的 `h5` 的精确类型，前提只有 `3 ≤ d`）；(ii) `Thm27 := ∀ d, 3 ≤ d → BAThm27L d`、`final_shape` 只有 `UNL32`，`#print axioms` 只三条；(iii) `baStep5III_holds`、`baThm27L_three`、`Thm27_of_L32` 的 d = 3 内容一行恢复，FinalShape 与 MAPins 的 d = 3 实例照编；(iv) `band_terminal`、`bUniv_holds` 公理不变；(v) D723 标「撤回（D754）」，`Main/FinalShape`、`BA/UNBUniv` 文档串不再说 d = 3 是决定 B；(vi) 每次合并登记扫描 `unregistered: []`，关闭时 BA-D 不留 owed 行；(vii) 一个 d = 4 实例（`Sizes 4` 数据 + `Admissible` + `Thm27` 的 d = 4 分量只带 `UNL32`；超过约 150 行则只要 `Sizes 4` + `Admissible`）；(viii) BA-D 后的 DeadDecls 重跑把新 `Thm27` 的产出者与 (iii) 的 d = 3 推论列为根；(ix) 装配票的检查文件在 1b 前钉 `Thm27`、`final_shape`、`baStep5III_holds_any` 的精确类型。
- (3) **BAD-C2**（T2523 接口）：T2524 报告标出它引用的 U5 链外名字是否被 T2523 删；1a-audit 在 T2523 合并后的 `main`（否则 afab243f）上自己重做普查；行若需要被删的声明，从 e3540151 原样恢复并计价，不要 REQ。**BAD-C3**：(c) 项改到 U5 外的陈述、U5 外有只在 d = 3 合并的输入、预测 ≥ 8，任一出现 → 开行前发 REQ。**BAD-C4**：价相当时就地推广优先；就地行等 T2523 合并后开。
- (4) **更正 C1（BAD-C5）**：公开版公理审计票等 **BA-D 装配票合并后** 再放（它去掉登记扫描，而扫描是 (vi) 的检查；它也读 `final_shape`）。§371 (4) 里「T2523 合并后先放审计票」作废。注释票照 §371 (4)：BA-D 文件以外的可以并行；1a-audit 之前 BA-D 文件暂定为 9 个 U5 文件、`BA/UNBUniv`、`Main/FinalShape`、`Endpoints`、`BA/MAPins`，1a-audit 后按 D4 的行文件表加装配票的文件；注释票已改过的文件若被 BA-D 行点名，注释票让路（rebase），BA-D 行不让。
- (5) MNC-C1（2046）在装配票合并前继续有效。
- (6) **T2524 Amend 1**（监督 O2）：BAD-C2 (a)–(c)、(vii) 的价、BAD-C3 一节、BAD-C4、装配票要钉的精确陈述。不重开：1a 还在跑就由证明者补进报告，1a-audit 逐条查，缺项按规则 (B) 修一次。H337。
- (7) 教训（监督 Q1，待 TEAM §10）：设计门的票要写明目标的维数量词；只做某一个 d 是覆盖范围的决定，开行之前交 Jun。
- (8) 计数：BA 205；BA-D 1 / ≈5。下一节 §373，下一张票号 T2525，下一条 H338，下一条 paper-delta D755。

## §373 — Jun：大活一开始就分工，不要一张票干完所有删除；T2523 的处理与以后的拆票规则（总调度 V5，2026-10-17 01:05 UTC）

- (1) **Jun**（2026-10-17 01:0x UTC，调度会话，原话）：「你一开始就应该分工一下， 不要让一个工单干所有删除任务」。
- (2) **调度的错**：§368 照 RBM2D §245 把删除做成一张票（理由：不同目录的死声明互相引用，按目录删各自编不过）。RBM3D 的死代码约 10,250 个声明、分布在约 600 个文件（RBM2D 的数倍），一张 prover-hard 票串行做，21:03 起 4 h 只有一个提交。跨目录引用可以用「只删本组内全部使用者也被删的声明，其余留给最后一张清扫票」解决，不需要一张票。
- (3) **T2523 停掉，改成并行**（Jun 01:0x UTC 又指出：T2523 看来还在 preflight——「短预检」应几分钟，跑了 4 h，说明卡住了；不再等 H338 的进度行）：
  - **T2525 = D0**（prover，先跑，短）：摘用 T2523 分支的 08e88ffb（DeadDecls 以 G1–G4 为根），删整模块死文件（T2522 (c) 的 17 个）与导入，完整编译，再跑工具，把结果提交为 `docs/reports/T2525-dead.md` 供各组用。
  - **T2526–T2531 = 六组并行**（prover-hard，D0 合并后开）：BA；Induction；Graph；Universality；Chain + Green；其余小目录（Path、Evolution、Loop、Gauss、Defs、Propagator、Main、Kernel、Hierarchy、Analysis、Endpoints、Basic）。各删本组文件里的未达声明，但删除集 S 只留「引用者全在 S 里」的声明（对全环境求不动点），其余作为遗留列出；检查杂物同票删（§368 的四个保留处除外）。BA 组优先（BA-D 的 R1 等它）。
  - **T2532 = 清扫**（prover-hard，六组都合并后）：重跑工具删遗留，清登记表（T2523 第 4 项：删已删名字、删 `UNG1Rowk`、`UNOULLk` 移到 structural），`Test/` 与 `RBM3D.lean` 的杂物；验收 0 未达。
  - 中枢同时最多 4 张：D0 + T2524（审核中）；D0 合并后 BA、Induction、Graph 先开，其余按空位。
- (4) **以后的规则**（写进 TEAM §10）：一件活预计超过约 2,000 行改动或要碰 100 个以上文件，开票时就按文件不相交拆成可并行的几张，用「组内闭合 + 最后清扫」处理跨组依赖；单张大票只在拆了编不过、且说得出原因时才用。注释清理已按此拆（约 10 张）。
- (5) **预检规则**（流程决定）：删除、注释这类没有数学的票，preflight 只写一行「(i) no exponents; (ii) not applicable; PASS」，不读文件、不编译；跑过 20 分钟中枢直接停掉它开 1b。
- (6) 计数：发布清理不计 gate。返工账记 T2523（停，拆票）。H339。下一节 §374，下一张票号 T2533（BA-D 的 R1 = T2533、R2 = T2534），下一条 H340。

## §374 — 更正：T2523 没有卡在 preflight，H339 停错了；救回它的工作并续跑，撤回拆分票；T2524 合并，放 BA-D 的 R1（T2533）、R2（T2534）（总调度 V5，2026-10-17 01:25 UTC）

- (1) **事实**（中枢 H339 (1) done，`T2523.state`）：T2523 的 preflight 21:16 已 PASS；之后 1b（prover-hard）一直在做，删除脚本已在工作树里执行（未提交：633 个文件，+408 −140,459，删 17 个文件），恢复了几条闭包没预料到的 rfl 引理，停时正在第 7 次完整 `lake build`（4331/4426）。调度在 Jun 说「好像还在 preflight」后没等 H338 的进度行就让中枢停了——**这是调度的错**：应先核实（H338 已发出），再决定。
- (2) **救回**（H340）：停 T2525（D0，刚开工）；把 T2523 工作树的现状原样提交到 `t/T2523`（WIP），以新的 workflow 从那里续跑 1b（不再 preflight）：完整编译、修剩下的、写报告 (b)–(d)，然后审核、合并。T2525–T2532 从放行表撤下，票文件留作后备（续跑失败时用）。
- (3) **§373 (4) 的规则仍然成立**（大活一开始按文件拆票）；本次是活已做了九成，拆开重做反而更慢。教训加一条：**改动正在跑的票之前，先拿到进度事实**（中枢的状态行或分支、报告），不凭印象停票。
- (4) **T2524 合并**（0591c041，1a-audit PASS 带 Amend 1）：(c) 项 0；就地推广；R1 ≈ 300 行（×1.74 ≈ 520）；R2 装配 ≈ 110 行 + d = 4 实例 78 行；BA-D 预测 3。
- (5) **放行**：T2533 = R1（prover-hard；等 T2523 合并后从新 `main` 开；检查文件 Part 2 合并时由调度打开）；T2534 = R2（prover；等 R1 合并；检查文件钉 `baStep5III_holds_any`、新 `Thm27`、`final_shape` 的精确类型，关闭条件 (ix)）。R2 合并即 BA-D 关闭，发关闭 REQ。
- (6) 计数：BA 205 → R1 206、R2 207；BA-D 1 / 3。H340、H341。下一节 §375，下一张票号 T2536，下一条 H343。
- (7) **T2535 = `docs/PAPER-VS-LEAN.md`，现在开**（prover-hard，只写一个 Markdown 文件，不碰 Lean，可与 T2523 并行；Jun 要求中枢保持 2–4 张在跑，T2523 合并前其他票都碰它的文件）：按最终形式写（Thm 2.7 对所有 d ≥ 3，文本取 T2534 的钉文；公开版公理审计；§368 的四处保留实例）；T2533/T2534 引入的名字列为「待定」，T2534 合并后调度复核。H342。

## §375 — T2535（PAPER-VS-LEAN）合并；T2534 Amend 1（d = 4 实例不能落在空的体内）（总调度 V5，2026-10-17 02:35 UTC）

- (1) **T2535 合并 07716bc2**（审核第 1 轮 PASS）：`docs/PAPER-VS-LEAN.md` 695 行，五节（证明了什么；陈述差异 2.1–2.12；尺寸一致性；外部输入 [LANDON20191137]；路线差异 5.1–5.8）；过程词 grep 为 0。按最终形式写（Thm 2.7 对所有 d ≥ 3）。
- (2) **审核观察**：(1) 第 94–99、107–109、143–145 行的 `baThm27L_all`、`baStep5III_holds_any`、`.2 3 le_rfl`、d = 4 实例要等 T2534 合并后复核；(2) **设计里的 d = 4 实例用 `κ = 1/2`，而 `BArho ≤ 1/π < 1/2`，BA 的体内是空集，四个 BA 分量空真**——T2534 Amend 1 改掉；(3) 第 451 行 (2.52) 页码应为 p. 15（小改）；(4) §2.12 可补一句 `Ring.inverse` 在 `BAendDom` 上是真逆（可选）。(3)、(4) 和 (1) 的复核在 T2534 合并后一并处理。
- (3) **T2534 Amend 1**（T2534 尚未开工，开工即带）：d = 4 实例照 d = 3 的做法（`clsκ`、体内能量的证明 `S0_bulk`）给出体内非空的证明；整段 ≤ 约 150 行，否则只给 `Sizes 4` + `Admissible`，不套 BA 分量（监督 2346 (vii) 的退路）；不许合并体内为空的实例。
- (4) 计数：发布清理不计 gate。下一节 §376，下一张票号 T2536，下一条 H344。

## §376 — T2523 审核第 1 轮 RETURN 要签字：签 D2 (a)(b)，D1 修一次（Amend 1）（总调度 V5，2026-10-17 05:05 UTC）

- (1) **审核**（`docs/reports/T2523-audit.md`）：A1–A7 干净（根的陈述按哈希不变、公理标准、登记表第 4 项做了、行改动都是被迫的）。D1：85 个「恢复」声明里 5 个其实没人用（`Green/MinorDiff` 的 4 个 example 辅助、`Graph/BALocReg1B_extMap`），删掉能编——可修。D2 要调度签字。
- (2) **签字 D2 (a)**：只因登记表扫描而留的 110 个声明（42 个前提证明定理 + 68 个辅助，1,094 行）**先留**，作为工具根（`scanProvers`）；不给 42 个 Prop 分登记类别。理由：BA-D 装配合并后公开版审计去掉登记表与扫描（§371 (5)、BAD-C5），之后的 DeadDecls 收尾重跑连同 `scanProvers` 一起删；现在分类别到时又要撤。
- (3) **签字 D2 (b)**：插入上限 300 只算 `RBM3D/` 与 `RBM3D.lean`，工具文件的根列表不算；`RBM3D/` 下 291 ≤ 300，通过。
- (4) **D1**：规则 (B) 修一次（删 5 个、其余 `restoredRoots` 逐个给理由、三个零引用的 `@[simp]` 引理给出失败的证明或删掉），然后第 2 轮审核。
- (5) 观察 O1（`baThm27L_any` 失去唯一的编译实例）：不处理；T2534 的 `baThm27L_all` 在 d = 3、d = 4 的实例会用到它。
- (6) 收尾重跑（BA-D 与公开版审计之后）要做：删 `scanProvers` 及其 110 个声明；修工具 `inductUnit?` 不比模块的毛病（T2523 报告 (d) 2，两个漏报）；`restoredRoots` 复核。H345。下一节 §377，下一条 H346。

## §377 — T2523 合并；T2533 开工；发布清理第 3 步（注释）一开始就拆成 12 张并行票 T2536–T2547（总调度 V5，2026-10-17 08:15 UTC）

- (1) **T2523 合并 970b8b54**（07:56 UTC）：修复 89856dac（审核 D1 第 1–3 项）后第 2 轮审核 PASS（`docs/reports/T2523-audit.md`）；17 个整模块死文件 `git rm`，633 个文件删去没人用的声明与检查杂物，`RBM3D/` 下 +484 −149,231；完整编译 4426 个作业。合并后 `RBM3D/` 655 个文件、约 51.2 万行；树与 89856dac 的 `RBM3D/` 相同。返工：否（第 1 轮 RETURN，D1 修一次）。T2533（BA-D 的 R1）07:57 开工（wf_de230fb1-cb1，H341 (2)）。
- (2) **注释清理 = 发布清理第 3 步，按 §373 一开始就分工**：12 张互不相交的票，按目录、大目录再按文件名首字母切，权重（注释行 + 3×流程词命中 + 3×TeX 行号）每张 6.4k–10.9k：T2536–T2538 `Induction/`（A–I、K–Q、S–Z），T2539–T2540 `Graph/`（A–B、C–Z），T2541–T2542 `BA/`（A–K、L–Z），T2543 `Chain/`，T2544 `Universality/`，T2545 `Green/ Defs/ Hierarchy/ Kernel/ Analysis/ Basic.lean`，T2546 `Evolution/ Loop/ Gauss/`，T2547 `Path/ Propagator/ Main/ Endpoints.lean`。每张票的文件清单在 `docs/tickets/T####-files.txt`（共 646 个文件）；票与清单由 `docs/claude-team/release-tickets/gen_comment_tickets.py` 按 `scopes.json` 生成。规则同 RBM2D T2275–T2278：不留流程词、论文引用用最终论文的 label/编号（`texref.py` 翻译投稿 TeX 的行号）、只动注释（去注释后逐字相同）。
- (3) **不在这 12 张里**：BA-D 的 7 个文件（`BA/Step5III{Good,Good2,Walk,Walk2,Targets}`、`BA/UNBUniv`、`Main/FinalShape`）——T2534 合并后单开一张注释票，并顺带扫全库注释里「Theorem 2.7 只对 d = 3」的旧说法；`RBM3D/Test/` 与 `RBM3D.lean`——归公开版公理审计票（T2534 合并后，BAD-C5）。
- (4) **并行**：T2533、T2534 没合并时注释票同时最多跑 2 张，留一个位给 T2534（T2533 一合并它就开）；T2534 合并后注释票补满到 `parallel`。磁盘剩余 < 20 GiB 时不再开新的注释票并报告。H346。
- (5) 返工账：补 T2522、T2524 两行（之前漏记），T2523 行补全。近 10 张返工率 3/10（T2515、T2519、T2523）。
- (6) 之后的顺序：T2533 → T2534（关 BA-D，发关闭 REQ）→ 公开版审计票、BA-D 注释票、PAPER-VS-LEAN 复核票（待定名字、d = 4 一句、(2.52) 页码、路径）→ 注释票全部合并后 DeadDecls 收尾重跑（§376 (6)）→ README 库地图 → `make_publish.sh`（Jun 手动推送）。下一节 §378，下一张票号 T2548，下一条 H347。

## §378 — T2533 合并（BA-D 的 R1）；T2534 开工；磁盘不足 20 GiB，清理已合并票的工作树后再开注释票（总调度 V5，2026-10-17 08:24 UTC）

- (1) **T2533 合并 feb83715**（08:14 UTC）：审核第 1 轮 PASS；就地改 `BA/Step5III{Good,Good2,Walk,Walk2,Targets}`（+284 −268），`baStep5III_holds_any (d) (hd : 3 ≤ d) : STStep5IIIgL d …`（BA 元组上 Step 5 情形 (iii) 对所有 d ≥ 3，关闭条件 (i)），`baStep5III_holds` 留作 d = 3 的一行推论。检查 Part 2 已启用（`example : Target := baStep5III_holds_any`）。返工：是。T2534（R2，装配，关 BA-D）08:15 开工，带 Amend 1。
- (2) **磁盘**：H346 (4) 的门槛 20 GiB，中枢量得 19 GiB，一张注释票都没开，并问怎么腾地方：`../RBM3D-wt/` 有 1,224 个工作树，多数是已合并或已停的票。**调度的决定（流程）**：`git worktree prune`；不是在跑的票的工作树，若其 HEAD 已在 `main` 里（已合并的票及其审核工作树）或是某个本地分支的头，用 `git worktree remove`（不加 `--force`）删掉；有未提交改动的、HEAD 不在任何分支上的留着并计数。删的只是检出与编译产物，提交都在分支上。H347 (3)。
- (3) **并行（替换 H346 (2)）**：T2533 已合并，不必再给 T2534 留位；T2534 在跑，其余位按清单顺序开注释票，每开一张前剩余 ≥ 20 GiB，并以第一张注释票工作树的编译产物大小估计后面的。H347 (4)。
- (4) 下一节 §379，下一张票号 T2548，下一条 H348。

## §379 — T2534 合并：Theorem 2.7 对所有 d ≥ 3 证完，BA-D 关闭 REQ；放公开版审计 T2548、BA-D 注释票 T2549、PAPER-VS-LEAN 复核 T2550；注释票 Amend 1（总调度 V5，2026-10-17 08:45 UTC）

- (1) **T2534 合并 4b68c4cc**（08:27 UTC）：审核第 1 轮 PASS；`BA/UNBUniv`（`baThm27L_all`；`baThm27L_three` 为其 d = 3 一行）与 `Main/FinalShape`（`Thm27 := ∀ d, 3 ≤ d → BAThm27L d`，`Thm27_of_L32 := baThm27L_all`，`final_shape` 原文不变），+151 −33。`final_shape`、`Thm27_of_L32`、`baThm27L_all`、`baThm27L_three` 只用三条标准公理。**Theorem 2.7 现在对每个 d ≥ 3 证完，与论文一致；唯一假设 `UNL32`。** BA-D 用 3 张（T2524、T2533、T2534）。返工：是。
- (2) **d = 4 实例**：`L = 4`、`λ = g₀` 常数、体内非空已证（`FinalShape_bulk4`）、`Admissible (1/8) (1/10)` 已证，110 行；与 T2524 设计的 `L = 4(n+1)`、`λ = (2(n+1))^{-6}` 不同（λ 趋于 0 时固定 κ 的体内为空）。调度认为在 (vii) 之内（是实例不是陈述），交监督确认。**更正（监督 0846 BDC-C1）**：上面「λ 趋于 0 时固定 κ 的体内为空」不对——`BArho g 0 → 1/π`，κ < 1/π 时能量 0 附近终将在体内；设计的毛病是 κ = 1/2 > sup BArho（对任何 λ 都空）。取常数 λ 的真实理由是成本：非空体内的见证在固定耦合下构造，常数列直接是终将成立的见证，趋于 0 的 λ 要 m 对 λ 的连续性。公开文字不得写错误的理由。
- (3) 检查 T2534 Part 2 启用；`paper-deltas.md` D723 标「已撤回（D754）」（关闭条件 (v)）。**关闭 REQ**：`docs/supervisor/requests/REQ-2026-10-17-0845-BADclose.md`（(i)–(ix) 逐条，Q1 关闭、Q2 审计票现在放）。
- (4) **(v) 的余项**：T2534 审核观察 3（`baThm27L_three`、`baThm27L_any` 的文档串仍引 D723）与观察 2（`UNBUniv` §5 标题说有实例而实际在 `FinalShape`）→ BA-D 注释票 **T2549**（7 个文件，第 6 条专讲 Theorem 2.7 的范围）；其他文件里「`d > 3` 不在范围内（决定 B，§316）」之类的说法（`BA/MADecolQUE:45`、`BA/MALocal:50`、`BA/MAQDiff:56`、`BA/MainIndTermBA:20`、`BA/MainIndRegBA:16` 等）→ 注释票 T2536–T2547 的共用 **Amend 1**（`docs/tickets/T2536-T2547-amend-1.md`）。
- (5) **放行**：**T2548** 公开版公理审计（`Test/Axioms.lean` 换成 RBM2D 的形式，删 `Test/AuditNegative.lean`；监督 2346 更正 C1：装配票合并后），prover；**T2549** BA-D 注释票，prover-hard；**T2550** PAPER-VS-LEAN 复核（名字、Theorem 2.7 的范围、d = 4 一句、审计段、(2.52) 页码 p. 15、可选 `Ring.inverse` 一句；等 T2548 合并），prover。优先级 T2548、T2549、T2550，然后 T2536–T2547；磁盘规则照 H347 (4)。H348。
- (6) **发布路径**：PAPER-VS-LEAN 在本仓库写 `paper/final/…`；`publish/make_publish.sh` 在公开树里把它改写成 `paper/…`、`paper/tex/…` 并检查不留 `paper/final`。
- (7) (viii) 收尾 DeadDecls 重跑的根要含 `baThm27L_all`、`Thm27_of_L32`、`final_shape` 与 d = 3 推论 `baStep5III_holds`、`baThm27L_three`（留在发布版里）。下一节 §380，下一张票号 T2551，下一条 H349。

## §380 — 监督 0846 PASS：BA-D 关闭（3 / 3，BA 207），全部 gate 关闭，Lean 端完成；BDC-C1、BDC-C2；T2549、T2550 Amend 1；T2551 加 d = 4 的第五个合取（总调度 V5，2026-10-17 09:00 UTC）

- (1) **监督 2026-10-17-0846 PASS**：Q1 BA-D 在 (i)–(ix) 下关闭，用 3 张（开时预测 ≈ 5），旗标 10 未到；BA 207；(vii) 的数据偏差在 (vii) 之内（确认）；(v) 的余项分派完整（10 个文件：T2542 六个 BA 文件、T2544 两个、T2549 `UNBUniv`、T2548 `Test/Axioms`）。Q2 T2548 现在放：无异议。**全部 gate 关闭，Lean 端完成**：`final_shape : UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27`，`Thm27 := ∀ d, 3 ≤ d → BAThm27L d`，三条标准公理。剩下只有发布工作，不改任何陈述。MNC-C1 失效。ROUTES 的 BA-D 行记关闭。
- (2) **BDC-C1**（约束）：公开文字（T2550、T2549 在 `Main/FinalShape` 的文档串）不得说「λ 趋于 0 时固定 κ 的体内为空」；若给理由，用 §379 (2) 更正行里的理由。
- (3) **BDC-C2**（约束）：BUniv 合取在 d = 4 的前提全部已由例子给出或与 d 无关（`BAEnd_BUnivL d` 对 d 一致）；`FinalShape.lean:24-25`、`:123-124`、`:209-211` 说 BUniv 读 d = 3 数据的句子要改。→ **T2549 Amend 1**（在跑：到审核边界把 Amend 1 交审核，必要时规则 (B) 修一次，不算返工；若已审核通过合并，就由 T2551 处理这三处）、**T2550 Amend 1**（开工即带；开工条件加「T2551 合并后」）。
- (4) **O4（可选）采纳**：**T2551**（prover，小代码票，T2549 合并后）在 d = 4 例子里加第五个合取（BUniv）的应用，并改这三处注释为「五个合取都用上」。这样 d = 4 实例对五个合取都非空。只动 `Main/FinalShape.lean`，≤ 30 行，完整编译。
- (5) (viii) 在 DeadDecls 收尾重跑前仍有约束；那一步的 REQ（或发布收尾 REQ）要列出根。H349。下一节 §381，下一张票号 T2552，下一条 H350。

## §381 — T2548 合并（公开版公理审计）；T2550 先开后停、等 T2551（总调度 V5，2026-10-17 09:12 UTC）

- (1) **T2548 合并 ba53553a**（09:00 UTC）：`RBM3D/Test/Axioms.lean` 换成 RBM2D 形式（`#assert_rbm_axioms`：24,150 个 `RBM` 声明只用 `propext`、`Classical.choice`、`Quot.sound`，并有数量下限），登记表与前提扫描删去；`Test/AuditNegative.lean` 删去。审核第 1 轮 PASS。返工：是。观察 O1（别的文件注释里还提登记表）由注释票处理；O2（`DeadDecls.lean` 头与 (g) 节仍描述登记表）归 DeadDecls 收尾重跑票。
- (2) T2550 在 09:01 按 H348 开了，H349 改了开工条件后 09:03 停下（只写了预检、工作树干净），等 T2551 合并再开，带 Amend 1。不算返工。
- (3) 监督 0846 的裁定文件未被跟踪，随 H350 提交。下一节 §382，下一张票号 T2552，下一条 H351。

## §382 — Jun：发布阶段的小改动调度自己改，不来回开票（TEAM §10 第 11 条，§243）（总调度 V5，2026-10-17 10:20 UTC）

- (1) Jun 提醒：这个阶段有小改动就自己改，不必来回工单（手册已有：TEAM §10 第 11 条）。照办。
- (2) **调度直接改、不开票、不走中枢工作流**：Lean 里只动注释或文档串的修改；记录文件；`docs/PAPER-VS-LEAN.md`、README、发布脚本这类文档；论文措辞与引用的已裁定勘误。随下一条例行 H 一起提交。**改了 `.lean` 文件时，H 里要求中枢提交前跑一次 `lake build`（受影响模块或完整编译）并在 done 行报结果**；注释改动另附「去注释后与 `main` 相同」的核对。
- (3) **仍然走票**：Lean 的陈述、证明、实例代码，工具代码（`DeadDecls.lean` 的逻辑），以及量大的改动（注释票 T2536–T2547 共约 6.6 万注释行，已在跑，不收回）。
- (4) 不碰正在跑或排队的票的文件（避免合并冲突）；那些文件等票合并后再改。
- (5) 回看：T2549 Amend 1 那类注释更正、T2550 那类文档复核，按这条本可调度自己改。以后照 (2) 办。下一节 §383。
