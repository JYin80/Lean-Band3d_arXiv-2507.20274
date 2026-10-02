# RBM3D 交接包（给调度 V1；2026-10-02 16:48 UTC 由 RBM2D 的总调度 V2 按 Jun 的要求写）

Jun 的原话（2026-10-02）：「在 RBM3D 文件夹里把这些流程安排的方法写在他们的相关文件里，然后再写一个 prompt 给总调度。我会马上开始那里来做 lean proof for RBM3D 的 project。」

## 1. 项目
- 论文：Dubova, F. Yang, H.-T. Yau, J. Yin, *Delocalization of non-mean-field random matrices in dimensions d ≥ 3*，arXiv:2507.20274（Inventiones 投稿版，97 页）：`paper/2507.20274-inventiones-submission.pdf`，TeX 在 `paper/tex/`，节与文件对照见 `paper/README.md`。
- 仓库：`~/Lean_proof/RBM3D`，GitHub `JYin80/Lean-Band3d_arXiv-2507.20274`。Lean 4.34.0 / Mathlib v4.34.0（与 RBM1D、RBM2D 相同）。
- 现状（旧工作模式留下，**未核实**，TEAM §8 教训 22）：约 40 个 Lean 文件（`RBM3D/Defs`、`Propagator`、`Graph`、`Gauss`、`Loop`、`Kernel`、`Analysis`、`Test`），最近一次 `build.log`（2026-09-20）全量构建通过；`RBM3D/Test/Axioms.lean` 的 `#assert_rbm_axioms` 带一个「接口公理」白名单（`interfaceAxioms`），与新规则（只许三条标准公理，CLAUDE.md §5.3）冲突，见 DECISIONS §2 第 3 项。最后一条旧提交：「Author's call: the stochastic layer is on hold; keep what already compiles」。
- 旧计划（`docs/PLAN.md`）只做「确定性内核」（§2.5 传播子层、附录 A、附录 B），随机层（§3–§8）不形式化，`lem_propTH` 性质 5–8 当接口。RBM2D 已证明随机层可以照 RBM1D 的路线做完（单时刻高斯律、Gaussian IBP、生成元恒等式、矩界、连续归纳），所以范围要请 Jun 重新定（DECISIONS §2 第 1 项）。

## 2. 团队
- 三方：执行中枢（Mac 上的 Claude Code，Sonnet，`/loop 10m`）、总调度（Cowork，Opus）、数学监督（Cowork 定时任务，每小时 :41）。启动见 `docs/claude-team/STARTUP.md`；章程 `docs/claude-team/TEAM.md`（§9 是 RBM2D 后期新定的常规）；执行侧规则 `CLAUDE.md`；角色 `.claude/agents/`。
- 可参考的成品：`../RBM2D`（只读）——同一套流程跑完的完整项目。值得照抄的：票面模板与检查文件写法（`docs/tickets/`、`docs/tickets/checks/`）、CONTROL 的 H 指令格式（`docs/queue/CONTROL.md`）、簿记脚本范例（本仓库 `docs/claude-team/tools/example_*.py`）、`RBM2D/Main/` 与 `RBM2D/Endpoints.lean` 的终点写法、随机层的 Lean 代码（大量可移植到 d 维）。

## 3. 新总调度立即要做的事
1. 排心跳（STARTUP §2 的提示词里有固定消息）。新建 `docs/claude-team/HEARTBEAT-STATE.md`（不进版本库），写当前状态与每轮做法。
2. 确认中枢在线、H1 已执行（框架入库；见 CONTROL）。
3. 按 STARTUP §3 建监督定时任务（Jun 批准）。
4. 按 DECISIONS §2 的顺序向 Jun 确认口径，一次一件。口径定之前不派证明票；可以先写一张覆盖摸底单的票面草稿（TEAM §3），等 Jun 同意再放行。
5. 口径定后：建 `docs/ROUTES.md` 的 gate 表与第一批票（摸底单、各 gate 的设计单），CONTROL 改 `mode: RUN`。
