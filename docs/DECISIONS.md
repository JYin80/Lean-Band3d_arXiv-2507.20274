# RBM3D 决定记录（总调度维护；先原话，后落实）

## §1 团队与工作方式（Jun，2026-10-02：「在 RBM3D 文件夹里把这些流程安排的方法写在他们的相关文件里，然后再写一个 prompt 给总调度」）

- 2026-10-02 16:48 UTC，RBM2D 的总调度 V2 把 RBM2D 的三方团队框架写进本仓库，覆盖旧工作模式：`CLAUDE.md`、`.claude/agents/*.md`、`.claude/settings.json`、`docs/claude-team/`（TEAM、STARTUP、hb.sh、tools、DISPATCHER-PROMPT.txt）、`docs/queue/CONTROL.md`、`docs/tickets/README.md`、`docs/reports/README.md`、`docs/supervisor/`、本文件、`docs/HANDOFF.md`、`docs/ROUTES.md`、`docs/rework-ledger.md`。旧的 `CLAUDE.md`、`docs/TASKS.md`、`docs/QUEUE.md` 移进 `docs/archive/2026-10-02-old-workmode/`。
- RBM2D 定下、在本仓库直接生效的常规见 TEAM §9（模型档位与自动升级、Fable 子代理、流程自动、并行 4、接口规则、检查文件名字核对、尺度统一、心跳、简单任务、外部输入版本、收尾发布、CONTROL 归档）。
- 旧工作模式留下的 `docs/PLAN.md`、`docs/STATUS.md`、`docs/paper-deltas.md`、`docs/stochastic-audit.md`、`docs/mathlib-api.md`、蓝图与 Lean 文档串里的说法，一律按未核实处理（CLAUDE.md §5.10）。

## §2 目标与口径（待 Jun 确认，按顺序一次问一件）

1. **范围与验收终点**：做整篇论文（含随机层 §3–§8，照 RBM2D 的路线）还是只做旧计划的确定性内核？做整篇的话，终点是论文 §2 的哪几条主定理（逐条列出，钉文写在 `RBM3D/Endpoints.lean`，冻结前由覆盖摸底单核对）。
2. **论文忠实度**：照 RBM2D §5 的口径（以论文为唯一来源；笔误、必要条件、等价表述可小改并记 paper-deltas；实质改动由 Jun 定）？
3. **被引结果的处理**：论文引用别处的结果（例如 `lem_propTH` 性质 5–8、附录 B 引的三条展开引理）——作为授权的外部输入（Lean 里写成显式假设，不用 `axiom`），还是内部证明？旧模式在 `Test/Axioms.lean` 里留了「接口公理」白名单，新规则只许三条标准公理，需要 Jun 定是否改写成假设。
4. **并行上限**：默认 4；RBM2D 的中枢同时在跑时是否先用 3。
5. **从 RBM2D 移植**：允许并鼓励（CLAUDE.md §5.2 已写）；是否有不想照搬的部分。
