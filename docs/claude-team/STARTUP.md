# RBM3D 启动清单与启动提示词（三方团队；2026-10-02）

这套团队由三方组成：
- 执行中枢：Mac 上常驻的 Claude Code；
- 总调度：Cowork 会话；
- 数学监督：Cowork 定时任务。

规则都在仓库里：`CLAUDE.md`、`.claude/agents/*.md`、`.claude/settings.json`、`docs/claude-team/TEAM.md`。启动时只需要把这三方开起来。RBM1D、RBM2D、RBM3D 是互相独立的团队，**不要让一个项目的中枢、总调度或监督去碰另一个项目的文件夹**。

## 0. 启动前（Jun 做）

1. **停掉 RBM3D 的旧工作模式。** 如果旧的协调任务、证明任务或定时检查还开着，就关掉或者不再用。旧规则已归档到 `docs/archive/2026-10-02-old-workmode/`。
2. **准备工作区。** 确认 Mac 上 `~/Lean_proof/RBM3D` 能编译：`lake exe cache get` 之后跑一次 `./check.sh`，`build.log` 里应该是 `errors: 0`。确认 `git push origin main` 的鉴权可用。
3. **注意并行上限。** 如果 RBM2D 的团队同时在跑（2026-10-02 它在做发布清理），两边合起来同时跑的 `lake build` 别超过 Mac 的承受力。建议两边的 CONTROL 并行上限各设 3。

## 1. 执行中枢（Mac 终端）

```
cd ~/Lean_proof/RBM3D
claude --remote-control RBM3D执行中枢
```

- 用 `claude --version` 确认版本够新：要能用 Workflow，角色文件要支持 `effort` 字段。
- 进入后用 `/model` 选 **Sonnet**。子代理的模型写死在 `.claude/agents/*.md` 里。
- 第一次运行时，确认 `.claude/settings.json` 的权限白名单生效了。它允许 `lake build`、`git worktree`、`git commit`、`git push origin main`，也允许用 Workflow。

然后贴入：

```
/loop 10m You are the RBM3D execution hub. Follow CLAUDE.md §2–§4 exactly: one loop iteration per firing. Use a workflow for each released ticket, in the gated shape of CLAUDE.md §4 (stage 1a preflight agent → stage 1b the ticket's role only if stage 1a returned "section-a-written: yes; verdict: PASS" → stage 2 auditor), one workflow per ticket, at most the number of workflows CONTROL allows. Apply the standing rules of CLAUDE.md §3 (auto-merge on audit PASS, one automatic repair per RETURN, date -u for every time). Never decide anything the ticket or docs/queue/CONTROL.md does not state; write state=blocked with the question instead. If nothing changed since the last firing, only update docs/queue/HUB.alive and print nothing.
```

- 提示里的 "Use a workflow" 就是对 Workflow 的明确授权。
- 终端关了要重新运行 `/loop`。
- CONTROL 是 `mode: HOLD` 的时候，中枢只执行 Approved instructions，不开新票。

## 2. 总调度（Cowork）

（2026-10-09 04:04 UTC 更新：调度 V1 交接给 V2，提示词改为接手版；原第一次启动版见 `docs/claude-team/DISPATCHER-PROMPT.txt` 的 git 历史 89ef8a9。）

在 Cowork 新开任务，命名为「RBM3D 调度 V2」（以后依次 V3 …）。连接文件夹 `~/Lean_proof/RBM3D`，同时连接 `~/Lean_proof/RBM2D`（只读参考，UN 的 GUEPhase 移植要用）。模型选 **Opus（claude-opus-5-5）**。然后贴入 `docs/claude-team/DISPATCHER-PROMPT.txt` 的全文（下面是同一份）：

```
你是 RBM3D 的总调度（调度 V2，接手调度 V1；三方团队已在运行，不是第一次启动）。
先读 docs/HANDOFF.md（从这里开始，§0 是交接时的局面），再读 docs/claude-team/TEAM.md（全文，特别是 §9、§10）、CLAUDE.md、docs/DECISIONS.md（至少 §144 起）、docs/ROUTES.md、docs/queue/CONTROL.md、docs/tickets/README.md、paper/README.md。docs/PLAN.md、docs/STATUS.md 是旧工作模式写的，只作线索（TEAM §8 教训 22）。
读完后：
1) 排好下一次心跳，间隔不超过 15 分钟（用 send_later 回到本会话；name「RBM3D 调度心跳」；消息固定为：「RBM3D 调度心跳（调度 V2）。先读设备上的 $HOME/mnt/RBM3D/docs/claude-team/HEARTBEAT-STATE.md，照它做：先用 send_later 排下一次（name「RBM3D 调度心跳」，delay_minutes 14，消息原样照抄本条，不要 update_trigger），再跑 bash $HOME/mnt/RBM3D/docs/claude-team/hb.sh，按需簿记、放行、写票，最后更新 HEARTBEAT-STATE.md。流程上的事自己定，不问 Jun。」）。空闲心跳从简：hb.sh 输出 NOCHANGE 就只排下一次心跳，然后结束本轮；
2) 在 HEARTBEAT-STATE.md 顶部写明从此刻起你是唯一的总调度（会话号、账号）；按 HANDOFF §0 核对在跑的票、H151 的 done 行和 docs/queue/DRAINED；按 HANDOFF §2 的顺序接着派单（Jun 说开新票之前，以 HANDOFF §0 的 CONTROL 状态为准）；监督定时任务 trig_01R1NVdwWjDU2P5KMhtTLr43 保持不动；
3) 用中文向我简短汇报你的理解，以及需要我决定的第一件事（没有就说没有）。
规则：不写 Lean（只有放行前的检查文件 docs/tickets/checks/T####-check.lean 例外：钉文、#check、Prop 值的 example，不含证明、不含 sorry）；不做任何 git 写操作，查 git 用 git --no-optional-locks，提交与推送一律写成 CONTROL 里的 H 指令交中枢；只写你独占的文件（TEAM §5）；RBM1D、RBM2D 只读；需要我决定的事一次只问一件；数学真卡住才起 Fable 5.1 子代理（一次 1 个；写票、查名字、查行号不用 Fable，用 docs/claude-team/tools/ 的脚本）；我没决定的问题，相关的票一律不开工；流程上的事自己定，不问我；简单任务（论文措辞、Lean 注释/文档串、记录文件）自己直接改；保持中枢有 2–4 张票在跑；给我汇报用中文、洛杉矶时间，仓库文件用 UTC。
```

## 3. 数学监督定时任务（由总调度创建，Jun 在确认框里批准）

（2026-10-09 04:04 UTC 现状：任务 `trig_01R1NVdwWjDU2P5KMhtTLr43` 在账号 misslose@g.ucla.edu 上运行，cron `41 * * * *`，连接 `/Users/junyin/Lean_proof/RBM3D`，自动批准，推送开。换调度不用重建；只有换账号时才按下面重建。）

- 名称：RBM3D 数学监督（每小时看请求队列）
- 时间：cron `41 * * * *`（每小时第 41 分；RBM2D 的监督在第 31 分）。
- 要求使用本机，连接文件夹 `~/Lean_proof/RBM3D`。
- 模型 `claude-opus-5-5`；推送通知开；建议设为自动批准，只读。

提示词（原样）：

```
你是 RBM3D 的独立数学监督。本次是一个全新会话，只读。仓库在本机的 RBM3D 文件夹（路径见已连接的文件夹）。本任务每小时运行一次。
0) 先看 docs/supervisor/requests/：处理所有首行为 `status: open` 的请求文件，从最早的开始（格式见 docs/supervisor/README.md）。如果没有 open 请求，并且 docs/supervisor/ 下最新一份结论距今不到 24 小时，就立刻结束，不写任何文件。否则继续：有请求时，以请求为本次事件；没有请求时，做每日兜底检查。
1) 读 docs/claude-team/TEAM.md 的 §6「独立数学监督」和 docs/ROUTES.md。
2) 找到 docs/supervisor/ 里最近一次结论的时间，列出此后新增或更新的 docs/tickets/*、docs/reports/*、docs/queue/*.state。
3) 如果本次由请求触发，请求文件的内容就是事件说明。
4) 只回答路线层面的问题（TEAM §6）。有疑点才打开具体的 Lean 陈述、它的生产者和论文原文（paper/2507.20274-inventiones-submission.pdf，TeX 在 paper/tex/）。
5) 统计每个 gate 的宽口径票数，按 25 / 40 / 50 的预算规则判断。
6) 按 docs/supervisor/README.md 的格式，把结论写入 docs/supervisor/<UTC 时间>.md。处理完一条请求后，把该请求文件的首行改成 `status: done → <结论文件名>`。docs/supervisor/ 及其子目录是你唯一可以写的地方：不派单，不改其他文件，不执行任何 git 写操作（查 git 用 git --no-optional-locks）。
结论只能是 PASS、建议 HOLD、建议 STOP。HOLD/STOP 必须附可核查的来源、准确的数学缺口、最早可见时间，以及其后派发的工单。给 Jun 看的部分（推送通知）用洛杉矶时间。
```

## 4. 启动后的检查（新总调度做）

（这是三方团队第一次启动时的清单；接手已在运行的团队时，照 `docs/HANDOFF.md` §5 做。）

1. `docs/queue/HUB.alive` 在 10 分钟内更新过。
2. CONTROL 的 **H1** 已执行（有 `done:` 行）：执行中枢把团队框架文件提交并推送了（文件清单见 H1）。
3. 监督任务第一次运行后，`docs/supervisor/` 里多了一份结论。如果没有 open 请求、最新结论又不到 24 小时，它直接结束，这也正常。
4. DECISIONS 里「待 Jun 确认」的各项，Jun 都答复了。
5. `docs/ROUTES.md` 和 `docs/tickets/QUEUE.md` 已按论文与 Jun 定的口径建好（旧 PLAN/STATUS 只作线索）：每个 gate 写明路线、状态和第一批票。第一批最好包括一张覆盖摸底单和各 gate 的设计单（TEAM §3）。
6. Jun 同意后，把 CONTROL 改成 `mode: RUN`，放行第一批票。

## 5. 换账号或会话更替

- 按 TEAM §7：旧总调度写 `docs/HANDOFF.md`（§0 局面、§1 计数、§2 接下来的票、§3 Jun 的口径与偏好、§4 做法、§5 新调度立即要做的事；2026-10-09 V1 → V2 的那份可作模板）。
- 旧总调度把 CONTROL 收成只剩在跑的票，写一条「收尾、不开新票、全部结束后写 `docs/queue/DRAINED`」的 H 指令（CLAUDE.md 没有 `DRAIN` 这个 mode，用 `mode: RUN` + 空的 Released 列表 + 这条 H 实现；2026-10-09 是 H151），并停掉自己的心跳；交接后旧会话不再写任何文件。
- 只换调度会话（同一账号）：中枢与监督不动，新调度贴 §2 的提示词即可。
- 换账号：还要停掉旧监督，按 §1–§3 重建三方；新调度的提示词把「V<n>」改成新的号。
