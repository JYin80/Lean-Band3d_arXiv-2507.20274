# RBM3D 交接包（调度 V3 → 调度 V4；2026-10-13 12:00 UTC，由调度 V3 会话 session_01Qidfbgzdy6FV6jy1eSbZgb 写）

Jun 的原话（2026-10-13 08:4x UTC）：「这批工单结束就不要发工单，整理完这批就好，我要换 hub 账号。休息到 LA 9am」；（12:0x UTC）：「赶紧整理team startup 的调度prompt 这里额度马上要到了」。

新调度先读本文件，再读 `docs/claude-team/TEAM.md`（全文，§9、§10 是常规）、`CLAUDE.md`、`docs/DECISIONS.md` 的 **§255–§305**（V3 的全部决定；更早的按需查）、`docs/ROUTES.md`（BA 一格是计数总账）、`docs/queue/CONTROL.md`（H254–H284）、`docs/supervisor/` 最新几份（0658、0849 最重要）。启动提示词见 `docs/claude-team/STARTUP.md` §2（= `docs/claude-team/DISPATCHER-PROMPT.txt`）。

## 0. 交接时的局面（2026-10-13 12:00 UTC）

- **Jun 的指令仍有效：不放新票。** 这批只剩 **T2496 U4s3b**（`t/T2496b`）。**Jun 在 11:59 UTC 暂停了它的 1b 重跑（没有提交，停在 462b5e09），中枢循环已停。** 循环重启后照 state 文件恢复：按 Amend 1 + Amend 2 重跑 1b（prover-hard，skipPreflight）→ auditor。U4s3a 已合并 e89f5609（第一次原地转换，原地新增 1,411 行，带状读者全部照常编译）。U4s3b 合并后这批结束；CONTROL H280 (3) 让中枢写一条「batch complete」的 done 行后待命。
- **Jun 要换中枢账号**，并说休息到洛杉矶 9:00（16:00 UTC）。新调度在 Jun 说开新票之前只做簿记（U4s3b 合并、监督回复落账），不写票、不放票。
- **监督 Lclose 已回复（0947 PASS，§306）：** 阶段 L 在 48 / 50 关闭，`baStep2_closed` 闭合，T 的最后条件消掉。剩三件簿记：LC-1 过时文档注释（进下一张碰 `LWPinsBA`/`Step2CloseBA`/`BAGGExp` 的票）、LC-2 paper-deltas 补账（调度做，见 §5）、O4 V 接口（写 V 票时照 §306 (5)）。LC-3 的 ROUTES 已改。
- **已写好但未放行的票（草稿，在 `docs/claude-team/drafts/`，不在 `docs/tickets/`）：** T2497 = U1s2（混合布局：`IterationsB`、`QGridB` 原地，`IterationsA`、`QGridA` 新文件；约 2,050；一行，预签拆）、T2498 = U3s3（8 原地 + 2 新文件；约 4,830；三行预签，窄设计门 D1–D4；**要等 T2497 的 QGrid 一半合并**——U3s3 读 U1s2 的定义 `aTrueQN` 等，不能当前提）。两份都已按 UP-C2 双定价、带族前提表。放行前：给答复（DECISIONS 新节）、盖日期、挪进 `docs/tickets/`、写 CONTROL 行与 H 指令编译检查文件。
- **登记**（`RBM3D/Test/Axioms.lean`）：`BAStep5IIIEMatrix` 已删；`STDecayStronggL` 已加（owedProps，负责人 BA 主归纳 V）；`BALWterm`/`BALWtermExp` 已删（L5 证出）。

## 1. 计数（宽口径；监督 0658、0849 的口径）

- **BA 182**（§144 不设上限）。BA 全局预测 ≈ 219（212–227），UP-C2 下 ≈ 214。
- **T：关闭于 27 / 34.5**（监督 0849）。
- **U：26 / 42**（含 T2496 两行中的一行算法见 §300 (4)；U3s2 三行、U5d 两行、U2-BA 两行都已计入）。计划 ≈ 48（44–51），UP-C2 下 ≈ 44–45；**旗标 42 保留**：某次放行使预测 ≥ 49 → 放行前发短 REQ；U 已用 50 而未关闭 → 建议 HOLD（UP-C1）。
- **L：48 / 50，关闭**（监督 0947，旗标撤销）。
- **V：0 / 12**（预测 ≈ 13，UP-C2 下 ≈ 11；开场 REQ 用这个数，0658 O6）。**M/N：3 / 15**（其余行在 V 关闭时发短 REQ 开）。
- P、K、TL、E、G 已关闭。

## 2. 接下来的票（Jun 说开新票之后；按依赖）

1. **U1s2 = T2497**（草稿已有）；之后 **U3s3 = T2498**（等 T2497 的 QGrid 一半合并）；**U3s4**（`QtNonzero*`、`QtXiRoundLift`；6 个文件都在 2,000 行以下，UP-C2 原地价约 1,520，一行；读 U3s3 的 `STOeqQtRoundPTgL''`，T2498 建议把 `STOeqQtgL'` 的证明归 U3s4）。
2. **U5e**（U5 最后一行，BA 的目标；U5a–d 都已合并；读 `BAStep5IIIWalk` + `BAStep5IIIFromWalk`）。
3. **U-BA 各行**：U1-BA（等 U1s2；含 `stNewPQgL_wardCls` 的 BA 读法；读 U2-BA 的 `WardCls`）、U3-BA (a)/(b)（等 U3s2–s4；(b) 是 `hQ` 在 `baStep2Mat` 上的 BA 负责人，0849 TC-2；读 `baGridDrift_envelope`）、U4-BA（等 U4s3；欠项：A9 的 `lem:newKLK` 在 ℓ = L 的载体类的 BA 消法、D2 的 BA 消法）、U6-BA。BA 行按 T2379 价 ×2 估（0658 UP-F1）。
4. **V 阶段**：开场 REQ（≈ 13 行）；V1s1（`ExpHier` 的层级前提在 `∀ᶠ n` 下逐指标写，0658 UP-C4）、V1s2、V1s3（都按 UP-C2 双定价）、V1-BA、V2a/b、V3。
5. 每张泛型转换票都要：**UP-C2 双定价**（原地 = T2379 模型 ×1.2，只算 2,000 行以下文件；新文件 = 普查 ×1.24 校准；取便宜的，除非 1a 指出障碍）、**族前提表**（0349 U5S-C3：守卫与否、BA 消法；需要 `BAReal`/`0 < g₀`/`0 < Im m` 的前提放在流之下；`∃ C` 不依赖冻结的 `(sz, z)`；漂移/层级逐指标 `∀ᶠ n`）、**名字级表格放 1b 开头**（0149 `:98`）。UP-C2 (d)：T2496 是第一次 B 密集原地转换，整票落地超过 3,540 行（加减挪动）就回到新文件。

## 3. Jun 的口径与偏好

- 汇报用中文、洛杉矶时间；仓库文件用 UTC。数学术语用英文。
- 需要 Jun 决定的事一次只问一件；流程上的事自己定，不问 Jun；Jun 没决定的问题，相关票一律不开工。
- 论文 Jun 自己改（Lean 做完以后）；3D_Band 是母本，`RBM3D/paper/tex` 是参考副本，**不要改论文**。
- 不写 Lean（检查文件例外）；不做 git 写操作；RBM1D、RBM2D 只读。

## 4. 写票与簿记的做法（V3 的定式）

- 起草用后台子代理（general-purpose，`run_in_background`），一次 1–2 张；简报写清来源、绑定规则（R1、TN-C4、UBA-C1/C3、C1、U5S-C3、UP-C2）、文件、计数、模板，要求检查文件只用已合并模块、禁词（`by`/`rfl`/`Iff.rfl`/`theorem`/`lemma`/`sorry`/`inductive`，注释里也不许）、并核对导入闭包（T2490 曾因少导入编译失败）。
- 定稿：在 `**Dispatcher notes (DECISIONS §N):**` 下插「Dispatcher answers」一条、`sed` 盖日期、复制到 `/mnt/user-data/outputs/rbm3d/`、`device_commit_files` 写进 `docs/tickets/` 与 `checks/`。
- 簿记脚本 `$HOME/v3_NNN.py`（设备上；例子见 v3_298.py、v3_302.py）：DECISIONS 新节、CONTROL（删已合并行、加放行行、Pre-release checks、H 指令放在 `## Merge log` 前）、ROUTES（BA 格前缀、各阶段行）、账本、WORKLOG、HEARTBEAT-STATE。**f-string 里的 `{…}`**（`N^{-D}`、`𝒦^{(2)}`）要双写，否则会被求值。
- 中枢在 1b 开头停下问前提（名字级核对）时：看它的提案、核带状与 BA 消法都能编译、不违 U5S-C3，就写 Amend（就地补钉文或新起一个 amend 文件）并 H 指令重跑；审核里的登记缺口用「合并时由中枢加一行」的批准指令（T2482 / H271 (3) 先例）。
- 心跳：send_later，name「RBM3D 调度心跳」，14 分钟；先 list_triggers 去重。迟到的心跳只确认、不另排。

## 5. 新调度立即要做的事

1. 读 §0 列的文件；在 HEARTBEAT-STATE.md 顶部写明从此刻起你是唯一的总调度（会话号、账号）。
2. 排好心跳（STARTUP §2 的消息，把「调度 V4」写进去）；空闲心跳从简。
3. 查 T2496b 的状态：合并了就记账（DECISIONS 新节、账本行、ROUTES U 行写 U4s3 的落地行数与 UP-C2 (d) 结论），看 CONTROL 是否已有「batch complete」done 行；没合并就等。
4. Lclose 已落账（§306）。做 LC-2：`docs/paper-deltas.md` 补一节阶段 L（以及 15:10 UTC 之后合并的 T、U 行），按论文位置去重，`T2494a`+`T2494c` 记一条（§306 (3)）；Jun 换完账号后，确认中枢 `docs/queue/HUB.alive` 在更新、监督任务在新账号下存在（STARTUP §3）。
5. **Jun 说开新票之前不放票。** Jun 说开后，按 §2 的顺序，先放 T2497（草稿只需补答复与日期）。
6. 用中文向 Jun 简短汇报理解与需要他决定的第一件事。

---

## 附：上一份交接包（调度 V1 → V2，2026-10-09），原文保留

# RBM3D 交接包（调度 V1 → 调度 V2；2026-10-09 04:04 UTC，由调度 V1 会话 session_01RThagGKa4jNgUEWeKViyyg 写）

Jun 的原话（2026-10-09 04:00 UTC 前后）：「准备交班给下一个调度，修改一下 doc/team startup 的文件，不要发新工单了，收尾现在在跑的就行。」

新调度先读本文件，再读 `docs/claude-team/TEAM.md`（全文，§9、§10 是常规）、`CLAUDE.md`、`docs/DECISIONS.md` 的 §144–§165、`docs/ROUTES.md`、`docs/queue/CONTROL.md`。启动提示词见 `docs/claude-team/STARTUP.md` §2（= `docs/claude-team/DISPATCHER-PROMPT.txt`）。

## 0. 交接时的局面（2026-10-09 04:04 UTC）

- **CONTROL**：`mode: RUN`，但 Released 只剩 4 张在跑的票；H151 说「收尾、不开新票」，四张都结束（合并，或 RETURN/blocked 等调度处理）后中枢写 `docs/queue/DRAINED`。旧 CONTROL（约 190KB）已原样归档进 `docs/queue/CONTROL-archive.md`（标题「Archived … dispatcher V1 handoff」），新 CONTROL 只留在跑的票、常设规则、H151 与合并记录尾部。
- **四张在跑的票**（都在中枢 Workflow 里，合并按 CLAUDE.md §3 规则 (A) 自动进行，不需要调度）：

| 票 | 内容 | 状态 | 结束后调度要做的 |
|---|---|---|---|
| **T2356** | UN-47 `GUEPhase/Eq729B`（(7.29) 与 (7.47)，`d ≥ 3` 陈述设计已过监督 0344） | 1b 证明中（`prover-max`，停止线 2400，`docs/tickets/T2356-1b.md` 的 E1–E5） | 合并后可写 UN-51（见 §2）；RETURN（切分或链上数学 FAIL）→ 按 0243 O4 判断是钉文修补还是 REQ |
| **T2358** | LW-13b R1 = 来源引擎 `Graph/LWProv.lean`（`locStepXProv_holds`、`lw_localregularXP`、加权桥） | Amend 1 后 1a PASS，1b 中（停止线 1950） | 合并后写 **R3**（见 §2）；越停止线 = 预设切分 C1（P-a / P-b），不需新决定；切分以外 → REQ |
| **T2360** | BA-DK：阶段 K 设计（只出报告，探针 ≤ 400 行；条件 K1–K6，监督 0243） | 设计中 | 报告合并后**把它写成阶段 K 开启 REQ** 发监督（首行 `status: open`；附 K1 分类表、行表、行数与 1.5 倍旗标）；PASS 前不写 BA 证明票 |
| **T2361** | UN-50b `GUEPhase/PathBounds.lean`（`GUEPathBounds` 由 `t₁` 的输入给出） | 1a 预审中（`prover-hard`） | 1a 在「`MLConcl` ↦ `UNMLOut` 的 ST 结论」一点 FAIL → 写 REQ；PASS 则自行跑完合并 |

- **最近合并**：T2359 = LW-13b R2（eb56169，`ekTTkInf_holds`、`lwMomExp_nearInf`、`lwXiExpClaim_holds`、`lwMomExpNoExp_holds`、`lwTail32`）、T2357 = BA-P8（83847ef，`baProp5to8_holds`）、T2355 = UN-52a（5d7a660，`g2bRowk`）、T2354 = UN-49+50a（5d8f515，`HypB`、`LLTransfer`）、T2353（OneLoop）、T2352（HypA）、T2351（DuhamelC）、T2350、T2349。
- **open 的 REQ**：无（最后一份 REQ-2026-10-09-0254 已由监督 0344 答复 PASS）。
- **监督**：定时任务 `trig_01R1NVdwWjDU2P5KMhtTLr43`（cron `41 * * * *`，账号 misslose@g.ucla.edu，连接 `/Users/junyin/Lean_proof/RBM3D`，自动批准，推送开）。保持不动。
- **调度 V1 的心跳**：已停（交接后旧会话不再写文件，TEAM §7）。

## 1. 计数（宽口径；监督 0344 的预算表）

| gate | 已用 | 计划 / 上限 | 说明 |
|---|---|---|---|
| ST-1…ST-5 | 40+39+47+35+17(+1) | 已闭合 | |
| ST-6 | 3 | 4 | R4（`stMainInd_holds`、`unMLOut_holds`，删 `STMainInd`、`UNMLOut` 两行）等 LW-01，可并入 LW-01 收尾票（§150 (4)） |
| **LW** | 50 | 计划 52，**上限 55（硬，监督 0143 O2）** | 剩 R3、LW-01。第 56 张、C1–C3 以外的切分、R1–R3 的数学性 1a FAIL → REQ，监督会建议 HOLD 并上报 Jun。钉文修补不算（0243 O4） |
| **UN** | 58 | 计划 64，Jun 的上限 65（§124） | 剩 UN-51（`RandomLayerA/B`）、UN-52b（`Main/BUniv`、`BUnivHolds`） |
| **BA** | 35 | 不设上限（Jun §144），**每个阶段开关都要监督 REQ PASS** | 阶段 P 已关（6/9）；阶段 K 设计中（T2360）；之后 G/E、L、T/U/V、M/N |
| MA | 7 | 8 | MA-06 等 ST-6 R4、UN-52、BA 终端 |

下一张票号 **T2362**；下一节 DECISIONS **§166**；下一条 H 指令 **H152**；论文差异下一号 **D632**。

## 2. 接下来的票（按依赖；写法见 §4）

1. **LW R3**（T2358 合并后；LW 51）：`Graph/AuxGraphRooted.lean`（有根 `GtoAG`：`auxGraph_exists_forest` 去掉 `choose`、以根为前提；主和带指示函数；`LWAuxNestedOwnOn`）+ `Graph/LWMomentExp.lean`（探针 `T2348Pins.lean` 的 `LWMomentExpOn`、`domFar/NearA/NearB`、`dom_union/disj`、`LWf_split`、`norm_add3_pow_le`、远/近钉文、组装 `lwMomentExp_of_parts`、`lwMomentExp_holds : ∀ d, LWMomentExp d`）+ `Test/Axioms.lean` 删欠账 `LWMomentExp`（`:160` 附近，按名字 grep）。条件：**C5**（1a 先编出有根森林；只有具体障碍才退到路线 (E)，换 (E) 要 REQ）、**C6**（组装取 **(α)**：`∀ p, ∃ K`，远尾半径保持论文尺度）、0243 L1（只经引擎递归调用步引理）。(A) 已按 `LWf` 写（`LWMomExpNoExpF`），R3 用 `LWfD … univ = LWf` 转换（§162 (2)）。设计尺寸 1183 / 1567 / 2337，停止线 2100，预设切分 C3 = G | F。
2. **LW-01**（R3 合并后；LW 52）：范围按监督 1942 C8（`stMainInd_of_LW` 已做 Step 2 收口，**不要重证**）：`LWReduceB`、`LWReduceT`、`LWterm`、`LWtermB`、`LWtermExpS`、并集 `LWtermExp`，顺序 LWterm → LWtermExpN（已合并 T2342）→ LWtermExp；前提 ↔ 生产者表；可并入 ST-6 R4。
3. **UN-51**（T2356、T2361 都合并后）：`RandomLayerA`、`RandomLayerB`（RBM2D 521 + 152 行）：`g1Row`/`UNG1Row` 与 `UNOULLk`（`oull_of_pathBounds`，T2354）、`UNOUEq747`（`Eq729B_eq747_of_inputs` + `bridge` + `goodFlow`，T2356）；**先定监督 0344 E5**：`UNG1Rowk` 的 BA 实例 (a) 在 BA 侧（BA-C5 `BA/GUEHyp`）闭合，或 (b) `UNG1Rowk` 加种类的 `Eq747k` 生产者作前提；选 (a) 则把 `Test/Axioms.lean:188` 的归属注释改为「带状：UN-51；BA：BA-C5」。这是路线级问题，写票前发 REQ 或在 UN-51 的 1a 里定、交监督。
4. **UN-52b**：`Main/BUniv`（`ouRowk_of_pins`、`bUniv_of_g1Row`）、`BUnivHolds`（`bUniv_holds`），删 UN 欠账行；终点接 `RBM3D/Endpoints.lean`（MA 冻结）。
5. **ST-6 R4**（LW-01 后，或并入 LW-01）。**MA-06**（最后）。
6. **BA**：阶段 K 开启 REQ PASS 后按其行表写；BA 种类的 `UNOUEq747k` 归 BA-C5（0344 Q2 (3)），`UNOUProfRowk` 归 BA-C3。

## 3. Jun 的口径与偏好（原话或近原话；违反过的都被 Jun 指出过）

- **规则（原样）**：不写 Lean（只有放行前的检查文件 `docs/tickets/checks/T####-check.lean` 例外：钉文、`#check`、Prop 值的 example，不含证明、不含 sorry）；不做任何 git 写操作，查 git 用 `git --no-optional-locks`，提交与推送一律写成 CONTROL 里的 H 指令交中枢；只写你独占的文件（TEAM §5）；RBM1D、RBM2D 只读；需要 Jun 决定的事一次只问一件；我没决定的问题，相关的票一律不开工；流程上的事自己定，不问 Jun；简单任务（论文措辞、Lean 注释/文档串、记录文件）自己直接改；给 Jun 汇报用洛杉矶时间，仓库文件用 UTC。
- **用中文汇报**（Jun 指出过「写什么韩文」）；简短，先结论。
- **中枢不能空**：「hub 都没工单了你不干活么」「再开几个单，现在只有一个在跑」「hub 已经空了」——保持 2–4 张在跑或可放行；票快跑完时心跳要密（≤ 15–30 分钟），合并后同一轮补票。
- **Fable 不浪费**：「为什么有这么多 fable 使用量」「这滥用的 4 个 fable subagent 极大浪费这轮可用的额度」——Fable 5.1 只在数学真卡住时用，一次一个；**写票、找名字、查行号一律自己做（或用 `docs/claude-team/tools/` 的脚本），不用 Fable**。V1 后期全程没用 Fable。
- **BA**：「BA 肯定是要证明的，多少张我都批，只是每一个阶段都要有明确监督验证，只要不浪费走错路，都可以批，它本来就是非常复杂。」→ 张数不设上限，每个阶段开/关都要监督 REQ PASS（§144）。
- **优先级**：「另一方面尽量同时让其他方向先闭合。」→ ST/LW/UN/MA 先闭合，BA 只放过了阶段门的票（§145）。

## 4. 写票与簿记的做法（V1 后期的定式；细节见 TEAM §10）

- 每轮先 `date -u`，时间戳绝不写在未来；票头 `Ticket: T#### (dispatcher V2, <date -u>; DECISIONS §…)`。
- **移植票**（UN 的 GUEPhase 系列）：模板见 `docs/tickets/T2352.md`、`T2354.md`；移植表（`d : Sizes ↦ sz : Sizes d`、`Z2 ↦ Zd d`、`spectralZ/M ↦ zt/mE`、`Gsig ↦ Gres`、`gloop … (blockMat M) ↦ loopL d L W (blockMat d L W M)`、`KLoop.Kcal ↦ STKloop`、`KLoop.mSig ↦ mSigma`、`LLf ↦ loopL … (zt E u)`）照抄；先跑 `python3 RBM3D/docs/claude-team/tools/portmap.py RBM2D/RBM2D/<file>.lean`（在 `$HOME/mnt` 下）列 MISS 名，写进预审 (ii)。**`d = 2` 的输入/结论形式（`scaleM`、`MLConcl`、`Meta`、`(Nη)^{-k}`）在 3 维常被已合并钉文取代**——这种票先做 1a 设计门（T2356 的做法），不是纯移植。
- **检查文件**：每个 `#check` 的名字先用 `bash docs/claude-team/tools/nsof.sh <names>` 核全名与文件，再确认**它所在的文件被检查文件 import 了**（T2361、T2345/T2346、T2349 都栽在这里）；对新词汇的票，钉文写成 `def T####_X : Prop := …`，验收用「检查导入 + 新模块 + `example : T####Check.T####_X := X`」。
- **H 指令**：一写进 CONTROL 就不改（TEAM 教训 29）；要补就写新 H。每条 H：Step A 提交（按名列文件，含未入库的监督文件）→ Step B 逐个编译检查文件 → Step C 放行。
- **REQ**：首行必须恰为 `status: open`（监督 0143 O4）；写清 Situation / Questions（Q1…）/ For information；路线级才发。
- **1a FAIL 的分流**（监督 0243 O4）：靠加一个所有调用者都已提供的前提、或收窄到已合并目标的定义域就能修的，是钉文修补（写 `T####-amend-N.md` + 改检查文件 + 新 H，从 1a 重开，记返工账本，不算票）；所需事实在目标定义域上为假或未证，才是路线问题 → REQ。
- **删 `private` 还是拷贝**：一般删关键词（§153，审核用脚本核对 diff 只删关键词）；但被删文件处在导入树底层（如 `Propagator/Prop6Hold.lean`）时整树重编会堵合并，改为拷贝（§161 (1)）。
- **CONTROL 超过约 20KB 就归档**（TEAM §5、§9.14）：本次交接已归档一次。

## 5. 新调度立即要做的事

1. 排心跳（STARTUP §2 的固定消息）；新建或覆盖 `docs/claude-team/HEARTBEAT-STATE.md`（不进版本库），在顶部写明「从 <时间> 起唯一的总调度是 <会话>」。
2. 跑 `bash docs/claude-team/hb.sh`，核对 §0 的四张票（`docs/queue/T2356/T2358/T2360/T2361.state`）与 H151 的 `done:` 行。
3. 向 Jun 简短汇报接手，然后按 §2 继续：T2360 报告到了就发阶段 K REQ；T2358 合并后写 R3；T2356、T2361 合并后处理 UN-51 的 E5 问题。CONTROL 的 `reason` 行改回正常运行时写清楚。
4. 账号或会话再换时：照 TEAM §7、STARTUP §5。

---

## 附：2026-10-02 的启动交接包（调度 V1 用，原文保留供查）

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

