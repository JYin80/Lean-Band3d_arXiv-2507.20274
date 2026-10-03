# RBM3D 返工账本（总调度维护；每合并一张补一行）

规则见 TEAM §1「返工率」。

| 票 | 合并时间（提交） | 角色 | 模型 | 返工 | 说明 |
|---|---|---|---|---|---|
| T2001 | 2026-10-02 19:05 UTC (a62eeef) | prover-max（修复 repairer） | Sonnet 5.5 effort max（修复 claude-opus-5-5） | 是（审核 RETURN 一次，仅报告） | BA 钉文在 supp μ_N 非区间的序列上空真，未记 paper-delta；修复补 T2001l |
| T2005 | 2026-10-02 21:58 UTC (709c5c7) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；第一张 Lean 合并（`msc_eq_integral`，全库 3254 jobs，510 定理 / 0 公理） |
| T2002 | 2026-10-02 23:11 UTC (06f2064) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；1b 因额度两次 API 失败重跑（规则 H，不计返工） |
| T2003 | 2026-10-02 23:22 UTC (7ba7ba5) | prover-max | Sonnet 5.5 effort max | 否 | 审核 PASS 但要求总调度签字（路线 H 交 Jun，DECISIONS §13）；1b 因额度重跑（不计） |
| T2004 | 2026-10-02 23:23 UTC (0b91f7a) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；1b 因额度重跑（规则 H，不计） |
| T2006 | 2026-10-03 00:38 UTC (0a873f1) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；词汇层（Sizes、FineModel、LinearForm）+ RBM2D 移植，全库 3326 jobs / 0 公理；paper-delta D17–D24 |
| T2009 | 2026-10-03 00:40 UTC (73cf5c1) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；路线 H 试点之一（一维热核：级数、母函数、倾斜反演、周期化），3686 jobs / 0 公理 |
| T2010 | 2026-10-03 00:41 UTC (315e65e) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；Laplace–Gauss 引理 L1–L3，3688 jobs / 0 公理；T2010a 是路线内部修正（DECISIONS §14），不进 paper-deltas |
| T2007 | 2026-10-03 00:46 UTC (b20c658) | prover-hard（Amend 1：repairer） | Sonnet 5.5 effort xhigh（repairer claude-opus-5-5） | 否（流程缺口） | 审核一次 PASS；合并被根文件 `#assert_rbm_axioms` 拦（未登记假设 Prop），DECISIONS §16 归类后 Amend 1 只改 Axioms.lean，第 2 轮审核 PASS；性质 5s 已证（`prop5Short_holds`） |
| T2008 | 2026-10-03 00:46 UTC (710acd2) | prover | Sonnet 5.5 effort high | 否（流程缺口） | 审核一次 PASS；同 T2007 被公理登记拦，`KLPT` 由 T2007 Amend 1 登记后从第 5 步续合并 |
| T2011 | 2026-10-03 01:56 UTC (13dbbc0) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；路线 H 试点后半（ℤ 上热核的衰减与一、二阶差分界），3695 jobs / 0 公理；试点 B1+B2 通过（DECISIONS §14） |
| T2012 | 2026-10-03 02:07 UTC (9e2b00f) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；尺度 N 的 ≺、逐时刻控制、矩/Stein 桥接；Axioms.lean 记 2 条 structural（§16 预授权）；832 定理 / 0 公理；paper-delta D25 |
| T2013 | 2026-10-03 02:17 UTC (868b3b4) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；流数据、G_t、细格点 G-loop、BA 包装、包络 (5.2)（RBM2D 无对应文件，按秩 W^d 新证）；880 定理 / 0 公理 |
| T2017 | 2026-10-03 03:12 UTC (33049c0) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；环面热核 τ ≤ L² 的界与 τ ≥ L² 的零模/谱隙，884 定理 / 0 公理；1b 因额度两次 API 失败重跑（规则 H，不计） |
| T2014 | 2026-10-03 03:20 UTC (fa2ebc7) | prover-max | Sonnet 5.5 effort max | 否（票面错） | 第一次 preflight-fail 是总调度票面两处错（实例 n = 3 不存在、gval 映射错）→ Amend 1 重开，不计 RETURN；审核一次 PASS（O1：22 个公开 KL 辅助，仅可见性）；948 定理 / 0 公理 |
| T2018 | 2026-10-03 03:28 UTC (ddf5f74) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；网格游走、转移律、独立增量、逐时刻转移；978 定理 / 0 公理 |
| T2019 | 2026-10-03 04:01 UTC (cf8e79e) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；Θ 的 Laplace–乘积精确表示、1/d 引理、乘积核与差分的界；985 定理 / 0 公理 |
| T2016 | 2026-10-03 04:04 UTC (c154f29) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS（仅报告）；EK 钉文 7 条、拆 EK-1…EK-6（约 4.0k 行），签字 DECISIONS §18；1b 因额度重跑（规则 H，不计） |
| T2021 | 2026-10-03 04:19 UTC (58bedae) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；网格 Markov、停时、Azuma/Doob 移植；MD gate 收尾（MD-1…MD-5 全部合并）；1017 定理 / 0 公理 |
| T2020 | 2026-10-03 04:23 UTC (e2aa5fe) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；KLisKLoopPin（树和满足树方程）；1027 定理 / 0 公理 |
| T2022 | 2026-10-03 04:31 UTC (5fb7729) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；EK 钉文 7 条与 3 条桥接；1032 定理 / 0 公理 |
| T2026 | 2026-10-03 04:54 UTC (3dc4f1c) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；EK-2：Ξ 衰减、球和、同号行界（挂 PT 钉文）；1037 定理 / 0 公理 |
| T2024 | 2026-10-03 04:56 UTC (1c434bb) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；PT-F2：Θ 的单位一、二阶差分界；1039 定理 / 0 公理 |
| T2023 | 2026-10-03 04:57 UTC (f40d8ca) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；PT-F1：**性质 5（prop5Decay_holds）、性质 8（prop8ZeroMode_holds）对每个 d ≥ 3 证出**；1041 定理 / 0 公理 |
| T2015 | 2026-10-03 05:00 UTC (5e7de62) | prover-max（修复 repairer） | Sonnet 5.5 effort max（修复 claude-opus-5-5） | 是（审核 RETURN 一次，仅报告） | ST-D1 设计：钉文、ST-1 拆 36 张；审核 D1 缺一个实例、D2 两条 paper-delta 未列，修复一次后 PASS；签字 §19 |
| T2025 | 2026-10-03 05:38 UTC (c8bedf7) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；KL4+5：`KLK_unique`、`TwoLoopBounded` 退役三条、`KLK_rotate`/`KLK_translate`；1058 定理 / 0 公理；T2025a 仅备注（论文用旋转/平移不变性未单列引理），不入 paper-deltas |
| T2027 | 2026-10-03 05:46 UTC (6cc5032) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；PT-G：性质 6、7（路径引理）、`prop5to8_holds`、旧接口 `thetaDecay/Short/ZeroMode_holds`；登记表删借用项；**PT gate 完成**；1065 定理 / 0 公理 |
| T2029 | 2026-10-03 05:52 UTC (890a89f) | prover（Amend 1：repairer） | Sonnet 5.5 effort high | 否（票面错） | 审核一次 PASS；合并第 5 步被登记拦（5 个事件/条件谓词未登记）是总调度票面缺陷（ST1-COMMON 第 8 条 + 预检盲区）→ DECISIONS §20、Amend 1，第 2 轮审核 PASS；S1-10；1110 定理 / 0 公理 |
| T2030 | 2026-10-03 05:53 UTC (6f99812) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-01 `Gauss/FlowCalculus`；1166 定理 / 0 公理 |
| T2032 | 2026-10-03 06:00 UTC (e318c24) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-03 `Hierarchy/ContractionBasic`（收缩系数 `W^d`，T2032c 数值核对）；1196 定理 / 0 公理 |
| T2034 | 2026-10-03 06:18 UTC (1678ea4) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；EK-3：`(sum_res_1)`、`(sum_res_2_NAL)` 全部 n；首次照 §20 自登记（`EKFastDecay` structural），合并按 H23 b 取并集；1206 定理 / 0 公理 |
| T2038 | 2026-10-03 06:29 UTC (cace419) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-11 `Green/RowIndep`；自登记 `AgreeOffRow`（structural）；1265 定理 / 0 公理 |
| T2036 | 2026-10-03 06:32 UTC (85ab436) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；KL6：`KLK_ward`（Ward 恒等式，全部 n、两种电荷顺序）；1224 行；1273 定理 / 0 公理 |
| T2031 | 2026-10-03 06:33 UTC (cca94be) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-12 `Green/LDEQuad`；自登记 `GaussIBP`（owed，S1-19 证）、`FinDep`（structural）；1345 定理 / 0 公理 |
| T2028 | 2026-10-03 08:03 UTC (64bdfd3) | prover-max（修复 repairer） | Sonnet 5.5 effort max（修复 claude-opus-5-5） | 是（审核 RETURN 一次，仅报告：补 paper-delta 候选 T2028e/f） | S1-07：ST-1 钉文入库 `Induction/Defs`、`Green/Pins`、登记（owed 9 个由 §20 自登记，§22 确认）；审核撞用量墙两次（H27，不计）；1441 定理 / 0 公理 |
| T2042 | 2026-10-03 09:45 UTC (d9de66f) | prover-max | Sonnet 5.5 effort max | 否（钉文错） | 第一次预检 FAIL：§18 签的 `EKSumDecay2` 为假（缺 `L^d ≤ W^K`）→ DECISIONS §21、Amend 1 从预检重开；重开后审核一次 PASS；EK-4 `(sumAzero) ⟹ (sum_res_2)`（唯一高风险票）；1477 定理 / 0 公理 |
| T2043 | 2026-10-03 09:02 UTC (cb7d4ba) | prover-max | Sonnet 5.5 effort max | 否 | 审核 PASS 但要签字（R1/R2：`∏ m(σ_i)` 因子，被冻结的 `KLKpi` 逼出、与论文一致）→ DECISIONS §23 照准后合并；KL7a `Loop/KLSumZero`；1476 定理 / 0 公理 |
| T2041 | 2026-10-03 10:21 UTC (3747ff7) | prover-max（修复 claude-opus-5-5） | Sonnet 5.5 effort max | 是（审核 RETURN 一次：R1–R3，补 T2041i 等） | ST-D3 设计：Steps 3–4 钉文、EK-6 消费形式、拆 34 张；签字 §25 |
| T2040 | 2026-10-03 10:23 UTC (45e2630) | prover-max（修复） | Sonnet 5.5 effort max | 是（审核 RETURN 一次：实例窗口 `ℓT`、`inst_LWtermExpN`） | LW-D1 设计：图词汇（记录 A）、钉文、展开式按 =_E、27 张；签字 §24 |
| T2046 | 2026-10-03 10:24 UTC (ea63565) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；S1-15 `Green/Stability`（d ≥ 3 常数，ST-1 关键路径第二张）；1484 定理 / 0 公理 |
| T2044 | 2026-10-03 10:36 UTC (84e54a8) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-13 `Green/LDEQuadMom`（与维数无关） |
| T2049 | 2026-10-03 10:57 UTC (56c30fb) | prover（修复 repairer） | Sonnet 5.5 effort high（修复 claude-opus-5-5） | 是（审核 RETURN 一次：D1） | S3-01：Steps 3–4 钉文入库 `Induction/Step34Pins`、登记 24 个 owed |
| T2048 | 2026-10-03 12:55 UTC (057edb0) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS（用量触顶后按规则 (H) 重跑，不算返工）；KL7b `Loop/KLSumAll` 总和界；1569 定理 / 0 公理 |
| T2035 | 2026-10-03 13:08 UTC (c163ca8) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；EK-5 `Evolution/Nonzero`（`lem:sum_decay_nonzero` 无损、两种电荷）；1570 定理 / 0 公理 |
| T2045 | 2026-10-03 13:08 UTC (5d1e6b1) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS，要求签字（三条未移植，§26 照准，不算返工）；S1-08 `Induction/{ScaleFacts,PerTimeCalc}`（D46、D47） |
| T2055 | 2026-10-03 13:44 UTC (6b2494e) | prover-hard（修复 repairer） | Sonnet 5.5 effort xhigh（修复 claude-opus-5-5） | 是（审核 RETURN 一次：缺两个编译实例） | S3-04 `Induction/QopAlgebra`：`stMollifierEx_holds`（光滑化尺度）与 `𝒫/ϑ/𝒬_t` 代数 |
| T2050 | 2026-10-03 14:02 UTC (37db678) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；LW-03 `Graph/LWVocab`（图词汇，表示法 A；登记 `DotWF`、`Consistent` structural）；D57–D62 |
| T2039 | 2026-10-03 14:16 UTC (6ef5d49) | prover-max（修复 repairer） | Sonnet 5.5 effort max（修复 claude-opus-5-5） | 是（审核 RETURN 一次） | ST-D2：Step 2 与路径层设计（仅报告；探针 `t/T2039` 0362cbc）；待签字 |
| T2057 | 2026-10-03 14:33 UTC (a68a954) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-16 `Green/EntryDom`（关键路径） |
| T2047 | 2026-10-03 14:57 UTC (5b6cbc1) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-33 `Induction/ContinuityNet` |
| T2056 | 2026-10-03 14:58 UTC (c1d4ebe) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；KL7c `Loop/KLSumZeroWard`（KL7 完结） |
| T2058 | 2026-10-03 15:02 UTC (7c3072a) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S3-23 `Induction/ScaleFacts3` |
| T2059 | 2026-10-03 15:12 UTC (eb6d67a) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS（观察：一个实例结论空真）；S3-05 `Induction/QopNorm`（`STQopNorm` 证出） |
| T2052 | 2026-10-03 15:13 UTC (bc637ce) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-14 `Green/LDEQuadT` |
| T2054 | 2026-10-03 15:16 UTC (86368fa) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S3-02 `Induction/Contract`（`STContract` 证出） |
| T2037 | 2026-10-03 15:28 UTC (31476de) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-02 `Gauss/LoopCoordinate` |
| T2051 | 2026-10-03 15:39 UTC (461ae86) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；LW-15 `Graph/LWPsi` |
| T2033 | 2026-10-03 15:45 UTC (aa42e43) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-09 `Induction/Split` |
| T2060 | 2026-10-03 16:10 UTC (89f29cf) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；LW-04 `Graph/LWStein`（登记 `Tame1` structural） |
| T2053 | 2026-10-03 19:12 UTC (fc76526) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS（Amend 1 重开不算返工，§27）；EK-6 `Evolution/Prec`（五条 `STEK*` 消费钉文）；EK gate 完成 |
| T2066 | 2026-10-03 19:31 UTC (86124dc) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；ST2-01 `Induction/Step2Defs`（ST-2 钉文入库，登记 18 行）；D83–D92 |
| T2062 | 2026-10-03 19:22 UTC (a51b69e) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-34 `Induction/Continuity`（`stNetLift_holds`）；D104 |
| T2067 | 2026-10-03 19:33 UTC (ed199e7) | prover（修复 repairer） | Sonnet 5.5 effort high（修复 claude-opus-5-5） | 是（审核 RETURN 一次：缺两个实例） | LW-P `Graph/LWPins`（LW 钉文入库）；D93–D103 |
| T2063 | 2026-10-03 19:50 UTC (bbd22a5) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-31 `Induction/ConArgDet`（`lem_ConArg` 确定性部分）；D105–D106 |
| T2065 | 2026-10-03 19:54 UTC (64a33ea) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；S1-04 `Hierarchy/ContractionSecondLoop` |
| T2061 | 2026-10-03 19:55 UTC (40f70b9) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-17 `Green/FlucVanish`（Amend 1 有界权重开不算返工，§30） |
| T2064 | 2026-10-03 20:09 UTC (06429ba) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-05 `Gauss/LoopFlowStein` |
| T2076 | 2026-10-03 20:23 UTC (8a8cfeb) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-32 `Induction/ConArg`（`STConArg` 证出） |
| T2071 | 2026-10-03 20:25 UTC (092aaf0) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；ST2-02 `Induction/Step2Core` |
| T2075 | 2026-10-03 20:32 UTC (a84c579) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；ST2-06b `Evolution/PropTInf` |
| T2073 | 2026-10-03 20:40 UTC (a262beb) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；ST2-22 `Path/StepDecomp` |
| T2070 | 2026-10-03 20:52 UTC (eaf0614) | prover-max | Sonnet 5.5 effort max | 否 | 审核一次 PASS；KL8+9 `Loop/KLMolecule` |
| T2072 | 2026-10-03 20:55 UTC (593e519) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；ST2-20 `Path/OneStep` |
| T2074 | 2026-10-03 20:58 UTC (06b49b2) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；ST2-18 `Path/NetLift1`（`stNetLift2_part1`） |
| T2082 | 2026-10-03 22:27 UTC (efeda82) | prover | Sonnet 5.5 effort high | 否 | 审核一次 PASS；ST2-19 `Path/NetLift2`（`STNetLift2` 证出）；D132–D134 |
| T2077 | 2026-10-03 22:32 UTC (3b98b27) | prover | Sonnet 5.5 effort high | 否 | Amend 1 后审核一次 PASS（删死代码两条目标，§31，票面错误不算返工）；S1-06 `Gauss/LoopGenerator`；D127–D128 |
| T2078 | 2026-10-03 22:36 UTC (7c7652e) | prover-hard | Sonnet 5.5 effort xhigh | 否 | 审核一次 PASS；S1-18 `Green/LDE`（有界权）；D129–D131 |
