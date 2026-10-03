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
