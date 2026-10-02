# RBM3D 路线账本（总调度独占；监督每次先读这一页）

2026-10-02 17:26 UTC 调度 V1 按 DECISIONS §3–§7 建立。终点：论文 §2 的六条主结果（§3）；唯一外部输入：Landon–Sosoe–Yau Thm 2.2（§5）；随机层默认走 RBM2D 的路线（§7）。宽口径票数含返工（设计单计入；Lean 未动的报告返工不计，同 RBM2D 监督 0749 的计法），按 gate 各自计数；到 25、40 写监督请求，到 50 仍未闭合自动建议 HOLD（TEAM §6）。旧工作模式的代码（89ef8a9：509 定理 / 173 定义 / 0 公理）只当线索，覆盖与否以 T2001 为准。

| gate | 论文位置 | 路线 | 状态 | 宽口径票数 | 未决问题 |
|---|---|---|---|---|---|
| SV 覆盖摸底（不属 gate） | 六条终点及其全部依赖 | 逐条对到 main 上的 Lean 与 RBM2D 对应声明 | T2001 待放行 | 1 | 终点钉文在探针里提出，冻结等 T2002 的词汇 |
| F0 基础层 | §2：`Zd d L`、`\|x\|_L`、`S^(B)(λ)`、`Θ_t`、`Θ̊_t`、`ℓ_t`、`B_{t,K}`、`m_sc`、`z_t`、`lem_propTH` 性质 1–4 | 旧代码（`RBM3D/Defs`、`Propagator/{Basic,Props4,Deriv}`） | 已编译，未核实（T2001 分类） | 0 | — |
| MD 模型与流的词汇 | `(bandcw0)`、`(eq:variancematrix)`、`(MBM)`、`def_flow`、`zztE`、`Def:G_loop`、`lem:SE_basic`、`(stoch_domination)`；BA 的 `(eq:H_blocka)`、`zztE_BA` | 设计单 T2002：保留旧定义或移植 RBM2D 的 `Sizes`/`seqP`/路径载体；`λ` 取序列；单一尺度参数 | T2002 待放行 | 1 | `λ` 随 `N` 变（可趋于 0）；RBM2D 的 `d : Sizes` 与维数 `d` 撞名 |
| PT 传播子性质 5–8 | `lem_propTH` 5–8（`(prop:ThfadC)`、`(prop:ThfadC_short)`、`(prop:BD1)`、`(prop:BD2)`、`(prop:ThfadC0)`）；App. A.1 | 设计单 T2003：论文路线（内部证明，不引 [yang2024Del]、[Lawler_book]、[bourgade2019random]）对比 RBM2D 的 Fourier 路线推到 d 维 | T2003 待放行 | 1 | 旧 `Interface.lean` 五个 Prop 的常数依赖 `g`、`m`（旧 D13），λ→0 时不够用 |
| KL K-loop 层 | `Def_Ktza`、`(Kn2sol)`、`(Kn3sol)`、`lem_WI_K`、`ML:Kbound`、App. A.5（`tree-representation`、`(eq_K-Kpi)`、`lem_pureloop`） | 设计单 T2004：移植 RBM2D P6（树表示定义）到 d 维；内部证明 [YY_25] 3.4/3.6/3.10/3.11 | T2004 待放行 | 1 | 旧 `KTreeRep`、`KLoopBound` 是 Prop 假设，要撤掉 |
| EK 演化核 | §4.5 `ks-statements`、App. A.2–A.4（`lem:propT`、`claim:TTk`）、sum-zero、去零模 | 待设计（EK-D1，在 T2003/T2004 之后） | 旧 `RBM3D/Kernel/*` 已编译，未核实 | 0 | — |
| ST 随机层 Steps 1–6 | `lem:main_ind`、`ML:GLoop`、`ML:GLoop_expec`、`ML:GtLocal`；§3–§6 | DECISIONS §7：网格高斯游走真路径 + 停时 + Azuma/Doob；其余单时刻律；Step 2 的 `J_{u,D}`/Gronwall 照本文 | 待设计（ST-D1…，子 gate 按 T2002 的移植表定） | 0 | Step 2 用停时 `(eq:def2_stopping)` |
| LW light-weight 项与图展开 | §7（`lem:LWterm`、`lem: EWGn2_N`、`lem:LW_moment`、`lem:Anp`、`lem:LW_moment_exp`）、App. B.1–B.2（`lem:LWterm_EXP`、`lem:localregular`、三条展开引理、`lvl1 lemma`） | 全部内部证明（DECISIONS §5）；姐妹项目都没有 | 待设计（LW-D1，在 T2002 之后） | 0 | 体量未知；如代价过大，单独问 Jun |
| MA 主定理装配 | §2.6；Thm 2.1、2.2、2.3、2.5；`RBM3D/Endpoints.lean` 冻结 | 照 RBM2D P9 | 等 T2001、T2002 | 0 | — |
| UN bulk universality | Thm 2.4 | 照 [DYYY25] Thm 2.6 与 RBM2D P10；外部输入只 LSY Thm 2.2（复 Hermitian、单位密度读法） | 待设计（UN-D1） | 0 | LSY 的极限核算按 d ≥ 3 重做 |
| BA block Anderson | §8、App. B.3；`(self_m)`、`(def_G0)`、`e_λ`、`(def:Theta_BA)`、`zztE_BA`、`tree-representation_BA`；Thm 2.7 | 全部内部证明（[RBSO1D] 各条、[LeeSchSteYau2015] Lemma 3.5、Combes–Thomas、[Biane]）；RBM2D 有 Combes–Thomas、FreeConv 文件可参考 | 待设计（BA-D1，在 PT、KL 之后） | 0 | 体量最大的未知块 |
