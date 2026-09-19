# CLAUDE.md — RBM3D

用 Lean 4 + Mathlib 形式化 *Delocalization of non-mean-field random matrices in
dimensions $d\ge 3$*（arXiv:2507.20274，Inventiones 投稿版）的确定性内核。

姊妹项目：`../RBM1D`（d=1，arXiv:2501.01718，**已完整编译**，2082 条声明，公理干净）
和 `../RBM2D`（d=2，arXiv:2503.07606）。RBM1D 的代码是本项目最可靠的参照——
`Defs/Domination.lean` 和 `Test/Axioms.lean` 就是从那边搬过来的。

## 开工流程（Claude Code 读这一段）

**工单在 `docs/QUEUE.md`。** 从上往下找第一条 `OPEN`，改成 `CLAIMED` 并单独提交这一行，
做完改 `DONE`，在 `docs/STATUS.md` 记一笔（新增了哪些声明、卡在哪、下一步）。

队列由 Cowork 侧约每 10 分钟刷新一次；**已被认领（`CLAIMED`）的工单不会被改写**，
所以认领动作要尽早提交。卡住时在 `STATUS.md` 里写清楚「卡在 X，试过 Y 和 Z，
失败原因是 W」——那是两边唯一的交接面。

## 唯一真相来源

- **论文**：`paper/2507.20274-inventiones-submission.pdf`（97 页），源码在 `paper/tex/`，
  节与文件的对照表见 `paper/README.md`。
  **只依据这篇论文，不引用任何其他文献**——论文引别人的地方，在 Lean 里当作 `axiom`。
- **路线图**：`docs/PLAN.md`
- **当前进度**：`docs/STATUS.md` —— **每次会话开始先读它，结束前更新它**
- **工单队列**：`docs/TASKS.md` —— **开工前先在表里认领并单独提交这一行**
- **与论文的偏差**：`docs/paper-deltas.md` —— 凡 Lean 陈述 ≠ 论文字面陈述，必须记一条

## 这个项目与 d=1、d=2 的两点根本区别

**一、`d` 是参数。** RBM1D 固定 d=1，RBM2D 固定 d=2（索引类型 `ZMod L × ZMod L`）。
这里格点是 `RBM.Zd d L := Fin d → ZMod L`，`3 ≤ d` 只在真正用到的地方引入。
论文里真正用到 `d ≥ 3` 的只有两处：临界格点求和 `(eq:latticesum_d3)`（d=3 多一个 $\log L$），
以及 $\mathcal T_t$ 的 $(r+1)^{-(d-2)/2}$ 衰减。别处一律保持 `d` 一般。

**二、传播子的衰减估计是公理，不是定理。** 这是本项目形状的决定性事实，务必先读懂：

d=2 那篇论文在它的 §8 里从零证明了传播子估计，所以 RBM2D 里那些是定理。
**这篇论文没有。** 附录 A.1 把 `lem_propTH` 的性质 5–8 归给了前人：

| 陈述 | 论文标签 | 出处 |
|---|---|---|
| 多项式 + 指数衰减 | `(prop:ThfadC)` | `[DYYY25]` Lemma 2.14，"we omit the details" |
| σ₁=σ₂ 的强衰减 | `(prop:ThfadC_short)` | 本文有证，但用了 `[bourgade2019random]` Lemma 4.2 |
| 一阶差分 | `(prop:BD1)` | "not stated explicitly in `[yang2024Del]` ... we omit the details" |
| 二阶差分 | `(prop:BD2)` | `[yang2024Del]` (E.19) |
| 去零模传播子 | `(prop:ThfadC0)` | `[yang2024Del]` Lemma 3.1 |

附录 B 同理：三条 expansion 引理引 `[yang2024Del]` B.9–B.11。

按「只依据这篇论文」的规则，这些一律是 `axiom`，全部集中在
`RBM3D/Propagator/Interface.lean`（以及将来的 `Graph/Expansions.lean`），
并且**必须**登记在 `RBM3D/Test/Axioms.lean` 的 `interfaceAxioms` 里。

**这不是缺陷，是产出。** 那张 axiom 清单是「这篇论文向前人借了什么」的精确、
机器可核查的记录，审稿人和 `#print axioms` 都看得见。审计命令还会报出每条
axiom 被多少条声明依赖——那个数字是衡量借用程度的诚实指标，把某条 axiom 降级成
定理，就是让它的计数归零。

## 环境

Lean `4.34.0` / Mathlib `v4.34.0`，与两个姊妹项目完全一致。

```bash
cd ~/Lean_proof/RBM3D
lake exe cache get      # 拉 Mathlib 预编译 olean
lake build
```

**磁盘**：已不是约束。卷上还有约 123 G（74% 用），一份 `.lake` 约 8.1 G（其中 mathlib 的
build 6.6 G），三个项目各一份放得下。三者 toolchain 与 mathlib rev 完全一致
（`5ed2965256430c3649e86755f9576b54eca72435`），所以**共享在原理上安全**，但既然空间够，
建议各用各的：互不干扰，`lake build` / `./check.sh` / CI 行为一致，也不会出现某个项目
`lake update` 静默改掉共享树的情况。真要省空间，macOS 上用 APFS 写时复制克隆
（`cp -c -R RBM1D/.lake/packages RBM3D/.lake/packages`，在 Terminal 里跑）比软链安全。
`lake exe cache get` 的下载缓存本来就是跨项目共用的，所以重复的只是解包后的 build 树。

Mathlib 源码在 `../RBM1D/.lake/packages/mathlib/Mathlib/` —— 找 API 就 grep 这里，
`.lake` 建好之前也能用。

## 构建回路

```bash
lake env lean RBM3D/Defs/Lattice.lean   # 单文件，秒级 —— 默认用这个
./check.sh                               # 全量，结果写进 build.log
./watch.sh                               # 另开终端，改动即自动重编
```

**绝不在没有实际跑过编译的情况下说「写好了」。** 每次回报前必须有一次 exit=0。

## 硬性规则

1. **不留 `sorry`。** 证不出来就停下说「卡在 X」，不要 sorry 占位然后继续往下写。
2. **不许发明 Mathlib 引理名。** 先 grep `../RBM1D/.lake/packages/mathlib/Mathlib/`，
   或新建临时 `RBM3D/Probe.lean` 加 `#check @foo` 编译看签名。
   `exact?` / `apply?` / `rw?` / `aesop` 鼓励用。
3. **公理审计。** `./check.sh` 会跑 `#assert_rbm_axioms`，它比 `#print axioms` 严：
   任何不在 `allowedAxioms ∪ interfaceAxioms` 里的公理（含 `sorryAx`）都让构建失败。
   **新增 axiom 必须同时改 `interfaceAxioms` 并在 `docs/paper-deltas.md` 记一条。**
   **不用 `native_decide`。**
4. **陈述逐字对应论文。** 不得不加假设（如 `3 ≤ L`）或换陈述形式，写进 `docs/paper-deltas.md`。
5. **小步提交。** 一次只动一条引理 / 一个文件；绿了就 `git commit`。
6. **不碰随机层**（Itô、Dyson Brownian motion、loop hierarchy、universality）。
7. **常数不求最优。** 统一 `∃ C > 0, ∃ c > 0, ∀ ...`；`≺` 用 `DetDom` / `UnifDetDom` 封装。
   但**接口公理写成展开式**（`∀ τ > 0, ∃ C > 0, ...`）而不是 `≺`：公理是要被人逐字
   对着论文核的，不该让核对的人再去展开一个定义。

## 命名与风格

- namespace `RBM`（与两个姊妹项目同名，不会同时 import，不冲突）；图论层在 `RBM.Graph`
- 格点 `RBM.Zd d L := Fin d → ZMod L`，`abbrev` 以便 `Pi` 实例自动可见
- 距离是周期 ℓ¹ 距离 `RBM.zdistD`（论文明说范数选取无关紧要）
- 变量约定：`d L : ℕ`、`hd : 3 ≤ d`、`hL : 3 ≤ L`、耦合参数 `g : ℝ`、时间 `t : ℝ`
- 文件头 copyright 块照抄现有文件
- 每落地一个声明，去 `blueprint/src/content.tex` 对应节点补 `\lean{}` + `\leanok`；
  节点名与论文 label 一一对应（`lem_propTH`、`prop:ThfadC`、`lem:propT`、`def scalingBA`）

## 分工：Claude Code 与 Cowork

| | Claude Code（本机） | Cowork / chat（云端） |
|---|---|---|
| 证明的试错循环 | **主场**。`lake env lean 单文件` 秒级返回 | 云端拉不到 Mathlib 的 olean cache（出口策略挡掉 `reservoir.lean-lang.org` 和 GitHub releases），**编不了** |
| 读论文 PDF / tex | `paper/` 下都有 | 同样都有 |
| 路线规划、阶段划分、开工单 | — | **主场** |
| 蓝图渲染 / 依赖图 | 需本机装 plasTeX + graphviz | 工具链现成 |
| git / CI / GitHub Pages | 都行 | **push 不了**，见下 |

**CI 是通的，而且快。** 仓库公开，`Lean Action CI` 每次约 2 分钟，
运行页上的 job summary 公开可读（`lean_action_ci.yml` 第二步把完整 `lake build` 输出写进
`$GITHUB_STEP_SUMMARY`）。所以只要 Jun push 了，Cowork 侧就能读到全部编译错误。

**Cowork 无法编译，也无法 push。** 这个仓库不在云端会话的授权仓库集里，git 代理
会拒绝注入凭据（403）。所以 RBM2D 那套「写 → push → 读 CI 日志 → 改」的回路，
在这个项目里**暂时不可用**。要打通，Jun 需要把
`JYin80/Lean-Band3d_arXiv-2507.20274` 加进会话的 sources。在那之前：

**Cowork 写出来的 Lean 一律按「草稿」对待，第一件事是拿到本机编译。** 这就是 T1。

### 交接契约

`docs/STATUS.md` 是两边**唯一**的共享状态。任何一边：开工前读它，收工前更新它。
卡住时写清楚「卡在 X，试过 Y 和 Z，失败原因是 W」，另一边才接得上。
分工按**文件**切分，不按难度切分。**绝不用 `git add -A`**。
