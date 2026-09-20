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

每个 agent 开工先读这一段。

1. **不留 `sorry`。** 证不出来就停下说「卡在 X，试过 Y 和 Z，失败原因是 W」。
   共享工作树里一个 `sorry` 会让所有人的 `build.log` 变红，还会触发公理审计。
2. **做不了的东西写成 `structure` 字段或定理参数，不写 `axiom`。** 见下面「接口的形式」一节。
3. **不许发明 Mathlib 引理名。** 先 grep `../RBM1D/.lake/packages/mathlib/Mathlib/`，
   或新建临时 `RBM3D/Probe.lean` 加 `#check @foo` 看签名。`exact?` / `apply?` / `rw?` / `aesop` 鼓励用。
   **核实过的名字和签名记进 `docs/mathlib-api.md`**，别让下一个人重查一遍。
4. **造轮子之前先查仓库。** `grep -rn` 一下 `RBM3D/`，看这条引理是不是已经有人证过了。
5. **公理审计写进构建。** `./check.sh` 会跑 `#assert_rbm_axioms`，违规即**编译失败**——
   靠人记得跑 `#print axioms` 是靠不住的。**不用 `native_decide`。**
6. **陈述逐字对应论文。** 任何偏离记进 `docs/paper-deltas.md`，而且要写明
   **论文第几页、改哪一段、大约几行**——这样「论文最终要改多少」随时能算出来。
7. **只按文件名 `git add`，绝不 `git add -A`。** `-A` 会把别人正在写的文件暂存进你的提交。
8. **小步提交。** 一次一条引理；绿了就 commit。攒一大坨再一起编译，错了无法二分。
9. **共享文件只做点插入，绝不整体重排。** 唯一的共享文件是根 import 列表 `RBM3D.lean`。
   用 `sorted(set(lines))` 之类去重会把末尾的 `#assert_rbm_axioms` 搅进 import 块，整体构建挂掉。
10. **随机层按「没有 Itô」那条路走，不要去碰 Itô 本身。**
    ⚠️ **这条 beat 15 整条重写过。若你记得的是「不碰随机层」，那是旧版，请读下面的现行文本。**
    （beat 19 有过一次按旧版跳过 Q42/Q43 的事，所以在这里加这一行。）
    beat 15 改的依据是：
    原来写的是「不碰随机层」，但 `docs/stochastic-audit.md` 的审计表明这篇论文的证明
    **不真的需要过程**——全文没有 Doob、没有 Markov 性、没有域流、没有两时刻联合律，
    而关键鞅引理 `lem:DIfREP` 的**陈述本来就是矩不等式**。
    于是随机层可以用「一时刻边缘律 + 生成元恒等式 + 高斯分部积分」重建，见工单 Q42–Q46。
    **仍然不要碰的**：Mathlib 里的 Itô 公式、SDE、矩阵布朗运动、DBM——它们不存在，
    也不在这条路线上。另外 universality 与 §6 之后的层级暂时仍不在范围内。
11. **常数不求最优。** 统一 `∃ C > 0, ∃ c > 0, ∀ ...`；`≺` 用 `DetDom` / `UnifDetDom` 封装。
    **对外一律保持论文的 `≺`**，矩只活在证明内部——接口签名冻结，论文那边就只需要改证明，
    不动任何陈述、不重新编号。
12. **论文里的 `≲`、`≺`、`≍`、`∼` 都是量词，不是不等号。** 翻译时最容易丢的就是它们背后的
    「存在常数」「对每个 `ε`」。`|r| ≲ |a|` 不是 `|r| ≤ |a|`，而是「存在常数 `c`，`|r| ≤ c|a|`」——
    用在假设位置时要写成 `∀ c > 0`（对每个常数都成立才是忠实的前件）。**Q21 在性质 6、7 上就栽在这里。**
13. **改正一条陈述时，留下一个机器可检的反例。** 光把陈述改对，下一个人不知道原来错在哪、
    为什么不能那样写。`RBM3D/Test/InterfaceShape.lean` 已经有两条：`not_decayShort_at_one`
    证明旧的性质 5' 在谱参数 `1` 处不成立；`not_zeroMode_without_removal` 证明性质 8 里把
    `Θ̊` 换成 `Θ` 可证伪。**这些反例随全量构建跑**——比注释可靠，比复述准确。
14. **heredoc 写完要验证。** `cat > f <<'EOF'` 有可能静默失败，而后续的 `sed` 却成功，把失败掩盖掉。
    写完 `ls -l` 确认，并**立刻提交**，免得被 `git clean` 清掉。

15. **凡是本项目没有证出来的数学前提，都必须是一个具名的 `Prop`，不许写成匿名的 `∀/∃` 从句。**
    `PropTH` 五条、`KTreeRep` 是这样做的，所以审计能报出「有多少条定理靠着它」。
    但 Q22a 的 `kTwoFormula_of_isKLoop` 带了一个先验界 `hbdd`（2-loop 在每个 `[0,T₀]` 上有界），
    它直接写在签名里——**签名里看得见，可任何汇总都数不到它**。
    于是「这个开发还欠什么」这个问题，只能靠逐条读签名来回答。
    **做法**：给它起名（如 `TwoLoopBounded`），与 `KTreeRep` 同级。
    这样 Q26 的自动发现能抓到、Q41 的证书能要求到、两本账才算完整。
    **匿名前提不是「隐藏」，但它是「数不着」——对一份声称零公理的开发，这两者差别不大。**

## 永不停工

**队列见底 = 全员停工，这是这个项目里唯一不可接受的状态。**

`docs/QUEUE.md` 里 OPEN 的工单永远要比 agent 多。若你开工时发现没有 OPEN 的，
**不要停下来等**，按这个顺序自己挑活，并在队列表里补一行说明你在做什么：

1. **储备工单**（队列末尾「储备」一节，已经写好但没编号的）；
2. **维护**：把带假设的引理消掉假设、把 `docs/mathlib-api.md` 补全、把长证明拆短；
3. **审计**：挑论文的一节逐字对一遍 Lean 陈述，把偏离记进 `paper-deltas.md`。

## 接口的形式：`structure` 字段，不是 `axiom`

**这一条推翻了本项目早期的做法，要按新的来。**

论文引用而未证的结论（`lem_propTH` 性质 5–8 等），早期写成了 `axiom` 放在
`Propagator/Interface.lean`。姊妹项目 RBM1D 的经验是**不要这样**：

* `axiom` 会污染公理审计，而且没人知道哪天该把它拿掉；
* 把它做成 **`structure` 字段或定理参数**，下游立刻能编译、能证、能并行推进；
* 等到有人真把它证出来时，**原地把字段换成定理，签名一个字不改**，
  依赖它的工单一张都不用返工。`axiom` 做不到这件事。

本项目已经在两处自发走对了：`Graph/Model.lean` 的 `Case.Rel` 是显式假设，
`Propagator/Basic.lean` 早期的 `hS` / `hone` 也是假设（后来被 Q3/Q4 消掉了，
签名没变，下游零返工——这正是这条规则要买的东西）。**Q19 是把剩下 5 条 axiom 也改过去。**

判据：**这条结论将来有没有可能被证出来？** 有，就写成字段/参数；
只有「永远不打算证」的才考虑 axiom，而目前一条都不属于这类。

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

**push 的正确做法：Cowork 只 commit，终端常驻一个 agent 负责 push 和编译。**
Cowork 的沙箱里没有 credential helper、没有 keychain，直接 push 必然失败
（实测：git 代理拒绝注入凭据）。但 `git add` / `git commit` 只动本地 `.git`，不需要凭据，
所以照常做。在 Mac 终端里常驻一个 Claude Code agent 负责 `git push`（顺带跑 `lake build`），
两边在**同一个工作树**上，它一 push 就把两边的 commit 一起推上去。
这也正是两边分工的意义：**终端 agent 有编译器和凭据，Cowork 有长上下文、能读 PDF、能管队列和蓝图。**

**Cowork 无法编译，也无法 push。** 这个仓库不在云端会话的授权仓库集里，git 代理
会拒绝注入凭据（403）。所以 RBM2D 那套「写 → push → 读 CI 日志 → 改」的回路，
在这个项目里**暂时不可用**。要打通，Jun 需要把
`JYin80/Lean-Band3d_arXiv-2507.20274` 加进会话的 sources。在那之前：

**Cowork 写出来的 Lean 一律按「草稿」对待，第一件事是拿到本机编译。** 这就是 T1。

### 交接契约

`docs/STATUS.md` 是两边**唯一**的共享状态。任何一边：开工前读它，收工前更新它。
卡住时写清楚「卡在 X，试过 Y 和 Z，失败原因是 W」，另一边才接得上。
分工按**文件**切分，不按难度切分。**绝不用 `git add -A`**。
