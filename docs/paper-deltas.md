# 与论文的偏差（RBM3D）

> 凡 Lean 陈述 ≠ 论文字面陈述，必须在这里记一条。谁发现谁记，不要只在对话里说。

## D1 · `3 ≤ L` 是显式假设

论文把 `S^(B)(g)` 的双随机性当作显然。它在 `L ≤ 2` 时不成立：`L = 2` 时
`1 = -1` in `ZMod 2`，每点的 `2d` 个邻居塌成 `d` 个，行和变成
`(1 + d g²)/(1 + 2d g²) ≠ 1`。所以 `3 ≤ L` 在本项目里是显式假设，
和两个姊妹项目的处理一致。
（2026-10-03 补，T2002c / DECISIONS §10 T2001a、§12）尺寸序列 `Sizes d` 把它做成字段 `three_le_L`（T2006，`RBM3D/Defs/Sizes.lean`）；论文只说 `L` 为偶数（1_2:269）。

## D2 · 周期距离取 ℓ¹

论文写 `|a|`、`|a - b|` 而不指定范数，并在 §2.1 说明范数的选取无关紧要。
本项目固定为周期 ℓ¹ 距离 `RBM.zdistD d L x = ∑ i, zdist L (x i)`，
其中 `zdist L u = min u.val (L - u.val)`。

## D3 · `d - 2`、`d - 1` 是自然数减法

`Bparam` 里的 `(K+1)^(d-2)`、`(prop:BD1)` 里的 `(|a|+1)^(d-1)` 用 `ℕ` 的截断减法。
在 `d ≥ 2`（本论文恒设 `d ≥ 3`）时与论文一致。

## D4 · `ℓ_t` 在 `t = 1` 处有值

`(eq:ellt)` 的 `|1-t|^{-1/2}` 在 Lean 里写成 `1 / Real.sqrt |1 - t|`，
于是 `t = 1` 时是 `1/0 = 0`，`ellT` 取值 `1` 而非无定义。
论文的每个使用点都有 `t < 1`，所以不影响任何陈述。

## D5 · 接口写成 `Prop` 定义 + 结构字段，且用展开式而非 `≺`

**形式（2026-09-19，Q19 改）**：性质 5–8 **不是 `axiom`**，而是
`Propagator/Interface.lean` 里的五个 `Prop` 定义（`ThetaDecay`、`ThetaDecayShort`、
`ThetaDiffOne`、`ThetaDiffTwo`、`ThetaZeroMode`），打包成 `structure PropTH d g m`。 〔T2127：此 Lean 声明已删，见 D277〕
用到它们的定理多带一个参数 `(hP : PropTH d g m)`，取 `hP.decay` 之类。
于是 `Test/Axioms.lean` 的 `interfaceAxioms` **为空**，审计回到 RBM1D 那种最严形式：
只允许 `propext` / `Classical.choice` / `Quot.sound`。
好处是将来逐条证出来时「原地把假设换成定理，下游签名一个字不用改」——
`Propagator/Basic.lean` 的 `hS` / `hone` 被 Q3/Q4 消掉时就是这样，零返工。
每个 `Prop` 自带论文的默认假设 `3 ≤ d`、`0 < g`、`‖m‖ = 1` 作为前件，可以单独陈述、单独假设、单独消解。

**陈述仍用展开式**：`(prop:BD1)`、`(prop:BD2)`、`(prop:ThfadC0)` 论文用 `≺` 写，
这里写成 `≺` 所缩写的 `∀ τ > 0, ∃ C > 0, ∀ L ≥ 3, ...`，而不用 `RBM.UnifDetDom`。
理由：这几条是要被人逐字对着论文核的，不该让核对的人再去展开一个定义。
定理层仍然用 `DetDom` / `UnifDetDom`。

`≺` 里的 `N^τ` 在展开式里写成 `L^τ`。论文的 `N = (WL)^d`，两者相差一个固定幂次，
被 `≺` 自身吸收，所以这不是实质偏差。

## D6 · 只形式化随机带状矩阵模型的传播子

> **作废**（调度 V1，2026-10-02 17:05 UTC）：Jun 定六条主结果全做，含 block Anderson 模型（DECISIONS §3）。

`def_Theta` 对两个模型统一定义 `Θ_t = (1 - t M^(σ₁,σ₂) S^(B))⁻¹`。
`RBM.Theta` 保留了这个一般形式，但 `RBM.ThetaRBM` 以及接口公理只覆盖
**随机带状矩阵模型**，那里 `M^(σ₁,σ₂) = m(σ₁)m(σ₂) I`，于是传播子只通过乘积
`m := m(σ₁)m(σ₂)` 依赖两个符号。
block Anderson 模型（`S^(B) = I`，结构全在 `M^(σ₁,σ₂)` 里）另开工单。

## D7 · `ord` 取值在 `ℤ`

`(eq:ordG)` 的 `n_W - n_V` 可以是负的，所以 `RBM.Graph.ord : Counters → ℤ`。
论文不区分。

## D8 · 附录 B 的 case (vi) 在 Lean 里是 case (iv) 的推论

`(eq:ordG_BA)` 的 case 分析里，第三轮补的 case (vi)
（`n_W + 1`、`n_V` 不变、`n_S` 不减）的算术被 case (iv)
（`n_W + 1`、`n_V ≤`、`n_S ≥`）包含，后者假设更弱。
所以 `ord_case_vi` 直接由 `ord_case_iv` 推出。
这不是偏差，而是记录一个事实：**case (vi) 的内容是那个构型存在，不是不等式成立**。

## D9 · 作者已答复的三个交叉引用问题（2026-09-19）

第三轮校对向作者提了三个「甲类」问题（形式化时可能变成 `sorry` 的地方）。答复如下，
**三条都不是缺口**，所以都不进 `interfaceAxioms`：

1. **CLT 增益因子**（`3_5_Loop_Hierarchy.tex` L2186，`lem;CLT` 证明的开头一段）。
   作者：**这是启发式陈述，没有用在证明里，后面有正式证明。**
   核对属实：这一段在 `\begin{proof}[Proof of \Cref{lem;CLT}]` 之后，上一句已经写了
   "intuitively"，整段是证明思路概述，正式论证在其后。
   *形式化影响*：无。这一段不产生 Lean 义务，形式化 `lem;CLT` 时对着后面的正式论证做。
   （旁注：紧随其后有一段注释掉的合作者笔记，写着增益因子是 `ℓ_s/ℓ_t`。仅供参考，
   不是论文正文。）

2. **`eq:LW` / `eq:BE` 与 `[yang2024Del]` Lemma B.10**。
   作者：合作者查过，**完全一样**。暂不处理，后面再核。
   为让以后那次核对省事，把我当时比对的**具体位置**记在这里：
   `eq:BE`（Lemma B.9）第一项写的是 `Ǧ_ββ G_αy`（`ββ` 带 check，`αy` 不带）；
   `eq:LW`（Lemma B.10）括号内对应的第一项写的是 `Ǧ_αy Ǧ_ββ`（**两个都带 check**）。
   若 `eq:LW` 的内层括号本应是 `eq:BE` 右端把 `x` 换成 `y`，则 `Ǧ_αy` 处多了一个 check。
   **待核**：`[yang2024Del]` Lemma B.10 那一项是 `G_αy` 还是 `Ǧ_αy`。
   *形式化影响*：这两条都是接口公理（论文引用而非证明），陈述写哪个版本以原文为准；
   落地前必须把这一条核清楚，否则公理就写错了。

3. **`S^±` 相对 `[yang2021delocalization]` 差一个 `m²`**。
   作者：**故意差着一个 `m²`**，是有意的重新归一化。
   *形式化影响*：无缺口。但 `S^±` 的 Lean 定义必须按**本文**的归一化写，
   并在 docstring 里注明与 `[yang2021delocalization]` 差 `m²` 是有意的，
   免得后来的人「修」回去。

## D10 · `(Owx)` 与 `(Oe2x)` 不作为公理进入 Lean（beat 2 决定）

**出处更正**：这两条展开出自 `[yang2021delocalization]` Lemma 3.5 与 Lemma 3.14
（`7_8_light_weight.tex` L293、L334），不是 `[yang2024Del]`。原文对 `G = (H−z)⁻¹` 陈述，
本文把 `G, S` 换成 `G_t, S_t = tS` 使用。

**决定**：**不把它们写成 `axiom`**。（2026-09-19 Q19 之后，`interfaceAxioms` 已经清空，全项目零公理。）

它们是 `=_𝔼` 恒等式，对 `G` 的任意可微函数成立；逐字陈述需要概率空间、预解式、
Wirtinger 导数 `∂_{h_{αx}}` 与 `f` 的具体函数类——前三者正是 `CLAUDE.md` 规则 6
划出 Phase 1 的随机层。而一条写错的 axiom 编译器查不出来，这两条又恰好带着
`S^±` 的 `m²` 归一化差（D9.3）和 `S → S_t` 的替换，是最容易写错的样本。

**证明实际用到的部分已经进了 Lean，而且形式更好**：
* 确定性内核 `∂_{h_{αw}} G_{ij} = −G_{iα} G_{wj}` 在 `Graph/Expansions.lean` 里是**定理**
  （沿矩阵单位 `E_{αw}` 的方向导数，即把 `h_{αw}`、`h_{wα}` 当独立变量的 Wirtinger 约定）；
* 展开产生的构型与计数关系，在 `Graph/Model.lean` 里是 `Case.Rel`，**作为显式假设**出现在
  每条定理的类型里——比 axiom 更可见，调用处一眼能看到依赖什么。

**原则**：凡是「论文引理的推论、而非论文逐字陈述」的东西，一律写成假设而非公理。
`eq:GGraisesord` 将来同样处理。

## D11 · `(prop:ThfadC_short)` 限定在 `σ₁ = σ₂`（2026-09-19 修正）

**问题**：接口里性质 5'（`(prop:ThfadC_short)`，强指数衰减）原先写成「对任意 `‖m‖ = 1`」，
谱参数取 `t·m`。**这样写是假的**：`σ₁ ≠ σ₂` 对应 `m(+)m(-) = |m|² = 1`，
此时 `Σ_b Θ_{t,0b} = (1−t)⁻¹` 随 `t → 1` 发散，而所claim的右端与 `t` 无关、求和后有界
（`Σ_a e^{-c|a|}` 一致有界，见 `RBM.sum_radial_exp_decay_le`）。

**已机器验证**：`RBM3D/Test/InterfaceShape.lean` 的 `not_decayShort_at_one` 证明了
谱参数为 `1` 时该界不成立。

**修正**：`ThetaDecayShort d g m` 现在是 `σ₁ = σ₂` 的陈述——谱参数取 `t·(m*m)`（即 `m(σ)²`），
并加上论文的默认假设 `0 < m.im`（`Im m > 0`，常数按论文本来就允许依赖 `κ`），它保证 `m² ≠ 1`。
`structure PropTH` 只打包性质 5、6、7、8（这四条对任意单位谱参数都成立）， 〔T2127：此 Lean 声明已删，见 D277〕
**性质 5' 不进 bundle**——否则 `PropTH d g 1` 就成了一个假的假设，而 `σ₁ ≠ σ₂` 的情形到处都要用。

**教训**：这个缺陷在它还是 `axiom` 的时候就存在，而那时它意味着**不一致**（可以推出任何东西），
审计也查不出来——公理审计只管「有没有公理」，不管「公理对不对」。改成假设之后，
同样的错误只会让定理变成空洞的，而这一条是能被证伪的，也确实被证伪了。
这条支持 Q19 的判断：**接口写成假设，比写成公理安全**。

## D12 · 性质 6、7 的 `|r| ≲ |a|` 按「对每个常数」读（2026-09-19，Q21）

论文性质 6、7（`(prop:BD1)`、`(prop:BD2)`）写的是「holds for all `a, r ∈ Z_L^d` satisfying `|r| ≲ |a|`」。
`≲` 在本文里表示「至多差一个常数倍」，所以忠实的读法是：**对每个常数 `c > 0`**，在 `|r| ≤ c|a|` 上成立，
而 `≺` 的常数可以依赖 `c`。`Propagator/Interface.lean` 的 `ThetaDiffOne` / `ThetaDiffTwo` 因此带一个 〔T2127：此 Lean 声明已删，见 D277〕
`∀ c : ℝ, 0 < c →` 前件，条件写成 `(zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ)`。

**原先写成 `zdistD r ≤ zdistD a`（即 `c = 1`）**，假设的比论文claim的弱；下游若在 `|r| ≤ 2|a|` 上用就接不上。
（作为假设，弱不会导致不一致，只会导致不够用；这和 D11 那种「假的假设」性质不同。）

## D13 · 接口常数允许依赖 `g` 与 `m`（2026-09-19，Q21）

论文说性质 5 的常数 `C_d, c_d`「depending on `d`」，性质 5' 的「depending on `d` and `κ`」。
Lean 里五条都是以 `(d, g, m)` 为参数的 `Prop`，`∃ C` 在参数之内，所以常数也可以依赖 `g` 和 `m`。
**这是有意的弱化**：作为假设，弱的版本更安全（更容易为真、更容易将来证出来），
而下游用到的只是「存在不依赖 `L, t, a, r` 的常数」这一点。若将来要求常数对 `g` 一致，
需要把 `g` 移到 `∃ C` 之后——届时再改，届时的下游签名不受影响（`PropTH` 仍是参数化的）。 〔T2127：此 Lean 声明已删，见 D277〕

## D14 · `claim:TTk` 的三种情形在 Lean 里合并成一条（2026-09-19，Q20）

论文 Appendix A.4 先把 `α` 的求和区域按 `𝛔 ∈ {0,1}^{2k}` 分成 `2^{2k}` 块 `D_{≤ℓ,𝛔}`，
再分三种情形（有 ≥2 条、恰好 1 条、0 条「短边路径」）讨论。

Lean 里 `sfT_pair_le` 把三条并成一条：多项式因子取 `|x_i−α| ∧ |y_i−α| ∧ ℓ`（**截断之后**取 min），
它同时是情形 1 中 `(eq:TtTt)` 的因子和情形 2、3 中 `(eq:KtKt)` 的因子。
于是分块与情形讨论都不出现；情形之分只决定「保留几个多项式因子」，由 `prod_wfac_le_two` 一条处理。

**这不是偏离**：结论与论文一致（常数显式），只是证明路线更短。记在这里是因为读者拿论文对 Lean 时，
会找不到 `D_{≤ℓ,𝛔}` 和那三段 `**1.** **2.** **3.**` 对应的代码——它们被合并掉了。

## D15 · A.4 的格点和不数 `D_{≤ℓ}` 的体积（2026-09-19，Q20）

论文在 `|x−α| > ℓ` 的区域里，被加项是常数 `(ℓ+1)^{-(d-2)}`，于是用 `|D_{≤ℓ}| ≲ ℓ^d` 乘上它得到 `ℓ²`。

`sum_ball_min_pow_le` 改成：`α ∈ D` 本来就保证 `|a−α| ≤ ℓ`，所以**以 `a` 为心的那份 K2 被加项**
（`(|a−α|+1)^{-(d-2)} e^{-√(|a−α|/ℓ)}`）本身 `≥ e^{-1}(ℓ+1)^{-(d-2)}`，正好盖住这个常数。
两个区域都由 `sum_radial_exp_le`（K2）付账，不需要球的基数引理。

**边界条件**：因此要求 `ℓ ≥ 1`（K2 的前提）。论文写 `0 ≤ ℓ ≤ (log W)^{10} ℓ_t`；
`ℓ < 1` 时球内只有 `α = a`，是平凡情形，没有并进来。

## D16 · 论文说的「需额外修改以处理 `d ≥ 3`」，可以在一行里说清楚（2026-09-20，Q24）

**这一条和前面的不一样**：D1–D15 记的是 Lean 相对论文的偏离，这一条记的是
**论文留白、Lean 填上了的地方**——如果作者愿意，它可以直接写回论文。

`ML:Kbound` 的证明，论文说「类似 `[YY_25]` Lemma 3.11，但**需要额外修改以处理 `d ≥ 3`**」，
没有说是哪一步。Q24 把它定位到 `(eq:ind-step-bound)` 情形 (ii).4 的那一步，就是这条不等式：

```
(|x|^{d-1}+1)^{-1} (|y|^{d-1}+1)^{-1}
    ≤ 2 [ (|x|^d+1)^{-1} (|y|^{d-2}+1)^{-1} + (|x|^{d-2}+1)^{-1} (|y|^d+1)^{-1} ]
```

在 `RBM3D/Loop/KBound.lean` 里是 `inv_pow_pair_le`，常数为 2，除 `0 ≤ x, y` 外无任何前提。

**为什么非得这样拆**：把其中一个 `(d-1)` 因子直接放大成 1（看起来更自然的对称做法）
会留下一个 `log L` 量级的和。**非对称拆分多出来的那个 `d-2` 指数，只有 `d ≥ 3` 时才有用**——
这正是 `[YY_25]` 的 `d = 1` 论证必须修改的原因。
`not_inv_pow_pair_le_single` 是机器可核的反面测试：单独一项不够。

**建议**：论文那句话后面加一行，把这条不等式写出来。读者现在只能自己猜「额外修改」指什么。

## D17 · `lam` 是论文的 `\ilambda`（印作 `g`）（2026-10-03，T2002a，DECISIONS §12；T2006 合并 0a873f1）

`Sizes d` 的字段 `lam : ℕ → ℝ` 是论文 `def:ilambda`（1_2:256）的 `\ilambda`，已合并代码一律印作 `g`。
论文正文另有 `λ` 指未缩放的耦合（1_2:253，「λ ≫ W^{d/2}」，即 `\ilambda^{-1}`）。只是命名，陈述不变。

## D18 · 随机层与终点陈述用 `L^∞` 距离，传播子层用 `ℓ¹`（2026-10-03，T2002b，DECISIONS §12；T2006）

论文固定 `L^∞`（1_2:274）；已合并的 `Defs/Lattice.lean` 固定 `ℓ¹`（D2）。`e^{-(|a|/ℓ)^{1/2}}`、`B_{t,|a|}`
带的是固定常数，所以随机层与终点陈述用新的 `zdistInf`（`L^∞`），传播子与 K-loop 层仍用 `zdistD`（`ℓ¹`）。
二者差常数 `d`：`zdistInf ≤ zdistD ≤ d · zdistInf`（`zdistInf_le_zdistD`、`zdistD_le_mul_zdistInf`，已编译）。

## D19 · 格点从 0 起编号（2026-10-03，T2002d，DECISIONS §12；T2006）

Lean 用 `ZMod (W*L)`，块 `[a] = a.val·W + {0, …, W−1}`；论文用 `⟦−WL/2+1, WL/2⟧` 与 `⟦(a(i)−1)W+1, a(i)W⟧`
（1_2:262–267）。差一个平移；模型只读块标号，所有陈述平移不变。

## D20 · 「`N` 充分大」写成沿序列 `∀ᶠ n`，并显式要求 `N → ∞`（2026-10-03，T2002e = T2001a，DECISIONS §10、§12；T2006）

论文的「provided `N` is sufficiently large」（1_2:366）在 Lean 里是尺寸序列上的 `∀ᶠ n in atTop`，
`N → ∞` 是 `Sizes.SizeTendsto`，进 `Admissible`。论文默认 `N → ∞`，没写出来。

## D21 · 流用单时刻律与网格游走表示，全体尺寸放在一个乘积空间上（2026-10-03，T2002g，DECISIONS §7、§12；T2006 部分）

论文的矩阵布朗运动 `(MBM)`（1_2:686）在 Lean 里由单时刻律 `seqHflow = √u • seqXmat` 承载；论文用停时的地方
改用 `pathP` 上的网格游走 `pathH`（独立增量；BDG 换成 Azuma 与 Doob，ST 层）。所有尺寸放在一个可数乘积空间
`seqP` 上（每个尺寸的边缘就是单尺寸的律，`seqP_map_slice`）。逐时刻的 `≺` 在 `P` 外取对 `u` 的并；论文用
`N^{-C}` 网把结论推到全体 `z`（1_2:1228），这里沿用 RBM2D 的 `NetLift`（时间）与 `RegionUnif`（谱域）（MA gate）。
本次 T2006 合并的是 `seqP`、`seqXmat`、`seqHflow`；`pathH` 随 ST 票进来。

## D22 · `G(z)` 写成 `Ring.inverse (H − z•1)`（2026-10-03，T2002h，DECISIONS §12）

`Gres`、`Mres` 用 `Ring.inverse`：全函数，可逆时等于逆矩阵（厄米 `H`、`Im z ≠ 0` 时恒可逆，
`isUnit_sub_smul_of_isHermitian`）。只是写法。

## D23 · `(G_bound)` 的 `W^τ` 统一写成 `N^τ`（2026-10-03，T2002i，DECISIONS §12；T2006）

论文 `(G_bound)`、`(G_bound_ave)` 带 `W^τ`（1_2:388–393），而它的 `≺` 带 `N^τ`（1_2:229）。钉文一律用 `N^τ`；
在 `W ≥ N^𝔠`、`W^d ≤ N` 下两者等价（`size_rpow_le_W_rpow`、`W_rpow_le`，T2006 已证）。

## D24 · 样本空间多带了几列不用的独立坐标（2026-10-03，T2006a；T2006 合并 0a873f1）

`Ω d L W`（与 `Sizes.SeqΩ`）带有 `Xentry` 不读的独立实坐标：`idxKey b < idxKey a` 的对 `(a, b, ·)`，以及对角线上的虚部
（`RBM3D/Gauss/FineModel.lean:105–111`）；论文的 `(bandcw0)` 没有这些。`X` 的律与 `(bandcw0)` 完全一致
（`integral_normSq_Xentry`、`Xmat_isHermitian`、`Xentry_swap`）。只是表示，陈述不变。

## D25 · `≺` 对任意测度与实值族定义，符号与有限性只在用到处要求（2026-10-03，T2012a；T2012 合并 9e2b00f）

`StochDomAt`、`HighProbAt`、`PerTimeDomAt`、`MomentDomAt`（`RBM3D/Defs/StochDomAt.lean`、`Gauss/DominationAt.lean`）对任意测度 `P`、
实值族定义，定义里不要求非负；论文的 `≺`（1_2:227–231）是对概率空间上的非负量。非负性只在 `refl`、`mul`、`const_mul_*` 等引理
里作为前提（`0 ≤ ζ`），矩桥接要求 `IsFiniteMeasure P`。与已合并的 `StochDom` 同一约定；用在 `seqP`（概率测度）与非负控制量上时
与论文一致。

## D26 · `lem_ConArg` 只陈述 `t < 1`（2026-10-03，T2015b；钉文 `STConArg`，`RBM3D/Induction/Defs.lean`（T2028 合并 64bdfd3））

论文 `lem_ConArg`（3_5:42–62）对流的全部时间陈述；`t = 1` 时 `η_t = 0`，界无意义。Lean 只取 `t < 1`。

## D27 · `lem:main_ind` 的时间限 `t ≤ t₀(z)`（2026-10-03，T2015c；`STMainInd`、`STStep1`（`t n ≤ lemT (z n)`））

论文 `lem:main_ind`（1_2:1256–1330）在 `zztE` 的流上把 `t` 限在 `t₀` 之前（`η_t > 0`）；Lean 显式写出 `t ≤ lemT (z n)`。

## D28 · 「小 `ε₀`」读作任意 `ε₀ > 0`（2026-10-03，T2015d；`STGbEXPii/ij/av`）

论文 `lem_GbEXP`（3_5:14–40）说对小 `ε₀`；Lean 对每个 `ε₀ > 0` 陈述（`≺` 吸收常数），强于字面。

## D29 · Step 1 对任意起点 `s ≥ 0`，时间连续性单独成陈述（2026-10-03，T2015e；`STStep1`、`STBootstrap`、`STNetLift`）

论文把 Step 1 交给 [YY_25] §5.1（3_5:64–66）。Lean 对任意 `s ≥ 0` 陈述；`u < 1/2` 处用尖锐包络；时间连续性（RBM2D `Gopboundu`）在 d ≥ 3 论文里无陈述，Lean 作为 `STNetLift` 单列。

## D30 · `(Eq:Gdecay+IND_s<g)` 只在 `g² ≤ 1 − τ` 的尺寸上（2026-10-03，T2015f；`STDecayStrong`）

论文 `(Eq:Gdecay+IND_s<g)` 只在 `1 − s ≥ g²` 时成立；Lean 的 `STDecayStrong` 把条件写进每个尺寸 `n`（不满足时空真）。

## D31 · `STStep1` 对每个 `𝔠_d ∈ (0, 10^{-2}]`，只用 (a)、(c) 与 `ML:Kbound`（2026-10-03，T2015g）

强于论文：论文 Step 1（1_2:1317–1328）在 `lem:main_ind` 的全部前提下陈述；Lean 只要 (a)、(c)、`STKbound`，且对 `(0, 10^{-2}]` 内每个 `𝔠_d` 成立。

## D32 · `STConArg` 只留 `(res_lo_bo_eta)` 的第一个界（2026-10-03，T2015h）

第二个界是确定性的 `η` 单调性，Lean 单列为 `STBctl_mono`。

## D33 · `(sum_res_2)` 带 `log L ≤ W^ε`（2026-10-03，T2016a；`EKSumDecay2`，`RBM3D/Evolution/Pins.lean`（T2022 合并 5fb7729））

论文 A.2（A_deterministic_estimates.tex:196–197）自己说用 `log L ≤ W^ε` 吸收 d = 3 的 `log L`；Lean 把它写成前提。

## D34 · `lem:sum_decay` 三条要求 `4 ≤ W^ε`（2026-10-03，T2016b；`EKSumDecay1`、`EKSumDecayNAL`、`EKSumDecay2`）

`≲` 的常数只在 `W^ε` 有下界时才能吸进 `W^{Cε}`（`W^ε ↓ 1` 时为假）；BD1 用在 `|r| ≤ |a|/2`。

## D35 · `lem:propT` 只含区间 (i)(ii)（2026-10-03，T2016c；`EKPropT`）

中间区间 `1 − t < g²/L² < 1 − u` 无下游使用，不陈述。

## D36 · `claim:TTk` 的 `D` 为任意 `ℓ`-球内集合、`ℓ ≥ 1`、`Λ²` 显式、`η_t ≍ 1 − t`（2026-10-03，T2016d；`EKTTk`）

论文 `D_{≤ℓ}`、`≺`；Lean 显式常数 `Λ²`（`Λ = (log W)^{10}` 由消费者给），`η_t` 换成 `1 − t`（`(eta)`）。

## D37 · `lem:sum_decay_nonzero` 无损、两种电荷（2026-10-03，T2016e；`EKSumDecayNonzero`）

强于论文：论文是 `≺`（含 `L^τ` 损失）且只写一种电荷；Lean 是 `C‖𝒜‖`，`C` 只依赖 `(d, n, Λ, κ)`。钉文另带 `0 ≤ s`（EK-1 钉文，已冻结），在论文的区间 `1 − λ²/L² ≤ s` 里自动成立（`λ ≤ 𝔡⁻¹`、`L ≥ 3`）。T2035 合并 c163ca8 证出此钉文（`ekSumDecayNonzero_holds`）。

## D38 · EK 钉文的常数对 `g ∈ (0, Λ]` 一致，距离用 `ℓ¹`（2026-10-03，T2016f）

`(deccA0)`、`(sumAzero)` 用周期 `ℓ¹` 距离 `zdistD`（D18：`L^∞` 的消费者把 `W^ε` 换成 `d·W^ε`）；`(sumAzero)` 取在值为 0 的指标上。

## D39 · `lem_GbEXP` 在 `Admissible 𝔠 𝔡`（含 `(eq:WO)`）下陈述（2026-10-03，T2028a；`GbEXPHypV3`、`GbEXPV3Theorem`，`RBM3D/Green/Pins.lean`（T2028 合并 64bdfd3））

RBM2D 用 `SizeTendsto → Bandwidth 𝔠`；论文 `lem_GbEXP` 是在随机带状矩阵模型的设定下（3_5:14），其前提含 `(eq:WO)`（1_2:357–363）。Lean 取 `Admissible`，常数 `𝔡` 排在 `𝔠` 之后（DECISIONS §22）。

## D40 · `(GijGEX)` 取单一取向的右端（2026-10-03，T2028b；`GijOmegaSeq`、`GijSeq`）

保留 RBM2D 的 `gexRHS … [y] [x]`（`σ = (−,+)` 那一半，3_5:24），强于论文的显示式；`stGijGEX_of_gijOmegaSeq` 推出论文形式。若 S1-16 在 d ≥ 3 只能证对称右端，再换成 `STgexRHS`。

## D41 · `(GavLGEX)` 的 `Ψ` 取 `0 ≤ Ψ ≤ N^{-a}`（2026-10-03，T2028c；`GbEXPHypV3`）

论文 `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`（3_5:27）；Lean 的条款更强（需要 S1-27 的下界），`stGavLGEX_of_v3` 取 `a = 𝔠 ε₀`。

## D42 · `RangeCond` 保留 `(E, t)` 形式（2026-10-03，T2028d）

RBM2D 的 `RangeCond`（论文无）；`v3_premises_of_stFlow` 由 `Im z ≥ N^{-1+ε}`（`δ = ε/2`，`t₀ ≥ 1/16`）推出。

## D43 · `(GiiGEX)` 的对角形式（2026-10-03，T2028e；`GiiOmegaSeq`、`GiiSeq`、`GiiGEXPT`）

这三者只界对角 `|G_pp − m|²`，论文 `(GiiGEX)`（3_5:21）界 `1(Ω)‖G_t − M‖²_max`。在 `GbEXPHypV3` 里与 `GijOmegaSeq` 合取后由 `stGiiGEX_of_omegaSeq` 推出论文形式；单独的 `GiiSeq`、`GiiGEXPT` 弱于论文显示式，只与非对角形式成对使用。逐时刻 `PrecPT` 与一致 `≺` 在这些有限指标集上等价（`asGMcSeq_iff_prec`、`gavLDetSeq_iff_prec`）。

## D44 · `GbEXPHypV3` 的无指示函数条款（2026-10-03，T2028f）

`AsGMcSeq c → GijSeq ∧ GiiSeq ∧ …`：在 `(asGMc)` 下不带 `1(Ω)` 的 `(GijGEX)`、`(GiiGEX)`，论文 `lem_GbEXP` 未显示（它只显示指示函数形式）。是 RBM2D 的读法，照移植保留；由 S1-30 的 `gbEXPV3` 证出。

## D45 · `(sum_res_2)` 要求 `L` 关于 `W` 多项式：`L^d ≤ W^K`（2026-10-03，T2042a；`EKSumDecay2`，`RBM3D/Evolution/Pins.lean`，T2042 合并 d9de66f；DECISIONS §21）

论文 A.2（A_deterministic_estimates.tex:186–190）把远处余项记成 `W^{-D+n}`；实际是 `W^{-D} L^{d(n−1)}`（`Σ_{b_i} |ΔΞ_{a_i;b_1 b_i}|` 中 `Ξ_{a_i b_1}` 一项对 `b_i` 求和得 `L^d`）。只有 `log L ≤ W^ε` 时钉文为假（T2042 预检的反例族）。Lean 加常数 `K > 0`（在 `∃ C` 之前）与前提 `(L : ℝ)^d ≤ W^K`，`C` 依赖 `K`（证明里 `C` 含 `K(n−1)`）。论文的 `(Main_DEL_COND)` `W ≥ N^𝔠` 给出 `K = 1/𝔠`，所以对论文的模型没有损失。

## D46 · `scaleFacts_R1` 在 `W^{-d}B_{t,0}` 上，前提加 `(eq:WO)`；比率事实不要 `0 ≤ s`（2026-10-03，T2045a；`RBM3D/Induction/ScaleFacts.lean`；DECISIONS §26）

RBM2D 的 R1 是关于 `M_t⁻¹ Im m` 的；本文 d ≥ 3 的控制参数是 `a_t = W^{-d}B_{t,0}`（`1_2:1108`）。Lean 的 `scaleFacts_R1` 结论为 `a_u ≤ 2 N^{-min(2𝔠𝔡, τ)}`，来自 `a_u ≤ (λ²W^d)⁻¹ + (N(1−u))⁻¹`，所以用到本文的常设假设 `(eq:WO)`（`1_2:363`）；`scaleFacts_R1_needs_WO` 编译了去掉它的反例。这不是新假设。`scaleFacts_ellT_ratio`、`scaleFacts_ellT_pow_four`（`1_2:1121`）的前提比 RBM2D 少 `0 ≤ s`。

## D47 · RBM2D 链式网格与 Step 5 近端事实不在 ST-1 移植（2026-10-03，T2045b；DECISIONS §26）

RBM2D `ChainStepCond`、`chainStepCond`（网格 `CondStInd`，指数 30）和 `scaleFacts_inv_sq_le_tailT`（2D Step 5 的 `tailT`、`ellStar`、`scaleM`）在本文的 Lean 里没有对应物。本文 `1_2:1308-1312` 的时间归纳分两段，不固定网格；链式归纳在 ST-6 按本文重写。

## D48–D56 · Steps 3–4 钉文（2026-10-03，T2041a–i；签字 §25；钉文随 T2049 入库 56c30fb，`RBM3D/Induction/Step34Pins.lean`）

- **D48（T2041a）**：`(am;asoi222)` 的控制参数在 `v ∈ [s,u]` 上取常数（依赖端点 `u`），`O(1)` 项的最大写成和，只控制出现的长度；`lem:STOeq_NQ` 右端带帽自项的上确界。
- **D49（T2041b）**：`rmk:choosechi` 的 mollifier 按性质钉（`STMollifierProps`：和为一、上界、可微、`∂_t` 界）加存在性钉文；`f_t` 里的尺度要光滑化（`ℓ_t` 有折点）。T2055 合并 6b2494e 证出存在性（`stMollifierEx_holds`，光滑化尺度 `ℓ̃_t`）。
- **D50（T2041c）**：`lem_+Q` 带 `4 ≤ W^ε` 与 `L^d ≤ W^K`（与 D45 / §21 同源：远处项有 `L^{dm}` 个）。
- **D51（T2041d）**：Steps 3–4 按区间谓词 `R ∈ {STAny, STCaseI, STCaseII}` 分别钉；一般 `(s,t)` 的陈述是组装钉文（S3-27）。
- **D52（T2041e）**：量词次序 `∀ C_d ∃ 𝔠_d`（`(eq:sumtwoloop)`、`3_5:1070`："sufficiently small depending on `C_d`"），`C_d` 取 Step 2 的指数时与 `STMainInd` 一致。
- **D53（T2041f）**：情形 (ii) 取 `A = (W^{-d}B_{s,0})⁻¹`（论文印出的 `Ψ`）；情形 (i) 取 `A = ilambda² W^d`。
- **D54（T2041g）**：`lem:SEforLn` (4) 钉的是 `(ℰ⊗ℰ)^{M,(n)} = Σ_k (ℰ⊗ℰ)^{M,(n;k)}`（`defEOTE`，`3_5:176-180`）；论文对每个 `(n;k)` 陈述，差因子 `n`。
- **D55（T2041h）**：`lem_wardineq_K` 钉在尺度 `N` 上（`STKward`），来自 KL12 的 `L^τ` 损失形式。
- **D56（T2041i）**：论文在 `lem:main_ind` 的全部假设下证 Steps 3–4；`STStep3R`、`STStep4R`、`STIngR`、`STIterR` 只取 (a) `(Eq:L-KGt+IND)` 在 `s`（`STLK`），去掉 (b)–(d)（由 `STMainInd` 携带），另加 `STKbound`（`ML:Kbound`）与 `STKward`。正文只在 `3_5:1159,1681,1902` 引用归纳假设，所以钉文比论文强、假设集不同。

## D57–D62 · 光权重层的图词汇（2026-10-03，T2050a–f；`RBM3D/Graph/LWVocab.lean`，T2050 合并 37db678；设计 §24）

- **D57（T2050a，`7_8:144`）**：系数"`m, m̄, m⁻¹, m̄⁻¹, (1−m²)⁻¹, (1−m̄²)⁻¹` 的多项式、阶 `O(1)`"在记录里只是 `coeff : ℂ`；多项式性与 `O(1)` 是使用者的前提。`m` 是 `LGraph.partition m` 的参数，`D.M x x = m`（`M = mI`，`1_2:344`）是值恒等式的前提；红权重用 `star m`（论文的 `m̄`）拆。审核观察 2：论文"非实线边的方向无关"（`7_8:151`）在 Lean 里只对对称的 `S`、`S⁺` 成立。
- **D58（T2050b，`dot-def`，`7_8:214-225`）**：(1) 内部顶点与外部顶点合并后成为外部；(2) 同一类里的两个外部顶点标签须相同，否则该项为 `0`（`PGraph.val`）；(3) 每一项有自己的顶点类型（`PGraph`）；(4) 一对顶点有多条实线边时只展开一次，没有实线边的 `×` 虚线边各展开一次（论文的"每对至多一条虚线边" `LGraph.DotWF` 记录不强制）；(5) 空族的 `max`/`min` 取 `0`/`⊤`。审核观察 1：`merge` 不去重 `×` 虚线边，所以合并后的项可以 `Normal` 而不 `DotWF`。
- **D59（T2050c，`7_8:205` 对 `7_8:215, 217`）**：`defnlvl0` (iii) 写"实线边"，`dot-def` 写"`G` 边"：这里所有非环实线边（`G`、`Ḡ`、`G−M`、`\overline{G−M}`）都算，环不计入 (iii)。
- **D60（T2050d，`7_8:172`）**："由虚线边与波浪边连成的路径"：只有 `=` 虚线边连通分子，`×` 虚线边不连（`LGraph.molGraph`）。
- **D61（T2050e，`7_8:199`）**：`defnlvl0` (i)"至多 `O(1)` 个顶点与边"对单个记录无内容，是使用者在外面量化的界。
- **D62（T2050f，`7_8:238-241`, `276`）**：`size` 取 `Ψ : ℝ`、`W, d, L : ℕ`，`W^{−d(n_W−n_V)}` 取整数次幂；"`Ψ ≥ W^{−d/2}`"写成 `1 ≤ W^d Ψ²`（`one_le_pow_mul_sq_iff` 证等价）。

## D63–D65 · LW 设计里已随词汇入库的三条（2026-10-03，T2040c、d、i；签字 §24；T2050 合并 37db678）

- **D63（T2040c）**：论文的 `Z_L^d` 只对偶数 `L` 定义（`1_2:269`，奇数"类似"）；钉文取 `3 ≤ L`，实例用 `L = 3`。
- **D64（T2040d）**：`f` 取预解式多项式（`G`、`G*` 的元素的多项式），论文写"`G` 的可微函数"（`7_8:295, 310, 335`）。
- **D65（T2040i）**：`∂_{h_{αx}}` 在 §7 未定义；取沿 `E_{αx}` 的导数（具体约定由 LW-04 = T2060 定，见其 `T2060a`）。其余 T2040a、e–h、j–o 等 LW 钉文入库时编号。

## D66–D82 · 断线期间合并的 ST-1、ST-3、LW 票（2026-10-03 补编，19:21 UTC）

- **D66（T2033a，S1-09 `Induction/Split`，aa42e43）**：RBM2D 引用的 (5.2)、(5.114)–(5.118)、(6.4)、Lemma 6.1 是 d = 2 论文的编号；本文只在 `3_5:1841` 引 (5.118)，结果是 `eq:boundtwochains`（`3_5:1842-1850`）。Lean 给的是圈层面的形式（`norm_gloop_symIdx_split_le`、`loopMax_two_mul_add_le`、`loopXi_le`），对一个确定的 `(H, z)`；到 `eq:boundtwochains` 的一步归使用者（S3-24a）。
- **D67（T2033b）**：`loopMax`/`loopXi` 是对固定的确定性 `H`、`z`，对所有符号与标号取最大；论文的 `Ξ^{(L)}_{v,m}` 是随机的（`H_v` 的圈、对 `v ∈ [s,u]` 取上确界、`≺`）。`loopXi_le` 的 `A ≥ 0` 是自由的（论文取 `A = g²W^d`）。（T2033c 只是短名 `loopMax` 在 `RBM.Ind` 与 `RBM.Gauss` 各有一个，命名空间已区分，不改名，不记 delta。）
- **D68（T2037a，S1-02 `Gauss/LoopCoordinate`，31476de）**：两条可积性引理显式带 `g`，在 `PF d L W g` 下陈述（RBM2D 无参数 `P L W`）；证明只用它是概率测度，对任意 `g` 成立。
- **D69（T2047a，S1-33 `Induction/ContinuityNet`，5b6cbc1）**：`GopboundPin` 的读法照 RBM2D 保留：前提 `0 < κ`；`u ≥ N^{-1}` 读作 `1 − u ≥ N^{-1}`；"指数小"读作对每个 `D` 都 `≤ N^{-D}`。d ≥ 3 论文没有 `Gopboundu` 的陈述（T2015e 已签）。
- **D70（T2051a，LW-15 `Graph/LWPsi`，461ae86）**：论文 `W^{-d} wT^ℓ_{t,D}(r) ≍ [sT_t(r∧ℓ)]² + W^{-D}`（`7_8:21`）在 Lean 里是 `W^{-d}W^{-D}` 代替 `W^{-D}`（`tailW = max(𝒯, W^{-D})` 没有 `W^{-d}` 因子）；带 `W^{-D}` 的下界为假。`D ↦ D + d` 后对一切 `D` 成立，论文的"任意大 `D`"不受影响。
- **D71（T2057a，S1-16 `Green/EntryDom`，a68a954）**：RBM2D→RBM3D 的常数变化（不是与论文的差别，论文只有 `≺`）：`svar_le_maxLoopPM` 等的下界常数 `2 → 4`，`diag_bound_stochDom` 的 `4320 → 8640`——剖面 `S^(B)(g)` 在 `g → 0` 时元素趋于 1，RBM2D 的权 `1/5` 不再可用。
- **D72（T2057b）**：这里是 `|E n| ≤ 2 − κ`，`GbEXPHypV3` 是 `<`（S1-30 装配时由 `<` 推 `≤`）；合并的钉文 `GijOmegaSeq`/`GiiOmegaSeq` 在 `Idx d L W` 上，块引理在 `Vtx d L W` 上，由 `offSq_le_gexRHS_fine`、`diagSq_le_maxLoopPM_fine` 桥接。
- **D73（T2058a，S3-23 `Induction/ScaleFacts3`，7c3072a）**：`hBA` 情形 (ii)（`3_5:1577-1595`，论文略去细节）以显式的 `𝔠d ≤ 1/4` 与由 `(con_st_ind)` 推出的 `Bctl < 1` 证明。
- **D74（T2058b）**：`lem:sum_decay` 的窗口 `(1−t)/(1−s) ≥ W^{-1}`（`3_5:1633-1637`）由 `(con_st_ind)` 推出，只在 `d𝔠d < 1`、`(eq:WO)` 与 `W → ∞` 下成立（编译了反例）。
- **D75（T2058c）**：`hBA` 情形 (i)（`3_5:1396`）用到 `2 ≤ d`（`L^d ≥ L²`）；论文是 `d ≥ 3`，无损。
- **D76（T2058d）**：论文"`k` 足够大"（`3_5:1431`）给成显式深度 `k_min = ⌊2 + 8𝔠d(r−1)⌋ + 1` 与常数 `Ψ ≤ (1 + 2^{𝔠d(r−1)}) A^{3/4}`（(i)）、`2A^{3/4}`（(ii)）。
- **D77（T2058e）**：在 `u = 1 − ilambda²/L²` 的分段（`3_5:1104-1105`）用严格的 `s < u`（第一段）与 `u < t`（第二段），保证两段都非空。
- **D78（T2059a，S3-05 `Induction/QopNorm`，eb6d67a）**：`lem_+Q` 衰减条款的量词次序（论文未给）：`∃ W₀`（依赖 `d, m, K, C, c, C₀, ε', D'`），`∀ W ≥ W₀`，带 `L^d ≤ W^K`；没有 `L` 的界时远处和的 `L^{dm}` 因子压不住 `e^{-cW^{ε'}/2}`。与 D50 同形。（T2059b 只引 D50：`C_n = C + 2dm + Km` 只依赖 `(d, m, K, C)`。）
- **D79（T2060b，LW-04 `Graph/LWStein`，89f29cf）**：`(Owx)` 的 `=_𝔼` 读作两边积分相等（`owx_integral`），对每个预解式多项式 `f` 与流数据 `S = u·svarF`、`z + um = −m⁻¹`（T2040e）。
- **D80（T2060c）**：Stein 恒等式用模型的方差（对角实 `S_{ww}`，非对角每个实坐标 `S/2`），`u ≥ 0`，`GaussIBP`（owed，S1-19）作前提。
- **D81（T2060d）**：`(Owx)` 的导数项是以 `α, w` 为新顶点的图；这里是两个新的外部顶点（`E ⊕ Fin 2`）；对 `α` 求和、取 `w = x` 是 LW-05…07 的步骤。
- **D82（T2060e）**：论文用 `Θ^{(+,+)}` 定义 `S⁺`（`7_8:110`；`S/(1−m²S)` 是旁注）；Lean 取任意满足 `Sp(1 − m²S) = S` 的 `Sp`，并由 `lwS_isUnit` 证 `|m|²u < 1` 时 `S(1 − m²S)⁻¹` 就是一个。

## D83–D92 · Step 2 钉文（2026-10-03，T2039a–j；签字 §28；随 T2066 入库 86124dc，`RBM3D/Induction/Step2Defs.lean`）

- **D83（T2039a）**：`lem:newKLK` 钉成确定性的：对每个 Hermitian `H`、`‖G − M‖_max ≤ δ₀`（论文：在 `(Gtmwc)` 下以高概率；`C` 来自 `prop:ThfadC`）。
- **D84（T2039b）**：`C_d`、`𝔠_d` 论文无数值；钉 `∃ C_d, ∃ 𝔠_d ≤ 10⁻²`（`C_d` 在前），编译闭合 `C_d𝔠_d ≤ 1/60`、`𝔠_d ≤ 𝔠₀`（`(eq:opt_L2)`）。
- **D85（T2039c）**：两族光权重项都作输入；`STLWB` 把 `(initialGT2)` 的控制绑到 `Ψ_t(0)`。
- **D86（T2039d）**："任意大 `D`"读作 `∀ D > 0`（`STStep2Decay`、`STLWT`、`STEMn2Exp`）。
- **D87（T2039e）**：`(eq:def_ell1)` 的尺度族在 `L` 处截断（`STScaleAdm`）。
- **D88（T2039f）**：`|·|_∞` 下的 `(TTT2)` 要自己证（合并的 `EKPropT` 是 `ℓ¹`；ST2-06b）。
- **D89（T2039g）**：`STStep2Avg` 是单电荷 `tr((G_u − M)E_a)`；合并的 `STAvgU` 是双电荷，等价（已编译）。
- **D90（T2039h）**：`STGridRepN` 里 BDG 矩界换成网格上的 Azuma–Hoeffding 尾（DECISIONS §7），损失 `N^{ε'}`、加性 `N^{-D}`、余项 `N^{C₀}Δ^{1/2}`，对所有 `k ≤ K` 同时成立。
- **D91（T2039i）**：`STContractPt` 带显式常数 `3^d` 与依赖标号的最大值（合并的 `STContract` 是 Step 3 形式）。
- **D92（T2039j）**：`STScaleAdm`/`STScaleOk` 的条款（`(eq:def_ell1)`、`(eq:monotone_Ku)`）只对大 `N` 要求（对每个层次 `m` 是 `∀ᶠ n`）；论文在固定 `N`、`W^{-d}B_{u,0} ≤ N^{-c}` 的范围内陈述。另：库里的 `STStep2` 结论是合并的 `STStep2Concl`（T2066a，与三部分形式等价，到 T2039g 为止）。

## D93–D103 · LW 钉文（2026-10-03，T2040a、e–h、j–o；签字 §24；随 T2067 入库 ed199e7，`RBM3D/Graph/LWPins.lean`）

- **D93（T2040a）**：`7_8:65` 取 `Ψ_t = (W^{-d}B_{t,0})^{1/2}`，在 `B_{t,0} < 1` 时违反 `W^{-d/2} ≤ Ψ_t`（`t = 1/2, ĝ = 1, L = 3`：0.7407）；钉成带窗口前提与常数 `C₃`。
- **D94（T2040e）**：`G_t` 的展开（`7_8:291`）钉成 `S_t = tS`、`S⁺_t = S_t(1 − m²S_t)⁻¹`、`z_t = E + (1 − t)m`。
- **D95（T2040f）**：`lem: EWGn2_N` 说"任意 `t ∈ [0,1)`"（`3_5:407`），钉在 `0 ≤ t ≤ lemT z`。
- **D96（T2040g）**：`lem:Anp_key` 的 `Ψ_t` 是 `Ψ_t(0)`（`7_8:949`）。
- **D97（T2040h）**："不妨设 `Ψ_t` 递减"（`3_5:389`）作前提（上包络保持 `(eq:Psi)`；未证）。
- **D98（T2040j）**：`∃ c` 在序列之前（`c` 只依赖 `p` 或图与常数）；Markov 一步要 `LWInteg`（有界可测，成立）。
- **D99（T2040k）**：`1 − t ≤ ĝ²/L²` 时的 `lem: EWGn2_N` 论文说"直接推论"（`7_8:20`）：要 `(LW_assm_exp)` 的类、`r ≤ L` 时 `W^{-d}T̃ ≍ B` 与子序列转移；单钉为 `LWtermExpN`（LW-16）。
- **D100（T2040l）**：`lem:Anp`（`7_8:933`）讲的是局部标准图的 `Γ^aux`；`LWAnp` 是嵌套形式（`lwanp_of_key`），`def_auxgraph` 与 `GtoAG` 归 LW-11。
- **D101（T2040m）**：`Anp_key` 是 ghost 版本的"容易推论"（`7_8:1025`）；`claim:size`（`7_8:264`）、`claim:xi`（`7_8:884`）论文无证明（LW-09、LW-11 补）。
- **D102（T2040n）**：`lem:LWterm_EXP`（`6:83`）的前提范围"(Gt_bound_flow)–(Eq:Gdecay_flow)"读作 `t` 时刻的 `STLocalEntry`、`LWAvgLaw`、`STLmax`、`STLK`、`STDecay`（`(Eq:Gdecay_w)` 由 `(Eq:Gdecay_flow)` 推出）。
- **D103（T2040o）**：`7_8:20-91` 的约化（`LWReduceB/T`）与分段（`LWtermExpS/N`）不是论文编号陈述；`LWedgeExp` 写 `k₁ + 1` 代替论文的 `k₁ ≥ 1`。另（T2067a）：三条展开式钉在固定尺寸的 `PF d L W g` 上，合并的 Stein 层（`owx_integral`）在 `Sizes.seqP` 上、带 `GaussIBP sz`、`0 < u`；LW-05 要单独处理 `t = 0` 并在两个空间之间搭桥。

## D104 · `Step1NetLift` 去掉不用的参数（2026-10-03，T2062a；S1-34 `Induction/Continuity`，a51b69e）

`Step1NetLift`（`Continuity:1261`）比 RBM2D 少了 `c`、`Bandwidth d c`、`CondStInd d E s t`（证明不用，RBM2D T2070b），并把 `Step1LoopPT/Unif`、`Step1WeakLawPT/Unif`、`RangeCond` 读作合并的 `STStep1LoopPT/Loop`、`STStep1WeakPT/Weak`、`Sizes.RangeCond`。没有加前提。`stNetLift_holds : STNetLift d` 证出，`STNetLift` 的 owed 行可删（清理票）。

## D105 · Ward 恒等式只移植一个符号组合（2026-10-03，T2063a；S1-31 `Induction/ConArgDet`，bbd22a5）

`sum_gloop_ward_last_div`、`sum_gloop_ward_last` 是 `WI_calL`（`1_2:1036-1042`，对 `σ₁ = −σ_n` 的两种次序都成立，右边为 `(2i W^d η_t)⁻¹(𝓛^{(n-1),+} − 𝓛^{(n-1),−})`）在 `σ₁ = +`、`σ_n = −` 时的特例，`η_t` 写作 `Im z`（`z = z_t`，`etaT_eq_zt_im`）。`σ₁ = −`、`σ_n = +` 的情形没有移植（同 RBM2D）。是特例，不是一般陈述。

## D106 · `lem_ConArg` 拆成确定性部分与概率部分（2026-10-03，T2063b；S1-31 `Induction/ConArgDet`，bbd22a5）

`Induction/ConArgDet` 是 `lem_ConArg`（`3_5:42-57`；论文的证明 `3_5:60` 说与 [YY_25] 引理 5.1 "完全相同"）的确定性部分：对固定的厄米矩阵 `H` 证 (6.3)–(6.12)，常数 `C_m = m+1`；Ward 引理对一般矩阵 `H`（带 `IsUnit` 前提）陈述，比 `G_t` 更一般。概率陈述（钉文 `STConArg`）归 S1-32。`t < 1` 的限制见 D26。

## D107 · 波动平均的行权用有界权（2026-10-03，T2061a；S1-17 `Green/FlucVanish`，40f70b9；DECISIONS §30）

行权 `j ↦ S_ij` 在 Lean 里陈述为 `BoundedWeight`：在 `i` 所在块及其 `2d` 个邻块共 `(2d+1) W^d` 个点上 `0 ≤ t ≤ W^{-d}`，其余为 `0`，`Σ t ≤ 1`。RBM2D 用 `UniformWeight`（支撑上取同一值），在 `d ≥ 3`、`g² ≠ 1` 时为假（`not_uniformWeight_svarF`）。论文没有单列这条引理；块平均 `W^{-d} 1(k ∈ 𝓘_a)` 仍是 `UniformWeight`。

## D108 · 圈流 Stein 层带参数 `g`（2026-10-03，T2064a；S1-05 `Gauss/LoopFlowStein`，06429ba）

关于律的七条陈述带额外参数 `g`，在 `PF d L W g` 下陈述（理由同 D68 = T2037a）；证明只用 `PF d L W g` 是概率测度、边缘为 `gaussianReal 0 (gvarF d L W g c)`（对每个 `g`）。

## D109 · 圈流 Stein 层的记号（2026-10-03，T2064b；S1-05 `Gauss/LoopFlowStein`，06429ba）

`blockMat d L W (Xmat d L W ω)` 代替 RBM2D 的 `(Xmat ω).submatrix …`（`rfl` 相等）；`spectralWordBound d W`、`driftA`、`driftD` 显式带 `d`。只是记号。

## D110 · 第二圈收缩系数 `W^d` 与参数 `g`（2026-10-03，T2065a；S1-04 `Hierarchy/ContractionSecondLoop`，64a33ea）

13 个 RBM2D 文件里的 17 个收缩系数 `W^2` 都换成 `W^d`（与合并的 `sum_allCoords_trace_blocks` 一致，T2032）；陈述带 `svarF`/`SB` 的实参数 `g`（RBM2D 没有）。论文的系数正是 `W^d`（`(eq:variancematrix)`）。

## D111 · `ContractionSecondLoopReverse` 未移植（2026-10-03，T2065b；S1-04，64a33ea）

没有消费者，故未移植；后面的票若要 `coordinateSecondWordDeriv_two_edges`，需另行申请。

## D112 · `(eq:Sigma-empty-sum-zero)` 第二个估计在 Lean 内证出（2026-10-03，T2070a；KL8+9 `Loop/KLMolecule`，eaf0614）

论文（`A_deterministic_estimates.tex:731`）写 `OO(ilambda² + |1-t|)` 并引 [RBSO1D] Claim 4.30（"与维数无关"）。Lean 在 `d ≥ 3` 由 `(prop:ThfadC_short)` 与带符号估计证出：`∑_{δ_0=x}|Σ^{(∅)}(σ^{alt},δ)| ≤ C(g² + (1-t))`，`C = C(d,n,κ,gmax)`，对每个 `0 < g ≤ gmax`、`|E| ≤ 2-κ`、`t ∈ [0,1)`、`L ≥ 3`、`W ≥ 1`、`n ≥ 4` 偶数成立。所以 [RBSO1D] Claim 4.30 不再是外部输入。

## D113 · 分子衰减与和为零的常数显式化（2026-10-03，T2070b；KL8+9，eaf0614）

`(eq:molecule-decay)`（`:691`）与 `(eq:Sigma-empty-sum-zero)` 带符号估计里论文的"某些常数 `c, C`"和 `OO(|1-t|)` 在 Lean 里是显式的，依赖 `(d, n, κ, gmax)`（体内 `|E| ≤ 2-κ`、`g ≤ gmax`）；分子衰减率 `c = c_κ/2`。其余与论文相同。K-圈模型限于带状/`Theta` 传播子、和为零钉文要 `n ≥ 4` 偶数、层 `π = ∅`：沿用 T2004 探针钉文，不是本票新增。

## D114 · Step 2 核心的命名空间（2026-10-03，T2071a；ST2-02 `Induction/Step2Core`，092aaf0）

探针 §3–§7 原在 `RBM.Probe.T2039`（§8 在 `RBM.Gauss.Sizes`），入库后都在 `RBM.Gauss.Sizes`。探针 §9–§12 在 `RBM.Probe.T2039` 下并 `open RBM.Gauss.Sizes`；后面搬它们的票在 `RBM.Gauss.Sizes` 里找这些名字。只是记号。

## D115 · 探针的 `ST2_Bctl_*` 即合并的 `STBctl_*`（2026-10-03，T2071b；ST2-02，092aaf0）

探针 `ST2_Bctl_pos`/`ST2_Bctl_mono`（探针 1738、1748 行）就是合并的 `STBctl_pos`/`STBctl_mono`；探针 2723、3013、3091、3821、3905、4696、4697、4704、4706 行用到它们，后面搬 §9–§12 的票要改名。

## D116 · `hsmall` 的指数 `1/30` 要求 `W` 很大（2026-10-03，T2071c；ST2-02，092aaf0）

`hsmall` 里的 `b^{1/30}` 要 `b < 6^{-30}`，即 `W^3` 约 `2.2·10^{23}`；所以实例取 `n = 100`，不取小 `n`。`ST_good_engine` 逐 `n` 成立（不带 `∀ᶠ`）。论文对应处只说"`W` 足够大"。

## D117 · 一步生成元带参数 `d`、`g`（2026-10-03，T2072a；ST2-20 `Path/OneStep`，593e519）

`genMat`、`OneStepEnvelope`、`loopDrift`、`DriftLip_eGterm`、`norm_loopDrift_sub_le` 加参数 `d` 与 `g`，`envConst`、`driftLip` 加 `d`（RBM2D 隐含 `L W`，方差剖面是固定的五点剖面，没有 `g`）。陈述对每个实数 `g` 成立，常数不含 `g`。

## D118 · 树方程右端用 `treeEqRhs d L W g`（2026-10-03，T2072b；ST2-20，593e519）

`Loop.treeEqRhs d L W g`（权 `W^d`、`S^{(B)}(g)`，论文 `1_2:990` `(pro_dyncalK)`）代替 RBM2D 的 `KLoop.primRhs`（权 `W^2`），`mSigma` 代替 `KLoop.mSig`；改名后陈述相同。

## D119 · 单位球点数对所有 `L` 证出，不加 `3 ≤ L`（2026-10-03，T2072c；ST2-20，593e519）

不加 `3 ≤ L` 前提（RBM2D 也没有）。`d ≥ 3` 的证明要 `Z_L^d` 的单位球至多 `2d` 个点（对每个 `L ≥ 1`），在本文件内私有证出（`OneStep_card_sphere_le`）；合并的邻点计数只对 `3 ≤ L`。

## D120 · `stepDecomp` 的观测量类 `HermTestFun`（2026-10-03，T2073a；ST2-22 `Path/StepDecomp`，a262beb）

观测量通过类 `HermTestFun`（`C²` 且在厄米点有界）进入 `stepDecomp`，另加沿厄米方向 `fderiv²` 的前提 `hC₂`；论文对预解式多项式的 Taylor 展开不写这样的类。沿用 RBM2D T2076a，本票未对照论文 TeX 核对。

## D121 · `stepDecomp` 余项的粗矩界（2026-10-03，T2073b；ST2-22，a262beb）

矩界 `E‖X‖² ≤ 16 N⁴`、`E‖X‖⁴ ≤ 768 N⁸` 是只为余项可积性用的粗多项式界，不是论文的陈述。

## D122 · `Step2NetLift` 去掉不用的参数（2026-10-03，T2074a；ST2-18 `Path/NetLift1`，06b49b2）

RBM2D `Step2NetLift` 的 `Bandwidth d c` 与 `CondStInd d E s t` 证明不用，去掉（同 D104 = T2062a、RBM2D T2070b 对 Step 1 的处理）。

## D123 · `Step2NetLift` 带 `sz.WO 𝔡`（2026-10-03，T2074b；ST2-18，06b49b2）

`Step2NetLift` 带 `sz.WO 𝔡`（RBM2D 的控制没有 `ĝ`，所以没有）；`stNetLift2_part1` 从 `STFlow`（`Admissible`）取得它，钉文不变。

## D124 · `stNetLift2_part1` 只是衰减那一项（2026-10-03，T2074c；ST2-18，06b49b2）

`stNetLift2_part1` 只证 `STNetLift2` 的衰减合取项（前提只用 `STStep2DecayPT`）；`STStep2Local ∧ STStep2Avg` 归 ST2-19（T2082），由它闭合 `STNetLift2`。

## D125 · `ConArgPin` 允许 `k ≥ 1`、`C₀ ≥ 0`（2026-10-03，T2076a；S1-32 `Induction/ConArg`，8a8cfeb；说明性）

`ConArgPin`/`conArg` 陈述 `k ≥ 1`（论文 `lem_ConArg` 为 `n ≥ 2`，钉文 `STConArg` 保留 `k ≥ 2`）并取 `0 ≤ C₀`；`k = 1` 时界为 `Y_1 ≤ C₀`（基础情形）。对钉文不构成差别。`STConArg` 本身与论文的差别已记在 D26（`t < 1`）、D32（只留第一个界）。

## D126 · `ConArgPin` 的时间前提 `c ≤ s`（2026-10-03，T2076b；S1-32，8a8cfeb；说明性）

前提 `c ≤ s`（论文 `ε ≤ s`）代替 RBM2D 的 `c < t_1`；合并的 `ztTilde_arith`（T2063）取 `c ≤ t_1`。

（T2075 = ST2-06b `Evolution/PropTInf`，a84c579：无 paper-delta。合并的 `propT`/`EKPropT` 用 `ℓ¹` 距离 `zdistD`，论文的 `|·|` 是 `L^∞`（`1_2_Intro_model_result.tex:274`），`EKPropTInf` 就是论文的陈述。）

## D127 · 圈生成元带参数 `g`（2026-10-03，T2077a；S1-06 `Gauss/LoopGenerator`，3b98b27）

关于 `PF d L W g`、`SB d L g` 的每条陈述都带显式参数 `g`（同 D108 = T2064a）。

## D128 · 圈初值与邻块权的指数（2026-10-03，T2077b；S1-06，3b98b27）

`adjacentBlockWeight_three` 的值为 `((W⁻¹)^d)^2 = W^{-2d}`（RBM2D `W^{-4}`）；`initialLoopValue_all_same` 的指数为 `d·(n-1)`；`initialLoopValue_two_edges` 的权为 `W^{-d}`。与 `eq:initial_K`（`M^{(k)} = W^{-(k-1)d}∏m(σ_i)1(a_1=…=a_k)`）一致。另：票里点名的 `sum_norm_integral_pairCutIntegrand_le`、`expected_gloop_hierarchy_integral_unconditional` 依赖 RBM2D 上游已删的死代码，未移植（DECISIONS §31）。

## D129 · 方差剖面行支撑的方向与大小（2026-10-03，T2078a；S1-18 `Green/LDE`，7c7652e）

行支撑写成 `{j : blk j - blk i ∈ flucVanish_sbSupport d L}`（与 `boundedWeight_svarF` 同向；RBM2D 为 `blk i - blk j`，因支撑对称而是同一集合），大小 `(2d+1) W^d`（RBM2D `5 W²`）。

## D130 · 方差剖面对角元带 `g`（2026-10-03，T2078b；S1-18，7c7652e）

`svar d L W g i i = W^{-d}(1 + 2dg²)⁻¹`，对每个实数 `g` 为正（RBM2D 为 `1/(5W²)`，无耦合参数）。

## D131 · 波动平均的有界权形式（2026-10-03，T2078c；S1-18，7c7652e）

新增 `LDE_norm_flucAvg_le_of_boundedWeight`：`norm_flucAvg_le` 的 `BoundedWeight` 形式（依 D107 = T2061a，DECISIONS §30），RBM2D 无对应。

## D132 · Step 2 局部网提升去掉不用的参数并改控制（2026-10-03，T2082a；ST2-19 `Path/NetLift2`，efeda82）

`Step2LocalNetLift` 去掉 RBM2D 的 `c`、`Bandwidth d c`、`CondStInd d E s t`（证明不用，同 D104、D122）；`Step2LocalUnif` 的形式就是合并钉文 `STStep2Local`（平方项，`d ≥ 3` 时控制为 `STWB_{u,|[x]-[y]|}`，代替 `M_u^{-1/2}`）。

## D133 · `STStep2Avg` 的网提升是新增（2026-10-03，T2082b；ST2-19，efeda82）

`STStep2Avg` 的提升在 RBM2D 没有对应（`d ≥ 3` 新增）；`(Gt_avgbound_flow)` 的网提升用 `1_2:1400` 的标准论证，对象是 `‖𝓛^{(1)}_{u,+,a} − m(E)‖` 对 `Bctl`。

## D134 · 局部与平均提升不需要 `(eq:WO)`（2026-10-03，T2082c；ST2-19，efeda82）

Local/Avg 两项提升不需要 `(eq:WO)`，而 `step2NetLift` 需要（D123）；Local/Avg 的控制不含 `ℓ_u`。`stNetLift2_holds : STNetLift2 d` 证出，`STNetLift2` 的 owed 行可删（清理票）。

## D135 · 尺度族取"一个解"而非"唯一正解"（2026-10-03，T2081a；ST2-05 `Induction/Step2Scale`，6e7bb9c）

论文（`(eq:def_ell1)`，`3_5:570-571`）取"唯一正解 `K'_u`"；Lean 的 `st2sStep` 取 `𝒯_u(r) = q 𝒯_u(K)` 的一个解 `r ≥ K`，在 `L` 处截断（`min r L`；论文以 `𝒯̃^K ≍ 𝒯̃^L` 的说明处理 `K_u ≥ L`），无解处（`n < n₀`）保持 `K`。唯一性未证（不需要）。`L` 处截断见 D87，对大 `N` 才要求的条款见 D92。

## D136 · 地板步数 `M(D)` 的依赖（2026-10-03，T2081b；ST2-05，6e7bb9c）

钉文把 `M(D)` 留作 `∃ M`；文件里 `M(D) = 6⌈(2+D)/c₀⌉`，`c₀ = min(2𝔠𝔡, ε/2)`，依赖 `𝔠, 𝔡, ε`，不只依赖钉文文档串所写的 `(D+d)/c`（钉文陈述不变，只是文档串措辞）。

## D137 · 上限 `K ≤ (log W)^{10} ℓ_u` 对每个 `m` 逐个成立（2026-10-03，T2081c；ST2-05，6e7bb9c）

钉文的上限对固定的 `m` 成立，`n₀` 依赖 `m`（钉文是 `∀ m` 之后 `∀ᶠ n`）；不声称对 `m` 一致。`stScaleExists_holds : STScaleExists d` 证出，`STScaleExists` 的 owed 行可删（清理票）。

## D138 · `Step1TargetV3` 的 d 维形式（2026-10-03，T2079a；S1-35 `Induction/Step1Setup`，4f186cf）

d 维形式是 `STGbEXPii d → STGbEXPij d → STStep1 d`；RBM2D 的 `GbEXPHypV3 d (κ/2) c τ` 针对一条尺寸序列和固定的 `c, τ`，钉文则对所有 `κ ε 𝔡 ε₀` 量化；`STGbEXPav` 不用。

## D139 · Step 1 的维数常数（2026-10-03，T2079b；S1-35，4f186cf）

`s1_near_card ≤ 3^d`（`zdistInf` 球；票面写的 `2d+1` 不对）；`s1_gexRHS_le` 为 `2·9^d B + W^{-d}`（RBM2D `25 B + W⁻²`）；`s1_wl_det` 为 `(2·9^d+1) N^{2τ} g`（RBM2D `26`）；`C_d = 2·3^d`（RBM2D `6`）。

## D140 · `S1Std` 的新字段与 `𝔠_d` 的范围（2026-10-03，T2079c；S1-35，4f186cf）

新增字段 `hWO`（参 D46 = T2045a）、`h𝔠d`、`h𝔠d'`；RBM2D `CondStInd` 的指数 `30` 即 `STConStInd` 的参数 `𝔠_d`；`s1_ratio_ev` 需 `𝔠_d ≤ 1/15`（钉文取 `1/100`，满足）。

## D141 · Step 1 在 `u < 1/2` 区间的处理（2026-10-03，T2079d；S1-35，4f186cf）

`‖𝓛‖ ≤ (2/c₁)^k (W^{-d})^{k-1} ≤ C a_s^{k-1}`，`C = (2/c₁)^k (𝔡⁻²+1)^{k-1}`，需 `0 ≤ s` 与（最终）`ilambda ≤ 𝔡⁻¹`；RBM2D 的 `M_u ≤ W²` 在 d 维无对应。

## D142 · 常数 `c' = c₀/8`（2026-10-03，T2079e；S1-35，4f186cf）

`F5` 的 `c' = c₀/8`（RBM2D 用 `W² ≤ N` 得 `c₀/4`），对每个 `d ≥ 1` 成立。

## D143 · ST-2 ↔ LW 两座桥带 `3 ≤ d`（2026-10-03，T2080a；ST2-03 `Induction/Step2Events`，7f9bfa1；DECISIONS §31）

`STLWB_of_LWterm`、`STLWT_of_LWtermExp` 带 `(hd : 3 ≤ d)`：Step 2 钉文 `STLWB d`、`STLWT d` 没有 `3 ≤ d` 前提，`LWterm d`、`LWtermExp d` 有（论文的 `lem:LWterm`、`lem: EWGn2_N` 本就只对 `d ≥ 3`）。

## D144 · `STLWB` 的控制 `Ψ` 的绑定（2026-10-03，T2080b；ST2-03，7f9bfa1）

`STLWB` 把 `(initialGT2)` 的控制绑到 `Ψ_t(0)`，`LWAssm` 单独取 `Ψ'`；桥取 `Ψ' = max(Ψ_t(0), W^{-d/2})`，因为 `LWWindow` 不带常数而 `STPsiClass` (3) 带常数。

## D145 · 实数 `ℓ` 与自然数 `r` 的对接（2026-10-03，T2080c；ST2-03，7f9bfa1）

`Φ_t(r) = Ψ_t(⌊r⌋₊)`（`LWPsiRel` 对 `ℓ ∈ ℝ` 陈述，`STPsiClass` 对 `r ∈ ℕ`），常数 `C₁' = C₁ 2^{C₂}`。

## D146 · 第二座桥在有限个 `n` 处改 `ℓ_n`（2026-10-03，T2080d；ST2-03，7f9bfa1）

`STLWT` 是 `∀ᶠ n`，`LWAssmExp` 是 `∀ n`；桥在有限个 `n` 处改动 `ℓ_n`，不影响结论。

## D147 · 探针 §10 三条声明并入 `Step2Events`（2026-10-03，T2080e；ST2-03，7f9bfa1；DECISIONS §31）

接 D114、D115：命名空间 `RBM.Gauss.Sizes`，`ST2_Bctl_pos` 即 `STBctl_pos`；`STScaleInv`、`ST_STprof_pos`、`ST_card_lab_le`（探针 §10）现在在 `Step2Events.lean`，ST2-04 导入。只是记号。

## D148 · 登记新增 `STStep1Weak`、`STScaleInv`（2026-10-03，T2080f；ST2-03，7f9bfa1）

`STStep1Weak`、`STScaleInv` 加入 owed 登记；`STLWB`、`STLWT`、`STGoodAt` 的登记注释更新。登记事项，非论文差别。

## D149 · ST2-21 的漂移代数只做 `n = 2`、`σ = (+,−)`（2026-10-03，T2083a；ST2-21 `Path/LoopStep`、`Path/DriftAlgebra`，07ede19）

`KpmODE`、`LoopGenN2`、`HierarchyN2` 是 `(pro_dyncalK)`、`(eq:mainStoflow)`、`(LK_SDE)` 在 `n = 2`、`σ = (+,−)` 的特例，不是一般 `n`、一般 `σ` 的陈述；并在 `g = sz.lam n` 处陈述（矩阵层核心 `DriftAlgebra_loopGen_core` 私有，对每个实数 `g` 成立）。ST2-28a（`HierAlgebra`、`HierarchyN`）须沿用这一 `∀ sz n` 形状与合并的 `ST*` 词汇。

## D150 · ST2-21 用合并的 `ST*` 词汇（2026-10-03，T2083b；ST2-21，07ede19）

RBM2D 的 `Kpm`、`lkMat`、`LLpair`、`EGt`、`ELKLK`、`thetaGen` 换成合并的 `ST*` 项；`STELKLKM` 的下标次序为 `LK(x,a₂) S_{xy} LK(a₁,y)`。只是陈述形状，无数学差别。

## D151 · `condExp_loop_drift` 的界（2026-10-03，T2083c；ST2-21，07ede19）

`condExp_loop_drift` 的界为 `envConst · Δ^{3/2}`（合并的 `oneStepEnvelope`），不经 RBM1D 的 `loopDrift`/`zMotionLip`/`genPtLip`（同 RBM2D）；前提 `_hK`、`_hk` 未用。

## D152 · 二次变差层带耦合 `g`（2026-10-03，T2084a；ST2-23 `Path/QVIdentity`，fe32346）

`S^{(B)}(g)` 的耦合 `g` 是 `EE`、`EECutIdentity`、`QVPropagated`、`EEShift` 的参数（RBM2D 无耦合）；`v_gradMat_eq_quadVar` 的 `gvarF` 取在 `sz.lam n`。

## D153 · `loop6`、`EE` 等在 `RBM.Path` 里（2026-10-03，T2084b；ST2-23，fe32346）

`loop6`、`EE`、`cutDeriv1`、`cutDeriv2`、`loopDeriv` 公开在本文件的 `RBM.Path` 里，不在 `Step2Defs.lean`；用到它们的 ST2-26、ST2-28 须导入 `RBM3D.Path.QVIdentity`。流程事项。

## D154 · `(𝓔⊗𝓔)` 并不字面上就是鞅项的二次变差（2026-10-03，T2084c；ST2-23，fe32346；审核第 1 轮）

论文（`3_5:166`，`defEOTE` `3_5:166-190`）称 `(𝓔⊗𝓔)` 为"`def_Edif` 中鞅项的二次变差"，但它字面上不是。Lean 证的是：(i) 逐切口恒等式 `EECutIdentity`：`(𝓔⊗𝓔)_{a,a'} = Σ_c S_c Σ_{k=1,2} ∂^{(k)}_c𝓛_a · conj ∂^{(k)}_c𝓛_{a'}`（无 `k ≠ k'` 的交叉项）；(ii) 界 `QVPropagated`：`Σ_c S_c |Σ_b κ_b ∂_c𝓛_b|² ≤ 2 Re Σ_{b,b'} κ_b κ̄_{b'} (𝓔⊗𝓔)_{b,b'}`（因子 `2 = n`）。`d = 3` 的见证（`M = 0`、`u = 0`、`E = 0`，`z = i`，`a = a'`）：二次变差为 `0` 而 `(𝓔⊗𝓔)_{a,a} > 0`，故两者不相等。参 D54（`lem:SEforLn` (4) 的因子 `n`）与 RBM2D delta #22 的更正（T2049e）。论文的用法只需要 (ii) 的不等式，结论不受影响；措辞应改为"控制二次变差"。

## D155 · `EE` 只在 `n = 2`、`σ = (+,−)`；`EEShift` 是 Lean 独有（2026-10-03，T2084d；ST2-23，fe32346）

`EE` 只是 `defEOTE` 在 `n = 2`、`σ = (+,−)` 的情形（两个切口 `k = 1, 2`）；论文对所有 `n`、`σ ∈ {+,−}^n` 定义并取 `max_σ`（`eq:MG_nloop`，`3_5:1043`）。`EEShift`（`‖EE(u+Δ) − EE(u)‖ ≤ 16 N² η_{u+Δ}^{-7} Δ`，`N = (WL)^d`）是 Lean 独有的时间离散化界，论文无对应陈述。

## D156 · 二次大偏差在 Lean 内证出（2026-10-03，T2088a；S1-19 `Green/IBPPoly`，3b8c687）

论文引 [YY_25, Lemma 4.2] 取二次大偏差 (4.7)；这里 `stochDom_ldeQuad` 对高斯流证出（陈述 `hLquad`，常数 `hwConst q`，门槛 `N^{τ(q+1)-D}`），所以调用方用上此定理后，`diag_bound_stochDom` 的 `hLquad` 不再是输入。其它陈述不变。

## D157 · `GaussIBP` 证出（2026-10-03，T2088b；S1-19，3b8c687）

`GaussIBP sz`（登记为 owed，`Test/Axioms.lean:90`）现在是定理 `gaussIBP`；登记行多余，清理票删。`Tame.integrable`、`RowChaos.mom_le_momVpow`、`RowChaos.integrable_norm_pow` 现在可直接用 `gaussIBP sz`。

## D158 · 演化核带传播子参数（2026-10-04，T2085a；ST2-24 `Path/Kernel`、`Path/StepDecompLoop`，e88681b）

`ukerMat`、`Uop`、`UopSemigroup`、`uopSemigroup` 与 `Uop_*` 引理显式带传播子参数 `(d, L, g)`（RBM2D 只带 `L`）；模型处 `g = sz.lam n`。数学不变（`def_Ustz`）。

## D159 · 一步分解的 `W^{-2d}` 与常数（2026-10-04，T2085b；ST2-24，e88681b）

`hermTestFun_loopPM`、`stepDecomp_loopPM` 的证明用 `W^{-2d}`（RBM2D `W^{-4}`）；所陈述的 `C₂ = 6 N η⁻⁴` 中 `N = (LW)^d`。

## D160 · 私有副本 `StepDecompLoop_ukerNonneg`（2026-10-04，T2085c；ST2-24，e88681b）

`StepDecompLoop_ukerNonneg`（私有）重复 RBM2D `Path/UBounds`（ST2-25）的内容；ST2-25 移植后可替换，无公开名依赖它。流程事项。

## D161 · 演化核只做 `n = 2`（2026-10-04，T2085d；ST2-24，e88681b；审核第 1 轮）

`ukerMat`（`Kernel.lean:46`）、`Uop`（`:51`）、`UopSemigroup`（`:56`）、`uopSemigroup`（`:173`）与 `Uop_*` 引理（`:108–:311`）只把 `(def_Ustz)`（`DefTHUST`，`3_5:108–118`）的演化核 `𝒰^{(n)}_{s,t,σ}` 形式化到 `n = 2`，两个下标槽用同一个标量 `ξ`（即 `σ = (+,−)`，用处 `M^{(+,−)} = |m|²`）；论文对每个 `n ≥ 2`、`σ ∈ {+,−}^n` 定义，每个槽各用 `M^{(σ_i,σ_{i+1})}`。

## D162 · Duhamel 只有离散代数部分（2026-10-04，T2085e；ST2-24，e88681b；审核第 1 轮）

`Uop_duhamel_telescope`（`Kernel.lean:292`）、`Uop_duhamel_telescope_stopped`（`:311`）与抽象的 `duhamel_telescope`（`:193`）、`duhamel_telescope_stopped`（`:236`）是离散网格上的伸缩和 `A_m = 𝒰_{u_0,u_m}A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m}(A_{j+1} − 𝒰_{u_j,u_{j+1}}A_j)`（对任意序列 `A`）；论文的 `(int_K-L_ST)`、`(int_K-LcalE)`（`Sol_CalL`，`3_5:134–147`）是连续时间的 Duhamel 公式，带各类积分项与鞅项 `d𝓔^M`。Lean 这里只有代数（半群）部分。

## D163 · 一步分解是 Lean 独有的时间离散陈述（2026-10-04，T2085f；ST2-24，e88681b；审核第 1 轮）

`stepDecomp_loopPM`（`StepDecompLoop.lean:692`）与 `stepDecomp_Z_subG_loopPM`（`:788`）是时间离散化的 Lean 独有陈述（一步 `ξ_b = Z_b + Y_b`、`Ab` 可测、路径界、`Y_b` 条件均值为零、`L²` 项 `stepDecomp_Y_sq`、`1_S Z_b` 条件次高斯）；论文无此陈述。权 `Σ_a U b a` 代替 `Σ_a |U b a|`，需 `0 ≤ v ≤ w < 1`。

## D164 · `lem: newPQ` 证明在 `i = n` 处的循环处理（2026-10-04，T2086a；S3-03 `Induction/NewPQ`，f28fd9c）

论文 `lem: newPQ` 的证明（`3_5:1866-1886`）写 `(y2ussz)` 时的集合 `A_(i)` 与删去位置 `i` 的写法默认 `i < n`；`i = n` 时（循环，`σ_{n+1} = σ_1`）删去的是 `σ_n`、替换的是 `σ_1`；印出的 `σ_± = (σ_1 … σ_{i-1}, ±, σ_{i+2} …)` 只在循环旋转意义下是同一个圈。Lean 的 `npqSg` 从 `i + 1` 起循环列出位置。论文措辞小疏漏，结论不变。

## D165 · `ι_α` 是旋转后的复合（2026-10-04，T2086b；S3-03，f28fd9c）

Lean 的标签 `ι_α` 是 `ρ^(i+1) ∘ castSucc` 的复合（循环旋转，非递增）；论文的 `ι` 是保序嵌入。钉文只用 `a ∘ ι_α`，陈述不变。

## D166 · Ward 恒等式的另一符号与循环不变性（2026-10-04，T2086c；S3-03，f28fd9c；补 D105）

`(WI_calL)` 在 `σ₁ = −` 的情形与 `𝓛` 的循环不变性在本文件私有证出（`npq_loopL_ward`、`npq_loopL_rotate`）；若别的票需要，清理票可把它们移到 `ConArgDet.lean` 作公开引理。`stNewPQ_holds : STNewPQ d` 证出，`STNewPQ` 的 owed 行可删（清理票）。

（T2089 = S1-20 `Green/FlucIter` 前半，55f611e：无 paper-delta。）

## D167 · `STK2decay` 文档串里的 `c_d` 不需要（2026-10-04，T2093a；ST2-06 `Induction/Step2K2`，0fc2597）

钉文文档串（`Step2Defs.lean:564-567`）说 `ℓ¹` 与 `L^∞` 距离之差"只在指数里花一个常数 `c_d`"；证明只用 `zdistInf ≤ zdistD`（无 `c_d`，也不用把 `𝒯` 加倍）。陈述不受影响。

## D168 · `Prop5Decay` 已证，文档串过时（2026-10-04，T2093b；ST2-06，0fc2597）

文档串与票都称 `Prop5Decay` 为借用钉文；它已证出（`prop5Decay_holds`，`Propagator/Prop5Hold.lean:784`）。`STK2decay` 文档串过时（`Step2Defs.lean` 文件头已说明探针文档串的这一点）。

## D169 · `(eq:kn2sol_decay)` 与 `(eq:simpleboundK)` 的两种形式（2026-10-04，T2093c；ST2-06，0fc2597）

论文 `(eq:kn2sol_decay)`（`3_5:457`）是 `𝒦^{(2)}_{u,(-,+),(a₁,a₂)} ≺ W^{-d} B_{u,|a₁-a₂|}`，`(eq:simpleboundK)`（`3_5:518`）是 `𝒦^{(2)}_{u,σ,a} ≺ W^{-d} 𝒯̃^L_{u,D}(|a-b|)`，都对确定量用 `≺`。钉文对四个 `σ` 以显式常数 `C` 陈述第二种（无 `N^ε` 损失；`|·|` 为 `zdistInf`，见 T2002b）。只含 `B` 的形式由 `‖Θ‖ ≤ C 𝒯_u(r) ≤ C B_{u,r}`（`k2d_theta_tail`）得到，但没有单独的 Lean 陈述。`stK2decay_holds : STK2decay d` 证出，`STK2decay` 的 owed 行可删（T2093d，清理票）。

## D170 · Step 3 的 `Ψ` 演算在 `d ≥ 3` 重述（2026-10-04，T2087a；S3-24a `Induction/IterationsA`，6583ca2）

RBM2D `Induction/Step3.lean:1-777` 是 `d = 2`；`d ≥ 3` 的 `Ψ` 为 `A^{3/4} + ρ^{n-1} A^{1-k/8}`（`3_5:1396`），`b = A^{1/8}`。RBM2D 的实数引理、`Step3Scales`、`Lemma514`、`step3_Psi` 不能照搬，须重述；`Lemma514` 的位置由 `STXiBoot` 承担。票面"`b³, b⁴, R²` 与维数无关"的说法不成立（前提问题，非论文陈述）。

## D171 · 链式界取 `p ≥ 2`（论文 `p ≥ 4`）（2026-10-04，T2087 审核 O1；S3-24a，6583ca2）

`iterationsA_chain_term`、`iterationsA_boot_bound` 的前提是 `p ≥ 2`（论文 `3_5:1785` 为 `p ≥ 4`），前提更弱、Lean 陈述更强。

## D172 · Step 3 一步需要比合并的 `hBA` 更强的尺度前提（2026-10-04，T2087b；S3-24a，6583ca2）

合并的 `hBA`（T2058：`B_v A^{3/4} ≤ c`，即 `δ = 1/4`）对这一步太弱；需要 `B_v ≤ cB A^{-1+δ}` 且 `ρ² A^δ ≤ K A^{1/8}`（`IterationsAScale` 的字段 `rho`、`TA`、`Bctl`；情形 (i) `δ = 0`，情形 (ii) `δ = 𝔠d`）。S3-24b 须用 `IterationsAScale`，不能只靠 `st_hBA_I/II`。

## D173 · 情形 (ii) 的 `(rela_XILXILK)` 损失（2026-10-04，T2087c；S3-24a，6583ca2）

情形 (ii) 用 `(rela_XILXILK)`，损失 `T = A^{-1+𝔠d}`（`B_v ≤ B_s^{1-𝔠d}`），因 `𝔠d ≤ 1/24` 而被吸收；论文略去情形 (ii)（`3_5:1594`）。

## D174 · `(prop:BD1)`、`(prop:BD2)` 只在 `|r| ≤ c|a|`、`c < 1` 时成立（2026-10-04 补编，T2004c；KL 设计 T2004，0b91f7a；更正 D12）

`(prop:BD1)`、`(prop:BD2)`（`1_2:1153`、`1159`）写"`|r| ≲ |a|`"。D12 曾读作"对每个常数 `c > 0`"；T2004 的脚本（`bd` 块）表明 `c ≥ 1` 时为假：`r = −a`、`t = 0` 时 `Θ_0 = I`，左边为 `1`，右边量级为 `L^τ/|a|`，常数随 `L` 线性增长（`L = 17` 到 `65`，`g = 1`：`46.10` 到 `190.02`）；`|r| ≤ |a|/2` 时常数不超过 `7.77`。正确读法：对每个固定的 `c < 1`，在 `|r| ≤ c|a|` 上成立，常数依赖 `c`。KL 层的钉文 `KLDiffOne`、`KLDiffTwo`（`Loop/KLTree.lean`）已带此范围；按 D12 写的旧接口 `ThetaDiffOne`、`ThetaDiffTwo` 为假，清理票（KL14）删除。`(eq:ind-step-bound)` 的证明只在 `|s_j| ≺ 1` 时用 `(eq:f12)`，`|a_j − b_1| ≲ |s_j|` 的部分由 `(prop:ThfadC0)` 处理，所以范围限制不影响论文结论。 〔T2127：此 Lean 声明已删，见 D277〕

## D175 · `ML:Kbound` 在 `n = 3` 的证明还要 `(prop:ThfadC_short)`（2026-10-04 补编，T2004a；T2004，0b91f7a）

论文 `ML:Kbound` 在 `n = 3` 的证明（`A:673`）只引 `(prop:ThfadC)`；要得到锐利的界还需要 `(prop:ThfadC_short)`（短边以 `O(1)` 而非 `1/(1−t)` 求和）。`KLBoundAt_three` 用 `KLDecay` 与 `KLShort`。

## D176 · `ML:Kbound` 的常数对 `g` 一致只在 `g ≤ gmax` 时成立（2026-10-04 补编，T2004b；T2004，0b91f7a）

`ML:Kbound` 的常数对 `g` 一致，只在 `g ≤ g_max` 时成立（论文 `λ ≤ 𝔡⁻¹`，`(eq:WO)` `1_2:363`）；`g = 10` 时 `n = 2, 3, 4` 的比值为 `13.9`、`223.6`、`4071.7`。钉文带 `g ≤ gmax`，常数为 `C(d, κ, gmax, n, τ)`。

## D177 · `Def_Ktza` 与 `Θ_t` 定义里的 `t ∈ [0,1]` 应为 `[0,1)`（2026-10-04 补编，T2004d；T2004，0b91f7a；笔误）

`Def_Ktza`（`1_2:988–989`）与 `Θ_t` 的定义（`1_2:1072`）写 `t ∈ [0,1]`，应为 `t ∈ [0,1)`：`Σ_b Θ_t(0,b) = 1/(1−t)`，所以 `t = 1` 时 `Θ_1^{(+,−)}` 与 `𝒦^{(2)}` 不存在，`(WI_calK)` 里 `η_1 = 0`。

## D178 · KL 钉文的 `≺` 读作损失 `L^τ`（2026-10-04 补编，T2004e；T2004，0b91f7a）

KL 层钉文把 `≺` 读成对每个 `τ > 0` 的损失 `L^τ`，对 `g ∈ (0, gmax]`、体内 `E`、`t ∈ [0,1)`、`σ`、`a` 一致；`KLBoundAt_prec` 由它给出论文的 `≺`（`N = (WL)^d`），反之不成立。这是更强的形式。

## D179 · `Green/IBP` 证出论文留给 [YY_25] 的部分（2026-10-04，T2091a；S1-23 `Green/IBP`，382b6d9）

`Green/IBP.lean` 不对应论文的编号陈述：`3_5:37` 把 `(GavLGEX)`（`3_5:33`）的证明交给 [YY_25] Lemma 4.1（"与维数无关"）；本文件证出确切的展开式 `condExpDiag_eq_sum_Sblk` 与带显式余项 `ibpRem` 的分拆 `ibpRem_eq_add`。

## D180 · `(eq_sym_loop_bound)` 的常数显式为 `3^d/(W^d η_t)`（2026-10-04，T2094a；ST2-08 `Induction/ContractPt`，2b7c4f6）

论文 `(eq_sym_loop_bound)` 的 `≲` 在钉文里是显式常数 `3^d/(W^d η_t)`（锐利）；左边取 `Σ ‖𝓛^{(6)}‖`、最大值取 `max_{σ'} ‖𝓛^{(3)}‖`（范数；论文的 `𝓛^{(4)}_{alt}` 为非负实数：`= W^{-4d} hs(A_{c'})`）。`max_{c'∈𝒜}(𝓛^{(4)}_{alt})^{1/2}` 是前提 `‖𝓛^{(4)}‖^{1/2} ≤ M`。对称的另一式 `(eq_sym_loop_bound2)`（`3_5:758`）未单列。`stContractPt_holds : STContractPt d` 证出。

## D181 · `STContractPt` 文档串引用的比值（2026-10-04，T2094b；ST2-08，2b7c4f6）

钉文文档串（`Step2Defs.lean:380-390`）引 T2039 的比值 `0.39`；本票的检查在其数据上比值 `≤ 0.105`，在实例数据上为 `0.0055`、`0.0056`。陈述照写成立，只是所引数字来自另一组样本。

（T2090 = S1-36 `Induction/Step1`，b969625：无新 paper-delta；`step1TargetV3_holds` 证出，与 `stStep1_of_target` 合起来在 `STGbEXPii`、`STGbEXPij` 下给出 `STStep1`（论文 `(lRB1)` `1_2:1321`、`(Gtmwc)` `1_2:1327`）。）

## D182 · Step 2 结论的两种形式（2026-10-04，T2092a；ST2-04 `Induction/Step2Iterate`，c5bbae7）

合并的 `STStep2` 结论是打包的 `STStep2Concl`（`STLocalEntryU ∧ STAvgU ∧ STGdecayW`）；探针的三元形式现在叫 `STStep2Parts`（本文件新立），由 `ST_concl_of_step2`、`ST_avgU_of_avg` 桥接（`STStep2Avg` 是 `^1`、单电荷形式，`STAvgU` 含两种电荷；见 T2039g）。`ST_step2_concl` 取 `h : STStep2Parts d`，结论是合并的 `STStep2` 的陈述文本。

## D183 · Step 2 收尾新增的名字与登记（2026-10-04，T2092b–c；ST2-04，c5bbae7）

登记新增六行 owed；`ST_step2_of_pins'`、`ST_step2_of_pinsN'`、`ST_step2_of_pinsLW'`（用已证的 `stScaleExists_holds`、`stNetLift2_holds` 卸掉对应钉文，LW 形式带 `3 ≤ d`）、`ST_K2e_of_flow`、`ST_hq_of_data` 是探针里没有的新名字。登记与命名事项。

## D184 · `hierarchyN` 先取条件形式（2026-10-04，T2095a；ST2-28a `Induction/HierAlgebra`、`Induction/HierarchyN`，9bb2cbe；DECISIONS §32）

本文件的 `hierarchyN` 是条件形式 `hierarchyN_of_loopGenN : STLoopGenNForm d → HierarchyN d`；RBM2D 用 `loopGenN` 无条件证出。ST2-28 证出 `STLoopGenNForm d` 后去掉前提。论文陈述不变。

## D185 · `DefTHUST` 的算子即合并的 `ThetaN`（2026-10-04，T2095b；ST2-28a，9bb2cbe）

`DefTHUST`（`3_5:109`）的算子是合并的 `ThetaN`（`thetaKer = μ S Θ_{tμ}`、`cycProd`）；`k = 2` 时等于 `STthetaOp`（在 `hierarchyN_two` 内证出）。数学不变。

## D186 · `KellStarEv` 的尺度与新增前提（2026-10-04，T2097b；ST2-25 `Path/UBounds`、`UTransport`、`KellStar`，5bef95c）

`KellStarEv` 的尺度 `ℓ*_u = (log W)^{3/2} ℓ_u` 是 Lean 一侧的尺度（论文的定义是注释掉的一行，`3_5:2313`）；新增前提 `3 ≤ d`、`0 < Λ`、最终 `0 < lam ≤ Λ`、`0 < 𝔠`、`0 < τ`；远距离用 `zdistInf`。（T2097a 基于预检认错尾函数，已由 DECISIONS §33 更正撤销，不编号。）

## D187 · 局部极大值引理的远点计数为 `L^d`（2026-10-04，T2097c；ST2-25，5bef95c）

`UopLocalMax`、`UopPairLocalMax` 的远点计数是 `card (Zd d L) = L^d`（RBM2D `L²`）；消费者须让 `4 L^d W^{-D'}` 小（例如 `L^d ≤ W^K`，DECISIONS §21）。

## D188 · 网格展开带 `∀ n` 前提（2026-10-04，T2098a；ST2-26 `Path/Expansion`，2b7cab5）

`StoppedDuhamel105`、`grid_expansion_all`、`grid_expansion`、`grid_expansion'`、`grid_expansion_all'` 对 `s, t, K` 带 `∀ n` 前提（同 RBM2D 钉文），论文无此量词；`_at` 形式是在单个 `n` 处的前提，供 `∀ᶠ n` 的消费者用。钉文形式，非数学改动。

## D189 · `Avec`、`Dgrid` 的词汇与形状（2026-10-04，T2098b；ST2-26，2b7cab5）

`Avec`、`Dgrid` 用合并的 `STLKM`、`STELKLKM`、`STEGtM` 在 `σ = (+,−)` 定义；`Avec sz E s t K n k ω` 是 `Zd × Zd` 上的函数，而 `Step2Defs` 的张量是 `Fin 2 → Zd` 上的函数（私有桥 `Expansion_STthetaOp_eq`）。ST-3 消费者须对照其钉文核对形状。

## D190 · `(int_K-L_ST)` 的时间离散、逐路径形式（2026-10-04，T2098c；ST2-26，2b7cab5）

`StoppedDuhamel105`、`grid_expansion(_all)` 等是 `(int_K-L_ST)`（`3_5:134-139`，`Sol_CalL`，"[YY_25] Lemma 5.3"）的时间离散、逐路径形式：论文是停时 `τ ≥ s` 处的连续时间积分方程，Lean 是网格 `u_j` 上的伸缩和（参 D162）。

## D191 · `condExp_A_succ` 是 Lean 独有的 Euler 一步漂移分拆（2026-10-04，T2098d；ST2-26，2b7cab5）

`condExp_A_succ`（及 `Expansion_condExp_A_succ_of_lt_one`、`…_rpow`）是论文没有的 Euler 一步漂移分拆：`predInc_j = Δ·(E^{LK×LK} + E^{G̃})_{u_j} + R_j`，`‖R_j‖ ≤ envConst · Δ^{3/2} + 7 N η_{u_{j+1}}^{-4} Δ²`（几乎处处），`N = (WL)^d`；`d` 维常数来自 `W^{-d}`、`W^{-2d}`。

## D192 · `sum_prod_abs_card_image_le` 的证明换成标号论证（2026-10-04，T2096a；S1-21 `Green/FlucIterGain`，54c61da；DECISIONS §30）

RBM2D `sum_prod_abs_card_image_le`（`:966`）用均匀权的质量界 `c·#A ≤ 1`（`:1017`）证；对 `S` 的行在 `d ≥ 3` 为假（`c·#A = 2d + 1`）。Lean 用标号论证在界 `min c 1` 处证出同一陈述（RBM2D 的签名，`UniformWeight → BoundedWeight`）；前提 `hs : s ≤ #A` 未用。只是证明不同，陈述不变；预算常数不变（审核第 1 轮指出签名问题，修复一次）。

## D193 · `(eq:f12)` 对一切 `s` 成立须带 `(|s|+1)` 权（2026-10-04，T2100a；KL10a `Loop/KLIndStepA`，c4c1f80）

`KLf12_bound`：`|f₁| ≤ C L^τ (g²+|1−t|)⁻¹ (|s|+1)^{d−1}/(|y|+1)^{d−1}`、`|f₂| ≤ C L^τ (g²+|1−t|)⁻¹ (|s|+1)^d/(|y|+1)^d`，对一切 `s`（`q₁ = d−1`、`q₂ = d`、`c = 1/2`）；论文（tex l.748）只对 `|s| ≺ 1` 陈述。不带权时常数随 `L` 增长（预检脚本：`L` 由 9 到 17，`f₁` 比值 169→625，`f₂` 2197→15625），所以权是必需的；权由 D194 的带权和为零估计吸收。

## D194 · `(eq:Sigma-empty-sum-zero)` 的第二估计用带权形式（2026-10-04，T2100b；KL10a，c4c1f80）

`KLsumZero_weighted`：`Σ_{δ_r=x} |Σ^{(∅)}(σ,δ)| (max|δ_i−δ_j|+1)^Q ≤ C(g²+|1−t|)`，`σ ∈ {σ_alt, ¬σ_alt}`、任意根 `r`、任意 `Q`；由非常数 `δ` 的逐点 `g²` 因子与带号估计推出。论文引 [RBSO1D] Claim 4.30 的不带权形式；只由 `KLmolecule_holds` 与 `KLsumZeroAt` 推不出（质量 `A` 可落在 `M ≈ c⁻¹ log(1/A)`，给 `A·log^Q(1/A)`，在固定 `L` 下 `g, τ → 0` 时无界）。

## D195 · 情形 (i) 无损失（2026-10-04，T2100c；KL10a，c4c1f80）

`KLindStep_nonAlt_noloss`：非交错 `σ`（某个 `j ≠ r` 为短叶）时 `(eq:ind-step-bound)` 不带 `L^τ` 也不带 `log L`，比论文强。

## D196 · 衰减剖面写成 `(|x|+1)^p`（2026-10-04，T2100d；KL10a，c4c1f80）

Lean 用 `(|x|+1)^p`，论文用 `|x|^p + 1`；两者相差至多 `2^p`（`pow_add_pow_le`、`KLIndStepA_pow_le`）。记号事项。

## D197 · `lem:newKLK` 的证明用近/远分拆代替截断 `K`（2026-10-04，T2099a；ST2-07 `Induction/NewKLK`，b9875c0）

`3_5:611` 先设"不妨 `𝒯_u(ℓ) ≥ W^{-D}`"，再取截断 `K ≤ ℓ` 使 `𝒯_u(K) = W^{-D}`；Lean 保留下界、按 `1 ≤ ℓ`、`r ≤ ℓ`、`W^{-D} ≤ 𝒯(r)` 分近/远，用 `𝒯(max(r−1,0)) ≤ 2^{d−2} e 𝒯(r)` 代替 `𝒯_u(K+1) ≍ 𝒯_u(K)`（`3_5:651`），不用 `ℓ ≤ L`。证明路线，陈述不变。

## D198 · 弱局部律取显式 `δ₀ = κ/2`（2026-10-04，T2099b；ST2-07，b9875c0）

`3_5:644` 的"弱局部律 `(Gtmwc)`，`1 + o(1)`"在 Lean 中是 `‖G_u − M‖_max ≤ δ₀ = κ/2`（`Ind.half_le_mE_im`：`κ/2 ≤ Im m`），给 `Im G_{xx} ≤ 2 Im m` 与 Ward 因子 `5 W^{-d}/(1−u)`（`𝓛` 贡献 4、`𝒦` 贡献 1），代替 `(1+o(1))/(W^d(1−u))`；吸收进 `C`。钉文本已带 `δ₀`（D83），签名不变。

## D199 · `𝓛` 用逐项 Ward 界，`𝒦` 不用 Ward（2026-10-04，T2099c；ST2-07，b9875c0）

论文用 Cauchy–Schwarz 把 `|𝓛_{±±}|` 比到 `𝓛_{−+}`，并用 `(WI_calL)`、`(WI_calK)`；Lean 对四种符号都证 `|𝓛_σ(a,b)| ≤ W^{-2d}(Q_{ab}+Q_{ba})`，`Σ_c |𝒦_σ(a,c)| ≤ W^{-d}(1−u)⁻¹` 直接来自 `sum_norm_Theta_row_le`。证明路线。登记表删 `STNewKLK`（已证）；`STNewKLKAt` 一行保留（它是 `ST_good_engine` 的前提，无定理直接给出它），KL14 时可补一行推论再删。

## D200 · `W_le_self`、`perTimeDomAt_of_le_left_on` 带 `1 ≤ d`（2026-10-04，T2101a；S1-24 `Green/CondDom`，d4a34da）

RBM2D 的 `size = (W L)² ≥ 9` 白给；`d = 0` 时 `size = 1`，所以 Lean 加前提 `hd : 1 ≤ d`。消费者都在 `d ≥ 3`。登记与形式事项。

## D201 · `giiOmegaSeq`、`giiSeq_of_asGMc` 带 `3 ≤ d`（2026-10-04，T2101b；S1-24，d4a34da）

两条与合并的 `diag_bound_stochDom` 一样带 `hd : 3 ≤ d`；其余前提用 `Admissible` 形式（D39）；`hG : GaussIBP` 去掉（T2091 审核 O1）。`gijOmegaSeq`、`giiOmegaSeq` 对高斯流在 `Admissible` 下无条件证出：登记表里 `RBM.Green.GijOmegaSeq`（owed，注释"S1-24"）可改类（T2101 审核 O2，KL14 清理时处理）。

## D202 · `qvPropagatedN` 带因子 `k`（切口数）（2026-10-04，T2103a；ST2-28 `Induction/LoopGenN`、`Induction/QVN`，e56d95c）

`defEOTE`（`3_5:166-190`）的 `(𝓔⊗𝓔)` 不是字面意义上的二次变差（有跨切口项），所以一般 `n` 的 `qvPropagatedN` 带因子 `k`，不是 `1`；这是 T2084c / D152–D155 在一般 `n` 的重复（预检数值：`d = 3, L = 3, W = 1` 时 `LHS/Re = 1.0931 > 1`）。只用不等式；论文数学不变。`STLoopGenNForm` 由 `stLoopGenNForm_holds` 证出，`hierarchyN_holds` 无条件成立（D184 的前提去掉）；`QVPropagatedN` 是已证的钉文，由第一个消费者（ST-3）登记。

## D203 · `loopGenN`、`QVN_core` 以耦合 `g` 为参数（2026-10-04，T2103b；ST2-28，e56d95c）

`S^{(B)}(g)` 的 `g` 是参数（同 T2084a、T2077a）；RBM2D 的 `W²` 一律为 `W^d`。形式事项。

## D204 · `Ugen` 与 `*N` 词汇去掉 `[NeZero k]`（2026-10-04，T2104a；ST2-27 `Path/DuhamelTail`、`Induction/GridDuhamelN`，2ebee73）

用 `finRotate` 形式；`Ugen` 是合并的 `UN` 在 `m i = m(σ_i)` 处。形式事项。

## D205 · `StoppedDuhamelN`、`StoppedAzumaN` 的能量是序列（2026-10-04，T2104b；ST2-27，2ebee73）

同 RBM2D 取 `E : ℕ → ℝ`；合并的 `StoppedDuhamel105`、`StoppedAzuma108` 取标量 `E`；桥是 `stoppedDuhamel105_of_stoppedDuhamelN` 与 `AvecN_two`、`martIncN_two`、`predIncN_two`。

## D206 · `_at` 形式更强（2026-10-04，T2104c；ST2-27，2ebee73）

`stoppedAzuma108_at`、`stoppedAzumaN_at` 不需要窗口前提；`stoppedDuhamelN_at` 只在下标 `n` 处要 `|E n| < 2`、`0 ≤ s n ≤ t n < 1`、`K n ≠ 0`。停止的 Azuma 的次高斯输入（停止鞅差的条件 Hoeffding）是钉文前提，不在此证。

## D207 · `stopped_duhamel_cheb_tail` 的标号数 `L^{2d}`（2026-10-04，T2104d；ST2-27，2ebee73）

RBM2D 是 `L⁴`；Lean 独有的中间量，无论文陈述。BDG 换成 Azuma（常数 `4`、`4 Σ c`）见 D21、D90（T2104 报告误引 D10，审核 O2 已更正）。

## D208 · `STEMn2Poly` 不需 `STGbEXP*`（2026-10-04，T2102a；ST2-09 `Induction/EMn2Poly`，90a2761）

论文用条目界 `(GijGEX)`、`(GiiGEX)` 估 `(𝓛⁴)^{1/2}` 与 `𝓛³`（`3_5:812–825`）；Lean 用分块 Cauchy–Schwarz（F1、F2），只需 `(eq:LW_assm)`，所以 `stEMn2Poly_holds` 无条件成立；钉文的前提 `(initialGT2)` 没用到。证明路线，陈述不变。登记表 `STEMn2Poly` 的 owed 行可删（KL14 清理）。

## D209 · `(eq_sym_loop_bound2)` 的交错 4-圈（2026-10-04，T2102b；ST2-09，90a2761）

`(eq_sym_loop_bound2)`（`3_5:758`）在 Lean 中是 `emn2Poly_contractPt_partner`（旋转并翻转全部荷）；其交错 4-圈是 `(c,a,c,a)` 处的 `(−σ₁,σ₁,−σ₁,σ₁)`，论文写 `σ^{(alt)} = (σ₁,−σ₁,σ₁,−σ₁)`，涉及分块 `P_aGP_c` 而非 `P_cGP_a`，一般不同。无害：两者都 `≤ |𝓛²_{(±)}|`（F1）。

## D210 · `flucGainUpTo'_of_minorDiffGainUpTo'`、`minorGoodLe_of_goodEvent_flow` 对一切实 `u` 成立（2026-10-04，T2105a；S1-22 `Green/MinorGoodLe`，ec0e7d5）

目标 1 在 `|E| < 2`、`t < 1` 下对一切实 `u` 成立，目标 2 在 `(zt E u).im ≠ 0`、`|E| ≤ 2` 下对一切实 `u` 成立；论文的流时间是 `0 ≤ s ≤ t < 1`。推广，无损失。

## D211 · 高阶子式展开、`MinorDiffGainUpTo'` 与 `MinorGoodLe` 是 Lean 的构造（2026-10-04，T2105b；S1-22，ec0e7d5）

论文没有高阶子式展开、子式 `G^{(S)}` 与层预算：`(GavLGEX)`（`3_5:33`）推给 [YY_25] Lemma 4.1（`3_5:37`）。Lean 加 `MinorDiffGainUpTo'`（前提，S1-25/S1-26 证）与 `MinorGoodLe`，常数 `2Ψ`、`8MΨ ≤ 1`、`‖(G^{(S)}_{aa})⁻¹‖ ≤ 2` 是与维数无关的 Lean 选择。预检：`q = 0` 层的增益量级 `B ≈ 0.55 W^{-d/2}`（指数 `d/2`，RBM2D 为 1），`q ≥ 1` 未核。

## D212 · 文档串中的方程号 (4.1)–(4.3)、(4.9) 是 [YY_25] 的（2026-10-04，T2105c；S1-22，ec0e7d5）

继承自 RBM2D；arXiv:2507.20274 无此编号。记号事项。

## D213 · `LocalLawDetThm` 等的下界取 `W^{-d/2} ≤ Ψ`（2026-10-04，T2108a；S1-27 `Green/LocalLaw`，6187713）

`LocalLawDetThm d`、`FixedTimeFAThm d`、`IBPDetThm d`、`GavLDetFloorThm d` 的下界是 `W^{-d/2} ≤ Ψ`（论文 `3_5:27`），RBM2D 是 `W⁻¹ ≤ Ψ`；`LoopFloorThm d` 的结论是 `(W^d)⁻¹ ≤ 4 N^ε Ψ²`（RBM2D `(W⁻¹)² ≤ …`）。照字面移植在 `d = 3` 编译为假，所以按 R3 重算指数；审核认定在 ST1-COMMON 第 6 条范围内，无需签字。**后果**：钉文 `FixedTimeFAThm d`、`IBPDetThm d`（S1-29/S1-30 证）带论文的较弱前提 `W^{-d/2} ≤ Ψ`；RBM2D 在 `W⁻¹ ≤ Ψ` 下的证明是否在此下界成立，由 S1-29、S1-30 的预检核对。另：近邻集合用 `zdistInf`，点数 `3^d`、`9^d`（票面 `2d+1` 有误，审核 O1）。

## D214 · `KLindStepAt` 的叶子与根（2026-10-04，T2106a；KL10b `Loop/KLIndStepB`，f590e74）

`KLindStepAt` 对叶子 `Θ_t^{(σ_i,σ_{i+1})}`（交错 `σ` 时即 `Θ_t`）与任一满足 `σ_r ≠ σ_{r+1}` 的根 `r` 陈述 `(eq:ind-step-bound)`（`A_deterministic_estimates.tex:703`）；论文的叶子是 `Θ̃_t ∈ {Θ_t, tS^{(B)}Θ_t^{(+,−)}}`、根为 `1`。叶子更窄、根更一般；`tSΘ` 叶子此处既不陈述也不证（钉文文档串：`tSΘ^{(+,−)} = Θ^{(+,−)} − I`），由 KL11（T2115）在切割处说明如何化归。承自签过的探针钉文。`KLindStepPin_holds` 证出：KL10 完成。

## D215 · 成对格点和是 `O(1 + log L)`（2026-10-04，T2106b；KL10b，f590e74）

`Σ_b [(|y_i|+1)(|y_k|+1)]^{-(d−1)}` 在 Lean 是 `O(1 + log L)`（`KLlat_pair_rpow`），论文 item 4 末行（`:776`）写 `≲ 1`；`log L` 由损失 `L^τ` 付（G3 用 `τ/3 × 3`，无余量）。证明预算，陈述不变（T2100 审核已判）。

## D216 · `STOptL2` 不需 `N^{-C}` 网（2026-10-04，T2110a；ST2-14 `Induction/OptL2a`，6f8ca5b）

论文对 `u` 的 `N^{-C}` 网与扰动论证（`3_5:511`）对逐时刻钉文 `STOptL2`（`PrecPT`，`ST_PT_of_sections`）不需要。证明路线。

## D217 · `(lokis2)` 的 `W^{-c₀}` 是 `λ = ((1−s)/(1−T)) W^{-d}B_{T,0}`（2026-10-04，T2110b；ST2-14，6f8ca5b）

`OptL2alam`；`(lokis2)` 由 `STStep1Loop` 与 `STBctl_mono` 推出（`OptL2a_loop_ctl`）。记号事项。

## D218 · `(eq:Psi)` 的 `Ψ_t` 取 `min(√λ, W^{-ε₀})`（2026-10-04，T2110c；ST2-14，6f8ca5b）

因 `STPsiClass` 要求对每个 `n` 有 `0 < Ψ ≤ W^{-ε₀}`；终究不起作用（同 T2109b 的截断）。形式事项。

## D219 · `(con_st_ind)` 只用第一合取（2026-10-04，T2110d；ST2-14，6f8ca5b）

`(con_st_ind)` 只经第一合取 `B_T^{𝔠_d} ≤ (1−T)/(1−s)` 与 `𝔠_d ≤ 1/2` 进入；第二合取 `(1−T)/(1−s) < 1` 在截面 `T = s` 不成立，所以截面上的定理只取第一合取。§29 边界事项，钉文不变。

## D220 · `O_≺` 项显式化（2026-10-04，T2110e；ST2-14，6f8ca5b）

初值 `N^τ B_s²`、余项 `≤ N^{-2}`、鞅 `≤ N^τ λ^{5/4}`、轻权漂移 `≤ N^τ η⁻¹ λ^{3/2}`；Grönwall 右边 `α` 为常数（不减）、`β_j = C₀/(1−u_j)`。证明路线。`stOptL2_of_pins` 需 `3 ≤ d`（T2110f，由 ST2-15 的票写明）。

## D221 · 子式差分的常数与预算是 Lean 的构造（2026-10-04，T2113a；S1-25 `Green/MinorDiff`，778bdf7）

论文没有子式 `G^{(S)}`、子式差、预算 `M`、常数 `atomC`、`minorDiffC`、`DiffBd.mul` 的 `2^n`；`(GavLGEX)`（`3_5:33`）推给 [YY_25] Lemma 4.1（`3_5:37`）。常数、预算与 `Ψ ≤ 1` 是 Lean 的构造，与维数无关（RBM2D T2158a）。常数极大（`minorDiffC 2 = 2^91`），不影响陈述（CLAUDE.md §7）。登记表 `MinorDiffGainUpTo'` 一行的注释应为 S1-26（KL14 清理时改）。

## D222 · `LWweightExp`、`LWggExp` 的 `S⁺` 实参次序（2026-10-04，T2107a；LW-05 `Graph/LWWeightExp`，975f4ff；DECISIONS §34）

钉文的 `S⁺` 是 `S(g)(1 − m(E)² S(g))⁻¹`（`eq:def-Spm`），定义的实参次序 `(g, E, t)`；T2067 入库时两条钉文把 `E`、`g` 写反，§34 改了六处。Lean 内部的钉文更正，非论文差别；记录在此备查。`lwWeightExp_holds` 证出，登记删 `LWweightExp`。

## D223 · `(Owx)` 的图运算形式只对蓝色带圈权、内点、`0 < u`（2026-10-04，T2107b；LW-05，975f4ff）

陈述对内点 `x` 的蓝色权 `Ǧ_{xx}`、`p ∈ lwSplit Γ.solid`、`0 < u`、`M_{aa} = m`；红色权与 `u = 0` 未陈述（另行的陈述，目标不需要）。

## D224 · `(Owx)` 的导数项：每条实边一个图（2026-10-04，T2107c；LW-05，975f4ff）

导数项是 `f` 的每条实边各一个图（`lwSplit p.2`），`w = x` 由边表实现（`owxDE`），不用 `LGraph.dTerm`（后者有两个新外点）；`∂_{h_{αx}}` 是 T2060a 的 `dhSample`。

## D225 · 桥接在常数尺寸序列上（2026-10-04，T2107d；LW-05，975f4ff）

桥对常数序列 `lwWxSizes d L W g hL` 在 `n = 0` 陈述；`lwWx_integral` 要求被积函数连续（钉文的被积函数都是样本的连续函数）。形式事项。

## D226 · `|b−c'| ≥ (1−o(1))|a−b|` 用作 `2(ℓ*+1) ≤ ℓ†`（2026-10-04，T2109a；ST2-10 `Induction/EMn2Exp1`，aaf704f）

`3_5:851–852` 的估计在 Lean 是 `2(ℓ*+1) ≤ ℓ†`（`emn2Exp_profile_cmp` 的前提；`emn2Exp_scale_gap` 在 `(log W)^{1/4} ≥ 4` 下，终究成立；精确门槛 `log W ≳ 16.94`）。小 `n` 不成立，钉文是终究形式，无碍。

## D227 · 截断剖面 `Ψ'` 带上限与 `W^{-D}`（2026-10-04，T2109b；ST2-10，aaf704f）

`3_5:833–838` 的 `Ψ_t(r) = (W^{-d}B_{t,r∧ℓ})^{1/2}` 换成 `Ψ'_n(r) = min(√(W^{-d}(B_{t,r∧ℓ⁺} + W^{-D})), W^{-ε'})`：上限使 `STPsiClass` 的 `Ψ ≤ W^{-ε'}`（每个 `n`）成立；`+W^{-D}` 给出对一切 `r`、`D` 的 `W^{-d}𝒯̃ ≤ Ψ'²`（论文的第二个事实需 `W^{-D} ≲ B_{t,r∧ℓ}`）。

## D228 · `(eq:pointwise_loop2)` 与 3-圈界不需条目界（2026-10-04，T2109c；ST2-10，aaf704f）

由 `(eq:LW_assm_exp)` 经分块 Cauchy–Schwarz 得到，`(GijGEX)`、`(GiiGEX)` 不出现（同 D208）。证明路线。

## D229 · `R₃` 的读法（2026-10-04，T2109d；ST2-10，aaf704f）

`3_5:842–845` 的 `R₃` 读作 `ℓ* < |c'−b| ≤ ℓ` 且 `ℓ* < |c−a| ≤ ℓ`，即 `R₁ ∪ R₂` 的补；覆盖常数为 `1`（`|S^{(B)}| ≤ 1`）。

## D230 · 损失 `K_n` 等为 `N^{o(1)}`（2026-10-04，T2109e；ST2-10，aaf704f）

`K_n`、`√(1 + c_B⁻¹)`（`c_B` 只依赖 `𝔡`）、近处的 `4√(1+c_B⁻¹) exp(2(log W)^{7/8})` 都是 `N^{o(1)}`，吸收进 `≺`（`emn2Exp_ev_exp_pow`）。

## D231 · 未用到的前提（2026-10-04，T2109f；ST2-10，aaf704f）

两条定理与钉文逐字相同但未用到：`Ψ` 及其窗口、`STInitialGT2.2`、`ℓ ≤ (log W)^{10}ℓ_t`；`emn2Exp_far12` 另有 `ε₀`、`STInitialGT2.1` 未用。`STEMn2Exp` 不变，仍欠（ST2-11）。

## D232 · `exists_norm_Kcal_le_win` 沿尺寸序列、以欠下的 `STKbound` 为前提（2026-10-04，T2111a；ST2-29 `Induction/LoopC2N`、`GridDriftN`，14137ce）

RBM2D 由已证的 `Kbound_prec_uncond` 对 `(L,W,E,u,v)` 一致地证；本库沿尺寸序列陈述，前提为欠下的 `STKbound sz E` 与 `SizeTendsto`，对一切 `w ∈ [0, v_n]`。总调度 06:20 照准（票末注）；消费者 ST2-31 须用此形式；`STKbound` 由 KL11 的 `KLboundPin` 与 PT 证明在 KL14 推出。

## D233 · `HermTestFunLoopN`、`GridDriftN` 去掉 `[NeZero k]`（2026-10-04，T2111b；ST2-29，14137ce）

同 D204；更强，`k = 0` 也被证明覆盖。（文件文档串里误标为 T2111a，以报告编号为准，审核 O1。）

## D234 · `GridDriftN_exists_envelope` 是新的逐 `n` 确定性包络（2026-10-04，T2111c；ST2-29，14137ce）

论文无对应陈述。

## D235 · `stepErrN`、`kStepC` 是 Lean 中间量（2026-10-04，T2111d；ST2-29，14137ce）

带 `W^d`、`L^d`；论文无对应陈述。`hermTestFunLoopN` 的证明用 `‖E_b‖ ≤ 1`，丢掉 `W^{-dk}` 增益（同 2D 钉文，审核 O3）。

## D236 · `𝔠₀ = 1/(8C₀ + 10)`（2026-10-04，T2116a；ST2-15 `Induction/OptL2b`，2270c89）

`3_5:508–509` "取 `𝔠_d` 依 `C₀` 足够小"：Lean 给出 `𝔠₀ = 1/(8C₀ + 10)`，`C₀` 是 `stOptL2a_gronwall` 的常数（在 `κ ε 𝔡` 之后、`𝔠` 与序列之前取定）。`stOptL2_of_pins (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d` 证出（条件于欠下的 `STLWB`、`STGridMart`）。

## D237 · `(eq:L-K2max)` 的末步用 `B_T` 与指数计数（2026-10-04，T2116b；ST2-15，2270c89）

论文以 `ρ^{C₀+5/4}(W^{-d}B_{t,0})^{1/4} ≪ 1` 收尾；Lean 用 `B_s ≤ B_T`（`STBctl_mono`），两项各自由 `1 + 𝔠_d(C₀ + 5/4) ≤ 5/4`、`1 + 𝔠_d C₀ ≤ 2`、`B_T ≤ 1` 精确地 `≤ B_T`，不需要 `B_T^{1/4}` 小；和为 `≤ 2B_T`，因子 `2` 吸收进 `≺` 的损失。证明路线。

## D238 · `(eq:K-pi-bound)` 的归纳按顶点数、只对标准 `K^{(π)}`（2026-10-04，T2115a；KL11 `Loop/KLInduct`，f4cc46d）

论文（`A_deterministic_estimates.tex:678–680, 791–805`）对推广的 `K̃^{(π)}`（叶子 `Θ̃ ∈ {Θ, tSΘ}`，`(eq:wtKpi)`）按分子数 `r` 归纳、切下一个叶分子（`(eq:Kpipi)`）；Lean 按多边形顶点数 `n` 归纳，在最内长边处切树（RBM2D `Kpi_cut`），只对标准 `K^{(π)}`（钉文 `KLKpiBoundAt` 即 `K̃` 的 `Θ̃ = Θ` 情形）；`k = l+1`、`n'' − 1 = n − l` 给出同样的指数。`tSΘ` 叶子从不出现：粘合边是 `ξ_J S^{(B)}` 乘标准叶子（回答 D214）。证明路线。`KLKpiBoundPin_holds`、`KLboundPin_holds` 证出：`ML:Kbound` 对一切 `n ≥ 1` 在 `KLPT` 下成立；`KLoopBound`（`KBound.lean:74`，欠）由其蕴含，KL14 处理。

## D239 · 切割前因子是 `t`（2026-10-04，T2115b；KL11，f4cc46d）

合并的 `KLKpi` 下 `∏_{in} m ∏_{out} m = (∏ m) m(σ_i) m(σ_j)`，RBM2D 的 `ξ_J` 变为 `t`（票面写的"模为 1 的 `∏ m`"不确）。票面事项，无论文差别。

## D240 · `n ≤ 3` 的界取 `KLPT` 为前提（2026-10-04，T2115c；KL11，f4cc46d）

`KLedge_sup`、`KLBoundAt_two`、`KLBoundAt_three` 取 `KLPT d κ gmax`，探针取 `KLDecay d gmax`（及 `KLShort`）；要按 `KLDecay` 陈述须先登记 `KLDecay`。形式事项。

## D241 · 交换关系的前提（2026-10-04，T2112a；S3-20 `Induction/ZeroModeCalc`，d1cb5a6）

论文的交换说明（`3_5:1540–1545`）无前提；Lean 需 `3 ≤ L` 与 `‖t m_i m_{i+1}‖ < 1`（`Θ_{tμ}` 存在），`Ugen` 另需 `|E| ≤ 2`、`0 ≤ w < 1`。

## D242 · `(normQA2)` 对 `Q^{(A)}` 取 `2^{|A|}`（2026-10-04，T2112b；S3-20，d1cb5a6）

论文对 `Q^{(i)}` 给常数 2；Lean 另对 `Q^{(A)}` 陈述，常数 `2^{|A|}`（单指标界之积）。

## D243 · `(iisuwjyys)` 是逐路径的停止网格 Duhamel 恒等式（2026-10-04，T2112c；S3-20，d1cb5a6）

对 `i < j∧τ` 求和，核 `𝒰_{u_{i+1}, u_{j∧τ}}`，不是对 `u` 的积分；`Q^{(A)}` 在外与在内两种形式都陈述。可预测部分的核在合并的伸缩和里是 `u_{j+1}`（票面写 `u_j`，预检 F2）。`Q^{(A)} martIncN` 是鞅增量（坐标的有限线性组合）留给 S3-21 证（审核 O1）。

## D244 · `lem: newPQ` 的组合对一切 `A`（2026-10-04，T2112d；S3-20，d1cb5a6）

论文 `3_5:1590` 只用 `A = ∅`；Lean 对一切 `A` 陈述，`(𝓛−𝒦) = STLKM sz n E τ (sz.seqHflow n τ ω)`。

## D245 · `norm_zeroModeSet_UN_le` 只适用于全正荷（2026-10-04，T2112e；合并的 EK-5 `Kernel/Evolution.lean:629` 的观察）

其前提 `hmi : ∀ i, 0 < (m i).im` 对 `m i = mSigma E false` 不可满足，只对全 `+` 荷可用；混合荷 `σ` 须经 `ekSumDecayNonzero_holds` / `STEKNonzero`。S3-21 的票照此路由。

## D246 · 坏事件塔与条件包络是 Lean 的构造（2026-10-04，T2117a；S1-26 `Green/MinorDiffCond`，c24f54b）

`badStep`、`badTower`、`BadFamily`、`badBase`、`condEnv`、`condCost`、`condEps`、`minorDiffGainUpTo'_of_le_on` 与常数 `minorDiffC M` 是 Lean 从事件 `Ω(t, ε₀)`（`def_asGMc`，`3_5:16`）过渡到矩界的装置；论文推给 [YY_25] Lemma 4.1（`3_5:37`）。

## D247 · 端点以显式 `hB1`、`hsmall` 代替 `≺`（2026-10-04，T2117b；S1-26，c24f54b）

`hsmall` 由 `P(Ω^c) ≤ N^{-D}`（`D ≥ D_W`）推出，`∀ᶠ n` 由消费者给；`hB1` 在 `M = 1` 需 `δ ≤ 2^{-19}`。两者只对固定 `M, K, c` 终究成立。**欠账**：`hsmall` 对公理扫描不可见，S1-28（`FlucThreshold`）须由高概率局部律推出或作具名前提带上。登记表 `MinorDiffGainUpTo'` 一行此后扫描不再报出（KL14 删或改注释，S1-25 → S1-26）。

## D248 · `hB1 ∧ hsmall` 的联合可满足性（2026-10-04，T2117c；S1-26，c24f54b）

`M ≥ 1` 时 `hB1` 迫使 `δ ≤ 2^{-19}`（`M = 1`）、`2^{-93}`（`M = 2`），与 `W, t` 无关；`hsmall` 需 `P(‖G_t − m‖_max > δ) ≤ (δ/4)^K`。`W = 2` 时只有 `t ≤ 10^{-17}` 的极端数据可用；`t` 为常数阶时要求 `W^{d/2} ≫ 2^{19}`。系继承的常数 `minorDiffC`（无论文对应）所致，不影响陈述。

## D249 · `(Oe1x)` 第 1 项的 `Δn_M ≤ 0`（2026-10-04，T2119a；LW-06 `Graph/LWEdgeExp`，3fcd6c6）

T2040 (a)(i) 的表列 `Oe1x-delta` 的 `Δn_M = 0`；Lean 证 `Δn_M ≤ 0`：`x` 并入外点或另一分子时为 `−1`，同一分子内为 `0`（尺寸 `(L^d)^{n_M}` 只要 `≤`）。`lwEdgeExp_holds` 证出，登记删 `LWedgeExp`。

## D250 · 第 7、8 项每条边一个图（2026-10-04，T2119b；LW-06，3fcd6c6）

钉文保留 `k₁ m`、`k₄ m`；图层面是 `x` 的每条蓝出边 / 红入边各一个图 `oe1xD`（系数 `m`），值相同（`oe1x_pointwise`）。

## D251 · 第 3–6 项的拆分图（2026-10-04，T2119c；LW-06，3fcd6c6）

未拆的导数图 `oe1xD` 带不带圈的环 `Ḡ_{xx}` / `G_{xx}`（`Δord = +1`）；论文的第 3、4 项（`Δord = 0`）与 5、6 项是 `oe1xDs` 的拆分图（`G_{xx} = Ǧ_{xx} + m`，前提 `M_{aa} = m`）；按被求导边的 `(σ, 起点, 终点)` 分类。

## D252 · `y₁ = x` 的情形（2026-10-04，T2119d；LW-06，3fcd6c6）

第 1 项的合并需 `y₁ ≠ x`；`y₁ = x`（`e₀` 是不带圈的环，即权）时第 1 项是 `oe1xT1loop`，`Δ(n_S, n_V) = (−1, 0)`、`Δord = −1`；论文表只列合并情形。

## D253 · `(Oe1x)` 的适用范围（2026-10-04，T2119e；LW-06，3fcd6c6）

`e₀` 为蓝色、不带圈；其余边任意（含带圈）；带圈的 `e₀ = (G − M)_{xy₁}` 不陈述。钉文（值层面）不需要。

## D254 · `(Oe2x)` 的 R1、R2 的 `n_M` 变化（2026-10-04，T2120a；LW-07 `Graph/LWGGExp`，5c69cb4）

T2040 表（`Oe2x-R1`、`R2`）列 `Δn_M = 0`；Lean 给 `n_M(Γ) − 1 ≤ n_M(R) ≤ n_M(Γ)`（合并 `x ↦ y` 与新的波边 `S⁺_{xy}` 可能连起两个分子），`n_M(R) = n_M(Γ) − 1` 确有实例。`ord` 不含 `n_M`。`lwGGExp_holds` 证出（§34 修后的钉文），登记删 `LWggExp`。

## D255 · R1 的计数需 `y ≠ x`（2026-10-04，T2120b；LW-07，5c69cb4）

`R1`（`m δ_{xy} G_{y'x} f`）只在 `x` 并入别的顶点时 `Δ(n_S, n_W, n_V) = (−1, 0, −1)`；`oe2x_graph_E` 设 `y ≠ x`；`y = x` 时 `G_{xx}` 为权，`Δord = −1`，未陈述；值恒等式对一切 `y` 成立。

## D256 · `(Oe2x)` 的 `=_E` 读作期望相等（2026-10-04，T2120c；LW-07，5c69cb4）

对一切预解多项式 `f`（T2040d）与流数据 `S = t svarF`、`z + tm = −m⁻¹`、`S⁺ = S(1 − m²S)⁻¹`（§34 的实参次序）。图层面恒等式设 `0 < u`（同 `owx_graph_E`），`t = 0` 只在钉文层面（审核 O1）。只陈述 `GG` 形式，`ḠḠ` 由共轭得（审核 O2）。

## D257 · `(Oe2x)` 作图运算时 `f` 的读法（2026-10-04，T2120d；LW-07，5c69cb4）

`f` 是除 `G_{xy}`、`G_{y'x}` 外的实边之积（`q.2`），每条（含权与轻权）在 `R7`、`R8` 各求导一个图；`G_{xy}`、`G_{y'x}` 蓝色无圈；允许 `y' = x`。

## D258 · `lem_wardineq_K` 的 `π = ∅` 一行只写了 `σ_n ≠ σ_1`（2026-10-04，T2122a；KL12 `Loop/KLWardIneq`，1cd777f）

论文 `A_deterministic_estimates.tex:816–818` 把最后一片叶子写成 `Θ^{(+,−)}_{t,a_n b_n}`（即 `σ_n ≠ σ_1`），而引理是对 `max_σ`；`σ_n = σ_1` 时 Lean 用绝对值界（短程叶子）。论文的小缺口，陈述不变。`KLwardIneqPin_holds` 证出：KL10–KL12 完成。

## D259 · `(eq:K-pi-bound_partial)` 的归纳（2026-10-04，T2122b；KL12，1cd777f）

同 D238：对标准 `K^{(π)}` 按顶点数归纳，求和标号放在最后，不按分子数归纳 `K̃^{(π)}`；指数与论文同（`B^{l−1} · η⁻¹B^{n−l−1}`）。

## D260 · `(eq:K-pi-bound_partial)` 对 `n ≥ 3`（2026-10-04，T2122c；KL12，1cd777f）

`(eq_K-Kpi)` 与 `K^{(π)}` 只在 `n ≥ 3` 有定义（`KLgen` 在长度 2 用 `kTwo`）；`n = 2` 是 `(Kn2sol)`。

## D261 · `StepDecompN` 去掉 `[NeZero k]`、`Ugen` 用合并的形式（2026-10-04，T2121a；ST2-30 `Induction/StepDecompN`，45ca385）

`stoppedEdgeN`、`SubGaussStopN`、`Ugen_stepZCN`、`Ugen_stepYCN`、`StepDecompN_subGaussStopN_zvecN` 去掉 `[NeZero k]`（更强，同 D204、D233）；`Ugen` 是合并的 `Ugen d L g`，`g = sz.lam n`。形式事项。`dirDerivN` 作为第七个词汇定义（Amend 1），ST2-32 从此文件导入。

## D262 · 涨落增益阈值引理的下界与权（2026-10-04，T2123a；S1-28 `Green/FlucThreshold`，aa6e061）

`flucGain_of_localLaw` 用论文的下界 `W^{-d/2} ≤ Ψ`（`3_5:27`，接 D213/T2108a）与有界权 `c = W^{-d} ≤ ρ²`（D192/§30），不是 RBM2D 的 `W⁻¹ ≤ Ψ`、`c = W⁻²`；RBM2D 的结论项在 `d = 3` 为假（`flucThreshold_literal_false`，只在 `n = 3` 编译）。`hsmall_of_highProb` 与 RBM2D 同，清掉 S1-26 的 `hsmall` 欠账（D247）。`PolyLo`、`PolyHi`、`detFlucDelta` 是 Lean 从 `Ω(t,c)` 到矩界的内部过渡，论文无对应。

## D263 · 序列层 `ML:Kbound`、`lem_wardineq_K` 要 `N → ∞`、体内能量与 `lam` 的范围（2026-10-04，T2125a；KL14a `Loop/KLFinal`，471b643）

钉文 `STKbound sz E`（任意 `sz`、任意 `E`）照字面为假：`KLFinal_not_stKbound`（`L ≡ 3, W ≡ 1, lam ≡ 1/2`，`k = 2`，`τ ≡ 0`）；`STKward` 同形。Lean 证的是条件形式 `stKbound_holds`、`stKward_holds`：`SizeTendsto`、最终 `|E n| ≤ 2 − κ`、最终 `0 < lam n ≤ gmax`；`STFlow`（`stKbound_of_flow`、`stKward_of_flow`）与 `S1Std`（审核 §3 编译核对）都提供这些。论文的序列层陈述隐含这些条件。钉文不改；以之为前提的消费者（`Step1Setup.lean:671,693`、`Step34Pins.lean:255`）照旧，可在使用处用上述定理卸掉。

## D264 · `KLPT` 由 PT 证明得出时的常数（2026-10-04，T2125b；KL14a，471b643）

`Prop5Short ↦ KLShort` 取 `κ' = min κ 1 / 2`；`Prop6/7/8 ↦ KLDiffOne/Two/KLZero` 取 `m = I`、`κ'' = 1`；`m(+) m(−) = 1`。`KLoopBound_KLK`：`KLoopBound` 对 `K = KLK` 在 `|E| < 2` 下成立（`KLoopBound` 登记行删）。KL10–KL14a 完成：`KLPT_holds`、`KLbound_holds`、`KLwardIneq_holds` 无条件（`3 ≤ d`）。

## D265 · `claim:size` 里 `scalemole` 换成确定性的 `L¹` 剥树界（2026-10-04，T2124a；LW-09 `Graph/LWSizeClaim`，dd1748c）

`scalemole`（`7_8:190-193`，局限在 `W (log W)^{3/2}` 内）在 `claim:size` 的证明里换成 `lwForest_sum_le`、`LGraph.waved_sum_le`：每条树边付 `K₁`（`S`、`S^±` 的行列和），其余波边付入口界 `K₀ W^{-d}`，每个内分子付 `N`；没有 `W^{-D}` 误差，也没有 `log W`。局限本身另存为 `lwKernel_tail`、`lwTail_log32`。

## D266 · `claim:size` 是确定性的（2026-10-04，T2124b；LW-09，dd1748c）

论文 `7_8:264-266` 只陈述、不证。Lean 逐样本证明：入口界 `|G_xy| ≤ Ψ`（`x ≠ y`）、`|G_xx − m| ≤ Ψ` 作假设，任意 `Ψ ≥ 0`，不要窗口 `W^{-d/2} ≤ Ψ`，不要 `N^τ`；论文的 `≺` 取 `Ψ := N^τ Ψ_t` 得到（`LGraph.scalingSize_mul`）。随机情形下这两条假设是 `STGbEXPii`/`STGbEXPij`（S1-30），LW-08 要逐样本供给。

## D267 · `(eq:estSpm-W)` 要 `0 < g` 与体内能量（2026-10-04，T2124c；LW-09，dd1748c）

对 `0 < g ≤ Λ`、`|E| ≤ 2 − κ` 证出，常数依赖 `(d, Λ, κ)`（性质 5s 的钉文要 `0 < g`）。DECISIONS §29 的"`|E| < 2`、常数不依赖 `E`"在这里为假：`sup_y |S^+_{0y}| e^{|y|/2}` 在 `E → 2` 时发散（预检脚本 3）。

## D268 · 衰减用块 `ℓ¹` 距离（2026-10-04，T2124d；LW-09，dd1748c）

衰减用 `lwBdist`（`[x] − [y]` 的周期 `ℓ¹`）陈述，不是论文的 `|x − y|/W`（细格 `ℓ^∞`）。二者差一个因子 `e^{cd}`，报告里有论证，未形式化（审核 O2）。

## D269 · `S̃₃` 按剖面分区，`(eq:MG_conclusion3)` 对一切 `D > 0`（2026-10-04，T2118a；ST2-11 `Induction/EMn2Exp2`，6329018；DECISIONS §35）

论文 `3_5:885-886` 的 `Σ_c[𝒯+W^{-D}][𝒯+W^{-D}]` 含 `W^{-2D}Σ_c 1`，要 `D ≥ (d−2) log_W ℓ_t`。Lean 在 `𝒯̃(|c'−b|) ≤ 𝒯̃(|a−b|)` 处把 `S̃₃` 分两块：这一块照 `S̃₁` 用收缩不等式，另一块用六腿 Hölder 与 `(TTT2)`；结论对一切 `D > 0` 成立。论文的小缺口，陈述不变。

## D270 · `stEMn2Exp_holds` 带 `3 ≤ d`（2026-10-04，T2118b；ST2-11，6329018；DECISIONS §36）

输入 `EKPropTInf`、`KellStarEv` 只对 `d ≥ 3` 陈述；所有消费者都在 `STStep2 d := 3 ≤ d → …` 之下。钉文 `STEMn2Exp` 不改，登记行删。

## D271 · 六条腿用 2-圈与 Hilbert–Schmidt 范数（2026-10-04，T2118c；ST2-11，6329018）

论文 `3_5:871, 876` 用 `(GijGEX)` 界六条腿；Lean 用三个 2-圈与 Hilbert–Schmidt 范数（同 T2102a、T2109c），不需要入口界。

## D272 · `(eq_L2-J)` 的小项是 `W^{-d}`（2026-10-04，T2118d；ST2-11，6329018）

`3_5:872-875` 远场的小项在 Lean 里是 `W^{-d}`（`D_K = D + d`），不是 `W^{-D}`；最后一步 `(Ĵ + W^{-d})³ ≲ Ĵ³ + (W^{-d}B_{t,0})^{1/2}` 最终成立。

## D273 · `3_5:886` 最后的 `≲ η_t⁻¹`（2026-10-04，T2118e；ST2-11，6329018）

是 `(1−t)⁻¹ ≤ η_t⁻¹`（`Im m ≤ 1`），这里不用体内假设。

## D274 · FA/IBP 在论文的下界 `W^{-d/2} ≤ Ψ` 下（2026-10-04，T2126a；S1-30 `Green/GbEXP`，0ce09c2）

接 D213、D262：`fixedTimeFAThm`、`ibpDetThm` 用 `W^{-d/2} ≤ Ψ`（`3_5:27`）与 `W^d ≤ N`，不是 RBM2D 的 `W⁻¹ ≤ Ψ`、`W ≤ size`。

## D275 · 涨落平均的权是有界权（2026-10-04，T2126b；S1-30，0ce09c2）

接 D192（§30）：行族 `c = W^{-d}`、`#A = (2d+1) W^d`，块族 `c = W^{-d}`、`#A = W^d`（`BoundedWeight`）；即 `jasdu`（`Acta:4571`：`0 ≤ |t_k| ≤ W^{-1}`、`Σ|t_k| ≤ 1`）的 `d` 维形式。

## D276 · `lem_GbEXP` 与 Step 1 在 `3 ≤ d` 下证出（2026-10-04，T2126c；S1-30，0ce09c2）

`fixedTimeFAThm`、`ibpDetThm` 带 `hd : 1 ≤ d`（D200、D201 的样式；`1 ≤ d` 可由 `SizeTendsto` 推出）；`gbEXPV3 : GbEXPV3Theorem d`、`stGbEXP_holds : STGbEXP d`、`stStep1_holds : STStep1 d` 带 `hd : 3 ≤ d`（§36）。登记删 `GbEXPV3Theorem`、`FixedTimeFAThm`、`IBPDetThm`、`STStep1`。**ST-1 完成。**

## D277 · 旧传播子接口与退役 K 环假设从 Lean 中删除（2026-10-04，T2127a；KL14b 清理，b06ff9b）

`ThetaDiffOne`、`ThetaDiffTwo`、`structure PropTH`（照字面为假，DECISIONS §14）及其反例定理、`KTreeRep`、`TwoLoopBounded`（由树表示定义与退役引理取代，DECISIONS §15）已删；四条以 `TwoLoopBounded` 为前提的定理（`Loop/Unique.lean`、`Loop/TreeThree.lean`）前提已卸去。上文 D 条目里出现这些名字的段落（行尾标 〔T2127〕）是历史记录；D12（`c ≥ 1` 为假）的数学不变，由钉文的 `c < 1` 承担，反例陈述记在 `docs/reports/T2127-prove.md` 第 5 块。K-loop 私有引理已改公开，除 `KLIndStepB.lean:13` 的一行注释与 `Induction/EMn2Exp2.lean`（审核 O1）外不再有 `open private`。登记表删去已证钉文的 owed 行（`GaussIBP`、`STKbound`、`STConArg`、`STContractPt`、`STEMn2Poly`、`MinorDiffGainUpTo'`、`GijOmegaSeq` 等，见报告 Block 7）。**KL gate 完成**（KL13 可选）。

## D278 · `STKcalDecay` 要 `W^{-Q} ≤ g`（2026-10-04，T2129a；S3-06 `Induction/KDecay`，dab074c；DECISIONS §37）

没有 `g` 的下界时为假（`|𝒦^{(3)}| ≈ g⁻⁴`）；论文由 `(eq:WO)`（`W^{-d/2+𝔡} ≤ λ`）得到，`Q = d/2`（编译于 `inst_stKcalDecay_admissible`）。

## D279 · `𝒯_t` 的格点和用块 `l^∞` 距离（2026-10-04，T2129b；S3-06，dab074c）

`Σ_a 𝒯_t(|a|_∞) ≤ C_∞(d)(1−t)⁻¹`，`C_∞(d) = d^{d−2} 2^d radC(1/d) + 1`，对 `L ≥ 1`、`g ≥ 0`、`t < 1` 一致；常数较粗（避开 `√d`），预检表最大值 223.9。

## D280 · `(eq:sumtwoloop)` 的第二个 `≺`（2026-10-04，T2129c；S3-06，dab074c）

`stSumTwoLoop`：确定性不等式，常数 `C = C_∞(d)`，最终成立，条件 `𝔠d · C_d ≤ 1/30`（`stSumTwoLoop_exists`：`𝔠d = min(1/100, 1/(30 C_d))`，T2041e 的量词次序）。第一个 `≺`（含 `+W^{-D}`）是 Step 2 钉文 `STGdecayW`，不在此证。

## D281 · `STKbound`/`STKward` 在 `[s,t]` 上一致（2026-10-04，T2129d；S3-06，dab074c）

`stKbound_timeIcc`、`stKward_timeIcc` 要 `0 ≤ s n ≤ t n < 1`（对一切 `n`）与 `stKbound_holds` 的前提；论文的"关于 `u ∈ [s,t]` 一致"没有单独陈述。

## D282 · S3-06 的维数条件（2026-10-04，T2129e；S3-06，dab074c）

`stKcalDecay_holds`、`stKbound_timeIcc`、`stKward_timeIcc` 带 `3 ≤ d`（§36）；`KDecay_sum_tailT_le`、`stSumTwoLoop` 带 `2 ≤ d`。

## D283 · `(initialGT2)` 的控制取 `max(W^{-d/2}, (W^{-d}B_{u,0})^{1/2})`（2026-10-04，T2130a；ST2-16+17 `Induction/LocalAvg1/2`，3389d24）

论文的 `(W^{-d}B_{u,0})^{1/2}` 只在常数 `cB < 1` 之内满足下窗口 `W^{-d/2} ≤ Ψ_u`（`ST_Bdata_holds`）；`Ψ_u² ≤ (cB⁻¹ + 1) W^{-d}B_{u,0}`。同 T2040a/D93 的办法。

## D284 · `stLocalAvgOfL2_holds` 带 `3 ≤ d`（2026-10-04，T2130b；ST2-16+17，3389d24）

§36；钉文 `STLocalAvgOfL2` 不改，登记行删。

## D285 · `(initialGT2)` 的 `ε₀` 取一个固定值（2026-10-04，T2130c；ST2-16+17，3389d24）

Lean 里 `ε₀` 存在量化（只经 `c` 依赖 `d, 𝔠, 𝔡, ε`），即论文"小常数 `ε₀`"；T2015d 对 `lem_GbEXP` 读作一切 `ε₀ > 0`，这里用一个值即可。

## D286 · 虚部翻转取 `b = false` 坐标（2026-10-04，T2131a；LW-08a `Graph/LWSymm`，a871db4）

`Gauss/FineModel.lean:105-109` 里虚部是 `(i, j, false)` 坐标；翻转它保持 `seqP`，且 `G(ω') = G(ω)ᵀ`。票面写的翻 `b = true`（实部）给出 `X(ω') = −X(ω)ᵀ`（编译反例 `lwSymm_flipLit_ne`）。形式事项。

## D287 · 图共轭用同一份数据（2026-10-04，T2131b；LW-08a，a871db4）

`Γ.conj.val D = conj(Γ.val D)`，数据 `D` 不变（红边本来就读 `star G`）；按"共轭数据"的读法为假（`lwSymm_conj_literal_false`）。

## D288 · 共轭交换彩色波边的两端（2026-10-04，T2131c；LW-08a，a871db4）

`conj S^+_{xy} = S^-_{yx}`（由 `WEdge.val`）；黑色波边 `S` 为实，不变。

## D289 · `(Owx)` 对任意顶点（2026-10-04，T2131d；LW-08a，a871db4）

外部顶点 `x : E` 与内部顶点一样展开；合并的 `owxT1…owxT4` 是其内部情形（`owxET*_inr`）。论文的 `ssl` 只写内部顶点。

## D290 · 带圈非自环选定边（2026-10-04，T2131e；LW-08a，a871db4）

T2128 (a) C4 由 `M a b = 0` 加两端之间的 `×` 点边处理（正规图对每条非自环实边都有，`defnlvl0` (iii)，`lwSymm_hX_of_normal`），不靠消去 `m δ_{xy}` 项。

## D291 · 转置形式要 `S⁺ᵀ = S⁺`（2026-10-04，T2131f；LW-08a，a871db4）

作为前提携带（`lwSymm_lwSplus_symm` 对 `S⁺ = lwSplus` 证出）。

## D292 · 网格 𝒬 过程的漂移写成 `𝒬_u D + ℬ₄ + ℬ₅`（2026-10-04，T2132a；S3-13a `Induction/QGridA`，549a62d）

论文 `int_K-L+Q`（`3_5:1337–1346`）写 `𝒰∘𝒬_u∘Σ_{k=1}^5 ℬ_k`；二者相等因为 `𝒫ℬ₄ = 0`（`QopAlgebra_ThetaN_sumZero`）、`𝒫ℬ₅ = 0`（`QopAlgebra_Psum_deriv`），故 `𝒬_uℬ_k = ℬ_k`（同 RBM2D #130）；此桥本票未证。

## D293 · `ϑ` 的二阶时间正则性（2026-10-04，T2132b；S3-13a，549a62d）

Lean 用 `‖ϑ_v − ϑ_u − Δ∂_uϑ_u‖ ≤ C₂(1−v)⁻²Δ²`；论文 `eq:derv_Theta` 只给一阶。对合并的磨光子（平滑尺度，T2041b）证出，不进 `STMollifierProps`；只用一阶界的余项与 `K` 无关，求和不收敛（预检）。

## D294 · 张量指标 `m + 1`（2026-10-04，T2132c；S3-13a，549a62d）

`m ≥ 1` 代替 `n ≥ 2`，不要 `[NeZero k]`。形式事项。

## D295 · 时间可微性在 `[0,1)` 上逐点（2026-10-04，T2132d；S3-13a，549a62d）

一般定理要 `t ↦ ϑ_t(a)` 在 `[0,1)` 每点 `DifferentiableAt`，`STMollifierProps` 只给 `DifferentiableOn (Ico 0 1)`；假设只在尺寸 `n` 处，另要 `0 < lam n`。

## D296 · `lem_decayLoop` 不用 `(GijGEX)`（2026-10-04，T2133a；S3-07a `Induction/DecayLoopA`，6179d8c）

论文 `3_5:1113` 用 `(GijGEX)` 得到一般 `G` 圈的衰减，`lem_decayLoop`（`3_5:1126-1127`）列 `(Gt_bound_flow)`、`(Eq:Gdecay_w)` 为前提；Lean 用 Cauchy–Schwarz 切割，只从 `(+,−)` 2-圈衰减得出，前提更弱。

## D297 · `stDecayLoopAt_holds` 带 `3 ≤ d`（2026-10-04，T2133b；S3-07a，6179d8c）

来自 `stKcalDecay_holds`（§36）。

## D298 · `res_decayLK` 的写法（2026-10-04，T2133c；S3-07a，6179d8c）

论文界 `|𝓛| + |𝒦|`，Lean 界 `|𝓛| + |𝓛−𝒦|`（相差因子 2，归入 `≺`）；含 `k = 1`（空真）；`τ' = ε`；按时刻 `≺`，误差 `W^{-D'}`。关于 `(σ,a)` 一致的形式未证（审核 O4）。

## D299 · `(Eq:Gdecay_w)` 的前因子（2026-10-04，T2133d；S3-07a，6179d8c）

`P' = max(((1−s)/(1−u))^{Cd} Bctl^{1/5}, 1)`，`C₀ = max Cd 0 + 1`；论文不追踪（RBM2D 用 `P = (η_s/η_u)^4`、`C₀ = 4`）。

## D300 · 割的衰减引理无论文钉文（2026-10-04，T2135a；S3-07b `Induction/DecayLoopB`，250a118）

`LoopDecay`（`zdistInf`）、窗口和 `(2R+1)^d M + L^d δ`、`glueTerm`、`eeLoop` 标号引理：论文只陈述 `Def_decay`（`3_5:1115`）与 `lem_decayLoop`（`3_5:1126`）。窗口与粘接引理带 `3 ≤ L`。

## D301 · 衰减输入关于 `u` 一致（2026-10-04，T2135b；S3-07b，250a118；DECISIONS §39）

`STDecayLoopU`（`Prec`）由 `STGdecayW`（`Prec`）得到，代替按时刻的 `STDecayLoopPT`/`STStep2DecayPT`；论文 `(Eq:L-KGt-flow)`（`1_2:1371-1373`）的 `∀ u ∈ [s,t]` 本在 `≺` 之内。

## D302 · `ℰ` 项标号衰减的写法（2026-10-04，T2135c；S3-07b，250a118）

`stEtermDecay`：`STksimLK` 对一切 `l`（论文 `3 ≤ l ≤ n`，`3_5:1027`）；`STee` 作为 `(a, a')` 的 `2k` 标号张量；`l¹ → l^∞` 换算 `ε → ε/2`；另要 `0 ≤ s ≤ t < 1`、`|E| ≤ 2 − κ`、`Admissible`。`STGdecayW` 仍 owed（Step 2 链）。

## D303 · 磨光子常数 `c` 对一切实数（2026-10-04，T2136a；S3-19 `Induction/B45`，1ef8fa7）

钉文对 `C, c ∈ ℝ` 量化（`STMollifierProps`），论文 `3_5:1214` 是 `c > 0`；Lean 对一切实 `c` 证出（`c < 0` 时上界多 `2 max(0, −log g) ≤ log N`，归入 `N^{τ₁}`）。更强。

## D304 · `(ℓ_u^d η_u)⁻¹ ≲ B_{u,0}` 对一切 `u < 1`（2026-10-04，T2136b；S3-19，1ef8fa7）

论文 `3_5:1264` 在 `1 − u ≥ g²/L²` 下陈述；Lean 的 `ellT`、`Bparam` 下对一切 `u < 1` 成立，常数 `2/Im m_E ≤ 4/√κ`（`B45_scale`，`d ≥ 2`）；两个钉文的证明不用情形 (i) 条件。

## D305 · S3-19 只用 Step 2 结论的 `STGdecayW`（2026-10-04，T2136c；S3-19，1ef8fa7）

加上 `Ξ̂ ≺ X`；比 `STIngR` 提供的前提少（同 T2041i）。

## D306 · 偶数 `m` 时钉文为空（2026-10-04，T2136d；S3-19，1ef8fa7）

`m + 1` 为奇数时 `STAlternating` 为空（编译了 3、5 个指标），两个钉文在偶数 `m` 无内容；实例取 `m = 1, 3`。观察。

## D307 · `lvl1 lemma` 的数据假设（2026-10-04，T2128a；LW-08 `Graph/LWLvl1`，c967b9c）

除三个合并的 `*_graph_E` 外另要 `Spᵀ = Sp`（T2131；`lwSymm_lwSplus_symm` 在 `0 ≤ u`、`‖m‖²u < 1` 时对 `S⁺ = lwSplus` 证出）与 `M a b = 0`（`a ≠ b`，§38 C4）。

## D308 · 截断用 `ord ≥ K`（2026-10-04，T2128b；LW-08，c967b9c）

代替 `(eq:smallsize)`（`B:140`）；`errs` 里也可有阶 `≥ K` 的局部标准图；`lvl1_size_le` 常数 1，需 `1 ≤ W`、`1 ≤ L`、`L^d ≤ W^{K₀}`、`W^{-d/2} ≤ Ψ ≤ W^{-c}`，给出 `size ≤ W^{-D}`。

## D309 · `(Oe1x)` 的 `m 1_{x=y₁}` 与 `(Oe2x)` 的 `R1` 不出现（2026-10-04，T2128c；LW-08，c967b9c）

在正规图上取值为 0，`LocStep` 的输出里略去。

## D310 · 终止度量（2026-10-04，T2128d；LW-08，c967b9c）

`(K − ord, nLoops, nS, nPairs)` 字典序，代替预检的 `(·, w, Φ, n_S)`；内部事项，陈述不变。论文引 [yang2021] Lemma 3.22 不证，此处证出。

## D311 · 正规权分解放在 partition 里（2026-10-04，T2128e；LW-08，c967b9c）

`(G_αα − m) + m` 由每个输出的 `LGraph.partition m` 完成，不在 Step 1 内（`B:138-145`）；引理对正规打包图陈述。

## D312 · `(bEwGn)` 的证明要循环旋转（2026-10-04，T2137a；S3-08 `Induction/SEforLn1`，7f82dd6）

`(yi2oslxj2)` 对最后一个标号求和，而 `cut_k^{(b)}` 的粘接标号在第 `k` 位；论文 `3_5:1048-1053` 未提旋转。证明细节，陈述不变。

## D313 · `(eq:KsimL-K)` 用 `𝒦` 的循环不变性（2026-10-04，T2137b；S3-08，7f82dd6）

二阶项的求和标号在第 `k < l` 位，先用 `KLK_rotate` 再用 `(wardineq_K)`；论文 `3_5:1054-1061` 未提。

## D314 · `(eq:KsimL-K)` 不需 `(eq:bcal_k)`（2026-10-04，T2137c；S3-08，7f82dd6）

只用 `(wardineq_K)`；论文 `3_5:1056` 引的 `(eq:bcal_k)` 用不到（圈数 `≤ 2m²` 归入 `N^τ`）。观察。

## D315–D324 · Step 5 钉文（2026-10-04，T2134a–j；ST-D4 设计，3668596；签字 §40）

- **D315（T2134a）**：`lem:newKLK` 在 `ℓ = L` 取锐形式 `C/(1−u)(Ĵ² W^{-d}𝒯̃^L + Ĵ W^{-d-D})`（`STNewKLKL`）；论文印的 `(juwo=Lklk)` 带 `Ĵ + Ĵ²`，对情形 (i) 弱 `ρA^{1/30}`；依据论文 `3_5:1968` 的注。
- **D316（T2134b）**：`TailtoTail` 用 `def_WTuD` 的 `T_{u,D}`，显式常数 `C_d² T_{t,D} + ((1−s)/(1−t))² W^{-D}`，`0 ≤ s ≤ t < 1`、`g² ≤ 1−t`，一切荷、`zdistInf`（§33 更正）。
- **D317（T2134c）**：`lem_dec_calE` 写成 `Prec`：控制量 `J*_{u,D} ≥ 1` 为假设函数，`W^D ≥ N` 为 `∀ᶠ n, size ≤ W^D`，关于 `u ∈ [s,t]` 一致。
- **D318（T2134d）**：`lem:pf_step5` 写成"对一切 `D > 0`，`max|𝓛−𝒦|/T_{u,D} ≺ 1`"（论文：小 `ε` 时 `T ≥ t` 高概率）。
- **D319（T2134e）**：`(eq:bound_isolated)` 论文引用，此处钉为 `STCltIso` 并内部证明（S5-17…S5-21）。
- **D320（T2134f）**：`lem;CLT` 以 `(eq:ells_to_ellt)`、`(eq:ells_to_ellt2)` 为指标集条件，`σ₁ ≠ σ₂`；`d ≥ 3` 的两标号形式保留 `1/(|a₁−a₂|^{d−2}+1)`，矩和要 `(d−1)k > d`（`d = 3` 时 `k ≥ 2`），单点由隔离去掉。
- **D321（T2134g）**：情形 (ii) 钉为 `STDuhamelII`（异号用 `Q^{(1)}`，同号不用）、`STIniTermII`、`STWardII`；论文"类似论证、从略"（`3_5:2253, 2268`）；闭合用一个 `ρ`：`(1−s)²‖Θ̊‖‖Θ‖ ≤ ρ(1−s)L²/g² ≤ ρ`。
- **D322（T2134h）**：`(iksjuwjx0)` 用 `A^{-1/5}W^{-d}𝒯̃^L_{u,D} + W^{-D}` 代替 `A^{-1/5}W^{-d}𝒯_t + W^{-D}`（`≺` 下等价）。
- **D323（T2134i）**：`𝔼𝓛^{(2)}` 的平移/反射不变性（`3_5:2196` 非正式使用）钉为 `STExpInv`；`STDecayStrongU` 的指标集为 `g² ≤ 1−t`（否则空），同合并的 `STDecayStrong`。
- **D324（T2134j）**：积分层级 `(iois-mtx2)`（`3_5:2067`）条件化钉为 `STDuhamelConcl`：对一切确定的 `F ≥ 0`，初始项 `≺ F` 则 `Q∘(𝓛−𝒦)_u ≺ F + A^{-1/5}W^{-d}𝒯̃^L_{u,D} + W^{-D}`，关于 `u` 一致。
- 另：`(eq:assmtlarge)` 不能在具体 `W` 实例化（大 `ρ` 分支要 `log W ≳ 1.26·10⁴`），钉文不假设它，证明两支都处理（F-E）；情形 (iii) 强估计推弱估计只差一个多对数，`≺` 吸收（F-G）。
- **D325（T2140a）**：`(eq:bound_isolated)`（`3_5:2245`，引 [DYYY25] (7.39)）的证明第一块（S5-17，`Evolution/CltSwap`，f22c63c）：独立副本 `H'` 与逐坐标交换的路线论文里没有；伸缩和对 `2(WL)^{2d}` 个实坐标求和，不是对 `i ≤ j` 的矩阵元；陈述与 RBM2D 同（换模型 `PF d L W g`）。
- **D326（T2139a）**：`(eq:sumtwoloop)` 在运行时刻 `u ∈ [s,t]` 上用，`(con_st_ind)` 只取弱形式 `B_u^{𝔠_d} ≤ (1−u)/(1−s)`、`B_u ≤ 1`（`u = s` 时严格的 `< 1` 不成立）；S3-09 `Induction/SEforLn2`，ae259a6；私有副本 `SEforLn2_sumTwo_pt`。
- **D327（T2139b）**：`(eq:sumtwoloop)` 里 `W^{−D}` 项的吸收用 `D = 2/𝔠` 与 `W ≥ N^𝔠`（`Bandwidth`，`(Main_DEL_COND)`），不是票面写的 `(eq:WO)`；`lem:SEforLn` 全文（`STSEforLn`）在 `3 ≤ d` 证出，登记行删除。
- **D328（T2141a）**：`(eq:bound_isolated)` 证明里的远距矩阵元衰减取对数尺度：远集 `{c (log W)^3 ℓ_τ ≤ |[x]−[y]|_∞}`（每个 `c > 0`），`|G_xy| ≺ W^{−D'}`（`STFarEntryAtLog`，S5-19 `Evolution/FarEntry`，3b1c6a5；§43）；RBM2D 用 `W^{τ'}ℓ`。论文此处引 [DYYY25, (7.39)]，无证明。
- **D329（T2141b）**：`stFarEntryAtLog` 需要 `0 < ε`（`STGbEXPij` 的量词，论文 `𝐃_{κ,ε}`），不需要 `s < t`；结论对两种荷与一切细格点对 `(x,y)`。
- **D330（T2144a）**：替换步的局部形式带标号数 `k`（`LocalForm d L W k K`、`…Multi` 形式）；RBM2D 只有 `k = 1`（S5-18 `Evolution/CltResolvent`、`CltPath`，5a8f89e）。
- **D331（T2144b）**：`CltFarGeomNear` 以局部半径 `ρ`、隔离距离 `R` 为参数，结论 `R/2 − ρ − 1`；RBM2D 为 `w ≥ 6`、`ρ = ℓw`、`R = w²ℓ`（§43 的对数尺度要用线性形式）。
- **D332（T2144c）**：`CltCoordAdj` 显式带 `g`、不要 `3 ≤ L`，邻接用 `zdistInf ≤ 1`（`S^{(B)}` 支撑 `2d+1` 点，`∞` 球 `3^d` 点）。
- **D333（T2144d）**：`cltGoodAt`/`CltPathBound` 以远距门槛 `θ ≤ R/2 − ρ − 1` 为参数（RBM2D：`ρ = ℓ W^τ`）；`gEntry` 即合并的 `Gres` 矩阵元。
- **D334（T2147a）**：`TailtoTail` `(neiwuj)`（`3_5:2344-2362`）对一切实数 `D` 成立（论文：某个 `D > 0`，`≲`），显式常数 `C = (3 e^{(4d+1)/4})²`（S5-04 `Induction/TailtoTail`，37f3a22；`STTailtoTail` 证出，登记删）。
- **D335（T2147b）**：证明路线不用 `(prop:ThfadC)` 与论文的连续微积分事实（`3_5:2365`，从略）：改用加权预解式界 `Σ_b Θ_t(a,b) e^{c|a−b|_∞} ≤ 2/(1−t)`，`c = 1/(4d+1)`（`g² ≤ 1−t` 区域，含边界）。
- **D336（T2148a）**：`(zYU1)` 对 `σ ∈ {(+,−),(−,+)}` 都是 `+` 号；Lean 陈述要 `H` Hermitian、`|E| < 2`、`0 ≤ u < 1`（S5-28 `Induction/WardII`，8ec98a6；`STWardII` 证出，登记删）。
- **D337（T2148b）**：`3_5:2259` 的 `Δ_u ≍ A⁻¹` 只用上界 `W^{−d}B_{u,0} ≤ 2A⁻¹`（由 `1−u ≥ ilambda²/L^d`），常数被 `≺` 吸收。
- **D338（T2142a）**：`lem:localregular` (3)–(5) 是分子多重图上的游走（每条边的出现只用一次，分子可重访），不是简单路径；不假设 `(eq:far_ab)`（`7_8:792`），`𝓜_x = 𝓜_y` 时为闭游走（LW-10a `Graph/LocalRegular`，3bf20e1）。
- **D339（T2142b）**：(5) 由不变量里的 Hall 条件携带，不用 `B:178-199` 的「路径 ↔ 分子」带标号对应（(4) 要它，LW-10b）。
- **D340（T2142c）**：`(eq:MolVW)`（`7_8:798`）对分子的一切顶点（含外部顶点）成立，比论文强。
- **D341（T2142d）**：起点图 `fxyPowGraph p`、路径不变量与 `lw_localregular_expansion` 对一切 `p`；`p` 偶只用于值恒等式。
- **D342（T2149a）**：坐标尾 `CltCoordTail` 只要 `2 ≤ d`（`W^{d−1} ≥ W`）；门槛 `W^{−1/2}` 即 `CltPathBound` 的步长（论文无显式陈述）（S5-20 `Evolution/CltGood`，4f4612b）。
- **D343（T2149b）**：替换步好事件属论文没有的 i.i.d. 副本路线；`HClt` 只用到 `STLocalEntryU` 与（经 `stFarEntryAtLog`）`STGdecayW`，不用 `STAvgU`。
- **D344（T2149c）**：`CltGoodWhp` 的远距门槛取序列 `θ n ≥ c (log W)^3 ℓ_τ`（消费者的 `θ = 4(log W)^3ℓ_s − 1` 取 `c = 1`）；`cltGoodAt` 对门槛单调。
- **D345（T2146a）**：网格好集 `GoodSetN`（ST2-32 `Induction/GridGoodN`，2f246bf）不再有 RBM2D 的 (G1) `Ξ^{(𝓛)}_{2k+2} ≤ ΓΛ`、(G3) 乘积、(G4) `Ξ^{(𝓛)}_{k+1} ≤ ΓΦ` 三条；`Λ` 经 `lem:SEforLn` (4) 的参数 `q` 进入（前提 `hQ`），`Φ` 经 `hX`、`hY`。
- **D346（T2146b）**：(D1)–(D4) 的水平为 `Γ(ΓΦ)B^k/η`、`Γk(ΓΦ)²B^k/η`、`Γ(ΓΦ)B^k/η`、`Γ(ΓΛ)B^{2k}/η`，无附加 `W^{−D'}`，(D1) 无 `(k−1)`（RBM2D 为 `Γ(k−1)(ΓΦ)M^{−k}η⁻¹ (+W^{−D'})`）。
- **D347（T2146c）**：远距子句用 `ℓ^∞` 跨度 `STdiamInf` 与 `ℓ_u W^{τ'}`；`GridGoodN` 是 `STIngR` 形状的钉文，RBM2D 的 `MainIndHyp…PT` 前提逐一换成合并的一致陈述。
- **D348（T2150a）**：`lem:newKLK` 锐形式（D315）的证明用逐点近/远分割代替论文的「不妨设 `𝒯_u(ℓ) ≥ W^{−D}`」（`3_5:612-616`），`ℓ = L` 时远处取值恰为 `W^{−D}`（S5-12 `Induction/NewKLKL`，7388d13；`STNewKLKL` 证出，登记删）。
- **D349（T2150b）**：常数 `C = 10 + 2^{d−2} e C_T`、`δ₀ = κ/2`；论文「高概率、`1+o(1)`」（`3_5:640-646`）写成显式前提 `‖G_u − M‖_max ≤ δ₀`、`Im G_xx ≤ 2 Im m`（同 `STNewKLK`）。
- **D350（T2153a）**：`gridDriftN_envelope` 多一个前提 `STKbound`（KL 的条件形式，经合并的 `exists_norm_Kcal_le_win`，T2111a）；RBM2D 无条件（ST2-31 `Induction/GridEnvelopeN`，a438a51）。
- **D351（T2153b）**：`gridDriftN_envelope`、`SumWeightedStepErrN_Stmt` 去掉 `[NeZero k]`（更强）。
- **D352（T2152a）**：`(eq:bound_isolated)`（`3_5:2245-2248`，论文引 [DYYY25, (7.39)]、[RBSO1D, (A.112)]）在 Lean 中由 RBM2D 的 i.i.d. 副本 + 坐标伸缩路线证出（S5-21 `Evolution/CltStep`，74400b7；`STCltIso` 证出，登记删）；对数尺度常数 `ρ = w+1`、`R = 8w`、`θ = 3w−2`、`w = (log W)^3 ℓ_s` 论文中没有。
- **D353（T2152b）**：`stCltIso_holds` 对一切 `σ ∈ {±}²` 成立（钉文要 `σ 0 ≠ σ 1`），且不要 regime `STReg5I`：只用 `STFlow` 与 `STStep2Concl`。
- **D354（T2152c）**：`𝗕_b` 编码为局部形式，系数 `scale·W^{−2d}` 乘单项式 `G(σ₁)_{yx}G(σ₂)_{xy}`，窗口 `|b₁−b₂|_∞ ≤ w` 外为零；论文对 `𝗕` 无局部形式陈述。
- **D355（T2155a）**：`STExpInv` 对一切实数 `E`、`u` 成立（钉文带 `|E| < 2`、`0 ≤ u < 1`，未用）（S5-22a `Evolution/ExpInv`，88600b1；`STExpInv` 证出，登记删）。
- **D356（T2155b）**：`STExpInv` 对单时刻流 `H_u = √u X`（合并的 `seqHflow`，§7 的模型）证出，不涉矩阵布朗运动。
- **D357（T2156a）**：`sum_weighted_qErrQN_le` 的陈述带固定常数 `0 ≤ C`、`0 ≤ C₂`（合并的 `qStepErrN` 的参数），量词在 `∀ᶠ n` 之前；RBM2D 无（S3-13b `Induction/QGridB`，3013163）。
- **D358（T2156b）**：衰减指数用 `D_t + (m+1)`（RBM2D `D_t + k`）；张量指标 `m ≥ 1`、圈长 `m+1`，结论对一切 `p ≤ K n`。
- **D359（T2156c）**：陈述不带 `STKbound`（它在消费者处经 `gridDriftN_envelope` 进入），与 RBM2D 同为确定性陈述。
- **D360（T2154a）**：组装钉文与目标去掉 `[NeZero k]`（更强，同合并的 `SubGaussStopN`）（ST2-33 `Induction/GridAssemblyN`，686cf71）。
- **D361（T2154b）**：`YMomentsN` 照 RBM2D 把 `∃ C_P` 放在 `K` 之后，`AssembledN` 用不上；由 ST2-35 的 `YMomentsUnifN`（`C_P` 在 `K` 之前）补（§45 O3）。
- **D362（T2158a）**：`(uwp2-92kj)`、`(uwftgwesj)` 的 `≺`/`≲` 写成显式常数 `C(d, Λ)`（`0 < g ≤ Λ`，来自 `prop5Decay_holds`），不是 `C(d)`（S5-14 `Induction/Step5Kernel`，19a2b09）。
- **D363（T2158b）**：`(TTT2)` 要 `g²/L² ≤ 1−t ∨ 1−u ≤ g²/L²`（同 `EKPropTInf`）；(uwftgwesj) 带 `g²/L² ≤ 1−t ∨ 1−s ≤ g²/L²`。
- **D364（T2158c）**：**论文 `(uwp2-92kj)` 的最后一个 `≲`**，`(1−u)/(1−t) W^{−D} ≲ 𝒯̃_{t,D−1}`，对与 `L` 无关的常数不成立（`step5Kernel_profile_not_unconditional`）；正确形式：显式的 `C 𝒯_t + (1−u)/(1−t) W^{−D}`，或在前提 `(1−u)/(1−t) ≤ W^θ` 下损失 `D−θ`、`D−2θ`（论文的 `D−1`、`D−2` 即 `θ = 1`）。S5-15 须提供 `θ`（流给 `1−t ≥ N^{−κ}`、`W ≥ N^𝔠` 时 `θ = κ/𝔠`）。
- **D365（T2158d）**：`max_{u∈[s,t]}` 写成 `∀ u ∈ [s,t]` 与 `Set.Icc s t` 上的 `sSup`；`𝒜` 里 `Θ^{(+,−)}` 取 `Re Theta`；`(eq:decompU)` 要 `t ≠ 0`。
- **D366（T2159a）**：`0 ∈ GoodSetN`（`u = 0`、`H = 0`）的 (D4) 条款要 `k S_cc η_0 ≤ Γ²Λ b^{2k}`（`S_cc = (1+2dg²)^{-1}`，`b = (1+g²)^{-1} + L^{-d}`）；RBM2D `NonAltGood:996` 的 `k/5 ≤ Γ²Λ` 不照搬，单位水平 `Γ = Λ = Φ = 1` 不满足（`sz0` 上 `k = 2, 3` 门槛 1.82、2.65）；Lean 用充分条件 `Γ²Λ ≥ k(1+g²)^{2k}`（`zero_mem_goodSetN_of_levels`）。消费者（ST2-35、S3-10、S3-14）须按此传水平（ST2-34 `Induction/AzumaProxyN`，43ab861；`AzumaSubGN` 证出）。
- **D367（T2157a）**：`(eq:boundEfar)` 的 `≺` 藏了 `(log W)^{12}` 与 `log L`：Lean 的界带 `(d (log W)³ ℓ_s + 1)⁴`（窗口 `w₁ = d(log W)³ℓ_s` 的 `|r|²` 与体积）与 `1 + log(L+1)`（临界和 `Σ_b (|b−a₂|+1)^{-d}`），两者最终都 `≤ N^{τ/4}`；票面字面的 `C K (1−s)² ilambda^{-4} ℓ_s⁴` 不成立（S5-22b `Evolution/MeanFar`，a21a819；`STMeanFar` 证出）。
- **D368（T2157b）**：窗口与 `(prop:BD2)` 用 `ℓ¹`（`|r|₁ ≤ w₁`），轮廓用 `ℓ^∞`（`|x|₁ ≤ d|x|_∞`）；前提 `2w₁ ≤ ⌊ρ⌋₊ + 1`，由 `log W ≥ 2d` 给出。
- **D369（T2157c）**：均值部分对一切 `σ ∈ {±}²`、一切 `a` 成立；`σ₁ ≠ σ₂`、`(eq:ells_to_ellt)`、`(eq:ells_to_ellt2)` 只是 `STCltFarConcl` 的指标集条件，证明未用。
- **D370（T2157d）**：`≺ ⟹ 𝔼` 给出证明（坏事件上的 a.s. 包络 `η_s^{-2} + ‖𝒦^{(2)}‖`，`D₁ = 5d+19`，`D_w = (5d+13)/𝔠`）；论文对 `𝔼𝓑` 直接用 `(eq:propcalB)`，未说明。
- **D371（T2160a）**：论文用 BDG 界鞅项（`3_5:166`、`3_5:216`）；Lean 的网格游走有二阶余项 `Y`，其矩钉文 `v_j = Δ²P`、`w_j = Δ⁴P²`、`P ≤ N^{C_P}`，显式 `C_P = 11 + (4k+4)·max 0 (1−τ')`（同 RBM2D 的 T2160a/b）（ST2-35 `Induction/AzumaProxyN2`，88183f4；`YMomentsUnifN`、`yMomentsN` 证出）。
- **D372（T2160b）**：`𝔼 ω_c⁸ ≤ 105` 用 `gvarF ≤ 1`，需 `3 ≤ L`（`sum_sbKernelR`），写作 `sz.three_le_L n`（同 T2001a）。
- **D373（T2160c）**：`YMomentsUnifN`（`C_P` 在网格 `K` 之前）是 `AssembledN` 能用的形式；合并的 `YMomentsN` 保留，由 `yMomentsN_of_unif` 推出（陈述形状，非论文差异）。
- **D374（T2164a）**：`lem_dec_calE` 的前提「`W^D ≥ N`」（`3_5:2317`）对这里证出的 `res_deccalE_lk` 不够，用的是 `L^d W^{2d} ≤ W^D`（约 `N² ≤ W^D`）；因 `T_{u,D}` 随 `D` 递减，下游无碍（S5-05 `Path/LemDecCalE`，6e63fbc）。
- **D375（T2164b）**：`gexRHS` 的邻对（`zdistInf ≤ 1`）在 `d = 3` 是 `9^d = 729` 对，不是 portmap 的 `(1+2d)² = 49`（常数）。
- **D376（T2164c）**：`M_u = W^d(1−u)`（不带 `Im m`，`ℓ_u = 1`）；尾函数 `tailTD`（幅度 `M_u^{-2}`）；`E2Hyp` 不带 `s`、`v`（与 RBM2D 不同）。
- **D377（T2164d）**：`lossE2` 的首常数 `10^12 (1600 d⁴)^d`、对数 `log(L^d W^{2d})`；卷积常数 `S_d = (1+1536 d⁴)^d`（非最优）。
- **D378（T2163a）**：`(zYU2)` 的第二项 `(1−s)²(Θ̊_t(𝓛−𝒦)_sΘ_t)_a` 是精确展开 `Q^{(1)}𝒰^{(2)}_{s,u}X = [(s/u)(I − L^{-d}J) + ((u−s)/u)Θ̊_u] ⊗ [(s/u)I + ((u−s)/u)Θ_u] X` 的 `β²` 项，另三项在 Lean 中另行界住；`(u−s)/u ≤ 1−s`（S5-27 `Induction/IniTermII`，69b1099；`STIniTermII` 证出，登记删）。
- **D379（T2163b）**：`3_5:2275-2281` 里传播子的时间是指标的运行时间 `u ∈ [s,t]`（论文写 `t`）；输出的下限是 `((1−s)/(1−u)) W^{-D'}`，不是 `W^{-D}`，取 `STDecay` 的 `D' = D + 1/𝔠` 即 `≤ W^{-D}`。四个 `≲` 本身都成立。
- **D380（T2163c）**：票面的实例数据（`L = 3`、`g = 1/2`、`s = 15/16`）不在情形 (ii) 内；实例改用 `L = 4`、`g = 1`（票面笔误，非论文差异）。
- **D381（T2163d）**：核心常数依赖 `(d, Λ, κ_m)`（`Λ = 𝔡^{-1}`、`κ_m = √(κ(4−κ))/2`），不是论文的 `C(d)`（同 D362）。
- **D382（T2162a）**：`M_{y,α}`（论文引 [DYYY25] (2.24)，d ≥ 3 未定义）读作按 `S^{(B)}` 权重的加权平均 `N Σ_x |ψ_α(x)|² S°_{xy}`（权和为 1、至多 `2d+1` 块），`ℙ(𝓑(y)) ≤ (2d+1)·ℙ(QUE 坏)`（RBM2D 是五个等权）（UN-D1 设计，T2162 合并 04aedec，探针在 `t/T2162`）。
- **D383（T2162b）**：Thm 2.4 的证明除论文列出的 `MR:decol`、`MR:locSC`、`(Meq:QUE)`（`1_2:567-568`）外，还要 `𝐇_t`（`t ≤ N^{-1+τ_U}`）的 QUE 与对角 local law、`ML:GLoop`/`ML:GLoop_expec`/`ML:GtLocal` 沿 `z` 序列的输出、弱 GUE local law；论文只写「同 [YY_25] §7.2」（同 RBM2D paper-delta #95/#139）。按 §50 内部证明（GUE 相 28 张）。
- **D384（T2162c）**：`(Meq:QUE)` 的窗口只用到 `W^{-ε₀}(λ∧1)W^{d/2} ≥ W^{2𝔡/3}`（脚注 `1_2:372`），`λ` 与 `λ∧1` 两种读法都可。
- **D385（T2162d）**：`UNGreenCorr` 对伸缩序列 `r_n ∈ [a,b]` 陈述（BA 的密度 `ρ_N(E)` 随 `n` 变；带状模型 `r ≡ 1`）（设计形状，非论文差异）。
- **D386（T2162e）**：`τ_U` 的范围：Step 1 中 `τ_s ≤ 𝔠𝔡`，`τ_U ≤ c'/(2(C_n+1))`，`c' = 𝔠𝔡/30`（d ≥ 3 是 `ℙ(𝓑)` 起约束，RBM2D 是 θ）；RBM2D 的常数 `C = 3n_f+16`、`C_n = 1` 要按 d ≥ 3 重算。
- **D387（T2162f）**：§11 的 BA 形式是 `UNUnivDilAt`，`ρ_n = π⁻¹ Im m_n(E+i0)`（与 §51 的体内条件一致）。
- **D388（T2162g）**：票面的 `L ∈ {W^{1/𝔠−1}}` 是 d = 1 的形式，d ≥ 3 为 `L ≤ W^{1/(d𝔠)−1}`（`un_dc_lt_one`）（票面笔误，非论文差异）。
- **D389（T2151d）**：lem:localregular 性质 (4) 用带颜色的精确不变量证（同色 walk、每条非环分子边恰在一条 walk 上、颜色访问条款），不是 `B:178-199` 的带标号对应「walk `i` ↔ `M_i`」；是 walk 不是简单路径，不用 `(eq:far_ab)`（同 T2142a）（LW-10b `Graph/LocalRegular2`，32d895b）。
- **D390（T2151e）**：`B:197` 中被拉出的 `Ḡ` 边落在分子内部（或是权）的情形是 `localReg2_Fam.thr` 的闭合绕行，要用不变量的 (c) 条款处理权与分子内部的边（论文从略）。T2151a–c（性质 (6) 的远离假设、`B:232-249` 情形 (iii)(iv) 声称 Δord ≥ 2 实测 0、`B:275-277` 的步进断言 (E) 不成立）留给 LW-10c 编号（§47，Fable 报告 `docs/claude-team/fable/2026-10-04-localreg6.md`）。
- **D391（T2165a）**：`(eq:pairingcond)` 论文写 `≤`，Lean 取严格 `<`（`(eq:bound_isolated)` 的 `≥` 的精确补集，二者在等号处重叠）；聚类取 `2R` 分离覆盖、最近点归属（成员在 `2R` 内），不是连通分支（S5-23 `Evolution/CltMoments1`，daa7cc1）。
- **D392（T2165b）**：`a₂` 处权重的分子是窗口 `C₆ d (log W)³ ℓ_s`，不是 `ℓ_s`；`(eq:simplecalculus)` 成立的形式为 `λ^q ρ^{-((d−1)q−d)}`，`ℓ ≤ ρ`（`log W ≥ 1`）时为 `ℓ^d/(ℓ^{d−2})^q`。
- **D393（T2165c）**：`(eq:2p_product_pair)` 的 `≺` 每个聚类藏 `lw^{d+(13−d)|A|} ≤ lw^{12|A|}`，合计 `lw^{24p}`（`cltMom1_clusterSum_le` 里显式）。
- **D394（T2165d）**：尺度前提：半径 `2R` 的可比性要 `log W ≥ 40`（`2pR` 要 `≥ 40p`），`(prop:BD1)` 要 `log W ≥ 2d`（D368 形式）；Lean 陈述写作 `2r ≤ ρ`、`2dw ≤ ρ`。
- **D395（T2166a）**：非交错 `σ` 的 `hker` 系数是 EK-6 的 `W^{Cε} r^{k−1}` 与 `W^C δ`（`r = (g²+|1−s|)/(g²+|1−t|)`），类为 `δ ≤ W^{-D}`、`D > 1`；不同于 RBM2D 的 `cCase1(1+log L)^k…`（S3-10a `Induction/NQGood1`，691566a）。
- **D396（T2166b）**：二次变差上界 `κ₁(κ₁Γ(ΓΛ)B_u^{2k}/η_u + W^C W^{-D'}) + W^C W^k W^{-D'}` 要 `D' > k+1`；路线是两次用 EK-6 加行和，不是论文的一步 pair 估计。
- **D397（T2166c）**：`η⁻¹` 平移取改正形式 `η_{u'}⁻¹ ≤ η_u⁻¹(1 + 2Δη_u⁻¹)`（`2Δ ≤ η_u`）；`(1 + Δη_u⁻¹)` 在 `E = 0`、`u = 0`、`Δ = 1/10` 为假（同 RBM2D 票面的错）。
- **D398（T2166d）**：`goodSetN_dec_shiftN` 的前提取 `2 ≤ ℓ ≤ 2k+2`，结论只含 `𝓛` 部分；`ℓ = 1` 空真。
- **D399（T2166e）**：对一切实数 `g` 有 `ℓ_u ≤ ℓ_{u'}`（`nqGood1_ellT_mono`），不需要 `0 ≤ lam n`（§45 O3 (3) 了结）。
- **D400（T2166f）**：`Ξ̂^{(𝓛)}` 的平移用 `Bctl` 单调（`STBctl_mono`）；`GoodSetN` 没有 `Ξ̂^{(𝓛)}` 条款（T2146a），无须平移；`STXiLKM_crudeN` 要 `B_u ≤ 1` 与 `‖𝒦‖` 的界 `M_K`。
- **D401（T2166g）**：`nqGood1C` 是 EK-6 对 `(d, k, Λ_g, κ')` 的常数，`κ' = min κ (4/5)`（由 `|E| ≤ 2−κ`）；`driftTensorN` 是 `GridDriftN` 内联和的新名字（陈述形状，非论文差异）。
- **D402（T2161a）**：`GGGamma`（`B:393-405`）前两个和里的系数 `S^+_{xβ}` 应为 `(M^+S^+)_{xβ} = (1+M^+S^+)_{xβ} − δ_{xβ}`（数值核对 b.7；探针 `BAGGGamma` 用改正形式；第三个和、`lanlw`、`lem_lweight` 原样成立）（BA-D1 设计，T2161 合并 87f617a，探针在 `t/T2161` 的 82e72b3）。
- **D403（T2161b）**：体内条件 `|E| ≤ e_λ − κ`（`1_2:649`、`7_8:1817`）与 `lem:propM`(2) 的 `Im m ≳ 1`（`7_8:1908`）在 L 为奇数时无定义、有 gap 时为空、cusp 处 `Im m = 0`；按 §51 改为 `ρ_N(E) ≥ κ`。另：[RBSO1D] Lemma 3.9 在 TeX 里只出现在注释中（`7_8:1844, 1846`）。
- **D404（T2161c）**（约定）：`B_{t,K}`（`1_2:1107-1108`）与 `ℓ_t`（`1_2:1121-1123`）带 `λ`；BA 流里耦合是 `g_0 = √t_0 g`，探针保留模型的 `g_n`（合并的 `Bparam`）；二者差常数 `t_0 ≥ κ/(κ+1)`（`Im m ≥ κ`、`Im z ≤ 1`）；论文未说明取哪个。
- **D405（T2167a）**：(5.93)（`3_5:1158`）在 d ≥ 3 是不等式 `r_{u,t} B_u ≤ B_t`（亏量 `g²(t−u) ≥ 0`），不是 RBM2D 的恒等式；核权满足 `κ_{i,m} B_{u_i}^k ≤ W^{Cε} B_{u_m}^k`（S3-10b `Induction/NQGood2`，cc96b69）。
- **D406（T2167b）**：核类带 `δ ≤ W^{-Dc}`、`1 < Dc ≤ D'`，加性权 `εK = W^C`（EK-6），`κ_{i,m} = W^{Cε} r^{k−1}`；无 RBM2D 的 `(1+log L)^k K_w^{2(k−1)}`。
- **D407（T2167c）**：平移后的二次变差上界要 `k+1 < D''`、`W^{-D'} + eeShiftErrN ≤ W^{-D''}`（故 `D'' ≤ D'`）与 `|E| < 2`。
- **D408（T2167d）**：`hc_pos` 要 `Δ > 0`（`s n < v n` 且 `K n ≠ 0`）；`AssembledN` 只给 `0 ≤ Δ`。
- **D409（T2167e）**：`qvBdNonAltN_pos`、`cQVNonAltN_sum_pos` 不要能量条件、不要 `1 < W`。
- **D410（T2167f）**：漂移水平 `dDriftNonAltN` 无加性 `2W^{-D'}`（同 T2154 (d)）（陈述形状）。
- **D411（T2168a）**：`Rem`、`Mart` 是网格上的 Lean 构造（论文是精确 SDE `(int_K-L_ST)`，`3_5:136`）：`difRepMartN` 含二阶部分的全鞅（ST2-12 `Path/DifREP1`，3df1812）。
- **D412（T2168b）**：常数 `C₀ = m+9`、`CK = 8m+20`，只依赖 `m`（钉文文档串写 `C₀(d,m)`）。
- **D413（T2168c）**：`difRep_identity` 对每个 `k`、`ω` 逐路径成立（钉文条款 (i) 保留 a.e. 形式）（强于需要）。
- **D414（T2168d）**：`3 ≤ d` 经 `STKbound` 进入（D263，§36）。
- **D415（T2168e）**：`STGridRepN`、`STGridMart` 只在两条 owed 尾界下证出；余项部分（条款 (i)(ii)）对 `3 ≤ d` 无条件（条件形式，§53：尾界交 ST2-13a/b）。
- **D416（T2169a）**：`(eq:2p_product_pair)` 第一行逐因子的 `≺` 写成窗口上按剖面归一化的最大值加尾 `(Λ', q₁)`（`CltMom2.DomHyp`）与 a.s. 包络 `CltMom2.BY`，`≺ ⟹ 𝔼` 为 `CltMom2.rhs` 中的因子（D370）（S5-24 `Evolution/CltMoments2`，7738afa）。
- **D417（T2169b）**：`(eq:2p_product)` 的 `O(W^{-D})` 是单独的精确项 `CltMom2.off`（`f^{far} − 𝔼f^{far} = c_n·fluc + off`），不在矩内。
- **D418（T2169c）**：聚类半径 `2R = 20w` 的可比性付因子 `4^d`；权常数 `M_w = C₅(1+2^{d−1})C₆ d`；`log W ≥ 40`、`log W ≥ 2d` 为前提。
- **D419（T2169d）**：矩界在单个 `n` 陈述，孤立窗口组 `|𝔼∏𝕀𝔼𝗕| ≤ εf`，显式 `Λ'、q₁、εf`、中心化 `2^{2p}` 与 `lw^{24p}`（D393）。
- **D420（T2170a）**：`GtoAG` 的确定性形式：项界、`S`/`S^±` 衰减与 `R`-球上的 `ξ` 控制作样本前提；`W^{-D}` 为显式尾 `e^{-cr/2}C'_Γ size(Γ)`；无 `(log W)` 损失（LW-11a `Graph/AuxGraph`，87cf70c）。
- **D421（T2170b）**：`Γ^aux` 对外部顶点分属不同分子的正规图定义；`(eq:MolVW)` 只以求和形式用（`n_V − n_M ≤ n_W`）。
- **D422（T2170c）**：`ξ` 取任意在 `R`-球上控制非对角项的非负块函数；`(eq:xia1a2)`、`claim:xi` 归 LW-11b。
- **D423（T2170d）**：nested 形式要 `𝓜_x ≠ 𝓜_y`、`p ≥ 1`、对称 `ξ`；用 walk（D338）。
- **D424（T2170e）**：两外部顶点在同一分子时的 `(scalemole)`，确定性形式（`(eq:far_ab)` 下 `𝓜_x = 𝓜_y` 的输出）。
- **D425（T2170f）**：`GtoAG` 的 `hext` 对界不需要（钉文保留）（陈述形状）。
- **D426（T2170g）**：目标 4 的实例用 `S^+_{xy}`（带色波浪边），票面写 `S_{xy}`（票面笔误）。
- **D427（T2174a）**：（只改文档串）`un_step1_floor` 的文档串原写「sharp up to `τ_s < 16𝔠𝔡/(3+𝔠)`」有误：`W = N^𝔠` 时不等式成立当且仅当 `τ_s ≤ 32𝔠𝔡/(15+2𝔠)`；陈述 `τ_s ≤ 𝔠𝔡` 不变（UN-01 `Universality/Pins`，f8ad4b4）。
- **D428（T2171a）**：四、六圈界是 `E2HypDif` 的前提（RBM2D `goodSet` 条款 2，`k = 4, 6`），`E2Hyp` 不带（S5-06 `Path/LemDecCalEdif`，7d9f111）。
- **D429（T2171b）**：下限 `(L^dW^{6d})² ≤ W^D`，强于 D374 的 `L^dW^{2d} ≤ W^D` 与论文的 `W^D ≥ N`（T2164 的 M1 更紧，S5-09 写前定）。
- **D430（T2171c）**：`σ ∈ {+,−}²` 全部四种（RBM2D 只 `(+,−)`）。
- **D431（T2171d）**：`lossE2dif = lossE2·729^d(1+log(L^dW^{6d}))^{2d}` 是 `res_deccalE_dif` 中 `≺` 的显式损失。
- **D432（T2171e）**：`_cut_far` 的四圈因子写作 `Λ((W^d(1−u))^{-1})^{3/2}`（先取逆再实幂），值同 `M_u^{-3/2}`（陈述形状）。
- **D433（T2172a）**：三圈前提 `|𝓛^{(3)}_{u,σ,a}| ≤ Λ(W^d(1−u))^{-2}`（RBM2D `goodSet` 条款 2，`k = 3`）是 `E2HypWG` 的第三合取项，`E2Hyp` 不带（S5-08 `Path/LemDecCalEwG`，3e22603）。
- **D434（T2172b）**：下限 `(L^dW^{6d})² ≤ W^D`（同 D429）；`STIngR5` 不供。
- **D435（T2172c）**：`σ ∈ {±}²` 全部（RBM2D 只 `(+,−)`）。
- **D436（T2172d）**：`J^{3/2}` 照论文（RBM2D 钉文是 `J²`）：`fG_off` 保留 `√J`。
- **D437（T2172e）**：`lossE2wG = lossE2·1000^d(1+log P)^{2d}`，`P = L^dW^{6d}`。
- **D438（T2172f）**：`LemDecCalEwG_sum_sqrt_tail`：`C_sq(d) = 5(1+24576 d⁴)^d`，条件 `wL^{2d} ≤ A`。
- **D439（T2172g）**：不用 `J ≤ W`；近区远 `y` 项为 `W^{-6d} ≤ M_u^{-2}√(M_u^{-1})`（T2164 的 M3 在此了结）。
- **D440（T2177a）**：（形状）`ouSample_law` 只对 `UNModel.band sz` 陈述（抽象模型无高斯律）；`ouMat = Xmat ∘ ouSample` 为 `ouMat_eq_Xmat_ouSample`（UN-02a `Universality/OU`，a52eb85）。
- **D441（T2177b）**：`ouMat_zero_map` 对每个 `UNModel` 陈述为 `M.μ.map (M.H n)`；带状实例 `seqXmat_map_eq_ouMat_zero`。
- **D442（T2177c）**：`measurable_ouMat` 取 `M : UNModel sz` 与 `n`；其余取 `sz : Sizes d`（陈述形状）。
- **D443（T2173a）**：T2161 的 BA 钉文写在 `sz.seqP` 下（高斯部分是带状剖面 `S^{(B)}(λ)`），BA 的律是 `(sz.withLam 0).seqP`（编译见证 `seqGvar_ne_withLam_zero`）；BA 票照 §57 带律参数重钉（BA-DS 设计，T2173；探针在 `t/T2173`）。
- **D444（T2173b）**：`BAGlueUniv`（T2161 `:1847`）缺 `BAEnd_QUE` 与 BA-V3 的流输出，而 OU 行要用；论文只列 decol、locSC、QUE 为输入（`1_2:567-568`）。
- **D445（T2173c）**：对 BA，Thm 2.4 的证明走中心化流 `(MBM)`（`1_2:686`）；论文只写「同带状情形」（`7_8:1835`）。
- **D446（T2173d）**：`m(z, λ)` 在体内关于 `(z, λ)` 的一致连续模（`UNDens`）超出 `lem:propM`，T2161 的钉文里没有（新 BA-C2）。
- **D447（T2173e）**：BA 的 `M_{y,α}` 权重为 `S^V = I`（单块），是对「[DYYY25] (2.24) 下方定义」的读法（T2162a 的变体，D382）。
- **D448（T2178a）**：（陈述形状）`InjSum_stieltjes`（`green` 形式）与 `stieltjesN`（`Gres _ _ true`）只在定义上不同，由 `InjSum_stieltjesN_eq_stieltjes` 连接，不是 `rfl`（UN-03a `Universality/InjSum` + `PoissonSmoothing`，4c52041）。
- **D449（T2179a）**：预算目标为 `assembledRHSNonAltN ≤ N^{ε₀}(Λ^{1/2} + Φ + Φ²)B_v^k`；`Φ²` 来自 `dDriftNonAltN` 的 `kΓ³Φ²`（`GoodSetN` 条款 (D2)），RBM2D `budgetNonAlt` 是 `(Λ^{1/2}+Φ)M_v^{-k}`；S3-12 要把 `Φ²` 压到 `STNQConcl` 的线性右端（S3-11 `Induction/NQBudget`，5b887a6）。
- **D450（T2179b）**：前提 `Δη_v^{-1} ≤ 1` 代替 RBM2D 的 `ΔN ≤ 1`（后者在实例处为假）。
- **D451（T2179c）**：远处部分带 `W^C`（`C = nqGood1C`）：`D'`、`D''` 须在 `C` 之后取；无 `cCase1`、`cPair1`、`(1+log L)^k`。
- **D452（T2179d）**：`N^{-1} ≤ B_v`（`cont_inv_size_le_Bctl`）代替 `M_v ≤ N`；`κ_{i,m} ≤ nqBudget_kapFar` 经 `r_{i,m} ≤ (1+g²)N`。
- **D453（T2179e）**：`ha2` 为 `kW^{Cε}(N^{ε₁})³Ls ≤ N^{ε₀}/12`（由 `Γ ≥ 1`）（常数形状）。
- **D454（T2181a）**：`E2Hyp` 的合取项 `J ≤ W`（T2164 M3）不用：近区远项为 `W^dL^dP^{-1} = W^{-5d} ≤ M_u^{-1/2}M_u^{-4}`（S5-07 `Path/LemDecCalEdif2`，a34c217；`lemDecCalE_dif` 证出）。
- **D455（T2181b）**：远区单项 `(1−u)^{-1}M_u^{-1/2}J³`（RBM2D 两项）。
- **D456（T2181c）**：RBM2D 的 `convTailT` 换成 `LemDecCalE_sum_tail_tail`（`(2S_d+1)M_u^{-2}`，`S_d = (1+1536d⁴)^d`）。
- **D457（T2183a）**：（陈述形状）合并的 `ouMat` 按模型索引（`Pins.lean:150`），故 `integral_kPoint_ouMat_cond` 对 `M : UNModel sz` 陈述（`ouP M n`、`M.μ`、`M.herm n`），`gueP_prod_map_ouMat` 对显式矩阵陈述；非数学差异（UN-02b `Universality/Step1Cond`，7771372）。
- **D458（T2182a）**：`(eq:ells_to_ellt)`、`(eq:ells_to_ellt2)` 远处部分不用：估计对一切 `σ₀ ≠ σ₁` 与 `a` 成立；它们只描述 `STCltFarConcl` 的指标集（同 D369）（S5-25 `Evolution/CltFar`，f23811b；`STCltFar` 证出，登记删）。
- **D459（T2182b）**：`(eq:propcalB)`（`3_5:2155`）是 `(Eq:Gdecay_w)` 在 `u = s` 的事件 `{N^τ ζ' < |𝓑|}`，标度 `Λ' = N^τ`；窗外一半 `‖off‖ ≤ W^{-D}` 对所有 `(σ, a)` 在同一事件外成立。
- **D460（T2182c）**：矩阶与指数显式：`p = ⌈(D+2)/τ⌉`、`Λ' = N^{τ/2}`、`q₁ = N^{-D₁}`、`D₁ = 18p+⌈D⌉+4`、`εf = W^{-D'}`、`D' = (6p+⌈D⌉+3)/𝔠`（论文「任意固定 `p`」与 `≺` 藏着）。
- **D461（T2182d）**：`‖Θ_t‖ ≤ c_Θ/g²` 不是常数；和式用 `1−s ≤ g²`（`STReg5I.2`），论文 `≲`（`3_5:2204-2211`）藏着。
- **D462（T2182e）**：指标集上的 `≺` 是显式有限并（`≤ 4N²` 个元素），在 `P` 内（不是 `PrecPT`）。
- **D463（T2182f）**：（§36）陈述在 `3 ≤ d` 下；消费者经 `STIngR5` 有此条件。
- **D464（T2185a）**：`ξ²` 把两个荷 `![true,false]`、`![false,true]` 相加（论文 `7_8:882` 取最大，差因子 2）（LW-11b `Graph/AuxGraph2`，fbaa460）。
- **D465（T2185b）**：`(eq:xia1a2)` 的半径 `ρ` 是参数，`ρ + 1 = N^{o(1)}`，球按块上的 `zdistInf`；LW-02 取 `R = (log W)^{3/2}`、`ρ = 2(log W)^{3/2} + 1`，代替论文的 `(log W)^{1+ε₁}`、`(log W)^{1+2ε₁}`（论文那一对要 `(log W)^{ε₁} ≥ 3` 才有 `2R + 1 ≤ ρ`）。
- **D466（T2185c）**：`(eq:Gbyxi)` 拆成 `‖G − M‖_max ≺ Ψ_t(0)`（全部元素，`(GiiGEX)` + `(LW_assm)`）与 `R` 球上（`2R + 1 ≤ ρ`）一致的 `|G_{xy}| ≺ ξ(a,b)`；无 `W^{-D}`（禁闭由 LW-11a 的尾项给）。
- **D467（T2185d）**：`claim:xi` 除 `(LW_assm)`、`(eq:Psi)`、Ward 外只用 `‖G_t − M‖_max ≺ W^{-ε₁}`（给 `|𝓛^{(1)}| ≤ 1 + A`）。
- **D468（T2187a）**：（Lean 结构，非数学）探针在原处改 `UNModel`（加 `mean`）与 `ouMat`；合并版用 `UNModelC extends UNModel`、中心化流 `ouMatC`、`UNKind.M : ∀ sz, UNModelC sz`，钉文 `UNClaim417C … UNUnivMainC` 是对 `UNModelC` 的副本；数学修改（中心化流）即 D445（T2173c）（UN-01b `Universality/PinsK`，fdbb6f0；§57）。登记：`RBM.Univ.UNKind.bulk` 记为结构性（T2187b，总调度确认）。
- **D469（T2184a）**：性质 (6) 经局部代价 `c = ord + #elem`（对合并取最小，`scost`、`LocCostGe`）证，不经论文的 `ord + n_dv + n_lw`（`B:200-278`）；初值 `Φ^far(Γ_p) ≥ 3p`、`Φ^all(Γ_p) ≥ 2p`（`fxyPowGraph_locCostGe`）代替 `3p − n_dv/2 > 2p`（LW-10c1 `Graph/LocalRegular6a`，2a42f07；§55）。
- **D470（T2184b）**：合并是 `Setoid (E ⊕ I)`；一类含外部成员即为外部类；边保留当且仅当被圈或连两个类；`scost = #kept + 2n_W − 2#intCls + #elemCls`。（T2184c：`B:272-275` 略去的边与 `GG` 情形由 c2–c4 补，随它们编号。）
- **D471（T2189a）**：论文在 `C_+` 中陈述 `m(z)` 唯一，用 `m(E) = m(E + i0)` 而未陈述实轴唯一；文件对一切 `Im z ≥ 0`（含实轴）、`L ≥ 1`、实 `g` 证 `BASelf_unique`；实 `E` 处 `BAm` 取实轴唯一解（无解为 0，`BAm_real_eq_of_self`）；与边界值 `m(E + i0)` 的等同是 owed 钉文 `BAmBoundary`（BA-D1a + BA-D2 `BA/MFixedPoint`，ae63e74）。
- **D472（T2189b）**：`(self_m)` 论文是精细 `N × N` 矩阵上的 `N⁻¹ tr`；`BASelf` 在块格上陈述为 `L^{-d} tr M^{(B)}`（`Ψ = Ψ^{(B)} ⊗ I_{W^d}`）；两个归一化迹相等本文件未证（BA-C1 或其消费者须补）。
- **D473（T2186a）**：`lem:STOeq_NQ`（`3_5:1136`，`(am;asoiuw)` `3_5:1143-1148`）的随机自项 `B_u^{1/6} sup_{w∈[s,u]} Ξ̂^{𝓛−𝒦}_{w,n_}` 换成确定性 `B_u^{1/6}·XLK n_ n u`，前提 `Ξ̂^{𝓛−𝒦}_m ≺ XLK m` 对 `m ≤ n_`（同 RBM2D `STOeqPT`）；合并钉文蕴含主撇钉文（`stOeqNQ'_of_stOeqNQ`）；自吸收挪到 S3-18b（§60、§62）（S3-12a `Induction/Step34PinsP` + `Induction/NQLin`，d783ee3）。
- **D474（T2186b）**：论文好集（`lem:SEforLn`）的条款 (D1)–(D3) 在 `GoodLinN` 中各取确定性水平 `Φ₁, Φ₂, Φ₃`，`Φ₂` 线性（`Γ(ΓΦ₂)B^k/η`，代替 `Γk(ΓΦ)²`）；`GoodSetN` 只在粗水平上用。
- **D475（T2186c）**：`lem:SEforLn` 与假设 `XL`、`XLK` 的每个 `≺` 都在指数 `ε/3` 上用；损失 `Γ = N^ε` 以 `Γ(ΓΦ_i)` 出现（(D1′)(D3′) 余量 `4ε/3`，(D2′) `ε`）。
- **D476（T2186d）**：`NQLinConcl` 的控制量取在网格窗 `[s_n, v_n]`（不是 `[s_n, t_n]`）；`lem:SEforLn` 从 `[s,t]` 限制到 `[s,v]`，`Φ₂` 带 `B_v^{1/6}`（`B_{u,0}` 单调）。
- **D477（T2186e）**：`budgetNonAltLinN` 的 `ha2` 是 `(N^{ε₁})²`（`budgetNonAltN` 是 `(N^{ε₁})³`），结论对控制量一次：`N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃)B_v^k`（代替 `Φ + Φ²`）。留给 S3-12b/c：`ha2`、`ha3` 只在固定 `ε₀` 下 `n` 大时成立（`log₁₀ N ≥ 48.6 / 51.5 / 56.2`，`k = 2/3/6`）。
- **D478（T2190b）**：（设计）`7_8_light_weight.tex:1835` 说离域、QUE 与体普适性「作为推论」得出（`subsec:main`）；对 `m(·,λ)`（不是 `msc`）的 Step 1 稳定性带目标 4–5 的 `O(t*)` 项 `C₀(ε + t)`，`C₀` 只依赖 `(c, K, Lp, δ, A)`（T2173c 的变体）（UN-07 `Universality/FreeConvRegular`，d1a0316）。（T2190a 是钉文问题，见 DECISIONS §65。）
- **D479（T2180a）**：BDG `(aaswtghh)` + Markov 换成带可料代理、对 `K` 一致的极大指数界（D90）：`μ(max ≥ x) ≤ e^{-x²/(2V)}`；水平 `V_ℓ = 2^ℓ N^{-D}`，对 `ℓ` 取并，`±Re, ±Im` 因子 4（ST2-13a `Path/DifREP2`，76b840e；`STGridMart` 无条件）。
- **D480（T2180b）**：一阶混沌代理是 `u_{j+1}` 处的 `k Re(𝓔⊗𝓔)`（`ZvecN` 在 `H_j` 对 `𝓛_{u_{j+1}}` 求导），挪到论文的 `u_j` 代价 `m(2m+2)16^{2m+3}N^{2m+4}Δ`（`difRep2_eeShift_sum_le`），吸收进 `N^{-D}` 下限。
- **D481（T2180c）**：二阶部分 `Y` 用 Doob `L²` 不等式，在同一 `N^{-D}` 下限内；`AzumaProxyN_YfieldsW` 的 `L⁴` 字段只用于平方可积。
- **D482（T2180d）**：`CK = 2m + 2D + 16` 只依赖 `m, D`（与 `ε'` 无关）；尾项 `GridRepTailNAt d m` 对一切 `d` 成立，`3 ≤ d` 只在组装处用。
- **D483（T2180e）**：`STGridMart d`、`STGridMartAt d 11` 在 `3 ≤ d` 下无条件；`C₀ = 2 + 9 = 11` 显式（论文 `C₀(d)`）。（T2180f，Lean 写法：`Mart = Σ ZvecN + Σ YvecN`，`YvecN := martIncN − ZvecN` 按定义。）
- **D484（T2196a）**：二次大偏差 (4.7) 对 `A + X` 的子式成立（`A` 确定性 Hermite，`gaussLaw_quad_tail`、`kind_quad_tail`）；RBM2D 只有中心化情形（`A = 0` 即 `gue_quad_tail`）；论文（`3_5_Loop_Hierarchy.tex:13-38`，`lem_GbEXP`）引 [YY_25] 引理 4.1，未陈述平移形式（UN-25 `Universality/GUEPhase/AuxCarrier`，9eb0502）。（T2196b、T2196c 是 Lean 写法：辅助方差在一块上的正性由 `sbKernelR d L g 0 = (1+2dg²)⁻¹` 对一切 `d, g` 得；`mixVar`、`Smix` 带剖面耦合 `g`，与合并的 `ouVar` 一致。）
- **D485（T2191a）**：`6:97` 区域 (ii)、`σ₁ = σ₂`：论文引 `(sum_res_2_NAL)`，其引理 `lem:sum_decay`（`3_5:1632-1637`）要 `t ≤ 1 − ilambda²/L²`，与 `1 − t < 1 − s ≤ ilambda²/L²` 合起来迫使 `s = t`；Lean 用 `(sum_res_Ndecay_nonzero)`（`3_5:1667`）在 `A = ∅`（`I_diff = ∅`）（ST-D5 设计 T2191，签字 §67）。
- **D486（T2191b）**：（形状）Step 6 钉文去掉 `STKbound`、`STKward`、`STDecayStrong s`、`STDecayStrongU`、`STStep1Loop`，用 `STStep2Core` 代替 `STStep2Concl … C_d`，无 `∀ C_d`（论文 Step 6 都不用）。
- **D487（T2191c）**：`lem:improve_exp_aver`（`6:12-21`）按时间序列 `u` 钉（两前提都在 `u`）；论文对 `[s,t]` 一致的形式是 `STExpAvgU`，对确定性左端由 (g) 得。
- **D488（T2191d）**：Ward 界 `(eq:EPL-K)`、`(eq:boundELKQ1)`、`(eq:boundcommutator)` 与区域 (ii) 分解对 `u ∈ [s,t]` 一致地钉（论文在 `t`），前三者对一切满足 `STMollifierProps` 的磨光族（论文：`Def:QtPt` 那一族）（`6:104-132`、`6:137-141`）。
- **D489（T2191e）**：`(Eq:Gtlp_exp_flow)` 的 `max_{σ,a}` 是 `Prec` 内对 `(u,σ,a)` 的并，尺度 `N`（合并约定）；`lam n > 0` 只最终成立（`(eq:WO)`）（`1_2:1390-1396`）。
- **D490（T2195a）**：局部引理可复合（Fable §3），把新顶点放进至多与其一个邻点相交的类的合并，代价不低于不动它（Fable §4.3），故 17 项归为 7 个基本操作（论文按项记账，`B:213-262`）（LW-10c2 `Graph/LocalRegular6b`，b43cb93；§55）。
- **D491（T2195b）**：`GG` 项 `R2`（`Contract`）：2-圈坍缩降低平凡合并的代价（`localReg6b_instCyc_repair_forced`），故 `B:272-273` 无逐步对应；对合并取最小由把圈的两类合并恢复（`scostLL_repair`），从不合并两个外部类。
- **D492（T2195c；即 T2184c 的一部分）**：c2 补 `Loop`（`Oe1xOwx`、`R3`、`T1`）、`Contract`（`R2`）与因子 `AddLoop`（`P5`、`P6`、`R5`）、`Loop`（`R4`、`R6`）、`MoveLoop`（`T2`、`T4`）的局部引理；其余边与 `GG` 项由 c3 的 `MoveSC`、`MoveOut`、`Dmove` 补。
- **D493（T2194a）**：`𝒬` 过程的次高斯输入在任意可测族 `G` 的离出时 `gridExitTauN … G` 陈述（7a：任意停时族），代替 RBM2D 写死单水平的 `azumaSubGQ_goodExit`（§62 (4)）（S3-14 `Induction/QProxy`，9a207a1）。
- **D494（T2194b）**：交错鞅的方差代理是对 `(𝒬_v⊗𝒬̄_v)(𝓔⊗𝓔)` 两次用 `(sum_res_2)`（EK-4）：块内和为零、块内 `ℓ¹` 衰减、对一切 `σ`；代替 RBM2D 的 `d = 2` Case 5 核界。
- **D495（T2194c）**：`d ≥ 3` 的双副本 `lem_+Q` 带加项 `W^{-D+C_Q}`，`C_Q = 2C_n + 2`。
- **D496（T2194d）**：`C_P` 多 `2m + 2`，来自 `𝒬_u` 的行和 `1 + C(L^d)^m ≤ N^{m+1}`（`‖ϑ‖ ≤ C` 不是 `≤ 1`；要 `0 ≤ c`，T2194 Amend 1）。
- **D497（T2198a）**：Hölder-1/2 界、`J♯` 与提升在 `contGood`（每个高斯坐标 `≤ N`，概率 `≥ 1 − N^{-D}`）上、前提 `(1 − t_n)⁻¹ ≤ N`（最终）下做（S5-09a `Induction/LemDecCalELip`，e4126a2；§64）。
- **D498（T2198b）**：(G) 陈述为 `PrecPT(ξ ≺ R₀ + J^m R) → Prec(ξ ≺ R₀ + J^m R)`，`m ≥ 0`、确定性 `R₀ ≥ 0`、`R ≥ N^{-C_R}`、`R₀, R, J` 相对连续 `1 + N^C√|u−u'|`、`ξ` Hölder-1/2。
- **D499（T2198c）**：`J♯ := max(1, max_{σ,a} |(𝓛−𝒦)^{(2)}_{u,σ,a}|/T_{u,D}(|a₁−a₂|))` 是单时刻的实现随机控制量（监督 1550 的 1.3），不是 `(eq:def_new_J*)`（`3_5:2310`）的确定性 `J*`；与 T2193c′ 一起编号。
- **D500（T2192a）**：`(Meq:QdS1)`、`(Meq:QdS2)` 读作「对每个 `z ∈ 𝐃_{κ,ε}`、`N` 大」，`N₀` 对 `𝐃_{κ,ε}` 一致（`QDiff` 第三、四合取项）（MA-D1 设计 T2192，3429d7d）。
- **D501（T2192b）**：`(G_bound)` 的 `|x−y|` 与 `(eq:diffu1,2)` 的 `W|a−b|` 读作 `W|[x]−[y]|_∞`（`L^∞` 块距离，`1_2:274`，同合并的 `STLocalEntry`）；T2001、T2161 用 `ℓ¹` 块距离（`calB_distB_compare`：因子 `d^{-(d-2)}`）；精细格点距离的字面形式未编译。
- **D502（T2192c）**：Thm 2.1 的证明：`η = N^{-1+τ}` 给 `‖ψ_k‖² ≤ 2N^{-1+τ}`；编译的证明用 `η = N^{-1+ε}`，`ε = min(τ/2, 1/2)`。
- **D503（T2192d）**：`(eq:diffu1)`、`(eq:diffu2)` 的「对一切 `a, b`」读作 `a, b` 在概率之内（对 `L^{2d} ≤ N²` 对取并），同 `∩_z`。
- **D504（T2192e）**：终点形式：Thm 2.1–2.5、2.7 用显式 `W^τ`、`N^{-D}`；与合并的 `Prec` 等价（`explicit_of_stochDomAt`、`prec_of_explicit`）；是决定，不改陈述。
- **D505（T2192f）**：区域 `𝐃_{κ,ε}` 恰在 `κ > 2` 或 `ε > 1`（`N > 1`）时为空，等号处不空。
- **D506（T2192g）**：`(eq:diffu1,2)` 归为 `ML:GLoop`，环指标 `(b,a)`（`zTrace`）；剖面对称，陈述不变。
- **D507（T2199a）**：`lem:STOeq_NQ` 在网格上对一个终点时刻 `v` 证出：`GoodSetN` 取自由粗水平 `Φc`，`GoodLinN` 取确定性水平 `Φ₁ Φ₂ Φ₃`（S3-12b `Induction/NQEndLin`，cef761a；§62）。
- **D508（T2199b）**：「`N` 足够大」的显式指数与最终门槛：`ε₀' = min ε₀ 1`、`ε₁ = εq = ε₀'/8`、`ε = min(ε₀'/(8C), 1/2)`、`τ' = ε/2`、`D'' = C + k + 2 + (4k+2)/𝔠`、`D' = D'' + 1`、`C_K = D₁ + 2C_P* + 6k + 20 + D''`。
- **D509（T2199c）**：塌缩窗 `v_n = s_n`（`Δ = 0`、`H_j = H_0`、`G = univ`）单独处理。
- **D510（T2199d）**：端点前提：最终 `W⁻¹ ≤ (1−t)/(1−s)`（`nonAlt_hkerN` 中 EK-6 的窗）与 `STCaseI`（`1−t ≥ g²/L²`，给 `v ≤ 1 − g²/L²`）。
- **D511（T2199e）**：`STKbound` 不作前提（由 `stKbound_holds` 从 `3 ≤ d`、`N → ∞`、`|E| ≤ 2−κ`、`WO` 给的 `0 < g ≤ 𝔡⁻¹` 得）。
- **D512（T2201c）**：（登记）新类 `refutedProps`（§66 (2)）：`UNStep1Good`、`UNInfty1Row`、`UNStep1GoodC`、`UNCoreC` 移入；合并文件里它们的文档串仍写 owed，不改（CLAUDE.md §5.3）；主撇后继 owed，`UNDens'` 结构性（UN-01c `Universality/PinsDens`，3fc9d03）。（T2201a、b：Lean 结构，无陈述差异。）
- **D513（T2193a，续 D374、D429）**：钉文下限 `(L^dW^{6d})² ≤ W^D`（最终）代替论文 `W^D ≥ N`（`3_5:2317`）（S5-09 `Induction/LemDecCalEPrec`，d7da51e；§61、§63、§64；`STLemDecCalE` 证出）。
- **D514（T2193b）**：加前提 `J*_{u,D} ≤ W^{1/2}`（由 `lem:pf_step5` 的停时 `J* < W^ε`、`ε < 1/2` 满足）。
- **D515（T2193c′）**：`lem_dec_calE` 对 `u` 一致：确定性引理逐时刻在实现控制量 `J♯` 上用，三个结论做网格提升（§7），再在假设事件上把 `J♯` 换成 `Jst`（连同 D497–D499）。
- **D516（T2200a）**：`lem:DIfREP` 的 `(alu9_STime)`（`3_5:229`）对网格上终点 `k ≤ K` 一致成立：用与 `K` 无关的粗时间网格 `v_p`（`P = ⌈N^{C'}⌉` 点）与精确转移 `Σ_{j<k} 𝒰_{u_j,u_k}ξ_j = 𝒰_{v_p,u_k}Σ_{j<k}𝒰_{u_j,v_p}ξ_j`（半群性），`𝒰_{v_p,u_k} = id + O(N^{1−C'})`（ST2-13b `Path/DifREP3`，b3c37aa；`STGridRepN` 证出，ST-2 完成）。
- **D517（T2200b）**：去零模形式 `Q^{(A)} ∘ 𝒰` 对一切 `A ⊆ ⟦m⟧`（`(sahwNQ2)`，`3_5:1908`），代理 `((Q∘𝒰)⊗(Q∘𝒰̄))∘(ℰ⊗ℰ)`，无情形条件（§59 O3）。
- **D518（T2200c）**：二阶部分对每个 `(p, a')` 用 Doob，权重同一阶混沌部分。
- **D519（T2200d）**：代理从 `u_{j+1}` 挪到 `u_j` 代价 `(32N)^{2m}m(2m+2)16^{2m+3}N^{2m+4}Δ`，从 `(u_j, v_p)` 挪到 `(u_j, u_k)` 代价 `c₃N^{4m+4}(v_p − u_k)`（绝对、确定性），都吸收进 `N^{-D}` 下限；加权尾项对一切 `d` 成立（T2200e）。
- **D520（T2202a）**：(7.30) ⟹ 对合并的带耦合与下限的 `ellT` 有 `ℓ_{t₁} = L`：`ellT_eq_L : 0 ≤ g → t < 1 → L²(1−t) ≤ g² → ellT L g t = L`（RBM2D/[YY_25]：`L²(1−t) ≤ 1`，无耦合、无下限）（UN-26a `Universality/GUEPhase/Bootstrap`，98e6d5b）。
- **D521（T2202b）**：GUE 相 (7.33)–(7.36) 的 `d ≥ 3` 形式（论文未写出，`1_2:566-570` 指向 [YY_25]（`d = 1`）与 [DYYY25]（`d = 2`））：`S^{(B)}_{GUE} = L^{-d}`、前因子 `W^d`、幂次计数 `n²N`、`N = (WL)^d`。
- **D522（T2202c）**：（记账）在最大容许 `1 − t₁ = g²/L²` 处 `Nη_{t₁} ≤ g²W^dL^{d−2} Im m`（`d = 2`：`g²W²`）。（T2202d、e：Lean 结构——RBM2D 死代码未移植、多三个 Mathlib 导入。）
- **D523（T2206a）**：沿序列的 `(stoch_domination)`（`1_2:227-231`）对子列稳定，并可由覆盖一切大 `n` 的有限个子列恢复（ST-A `Induction/SizesComp`，8810a23；§68 (8)）。（T2206b、c：Lean 写法——子列的模型律是 `seqP` 在坐标重标号下的像，对一切集合与被积函数。）
- **D524（T2208c）**：`C₀ t` 项、`t ≤ N^{-1+τ_s}` 要 `τ_s < 8/11`；钉文的 `τ_s < 1` 不给，`Admissible` 给：`τ_s ≤ 𝔠𝔡 < 1/2`（`un_admissible_c_mul_lt_one`、`un_admissible_d_le_half`）（UN-12 `Universality/Step1Good`，a42cad0；`UNStep1Good'` 证出）。（T2208a、b 见 §69。）
- **D525（T2203a；续 D492）**：`MoveSC`、`MoveOut`、`Dmove` 的局部引理（Fable §4.5）证出；与 c2 合起来 `strat_local` 的每个边、`GG` 与权项都归为有局部引理的基本操作（论文逐项记账 `B:213-262`）（LW-10c3 `Graph/LocalRegular6c`，ed9c0f1）。
- **D526（T2203b；续 D491）**：2-圈坍缩也出现在 `MoveSC` 与蓝色 `Dmove` 的 `k = 2`（`P4`、`D`、`T3`、`R7`、`R8` 由它们构成）；由合并圈的两个类修复，从不合并两个外部类；`MoveOut` 与红色 `Dmove` 不坍缩。（T2203c：证明路线——Fable §4.5 的手算行换成一个逐类模式界 `localReg6c_dlb` 加对命名顶点类的相等模式的有限分情形。）
- **D527（T2209a）**：`lem_dec_calE` 逐时刻在实现控制量 `J♯ ≤ W^ε` 上用于停止过程（S5-09 的逐时刻层），不是作带确定性 `J*` 的 `Prec` 引理（`3_5:2367-2369`）：目标 4′、4 是停时条件那一步（S5-10 `Induction/PfStep5Alg`，14513ee；§70）。
- **D528（T2209b）**：`(int_K-L_ST)` 的时间积分取 §7 网格上的左黎曼和（常数 1、2 与 `log`，目标 3），不用值域论证。
- **D529（T2209d）**：`lem:pf_step5` 在随时间变的水平 `D_u = D* + 2 log_W(1−u)`、`D* = max(D, D₀) + 2d + 1` 上证，由目标 1 降下（§70）：目标 2′ 的水平是序列，目标 4′ 的好事件水平 `D₁` 与结论水平分开（续 D513）。
- **D530（T2209e）**：`lem:pf_step5` 的闭合显式：`ε < 𝔡/4`、`τ = 𝔠ε/2`，括号 `1 + log W + W^{2ε}(ilambda²W^d)^{-1/4}`（目标 6）。
- **D531（T2214d）**：（证明路线）RBM2D 的归一 `r = ρ'/ρ_sc(E)`、因子 `r^k` 与伸缩 `ρ_sc(0)/ρ_sc(E)` 不出现；密度序列 `ρ_n` 只经其值域进入，Lipschitz 步在 `(ρ_n, ρ'_n)` 上取（抽象模型无固定 `ρ_sc(E)`）（UN-13 `Universality/Step1Band`，18a41d3）。
- **D532（T2213a–c）**：（登记与文档串）`UNStep1GoodC''` 在本票证出，故不登记；`refutedProps` 的文档串写「已证假」，而 `UNCoreC'` 只是被取代、`UNTrLocalInit` 是对带状模型论证为假的谓词，新条目的注释照实写（「被取代、不需要」类见 §68 (9)）；`τ = τs/8` 时新项 `W^τ t*` 要 `τs < 2/3`（监督的 `8/11` 是 `τ → 0` 的极限），由 `un_admissible_cd_lt_half` 给（UN-12b `Universality/PinsC2`，122f299；§69）。
- **D533（T2215a）**：二次变差的平方剖面 `TailtoTail`（论文 `3_5:2364-2383` 只用 BDG 加 `(res_deccalE_dif)`，无陈述）：近/远分界在 `(log W)^{3/2}`，常数 `18e^{8d+2}`（`tailtoTailSq_kernelGen`、`tailtoTailSq_kernel`；S5-10a `Induction/TailtoTailSq`，5d313ca）。
- **D534（T2215b）**：远段余项写成 `4YL^dρ³W^{-D₂}`，指数 `D₂` 与主 `D` 分开、`Y` 取粗界（论文一并写 `W^{-D+C}`）；`D₂` 的选取与 `L`–`W` 关系的吸收归 S5-11（S5-10a，5d313ca）。
- **D535（T2205a）**：`zztE_BA` 的 `|E| ≤ 2−κ`（`7_8:1797`）是论文路线（从 `t ≈ 0` 起的 ConArg 链）的条件，不是笔误；`d = 3`、有限 `L` 时它保不住耦合路径在体内（L=4、`g₀ ≥ 2`；L=16、`g₀ = 10`；那里 `Im m ∝ η`）；不用，路线换成窗口 `BAWinBulk`，§51 的集合 `ρ_N(E) ≥ κ` 保留（BA-D3 设计单，63d62b4）。
- **D536（T2205b）**：`lem:main_ind_BA` 的 Step 1（`7_8:1987-1990`，「同 [RBSO1D, §7.1]」）与归纳在流族 `Fam(u)` 上成立：`lem_ConArg_BA`（`7_8:1956-1966`）用 `s` 时刻流 `(E, g_s)`（`g_s = g₀√(s/t)`）的圈界 `t` 时刻流 `(E, g₀)` 的圈，且要 `Im m(E, g_s) ≥ κ`（缺这条 `BAConArg` 为假，F1）（BA-D3，63d62b4）。
- **D537（T2205c）**：间隙 `Re(1 − L^{-d} tr M²) ≥ 2(Im m)²`（`BAgapReal_holds`）与窗口 `c₁ = min(1/2, κ⁹/(64dΛ))`、`C = 2d/κ⁴`（`BAmWindow_holds`）论文没有；被注释掉的 `7_8:1812-1813`（「`t ≥ 1 − ε` 时 `z_t` 留在体内」）是其连续形式（BA-D3，63d62b4）。
- **D538（T2205d）**：族钉文带 `∀ n, 0 < sz.lam n`；`BAFlow` 只给最终正（`WO`）；结论是最终的，消费者走尾巴（`Sizes.comp`、`comp_admissible`）（BA-D3，63d62b4）。
- **D539（T2205e）**：T2161 的 `BAGbEXP`（`:1115`）前提是全局的（`(initialGT2)`、`𝓛^{(2)} ≺ Φ²`）、无事件；带状的 `STGiiGEX`/`STGijGEX`/`STGavLGEX`（`Induction/Defs.lean:202`）带 `1(Ω(t,ε₀))`，`step1TargetV3_holds`（`Induction/Step1.lean:525`）用它们：BA-G6、BA-S2b 要事件形式（BA-G3/G4/G6/S2b 有风险）；论文的全局形式是对的，事件形式是连续性论证（`7_8:1987-1990`，[RBSO1D §7.1]）在形式化里的要求（监督 2252 O2；§72 (4)）（BA-D3，63d62b4）。
- **D540（T2220a–b）**：（设计表与文档）UN-11 的实际依赖是 UN-12（`Step1Good`）与 UN-06（`FreeConvStability`），不是门户表 `T2162-portmap.md:205` 写的 UN-10、UN-05；票面「`Im m_sc ≥ min κ 1/480`」不是 `m_sc` 的界：文件内是 `Im m_sc ≥ κ'/12`（`|Re z| ≤ 2 − κ'/2`、`Im z ≤ 3`、`κ' = min κ 1`），链到 `η Im m_N` 是 `κ'/480`，给 `c = κ'/960`（UN-11 `Universality/Step1RegularityGUE`，e9ef940）。
- **D541（T2222a–b）**：`(eq:Exp(L-K)1)` 的窗口 `1−u ≥ ilambda²/L^d`（`6:58`）对界本身不需要，`stExpLKLKHi_holds` 对一切 `u < 1` 成立（窗口只在使用处要）；`6:61` 的 `≲ (1−u)^{-1}` 带显式常数 `KDecay_tailC d + 1`（`d = 3` 时约 `4.0·10^8`），只进最终门槛（`∀ᶠ n`），不进陈述（S6-06 `Induction/ExpEtermsA`，cd6fcba）。
- **D542（T2223a）**：合并的 `STExpIniIConcl`（`Step6Pins.lean:458-469`）对一切磨光常数 `(C, c)` 量化；论文（`6:117`、`Def:QtPt` `3_5:1204-1229`，`:1214`「for a constant `c>0`」，`rmk:choosechi` `3_5:1250`）的磨光函数 `c > 0`。Lean 后继 `STExpIniIConcl'`、`STExpIniI'`（加 `0 < C → 0 < c →`），由 `stExpIniI'_holds` 证；主撇消费者 `ST_step6_caseI_of_pins'`；`STExpIniI` 仍 owed（`c ≤ 0` 要 Ward 步 `STExpWardI`，预检 FFT 上界，非反驳）；`STExpIntQConcl`、`STExpWardIConcl` 同样量词（REQ-2312）（S6-11 `Induction/ExpIniI`，f2766db；§71）。
- **D543（T2221a–b）**：`(eq:def_TTT)` 写成时间依赖水平 `D_{u_j} = D* + 2 log_W(1−u_j)`（§70）上的网格停时下标（`PfStep5Grid_level`、`PfStep5Grid_stopIdx`），不是单一 `D` 的连续停时；Duhamel 形式 `(int_K-L_ST)`（`3_5:134`）从可加网格分解推出，确定性余项 `64(1−u_k)^{-7}(R + ΔM)`，两次分部求和，鞅按 `(alu9_STime)` 用 `𝒰_{u_j,u_k}` 加权（S5-11a `Induction/PfStep5Grid`，0f44a56）。
- **D544（T2216a）**：`lem:localregular` (6) 对每个输出证 `ord ≥ 2p`（`7_8:815-818`），两外顶点不同（`Q.ext 0 ≠ Q.ext 1`）时 `ord ≥ 3p`，不用假设 `(eq:far_ab)`（`7_8:792`）；论文路线 `ord ≥ 3p − n_dv/2 > 2p`（`B:268-277`）换成对合并 `Φ` 取局部代价最小值、沿 `strat_local` 单调（LW-10c4 `Graph/LocalRegular6d`，37289f6；接 T2151a）。
- **D545（T2226a–b）**：（设计表、证明内部）UN-14 对 UN-08 只是传递依赖（经 `Step1Cond` 的导入）；`UNGUETranslation` 内部时间取 `τs = 1/2`，与 `τ_U` 无关、不要 `τs ≤ 𝔠𝔡`（同 RBM2D paper-delta #139），陈述不带 `τs`（UN-14 `Universality/GUETranslation`，dc2d99b）。
- **D546（T2228a–d）**：`(deccA0)` 对 `D_u`（`STExpDriftDecay`，`3_5:1634`）在每个区域都成立（`STReg5I` 未用）；`6:65`、`6:77` 的 `≺ W^dL^d(N|1−u|)^{-4}` 由区域 (iv) 的 `B_{u,0} ≤ 2(L^d(1−u))^{-1}` 得，常数 16、三段漂移因子 3，被 `N^{τ/2} ≥ 48` 吸收；`6:78` 的 `(eq:bcal_k)`（`n = 3`）对 `u` 一致使用（`stKbound_timeIcc`）；`≺ → 𝔼` 一步要多项式包络 `N⁶` 与下限 `R ≥ N^{-3}`（S6-07 `Induction/ExpEtermsB`，6b4fe24）。
- **D547（T2197a–d）**：`(def_G0)` 的 `M = M^{(B)} ⊗ I_{W^d}` 与 `N^{-1} tr M = L^{-d} tr M^{(B)}` 已证（`BAMres_fine_kron`、`BAfine_trace`），合并的 `BASelf`、`BAm` 即论文 `(self_m)`、`m(z, ilambda)`（`BASelf_iff_fine`，关 D472）；耦合（`7_8:1816-1832`）：链上控制量（`Bctl`、`STWB`、`ellT`、`1−t ≥ ilambda²` 门）取 `g_n = sz.lam n`，流点上的 PT 钉文取 `g₀_n`（归纳钉文按 `g` 读不是按 `g₀` 读的形式推论，未定，留 BA-V2）；`lem_ConArg_BA`（`7_8:1956-1987`）钉成 `BAConArg'`（加 `κ ≤ Im m(E_n, g_s)`），原式为假，`not_BAConArg_of_data` 给条件反驳；新确定性事实：实 `|E| > 2 + 2d|g|` 时 `(self_m)` 无解（`baSelf_none_of_gt`；`1 + 2d|g|` 不对）（BA-C1a `BA/FlowPins`，b750bf3）。
- **D548（T2229a–b）**：`6:141` 的 `(W^{-d}B_{t,0})²(Nη_t)^{-1} ≲ (W^{-d}B_{t,0})³` 在每个区域成立（`(N(1−t))^{-1} ≤ W^{-d}B_{t,0}`，`expWII_inv_Neta_le`；体内常数 `(Im m)^{-1} ≤ 2/√(2κ)`）；`6:138-140` 的分解在 Lean 里写成两个单槽 Ward 恒等式之和 `f − Q^{(1)}Q^{(2)}f = (f − Q^{(1)}f) + Q^{(1)}(f − Q^{(2)}f)`，常数 3，不用 `N^{-1}tr G̃` 的闭式（S6-12a `Induction/ExpWardII`，e64e4f0）。
- **D549（T2232a）**：合并的 `STExpWardI`（`Step6Pins.lean:361`）对一切实磨光常数 `C, c`（含 `c ≤ 0`）证出（`stExpWardI_holds`；论文磨光函数 `c > 0`，`3_5:1214`），主撇 `STExpWardIConcl'` 是推论 `expWI_concl_prime`；`(eq:boundcommutator)` 与 `(eq:boundELKQ1)` 照合并结论合成一个 `Prec`（论文分开写）（S6-10 `Induction/ExpWardI`，b112700）。
- **D550（T2233a–c）**：`6:146-147` 的「对 `u` 积分」写明为 `∫_s^u (1−v)^{-1}dv ≤ (d−2) log L ≺ 1` 与 `B^{11/5} + B^{5/2} ≤ 3T_u`（由 `1−u ≥ λ²/L^d`）；`(normQA2)` 不用，`(sum_res_Ndecay_nonzero)` 直接界 `Q^{(A)}𝒰_{v,u}`；论文只写 `σ₁ ≠ σ₂`，`σ₁ = σ₂` 取 `A = ∅`（S6-12b `Induction/ExpIntII`，f6650b2）。
- **D551（T2235a–c）**：`6:94-96` 区域 (iii) 写明为 `(1−v)B_v ≤ 2(1−u)B_u`（要 `1−u ≥ ilambda²`）、`∫ x_v^{-6/5}, x_v^{-3/2}`、`5(2B)^{11/5} + 2(2B)^{5/2} ≤ 64T_u`，`B_{u,0} ≍ |1−u|^{-1}` 只用一侧；区域 (iv) 的积分界不用区域条件（常数 1），区域只经 `STExpDriftLoConcl` 进入；(iii) 用最终的 `ilambda > 0`（`(eq:WO)`）（S6-08 `Induction/ExpIntEasy`，cc4d165；`STStep6IV` 证出）。
- **D552（T2231a）**：`lem:pf_step5`（`3_5:2371-2383`）在网格上证，不用 `(eq:def_TTT)` 的连续停时 `T`：`STGridRepNAt` 第 4 合取（随机代理的 Azuma，§7）对 `k ≤ K` 一致，在水平 `D_{u_k}` 上对网格下标强归纳代替停时论证（`pfStep5_path`、`PfStep5_walkConcl`）（S5-11b `Induction/PfStep5`，e2ec919；`STPfStep5`、`STStep5III` 证出）。
- **D553（T2234a–d）**：`lem:Anp_key_gh` 证成确定性形式（`AnpDetGhAt`：确定性 `(eq:Gbyxi3)` 下的精确不等式，`C, c` 只依赖 `Γ`、`d`），再在一个事件上提升到 `≺`（`LWXi` 两前提的 `Prec.whp`、`HighProbAt.inter`），不需对 `L^{2d}` 对取并；论文以 `≺` 陈述（`7_8:1043`，`:963-966`）；`q = 0` 基例（`7_8:1117`）要沿外顶点路径走的三角不等式，`c = 1/max(1, max_i|path i|)`、`C = 1`；`7_8:1143-1148` 的 A2 替换写成 `NGraph.ghostify`（`(eq:noA2)`）；`0 < η_t` 由 `STFlow`、`t ≤ lemT z` 推出，论文默认（LW-12a `Graph/AnpKey`，e5b944a）。
- **D554（T2236a–c）**：`(eq:termI1)`、`(eq:termI41)`（`B:40-42`、`B:64-66`）引 `(res_ELK_n=1)`，它不在 `lem:LWterm_EXP`（`6:83-86`）的假设里；Lean 由 `LWAvgLaw` 在同一时刻推出（`STExpAvgAt_of_LWAvgLaw`，`ExpAvg:799`），引理照原陈述成立；`B:61` 把 `Σ_{a₂}|𝓛^{(2)}|` 换成 `Σ_{a₂}𝓛^{(2)}` 用了 `𝓛^{(2)}_{(-,+),(a,b)} ≥ 0`（论文未写，Lean 证 `lwExpTerm_loop2_nonneg`）；`I₁`、`I₄₁` 的钉文去掉因子 `m`（`|m(σ)| = 1`）并对一切荷陈述（LW-14a `Graph/LWExpTerm`，23d83c4）。
- **D555（T2239b）**：区域 (i)、`σ₁ = σ₂`（`6:97`、`6:104`）写明：`(sum_res_2_NAL)` 取 `n = 2`，比 `(λ² + 1−v)/(λ² + 1−u) ≤ 2`（`1−s ≤ λ²`），`∫_s^u (1−v)^{-1}dv ≤ 2 log L`（`1−u ≥ λ²/L²`），漂移率 `B^{11/5} + B^{5/2} ≤ 3T_u`，核损失 4 由 `4 ≤ N^{τ/2}` 吸收；`(sum_res_2)` 一支比² `≤ 4`（S6-09a `Induction/ExpIntI`，25362ad）。T2239a（磨光导数无衰减，`(sum_res_2)` 要 `(𝒫f)∂ϑ` 衰减，`6:132` 未写）待 REQ-0226 定后编号。
