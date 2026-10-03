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
`ThetaDiffOne`、`ThetaDiffTwo`、`ThetaZeroMode`），打包成 `structure PropTH d g m`。
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
`structure PropTH` 只打包性质 5、6、7、8（这四条对任意单位谱参数都成立），
**性质 5' 不进 bundle**——否则 `PropTH d g 1` 就成了一个假的假设，而 `σ₁ ≠ σ₂` 的情形到处都要用。

**教训**：这个缺陷在它还是 `axiom` 的时候就存在，而那时它意味着**不一致**（可以推出任何东西），
审计也查不出来——公理审计只管「有没有公理」，不管「公理对不对」。改成假设之后，
同样的错误只会让定理变成空洞的，而这一条是能被证伪的，也确实被证伪了。
这条支持 Q19 的判断：**接口写成假设，比写成公理安全**。

## D12 · 性质 6、7 的 `|r| ≲ |a|` 按「对每个常数」读（2026-09-19，Q21）

论文性质 6、7（`(prop:BD1)`、`(prop:BD2)`）写的是「holds for all `a, r ∈ Z_L^d` satisfying `|r| ≲ |a|`」。
`≲` 在本文里表示「至多差一个常数倍」，所以忠实的读法是：**对每个常数 `c > 0`**，在 `|r| ≤ c|a|` 上成立，
而 `≺` 的常数可以依赖 `c`。`Propagator/Interface.lean` 的 `ThetaDiffOne` / `ThetaDiffTwo` 因此带一个
`∀ c : ℝ, 0 < c →` 前件，条件写成 `(zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ)`。

**原先写成 `zdistD r ≤ zdistD a`（即 `c = 1`）**，假设的比论文claim的弱；下游若在 `|r| ≤ 2|a|` 上用就接不上。
（作为假设，弱不会导致不一致，只会导致不够用；这和 D11 那种「假的假设」性质不同。）

## D13 · 接口常数允许依赖 `g` 与 `m`（2026-09-19，Q21）

论文说性质 5 的常数 `C_d, c_d`「depending on `d`」，性质 5' 的「depending on `d` and `κ`」。
Lean 里五条都是以 `(d, g, m)` 为参数的 `Prop`，`∃ C` 在参数之内，所以常数也可以依赖 `g` 和 `m`。
**这是有意的弱化**：作为假设，弱的版本更安全（更容易为真、更容易将来证出来），
而下游用到的只是「存在不依赖 `L, t, a, r` 的常数」这一点。若将来要求常数对 `g` 一致，
需要把 `g` 移到 `∃ C` 之后——届时再改，届时的下游签名不受影响（`PropTH` 仍是参数化的）。

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
