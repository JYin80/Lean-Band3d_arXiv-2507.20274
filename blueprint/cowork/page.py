from graphs import G0, G1, G2, G3, G4

def rows(items):
    out = ['<ul class="rows">']
    for name, pill, cls, code in items:
        c = f'<code>{code}</code>' if code else ''
        out.append(f'<li class="row"><div class="row-main"><span class="row-name">{name}</span></div>'
                   f'<div class="row-side"><span class="pill {cls}">{pill}</span>{c}</div></li>')
    out.append('</ul>')
    return "\n".join(out)

CH1 = rows([
 ("格点 Z_L^d 与周期 ℓ¹ 距离","已证","done","Zd · zdistD · zdistD_add_le · zdistD_neg"),
 ("块方差矩阵 S^(B)(g)","已证","done","sbKernel · SB · SB_isSymm · SB_apply_add_right"),
 ("控制参数 ℓ_t 与 B_{t,K}","已证","done","ellT · Bparam · one_le_ellT"),
 ("确定性 ≺（从 RBM1D 原样搬来）","已证","done","UnifDetDom · DetDom · detDom_iff"),
 ("邻居计数 #{x : |x| = 1} = 2d","Q2 ✓ 已证","done","card_nbhd · card_adj"),
 ("‖S^(B)(g)‖ = 1","Q3 ✓ 已证","done","norm_SB · sum_SB_row"),
 ("S^(B)·1 = 1","Q4 ✓ 已证","done","SB_mulVec_one"),
])

CH2 = rows([
 ("Θ_ξ = Ring.inverse (1 − ξ S^(B))","已证","done","Theta · Theta0"),
 ("逆的唯一性 —— 本层的全部支点","已证","done","eq_Theta_of_mul · Theta_mul · mul_Theta"),
 ("性质 1 对称性","已证","done","Theta_transpose · Theta_isSymm"),
 ("性质 2 平移不变","已证","done","Theta_apply_add_right"),
 ("性质 3 交换性","已证","done","Theta_commute_SB · Theta_commute"),
 ("行和 Σ_b Θ_{ab} = (1−ξ)⁻¹","已证","done","Theta_mulVec_one · sum_Theta_row"),
 ("Neumann 级数 (eq;Taylor)","已证","done","Theta_eq_tsum"),
 ("性质 4 ‖Θ‖_{∞→∞} ≤ (1−t)⁻¹，并消掉 hS / hone","Q5 ✓ 已证","done","norm_Theta_le · norm_Theta_apply_le · *_of_three_le"),
 ("对 t 的求导 (2.51) ∂Θ = Θ S^(B) Θ —— Q22 的前置，RBM1D 处 92 行","Q23 · 可开工","ready","移植 RBM1D/Propagator/Deriv.lean"),
 ("性质 5 (prop:ThfadC) 多项式+指数衰减","接口假设","cited","ThetaDecay"),
 ("性质 5′ (prop:ThfadC_short)","接口假设","cited","ThetaDecayShort"),
 ("性质 6 (prop:BD1) 一阶差分 —— 所引文献里也没有证明；Q21 修正了 ≲ 的读法","接口假设","cited","ThetaDiffOne"),
 ("性质 7 (prop:BD2) 二阶差分 —— 同上，D12","接口假设","cited","ThetaDiffTwo"),
 ("性质 8 (prop:ThfadC0) 去零模","接口假设","cited","ThetaZeroMode · 打包为 structure PropTH"),
])

CH3 = rows([
 ("scaling order 的定义 (eq:ordG)","已证","done","Graph.Counters · Graph.ord"),
 ("case (ii)–(vi) 的算术记账","已证","done","ord_case_ii … ord_case_vi"),
 ("图模型 · case 分析穷尽性","Q6 ✓ 已证","done","Pattern.classify · classify_vi_occurs · ord_weight_step"),
 ("∂_h G = −G G：(Owx) 第三项产生三条新边的确定性一步","Q8 ✓ 已证","done","hasDerivAt_inverse_apply"),
 ("(Owx) / (Oe2x) 的 =𝔼 恒等式本身 —— 仅在蓝图，不写 axiom","规则 6 · 随机层","cited","见 paper-deltas D10"),
])

CH4 = rows([
 ("演化核 U^(n) 与 lem:sum_Ndecay","Q9 ✓ 已证","done","ThetaN · UN · norm_UN_le"),
 ("尾函数 𝒯_t 与截断版 wT^ℓ_{t,D}","Q10 ✓ 已证","done","tailT · tailW · zeroMode_le_of_ge · ellT_eq_of_le"),
 ("lem:propT 的卷积界 TTT2 —— 分析量最大的一条，拆成 K0–K5","Q11 ✓ 已证","done","Defs/Shells.lean · Defs/RadialSum.lean"),
 ("claim:TTk —— 第三轮发现漏截断之处，∧ℓ 与下标范围已逐条核实","Q12 ✓ 已证","done","sfT · PsiT · sfT_pair_cases"),
 ("lem:sum_decay_nonzero —— 第一条真正使用接口假设的定理，签名里写着借了什么","Q13 ✓ 已证","done","norm_zeroModeSet_UN_le · projMat_mul_Theta"),
 ("eq:latticesum_d3 —— 第三轮新加的那条临界格点求和，附录里唯一一处新数学","Q17a ✓ 已证","done","latticesum_d3 · sum_inv_Icc_le · sum_radial_tail_le"),
 ("(eq:decomp_U2) 子集展开与 (eq:decayXi) —— lem:sum_decay 的两块零件","Q17b ✓ 已证","done","UN_apply_eq_sum_powerset · norm_XiKer_apply_le · SB_apply_eq_zero_of_one_lt"),
 ("lem:sum_decay 的三条结论 —— 不能走 ‖Ξ‖ 捷径，须过 (deccA0) 球内截断","Q28 · 可开工","ready","sum_res_1 · sum_res_2_NAL · sum_res_2"),
 ("典范树划分 TSP(P_a) 与边值 —— 表示刻意与 RBM1D 对齐，为移植铺路","Q14 ✓ 已证","done","TSP · thetaEdge · treeVal · GammaN · GammaSum"),
 ("树表示 eq_Ktree —— 陈述层落地，eq_Ktree 暂作假设 KTreeRep（形状同 PropTH）","Q15 ✓ 已证","done","LoopIdx · treeEqRhs · IsKLoop · KTreeRep"),
 ("2-K-loop 的显式解 (Kn2sol) —— 本拍查明它能证，不必借","Q27 · 待 Q23","todo","Loop/Primitive.lean · 168 行"),
 ("Grönwall 唯一性 —— 落地后 KTreeRep 只欠存在性","Q22a · 待 Q27","todo","Loop/Unique.lean · 250 行"),
 ("树公式 = 存在性（真正的大件）","Q22b · 待 Q22a","todo","TreeRep.lean 729 + TreeRepGeneral.lean 2546"),
 ("lem_pureloop 同号 K-loop 的指数衰减（本文自足证）","Q16 ✓ n=2 · Q25 一般 n","ready","pureLoop_two · sum_exp_decay_conv"),
 ("ML:Kbound —— 论文说「需额外修改以处理 d ≥ 3」，先做陈述层并定位那处修改","Q24 · 可开工","ready","Loop/KBound.lean"),
])

QUEUE = """
<table class="q">
<thead><tr><th>#</th><th>工单</th><th>文件</th><th>状态</th></tr></thead>
<tbody>
<tr><td>Q1</td><td>让现有草稿编译通过</td><td><code>RBM3D/**</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q2</td><td>邻居计数 <code>#{|x| = 1} = 2d</code> —— 整层的地基</td><td><code>Defs/Block.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q3</td><td><code>‖S^(B)(g)‖ = 1</code></td><td><code>Defs/Block.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q4</td><td><code>S^(B)·1 = 1</code></td><td><code>Defs/Block.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q5</td><td>性质 4 的 (∞→∞) 范数界</td><td><code>Propagator/Props4.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q6</td><td>图模型 · case 穷尽性 <b>⭐</b></td><td><code>Graph/Model.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q7</td><td>核对 [yang2024Del] B.10 的 check 记号</td><td>查文献</td><td><span class="pill cited">降级 · 不在关键路径</span></td></tr>
<tr><td>Q8</td><td><code>(Owx)</code>/<code>(Oe2x)</code> 的确定性内核（决定不写 axiom）</td><td><code>Graph/Expansions.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q9</td><td>演化核 <code>U^(n)</code> 与 <code>lem:sum_Ndecay</code></td><td><code>Kernel/Evolution.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q10</td><td>尾函数 <code>𝒯_t</code> / <code>wT^ℓ_{t,D}</code></td><td><code>Defs/Tail.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q11</td><td><code>lem:propT</code> 的卷积界</td><td><code>Kernel/PropT.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q12</td><td><code>claim:TTk</code>（<code>∧ℓ</code> 截断）</td><td><code>Kernel/PropT.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q13</td><td><code>lem:sum_decay_nonzero</code></td><td><code>Kernel/Evolution.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q14</td><td>典范树划分 <code>TSP(P_a)</code> 与边值</td><td><code>Loop/Partition.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q15</td><td>树表示 <code>eq_Ktree</code> —— 陈述层落地，<code>eq_Ktree</code> 作假设</td><td><code>Loop/TreeRep.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q16</td><td><code>lem_pureloop</code> —— <code>n = 2</code> 已证，一般 <code>n</code> → Q25</td><td><code>Loop/PureLoop.lean</code></td><td><span class="pill done">PARTIAL</span></td></tr>
<tr><td>Q17a</td><td><code>eq:latticesum_d3</code>（第三轮新加的临界格点求和）</td><td><code>Kernel/SumDecay.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q17b</td><td><code>lem:sum_decay</code> 的两块零件 —— 三条结论 → Q28</td><td><code>Kernel/SumDecay.lean</code></td><td><span class="pill done">PARTIAL</span></td></tr>
<tr><td>Q18</td><td>让审计直接报定理数与公理承重情况</td><td><code>Test/Axioms.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q19</td><td><b>5 条接口 axiom 改成 <code>structure</code> 字段</b> —— 全项目零公理</td><td><code>Propagator/Interface.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q20</td><td><code>(eq:key_T_reudce)</code> 求和版（带 <code>≺</code>）</td><td><code>Kernel/PropT.lean</code></td><td><span class="pill draft">认领中</span></td></tr>
<tr><td>Q21</td><td><b>逐字核对剩下四条接口陈述</b> —— 又修正 1 条，新增 1 条反例</td><td><code>Propagator/Interface.lean</code></td><td><span class="pill done">DONE</span></td></tr>
<tr><td>Q23</td><td><b>传播子对 <code>t</code> 的求导层</b> <b>⭐</b> —— <b>主线第一步</b>，RBM1D 处只有 92 行</td><td><code>Propagator/Deriv.lean</code></td><td><span class="pill ready">OPEN</span></td></tr>
<tr><td>Q27</td><td><b>证出 <code>KTwoFormula</code></b> —— 主线第二步，168 行</td><td><code>Loop/Primitive.lean</code></td><td><span class="pill todo">待 Q23</span></td></tr>
<tr><td>Q22a</td><td><b>Grönwall 唯一性</b> —— 主线第三步；落地后 <code>KTreeRep</code> 只欠存在性</td><td><code>Loop/Unique.lean</code></td><td><span class="pill todo">待 Q27</span></td></tr>
<tr><td>Q22b</td><td>树公式 = 存在性（真正的大件）</td><td><code>Loop/TreeRep*.lean</code></td><td><span class="pill todo">待 Q22a</span></td></tr>
<tr><td>Q24</td><td><code>ML:Kbound</code> <b>⭐</b> —— 论文说「需额外修改以处理 <code>d ≥ 3</code>」</td><td><code>Loop/KBound.lean</code></td><td><span class="pill ready">OPEN</span></td></tr>
<tr><td>Q25</td><td><code>lem_pureloop</code> 的一般 <code>n</code></td><td><code>Loop/PureLoop.lean</code></td><td><span class="pill ready">OPEN</span></td></tr>
<tr><td>Q26</td><td><b>审计自动发现借用谓词 + 分两本账</b> <b>⭐</b> —— <code>KTwoFormula</code> 已漏报</td><td><code>Test/Axioms.lean</code></td><td><span class="pill ready">OPEN</span></td></tr>
<tr><td>Q28</td><td><code>lem:sum_decay</code> 的三条结论（<code>sum_res_1</code> / <code>(I)</code> / <code>(II)</code>）</td><td><code>Kernel/SumDecay.lean</code></td><td><span class="pill ready">OPEN</span></td></tr>
</tbody></table>
"""

HTML = """<title>d≥3 Band Blueprint</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Newsreader:opsz,wght@6..72,400;6..72,600&family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&display=swap">
<style>
:root{
  --bg:#f5f7f8; --surface:#fff; --border:#dfe4e9; --ink:#141a20; --muted:#6d7883;
  --accent:#2c4a7c; --done:#1a8a5e; --done-bg:#e3f3ec; --ready:#1a8a5e; --ready-bg:#e3f3ec;
  --draft:#3d74ad; --draft-bg:#e2edf7; --todo:#8d97a2; --todo-bg:#eceff2;
  --cited:#9a7328; --cited-bg:#fbf1de;
  --plate:#f8fafb; --plate-border:#dde3e8;
  --edge:#aeb6bf; --axband:rgba(154,115,40,.07); --axline:#cda85f; --axtext:#9a7328;
}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
  --bg:#11161b; --surface:#191f26; --border:#2a333c; --ink:#e5e9ed; --muted:#98a3ae;
  --accent:#8fb4e0; --done:#4bc094; --done-bg:#14302a; --ready:#4bc094; --ready-bg:#14302a;
  --draft:#79a9d8; --draft-bg:#16283a; --todo:#8e99a4; --todo-bg:#222a32;
  --cited:#d7ab5f; --cited-bg:#2e2617;
  --plate:#e7ebee; --plate-border:#c7ced4;
  --edge:#8d97a2; --axband:rgba(154,115,40,.10); --axline:#a8823c; --axtext:#7a5c1e;
}}
:root[data-theme="dark"]{
  --bg:#11161b; --surface:#191f26; --border:#2a333c; --ink:#e5e9ed; --muted:#98a3ae;
  --accent:#8fb4e0; --done:#4bc094; --done-bg:#14302a; --ready:#4bc094; --ready-bg:#14302a;
  --draft:#79a9d8; --draft-bg:#16283a; --todo:#8e99a4; --todo-bg:#222a32;
  --cited:#d7ab5f; --cited-bg:#2e2617;
  --plate:#e7ebee; --plate-border:#c7ced4;
  --edge:#8d97a2; --axband:rgba(154,115,40,.10); --axline:#a8823c; --axtext:#7a5c1e;
}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);
  font-family:"IBM Plex Sans",system-ui,-apple-system,sans-serif;font-size:15px;line-height:1.55;
  -webkit-font-smoothing:antialiased}
.wrap{max-width:1000px;margin:0 auto;padding-inline:16px;padding-block:40px 64px}
header{border-bottom:1px solid var(--border);padding-bottom:22px;margin-bottom:26px}
.eyebrow{font-size:11px;letter-spacing:.14em;text-transform:uppercase;color:var(--muted);margin:0 0 8px}
h1{font-family:"Newsreader",Georgia,serif;font-weight:600;font-size:clamp(26px,4.4vw,38px);
  line-height:1.15;margin:0 0 6px;text-wrap:balance;letter-spacing:-.01em}
.sub{color:var(--muted);margin:0;font-size:14px}
.chips{display:flex;flex-wrap:wrap;gap:10px;margin-top:20px}
.chip{display:flex;align-items:baseline;gap:8px;background:var(--surface);
  border:1px solid var(--border);border-radius:6px;padding:9px 13px}
.chip b{font-size:19px;font-weight:600;font-variant-numeric:tabular-nums}
.chip span{font-size:12.5px;color:var(--muted)}
.chip.done b{color:var(--done)} .chip.cited b{color:var(--cited)}
.chip.ready b{color:var(--ready)} .chip.todo b{color:var(--todo)}
h2{font-family:"Newsreader",Georgia,serif;font-weight:600;font-size:21px;margin:38px 0 4px}
h2+p{margin:0 0 16px;color:var(--muted);font-size:13.5px}
.legend{display:flex;flex-wrap:wrap;gap:14px;margin:18px 0 0;font-size:13px;color:var(--muted)}
.legend i{display:inline-block;width:11px;height:11px;border-radius:3px;margin-right:7px;
  vertical-align:-1px;border:1px solid rgba(0,0,0,.18)}
.plate{background:var(--plate);border:1px solid var(--plate-border);border-radius:8px;
  padding:10px;overflow-x:auto}
svg.dep{display:block;min-width:640px;width:100%;height:auto}
.plate.wide svg.dep{min-width:1000px}
ul.rows{list-style:none;margin:14px 0 0;padding:0;border-top:1px solid var(--border)}
.row{display:flex;flex-wrap:wrap;gap:6px 16px;justify-content:space-between;align-items:baseline;
  padding:10px 2px;border-bottom:1px solid var(--border)}
.row-main{display:flex;flex-wrap:wrap;align-items:baseline;gap:10px;min-width:0}
.row-name{font-weight:500}
.row-side{display:flex;flex-wrap:wrap;align-items:baseline;gap:10px;min-width:0}
.pill{font-size:11.5px;padding:2px 8px;border-radius:99px;white-space:nowrap}
.pill.done{color:var(--done);background:var(--done-bg)}
.pill.ready{color:var(--ready);background:var(--ready-bg)}
.pill.todo{color:var(--todo);background:var(--todo-bg)}
.pill.cited{color:var(--cited);background:var(--cited-bg)}
code{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12px;color:var(--muted);
  overflow-wrap:anywhere}
.note{background:var(--surface);border:1px solid var(--border);border-left:3px solid var(--cited);
  border-radius:0 6px 6px 0;padding:15px 17px;margin-top:22px;font-size:13.5px;color:var(--muted)}
.note.acc{border-left-color:var(--accent)}
.note strong{color:var(--ink);font-weight:600}
.note p{margin:0 0 9px} .note p:last-child{margin:0}
table.q{width:100%;border-collapse:collapse;margin-top:14px;font-size:13.5px}
table.q th{text-align:left;font-size:11px;letter-spacing:.1em;text-transform:uppercase;
  color:var(--muted);font-weight:500;padding:0 10px 8px 0;border-bottom:1px solid var(--border)}
table.q td{padding:9px 10px 9px 0;border-bottom:1px solid var(--border);vertical-align:top}
table.q td:first-child{font-variant-numeric:tabular-nums;color:var(--muted);width:2.6em}
footer{margin-top:36px;padding-top:16px;border-top:1px solid var(--border);
  font-size:12.5px;color:var(--muted)}
@media (max-width:640px){.row{flex-direction:column;align-items:flex-start}}
</style>

<div class="wrap">
<header>
  <p class="eyebrow">Lean 4 · Mathlib · 形式化蓝图</p>
  <h1>d ≥ 3 非平均场随机矩阵的退局域化</h1>
  <p class="sub">Dubova · F. Yang · H.-T. Yau · J. Yin，<em>Delocalization of Non-Mean-Field Random Matrices in Dimensions d ≥ 3</em>（arXiv:2507.20274）· Lean 4.34.0 / Mathlib v4.34.0 · <code>~/Lean_proof/RBM3D</code></p>
  <div class="chips">
    <div class="chip done"><b>291</b><span>定理已证</span></div>
    <div class="chip done"><b>0</b><span>sorry</span></div>
    <div class="chip done"><b>0</b><span>项目公理</span></div>
    <div class="chip ready"><b>5</b><span>可立即开工</span></div>
  </div>
</header>

<div class="note">
<p><strong>这个项目和两个姊妹项目形状不同，先读这一段。</strong></p>
<p>d = 2 那篇论文在它的 §8 里从零证明了传播子衰减估计，所以 <code>RBM2D</code> 里那些是<em>定理</em>。
这篇论文没有：<code>lem_propTH</code> 的性质 5–8 分别归给 <code>[DYYY25]</code> Lemma 2.14、
<code>[yang2024Del]</code> Lemma 3.1 与 (E.19)，其中 <code>(prop:BD1)</code> 论文自己说
“not stated explicitly in [yang2024Del] … we omit the details”——它在所引文献里根本没有显式证明。
附录 B 的三条 expansion 引理（块 Anderson 线）同样引自 <code>[yang2024Del]</code> B.9–B.11；
随机带矩阵线实际用的 <code>(Owx)</code>、<code>(Oe2x)</code> 则引自 <code>[yang2021delocalization]</code>
Lemma 3.5 / 3.14。</p>
<p><strong>这些借来的结论不是 <code>axiom</code>，是假设。</strong> 它们写成
<code>Propagator/Interface.lean</code> 里的五条 <code>Prop</code> 定义（<code>ThetaDecay</code>、
<code>ThetaDiffOne</code> …），打包成 <code>structure PropTH</code>。用到它们的定理多带一个参数
<code>(hP : PropTH d g m)</code>，取 <code>hP.decay</code>。</p>
<p>这比写公理好在两处。<strong>一是可见</strong>：依赖关系出现在每条定理的类型里，调用处一眼看得见，
而不是躲在 <code>#print axioms</code> 里等人去查。<strong>二是可卸</strong>：哪天有人真把某一条证出来了，
<em>原地把假设换成定理，签名一个字不改</em>，依赖它的工单一张都不用返工——这正是本项目已经发生过一次的事，
<code>Propagator/Basic.lean</code> 整层当初带着假设 <code>hS</code> 证完，Q3/Q4 落地后假设被消掉，下游零改动。
<code>axiom</code> 做不到这件事。</p>
<p>结果是：<strong>全项目零公理。</strong> <code>Test/Axioms.lean</code> 的审计现在只允许
<code>propext</code> / <code>Classical.choice</code> / <code>Quot.sound</code>，与两个姊妹项目同标准，
违规即构建失败。下面每张图顶部色带内的节点，就是这五条假设——<strong>整张图里只有那一条带是借来的，
其余每个绿色节点都是在 Lean 里证出来的</strong>。</p>
</div>

<div class="note">
<p><strong>形式化已经抓到一处真缺陷，值得单独说。</strong></p>
<p>接口的第二条 <code>(prop:ThfadC_short)</code> 原先写成「对任意 <code>‖m‖ = 1</code>」。
论文写的不是这个——原文是「Furthermore, <strong>when σ₁ = σ₂</strong>, we have a much stronger
exponential decay」。<strong>论文是对的，漏掉那个限定的是形式化</strong>（Cowork 在第一拍写接口时写错的）。
σ₁ ≠ σ₂ 对应谱参数 <code>1</code>，那时 <code>Σ_b Θ_{t,0b} = (1−t)⁻¹</code> 发散，而右端与 <code>t</code>
无关且可求和——<strong>该陈述为假</strong>。</p>
<p>三点后果值得记住。<strong>一、它当 <code>axiom</code> 的那段时间，整个项目是不一致的</strong>——
从一条假命题出发什么都能证。<strong>二、公理审计查不出这种错</strong>：审计管的是「用了哪些公理」，
不管「公理说得对不对」。<strong>三、发现它的不是任何自动机制，是 Q13 第一次真去用它。</strong>
一条没人使用的接口陈述，等于没被检验过。</p>
<p>改法有两层：陈述修正为 <code>t·m²</code> 且要求 <code>0 &lt; m.im</code>；另加一条
<strong>负面测试</strong> <code>not_decayShort_at_one</code>，<em>机器证明</em>旧写法在谱参数 <code>1</code>
处不成立。</p>
<p><strong>Q21 把其余四条逐字重核了一遍，又抓到一处。</strong> 性质 6、7 里论文写的是
<code>|r| ≲ |a|</code>，形式化写成了 <code>|r| ≤ |a|</code>——但 <code>≲</code> 是个量词
（「存在常数 <code>c</code>，<code>|r| ≤ c|a|</code>」），放在前件位置忠实的写法是
<strong><code>∀ c &gt; 0</code></strong>。已改（D12）。性质 5、8 与论文一致；性质 8 另加了反例
<code>not_zeroMode_without_removal</code>，证明把 <code>Θ̊</code> 换回 <code>Θ</code> 在谱参数
<code>1</code> 处可证伪——<em>零模去除就是那条估计的全部内容</em>。</p>
<p>两处缺陷是同一个错误的两件外衣：<strong>论文里的限定词在翻译中丢了</strong>。
所以 <code>CLAUDE.md</code> 现在写死两条：<code>≲ ≺ ≍ ∼</code> 一律当量词读，不是不等号；
以及改正一条陈述时，<strong>留下一个随全量构建跑的机器可检反例</strong>——比注释可靠，比复述准确。</p>
</div>

<div class="legend">
  <span><i style="background:#1a8a5e"></i>已在 Lean 中证明</span>
  <span><i style="background:#cfe9dc"></i>定义（已形式化）</span>
  <span><i style="background:#3d74ad"></i>依赖就绪，可开工</span>
  <span><i style="background:#fbf1de"></i>接口假设 · 论文引用而未证</span>
  <span><i style="background:#ffffff"></i>尚被上游阻塞</span>
  <span><i style="background:#146b4a"></i>机器检查收益最高的节点</span>
</div>

<h2>全局依赖图</h2>
<p>四章全部节点与跨章依赖。①–④ 是章号，箭头由前提指向结论。顶部色带内是论文引用而未证的结论——<strong>整张图里只有那一条带是借来的，其余每个绿色节点都是在 Lean 里证出来的</strong>。</p>
<div class="plate wide">__G0__</div>

<h2>第 1 章 · 格点与模型</h2>
<p>§2.1 与 §2.5 的定义层：环面 Z_L^d、周期 ℓ¹ 距离、块方差矩阵 S^(B)(g)、控制参数 ℓ_t 与 B_{t,K}。d 全程是参数，<code>3 ≤ d</code> 只在真正用到的地方引入。</p>
<div class="plate">__G1__</div>
__CH1__

<div class="note acc">
<p><strong>Q2 是整层的地基。</strong> 邻居计数 <code>#{x : |x| = 1} = 2d</code> 看着不起眼，
但 <code>‖S^(B)‖ = 1</code> 和 <code>S^(B)·1 = 1</code> 都归结到它，而第 2 章每一条结构引理
现在都带着假设 <code>hS : ‖S^(B)(g)‖ = 1</code>。<strong>做完 Q2，传播子那一层立刻全部解除假设。</strong>
这也正是 <code>3 ≤ L</code> 的来源：L = 2 时 <code>1 = −1</code>，2d 个邻居塌成 d 个。</p>
</div>

<h2>第 2 章 · 传播子 Θ</h2>
<p>整层只靠一条引理撑着：<code>eq_Theta_of_mul</code>——<em>任何</em> 1 − ξS^(B) 的左逆<em>就是</em> Θ_ξ。要证 Θ 有某个性质，就构造一个有那个性质的左逆，再引唯一性。这条路线从 RBM1D 逐行移植，其中没有一步用到维数。</p>
<div class="plate">__G2__</div>
__CH2__

<h2>第 3 章 · 附录 B · scaling order</h2>
<p>ord(Γ) = n_S + 2(n_W − n_V) 的记账，以及 <code>lem_scalingorder</code> 的 case 分析。</p>
<div class="plate">__G3__</div>
__CH3__

<div class="note acc">
<p><strong>Q6 是这个项目机器检查收益最高的一块，而且现在就能动。</strong></p>
<p>第三轮人工校对在附录 B 发现漏掉了一种情形 case (vi)。但它的算术与 case (iv) 完全相同——
<code>ord_case_vi</code> 在 Lean 里就是 <code>ord_case_iv</code> 的推论。
<strong>只检查算术的形式化抓不到它</strong>：漏的是情形枚举，不是不等式。</p>
<p>所以真正的价值在把图的构型做成一个归纳类型，让 <code>cases</code> 的穷尽性由编译器保证。
验收标准很干脆：<em>删掉 case (vi) 那一个分支，编译器应当报 non-exhaustive。</em>
做到这一点，这个项目就有了第三轮人工校对没有的保证。</p>
</div>

<h2>第 4 章 · 附录 A · 确定性估计</h2>
<p>以 <code>lem_propTH</code> 为输入、<strong>本文自足</strong>的推导——这一章不引用任何外部结论，是接下来的主战场。第三轮补写隐含步骤最多的也是这里。Q9 与 Q10 文件不相交，可并行。</p>
<div class="plate">__G4__</div>
__CH4__

<h2>工单队列</h2>
<p>Claude Code 从 <code>docs/QUEUE.md</code> 从上往下领第一条 OPEN。此表每次心跳刷新。
主线四条（<b>Q23 → Q27 → Q22a → Q22b</b>）已按依赖顺序排在一起，未满足前置的标「待 Qxx」而不是 OPEN——
标成 OPEN 却开不了工，和该解封时忘了解封一样费一拍。</p>
__QUEUE__

<div class="note">
<p><strong>每条都编过。</strong> 磁盘腾出来之后 <code>lake exe cache get</code> + <code>lake build</code> 已在本机跑通，
从此每次回报前必须有一次 <code>./check.sh</code> → <code>exit=0</code>（最近一次：<code>errors: 0</code>、2550 jobs、审计干净）。
上面所有条目都是编译通过的定理，不是草稿。</p>
<p><strong>借来的结果开始承重了。</strong> Q18 让审计报出「有多少条定理的类型里带着接口假设」：
目前 <code>ThetaDecay: 1</code>、<code>ThetaDecayShort: 4</code>、<code>ThetaZeroMode: 2</code>，其余为 0。
在 Q13 之前，全项目没有任何结论依赖论文引用的估计；现在有了，而且<em>写在定理的签名里</em>。</p>
<p><strong>但这份报告本身有个缺口，本拍抓到了。</strong> 它的名单是手写的六条。
紧接 Q18 的 Q16 引入了第七条假设 <code>KTwoFormula</code>，<em>不在名单里，审计一声不吭</em>——
一份声称「全部记账」的报告漏了记，这比没有报告更危险。Q26 就是去修它：
让审计自己发现前件，而不是等人登记。</p>
<p><strong>还要分两本账。</strong> <em>借来的</em>是论文引文献而未证的（<code>PropTH</code> 五条、
<code>KTreeRep</code>）；<em>欠下的</em>是本可以在这里证、只为往前走而先假设的。
本拍算明白 <code>KTwoFormula</code> 属于第二本：<code>IsKLoop</code> 已经是「树方程 ODE + 初值」的刻画，
而 <code>(Kn2sol)</code> 的显式解 <code>W^(−d) m₁m₂ Θ_{t m₁m₂}</code> 恰好满足同一个方程与同一个初值
（求导用 Q23，右端用 Q15 已证的 <code>treeEqRhs_two</code>，初值用 <code>Θ₀ = 1</code>）。
<strong>两本账混在一起，「零公理」这个标题就比实情好看。</strong></p>
</div>

<footer>
  计数说明：<b>291 定理 / 134 定义 / 0 公理</b> 由 <code>./check.sh</code> 的审计直接报出（Q18），
  编译器生成的声明已排除。<br>
  蓝图由 Cowork 侧维护，约每 10 分钟随工单队列一同刷新 · beat 11 · 2026-09-20 06:00 UTC<br>
  姊妹项目：<code>~/Lean_proof/RBM1D</code>（d=1，已完整编译，2082 条声明，公理干净）·
  <code>~/Lean_proof/RBM2D</code>（d=2）
</footer>
</div>
"""

out = (HTML.replace("__G0__", G0).replace("__G1__", G1).replace("__G2__", G2).replace("__G3__", G3)
           .replace("__G4__", G4).replace("__CH1__", CH1).replace("__CH2__", CH2)
           .replace("__CH3__", CH3).replace("__CH4__", CH4).replace("__QUEUE__", QUEUE))
open("/home/claude/bp/blueprint.html","w").write(out)
print("bytes:", len(out))
