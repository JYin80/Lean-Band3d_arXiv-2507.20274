from gen import build

W  = 860    # 章节图
WG = 1280   # 全局图

BAND = "接口层 · 论文引用而未证 · 现为 PropTH 的假设，非 axiom"

# ─────────────────────────── 全局图：四章所有节点 ───────────────────────────
g0 = build(
 nodes=[
  ("ax","接口假设 PropTH · lem_propTH 性质 5–8","axiom",0),

  ("lat","① Z_L^d · 周期 ℓ¹ 距离","def",1),
  ("prec","① ≺ (DetDom)","def",1),
  ("par","① ℓ_t · B_{t,K}","def",1),

  ("sb","① S^(B)(g)","def",2),
  ("tail","④ 尾函数 𝒯_t · wT","done",2),
  ("ord","③ ord = n_S+2(n_W−n_V)","def",2),

  ("cnt","① 邻居计数 = 2d","done",3),
  ("th","② Θ_ξ = (1−ξS)⁻¹","def",3),
  ("arith","③ case (ii)–(vi) 算术","done",3),
  ("exp","③ ∂_h G = −G·G","done",3),

  ("nrm","① ‖S^(B)‖=1","done",4),
  ("one","① S^(B)·1=1","done",4),
  ("uniq","② 逆唯一性","done",4),
  ("model","③ 图模型穷尽性","star",4),
  ("part","④ Q14 ✓ 树划分","done",4),

  ("p123","② 性质 1–3","done",5),
  ("row","② 行和 = (1−ξ)⁻¹","done",5),
  ("pt","④ Q11 lem:propT","done",5),
  ("ttk","④ Q12 claim:TTk","done",5),
  ("tree","④ Q15 树表示（假设）","done",5),
  ("deriv","② Q23 ✓ ∂Θ = ΘSΘ","done",5),

  ("p4","② 性质 4  ‖Θ‖ ≤ (1−t)⁻¹","done",6),
  ("ksum","④ Q20 求和版","todo",6),
  ("prim","④ Q27 ✓ (Kn2sol) 显式解","done",6),

  ("uk","④ Q9 U^(n) · lem:sum_Ndecay","done",7),
  ("pure","④ Q16 n=2 ✓ · Q25 一般 n","ready",7),
  ("uniq22","④ Q22a ✓ 唯一性 ⇒ KTwoFormula 已消","star",7),

  ("nz","④ Q13 ✓ sum_decay_nonzero","done",8),
  ("sd","④ Q17a ✓ · Q17b ✓ · Q28 待做","ready",8),
  ("ktree","④ Q22b ✓ n=3 · Q30 n=4 · Q31 一般 n","ready",8),
  ("kb","④ Q24 ✓ d≥3 那步已定位","done",8),
 ],
 edges=[
  ("lat","sb"),("lat","par"),("par","tail"),
  ("sb","cnt"),("sb","th"),
  ("cnt","nrm"),("cnt","one"),
  ("th","uniq"),("nrm","uniq"),
  ("uniq","p123"),("uniq","row"),("one","row"),
  ("row","p4"),("nrm","p4"),
  ("p4","uk"),("th","uk"),
  ("uk","nz"),("uk","sd"),
  ("tail","pt"),("tail","ttk"),("ttk","ksum"),
  ("ord","arith"),("arith","model"),("exp","model"),
  ("th","part"),("part","tree"),("tree","pure"),
  ("uniq","deriv"),("deriv","prim"),("tree","prim"),
  ("prim","pure"),("prim","uniq22"),("uniq22","ktree"),("tree","ktree"),
  ("tree","kb"),("pure","kb"),
  ("ax","nz","d"),("ax","sd","d"),("ax","pure","d"),
 ],
 width=WG, band=1, band_label=BAND)

# ─────────────────────────── 章节图 ───────────────────────────
g1 = build(
 nodes=[
  ("lat","Z_L^d  ·  |x| 周期 ℓ¹","def",0),
  ("prec","≺   DetDom","def",0),
  ("sb","S^(B)(g)   (eq:variancematrix)","def",1),
  ("par","ℓ_t ,  B_{t,K}","def",1),
  ("cnt","Q2 ✓ 邻居计数  #{|x|=1} = 2d","done",2),
  ("nrm","Q3 ✓ ‖S^(B)‖ = 1","done",3),
  ("one","Q4 ✓ S^(B)·1 = 1","done",3),
 ],
 edges=[("lat","sb"),("lat","par"),("sb","cnt"),("cnt","nrm"),("cnt","one")],
 width=W)

g2 = build(
 nodes=[
  ("ax1","(prop:ThfadC)","axiom",0),
  ("ax2","(prop:ThfadC_short)","axiom",0),
  ("ax3","(prop:BD1)","axiom",0),
  ("ax4","(prop:BD2)","axiom",0),
  ("ax5","(prop:ThfadC0)","axiom",0),
  ("th","Θ_ξ = Ring.inverse (1 − ξ S^(B))","def",1),
  ("uniq","eq_Theta_of_mul   逆的唯一性","done",2),
  ("p12","性质 1–2   对称 · 平移不变","done",3),
  ("p3","性质 3   交换性","done",3),
  ("row","行和 = (1−ξ)⁻¹","done",3),
  ("p4","Q5 ✓ 性质 4  ‖Θ‖ ≤ (1−t)⁻¹","done",4),
  ("deriv","Q23 ✓ ∂_t Θ = Θ S^(B) Θ   (2.51)","done",4),
 ],
 edges=[("th","uniq"),("uniq","p12"),("uniq","p3"),("uniq","row"),("row","p4"),
        ("uniq","deriv")],
 width=W, band=1, band_label=BAND)

g3 = build(
 nodes=[
  ("b9","(Owx) 权展开 · (Oe2x) GG 展开","axiom",0),
  ("ord","ord = n_S + 2(n_W − n_V)","def",1),
  ("exp","Q8 ✓ ∂_h G = −G·G  确定性内核","done",1),
  ("arith","case (ii)–(vi)  算术记账","done",2),
  ("model","Q6 ✓ 图模型 · case 穷尽性","star",3),
 ],
 edges=[("ord","arith"),("arith","model"),("exp","model"),("b9","model","d")],
 width=W, band=1, band_label="接口层 · 不写成 axiom，见 paper-deltas D10")

g4 = build(
 nodes=[
  ("ax1","(prop:ThfadC) · (prop:ThfadC_short)","axiom",0),
  ("uk","Q9 ✓ U^(n) · lem:sum_Ndecay","done",1),
  ("tail","Q10 ✓ 尾函数 𝒯_t , wT^ℓ_{t,D}","done",1),
  ("part","Q14 ✓ 典范树划分 TSP(P_a)","done",1),
  ("nz","Q13 ✓ lem:sum_decay_nonzero","done",2),
  ("sd","Q17a ✓ latticesum_d3","done",2),
  ("pt","Q11 ✓ lem:propT 卷积界","done",2),
  ("ttk","Q12 ✓ claim:TTk (∧ℓ 截断)","done",2),
  ("tree","Q15 ✓ 树表示（eq_Ktree 作假设 KTreeRep）","done",3),
  ("ksum","Q20 · 求和版 key_T_reudce","todo",3),
  ("sdb","Q17b ✓ 两块零件（decomp_U2 · decayXi）","done",3),
  ("sd3","Q28 · sum_decay 的三条结论","ready",4),
  ("prim","Q27 ✓ (Kn2sol) 显式解 + norm_kTwo_le","done",4),
  ("pure","Q16 ✓ n=2 · Q25 一般 n","ready",5),
  ("uniq22","Q22a ✓ 唯一性 ⇒ KTwoFormula 从假设变定理","star",5),
  ("ktree","Q22b ✓ n=3 · Q30 n=4 · Q31 一般 n","ready",6),
  ("kb","Q24 ✓ 那句「额外修改」已定位 · 格点和 → Q32","done",6),
 ],
 edges=[("uk","nz"),("uk","sd"),("tail","pt"),("tail","ttk"),("ttk","ksum"),
        ("part","tree"),("sd","sdb"),("uk","sdb"),("sdb","sd3"),("sd","sd3"),("tree","prim"),
        ("prim","pure"),("prim","uniq22"),("uniq22","ktree"),
        ("tree","kb"),("pure","kb"),
        ("ax1","nz","d"),("ax1","sdb","d"),("ax1","pure","d")],
 width=W, band=1, band_label=BAND)

# ─────────────────────────── 第 5 章 · 随机层（beat 15 新开） ───────────────────────────
g5 = build(
 nodes=[
  ("audit","随机层审计 ✓ —— 没有 Doob / Markov / 域流 / 两时刻联合律","star",0),
  ("env","Q42 · 确定性包络 ‖G‖ ≤ η⁻¹（免费，解锁全部）","ready",1),
  ("stein","Q43 · Stein 三层（重采样路线，与 d 无关）","ready",1),
  ("gen","Q44 · 生成元恒等式 —— 二阶项 = 二次变差 (E⊗E)","todo",2),
  ("gron","Q45 · 对矩的 Grönwall + 两座 ≺ 桥 + 连续归纳","todo",3),
  ("stop","Q46 · 三处停时 → 连续归纳（等作者回答）","todo",4),
 ],
 edges=[("audit","env"),("audit","stein"),("stein","gen"),
        ("gen","gron"),("env","gron"),("gron","stop")],
 width=W)

# ─────────────────────────── 第 6 章 · 非空洞证书链 ───────────────────────────
g6 = build(
 nodes=[
  ("cert","Q41 ✓ 提出「固定 L 版证书」：假设可满足吗","star",0),
  ("obst","Q41 ✓ 四条的障碍已机器化（尺寸界给不出来）","done",1),
  ("gap1","Q51 ✓ 连通性 + Doeblin 极小化条件","done",2),
  ("gap2","Q52 ✓ Dobrushin 收缩 + 几何混合","done",3),
  ("c0","Q53 ✓ (prop:ThfadC0) 的证书 —— 靠去零模后的相消","done",4),
  ("bd","Q54 ✓ BD1 / BD2 / PropTH 的证书 —— 审计 6 of 9","done",5),
  ("short","(prop:ThfadC_short) 仍无证书","todo",5),
 ],
 edges=[("cert","obst"),("obst","gap1"),("gap1","gap2"),("gap2","c0"),
        ("c0","bd"),("obst","short")],
 width=W)

open("graphs.py","w").write("G0=%r\nG1=%r\nG2=%r\nG3=%r\nG4=%r\nG5=%r\nG6=%r\n" % (g0,g1,g2,g3,g4,g5,g6))
print("ok", [len(x) for x in (g0,g1,g2,g3,g4,g5,g6)])
