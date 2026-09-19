from gen import build
W = 860

g1 = build(
 nodes=[
  ("lat","Z_L^d  ·  |x| 周期 ℓ¹","def",0),
  ("prec","≺   DetDom","def",0),
  ("sb","S^(B)(g)   (eq:variancematrix)","def",1),
  ("par","ℓ_t ,  B_{t,K}","def",1),
  ("cnt","Q2 · 邻居计数  #{|x|=1} = 2d","ready",2),
  ("nrm","Q3 · ‖S^(B)‖ = 1","todo",3),
  ("one","Q4 · S^(B)·1 = 1","todo",3),
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
  ("uniq","eq_Theta_of_mul   逆的唯一性","draft",2),
  ("p12","性质 1–2   对称 · 平移不变","draft",3),
  ("p3","性质 3   交换性","draft",3),
  ("row","行和 = (1−ξ)⁻¹","draft",3),
  ("p4","Q5 · 性质 4  ‖Θ‖ ≤ (1−t)⁻¹","todo",4),
 ],
 edges=[("th","uniq"),("uniq","p12"),("uniq","p3"),("uniq","row"),("row","p4"),
        ("th","ax1","d"),("th","ax3","d"),("th","ax5","d")],
 width=W, band=1, band_label="以下 · 接口公理 · 论文引用而未证")

g3 = build(
 nodes=[
  ("b9","B.9  基本展开","axiom",0),
  ("b10","B.10  权展开   ⚠ Q7 待核","axiom",0),
  ("b11","B.11  GG 展开","axiom",0),
  ("ord","ord = n_S + 2(n_W − n_V)","def",1),
  ("arith","case (ii)–(vi)  算术记账","draft",2),
  ("model","Q6 · 图模型 · case 穷尽性","ready",3),
 ],
 edges=[("ord","arith"),("arith","model"),("b9","model","d"),("b10","model","d"),("b11","model","d")],
 width=W, band=1, band_label="以下 · 接口公理 · 论文引用而未证")

g4 = build(
 nodes=[
  ("tr","[YY_25] Lem 3.4  树表示","axiom",0),
  ("uk","A.2  U^(n) 分解 · Q^(A) · I_diff(σ)","todo",1),
  ("pt","A.3–A.4  lem:propT · claim:TTk","todo",2),
  ("kl","A.5  典范划分 · K-loop","todo",2),
 ],
 edges=[("uk","pt"),("uk","kl"),("tr","kl","d")],
 width=W, band=1, band_label="以下 · 接口公理")

open("graphs.py","w").write("G1=%r\nG2=%r\nG3=%r\nG4=%r\n" % (g1,g2,g3,g4))
print("ok", [len(x) for x in (g1,g2,g3,g4)])
