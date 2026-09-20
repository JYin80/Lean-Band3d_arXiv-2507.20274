# Cowork 侧的蓝图生成脚本

蓝图页面（Artifact）由 Cowork 每 10 分钟心跳时重建并 republish 到同一个 URL。
脚本放在这里是为了在云端容器被清空后还能取回。

* `gen.py` —— 分层 DAG → SVG。节点给定所在行，行内自动均分 x。
  `KIND` 决定配色：`def` 定义 / `draft` 已写未编译 / `ready` 可开工 / `todo` 待解锁 /
  `axiom` 接口公理 / `star` 高价值节点。`band=<行号>` 画出接口公理分界带。
* `mk3.py` —— **全局图 + 四章图**的节点与边，产出 `graphs.py`（取代旧的 `mk2.py`）。
  `G0` 是全局图：四章全部节点与跨章依赖，节点标签以 ①–④ 标章号。
* `page.py` —— 读 `graphs.py`，拼出整页 HTML 到 `blueprint.html`。

用法（在云端容器里）：

```bash
mkdir -p /home/claude/bp && cd /home/claude/bp
# 从这里取回 gen.py mk2.py page.py
python3 mk3.py && python3 page.py
# 然后 Artifact 工具 file_path=/home/claude/bp/blueprint.html republish
```

**这不是 `leanblueprint` 的产物。** 正式的 leanblueprint 站点走 `blueprint/src/` +
`blueprint.yml`，见 `docs/TASKS.md` 的 T12；这一份是给 Jun 在会话里跟进度用的活页。
两者的节点名保持一致（都对着论文的 label）。

## 两个踩过的坑

* **字宽要分中西文。** `textw()` 把 CJK 字形按两倍 ASCII 计宽。早先按 `len(label)` 统一算，
  中文节点的框画得比文字窄，相邻标签就会叠在一起——全局图第 4 行叠过一次。
* **接口色带是顶部条带。** `band=N` 表示**最上面 N 行**是接口层，色带从画布顶画到第 N 行下沿。
  早先的实现是从第 N 行往下画，而公理在第 0 行，于是「以下 · 接口公理」这个标注指错了区域。

## 同步回本机的注意事项（beat 10 记）

`device_commit_files` **报成功却写了旧内容**，已出现两次（beat 8、beat 10）。
所以每次把 `mk3.py` / `page.py` 同步回来之后，**必须 grep 一个本次新增的标记再下结论**
（例如 `grep -c Q27 page.py`），不能信它的返回值。

对不上就改走本机直接改：把同一份 patch 脚本 heredoc 到 `/tmp` 里，在这个目录跑一遍
（脚本里每处替换都带 `assert count == 1`，所以本机文件若与预期不符会当场停住，不会改坏）。
重新生成用 `python3 mk3.py`，再 `PYTHONPATH=. python3` 一份把输出路径换成 `blueprint.html`
的 `page.py` 副本——`page.py` 里的输出路径写死在云端容器那侧。

`graphs.py` 与 `__pycache__/` 是生成物，已进 `.gitignore`。
