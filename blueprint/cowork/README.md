# Cowork 侧的蓝图生成脚本

蓝图页面（Artifact）由 Cowork 每 10 分钟心跳时重建并 republish 到同一个 URL。
脚本放在这里是为了在云端容器被清空后还能取回。

* `gen.py` —— 分层 DAG → SVG。节点给定所在行，行内自动均分 x。
  `KIND` 决定配色：`def` 定义 / `draft` 已写未编译 / `ready` 可开工 / `todo` 待解锁 /
  `axiom` 接口公理 / `star` 高价值节点。`band=<行号>` 画出接口公理分界带。
* `mk2.py` —— 四章的节点与边，产出 `graphs.py`。
* `page.py` —— 读 `graphs.py`，拼出整页 HTML 到 `blueprint.html`。

用法（在云端容器里）：

```bash
mkdir -p /home/claude/bp && cd /home/claude/bp
# 从这里取回 gen.py mk2.py page.py
python3 mk2.py && python3 page.py
# 然后 Artifact 工具 file_path=/home/claude/bp/blueprint.html republish
```

**这不是 `leanblueprint` 的产物。** 正式的 leanblueprint 站点走 `blueprint/src/` +
`blueprint.yml`，见 `docs/TASKS.md` 的 T12；这一份是给 Jun 在会话里跟进度用的活页。
两者的节点名保持一致（都对着论文的 label）。
