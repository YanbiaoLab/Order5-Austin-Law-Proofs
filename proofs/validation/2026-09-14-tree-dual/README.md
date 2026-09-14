# Equation18137 / Equation27863：无限树模型归档

2026-09-14，两条方程均补齐非平凡无限模型，与已有的有限平凡性证书组成两条完整 Austin 律。

| 方程 | 新增模型证书 | 本地编译单元 | Judge 任务 | 结果 |
|---|---|---:|---|---|
| Equation18137 | [InfiniteModel.lean](../../Equation18137/InfiniteModel.lean) | 6 / 6 | `25f7dd0341414b5c83e91957ee920fba` | ACCEPTED |
| Equation27863 | [InfiniteModel.lean](../../Equation27863/InfiniteModel.lean) | 7 / 7 | `c57824e679ec4461b923a5237bdfcd56` | ACCEPTED |

Equation18137 的载体为自然数标号的全部有限二叉树，运算由唯一关系解码定义。
Equation27863 复用此载体并反转运算；其独立提交文件包含完整原构造与精确对偶转移证明。
构造细节见[模型说明](../../Equation18137/MODEL.zh-CN.md)和[对偶证明](../../Equation27863/DualModel.lean)。

两份证书都证明原恒等式、非平凡性及 `Nat` 到载体的单射。
Judge 的目标直接要求非平凡模型；显式无限性定理另经本地 Lean 核验。
最终模型定理只使用 `propext`、`Classical.choice`、`Quot.sound`，原子单射不依赖公理。
本批未改动已有有限平凡性证书，也未重新提交有限侧目标。

## 从检出源码复现

只需 Python 标准库及已安装的 `leanprover/lean4:v4.33.1`，不需要 Mathlib 或搜索工具。
所有脚本从任意工作目录均可定位仓库；以下命令以仓库根目录为起点。

先只读核对现存归档、全部索引文件哈希、本批回执和中英文 README：

```sh
python3 proofs/validation/2026-09-14-tree-dual/verify.py
```

按顺序重新编译两份模型：

```sh
python3 proofs/validation/eq18137-formal/verify.py
python3 proofs/validation/eq27863-formal/verify.py
```

每题建立两个空临时目录，分别检查模块化证明与独立展平证书，结束后删除编译产物。
每次只运行一个 Lean 进程：内部内存上限 192 MiB，外部进程树 RSS 上限 256 MiB，
单元时间上限 20 秒，每 0.05 秒采样；超限会终止该进程组。

重编译会刷新各题 `summary.json` 和日志，包括运行时间与临时目录路径。
如需将新运行记录写回索引，再依次运行：

```sh
python3 proofs/validation/eq18137-formal/record_index.py
python3 proofs/validation/eq27863-formal/record_index.py
python3 proofs/validation/2026-09-14-tree-dual/verify.py
```

上述命令均不调用网络。实际提交证书、请求及原始回执分别保存在
[Equation18137 远端归档](../aurora/Equation18137/README.md)和
[Equation27863 远端归档](../aurora/Equation27863/README.md)。
发布整理只调整复核脚本与说明，两份已验收证书保持逐字节一致，无需重复提交 Judge。

## 库存变化

| 项目 | 上一批之后 | 本批之后 |
|---|---:|---:|
| 有限平凡性证书 | 120 | 120 |
| 非平凡模型证书 | 114 | 116 |
| 显式无限性证明 | 86 | 88 |
| 两侧证书齐全 | 106 | 108 |
| 所有模型平凡，已排除 | 2 | 2 |
| 有限侧待解 | 10 | 10 |
| 无限侧待解 | 14 | 12 |

原表 20.2 现在有 90 条模型证书、2 条排除、4 条待解；原表分类保持不变。
全量状态见[索引](../../index.json)、[英文 README](../../../README.md)和[中文 README](../../../README.zh-CN.md)。
