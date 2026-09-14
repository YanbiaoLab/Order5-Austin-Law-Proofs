# Equation18137

- 对偶：[Equation27863](../Equation27863/README.md)
- 原表：20.2
- 方程：`x = (y ◇ x) ◇ (z ◇ ((x ◇ z) ◇ z))`
- 有限侧数学状态：已证仅平凡（Lean）

对偶 Equation27863 也已通过反转运算完成独立 Lean 证书及远端 Judge 验收，
见[对偶核验记录](../validation/eq27863-formal/README.md)。

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean) 在 `[Finite G]` 下推出 Equation2，已通过 Lean 4.33.1 本地编译与公理检查。

无限侧：**已构造非平凡无限模型（2026-09-14，本地 Lean 4.33.1 核验通过）**。
载体为自然数标号的所有有限二叉树，运算使用唯一关系解码，包含显式自然数单射。
见[模型解释](MODEL.zh-CN.md)、[独立证书](InfiniteModel.lean)及
[完整验证记录](../validation/eq18137-formal/README.md)。历史超时状态保留为历史记录。

来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。
无限侧证书已本地重新编译，并通过远端 Judge **ACCEPTED**：
任务 `25f7dd0341414b5c83e91957ee920fba`，见[原始回执](../validation/aurora/Equation18137/latest.json)。

有限侧极光云验收尚未完成：当前服务缺少有限目标接口，见[本批报告](../validation/finite130/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation18137.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。

## 无限模型的证明文件

[TreeSchema.lean](TreeSchema.lean) 定义载体、列关系与解码关系；
[TreeBounds.lean](TreeBounds.lean) 证明大小和秩约束；
[TreeUnique.lean](TreeUnique.lean) 证明解码唯一性；
[TreeModel.lean](TreeModel.lean) 定义总运算并证明完整原式、非平凡性及无限性。
[InfiniteModel.lean](InfiniteModel.lean) 将四模块展平，包含远端所需的精确目标定理。
构造思路、成功原因和证明细节见 [MODEL.zh-CN.md](MODEL.zh-CN.md)。

从仓库根目录运行：

```sh
python3 proofs/validation/eq18137-formal/verify.py
python3 proofs/validation/eq18137-formal/audit_remote.py
```
