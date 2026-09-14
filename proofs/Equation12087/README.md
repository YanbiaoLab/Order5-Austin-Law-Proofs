# Equation12087

- 对偶：[Equation33884](../Equation33884/README.md)
- 原表：20.2
- 方程：`x = y ◇ (((y ◇ x) ◇ z) ◇ (x ◇ z))`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean) 在 `[Finite G]` 下推出 Equation2，已通过 Lean 4.33.1 本地编译与公理检查。

无限侧：**2026-09-14 已完成非平凡无限正规树模型**。[InfiniteModel.lean](InfiniteModel.lean) 证明精确目标，[模型说明与复盘](MODEL.zh-CN.md) 给出载体、总运算、完整原式和显式自然数单射。125 个核心模块与两条方程包装共 129 次空目录串行构建通过 Lean 4.33.1；见[核验报告](../validation/eq12087-formal/README.md)。独立[单文件证书](JudgeSubmission.lean)现已获远端 Judge **ACCEPTED**；见[实际回执](../validation/aurora/Equation12087/latest.json)与[完整提交记录](../validation/eq12087-formal/JUDGE.md)。



来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。模型依赖完整收录于 [Lean](Lean/TraceFullSource.lean)，最终原式定理不含待证明假设。早期超时与未完成记录保留为历史。

有限侧极光云验收尚未完成：当前服务缺少有限目标接口，见[本批报告](../validation/finite130/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation12087.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。
