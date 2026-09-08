# Equation12073

- 对偶：[Equation33998](../Equation33998/README.md)
- 原表：20.2
- 方程：`x = y ◇ (((y ◇ x) ◇ x) ◇ (z ◇ z))`
- 无限侧：本地 Lean 4.33.1 检查通过，含自然数单射；远程结果单独记录。
- 有限侧：已证仅平凡（Lean）；已归档 [FiniteTrivial.lean](FiniteTrivial.lean)。

[InfiniteModel.lean](InfiniteModel.lean) 证明本目录精确的 [Goal](JudgeProblem.lean)。
共享的[模型定义及无限性证明](../Equation12073/Lean/Model.lean)由 22 条终止、汇合的重写规则构造。
Equation33998 使用相同载体上的反向乘法。`submission.CM.tower_injective` 是显式无限性证书。

没有 `sorry` 或自定义公理；最终定理仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。
详见[构造笔记](../../docs/Equation12073-model.md)及[编译报告](../validation/eq12073-formal/README.md)。

复跑：在仓库根目录运行 `python3 scripts/check_12073_lean.py`。
历史 timeout 记录保留；每次本地、远程验证各有源码哈希和日志。

<!-- aurora-accepted -->

随后已通过极光云 **judge-v3-repl** 实际验证，结果为 **accepted**。任务 ID：`5745f8cde49a4647b810ce183d6f5d91`。见[完整结果](../validation/aurora/Equation12073/latest.json)和[实际提交的单文件证书](../validation/aurora/Equation12073/certificate.lean)。原来的本地编译记录和历史验收状态保留。
