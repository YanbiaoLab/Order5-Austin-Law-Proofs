# Equation5833

- 对偶：[Equation40070](../Equation40070/README.md)
- 原表：20.2
- 方程：`x = y ◇ (x ◇ (y ◇ ((z ◇ x) ◇ y)))`
- 无限侧：本地 Lean 4.33.1 检查通过，含自然数单射；远程结果单独记录。
- 有限侧：已证仅平凡（Lean）；已归档 [FiniteTrivial.lean](FiniteTrivial.lean)。

[InfiniteModel.lean](InfiniteModel.lean) 证明本目录精确的 [Goal](JudgeProblem.lean)。
共享的[模型定义及无限性证明](../Equation5833/Lean/Model.lean)使用互归纳定义的 Step/Code 关系构造。
Equation40070 使用相同载体上的反向乘法。`submission.CM.tower_injective` 是显式无限性证书。

没有 `sorry` 或自定义公理；最终定理仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。
详见[构造笔记](../../docs/Trace-tree-models.md)及[编译报告](../validation/eq5833-formal/README.md)。

复跑：在仓库根目录运行 `python3 scripts/trace_models.py check 5833`。
历史 timeout 记录保留；每次本地、远程验证各有源码哈希和日志。

<!-- aurora-accepted -->

随后已通过极光云 **judge-v3-repl** 实际验证，结果为 **accepted**。任务 ID：`bbf2a747c9c743278bc05c65fe609009`。见[完整结果](../validation/aurora/Equation5833/latest.json)和[实际提交的单文件证书](../validation/aurora/Equation5833/certificate.lean)。原来的本地编译记录和历史验收状态保留。
