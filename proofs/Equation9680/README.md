# Equation9680

- 对偶：[Equation36524](../Equation36524/README.md)
- 原表：20.2
- 方程：`x = y ◇ ((z ◇ y) ◇ (y ◇ (x ◇ y)))`
- 无限侧：本地 Lean 4.33.1 检查通过，含自然数单射；远程结果单独记录。
- 有限侧：已证仅平凡（Lean）；已归档 [FiniteTrivial.lean](FiniteTrivial.lean)。

[InfiniteModel.lean](InfiniteModel.lean) 证明本目录精确的 [Goal](JudgeProblem.lean)。
共享的[模型定义及无限性证明](../Equation9680/Lean/Model.lean)使用互归纳定义的 Step/Code 关系构造。
Equation36524 使用相同载体上的反向乘法。`submission.CM.tower_injective` 是显式无限性证书。

没有 `sorry` 或自定义公理；最终定理仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。
详见[构造笔记](../../docs/Trace-tree-models.md)及[编译报告](../validation/eq9680-formal/README.md)。

复跑：在仓库根目录运行 `python3 scripts/trace_models.py check 9680`。
历史 timeout 记录保留；每次本地、远程验证各有源码哈希和日志。

<!-- aurora-accepted -->

随后已通过极光云 **judge-v3-repl** 实际验证，结果为 **accepted**。任务 ID：`ffb84e7cf57341cc949fd85f8440e636`。见[完整结果](../validation/aurora/Equation9680/latest.json)和[实际提交的单文件证书](../validation/aurora/Equation9680/certificate.lean)。原来的本地编译记录和历史验收状态保留。
