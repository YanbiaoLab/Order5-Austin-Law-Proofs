# Equation12857

- 对偶：[Equation33436](../Equation33436/README.md)
- 原表：20.2
- 方程：`x = y ◇ ((x ◇ (y ◇ (z ◇ z))) ◇ y)`
- 有限侧数学状态：已证仅平凡（Lean）
- 无限侧：**Lean 4.33.1 编译通过，含 Nat 单射证明。**

直接使用已证明的 E12857 运算。

[InfiniteModel.lean](InfiniteModel.lean) 证明本目录 [JudgeProblem.lean](JudgeProblem.lean) 的精确 `Goal`。
`submission.CM.tower_injective` 证明载体无限；完整构造见[共享 Lean 模块](../Equation12857/Lean/README.md)。

最终依赖仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorryAx` 或自定义公理。
这是本仓独立新增证明；历史 `timeout` 记录保留，本次没有重新调用官方 Judge。

从项目根目录运行 `python3 scripts/check_12857_lean.py` 可串行重建并检查全部依赖。
源码哈希、完整命令、编译日志及资源使用见[形式化报告](../validation/eq12857-formal/README.md)。

<!-- aurora-accepted -->

随后已通过极光云 **judge-v3-repl** 实际验证，结果为 **accepted**。任务 ID：`f343d53fdad6449cb0162cbcdb71a8dc`。见[完整结果](../validation/aurora/Equation12857/attempt02/latest.json)和[实际提交的单文件证书](../validation/aurora/Equation12857/attempt02/certificate.lean)。原来的本地编译记录和历史验收状态保留。
