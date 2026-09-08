# Equation28770

- 对偶：[Equation17522](../Equation17522/README.md)
- 原表：20.1
- 方程：`x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean)，在 `[Finite G]` 下推出 Equation2。保留上游定理正文，调整为最小依赖；已在本仓 Lean 4.33.1 编译通过。

非平凡模型：[InfiniteModel.lean](InfiniteModel.lean)，原样归档，SHA-256 与历史 accepted 记录一致。目标定义在 [JudgeProblem.lean](JudgeProblem.lean)，共享依赖在 [support](../support/)。

显式无限性：证书包含 `submission.CM.tower_injective`，给出 `Nat` 到模型载体的单射。



来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。本条已归档证明均已在 Lean 4.33.1 编译通过；详见[重新编译报告](../validation/2026-09-08/README.md)。
