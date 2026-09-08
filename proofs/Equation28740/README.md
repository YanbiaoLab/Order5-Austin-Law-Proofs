# Equation28740

- 对偶：[Equation17260](../Equation17260/README.md)
- 原表：20.3
- 方程：`x = (((y ◇ y) ◇ x) ◇ y) ◇ (x ◇ z)`
- 有限侧数学状态：未知

有限侧 Lean：未收录。预留文件名 `FiniteTrivial.lean`，仅在有完整证明时创建。

非平凡模型：[InfiniteModel.lean](InfiniteModel.lean)，原样归档，SHA-256 与历史 accepted 记录一致。目标定义在 [JudgeProblem.lean](JudgeProblem.lean)，共享依赖在 [support](../support/)。

显式无限性：证书包含 `submission.CM.tower_injective`，给出 `Nat` 到模型载体的单射。

非平凡有限模型的存在性仍未知；无限侧通过验收不能单独确认为 Austin 律。

来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。本条已归档证明均已在 Lean 4.33.1 编译通过；详见[重新编译报告](../validation/2026-09-08/README.md)。
