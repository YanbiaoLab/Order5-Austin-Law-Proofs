# Equation41239

- 对偶：[Equation5066](../Equation5066/README.md)
- 原表：20.2
- 方程：`x = ((((y ◇ z) ◇ y) ◇ x) ◇ y) ◇ y`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean) 在 `[Finite G]` 下推出 Equation2，已通过 Lean 4.33.1 本地编译与公理检查。

非平凡模型：[InfiniteModel.lean](InfiniteModel.lean)，原样归档，SHA-256 与历史 accepted 记录一致。目标定义在 [JudgeProblem.lean](JudgeProblem.lean)，共享依赖在 [support](../support/)。

显式无限性：证书使用含 `e/k/p` 构造子的无限归纳树载体，但尚未单列 `Nat` 单射或 `Infinite` 定理。历史 Judge 验收目标仅要求非平凡模型。



来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。本条已归档证明均已在 Lean 4.33.1 编译通过；详见[重新编译报告](../validation/2026-09-08/README.md)。

有限侧极光云验收尚未完成：当前服务缺少有限目标接口，见[本批报告](../validation/finite130/README.md)。
