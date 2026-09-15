# Equation22591

- 对偶：[Equation22446](../Equation22446/README.md)
- 原表：20.3
- 方程：`x = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ z)`
- 有限侧数学状态：已证所有有限模型平凡（Lean 4.33.1）

有限侧 Lean：[FiniteTrivial.lean](FiniteTrivial.lean)，完整定理 `finite_trivial_dual` 在 `[Finite G]` 下证明源方程推出 `Equation2 G`。独立证书包含对偶转移所需的证明（如适用）。

原本机 Lean 4.33.1 验证已通过；[运行记录](../../proofs/validation/finite130/finite-incidence/Equation22591.json)和[公理日志](../../proofs/validation/finite130/finite-incidence/Equation22591.log)绑定原证书哈希。本次有限侧只核对保存的证据，未重新编译或提交云端。

**2026-09-15：非平凡无限模型及独立 Lean 证书完成，远端 Judge 首次提交返回 ACCEPTED。** 结合已有有限平凡性证明，E22591 的 Austin 律性质已获形式化证明。

- [模块化模型](InfiniteModel.lean)：反向乘法、精确原式、非平凡性与显式 Nat 单射。
- [本题目标](JudgeProblem.lean)与[完整单文件证书](JudgeSubmission.lean)。
- [对偶构造说明](MODEL.zh-CN.md)：E22446 定理取参数 `x, z, y`。
- [本机核验及只读审计](../validation/eq22591-formal/README.md)：58 个模型模块与 56 个导出分段，共 114 次空目录串行编译。
- [远端验收](../validation/aurora/Equation22591/README.md)：任务 `910bd0a8ccad40e69c784c03968a3714`，17.436 秒，缓存关闭。

同一载体上的原式、非平凡性和自然数单射均经 Lean 4.33.1 检查。单射端点无公理，其余最终端点只使用 `propext`、`Classical.choice`、`Quot.sound`。

详见[本批归档报告](../../proofs/validation/2026-09-11-latest-proofs/README.md)、[总索引](../index.json)。历史 timeout 仅记录历史搜索结果。
