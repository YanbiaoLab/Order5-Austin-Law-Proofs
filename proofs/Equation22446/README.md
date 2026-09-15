# Equation22446

- 对偶：[Equation22591](../Equation22591/README.md)
- 原表：20.3
- 方程：`x = (y ◇ (x ◇ x)) ◇ ((x ◇ z) ◇ z)`
- 有限侧数学状态：已证所有有限模型平凡（Lean 4.33.1）

有限侧 Lean：[FiniteTrivial.lean](FiniteTrivial.lean)，完整定理 `Equation22446Finite.finite_trivial` 在 `[Finite G]` 下证明源方程推出 `Equation2 G`。独立证书包含对偶转移所需的证明（如适用）。

原本机 Lean 4.33.1 验证已通过；[运行记录](../../proofs/validation/finite130/finite-incidence/Equation22446.json)和[公理日志](../../proofs/validation/finite130/finite-incidence/Equation22446.log)绑定原证书哈希。本次只核对保存的证据，未重新编译或提交云端。

**2026-09-15：非平凡无限模型已完成，并获远端 Judge ACCEPTED。** 结合已有有限平凡性证明，E22446 的 Austin 律性质已获形式化证明。

- [模块化模型](InfiniteModel.lean)：精确原式、非平凡性和显式 Nat 单射。
- [完整单文件证书](JudgeSubmission.lean)：远端实际提交版本。
- [模型构造与证明](MODEL.zh-CN.md)。
- [本机核验及只读审计](../validation/eq22446-infinite-model/README.md)。
- [远端验收](../validation/aurora/Equation22446/README.md)：任务 `a10791d664bd43df97dad1531bb1acfa`，17.413 秒，缓存关闭。

本机 58 个模块从空目录重建通过，291 条公理报告覆盖 290 个不同声明；原式、非平凡性和自然数单射均使用同一载体。所有唯一性和覆盖前提已经关闭。有限侧本次仅核对已有证书，不重新编译 Mathlib 或提交远端任务。

首次远端提交因注释单词 `syntax` 被词法预检误判而退回；移除注释、保持数学证明代码不变并重新分段核验后通过。两次回执和实际证书均保留。对偶 E22591 的独立证书尚待另行归档。

详见[本批归档报告](../../proofs/validation/2026-09-11-latest-proofs/README.md)、[总索引](../index.json)。历史 timeout 仅记录历史搜索结果。
