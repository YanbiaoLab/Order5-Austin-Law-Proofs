# Equation22591

- 对偶：[Equation22446](../Equation22446/README.md)
- 原表：20.3
- 方程：`x = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ z)`
- 有限侧数学状态：已证所有有限模型平凡（Lean 4.33.1）

有限侧 Lean：[FiniteTrivial.lean](FiniteTrivial.lean)，完整定理 `finite_trivial_dual` 在 `[Finite G]` 下证明源方程推出 `Equation2 G`。独立证书包含对偶转移所需的证明（如适用）。

原本机 Lean 4.33.1 验证已通过；[运行记录](../../proofs/validation/finite130/finite-incidence/Equation22591.json)和[公理日志](../../proofs/validation/finite130/finite-incidence/Equation22591.log)绑定原证书哈希。本次只核对保存的证据，未重新编译或提交云端。

无限侧仍待解，尚无非平凡无限模型证书，因此尚未确认为 Austin 律。单元素平凡模型存在。

详见[本批归档报告](../../proofs/validation/2026-09-11-latest-proofs/README.md)、[总索引](../index.json)。历史 timeout 仅记录历史搜索结果。
