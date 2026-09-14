# Equation28626

- 对偶：[Equation17286](../Equation17286/README.md)
- 原表：20.3
- 方程：`x = (((y ◇ x) ◇ y) ◇ y) ◇ (x ◇ z)`
- 有限侧数学状态：已证所有有限模型平凡（Lean 4.33.1）

有限侧 Lean：[FiniteTrivial.lean](FiniteTrivial.lean)，完整定理 `finite_trivial_dual` 在 `[Finite G]` 下证明源方程推出 `Equation2 G`。独立证书包含对偶转移所需的证明（如适用）。

原本机 Lean 4.33.1 验证已通过；[运行记录](../../proofs/validation/finite130/column-incidence/Equation28626.json)和[公理日志](../../proofs/validation/finite130/column-incidence/Equation28626.log)绑定原证书哈希。本次只核对保存的证据，未重新编译或提交云端。

2026-09-14：非平凡无限模型已完成，现已确认为 Austin 律。[InfiniteModel.lean](InfiniteModel.lean) 包含 E17286 的完整有限树构造及反向乘法转移，独立证明本题精确原式、非平凡性和自然数单射。两条方程共八个编译单元通过空目录 Lean 4.33.1 核验；随后独立证书经远端 Judge 返回 **ACCEPTED**，见[远端验收记录](../validation/eq17286-formal/JUDGE.md)。详见[模型与复盘](../Equation17286/MODEL.zh-CN.md)及[核验报告](../validation/eq17286-formal/README.md)。

详见[本批归档报告](../../proofs/validation/2026-09-11-latest-proofs/README.md)、[总索引](../index.json)。历史 timeout 仅记录历史搜索结果。
