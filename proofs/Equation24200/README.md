# Equation24200

- 对偶：[Equation21714](../Equation21714/README.md)
- 原表：20.3
- 方程：`x = ((y ◇ x) ◇ x) ◇ ((x ◇ z) ◇ z)`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean) 在 `[Finite G]` 下推出 Equation2，已通过 Lean 4.33.1 本地编译与公理检查。

无限侧 Lean：已收录非平凡无限模型；精确原式和显式 Nat 单射已有 Lean 4.33.1 验证记录，历史超时状态保留。

有限侧平凡性与非平凡无限模型两方面证书齐全，确认为 Austin 律；原表分类保留。

来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。本条有限侧已有可重新编译的 Lean 证书。

有限侧极光云验收尚未完成：当前服务缺少有限目标接口，见[本批报告](../validation/finite130/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation24200.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。

## 2026-09-11 无限模型归档

[InfiniteModel.lean](InfiniteModel.lean) 证明本题精确 [Goal](JudgeProblem.lean)，并导出 `submission.CM.tower_injective`。与既有 [FiniteTrivial.lean](FiniteTrivial.lean) 共同确立本条为 Austin 律。

见[原验证记录](../validation/eq21866-formal/README.md)与[本批归档审计](../validation/2026-09-11-ten-austin/README.md)。另有云端 judge-v3-repl [accepted 回执](../validation/aurora/Equation24200/latest.json)。 本次归档核对原证书和验证记录，未重新运行 Lean/Judge。
