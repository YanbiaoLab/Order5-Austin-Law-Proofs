# Equation35836

- 对偶：[Equation10222](../Equation10222/README.md)
- 原表：20.2
- 方程：`x = ((y ◇ (y ◇ z)) ◇ (y ◇ x)) ◇ y`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean) 在 `[Finite G]` 下推出 Equation2，已通过 Lean 4.33.1 本地编译与公理检查。

无限侧 Lean：已收录非平凡无限模型；精确原式和显式 Nat 单射已有 Lean 4.33.1 验证记录，历史超时状态保留。

来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。本条有限侧与无限侧均已有 Lean 证书和验证记录。

有限侧极光云验收尚未完成：当前服务缺少有限目标接口，见[本批报告](../validation/finite130/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation35836.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。

## 2026-09-11 无限模型归档

[InfiniteModel.lean](InfiniteModel.lean) 证明本题精确 [Goal](JudgeProblem.lean)，并导出 `submission.CM.tower_injective`。与既有 [FiniteTrivial.lean](FiniteTrivial.lean) 共同确立本条为 Austin 律。

见[原验证记录](../validation/eq10222-formal/README.md)与[本批归档审计](../validation/2026-09-11-ten-austin/README.md)。这两条的本批无限模型证明只作过本地验证，未提交云端。 本次归档核对原证书和验证记录，未重新运行 Lean/Judge。
