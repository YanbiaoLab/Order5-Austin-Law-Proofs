# Equation9680

- 对偶：[Equation36524](../Equation36524/README.md)
- 原表：20.2
- 方程：`x = y ◇ ((z ◇ y) ◇ (y ◇ (x ◇ y)))`
- 有限侧数学状态：仅平凡（Blueprint）

有限侧 Lean：未收录。预留文件名 `FiniteTrivial.lean`，仅在有完整证明时创建。

无限侧 Lean：已补入论文原有的历史 Judge v3 `accepted / false` 证书，精确目标为 `Equation9680 ↛ Equation2`。

- [`InfiniteModel.lean`](InfiniteModel.lean)：原证书逐字节副本，仅改文件名。
- [`JudgeProblem.lean`](JudgeProblem.lean)：按冻结题目重建，**非历史 Judge 原始模块**。
- [`problem.json`](problem.json)：冻结输入记录。
- [`judge_acceptance.json`](judge_acceptance.json)：脱敏历史验收摘录。

证书长度、SHA-256 和发布包规范化题目哈希已核对。此题是论文原有结果，不算新发现。本次无新的 Lean/Judge 执行或独立无限性定理核验；精确验收目标直接证明非平凡性。

请在匹配的 Lean/Mathlib 与 `JudgeMagma.Magma` 环境中逐题隔离编译，避免混用不同题目的 `Goal`／`submission`。

参见 [index.json](../index.json)、[归档说明](../README.md) 和 [补录审计](../validation/2026-09-09-trace-tree-pair/README.md)。


本批 Aurora-56 补充：[另存的已验证证书](../validation/aurora/Equation9680/certificate.lean) 与[实际 accepted 回执](../validation/aurora/Equation9680/latest.json)。目标为本题源等式成立且模型非平凡；`submission.CM.tower_injective` 给出显式无限性。任务 ID：`ffb84e7cf57341cc949fd85f8440e636`。本次归档核对已有验收记录，未重跑 Lean/Judge；见[批次报告](../validation/2026-09-09-aurora56/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation9680.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。
