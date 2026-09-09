# Equation32281

- 对偶：[Equation13849](../Equation13849/README.md)
- 原表：20.2
- 方程：`x = (y ◇ ((y ◇ (y ◇ x)) ◇ z)) ◇ z`
- 有限侧数学状态：仅平凡（Blueprint）

有限侧 Lean：未收录。预留文件名 `FiniteTrivial.lean`，仅在有完整证明时创建。

无限侧 Lean：已收录历史 Judge v3 `accepted / ACCEPTED / false` 证书，精确命题为 `Equation32281 ↛ Equation2`。

- [`InfiniteModel.lean`](InfiniteModel.lean)：原 `Submission.lean` 仅改文件名，字节内容不变。
- [`JudgeProblem.lean`](JudgeProblem.lean)：原始命题定义。
- [`judge_acceptance.json`](judge_acceptance.json)：脱敏历史验收记录，非本次新提交结果。
- [`problem.json`](problem.json)：原题目及编号。

本次已核对证书哈希、等式编号和命题绑定；未重新运行 Lean/Judge，故不标记为“本仓重新编译通过”。该 Judge 目标直接证明非平凡模型存在；本次不额外声称已核验独立的无限性定理。

请在证书及其 `JudgeProblem.lean` 所在目录隔离编译；不同题目共用 `Goal`／`submission` 名称，不能合并导入。依赖须使用匹配的 Lean／Mathlib 与 `JudgeMagma.Magma`。

来源与验证状态见 [index.json](../index.json)、[归档说明](../README.md) 和 [增补记录](../validation/2026-09-09-austin24/README.md)。


本批 Aurora-56 补充：[另存的已验证证书](../validation/aurora/Equation32281/certificate.lean) 与[实际 accepted 回执](../validation/aurora/Equation32281/latest.json)。目标为本题源等式成立且模型非平凡；`submission.CM.tower_injective` 给出显式无限性。任务 ID：`e725b72b99d94e498b5c4b311f2ad6e6`。本次归档核对已有验收记录，未重跑 Lean/Judge；见[批次报告](../validation/2026-09-09-aurora56/README.md)。
