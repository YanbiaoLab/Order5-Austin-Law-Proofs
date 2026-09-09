# Equation12857

- 对偶：[Equation33436](../Equation33436/README.md)
- 原表：20.2
- 方程：`x = y ◇ ((x ◇ (y ◇ (z ◇ z))) ◇ y)`
- 有限侧数学状态：仅平凡（Blueprint）

有限侧 Lean：未收录。预留文件名 `FiniteTrivial.lean`，仅在有完整证明时创建。

无限侧 Lean：已收录历史 Judge v3 `accepted / ACCEPTED / false` 证书，精确命题为 `Equation12857 ↛ Equation2`。

原有 [`InfiniteModel.lean`](InfiniteModel.lean) 及配套模块保持不变。本次补充以下独立证书：

- [`InfiniteModel.lean`](JudgeV3/InfiniteModel.lean)：原 `Submission.lean` 仅改文件名，字节内容不变。
- [`JudgeProblem.lean`](JudgeV3/JudgeProblem.lean)：原始命题定义。
- [`judge_acceptance.json`](JudgeV3/judge_acceptance.json)：脱敏历史验收记录，非本次新提交结果。
- [`problem.json`](JudgeV3/problem.json)：原题目及编号。

本次已核对证书哈希、等式编号和命题绑定；未重新运行 Lean/Judge，故不标记为“本仓重新编译通过”。该 Judge 目标直接证明非平凡模型存在；本次不额外声称已核验独立的无限性定理。

请在证书及其 `JudgeProblem.lean` 所在目录隔离编译；不同题目共用 `Goal`／`submission` 名称，不能合并导入。依赖须使用匹配的 Lean／Mathlib 与 `JudgeMagma.Magma`。

来源与验证状态见 [index.json](../index.json)、[归档说明](../README.md) 和 [增补记录](../validation/2026-09-09-austin24/README.md)。


本批 Aurora-56 补充：[另存的已验证证书](../validation/aurora/Equation12857/attempt02/certificate.lean) 与[实际 accepted 回执](../validation/aurora/Equation12857/attempt02/latest.json)。目标为本题源等式成立且模型非平凡；`submission.CM.tower_injective` 给出显式无限性。任务 ID：`f343d53fdad6449cb0162cbcdb71a8dc`。本次归档核对已有验收记录，未重跑 Lean/Judge；见[批次报告](../validation/2026-09-09-aurora56/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation12857.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。
