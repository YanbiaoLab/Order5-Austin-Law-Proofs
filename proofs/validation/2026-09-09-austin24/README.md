# 24 份 Austin 候选历史 Judge v3 证书增补

按仓库原结构收录，不上传独立 ZIP。每题精确目标为 `EquationN ↛ Equation2`，历史状态为 `accepted / ACCEPTED / false`。

- 22 个缺少 Lean 文件的目录：补入 `InfiniteModel.lean`、原始 `JudgeProblem.lean`、`problem.json`、脱敏 `judge_acceptance.json`。
- Equation12857／Equation33436 原文件不变；新四文件放入 `JudgeV3/`，避免替换原模块或混用 `Goal`。
- 证书只从 `Submission.lean` 改名，内容与历史接受哈希一致。96 个文件均核对 SHA-256。
- 8 份早期回执不含题目正文（12857、13764、13849、13992、32280、32281、32294、33436），保留 `receipt_contains_problem_text: false`。绑定审计使用原始命题、题目与冻结候选表，不把正文说成回执内字段。
- 本次不重跑 Lean/Judge，不声称所有证书都含独立核验的无限性定理。精确验收目标直接证明非平凡性。
- 24 个编号是原论文库存的后续批次，不构成全球首次发现声明。

完整路径、题目与哈希见 [manifest.json](manifest.json)。[verify.ps1](verify.ps1) 只读核对文件、历史状态及编号；Lean 编译仍须匹配依赖，并按对应 `JudgeProblem` 隔离。

| 等式 | 证书 | 放置方式 |
|---|---|---|
| Equation5833 | [InfiniteModel.lean](../../Equation5833/InfiniteModel.lean) | 填补缺失 |
| Equation6878 | [InfiniteModel.lean](../../Equation6878/InfiniteModel.lean) | 填补缺失 |
| Equation7763 | [InfiniteModel.lean](../../Equation7763/InfiniteModel.lean) | 填补缺失 |
| Equation9603 | [InfiniteModel.lean](../../Equation9603/InfiniteModel.lean) | 填补缺失 |
| Equation11205 | [InfiniteModel.lean](../../Equation11205/InfiniteModel.lean) | 填补缺失 |
| Equation11280 | [InfiniteModel.lean](../../Equation11280/InfiniteModel.lean) | 填补缺失 |
| Equation12073 | [InfiniteModel.lean](../../Equation12073/InfiniteModel.lean) | 填补缺失 |
| Equation12857 | [InfiniteModel.lean](../../Equation12857/JudgeV3/InfiniteModel.lean) | 追加，原证明保留 |
| Equation13764 | [InfiniteModel.lean](../../Equation13764/InfiniteModel.lean) | 填补缺失 |
| Equation13849 | [InfiniteModel.lean](../../Equation13849/InfiniteModel.lean) | 填补缺失 |
| Equation13992 | [InfiniteModel.lean](../../Equation13992/InfiniteModel.lean) | 填补缺失 |
| Equation18212 | [InfiniteModel.lean](../../Equation18212/InfiniteModel.lean) | 填补缺失 |
| Equation27859 | [InfiniteModel.lean](../../Equation27859/InfiniteModel.lean) | 填补缺失 |
| Equation32280 | [InfiniteModel.lean](../../Equation32280/InfiniteModel.lean) | 填补缺失 |
| Equation32281 | [InfiniteModel.lean](../../Equation32281/InfiniteModel.lean) | 填补缺失 |
| Equation32294 | [InfiniteModel.lean](../../Equation32294/InfiniteModel.lean) | 填补缺失 |
| Equation33436 | [InfiniteModel.lean](../../Equation33436/JudgeV3/InfiniteModel.lean) | 追加，原证明保留 |
| Equation33998 | [InfiniteModel.lean](../../Equation33998/InfiniteModel.lean) | 填补缺失 |
| Equation34778 | [InfiniteModel.lean](../../Equation34778/InfiniteModel.lean) | 填补缺失 |
| Equation35100 | [InfiniteModel.lean](../../Equation35100/InfiniteModel.lean) | 填补缺失 |
| Equation36514 | [InfiniteModel.lean](../../Equation36514/InfiniteModel.lean) | 填补缺失 |
| Equation38565 | [InfiniteModel.lean](../../Equation38565/InfiniteModel.lean) | 填补缺失 |
| Equation39126 | [InfiniteModel.lean](../../Equation39126/InfiniteModel.lean) | 填补缺失 |
| Equation40070 | [InfiniteModel.lean](../../Equation40070/InfiniteModel.lean) | 填补缺失 |
