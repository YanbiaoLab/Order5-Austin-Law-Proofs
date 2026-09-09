# 两个 Austin-96 候选的 true 证书：先 Judge，后归档

本批上传的两份 Lean 证书均在 2026-09-09 独立提交精确题目，取得 **Judge v3 accepted / ACCEPTED / true** 后才归档。并非将 Twee 的 `Theorem` 状态当作 Lean 验收。

| 精确命题 | Lean 证书 | 字节数 | Judge 回执 |
|---|---|---:|---|
| Equation5834 → Equation2 | [Triviality.lean](../../Equation5834/Triviality.lean) | 671407 | [accepted / true](../../Equation5834/judge_acceptance.json) |
| Equation40037 → Equation2 | [Triviality.lean](../../Equation40037/Triviality.lean) | 671279 | [accepted / true](../../Equation40037/judge_acceptance.json) |

两份证明的公理依赖均为空，未使用 `grind`、`sorry` 或额外公理。上传的是 Judge 接受的原始证书字节，仅将文件命名为 `Triviality.lean`。

## 数学结论与库存

目标是 `∀ (G : Type) [Magma G], EquationN G → Equation2 G`，**没有 `[Finite G]` 假设**。Equation2 是 `∀ x y, x = y`，所以所有源模型都平凡。这排除非平凡无限模型，因此两题不是 Austin law；不能把 true 证明记入无限模型证书列。

原 Blueprint 表 20.2 分类保持不变。Candidate-96 现有 56 个非平凡模型证书编号、2 个由本批排除的编号、38 个尚未被这些归档结果分类的编号。后者不构成全球未知声明。历史 timeout 保留为历史字段。

## 证明来源

原论文冻结实验：`same_resource_atp_baselines_20260904`，输入 `inputs/austin96.jsonl`，Twee 2.6.1 完整输出存于 `results/atp/twee_complete/status_evidence_streams.jsonl.gz`。原 ATP 实验没有调用 Lean Judge；本次补上此验证步骤。

Equation40037 的完整 TSTP 推导先由已有通用转换器 `translate_twee_formal_tstp.py` 转为等式证明 DAG，并独立重放代入、对称、传递与同余推理；只取连接源式到目标等式的证明祖先，生成紧凑 Lean。独立重放检查 2470 个节点；源输出 SHA-256 和转换统计见 [translation.json](../../Equation40037/translation.json)。最终可靠性由本次精确 Judge 验收确认，不依赖转换器自报成功。

Equation5834 与 Equation40037 对偶。归档的精简证书反转上述推导中每一个二元乘法节点，并显式使用变量置换 `hOriginal a c b`。这是相反运算下同一个等式推理，不需要新的推理公理；**精简后的具体 E5834 证书也单独取得 Judge accepted**，并非仅因对偶题已接受就改变状态。来源哈希见 [translation.json](../../Equation5834/translation.json)。另外，本地直接转换 E5834 自身 TSTP 的约 2 MB 版本也已通过 Judge，但不重复上传。

## 验收记录与复核边界

每题目录包括精确 `problem.json`、接受时原字节证书、脱敏 `judge_acceptance.json` 和配套 `JudgeProblem.lean`。目标模块根据实际提交的题目重建，并非 Judge 返回的历史原件。回执绑定的是题目五字段与实际提交证书 SHA-256；公开回执保留状态、公理、直接依赖、服务版本及执行指纹，移除内部地址、任务路径和原始日志。

`translation.json` 中 `official_judge_used: false` 描述生成阶段本身，不代表之后未验证；之后的实际验证以 `judge_acceptance.json` 为准。

[manifest.json](manifest.json) 绑定 10 个文件；[verify.ps1](verify.ps1) 只读检查这些哈希、精确命题、接受回执和索引分类。执行审计不再次调用 Judge，也不冒充数字签名或远端独立重放：

```powershell
pwsh -NoProfile -File proofs/validation/2026-09-09-twee-true/verify.ps1
```

Lean 重放须使用匹配的 Judge 依赖，每题隔离放置对应 `JudgeProblem.lean`；不能混用不同题的同名目标模块。
