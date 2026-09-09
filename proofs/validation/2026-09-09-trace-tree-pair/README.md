# trace-tree 论文遗漏对偶对补录

本次仅补齐旧归档缺口：Equation9680 与 Equation36524 均已列入论文的 32 个 Candidate-96 结果，不计为新发现。

| 等式 | 证书 | 历史批次 |
|---|---|---|
| Equation9680 | [InfiniteModel.lean](../../Equation9680/InfiniteModel.lean) | trace_depth_sweep_soundfix_v5 |
| Equation36524 | [InfiniteModel.lean](../../Equation36524/InfiniteModel.lean) | trace_depth_sweep_soundfix_v5 |

证据来自 `trace-tree-magmas-release-20260905/arxiv-v1/experiments/unrestricted_four_search_20260904/`：`results/certificates/` 原始证书、`results/judge_receipts.jsonl` 的历史 `accepted / false` 记录和 `inputs/order5_130.jsonl` 冻结题目。

- 证书复制后逐字节、长度及 SHA-256 一致；仅改变文件名。
- 记录的 `problem_sha256` 由发布包 `scripts/bind_problem_hashes.py` 绑定；按其定义重新计算一致，不把这一字段称为在线 Judge 自身生成的签名。
- 发布包未包含对应原始 `JudgeProblem.lean`，本次按冻结输入重建。精确目标为 `∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G`。
- 此次只做静态绑定与哈希审计，无新的 Lean/Judge 执行或独立无限性定理核验。不同题目仍须在匹配依赖环境中隔离编译。
- 原论文 32 个编号均已收录，加后续 24 个不重叠编号，Candidate-96 中共 56 个证书条目；这不改变已验证旧批次 42/42 重编译的历史口径。

[manifest.json](manifest.json) 记录逐文件哈希；[verify.ps1](verify.ps1) 可只读核对归档、历史状态、题目绑定与重建目标。
