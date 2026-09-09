# Equation40037

- 对偶：[Equation5834](../Equation5834/README.md)
- 原表：20.2
- 方程：`x = (((y ◇ (x ◇ y)) ◇ z) ◇ x) ◇ z`
- 有限侧数学状态：仅平凡（Blueprint）

## 已排除为 Austin law

[Triviality.lean](Triviality.lean) 证明不带有限性假设的精确命题 `Equation40037 → Equation2`。本次独立提交 Judge v3，结果为 **accepted / ACCEPTED / true**。因此所有满足源等式的模型都平凡，不存在非平凡无限模型；这不是新增 Austin law。

这比仅证明有限模型平凡更强，无须另外复制一份 `FiniteTrivial.lean`。原表分类与历史 timeout 保留为历史信息，不代表当前数学状态。

配套：[精确题目](problem.json)、[目标模块](JudgeProblem.lean)、[脱敏 Judge 接受回执](judge_acceptance.json)、[证明生成来源](translation.json)。目标模块按实际提交的题目重建，不冒充服务端返回文件。证书本身保持 Judge 接受时的原始字节。

证明来自论文 ATP 实验的 Twee 完整 TSTP 推导，经通用转换器逐步重放等式推理并生成 Lean，再独立提交 Judge；并非仅凭 ATP 的 `Theorem` 状态判定。未使用 `grind`。

方法与复核见 [本批审计说明](../validation/2026-09-09-twee-true/README.md)；状态见 [index.json](../index.json)。每题须独立编译，不能把不同题的同名 `JudgeProblem` 混用。
