# Equation25087

- 对偶：[Equation20911](../Equation20911/README.md)
- 原表：20.3
- 方程：`x = (y ◇ (x ◇ (x ◇ y))) ◇ (z ◇ z)`
- 有限侧数学状态：未知

有限侧 Lean：未收录。预留文件名 `FiniteTrivial.lean`，仅在有完整证明时创建。

无限模型：[InfiniteModel.lean](InfiniteModel.lean)，为已接受 `Submission.lean` 的逐字节副本。配套 [JudgeProblem.lean](JudgeProblem.lean)、[原始题目](problem.json)及[脱敏 Judge v3 回执](judge_acceptance.json)一并归档。验收结果为 `accepted / ACCEPTED / false`。

载体为有理数 `ℚ`；证书中的 `submission.CM.tower_injective` 证明 `n ↦ (n : ℚ)` 为单射，故模型无限。本式与 [Equation20911](../Equation20911/README.md) 使用同一构造及相反运算，两份证书分别验收。

基本分段运算来自 [Bruno Le Floch 的公开模型](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#554572972)；这里形式化其对本式的应用，不声称发明了该运算。

非平凡有限模型的存在性仍未知；无限侧通过验收不能单独确认为 Austin 律。

来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。本次只核对保存的证书及历史验收证据，未重新运行 Lean/Judge；详见[本批归档审计](../validation/2026-09-10-open24-two-models/README.md)。
