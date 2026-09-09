# Equation5093

- 对偶：[Equation41179](../Equation41179/README.md)
- 原表：20.2
- 方程：`x = y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y))))`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean)，在 `[Finite G]` 下推出 Equation2。保留上游定理正文，调整为最小依赖；已在本仓 Lean 4.33.1 编译通过。

无限侧 Lean：已收录本批经极光云 judge-v3-repl 接受的单文件模型证书，并包含显式 Nat 单射。历史批次超时记录保留。



来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。历史批次的本机检查见[重新编译报告](../validation/2026-09-08/README.md)；本批新模型的云端验收及已有本机记录见下方批次报告。


本批 Aurora-56 补充：[实际提交的单文件证书](../validation/aurora/Equation5093/certificate.lean) 与[实际 accepted 回执](../validation/aurora/Equation5093/latest.json)。目标为本题源等式成立且模型非平凡；`submission.CM.tower_injective` 给出显式无限性。任务 ID：`af34a280433348c29e16fd23a554949c`。本次归档核对已有验收记录，未重跑 Lean/Judge；见[批次报告](../validation/2026-09-09-aurora56/README.md)。
