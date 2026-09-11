# Equation23354

- 对偶：[Equation23337](../Equation23337/README.md)
- 原表：20.3
- 方程：`x = ((y ◇ x) ◇ y) ◇ (x ◇ (x ◇ z))`
- 有限侧数学状态：未知

无限侧 Lean：[InfiniteModel.lean](InfiniteModel.lean)，为原云端 accepted 单文件证书的逐字节副本；配套 [JudgeProblem.lean](JudgeProblem.lean) 给出精确题面。证书同时证明非平凡性及 `submission.CM.tower_injective`，给出从自然数到模型载体的单射。

[原请求](../validation/aurora/Equation23354/request.json)、[实际回执](../validation/aurora/Equation23354/latest.json)及[任务绑定](../validation/aurora/Equation23354/job.json)随同归档。本次核对提交字节、题面、哈希及 accepted 结果，未重跑 Lean/Judge。

有限侧仍未知：尚未证明所有有限模型平凡，也没有已验证的非平凡有限模型，因此仅凭本次无限模型不能确认为 Austin 律。

构造使用三条夹心行像关系的正规树模型；两个对偶方程共享构造。

详见[本批归档报告](../../proofs/validation/2026-09-11-latest-proofs/README.md)、[总索引](../index.json)。历史 timeout 仅记录历史搜索结果。
