# 表 20.3：Equation20911／Equation25087 无限模型归档

本批收录两份已有 Judge v3 验收的精确模型证书，分别位于
[Equation20911](../../Equation20911/InfiniteModel.lean) 和
[Equation25087](../../Equation25087/InfiniteModel.lean)。两者原表均为 20.3。

| 方程 | 保存的 Judge v3 结果 | 证书字节数 | 显式无限性 |
|---|---|---:|---|
| Equation20911 | accepted / ACCEPTED / false | 2879 | `submission.CM.tower_injective` |
| Equation25087 | accepted / ACCEPTED / false | 2862 | `submission.CM.tower_injective` |

`false` 对应精确命题 `EquationN ↛ Equation2`，不是证明被拒绝。
两份文件分别有自己的 `JudgeProblem.lean` 与 `submission` 入口；均在有理数
载体上证明源等式成立及非平凡性，并在同一模块内证明自然数到该载体的单射。

这是一个独立构造及其相反运算，按方程编号计两项。基本运算来自
[Bruno Le Floch 于 2025-11-09 的公开模型](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#554572972)。
本批收录其对 Equation25087 及对偶 Equation20911 的形式化应用，不声称发明
基本运算，也不作全球优先权声明。

两式的**有限侧仍未知**；本批没有新增有限必平凡证明，因此不能据此确认它们为
Austin 律。已有 Equation20911 的 `FiniteStructure.lean` 及其证据保持原样。

## 字节、题目与验收记录

- `InfiniteModel.lean` 是保存的已接受 `Submission.lean` 的逐字节副本，仅文件名改变。
- `JudgeProblem.lean`、`problem.json` 使用该次提交保存的配套文件。
- `judge_acceptance.json` 按本仓已有格式保存脱敏验收摘要，包含精确源/目标、证书
  SHA-256、字节数、时间及实际 `accepted / ACCEPTED / false` 状态。内部地址和任务标识不发布。
- 两份已接受证书 SHA-256 分别为：
  - Equation20911：`eb3fa642caa3c0532a5060a09b216ca4fb984c45a1cc16c0eb5bf286d26ee185`
  - Equation25087：`c34100d47dd51620bb4d19e3b4241a191353886e20a4be7b7e8e6e41182c1441`
- 共享 `proofs/support/JudgeMagma/Magma.lean` 与保存的提交依赖仅有 CRLF/LF 换行差异，文本一致；仓库依赖保持原样，两种文件的哈希均记录在清单中。

本次上传只审计保存的证据，**未重新运行 Lean 或 Judge**。历史 accepted 不冒充本仓
重新编译结果，也不计入早期 42/42 的重新编译统计。重放两份证明需要匹配的
Judge/Mathlib 环境，且须各自使用自己的目标模块隔离编译。

## 清单更新与只读检查

逐文件 SHA-256、大小和题目绑定见 [manifest.json](manifest.json)。
按主分支去重后的库存为：总模型证书 **100/130**，有显式无限性的方程 **72**；
表 20.3 模型证书 **4/24**，有限必平凡证书仍为 **8/24**。Candidate-96 的计数未改变。

在仓库根目录运行（Python 标准库，不运行求解器）：

```sh
python3 proofs/validation/2026-09-10-open24-two-models/verify.py
python3 scripts/build_index.py --check
```

`index.json` 保存本批状态及来源；根 README 表格使用既有 `scripts/build_index.py` 生成。
