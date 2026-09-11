# 2026-09-11：最新完整证明同步

以 main 的 `7152201b` 为基线，补入六份有限平凡性证明和四份非平凡无限模型证明。它们是十条方程、五对对偶；本批每条只补齐一侧，另一侧仍待解，不能把它们计作十条新 Austin 律。

| 方程与对偶 | 本批归档结论 | 保存的验证证据 | 另一侧 |
|---|---|---|---|
| [E12294](../../Equation12294/README.md) / [E33856](../../Equation33856/README.md) | 所有有限模型平凡 | Lean 4.33.1；[E12294](../finite130/division-images/Equation12294.json)、[E33856](../finite130/division-images/Equation33856.json) | 无限侧待解 |
| [E17286](../../Equation17286/README.md) / [E28626](../../Equation28626/README.md) | 所有有限模型平凡 | Lean 4.33.1；[E17286](../finite130/column-incidence/Equation17286.json)、[E28626](../finite130/column-incidence/Equation28626.json) | 无限侧待解 |
| [E22446](../../Equation22446/README.md) / [E22591](../../Equation22591/README.md) | 所有有限模型平凡 | Lean 4.33.1；[E22446](../finite130/finite-incidence/Equation22446.json)、[E22591](../finite130/finite-incidence/Equation22591.json) | 无限侧待解 |
| [E13102](../../Equation13102/README.md) / [E33273](../../Equation33273/README.md) | 非平凡无限模型，含 Nat 单射 | 云端 accepted；[E13102](../aurora/Equation13102/latest.json)、[E33273](../aurora/Equation33273/latest.json) | 有限侧待解 |
| [E23337](../../Equation23337/README.md) / [E23354](../../Equation23354/README.md) | 非平凡无限模型，含 Nat 单射 | 云端 accepted；[E23337](../aurora/Equation23337/latest.json)、[E23354](../aurora/Equation23354/latest.json) | 有限侧待解 |

有限证书为已成功编译源文件的逐字节副本，每题都有自己的完整定理及日志。无限模型的 `InfiniteModel.lean` 为云端实际提交并 accepted 的独立单文件源码的逐字节副本，不依赖本地未归档的模型模块。配套 `JudgeProblem.lean`、原请求、实际回执及任务绑定同时保存。四份模型均包含 `submission.CM.tower_injective`。

E13102/E33273 使用 Bruno Le Floch 的有理数分段构造，源码保留出处；E23337/E23354 使用三条夹心行像关系的正规树构造。对偶应用不计作独立构造。

## 库存变化

| 指标 | 原 main | 本批归档后 |
|---|---:|---:|
| 有限平凡性证书 | 114 | 120 |
| 非平凡模型证书 | 110 | 114 |
| 显式无限性证明 | 82 | 86 |
| 两侧证书齐全 | 106 | 106 |
| 已证所有模型平凡、排除 Austin 律 | 2 | 2 |
| 有限侧待解 | 16 | 10 |
| 无限侧尚无模型证书（含已排除项） | 20 | 16 |
| 无限侧实际待解 | 18 | 14 |

E5834/E40037 的 unrestricted true 证明已在 main 的 `Triviality.lean` 归档，保持原证书和验收记录，不重复计数。表 20.3 现在有 14/24 份有限证书、16/24 份模型证书，两侧齐全仍为 8/24。

有限侧剩余五对：E13102/E33273、E17260/E28740、E20911/E25087、E23337/E23354、E23357/E23653。

无限侧剩余七对：E9663/E36487、E12087/E33884、E18137/E27863、E12294/E33856、E17286/E28626、E22446/E22591、E23357/E23653。

## 核对方法

本次只使用 Python 标准库检查保存的证据，以 64 KiB 分块计算 SHA-256。没有重跑 Lean、求解器或云端 Judge，也没有把历史记录当成本次新验收。历史命令中的绝对路径仅表示原运行环境。

核对包括：全部 130 条库存的文件与证据哈希；六份有限证书的成功编译记录、精确源方程、有限性条件和目标定理；四份模型的精确请求、提交字节与 accepted 回执、Nat 单射源码；对偶映射；中英文 README 的完整表格与剩余清单；本批新增/修改文档的相对链接。公理审计仅允许 `propext`、`Classical.choice`、`Quot.sound`。

```sh
python3 proofs/validation/2026-09-11-latest-proofs/verify.py
```

[manifest.json](manifest.json) 绑定本批新增证书、原始证据和文档。[verify.py](verify.py) 为独立低内存审计入口，不依赖 main 已删除的 `scripts/` 目录。原有证明、贡献者记录和历史批次数据保留；本地未完成研究和构建产物不纳入本批。
