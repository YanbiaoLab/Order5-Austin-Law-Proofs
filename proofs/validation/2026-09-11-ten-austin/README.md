# 2026-09-11：十条完整 Austin 律证明归档

以 `main` 的 `3bee0d5062bb0dd40c319aec07b55bab9b4724a8` 为基线，补入下列十条方程的非平凡无限模型证明。它们的有限平凡性证明已在 main；此次补齐无限侧，使十条方程均具有完整 Austin 律证据。

| 方程 | 对偶 | 本地验证记录 | 云端记录 |
|---|---|---|---|
| E10222 | E35836 | [15 个编译单元通过](../eq10222-formal/summary.json) | 未提交 |
| E21714 | E24200 | [30 个编译单元通过，八题共用](../eq21866-formal/summary.json) | [E21714](../aurora/Equation21714/latest.json)、[E24200](../aurora/Equation24200/latest.json) accepted |
| E21864 | E24199 | 同上 | [E21864](../aurora/Equation21864/latest.json)、[E24199](../aurora/Equation24199/latest.json) accepted |
| E21865 | E24197 | 同上 | [E21865](../aurora/Equation21865/latest.json)、[E24197](../aurora/Equation24197/latest.json) accepted |
| E21866 | E24201 | 同上 | [E21866](../aurora/Equation21866/latest.json)、[E24201](../aurora/Equation24201/latest.json) accepted |

这是十条方程、五对对偶、两组共享构造，不计作十个独立构造。每条均有自己的 `InfiniteModel.lean`、精确 `JudgeProblem.Goal` 和 `submission.CM.tower_injective`。核心证明、独立单文件证书、逐单元日志和 JSON 清单随同归档。核心源码见 [E10222 原式证明](../../Equation10222/Lean/Austin10222/UnitLaw.lean)和 [E21866 行像关系模型](../../Equation21866/Lean/Austin21866/Model.lean)。

## 库存变化

| 指标 | main 基线 | 本批归档后 |
|---|---:|---:|
| 有限平凡性 Lean 证书 | 114 | 114 |
| 非平凡模型 Lean 证书 | 100 | 110 |
| 两方面证书齐全 | 96 | 106 |
| 显式无限性证明 | 72 | 82 |
| 表 20.2 的模型证书 | 86 / 96 | 88 / 96 |
| 表 20.3 的模型证书 | 4 / 24 | 12 / 24 |
| 表 20.3 两方面证书齐全 | 0 / 24 | 8 / 24 |

表 20.2 另有两条已被排除，剩余六条无限侧未分类。表 20.3 的其余四份既有模型证书，其有限侧仍未知。原始表分类保留。其他本地研究结果未纳入本批统计。

## 本次核对范围

归档核对使用 Python 标准库并以 64 KiB 分块计算 SHA-256，不运行求解器、Lean 或远程 Judge。原 Lean 4.33.1 验证记录与实际回执保留，历史绝对命令路径只表示原运行环境。本次归档没有产生新的编译或云端验收结果。

核对包括十条精确题面、源文件和依赖哈希、45 份成功编译记录及其日志、公理依赖、八份请求的实际提交字节与 accepted 回执，以及双语 README 的库存表格和链接。允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`。可重建的 `.olean` 和研究过程文件未归档；保存的 `.olean` 哈希是历史产物信息，本次不声称重新验证该产物。

```sh
python3 proofs/validation/2026-09-11-ten-austin/verify.py
python3 scripts/build_index.py --check
```

[manifest.json](manifest.json) 绑定本批归档文件。原始证明源码与验证 JSON、日志逐字节保留；说明文档调整为本批归档范围。所有既有有限侧记录和其他 120 条方程记录保持原样。
