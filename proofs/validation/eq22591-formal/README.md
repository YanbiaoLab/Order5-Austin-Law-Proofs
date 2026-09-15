# E22591：Lean 与远端 Judge 核验

2026-09-15。[E22591 独立模型](../../Equation22591/InfiniteModel.lean)已证明精确原式、非平凡性和显式自然数单射；[完整单文件证书](../../Equation22591/JudgeSubmission.lean)首次提交远端 Judge 返回 **ACCEPTED**。结合既有有限平凡性证明，E22591 为 Austin 律。

模型保留 E22446 的 `NormalTree` 载体，定义 `a ◇ b := b * a`，由 E22446 原式取参数 `x, z, y` 得到本题原式。见[构造说明](../../Equation22591/MODEL.zh-CN.md)。

## 本机 Lean 检查

[summary.json](summary.json)保存全部命令、源码及日志 SHA-256、公理依赖和资源采样：

- Lean 4.33.1，从空目录构建，不复用 `.olean`，临时构建目录已清理。
- 58 个模型模块：E22446 的 56 个共享基础模块，以及 E22591 的独立目标和模型包装。
- 另编译 56 个导出分段：55 个原有导出核心分段，以及 E22591 导出包装；复用本次刚构建的基础 Magma 和 E22591 目标模块。
- 共 114 次编译，累计 17.431 秒，采样峰值 RSS 135.55 MiB。
- 单进程 `-j1 -M192`；RSS 超过 256 MiB 或单模块超过 120 秒即停止。
- 模型包装和导出包装各检查五个端点：`submission`、`submission.source_law`、`submission.nontrivial`、`submission.CM.tower_injective`、`submission.infinite_model`。
- Nat 单射无公理；其余最终端点仅用 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义公理。

[export.py](export.py)保留 E22446 已获接受证书的核心前缀，逐字节核对，仅替换末尾目标包装。模块化与导出版本均已分段检查；本机未运行完整单文件编译。完整单文件由远端 Judge 独立验收。

## 远端验收

任务 `910bd0a8ccad40e69c784c03968a3714`，状态 `done / accepted / ACCEPTED`，`verdict=false`，关闭缓存，17.436 秒。详细[回执与实际请求](../aurora/Equation22591/README.md)已保存。`false` 表示精确 E22591 不蕴含所有元素相等；显式无限性另由本机五端点检查中的单射定理证明。

## 复核入口

在仓库根目录运行，只使用 Python 标准库，不启动 Lean 或提交远端任务：

```sh
python3 proofs/validation/eq22591-formal/archive.py
```

该审计检查 [archive-manifest.json](archive-manifest.json)、114 次编译日志与源码、证书与请求的逐字节一致性、远端目标及回执、公理、有限侧原始证据、索引字段、双语 README 数量和链接。

仅检查本机和远端证明记录：

```sh
python3 proofs/validation/eq22591-formal/verify.py --remote
```

需要重新编译时，在单独的仓库副本中先将本目录的 `summary.json` 和 `logs/` 移出保存，再运行 `python3 proofs/validation/eq22591-formal/verify.py --compile`。脚本拒绝覆盖已有完整记录；新运行产生自己的时间、日志和哈希，不能冒充本次归档的原始记录。[remote.py](remote.py)保存了实际提交与续查过程；已有终态任务不会被重复提交。

有限侧仅核对 [FiniteTrivial.lean](../../Equation22591/FiniteTrivial.lean)、[原 Lean 运行记录](../finite130/finite-incidence/Equation22591.json)和[原日志](../finite130/finite-incidence/Equation22591.log)的哈希。本次没有重新构建 Mathlib 或重新提交有限侧远端任务。

本次发布后库存：120 份有限平凡性证书、122 份模型证书、94 份显式无限性证明，114 条两侧齐全，2 条已排除；无限侧尚有 6 条待补模型证书。
