# Equation12087 / Equation33884 完整无限模型验证

2026-09-14：两条精确原式、非平凡性与显式自然数单射均通过 Lean 4.33.1 本地核验。模型及历史复盘见 [MODEL.zh-CN.md](../../Equation12087/MODEL.zh-CN.md)。后续独立单文件证书已分别获得远端 Judge **ACCEPTED**；见[提交与回执审计记录](JUDGE.md)。下文保留原模块化本地核验的范围。

## 核验范围

- [125 个冻结核心模块](../../Equation12087/Lean/TraceFullSource.lean)，逐个从空目录编译，311 个指定端点全部做公理审计。
- [12087 正式目标](../../Equation12087/JudgeProblem.lean)和[模型包装](../../Equation12087/InfiniteModel.lean)。
- [33884 正式目标](../../Equation33884/JudgeProblem.lean)和[反向运算模型](../../Equation33884/InfiniteModel.lean)。对偶包装调用 `full_source_law x z y`，变量位置与索引公式一致。
- 两个 `submission : Goal` 都证明存在满足精确方程的非平凡 magma；`submission.CM.tower_injective` 检查任意自然数上的单射。
- 核心 `Austin12087Trace.infinite_model` 将原式、单射、两个不同元素封装在同一个无条件存在命题中。

共 129 次模块构建，没有复用研究目录缓存。全部端点的公理仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集；源码无 `sorry`、`admit`、自定义公理或 `native_decide`。核心 311 端点与两个模型包装的 7 个检查项共 318 个公理报告。

使用串行 `-j1 -M256`、384 MiB RSS 停止线、单模块 120 秒上限。本轮新鲜构建累计约 44.43 秒，采样峰值约 198.34 MiB；短进程的采样不代表精确峰值。所有验证进程均已退出。

[summary.json](summary.json) 记录每个源码、编译命令、日志、产物哈希和公理集合。模型是模块化证书，登记的依赖显式包含全部 125 个核心源码及该方程的目标定义；不声称包装文件脱离依赖后可单独编译。

## 复现

```sh
python3 proofs/validation/eq12087-formal/portable.py
python3 proofs/validation/eq12087-formal/portable.py --rebuild
```

`portable.py` 默认只读核对归档源码、日志、精确导出、回执和库存哈希；加 `--rebuild` 后，从新建空目录串行编译 125 个核心模块及两个精确目标包装，输出放在 `.build/`。只需 Python 标准库与 Lean 4.33.1，不需要原研究目录。

原 `verify.py`、`audit.py`、`verify_judge.py` 等脚本及历史清单按原字节保留，记录当时使用的路径，不能作为新检出的运行入口。历史清单中的 `scripts/check_12857_lean.py` 对应本目录 [support/check_12857_lean.py](support/check_12857_lean.py) 的相同字节；可移植审计显式处理这一归档映射。旧 `.olean` 的绝对路径与哈希只作为历史信息保存，新检出通过新鲜重编译验证，未随仓库发布编译缓存。

早期 `search/validation/12087-trace-candidate` 的检查器为所有请求打印固定的候选提示，没有专门检查正式 `Goal`；因此最终完整性以本目录的精确目标检查为准。历史记录不被覆盖为“当时已完成”。

发布前已在基于最新远端 main 的独立工作区运行上述 `portable.py --rebuild`：129 次新鲜构建、318 个公理报告通过，采样峰值 223.69 MiB。见[发布核验摘要](publication-check.json)与[构建日志](publication-rebuild.log)。源码及回执均在 `proofs/`，不发布 `.olean` 缓存。
