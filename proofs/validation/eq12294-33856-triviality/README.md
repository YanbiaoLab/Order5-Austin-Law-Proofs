# E12294／E33856：普遍平凡性证书与验收

2026-09-15。两题的精确命题均为 `EquationN → Equation2`，没有有限性、预设幂等点或额外消去律假设。全部非空模型只有一个元素，因此非平凡无限模型不存在，两题均不是 Austin 律。

| 方程 | Judge 接受的原字节证书 | 独立远端结果 | 任务 ID |
|---|---|---|---|
| E12294 | [Triviality.lean](../../Equation12294/Triviality.lean) | [accepted / ACCEPTED / true](../../Equation12294/judge_acceptance.json) | `2d6bf2b0724447038ae6f8931ad0b426` |
| E33856 | [Triviality.lean](../../Equation33856/Triviality.lean) | [accepted / ACCEPTED / true](../../Equation33856/judge_acceptance.json) | `3c2e09318f86444898b07387659df182` |

两份回执的公理依赖均为空。先收到 E12294 的 accepted，再准备和提交 E33856。每题一次提交、关闭缓存，Judge 耗时分别为 3.782 秒、3.705 秒。对应请求和响应保存在 [E12294 记录](Equation12294/request.json)、[E33856 记录](Equation33856/request.json)；响应只移除了内部后端地址，结果和时间戳保持原样。

E12294 证明右列像中的前驱唯一性，再通过自左除关系推出任意两元素相等。E33856 采用相反运算，完整基础证明嵌入其单文件，使用自己的精确目标独立验收。见[完整数学证明](../../Equation12294/PROOF.zh-CN.md)。

## 发布文件的本机重编译

本次从最新 `main` 的独立工作区整理发布文件，并在全新的临时目录中串行重新编译。两题各五个单元：本地兼容 Magma 接口、精确 Judge 目标、完整提交、入口公理检查和只依赖 Init 的独立证书，共 **10/10 通过**。两个 `submission : Goal` 入口均无公理依赖；E12294／E33856 独立文件分别审计七／九个最终声明，均为空。

Lean 4.33.1，单线程 `-j1 -M96`，外部 RSS 停止线 160 MiB，每单元 15 秒。最大实际 RSS 为 96,059,392 字节，约 91.61 MiB。没有复用原研究目录的 `.olean`，临时构建目录已清理。[summary.json](summary.json)绑定每个输入、日志及公理检查。

[Magma.lean](Magma.lean)是本地兼容接口；每题 [JudgeProblem.lean](../../Equation12294/JudgeProblem.lean)按其实际提交题目重建，不冒充远端返回文件。实际远端服务使用自己的可信目标模块。Judge 接受的原始提交字节保持不变：

| 方程 | 字节数 | SHA-256 |
|---|---:|---|
| E12294 | 10,517 | `e594322cd9a5652ecbf6a124316acdec468efef94be6ec1ea87f5280b8e85675` |
| E33856 | 11,084 | `cbea0aa9706bad6ca77eaf2da51ca0cd22b8ad1d458b7e9e0a73e6bcc6b1f287` |

## 只读复核与重编译

在仓库根目录运行，使用 Python 标准库，不发起远端任务：

```sh
python3 proofs/validation/eq12294-33856-triviality/check.py
```

该命令核对 [manifest.json](manifest.json)、十个编译单元的源码和日志、精确命题、请求与实际证书的逐字节一致性、远端回执和公理列表、独立提交顺序、索引及 README 状态。

如需重新编译，请安装 Lean 4.33.1，并选择新的输出目录，保存本次日志：

```sh
python3 proofs/validation/eq12294-33856-triviality/check.py --compile --output /tmp/eq12294-33856-recheck
```

脚本拒绝覆盖已有 `summary.json`；新运行只生成自己的时间和证据，不重写已归档记录，也不提交远端 Judge。

## 库存与提交范围

Lean 证书全部位于 `proofs/Equation12294`、`proofs/Equation33856`；发布包含精确题目、单文件证明、接受回执、数学说明和本目录的可复核记录。未纳入原工作区的大量部分模型试验，也未改动其它方程的证书。

两题在索引中记为 `unrestricted_triviality_proof` 和 `excluded_all_models_trivial`，不填入 `infinite_model_proof`。原有限侧证书与历史记录保留。其余 128 条方程记录和已有证据保持原样。

本次库存仍为 122 份模型证书；已证非平凡无限模型不可能的方程从 2 增至 4，无限侧待解从 6 降至 4。中英文 README 与 `proofs/README.md` 已同步更新。
