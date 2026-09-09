# Aurora-56 云端证书归档

基于最新主分支 `c5c39e3`（2026-09-09）。本批归档 56 份已由极光云 `judge-v3-repl` 实际接受的非平凡模型单文件证书，均包含 `submission.CM.tower_injective` 显式无限性证明。

**新增 30 个方程的模型条目；为已有 26 个编号补充本批证书和回执。** 主分支原有证书、JudgeProblem、历史回执和 E5834／E40037 的普遍平凡性证明全部保留。

合并后按方程编号去重：模型证书 98/130；其中 70 个编号至少有一份包含显式无限性定理的证书。表 20.2 为 86/96 个模型条目、2 个已排除、8 个未分类；表 20.1 为 10/10，表 20.3 为 2/24 个模型条目。

本次同步仅重核保存的 SHA-256、请求中的精确方程、提交代码、任务 ID、实际 `accepted / false` 返回及公理列表，没有重新运行 Lean 或调用 Judge。56 份均有云端 accepted；其中 30 份另附这些确切单文件字节的本机 Lean 4.33.1 编译记录。其他本地模块化证明的校验与本批单文件证据分开记录，不把不同文件的编译结果混用。

每份云端证书旁新增配套 `JudgeProblem.lean`，只有 `Lean.Elab.Tactic.Omega` 和 `JudgeProblem` 两项导入；共享 `JudgeMagma.Magma` 已在仓库归档。用于填补缺口的 30 份 `InfiniteModel.lean` 与云端提交字节一致。

低内存归档检查（Python 标准库，逐文件读取，不运行 Lean）：

```sh
python3 proofs/validation/2026-09-09-aurora56/validate.py
```

证书清单、哈希和主分支重合关系见 [manifest.json](manifest.json)。完整云端表见[实际验收记录](../aurora/README.md)。

| 方程 | 主分支原有条目 | 本批证书 | accepted 回执 |
|---|---|---|---|
| Equation5093 | 新增模型条目 | [Lean](../aurora/Equation5093/certificate.lean) | [accepted](../aurora/Equation5093/latest.json) |
| Equation41179 | 新增模型条目 | [Lean](../aurora/Equation41179/certificate.lean) | [accepted](../aurora/Equation41179/latest.json) |
| Equation5107 | 新增模型条目 | [Lean](../aurora/Equation5107/certificate.lean) | [accepted](../aurora/Equation5107/latest.json) |
| Equation40951 | 新增模型条目 | [Lean](../aurora/Equation40951/certificate.lean) | [accepted](../aurora/Equation40951/latest.json) |
| Equation5833 | 已有，补充证据 | [Lean](../aurora/Equation5833/certificate.lean) | [accepted](../aurora/Equation5833/latest.json) |
| Equation40070 | 已有，补充证据 | [Lean](../aurora/Equation40070/certificate.lean) | [accepted](../aurora/Equation40070/latest.json) |
| Equation5837 | 新增模型条目 | [Lean](../aurora/Equation5837/certificate.lean) | [accepted](../aurora/Equation5837/latest.json) |
| Equation40221 | 新增模型条目 | [Lean](../aurora/Equation40221/certificate.lean) | [accepted](../aurora/Equation40221/latest.json) |
| Equation5947 | 新增模型条目 | [Lean](../aurora/Equation5947/certificate.lean) | [accepted](../aurora/Equation5947/latest.json) |
| Equation40057 | 新增模型条目 | [Lean](../aurora/Equation40057/certificate.lean) | [accepted](../aurora/Equation40057/latest.json) |
| Equation5951 | 新增模型条目 | [Lean](../aurora/Equation5951/certificate.lean) | [accepted](../aurora/Equation5951/latest.json) |
| Equation40208 | 新增模型条目 | [Lean](../aurora/Equation40208/certificate.lean) | [accepted](../aurora/Equation40208/latest.json) |
| Equation6820 | 新增模型条目 | [Lean](../aurora/Equation6820/certificate.lean) | [accepted](../aurora/Equation6820/latest.json) |
| Equation39485 | 新增模型条目 | [Lean](../aurora/Equation39485/certificate.lean) | [accepted](../aurora/Equation39485/latest.json) |
| Equation6878 | 已有，补充证据 | [Lean](../aurora/Equation6878/certificate.lean) | [accepted](../aurora/Equation6878/latest.json) |
| Equation39126 | 已有，补充证据 | [Lean](../aurora/Equation39126/certificate.lean) | [accepted](../aurora/Equation39126/latest.json) |
| Equation6895 | 新增模型条目 | [Lean](../aurora/Equation6895/certificate.lean) | [accepted](../aurora/Equation6895/latest.json) |
| Equation39163 | 新增模型条目 | [Lean](../aurora/Equation39163/certificate.lean) | [accepted](../aurora/Equation39163/latest.json) |
| Equation6912 | 新增模型条目 | [Lean](../aurora/Equation6912/certificate.lean) | [accepted](../aurora/Equation6912/latest.json) |
| Equation39214 | 新增模型条目 | [Lean](../aurora/Equation39214/certificate.lean) | [accepted](../aurora/Equation39214/latest.json) |
| Equation7587 | 新增模型条目 | [Lean](../aurora/Equation7587/certificate.lean) | [accepted](../aurora/Equation7587/latest.json) |
| Equation38316 | 新增模型条目 | [Lean](../aurora/Equation38316/certificate.lean) | [accepted](../aurora/Equation38316/latest.json) |
| Equation7763 | 已有，补充证据 | [Lean](../aurora/Equation7763/certificate.lean) | [accepted](../aurora/Equation7763/latest.json) |
| Equation38565 | 已有，补充证据 | [Lean](../aurora/Equation38565/certificate.lean) | [accepted](../aurora/Equation38565/latest.json) |
| Equation8485 | 新增模型条目 | [Lean](../aurora/Equation8485/certificate.lean) | [accepted](../aurora/Equation8485/latest.json) |
| Equation37519 | 新增模型条目 | [Lean](../aurora/Equation37519/certificate.lean) | [accepted](../aurora/Equation37519/latest.json) |
| Equation9337 | 新增模型条目 | [Lean](../aurora/Equation9337/certificate.lean) | [accepted](../aurora/Equation9337/latest.json) |
| Equation36867 | 新增模型条目 | [Lean](../aurora/Equation36867/certificate.lean) | [accepted](../aurora/Equation36867/latest.json) |
| Equation9603 | 已有，补充证据 | [Lean](../aurora/Equation9603/certificate.lean) | [accepted](../aurora/Equation9603/latest.json) |
| Equation36514 | 已有，补充证据 | [Lean](../aurora/Equation36514/certificate.lean) | [accepted](../aurora/Equation36514/latest.json) |
| Equation9680 | 已有，补充证据 | [Lean](../aurora/Equation9680/certificate.lean) | [accepted](../aurora/Equation9680/latest.json) |
| Equation36524 | 已有，补充证据 | [Lean](../aurora/Equation36524/certificate.lean) | [accepted](../aurora/Equation36524/latest.json) |
| Equation10218 | 新增模型条目 | [Lean](../aurora/Equation10218/certificate.lean) | [accepted](../aurora/Equation10218/latest.json) |
| Equation35685 | 新增模型条目 | [Lean](../aurora/Equation35685/certificate.lean) | [accepted](../aurora/Equation35685/latest.json) |
| Equation11082 | 新增模型条目 | [Lean](../aurora/Equation11082/certificate.lean) | [accepted](../aurora/Equation11082/latest.json) |
| Equation34889 | 新增模型条目 | [Lean](../aurora/Equation34889/certificate.lean) | [accepted](../aurora/Equation34889/latest.json) |
| Equation11205 | 已有，补充证据 | [Lean](../aurora/Equation11205/certificate.lean) | [accepted](../aurora/Equation11205/latest.json) |
| Equation35100 | 已有，补充证据 | [Lean](../aurora/Equation35100/certificate.lean) | [accepted](../aurora/Equation35100/latest.json) |
| Equation11280 | 已有，补充证据 | [Lean](../aurora/Equation11280/certificate.lean) | [accepted](../aurora/Equation11280/latest.json) |
| Equation34778 | 已有，补充证据 | [Lean](../aurora/Equation34778/certificate.lean) | [accepted](../aurora/Equation34778/latest.json) |
| Equation12073 | 已有，补充证据 | [Lean](../aurora/Equation12073/certificate.lean) | [accepted](../aurora/Equation12073/latest.json) |
| Equation33998 | 已有，补充证据 | [Lean](../aurora/Equation33998/certificate.lean) | [accepted](../aurora/Equation33998/latest.json) |
| Equation12234 | 新增模型条目 | [Lean](../aurora/Equation12234/certificate.lean) | [accepted](../aurora/Equation12234/latest.json) |
| Equation33883 | 新增模型条目 | [Lean](../aurora/Equation33883/certificate.lean) | [accepted](../aurora/Equation33883/latest.json) |
| Equation12857 | 已有，补充证据 | [Lean](../aurora/Equation12857/attempt02/certificate.lean) | [accepted](../aurora/Equation12857/attempt02/latest.json) |
| Equation33436 | 已有，补充证据 | [Lean](../aurora/Equation33436/certificate.lean) | [accepted](../aurora/Equation33436/latest.json) |
| Equation12883 | 新增模型条目 | [Lean](../aurora/Equation12883/certificate.lean) | [accepted](../aurora/Equation12883/latest.json) |
| Equation33020 | 新增模型条目 | [Lean](../aurora/Equation33020/certificate.lean) | [accepted](../aurora/Equation33020/latest.json) |
| Equation13764 | 已有，补充证据 | [Lean](../aurora/Equation13764/certificate.lean) | [accepted](../aurora/Equation13764/latest.json) |
| Equation32294 | 已有，补充证据 | [Lean](../aurora/Equation32294/certificate.lean) | [accepted](../aurora/Equation32294/latest.json) |
| Equation13849 | 已有，补充证据 | [Lean](../aurora/Equation13849/certificate.lean) | [accepted](../aurora/Equation13849/latest.json) |
| Equation32281 | 已有，补充证据 | [Lean](../aurora/Equation32281/certificate.lean) | [accepted](../aurora/Equation32281/latest.json) |
| Equation13992 | 已有，补充证据 | [Lean](../aurora/Equation13992/certificate.lean) | [accepted](../aurora/Equation13992/latest.json) |
| Equation32280 | 已有，补充证据 | [Lean](../aurora/Equation32280/certificate.lean) | [accepted](../aurora/Equation32280/latest.json) |
| Equation18212 | 已有，补充证据 | [Lean](../aurora/Equation18212/certificate.lean) | [accepted](../aurora/Equation18212/latest.json) |
| Equation27859 | 已有，补充证据 | [Lean](../aurora/Equation27859/certificate.lean) | [accepted](../aurora/Equation27859/latest.json) |
