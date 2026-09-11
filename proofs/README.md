# 证明归档约定

当前归档（2026-09-11）：**120 份有限平凡性证书、114 份非平凡模型证书、86 份显式无限性证明**。两侧证书齐全为 106 条；另 2 条已有所有模型平凡的证明。有限侧剩 10 条、无限侧剩 14 条待解（另 2 条已排除，因此缺模型证书合计 16 条）。最新十条方程补证及剩余编号见[同步报告](validation/2026-09-11-latest-proofs/README.md)；以下早期批次数字保留为历史记录。

本次审计入口不依赖已删除的 `scripts/`：

```sh
python3 proofs/validation/2026-09-11-latest-proofs/verify.py
```

每条方程使用一个目录；对偶方程也有独立记录。若证明由对偶转移，应保存实际 Lean 包装定理并链接原证明，不能仅因对偶已解决就把本方程的 Lean 状态改为已完成。

```text
proofs/
  index.json                         # 状态与逐文件 SHA-256
  Equation17260/
    README.md                        # 公式、对偶、原表、两侧状态、缺口
    InfiniteModel.lean               # 已有的非平凡模型证书
    JudgeProblem.lean                # 本题专用的目标定义
    FiniteTrivial.lean               # 约定名称；没有证明时不创建
    Triviality.lean                  # 更强的全部模型平凡证明；若有，则排除 Austin
  support/JudgeMagma/Magma.lean       # Judge 证书使用的共享基础模块
  provenance/                        # 原始验收索引、分类、对偶映射、上游源码
```

有限侧文件应证明在 `[Finite G]` 下源方程蕴含 Equation2。`Triviality.lean` 则无有限性假设，证明精确 `EquationN → Equation2`，应记录在 `unrestricted_triviality_proof`，不得填入 `infinite_model_proof`。无限侧文件应提供运算、源方程成立的证明及载体无限性的证明。对偶模型可以复用载体并反转运算。

`index.json` 是 README 索引的数据源。状态分别记录数学结论、是否有 Lean 源码、历史验收以及本仓重编译，不能用单个 `solved` 字段代替。未收录的 `.lean` 文件不使用 `sorry` 占位。

2026-09-08 已验证快照包含：

- 130 条方程与 65 个对偶对，原表计数为 10 / 96 / 24。
- 42 份 `InfiniteModel.lean`，全部在本仓重新编译通过。40 份保持历史证书原样；Equation22619、Equation22634 仅将整库 Mathlib 导入缩小为 `Mathlib.Data.Nat.Basic`，证明正文不变，历史原件及哈希保存在 `provenance/`。历史目标是“不蕴含 Equation2”。其中 14 份另含 `tower_injective`，也已重新编译并检查公理；其余 28 份未单列无限性定理。
- Equation5093、Equation28770 的 `FiniteTrivial.lean`，定理正文从上游 `InfModel.lean` 提取，保留命名空间。使用最小 Mathlib 导入及显式等价方程定义，已在本仓编译通过。原始完整文件及 Apache-2.0 许可证保存在 `provenance/`；依赖调整与前后哈希记录在 `index.json`。
- 每份模型证书配套的 `JudgeProblem.lean` 根据归档方程重新生成，其 `Goal` 为非平凡模型存在性。这些目标文件没有冒充历史 Judge 的原始模块。

2026-09-08 已完成 **44 / 44** 本地 Lean 重新编译、目标类型检查及公理依赖检查，详见[编译报告](validation/2026-09-08/README.md)。这是本地编译结果，没有重新调用官方 Judge。导入范围是已核实的 v1 验收集及上述上游有限定理，后续批次须按实际验收证据增补。

上游有限定理原环境是 Lean 4.29.1，历史 Judge 环境是 Lean 4.33.1，对应 toolchain 文件保存在 `provenance/`。本次所有归档证明统一在 **Lean 4.33.1** 编译；有限侧和两份模型需要现有 Mathlib 缓存，其余模型只需要 Lean 与 `JudgeMagma`。本仓提供逐题隔离编译脚本，尚未配置 Lake 工程。重放历史 Judge 时仍须检查其完整协议；本地编译不能替代官方验收。

重新编译（一次一个进程；下列资源上限已获本次用户授权）：

```sh
python3 scripts/recompile_lean.py --memory-mib 2048 --rss-mib 3072 \
  --finite-mathlib-root /path/to/equational-theories-lean-stage2
python3 scripts/record_lean_validation.py
```

Mathlib 路径必须指向已有 Lean 4.33.1 编译缓存的 Lake 项目；脚本不会构建大型依赖。`--resume` 只复用本地成功且输入哈希未变的检查。逐题日志和命令保存在 `validation/2026-09-08/`，可重建的编译输出放在被 Git 忽略的 `.build/`。

历史索引维护命令（`scripts/` 已从 main 删除；当前请使用顶部审计入口）：

```sh
python3 scripts/build_index.py
python3 scripts/build_index.py --check
```

修改证明后须重新验证，再更新 `index.json` 中的文件哈希、验证状态和证据来源。不得只更新 README 的勾选状态。新增无限性定理也须明确区分“写出了源码”和“已通过 Lean 内核检查”。

`provenance/` 的历史索引保留来源仓库内的原始路径；本仓可用路径见 `index.json` 的 `path` 字段。来源仓库的未决/超时状态只是当时运行结果，不是数学不可解结论。

## 2026-09-09 增补

新增 24 份精确 `EquationN ↛ Equation2` 的历史 Judge v3 accepted 证书，详见 [增补记录](validation/2026-09-09-austin24/README.md)。22 个此前只有说明页的目录补入 `InfiniteModel.lean` 和原始 `JudgeProblem.lean`；Equation12857／Equation33436 原证明不变，新证书独立放在 `JudgeV3/`。

证书为 `Submission.lean` 的逐字节副本（仅改文件名），不套用旧批次重建的目标定义。每题提供脱敏历史回执与原始题目。此次只有哈希、编号及命题绑定审计，无新的 Lean/Judge 执行。历史接受不冒充本仓重编译或独立无限性定理的验证。各题须隔离编译。

只读核验：

```powershell
pwsh -NoProfile -File proofs/validation/2026-09-09-austin24/verify.ps1
```

## 论文原有两题补录

另见本日新增的 [Twee true 证书审计](validation/2026-09-09-twee-true/README.md)：Equation5834／Equation40037 的精确 unrestricted true 命题均重新获得 Judge v3 accepted，排除这两个 Austin-96 候选。它们不是本节下述两份历史 false 证书，也不计入 56 份非平凡模型库存。

补入 Equation9680／Equation36524 的历史 `trace_depth_sweep_soundfix_v5` 证书，恢复论文原有 **32/32** 个 Candidate-96 编号；加后续 24 个不重叠编号，现有 **56/96** 个候选条目。旧库存的 30 不是论文总数。

证书字节不变，`JudgeProblem.lean` 按冻结输入重建，非历史原始模块。证书哈希与发布包规范化题目哈希已核对，本次未重跑 Lean/Judge。详见 [补录审计](validation/2026-09-09-trace-tree-pair/README.md)。

```powershell
pwsh -NoProfile -File proofs/validation/2026-09-09-trace-tree-pair/verify.ps1
```


2026-09-09 Aurora-56 增补：本次按最新 main 去重后新增 30 个模型条目，并为已有 26 个编号追加本批云端证书。累计 98 个方程有模型证书、70 个有显式无限性定理；本批 56 份均有实际 accepted 回执。原有证书保留；`explicit_infinity_proof` 指向本批显式无限性定理，`additional_model_proofs` 收录已有编号的补充证书。文件和回执的核对方式见[批次报告](validation/2026-09-09-aurora56/README.md)。

## 2026-09-10 表 20.3 新增两份模型

Equation20911／Equation25087 分别补入原样模型证书、原始配套目标和脱敏 Judge v3 accepted 回执，均含 `submission.CM.tower_injective`。表 20.3 模型证书由 2 增至 4，总模型库存由 98 增至 100，显式无限性由 70 增至 72；有限侧状态未改变。本批仅核对保存的验收证据，不计入早期本仓重新编译结果；详见[归档报告](validation/2026-09-10-open24-two-models/README.md)。

## 2026-09-11：补齐十条 Austin 律

新增十条方程的无限模型证书、依赖与原验证记录，配对既有有限平凡性证明。模型证书累计 110 份，有限平凡性证书 114 份，两方面齐全 106 条；显式无限性证明 82 份。详见[本批报告](validation/2026-09-11-ten-austin/README.md)。本次审计保存的证据，未重跑 Lean/Judge。

上述历史批次使用 `scripts/build_index.py` 生成双语表格；该目录现已从 main 删除，当前核验请使用顶部独立审计入口。
