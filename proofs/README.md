# 证明归档约定

每条方程使用一个目录；对偶方程也有独立记录。若证明由对偶转移，应保存实际 Lean 包装定理并链接原证明，不能仅因对偶已解决就把本方程的 Lean 状态改为已完成。

```text
proofs/
  index.json                         # 状态与逐文件 SHA-256
  Equation17260/
    README.md                        # 公式、对偶、原表、两侧状态、缺口
    InfiniteModel.lean               # 已有的非平凡模型证书
    JudgeProblem.lean                # 本题专用的目标定义
    FiniteTrivial.lean               # 约定名称；没有证明时不创建
  support/JudgeMagma/Magma.lean       # Judge 证书使用的共享基础模块
  provenance/                        # 原始验收索引、分类、对偶映射、上游源码
```

有限侧文件应证明在 `[Finite G]` 下源方程蕴含 Equation2。无限侧文件应提供运算、源方程成立的证明及载体无限性的证明。对偶模型可以复用载体并反转运算。

`index.json` 是 README 索引的数据源。状态分别记录数学结论、是否有 Lean 源码、历史验收以及本仓重编译，不能用单个 `solved` 字段代替。未收录的 `.lean` 文件不使用 `sorry` 占位。

当前快照包含：

- 130 条方程与 65 个对偶对，原表计数为 10 / 96 / 24。
- 42 份历史 `InfiniteModel.lean`，全部在本仓重新编译通过。40 份保持历史证书原样；Equation22619、Equation22634 仅将整库 Mathlib 导入缩小为 `Mathlib.Data.Nat.Basic`，证明正文不变，历史原件及哈希保存在 `provenance/`。历史目标是“不蕴含 Equation2”。其中 14 份另含 `tower_injective`，也已重新编译并检查公理；其余 28 份未单列无限性定理。
- 另新增 Equation12857、Equation33436 两份独立形式化模型证书，均含 Nat 单射；共享重写系统、汇合性和模型证明已在 Lean 4.33.1 内核检查通过。库存共有 44 份模型证书，其中 16 份单列无限性证明；新证明保留原历史 timeout 元数据。详见[新增形式化报告](validation/eq12857-formal/README.md)。
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

索引维护与低内存检查（Python 标准库，不运行求解器）：

```sh
python3 scripts/build_index.py
python3 scripts/build_index.py --check
```

修改证明后须重新验证，再更新 `index.json` 中的文件哈希、验证状态和证据来源。不得只更新 README 的勾选状态。新增无限性定理也须明确区分“写出了源码”和“已通过 Lean 内核检查”。

`provenance/` 的历史索引保留来源仓库内的原始路径；本仓可用路径见 `index.json` 的 `path` 字段。来源仓库的未决/超时状态只是当时运行结果，不是数学不可解结论。


E12857／E33436 新增模块的复跑与索引记录独立于上述历史批次：

```sh
python3 scripts/check_12857_lean.py
python3 scripts/record_12857_formal.py
python3 scripts/build_index.py --check
```

这批不依赖 Mathlib，串行运行，Lean 上限 768 MiB、RSS 采样停止线 1024 MiB。共享模块、两题各自的精确 Goal 包装和公理审计共 19 个编译单元，源码哈希及日志记录在 `validation/eq12857-formal/`。历史批次脚本跳过这两份本地模块证书，由此处的专用脚本完整重建依赖。

有限侧补证进度：表 20.1 10/10、表 20.2 96/96、表 20.3 8/24 份本地 Lean 证书通过。极光云有限目标验收仍待接口支持，详见[有限侧工作报告](validation/finite130/README.md)。
