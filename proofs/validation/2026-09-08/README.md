# Lean 重新编译报告

日期：2026-09-08。结果：**44 / 44 通过**。

- 非平凡模型证书：42 / 42；40 份原文件哈希保持不变。Equation22619、Equation22634 仅将整库导入替换为 `Mathlib.Data.Nat.Basic`，证明正文不变，历史原件及哈希单独保存在 provenance。
- 显式无限性：上述证书中的 14 份 `tower_injective` 均通过，并检查其公理依赖。其余 28 份未新增无限性定理。
- 有限坍缩定理：2 / 2（Equation5093、Equation28770）。原定理正文不变，使用显式方程定义、JudgeMagma 和现有 Mathlib 缓存，在 Lean 4.33.1 编译；本次没有重建旧版上游工程。
- 各证明的依赖仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或其他自定义公理。
- 这是本地 Lean 编译、目标类型和公理依赖检查，不是重新调用官方 Judge。

每个模型检查文件使用原证书全文，追加 `example : Goal := submission` 和 `#print axioms`。目标由每题 `JudgeProblem.lean` 定义。有限侧显式定义与库存公式一致，原定理证明正文与归档上游源码逐字核对。

资源：单进程、单线程；Lean 内存上限 2048 MiB，采样 RSS 上限 3072 MiB，单文件 120 秒。本次已通过的证明采样峰值为 1208.98 MiB。RSS 每 0.2 秒采样，不代表操作系统记录的精确峰值。

两份整库 Mathlib 导入曾触发 3 GiB RSS 停止线；缩小导入后，两份分别在 795.28 / 796.55 MiB 采样峰值下通过。

编译保留 warning-as-error，按需关闭 `linter.defProp`、`linter.unusedVariables`、`linter.unusedSimpArgs` 三项风格检查以兼容历史源码；没有关闭证明或公理检查。

重放命令（项目根目录；第二个路径指向已存在且编译好的 Mathlib 环境）：

```sh
python3 scripts/recompile_lean.py --memory-mib 2048 --rss-mib 3072 \
  --finite-mathlib-root /path/to/equational-theories-lean-stage2
python3 scripts/record_lean_validation.py
python3 scripts/build_index.py --check
```

JSON 记录保存实际命令、编译版本、输入哈希、LEAN_PATH、退出码和采样内存。`.build/` 是可重建缓存。

| 方程 | 类型 | 结果 | 秒 | 采样峰值 MiB | 日志 |
|---|---|---|---:|---:|---|
| Equation4916 | model | PASS | 2.081 | 429.78 | [日志](Equation4916-model.log) |
| Equation41082 | model | PASS | 2.067 | 438.42 | [日志](Equation41082-model.log) |
| Equation15535 | model | PASS | 14.512 | 522.59 | [日志](Equation15535-model.log) |
| Equation30591 | model | PASS | 16.164 | 515.11 | [日志](Equation30591-model.log) |
| Equation17522 | model | PASS | 0.824 | 420.77 | [日志](Equation17522-model.log) |
| Equation28770 | model | PASS | 1.04 | 425.5 | [日志](Equation28770-model.log) |
| Equation28770 | finite | PASS | 0.833 | 1208.98 | [日志](Equation28770-finite.log) |
| Equation20034 | model | PASS | 0.624 | 417.66 | [日志](Equation20034-model.log) |
| Equation25964 | model | PASS | 0.623 | 417.75 | [日志](Equation25964-model.log) |
| Equation22455 | model | PASS | 1.039 | 426.27 | [日志](Equation22455-model.log) |
| Equation22818 | model | PASS | 1.454 | 443.16 | [日志](Equation22818-model.log) |
| Equation4952 | model | PASS | 0.624 | 682.45 | [日志](Equation4952-model.log) |
| Equation41252 | model | PASS | 0.625 | 694.11 | [日志](Equation41252-model.log) |
| Equation4957 | model | PASS | 0.624 | 684.64 | [日志](Equation4957-model.log) |
| Equation40914 | model | PASS | 0.62 | 683.8 | [日志](Equation40914-model.log) |
| Equation5012 | model | PASS | 0.624 | 673.91 | [日志](Equation5012-model.log) |
| Equation41253 | model | PASS | 0.62 | 662.3 | [日志](Equation41253-model.log) |
| Equation5066 | model | PASS | 0.626 | 607.47 | [日志](Equation5066-model.log) |
| Equation41239 | model | PASS | 0.623 | 606.03 | [日志](Equation41239-model.log) |
| Equation5093 | finite | PASS | 0.83 | 1205.53 | [日志](Equation5093-finite.log) |
| Equation5141 | model | PASS | 0.621 | 684.02 | [日志](Equation5141-model.log) |
| Equation40917 | model | PASS | 0.624 | 686.14 | [日志](Equation40917-model.log) |
| Equation5295 | model | PASS | 0.623 | 686.78 | [日志](Equation5295-model.log) |
| Equation40909 | model | PASS | 0.624 | 686.23 | [日志](Equation40909-model.log) |
| Equation7701 | model | PASS | 0.414 | 605.88 | [日志](Equation7701-model.log) |
| Equation38303 | model | PASS | 0.413 | 602.38 | [日志](Equation38303-model.log) |
| Equation7755 | model | PASS | 0.417 | 607.41 | [日志](Equation7755-model.log) |
| Equation38249 | model | PASS | 0.626 | 611.75 | [日志](Equation38249-model.log) |
| Equation9345 | model | PASS | 0.622 | 685.19 | [日志](Equation9345-model.log) |
| Equation36713 | model | PASS | 0.624 | 682.86 | [日志](Equation36713-model.log) |
| Equation9384 | model | PASS | 0.624 | 602.25 | [日志](Equation9384-model.log) |
| Equation36714 | model | PASS | 0.417 | 604.69 | [日志](Equation36714-model.log) |
| Equation9667 | model | PASS | 0.624 | 684.36 | [日志](Equation9667-model.log) |
| Equation36638 | model | PASS | 0.625 | 610.34 | [日志](Equation36638-model.log) |
| Equation11081 | model | PASS | 0.826 | 690.78 | [日志](Equation11081-model.log) |
| Equation35036 | model | PASS | 0.824 | 662.84 | [日志](Equation35036-model.log) |
| Equation11116 | model | PASS | 0.415 | 611.83 | [日志](Equation11116-model.log) |
| Equation34888 | model | PASS | 0.624 | 688.3 | [日志](Equation34888-model.log) |
| Equation19966 | model | PASS | 57.06 | 659.52 | [日志](Equation19966-model.log) |
| Equation26105 | model | PASS | 53.93 | 611.78 | [日志](Equation26105-model.log) |
| Equation22619 | model | PASS | 1.25 | 795.28 | [日志](Equation22619-model.log) |
| Equation22634 | model | PASS | 1.042 | 796.55 | [日志](Equation22634-model.log) |
| Equation17260 | model | PASS | 0.832 | 420.67 | [日志](Equation17260-model.log) |
| Equation28740 | model | PASS | 0.826 | 420.81 | [日志](Equation28740-model.log) |
