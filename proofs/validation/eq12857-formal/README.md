# E12857／E33436 Lean 形式化验收

**结果：全部 19 个编译单元通过 Lean 4.33.1；两条源等式及载体无限性均已证明。**

这批是本仓独立新增的形式化，独立于原有 42 份历史模型证书。历史 timeout 记录未改成 accepted，未重新调用官方 Judge。

已验证：严格终止、每条根部规则与任意一步重写的分歧可汇合、局部及全局汇合、规范形存在和唯一、规范树上的二元运算满足 E12857、反向运算满足 E33436，以及显式 Nat 单射。两份标准 Goal 包装另行检查非平凡模型存在性。

尚未新增有限侧坍缩定理，亦未另行形式化可数性的上界；本批所证明的无限性使用 Nat 单射。

生成器只输出普通证明文本。Lean 直接检查所有重叠分类分支和归约步骤，不把 Python 的关键对枚举结果作为公理。

公理检查仅出现 `propext`、`Classical.choice`、`Quot.sound` 的子集；无 `sorryAx` 或自定义公理。`norm` 用经典选择取得已经证明存在且唯一的规范形。

## 复跑

```sh
python3 scripts/check_12857_lean.py
python3 scripts/record_12857_formal.py
python3 scripts/build_index.py --check
```

需要已安装 `leanprover/lean4:v4.33.1`，不需要 Mathlib。一次一个进程、单线程；Lean 内存上限 768 MiB，每 0.2 秒采样 RSS，超过 1024 MiB 即停止；每文件上限 120 秒。

本次采样峰值 **685.31 MiB**，所有单元总计 **11.246 秒**。采样峰值不等同于操作系统记录的精确峰值。

完整输入哈希、命令、退出码及逐模块结果见 [summary.json](summary.json)。最终核心定理公理输出见 [Audit.log](Audit.log)。

| 模块 | 结果 | 秒 | 采样峰值 MiB | 日志 |
|---|---|---:|---:|---|
| Basic | PASS | 3.33 | 653.03 | [日志](Basic.log) |
| Peak1 | PASS | 0.416 | 610.53 | [日志](Peak1.log) |
| Peak2 | PASS | 0.625 | 605.47 | [日志](Peak2.log) |
| Peak3 | PASS | 0.624 | 598.88 | [日志](Peak3.log) |
| Peak4 | PASS | 0.422 | 599.36 | [日志](Peak4.log) |
| Peak5 | PASS | 0.622 | 671.91 | [日志](Peak5.log) |
| Peak6 | PASS | 0.418 | 603.58 | [日志](Peak6.log) |
| Peak7 | PASS | 0.412 | 585.33 | [日志](Peak7.log) |
| Peak8 | PASS | 0.621 | 675.8 | [日志](Peak8.log) |
| Peak9 | PASS | 0.626 | 685.31 | [日志](Peak9.log) |
| Peak10 | PASS | 0.419 | 579.34 | [日志](Peak10.log) |
| Confluence | PASS | 0.413 | 601.44 | [日志](Confluence.log) |
| Model | PASS | 0.415 | 603.27 | [日志](Model.log) |
| Audit | PASS | 0.418 | 572.33 | [日志](Audit.log) |
| JudgeMagma | PASS | 0.211 | 4.38 | [日志](JudgeMagma.log) |
| Equation12857-Goal | PASS | 0.208 | 4.38 | [日志](Equation12857-Goal.log) |
| Equation12857-Submission | PASS | 0.418 | 606.39 | [日志](Equation12857-Submission.log) |
| Equation33436-Goal | PASS | 0.211 | 4.36 | [日志](Equation33436-Goal.log) |
| Equation33436-Submission | PASS | 0.417 | 607.0 | [日志](Equation33436-Submission.log) |
