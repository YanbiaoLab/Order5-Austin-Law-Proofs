# Equation18137：非平凡无限模型的本地核验

2026-09-14，Lean 4.33.1。**已通过**四模块源码重建、独立单文件证书、精确原式、
非平凡性及自然数单射检查。随后已通过远端 Judge **ACCEPTED**，
见[远端归档](../aurora/Equation18137/README.md)。

模型与证明解释见 [MODEL.zh-CN.md](../../Equation18137/MODEL.zh-CN.md)。
单文件证书为 [InfiniteModel.lean](../../Equation18137/InfiniteModel.lean)。

## 重现

```sh
python3 proofs/validation/eq18137-formal/verify.py
```

只需 Python 标准库及已安装的 Lean `leanprover/lean4:v4.33.1`，不需要 Mathlib。
脚本验证单文件与四个模块一致，然后使用两个全新的临时编译目录。

第一目录依次编译 `TreeSchema`、`TreeBounds`、`TreeUnique`、`TreeModel`。
第二目录只编译本题的最小 `JudgeProblem` 和展平的 `InfiniteModel`，
不能复用第一目录的模块或旧的障碍定理。六个编译单元全部通过。

修改模块后重新生成单文件：

```sh
python3 proofs/validation/eq18137-formal/export_certificate.py
python3 proofs/validation/eq18137-formal/verify.py
```

`JudgeProblem.lean` 是按仓库原式重建的本地目标，包含最小 Magma 类；
`Goal` 是同一运算满足原式且不满足 `∀x y,x=y`。
证书另有字面原式的 `example` 和 `submission.CM.tower_injective`。
为符合远端声明白名单，导出证书把辅助声明放在 `submission.Equation18137TreeSchema`
命名空间；四个开发模块的数学内容不变。调整后的证书再次通过了全部本地检查。

## 证据边界

[summary.json](summary.json) 保存每个源码 SHA-256、完整命令、结果、公理和日志哈希。
最终 `submission`、`infinite_model` 只依赖标准经典公理
`propext`、`Classical.choice`、`Quot.sound`；原子单射不依赖公理。
四模块中的关系、大小、唯一性和中间步骤引理均在构造内部证明。
不存在外加的唯一性、原式、无限性假设。

最终运行按顺序执行，Lean 内部上限 192 MiB、外部进程树 RSS 上限 256 MiB、
每单元 20 秒。各次运行的累计子进程高水位见当前 `summary.json`，
RSS 采样间隔 0.05 秒；采样峰值和内核高水位分别记录，不能混为精确的进程树峰值。
结束后临时编译目录删除，没有遗留后台进程。

早先尝试编译通用 `JudgeMagma/Magma.lean` 时，它的完整 Init 导入超过外部上限，
进程被终止。随后目标文件改为仅定义本题需要的二元运算类，保持原资源上限。
早期停止不是数学失败；最终核验不再依赖那个模块。

模型结论来自上述 Lean 证明；编译不依赖探索实验或有限枚举。

## 远端验收

任务 `25f7dd0341414b5c83e91957ee920fba` 返回 `ACCEPTED`，耗时 4,633 ms，
只使用标准经典公理。实际请求、证书和回执均已归档。
本地 `summary.json` 的 `remote_judge: not_run` 只描述本地核验脚本本身；
远端结果独立保存在 `aurora/Equation18137` 与索引的 `aurora_validation` 字段。

```sh
python3 proofs/validation/eq18137-formal/audit_remote.py
```
