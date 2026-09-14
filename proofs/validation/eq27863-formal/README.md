# Equation27863：对偶无限模型的本地与远端核验

2026-09-14，Lean 4.33.1。**本地七个编译单元通过，远端 Judge ACCEPTED。**

模型载体与 Equation18137 相同，是自然数标号的所有有限二叉树。
定义 `dualOp(a,b) = Equation18137.op(b,a)`；原式中交换后两个变量即可证明
精确的 Equation27863。自然数单射与两个不同原子均保留。
参见 [DualModel.lean](../../Equation27863/DualModel.lean)。

## 本地核验

```sh
python3 proofs/validation/eq27863-formal/verify.py
```

第一个空目录依次重编译 `TreeSchema`、`TreeBounds`、`TreeUnique`、`TreeModel`、
`DualModel`，不假设旧模型模块已经正确或可用。
第二个空目录只编译本题的 `JudgeProblem` 与独立展平的 `InfiniteModel`，
不能复用前一个目录的产物。

检查范围包括：同一总运算的精确原式、非平凡性、任意自然数上的单射，以及各指定定理的公理依赖。
模型证书仅依赖标准经典公理 `propext`、`Classical.choice`、`Quot.sound`；
单射定理不依赖任何公理。没有 `sorryAx` 或外加模型假设。

源码、命令、日志哈希和资源记录见 [summary.json](summary.json)。
按顺序执行，每单元内部上限 192 MiB、外部 RSS 上限 256 MiB、20 秒；
采样峰值与内核高水位分别保存在当前记录中，临时编译目录在结束后清理。
核验工具只依赖 Python 标准库和已安装的 Lean `leanprover/lean4:v4.33.1`，不需要 Mathlib；
有界子进程运行器内置于 `verify.py`，每 0.05 秒监控进程树 RSS。

修改源模块后重导出并重新验证：

```sh
python3 proofs/validation/eq27863-formal/export_certificate.py
python3 proofs/validation/eq27863-formal/verify.py
```

## 远端验收

任务 `c57824e679ec4461b923a5237bdfcd56` 返回 `ACCEPTED`，耗时 4,578 ms。
请求关闭缓存，只提交一次。远端目标是 `Equation27863 ↛ Equation2`；
自然数单射另在本地单列核验。

[实际提交证书](../aurora/Equation27863/certificate.lean)、
[请求](../aurora/Equation27863/request.json)、[原始回执](../aurora/Equation27863/latest.json)。

核对本地证明、实际提交字节、命题绑定和回执：

```sh
python3 proofs/validation/eq27863-formal/audit_remote.py
```

读取同一个已有任务，不重复提交：

```sh
python3 proofs/validation/eq27863-formal/remote_judge.py --wait
```
