# Equation27863

- 对偶：[Equation18137](../Equation18137/README.md)
- 原表：20.2
- 方程：`x = ((y ◇ (y ◇ x)) ◇ y) ◇ (x ◇ z)`
- 有限侧数学状态：已证仅平凡（Lean）

有限侧：[FiniteTrivial.lean](FiniteTrivial.lean) 在 `[Finite G]` 下推出 Equation2，已通过 Lean 4.33.1 本地编译与公理检查。

无限侧：**非平凡无限模型已完成，本地 Lean 4.33.1 与远端 Judge 均通过（2026-09-14）**。
见[对偶转移证明](DualModel.lean)、[独立完整证书](InfiniteModel.lean)和
[验证记录](../validation/eq27863-formal/README.md)。历史超时只表示此前的运行结果。



来源与验证状态见 [index.json](../index.json) 和 [归档说明](../README.md)。
远端任务 `c57824e679ec4461b923a5237bdfcd56` 返回 **ACCEPTED**，
见[原始回执](../validation/aurora/Equation27863/latest.json)。

## 对偶构造

保持 Equation18137 的无限树载体，将原运算 \(\diamond\) 反转：
\[
a\star b=b\diamond a.
\]
则
\[
((y\star(y\star x))\star y)\star(x\star z)
=(z\diamond x)\diamond\bigl(y\diamond((x\diamond y)\diamond y)\bigr)=x.
\]
最后一步是 Equation18137 对变量 `(x,z,y)` 的应用。自然数标号原子的单射不变，
因此同一载体仍然无限且非平凡。Lean 已核验字面原式，并非仅凭对偶编号更新状态。

```sh
python3 proofs/validation/eq27863-formal/verify.py
python3 proofs/validation/eq27863-formal/audit_remote.py
```

有限侧极光云验收尚未完成：当前服务缺少有限目标接口，见[本批报告](../validation/finite130/README.md)。

## 本分支有限侧证书补充

[FiniteTrivial.lean](FiniteTrivial.lean) 已收录；对应本地 Lean 编译与公理检查记录见 [校验日志](../../proofs/validation/finite130/Equation27863.log)。这是新增的有限侧归档记录，上文各批次的来源、模型证书和历史验证说明保留。
