# E22591：E22446 模型的反向乘法

E22591 的精确方程为

\[
x=(y\diamond(y\diamond x))\diamond((x\diamond x)\diamond z).
\]

复用 [E22446 的正规三色树模型](../Equation22446/MODEL.zh-CN.md)，
保留同一个 `NormalTree` 载体。若原乘法记为 `*`，定义

\[
a\diamond b=b*a.
\]

于是 E22591 右侧化为

\[
(z*(x*x))*((x*y)*y),
\]

它由 E22446 定理取参数 `x,z,y` 等于 `x`。
因此 [InfiniteModel.lean](InfiniteModel.lean) 中的原式证明仅需
`Equation22446Lineage.equation22446 x z y`。
这里复用的是无条件的核心模型定理，不导入 E22446 的目标文件或 Magma 实例。
本题有独立的 [JudgeProblem.lean](JudgeProblem.lean)、反向乘法实例和 `submission : Goal`。

反转乘法不改变载体。原模型的 `normalTower` 仍给出自然数单射，
`normalTower 0` 和 `normalTower 1` 仍不相等。
原式、非平凡性和单射在本题的 `submission.infinite_model` 中合并。
最终五个端点全部经过 Lean 公理审计；自然数单射不依赖任何公理，
其余只使用 `propext`、`Classical.choice`、`Quot.sound`。

本机从空目录构建了 58 个模型模块，另外构建 56 个导出分段，共 114 次串行编译。
导出证书的核心前缀与 E22446 已获远端接受的证书逐字节相同；
仅替换最后的目标包装，使用本题反向乘法。
这既复用已有构造，又独立检查了 E22591 的目标及参数顺序。

[完整单文件证书](JudgeSubmission.lean)、[本机核验](../validation/eq22591-formal/README.md)、
[远端验收记录](../validation/aurora/Equation22591/README.md)。
结合此前已验证的 [有限平凡性证书](FiniteTrivial.lean)，E22591 的 Austin 律性质成立。
本次没有重跑有限侧 Mathlib 构建或重新提交有限侧远端任务。
