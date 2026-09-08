# 表 20.3：通过有限乘积集补齐八份有限坍缩证明

以下八份 `FiniteTrivial.lean` 已通过 Lean 4.33.1 串行编译和公理检查。每份独立包含有限性引理和完整等式推导，结论为 `[Finite G]` 下原方程推出 Equation2。云端有限目标验收仍待部署入口。

| 方程 | 对偶 |
|---|---|
| [Equation21714](../../../Equation21714/FiniteTrivial.lean) | [Equation24200](../../../Equation24200/FiniteTrivial.lean) |
| [Equation21864](../../../Equation21864/FiniteTrivial.lean) | [Equation24199](../../../Equation24199/FiniteTrivial.lean) |
| [Equation21865](../../../Equation21865/FiniteTrivial.lean) | [Equation24197](../../../Equation24197/FiniteTrivial.lean) |
| [Equation21866](../../../Equation21866/FiniteTrivial.lean) | [Equation24201](../../../Equation24201/FiniteTrivial.lean) |

四条代表方程都可通过代入变量得到

```text
x = (y ◇ (y ◇ x)) ◇ (x ◇ (x ◇ y)).
```

在 `G × G` 上定义

```text
F(x,y) = (x ◇ (x ◇ y), y ◇ (y ◇ x)),
H(u,v) = (v ◇ u, u ◇ v).
```

上述等式及交换变量后的等式给出 `H(F(x,y)) = (x,y)`，所以 F 单射。G 有限时，`G × G` 有限，因此 F 满射，进而 `F(H(u,v)) = (u,v)`。取分量得到新的运算恒等式

```text
(x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ x)) = y.
```

这个有限性步骤是关键；只对 G 上的一元映射做搜索时没有得到它。[FinitePairInverse.lean](FinitePairInverse.lean) 给出了 Lean 证明，同时证明平方映射双射及两元素可交换时必相等。

将新恒等式与四条原方程分别结合，Prover9 给出了长度为 18、74、37、13 的推导。搜索结果经过逐步等式重放，最终由 Lean 检查；Prover9 不作为受信任的证明工具。对偶通过相反运算转移，四变量的 Equation21866／Equation24201 保留全部四个量词。

八份有限定理的公理依赖均仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集；最高采样 RSS 为 1438.80 MiB。逐题成功记录与源码 SHA-256 在上一级目录对应的 `Equation*.json`、`.log` 中。[search-summary.json](search-summary.json) 保存搜索输入、完整输出哈希及四份完整证明摘录。

原表编号保留为 20.3，表示 Blueprint 的原始分类。本仓已解决这八条的有限侧；本报告不声称已完成其非平凡无限模型侧，也不把本地检查计为极光云接受。
