# 剩余表 20.3 方程的乘积集搜索

在已补齐八份有限证书后，对其余代表方程中的七条分别测试八种对称乘积映射 `F(x,y) = (T(x,y), T(y,x))` 的单射性，并用找到的有限逆映射做坍缩搜索。每次 Prover9 内存上限 64 MiB；单射性检查限 1 秒，最终坍缩检查限 5 秒，全程串行。

[summary.json](summary.json) 记录 56 次单射性检查与 7 次坍缩搜索、完整输出哈希及终止状态。只有 Equation20911 得到两条乘积映射单射性线索，尚未转为 Lean；全部七次搜索均未产生新的 Equation2 证明。有限时间／内存内未找到证明，不表示存在非平凡有限模型。

Equation22446 的搜索使用平方映射的有限逆。其前提现在已由 [FiniteStructure.lean](../../../Equation22446/FiniteStructure.lean) 独立形式化：源方程在任意模型上推出平方映射单射，在有限模型上推出平方映射双射。单射性定理不依赖任何公理；双射性只使用通常的 `propext`、`Classical.choice`、`Quot.sound`。证据见 [Equation22446-structure.json](Equation22446-structure.json)。这些结构引理尚不能推出 Equation2，故未创建本条的 `FiniteTrivial.lean`。

本批跳过 Equation13102：其已归档的上游说明给出了非平凡无限的 surjunctive 模型，说明单靠“代数定义映射单射则满射”的路线不足以排除所有非平凡模型。仍需其他有限性论证；跳过此策略不表示该方程已解决。
