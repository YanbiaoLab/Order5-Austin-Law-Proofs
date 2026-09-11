# Equation10222／Equation35836：非平凡无限模型

2026-09-10：两条精确原式、非平凡性及显式 Nat 单射均已通过 Lean 4.33.1 内核核验。
2026-09-11 本批仅归档指定的十条完整 Austin 律证明；合并后库存为 110 条有模型。
本批只作本地验证，没有远程提交。

原式分别为

```
E10222: x = y ◇ ((x ◇ y) ◇ ((z ◇ y) ◇ y))
E35836: x = ((y ◇ (y ◇ z)) ◇ (y ◇ x)) ◇ y
```

## 构造

有限树由 `atom(n)`、一元构造子 `S(a)`、`U(a)` 和二元构造子 `P(a,b)` 组成。
`S` 记录平方，`U` 提供逐元素的右固定参数，即 `a ◇ U(a) = a`。
不同自然数原子保持不同；树的大小不对自然数标签设限。

[UnitBasic.lean](../proofs/Equation10222/Lean/Austin10222/UnitBasic.lean) 同时定义总乘法
`mul(a,b)` 和可计算的部分逆 `inverse(b,out)`。
所有互递归查询严格减小两个输入的树大小之和，Lean 直接检查终止性。
`inverse(b,out) = some(a)` 表示在右乘 b 的列中，out 的原像为 a。
乘法通常保留为 `P(a,b)`，在平方、固定参数和解码模式中约化；例如

```
a ◇ a = S(a)
a ◇ U(a) = a
U(a) ◇ S(a) = a
S(U(a)) ◇ a = U(U(a))
```

配对解码分支同时核对实际乘法边和部分逆查询。完整的优先顺序以源码为准；
这些局部等式本身不代替完整原式证明。

载体不是任意未经约化的树，而是正规树子类型 `Carrier = {t : T // NF(t)}`：

```
NF(atom(n)) = True
NF(S(a)) = NF(a)
NF(U(a)) = NF(a)
NF(P(a,b)) = NF(a) ∧ NF(b) ∧ mul(a,b) = P(a,b)
```

[UnitNormal.lean](../proofs/Equation10222/Lean/Austin10222/UnitNormal.lean) 证明乘法在这个载体上封闭，
并定义 `embed(n) = atom(n)`，证明 `embed` 为单射。因此载体无限。

## 完整原式为何成立

首先证明部分逆的可靠性与完备性：

```
inverse(b,out) = some(a)  →  mul(a,b) = out
inverse(b,mul(a,b)) = some(a)
```

这两条在全部树上成立，并推出每个右乘映射都是单射。
像的大小界限、互斥性和解码键冲突排除保证部分逆不会选错分支。

对于正规右输入 b，[UnitDouble.lean](../proofs/Equation10222/Lean/Austin10222/UnitDouble.lean)
证明二次右乘的完整分类：要么 `b = U(a)` 且 `a ◇ b = a`，
要么 `(a ◇ b) ◇ b = P(a ◇ b,b)`。
这个分类只要求 b 正规，对 a 没有额外正规性假设。

由此对原式的中间二次右乘分情况：普通配对分支再分为配对、平方和固定参数解码；
固定参数分支使用右乘 `U(a)` 的四类输出。每种情况都由部分逆恢复 x。
[UnitLaw.lean](../proofs/Equation10222/Lean/Austin10222/UnitLaw.lean) 的
`source_of_normal_middle` 证明任意树 x、z 和任意正规树 y 的完整等式，
`carrier_source` 将其限制到封闭载体。`carrier_dual` 使用反向乘法证明 E35836。
`carrier_nontrivial` 证明 `embed(0) ≠ embed(1)`。

## 验证和复现

九个核心模块、两条精确 Goal、两份模型包装和两份独立单文件证书，共 **15 个编译单元全部通过**。
两份独立证书只导入 Lean 标准库，包含题面、全部模型定义和证明；检查时未使用项目的已编译模块。
最终定理没有 `sorryAx` 或自定义公理，只依赖标准 `propext`、`Quot.sound`。
证明不含树高、标签、搜索次数的有限上界，Python 采样不属于证明的信任基础。

串行单线程验证采用 `-M256`，外部 RSS 停止线 384 MiB，每单元时间上限 120 秒。
本次累计编译用时 10.169 秒，周期采样峰值 243.19 MiB；采样峰值不是严格内存上界。

上述数字来自原验证记录；本次不重新编译。归档核对命令见[本批报告](../proofs/validation/2026-09-11-ten-austin/README.md)。

[核验清单](../proofs/validation/eq10222-formal/summary.json) 绑定每份源码、日志及输出模块哈希。
独立证书：[E10222](../proofs/validation/eq10222-formal/Equation10222/certificate.lean)、
[E35836](../proofs/validation/eq10222-formal/Equation35836/certificate.lean)。
