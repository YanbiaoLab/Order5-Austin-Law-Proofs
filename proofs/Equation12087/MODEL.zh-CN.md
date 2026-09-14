# Equation12087 的非平凡无限正规树模型

2026-09-14：完整构造与证明完成，已从空构建目录通过 Lean 4.33.1 本地核验。对偶 Equation33884 也有独立的精确目标包装证明。后续本条与对偶的独立单文件证书均已获远端 Judge **ACCEPTED**，见[回执审计记录](../validation/eq12087-formal/JUDGE.md)。

所证明的原式是

\[
x=y\diamond\bigl(((y\diamond x)\diamond z)\diamond(x\diamond z)\bigr).
\]

这里是所有载体元素、所有三元组上的全称恒等式，不再带未证明的查询排除条件或归纳假设。

## 模型是什么

先定义有限树类型 T，具有以下构造子：

- `atom(n)`：自然数标号的原子；
- `s(a)`：平方树；
- `p(a,b)`：普通配对树；
- `c(y,x,z,l,r)`：返回代码，记录返回键 y、目标 x、列 z，以及实际乘法输入 l,r。

树的 `origin` 记录实际左右来源：平方树为 (a,a)，普通配对为 (a,b)，代码树为 (l,r)。代码字段不被擅自当作实际乘法；正规性会要求来源等式真正成立。

在全部 T 上同时定义总乘法 `mul(a,b)` 和部分右列逆 `inverse(b,out)`。后者寻找满足 `a*b=out` 的左输入 a。它们按树大小构成的自然数秩下降递归，具体秩是

```
rankM(a,b)=3*max(size(a),size(b))+2，
rankI(a,b)=3*max(size(a),size(b))+1。
```

完整的可执行定义见 [TraceBasic.lean](Lean/TraceBasic.lean)。乘法规则概要如下：

1. 相等输入 a,a 生成 s(a)。
2. 如果右输入是以左输入为返回键的代码，返回其目标。
3. 否则，依次检查左右实际来源，通过已在较小秩上定义的乘法与部分逆，寻找共同列编码轨迹。找到就生成相应代码树，找不到就生成普通配对。

左右编码分支有确定的优先次序；查询均保留严格的秩限制。这个定义没有使用待证明的恒等式作为判定器。它先独立给出总运算，再证明恒等式。

实际模型载体为

\[
G=\{t\in T:\operatorname{NF}(t)\}.
\]

[TraceNormal.lean](Lean/TraceNormal.lean) 归纳定义 NF：原子正规；正规树的平方正规；配对和代码的所有字段须正规，并且该节点确实等于记录的左右输入之乘积。已证明 NF 对 mul 封闭，因此 `normalMul` 是 G 上的总二元运算。

## 为什么它无限且非平凡

映射 `normalAtom : Nat → G` 将 n 送到正规原子 atom(n)。两个这样的元素相等，会由构造子的单射性推出自然数标号相等。因此这是一个显式自然数单射，且 atom(0)≠atom(1)。

无限性、非平凡性和原式使用同一载体、同一运算。[TraceFullSource.infinite_model](Lean/TraceFullSource.lean) 把三项结论封装在一个无条件存在定理中；[InfiniteModel.lean](InfiniteModel.lean) 另证明与索引原式完全对应的 `Goal`。

## 完整原式如何闭合

代码树的设计保证：当中间乘积走编码增长时，最终返回会恢复 x。困难是排除可能破坏这一轨迹的中间返回。

证明先将危险情况归约为两类查询，再证明第二类查询排除足以推出第一类和完整原式。第二类循环的记号为

```
g=u*a，q=g*k，v=a*k，w=a*q，e=w*v，y*e=u。
```

按高度进行强归纳，历史证明先后关闭 q 返回、v 的高头部、增长中间项、不同返回键等情况；之后锁定 w=a、g<v。共同列的来源排除 s 与 v 同高；第 39 批完整排除 s>v。

最后的低列 s<v 由本批四个模块闭合：

1. [TraceLowColumnTailHeight](Lean/TraceLowColumnTailHeight.lean) 证明 `B*t=v` 的列 t 必须恰在 v 下一层。若更低，来源对齐会同时要求一段正规返回至少有三层间隔、又只有两层，矛盾。
2. [TraceLowColumnCrossLadder](Lean/TraceLowColumnCrossLadder.lean) 展开 `a*v=e` 和 `g*t=s`，构成新的交叉返回链。支配排除先证明 e*s=a 必须返回，再迫使 g=e。
3. [TraceLowEqualHeadCycle](Lean/TraceLowEqualHeadCycle.lean) 利用 g=e=u*a 与外层 y*e=u，得到 height(e)≤height(a)+1。令 A=a*a、B=A*e、H=a*e、F=H*B，则 B 比 a 高两层、F 比 B 高一层。重复头部返回链的长尾经过三次旋转，使第二键支配所有头部；短尾则先以交换返回的共同来源排除增长，再形成另一个支配矛盾。两种尾部都关闭。
4. [TraceFullSource](Lean/TraceFullSource.lean) 将各段接回 `NormalSameKeyMiddleStep`，正式提供先前条件定理缺失的证明，最后得到无条件 `full_source_law`。

所以早期记录中“仍需高度归纳”“只在归纳假设下成立”的限制已经在最终端点中消除。早期文件中的注释描述各模块当时的局部作用；判断最终状态应查看 `TraceFullSource` 和正式目标包装，不能把历史检查器固定打印的候选提示当作最终结论。

## 历史复盘与其他成功方程的经验

历史复盘保留了直接重写、平方周期、线性方案、部分关系见证等历史尝试。它们的失败或有界停止，只限制当时的方案，未被扩大成“原式不存在模型”。

本次真正起作用的是：把代码节点的实际来源保留下来，在同一棵树出现两条轨迹时同时对齐，然后把结果组织成能整体旋转、下降的返回链。只增加局部高度不等式往往仍会得到抽象 SAT；证明必须使用全称的来源唯一性和链支配不变量。

其他模型提供了不同层面的启发：12234 的关系相容性与五步循环排除支持联合分析整个轨迹；10222 的完整分类提醒我们最终必须覆盖所有增长／返回分支；12073 的商代数重写是备选，但本题未依赖未经完成的重写补全。18137 后来成功使用列关系的包含性，提供了值得保留的另一种构造路线，但本题最终完成的是此前的正规树候选，没有把其定理直接套用为本题证明。

历史上 71 模块、208 端点是局部成果；最终核心为 **125 模块、311 个审计端点**。数量仅说明证据规模，完整性的决定性证据是无条件原式和显式单射同时通过核验。

## 对偶与验证边界

在同一载体上定义反向运算 a◇ᵈb=b◇a。对原式交换相应变量后，得到索引中的精确对偶

\[
x=((y\diamond^d x)\diamond^d(y\diamond^d(x\diamond^d z)))\diamond^d z.
\]

[Equation33884/InfiniteModel.lean](../Equation33884/InfiniteModel.lean) 已独立检查这一目标及非平凡性；自然数单射保持相同。

验证从空目录逐个编译 125 个核心模块，再分别编译两条方程的目标定义和模型包装，共 **129 次模块构建**；没有复用此前研究目录的 `.olean`。所有端点公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集；无 `sorry`、`admit`、自定义公理或 `native_decide`。

使用串行 `-j1 -M256`、384 MiB RSS 停止线、单模块 120 秒上限。这里记录原模块化本地核验；后续远端验收单独记录于 [JUDGE.md](../validation/eq12087-formal/JUDGE.md)。完整源码哈希、依赖、命令、公理及日志见[验证报告](../validation/eq12087-formal/README.md)和 [summary.json](../validation/eq12087-formal/summary.json)。

```sh
python3 proofs/validation/eq12087-formal/portable.py --rebuild
```
