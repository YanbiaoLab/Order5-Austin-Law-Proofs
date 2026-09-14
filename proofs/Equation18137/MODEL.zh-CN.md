# Equation18137 的非平凡无限树模型

2026-09-14：已构造并通过 Lean 4.33.1 本地核验，随后通过远端 Judge **ACCEPTED**。

原式是
\[
x=(y\diamond x)\diamond\bigl(z\diamond((x\diamond z)\diamond z)\bigr).
\]

模型载体是**所有有限二叉树，叶子用自然数标号**。不取商，不要求正规形，
也不把运算限制在测试过的项上。运算由唯一关系解码定义；不存在解码结果时，
就把两个输入配成一棵新树。

## 1. 载体与运算的完整定义

记叶子为 \(A_n\)，配对构造子为 \(P(a,b)\)，全体树为 \(\mathcal T\)。
对每棵树 b 定义两个集合 \(R_b,C_b\)：
\[
C_b=\{P(t,b):t\in\mathcal T\}\cup R_b.
\]
这里 C 是辅助列关系：它包含所有真实列像，也保留可能被解码替换的原始配对轨迹。
不要求 C 等于最终运算的实际列像；证明只使用包含关系。

若 b 不能写成 \(P(z,P(v,z))\)，令 \(R_b=\varnothing\)。若
\(b=P(z,P(v,z))\)，令
\[
R_b=\{x:v=P(x,z)\}\ \cup\
\begin{cases}
C_v,&v\in R_z,\\
\varnothing,&v\notin R_z.
\end{cases}
\]

z、v 都是 b 的真子树，因而这是有限结构上的递归定义。
Lean 使用等价的互归纳关系 `Column`、`Target`；
`code_trace_iff` 证明它与最初的运算轨迹规则精确对应。

定义
\[
\operatorname{Code}(a,b,o)\quad\Longleftrightarrow\quad
o\in R_b\ \text{且}\ a\in C_o.
\]
已证明：对于任意 a、b，满足这个条件的 o **至多一个**。于是定义总运算
\[
a\diamond b=
\begin{cases}
o,&\operatorname{Code}(a,b,o),\\
P(a,b),&\text{不存在这样的 }o.
\end{cases}
\]

Lean 中通过经典选择定义该运算，随后证明所有解码规则都被满足。
这是一项已定义并已验证的数学运算；Python 查询器提供可执行探索版本，
其有限对照检查没有被用来替代 Lean 证明。

## 2. 为什么解码结果唯一

设 `size(t)` 为树的结点数；叶子的 `rank` 为 0，
\(\operatorname{rank}(P(a,b))=\operatorname{size}(b)\)。互归纳证明给出
\[
o\in C_b\Longrightarrow \operatorname{rank}(o)\le\operatorname{size}(b),
\qquad
o\in R_b\Longrightarrow \operatorname{rank}(o)<\operatorname{rank}(b).
\]
由此证明解码容器的右子树不能再充当解码容器：
\[
R_{P(a,b)}\ne\varnothing\Longrightarrow R_b=\varnothing.
\]
然后对 `Column`、`Target` 的推导互归纳，得到
\[
x,y\in C_b,\quad u\in C_x\cap C_y\Longrightarrow x=y.
\]
这正是“从 b 到 u 的两步辅助列关系路径，中间点唯一”。结合 \(R_b\) 的单点／继承结构，
推出 `Code(a,b,x)` 与 `Code(a,b,y)` 必须给出 x=y。

这些结论已在 [TreeBounds.lean](TreeBounds.lean) 和 [TreeUnique.lean](TreeUnique.lean)
核验，不依赖经典选择或额外公理。

## 3. 为什么完整原式成立

证明还排除了同一列像中的一条额外边：
\[
x,y\in C_b\Longrightarrow y\notin C_x.
\]
利用这个性质和右子树障碍，对任意 x、z，令 \(v=x\diamond z\)，已证明
\[
v\diamond z=P(v,z),\qquad z\diamond(v\diamond z)=P(z,P(v,z)).
\]
这没有要求第一次 \(x\diamond z\) 是普通配对；它可以已经解码。
同样，\(y\diamond x\) 也可以已经解码。

对于 \(u=y\diamond x\)，真实运算轨迹总有 \(u\in C_x\)。
定义中的两种分支又保证 \(x\in R_{P(z,P(v,z))}\)。所以
\[
\operatorname{Code}\bigl(u,P(z,P(v,z)),x\bigr),
\]
最终一次乘法必定恢复 x。这证明了所有树、所有三元组上的完整原式。
对应无条件定理是 [TreeModel.lean](TreeModel.lean) 中的 `source_law_explicit`。
早期 `template_law` 的全部假设在这个文件中得到证明。

## 4. 无限性与必要碰撞

映射 \(n\mapsto A_n\) 是单射，因此载体无限；\(A_0\ne A_1\) 给出非平凡性。
`infinite_model` 将同一个载体、同一个运算的原式和自然数单射封装在一个存在定理中。

模型保留了历史障碍要求的碰撞。例如令
\[
a=A_0,\quad b=A_1,\quad d=P(a,P(P(a,a),a)).
\]
则 \(R_d=\{a\}\)，因此
\[
P(a,a)\diamond d=a=P(b,a)\diamond d,\qquad P(a,a)\ne P(b,a).
\]
这解释了为什么该构造没有落入已排除的全局右消去模板。

## 5. 验证与复现

- 四个模块从空目录逐一编译，全部指定端点通过公理审计。
- 将四模块展平成 [InfiniteModel.lean](InfiniteModel.lean)，在另一个空目录独立编译。
  此目录没有任何 `Tree*.olean`，也没有此前的有限性或结构障碍模块。
- 精确目标 `Goal` 同时要求原式成立和 `¬∀x y,x=y`；另审计任意自然数上的单射定理。
- 最终模型定理只使用 `propext`、`Classical.choice`、`Quot.sound`；
  没有 `sorryAx`，没有额外假设。原子单射本身无公理依赖。
- 已通过远端 Judge，见[原始回执](../validation/aurora/Equation18137/latest.json)。
  远端目标是精确的 `Equation18137 ↛ Equation2`；自然数单射另在本地单列审计。

```sh
python3 proofs/validation/eq18137-formal/verify.py
```

完整命令、源码哈希与编译日志见
[验证报告](../validation/eq18137-formal/README.md) 和
[summary.json](../validation/eq18137-formal/summary.json)。

## 6. 从复盘到构造的实际转折

E7587 的多键经验提示保留碰撞；E12234 的关系定义方法允许先证明相容性。
真正使本题闭合的是进一步把无限键集合压缩为列像，并证明两步列像路径唯一。
最后的证明允许载体包含所有原始树，无须额外正规形条件。

小范围关系闭包与独立解释器帮助发现这个结构；成功结论最终来自全称 Lean 证明，
而不是这些有限实验。
