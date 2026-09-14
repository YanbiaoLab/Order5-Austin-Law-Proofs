**Equation17286 / Equation28626：非平凡无限树模型与成功复盘**

2026-09-14。E17286 的完整原式、非平凡性和显式自然数单射已通过 Lean 4.33.1；精确对偶 E28626 也通过独立证书检查。结合已有有限平凡性证明，两式现已确认为 Austin 律。两份独立证书随后均获远端 Judge **ACCEPTED**，见[远端验收记录](../validation/eq17286-formal/JUDGE.md)。

\[
x=(y\diamond x)\diamond\bigl(z\diamond(z\diamond(x\diamond z))\bigr).
\]

**模型定义。** 载体是自然数标号的全部有限二叉树，构造子为叶子 \(A_n\) 和配对 \(P(a,b)\)。不取商，也不要求正规性。以下关系由四条规则互归纳生成：

\[
\begin{aligned}
&\mathcal C(b,P(a,b)),\\
&\mathcal T(b,o)\Longrightarrow\mathcal C(b,o),\\
&\mathcal T(P(z,P(z,P(x,z))),x),\\
&\mathcal T(z,v)\land\mathcal C(v,x)
 \Longrightarrow\mathcal T(P(z,P(z,v)),x).
\end{aligned}
\]

\(\mathcal C\) 包含实际右列像，也保留原始配对轨迹；无需证明它恰好等于实际列像。定义

\[
\operatorname{Code}(a,b,o)\iff\mathcal T(b,o)\land\mathcal C(o,a).
\]

已经证明每对 a、b 最多有一个 Code 目标。乘法定义为：有 Code 时返回其唯一目标；没有时返回 P(a,b)。Lean 使用经典选择将它定义为总函数。关系与唯一性均在文件内证明，没有把外部搜索结果当作公理。[TreeSchema.lean](TreeSchema.lean)、[TreeModel.lean](TreeModel.lean)

**为什么解码唯一。** 令 size 为树节点数，叶子 rank 为 0，\(\operatorname{rank}(P(a,b))=\operatorname{size}(b)\)。首先互归纳证明

\[
\mathcal C(b,o)\Longrightarrow\operatorname{rank}(o)\le\operatorname{size}(b),
\qquad
\mathcal T(b,o)\Longrightarrow\operatorname{rank}(o)<\operatorname{rank}(b).
\]

这里没有声称解码结果的整个树大小小于输入；继承规则可以保留任意大的左子树。[TreeBounds.lean](TreeBounds.lean)

随后按 b 的大小，同时证明两项全称性质：

\[
\mathcal C(b,x),\mathcal C(b,y),\mathcal C(x,u),\mathcal C(y,u)
\Longrightarrow x=y,
\]

\[
\mathcal C(b,x),\mathcal C(b,y)\Longrightarrow\neg\mathcal C(x,y).
\]

第一项是两步路径的中间点唯一；第二项排除同一列关系中的三角形。继承目标形成较小 v 的整个 \(\mathcal C_v\)，因此可以直接使用对 v 的归纳假设。普通配对与继承目标的混合情况依靠一个新的递减步骤：若容器和它的右子树都能解码，就能在严格更小的树上制造三角形，与归纳假设矛盾。

于是得到 `target_right_empty`，再将两步路径唯一性用于同一代码容器的目标，得到无条件的 `code_output_unique`。[TreeGeometry.lean](TreeGeometry.lean)

**为什么完整原式成立。** 第一次乘法 \(v=x\diamond z\) 可以配对，也可以已经返回，但始终有 \(\mathcal C(z,v)\)。另外两次左乘必须保持配对：

\[
z\diamond v=P(z,v),\qquad
z\diamond P(z,v)=P(z,P(z,v)).
\]

第一项依靠列关系不存在三步循环。若 \(z\diamond v\) 解码为 o，就有
\(\mathcal C(z,v),\mathcal C(v,o),\mathcal C(o,z)\)，恰好形成这种循环。
三步循环的排除使用秩下降及如下较弱性质：解码目标不能经一步列关系到达容器的右子树。

第二项依靠三角形排除。若 P(z,v) 可以作为代码容器，则必有 \(v=P(z,w)\) 且 \(\mathcal C(z,w)\)。又有 \(\mathcal C(z,v)\) 和 \(\mathcal C(w,P(z,w))\)，形成被排除的三角形。

最后令 \(u=y\diamond x\)，实际运算保证 \(\mathcal C(x,u)\)；无论 v 的第一次乘法是否已经返回，关系规则都保证

\[
\mathcal T(P(z,P(z,v)),x).
\]

因此 `Code(u,P(z,P(z,v)),x)`，最终乘法返回 x。`source_law_explicit` 无额外假设地证明任意三棵树上的 E17286；研究阶段 `conditional_source` 的所有前提已在此实际运算上补齐。

**无限性与碰撞。** 映射 \(n\mapsto A_n\) 是单射，\(A_0\ne A_1\) 给出非平凡性。`infinite_model` 将同一载体、同一运算的原式与自然数单射封装在一个存在定理中。

模型保留了历史障碍所要求的碰撞。例如，取不同叶子 a、b，令 \(q=P(a,P(a,P(a,a)))\)。由关系规则可得

\[
P(a,a)\diamond q=a=P(b,a)\diamond q,\qquad P(a,a)\ne P(b,a).
\]

所以该运算没有错误地落入全局右消去模板。它也无需平移等变、整数高度或有限颜色参数，因此与历史有界取整族排除完全相容。

**这次从哪里取得突破。** [上一轮复盘](ResearchRetrospective-2026-09-14.md)辨认出 E18137 与 E17286 的差异只是解码器的一处括号，提出移植辅助列关系的方案。有限实验没有发现冲突，但真正的障碍是 E18137 的旧引理
“解码目标不能等于容器右子树”在新关系里为假：

\[
\mathcal T(z,v)\Longrightarrow\mathcal T(P(z,P(z,v)),P(z,v)).
\]

这个反例是正确的，现仍保留在 TreeSchema 中。突破不是否认反例，而是发现原式证明不需要那么强的引理。替代它的性质为：

\[
\mathcal T(P(a,b),o)\Longrightarrow\neg\mathcal C(o,b).
\]

目标可以等于右子树，因为列关系本身无自环。将三角形排除与路径唯一性按树大小共同归纳，又打破了“先排除嵌套容器才能证明唯一性、先有唯一性才能排除嵌套容器”的证明依赖环。之后三步循环排除使两次中间左乘闭合。

其它方程的成功经验确实改变了这次构造：E18137 提供辅助列关系和全部树载体；E21866 提醒我们只证明实际需要的形状不变量；E12087 强调覆盖首次乘法已返回的真实轨迹。E10222 的全局唯一列逆与本题障碍不相容，因此没有照搬。历史中大量 SAT 与斜率工作仍是有效的受限模型排除，但最终构造来自不同的树关系结构。

**精确对偶。** 定义 \(a\diamond^d b=b\diamond a\)，原式取参数 x、z、y，得到

\[
x=(((y\diamond^d x)\diamond^d y)\diamond^d y)\diamond^d(x\diamond^d z).
\]

同一个自然数单射保留。[Equation28626 的独立证书](../Equation28626/InfiniteModel.lean)包含完整构造和精确对偶目标，不依赖 E17286 的已编译模型。

**验证。** 四个核心模块从空目录编译；随后分别在另外两个空目录编译两份精确题面和两份展平证书，共八个编译单元。核验同时检查题面、非平凡性、自然数单射、源码哈希、日志哈希和公理清单。证明只使用 `propext`、`Classical.choice`、`Quot.sound`；结构分离定理与原子单射无需公理。

首次尝试完整 Init 导入触及外部停止线，已中止并改用最小依赖。展平证书初次触及 128 MiB 的 Lean 内部限制，关闭异步 elaboration 后在原资源上限内通过。最终八单元检查约 1.21 秒，采样峰值约 119.70 MiB；未复用旧 `.olean`；这段本地构建没有调用远端服务。后续远端提交另见上述验收记录。

```sh
python3 proofs/validation/eq17286-formal/verify.py
python3 proofs/validation/eq17286-formal/audit.py
```

[验证报告](../validation/eq17286-formal/README.md)、[逐项记录](../validation/eq17286-formal/summary.json)、[E17286 独立证书](InfiniteModel.lean)。已有有限证书本轮只核对源码与历史记录，不重跑其较大的 Mathlib 构建。
