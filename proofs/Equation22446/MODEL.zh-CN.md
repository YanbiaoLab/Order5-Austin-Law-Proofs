# E22446 的非平凡无限模型

2026-09-15。完整模型已通过 Lean 4.33.1 核验，单文件证书随后获远端 Judge **ACCEPTED**。
原式为

\[
x=(y*(x*x))*((x*z)*z).
\]

[InfiniteModel.lean](InfiniteModel.lean) 是模块化入口；
[JudgeSubmission.lean](JudgeSubmission.lean) 是实际提交的完整单文件证书。
结合已有 [FiniteTrivial.lean](FiniteTrivial.lean)，E22446 的 Austin 律性质已获形式化证明。

载体由正规三色有限树组成。叶子带自然数标签，每个节点的根颜色取 0、1、2。
`P(a,b)` 是零色配对，`S` 只循环旋转根颜色，因此 `S³=id`。
这里不要求 `S` 是乘法自同构。

[Relations.lean](Lean/LineageSyntax/Relations.lean) 独立定义像、列和祖先三个互递归证书关系。
它们由六条像规则、三条列规则和两条祖先规则生成，不假设待证的原方程。
祖先链在 `Image(a,b)` 处可以延伸到 `S²P(a,b)`，记录返回后的来源。
[Decoder.lean](Lean/LineageSyntax/Decoder.lean) 给出矩形、逆双重、像返回和循环返回四类守卫。
所有守卫输出均为输入的旋转子树，严格小于新配对。

正规树的孩子也正规，且每个配对的孩子之间均无返回守卫。
对正规输入，乘法在有守卫时取其返回值，否则产生原始配对。
[Evaluation.lean](Lean/LineageSyntax/Evaluation.lean) 用 `Classical.choose` 定义全函数，
并证明其值仍正规；最终唯一性定理保证不同守卫给出同一结果。

原方程的证明分为三个可分别检查的部分。对正规 `x,y,z`，令
`a=y*(x*x)`、`b=(x*z)*z`，则有：

1. 平方公式 `x*x=Sx`。
2. 列覆盖 `Column(x,a)` 和完整双右像覆盖 `Image(x,b)`。
3. 目标 `x` 是某个输入的旋转子树，故 `Guard(a,b,x)`；返回唯一性给出 `a*b=x`。

[FullImageCoverage.lean](Lean/LineageSyntax/FullImageCoverage.lean) 通过联合排除像／列三角形，
处理两次乘法中的全部返回分支。
最后的 [PrincipalUnique.lean](Lean/LineageSyntax/PrincipalUnique.lean) 按目标根颜色分类，
结合共同祖先的查询唯一性及严格大小下降，证明一般矩形目标唯一，从而关闭全部守卫唯一性。
[CanonicalInduction.lean](Lean/LineageSyntax/CanonicalInduction.lean) 的联合归纳先处理像，
再处理同大小列；像传递调用更小的列分支，列逆像调用已完成的同层像分支。
最终 [Model.lean](Lean/LineageSyntax/Model.lean) 没有未传入的唯一性或 Source 前提。

无限性见证十分直接。取一个零色叶子 `e`，令

\[
t_0=Se,\qquad t_{n+1}=P(e,t_n).
\]

[CleanTower.lean](Lean/LineageSyntax/CleanTower.lean) 证明每个 `t_n` 正规且恰有 `n` 个配对节点。
因此 `normalTower` 是自然数到同一模型载体的单射；特别地，`t_0≠t_1`。
原式、非平凡性和单射在 `Equation22446Lineage.infinite_model` 中合并。

研究中的关键修正是：旧守卫系统虽已具备覆盖，仍被五节点正规平方的多返回冲突否定。
新系统加入祖先列、逆像循环及返回后继；新系统中直接头部界又曾失效，
最后用共同祖先界和按颜色分类的大小归纳完成证明。
这说明正规载体无限、有限测试无冲突、甚至全称覆盖，都不能替代最后的返回唯一性。

其它方程的启发来自实际来源追踪、局部冲突分类和联合归纳。
本题只证明所需的矩形目标唯一性，不强加全部实际列路径的中间点唯一性。
交付模型也不依赖 Python 原型与 Lean 乘法之间尚未形式化的等价性。

验证见 [本机核验](../validation/eq22446-infinite-model/README.md)和
[远端验收](../validation/aurora/Equation22446/README.md)。
单射端点不依赖任何公理；最终模型端点只用 `propext`、`Classical.choice`、`Quot.sound`。
本次只归档 E22446。E22591 的独立 Lean 包装与验收记录仍需另行补入。
