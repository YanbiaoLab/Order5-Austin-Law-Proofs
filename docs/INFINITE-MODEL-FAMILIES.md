# 已归档无限模型的构造家族与方程覆盖

审计日期：2026-09-17。依据 [proofs/index.json](../proofs/index.json)（更新日 2026-09-15）、对应 Lean 定义、补充证书和模型说明。

**按载体限制、运算定义和核心证明方法，本次整理为 9 个构造家族，去重覆盖 122 条方程。** 这是本次采用的分类，不是互不同构的无限代数数量。同一个家族内部可以有多套不同的具体规则。

计数规则：每条精确方程计一次；原运算和相反运算归入同一构造家族。只计已归档证书确认的应用，不表示这些模型实际满足的全部方程。一个方程有多种模型时保留跨家族覆盖。

| 构造家族 | 已登记覆盖方程数 | 每题选一个代表后的覆盖数 |
|---|---:|---:|
| 自由树上的 Step/Code 关系解码 | 42 | 42 |
| 自由树上的直接解码或递归逆查询 | 26 | 24 |
| 有限模式规则的正规树 | 16 | 14 |
| 终止汇合重写、商树与规范形 | 14 | 14 |
| 有限颜色循环的正规树 | 6 | 6 |
| 带辅助节点和部分逆的正规树 | 4 | 4 |
| 行像关系树 | 10 | 10 |
| 辅助列关系与目标关系树 | 4 | 4 |
| 有理数分段线性运算 | 4 | 4 |
| 合计 | 126 次覆盖，122 条去重方程 | 122 |

“每题选一个代表”优先采用索引中的 `explicit_infinity_proof`，否则采用 `infinite_model_proof`，仅用于给出可加总的清单，不抛弃其他历史构造。

索引中 **94 条**单列了显式无限性证明；另 **28 条**使用无限归纳树载体，但未单列 Nat 单射或 Infinite 定理。这里沿用整个模型库存口径，不把 122 说成 122 份独立无限性定理。

## 同一具体构造覆盖多个对偶对

- [E21866 四规则行像模型](../proofs/Equation21866/Lean/Austin21866/Model.lean)：**8 条**，即 E21714/E24200、E21864/E24199、E21865/E24197、E21866/E24201。E21714、E21864、E21865 由同一更一般恒等式代入得到，另四条用相反运算。
- [Le Floch 有理数分段模型](../proofs/Equation13102/InfiniteModel.lean)：**4 条**，即 E13102/E33273、E20911/E25087。
- 代表清单中其余按每个构造对应一对列出，共 55 组、110 条；不据此断言这些构造两两不同构，也不声称一组最多只能满足两条方程。

因此，可以用 **57 组代表构造应用**覆盖 122 条（55×2+8+4）。这不是全部历史模型按相等或同构去重后的精确数量。历史证书还保存了其他构造或同家族的不同呈示。

## 为什么覆盖数有重叠

- **E5833/E40070**：历史主证书直接递归定义 op；补充证书采用互归纳 Step/Code。
- **E6878/E39126**：历史主证书使用 e/k/p/q/r 正规树及有限优先规则；补充证书采用全部 e/k/p 自由树及递归解码器。
- 商树与规范形表示归入同一个重写家族；同一家族中的不同历史证明不重复增加该家族的方程覆盖数。

## 各类的具体含义

- **Step/Code**：在全部构造树上定义运算轨迹和解码关系；证明解码输出唯一，命中时返回输出，否则构造原始配对，部分模型另有平方分支。参见 [两步轨迹树](../proofs/validation/aurora/Equation5833/certificate.lean)与 [平方标记解码](../proofs/Equation12234/InfiniteModel.lean)。
- **直接解码或递归逆查询**：通过明确模式、部分逆、像查询或良基递归定义运算；取全部构造树。包含多键列表、五函数查询等不同具体模型，不把它们当作同一个运算。参见 [E7587](../proofs/Equation7587/InfiniteModel.lean)、[E8485](../proofs/Equation8485/InfiniteModel.lean)、[E6878](../proofs/validation/aurora/Equation6878/certificate.lean)。
- **有限模式规则的正规树**：给定有限 Code/返回规则，取满足 NF 的树，并证明运算封闭；E6878 历史版本还含 q/r 辅助构造子和规则优先级。
- **重写、商树与规范形**：增加辅助构造符，证明重写终止和汇合，通过商树或唯一规范形解释乘法。三元载荷模型各有自己的规则，不能混成一个模型。参见 [三元载荷模型](../proofs/validation/aurora/Equation13764/certificate.lean)、[E12073](../proofs/validation/aurora/Equation12073/certificate.lean)。
- **颜色循环正规树**：E6912/E39214 用五色；E11082/E34889 用六色；E22446/E22591 用三色。三组各覆盖 2 条。颜色循环、运算和正规性规则不同。
- **辅助节点与部分逆正规树**：E10222/E35836 使用平方、右固定参数与部分逆；E12087/E33884 使用记录实际来源的返回代码与部分逆；两组各覆盖 2 条。
- **行像关系树**：E21866 的四条 R 规则覆盖 8 条；E23354 的三条 Row 规则是另一模型，覆盖 E23337/E23354 两条。参见 [E23354](../proofs/Equation23354/InfiniteModel.lean)。
- **辅助列与目标关系树**：E18137/E27863、E17286/E28626 各有自己的 Column/Target/Step 构造，各覆盖 2 条。参见 [E18137](../proofs/Equation18137/MODEL.zh-CN.md)、[E17286](../proofs/Equation17286/MODEL.zh-CN.md)。
- **有理数分段线性运算**：同一 Le Floch 构造及其相反运算，共覆盖 4 条。

## 核对范围

122 条模型方程与索引集合一致，每个代表归属恰好一次，对偶映射相互一致。逐个用 64 KiB 块读取所引用证书，核对 126 个不同文件的存在性和索引 SHA-256。分类由实际定义与模型说明判读；本次未重新编译 Lean 或提交 Judge。

未将候选、有限样本通过、带未证假设的局部引理，以及模型不存在性证明计入模型。分类统计不证明任何两个具体模型同构或不同构。

[机器可读清单](infinite-model-families.json) 保存逐题归属、证书路径、哈希及重复覆盖；以下列出全部精确方程和证书入口。


## 逐题证书清单

### 自由树上的 Step/Code 关系解码

| 方程 | 归属 | 证书 |
|---|---|---|
| E4952 / E41252 | 代表归属 | [E4952](../proofs/Equation4952/InfiniteModel.lean) / [E41252](../proofs/Equation41252/InfiniteModel.lean) |
| E4957 / E40914 | 代表归属 | [E4957](../proofs/Equation4957/InfiniteModel.lean) / [E40914](../proofs/Equation40914/InfiniteModel.lean) |
| E5012 / E41253 | 代表归属 | [E5012](../proofs/Equation5012/InfiniteModel.lean) / [E41253](../proofs/Equation41253/InfiniteModel.lean) |
| E5066 / E41239 | 代表归属 | [E5066](../proofs/Equation5066/InfiniteModel.lean) / [E41239](../proofs/Equation41239/InfiniteModel.lean) |
| E5141 / E40917 | 代表归属 | [E5141](../proofs/Equation5141/InfiniteModel.lean) / [E40917](../proofs/Equation40917/InfiniteModel.lean) |
| E5295 / E40909 | 代表归属 | [E5295](../proofs/Equation5295/InfiniteModel.lean) / [E40909](../proofs/Equation40909/InfiniteModel.lean) |
| E5833 / E40070 | 代表归属 | [E5833](../proofs/validation/aurora/Equation5833/certificate.lean) / [E40070](../proofs/validation/aurora/Equation40070/certificate.lean) |
| E7701 / E38303 | 代表归属 | [E7701](../proofs/Equation7701/InfiniteModel.lean) / [E38303](../proofs/Equation38303/InfiniteModel.lean) |
| E7755 / E38249 | 代表归属 | [E7755](../proofs/Equation7755/InfiniteModel.lean) / [E38249](../proofs/Equation38249/InfiniteModel.lean) |
| E7763 / E38565 | 代表归属 | [E7763](../proofs/validation/aurora/Equation7763/certificate.lean) / [E38565](../proofs/validation/aurora/Equation38565/certificate.lean) |
| E9345 / E36713 | 代表归属 | [E9345](../proofs/Equation9345/InfiniteModel.lean) / [E36713](../proofs/Equation36713/InfiniteModel.lean) |
| E9384 / E36714 | 代表归属 | [E9384](../proofs/Equation9384/InfiniteModel.lean) / [E36714](../proofs/Equation36714/InfiniteModel.lean) |
| E9603 / E36514 | 代表归属 | [E9603](../proofs/validation/aurora/Equation9603/certificate.lean) / [E36514](../proofs/validation/aurora/Equation36514/certificate.lean) |
| E9667 / E36638 | 代表归属 | [E9667](../proofs/Equation9667/InfiniteModel.lean) / [E36638](../proofs/Equation36638/InfiniteModel.lean) |
| E9680 / E36524 | 代表归属 | [E9680](../proofs/validation/aurora/Equation9680/certificate.lean) / [E36524](../proofs/validation/aurora/Equation36524/certificate.lean) |
| E10218 / E35685 | 代表归属 | [E10218](../proofs/validation/aurora/Equation10218/certificate.lean) / [E35685](../proofs/validation/aurora/Equation35685/certificate.lean) |
| E11081 / E35036 | 代表归属 | [E11081](../proofs/Equation11081/InfiniteModel.lean) / [E35036](../proofs/Equation35036/InfiniteModel.lean) |
| E11116 / E34888 | 代表归属 | [E11116](../proofs/Equation11116/InfiniteModel.lean) / [E34888](../proofs/Equation34888/InfiniteModel.lean) |
| E11205 / E35100 | 代表归属 | [E11205](../proofs/validation/aurora/Equation11205/certificate.lean) / [E35100](../proofs/validation/aurora/Equation35100/certificate.lean) |
| E11280 / E34778 | 代表归属 | [E11280](../proofs/validation/aurora/Equation11280/certificate.lean) / [E34778](../proofs/validation/aurora/Equation34778/certificate.lean) |
| E12234 / E33883 | 代表归属 | [E12234](../proofs/validation/aurora/Equation12234/certificate.lean) / [E33883](../proofs/validation/aurora/Equation33883/certificate.lean) |

### 自由树上的直接解码或递归逆查询

| 方程 | 归属 | 证书 |
|---|---|---|
| E5093 / E41179 | 代表归属 | [E5093](../proofs/validation/aurora/Equation5093/certificate.lean) / [E41179](../proofs/validation/aurora/Equation41179/certificate.lean) |
| E5107 / E40951 | 代表归属 | [E5107](../proofs/validation/aurora/Equation5107/certificate.lean) / [E40951](../proofs/validation/aurora/Equation40951/certificate.lean) |
| E5947 / E40057 | 代表归属 | [E5947](../proofs/validation/aurora/Equation5947/certificate.lean) / [E40057](../proofs/validation/aurora/Equation40057/certificate.lean) |
| E5951 / E40208 | 代表归属 | [E5951](../proofs/validation/aurora/Equation5951/certificate.lean) / [E40208](../proofs/validation/aurora/Equation40208/certificate.lean) |
| E6820 / E39485 | 代表归属 | [E6820](../proofs/validation/aurora/Equation6820/certificate.lean) / [E39485](../proofs/validation/aurora/Equation39485/certificate.lean) |
| E6878 / E39126 | 代表归属 | [E6878](../proofs/validation/aurora/Equation6878/certificate.lean) / [E39126](../proofs/validation/aurora/Equation39126/certificate.lean) |
| E6895 / E39163 | 代表归属 | [E6895](../proofs/validation/aurora/Equation6895/certificate.lean) / [E39163](../proofs/validation/aurora/Equation39163/certificate.lean) |
| E7587 / E38316 | 代表归属 | [E7587](../proofs/validation/aurora/Equation7587/certificate.lean) / [E38316](../proofs/validation/aurora/Equation38316/certificate.lean) |
| E8485 / E37519 | 代表归属 | [E8485](../proofs/validation/aurora/Equation8485/certificate.lean) / [E37519](../proofs/validation/aurora/Equation37519/certificate.lean) |
| E9337 / E36867 | 代表归属 | [E9337](../proofs/validation/aurora/Equation9337/certificate.lean) / [E36867](../proofs/validation/aurora/Equation36867/certificate.lean) |
| E12883 / E33020 | 代表归属 | [E12883](../proofs/validation/aurora/Equation12883/certificate.lean) / [E33020](../proofs/validation/aurora/Equation33020/certificate.lean) |
| E22619 / E22634 | 代表归属 | [E22619](../proofs/Equation22619/InfiniteModel.lean) / [E22634](../proofs/Equation22634/InfiniteModel.lean) |
| E5833 / E40070 | 另存历史构造 | [E5833](../proofs/Equation5833/InfiniteModel.lean) / [E40070](../proofs/Equation40070/InfiniteModel.lean) |

### 有限模式规则的正规树

| 方程 | 归属 | 证书 |
|---|---|---|
| E4916 / E41082 | 代表归属 | [E4916](../proofs/Equation4916/InfiniteModel.lean) / [E41082](../proofs/Equation41082/InfiniteModel.lean) |
| E15535 / E30591 | 代表归属 | [E15535](../proofs/Equation15535/InfiniteModel.lean) / [E30591](../proofs/Equation30591/InfiniteModel.lean) |
| E17522 / E28770 | 代表归属 | [E17522](../proofs/Equation17522/InfiniteModel.lean) / [E28770](../proofs/Equation28770/InfiniteModel.lean) |
| E20034 / E25964 | 代表归属 | [E20034](../proofs/Equation20034/InfiniteModel.lean) / [E25964](../proofs/Equation25964/InfiniteModel.lean) |
| E22455 / E22818 | 代表归属 | [E22455](../proofs/Equation22455/InfiniteModel.lean) / [E22818](../proofs/Equation22818/InfiniteModel.lean) |
| E19966 / E26105 | 代表归属 | [E19966](../proofs/Equation19966/InfiniteModel.lean) / [E26105](../proofs/Equation26105/InfiniteModel.lean) |
| E17260 / E28740 | 代表归属 | [E17260](../proofs/Equation17260/InfiniteModel.lean) / [E28740](../proofs/Equation28740/InfiniteModel.lean) |
| E6878 / E39126 | 另存历史构造 | [E6878](../proofs/Equation6878/InfiniteModel.lean) / [E39126](../proofs/Equation39126/InfiniteModel.lean) |

### 终止汇合重写、商树与规范形

| 方程 | 归属 | 证书 |
|---|---|---|
| E5837 / E40221 | 代表归属 | [E5837](../proofs/validation/aurora/Equation5837/certificate.lean) / [E40221](../proofs/validation/aurora/Equation40221/certificate.lean) |
| E12073 / E33998 | 代表归属 | [E12073](../proofs/validation/aurora/Equation12073/certificate.lean) / [E33998](../proofs/validation/aurora/Equation33998/certificate.lean) |
| E12857 / E33436 | 代表归属 | [E12857](../proofs/validation/aurora/Equation12857/attempt02/certificate.lean) / [E33436](../proofs/validation/aurora/Equation33436/certificate.lean) |
| E13764 / E32294 | 代表归属 | [E13764](../proofs/validation/aurora/Equation13764/certificate.lean) / [E32294](../proofs/validation/aurora/Equation32294/certificate.lean) |
| E13849 / E32281 | 代表归属 | [E13849](../proofs/validation/aurora/Equation13849/certificate.lean) / [E32281](../proofs/validation/aurora/Equation32281/certificate.lean) |
| E13992 / E32280 | 代表归属 | [E13992](../proofs/validation/aurora/Equation13992/certificate.lean) / [E32280](../proofs/validation/aurora/Equation32280/certificate.lean) |
| E18212 / E27859 | 代表归属 | [E18212](../proofs/validation/aurora/Equation18212/certificate.lean) / [E27859](../proofs/validation/aurora/Equation27859/certificate.lean) |

### 有限颜色循环的正规树

| 方程 | 归属 | 证书 |
|---|---|---|
| E6912 / E39214 | 代表归属 | [E6912](../proofs/validation/aurora/Equation6912/certificate.lean) / [E39214](../proofs/validation/aurora/Equation39214/certificate.lean) |
| E11082 / E34889 | 代表归属 | [E11082](../proofs/validation/aurora/Equation11082/certificate.lean) / [E34889](../proofs/validation/aurora/Equation34889/certificate.lean) |
| E22446 / E22591 | 代表归属 | [E22446](../proofs/Equation22446/InfiniteModel.lean) / [E22591](../proofs/Equation22591/InfiniteModel.lean) |

### 带辅助节点和部分逆的正规树

| 方程 | 归属 | 证书 |
|---|---|---|
| E10222 / E35836 | 代表归属 | [E10222](../proofs/Equation10222/InfiniteModel.lean) / [E35836](../proofs/Equation35836/InfiniteModel.lean) |
| E12087 / E33884 | 代表归属 | [E12087](../proofs/Equation12087/InfiniteModel.lean) / [E33884](../proofs/Equation33884/InfiniteModel.lean) |

### 行像关系树

| 方程 | 归属 | 证书 |
|---|---|---|
| E21714 / E24200 | 代表归属 | [E21714](../proofs/Equation21714/InfiniteModel.lean) / [E24200](../proofs/Equation24200/InfiniteModel.lean) |
| E21864 / E24199 | 代表归属 | [E21864](../proofs/Equation21864/InfiniteModel.lean) / [E24199](../proofs/Equation24199/InfiniteModel.lean) |
| E21865 / E24197 | 代表归属 | [E21865](../proofs/Equation21865/InfiniteModel.lean) / [E24197](../proofs/Equation24197/InfiniteModel.lean) |
| E21866 / E24201 | 代表归属 | [E21866](../proofs/Equation21866/InfiniteModel.lean) / [E24201](../proofs/Equation24201/InfiniteModel.lean) |
| E23337 / E23354 | 代表归属 | [E23337](../proofs/Equation23337/InfiniteModel.lean) / [E23354](../proofs/Equation23354/InfiniteModel.lean) |

### 辅助列关系与目标关系树

| 方程 | 归属 | 证书 |
|---|---|---|
| E18137 / E27863 | 代表归属 | [E18137](../proofs/Equation18137/InfiniteModel.lean) / [E27863](../proofs/Equation27863/InfiniteModel.lean) |
| E17286 / E28626 | 代表归属 | [E17286](../proofs/Equation17286/InfiniteModel.lean) / [E28626](../proofs/Equation28626/InfiniteModel.lean) |

### 有理数分段线性运算

| 方程 | 归属 | 证书 |
|---|---|---|
| E13102 / E33273 | 代表归属 | [E13102](../proofs/Equation13102/InfiniteModel.lean) / [E33273](../proofs/Equation33273/InfiniteModel.lean) |
| E20911 / E25087 | 代表归属 | [E20911](../proofs/Equation20911/InfiniteModel.lean) / [E25087](../proofs/Equation25087/InfiniteModel.lean) |
