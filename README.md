# Order 5 Austin Laws — 证明索引

记录 Blueprint 表 20.1–20.3 的全部 130 条方程（65 个对偶对），逐项追踪有限侧与无限侧的 Lean 证据。

表类型取自 [Order 5 Austin laws](https://teorth.github.io/equational_theories/blueprint/order-5-austin-laws.html)，保留原始分类，不随本仓库证明进展改写：

| 原表 | 方程数 | 原表含义 |
|---|---:|---|
| 20.1 | 10 | 已知 Austin 律：只有平凡有限模型，存在非平凡无限模型 |
| 20.2 | 96 | 已知只有平凡有限模型；原表中无限侧未知 |
| 20.3 | 24 | 原表中是否存在非平凡有限模型未知 |

“有限侧证明”指 `∀ (G : Type) [Magma G] [Finite G], EquationN G → Equation2 G`，即所有有限模型都平凡。单元素模型对这些恒等式总是存在；仅证明其存在没有分类作用。无有限性假设地推出 Equation2 是更强结论，会排除非平凡无限模型。

“无限侧证明”须构造满足源方程的模型并证明载体无限，例如给出 `Nat` 到载体的单射。Judge 的 `EquationN ↛ Equation2` 目标只直接要求非平凡性。“非平凡无限 Lean 证书”列链接已归档的模型证书；是否另含显式无限性定理，在方程详情页说明。

本次归档：42 份历史 Judge 已接受的非平凡模型证书（10 / 30 / 2），其中 14 份包含 `tower_injective`；其余 28 份使用无限归纳树载体，但未单列无限性定理。另收录 2 份上游有限坍缩定理源码。这些是指定来源的已核实库存，未穷尽所有历史分支；未收录不等于不存在证明。

已用 Lean 4.33.1 串行重新编译：模型证书 42/42，有限坍缩定理 2/2 通过。目标与公理依赖检查见 [编译报告](proofs/validation/2026-09-08/README.md)。历史验收、上游源码、未形式化数学论证分别记录；不把缺少 Lean 文件标为数学上未知。表 20.3 的两份已接受证书只完成非平凡模型侧，有限侧仍未知，不能据此确认为 Austin 律。

已有 Equation12857／Equation33436 的重写模型论证保存在 [构造笔记](docs/Equation12857-model.md)，尚未形式化。

每条方程的公式、对偶、来源与缺口见下表的方程链接。库存数据为 [index.json](proofs/index.json)，归档和验证方式见 [proofs/README.md](proofs/README.md)。

| 方程 | 对偶方程 | 原表 | 平凡有限状态 | 平凡有限 Lean 证书 | 非平凡无限状态 | 非平凡无限 Lean 证书 |
|---|---|---|---|---|---|---|
| [Equation4916](proofs/Equation4916/README.md) | Equation41082 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation4916/InfiniteModel.lean) |
| [Equation41082](proofs/Equation41082/README.md) | Equation4916 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation41082/InfiniteModel.lean) |
| [Equation15535](proofs/Equation15535/README.md) | Equation30591 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation15535/InfiniteModel.lean) |
| [Equation30591](proofs/Equation30591/README.md) | Equation15535 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation30591/InfiniteModel.lean) |
| [Equation17522](proofs/Equation17522/README.md) | Equation28770 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation17522/InfiniteModel.lean) |
| [Equation28770](proofs/Equation28770/README.md) | Equation17522 | 20.1 | 已证仅平凡（Lean） | [FiniteTrivial.lean](proofs/Equation28770/FiniteTrivial.lean) | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation28770/InfiniteModel.lean) |
| [Equation20034](proofs/Equation20034/README.md) | Equation25964 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation20034/InfiniteModel.lean) |
| [Equation25964](proofs/Equation25964/README.md) | Equation20034 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation25964/InfiniteModel.lean) |
| [Equation22455](proofs/Equation22455/README.md) | Equation22818 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation22455/InfiniteModel.lean) |
| [Equation22818](proofs/Equation22818/README.md) | Equation22455 | 20.1 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation22818/InfiniteModel.lean) |
| [Equation4952](proofs/Equation4952/README.md) | Equation41252 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation4952/InfiniteModel.lean) |
| [Equation41252](proofs/Equation41252/README.md) | Equation4952 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation41252/InfiniteModel.lean) |
| [Equation4957](proofs/Equation4957/README.md) | Equation40914 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation4957/InfiniteModel.lean) |
| [Equation40914](proofs/Equation40914/README.md) | Equation4957 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation40914/InfiniteModel.lean) |
| [Equation5012](proofs/Equation5012/README.md) | Equation41253 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation5012/InfiniteModel.lean) |
| [Equation41253](proofs/Equation41253/README.md) | Equation5012 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation41253/InfiniteModel.lean) |
| [Equation5066](proofs/Equation5066/README.md) | Equation41239 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation5066/InfiniteModel.lean) |
| [Equation41239](proofs/Equation41239/README.md) | Equation5066 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation41239/InfiniteModel.lean) |
| [Equation5093](proofs/Equation5093/README.md) | Equation41179 | 20.2 | 已证仅平凡（Lean） | [FiniteTrivial.lean](proofs/Equation5093/FiniteTrivial.lean) | 未收录 | 未收录 |
| [Equation41179](proofs/Equation41179/README.md) | Equation5093 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation5107](proofs/Equation5107/README.md) | Equation40951 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation40951](proofs/Equation40951/README.md) | Equation5107 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation5141](proofs/Equation5141/README.md) | Equation40917 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation5141/InfiniteModel.lean) |
| [Equation40917](proofs/Equation40917/README.md) | Equation5141 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation40917/InfiniteModel.lean) |
| [Equation5295](proofs/Equation5295/README.md) | Equation40909 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation5295/InfiniteModel.lean) |
| [Equation40909](proofs/Equation40909/README.md) | Equation5295 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation40909/InfiniteModel.lean) |
| [Equation5833](proofs/Equation5833/README.md) | Equation40070 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation40070](proofs/Equation40070/README.md) | Equation5833 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation5834](proofs/Equation5834/README.md) | Equation40037 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation40037](proofs/Equation40037/README.md) | Equation5834 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation5837](proofs/Equation5837/README.md) | Equation40221 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation40221](proofs/Equation40221/README.md) | Equation5837 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation5947](proofs/Equation5947/README.md) | Equation40057 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation40057](proofs/Equation40057/README.md) | Equation5947 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation5951](proofs/Equation5951/README.md) | Equation40208 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation40208](proofs/Equation40208/README.md) | Equation5951 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation6820](proofs/Equation6820/README.md) | Equation39485 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation39485](proofs/Equation39485/README.md) | Equation6820 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation6878](proofs/Equation6878/README.md) | Equation39126 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation39126](proofs/Equation39126/README.md) | Equation6878 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation6895](proofs/Equation6895/README.md) | Equation39163 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation39163](proofs/Equation39163/README.md) | Equation6895 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation6912](proofs/Equation6912/README.md) | Equation39214 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation39214](proofs/Equation39214/README.md) | Equation6912 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation7587](proofs/Equation7587/README.md) | Equation38316 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation38316](proofs/Equation38316/README.md) | Equation7587 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation7701](proofs/Equation7701/README.md) | Equation38303 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation7701/InfiniteModel.lean) |
| [Equation38303](proofs/Equation38303/README.md) | Equation7701 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation38303/InfiniteModel.lean) |
| [Equation7755](proofs/Equation7755/README.md) | Equation38249 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation7755/InfiniteModel.lean) |
| [Equation38249](proofs/Equation38249/README.md) | Equation7755 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation38249/InfiniteModel.lean) |
| [Equation7763](proofs/Equation7763/README.md) | Equation38565 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation38565](proofs/Equation38565/README.md) | Equation7763 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation8485](proofs/Equation8485/README.md) | Equation37519 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation37519](proofs/Equation37519/README.md) | Equation8485 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation9337](proofs/Equation9337/README.md) | Equation36867 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation36867](proofs/Equation36867/README.md) | Equation9337 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation9345](proofs/Equation9345/README.md) | Equation36713 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation9345/InfiniteModel.lean) |
| [Equation36713](proofs/Equation36713/README.md) | Equation9345 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation36713/InfiniteModel.lean) |
| [Equation9384](proofs/Equation9384/README.md) | Equation36714 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation9384/InfiniteModel.lean) |
| [Equation36714](proofs/Equation36714/README.md) | Equation9384 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation36714/InfiniteModel.lean) |
| [Equation9603](proofs/Equation9603/README.md) | Equation36514 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation36514](proofs/Equation36514/README.md) | Equation9603 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation9663](proofs/Equation9663/README.md) | Equation36487 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation36487](proofs/Equation36487/README.md) | Equation9663 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation9667](proofs/Equation9667/README.md) | Equation36638 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation9667/InfiniteModel.lean) |
| [Equation36638](proofs/Equation36638/README.md) | Equation9667 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation36638/InfiniteModel.lean) |
| [Equation9680](proofs/Equation9680/README.md) | Equation36524 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation36524](proofs/Equation36524/README.md) | Equation9680 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation10218](proofs/Equation10218/README.md) | Equation35685 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation35685](proofs/Equation35685/README.md) | Equation10218 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation10222](proofs/Equation10222/README.md) | Equation35836 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation35836](proofs/Equation35836/README.md) | Equation10222 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation11081](proofs/Equation11081/README.md) | Equation35036 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation11081/InfiniteModel.lean) |
| [Equation35036](proofs/Equation35036/README.md) | Equation11081 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation35036/InfiniteModel.lean) |
| [Equation11082](proofs/Equation11082/README.md) | Equation34889 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation34889](proofs/Equation34889/README.md) | Equation11082 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation11116](proofs/Equation11116/README.md) | Equation34888 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation11116/InfiniteModel.lean) |
| [Equation34888](proofs/Equation34888/README.md) | Equation11116 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation34888/InfiniteModel.lean) |
| [Equation11205](proofs/Equation11205/README.md) | Equation35100 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation35100](proofs/Equation35100/README.md) | Equation11205 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation11280](proofs/Equation11280/README.md) | Equation34778 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation34778](proofs/Equation34778/README.md) | Equation11280 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation12073](proofs/Equation12073/README.md) | Equation33998 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation33998](proofs/Equation33998/README.md) | Equation12073 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation12087](proofs/Equation12087/README.md) | Equation33884 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation33884](proofs/Equation33884/README.md) | Equation12087 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation12234](proofs/Equation12234/README.md) | Equation33883 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation33883](proofs/Equation33883/README.md) | Equation12234 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation12857](proofs/Equation12857/README.md) | Equation33436 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation33436](proofs/Equation33436/README.md) | Equation12857 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation12883](proofs/Equation12883/README.md) | Equation33020 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation33020](proofs/Equation33020/README.md) | Equation12883 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation13764](proofs/Equation13764/README.md) | Equation32294 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation32294](proofs/Equation32294/README.md) | Equation13764 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation13849](proofs/Equation13849/README.md) | Equation32281 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation32281](proofs/Equation32281/README.md) | Equation13849 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation13992](proofs/Equation13992/README.md) | Equation32280 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation32280](proofs/Equation32280/README.md) | Equation13992 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation18137](proofs/Equation18137/README.md) | Equation27863 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation27863](proofs/Equation27863/README.md) | Equation18137 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation18212](proofs/Equation18212/README.md) | Equation27859 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation27859](proofs/Equation27859/README.md) | Equation18212 | 20.2 | 仅平凡（Blueprint） | 未收录 | 未收录 | 未收录 |
| [Equation19966](proofs/Equation19966/README.md) | Equation26105 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation19966/InfiniteModel.lean) |
| [Equation26105](proofs/Equation26105/README.md) | Equation19966 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation26105/InfiniteModel.lean) |
| [Equation22619](proofs/Equation22619/README.md) | Equation22634 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation22619/InfiniteModel.lean) |
| [Equation22634](proofs/Equation22634/README.md) | Equation22619 | 20.2 | 仅平凡（Blueprint） | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation22634/InfiniteModel.lean) |
| [Equation12294](proofs/Equation12294/README.md) | Equation33856 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation33856](proofs/Equation33856/README.md) | Equation12294 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation13102](proofs/Equation13102/README.md) | Equation33273 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation33273](proofs/Equation33273/README.md) | Equation13102 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation17260](proofs/Equation17260/README.md) | Equation28740 | 20.3 | 未知 | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation17260/InfiniteModel.lean) |
| [Equation28740](proofs/Equation28740/README.md) | Equation17260 | 20.3 | 未知 | 未收录 | 本仓编译通过 | [InfiniteModel.lean](proofs/Equation28740/InfiniteModel.lean) |
| [Equation17286](proofs/Equation17286/README.md) | Equation28626 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation28626](proofs/Equation28626/README.md) | Equation17286 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation20911](proofs/Equation20911/README.md) | Equation25087 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation25087](proofs/Equation25087/README.md) | Equation20911 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation21714](proofs/Equation21714/README.md) | Equation24200 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation24200](proofs/Equation24200/README.md) | Equation21714 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation21864](proofs/Equation21864/README.md) | Equation24199 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation24199](proofs/Equation24199/README.md) | Equation21864 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation21865](proofs/Equation21865/README.md) | Equation24197 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation24197](proofs/Equation24197/README.md) | Equation21865 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation21866](proofs/Equation21866/README.md) | Equation24201 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation24201](proofs/Equation24201/README.md) | Equation21866 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation22446](proofs/Equation22446/README.md) | Equation22591 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation22591](proofs/Equation22591/README.md) | Equation22446 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation23337](proofs/Equation23337/README.md) | Equation23354 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation23354](proofs/Equation23354/README.md) | Equation23337 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation23357](proofs/Equation23357/README.md) | Equation23653 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
| [Equation23653](proofs/Equation23653/README.md) | Equation23357 | 20.3 | 未知 | 未收录 | 未收录 | 未收录 |
