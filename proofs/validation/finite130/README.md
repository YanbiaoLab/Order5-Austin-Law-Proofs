# 全部 130 条方程的有限侧证明工作

目标：依次完成表 20.1、20.2、20.3 中每条方程的有限侧 Lean 证书，并通过极光云 judge-v3-repl 对有限目标的验证。目标仍在进行；本地编译不等于云端验收。

| 原表 | 条数 | 本地有限证书已通过 | 极光云有限目标已接受 |
|---|---:|---:|---:|
| 20.1 | 10 | 10 | 0 |
| 20.2 | 96 | 96 | 0 |
| 20.3 | 24 | 8 | 0 |

表 20.1 首批新建 9 份 `FiniteTrivial.lean`，补齐表 20.1 的本地有限侧证明。已有 Equation28770 的证明保留。

- Equation4916：由有限性得到左平移单射性，推出共同平方，再由源方程推导右乘共同平方为常值，完成坍缩。
- Equation15535：建立左右平移双射性，推出共同平方，随后用消去律与等式实例完成坍缩。
- Equation20034：平方映射和一个派生映射为双射，推出运算不依赖左参数，再由源方程推出任意两元素相等。
- Equation22455：平方映射为双射，所有左平移为单射；源方程迫使每个右平移为常值，从而坍缩。
- Equation41082、Equation30591、Equation17522、Equation25964、Equation22818：分别通过相反运算转移上述证明及已有 Equation28770 证明。每份文件包含所需的基础定理，可独立编译。

表 20.1 的 9 份新证书均已在 Lean 4.33.1 串行编译通过，目标为 `[Finite G]` 下源方程推出 `Equation2 G`。公理依赖仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集。逐项日志和输入 SHA-256 在本目录对应的 JSON 与 log 文件中。[inventory.json](inventory.json) 记录全部 130 条方程的缺口。

## 极光云接口核对

测试地址：`http://10.220.69.172:8900`，服务正常。使用已有 Equation28770 有限定理核对接口，job 为 `b208b4ba010548b18e1a71e15b4dcdce`。任务已结束，返回 `LEAN_REJECTED`，原因是 `failed to synthesize instance of type class Finite G`。

当前服务从题目生成 `∀ G [Magma G], EquationLHS G → EquationRHS G`，需要的目标则是 `∀ G [Magma G] [Finite G], EquationLHS G → EquationRHS G`。这是目标契约不匹配，不是否定本地已验证的有限定理。Austin 律有非平凡无限模型，不能删除有限性假设。

原始证据：[request.json](remote-contract/request.json)、[job.json](remote-contract/job.json)、[health.json](remote-contract/health.json)、[result.json](remote-contract/result.json)。服务指纹及完整返回均已保存。本次接口核对不计为有限题目的云端接受。

仍需取得支持有限目标的入口或为服务增加明确的有限目标支持，再逐条验收。不会用无关的恒真蕴含包装来冒充有限目标验收。表 20.3 的有限侧属于原分类中的未知问题，不能预设全部存在有限坍缩证明。

## 表 20.2 新增本地证书（finite_cancellation）

本批新增 39 份，均已通过 Lean 4.33.1 串行编译与公理检查，公理仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。对偶证书通过相反运算转移，包含所需基础定理。

Equation10222、Equation11081、Equation11205、Equation11280、Equation12883、Equation13764、Equation13992、Equation32280、Equation32294、Equation33020、Equation34778、Equation35036、Equation35100、Equation35836、Equation36524、Equation36713、Equation36867、Equation38249、Equation38303、Equation39163、Equation39485、Equation40909、Equation40917、Equation40951、Equation41179、Equation41239、Equation41252、Equation4952、Equation5066、Equation5107、Equation5141、Equation5295、Equation6820、Equation6895、Equation7701、Equation7755、Equation9337、Equation9345、Equation9680。

每份源码与对应 JSON、日志按 SHA-256 绑定；云端有限目标验收仍未完成。

## 表 20.2 新增本地证书（explicit_equational_replay）

本批新增 48 份，均已通过 Lean 4.33.1 串行编译与公理检查，公理仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。对偶证书通过相反运算转移，包含所需基础定理。

Equation10218、Equation11082、Equation11116、Equation12073、Equation12087、Equation12234、Equation12857、Equation13849、Equation32281、Equation33436、Equation33883、Equation33884、Equation33998、Equation34888、Equation34889、Equation35685、Equation36487、Equation36514、Equation36638、Equation36714、Equation37519、Equation38316、Equation38565、Equation39126、Equation39214、Equation40037、Equation40057、Equation40070、Equation40208、Equation40221、Equation40914、Equation41253、Equation4957、Equation5012、Equation5833、Equation5834、Equation5837、Equation5947、Equation5951、Equation6878、Equation6912、Equation7587、Equation7763、Equation8485、Equation9384、Equation9603、Equation9663、Equation9667。

每份源码与对应 JSON、日志按 SHA-256 绑定；云端有限目标验收仍未完成。

## 表 20.2 新增本地证书（square_translation_and_equational_replay）

本批新增 6 份，均已通过 Lean 4.33.1 串行编译与公理检查，公理仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。对偶证书通过相反运算转移，包含所需基础定理。

Equation18212、Equation27859、Equation19966、Equation26105、Equation22619、Equation22634。

每份源码与对应 JSON、日志按 SHA-256 绑定；云端有限目标验收仍未完成。

## 表 20.2 新增本地证书（derived_translation_bijection）

本批新增 2 份，均已通过 Lean 4.33.1 串行编译与公理检查，公理仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。对偶证书通过相反运算转移，包含所需基础定理。

Equation18137、Equation27863。

每份源码与对应 JSON、日志按 SHA-256 绑定；云端有限目标验收仍未完成。

## 表 20.1–20.2 本地完成核对

两表共 106 份有限坍缩证书全部具备源码、成功编译记录与公理审计；本轮新增表 20.2 的 95 份。最高采样 RSS 低于 1.5 GiB。

最后一对 Equation18137／Equation27863 使用派生映射 `t ↦ (y ◇ t) ◇ t`：先从源方程证明单射，再由有限性取得满射，最后完成等式推导。派生映射的线索来自[上游 Conjectures.lean](https://github.com/vlad902/equational_theories/blob/6954db7498e222a7ca9a9aac791cb267b4442fc6/equational_theories/Generated/Order5/Conjectures.lean)；本仓证书包含完整单射性证明，没有采用其中的 conjecture 或额外公理。

完成表 20.1–20.2 时，表 20.3 尚有 24 个有限侧缺口；随后补齐其中 8 个，详见下文。极光云有限目标 accepted 仍为 0。

## 表 20.3 首批有限侧搜索

对 Equation12294、Equation13102、Equation20911 的可由有限性建立的平移双射性质进行了等式搜索，每题 10 秒、Prover9 内存上限 128 MiB。本轮均未得到证明；这是有界搜索结果，不是有限模型存在性证明，也不是无解结论。原输入、完整输出哈希及终止日志摘录见[搜索记录](table20_3-search/summary.json)。

极光云入口已再次核对，VerifyReq 仍只有 problem、verdict、code、timeout_seconds、cache_mode，未出现有限目标选项；见[接口复核](remote-contract/recheck.json)。未重复提交已知目标不匹配的任务。

## 表 20.3 新增本地证书（finite_product_bijection_and_equational_replay）

本批新增 8 份，均已通过 Lean 4.33.1 串行编译与公理检查，公理仅包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。对偶证书通过相反运算转移，包含所需基础定理。

Equation21714、Equation24200、Equation21864、Equation24199、Equation21865、Equation24197、Equation21866、Equation24201。

每份源码与对应 JSON、日志按 SHA-256 绑定；云端有限目标验收仍未完成。

## 表 20.3 的有限乘积集方法

本轮新增的 8 份证书使用 `G × G` 上的单射转满射，得到新的运算恒等式，再完成有限坍缩推导。详细数学论证、证书链接与验证证据见[表 20.3 报告](table20_3-pairs/README.md)。目前本地证书共 114 份，尚缺 16 份。

## 有限目标 judge 扩展

[扩展补丁与验证报告](judge-extension/README.md) 已备妥：80 项 Python 测试通过，真实定制 REPL 的 6 项正负对照及新增表 20.3 的 8 份有限证书检查全部符合预期。补丁增加由 judge 生成的原生有限目标，维持公理策略，并隔离域与缓存。未部署极光云；等待新增独立单 worker 入口的授权。

剩余方程的 56 次对称乘积映射检查和 7 次坍缩搜索暂未得到新的有限坍缩证明；Equation22446 的平方映射单射／双射性已单独形式化，见[后续搜索报告](table20_3-pair-search/README.md)。这不改变本条尚缺 FiniteTrivial.lean 的状态。

## 后续结构化简

Equation20911 的有限左右消去律、共同平方、右单位元和两条迭代关系已通过 Lean 检查，保存于独立的 FiniteStructure.lean。它们尚未完成 Equation2 的推导；有限证书总数仍为 114。上下文逆映射、非对称乘积映射和三坐标切分的有界探索见[结构化简报告](context-inverses/README.md)。极光云现有接口再次确认尚无有限目标支持，等待独立入口部署授权。
