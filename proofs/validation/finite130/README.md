# 全部 130 条方程的有限侧证明工作

目标：依次完成表 20.1、20.2、20.3 中每条方程的有限侧 Lean 证书，并通过极光云 judge-v3-repl 对有限目标的验证。目标仍在进行；本地编译不等于云端验收。

| 原表 | 条数 | 本地有限证书已通过 | 极光云有限目标已接受 |
|---|---:|---:|---:|
| 20.1 | 10 | 10 | 0 |
| 20.2 | 96 | 1 | 0 |
| 20.3 | 24 | 0 | 0 |

本批新建 9 份 `FiniteTrivial.lean`，补齐表 20.1 的本地有限侧证明。已有 Equation28770 的证明保留。

- Equation4916：由有限性得到左平移单射性，推出共同平方，再由源方程推导右乘共同平方为常值，完成坍缩。
- Equation15535：建立左右平移双射性，推出共同平方，随后用消去律与等式实例完成坍缩。
- Equation20034：平方映射和一个派生映射为双射，推出运算不依赖左参数，再由源方程推出任意两元素相等。
- Equation22455：平方映射为双射，所有左平移为单射；源方程迫使每个右平移为常值，从而坍缩。
- Equation41082、Equation30591、Equation17522、Equation25964、Equation22818：分别通过相反运算转移上述证明及已有 Equation28770 证明。每份文件包含所需的基础定理，可独立编译。

9 份新证书均已在 Lean 4.33.1 串行编译通过，目标为 `[Finite G]` 下源方程推出 `Equation2 G`。公理依赖仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集。逐项日志和输入 SHA-256 在本目录对应的 JSON 与 log 文件中。[inventory.json](inventory.json) 记录全部 130 条方程的缺口。

## 极光云接口核对

测试地址：`http://10.220.69.172:8900`，服务正常。使用已有 Equation28770 有限定理核对接口，job 为 `b208b4ba010548b18e1a71e15b4dcdce`。任务已结束，返回 `LEAN_REJECTED`，原因是 `failed to synthesize instance of type class Finite G`。

当前服务从题目生成 `∀ G [Magma G], EquationLHS G → EquationRHS G`，需要的目标则是 `∀ G [Magma G] [Finite G], EquationLHS G → EquationRHS G`。这是目标契约不匹配，不是否定本地已验证的有限定理。Austin 律有非平凡无限模型，不能删除有限性假设。

原始证据：[request.json](remote-contract/request.json)、[job.json](remote-contract/job.json)、[health.json](remote-contract/health.json)、[result.json](remote-contract/result.json)。服务指纹及完整返回均已保存。本次接口核对不计为有限题目的云端接受。

仍需取得支持有限目标的入口或为服务增加明确的有限目标支持，再逐条验收。不会用无关的恒真蕴含包装来冒充有限目标验收。表 20.3 的有限侧属于原分类中的未知问题，不能预设全部存在有限坍缩证明。
