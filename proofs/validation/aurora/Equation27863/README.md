# Equation27863：远端 Judge ACCEPTED

2026-09-14。任务 `c57824e679ec4461b923a5237bdfcd56` 已完成，返回
`status: accepted`、`error_code: ACCEPTED`，验收耗时 4,578 ms。

- [实际提交的独立证书](certificate.lean)
- [完整请求](request.json)
- [原始验收回执](latest.json)
- [持久化任务记录](submission-state.json)
- [本地七单元核验](../../eq27863-formal/summary.json)

提交命题为精确的 `Equation27863 ↛ Equation2`，即存在满足
`x = ((y ◇ (y ◇ x)) ◇ y) ◇ (x ◇ z)` 的非平凡模型。
请求中的 `verdict: false` 表示“不蕴含”；验收结果为成功。
相同证书的自然数单射已在本地另行审计。

证书 SHA-256：
`c21104d9525bf39facb0b7a8638f72c60b5df516096ddb479ce239f4bf8acc22`。
本目录证书与 `proofs/Equation27863/InfiniteModel.lean` 逐字节一致，
包含完整原模型构造和对偶转移证明，不要求 Judge 预装 Equation18137 模型。

缓存关闭，仅提交一次；返回公理仅为 `Classical.choice`、`Quot.sound`、`propext`。
服务地址为 `http://10.220.69.172:8900`；实际后端、服务版本、证明策略和执行指纹见回执。
