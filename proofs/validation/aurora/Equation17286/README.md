**Equation17286：远端 Judge 已验收**

2026-09-14，任务 `d5ccb148a13d4648a13520ee3d457b00` 返回 **ACCEPTED**，服务报告耗时 4.566 秒。
`cache_mode=off`，客户端提交一次，后端执行一次。

[实际提交证书](certificate.lean) 与 [本地独立证书](../../../Equation17286/InfiniteModel.lean) 逐字节一致。
证书 SHA-256：`9a04b41870ab41845263fd561a6b3843392b0f05049ab096c4f61ae34d924c43`。
请求 SHA-256（排序键 JSON）：`0e1ee220db81621426857c87c2997cdab24e4bd0097f4b91ac5e007dd921b7c9`。

[请求](request.json)、[初始任务](job.json)、[最终回执](latest.json)、[持久任务状态](submission-state.json)、[提交时健康状态](health-at-submission.json) 均保留。
精确原式不蕴含 `x = y`，即存在非平凡模型；同一模型的自然数单射另有本地 Lean 核验。详见[两式验收与审计报告](../../eq17286-formal/JUDGE.md)。
