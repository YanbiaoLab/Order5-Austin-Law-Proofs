# Equation18137：远端 Judge ACCEPTED

2026-09-14，远端任务 `25f7dd0341414b5c83e91957ee920fba` 已完成，返回
`status: accepted`、`error_code: ACCEPTED`。实际验收耗时 4,633 ms。

- [实际提交证书](certificate.lean)
- [完整请求](request.json)
- [原始验收回执](latest.json)
- [持久化任务记录](submission-state.json)
- [本地六单元核验](../../eq18137-formal/summary.json)

提交命题为精确的 `Equation18137 ↛ Equation2`，即存在满足
`x = (y ◇ x) ◇ (z ◇ ((x ◇ z) ◇ z))` 的非平凡模型。
请求中的 `verdict: false` 指这个“不蕴含”结论；验收结果是成功。
同一证书还包含自然数到树载体的单射，已在本地单独检查。

证书 SHA-256：
`80f1d61cabd487ebc4b43dfcd14034c58061e3340865ed3d12447ccffd56050c`。
本目录证书与 `proofs/Equation18137/InfiniteModel.lean` 逐字节一致。
模型的四个开发模块不变，导出时将辅助声明移入官方允许的 `submission` 命名空间。
没有修改 Judge 的证明策略或放宽公理检查。

远端检查报告的公理仅为 `Classical.choice`、`Quot.sound`、`propext`。
请求关闭缓存，超时设为 300 秒，只提交了一次。服务地址为
`http://10.220.69.172:8900`；实际后端、服务版本、策略版本和执行指纹见原始回执。

核对证书、本地日志、请求、任务 ID 与回执：

```sh
python3 proofs/validation/eq18137-formal/audit_remote.py
```

只读取这个已有任务的远端状态，不会重复提交：

```sh
python3 proofs/validation/eq18137-formal/remote_judge.py --wait
```
