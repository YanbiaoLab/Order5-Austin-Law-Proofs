# E22591 远端 Judge ACCEPTED

2026-09-15，完整独立证书首次提交成功，缓存关闭。

- 任务：`910bd0a8ccad40e69c784c03968a3714`
- 精确目标：`Equation22591 ↛ Equation2`
- 原式：`x = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ z)`
- 结果：`done / accepted / ACCEPTED / false`
- 远端用时：17.436 秒
- 公理：`Classical.choice`、`Quot.sound`、`propext`
- 证书 SHA-256：`4972f81092a903ae8fd31dc8c8ae2dc810d57b6c3f7f0da5bbc3212e8e3c11c0`

[certificate.lean](certificate.lean)与[公开单文件证书](../../../Equation22591/JudgeSubmission.lean)及[request.json](request.json)中的代码逐字节一致。[latest.json](latest.json)为完整终态回执；[job.json](job.json)为提交返回记录；[submission-state.json](submission-state.json)绑定任务、请求和证书哈希，记录一次 POST；[health-at-submission.json](health-at-submission.json)保存服务检查结果。

Judge 的 `false` 判定验证本题非平凡模型存在性。显式自然数单射由[本机 Lean 核验](../../eq22591-formal/README.md)额外检查，不能仅从 Judge 的 `false` 字段推出。

只读审计，不重复提交：

```sh
python3 proofs/validation/eq22591-formal/archive.py
```
