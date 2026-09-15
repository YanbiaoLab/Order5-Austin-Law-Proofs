# E22446 远端 Judge 验收

2026-09-15。**ACCEPTED**，任务 `a10791d664bd43df97dad1531bb1acfa`。

精确目标为 E22446 不蕴含 Equation2，即存在满足原式的非平凡 magma。完整单文件由远端 Judge 实际编译并验收，耗时 **17.413 秒**，缓存关闭。

- [实际提交证书](certificate.lean)：172,673 字节，SHA-256 `2065d90f6e43c362723bfea4b6d41bb6c710ad9eedac4ee9f57059d1e705e95c`。
- [完整服务回执](latest.json)、[请求](request.json)、[任务状态](submission-state.json)。
- 公理依赖仅为 `Classical.choice`、`Quot.sound`、`propext`。
- 证书包含自然数单射；其导出端点也已在本机分段核验中单独审计。

首次任务 `f6e7859371cb44d78bc9a2b3a05b5f87` 在进入 Lean 之前因说明性注释里的 `syntax` 被预检识别为禁用词而退回。保留[原证书](attempt01/certificate.lean)和[原回执](attempt01/latest.json)。第二版只移除注释，数学证明代码不变；[差异记录](../../eq22446-judge-export-v2/comment-removal-audit.json)和[58 个分段核验](../../eq22446-judge-export-v2/summary.json)均通过。两版各提交一次，每次均使用已保存的任务 ID 取回结果。

[归档核验入口](../../eq22446-infinite-model/README.md)检查证书字节、请求、回执、模块源码与本机日志的绑定。原始命令和脚本副本用于记录当时环境；公开核验不依赖仓库根目录的 `scripts/` 或本机绝对路径。

本次没有提交有限侧证明或对偶 E22591。模型说明见[构造报告](../../../Equation22446/MODEL.zh-CN.md)。
