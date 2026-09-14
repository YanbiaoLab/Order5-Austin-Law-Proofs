# 12087 / 33884 远端提交核验记录

## 本地验证

原模型的 125 个模块及两条精确目标共 129 次空目录构建已通过，318 个公理报告已审计；本次再次通过原始 [audit.py](audit.py) 的源码、日志、产物和索引校验。

[export_judge.py](export_judge.py) 按依赖顺序拼接全部证明正文，把辅助命名空间移到 `submission.Austin12087Trace`，移除本地模块导入和中间公理打印，保留两条独立目标包装。导出文件不依赖项目内的 Trace 模块，只导入 Judge 提供的 `JudgeProblem` 与 Lean 标准库。

完整单文件的本地预检有三次触及 RSS 停止线，均由检查器终止：

| 尝试 | 内部限额 / RSS 停止线 | 采样峰值 | 归档 |
|---|---|---|---|
| 默认异步 | 256 / 384 MiB | 404.38 MiB | [attempt01](judge-local-attempt01/Equation12087-JudgeSubmission-Standalone.json) |
| 关闭异步 | 256 / 384 MiB | 396.86 MiB | [attempt02](judge-local-attempt02/Equation12087-JudgeSubmission-Standalone.json) |
| 用户明确授权提高限额 | 512 / 768 MiB | 788.06 MiB | [attempt03](judge-local-attempt03/Equation12087-JudgeSubmission-Standalone.json) |

采样间隔会使实际停止值稍高于停止线。未将上述中止记录为证明失败或编译成功，也未继续提高本地限额。

最终对导出正文采用分段核验：[verify_judge.py](verify_judge.py) 将单文件中的 125 段正文原样生成模块，并从新的空目录串行构建，随后核验两个独立目标和模型包装。129 次构建全部通过，采样峰值 195.36 MiB，保持 `-j1 -M256`、RSS 384 MiB 停止线。[本地导出清单](judge-local/summary.json) 明确记录 `monolithic_local_pass: false`；[audit_judge.py](audit_judge.py) 检查分段正文与完整导出的拼接一致性、源码和日志及产物哈希，以及目标与单射的公理集合。

完整单文件的最终编译由远端 Judge 独立执行。本地分段通过不等同于远端验收。

## 提交协议

[remote_judge.py](remote_judge.py) 使用仓库现有 Judge 控制服务，关闭缓存，分别提交 `Equation12087 → Equation2`、`Equation33884 → Equation2` 的否定证书。每份请求最多 POST 一次；发送前持久化请求、证书和状态，响应丢失时不自动重发，后续按任务 ID 观察同一任务。

远端检验精确方程和非平凡性；无限性另由已通过本地内核检查的 `submission.CM.tower_injective` 与核心 `infinite_model` 证明。

## 远端结果

12087 首次提交任务 `8412f8e9309e4e2e9128be1c35124f62` 已在 114.811 秒后完成完整编译和公理检查，但远端返回 `DISALLOWED_DECLARATIONS`：最终包装显式引用了白名单外的 `inferInstance`。首次[回执](../aurora/Equation12087/attempt01/latest.json)、请求和证书完整保留。

修订仅涉及导出包装：给实例命名为 `submission.modelMagma` 并直接传入存在量词见证，核心模型与证明不变。修订版再次完成 129 次空目录分段构建，累计 46.413 秒、采样峰值 202.06 MiB。首次拒绝不会被改写为通过。

**12087 修订版已获 ACCEPTED**：任务 `8ab6915586de47139b55c7214e2657be`，远端用时 125.376 秒；[实际回执](../aurora/Equation12087/latest.json)。公理仅含 `Classical.choice`、`Quot.sound`、`propext`，关闭缓存。

**33884 已独立获 ACCEPTED**：任务 `d235f2155594437db5bc93cbb6b86cb5`，远端用时 120.230 秒；[实际回执](../aurora/Equation33884/latest.json)。

两个最终证书的 SHA-256：

- 12087：`2a3456f8ca387c00fadc2f4d77be9eddc1aff31d9f1fabcfddb0df2f322cbd54`
- 33884：`6895af7357d28ad69220f995ed9134fad031534e42b396ed6d90757d55020018`

在原研究工作区运行 `audit_judge.py` 可核对本地分段编译、完整导出、精确请求、首次拒绝历史、最终验收回执与索引绑定。运行 `record_remote.py` 登记已经通过审计的回执；它只修改这两条方程记录。

## 远程仓库复现入口

新检出请运行 `python3 proofs/validation/eq12087-formal/portable.py` 核对归档，或加 `--rebuild` 重新编译核心模型与两条精确目标。原脚本、绝对构建路径和历史产物哈希保留为当时证据；可移植入口不要求这些旧路径或二进制缓存存在，也不会重新提交 Judge。
