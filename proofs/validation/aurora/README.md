# 极光云 judge-v3-repl 验证

只记录服务实际返回的 accepted；本地 Lean 通过、搜索完成和请求已入队均不代替远程验收。

| 方程 | 任务 ID | 结果 | 实际提交证书 |
|---|---|---|---|
| Equation12857 | `f343d53fdad6449cb0162cbcdb71a8dc` | [accepted](Equation12857/attempt02/latest.json) | [Lean](Equation12857/attempt02/certificate.lean) |
| Equation33436 | `30f2f241005a49849b4e416111c52582` | [accepted](Equation33436/latest.json) | [Lean](Equation33436/certificate.lean) |

Equation12857 的首次提交因辅助声明命名不符合默认白名单而被拒绝，相关失败记录保留。后续把自建定义放入官方允许的 submission 命名空间，使用明确的 Magma 实例和 Nat.noConfusion 后通过；未更改 judge 的证明策略。
