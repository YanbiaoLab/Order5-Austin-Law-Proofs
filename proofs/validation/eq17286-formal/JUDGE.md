**Equation17286 / Equation28626：远端 Lean 验收完成**

2026-09-14，两份已通过本地核验的独立证书均获远端 Judge **ACCEPTED**，源码无需修改。

| 方程 | 任务 ID | 结果 | 服务耗时 | 证据 |
|---|---|---|---:|---|
| Equation17286 | `d5ccb148a13d4648a13520ee3d457b00` | **ACCEPTED** | 4.566 秒 | [回执](../aurora/Equation17286/latest.json) |
| Equation28626 | `1287d4bc4fa6417ca2ced84608cfac13` | **ACCEPTED** | 5.168 秒 | [回执](../aurora/Equation28626/latest.json) |

两次均使用 `cache_mode=off`、300 秒请求上限，客户端各提交一次，后端各执行一次；串行完成。服务入口为 `http://10.220.69.172:8900`。完整服务版本、证明策略版本和执行指纹保存在各回执中。

远端精确题面分别为：

- E17286：`x = (y ◇ x) ◇ (z ◇ (z ◇ (x ◇ z)))`。
- E28626：`x = (((y ◇ x) ◇ y) ◇ y) ◇ (x ◇ z)`。

两次结论均为“不蕴含 `x = y`”，即对应原式存在非平凡模型。远端 `Goal` 直接检查原式与非平凡性；证书也包含同一运算上的自然数单射证明，该显式无限性已由八单元[本地核验](README.md)单独审计。远端回执报告的 `submission` 公理仅为 `Classical.choice`、`Quot.sound`、`propext`。

[只读审计](audit_remote.py)核对：当前源码、实际发送的 `code`、归档证书三者逐字节一致；请求哈希、证书哈希、任务 ID、精确公式、允许公理、原本地构建日志与索引绑定均一致。详见[机器可读审计](remote-audit.json)。

```sh
python3 proofs/validation/eq17286-formal/audit_remote.py
```

恢复观察已有任务（不会重新提交）：

```sh
python3 proofs/validation/eq17286-formal/remote_judge.py 17286 --wait
python3 proofs/validation/eq17286-formal/remote_judge.py 28626 --wait
```

初次执行使用同一命令加 `--submit`。脚本先保存请求和提交状态，再发送；已有任务只查询既存 ID，POST 结果不确定时禁止自动重发。若重新观察导致归档状态文件变化，用 `record_remote.py` 重新审计并登记文件哈希。

本地 `summary.json` 仍准确保留当时八单元构建未调用远端的事实；远端验收记录另存。有限平凡性沿用已经归档的证明与日志，这次未重新提交有限侧证书。
