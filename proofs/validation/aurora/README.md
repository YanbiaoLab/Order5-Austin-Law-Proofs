# 极光云 judge-v3-repl 验证

只记录服务实际返回的 accepted；本地 Lean 通过、搜索完成和请求已入队均不代替远程验收。

| 方程 | 任务 ID | 结果 | 实际提交证书 |
|---|---|---|---|
| Equation11205 | `6c838116ef2e4be4ad7c2f4718927173` | [accepted](Equation11205/latest.json) | [Lean](Equation11205/certificate.lean) |
| Equation11280 | `d22c3dc261bf4855826905e90096e5ac` | [accepted](Equation11280/latest.json) | [Lean](Equation11280/certificate.lean) |
| Equation12073 | `5745f8cde49a4647b810ce183d6f5d91` | [accepted](Equation12073/latest.json) | [Lean](Equation12073/certificate.lean) |
| Equation12857 | `f343d53fdad6449cb0162cbcdb71a8dc` | [accepted](Equation12857/attempt02/latest.json) | [Lean](Equation12857/attempt02/certificate.lean) |
| Equation13764 | `f2b2acd87bfb463fa5628eec6cb3657b` | [accepted](Equation13764/latest.json) | [Lean](Equation13764/certificate.lean) |
| Equation13849 | `f59910cf5ef94eba9c133ba355fe5e33` | [accepted](Equation13849/latest.json) | [Lean](Equation13849/certificate.lean) |
| Equation13992 | `d188d697d8cd4bcc8cda676b1f3e42dc` | [accepted](Equation13992/latest.json) | [Lean](Equation13992/certificate.lean) |
| Equation18212 | `a8304b9078974beba599f81ca08dffc0` | [accepted](Equation18212/latest.json) | [Lean](Equation18212/certificate.lean) |
| Equation27859 | `9fb709bdc4bc4834a0e02a9e59b908a8` | [accepted](Equation27859/latest.json) | [Lean](Equation27859/certificate.lean) |
| Equation32280 | `e9621dc79d584d90a3aba854cd4cdeae` | [accepted](Equation32280/latest.json) | [Lean](Equation32280/certificate.lean) |
| Equation32281 | `e725b72b99d94e498b5c4b311f2ad6e6` | [accepted](Equation32281/latest.json) | [Lean](Equation32281/certificate.lean) |
| Equation32294 | `bba25eec9fa449879927d39b73b505f6` | [accepted](Equation32294/latest.json) | [Lean](Equation32294/certificate.lean) |
| Equation33436 | `30f2f241005a49849b4e416111c52582` | [accepted](Equation33436/latest.json) | [Lean](Equation33436/certificate.lean) |
| Equation33998 | `b3017123e7b64c3dbba4b456ac1f3cc8` | [accepted](Equation33998/latest.json) | [Lean](Equation33998/certificate.lean) |
| Equation34778 | `ac2267430eee4217bb11281d6fbd3cc4` | [accepted](Equation34778/latest.json) | [Lean](Equation34778/certificate.lean) |
| Equation35100 | `db77c6fa397e4c988afd0be3f263b9c4` | [accepted](Equation35100/latest.json) | [Lean](Equation35100/certificate.lean) |
| Equation36514 | `eb5508e6080f4aea815fd29fb9568ac3` | [accepted](Equation36514/latest.json) | [Lean](Equation36514/certificate.lean) |
| Equation36524 | `19c99c9affe24b8d8e00bf102f05bd05` | [accepted](Equation36524/latest.json) | [Lean](Equation36524/certificate.lean) |
| Equation38565 | `609c63203f4c4bdeb36d26297b69cc8b` | [accepted](Equation38565/latest.json) | [Lean](Equation38565/certificate.lean) |
| Equation40070 | `3275d1edba4344d18b172d5f779c0419` | [accepted](Equation40070/latest.json) | [Lean](Equation40070/certificate.lean) |
| Equation40221 | `9d802ff6f9fd4845b524a999020d45ef` | [accepted](Equation40221/latest.json) | [Lean](Equation40221/certificate.lean) |
| Equation5833 | `bbf2a747c9c743278bc05c65fe609009` | [accepted](Equation5833/latest.json) | [Lean](Equation5833/certificate.lean) |
| Equation5837 | `3b3ac54967e2476a9f4e2963e205a5c2` | [accepted](Equation5837/latest.json) | [Lean](Equation5837/certificate.lean) |
| Equation7763 | `e512171e0e734745b0219924f84f0438` | [accepted](Equation7763/latest.json) | [Lean](Equation7763/certificate.lean) |
| Equation9603 | `ac40e63a812d4a19b34e62bff599b4ca` | [accepted](Equation9603/latest.json) | [Lean](Equation9603/certificate.lean) |
| Equation9680 | `ffb84e7cf57341cc949fd85f8440e636` | [accepted](Equation9680/latest.json) | [Lean](Equation9680/certificate.lean) |

Equation12857 的首次提交因辅助声明命名不符合默认白名单而被拒绝，相关失败记录保留。后续把自建定义放入官方允许的 submission 命名空间，使用明确的 Magma 实例和 Nat.noConfusion 后通过；未更改 judge 的证明策略。
