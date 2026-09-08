# solo_v9_v1 Austin-130 验收报告

结论：**通过**。

## 总览

- 精确覆盖：130/130
- 已解决：42/130（false 42，true 0）
- 旧版 38 题保留：38/38
- 完整对偶对：21/65
- 运行 provenance 分组：2

## Blueprint 表

| 表 | 已解决 | 总数 | false | true | 干净未解 | 运行故障 |
|---|---:|---:|---:|---:|---:|---:|
| 20.1 | 10 | 10 | 10 | 0 | 0 | 0 |
| 20.2 | 30 | 96 | 30 | 0 | 66 | 0 |
| 20.3 | 2 | 24 | 2 | 0 | 22 | 0 |

## 发布门槛

- PASS — `exact_austin_130_coverage`
- PASS — `Equation15535`
- PASS — `Equation30591`
- PASS — `legacy_solved_retained`
- PASS — `austin_130_solved_minimum`
- PASS — `complete_dual_pairs_minimum`
- PASS — `blueprint_table_20_1`
- PASS — `blueprint_table_20_2`
- PASS — `blueprint_table_20_3`
- PASS — `operational_integrity`
- PASS — `accepted_certificate_attempt_provenance`

## 回归差异

- 丢失的旧解：无
- 新增解：Equation15535、Equation30591、Equation19966、Equation26105

## 完整性口径

仅 `status == accepted`、严格墙钟内完成且证书、Judge attempt、官方执行指纹（official execution fingerprint）一致的结果计为已解决。
输入结果可来自多个 shard；验收索引始终恢复为 Blueprint 的固定 130 题顺序。
