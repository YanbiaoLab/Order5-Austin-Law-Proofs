**Equation17286 / Equation28626：完整无限模型本地与远端核验**

2026-09-14，两条精确原式、非平凡性及自然数单射均通过 Lean 4.33.1。
结合已经归档的有限平凡性证明，两条方程均确认为 Austin 律。随后两份独立证书均经远端 Judge 首次提交返回 **ACCEPTED**，见[远端验收与审计](JUDGE.md)。

| 构建 | 单元数 | 结果 |
|---|---:|---|
| TreeSchema / TreeBounds / TreeGeometry / TreeModel | 4 | 全部通过 |
| E17286 精确题面与独立展平证书 | 2 | 全部通过 |
| E28626 精确题面与独立展平证书 | 2 | 全部通过 |

三个空构建目录彼此独立，没有复用研究目录或其它模型的 `.olean`。两个独立证书只导入本地精确 `JudgeProblem` 与最小 Lean 标准库，不导入树模型模块。

核心检查包含 25 个公理审计端点；每份独立证书另审计 `submission : Goal`、`submission.CM.tower_injective` 和对应的完整 `infinite_model` 定理。全部公理依赖均属于 `propext`、`Classical.choice`、`Quot.sound`；没有占位证明、自定义公理、原式以外的模型假设或外部求解器断言。

`Goal` 精确要求同一个 magma 满足对应原式且不满足 `∀x y,x=y`。自然数单射另单列检查，完整存在定理将原式与单射绑定到同一运算。E28626 使用反向运算并核对实际变量排列。

```sh
python3 proofs/validation/eq17286-formal/verify.py
python3 proofs/validation/eq17286-formal/audit.py
```

第一条重新编译全部八个单元，刷新 [summary.json](summary.json) 与日志；第二条只读核对归档、精确公式和索引。修改核心后可先用 [export_certificate.py](export_certificate.py) 重生成两份独立证书，再核验；通过后用 [record_index.py](record_index.py) 登记本批证据。

所有编译串行，Lean 单线程、128 MiB 内部限制，进程树 RSS 停止线 192 MiB，单元时间上限 30 秒，每 0.05 秒采样。最终构建约 1.21 秒、采样峰值约 119.70 MiB。关闭展平证书的异步 elaboration 后，保持原内存上限通过；编译目录均已清理。周期采样不是瞬时峰值保证。

新增证书：[E17286](../../Equation17286/InfiniteModel.lean)、[E28626](../../Equation28626/InfiniteModel.lean)；[构造、证明和成功复盘](../../Equation17286/MODEL.zh-CN.md)。旧有限证书未修改，本轮只核对其已归档证据。
