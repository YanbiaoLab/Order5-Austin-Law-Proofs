# E12857／E33436 的 Lean 形式化

状态：**已在 Lean 4.33.1 编译通过，最终定理已检查公理依赖。**

本目录形式化的是两张截图启发的独立重写模型，不声称与嘉铭未提供的原始规则相同。

| 文件 | 内容 |
|---|---|
| [Basic.lean](Basic.lean) | 有限树、10 条规则、任意位置的重写、多步归约；严格减小节点数 |
| Peak1.lean–Peak10.lean | 每条根部规则与任意一步重写的分歧都可汇合，包括重复变量内部的重写 |
| [Confluence.lean](Confluence.lean) | 任意局部分歧可汇合；大小归纳证明规范形存在、唯一及全局汇合 |
| [Model.lean](Model.lean) | 规范树载体和乘法；E12857、E33436；显式 Nat 单射 |
| [Audit.lean](Audit.lean) | 核对定理类型及其传递公理依赖 |

`Austin12857.infinite_model` 无模型成立、汇合性或无限性等外部假设。其结论同时给出一个类型、二元运算、满足 E12857 的全称证明，以及从自然数到载体的单射。`equation33436` 使用同一载体上的反向乘法。

`Peak*.lean` 由 `scripts/generate_12857_lean.py` 生成普通证明文本。Lean 自己检查所有分类分支和每一步归约，Python 结果不作为公理。最终依赖仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx`、自定义公理或 `native_decide` 信任捷径。

`norm` 使用经典选择从已证明存在且唯一的规范形中选取；这与数学构造的规范化函数定义相同。当前证明给出了无限性（Nat 单射），未另行形式化可数性的上界，也未新增有限侧坍缩定理。

从项目根目录复跑：

```sh
python3 scripts/check_12857_lean.py
python3 scripts/record_12857_formal.py
python3 scripts/build_index.py --check
```

可选地先运行 `python3 scripts/generate_12857_lean.py` 再复跑，重新生成冲突处理证明。需要已安装 Lean 4.33.1，不需要 Mathlib。一次一个编译进程，Lean 上限 768 MiB，RSS 采样停止线 1024 MiB，每文件最多 120 秒。完整命令、日志与源码哈希见[形式化报告](../../validation/eq12857-formal/README.md)。

标准 `Goal` 包装分别在 [E12857](../InfiniteModel.lean) 和 [E33436](../../Equation33436/InfiniteModel.lean)，都已实际编译，不能仅凭对偶关系推断文件已验收。此次是本地 Lean 内核验证，没有重新提交官方 Judge。
