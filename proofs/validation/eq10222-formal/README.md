# E10222／E35836 完整无限模型核验

两条精确原式、非平凡性和显式 Nat 单射全部通过本地 Lean 4.33.1。
15 个编译单元通过：九个核心模块、两个 Goal、两个模型包装、两份独立单文件证书。
本批没有远程提交。

关键端点：`Austin10222Unit.inverse_sound`、`inverse_complete`、`right_injective`、
`mul_normal`、`column_double_cases`、`carrier_source`、`carrier_dual`、
`carrier_nontrivial`、`embed_injective`，以及两份证书的 `submission`、
`submission.CM.tower_injective`。

载体是正规树子类型；乘法封闭性已证明。不能把结论换成未经约化的全部树。
全称证明没有有限采样假设，Python 不在信任基础内；没有 `sorry` 或自定义公理。
完整公理列表在各日志及 [summary.json](summary.json)，最终定理只依赖 `propext` 和 `Quot.sound`。

两份独立证书包含精确 Goal、全部核心定义与证明，只导入 Lean 标准库。
核验使用空项目搜索目录，从而不依赖项目 `.olean`：
[E10222 单文件](Equation10222/certificate.lean)、[E35836 单文件](Equation35836/certificate.lean)。

所有编译串行、单线程、`-M256`；每单元超过 RSS 384 MiB 或 120 秒停止。
本次累计 10.169 秒，0.2 秒间隔采样的最高 RSS 为 243.19 MiB。
快速检查可能错过实际峰值，不将采样值当作严格上界。

以上为原研究环境的验证结果。本次归档的核对方法见[2026-09-11 报告](../2026-09-11-ten-austin/README.md)；原命令与路径保留在 JSON 中。
源码、日志、输出模块哈希与命令均已归档；打包脚本逐模块保留研究实现正文，只调整导入路径。
模型定义与原式证明见 [UnitLaw.lean](../../Equation10222/Lean/Austin10222/UnitLaw.lean)。
