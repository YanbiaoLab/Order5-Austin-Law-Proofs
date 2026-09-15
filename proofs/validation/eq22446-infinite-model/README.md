# E22446 模型与证书核验

2026-09-15。模型源码、完整导出证书和远端回执均已核验。

- 模块化模型：58 个模块从空目录用 Lean 4.33.1 串行重建通过。
- 公理审计：291 条报告覆盖 290 个不同声明；最终包装再次检查合并模型定理。
- 精确端点：`submission`、`submission.source_law`、`submission.nontrivial`、`submission.CM.tower_injective`。
- 自然数单射不依赖任何公理；其余最终端点只用 `propext`、`Classical.choice`、`Quot.sound`。
- 无 `sorry`、新公理、未证明的 Source 或唯一性前提。

[原始本机记录](summary.json)、[导出后 58 个分段核验](../eq22446-judge-export-v2/summary.json)、
[远端完整证书验收](../aurora/Equation22446/README.md)、[模型说明](../../Equation22446/MODEL.zh-CN.md)。
原始记录中的绝对命令路径描述当时环境；归档文件均由仓库相对路径和 SHA-256 绑定。
导出器及分段核验器的当时源码副本保存在 `../eq22446-judge-export-v2/provenance/`，
用于核对原始清单里的脚本哈希；本归档不依赖仓库根目录的 `scripts/`。

只读核验，不启动 Lean 或远端任务：

```sh
python3 proofs/validation/eq22446-infinite-model/verify.py
```

重建模块化模型（需要已安装的 Lean 4.33.1）：

```sh
python3 proofs/validation/eq22446-infinite-model/compile.py
```

编译按已核验依赖顺序串行执行，使用 `-j1 -M192`，每模块最多 120 秒，
采样 RSS 达 256 MiB 时终止进程组。每次使用新的临时构建目录，结束后删除编译输出。
本次还用上述入口在独立提交目录重新构建 58 个模块，全部通过；[重建记录](publication-rebuild.log)保留运行输出。远端验收使用已保存的实际回执，本次没有重复提交。
本机未编译完整单文件；该文件由远端 Judge 实际编译并接受。

有限侧只核对既有源码与原始日志，未重新编译 Mathlib，也未提交有限侧远端任务。
旧构造的研究记录与完整模型的验证范围明确区分；本归档只包含最终模型所需的依赖。
