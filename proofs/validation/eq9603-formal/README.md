# E9603／E36514 Lean 形式化验收

7 个编译单元全部通过 Lean 4.33.1；包含轨迹大小界、解码唯一性、非解码分支排除、两条原等式、Nat 单射及两份精确 Goal。

全部核心引理由 Lean 检查。Step 是允许原始配对或已证明解码的关系；实际乘法只在存在 Code 时解码，否则配对。每个强制配对分支均另外证明没有 Code。

`eval` 通过经典选择判断并选取 Code 输出，已证明输出唯一；这是全函数，但当前实现使用 noncomputable，未额外形式化可执行判定器。最终定理公理列表仅含标准的 `propext`、`Classical.choice`、`Quot.sound` 的子集。

本次分模块检查采样峰值 644.81 MiB，累计 2.356 秒。
单进程、单线程、`-M768`，每 0.2 秒监测 RSS，超过 1024 MiB 停止。
本批本地检查采用分模块编译，没有对合并文件提高内存限额进行本地编译。
本地最终证书导入经过检查的模块；远程提交包含这些模块的原文，远程状态见[独立验收记录](../aurora/README.md)。

复跑：`python3 scripts/trace_models.py check 9603`。
完整源码哈希、命令和退出码见 [summary.json](summary.json)；核心公理列表见 [Audit.log](Audit.log)。
