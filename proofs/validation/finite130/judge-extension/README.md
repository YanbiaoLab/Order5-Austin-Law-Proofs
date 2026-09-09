# judge-v3-repl 有限目标支持提案

状态：本地补丁和测试已准备；未修改服务仓库，未部署极光云，有限目标云端 accepted 为 0。

[finite-domain.patch](finite-domain.patch) 修改 judge-v3-repl 的五个 Python 文件并增加一份测试文件。[patch-manifest.json](patch-manifest.json) 绑定原文件、补丁、测试结果和 Lean 审计的 SHA-256；补丁已通过服务仓库中的 `git apply --check`。

请求新增顶层字段 `model_domain`，仅接受 `all`、`finite`，默认仍为 `all`。有限目标由 judge 生成：

```lean
-- model_domain = "finite", verdict = "true"
∀ (G : Type) [Magma G] [Finite G], EquationLHS G → EquationRHS G

-- model_domain = "finite", verdict = "false"
∃ (G : Type) (_ : Magma G) (_ : Finite G), EquationLHS G ∧ ¬ EquationRHS G
```

有限模式的默认声明白名单增加目标所需的 `Finite` 和 `Finite.`；公理白名单不变，显式提供的证明策略不变。域参与缓存键、持久化请求和派发；worker 通过健康检查声明支持的域，control 拒绝将有限请求发给旧 worker，并核对结果返回的域。原有全体模型目标不变。

验证证据：

- [Python 测试日志](python-tests.log)：有限域测试以及原 verifier、worker runtime、control runtime、control cache 回归测试合计 80 项通过；其中模拟后端仅用于验证接口流程。
- [114 份实际 Lean 检查](kernel/all-finite-summary.json)：每题分别编译 judge 生成的有限目标、完整证书，以及在独立模块中的目标类型检查和公理／声明依赖报告。均通过官方策略检查，无额外公理。
- [三个对照](kernel/controls-summary.json)：同一有限证明用于全体模型目标或无关有限目标均被 Lean 拒绝；明确携带 `Finite Bool` 的两元素反例通过本地检查。
- [真实原生 REPL 检查](repl-integration/summary.json)：通过本地 worker 的 ASGI `/verify` 接口，使用生产代码中的定制 `stage2-staged-v2` 入口实际执行 Lean。Equation4916、Equation5093、Equation18137 的有限证明及 Bool 有限反例获 accepted；全体模型及无关有限目标两项获 LEAN_REJECTED。新增表 20.3 的八份有限证书随后也全部获 accepted，共 14 项检查符合预期。八个新增 REPL 进程的最高采样 RSS 为 2824.94 MiB，低于 3072 MiB 停止阈值。不是模拟后端结果。[构建清单](repl-build/manifest.json) 固定上游 REPL 提交、定制入口和原生二进制哈希。
- `kernel/summary.json` 是增加有限域默认声明策略之前的诊断记录；其中 `Finite` 被拒绝的结果用于定位问题，不代表最终验证结果。最终结果以 `all-finite-summary.json` 和 `controls-summary.json` 为准。

Lean 编译串行运行，内存参数 2048 MiB，采样 RSS 超过 3072 MiB 则停止；原生 REPL 执行也有 3072 MiB 的 RSS 停止限制。峰值见补丁清单及构建记录。解释执行入口的两次尝试触及 2 GiB 限制，原生构建随后成功；失败诊断单独保存在 `repl-integration/*attempt.json`。本地检查覆盖了定制 REPL 和 worker ASGI 接口，尚未覆盖极光云网络链路与 Linux 发布镜像，因此不能称为极光云验收。

[requests-manifest.json](requests-manifest.json) 按表 20.1、20.2、20.3 排序，恰好列出 114 个已检查、尚未提交的真实有限目标请求。`requests/` 另有负面对照请求，批量提交时必须使用清单，不能直接遍历整个目录。每个请求携带完整有限定理及其到 `submission : Goal` 的直接引用，题目仍为原方程推出 Equation2。

后续上线需要服务维护授权。建议先建立独立、单 worker 的有限目标验证实例，固定镜像版本并验证新域的正负对照；通过后再串行验收 114 个请求。发布前应核对现有部署的资源和访问配置。Linux 镜像构建、Harbor 上传、服务重启均尚未执行。

`export_patch.py` 可从已测试的 `.build/judge-finite-extension` 副本重建补丁和清单；它校验服务源文件未变化，不写入服务仓库。
