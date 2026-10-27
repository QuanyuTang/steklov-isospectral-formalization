# 严格凸 Steklov 等谱平面区域：Lean 形式化

**作者：[Tao Hu](https://github.com/taohu-hub)、[Jiachen Shi](https://github.com/RGConj)、[Quanyu Tang](https://github.com/QuanyuTang)。**

[![Lean 验证](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/lean.yml?query=branch%3Amain)
[![Palomar Comparator](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/palomar.yml/badge.svg?branch=main)](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/palomar.yml?query=branch%3Amain)

**已核验的证明快照：** 提交 `6932e18512a7` 已在 Lean 4.35.0-rc2 下完成全部 176 模块的无项目缓存编译、590 目标类型与公理审计，并通过沙箱中 bundled Lean 和 NanoDa 双内核复核。con-ron 也接受了证明。 [当前状态](PALOMAR_STATUS.md) · [准确证据](docs/lean435-build-audit-evidence.json)

**Hu–Shi–Tang 论文定理 1.1.2 的 Lean 4 形式化，采用显式七次多项式构造。**

[English](README.md) · [论文](https://arxiv.org/abs/2608.10557v2) · [独立定理陈述](Challenge.lean) · [证明入口](Solution.lean)

该工程证明：存在单参数平面区域对族 `(Ω P ε, Ω L ε)`，对每个相同参数 `ε`，这一对区域的 Steklov 谱完全相同（包含重数）；不同标签或不同参数对应的区域彼此不全等。每个区域都有界、单连通、严格凸，边界为实解析 Jordan 曲线；周长均为 2π，没有反向欧氏对称，归一化共形映射在 C∞ 意义下趋于恒等映射。

这回答了 Dirichlet-to-Neumann 算子的逆谱几何问题：即便限制在任意接近圆盘的严格凸解析平面区域中，完整 Steklov 谱仍不能在欧氏全等意义下确定区域形状。相关研究领域包括谱几何、反问题和复分析。

## 核验与范围

- 176 个可编译的 Lean 库模块与 4 份保留的原始审计模板（共 180 份原始源码），`RequestProject/` 中没有 `sorry`、`admit` 或新增数学公理。
- 原始基线核验环境：Lean **4.28.0**；Mathlib 固定为 `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
- 原始基线发布布局已在独立目录中完整编译通过（8206 个任务），590 个不同导出审计目标均只依赖三个标准公理。[基线核验报告](verification/package-verification.json)、[构建日志](verification/package-build.log)、[审计日志](verification/package-audit.log) 均随包提供；590 是审计声明数，不是独立数学定理数。
- 已核验提交 `6932e18512a776e4edae15bc076f4224ec85e4ad` 在目标 Lean **4.35.0-rc2**、canonical Mathlib 下通过无项目缓存的完整编译、590 目标审计、元数据和源码检查，以及 Lean、NanoDa 双内核复核。后续提交仍须各自重新通过 CI；这些结果不等于 Palomar 已核验或登记。[准确记录](docs/lean435-build-audit-evidence.json)
- 主定理的五项结论全部包含；更强入口 `SteklovCoalescence.mainTheoremClassical_proved` 连接弱 Sobolev 谱与经典调和 PDE 的 Steklov 边界条件。
- 仅使用 `propext`（命题外延性）、`Classical.choice`（经典选择）、`Quot.sound`（商类型等价代表元的相等性）。没有把论文结论作为公理。

证明采用显式七次多项式及实际单值群数据。没有形式化任意置换数据的一般 Riemann 存在定理；轨形采用经证明的具体圆盘坐标模型。不能将本项目宣传为“论文提到的所有一般理论均已形式化”。详细对应见 [RESULTS.md](docs/RESULTS.md)。

## 复现

安装 elan、Git 与 Lean 支持的 C/C++ 工具链后，在本目录执行：

```sh
python3 -m pip install jsonschema==4.25.1
python3 scripts/validate-metadata.py
lake exe cache get
lake build
python3 scripts/audit.py
python3 scripts/check-release.py
```

`Challenge.lean` 是只导入 Mathlib 的独立陈述文件，其中有 **一个有意保留的 `sorry`**，用于 Palomar 的陈述与证明对比机制。实际证明位于 `Solution.lean` 和 `RequestProject/`，不导入该陈述文件。这个占位不属于主定理证明。

主动修改仓库文件后，运行 `python3 scripts/refresh-release.py`，同时更新源码校验清单、结构报告和发布清单，再重新核验。投稿时应核对**实际提交的完整 SHA** 对应的两项 CI 结果；其他提交的绿色徽章不能替代它。[本次源码审查记录](verification/final-review.json) 明确列出了核查范围与限制。

## GitHub 发布与 Palomar

本仓库的根目录就是投稿项目根目录；无需再上传 ZIP 或嵌套一层 `formalization/`。原始论文 PDF、TeX 和原始源码包位于 `paper/`。

**记录的证明快照已通过所需本地准备检查。** con-ron 也接受了证明。 原始 Lean 4.28 日志只核验原基线；目标版本以精确提交的 CI 记录为准。仓库公开、实际投稿及永久登记仍须项目所有者最终批准。[当前状态](PALOMAR_STATUS.md)

Palomar 使用公开 GitHub 仓库及完整 commit SHA 进行审查，并不是直接接收 ZIP。发布和后续提交步骤见 [PALOMAR.md](docs/PALOMAR.md)。本项目目前**没有获得 Palomar 核验、登记或背书**。

## 署名、AI 使用与许可

仓库维护者：[Tao Hu](https://github.com/taohu-hub)、[Jiachen Shi](https://github.com/RGConj)、[Quanyu Tang](https://github.com/QuanyuTang)。形式化主要使用 **Aristotle（Harmonic）** 生成证明，**OpenAI Codex** 用于组织工作、补充中间步骤、核验与整理。详见 [PROVENANCE.md](docs/PROVENANCE.md)。

原论文作者为 **Tao Hu、Jiachen Shi、Quanyu Tang**。据维护者说明，作者已人工审阅论文并对数学结论负责；这与 Lean 形式化的独立人工审查是两回事。本仓库不宣称已获得对形式化代码的独立人工审稿。

## 原文差异记录

[差异记录](docs/ERRATA-AND-DEVIATIONS.md) 不主张论文存在勘误，记录四项形式化选择：显式多项式构造、具体度量轨形模型、加权圆盘谱证明路线，以及带有已证 PDE 桥接的变分谱编码。主定理五项结论均保留。[第三方工具归属](docs/THIRD_PARTY_NOTICES.md) 另行列明。

形式化代码和新增文档采用 **Apache-2.0**。`paper/` 中的论文文件保留原作者权利，不适用本仓库的代码许可；arXiv 页面显示的是授予 arXiv 的非独占传播许可，不是通用的开放再利用许可。见 [论文来源与权利说明](paper/README.md)。
