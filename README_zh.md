# 刚性超图与无界 GHZ 维数的 Lean 形式化

形式化作者及责任维护者：**Xizhi Liu**。

公开仓库：[xliu2022/GHZ-unbounded-lean](https://github.com/xliu2022/GHZ-unbounded-lean)。英文说明见 [README.md](README.md)。

本项目形式化 Heng Li 与 Xizhi Liu 的论文 *Unbounded GHZ dimension from fixed-order multiphoton sources* 及部分补充结果。数学原文保存在 [paper/](paper/)。证明开发使用了 AI，具体贡献及验证范围见 [PRODUCTION.md](PRODUCTION.md)。项目代码采用 Apache-2.0；数学来源与外部依赖保留各自的权利及许可证。

## 数学内容

输出路径对应超图顶点，发出 `r` 个光子的光源对应一条含 `r` 个顶点的超边。每条路径恰好收到一个光子的发射组合，对应超图的完美匹配。非空顶点集上的 `d`-刚性超图恰好有 `d` 个完美匹配，它们的边集两两不交并覆盖全部超边。

主要结果包括：

- 对每个固定的 `r ≥ 3` 和每个正整数 `m`，构造平衡 `r` 部超图，在 `n = r*m` 条路径上实现维数至少为 `(m / (128*(r-2)^3))^(2*(r-2)/7)` 的 GHZ 态。
- 指定恰好 `d ≥ 2` 个分支的构造，以及源数量、加权影子不等式和对数上界。
- 精确极值 `f_3(6)=10`、`f_3(9)=13`、`g_3(3)=6`，以及平衡九顶点极值例子的唯一性。
- 在独立相干二元光源和精确光子数后选择模型下，证明归一化、态的支撑、相位校正，以及等权 GHZ 态的最优发射概率 `1/d`。

物理结论使用论文明确给出的模型假设。有限极值的部分证明使用经 Lean 重建的 SAT/LRAT 证书；外部求解器的返回值本身不作为公理。论文与形式化逐项对应、替代证明和未单独形式化的内容见 [COVERAGE_AUDIT.md](COVERAGE_AUDIT.md)。

## 源码组织

| 路径 | 内容 |
| --- | --- |
| `RigidGHZ/Basic.lean` | 超图、完美匹配和刚性定义 |
| `RigidGHZ/Selector/`、`Construction/` | 排除混合匹配的构造及定量估计 |
| `RigidGHZ/UpperBounds/` | 一般上界和渐近结果 |
| `RigidGHZ/Finite/` | 有限极值、明确例子和计算证书 |
| `RigidGHZ/SourceModel/` | 光源态、后选择、GHZ 态及成功概率 |
| `RigidGHZ/Supplement/` | 补充构造与存在性阈值 |
| `scripts/`、`verification/` | 复现脚本与保存的验证证据 |

`Challenge` 模块独立陈述定理，`Solution` 模块导入实际证明。Challenge 中的 `sorry` 是有意保留的陈述占位符，Solution 不导入 Challenge。证明模块不允许这些占位符、自定义公理或原生计算证明捷径。

## 验证与复现

项目固定 Lean `v4.35.0-rc2` 和 Mathlib 提交 `065356127b1dc0016f66b7283ce0ce2c4055aa55`。安装 Lean/Lake 与 Python 3.11 或更新版本后，在仓库根目录运行：

```sh
python3 scripts/check_source.py --require-metadata
lake exe cache get
python3 scripts/build_serial.py --all
```

串行构建默认覆盖三个主要 Challenge/Solution 配置，减少同时编译大型证书造成的内存压力。若需要全部保留的补充开发，显式添加 `--include-supplement`。

重新执行本地陈述比较、公理审计和独立内核检查：

```sh
python3 scripts/check_exports.py comparator.json
python3 scripts/check_exports.py comparator-finite.json
python3 scripts/check_exports.py comparator-physics.json
```

保存的报告显示，这三个配置的共 20 个定理已通过本地陈述比较、公理检查、Lean 内核和 NanoDa 检查。可选的 `comparator-supplement.json` 尚无完整的独立重放通过记录，不属于本次主要提交范围。具体状态见 [STATUS.md](STATUS.md)。

## Palomar 提交

仓库根目录是 Lean 项目根目录，正式元数据是 `formalization.yaml`。三份主要配置对应三次独立提交：

| 配置 | 定理数 | 范围 |
| --- | ---: | --- |
| `comparator.json` | 9 | 构造、指定维数及一般上界 |
| `comparator-finite.json` | 4 | 有限精确极值及唯一性 |
| `comparator-physics.json` | 7 | 光源模型、GHZ 实现及最优概率 |

[完整机械预检工作流](https://github.com/xliu2022/GHZ-unbounded-lean/actions/workflows/palomar-preflight.yml) 调用固定版本的 Palomar 官方验证器，使用 `mode: full` 和 `palomar-standard-v1`。提交前应确认所选配置在准备提交的完整 40 位 commit SHA 上取得 `status: pass`。本地验证报告和工作流文件本身不能代替该结果。

详细填写信息见 [SUBMISSION.md](SUBMISSION.md)。正式提交入口是 <https://submit.palomar-registry.org/>。完整机械预检不执行注册；编辑审核和最终注册由责任维护者随后完成。
