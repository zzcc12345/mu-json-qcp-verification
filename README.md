# mu_json 的 QCP 程序验证

本项目使用 QCP 和 Rocq/Coq，对 C 语言 JSON 解析模块 `mu_json.c` 进行增量程序验证。工作包括函数规约设计、循环不变量标注、证明义务生成及手工证明。

当前仍处于部分验证阶段：以包含全部 48 个函数的适配版 C 文件作为输入，已覆盖其中 23 个函数。未标注的函数不因整文件检查通过而自动成为已验证函数。

## 验证对象

上游项目：[rdpoor/mu_json](https://github.com/rdpoor/mu_json)。选取的源码版本为：

```text
e9050ff0d75ea2bfa2bdfa835cc1d5a2f5666631
```

`mu_json.c` 负责扫描 JSON 输入并生成调用方提供的 token 数组，包括基本值解析、对象和数组解析，以及 token 查询和遍历。它记录原输入中的子串范围，不直接将数字转换为 C 数值，也不构造动态分配的对象树。

本项目主要验证解析模块；独立的 JSON 生成模块 `mu_jems.c` 不在当前验证范围内。

## 当前进度

截至 2026-10-28：

| 项目 | 结果 |
| --- | ---: |
| 输入文件中的函数数 | 48 |
| 已覆盖函数数 | 23 |
| 待验证函数数 | 25 |
| 最终接口要求的主证明义务 | 182 |
| QCP 自动路径义务 | 174 |
| 已完成的手工主义务 | 8 |
| manual 文件中的 lemma 数 | 18 |

手工证明文件包含 **8 个主目标 lemma 和 10 个分拆目标 lemma**，均以 `Qed` 结束，manual 中无 `Admitted`。分拆 lemma 是完成主目标的子证明，因此 lemma 数与主义务数不同。

自动证明文件保留 QCP 既定生成机制中的 `Admitted` 占位。本项目将这部分记为“QCP 自动路径通过”，不将其描述为已经生成了 174 项不依赖占位的 Rocq 内核证明项。

当前成果通过了对应工作区中的手工分组检查、完整证明汇总编译及独立义务重放。最近完成的验证 run 为 `mu_json-20261028113238`。

### 已覆盖函数

| 分类 | 函数 |
| --- | --- |
| 字符分类 | `is_digit`、`is_hex`、`is_number_prefix` |
| 输入位置与读取 | `at_eos`、`peek_char`、`get_char`、`ref_char` |
| 空白扫描 | `skip_whitespace` |
| 内部 token 判断 | `token_is_null`、`token_is_first`、`token_is_last` |
| 文本地址操作 | `set_token_string`、`get_token_string`、`mu_json_token_string` |
| 公开属性查询 | `mu_json_token_string_length`、`mu_json_token_type`、`mu_json_token_level`、`mu_json_token_is_first`、`mu_json_token_is_last` |
| 打包字段设置 | `set_token_string_length`、`set_token_type`、`set_token_level`、`set_token_is_last` |

其中，`skip_whitespace` 的规约描述完整的连续 JSON 空白前缀：已消费的字节均为允许的空白，退出时到达输入末尾或第一个非空白字符，并保持输入内容不变。字符读取函数在有效缓冲区和位置条件下证明读取安全及位置变化。

具体顺序和历史记录见 [验证计划与进度](docs/verification_order.md)。

## 目录说明

```text
.
├── README.md
├── mu_json-main/               下载的上游项目副本，含早期 is_digit 标注
├── dependencies/               固定版本的 mu_log、mu_str 依赖及来源记录
├── qcp_compat/                 兼容性转换候选与说明，可能落后于当前标注
├── verification/               当前通过检查的验证成果
│   ├── mu_json.c
│   ├── mu_json_goal.v
│   ├── mu_json_proof_auto.v
│   ├── mu_json_proof_manual.v
│   └── mu_json_goal_check.v
├── docs/
│   └── verification_order.md
├── build_native.py             原生编译与回归测试脚本
├── prepare_qcp_compat.py        兼容性转换和前端预检脚本
└── verification_preparation.md 初始准备记录
```

**查看最新规约和证明时，以 `verification/` 为准。** 下载目录和较早的兼容性候选不包含所有后续标注。不要重新生成旧候选后直接覆盖当前验证成果。

`mu_json_goal.v` 保存生成的证明目标，`mu_json_proof_auto.v` 保存自动部分，`mu_json_proof_manual.v` 保存手工证明，`mu_json_goal_check.v` 汇总检查最终证明接口。所有函数共同使用这套文件，无须每个函数单独建一套。

## 适配方式与结论边界

为适应当前 QCP 前端，本项目使用了独立的适配版本，主要处理：

- 展开宏、明确数组长度、规范化部分表达式和语句。
- 将原 token 位域表示为一个 32 位打包字段，通过掩码和移位读写。
- 从验证版本中排除诊断日志调用。

适配候选以 GCC 小端位域布局、32 位 `unsigned int` 为目标假设。字段设置规约覆盖相应截断行为，并保留其他字段所占位。

**当前证明针对适配版，不等同于原始位域程序的完整验证。** 原位域与打包表示、相关源代码变换的形式化对应证明尚未完成；有限布局测试不替代该证明。日志输出、日志回调和日志参数求值也不在当前验证范围内。

函数正确性结论均依赖各自的前置条件，包括字段所有权、有效输入数组、可读写范围及整数范围。尚未完成对象/数组互递归、完整 token 树及全部错误路径的组合证明，也不声称支持所有标准 JSON 输入。

## 环境与复现状态

现有结果在 Windows、Python 3.12、QCP 二进制及 Coq Platform 8.20 系列工作区中生成。Rocq 文件依赖 QCP 的逻辑库、策略和逻辑路径；不能假定仅对这四个 `.v` 文件直接运行 `coqc` 就能编译。

工作区中的路径约定为：

```text
QCP_examples/QCP_demos_LLM/mu_json/mu_json.c
Rocq/examples/QCP_demos_LLM/mu_json/mu_json_*.v
```

检查当前成果需要：

1. 准备相匹配的 QCP/Rocq 工作区及其基础库依赖。
2. 将本项目的验证输入和证明文件放入对应逻辑路径。
3. 使用工作区的 verification-orchestrator 流程重新生成义务，并与保存的证明目标比对。
4. 编译手工证明及汇总接口，执行最终独立重放。

重新生成的 manual 模板应放入临时目录，不能覆盖已经完成的手工证明。

**尚未整理独立的一键证明复现入口。** 当前两个 Python 脚本包含本地工作区路径，需要按实际环境调整：

- `build_native.py` 用于普通 C 编译和测试，不是形式化证明检查。
- `prepare_qcp_compat.py` 从下载副本生成兼容性候选并做前端预检，不是当前证明成果的双向同步或完整复现脚本。

后续将补充 QCP 工具版本与本地改动的固定记录、可配置路径及 `scripts/` 下的统一复现入口。当前 GitHub 仓库中的成果应视为部分验证案例和证明快照。

## 后续工作

- 验证 `find_and_skip`，组合空白扫描、分隔符匹配与错误返回。
- 推进 token 分配、初始化、解析器复位等状态管理函数。
- 建立基本值解析和递归容器所需的共享规约及 token 树模型。
- 完成适配表示与原程序的对应关系证明。
- 整理可独立复现的验证环境与脚本。

## 来源与许可证

上游 mu_json 使用 MIT License，原版权声明及许可证见 [mu_json-main/LICENSE](mu_json-main/LICENSE)。引入的依赖保留各自许可证与固定版本记录，见 [dependencies](dependencies/)。新增标注、证明及脚本的项目级许可证可在正式发布时另行明确；此说明不替代上游许可证。
