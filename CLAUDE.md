# lean6x7mbt 工作约定

- 先读 `README.md`（翻译方案、命令、限制）。用中文交流。
- Lean 4 项目，**不依赖 Mathlib**，toolchain 固定 `v4.29.0-rc8`（用到 4.29 的内部 API：`getSparseCasesOnInfoCore`、
  `Meta.getMatcherInfo?`、`unfoldProjInst?` 等，换版本可能要改）。本项目在 Windows 原生环境下构建
  （`lake build`），不需要 WSL。
- 提取直接作用于**内核 `Expr`**（用户已确认，不用编译器 LCNF）：递归定义取 `_unsafe_rec` 版本，matcher 内联，
  实例投影归约，类型与证明擦除。设计参考 `rocq2mbt`（顶层非柯里化 + 调用点饱和/η 展开，函数值是单参闭包，
  多态常量是无参泛型函数，`extract_constant` 模板，`Nat/Int` 默认 `BigInt` 可用 `lean6x7mbt.nat` 切换）。
  遇到新的提取设计问题先问用户。
- 测试：`bash tests/run.sh`。新特性在 `tests/*.lean` 加用例（`extract_moonbit "tests/moon/<pkg>/<pkg>.mbt" ...`），
  并在 `tests/moon/<pkg>/*_wbtest.mbt` 加运行时断言；每个 `.lean` 对应自己的 moon 包（`moon.pkg` 可为空）。
- 诊断：`drain` 不在第一个错误处终止，错误记在 `ExState.errors`（依赖来源在 `origin`，缺映射用 `throwMissing`），
  最后 `reportErrors` 抛一个合并错误；报错用例在 `tests/Regress.lean`（`#guard_msgs`）。
- 差分测试：`extract_moonbit .. with_tests [t, ..]` 用 Lean 求值生成 `<pkg>_gen_wbtest.mbt`（`tests/Diff*.lean`）。
  新的运行时断言优先用它，不要手抄 `#eval` 结果；`*_gen_wbtest.mbt` 是生成物，不要手改。
- MoonBit 语法要点（moon 0.1.20261028 实测）：模块文件是 `moon.mod`/`moon.pkg`（不是 json）；函数名必须小写开头；
  `not(x)` 已废弃用 `!x`；BigInt 字面量 `5N`，未带后缀的整数字面量按期望类型重载，但 `let x = 5` 会推成 `Int`，所以
  Nat/Int 字面量一律带后缀；闭包类型的字段调用要写 `(x.f)(a)`；结构体字面量 `S::{ x: .., y: .. }`。
- 模板必须是原子表达式或自带括号（打印器对 `.tpl` 当原子处理，顶层才会去掉最外层括号）。
- 高阶（monad）多态函数：非递归内联，递归的特化成 `xxx_specN`（`Translate.lean` 的 `specialize`，键是代入后的实参，
  合成常量放在 `ExState.aux`，不进环境）。
- 内联不得重复求值：β/实例方法/matcher 判别式都走 `betaShare`/`needsSharing`（多次使用的非平凡一阶值先
  `let`）。不要再直接用 `headBeta`/`Expr.beta` 代入值实参。
- `while`/`repeat`：`trConstApp` 把 `Lean.Loop.forIn` 改写成 `Lean6x7mbt.loopForIn`（`Runtime.lean`，公开的 `partial` 等价物），再走特化；不给 `opaque` 开后门。
- `opaque` 常量没有可提取的定义体（`getBodyInfo?` 不用 `allowOpaque`）；宁可报错也不静默生成错误代码。
  回归用例在 `tests/Regress.lean`（含 `#guard_msgs` 的报错用例），`run.sh` 在任一 `.lean` 报错时失败。
- 标了 `@[inline]` 的非递归函数在饱和调用点内联（`trGlobal` 的 `inlinable`）；特化副本按结果类型 η 展开
  （`buildSpec`），调用实参不足时走 `trSpecEta`。两者合起来保证 monadic 循环是尾递归，回归用例是
  `tests/While.lean` 的 `deep*`（20 万次迭代）。
- 已知缺口（见 README 限制）：特化实参依赖局部值时报错；数组/UIntN 映射只是常用子集。
- 多包输出：`extract_moonbit_project "dir" roots…`（`Command.lean`/`Translate.lean` 的 `extractProject`），按 Lean 模块分包，核心库+辅助函数进
  `lean_core`，特化副本放在请求它的包（`specs` 的键带包名），跨包引用写 `@pkg.name`（`qualify`/`qualifyHelpers`）。用例 `tests/proj/` →
  `tests/moon_proj/`（`ProjTest` 库，`run.sh` 里单独构建）。单文件模式的输出必须保持逐字节不变。
- 反方向 `import_mbti`（`Lean6x7mbt/Mbti.lean`）：解析 `.mbti` → `@[extern] axiom`（不用 `noncomputable`）+ `extract_constant` 模板；不透明类型走 `extract_type`
  （`Table.lean`），`pub(all)` 的 enum/struct 生成 Lean inductive/structure。结构体的构造模板 `@pkg.S::{..}` 作模式时由 `patTpl` 改成 `{..}`。
  不支持的条目一律警告跳过（不要悄悄映射成语义不同的类型：`Int`/`Int64` 在 bigint 模式下跳过）。用例 `tests/Mbti.lean`、`tests/MbtiProj.lean`，
  库 `tests/moon/extlib`（改它之后要 `moon info` 更新并提交 `pkg.generated.mbti`，并更新 `#guard_msgs` 里的警告清单）。
