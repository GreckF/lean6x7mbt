# lean6x7mbt — Lean 4 → MoonBit 提取

一个 Lean 4 元程序：把 Lean 定义直接从**内核 `Expr`** 提取成可读的 MoonBit 代码。
设计参考同仓库的 `rocq2mbt`（Rocq 的 MoonBit 后端）。

- toolchain：`leanprover/lean4:v4.29.0-rc8`（见 `lean-toolchain`），无任何 Lake 依赖。
- MoonBit：测试用 `moon 0.1.20261028`。

```lean
import Lean6x7mbt

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

extract_moonbit "out/fact.mbt" fact      -- 不写路径则显示在 infoview
```

生成：

```moonbit
pub fn fact(x : BigInt) -> BigInt {
  if x == 0N { 1N } else {
    let n = x - 1N
    (n + 1N) * fact(n)
  }
}
```

提取单个文件（monolithic）：从给定根出发，沿依赖把用到的类型、函数（包括 `List.map` 这类核心库函数）
一起提取，类型在前、函数在后；输出文件不依赖任何运行时包。

## 目录

| 路径 | 内容 |
| --- | --- |
| `Lean6x7mbt/Ast.lean` | MoonBit AST 与打印器（纯函数） |
| `Lean6x7mbt/Table.lean` | 提取表（环境扩展）、`extract_constant/inductive/helper` 命令、`lean6x7mbt.nat` 选项 |
| `Lean6x7mbt/Translate.lean` | `Expr` → MoonBit 的翻译（擦除、matcher/casesOn、类型、依赖收集） |
| `Lean6x7mbt/Runtime.lean` | 核心库私有/opaque 定义的公开等价物（目前是 `while` 的 `loopForIn`） |
| `Lean6x7mbt/Command.lean` | `extract_moonbit`、`extract_moonbit_project` 命令 |
| `Lean6x7mbt/Mbti.lean` | `import_mbti`：从 MoonBit 的 `.mbti` 接口生成 Lean 公理（反方向，见下） |
| `Lean6x7mbt/Prelude.lean` | 核心类型/函数的默认映射（Nat、Int、Bool、Option、Prod、Except、Array、String、Char、UIntN、Float） |
| `tests/*.lean` | 提取用例，输出到 `tests/moon/<pkg>/`；`Diff*.lean` 是差分测试（`with_tests`，自动生成 `*_gen_wbtest.mbt`） |
| `tests/moon/` | MoonBit 测试模块，每个包里有 `*_wbtest.mbt` 运行时断言 |
| `tests/proj/`、`tests/moon_proj/` | 多包提取用例（三个 Lean 模块）及其输出（独立的 MoonBit 模块） |

`bash tests/run.sh` 编译、提取全部用例并运行 `moon test`（含多包工程 `tests/moon_proj/`）。

## 翻译方案

| Lean | MoonBit |
| --- | --- |
| 递归函数 | 取编译器保留的 `_unsafe_rec` 版本（保留源码里的 `match` 与直接递归，无需处理 `brecOn`/`WellFounded.fix`） |
| `match`（matcher） | 内联为 `match`/`if`；每个 alt 只用一次就直接代入，多次使用则变成局部闭包 `let alt = fn(..) {..}` |
| `casesOn`、sparse `casesOn` | `match`；`Nat`/`Int`/`Bool`/`Decidable` 变 `if`；结构体变字段读取 |
| 实例投影 | 先归约：`HAdd.hAdd Nat Nat Nat inst a b` → `Nat.add a b` → `a + b`；字典仍是参数时（`[Add α]`）保留为结构体 `Add_[A]`，调用写 `(inst.add)(x)(y)` |
| 归纳类型 | `pub(all) enum T[A] { C(A, T[A]) }`，构造子限定写 `T::C(..)` |
| 结构（有运行时字段） | `pub(all) struct S { x : BigInt }`，构造 `S::{ x: .. }`，投影 `s.x`，`{ s with .. }` 自然成立 |
| 类型参数 | 变成泛型 `A, B, …`（按位置命名）；类型参数 `α → Prop` 之类的谓词一并擦除 |
| 证明、类型实参 | 擦除（声明和调用点都丢掉，不留占位参数） |
| `Decidable p` | `Bool`（`ite`/`dite` 直接变 `if`） |
| 顶层函数 | **非柯里化**，元数 = 定义里前导 λ 个数；调用点饱和则直接调用，不足则 η 展开 |
| 函数类型的值 | 单参闭包 `(A) -> (B) -> C` |
| 常量 / 无值参数的泛型常量 | 无泛型：`pub let c : T = ..`；有泛型：`pub fn[A] c() -> T`，引用写 `c()` |
| 下标等索引 | `Fin n` 之类的值索引被擦除成无索引的类型 |
| 强制转换 `Eq.mpr/cast/Eq.rec…` | 取值本身（可能引入 MoonBit 类型不匹配，见限制） |
| `False.elim`/`absurd` | `abort("unreachable …")` |
| 局部名 | 唯一化、小写开头、避开关键字与全局名；未使用的模式变量写 `_` |
| 全局名 | `Tree.size` → `tree_size`；类型 `Foo.Bar` → `Foo_Bar`；与关键字/内建类型冲突时加 `_` |

### Nat / Int

默认 `Nat`、`Int` 都是 `BigInt`（语义忠实，较慢）。`set_option lean6x7mbt.nat "int"` 或 `"int64"`
改成 MoonBit 的 `Int`/`Int64`（会回绕，由使用者自担溢出）。Nat 的 `-`、`/`、`%` 用生成文件里附带的
辅助函数（`lean_nat_sub` 等）实现截断减、除零为 0 等 Lean 语义。

### 特化（monad 多态函数）

含高阶类型参数的函数（`forIn`、`List.mapM`、`bind`、`throw`…）不能是 MoonBit 泛型：

- **非递归**的在调用点内联；
- **递归**的按调用处的具体 monad/实例特化成一份副本 `xxx_specN`：把高阶类型参数和提到它们的字典实参
  代入函数体，其余参数保留，副本里的递归调用命中同一份副本（以代入后的实参为键）。实参里的局部类型变量
  变成副本的泛型参数。

`while`/`repeat`（`Lean.Loop.forIn`）的循环体是核心库里私有的 `partial`/`opaque` 定义，无定义体可提取；提取器把 `Loop.forIn β m inst loop init f` 改写成本库公开的等价定义 `Lean6x7mbt.loopForIn`（`Lean6x7mbt/Runtime.lean`），再走上面的特化，得到 `lean6x7mbt_loopForIn_specN`。

于是 `Id.run do … for … ` 循环、`Option`/`Except` 里的 `mapM`、`StateM` 里的 `for` 都能提取
（见 `tests/Monads.lean`）：`Id`/`StateT` 这类类型别名会被展开，`StateM σ α` 就是闭包 `(σ) -> (α, σ)`。

### 自定义提取（定义在 `Table.lean`，默认映射见 `Prelude.lean`）

```lean
extract_constant Nat.add => "($0 + $1)"
extract_inductive Option => "Option[$0]" ["None", "Some($0)"]
extract_helper lean_nat_sub => "fn lean_nat_sub(a : @Nat, b : @Nat) -> @Nat { .. }"
```

- `extract_constant c => "tpl"`：`$i` 是第 i 个**保留**实参（类型、证明被擦除；`[Add α]` 这类字典实参
  也跳过，`Decidable` 实例除外）。模板代表 `c` 作用于其**全部**声明参数的结果：没被 `$i` 提到的实参
  直接丢弃（`Array.mkEmpty n` ↦ `[]`），实参不足时先 η 展开。模板要么自带括号、要么是原子表达式；同一个 `$i` 出现多次且实参不是
  变量时会先 `let` 绑定。
- `extract_inductive I => "ty" [ctors…]`：`ty` 里 `$i` 是第 i 个类型参数；构造子模板既用作表达式也用作模式，
  `$i` 是第 i 个保留字段。
- `extract_helper f => "src"`：模板里出现名字 `f` 时，把 `src` 作为声明写进输出（传递闭包）。
- 模板里的 `@Nat/@Int`（类型名）、`@zero/@one`（字面量）、`@ofInt/@toInt/@toInt64/@ofU64/@ofU32/@toU32`
  （与 MoonBit `Int` 等互转的函数名）随 `lean6x7mbt.nat` 展开。
- 没有映射、也没有定义体的常量（公理、`opaque`、`@[extern] opaque`）会报 "no extraction for …"
  （`opaque` 的值只是 inhabitant 见证，绝不当作定义体）；后写的映射覆盖前面的。
- 对已映射类型做结构投影（如 `s.toByteArray`）而该投影没有模板时报错，不会凭空生成同名 struct。

### 诊断：一次报出所有问题

提取某个常量失败时不会终止，而是记录错误、跳过该常量，继续处理队列里剩下的；全部处理完后抛出**一个**合并的
错误（不写输出文件）：同一原因只列一次，下面给出每条触发它的依赖链（`根 → … → 失败项`，缺映射的常量排在最后），
末尾汇总缺失映射，方便一次补齐：

```
error: extraction failed (2 items could not be extracted):

no extraction for `myExt`: it has no definition (axiom, `opaque` or `extern` constant)
  via useBoth → myExt

no extraction for `myExt2`: it has no definition (axiom, `opaque` or `extern` constant)
  via useBoth → helper → myExt2

missing mappings (add them, e.g.):
  extract_constant myExt => "..."
  extract_constant myExt2 => "..."
```

“缺失映射”包括 `no extraction for …` 与“已映射类型的投影没有模板”（`extract_constant String.toByteArray => "..."`）两类；
一个常量只报它遇到的第一个错误（补上映射后才会看到它的下一个问题）。回归用例见 `tests/Regress.lean`。

### 差分测试：自动生成运行时断言

```lean
extract_moonbit "tests/moon/x/x.mbt" f g with_tests [f 5, g [1, 2] == 3, Tree.size t0]
```

根列表后可跟 `with_tests [项, …]`（关键字取 `with_tests`，避免占用常见标识符 `testing`）。每一项是**闭合**的 Lean 项
`t : α`，由 Lean 自己用编译求值（`evalExpr`，所以良基递归、`partial` 都能算）得到值，并写出
`<主文件名>_gen_wbtest.mbt`（与主文件同目录；没有路径时测试打印在 infoview 里）：

- `α = Bool`：`assert_eq(<t 的提取结果>, <Lean 的值>)`；
- 其他类型：需要 `ToExpr α` 与 `BEq α`（`deriving ToExpr, BEq`）。求 `toExpr t` 得到值表达式 `v`，把 Lean 项 `t == v`
  当 Bool 项提取，生成 `assert_true(..)`——用户类型不需要 MoonBit 的 `Eq`/`Show`。没有这两个实例时报错并提示改成 Bool 测试。

测试项和根在同一次提取里翻译（共享名字分配和依赖队列），所以测试用到的常量会一并产出。每个测试一个
`test "<pp 出来的 Lean 项>" { … }`，注释里是 Lean 求得的值：

```moonbit
test "(Shape.rect 2 3).grow 4" {
  // Lean: Shape.rect 6 12
  let got = instBEqShape_beq(shape_grow(Shape::Rect(2N, 3N), 4N), Shape::Rect(6N, 12N))
  assert_true(got)
}
```

用例：`tests/Diff.lean`、`tests/DiffInt.lean`（`int` 模式）。不要手写期望值；生成文件不要手改。

### 多包输出：`extract_moonbit_project`

单文件模式会在每个输出里重复带一份核心库代码。项目较大时改用

```lean
extract_moonbit_project "out/dir" root₁ root₂ … with_tests [t₁, …]    -- with_tests 可省
```

输出一个 MoonBit 模块目录（现有 `extract_moonbit` 的行为不变）：

```
out/dir/moon.mod                    -- 目录里没有才生成；已有则不覆盖（读取其中的 name 拼 import 路径）
out/dir/lean_core/{lean_core.mbt, moon.pkg}
out/dir/proj_a/{proj_a.mbt, moon.pkg}      -- Lean 模块 ProjA
out/dir/proj_main/{proj_main.mbt, moon.pkg, proj_main_gen_wbtest.mbt}
```

- **分包**：每个被提取的常量按它所在的 Lean 模块归包。根模块为 `Init`/`Std`/`Lean`（以及本库的
  `Lean6x7mbt`）的归到 `lean_core`；其余每个模块一个包，目录名 = 模块名转小写蛇形（`Foo.Bar` → `foo_bar`，
  `ProjA` → `proj_a`），避开关键字/保留名（`core`、`main`、`test` 等）并在冲突时加 `_2`。当前文件里定义的常量
  归“主包”（`set_option lean6x7mbt.main_package "x"`；默认由模块名得出，独立文件（`_stdin`）为 `app`）。
- **辅助函数**（`extract_helper`）全部放进 `lean_core` 并加 `pub`；别的包里模板用到它们时写成
  `@lean_core.lean_nat_sub(..)`。`List` 等被辅助函数引用的类型本来就是核心库类型，同样在 `lean_core`。
- **特化副本**（`xxx_specN`）放在**请求它的那个包**里，缓存键带上包名：每个包各自一份，`lean_core`
  不会反过来依赖用户包。
- **跨包引用**写 `@pkg.name`、`@pkg.T[A]`、`@pkg.T::C(..)`（表达式和模式）、`@pkg.S::{ x: .. }`；同包不加限定；
  结构体字段访问 `s.x` 不需要限定。全局名仍在整个提取里唯一，不按包重新编号。
- **`moon.pkg`** 只列真正用到的包（扫描生成的源码里的 `@pkg.`）；整个目录的依赖图会检查：`lean_core`
  依赖用户包、或包之间成环，都直接报错，不生成坏工程。
- **`with_tests`**：断言写进主包的 `<主包>_gen_wbtest.mbt`；测试里用到、而主包源码没有 import 的包放进
  `import { .. } for "wbtest"`。
- 模块名：`set_option lean6x7mbt.module "user/name"`（默认 `lean6x7mbt/extracted`），仅在目录里没有 `moon.mod` 时使用。
- 每次运行覆盖各包的 `<pkg>.mbt`、`moon.pkg` 和 `_gen_wbtest.mbt`；以前生成但现在不再需要的包目录不会被删除。

用例：`tests/proj/{ProjA,ProjB,ProjMain}.lean`（`lakefile.toml` 里的测试库 `ProjTest`，不是默认目标，
`tests/run.sh` 会显式 `lake build ProjTest`），输出到 `tests/moon_proj/`。

### 反方向：`import_mbti`（在 Lean 里调用已有的 MoonBit 包）

```lean
import_mbti "path/to/pkg.generated.mbti" as Foo          -- `as Foo` 缺省取包名最后一段
import_mbti "…mbti" as Foo (alias := "lib") (unqualified)  -- 两个选项都可省，可同时给
```

在 elaboration 时读取 `moon info` 生成的接口文件（路径相对于运行 `lean` 的目录），往环境里加声明并登记提取映射：

```moonbit
pub fn add3(@bigint.BigInt, @bigint.BigInt, @bigint.BigInt) -> @bigint.BigInt
```
↦ `@[extern "mbti_Foo_add3"] axiom Foo.add3 : Int → Int → Int → Int` + 模板 `@pkg.add3($0, $1, $2)`。
提取时 Lean 代码里出现 `Foo.add3` 就生成对 MoonBit 函数的直接调用（支持部分应用、作为高阶参数、在 `map`/循环里调用）。
测试见 `tests/Mbti.lean`（手写 MoonBit 库 `tests/moon/extlib`，输出 `tests/moon/mbti`）、`tests/MbtiProj.lean`。

- **为什么是 `@[extern] axiom`**：它仍是公理（Lean 不知道函数的行为，只能自己再补公理），但 Lean 编译器接受对它的
  调用，使用方的 `def` 不必写 `noncomputable`（递归的 `noncomputable def` 没有 `_unsafe_rec`，提取不了）。
  Lean 端**不能求值**：`#eval`、`with_tests` 里出现这些函数会报错（`with_tests` 的报错会点名函数并建议改写
  手写的 `*_wbtest.mbt`，期望值按 MoonBit 实现手算）。
- **调用形式**：默认写 `@pkg.f(..)`，`pkg` 取 `.mbti` 里 `package "…"` 的最后一段，可用 `(alias := "x")` 改；
  `(unqualified)` 生成不带限定的 `f(..)`（生成代码与被调用代码在同一个 MoonBit 包时用）。
  **单文件模式**下使用者要自己在输出所在包的 `moon.pkg` 里 `import { "<package 行里的路径>" @pkg }`。
  **多包模式**（`extract_moonbit_project`）自动处理：`import_mbti` 往表里登记 `(alias, 路径)`，生成包的 `moon.pkg`
  只要用到 `@alias.` 就写 `"路径" @alias`（测试里输出到 `tests/moon`，与 `extlib` 同模块）。外部包所在的模块
  要能被生成工程的 `moon.mod`/`moon.work` 找到，这一步仍由使用者负责。
- **选项必须一致**：类型对应读取导入时的 `lean6x7mbt.nat`，要和提取时的取值相同。

类型对应（MoonBit → Lean；`tyOf` 再把它翻回去得到原类型）：

| MoonBit | Lean |
| --- | --- |
| `Bool` `String` `Char` `Unit` | 同名 |
| `Double` | `Float`（MoonBit 的 32 位 `Float` 没有对应，跳过） |
| `Byte` / `UInt` `UInt32` / `UInt16` / `UInt64` | `UInt8` / `UInt32` / `UInt16` / `UInt64` |
| `BigInt` | `Int`（`bigint` 模式；`Nat` 无法从 MoonBit 类型区分，需要时自己写 `Int.toNat`） |
| `Int`（旧版写 `Int32`） | `bigint` 模式**没有对应**（`Int`/`Nat` 提取成 `BigInt`），跳过并警告；`int` 模式下是 Lean `Int` |
| `Int64` | 仅 `int64` 模式下是 Lean `Int`，否则跳过并警告 |
| `Array[T]`、`T?`/`Option[T]` | `Array T`、`Option T` |
| `Result[T, E]` | `Except E T` |
| `(A, B)` | `A × B`（三元及以上的元组跳过：`Prod` 嵌套与 MoonBit 元组不同） |
| `(A) -> B` | `A → B` |
| 参数位置的 `() -> B`、`(A, B) -> C` | `Unit → B`、`A → B → C`，模板里用 `fn() { ($i)(()) }`、`fn(p0, p1) { ($i)(p0)(p1) }` 适配 |
| 返回值、容器里的多参/零参闭包 | 跳过并警告（需要反向适配；柯里化闭包的约定见上） |
| 本包的 `pub type T`、`pub struct`（私有字段/`mut` 字段）、`pub enum`（非 `(all)`） | 不透明类型：`axiom Foo.T : Type`，登记 `extract_type`，提取为 `@pkg.T` |
| `pub(all) enum E[A]`、`pub(all) struct S` | Lean `inductive Foo.E` / `structure Foo.S`，登记 `extract_inductive`：构造子 ↦ `@pkg.E::C(..)`，结构体 ↦ `@pkg.S::{ x: .., y: .. }`、字段 ↦ `$0.x`；模式里的记录写成 `{ x: a, y: b }` |
| 带标签的构造子参数 `C(x~ : T)` | 表达式/模式都写 `C(x=..)`（MoonBit 接受） |
| 其他本包类型（元组结构体、互递归类型、字段类型不支持） | 退化成不透明类型并警告 |
| `fn f(..)`、`fn T::m(self, ..)` | `Foo.f`、`Foo.T.m`（可用点记法 `x.m ..`）；方法调用写 `@pkg.T::m(..)` |
| `fn[A, B] f` | `{A B : Type}`（类型实参提取时擦除） |
| `pub let x : T`、`pub const X : T = ..` | `axiom Foo.x : T`，模板 `@pkg.x`（`const` 只要类型是支持的） |
| `fn f() -> T` | `Unit → T`，模板 `@pkg.f()` |
| 带标签参数 `x~ : T` / 可选参数 `x? : T` | 位置参数，模板 `x=$i` / 省略（用默认值） |

**跳过并警告**（不影响其余声明，最后一条 info 汇总数量）：`raise`/`async` 函数、带 trait 约束的泛型
（`[T : Eq]`）、`trait`、`impl`、`suberror`、类型别名（签名里已展开）、`@pkg.X`/`Bytes`/`Map`/`FixedArray` 等其他包或
未知类型、`&Trait`、`Int`/`Int64`/`Float` 无对应的情形、三元以上元组、未知语法的行。所有 `.mbti` 只靠逐行解析：
不认识的行不会崩溃也不会被误解析，而是警告跳过。已存在的 Lean 名字同样跳过并警告。

不透明类型的 `extract_type T => "@pkg.T[$0]"` 是 `Table.lean` 里新增的最小机制（也可手写）：等价于没有构造子的
`extract_inductive`，`$i` 是第 i 个类型参数。

### 内联与共享

Lean 里标了 `@[inline]`/`@[always_inline]`/`@[macro_inline]` 的**非递归**函数（实例除外），饱和调用时在
调用点内联，和 Lean 编译器一致（`Id.run`、`Option.map`、`Except.bind`、`StateT.bind`…）。特化副本还会按
展开后的结果类型 η 展开：`StateM σ` 里的循环把状态作为参数，于是循环的递归调用是饱和的尾调用。

内联（β 归约、实例方法归约、matcher 展开）时，若某个实参不是变量/常量/字面量、是一阶值、且在函数体里
出现多次，则先 `let` 绑定再使用，保证不重复求值（`1 + max l.depth r.depth` 只各算一次）。类型、证明、
字典、函数（含 `StateM` 这类 monadic 动作）仍直接代入，以便实例投影和高阶包装继续归约。

## 限制

- 多包输出：Lean 模块名以 `Init`/`Std`/`Lean` 开头的用户模块会被当成核心库归入 `lean_core`；包目录名由模块名
  推出，`Foo.Bar` 与 `FooBar` 这类同名冲突靠 `_2` 后缀区分；不会清理旧的包目录。
- **高阶类型参数**（`m : Type → Type`，即 Monad 多态）MoonBit 无法表达，处理方式见下节“特化”。
  特化的实参若依赖局部**值**（而不是类型变量）会报错。
- 存在类型字段（`structure S where (α : Type) (x : α)`）、rank-n 类型、依赖类型里无法擦除的类型计算
  会报错；`Eq.rec` 之类转换在 MoonBit 里可能需要手工修。
- `Array` 用 MoonBit 数组，更新一律拷贝（保持 Lean 的持久语义，O(n)）。`Array.map/foldl/push/size/
  getD/set!`、`#[..]` 已映射，其余数组函数（`filter`、`any`…）暂时没有，会因递归的高阶参数或缺定义报错。
- `String` 是 MoonBit 的 UTF-16 字符串，`String.length` 数的是码元；`String.mk` 不可用，`Char.mk`
  只能作表达式（不能出现在模式里）。Lean 4.29 的字符串函数大多落到 `String.Internal.*`（`@[extern] opaque`）
  或 `ByteArray`/`String.Slice` 上：已映射 `append/length/isEmpty/isPrefixOf/contains/any/pushn/intercalate`，
  其余（`toUpper`、`<`、`startsWith`、`toList`、`get`…）会报错，需要自行 `extract_constant`。
- `xs[i]!` 越界时 Lean 返回默认值，提取结果是 `abort`。
- 循环（`for`/`while`）提取成尾递归函数，栈深度不随迭代次数增长（`Id`、`Except`、`StateM`、
  `StateT σ (Except ε)` 实测 20 万次以上）。这依赖 monad 的 `bind` 标了 `@[inline]`；自定义 monad 若
  `bind` 不内联，递归调用会落在回调闭包里，栈深度与迭代次数成正比。`Float` 字面量经 `lean_float_of_scientific` 逐位乘除，可能与 Lean 差一个 ulp。
- `UIntN` 只映射了 `add/sub/mul/ofNat/toNat/比较`；`/`、`%`、位运算尚无。
- 用户在局部对多个类型使用 `let` 多态函数会得到 MoonBit 类型错误（MoonBit 无 let 多态）。
- 单字母大写的类型名（如 `P`）会被改成 `P_`，避免与泛型参数 `A..Z` 冲突。
- `import_mbti` 的限制见上节；被导入的函数只存在于 MoonBit 侧，Lean 里不能求值，也不要往生成的公理文件之外加
  关于它们行为的定理（除非自己担保）。
- 生成的类型不带 `derive`，测试里需要比较时请通过提取出来的函数（如 `BEq` 实例）。
