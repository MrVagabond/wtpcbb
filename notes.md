>根据虎书的`semant.sml`代码，可以写出Python的类型检查器，包含如下几个模块：
>
>1. 抽象语法模块，`semant.sml`中对应`Absyn`，Python中对应`ast`
>2. 符号模块，`semant.sml`中对应`Symbol`，Python中对应`??`
>3. 表格模块，`semant.sml`中对应`Table`，Python中对应`??`
>4. 环境模块，`semant.sml`中对应`Env`，Python中对应`??`
>5. 类型模块，`semant.sml`中对应`Types`，Python中对应`??`
>6. 错误处理模块，`semant.sml`中对应`ErrorMsg`模块，Python中对应`??`
>7. 目标语言模块，`semant.sml`中对应`Tree`模块，Python中对应`ast_trans`

并不是每个模块都要对应，比如错误处理模块，在Python中我更倾向于在每个模块中分别定义异常



