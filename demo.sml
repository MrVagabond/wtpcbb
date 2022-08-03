structure Demo =
struct

    (**********************先快速定义环境*)

    type symbol = string * int
    structure SymTable = Map2IntBinaryTable(type key = symbol
            fun getInt(s,n) = n)
    type 'a table = 'a SymTable.table


    (********************再写一个符号管理*)
    exception Symbol

    val nextsym = ref 0
    val sizeHint = 128
    val hashtable : (string,int) HashTable.hash_table = (*使用哈希表来保存已有的符号名*)
        HashTable.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)

    fun str2sym name = (*生成该字符串对应的符号，如果存在则沿用，否则创建一个新的*)
            case HashTable.find hashtable name
            of SOME i => (name,i)
            | NONE => let val i = !nextsym
                in nextsym := i+1;
                    HashTable.insert hashtable (name,i);
                    (name,i)
                end

    fun sym2str (s,n) = s

    (***************************抽象语法*)
    datatype term =   TmVar of string
                    | TmInt of int
                    | TmTru
                    | TmFals
                    | TmAbs of {para: string, anno: ty, body: term}
                    | TmApp of {func: term, arg: term}
                    | TmCast of {term: term, srcType: ty, destType: ty, lab: int}
                    | TmDyn of {fromType: ty, value: term}
                    | TmBlame of {lab: int}
    and ty =  TyDyn
            | TyBool
            | TyInt
            | TyFun of {paraType:ty, bodyType:ty}



    (* 与类型相关的谓词 *)
    fun consistType t1 t2 =
            case (t1, t2)
            of (TyDyn, _) => true
            | (_, TyDyn) => true
            | (TyBool, TyBool) => true
            | (TyInt, TyInt) => true
            | (TyFun {paraType=p1, bodyType=b1}, TyFun {paraType=p2, bodyType=b2}) => (consistType p1 p2) andalso (consistType b1 b2)
            | _ => false

    fun eqType t1 t2 = 
            case (t1, t2)
            of (TyDyn, TyDyn) => true
            | (TyBool, TyBool) => true
            | (TyInt, TyInt) => true
            | (TyFun {paraType=p1,bodyType=b1}, TyFun {paraType=p2,bodyType=b2}) => (eqType p1 p2) andalso (eqType b1 b2)
    
    fun isGroundType typ = 
            case typ
            of TyBool => true
            | TyInt => true
            | TyFun {paraType=TyDyn, bodyType=TyDyn} => true
            | _ => false

    fun isValue t =
            case t
            of TmVar _ => true
            | TmInt _ => true
            | TmTru => true
            | TmFals => true
            | TmAbs {para,anno,body} => true
            | TmCast {term=v,srcType=TyFun{paraType=p1,bodyType=b1}, destType=TyFun{paraType=p2,bodyType=b2}, lab=l} => isValue v
            | TmDyn {fromType=ft,value=v} => (isGroundType ft) andalso (isValue v)
            | _ => false




    (*定义环境中的表项*)
    datatype enventry = VarEntry of {ty:ty, tm:term}


    exception TypingError of string

    fun typing env TmTru = TyBool
        | typing env TmFals = TyBool
        | typing env (TmInt (i)) = TyInt
        | typing env (TmVar (s)) = (
                case SymTable.look(env, str2sym s)
                of SOME (VarEntry{ty=ty, tm}) => ty
                | NONE => raise TypingError "undefined variable"
            )
        | typing env (TmAbs {para=p,anno=a,body=b}) = (
                let 
                    val env' = SymTable.enter(env, str2sym p, VarEntry {ty=a,tm=TmVar(p)}) (*注意这里要向env中先更新*)
                in
                    TyFun{paraType=a, bodyType=(typing env' b)}
                end
            )
        | typing env (TmApp {func=f,arg=a}) = (
                (*先检查参数类型正确，再返回结果类型*)
                let
                    val funType = typing env f
                in
                    case funType
                    of (TyFun {paraType=p,bodyType=b}) =>   if eqType p (typing env a)
                            then b
                            else raise TypingError "unmatched argument type with parameter type"
                    | _ => raise TypingError "not a function"
                end
            )
        | typing env (TmCast {term=t,srcType=s,destType=d,lab=l}) = (
                (*先检查两种类型是协调的，再返回目标类型*)
                if (consistType s d)
                then d 
                else raise TypingError "unconsistent type cast"
            )
        | typing env (TmDyn {fromType=t,value=v}) = (
                if (isGroundType t) andalso (isValue v) (*只需要做出判断，不需要同时归约，因为会在归约的时候调用typing函数*)
                then TyDyn
                else raise TypingError "TmDyn bad type"
            )


    val initenv = 
        SymTable.enter(SymTable.empty, str2sym "foo", VarEntry {ty=(TyFun {paraType=TyInt, bodyType=TyBool}), tm=TmAbs{para="z", anno=TyInt, body=TmTru}})


    fun whole_typing tm =
            typing initenv tm


    exception ReduceError of string


    fun reduce env (TmApp{func=TmVar(s), arg=t2}) = ( (*规则1*)
        if (isValue t2)
        then (
            case SymTable.look(env, str2sym s)
            of SOME (VarEntry{ty=ty, tm=f}) => reduce env (TmApp{func=f, arg=t2})
            | NONE => raise TypingError "undefined variable"
        )
        else (reduce env (TmApp{func=TmVar(s), arg=reduce env t2}))
    )
    | reduce env (TmApp{func=TmAbs{para=p,anno=a,body=t1}, arg=t2}) = ( (*规则2*)
        if (isValue t2)
        then (
            (* 安全假设所有变量都是不重名的，所以直接替换即可 *)
            let
                fun replace tmS x tmT = (*S[x:=T]*)
                    case tmS
                    of TmVar(y) => if (x=y) then (tmT) else (tmS)
                    | TmTru => tmS
                    | TmFals => tmS
                    | TmInt(_) => tmS
                    | TmAbs{para=p,anno=a,body=b} => TmAbs{para=p,anno=a,body=replace b x tmT}
                    | TmApp{func=f, arg=a} => TmApp{func=replace f x tmT, arg=replace a x tmT}
                    | TmCast{term=t, srcType=st, destType=dt, lab=l} => TmCast{term=replace t x tmT, srcType=st, destType=dt, lab=l}
                    | TmDyn{fromType=ft, value=t} => TmDyn{fromType=ft, value=replace t x tmT}
                    | _ => raise ReduceError "bad replace"
            in
                replace t1 p t2
            end
        )
        else (reduce env (TmApp{func=TmAbs{para=p,anno=a,body=t1}, arg=reduce env t2}))
    )
    | reduce env (TmApp{
                    func=TmCast{term=t1,srcType=TyFun{paraType=pt,bodyType=bt}, destType=TyFun{paraType=pt',bodyType=bt'},lab=l},
                    arg=t2}) = ( (*规则4*)
        if (isValue t2)
        then (
            if (isValue t1)
            then (
                TmCast{term=TmApp{
                    func=t1,
                    arg=TmCast{term=t2, srcType=pt', destType=pt, lab=(~ l)}
                    }, 
                    srcType=bt, destType=bt', lab=l}
            )
            else (reduce env (TmApp{
                    func=TmCast{term=reduce env t1,srcType=TyFun{paraType=pt,bodyType=bt}, destType=TyFun{paraType=pt',bodyType=bt'},lab=l},
                    arg=t2}))
        )
        else (reduce env (TmApp{
                    func=TmCast{term=t1,srcType=TyFun{paraType=pt,bodyType=bt}, destType=TyFun{paraType=pt',bodyType=bt'},lab=l},
                    arg=reduce env t2}))
    )
    | reduce env (TmApp{func=TmBlame{lab=p}, arg=t}) = (*出错处理*)
        TmBlame{lab=p}
    | reduce env (TmApp{func=t, arg=TmBlame{lab=p}}) = (*出错处理*)
        TmBlame{lab=p}
    | reduce env (TmApp{func=t1, arg=t2}) = ( (* 收尾工作 *)
        if (isValue t1)
        then (reduce env (TmApp{func=t1, arg=reduce env t2}))
        else (reduce env (TmApp{func=reduce env t1, arg=t2}))
    )
    (* 对cast的归约规则 *)
    | reduce env (TmCast{term=TmDyn{fromType=ft,value=t},srcType=TyDyn,destType=dt,lab=l}) = ( (*规则8、9*)
        if (isValue t)
        then (
            if (isGroundType ft)
            then (
                if (consistType ft dt)
                then (TmCast{term=t, srcType=ft, destType=dt, lab=l})
                else (TmBlame{lab=l})
            )
            else raise ReduceError "not ground type"
        )
        else (reduce env (TmCast{term=TmDyn{fromType=ft,value=reduce env t},srcType=TyDyn,destType=dt,lab=l}))
    )
    | reduce env (TmCast{term=t,srcType=TyInt,destType=TyInt,lab=l}) = ( (*规则3*)
        if (isValue t)
        then (t)
        else (reduce env (TmCast{term=reduce env t,srcType=TyInt,destType=TyInt,lab=l}))
    )
    | reduce env (TmCast{term=t,srcType=TyBool,destType=TyBool,lab=l}) = ( (*规则3*)
        if (isValue t)
        then (t)
        else (reduce env (TmCast{term=reduce env t,srcType=TyBool,destType=TyBool,lab=l}))
    )
    | reduce env (TmCast{term=t, srcType=TyDyn,destType=TyDyn,lab=l}) = ( (*规则5*)
        if (isValue t)
        then (t)
        else (reduce env (TmCast{term=reduce env t,srcType=TyDyn,destType=TyDyn,lab=l}))
    )
    | reduce env (TmCast{term=t, srcType=TyInt,destType=TyDyn,lab=l}) = ( (*规则6*)
        if (isValue t)
        then (TmDyn{value=t, fromType=TyInt})
        else (reduce env (TmCast{term=reduce env t,srcType=TyInt,destType=TyDyn,lab=l}))
    )
    | reduce env (TmCast{term=t, srcType=TyBool,destType=TyDyn,lab=l}) = ( (*规则6*)
        if (isValue t)
        then (TmDyn{value=t, fromType=TyBool})
        else (reduce env (TmCast{term=reduce env t,srcType=TyBool,destType=TyDyn,lab=l}))
    )
    | reduce env (TmCast{term=t, srcType=TyFun{paraType=pt,bodyType=bt},destType=TyDyn,lab=l}) = ( (*规则7*)
        if (isValue t)
        then (
            TmDyn{value=TmCast{term=t, srcType=TyFun{paraType=pt, bodyType=bt}, destType=TyFun{paraType=TyDyn, bodyType=TyDyn}, lab=l},
                  fromType=TyFun{paraType=TyDyn, bodyType=TyDyn}}
        )
        else (reduce env (TmCast{term=reduce env t, srcType=TyFun{paraType=pt,bodyType=bt},destType=TyDyn,lab=l}))
    )
    | reduce env (TmCast{term=TmBlame{lab=p}, srcType=st, destType=dt, lab=l}) = (*出错处理*)
        TmBlame{lab=p}
    | reduce env (TmCast{term=t, srcType=st, destType=dt, lab=l}) = ( (* 收尾工作 *)
        if (isValue t)
        then (reduce env (TmCast{term=t, srcType=st, destType=dt, lab=l}))
        else (reduce env (TmCast{term=reduce env t, srcType=st, destType=dt, lab=l})) 
    )
    
    

    






    (*示例程序*)
    val prog1 = TmApp {
            func=TmAbs {
                para="x",
                anno=TyBool,
                body=TmVar("x")
            },
            arg=TmTru
        }

    val prog2 = TmApp {
            func=TmAbs {
                para="x",
                anno=TyInt,
                body=TmVar("x")
            },
            arg=TmTru
        }

    val prog3 = TmApp {
            func=TmAbs {
                para="x",
                anno=TyBool,
                body=TmVar("x")
            },
            arg=TmInt(1)
        }
    val prog4 = TmApp {
            func=TmVar("foo"),
            arg=TmInt(3)
        }
end