structure Demo =
struct

    (*先快速定义环境*)

    type symbol = string * int
    structure SymTable = Map2IntBinaryTable(type key = symbol
            fun getInt(s,n) = n)
    type 'a table = 'a SymTable.table


    (*再写一个符号管理*)
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

    (*抽象语法*)
    datatype term =   TmVar of string
    | TmInt of int
    | TmTru
    | TmFals
    | TmAbs of {para: string, anno: ty, body: term}
    | TmApp of {func: term, arg: term}
    | TmCast of {term: term, srcType: ty, destType: ty, lab: int}
    | TmDyn of {fromType: ty, value: term} (*不会在输入中出现，但会在归约过程中出现*)
    | TmBlame of {lab: int} (*同上*)
    and ty =  TyDyn
    | TyBool
    | TyInt
    | TyFun of {paraType:ty, bodyType:ty}



    (* 与类型相关的一元或二元谓词 *)
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
            | _ => false
    
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

    fun isSubType t1 t2 = 
            case (t1, t2)
            of (TyBool, TyBool) => true
            | (TyInt, TyInt) => true
            | (TyDyn, TyDyn) => true
            | (TyFun {paraType=p1, bodyType=b1}, TyFun {paraType=p2, bodyType=b2}) => (isSubType p2 p1) andalso (isSubType b1 b2)
            | (t1, TyDyn) => (isSubType t1 TyBool) orelse (isSubType t1 TyInt) orelse (isSubType t1 (TyFun {paraType=TyDyn, bodyType=TyDyn}))
            | _ => false

    fun isNaiveSubType t1 t2 = 
            case (t1, t2)
            of (TyBool, TyBool) => true
            | (TyInt, TyInt) => true
            | (_, TyDyn) => true
            | (TyFun {paraType=p1, bodyType=b1}, TyFun {paraType=p2, bodyType=b2}) => (isNaiveSubType p1 p2) andalso (isNaiveSubType b1 b2)
            | _ => false

    fun isPosSubType t1 t2 =
            case (t1, t2)
            of (TyBool, TyBool) => true
            | (TyInt, TyInt) => true
            | (_, TyDyn) => true
            | (TyFun {paraType=p1, bodyType=b1}, TyFun {paraType=p2, bodyType=b2}) => (isNegSubType p2 p1) andalso (isPosSubType b1 b2)
            | _ => false
    and isNegSubType t1 t2 = 
            case (t1, t2)
            of (TyBool, TyBool) => true
            | (TyInt, TyInt) => true
            | (TyDyn, _) => true
            | (TyFun {paraType=p1, bodyType=b1}, TyFun {paraType=p2, bodyType=b2}) => (isPosSubType p2 p1) andalso (isNegSubType b1 b2)
            | (t1, t2) => (isNegSubType t1 TyBool) orelse (isNegSubType t1 TyInt) orelse (isNegSubType t1 (TyFun {paraType=TyDyn, bodyType=TyDyn}))



    (*定义环境中的表项*)
    datatype enventry = VarEntry of {ty:ty, tm:term}


    exception TypingError of string


    (* typing relation for term and type *)
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

     (*typing函数的测试程序*)
    (* (λx:bool.x) true *)
    val typing_test1 = TmApp {
            func=TmAbs {
                para="x",
                anno=TyBool,
                body=TmVar("x")
            },
            arg=TmTru
        }

    (* (λx:int.x) true *)
    val typing_test2 = TmApp {
            func=TmAbs {
                para="x",
                anno=TyInt,
                body=TmVar("x")
            },
            arg=TmTru
        }

    (* (λx:bool.x) 1 *)
    val typing_test3 = TmApp {
            func=TmAbs {
                para="x",
                anno=TyBool,
                body=TmVar("x")
            },
            arg=TmInt(1)
        }

    (* foo 3 *)
    val typing_test4 = TmApp {
            func=TmVar("foo"),
            arg=TmInt(3)
        }


    (*初始环境initenv用于声明一些预定义的函数*)
    val initenv = 
        let 
        val env1 = SymTable.enter(SymTable.empty, str2sym "foo", VarEntry {ty=(TyFun {paraType=TyInt, bodyType=TyBool}), tm=TmAbs{para="z", anno=TyInt, body=TmTru}})
        val env2 = SymTable.enter(env1, str2sym "add1", VarEntry {ty=(TyFun {paraType=TyInt, bodyType=TyInt}), tm=TmBlame {lab=0}})
        in
        env2
        end
        

    fun whole_typing tm =
            typing initenv tm


    exception ReduceError of string


    (*term之间的归约关系*)
    (* 如果是一个cast，那么先归约t；如果是一个app，那么先归约first再归约second最后归约这个app *)
    fun reduce env (TmApp{func=TmVar(s), arg=t2}) = ( (*规则1*)
                if (isValue t2)
                then (
                        case SymTable.look(env, str2sym s)
                        of SOME (VarEntry{ty=ty, tm=f}) => (
                            (*reduce env (TmApp{func=f, arg=t2})*)
                            (*对于预定义的函数，可以直接归约*)
                            case s
                            of "add1" => (
                                case t2 of TmInt i => TmInt (i+1)
                                | _ => raise (ReduceError "add1 should be applied to an integer")
                            )
                            | _ => raise (ReduceError ("unsupported predefined function: " ^ s))
                        )
                        | NONE => raise (ReduceError ("undefined identifier: " ^ s))
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
                            reduce env (replace t1 p t2)
                        end
                    )
                else (reduce env (TmApp{func=TmAbs{para=p,anno=a,body=t1}, arg=reduce env t2}))
            )
        | reduce env (TmApp{
            func=TmCast{term=t1,srcType=TyFun{paraType=pt,bodyType=bt}, destType=TyFun{paraType=pt',bodyType=bt'},lab=l},
            arg=t2}) = ( (*规则4*)
                if (isValue t1)
                then (
                        if (isValue t2)
                        then (
                                TmCast{term=TmApp{
                                        func=t1,
                                        arg=TmCast{term=t2, srcType=pt', destType=pt, lab=(~ l)}
                                    }, 
                                    srcType=bt, destType=bt', lab=l}
                            )
                        else (reduce env (TmApp{
                                        func=TmCast{term=t1,srcType=TyFun{paraType=pt,bodyType=bt}, destType=TyFun{paraType=pt',bodyType=bt'},lab=l},
                                        arg=reduce env t2}))
                    )
                else (reduce env (TmApp{
                                func=TmCast{term=reduce env t1,srcType=TyFun{paraType=pt,bodyType=bt}, destType=TyFun{paraType=pt',bodyType=bt'},lab=l},
                                arg=t2}))
            )
        | reduce env (TmApp{func=t1, arg=t2}) = ( (* 对于其他app term，不存在归约规则 *)
                if (isValue t1)
                then (
                        if (isValue t2)
                        then raise (ReduceError "no reduce rule can be applied to this app term")
                        else (reduce env (TmApp{func=t1, arg=reduce env t2}))
                    )
                else (reduce env (TmApp{func=reduce env t1, arg=t2}))
            )
        (* 对cast的归约规则 *)
        | reduce env (TmCast{term=TmDyn{fromType=ft,value=t},srcType=TyDyn,destType=dt,lab=l}) = ( (*规则8、9，需要继续归约或者直接归约成blame*)
                if (isValue t)
                then (
                        if (isGroundType ft)
                        then (
                                if (consistType ft dt)
                                then (reduce env (TmCast{term=t, srcType=ft, destType=dt, lab=l}))
                                else (TmBlame{lab=l}) (* 直接归约成blame *)
                            )
                        else raise ReduceError "not ground type"
                    )
                else (reduce env (TmCast{term=TmDyn{fromType=ft,value=reduce env t},srcType=TyDyn,destType=dt,lab=l}))
            )
        | reduce env (TmCast{term=t,srcType=TyInt,destType=TyInt,lab=l}) = ( (*规则3，停止继续归约*)
                if (isValue t)
                then (t)
                else (reduce env (TmCast{term=reduce env t,srcType=TyInt,destType=TyInt,lab=l}))
            )
        | reduce env (TmCast{term=t,srcType=TyBool,destType=TyBool,lab=l}) = ( (*规则3，停止继续归约*)
                if (isValue t)
                then (t)
                else (reduce env (TmCast{term=reduce env t,srcType=TyBool,destType=TyBool,lab=l}))
            )
        | reduce env (TmCast{term=t, srcType=TyDyn,destType=TyDyn,lab=l}) = ( (*规则5，停止继续归约*)
                if (isValue t)
                then (t)
                else (reduce env (TmCast{term=reduce env t,srcType=TyDyn,destType=TyDyn,lab=l}))
            )
        | reduce env (TmCast{term=t, srcType=TyInt,destType=TyDyn,lab=l}) = ( (*规则6，停止继续归约*)
                if (isValue t)
                then (TmDyn{value=t, fromType=TyInt})
                else (reduce env (TmCast{term=reduce env t,srcType=TyInt,destType=TyDyn,lab=l}))
            )
        | reduce env (TmCast{term=t, srcType=TyBool,destType=TyDyn,lab=l}) = ( (*规则6，停止继续归约*)
                if (isValue t)
                then (TmDyn{value=t, fromType=TyBool})
                else (reduce env (TmCast{term=reduce env t,srcType=TyBool,destType=TyDyn,lab=l}))
            )
        | reduce env (TmCast{term=t, srcType=TyFun{paraType=pt,bodyType=bt},destType=TyDyn,lab=l}) = ( (*规则7，停止继续归约*)
                if (isValue t)
                then (
                        TmDyn{value=TmCast{term=t, srcType=TyFun{paraType=pt, bodyType=bt}, destType=TyFun{paraType=TyDyn, bodyType=TyDyn}, lab=l},
                            fromType=TyFun{paraType=TyDyn, bodyType=TyDyn}}
                    )
                else (reduce env (TmCast{term=reduce env t, srcType=TyFun{paraType=pt,bodyType=bt},destType=TyDyn,lab=l}))
            )
        | reduce env (TmCast{term=t, srcType=st, destType=dt, lab=l}) = ( (* 对于其他cast term，不存在归约规则 *)
                if (isValue t)
                then raise (ReduceError "no reduce rule can be applied to this cast term")
                else (reduce env (TmCast{term=reduce env t, srcType=st, destType=dt, lab=l})) 
            )
        | reduce env tm = (* 对于其他term，不存在归约规则 *)
            if (isValue tm)
            then tm
            else raise (ReduceError "no reduce rule can be applied to this term")
    
    (*reduce函数的测试程序*)
    val reduce_test1 = TmCast {
        term=TmAbs {para="x", anno=TyInt, body=TmVar "x"},
        srcType=TyFun {paraType=TyInt, bodyType=TyInt},
        destType=TyDyn,
        lab=123
    }
    (* reduce_test1的结果应为
    TmDyn {
        fromType=TyFun {bodyType=TyDyn,paraType=TyDyn},
        value=TmCast {
            destType=TyFun {bodyType=TyDyn,paraType=TyDyn},lab=123,
            srcType=TyFun {bodyType=TyInt,paraType=TyInt},
            term=TmAbs {anno=TyInt,body=TmVar "x",para="x"}}}
    *)
    val reduce_test2 = TmApp {
        func=TmVar "add1",
        arg=TmInt 2
    }
    (* reduce_test2的结果应为
    TmInt 3
    *)

    val reduce_test3 = TmApp {
        func=TmCast {
            term=TmVar "add1",
            srcType=TyFun {paraType=TyInt, bodyType=TyInt},
            destType=TyFun {paraType=TyDyn, bodyType=TyDyn},
            lab=123
        },
        arg=TmInt 2
    }
    (* 最后的结果为
    TmCast {
        destType=TyDyn,lab=123,srcType=TyInt,
        term=TmApp {
            arg=TmCast {destType=TyInt,lab=~123,srcType=TyDyn,term=TmInt 2},
            func=TmVar "add1"}}
    这是因为cast中的term无法继续归约
    *)
    val reduce_test4 = TmApp {
            arg=TmCast {destType=TyInt,lab=(~123),srcType=TyDyn,term=TmInt 2},
            func=TmVar "add1"}
    (*
    直接报错，不存在cast的归约规则
    *)
    
    datatype uterm = UtmVar of string
    | UtmInt of int
    | UtmTru
    | UtmFals
    | UtmAbs of {para: string, body: uterm}
    | UtmApp of {func: uterm, arg: uterm}
    | UtmTerm of term

    val nextNewLabel = ref 666
    fun newLabel () =
            let val i = !nextNewLabel
            in nextNewLabel := i + 1; i
            end

    fun embedding utm =
            case utm
            of UtmVar x => TmVar x
            | UtmInt i => TmInt i
            | UtmTru => TmTru
            | UtmFals => TmFals
            | UtmAbs {para=p, body=b} => TmCast {term=(TmAbs {para=p, anno=TyDyn, body=(embedding b)}), srcType=TyFun{paraType=TyDyn, bodyType=TyDyn}, destType=TyDyn, lab=newLabel()}
            | UtmApp {func=f, arg=a} => TmApp {func=(TmCast {term=(embedding f), srcType=TyDyn, destType=TyFun{paraType=TyDyn, bodyType=TyDyn}, lab=newLabel()}),
                    arg=(embedding a)}
            | UtmTerm t => t
    
   

    
end