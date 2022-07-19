structure Demo =
struct

(**********************先快速定义类型环境*)

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
and ty =  TyDyn
        | TyBool
        | TyInt
        | TyFun of {paraType:ty, bodyType:ty}

fun consistType t1 t2 =
    case (t1, t2)
    of (TyDyn, _) => true
    | (_, TyDyn) => true
    | (TyBool, TyBool) => true
    | (TyInt, TyInt) => true
    | (TyFun {paraType=p1, bodyType=b1}, TyFun {paraType=p2, bodyType=b2}) => (consistType p1 p2) andalso (consistType b1 b2)
    | _ => false
    
    

(*定义环境中的表项*)
datatype enventry = VarEntry of {ty:ty}


exception TypingError of string

fun typing tenv TmTru = TyBool
    | typing tenv TmFals = TyBool
    | typing tenv (TmInt (i)) = TyInt
    | typing tenv (TmVar (s)) = (
        case SymTable.look(tenv, str2sym s)
        of SOME (VarEntry{ty=ty}) => ty
        | NONE => raise TypingError "undefined variable"
    )
    | typing tenv (TmAbs {para=p,anno=a,body=b}) = (
        let 
            val tenv' = SymTable.enter(tenv, str2sym p, VarEntry {ty=a}) (*注意这里要向tenv中先更新*)
        in
            TyFun{paraType=a, bodyType=(typing tenv' b)}
        end
    )
    | typing tenv (TmApp {func=f,arg=a}) = (
        (*先检查参数类型正确，再返回结果类型*)
        let
            val funType = typing tenv f
        in
            case funType
            of (TyFun {paraType=p,bodyType=b}) => if consistType p (typing tenv a)
                              then b
                              else raise TypingError "unconsistent argument type with parameter type"
            | _ => raise TypingError "not a function"
        end
    )
    | typing tenv (TmCast {term=t,srcType=s,destType=d,lab=l}) = (
        (*先检查两种类型是协调的，再返回目标类型*)
        if (consistType s d)
        then d 
        else raise TypingError "unconsistent type cast"
    )


val initenv = 
    SymTable.enter(SymTable.empty, str2sym "foo", VarEntry {ty=(TyFun {paraType=TyInt, bodyType=TyBool})})

fun static_typing tm =
    typing initenv tm


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