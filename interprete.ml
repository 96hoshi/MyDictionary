type ide = string;;
type exp = 
	  Eint of int 
	| Ebool of bool 
	| Estring of string
	| Den of ide 
	| Prod of exp * exp 
	| Sum of exp * exp 
	| Diff of exp * exp 
	| Eq of exp * exp 
	| Minus of exp 
	| IsZero of exp 
	| Or of exp * exp 
	| And of exp * exp 
	| Not of exp 
	| Ifthenelse of exp * exp * exp 
	| Let of ide * exp * exp 
	| Fun of ide * exp 
	| FunCall of exp * exp 
	| Letrec of ide * exp * exp 
	| Dict of (ide * exp) list
	| Get of exp * ide
	| Add of exp * ide * exp
	| Remove of exp * ide
	| Clear of exp
	| ApplyOver of exp * exp
	| Rt_eval of exp;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = 
	  Int of int 
	| Bool of bool 
	| String of string
	| Unbound 
	| FunVal of evFun 
	| RecFunVal of ide * evFun 
	| DictVal of (ide * evT) list
	| DynFunVal of evFunD 
	| DynRecFunVal of ide * evFunD 
and evFun = ide * exp * evT env
and evFunD = ide * exp ;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"dict" -> (match v with
		DictVal(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;
	
let rec search (id : ide) (lis : (ide * 't) list) : bool = match lis with
	[ ] -> false |
	(key,value) :: pairs -> if key = id then true else search id pairs;;

let rec invariant (lis : (ide * 't) list) : bool = match lis with
	[ ] -> true |
	(key,value) :: pairs -> if search key pairs then false else invariant pairs;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
		(match funDef with
    		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                 			                eval letBody r1 |
    		_ -> failwith("non functional def")) |
					
	Rt_eval(ex) -> eval_dyn ex r |

	Dict(d) -> 
		if invariant d then DictVal(evalList d r) 
			else failwith("dict invariant not preserved")|

	Get(d, key) -> 
		(let x = (eval d r) in match x with
			DictVal(pairs) -> searchVal key pairs |
			_ -> failwith("not a dict")) |

	Add(d,k,v) -> 
		(let x = (eval d r) in match x with
			DictVal(pairs) -> DictVal(addVal pairs k (eval v r) ) |
			_ -> failwith("not a dict")) |

	Remove(d,key) -> 
		(let x = (eval d r) in match x with
			DictVal(lis) -> DictVal(removeVal key lis) |
			_ -> failwith("not a dict")) |

	Clear(d) ->
		(let x = (eval d r) in match x with
			DictVal(lis) -> DictVal(evalList [ ] r) |
			_ -> failwith("not a dict")) |

	ApplyOver(ex,d) -> 
		match d with
			Dict(dict) -> DictVal(applyOverList ex dict r) |
			_-> failwith("not a dict") 

	and	evalList (lis : (ide * exp) list) (r1 : evT env) : (ide * evT) list = match lis with
		[ ] -> [ ] |
		(key, value) :: pairs -> let v1 = (eval value r1) in (key, v1) :: (evalList pairs r1)

	and searchVal (id : ide) (lis : (ide * evT) list) : evT = match lis with
		[ ] -> failwith("Val not found") |
		(key, value) :: pairs -> if id = key then value else searchVal id pairs

	and addVal (lis : (ide * evT) list) (id : ide) (v : evT) : (ide * evT) list = 
		if search id lis then failwith("key exists already") else (id, v) :: lis

	and removeVal (id : ide) (lis : (ide * evT) list) : (ide * evT) list = match lis with
		[ ] -> [ ] |
		(key, value) :: pairs -> if id = key then pairs else (key, value) :: (removeVal id pairs)

	and applyOverList (g : exp) (lis : (ide * exp) list) (rr : evT env) : (ide * evT) list = match lis with
		[ ] -> [ ] |
		(key, value) :: pairs -> (key, (eval (FunCall(g, value)) rr)) :: (applyOverList g pairs rr)

	and	evalListD (lis : (ide * exp) list) (r1 : evT env) : (ide * evT) list = match lis with
		[ ] -> [ ] |
		(key, value) :: pairs -> let v1 = (eval_dyn value r1) in (key, v1) :: (evalList pairs r1)

	and applyOverListD (g : exp) (lis : (ide * exp) list) (rr : evT env) : (ide * evT) list = match lis with
		[ ] -> [ ] |
		(key, value) :: pairs -> (key, (eval_dyn (FunCall(g, value)) rr)) :: (applyOverList g pairs rr)

(*interprete dinamico*)
	and eval_dyn (e : exp) (r : evT env) : evT = match e with
		Eint n -> Int n |
		Ebool b -> Bool b |
		Estring s -> String s |
		IsZero a -> iszero (eval_dyn a r) |
		Den i -> applyenv r i |
		Eq(a, b) -> eq (eval_dyn a r) (eval_dyn b r) |
		Prod(a, b) -> prod (eval_dyn a r) (eval_dyn b r) |
		Sum(a, b) -> sum (eval_dyn a r) (eval_dyn b r) |
		Diff(a, b) -> diff (eval_dyn a r) (eval_dyn b r) |
		Minus a -> minus (eval_dyn a r) |
		And(a, b) -> et (eval_dyn a r) (eval_dyn b r) |
		Or(a, b) -> vel (eval_dyn a r) (eval_dyn b r) |
		Not a -> non (eval_dyn a r) |
		Ifthenelse(a, b, c) -> 
			let g = (eval_dyn a r) in
				if (typecheck "bool" g) 
					then (if g = Bool(true) then (eval_dyn b r) else (eval_dyn c r))
					else failwith ("nonboolean guard") |
		Let(i, e1, e2) -> eval_dyn e2 (bind r i (eval_dyn e1 r)) |
		Fun(i, a) -> DynFunVal(i, a) |
		FunCall(f, eArg) -> 
			let fClosure = (eval_dyn f r) in
				(match fClosure with
					DynFunVal(arg, fBody) -> 
						let v = (eval_dyn eArg r) in eval_dyn fBody (bind r arg v) |
					DynRecFunVal(g, (arg, fBody)) -> 
						let aVal = (eval_dyn eArg r) in
							let rEnv = (bind r g fClosure) in
								let aEnv = (bind rEnv arg aVal) in
									eval_dyn fBody aEnv |
					_ -> failwith("non functional value")) |
	    Letrec(f, funDef, letBody) ->
    		(match funDef with
        		Fun(i, fBody) -> let r1 = (bind r f (DynRecFunVal(f, (i, fBody)))) in
                     			                eval_dyn letBody r1 |
        		_ -> failwith("non functional def")) |
				
		Dict(d) -> 
			if invariant d then DictVal(evalListD d r) 
				else failwith("dict invariant not preserved")|

		Get(d, key) -> 
			(let x = (eval_dyn d r) in match x with
				DictVal(pairs) -> searchVal key pairs |
				_ -> failwith("not a dict")) |

		Add(d, k, v) -> 
			(let x = (eval_dyn d r) in match x with
				DictVal(pairs) -> DictVal(addVal pairs k (eval_dyn v r) ) |
				_ -> failwith("not a dict")) |

		Remove(d,key) -> 
			(let x = (eval_dyn d r) in match x with
				DictVal(lis) -> DictVal(removeVal key lis) |
				_ -> failwith("not a dict")) |

		Clear(d) ->
			(let x = (eval_dyn d r) in match x with
				DictVal(lis) -> DictVal(evalListD [ ] r) |
				_ -> failwith("not a dict")) |

		ApplyOver(ex,d) -> 
			match d with
				Dict(dict) -> DictVal(applyOverListD ex dict r) |
				_-> failwith("not a dict") ;;