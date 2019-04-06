
(* =============================  TESTS  ================= *)

(* basico: no let *)
let env0 = emptyenv Unbound;; 

(*Dizionario vuoto*)
let emptydict = Dict[];;

eval emptydict env0;; 

(*Dizionario con uno o più elementi*)
let my_dict = Dict[("key", Eint 10);("key2", Estring "data")];;

eval my_dict env0;;

(*ERROR:Dizionario con chivi uguali*)
let my_dict = Dict[("sameKey", Eint 20);("sameKey", Estring "errorExpected")];;

eval my_dict env0;;

(*ricerca tramite chiave di un elemento*)
let value = Get(my_dict, "key");;

eval value env0;;

(*ERROR:ricerca tramite chiave inesistente di un elemento*)
let errorval = Get(my_dict, "notakey");;

eval errorval env0;;

(*aggiunta di una coppia al dizionario*)
let my_dict1 = Dict[("nome", Estring "Marco");("matricola", Eint 123456)];;

let my_dict11 = Add(my_dict1,"eta", Eint 22);;

eval my_dict11 env0;;

(*ERROR: aggiunta di un elemento con key già esistente*)
	let my_dict1 = Dict[("nome", Estring "Giovanni");("matricola", Eint 123456)];;

	let my_dict11 = Add(my_dict1,"nome", Eint 10000);;

	eval my_dict11 env0;;

(*rimozione di un elemento, data la chiave*)
let my_dict2 = Dict[("nome", Estring "Giovanni");("toRemove", Eint 00000)];;

let my_dict3 =  Remove(my_dict2,"toRemove");;

eval my_dict3 env0;;

(*clear di un dizionario*)
let my_dict1 = Dict[("nome", Estring "Giovanni");("matricola", Eint 123456)];;

let my_dict4 =  Clear(my_dict1);;

eval my_dict4 env0;;
(*ApplyOver di una funzione ai valori interi di un dizionario*)
let my_dict2 = Dict[("nome", Eint 10);("matricola", Eint 20)];;

let plusOne = Fun("x", Sum(Den "x", Eint 1));;

let md = ApplyOver(plusOne, my_dict2);;

eval md env0;;


(*ERROR:ApplyOver di una fun in un dizionario con valori a cui non è possibile applicare fun *)
let my_dict3 = Dict[("val", Eint 0);("nome", Estring "Giovanni")];;

let g = Fun("x", Sum(Den "x", Eint 42));;

let md = ApplyOver(g, my_dict3);;

eval md env0;;

	(*prove parte optional*)
let rt = (Let ("x", Eint 1, 
			Let ("f", Fun("y", Den "x"),
				Let ("x", Eint 2, FunCall(Den "f", Eint 0)))));;

let dyn = Rt_eval(rt);;

eval dyn env0;;

(* static = 1
dynamic = 2
 *)

let prova = 
    Let("x", Eint 1,
        Let("g", Fun("z", Sum( Den "z", Den "x")),
            Let("f", Fun("y", 
            	Let("x", Sum(Den "y", Eint 1),
                        FunCall(Den "g", Prod(Den "x", Den "y")))),
                FunCall(Den "f", Eint 3))));;

let test = Rt_eval(prova);;

eval test env0;;
