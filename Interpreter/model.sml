(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 



(* added runtime error, might need to be moved *)
exception runtime_error;

fun error msg = (print msg; raise runtime_error);

(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

fun new (env,addr,s) = addr+1;

fun accessEnv( id1, (env,addr,s) ) =
    let
        val msg = "Error: accessEnv " ^ id1 ^ " not found.";

        fun aux [] = error msg
          | aux ( (id,t,loc)::env ) =
                if id1 = id then (t,loc)
                else aux env;
    in
        aux env
    end;
    
fun accessStore( loc1: int, (env,addr,s) ) =
    let
      val msg = "Error: accessStore " ^ Int.toString loc1 ^ " not found.";

      fun aux [] = error msg
        | aux ( (loc,dv:denotable_value)::s ) =
              if loc1 = loc then dv
              else aux s;
    in
      aux s
    end;
    
    
fun update_aux1( (tuple1 as (x1,y1: types,z1))::env, tuple2 as (x2,y2: types,z2)) =
  if x1 = x2 then tuple2::env
  else            tuple1::update_aux1(env, tuple2)
  | update_aux1([], tuple) = [tuple];

fun updateEnv(id1,t1: types,loc1, (env,addr,s)) =
let
  val new_env = update_aux1(env,(id1,t1,loc1))
in
  (new_env, addr, s)
end;


fun update_aux( (tuple1 as (x1,y1))::flr, tuple2 as (x2,y2)) =
    if x1 = x2 then tuple2::flr
    else            tuple1::update_aux(flr,tuple2)
  | update_aux( [], tuple) = [tuple];

fun updateStore(loc1, dv1, (env,addr,s)) =
let
  val new_store = update_aux(s,(loc1,dv1))
in
  (env,addr,new_store)
end;


fun getLoc(t:types,l: int) = l;
fun getType(t:types,l:int) = t;

fun typeToString BOOL  = "bool"
  | typeToString INT   = "integer"
  | typeToString ERROR = "error";

fun envEntryToString (id,t,loc) =
   "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")";

fun showEnv [] = print "\n"
  | showEnv (entry::env) = (
                           print("\n" ^ envEntryToString entry);
                           showEnv env
                           );

fun dvToString (Boolean x) = Bool.toString x
  | dvToString (Integer y) = Int.toString y;

fun storeEntryToString (loc, dv) =
    "(" ^ Int.toString loc ^ "," ^ dvToString dv ^ ")";

fun showStore [] = print "\n"
  | showStore (entry::store) = (
                                print("\n" ^ storeEntryToString entry);
                                showStore store
                                );

fun printModel (env,addr,s) = (
                              print("\n Enviroment: \n");
                              showEnv env;
                              print("\n Store: \n");
                              showStore s;
                              print("\n next mem loc: \n" ^ Int.toString addr ^
                              "\n")
                              );

(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)












