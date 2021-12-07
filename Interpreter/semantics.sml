(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun E(itree(inode("expr",_),
                    [
                        expr,
                        itree(inode("or",_),[]),
                        logical_and
                    ]
                  ),
                  m
                ) =
                let
                    val (dv1, m1) = E(expr, m)
                in
                    if (dvToString dv1) = "false" then
                        let
                            val (dv2,m2) = E(logical_and, m1)
                        in 
                            (dv2, m2)
                        end
                    else
                        (dv1,m1)
                end

  | E(itree(inode("expr",_),
                    [
                        pass
                    ]
                  ),
                  m
                ) = E(pass,m)
  | E(itree(inode("logical_and",_),
                [
                    logical_and,
                    itree(inode("and",_),[]),
                    equality
                ]
              ),
              m
            ) = 
            let
                val (dv1,m1) = E(logical_and,m)
            in
                if (dvToString dv1) = "true" then
                    let
                        val (dv2,m2) = E(equality, m1)
                    in 
                        (dv2, m2)
                    end
                else
                    (dv1,m1)
            end
  | E(itree(inode("logical_and",_),
                [
                    pass
                ]
            ),
            m
        ) = E(pass,m)
  | E(itree(inode("equality",_),
                [
                    relational1,
                    itree(inode("=",_),[]),
                    relational2
                ]
              ),
              m
            ) = 
            let
                val (dv1, m1) = E(relational1, m)
                val (dv2, m2) = E(relational2, m1)
                val v1_string = dvToString dv1
                val v2_string = dvToString dv2
            in
                if v1_string = "true"
                then (Boolean (v1_string = v2_string), m2)
                else if v1_string = "false"
                then (Boolean (v1_string = v2_string), m2)
                else  (* they are both INT *)
                    let
                        val v1_num = valOf(Int.fromString v1_string)
                        val v2_num = valOf(Int.fromString v2_string)
                    in
                        (Boolean (v1_num = v2_num), m2)
                    end
            end
  | E(itree(inode("equality",_),
                [
                    relational1,
                    itree(inode("!=",_),[]),
                    relational2
                ]
              ),
              m
            ) = 
            let
                val (dv1, m1) = E(relational1, m)
                val (dv2, m2) = E(relational2, m1)
                val v1_string = dvToString dv1
                val v2_string = dvToString dv2
            in
                if v1_string = "true"
                then (Boolean (v1_string <> v2_string), m2)
                else if v1_string = "false"
                then (Boolean (v1_string <> v2_string), m2)
                else  (* they are INT *)
                    let
                        val v1_num = valOf(Int.fromString v1_string)
                        val v2_num = valOf(Int.fromString v2_string)
                    in
                        (Boolean (v1_num <> v2_num), m2)
                    end
            end
                 
  | E(itree(inode("equality",_),
                [
                    pass
                ]
            ),
            m
        ) = E(pass,m)
  | E(itree(inode("relational",_),
                    [
                        additive1,
                        itree(inode(">=",_),[]),
                        additive2
                    ]
                ),
                m
            ) = 
            let
                val (dv1,m1) = E(additive1, m)
                val (dv2,m2) = E(additive2, m1)
                val v1_int = valOf(Int.fromString(dvToString dv1))
                val v2_int = valOf(Int.fromString(dvToString dv2))
                val v3_bool = v1_int >= v2_int
            in
                if v3_bool = true
                then (Boolean true, m2)
                else (Boolean false, m2)
            end
  | E(itree(inode("relational",_),
                    [
                        additive1,
                        itree(inode(">",_),[]),
                        additive2
                    ]
                ),
                m
            ) = 
            let
                val (dv1,m1) = E(additive1, m)
                val (dv2,m2) = E(additive2, m1)
                val v1_int = valOf(Int.fromString(dvToString dv1))
                val v2_int = valOf(Int.fromString(dvToString dv2))
                val v3_bool = v1_int > v2_int
            in
                if v3_bool = true
                then (Boolean true, m2)
                else (Boolean false, m2)
            end
  | E(itree(inode("relational",_),
                    [
                        additive1,
                        itree(inode("<=",_),[]),
                        additive2
                    ]
                ),
                m
            ) = 
            let
                val (dv1,m1) = E(additive1, m)
                val (dv2,m2) = E(additive2, m1)
                val v1_int = valOf(Int.fromString(dvToString dv1))
                val v2_int = valOf(Int.fromString(dvToString dv2))
                val v3_bool = v1_int <= v2_int
            in
                if v3_bool = true
                then (Boolean true, m2)
                else (Boolean false, m2)
            end
  | E(itree(inode("relational",_),
                    [
                        additive1,
                        itree(inode("<",_),[]),
                        additive2
                    ]
                ),
                m
            ) = 
            let
                val (dv1,m1) = E(additive1, m)
                val (dv2,m2) = E(additive2, m1)
                val v1_int = valOf(Int.fromString(dvToString dv1))
                val v2_int = valOf(Int.fromString(dvToString dv2))
                val v3_bool = v1_int < v2_int
            in
                if v3_bool = true
                then (Boolean true, m2)
                else (Boolean false, m2)
            end
  | E(itree(inode("relational",_),
          [
              pass
          ]
      ),
      m
  ) = E(pass,m)
  | E(itree(inode("additive",_),
                    [
                        additive,
                        itree(inode("+",_),[]),
                        multiplicative
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1, m2) = E(additive, m)
                    val (dv2, m1) = E(multiplicative, m)
                    val v1_int = valOf(Int.fromString(dvToString dv1))
                    val v2_int = valOf(Int.fromString(dvToString dv2))
                    val v3_int = v1_int + v2_int
                in
                    (Integer v3_int, m2)
                end
  | E(itree(inode("additive",_),
                    [
                        additive,
                        itree(inode("-",_),[]),
                        multiplicative
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1, m1) = E(additive, m)
                    val (dv2, m2) = E(multiplicative, m)
                    val v1_int = valOf(Int.fromString(dvToString dv1))
                    val v2_int = valOf(Int.fromString(dvToString dv2))
                    val v3_int = v1_int - v2_int
                in 
                    (Integer v3_int, m2)
                end
  | E(itree(inode("additive",_),
                [
                    pass
                ]
            ),
            m
        ) = E(pass,m)
  | E(itree(inode("multiplicative",_),
                    [
                        multiplicative,
                        itree(inode("*",_),[]),
                        negation
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1, m1) = E(multiplicative, m)
                    val (dv2, m2) = E(negation, m)
                    val v1_int = valOf(Int.fromString(dvToString dv1))
                    val v2_int = valOf(Int.fromString(dvToString dv2))
                    val v3_int = v1_int * v2_int
                in 
                    (Integer v3_int, m2)
                end
                
  | E(itree(inode("multiplicative",_),
                    [
                        multiplicative,
                        itree(inode("div",_),[]),
                        negation
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1, m1) = E(multiplicative, m)
                    val (dv2, m2) = E(negation, m)
                    val v1_int = valOf(Int.fromString(dvToString dv1))
                    val v2_int = valOf(Int.fromString(dvToString dv2))
                    val v3_int = v1_int div v2_int
                in 
                    (Integer v3_int, m2)
                end
  | E(itree(inode("multiplicative",_),
                    [
                        multiplicative,
                        itree(inode("mod",_),[]),
                        negation
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1, m1) = E(multiplicative, m)
                    val (dv2, m2) = E(negation, m)
                    val v1_int = valOf(Int.fromString(dvToString dv1))
                    val v2_int = valOf(Int.fromString(dvToString dv2))
                    val v3_int = v1_int mod v2_int
                in 
                    (Integer v3_int, m2)
                end
  | E(itree(inode("multiplicative",_),
                [
                    pass
                ]
            ),
            m
        ) = E(pass,m)
  | E(itree(inode("negation",_),
                [
                    itree(inode("-",_),[]),
                    exponentiation
                ]
            ),
            m
        ) = 
        let
            val (dv,m1) = E(exponentiation,m)
            val v_num = valOf(Int.fromString (dvToString dv))
        in
            (Integer (~v_num), m1)
        end
  | E(itree(inode("negation",_),
                [
                    itree(inode("not",_),[]),
                    exponentiation
                ]
            ),
            m
        ) = 
        let
            val (dv,m1) = E(exponentiation,m)
            val v_bool = dvToString dv
        in
            if v_bool = "true"
            then (Boolean false, m1)
            else (Boolean true, m1)
        end
  | E(itree(inode("negation",_),
                [
                    pass
                ]
            ),
            m
        ) = E(pass,m)
  | E(itree(inode("exponentiation",_),
                [
                    final,
                    itree(inode("^",_),[]),
                    exponentiation
                ]
              ),
              m
            ) = 
            let
                fun expo (a,0) = 1 | expo (a,b) = a * expo(a,b-1);
                val (dv1,m1) = E(final, m)
                val (dv2, m2) = E(exponentiation, m1)
                val dv1_string = dvToString dv1
                val dv2_string = dvToString dv2
                val v1_num = valOf(Int.fromString dv1_string)
                val v2_num = valOf(Int.fromString dv2_string)
                val v3 = expo (v1_num, v2_num)
            in
                (Integer v3, m2)
            end
  | E(itree(inode("exponentiation",_),
                [
                    pass
                ]
            ),
            m
        ) = E(pass,m)
        
  | E(itree(inode("final",_),
                [
                    boolean as itree(inode("true",_),children)
                ]
            ),
            m
        ) = (Boolean true,m)

  | E(itree(inode("final",_),
                [
                    boolean as itree(inode("false",_),children)
                ]
            ),
            m
        ) = (Boolean false,m)
  
  | E(itree(inode("final",_),
                    [
                        integer as itree(inode("integer",_),children)
                    ]
                ),
                m
            ) = 
            let
                val int_string = getLeaf(integer)
                val int_num = valOf(Int.fromString int_string)
            in
                (Integer int_num, m)
            end
  | E(itree(inode("final",_),
                [
                    id as itree(inode("id",_),children)
                ]
              ),
              m
            ) = 
            let
                val id_string = getLeaf(id)
                val loc = getLoc(accessEnv(id_string, m))
                val dv = accessStore(loc, m)
                
            in
                (dv, m)
            end
  | E(itree(inode("final",_),
                [
                    
                    itree(inode("(",_),[]),
                    expr,
                    itree(inode(")",_),[])
                ]
            ),
            m
        ) = E(expr, m)
        
  | E(itree(inode("final",_),
                [
                    
                    itree(inode("|",_),[]),
                    expr,
                    itree(inode("|",_),[])
                ]
            ),
            m
        ) = 
        let
            val (dv,m1) = E(expr,m)
            val v_num = valOf(Int.fromString( dvToString dv))
        in
            if v_num < 0
            then (Integer (~v_num), m1)
            else (Integer v_num, m1)
        end
        

  | E(itree(inode("final",_),
                [
                    change
                ]
              ),
              m
            ) = E(change, m)
  | E(itree(inode("change",_),
                [
                    pass
                ]
              ),
              m
            ) = E(pass, m)
  | E(itree(inode("pre_inc",_),
                [
                    itree(inode("++",_),[]),
                    id
                ]
              ),
              m
            ) =
            let
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v+1
                    val m1 = updateStore(loc, (Integer updated_v), m)
            in
                (Integer updated_v, m1)
            end
  | E(itree(inode("post_inc",_),
                [
                    id,
                    itree(inode("++",_),[])
                ]
              ),
              m
            ) =
            let
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v+1
                    val m1 = updateStore(loc, (Integer updated_v), m)
            in
                (Integer v, m1)
            end
  | E(itree(inode("pre_dec",_),
                [
                    itree(inode("--",_),[]),
                    id
                ]
              ),
              m
            ) =
            let
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v-1
                    val m1 = updateStore(loc, (Integer updated_v), m)
            in
                (Integer updated_v, m1)
            end
  | E(itree(inode("post_dec",_),
                [
                    id,
                    itree(inode("--",_),[])
                ]
              ),
              m
            ) =
            let
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v-1
                    val m1 = updateStore(loc, (Integer updated_v), m)
            in
                (Integer v, m1)
            end

  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\n In E root = " ^ x_root ^ "\n\n")
  
  | E _ = raise Fail("error in Semantics.E - this should never occur");

                
fun M(itree(inode("prog",_), 
                [ 
                    statement_list
                ] 
            ), 
            m
        ) = M(statement_list,m)
    
  | M(itree(inode("statement_list",_),
                [
                    statement,
                    itree(inode(";",_),[]),
                    statement_list
                ]
            ),
            m
        ) = M(statement_list, M(statement,m))
        
  | M(itree(inode("statement_list",_),
                [
                    epsilon
                ]
            ),
            m
        ) = m

  | M(itree(inode("statement",_),
                  [
                    any_statement
                  ]
                ),
                m
              ) = M(any_statement,m)
              


  | M(itree(inode("decl",_),
                [
                    itree(inode("bool",_),[]),
                    id
                ]
            ),
            m
        ) =
        let
          val (env,addr,s) = m
          val id_string = getLeaf(id)
          val m1 = updateEnv(id_string, BOOL, new(m),(env,new(m),s));
        in
          m1
        end
        
  | M(itree(inode("decl",_),
                [
                    itree(inode("int",_),[]),
                    id
                ]
            ),
            m
        ) =
        let
          val (env,addr,s) = m
          val id_string = getLeaf(id)
          val m1 = updateEnv(id_string, INT, new(m),(env,new(m),s));
        in
          m1
        end

  | M(itree(inode("assign",_),
                [
                    id,
                    itree(inode(":=",_),[]),
                    expr
                ]
            ),
            m
        ) = 
        let
            val id_string = getLeaf(id)
            val loc = getLoc(accessEnv(id_string, m))
            val (dv, m1) = E(expr, m)
            val m2 = updateStore(loc, dv, m1)
        in
            m2
        end
 
   | M(itree(inode("init",_),
                [
                    itree(inode("bool",_),[]),
                    id,
                    itree(inode(":=",_),[]),
                    expr
                ]
              ),
              m
            ) =
            let
                val (env,addr,s) = m
                val id_string = getLeaf(id)
                val m1 = updateEnv(id_string, BOOL, new(m),(env,new(m),s))

                val loc = getLoc(accessEnv(id_string, m1))
                val (dv, m2) = E(expr, m1)
                val m3 = updateStore(loc, dv, m2)             
            in
                m3
            end
   | M(itree(inode("init",_),
                [
                    itree(inode("int",_),[]),
                    id,
                    itree(inode(":=",_),[]),
                    expr
                ]
              ),
              m
            ) =
            let
                val (env,addr,s) = m
                val id_string = getLeaf(id)
                val m1 = updateEnv(id_string, INT, new(m),(env,new(m),s))
                val loc = getLoc(accessEnv(id_string, m1))
                val (dv, m2) = E(expr, m1)
                val m3 = updateStore(loc, dv, m2)           
            in
                m3
            end
            
            
  | M(itree(inode("change",_),
                    [
                        pass
                    ]
                  ),
                  m
                ) = M(pass,m)
                
  | M(itree(inode("pre_inc",_),
                    [
                        itree(inode("++",_),[]),
                        id
                    ]
                  ),
                  m
                ) = 
                let 
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v+1
                    val m1 = updateStore(loc, (Integer updated_v), m)
                in
                    m1
                end
                
  | M(itree(inode("post_inc",_),
                    [
                        id,
                        itree(inode("++",_),[])
                    ]
                  ),
                  m
                ) = 
                let 
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v+1
                    val m1 = updateStore(loc, (Integer updated_v), m)
                in
                    m1
                end
                
                
  | M(itree(inode("pre_dec",_),
                    [
                        itree(inode("--",_),[]),
                        id
                    ]
                  ),
                  m
                ) = 
                let 
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v-1
                    val m1 = updateStore(loc, (Integer updated_v), m)
                in
                    m1
                end
                
  | M(itree(inode("post_dec",_),
                    [
                        id,
                        itree(inode("--",_),[])
                    ]
                  ),
                  m
                ) = 
                let 
                    val id_string = getLeaf(id)
                    val loc = getLoc(accessEnv(id_string, m)) 
                    val dv = accessStore(loc, m)
                    val v = valOf(Int.fromString (dvToString dv))
                    val updated_v = v-1
                    val m1 = updateStore(loc, (Integer updated_v), m)
                in
                    m1
                end
                
  | M(itree(inode("print_result",_),
                    [
                        itree(inode("print",_),[]),
                        expr
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv,m1) = E(expr,m)
                    val _ = print (dvToString dv)
                in
                    m1
                end
  | M(itree(inode("block",_),
                    [
                        itree(inode("{",_),[]),
                        statement_list,
                        itree(inode("}",_),[])
                    ]
                  ),
                  (env0,addr,s0)
                ) =
                let
                    val (env1,addr,s1) = M(statement_list, (env0,addr,s0))
                    val m2 = (env0,addr,s1)
                in
                    m2
                end

  | M(itree(inode("branch",_),
                    [
                        itree(inode("if",_),[]),
                        expr,
                        itree(inode("then",_),[]),
                        block
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1,m1) = E(expr,m)
                in
                    if (dvToString dv1) = "true" then
                        let 
                            val m2 = M(block, m1)
                        in
                            m2
                        end
                    else
                        m1
                end
  | M(itree(inode("branch",_),
                    [
                        itree(inode("if",_),[]),
                        expr,
                        itree(inode("then",_),[]),
                        block1,
                        itree(inode("else",_),[]),
                        block2
                    ]
                  ),
                  m
                ) = 
                let
                    val (dv1,m1) = E(expr,m)
                in
                    if (dvToString dv1) = "true" then
                        let 
                            val m2 = M(block1, m1)
                        in
                            m2
                        end
                    else
                        let
                            val m2 = M(block2, m1)
                        in
                            m2
                        end
                end
                

  | M(itree(inode("while_loop",_),
                    [
                        itree(inode("while",_),[]),
                        expr,
                        itree(inode("do",_),[]),
                        block
                    ]
                  ),
                  m
                ) =
                let
                    fun W(expr0,block0,m0) =
                        let
                            val (dv1,m1) = E(expr0,m0)
                            val v1_string = dvToString dv1
                        in
                            if v1_string = "true" then
                                let
                                    val m2 = M(block0, m1)
                                    val m3 = W(expr0, block0, m2)
                                in
                                    m3
                                end
                            else
                                m1
                        end
                in
                    W(expr, block, m)
                end


(*
  | M(itree(inode("for_loop",_),
                    [
                        itree(inode("for",_),[]),
                        itree(inode("(",_),[]),
                        init,
                        itree(inode(";",_),[]),
                        expr,
                        itree(inode(";",_),[]),
                        change,
                        itree(inode(")",_),[]),
                        block
                    ]
                  ),
                  m
                ) =
                let
                    fun F(expr0,change0,block0,m0) = 
                        let
                            val (dv1,m1) = E(expr0,m0)
                        in
                            if (dvToString dv1) = "true" then
                                let
                                    val m2 = M(block0,m1)
                                    val m3 = M(change0, m2)
                                    val m4 = F(expr0,change0,block0,m3)
                                in
                                    m4
                                end
                            else
                                m1
                        end
                    
                    val (env1,addr,s1) = M(init,m)
                    val (env2,addr,s2) = F(expr,change,block,(env1,addr,s1))
                    val m5 = (env2,addr,s1)
                in
                    m5
                end
*)

  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\n In M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur");
          

        
        
        

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








