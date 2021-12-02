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


val model = initialModel;

    (* prog ::= statement_list *)
fun M(  itree(inode("prog",_), 
                [ 
                   statement_list
                ] 
             ), 
        m
    ) = M(statement_list, m)
    (* statement_list ::= statement ; *)
  | M(itree(inode("statement_list",_),
                [
                    itree(inode("statement",_),_),
                    itree(inode(";",_),[])
                ]
            ),
            m
        ) = M(itree(inode("statement",_),_), m)
    (* statement_list ::= statement ; statement_list *)
  | M( itree(inode("statement_list",_),
                [
                    statement,
                    itree(inode(";",_),[]),
                    statement_list
                ]
            ),
            m
        ) = M(statement_list, M(statement,m) )
    (* statement ::= int id1 *)
  | M(itree(inode("statement",_),
                  [
                    itree(inode("int",_), []),
                    id
                  ]
                ),
                m
              ) = 
              let
                val (env,addr0,s) = m;
              in 
                updateEnv(id, INT, new(m), (env,new(m),s))
              end
  | M(itree(inode("statement",_),
                  [
                    assign
                  ]
                ),
                m
              ) = M(assign,m)
  | M(itree(inode("statement",_),
                  [
                    decl
                  ]
                ),
                m
              ) = M(decl,m)
  | M(itree(inode("statement",_),
                  [
                    block
                  ]
                ),
                m
              ) = M(block,m)
  | M(itree(inode("statement",_),
                  [
                    for_loop
                  ]
                ),
                m
              ) = M(for_loop,m)
  | M(itree(inode("statement",_),
                  [
                    while_loop
                  ]
                ),
                m
              ) = M(while_loop,m);
  | M(itree(inode("statement",_),
                  [
                    branch
                  ]
                ),
                m
              ) = M(branch,m)
  | M(itree(inode("statement",_),
                  [
                    change
                  ]
                ),
                m
              ) = M(change,m)
  | M(itree(inode("statement",_),
                  [
                    print_result
                  ]
                ),
                m
              ) = M(print_result,m)
    (* init ::= int id := expr *)
  | M(itree(inode("init",_),
                  [
                    itree(inode("int",_)[]),
                    id,
                    itree(inode(":=",_),[]),
                    expr
                  ]
                ),
                m
              ) = 
              let
                val (env,addr,s) = m;
                val m1 = updateEnv(id, INT, new(m), (env,new(m),s));
                val (v1,m2) = E(expr, m1);
                val loc = getLoc(accessEnv(id,m2));
                val m3 = updateStore(loc,v1,m2)
              in
                m3
              end
    (* init ::= bool id := expr *)
  | M(itree(inode("init",_),
                  [
                    itree(inode("bool",_)[]),
                    id,
                    itree(inode(":=",_),[]),
                    expr
                  ]
                ),
                m
              ) = 
              let
                val (env,addr,s) = m;
                val m1 = updateEnv(id, BOOL, new(m), (env,new(m),s));
                val (v1,m2) = E(expr, m1);
                val loc = getLoc(accessEnv(id,m2));
                val m3 = updateStore(loc,v1,m2)
              in
                m3
              end
    (* assign ::= id := expression *)
  | M(itree(inode("assign",_),
                [
                    id1,
                    itree(inode(":=",_),[]),
                    expression1
                ]
            ),
            m
        ) = 
        let
          val (v1,m1) = E(expression1, m)
          val loc1 = getLoc(accessEnv(id1,m1))
          val m2 = updateStore(loc1,v1,m1)
        in
          m2
        end
    (* decl ::= int id *)
  | M(itree(inode("decl",_),
                [
                    itree(inode("int",_),[]),
                    id
                ]
            ),
            model
        ) = 
        let
          val (env,addr,s) = model;
          val m1 = updateStore(id,INT,new(model),(env,new(model),s));
        in
          m1
        end
    (* decl ::= bool id *)
  | M(itree(inode("decl",_),
                [
                    itree(inode("bool",_),[]),
                    id
                ]
            ),
            model
        ) = 
        let
          val (env,addr,s) = model;
          val m1 = updateStore(id,BOOL,new(model),(env,new(model),s));
        in
          m1
        end
    (*id ::= identifier *)
  | M(itree(inode("id",_),
                [
                  identifier
                ]
              ),
              m
            ) = accessStore(getStore(accessEnv(identifier,m)),m)
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
                val (env1,s1) = M(statement_list, (env0,addr,s0));
                val m2 = (env0,addr,s1)
              in
                m2
              end
  | M(itree(inode("for_loop",_),
                  [
                    itree(inode("for",_),[]),
                    itree(inode("(",_),[]),
                    init
                    itree(inode(";",_),[]),
                    expr
                    itree(inode(";",_),[]),
                    change
                    itree(inode(")",_),[]),
                    block 
                  ]
                ),
                m
              ) = 
              let
                fun for_loop_eval(expr0,change0,block0,m0) = 
                  let
                    val (v1,m1) = E(expr0,m0)
                  in
                    if v1 = true then
                      let
                        val m2 = M(block0,m1);
                        val m3 = M(change0,m2);
                        val m4 = for_loop_eval(expr0,change0,block0,m3);
                      in
                        m4
                      end
                    else
                      m1
                  end
                val (env1,addr,s1) = M(init,m);
                val (env2,addr,s2) =
                  for_loop_eval(expr,change,block,(env1,adde,s1));
                val m1 = (env2,addr,s1)
              in
                m1
              end
  | M(itree(inode("while_loop",_),
                  [
                    itree(inode("while",_),[]),
                    itree(inode("(",_),[]),
                    expr,
                    itree(inode(")",_),[]),
                    block
                  ]
                ),
                m
              ) = 
              let
                fun while_loop_eval(expr0,block0,m0) = 
                  let
                    val (v1,m1) = E(expr0,m0);
                  in
                    if v1 then 
                      let 
                        val m2 = M(block0,m1);
                        val m3 = while_loop_eval(expr0,block0,m2);
                      in
                        m3
                      end
                    else
                      m1
                  end 
              in
                while_loop_eval(expr, block, m)
              end
  | M(itree(inode("branch",_),
                  [
                    itree(inode("if",_),[]),
                    itree(inode("(",_),[]),
                    expr,
                    itree(inode(")",_),[]),
                    block1,
                    itree(inode("else",_),[]),
                    block2
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(expr,m);
              in
                if v1 then
                  let
                    val m2 = M(block1,m1);
                  in 
                    m2
                  end
                else
                  let
                    val m2 = M(block2,m1)
                  in
                    m2
                  end
              end
  | M(itree(inode("branch",_),
                  [
                    itree(inode("if",_),[]),
                    itree(inode("(",_),[]),
                    expr,
                    itree(inode(")",_),[]),
                    block
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(expr,m);
              in
                if v1 then
                  let
                    val m2 = M(block,m1);
                  in
                    m2
                  end
                else
                  m1
              end
  | M(itree(inode("change",_),
                  [
                    pre_inc
                  ]
                ),
                m
              ) = M(pre_inc,m)
  | M(itree(inode("change",_),
                  [
                    post_inc
                  ]
                ),
                m
              ) = M(post_inc,m)
  | M(itree(inode("change",_),
                  [
                    pre_dec
                  ]
                ),
                m
              ) = M(pre_dec,m)
  | M(itree(inode("change",_),
                  [
                    post_dec
                  ]
                ),
                m
              ) = M(post_dec,m)
                    
  | M(itree(inode("pre_inc",_),
                  [
                    itree(inode("++",_),[]),
                    id
                  ]
                ),
                m
              ) =
              let
                val (v1,m1) = E(id,m)
                val loc = getLoc(accessEnv(id,m1)
                val v2 = v1+1
                val m2 = updateStore(loc,v2,m1)
              in
                m2
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
                val (v1,m1) = E(id,m)
                val loc = getLoc(accessEnv(id,m1)
                val v2 = v1+1
                val m2 = updateStore(loc,v2,m1)
              in
                m2
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
                val (v1,m1) = E(id,m)
                val loc = getLoc(accessEnv(id,m1)
                val v2 = v1-1
                val m2 = updateStore(loc,v2,m1)
              in
                m2
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
                val (v1,m1) = E(id,m)
                val loc = getLoc(accessEnv(id,m1)
                val v2 = v1-1
                val m2 = updateStore(loc,v2,m1)
              in
                m2
              end

  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")


fun E(itree(inode("expr",_),
                  [
                    expr
                    itree(inode("or",_),[]),
                    logical_and
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(expr,m);
              in
                if v1 then
                  let
                    val (v2,m2) = E(logical_and, m1);
                  in
                    (v2,m2)
                  end
                else
                  (v1,m1)
              end
  | E(itree(inode("expr",_),
                  [
                    logical_and
                  ]
                ),
                m
              ) = E(logical_and,m)
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
                      val (v1,m1) = E(logical_and,m1);
                    in
                      if v1 = false then
                        let
                          val (v2,m2) = E(equality,m1);
                        in
                          (v2,m2)
                        end
                      else
                        (v1,m1)
                    end
  | E(itree(inode("logical_and",_),
                        [
                          equality
                        ]
                      ),
                      m
                    ) = E(equality,m)
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
                      val (v1,m1) = E(relational1, m)
                      val (v2,m2) = E(relational2, m1)
                    in
                      (v1 = v2, m2)
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
                      val (v1,m1) = E(relational1, m)
                      val (v2,m2) = E(relational2, m1)
                    in
                      (v1 <> v2, m2)
                    end
  | E(itree(inode("equality",_),
                    [
                      relational
                    ]
                  ),
                  m
                ) = E(relational,m)
  | E(itree(inode("relational", _),
                  [
                    additive1,
                    itree(inode("<",_),[]),
                    additive2
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(additive1,m)
                val (v2,m2) = E(additive2,m)
              in
                (v1 < v2, m2)
              end
  | E(itree(inode("relational", _),
                  [
                    additive1,
                    itree(inode(">",_),[]),
                    additive2
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(additive1,m)
                val (v2,m2) = E(additive2,m)
              in
                (v1 > v2, m2)
              end
  | E(itree(inode("relational", _),
                  [
                    additive1,
                    itree(inode(">=",_),[]),
                    additive2
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(additive1,m)
                val (v2,m2) = E(additive2,m)
              in
                (v1 >= v2, m2)
              end
  | E(itree(inode("relational", _),
                  [
                    additive1,
                    itree(inode("<=",_),[]),
                    additive2
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(additive1,m)
                val (v2,m2) = E(additive2,m)
              in
                (v1 <= v2, m2)
              end
  | E(itree(inode("relational",_), [additive]),m) = E(additive,m)

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
                  val (v1,m1) = E(additive,m)
                  val (v2,m2) = E(multiplicative,m)
                in
                  (v1 + v2, m2)
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
                  val (v1,m1) = E(additive,m)
                  val (v2,m2) = E(multiplicative,m)
                in
                  (v1 - v2, m2)
                end
  | E(itree(inode("additive",_), [additive]),m) = E(additive,m)
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
                  val (v1,m1) = E(multiplicative,m)
                  val (v2,m2) = E(negation,m1)
                in
                  (v1 * v2, m2)
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
                  val (v1,m1) = E(multiplicative,m)
                  val (v2,m2) = E(negation,m1)
                in
                  (v1 div v2, m2)
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
                  val (v1,m1) = E(multiplicative,m)
                  val (v2,m2) = E(negation,m1)
                in
                  (v1 mod v2, m2)
                end
  | E(itree(inode("multiplicative",_),
                    [
                      negation
                    ]
                  ),
                  m
                ) = E(negation,m)
  | E(itree(inode("negation",_),
                    [
                      itree(inode("not",_),[]),
                      negation
                    ]
                  ),
                  m
                ) = 
                let
                  val v = E(negation,m)
                in
                  not v
                end
  | E(itree(inode("negation",_),
                    [
                      itree(inode("-",_),[]),
                      negation
                    ]
                  ),
                  m
                ) = 
                let
                  val v = E(negation,m)
                in
                  0 - v
                end
  | E(itree(inode("negation",_),
                    [
                      exponentiation
                    ]
                  ),
                  m
                ) = E(exponentiation,m)
  | E(itree(inode("exponentiation",_),
                    [
                      final
                      itree(inode("^",_),[]),
                      exponentiation
                    ]
                  ),
                  m
                ) = 
                let
                  val (v1,m1) = E(final,m)
                  val (v2,m2) = E(exponentiation,m1)
                  fun expo (a,0) = a
                    | expo (a,b) = a * expo(b - 1)
                in
                  (expo(v1,v2),m2)
  | E(itree(inode("exponentiation",_),[final]),m) = E(final,m)
  | E(itree(inode("final",_),
                    [
                      itree(inode("(",_),[]),
                      expr,
                      itree(inode(")",_),[])
                    ]
                  ),
                  m
                ) = E(expr,m)
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
                  val (v1,m1) = E(expr,m)
                in
                  if v1 < 0 then
                    (-v1,m1)
                  else
                    (v1,m1)
                end
  | E(itree(inode("final",_),
                    [
                      id
                    ]
                  ),
                  m
                ) = 
                let
                  val loc = getLoc(accessEnv(id,m))
                  val v1 = accessStore(loc,m)
                in
                  (v1,m)
                end
  | E(itree(inode("final",_),
                  [
                    integer
                  ]
                ),
                m
              ) = (integer,m)
  | E(itree(inode("final",_),
                  [
                    true
                  ]
                ),
                m
              ) = (true,m)
  | E(itree(inode("final",_),
                  [
                    false
                  ]
                ),
                m
              ) = (false,m)
  | E(itree(inode("final",_),
                  [
                    change
                  ]
                ),
                m
              ) = 
              let
                val (v1,m1) = E(change,m)
              in
                (v1,m1)
              end
      (* This is not the right way to do print, i dont think it shoudl be an E
      * function, probably just an M *)
  | E(itree(inode("print_result",_),
                    [
                      itree(inode("print",_),[]),
                      expr
                    ]
                  ),
                  m
                ) = 
                let
                  val (v1,m1) = E(expr,m);
                in
                  print v1;
                  (v1,m1)
                end

  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
  | E _ = raise Fail("error in Semantics.M - this should never occur")
              


(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)


