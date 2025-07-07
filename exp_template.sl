(set-logic BV)

(synth-fun mult_mxint_exp (
    (m1 (_ BitVec 4)) (e1 (_ BitVec 4))
    (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 4)

    (
     (Start (_ BitVec 4))
     (Expr4 (_ BitVec 4))
     (Cond Bool)
    )

    (
      (Start (_ BitVec 4) (
        Expr4
      ))

      (Expr4 (_ BitVec 4) (
        e1
        e2
        #x0
        #x1
        #x3
        (bvadd e1 e2)
        (bvadd Expr4 Expr4)
        (bvsub Expr4 Expr4)
        (ite Cond Expr4 Expr4)
      ))
      
      (Cond Bool (
        (bvsgt (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2)) (_ bv56 8))
        (and (not (= (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2)) #x00))
             (bvsle (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2)) #x08))
        (or (= m1 #x0) (= m2 #x0))
      ))
    )
)

