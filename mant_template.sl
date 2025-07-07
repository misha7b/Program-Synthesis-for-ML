(set-logic BV)

(synth-fun mult_mxint_mant (
    (m1 (_ BitVec 4)) (e1 (_ BitVec 4))
    (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 4)

    (
     (Start (_ BitVec 4))
     (Expr8 (_ BitVec 8))
     (ShiftAmt (_ BitVec 4))
     (Cond Bool)
    )

    (
      (Start (_ BitVec 4) (
        ((_ extract 3 0) Expr8)
      ))

      (Expr8 (_ BitVec 8) (
        
        #x00  
        #x01  
        ((_ sign_extend 4) m1)
        ((_ sign_extend 4) m2)
        
        ; --- Core Operation ---
        (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))

        ; --- General Operations on 8-bit Expressions ---
        (bvadd Expr8 Expr8)
        (bvsub Expr8 Expr8)
        (bvashr Expr8 ((_ sign_extend 4) ShiftAmt))
        (ite Cond Expr8 Expr8)
      ))
      
      (ShiftAmt (_ BitVec 4) (
        #x2
        #x3
        #x4
      ))
      
      (Cond Bool (
        ; --- Conditions can only use inputs or other conditions ---
        (bvslt m1 #x0)
        (bvslt m2 #x0)
        (= m1 #x0)
        (= m2 #x0)
        (bvsge e1 e2)
        (and Cond Cond)
        (not Cond)
      ))
    )
)