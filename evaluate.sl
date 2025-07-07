(set-logic BV)

(define-fun mult_mxint_exp ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 4)
  (let ((e_sum (bvadd e1 e2)))
    (ite (or (= m1 #b0000) (= m2 #b0000))
        e_sum
        (let ((m_prod (bvmul ((_ zero_extend 4) m1) ((_ zero_extend 4) m2))))
            (ite (bvult m_prod #b10000000)
                 (bvsub e_sum #b0001)
                 e_sum
            )
        )
    )
  )
)

(synth-fun output () (_ BitVec 4))

(constraint (= output (mult_mxint_exp #x9 #x2 #x5 #xf)))

(check-synth)
