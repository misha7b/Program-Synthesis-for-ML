import torch
from a_cx_mxint_quant.quantizers import mxint_hardware

import torch
import random
import subprocess
import re
import os
import math


TEMPLATE_FILE = "exp_template.sl"


EXPONENT_WIDTH = 4
Q_CONFIG_IN1 = {"width": 4, "exponent_width": EXPONENT_WIDTH, "round_bits": 0}
Q_CONFIG_IN2 = {"width": 4, "exponent_width": EXPONENT_WIDTH, "round_bits": 0}
Q_CONFIG_OUT = {"width": 4, "exponent_width": EXPONENT_WIDTH, "round_bits": 0}
PARALLELISM = [1, 1]

def to_twos_complement(value: int, bits: int) -> int:
    mask = (1 << bits) - 1
    return value & mask

def mxint_mult(float1: float, float2: float,
                       q_config_in1: dict, q_config_in2: dict, q_config_out: dict,
                       parallelism: list) -> tuple:
    tensor1 = torch.tensor([[float1]])
    tensor2 = torch.tensor([[float2]])

    dequant_float1, mant_tensor1, exp_tensor1 = mxint_hardware(tensor1, q_config_in1, parallelism)
    dequant_float2, mant_tensor2, exp_tensor2 = mxint_hardware(tensor2, q_config_in2, parallelism)



    sum_dequant_float = dequant_float1 * dequant_float2

    #print(sum_dequant_float.item())

    _, out_mant_tensor, out_exp_tensor = mxint_hardware(sum_dequant_float, q_config_out, parallelism)


    return (int(mant_tensor1.item()), int(exp_tensor1.item()),
            int(mant_tensor2.item()), int(exp_tensor2.item()),
            int(out_mant_tensor.item()), int(out_exp_tensor.item()))

def gen_mxint_constraint(float1: float, float2: float, val: str, relative_tolerance_percent: float ) -> str:
    in1_mant_val, in1_exp_val, in2_mant_val, in2_exp_val, out_mant_val, out_exp_val = \
mxint_mult(float1, float2, Q_CONFIG_IN1, Q_CONFIG_IN2, Q_CONFIG_OUT, PARALLELISM)


    in1_mant_hex = f"#x{to_twos_complement(in1_mant_val, 4):x}"
    in1_exp_hex = f"#x{to_twos_complement(in1_exp_val, 4):x}"
    in2_mant_hex = f"#x{to_twos_complement(in2_mant_val, 4):x}"
    in2_exp_hex = f"#x{to_twos_complement(in2_exp_val, 4):x}"
    oracle_mant_hex = f"#x{to_twos_complement(out_mant_val, 4):x}"
    oracle_exp_hex = f"#x{to_twos_complement(out_exp_val, 4):x}"

    if val == "exp":
        synth_call = f"(mult_mxint_exp {in1_mant_hex} {in1_exp_hex} {in2_mant_hex} {in2_exp_hex})"
        
    elif val == "mant":
        synth_call = f"(mult_mxint_mant {in1_mant_hex} {in1_exp_hex} {in2_mant_hex} {in2_exp_hex})"


    dequant_int_oracle_py = out_mant_val * (2 ** out_exp_val)
    

    allowed_error = math.ceil((relative_tolerance_percent / 100.0) * abs(dequant_int_oracle_py))
    
    if relative_tolerance_percent == 0:
        #return f"(constraint (= {synth_call} {oracle_mant_hex}))"
        return f"(constraint (= {synth_call} {oracle_exp_hex}))"
    else:
        return f"""(constraint (let (
        (synth_res_16b ((_ sign_extend 12) {synth_call}))
        (oracle_res_16b ((_ sign_extend 12) {oracle_mant_hex}))
        (oracle_exp_16b ((_ zero_extend 12) (_ bv{to_twos_complement(out_exp_val, 4)} 4)))
    )
    (let (
        (dequant_synth (bvshl synth_res_16b oracle_exp_16b))
        (dequant_oracle (bvshl oracle_res_16b oracle_exp_16b))
    )
    (let ((abs_diff (ite (bvsge dequant_synth dequant_oracle)
                         (bvsub dequant_synth dequant_oracle)
                         (bvsub dequant_oracle dequant_synth))))
        (bvsle abs_diff (_ bv{int(allowed_error)} 16))
    ))))""".strip()
    

    
    
def run_synthesis(constraints: list) -> str | None:


    with open(TEMPLATE_FILE, "r") as f:
            sygus_query = f.read()
    sygus_query += "\n; --- CONSTRAINTS ---\n"

    for c in constraints:
        sygus_query += c + "\n"

    sygus_query += "\n(check-synth)\n"

    run_file = "run.sl"
    with open(run_file, "w") as f:
        f.write(sygus_query)

    try:
        result = subprocess.run(
    ["cvc5", "--lang=sygus2", run_file],
    capture_output=True, text=True, timeout=60
)
        print("CVC5 Output:\n", result.stdout)

        solution_text = result.stdout.strip()
        if "(define-fun" in solution_text:
            return solution_text
        else:
            print("CVC5 did not return a valid solution.")
            return None

    except subprocess.TimeoutExpired:
        print("CVC5 timed out!")
        return None


    #finally:
    #    if os.path.exists(run_file):
    #        os.remove(run_file)

if __name__ == "__main__":
    print("--- Its synthesising time! ---")

    accepted_constraints = []
    current_best_program = None

    """
    floats = [
        (7.5, 0.25),
        (0.25, 7.5),
        (-6.0, 0.5),
        (7.0, 6.0),
        (-0.5, -0.75),
        (3.0, 3.0),
        (4.0, -0.5),
    ]
    """

    floats = [
        (-8.0, -8.0),   
        (7.5, 7.5),    
        (-6.5, 0.0),    #
        (5.25, 1.0),  
        (5.25, -1.0),   
        (-3.5, -4.5),   
        (7.0, -0.5),    
        (-0.5, 7.0),    
        (0.25, 0.5)   ]  

    floats_used = []

    for i in range(9):
        print(f"\n--- Iteration {i+1} ---")

        #f1 = random.uniform(-8, 8)
        #f2 = random.uniform(-8, 8)



        f1 = floats[i][0]
        f2 = floats[i][1]

        #f1 = -6.0
        #f2 =0.5

        #rand1 = random.randint(0, 5)
        #rand2 = random.randint(0, 5)

        #f1 = 0.25 * rand1
        #f2 = 0.25 * rand2

        floats_used.append((f1, f2))

        print(f"Generating new constraint with floats: ({f1:.3f}, {f2:.3f})")
        new_constraint = gen_mxint_constraint(f1, f2, "exp", relative_tolerance_percent=0)


        constraints_to_test = accepted_constraints + [new_constraint]

        #print(f"Testing with {len(constraints_to_test)} constraints...")
        #print(constraints_to_test)

        solution = run_synthesis(constraints_to_test)

        if solution:
            accepted_constraints.append(new_constraint)
            current_best_program = solution
            print(f"SUCCESS: New constraint accepted. Total constraints: {len(accepted_constraints)}")
        else:
            print(f"REJECTED: New constraint '{new_constraint}' is incompatible or caused a timeout.")


    print("\n\n--- Synthesis Complete! ---")

    if current_best_program:
        #print("\nFinal set of accepted constraints:")
        #for c in accepted_constraints:
            #print(c)

        print("\n Number of accepted constraints:", len(accepted_constraints))
        print("Constraints:")
        for c in accepted_constraints:
            print(c)

        print("\n Final Synthesized Program:")
        print(current_best_program)

        with open("solution_exp.txt", "w") as f:
            f.write(current_best_program)
    else:
        print("\nCould not find a valid program that satisfies any constraints.")