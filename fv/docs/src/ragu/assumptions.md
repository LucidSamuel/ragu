# Assumptions


The soundness of the Ragu Formal Verification relies on some assumptions:

- The extraction is correct
    - The semantics of the Ragu Driver operations are correctly captured, and are correctly translated into Clean operations (i.e., the exported operations and the Ragu circuit are semantically equivalent)
    - The inputs/outputs serialization is done correctly
    - The circuit instance is defined correctly and is coherent with the goal of the FV

- The assumptions and specification properties suffice to fully characterize the circuit within the scope of the FV (e.g., we could prove a Spec that does not imply some real-world broader property we care about)

- The lean "core" statements are correct
    - The same circuit/same output theorem statements suffice to fully characterize semantic equivalence of circuits
    - more generally, the formal instance in lean is correct
    - the Clean core statements about circuit semantics and subcircuit composition are correct
