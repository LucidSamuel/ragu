import Clean.Circuit
import Clean.Circuit.Loops
import Ragu.Circuits.Endoscalar.Hoist
import Ragu.Circuits.Endoscalar.HoistedAlloc
import Ragu.Circuits.Endoscalar.Walk

namespace Ragu.Circuits.Endoscalar.HoistedConsistent
open Walk
variable {p : ℕ} [Fact p.Prime]

/-- The gadget's wires as a stage holds them: the bits, then per digit the
products `e₁ e₂` and `e₁ e₂ s`. -/
structure Input (F : Type) where
  bits : Vector F numBits
  products : Vector F numProducts
deriving ProvableStruct

/-- The hint `HoistedEndoscalar::enforce_consistent` passes to `alloc` is the
gadget's own witness. Here it is read off the bit wires, as
`Boolean.Consistent` reads its hint: bit `i` is whether wire `i` holds `1`. -/
def hint (env : ProverEnvironment (F p)) (bits : Vector (Expression (F p)) numBits) :
    BitVec numBits :=
  (BitVec.ofBoolListLE (bits.toList.map fun b => decide (env b = 1))).cast (by simp)

lemma hint_getElem (env : ProverEnvironment (F p)) (bits : Vector (Expression (F p)) numBits)
    (i : ℕ) (h : i < numBits) :
    (hint env bits)[i] = decide (Expression.eval env.toEnvironment bits[i] = 1) := by
  simp only [hint, BitVec.getElem_cast]
  rw [← BitVec.getLsbD_eq_getElem (by simpa using h)]
  simp [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem, h]
  first | rfl | simp

/-- `HoistedEndoscalar::enforce_consistent` (`endoscalar.rs`):

```rust
Self::alloc(dr, self.endoscalar.value.clone())?.enforce_conservative_equal(dr, self)
```

A fresh `HoistedEndoscalar::alloc` seeded from the existing gadget's own
witness, linked to it wire by wire in the gadget's wire order: the bits, then
per digit the two products. This is what the staging machinery re-emits when
it substitutes the gadget's wires into a context where `alloc` never ran. -/
def main (input : Var Input (F p)) : Circuit (F p) (Var unit (F p)) := do
  let fresh ← HoistedAlloc.circuit fun env => hint env input.bits
  Circuit.forEach (Vector.finRange numBits) fun (i : Fin numBits) =>
    assertZero (fresh.bits[i] - input.bits[i])
  Circuit.forEach (Vector.finRange numDigits) fun (i : Fin numDigits) => do
    assertZero (fresh.products[2 * i.val]'(product_index_lt i) -
      input.products[2 * i.val]'(product_index_lt i))
    assertZero (fresh.products[2 * i.val + 1]'(product_index_succ_lt i) -
      input.products[2 * i.val + 1]'(product_index_succ_lt i))

/-- No caller precondition: this is what *establishes* the wires' contract. -/
def Assumptions (_input : Input (F p)) := True

/-- The existing wires satisfy the hoisted gadget's contract: the bits are
boolean and the products are the products of their bits. -/
def Spec (input : Input (F p)) :=
  (∀ i : Fin numBits, IsBool input.bits[i]) ∧ Hoist.Spec ⟨input.bits⟩ input.products

/-- One `HoistedEndoscalar::alloc`; the links allocate nothing. -/
instance elaborated : ElaboratedCircuit (F p) Input unit main where
  localLength _ := numBits * 3 + numDigits * 6
  localLength_eq input offset := by
    simp +arith [main, circuit_norm, HoistedAlloc.circuit, HoistedAlloc.elaborated]
  subcircuitsConsistent input offset := by
    simp +arith [main, circuit_norm, HoistedAlloc.circuit, HoistedAlloc.elaborated]
  channelsLawful := by
    simp +arith [main, circuit_norm, HoistedAlloc.circuit, HoistedAlloc.elaborated]

/-- The fresh gadget satisfies the contract by `HoistedAlloc`'s spec, and the
links make its wires the existing ones. -/
theorem soundness : FormalAssertion.Soundness (F p) (Input := Input) main Assumptions Spec := by
  circuit_proof_start [main, HoistedAlloc.circuit, HoistedAlloc.Assumptions, HoistedAlloc.Spec,
    Hoist.Spec]
  obtain ⟨h_bits_eval, h_products_eval⟩ := h_input
  have h_bits_eq : ∀ (j : ℕ) (h : j < numBits),
      Expression.eval env (input_var_bits[j]'h) = (input_bits[j]'h) := by
    intro j h
    have := congrArg (fun v => v[j]'h) h_bits_eval
    simpa [Vector.getElem_map] using this
  have h_prod_eq : ∀ (j : ℕ) (h : j < numProducts),
      Expression.eval env (input_var_products[j]'h) = (input_products[j]'h) := by
    intro j h
    have := congrArg (fun v => v[j]'h) h_products_eval
    simpa [Vector.getElem_map] using this
  obtain ⟨⟨h_fresh_bool, h_fresh_products⟩, h_link_bits, h_link_products⟩ := h_holds
  simp only [h_bits_eq, h_prod_eq, sub_eq_zero] at h_link_bits h_link_products
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [← h_link_bits i]
    exact h_fresh_bool i
  · obtain ⟨hp, hq⟩ := h_link_products i
    obtain ⟨hp', hq'⟩ := h_fresh_products i
    rw [← hp, ← hq, hq', hp',
      ← h_link_bits ⟨2 + 3 * i.val, bit_index_lt i (by norm_num)⟩,
      ← h_link_bits ⟨3 + 3 * i.val, bit_index_lt i (by norm_num)⟩,
      ← h_link_bits ⟨4 + 3 * i.val, bit_index_lt i (by norm_num)⟩]
    exact ⟨rfl, rfl⟩

/-- Seeding the fresh gadget from wires that already satisfy the contract
reproduces them, so every link holds. -/
theorem completeness : FormalAssertion.Completeness (F p) (Input := Input) main Assumptions Spec := by
  circuit_proof_start [main, HoistedAlloc.circuit, HoistedAlloc.ProverAssumptions,
    HoistedAlloc.ProverSpec, Hoist.Spec]
  obtain ⟨h_bits_eval, h_products_eval⟩ := h_input
  obtain ⟨h_bool, h_products⟩ := h_spec
  have h_bits_eq : ∀ (j : ℕ) (h : j < numBits),
      Expression.eval env.toEnvironment (input_var_bits[j]'h) = (input_bits[j]'h) := by
    intro j h
    have := congrArg (fun v => v[j]'h) h_bits_eval
    simpa [Vector.getElem_map] using this
  have h_prod_eq : ∀ (j : ℕ) (h : j < numProducts),
      Expression.eval env.toEnvironment (input_var_products[j]'h) = (input_products[j]'h) := by
    intro j h
    have := congrArg (fun v => v[j]'h) h_products_eval
    simpa [Vector.getElem_map] using this
  obtain ⟨_, h_fresh_bits, h_fresh_products⟩ := h_env
  have h_hint : ∀ i : Fin numBits,
      (if (hint env input_var_bits)[i.val] then (1 : F p) else 0) = input_bits[i.val] := by
    intro i
    rw [hint_getElem, h_bits_eq]
    rcases h_bool i with h | h <;> simp [h]
  simp only [h_hint] at h_fresh_bits
  simp only [h_bits_eq, h_prod_eq]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [h_fresh_bits i, sub_self]
  · obtain ⟨hp', hq'⟩ := h_fresh_products i
    obtain ⟨hp, hq⟩ := h_products i
    rw [hq', hp', hq, hp, h_fresh_bits, h_fresh_bits, h_fresh_bits]
    exact ⟨sub_self _, sub_self _⟩

/-- `HoistedEndoscalar::enforce_consistent`. -/
def circuit : FormalAssertion (F p) Input :=
  { main, elaborated := elaborated, Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Endoscalar.HoistedConsistent
