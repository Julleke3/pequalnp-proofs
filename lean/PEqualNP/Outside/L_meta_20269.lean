import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20269

def witness : Circuit :=
  ⟨[⟨.or, [0, 8]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [1, 24]⟩, ⟨.or, [2, 21]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [17, 27]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [18, 31]⟩, ⟨.or, [29, 30]⟩, ⟨.and, [32, 22]⟩, ⟨.and, [31, 26]⟩, ⟨.and, [25, 28]⟩, ⟨.and, [29, 30]⟩, ⟨.and, [3, 33]⟩, ⟨.and, [14, 27]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [40, 36]⟩, ⟨.or, [41, 37]⟩, ⟨.or, [42, 38]⟩, ⟨.or, [43, 39]⟩], 44⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_20269

open PEqualNP.Outside.L_meta_20269 in
theorem PEqualNP.Outside.L_meta_20269 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6614477138885590260 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
