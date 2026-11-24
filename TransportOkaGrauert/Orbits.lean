import Mathlib.Topology.Connected.Clopen

/-!
# Open gauge orbits

For an orbit equivalence relation, local solvability makes every orbit open.
Its complement is the union of all other orbits. Connectedness of the
attenuation space then gives transitivity, as in §3 of Bohr–Paternain.
-/

namespace TransportOkaGrauert

open Set

variable {α : Type*}

/-- The complement of the class of `x` is the union of the equivalence
classes of all points outside that class. -/
theorem class_complement_eq_union (r : Setoid α) (x : α) :
    {z | r.r x z}ᶜ = ⋃ y : {w // ¬ r.r x w}, {z | r.r y.val z} := by
  ext z
  constructor
  · intro hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, r.iseqv.refl z⟩
  · intro hz
    obtain ⟨y, hyz⟩ := mem_iUnion.mp hz
    exact fun hxz => y.property (r.iseqv.trans hxz (r.iseqv.symm hyz))

variable [TopologicalSpace α]

/-- A local section of the orbit map based at each point supplies the
neighborhood in this hypothesis. Transitivity of `r` makes the entire class
of each point open. -/
theorem open_classes_of_local_reachability (r : Setoid α)
    (h : ∀ x, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, r.r x y)
    (x : α) : IsOpen {y | r.r x y} := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hxy
  obtain ⟨U, hU, hyU, hreach⟩ := h y
  exact Filter.mem_of_superset (hU.mem_nhds hyU)
    (fun z hz => r.iseqv.trans hxy (hreach z hz))

/-- If all classes are open, their complements are open as well. -/
theorem open_class_complement (r : Setoid α)
    (ho : ∀ x, IsOpen {y | r.r x y}) (x : α) : IsOpen {y | r.r x y}ᶜ := by
  rw [class_complement_eq_union r x]
  exact isOpen_iUnion (fun y => ho y.val)

/-- In a preconnected space an equivalence relation with open classes
relates every pair of points. -/
theorem related_of_open_classes [PreconnectedSpace α] (r : Setoid α)
    (ho : ∀ x, IsOpen {y | r.r x y}) (x y : α) : r.r x y := by
  have hclopen : IsClopen {z | r.r x z} :=
    ⟨isOpen_compl_iff.mp (open_class_complement r ho x), ho x⟩
  have huniv := hclopen.eq_univ ⟨x, r.iseqv.refl x⟩
  change y ∈ {z | r.r x z}
  rw [huniv]
  exact mem_univ y

end TransportOkaGrauert
